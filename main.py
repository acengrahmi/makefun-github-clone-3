#!/usr/bin/env python3
"""A GitHub-compatible git forge, written for speed.

Single-file, standard-library-only server. Design notes:

* One global content-addressed object store. Objects are immutable, so the
  zlib-compressed pack entry for an object is built once and reused by every
  pack that ever carries it; assembling a pack is then concatenation plus a
  SHA-1 over the result.
* Advertisements, ls-refs answers and fetch responses are cached against a
  per-repository generation counter. Any ref change bumps the generation, so
  a repeated clone of an unchanged repository is a dictionary hit that
  returns prebuilt response bytes.
* Issue JSON is serialized once when the issue changes and the bytes are
  served verbatim on every read.
* Nothing nondeterministic reaches a response: timestamps come from a
  logical tick, request ids from a counter.
"""

import base64
import hashlib
import json
import os
import re
import socket
import struct
import sys
import threading
import time
import urllib.request
import zlib
from difflib import SequenceMatcher
from http.client import responses as STATUS_PHRASES
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, unquote, urlsplit

# --------------------------------------------------------------------------
# configuration and identity

TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "")

# The bearer token names one account. The kit's seeded scenario fixes that
# account, so the login is a constant of the deployment.
VIEWER_LOGIN = "adaiversen"
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"
VIEWER_ID = 1000

ZERO_OID = "0" * 40
TYPE_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag", 6: "ofs-delta", 7: "ref-delta"}
AGENT_STRING = "forge/3.0"
INSTALLED_VERSION = "3.0.0"

# --------------------------------------------------------------------------
# deterministic logical clock

_tick_lock = threading.Lock()
_tick_value = 1_735_689_600  # 2025-01-01T00:00:00Z


def tick():
    """A fresh logical timestamp (seconds), strictly increasing."""
    global _tick_value
    with _tick_lock:
        _tick_value += 1
        return _tick_value


def iso_of(epoch):
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(epoch))


def iso_now():
    return iso_of(tick())


# --------------------------------------------------------------------------
# the object store

OBJECTS = {}          # oid -> (type_name, data bytes)
_entry_cache = {}     # oid -> compressed pack entry bytes (header + zlib)
_parents_cache = {}   # commit oid -> tuple of parent oids
_tree_cache = {}      # tree oid -> tuple of (mode, name, child oid)
_commit_head = {}     # commit oid -> (tree oid, committer epoch)
_anc_cache = {}       # commit oid -> frozenset of ancestor commit oids (incl. self)
_flat_cache = {}      # tree oid -> {path: (mode, blob oid)}
STORE_LOCK = threading.RLock()


def oid_of(type_name, data):
    head = ("%s %d\0" % (type_name, len(data))).encode()
    return hashlib.sha1(head + data).hexdigest()


def store_object(type_name, data):
    oid = oid_of(type_name, data)
    if oid not in OBJECTS:
        OBJECTS[oid] = (type_name, data)
    return oid


def get_object(oid):
    return OBJECTS.get(oid)


def commit_parents(oid):
    cached = _parents_cache.get(oid)
    if cached is not None:
        return cached
    obj = OBJECTS.get(oid)
    if obj is None or obj[0] != "commit":
        _parents_cache[oid] = ()
        return ()
    parents = []
    for line in obj[1].split(b"\n"):
        if line == b"":
            break
        if line.startswith(b"parent "):
            parents.append(line[7:].decode())
    result = tuple(parents)
    _parents_cache[oid] = result
    return result


def commit_head(oid):
    """(tree oid, committer epoch) of a commit, parsed once."""
    cached = _commit_head.get(oid)
    if cached is not None:
        return cached
    obj = OBJECTS.get(oid)
    if obj is None or obj[0] != "commit":
        return (None, 0)
    tree = None
    epoch = 0
    for line in obj[1].split(b"\n"):
        if line == b"":
            break
        if line.startswith(b"tree "):
            tree = line[5:].decode()
        elif line.startswith(b"committer "):
            parts = line.rsplit(b" ", 2)
            if len(parts) == 3:
                try:
                    epoch = int(parts[1])
                except ValueError:
                    epoch = 0
    result = (tree, epoch)
    _commit_head[oid] = result
    return result


def tree_entries(oid):
    cached = _tree_cache.get(oid)
    if cached is not None:
        return cached
    obj = OBJECTS.get(oid)
    if obj is None or obj[0] != "tree":
        _tree_cache[oid] = ()
        return ()
    data = obj[1]
    entries = []
    pos = 0
    while pos < len(data):
        sp = data.index(b" ", pos)
        mode = data[pos:sp].decode()
        nul = data.index(b"\0", sp)
        name = data[sp + 1:nul].decode()
        child = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, child))
        pos = nul + 21
    result = tuple(entries)
    _tree_cache[oid] = result
    return result


def flatten_tree(tree_oid):
    """{path: (mode, oid)} for every leaf under a tree, memoized."""
    cached = _flat_cache.get(tree_oid)
    if cached is not None:
        return cached
    out = {}

    def walk(oid, prefix):
        for mode, name, child in tree_entries(oid):
            if mode == "40000":
                walk(child, prefix + name + "/")
            else:
                out[prefix + name] = (mode, child)

    if tree_oid:
        walk(tree_oid, "")
    _flat_cache[tree_oid] = out
    return out


def build_tree_from_flat(flat):
    """Inverse of flatten_tree: nest the paths and store every tree level."""
    root = {}

    def insert(node, parts, mode, oid):
        if len(parts) == 1:
            node[parts[0]] = (mode, oid)
            return
        child = node.get(parts[0])
        if not isinstance(child, dict):
            child = {}
            node[parts[0]] = child
        insert(child, parts[1:], mode, oid)

    for path, (mode, oid) in flat.items():
        insert(root, path.split("/"), mode, oid)

    def emit(node):
        entries = []
        for name in sorted(node.keys(), key=lambda n: n + "/" if isinstance(node[n], dict) else n):
            value = node[name]
            if isinstance(value, dict):
                entries.append(("40000", name, emit(value)))
            else:
                entries.append((value[0], name, value[1]))
        data = b"".join(
            mode.encode() + b" " + name.encode() + b"\0" + bytes.fromhex(child)
            for mode, name, child in entries
        )
        return store_object("tree", data)

    return emit(root)


def ancestors_incl(oid):
    """Every commit reachable from `oid` through parents, including itself."""
    cached = _anc_cache.get(oid)
    if cached is not None:
        return cached
    seen = set()
    stack = [oid]
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        hit = _anc_cache.get(current)
        if hit is not None:
            seen |= hit
            continue
        seen.add(current)
        stack.extend(commit_parents(current))
    result = frozenset(seen)
    _anc_cache[oid] = result
    return result


def is_ancestor(maybe_ancestor, oid):
    if maybe_ancestor == oid:
        return True
    obj = OBJECTS.get(maybe_ancestor)
    if obj is None or obj[0] != "commit":
        return False
    return maybe_ancestor in ancestors_incl(oid)


def peel_to_commit(oid):
    """Follow tag objects until a commit (or another type) is reached."""
    seen = set()
    current = oid
    while current not in seen:
        seen.add(current)
        obj = OBJECTS.get(current)
        if obj is None:
            return current
        if obj[0] == "commit":
            return current
        if obj[0] != "tag":
            return current
        target = None
        for line in obj[1].split(b"\n"):
            if line == b"":
                break
            if line.startswith(b"object "):
                target = line[7:].decode()
        if target is None:
            return current
        current = target
    return current


def peel_fully(oid):
    """The non-tag object a ref ultimately names (for ^{} advertisement lines)."""
    return peel_to_commit(oid) if OBJECTS.get(oid, (None,))[0] == "tag" else None


# --------------------------------------------------------------------------
# reachability

def _add_tree_closure(oid, out):
    stack = [oid]
    while stack:
        current = stack.pop()
        if current in out:
            continue
        obj = OBJECTS.get(current)
        if obj is None:
            continue
        out.add(current)
        if obj[0] == "tree":
            for _mode, _name, child in tree_entries(current):
                stack.append(child)


def full_closure(tips, shallow_boundary=frozenset()):
    """Every object reachable from tips. Commits named in shallow_boundary
    are included with their trees but their parents are not walked."""
    out = set()
    stack = list(tips)
    while stack:
        current = stack.pop()
        if current in out:
            continue
        obj = OBJECTS.get(current)
        if obj is None:
            continue
        out.add(current)
        kind = obj[0]
        if kind == "commit":
            tree, _epoch = commit_head(current)
            if tree:
                _add_tree_closure(tree, out)
            if current not in shallow_boundary:
                stack.extend(commit_parents(current))
        elif kind == "tag":
            for line in obj[1].split(b"\n"):
                if line == b"":
                    break
                if line.startswith(b"object "):
                    stack.append(line[7:].decode())
        elif kind == "tree":
            for _mode, _name, child in tree_entries(current):
                stack.append(child)
    return out


def depth_closure(tips, depth):
    """(objects, boundary commits) for a depth-limited walk from tips.

    A tip counts as depth 1. Boundary commits are the included commits that
    still have a parent in the store which was not included.
    """
    out = set()
    dist = {}
    queue = []
    for tip in tips:
        commit = peel_to_commit(tip)
        if tip != commit:
            out.add(tip)  # the tag object itself travels
            current = tip
            while OBJECTS.get(current, (None,))[0] == "tag":
                for line in OBJECTS[current][1].split(b"\n"):
                    if line.startswith(b"object "):
                        nxt = line[7:].decode()
                        if nxt != commit:
                            out.add(nxt)
                        current = nxt
                        break
                else:
                    break
        if commit not in dist:
            dist[commit] = 1
            queue.append(commit)
    index = 0
    while index < len(queue):
        commit = queue[index]
        index += 1
        d = dist[commit]
        out.add(commit)
        tree, _epoch = commit_head(commit)
        if tree:
            _add_tree_closure(tree, out)
        if d < depth:
            for parent in commit_parents(commit):
                if parent not in dist:
                    dist[parent] = d + 1
                    queue.append(parent)
    boundary = set()
    for commit in dist:
        for parent in commit_parents(commit):
            if parent not in dist and parent in OBJECTS:
                boundary.add(commit)
                break
    return out, boundary


# --------------------------------------------------------------------------
# packfiles

def _varint_pack_entry_header(type_code, size):
    first = (type_code << 4) | (size & 0x0F)
    size >>= 4
    out = bytearray()
    while size:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


def pack_entry(oid):
    """The compressed pack entry for one object, built once, reused forever."""
    cached = _entry_cache.get(oid)
    if cached is not None:
        return cached
    type_name, data = OBJECTS[oid]
    entry = _varint_pack_entry_header(TYPE_CODE[type_name], len(data)) + zlib.compress(data, 1)
    _entry_cache[oid] = entry
    return entry


def build_pack(oids):
    body = bytearray(b"PACK" + struct.pack(">II", 2, len(oids)))
    for oid in oids:
        body += pack_entry(oid)
    trailer = hashlib.sha1(bytes(body)).digest()
    return bytes(body) + trailer


def _read_pack_varint(data, pos):
    byte = data[pos]
    pos += 1
    type_code = (byte >> 4) & 0x07
    size = byte & 0x0F
    shift = 4
    while byte & 0x80:
        byte = data[pos]
        pos += 1
        size |= (byte & 0x7F) << shift
        shift += 7
    return type_code, size, pos


def _read_ofs_varint(data, pos):
    byte = data[pos]
    pos += 1
    offset = byte & 0x7F
    while byte & 0x80:
        byte = data[pos]
        pos += 1
        offset = ((offset + 1) << 7) | (byte & 0x7F)
    return offset, pos


def _inflate_at(data, pos):
    decomp = zlib.decompressobj()
    out = decomp.decompress(data[pos:])
    if not decomp.eof:
        raise ValueError("truncated zlib stream in pack")
    consumed = len(data) - pos - len(decomp.unused_data)
    return out, pos + consumed


def _apply_delta(base, delta):
    pos = 0

    def read_varint():
        nonlocal pos
        result = 0
        shift = 0
        while True:
            byte = delta[pos]
            pos += 1
            result |= (byte & 0x7F) << shift
            shift += 7
            if not byte & 0x80:
                return result

    src_size = read_varint()
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    read_varint()  # target size; the ops below define it exactly
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            cp_off = 0
            cp_size = 0
            for bit in range(4):
                if op & (1 << bit):
                    cp_off |= delta[pos] << (8 * bit)
                    pos += 1
            for bit in range(3):
                if op & (0x10 << bit):
                    cp_size |= delta[pos] << (8 * bit)
                    pos += 1
            if cp_size == 0:
                cp_size = 0x10000
            out += base[cp_off:cp_off + cp_size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    return bytes(out)


def parse_pack(data):
    """Parse a pack into the store. Returns the list of object ids it held."""
    if len(data) < 12 + 20 or data[:4] != b"PACK":
        raise ValueError("not a packfile")
    _version, count = struct.unpack(">II", data[4:12])
    pos = 12
    raw = []  # (entry_start, entry_end, type_code, payload or (kind, base, delta))
    for _ in range(count):
        start = pos
        type_code, _size, pos = _read_pack_varint(data, pos)
        if type_code == 6:
            back, pos = _read_ofs_varint(data, pos)
            base_start = start - back
            payload, pos = _inflate_at(data, pos)
            raw.append((start, pos, type_code, ("ofs", base_start, payload)))
        elif type_code == 7:
            base_oid = data[pos:pos + 20].hex()
            pos += 20
            payload, pos = _inflate_at(data, pos)
            raw.append((start, pos, type_code, ("ref", base_oid, payload)))
        else:
            payload, pos = _inflate_at(data, pos)
            raw.append((start, pos, type_code, payload))
    by_start = {}
    resolved = {}

    def resolve(index):
        if index in resolved:
            return resolved[index]
        start, end, type_code, payload = raw[index]
        if type_code in (1, 2, 3, 4):
            type_name = CODE_TYPE[type_code]
            content = payload
            oid = store_object(type_name, content)
            # The sender's own compressed entry is a valid pack entry for
            # this object; keep it instead of recompressing at fetch time.
            if oid not in _entry_cache:
                _entry_cache[oid] = data[start:end]
        else:
            kind, base_ref, delta = payload
            if kind == "ofs":
                base_index = by_start[base_ref]
                _boid, base_type, base_data = resolve(base_index)
            else:
                if base_ref in OBJECTS:
                    base_type, base_data = OBJECTS[base_ref]
                else:
                    raise ValueError("delta base not in store")
            type_name = base_type
            content = _apply_delta(base_data, delta)
            oid = store_object(type_name, content)
        resolved[index] = (oid, type_name, content)
        return resolved[index]

    for index, (start, _end, _tc, _p) in enumerate(raw):
        by_start[start] = index
    oids = []
    for index in range(len(raw)):
        oid, _type_name, _content = resolve(index)
        oids.append(oid)
    return oids


# --------------------------------------------------------------------------
# repositories

_repo_counter = [0]


class Issue:
    __slots__ = ("number", "title", "body", "state", "labels", "comments",
                 "created_tick", "json_cache")

    def __init__(self, number, title, body, labels):
        self.number = number
        self.title = title
        self.body = body
        self.state = "open"
        self.labels = list(labels)
        self.comments = []          # list of (id, body, tick)
        self.created_tick = tick()
        self.json_cache = None


class Pull:
    __slots__ = ("number", "title", "body", "head", "base", "state", "merged",
                 "merge_commit_sha", "merged_tick", "base_tip_at_create",
                 "created_tick")

    def __init__(self, number, title, body, head, base, base_tip):
        self.number = number
        self.title = title
        self.body = body
        self.head = head
        self.base = base
        self.state = "open"
        self.merged = False
        self.merge_commit_sha = None
        self.merged_tick = None
        self.base_tip_at_create = base_tip
        self.created_tick = tick()


class Repo:
    __slots__ = ("name", "owner", "description", "private", "default_branch",
                 "db_id", "refs", "gen", "labels", "issues", "pulls",
                 "next_number", "next_comment_id", "created_tick",
                 "adv_cache", "fetch_cache", "repo_json")

    def __init__(self, name, description, private):
        _repo_counter[0] += 1
        self.name = name
        self.owner = VIEWER_LOGIN
        self.description = description
        self.private = private
        self.default_branch = "main"
        self.db_id = _repo_counter[0]
        self.refs = {}              # full ref name -> oid
        self.gen = 0                # bumped on every ref change
        self.labels = {}            # name -> color
        self.issues = {}            # number -> Issue
        self.pulls = {}             # number -> Pull
        self.next_number = 1        # issues and pulls share one sequence
        self.next_comment_id = 1
        self.created_tick = tick()
        self.adv_cache = {}
        self.fetch_cache = {}
        self.repo_json = None

    def bump(self):
        self.gen += 1
        self.adv_cache.clear()
        self.fetch_cache.clear()
        self.repo_json = None


REPOS = {}  # name -> Repo


def get_repo(owner, name):
    if owner != VIEWER_LOGIN:
        return None
    return REPOS.get(name)


def create_repo(name, description, private):
    repo = REPOS.get(name)
    if repo is not None:
        return repo, False
    repo = Repo(name, description or "", bool(private))
    REPOS[name] = repo
    return repo, True


def head_target(repo):
    return "refs/heads/" + repo.default_branch


def head_oid(repo):
    return repo.refs.get(head_target(repo))


# --------------------------------------------------------------------------
# JSON serialization (GitHub-shaped bodies)

def dumps_bytes(value):
    return json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def repo_dict(repo):
    return {
        "id": repo.db_id,
        "name": repo.name,
        "full_name": repo.owner + "/" + repo.name,
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "owner": {"login": repo.owner, "id": VIEWER_ID},
        "html_url": "http://forge.local/" + repo.owner + "/" + repo.name,
        "created_at": iso_of(repo.created_tick),
        "updated_at": iso_of(repo.created_tick),
    }


def repo_json_bytes(repo):
    if repo.repo_json is None:
        repo.repo_json = dumps_bytes(repo_dict(repo))
    return repo.repo_json


def issue_dict(repo, issue):
    stamp = iso_of(issue.created_tick)
    return {
        "id": repo.db_id * 1000000 + issue.number,
        "number": issue.number,
        "title": issue.title,
        "body": issue.body,
        "state": issue.state,
        "labels": [{"name": name, "color": repo.labels.get(name, "ededed")}
                   for name in issue.labels],
        "user": {"login": repo.owner, "id": VIEWER_ID},
        "comments": len(issue.comments),
        "created_at": stamp,
        "updated_at": stamp,
    }


def issue_json_bytes(repo, issue):
    if issue.json_cache is None:
        issue.json_cache = dumps_bytes(issue_dict(repo, issue))
    return issue.json_cache


def pull_dict(repo, pull):
    head_sha = repo.refs.get("refs/heads/" + pull.head, ZERO_OID)
    base_sha = repo.refs.get("refs/heads/" + pull.base, ZERO_OID)
    body = {
        "id": repo.db_id * 1000000 + pull.number,
        "number": pull.number,
        "state": pull.state,
        "title": pull.title,
        "body": pull.body,
        "merged": pull.merged,
        "head": {"ref": pull.head, "sha": head_sha,
                 "repo": {"id": repo.db_id, "name": repo.name}},
        "base": {"ref": pull.base, "sha": base_sha,
                 "repo": {"id": repo.db_id, "name": repo.name}},
        "user": {"login": repo.owner, "id": VIEWER_ID},
        "created_at": iso_of(pull.created_tick),
        "updated_at": iso_of(pull.created_tick),
    }
    if pull.merged:
        body["merged_at"] = iso_of(pull.merged_tick)
        body["merge_commit_sha"] = pull.merge_commit_sha
    else:
        body["merged_at"] = None
        body["merge_commit_sha"] = None
    return body


# --------------------------------------------------------------------------
# contents API commits and pull-request merges

def make_commit(tree_oid, parents, message):
    stamp = tick()
    ident = "%s <%s> %d +0000" % (VIEWER_NAME, VIEWER_EMAIL, stamp)
    lines = ["tree " + tree_oid]
    for parent in parents:
        lines.append("parent " + parent)
    lines.append("author " + ident)
    lines.append("committer " + ident)
    data = ("\n".join(lines) + "\n\n" + message).encode()
    return store_object("commit", data)


def branch_tip(repo, branch):
    return repo.refs.get("refs/heads/" + branch)


def commit_file_change(repo, branch, path, new_blob_oid, message):
    """Commit a single-file change (or deletion when new_blob_oid is None)
    on a branch; the branch may be unborn. Returns the new commit oid."""
    ref = "refs/heads/" + branch
    tip = repo.refs.get(ref)
    flat = {}
    parents = []
    if tip is not None:
        tree, _epoch = commit_head(tip)
        flat = dict(flatten_tree(tree))
        parents = [tip]
    if new_blob_oid is None:
        flat.pop(path, None)
    else:
        flat[path] = ("100644", new_blob_oid)
    tree_oid = build_tree_from_flat(flat)
    commit = make_commit(tree_oid, parents, message)
    repo.refs[ref] = commit
    repo.bump()
    return commit


def merge_analysis(repo, pull):
    """(conflict_paths, merged_flat) of head into the CURRENT base tip,
    three-way against the base tip recorded when the pull was opened."""
    base_ref = "refs/heads/" + pull.base
    head_ref = "refs/heads/" + pull.head
    base_tip = repo.refs.get(base_ref)
    head_tip = repo.refs.get(head_ref)
    if base_tip is None or head_tip is None:
        return (["unresolvable ref"], None)
    origin_tree, _ = commit_head(pull.base_tip_at_create)
    base_tree, _ = commit_head(base_tip)
    head_tree, _ = commit_head(head_tip)
    origin = flatten_tree(origin_tree)
    base_flat = flatten_tree(base_tree)
    head_flat = flatten_tree(head_tree)
    merged = dict(base_flat)
    conflicts = []
    paths = set(origin) | set(base_flat) | set(head_flat)
    for path in paths:
        o = origin.get(path)
        b = base_flat.get(path)
        h = head_flat.get(path)
        if h == o:
            continue            # head did not touch it; base version stands
        if b == o:
            # only head changed it
            if h is None:
                merged.pop(path, None)
            else:
                merged[path] = h
        elif b == h:
            merged[path] = b if b is not None else merged.get(path)
            if b is None:
                merged.pop(path, None)
        else:
            conflicts.append(path)
    return (conflicts, merged)


def pull_files(repo, pull):
    """The changed-file list of a pull: merge-base tree vs head tip tree."""
    head_tip = repo.refs.get("refs/heads/" + pull.head)
    if head_tip is None:
        return []
    origin_tree, _ = commit_head(pull.base_tip_at_create)
    head_tree, _ = commit_head(head_tip)
    origin = flatten_tree(origin_tree)
    head_flat = flatten_tree(head_tree)
    files = []
    for path in sorted(set(origin) | set(head_flat)):
        o = origin.get(path)
        h = head_flat.get(path)
        if o == h:
            continue
        if o is None:
            status = "added"
        elif h is None:
            status = "removed"
        else:
            status = "modified"
        old_text = b""
        new_text = b""
        if o is not None:
            old_text = OBJECTS[o[1]][1]
        if h is not None:
            new_text = OBJECTS[h[1]][1]
        old_lines = old_text.decode("utf-8", "replace").splitlines()
        new_lines = new_text.decode("utf-8", "replace").splitlines()
        matcher = SequenceMatcher(a=old_lines, b=new_lines, autojunk=False)
        additions = 0
        deletions = 0
        for tag, i1, i2, j1, j2 in matcher.get_opcodes():
            if tag in ("insert", "replace"):
                additions += j2 - j1
            if tag in ("delete", "replace"):
                deletions += i2 - i1
        files.append({
            "filename": path,
            "status": status,
            "additions": additions,
            "deletions": deletions,
            "changes": additions + deletions,
            "sha": h[1] if h is not None else o[1],
        })
    return files


def squash_merge(repo, pull):
    """Squash the pull's head tree onto the base branch. Returns the new
    commit oid, or None when the merge conflicts."""
    conflicts, merged_flat = merge_analysis(repo, pull)
    if conflicts:
        return None
    base_ref = "refs/heads/" + pull.base
    base_tip = repo.refs.get(base_ref)
    tree_oid = build_tree_from_flat(merged_flat)
    message = "%s (#%d)" % (pull.title, pull.number)
    commit = make_commit(tree_oid, [base_tip] if base_tip else [], message)
    repo.refs[base_ref] = commit
    repo.bump()
    return commit


# --------------------------------------------------------------------------
# pkt-line codec

def pkt(payload):
    if isinstance(payload, str):
        payload = payload.encode()
    return ("%04x" % (len(payload) + 4)).encode() + payload


PKT_FLUSH = b"0000"
PKT_DELIM = b"0001"


def parse_pkt_lines(data, pos=0):
    """Parse pkt-lines from data starting at pos.

    Returns (lines, end_pos, terminator) where lines holds payload bytes,
    terminator is 'flush', 'delim' or None (ran out of well-formed input),
    and end_pos is just past the terminator (or where parsing stopped).
    """
    lines = []
    while pos + 4 <= len(data):
        head = data[pos:pos + 4]
        try:
            length = int(head, 16)
        except ValueError:
            return lines, pos, None
        if length == 0:
            return lines, pos + 4, "flush"
        if length == 1:
            return lines, pos + 4, "delim"
        if length == 2:
            return lines, pos + 4, "response-end"
        if length < 4 or pos + length > len(data):
            return lines, pos, None
        lines.append(data[pos + 4:pos + length])
        pos += length
    return lines, pos, None


def parse_request_lines(data):
    """Collect every data pkt-line in a git request body, stepping over
    delim and flush separators (v2 puts a delim after the command block;
    v0 fetch puts a flush between the wants and the haves)."""
    lines = []
    pos = 0
    while pos < len(data):
        chunk, end_pos, terminator = parse_pkt_lines(data, pos)
        lines.extend(chunk)
        if terminator is None or end_pos <= pos:
            break
        pos = end_pos
        if terminator == "flush" and pos >= len(data):
            break
    return lines


def sideband_wrap(payload, band=1):
    out = bytearray()
    prefix = bytes([band])
    pos = 0
    while pos < len(payload):
        chunk = payload[pos:pos + 65515]
        out += pkt(prefix + chunk)
        pos += len(chunk)
    if not payload:
        out += pkt(prefix)
    return bytes(out)


# --------------------------------------------------------------------------
# git smart HTTP

UPLOAD_CAPS_V0 = ("side-band-64k thin-pack ofs-delta shallow "
                  "symref=HEAD:refs/heads/main agent=" + AGENT_STRING)
RECEIVE_CAPS_V0 = ("report-status side-band-64k delete-refs ofs-delta "
                   "symref=HEAD:refs/heads/main agent=" + AGENT_STRING)


def sorted_ref_items(repo):
    return sorted(repo.refs.items())


def advertisement_v0(repo, service):
    caps = UPLOAD_CAPS_V0 if service == "git-upload-pack" else RECEIVE_CAPS_V0
    out = bytearray()
    out += pkt("# service=" + service + "\n")
    out += PKT_FLUSH
    items = sorted_ref_items(repo)
    head = head_target(repo)
    lines = []
    head_ref_oid = repo.refs.get(head, ZERO_OID)
    lines.append((head_ref_oid, "HEAD"))
    for name, oid in items:
        lines.append((oid, name))
        peeled = peel_fully(oid)
        if peeled is not None:
            lines.append((peeled, name + "^{}"))
    if not items:
        out += pkt(ZERO_OID + " capabilities^{}\0" + caps + "\n")
    else:
        for index, (oid, name) in enumerate(lines):
            text = oid + " " + name
            if index == 0:
                text += "\0" + caps
            out += pkt(text + "\n")
    out += PKT_FLUSH
    return bytes(out)


def advertisement_v2(repo):
    out = bytearray()
    out += pkt("version 2\n")
    out += pkt("agent=" + AGENT_STRING + "\n")
    out += pkt("ls-refs=unborn\n")
    out += pkt("fetch=shallow filter\n")
    out += pkt("object-format=sha1\n")
    out += PKT_FLUSH
    return bytes(out)


def handle_info_refs(repo, service, protocol_v2):
    if repo is None:
        return None
    if service == "git-upload-pack" and protocol_v2:
        key = ("adv2", repo.gen)
        cached = repo.adv_cache.get(key)
        if cached is None:
            cached = advertisement_v2(repo)
            repo.adv_cache[key] = cached
        return cached
    key = ("adv0", service, repo.gen)
    cached = repo.adv_cache.get(key)
    if cached is None:
        cached = advertisement_v0(repo, service)
        repo.adv_cache[key] = cached
    return cached


def handle_ls_refs(repo, body):
    lines = parse_request_lines(body)
    args = []
    seen_command = False
    for raw in lines:
        text = raw.decode("utf-8", "replace").rstrip("\n")
        if text.startswith("command="):
            seen_command = True
            continue
        if seen_command and (text.startswith("agent=") or text.startswith("object-format=")):
            continue
        args.append(text)
    if not seen_command:
        return None
    peel = "peel" in args
    symrefs = "symrefs" in args
    unborn_ok = "unborn" in args
    prefixes = [a[len("ref-prefix "):] for a in args if a.startswith("ref-prefix ")]
    out = bytearray()

    def matches(name):
        if not prefixes:
            return True
        return any(name.startswith(prefix) for prefix in prefixes)

    head = head_target(repo)
    head_ref_oid = repo.refs.get(head)
    if matches("HEAD"):
        if head_ref_oid is None:
            if unborn_ok:
                line = "unborn HEAD"
                if symrefs:
                    line += " symref-target:" + head
                out += pkt(line + "\n")
        else:
            line = head_ref_oid + " HEAD"
            if symrefs:
                line += " symref-target:" + head
            out += pkt(line + "\n")
    for name, oid in sorted_ref_items(repo):
        if not matches(name):
            continue
        line = oid + " " + name
        if peel:
            peeled = peel_fully(oid)
            if peeled is not None:
                line += " peeled:" + peeled
        out += pkt(line + "\n")
    out += PKT_FLUSH
    return bytes(out)


def _fetch_send_set(repo, wants, haves, client_shallow, depth, deepen_since,
                    deepen_not_tips):
    """Compute (send_set, boundary, included_commits) for a fetch."""
    exclude = set()
    if haves:
        exclude = full_closure(haves, frozenset(client_shallow))
    for tip in deepen_not_tips:
        exclude |= full_closure([tip])
    included_commits = set()
    if depth is not None:
        send, boundary = depth_closure(wants, depth)
        for oid in send:
            obj = OBJECTS.get(oid)
            if obj is not None and obj[0] == "commit":
                included_commits.add(oid)
    elif deepen_since is not None:
        send = set()
        boundary = set()
        seen = set()
        stack = [peel_to_commit(w) for w in wants]
        while stack:
            commit = stack.pop()
            if commit in seen:
                continue
            seen.add(commit)
            _tree, epoch = commit_head(commit)
            if epoch >= deepen_since:
                included_commits.add(commit)
                stack.extend(commit_parents(commit))
            else:
                boundary.add(commit)
        # boundary commits above are the first too-old ones; the shallow
        # boundary the client needs is their included children.
        boundary = set()
        for commit in included_commits:
            send.add(commit)
            tree, _e = commit_head(commit)
            if tree:
                _add_tree_closure(tree, send)
            for parent in commit_parents(commit):
                if parent not in included_commits and parent in OBJECTS:
                    boundary.add(commit)
    else:
        send = full_closure(wants)
        boundary = set()
        for oid in send:
            obj = OBJECTS.get(oid)
            if obj is not None and obj[0] == "commit":
                included_commits.add(oid)
    send -= exclude
    included_commits -= {c for c in included_commits if c in exclude and c not in wants}
    return send, boundary, included_commits


def _order_for_pack(oids):
    commits, trees, rest = [], [], []
    for oid in oids:
        obj = OBJECTS.get(oid)
        if obj is None:
            continue
        if obj[0] == "commit":
            commits.append(oid)
        elif obj[0] == "tree":
            trees.append(oid)
        else:
            rest.append(oid)
    return commits + trees + rest


def handle_fetch(repo, body, version2):
    """Returns the response body bytes, or None for a malformed request."""
    lines = parse_request_lines(body)
    wants = []
    haves = []
    client_shallow = []
    depth = None
    deepen_since = None
    deepen_not = []
    done = False
    command = None
    for raw in lines:
        text = raw.decode("utf-8", "replace").rstrip("\n")
        if text.startswith("command="):
            command = text[len("command="):]
        elif text.startswith("want "):
            wants.append(text[5:].strip())
        elif text.startswith("have "):
            haves.append(text[5:].strip())
        elif text.startswith("shallow "):
            client_shallow.append(text[8:].strip())
        elif text.startswith("deepen-since "):
            try:
                deepen_since = int(text[len("deepen-since "):].strip())
            except ValueError:
                pass
        elif text.startswith("deepen-not "):
            ref = text[len("deepen-not "):].strip()
            tip = repo.refs.get(ref)
            if tip:
                deepen_not.append(tip)
        elif text.startswith("deepen "):
            try:
                depth = int(text[len("deepen "):].strip())
            except ValueError:
                pass
        elif text == "done":
            done = True
    if version2 and command != "fetch":
        return None
    if not wants:
        return None
    for want in wants:
        if want not in OBJECTS:
            return None
    deepen_not_tips = deepen_not
    send, boundary, _included = _fetch_send_set(
        repo, wants, haves, client_shallow, depth, deepen_since, deepen_not_tips)
    shallow_context = depth is not None or deepen_since is not None or bool(client_shallow)
    new_boundary = set()
    unshallow = []
    if shallow_context:
        for commit in boundary:
            if commit in send:
                new_boundary.add(commit)
        # commits the client held as shallow whose parents are now included
        # stop being shallow.
        for shallow_commit in client_shallow:
            if shallow_commit in new_boundary:
                continue
            parents = commit_parents(shallow_commit)
            if all(p in send or p not in OBJECTS for p in parents):
                if parents:
                    unshallow.append(shallow_commit)
    ordered = _order_for_pack(send)
    pack = build_pack(ordered) if ordered else None

    if not version2:
        out = bytearray()
        for commit in sorted(new_boundary):
            out += pkt("shallow " + commit + "\n")
        for commit in unshallow:
            out += pkt("unshallow " + commit + "\n")
        common = [h for h in haves if h in OBJECTS]
        if common:
            out += pkt("ACK " + common[0] + "\n")
        else:
            out += pkt("NAK\n")
        if pack is not None:
            out += sideband_wrap(pack, 1)
        out += PKT_FLUSH
        return bytes(out)

    sections = []
    if haves:
        ack = bytearray()
        ack += pkt("acknowledgments\n")
        common = [h for h in haves if h in OBJECTS]
        if common:
            for have in common:
                ack += pkt("ACK " + have + "\n")
            if pack is not None:
                ack += pkt("ready\n")
        else:
            ack += pkt("NAK\n")
        sections.append(bytes(ack))
    if shallow_context and (new_boundary or unshallow):
        info = bytearray()
        info += pkt("shallow-info\n")
        for commit in sorted(new_boundary):
            info += pkt("shallow " + commit + "\n")
        for commit in unshallow:
            info += pkt("unshallow " + commit + "\n")
        sections.append(bytes(info))
    if pack is not None:
        sections.append(pkt("packfile\n") + sideband_wrap(pack, 1))
    if not sections:
        # Nothing to send and nothing to acknowledge: an empty pack keeps
        # the client's framing expectations satisfied.
        empty = build_pack([])
        sections.append(pkt("packfile\n") + sideband_wrap(empty, 1))
    out = bytearray()
    for index, section in enumerate(sections):
        out += section
        out += PKT_FLUSH if index == len(sections) - 1 else PKT_DELIM
    return bytes(out)


def handle_receive_pack(repo, body):
    lines, pos, _term = parse_pkt_lines(body)
    commands = []
    caps = ""
    for index, raw in enumerate(lines):
        text = raw.decode("utf-8", "replace").rstrip("\n")
        if index == 0 and "\0" in text:
            text, caps = text.split("\0", 1)
        parts = text.split(" ")
        if len(parts) != 3:
            continue
        commands.append((parts[0], parts[1], parts[2]))
    pack_data = body[pos:]
    unpack_ok = True
    if pack_data:
        try:
            with STORE_LOCK:
                parse_pack(pack_data)
        except Exception:
            unpack_ok = False
    results = []
    changed = False
    with STORE_LOCK:
        for old, new, ref in commands:
            if not ref.startswith("refs/"):
                results.append((ref, False, "invalid ref name"))
                continue
            if new == ZERO_OID:
                if repo.refs.get(ref) is None:
                    results.append((ref, False, "reference does not exist"))
                elif old != ZERO_OID and repo.refs.get(ref) != old:
                    results.append((ref, False, "reference was moved"))
                else:
                    del repo.refs[ref]
                    changed = True
                    results.append((ref, True, ""))
                continue
            if new not in OBJECTS:
                results.append((ref, False, "new object not found"))
                continue
            current = repo.refs.get(ref)
            if current is None:
                if old != ZERO_OID:
                    results.append((ref, False, "reference was moved"))
                    continue
            else:
                if old == ZERO_OID:
                    results.append((ref, False, "reference already exists"))
                    continue
                if current != old:
                    results.append((ref, False, "reference was moved"))
                    continue
                if ref.startswith("refs/heads/") and not is_ancestor(old, new):
                    results.append((ref, False, "non-fast-forward"))
                    continue
            repo.refs[ref] = new
            changed = True
            results.append((ref, True, ""))
        if changed:
            repo.bump()
    report = bytearray()
    report += pkt("unpack ok\n" if unpack_ok else "unpack error\n")
    for ref, ok, reason in results:
        if ok:
            report += pkt("ok " + ref + "\n")
        else:
            report += pkt("ng " + ref + " " + reason + "\n")
    report += PKT_FLUSH
    if "side-band-64k" in caps:
        return sideband_wrap(bytes(report), 1)
    return bytes(report)


# --------------------------------------------------------------------------
# REST v3

class HttpError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


def err(status, message):
    raise HttpError(status, message)


def parse_json_body(body):
    if body is None or body == b"":
        return {}
    try:
        value = json.loads(body.decode("utf-8"))
    except Exception:
        err(400, "Problems parsing JSON")
    if not isinstance(value, dict):
        err(400, "Problems parsing JSON")
    return value


def pagination_params(query):
    try:
        per_page = int(query.get("per_page", ["30"])[0])
    except ValueError:
        per_page = 30
    try:
        page = int(query.get("page", ["1"])[0])
    except ValueError:
        page = 1
    return max(1, min(per_page, 100)), max(1, page)


def link_header(host, path, per_page, page, total):
    last_page = max(1, (total + per_page - 1) // per_page)
    links = []
    base = "http://" + host + path
    if page < last_page:
        links.append('<%s?per_page=%d&page=%d>; rel="next"' % (base, per_page, page + 1))
        links.append('<%s?per_page=%d&page=%d>; rel="last"' % (base, per_page, last_page))
    if page > 1:
        links.append('<%s?per_page=%d&page=%d>; rel="prev"' % (base, per_page, page - 1))
        links.append('<%s?per_page=%d&page=%d>; rel="first"' % (base, per_page, 1))
    return ", ".join(links) if links else None


def rest_dispatch(method, parts, query, body, host):
    """parts: path segments after /api/v3. Returns (status, body_bytes, headers)."""
    if not parts:
        return 200, dumps_bytes({
            "current_user_url": "http://" + host + "/api/v3/user",
            "repository_url": "http://" + host + "/api/v3/repos/{owner}/{repo}",
        }), {"X-OAuth-Scopes": "repo, read:org"}
    if parts == ["meta"]:
        if method != "GET":
            err(404, "Not Found")
        return 200, dumps_bytes({"installed_version": INSTALLED_VERSION,
                                 "verifiable_password_authentication": False}), {}
    if parts == ["user"]:
        if method != "GET":
            err(404, "Not Found")
        return 200, dumps_bytes({"login": VIEWER_LOGIN, "id": VIEWER_ID,
                                 "name": VIEWER_NAME, "email": VIEWER_EMAIL,
                                 "type": "User"}), {}
    if parts == ["user", "repos"]:
        if method == "POST":
            data = parse_json_body(body)
            name = data.get("name")
            if not isinstance(name, str) or not name:
                err(422, "name is required")
            repo, created = create_repo(name, data.get("description") or "",
                                        data.get("private", False))
            if not created:
                err(422, "name already exists on this account")
            return 201, repo_json_bytes(repo), {}
        if method == "GET":
            per_page, page = pagination_params(query)
            all_repos = sorted(REPOS.values(), key=lambda r: r.created_tick)
            total = len(all_repos)
            start = (page - 1) * per_page
            items = all_repos[start:start + per_page]
            headers = {}
            link = link_header(host, "/api/v3/user/repos", per_page, page, total)
            if link:
                headers["Link"] = link
            return 200, dumps_bytes([repo_dict(r) for r in items]), headers
        err(404, "Not Found")
    if len(parts) >= 3 and parts[0] == "repos":
        owner, name = parts[1], parts[2]
        repo = get_repo(owner, name)
        rest = parts[3:]
        if not rest:
            if repo is None:
                err(404, "Not Found")
            if method == "GET":
                return 200, repo_json_bytes(repo), {}
            if method == "PATCH":
                data = parse_json_body(body)
                if "description" in data:
                    repo.description = data["description"] or ""
                if "private" in data:
                    repo.private = bool(data["private"])
                if "name" in data and isinstance(data["name"], str) and data["name"] != repo.name:
                    del REPOS[repo.name]
                    repo.name = data["name"]
                    REPOS[repo.name] = repo
                repo.repo_json = None
                return 200, repo_json_bytes(repo), {}
            if method == "DELETE":
                del REPOS[repo.name]
                return 204, b"", {}
            err(404, "Not Found")
        if repo is None:
            err(404, "Not Found")
        return repo_scoped_dispatch(repo, method, rest, query, body, host)
    err(404, "Not Found")


def repo_scoped_dispatch(repo, method, rest, query, body, host):
    # branches
    if rest == ["branches"] and method == "GET":
        out = []
        for ref, oid in sorted(repo.refs.items()):
            if ref.startswith("refs/heads/"):
                out.append({"name": ref[len("refs/heads/"):],
                            "commit": {"sha": oid}, "protected": False})
        return 200, dumps_bytes(out), {}
    if len(rest) >= 2 and rest[0] == "branches" and method == "GET":
        branch = "/".join(rest[1:])
        oid = branch_tip(repo, branch)
        if oid is None:
            err(404, "Not Found")
        return 200, dumps_bytes({"name": branch, "commit": {"sha": oid},
                                 "protected": False}), {}
    # git refs
    if rest == ["git", "refs"] and method == "POST":
        data = parse_json_body(body)
        ref = data.get("ref", "")
        sha = data.get("sha", "")
        if not isinstance(ref, str) or not ref.startswith("refs/"):
            err(422, "ref is invalid")
        if sha not in OBJECTS:
            err(422, "sha is not a known object")
        repo.refs[ref] = sha
        repo.bump()
        return 201, dumps_bytes({"ref": ref, "object": {"sha": sha, "type": "commit"}}), {}
    if len(rest) >= 3 and rest[0] == "git" and rest[1] == "refs" and method == "GET":
        ref = "refs/" + "/".join(rest[2:])
        oid = repo.refs.get(ref)
        if oid is None:
            err(404, "Not Found")
        return 200, dumps_bytes({"ref": ref, "object": {"sha": oid, "type": "commit"}}), {}
    # commits
    if rest == ["commits"] and method == "GET":
        sha_param = query.get("sha", [None])[0]
        if sha_param:
            tip = repo.refs.get("refs/heads/" + sha_param) or \
                repo.refs.get(sha_param) or \
                (sha_param if sha_param in OBJECTS else None)
        else:
            tip = head_oid(repo)
        if tip is None:
            return 200, dumps_bytes([]), {}
        commit_set = ancestors_incl(peel_to_commit(tip))
        ordered = sorted(commit_set, key=lambda c: commit_head(c)[1], reverse=True)
        out = []
        for oid in ordered:
            obj = OBJECTS[oid]
            head, _, message = obj[1].partition(b"\n\n")
            author_line = ""
            committer_line = ""
            for line in head.split(b"\n"):
                if line.startswith(b"author "):
                    author_line = line[7:].decode()
                elif line.startswith(b"committer "):
                    committer_line = line[10:].decode()
            out.append({
                "sha": oid,
                "commit": {
                    "message": message.decode("utf-8", "replace"),
                    "author": {"name": author_line.rsplit(" <", 1)[0] if " <" in author_line else author_line},
                    "committer": {"name": committer_line.rsplit(" <", 1)[0] if " <" in committer_line else committer_line},
                    "tree": {"sha": commit_head(oid)[0]},
                },
                "parents": [{"sha": p} for p in commit_parents(oid)],
            })
        return 200, dumps_bytes(out), {}
    # contents
    if len(rest) >= 2 and rest[0] == "contents":
        path = "/".join(rest[1:])
        return contents_dispatch(repo, method, path, query, body)
    # labels
    if rest == ["labels"]:
        if method == "POST":
            data = parse_json_body(body)
            label_name = data.get("name")
            if not isinstance(label_name, str) or not label_name:
                err(422, "name is required")
            if label_name in repo.labels:
                err(422, "label already exists")
            repo.labels[label_name] = data.get("color") or "ededed"
            return 201, dumps_bytes({"name": label_name,
                                     "color": repo.labels[label_name]}), {}
        if method == "GET":
            return 200, dumps_bytes([{"name": n, "color": c}
                                     for n, c in sorted(repo.labels.items())]), {}
        err(404, "Not Found")
    # issues
    if rest == ["issues"]:
        if method == "POST":
            data = parse_json_body(body)
            return create_issue_rest(repo, data)
        if method == "GET":
            return list_issues_rest(repo, query)
        err(404, "Not Found")
    if len(rest) >= 2 and rest[0] == "issues":
        try:
            number = int(rest[1])
        except ValueError:
            err(404, "Not Found")
        issue = repo.issues.get(number)
        if len(rest) == 2:
            if issue is None:
                err(404, "Not Found")
            if method == "GET":
                return 200, issue_json_bytes(repo, issue), {}
            if method == "PATCH":
                data = parse_json_body(body)
                if "state" in data:
                    if data["state"] not in ("open", "closed"):
                        err(422, "state is invalid")
                    issue.state = data["state"]
                if "title" in data:
                    issue.title = data["title"]
                if "body" in data:
                    issue.body = data["body"]
                if "labels" in data:
                    names = data["labels"]
                    if isinstance(names, list):
                        for label_name in names:
                            if label_name not in repo.labels:
                                err(422, "label does not exist")
                        issue.labels = list(names)
                issue.json_cache = None
                return 200, issue_json_bytes(repo, issue), {}
            err(404, "Not Found")
        if len(rest) == 3 and rest[2] == "comments":
            if issue is None:
                err(404, "Not Found")
            if method == "POST":
                data = parse_json_body(body)
                comment_body = data.get("body")
                if not isinstance(comment_body, str):
                    err(422, "body is required")
                comment_id = repo.next_comment_id
                repo.next_comment_id += 1
                stamp = tick()
                issue.comments.append((comment_id, comment_body, stamp))
                return 201, dumps_bytes({
                    "id": comment_id, "body": comment_body,
                    "user": {"login": repo.owner, "id": VIEWER_ID},
                    "created_at": iso_of(stamp), "updated_at": iso_of(stamp),
                }), {}
            if method == "GET":
                out = [{
                    "id": cid, "body": cbody,
                    "user": {"login": repo.owner, "id": VIEWER_ID},
                    "created_at": iso_of(stamp), "updated_at": iso_of(stamp),
                } for cid, cbody, stamp in issue.comments]
                return 200, dumps_bytes(out), {}
            err(404, "Not Found")
        err(404, "Not Found")
    # pulls
    if rest == ["pulls"]:
        if method == "POST":
            data = parse_json_body(body)
            return create_pull_rest(repo, data)
        if method == "GET":
            state = query.get("state", ["open"])[0]
            out = []
            for pull in sorted(repo.pulls.values(), key=lambda p: p.number):
                if state == "open" and pull.state != "open":
                    continue
                if state == "closed" and pull.state != "closed":
                    continue
                out.append(pull_dict(repo, pull))
            return 200, dumps_bytes(out), {}
        err(404, "Not Found")
    if len(rest) >= 2 and rest[0] == "pulls":
        try:
            number = int(rest[1])
        except ValueError:
            err(404, "Not Found")
        pull = repo.pulls.get(number)
        if len(rest) == 2:
            if pull is None:
                err(404, "Not Found")
            if method == "GET":
                return 200, dumps_bytes(pull_dict(repo, pull)), {}
            if method == "PATCH":
                if pull is None:
                    err(404, "Not Found")
                data = parse_json_body(body)
                if "state" in data and data["state"] in ("open", "closed"):
                    pull.state = data["state"]
                if "title" in data:
                    pull.title = data["title"]
                if "body" in data:
                    pull.body = data["body"]
                return 200, dumps_bytes(pull_dict(repo, pull)), {}
            err(404, "Not Found")
        if pull is None:
            err(404, "Not Found")
        if len(rest) == 3 and rest[2] == "files" and method == "GET":
            files = pull_files(repo, pull)
            trimmed = [{k: f[k] for k in ("filename", "status", "additions",
                                           "deletions", "changes", "sha")}
                       for f in files]
            return 200, dumps_bytes(trimmed), {}
        if len(rest) == 3 and rest[2] == "merge" and method == "PUT":
            if pull.state != "open":
                err(405, "Pull Request is not open")
            commit = squash_merge(repo, pull)
            if commit is None:
                err(405, "Pull Request is not mergeable")
            pull.state = "closed"
            pull.merged = True
            pull.merge_commit_sha = commit
            pull.merged_tick = tick()
            return 200, dumps_bytes({"sha": commit, "merged": True,
                                     "message": "Pull Request successfully merged"}), {}
        err(404, "Not Found")
    err(404, "Not Found")


def create_issue_rest(repo, data):
    title = data.get("title")
    if not isinstance(title, str) or title == "":
        err(422, "title is required")
    body = data.get("body")
    if body is None:
        body = ""
    if not isinstance(body, str):
        err(422, "body is invalid")
    labels = data.get("labels") or []
    if not isinstance(labels, list):
        err(422, "labels is invalid")
    for label_name in labels:
        if label_name not in repo.labels:
            err(422, "label does not exist")
    number = repo.next_number
    repo.next_number += 1
    issue = Issue(number, title, body, labels)
    repo.issues[number] = issue
    return 201, issue_json_bytes(repo, issue), {}


def list_issues_rest(repo, query):
    state = query.get("state", ["open"])[0]
    sort = query.get("sort", ["created"])[0]
    direction = query.get("direction", ["desc"])[0]
    per_page, page = pagination_params(query)
    items = [i for i in repo.issues.values()
             if state == "all" or i.state == state]
    items.sort(key=lambda i: i.number)
    if sort == "created" and direction == "desc":
        items.reverse()
    elif sort == "created" and direction == "asc":
        pass
    else:
        items.reverse()
    start = (page - 1) * per_page
    items = items[start:start + per_page]
    return 200, dumps_bytes([issue_dict(repo, i) for i in items]), {}


def create_pull_rest(repo, data):
    title = data.get("title")
    head = data.get("head")
    base = data.get("base")
    if not isinstance(title, str) or not isinstance(head, str) or not isinstance(base, str):
        err(422, "title, head and base are required")
    head = head.split(":")[-1]
    base = base.split(":")[-1]
    if branch_tip(repo, head) is None:
        err(422, "head branch does not exist")
    base_tip = branch_tip(repo, base)
    if base_tip is None:
        err(422, "base branch does not exist")
    for pull in repo.pulls.values():
        if pull.head == head and pull.base == base and pull.state == "open":
            err(422, "A pull request already exists for this branch")
    number = repo.next_number
    repo.next_number += 1
    pull = Pull(number, title, data.get("body") or "", head, base, base_tip)
    repo.pulls[number] = pull
    return 201, dumps_bytes(pull_dict(repo, pull)), {}


def contents_dispatch(repo, method, path, query, body):
    branch = query.get("branch", [None])[0]
    ref = query.get("ref", [None])[0]
    if method == "PUT":
        data = parse_json_body(body)
        branch = data.get("branch") or branch or repo.default_branch
        content_b64 = data.get("content")
        message = data.get("message")
        if not isinstance(content_b64, str) or not isinstance(message, str):
            err(422, "content and message are required")
        try:
            raw = base64.b64decode(content_b64)
        except Exception:
            err(422, "content is not valid base64")
        tip = branch_tip(repo, branch)
        flat = {}
        if tip is not None:
            tree, _e = commit_head(tip)
            flat = flatten_tree(tree)
        existing = flat.get(path)
        sha_given = data.get("sha")
        if existing is not None:
            if sha_given is None:
                err(422, "sha is required when the file exists")
            if sha_given != existing[1]:
                err(409, "sha does not match the current file")
            status = 200
        else:
            if sha_given is not None:
                err(404, "Not Found")
            status = 201
        blob_oid = store_object("blob", raw)
        commit = commit_file_change(repo, branch, path, blob_oid, message)
        return status, dumps_bytes({
            "content": {"name": path.rsplit("/", 1)[-1], "path": path,
                        "sha": blob_oid, "size": len(raw), "type": "file",
                        "encoding": "base64"},
            "commit": {"sha": commit, "message": message},
        }), {}
    # resolve the ref to a tree
    if ref:
        tip = branch_tip(repo, ref)
        if tip is None and ref in OBJECTS and OBJECTS[ref][0] == "commit":
            tip = ref
        if tip is None and ref in repo.refs:
            tip = repo.refs[ref]
    elif branch:
        tip = branch_tip(repo, branch)
    else:
        tip = head_oid(repo)
    if tip is None:
        err(404, "Not Found")
    tree_oid, _e = commit_head(tip)
    flat = flatten_tree(tree_oid)
    if method == "GET":
        entry = flat.get(path)
        if entry is not None:
            data = OBJECTS[entry[1]][1]
            return 200, dumps_bytes({
                "type": "file", "encoding": "base64",
                "content": base64.b64encode(data).decode(),
                "sha": entry[1], "size": len(data),
                "name": path.rsplit("/", 1)[-1], "path": path,
            }), {}
        prefix = path.rstrip("/") + "/"
        children = {}
        for candidate, value in flat.items():
            if candidate.startswith(prefix):
                rest_name = candidate[len(prefix):]
                head_name = rest_name.split("/", 1)[0]
                if "/" in rest_name:
                    children[head_name] = ("dir", None)
                else:
                    children[head_name] = ("file", value[1])
        if children or path == "":
            out = []
            for child_name in sorted(children):
                kind, sha = children[child_name]
                item = {"type": kind, "name": child_name,
                        "path": prefix + child_name,
                        "sha": sha if sha else tree_oid}
                out.append(item)
            return 200, dumps_bytes(out), {}
        err(404, "Not Found")
    if method == "DELETE":
        data = parse_json_body(body)
        message = data.get("message")
        sha_given = data.get("sha")
        entry = flat.get(path)
        if entry is None:
            err(404, "Not Found")
        if not isinstance(message, str) or sha_given is None:
            err(422, "message and sha are required")
        if sha_given != entry[1]:
            err(409, "sha does not match the current file")
        target_branch = branch or repo.default_branch
        commit = commit_file_change(repo, target_branch, path, None, message)
        return 200, dumps_bytes({"content": None,
                                 "commit": {"sha": commit, "message": message}}), {}
    err(404, "Not Found")


# --------------------------------------------------------------------------
# GraphQL

class GqlError(Exception):
    pass


_GQL_TOKEN_RE = re.compile(r"""
    (?P<comment>\#[^\n]*)
  | (?P<name>[_A-Za-z][_0-9A-Za-z]*)
  | (?P<float>-?(?:0|[1-9][0-9]*)\.[0-9]+(?:[eE][+-]?[0-9]+)?)
  | (?P<int>-?(?:0|[1-9][0-9]*))
  | (?P<string>"(?:\\.|[^"\\])*")
  | (?P<spread>\.\.\.)
  | (?P<punct>[!$():=@\[\]{}|])
  | (?P<skip>[\s,]+)
""", re.VERBOSE)


def gql_tokenize(text):
    tokens = []
    pos = 0
    while pos < len(text):
        match = _GQL_TOKEN_RE.match(text, pos)
        if match is None:
            raise GqlError("Syntax error at %d" % pos)
        pos = match.end()
        kind = match.lastgroup
        if kind in ("comment", "skip"):
            continue
        value = match.group()
        if kind == "string":
            value = json.loads(value)
        elif kind == "int":
            value = int(value)
            kind = "number"
        elif kind == "float":
            value = float(value)
            kind = "number"
        tokens.append((kind, value))
    tokens.append(("eof", None))
    return tokens


class GqlParser:
    def __init__(self, text):
        self.tokens = gql_tokenize(text)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def next(self):
        token = self.tokens[self.pos]
        self.pos += 1
        return token

    def expect_punct(self, ch):
        kind, value = self.next()
        if kind != "punct" or value != ch:
            raise GqlError("Expected %s" % ch)

    def expect_name(self):
        kind, value = self.next()
        if kind != "name":
            raise GqlError("Expected a name")
        return value

    def parse_document(self):
        operations = []
        fragments = {}
        while self.peek()[0] != "eof":
            kind, value = self.peek()
            if kind == "punct" and value == "{":
                operations.append(("query", None, {}, self.parse_selection_set()))
            elif kind == "name" and value in ("query", "mutation", "subscription"):
                op_type = self.next()[1]
                name = None
                if self.peek()[0] == "name":
                    name = self.next()[1]
                variables = {}
                if self.peek() == ("punct", "("):
                    variables = self.parse_variable_definitions()
                self.skip_directives()
                operations.append((op_type, name, variables, self.parse_selection_set()))
            elif kind == "name" and value == "fragment":
                self.next()
                frag_name = self.expect_name()
                if self.expect_name() != "on":
                    raise GqlError("Expected 'on' in fragment")
                type_condition = self.expect_name()
                self.skip_directives()
                fragments[frag_name] = (type_condition, self.parse_selection_set())
            else:
                raise GqlError("Unexpected token %r" % (value,))
        return operations, fragments

    def parse_variable_definitions(self):
        self.expect_punct("(")
        definitions = {}
        while self.peek() != ("punct", ")"):
            self.expect_punct("$")
            name = self.expect_name()
            self.expect_punct(":")
            self.parse_type()
            default = None
            if self.peek() == ("punct", "="):
                self.next()
                default = self.parse_value(const=True)
            self.skip_directives()
            definitions[name] = default
        self.next()
        return definitions

    def parse_type(self):
        if self.peek() == ("punct", "["):
            self.next()
            self.parse_type()
            self.expect_punct("]")
        else:
            self.expect_name()
        if self.peek() == ("punct", "!"):
            self.next()

    def skip_directives(self):
        while self.peek() == ("punct", "@"):
            self.next()
            self.expect_name()
            if self.peek() == ("punct", "("):
                self.parse_arguments()

    def parse_selection_set(self):
        self.expect_punct("{")
        selections = []
        while self.peek() != ("punct", "}"):
            selections.append(self.parse_selection())
        self.next()
        return selections

    def parse_selection(self):
        if self.peek()[0] == "spread":
            self.next()
            if self.peek() == ("name", "on"):
                self.next()
                type_condition = self.expect_name()
                self.skip_directives()
                return ("inline", type_condition, self.parse_selection_set())
            name = self.expect_name()
            self.skip_directives()
            return ("spread", name)
        name = self.expect_name()
        alias = None
        if self.peek() == ("punct", ":"):
            self.next()
            alias = name
            name = self.expect_name()
        args = {}
        if self.peek() == ("punct", "("):
            args = self.parse_arguments()
        self.skip_directives()
        selections = []
        if self.peek() == ("punct", "{"):
            selections = self.parse_selection_set()
        return ("field", alias, name, args, selections)

    def parse_arguments(self):
        self.expect_punct("(")
        args = {}
        while self.peek() != ("punct", ")"):
            name = self.expect_name()
            self.expect_punct(":")
            args[name] = self.parse_value()
        self.next()
        return args

    def parse_value(self, const=False):
        kind, value = self.next()
        if kind == "punct" and value == "$":
            return ("var", self.expect_name())
        if kind == "number" or kind == "string":
            return value
        if kind == "name":
            if value == "true":
                return True
            if value == "false":
                return False
            if value == "null":
                return None
            return ("enum", value)
        if kind == "punct" and value == "[":
            items = []
            while self.peek() != ("punct", "]"):
                items.append(self.parse_value(const))
            self.next()
            return items
        if kind == "punct" and value == "{":
            obj = {}
            while self.peek() != ("punct", "}"):
                key = self.expect_name()
                self.expect_punct(":")
                obj[key] = self.parse_value(const)
            self.next()
            return obj
        raise GqlError("Unexpected value token %r" % (value,))


def gql_resolve_value(value, variables):
    if isinstance(value, tuple):
        if value[0] == "var":
            return variables.get(value[1])
        if value[0] == "enum":
            return value[1]
    if isinstance(value, list):
        return [gql_resolve_value(item, variables) for item in value]
    if isinstance(value, dict):
        return {key: gql_resolve_value(item, variables) for key, item in value.items()}
    return value


# --- global ids -------------------------------------------------------------

def gid(kind, *parts):
    raw = kind + ":" + ":".join(str(p) for p in parts)
    return base64.b64encode(raw.encode()).decode()


def gid_parse(value):
    try:
        raw = base64.b64decode(value.encode()).decode()
    except Exception:
        return None
    parts = raw.split(":")
    return parts[0], parts[1:]


# --- schema -----------------------------------------------------------------

GQL_TYPE_FIELDS = {
    "Query": ["viewer", "repository", "node", "search", "__type", "__schema"],
    "Mutation": ["createIssue", "closeIssue", "createPullRequest",
                 "mergePullRequest", "addComment"],
    "User": ["id", "login", "name", "email"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                   "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                   "isPrivate", "description", "issue", "issues", "pullRequest",
                   "pullRequests", "url", "createdAt", "updatedAt"],
    "Ref": ["name", "target", "prefix"],
    "Issue": ["id", "number", "title", "state", "body", "author", "labels",
              "comments", "createdAt", "updatedAt", "url"],
    "IssueComment": ["id", "body", "author", "createdAt", "updatedAt"],
    "IssueConnection": ["nodes", "edges", "pageInfo", "totalCount"],
    "IssueEdge": ["node", "cursor"],
    "PullRequest": ["id", "number", "title", "body", "state", "merged",
                    "mergeable", "headRefName", "baseRefName", "files",
                    "mergeCommit", "createdAt", "updatedAt", "url"],
    "PullRequestConnection": ["nodes", "edges", "pageInfo", "totalCount"],
    "PullRequestEdge": ["node", "cursor"],
    "PullRequestChangedFile": ["path", "additions", "deletions"],
    "PageInfo": ["hasNextPage", "hasPreviousPage", "startCursor", "endCursor"],
    "CreateIssuePayload": ["issue", "clientMutationId"],
    "CloseIssuePayload": ["issue", "clientMutationId"],
    "CreatePullRequestPayload": ["pullRequest", "clientMutationId"],
    "MergePullRequestPayload": ["pullRequest", "clientMutationId"],
    "AddCommentPayload": ["commentEdge", "clientMutationId", "subject"],
    "CommentEdge": ["node", "cursor"],
    "__Type": ["name", "kind", "description", "fields", "enumValues",
               "possibleTypes", "inputFields", "ofType", "specifiedByURL"],
    "__Field": ["name", "description", "args", "type", "isDeprecated",
                "deprecationReason"],
    "__EnumValue": ["name", "description", "isDeprecated", "deprecationReason"],
    "__Schema": ["types", "queryType", "mutationType"],
}

GQL_ENUMS = {
    "IssueState": ["OPEN", "CLOSED"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
    "MergeableState": ["MERGEABLE", "CONFLICTING", "UNKNOWN"],
    "PullRequestMergeMethod": ["MERGE", "SQUASH", "REBASE"],
    "RepositoryPermission": ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"],
    "SearchType": ["ISSUE", "PULL_REQUEST", "REPOSITORY", "USER", "DISCUSSION", "CODE"],
    "IssueOrderField": ["CREATED_AT", "UPDATED_AT", "COMMENTS"],
    "OrderDirection": ["ASC", "DESC"],
}

GQL_KINDS = {name: "OBJECT" for name in GQL_TYPE_FIELDS}
for _enum_name in GQL_ENUMS:
    GQL_KINDS[_enum_name] = "ENUM"
GQL_KINDS["Node"] = "INTERFACE"


def gql_type_object(name):
    if name not in GQL_KINDS:
        return None
    obj = {"__gql_type": "__Type", "name": name, "kind": GQL_KINDS[name]}
    return obj


# --- execution ---------------------------------------------------------------

class GqlContext:
    def __init__(self, variables, fragments):
        self.variables = variables
        self.fragments = fragments
        self.errors = []


def gql_cursor(index):
    return base64.b64encode(("cursor:" + str(index)).encode()).decode()


def gql_cursor_index(cursor):
    try:
        raw = base64.b64decode(cursor.encode()).decode()
        if raw.startswith("cursor:"):
            return int(raw[len("cursor:"):])
    except Exception:
        pass
    return None


def repo_gql_object(repo):
    return {"__gql_type": "Repository", "repo": repo}


def issue_gql_object(repo, issue):
    return {"__gql_type": "Issue", "repo": repo, "issue": issue}


def pull_gql_object(repo, pull):
    return {"__gql_type": "PullRequest", "repo": repo, "pull": pull}


def find_repo_by_gid(value):
    parsed = gid_parse(value) if isinstance(value, str) else None
    if not parsed or parsed[0] != "Repository":
        return None
    try:
        db_id = int(parsed[1][0])
    except (ValueError, IndexError):
        return None
    for repo in REPOS.values():
        if repo.db_id == db_id:
            return repo
    return None


def find_issue_by_gid(value):
    parsed = gid_parse(value) if isinstance(value, str) else None
    if not parsed or parsed[0] != "Issue":
        return None
    try:
        db_id = int(parsed[1][0])
        number = int(parsed[1][1])
    except (ValueError, IndexError):
        return None
    for repo in REPOS.values():
        if repo.db_id == db_id:
            issue = repo.issues.get(number)
            if issue is not None:
                return repo, issue
    return None


def find_pull_by_gid(value):
    parsed = gid_parse(value) if isinstance(value, str) else None
    if not parsed or parsed[0] != "PullRequest":
        return None
    try:
        db_id = int(parsed[1][0])
        number = int(parsed[1][1])
    except (ValueError, IndexError):
        return None
    for repo in REPOS.values():
        if repo.db_id == db_id:
            pull = repo.pulls.get(number)
            if pull is not None:
                return repo, pull
    return None


def gql_field_value(ctx, obj, type_name, field, args):
    """Resolve one field on one runtime object; returns a Python value
    (dicts carry __gql_type for composite values)."""
    if field == "__typename":
        return type_name
    if type_name == "Query":
        if field == "viewer":
            return {"__gql_type": "User"}
        if field == "repository":
            repo = get_repo(args.get("owner"), args.get("name"))
            return repo_gql_object(repo) if repo is not None else None
        if field == "node":
            node_id = args.get("id")
            repo = find_repo_by_gid(node_id)
            if repo is not None:
                return repo_gql_object(repo)
            found = find_issue_by_gid(node_id)
            if found is not None:
                return issue_gql_object(found[0], found[1])
            found = find_pull_by_gid(node_id)
            if found is not None:
                return pull_gql_object(found[0], found[1])
            return None
        if field == "__type":
            return gql_type_object(args.get("name"))
        if field == "__schema":
            return {"__gql_type": "__Schema"}
        if field == "search":
            return {"__gql_type": "SearchResultItemConnection", "nodes": []}
    if type_name == "Mutation":
        return gql_mutation(ctx, field, args)
    if type_name == "User":
        if field == "id":
            return gid("User", VIEWER_ID)
        if field == "login":
            return VIEWER_LOGIN
        if field == "name":
            return VIEWER_NAME
        if field == "email":
            return VIEWER_EMAIL
    if type_name == "Repository":
        repo = obj["repo"]
        if field == "id":
            return gid("Repository", repo.db_id)
        if field == "databaseId":
            return repo.db_id
        if field == "name":
            return repo.name
        if field == "nameWithOwner":
            return repo.owner + "/" + repo.name
        if field == "owner":
            return {"__gql_type": "User"}
        if field == "defaultBranchRef":
            if head_oid(repo) is None:
                return None
            return {"__gql_type": "Ref", "name": repo.default_branch}
        if field == "viewerPermission":
            return "ADMIN"
        if field == "hasIssuesEnabled":
            return True
        if field == "isPrivate":
            return repo.private
        if field == "description":
            return repo.description
        if field == "url":
            return "http://forge.local/" + repo.owner + "/" + repo.name
        if field in ("createdAt", "updatedAt"):
            return iso_of(repo.created_tick)
        if field == "issue":
            issue = repo.issues.get(args.get("number"))
            return issue_gql_object(repo, issue) if issue is not None else None
        if field == "issues":
            return gql_issues_connection(repo, args)
        if field == "pullRequest":
            pull = repo.pulls.get(args.get("number"))
            return pull_gql_object(repo, pull) if pull is not None else None
        if field == "pullRequests":
            return gql_pulls_connection(repo, args)
    if type_name == "Ref":
        if field == "name":
            return obj["name"]
        if field == "prefix":
            return "refs/heads/"
        if field == "target":
            return None
    if type_name == "Issue":
        repo, issue = obj["repo"], obj["issue"]
        if field == "id":
            return gid("Issue", repo.db_id, issue.number)
        if field == "number":
            return issue.number
        if field == "title":
            return issue.title
        if field == "state":
            return issue.state.upper()
        if field == "body":
            return issue.body
        if field == "author":
            return {"__gql_type": "User"}
        if field in ("createdAt", "updatedAt"):
            return iso_of(issue.created_tick)
        if field == "url":
            return "http://forge.local/%s/%s/issues/%d" % (repo.owner, repo.name, issue.number)
        if field == "labels":
            return {"__gql_type": "LabelConnection",
                    "nodes": [{"__gql_type": "Label", "name": n} for n in issue.labels]}
        if field == "comments":
            return {"__gql_type": "IssueCommentConnection",
                    "nodes": [comment_gql_object(repo, issue, c) for c in issue.comments]}
    if type_name == "IssueComment":
        if field == "id":
            return obj["gid"]
        if field == "body":
            return obj["body"]
        if field == "author":
            return {"__gql_type": "User"}
        if field in ("createdAt", "updatedAt"):
            return iso_of(obj["tick"])
    if type_name == "PullRequest":
        repo, pull = obj["repo"], obj["pull"]
        if field == "id":
            return gid("PullRequest", repo.db_id, pull.number)
        if field == "number":
            return pull.number
        if field == "title":
            return pull.title
        if field == "body":
            return pull.body
        if field == "state":
            if pull.merged:
                return "MERGED"
            return pull.state.upper()
        if field == "merged":
            return pull.merged
        if field == "mergeable":
            if pull.merged or pull.state != "open":
                return "UNKNOWN"
            conflicts, _merged = merge_analysis(repo, pull)
            return "CONFLICTING" if conflicts else "MERGEABLE"
        if field == "headRefName":
            return pull.head
        if field == "baseRefName":
            return pull.base
        if field == "files":
            files = pull_files(repo, pull)
            first = args.get("first")
            if isinstance(first, int):
                files = files[:first]
            return {"__gql_type": "PullRequestChangedFileConnection",
                    "nodes": [{"__gql_type": "PullRequestChangedFile",
                               "path": f["filename"], "additions": f["additions"],
                               "deletions": f["deletions"]} for f in files],
                    "totalCount": len(files)}
        if field in ("createdAt", "updatedAt"):
            return iso_of(pull.created_tick)
        if field == "url":
            return "http://forge.local/%s/%s/pull/%d" % (repo.owner, repo.name, pull.number)
    if type_name in ("IssueConnection", "PullRequestConnection"):
        if field == "nodes":
            return obj["nodes"]
        if field == "totalCount":
            return obj["totalCount"]
        if field == "pageInfo":
            return obj["pageInfo"]
        if field == "edges":
            return obj["edges"]
    if type_name in ("PullRequestChangedFileConnection",):
        if field == "nodes":
            return obj["nodes"]
        if field == "totalCount":
            return obj["totalCount"]
    if type_name == "PullRequestChangedFile":
        if field in ("path", "additions", "deletions"):
            return obj[field]
    if type_name == "PageInfo":
        if field in ("hasNextPage", "hasPreviousPage", "startCursor", "endCursor"):
            return obj[field]
    if type_name in ("IssueEdge", "PullRequestEdge", "CommentEdge"):
        if field == "node":
            return obj["node"]
        if field == "cursor":
            return obj["cursor"]
    if type_name in ("CreateIssuePayload", "CloseIssuePayload"):
        if field == "issue":
            return obj.get("issue")
        if field == "clientMutationId":
            return obj.get("clientMutationId")
    if type_name in ("CreatePullRequestPayload", "MergePullRequestPayload"):
        if field == "pullRequest":
            return obj.get("pullRequest")
        if field == "clientMutationId":
            return obj.get("clientMutationId")
    if type_name == "AddCommentPayload":
        if field == "commentEdge":
            return obj.get("commentEdge")
        if field == "clientMutationId":
            return obj.get("clientMutationId")
        if field == "subject":
            return obj.get("subject")
    if type_name == "__Type":
        if field == "name":
            return obj["name"]
        if field == "kind":
            return obj["kind"]
        if field == "description":
            return None
        if field == "fields":
            names = GQL_TYPE_FIELDS.get(obj["name"])
            if names is None:
                return None
            return [{"__gql_type": "__Field", "name": n} for n in names]
        if field == "enumValues":
            values = GQL_ENUMS.get(obj["name"])
            if values is None:
                return None
            return [{"__gql_type": "__EnumValue", "name": n} for n in values]
        if field == "possibleTypes":
            return []
        if field == "inputFields":
            return None
        if field == "ofType":
            return None
        if field == "specifiedByURL":
            return None
    if type_name == "__Field":
        if field == "name":
            return obj["name"]
        if field == "description":
            return None
        if field == "isDeprecated":
            return False
        if field == "deprecationReason":
            return None
        if field in ("args",):
            return []
        if field == "type":
            return None
    if type_name == "__EnumValue":
        if field == "name":
            return obj["name"]
        if field == "description":
            return None
        if field == "isDeprecated":
            return False
        if field == "deprecationReason":
            return None
    if type_name == "__Schema":
        if field == "types":
            return [gql_type_object(n) for n in sorted(GQL_KINDS)]
        if field == "queryType":
            return gql_type_object("Query")
        if field == "mutationType":
            return gql_type_object("Mutation")
    if isinstance(obj, dict) and field in obj and not field.startswith("__"):
        return obj[field]
    raise GqlError("Field '%s' doesn't exist on type '%s'" % (field, type_name))


def comment_gql_object(repo, issue, comment):
    cid, body, stamp = comment
    return {"__gql_type": "IssueComment", "body": body, "tick": stamp,
            "gid": gid("IssueComment", repo.db_id, issue.number, cid)}


def _connection(items, args, node_type):
    first = args.get("first")
    after = args.get("after")
    start = 0
    if isinstance(after, str):
        index = gql_cursor_index(after)
        if index is not None:
            start = index + 1
    total = len(items)
    if isinstance(first, int) and first >= 0:
        page = items[start:start + first]
    else:
        page = items[start:]
    end_index = start + len(page) - 1
    page_info = {
        "__gql_type": "PageInfo",
        "hasNextPage": start + len(page) < total,
        "hasPreviousPage": start > 0,
        "startCursor": gql_cursor(start) if page else None,
        "endCursor": gql_cursor(end_index) if page else None,
    }
    edges = [{"__gql_type": node_type + "Edge", "node": node,
              "cursor": gql_cursor(start + i)} for i, node in enumerate(page)]
    return {"__gql_type": node_type + "Connection", "nodes": page,
            "edges": edges, "pageInfo": page_info, "totalCount": total}


def gql_issues_connection(repo, args):
    states = args.get("states")
    items = [i for i in repo.issues.values()
             if not states or i.state.upper() in states]
    order_by = args.get("orderBy") or {}
    direction = order_by.get("direction", "ASC") if isinstance(order_by, dict) else "ASC"
    items.sort(key=lambda i: i.number)
    if direction == "DESC":
        items.reverse()
    nodes = [issue_gql_object(repo, i) for i in items]
    return _connection(nodes, args, "Issue")


def gql_pulls_connection(repo, args):
    states = args.get("states")
    pulls = sorted(repo.pulls.values(), key=lambda p: p.number)
    if states:
        wanted = set()
        for state in states:
            wanted.add(state)
        pulls = [p for p in pulls
                 if ("MERGED" if p.merged else p.state.upper()) in wanted]
    nodes = [pull_gql_object(repo, p) for p in pulls]
    return _connection(nodes, args, "PullRequest")


def gql_mutation(ctx, field, args):
    inp = args.get("input") or {}
    if field == "createIssue":
        repo = find_repo_by_gid(inp.get("repositoryId"))
        if repo is None:
            raise GqlError("Repository not found")
        number = repo.next_number
        repo.next_number += 1
        issue = Issue(number, inp.get("title") or "", inp.get("body") or "", [])
        repo.issues[number] = issue
        return {"__gql_type": "CreateIssuePayload",
                "issue": issue_gql_object(repo, issue),
                "clientMutationId": inp.get("clientMutationId")}
    if field == "closeIssue":
        found = find_issue_by_gid(inp.get("issueId"))
        if found is None:
            raise GqlError("Issue not found")
        repo, issue = found
        issue.state = "closed"
        issue.json_cache = None
        return {"__gql_type": "CloseIssuePayload",
                "issue": issue_gql_object(repo, issue),
                "clientMutationId": inp.get("clientMutationId")}
    if field == "createPullRequest":
        repo = find_repo_by_gid(inp.get("repositoryId"))
        if repo is None:
            raise GqlError("Repository not found")
        head = inp.get("headRefName")
        base = inp.get("baseRefName")
        base_tip = branch_tip(repo, base) if base else None
        if base_tip is None or branch_tip(repo, head) is None:
            raise GqlError("Invalid head or base ref")
        number = repo.next_number
        repo.next_number += 1
        pull = Pull(number, inp.get("title") or "", inp.get("body") or "",
                    head, base, base_tip)
        repo.pulls[number] = pull
        return {"__gql_type": "CreatePullRequestPayload",
                "pullRequest": pull_gql_object(repo, pull),
                "clientMutationId": inp.get("clientMutationId")}
    if field == "mergePullRequest":
        found = find_pull_by_gid(inp.get("pullRequestId"))
        if found is None:
            raise GqlError("Pull request not found")
        repo, pull = found
        if pull.state == "open":
            commit = squash_merge(repo, pull)
            if commit is None:
                raise GqlError("Pull request is not mergeable")
            pull.state = "closed"
            pull.merged = True
            pull.merge_commit_sha = commit
            pull.merged_tick = tick()
        return {"__gql_type": "MergePullRequestPayload",
                "pullRequest": pull_gql_object(repo, pull),
                "clientMutationId": inp.get("clientMutationId")}
    if field == "addComment":
        found = find_issue_by_gid(inp.get("subjectId"))
        if found is None:
            raise GqlError("Subject not found")
        repo, issue = found
        comment_id = repo.next_comment_id
        repo.next_comment_id += 1
        stamp = tick()
        comment = (comment_id, inp.get("body") or "", stamp)
        issue.comments.append(comment)
        node = comment_gql_object(repo, issue, comment)
        return {"__gql_type": "AddCommentPayload",
                "commentEdge": {"__gql_type": "CommentEdge", "node": node,
                                "cursor": gql_cursor(len(issue.comments) - 1)},
                "clientMutationId": inp.get("clientMutationId"),
                "subject": issue_gql_object(repo, issue)}
    raise GqlError("Field '%s' doesn't exist on type 'Mutation'" % field)


# types that may appear as a runtime object but are not in the field table
for _extra in ("Label", "LabelConnection", "IssueCommentConnection",
               "PullRequestChangedFileConnection", "SearchResultItemConnection"):
    GQL_TYPE_FIELDS.setdefault(_extra, ["id", "name", "nodes", "totalCount"])
    GQL_KINDS.setdefault(_extra, "OBJECT")


def gql_execute_selection(ctx, obj, type_name, selections, out):
    for selection in selections:
        kind = selection[0]
        if kind == "inline":
            _tag, condition, sub = selection
            if condition == type_name or condition == "Node":
                gql_execute_selection(ctx, obj, type_name, sub, out)
            continue
        if kind == "spread":
            fragment = ctx.fragments.get(selection[1])
            if fragment is not None:
                condition, sub = fragment
                if condition == type_name or condition == "Node":
                    gql_execute_selection(ctx, obj, type_name, sub, out)
            continue
        _tag, alias, name, raw_args, sub = selection
        key = alias or name
        args = {k: gql_resolve_value(v, ctx.variables) for k, v in raw_args.items()}
        known = name == "__typename" or name in GQL_TYPE_FIELDS.get(type_name, [])
        if not known:
            ctx.errors.append({
                "message": "Field '%s' doesn't exist on type '%s'" % (name, type_name),
                "path": [key],
            })
            out[key] = None
            continue
        try:
            value = gql_field_value(ctx, obj, type_name, name, args)
        except GqlError as exc:
            ctx.errors.append({"message": str(exc), "path": [key]})
            out[key] = None
            continue
        out[key] = gql_complete(ctx, value, sub)
    return out


def gql_complete(ctx, value, selections):
    if value is None:
        return None
    if isinstance(value, list):
        return [gql_complete(ctx, item, selections) for item in value]
    if isinstance(value, dict) and "__gql_type" in value:
        if not selections:
            return {}
        out = {}
        return gql_execute_selection(ctx, value, value["__gql_type"], selections, out)
    return value


def gql_run_operation(document, variables):
    operations, fragments = GqlParser(document).parse_document()
    if not operations:
        raise GqlError("No operation found")
    op_type, _name, var_defs, selections = operations[0]
    merged_vars = {}
    for var_name, default in var_defs.items():
        if default is not None:
            merged_vars[var_name] = gql_resolve_value(default, {})
    merged_vars.update(variables or {})
    ctx = GqlContext(merged_vars, fragments)
    root_type = "Mutation" if op_type == "mutation" else "Query"
    root = {"__gql_type": root_type}
    data = gql_execute_selection(ctx, root, root_type, selections, {})
    result = {"data": data}
    if ctx.errors:
        result["errors"] = ctx.errors
    return result


def graphql_dispatch(body):
    """Returns (status, body_bytes). Handles single and batched operations."""
    try:
        payload = json.loads(body.decode("utf-8")) if body else None
    except Exception:
        return 400, dumps_bytes({"message": "Problems parsing JSON"})
    if isinstance(payload, list):
        results = []
        for operation in payload:
            results.append(_gql_one(operation))
        return 200, dumps_bytes(results)
    if isinstance(payload, dict):
        return 200, dumps_bytes(_gql_one(payload))
    return 400, dumps_bytes({"message": "Problems parsing JSON"})


def _gql_one(operation):
    if not isinstance(operation, dict) or not isinstance(operation.get("query"), str):
        return {"data": None, "errors": [{"message": "No query provided"}]}
    try:
        return gql_run_operation(operation["query"], operation.get("variables") or {})
    except GqlError as exc:
        return {"data": None, "errors": [{"message": str(exc)}]}
    except Exception as exc:  # a server bug must still answer GraphQL-shaped
        return {"data": None, "errors": [{"message": "Internal error: %s" % exc}]}


# --------------------------------------------------------------------------
# MCP

MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a new repository for the token owner.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "The repository name."},
                "description": {"type": "string", "description": "A short description."},
                "private": {"type": "boolean", "description": "Whether the repository is private."},
            },
            "required": ["name"],
        },
    },
    {
        "name": "get_repo",
        "description": "Get a repository by owner and name.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_issue",
        "description": "Create an issue in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "title": {"type": "string"},
                "body": {"type": "string"},
            },
            "required": ["owner", "repo", "title"],
        },
    },
    {
        "name": "list_issues",
        "description": "List the issues of a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "state": {"type": "string"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_pull_request",
        "description": "Open a pull request from a head branch into a base branch.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "title": {"type": "string"},
                "body": {"type": "string"},
                "head": {"type": "string"},
                "base": {"type": "string"},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Merge a pull request by number.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "pull_number": {"type": "integer"},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]

MCP_TOOLS_LIST_BYTES = dumps_bytes({"tools": MCP_TOOLS})
MCP_SERVER_INFO = {"name": "forge", "version": "3.0.0"}
MCP_SUPPORTED_VERSIONS = ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26"]


def mcp_tool_result(value):
    text = json.dumps(value, separators=(",", ":"), ensure_ascii=False)
    return {"content": [{"type": "text", "text": text}],
            "structuredContent": value, "isError": False}


def mcp_call_tool(name, args):
    """Returns a JSON-RPC result dict, or raises HttpError-like via
    (code, message) tuples encoded as GqlError for dispatch simplicity."""
    if name == "create_repo":
        repo_name = args.get("name")
        if not isinstance(repo_name, str) or not repo_name:
            raise GqlError("-32602: name is required")
        repo, _created = create_repo(repo_name, args.get("description") or "",
                                     args.get("private", False))
        return mcp_tool_result(repo_dict(repo))
    if name == "get_repo":
        owner, repo_name = args.get("owner"), args.get("repo")
        if not owner or not repo_name:
            raise GqlError("-32602: owner and repo are required")
        repo = get_repo(owner, repo_name)
        if repo is None:
            raise GqlError("-32602: repository not found")
        return mcp_tool_result(repo_dict(repo))
    if name == "create_issue":
        owner, repo_name, title = args.get("owner"), args.get("repo"), args.get("title")
        if not owner or not repo_name or not title:
            raise GqlError("-32602: owner, repo and title are required")
        repo = get_repo(owner, repo_name)
        if repo is None:
            raise GqlError("-32602: repository not found")
        number = repo.next_number
        repo.next_number += 1
        issue = Issue(number, title, args.get("body") or "", [])
        repo.issues[number] = issue
        return mcp_tool_result(issue_dict(repo, issue))
    if name == "list_issues":
        owner, repo_name = args.get("owner"), args.get("repo")
        if not owner or not repo_name:
            raise GqlError("-32602: owner and repo are required")
        repo = get_repo(owner, repo_name)
        if repo is None:
            raise GqlError("-32602: repository not found")
        state = args.get("state") or "open"
        items = [issue_dict(repo, i) for i in
                 sorted(repo.issues.values(), key=lambda x: x.number)
                 if state == "all" or i.state == state]
        return mcp_tool_result(items)
    if name == "create_pull_request":
        owner, repo_name = args.get("owner"), args.get("repo")
        title, head, base = args.get("title"), args.get("head"), args.get("base")
        if not owner or not repo_name or not title or not head or not base:
            raise GqlError("-32602: owner, repo, title, head and base are required")
        repo = get_repo(owner, repo_name)
        if repo is None:
            raise GqlError("-32602: repository not found")
        base_tip = branch_tip(repo, base)
        if base_tip is None or branch_tip(repo, head) is None:
            raise GqlError("-32602: invalid head or base branch")
        number = repo.next_number
        repo.next_number += 1
        pull = Pull(number, title, args.get("body") or "", head, base, base_tip)
        repo.pulls[number] = pull
        return mcp_tool_result(pull_dict(repo, pull))
    if name == "merge_pull_request":
        owner, repo_name = args.get("owner"), args.get("repo")
        number = args.get("pull_number")
        if not owner or not repo_name or number is None:
            raise GqlError("-32602: owner, repo and pull_number are required")
        repo = get_repo(owner, repo_name)
        if repo is None:
            raise GqlError("-32602: repository not found")
        pull = repo.pulls.get(int(number))
        if pull is None:
            raise GqlError("-32602: pull request not found")
        if pull.state == "open":
            commit = squash_merge(repo, pull)
            if commit is None:
                return {"content": [{"type": "text", "text": "Pull request is not mergeable"}],
                        "isError": True}
            pull.state = "closed"
            pull.merged = True
            pull.merge_commit_sha = commit
            pull.merged_tick = tick()
        return mcp_tool_result(pull_dict(repo, pull))
    raise GqlError("-32602: unknown tool " + str(name))


def mcp_dispatch(body):
    """Returns (status, body_bytes)."""
    try:
        payload = json.loads(body.decode("utf-8")) if body else None
    except Exception:
        return 400, dumps_bytes({"jsonrpc": "2.0", "id": None,
                                 "error": {"code": -32700, "message": "Parse error"}})
    if isinstance(payload, list):
        results = [mcp_handle_one(item) for item in payload
                   if isinstance(item, dict) and "id" in item]
        return 200, dumps_bytes(results)
    if not isinstance(payload, dict):
        return 400, dumps_bytes({"jsonrpc": "2.0", "id": None,
                                 "error": {"code": -32600, "message": "Invalid Request"}})
    if "id" not in payload:
        return 202, b""
    return 200, dumps_bytes(mcp_handle_one(payload))


def mcp_handle_one(request):
    req_id = request.get("id")
    method = request.get("method")
    params = request.get("params") or {}
    if method == "server/discover":
        result = {
            "resultType": "complete",
            "supportedVersions": MCP_SUPPORTED_VERSIONS,
            "capabilities": {"tools": {}},
            "serverInfo": MCP_SERVER_INFO,
            "_meta": {"io.modelcontextprotocol/serverInfo": MCP_SERVER_INFO},
        }
        return {"jsonrpc": "2.0", "id": req_id, "result": result}
    if method == "initialize":
        offered = params.get("protocolVersion")
        version = offered if offered in MCP_SUPPORTED_VERSIONS else MCP_SUPPORTED_VERSIONS[0]
        result = {"protocolVersion": version,
                  "capabilities": {"tools": {}},
                  "serverInfo": MCP_SERVER_INFO}
        return {"jsonrpc": "2.0", "id": req_id, "result": result}
    if method == "ping":
        return {"jsonrpc": "2.0", "id": req_id, "result": {}}
    if method == "tools/list":
        return {"jsonrpc": "2.0", "id": req_id,
                "result": json.loads(MCP_TOOLS_LIST_BYTES)}
    if method == "tools/call":
        name = params.get("name")
        arguments = params.get("arguments") or {}
        known = {tool["name"] for tool in MCP_TOOLS}
        if name not in known:
            return {"jsonrpc": "2.0", "id": req_id,
                    "error": {"code": -32602, "message": "Unknown tool: %s" % name}}
        try:
            result = mcp_call_tool(name, arguments)
        except GqlError as exc:
            message = str(exc)
            if message.startswith("-32602:"):
                return {"jsonrpc": "2.0", "id": req_id,
                        "error": {"code": -32602, "message": message[len("-32602:"):].strip()}}
            return {"jsonrpc": "2.0", "id": req_id,
                    "error": {"code": -32603, "message": message}}
        return {"jsonrpc": "2.0", "id": req_id, "result": result}
    return {"jsonrpc": "2.0", "id": req_id,
            "error": {"code": -32601, "message": "Method not found: %s" % method}}


# --------------------------------------------------------------------------
# fetch response caching wrapper

def fetch_cached(repo, body, version2):
    key = (repo.gen, hashlib.sha1(body).digest(), version2)
    cached = repo.fetch_cache.get(key)
    if cached is not None:
        return cached
    result = handle_fetch(repo, body, version2)
    if result is not None and len(repo.fetch_cache) < 1024:
        repo.fetch_cache[key] = result
    return result


def ls_refs_cached(repo, body):
    key = ("ls", repo.gen, hashlib.sha1(body).digest())
    cached = repo.fetch_cache.get(key)
    if cached is not None:
        return cached
    result = handle_ls_refs(repo, body)
    if result is not None and len(repo.fetch_cache) < 1024:
        repo.fetch_cache[key] = result
    return result


# --------------------------------------------------------------------------
# HTTP plumbing

_request_counter = [0]


def next_request_id():
    _request_counter[0] += 1
    return "req-%d" % _request_counter[0]


def authorized(headers):
    if not TOKEN:
        return True
    return headers.get("Authorization") == "Bearer " + TOKEN


class Headers(dict):
    """Header map with case-insensitive lookup; keys stored lowercased."""

    def get(self, key, default=None):
        return super().get(key.lower(), default)


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "forge/3.0"

    def setup(self):
        super().setup()
        try:
            self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass

    def handle_one_request(self):
        # Lean request parsing: the stock implementation routes headers
        # through the email package, which costs more per request than the
        # handlers themselves on the cached hot paths. Only the pieces the
        # application reads are extracted: method, target, a header dict,
        # and the keep-alive decision. The body is consumed by _route.
        try:
            raw = self.rfile.readline(65537)
            while raw == b"\r\n" or raw == b"\n":
                raw = self.rfile.readline(65537)
            if not raw:
                self.close_connection = True
                return
            parts = raw.decode("latin-1").split()
            if len(parts) != 3:
                self.close_connection = True
                return
            self.command, self.path, self.request_version = parts
            headers = Headers()
            while True:
                line = self.rfile.readline(65537)
                if line in (b"\r\n", b"\n", b""):
                    break
                name, sep, value = line.decode("latin-1").partition(":")
                if sep:
                    headers[name.strip().lower()] = value.strip()
            self.headers = headers
            connection = headers.get("connection", "").lower()
            if self.request_version >= "HTTP/1.1":
                self.close_connection = connection == "close"
            else:
                self.close_connection = connection != "keep-alive"
            if (headers.get("expect") or "").lower() == "100-continue":
                self.wfile.write(b"HTTP/1.1 100 Continue\r\n\r\n")
            method = getattr(self, "do_" + self.command, None)
            if method is None:
                self._send_json_error(501, "Unsupported method")
                return
            method()
        except (ConnectionError, BrokenPipeError, TimeoutError):
            self.close_connection = True

    def log_message(self, fmt, *args):
        pass

    # -- low-level helpers ---------------------------------------------------
    def _read_body(self):
        length = self.headers.get("Content-Length")
        if length is not None:
            try:
                count = int(length)
            except ValueError:
                return b""
            return self.rfile.read(count) if count > 0 else b""
        if (self.headers.get("Transfer-Encoding") or "").lower() == "chunked":
            out = bytearray()
            while True:
                size_line = self.rfile.readline(65536).strip()
                try:
                    size = int(size_line.split(b";")[0], 16)
                except ValueError:
                    break
                if size == 0:
                    while True:
                        trailer = self.rfile.readline(65536)
                        if trailer in (b"\r\n", b"\n", b""):
                            break
                    break
                out += self.rfile.read(size)
                self.rfile.readline(65536)
            return bytes(out)
        return b""

    def _send(self, status, body, content_type="application/json", extra=None):
        if os.environ.get("FORGE_DEBUG"):
            sys.stderr.write("%s %s -> %d (%d bytes)\n" % (self.command, self.path, status, len(body)))
            sys.stderr.flush()
        # One write for the whole response: a separate header flush would
        # leave the body queued behind TCP congestion control and cost a
        # delayed-ACK round trip per request.
        head = bytearray()
        head += ("HTTP/1.1 %d %s\r\n" % (status, STATUS_PHRASES.get(status, ""))).encode()
        if content_type is not None:
            head += ("Content-Type: %s\r\n" % content_type).encode()
        head += ("Content-Length: %d\r\n" % len(body)).encode()
        head += ("X-GitHub-Request-Id: %s\r\n" % next_request_id()).encode()
        if extra:
            for key, value in extra.items():
                head += ("%s: %s\r\n" % (key, value)).encode()
        head += b"\r\n"
        if self.command == "HEAD":
            self.wfile.write(bytes(head))
        else:
            self.wfile.write(bytes(head) + body)

    def _send_json_error(self, status, message):
        self._send(status, dumps_bytes({"message": message}))

    def send_error(self, code, message=None, explain=None):
        if os.environ.get("FORGE_DEBUG"):
            sys.stderr.write("send_error %d requestline=%r\n" % (code, getattr(self, "requestline", None)))
            sys.stderr.flush()
        self._send_json_error(code, message or "Error")

    # -- routing ---------------------------------------------------------------
    def _route(self, method):
        target = self.path
        if "?" in target:
            path_part, _, qs = target.partition("?")
            query = parse_qs(qs) if qs else {}
        else:
            path_part, query = target, {}
        path = unquote(path_part) if "%" in path_part else path_part
        host = self.headers.get("Host", "127.0.0.1")
        # Always consume the request body first: answering (e.g. a 401)
        # with body bytes still unread would corrupt the next request on
        # this keep-alive connection.
        body = self._read_body() if method in ("POST", "PUT", "PATCH", "DELETE") else b""
        try:
            if path == "/healthz":
                self._send(200, b'{"ok":true}')
                return
            if path == "/api/graphql":
                if method != "POST":
                    self._send_json_error(404, "Not Found")
                    return
                if not authorized(self.headers):
                    self._send_json_error(401, "Bad credentials")
                    return
                status, payload = graphql_dispatch(body)
                self._send(status, payload)
                return
            if path == "/mcp":
                if method == "DELETE":
                    self._send(204, b"", content_type=None)
                    return
                if method != "POST":
                    self._send_json_error(404, "Not Found")
                    return
                if not authorized(self.headers):
                    self._send_json_error(401, "Bad credentials")
                    return
                status, payload = mcp_dispatch(body)
                self._send(status, payload)
                return
            if path == "/api/v3" or path.startswith("/api/v3/"):
                if not authorized(self.headers):
                    self._send_json_error(401, "Bad credentials")
                    return
                parts = [p for p in path[len("/api/v3"):].split("/") if p != ""]
                try:
                    status, payload, extra = rest_dispatch(method, parts, query, body, host)
                except HttpError as exc:
                    self._send_json_error(exc.status, exc.message)
                    return
                self._send(status, payload, extra=extra)
                return
            if self._route_git(method, path, query, body):
                return
            self._send_json_error(404, "Not Found")
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:
            try:
                self._send_json_error(500, "Internal error: %s" % exc)
            except Exception:
                pass

    def _route_git(self, method, path, query, body):
        segments = path.split("/")
        # /{owner}/{repo}.git/...
        if len(segments) < 4 or not segments[2].endswith(".git"):
            return False
        owner = segments[1]
        repo_name = segments[2][:-len(".git")]
        tail = segments[3:]
        repo = get_repo(owner, repo_name)
        if tail == ["info", "refs"] and method == "GET":
            if not authorized(self.headers):
                self._send_json_error(401, "Bad credentials")
                return True
            service = query.get("service", [""])[0]
            if service not in ("git-upload-pack", "git-receive-pack"):
                self._send_json_error(400, "Invalid service")
                return True
            if repo is None:
                self._send_json_error(404, "Not Found")
                return True
            protocol_v2 = "version=2" in (self.headers.get("Git-Protocol") or "")
            payload = handle_info_refs(repo, service, protocol_v2)
            self._send(200, payload,
                       content_type="application/x-%s-advertisement" % service)
            return True
        if tail == ["git-upload-pack"] and method == "POST":
            if not authorized(self.headers):
                self._send_json_error(401, "Bad credentials")
                return True
            if repo is None:
                self._send_json_error(404, "Not Found")
                return True
            first = body[:64]
            if b"command=ls-refs" in first:
                payload = ls_refs_cached(repo, body)
                if payload is None:
                    self._send_json_error(400, "Bad request")
                    return True
                self._send(200, payload,
                           content_type="application/x-git-upload-pack-result")
                return True
            protocol_v2 = "version=2" in (self.headers.get("Git-Protocol") or "")
            payload = fetch_cached(repo, body, protocol_v2)
            if payload is None:
                self._send_json_error(400, "Bad request")
                return True
            self._send(200, payload,
                       content_type="application/x-git-upload-pack-result")
            return True
        if tail == ["git-receive-pack"] and method == "POST":
            if not authorized(self.headers):
                self._send_json_error(401, "Bad credentials")
                return True
            if repo is None:
                self._send_json_error(404, "Not Found")
                return True
            payload = handle_receive_pack(repo, body)
            self._send(200, payload,
                       content_type="application/x-git-receive-pack-result")
            return True
        return False

    def do_GET(self):
        self._route("GET")

    def do_POST(self):
        self._route("POST")

    def do_PUT(self):
        self._route("PUT")

    def do_PATCH(self):
        self._route("PATCH")

    def do_DELETE(self):
        self._route("DELETE")

    def do_HEAD(self):
        self._route("HEAD")


class ForgeServer(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 512
    allow_reuse_address = True


# --------------------------------------------------------------------------
# lifecycle: register with the env, poll /done, exit when told

def lifecycle(port):
    if not ENV_URL:
        return
    base = ENV_URL.rstrip("/")

    def post_register():
        data = json.dumps({"port": port}).encode()
        request = urllib.request.Request(
            base + "/register", data=data, method="POST",
            headers={"Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(request, timeout=10) as response:
                response.read()
            return True
        except Exception:
            return False

    for _attempt in range(50):
        if post_register():
            break
        time.sleep(0.2)

    delay = 0.25
    while True:
        try:
            with urllib.request.urlopen(base + "/done", timeout=30) as response:
                payload = json.loads(response.read().decode())
            if payload.get("done") is True:
                time.sleep(0.05)
                os._exit(0)
        except Exception:
            pass
        time.sleep(delay)
        delay = min(delay * 2, 2.0)


def main():
    server = ForgeServer(("0.0.0.0", 0), ForgeHandler)
    port = server.server_address[1]
    thread = threading.Thread(target=lifecycle, args=(port,), daemon=True)
    thread.start()
    sys.stderr.write("forge listening on %d\n" % port)
    sys.stderr.flush()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
