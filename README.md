# GitHub-compatible git forge (perf rebuild)

A latency-tuned GitHub-compatible git forge in a single Python file:
REST + GraphQL + MCP surfaces, smart-HTTP git transport, generation-keyed
caches for ref advertisements and fetch responses, zero-recompression pack
ingest, and single-write responses with TCP_NODELAY.

Run: `python3 main.py` (stdlib only).
