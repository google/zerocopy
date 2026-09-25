# Boundaries

- No fresh `lean --server`, `lake serve`, editor, LSP, or MCP process was run.
- No protocol transcript was generated on this surface. Lean's checked-in server test runner is source evidence for the client handshake, not execution performed by this report.
- This package establishes the source-level protocol and state lifecycle at Lean `v4.30.0-rc2`; it does not establish latency, throughput, memory growth, long-run stability, or concurrent-agent scaling.
- It does not establish that a goal response obtained without an explicit synchronization barrier always corresponds to the document version an external client intended. Clients that require a deterministic edit/query boundary should use versioned synchronization and handle content-modified responses.
- It does not characterize every cursor-boundary edge case in `InfoTree.goalsAt?`. Lean's own selection algorithm is the authority for whitespace, syntax boundaries, nested tactics, and before/after-tactic choice.
- It does not establish server-state equivalence with batch `lean` checking.
- It does not establish multiple-workspace behavior inside one server process.
- It does not establish Lake package/configuration, relocation, read-only, offline, or cache behavior. The server source documents its dependency-refresh relationship with `lake setup-file`, but the Lake side needs separate study.
- It does not establish how Anneal should map a Rust annotation position to a generated Lean position. The query primitive starts from a Lean URI and Lean position.
- It does not establish that generated Anneal/Aeneas files can be changed underneath an existing worker without a restart; dependency staleness is an explicit lifecycle concern.
- It does not prescribe whether Anneal should expose the full interactive RPC result or a smaller stable MCP schema.
- It does not assume that Lean's internal implementation structures are stable APIs across releases.
