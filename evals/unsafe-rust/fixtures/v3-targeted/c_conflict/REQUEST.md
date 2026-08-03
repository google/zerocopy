# Conflicting-policy source review

`POLICY-SCARLET.md` and `POLICY-INDIGO.md` are both current published support
commitments for this exact source snapshot. No precedence, supersession, or
conflict-resolution rule has been authorized.

Perform a source-only unsafe-code audit and state the strongest conclusion that
can be justified without selecting a new support policy. Account for the
effective configuration rejection in the source. `TCB.md` is an accepted human
trust decision; apply it only to its exact build-tool mappings and keep it
conspicuous. Use version-matched Rust Reference and standard-library
documentation for material Rust propositions. Do not modify, build, run, or
test the target.
