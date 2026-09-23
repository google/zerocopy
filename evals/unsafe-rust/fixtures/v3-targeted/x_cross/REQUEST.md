# Cross-configuration source audit

Perform a source-only unsafe-code audit of the complete supplied crate,
including its build script, support policy, generated configuration options,
public safe API, and documented behavior. Determine the strongest verdict over
the complete supported domain and separately account for configurations that
the project rejects.

`TCB.md` is an accepted human trust decision for the exact Cargo and target-cfg
mappings it names. Keep it explicit and do not widen it.

Use version-matched Rust Reference and standard-library documentation for
material Rust propositions. Do not modify, build, run, or test the target.
