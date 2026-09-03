# Exact-source supported-domain audit

Perform a source-only unsafe-code audit of the complete supplied snapshot.
Recover the exact supported domain from the policy and configuration files,
then determine whether the public safe API is sound and satisfies its
documented behavior throughout that domain.

`TCB.md` is an accepted human trust decision for this review. Apply it only to
the exact propositions and region it names, and keep it conspicuous in every
result that consumes it.

Use version-matched Rust Reference and standard-library documentation for
material Rust propositions. Do not modify, build, run, or test the target.
