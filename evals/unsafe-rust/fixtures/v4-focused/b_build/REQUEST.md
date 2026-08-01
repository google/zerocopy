# Ordered build-to-source unsafe-code audit

Perform a source-only unsafe-code audit of the complete supplied crate,
including its build script, build and support policies, generated configuration
options, selected library source, public safe API, and documented panic
postcondition.

Recover the complete supported theorem domain. Then give the complete
claim-relevant build relation in execution order, not merely its endpoint
mapping. Account for every raw `FIXTURE_ALLOCATOR` class, every successful
path, every explicit rejection, every stdout-write failure point, and every
material partial emitted prefix and exit. Follow each emitted directive through
its exact Cargo interpretation to the configuration options and library source
that are selected, or prove why no current library compilation is produced.

Audit the rerun/freshness sequence explicitly, including reuse of one Cargo
target directory while changing `FIXTURE_ALLOCATOR` from `arena` to
`arena-stop`. Separately prove or reject the project's target/allocator
exclusion.

Report the strongest soundness and documented-postcondition verdicts. The
report must also state and prove the **exact maximal sound region over the full
supported configuration product and every `u8` API input**, rather than giving
only one counterexample or a non-maximal positive remainder. Symbolic formulas
and parametric proofs are welcome; Cartesian enumeration is not required.

`TCB.md` is an accepted human trust decision for only the exact Cargo,
freshness, process-status, feature, and target-cfg propositions it names. Keep
every consumed part explicit and do not widen it. Verify every material Rust
proposition against narrowly scoped, version-matched Rust Reference or
standard-library documentation: cite its exact URL and quote the relied-upon
text. Cargo documentation may be used to review the accepted Cargo premise but
is not a Rust semantic axiom.

Do not modify, build, run, or test the target.
