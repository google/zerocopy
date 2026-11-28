<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Red-Team & TCB Containment Escapes (`RT-*`)

`RT-<KIND>-<12hex>` tracks adversarial exploits that attempt to obtain a false
passing verification receipt, compromise elaborator containment, or bypass
auditor checks (`PROOF_HACK`, `CODE_AND_PROOF_HACK`, `SPEC_PREFLIGHT_HACK`,
`THEORY_AUDIT_HACK`, and related vectors). See
[two-phase bug management][two-phase] for issue-lifecycle rules.

## Matching the Phase-0 layer to the attack surface

Static capture rules in [`tripwires.rs`][tripwires-rs] inspect Rust crate
flags and raw `&mir::Body<'_>` shapes, so they work well when a vulnerability
is entered through Rust code generation or MIR lowering (`CODE_AND_PROOF_HACK`
targeting `Trusted.MirSemantics` or `rustc-capture`).

However, **`rustc-capture` is NOT the right Phase-0 layer for pure proof,
spec-preflight, elaborator, or TCB-boundary escapes**, because those payloads
are introduced *after* or *outside* MIR extraction inside authored Lean files,
OS sandboxing, or kernel auditing:

- **Specification preflight escapes (`SPEC_PREFLIGHT_HACK`):** Place temporary
  fail-closed rejection in [`SpecPreflight.lean`][spec-preflight] or its
  driver so untrusted syntax macros or `EnvExtension` smuggling fail preflight
  before elaboration.
- **Proof/kernel escapes (`PROOF_HACK`, `THEORY_AUDIT_HACK`):** Place
  fail-closed rejection in [`TrustedBoundary.lean`][trusted-boundary],
  [`verify.rs`][verify-rs], or the `theory/` auditor rather than refusing valid
  Rust inputs in `rustc-capture`.
- **Elaborator containment escapes (`ExecSeal`):** Harden [`sandbox.rs`][sbox]
  fail-closed before launching child `lean` processes ([elaborator containment
  architecture][elab-doc]).

## Pre-triage confirmation (`needs_human_review`) for non-oracle `RT-*`

Because adversarial `CODE_AND_PROOF_HACK` targets control both Rust code and
proofs, executable oracles (`rustc`/Miri) can miss unsound semantics rules:

1. **Executable oracle (`P0`, immediate `open`/`triaged`):** When Miri or
   `rustc` confirms UB / contract failure on a passing Anneal proof (or on
   fixed-target / sandbox escapes), triage and Phase 0 proceed immediately.
2. **Machine-checked Lean semantics patch + preservation gate (`P1`,
   promotable to `P0` -> `needs_human_review`):** When executable oracles are
   silent, a candidate counter-semantics patch scoped to `Trusted/MirSemantics/`
   paired with a kernel-checked incorrectness proof *and* positive preservation
   canary checks enters `needs_human_review`. Once humans confirm the proposed
   patch models real Rust UB rather than weakening good programs, that patch
   directly seeds Phase 1 (bypassing or accelerating Phase 0 if ready to land).
3. **Prose incorrectness claim + optional inputs (`P2` / `P1` ->
   `needs_human_review`):** Pure prose explanations enter `needs_human_review`
   until human maintainers validate an actual soundness defect before initiating
   Phase 0 or Phase 1 work.

## Policy and audit requirements for TCB-layer Phase-0 checks

Any temporary guard inside `trusted/audit/`, `trusted/cargo-anneal/`, or
`trusted/lean/` outside `tripwires.rs`:

1. **Must carry an inline `// PHASE0_TRIPWIRE(...)` or `-- PHASE0_TRIPWIRE(...)`
   marker** with the canonical `RT-*` `bug_id`, `issue`
   (`https://github.com/google/zerocopy/issues/<N>`, or `"embargoed"` for
   private security disclosure per [two-phase bug management][two-phase] and
   `AGENTS.md` without exploit payloads), `owner`, `added_date`, `scope`,
   `rationale`, and `regression_test`.
   [`check_phase0_tripwires.py`][tripwire-ci] (`--mode tree` and
   `--mode phase1-cleanup`) scans `anneal/trusted/**/*.{rs,lean}` recursively so
   commented markers never linger undetected.
2. **Must NOT bypass Pass 1 / Pass 2 audit:** Edits outside `tripwires.rs`
   fail `isolated_tripwire_surface`, require full `AGENTS.md` trust review,
   and should add matching negative fixtures under `AUDIT_HEADER_GUARDS` in
   [`check_guard_mutation.py`][guard-mut] during Phase 1 cleanup.

[two-phase]: ../two-phase-bug-management.md
[tripwires-rs]: ../../trusted/rustc-capture/src/tripwires.rs
[spec-preflight]: ../../trusted/audit/SpecPreflight.lean
[trusted-boundary]: ../../trusted/audit/TrustedBoundary.lean
[verify-rs]: ../../trusted/cargo-anneal/src/verify.rs
[sbox]: ../../trusted/cargo-anneal/src/sandbox.rs
[elab-doc]: ../elaborator-containment-design.md
[tripwire-ci]: ../../ci/check_phase0_tripwires.py
[guard-mut]: ../../ci/check_guard_mutation.py
