# Lean trust, admissions, and dependency auditing at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), logical admissions and executable-code trust are separate mechanisms. Ordinary assumptions are represented as axioms. `sorry` expands to `sorryAx`, and `#print axioms` computes transitive axiom dependencies. Declarations marked `unsafe` are fenced from ordinary safe declarations by the kernel, while compiler mechanisms such as `@[implemented_by]` and native-evaluation proof machinery create a distinct executable-code trust boundary.

`debug.skipKernelTC` is a direct exception to the normal kernel-check path. It defaults to `false`; its source documentation warns that enabling it compromises the ordinary proof-checking guarantee.

No fresh Lean execution was performed. The package is based on exact pinned source. Detailed findings, evidence, boundaries, and revalidation are split into support files so the reusable report remains easy to navigate.

## Applicability

- Lean: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tag `v4.30.0-rc2`.
- Anneal: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`; `anneal/flake.nix` selects `v4.30.0-rc2`.
- Aeneas: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`; `backends/lean/lean-toolchain` selects the same Lean release.

This package characterizes trust mechanisms at this exact revision. It does not assume adjacent-version continuity and does not claim that the Lean kernel, compiler, runtime, operating system, or hardware is formally verified.

## Findings

See [`FINDINGS.md`](FINDINGS.md). The high-value conclusions are: axioms are explicit assumptions without proof bodies; local hypotheses are not global axioms; `sorry` is `sorryAx`; `#print axioms` is the built-in transitive admission audit; safe declarations cannot directly depend on unsafe declarations; `@[implemented_by]` can change compiled behavior without a proof of equivalence; native-evaluation proof infrastructure adds an axiom after compiled execution; and `debug.skipKernelTC` bypasses kernel checking.

## Boundaries

See [`BOUNDARIES.md`](BOUNDARIES.md). In particular, this package contains no fresh Lean execution. A clean axiom dependency set does not establish Rust-to-Lean semantic adequacy or compiled-code correctness, and this package does not choose which assumptions Anneal should accept.

## Evidence

See [`EVIDENCE.md`](EVIDENCE.md) for exact source files and blob identities. Evidence roles are **source** and **derived**; there is no fresh **execution** evidence.

## Revalidation

See [`REVALIDATION.md`](REVALIDATION.md) for a source-first checklist and a minimal future execution probe that distinguishes ordinary proofs, explicit axioms, `sorry`, unsafe declarations, compiled implementation substitution, native evaluation, and the kernel-check bypass.
