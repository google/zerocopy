# SMT frame diagnostics, elaboration and checking costs

## Summary

An actual cvc5 Alethe proof of an outside-cell frame obligation passed current Carcara. Elaborating and independently rechecking the resulting proof also passed, with explicit resolution pivots. The producer's equivalent `distinct` formulation instead contained an untranslated-rewrite hole; Carcara returned `holey` with exit zero. A consumer that accepts process zero alone would misclassify that evidence.

A changed source premise and a wrong semantic rule were rejected. Removing the outside-cell premise made the formula satisfiable, with a concrete safe Rust replay of its witness. These observations separate a source counterexample, incomplete proof support, source/proof mismatch and an operational reader failure.

## Applicability

The formula uses SMT-LIB QF_AUFBV: an array of 8-bit indices/values, one store, a second read and a premise that the two indices differ. Its negated obligation says the outside read changed. This is a manually encoded array operation; it does not model Rust allocation, initialization, provenance, lifetimes or aliasing by itself.

cvc5 1.4.2 is exact revision `282d5e0c84baf49c780704c532f87ba66d8b513d`, official macOS arm64 static archive SHA-256 `24397f7d022e755876ca836193d4c5f9c1d4326f0f6c01f7d7fc1ddd6bc5096c`. Carcara is exact source `20bf49c5ce31089ac83118574c888669355aaae1`, built with Rust 1.99.0 in release mode from the locked dependencies and task-local Cargo cache. No global installation occurred. The checked configurations use no allowed-rule override, ignored-rule option, custom checker or external rule solver.

## Findings

### F1. Exact solver input and result category are part of proof meaning

Basis: source + execution + derived.

The [SMT-LIB ArraysEx 2.7 definition](https://smt-lib.org/theories-ArraysEx.shtml), release 2024-07-21, supplies read-over-write equality at a different index. This is a normative array-law premise, with an explicit manual Rust interpretation. For the direct premise `(not (= changed framed))`, cvc5 emits `unsat` and a 281-byte Alethe payload. It assumes the outside-cell premise and negated frame equation, uses `arrays_row`, and resolves to the empty clause. Carcara checks that proof against the actual SMT input and reports `valid`, exit zero.

Replacing the direct premise with `distinct` produces an equivalent logical problem but an additional rewriting step with rule `hole` and argument `untranslated rewrite`. Carcara reports `holey`, also exit zero. The exact CLI `main.rs` prints either successful Status value and returns normally; `Status::Display` distinguishes `valid`/`holey`, and `checker/mod.rs` marks `hole` and `lia_generic` as holey. This is a real partial-result interface, not an inferred bug in the solver's unsatisfiability claim.

A closed-certificate consumer must require the exact accepted verdict and permitted rule/configuration closure. Allowing rules or delegating to external commands changes that policy; a `valid` label under a different configuration is not this observation. These runs exercise only array/equality/resolution checking, not all SMT theories.

### F2. Elaborator output can be checked without treating elaboration as authority

Basis: source + execution.

Carcara's elaboration command checks the input while elaborating it, prints its verdict, then prints the output proof. The elaborated proof is 265 bytes and adds explicit resolution arguments. Rechecking with `--check-granularity elaborated` against the original problem succeeds; this avoids relying on the elaborator's reported result alone. Both processes nevertheless use the same checker/parser implementation, so this is not diversity against correlated implementation defects.

The first consumer attempt incorrectly passed the entire verdict-prefixed stdout as proof data. The checker rejected token `valid`, exit one. No certificate was accepted or published. Inspection identified the exact CLI output contract; the corrected narrow reader requires exit zero, the complete `valid` prefix and nonempty proof payload before invoking strict rechecking. It rejects holey, unknown, nonzero and empty-output fixtures. Raw initial output and failure are retained. No checking rule was weakened to recover.

### F3. A false frame claim, incomplete proof and mismatch need different diagnostics

Basis: execution + source + derived.

Checking the old proof against the problem without the outside-cell premise rejects its unmatched assumption, exit one. Changing its `arrays_row` rule to `refl` is a separate semantic checker failure. Neither result proves that the requested original Rust program is unsafe: one is claim mismatch and the other is invalid evidence.

The premise-free formula is actually satisfiable. cvc5's model selects changed=framed=255, an initial value 254 and replacement 255. `diagnostic_witness.rs` independently constructs that 256-byte array, performs a safe store, and observes 254 before/255 after. This validates the particular modeled counterexample at a concrete safe Rust operation. It does not validate arbitrary solver models, source extraction or unsafe traces.

`binding.json` maps the assertion roles to the store/read obligation. A useful future diagnostic should preserve source/model/SMT/certificate identities, the requested operation and source location, whether a concrete model was found, whether replay succeeded, and the exact unsupported/partial/checker/operational outcome. A resource obligation can fail because an outside-footprint premise was omitted; blindly strengthening the contract to exclude a real valid caller can still make the source claim inadequate. Diagnostic explanation and accepted input coverage must therefore be reviewed together.

### F4. Generation, elaboration and checking costs are separate measured phases

Basis: execution + derived.

Three complete samples measured cvc5 generation, Carcara checking, elaboration and strict rechecking of the same small formula. Median process-inclusive times were approximately 5.65, 2.95, 3.00 and 2.87 ms respectively. The raw cvc5 output includes a six-byte `unsat` line; the logical payload is 281 bytes. Carcara's raw output similarly contains a six-byte `valid` line before the 265-byte elaborated proof. The exact streams, statuses and timings are retained.

These are one tiny obligation on one host with uncontrolled caches and concurrent load. They establish that the four phases were actually exercised; they do not rank general SMT, Lean or separation-logic checking, nor estimate realistic whole-crate cost. Parsing, input transport, native checker compilation/runtime, original source encoding, SMT semantics and the unverified Carcara implementation remain trusted at this endpoint. There is no Lean/Rocq reconstruction of this actual proof in the experiment. SMTCoq, LFSC and Lean-SMT routes and their different trust boundaries are covered in the [comparison report](../smt-certificates-reconstruction-and-root-binding-2026-10-14/REPORT.md).

## Boundaries

Not examined: formal verification of the built Carcara binary, end-to-end Rust-to-SMT adequacy, proof transport of this specimen into Lean/Rocq, larger proof families, nonlinear/floating-point/quantifier certificates, adversarial resource exhaustion or comprehensive counterexample replay. The finite array encoding is an explicit source-import premise. A holey proof is incomplete independent checking, not a proof of unsafe Rust or a counterexample to solver soundness.

The selected cvc5 archive is a static non-GPL variant but reports LGPL-linked components; its exact license closure is a separate source/distribution question. The source build was permitted only as an experiment, not treated as a trusted or verified compiler artifact. No native binary or upstream source mirror is included in the report.

## Evidence

Source: [Carcara exact CLI](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/bin/cli/main.rs), `main`, `check_command`, `elaborate_command`; `src/lib.rs:Status/Display` lines 77–89; `src/checker/mod.rs`, configuration, rule dispatch and holey classification, lines 380–407. The official [cvc5 release](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.4.2) supplies the examined archive/commit identity.

Execution: `support/` preserves all three original SMT inputs, raw and extracted proofs, complete initial outcomes (one diagnostic path normalized with raw hash retained), failed verdict-prefix attempt, corrected reader/regression, measured elaborations/rechecks, semantic mutant and concrete Rust witness. `downloads.json`, `build-observation.json` and `carcara-Cargo.lock` identify acquisition/build scope. `artifact-identities.json` binds retained inputs/outputs. Evidence acquired 2026-10-14.

## Revalidation

Select the exact supplied cvc5 and built Carcara subjects, then run `support/measure.py <carcara> <cvc5> <new-output>`. Inspect the raw/extracted proof boundary and require all valid verdicts and the wrong-rule rejection. Separately rerun the distinct-input holey case, source-mismatch rejection, premise-free model and safe witness. Changes in verdict syntax, proof granularity, rules, options or source encoding require a new interface review; never normalize an unknown verdict into acceptance.

*Authored by an AI agent acting on joshlf's behalf.*
