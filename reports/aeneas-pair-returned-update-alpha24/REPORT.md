# Certifying an actual Aeneas returned pair update from alpha24

## Summary

The actual Aeneas-generated `choose` and `update_second` bodies compile with the bundle's Lean 4.30rc2 backend and admit direct endpoint proofs with no axioms. An additional certificate relates the selected imported pair-field update to the emitted returned pair, preserving the first field, outside heap cells, temporary storage cleanup, and unit return initialization under explicit entry-root and exclusive-write premises.

This is one representative borrow/update certificate under a restricted logical memory model. The imported Rust frontend and the interpretation of exclusive permission remain assumed. The safe source contains no unsafe representation operations, so it does not perform the safe-wrapper-over-unsafe experiment requested by P135.

## Applicability

The source is the exact standalone two-function `certificate_probe` specimen preserved as `support/probe.rs`, SHA-256 `cb328552754e6c54ac06e827dea6c52f12c23fa2d987b55e0c2644472faaf7d0`. The selected update is function ID 1:

```rust
pub fn update_second(p: &mut (u8, u8), x: u8) { p.1 = x; }
```

The legacy alpha24 Aeneas binary is identified by SHA-256 `244397c4178329f2b8ab48240cd19dafd6511efb6c4e78be6345011ca8786f8e`; the examined emitted backend uses Lean 4.30.0-rc2 revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. The native control uses the same bundle's rustc 1.98.0-nightly revision `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`. No current patched Charon/Aeneas or Lean 4.31 emission result is inferred.

The parent initially observed a loader failure for missing `libgmp.10.dylib`, then recovered only the task-owned runtime by linking the exact bundled GMP static archive using `clang -dynamiclib -Wl,-all_load`. The original Aeneas binary and program/admission checks were unchanged; the downloaded archive was unchanged. The recovered producer exited 0 and emitted `Types.lean`/`Funs.lean`. Original binary, GMP static, and derived dylib hashes and the actual command/stdout are preserved. This is a recovered loader environment, not a different semantic transformation or an unsupported-program outcome.

## Findings

Basis: source + execution + derived.

`CapturedFuns.lean` preserves the emitted definitions byte for byte. Only its source-path comment and the import `Aeneas.Types` were adapted: the latter refers to the separately copied `CapturedTypes` module so this standalone specimen can compile in scratch. `capture-identities.json` records both original and adapted whole-file hashes, exact definition-body hashes/text, and original selected export identities. The copied types file contains no additional type definitions.

The two emitted endpoints are:

```lean
choose b x y = Result.ok (if b then x else y)
update_second p x = Result.ok (p.1, x)
```

`choose_emitted` and `update_emitted` prove these for every Boolean and every `Aeneas.Std.U8`/pair by constructor cases and reflexivity. Their actual `#print axioms` output is empty. The examined backend's `UScalar` contains a `BitVec ty.numBits`, `U8` abbreviates `UScalar .U8`, and `.U8.numBits` reduces to 8. The result type has `ok`, `fail`, and `div` constructors. These particular bodies produce `ok` directly; no result-divergence claim for other translated programs follows.

The exact final selected LLBC operation order is: initialize `_0` to unit; `StorageLive(3)`; copy byte argument 2 into temporary 3; assign by moving temporary 3 through dereferenced reference local 1 to tuple field 1 of arity 2; `StorageDead(3)`; initialize `_0` to unit; return. The selected raw serialized ULLBC has the same operations, with the final unit expressed as a constant rather than an empty aggregate. Both selected subtrees are retained. The original Aeneas-preset ULLBC *print* lacks the entry unit assignment, as documented by the companion fork report; that earlier phase is not silently treated as the selected raw subtree here.

`check_capture.py` admits the exact complete selected JSON specimens and adapted generated files by consumer-selected hashes, then checks the region/local inventory, projection path, unit forms, operand modes, and complete selected operation order. This is an exact specimen gate with a trusted Python parser, not a certified general JSON parser. A modified tuple field remains plausible JSON but fails the full selected-artifact fingerprint admission. No unmodeled operation in an accepted new input is silently dropped: inputs outside this exact selected specimen are unsupported until their relation is defined.

`UpdateCertificate.lean` uses a heap `Nat → Option (U8 × U8)` and an explicit state containing root, input byte, external write-permission flag, return initialization, temporary liveness/value, and prior events. `actualLLBCUpdate` models the selected sequence. `sourcePlaceUpdate` independently states assignment to the second field at a valid root; interpreting the original Rust place as this model is a named frontend assumption. `returned_update_correspondence` establishes:

- The imported operation sequence produces `expectedState` for every entry state with `heap root = some p` and `canWriteRoot = true`.
- The generated pure function returns `ok (p.1, input)`.
- The final root contains `(p.1, input)`; every cell `j ≠ root` equals its entry contents.
- The temporary is dead and empty, `_0` is initialized, and the selected storage/move/update/unit/return events are retained in order.

The entry state may contain arbitrary prior return/temporary flags, temporary contents, prior event history, and arbitrary outside heap cells. No byte-input predicate narrows this domain. The correspondence and state/frame proofs depend only on `[propext, Quot.sound]`; the source-place heap equality depends on `[propext]`. False write permission or an absent root yields `none` in the modeled checker. The permission flag is an assumed entry authority supplied by a caller/resource model; it neither constructs a Rust reference nor proves absence of aliases or lifetime extension.

Native controls actually compile the same copied safe source with the bundled rustc, using `black_box` inputs and explicit assertions. They pass all `2 × 256 × 256 = 131,072` choose inputs and all `256³ = 16,777,216` pair/update inputs. The update retains the first field and a separate fixed frame cell; aggregate output is `choose_cases=131072 update_cases=16777216 digest=551903232000`. These executions corroborate value behavior on that native build; they do not prove source-to-LLBC import or a general Rust frame rule.

Changed-branch and changed-field examples have kernel-checked concrete distinguishing byte witnesses. Separate `WrongChoose`/`WrongUpdate` fixtures fail their attempted universal correspondence elaboration, exiting 1; those failures are recorded as failed proofs, not accepted proofs with hidden assumptions. Fresh-scratch revalidation recompiles the emitted files, endpoint/frame certificates, witnesses, and native control without modifying the runtime.

## Boundaries

- **Not examined:** unsafe representation operations and safe-wrapper callers (P135); reference construction, splitting, casting/reconstruction, lifetime-extension and aliasing counterexamples in Rust (full R096); nested borrows/backward functions, borrow-checker semantics, full Aeneas symbolic execution or join correctness.
- **Known not to establish:** Rust/frontend adequacy, actual exclusive permission, address/provenance/alignment/layout semantics, or a verified compiler for the native control. The heap model is a logical collection of valid pair cells, not a concrete byte memory.
- **Unsupported in the specimen gate:** new calls, loops, pointers, additional projections or generic instances, and any changed selected artifact without a new checked relation. Failure causes/partial traces are collapsed to `none`.

P129 has a completed bounded research answer: one actual representative returned-update transformation is certified with precise named premises. Full Rust import/permission adequacy and integration are future engineering obligations, while the unexamined unsafe-wrapper, alias/lifetime, and nested-borrow questions remain research gaps. Exact per-ID scopes are in `support/coverage.json`.

## Evidence

The package preserves generated files, original/adapted identities, exact selected raw/final JSON subtrees, source and native harness, producer recovery/run records, backend primary source-unit hashes and declaration paths, proof/control stdout and statuses, native output, and fresh-scratch results. Relevant bundled primary definitions are `Aeneas/Std/Scalar/Core.lean` (`UScalarTy.numBits`, `UScalar`, `U8`, approximately lines 30–75 and 652) and `Aeneas/Std/Primitives.lean` (`Result`, lines 62–66); their exact file hashes and backend manifest hash are in `capture-identities.json`. These local release artifact identities are stronger than the producer's `aeneas unknown` version string.

## Revalidation

Run `python3 -B support/revalidate.py --legacy-runtime /path/to/alpha24/runtime --out /new/task/scratch`. It uses the existing precompiled backend/package paths through `LEAN_PATH`, compiles only copied report files in scratch, checks expected failing proof controls, and compiles/runs the exhaustive native harness. It neither rebuilds nor repairs the runtime. A new generated body, artifact/configuration, or borrow grammar requires redoing the capture binding and stated relation; successful old proofs do not certify the new import.

*Authored by an AI agent acting on joshlf's behalf.*
