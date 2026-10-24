# Charon 0.1.210 ULLBC vs. LLBC, Aeneas Lowering, and Direct Rustc MIR: Three-Layer Attribution and Multi-Crate Operational Comparison

## Summary

Evaluating Charon `0.1.210` (`commit 1e08453924610c19d74c245a7308f17c1008e2db`, pinned to `rustc 1.98.0-nightly f8a08b688`) and Aeneas (`commit ca282ec2`) against direct `rustc_driver` MIR extraction requires separating three distinct layers that are frequently conflated:

1. **Layer A — Charon ULLBC / LLBC AST expressiveness (`charon-lib/src/ast/`):** Charon's unstructured (`ullbc_ast.rs`) and structured (`llbc_ast.rs`) AST definitions natively represent raw pointer types (`RefKind::Raw`), `&raw const` / `&raw mut` (`Rvalue::RawPtr`), pointer metadata (`Rvalue::PtrMetadata`), `CastKind::Transmute`, `StorageLive`, `StorageDead`, `PlaceMention`, `UnwindResume`, and `TerminatorKind::Drop(DropKind, Place, TraitRef, TargetId, Option<TargetId>)`. At the same time, the ULLBC/LLBC AST drops `rustc`'s `WithRetag` copy discriminator (`Rvalue::Use(Operand)` has no `WithRetag` field), lowers `StatementKind::Retag` and `StatementKind::FakeRead` to `Nop`, lowers `NullaryOp::UbChecks` to `Constant(false)`, and omits `LocalInfo::User` vs. `LocalInfo::Boring` classification.
2. **Layer B — Charon `0.1.210` CLI flag pipeline (`--ullbc --precise-drops --extract-opaque-bodies --mir elaborated` vs. default LLBC):**
   - Under **strongest ULLBC flags** (`charon rustc --ullbc --precise-drops --extract-opaque-bodies --mir elaborated --rustc-arg=-Zmir-preserve-ub --rustc-arg=-Zalways-encode-mir=yes`), Charon skips `ullbc_to_llbc` (`control_flow/ullbc_to_llbc.rs`) and preserves `Runtime(PostCleanup)` CFG blocks, compiler-synthesized drop flags (`_20.._23: bool` in `cleanup_subject.rs`), field-precise drops (`DropKind::Precise`), unwind cleanup paths (`unwind_continue` and `on_unwind` drop targets), `StorageLive`/`StorageDead`, and `PlaceMention`.
   - Under **default LLBC structuring** (`charon rustc --mir elaborated`), `ullbc_to_llbc` (`ullbc_to_llbc.rs:731–737`) filters out every basic block that reaches `UnwindResume` (`!is_unwrap_block`), reducing `unwind_drop_blocks` to `0` on both `partial_init_move_cleanup` (`3 -> 0`) and `partial_field_reinit_cleanup` (`1 -> 0`).
3. **Layer C — Aeneas (`ca282ec2`) symbolic-to-pure functional translation (`aeneas/src/interp/`, `SymbolicToPure.ml`):** Aeneas consumes structured LLBC, rejects loops without static exits (`InterpLoops.ml:411`: `"Loops that don't have exits are not supported yet"`), rejects raw-pointer dereferences outside its borrow-checker value model, and translates functions to pure value-returning state-error definitions without byte-level memory/provenance/alignment semantics.
4. **Matched 3-crate operational comparison (`Direct-MIR` vs. strongest-flags Charon `0.1.210` ULLBC):** On a 3-crate workspace (`stateful_generic_lib`, `client_contract_user`, `client_direct_mir_inspector`) exercising raw pointer writes (`*slot_ptr = next_val`), generic layout queries (`size_of::<T>()`, `align_of::<T>()`), non-inline cross-crate calls (`transactional_step`), and scope-exit/unwind `Guard` drop side effects, strongest-flags Charon `0.1.210` ULLBC (`client_direct_mir_inspector_strongest.ullbc`, `778,542` B) translates via `support/extract_and_link_charon_h3.py` into a single-artifact `.amir` v3 closure (`1,019` B) that satisfies the **exact same universal operational theorems** in Lean `4.34.1` (`∀ base : Nat`) as direct `rustc_driver` `Runtime(PostCleanup)` extraction—provided three adapter gaps are closed: (a) a `TraitDropAdapter` mapping `Destruct::drop_in_place` to `<Guard as Drop>::drop`, (b) complete local-type table validation across all translated bodies (`verifyCharonNativeInspectorClosureCompleteC2`), and (c) an independent `rustc` monomorphization completion check (`collect_and_partition_mono_items`).

## Applicability

These findings apply to:

- **Charon `0.1.210`** (`commit 1e08453924610c19d74c245a7308f17c1008e2db`, binary SHA-256 `88542ca0b2bf52429fd5b9f2bf29f0f1183ba2279854567ab13d82bc789a8d47`, `charon-driver` SHA-256 `8831ba28df3e3ef594c80adc90fcd9bb5993e23107e739145383159356722363`), specifically:
  - `charon-lib/src/ast/ullbc_ast.rs`, `llbc_ast.rs`, `expressions.rs`, `types.rs`
  - `charon/src/bin/charon-driver/translate/get_mir.rs`, `translate_bodies.rs`, `translate_crate_to_ullbc.rs`
  - `charon-lib/src/transform/control_flow/ullbc_to_llbc.rs`, `simplify_output/remove_drop_never.rs`, `resugar/reconstruct_boxes.rs`, and `monomorphize.rs`
- **Aeneas** (`https://github.com/AeneasVerif/aeneas`, commit `ca282ec2`), specifically `src/interp/InterpLoops.ml`, `src/interp/InterpStatements.ml`, and `src/symbolic/SymbolicToPure.ml`.
- **`rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-30`, LLVM `22.1.6`)** on `x86_64-unknown-linux-gnu`.
- **Lean `4.34.1`** (`commit 5045d0056413266e57c625dcd7c365b10e377c52`), used to mechanize the pipeline trust model, the 3-crate operational equivalence proofs, the native Charon `.ullbc` closures, and the negative controls in `support/*.lean`.

## Findings

### 1. Three-Layer Attribution: ULLBC AST vs. Charon Pass Pipeline vs. Aeneas Pure Lowering

**Basis:** `source`, `execution`

Inspecting Charon `0.1.210` and Aeneas `ca282ec2` source code alongside empirical `.ullbc` and `.llbc` outputs on `cleanup_subject.rs` (`support/r15-compiler-revalidation.json`) isolates which constructs are preserved or lost at each stage:

| Semantic / MIR feature | Direct `rustc_driver` (`Built` + `PostCleanup`, `-Z mir-preserve-ub`) | Layer A: Charon `0.1.210` ULLBC AST (`ullbc_ast.rs`) | Layer B1: Charon `0.1.210` Strongest ULLBC (`--ullbc --precise-drops --extract-opaque-bodies --mir elaborated -Zmir-preserve-ub -Zalways-encode-mir=yes`) | Layer B2: Charon `0.1.210` Default LLBC (`--mir elaborated`) | Layer C: Aeneas (`ca282ec2`) `SymbolicToPure` |
|---|---|---|---|---|---|
| Explicit CFG blocks & `SwitchInt` | Preserved | Preserved | Preserved | Reconstructed to structured `llbc_ast::Statement` | Lowered to functional `match` / `if` |
| Unwind cleanup paths (`is_cleanup` / `UnwindResume` / `on_unwind`) | Preserved (`3` unwind drop blocks in `partial_init_move_cleanup`, `1` in `partial_field_reinit_cleanup`) | Representable (`UnwindResume`, `Drop(..., Option<TargetId>)`) | **Preserved** (`3` and `1` unwind drop blocks + `unwind_continue`) | **Stripped** (`ullbc_to_llbc.rs:731` removes all `!is_unwrap_block` blocks; `0` unwind drop blocks) | Absent (no unwind edges in LLBC input) |
| Elaborated drop flags (`_20.._23: bool`) & field-precise drops | Preserved | Representable (`DropKind::Precise`) | **Preserved** (`_23: bool`, `drop (Precise, (_2.1: Guard))`) | Conditional (`DropKind::Conditional` unless `--precise-drops`) | Rejects nontrivial drop glue / raw state |
| `StorageLive` / `StorageDead` / `PlaceMention` | Preserved | Representable | **Preserved** (`StorageLive`, `StorageDead`, `PlaceMention(_3)`) | Preserved in LLBC only if `-Z mir-preserve-ub` passed | Erased in pure functional translation |
| Non-terminating / exitless loops (`loop {}`) | Preserved | Representable (`SwitchInt` / `Goto` cycle) | **Preserved** | Restructured to `Loop` | **Rejected** (`InterpLoops.ml:411`) |
| Raw pointer writes (`*ptr = v`), `&raw`, `Transmute` | Preserved | Representable (`RefKind::Raw`, `RawPtr`, `Transmute`) | **Preserved** | Preserved in AST | **Rejected** outside safe borrow model |
| `WithRetag::Yes` vs. `WithRetag::No` & `StatementKind::Retag` | Preserved (`use_retag_no: 1..2`) | **Omitted** (`Rvalue::Use(Operand)` has 1 arg; `Retag` -> `Nop` at `translate_bodies.rs:647`) | **Omitted** | **Omitted** | **Omitted** |
| `LocalInfo::User` vs. `LocalInfo::Boring` | Preserved at `Built` | **Omitted** (`Var` has only `index`, `name`, `ty`) | **Omitted** | **Omitted** | **Omitted** |
| `Drop` terminator target resolution | Direct `Instance::resolve_drop_glue(tcx, ty)` | Stores `TraitRef` to `core::marker::Destruct` | Requires `TraitDropAdapter` to link `Destruct` to `<T as Drop>::drop` | Requires `TraitDropAdapter` | N/A |
| Post-monomorphization associated-const CTFE (`E0080`) | Enforced via `collect_and_partition_mono_items` | N/A | Bypassed (`Compilation::Stop` in `after_analysis`) | Bypassed | N/A |

Re-validating `cleanup_subject.rs` across the three Charon `0.1.210` invocation modes (`support/r15-compiler-revalidation.json`) produces:

- `ullbc_elaborated_default` (`charon rustc --ullbc --mir elaborated`): `exit_code: 0`, `151,887` B, SHA-256 `46bb416bb062327ad554a724860508df3cd8d2494002118d01c9b75ffd575bfb` (preserves unwind blocks, but marks drops `Conditional` rather than `Precise` and omits `-Z mir-preserve-ub` `PlaceMention`).
- `ullbc_elaborated_strongest` (`charon rustc --ullbc --precise-drops --extract-opaque-bodies --mir elaborated --rustc-arg=-Zmir-preserve-ub --rustc-arg=-Zalways-encode-mir=yes`): `exit_code: 0`, `634,884` B, SHA-256 `d0743df5fa54d33e15c0eb35014be5c251aeb704d87cef04cdb716e7d2e0435d` (preserves `_23: bool`, `DropKind::Precise`, all `6` normal and `3` unwind drop blocks in `partial_init_move_cleanup`, all `3` normal and `1` unwind drop blocks in `partial_field_reinit_cleanup`, and `PlaceMention`).
- `llbc_elaborated_default` (`charon rustc --mir elaborated`): `exit_code: 0`, `146,811` B, SHA-256 `ebf12384ee03c73224cbcefeb851ed42a3bf4daa20227a907dab5ac90ee84e11` (`ullbc_to_llbc` strips all unwind cleanup blocks).

### 2. Matched 3-Crate Operational Comparison (`stateful_generic_lib`, `client_contract_user`, `client_direct_mir_inspector`)

**Basis:** `execution`, `derived`

To compare Direct-MIR and strongest-flags Charon `0.1.210` ULLBC on identical multi-crate verification obligations, both pipelines were executed on a 3-crate Cargo workspace:

1. **`stateful_generic_lib`:** Defines `EffectLog`, `Guard` (`impl Drop for Guard` recording `drop_tag` via `EffectLog::record`), generic `pub unsafe fn step_generic_slot<T>(log: &mut EffectLog, slot_ptr: *mut u32, delta: u32) -> usize` (querying `core::mem::size_of::<T>()` and `core::mem::align_of::<T>()`, writing `*slot_ptr = next_val`, and dropping a local `Guard` on scope exit), and non-inline `pub fn transactional_step(log: &mut EffectLog, val: u32, should_abort: bool) -> Result<u32, u32>` (creating a `Guard` with `drop_tag = 1`, returning `Err(100)` with drop effect `1` on early exit, or `mem::forget(guard)` + `EffectLog::record(2)` + `Ok(val + 10)` on commit).
2. **`client_contract_user`:** Calls `step_generic_slot::<u32>` and reasons modularly through `stateful_generic_lib`'s operational contract (`PublishedStatefulLibContractOperational`).
3. **`client_direct_mir_inspector`:** Calls both `step_generic_slot::<u32>` and non-inline `transactional_step` inside `inspect_and_commit_slot` and proves exact private event-sequence theorems (`obsEvents = [4, 2, 1]` on commit, `[4, 1]` on early abort) that require inspecting the dependency's implementation bodies.

With `--extract-opaque-bodies` and `--rustc-arg=-Zalways-encode-mir=yes`, running Charon `0.1.210` on each client crate extracts the upstream `stateful_generic_lib` `.rlib` bodies directly into the client's `.ullbc` file (`client_direct_mir_inspector_strongest.ullbc`, `778,542` B, SHA-256 `226b75307521c2b110ccb9a747a8c51f3a540cfa2c179aec08aeec975c0a3081`; `client_contract_user_strongest.ullbc`, `674,406` B, SHA-256 `d0e6c2741abceb38099775b07fc0c08c9c0a9cea3317e16b8c4049423e828271`).

The translator `support/extract_and_link_charon_h3.py` (SHA-256 `97c35e45121c5695f64e505088686753991c9bab1efc689ea561c8176e500aa7`) lowers each single-artifact client `.ullbc` into a self-contained binary `.amir` v3 package (`charon_h3_native_client_inspector_closure.amir`, `1,019` B, SHA-256 `fafd26afcc9a0f1d7e87a85846cda92edc97d690ee472932d6a49595a43b2c77`; `charon_h3_native_client_contract_closure.amir`, `418` B, SHA-256 `7a68aab4b07ece253d052f4a864849ad967e321073956aadecd4283cd2998fe2`). In `support/CharonNativeAndControlsR3R4.lean` and `support/StatefulGenericLibraryH3H7Core.lean` (`support/r15-lean-revalidation.json`), Lean `4.34.1` proves:

- **`r3_charon_native_single_artifact_closures_satisfy_contract_and_inspector_endpoints`:** Decoding `charonNativeClientContractClosureAmirBytes` (`418` B) and `charonNativeClientInspectorClosureAmirBytes` (`1,019` B) and executing them under `evalBodyWithFuel` satisfies the universal operational contract (`∀ base : Nat`) on `run_client_contract_workflow` (`symId = 66`) and both commit (`abortFlag = 0`) and abort (`abortFlag = 1`) endpoints on `inspect_and_commit_slot` (`symId = 67`), matching Direct-MIR byte-for-byte on all observable state transitions.

### 3. Adapter Obligations Required by Strongest-Flags Charon `0.1.210` ULLBC

**Basis:** `source`, `execution`, `derived`

Achieving operational equivalence between strongest-flags Charon `0.1.210` ULLBC and Direct-MIR exposed three concrete adapter requirements that are mechanized with positive and negative controls in `support/StatefulGenericLibraryH3H7Controls.lean` and `support/CharonNativeAndControlsR3R4.lean`:

1. **`TraitDropAdapter` for `core::marker::Destruct` (`charonCtrl3DroppedTraitDropAdapter`):**
   In `client_direct_mir_inspector_strongest.ullbc`, `step_generic_slot` (`fun_decls[4]`, `symId = 63`) and `transactional_step` (`fun_decls[5]`, `symId = 65`) emit `TerminatorKind::Drop(DropKind::Precise, place, trait_ref)` where `trait_ref` points to `trait_decls[0]` (`core::marker::Destruct`), while `<Guard as core::ops::Drop>::drop` is emitted separately as `fun_decls[8]` (`symId = 1`). Without `TraitDropAdapter` resolving `(Guard, Destruct)` to `symId = 1`, `Drop` terminators fail to invoke `<Guard as Drop>::drop` and lose all scope-exit and unwind cleanup effects (`r4_all_seven_charon_generated_amir_controls_connected_and_verified`).
2. **Complete local-type table validation across all translated ULLBC bodies (`verifyCharonNativeInspectorClosureCompleteC2`):**
   Because `.amir` v3 statements index locals by position (`localIdx : Nat`) while `WireBody.localTypes` records each local's `MirTypeTag`, mutating a local's type in `.ullbc`—such as changing local `_0` in `inspect_and_commit_slot` (`symId = 67`) from `u32` (`0x03`) to `u64`/`usize` (`0x04`) (`charonCtrl6LocalU64TypeMismatchAmirBytes`), or changing local `_2` in `<Guard as Drop>::drop` (`symId = 1`) from `u32` (`0x03`) to `u64`/`usize` (`0x04`) (`charonCtrl7UncheckedLocalMutantAmirBytes`, SHA-256 `5342601cf574a1aa4dbc93ed73857f63de8d54e9f6ef125506222e2b0922e66a`)—alters the decoded `WireBody.localTypes` table while leaving untyped instruction evaluation unchanged. A partial domain gate (`verifyCharonNativeInspectorClosureQ6`) that checks only selected locals in `symId ∈ {67, 63, 65, 24}` rejects `ctrl6` (`q6_charon_adapter_domain_accepts_native_closure_and_rejects_local_u64_type_mismatch`) but falsely accepts `ctrl7`, whereas the complete 10-body local-type gate `verifyCharonNativeInspectorClosureCompleteC2` accepts the genuine Charon closure and rejects both `ctrl6` and `ctrl7` (`c2_d4_complete_charon_local_domain_gate_rejects_both_ctrl6_and_ctrl7_unchecked_local_mutant`).
3. **Five-arrow pipeline trust chain and four-axis architectural comparison (`FrontendPipelineTrust.lean`, `CompilerIntegrationDossier.lean`):**
   - `complete_five_arrow_chain_transfers_claim` and the six controls in `FrontendPipelineControls.lean` (`wrong_callee_same_scalar_return_control`, `wrong_written_location_same_return_control`, `erased_unwind_edge_hides_exceptional_effect_control`, `typed_copy_padding_loss_control`, `untracked_trusted_import_dependency_control`) prove that scalar return agreement alone is insufficient to validate a frontend pipeline; call identity, memory write footprint, unwind cleanup trace, byte padding, and crate-pin identity must all be preserved.
   - `CompilerIntegrationDossier.lean` and `CompilerIntegrationDossierControls.lean` formalize the four frontend decision axes (Acquisition, Semantic Capture Boundary, Interchange Format, Proof Representation) and prove why `rustc_driver` direct capture (`Built` + `Runtime(PostCleanup)`) is the primary zero-adapter boundary while strongest-flags Charon `0.1.210` ULLBC is an admissible secondary route when paired with `TraitDropAdapter`, complete `localTypes` validation, and `rustc` completion checking.

## Boundaries

- **`known not to apply`:** Default Charon LLBC (`charon rustc` or `charon rustc --mir elaborated` without `--ullbc --precise-drops`) does **not** preserve unwind cleanup blocks (`ullbc_to_llbc.rs:731` strips all blocks leading to `UnwindResume`).
- **`known not to apply`:** Aeneas (`ca282ec2`) `SymbolicToPure` translation does **not** support exitless loops (`InterpLoops.ml:411`) or raw-pointer spatial memory/provenance verification.
- **`unsupported`:** Even under strongest ULLBC flags, Charon `0.1.210`'s AST does **not** preserve `WithRetag::Yes` vs. `WithRetag::No` on `Rvalue::Use`, `StatementKind::Retag`, `NullaryOp::UbChecks`, or `LocalInfo::User` metadata, and Charon fails on `async fn` coroutine state machines (`feature_ladder_async`).
- **`not examined`:** Aeneas's experimental borrows-to-pure extensions for nested mutable slices with non-static lifetimes were not examined.
- **`unknown`:** Whether upstream Charon will add an option to preserve `UnwindResume` cleanup paths during `ullbc_to_llbc` structuring is unknown.

## Evidence

- **`support/extract_and_link_charon_h3.py`** (SHA-256 `97c35e45121c5695f64e505088686753991c9bab1efc689ea561c8176e500aa7`): Translator from strongest-flags Charon `0.1.210` `.ullbc` artifacts (`stateful_generic_lib_strongest.ullbc`, `client_contract_user_strongest.ullbc`, `client_direct_mir_inspector_strongest.ullbc`) to binary `.amir` v3 packages, implementing `TraitDropAdapter` and emitting the positive closures and mutation controls.
- **`support/r15-compiler-revalidation.json`**: Fresh execution ledger captured on `2026-10-24` using `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` and `charon 0.1.210`, recording the 3-way `cleanup_subject.rs` `.ullbc`/`.llbc` comparison and verifying SHA-256 hashes and byte sizes of the 3-crate strongest-flags `.ullbc` and `.amir` v3 artifacts.
- **`support/FrontendPipelineTrust.lean`** (`41b70198...`) and **`support/FrontendPipelineControls.lean`** (`c814decc...`): Lean `4.34.1` mechanization of the five-arrow frontend pipeline trust model and five negative controls.
- **`support/StatefulGenericLibraryH3H7Core.lean`** (`ddcd212e...`), **`support/StatefulGenericLibraryH3H7.lean`** (`2f648e1a...`), **`support/StatefulGenericLibraryH3H7Controls.lean`** (`eb23e84b...`), and **`support/CharonNativeAndControlsR3R4.lean`** (`00eeb14c...`): Lean `4.34.1` mechanization of the 3-crate workspace operational contracts, native single-artifact Charon `.ullbc` closures (`r3_charon_native_single_artifact_closures_satisfy_contract_and_inspector_endpoints`), all seven binary `.amir` v3 Charon controls (`r4_all_seven_charon_generated_amir_controls_connected_and_verified`), and the complete 10-body local-type validator (`c2_d4_complete_charon_local_domain_gate_rejects_both_ctrl6_and_ctrl7_unchecked_local_mutant`).
- **`support/CompilerIntegrationDossier.lean`** (`f5c885d1...`) and **`support/CompilerIntegrationDossierControls.lean`** (`45767524...`): Lean `4.34.1` mechanization of the four-axis frontend decision model and nine negative controls.
- **`support/r15-lean-revalidation.json`**: Fresh Lean `4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`) execution ledger captured on `2026-10-24`, confirming `exit_code: 0` for all `8` target modules and their transitive dependencies.

## Revalidation

To reproduce the Charon `0.1.210` ULLBC vs. LLBC measurements, `.ullbc`-to-`.amir` translation, and Lean `4.34.1` proofs from this package's `support/` directory:

```bash
# 1. Compare Charon 0.1.210 default ULLBC, strongest-flags ULLBC, and default LLBC
charon rustc --ullbc --mir elaborated \
  --dest-file /tmp/cleanup_default.ullbc \
  -- --crate-type=lib --edition=2021 ../rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/support/cleanup_subject.rs

charon rustc --ullbc --precise-drops --extract-opaque-bodies --mir elaborated \
  --rustc-arg=-Zmir-preserve-ub --rustc-arg=-Zalways-encode-mir=yes \
  --dest-file /tmp/cleanup_strongest.ullbc \
  -- --crate-type=lib --edition=2021 ../rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/support/cleanup_subject.rs

charon rustc --mir elaborated \
  --dest-file /tmp/cleanup_default.llbc \
  -- --crate-type=lib --edition=2021 ../rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/support/cleanup_subject.rs

# 2. Re-check the Lean 4.34.1 formalization modules
for mod in FrontendPipelineTrust FrontendPipelineControls \
           StatefulGenericLibraryH3H7Core StatefulGenericLibraryH3H7 \
           StatefulGenericLibraryH3H7Controls CharonNativeAndControlsR3R4 \
           CompilerIntegrationDossier CompilerIntegrationDossierControls; do
  lean -j1 -M1024 "support/${mod}.lean"
done
```
