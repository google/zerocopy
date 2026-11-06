import AnnealResearch.SubstantiveMirByteParser
import AnnealResearch.SemanticVerticalSliceCore
import AnnealResearch.CargoWorkspaceIntegration

set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

namespace AnnealResearch.StatefulGenericLibraryH3H7

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration

/-!
# Wave B (`H3`, `H4`/`H6`, `H5`, `H7`) + `#68` Corrective Tracks `N1`, `N2`, `N3`, `N6`

Addresses `joshlf/anneal#64` Section 9 (`H3`–`H7`), `joshlf/anneal#1` (`LIB-01`–`13`), and
`joshlf/anneal#68` Sections 4.1–4.4 and 6 (`N1`, `N2`, `N3`, `N6`):

1. **`N1` (`#68` §4.1 & §6 N1) — Universal Operational Library & Modular Client Proofs + Bound Compiler Layout Table**:
   - Explicitly accounts for compiler-computed layout facts via `BoundCompilerLayoutTable`
     (`statefulGenericLibLayoutTable`, bound to `statefulGenericLibExpectedCtx` by crate name, SVH,
     and source SHA-256 tag), deriving `size_of::<u32>() = 4` (`symId = 37`) and
     `align_of::<u32>() = 4` (`symId = 38`) via `deriveLayoutCalleeBodies`.
   - States `PublishedStatefulLibContractOperational` **directly over `evalStepGenericSlotWithFuel`
     (`SemanticVerticalSliceCore.runSteps`)** for **all `base : Nat`** and both `ptrValid = false` (`.ub`)
     and `ptrValid = true` (`.returned (.scalar ((base + 4) % usizeMod))` with `stepCount = 1` and
     existentially abstracted `traceAcc`/`obsEvents`).
   - Proves `stateful_generic_lib_satisfies_operational_contract` universally for all `base : Nat` by
     reducing `runSteps` directly on the decoded AST, and proves
     `step_generic_slot_symbolic_summary_matches_runSteps_universal` for all `ptrValid : Bool` and
     `base : Nat`.
   - Defines the operational call-contract evaluator `runClientWithCalleeOracle` (which steps
     `client_contract_entry`'s decoded statements and terminators directly and queries a callee
     contract oracle at `Call(63, ...)` without unfolding `libBodies`), proves
     `client_contract_user_verified_modularly_from_operational_contract` for all `base : Nat` from
     `PublishedStatefulLibContractOperational` alone, and proves the universal operational bridge
     `client_contract_oracle_matches_linked_runSteps_universal` connecting `runClientWithCalleeOracle`
     to linked `runSteps (clientContractUserBodies ++ statefulGenericLibBodies)` for all
     `ptrValid : Bool` and `base : Nat`.
2. **`N2` (`#68` §4.4 & §6 N2) — Matched 3-Crate Strongest-Flags Charon `0.1.210` Operational Endpoint**:
   - Embeds the `.amir` v3 packages translated by `extract_and_link_charon_h3.py` from
     `stateful_generic_lib_strongest.ullbc`, `client_contract_user_strongest.ullbc`, and
     `client_direct_mir_inspector_strongest.ullbc` captured with
     `charon cargo --ullbc --precise-drops --mir elaborated --extract-opaque-bodies --rustc-arg=-Zmir-preserve-ub --rustc-arg=-Zalways-encode-mir=yes`.
   - Proves `charon_h3_stateful_generic_lib_satisfies_operational_contract` universally for all `base : Nat`,
     `charon_h3_client_contract_user_verified_modularly_and_linked` for all `base : Nat`, and
     `charon_h3_inspector_matches_direct_mir_operational_outcomes` (`[4, 2, 1]`, `[4, 10, 1, 2]`, and `.failed .ub`).
3. **`N3` (`#68` §4.2 & §6 N3) — Actual `MirPhase::Built` Graph Ingestion & Independent Conditional-Drop Validator**:
   - Embeds `realStatefulGenericLibBuiltAmirBytes` (`stateful_generic_lib_built_phase.amir`,
     `defaultPhase = .built`, containing the actual 15-block, 18-local `MirPhase::Built` graph of
     `transactional_step` `symId = 65` with no drop flags `_19`/`_20` and the 5-block, 10-local
     `MirPhase::Built` graph of `step_generic_slot` `symId = 63`).
   - Defines an independent `MirPhase::Built` conditional-drop operational interpreter
     (`runStepsBuiltConditionalDrop`, where moving a local deinitializes it and `WireTerm.drop`
     executes iff the local is still initialized in `fr.locals`).
   - Proves that running the late unconditional-drop interpreter (`runSteps`) on the `Built` graph
     double-drops `g2` (`[2, 2, 1]`) and `g1` (`[10, 1, 2, 1]`), whereas `runStepsBuiltConditionalDrop`
     on the `Built` graph agrees with `runSteps` on the `Runtime(PostCleanup)` graph across normal,
     unwind, and invalid-pointer executions (`validateBuiltToPostCleanupTwoSided`).
4. **`N6` (`#68` §4.3 & §6 N6) — Statement-Inspecting `reconstructVerifiedStructuredView`**:
   - Withdraws any general soundness claim for the naive `reconstructStructuredView` (whose
     counterexample on `altStatefulLibBodies` is proved in `StatefulGenericLibraryH3H7Controls.lean`)
     and defines `reconstructVerifiedStructuredView`, which inspects the decoded basic blocks,
     statements, operands, and call targets to extract the actual event tag `evTag` and arithmetic
     constant `addK`.
-/

/-! ## 1. Captured Direct-MIR `.amir` v3 Byte Streams (`Runtime(PostCleanup)` and `MirPhase::Built`) -/

/-- `stateful_generic_lib_always_encode.amir` (`791` bytes, `fp16 = [153, 48]`, `defaultPhase = .runtimePostCleanup`),
    containing `EffectLog::record` (`1`), `<Guard as Drop>::drop` (`2`), `may_unwind_op` (`3`),
    `step_generic_slot` (`63`), `step_u32_slot` (`64`), `transactional_step` (`65`),
    `DropGlue<Guard>` (`7`), and `core::mem::drop::<Guard>` (`24`). -/
def realStatefulGenericLibAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 153, 48, 8, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 3, 1, 3, 10, 2, 5, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 252, 131, 2, 0, 0, 74, 27, 7, 0, 255, 252, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 252, 73, 0, 129, 100, 0, 1, 33, 9, 64, 4, 63, 1, 3, 10, 3, 4, 4, 6, 5, 4, 1, 4, 1, 6, 4, 4, 0, 5, 32, 4, 17, 4, 0, 131, 0, 33, 4, 48, 2, 4, 32, 5, 73, 38, 5, 0, 1, 252, 0, 3, 32, 6, 32, 7, 19, 7, 0, 1, 1, 4, 75, 1, 6, 0, 2, 252, 71, 0, 129, 4, 0, 6, 33, 7, 33, 6, 32, 8, 17, 8, 0, 3, 0, 32, 9, 17, 9, 0, 5, 0, 75, 40, 0, 0, 3, 252, 72, 0, 73, 0, 0, 3, 33, 9, 33, 8, 33, 5, 64, 5, 64, 1, 3, 7, 3, 2, 4, 6, 5, 4, 6, 5, 4, 0, 6, 32, 4, 19, 4, 0, 1, 1, 4, 32, 5, 17, 5, 0, 2, 0, 32, 6, 17, 6, 0, 3, 0, 76, 63, 0, 0, 1, 252, 68, 0, 69, 0, 70, 0, 0, 3, 33, 6, 33, 5, 33, 4, 64, 6, 65, 1, 3, 21, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 17, 17, 19, 0, 128, 0, 17, 20, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 19, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 20, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 4, 32, 10, 32, 11, 16, 18, 0, 4, 2, 19, 11, 0, 1, 18, 4, 75, 1, 10, 0, 2, 13, 75, 0, 129, 10, 0, 6, 33, 11, 33, 10, 32, 12, 32, 13, 17, 19, 0, 128, 0, 17, 13, 0, 68, 0, 74, 24, 12, 0, 3, 13, 77, 0, 0, 3, 33, 13, 33, 12, 17, 8, 0, 131, 0, 68, 5, 0, 1, 17, 8, 0, 131, 0, 68, 5, 0, 5, 33, 9, 33, 8, 32, 14, 32, 15, 17, 15, 0, 3, 0, 75, 3, 14, 0, 6, 13, 79, 0, 129, 5, 0, 5, 33, 15, 32, 16, 32, 17, 17, 20, 0, 128, 0, 17, 17, 0, 70, 0, 74, 24, 16, 0, 7, 13, 81, 0, 0, 6, 33, 17, 33, 16, 17, 0, 0, 14, 0, 33, 14, 17, 20, 0, 128, 0, 33, 6, 69, 19, 0, 0, 8, 11, 0, 2, 17, 19, 0, 128, 0, 33, 4, 64, 1, 0, 69, 19, 0, 0, 10, 14, 1, 0, 65, 0, 0, 71, 4, 0, 7, 8, 10, 1, 0, 71, 6, 0, 7, 9, 255, 1, 0, 69, 20, 0, 0, 9, 12, 1, 0, 71, 4, 0, 7, 10, 255, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

/-- `stateful_generic_lib_built_phase.amir` (`756` bytes, `fp16 = [198, 148]`, `defaultPhase = .built`),
    encoding the actual `MirPhase::Built` graphs from `bodies_stateful_generic_lib_always_encode.json[0, 2, 4, 6, 10, 12]`
    (including the 15-block, 18-local `Built` graph of `transactional_step` `symId = 65` with NO drop flags `_19`/`_20`)
    plus `DropGlue<Guard>` (`7`) and `core::mem::drop::<Guard>` (`24`). -/
def realStatefulGenericLibBuiltAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 1, 11, 198, 148, 8, 1, 1, 1, 1, 9, 2, 5, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 4, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 4, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 4, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 1, 0, 65, 2, 2, 1, 1, 5, 1, 3, 1, 22, 1, 6, 3, 0, 5, 32, 2, 32, 3, 19, 3, 0, 1, 1, 6, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 2, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 1, 0, 65, 3, 3, 1, 1, 10, 2, 6, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 5, 131, 2, 0, 0, 74, 27, 7, 0, 255, 5, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 5, 73, 0, 129, 100, 0, 1, 33, 9, 64, 1, 0, 65, 4, 63, 1, 1, 10, 3, 5, 4, 6, 5, 4, 1, 4, 1, 6, 4, 4, 0, 5, 32, 4, 17, 4, 0, 131, 0, 33, 4, 48, 2, 4, 32, 5, 73, 38, 5, 0, 1, 4, 0, 4, 34, 32, 6, 32, 7, 19, 7, 0, 1, 1, 4, 75, 1, 6, 0, 2, 4, 71, 0, 129, 4, 0, 6, 33, 7, 33, 6, 32, 8, 17, 8, 0, 3, 0, 32, 9, 17, 9, 0, 5, 0, 75, 40, 0, 0, 3, 4, 72, 0, 73, 0, 0, 3, 33, 9, 33, 8, 33, 5, 64, 1, 0, 65, 5, 64, 1, 1, 7, 3, 3, 4, 6, 5, 4, 6, 5, 4, 0, 6, 32, 4, 19, 4, 0, 1, 1, 4, 32, 5, 17, 5, 0, 2, 0, 32, 6, 17, 6, 0, 3, 0, 76, 63, 0, 0, 1, 2, 68, 0, 69, 0, 70, 0, 0, 3, 33, 6, 33, 5, 33, 4, 64, 1, 0, 65, 6, 65, 1, 1, 18, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 1, 6, 1, 8, 3, 2, 1, 8, 0, 15, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 34, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 34, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 3, 32, 10, 32, 11, 19, 11, 0, 1, 4, 2, 75, 1, 10, 0, 2, 12, 75, 0, 129, 10, 0, 5, 33, 11, 33, 10, 32, 12, 32, 13, 17, 13, 0, 68, 0, 74, 24, 12, 0, 3, 11, 77, 0, 0, 3, 33, 13, 33, 12, 17, 8, 0, 131, 0, 68, 5, 0, 1, 17, 8, 0, 131, 0, 68, 5, 0, 5, 33, 9, 33, 8, 32, 14, 32, 15, 17, 15, 0, 3, 0, 75, 3, 14, 0, 6, 12, 79, 0, 129, 5, 0, 5, 33, 15, 34, 32, 16, 32, 17, 17, 17, 0, 70, 0, 74, 24, 16, 0, 7, 10, 81, 0, 0, 4, 33, 17, 33, 16, 17, 0, 0, 14, 0, 33, 14, 71, 6, 0, 7, 8, 13, 0, 1, 33, 6, 71, 4, 0, 7, 9, 14, 0, 1, 33, 4, 64, 1, 0, 71, 17, 0, 7, 12, 255, 1, 0, 71, 13, 0, 7, 12, 255, 1, 0, 71, 6, 0, 7, 13, 255, 1, 0, 71, 4, 0, 7, 14, 255, 1, 0, 65, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

/-- `client_contract_user_always_encode.amir` (`96` bytes, `fp16 = [154, 137]`),
    containing `client_contract_entry` (`symId = 66`). -/
def realClientContractUserAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 154, 137, 1, 1, 66, 1, 3, 9, 3, 3, 4, 6, 5, 4, 4, 6, 5, 4, 4, 0, 7, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 32, 6, 17, 6, 0, 2, 0, 32, 7, 17, 7, 0, 3, 0, 76, 63, 4, 0, 1, 252, 69, 0, 70, 0, 71, 0, 0, 5, 33, 7, 33, 6, 33, 5, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 2, 252, 72, 0, 130, 8, 0, 2, 33, 8, 33, 4, 64]

/-- `client_direct_mir_inspector_always_encode.amir` (`167` bytes, `fp16 = [65, 139]`),
    containing `client_audit_entry` (`symId = 67`). -/
def realClientDirectMirInspectorAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 65, 139, 1, 1, 67, 1, 3, 14, 4, 6, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 1, 252, 70, 0, 71, 0, 130, 16, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 2, 252, 73, 0, 74, 0, 75, 0, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 4, 3, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 5, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 5, 0, 3, 33, 12, 33, 8, 33, 5, 64]

/-! ## 2. Matched Charon `0.1.210` Strongest-Flags `.amir` v3 Byte Streams (`N2`, `#68` §4.4 & §6 N2) -/

/-- `charon_h3_stateful_generic_lib.amir` (`886` bytes, `fp16 = [163, 72]`), translated from
    `stateful_generic_lib_strongest.ullbc` (`--ullbc --precise-drops --mir elaborated --extract-opaque-bodies --rustc-arg=-Zmir-preserve-ub --rustc-arg=-Zalways-encode-mir=yes`). -/
def charonH3StatefulGenericLibAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 163, 72, 8, 1, 1, 1, 3, 9, 2, 7, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 4, 16, 0, 0, 131, 0, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 2, 1, 68, 0, 129, 1, 1, 0, 65, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 4, 3, 71, 0, 129, 16, 1, 0, 65, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 6, 5, 70, 0, 72, 0, 1, 0, 65, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 16, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 3, 1, 22, 1, 6, 3, 6, 0, 8, 32, 5, 16, 0, 0, 131, 0, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 2, 1, 67, 0, 68, 0, 1, 0, 65, 0, 4, 33, 4, 33, 3, 33, 2, 16, 0, 0, 131, 0, 64, 3, 3, 1, 3, 6, 2, 7, 3, 2, 3, 2, 19, 3, 0, 2, 32, 3, 17, 3, 0, 1, 0, 69, 67, 0, 0, 2, 1, 0, 1, 32, 4, 74, 26, 4, 0, 4, 3, 131, 2, 0, 3, 33, 3, 32, 5, 17, 5, 0, 2, 0, 75, 20, 0, 0, 6, 5, 69, 0, 129, 100, 1, 0, 65, 0, 0, 74, 27, 0, 0, 255, 3, 131, 2, 1, 0, 65, 0, 1, 33, 5, 64, 4, 63, 1, 3, 12, 3, 12, 4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19, 0, 2, 32, 9, 32, 10, 73, 37, 10, 0, 8, 7, 1, 0, 65, 0, 3, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 75, 1, 5, 0, 4, 3, 70, 0, 129, 4, 1, 0, 65, 0, 6, 33, 6, 33, 5, 32, 7, 17, 7, 0, 3, 0, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 6, 5, 71, 0, 72, 0, 1, 0, 65, 0, 3, 33, 8, 33, 7, 33, 4, 64, 0, 0, 67, 0, 1, 21, 9, 0, 5, 74, 0, 130, 0, 69, 73, 0, 0, 10, 9, 0, 4, 33, 10, 33, 9, 48, 2, 4, 32, 4, 73, 38, 4, 0, 2, 1, 0, 2, 33, 10, 32, 11, 74, 26, 11, 0, 11, 7, 131, 2, 0, 0, 74, 27, 0, 0, 255, 7, 131, 2, 5, 64, 1, 3, 7, 3, 3, 4, 6, 5, 4, 6, 5, 4, 0, 6, 32, 4, 19, 4, 0, 1, 1, 4, 32, 5, 17, 5, 0, 2, 0, 32, 6, 17, 6, 0, 3, 0, 76, 63, 0, 0, 2, 1, 68, 0, 69, 0, 70, 0, 1, 0, 65, 0, 3, 33, 6, 33, 5, 33, 4, 64, 6, 65, 1, 3, 20, 3, 16, 3, 6, 6, 2, 8, 6, 8, 6, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 19, 32, 17, 32, 18, 32, 19, 17, 18, 0, 128, 0, 17, 19, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 18, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 19, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 17, 8, 0, 3, 0, 69, 72, 0, 0, 4, 1, 0, 4, 32, 9, 32, 10, 16, 17, 0, 4, 2, 19, 10, 0, 1, 17, 4, 75, 1, 9, 0, 3, 2, 74, 0, 129, 10, 0, 0, 69, 19, 0, 0, 6, 5, 0, 6, 33, 10, 33, 9, 32, 11, 32, 12, 17, 18, 0, 128, 0, 17, 12, 0, 68, 0, 74, 24, 11, 0, 7, 2, 76, 0, 0, 4, 33, 8, 32, 13, 32, 14, 17, 14, 0, 3, 0, 75, 3, 13, 0, 8, 2, 78, 0, 129, 5, 0, 0, 71, 6, 0, 7, 6, 9, 0, 0, 69, 18, 0, 0, 11, 10, 0, 2, 33, 12, 33, 11, 68, 4, 0, 5, 33, 14, 32, 15, 32, 16, 17, 19, 0, 128, 0, 17, 16, 0, 70, 0, 74, 24, 15, 0, 12, 2, 80, 0, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 11, 13, 1, 0, 65, 0, 6, 33, 16, 33, 15, 17, 0, 0, 13, 0, 33, 13, 17, 19, 0, 128, 0, 33, 6, 69, 18, 0, 0, 15, 14, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 15, 11, 0, 2, 17, 18, 0, 128, 0, 33, 4, 64, 7, 7, 2, 3, 4, 1, 3, 1, 22, 22, 1, 0, 4, 32, 2, 32, 3, 16, 0, 0, 131, 0, 19, 2, 0, 1, 1, 4, 74, 2, 3, 0, 2, 1, 66, 0, 1, 0, 65, 0, 0, 64, 8, 24, 3, 3, 2, 1, 3, 1, 8, 0, 1, 16, 0, 0, 131, 0, 71, 1, 0, 7, 2, 1, 1, 0, 65, 0, 0, 64]

/-- `charon_h3_client_contract_user.amir` (`102` bytes, `fp16 = [160, 180]`), translated from
    `client_contract_user_strongest.ullbc`. -/
def charonH3ClientContractUserAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 160, 180, 1, 1, 66, 1, 3, 9, 3, 5, 4, 6, 5, 4, 4, 6, 5, 4, 4, 0, 7, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 32, 6, 17, 6, 0, 2, 0, 32, 7, 17, 7, 0, 3, 0, 76, 63, 4, 0, 2, 1, 69, 0, 70, 0, 71, 0, 1, 0, 65, 0, 5, 33, 7, 33, 6, 33, 5, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 4, 3, 72, 0, 130, 8, 1, 0, 65, 0, 2, 33, 8, 33, 4, 64]

/-- `charon_h3_client_direct_mir_inspector.amir` (`173` bytes, `fp16 = [29, 2]`), translated from
    `client_direct_mir_inspector_strongest.ullbc`. -/
def charonH3ClientDirectMirInspectorAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 29, 2, 1, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64]

/-- `charon_h3_linked_inspector_and_lib.amir` (`1,049` bytes, `fp16 = [44, 164]`), linking
    `client_direct_mir_inspector_strongest.ullbc` and `stateful_generic_lib_strongest.ullbc`. -/
def charonH3LinkedInspectorAndLibAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 44, 164, 9, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64] ++
  charonH3StatefulGenericLibAmirBytes.drop 10

def decodePackageBodies (bytes : List Nat) : List WireBody :=
  match parseRawPackageBytes bytes with
  | .ok (pkg, []) => pkg.bodies
  | _ => []

/-! ## 3. Compilation-Bound Layout Sidecar Table (`N1` Item 4 & `N5`, `#68` §§4.5, 6 N1) -/

/-- Single entry in a compilation-bound layout table (`tcx.layout_of` sidecar in `out_*.json`). -/
structure CompilerTypeLayoutEntry where
  typeName : String
  typeTag : MirTypeTag
  sizeBytes : Nat
  alignBytes : Nat
  deriving DecidableEq, Repr

/-- Compilation-bound layout table tying `tcx.layout_of` facts to an exact
    `ExpectedCargoInvocationContext` (`crateName`, `svhFingerprintLo`, `sourceContentSha256Hi64`).
    Explicitly labeled under `ASSUMP-LAYOUT-01` as a producer-captured compiler layout sidecar. -/
structure BoundCompilerLayoutTable where
  crateName : String
  crateNameBytes : List Nat
  svhFingerprintLo : Nat
  sourceContentSha256Hi64 : Nat
  entries : List CompilerTypeLayoutEntry
  deriving DecidableEq, Repr

def lookupTypeLayoutByTag : List CompilerTypeLayoutEntry → MirTypeTag → Option CompilerTypeLayoutEntry
  | [], _ => none
  | e :: es, tag =>
      bif Nat.beq (specEncodeTypeTag e.typeTag) (specEncodeTypeTag tag) then some e
      else lookupTypeLayoutByTag es tag

def checkLayoutTableBinding
    (ctx : ExpectedCargoInvocationContext)
    (expectedCrateBytes : List Nat)
    (tbl : BoundCompilerLayoutTable) : Bool :=
  listNatBeq tbl.crateNameBytes expectedCrateBytes &&
  Nat.beq tbl.svhFingerprintLo ctx.expectedSvhLo &&
  Nat.beq tbl.sourceContentSha256Hi64 ctx.expectedSourceContentSha256Hi64

/-- Synthesize monomorphized `core::mem::size_of::<T>()` (`symId = 37`) and
    `core::mem::align_of::<T>()` (`symId = 38`) bodies from a verified `BoundCompilerLayoutTable`
    when `checkLayoutTableBinding ctx expectedCrateBytes tbl = true`. Fails closed (`[]`) if the
    layout table's compilation binding or requested type entry does not match. -/
def deriveLayoutCalleeBodies
    (ctx : ExpectedCargoInvocationContext)
    (expectedCrateBytes : List Nat)
    (tbl : BoundCompilerLayoutTable)
    (typeTag : MirTypeTag) : List WireBody :=
  bif checkLayoutTableBinding ctx expectedCrateBytes tbl then
    match lookupTypeLayoutByTag tbl.entries typeTag with
    | some entry =>
        [ { bodyId := 98
          , symId := 37
          , originKind := .externalOptimized
          , mirPhase := .runtimeOptimized
          , localCount := 1
          , argCount := 0
          , localTypes := [.usize]
          , blocks :=
              [ { isCleanup := false
                , stmts := [.assignUseRetagYes { localIdx := 0, proj := .here } (.constUsize entry.sizeBytes)]
                , term := .ret } ] }
        , { bodyId := 99
          , symId := 38
          , originKind := .externalOptimized
          , mirPhase := .runtimeOptimized
          , localCount := 1
          , argCount := 0
          , localTypes := [.usize]
          , blocks :=
              [ { isCleanup := false
                , stmts := [.assignUseRetagYes { localIdx := 0, proj := .here } (.constUsize entry.alignBytes)]
                , term := .ret } ] } ]
    | none => []
  else
    []

/-! ## 4. Per-Invocation Cargo Binding for the 3-Crate Workspace (`H6`/`H7` & `N1`) -/

def statefulGenericLibCrateBytes : List Nat :=
  [115, 116, 97, 116, 101, 102, 117, 108, 95, 103, 101, 110, 101, 114, 105, 99, 95, 108, 105, 98]

def clientContractUserCrateBytes : List Nat :=
  [99, 108, 105, 101, 110, 116, 95, 99, 111, 110, 116, 114, 97, 99, 116, 95, 117, 115, 101, 114]

def clientDirectMirInspectorCrateBytes : List Nat :=
  [99, 108, 105, 101, 110, 116, 95, 100, 105, 114, 101, 99, 116, 95, 109, 105, 114, 95, 105, 110, 115, 112, 101, 99, 116, 111, 114]

def statefulGenericLibExpectedCtx : ExpectedCargoInvocationContext :=
  { expectedCrateName := "stateful_generic_lib"
  , expectedFeatures := []
  , expectedCfgFlags := []
  , reqAlwaysEncodeMir := true
  , reqPreserveUb := true
  , expectedSvhLo := 6197821298087832015
  , expectedExternalDepSvhs := [("core", 3402364753734922174)]
  , expectedSourceContentSha256Hi64 := 0x3e293f9cc065f24c
  , expectedGeneratedOutDirFileDigestTag := none }

def statefulGenericLibLayoutTable : BoundCompilerLayoutTable :=
  { crateName := "stateful_generic_lib"
  , crateNameBytes := statefulGenericLibCrateBytes
  , svhFingerprintLo := 6197821298087832015
  , sourceContentSha256Hi64 := 0x3e293f9cc065f24c
  , entries :=
      [ { typeName := "u32", typeTag := .u32, sizeBytes := 4, alignBytes := 4 }
      , { typeName := "EffectLog", typeTag := .effectLog, sizeBytes := 8, alignBytes := 4 }
      , { typeName := "Guard", typeTag := .guard, sizeBytes := 16, alignBytes := 8 } ] }

def u32LayoutCalleeBodies : List WireBody :=
  deriveLayoutCalleeBodies statefulGenericLibExpectedCtx statefulGenericLibCrateBytes
    statefulGenericLibLayoutTable .u32

/-- Retained alias for backward compatibility with existing references. -/
def alignOfU32CalleeInstanceBody : WireBody :=
  { bodyId := 99
  , symId := 38
  , originKind := .externalOptimized
  , mirPhase := .runtimeOptimized
  , localCount := 1
  , argCount := 0
  , localTypes := [.usize]
  , blocks :=
      [ { isCleanup := false
        , stmts := [.assignUseRetagYes { localIdx := 0, proj := .here } (.constUsize 4)]
        , term := .ret } ] }

def statefulGenericLibBodies : List WireBody :=
  decodePackageBodies realStatefulGenericLibAmirBytes ++ u32LayoutCalleeBodies

def statefulGenericLibBuiltBodies : List WireBody :=
  decodePackageBodies realStatefulGenericLibBuiltAmirBytes ++ u32LayoutCalleeBodies

def clientContractUserBodies : List WireBody :=
  decodePackageBodies realClientContractUserAmirBytes

def clientDirectMirInspectorBodies : List WireBody :=
  decodePackageBodies realClientDirectMirInspectorAmirBytes

def linkedInspectorAndLibBodies : List WireBody :=
  clientDirectMirInspectorBodies ++ statefulGenericLibBodies

def charonStatefulGenericLibBodies : List WireBody :=
  decodePackageBodies charonH3StatefulGenericLibAmirBytes ++ u32LayoutCalleeBodies

def charonClientContractUserBodies : List WireBody :=
  decodePackageBodies charonH3ClientContractUserAmirBytes

def charonClientDirectMirInspectorBodies : List WireBody :=
  decodePackageBodies charonH3ClientDirectMirInspectorAmirBytes

def charonLinkedInspectorAndLibBodies : List WireBody :=
  decodePackageBodies charonH3LinkedInspectorAndLibAmirBytes ++ u32LayoutCalleeBodies

def statefulGenericLibBindingRec : CargoInvocationBindingRecord :=
  { crateName := "stateful_generic_lib"
  , role := .targetCrate
  , features := []
  , cfgFlags := []
  , alwaysEncodeMir := true
  , preserveUb := true
  , svhFingerprintLo := 6197821298087832015
  , externalDepSvhs := [("core", 3402364753734922174)]
  , sourceContentSha256Hi64 := 0x3e293f9cc065f24c
  , generatedOutDirFileDigestTag := none
  , completeness := .acceptedComplete
  , expectedFp16 := (153, 48) }

def statefulGenericLibBuiltBindingRec : CargoInvocationBindingRecord :=
  { statefulGenericLibBindingRec with expectedFp16 := (198, 148) }

def clientContractUserExpectedCtx : ExpectedCargoInvocationContext :=
  { expectedCrateName := "client_contract_user"
  , expectedFeatures := []
  , expectedCfgFlags := []
  , reqAlwaysEncodeMir := true
  , reqPreserveUb := true
  , expectedSvhLo := 981680503637594314
  , expectedExternalDepSvhs :=
      [ ("core", 3402364753734922174)
      , ("stateful_generic_lib", 6197821298087832015) ]
  , expectedSourceContentSha256Hi64 := 0x1f3f74fb50d6e764
  , expectedGeneratedOutDirFileDigestTag := none }

def clientContractUserBindingRec : CargoInvocationBindingRecord :=
  { crateName := "client_contract_user"
  , role := .targetCrate
  , features := []
  , cfgFlags := []
  , alwaysEncodeMir := true
  , preserveUb := true
  , svhFingerprintLo := 981680503637594314
  , externalDepSvhs :=
      [ ("core", 3402364753734922174)
      , ("stateful_generic_lib", 6197821298087832015) ]
  , sourceContentSha256Hi64 := 0x1f3f74fb50d6e764
  , generatedOutDirFileDigestTag := none
  , completeness := .acceptedComplete
  , expectedFp16 := (154, 137) }

def clientDirectMirInspectorExpectedCtx : ExpectedCargoInvocationContext :=
  { expectedCrateName := "client_direct_mir_inspector"
  , expectedFeatures := []
  , expectedCfgFlags := []
  , reqAlwaysEncodeMir := true
  , reqPreserveUb := true
  , expectedSvhLo := 12124704303001870283
  , expectedExternalDepSvhs :=
      [ ("core", 3402364753734922174)
      , ("stateful_generic_lib", 6197821298087832015) ]
  , expectedSourceContentSha256Hi64 := 0xf48865b90c1d5c2f
  , expectedGeneratedOutDirFileDigestTag := none }

def clientDirectMirInspectorBindingRec : CargoInvocationBindingRecord :=
  { crateName := "client_direct_mir_inspector"
  , role := .targetCrate
  , features := []
  , cfgFlags := []
  , alwaysEncodeMir := true
  , preserveUb := true
  , svhFingerprintLo := 12124704303001870283
  , externalDepSvhs :=
      [ ("core", 3402364753734922174)
      , ("stateful_generic_lib", 6197821298087832015) ]
  , sourceContentSha256Hi64 := 0xf48865b90c1d5c2f
  , generatedOutDirFileDigestTag := none
  , completeness := .acceptedComplete
  , expectedFp16 := (65, 139) }

theorem h3_three_crate_workspace_bindings_and_admission_verified :
    verifyCargoInvocationBinding statefulGenericLibExpectedCtx statefulGenericLibBindingRec
      statefulGenericLibCrateBytes realStatefulGenericLibAmirBytes = true ∧
    verifyCargoInvocationBinding clientContractUserExpectedCtx clientContractUserBindingRec
      clientContractUserCrateBytes realClientContractUserAmirBytes = true ∧
    verifyCargoInvocationBinding clientDirectMirInspectorExpectedCtx clientDirectMirInspectorBindingRec
      clientDirectMirInspectorCrateBytes realClientDirectMirInspectorAmirBytes = true ∧
    checkLayoutTableBinding statefulGenericLibExpectedCtx statefulGenericLibCrateBytes
      statefulGenericLibLayoutTable = true ∧
    isAdmittedPackageBytes realStatefulGenericLibAmirBytes = true ∧
    isAdmittedPackageBytes realStatefulGenericLibBuiltAmirBytes = true ∧
    checkBodiesClosure linkedInspectorAndLibBodies linkedInspectorAndLibBodies = true := by
  decide

/-! ## 5. `N1` (`#68` §4.1 & §6 N1): Universal Operational Library & Modular Client Proofs -/

/-- Execute `step_generic_slot::<u32>(log, ptr, base)` (`symId = 63`) on `bodies` with explicit
    step fuel via the general `SemanticVerticalSliceCore.runSteps` stack machine. -/
def evalStepGenericSlotWithFuel (bodies : List WireBody) (fuel : Nat) (s0 t0 : Nat) (ptrValid : Bool) (base : Nat) :
    ExecStatus × HeapLogSlot × List Nat :=
  let initSt := initEntryStateWithHeap bodies 63
    [.heapPtr 0, .extPtr ptrValid, .scalar base]
    [{ stepCount := s0, traceAcc := t0 }]
  let finalSt := runSteps bodies fuel initSt
  let slot0 := match finalSt.heap with
    | h :: _ => h
    | [] => { stepCount := 0, traceAcc := 0 }
  (finalSt.status, slot0, finalSt.obsEvents)

def evalStepGenericSlot (bodies : List WireBody) (s0 t0 : Nat) (ptrValid : Bool) (base : Nat) :
    ExecStatus × HeapLogSlot × List Nat :=
  evalStepGenericSlotWithFuel bodies 12 s0 t0 ptrValid base

/-- Symbolic decoded-AST summary for `step_generic_slot::<u32>` (`symId = 63`), retained alongside
    the universal operational bridge theorem `step_generic_slot_symbolic_summary_matches_runSteps_universal`. -/
def evalDecodedStepGenericSlotSymbolic (bodies : List WireBody) (ptrValid : Bool) (base : Nat) :
    Option (ExecStatus × HeapLogSlot × List Nat) :=
  match findBodyBySym bodies 63 with
  | some b =>
      match getBlockAt b.blocks 0, getBlockAt b.blocks 1, getBlockAt b.blocks 2, getBlockAt b.blocks 3 with
      | some bb0, some bb1, some bb2, some bb3 =>
          match bb0.term, bb1.term, bb2.term, bb3.term with
          | .call0 38 dst5 (some 1) _,
            .call2 1 _ (some 2) _ _ (.constU32 evTag),
            .call2 40 dst0 (some 3) _ _ _,
            .ret =>
              if dst5.localIdx == 5 && dst0.localIdx == 0 then
                if stmtsHavePlaceMention bb0.stmts && !ptrValid then
                  some (.ub, { stepCount := 0, traceAcc := 0 }, [])
                else
                  some (.returned (.scalar ((base + 4) % usizeMod)), { stepCount := 1, traceAcc := evTag }, [evTag])
              else none
          | _, _, _, _ => none
      | _, _, _, _ => none
  | none => none

/-- **Universal Operational Bridge (`N1`, `#68` §4.1 & §6 N1 Item 1)**:
    For **every** `ptrValid : Bool` and **every** `base : Nat`, `evalStepGenericSlot` (full stack-machine
    `runSteps` over the decoded `statefulGenericLibBodies` AST) reduces to the exact operational outcome,
    and agrees universally with `evalDecodedStepGenericSlotSymbolic`. -/
def blocks_D_1_0 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 3, WireStmt.storageLive 4, WireStmt.assignUseRetagYes { localIdx := 4, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField0 })], term := WireTerm.call2 20 { localIdx := 3, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) (OperandSpec.constU32 1) }, { isCleanup := false, stmts := [WireStmt.storageDead 4, WireStmt.assignUseRetagYes { localIdx := 1, proj := ProjChain.derefField0 } (OperandSpec.move { localIdx := 3, proj := ProjChain.here }), WireStmt.storageDead 3, WireStmt.storageLive 5, WireStmt.storageLive 6, WireStmt.storageLive 7, WireStmt.assignUseRetagYes { localIdx := 7, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField1 })], term := WireTerm.call2 21 { localIdx := 6, proj := ProjChain.here } (some 2) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.constU32 16) }, { isCleanup := false, stmts := [WireStmt.storageDead 7, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here })], term := WireTerm.call2 20 { localIdx := 5, proj := ProjChain.here } (some 3) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) }, { isCleanup := false, stmts := [WireStmt.storageDead 8, WireStmt.storageDead 6, WireStmt.assignUseRetagYes { localIdx := 1, proj := ProjChain.derefField1 } (OperandSpec.move { localIdx := 5, proj := ProjChain.here }), WireStmt.storageDead 5, WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit)], term := WireTerm.ret }]
def body_D_1_0 : WireBody := { bodyId := 1, symId := 1, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 9, argCount := 2, localTypes := [MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32], blocks := blocks_D_1_0 }
def blocks_D_2_1 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 2, WireStmt.storageLive 3, WireStmt.assignUseNoRetag { localIdx := 5, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField1 }), WireStmt.assignRefOrPtr { localIdx := 3, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 5, proj := ProjChain.deref }, WireStmt.storageLive 4, WireStmt.assignUseRetagYes { localIdx := 4, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField0 })], term := WireTerm.call2 1 { localIdx := 2, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 3, proj := ProjChain.here }) (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) }, { isCleanup := false, stmts := [WireStmt.storageDead 4, WireStmt.storageDead 3, WireStmt.storageDead 2, WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit)], term := WireTerm.ret }]
def body_D_2_1 : WireBody := { bodyId := 2, symId := 2, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 6, argCount := 1, localTypes := [MirTypeTag.unit, MirTypeTag.refGuard, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.refMutEffectLog], blocks := blocks_D_2_1 }
def blocks_D_3_2 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 3, WireStmt.storageLive 4, WireStmt.assignUseRetagYes { localIdx := 4, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.here })], term := WireTerm.switchInt1 (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) 0 3 1 }, { isCleanup := false, stmts := [WireStmt.storageLive 7, WireStmt.storageLive 8], term := WireTerm.call1 26 { localIdx := 8, proj := ProjChain.here } (some 2) (UnwindSpec.continueUnwind) (OperandSpec.constPanicStr) }, { isCleanup := false, stmts := [], term := WireTerm.call1 27 { localIdx := 7, proj := ProjChain.here } none (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) }, { isCleanup := false, stmts := [WireStmt.assignUseRetagYes { localIdx := 3, proj := ProjChain.here } (OperandSpec.constUnit), WireStmt.storageDead 4, WireStmt.storageDead 3, WireStmt.storageLive 9, WireStmt.assignUseRetagYes { localIdx := 9, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here })], term := WireTerm.call2 20 { localIdx := 0, proj := ProjChain.here } (some 4) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 9, proj := ProjChain.here }) (OperandSpec.constU32 100) }, { isCleanup := false, stmts := [WireStmt.storageDead 9], term := WireTerm.ret }]
def body_D_3_2 : WireBody := { bodyId := 3, symId := 3, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 10, argCount := 2, localTypes := [MirTypeTag.u32, MirTypeTag.bool, MirTypeTag.u32, MirTypeTag.unit, MirTypeTag.bool, MirTypeTag.panicOrNever, MirTypeTag.panicOrNever, MirTypeTag.panicOrNever, MirTypeTag.panicOrNever, MirTypeTag.u32], blocks := blocks_D_3_2 }
def blocks_D_63_3 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 4, WireStmt.assignUseRetagYes { localIdx := 4, proj := ProjChain.here } (OperandSpec.constUnit), WireStmt.storageDead 4, WireStmt.placeMention { localIdx := 2, proj := ProjChain.deref }, WireStmt.storageLive 5], term := WireTerm.call0 38 { localIdx := 5, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) }, { isCleanup := false, stmts := [WireStmt.storageLive 6, WireStmt.storageLive 7, WireStmt.assignRefOrPtr { localIdx := 7, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }], term := WireTerm.call2 1 { localIdx := 6, proj := ProjChain.here } (some 2) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.constU32 4) }, { isCleanup := false, stmts := [WireStmt.storageDead 7, WireStmt.storageDead 6, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here }), WireStmt.storageLive 9, WireStmt.assignUseRetagYes { localIdx := 9, proj := ProjChain.here } (OperandSpec.copy { localIdx := 5, proj := ProjChain.here })], term := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 3) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) (OperandSpec.move { localIdx := 9, proj := ProjChain.here }) }, { isCleanup := false, stmts := [WireStmt.storageDead 9, WireStmt.storageDead 8, WireStmt.storageDead 5], term := WireTerm.ret }]
def body_D_63_3 : WireBody := { bodyId := 4, symId := 63, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 10, argCount := 3, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize], blocks := blocks_D_63_3 }
def blocks_D_64_4 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 4, WireStmt.assignRefOrPtr { localIdx := 4, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }, WireStmt.storageLive 5, WireStmt.assignUseRetagYes { localIdx := 5, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here }), WireStmt.storageLive 6, WireStmt.assignUseRetagYes { localIdx := 6, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here })], term := WireTerm.call3 63 { localIdx := 0, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) }, { isCleanup := false, stmts := [WireStmt.storageDead 6, WireStmt.storageDead 5, WireStmt.storageDead 4], term := WireTerm.ret }]
def body_D_64_4 : WireBody := { bodyId := 5, symId := 64, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 7, argCount := 3, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize], blocks := blocks_D_64_4 }
def blocks_D_65_5 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.assignUseRetagYes { localIdx := 19, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.assignUseRetagYes { localIdx := 20, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.storageLive 4, WireStmt.storageLive 5, WireStmt.assignRefOrPtr { localIdx := 5, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }, WireStmt.assignUseRetagYes { localIdx := 19, proj := ProjChain.here } (OperandSpec.constBool true), WireStmt.assignAgg2 { localIdx := 4, proj := ProjChain.here } (Agg2Kind.guard) (OperandSpec.constU32 1) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }), WireStmt.storageDead 5, WireStmt.storageLive 6, WireStmt.storageLive 7, WireStmt.assignRefOrPtr { localIdx := 7, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 2, proj := ProjChain.deref }, WireStmt.assignUseRetagYes { localIdx := 20, proj := ProjChain.here } (OperandSpec.constBool true), WireStmt.assignAgg2 { localIdx := 6, proj := ProjChain.here } (Agg2Kind.guard) (OperandSpec.constU32 2) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), WireStmt.storageDead 7, WireStmt.storageLive 8, WireStmt.storageLive 9, WireStmt.assignUseRetagYes { localIdx := 9, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here })], term := WireTerm.switchInt1 (OperandSpec.move { localIdx := 9, proj := ProjChain.here }) 0 4 1 }, { isCleanup := false, stmts := [WireStmt.storageLive 10, WireStmt.storageLive 11, WireStmt.assignUseNoRetag { localIdx := 18, proj := ProjChain.here } (OperandSpec.copy { localIdx := 4, proj := ProjChain.field1 }), WireStmt.assignRefOrPtr { localIdx := 11, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 18, proj := ProjChain.deref }], term := WireTerm.call2 1 { localIdx := 10, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 13) (OperandSpec.move { localIdx := 11, proj := ProjChain.here }) (OperandSpec.constU32 10) }, { isCleanup := false, stmts := [WireStmt.storageDead 11, WireStmt.storageDead 10, WireStmt.storageLive 12, WireStmt.storageLive 13, WireStmt.assignUseRetagYes { localIdx := 19, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.assignUseRetagYes { localIdx := 13, proj := ProjChain.here } (OperandSpec.move { localIdx := 4, proj := ProjChain.here })], term := WireTerm.call1 24 { localIdx := 12, proj := ProjChain.here } (some 3) (UnwindSpec.cleanup 13) (OperandSpec.move { localIdx := 13, proj := ProjChain.here }) }, { isCleanup := false, stmts := [WireStmt.storageDead 13, WireStmt.storageDead 12, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.constUnit)], term := WireTerm.goto 5 }, { isCleanup := false, stmts := [WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.constUnit)], term := WireTerm.goto 5 }, { isCleanup := false, stmts := [WireStmt.storageDead 9, WireStmt.storageDead 8, WireStmt.storageLive 14, WireStmt.storageLive 15, WireStmt.assignUseRetagYes { localIdx := 15, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here })], term := WireTerm.call2 3 { localIdx := 14, proj := ProjChain.here } (some 6) (UnwindSpec.cleanup 13) (OperandSpec.move { localIdx := 15, proj := ProjChain.here }) (OperandSpec.constU32 5) }, { isCleanup := false, stmts := [WireStmt.storageDead 15, WireStmt.storageLive 16, WireStmt.storageLive 17, WireStmt.assignUseRetagYes { localIdx := 20, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.assignUseRetagYes { localIdx := 17, proj := ProjChain.here } (OperandSpec.move { localIdx := 6, proj := ProjChain.here })], term := WireTerm.call1 24 { localIdx := 16, proj := ProjChain.here } (some 7) (UnwindSpec.cleanup 13) (OperandSpec.move { localIdx := 17, proj := ProjChain.here }) }, { isCleanup := false, stmts := [WireStmt.storageDead 17, WireStmt.storageDead 16, WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } (OperandSpec.copy { localIdx := 14, proj := ProjChain.here }), WireStmt.storageDead 14, WireStmt.assignUseRetagYes { localIdx := 20, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.storageDead 6], term := WireTerm.switchInt1 (OperandSpec.copy { localIdx := 19, proj := ProjChain.here }) 0 8 11 }, { isCleanup := false, stmts := [WireStmt.assignUseRetagYes { localIdx := 19, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.storageDead 4], term := WireTerm.ret }, { isCleanup := true, stmts := [], term := WireTerm.switchInt1 (OperandSpec.copy { localIdx := 19, proj := ProjChain.here }) 0 10 14 }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [], term := WireTerm.drop { localIdx := 4, proj := ProjChain.here } 7 8 (UnwindSpec.cleanup 10) }, { isCleanup := true, stmts := [], term := WireTerm.drop { localIdx := 6, proj := ProjChain.here } 7 9 (UnwindSpec.terminateCleanup) }, { isCleanup := true, stmts := [], term := WireTerm.switchInt1 (OperandSpec.copy { localIdx := 20, proj := ProjChain.here }) 0 9 12 }, { isCleanup := true, stmts := [], term := WireTerm.drop { localIdx := 4, proj := ProjChain.here } 7 10 (UnwindSpec.terminateCleanup) }]
def body_D_65_5 : WireBody := { bodyId := 6, symId := 65, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 21, argCount := 3, localTypes := [MirTypeTag.u32, MirTypeTag.refMutEffectLog, MirTypeTag.refMutEffectLog, MirTypeTag.bool, MirTypeTag.guard, MirTypeTag.refMutEffectLog, MirTypeTag.guard, MirTypeTag.refMutEffectLog, MirTypeTag.unit, MirTypeTag.bool, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.unit, MirTypeTag.guard, MirTypeTag.u32, MirTypeTag.bool, MirTypeTag.unit, MirTypeTag.guard, MirTypeTag.refMutEffectLog, MirTypeTag.bool, MirTypeTag.bool], blocks := blocks_D_65_5 }
def blocks_D_7_6 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.assignUseRetagYes { localIdx := 2, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.here })], term := WireTerm.call1 2 { localIdx := 3, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 2, proj := ProjChain.here }) }, { isCleanup := false, stmts := [], term := WireTerm.ret }]
def body_D_7_6 : WireBody := { bodyId := 7, symId := 7, originKind := BodyOriginKind.compilerShim, mirPhase := MirPhaseTag.runtimeOptimized, localCount := 4, argCount := 1, localTypes := [MirTypeTag.unit, MirTypeTag.refGuard, MirTypeTag.refGuard, MirTypeTag.unit], blocks := blocks_D_7_6 }
def blocks_D_24_7 : List WireBlock := [{ isCleanup := false, stmts := [], term := WireTerm.drop { localIdx := 1, proj := ProjChain.here } 7 1 (UnwindSpec.continueUnwind) }, { isCleanup := false, stmts := [], term := WireTerm.ret }]
def body_D_24_7 : WireBody := { bodyId := 8, symId := 24, originKind := BodyOriginKind.externalOptimized, mirPhase := MirPhaseTag.runtimeOptimized, localCount := 2, argCount := 1, localTypes := [MirTypeTag.unit, MirTypeTag.guard], blocks := blocks_D_24_7 }
def blocks_D_37_8 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUsize 4)], term := WireTerm.ret }]
def body_D_37_8 : WireBody := { bodyId := 98, symId := 37, originKind := BodyOriginKind.externalOptimized, mirPhase := MirPhaseTag.runtimeOptimized, localCount := 1, argCount := 0, localTypes := [MirTypeTag.usize], blocks := blocks_D_37_8 }
def blocks_D_38_9 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUsize 4)], term := WireTerm.ret }]
def body_D_38_9 : WireBody := { bodyId := 99, symId := 38, originKind := BodyOriginKind.externalOptimized, mirPhase := MirPhaseTag.runtimeOptimized, localCount := 1, argCount := 0, localTypes := [MirTypeTag.usize], blocks := blocks_D_38_9 }
def statefulGenericLibBodiesVal : List WireBody := [body_D_1_0, body_D_2_1, body_D_3_2, body_D_63_3, body_D_64_4, body_D_65_5, body_D_7_6, body_D_24_7, body_D_37_8, body_D_38_9]
def blocks_DC_66_0 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 4, WireStmt.storageLive 5, WireStmt.assignRefOrPtr { localIdx := 5, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }, WireStmt.storageLive 6, WireStmt.assignUseRetagYes { localIdx := 6, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here }), WireStmt.storageLive 7, WireStmt.assignUseRetagYes { localIdx := 7, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here })], term := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) }, { isCleanup := false, stmts := [WireStmt.storageDead 7, WireStmt.storageDead 6, WireStmt.storageDead 5, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 4, proj := ProjChain.here })], term := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 2) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) (OperandSpec.constUsize 8) }, { isCleanup := false, stmts := [WireStmt.storageDead 8, WireStmt.storageDead 4], term := WireTerm.ret }]
def body_DC_66_0 : WireBody := { bodyId := 1, symId := 66, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 9, argCount := 3, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], blocks := blocks_DC_66_0 }
def clientContractUserBodiesVal : List WireBody := [body_DC_66_0]
def blocks_C_1_0 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.assignUseNoRetag { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit), WireStmt.storageLive 3, WireStmt.storageLive 4, WireStmt.assignUseRetagYes { localIdx := 4, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField0 })], term := WireTerm.call2 20 { localIdx := 3, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) (OperandSpec.constU32 1) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 4, WireStmt.assignUseRetagYes { localIdx := 1, proj := ProjChain.derefField0 } (OperandSpec.move { localIdx := 3, proj := ProjChain.here }), WireStmt.storageDead 3, WireStmt.storageLive 5, WireStmt.storageLive 6, WireStmt.storageLive 7, WireStmt.assignUseRetagYes { localIdx := 7, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField1 })], term := WireTerm.call2 21 { localIdx := 6, proj := ProjChain.here } (some 4) (UnwindSpec.cleanup 3) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.constU32 16) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 7, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here })], term := WireTerm.call2 20 { localIdx := 5, proj := ProjChain.here } (some 6) (UnwindSpec.cleanup 5) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 8, WireStmt.storageDead 6, WireStmt.assignUseRetagYes { localIdx := 1, proj := ProjChain.derefField1 } (OperandSpec.move { localIdx := 5, proj := ProjChain.here }), WireStmt.storageDead 5, WireStmt.assignUseNoRetag { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit)], term := WireTerm.ret }]
def body_C_1_0 : WireBody := { bodyId := 1, symId := 1, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 9, argCount := 2, localTypes := [MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32], blocks := blocks_C_1_0 }
def blocks_C_2_1 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 5, WireStmt.assignUseNoRetag { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit), WireStmt.storageLive 2, WireStmt.storageLive 3, WireStmt.assignUseNoRetag { localIdx := 5, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField1 }), WireStmt.assignRefOrPtr { localIdx := 3, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 5, proj := ProjChain.deref }, WireStmt.storageLive 4, WireStmt.assignUseRetagYes { localIdx := 4, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField0 })], term := WireTerm.call2 1 { localIdx := 2, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 3, proj := ProjChain.here }) (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 4, WireStmt.storageDead 3, WireStmt.storageDead 2, WireStmt.assignUseNoRetag { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit)], term := WireTerm.ret }]
def body_C_2_1 : WireBody := { bodyId := 2, symId := 2, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 6, argCount := 1, localTypes := [MirTypeTag.unit, MirTypeTag.refGuard, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.refMutEffectLog], blocks := blocks_C_2_1 }
def blocks_C_3_2 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 3, WireStmt.assignUseRetagYes { localIdx := 3, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.here })], term := WireTerm.switchInt1 (OperandSpec.move { localIdx := 3, proj := ProjChain.here }) 0 2 1 }, { isCleanup := false, stmts := [WireStmt.storageLive 4], term := WireTerm.call1 26 { localIdx := 4, proj := ProjChain.here } (some 4) (UnwindSpec.cleanup 3) (OperandSpec.constPanicStr) }, { isCleanup := false, stmts := [WireStmt.storageDead 3, WireStmt.storageLive 5, WireStmt.assignUseRetagYes { localIdx := 5, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here })], term := WireTerm.call2 20 { localIdx := 0, proj := ProjChain.here } (some 6) (UnwindSpec.cleanup 5) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.constU32 100) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [], term := WireTerm.call1 27 { localIdx := 0, proj := ProjChain.here } none (UnwindSpec.cleanup 3) (OperandSpec.constPanicStr) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 5], term := WireTerm.ret }]
def body_C_3_2 : WireBody := { bodyId := 3, symId := 3, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 6, argCount := 2, localTypes := [MirTypeTag.u32, MirTypeTag.bool, MirTypeTag.u32, MirTypeTag.bool, MirTypeTag.panicOrNever, MirTypeTag.u32], blocks := blocks_C_3_2 }
def blocks_C_63_3 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 9, WireStmt.storageLive 10], term := WireTerm.call0 37 { localIdx := 10, proj := ProjChain.here } (some 8) (UnwindSpec.cleanup 7) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageLive 5, WireStmt.storageLive 6, WireStmt.assignRefOrPtr { localIdx := 6, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }], term := WireTerm.call2 1 { localIdx := 5, proj := ProjChain.here } (some 4) (UnwindSpec.cleanup 3) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.constU32 4) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 6, WireStmt.storageDead 5, WireStmt.storageLive 7, WireStmt.assignUseRetagYes { localIdx := 7, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here }), WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 4, proj := ProjChain.here })], term := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 6) (UnwindSpec.cleanup 5) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 8, WireStmt.storageDead 7, WireStmt.storageDead 4], term := WireTerm.ret }, { isCleanup := false, stmts := [], term := WireTerm.unreachable }, { isCleanup := false, stmts := [WireStmt.assignBinOp { localIdx := 9, proj := ProjChain.here } (BinOpTag.gt) (OperandSpec.move { localIdx := 10, proj := ProjChain.here }) (OperandSpec.constUsize 0)], term := WireTerm.switchInt1 (OperandSpec.move { localIdx := 9, proj := ProjChain.here }) 0 10 9 }, { isCleanup := false, stmts := [WireStmt.storageDead 10, WireStmt.storageDead 9, WireStmt.placeMention { localIdx := 2, proj := ProjChain.deref }, WireStmt.storageLive 4], term := WireTerm.call0 38 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) }, { isCleanup := false, stmts := [WireStmt.storageDead 10, WireStmt.storageLive 11], term := WireTerm.call1 26 { localIdx := 11, proj := ProjChain.here } (some 11) (UnwindSpec.cleanup 7) (OperandSpec.constPanicStr) }, { isCleanup := false, stmts := [], term := WireTerm.call1 27 { localIdx := 0, proj := ProjChain.here } none (UnwindSpec.cleanup 7) (OperandSpec.constPanicStr) }]
def body_C_63_3 : WireBody := { bodyId := 4, symId := 63, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 12, argCount := 3, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], blocks := blocks_C_63_3 }
def blocks_C_64_4 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 4, WireStmt.assignRefOrPtr { localIdx := 4, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }, WireStmt.storageLive 5, WireStmt.assignUseRetagYes { localIdx := 5, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here }), WireStmt.storageLive 6, WireStmt.assignUseRetagYes { localIdx := 6, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here })], term := WireTerm.call3 63 { localIdx := 0, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 6, WireStmt.storageDead 5, WireStmt.storageDead 4], term := WireTerm.ret }]
def body_C_64_4 : WireBody := { bodyId := 5, symId := 64, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 7, argCount := 3, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize], blocks := blocks_C_64_4 }
def blocks_C_65_5 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 17, WireStmt.storageLive 18, WireStmt.storageLive 19, WireStmt.assignUseRetagYes { localIdx := 18, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.assignUseRetagYes { localIdx := 19, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.storageLive 4, WireStmt.storageLive 5, WireStmt.assignRefOrPtr { localIdx := 5, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }, WireStmt.assignUseRetagYes { localIdx := 18, proj := ProjChain.here } (OperandSpec.constBool true), WireStmt.assignAgg2 { localIdx := 4, proj := ProjChain.here } (Agg2Kind.guard) (OperandSpec.constU32 1) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }), WireStmt.storageDead 5, WireStmt.storageLive 6, WireStmt.storageLive 7, WireStmt.assignRefOrPtr { localIdx := 7, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 2, proj := ProjChain.deref }, WireStmt.assignUseRetagYes { localIdx := 19, proj := ProjChain.here } (OperandSpec.constBool true), WireStmt.assignAgg2 { localIdx := 6, proj := ProjChain.here } (Agg2Kind.guard) (OperandSpec.constU32 2) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), WireStmt.storageDead 7, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here })], term := WireTerm.switchInt1 (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) 0 4 1 }, { isCleanup := false, stmts := [WireStmt.storageLive 9, WireStmt.storageLive 10, WireStmt.assignUseNoRetag { localIdx := 17, proj := ProjChain.here } (OperandSpec.copy { localIdx := 4, proj := ProjChain.field1 }), WireStmt.assignRefOrPtr { localIdx := 10, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 17, proj := ProjChain.deref }], term := WireTerm.call2 1 { localIdx := 9, proj := ProjChain.here } (some 3) (UnwindSpec.cleanup 2) (OperandSpec.move { localIdx := 10, proj := ProjChain.here }) (OperandSpec.constU32 10) }, { isCleanup := false, stmts := [], term := WireTerm.switchInt1 (OperandSpec.copy { localIdx := 19, proj := ProjChain.here }) 0 6 5 }, { isCleanup := false, stmts := [WireStmt.storageDead 10, WireStmt.storageDead 9, WireStmt.storageLive 11, WireStmt.storageLive 12, WireStmt.assignUseRetagYes { localIdx := 18, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.assignUseRetagYes { localIdx := 12, proj := ProjChain.here } (OperandSpec.move { localIdx := 4, proj := ProjChain.here })], term := WireTerm.call1 24 { localIdx := 11, proj := ProjChain.here } (some 7) (UnwindSpec.cleanup 2) (OperandSpec.move { localIdx := 12, proj := ProjChain.here }) }, { isCleanup := false, stmts := [WireStmt.storageDead 8, WireStmt.storageLive 13, WireStmt.storageLive 14, WireStmt.assignUseRetagYes { localIdx := 14, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here })], term := WireTerm.call2 3 { localIdx := 13, proj := ProjChain.here } (some 8) (UnwindSpec.cleanup 2) (OperandSpec.move { localIdx := 14, proj := ProjChain.here }) (OperandSpec.constU32 5) }, { isCleanup := false, stmts := [], term := WireTerm.drop { localIdx := 6, proj := ProjChain.here } 7 6 (UnwindSpec.cleanup 9) }, { isCleanup := false, stmts := [], term := WireTerm.switchInt1 (OperandSpec.copy { localIdx := 18, proj := ProjChain.here }) 0 11 10 }, { isCleanup := false, stmts := [WireStmt.storageDead 12, WireStmt.storageDead 11], term := WireTerm.goto 4 }, { isCleanup := false, stmts := [WireStmt.storageDead 14, WireStmt.storageLive 15, WireStmt.storageLive 16, WireStmt.assignUseRetagYes { localIdx := 19, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.assignUseRetagYes { localIdx := 16, proj := ProjChain.here } (OperandSpec.move { localIdx := 6, proj := ProjChain.here })], term := WireTerm.call1 24 { localIdx := 15, proj := ProjChain.here } (some 12) (UnwindSpec.cleanup 2) (OperandSpec.move { localIdx := 16, proj := ProjChain.here }) }, { isCleanup := true, stmts := [], term := WireTerm.unwindTerminate 2 }, { isCleanup := false, stmts := [], term := WireTerm.drop { localIdx := 4, proj := ProjChain.here } 7 11 (UnwindSpec.cleanup 13) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 16, WireStmt.storageDead 15, WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } (OperandSpec.copy { localIdx := 13, proj := ProjChain.here }), WireStmt.storageDead 13, WireStmt.assignUseRetagYes { localIdx := 19, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.storageDead 6], term := WireTerm.switchInt1 (OperandSpec.copy { localIdx := 18, proj := ProjChain.here }) 0 15 14 }, { isCleanup := true, stmts := [], term := WireTerm.unwindTerminate 2 }, { isCleanup := false, stmts := [], term := WireTerm.drop { localIdx := 4, proj := ProjChain.here } 7 15 (UnwindSpec.cleanup 11) }, { isCleanup := false, stmts := [WireStmt.assignUseRetagYes { localIdx := 18, proj := ProjChain.here } (OperandSpec.constBool false), WireStmt.storageDead 4], term := WireTerm.ret }]
def body_C_65_5 : WireBody := { bodyId := 6, symId := 65, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 20, argCount := 3, localTypes := [MirTypeTag.u32, MirTypeTag.refMutEffectLog, MirTypeTag.refMutEffectLog, MirTypeTag.bool, MirTypeTag.guard, MirTypeTag.refMutEffectLog, MirTypeTag.guard, MirTypeTag.refMutEffectLog, MirTypeTag.bool, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.unit, MirTypeTag.guard, MirTypeTag.u32, MirTypeTag.bool, MirTypeTag.unit, MirTypeTag.guard, MirTypeTag.refMutEffectLog, MirTypeTag.bool, MirTypeTag.bool], blocks := blocks_C_65_5 }
def blocks_C_7_6 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 2, WireStmt.storageLive 3, WireStmt.assignUseNoRetag { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit), WireStmt.assignRefOrPtr { localIdx := 2, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }], term := WireTerm.call1 2 { localIdx := 3, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 2, proj := ProjChain.here }) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [], term := WireTerm.ret }]
def body_C_7_6 : WireBody := { bodyId := 7, symId := 7, originKind := BodyOriginKind.compilerShim, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 4, argCount := 1, localTypes := [MirTypeTag.unit, MirTypeTag.refGuard, MirTypeTag.refGuard, MirTypeTag.unit], blocks := blocks_C_7_6 }
def blocks_C_24_7 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.assignUseNoRetag { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit)], term := WireTerm.drop { localIdx := 1, proj := ProjChain.here } 7 2 (UnwindSpec.cleanup 1) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [], term := WireTerm.ret }]
def body_C_24_7 : WireBody := { bodyId := 8, symId := 24, originKind := BodyOriginKind.externalOptimized, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 2, argCount := 1, localTypes := [MirTypeTag.unit, MirTypeTag.guard], blocks := blocks_C_24_7 }
def blocks_C_37_8 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUsize 4)], term := WireTerm.ret }]
def body_C_37_8 : WireBody := { bodyId := 98, symId := 37, originKind := BodyOriginKind.externalOptimized, mirPhase := MirPhaseTag.runtimeOptimized, localCount := 1, argCount := 0, localTypes := [MirTypeTag.usize], blocks := blocks_C_37_8 }
def blocks_C_38_9 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUsize 4)], term := WireTerm.ret }]
def body_C_38_9 : WireBody := { bodyId := 99, symId := 38, originKind := BodyOriginKind.externalOptimized, mirPhase := MirPhaseTag.runtimeOptimized, localCount := 1, argCount := 0, localTypes := [MirTypeTag.usize], blocks := blocks_C_38_9 }
def charonStatefulGenericLibBodiesVal : List WireBody := [body_C_1_0, body_C_2_1, body_C_3_2, body_C_63_3, body_C_64_4, body_C_65_5, body_C_7_6, body_C_24_7, body_C_37_8, body_C_38_9]
def blocks_CC_66_0 : List WireBlock := [{ isCleanup := false, stmts := [WireStmt.storageLive 4, WireStmt.storageLive 5, WireStmt.assignRefOrPtr { localIdx := 5, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }, WireStmt.storageLive 6, WireStmt.assignUseRetagYes { localIdx := 6, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here }), WireStmt.storageLive 7, WireStmt.assignUseRetagYes { localIdx := 7, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here })], term := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 7, WireStmt.storageDead 6, WireStmt.storageDead 5, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 4, proj := ProjChain.here })], term := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 4) (UnwindSpec.cleanup 3) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) (OperandSpec.constUsize 8) }, { isCleanup := true, stmts := [], term := WireTerm.unwindResume }, { isCleanup := false, stmts := [WireStmt.storageDead 8, WireStmt.storageDead 4], term := WireTerm.ret }]
def body_CC_66_0 : WireBody := { bodyId := 1, symId := 66, originKind := BodyOriginKind.localOwner, mirPhase := MirPhaseTag.runtimePostCleanup, localCount := 9, argCount := 3, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], blocks := blocks_CC_66_0 }
def charonClientContractUserBodiesVal : List WireBody := [body_CC_66_0]
def linkedDirectBodiesVal : List WireBody := clientContractUserBodiesVal ++ statefulGenericLibBodiesVal
def linkedCharonBodiesVal : List WireBody := charonClientContractUserBodiesVal ++ charonStatefulGenericLibBodiesVal

theorem runSteps_split (bodies : List WireBody) (m n : Nat) (st : ExecState) :
    runSteps bodies (m + n) st = runSteps bodies n (runSteps bodies m st) := by
  induction m generalizing st with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ m ih =>
      have h1 : m + 1 + n = (m + n) + 1 := Nat.add_right_comm m 1 n
      rw [h1, runSteps_succ, runSteps_succ]
      cases hst : st.status
      · exact ih (stepState bodies st)
      all_goals
        symm
        apply runSteps_nonRunning
        rw [hst]
        intro h; contradiction

theorem statefulGenericLibBodies_eq : statefulGenericLibBodies = statefulGenericLibBodiesVal := by decide
theorem clientContractUserBodies_eq : clientContractUserBodies = clientContractUserBodiesVal := by decide
theorem charonStatefulGenericLibBodies_eq : charonStatefulGenericLibBodies = charonStatefulGenericLibBodiesVal := by decide
theorem charonClientContractUserBodies_eq : charonClientContractUserBodies = charonClientContractUserBodiesVal := by decide
theorem linkedDirectBodies_eq :
    clientContractUserBodies ++ statefulGenericLibBodies = linkedDirectBodiesVal := by
  rw [clientContractUserBodies_eq, statefulGenericLibBodies_eq]
  rfl
theorem linkedCharonBodies_eq :
    charonClientContractUserBodies ++ charonStatefulGenericLibBodies = linkedCharonBodiesVal := by
  rw [charonClientContractUserBodies_eq, charonStatefulGenericLibBodies_eq]
  rfl

noncomputable def st_DLIB_3 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 1, localTypes := [MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32], bodyBlocks := blocks_D_1_0, bbIdx := 0, remStmts := [WireStmt.storageLive 3, WireStmt.storageLive 4, WireStmt.assignUseRetagYes { localIdx := 4, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField0 })], curTerm := WireTerm.call2 20 { localIdx := 3, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) (OperandSpec.constU32 1), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.scalar 4)], pending := none }, { symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_D_63_3, bbIdx := 1, remStmts := [], curTerm := WireTerm.call2 1 { localIdx := 6, proj := ProjChain.here } (some 2) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.constU32 4), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.scalar 4), (7, RtVal.heapPtr 0)], pending := some { retDst := { localIdx := 6, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.continueUnwind, isDropGlue := false } }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [4] }
theorem step_DLIB_0_3 (base : Nat) :
    runSteps statefulGenericLibBodiesVal 3 (initEntryStateWithHeap statefulGenericLibBodiesVal 63 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_DLIB_3 base := rfl
noncomputable def st_DLIB_6 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 1, localTypes := [MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32], bodyBlocks := blocks_D_1_0, bbIdx := 3, remStmts := [WireStmt.storageDead 8, WireStmt.storageDead 6, WireStmt.assignUseRetagYes { localIdx := 1, proj := ProjChain.derefField1 } (OperandSpec.move { localIdx := 5, proj := ProjChain.here }), WireStmt.storageDead 5, WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit)], curTerm := WireTerm.ret, locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.scalar 4), (5, RtVal.scalar 4), (6, RtVal.scalar 0), (8, RtVal.scalar 4)], pending := none }, { symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_D_63_3, bbIdx := 1, remStmts := [], curTerm := WireTerm.call2 1 { localIdx := 6, proj := ProjChain.here } (some 2) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.constU32 4), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.scalar 4), (7, RtVal.heapPtr 0)], pending := some { retDst := { localIdx := 6, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.continueUnwind, isDropGlue := false } }], heap := [{ stepCount := 1, traceAcc := 0 }], obsEvents := [4] }
theorem step_DLIB_3_6 (base : Nat) :
    runSteps statefulGenericLibBodiesVal 3 (st_DLIB_3 base) = st_DLIB_6 base := rfl
noncomputable def st_DLIB_7 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_D_63_3, bbIdx := 2, remStmts := [WireStmt.storageDead 7, WireStmt.storageDead 6, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here }), WireStmt.storageLive 9, WireStmt.assignUseRetagYes { localIdx := 9, proj := ProjChain.here } (OperandSpec.copy { localIdx := 5, proj := ProjChain.here })], curTerm := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 3) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) (OperandSpec.move { localIdx := 9, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.scalar 4), (6, RtVal.agg0 1), (7, RtVal.heapPtr 0)], pending := none }], heap := [{ stepCount := 1, traceAcc := 4 }], obsEvents := [4] }
theorem step_DLIB_6_7 (base : Nat) :
    runSteps statefulGenericLibBodiesVal 1 (st_DLIB_6 base) = st_DLIB_7 base := rfl
noncomputable def st_DLIB_9 (base : Nat) : ExecState := { status := ExecStatus.returned (RtVal.scalar ((base + 4) % usizeMod)), stack := [], heap := [{ stepCount := 1, traceAcc := 4 }], obsEvents := [4] }
theorem step_DLIB_7_9 (base : Nat) :
    runSteps statefulGenericLibBodiesVal 2 (st_DLIB_7 base) = st_DLIB_9 base := rfl
theorem step_DLIB_9_12 (base : Nat) :
    runSteps statefulGenericLibBodiesVal 3 (st_DLIB_9 base) = st_DLIB_9 base := rfl
theorem runSteps_DLIB_full (base : Nat) :
    runSteps statefulGenericLibBodiesVal 12 (initEntryStateWithHeap statefulGenericLibBodiesVal 63 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_DLIB_9 base := by
  have hTot : (12 : Nat) = ((((3 + 3) + 1) + 2) + 3) := rfl
  rw [hTot, runSteps_split, runSteps_split, runSteps_split, runSteps_split, step_DLIB_0_3, step_DLIB_3_6, step_DLIB_6_7, step_DLIB_7_9, step_DLIB_9_12]
noncomputable def st_DLINK_3 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_D_63_3, bbIdx := 1, remStmts := [WireStmt.storageLive 6, WireStmt.storageLive 7, WireStmt.assignRefOrPtr { localIdx := 7, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }], curTerm := WireTerm.call2 1 { localIdx := 6, proj := ProjChain.here } (some 2) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.constU32 4), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.scalar 4)], pending := none }, { symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_DC_66_0, bbIdx := 0, remStmts := [], curTerm := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.heapPtr 0), (6, RtVal.extPtr true), (7, RtVal.scalar base)], pending := some { retDst := { localIdx := 4, proj := ProjChain.here }, targetBbOpt := some 1, unwind := UnwindSpec.continueUnwind, isDropGlue := false } }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }
theorem step_DLINK_0_3 (base : Nat) :
    runSteps linkedDirectBodiesVal 3 (initEntryStateWithHeap linkedDirectBodiesVal 66 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_DLINK_3 base := rfl
noncomputable def st_DLINK_6 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 1, localTypes := [MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32], bodyBlocks := blocks_D_1_0, bbIdx := 2, remStmts := [WireStmt.storageDead 7, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here })], curTerm := WireTerm.call2 20 { localIdx := 5, proj := ProjChain.here } (some 3) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.scalar 4), (6, RtVal.scalar 0), (7, RtVal.scalar 0)], pending := none }, { symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_D_63_3, bbIdx := 1, remStmts := [], curTerm := WireTerm.call2 1 { localIdx := 6, proj := ProjChain.here } (some 2) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.constU32 4), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.scalar 4), (7, RtVal.heapPtr 0)], pending := some { retDst := { localIdx := 6, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.continueUnwind, isDropGlue := false } }, { symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_DC_66_0, bbIdx := 0, remStmts := [], curTerm := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.heapPtr 0), (6, RtVal.extPtr true), (7, RtVal.scalar base)], pending := some { retDst := { localIdx := 4, proj := ProjChain.here }, targetBbOpt := some 1, unwind := UnwindSpec.continueUnwind, isDropGlue := false } }], heap := [{ stepCount := 1, traceAcc := 0 }], obsEvents := [4] }
theorem step_DLINK_3_6 (base : Nat) :
    runSteps linkedDirectBodiesVal 3 (st_DLINK_3 base) = st_DLINK_6 base := rfl
noncomputable def st_DLINK_8 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_D_63_3, bbIdx := 2, remStmts := [WireStmt.storageDead 7, WireStmt.storageDead 6, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here }), WireStmt.storageLive 9, WireStmt.assignUseRetagYes { localIdx := 9, proj := ProjChain.here } (OperandSpec.copy { localIdx := 5, proj := ProjChain.here })], curTerm := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 3) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) (OperandSpec.move { localIdx := 9, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.scalar 4), (6, RtVal.agg0 1), (7, RtVal.heapPtr 0)], pending := none }, { symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_DC_66_0, bbIdx := 0, remStmts := [], curTerm := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.heapPtr 0), (6, RtVal.extPtr true), (7, RtVal.scalar base)], pending := some { retDst := { localIdx := 4, proj := ProjChain.here }, targetBbOpt := some 1, unwind := UnwindSpec.continueUnwind, isDropGlue := false } }], heap := [{ stepCount := 1, traceAcc := 4 }], obsEvents := [4] }
theorem step_DLINK_6_8 (base : Nat) :
    runSteps linkedDirectBodiesVal 2 (st_DLINK_6 base) = st_DLINK_8 base := rfl
noncomputable def st_DLINK_10 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_DC_66_0, bbIdx := 1, remStmts := [WireStmt.storageDead 7, WireStmt.storageDead 6, WireStmt.storageDead 5, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 4, proj := ProjChain.here })], curTerm := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 2) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) (OperandSpec.constUsize 8), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (4, RtVal.scalar ((base + 4) % usizeMod)), (5, RtVal.heapPtr 0), (6, RtVal.extPtr true), (7, RtVal.scalar base)], pending := none }], heap := [{ stepCount := 1, traceAcc := 4 }], obsEvents := [4] }
theorem step_DLINK_8_10 (base : Nat) :
    runSteps linkedDirectBodiesVal 2 (st_DLINK_8 base) = st_DLINK_10 base := rfl
noncomputable def st_DLINK_12 (base : Nat) : ExecState := { status := ExecStatus.returned (RtVal.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), stack := [], heap := [{ stepCount := 1, traceAcc := 4 }], obsEvents := [4] }
theorem step_DLINK_10_12 (base : Nat) :
    runSteps linkedDirectBodiesVal 2 (st_DLINK_10 base) = st_DLINK_12 base := rfl
theorem step_DLINK_12_16 (base : Nat) :
    runSteps linkedDirectBodiesVal 4 (st_DLINK_12 base) = st_DLINK_12 base := rfl
theorem runSteps_DLINK_full (base : Nat) :
    runSteps linkedDirectBodiesVal 16 (initEntryStateWithHeap linkedDirectBodiesVal 66 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_DLINK_12 base := by
  have hTot : (16 : Nat) = (((((3 + 3) + 2) + 2) + 2) + 4) := rfl
  rw [hTot, runSteps_split, runSteps_split, runSteps_split, runSteps_split, runSteps_split, step_DLINK_0_3, step_DLINK_3_6, step_DLINK_6_8, step_DLINK_8_10, step_DLINK_10_12, step_DLINK_12_16]
noncomputable def st_DLINK_F_2 (base : Nat) : ExecState := { status := ExecStatus.ub, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_D_63_3, bbIdx := 0, remStmts := [], curTerm := WireTerm.call0 38 { localIdx := 5, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr false), (3, RtVal.scalar base)], pending := none }, { symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_DC_66_0, bbIdx := 0, remStmts := [], curTerm := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 1) (UnwindSpec.continueUnwind) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr false), (3, RtVal.scalar base), (5, RtVal.heapPtr 0), (6, RtVal.extPtr false), (7, RtVal.scalar base)], pending := some { retDst := { localIdx := 4, proj := ProjChain.here }, targetBbOpt := some 1, unwind := UnwindSpec.continueUnwind, isDropGlue := false } }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }
theorem step_DLINK_F_0_2 (base : Nat) :
    runSteps linkedDirectBodiesVal 2 (initEntryStateWithHeap linkedDirectBodiesVal 66 [.heapPtr 0, .extPtr false, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_DLINK_F_2 base := rfl
theorem step_DLINK_F_2_16 (base : Nat) :
    runSteps linkedDirectBodiesVal 14 (st_DLINK_F_2 base) = st_DLINK_F_2 base := rfl
theorem runSteps_DLINK_F_full (base : Nat) :
    runSteps linkedDirectBodiesVal 16 (initEntryStateWithHeap linkedDirectBodiesVal 66 [.heapPtr 0, .extPtr false, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_DLINK_F_2 base := by
  have hTot : (16 : Nat) = (2 + 14) := rfl
  rw [hTot, runSteps_split, step_DLINK_F_0_2, step_DLINK_F_2_16]
noncomputable def st_CLIB_3 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 9, remStmts := [WireStmt.storageDead 10, WireStmt.storageDead 9, WireStmt.placeMention { localIdx := 2, proj := ProjChain.deref }, WireStmt.storageLive 4], curTerm := WireTerm.call0 38 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (9, RtVal.scalar 1), (10, RtVal.scalar 4)], pending := none }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }
theorem step_CLIB_0_3 (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 3 (initEntryStateWithHeap charonStatefulGenericLibBodiesVal 63 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_CLIB_3 base := rfl
noncomputable def st_CLIB_6 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 1, localTypes := [MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32], bodyBlocks := blocks_C_1_0, bbIdx := 0, remStmts := [WireStmt.assignUseNoRetag { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit), WireStmt.storageLive 3, WireStmt.storageLive 4, WireStmt.assignUseRetagYes { localIdx := 4, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField0 })], curTerm := WireTerm.call2 20 { localIdx := 3, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) (OperandSpec.constU32 1), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.scalar 4)], pending := none }, { symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 2, remStmts := [], curTerm := WireTerm.call2 1 { localIdx := 5, proj := ProjChain.here } (some 4) (UnwindSpec.cleanup 3) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.constU32 4), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (4, RtVal.scalar 4), (6, RtVal.heapPtr 0)], pending := some { retDst := { localIdx := 5, proj := ProjChain.here }, targetBbOpt := some 4, unwind := UnwindSpec.cleanup 3, isDropGlue := false } }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [4] }
theorem step_CLIB_3_6 (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 3 (st_CLIB_3 base) = st_CLIB_6 base := rfl
noncomputable def st_CLIB_9 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 1, localTypes := [MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32], bodyBlocks := blocks_C_1_0, bbIdx := 6, remStmts := [WireStmt.storageDead 8, WireStmt.storageDead 6, WireStmt.assignUseRetagYes { localIdx := 1, proj := ProjChain.derefField1 } (OperandSpec.move { localIdx := 5, proj := ProjChain.here }), WireStmt.storageDead 5, WireStmt.assignUseNoRetag { localIdx := 0, proj := ProjChain.here } (OperandSpec.constUnit)], curTerm := WireTerm.ret, locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.scalar 4), (5, RtVal.scalar 4), (6, RtVal.scalar 0), (8, RtVal.scalar 4)], pending := none }, { symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 2, remStmts := [], curTerm := WireTerm.call2 1 { localIdx := 5, proj := ProjChain.here } (some 4) (UnwindSpec.cleanup 3) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.constU32 4), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (4, RtVal.scalar 4), (6, RtVal.heapPtr 0)], pending := some { retDst := { localIdx := 5, proj := ProjChain.here }, targetBbOpt := some 4, unwind := UnwindSpec.cleanup 3, isDropGlue := false } }], heap := [{ stepCount := 1, traceAcc := 0 }], obsEvents := [4] }
theorem step_CLIB_6_9 (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 3 (st_CLIB_6 base) = st_CLIB_9 base := rfl
noncomputable def st_CLIB_10 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 4, remStmts := [WireStmt.storageDead 6, WireStmt.storageDead 5, WireStmt.storageLive 7, WireStmt.assignUseRetagYes { localIdx := 7, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here }), WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 4, proj := ProjChain.here })], curTerm := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 6) (UnwindSpec.cleanup 5) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (4, RtVal.scalar 4), (5, RtVal.agg0 1), (6, RtVal.heapPtr 0)], pending := none }], heap := [{ stepCount := 1, traceAcc := 4 }], obsEvents := [4] }
theorem step_CLIB_9_10 (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 1 (st_CLIB_9 base) = st_CLIB_10 base := rfl
noncomputable def st_CLIB_12 (base : Nat) : ExecState := { status := ExecStatus.returned (RtVal.scalar ((base + 4) % usizeMod)), stack := [], heap := [{ stepCount := 1, traceAcc := 4 }], obsEvents := [4] }
theorem step_CLIB_10_12 (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 2 (st_CLIB_10 base) = st_CLIB_12 base := rfl
theorem step_CLIB_12_16 (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 4 (st_CLIB_12 base) = st_CLIB_12 base := rfl
theorem runSteps_CLIB_full (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 16 (initEntryStateWithHeap charonStatefulGenericLibBodiesVal 63 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_CLIB_12 base := by
  have hTot : (16 : Nat) = (((((3 + 3) + 3) + 1) + 2) + 4) := rfl
  rw [hTot, runSteps_split, runSteps_split, runSteps_split, runSteps_split, runSteps_split, step_CLIB_0_3, step_CLIB_3_6, step_CLIB_6_9, step_CLIB_9_10, step_CLIB_10_12, step_CLIB_12_16]
noncomputable def st_CLIB_F_2 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 8, remStmts := [WireStmt.assignBinOp { localIdx := 9, proj := ProjChain.here } (BinOpTag.gt) (OperandSpec.move { localIdx := 10, proj := ProjChain.here }) (OperandSpec.constUsize 0)], curTerm := WireTerm.switchInt1 (OperandSpec.move { localIdx := 9, proj := ProjChain.here }) 0 10 9, locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr false), (3, RtVal.scalar base), (10, RtVal.scalar 4)], pending := none }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }
theorem step_CLIB_F_0_2 (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 2 (initEntryStateWithHeap charonStatefulGenericLibBodiesVal 63 [.heapPtr 0, .extPtr false, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_CLIB_F_2 base := rfl
noncomputable def st_CLIB_F_4 (base : Nat) : ExecState := { status := ExecStatus.ub, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 9, remStmts := [], curTerm := WireTerm.call0 38 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr false), (3, RtVal.scalar base)], pending := none }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }
theorem step_CLIB_F_2_4 (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 2 (st_CLIB_F_2 base) = st_CLIB_F_4 base := rfl
theorem step_CLIB_F_4_16 (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 12 (st_CLIB_F_4 base) = st_CLIB_F_4 base := rfl
theorem runSteps_CLIB_F_full (base : Nat) :
    runSteps charonStatefulGenericLibBodiesVal 16 (initEntryStateWithHeap charonStatefulGenericLibBodiesVal 63 [.heapPtr 0, .extPtr false, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_CLIB_F_4 base := by
  have hTot : (16 : Nat) = ((2 + 2) + 12) := rfl
  rw [hTot, runSteps_split, runSteps_split, step_CLIB_F_0_2, step_CLIB_F_2_4, step_CLIB_F_4_16]
noncomputable def st_CLINK_3 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 8, remStmts := [WireStmt.assignBinOp { localIdx := 9, proj := ProjChain.here } (BinOpTag.gt) (OperandSpec.move { localIdx := 10, proj := ProjChain.here }) (OperandSpec.constUsize 0)], curTerm := WireTerm.switchInt1 (OperandSpec.move { localIdx := 9, proj := ProjChain.here }) 0 10 9, locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (10, RtVal.scalar 4)], pending := none }, { symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_CC_66_0, bbIdx := 0, remStmts := [], curTerm := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.heapPtr 0), (6, RtVal.extPtr true), (7, RtVal.scalar base)], pending := some { retDst := { localIdx := 4, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.cleanup 1, isDropGlue := false } }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }
theorem step_CLINK_0_3 (base : Nat) :
    runSteps linkedCharonBodiesVal 3 (initEntryStateWithHeap linkedCharonBodiesVal 66 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_CLINK_3 base := rfl
noncomputable def st_CLINK_6 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 2, remStmts := [WireStmt.storageLive 5, WireStmt.storageLive 6, WireStmt.assignRefOrPtr { localIdx := 6, proj := ProjChain.here } (RefPtrKind.mutRef) { localIdx := 1, proj := ProjChain.deref }], curTerm := WireTerm.call2 1 { localIdx := 5, proj := ProjChain.here } (some 4) (UnwindSpec.cleanup 3) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.constU32 4), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (4, RtVal.scalar 4)], pending := none }, { symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_CC_66_0, bbIdx := 0, remStmts := [], curTerm := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.heapPtr 0), (6, RtVal.extPtr true), (7, RtVal.scalar base)], pending := some { retDst := { localIdx := 4, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.cleanup 1, isDropGlue := false } }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }
theorem step_CLINK_3_6 (base : Nat) :
    runSteps linkedCharonBodiesVal 3 (st_CLINK_3 base) = st_CLINK_6 base := rfl
noncomputable def st_CLINK_9 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 1, localTypes := [MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32], bodyBlocks := blocks_C_1_0, bbIdx := 4, remStmts := [WireStmt.storageDead 7, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here })], curTerm := WireTerm.call2 20 { localIdx := 5, proj := ProjChain.here } (some 6) (UnwindSpec.cleanup 5) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.scalar 4), (6, RtVal.scalar 0), (7, RtVal.scalar 0)], pending := none }, { symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 2, remStmts := [], curTerm := WireTerm.call2 1 { localIdx := 5, proj := ProjChain.here } (some 4) (UnwindSpec.cleanup 3) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.constU32 4), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (4, RtVal.scalar 4), (6, RtVal.heapPtr 0)], pending := some { retDst := { localIdx := 5, proj := ProjChain.here }, targetBbOpt := some 4, unwind := UnwindSpec.cleanup 3, isDropGlue := false } }, { symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_CC_66_0, bbIdx := 0, remStmts := [], curTerm := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.heapPtr 0), (6, RtVal.extPtr true), (7, RtVal.scalar base)], pending := some { retDst := { localIdx := 4, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.cleanup 1, isDropGlue := false } }], heap := [{ stepCount := 1, traceAcc := 0 }], obsEvents := [4] }
theorem step_CLINK_6_9 (base : Nat) :
    runSteps linkedCharonBodiesVal 3 (st_CLINK_6 base) = st_CLINK_9 base := rfl
noncomputable def st_CLINK_11 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 4, remStmts := [WireStmt.storageDead 6, WireStmt.storageDead 5, WireStmt.storageLive 7, WireStmt.assignUseRetagYes { localIdx := 7, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here }), WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 4, proj := ProjChain.here })], curTerm := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 6) (UnwindSpec.cleanup 5) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (4, RtVal.scalar 4), (5, RtVal.agg0 1), (6, RtVal.heapPtr 0)], pending := none }, { symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_CC_66_0, bbIdx := 0, remStmts := [], curTerm := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.heapPtr 0), (6, RtVal.extPtr true), (7, RtVal.scalar base)], pending := some { retDst := { localIdx := 4, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.cleanup 1, isDropGlue := false } }], heap := [{ stepCount := 1, traceAcc := 4 }], obsEvents := [4] }
theorem step_CLINK_9_11 (base : Nat) :
    runSteps linkedCharonBodiesVal 2 (st_CLINK_9 base) = st_CLINK_11 base := rfl
noncomputable def st_CLINK_13 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_CC_66_0, bbIdx := 2, remStmts := [WireStmt.storageDead 7, WireStmt.storageDead 6, WireStmt.storageDead 5, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 4, proj := ProjChain.here })], curTerm := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 4) (UnwindSpec.cleanup 3) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) (OperandSpec.constUsize 8), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (4, RtVal.scalar ((base + 4) % usizeMod)), (5, RtVal.heapPtr 0), (6, RtVal.extPtr true), (7, RtVal.scalar base)], pending := none }], heap := [{ stepCount := 1, traceAcc := 4 }], obsEvents := [4] }
theorem step_CLINK_11_13 (base : Nat) :
    runSteps linkedCharonBodiesVal 2 (st_CLINK_11 base) = st_CLINK_13 base := rfl
noncomputable def st_CLINK_15 (base : Nat) : ExecState := { status := ExecStatus.returned (RtVal.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), stack := [], heap := [{ stepCount := 1, traceAcc := 4 }], obsEvents := [4] }
theorem step_CLINK_13_15 (base : Nat) :
    runSteps linkedCharonBodiesVal 2 (st_CLINK_13 base) = st_CLINK_15 base := rfl
theorem step_CLINK_15_22 (base : Nat) :
    runSteps linkedCharonBodiesVal 7 (st_CLINK_15 base) = st_CLINK_15 base := rfl
theorem runSteps_CLINK_full (base : Nat) :
    runSteps linkedCharonBodiesVal 22 (initEntryStateWithHeap linkedCharonBodiesVal 66 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_CLINK_15 base := by
  have hTot : (22 : Nat) = ((((((3 + 3) + 3) + 2) + 2) + 2) + 7) := rfl
  rw [hTot, runSteps_split, runSteps_split, runSteps_split, runSteps_split, runSteps_split, runSteps_split, step_CLINK_0_3, step_CLINK_3_6, step_CLINK_6_9, step_CLINK_9_11, step_CLINK_11_13, step_CLINK_13_15, step_CLINK_15_22]
noncomputable def st_CLINK_F_3 (base : Nat) : ExecState := { status := ExecStatus.running, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 8, remStmts := [WireStmt.assignBinOp { localIdx := 9, proj := ProjChain.here } (BinOpTag.gt) (OperandSpec.move { localIdx := 10, proj := ProjChain.here }) (OperandSpec.constUsize 0)], curTerm := WireTerm.switchInt1 (OperandSpec.move { localIdx := 9, proj := ProjChain.here }) 0 10 9, locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr false), (3, RtVal.scalar base), (10, RtVal.scalar 4)], pending := none }, { symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_CC_66_0, bbIdx := 0, remStmts := [], curTerm := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr false), (3, RtVal.scalar base), (5, RtVal.heapPtr 0), (6, RtVal.extPtr false), (7, RtVal.scalar base)], pending := some { retDst := { localIdx := 4, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.cleanup 1, isDropGlue := false } }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }
theorem step_CLINK_F_0_3 (base : Nat) :
    runSteps linkedCharonBodiesVal 3 (initEntryStateWithHeap linkedCharonBodiesVal 66 [.heapPtr 0, .extPtr false, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_CLINK_F_3 base := rfl
noncomputable def st_CLINK_F_5 (base : Nat) : ExecState := { status := ExecStatus.ub, stack := [{ symId := 63, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.bool, MirTypeTag.usize, MirTypeTag.panicOrNever], bodyBlocks := blocks_C_63_3, bbIdx := 9, remStmts := [], curTerm := WireTerm.call0 38 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr false), (3, RtVal.scalar base)], pending := none }, { symId := 66, localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.usize], bodyBlocks := blocks_CC_66_0, bbIdx := 0, remStmts := [], curTerm := WireTerm.call3 63 { localIdx := 4, proj := ProjChain.here } (some 2) (UnwindSpec.cleanup 1) (OperandSpec.move { localIdx := 5, proj := ProjChain.here }) (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 7, proj := ProjChain.here }), locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr false), (3, RtVal.scalar base), (5, RtVal.heapPtr 0), (6, RtVal.extPtr false), (7, RtVal.scalar base)], pending := some { retDst := { localIdx := 4, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.cleanup 1, isDropGlue := false } }], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }
theorem step_CLINK_F_3_5 (base : Nat) :
    runSteps linkedCharonBodiesVal 2 (st_CLINK_F_3 base) = st_CLINK_F_5 base := rfl
theorem step_CLINK_F_5_22 (base : Nat) :
    runSteps linkedCharonBodiesVal 17 (st_CLINK_F_5 base) = st_CLINK_F_5 base := rfl
theorem runSteps_CLINK_F_full (base : Nat) :
    runSteps linkedCharonBodiesVal 22 (initEntryStateWithHeap linkedCharonBodiesVal 66 [.heapPtr 0, .extPtr false, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_CLINK_F_5 base := by
  have hTot : (22 : Nat) = ((3 + 2) + 17) := rfl
  rw [hTot, runSteps_split, runSteps_split, step_CLINK_F_0_3, step_CLINK_F_3_5, step_CLINK_F_5_22]

theorem evalStepGenericSlot_false_universal (base : Nat) :
    evalStepGenericSlotWithFuel statefulGenericLibBodies 12 0 0 false base =
      (.ub, { stepCount := 0, traceAcc := 0 }, []) := by
  dsimp only [evalStepGenericSlotWithFuel]
  rw [statefulGenericLibBodies_eq]
  rfl

theorem evalStepGenericSlot_true_universal (base : Nat) :
    evalStepGenericSlotWithFuel statefulGenericLibBodies 12 0 0 true base =
      (.returned (.scalar ((base + 4) % usizeMod)), { stepCount := 1, traceAcc := 4 }, [4]) := by
  dsimp only [evalStepGenericSlotWithFuel]
  rw [statefulGenericLibBodies_eq, runSteps_DLIB_full]
  rfl

theorem evalCharonStepGenericSlot_false_universal (base : Nat) :
    evalStepGenericSlotWithFuel charonStatefulGenericLibBodies 16 0 0 false base =
      (.ub, { stepCount := 0, traceAcc := 0 }, []) := by
  dsimp only [evalStepGenericSlotWithFuel]
  rw [charonStatefulGenericLibBodies_eq, runSteps_CLIB_F_full]
  rfl

theorem evalCharonStepGenericSlot_true_universal (base : Nat) :
    evalStepGenericSlotWithFuel charonStatefulGenericLibBodies 16 0 0 true base =
      (.returned (.scalar ((base + 4) % usizeMod)), { stepCount := 1, traceAcc := 4 }, [4]) := by
  dsimp only [evalStepGenericSlotWithFuel]
  rw [charonStatefulGenericLibBodies_eq, runSteps_CLIB_full]
  rfl

theorem evalDecodedStepGenericSlotSymbolic_false_universal (base : Nat) :
    evalDecodedStepGenericSlotSymbolic statefulGenericLibBodies false base =
      some (.ub, { stepCount := 0, traceAcc := 0 }, []) := by
  rw [statefulGenericLibBodies_eq]
  rfl

theorem evalDecodedStepGenericSlotSymbolic_true_universal (base : Nat) :
    evalDecodedStepGenericSlotSymbolic statefulGenericLibBodies true base =
      some (.returned (.scalar ((base + 4) % usizeMod)), { stepCount := 1, traceAcc := 4 }, [4]) := by
  rw [statefulGenericLibBodies_eq]
  rfl

theorem step_generic_slot_symbolic_summary_matches_runSteps_universal
    (ptrValid : Bool) (base : Nat) :
    evalDecodedStepGenericSlotSymbolic statefulGenericLibBodies ptrValid base =
      some (evalStepGenericSlot statefulGenericLibBodies 0 0 ptrValid base) := by
  unfold evalStepGenericSlot
  cases ptrValid
  · rw [evalDecodedStepGenericSlotSymbolic_false_universal, evalStepGenericSlot_false_universal]
  · rw [evalDecodedStepGenericSlotSymbolic_true_universal, evalStepGenericSlot_true_universal]

/-- Retained 4-input corollary for backward compatibility. -/
theorem step_generic_slot_stack_machine_agrees_with_symbolic_decoded_eval :
    evalDecodedStepGenericSlotSymbolic statefulGenericLibBodies false 16 =
      some (evalStepGenericSlot statefulGenericLibBodies 0 0 false 16) ∧
    evalDecodedStepGenericSlotSymbolic statefulGenericLibBodies true 0 =
      some (evalStepGenericSlot statefulGenericLibBodies 0 0 true 0) ∧
    evalDecodedStepGenericSlotSymbolic statefulGenericLibBodies true 16 =
      some (evalStepGenericSlot statefulGenericLibBodies 0 0 true 16) ∧
    evalDecodedStepGenericSlotSymbolic statefulGenericLibBodies true 255 =
      some (evalStepGenericSlot statefulGenericLibBodies 0 0 true 255) := by
  decide

/-- **Published Operational Library Contract (`PublishedStatefulLibContractOperational`, `N1`, `LIB-01`/`LIB-02`)**:
    Stated **directly over `evalStepGenericSlotWithFuel` (`SemanticVerticalSliceCore.runSteps`)**:
    1. On `ptrValid = false`, for **all** `base : Nat`, `step_generic_slot::<u32>` fails closed with `.ub`.
    2. On `ptrValid = true`, for **all** `base : Nat`, `step_generic_slot::<u32>` returns
       `.returned (.scalar ((base + 4) % usizeMod))` and sets `log.stepCount = 1`, while existentially
       abstracting the private `traceAcc` (`t1`) and `obsEvents` (`evs`)! -/
def PublishedStatefulLibContractOperational (libBodies : List WireBody) (fuel : Nat) : Prop :=
  (∀ base : Nat,
    evalStepGenericSlotWithFuel libBodies fuel 0 0 false base =
      (.ub, { stepCount := 0, traceAcc := 0 }, [])) ∧
  (∀ base : Nat,
    ∃ t1 : Nat, ∃ evs : List Nat,
      evalStepGenericSlotWithFuel libBodies fuel 0 0 true base =
        (.returned (.scalar ((base + 4) % usizeMod)), { stepCount := 1, traceAcc := t1 }, evs))

/-- Legacy alias over `evalDecodedStepGenericSlotSymbolic` preserved for historical cross-references. -/
def PublishedStatefulLibContract (libBodies : List WireBody) : Prop :=
  ∀ base : Nat,
    ∃ t1 : Nat, ∃ evs : List Nat,
      evalDecodedStepGenericSlotSymbolic libBodies true base =
        some (.returned (.scalar ((base + 4) % usizeMod)), { stepCount := 1, traceAcc := t1 }, evs)

/-- **Universal Operational Library Theorem (`N1`, `#68` §6 N1 Item 1)**:
    `statefulGenericLibBodies` satisfies `PublishedStatefulLibContractOperational` directly over
    `runSteps` (`fuel = 12`) for **all** `base : Nat`! -/
theorem stateful_generic_lib_satisfies_operational_contract :
    PublishedStatefulLibContractOperational statefulGenericLibBodies 12 := by
  refine ⟨evalStepGenericSlot_false_universal, fun base => ⟨4, [4], evalStepGenericSlot_true_universal base⟩⟩

theorem stateful_generic_lib_satisfies_published_contract :
    PublishedStatefulLibContract statefulGenericLibBodies := by
  intro base
  exact ⟨4, [4], evalDecodedStepGenericSlotSymbolic_true_universal base⟩

/-- **Operational Call-Contract Interpreter (`N1`, `#68` §6 N1 Item 2)**:
    Executes a client body (`client_contract_entry`, `symId = 66`) step-by-step using
    `execBlockStmts` and `stepTerm` from `SemanticVerticalSliceCore`, EXCEPT that when
    `fr.curTerm` is a 3-argument call to external library symbol `63` (`step_generic_slot`),
    it invokes the black-box operational callee oracle
    `calleeOracle : Bool → Nat → ExecStatus × HeapLogSlot × List Nat` on the evaluated
    operands `(ptrValid, base)` rather than unfolding `libBodies`! -/
def stepStateWithCallee63Oracle
    (clientBodies : List WireBody)
    (calleeOracle : Bool → Nat → ExecStatus × HeapLogSlot × List Nat)
    (st : ExecState) : ExecState :=
  match st.status with
  | .running =>
      match st.stack with
      | [] => { st with status := .stuck }
      | fr :: rest =>
          match execBlockStmts fr.localTypes fr.remStmts fr.locals st.heap with
          | (.running, nl, nh) =>
              let frAfterStmts := { fr with remStmts := [], locals := nl }
              match frAfterStmts.curTerm with
              | .call3 63 dst (some targetBb) uw a0 a1 a2 =>
                  match evalOperandList nl nh [a0, a1, a2] with
                  | some (some [.heapPtr 0, .extPtr pv, .scalar bVal]) =>
                      let (cStatus, nextSlot, cEvs) := calleeOracle pv bVal
                      match cStatus with
                      | .returned retVal =>
                          let nh1 := [nextSlot]
                          match writePlace nl nh1 dst retVal with
                          | some (nl2, nh2) =>
                              match jumpToBlock { frAfterStmts with locals := nl2 } targetBb with
                              | some nfr =>
                                  { status := .running
                                  , stack := nfr :: rest
                                  , heap := nh2
                                  , obsEvents := st.obsEvents ++ cEvs }
                              | none => { st with status := .stuck, heap := nh2 }
                          | none => { st with status := .stuck, heap := nh1 }
                      | .unwoundTop =>
                          handleCallUnwind frAfterStmts rest uw [nextSlot] (st.obsEvents ++ cEvs)
                      | otherStatus =>
                          { status := otherStatus
                          , stack := frAfterStmts :: rest
                          , heap := [nextSlot]
                          , obsEvents := st.obsEvents ++ cEvs }
                  | some none => { st with status := .ub, stack := frAfterStmts :: rest, heap := nh }
                  | _ => { st with status := .stuck, stack := frAfterStmts :: rest, heap := nh }
              | _ => stepTerm clientBodies frAfterStmts rest nh st.obsEvents
          | (otherStatus, nl, nh) =>
              { st with status := otherStatus, stack := { fr with remStmts := [], locals := nl } :: rest, heap := nh }
  | _ => st

def runStepsWithCallee63Oracle
    (clientBodies : List WireBody)
    (calleeOracle : Bool → Nat → ExecStatus × HeapLogSlot × List Nat) :
    Nat → ExecState → ExecState
  | 0, st => st
  | n + 1, st =>
      match st.status with
      | .running => runStepsWithCallee63Oracle clientBodies calleeOracle n
          (stepStateWithCallee63Oracle clientBodies calleeOracle st)
      | _ => st

def evalClientEntryOperationalWithCalleeOracle
    (clientBodies : List WireBody)
    (clientFuel : Nat)
    (calleeOracle : Bool → Nat → ExecStatus × HeapLogSlot × List Nat)
    (ptrValid : Bool)
    (base : Nat) : ExecStatus × Nat :=
  let initSt := initEntryStateWithHeap clientBodies 66
    [.heapPtr 0, .extPtr ptrValid, .scalar base]
    [{ stepCount := 0, traceAcc := 0 }]
  let st1 := stepStateWithCallee63Oracle clientBodies calleeOracle initSt
  let finalSt := runSteps clientBodies (clientFuel - 1) st1
  let stepCnt := match finalSt.heap with
    | h :: _ => h.stepCount
    | [] => 0
  (finalSt.status, stepCnt)

/-- Full linked stack-machine execution of `client_contract_entry` (`symId = 66`) on
    `clientBodies ++ libBodies` via `SemanticVerticalSliceCore.runSteps`. -/
def evalClientEntryLinkedOperational
    (linkedBodies : List WireBody)
    (fuel : Nat)
    (ptrValid : Bool)
    (base : Nat) : ExecStatus × Nat :=
  let initSt := initEntryStateWithHeap linkedBodies 66
    [.heapPtr 0, .extPtr ptrValid, .scalar base]
    [{ stepCount := 0, traceAcc := 0 }]
  let finalSt := runSteps linkedBodies fuel initSt
  let stepCnt := match finalSt.heap with
    | h :: _ => h.stepCount
    | [] => 0
  (finalSt.status, stepCnt)

/-- **Universal Modular Client Theorem Over Operational Semantics (`N1`, `#68` §6 N1 Item 2)**:
    For **any** library `libBodies` and `libFuel` satisfying `PublishedStatefulLibContractOperational libBodies libFuel`,
    stepping `clientContractUserBodies` (`client_contract_entry`, `symId = 66`) through
    `evalClientEntryOperationalWithCalleeOracle` (which executes every statement and terminator of
    `client_contract_entry` and queries `evalStepGenericSlotWithFuel libBodies libFuel 0 0` at the
    call site without unfolding `libBodies`) proves for **all** `base : Nat`:
    1. On `ptrValid = false`, execution fails closed with `(.ub, 0)`.
    2. On `ptrValid = true`, execution returns `(.returned (.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), 1)`. -/
theorem client_contract_user_verified_modularly_from_operational_contract
    (libBodies : List WireBody)
    (libFuel : Nat)
    (hContract : PublishedStatefulLibContractOperational libBodies libFuel)
    (base : Nat) :
    evalClientEntryOperationalWithCalleeOracle clientContractUserBodies 4
      (evalStepGenericSlotWithFuel libBodies libFuel 0 0) false base = (.ub, 0) ∧
    evalClientEntryOperationalWithCalleeOracle clientContractUserBodies 4
      (evalStepGenericSlotWithFuel libBodies libFuel 0 0) true base =
        (.returned (.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), 1) := by
  rcases hContract with ⟨hUb, hOk⟩
  constructor
  · have h0 := hUb base
    change evalClientEntryOperationalWithCalleeOracle clientContractUserBodies 4
      (fun _ _ => evalStepGenericSlotWithFuel libBodies libFuel 0 0 false base) false base = (.ub, 0)
    rw [clientContractUserBodies_eq, h0]
    rfl
  · obtain ⟨t1, evs, h1⟩ := hOk base
    change evalClientEntryOperationalWithCalleeOracle clientContractUserBodies 4
      (fun _ _ => evalStepGenericSlotWithFuel libBodies libFuel 0 0 true base) true base =
        (.returned (.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), 1)
    rw [clientContractUserBodies_eq, h1]
    rfl

theorem evalClientEntryLinkedOperational_direct_false(base : Nat) :
    evalClientEntryLinkedOperational (clientContractUserBodies ++ statefulGenericLibBodies) 16 false base =
      (.ub, 0) := by
  dsimp only [evalClientEntryLinkedOperational]
  rw [linkedDirectBodies_eq, runSteps_DLINK_F_full]
  rfl

theorem evalClientEntryLinkedOperational_direct_true (base : Nat) :
    evalClientEntryLinkedOperational (clientContractUserBodies ++ statefulGenericLibBodies) 16 true base =
      (.returned (.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), 1) := by
  dsimp only [evalClientEntryLinkedOperational]
  rw [linkedDirectBodies_eq, runSteps_DLINK_full]
  rfl

/-- **Universal Operational Call-Oracle to Linked-`runSteps` Bridge (`N1`, `#68` §6 N1 Item 2)**:
    For **every** `ptrValid : Bool` and **every** `base : Nat`, the modular oracle execution
    `evalClientEntryOperationalWithCalleeOracle` on `clientContractUserBodies` equals the full linked
    stack-machine execution `evalClientEntryLinkedOperational (clientContractUserBodies ++ statefulGenericLibBodies) 16`! -/
theorem client_contract_oracle_matches_linked_runSteps_universal
    (ptrValid : Bool) (base : Nat) :
    evalClientEntryLinkedOperational (clientContractUserBodies ++ statefulGenericLibBodies) 16 ptrValid base =
      evalClientEntryOperationalWithCalleeOracle clientContractUserBodies 4
        (evalStepGenericSlotWithFuel statefulGenericLibBodies 12 0 0) ptrValid base := by
  have hMod := client_contract_user_verified_modularly_from_operational_contract
    statefulGenericLibBodies 12 stateful_generic_lib_satisfies_operational_contract base
  cases ptrValid
  · rw [evalClientEntryLinkedOperational_direct_false, hMod.1]
  · rw [evalClientEntryLinkedOperational_direct_true, hMod.2]

/-- Universal operational corollary for `client_contract_entry` on the linked Direct-MIR bodies. -/
theorem client_contract_linked_runSteps_universal
    (base : Nat) :
    evalClientEntryLinkedOperational (clientContractUserBodies ++ statefulGenericLibBodies) 16 false base = (.ub, 0) ∧
    evalClientEntryLinkedOperational (clientContractUserBodies ++ statefulGenericLibBodies) 16 true base =
      (.returned (.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), 1) := by
  rw [client_contract_oracle_matches_linked_runSteps_universal false base]
  rw [client_contract_oracle_matches_linked_runSteps_universal true base]
  exact client_contract_user_verified_modularly_from_operational_contract
    statefulGenericLibBodies 12 stateful_generic_lib_satisfies_operational_contract base

/-- Legacy summary-based client helpers retained for backward compatibility. -/
def evalClientContractEntryWithCalleeSummary
    (clientBodies : List WireBody)
    (stepGenericSummary : Nat → Option (Nat × HeapLogSlot))
    (base : Nat) : Option (Nat × Nat) :=
  match findBodyBySym clientBodies 66 with
  | some body =>
      match getBlockAt body.blocks 0, getBlockAt body.blocks 1, getBlockAt body.blocks 2 with
      | some bb0, some bb1, some bb2 =>
          match bb0.term, bb1.term, bb2.term with
          | .call3 63 dst4 (some 1) _ _ _ _, .call2 40 dst0 (some 2) _ (.move p8) (.constUsize addK), .ret =>
              if dst4.localIdx == 4 && dst0.localIdx == 0 && p8.localIdx == 8 then
                match stepGenericSummary base with
                | some (steppedVal, nextLog) =>
                    some ((steppedVal + addK) % usizeMod, nextLog.stepCount)
                | none => none
              else none
          | _, _, _ => none
      | _, _, _ => none
  | none => none

def clientContractSummaryFromLib (libBodies : List WireBody) (b : Nat) : Option (Nat × HeapLogSlot) :=
  match evalDecodedStepGenericSlotSymbolic libBodies true b with
  | some (.returned (.scalar v), lg, _) => some (v, lg)
  | _ => none

theorem client_contract_user_verified_modularly_from_published_contract
    (libBodies : List WireBody)
    (hContract : PublishedStatefulLibContract libBodies)
    (base : Nat) :
    evalClientContractEntryWithCalleeSummary clientContractUserBodies (clientContractSummaryFromLib libBodies) base =
      some ((((base + 4) % usizeMod) + 8) % usizeMod, 1) := by
  obtain ⟨t1, evs, hEval⟩ := hContract base
  have hSum : clientContractSummaryFromLib libBodies base = some ((base + 4) % usizeMod, { stepCount := 1, traceAcc := t1 }) := by
    unfold clientContractSummaryFromLib
    rw [hEval]
  change (match clientContractSummaryFromLib libBodies base with
    | some (steppedVal, nextLog) => some ((steppedVal + 8) % usizeMod, nextLog.stepCount)
    | none => none) = some ((((base + 4) % usizeMod) + 8) % usizeMod, 1)
  rw [hSum]

/-- Execute `client_audit_entry(log1, log2, ptr, trigger_panic)` (`symId = 67` in
    `client_direct_mir_inspector`) directly on a linked decoded AST with configurable step fuel. -/
def evalClientDirectMirInspectorWithFuel (bodies : List WireBody) (fuel : Nat) (ptrValid triggerPanic : Bool) :
    CleanupExecOutcome :=
  let args : List RtVal :=
    [ .heapPtr 0
    , .heapPtr 1
    , .extPtr ptrValid
    , .scalar (bif triggerPanic then 1 else 0) ]
  let finalSt := runSteps bodies fuel (initEntryState bodies 67 args)
  let (l1, l2) := summarizeTwoHeapLogs finalSt.heap
  match finalSt.status with
  | .returned (.scalar rv) => .normalReturn rv l1 l2 finalSt.obsEvents
  | .unwoundTop => .unwoundWithCleanup l1 l2 finalSt.obsEvents
  | other => .failed other

def evalClientDirectMirInspector (bodies : List WireBody) (ptrValid triggerPanic : Bool) :
    CleanupExecOutcome :=
  evalClientDirectMirInspectorWithFuel bodies 45 ptrValid triggerPanic

/-- **`LIB-03`, `LIB-04`, `LIB-05`: Downstream Client 2 (`client_direct_mir_inspector`) Proof of Omitted Implementation Facts**:
    Without forking `stateful_generic_lib`, `client_direct_mir_inspector` proves directly from the bound
    upstream `.amir` v3 representation (`linkedInspectorAndLibBodies`):
    1. Normal execution (`ptrValid = true, triggerPanic = false`) returns `105` with exact
       `log1 = (2, 65)`, `log2 = (1, 2)`, and chronological trace `obsEvents = [4, 2, 1]`.
    2. Exceptional unwind execution (`ptrValid = true, triggerPanic = true`) unwinds cleanly without
       double-dropping `g1`, producing exact `log1 = (3, 1185)`, `log2 = (1, 2)`, and `obsEvents = [4, 10, 1, 2]`.
    3. Invalid pointer execution (`ptrValid = false`) fails closed at `PlaceMention((*ptr))` inside
       `step_generic_slot::<u32>` with `.failed .ub`. -/
theorem client_direct_mir_inspector_proves_omitted_impl_facts_without_forking :
    evalClientDirectMirInspector linkedInspectorAndLibBodies true false =
      .normalReturn 105 (2, 65) (1, 2) [4, 2, 1] ∧
    evalClientDirectMirInspector linkedInspectorAndLibBodies true true =
      .unwoundWithCleanup (3, 1185) (1, 2) [4, 10, 1, 2] ∧
    evalClientDirectMirInspector linkedInspectorAndLibBodies false false =
      .failed .ub := by
  decide

/-! ## 6. `N2` (`#68` §4.4 & §6 N2): Matched 3-Crate Strongest-Flags Charon `0.1.210` Operational Endpoint -/

/-- All 4 strongest-flags Charon `0.1.210` H3 `.amir` v3 packages (`stateful_generic_lib`,
    `client_contract_user`, `client_direct_mir_inspector`, and `linked_inspector_and_lib`)
    are syntactically and canonically valid `.amir` v3 packages, and the library and linked
    multi-crate packages satisfy full call/drop-glue admission closure (`isAdmittedPackageBytes = true`). -/
theorem charon_h3_packages_admitted_and_closed :
    isAdmittedPackageBytes charonH3StatefulGenericLibAmirBytes = true ∧
    isAdmittedPackageBytes charonH3LinkedInspectorAndLibAmirBytes = true ∧
    checkBodiesWellFormed charonClientContractUserBodies = true ∧
    checkBodiesWellFormed charonClientDirectMirInspectorBodies = true ∧
    checkBodiesClosure (charonClientContractUserBodies ++ charonStatefulGenericLibBodies)
      (charonClientContractUserBodies ++ charonStatefulGenericLibBodies) = true ∧
    checkBodiesClosure charonLinkedInspectorAndLibBodies charonLinkedInspectorAndLibBodies = true := by
  decide

/-- **Universal Operational Library Theorem on Strongest-Flags Charon ULLBC (`N2`)**:
    `charonStatefulGenericLibBodies` (12-block `step_generic_slot` with inlined `const { assert!(size_of::<T>() > 0); }`
    calling `size_of::<u32>() = 4` at `symId = 37` and `align_of::<u32>() = 4` at `symId = 38` from
    `BoundCompilerLayoutTable`) satisfies the exact same `PublishedStatefulLibContractOperational`
    directly over `runSteps` (`fuel = 16`) for **all** `base : Nat`! -/
theorem charon_h3_stateful_generic_lib_satisfies_operational_contract :
    PublishedStatefulLibContractOperational charonStatefulGenericLibBodies 16 := by
  refine ⟨evalCharonStepGenericSlot_false_universal, fun base => ⟨4, [4], evalCharonStepGenericSlot_true_universal base⟩⟩

theorem evalClientEntryLinkedOperational_charon_false(base : Nat) :
    evalClientEntryLinkedOperational (charonClientContractUserBodies ++ charonStatefulGenericLibBodies) 22 false base =
      (.ub, 0) := by
  dsimp only [evalClientEntryLinkedOperational]
  rw [linkedCharonBodies_eq, runSteps_CLINK_F_full]
  rfl

theorem evalClientEntryLinkedOperational_charon_true (base : Nat) :
    evalClientEntryLinkedOperational (charonClientContractUserBodies ++ charonStatefulGenericLibBodies) 22 true base =
      (.returned (.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), 1) := by
  dsimp only [evalClientEntryLinkedOperational]
  rw [linkedCharonBodies_eq, runSteps_CLINK_full]
  rfl

/-- **Universal Modular & Linked Client Theorem on Strongest-Flags Charon ULLBC (`N2`)**:
    1. `charonClientContractUserBodies` is verified modularly for **all** `base : Nat` using only
       `PublishedStatefulLibContractOperational` (`runClientWithCalleeOracle`).
    2. For **all** `ptrValid : Bool` and `base : Nat`, `evalClientEntryOperationalWithCalleeOracle`
       on `charonClientContractUserBodies` equals full linked `runSteps` on
       `charonClientContractUserBodies ++ charonStatefulGenericLibBodies` (`fuel = 22`)! -/
theorem charon_client_contract_user_verified_modularly_from_operational_contract
    (libBodies : List WireBody)
    (libFuel : Nat)
    (hContract : PublishedStatefulLibContractOperational libBodies libFuel)
    (base : Nat) :
    evalClientEntryOperationalWithCalleeOracle charonClientContractUserBodies 5
      (evalStepGenericSlotWithFuel libBodies libFuel 0 0) false base = (.ub, 0) ∧
    evalClientEntryOperationalWithCalleeOracle charonClientContractUserBodies 5
      (evalStepGenericSlotWithFuel libBodies libFuel 0 0) true base =
        (.returned (.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), 1) := by
  rcases hContract with ⟨hUb, hOk⟩
  constructor
  · have h0 := hUb base
    change evalClientEntryOperationalWithCalleeOracle charonClientContractUserBodies 5
      (fun _ _ => evalStepGenericSlotWithFuel libBodies libFuel 0 0 false base) false base = (.ub, 0)
    rw [charonClientContractUserBodies_eq, h0]
    rfl
  · obtain ⟨t1, evs, h1⟩ := hOk base
    change evalClientEntryOperationalWithCalleeOracle charonClientContractUserBodies 5
      (fun _ _ => evalStepGenericSlotWithFuel libBodies libFuel 0 0 true base) true base =
        (.returned (.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), 1)
    rw [charonClientContractUserBodies_eq, h1]
    rfl

theorem charon_h3_client_contract_user_verified_modularly_and_linked
    (base : Nat) :
    evalClientEntryOperationalWithCalleeOracle charonClientContractUserBodies 5
      (evalStepGenericSlotWithFuel charonStatefulGenericLibBodies 16 0 0) false base = (.ub, 0) ∧
    evalClientEntryOperationalWithCalleeOracle charonClientContractUserBodies 5
      (evalStepGenericSlotWithFuel charonStatefulGenericLibBodies 16 0 0) true base =
        (.returned (.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), 1) ∧
    evalClientEntryLinkedOperational (charonClientContractUserBodies ++ charonStatefulGenericLibBodies) 22 false base =
      (.ub, 0) ∧
    evalClientEntryLinkedOperational (charonClientContractUserBodies ++ charonStatefulGenericLibBodies) 22 true base =
      (.returned (.scalar ((((base + 4) % usizeMod) + 8) % usizeMod)), 1) := by
  have hMod := charon_client_contract_user_verified_modularly_from_operational_contract
    charonStatefulGenericLibBodies 16 charon_h3_stateful_generic_lib_satisfies_operational_contract base
  exact ⟨hMod.1, hMod.2, evalClientEntryLinkedOperational_charon_false base, evalClientEntryLinkedOperational_charon_true base⟩

/-- **Matched H3 Downstream Inspector Operational Endpoint on Strongest-Flags Charon ULLBC (`N2`)**:
    Executing `charonLinkedInspectorAndLibBodies` (translated and linked by `extract_and_link_charon_h3.py`
    from `client_direct_mir_inspector_strongest.ullbc` and `stateful_generic_lib_strongest.ullbc`, with
    `core::mem::drop<T>`'s `Destruct::drop_in_place` resolved via `translated.trait_impls[1]` to
    `Guard::drop_in_place` `symId = 7`) through `evalClientDirectMirInspectorWithFuel` (`fuel = 60`)
    produces the **exact same** normal return (`105`, `(2, 65)`, `(1, 2)`, `[4, 2, 1]`), unwind cleanup
    (`(3, 1185)`, `(1, 2)`, `[4, 10, 1, 2]`), and invalid-pointer UB (`.failed .ub`) outcomes as Direct MIR! -/
theorem charon_h3_inspector_matches_direct_mir_operational_outcomes :
    evalClientDirectMirInspectorWithFuel charonLinkedInspectorAndLibBodies 60 true false =
      evalClientDirectMirInspector linkedInspectorAndLibBodies true false ∧
    evalClientDirectMirInspectorWithFuel charonLinkedInspectorAndLibBodies 60 true true =
      evalClientDirectMirInspector linkedInspectorAndLibBodies true true ∧
    evalClientDirectMirInspectorWithFuel charonLinkedInspectorAndLibBodies 60 false false =
      evalClientDirectMirInspector linkedInspectorAndLibBodies false false ∧
    evalClientDirectMirInspectorWithFuel charonLinkedInspectorAndLibBodies 60 true false =
      .normalReturn 105 (2, 65) (1, 2) [4, 2, 1] ∧
    evalClientDirectMirInspectorWithFuel charonLinkedInspectorAndLibBodies 60 true true =
      .unwoundWithCleanup (3, 1185) (1, 2) [4, 10, 1, 2] ∧
    evalClientDirectMirInspectorWithFuel charonLinkedInspectorAndLibBodies 60 false false =
      .failed .ub := by
  decide


#print axioms h3_three_crate_workspace_bindings_and_admission_verified
#print axioms step_generic_slot_symbolic_summary_matches_runSteps_universal
#print axioms step_generic_slot_stack_machine_agrees_with_symbolic_decoded_eval
#print axioms stateful_generic_lib_satisfies_operational_contract
#print axioms stateful_generic_lib_satisfies_published_contract
#print axioms client_contract_user_verified_modularly_from_operational_contract
#print axioms client_contract_oracle_matches_linked_runSteps_universal
#print axioms client_contract_linked_runSteps_universal
#print axioms client_contract_user_verified_modularly_from_published_contract
#print axioms client_direct_mir_inspector_proves_omitted_impl_facts_without_forking
#print axioms charon_h3_packages_admitted_and_closed
#print axioms charon_h3_stateful_generic_lib_satisfies_operational_contract
#print axioms charon_h3_client_contract_user_verified_modularly_and_linked
#print axioms charon_h3_inspector_matches_direct_mir_operational_outcomes

end AnnealResearch.StatefulGenericLibraryH3H7
