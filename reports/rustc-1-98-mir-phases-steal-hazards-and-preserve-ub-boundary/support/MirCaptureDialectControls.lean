import AnnealResearch.MirCaptureDialects

set_option Elab.async false

/-!
# Negative and Adversarial Controls for MIR Capture and Dialects (`FE-03` and `FE-04`)

This module proves six negative and adversarial control theorems demonstrating
what goes wrong when any component of the `FE-03` capture contract or `FE-04`
`Runtime(PostCleanup)` dialect discipline is weakened:

1. **Silent fallback to `optimized_mir` after `Steal<Body>` consumption**:
   Accepting a post-steal fallback to `Runtime(Optimized)` (`dialectId = 4`)
   passes a naive runtime-dialect check while violating `AdmissibleCapture`.
2. **Unsound `SysNoUB` verification on `Runtime(Optimized)`**: An optimization
   pass that elides a dead unsafe load before an infinite loop turns a
   `Runtime(PostCleanup)` body with reachable UB (`¬ Execution.SysNoUB`) into a
   `Runtime(Optimized)` body that spuriously satisfies `Execution.SysNoUB`.
3. **Misinterpreting partial moves in unelaborated `Analysis(PostCleanup)`**:
   Without drop elaboration (`ElaborateDrops`) and dynamic drop flag `_16`,
   `Analysis(PostCleanup)` predicts a scope-exit drop of `(_4.1: Leaf)` on
   configuration `c3` (`(false, true, false)`) even though `_4.1` was moved into
   `std::mem::forget`.
4. **Early callback before post-monomorphization CTFE failure**: Grounded in
   `experiments/configured-admission/probe.rs` (`b1`), a callback that captures
   MIR before post-monomorphization evaluation of `checked::{constant#0}`
   (`Le(const N, const <T as Bound>::LIMIT)`) admits a crate whose compilation
   fails.
5. **Omitted promoted constant or closure bodies**: Grounded in
   `cleanup_binding.mir` (`record::promoted[0]` and `record::{closure#0}`),
   capturing only top-level `fn` items violates `CompleteBodyInventory` and
   `AdmissibleCapture`.
6. **Adversarial unwind-edge mutations (`bb6` and `bb11`)**: Mutating `bb6`'s
   unwind target or ignoring drop flag `_16` at `bb11` preserves normal-return
   behavior (`c1`) while either leaking `(_4.1: Leaf)` on `c4` or double-dropping
   the forgotten field on `(false, true, true)`.
-/

namespace AnnealResearch.MirCaptureDialectControls

open AnnealResearch.MirCaptureDialects

/-- Naive capture check that accepts either `Runtime(PostCleanup)` (`3`) or
`Runtime(Optimized)` (`4`) without verifying `beforeSteal` (`r.2.1 = true`). -/
def NaiveRuntimeMirCheck (r : CaptureReceipt) : Prop :=
  (r.1 = 3 ∨ r.1 = 4) ∧ r.2.2.1 = true ∧ CompleteBodyInventory r

/-- Receipt produced when a capture tool attempts to read
`mir_drops_elaborated_and_const_checked` after `Steal<Body>` theft
(`beforeSteal = false`) and silently falls back to `tcx.optimized_mir(def_id)`
(`dialectId = 4`). -/
noncomputable def stolenFallbackReceipt : CaptureReceipt :=
  (4, false, true, true, true, true, true)

/-- **Control 1 (`FE-03` / `FE-04`)**: Silent fallback to `optimized_mir` after
`Steal<Body>` consumption passes `NaiveRuntimeMirCheck` but is rejected by
`AdmissibleCapture`. -/
theorem stolen_query_silent_optimized_fallback_control :
    NaiveRuntimeMirCheck stolenFallbackReceipt ∧
    ¬ AdmissibleCapture stolenFallbackReceipt := by
  refine ⟨⟨Or.inr rfl, rfl, ⟨rfl, rfl, rfl⟩⟩, ?_⟩
  intro hAdm
  have h43 : (4 : Nat) = 3 := hAdm.1
  cases h43

/-- `Runtime(Optimized)` transition step after dead-load elimination elides the
unsafe operation before an infinite loop, collapsing `0 → 1 → 1` into `0 → 0`. -/
def optimizedElidedUbStep (s s' : Nat) : Prop := s = 0 ∧ s' = 0

/-- **Control 2 (`FE-04`)**: Verifying `Execution.NoUB` on `Runtime(Optimized)`
after dead-operation elimination before a diverging loop is unsound with respect
to `Runtime(PostCleanup)`: `optimizedElidedUbStep` satisfies `Execution.NoUB`,
whereas `postCleanupUbBeforeLoopStep` violates `Execution.NoUB`. -/
theorem optimized_mir_elides_ub_before_divergence_control :
    Execution.NoUB optimizedElidedUbStep divergingLoopBad 0 ∧
    ¬ Execution.NoUB postCleanupUbBeforeLoopStep divergingLoopBad 0 :=
  ⟨post_cleanup_preserves_safe_divergence_and_exposes_unsafe_prefix.1,
   post_cleanup_preserves_safe_divergence_and_exposes_unsafe_prefix.2.2⟩

/-- **Control 3 (`FE-04`)**: On partial-move configuration `c3`
(`(false, true, false)`, where `_4.1` is passed to `std::mem::forget` after
`bb4` sets `_16 = const false`), the unelaborated `Analysis(PostCleanup)` drop
view `(1, 1)` disagrees with the `Runtime(PostCleanup)` elaborated drop count
`(1, 0)` because `DropFlagCoincidenceObligation` fails. -/
theorem analysis_mir_unelaborated_drop_misinterprets_partial_move_control :
    AnalysisDropView (false, true, false) = (1, 1) ∧
    RuntimeElaboratedDropView (false, true, false) = (1, 0) ∧
    RuntimeElaboratedDropView (false, true, false) ≠
      AnalysisDropView (false, true, false) ∧
    ¬ DropFlagCoincidenceObligation (false, true, false) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro hEq
    have h01 : (0 : Nat) = 1 := congrArg Prod.snd hEq
    cases h01
  · intro hObl
    have htf : true = false := hObl.2
    cases htf

/-- Early callback check that inspects `Runtime(PostCleanup)` syntax and body
inventory before post-monomorphization constant evaluation (`r.2.2.1`) completes. -/
def EarlyBeforePostMonoConstCheck (r : CaptureReceipt) : Prop :=
  r.1 = 3 ∧ r.2.1 = true ∧ CompleteBodyInventory r ∧ r.2.2.2.2.2.2 = true

/-- Receipt for `experiments/configured-admission/probe.rs` in configuration `b1`
(no `--cfg admit`), where `probe.mir` is emitted with `checked::<B, 1>()` and
inline constant body `checked::{constant#0}`, but post-monomorphization CTFE
panics at `Le(const N, const <T as Bound>::LIMIT)` (`postMonoConstOk = false`). -/
noncomputable def probeB1EarlyReceipt : CaptureReceipt :=
  (3, true, false, true, true, true, true)

/-- **Control 4 (`FE-03`)**: An early compiler callback that does not gate on
post-monomorphization CTFE (`EarlyBeforePostMonoConstCheck`) admits
`probeB1EarlyReceipt`, whereas `AdmissibleCapture` rejects it. -/
theorem early_callback_before_post_mono_const_error_control :
    EarlyBeforePostMonoConstCheck probeB1EarlyReceipt ∧
    ¬ AdmissibleCapture probeB1EarlyReceipt := by
  refine ⟨⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩, ?_⟩
  intro hAdm
  have hft : false = true := hAdm.2.2.1
  cases hft

/-- Receipt that captures top-level functions and closures of `cleanup_binding.rs`
but omits promoted constant bodies (`const record::promoted[0]`, lines 639–648). -/
noncomputable def missingPromotedReceipt : CaptureReceipt :=
  (3, true, true, true, false, true, true)

/-- Receipt that captures top-level functions and promoted constants of
`cleanup_binding.rs` but omits closure bodies (`record::{closure#0}`,
lines 650–688, and `EVENTS::{constant#0}::{closure#0..1}`). -/
noncomputable def missingClosureReceipt : CaptureReceipt :=
  (3, true, true, true, true, false, true)

/-- **Control 5 (`FE-03`)**: Omitting either promoted constant bodies
(`missingPromotedReceipt`) or closure/shim bodies (`missingClosureReceipt`)
violates both `CompleteBodyInventory` and `AdmissibleCapture`. -/
theorem omitted_promoted_or_closure_body_control :
    ¬ CompleteBodyInventory missingPromotedReceipt ∧
    ¬ AdmissibleCapture missingPromotedReceipt ∧
    ¬ CompleteBodyInventory missingClosureReceipt ∧
    ¬ AdmissibleCapture missingClosureReceipt := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hInv
    have hft : false = true := hInv.2.1
    cases hft
  · intro hAdm
    have hft : false = true := hAdm.2.2.2.2.1
    cases hft
  · intro hInv
    have hft : false = true := hInv.2.2
    cases hft
  · intro hAdm
    have hft : false = true := hAdm.2.2.2.2.2.1
    cases hft

/-- Adversarial CFG mutation of `cleanup_binding::exercise`: mutates `bb6`'s
unwind edge to jump directly to `bb10: resume` instead of `bb11`, AND mutates
`bb11` to jump unconditionally to `bb12` without checking drop flag `_16`. -/
noncomputable def mutatedUnwindExerciseRun
    (skipBb11OnUnwind : Bool) (cfg : ExerciseCfg) : ExerciseState :=
  let step (s : ExerciseState) : ExerciseState :=
    let bb := s.1
    let flag16 := s.2.1
    let d1 := s.2.2.1
    let d2 := s.2.2.2.1
    if bb = 5 then
      if cfg.2.2 then
        if skipBb11OnUnwind then (10, flag16, d1 + 1, d2, 2)
        else (11, flag16, d1 + 1, d2, 0)
      else
        postCleanupExerciseNext cfg s
    else if bb = 11 then
      (12, flag16, d1, d2, 0)
    else
      postCleanupExerciseNext cfg s
  let s1 := step exerciseInit
  let s2 := step s1
  let s3 := step s2
  let s4 := step s3
  let s5 := step s4
  let s6 := step s5
  step s6

/-- **Control 6 (`FE-04`)**: Both unwind-edge mutations agree with
`postCleanupExerciseRun` on normal-return case `c1` (`(false, false, false)`),
but skipping `bb11` on unwind (`skipBb11OnUnwind = true`) leaks `(_4.1: Leaf)`
on panic-in-drop case `c4` (`(false, false, true)`), while ignoring `_16` at
`bb11` (`skipBb11OnUnwind = false`) drops the already-forgotten `(_4.1: Leaf)`
on `(false, true, true)`. -/
theorem mutated_unwind_edge_preserves_normal_return_but_leaks_or_double_drops :
    mutatedUnwindExerciseRun true (false, false, false) =
      postCleanupExerciseRun (false, false, false) ∧
    mutatedUnwindExerciseRun false (false, false, false) =
      postCleanupExerciseRun (false, false, false) ∧
    (mutatedUnwindExerciseRun true (false, false, true)).2.2.2.1 = 0 ∧
    (postCleanupExerciseRun (false, false, true)).2.2.2.1 = 1 ∧
    (mutatedUnwindExerciseRun false (false, true, true)).2.2.2.1 = 1 ∧
    (postCleanupExerciseRun (false, true, true)).2.2.2.1 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms stolen_query_silent_optimized_fallback_control
#print axioms optimized_mir_elides_ub_before_divergence_control
#print axioms analysis_mir_unelaborated_drop_misinterprets_partial_move_control
#print axioms early_callback_before_post_mono_const_error_control
#print axioms omitted_promoted_or_closure_body_control
#print axioms mutated_unwind_edge_preserves_normal_return_but_leaks_or_double_drops

end AnnealResearch.MirCaptureDialectControls
