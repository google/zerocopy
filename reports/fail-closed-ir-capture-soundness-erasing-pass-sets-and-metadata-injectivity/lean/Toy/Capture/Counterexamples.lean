import Toy.Capture.Examples

/-!
# Counterexamples, non-vacuity witnesses and positive controls

Each counterexample is stated in canonical form: a concrete instance satisfies all
other hypotheses of the named theorem, and its conclusion fails.
-/

namespace Toy.Capture

/-! ## Shared facts -/

theorem hV_exact (os : OpaqueSem) : VerifierSound (semV os) (exactVerifier (semV os)) :=
  exactVerifier_sound _

theorem hcap_FC (os : OpaqueSem) : OverApproxOnOk semS (semV os) capFC :=
  (capFC_faithfulOnOk os).overApproxOnOk

theorem qRet_ubFree (os : OpaqueSem) : exactVerifier (semV os) qRet ubFree :=
  sat_semV_of_run (fun _ => ⟨[], .ret⟩) (runV_qRet os) (fun _ => by simp [ubFree])

theorem qGoto_ubFree (os : OpaqueSem) : exactVerifier (semV os) qGoto ubFree :=
  sat_semV_of_run (fun _ => ⟨[], .ret⟩) (runV_qGoto os) (fun _ => by simp [ubFree])

theorem qOk_ubFree (os : OpaqueSem) : exactVerifier (semV os) qOk ubFree :=
  sat_semV_of_run (fun _ => ⟨[], .ret⟩) (runV_qOk os) (fun _ => by simp [ubFree])

theorem pPM_not_ubFree : ¬ Sat (semS pPM) ubFree :=
  not_sat_semS_of_run 0 ⟨[], .ub⟩ rfl (by decide)

theorem qPM_not_ubFree (os : OpaqueSem) : ¬ exactVerifier (semV os) qPM ubFree :=
  not_sat_semV_of_run 0 ⟨[], .ub⟩ (runV_qPM os 0) (by decide)

theorem nilPipe_equivTagSound : ∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P :=
  fun _ h => by cases h

theorem nilPipe_erasingSetPrecondition (src : SProg) :
    ErasingSetPrecondition semS ([] : List (Pass SProg)) src :=
  fun _ h => by simp at h

theorem nilPipe_losesNoBehaviourAtInputs (src : SProg) :
    LosesNoBehaviourAtInputs semS ([] : List (Pass SProg)) src :=
  fun _ h => by simp at h

/-- One `erasing` pass that removes zero-size reads. -/
def pipeZst : List (Pass SProg) := [⟨.erasing, eraseZstReads⟩]
/-- One `erasing` pass that replaces equal-target switches by gotos. -/
def pipeSw : List (Pass SProg) := [⟨.erasing, simplifyTrivialSwitches⟩]
/-- A mis-tagged pipeline: the place-mention eraser tagged `equiv`. -/
def pipeMis : List (Pass SProg) := [⟨.equiv, erasePlaceMentions⟩]

theorem pipePM_equivTagSound : ∀ P ∈ pipePM, EquivTagSound semS P := by
  intro P hP
  simp only [pipePM, List.mem_cons, List.not_mem_nil, or_false] at hP
  subst hP
  exact equivTagSound_erasing _

theorem pipeZst_equivTagSound : ∀ P ∈ pipeZst, EquivTagSound semS P := by
  intro P hP
  simp only [pipeZst, List.mem_cons, List.not_mem_nil, or_false] at hP
  subst hP
  exact equivTagSound_erasing _

theorem pipeSw_equivTagSound : ∀ P ∈ pipeSw, EquivTagSound semS P := by
  intro P hP
  simp only [pipeSw, List.mem_cons, List.not_mem_nil, or_false] at hP
  subst hP
  exact equivTagSound_erasing _

theorem pipeOk_equivTagSound : ∀ P ∈ pipeOk, EquivTagSound semS P := by
  intro P hP
  simp only [pipeOk, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl
  · exact equivTagSound_erasing _
  · exact equivTagSound_example_pos

/-! ## Capture after a UB-erasing pass -/

/-- **Capture after place-mention erasure.** For `transfer_relative_to_erasingSet` with the exact
verifier for `semV .noop`, the fail-closed capture, the pipeline `pipePM` (one
`erasing` pass removing place mentions), source `pPM`, `q = qRet` and spec
`ubFree`: every hypothesis except the erasing-set precondition holds, the
precondition fails, and the conclusion fails (`pPM` is UB on input `0`). -/
theorem cex_erasingSet_placeMention :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ pipePM, EquivTagSound semS P) ∧
    capFC (runPipe pipePM pPM) = .ok qRet ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    ¬ ErasingSetPrecondition semS pipePM pPM ∧
    ¬ Sat (semS pPM) ubFree :=
  ⟨hV_exact _, hcap_FC _, pipePM_equivTagSound, rfl, qRet_ubFree _,
    erasingSetPrecondition_example_neg, pPM_not_ubFree⟩

/-- **Capture after zero-size-read erasure.** As `cex_erasingSet_placeMention`, with the pass
removing zero-size reads and the source `pZst`. -/
theorem cex_erasingSet_zstRead :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ pipeZst, EquivTagSound semS P) ∧
    capFC (runPipe pipeZst pZst) = .ok qRet ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    ¬ ErasingSetPrecondition semS pipeZst pZst ∧
    ¬ Sat (semS pZst) ubFree := by
  refine ⟨hV_exact _, hcap_FC _, pipeZst_equivTagSound, rfl, qRet_ubFree _, ?_,
    not_sat_semS_of_run 0 ⟨[], .ub⟩ rfl (by decide)⟩
  intro h
  have := h 0 (by decide) rfl (0, ⟨[], .ub⟩) rfl
  exact absurd this (by decide)

/-- **Capture after equal-target switch erasure.** As `cex_erasingSet_placeMention`, with the pass
replacing equal-target switches by gotos and the source `pSw` (a switch on an
uninitialized local, UB on every input). -/
theorem cex_erasingSet_trivialSwitch :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ pipeSw, EquivTagSound semS P) ∧
    capFC (runPipe pipeSw pSw) = .ok qGoto ∧
    exactVerifier (semV .noop) qGoto ubFree ∧
    ¬ ErasingSetPrecondition semS pipeSw pSw ∧
    ¬ Sat (semS pSw) ubFree := by
  refine ⟨hV_exact _, hcap_FC _, pipeSw_equivTagSound, rfl, qGoto_ubFree _, ?_,
    not_sat_semS_of_run 0 ⟨[], .ub⟩ rfl (by decide)⟩
  intro h
  have := h 0 (by decide) rfl (0, ⟨[], .ub⟩) rfl
  exact absurd this (by decide)

/-- **Control: erasure disabled.** Without the erasing pass (empty pipeline), the
fail-closed capture of `pPM` keeps the place mention, and the exact verifier does
not accept `ubFree` for it. -/
theorem erasure_disabled_control (os : OpaqueSem) :
    capFC (runPipe [] pPM) = .ok qPM ∧ ¬ exactVerifier (semV os) qPM ubFree :=
  ⟨rfl, qPM_not_ubFree os⟩

/-! ## Fail-open captures -/

/-- **Fail-open capture, default.** For `transfer_relative_to_erasingSet` with the exact
verifier for `semV .noop`, the empty pipeline, source `pTrap` (aborts through the
unmodeled `trap`), `q = qGoto` and spec `returnsNormally`: every hypothesis except
over-approximation holds for `capDefault`, over-approximation fails, and the
conclusion fails. -/
theorem cex_hcap_default :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pTrap ∧
    capDefault (runPipe [] pTrap) = .ok qGoto ∧
    exactVerifier (semV .noop) qGoto returnsNormally ∧
    ¬ OverApproxOnOk semS (semV .noop) capDefault ∧
    ¬ Sat (semS pTrap) returnsNormally := by
  refine ⟨hV_exact _, nilPipe_equivTagSound, nilPipe_erasingSetPrecondition _, rfl,
    sat_semV_of_run (fun _ => ⟨[], .ret⟩) (runV_qGoto _) (fun _ => rfl), ?_,
    not_sat_semS_of_run 0 _ (runS_pTrap 0) (by decide)⟩
  intro h
  have := h pTrap qGoto capDefault_pTrap (0, ⟨[], .trap⟩) rfl
  simp [semV, runV_qGoto, VRes.admits] at this

/-- **Fail-open capture, stringify (opaque read as a no-op).** Source `pAsm` (outputs `7`),
`capStringify`, `q = qAsm`, spec `silent`, verifier semantics `semV .noop`. -/
theorem cex_hcap_stringify_noop :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pAsm ∧
    capStringify (runPipe [] pAsm) = .ok qAsm ∧
    exactVerifier (semV .noop) qAsm silent ∧
    ¬ OverApproxOnOk semS (semV .noop) capStringify ∧
    ¬ Sat (semS pAsm) silent :=
  ⟨hV_exact _, nilPipe_equivTagSound, nilPipe_erasingSetPrecondition _, rfl,
    sat_semV_of_run (fun _ => ⟨[], .ret⟩) runV_qAsm_noop (fun _ => rfl),
    overApproxOnOk_example_neg, not_sat_semS_of_run 0 _ (runS_pAsm 0) (by decide)⟩

/-- **Fail-open capture, swallow.** Source `pErr` (outputs an erroneous constant, outcome
`constErr`), `capSwallow` (the constant becomes `0`), `q = qZero`, spec
`returnsNormally`. -/
theorem cex_hcap_swallow :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pErr ∧
    capSwallow (runPipe [] pErr) = .ok qZero ∧
    exactVerifier (semV .noop) qZero returnsNormally ∧
    ¬ OverApproxOnOk semS (semV .noop) capSwallow ∧
    ¬ Sat (semS pErr) returnsNormally := by
  refine ⟨hV_exact _, nilPipe_equivTagSound, nilPipe_erasingSetPrecondition _, rfl,
    sat_semV_of_run (fun _ => ⟨[0], .ret⟩) (runV_qZero _) (fun _ => rfl), ?_,
    not_sat_semS_of_run 0 _ (runS_pErr 0) (by decide)⟩
  intro h
  have := h pErr qZero capSwallow_pErr (0, ⟨[], .constErr⟩) rfl
  simp [semV, runV_qZero, VRes.admits] at this

/-! ## Captures that forget behaviour-distinguishing metadata -/

/-- **Cleanup mark forgotten.** `capNoCleanup` maps `pCl` and `pNo` to the same `qUnw`,
although `pCl` aborts with reason `inCleanup` and `pNo` unwinds. -/
theorem cleanupMark_merged_pair :
    capNoCleanup pCl = .ok qUnw ∧ capNoCleanup pNo = .ok qUnw ∧
    ¬ DenEquiv (semS pCl) (semS pNo) :=
  ⟨rfl, rfl, denEquiv_example_neg⟩

/-- **Cleanup mark forgotten, transfer failure.** For
`transfer_relative_to_erasingSet` with the exact verifier for `semV .noop`, the
empty pipeline, source `pCl`, `q = qUnw` and spec `noAbort`: every hypothesis
except over-approximation holds for `capNoCleanup`, and the conclusion fails. -/
theorem cex_hcap_noCleanup :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pCl ∧
    capNoCleanup (runPipe [] pCl) = .ok qUnw ∧
    exactVerifier (semV .noop) qUnw noAbort ∧
    ¬ OverApproxOnOk semS (semV .noop) capNoCleanup ∧
    ¬ Sat (semS pCl) noAbort := by
  refine ⟨hV_exact _, nilPipe_equivTagSound, nilPipe_erasingSetPrecondition _, rfl,
    sat_semV_of_run (fun _ => ⟨[], .unwind⟩) (runV_qUnw _) (fun _ => rfl), ?_,
    not_sat_semS_of_run 0 _ (runS_pCl 0) (by decide)⟩
  intro h
  have := h pCl qUnw capNoCleanup_pCl (0, ⟨[], .abort .inCleanup⟩) rfl
  simp [semV, runV_qUnw, VRes.admits] at this

/-- **Terminate reason forgotten.** `capNoReason` maps `pTerm .abi` and
`pTerm .inCleanup` to the same `qTermAbi`, although their abort reasons differ. -/
theorem terminateReason_merged_pair :
    capNoReason (pTerm .abi) = .ok qTermAbi ∧ capNoReason (pTerm .inCleanup) = .ok qTermAbi ∧
    ¬ DenEquiv (semS (pTerm .abi)) (semS (pTerm .inCleanup)) :=
  ⟨rfl, rfl, not_denEquiv_of_run (0, ⟨[], .abort .abi⟩) rfl (by decide)⟩

/-- **Terminate reason forgotten, transfer failure.** Source `pTerm .inCleanup`,
`capNoReason`, `q = qTermAbi`, spec `noAbortInCleanup`. -/
theorem cex_hcap_noReason :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] (pTerm .inCleanup) ∧
    capNoReason (runPipe [] (pTerm .inCleanup)) = .ok qTermAbi ∧
    exactVerifier (semV .noop) qTermAbi noAbortInCleanup ∧
    ¬ OverApproxOnOk semS (semV .noop) capNoReason ∧
    ¬ Sat (semS (pTerm .inCleanup)) noAbortInCleanup := by
  refine ⟨hV_exact _, nilPipe_equivTagSound, nilPipe_erasingSetPrecondition _, rfl,
    sat_semV_of_run (fun _ => ⟨[], .abort .abi⟩) (runV_qTermAbi _) (fun _ => by simp [noAbortInCleanup]), ?_,
    not_sat_semS_of_run 0 _ (runS_pTerm .inCleanup 0) (by decide)⟩
  intro h
  have := h (pTerm .inCleanup) qTermAbi (capNoReason_pTerm _) (0, ⟨[], .abort .inCleanup⟩) rfl
  simp [semV, runV_qTermAbi, VRes.admits] at this

/-! ## Remaining tightness counterexamples for the transfer theorems -/

/-- Tightness of verifier soundness: with the unsound `trustAll`, every other
hypothesis of `transfer_relative_to_erasingSet` holds (empty pipeline, `capFC`,
source `pPM`, `q = qPM`, spec `ubFree`) and the conclusion fails. -/
theorem cex_hV :
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pPM ∧
    capFC (runPipe [] pPM) = .ok qPM ∧
    trustAll qPM ubFree ∧
    ¬ VerifierSound (semV .noop) trustAll ∧
    ¬ Sat (semS pPM) ubFree :=
  ⟨hcap_FC _, nilPipe_equivTagSound, nilPipe_erasingSetPrecondition _, rfl, trivial,
    verifierSound_example_neg _, pPM_not_ubFree⟩

/-- Tightness of `equiv`-tag soundness: with the place-mention eraser tagged
`equiv` (`pipeMis`), the erasing set is empty, so the erasing-set precondition
holds vacuously; every other hypothesis holds and the conclusion fails. -/
theorem cex_hEq :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    ErasingSetPrecondition semS pipeMis pPM ∧
    capFC (runPipe pipeMis pPM) = .ok qRet ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    ¬ (∀ P ∈ pipeMis, EquivTagSound semS P) ∧
    ¬ Sat (semS pPM) ubFree := by
  refine ⟨hV_exact _, hcap_FC _, ?_, rfl, qRet_ubFree _, ?_, pPM_not_ubFree⟩
  · intro i hi htag
    match i, hi, htag with
    | 0, _, h => cases h
  · intro h
    exact equivTagSound_example_neg (h _ (by simp [pipeMis]))

/-- Tightness of the capture premise: `qRet` is verified UB-free, but it is not the
capture of `pPM`; every other hypothesis holds and the conclusion fails. -/
theorem cex_hok :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pPM ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    capFC (runPipe [] pPM) ≠ .ok qRet ∧
    ¬ Sat (semS pPM) ubFree :=
  ⟨hV_exact _, hcap_FC _, nilPipe_equivTagSound, nilPipe_erasingSetPrecondition _,
    qRet_ubFree _, by decide, pPM_not_ubFree⟩

/-- Tightness of the verdict premise: `qPM` is the capture of `pPM` but is not
verified UB-free; every other hypothesis holds and the conclusion fails. -/
theorem cex_hver :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    (∀ P ∈ ([] : List (Pass SProg)), EquivTagSound semS P) ∧
    ErasingSetPrecondition semS [] pPM ∧
    capFC (runPipe [] pPM) = .ok qPM ∧
    ¬ exactVerifier (semV .noop) qPM ubFree ∧
    ¬ Sat (semS pPM) ubFree :=
  ⟨hV_exact _, hcap_FC _, nilPipe_equivTagSound, nilPipe_erasingSetPrecondition _, rfl,
    qPM_not_ubFree _, pPM_not_ubFree⟩

/-! ### Counterexamples in the exact shape of the other transfer theorems -/

/-- The single pass removing place mentions, tagged `erasing`. -/
def passPM : Pass SProg := ⟨.erasing, erasePlaceMentions⟩
/-- `transfer_of_losesNoBehaviourAtInputs`, hypothesis `hpipe`: `pipePM` at `pPM`;
all other hypotheses hold and the conclusion fails. -/
theorem cex_pipeline_hpipe :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    capFC (runPipe pipePM pPM) = .ok qRet ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    ¬ LosesNoBehaviourAtInputs semS pipePM pPM ∧
    ¬ Sat (semS pPM) ubFree :=
  ⟨hV_exact _, hcap_FC _, rfl, qRet_ubFree _, losesNoBehaviourAtInputs_example_neg,
    pPM_not_ubFree⟩

/-- `transfer_of_losesNoBehaviourAtInputs`, hypothesis `hV`: the empty pipeline,
`capFC`, source `pPM`, the unsound `trustAll`. -/
theorem cex_pipeline_hV :
    OverApproxOnOk semS (semV .noop) capFC ∧
    LosesNoBehaviourAtInputs semS [] pPM ∧
    capFC (runPipe [] pPM) = .ok qPM ∧
    trustAll qPM ubFree ∧
    ¬ VerifierSound (semV .noop) trustAll ∧
    ¬ Sat (semS pPM) ubFree :=
  ⟨hcap_FC _, nilPipe_losesNoBehaviourAtInputs _, rfl, trivial,
    verifierSound_example_neg _, pPM_not_ubFree⟩

/-- `transfer_of_losesNoBehaviourAtInputs`, hypothesis `hcap`: the empty pipeline,
`capDefault`, source `pTrap`, spec `returnsNormally`. -/
theorem cex_pipeline_hcap :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    LosesNoBehaviourAtInputs semS [] pTrap ∧
    capDefault (runPipe [] pTrap) = .ok qGoto ∧
    exactVerifier (semV .noop) qGoto returnsNormally ∧
    ¬ OverApproxOnOk semS (semV .noop) capDefault ∧
    ¬ Sat (semS pTrap) returnsNormally :=
  ⟨hV_exact _, nilPipe_losesNoBehaviourAtInputs _, rfl,
    cex_hcap_default.2.2.2.2.1, cex_hcap_default.2.2.2.2.2.1, cex_hcap_default.2.2.2.2.2.2⟩

/-- `transfer_of_losesNoBehaviourAtInputs`, hypothesis `hok`: `qRet` is verified
UB-free but is not the capture of `pPM`. -/
theorem cex_pipeline_hok :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    LosesNoBehaviourAtInputs semS [] pPM ∧
    exactVerifier (semV .noop) qRet ubFree ∧
    capFC (runPipe [] pPM) ≠ .ok qRet ∧
    ¬ Sat (semS pPM) ubFree :=
  ⟨hV_exact _, hcap_FC _, nilPipe_losesNoBehaviourAtInputs _,
    qRet_ubFree _, by decide, pPM_not_ubFree⟩

/-- `transfer_of_losesNoBehaviourAtInputs`, hypothesis `hver`: the capture `qPM` of
`pPM` is not verified UB-free. -/
theorem cex_pipeline_hver :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧
    LosesNoBehaviourAtInputs semS [] pPM ∧
    capFC (runPipe [] pPM) = .ok qPM ∧
    ¬ exactVerifier (semV .noop) qPM ubFree ∧
    ¬ Sat (semS pPM) ubFree :=
  ⟨hV_exact _, hcap_FC _, nilPipe_losesNoBehaviourAtInputs _,
    rfl, qPM_not_ubFree _, pPM_not_ubFree⟩

/-! ### Counterexamples in the exact shape of `transfer_to_capture_input` -/

/-- `transfer_to_capture_input`, hypothesis `hV`: `capFC`, `p = pPM`, `q = qPM`,
spec `ubFree`, the unsound `trustAll`. -/
theorem cex_capInput_hV :
    OverApproxOnOk semS (semV .noop) capFC ∧ capFC pPM = .ok qPM ∧ trustAll qPM ubFree ∧
    ¬ VerifierSound (semV .noop) trustAll ∧ ¬ Sat (semS pPM) ubFree :=
  ⟨hcap_FC _, rfl, trivial, verifierSound_example_neg _, pPM_not_ubFree⟩

/-- `transfer_to_capture_input`, hypothesis `hcap`: `capDefault`, `p = pTrap`,
`q = qGoto`, spec `returnsNormally`. -/
theorem cex_capInput_hcap :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧ capDefault pTrap = .ok qGoto ∧
    exactVerifier (semV .noop) qGoto returnsNormally ∧
    ¬ OverApproxOnOk semS (semV .noop) capDefault ∧ ¬ Sat (semS pTrap) returnsNormally :=
  ⟨hV_exact _, rfl, cex_hcap_default.2.2.2.2.1, cex_hcap_default.2.2.2.2.2.1,
    cex_hcap_default.2.2.2.2.2.2⟩

/-- `transfer_to_capture_input`, hypothesis `hok`: `qRet` is verified UB-free but is
not the capture of `pPM`. -/
theorem cex_capInput_hok :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧ exactVerifier (semV .noop) qRet ubFree ∧
    capFC pPM ≠ .ok qRet ∧ ¬ Sat (semS pPM) ubFree :=
  ⟨hV_exact _, hcap_FC _, qRet_ubFree _, by decide, pPM_not_ubFree⟩

/-- `transfer_to_capture_input`, hypothesis `hver`: the capture `qPM` of `pPM` is
not verified UB-free. -/
theorem cex_capInput_hver :
    VerifierSound (semV .noop) (exactVerifier (semV .noop)) ∧
    OverApproxOnOk semS (semV .noop) capFC ∧ capFC pPM = .ok qPM ∧
    ¬ exactVerifier (semV .noop) qPM ubFree ∧ ¬ Sat (semS pPM) ubFree :=
  ⟨hV_exact _, hcap_FC _, rfl, qPM_not_ubFree _, pPM_not_ubFree⟩

/-! ## Non-vacuity of the transfer theorems -/

/-- Non-vacuity of `transfer_to_capture_input`: the exact verifier for `semV os`,
`capFC`, `p = pRet`, `q = qRet`, spec `ubFree`. -/
theorem transfer_to_capture_input_nonvacuous (os : OpaqueSem) :
    VerifierSound (semV os) (exactVerifier (semV os)) ∧ OverApproxOnOk semS (semV os) capFC ∧
    capFC pRet = .ok qRet ∧ exactVerifier (semV os) qRet ubFree :=
  ⟨hV_exact _, hcap_FC _, rfl, qRet_ubFree _⟩

/-- Non-vacuity of `transfer_single_pass` with an `erasing` pass whose
precondition holds: `passPM` at `pOk` (whose place mention is valid), `q = qOk`. -/
theorem transfer_single_pass_nonvacuous (os : OpaqueSem) :
    VerifierSound (semV os) (exactVerifier (semV os)) ∧ OverApproxOnOk semS (semV os) capFC ∧
    EquivTagSound semS passPM ∧
    (passPM.tag = .erasing → LosesNoBehaviourAt semS passPM.run pOk) ∧
    capFC (passPM.run pOk) = .ok qOk ∧ exactVerifier (semV os) qOk ubFree :=
  ⟨hV_exact _, hcap_FC _, equivTagSound_erasing _, fun _ => losesNoBehaviourAt_example_pos,
    rfl, qOk_ubFree _⟩

/-- Non-vacuity of `transfer_relative_to_erasingSet` with a non-empty erasing set
and a non-trivial `equiv` pass: `pipeOk` at `pOk`, `q = qOk`. -/
theorem transfer_relative_to_erasingSet_nonvacuous (os : OpaqueSem) :
    VerifierSound (semV os) (exactVerifier (semV os)) ∧ OverApproxOnOk semS (semV os) capFC ∧
    (∀ P ∈ pipeOk, EquivTagSound semS P) ∧ ErasingSetPrecondition semS pipeOk pOk ∧
    InErasingSet pipeOk 0 ∧
    capFC (runPipe pipeOk pOk) = .ok qOk ∧ exactVerifier (semV os) qOk ubFree :=
  ⟨hV_exact _, hcap_FC _, pipeOk_equivTagSound, erasingSetPrecondition_example_pos,
    ⟨by decide, rfl⟩, rfl, qOk_ubFree _⟩

/-- Non-vacuity of `transfer_of_losesNoBehaviourAtInputs`: `pipeOk` at `pOk`. -/
theorem transfer_of_losesNoBehaviourAtInputs_nonvacuous (os : OpaqueSem) :
    VerifierSound (semV os) (exactVerifier (semV os)) ∧ OverApproxOnOk semS (semV os) capFC ∧
    LosesNoBehaviourAtInputs semS pipeOk pOk ∧
    capFC (runPipe pipeOk pOk) = .ok qOk ∧ exactVerifier (semV os) qOk ubFree :=
  ⟨hV_exact _, hcap_FC _, losesNoBehaviourAtInputs_example_pos, rfl, qOk_ubFree _⟩

/-! ## Merged pairs -/

/-- `pCl` captured by `capFC` (cleanup marks kept). -/
def qCl : VProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩,
    ⟨[], .call true 3 .continueUnwind, true⟩, ⟨[], .resume, true⟩]⟩

/-- Non-vacuity of `no_semV_faithful_at_merged_pair` (the cleanup-mark instance),
and its conclusion for that instance. -/
theorem cleanupMark_no_faithful_semV :
    (capNoCleanup pCl = .ok qUnw ∧ capNoCleanup pNo = .ok qUnw ∧
      ¬ DenEquiv (semS pCl) (semS pNo)) ∧
    ∀ semV' : VProg → Den Run,
      ¬ (FaithfulAt semS semV' capNoCleanup pCl ∧ FaithfulAt semS semV' capNoCleanup pNo) :=
  ⟨cleanupMark_merged_pair,
    no_semV_faithful_at_merged_pair semS capNoCleanup rfl rfl denEquiv_example_neg⟩

/-- The terminate-reason instance of `no_semV_faithful_at_merged_pair`. -/
theorem terminateReason_no_faithful_semV :
    ∀ semV' : VProg → Den Run,
      ¬ (FaithfulAt semS semV' capNoReason (pTerm .abi) ∧
        FaithfulAt semS semV' capNoReason (pTerm .inCleanup)) :=
  no_semV_faithful_at_merged_pair semS capNoReason (capNoReason_pTerm _) (capNoReason_pTerm _)
    terminateReason_merged_pair.2.2

/-- **Positive control for `no_semV_faithful_at_merged_pair` (and tightness of
`hdiff`).** `capFC` maps `pDrop true` and `pDrop false` (which differ in nothing but the
drop replace flag) to the same `qDrop`; the two programs have the same runs; and
`semV os` makes `capFC` faithful at both. -/
theorem dropReplace_merged_yet_faithful (os : OpaqueSem) :
    capFC (pDrop true) = .ok qDrop ∧ capFC (pDrop false) = .ok qDrop ∧
    DenEquiv (semS (pDrop true)) (semS (pDrop false)) ∧
    FaithfulAt semS (semV os) capFC (pDrop true) ∧
    FaithfulAt semS (semV os) capFC (pDrop false) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro ⟨x, b⟩
    simp only [semS, runS_pDrop]
  · exact (faithfulOnOk_iff_forall_faithfulAt _ _ _).1 (capFC_faithfulOnOk os) _
  · exact (faithfulOnOk_iff_forall_faithfulAt _ _ _).1 (capFC_faithfulOnOk os) _

/-- Tightness of the merge hypotheses `h₁`, `h₂` of
`no_semV_faithful_at_merged_pair`: `capFC` maps `pCl` to `qCl` and `pNo` to
`qUnw` (`qCl ≠ qUnw`); `pCl` and `pNo` have different runs; and `semV os` makes
`capFC` faithful at both. With `q = qCl`, `h₁` and `hdiff` hold and `h₂` fails;
with `q = qUnw`, `h₂` and `hdiff` hold and `h₁` fails; the conclusion fails in
both cases. -/
theorem merge_hypotheses_tight (os : OpaqueSem) :
    capFC pCl = .ok qCl ∧ capFC pNo = .ok qUnw ∧ qCl ≠ qUnw ∧
    ¬ DenEquiv (semS pCl) (semS pNo) ∧
    FaithfulAt semS (semV os) capFC pCl ∧ FaithfulAt semS (semV os) capFC pNo :=
  ⟨rfl, rfl, by decide, denEquiv_example_neg,
    (faithfulOnOk_iff_forall_faithfulAt _ _ _).1 (capFC_faithfulOnOk os) _,
    (faithfulOnOk_iff_forall_faithfulAt _ _ _).1 (capFC_faithfulOnOk os) _⟩

/-- Witnesses for `exists_faithful_semV_iff_merges_only_equivalent`: both sides
hold for `capFC`, and both sides fail for `capNoCleanup`. -/
theorem exists_faithful_semV_witnesses :
    (∃ semV' : VProg → Den Run, FaithfulOnOk semS semV' capFC) ∧
    (∀ p₁ p₂ q, capFC p₁ = .ok q → capFC p₂ = .ok q → DenEquiv (semS p₁) (semS p₂)) ∧
    ¬ (∃ semV' : VProg → Den Run, FaithfulOnOk semS semV' capNoCleanup) ∧
    ¬ (∀ p₁ p₂ q, capNoCleanup p₁ = .ok q → capNoCleanup p₂ = .ok q →
        DenEquiv (semS p₁) (semS p₂)) := by
  have h1 : ∃ semV' : VProg → Den Run, FaithfulOnOk semS semV' capFC :=
    ⟨semV .noop, capFC_faithfulOnOk .noop⟩
  have h3 : ¬ ∀ p₁ p₂ q, capNoCleanup p₁ = .ok q → capNoCleanup p₂ = .ok q →
      DenEquiv (semS p₁) (semS p₂) :=
    fun h => denEquiv_example_neg (h pCl pNo qUnw rfl rfl)
  exact ⟨h1, (exists_faithful_semV_iff_merges_only_equivalent semS capFC).1 h1,
    fun h => h3 ((exists_faithful_semV_iff_merges_only_equivalent semS capNoCleanup).1 h), h3⟩

/-! ## Witnesses for transfer soundness and faithfulness -/

/-- The stringify capture under `havoc` is not faithful (at `pAsm`). -/
theorem capStringify_havoc_not_faithful : ¬ FaithfulOnOk semS (semV .havoc) capStringify := by
  intro h
  have := (h pAsm qAsm capStringify_pAsm (0, ⟨[], .ub⟩)).1 trivial
  exact absurd this (by decide)

/-- Witnesses for `transferSound_all_sound_verifiers_iff_overApproxOnOk`: both
sides hold for `capFC`; both sides fail for `capDefault`; both sides hold for
`capStringify` under `havoc`, which is not faithful. -/
theorem transferSound_iff_witnesses :
    (∀ verified, VerifierSound (semV .noop) verified → TransferSound semS capFC verified) ∧
    ¬ (∀ verified, VerifierSound (semV .noop) verified → TransferSound semS capDefault verified) ∧
    ¬ OverApproxOnOk semS (semV .noop) capDefault ∧
    (∀ verified, VerifierSound (semV .havoc) verified →
      TransferSound semS capStringify verified) ∧
    ¬ FaithfulOnOk semS (semV .havoc) capStringify :=
  ⟨(transferSound_all_sound_verifiers_iff_overApproxOnOk _ _ _).2 (hcap_FC _),
    fun h => cex_hcap_default.2.2.2.2.2.1
      ((transferSound_all_sound_verifiers_iff_overApproxOnOk _ _ _).1 h),
    cex_hcap_default.2.2.2.2.2.1,
    (transferSound_all_sound_verifiers_iff_overApproxOnOk _ _ _).2
      capStringify_overApproxOnOk_havoc,
    capStringify_havoc_not_faithful⟩

/-- Every program in the ok-image of `capFC` has a deterministic verifier
denotation. -/
theorem capFC_image_det (os : OpaqueSem) :
    ∀ p q, capFC p = .ok q → Det (semV os q) := by
  intro p q h x o o' h₁ h₂
  have e₁ := ((capFC_faithfulOnOk os) p q h (x, o)).1 h₁
  have e₂ := ((capFC_faithfulOnOk os) p q h (x, o')).1 h₂
  exact semS_det p x o o' e₁ e₂

/-- Non-vacuity of `faithfulOnOk_iff_overApproxOnOk_of_total_of_det`: `capFC`. -/
theorem faithful_iff_overApprox_nonvacuous (os : OpaqueSem) :
    (∀ p q, capFC p = .ok q → Total (semS p)) ∧ (∀ p q, capFC p = .ok q → Det (semV os q)) :=
  ⟨fun p _ _ => semS_total p, capFC_image_det os⟩

/-- Tightness of `hdet`: `capStringify` under `havoc` has total sources and
over-approximates, but is not faithful (`qAsm` is not deterministic). -/
theorem cex_faithful_iff_hdet :
    (∀ p q, capStringify p = .ok q → Total (semS p)) ∧
    ¬ (∀ p q, capStringify p = .ok q → Det (semV .havoc q)) ∧
    OverApproxOnOk semS (semV .havoc) capStringify ∧
    ¬ FaithfulOnOk semS (semV .havoc) capStringify :=
  ⟨fun p _ _ => semS_total p, fun h => det_example_neg (h pAsm qAsm capStringify_pAsm),
    capStringify_overApproxOnOk_havoc, capStringify_havoc_not_faithful⟩

/-- Tightness of `htot`: an empty source denotation with a deterministic target
over-approximates (vacuously) but is not faithful. -/
theorem cex_faithful_iff_htot :
    let semS' : Unit → Den (Unit × Bool) := fun _ _ => False
    let semV' : Unit → Den (Unit × Bool) := fun _ r => r.2 = true
    let cap' : Unit → Except Unit Unit := fun _ => .ok ()
    ¬ (∀ p q, cap' p = .ok q → Total (semS' p)) ∧
    (∀ p q, cap' p = .ok q → Det (semV' q)) ∧
    OverApproxOnOk semS' semV' cap' ∧ ¬ FaithfulOnOk semS' semV' cap' := by
  refine ⟨fun h => total_example_neg (h () () rfl), ?_, fun _ _ _ _ h => h.elim, ?_⟩
  · intro _ _ _ _ o o' h₁ h₂
    exact h₁.trans h₂.symm
  · intro h
    exact (h () () rfl ((), true)).1 rfl

/-- Non-vacuity of `failClosed_overApproxOnOk_iff` and
`failOpen_overApproxOnOk_iff`: on `Nat` with identity semantics, fragment `{0}`,
`tr = id` and fallback `fun _ => 0`, the fail-closed capture over-approximates,
and the fail-open capture does not (program `1` is mapped to `0`). -/
theorem failClosed_failOpen_witnesses :
    let semN : Nat → Den Nat := fun p r => r = p
    OverApproxOnOk semN semN (failClosed (· = 0) id ()) ∧
    ¬ OverApproxOnOk semN semN (failOpen (E := Unit) (· = 0) id (fun _ => 0)) := by
  refine ⟨?_, ?_⟩
  · refine (failClosed_overApproxOnOk_iff _ _ _ _ _).2 ?_
    intro p _ b hb
    exact hb
  · intro h
    have := ((failOpen_overApproxOnOk_iff _ _ _ _ _).1 h).2 1 (by decide) 1 rfl
    exact absurd this (by decide)

/-- `failOpen` with a fallback that over-approximates: on `Nat` with identity source
semantics, fragment `{0}`, `tr = some` and the fallback `none`, which admits every
run, the fail-open capture over-approximates on its ok-image. -/
theorem failOpen_overApproxOnOk_example_pos :
    let semS' : Nat → Den Nat := fun p r => r = p
    let semV' : Option Nat → Den Nat := fun q r => match q with | some n => r = n | none => True
    OverApproxOnOk semS' semV' (failOpen (E := Unit) (· = 0) some (fun _ => none)) := by
  refine (failOpen_overApproxOnOk_iff _ _ _ _ _).2 ⟨?_, ?_⟩
  · intro p _ b hb
    exact hb
  · intro _ _ _ _
    trivial

/-- The fail-closed capture on the empty fragment rejects every program and
over-approximates on its (empty) ok-image. -/
theorem failClosed_empty_fragment {S V E B : Type} (semS : S → Den B) (semV : V → Den B)
    (tr : S → V) (e : E) :
    (∀ p, failClosed (fun _ : S => False) tr e p = .error e) ∧
    OverApproxOnOk semS semV (failClosed (fun _ : S => False) tr e) := by
  refine ⟨fun p => by simp [failClosed], ?_⟩
  intro p q h
  simp [failClosed] at h

/-- Tightness of the capture premise of `capFC_runV_eq_runS`: `qRet` is not the
capture of `pPM`, and on input `0` with fuel `2` the verifier run of `qRet` is not the
source run of `pPM`. -/
theorem cex_capFC_runV_h :
    capFC pPM ≠ .ok qRet ∧ runV .noop qRet 2 0 (St.init 0) ≠ .det (runS pPM 2 0 (St.init 0)) := by
  decide

/-! ## Refuted shape claims -/

/-- **Refuted: `capFC` has the shape `failClosed M tr e`.** No fragment `M`,
translation `tr` and single error `e` give `failClosed M tr e = capFC`: `capFC`
returns different errors on `pTrap` and `pAsm`. -/
theorem refuted_capFC_has_failClosed_shape :
    ¬ ∃ (M : SProg → Prop) (inst : DecidablePred M) (tr : SProg → VProg) (e : CapErr),
      @failClosed SProg VProg CapErr M inst tr e = capFC := by
  rintro ⟨M, inst, tr, e, h⟩
  have hTrap := congrFun h pTrap
  have hAsm := congrFun h pAsm
  rw [capFC_pTrap] at hTrap
  rw [capFC_pAsm] at hAsm
  unfold failClosed at hTrap hAsm
  by_cases hpT : M pTrap <;> by_cases hpA : M pAsm <;> simp [hpT, hpA] at hTrap hAsm
  rw [hTrap] at hAsm
  cases hAsm

/-- **Refuted: the fail-open variants have the shape `failOpen M tr fb`.** For each
of `capDefault`, `capStringify` and `capSwallow` there are no `M`, `tr`, `fb` with
`failOpen M tr fb` equal to it: `failOpen` never returns an error, and each variant
returns an error on some program (`pAsm` for `capDefault`, `pTrap` for the other
two). -/
theorem refuted_failOpenVariants_have_failOpen_shape :
    (¬ ∃ (M : SProg → Prop) (inst : DecidablePred M) (tr fb : SProg → VProg),
      @failOpen SProg VProg CapErr M inst tr fb = capDefault) ∧
    (¬ ∃ (M : SProg → Prop) (inst : DecidablePred M) (tr fb : SProg → VProg),
      @failOpen SProg VProg CapErr M inst tr fb = capStringify) ∧
    (¬ ∃ (M : SProg → Prop) (inst : DecidablePred M) (tr fb : SProg → VProg),
      @failOpen SProg VProg CapErr M inst tr fb = capSwallow) := by
  have hok : ∀ (M : SProg → Prop) (inst : DecidablePred M) (tr fb : SProg → VProg)
      (p : SProg), ∃ q, @failOpen SProg VProg CapErr M inst tr fb p = .ok q := by
    intro M inst tr fb p
    unfold failOpen
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨M, inst, tr, fb, h⟩
    obtain ⟨q, hq⟩ := hok M inst tr fb pAsm
    rw [h] at hq
    have : capDefault pAsm = .error .unmodeledStmt := rfl
    rw [this] at hq
    cases hq
  · rintro ⟨M, inst, tr, fb, h⟩
    obtain ⟨q, hq⟩ := hok M inst tr fb pTrap
    rw [h] at hq
    have : capStringify pTrap = .error .unmodeledTerm := rfl
    rw [this] at hq
    cases hq
  · rintro ⟨M, inst, tr, fb, h⟩
    obtain ⟨q, hq⟩ := hok M inst tr fb pTrap
    rw [h] at hq
    have : capSwallow pTrap = .error .unmodeledTerm := rfl
    rw [this] at hq
    cases hq

/-! ## The fixed fuel of the concrete semantics -/

/-- A loop on blocks `0`–`4` that runs its body twice and returns, followed by three
unreachable blocks. -/
def pLoopDead : SProg :=
  ⟨[ ⟨[.assign 1 (.const (.val 0)), .assign 2 (.const (.val 0))], .goto 1, false⟩,
     ⟨[], .switchInt (.copy 2) [2] 4, false⟩,
     ⟨[], .goto 3, false⟩,
     ⟨[.assign 2 (.copy 1), .assign 1 (.const (.val 1))], .goto 1, false⟩,
     ⟨[], .ret, false⟩,
     ⟨[], .ret, false⟩,
     ⟨[], .ret, false⟩,
     ⟨[], .ret, false⟩ ]⟩

/-- `pLoopDead` without its three unreachable blocks. -/
def pLoopTrim : SProg := ⟨pLoopDead.blocks.take 5⟩

/-- `pLoopTrim` with its exit block replaced by `unreachable`. -/
def pLoopUB : SProg :=
  ⟨(pLoopDead.blocks.take 4) ++ [⟨[], .unreachable, false⟩]⟩

/-- **The fixed fuel makes `semS` depend on unreachable blocks and hides UB beyond
the bound.** `pLoopTrim` agrees with `pLoopDead` on blocks `0`–`4` (the only blocks
reachable from block `0`); `pLoopDead` returns on every input while `pLoopTrim` runs
out of fuel on every input, so deleting unreachable blocks changes the denotation.
`pLoopUB` satisfies `ubFree` under `semS` (every run ends in `fuelOut`), although
with fuel `9` every run reaches `unreachable` (UB). -/
theorem fixedFuel_boundary :
    (∀ i < 5, pLoopTrim.blocks[i]? = pLoopDead.blocks[i]?) ∧
    (∀ x, runS pLoopDead pLoopDead.fuel 0 (St.init x) = ⟨[], .ret⟩) ∧
    (∀ x, runS pLoopTrim pLoopTrim.fuel 0 (St.init x) = ⟨[], .fuelOut⟩) ∧
    ¬ DenEquiv (semS pLoopTrim) (semS pLoopDead) ∧
    Sat (semS pLoopUB) ubFree ∧
    (∀ x, runS pLoopUB 9 0 (St.init x) = ⟨[], .ub⟩) := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, ?_, ?_, fun _ => rfl⟩
  · intro i hi
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
  · exact not_denEquiv_of_run (0, ⟨[], .fuelOut⟩) rfl (by decide)
  · exact sat_semS_of_run (fun _ => ⟨[], .fuelOut⟩) (fun _ => rfl) (fun _ => by simp [ubFree])

end Toy.Capture

namespace Toy.Capture

/-- The verdict relation that accepts nothing is sound (vacuously) and makes the
default capture transfer-sound, although the default capture does not
over-approximate. -/
theorem acceptNothing_control (os : OpaqueSem) :
    VerifierSound (semV os) (fun _ _ => False) ∧
    TransferSound semS capDefault (fun _ _ => False) ∧
    ¬ OverApproxOnOk semS (semV .noop) capDefault :=
  ⟨fun _ _ h => h.elim, transferSound_of_verifier_accepts_nothing _ _,
    cex_hcap_default.2.2.2.2.2.1⟩

end Toy.Capture
