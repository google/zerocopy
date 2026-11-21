import Toy.Capture.Sim

/-!
# Concrete programs, helpers, and definition examples

Every definition used in a main statement has at least one proved positive and one
proved negative example here.
-/

namespace Toy.Capture

/-! ## Programs -/

/-- Mentions the place `*x` (`x` = the input): UB iff `x = 0`, otherwise returns. -/
def pPM : SProg := ⟨[⟨[.placeMention 0], .ret, false⟩]⟩
/-- Zero-size read through `x`: UB iff `x = 0`, otherwise returns. -/
def pZst : SProg := ⟨[⟨[.zstRead 0], .ret, false⟩]⟩
/-- A switch whose only target and `otherwise` label are both block `1`, on the
uninitialized local `1`: UB on every input. -/
def pSw : SProg := ⟨[⟨[], .switchInt (.copy 1) [1] 1, false⟩, ⟨[], .ret, false⟩]⟩
/-- Returns immediately. -/
def pRet : SProg := ⟨[⟨[], .ret, false⟩]⟩
/-- Aborts through the unmodeled `trap` terminator. -/
def pTrap : SProg := ⟨[⟨[], .trap 1, false⟩, ⟨[], .ret, false⟩]⟩
/-- Outputs `7` through the unmodeled `asm` statement, then returns. -/
def pAsm : SProg := ⟨[⟨[.asm 7], .ret, false⟩]⟩
/-- Outputs an erroneous constant (its evaluation fails with `constErr`). -/
def pErr : SProg := ⟨[⟨[.emit (.const .err)], .ret, false⟩]⟩
/-- A panicking call unwinds to cleanup block `2`, which calls a panicking function
again. With the cleanup marks, the second panic aborts with reason `inCleanup`. -/
def pCl : SProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩,
    ⟨[], .call true 3 .continueUnwind, true⟩, ⟨[], .resume, true⟩]⟩
/-- `pCl` with blocks `2` and `3` marked normal: the second panic unwinds out. -/
def pNo : SProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩,
    ⟨[], .call true 3 .continueUnwind, false⟩, ⟨[], .resume, false⟩]⟩
/-- A panicking call unwinds to cleanup block `2`, which terminates with reason
`r`. -/
def pTerm (r : Reason) : SProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩, ⟨[], .terminate r, true⟩]⟩
/-- Drops the input local with replace flag `rep`, then returns. -/
def pDrop (rep : Bool) : SProg := ⟨[⟨[], .drop rep 0 1, false⟩, ⟨[], .ret, false⟩]⟩
/-- Mentions `*l` for a local `l` holding `5` (a valid place), drops it with the
replace flag set, then returns: no UB on any input. -/
def pOk : SProg :=
  ⟨[⟨[.assign 1 (.const (.val 5)), .placeMention 1], .drop true 1 1, false⟩,
    ⟨[], .ret, false⟩]⟩
/-- A switch on an erroneous constant whose only target and `otherwise` label are
both block `1`: it ends in `constErr` on every input. -/
def pSwConstErr : SProg := ⟨[⟨[], .switchInt (.const .err) [1] 1, false⟩, ⟨[], .ret, false⟩]⟩

/-- Verifier programs. -/
def qRet : VProg := ⟨[⟨[], .ret, false⟩]⟩
def qGoto : VProg := ⟨[⟨[], .goto 1, false⟩, ⟨[], .ret, false⟩]⟩
def qPM : VProg := ⟨[⟨[.placeMention 0], .ret, false⟩]⟩
def qAsm : VProg := ⟨[⟨[.opaque 7], .ret, false⟩]⟩
def qZero : VProg := ⟨[⟨[.emit (.const 0)], .ret, false⟩]⟩
def qUnw : VProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩,
    ⟨[], .call true 3 .continueUnwind, false⟩, ⟨[], .resume, false⟩]⟩
def qTermAbi : VProg :=
  ⟨[⟨[], .call true 1 (.cleanup 2), false⟩, ⟨[], .ret, false⟩, ⟨[], .terminate .abi, true⟩]⟩
def qDrop : VProg := ⟨[⟨[], .drop 0 1, false⟩, ⟨[], .ret, false⟩]⟩
def qOk : VProg :=
  ⟨[⟨[.assign 1 (.const 5)], .drop 1 1, false⟩, ⟨[], .ret, false⟩]⟩

/-- A verdict relation that accepts everything (unsound). -/
def trustAll : VProg → (Run → Prop) → Prop := fun _ _ => True

/-! ## Helpers -/

theorem sat_semV_of_run {os : OpaqueSem} {q : VProg} {spec : Run → Prop} (b₀ : Nat → Beh)
    (h : ∀ x, runV os q q.fuel 0 (St.init x) = .det (b₀ x)) (hs : ∀ x, spec (x, b₀ x)) :
    Sat (semV os q) spec := by
  intro ⟨x, b⟩ hb
  simp only [semV, h, VRes.admits] at hb
  subst hb
  exact hs x

theorem sat_semS_of_run {p : SProg} {spec : Run → Prop} (b₀ : Nat → Beh)
    (h : ∀ x, runS p p.fuel 0 (St.init x) = b₀ x) (hs : ∀ x, spec (x, b₀ x)) :
    Sat (semS p) spec := by
  intro ⟨x, b⟩ hb
  simp only [semS, h] at hb
  subst hb
  exact hs x

theorem not_sat_semS_of_run {p : SProg} {spec : Run → Prop} (x : Nat) (b : Beh)
    (h : runS p p.fuel 0 (St.init x) = b) (hs : ¬ spec (x, b)) : ¬ Sat (semS p) spec :=
  fun hS => hs (hS (x, b) h)

theorem not_sat_semV_of_run {os : OpaqueSem} {q : VProg} {spec : Run → Prop} (x : Nat)
    (b : Beh) (h : runV os q q.fuel 0 (St.init x) = .det b) (hs : ¬ spec (x, b)) :
    ¬ Sat (semV os q) spec :=
  fun hS => hs (hS (x, b) (by simp [semV, h, VRes.admits]))

theorem not_denEquiv_of_run {d₁ d₂ : Den Run} (r : Run) (h₁ : d₁ r) (h₂ : ¬ d₂ r) :
    ¬ DenEquiv d₁ d₂ :=
  fun h => h₂ ((h r).1 h₁)

/-! ## Runs of the concrete programs -/

theorem runS_pPM (x : Nat) :
    runS pPM pPM.fuel 0 (St.init x) = if x = 0 then ⟨[], .ub⟩ else ⟨[], .ret⟩ := by
  cases x <;> rfl

theorem runS_pZst (x : Nat) :
    runS pZst pZst.fuel 0 (St.init x) = if x = 0 then ⟨[], .ub⟩ else ⟨[], .ret⟩ := by
  cases x <;> rfl

theorem runS_pSw (x : Nat) : runS pSw pSw.fuel 0 (St.init x) = ⟨[], .ub⟩ := rfl
theorem runS_pRet (x : Nat) : runS pRet pRet.fuel 0 (St.init x) = ⟨[], .ret⟩ := rfl
theorem runS_pTrap (x : Nat) : runS pTrap pTrap.fuel 0 (St.init x) = ⟨[], .trap⟩ := rfl
theorem runS_pAsm (x : Nat) : runS pAsm pAsm.fuel 0 (St.init x) = ⟨[7], .ret⟩ := rfl
theorem runS_pErr (x : Nat) : runS pErr pErr.fuel 0 (St.init x) = ⟨[], .constErr⟩ := rfl
theorem runS_pCl (x : Nat) :
    runS pCl pCl.fuel 0 (St.init x) = ⟨[], .abort .inCleanup⟩ := rfl
theorem runS_pNo (x : Nat) : runS pNo pNo.fuel 0 (St.init x) = ⟨[], .unwind⟩ := rfl
theorem runS_pTerm (r : Reason) (x : Nat) :
    runS (pTerm r) (pTerm r).fuel 0 (St.init x) = ⟨[], .abort r⟩ := rfl
theorem runS_pDrop (rep : Bool) (x : Nat) :
    runS (pDrop rep) (pDrop rep).fuel 0 (St.init x) = ⟨[], .ret⟩ := rfl
theorem runS_pOk (x : Nat) : runS pOk pOk.fuel 0 (St.init x) = ⟨[], .ret⟩ := rfl

theorem runV_qRet (os : OpaqueSem) (x : Nat) :
    runV os qRet qRet.fuel 0 (St.init x) = .det ⟨[], .ret⟩ := rfl
theorem runV_qGoto (os : OpaqueSem) (x : Nat) :
    runV os qGoto qGoto.fuel 0 (St.init x) = .det ⟨[], .ret⟩ := rfl
theorem runV_qPM (os : OpaqueSem) (x : Nat) :
    runV os qPM qPM.fuel 0 (St.init x) = .det (if x = 0 then ⟨[], .ub⟩ else ⟨[], .ret⟩) := by
  cases x <;> rfl
theorem runV_qAsm_noop (x : Nat) :
    runV .noop qAsm qAsm.fuel 0 (St.init x) = .det ⟨[], .ret⟩ := rfl
theorem runV_qAsm_havoc (x : Nat) : runV .havoc qAsm qAsm.fuel 0 (St.init x) = .top := rfl
theorem runV_qZero (os : OpaqueSem) (x : Nat) :
    runV os qZero qZero.fuel 0 (St.init x) = .det ⟨[0], .ret⟩ := rfl
theorem runV_qUnw (os : OpaqueSem) (x : Nat) :
    runV os qUnw qUnw.fuel 0 (St.init x) = .det ⟨[], .unwind⟩ := rfl
theorem runV_qTermAbi (os : OpaqueSem) (x : Nat) :
    runV os qTermAbi qTermAbi.fuel 0 (St.init x) = .det ⟨[], .abort .abi⟩ := rfl
theorem runV_qOk (os : OpaqueSem) (x : Nat) :
    runV os qOk qOk.fuel 0 (St.init x) = .det ⟨[], .ret⟩ := rfl

/-! ## Captures and passes on the concrete programs -/

theorem capFC_pPM : capFC pPM = .ok qPM := rfl
theorem capFC_erasePlaceMentions_pPM : capFC (erasePlaceMentions pPM) = .ok qRet := rfl
theorem capFC_eraseZstReads_pZst : capFC (eraseZstReads pZst) = .ok qRet := rfl
theorem capFC_simplifyTrivialSwitches_pSw : capFC (simplifyTrivialSwitches pSw) = .ok qGoto :=
  rfl
theorem capFC_pRet : capFC pRet = .ok qRet := rfl
theorem capFC_pTrap : capFC pTrap = .error .unmodeledTerm := rfl
theorem capFC_pAsm : capFC pAsm = .error .unmodeledStmt := rfl
theorem capFC_pErr : capFC pErr = .error .erroneousConst := rfl
theorem capDefault_pTrap : capDefault pTrap = .ok qGoto := rfl
theorem capStringify_pAsm : capStringify pAsm = .ok qAsm := rfl
theorem capSwallow_pErr : capSwallow pErr = .ok qZero := rfl
theorem capNoCleanup_pCl : capNoCleanup pCl = .ok qUnw := rfl
theorem capNoCleanup_pNo : capNoCleanup pNo = .ok qUnw := rfl
theorem capNoReason_pTerm (r : Reason) : capNoReason (pTerm r) = .ok qTermAbi := by
  cases r <;> rfl
theorem capFC_pDrop (rep : Bool) : capFC (pDrop rep) = .ok qDrop := by cases rep <;> rfl
theorem capFC_pOk_pipeline : capFC (clearReplace (erasePlaceMentions pOk)) = .ok qOk := rfl
theorem capFC_pCl_ne_pNo : capFC pCl ≠ capFC pNo := by decide
theorem capFC_pTerm_abi_ne_inCleanup : capFC (pTerm .abi) ≠ capFC (pTerm .inCleanup) := by
  decide

/-! ## Definition examples -/

/-- `Sat`, positive: `pRet` is UB-free. -/
theorem sat_example_pos : Sat (semS pRet) ubFree :=
  sat_semS_of_run (fun _ => ⟨[], .ret⟩) runS_pRet (fun _ => by simp [ubFree])
/-- `Sat`, negative: `pPM` is not UB-free (input `0`). -/
theorem sat_example_neg : ¬ Sat (semS pPM) ubFree :=
  not_sat_semS_of_run 0 ⟨[], .ub⟩ rfl (by decide)

/-- `DenIncl`, positive: every run of `pAsm` is admitted by `qAsm` under `havoc`. -/
theorem denIncl_example_pos : DenIncl (semS pAsm) (semV .havoc qAsm) := by
  intro ⟨x, b⟩ _
  simp [semV, runV_qAsm_havoc, VRes.admits]
/-- `DenIncl`, negative: `qAsm` under `havoc` admits runs that `pAsm` lacks. -/
theorem denIncl_example_neg : ¬ DenIncl (semV .havoc qAsm) (semS pAsm) := by
  intro h
  have := h (0, ⟨[], .ub⟩) (by simp [semV, runV_qAsm_havoc, VRes.admits])
  exact absurd this (by decide)

/-- `DenEquiv`, positive: clearing the replace flag of `pDrop true`. -/
theorem denEquiv_example_pos : DenEquiv (semS (clearReplace (pDrop true))) (semS (pDrop true)) :=
  clearReplace_denEquiv _
/-- `DenEquiv`, negative: `pCl` and `pNo` differ on input `0`. -/
theorem denEquiv_example_neg : ¬ DenEquiv (semS pCl) (semS pNo) :=
  not_denEquiv_of_run (0, ⟨[], .abort .inCleanup⟩) rfl (by decide)

/-- `FaithfulAt`, positive: the fail-closed capture at `pCl`. -/
theorem faithfulAt_example_pos (os : OpaqueSem) : FaithfulAt semS (semV os) capFC pCl :=
  (faithfulOnOk_iff_forall_faithfulAt _ _ _).1 (capFC_faithfulOnOk os) pCl
/-- `FaithfulAt`, negative: the cleanup-dropping capture at `pCl`. -/
theorem faithfulAt_example_neg (os : OpaqueSem) : ¬ FaithfulAt semS (semV os) capNoCleanup pCl := by
  intro h
  have := (h qUnw capNoCleanup_pCl (0, ⟨[], .abort .inCleanup⟩)).2 rfl
  simp [semV, runV_qUnw, VRes.admits] at this

/-- `FaithfulOnOk`, positive: `capFC` (proved in general, `capFC_faithfulOnOk`). -/
theorem faithfulOnOk_example_pos (os : OpaqueSem) : FaithfulOnOk semS (semV os) capFC :=
  capFC_faithfulOnOk os
/-- `FaithfulOnOk`, negative: the default capture is not faithful (at `pTrap`). -/
theorem faithfulOnOk_example_neg (os : OpaqueSem) : ¬ FaithfulOnOk semS (semV os) capDefault := by
  intro h
  have := (h pTrap qGoto capDefault_pTrap (0, ⟨[], .trap⟩)).2 rfl
  simp [semV, runV_qGoto, VRes.admits] at this

/-- `OverApproxOnOk`, positive: stringify under `havoc`. -/
theorem overApproxOnOk_example_pos : OverApproxOnOk semS (semV .havoc) capStringify :=
  capStringify_overApproxOnOk_havoc
/-- `OverApproxOnOk`, negative: stringify under `noop` (at `pAsm`). -/
theorem overApproxOnOk_example_neg : ¬ OverApproxOnOk semS (semV .noop) capStringify := by
  intro h
  have := h pAsm qAsm capStringify_pAsm (0, ⟨[7], .ret⟩) rfl
  simp [semV, runV_qAsm_noop, VRes.admits] at this

/-- `VerifierSound`, positive: the exact verifier. -/
theorem verifierSound_example_pos (os : OpaqueSem) :
    VerifierSound (semV os) (exactVerifier (semV os)) :=
  exactVerifier_sound _
/-- `VerifierSound`, negative: `trustAll` (it accepts `ubFree` for `qPM`). -/
theorem verifierSound_example_neg (os : OpaqueSem) : ¬ VerifierSound (semV os) trustAll := by
  intro h
  exact not_sat_semV_of_run 0 ⟨[], .ub⟩ (runV_qPM os 0) (by decide) (h qPM ubFree trivial)

/-- `TransferSound`, positive: `capFC` with the exact verifier. -/
theorem transferSound_example_pos (os : OpaqueSem) :
    TransferSound semS capFC (exactVerifier (semV os)) :=
  (transferSound_exactVerifier_iff_overApproxOnOk _ _ _).2 (capFC_faithfulOnOk os).overApproxOnOk
/-- `TransferSound`, negative: `capDefault` with the exact verifier. -/
theorem transferSound_example_neg (os : OpaqueSem) :
    ¬ TransferSound semS capDefault (exactVerifier (semV os)) := by
  intro h
  have := h pTrap qGoto returnsNormally capDefault_pTrap
    (sat_semV_of_run (fun _ => ⟨[], .ret⟩) (runV_qGoto os) (fun _ => rfl))
  exact not_sat_semS_of_run 0 _ (runS_pTrap 0) (by decide) this

/-- `EquivTagSound`, positive: `clearReplace` tagged `equiv`. -/
theorem equivTagSound_example_pos : EquivTagSound semS ⟨.equiv, clearReplace⟩ :=
  fun _ p => clearReplace_denEquiv p
/-- `EquivTagSound`, negative: `erasePlaceMentions` tagged `equiv`. -/
theorem equivTagSound_example_neg : ¬ EquivTagSound semS ⟨.equiv, erasePlaceMentions⟩ := by
  intro h
  have := (h rfl pPM (0, ⟨[], .ub⟩)).2 rfl
  exact absurd this (by decide)
/-- `EquivTagSound` is vacuous for `erasing`-tagged passes. -/
theorem equivTagSound_erasing (f : SProg → SProg) : EquivTagSound semS ⟨.erasing, f⟩ :=
  fun h => by cases h

/-- `LosesNoBehaviourAt`, positive: erasing the valid place mention of `pOk`. -/
theorem losesNoBehaviourAt_example_pos : LosesNoBehaviourAt semS erasePlaceMentions pOk := by
  intro ⟨x, b⟩ hb
  simp only [semS, runS_pOk] at hb
  subst hb
  rfl
/-- `LosesNoBehaviourAt`, negative: erasing the place mention of `pPM` loses the UB
run on input `0`. -/
theorem losesNoBehaviourAt_example_neg : ¬ LosesNoBehaviourAt semS erasePlaceMentions pPM := by
  intro h
  have := h (0, ⟨[], .ub⟩) rfl
  exact absurd this (by decide)

/-- One `erasing` pass that removes place mentions. -/
def pipePM : List (Pass SProg) := [⟨.erasing, erasePlaceMentions⟩]
/-- The pipeline used for non-vacuity: an `erasing` pass, then an `equiv` pass. -/
def pipeOk : List (Pass SProg) := [⟨.erasing, erasePlaceMentions⟩, ⟨.equiv, clearReplace⟩]

/-- `InErasingSet`, positive: index `0` of `pipePM`. -/
theorem inErasingSet_example_pos : InErasingSet pipePM 0 := ⟨by decide, rfl⟩
/-- `InErasingSet`, negative: index `1` of `pipeOk` (an `equiv` pass) and index `1`
of `pipePM` (out of range). -/
theorem inErasingSet_example_neg : ¬ InErasingSet pipeOk 1 ∧ ¬ InErasingSet pipePM 1 := by
  constructor
  · rintro ⟨_, h⟩
    simp [pipeOk] at h
  · rintro ⟨h, _⟩
    simp [pipePM] at h

/-- `ErasingSetPrecondition`, positive: `pipeOk` at `pOk`. -/
theorem erasingSetPrecondition_example_pos : ErasingSetPrecondition semS pipeOk pOk := by
  intro i hi htag
  match i, hi, htag with
  | 0, _, _ => exact losesNoBehaviourAt_example_pos
  | 1, _, h => cases h
/-- `ErasingSetPrecondition`, negative: `pipePM` at `pPM`. -/
theorem erasingSetPrecondition_example_neg : ¬ ErasingSetPrecondition semS pipePM pPM :=
  fun h => losesNoBehaviourAt_example_neg (h 0 (by decide) rfl)

/-- `LosesNoBehaviourAtInputs`, positive: `pipeOk` at `pOk`. -/
theorem losesNoBehaviourAtInputs_example_pos : LosesNoBehaviourAtInputs semS pipeOk pOk :=
  losesNoBehaviourAtInputs_of_erasingSet semS pipeOk pOk
    (by
      intro P hP
      simp only [pipeOk, List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · exact equivTagSound_erasing _
      · exact equivTagSound_example_pos)
    erasingSetPrecondition_example_pos
/-- `LosesNoBehaviourAtInputs`, negative: `pipePM` at `pPM`. -/
theorem losesNoBehaviourAtInputs_example_neg : ¬ LosesNoBehaviourAtInputs semS pipePM pPM :=
  fun h => losesNoBehaviourAt_example_neg (h 0 (by decide))

/-- `runPipe` example: `pipeOk` on `pOk`. -/
theorem runPipe_example : runPipe pipeOk pOk = clearReplace (erasePlaceMentions pOk) := rfl

/-- `Total` and `Det`, positive: every source denotation is total and deterministic. -/
theorem semS_total (p : SProg) : Total (semS p) :=
  fun x => ⟨runS p p.fuel 0 (St.init x), rfl⟩
theorem semS_det (p : SProg) : Det (semS p) := fun _ _ _ h₁ h₂ => h₁.symm.trans h₂
/-- `Total`, negative: the empty denotation. -/
theorem total_example_neg : ¬ Total (fun _ : Unit × Bool => False) :=
  fun h => (h ()).elim fun _ h => h
/-- `Det`, negative: `qAsm` under `havoc` admits two behaviours on input `0`. -/
theorem det_example_neg : ¬ Det (semV .havoc qAsm) := by
  intro h
  have := h 0 ⟨[], .ret⟩ ⟨[], .ub⟩ (by simp [semV, runV_qAsm_havoc, VRes.admits])
    (by simp [semV, runV_qAsm_havoc, VRes.admits])
  exact absurd this (by decide)

/-- `failClosed` and `failOpen` examples on `Nat` with the fragment `{0}`. -/
theorem failClosed_example_pos : failClosed (· = 0) id () 0 = .ok 0 := rfl
theorem failClosed_example_neg : failClosed (· = 0) id () 1 = .error () := rfl
theorem failOpen_example : failOpen (E := Unit) (· = 0) id (fun _ => 0) 1 = .ok 0 := rfl

/-- `semS` and `semV` examples. -/
theorem semS_example_pos : semS pPM (0, ⟨[], .ub⟩) := rfl
theorem semS_example_neg : ¬ semS pPM (0, ⟨[], .ret⟩) := by decide
theorem semV_example_pos : semV .havoc qAsm (0, ⟨[], .ub⟩) := trivial
theorem semV_example_neg : ¬ semV .noop qAsm (0, ⟨[7], .ret⟩) := by decide

/-- A verifier program that outputs `42` and then reaches `opaque`. -/
def qEmitOpaque : VProg := ⟨[⟨[.emit (.const 42), .opaque 7], .ret, false⟩]⟩

/-- Under `havoc`, reaching `opaque` admits every behaviour for the input, including
one whose trace does not start with the `42` already output; under `noop` that
behaviour is not admitted. -/
theorem semV_havoc_admits_any_trace :
    semV .havoc qEmitOpaque (0, ⟨[], .ret⟩) ∧ ¬ semV .noop qEmitOpaque (0, ⟨[], .ret⟩) :=
  ⟨trivial, by decide⟩

/-- Specification examples. -/
theorem specs_example :
    ubFree (0, ⟨[], .ret⟩) ∧ ¬ ubFree (0, ⟨[], .ub⟩) ∧
    returnsNormally (0, ⟨[], .ret⟩) ∧ ¬ returnsNormally (0, ⟨[], .trap⟩) ∧
    silent (0, ⟨[], .ret⟩) ∧ ¬ silent (0, ⟨[7], .ret⟩) ∧
    noAbort (0, ⟨[], .unwind⟩) ∧ ¬ noAbort (0, ⟨[], .abort .inCleanup⟩) ∧
    noAbortInCleanup (0, ⟨[], .abort .abi⟩) ∧ ¬ noAbortInCleanup (0, ⟨[], .abort .inCleanup⟩) := by
  decide

/-- Pass examples: each erasing pass removes the construct; a switch on an
erroneous constant is kept; `clearReplace` clears the flag. -/
theorem passes_example :
    erasePlaceMentions pPM = pRet ∧ eraseZstReads pZst = pRet ∧
    simplifyTrivialSwitches pSw = ⟨[⟨[], .goto 1, false⟩, ⟨[], .ret, false⟩]⟩ ∧
    simplifyTrivialSwitches pSwConstErr = pSwConstErr ∧
    clearReplace (pDrop true) = pDrop false ∧
    simplifyTrivialSwitches pCl = pCl := by
  decide

end Toy.Capture
