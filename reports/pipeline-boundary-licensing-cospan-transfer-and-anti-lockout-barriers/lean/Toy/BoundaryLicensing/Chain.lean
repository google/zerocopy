import Toy.BoundaryLicensing.Transfer

set_option autoImplicit false

namespace Toy.BoundaryLicensing

/-! ## Uniform Semantic Chain Composition Iff & Operational TCB Warrant -/

/-- Multi-step semantic realization chain across `[rel₁, …, relₙ]` from `S₀` to `Sₙ`. -/
inductive RealizesChain : List BoundaryRel → Sys → Sys → Prop where
  | nil (S : Sys) : RealizesChain [] S S
  | cons {rel : BoundaryRel} {rels : List BoundaryRel} {S₀ S₁ Sₙ : Sys} :
      Realizes rel S₀ S₁ → RealizesChain rels S₁ Sₙ → RealizesChain (rel :: rels) S₀ Sₙ

/-- Folded directional transfer status across a finite boundary chain `rels`. -/
def transferChain (rels : List BoundaryRel) (sh : PosShape) (st₀ : Status) : Status :=
  rels.foldl (fun st rel => transfer rel sh st) st₀

/-- Operational TCB warrant gate collapsing any verdict to `.undetermined` when `warrantValid = false`. -/
def gateWarrant (warrantValid : Bool) (st : Status) : Status :=
  if warrantValid then st else .undetermined

/-- Warrant-gated chain transfer transformer. -/
def licensedTransfer (warrantValid : Bool) (rels : List BoundaryRel)
    (sh : PosShape) (st₀ : Status) : Status :=
  gateWarrant warrantValid (transferChain rels sh st₀)

/-- Conditional chain realization under operational TCB warrant `warrantValid`. -/
def RealizesUnderTCB (warrantValid : Bool) (rels : List BoundaryRel) (S₀ Sₙ : Sys) : Prop :=
  warrantValid = true → RealizesChain rels S₀ Sₙ

/-- Trace-determinism predicate (`HasTrace S` contains at most one valuation trace). -/
def TraceDeterministic (S : Sys) : Prop :=
  ∀ τ₁ τ₂, HasTrace S τ₁ → HasTrace S τ₂ → τ₁ = τ₂

/-! ### Chain Helper Lemmas -/

theorem realizesChain_refl (rels : List BoundaryRel) (S : Sys) :
    RealizesChain rels S S := by
  induction rels with
  | nil => exact .nil S
  | cons rel rest ih => exact .cons (realizes_refl rel S) ih

theorem realizesChain_append {r₁ r₂ : List BoundaryRel} {A B C : Sys}
    (h₁ : RealizesChain r₁ A B) (h₂ : RealizesChain r₂ B C) :
    RealizesChain (r₁ ++ r₂) A C := by
  induction h₁ with
  | nil _ => exact h₂
  | cons hrel _ ih => exact .cons hrel (ih h₂)

theorem transferChain_undetermined (rels : List BoundaryRel) (sh : PosShape) :
    transferChain rels sh .undetermined = .undetermined := by
  induction rels with
  | nil => rfl
  | cons rel rest ih =>
    simp only [transferChain, List.foldl_cons, transfer_undetermined]
    exact ih

theorem transferChain_sound (rels : List BoundaryRel) (sh : PosShape) (P : Spec)
    (S₀ Sₙ : Sys) (hchain : RealizesChain rels S₀ Sₙ) :
    (transferChain rels sh (statusOf S₀ sh P)).le (statusOf Sₙ sh P) := by
  induction hchain with
  | nil _ => exact status_le_refl _
  | @cons rel rest A B C hrel _ ih =>
    change (transferChain rest sh (transfer rel sh (statusOf A sh P))).le (statusOf C sh P)
    have h1 := transfer_sound rel sh P A B hrel
    rcases transfer_eq_self_or_undetermined rel sh (statusOf A sh P) with heq | hund
    · rw [heq] at h1 ⊢
      cases hA : statusOf A sh P with
      | undetermined =>
        exact False.elim (statusOf_ne_undetermined A sh P hA)
      | supported =>
        rw [hA] at h1
        have hB : statusOf B sh P = .supported := h1.symm
        rw [← hB]
        exact ih
      | contradicted =>
        rw [hA] at h1
        have hB : statusOf B sh P = .contradicted := h1.symm
        rw [← hB]
        exact ih
    · rw [hund, transferChain_undetermined]
      trivial

theorem split_at_first_undetermined (rels : List BoundaryRel) (sh : PosShape) (st₀ : Status)
    (hne : transferChain rels sh st₀ ≠ st₀) :
    ∃ (pre : List BoundaryRel) (rel : BoundaryRel) (suf : List BoundaryRel),
      rels = pre ++ rel :: suf ∧
      transferChain pre sh st₀ = st₀ ∧
      transfer rel sh st₀ = .undetermined := by
  induction rels with
  | nil => exact False.elim (hne rfl)
  | cons r rs ih =>
    rcases transfer_eq_self_or_undetermined r sh st₀ with heq | hund
    · simp only [transferChain, List.foldl_cons, heq] at hne
      obtain ⟨pre, rel, suf, hrs, hpre, hrel⟩ := ih hne
      refine ⟨r :: pre, rel, suf, by simp [hrs], ?_, hrel⟩
      simp only [transferChain, List.foldl_cons, heq]
      exact hpre
    · exact ⟨[], r, rs, rfl, rfl, hund⟩

theorem flip_ne_self_of_definite {st : Status} (hdef : st.Definite) : st.flip ≠ st := by
  rcases hdef with rfl | rfl <;> decide

/-! ### Uniform Semantic Chain Composition Characterization -/

/-- Uniform semantic chain composition: across any `n`-step chain `rels` on a non-degenerate
`(sh, P)`, `transferChain rels sh st₀ = st₀` iff every realization chain starting at `st₀` ends at `st₀`. -/
theorem transferChain_eq_iff_forall_realizesChain (rels : List BoundaryRel) (sh : PosShape)
    (P : Spec) (st₀ : Status) (hnd : NonDegen sh P) :
    transferChain rels sh st₀ = st₀ ↔
      ∀ S₀ Sₙ : Sys, RealizesChain rels S₀ Sₙ →
        statusOf S₀ sh P = st₀ → statusOf Sₙ sh P = st₀ := by
  constructor
  · intro heq S₀ Sₙ hchain hS₀
    cases st₀ with
    | undetermined =>
      exact False.elim (statusOf_ne_undetermined S₀ sh P hS₀)
    | supported =>
      have hle := transferChain_sound rels sh P S₀ Sₙ hchain
      rw [hS₀, heq] at hle
      exact hle.symm
    | contradicted =>
      have hle := transferChain_sound rels sh P S₀ Sₙ hchain
      rw [hS₀, heq] at hle
      exact hle.symm
  · intro hforall
    cases st₀ with
    | undetermined => exact transferChain_undetermined rels sh
    | supported =>
      refine Classical.byContradiction fun hne => ?_
      obtain ⟨pre, rel, suf, hsplit, _, hund⟩ :=
        split_at_first_undetermined rels sh .supported hne
      obtain ⟨src, tgt, hrel, hsrc, htgt⟩ :=
        exists_flip_realization rel sh P .supported hnd (Or.inl rfl) hund
      have hchain : RealizesChain rels src tgt := by
        rw [hsplit]
        exact realizesChain_append (realizesChain_refl pre src)
          (.cons hrel (realizesChain_refl suf tgt))
      have hend := hforall src tgt hchain hsrc
      rw [htgt] at hend
      cases hend
    | contradicted =>
      refine Classical.byContradiction fun hne => ?_
      obtain ⟨pre, rel, suf, hsplit, _, hund⟩ :=
        split_at_first_undetermined rels sh .contradicted hne
      obtain ⟨src, tgt, hrel, hsrc, htgt⟩ :=
        exists_flip_realization rel sh P .contradicted hnd (Or.inr rfl) hund
      have hchain : RealizesChain rels src tgt := by
        rw [hsplit]
        exact realizesChain_append (realizesChain_refl pre src)
          (.cons hrel (realizesChain_refl suf tgt))
      have hend := hforall src tgt hchain hsrc
      rw [htgt] at hend
      cases hend

/-- Tightness counterexample for `hnd : NonDegen sh P` in `transferChain_eq_iff_forall_realizesChain`:
on `specConstTrue`, every realization chain of `[.none]` ends at `.supported` while `transferChain = .undetermined`. -/
theorem cex_transferChain_iff_without_nonDegen :
    transferChain [.none] .univSafety .supported ≠ .supported ∧
    ∀ S₀ Sₙ : Sys, RealizesChain [.none] S₀ Sₙ →
      statusOf S₀ .univSafety specConstTrue = .supported →
      statusOf Sₙ .univSafety specConstTrue = .supported := by
  refine ⟨by decide, ?_⟩
  intro _ Sₙ _ _
  exact (statusOf_eq_supported_iff Sₙ .univSafety specConstTrue).2 (fun _ _ _ => rfl)

/-- Coincidental truth on a single concrete system chain never licenses an unlicensed chain:
`[.stutterSim .s2m, .lockStepSim .s2m]` preserves `.supported` on `(constSys valTrue)` for `.termination`,
yet `transferChain` returns `.undetermined` and a valid realization chain falsifies `.termination`. -/
theorem cex_coincidental_truth_on_unlicensed_chain :
    let rels : List BoundaryRel := [.stutterSim .s2m, .lockStepSim .s2m]
    RealizesChain rels (constSys valTrue) (constSys valTrue) ∧
    statusOf (constSys valTrue) .termination specAtom0 = .supported ∧
    transferChain rels .termination .supported = .undetermined ∧
    ∃ S₀ Sₙ : Sys, RealizesChain rels S₀ Sₙ ∧
      statusOf S₀ .termination specAtom0 = .supported ∧
      statusOf Sₙ .termination specAtom0 = .contradicted := by
  intro rels
  have hsup : statusOf (constSys valTrue) .termination specAtom0 = .supported :=
    (statusOf_eq_supported_iff _ _ _).2 (evalShape_constSys_valTrue specAtom0 rfl).2.2.1
  refine ⟨realizesChain_refl rels _, hsup, rfl, ?_⟩
  refine ⟨stepSys valFalse valTrue, constSys valFalse,
    .cons stutter_constFalse_to_step (.cons (realizes_refl _ _) (.nil _)), ?_, ?_⟩
  · exact (statusOf_eq_supported_iff _ _ _).2 (evalShape_stepSys_terminates specAtom0 rfl)
  · exact (statusOf_eq_contradicted_iff _ _ _).2 (evalShape_constSys_valFalse specAtom0 rfl).2.2.1

/-- Boundary witness showing that completeness of `transferChain` relies on unconstrained intermediate
systems `S₁ : Sys`: if an intermediate stage guarantees `TraceDeterministic S₁`, then a subsequent
`.traceRefine .s2m` link preserves `.existWitness` `.supported` even though
`transfer (.traceRefine .s2m) .existWitness .supported = .undetermined`. -/
theorem determinizing_stage_breaks_markovian_completeness :
    transfer (.traceRefine .s2m) .existWitness .supported = .undetermined ∧
    ∀ (S₀ S₁ S₂ : Sys) (P : Spec),
      (TraceIncl S₀ S₁ ∧ TraceDeterministic S₁) →
      Realizes (.traceRefine .s2m) S₁ S₂ →
      statusOf S₀ .existWitness P = .supported →
      statusOf S₂ .existWitness P = .supported := by
  refine ⟨rfl, ?_⟩
  intro S₀ S₁ S₂ P ⟨htr01, hdet1⟩ htr21 hsup0
  rw [statusOf_eq_supported_iff] at hsup0 ⊢
  rcases hsup0 with ⟨τ₀, hτ₀, n, hn⟩
  obtain ⟨τ₂, hτ₂⟩ := hasTrace_nonempty S₂
  have heq : τ₀ = τ₂ := hdet1 τ₀ τ₂ (htr01 τ₀ hτ₀) (htr21 τ₂ hτ₂)
  subst heq
  exact ⟨τ₀, hτ₂, n, hn⟩

/-! ### Operational TCB Warrant Gating -/

/-- Exact warrant-gated chain characterization: `licensedTransfer warrantValid rels sh st₀ = st₀`
iff every TCB-conditional realization `RealizesUnderTCB warrantValid rels S₀ Sₙ` preserves `st₀`. -/
theorem licensedTransfer_eq_iff_forall_realizesUnderTCB (warrantValid : Bool)
    (rels : List BoundaryRel) (sh : PosShape) (P : Spec) (st₀ : Status) (hnd : NonDegen sh P) :
    licensedTransfer warrantValid rels sh st₀ = st₀ ↔
      ∀ S₀ Sₙ : Sys, RealizesUnderTCB warrantValid rels S₀ Sₙ →
        statusOf S₀ sh P = st₀ → statusOf Sₙ sh P = st₀ := by
  cases warrantValid with
  | true =>
    simp only [licensedTransfer, gateWarrant, ↓reduceIte, RealizesUnderTCB, forall_const]
    exact transferChain_eq_iff_forall_realizesChain rels sh P st₀ hnd
  | false =>
    simp only [licensedTransfer, gateWarrant, Bool.false_eq_true, ↓reduceIte]
    cases st₀ with
    | undetermined =>
      refine ⟨fun _ S₀ _ _ hS₀ => False.elim (statusOf_ne_undetermined S₀ sh P hS₀), fun _ => rfl⟩
    | supported =>
      refine ⟨(fun h => by cases h), ?_⟩
      intro hforall
      rcases hnd with ⟨⟨S₁, h₁⟩, ⟨S₂, h₂⟩⟩
      have hbad := hforall S₁ S₂ (fun h => by cases h) h₁
      rw [h₂] at hbad
      cases hbad
    | contradicted =>
      refine ⟨(fun h => by cases h), ?_⟩
      intro hforall
      rcases hnd with ⟨⟨S₁, h₁⟩, ⟨S₂, h₂⟩⟩
      have hbad := hforall S₂ S₁ (fun h => by cases h) h₂
      rw [h₁] at hbad
      cases hbad

/-- Dedicated tightness counterexample for `hnd : NonDegen sh P` in
`licensedTransfer_eq_iff_forall_realizesUnderTCB` at `warrantValid = false`. -/
theorem cex_licensedTransfer_iff_without_nonDegen :
    licensedTransfer false [.certFaithfulSoundPinned] .univSafety .supported ≠ .supported ∧
    ∀ S₀ Sₙ : Sys, RealizesUnderTCB false [.certFaithfulSoundPinned] S₀ Sₙ →
      statusOf S₀ .univSafety specConstTrue = .supported →
      statusOf Sₙ .univSafety specConstTrue = .supported := by
  refine ⟨by decide, ?_⟩
  intro _ Sₙ _ _
  exact (statusOf_eq_supported_iff Sₙ .univSafety specConstTrue).2 (fun _ _ _ => rfl)

/-- When `warrantValid = false`, licensed transfer collapses to `.undetermined` for both `.supported`
and `.contradicted` claims, even across `[.certFaithfulSoundPinned, .termRoundTrip]`, and both verdicts
have TCB-conditional countermodels. -/
theorem unwarranted_collapses_both_statuses (rels : List BoundaryRel) (sh : PosShape)
    (P : Spec) (hnd : NonDegen sh P) :
    licensedTransfer false rels sh .supported = .undetermined ∧
    licensedTransfer false rels sh .contradicted = .undetermined ∧
    (∃ S₀ Sₙ : Sys, RealizesUnderTCB false rels S₀ Sₙ ∧
      statusOf S₀ sh P = .supported ∧ statusOf Sₙ sh P = .contradicted) ∧
    (∃ S₀ Sₙ : Sys, RealizesUnderTCB false rels S₀ Sₙ ∧
      statusOf S₀ sh P = .contradicted ∧ statusOf Sₙ sh P = .supported) := by
  rcases hnd with ⟨⟨S₁, h₁⟩, ⟨S₂, h₂⟩⟩
  exact ⟨rfl, rfl,
    ⟨S₁, S₂, (fun h => by cases h), h₁, h₂⟩,
    ⟨S₂, S₁, (fun h => by cases h), h₂, h₁⟩⟩

/-- Tightness counterexample for `hnd : NonDegen sh P` in `unwarranted_collapses_both_statuses`:
on `specConstTrue`, no system has verdict `.contradicted`, falsifying the countermodel conjuncts. -/
theorem cex_unwarranted_collapse_without_nonDegen :
    ¬ ∃ S₀ Sₙ : Sys, RealizesUnderTCB false [] S₀ Sₙ ∧
        statusOf S₀ .univSafety specConstTrue = .supported ∧
        statusOf Sₙ .univSafety specConstTrue = .contradicted := by
  rintro ⟨_, Sₙ, _, _, hcon⟩
  rw [statusOf_eq_contradicted_iff] at hcon
  exact hcon (fun _ _ _ => rfl)

/-- Vacuous agreement at `st₀ = .undetermined` when `warrantValid = false`. -/
theorem unwarranted_undetermined_vacuous_agreement (rels : List BoundaryRel) (sh : PosShape)
    (P : Spec) :
    licensedTransfer false rels sh .undetermined = .undetermined ∧
    ∀ S₀ Sₙ : Sys, RealizesUnderTCB false rels S₀ Sₙ →
      statusOf S₀ sh P = .undetermined → statusOf Sₙ sh P = .undetermined := by
  refine ⟨rfl, fun S₀ _ _ h => False.elim (statusOf_ne_undetermined S₀ sh P h)⟩

/-! ### Proved Positive and Negative Examples & Non-Vacuity Witnesses for `Chain.lean` -/

theorem realizesChain_pos :
    RealizesChain [.cospanCaptureLower, .lockStepSim .s2m] (constSys valTrue) (constSys valTrue) :=
  realizesChain_refl _ _

theorem realizesChain_neg :
    ¬ RealizesChain [.embed .m2s] (constSys valFalse) (constSys valTrue) := by
  intro h
  cases h with
  | cons hrel htail =>
    cases htail with
    | nil _ => exact realizes_neg hrel

theorem transferChain_pos :
    transferChain [.cospanCaptureLower, .lockStepSim .s2m, .litEntails] .hyperSubsetClosed .supported =
      .supported := rfl

theorem transferChain_neg :
    transferChain [.cospanCaptureLower, .wfStutterSim .s2m] .hyperSubsetClosed .supported ≠
      .supported := by decide

theorem gateWarrant_pos : gateWarrant true .contradicted = .contradicted := rfl
theorem gateWarrant_neg : gateWarrant false .contradicted ≠ .contradicted := by decide

theorem licensedTransfer_pos :
    licensedTransfer true [.certFaithfulSoundPinned, .termRoundTrip] .hyperGeneral .contradicted =
      .contradicted := rfl

theorem licensedTransfer_neg :
    licensedTransfer false [.certFaithfulSoundPinned, .termRoundTrip] .hyperGeneral .contradicted ≠
      .contradicted := by decide

theorem realizesUnderTCB_pos :
    RealizesUnderTCB false [.embed .m2s] (constSys valFalse) (constSys valTrue) :=
  fun h => by cases h

theorem realizesUnderTCB_neg :
    ¬ RealizesUnderTCB true [.embed .m2s] (constSys valFalse) (constSys valTrue) :=
  fun h => realizesChain_neg (h rfl)

theorem traceDeterministic_pos : TraceDeterministic (constSys valTrue) := by
  intro τ₁ τ₂ h₁ h₂
  funext n
  rw [(hasTrace_constSys_iff valTrue τ₁).1 h₁ n, (hasTrace_constSys_iff valTrue τ₂).1 h₂ n]

theorem traceDeterministic_neg :
    ¬ TraceDeterministic (twoBranchSys valFalse valTrue valFalse valFalse) := by
  intro hdet
  let τ₀ : Trace := fun n => match n with | 0 => valFalse | _ + 1 => valTrue
  let τ₁ : Trace := fun _ => valFalse
  have h₀ : HasTrace (twoBranchSys valFalse valTrue valFalse valFalse) τ₀ := by
    unfold twoBranchSys; rw [hasTrace_maskedBranchSys_iff]; exact ⟨⟨0, by omega⟩, rfl, fun _ => rfl⟩
  have h₁ : HasTrace (twoBranchSys valFalse valTrue valFalse valFalse) τ₁ := by
    unfold twoBranchSys; rw [hasTrace_maskedBranchSys_iff]; exact ⟨⟨1, by omega⟩, rfl, fun _ => rfl⟩
  have heq := congrFun (congrFun (hdet τ₀ τ₁ h₀ h₁) 1) 0
  simp [τ₀, τ₁, valTrue, valFalse] at heq

/-- Explicit 3-step `RealizesChain` non-vacuity witness with distinct trace sets `S₀` vs. `S₃` for
`transferChain_eq_iff_forall_realizesChain`. -/
theorem nonvacuity_transferChain :
    let rels : List BoundaryRel := [.cospanCaptureLower, .lockStepSim .s2m, .litEntails]
    let S₀ : Sys := twoBranchSys valTrue valTrue valFalse valFalse
    let S₃ : Sys := oneBranchSys valTrue valTrue
    NonDegen .hyperSubsetClosed specAtom0 ∧
    transferChain rels .hyperSubsetClosed .supported = .supported ∧
    RealizesChain rels S₀ S₃ ∧
    ¬ TraceIncl S₀ S₃ ∧
    statusOf S₀ .hyperSubsetClosed specAtom0 = .supported ∧
    statusOf S₃ .hyperSubsetClosed specAtom0 = .supported := by
  intro rels S₀ S₃
  have hemb : IsEmbedFrom S₃ S₀ := isEmbedFrom_one_two valTrue valTrue valFalse valFalse
  have hcs : Realizes .cospanCaptureLower S₀ S₃ :=
    (cospanSysWitness_iff_traceIncl S₀ S₃).2
      (lockStepSimFrom_traceIncl (isEmbedFrom_lockStepSimFrom hemb))
  have hchain : RealizesChain rels S₀ S₃ :=
    .cons hcs (.cons (realizes_refl _ S₃) (.cons (realizes_refl _ S₃) (.nil S₃)))
  have hsup0 : statusOf S₀ .hyperSubsetClosed specAtom0 = .supported := by
    rw [statusOf_eq_supported_iff]
    intro τ₁ τ₂ h₁ h₂ h0eq n
    unfold S₀ twoBranchSys at h₁ h₂
    rw [hasTrace_maskedBranchSys_iff] at h₁ h₂
    rcases h₁ with ⟨⟨c₁, hc₁⟩, h10, h11⟩
    rcases h₂ with ⟨⟨c₂, hc₂⟩, h20, h21⟩
    have hc₁' : c₁ = 0 ∨ c₁ = 1 := by omega
    have hc₂' : c₂ = 0 ∨ c₂ = 1 := by omega
    rcases hc₁' with rfl | rfl <;> rcases hc₂' with rfl | rfl
    · cases n with | zero => rw [h10, h20] | succ m => rw [h11 m, h21 m]
    · simp [h10, h20, evalVal, specAtom0, valTrue, valFalse] at h0eq
    · simp [h10, h20, evalVal, specAtom0, valTrue, valFalse] at h0eq
    · cases n with | zero => rw [h10, h20] | succ m => rw [h11 m, h21 m]
  have hnd : NonDegen .hyperSubsetClosed specAtom0 :=
    (nonDegen_iff_evalVal_false_true .hyperSubsetClosed specAtom0).2 ⟨rfl, rfl⟩
  have hsup3 : statusOf S₃ .hyperSubsetClosed specAtom0 = .supported :=
    (transferChain_eq_iff_forall_realizesChain rels .hyperSubsetClosed specAtom0 .supported hnd).1
      rfl S₀ S₃ hchain hsup0
  refine ⟨hnd, rfl, hchain, ?_, hsup0, hsup3⟩
  intro htr
  have hbad : HasTrace S₀ (fun _ => valFalse) := by
    unfold S₀ twoBranchSys; rw [hasTrace_maskedBranchSys_iff]
    exact ⟨⟨1, by omega⟩, rfl, fun _ => rfl⟩
  have h0eq := congrFun ((evalShape_oneBranch valTrue valTrue _).1 (htr _ hbad)).1 0
  simp [valTrue, valFalse] at h0eq

/-- Non-vacuity witness for `licensedTransfer_eq_iff_forall_realizesUnderTCB` and
`unwarranted_collapses_both_statuses`. -/
theorem nonvacuity_licensedTransfer :
    let rels : List BoundaryRel := [.cospanCaptureLower, .lockStepSim .s2m, .litEntails]
    let S₀ : Sys := twoBranchSys valTrue valTrue valFalse valFalse
    let S₃ : Sys := oneBranchSys valTrue valTrue
    NonDegen .hyperSubsetClosed specAtom0 ∧
    licensedTransfer true rels .hyperSubsetClosed .supported = .supported ∧
    RealizesUnderTCB true rels S₀ S₃ ∧
    statusOf S₀ .hyperSubsetClosed specAtom0 = .supported ∧
    licensedTransfer false rels .hyperSubsetClosed .supported = .undetermined := by
  have h := nonvacuity_transferChain
  exact ⟨h.1, rfl, fun _ => h.2.2.1, h.2.2.2.2.1, rfl⟩

end Toy.BoundaryLicensing
