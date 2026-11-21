import Toy.PlaceEval.Simulation

/-!
# Simulations for the single-block edits

Instances of the simulation argument of `Simulation.lean` for deleting a `placeMention`
(`deleteStmt`), replacing an equal-target `switchInt` by a `goto` (`setTerm`) and rewriting
`&p` to `&raw p` (`setStmt`). Each edit leaves the locals and the storage markers unchanged,
so the initial states coincide, and the two programs run in lockstep except at the edited
point.
-/

namespace Toy.PlaceEval

theorem drop_succ_ne_drop {ss : List Stmt} {i : Nat} (hi : i < ss.length) :
    ss.drop (i + 1) ≠ ss.drop i := by
  intro h
  have := congrArg List.length h
  simp only [List.length_drop] at this
  omega

theorem not_drop_suffix_drop_succ {ss : List Stmt} {i : Nat} (hi : i < ss.length) :
    ¬ ss.drop i <:+ ss.drop (i + 1) := by
  intro h
  have := h.length_le
  simp only [List.length_drop] at this
  omega

/-! ## Deleting a `placeMention` -/

section DeleteStmt

variable {P : Prog} {l : Label} {i : Nat} {p : Place}

/-- Remaining statements of block `l`: `r` in `P`, `r'` in `deleteStmt P l i`. Before the
deleted statement they differ by it; after it they coincide. -/
def DelRel (P : Prog) (l : Label) (i : Nat) (r r' : List Stmt) : Prop :=
  (∃ a, a <:+ (P.blk l).stmts.take i ∧ r = a ++ (P.blk l).stmts.drop i ∧
      r' = a ++ (P.blk l).stmts.drop (i + 1)) ∨
  (r' = r ∧ r <:+ (P.blk l).stmts.drop (i + 1))

theorem deleteStmt_facts (hs : (P.blk l).stmts[i]? = some (.placeMention p)) :
    i < (P.blk l).stmts.length ∧
    (P.blk l).stmts.drop i = .placeMention p :: (P.blk l).stmts.drop (i + 1) ∧
    (deleteStmt P l i).blk l =
      ⟨(P.blk l).stmts.take i ++ (P.blk l).stmts.drop (i + 1), (P.blk l).term⟩ ∧
    (∀ l', l' ≠ l → (deleteStmt P l i).blk l' = P.blk l') ∧
    (deleteStmt P l i).locals = P.locals ∧
    (∀ x, (deleteStmt P l i).hasMarkers x = P.hasMarkers x) := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.1 hs
  have hdrop : (P.blk l).stmts.drop i = .placeMention p :: (P.blk l).stmts.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hget]
  have hl := lt_length_of_stmt hs
  refine ⟨hi, hdrop, ?_, fun l' h => blk_setBlk_ne P _ h, rfl, fun x => ?_⟩
  · simp only [deleteStmt]
    rw [blk_setBlk_self P _ hl, List.eraseIdx_eq_take_drop_succ]
  · apply hasMarkers_setBlk
    simp only [List.eraseIdx_eq_take_drop_succ]
    conv => rhs; rw [← List.take_append_drop i (P.blk l).stmts, hdrop]
    simp [List.any_append, Stmt.isMarkerOf]

theorem deleteStmt_entryRel (hs : (P.blk l).stmts[i]? = some (.placeMention p)) :
    DelRel P l i (P.blk l).stmts ((deleteStmt P l i).blk l).stmts := by
  obtain ⟨_, _, hblk, _⟩ := deleteStmt_facts hs
  rw [hblk]
  exact Or.inl ⟨_, List.suffix_refl _, (List.take_append_drop i _).symm, rfl⟩

theorem deleteStmt_at (hs : (P.blk l).stmts[i]? = some (.placeMention p)) (st : State) :
    (deleteStmt P l i).at l i st = ⟨l, (P.blk l).stmts.drop (i + 1), st⟩ := by
  obtain ⟨hi, _, hblk, _⟩ := deleteStmt_facts hs
  simp only [Prog.at, hblk]
  rw [List.drop_left']
  simp only [List.length_take]
  omega

/-- Forward matching: `deleteStmt P l i` (target) against `P` (source). -/
theorem deleteStmt_stepSim (ms : AllocMode) (hs : (P.blk l).stmts[i]? = some (.placeMention p)) :
    ∀ cs ct, BRel l (DelRel P l i) cs ct →
      StepSim ms P ms (deleteStmt P l i) (BRel l (DelRel P l i)) (fun _ => 0) cs ct := by
  obtain ⟨_, hdrop, hblk, hout, hloc, _⟩ := deleteStmt_facts hs
  have hentry := deleteStmt_entryRel hs
  have hsuf : ∀ r st, r <:+ (P.blk l).stmts.drop (i + 1) →
      StepSimU ms P ms (deleteStmt P l i) (BRel l (DelRel P l i)) (fun _ => 0)
        (fun _ _ => False) ⟨l, r, st⟩ ⟨l, r, st⟩ := by
    intro r st hr
    cases r with
    | cons s r =>
      exact stepSimU_cons hloc l s r r st fun st' =>
        ⟨rfl, rfl, fun h => absurd rfl h, fun _ => Or.inr ⟨rfl, (List.suffix_cons s r).trans hr⟩⟩
    | nil => exact stepSimU_nil l st (by rw [hblk]) (fun b => bRel_entry hout hentry b st)
  rintro ⟨lbl, rs, st⟩ ⟨lbl', rt, st'⟩ ⟨hst, hlbl, hne, heq⟩
  simp only at hst hlbl hne heq
  subst hst hlbl
  by_cases hl : lbl = l
  · subst hl
    rcases heq rfl with ⟨a, ha, rfl, rfl⟩ | ⟨rfl, hr⟩
    · cases a with
      | nil =>
        simp only [List.nil_append]
        cases he : evalPlace st p with
        | none =>
          refine Or.inl (srcUB_of_step_ub ?_)
          rw [hdrop]; simp [step, execStmt, he]
        | some q =>
          refine stepSim_of_silent (cs1 := ⟨lbl, (P.blk lbl).stmts.drop (i + 1), st⟩) ?_
            ((hsuf _ st (List.suffix_refl _)).toStepSim False.elim)
          rw [hdrop]; simp [step, execStmt, he]
      | cons s a =>
        exact (stepSimU_cons (U := fun _ _ => False) hloc lbl s _ _ st fun st' => ⟨rfl, rfl, fun h => absurd rfl h,
          fun _ => Or.inl ⟨a, (List.suffix_cons s a).trans ha, rfl, rfl⟩⟩).toStepSim
          False.elim
    · exact (hsuf _ st hr).toStepSim False.elim
  · obtain rfl := hne hl
    exact (bRel_stepSimU_out (U := fun _ _ => False) hloc hout hentry lbl hl rs st).toStepSim
      False.elim

/-- Measure for the reverse matching: `1` exactly at the deleted `placeMention`. -/
def delMeasure (P : Prog) (l : Label) (i : Nat) (c : Cfg) : Nat :=
  if c.lbl = l ∧ c.rest = (P.blk l).stmts.drop i then 1 else 0

/-- The exceptional pairs of the reverse matching: `P` at the deleted `placeMention`, whose
place evaluation fails. -/
def DelExc (P : Prog) (l : Label) (i : Nat) (p : Place) (cs ct : Cfg) : Prop :=
  ct = ⟨l, (P.blk l).stmts.drop i, ct.st⟩ ∧ evalPlace ct.st p = none ∧
    cs = ⟨l, (P.blk l).stmts.drop (i + 1), ct.st⟩

/-- Reverse matching: `P` (target) against `deleteStmt P l i` (source). -/
theorem deleteStmt_rev_stepSimU (ms : AllocMode)
    (hs : (P.blk l).stmts[i]? = some (.placeMention p)) :
    ∀ cs ct, BRel l (fun r' r => DelRel P l i r r') cs ct →
      StepSimU ms (deleteStmt P l i) ms P (BRel l (fun r' r => DelRel P l i r r'))
        (delMeasure P l i) (DelExc P l i p) cs ct := by
  obtain ⟨hi, hdrop, hblk, hout, hloc, _⟩ := deleteStmt_facts hs
  have hout' : ∀ l', l' ≠ l → P.blk l' = (deleteStmt P l i).blk l' :=
    fun l' h => (hout l' h).symm
  have hentry : (fun r' r => DelRel P l i r r') ((deleteStmt P l i).blk l).stmts
      (P.blk l).stmts := deleteStmt_entryRel hs
  have hsuf : ∀ r st, r <:+ (P.blk l).stmts.drop (i + 1) →
      StepSimU ms (deleteStmt P l i) ms P (BRel l (fun r' r => DelRel P l i r r'))
        (delMeasure P l i) (DelExc P l i p) ⟨l, r, st⟩ ⟨l, r, st⟩ := by
    intro r st hr
    cases r with
    | cons s r =>
      exact stepSimU_cons hloc.symm l s r r st fun st' =>
        ⟨rfl, rfl, fun h => absurd rfl h, fun _ => Or.inr ⟨rfl, (List.suffix_cons s r).trans hr⟩⟩
    | nil => exact stepSimU_nil l st (by rw [hblk]) (fun b => bRel_entry hout' hentry b st)
  rintro ⟨lbl, rs, st⟩ ⟨lbl', rt, st'⟩ ⟨hst, hlbl, hne, heq⟩
  simp only at hst hlbl hne heq
  subst hst hlbl
  by_cases hl : lbl = l
  · subst hl
    rcases heq rfl with ⟨a, ha, rfl, rfl⟩ | ⟨rfl, hr⟩
    · cases a with
      | nil =>
        simp only [List.nil_append]
        have hμ1 : delMeasure P lbl i ⟨lbl, (P.blk lbl).stmts.drop i, st⟩ = 1 := by
          simp [delMeasure]
        have hμ0 : delMeasure P lbl i ⟨lbl, (P.blk lbl).stmts.drop (i + 1), st⟩ = 0 := by
          simp [delMeasure, drop_succ_ne_drop hi]
        cases he : evalPlace st p with
        | none =>
          have hstep : step ms P ⟨lbl, (P.blk lbl).stmts.drop i, st⟩ = .ub := by
            rw [hdrop]; simp [step, execStmt, he]
          refine ⟨(fun _ _ h => by rw [hstep] at h; cases h), (fun _ h => by rw [hstep] at h; cases h),
            (fun _ => Or.inl ⟨rfl, he, rfl⟩)⟩
        | some q =>
          have hstep : step ms P ⟨lbl, (P.blk lbl).stmts.drop i, st⟩ =
              .next none ⟨lbl, (P.blk lbl).stmts.drop (i + 1), st⟩ := by
            rw [hdrop]; simp [step, execStmt, he]
          refine ⟨fun ev ct' h => ?_, (fun _ h => by rw [hstep] at h; cases h),
            (fun h => by rw [hstep] at h; cases h)⟩
          rw [hstep] at h
          cases h
          refine Or.inr ⟨rfl, by rw [hμ0, hμ1]; exact Nat.zero_lt_one, rfl, rfl,
            fun h => absurd rfl h, fun _ => Or.inr ⟨rfl, List.suffix_refl _⟩⟩
      | cons s a =>
        exact stepSimU_cons hloc.symm lbl s _ _ st fun st' => ⟨rfl, rfl, fun h => absurd rfl h,
          fun _ => Or.inl ⟨a, (List.suffix_cons s a).trans ha, rfl, rfl⟩⟩
    · exact hsuf _ st hr
  · obtain rfl := hne hl
    exact bRel_stepSimU_out hloc.symm hout' hentry lbl hl rs st

/-- The reverse relation pins the source configuration at the deleted point. -/
theorem deleteStmt_rev_at (hs : (P.blk l).stmts[i]? = some (.placeMention p)) {cs : Cfg}
    {st : State} (h : BRel l (fun r' r => DelRel P l i r r') cs ⟨l, (P.blk l).stmts.drop i, st⟩) :
    cs = ⟨l, (P.blk l).stmts.drop (i + 1), st⟩ := by
  obtain ⟨hi, _⟩ := deleteStmt_facts hs
  obtain ⟨lbl, r, st'⟩ := cs
  obtain ⟨hst, hlbl, _, heq⟩ := h
  simp only at hst hlbl heq
  subst hst hlbl
  rcases heq rfl with ⟨a, _, ha, rfl⟩ | ⟨rfl, hr⟩
  · have : a.length = 0 := by
      have := congrArg List.length ha
      simp only [List.length_append] at this
      omega
    rw [List.length_eq_zero_iff] at this
    subst this
    rfl
  · exact absurd hr (not_drop_suffix_drop_succ hi)

/-- Reverse refinement for `deleteStmt`, given that every reached failing evaluation of the
deleted place is matched by UB of the edited program. -/
theorem deleteStmt_rev_refinesPP (S : Sem) (hs : (P.blk l).stmts[i]? = some (.placeMention p))
    (hfail : ∀ ω st0 st, P.initState (S.mode ω) = some st0 →
      Reach (S.mode ω) P (P.entry 0 st0) ⟨l, (P.blk l).stmts.drop i, st⟩ →
      evalPlace st p = none →
      SrcUB (S.mode ω) (deleteStmt P l i) ⟨l, (P.blk l).stmts.drop (i + 1), st⟩) :
    RefinesPP S (deleteStmt P l i) P := by
  obtain ⟨_, _, _, hout, hloc, hmark⟩ := deleteStmt_facts hs
  refine refinesAcross_of_sim fun ω st0 h0 =>
    ⟨ω, st0, _, delMeasure P l i, 1, by rw [initState_congr hloc hmark]; exact h0,
      IsSim.withReach (P.entry 0 st0) (fun _ _ _ => by unfold delMeasure; split <;> omega)
        (fun cs ct hR hreach => (deleteStmt_rev_stepSimU _ hs cs ct hR).toStepSim ?_),
      bRel_entry (fun l' h => (hout l' h).symm) (deleteStmt_entryRel hs) 0 st0, ⟨0, [], rfl⟩⟩
  rintro ⟨hct, hnone, rfl⟩
  rw [hct] at hreach
  exact hfail ω st0 _ h0 hreach hnone

/-- Forward refinement for `deleteStmt` of a `placeMention`. -/
theorem deleteStmt_refinesPP (S : Sem) (hs : (P.blk l).stmts[i]? = some (.placeMention p)) :
    RefinesPP S P (deleteStmt P l i) := by
  obtain ⟨_, _, _, hout, hloc, hmark⟩ := deleteStmt_facts hs
  exact refinesAcross_of_sim fun ω st0 h0 =>
    ⟨ω, st0, BRel l (DelRel P l i), fun _ => 0, 0,
      by rw [← initState_congr hloc hmark]; exact h0,
      ⟨fun _ _ _ => Nat.le_refl 0, deleteStmt_stepSim _ hs⟩,
      bRel_entry hout (deleteStmt_entryRel hs) 0 st0⟩

end DeleteStmt

/-! ## Replacing an equal-target `switchInt` by a `goto` -/

section SetTerm

variable {P : Prog} {l : Label} {o : Operand} {arms : List (Nat × Label)} {b : Label}

theorem selectTarget_of_all (hall : ∀ a ∈ arms, a.2 = b) (n : Nat) :
    selectTarget arms b n = b := by
  induction arms with
  | nil => rfl
  | cons a arms ih =>
    obtain ⟨v, b'⟩ := a
    simp only [selectTarget]
    split
    · exact hall _ (List.mem_cons_self ..)
    · exact ih fun a ha => hall a (List.mem_cons_of_mem _ ha)

theorem setTerm_facts (ht : (P.blk l).term = .switchInt o arms b) :
    (setTerm P l (.goto b)).blk l = ⟨(P.blk l).stmts, .goto b⟩ ∧
    (∀ l', l' ≠ l → (setTerm P l (.goto b)).blk l' = P.blk l') ∧
    (setTerm P l (.goto b)).locals = P.locals ∧
    (∀ x, (setTerm P l (.goto b)).hasMarkers x = P.hasMarkers x) := by
  have hl := lt_length_of_term ht
  refine ⟨?_, fun l' h => blk_setBlk_ne P _ h, rfl, fun x => hasMarkers_setBlk P l _ x rfl⟩
  simp only [setTerm]
  rw [blk_setBlk_self P _ hl]

theorem setTerm_entryRel (ht : (P.blk l).term = .switchInt o arms b) :
    (fun r r' => r' = r) (P.blk l).stmts ((setTerm P l (.goto b)).blk l).stmts := by
  obtain ⟨hblk, _⟩ := setTerm_facts ht
  simp only [hblk]

/-- Forward matching: `setTerm P l (.goto b)` (target) against `P` (source). -/
theorem setTerm_stepSim (ms : AllocMode) (ht : (P.blk l).term = .switchInt o arms b)
    (hall : ∀ a ∈ arms, a.2 = b) :
    ∀ cs ct, BRel l (fun r r' => r' = r) cs ct →
      StepSim ms P ms (setTerm P l (.goto b)) (BRel l (fun r r' => r' = r)) (fun _ => 0) cs ct := by
  obtain ⟨hblk, hout, hloc, _⟩ := setTerm_facts ht
  have hentry := setTerm_entryRel ht
  rintro ⟨lbl, rs, st⟩ ⟨lbl', rt, st'⟩ ⟨hst, hlbl, hne, heq⟩
  simp only at hst hlbl hne heq
  subst hst hlbl
  by_cases hl : lbl = l
  · subst hl
    obtain rfl := heq rfl
    cases rt with
    | cons s r =>
      exact (stepSimU_cons (U := fun _ _ => False) hloc lbl s r r st fun st' =>
        ⟨rfl, rfl, fun h => absurd rfl h, fun _ => rfl⟩).toStepSim False.elim
    | nil =>
      have htgt : step ms (setTerm P lbl (.goto b)) ⟨lbl, [], st⟩ =
          .next none ((setTerm P lbl (.goto b)).entry b st) := by
        simp [step, hblk]
      cases hv : o.evalInt st with
      | none =>
        refine Or.inl (srcUB_of_step_ub ?_)
        simp [step, ht, hv]
      | some n =>
        have hsrc : step ms P ⟨lbl, [], st⟩ = .next none (P.entry b st) := by
          simp [step, ht, hv, selectTarget_of_all hall]
        refine Or.inr ⟨fun ev ct' h => ?_, (fun _ h => by rw [htgt] at h; cases h),
          (by rw [htgt]; simp)⟩
        rw [htgt] at h
        cases h
        exact Or.inl ⟨0, _, run_one_next hsrc, bRel_entry hout hentry b st⟩
  · obtain rfl := hne hl
    exact (bRel_stepSimU_out (U := fun _ _ => False) hloc hout hentry lbl hl rs st).toStepSim
      False.elim

/-- The exceptional pairs of the reverse matching: `P` at the switch, whose operand does not
evaluate to an integer. -/
def SwExc (l : Label) (o : Operand) (cs ct : Cfg) : Prop :=
  ct = ⟨l, [], ct.st⟩ ∧ o.evalInt ct.st = none ∧ cs = ⟨l, [], ct.st⟩

/-- Reverse matching: `P` (target) against `setTerm P l (.goto b)` (source). -/
theorem setTerm_rev_stepSimU (ms : AllocMode) (ht : (P.blk l).term = .switchInt o arms b)
    (hall : ∀ a ∈ arms, a.2 = b) :
    ∀ cs ct, BRel l (fun r' r => r' = r) cs ct →
      StepSimU ms (setTerm P l (.goto b)) ms P (BRel l (fun r' r => r' = r)) (fun _ => 0)
        (SwExc l o) cs ct := by
  obtain ⟨hblk, hout, hloc, _⟩ := setTerm_facts ht
  have hout' : ∀ l', l' ≠ l → P.blk l' = (setTerm P l (.goto b)).blk l' :=
    fun l' h => (hout l' h).symm
  have hentry : (fun r' r => r' = r) ((setTerm P l (.goto b)).blk l).stmts (P.blk l).stmts := by
    simp only [hblk]
  rintro ⟨lbl, rs, st⟩ ⟨lbl', rt, st'⟩ ⟨hst, hlbl, hne, heq⟩
  simp only at hst hlbl hne heq
  subst hst hlbl
  by_cases hl : lbl = l
  · subst hl
    obtain rfl := heq rfl
    cases rs with
    | cons s r =>
      exact stepSimU_cons hloc.symm lbl s r r st fun st' =>
        ⟨rfl, rfl, fun h => absurd rfl h, fun _ => rfl⟩
    | nil =>
      have hsrc : step ms (setTerm P lbl (.goto b)) ⟨lbl, [], st⟩ =
          .next none ((setTerm P lbl (.goto b)).entry b st) := by
        simp [step, hblk]
      cases hv : o.evalInt st with
      | none =>
        have htgt : step ms P ⟨lbl, [], st⟩ = .ub := by simp [step, ht, hv]
        exact ⟨(fun _ _ h => by rw [htgt] at h; cases h), (fun _ h => by rw [htgt] at h; cases h),
          (fun _ => Or.inl ⟨rfl, hv, rfl⟩)⟩
      | some n =>
        have htgt : step ms P ⟨lbl, [], st⟩ = .next none (P.entry b st) := by
          simp [step, ht, hv, selectTarget_of_all hall]
        refine ⟨fun ev ct' h => ?_, (fun _ h => by rw [htgt] at h; cases h),
          (fun h => by rw [htgt] at h; cases h)⟩
        rw [htgt] at h
        cases h
        exact Or.inl ⟨0, _, run_one_next hsrc, bRel_entry hout' hentry b st⟩
  · obtain rfl := hne hl
    exact bRel_stepSimU_out hloc.symm hout' hentry lbl hl rs st

/-- Forward refinement for replacing an equal-target `switchInt` by a `goto`. -/
theorem setTerm_refinesPP (S : Sem) (ht : (P.blk l).term = .switchInt o arms b)
    (hall : ∀ a ∈ arms, a.2 = b) : RefinesPP S P (setTerm P l (.goto b)) := by
  obtain ⟨_, hout, hloc, hmark⟩ := setTerm_facts ht
  exact refinesAcross_of_sim fun ω st0 h0 =>
    ⟨ω, st0, BRel l (fun r r' => r' = r), fun _ => 0, 0,
      by rw [← initState_congr hloc hmark]; exact h0,
      ⟨fun _ _ _ => Nat.le_refl 0, setTerm_stepSim _ ht hall⟩,
      bRel_entry hout (setTerm_entryRel ht) 0 st0⟩

/-- Reverse refinement, given that every reached failing operand evaluation is matched by UB
of the edited program from the entry of `b`. -/
theorem setTerm_rev_refinesPP (S : Sem) (ht : (P.blk l).term = .switchInt o arms b)
    (hall : ∀ a ∈ arms, a.2 = b)
    (hfail : ∀ ω st0 st, P.initState (S.mode ω) = some st0 →
      Reach (S.mode ω) P (P.entry 0 st0) ⟨l, [], st⟩ → o.evalInt st = none →
      SrcUB (S.mode ω) (setTerm P l (.goto b)) ((setTerm P l (.goto b)).entry b st)) :
    RefinesPP S (setTerm P l (.goto b)) P := by
  obtain ⟨hblk, hout, hloc, hmark⟩ := setTerm_facts ht
  refine refinesAcross_of_sim fun ω st0 h0 =>
    ⟨ω, st0, _, fun _ => 0, 0, by rw [initState_congr hloc hmark]; exact h0,
      IsSim.withReach (P.entry 0 st0) (fun _ _ _ => Nat.le_refl 0)
        (fun cs ct hR hreach => (setTerm_rev_stepSimU _ ht hall cs ct hR).toStepSim ?_),
      bRel_entry (fun l' h => (hout l' h).symm) (by simp only [hblk]) 0 st0, ⟨0, [], rfl⟩⟩
  rintro ⟨hct, hnone, rfl⟩
  rw [hct] at hreach
  refine srcUB_of_silent ?_ (hfail ω st0 _ h0 hreach hnone)
  simp [step, hblk]

end SetTerm

/-! ## Rewriting `&p` to `&raw p` -/

section SetStmt

variable {P : Prog} {l : Label} {i : Nat} {dst : Place} {τ : Ty} {p : Place} {L : Layout}

/-- Remaining statements of block `l`: `r` in `P`, `r'` in the program with statement `i`
replaced by `s'`. -/
def SetRel (P : Prog) (l : Label) (i : Nat) (s' : Stmt) (r r' : List Stmt) : Prop :=
  (∃ a, a <:+ (P.blk l).stmts.take i ∧ r = a ++ (P.blk l).stmts.drop i ∧
      r' = a ++ s' :: (P.blk l).stmts.drop (i + 1)) ∨
  (r' = r ∧ r <:+ (P.blk l).stmts.drop (i + 1))

theorem setStmt_ref_facts (hs : (P.blk l).stmts[i]? = some (.assign dst τ (.ref p L))) :
    (P.blk l).stmts.drop i = .assign dst τ (.ref p L) :: (P.blk l).stmts.drop (i + 1) ∧
    (setStmt P l i (.assign dst τ (.rawRef p))).blk l =
      ⟨(P.blk l).stmts.take i ++ .assign dst τ (.rawRef p) :: (P.blk l).stmts.drop (i + 1),
        (P.blk l).term⟩ ∧
    (∀ l', l' ≠ l → (setStmt P l i (.assign dst τ (.rawRef p))).blk l' = P.blk l') ∧
    (setStmt P l i (.assign dst τ (.rawRef p))).locals = P.locals ∧
    (∀ x, (setStmt P l i (.assign dst τ (.rawRef p))).hasMarkers x = P.hasMarkers x) := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.1 hs
  have hdrop : (P.blk l).stmts.drop i = .assign dst τ (.ref p L) :: (P.blk l).stmts.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hget]
  have hl := lt_length_of_stmt hs
  have hset : (P.blk l).stmts.set i (.assign dst τ (.rawRef p)) =
      (P.blk l).stmts.take i ++ .assign dst τ (.rawRef p) :: (P.blk l).stmts.drop (i + 1) := by
    simp [List.set_eq_take_append_cons_drop, hi]
  refine ⟨hdrop, ?_, fun l' h => blk_setBlk_ne P _ h, rfl, fun x => ?_⟩
  · simp only [setStmt]
    rw [blk_setBlk_self P _ hl, hset]
  · apply hasMarkers_setBlk
    simp only [hset]
    conv => rhs; rw [← List.take_append_drop i (P.blk l).stmts, hdrop]
    simp [List.any_append, Stmt.isMarkerOf]

/-- `&p` succeeds only where `&raw p` succeeds, with the same result. -/
theorem execStmt_ref_rawRef (mode : AllocMode) (P : Prog) (st : State) :
    execStmt mode P st (.assign dst τ (.ref p L)) = .ub ∨
      execStmt mode P st (.assign dst τ (.rawRef p)) =
        execStmt mode P st (.assign dst τ (.ref p L)) := by
  simp only [execStmt, Rvalue.eval]
  cases evalPlace st dst with
  | none => exact Or.inr rfl
  | some q =>
    simp only
    cases evalPlace st p with
    | none => exact Or.inr rfl
    | some q' =>
      by_cases h : RefOk st.mem q' L
      · exact Or.inr (by simp [h])
      · exact Or.inl (by simp [h])

/-- Forward matching: the rewritten program (target) against `P` (source). -/
theorem setStmt_ref_stepSim (ms : AllocMode)
    (hs : (P.blk l).stmts[i]? = some (.assign dst τ (.ref p L))) :
    ∀ cs ct, BRel l (SetRel P l i (.assign dst τ (.rawRef p))) cs ct →
      StepSim ms P ms (setStmt P l i (.assign dst τ (.rawRef p)))
        (BRel l (SetRel P l i (.assign dst τ (.rawRef p)))) (fun _ => 0) cs ct := by
  obtain ⟨hdrop, hblk, hout, hloc, _⟩ := setStmt_ref_facts hs
  have hentry : SetRel P l i (.assign dst τ (.rawRef p)) (P.blk l).stmts
      ((setStmt P l i (.assign dst τ (.rawRef p))).blk l).stmts := by
    rw [hblk]
    exact Or.inl ⟨_, List.suffix_refl _, (List.take_append_drop i _).symm, rfl⟩
  have hsuf : ∀ r st, r <:+ (P.blk l).stmts.drop (i + 1) →
      StepSimU ms P ms (setStmt P l i (.assign dst τ (.rawRef p)))
        (BRel l (SetRel P l i (.assign dst τ (.rawRef p)))) (fun _ => 0)
        (fun _ _ => False) ⟨l, r, st⟩ ⟨l, r, st⟩ := by
    intro r st hr
    cases r with
    | cons s r =>
      exact stepSimU_cons hloc l s r r st fun st' =>
        ⟨rfl, rfl, fun h => absurd rfl h, fun _ => Or.inr ⟨rfl, (List.suffix_cons s r).trans hr⟩⟩
    | nil => exact stepSimU_nil l st (by rw [hblk]) (fun b => bRel_entry hout hentry b st)
  rintro ⟨lbl, rs, st⟩ ⟨lbl', rt, st'⟩ ⟨hst, hlbl, hne, heq⟩
  simp only at hst hlbl hne heq
  subst hst hlbl
  by_cases hl : lbl = l
  · subst hl
    rcases heq rfl with ⟨a, ha, rfl, rfl⟩ | ⟨rfl, hr⟩
    · cases a with
      | nil =>
        simp only [List.nil_append]
        rw [hdrop]
        rcases execStmt_ref_rawRef (dst := dst) (τ := τ) (p := p) (L := L) ms P st with hub | heqx
        · refine Or.inl (srcUB_of_step_ub ?_)
          simp [step, hub]
        · refine (stepSimU_cons2 (U := fun _ _ => False) lbl _ _ _ _ st ?_ fun st' =>
            ⟨rfl, rfl, fun h => absurd rfl h, fun _ => Or.inr ⟨rfl, List.suffix_refl _⟩⟩).toStepSim
            False.elim
          rw [execStmt_congr hloc]; exact heqx
      | cons s a =>
        exact (stepSimU_cons (U := fun _ _ => False) hloc lbl s _ _ st fun st' =>
          ⟨rfl, rfl, fun h => absurd rfl h,
            fun _ => Or.inl ⟨a, (List.suffix_cons s a).trans ha, rfl, rfl⟩⟩).toStepSim False.elim
    · exact (hsuf _ st hr).toStepSim False.elim
  · obtain rfl := hne hl
    exact (bRel_stepSimU_out (U := fun _ _ => False) hloc hout hentry lbl hl rs st).toStepSim
      False.elim

/-- Forward refinement for rewriting `dst := &p` to `dst := &raw p`. -/
theorem setStmt_ref_refinesPP (S : Sem)
    (hs : (P.blk l).stmts[i]? = some (.assign dst τ (.ref p L))) :
    RefinesPP S P (setStmt P l i (.assign dst τ (.rawRef p))) := by
  obtain ⟨_, hblk, hout, hloc, hmark⟩ := setStmt_ref_facts hs
  exact refinesAcross_of_sim fun ω st0 h0 =>
    ⟨ω, st0, _, fun _ => 0, 0, by rw [← initState_congr hloc hmark]; exact h0,
      ⟨fun _ _ _ => Nat.le_refl 0, setStmt_ref_stepSim _ hs⟩,
      bRel_entry hout (by rw [hblk]; exact Or.inl ⟨_, List.suffix_refl _,
        (List.take_append_drop i _).symm, rfl⟩) 0 st0⟩

end SetStmt

end Toy.PlaceEval
