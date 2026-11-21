import Toy.ZstAssume.Sim

/-!
# Simulations for the individual program edits

Each edit changes one block. The simulations relate configurations through `BlockRel`,
with a correspondence of the remaining statements inside the edited block.
-/

namespace Toy.ZstAssume

/-! ### Inserting one statement -/

/-- Remaining statements of the edited block when the right program has `s` inserted
between `as` and `bs` and the left program has `as ++ bs`. Up to the insertion point the
right rest has `s` in front of `bs`; once the left program has executed a statement of
`bs`, the two rests coincide. -/
def InsFwd (as bs : List Stmt) (s : Stmt) (r₀ r₁ : List Stmt) (_ : State) : Prop :=
  (∃ u, u <:+ as ∧ r₀ = u ++ bs ∧ r₁ = u ++ s :: bs) ∨ (∃ a, a :: r₀ <:+ bs ∧ r₁ = r₀)

/-- Remaining statements of the edited block when the left program has `s` inserted
between `as` and `bs` and the right program has `as ++ bs`. -/
def InsRev (as bs : List Stmt) (s : Stmt) (r₁ r₀ : List Stmt) (_ : State) : Prop :=
  (∃ u, u <:+ as ∧ r₁ = u ++ s :: bs ∧ r₀ = u ++ bs) ∨ (r₁ <:+ bs ∧ r₀ = r₁)

/-- `I` is `B` with the statement `s` inserted between `as` and `bs` in block `l`; `s`
either fails or is a silent no-op. -/
structure InsSetting (K : ZContract) (B I : Prog) (l : Label) (as bs : List Stmt) (s : Stmt) :
    Prop where
  hB : (B.blk l).stmts = as ++ bs
  hI : (I.blk l).stmts = as ++ s :: bs
  hτ : (I.blk l).term = (B.blk l).term
  hblk : ∀ l', l' ≠ l → I.blk l' = B.blk l'
  hs : ∀ st, execStmt K s st = some (none, st) ∨ execStmt K s st = none

theorem insRev_inv {as bs : List Stmt} {s : Stmt} {r₀ : List Stmt} {st : State}
    (h : InsRev as bs s (s :: bs) r₀ st) : r₀ = bs := by
  rcases h with ⟨u, -, hu, rfl⟩ | ⟨hsuf, -⟩
  · have := congrArg List.length hu
    simp only [List.length_cons, List.length_append] at this
    have hu0 : u = [] := List.length_eq_zero_iff.1 (by omega)
    subst hu0
    rfl
  · have := hsuf.length_le
    simp only [List.length_cons] at this
    omega

theorem insFwd_inv {as bs : List Stmt} {s : Stmt} {r₁ : List Stmt} {st : State}
    (h : InsFwd as bs s bs r₁ st) : r₁ = s :: bs := by
  rcases h with ⟨u, -, hu, rfl⟩ | ⟨a, hsuf, -⟩
  · have := congrArg List.length hu
    simp only [List.length_append] at this
    have hu0 : u = [] := List.length_eq_zero_iff.1 (by omega)
    subst hu0
    rfl
  · have := hsuf.length_le
    simp only [List.length_cons] at this
    omega

namespace InsSetting

variable {K : ZContract} {B I : Prog} {l : Label} {as bs : List Stmt} {s : Stmt}

theorem hent_rev (S : InsSetting K B I l as bs s) (st : State) :
    InsRev as bs s (I.blk l).stmts (B.blk l).stmts st := by
  rw [S.hI, S.hB]
  exact Or.inl ⟨as, List.suffix_refl _, rfl, rfl⟩

theorem hent_fwd (S : InsSetting K B I l as bs s) (st : State) :
    InsFwd as bs s (B.blk l).stmts (I.blk l).stmts st := by
  rw [S.hI, S.hB]
  exact Or.inl ⟨as, List.suffix_refl _, rfl, rfl⟩

theorem hblk_fwd (S : InsSetting K B I l as bs s) : ∀ l', l' ≠ l → B.blk l' = I.blk l' :=
  fun l' h => (S.hblk l' h).symm

/-- The program with the inserted statement is simulated by the program without it, the
inserted statement being a stutter step; the only stops are actual UB steps. -/
theorem sim_rev (S : InsSetting K B I l as bs s) :
    IsSim K I B (RelR K I B (BlockRel l (InsRev as bs s))) stutterμ
      (fun c => step K I c = .ub) 1 := by
  refine blockSim S.hblk S.hent_rev stutterμ_le (fun _ h => h) ?_
  intro r₁ r₀ st hρ _ _
  rcases hρ with ⟨u, hu, rfl, rfl⟩ | ⟨hsuf, h⟩
  · cases u with
    | nil =>
      exact simStep_stutter l s bs st ⟨l, bs, st⟩ (S.hs st) (fun h => h)
        (fun _ => blockRel_in (Or.inr ⟨List.suffix_refl _, rfl⟩)) rfl
    | cons a u' =>
      exact simStep_head l a _ _ st (fun h => h)
        (fun st' => blockRel_in (Or.inl ⟨u', (List.suffix_cons a u').trans hu, rfl, rfl⟩))
  · rw [h]
    exact simStep_same l r₁ st S.hτ (fun _ h => h)
      (fun a r' st' h => blockRel_in (Or.inr ⟨by
        rw [h] at hsuf
        exact (List.suffix_cons a r').trans hsuf, rfl⟩))
      (blockRel_entry S.hblk S.hent_rev)

/-- The program without the inserted statement is simulated by the program with it,
stopping (at least) where the inserted statement would fail. -/
theorem sim_fwd (S : InsSetting K B I l as bs s) {Stop : Cfg → Prop}
    (hgen : ∀ c, step K B c = .ub → Stop c)
    (hstop : ∀ st, Reach K B ⟨l, bs, st⟩ → Reach K I ⟨l, s :: bs, st⟩ →
      execStmt K s st = none → Stop ⟨l, bs, st⟩) :
    IsSim K B I (RelR K B I (BlockRel l (InsFwd as bs s))) stutterμ Stop 1 := by
  refine blockSim S.hblk_fwd S.hent_fwd stutterμ_le hgen ?_
  intro r₀ r₁ st hρ hc hd
  rcases hρ with ⟨u, hu, rfl, rfl⟩ | ⟨a, hsuf, h⟩
  · cases u with
    | nil =>
      rcases S.hs st with hok | hnone
      · exact simStep_pre_silent (step_cons_some hok)
          (simStep_same l bs st S.hτ.symm hgen
            (fun a r' st' h => blockRel_in (Or.inr ⟨a, ⟨[], h.symm⟩, rfl⟩))
            (blockRel_entry S.hblk_fwd S.hent_fwd))
      · exact Or.inl (hstop st hc hd hnone)
    | cons a u' =>
      exact simStep_head l a _ _ st (hgen _)
        (fun st' => blockRel_in (Or.inl ⟨u', (List.suffix_cons a u').trans hu, rfl, rfl⟩))
  · rw [h]
    exact simStep_same l r₀ st S.hτ.symm hgen
      (fun a' r' st' h => blockRel_in (Or.inr ⟨a', by
        rw [← h]
        exact (List.suffix_cons a r₀).trans hsuf, rfl⟩))
      (blockRel_entry S.hblk_fwd S.hent_fwd)

end InsSetting

/-! ### Deleting a zero-size access -/

theorem deleteSetting {K : ZContract} {P : Prog} {l : Label} {i : Nat} {s : Stmt}
    (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    InsSetting K (deleteStmt P l i) P l ((P.blk l).stmts.take i)
        ((P.blk l).stmts.drop (i + 1)) s ∧
      (∀ st, P.at l i st = ⟨l, s :: (P.blk l).stmts.drop (i + 1), st⟩) ∧
      (∀ st, (deleteStmt P l i).at l i st = ⟨l, (P.blk l).stmts.drop (i + 1), st⟩) := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.1 hs
  have hl : l < P.length := by
    refine Nat.lt_of_not_le fun hle => ?_
    rw [blk_of_length_le hle] at hi
    simp [Block.unreach] at hi
  have hdrop : (P.blk l).stmts.drop i = s :: (P.blk l).stmts.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hget]
  have hTl : (deleteStmt P l i).blk l =
      { P.blk l with stmts := (P.blk l).stmts.eraseIdx i } := blk_set_self hl _
  have hT : ((deleteStmt P l i).blk l).stmts =
      (P.blk l).stmts.take i ++ (P.blk l).stmts.drop (i + 1) := by
    rw [hTl, List.eraseIdx_eq_take_drop_succ]
  refine ⟨⟨hT, ?_, by rw [hTl], fun l' h => (blk_set_ne h _).symm,
    execStmt_zeroSize_cases K hz⟩, fun st => ?_, fun st => ?_⟩
  · rw [← hdrop, List.take_append_drop]
  · simp only [Prog.at, hdrop]
  · simp only [Prog.at, hT]
    rw [List.drop_append_of_le_length (by simp; omega)]
    simp

section deletion

variable {K : ZContract} {P : Prog} {l : Label} {i : Nat} {s : Stmt}

theorem del_refinesPP (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    RefinesPP K P (deleteStmt P l i) := by
  obtain ⟨S, -, -⟩ := deleteSetting (K := K) hs hz
  exact refinesPP_of_sim S.sim_rev (fun _ h => goesWrong_of_step_ub h)
    (blockSim_init S.hblk S.hent_rev)

/-- The source reaching the deleted access is matched by the target reaching the point
after it, with the same trace. -/
theorem del_reach (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) {σ : State}
    {n : Nat} {t : List Int} {st : State}
    (h : run K P n (P.init σ) = .running (P.at l i st) t) :
    ∃ m, run K (deleteStmt P l i) m ((deleteStmt P l i).init σ) =
      .running ((deleteStmt P l i).at l i st) t := by
  obtain ⟨S, hPat, hTat⟩ := deleteSetting (K := K) hs hz
  rw [hPat] at h
  obtain ⟨m, d', hm, hR, -, -⟩ := sim_reach S.sim_rev (blockSim_init S.hblk S.hent_rev σ) h
    (fun c₀ h₀ => iso_of_step_ub h₀ _)
  obtain ⟨r, rfl, hρ⟩ := blockRel_inv hR
  rw [insRev_inv hρ] at hm
  exact ⟨m, by rw [hTat]; exact hm⟩

theorem del_step_ub (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) {st : State}
    (hpre : s.zeroPre K st = false) : GoesWrongFrom K P (P.at l i st) [] := by
  obtain ⟨-, hPat, -⟩ := deleteSetting (K := K) hs hz
  rw [hPat]
  exact goesWrong_of_step_ub (step_cons_none ((execStmt_zeroSize_none_iff K hz st).2 hpre))

theorem del_equivPP_iff (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    EquivPP K P (deleteStmt P l i) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        GoesWrongFrom K (deleteStmt P l i) ((deleteStmt P l i).at l i st) [] := by
  obtain ⟨S, hPat, hTat⟩ := deleteSetting (K := K) hs hz
  constructor
  · rintro ⟨-, hTP⟩ st ⟨σ, n, t, hn⟩ hpre
    obtain ⟨m, hm⟩ := del_reach hs hz hn
    exact goesWrong_nil_of_refinesPP hTP hn (del_step_ub hs hz hpre) hm
  · intro hcond
    refine ⟨del_refinesPP hs hz, refinesPP_of_sim
      (S.sim_fwd (Stop := fun c => GoesWrongFrom K (deleteStmt P l i) c [])
        (fun _ h => goesWrong_of_step_ub h) ?_) (fun _ h => h)
      (blockSim_init S.hblk_fwd S.hent_fwd)⟩
    intro st _ hP hnone
    have := hcond st (by rw [reachableAt_iff, hPat]; exact hP)
      ((execStmt_zeroSize_none_iff K hz st).1 hnone)
    rwa [hTat] at this

theorem del_equivWT_iff (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s) :
    EquivWT K P (deleteStmt P l i) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        ∃ t, GoesWrongFrom K (deleteStmt P l i) ((deleteStmt P l i).at l i st) t := by
  obtain ⟨S, hPat, hTat⟩ := deleteSetting (K := K) hs hz
  constructor
  · rintro ⟨-, hTP⟩ st ⟨σ, n, t, hn⟩ hpre
    obtain ⟨m, hm⟩ := del_reach hs hz hn
    exact goesWrong_of_refinesWT hTP hn (del_step_ub hs hz hpre) hm
  · intro hcond
    refine ⟨refinesWT_of_refinesPP (del_refinesPP hs hz), refinesWT_of_sim
      (S.sim_fwd (Stop := fun c => ∃ u, GoesWrongFrom K (deleteStmt P l i) c u)
        (fun _ h => ⟨[], goesWrong_of_step_ub h⟩) ?_) (fun _ h => h)
      (blockSim_init S.hblk_fwd S.hent_fwd)⟩
    intro st _ hP hnone
    obtain ⟨u, hu⟩ := hcond st (by rw [reachableAt_iff, hPat]; exact hP)
      ((execStmt_zeroSize_none_iff K hz st).1 hnone)
    exact ⟨u, by rwa [hTat] at hu⟩

theorem del_equivPP_of_zeroPre (hs : (P.blk l).stmts[i]? = some s) (hz : IsZeroSizeAccess s)
    (hpre : ∀ st, ReachableAt K P l i st → s.zeroPre K st = true) :
    EquivPP K P (deleteStmt P l i) :=
  (del_equivPP_iff hs hz).2 fun st hr hf => by
    have := hpre st hr
    rw [hf] at this
    cases this

theorem zeroPre_anyPtr (s : Stmt) (st : State) : s.zeroPre .anyPtr st = true := by
  cases s <;> simp [Stmt.zeroPre, ZContract.holds]

end deletion

/-! ### Inserting a zero-size access -/

theorem insertSetting {K : ZContract} {P : Prog} {l : Label} {i : Nat} {s : Stmt}
    (hl : l < P.length) (hz : IsZeroSizeAccess s) :
    InsSetting K P (insertStmt P l i s) l ((P.blk l).stmts.take i) ((P.blk l).stmts.drop i) s := by
  have hI : (insertStmt P l i s).blk l =
      ⟨(P.blk l).stmts.take i ++ s :: (P.blk l).stmts.drop i, (P.blk l).term⟩ :=
    blk_set_self hl _
  exact ⟨(List.take_append_drop i _).symm, by rw [hI], by rw [hI], fun l' h => blk_set_ne h _,
    execStmt_zeroSize_cases K hz⟩

theorem insertStmt_of_length_le {P : Prog} {l : Label} (i : Nat) (s : Stmt)
    (hl : P.length ≤ l) : insertStmt P l i s = P :=
  List.set_eq_of_length_le hl

theorem goesWrong_at_of_length_le {K : ZContract} {P : Prog} {l : Label} (i : Nat) (st : State)
    (hl : P.length ≤ l) : GoesWrongFrom K P (P.at l i st) [] :=
  goesWrong_of_step_ub (by simp [Prog.at, step, blk_of_length_le hl, Block.unreach])

section insertion

variable {K : ZContract} {P : Prog} {l : Label} {i : Nat} {s : Stmt}

/-- The stops used for the necessity direction: actual UB of the source, or the insertion
point in a state where the inserted access fails. -/
def insSpecial (K : ZContract) (P : Prog) (l : Label) (i : Nat) (s : Stmt) (c : Cfg) : Prop :=
  ∃ st', c = ⟨l, (P.blk l).stmts.drop i, st'⟩ ∧ s.zeroPre K st' = false

theorem ins_sim_special (hl : l < P.length) (hz : IsZeroSizeAccess s) :
    IsSim K P (insertStmt P l i s)
      (RelR K P (insertStmt P l i s) (BlockRel l (InsFwd ((P.blk l).stmts.take i)
        ((P.blk l).stmts.drop i) s))) stutterμ
      (fun c => step K P c = .ub ∨ insSpecial K P l i s c) 1 :=
  (insertSetting (K := K) hl hz).sim_fwd (fun _ h => Or.inl h)
    (fun st' _ _ hnone => Or.inr ⟨st', rfl, (execStmt_zeroSize_none_iff K hz st').1 hnone⟩)

theorem ins_special_wrong (hz : IsZeroSizeAccess s) :
    ∀ c d, insSpecial K P l i s c →
      RelR K P (insertStmt P l i s) (BlockRel l (InsFwd ((P.blk l).stmts.take i)
        ((P.blk l).stmts.drop i) s)) c d → GoesWrongFrom K (insertStmt P l i s) d [] := by
  rintro c d ⟨st', rfl, hpre⟩ ⟨hR, -, -⟩
  obtain ⟨r, rfl, hρ⟩ := blockRel_inv hR
  rw [insFwd_inv hρ]
  exact goesWrong_of_step_ub (step_cons_none ((execStmt_zeroSize_none_iff K hz st').2 hpre))

theorem ins_refinesPP_iff (hz : IsZeroSizeAccess s) :
    RefinesPP K P (insertStmt P l i s) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        GoesWrongFrom K P (P.at l i st) [] := by
  by_cases hl : l < P.length
  · have S := insertSetting (K := K) (i := i) hl hz
    constructor
    · intro href st hr hpre
      exact goesWrong_nil_of_sim_necessity (ins_sim_special hl hz) (fun _ h => h)
        (ins_special_wrong hz) (blockSim_init S.hblk_fwd S.hent_fwd) href hr ⟨st, rfl, hpre⟩
    · intro hcond
      exact refinesPP_of_sim (S.sim_fwd (Stop := fun c => GoesWrongFrom K P c [])
        (fun _ h => goesWrong_of_step_ub h)
        (fun st hP _ hnone => hcond st hP ((execStmt_zeroSize_none_iff K hz st).1 hnone)))
        (fun _ h => h) (blockSim_init S.hblk_fwd S.hent_fwd)
  · rw [insertStmt_of_length_le i s (Nat.le_of_not_lt hl)]
    exact iff_of_true (refinesPP_refl K P)
      fun st _ _ => goesWrong_at_of_length_le i st (Nat.le_of_not_lt hl)

theorem ins_refinesWT_iff (hz : IsZeroSizeAccess s) :
    RefinesWT K P (insertStmt P l i s) ↔
      ∀ st, ReachableAt K P l i st → s.zeroPre K st = false →
        ∃ t, GoesWrongFrom K P (P.at l i st) t := by
  by_cases hl : l < P.length
  · have S := insertSetting (K := K) (i := i) hl hz
    constructor
    · intro href st hr hpre
      exact goesWrong_of_sim_necessity (ins_sim_special hl hz) (fun _ h => h)
        (ins_special_wrong hz) (blockSim_init S.hblk_fwd S.hent_fwd) href hr ⟨st, rfl, hpre⟩
    · intro hcond
      exact refinesWT_of_sim (S.sim_fwd (Stop := fun c => ∃ u, GoesWrongFrom K P c u)
        (fun _ h => ⟨[], goesWrong_of_step_ub h⟩)
        (fun st hP _ hnone => hcond st hP ((execStmt_zeroSize_none_iff K hz st).1 hnone)))
        (fun _ h => h) (blockSim_init S.hblk_fwd S.hent_fwd)
  · rw [insertStmt_of_length_le i s (Nat.le_of_not_lt hl)]
    exact iff_of_true (refinesWT_refl K P)
      fun st _ _ => ⟨[], goesWrong_at_of_length_le i st (Nat.le_of_not_lt hl)⟩

theorem ins_equivPP_of_zeroPre (hz : IsZeroSizeAccess s)
    (hpre : ∀ st, ReachableAt K P l i st → s.zeroPre K st = true) :
    EquivPP K P (insertStmt P l i s) := by
  by_cases hl : l < P.length
  · have S := insertSetting (K := K) (i := i) hl hz
    refine ⟨(ins_refinesPP_iff hz).2 fun st hr hf => ?_, refinesPP_of_sim S.sim_rev
      (fun _ h => goesWrong_of_step_ub h) (blockSim_init S.hblk S.hent_rev)⟩
    have := hpre st hr
    rw [hf] at this
    cases this
  · rw [insertStmt_of_length_le i s (Nat.le_of_not_lt hl)]
    exact ⟨refinesPP_refl K P, refinesPP_refl K P⟩

end insertion

/-! ### Changing the terminator of one block -/

/-- Equal remaining statements. -/
def EqRest (r₁ r₂ : List Stmt) (_ : State) : Prop := r₁ = r₂

/-- A simulation between programs that differ only in the terminator of block `l`, from
the obligation at that terminator. -/
theorem termSim {K : ZContract} {L Rt : Prog} {l : Label} {Stop : Cfg → Prop}
    (hblk : ∀ l', l' ≠ l → L.blk l' = Rt.blk l') (hstm : (L.blk l).stmts = (Rt.blk l).stmts)
    (hgen : ∀ c, step K L c = .ub → Stop c)
    (hterm : ∀ st, Reach K L ⟨l, [], st⟩ → Reach K Rt ⟨l, [], st⟩ →
      SimStep K L Rt (BlockRel l EqRest) (fun _ _ => 0) Stop ⟨l, [], st⟩ ⟨l, [], st⟩) :
    IsSim K L Rt (RelR K L Rt (BlockRel l EqRest)) (fun _ _ => 0) Stop 0 := by
  refine blockSim hblk (fun _ => hstm) (fun _ _ => Nat.le_refl 0) hgen ?_
  intro r₁ r₂ st h hc hd
  cases h
  cases r₁ with
  | cons a r => exact simStep_head l a r r st (hgen _) (fun _ => blockRel_in rfl)
  | nil => exact hterm st hc hd

theorem eqRest_at_inv {K : ZContract} {L Rt : Prog} {l : Label} {st : State} {d : Cfg}
    (h : RelR K L Rt (BlockRel l EqRest) ⟨l, [], st⟩ d) : d = ⟨l, [], st⟩ := by
  obtain ⟨r, rfl, hρ⟩ := blockRel_inv h.1
  cases hρ
  rfl

theorem goesWrong_of_next_silent {K : ZContract} {P : Prog} {c c' : Cfg} {u : List Int}
    (h : step K P c = .next none c') (hw : GoesWrongFrom K P c' u) : GoesWrongFrom K P c u := by
  obtain ⟨n, hn⟩ := hw
  exact ⟨n + 1, by rw [run_succ_next n h, cons_none, hn]⟩

theorem goesWrong_of_next_silent_rev {K : ZContract} {P : Prog} {c c' : Cfg} {u : List Int}
    (h : step K P c = .next none c') (hw : GoesWrongFrom K P c u) : GoesWrongFrom K P c' u := by
  obtain ⟨n, hn⟩ := hw
  cases n with
  | zero => cases hn
  | succ n =>
    rw [run_succ_next n h, cons_none] at hn
    exact ⟨n, hn⟩

theorem goesWrong_unreachBlock {K : ZContract} {P : Prog} {u : Label} (hU : IsUnreachableBlock P u)
    (st : State) : GoesWrongFrom K P (P.entry u st) [] := by
  unfold IsUnreachableBlock at hU
  exact goesWrong_of_step_ub (by simp [Prog.entry, step, hU, Block.unreach])

theorem selectTarget_dropArms_ne (arms : List (Int × Label)) (ow : Label) {v y : Int}
    (h : y ≠ v) : selectTarget (dropArms arms v) ow y = selectTarget arms ow y := by
  induction arms with
  | nil => rfl
  | cons a arms ih =>
    obtain ⟨w, b⟩ := a
    simp only [dropArms, List.filter_cons] at ih ⊢
    by_cases hw : w = v
    · subst hw
      have hyw : ¬ y = w := h
      simp [selectTarget, hyw, ih]
    · simp [hw, selectTarget, ih]

theorem selectTarget_dropArms_self (arms : List (Int × Label)) (ow : Label) (v : Int) :
    selectTarget (dropArms arms v) ow v = ow := by
  induction arms with
  | nil => rfl
  | cons a arms ih =>
    obtain ⟨w, b⟩ := a
    simp only [dropArms, List.filter_cons] at ih ⊢
    by_cases hw : w = v
    · simp [hw, ih]
    · have hvw : ¬ v = w := fun e => hw e.symm
      simp [hw, selectTarget, hvw, ih]

/-! ### Pruning a switch arm without `assume` -/

section pruneArm

variable {K : ZContract} {P : Prog} {l : Label} {x : Var} {arms : List (Int × Label)}
  {ow : Label} {v : Int}

theorem pruneArm_blk (hterm : (P.blk l).term = .switch x arms ow) :
    l < P.length ∧ (pruneArm P l v).blk l = ⟨(P.blk l).stmts, .switch x (dropArms arms v) ow⟩ ∧
      ∀ l', l' ≠ l → (pruneArm P l v).blk l' = P.blk l' := by
  have hl : l < P.length := length_of_blk_ne_unreach fun h => by
    rw [h] at hterm; cases hterm
  have he : pruneArm P l v = setTerm P l (.switch x (dropArms arms v) ow) := by
    simp only [pruneArm, hterm]
  rw [he]
  exact ⟨hl, blk_set_self hl _, fun l' h => blk_set_ne h _⟩

theorem pruneArm_step_P (hterm : (P.blk l).term = .switch x arms ow) (st : State) :
    step K P ⟨l, [], st⟩ = .next none (P.entry (selectTarget arms ow (st.locals x)) st) := by
  simp [step, hterm]

theorem pruneArm_step_Q (hterm : (P.blk l).term = .switch x arms ow) (st : State) :
    step K (pruneArm P l v) ⟨l, [], st⟩ =
      .next none ((pruneArm P l v).entry (selectTarget (dropArms arms v) ow (st.locals x)) st) := by
  simp [step, (pruneArm_blk (v := v) hterm).2.1]

theorem pruneArm_target_ne {st : State} (h : st.locals x ≠ v) :
    selectTarget (dropArms arms v) ow (st.locals x) = selectTarget arms ow (st.locals x) :=
  selectTarget_dropArms_ne arms ow h

theorem unreach_ne_of_switch (hterm : (P.blk l).term = .switch x arms ow) {u : Label}
    (hU : IsUnreachableBlock P u) : u ≠ l := by
  rintro rfl
  unfold IsUnreachableBlock at hU
  rw [hU] at hterm
  cases hterm

/-- At the switch with `x = v`, the source goes wrong silently (its arm leads to an
unreachable block). -/
theorem pruneArm_src_wrong (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) {st : State} (h : st.locals x = v) :
    GoesWrongFrom K P ⟨l, [], st⟩ [] := by
  refine goesWrong_of_next_silent (pruneArm_step_P hterm st) ?_
  rw [h]
  exact goesWrong_unreachBlock hU st

/-- The source simulated by the pruned program. -/
theorem pruneArm_sim_PQ (hterm : (P.blk l).term = .switch x arms ow) {Stop : Cfg → Prop}
    (hgen : ∀ c, step K P c = .ub → Stop c)
    (hbad : ∀ st, Reach K P ⟨l, [], st⟩ → st.locals x = v → Stop ⟨l, [], st⟩) :
    IsSim K P (pruneArm P l v) (RelR K P (pruneArm P l v) (BlockRel l EqRest)) (fun _ _ => 0)
      Stop 0 := by
  obtain ⟨-, hQl, hQ⟩ := pruneArm_blk (v := v) hterm
  have hblk : ∀ l', l' ≠ l → P.blk l' = (pruneArm P l v).blk l' := fun l' h => (hQ l' h).symm
  have hstm : (P.blk l).stmts = ((pruneArm P l v).blk l).stmts := by rw [hQl]
  have hent : ∀ st, EqRest (P.blk l).stmts ((pruneArm P l v).blk l).stmts st := fun _ => hstm
  refine termSim hblk hstm hgen fun st hc _ => ?_
  by_cases hx : st.locals x = v
  · exact Or.inl (hbad st hc hx)
  · refine simStep_target _ st (pruneArm_step_P hterm st) ?_ (blockRel_entry hblk hent _ st)
    rw [pruneArm_step_Q hterm st, pruneArm_target_ne hx]

/-- The pruned program simulated by the source. -/
theorem pruneArm_sim_QP (hterm : (P.blk l).term = .switch x arms ow) {Stop : Cfg → Prop}
    (hgen : ∀ c, step K (pruneArm P l v) c = .ub → Stop c)
    (hbad : ∀ st, Reach K P ⟨l, [], st⟩ → st.locals x = v → Stop ⟨l, [], st⟩) :
    IsSim K (pruneArm P l v) P (RelR K (pruneArm P l v) P (BlockRel l EqRest)) (fun _ _ => 0)
      Stop 0 := by
  obtain ⟨-, hQl, hQ⟩ := pruneArm_blk (v := v) hterm
  have hstm : ((pruneArm P l v).blk l).stmts = (P.blk l).stmts := by rw [hQl]
  have hent : ∀ st, EqRest ((pruneArm P l v).blk l).stmts (P.blk l).stmts st := fun _ => hstm
  refine termSim hQ hstm hgen fun st _ hd => ?_
  by_cases hx : st.locals x = v
  · exact Or.inl (hbad st hd hx)
  · refine simStep_target _ st ?_ (pruneArm_step_P hterm st) (blockRel_entry hQ hent _ st)
    rw [pruneArm_step_Q hterm st, pruneArm_target_ne hx]

theorem pruneArm_at_len {P : Prog} {l : Label} (st : State) : P.at l (P.blk l).stmts.length st = ⟨l, [], st⟩ := by
  simp [Prog.at]

theorem pa_refinesPP (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) : RefinesPP K P (pruneArm P l v) := by
  have hblk := (pruneArm_blk (v := v) hterm).2.2
  exact refinesPP_of_sim (pruneArm_sim_PQ hterm (Stop := fun c => GoesWrongFrom K P c [])
      (fun _ h => goesWrong_of_step_ub h) fun st _ hx => pruneArm_src_wrong hterm hU hx)
    (fun _ h => h) (blockSim_init (fun l' h => (hblk l' h).symm)
      (fun st => by rw [(pruneArm_blk (v := v) hterm).2.1]; rfl))

theorem pa_wp (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) (Q : List Int → State → Prop)
    (σ : State) : wp K P Q σ → wp K (pruneArm P l v) Q σ := by
  have hblk := (pruneArm_blk (v := v) hterm).2.2
  exact wp_of_sim (pruneArm_sim_PQ hterm (Stop := fun c => GoesWrongFrom K P c [])
      (fun _ h => goesWrong_of_step_ub h) fun st _ hx => pruneArm_src_wrong hterm hU hx)
    (fun c h => ⟨[], h⟩) (blockSim_init (fun l' h => (hblk l' h).symm)
      (fun st => by rw [(pruneArm_blk (v := v) hterm).2.1]; rfl)) Q σ

/-- The source reaching the switch of block `l` is matched by the pruned program reaching
the same configuration with the same trace. -/
theorem pa_reach (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) {σ : State} {n : Nat} {t : List Int}
    {st : State} (h : run K P n (P.init σ) = .running ⟨l, [], st⟩ t) :
    ∃ m, run K (pruneArm P l v) m ((pruneArm P l v).init σ) = .running ⟨l, [], st⟩ t := by
  have hblk := (pruneArm_blk (v := v) hterm).2.2
  have hS := pruneArm_sim_PQ hterm
    (Stop := fun c => step K P c = .ub ∨ (c.lbl = l ∧ c.rest = [] ∧ c.st.locals x = v))
    (fun _ h => Or.inl h) (fun st _ hx => Or.inr ⟨rfl, rfl, hx⟩)
  have hu := unreach_ne_of_switch hterm hU
  have hiso : ∀ c₀, (step K P c₀ = .ub ∨ (c₀.lbl = l ∧ c₀.rest = [] ∧ c₀.st.locals x = v)) →
      ∀ j u, run K P (j + 1) c₀ ≠ .running ⟨l, [], st⟩ u := by
    rintro c₀ (hub | ⟨hl₀, hr₀, hx₀⟩) j u
    · exact iso_of_step_ub hub _ j u
    rcases c₀ with ⟨l₀, r₀, st₀⟩
    simp only at hl₀ hr₀ hx₀
    subst hl₀ hr₀
    rw [run_succ_next j (pruneArm_step_P hterm st₀), hx₀]
    cases j with
    | zero =>
      intro e
      simp only [run, Outcome.cons, Prog.entry] at e
      injection e with e1 _
      injection e1 with e3 _ _
      exact hu e3
    | succ j =>
      have : step K P (P.entry (selectTarget arms ow v) st₀) = .ub := by
        unfold IsUnreachableBlock at hU
        simp [Prog.entry, step, hU, Block.unreach]
      rw [run_succ_ub j this]
      intro e
      cases e
  obtain ⟨m, d', hm, hR⟩ := sim_reach hS (blockSim_init (fun l' h => (hblk l' h).symm)
      (fun st => by rw [(pruneArm_blk (v := v) hterm).2.1]; rfl) σ) h hiso
  rw [eqRest_at_inv hR] at hm
  exact ⟨m, hm⟩

theorem pa_equivPP_iff (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    EquivPP K P (pruneArm P l v) ↔
      ∀ st, ReachableAt K P l (P.blk l).stmts.length st → st.locals x = v →
        GoesWrongFrom K (pruneArm P l v) ((pruneArm P l v).entry ow st) [] := by
  obtain ⟨-, hQl, hQ⟩ := pruneArm_blk (v := v) hterm
  constructor
  · rintro ⟨-, hQP⟩ st ⟨σ, n, t, hn⟩ hx
    rw [pruneArm_at_len] at hn
    obtain ⟨m, hm⟩ := pa_reach hterm hU hn
    have hw := goesWrong_nil_of_refinesPP hQP hn (pruneArm_src_wrong hterm hU hx) hm
    have hs := pruneArm_step_Q (K := K) (v := v) hterm st
    rw [hx, selectTarget_dropArms_self] at hs
    exact goesWrong_of_next_silent_rev hs hw
  · intro hcond
    refine ⟨pa_refinesPP hterm hU, refinesPP_of_sim
      (pruneArm_sim_QP hterm (Stop := fun c => GoesWrongFrom K (pruneArm P l v) c [])
        (fun _ h => goesWrong_of_step_ub h) fun st hd hx => ?_)
      (fun _ h => h) (blockSim_init hQ (fun st => by rw [hQl]; rfl))⟩
    have hs := pruneArm_step_Q (K := K) (v := v) hterm st
    rw [hx, selectTarget_dropArms_self] at hs
    exact goesWrong_of_next_silent hs (hcond st (by rw [reachableAt_iff, pruneArm_at_len]; exact hd) hx)

theorem pa_equivWT_iff (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) :
    EquivWT K P (pruneArm P l v) ↔
      ∀ st, ReachableAt K P l (P.blk l).stmts.length st → st.locals x = v →
        ∃ t, GoesWrongFrom K (pruneArm P l v) ((pruneArm P l v).entry ow st) t := by
  obtain ⟨-, hQl, hQ⟩ := pruneArm_blk (v := v) hterm
  constructor
  · rintro ⟨-, hQP⟩ st ⟨σ, n, t, hn⟩ hx
    rw [pruneArm_at_len] at hn
    obtain ⟨m, hm⟩ := pa_reach hterm hU hn
    obtain ⟨u, hw⟩ := goesWrong_of_refinesWT hQP hn (pruneArm_src_wrong hterm hU hx) hm
    have hs := pruneArm_step_Q (K := K) (v := v) hterm st
    rw [hx, selectTarget_dropArms_self] at hs
    exact ⟨u, goesWrong_of_next_silent_rev hs hw⟩
  · intro hcond
    refine ⟨refinesWT_of_refinesPP (pa_refinesPP hterm hU), refinesWT_of_sim
      (pruneArm_sim_QP hterm (Stop := fun c => ∃ u, GoesWrongFrom K (pruneArm P l v) c u)
        (fun _ h => ⟨[], goesWrong_of_step_ub h⟩) fun st hd hx => ?_)
      (fun _ h => h) (blockSim_init hQ (fun st => by rw [hQl]; rfl))⟩
    have hs := pruneArm_step_Q (K := K) (v := v) hterm st
    rw [hx, selectTarget_dropArms_self] at hs
    obtain ⟨u, hu⟩ := hcond st (by rw [reachableAt_iff, pruneArm_at_len]; exact hd) hx
    exact ⟨u, goesWrong_of_next_silent hs hu⟩

theorem pa_ow_wrong (hterm : (P.blk l).term = .switch x arms ow) (hOw : IsUnreachableBlock P ow)
    (st : State) : GoesWrongFrom K (pruneArm P l v) ((pruneArm P l v).entry ow st) [] := by
  have hne := unreach_ne_of_switch hterm hOw
  have : IsUnreachableBlock (pruneArm P l v) ow := by
    unfold IsUnreachableBlock at hOw ⊢
    rw [(pruneArm_blk (v := v) hterm).2.2 ow hne, hOw]
  exact goesWrong_unreachBlock this st

theorem pa_equivPP_of_invariant (hterm : (P.blk l).term = .switch x arms ow)
    (hinv : ∀ st, ReachableAt K P l (P.blk l).stmts.length st → st.locals x ≠ v) :
    EquivPP K P (pruneArm P l v) := by
  obtain ⟨-, hQl, hQ⟩ := pruneArm_blk (v := v) hterm
  have hbad : ∀ (Stop : Cfg → Prop) st, Reach K P ⟨l, [], st⟩ → st.locals x = v →
      Stop ⟨l, [], st⟩ := fun _ st hc hx =>
    absurd hx (hinv st (by rw [reachableAt_iff, pruneArm_at_len]; exact hc))
  refine ⟨refinesPP_of_sim (pruneArm_sim_PQ hterm (Stop := fun c => step K P c = .ub)
      (fun _ h => h) (hbad (fun c => step K P c = .ub))) (fun _ h => goesWrong_of_step_ub h)
      (blockSim_init (fun l' h => (hQ l' h).symm) (fun st => by rw [hQl]; rfl)),
    refinesPP_of_sim (pruneArm_sim_QP hterm (Stop := fun c => step K (pruneArm P l v) c = .ub)
      (fun _ h => h) (hbad (fun c => step K (pruneArm P l v) c = .ub)))
      (fun _ h => goesWrong_of_step_ub h) (blockSim_init hQ (fun st => by rw [hQl]; rfl))⟩

end pruneArm

/-! ### Appending an `assume` before a changed terminator -/

/-- Remaining statements of block `l` when the right program appends `a` to the block. -/
def AppFwd (xs : List Stmt) (a : Stmt) (r₀ r₁ : List Stmt) (_ : State) : Prop :=
  r₀ <:+ xs ∧ r₁ = r₀ ++ [a]

/-- Remaining statements of block `l` when the left program appends `a` to the block;
after a successful `a` both are at the terminator. -/
def AppRev (K : ZContract) (xs : List Stmt) (a : Stmt) (r₁ r₀ : List Stmt) (st : State) :
    Prop :=
  (r₀ <:+ xs ∧ r₁ = r₀ ++ [a]) ∨ (r₁ = [] ∧ r₀ = [] ∧ execStmt K a st = some (none, st))

/-- `A` is `P` with the statement `a` appended to block `l` and a terminator that, whenever
`a` succeeds, jumps to the same label as `P`'s terminator. -/
structure AppSetting (K : ZContract) (P A : Prog) (l : Label) (a : Stmt) : Prop where
  hA : (A.blk l).stmts = (P.blk l).stmts ++ [a]
  hblk : ∀ l', l' ≠ l → A.blk l' = P.blk l'
  ha : ∀ st, execStmt K a st = some (none, st) ∨ execStmt K a st = none
  hgood : ∀ st, execStmt K a st = some (none, st) → ∃ b,
    step K P ⟨l, [], st⟩ = .next none (P.entry b st) ∧
      step K A ⟨l, [], st⟩ = .next none (A.entry b st)

namespace AppSetting

variable {K : ZContract} {P A : Prog} {l : Label} {a : Stmt}

theorem hent_fwd (S : AppSetting K P A l a) (st : State) :
    AppFwd (P.blk l).stmts a (P.blk l).stmts (A.blk l).stmts st :=
  ⟨List.suffix_refl _, S.hA⟩

theorem hent_rev (S : AppSetting K P A l a) (st : State) :
    AppRev K (P.blk l).stmts a (A.blk l).stmts (P.blk l).stmts st :=
  Or.inl ⟨List.suffix_refl _, S.hA⟩

theorem hblk_fwd (S : AppSetting K P A l a) : ∀ l', l' ≠ l → P.blk l' = A.blk l' :=
  fun l' h => (S.hblk l' h).symm

/-- `P` simulated by `A`, stopping (at least) where the appended statement fails. -/
theorem sim_fwd (S : AppSetting K P A l a) {Stop : Cfg → Prop}
    (hgen : ∀ c, step K P c = .ub → Stop c)
    (hbad : ∀ st, Reach K P ⟨l, [], st⟩ → execStmt K a st = none → Stop ⟨l, [], st⟩) :
    IsSim K P A (RelR K P A (BlockRel l (AppFwd (P.blk l).stmts a))) stutterμ Stop 1 := by
  refine blockSim S.hblk_fwd S.hent_fwd stutterμ_le hgen ?_
  rintro r₀ r₁ st ⟨hsuf, rfl⟩ hc _
  cases r₀ with
  | cons b r' =>
    exact simStep_head l b r' (r' ++ [a]) st (hgen _)
      (fun _ => blockRel_in ⟨(List.suffix_cons b r').trans hsuf, rfl⟩)
  | nil =>
    rcases S.ha st with hok | hnone
    · obtain ⟨b, hP, hA'⟩ := S.hgood st hok
      exact simStep_pre_silent (step_cons_some hok)
        (simStep_target b st hP hA' (blockRel_entry S.hblk_fwd S.hent_fwd b st))
    · exact Or.inl (hbad st hc hnone)

/-- `A` simulated by `P`, the appended statement being a stutter step. -/
theorem sim_rev (S : AppSetting K P A l a) :
    IsSim K A P (RelR K A P (BlockRel l (AppRev K (P.blk l).stmts a))) stutterμ
      (fun c => step K A c = .ub) 1 := by
  refine blockSim S.hblk S.hent_rev stutterμ_le (fun _ h => h) ?_
  rintro r₁ r₀ st (⟨hsuf, rfl⟩ | ⟨rfl, rfl, hok⟩) _ _
  · cases r₀ with
    | cons b r' =>
      exact simStep_head l b (r' ++ [a]) r' st (fun h => h)
        (fun _ => blockRel_in (Or.inl ⟨(List.suffix_cons b r').trans hsuf, rfl⟩))
    | nil =>
      exact simStep_stutter l a [] st ⟨l, [], st⟩ (S.ha st) (fun h => h)
        (fun hok => blockRel_in (Or.inr ⟨rfl, rfl, hok⟩)) rfl
  · obtain ⟨b, hP, hA'⟩ := S.hgood st hok
    exact simStep_target b st hA' hP (blockRel_entry S.hblk S.hent_rev b st)

theorem equivPP (S : AppSetting K P A l a)
    (hbad : ∀ st, execStmt K a st = none → GoesWrongFrom K P ⟨l, [], st⟩ []) :
    EquivPP K P A :=
  ⟨refinesPP_of_sim (S.sim_fwd (Stop := fun c => GoesWrongFrom K P c [])
      (fun _ h => goesWrong_of_step_ub h) (fun st _ h => hbad st h)) (fun _ h => h)
      (blockSim_init S.hblk_fwd S.hent_fwd),
    refinesPP_of_sim S.sim_rev (fun _ h => goesWrong_of_step_ub h)
      (blockSim_init S.hblk S.hent_rev)⟩

theorem wp_iff (S : AppSetting K P A l a)
    (hbad : ∀ st, execStmt K a st = none → GoesWrongFrom K P ⟨l, [], st⟩ [])
    (Q : List Int → State → Prop) (σ : State) : wp K A Q σ ↔ wp K P Q σ :=
  ⟨wp_of_sim S.sim_rev (fun _ h => ⟨[], goesWrong_of_step_ub h⟩)
      (blockSim_init S.hblk S.hent_rev) Q σ,
    wp_of_sim (S.sim_fwd (Stop := fun c => GoesWrongFrom K P c [])
      (fun _ h => goesWrong_of_step_ub h) (fun st _ h => hbad st h)) (fun _ h => ⟨[], h⟩)
      (blockSim_init S.hblk_fwd S.hent_fwd) Q σ⟩

/-- A configuration of `P` related to the program point `(l', i')` of `A` is the same
program point of `P`. -/
theorem at_inv (S : AppSetting K P A l a) {l' : Label} {i' : Nat} {st : State} {d : Cfg}
    (h : RelR K A P (BlockRel l (AppRev K (P.blk l).stmts a)) (A.at l' i' st) d) :
    d = P.at l' i' st := by
  obtain ⟨hR, -, -⟩ := h
  by_cases hl : l' = l
  · subst hl
    obtain ⟨r, rfl, hρ⟩ := blockRel_inv (r₁ := ((A.blk l').stmts).drop i') hR
    rw [S.hA] at hρ
    have hr : r = (P.blk l').stmts.drop i' := by
      rcases hρ with ⟨-, he⟩ | ⟨he, rfl, -⟩
      · by_cases hi : i' ≤ (P.blk l').stmts.length
        · rw [List.drop_append_of_le_length hi] at he
          exact (List.append_cancel_right he).symm
        · rw [List.drop_eq_nil_of_le (by simp; omega)] at he
          simp at he
      · rw [List.drop_eq_nil_iff] at he
        simp at he
        exact (List.drop_eq_nil_of_le (by omega)).symm
    rw [hr]
    rfl
  · rw [blockRel_inv_ne hR hl]
    simp only [Prog.at, S.hblk l' hl]

end AppSetting

theorem assume_ne_ok {K : ZContract} {x : Var} {v : Int} {st : State}
    (h : execStmt K (.assume (.ne x v)) st = some (none, st)) : st.locals x ≠ v := by
  intro hx
  rw [execStmt_assume] at h
  simp [Cond.eval, hx] at h

theorem assume_ne_none {K : ZContract} {x : Var} {v : Int} {st : State}
    (h : execStmt K (.assume (.ne x v)) st = none) : st.locals x = v := by
  refine Classical.byContradiction fun hx => ?_
  rw [execStmt_assume] at h
  simp [Cond.eval, hx] at h

theorem assume_eq_ok {K : ZContract} {x : Var} {v : Int} {st : State}
    (h : execStmt K (.assume (.eq x v)) st = some (none, st)) : st.locals x = v := by
  refine Classical.byContradiction fun hx => ?_
  rw [execStmt_assume] at h
  simp [Cond.eval, hx] at h

theorem assume_eq_none {K : ZContract} {x : Var} {v : Int} {st : State}
    (h : execStmt K (.assume (.eq x v)) st = none) : st.locals x ≠ v := by
  intro hx
  rw [execStmt_assume] at h
  simp [Cond.eval, hx] at h

/-! ### Pruning a switch arm with `assume` -/

section pruneArmAssume

variable {K : ZContract} {P : Prog} {l : Label} {x : Var} {arms : List (Int × Label)}
  {ow : Label} {v : Int}

theorem pruneArmAssume_setting (hterm : (P.blk l).term = .switch x arms ow) :
    AppSetting K P (pruneArmAssume P l v) l (.assume (.ne x v)) := by
  have hl : l < P.length := length_of_blk_ne_unreach fun h => by
    rw [h] at hterm; cases hterm
  have he : pruneArmAssume P l v =
      P.set l ⟨(P.blk l).stmts ++ [.assume (.ne x v)], .switch x (dropArms arms v) ow⟩ := by
    simp only [pruneArmAssume, hterm]
  have hAl : (pruneArmAssume P l v).blk l =
      ⟨(P.blk l).stmts ++ [.assume (.ne x v)], .switch x (dropArms arms v) ow⟩ := by
    rw [he]; exact blk_set_self hl _
  refine ⟨by rw [hAl], fun l' h => by rw [he]; exact blk_set_ne h _,
    execStmt_assume_cases K _, fun st hok => ?_⟩
  have hx := assume_ne_ok hok
  exact ⟨selectTarget arms ow (st.locals x), by simp [step, hterm],
    by simp [step, hAl, selectTarget_dropArms_ne arms ow hx]⟩

theorem paa_equivPP (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) : EquivPP K P (pruneArmAssume P l v) :=
  (pruneArmAssume_setting hterm).equivPP fun _ h => pruneArm_src_wrong hterm hU (assume_ne_none h)

theorem paa_wp_iff (hterm : (P.blk l).term = .switch x arms ow)
    (hU : IsUnreachableBlock P (selectTarget arms ow v)) (Q : List Int → State → Prop)
    (σ : State) : wp K (pruneArmAssume P l v) Q σ ↔ wp K P Q σ :=
  (pruneArmAssume_setting hterm).wp_iff
    (fun _ h => pruneArm_src_wrong hterm hU (assume_ne_none h)) Q σ

end pruneArmAssume

theorem pruneArmAssume_eq_self {P : Prog} {l : Label} {v : Int}
    (h : ∀ x arms ow, (P.blk l).term ≠ .switch x arms ow) : pruneArmAssume P l v = P := by
  unfold pruneArmAssume
  split
  · rename_i x arms ow heq
    exact absurd heq (h x arms ow)
  · rfl

theorem paa_fact {K : ZContract} {P : Prog} {l : Label} {v : Int} {l' : Label} {i' : Nat}
    {F : State → Prop} (hF : FactOnDefinedRuns K P l' i' F) :
    FactOnDefinedRuns K (pruneArmAssume P l v) l' i' F := by
  by_cases hsw : ∃ x arms ow, (P.blk l).term = .switch x arms ow
  · obtain ⟨x, arms, ow, hterm⟩ := hsw
    have S := pruneArmAssume_setting (K := K) (v := v) hterm
    rintro σ st ⟨n, t, hn⟩ hnw
    obtain ⟨m, d', hm, hR⟩ := sim_reach S.sim_rev (blockSim_init S.hblk S.hent_rev σ) hn
      (fun c₀ h₀ => iso_of_step_ub h₀ _)
    rw [S.at_inv hR] at hm
    refine hF σ st ⟨m, t, hm⟩ fun t' hw => ?_
    obtain ⟨b, hb⟩ := hasBehFrom_exists K (pruneArmAssume P l v) ((pruneArmAssume P l v).init σ)
    have hnwb : ∀ t'', b ≠ .wrong t'' := fun t'' h => hnw t'' (h ▸ hb)
    have hb' := sim_beh_of_not_wrong S.sim_rev (fun _ h => ⟨[], goesWrong_of_step_ub h⟩)
      (blockSim_init S.hblk S.hent_rev σ) hb hnwb
    exact hnwb t' (hasBehFrom_unique hb' hw)
  · rw [pruneArmAssume_eq_self fun x arms ow h => hsw ⟨x, arms, ow, h⟩]
    exact hF

/-! ### The single-arm shape with unreachable `otherwise` -/

section pruneOtherwiseAssume

variable {K : ZContract} {P : Prog} {l : Label} {x : Var} {v : Int} {b ow : Label}

theorem pruneOtherwiseAssume_setting (hterm : (P.blk l).term = .switch x [(v, b)] ow) :
    AppSetting K P (pruneOtherwiseAssume P l) l (.assume (.eq x v)) := by
  have hl : l < P.length := length_of_blk_ne_unreach fun h => by
    rw [h] at hterm; cases hterm
  have he : pruneOtherwiseAssume P l =
      P.set l ⟨(P.blk l).stmts ++ [.assume (.eq x v)], .goto b⟩ := by
    simp only [pruneOtherwiseAssume, hterm]
  have hAl : (pruneOtherwiseAssume P l).blk l =
      ⟨(P.blk l).stmts ++ [.assume (.eq x v)], .goto b⟩ := by
    rw [he]; exact blk_set_self hl _
  refine ⟨by rw [hAl], fun l' h => by rw [he]; exact blk_set_ne h _,
    execStmt_assume_cases K _, fun st hok => ?_⟩
  have hx := assume_eq_ok hok
  exact ⟨b, by simp [step, hterm, selectTarget, hx], by simp [step, hAl]⟩

theorem poa_bad (hterm : (P.blk l).term = .switch x [(v, b)] ow) (hU : IsUnreachableBlock P ow)
    (st : State) (h : execStmt K (.assume (.eq x v)) st = none) :
    GoesWrongFrom K P ⟨l, [], st⟩ [] := by
  have hx := assume_eq_none h
  refine goesWrong_of_next_silent (pruneArm_step_P hterm st) ?_
  simp only [selectTarget, hx, ite_false]
  exact goesWrong_unreachBlock hU st

theorem poa_equivPP (hterm : (P.blk l).term = .switch x [(v, b)] ow)
    (hU : IsUnreachableBlock P ow) : EquivPP K P (pruneOtherwiseAssume P l) :=
  (pruneOtherwiseAssume_setting hterm).equivPP (poa_bad hterm hU)

theorem poa_wp_iff (hterm : (P.blk l).term = .switch x [(v, b)] ow)
    (hU : IsUnreachableBlock P ow) (Q : List Int → State → Prop) (σ : State) :
    wp K (pruneOtherwiseAssume P l) Q σ ↔ wp K P Q σ :=
  (pruneOtherwiseAssume_setting hterm).wp_iff (poa_bad hterm hU) Q σ

end pruneOtherwiseAssume

/-! ### Replacing a block by `Block.unreach` -/

/-- In the replaced block only entries are related: the left program at the entry of its
block, the right program at the entry of `Block.unreach`. -/
def RURel (xs : List Stmt) (r₀ r₁ : List Stmt) (_ : State) : Prop := r₀ = xs ∧ r₁ = []

section replaceUnreachable

variable {K : ZContract} {P : Prog} {b : Label}

theorem ru_blk (P : Prog) (b : Label) : (replaceUnreachable P b).blk b = Block.unreach ∧
    ∀ b', b' ≠ b → (replaceUnreachable P b).blk b' = P.blk b' := by
  refine ⟨?_, fun b' h => blk_set_ne h _⟩
  by_cases hb : b < P.length
  · exact blk_set_self hb _
  · have : replaceUnreachable P b = P := List.set_eq_of_length_le (Nat.le_of_not_lt hb)
    rw [this]
    exact blk_of_length_le (Nat.le_of_not_lt hb)

theorem ru_sim {Stop : Cfg → Prop} (hgen : ∀ c, step K P c = .ub → Stop c)
    (hstop : ∀ st, Reach K P ⟨b, (P.blk b).stmts, st⟩ → Stop ⟨b, (P.blk b).stmts, st⟩) :
    IsSim K P (replaceUnreachable P b)
      (RelR K P (replaceUnreachable P b) (BlockRel b (RURel (P.blk b).stmts))) (fun _ _ => 0)
      Stop 0 := by
  obtain ⟨hU, hne⟩ := ru_blk P b
  refine blockSim (fun b' h => (hne b' h).symm) (fun _ => ⟨rfl, by simp [hU, Block.unreach]⟩)
    (fun _ _ => Nat.le_refl 0) hgen ?_
  rintro r₀ r₁ st ⟨rfl, rfl⟩ hc _
  exact Or.inl (hstop st hc)

theorem ru_init (σ : State) :
    RelR K P (replaceUnreachable P b) (BlockRel b (RURel (P.blk b).stmts)) (P.init σ)
      ((replaceUnreachable P b).init σ) :=
  blockSim_init (fun b' h => ((ru_blk P b).2 b' h).symm)
    (fun _ => ⟨rfl, by simp [(ru_blk P b).1, Block.unreach]⟩) σ

theorem ru_special :
    ∀ c d, (c.lbl = b ∧ c.rest = (P.blk b).stmts) →
      RelR K P (replaceUnreachable P b) (BlockRel b (RURel (P.blk b).stmts)) c d →
        GoesWrongFrom K (replaceUnreachable P b) d [] := by
  rintro ⟨lb, r, st'⟩ d ⟨hlb, hr⟩ ⟨hR, -, -⟩
  dsimp only at hlb hr
  subst hlb hr
  obtain ⟨r', rfl, -, rfl⟩ := blockRel_inv hR
  exact goesWrong_of_step_ub (by simp [step, (ru_blk P lb).1, Block.unreach])

theorem ru_refinesPP_iff :
    RefinesPP K P (replaceUnreachable P b) ↔
      ∀ st, ReachableAt K P b 0 st → GoesWrongFrom K P (P.entry b st) [] := by
  constructor
  · intro href st hr
    exact goesWrong_nil_of_sim_necessity
      (ru_sim (Stop := fun c => step K P c = .ub ∨ (c.lbl = b ∧ c.rest = (P.blk b).stmts))
        (fun _ h => Or.inl h) (fun _ _ => Or.inr ⟨rfl, rfl⟩))
      (Special := fun c => c.lbl = b ∧ c.rest = (P.blk b).stmts) (fun _ h => h) ru_special
      ru_init href hr ⟨rfl, rfl⟩
  · intro hcond
    exact refinesPP_of_sim (ru_sim (Stop := fun c => GoesWrongFrom K P c [])
      (fun _ h => goesWrong_of_step_ub h) (fun st hc => hcond st hc)) (fun _ h => h) ru_init

theorem ru_refinesWT_iff :
    RefinesWT K P (replaceUnreachable P b) ↔
      ∀ st, ReachableAt K P b 0 st → ∃ t, GoesWrongFrom K P (P.entry b st) t := by
  constructor
  · intro href st hr
    exact goesWrong_of_sim_necessity
      (ru_sim (Stop := fun c => step K P c = .ub ∨ (c.lbl = b ∧ c.rest = (P.blk b).stmts))
        (fun _ h => Or.inl h) (fun _ _ => Or.inr ⟨rfl, rfl⟩))
      (Special := fun c => c.lbl = b ∧ c.rest = (P.blk b).stmts) (fun _ h => h) ru_special
      ru_init href hr ⟨rfl, rfl⟩
  · intro hcond
    exact refinesWT_of_sim (ru_sim (Stop := fun c => ∃ u, GoesWrongFrom K P c u)
      (fun _ h => ⟨[], goesWrong_of_step_ub h⟩) (fun st hc => hcond st hc)) (fun _ h => h)
      ru_init

end replaceUnreachable

end Toy.ZstAssume
