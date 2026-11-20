import ToyProphecy.Sim.MainChain

/-!
# Proof infrastructure: simulation of the main program — calls and whole runs

Auxiliary definitions and lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

theorem calleeRunP_congr {ex : Bool} {φ φ' : Nat → Int} {f : Callee} {a pf : Int} {n : Nat}
    {fr : PState} (h : calleeRunP ex φ f a pf n = some fr) (hφ : ∀ j < fr.next, φ' j = φ j) :
    calleeRunP ex φ' f a pf n = some fr := by
  simp only [calleeRunP, Option.map_eq_some_iff] at h ⊢
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨s, runOpsP_congr hs hφ, rfl⟩

theorem calleeRunP_next {ex : Bool} {φ : Nat → Int} {f : Callee} {a pf : Int} {n : Nat}
    {fr : PState} (h : calleeRunP ex φ f a pf n = some fr) : n ≤ fr.next := by
  simp only [calleeRunP, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  simpa [calleeInitP] using runOpsP_next hs

/-! ## `s = f(&mut *r)` -/

theorem m_step_call {c sR sB sP ch} {t r : RefVar} {f : Callee} (hM : MRel c sR sB sP ch)
    (hs : (checkStmt c (.call t f r)).stuck = false)
    (hv : (checkStmt c (.call t f r)).viol = []) :
    ∃ sR' sB', stepR sR (.call t f r) = some sR' ∧ stepB sB (.call t f r) = some sB' ∧
      ∀ φ i sP', stepP ResPolicy.std φ i sP (.call t f r) = some sP' → Sat sP'.cs →
        ∃ ch', MRel (checkStmt c (.call t f r)) sR' sB' sP' ch' := by
  obtain ⟨-, hr, hcf, hcv, ht, hc'⟩ := clean_call hs (by rw [hv, hM.viol])
  obtain ⟨x, rest, hx, hch⟩ := hM.active_head hr
  obtain ⟨-, -, ⟨qb, hqb, hqbc⟩, ⟨qp, hqp, hqpc⟩⟩ := hM.head x r rest hch
  obtain ⟨sR1, hR1, hret, hframe, hfwd, hsound, -, -⟩ := callee_summary f hcf hcv sR.store x
  have hback : ∀ a v, calleeBack f a v = v :=
    calleeBack_eq_final_aux f hcf (by simp [CalleeFreshBindings, CalleeAvoids, calleeViolations, hcv])
  refine ⟨{ store := sR1.store, refs := fupd sR.refs t (some x) },
    { sB with refs := fupd sB.refs t (some { cur := sR1.store x, back := fun v => [(.ref r, v)] }) },
    by simp [stepR, hx, hR1, hret], by simp [stepB, hqb, hqbc, hfwd, hback], ?_⟩
  intro φ i sP' hP hsat
  rw [stepP_std_call] at hP
  simp only [hqp, Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hP
  obtain ⟨fr, hfr, q, hq, rfl⟩ := hP
  simp only at hsat
  rw [hqpc] at hfr
  obtain ⟨q', hq', hq'c, hq'f⟩ := hsound φ (φ sP.next) (sP.next + 1) fr hfr (sat_of_append hsat).2
  rw [hq] at hq'; cases hq'
  rw [hc', hq'c, hq'f]
  exact ⟨_, m_push hM hr ht hx hch qp hqp sR1.store hframe (φ sP.next) fr.next (sP.cs ++ fr.cs)⟩

/-! ## One statement -/

theorem m_step {c sR sB sP ch} {st : Stmt} (hM : MRel c sR sB sP ch)
    (hs : (checkStmt c st).stuck = false) (hv : (checkStmt c st).viol = []) :
    ∃ sR' sB', stepR sR st = some sR' ∧ stepB sB st = some sB' ∧
      ∀ φ i sP', stepP ResPolicy.std φ i sP st = some sP' → Sat sP'.cs →
        ∃ ch', MRel (checkStmt c st) sR' sB' sP' ch' := by
  cases st with
  | call t f r => exact m_step_call hM hs hv
  | op o =>
    simp only [checkStmt] at hs hv ⊢
    simp only [stepR, stepB, stepP_std_op]
    cases o with
    | assign x e =>
      obtain ⟨sR', sB', h1, h2, h3⟩ := m_step_assign hM hs hv
      exact ⟨sR', sB', h1, h2, fun φ _ sP' h _ => ⟨ch, h3 φ sP' h⟩⟩
    | borrow k x =>
      obtain ⟨sR', sB', h1, h2, h3⟩ := m_step_borrow hM hs hv
      exact ⟨sR', sB', h1, h2, fun φ _ sP' h _ => ⟨_, h3 φ sP' h⟩⟩
    | borrowSel k e x y =>
      obtain ⟨sR', sB', h1, h2, h3⟩ := m_step_borrowSel hM hs hv
      exact ⟨sR', sB', h1, h2, fun φ _ sP' h _ => h3 φ sP' h⟩
    | reborrow t r =>
      obtain ⟨sR', sB', h1, h2, h3⟩ := m_step_reborrow hM hs hv
      exact ⟨sR', sB', h1, h2, fun φ _ sP' h _ => h3 φ sP' h⟩
    | write r e =>
      obtain ⟨sR', sB', h1, h2, h3⟩ := m_step_write hM hs hv
      exact ⟨sR', sB', h1, h2, fun φ _ sP' h _ => ⟨ch, h3 φ sP' h⟩⟩
    | endBorrow r =>
      obtain ⟨sB', h1, h2, h3⟩ := m_step_end hM hs hv
      exact ⟨sR, sB', h1, h2, fun φ _ sP' h hsat => h3 φ sP' h hsat⟩

/-! ## Bookkeeping for main-program steps -/

theorem stepP_cs {pol : ResPolicy} {φ : Nat → Int} {i : Nat} {s s' : PState} {st : Stmt}
    (h : stepP pol φ i s st = some s') : ∃ l, s'.cs = s.cs ++ l := by
  simp only [stepP, Option.map_eq_some_iff] at h
  obtain ⟨s1, h1, rfl⟩ := h
  have : ∃ l, s1.cs = s.cs ++ l := by
    cases st with
    | op o => obtain ⟨l, hl, -⟩ := stepOpP_cs h1; exact ⟨l, hl⟩
    | call t f r =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h1
      obtain ⟨q, -, fr, -, ret, -, rfl⟩ := h1
      exact ⟨fr.cs, rfl⟩
  obtain ⟨l, hl⟩ := this
  exact ⟨l ++ earlyCs pol i s1, by simp [hl]⟩

theorem runP_cs {pol : ResPolicy} {φ : Nat → Int} : ∀ {i : Nat} {s s' : PState} {P : Prog},
    runP pol φ i s P = some s' → ∃ l, s'.cs = s.cs ++ l
  | i, s, s', [], h => by simp [runP] at h; subst h; exact ⟨[], by simp⟩
  | i, s, s', st :: P, h => by
      simp only [runP, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h2⟩ := h
      obtain ⟨l1, hl1⟩ := stepP_cs h1
      obtain ⟨l2, hl2⟩ := runP_cs h2
      exact ⟨l1 ++ l2, by rw [hl2, hl1, List.append_assoc]⟩

theorem stepP_std_next {φ : Nat → Int} {i : Nat} {s s' : PState} {st : Stmt}
    (h : stepP ResPolicy.std φ i s st = some s') : s.next ≤ s'.next := by
  cases st with
  | op o =>
    rw [stepP_std_op] at h
    have := stepOpP_next h
    split at this <;> omega
  | call t f r =>
    rw [stepP_std_call] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, -, fr, hfr, ret, -, rfl⟩ := h
    have := calleeRunP_next hfr
    simp only; omega

theorem stepP_std_congr {φ φ' : Nat → Int} {i : Nat} {s s' : PState} {st : Stmt}
    (h : stepP ResPolicy.std φ i s st = some s') (hφ : ∀ j < s'.next, φ' j = φ j) :
    stepP ResPolicy.std φ' i s st = some s' := by
  cases st with
  | op o =>
    rw [stepP_std_op] at h ⊢
    exact stepOpP_congr h hφ
  | call t f r =>
    rw [stepP_std_call] at h ⊢
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨q, hq, fr, hfr, ret, hret, rfl⟩ := h
    have hn := calleeRunP_next hfr
    have h0 : φ' s.next = φ s.next := hφ _ (by simp only; omega)
    refine ⟨q, hq, fr, ?_, ret, hret, by rw [h0]⟩
    rw [h0]
    exact calleeRunP_congr hfr (fun j hj => hφ j (by simpa using hj))

theorem runP_std_next {φ : Nat → Int} : ∀ {i : Nat} {s s' : PState} {P : Prog},
    runP ResPolicy.std φ i s P = some s' → s.next ≤ s'.next
  | i, s, s', [], h => by simp [runP] at h; subst h; exact Nat.le_refl _
  | i, s, s', st :: P, h => by
      simp only [runP, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h2⟩ := h
      exact Nat.le_trans (stepP_std_next h1) (runP_std_next h2)

/-! ## Soundness direction: any satisfying prophecy assignment -/

theorem m_run_sound {φ : Nat → Int} : ∀ (P : Prog) {c sR sB sP ch} {i : Nat} {sP' : PState},
    MRel c sR sB sP ch → (checkStmts c P).stuck = false → (checkStmts c P).viol = [] →
    runP ResPolicy.std φ i sP P = some sP' → Sat sP'.cs →
    ∃ sR' sB' ch', runR sR P = some sR' ∧ runB sB P = some sB' ∧
      MRel (checkStmts c P) sR' sB' sP' ch'
  | [], c, sR, sB, sP, ch, i, sP', hM, _, _, hrun, _ => by
      simp [runP] at hrun; subst hrun
      exact ⟨sR, sB, ch, rfl, rfl, hM⟩
  | st :: P, c, sR, sB, sP, ch, i, sP', hM, hs, hv, hrun, hsat => by
      simp only [checkStmts] at hs hv ⊢
      have hs1 := checkStmt_not_stuck_of_checkStmts hs
      have hv1 := viol_nil_of_checkStmts hv
      simp only [runP, Option.bind_eq_some_iff] at hrun
      obtain ⟨sP1, hP1, hrest⟩ := hrun
      obtain ⟨l, hl⟩ := runP_cs hrest
      have hsat1 : Sat sP1.cs := (sat_of_append (hl ▸ hsat)).1
      obtain ⟨sR1, sB1, h1, h2, h3⟩ := m_step hM hs1 hv1
      obtain ⟨ch1, hM1⟩ := h3 φ i sP1 hP1 hsat1
      obtain ⟨sR', sB', ch', h4, h5, hM'⟩ := m_run_sound P hM1 hs hv hrest hsat
      exact ⟨sR', sB', ch', by simp [runR, h1, h4], by simp [runB, h2, h5], hM'⟩

/-! ## Existence direction: constructing a satisfying prophecy assignment -/

def curR (s : RState) (k : RefVar) : Int := ((s.refs k).map s.store).getD 0

/-- The final value of main-program borrow `k` in the remaining program `P`, read
off the reference semantics: the value at its address when it ends, or at the
end of the program if it never ends. -/
def FVm : Prog → RState → RefVar → Int
  | [], s, k => curR s k
  | st :: P, s, k =>
      if st = .op (.endBorrow k) then curR s k else
      match stepR s st with
      | some s' => FVm P s' k
      | none => 0

def MPend (P : Prog) (c : CState) (sR : RState) (sP : PState) : Prop :=
  ∀ k, Live c k → ∃ p, sP.refs k = some p ∧ p.fin = FVm P sR k

theorem FVm_cons_of_ne {st : Stmt} {P : Prog} {s s' : RState} {k : RefVar}
    (hne : st ≠ .op (.endBorrow k)) (h : stepR s st = some s') : FVm (st :: P) s k = FVm P s' k := by
  simp [FVm, hne, h]

/-- Live names after a clean step: the bound name, or live before (and not the
ended one). -/
theorem live_after {c : CState} {st : Stmt} (hs : (checkStmt c st).stuck = false)
    (hv : (checkStmt c st).viol = c.viol) (k : RefVar) (hk : Live (checkStmt c st) k) :
    Stmt.binds st = some k ∨ (Live c k ∧ st ≠ .op (.endBorrow k)) := by
  cases st with
  | call t f r =>
    obtain ⟨-, hr, -, -, -, hc'⟩ := clean_call hs hv
    rw [hc'] at hk
    by_cases hkt : k = t
    · left; simp [Stmt.binds, hkt]
    · right
      refine ⟨?_, by simp⟩
      by_cases hkr : k = r
      · subst hkr; exact Or.inl hr
      · simpa [Live, hkt, hkr] using hk
  | op o =>
    simp only [checkStmt] at hs hv hk
    cases o with
    | assign x e =>
      obtain ⟨-, -, hc'⟩ := clean_assign hs hv
      rw [hc'] at hk; exact Or.inr ⟨hk, by simp⟩
    | borrow r x =>
      obtain ⟨-, -, hc'⟩ := clean_borrow hs hv
      rw [hc'] at hk
      by_cases hkr : k = r
      · left; simp [Stmt.binds, Op.binds, hkr]
      · right; exact ⟨by simpa [Live, hkr] using hk, by simp⟩
    | borrowSel r e x y =>
      obtain ⟨-, -, -, -, hc'⟩ := clean_borrowSel hs hv
      rw [hc'] at hk
      by_cases hkr : k = r
      · left; simp [Stmt.binds, Op.binds, hkr]
      · right; exact ⟨by simpa [Live, hkr] using hk, by simp⟩
    | reborrow t r =>
      obtain ⟨hr, -, hc'⟩ := clean_reborrow hs hv
      rw [hc'] at hk
      by_cases hkt : k = t
      · left; simp [Stmt.binds, Op.binds, hkt]
      · right
        refine ⟨?_, by simp⟩
        by_cases hkr : k = r
        · subst hkr; exact Or.inl hr
        · simpa [Live, hkt, hkr] using hk
    | write r e =>
      obtain ⟨-, -, hc'⟩ := clean_write hs hv
      rw [hc'] at hk; exact Or.inr ⟨hk, by simp⟩
    | endBorrow r =>
      obtain ⟨hr, hc'⟩ := clean_endBorrow hs hv
      rw [hc'] at hk
      right
      have hkr : k ≠ r := by
        intro h; subst h; simp [Live] at hk
      refine ⟨?_, by simp [Ne.symm hkr]⟩
      simp only [Live, upd_apply, hkr, ↓reduceIte] at hk
      unfold CState.release at hk
      split at hk
      · exact hk
      · exact hk
      · split at hk
        · simp only [upd_apply] at hk
          split at hk
          · rename_i hkq
            subst hkq; exact Or.inr ‹_›
          · exact hk
        · exact hk
      · exact hk

end Sim
end Toy.Prophecy
