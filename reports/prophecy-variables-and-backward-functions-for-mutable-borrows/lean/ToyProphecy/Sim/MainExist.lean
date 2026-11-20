import ToyProphecy.Sim.MainRun

/-!
# Proof infrastructure: simulation of the main program — existence of a
satisfying prophecy assignment, and the assembled statements

Auxiliary lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

theorem stepOpP_bind_fin {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} {s s' : PState}
    {o : Op} {t : RefVar} (h : stepOpP L res φ s o = some s') (ht : o.binds = some t) :
    ∃ p, s'.refs t = some p ∧ p.fin = φ s.next := by
  cases o with
  | assign x e => simp [Op.binds] at ht
  | write r e => simp [Op.binds] at ht
  | endBorrow r => simp [Op.binds] at ht
  | borrow r x =>
    simp only [Op.binds, Option.some.injEq] at ht; subst ht
    simp only [stepOpP] at h; split at h
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨{ cur := s.store x, fin := φ s.next, done := false }, by simp, rfl⟩
    · simp at h
  | borrowSel r e x y =>
    simp only [Op.binds, Option.some.injEq] at ht; subst ht
    simp only [stepOpP] at h; split at h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h
      split
      · exact ⟨{ cur := s.store x, fin := φ s.next, done := false }, by simp, rfl⟩
      · exact ⟨{ cur := s.store y, fin := φ s.next, done := false }, by simp, rfl⟩
    · simp at h
  | reborrow t' r =>
    simp only [Op.binds, Option.some.injEq] at ht; subst ht
    simp only [stepOpP, Option.map_eq_some_iff] at h; obtain ⟨a, -, rfl⟩ := h
    exact ⟨{ cur := a.cur, fin := φ s.next, done := false }, by simp, rfl⟩

theorem m_step_exist {c sR sB sP ch} {st : Stmt} {P : Prog} (φ : Nat → Int) (i : Nat)
    (hM : MRel c sR sB sP ch) (hsat : Sat sP.cs) (hpend : MPend (st :: P) c sR sP)
    (hs : (checkStmt c st).stuck = false) (hv : (checkStmt c st).viol = []) :
    ∃ φ1 : Nat → Int, (∀ j < sP.next, φ1 j = φ j) ∧ ∃ sP1 sR1 sB1 ch1,
      stepP ResPolicy.std φ1 i sP st = some sP1 ∧ Sat sP1.cs ∧ stepR sR st = some sR1 ∧
      stepB sB st = some sB1 ∧ MRel (checkStmt c st) sR1 sB1 sP1 ch1 ∧
      MPend P (checkStmt c st) sR1 sP1 := by
  obtain ⟨sR1, sB1, h1, h2, h3⟩ := m_step hM hs hv
  have hlive := live_after hs (by rw [hv, hM.viol])
  cases st with
  | call t f r =>
    obtain ⟨-, hr, hcf, hcv, ht, -⟩ := clean_call hs (by rw [hv, hM.viol])
    obtain ⟨x, rest, hx, hch⟩ := hM.active_head hr
    obtain ⟨-, -, -, ⟨qp, hqp, hqpc⟩⟩ := hM.head x r rest hch
    obtain ⟨sRc, -, -, -, -, hsound, hexist, -⟩ := callee_summary f hcf hcv sR.store x
    let φ0 := fupd φ sP.next (FVm P sR1 t)
    obtain ⟨φ1, hφ1, fr, hfr, hsatfr⟩ := hexist φ0 (φ0 sP.next) (sP.next + 1)
    obtain ⟨q, hq, -, hqf⟩ := hsound φ1 (φ0 sP.next) (sP.next + 1) fr hfr hsatfr
    have h01 : φ1 sP.next = φ0 sP.next := hφ1 sP.next (by omega)
    let sP1 : PState := { sP with refs := fupd (fupd sP.refs r (some { qp with cur := φ1 sP.next })) t (some { cur := q.cur, fin := q.fin, done := false }), next := fr.next, cs := sP.cs ++ fr.cs }
    have hP1 : stepP ResPolicy.std φ1 i sP (.call t f r) = some sP1 := by
      rw [stepP_std_call]
      simp only [hqp, Option.bind_some, hqpc]
      rw [h01, hfr]
      simp [hq, sP1, h01]
    have hsat1 : Sat sP1.cs := sat_append hsat hsatfr
    obtain ⟨ch1, hM1⟩ := h3 φ1 i sP1 hP1 hsat1
    refine ⟨φ1, fun j hj => ?_, sP1, sR1, sB1, ch1, hP1, hsat1, h1, h2, hM1, ?_⟩
    · rw [hφ1 j (by omega)]; simp [φ0, Nat.ne_of_lt hj]
    · intro k hk
      rcases hlive k hk with hkt | ⟨hk', -⟩
      · simp only [Stmt.binds, Option.some.injEq] at hkt; subst hkt
        refine ⟨{ cur := q.cur, fin := q.fin, done := false }, by simp [sP1], ?_⟩
        simp only; rw [hqf]; simp [φ0]
      · obtain ⟨p, hp, hpf⟩ := hpend k hk'
        have hkt : k ≠ t := by
          intro h; subst h; rcases hk' with h | h <;> rw [ht] at h <;> cases h
        by_cases hkr : k = r
        · subst hkr
          rw [hqp] at hp; cases hp
          refine ⟨{ qp with cur := φ1 sP.next }, by simp [sP1, hkt], ?_⟩
          simp only; rw [hpf, FVm_cons_of_ne (by simp) h1]
        · refine ⟨p, by simp [sP1, hkt, hkr, hp], ?_⟩
          rw [hpf, FVm_cons_of_ne (by simp) h1]
  | op o =>
    simp only [checkStmt] at hs hv
    rw [checkStmt] at h3 hlive ⊢
    simp only [stepP_std_op] at h3 ⊢
    by_cases hb : o.binds = none
    · -- no new borrow: the prophecy assignment is unchanged
      obtain ⟨sP1, hP1⟩ := stepOpP_some hM.brP hs (fun _ => true) φ
      obtain ⟨l, hl, hl0, hlend⟩ := stepOpP_cs hP1
      have hsatl : Sat l := by
        by_cases he : ∃ r, o = .endBorrow r
        · obtain ⟨r, rfl⟩ := he
          obtain ⟨p, hp, rfl⟩ := hlend r rfl
          obtain ⟨hr, -⟩ := clean_endBorrow hs (by rw [hv, hM.viol])
          obtain ⟨x, rest, hx, hch⟩ := hM.active_head hr
          obtain ⟨-, -, -, ⟨p0, hp0, hp0c⟩⟩ := hM.head x r rest hch
          rw [hp] at hp0; cases hp0
          obtain ⟨p1, hp1, hp1f⟩ := hpend r (Or.inl hr)
          rw [hp] at hp1; cases hp1
          intro y hy
          simp at hy; subst hy
          simp only
          rw [hp0c, hp1f]
          simp [FVm, curR, hx]
        · have he' : ∀ r, o ≠ .endBorrow r := fun r h => he ⟨r, h⟩
          rw [hl0 he']; intro y hy; simp at hy
      have hsat1 : Sat sP1.cs := by rw [hl]; exact sat_append hsat hsatl
      obtain ⟨ch1, hM1⟩ := h3 φ i sP1 hP1 hsat1
      refine ⟨φ, fun _ _ => rfl, sP1, sR1, sB1, ch1, hP1, hsat1, h1, h2, hM1, ?_⟩
      intro k hk
      rcases hlive k hk with hkb | ⟨hk', hne⟩
      · simp [Stmt.binds, hb] at hkb
      · obtain ⟨p, hp, hpf⟩ := hpend k hk'
        have hfin := stepOpP_fin hP1 k (by simp [hb])
        rw [hp] at hfin
        obtain ⟨p', hp', hp'f⟩ := map_eq_some_of hfin rfl
        exact ⟨p', hp', by rw [hp'f, hpf, FVm_cons_of_ne hne h1]⟩
    · -- a new borrow `t`: its prophecy is its final value in the reference semantics
      obtain ⟨t, ht⟩ : ∃ t, o.binds = some t := by
        cases h : o.binds with
        | none => exact absurd h hb
        | some t => exact ⟨t, rfl⟩
      let φ1 := fupd φ sP.next (FVm P sR1 t)
      obtain ⟨sP1, hP1⟩ := stepOpP_some hM.brP hs (fun _ => true) φ1
      obtain ⟨l, hl, hl0, -⟩ := stepOpP_cs hP1
      have hl' : l = [] := hl0 (by intro r h; subst h; simp [Op.binds] at ht)
      have hsat1 : Sat sP1.cs := by rw [hl, hl']; simpa using hsat
      obtain ⟨ch1, hM1⟩ := h3 φ1 i sP1 hP1 hsat1
      refine ⟨φ1, fun j hj => by simp [φ1, Nat.ne_of_lt hj], sP1, sR1, sB1, ch1, hP1, hsat1, h1, h2,
        hM1, ?_⟩
      intro k hk
      by_cases hkt : k = t
      · subst hkt
        obtain ⟨p, hp, hpf⟩ := stepOpP_bind_fin hP1 ht
        exact ⟨p, hp, by rw [hpf]; simp [φ1]⟩
      · rcases hlive k hk with hkb | ⟨hk', hne⟩
        · simp only [Stmt.binds, ht, Option.some.injEq] at hkb; exact absurd hkb.symm hkt
        · obtain ⟨p, hp, hpf⟩ := hpend k hk'
          have hfin := stepOpP_fin hP1 k (by rw [ht]; simp [Ne.symm hkt])
          rw [hp] at hfin
          obtain ⟨p', hp', hp'f⟩ := map_eq_some_of hfin rfl
          exact ⟨p', hp', by rw [hp'f, hpf, FVm_cons_of_ne hne h1]⟩

theorem m_run_exist : ∀ (P : Prog) {c sR sB sP ch} (φ : Nat → Int) (i : Nat),
    MRel c sR sB sP ch → Sat sP.cs → MPend P c sR sP →
    (checkStmts c P).stuck = false → (checkStmts c P).viol = [] →
    ∃ φ' : Nat → Int, (∀ j < sP.next, φ' j = φ j) ∧ ∃ sP' sR' sB' ch',
      runP ResPolicy.std φ' i sP P = some sP' ∧ Sat sP'.cs ∧ runR sR P = some sR' ∧
      runB sB P = some sB' ∧ MRel (checkStmts c P) sR' sB' sP' ch' ∧
      MPend [] (checkStmts c P) sR' sP'
  | [], c, sR, sB, sP, ch, φ, i, hM, hsat, hpend, _, _ =>
      ⟨φ, fun _ _ => rfl, sP, sR, sB, ch, rfl, hsat, rfl, rfl, hM, hpend⟩
  | st :: P, c, sR, sB, sP, ch, φ, i, hM, hsat, hpend, hs, hv => by
      simp only [checkStmts] at hs hv ⊢
      have hs1 := checkStmt_not_stuck_of_checkStmts hs
      have hv1 := viol_nil_of_checkStmts hv
      obtain ⟨φ1, hφ1, sP1, sR1, sB1, ch1, hP1, hsat1, h1, h2, hM1, hpend1⟩ :=
        m_step_exist φ i hM hsat hpend hs1 hv1
      obtain ⟨φ2, hφ2, sP', sR', sB', ch', hP', hsat', h3, h4, hM', hpend'⟩ :=
        m_run_exist P φ1 (i + 1) hM1 hsat1 hpend1 hs hv
      have hn := stepP_std_next hP1
      refine ⟨φ2, fun j hj => by rw [hφ2 j (by omega), hφ1 j hj], sP', sR', sB', ch', ?_, hsat',
        by simp [runR, h1, h3], by simp [runB, h2, h4], hM', hpend'⟩
      simp [runP, stepP_std_congr hP1 hφ2, hP']

/-! ## Final stores -/

theorem final_store_P {c sR sB sP ch} (hM : MRel c sR sB sP ch) (hpend : MPend [] c sR sP)
    (x : Var) : sP.store x = sR.store x := by
  cases h : ch x with
  | nil => exact (hM.free x h).2
  | cons k l =>
    obtain ⟨kr, hkr⟩ := getLast?_some_of_ne_nil (by simp [h] : ch x ≠ [])
    obtain ⟨pk, qk, hpk, -, hfin, -⟩ := hM.root x kr hkr
    have hm := (hM.mem kr x).1 (List.mem_of_getLast? hkr)
    obtain ⟨p, hp, hpf⟩ := hpend kr hm.1
    rw [hpk] at hp; cases hp
    rw [hfin, hpf]
    simp [FVm, curR, hm.2]

theorem no_live_of_allEnded {P : Prog} {sR sB sP ch} (hX : AllEndedAtExit P)
    (hM : MRel (checkStmts CState.init P) sR sB sP ch) : ∀ x, ch x = [] := by
  intro x
  cases h : ch x with
  | nil => rfl
  | cons k l =>
    exfalso
    have hm := (hM.mem k x).1 (by rw [h]; simp)
    have hb := hM.bound k (by rcases hm.1 with h' | h' <;> rw [h'] <;> simp)
    apply hX
    simp only [violations, hM.stuck, Bool.not_false, Bool.true_and]
    have : (checkStmts CState.init P).bound.any (fun r => (checkStmts CState.init P).status r = .active ||
        (checkStmts CState.init P).status r = .frozen) = true := by
      rw [List.any_eq_true]
      exact ⟨k, hb, by rcases hm.1 with h' | h' <;> simp [h']⟩
    simp [this]

end Sim

open Sim

theorem backSem_eq_refSem_aux (P : Prog) (σ : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) :
    backSem P σ = refSem P σ := by
  by_cases hst : (checkStmts CState.init P).stuck = true
  · have hR := runR_none_of_stuck (s := RState.init σ) (by intro k; simp [CState.init, RState.init])
      rfl hst
    have hB' := runB_none_of_stuck (s := BState.init σ) (by intro k; simp [CState.init, BState.init])
      rfl hst
    simp [backSem, refSem, hR, hB']
  · have hst' : (checkStmts CState.init P).stuck = false := by simpa using hst
    have hv := viol_nil_of_discipline hL hF hE hB
    obtain ⟨φ', hφ', sP', sR', sB', ch', hP', hsat', hR', hB', hM', hpend'⟩ :=
      m_run_exist P (fun _ => 0) 0 (mrel_init σ) (by simp [PState.init, Sat])
        (by intro k hk; simp [Live, CState.init] at hk) hst' hv
    have hnil := no_live_of_allEnded hX hM'
    simp only [backSem, refSem, hR', hB', Option.map_some]
    congr 1
    funext x
    exact (hM'.free x (hnil x)).1

theorem prophOutcome_of_refSem_aux (P : Prog) (σ σ' : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (h : refSem P σ = some σ') : ProphOutcome P σ σ' := by
  by_cases hst : (checkStmts CState.init P).stuck = true
  · have hR := runR_none_of_stuck (s := RState.init σ) (by intro k; simp [CState.init, RState.init])
      rfl hst
    simp [refSem, hR] at h
  · have hst' : (checkStmts CState.init P).stuck = false := by simpa using hst
    have hv := viol_nil_of_discipline hL hF hE hB
    obtain ⟨φ', -, sP', sR', sB', ch', hP', hsat', hR', -, hM', hpend'⟩ :=
      m_run_exist P (fun _ => 0) 0 (mrel_init σ) (by simp [PState.init, Sat])
        (by intro k hk; simp [Live, CState.init] at hk) hst' hv
    simp only [refSem, hR', Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨φ', sP', hP', hsat', funext (final_store_P hM' hpend')⟩

theorem prophOutcome_sound_aux (P : Prog) (σ σ' : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) (h : ProphOutcome P σ σ') :
    refSem P σ = some σ' := by
  obtain ⟨φ, s, hrun, hsat, rfl⟩ := h
  by_cases hst : (checkStmts CState.init P).stuck = true
  · have := runP_none_of_stuck (φ := φ) (s := PState.init σ) (i := 0)
      (by intro k; simp [CState.init, PState.init]) rfl hst
    rw [this] at hrun; cases hrun
  · have hst' : (checkStmts CState.init P).stuck = false := by simpa using hst
    have hv := viol_nil_of_discipline hL hF hE hB
    obtain ⟨sR', sB', ch', hR', hB', hM'⟩ := m_run_sound P (mrel_init σ) hst' hv hrun hsat
    have hnil := no_live_of_allEnded hX hM'
    simp only [refSem, hR', Option.map_some, Option.some.injEq]
    funext x
    exact ((hM'.free x (hnil x)).2).symm

end Toy.Prophecy
