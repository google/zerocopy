import ToyProphecy.Sim.Callee

/-!
# Proof infrastructure: whole callee runs and the callee summary

Auxiliary definitions and lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

theorem viol_nil_of_checkOps {L : Bool} {c : CState} {o : Op} {os : List Op}
    (h : (checkOps L (checkOp L c o) os).viol = []) : (checkOp L c o).viol = [] := by
  obtain ⟨l, hl, -⟩ := checkOps_viol L (checkOp L c o) os
  rw [hl] at h
  exact (List.append_eq_nil_iff.mp h).1

theorem viol_eq_of_checkOps {L : Bool} {c : CState} {o : Op} {os : List Op}
    (h : (checkOps L (checkOp L c o) os).viol = c.viol) : (checkOp L c o).viol = c.viol := by
  obtain ⟨l, hl, -⟩ := checkOps_viol L (checkOp L c o) os
  obtain ⟨l0, hl0, -⟩ := checkOp_viol L c o
  rw [hl, hl0] at h
  rw [hl0, (viol_prefix_eq h).1]
  simp

theorem callee_op_not_local {c : CState} {o : Op} (hs : (checkOp false c o).stuck = false) :
    (∃ t r, o = .reborrow t r) ∨ (∃ r e, o = .write r e) ∨ (∃ r, o = .endBorrow r) := by
  have h := (checkOp_ns_cases hs).2
  cases o with
  | assign x e => exact absurd h.1 (by simp)
  | borrow r x => exact absurd h (by simp)
  | borrowSel r e x y => exact absurd h.1 (by simp)
  | reborrow t r => exact Or.inl ⟨t, r, rfl⟩
  | write r e => exact Or.inr (Or.inl ⟨r, e, rfl⟩)
  | endBorrow r => exact Or.inr (Or.inr ⟨r, rfl⟩)

/-- With no active borrow, no clean callee operation is possible and the returned
name cannot be used cleanly. -/
theorem noactive_contra {c : CState} (hna : ∀ k, c.status k ≠ .active) (ret : RefVar) :
    ∀ (os : List Op), (checkOps false c os).stuck = false → (checkOps false c os).viol = c.viol →
      ((checkOps false c os).useRef ret).stuck = false →
      ((checkOps false c os).useRef ret).viol = (checkOps false c os).viol → False
  | [], _, _, hs, hv => hna ret (useRef_clean hs hv).1
  | o :: os, hs, hv, _, _ => by
      simp only [checkOps] at hs hv
      have hs1 := checkOp_not_stuck_of_checkOps hs
      have hv1 := viol_eq_of_checkOps hv
      rcases callee_op_not_local hs1 with ⟨t, r, rfl⟩ | ⟨r, e, rfl⟩ | ⟨r, rfl⟩
      · exact hna r (clean_reborrow hs1 hv1).1
      · exact hna r (clean_write hs1 hv1).2.1
      · exact hna r (clean_endBorrow hs1 hv1).1

theorem runOpsP_some {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} :
    ∀ {c : CState} {s : PState} {os : List Op}, BRel c.status s.refs →
      (checkOps L c os).stuck = false → ∃ s', runOpsP L res φ s os = some s'
  | c, s, [], _, _ => ⟨s, rfl⟩
  | c, s, o :: os, hb, hs => by
      simp only [checkOps] at hs
      have hs1 := checkOp_not_stuck_of_checkOps hs
      obtain ⟨s1, h1⟩ := stepOpP_some hb hs1 res φ
      obtain ⟨s2, h2⟩ := runOpsP_some (res := res) (φ := φ) (brel_step hb hs1 (stepOpP_refs h1)) hs
      exact ⟨s2, by simp [runOpsP, h1, h2]⟩

/-! ## Soundness direction: any satisfying prophecy assignment -/

theorem c_run_sound {a : Var} {pf : Int} {σ : Store} {φ : Nat → Int} :
    ∀ (os : List Op) {c sR sB sP stk sP'}, CRel a pf σ c sR sB sP stk →
      (checkOps false c os).stuck = false → (checkOps false c os).viol = [] →
      runOpsP false (fun _ => true) φ sP os = some sP' → Sat sP'.cs →
      ∃ sR' sB' stk', runOpsR false sR os = some sR' ∧ runOpsB false sB os = some sB' ∧
        CRel a pf σ (checkOps false c os) sR' sB' sP' stk'
  | [], c, sR, sB, sP, stk, sP', hR, _, _, hrun, _ => by
      simp [runOpsP] at hrun; subst hrun
      exact ⟨sR, sB, stk, rfl, rfl, hR⟩
  | o :: os, c, sR, sB, sP, stk, sP', hR, hs, hv, hrun, hsat => by
      simp only [checkOps] at hs hv ⊢
      have hs1 := checkOp_not_stuck_of_checkOps hs
      have hv1 := viol_nil_of_checkOps hv
      simp only [runOpsP, Option.bind_eq_some_iff] at hrun
      obtain ⟨sP1, hP1, hrest⟩ := hrun
      obtain ⟨l, hl⟩ := runOpsP_cs hrest
      have hsat1 : Sat sP1.cs := (sat_of_append (hl ▸ hsat)).1
      have finish : ∀ sR1 sB1 stk1, stepOpR false sR o = some sR1 → stepOpB false sB o = some sB1 →
          CRel a pf σ (checkOp false c o) sR1 sB1 sP1 stk1 →
          ∃ sR' sB' stk', runOpsR false sR (o :: os) = some sR' ∧
            runOpsB false sB (o :: os) = some sB' ∧
            CRel a pf σ (checkOps false (checkOp false c o) os) sR' sB' sP' stk' := by
        intro sR1 sB1 stk1 h1 h2 hR1
        obtain ⟨sR', sB', stk', h3, h4, hR'⟩ := c_run_sound os hR1 hs hv hrest hsat
        exact ⟨sR', sB', stk', by simp [runOpsR, h1, h3], by simp [runOpsB, h2, h4], hR'⟩
      rcases callee_op_not_local hs1 with ⟨t, r, rfl⟩ | ⟨r, e, rfl⟩ | ⟨r, rfl⟩
      · obtain ⟨sR1, sB1, h1, h2, h3⟩ := c_step_reborrow hR hs1 hv1
        exact finish sR1 sB1 _ h1 h2 (h3 φ sP1 hP1)
      · obtain ⟨sR1, sB1, h1, h2, h3⟩ := c_step_write hR hs1 hv1
        exact finish sR1 sB1 _ h1 h2 (h3 φ sP1 hP1)
      · obtain ⟨sB1, h1, h2, stk1, -, h3⟩ := c_step_end hR hs1 hv1
        exact finish sR sB1 _ h1 h2 (h3 φ sP1 hP1 hsat1)

/-! ## Existence direction: constructing a satisfying prophecy assignment -/

/-- The final value of callee borrow `k` in the remaining operations `os`, read
off the reference semantics: the value at the argument's address when `k` ends,
or the parameter's prophecy `pf` if `k` is still live at callee exit. -/
def FVc (a : Var) (pf : Int) : List Op → RState → RefVar → Int
  | [], _, _ => pf
  | o :: os, s, k =>
      if o = .endBorrow k then s.store a else
      match stepOpR false s o with
      | some s' => FVc a pf os s' k
      | none => 0

def CPend (a : Var) (pf : Int) (os : List Op) (sR : RState) (sP : PState) (stk : List RefVar) :
    Prop :=
  ∀ k ∈ stk, k ≠ 0 → ∃ p, sP.refs k = some p ∧ p.fin = FVc a pf os sR k

theorem FVc_cons_of_ne {a : Var} {pf : Int} {o : Op} {os : List Op} {s s' : RState} {k : RefVar}
    (hne : o ≠ .endBorrow k) (h : stepOpR false s o = some s') :
    FVc a pf (o :: os) s k = FVc a pf os s' k := by
  simp [FVc, hne, h]

theorem c_run_exist {a : Var} {pf : Int} {σ : Store} {ret : RefVar} :
    ∀ (os : List Op) {c sR sB sP stk} (φ : Nat → Int), CRel a pf σ c sR sB sP stk → Sat sP.cs →
      CPend a pf os sR sP stk →
      (checkOps false c os).stuck = false → (checkOps false c os).viol = [] →
      ((checkOps false c os).useRef ret).stuck = false →
      ((checkOps false c os).useRef ret).viol = [] →
      ∃ φ', (∀ i < sP.next, φ' i = φ i) ∧ ∃ sP' sR' sB' stk',
        runOpsP false (fun _ => true) φ' sP os = some sP' ∧ Sat sP'.cs ∧
        runOpsR false sR os = some sR' ∧ runOpsB false sB os = some sB' ∧
        CRel a pf σ (checkOps false c os) sR' sB' sP' stk' ∧ CPend a pf [] sR' sP' stk'
  | [], c, sR, sB, sP, stk, φ, hR, hsat, hpend, _, _, _, _ =>
      ⟨φ, fun _ _ => rfl, sP, sR, sB, stk, rfl, hsat, rfl, rfl, hR, hpend⟩
  | o :: os, c, sR, sB, sP, stk, φ, hR, hsat, hpend, hs, hv, hus, huv => by
      simp only [checkOps] at hs hv hus huv ⊢
      have hs1 := checkOp_not_stuck_of_checkOps hs
      have hv1 := viol_nil_of_checkOps hv
      -- assemble the result from one step under `φ1` and the rest under `φ2`
      have finish : ∀ (φ1 : Nat → Int) sP1 sR1 sB1 stk1,
          (∀ i < sP.next, φ1 i = φ i) →
          stepOpP false (fun _ => true) φ1 sP o = some sP1 → Sat sP1.cs →
          stepOpR false sR o = some sR1 → stepOpB false sB o = some sB1 →
          CRel a pf σ (checkOp false c o) sR1 sB1 sP1 stk1 → CPend a pf os sR1 sP1 stk1 →
          ∃ φ', (∀ i < sP.next, φ' i = φ i) ∧ ∃ sP' sR' sB' stk',
            runOpsP false (fun _ => true) φ' sP (o :: os) = some sP' ∧ Sat sP'.cs ∧
            runOpsR false sR (o :: os) = some sR' ∧ runOpsB false sB (o :: os) = some sB' ∧
            CRel a pf σ (checkOps false (checkOp false c o) os) sR' sB' sP' stk' ∧
            CPend a pf [] sR' sP' stk' := by
        intro φ1 sP1 sR1 sB1 stk1 hφ1 hP1 hsat1 h1 h2 hR1 hpend1
        obtain ⟨φ2, hφ2, sP', sR', sB', stk', hP', hsat', h3, h4, hR', hpend'⟩ :=
          c_run_exist os φ1 hR1 hsat1 hpend1 hs hv hus huv
        have hn1 := stepOpP_next hP1
        refine ⟨φ2, fun i hi => by rw [hφ2 i (by split at hn1 <;> omega), hφ1 i hi], sP', sR', sB',
          stk', ?_, hsat', by simp [runOpsR, h1, h3], by simp [runOpsB, h2, h4], hR', hpend'⟩
        have hP1' : stepOpP false (fun _ => true) φ2 sP o = some sP1 := stepOpP_congr hP1 hφ2
        simp [runOpsP, hP1', hP']
      rcases callee_op_not_local hs1 with ⟨t, r, rfl⟩ | ⟨r, e, rfl⟩ | ⟨r, rfl⟩
      · obtain ⟨sR1, sB1, h1, h2, h3⟩ := c_step_reborrow hR hs1 hv1
        obtain ⟨hr, ht, -⟩ := clean_reborrow hs1 (by rw [hv1, hR.viol])
        obtain ⟨qp, hqp⟩ := bound_of hR.brP (by rw [hr]; simp : c.status r ≠ .unborn)
        let φ1 := fupd φ sP.next (FVc a pf os sR1 t)
        let sP1 : PState :=
          { sP with refs := fupd (fupd sP.refs r (some { qp with cur := φ1 sP.next }))
                      t (some { cur := qp.cur, fin := φ1 sP.next, done := false }),
                    next := sP.next + 1 }
        have hP1 : stepOpP false (fun _ => true) φ1 sP (.reborrow t r) = some sP1 := by
          simp [stepOpP, hqp, sP1]
        have htstk : t ∉ stk := by
          intro h; rcases (hR.mem t).1 h with h | h <;> rw [ht] at h <;> cases h
        refine finish φ1 sP1 sR1 sB1 _ (fun i hi => by simp [φ1, Nat.ne_of_lt hi]) hP1
          (by simpa [sP1] using hsat) h1 h2 (h3 φ1 sP1 hP1) ?_
        intro k hk hk0
        rcases List.mem_cons.mp hk with rfl | hk
        · exact ⟨{ cur := qp.cur, fin := φ1 sP.next, done := false }, by simp [sP1], by simp [φ1]⟩
        · obtain ⟨p, hp, hpf⟩ := hpend k hk hk0
          have hkt : k ≠ t := fun h => htstk (h ▸ hk)
          have hfin := stepOpP_fin hP1 k (by simp [Op.binds, Ne.symm hkt])
          rw [hp] at hfin
          obtain ⟨p', hp', hp'f⟩ := map_eq_some_of hfin rfl
          refine ⟨p', hp', ?_⟩
          rw [hp'f, hpf, FVc_cons_of_ne (by simp) h1]
      · obtain ⟨sR1, sB1, h1, h2, h3⟩ := c_step_write hR hs1 hv1
        obtain ⟨sP1, hP1⟩ := stepOpP_some hR.brP hs1 (fun _ => true) φ
        obtain ⟨l, hl, hl0, -⟩ := stepOpP_cs hP1
        have hl' : l = [] := hl0 (by simp)
        subst hl'
        refine finish φ sP1 sR1 sB1 _ (fun _ _ => rfl) hP1 (by simpa [hl] using hsat) h1 h2
          (h3 φ sP1 hP1) ?_
        intro k hk hk0
        obtain ⟨p, hp, hpf⟩ := hpend k hk hk0
        have hfin := stepOpP_fin hP1 k (by simp [Op.binds])
        rw [hp] at hfin
        obtain ⟨p', hp', hp'f⟩ := map_eq_some_of hfin rfl
        refine ⟨p', hp', ?_⟩
        rw [hp'f, hpf, FVc_cons_of_ne (by simp) h1]
      · obtain ⟨sB1, h1, h2, stk1, hstk, h3⟩ := c_step_end hR hs1 hv1
        obtain ⟨hr, hc'⟩ := clean_endBorrow hs1 (by rw [hv1, hR.viol])
        by_cases hr0 : r = 0
        · -- ending the parameter leaves no active borrow: impossible for a clean callee
          exfalso
          subst hr0
          apply noactive_contra (c := checkOp false c (.endBorrow 0)) _ ret os hs
            (by rw [hv, hv1]) hus (by rw [huv, hv])
          intro k hk
          rw [hc', release_none hR.plender] at hk
          simp only [upd_apply] at hk
          split at hk
          · cases hk
          · rename_i hk0
            obtain ⟨rest, hrest⟩ := hR.active_head hk
            rw [hstk] at hrest
            simp only [List.cons.injEq] at hrest
            exact hk0 hrest.1.symm
        · obtain ⟨qp, hqp⟩ := bound_of hR.brP (by rw [hr]; simp : c.status r ≠ .unborn)
          let sP1 : PState :=
            { sP with refs := fupd sP.refs r (some { qp with done := true }),
                      cs := sP.cs ++ [(qp.cur, qp.fin)] }
          have hP1 : stepOpP false (fun _ => true) φ sP (.endBorrow r) = some sP1 := by
            simp [stepOpP, hqp, sP1]
          obtain ⟨-, -, -, ⟨p0, hp0, hp0c⟩⟩ := hR.head r stk1 hstk
          rw [hqp] at hp0; cases hp0
          obtain ⟨p1, hp1, hp1f⟩ := hpend r (by rw [hstk]; simp) hr0
          rw [hqp] at hp1; cases hp1
          have hcf : qp.cur = qp.fin := by rw [hp0c, hp1f]; simp [FVc]
          have hsat1 : Sat sP1.cs := sat_append hsat (by intro x hx; simp at hx; subst hx; exact hcf)
          have hnd := hR.nodup
          rw [hstk] at hnd
          refine finish φ sP1 sR sB1 stk1 (fun _ _ => rfl) hP1 hsat1 h1 h2 (h3 φ sP1 hP1 hsat1) ?_
          intro k hk hk0
          have hkr : k ≠ r := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hk)
          obtain ⟨p, hp, hpf⟩ := hpend k (by rw [hstk]; exact List.mem_cons_of_mem _ hk) hk0
          refine ⟨p, by simp [sP1, hkr, hp], ?_⟩
          rw [hpf, FVc_cons_of_ne (by simp [Ne.symm hkr]) h1]

/-! ## Callee exit -/

theorem mem_refNames {f : Callee} {j : RefVar} (h : j = 0 ∨ j ∈ f.body.filterMap Op.binds) :
    j ∈ f.refNames := by
  simp only [Callee.refNames, List.mem_eraseDups, List.mem_cons, Callee.param]
  exact h

theorem mem_exitCs {f : Callee} {s : PState} {j : RefVar} {p : PRef} (hj : j ∈ f.refNames)
    (hjr : j ≠ f.ret) (hp : s.refs j = some p) (hd : p.done = false) :
    (p.cur, p.fin) ∈ calleeExitCs f s := by
  simp only [calleeExitCs, List.mem_filterMap, List.mem_filter]
  exact ⟨j, ⟨hj, by simp [hjr]⟩, by simp [hp, hd]⟩

theorem exitCs_inv {f : Callee} {s : PState} {x : Int × Int} (hx : x ∈ calleeExitCs f s) :
    ∃ j p, j ≠ f.ret ∧ s.refs j = some p ∧ p.done = false ∧ x = (p.cur, p.fin) := by
  simp only [calleeExitCs, List.mem_filterMap, List.mem_filter] at hx
  obtain ⟨j, ⟨-, hjr⟩, hj⟩ := hx
  cases hp : s.refs j with
  | none => rw [hp] at hj; simp at hj
  | some p =>
    rw [hp] at hj
    cases hd : p.done
    · simp [hd] at hj
      exact ⟨j, p, by simpa using hjr, hp, hd, hj.symm⟩
    · simp [hd] at hj

/-- In a chain whose bottom is the parameter, if every non-head element has
`cur = fin`, then every element has the parameter's prophecy as its `fin`. -/
theorem links_fin_pf {c : CState} {sB : BState} {sP : PState} {pf : Int} :
    ∀ (l : List RefVar), Links c sB sP l → (∀ k, l.getLast? = some k → k = 0) →
      (∀ j ∈ l.tail, ∃ p, sP.refs j = some p ∧ p.cur = p.fin) →
      (∀ p, sP.refs 0 = some p → p.fin = pf) → (∀ k ∈ l, sP.refs k ≠ none) →
      ∀ k ∈ l, ∃ p, sP.refs k = some p ∧ p.fin = pf
  | [], _, _, _, _, _, k, hk => by simp at hk
  | [k0], _, hb, _, hpf, hbd, k, hk => by
      simp at hk; subst hk
      have := hb k (by simp); subst this
      obtain ⟨p, hp⟩ : ∃ p, sP.refs 0 = some p := by
        cases h : sP.refs 0 with
        | none => exact absurd h (hbd 0 (by simp))
        | some p => exact ⟨p, rfl⟩
      exact ⟨p, hp, hpf p hp⟩
  | k0 :: p0 :: rest, ⟨⟨_, _, ⟨pk, pp, hpk, hpp, hcur⟩⟩, hrest⟩, hb, ht, hpf, hbd, k, hk => by
      have ih := links_fin_pf (p0 :: rest) hrest
        (fun j hj => hb j (by rw [List.getLast?_cons_cons]; exact hj))
        (fun j hj => ht j (by simp only [List.tail_cons] at hj ⊢; exact List.mem_cons_of_mem _ hj))
        hpf (fun j hj => hbd j (List.mem_cons_of_mem _ hj))
      rcases List.mem_cons.mp hk with rfl | hk
      · obtain ⟨pp', hpp', hpp'f⟩ := ih p0 (by simp)
        rw [hpp] at hpp'; cases hpp'
        obtain ⟨pp'', hpp'', hpp''c⟩ := ht p0 (by simp)
        rw [hpp] at hpp''; cases hpp''
        exact ⟨pk, hpk, by rw [← hcur, hpp''c, hpp'f]⟩
      · exact ih k hk

/-! ## The callee summary -/

theorem callee_summary (f : Callee) (hS : (checkCallee f).stuck = false)
    (hV : (checkCallee f).viol = []) (σ : Store) (a : Var) :
    ∃ sR', runOpsR false { store := σ, refs := calleeRefsR a } f.body = some sR' ∧
      sR'.refs f.ret = some a ∧ (∀ y, y ≠ a → sR'.store y = σ y) ∧
      calleeFwd f (σ a) = some (sR'.store a) ∧
      (∀ (φ : Nat → Int) (pf : Int) (n : Nat) fr, calleeRunP true φ f (σ a) pf n = some fr →
        Sat fr.cs → ∃ q, fr.refs f.ret = some q ∧ q.cur = sR'.store a ∧ q.fin = pf) ∧
      (∀ (φ : Nat → Int) (pf : Int) (n : Nat), ∃ φ' : Nat → Int, (∀ i < n, φ' i = φ i) ∧
        ∃ fr, calleeRunP true φ' f (σ a) pf n = some fr ∧ Sat fr.cs) ∧
      (∀ (φ : Nat → Int) (pf : Int) (n : Nat), ∃ fr, calleeRunP true φ f (σ a) pf n = some fr ∧
        fr.refs f.ret ≠ none ∧ n ≤ fr.next) := by
  -- the checker facts
  simp only [checkCallee] at hS hV
  have hst : (checkOps false CState.calleeInit f.body).stuck = false := by
    cases h : (checkOps false CState.calleeInit f.body).stuck
    · rfl
    · simp [h] at hS
  simp only [hst, Bool.false_eq_true, ↓reduceIte] at hS hV
  have hv0 : (checkOps false CState.calleeInit f.body).viol = [] := by
    obtain ⟨l, hl, -⟩ := useRef_viol (checkOps false CState.calleeInit f.body) f.ret
    rw [hl] at hV; exact (List.append_eq_nil_iff.mp hV).1
  have hret : (checkOps false CState.calleeInit f.body).status f.ret = .active :=
    (useRef_clean hS (by rw [hV, hv0])).1
  -- a satisfying run (any prophecy for the parameter) gives the reference and backward facts
  obtain ⟨φ0, -, sP0, sR', sB', stk', hP0, -, hR', hB', hrel, -⟩ :=
    c_run_exist (ret := f.ret) f.body (fun _ => 0) (crel_init a 0 σ 0) (by simp [calleeInitP, Sat])
      (by intro k hk hk0; simp at hk; exact absurd hk hk0) hst hv0 hS (by rw [hV])
  obtain ⟨rest, hstk⟩ := hrel.active_head hret
  obtain ⟨-, -, ⟨qb, hqb, hqbc⟩, -⟩ := hrel.head f.ret rest hstk
  obtain ⟨x, hx⟩ := bound_of hrel.brR (by rw [hret]; simp : _ ≠ RStatus.unborn)
  have hxa := hrel.addr f.ret x hx; subst hxa
  have hbound : ∀ (sP : PState) (n : Nat) (pf : Int) (φ : Nat → Int),
      runOpsP false (fun _ => true) φ (calleeInitP (σ x) pf n) f.body = some sP →
      ∀ j, sP.refs j ≠ none → j ∈ f.refNames := by
    intro sP n pf φ h j hj
    rcases runOpsP_bound h j hj with h | h
    · apply mem_refNames; left
      by_cases hj0 : j = 0
      · exact hj0
      · simp [calleeInitP, Callee.param, hj0] at h
    · exact mem_refNames (Or.inr h)
  refine ⟨sR', hR', hx, hrel.frame, by simp [calleeFwd, calleeRunB, hB', hqb, hqbc], ?_, ?_, ?_⟩
  · -- soundness
    intro φ pf n fr hfr hsat
    simp only [calleeRunP, Option.map_eq_some_iff] at hfr
    obtain ⟨s, hs, rfl⟩ := hfr
    simp only at hsat
    obtain ⟨hsat1, hsat2⟩ := sat_of_append hsat
    obtain ⟨sR'', sB'', stk'', hR'', -, hrel''⟩ :=
      c_run_sound f.body (crel_init x pf σ n) hst hv0 hs hsat1
    rw [hR'] at hR''; cases hR''
    obtain ⟨rest'', hstk''⟩ := hrel''.active_head hret
    obtain ⟨-, -, -, ⟨q, hq, hqc⟩⟩ := hrel''.head f.ret rest'' hstk''
    refine ⟨q, hq, hqc, ?_⟩
    have hnd := hrel''.nodup
    rw [hstk''] at hnd
    have hall := links_fin_pf stk'' hrel''.links hrel''.bottom ?_ hrel''.pfin ?_
    · obtain ⟨q', hq', hq'f⟩ := hall f.ret (by rw [hstk'']; simp)
      rw [hq] at hq'; cases hq'; exact hq'f
    · intro j hj
      rw [hstk''] at hj
      simp only [List.tail_cons] at hj
      have hjr : j ≠ f.ret := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hj)
      have hlive := (hrel''.mem j).1 (by rw [hstk'']; exact List.mem_cons_of_mem _ hj)
      obtain ⟨p, hp⟩ := bound_of hrel''.brP (by rcases hlive with h | h <;> rw [h] <;> simp)
      have hd := (hrel''.done j p hp).2 hlive
      exact ⟨p, hp, hsat2 _ (mem_exitCs (hbound s n pf φ hs j (by rw [hp]; simp)) hjr hp hd)⟩
    · intro k hk
      have hlive := (hrel''.mem k).1 hk
      obtain ⟨p, hp⟩ := bound_of hrel''.brP (by rcases hlive with h | h <;> rw [h] <;> simp)
      rw [hp]; simp
  · -- existence
    intro φ pf n
    obtain ⟨φ', hφ', s, sR2, sB2, stk2, hs, hsat, hR2, -, hrel2, hpend2⟩ :=
      c_run_exist (ret := f.ret) f.body φ (crel_init x pf σ n) (by simp [calleeInitP, Sat])
        (by intro k hk hk0; simp at hk; exact absurd hk hk0) hst hv0 hS (by rw [hV])
    refine ⟨φ', fun i hi => hφ' i (by simpa [calleeInitP] using hi),
      { s with cs := s.cs ++ calleeExitCs f s }, by simp [calleeRunP, hs], ?_⟩
    simp only
    apply sat_append hsat
    intro y hy
    obtain ⟨j, p, hjr, hp, hd, rfl⟩ := exitCs_inv hy
    have hlive := (hrel2.done j p hp).1 hd
    obtain ⟨rest2, hstk2⟩ := hrel2.active_head hret
    have hjt : j ∈ stk2.tail := by
      have := (hrel2.mem j).2 hlive
      rw [hstk2] at this ⊢
      rcases List.mem_cons.mp this with h | h
      · exact absurd h hjr
      · exact h
    have hfin : ∀ k ∈ stk2, ∀ p, s.refs k = some p → p.fin = pf := by
      intro k hk p hp
      by_cases hk0 : k = 0
      · subst hk0; exact hrel2.pfin p hp
      · obtain ⟨p', hp', hp'f⟩ := hpend2 k hk hk0
        rw [hp] at hp'; cases hp'; simpa [FVc] using hp'f
    obtain ⟨k, hk, pk, pj, hpk, hpj, hcur⟩ := links_child stk2 hrel2.links j hjt
    rw [hp] at hpj; cases hpj
    have hjstk : j ∈ stk2 := by rw [hstk2]; exact List.mem_cons_of_mem _ (by simpa [hstk2] using hjt)
    show p.cur = p.fin
    rw [hcur, hfin k hk pk hpk, hfin j hjstk p hp]
  · -- every prophecy assignment runs to completion
    intro φ pf n
    obtain ⟨s, hs⟩ := runOpsP_some (res := fun _ => true) (φ := φ) (calleeInit_brelP (σ x) pf n) hst
    have hb := runOpsP_brel (calleeInit_brelP (σ x) pf n) hst hs
    refine ⟨{ s with cs := s.cs ++ calleeExitCs f s }, by simp [calleeRunP, hs], ?_, ?_⟩
    · simp only
      intro h; exact (by rw [hret]; simp : _ ≠ RStatus.unborn) ((hb f.ret).2 h)
    · simpa [calleeInitP] using runOpsP_next hs

end Sim

open Sim in
theorem prophContract_iff_aux (f : Callee)
    (hF : CalleeNoFrozenAccess f) (hE : CalleeNoUseAfterEnd f) (hB : CalleeFreshBindings f) :
    ∀ a c pf rf, ProphContract f a c pf rf ↔ (calleeFwd f a = some c ∧ pf = calleeBack f a rf) := by
  intro a c pf rf
  have hV : (checkCallee f).viol = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    obtain ⟨h1, h2⟩ := checkCallee_viol f v hv
    cases v with
    | lentAccess => exact h2 rfl
    | frozenAccess => exact hF hv
    | useAfterEnd => exact hE hv
    | rebind => exact hB hv
    | unendedAtExit => exact h1 rfl
  by_cases hS : (checkCallee f).stuck = true
  · constructor
    · rintro ⟨φ, s, hs, -, q, hq, -⟩
      rw [calleeP_stuck hS true φ a pf 0 s hs] at hq; cases hq
    · rintro ⟨h, -⟩
      rw [calleeB_stuck hS a] at h; cases h
  · have hS' : (checkCallee f).stuck = false := by simpa using hS
    obtain ⟨sR', -, -, -, hfwd, hsound, hexist, -⟩ := callee_summary f hS' hV (fun _ => a) 0
    have hback : calleeBack f a rf = rf := calleeBack_eq_final_aux f hS' hB a rf
    rw [hback]
    constructor
    · rintro ⟨φ, s, hs, hsat, q, hq, hqc, hqf⟩
      obtain ⟨q', hq', hq'c, hq'f⟩ := hsound φ pf 0 s hs hsat
      rw [hq] at hq'; cases hq'
      exact ⟨by rw [hfwd, ← hqc, hq'c], by rw [← hqf, hq'f]⟩
    · rintro ⟨hc, rfl⟩
      rw [hfwd] at hc; cases hc
      obtain ⟨φ', -, fr, hfr, hsat⟩ := hexist (fun _ => 0) pf 0
      obtain ⟨q, hq, hqc, hqf⟩ := hsound φ' pf 0 fr hfr hsat
      exact ⟨φ', fr, hfr, hsat, q, hq, hqc, hqf⟩

end Toy.Prophecy
