import ToyProphecy.Sim.Stuck

/-!
# Proof infrastructure: the backward function of a scoped callee with fresh
names is the projection

Auxiliary lemmas used only inside the proof of
`calleeBack_eq_final_of_calleeScoped_of_calleeFreshBindings`.
-/

namespace Toy.Prophecy
namespace Sim

open CState

/-- Shape of a backward function in a callee frame: the parameter gives nothing
back; every other borrow writes its final value into a parent bound earlier
(smaller depth `d`). -/
def BackOK (d : RefVar → Nat) (refs : RefVar → Option BRef) (k : RefVar)
    (b : Int → List (Target × Int)) : Prop :=
  (k = 0 → b = fun _ => []) ∧
  (k ≠ 0 → ∃ j, b = (fun v => [(.ref j, v)]) ∧ d j < d k ∧ refs j ≠ none)

def T4C (d : RefVar → Nat) (refs : RefVar → Option BRef) : Prop :=
  ∀ k q, refs k = some q → BackOK d refs k q.back

theorem t4c_congr {d : RefVar → Nat} {refs refs' : RefVar → Option BRef} (h : T4C d refs)
    (hm : ∀ k, (refs' k).map BRef.back = (refs k).map BRef.back) : T4C d refs' := by
  intro k q hq
  have hk := hm k
  rw [hq] at hk
  cases hr : refs k with
  | none => rw [hr] at hk; simp at hk
  | some q0 =>
    rw [hr] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    obtain ⟨h0, h1⟩ := h k q0 hr
    refine ⟨fun hk0 => hk ▸ h0 hk0, fun hk0 => ?_⟩
    obtain ⟨j, hb, hd, hj⟩ := h1 hk0
    refine ⟨j, hk ▸ hb, hd, ?_⟩
    intro hj'
    have := hm j
    rw [hj'] at this
    cases hrj : refs j with
    | none => exact hj hrj
    | some _ => rw [hrj] at this; simp at this

structure T4Rel (c : CState) (s : BState) (d : RefVar → Nat) (n : Nat) : Prop where
  stuck : c.stuck = false
  brel : BRel c.status s.refs
  param : s.refs 0 ≠ none
  backs : T4C d s.refs
  depth : ∀ k, s.refs k ≠ none → d k ≤ n

theorem applyBack_backs : ∀ {s s' : BState} {l : List (Target × Int)}, applyBack s l = some s' →
    ∀ k, (s'.refs k).map BRef.back = (s.refs k).map BRef.back
  | s, s', [], h, k => by simp [applyBack] at h; subst h; rfl
  | s, s', (.loc x, v) :: rest, h, k => by
      simp only [applyBack] at h
      exact applyBack_backs h k
  | s, s', (.ref q, v) :: rest, h, k => by
      simp only [applyBack, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp, h⟩ := h
      rw [applyBack_backs h k]
      by_cases hk : k = q
      · subst hk; simp [hp]
      · simp [hk]

theorem evalB_some_of_not_stuck {L : Bool} {c : CState} {s : BState}
    (hb : BRel c.status s.refs) : ∀ e, (checkExpr L c e).stuck = false →
      ∃ v, evalB L s e = some v
  | .lit n, _ => ⟨n, rfl⟩
  | .var x, h => by
      cases L
      · simp [checkExpr, CState.setStuck] at h
      · exact ⟨_, rfl⟩
  | .deref r, h => by
      simp only [checkExpr] at h
      rw [useRef_stuck_iff] at h
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
      cases hr : s.refs r with
      | none => exact absurd ((hb r).2 hr) h.2
      | some q => exact ⟨q.cur, by simp [evalB, hr]⟩
  | .add a b, h => by
      simp only [checkExpr] at h
      have ha : (checkExpr L c a).stuck = false := by
        cases h' : (checkExpr L c a).stuck
        · rfl
        · rw [checkExpr_stuck_mono L _ b h'] at h; exact h
      have hb' : BRel (checkExpr L c a).status s.refs := by
        rw [(checkExpr_shape L c a).status]; exact hb
      obtain ⟨u, hu⟩ := evalB_some_of_not_stuck hb a ha
      obtain ⟨v, hv⟩ := evalB_some_of_not_stuck hb' b h
      exact ⟨u + v, by simp [evalB, hu, hv]⟩

theorem t4_step {c : CState} {s : BState} {d : RefVar → Nat} {n : Nat} {o : Op}
    (hR : T4Rel c s d n) (hs : (checkOp false c o).stuck = false)
    (hv : Violation.rebind ∉ (checkOp false c o).viol) :
    ∃ s' d', stepOpB false s o = some s' ∧ T4Rel (checkOp false c o) s' d' (n + 1) := by
  have hc := hR.stuck
  -- the semantic step, whenever it succeeds, keeps the bound-name relation
  have hbr : ∀ s', stepOpB false s o = some s' → BRel (checkOp false c o).status s'.refs :=
    fun s' h => brel_step hR.brel hs (stepOpB_refs h)
  cases o with
  | assign x e => simp [checkOp, hc, CState.setStuck] at hs
  | borrow r x => simp [checkOp, hc, CState.setStuck] at hs
  | borrowSel r e x y => simp [checkOp, hc, CState.setStuck] at hs
  | reborrow t r =>
      have hr : c.status r ≠ .unborn := by
        intro hr; simp [checkOp, hc, CState.useRef, hr, CState.setStuck] at hs
      have hus : (c.useRef r).stuck = false := by rw [useRef_stuck_iff]; simp [hc, hr]
      have ht : c.status t = .unborn := by
        refine Classical.byContradiction fun ht => ?_
        apply hv
        simp only [checkOp, hc, hus, Bool.false_eq_true, ↓reduceIte]
        simp [CState.bindRef, (useRef_shape c r).status, ht, CState.addV]
      obtain ⟨q, hq⟩ : ∃ q, s.refs r = some q := by
        cases h : s.refs r with
        | none => exact absurd ((hR.brel r).2 h) hr
        | some q => exact ⟨q, rfl⟩
      have ht' : s.refs t = none := (hR.brel t).1 ht
      have htr : t ≠ r := by intro h; subst h; rw [hq] at ht'; simp at ht'
      have ht0 : t ≠ 0 := by intro h; subst h; exact hR.param ht'
      let s' : BState := { s with refs := fupd s.refs t (some { cur := q.cur, back := fun v => [(.ref r, v)] }) }
      have hstep : stepOpB false s (.reborrow t r) = some s' := by simp [stepOpB, hq, s']
      refine ⟨s', fupd d t (d r + 1), hstep, ⟨by rw [hs], hbr s' hstep, ?_, ?_, ?_⟩⟩
      · simp only [s', fupd_apply]; split
        · simp
        · exact hR.param
      · intro k q' hk
        simp only [s', fupd_apply] at hk
        by_cases hkt : k = t
        · subst hkt
          simp only [↓reduceIte, Option.some.injEq] at hk
          subst hk
          refine ⟨fun h => absurd h ht0, fun _ => ⟨r, rfl, ?_, ?_⟩⟩
          · simp [htr.symm]
          · simp [s', htr.symm, hq]
        · simp only [hkt, ↓reduceIte] at hk
          obtain ⟨h0, h1⟩ := hR.backs k q' hk
          refine ⟨h0, fun hk0 => ?_⟩
          obtain ⟨j, hb, hd, hj⟩ := h1 hk0
          have hjt : j ≠ t := by intro h; subst h; exact hj ht'
          exact ⟨j, hb, by simp [hjt, hkt, hd], by simp [s', hjt, hj]⟩
      · intro k hk
        simp only [s', fupd_apply] at hk
        by_cases hkt : k = t
        · subst hkt
          have := hR.depth r (by rw [hq]; simp)
          simp; omega
        · simp only [hkt, ↓reduceIte] at hk
          have := hR.depth k hk
          simp [hkt]; omega
  | write r e =>
      have hes : (checkExpr false c e).stuck = false := by
        cases h : (checkExpr false c e).stuck
        · rfl
        · simp [checkOp, hc, h] at hs
      have hr : c.status r ≠ .unborn := by
        intro hr
        simp only [checkOp, hc, hes, Bool.false_eq_true, ↓reduceIte] at hs
        rw [useRef_stuck_iff] at hs
        simp [hes, (checkExpr_shape false c e).status, hr] at hs
      obtain ⟨q, hq⟩ : ∃ q, s.refs r = some q := by
        cases h : s.refs r with
        | none => exact absurd ((hR.brel r).2 h) hr
        | some q => exact ⟨q, rfl⟩
      obtain ⟨v, hv'⟩ := evalB_some_of_not_stuck hR.brel e hes
      let s' : BState := { s with refs := fupd s.refs r (some { q with cur := v }) }
      have hstep : stepOpB false s (.write r e) = some s' := by simp [stepOpB, hq, hv', s']
      have hm : ∀ k, (s'.refs k).map BRef.back = (s.refs k).map BRef.back := by
        intro k; by_cases hk : k = r
        · subst hk; simp [s', hq]
        · simp [s', hk]
      have hnone : ∀ k, s'.refs k ≠ none ↔ s.refs k ≠ none := by
        intro k; by_cases hk : k = r
        · subst hk; simp [s', hq]
        · simp [s', hk]
      refine ⟨s', d, hstep, ⟨by rw [hs], hbr s' hstep, (hnone 0).2 hR.param,
        t4c_congr hR.backs hm, fun k hk => Nat.le_succ_of_le (hR.depth k ((hnone k).1 hk))⟩⟩
  | endBorrow r =>
      have hr : c.status r ≠ .unborn := by
        intro hr; simp [checkOp, hc, CState.useRef, hr, CState.setStuck] at hs
      obtain ⟨q, hq⟩ : ∃ q, s.refs r = some q := by
        cases h : s.refs r with
        | none => exact absurd ((hR.brel r).2 h) hr
        | some q => exact ⟨q, rfl⟩
      obtain ⟨h0, h1⟩ := hR.backs r q hq
      obtain ⟨s', hs'⟩ : ∃ s', applyBack s (q.back q.cur) = some s' := by
        by_cases hr0 : r = 0
        · rw [h0 hr0]; exact ⟨s, rfl⟩
        · obtain ⟨j, hb, -, hj⟩ := h1 hr0
          rw [hb]
          cases hpj : s.refs j with
          | none => exact absurd hpj hj
          | some p =>
            exact ⟨{ s with refs := fupd s.refs j (some { p with cur := q.cur }) },
              by simp [applyBack, hpj]⟩
      have hstep : stepOpB false s (.endBorrow r) = some s' := by simp [stepOpB, hq, hs']
      have hm := applyBack_backs hs'
      have hnone : ∀ k, s'.refs k ≠ none ↔ s.refs k ≠ none := by
        intro k; rw [ne_eq, ne_eq, applyBack_refs hs' k]
      refine ⟨s', d, hstep, ⟨by rw [hs], hbr s' hstep, (hnone 0).2 hR.param,
        t4c_congr hR.backs hm, fun k hk => Nat.le_succ_of_le (hR.depth k ((hnone k).1 hk))⟩⟩

theorem t4_run : ∀ (os : List Op) {c : CState} {s : BState} {d : RefVar → Nat} {n : Nat},
    T4Rel c s d n → (checkOps false c os).stuck = false →
    Violation.rebind ∉ (checkOps false c os).viol →
    ∃ s' d', runOpsB false s os = some s' ∧ T4Rel (checkOps false c os) s' d' (n + os.length)
  | [], c, s, d, n, hR, _, _ => ⟨s, d, rfl, by simpa [checkOps] using hR⟩
  | o :: os, c, s, d, n, hR, hs, hv => by
      simp only [checkOps] at hs hv ⊢
      have hs1 := checkOp_not_stuck_of_checkOps hs
      have hv1 : Violation.rebind ∉ (checkOp false c o).viol := by
        intro h; apply hv
        obtain ⟨l, hl, -⟩ := checkOps_viol false (checkOp false c o) os
        rw [hl]; exact List.mem_append_left _ h
      obtain ⟨s1, d1, h1, hR1⟩ := t4_step hR hs1 hv1
      obtain ⟨s2, d2, h2, hR2⟩ := t4_run os hR1 hs hv
      refine ⟨s2, d2, by simp [runOpsB, h1, h2], ?_⟩
      have : n + 1 + os.length = n + (os.length + 1) := by omega
      rw [this] at hR2; exact hR2

theorem t4_unwind (d : RefVar → Nat) : ∀ (fuel : Nat) (s : BState) (k : RefVar) (q : BRef) (v : Int),
    T4C d s.refs → s.refs k = some q → d k < fuel →
    unwindB { s with refs := fupd s.refs k (some { q with cur := v }) } fuel k = some v
  | 0, _, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, s, k, q, v, hC, hq, hd => by
      obtain ⟨h0, h1⟩ := hC k q hq
      by_cases hk0 : k = 0
      · subst hk0; simp [unwindB, Callee.param]
      · obtain ⟨j, hb, hdj, hj⟩ := h1 hk0
        have hjk : j ≠ k := by intro h; subst h; omega
        obtain ⟨p, hp⟩ : ∃ p, s.refs j = some p := by
          cases h : s.refs j with
          | none => exact absurd h hj
          | some p => exact ⟨p, rfl⟩
        have hk0' : k ≠ Callee.param := hk0
        obtain ⟨qc, qb⟩ := q
        simp only at hb
        subst hb
        let s1 : BState := { s with refs := fupd s.refs k (some { cur := v, back := fun v => [(.ref j, v)] }) }
        have hC1 : T4C d s1.refs := by
          apply t4c_congr hC
          intro i; by_cases hi : i = k
          · subst hi; simp [s1, hq]
          · simp [s1, hi]
        have hp1 : s1.refs j = some p := by simp [s1, hjk, hp]
        have := t4_unwind d fuel s1 j p v hC1 hp1 (by omega)
        simpa [unwindB, hk0', hjk, hp, s1, Option.bind] using this

end Sim

open Sim in
theorem calleeBack_eq_final_aux (f : Callee)
    (hS : CalleeScoped f) (hB : CalleeFreshBindings f) :
    ∀ a v, calleeBack f a v = v := by
  intro a v
  have hS' : (checkCallee f).stuck = false := hS
  have hB' : Violation.rebind ∉ (checkCallee f).viol := hB
  simp only [checkCallee] at hS' hB'
  have hst : (checkOps false CState.calleeInit f.body).stuck = false := by
    cases h : (checkOps false CState.calleeInit f.body).stuck
    · rfl
    · simp [h] at hS'
  simp only [hst, Bool.false_eq_true, ↓reduceIte] at hS' hB'
  have hret : (checkOps false CState.calleeInit f.body).status f.ret ≠ .unborn := by
    rw [useRef_stuck_iff] at hS'; simpa [hst] using hS'
  have hB2 : Violation.rebind ∉ (checkOps false CState.calleeInit f.body).viol := by
    intro h; apply hB'
    obtain ⟨l, hl, -⟩ := useRef_viol (checkOps false CState.calleeInit f.body) f.ret
    rw [hl]; exact List.mem_append_left _ h
  have hR0 : T4Rel CState.calleeInit (calleeInitB a) (fun _ => 0) 0 := by
    refine ⟨rfl, calleeInit_brelB a, by simp [calleeInitB, Callee.param], ?_, fun _ _ => Nat.le_refl 0⟩
    intro k q hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [calleeInitB, Callee.param] at hk
      subst hk
      exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
    · simp [calleeInitB, Callee.param, hk0] at hk
  obtain ⟨s, d, hrun, hR⟩ := t4_run f.body hR0 hst hB2
  obtain ⟨q, hq⟩ : ∃ q, s.refs f.ret = some q := by
    cases h : s.refs f.ret with
    | none => exact absurd ((hR.brel f.ret).2 h) hret
    | some q => exact ⟨q, rfl⟩
  have hd := hR.depth f.ret (by rw [hq]; simp)
  have hu := t4_unwind d (f.body.length + 1) s f.ret q v hR.backs hq (by omega)
  simp [calleeBack, calleeBack?, calleeRunB, hrun, hq, hu]

end Toy.Prophecy
