import ToyProphecy.Sim.Links

/-!
# Proof infrastructure: simulation of a callee frame

In a callee frame with no frozen access, no use after end and fresh names, the
live borrows form one chain from the parameter (bottom) to the single active
borrow (top). All reference variables of the frame point to the argument's
address `a`.

Auxiliary definitions and lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

structure CRel (a : Var) (pf : Int) (σ : Store) (c : CState) (sR : RState) (sB : BState)
    (sP : PState) (stk : List RefVar) : Prop where
  stuck : c.stuck = false
  viol : c.viol = []
  brR : BRel c.status sR.refs
  brB : BRel c.status sB.refs
  brP : BRel c.status sP.refs
  addr : ∀ k x, sR.refs k = some x → x = a
  nodup : stk.Nodup
  mem : ∀ k, k ∈ stk ↔ (c.status k = .active ∨ c.status k = .frozen)
  head : ∀ k rest, stk = k :: rest → c.status k = .active ∧ (∀ p ∈ rest, c.status p = .frozen) ∧
    (∃ q, sB.refs k = some q ∧ q.cur = sR.store a) ∧ (∃ p, sP.refs k = some p ∧ p.cur = sR.store a)
  links : Links c sB sP stk
  bottom : ∀ k, stk.getLast? = some k → k = 0
  pbound : c.status 0 ≠ .unborn
  plender : c.lender 0 = none
  pback : ∀ q, sB.refs 0 = some q → q.back = fun _ => []
  pfin : ∀ p, sP.refs 0 = some p → p.fin = pf
  done : ∀ k p, sP.refs k = some p → (p.done = false ↔ (c.status k = .active ∨ c.status k = .frozen))
  frame : ∀ y, y ≠ a → sR.store y = σ y

theorem bound_of {α : Type} {st : RefVar → RStatus} {refs : RefVar → Option α} (h : BRel st refs)
    {k : RefVar} (hk : st k ≠ .unborn) : ∃ v, refs k = some v := by
  cases hr : refs k with
  | none => exact absurd ((h k).2 hr) hk
  | some v => exact ⟨v, rfl⟩

theorem CRel.active_head {a pf σ c sR sB sP stk} (hR : CRel a pf σ c sR sB sP stk) {k : RefVar}
    (hk : c.status k = .active) : ∃ rest, stk = k :: rest := by
  have hm := (hR.mem k).2 (Or.inl hk)
  cases stk with
  | nil => simp at hm
  | cons k0 rest =>
    refine ⟨rest, ?_⟩
    rcases List.mem_cons.mp hm with h | h
    · rw [h]
    · have := (hR.head k0 rest rfl).2.1 k h
      rw [hk] at this; cases this

theorem crel_init (a : Var) (pf : Int) (σ : Store) (n : Nat) :
    CRel a pf σ CState.calleeInit { store := σ, refs := calleeRefsR a } (calleeInitB (σ a))
      (calleeInitP (σ a) pf n) [0] where
  stuck := rfl
  viol := rfl
  brR := calleeInit_brelR a
  brB := calleeInit_brelB (σ a)
  brP := calleeInit_brelP (σ a) pf n
  addr := by
    intro k x hx
    by_cases hk : k = 0
    · subst hk; simp [calleeRefsR, Callee.param] at hx; exact hx.symm
    · simp [calleeRefsR, Callee.param, hk] at hx
  nodup := by simp
  mem := by
    intro k; by_cases hk : k = 0
    · subst hk; simp [CState.calleeInit, Callee.param]
    · simp [CState.calleeInit, Callee.param, hk]
  head := by
    intro k rest h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp [CState.calleeInit, Callee.param], by simp, ?_, ?_⟩
    · exact ⟨{ cur := σ a, back := fun _ => [] }, by simp [calleeInitB, Callee.param], rfl⟩
    · exact ⟨{ cur := σ a, fin := pf, done := false }, by simp [calleeInitP, Callee.param], rfl⟩
  links := trivial
  bottom := by intro k h; simp at h; exact h.symm
  pbound := by simp [CState.calleeInit, Callee.param]
  plender := rfl
  pback := by intro q hq; simp [calleeInitB, Callee.param] at hq; subst hq; rfl
  pfin := by intro p hp; simp [calleeInitP, Callee.param] at hp; subst hp; rfl
  done := by
    intro k p hp
    by_cases hk : k = 0
    · subst hk; simp [calleeInitP, Callee.param] at hp; subst hp
      simp [CState.calleeInit, Callee.param]
    · simp [calleeInitP, Callee.param, hk] at hp
  frame := fun _ _ => rfl

theorem c_step_reborrow {a pf σ c sR sB sP stk} {t r : RefVar} (hR : CRel a pf σ c sR sB sP stk)
    (hs : (checkOp false c (.reborrow t r)).stuck = false)
    (hv : (checkOp false c (.reborrow t r)).viol = []) :
    ∃ sR' sB', stepOpR false sR (.reborrow t r) = some sR' ∧
      stepOpB false sB (.reborrow t r) = some sB' ∧
      ∀ φ sP', stepOpP false (fun _ => true) φ sP (.reborrow t r) = some sP' →
        CRel a pf σ (checkOp false c (.reborrow t r)) sR' sB' sP' (t :: stk) := by
  obtain ⟨hr, ht, hc'⟩ := clean_reborrow hs (by rw [hv, hR.viol])
  obtain ⟨rest, hstk⟩ := hR.active_head hr
  have hr' : c.status r ≠ .unborn := by rw [hr]; simp
  obtain ⟨x, hx⟩ := bound_of hR.brR hr'
  have hxa := hR.addr r x hx; subst hxa
  obtain ⟨qb, hqb⟩ := bound_of hR.brB hr'
  obtain ⟨qp, hqp⟩ := bound_of hR.brP hr'
  have htR : sR.refs t = none := (hR.brR t).1 ht
  have htB : sB.refs t = none := (hR.brB t).1 ht
  have htP : sP.refs t = none := (hR.brP t).1 ht
  have htr : t ≠ r := by intro h; subst h; rw [hr] at ht; cases ht
  have ht0 : t ≠ 0 := by intro h; subst h; exact hR.pbound ht
  have htstk : t ∉ stk := by intro h; rcases (hR.mem t).1 h with h | h <;> rw [ht] at h <;> cases h
  obtain ⟨-, htail, ⟨qb0, hqb0, hqbc⟩, ⟨qp0, hqp0, hqpc⟩⟩ := hR.head r rest hstk
  rw [hqb] at hqb0; cases hqb0
  rw [hqp] at hqp0; cases hqp0
  refine ⟨{ sR with refs := fupd sR.refs t (some x) },
    { sB with refs := fupd sB.refs t (some { cur := qb.cur, back := fun v => [(.ref r, v)] }) },
    by simp [stepOpR, hx], by simp [stepOpB, hqb], ?_⟩
  intro φ sP' hP
  simp only [stepOpP, hqp, Option.map_some, Option.some.injEq] at hP
  subst hP
  rw [hc']
  have hrstk : r ∈ stk := by rw [hstk]; simp
  have hnd := hR.nodup
  rw [hstk] at hnd
  have hrrest : r ∉ rest := (List.nodup_cons.mp hnd).1
  refine ⟨hR.stuck, hR.viol, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; by_cases hk : k = t
    · subst hk; simp
    · by_cases hkr : k = r
      · subst hkr; simp [hk, hx]
      · simp [hk, hkr, hR.brR k]
  · intro k; by_cases hk : k = t
    · subst hk; simp
    · by_cases hkr : k = r
      · subst hkr; simp [hk, hqb]
      · simp [hk, hkr, hR.brB k]
  · intro k; by_cases hk : k = t
    · subst hk; simp
    · by_cases hkr : k = r
      · subst hkr; simp [hk]
      · simp [hk, hkr, hR.brP k]
  · intro k y hy; by_cases hk : k = t
    · subst hk; simp at hy; exact hy.symm
    · simp [hk] at hy; exact hR.addr k y hy
  · exact List.nodup_cons.mpr ⟨htstk, hR.nodup⟩
  · intro k; by_cases hk : k = t
    · subst hk; simp
    · by_cases hkr : k = r
      · subst hkr; simp [hk, hrstk]
      · simp [hk, hkr, hR.mem k]
  · intro k rest' h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp, ?_, ⟨{ cur := qb.cur, back := fun v => [(.ref r, v)] }, by simp, hqbc⟩,
      ⟨{ cur := qp.cur, fin := φ sP.next, done := false }, by simp, hqpc⟩⟩
    intro p hp
    have hpt : p ≠ t := fun h => htstk (h ▸ hp)
    by_cases hpr : p = r
    · subst hpr; simp [hpt]
    · rw [hstk] at hp
      rcases List.mem_cons.mp hp with h | h
      · exact absurd h hpr
      · simp [hpt, hpr, htail p h]
  · rw [hstk]
    refine ⟨⟨by simp, ⟨{ cur := qb.cur, back := fun v => [(.ref r, v)] }, by simp, rfl⟩,
      ⟨{ cur := qp.cur, fin := φ sP.next, done := false }, { qp with cur := φ sP.next },
        by simp, by simp [htr.symm], rfl⟩⟩, ?_⟩
    rw [← hstk]
    apply links_congr stk hR.links
    · intro k hk; have : k ≠ t := fun h => htstk (h ▸ hk); simp [this]
    · intro k hk; have : k ≠ t := fun h => htstk (h ▸ hk); simp [this]
    · intro k hk; have : k ≠ t := fun h => htstk (h ▸ hk)
      by_cases hkr : k = r
      · subst hkr; simp [this, hqp]
      · simp [this, hkr]
    · intro k hk
      rw [hstk] at hk
      simp only [List.tail_cons] at hk
      have hkt : k ≠ t := fun h => htstk (h ▸ (by rw [hstk]; exact List.mem_cons_of_mem _ hk))
      have hkr : k ≠ r := fun h => hrrest (h ▸ hk)
      simp [hkt, hkr]
  · intro k hk
    apply hR.bottom
    rw [hstk] at hk ⊢
    simpa [List.getLast?_cons_cons] using hk
  · simp only [upd_apply, Ne.symm ht0, ↓reduceIte]; split <;> simp [hR.pbound]
  · simp [Ne.symm ht0, hR.plender]
  · intro q hq; simp [Ne.symm ht0] at hq; exact hR.pback q hq
  · intro p hp
    simp only [fupd_apply, Ne.symm ht0, ↓reduceIte] at hp
    by_cases h0r : (0 : RefVar) = r
    · subst h0r; simp at hp; subst hp; exact hR.pfin qp hqp
    · simp [h0r] at hp; exact hR.pfin p hp
  · intro k p hp
    by_cases hk : k = t
    · subst hk; simp at hp; subst hp; simp
    · by_cases hkr : k = r
      · subst hkr; simp [hk] at hp; subst hp
        have := hR.done k qp hqp
        simp only [hk, ↓reduceIte, upd_apply]
        simp [hr] at this; simp [this]
      · simp [hk, hkr] at hp
        simp [hk, hkr, hR.done k p hp]
  · exact hR.frame

theorem c_step_write {a pf σ c sR sB sP stk} {r : RefVar} {e : Expr} (hR : CRel a pf σ c sR sB sP stk)
    (hs : (checkOp false c (.write r e)).stuck = false)
    (hv : (checkOp false c (.write r e)).viol = []) :
    ∃ sR' sB', stepOpR false sR (.write r e) = some sR' ∧
      stepOpB false sB (.write r e) = some sB' ∧
      ∀ φ sP', stepOpP false (fun _ => true) φ sP (.write r e) = some sP' →
        CRel a pf σ (checkOp false c (.write r e)) sR' sB' sP' stk := by
  obtain ⟨hok, hr, hc'⟩ := clean_write hs (by rw [hv, hR.viol])
  obtain ⟨rest, hstk⟩ := hR.active_head hr
  have hr' : c.status r ≠ .unborn := by rw [hr]; simp
  obtain ⟨x, hx⟩ := bound_of hR.brR hr'
  have hxa := hR.addr r x hx; subst hxa
  obtain ⟨qb, hqb⟩ := bound_of hR.brB hr'
  obtain ⟨qp, hqp⟩ := bound_of hR.brP hr'
  have hd : ∀ k, c.status k = .active → ∃ y, sR.refs k = some y ∧
      (sB.refs k).map BRef.cur = some (sR.store y) ∧ (sP.refs k).map PRef.cur = some (sR.store y) := by
    intro k hk
    obtain ⟨rest', hstk'⟩ := hR.active_head hk
    obtain ⟨y, hy⟩ := bound_of hR.brR (by rw [hk]; simp : c.status k ≠ .unborn)
    have := hR.addr k y hy; subst this
    obtain ⟨-, -, ⟨q1, hq1, hq1c⟩, ⟨p1, hp1, hp1c⟩⟩ := hR.head k rest' hstk'
    exact ⟨_, hy, by simp [hq1, hq1c], by simp [hp1, hp1c]⟩
  obtain ⟨v, hvR, hvB, hvP⟩ := eval_agree (L := false) hd (fun _ h => absurd h (by simp)) e hok
  obtain ⟨-, htail, ⟨qb0, hqb0, hqbc⟩, ⟨qp0, hqp0, hqpc⟩⟩ := hR.head r rest hstk
  refine ⟨{ sR with store := sR.store.set x v },
    { sB with refs := fupd sB.refs r (some { qb with cur := v }) },
    by simp [stepOpR, hx, hvR], by simp [stepOpB, hqb, hvB], ?_⟩
  intro φ sP' hP
  simp only [stepOpP, hqp, hvP, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hP
  subst hP
  rw [hc']
  have hnd := hR.nodup
  rw [hstk] at hnd
  have hrrest : r ∉ rest := (List.nodup_cons.mp hnd).1
  refine ⟨hR.stuck, hR.viol, hR.brR, ?_, ?_, hR.addr, hR.nodup, hR.mem, ?_, ?_, hR.bottom,
    hR.pbound, hR.plender, ?_, ?_, ?_, ?_⟩
  · intro k; by_cases hk : k = r
    · subst hk; simp [hqb, hR.brB k]
    · simp [hk, hR.brB k]
  · intro k; by_cases hk : k = r
    · subst hk; simp [hqp, hR.brP k]
    · simp [hk, hR.brP k]
  · intro k rest' h
    rw [hstk] at h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hr, htail, ⟨{ qb with cur := v }, by simp, by simp⟩, ⟨{ qp with cur := v }, by simp, by simp⟩⟩
  · apply links_congr stk hR.links
    · intro k _; rfl
    · intro k _; by_cases hk : k = r
      · subst hk; simp [hqb]
      · simp [hk]
    · intro k _; by_cases hk : k = r
      · subst hk; simp [hqp]
      · simp [hk]
    · intro k hk
      rw [hstk] at hk
      simp only [List.tail_cons] at hk
      have hkr : k ≠ r := fun h => hrrest (h ▸ hk)
      simp [hkr]
  · intro q hq
    by_cases h0 : (0 : RefVar) = r
    · subst h0; simp at hq; subst hq; exact hR.pback qb hqb
    · simp [h0] at hq; exact hR.pback q hq
  · intro p hp
    by_cases h0 : (0 : RefVar) = r
    · subst h0; simp at hp; subst hp; exact hR.pfin qp hqp
    · simp [h0] at hp; exact hR.pfin p hp
  · intro k p hp
    by_cases hk : k = r
    · subst hk; simp at hp; subst hp; exact hR.done k qp hqp
    · simp [hk] at hp; exact hR.done k p hp
  · intro y hy
    have hyx : y ≠ x := hy
    simp [hyx, hR.frame y hy]

theorem c_step_end {a pf σ c sR sB sP stk} {r : RefVar} (hR : CRel a pf σ c sR sB sP stk)
    (hs : (checkOp false c (.endBorrow r)).stuck = false)
    (hv : (checkOp false c (.endBorrow r)).viol = []) :
    ∃ sB', stepOpR false sR (.endBorrow r) = some sR ∧
      stepOpB false sB (.endBorrow r) = some sB' ∧
      ∃ stk', stk = r :: stk' ∧
      ∀ φ sP', stepOpP false (fun _ => true) φ sP (.endBorrow r) = some sP' → Sat sP'.cs →
        CRel a pf σ (checkOp false c (.endBorrow r)) sR sB' sP' stk' := by
  obtain ⟨hr, hc'⟩ := clean_endBorrow hs (by rw [hv, hR.viol])
  obtain ⟨rest, hstk⟩ := hR.active_head hr
  have hr' : c.status r ≠ .unborn := by rw [hr]; simp
  obtain ⟨x, hx⟩ := bound_of hR.brR hr'
  have hxa := hR.addr r x hx; subst hxa
  obtain ⟨qb, hqb⟩ := bound_of hR.brB hr'
  obtain ⟨qp, hqp⟩ := bound_of hR.brP hr'
  obtain ⟨-, htail, ⟨qb0, hqb0, hqbc⟩, ⟨qp0, hqp0, hqpc⟩⟩ := hR.head r rest hstk
  rw [hqb] at hqb0; cases hqb0
  rw [hqp] at hqp0; cases hqp0
  have hnd := hR.nodup
  rw [hstk] at hnd
  have hrrest : r ∉ rest := (List.nodup_cons.mp hnd).1
  have hlinks := hR.links
  rw [hstk] at hlinks
  have hP : ∀ φ sP', stepOpP false (fun _ => true) φ sP (.endBorrow r) = some sP' →
      sP' = { sP with refs := fupd sP.refs r (some { qp with done := true }),
                      cs := sP.cs ++ [(qp.cur, qp.fin)] } := by
    intro φ sP' h
    simp only [stepOpP, hqp, Option.map_some, Option.some.injEq, ↓reduceIte] at h
    exact h.symm
  cases rest with
  | nil =>
    -- ending the parameter: the chain becomes empty
    have hr0 : r = 0 := hR.bottom r (by rw [hstk]; rfl)
    subst hr0
    have hback := hR.pback qb hqb
    have hrel : c.release 0 = c := release_none hR.plender
    refine ⟨sB, by simp [stepOpR, hx], by simp [stepOpB, hqb, hback, applyBack], [], hstk, ?_⟩
    intro φ sP' h _
    rw [hP φ sP' h, hc', hrel]
    have hlive : ∀ k, k ≠ 0 → ¬ (c.status k = .active ∨ c.status k = .frozen) := by
      intro k hk h
      have := (hR.mem k).2 h
      rw [hstk] at this; simp [hk] at this
    refine ⟨hR.stuck, hR.viol, ?_, ?_, ?_, hR.addr, by simp, ?_, ?_, trivial, ?_, ?_,
      hR.plender, hR.pback, ?_, ?_, hR.frame⟩
    · intro k; by_cases hk : k = 0
      · subst hk; simp [hx]
      · simp [hk, hR.brR k]
    · intro k; by_cases hk : k = 0
      · subst hk; simp [hqb]
      · simp [hk, hR.brB k]
    · intro k; by_cases hk : k = 0
      · subst hk; simp
      · simp [hk, hR.brP k]
    · intro k; by_cases hk : k = 0
      · subst hk; simp
      · simp only [upd_apply, hk, ↓reduceIte]; simp [hlive k hk]
    · intro k rest h; simp at h
    · intro k h; simp at h
    · simp
    · intro p hp; simp at hp; subst hp; exact hR.pfin qp hqp
    · intro k p hp
      by_cases hk : k = 0
      · subst hk; simp at hp; subst hp; simp
      · simp [hk] at hp
        simp only [upd_apply, hk, ↓reduceIte]
        have h1 := hR.done k p hp
        have h2 := hlive k hk
        constructor
        · intro h; exact absurd (h1.1 h) h2
        · intro h; exact absurd h (not_or.mpr (not_or.mp h2))
  | cons p rest2 =>
    obtain ⟨⟨hlp, ⟨qb1, hqb1, hqb1b⟩, ⟨pk, pp, hpk, hpp, hcur⟩⟩, hlinks2⟩ := hlinks
    rw [hqb] at hqb1; cases hqb1
    rw [hqp] at hpk; cases hpk
    have hpfroz : c.status p = .frozen := htail p (by simp)
    have hrel := release_ref hlp hpfroz
    have hp' : c.status p ≠ .unborn := by rw [hpfroz]; simp
    obtain ⟨pb, hpb⟩ := bound_of hR.brB hp'
    have hpr : p ≠ r := by intro h; subst h; exact hrrest (by simp)
    refine ⟨{ sB with refs := fupd sB.refs p (some { pb with cur := qb.cur }) },
      by simp [stepOpR, hx], by simp [stepOpB, hqb, hqb1b, applyBack, hpb], p :: rest2, hstk, ?_⟩
    intro φ sP' h hsat
    rw [hP φ sP' h] at hsat ⊢
    have hcf : qp.cur = qp.fin := hsat (qp.cur, qp.fin) (by simp)
    rw [hc', hrel]
    have hnd2 := (List.nodup_cons.mp hnd).2
    have hprest : p ∉ rest2 := (List.nodup_cons.mp hnd2).1
    refine ⟨hR.stuck, hR.viol, ?_, ?_, ?_, hR.addr, hnd2, ?_, ?_, ?_, ?_, ?_, hR.plender, ?_, ?_, ?_,
      hR.frame⟩
    · intro k; by_cases hk : k = r
      · subst hk; simp [hx]
      · by_cases hkp : k = p
        · subst hkp; simp [hk]; exact fun h => hp' ((hR.brR _).2 h)
        · simp [hk, hkp, hR.brR k]
    · intro k; by_cases hk : k = r
      · subst hk; simp [hpr.symm, hqb]
      · by_cases hkp : k = p
        · subst hkp; simp [hk]
        · simp [hk, hkp, hR.brB k]
    · intro k; by_cases hk : k = r
      · subst hk; simp
      · by_cases hkp : k = p
        · subst hkp; simp [hk]; exact fun h => hp' ((hR.brP _).2 h)
        · simp [hk, hkp, hR.brP k]
    · intro k
      by_cases hk : k = r
      · subst hk; simp [hrrest]
      · by_cases hkp : k = p
        · subst hkp; simp [hk]
        · have := hR.mem k
          rw [hstk] at this
          simp [hk, hkp] at this
          simp [hk, hkp, this]
    · intro k rest' h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [hpr], ?_, ⟨{ pb with cur := qb.cur }, by simp, by simp [hqbc]⟩,
        ⟨pp, by simp [hpr, hpp], ?_⟩⟩
      · intro j hj
        have hjr : j ≠ r := fun h => hrrest (h ▸ List.mem_cons_of_mem _ hj)
        have hjp : j ≠ p := fun h => hprest (h ▸ hj)
        simp [hjr, hjp, htail j (List.mem_cons_of_mem _ hj)]
      · rw [hcur, ← hcf, hqpc]
    · apply links_congr (p :: rest2) hlinks2
      · intro j hj
        rfl
      · intro j hj; by_cases hjp : j = p
        · subst hjp; simp [hpb]
        · simp [hjp]
      · intro j hj
        have hjr : j ≠ r := fun h => hrrest (h ▸ hj)
        simp [hjr]
      · intro j hj
        simp only [List.tail_cons] at hj
        have hjr : j ≠ r := fun h => hrrest (h ▸ List.mem_cons_of_mem _ hj)
        simp [hjr]
    · intro k hk
      apply hR.bottom
      rw [hstk]
      simpa [List.getLast?_cons_cons] using hk
    · have h0r : (0 : RefVar) ≠ r := by
        intro h; subst h
        have := hR.bottom 0
        have hl := hR.bottom
        -- 0 is the last element; it cannot also be the head of a longer chain
        have hlast : (0 :: p :: rest2).getLast? ≠ none := by simp
        obtain ⟨z, hz⟩ : ∃ z, (0 :: p :: rest2).getLast? = some z := by
          cases h : (0 :: p :: rest2).getLast? with
          | none => exact absurd h hlast
          | some z => exact ⟨z, rfl⟩
        have hz0 : z = 0 := hR.bottom z (by rw [hstk]; exact hz)
        subst hz0
        rw [List.getLast?_cons_cons] at hz
        have : (0 : RefVar) ∈ p :: rest2 := List.mem_of_getLast? hz
        exact hrrest this
      simp only [upd_apply, h0r, ↓reduceIte]
      by_cases h0p : (0 : RefVar) = p
      · simp [h0p]
      · simp [h0p, hR.pbound]
    · intro q hq
      by_cases h0p : (0 : RefVar) = p
      · subst h0p; simp at hq; subst hq; exact hR.pback pb hpb
      · simp [h0p] at hq; exact hR.pback q hq
    · intro p' hp'
      by_cases h0r : (0 : RefVar) = r
      · subst h0r; simp at hp'; subst hp'; exact hR.pfin qp hqp
      · simp [h0r] at hp'; exact hR.pfin p' hp'
    · intro k p' hpk
      by_cases hk : k = r
      · subst hk; simp at hpk; subst hpk; simp
      · simp [hk] at hpk
        by_cases hkp : k = p
        · subst hkp
          have := hR.done k p' hpk
          simp [hpfroz] at this
          simp [hk, this]
        · simp [hk, hkp, hR.done k p' hpk]

end Sim
end Toy.Prophecy
