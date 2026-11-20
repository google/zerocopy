import ToyProphecy.Sim.MainLocal

/-!
# Proof infrastructure: simulation of the main program — reborrows, writes, ends

Auxiliary lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

theorem MRel.mem_addr {c sR sB sP ch} (hM : MRel c sR sB sP ch) {k : RefVar} {x y : Var}
    (hk : k ∈ ch x) (hy : k ∈ ch y) : x = y := by
  have h1 := ((hM.mem k x).1 hk).2
  have h2 := ((hM.mem k y).1 hy).2
  rw [h1] at h2; cases h2; rfl

/-! ## Pushing a new top on a chain: `s = &mut *r` and calls -/

/-- Pushing a new active borrow `t` on top of the chain at `x` whose head is `r`,
with new value `σ' x` at address `x` (other locals unchanged). Covers reborrows
(`σ'` unchanged) and calls returning a borrow (`σ' x` the callee's forward value). -/
theorem m_push {c sR sB sP ch} {t r : RefVar} {x : Var} {rest : List RefVar}
    (hM : MRel c sR sB sP ch) (hr : c.status r = .active) (ht : c.status t = .unborn)
    (hx : sR.refs r = some x) (hch : ch x = r :: rest) (qp : PRef) (hqp : sP.refs r = some qp)
    (σ' : Store) (hσ : ∀ y, y ≠ x → σ' y = sR.store y) (fn : Int) (N : Nat)
    (CS : List (Int × Int)) :
    MRel { c with status := upd (upd c.status r .frozen) t .active, lender := upd c.lender t (some (.ref r)), bound := c.bound ++ [t] }
      { store := σ', refs := fupd sR.refs t (some x) }
      { sB with refs := fupd sB.refs t (some { cur := σ' x, back := fun v => [(.ref r, v)] }) }
      { store := sP.store, refs := fupd (fupd sP.refs r (some { qp with cur := fn })) t (some { cur := σ' x, fin := fn, done := false }), next := N, cs := CS }
      (fupd ch x (t :: ch x)) := by
  have hr' : c.status r ≠ .unborn := by rw [hr]; simp
  have hkR : sR.refs t = none := (hM.brR t).1 ht
  have hkB : sB.refs t = none := (hM.brB t).1 ht
  have hkP : sP.refs t = none := (hM.brP t).1 ht
  have htch := hM.unborn_not_mem ht
  have htr : t ≠ r := by intro h; subst h; rw [hr] at ht; cases ht
  have hrx : r ∈ ch x := by rw [hch]; simp
  have hrch : ∀ y, r ∈ ch y → y = x := fun y h => (hM.mem_addr hrx h).symm
  have hnd := hM.nodup x
  rw [hch] at hnd
  have hrrest : r ∉ rest := (List.nodup_cons.mp hnd).1
  obtain ⟨-, htail, -, -⟩ := hM.head x r rest hch
  have hlive' : ∀ j, Live { c with status := upd (upd c.status r .frozen) t .active, lender := upd c.lender t (some (.ref r)), bound := c.bound ++ [t] } j ↔ (j = t ∨ Live c j) := by
    intro j
    by_cases hj : j = t
    · subst hj; simp [Live]
    · by_cases hjr : j = r
      · subst hjr; simp [Live, hj, hr]
      · simp [Live, hj, hjr]
  have hlends : ∀ j w, LendsLoc { c with status := upd (upd c.status r .frozen) t .active, lender := upd c.lender t (some (.ref r)), bound := c.bound ++ [t] } j w ↔ (j ≠ t ∧ LendsLoc c j w) := by
    intro j w
    by_cases hj : j = t
    · subst hj; simp [LendsLoc]
    · simp [LendsLoc, hj]
  have hne : ∀ y, ch y = [] → y ≠ x := by intro y hy h; subst h; rw [hch] at hy; simp at hy
  refine ⟨hM.stuck, hM.viol, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; by_cases hj : j = t
    · subst hj; simp
    · by_cases hjr : j = r
      · subst hjr; simp [hj, hx]
      · simp [hj, hjr, hM.brR j]
  · intro j; by_cases hj : j = t
    · subst hj; simp
    · by_cases hjr : j = r
      · subst hjr; simp only [fupd_apply, hj, ↓reduceIte, upd_apply]
        simp only [reduceCtorEq, false_iff]
        exact fun h => hr' ((hM.brB j).2 h)
      · simp [hj, hjr, hM.brB j]
  · intro j; by_cases hj : j = t
    · subst hj; simp
    · by_cases hjr : j = r
      · subst hjr; simp [hj]
      · simp [hj, hjr, hM.brP j]
  · intro y; by_cases hy : y = x
    · subst hy; simp only [fupd_apply, ↓reduceIte]
      exact List.nodup_cons.mpr ⟨htch y, hM.nodup y⟩
    · simp [hy, hM.nodup y]
  · intro j y
    rw [hlive' j]
    by_cases hj : j = t
    · subst hj
      by_cases hy : y = x
      · subst hy; simp
      · simp [hy, htch y, Ne.symm hy]
    · have hm := hM.mem j y
      by_cases hy : y = x
      · subst hy; simp [hj, hm]
      · simp [hy, hj, hm]
  · intro y j rest' h
    by_cases hy : y = x
    · subst hy
      simp only [fupd_apply, ↓reduceIte, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, ?_, ⟨{ cur := σ' y, back := fun v => [(.ref r, v)] }, by simp, rfl⟩,
        ⟨{ cur := σ' y, fin := fn, done := false }, by simp, rfl⟩⟩
      intro p hp
      rw [hch] at hp
      have hpt : p ≠ t := fun h => htch y (h ▸ (by rw [hch]; exact hp))
      rcases List.mem_cons.mp hp with rfl | hp
      · simp [hpt]
      · have hpr : p ≠ r := fun h => hrrest (h ▸ hp)
        simp [hpt, hpr, htail p hp]
    · simp only [fupd_apply, hy, ↓reduceIte] at h
      have hjm : j ∈ ch y := by rw [h]; simp
      have hjt : j ≠ t := fun h' => htch y (h' ▸ hjm)
      have hjr : j ≠ r := fun h' => hy (hrch y (h' ▸ hjm))
      obtain ⟨h1, h2, ⟨q, hq, hqc⟩, ⟨p, hp, hpc⟩⟩ := hM.head y j rest' h
      refine ⟨by simp [hjt, hjr, h1], fun p' hp' => ?_, ⟨q, by simp [hjt, hq], by simp [hqc, hσ y hy]⟩,
        ⟨p, by simp [hjt, hjr, hp], by simp [hpc, hσ y hy]⟩⟩
      have hpm : p' ∈ ch y := by rw [h]; exact List.mem_cons_of_mem _ hp'
      have hpt : p' ≠ t := fun h' => htch y (h' ▸ hpm)
      have hpr : p' ≠ r := fun h' => hy (hrch y (h' ▸ hpm))
      simp [hpt, hpr, h2 p' hp']
  · intro y
    by_cases hy : y = x
    · subst hy
      simp only [fupd_apply, ↓reduceIte]
      rw [hch]
      refine ⟨⟨by simp, ⟨{ cur := σ' y, back := fun v => [(.ref r, v)] }, by simp, rfl⟩,
        ⟨{ cur := σ' y, fin := fn, done := false }, { qp with cur := fn }, by simp,
          by simp [htr.symm], rfl⟩⟩, ?_⟩
      rw [← hch]
      apply links_congr (ch y) (hM.links y)
      · intro j hj; have : j ≠ t := fun h => htch y (h ▸ hj); simp [this]
      · intro j hj; have : j ≠ t := fun h => htch y (h ▸ hj); simp [this]
      · intro j hj; have : j ≠ t := fun h => htch y (h ▸ hj)
        by_cases hjr : j = r
        · subst hjr; simp [this, hqp]
        · simp [this, hjr]
      · intro j hj
        rw [hch] at hj
        simp only [List.tail_cons] at hj
        have hjt : j ≠ t := fun h => htch y (h ▸ (by rw [hch]; exact List.mem_cons_of_mem _ hj))
        have hjr : j ≠ r := fun h => hrrest (h ▸ hj)
        simp [hjt, hjr]
    · simp only [fupd_apply, hy, ↓reduceIte]
      apply links_congr (ch y) (hM.links y)
      · intro j hj; have : j ≠ t := fun h => htch y (h ▸ hj); simp [this]
      · intro j hj; have : j ≠ t := fun h => htch y (h ▸ hj); simp [this]
      · intro j hj
        have h1 : j ≠ t := fun h => htch y (h ▸ hj)
        have h2 : j ≠ r := fun h => hy (hrch y (h ▸ hj))
        simp [h1, h2]
      · intro j hj
        have hj' := List.mem_of_mem_tail hj
        have h1 : j ≠ t := fun h => htch y (h ▸ hj')
        have h2 : j ≠ r := fun h => hy (hrch y (h ▸ hj'))
        simp [h1, h2]
  · intro y k hk
    have hgl : (ch y).getLast? = some k := by
      by_cases hy : y = x
      · subst hy
        simp only [fupd_apply, ↓reduceIte] at hk
        rw [hch] at hk ⊢
        simpa [List.getLast?_cons_cons] using hk
      · simpa [hy] using hk
    have hkm := List.mem_of_getLast? hgl
    have hkt : k ≠ t := fun h => htch y (h ▸ hkm)
    refine rootOK_congr (hM.root y k hgl) (by simp [hkt]) (by simp [hkt]) ?_ rfl ?_
    · by_cases hkr : k = r
      · subst hkr; simp [hkt, hqp]
      · simp [hkt, hkr]
    · intro n hn hchn hny
      have hnx := hne n hchn
      exact ⟨hσ n hnx, by simp [hnx, hchn]⟩
  · intro y hy
    have hyx : y ≠ x := by
      intro h; subst h; simp at hy
    simp only [fupd_apply, hyx, ↓reduceIte] at hy
    have := hM.free y hy
    exact ⟨by simp [hσ y hyx, this.1], by simp [hσ y hyx, this.2]⟩
  · intro j w hj hw
    rw [hlive' j] at hj
    rw [hlends] at hw
    exact hM.lendsLent j w (hj.resolve_left hw.1) hw.2
  · intro j1 j2 w h1 h2 hw1 hw2
    rw [hlive'] at h1 h2
    rw [hlends] at hw1 hw2
    exact hM.lendsUniq j1 j2 w (h1.resolve_left hw1.1) (h2.resolve_left hw2.1) hw1.2 hw2.2
  · intro j hj
    by_cases hjt : j = t
    · subst hjt; simp
    · apply List.mem_append_left
      apply hM.bound j
      by_cases hjr : j = r
      · subst hjr; exact hr'
      · simpa [hjt, hjr] using hj

theorem m_step_reborrow {c sR sB sP ch} {t r : RefVar} (hM : MRel c sR sB sP ch)
    (hs : (checkOp true c (.reborrow t r)).stuck = false)
    (hv : (checkOp true c (.reborrow t r)).viol = []) :
    ∃ sR' sB', stepOpR true sR (.reborrow t r) = some sR' ∧
      stepOpB true sB (.reborrow t r) = some sB' ∧
      ∀ φ sP', stepOpP true (fun _ => true) φ sP (.reborrow t r) = some sP' →
        ∃ ch', MRel (checkOp true c (.reborrow t r)) sR' sB' sP' ch' := by
  obtain ⟨hr, ht, hc'⟩ := clean_reborrow hs (by rw [hv, hM.viol])
  obtain ⟨x, rest, hx, hch⟩ := hM.active_head hr
  obtain ⟨-, -, ⟨qb, hqb, hqbc⟩, ⟨qp, hqp, hqpc⟩⟩ := hM.head x r rest hch
  refine ⟨{ store := sR.store, refs := fupd sR.refs t (some x) },
    { sB with refs := fupd sB.refs t (some { cur := sR.store x, back := fun v => [(.ref r, v)] }) },
    by simp [stepOpR, hx], by simp [stepOpB, hqb, hqbc], ?_⟩
  intro φ sP' hP
  simp only [stepOpP, hqp, Option.map_some, Option.some.injEq] at hP
  subst hP
  rw [hc', hqpc]
  exact ⟨_, m_push hM hr ht hx hch qp hqp sR.store (fun _ _ => rfl) (φ sP.next) (sP.next + 1) sP.cs⟩

/-! ## `*r = e` -/

theorem m_step_write {c sR sB sP ch} {r : RefVar} {e : Expr} (hM : MRel c sR sB sP ch)
    (hs : (checkOp true c (.write r e)).stuck = false)
    (hv : (checkOp true c (.write r e)).viol = []) :
    ∃ sR' sB', stepOpR true sR (.write r e) = some sR' ∧
      stepOpB true sB (.write r e) = some sB' ∧
      ∀ φ sP', stepOpP true (fun _ => true) φ sP (.write r e) = some sP' →
        MRel (checkOp true c (.write r e)) sR' sB' sP' ch := by
  obtain ⟨hok, hr, hc'⟩ := clean_write hs (by rw [hv, hM.viol])
  obtain ⟨x, rest, hx, hch⟩ := hM.active_head hr
  obtain ⟨-, htail, ⟨qb, hqb, -⟩, ⟨qp, hqp, -⟩⟩ := hM.head x r rest hch
  obtain ⟨v, hvR, hvB, hvP⟩ := hM.eval e hok
  have hr' : c.status r ≠ .unborn := by rw [hr]; simp
  have hrx : r ∈ ch x := by rw [hch]; simp
  have hrch : ∀ y, r ∈ ch y → y = x := fun y h => (hM.mem_addr hrx h).symm
  have hnd := hM.nodup x
  rw [hch] at hnd
  have hrrest : r ∉ rest := (List.nodup_cons.mp hnd).1
  have hrtail : ∀ y, r ∉ (ch y).tail := by
    intro y h
    have hy := hrch y (List.mem_of_mem_tail h)
    subst hy; rw [hch] at h; exact hrrest h
  have hne : ∀ y, ch y = [] → y ≠ x := by intro y hy h; subst h; rw [hch] at hy; simp at hy
  refine ⟨{ sR with store := sR.store.set x v }, { sB with refs := fupd sB.refs r (some { qb with cur := v }) },
    by simp [stepOpR, hx, hvR], by simp [stepOpB, hqb, hvB], ?_⟩
  intro φ sP' hP
  simp only [stepOpP, hqp, hvP, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hP
  subst hP
  rw [hc']
  refine ⟨hM.stuck, hM.viol, hM.brR, ?_, ?_, hM.nodup, hM.mem, ?_, ?_, ?_, ?_,
    hM.lendsLent, hM.lendsUniq, hM.bound⟩
  · intro j; by_cases hj : j = r
    · subst hj; simp only [fupd_apply, ↓reduceIte, reduceCtorEq, iff_false]; exact hr'
    · simp [hj, hM.brB j]
  · intro j; by_cases hj : j = r
    · subst hj; simp only [fupd_apply, ↓reduceIte, reduceCtorEq, iff_false]; exact hr'
    · simp [hj, hM.brP j]
  · intro y j rest' h
    by_cases hy : y = x
    · subst hy
      rw [hch] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hr, htail, ⟨{ qb with cur := v }, by simp, by simp⟩, ⟨{ qp with cur := v }, by simp, by simp⟩⟩
    · have hjm : j ∈ ch y := by rw [h]; simp
      have hjr : j ≠ r := fun h' => hy (hrch y (h' ▸ hjm))
      obtain ⟨h1, h2, ⟨q, hq, hqc⟩, ⟨p, hp, hpc⟩⟩ := hM.head y j rest' h
      exact ⟨h1, h2, ⟨q, by simp [hjr, hq], by simp [hqc, hy]⟩, ⟨p, by simp [hjr, hp], by simp [hpc, hy]⟩⟩
  · intro y
    apply links_congr (ch y) (hM.links y)
    · intro j _; rfl
    · intro j _; by_cases hj : j = r
      · subst hj; simp [hqb]
      · simp [hj]
    · intro j _; by_cases hj : j = r
      · subst hj; simp [hqp]
      · simp [hj]
    · intro j hj
      have hjr : j ≠ r := fun h => hrtail y (h ▸ hj)
      simp [hjr]
  · intro y k hk
    have hkm := List.mem_of_getLast? hk
    refine rootOK_congr (hM.root y k hk) rfl ?_ ?_ rfl ?_
    · by_cases hj : k = r
      · subst hj; simp [hqb]
      · simp [hj]
    · by_cases hj : k = r
      · subst hj; simp [hqp]
      · simp [hj]
    · intro n hn hchn hny
      exact ⟨by simp [hne n hchn], hchn⟩
  · intro y hy
    have hyx := hne y hy
    have := hM.free y hy
    exact ⟨by simp [hyx, this.1], by simp [hyx, this.2]⟩

/-! ## `end r` -/

/-- Ending the root of a singleton chain at `x`. -/
theorem m_end_root {c sR sB sP ch} {r : RefVar} {x : Var} (hM : MRel c sR sB sP ch)
    (hr : c.status r = .active) (hx : sR.refs r = some x) (hch : ch x = [r])
    (L' : Var → Bool) (hL' : ∀ w, ¬ LendsLoc c r w → L' w = c.lent w)
    (sB' : BState) (hB'r : sB'.refs = sB.refs) (hB'x : sB'.store x = sR.store x)
    (hB'y : ∀ y, y ≠ x → sB'.store y = sB.store y)
    (qp : PRef) (hqp : sP.refs r = some qp) (hcf : qp.cur = qp.fin) (CS : List (Int × Int)) :
    MRel { c with lent := L', status := upd c.status r .ended } sR sB'
      { sP with refs := fupd sP.refs r (some { qp with done := true }), cs := CS }
      (fupd ch x []) := by
  have hr' : c.status r ≠ .unborn := by rw [hr]; simp
  have hrx : r ∈ ch x := by rw [hch]; simp
  have hrch : ∀ y, r ∈ ch y → y = x := fun y h => (hM.mem_addr hrx h).symm
  obtain ⟨-, -, -, ⟨qp0, hqp0, hqpc⟩⟩ := hM.head x r [] hch
  rw [hqp] at hqp0; cases hqp0
  obtain ⟨pk, qk, hpk, hqk, hfin, -⟩ := hM.root x r (by rw [hch]; rfl)
  rw [hqp] at hpk; cases hpk
  have hliverr : Live c r := Or.inl hr
  have hlive' : ∀ j, Live { c with lent := L', status := upd c.status r .ended } j ↔ (j ≠ r ∧ Live c j) := by
    intro j; by_cases hj : j = r
    · subst hj; simp [Live]
    · simp [Live, hj]
  have hlends : ∀ j w, LendsLoc { c with lent := L', status := upd c.status r .ended } j w ↔ LendsLoc c j w := by
    intro j w; simp [LendsLoc]
  have hnotx : ∀ y, y ≠ x → r ∉ ch y := fun y hy h => hy (hrch y h)
  refine ⟨hM.stuck, hM.viol, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; by_cases hj : j = r
    · subst hj; simp [hx]
    · simp [hj, hM.brR j]
  · intro j; rw [hB'r]; by_cases hj : j = r
    · subst hj; simp only [upd_apply, ↓reduceIte, reduceCtorEq, false_iff]; exact fun h => hr' ((hM.brB j).2 h)
    · simp [hj, hM.brB j]
  · intro j; by_cases hj : j = r
    · subst hj; simp
    · simp [hj, hM.brP j]
  · intro y; by_cases hy : y = x
    · subst hy; simp
    · simp [hy, hM.nodup y]
  · intro j y
    rw [hlive' j]
    by_cases hy : y = x
    · subst hy
      simp only [fupd_apply, ↓reduceIte, List.not_mem_nil, false_iff, not_and]
      intro ⟨hjr, hj⟩ hjy
      have := (hM.mem j y).2 ⟨hj, hjy⟩
      rw [hch] at this; simp at this; exact hjr this
    · simp only [fupd_apply, hy, ↓reduceIte]
      rw [hM.mem j y]
      constructor
      · intro ⟨h1, h2⟩
        refine ⟨⟨?_, h1⟩, h2⟩
        intro hjr; subst hjr; rw [hx] at h2; cases h2; exact hy rfl
      · intro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · intro y k rest h
    have hyx : y ≠ x := by intro h'; subst h'; simp at h
    simp only [fupd_apply, hyx, ↓reduceIte] at h
    have hkr : k ≠ r := fun h' => hnotx y hyx (h' ▸ (by rw [h]; simp))
    obtain ⟨h1, h2, ⟨q, hq, hqc⟩, ⟨p, hp, hpc⟩⟩ := hM.head y k rest h
    refine ⟨by simp [hkr, h1], fun p' hp' => ?_, ⟨q, by rw [hB'r]; exact hq, hqc⟩,
      ⟨p, by simp [hkr, hp], hpc⟩⟩
    have hpr : p' ≠ r := fun h' => hnotx y hyx (h' ▸ (by rw [h]; exact List.mem_cons_of_mem _ hp'))
    simp [hpr, h2 p' hp']
  · intro y
    by_cases hy : y = x
    · subst hy; simp [Links]
    · simp only [fupd_apply, hy, ↓reduceIte]
      apply links_congr (ch y) (hM.links y)
      · intro j _; rfl
      · intro j _; rw [hB'r]
      · intro j hj; have : j ≠ r := fun h => hnotx y hy (h ▸ hj); simp [this]
      · intro j hj
        have : j ≠ r := fun h => hnotx y hy (h ▸ List.mem_of_mem_tail hj); simp [this]
  · intro y k hk
    have hyx : y ≠ x := by intro h'; subst h'; simp at hk
    simp only [fupd_apply, hyx, ↓reduceIte] at hk
    have hkm := List.mem_of_getLast? hk
    have hkr : k ≠ r := fun h => hnotx y hyx (h ▸ hkm)
    refine rootOK_congr (hM.root y k hk) rfl (by rw [hB'r]) (by simp [hkr]) rfl ?_
    intro n hn hchn hny
    refine ⟨rfl, ?_⟩
    by_cases hnx : n = x
    · subst hnx; simp
    · simp [hnx, hchn]
  · intro y hy
    by_cases hyx : y = x
    · subst hyx
      exact ⟨hB'x, by rw [← hqpc, hcf]; exact hfin⟩
    · simp only [fupd_apply, hyx, ↓reduceIte] at hy
      rw [hB'y y hyx]
      exact hM.free y hy
  · intro j w hj hw
    rw [hlive' j] at hj
    rw [hlends] at hw
    have hold := hM.lendsLent j w hj.2 hw
    have hnr : ¬ LendsLoc c r w := by
      intro h; exact hj.1 (hM.lendsUniq j r w hj.2 hliverr hw h)
    simp [hL' w hnr, hold]
  · intro j1 j2 w h1 h2 hw1 hw2
    rw [hlive'] at h1 h2
    rw [hlends] at hw1 hw2
    exact hM.lendsUniq j1 j2 w h1.2 h2.2 hw1 hw2
  · intro j hj
    apply hM.bound j
    by_cases hjr : j = r
    · subst hjr; exact hr'
    · simpa [hjr] using hj

/-- Ending the head `r` of a chain `r :: p :: rest` at `x`: `p` becomes the head. -/
theorem m_pop {c sR sB sP ch} {r p : RefVar} {x : Var} {rest : List RefVar}
    (hM : MRel c sR sB sP ch) (hr : c.status r = .active) (hx : sR.refs r = some x)
    (hch : ch x = r :: p :: rest) (qb : BRef) (hqb : sB.refs r = some qb)
    (hqbc : qb.cur = sR.store x) (pb : BRef) (hpb : sB.refs p = some pb)
    (qp : PRef) (hqp : sP.refs r = some qp) (hcf : qp.cur = qp.fin) (CS : List (Int × Int)) :
    MRel { c with status := upd (upd c.status p .active) r .ended } sR
      { sB with refs := fupd sB.refs p (some { pb with cur := qb.cur }) }
      { sP with refs := fupd sP.refs r (some { qp with done := true }), cs := CS }
      (fupd ch x (p :: rest)) := by
  have hr' : c.status r ≠ .unborn := by rw [hr]; simp
  have hrx : r ∈ ch x := by rw [hch]; simp
  have hpx : p ∈ ch x := by rw [hch]; simp
  have hrch : ∀ y, r ∈ ch y → y = x := fun y h => (hM.mem_addr hrx h).symm
  have hpch : ∀ y, p ∈ ch y → y = x := fun y h => (hM.mem_addr hpx h).symm
  have hnd := hM.nodup x
  rw [hch] at hnd
  have hrrest : r ∉ p :: rest := (List.nodup_cons.mp hnd).1
  have hnd2 := (List.nodup_cons.mp hnd).2
  have hprest : p ∉ rest := (List.nodup_cons.mp hnd2).1
  have hpr : p ≠ r := fun h => hrrest (h ▸ by simp)
  obtain ⟨-, htail, -, ⟨qp0, hqp0, hqpc⟩⟩ := hM.head x r (p :: rest) hch
  rw [hqp] at hqp0; cases hqp0
  have hlinks := hM.links x
  rw [hch] at hlinks
  obtain ⟨⟨hlp, -, ⟨pk, pp, hpk, hpp, hcur⟩⟩, hlinks2⟩ := hlinks
  rw [hqp] at hpk; cases hpk
  have hpfroz : c.status p = .frozen := htail p (by simp)
  have hp' : c.status p ≠ .unborn := by rw [hpfroz]; simp
  have hlive' : ∀ j, Live { c with status := upd (upd c.status p .active) r .ended } j ↔ (j ≠ r ∧ Live c j) := by
    intro j; by_cases hj : j = r
    · subst hj; simp [Live]
    · by_cases hjp : j = p
      · subst hjp; simp [Live, hj, hpfroz]
      · simp [Live, hj, hjp]
  have hlends : ∀ j w, LendsLoc { c with status := upd (upd c.status p .active) r .ended } j w ↔ LendsLoc c j w := by
    intro j w; simp [LendsLoc]
  have hnotr : ∀ y, y ≠ x → r ∉ ch y := fun y hy h => hy (hrch y h)
  have hnotp : ∀ y, y ≠ x → p ∉ ch y := fun y hy h => hy (hpch y h)
  have hne : ∀ y, ch y = [] → y ≠ x := by intro y hy h; subst h; rw [hch] at hy; simp at hy
  refine ⟨hM.stuck, hM.viol, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; by_cases hj : j = r
    · subst hj; simp [hx]
    · by_cases hjp : j = p
      · subst hjp; simp only [upd_apply, hj, ↓reduceIte, reduceCtorEq, false_iff]
        exact fun h => hp' ((hM.brR j).2 h)
      · simp [hj, hjp, hM.brR j]
  · intro j; by_cases hj : j = r
    · subst hj; simp [hpr.symm, hqb]
    · by_cases hjp : j = p
      · subst hjp; simp [hj]
      · simp [hj, hjp, hM.brB j]
  · intro j; by_cases hj : j = r
    · subst hj; simp
    · by_cases hjp : j = p
      · subst hjp; simp only [fupd_apply, upd_apply, hj, ↓reduceIte, reduceCtorEq, false_iff]
        exact fun h => hp' ((hM.brP j).2 h)
      · simp [hj, hjp, hM.brP j]
  · intro y; by_cases hy : y = x
    · subst hy; simp only [fupd_apply, ↓reduceIte]; exact hnd2
    · simp [hy, hM.nodup y]
  · intro j y
    rw [hlive' j]
    by_cases hy : y = x
    · subst hy
      simp only [fupd_apply, ↓reduceIte]
      have hm := hM.mem j y
      rw [hch] at hm
      by_cases hjr : j = r
      · subst hjr; simp [hrrest]
      · have h3 : j ∈ r :: p :: rest ↔ j ∈ p :: rest := by simp [hjr]
        rw [← h3, hm]; simp [hjr]
    · simp only [fupd_apply, hy, ↓reduceIte]
      rw [hM.mem j y]
      constructor
      · intro ⟨h1, h2⟩
        refine ⟨⟨?_, h1⟩, h2⟩
        intro hjr; subst hjr; rw [hx] at h2; cases h2; exact hy rfl
      · intro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · intro y k rest' h
    by_cases hy : y = x
    · subst hy
      simp only [fupd_apply, ↓reduceIte, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [hpr], ?_, ⟨{ pb with cur := qb.cur }, by simp, hqbc⟩,
        ⟨pp, by simp [hpr, hpp], by rw [hcur, ← hcf, hqpc]⟩⟩
      intro j hj
      have hjr : j ≠ r := fun h => hrrest (h ▸ List.mem_cons_of_mem _ hj)
      have hjp : j ≠ p := fun h => hprest (h ▸ hj)
      simp [hjr, hjp, htail j (List.mem_cons_of_mem _ hj)]
    · simp only [fupd_apply, hy, ↓reduceIte] at h
      have hkm : k ∈ ch y := by rw [h]; simp
      have hkr : k ≠ r := fun h' => hnotr y hy (h' ▸ hkm)
      have hkp : k ≠ p := fun h' => hnotp y hy (h' ▸ hkm)
      obtain ⟨h1, h2, ⟨q, hq, hqc⟩, ⟨p1, hp1, hp1c⟩⟩ := hM.head y k rest' h
      refine ⟨by simp [hkr, hkp, h1], fun p' hp' => ?_, ⟨q, by simp [hkp, hq], hqc⟩,
        ⟨p1, by simp [hkr, hp1], hp1c⟩⟩
      have hpm : p' ∈ ch y := by rw [h]; exact List.mem_cons_of_mem _ hp'
      have h3 : p' ≠ r := fun h' => hnotr y hy (h' ▸ hpm)
      have h4 : p' ≠ p := fun h' => hnotp y hy (h' ▸ hpm)
      simp [h3, h4, h2 p' hp']
  · intro y
    by_cases hy : y = x
    · subst hy
      simp only [fupd_apply, ↓reduceIte]
      apply links_congr (p :: rest) hlinks2
      · intro j _; rfl
      · intro j _; by_cases hjp : j = p
        · subst hjp; simp [hpb]
        · simp [hjp]
      · intro j hj; have : j ≠ r := fun h => hrrest (h ▸ hj); simp [this]
      · intro j hj
        simp only [List.tail_cons] at hj
        have : j ≠ r := fun h => hrrest (h ▸ List.mem_cons_of_mem _ hj)
        simp [this]
    · simp only [fupd_apply, hy, ↓reduceIte]
      apply links_congr (ch y) (hM.links y)
      · intro j _; rfl
      · intro j hj; have : j ≠ p := fun h => hnotp y hy (h ▸ hj); simp [this]
      · intro j hj; have : j ≠ r := fun h => hnotr y hy (h ▸ hj); simp [this]
      · intro j hj
        have : j ≠ r := fun h => hnotr y hy (h ▸ List.mem_of_mem_tail hj); simp [this]
  · intro y k hk
    have hgl : (ch y).getLast? = some k := by
      by_cases hy : y = x
      · subst hy
        simp only [fupd_apply, ↓reduceIte] at hk
        rw [hch, List.getLast?_cons_cons]; exact hk
      · simpa [hy] using hk
    have hkm := List.mem_of_getLast? hgl
    have hkr : k ≠ r := by
      intro h; subst h
      by_cases hy : y = x
      · subst hy; simp only [fupd_apply, ↓reduceIte] at hk; exact hrrest (List.mem_of_getLast? hk)
      · exact hnotr y hy hkm
    refine rootOK_congr (hM.root y k hgl) rfl ?_ (by simp [hkr]) rfl ?_
    · by_cases hkp : k = p
      · subst hkp; simp [hpb]
      · simp [hkp]
    · intro n hn hchn hny
      exact ⟨rfl, by simp [hne n hchn, hchn]⟩
  · intro y hy
    have hyx : y ≠ x := by intro h'; subst h'; simp at hy
    simp only [fupd_apply, hyx, ↓reduceIte] at hy
    exact hM.free y hy
  · intro j w hj hw
    rw [hlive' j] at hj
    rw [hlends] at hw
    exact hM.lendsLent j w hj.2 hw
  · intro j1 j2 w h1 h2 hw1 hw2
    rw [hlive'] at h1 h2
    rw [hlends] at hw1 hw2
    exact hM.lendsUniq j1 j2 w h1.2 h2.2 hw1 hw2
  · intro j hj
    apply hM.bound j
    by_cases hjr : j = r
    · subst hjr; exact hr'
    · by_cases hjp : j = p
      · subst hjp; exact hp'
      · simpa [hjr, hjp] using hj

theorem release_loc {c : CState} {r : RefVar} {x : Var} (hl : c.lender r = some (.loc x)) :
    c.release r = { c with lent := upd c.lent x false } := by simp [CState.release, hl]

theorem release_sel {c : CState} {r : RefVar} {y z : Var} (hl : c.lender r = some (.sel y z)) :
    c.release r = { c with lent := upd (upd c.lent y false) z false } := by simp [CState.release, hl]

theorem m_step_end {c sR sB sP ch} {r : RefVar} (hM : MRel c sR sB sP ch)
    (hs : (checkOp true c (.endBorrow r)).stuck = false)
    (hv : (checkOp true c (.endBorrow r)).viol = []) :
    ∃ sB', stepOpR true sR (.endBorrow r) = some sR ∧
      stepOpB true sB (.endBorrow r) = some sB' ∧
      ∀ φ sP', stepOpP true (fun _ => true) φ sP (.endBorrow r) = some sP' → Sat sP'.cs →
        ∃ ch', MRel (checkOp true c (.endBorrow r)) sR sB' sP' ch' := by
  obtain ⟨hr, hc'⟩ := clean_endBorrow hs (by rw [hv, hM.viol])
  obtain ⟨x, rest, hx, hch⟩ := hM.active_head hr
  obtain ⟨-, htail, ⟨qb, hqb, hqbc⟩, ⟨qp, hqp, hqpc⟩⟩ := hM.head x r rest hch
  have hP : ∀ φ sP', stepOpP true (fun _ => true) φ sP (.endBorrow r) = some sP' →
      sP' = { sP with refs := fupd sP.refs r (some { qp with done := true }),
                      cs := sP.cs ++ [(qp.cur, qp.fin)] } := by
    intro φ sP' h
    simp only [stepOpP, hqp, Option.map_some, Option.some.injEq, ↓reduceIte] at h
    exact h.symm
  have hsatcf : ∀ φ sP', stepOpP true (fun _ => true) φ sP (.endBorrow r) = some sP' →
      Sat sP'.cs → qp.cur = qp.fin := by
    intro φ sP' h hsat
    rw [hP φ sP' h] at hsat
    exact hsat (qp.cur, qp.fin) (by simp)
  cases rest with
  | cons p rest2 =>
    have hlinks := hM.links x
    rw [hch] at hlinks
    obtain ⟨⟨hlp, ⟨qb1, hqb1, hqb1b⟩, -⟩, -⟩ := hlinks
    rw [hqb] at hqb1; cases hqb1
    have hpfroz : c.status p = .frozen := htail p (by simp)
    obtain ⟨pb, hpb⟩ := bound_of hM.brB (by rw [hpfroz]; simp : c.status p ≠ .unborn)
    refine ⟨{ sB with refs := fupd sB.refs p (some { pb with cur := qb.cur }) },
      by simp [stepOpR, hx], by simp [stepOpB, hqb, hqb1b, applyBack, hpb], ?_⟩
    intro φ sP' h hsat
    have hcf := hsatcf φ sP' h hsat
    rw [hP φ sP' h, hc', release_ref hlp hpfroz]
    have hm := m_pop hM hr hx hch qb hqb hqbc pb hpb qp hqp hcf (sP.cs ++ [(qp.cur, qp.fin)])
    exact ⟨_, by simpa using hm⟩
  | nil =>
    obtain ⟨pk, qk, hpk, hqk, hfin, hroot⟩ := hM.root x r (by rw [hch]; rfl)
    rw [hqp] at hpk; cases hpk
    rw [hqb] at hqk; cases hqk
    have hlive : Live c r := Or.inl hr
    rcases hroot with ⟨hl, hback⟩ | ⟨y, z, b, y0, z0, hl, hxb, hback, hn⟩
    · refine ⟨{ sB with store := sB.store.set x qb.cur }, by simp [stepOpR, hx],
        by simp [stepOpB, hqb, hback, applyBack], ?_⟩
      intro φ sP' h hsat
      have hcf := hsatcf φ sP' h hsat
      rw [hP φ sP' h, hc', release_loc hl]
      have hL : ∀ w, ¬ LendsLoc c r w → upd c.lent x false w = c.lent w := by
        intro w hw
        have : w ≠ x := by intro h; subst h; exact hw (Or.inl hl)
        simp [this]
      have hm := m_end_root hM hr hx hch (upd c.lent x false) hL
        { sB with store := sB.store.set x qb.cur } rfl (by simp [hqbc])
        (fun y hy => by simp [hy]) qp hqp hcf (sP.cs ++ [(qp.cur, qp.fin)])
      exact ⟨_, by simpa using hm⟩
    · have hL : ∀ w, ¬ LendsLoc c r w → upd (upd c.lent y false) z false w = c.lent w := by
        intro w hw
        have h1 : w ≠ y := by intro h; subst h; exact hw (Or.inr ⟨w, z, hl, Or.inl rfl⟩)
        have h2 : w ≠ z := by intro h; subst h; exact hw (Or.inr ⟨y, w, hl, Or.inr rfl⟩)
        simp [h1, h2]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at hxb hn
        subst hxb
        refine ⟨{ sB with store := (sB.store.set y y0).set x qb.cur }, by simp [stepOpR, hx],
          by simp [stepOpB, hqb, hback, selBack, applyBack], ?_⟩
        intro φ sP' h hsat
        have hcf := hsatcf φ sP' h hsat
        rw [hP φ sP' h, hc', release_sel hl]
        have hw' : ∀ w, w ≠ x → ((sB.store.set y y0).set x qb.cur) w = sB.store w := by
          intro w hw
          simp only [store_set_apply, hw, ↓reduceIte]
          split
          · rename_i hwy; subst hwy
            obtain ⟨h1, h2⟩ := hn hw
            rw [h1, (hM.free w h2).1]
          · rfl
        have hm := m_end_root hM hr hx hch (upd (upd c.lent y false) x false) hL
          { sB with store := (sB.store.set y y0).set x qb.cur } rfl (by simp [hqbc])
          hw' qp hqp hcf (sP.cs ++ [(qp.cur, qp.fin)])
        exact ⟨_, by simpa using hm⟩
      · simp only [↓reduceIte] at hxb hn
        subst hxb
        refine ⟨{ sB with store := (sB.store.set z z0).set x qb.cur }, by simp [stepOpR, hx],
          by simp [stepOpB, hqb, hback, selBack, applyBack], ?_⟩
        intro φ sP' h hsat
        have hcf := hsatcf φ sP' h hsat
        rw [hP φ sP' h, hc', release_sel hl]
        have hw' : ∀ w, w ≠ x → ((sB.store.set z z0).set x qb.cur) w = sB.store w := by
          intro w hw
          simp only [store_set_apply, hw, ↓reduceIte]
          split
          · rename_i hwz; subst hwz
            obtain ⟨h1, h2⟩ := hn hw
            rw [h1, (hM.free w h2).1]
          · rfl
        have hm := m_end_root hM hr hx hch (upd (upd c.lent x false) z false) hL
          { sB with store := (sB.store.set z z0).set x qb.cur } rfl (by simp [hqbc])
          hw' qp hqp hcf (sP.cs ++ [(qp.cur, qp.fin)])
        exact ⟨_, by simpa using hm⟩

end Sim
end Toy.Prophecy
