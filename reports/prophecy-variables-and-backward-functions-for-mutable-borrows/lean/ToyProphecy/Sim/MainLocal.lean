import ToyProphecy.Sim.MainDefs

/-!
# Proof infrastructure: simulation of the main program — local operations

Auxiliary lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

theorem MRel.eval {c sR sB sP ch} (hM : MRel c sR sB sP ch) :
    ∀ e, ExprOK true c e → ∃ v, evalR true sR e = some v ∧ evalB true sB e = some v ∧
      evalP true sP e = some v := by
  apply eval_agree
  · intro k hk
    obtain ⟨x, rest, hx, hch⟩ := hM.active_head hk
    obtain ⟨-, -, ⟨q, hq, hqc⟩, ⟨p, hp, hpc⟩⟩ := hM.head x k rest hch
    exact ⟨x, hx, by simp [hq, hqc], by simp [hp, hpc]⟩
  · intro x _ hx
    apply hM.free x
    cases h : ch x with
    | nil => rfl
    | cons k l => have := hM.lent_of_ch (by simp [h] : ch x ≠ []); rw [hx] at this; cases this

theorem MRel.ch_nil_of_not_lent {c sR sB sP ch} (hM : MRel c sR sB sP ch) {x : Var}
    (hx : c.lent x = false) : ch x = [] := by
  cases h : ch x with
  | nil => rfl
  | cons k l => have := hM.lent_of_ch (by simp [h] : ch x ≠ []); rw [hx] at this; cases this

theorem MRel.live_of_mem {c sR sB sP ch} (hM : MRel c sR sB sP ch) {k : RefVar} {x : Var}
    (h : k ∈ ch x) : Live c k := ((hM.mem k x).1 h).1

theorem MRel.unborn_not_mem {c sR sB sP ch} (hM : MRel c sR sB sP ch) {k : RefVar}
    (hk : c.status k = .unborn) (x : Var) : k ∉ ch x := by
  intro h; rcases hM.live_of_mem h with h | h <;> rw [hk] at h <;> cases h

theorem ne_nil_of_getLast? {α : Type} {l : List α} {k : α} (h : l.getLast? = some k) : l ≠ [] := by
  intro h'; subst h'; simp at h

theorem live_unborn_ne {c : CState} {k t : RefVar} (hk : Live c k) (ht : c.status t = .unborn) :
    k ≠ t := by
  intro h; subst h; rcases hk with h | h <;> rw [ht] at h <;> cases h

theorem links_refs_eq {c : CState} {sB sB' : BState} {sP sP' : PState} {l : List RefVar}
    (h : Links c sB sP l) (hb : sB'.refs = sB.refs) (hp : sP'.refs = sP.refs) : Links c sB' sP' l :=
  links_congr l h (fun _ _ => rfl) (fun k _ => by rw [hb]) (fun k _ => by rw [hp])
    (fun k _ => by rw [hp])

/-! ## `x = e` -/

theorem m_step_assign {c sR sB sP ch} {x : Var} {e : Expr} (hM : MRel c sR sB sP ch)
    (hs : (checkOp true c (.assign x e)).stuck = false)
    (hv : (checkOp true c (.assign x e)).viol = []) :
    ∃ sR' sB', stepOpR true sR (.assign x e) = some sR' ∧
      stepOpB true sB (.assign x e) = some sB' ∧
      ∀ φ sP', stepOpP true (fun _ => true) φ sP (.assign x e) = some sP' →
        MRel (checkOp true c (.assign x e)) sR' sB' sP' ch := by
  obtain ⟨hok, hlx, hc'⟩ := clean_assign hs (by rw [hv, hM.viol])
  obtain ⟨v, hvR, hvB, hvP⟩ := hM.eval e hok
  have hchx := hM.ch_nil_of_not_lent hlx
  refine ⟨{ sR with store := sR.store.set x v }, { sB with store := sB.store.set x v },
    by simp [stepOpR, hvR], by simp [stepOpB, hvB], ?_⟩
  intro φ sP' hP
  simp only [stepOpP, hvP, ↓reduceIte, Option.map_some, Option.some.injEq] at hP
  subst hP
  rw [hc']
  have hne : ∀ y, ch y ≠ [] → y ≠ x := by intro y hy h; subst h; exact hy hchx
  refine ⟨hM.stuck, hM.viol, hM.brR, hM.brB, hM.brP, hM.nodup, hM.mem, ?_,
    fun y => links_refs_eq (hM.links y) rfl rfl, ?_, ?_, hM.lendsLent, hM.lendsUniq, hM.bound⟩
  · intro y k rest h
    have hyx := hne y (by simp [h])
    simpa [hyx] using hM.head y k rest h
  · intro y k hk
    have hyx := hne y (ne_nil_of_getLast? hk)
    refine rootOK_congr (hM.root y k hk) rfl rfl rfl (by simp [hyx]) ?_
    intro n hn hchn _
    have hnl := hM.lendsLent k n (hM.live_of_mem (List.mem_of_getLast? hk)) hn
    have hnx : n ≠ x := by intro h; subst h; rw [hlx] at hnl; cases hnl
    exact ⟨by simp [hnx], hchn⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; simp
    · simpa [hyx] using hM.free y hy

/-! ## `r = &mut x` -/

theorem m_step_borrow {c sR sB sP ch} {k : RefVar} {x : Var} (hM : MRel c sR sB sP ch)
    (hs : (checkOp true c (.borrow k x)).stuck = false)
    (hv : (checkOp true c (.borrow k x)).viol = []) :
    ∃ sR' sB', stepOpR true sR (.borrow k x) = some sR' ∧
      stepOpB true sB (.borrow k x) = some sB' ∧
      ∀ φ sP', stepOpP true (fun _ => true) φ sP (.borrow k x) = some sP' →
        MRel (checkOp true c (.borrow k x)) sR' sB' sP' (fupd ch x [k]) := by
  obtain ⟨hlx, hk, hc'⟩ := clean_borrow hs (by rw [hv, hM.viol])
  have hchx := hM.ch_nil_of_not_lent hlx
  obtain ⟨hfB, hfP⟩ := hM.free x hchx
  refine ⟨{ sR with refs := fupd sR.refs k (some x) },
    { sB with refs := fupd sB.refs k (some { cur := sB.store x, back := fun v => [(.loc x, v)] }) },
    by simp [stepOpR], by simp [stepOpB], ?_⟩
  intro φ sP' hP
  simp only [stepOpP, ↓reduceIte, Option.some.injEq] at hP
  subst hP
  have hst' : (checkOp true c (.borrow k x)).status = upd c.status k .active := by rw [hc']
  have hle' : (checkOp true c (.borrow k x)).lent = upd c.lent x true := by rw [hc']
  have hld' : (checkOp true c (.borrow k x)).lender = upd c.lender k (some (.loc x)) := by rw [hc']
  have hbd' : (checkOp true c (.borrow k x)).bound = c.bound ++ [k] := by rw [hc']
  have hsk' : (checkOp true c (.borrow k x)).stuck = false := hs
  have hvl' : (checkOp true c (.borrow k x)).viol = [] := hv
  have hkR : sR.refs k = none := (hM.brR k).1 hk
  have hkB : sB.refs k = none := (hM.brB k).1 hk
  have hkP : sP.refs k = none := (hM.brP k).1 hk
  have hkch := hM.unborn_not_mem hk
  have hne : ∀ y, ch y ≠ [] → y ≠ x := by intro y hy h; subst h; exact hy hchx
  have hlive : ∀ j, Live c j → j ≠ k := fun j hj => live_unborn_ne hj hk
  have hliveC : ∀ j, Live (checkOp true c (.borrow k x)) j ↔ (j = k ∨ Live c j) := by
    intro j; by_cases hj : j = k
    · subst hj; simp [Live, hst']
    · simp [Live, hj, hst']
  have conv : ∀ j w, j ≠ k → LendsLoc (checkOp true c (.borrow k x)) j w → LendsLoc c j w := by
    intro j w hj h; simpa [LendsLoc, hj, hld'] using h
  have atk : ∀ w, LendsLoc (checkOp true c (.borrow k x)) k w → w = x := by
    intro w h; rcases h with h | ⟨y, z, h, -⟩
    · simp [hld'] at h; exact h.symm
    · simp [hld'] at h
  rw [hc'] at hliveC conv atk ⊢
  refine ⟨hM.stuck, hM.viol, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; by_cases hj : j = k
    · subst hj; simp
    · simp [hj, hM.brR j]
  · intro j; by_cases hj : j = k
    · subst hj; simp
    · simp [hj, hM.brB j]
  · intro j; by_cases hj : j = k
    · subst hj; simp
    · simp [hj, hM.brP j]
  · intro y; by_cases hy : y = x
    · subst hy; simp
    · simp [hy, hM.nodup y]
  · intro j y
    rw [hliveC j]
    by_cases hy : y = x
    · subst hy
      by_cases hj : j = k
      · subst hj; simp
      · simp only [fupd_apply, ↓reduceIte, List.mem_singleton, hj, false_or, false_iff, not_and]
        intro hj' hjy
        have := (hM.mem j y).2 ⟨hj', by simpa [hj] using hjy⟩
        rw [hchx] at this; simp at this
    · by_cases hj : j = k
      · subst hj; simp [hy, hkch y, Ne.symm hy]
      · simp [hy, hj, hM.mem j y]
  · intro y j rest h
    by_cases hy : y = x
    · subst hy
      simp only [fupd_apply, ↓reduceIte, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, by simp, ⟨{ cur := sB.store y, back := fun v => [(.loc y, v)] }, by simp, hfB⟩,
        ⟨{ cur := sP.store y, fin := φ sP.next, done := false }, by simp, hfP⟩⟩
    · simp only [fupd_apply, hy, ↓reduceIte] at h
      have hjk : j ≠ k := fun h' => hkch y (h' ▸ (by rw [h]; simp))
      obtain ⟨h1, h2, ⟨q, hq, hqc⟩, ⟨p, hp, hpc⟩⟩ := hM.head y j rest h
      refine ⟨by simp [hjk, h1], fun p' hp' => ?_, ⟨q, by simp [hjk, hq], hqc⟩,
        ⟨p, by simp [hjk, hp], by simp [hpc]⟩⟩
      have hpk : p' ≠ k := fun h' => hkch y (h' ▸ (by rw [h]; exact List.mem_cons_of_mem _ hp'))
      simp [hpk, h2 p' hp']
  · intro y
    by_cases hy : y = x
    · subst hy; simp [Links]
    · simp only [fupd_apply, hy, ↓reduceIte]
      apply links_congr (ch y) (hM.links y)
      · intro j hj; have : j ≠ k := fun h => hkch y (h ▸ hj); simp [this]
      · intro j hj; have : j ≠ k := fun h => hkch y (h ▸ hj); simp [this]
      · intro j hj; have : j ≠ k := fun h => hkch y (h ▸ hj); simp [this]
      · intro j hj
        have : j ≠ k := fun h => hkch y (h ▸ List.mem_of_mem_tail hj)
        simp [this]
  · intro y j hj
    by_cases hy : y = x
    · subst hy
      simp only [fupd_apply, ↓reduceIte] at hj
      simp at hj; subst hj
      exact ⟨{ cur := sP.store y, fin := φ sP.next, done := false },
        { cur := sB.store y, back := fun v => [(.loc y, v)] }, by simp, by simp, by simp,
        Or.inl ⟨by simp, rfl⟩⟩
    · simp only [fupd_apply, hy, ↓reduceIte] at hj
      have hjm := List.mem_of_getLast? hj
      have hjk : j ≠ k := fun h => hkch y (h ▸ hjm)
      apply rootOK_congr (hM.root y j hj) (by simp [hjk]) (by simp [hjk]) (by simp [hjk])
        (by simp [hy])
      intro n hn hchn hny
      have hnl := hM.lendsLent j n (hM.live_of_mem hjm) hn
      have hnx : n ≠ x := by intro h; subst h; rw [hlx] at hnl; cases hnl
      exact ⟨rfl, by simp [hnx, hchn]⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; simp at hy
    · simp only [fupd_apply, hyx, ↓reduceIte] at hy
      simpa [hyx] using hM.free y hy
  · intro j w hj hw
    rw [hliveC j] at hj
    by_cases hjk : j = k
    · subst hjk
      rcases hw with hw | ⟨y, z, hw, -⟩
      · simp at hw; subst hw; simp
      · simp at hw
    · rcases hj with hj | hj
      · exact absurd hj hjk
      · have hw' : LendsLoc c j w := by simpa [LendsLoc, hjk] using hw
        have := hM.lendsLent j w hj hw'
        simp only [upd_apply]; split <;> simp [this]
  · intro j1 j2 w h1 h2 hw1 hw2
    rw [hliveC] at h1 h2
    by_cases hj1 : j1 = k
    · by_cases hj2 : j2 = k
      · rw [hj1, hj2]
      · exfalso
        rcases h2 with h2 | h2
        · exact hj2 h2
        · have := atk w (hj1 ▸ hw1); subst this
          have := hM.lendsLent j2 w h2 (conv j2 w hj2 hw2)
          rw [hlx] at this; cases this
    · by_cases hj2 : j2 = k
      · exfalso
        rcases h1 with h1 | h1
        · exact hj1 h1
        · have := atk w (hj2 ▸ hw2); subst this
          have := hM.lendsLent j1 w h1 (conv j1 w hj1 hw1)
          rw [hlx] at this; cases this
      · exact hM.lendsUniq j1 j2 w (h1.resolve_left hj1) (h2.resolve_left hj2)
          (conv j1 w hj1 hw1) (conv j2 w hj2 hw2)
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; simp
    · simp only [upd_apply, hjk, ↓reduceIte] at hj
      exact List.mem_append_left _ (hM.bound j hj)

/-! ## `r = if c ≠ 0 { &mut x } else { &mut y }` -/

theorem m_sel_core {c sR sB sP ch} {k : RefVar} {x y a : Var} (b : Bool) (w : Int)
    (ha : a = if b then x else y) (hM : MRel c sR sB sP ch)
    (hlx : c.lent x = false) (hly : c.lent y = false) (hk : c.status k = .unborn) :
    MRel { c with lent := upd (upd c.lent x true) y true, status := upd c.status k .active,
                  lender := upd c.lender k (some (.sel x y)), bound := c.bound ++ [k] }
      { sR with refs := fupd sR.refs k (some a) }
      { sB with refs := fupd sB.refs k (some { cur := sB.store a, back := selBack b x y (sB.store x) (sB.store y) }) }
      { sP with refs := fupd sP.refs k (some { cur := sP.store a, fin := w, done := false }), store := sP.store.set a w, next := sP.next + 1 }
      (fupd ch a [k]) := by
  have hchx := hM.ch_nil_of_not_lent hlx
  have hchy := hM.ch_nil_of_not_lent hly
  have hla : c.lent a = false := by rw [ha]; cases b <;> simp [hlx, hly]
  have hcha : ch a = [] := hM.ch_nil_of_not_lent hla
  obtain ⟨hfB, hfP⟩ := hM.free a hcha
  have hkR : sR.refs k = none := (hM.brR k).1 hk
  have hkB : sB.refs k = none := (hM.brB k).1 hk
  have hkP : sP.refs k = none := (hM.brP k).1 hk
  have hkch := hM.unborn_not_mem hk
  have hne : ∀ z, ch z ≠ [] → z ≠ a := by intro z hz h; subst h; exact hz hcha
  refine ⟨hM.stuck, hM.viol, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; by_cases hj : j = k
    · subst hj; simp
    · simp [hj, hM.brR j]
  · intro j; by_cases hj : j = k
    · subst hj; simp
    · simp [hj, hM.brB j]
  · intro j; by_cases hj : j = k
    · subst hj; simp
    · simp [hj, hM.brP j]
  · intro z; by_cases hz : z = a
    · subst hz; simp
    · simp [hz, hM.nodup z]
  · intro j z
    by_cases hz : z = a
    · subst hz
      by_cases hj : j = k
      · subst hj; simp [Live]
      · simp only [fupd_apply, ↓reduceIte, List.mem_singleton, hj, false_iff, not_and, Live,
          upd_apply]
        intro hj' hjz
        have := (hM.mem j z).2 ⟨hj', hjz⟩
        rw [hcha] at this; simp at this
    · by_cases hj : j = k
      · subst hj; simp [hz, hkch z, Ne.symm hz, Live]
      · simp [hz, hj, hM.mem j z, Live]
  · intro z j rest h
    by_cases hz : z = a
    · subst hz
      simp only [fupd_apply, ↓reduceIte, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, by simp, ⟨{ cur := sB.store z, back := selBack b x y (sB.store x) (sB.store y) },
        by simp, hfB⟩, ⟨{ cur := sP.store z, fin := w, done := false }, by simp, hfP⟩⟩
    · simp only [fupd_apply, hz, ↓reduceIte] at h
      have hjk : j ≠ k := fun h' => hkch z (h' ▸ (by rw [h]; simp))
      obtain ⟨h1, h2, ⟨q, hq, hqc⟩, ⟨p, hp, hpc⟩⟩ := hM.head z j rest h
      refine ⟨by simp [hjk, h1], fun p' hp' => ?_, ⟨q, by simp [hjk, hq], hqc⟩,
        ⟨p, by simp [hjk, hp], by simp [hpc]⟩⟩
      have hpk : p' ≠ k := fun h' => hkch z (h' ▸ (by rw [h]; exact List.mem_cons_of_mem _ hp'))
      simp [hpk, h2 p' hp']
  · intro z
    by_cases hz : z = a
    · subst hz; simp [Links]
    · simp only [fupd_apply, hz, ↓reduceIte]
      apply links_congr (ch z) (hM.links z)
      · intro j hj; have : j ≠ k := fun h => hkch z (h ▸ hj); simp [this]
      · intro j hj; have : j ≠ k := fun h => hkch z (h ▸ hj); simp [this]
      · intro j hj; have : j ≠ k := fun h => hkch z (h ▸ hj); simp [this]
      · intro j hj
        have : j ≠ k := fun h => hkch z (h ▸ List.mem_of_mem_tail hj)
        simp [this]
  · intro z j hj
    by_cases hz : z = a
    · subst hz
      simp only [fupd_apply, ↓reduceIte] at hj
      simp at hj; subst hj
      refine ⟨{ cur := sP.store z, fin := w, done := false },
        { cur := sB.store z, back := selBack b x y (sB.store x) (sB.store y) }, by simp, by simp,
        by simp, Or.inr ⟨x, y, b, sB.store x, sB.store y, by simp, ha, rfl, ?_⟩⟩
      intro hn
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at ha hn ⊢
        subst ha
        exact ⟨(hM.free x hchx).1, by simp [hn, hchx]⟩
      · simp only [↓reduceIte] at ha hn ⊢
        subst ha
        exact ⟨(hM.free y hchy).1, by simp [hn, hchy]⟩
    · simp only [fupd_apply, hz, ↓reduceIte] at hj
      have hjm := List.mem_of_getLast? hj
      have hjk : j ≠ k := fun h => hkch z (h ▸ hjm)
      refine rootOK_congr (hM.root z j hj) (by simp [hjk]) (by simp [hjk]) (by simp [hjk])
        (by simp [hz]) ?_
      intro n hn hchn hnz
      have hnl := hM.lendsLent j n (hM.live_of_mem hjm) hn
      have hna : n ≠ a := by intro h; subst h; rw [hla] at hnl; cases hnl
      exact ⟨rfl, by simp [hna, hchn]⟩
  · intro z hz
    by_cases hza : z = a
    · subst hza; simp at hz
    · simp only [fupd_apply, hza, ↓reduceIte] at hz
      simpa [hza] using hM.free z hz
  · intro j v hj hv
    by_cases hjk : j = k
    · subst hjk
      rcases hv with hv | ⟨y', z', hv, hw⟩
      · simp at hv
      · simp at hv
        obtain ⟨rfl, rfl⟩ := hv
        rcases hw with rfl | rfl <;> simp
    · have hj' : Live c j := by simpa [Live, hjk] using hj
      have hv' : LendsLoc c j v := by simpa [LendsLoc, hjk] using hv
      have := hM.lendsLent j v hj' hv'
      simp only [upd_apply]; split <;> (try split) <;> simp [this]
  · intro j1 j2 v h1 h2 hv1 hv2
    have conv : ∀ j, j ≠ k → LendsLoc { c with lent := upd (upd c.lent x true) y true, status := upd c.status k .active, lender := upd c.lender k (some (.sel x y)), bound := c.bound ++ [k] } j v → LendsLoc c j v := by
      intro j hj h; simpa [LendsLoc, hj] using h
    have atk : LendsLoc { c with lent := upd (upd c.lent x true) y true, status := upd c.status k .active, lender := upd c.lender k (some (.sel x y)), bound := c.bound ++ [k] } k v → v = x ∨ v = y := by
      intro h; rcases h with h | ⟨y', z', h, hw⟩
      · simp at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; exact hw
    have liveC : ∀ j, j ≠ k → Live { c with lent := upd (upd c.lent x true) y true, status := upd c.status k .active, lender := upd c.lender k (some (.sel x y)), bound := c.bound ++ [k] } j → Live c j := by
      intro j hj h; simpa [Live, hj] using h
    have notlent : ∀ j, j ≠ k → Live c j → LendsLoc c j v → v ≠ x ∧ v ≠ y := by
      intro j hj hl hv
      have := hM.lendsLent j v hl hv
      constructor
      · intro h; subst h; rw [hlx] at this; cases this
      · intro h; subst h; rw [hly] at this; cases this
    by_cases hj1 : j1 = k
    · by_cases hj2 : j2 = k
      · rw [hj1, hj2]
      · exfalso
        have hv := atk (hj1 ▸ hv1)
        have := notlent j2 hj2 (liveC j2 hj2 h2) (conv j2 hj2 hv2)
        rcases hv with h | h
        · exact this.1 h
        · exact this.2 h
    · by_cases hj2 : j2 = k
      · exfalso
        have hv := atk (hj2 ▸ hv2)
        have := notlent j1 hj1 (liveC j1 hj1 h1) (conv j1 hj1 hv1)
        rcases hv with h | h
        · exact this.1 h
        · exact this.2 h
      · exact hM.lendsUniq j1 j2 v (liveC j1 hj1 h1) (liveC j2 hj2 h2)
          (conv j1 hj1 hv1) (conv j2 hj2 hv2)
  · intro j hj
    by_cases hjk : j = k
    · subst hjk; simp
    · simp only [upd_apply, hjk, ↓reduceIte] at hj
      exact List.mem_append_left _ (hM.bound j hj)

theorem m_step_borrowSel {c sR sB sP ch} {k : RefVar} {e : Expr} {x y : Var}
    (hM : MRel c sR sB sP ch)
    (hs : (checkOp true c (.borrowSel k e x y)).stuck = false)
    (hv : (checkOp true c (.borrowSel k e x y)).viol = []) :
    ∃ sR' sB', stepOpR true sR (.borrowSel k e x y) = some sR' ∧
      stepOpB true sB (.borrowSel k e x y) = some sB' ∧
      ∀ φ sP', stepOpP true (fun _ => true) φ sP (.borrowSel k e x y) = some sP' →
        ∃ ch', MRel (checkOp true c (.borrowSel k e x y)) sR' sB' sP' ch' := by
  obtain ⟨hok, hlx, hly, hk, hc'⟩ := clean_borrowSel hs (by rw [hv, hM.viol])
  obtain ⟨v, hvR, hvB, hvP⟩ := hM.eval e hok
  rw [hc']
  by_cases hv0 : v = 0
  · subst hv0
    refine ⟨{ sR with refs := fupd sR.refs k (some y) },
      { sB with refs := fupd sB.refs k (some { cur := sB.store y, back := selBack false x y (sB.store x) (sB.store y) }) },
      by simp [stepOpR, hvR], by simp [stepOpB, hvB], ?_⟩
    intro φ sP' hP
    simp only [stepOpP, hvP, ↓reduceIte, Option.map_some, Option.some.injEq, ne_eq,
      not_true_eq_false] at hP
    subst hP
    exact ⟨_, m_sel_core (k := k) (x := x) (y := y) (a := y) false (φ sP.next) rfl hM hlx hly hk⟩
  · refine ⟨{ sR with refs := fupd sR.refs k (some x) },
      { sB with refs := fupd sB.refs k (some { cur := sB.store x, back := selBack true x y (sB.store x) (sB.store y) }) },
      by simp [stepOpR, hvR, hv0], by simp [stepOpB, hvB, hv0], ?_⟩
    intro φ sP' hP
    simp only [stepOpP, hvP, ↓reduceIte, Option.map_some, Option.some.injEq, ne_eq, hv0,
      not_false_eq_true] at hP
    subst hP
    exact ⟨_, m_sel_core (k := k) (x := x) (y := y) (a := x) true (φ sP.next) rfl hM hlx hly hk⟩

end Sim
end Toy.Prophecy
