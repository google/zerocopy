import Toy.Tricolor.EndOfMarking

/-!
# Barrier soundness: which steps preserve which invariant

* Dijkstra (insertion) barrier: every step preserves the strong invariant.
* Yuasa (deletion) barrier with non-white allocation: every step preserves the weak invariant
  together with its root clause (`RootsProtected`).
* Shaded root loads (a load barrier) with non-white allocation, under any heap barrier
  (including none): every step preserves the strong invariant together with `RootsNonWhite`
  (the theorem involves no root rescan).
-/

namespace Toy.Tricolor

variable {n : Nat}

/-! ## Color bookkeeping -/

/-- `ShadeLe s s'`: the colors of `s'` are those of `s` with some white objects greyed. -/
def ShadeLe (s s' : St n) : Prop :=
  ∀ v, s'.color v = s.color v ∨ (s.color v = .white ∧ s'.color v = .grey)

theorem ShadeLe.black {s s' : St n} (h : ShadeLe s s') {v : Fin n}
    (hv : s'.color v = .black) : s.color v = .black := by
  rcases h v with h | ⟨_, h⟩ <;> rw [h] at hv
  · exact hv
  · cases hv

theorem ShadeLe.white {s s' : St n} (h : ShadeLe s s') {v : Fin n}
    (hv : s'.color v = .white) : s.color v = .white := by
  rcases h v with h | ⟨_, h⟩ <;> rw [h] at hv
  · exact hv
  · cases hv

theorem ShadeLe.grey {s s' : St n} (h : ShadeLe s s') {v : Fin n}
    (hv : s.color v = .grey) : s'.color v = .grey := by
  rcases h v with h | ⟨h', _⟩
  · rw [h, hv]
  · rw [hv] at h'; cases h'

theorem shade_cases (c : Fin n → Color) (y v : Fin n) :
    shade c y v = c v ∨ (c v = .white ∧ shade c y v = .grey) := by
  unfold shade
  split
  · next h => exact Or.inr ⟨h.2, rfl⟩
  · exact Or.inl rfl

theorem shade_self_ne_white (c : Fin n → Color) (y : Fin n) : shade c y y ≠ .white := by
  unfold shade
  split
  · intro h; cases h
  · next h => intro hw; exact h ⟨rfl, hw⟩

theorem shadeLe_of {s s' : St n} (y : Fin n)
    (h : s'.color = shade s.color y ∨ s'.color = s.color) : ShadeLe s s' := by
  intro v
  rcases h with h | h <;> rw [h]
  · exact shade_cases _ _ _
  · exact Or.inl rfl

theorem shadeLe_store (b : Barrier) (s : St n) (x y : Fin n) : ShadeLe s (store b s x y) := by
  apply shadeLe_of y
  by_cases hb : b = .dijkstra
  · left; simp [store, hb]
  · right; simp [store, hb]

theorem shadeLe_erase (b : Barrier) (s : St n) (x z : Fin n) : ShadeLe s (erase b s x z) := by
  apply shadeLe_of z
  by_cases hb : b = .yuasa ∧ s.edge x z = true
  · left; simp only [erase, hb, and_self, ite_true]
  · right; simp only [erase, hb, ite_false]

theorem shadeLe_load (sh : Bool) (s : St n) (y : Fin n) : ShadeLe s (load sh s y) := by
  apply shadeLe_of y
  cases sh
  · right; rfl
  · left; rfl

theorem scan_white_iff {s : St n} {g v : Fin n} :
    (scan s g).color v = .white ↔ v ≠ g ∧ s.color v = .white ∧ s.edge g v = false := by
  simp only [scan]
  by_cases hvg : v = g
  · simp [hvg]
  · simp only [hvg, ite_false]
    cases he : s.edge g v <;> cases hc : s.color v <;> simp [hvg]

theorem scan_black {s : St n} {g v : Fin n} (h : (scan s g).color v = .black) :
    v = g ∨ s.color v = .black := by
  simp only [scan] at h
  by_cases hvg : v = g
  · exact Or.inl hvg
  · right
    simp only [hvg, ite_false] at h
    split at h
    · cases h
    · exact h

theorem scan_grey_of_grey {s : St n} {g v : Fin n} (hv : s.color v = .grey) (hvg : v ≠ g) :
    (scan s g).color v = .grey := by
  simp only [scan, hvg, ite_false, hv]
  split <;> rfl

theorem scan_grey_of_succ {s : St n} {g v : Fin n} (he : s.edge g v = true)
    (hv : s.color v = .white) (hvg : v ≠ g) : (scan s g).color v = .grey := by
  simp [scan, hvg, he, hv]

/-! ## Strong invariant -/

theorem strong_of_shadeLe {s s' : St n} (hs : Strong s)
    (hedge : ∀ x y, s'.edge x y = true → s.edge x y = true) (hcol : ShadeLe s s') :
    Strong s' := by
  intro x y he hx hy
  exact hs x y (hedge x y he) (hcol.black hx) (hcol.white hy)

theorem strong_scan {s : St n} (hs : Strong s) (g : Fin n) : Strong (scan s g) := by
  intro x y he hx hy
  obtain ⟨_, hyw, hgy⟩ := scan_white_iff.mp hy
  rcases scan_black hx with rfl | hxb
  · have he' : s.edge x y = true := he
    rw [he'] at hgy; cases hgy
  · exact hs x y he hxb hyw

theorem strong_store_dijkstra {s : St n} (hs : Strong s) (x y : Fin n) :
    Strong (store .dijkstra s x y) := by
  intro u v he hu hv
  have hcol := shadeLe_store .dijkstra s x y
  by_cases h : u = x ∧ v = y
  · obtain ⟨rfl, rfl⟩ := h
    exact shade_self_ne_white s.color v hv
  · have he' : s.edge u v = true := by
      simpa [store, addEdge, h] using he
    exact hs u v he' (hcol.black hu) (hcol.white hv)

theorem strong_erase {s : St n} (hs : Strong s) (b : Barrier) (x z : Fin n) :
    Strong (erase b s x z) := by
  apply strong_of_shadeLe hs _ (shadeLe_erase b s x z)
  intro u v he
  simp only [erase, delEdge] at he
  split at he
  · cases he
  · exact he

theorem strong_load {s : St n} (hs : Strong s) (sh : Bool) (y : Fin n) :
    Strong (load sh s y) :=
  strong_of_shadeLe hs (fun _ _ h => h) (shadeLe_load sh s y)

theorem strong_drop {s : St n} (hs : Strong s) (r : Fin n) : Strong (drop s r) :=
  strong_of_shadeLe hs (fun _ _ h => h) (fun _ => Or.inl rfl)

theorem strong_alloc {s : St n} (hs : Strong s) {a : Fin n} (hiso : Isolated s a) (c : Color) :
    Strong (alloc s a c) := by
  intro x y he hx hy
  have he' : s.edge x y = true := he
  have hxa : x ≠ a := by rintro rfl; rw [(hiso y).1] at he'; cases he'
  have hya : y ≠ a := by rintro rfl; rw [(hiso x).2] at he'; cases he'
  simp only [alloc, hxa, hya, ite_false] at hx hy
  exact hs x y he' hx hy

theorem strong_rescan {s : St n} (hs : Strong s) : Strong (rescan s) := by
  refine strong_of_shadeLe (s' := rescan s) hs (fun _ _ h => h) ?_
  intro v
  simp only [rescan]
  split
  · next h => exact Or.inr ⟨h.2, rfl⟩
  · exact Or.inl rfl

/-- **Dijkstra barrier soundness.** With the Dijkstra insertion barrier, every enabled step
(collector scan, store, erase, root load, root drop, allocation of any allowed color)
preserves the strong invariant. -/
theorem strong_preserved_of_dijkstra {cfg : Config} (hb : cfg.barrier = .dijkstra)
    {s s' : St n} (hs : Strong s) (hstep : Step cfg s s') : Strong s' := by
  obtain ⟨op, hen, rfl⟩ := hstep
  cases op with
  | scan g => exact strong_scan hs g
  | store x y => simp only [Op.apply, hb]; exact strong_store_dijkstra hs x y
  | erase x z => exact strong_erase hs _ x z
  | load y => exact strong_load hs _ y
  | drop r => exact strong_drop hs r
  | alloc a c => exact strong_alloc hs hen.2.2 c

theorem strong_run_of_dijkstra {cfg : Config} (hb : cfg.barrier = .dijkstra) {s s' : St n}
    {ops : List (Op n)} (hs : Strong s) (hrun : Run cfg s ops s') : Strong s' :=
  Run.invariant Strong (fun _ _ h hst => strong_preserved_of_dijkstra hb h hst) hrun hs

/-! ## Weak invariant -/

/-- Grey protection survives any step that only greys white objects and keeps every edge into
an object that is still white. -/
theorem GreyProtected.lift {s s' : St n} (hcol : ShadeLe s s')
    (hedge : ∀ u v, s.edge u v = true → s'.color v = .white → s'.edge u v = true) :
    ∀ {y}, GreyProtected s y → s'.color y = .white → GreyProtected s' y := by
  intro y h
  induction h with
  | direct hg he _ =>
    intro hy'
    exact GreyProtected.direct (hcol.grey hg) (hedge _ _ he hy') hy'
  | @chain w y hw he _ ih =>
    intro hy'
    rcases hcol w with h | ⟨_, h⟩
    · exact GreyProtected.chain (ih (h.trans hw.white)) (hedge _ _ he hy') hy'
    · exact GreyProtected.direct h (hedge _ _ he hy') hy'

theorem GreyProtected.scan {s : St n} {g : Fin n} :
    ∀ {y}, GreyProtected s y → (scan s g).color y = .white → GreyProtected (scan s g) y := by
  intro y h
  induction h with
  | @direct g0 y hg0 he _ =>
    intro hy'
    obtain ⟨_, _, hgy⟩ := scan_white_iff.mp hy'
    by_cases h0 : g0 = g
    · subst h0; rw [he] at hgy; cases hgy
    · exact GreyProtected.direct (scan_grey_of_grey hg0 h0) he hy'
  | @chain w y hw he _ ih =>
    intro hy'
    obtain ⟨_, _, hgy⟩ := scan_white_iff.mp hy'
    have hww := hw.white
    by_cases hwg : w = g
    · subst hwg; rw [he] at hgy; cases hgy
    · by_cases hgw : s.edge g w = true
      · exact GreyProtected.direct (scan_grey_of_succ hgw hww hwg) he hy'
      · have : (Tricolor.scan s g).color w = .white :=
          scan_white_iff.mpr ⟨hwg, hww, by simpa using hgw⟩
        exact GreyProtected.chain (ih this) he hy'

theorem GreyProtected.alloc {s : St n} {a : Fin n} (hiso : Isolated s a) (c : Color) :
    ∀ {y}, GreyProtected s y → GreyProtected (alloc s a c) y := by
  intro y h
  induction h with
  | @direct g y hg he hy =>
    have hga : g ≠ a := by rintro rfl; rw [(hiso y).1] at he; cases he
    have hya : y ≠ a := by rintro rfl; rw [(hiso g).2] at he; cases he
    exact GreyProtected.direct (g := g) (by simp [Tricolor.alloc, hga, hg]) he
      (by simp [Tricolor.alloc, hya, hy])
  | @chain w y _ he hy ih =>
    have hya : y ≠ a := by rintro rfl; rw [(hiso w).2] at he; cases he
    exact GreyProtected.chain ih he (by simp [Tricolor.alloc, hya, hy])

theorem weak_scan {s : St n} (hw : Weak s) (g : Fin n) : Weak (scan s g) := by
  intro x y he hx hy
  obtain ⟨_, hyw, hgy⟩ := scan_white_iff.mp hy
  rcases scan_black hx with rfl | hxb
  · have he' : s.edge x y = true := he
    rw [he'] at hgy; cases hgy
  · exact GreyProtected.scan (hw x y he hxb hyw) hy

theorem rootsProtected_scan {s : St n} (hr : RootsProtected s) (g : Fin n) :
    RootsProtected (scan s g) := by
  intro r hroot hwr
  exact GreyProtected.scan (hr r hroot (scan_white_iff.mp hwr).2.1) hwr

theorem weak_rootsProtected_store {s : St n} (hw : Weak s) (hr : RootsProtected s)
    (b : Barrier) (x : Fin n) {y : Fin n} (hy : Live s y) :
    Weak (store b s x y) ∧ RootsProtected (store b s x y) := by
  have hcol := shadeLe_store b s x y
  have hedge : ∀ u v, s.edge u v = true → (store b s x y).color v = .white →
      (store b s x y).edge u v = true := by
    intro u v he _
    simp [store, addEdge, he]
  refine ⟨?_, ?_⟩
  · intro u v he hu hv
    by_cases h : u = x ∧ v = y
    · obtain ⟨rfl, rfl⟩ := h
      exact GreyProtected.lift hcol hedge
        (greyProtected_of_live_of_white_of_weak_of_rootsProtected hw hr hy (hcol.white hv)) hv
    · have he' : s.edge u v = true := by simpa [store, addEdge, h] using he
      exact GreyProtected.lift hcol hedge (hw u v he' (hcol.black hu) (hcol.white hv)) hv
  · intro r hroot hwr
    exact GreyProtected.lift hcol hedge (hr r hroot (hcol.white hwr)) hwr

theorem weak_rootsProtected_erase_yuasa {s : St n} (hw : Weak s) (hr : RootsProtected s)
    (x z : Fin n) : Weak (erase .yuasa s x z) ∧ RootsProtected (erase .yuasa s x z) := by
  have hcol := shadeLe_erase .yuasa s x z
  have hedge : ∀ u v, s.edge u v = true → (erase .yuasa s x z).color v = .white →
      (erase .yuasa s x z).edge u v = true := by
    intro u v he hv
    by_cases h : u = x ∧ v = z
    · obtain ⟨rfl, rfl⟩ := h
      exfalso
      simp only [erase, he, and_self, ite_true] at hv
      exact shade_self_ne_white _ _ hv
    · simp [erase, delEdge, h, he]
  have hsub : ∀ u v, (erase .yuasa s x z).edge u v = true → s.edge u v = true := by
    intro u v he
    simp only [erase, delEdge] at he
    split at he
    · cases he
    · exact he
  refine ⟨?_, ?_⟩
  · intro u v he hu hv
    exact GreyProtected.lift hcol hedge (hw u v (hsub u v he) (hcol.black hu) (hcol.white hv)) hv
  · intro r hroot hwr
    exact GreyProtected.lift hcol hedge (hr r hroot (hcol.white hwr)) hwr

theorem weak_rootsProtected_load {s : St n} (hw : Weak s) (hr : RootsProtected s)
    (sh : Bool) {y : Fin n} (hy : Live s y) :
    Weak (load sh s y) ∧ RootsProtected (load sh s y) := by
  have hcol := shadeLe_load sh s y
  have hedge : ∀ u v, s.edge u v = true → (load sh s y).color v = .white →
      (load sh s y).edge u v = true := fun _ _ he _ => he
  refine ⟨?_, ?_⟩
  · intro u v he hu hv
    exact GreyProtected.lift hcol hedge (hw u v he (hcol.black hu) (hcol.white hv)) hv
  · intro r hroot hwr
    by_cases hry : r = y
    · subst hry
      exact GreyProtected.lift hcol hedge
        (greyProtected_of_live_of_white_of_weak_of_rootsProtected hw hr hy (hcol.white hwr)) hwr
    · have : s.root r = true := by simpa [load, hry] using hroot
      exact GreyProtected.lift hcol hedge (hr r this (hcol.white hwr)) hwr

theorem weak_rootsProtected_drop {s : St n} (hw : Weak s) (hr : RootsProtected s) (r : Fin n) :
    Weak (drop s r) ∧ RootsProtected (drop s r) := by
  have hcol : ShadeLe s (drop s r) := fun _ => Or.inl rfl
  have hedge : ∀ u v, s.edge u v = true → (drop s r).color v = .white →
      (drop s r).edge u v = true := fun _ _ he _ => he
  refine ⟨?_, ?_⟩
  · intro u v he hu hv
    exact GreyProtected.lift hcol hedge (hw u v he hu hv) hv
  · intro q hroot hwq
    have : s.root q = true := by
      simp only [drop] at hroot
      split at hroot
      · cases hroot
      · exact hroot
    exact GreyProtected.lift hcol hedge (hr q this hwq) hwq

theorem weak_rootsProtected_alloc {s : St n} (hw : Weak s) (hr : RootsProtected s)
    {a : Fin n} (hiso : Isolated s a) {c : Color} (hc : c ≠ .white) :
    Weak (alloc s a c) ∧ RootsProtected (alloc s a c) := by
  refine ⟨?_, ?_⟩
  · intro x y he hx hy
    have he' : s.edge x y = true := he
    have hxa : x ≠ a := by rintro rfl; rw [(hiso y).1] at he'; cases he'
    have hya : y ≠ a := by rintro rfl; rw [(hiso x).2] at he'; cases he'
    simp only [Tricolor.alloc, hxa, hya, ite_false] at hx hy
    exact GreyProtected.alloc hiso c (hw x y he' hx hy)
  · intro r hroot hwr
    by_cases hra : r = a
    · subst hra; simp [Tricolor.alloc] at hwr; exact absurd hwr hc
    · simp only [Tricolor.alloc, hra, ite_false] at hroot hwr
      exact GreyProtected.alloc hiso c (hr r hroot hwr)

/-- **Yuasa barrier soundness (non-white allocation).** With the Yuasa deletion barrier and an
allocator that never allocates white, every enabled step (a scan of a grey object, a store of a
pointer held in the roots, an erase, a root load of a live object, a root drop, an allocation of
an isolated object) preserves the weak invariant together with its root clause (every white
root is grey protected). The theorem has no hypothesis on root-load shading. -/
theorem weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc {cfg : Config}
    (hb : cfg.barrier = .yuasa)
    (halloc : ∀ c, cfg.allocOk c = true → c ≠ .white) {s s' : St n}
    (hw : Weak s) (hr : RootsProtected s) (hstep : Step cfg s s') :
    Weak s' ∧ RootsProtected s' := by
  obtain ⟨op, hen, rfl⟩ := hstep
  cases op with
  | scan g => exact ⟨weak_scan hw g, rootsProtected_scan hr g⟩
  | store x y => exact weak_rootsProtected_store hw hr _ x (Live.root hen)
  | erase x z => simp only [Op.apply, hb]; exact weak_rootsProtected_erase_yuasa hw hr x z
  | load y => exact weak_rootsProtected_load hw hr _ hen
  | drop r => exact weak_rootsProtected_drop hw hr r
  | alloc a c => exact weak_rootsProtected_alloc hw hr hen.2.2 (halloc c hen.1)

theorem weak_rootsProtected_run_of_yuasa_of_nonWhiteAlloc {cfg : Config}
    (hb : cfg.barrier = .yuasa)
    (halloc : ∀ c, cfg.allocOk c = true → c ≠ .white) {s s' : St n} {ops : List (Op n)}
    (hw : Weak s) (hr : RootsProtected s) (hrun : Run cfg s ops s') :
    Weak s' ∧ RootsProtected s' :=
  Run.invariant (fun t => Weak t ∧ RootsProtected t)
    (fun _ _ h hst => weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc hb halloc h.1 h.2 hst)
    hrun ⟨hw, hr⟩

/-! ## Allocation color -/

/-- **Allocation color under the weak invariant.** Allocating an isolated object into the roots
preserves the root clause exactly when the allocation color is non-white. -/
theorem rootsProtected_alloc_iff_ne_white {s : St n} (hr : RootsProtected s) {a : Fin n}
    (hiso : Isolated s a) (c : Color) : RootsProtected (alloc s a c) ↔ c ≠ .white := by
  constructor
  · intro h hc
    have hp := h a (by simp [Tricolor.alloc]) (by simp [Tricolor.alloc, hc])
    cases hp with
    | direct _ he _ =>
      have he' : s.edge _ a = true := he
      rw [(hiso _).2] at he'; cases he'
    | chain _ he _ =>
      have he' : s.edge _ a = true := he
      rw [(hiso _).2] at he'; cases he'
  · intro hc r hroot hwr
    by_cases hra : r = a
    · subst hra; simp [Tricolor.alloc] at hwr; exact absurd hwr hc
    · simp only [Tricolor.alloc, hra, ite_false] at hroot hwr
      exact GreyProtected.alloc hiso c (hr r hroot hwr)

/-- **Allocation color under non-white roots.** Allocating into the roots preserves
`RootsNonWhite` exactly when the allocation color is non-white. -/
theorem rootsNonWhite_alloc_iff_ne_white {s : St n} (hr : RootsNonWhite s) (a : Fin n)
    (c : Color) : RootsNonWhite (alloc s a c) ↔ c ≠ .white := by
  constructor
  · intro h hc
    exact h a (by simp [Tricolor.alloc]) (by simp [Tricolor.alloc, hc])
  · intro hc r hroot hwr
    by_cases hra : r = a
    · subst hra; simp [Tricolor.alloc] at hwr; exact hc hwr
    · simp only [Tricolor.alloc, hra, ite_false] at hroot hwr
      exact hr r hroot hwr

/-! ## Non-white roots -/

theorem rootsNonWhite_scan {s : St n} (hr : RootsNonWhite s) (g : Fin n) :
    RootsNonWhite (scan s g) :=
  fun r hroot hwr => hr r hroot (scan_white_iff.mp hwr).2.1

theorem rootsNonWhite_of_shadeLe {s s' : St n} (hr : RootsNonWhite s)
    (hroot : ∀ r, s'.root r = true → s.root r = true) (hcol : ShadeLe s s') :
    RootsNonWhite s' :=
  fun r h hw => hr r (hroot r h) (hcol.white hw)

theorem rootsNonWhite_load_shaded {s : St n} (hr : RootsNonWhite s) (y : Fin n) :
    RootsNonWhite (load true s y) := by
  intro r hroot hwr
  by_cases hry : r = y
  · subst hry; exact shade_self_ne_white s.color r hwr
  · have : s.root r = true := by simpa [load, hry] using hroot
    exact hr r this ((shadeLe_load true s y).white hwr)

theorem rootsNonWhite_drop {s : St n} (hr : RootsNonWhite s) (r : Fin n) :
    RootsNonWhite (drop s r) := by
  refine rootsNonWhite_of_shadeLe (s' := drop s r) hr ?_ (fun _ => Or.inl rfl)
  intro q hq
  simp only [drop] at hq
  split at hq
  · cases hq
  · exact hq

theorem rootsNonWhite_rescan (s : St n) : RootsNonWhite (rescan s) := by
  intro r hroot hwr
  simp only [rescan] at hwr hroot
  split at hwr
  · cases hwr
  · next h => exact h ⟨hroot, hwr⟩

/-- A store of a non-white object preserves the strong invariant under any barrier. -/
theorem strong_store_of_nonWhite {s : St n} (hs : Strong s) (b : Barrier) (x : Fin n)
    {y : Fin n} (hy : s.color y ≠ .white) : Strong (store b s x y) := by
  intro u v he hu hv
  have hcol := shadeLe_store b s x y
  by_cases h : u = x ∧ v = y
  · obtain ⟨rfl, rfl⟩ := h
    exact hy (hcol.white hv)
  · have he' : s.edge u v = true := by simpa [store, addEdge, h] using he
    exact hs u v he' (hcol.black hu) (hcol.white hv)

/-- **Load-barrier (black mutator) soundness, under any heap barrier.** With shaded root loads
and an allocator that never allocates white, every enabled step preserves the strong invariant
together with `RootsNonWhite`, whatever the heap barrier is (including none): a heap store writes
a pointer held in the roots, which `RootsNonWhite` keeps non-white. -/
theorem strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc {cfg : Config}
    (hsh : cfg.shadeLoads = true) (halloc : ∀ c, cfg.allocOk c = true → c ≠ .white)
    {s s' : St n} (hs : Strong s) (hr : RootsNonWhite s) (hstep : Step cfg s s') :
    Strong s' ∧ RootsNonWhite s' := by
  obtain ⟨op, hen, rfl⟩ := hstep
  cases op with
  | scan g => exact ⟨strong_scan hs g, rootsNonWhite_scan hr g⟩
  | store x y =>
    exact ⟨strong_store_of_nonWhite hs _ x (hr y hen),
      rootsNonWhite_of_shadeLe hr (fun _ h => h) (shadeLe_store _ s x y)⟩
  | erase x z =>
    exact ⟨strong_erase hs _ x z,
      rootsNonWhite_of_shadeLe hr (fun _ h => h) (shadeLe_erase _ s x z)⟩
  | load y =>
    simp only [Op.apply, hsh]
    exact ⟨strong_load hs true y, rootsNonWhite_load_shaded hr y⟩
  | drop r => exact ⟨strong_drop hs r, rootsNonWhite_drop hr r⟩
  | alloc a c =>
    exact ⟨strong_alloc hs hen.2.2 c, (rootsNonWhite_alloc_iff_ne_white hr a c).mpr (halloc c hen.1)⟩

/-! ## Allocation of non-isolated objects (state-level lemmas)

The step relation only allocates isolated objects. These lemmas are about the state update
`alloc` alone, applied to an object that may already have pointers (an object whose fields are
initialized at allocation time); they are not steps of the system. -/

/-- Allocating an object grey preserves the strong invariant even if the object already has
pointers: a grey object is neither the black source nor the white target of an edge. -/
theorem strong_alloc_grey {s : St n} (hs : Strong s) (a : Fin n) : Strong (alloc s a .grey) := by
  intro x y he hx hy
  have he' : s.edge x y = true := he
  have hxa : x ≠ a := by
    rintro rfl; simp [Tricolor.alloc] at hx
  have hya : y ≠ a := by
    rintro rfl; simp [Tricolor.alloc] at hy
  simp only [Tricolor.alloc, hxa, hya, ite_false] at hx hy
  exact hs x y he' hx hy

/-- Allocating an object black preserves the strong invariant even if the object already has
pointers, provided every object it points to is non-white (its initial targets were shaded). -/
theorem strong_alloc_black_of_successors_nonWhite {s : St n} (hs : Strong s) {a : Fin n}
    (hsucc : ∀ v, s.edge a v = true → s.color v ≠ .white) : Strong (alloc s a .black) := by
  intro x y he hx hy
  have he' : s.edge x y = true := he
  have hya : y ≠ a := by
    rintro rfl; simp [Tricolor.alloc] at hy
  simp only [Tricolor.alloc, hya, ite_false] at hy
  by_cases hxa : x = a
  · subst hxa; exact hsucc y he' hy
  · simp only [Tricolor.alloc, hxa, ite_false] at hx
    exact hs x y he' hx hy

/-- Under `RootsNonWhite`, allocating an object black preserves the strong invariant even if
the object already has pointers, provided every object it points to is held in the roots
(fields initialized from registers, which a load barrier keeps non-white). -/
theorem strong_alloc_black_of_successors_held {s : St n} (hs : Strong s)
    (hr : RootsNonWhite s) {a : Fin n} (hheld : ∀ v, s.edge a v = true → s.root v = true) :
    Strong (alloc s a .black) :=
  strong_alloc_black_of_successors_nonWhite hs (fun v he => hr v (hheld v he))

end Toy.Tricolor
