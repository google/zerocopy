import Toy.Tricolor.Basic

/-!
# Concrete states and definition examples

Each core definition of `Basic.lean` gets at least one proved positive example (an intended
instance it admits) and one proved negative example (an instance it must reject). Examples
for `Step`, `Run`, `ScansOnly` and the termination definitions are in `RunExamples.lean`.
-/

namespace Toy.Tricolor

/-- Build a concrete state from an edge list, a root list and a color list (objects beyond
the color list are white). -/
def mk (n : Nat) (edges : List (Nat × Nat)) (roots : List Nat) (colors : List Color) : St n :=
  { edge := fun u v => edges.contains (u.val, v.val)
    root := fun r => roots.contains r.val
    color := fun x => colors.getD x.val .white }

/-- Root `0` is black and points to the white object `1`; nothing is grey. -/
def sBlackWhite : St 2 := mk 2 [(0, 1)] [0] [.black, .white]
/-- Root `0` is grey and points to the white object `1`. -/
def sGreyWhite : St 2 := mk 2 [(0, 1)] [0] [.grey, .white]
/-- A single white root with no edges. -/
def sWhiteRoot : St 1 := mk 1 [] [0] [.white]
/-- Black root `0` points to grey `1` and to white `2`; grey `1` also points to `2`. -/
def sWeakNotStrong : St 3 := mk 3 [(0, 1), (1, 2), (0, 2)] [0] [.black, .grey, .white]
/-- Marking finished: root `0` and its successor `1` are black; `2` is unreachable and white. -/
def sDone : St 3 := mk 3 [(0, 1), (2, 1)] [0] [.black, .black, .white]
/-- Root `1` is white but grey protected through the grey non-root `0`. -/
def sProtectedRoot : St 2 := mk 2 [(0, 1)] [1] [.grey, .white]

/-! ### `Live` -/

example : Live sGreyWhite 1 := Live.step (x := 0) (Live.root rfl) rfl
example : Live sDone 1 := Live.step (x := 0) (Live.root rfl) rfl
/-- Negative: an object that points into the live graph is not thereby live. -/
example : ¬ Live sDone 2 := by
  intro h
  have := Live.subset (s := sDone) (fun x => x.val ≠ 2) (by decide) (by decide) h
  exact this rfl

/-! ### `NoGrey` -/

example : NoGrey sBlackWhite := by decide
example : ¬ NoGrey sGreyWhite := by decide

/-! ### `Strong` -/

example : Strong sGreyWhite := by decide
example : Strong sDone := by decide
example : ¬ Strong sBlackWhite := by decide
example : ¬ Strong sWeakNotStrong := by decide

/-! ### `GreyProtected` -/

example : GreyProtected sGreyWhite 1 := GreyProtected.direct (g := 0) rfl rfl rfl
example : GreyProtected sWeakNotStrong 2 := GreyProtected.direct (g := 1) rfl rfl rfl
/-- Chains through white objects: `0` grey, `1` and `2` white. -/
example : GreyProtected (mk 3 [(0, 1), (1, 2)] [] [.grey, .white, .white]) 2 :=
  GreyProtected.chain (w := 1) (GreyProtected.direct (g := 0) rfl rfl rfl) rfl rfl
/-- Negative: a white object reached only from a black one is not protected. -/
example : ¬ GreyProtected sBlackWhite 1 :=
  not_greyProtected_of_noGrey (by decide)
/-- Negative: the path must pass through white objects only; a black object breaks it. -/
example : ¬ GreyProtected (mk 3 [(0, 1), (1, 2)] [] [.grey, .black, .white]) 2 := by
  intro h
  have := GreyProtected.subset (s := mk 3 [(0, 1), (1, 2)] [] [.grey, .black, .white])
    (fun _ => False) (by decide) (by decide) h
  exact this

/-! ### `Weak` -/

theorem weak_sWeakNotStrong : Weak sWeakNotStrong := by
  intro x y hxy hx hy
  have : y = 2 := by revert x y; decide
  subst this
  exact GreyProtected.direct (g := 1) rfl rfl rfl

example : Weak sGreyWhite := by
  intro x y hxy hx _
  have : ∀ x y : Fin 2, sGreyWhite.edge x y = true → sGreyWhite.color x = .black → False := by
    decide
  exact (this x y hxy hx).elim
example : ¬ Weak sBlackWhite := by
  intro h
  exact not_greyProtected_of_noGrey (s := sBlackWhite) (by decide) (h 0 1 rfl rfl rfl)

/-! ### `RootsNonWhite` and `RootsProtected` -/

example : RootsNonWhite sGreyWhite := by decide
example : ¬ RootsNonWhite sWhiteRoot := by decide
example : ¬ RootsNonWhite sProtectedRoot := by decide

example : RootsProtected sGreyWhite := by
  intro r hr hw
  have : ∀ r : Fin 2, sGreyWhite.root r = true → sGreyWhite.color r = .white → False := by
    decide
  exact (this r hr hw).elim
/-- A white root can be protected: `RootsProtected` is strictly weaker than `RootsNonWhite`. -/
example : RootsProtected sProtectedRoot := by
  intro r hr _
  have : r = 1 := by revert r; decide
  subst this
  exact GreyProtected.direct (g := 0) rfl rfl rfl
example : ¬ RootsProtected sWhiteRoot := by
  intro h
  exact not_greyProtected_of_noGrey (s := sWhiteRoot) (by decide) (h 0 rfl rfl)

/-! ### `AllLiveBlack` -/

theorem allLiveBlack_sDone : AllLiveBlack sDone := by
  intro y hy
  exact Live.subset (s := sDone) (fun x => sDone.color x = .black) (by decide) (by decide) hy
example : ¬ AllLiveBlack sGreyWhite := by
  intro h
  have := h 1 (Live.step (x := 0) (Live.root rfl) rfl)
  exact absurd this (by decide)

/-! ### `Isolated` -/

example : Isolated sDone 2 = False := by
  apply propext; constructor
  · intro h; exact absurd (h 1).1 (by decide)
  · intro h; exact h.elim
example : Isolated (mk 2 [] [0] [.black, .black]) 1 := by decide
example : ¬ Isolated sGreyWhite 1 := by decide

/-! ### Operations -/

/-- `scan` blackens the scanned object and greys its white successors. -/
example : (scan sGreyWhite 0).color 0 = .black ∧ (scan sGreyWhite 0).color 1 = .grey := by
  decide
/-- `scan` does not touch white objects that are not successors. -/
example : (scan sDone 1).color 2 = .white := by decide

/-- The Dijkstra barrier shades the stored target; no barrier and Yuasa do not. -/
example : (store .dijkstra sBlackWhite 0 1).color 1 = .grey := by decide
example : (store .none sBlackWhite 0 1).color 1 = .white := by decide
example : (store .yuasa sBlackWhite 0 1).color 1 = .white := by decide

/-- The Yuasa barrier shades the erased target; no barrier and Dijkstra do not. -/
example : (erase .yuasa sGreyWhite 0 1).color 1 = .grey ∧
    (erase .yuasa sGreyWhite 0 1).edge 0 1 = false := by decide
example : (erase .dijkstra sGreyWhite 0 1).color 1 = .white := by decide
example : (erase .none sGreyWhite 0 1).color 1 = .white := by decide
/-- Erasing a pointer that does not exist shades nothing. -/
example : (erase .yuasa sDone 0 2).color 2 = .white := by decide

/-- Root loads are shaded only under `shadeLoads = true`. -/
example : (load true sGreyWhite 1).color 1 = .grey ∧ (load true sGreyWhite 1).root 1 = true := by
  decide
example : (load false sGreyWhite 1).color 1 = .white := by decide

example : (drop sGreyWhite 0).root 0 = false := by decide
example : (alloc sDone 2 .black).color 2 = .black ∧ (alloc sDone 2 .black).root 2 = true := by
  decide

/-- `initMark` greys roots and whitens everything else. -/
example : (initMark sDone).color 0 = .grey ∧ (initMark sDone).color 1 = .white := by decide
/-- `rescan` greys white roots only. -/
example : (rescan sWhiteRoot).color 0 = .grey := by decide
example : (rescan sDone).color 2 = .white := by decide

/-! ### `Op.Enabled` -/

/-- The configuration without any barrier, without load shading, allowing every allocation
color. -/
def cfgNone : Config := { barrier := .none, shadeLoads := false, allocOk := fun _ => true }

example : (Op.scan (0 : Fin 2)).Enabled cfgNone sGreyWhite := rfl
example : ¬ (Op.scan (1 : Fin 2)).Enabled cfgNone sGreyWhite := by
  show ¬ sGreyWhite.color 1 = .grey
  decide
/-- The mutator can store a pointer it holds in its roots. -/
example : (Op.store (1 : Fin 2) 0).Enabled cfgNone sGreyWhite := rfl
/-- The mutator cannot store a pointer it does not hold, even a pointer to a live object: it
must load it first. -/
example : Live sGreyWhite 1 ∧ ¬ (Op.store (0 : Fin 2) 1).Enabled cfgNone sGreyWhite := by
  refine ⟨Live.step (x := 0) (Live.root rfl) rfl, ?_⟩
  show ¬ sGreyWhite.root 1 = true
  decide
/-- The mutator can load any object it reaches. -/
example : (Op.load (1 : Fin 2)).Enabled cfgNone sGreyWhite :=
  Live.step (x := 0) (Live.root rfl) rfl
/-- The mutator cannot load an unreachable object. -/
example : ¬ (Op.load (2 : Fin 3)).Enabled cfgNone sDone := by
  intro h
  have := Live.subset (s := sDone) (fun x => x.val ≠ 2) (by decide) (by decide) h
  exact this rfl
example : (Op.alloc (1 : Fin 2) .grey).Enabled cfgNone (mk 2 [] [0] [.black, .black]) :=
  ⟨rfl, rfl, by decide⟩
/-- Allocation is enabled only for an isolated object (`Op.Enabled`). -/
example : ¬ (Op.alloc (1 : Fin 2) .grey).Enabled cfgNone sGreyWhite := by
  intro h
  exact absurd h.2.2 (by decide)

end Toy.Tricolor
