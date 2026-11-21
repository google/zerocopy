import Toy.Tricolor.Examples

/-!
# What the tricolor invariants guarantee

End-of-marking safety from the strong and from the weak invariant, the key grey-protection
lemma for the weak invariant during marking, and the relation between the two invariants.
-/

namespace Toy.Tricolor

variable {n : Nat}

theorem black_of_nonWhite_of_noGrey {s : St n} (hng : NoGrey s) {x : Fin n}
    (hx : s.color x ≠ .white) : s.color x = .black := by
  cases h : s.color x with
  | white => exact absurd h hx
  | grey => exact absurd h (hng x)
  | black => rfl

/-- **End-of-marking safety (strong invariant).** If no object is grey, the strong invariant
holds and every root is non-white, then every live object is black. -/
theorem allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite {s : St n}
    (hng : NoGrey s) (hs : Strong s) (hr : RootsNonWhite s) : AllLiveBlack s := by
  intro y hy
  induction hy with
  | root h => exact black_of_nonWhite_of_noGrey hng (hr _ h)
  | step _ he ih => exact black_of_nonWhite_of_noGrey hng (hs _ _ he ih)

/-- **Strong implies weak.** -/
theorem weak_of_strong {s : St n} (hs : Strong s) : Weak s :=
  fun x y he hx hy => absurd hy (hs x y he hx)

/-- With no grey object, the weak invariant collapses to the strong one. -/
theorem strong_of_weak_of_noGrey {s : St n} (hng : NoGrey s) (hw : Weak s) : Strong s :=
  fun x y he hx hy => not_greyProtected_of_noGrey hng (hw x y he hx hy)

/-- **End-of-marking safety (weak invariant).** If no object is grey, the weak invariant
holds and every root is non-white, then every live object is black. -/
theorem allLiveBlack_of_noGrey_of_weak_of_rootsNonWhite {s : St n}
    (hng : NoGrey s) (hw : Weak s) (hr : RootsNonWhite s) : AllLiveBlack s :=
  allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite hng (strong_of_weak_of_noGrey hng hw) hr

theorem rootsProtected_of_rootsNonWhite {s : St n} (hr : RootsNonWhite s) : RootsProtected s :=
  fun r h hw => absurd hw (hr r h)

theorem rootsNonWhite_of_rootsProtected_of_noGrey {s : St n} (hng : NoGrey s)
    (hr : RootsProtected s) : RootsNonWhite s :=
  fun r h hw => not_greyProtected_of_noGrey hng (hr r h hw)

/-- **Grey protection of live white objects.** Under the weak invariant together with its root
clause (every white root is grey protected), every live white object is grey protected. -/
theorem greyProtected_of_live_of_white_of_weak_of_rootsProtected {s : St n}
    (hw : Weak s) (hr : RootsProtected s) {y : Fin n} (hy : Live s y)
    (hwh : s.color y = .white) : GreyProtected s y := by
  revert hwh
  induction hy with
  | root h => exact fun hwh => hr _ h hwh
  | @step x y _ he ih =>
    intro hwh
    cases hc : s.color x with
    | white => exact GreyProtected.chain (ih hc) he hwh
    | grey => exact GreyProtected.direct hc he hwh
    | black => exact hw _ _ he hc hwh

/-- **End-of-marking safety (weak invariant, protected roots).** If no object is grey, the
weak invariant holds and every white root is grey protected, then every live object is
black. -/
theorem allLiveBlack_of_noGrey_of_weak_of_rootsProtected {s : St n}
    (hng : NoGrey s) (hw : Weak s) (hr : RootsProtected s) : AllLiveBlack s := by
  intro y hy
  cases hc : s.color y with
  | white =>
    exact absurd (greyProtected_of_live_of_white_of_weak_of_rootsProtected hw hr hy hc)
      (not_greyProtected_of_noGrey hng)
  | grey => exact absurd hc (hng y)
  | black => rfl

/-! ## Counterexamples (tightness) and non-vacuity -/

theorem live_one_sGreyWhite : Live sGreyWhite 1 := Live.step (x := 0) (Live.root rfl) rfl
theorem live_one_sBlackWhite : Live sBlackWhite 1 := Live.step (x := 0) (Live.root rfl) rfl
theorem live_zero_sWhiteRoot : Live sWhiteRoot 0 := Live.root rfl

theorem not_allLiveBlack_sGreyWhite : ¬ AllLiveBlack sGreyWhite :=
  fun h => absurd (h 1 live_one_sGreyWhite) (by decide)
theorem not_allLiveBlack_sBlackWhite : ¬ AllLiveBlack sBlackWhite :=
  fun h => absurd (h 1 live_one_sBlackWhite) (by decide)
theorem not_allLiveBlack_sWhiteRoot : ¬ AllLiveBlack sWhiteRoot :=
  fun h => absurd (h 0 live_zero_sWhiteRoot) (by decide)

theorem weak_sGreyWhite : Weak sGreyWhite := weak_of_strong (by decide)
theorem weak_sWhiteRoot : Weak sWhiteRoot := weak_of_strong (by decide)
theorem rootsProtected_sGreyWhite : RootsProtected sGreyWhite :=
  rootsProtected_of_rootsNonWhite (by decide)
theorem rootsProtected_sBlackWhite : RootsProtected sBlackWhite :=
  rootsProtected_of_rootsNonWhite (by decide)

/-- `NoGrey` cannot be dropped (a 2-object state): a grey root pointing to a white object satisfies the strong invariant
and has non-white roots, yet a live object is white. -/
theorem strong_rootsNonWhite_and_not_allLiveBlack :
    Strong sGreyWhite ∧ RootsNonWhite sGreyWhite ∧ ¬ AllLiveBlack sGreyWhite :=
  ⟨by decide, by decide, not_allLiveBlack_sGreyWhite⟩

/-- The invariant cannot be dropped (a 2-object state): a black root pointing to a white
object, nothing grey. -/
theorem noGrey_rootsNonWhite_and_not_allLiveBlack :
    NoGrey sBlackWhite ∧ RootsNonWhite sBlackWhite ∧ ¬ AllLiveBlack sBlackWhite :=
  ⟨by decide, by decide, not_allLiveBlack_sBlackWhite⟩

/-- Non-white roots cannot be dropped (a 1-object state): a lone white root. -/
theorem noGrey_strong_and_not_allLiveBlack :
    NoGrey sWhiteRoot ∧ Strong sWhiteRoot ∧ ¬ AllLiveBlack sWhiteRoot :=
  ⟨by decide, by decide, not_allLiveBlack_sWhiteRoot⟩

theorem weak_rootsNonWhite_and_not_allLiveBlack :
    Weak sGreyWhite ∧ RootsNonWhite sGreyWhite ∧ ¬ AllLiveBlack sGreyWhite :=
  ⟨weak_sGreyWhite, by decide, not_allLiveBlack_sGreyWhite⟩

theorem noGrey_weak_and_not_allLiveBlack :
    NoGrey sWhiteRoot ∧ Weak sWhiteRoot ∧ ¬ AllLiveBlack sWhiteRoot :=
  ⟨by decide, weak_sWhiteRoot, not_allLiveBlack_sWhiteRoot⟩

theorem weak_rootsProtected_and_not_allLiveBlack :
    Weak sGreyWhite ∧ RootsProtected sGreyWhite ∧ ¬ AllLiveBlack sGreyWhite :=
  ⟨weak_sGreyWhite, rootsProtected_sGreyWhite, not_allLiveBlack_sGreyWhite⟩

theorem noGrey_rootsProtected_and_not_allLiveBlack :
    NoGrey sBlackWhite ∧ RootsProtected sBlackWhite ∧ ¬ AllLiveBlack sBlackWhite :=
  ⟨by decide, rootsProtected_sBlackWhite, not_allLiveBlack_sBlackWhite⟩

/-- The weak invariant cannot be dropped from grey protection of live white objects (a
2-object state: a black root pointing to a white object, nothing grey). -/
theorem rootsProtected_live_white_and_not_greyProtected :
    RootsProtected sBlackWhite ∧ Live sBlackWhite 1 ∧ sBlackWhite.color 1 = .white ∧
      ¬ GreyProtected sBlackWhite 1 :=
  ⟨rootsProtected_sBlackWhite, live_one_sBlackWhite, rfl, not_greyProtected_of_noGrey (by decide)⟩

/-- The root clause cannot be dropped from grey protection of live white objects (a 1-object
state: a lone white root). -/
theorem weak_live_white_and_not_greyProtected :
    Weak sWhiteRoot ∧ Live sWhiteRoot 0 ∧ sWhiteRoot.color 0 = .white ∧
      ¬ GreyProtected sWhiteRoot 0 :=
  ⟨weak_sWhiteRoot, live_zero_sWhiteRoot, rfl, not_greyProtected_of_noGrey (by decide)⟩

/-- Liveness cannot be dropped (a 3-object state): an unreachable white object need not be
grey protected. -/
theorem weak_rootsProtected_white_and_not_greyProtected :
    Weak sDone ∧ RootsProtected sDone ∧ sDone.color 2 = .white ∧ ¬ GreyProtected sDone 2 :=
  ⟨weak_of_strong (by decide), rootsProtected_of_rootsNonWhite (by decide), rfl,
    not_greyProtected_of_noGrey (by decide)⟩

/-- Whiteness cannot be dropped (a 2-object state): a live grey root is not grey protected (protection is defined for
white objects only). -/
theorem weak_rootsProtected_live_and_not_greyProtected :
    Weak sGreyWhite ∧ RootsProtected sGreyWhite ∧ Live sGreyWhite 0 ∧
      ¬ GreyProtected sGreyWhite 0 :=
  ⟨weak_sGreyWhite, rootsProtected_sGreyWhite, Live.root rfl,
    fun h => absurd h.white (by decide)⟩

/-- **The converse of `weak_of_strong` fails.** -/
theorem weak_and_not_strong : Weak sWeakNotStrong ∧ ¬ Strong sWeakNotStrong :=
  ⟨weak_sWeakNotStrong, by decide⟩

theorem allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite_nonvacuous :
    NoGrey sDone ∧ Strong sDone ∧ RootsNonWhite sDone :=
  ⟨by decide, by decide, by decide⟩

theorem allLiveBlack_of_noGrey_of_weak_of_rootsNonWhite_nonvacuous :
    NoGrey sDone ∧ Weak sDone ∧ RootsNonWhite sDone :=
  ⟨by decide, weak_of_strong (by decide), by decide⟩

theorem allLiveBlack_of_noGrey_of_weak_of_rootsProtected_nonvacuous :
    NoGrey sDone ∧ Weak sDone ∧ RootsProtected sDone :=
  ⟨by decide, weak_of_strong (by decide), rootsProtected_of_rootsNonWhite (by decide)⟩

/-- Non-vacuity of the grey-protection lemma, with a live white object reached through a black
root (so the weak invariant is used, not just a grey parent). -/
theorem greyProtected_of_live_of_white_of_weak_of_rootsProtected_nonvacuous :
    Weak sWeakNotStrong ∧ RootsProtected sWeakNotStrong ∧ Live sWeakNotStrong 2 ∧
      sWeakNotStrong.color 2 = .white :=
  ⟨weak_sWeakNotStrong, rootsProtected_of_rootsNonWhite (by decide),
    Live.step (x := 0) (Live.root rfl) rfl, rfl⟩

/-- Non-vacuity of `weak_of_strong` with a black object that has an outgoing edge (so the
implication inside `Weak` is exercised, not vacuous for lack of black objects). -/
theorem weak_of_strong_nonvacuous :
    Strong sDone ∧ sDone.edge 0 1 = true ∧ sDone.color 0 = .black :=
  ⟨by decide, rfl, rfl⟩

end Toy.Tricolor
