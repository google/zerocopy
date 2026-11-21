import ToyChecker.Certificates

/-!
# Relabeling invariance

A *relabeling* of programs is a map `π : P → P` (in the intended use a
bijection that renames labels, e.g. variable names or node identifiers). A
predicate `Q` invariant under `π` takes the same value on `s` and `π s`; that
is the definition of `InvariantUnder` (recorded as the helper
`invariantUnder_cannot_separate`).

Applied to checkers:
* R5b: if `good` is invariant under a surjective map `π` (in particular the
  forward map of any `Relabeling`), soundness cannot distinguish a checker
  `c` from `c ∘ π`. A law that requires acceptance of a fixed anchor can
  (positive control).
* R5c: a law `L` on checkers that is itself invariant under `c ↦ c ∘ π`
  can still force an answer on a specific program `p` (for example, the
  anchored law with anchors `[0, 2]` is invariant under swapping `0` and `2`
  and forces acceptance of `0`). What it cannot do is force an answer at `p`
  without forcing the same answer at `π p`; for a bijective relabeling the
  forced answers are constant on orbits.

The anchor positive controls work because the framework supplies the
program `0 : P` itself, fixed outside any relabeling. If the tool could
choose the encoding of programs, a relabeling would move the anchors too.

The mathematical principle that notions invariant under all permutations of
a domain cannot distinguish an element from its image goes back to
Lindenbaum and Tarski (1935) and Tarski (1986); the informal idea that such
invariance prevents constraints from fixing reference is the model-theoretic
permutation argument of Putnam (1981). Nothing here formalizes either.
-/

namespace Toy.Checker

universe u

/-- `InvariantUnder π Q`: the predicate `Q` takes the same value on every
structure and its image under `π`. -/
def InvariantUnder {S : Type u} (π : S → S) (Q : S → Prop) : Prop :=
  ∀ s, Q (π s) ↔ Q s

/-- A relabeling of labels `α`: a bijection given with its inverse. -/
structure Relabeling (α : Type u) where
  /-- The forward renaming. -/
  toFun : α → α
  /-- The inverse renaming. -/
  invFun : α → α
  /-- `invFun` undoes `toFun`. -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- `toFun` undoes `invFun`. -/
  right_inv : ∀ a, toFun (invFun a) = a

/-- Relabel a toy structure (a list of labels) by renaming each label. -/
def relabelList {α : Type u} (σ : Relabeling α) : List α → List α :=
  List.map σ.toFun

/-- Swap the labels `0` and `2`, fix every other natural number. -/
def swap02Fun : Nat → Nat := fun n => if n = 0 then 2 else if n = 2 then 0 else n

theorem swap02Fun_swap02Fun (n : Nat) : swap02Fun (swap02Fun n) = n := by
  by_cases h0 : n = 0
  · subst h0; rfl
  by_cases h2 : n = 2
  · subst h2; rfl
  simp [swap02Fun, h0, h2]

/-- Swap the labels `0` and `1`, fix every other natural number. -/
def swap01Fun : Nat → Nat := fun n => if n = 0 then 1 else if n = 1 then 0 else n

theorem swap01Fun_swap01Fun (n : Nat) : swap01Fun (swap01Fun n) = n := by
  by_cases h0 : n = 0
  · subst h0; rfl
  by_cases h1 : n = 1
  · subst h1; rfl
  simp [swap01Fun, h0, h1]

/-- Positive example of `Relabeling`: the transposition of `0` and `2`. -/
def swap02 : Relabeling Nat :=
  ⟨swap02Fun, swap02Fun, swap02Fun_swap02Fun, swap02Fun_swap02Fun⟩

/-- Negative example of `Relabeling`: a non-injective map (constant `0`)
is not the forward map of any relabeling. -/
theorem not_relabeling_example_const : ¬ ∃ σ : Relabeling Nat, σ.toFun = fun _ => 0 := by
  rintro ⟨σ, hσ⟩
  have h0 := σ.left_inv 0
  have h1 := σ.left_inv 1
  rw [hσ] at h0 h1
  simp only at h0 h1
  rw [h0] at h1
  exact Nat.noConfusion h1

/-- Positive example of `InvariantUnder`: "has length `2`" is invariant
under every relabeling of toy structures. -/
theorem invariantUnder_example_length {α : Type u} (σ : Relabeling α) :
    InvariantUnder (relabelList σ) (fun s => s.length = 2) := by
  intro s
  simp [relabelList]

/-- Positive example of `InvariantUnder`: `evenGood` is invariant under the
transposition of `0` and `2`. -/
theorem invariantUnder_example_evenGood_swap02 : InvariantUnder swap02Fun evenGood := by
  intro n
  by_cases h0 : n = 0
  · subst h0; decide
  by_cases h2 : n = 2
  · subst h2; decide
  simp [swap02Fun, h0, h2]

/-- Negative example of `InvariantUnder`: "mentions the label `0`" is not
invariant under the transposition of `0` and `2` (it separates `[2]` from
its image `[0]`). -/
theorem not_invariantUnder_example_mentionsZero :
    ¬ InvariantUnder (relabelList swap02) (fun s => 0 ∈ s) := by
  intro h
  have := (h [2]).mp (by decide)
  simp at this

/-- Negative example of `InvariantUnder`: `evenGood` is not invariant under
the transposition of `0` and `1`. -/
theorem not_invariantUnder_example_evenGood_swap01 : ¬ InvariantUnder swap01Fun evenGood := by
  intro h
  have := (h 0).mpr rfl
  simp [swap01Fun, evenGood] at this

/-- The forward map of a relabeling is surjective (so R5b applies to it). -/
theorem Relabeling.surjective {α : Type u} (σ : Relabeling α) : Function.Surjective σ.toFun :=
  fun a => ⟨σ.invFun a, σ.right_inv a⟩

/-- Using bijectivity: invariance under a relabeling implies invariance under
its inverse (so the predicate is constant on orbits). -/
theorem invariantUnder_invFun_of_invariantUnder {α : Type u} {Q : α → Prop}
    (σ : Relabeling α) (hQ : InvariantUnder σ.toFun Q) : InvariantUnder σ.invFun Q := by
  intro a
  have := hQ (σ.invFun a)
  rw [σ.right_inv] at this
  exact this.symm

/-! ## Main statements -/

/-- Helper (the definition of `InvariantUnder` read at `s`): a predicate
invariant under a map `π` takes the same value on `s` and `π s`. No
bijectivity is assumed. -/
theorem invariantUnder_cannot_separate {S : Type u} {π : S → S} {Q : S → Prop}
    (hQ : InvariantUnder π Q) (s : S) : Q (π s) ↔ Q s :=
  hQ s

/-- The direction of R5b that needs no surjectivity: if `good` is invariant
under an arbitrary map `π` and `c` is sound, then `c ∘ π` is sound. -/
theorem sound_comp_of_invariantUnder {P : Type u} {good : P → Prop} {π : P → P}
    (hgood : InvariantUnder π good) {c : P → Bool} (hc : Sound good c) : Sound good (c ∘ π) :=
  fun p hp => (hgood p).mp (hc (π p) hp)

/-- R5b. If `good` is invariant under a surjective map `π` of programs (in
particular the forward map of any `Relabeling`), soundness cannot
distinguish a checker `c` from the relabeled checker `c ∘ π`. Surjectivity is
used only for the direction from `c ∘ π` to `c`. -/
theorem sound_comp_iff_of_surjective_of_invariantUnder {P : Type u} {good : P → Prop}
    {π : P → P} (hsurj : Function.Surjective π) (hgood : InvariantUnder π good)
    (c : P → Bool) : Sound good (c ∘ π) ↔ Sound good c := by
  constructor
  · intro h q hq
    obtain ⟨p, rfl⟩ := hsurj q
    exact (hgood p).mpr (h p hq)
  · intro h p hp
    exact (hgood p).mp (h (π p) hp)

/-! ## Tightness counterexamples and positive controls -/

/-- R5b without `hsurj`: the constant map `0` leaves the predicate `False`
invariant, yet soundness for `False` holds for `(· == 1) ∘ const 0` and
fails for `(· == 1)`. -/
theorem cex_sound_comp_iff_needs_surjective :
    InvariantUnder (fun _ : Nat => 0) (fun _ => False) ∧
    ¬ (Sound (fun _ : Nat => False) ((fun n => n == 1) ∘ (fun _ : Nat => 0)) ↔
        Sound (fun _ : Nat => False) (fun n => n == 1)) := by
  refine ⟨fun _ => Iff.rfl, fun h => ?_⟩
  have hl : Sound (fun _ : Nat => False) ((fun n => n == 1) ∘ (fun _ : Nat => 0)) := by
    intro p hp
    simp at hp
  exact absurd (h.mp hl 1 rfl) id

/-- R5b without `hgood`: the transposition of `0` and `1` is surjective,
`evenGood` is not invariant under it, and soundness separates `(· == 0)`
from `(· == 0) ∘ swap01Fun`. -/
theorem cex_sound_comp_iff_needs_invariant :
    Function.Surjective swap01Fun ∧
    ¬ (Sound evenGood ((fun n => n == 0) ∘ swap01Fun) ↔ Sound evenGood (fun n => n == 0)) := by
  refine ⟨fun n => ⟨swap01Fun n, swap01Fun_swap01Fun n⟩, fun h => ?_⟩
  have hr : Sound evenGood (fun n => n == 0) := by
    intro p hp
    simp at hp
    subst hp
    rfl
  have hl := h.mpr hr 1 (by decide)
  simp [evenGood] at hl

/-- Positive control for R5b: `evenGood` is invariant under the
surjective transposition of `0` and `2`, both `(· == 0)` and its relabeled
twin `(· == 2)` are sound, but the anchored law with anchor `0` admits the
first and excludes the second. -/
theorem positive_control_anchor_law_separates_relabeled_checker :
    Function.Surjective swap02Fun ∧ InvariantUnder swap02Fun evenGood ∧
    Sound evenGood ((fun n => n == 0) ∘ swap02Fun) ∧
    AnchoredSound evenGood [0] (fun n => n == 0) ∧
    ¬ AnchoredSound evenGood [0] ((fun n => n == 0) ∘ swap02Fun) := by
  have hs0 : Sound evenGood (fun n => n == 0) := by
    intro p hp
    simp at hp
    subst hp
    rfl
  have hsurj : Function.Surjective swap02Fun :=
    fun n => ⟨swap02Fun n, swap02Fun_swap02Fun n⟩
  refine ⟨hsurj, invariantUnder_example_evenGood_swap02,
    (sound_comp_iff_of_surjective_of_invariantUnder hsurj
      invariantUnder_example_evenGood_swap02 _).mpr hs0,
    ⟨hs0, by decide⟩, fun h => ?_⟩
  have := h.2 0 (by simp)
  simp [swap02Fun] at this

/-! ## Non-vacuity witnesses -/

/-- R5b hypotheses hold: the transposition of `0` and `2` is surjective and
leaves `evenGood` invariant. -/
theorem nonvacuous_sound_comp_iff :
    Function.Surjective swap02Fun ∧ InvariantUnder swap02Fun evenGood :=
  ⟨fun n => ⟨swap02Fun n, swap02Fun_swap02Fun n⟩, invariantUnder_example_evenGood_swap02⟩

/-! ## Laws invariant under relabeling (R5c) -/

/-- R5c (part, arbitrary map). If a law `L` on checkers is invariant under
precomposition with `π` (`L (c ∘ π) ↔ L c` for every checker `c`) and every
checker admitted by `L` answers `b` on `p`, then every admitted checker also
answers `b` on `π p`. No bijectivity is assumed. -/
theorem forced_value_at_image_of_invariantUnder_comp {P : Type u} {π : P → P} {L : Law P}
    (hL : InvariantUnder (fun c : P → Bool => c ∘ π) L) {p : P} {b : Bool}
    (hp : ∀ c, L c → c p = b) : ∀ c, L c → c (π p) = b :=
  fun c hc => hp (c ∘ π) ((hL c).mpr hc)

/-- R5c. For a bijective relabeling `σ` of programs and a law `L` invariant
under precomposition with `σ`, `L` forces the answer `b` on `σ p` iff it
forces `b` on `p`. So an invariant law can force answers on specific
programs only uniformly along `σ`-orbits; it cannot single out `p` from
`σ p`. -/
theorem forced_value_relabeled_iff_of_invariantUnder_comp {P : Type u} (σ : Relabeling P)
    {L : Law P} (hL : InvariantUnder (fun c : P → Bool => c ∘ σ.toFun) L) (p : P) (b : Bool) :
    (∀ c, L c → c (σ.toFun p) = b) ↔ (∀ c, L c → c p = b) := by
  constructor
  · intro h c hc
    have heq : (c ∘ σ.invFun) ∘ σ.toFun = c := by
      funext q
      simp [Function.comp, σ.left_inv q]
    have hc' : L (c ∘ σ.invFun) := (hL (c ∘ σ.invFun)).mp (by show L ((c ∘ σ.invFun) ∘ σ.toFun); rw [heq]; exact hc)
    have := h (c ∘ σ.invFun) hc'
    simpa [Function.comp, σ.left_inv p] using this
  · exact forced_value_at_image_of_invariantUnder_comp hL

/-- R5c without invariance of the law: the anchored law with the single
anchor `0` forces acceptance of `0` but not of its relabeled image
`swap02 0 = 2` (the allowlist `[0]` is admitted and rejects `2`). The
conclusion fails. -/
theorem cex_forced_value_relabeled_needs_invariant :
    ¬ ((∀ c, AnchoredSound evenGood [0] c → c (swap02.toFun 0) = true) ↔
        (∀ c, AnchoredSound evenGood [0] c → c 0 = true)) := by
  intro h
  have hforced : ∀ c, AnchoredSound evenGood [0] c → c 0 = true :=
    fun c hc => hc.2 0 (by simp)
  have h2 := h.mpr hforced (allowlist [0]) (allowlist_anchoredSound_of_anchors_good (by decide))
  revert h2
  decide

/-- R5c with the bijection `σ` replaced by a non-injective map: the law
"accepts `0`" is invariant under precomposition with the constant map `0`
and forces acceptance at the image `0` of `1`, but not at `1`. The conclusion
fails. -/
theorem cex_forced_value_relabeled_needs_bijective :
    InvariantUnder (fun c : Nat → Bool => c ∘ fun _ => 0) acceptsZeroLaw ∧
    ¬ ((∀ c, acceptsZeroLaw c → c ((fun _ : Nat => 0) 1) = true) ↔
        (∀ c, acceptsZeroLaw c → c 1 = true)) := by
  refine ⟨fun _ => Iff.rfl, fun h => ?_⟩
  have h1 := h.mp (fun c hc => hc) (fun n => n == 0) rfl
  revert h1
  decide

/-- `forced_value_at_image_of_invariantUnder_comp` without `hL`: `hp` holds
for the single-anchor law at `0` and the conclusion fails at the image
`swap02Fun 0 = 2`. -/
theorem cex_forced_value_at_image_needs_invariant :
    (∀ c, AnchoredSound evenGood [0] c → c 0 = true) ∧
    ¬ (∀ c, AnchoredSound evenGood [0] c → c (swap02Fun 0) = true) := by
  refine ⟨fun c hc => hc.2 0 (by simp), fun h => ?_⟩
  have h2 := h (allowlist [0]) (allowlist_anchoredSound_of_anchors_good (by decide))
  revert h2
  decide

/-- `forced_value_at_image_of_invariantUnder_comp` without `hp`: the trivial
law (invariant under every precomposition) forces nothing, so the conclusion
fails. -/
theorem cex_forced_value_at_image_needs_forced :
    InvariantUnder (fun c : Nat → Bool => c ∘ id) (fun _ => True) ∧
    ¬ (∀ c : Nat → Bool, (fun _ => True) c → c (id 0) = true) := by
  refine ⟨fun _ => Iff.rfl, fun h => ?_⟩
  have := h rejectAll trivial
  simp [rejectAll] at this

/-- The anchored law with anchors `[0, 2]` is invariant under precomposition
with the transposition of `0` and `2`. -/
theorem invariantUnder_comp_anchoredSound_swap02 :
    InvariantUnder (fun c : Nat → Bool => c ∘ swap02.toFun) (AnchoredSound evenGood [0, 2]) := by
  have hsurj : Function.Surjective swap02.toFun := Relabeling.surjective swap02
  intro c
  constructor
  · rintro ⟨hs, ha⟩
    refine ⟨?_, fun a ha' => ?_⟩
    · intro q hq
      obtain ⟨p, rfl⟩ := hsurj q
      exact (invariantUnder_example_evenGood_swap02 p).mpr (hs p hq)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · have := ha 2 (by simp); simpa [swap02, swap02Fun] using this
      · have := ha 0 (by simp); simpa [swap02, swap02Fun] using this
  · rintro ⟨hs, ha⟩
    refine ⟨sound_comp_of_invariantUnder invariantUnder_example_evenGood_swap02 hs, fun a ha' => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with rfl | rfl
    · have := ha 2 (by simp); simpa [swap02, swap02Fun] using this
    · have := ha 0 (by simp); simpa [swap02, swap02Fun] using this

/-- R5c hypotheses hold, and an invariant law does force an answer outright:
the anchored law with anchors `[0, 2]` is invariant under precomposition with
`swap02` and every checker it admits accepts `0`. -/
theorem nonvacuous_forced_value_relabeled :
    InvariantUnder (fun c : Nat → Bool => c ∘ swap02.toFun) (AnchoredSound evenGood [0, 2]) ∧
    (∀ c, AnchoredSound evenGood [0, 2] c → c 0 = true) :=
  ⟨invariantUnder_comp_anchoredSound_swap02, fun c hc => hc.2 0 (by simp)⟩

/-! ## Which half of bijectivity R5c uses

The proof of `forced_value_relabeled_iff_of_invariantUnder_comp` uses only
`σ.left_inv`, never `σ.right_inv`. The three statements below make that
precise: a left inverse suffices (constructively), injectivity suffices
(classically), and surjectivity without injectivity does not suffice. They
are supplementary facts about the hypothesis `σ : Relabeling P`; they do not
change R5c. -/

/-- Generalization of R5c: a map `π` with a left inverse `g`
(`g (π a) = a` for all `a`) suffices for the equivalence; no surjectivity is
needed. -/
theorem forced_value_relabeled_iff_of_leftInverse {P : Type u} {π g : P → P}
    (hleft : ∀ a, g (π a) = a) {L : Law P}
    (hL : InvariantUnder (fun c : P → Bool => c ∘ π) L) (p : P) (b : Bool) :
    (∀ c, L c → c (π p) = b) ↔ (∀ c, L c → c p = b) := by
  constructor
  · intro h c hc
    have heq : (c ∘ g) ∘ π = c := funext fun q => by simp [Function.comp, hleft q]
    have hc' : L (c ∘ g) := (hL (c ∘ g)).mp (by show L ((c ∘ g) ∘ π); rw [heq]; exact hc)
    simpa [Function.comp, hleft p] using h (c ∘ g) hc'
  · exact forced_value_at_image_of_invariantUnder_comp hL

/-- Generalization of R5c (classical): an injective map `π` suffices for the
equivalence. The left inverse is built with `Classical.choose`. -/
theorem forced_value_relabeled_iff_of_injective {P : Type u} {π : P → P}
    (hinj : Function.Injective π) {L : Law P}
    (hL : InvariantUnder (fun c : P → Bool => c ∘ π) L) (p : P) (b : Bool) :
    (∀ c, L c → c (π p) = b) ↔ (∀ c, L c → c p = b) := by
  constructor
  · intro h c hc
    let c' : P → Bool := fun q =>
      @dite _ (∃ x, π x = q) (Classical.propDecidable _)
        (fun hex => c (Classical.choose hex)) (fun _ => false)
    have heq : c' ∘ π = c := by
      funext x
      have hex : ∃ y, π y = π x := ⟨x, rfl⟩
      have hxeq : Classical.choose hex = x := hinj (Classical.choose_spec hex)
      change c' (π x) = c x
      simp [c', hex, hxeq]
    have hc' : L c' := (hL c').mp (by show L (c' ∘ π); rw [heq]; exact hc)
    exact (congrFun heq p).symm.trans (h c' hc')
  · exact forced_value_at_image_of_invariantUnder_comp hL

/-- Surjectivity without injectivity does not suffice: on `Nat`, with truncated
subtraction, `n ↦ n - 2` is surjective (and not injective), the law "accepts `0`"
is invariant under precomposition with it, and the law forces acceptance at the
image `2 - 2 = 0` of `2` but not at `2`. -/
theorem cex_forced_value_relabeled_surjective_not_injective :
    (∀ y : Nat, ∃ x, x - 2 = y) ∧
    InvariantUnder (fun c : Nat → Bool => c ∘ fun n => n - 2) acceptsZeroLaw ∧
    ¬ ((∀ c, acceptsZeroLaw c → c ((fun n : Nat => n - 2) 2) = true) ↔
        (∀ c, acceptsZeroLaw c → c 2 = true)) := by
  refine ⟨fun y => ⟨y + 2, Nat.add_sub_cancel y 2⟩, fun _ => Iff.rfl, fun h => ?_⟩
  have h2 := h.mp (fun _ hc => hc) (fun n => n == 0) rfl
  revert h2
  decide

end Toy.Checker
