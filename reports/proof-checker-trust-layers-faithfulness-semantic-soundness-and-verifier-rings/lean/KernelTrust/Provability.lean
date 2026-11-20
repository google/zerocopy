/-
  Toy.KernelTrust.Provability

  K4a / K5: an abstract interface for *families of theories that talk about each
  other's provability*, with every closure and derivability condition a named
  definition.

  The interface is abstract.  Its results apply to a concrete formal system
  only insofar as that system, with a concrete choice of provability
  predicates and a sentence language shared by all theories of the family, is
  shown to satisfy the named conditions.  Nothing in this file constructs an
  arithmetised provability predicate.
-/
import KernelTrust.Rings

namespace Toy.KernelTrust

/-- A family of theories, indexed by `ι`, over one shared sentence language.

* `Sent` is the type of sentences, with falsum `bot` and implication `imp`.
* `box j A` is the sentence "theory `j` proves `A`" (the provability predicate
  of theory `j`, applied to a name of `A`).
* `Thm i A` is the meta-level fact "theory `i` proves `A`".

`Thm` (theoremhood) and truth are deliberately *not* identified: no field says
that true sentences are provable.  All closure conditions are separate named
predicates below, so that each theorem lists exactly what it assumes. -/
structure ProvFamily (ι : Type) where
  Sent : Type
  bot  : Sent
  imp  : Sent → Sent → Sent
  box  : ι → Sent → Sent
  Thm  : ι → Sent → Prop

namespace ProvFamily

variable {ι : Type} (F : ProvFamily ι)

/-- The consistency statement of theory `j`: `□ⱼ⊥ → ⊥`. -/
def con (j : ι) : F.Sent := F.imp (F.box j F.bot) F.bot

/-- Theory `i` is consistent: it does not prove `⊥`. -/
def Consistent (i : ι) : Prop := ¬ F.Thm i F.bot

/-- **Closure under modus ponens** of theory `i`. -/
def MpClosed (i : ι) : Prop :=
  ∀ {A B : F.Sent}, F.Thm i (F.imp A B) → F.Thm i A → F.Thm i B

/-- **Ex falso** for theory `i`: `i ⊢ ⊥ → A` for every sentence `A`. -/
def HasEfq (i : ι) : Prop := ∀ A : F.Sent, F.Thm i (F.imp F.bot A)

/-- **Implicational closure** of theory `i`: modus ponens and the two Hilbert
axiom schemes `K` and `S` for implication.  Ex falso is *not* included
(`HasEfq` is separate). -/
structure ImpClosed (i : ι) : Prop where
  mp  : F.MpClosed i
  axK : ∀ A B : F.Sent, F.Thm i (F.imp A (F.imp B A))
  axS : ∀ A B C : F.Sent,
    F.Thm i (F.imp (F.imp A (F.imp B C)) (F.imp (F.imp A B) (F.imp A C)))

/-- **(D1)** necessitation for theory `i` about itself:
if `i ⊢ A` then `i ⊢ □ᵢA`. -/
def D1 (i : ι) : Prop := ∀ A : F.Sent, F.Thm i A → F.Thm i (F.box i A)

/-- **(D2)** distribution: `i ⊢ □ᵢ(A → B) → □ᵢA → □ᵢB`. -/
def D2 (i : ι) : Prop :=
  ∀ A B : F.Sent, F.Thm i (F.imp (F.box i (F.imp A B)) (F.imp (F.box i A) (F.box i B)))

/-- **(D3)** formalised necessitation: `i ⊢ □ᵢA → □ᵢ□ᵢA`. -/
def D3 (i : ι) : Prop :=
  ∀ A : F.Sent, F.Thm i (F.imp (F.box i A) (F.box i (F.box i A)))

/-- The Hilbert–Bernays–Löb derivability conditions for theory `i` and its own
provability predicate. -/
structure HBL (i : ι) : Prop where
  d1 : F.D1 i
  d2 : F.D2 i
  d3 : F.D3 i

/-- **Löb's rule** for theory `i`: if `i ⊢ □ᵢA → A` then `i ⊢ A`.

For concrete theories this is Löb's theorem, derived from `HBL` plus the
diagonal lemma.  The interface has no diagonal lemma, so Löb's rule is an
*assumption* here, not a consequence of `HBL`. -/
def LobRule (i : ι) : Prop :=
  ∀ A : F.Sent, F.Thm i (F.imp (F.box i A) A) → F.Thm i A

/-- **Gödel's second incompleteness property** of theory `i`, in Löb form: if
`i` proves its own consistency statement `□ᵢ⊥ → ⊥`, then `i` proves `⊥`.
It is the instance `A := ⊥` of `LobRule` (`LobRule.godelII`).  For concrete
theories it is Gödel's second incompleteness theorem; here it is a named
*hypothesis*, and it carries the substance of every impossibility result
below. -/
def GodelII (i : ι) : Prop := F.Thm i (F.con i) → F.Thm i F.bot

/-- **Bridge, part 1 (cross-necessitation).**  If `j ⊢ A` then `i ⊢ □ⱼA`.
Intended reading: theory `i` is Σ₁-complete and `□ⱼ` correctly numerates
`j`-provability, so `i` verifies every actual `j`-proof.  The diagonal case
`i = j` is `D1`. -/
def CrossNec (i j : ι) : Prop := ∀ A : F.Sent, F.Thm j A → F.Thm i (F.box j A)

/-- **Bridge, part 2 (cross-distribution).**  `i ⊢ □ⱼ(A → B) → □ⱼA → □ⱼB`.
Intended reading: theory `i` proves that theory `j` is closed under modus
ponens.  This is cross-theory normality, not a Σ₁-completeness principle.  The
diagonal case is `D2`. -/
def CrossDistrib (i j : ι) : Prop :=
  ∀ A B : F.Sent, F.Thm i (F.imp (F.box j (F.imp A B)) (F.imp (F.box j A) (F.box j B)))

/-- **Bridge, part 3 (formalised Σ₁-completeness for provability statements).**
`i ⊢ □ₖA → □ⱼ□ₖA`.  Intended reading: theory `i` proves that theory `j`
verifies every `k`-proof (`□ₖA` is a Σ₁ sentence, and `i` proves that `j` is
Σ₁-complete).  The diagonal case `i = j = k` is `D3`. -/
def CrossSigma1 (i j k : ι) : Prop :=
  ∀ A : F.Sent, F.Thm i (F.imp (F.box k A) (F.box j (F.box k A)))

/-- **The cross-theory Hilbert–Bernays–Löb conditions** (the "formalised
Σ₁-completeness bridge") between all theories of the family:
cross-necessitation, cross-distribution and formalised Σ₁-completeness, for all
index combinations.  Its diagonal is exactly `HBL` (`CrossHBL.hbl`). -/
structure CrossHBL : Prop where
  nec     : ∀ i j : ι, F.CrossNec i j
  distrib : ∀ i j : ι, F.CrossDistrib i j
  sigma1  : ∀ i j k : ι, F.CrossSigma1 i j k

/-- **The cross-theory conditions from theory `i` to every other theory.**
For every `j ≠ i`: `i` verifies `j`'s proofs (`CrossNec i j`), proves `j`
closed under modus ponens (`CrossDistrib i j`), and proves that `j` verifies
every theory's proofs (`CrossSigma1 i j k` for all `k`).  The diagonal
(`i`'s own `D1`–`D3`) is not included. -/
structure CrossHBLFrom (i : ι) : Prop where
  nec     : ∀ j : ι, j ≠ i → F.CrossNec i j
  distrib : ∀ j : ι, j ≠ i → F.CrossDistrib i j
  sigma1  : ∀ j k : ι, j ≠ i → F.CrossSigma1 i j k

variable {F}

/-- Löb's rule implies Gödel's second incompleteness property. -/
theorem LobRule.godelII {i : ι} (h : F.LobRule i) : F.GodelII i :=
  fun hCon => h F.bot hCon

/-- The diagonal of the cross-theory conditions is the Hilbert–Bernays–Löb
conditions of each theory. -/
theorem CrossHBL.hbl (h : F.CrossHBL) (i : ι) : F.HBL i :=
  ⟨h.nec i i, h.distrib i i, h.sigma1 i i i⟩

/-- The full cross-theory conditions contain the conditions from each theory. -/
theorem CrossHBL.toFrom (h : F.CrossHBL) (i : ι) : F.CrossHBLFrom i :=
  ⟨fun j _ => h.nec i j, fun j _ => h.distrib i j, fun j k _ => h.sigma1 i j k⟩

end ProvFamily

/-! ## K4a — no ring of consistency proofs under the named conditions -/

/-- **K4a-local (main statement): an anchor on a ring of consistency proofs is
inconsistent.**  Let `F` be a family of `n` theories in which every theory
proves the consistency statement of its ring successor
(`F.Thm i (F.con (ringNext i))`).  If one theory `i₀` is implicationally closed
(`ImpClosed i₀`), has Gödel's second incompleteness property (`GodelII i₀`),
and satisfies the cross-theory conditions towards every other theory
(`CrossHBLFrom i₀`), then `i₀` proves `⊥`.

Nothing is assumed about any other theory beyond the ring hypothesis, and no
`D1`–`D3` condition is assumed for any theory.  For `n = 1` the hypotheses
`ImpClosed i₀` and `CrossHBLFrom i₀` are not needed (the ring hypothesis is
then `i₀ ⊢ con i₀`).  This is a statement about abstract structures; it
applies to concrete formal systems only insofar as they satisfy the named
conditions. -/
theorem consistencyRing_anchor_inconsistent_of_impClosed_godelII_crossHBLFrom
    {n : Nat} (F : ProvFamily (Fin n)) (i₀ : Fin n)
    (hImpClosed : F.ImpClosed i₀)
    (hGodelII : F.GodelII i₀)
    (hFrom : F.CrossHBLFrom i₀)
    (hRing : ∀ i, F.Thm i (F.con (ringNext i))) :
    F.Thm i₀ F.bot := by
  -- Hypothetical syllogism at the anchor, from `mp`, `K` and `S`.
  have syll : ∀ {A B C : F.Sent},
      F.Thm i₀ (F.imp A B) → F.Thm i₀ (F.imp B C) → F.Thm i₀ (F.imp A C) :=
    fun h1 h2 => hImpClosed.mp (hImpClosed.mp (hImpClosed.axS _ _ _)
      (hImpClosed.mp (hImpClosed.axK _ _) h2)) h1
  -- The anchor proves the consistency of every node at distance `s + 1 ≤ n`.
  have hchain : ∀ s : Nat, s < n → F.Thm i₀ (F.con (ringIter i₀ (s + 1))) := by
    intro s hs
    induction s with
    | zero => exact hRing i₀
    | succ s ih =>
      have hij := ih (by omega)
      have hne : ringIter i₀ (s + 1) ≠ i₀ :=
        ringIter_ne_self_of_pos_of_lt i₀ (s + 1) (by omega) (by omega)
      have a := hFrom.nec _ hne _ (hRing (ringIter i₀ (s + 1)))
      have c := hImpClosed.mp (hFrom.distrib _ hne _ F.bot) a
      have d := hFrom.sigma1 _ (ringNext (ringIter i₀ (s + 1))) hne F.bot
      exact syll (syll d c) hij
  have hi := i₀.isLt
  have h := hchain (n - 1) (by omega)
  have hn : n - 1 + 1 = i₀.val + n - i₀.val := by omega
  rw [hn, ringIter_reach] at h
  exact hGodelII h

/-- **Inconsistency propagates backwards along a verified consistency proof.**
If theory `j` proves the consistency statement of theory `k`, verifies `k`'s
proofs (`CrossNec j k`), is closed under modus ponens, and `k` proves `⊥`, then
`j` proves `⊥`. -/
theorem inconsistent_of_proves_con_of_inconsistent {ι : Type} (F : ProvFamily ι) {j k : ι}
    (hMp : F.MpClosed j) (hNec : F.CrossNec j k) (hCon : F.Thm j (F.con k))
    (hk : F.Thm k F.bot) : F.Thm j F.bot :=
  hMp hCon (hNec F.bot hk)

/-- **K4a (derived from K4a-local): no ring of consistency proofs.**  Let `F` be
a family of `n` theories such that every theory is implicationally closed
(`ImpClosed`), at least one theory has Gödel's second incompleteness property
(`∃ i₀, GodelII i₀`), and the family satisfies the cross-theory
Hilbert–Bernays–Löb conditions (`CrossHBL`, whose diagonal is `D1`–`D3`).  If
every theory proves the consistency statement of its ring successor, then every
theory proves `⊥`.

The proof uses `CrossHBL` only off the diagonal (at the anchor, and for the
ring links `CrossNec i (ringNext i)`), and uses `ImpClosed` only through modus
ponens away from the anchor.  For `n = 0` the anchor hypothesis is
unsatisfiable. -/
theorem consistencyRing_all_inconsistent_of_impClosed_godelIIAnchor_crossHBL
    {n : Nat} (F : ProvFamily (Fin n))
    (hImpClosed : ∀ i, F.ImpClosed i)
    (hGodelII : ∃ i₀ : Fin n, F.GodelII i₀)
    (hBridge : F.CrossHBL)
    (hRing : ∀ i, F.Thm i (F.con (ringNext i))) :
    ∀ i, F.Thm i F.bot := by
  obtain ⟨i₀, hG⟩ := hGodelII
  have h0 : F.Thm i₀ F.bot :=
    consistencyRing_anchor_inconsistent_of_impClosed_godelII_crossHBLFrom F i₀ (hImpClosed i₀)
      hG (hBridge.toFrom i₀) hRing
  have hback : ∀ k : Nat, ∀ j : Fin n, F.Thm (ringIter j k) F.bot → F.Thm j F.bot := by
    intro k
    induction k with
    | zero => intro j hj; exact hj
    | succ k ih =>
      intro j hj
      rw [ringIter_succ'] at hj
      exact inconsistent_of_proves_con_of_inconsistent F (hImpClosed j).mp
        (hBridge.nec j (ringNext j)) (hRing j) (ih (ringNext j) hj)
  intro j
  exact hback (i₀.val + n - j.val) j (by rw [ringIter_reach]; exact h0)

/-! ## K5 — self-verification -/

/-- **K5.**  An inconsistent theory closed under modus ponens and ex falso
proves the local reflection schema `□ⱼA → A` for *every* theory `j` of the
family, in particular for itself, and for every sentence `A`.

Consequently, observing "theory `i` proves its own local reflection schema"
does not distinguish a sound theory from an inconsistent one. -/
theorem inconsistent_proves_every_local_reflection_of_mp_efq {ι : Type} (F : ProvFamily ι)
    (i : ι) (hMp : F.MpClosed i) (hEfq : F.HasEfq i) (hInconsistent : F.Thm i F.bot) :
    ∀ (j : ι) (A : F.Sent), F.Thm i (F.imp (F.box j A) A) :=
  fun _ _ => hMp (hEfq _) hInconsistent

/-- K5, consistency form: an inconsistent theory closed under modus ponens and
ex falso proves the consistency statement of every theory of the family,
itself included.  (Ex falso can here be replaced by the axiom scheme `K`.) -/
theorem inconsistent_proves_every_con_of_mp_efq {ι : Type} (F : ProvFamily ι) (i : ι)
    (hMp : F.MpClosed i) (hEfq : F.HasEfq i) (hInconsistent : F.Thm i F.bot) :
    ∀ j : ι, F.Thm i (F.con j) :=
  fun j => inconsistent_proves_every_local_reflection_of_mp_efq F i hMp hEfq hInconsistent j F.bot

/-- **K5-iff.**  For a theory closed under modus ponens and ex falso that has
Gödel's second incompleteness property, proving its own local reflection
schema is *equivalent* to being inconsistent. -/
theorem proves_own_local_reflection_iff_inconsistent_of_mp_efq_godelII
    {ι : Type} (F : ProvFamily ι) (i : ι)
    (hMp : F.MpClosed i) (hEfq : F.HasEfq i) (hGodelII : F.GodelII i) :
    (∀ A : F.Sent, F.Thm i (F.imp (F.box i A) A)) ↔ F.Thm i F.bot :=
  ⟨fun h => hGodelII (h F.bot),
   fun h A => inconsistent_proves_every_local_reflection_of_mp_efq F i hMp hEfq h i A⟩

/-! ## The inconsistent family, and a degenerate interface to avoid -/

/-- The trivial family: one sentence, and every theory proves it.  It satisfies
every closure condition and is inconsistent. -/
def trivialFamily (ι : Type) : ProvFamily ι where
  Sent := Unit
  bot := ()
  imp := fun _ _ => ()
  box := fun _ _ => ()
  Thm := fun _ _ => True

/-- **K4a non-vacuity.**  All hypotheses of K4a hold together in
`trivialFamily (Fin n)` for every `n ≥ 1`.  (By K4a every family satisfying
all of them is inconsistent; the tightness witnesses exhibit consistent
families satisfying all hypotheses but one.) -/
theorem k4a_nonvacuous (n : Nat) (hn : 1 ≤ n) :
    (∀ i, (trivialFamily (Fin n)).ImpClosed i) ∧
    (∃ i₀ : Fin n, (trivialFamily (Fin n)).GodelII i₀) ∧
    (trivialFamily (Fin n)).CrossHBL ∧
    (∀ i, (trivialFamily (Fin n)).Thm i ((trivialFamily (Fin n)).con (ringNext i))) :=
  ⟨fun _ => ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ _ => trivial⟩,
   ⟨⟨0, hn⟩, fun _ => trivial⟩,
   ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩,
   fun _ => trivial⟩

/-- **K4a-local non-vacuity.**  All hypotheses of K4a-local hold together in
`trivialFamily (Fin n)`, at every node. -/
theorem k4a_local_nonvacuous (n : Nat) (i₀ : Fin n) :
    (trivialFamily (Fin n)).ImpClosed i₀ ∧
    (trivialFamily (Fin n)).GodelII i₀ ∧
    (trivialFamily (Fin n)).CrossHBLFrom i₀ ∧
    (∀ i, (trivialFamily (Fin n)).Thm i ((trivialFamily (Fin n)).con (ringNext i))) :=
  ⟨⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ _ => trivial⟩, fun _ => trivial,
   ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩,
   fun _ => trivial⟩

/-- **K5 non-vacuity.**  The hypotheses of K5 hold in `trivialFamily`. -/
theorem k5_nonvacuous :
    (trivialFamily Unit).MpClosed () ∧ (trivialFamily Unit).HasEfq () ∧
    (trivialFamily Unit).Thm () (trivialFamily Unit).bot :=
  ⟨fun _ _ => trivial, fun _ => trivial, trivial⟩

/-- **K5-iff non-vacuity (inconsistent instance).**  The hypotheses of K5-iff
hold in `trivialFamily`, where both sides of the equivalence are true.  (A
consistent instance, where both sides are false, is
`k5_iff_nonvacuous_consistent`.) -/
theorem k5_iff_nonvacuous :
    (trivialFamily Unit).MpClosed () ∧ (trivialFamily Unit).HasEfq () ∧
    (trivialFamily Unit).GodelII () :=
  ⟨fun _ _ => trivial, fun _ => trivial, fun _ => trivial⟩

/-- A *degenerate* provability interface, recorded as a negative example of
interface design.  Sentences are meta-level propositions, and "necessitation"
is stated as `P → Prov P` ("every true proposition is provable"), which
conflates truth with theoremhood. -/
structure NaivePropProv where
  Prov : Prop → Prop
  nec  : ∀ {P : Prop}, P → Prov P
  lob  : ∀ {P : Prop}, Prov (Prov P → P) → Prov P

/-- Negative example (`NaivePropProv`): *no* such structure is consistent, with
no ring and no bridge involved.  If `Prov False` failed, that failure would be
a true proposition, hence "provable" by `nec`, and Löb would give `Prov False`.
Any impossibility theorem stated over this interface is vacuous; this is why
`ProvFamily` separates `Thm` from truth. -/
theorem NaivePropProv.not_not_prov_false (T : NaivePropProv) : ¬ ¬ T.Prov False :=
  fun h => h (T.lob (T.nec h))

/-- An instance of `NaivePropProv`, with `Prov P := True`. -/
def NaivePropProv.trivial : NaivePropProv where
  Prov := fun _ => True
  nec := fun _ => True.intro
  lob := fun _ => True.intro

/-- Positive example (`NaivePropProv`): the structure is inhabited, so the
negative example above is not vacuous. -/
theorem NaivePropProv.nonempty : Nonempty NaivePropProv := ⟨NaivePropProv.trivial⟩

end Toy.KernelTrust
