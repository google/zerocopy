import ToyPredTrans.Programs

/-!
# Angelic/demonic normal form of monotone transformers

Everything in this file is fully proved.  The normal form is near-definitional: the
multirelation of a monotone transformer `T` is `T` itself, read as "the set `P` is available
at `s` when `T P s`".  The content is the bookkeeping: which multirelations represent which
transformers, and that the representation is unique exactly among up-closed multirelations.
-/

namespace Toy.PredTrans

universe u

variable {σ : Type u}

/-- Every transformer of the form `angelicDemonic A` is monotone. -/
theorem monotone_angelicDemonic (A : σ → Pred σ → Prop) : Monotone (angelicDemonic A) := by
  intro P Q hPQ s h
  obtain ⟨P', hA, hP'⟩ := h
  exact ⟨P', hA, fun t ht => hPQ t (hP' t ht)⟩

/-- **Monotone transformers are exactly angelic choices of demonic updates, with the
multirelation exposed.**  `T` is monotone if and only if it equals the transformer of its own
multirelation `multirelOf T`, i.e. `T Q s ↔ ∃ P, T P s ∧ ∀ t, P t → Q t`. -/
theorem monotone_iff_eq_angelicDemonic_multirelOf (T : Transformer σ) :
    Monotone T ↔ T = angelicDemonic (multirelOf T) := by
  constructor
  · intro h
    apply trans_ext
    intro Q s
    constructor
    · intro hT
      exact ⟨Q, hT, fun _ ht => ht⟩
    · intro hh
      obtain ⟨P, hP, hPQ⟩ := hh
      exact h P Q hPQ s hP
  · intro h
    rw [h]
    exact monotone_angelicDemonic _

/-- Existential form: `T` is monotone if and only if it is `angelicDemonic A` for some
multirelation `A`. -/
theorem monotone_iff_exists_angelicDemonic (T : Transformer σ) :
    Monotone T ↔ ∃ A : σ → Pred σ → Prop, T = angelicDemonic A := by
  constructor
  · intro h
    exact ⟨multirelOf T, (monotone_iff_eq_angelicDemonic_multirelOf T).mp h⟩
  · intro h
    obtain ⟨A, hA⟩ := h
    rw [hA]
    exact monotone_angelicDemonic A

/-- The multirelation of `T` is up-closed exactly when `T` is monotone. -/
theorem upClosed_multirelOf_iff (T : Transformer σ) : UpClosed (multirelOf T) ↔ Monotone T :=
  ⟨fun h P Q hPQ s hP => h s P Q hP hPQ, fun h s P P' hP hPP' => h P P' hPP' s hP⟩

/-- A multirelation is recovered from its transformer exactly when it is up-closed.  So
up-closed multirelations and monotone transformers correspond one-to-one. -/
theorem multirelOf_angelicDemonic_eq_iff (A : σ → Pred σ → Prop) :
    multirelOf (angelicDemonic A) = A ↔ UpClosed A := by
  constructor
  · intro h
    rw [← h]
    exact (upClosed_multirelOf_iff _).mpr (monotone_angelicDemonic A)
  · intro h
    funext s P
    apply propext
    constructor
    · intro hh
      obtain ⟨P', hA, hP'⟩ := hh
      exact h s P' P hA hP'
    · intro hA
      exact ⟨P, hA, fun _ ht => ht⟩

/-- Without up-closure the multirelation is not unique: two different multirelations on
`Bool` (singletons only, versus all sets containing the current state) have the same
transformer. -/
theorem angelicDemonic_not_injective :
    ∃ A A' : Bool → Pred Bool → Prop, A ≠ A' ∧ angelicDemonic A = angelicDemonic A' := by
  refine ⟨fun s P => P = fun t => t = s, fun s P => P s, ?_, ?_⟩
  · intro h
    have h0 := congrFun (congrFun h true) (fun _ => True)
    have h1 : (fun _ : Bool => True) = fun t => t = true := h0.mpr trivial
    have h2 : (True : Prop) = (false = true) := congrFun h1 false
    have h3 : false = true := h2.mp trivial
    cases h3
  · apply trans_ext
    intro Q s
    constructor
    · intro h
      obtain ⟨P, hP, hPQ⟩ := h
      have hP' : P = fun t => t = s := hP
      refine ⟨P, ?_, hPQ⟩
      rw [hP']
    · intro h
      obtain ⟨P, hP, hPQ⟩ := h
      exact ⟨fun t => t = s, rfl, fun t ht => by
        rw [ht]
        exact hPQ s hP⟩

/-! ## Positive and negative examples -/

/-- Positive: every `wp` is an angelic choice of demonic updates in which the angel has at
most one option, the image of the current state. -/
theorem wp_eq_angelicDemonic (R : Rel σ) (term : Pred σ) :
    wp R term = angelicDemonic (fun s P => term s ∧ P = R s) := by
  apply trans_ext
  intro Q s
  constructor
  · intro h
    exact ⟨R s, ⟨h.1, rfl⟩, h.2⟩
  · intro h
    obtain ⟨P, ⟨ht, hP⟩, hPQ⟩ := h
    refine ⟨ht, ?_⟩
    intro s' hr
    apply hPQ
    rw [hP]
    exact hr

/-- Positive: `eventually` is the angelic choice of a threshold `N` followed by the demonic
choice of a number `≥ N`.  It is a legitimate angelic/demonic game although it is not the
`wp` of any relation. -/
theorem eventually_eq_angelicDemonic :
    eventually = angelicDemonic (fun _ P => ∃ N : Nat, P = fun n => N ≤ n) := by
  apply trans_ext
  intro Q s
  constructor
  · intro h
    obtain ⟨N, hN⟩ := h
    exact ⟨fun n => N ≤ n, ⟨N, rfl⟩, hN⟩
  · intro h
    obtain ⟨P, ⟨N, hP⟩, hPQ⟩ := h
    refine ⟨N, fun n hn => hPQ n ?_⟩
    rw [hP]
    exact hn

/-- Positive: angelic havoc is the angelic choice of a single final state. -/
theorem angelic_eq_angelicDemonic :
    (angelic : Transformer σ) = angelicDemonic (fun _ P => ∃ x : σ, P = fun t => t = x) := by
  apply trans_ext
  intro Q s
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨fun t => t = x, ⟨x, rfl⟩, fun t ht => by
      rw [ht]
      exact hx⟩
  · intro h
    obtain ⟨P, ⟨x, hP⟩, hPQ⟩ := h
    refine ⟨x, hPQ x ?_⟩
    rw [hP]

/-- Negative (`angelicDemonic`): negation is not `angelicDemonic A` for any multirelation
`A`, because it is not monotone. -/
theorem negT_ne_angelicDemonic (A : Unit → Pred Unit → Prop) :
    (negT : Transformer Unit) ≠ angelicDemonic A := by
  intro h
  apply not_monotone_negT
  rw [h]
  exact monotone_angelicDemonic A

/-- Positive (`multirelOf`): at state `s` the multirelation of `skip` offers exactly the sets
containing `s`. -/
theorem multirelOf_wlp_skipR (s : σ) (P : Pred σ) : multirelOf (wlp skipR) s P ↔ P s :=
  wlp_skipR P s

/-- Negative (`multirelOf`): at state `0` the multirelation of `skip` on `Nat` does not offer
the set `{1}`. -/
theorem not_multirelOf_wlp_skipR_example :
    ¬ multirelOf (wlp (skipR : Rel Nat)) 0 (fun n => n = 1) := by
  intro h
  have h1 : (0 : Nat) = 1 := (wlp_skipR _ 0).mp h
  omega

/-- Positive (`UpClosed`): "all sets containing the current state" is up-closed. -/
theorem upClosed_contains : UpClosed (fun (s : σ) (P : Pred σ) => P s) :=
  fun s _ _ hP hPP' => hPP' s hP

/-- Negative (`UpClosed`): "exactly the singleton of the current state" is not up-closed. -/
theorem not_upClosed_singleton :
    ¬ UpClosed (fun (s : Bool) (P : Pred Bool) => P = fun t => t = s) := by
  intro h
  have h1 : (fun _ : Bool => True) = fun t => t = true :=
    h true (fun t => t = true) (fun _ => True) rfl (fun _ _ => trivial)
  have h2 : (True : Prop) = (false = true) := congrFun h1 false
  have h3 : false = true := h2.mp trivial
  cases h3

/-! ## Canonical tightness witnesses and non-vacuity -/

/-- Canonical form of the monotonicity hypothesis: negation is not monotone and is not of the
form `angelicDemonic A` for any multirelation `A`. -/
theorem negT_not_monotone_not_angelicDemonic :
    ¬ Monotone (negT : Transformer Unit) ∧
      ¬ ∃ A : Unit → Pred Unit → Prop, (negT : Transformer Unit) = angelicDemonic A :=
  ⟨not_monotone_negT, fun ⟨A, hA⟩ => negT_ne_angelicDemonic A hA⟩

/-- Canonical form of the up-closure hypothesis of `multirelOf_angelicDemonic_eq_iff`: the
singleton multirelation on `Bool` is not up-closed and is not recovered from its transformer
by `multirelOf`. -/
theorem not_upClosed_not_recovered_by_multirelOf :
    ¬ UpClosed (fun (s : Bool) (P : Pred Bool) => P = fun t => t = s) ∧
      multirelOf (angelicDemonic (fun (s : Bool) (P : Pred Bool) => P = fun t => t = s)) ≠
        (fun (s : Bool) (P : Pred Bool) => P = fun t => t = s) :=
  ⟨not_upClosed_singleton, fun h => not_upClosed_singleton ((multirelOf_angelicDemonic_eq_iff _).mp h)⟩

/-- Non-vacuity of `multirelOf_angelicDemonic_eq_iff`: "all sets containing the current state"
is up-closed and is recovered by `multirelOf` (both sides hold); the singleton multirelation is
neither (both sides fail). -/
theorem multirelOf_angelicDemonic_both_sides_occur :
    (UpClosed (fun (s : Bool) (P : Pred Bool) => P s) ∧
        multirelOf (angelicDemonic (fun (s : Bool) (P : Pred Bool) => P s)) =
          (fun (s : Bool) (P : Pred Bool) => P s)) ∧
      (¬ UpClosed (fun (s : Bool) (P : Pred Bool) => P = fun t => t = s) ∧
        multirelOf (angelicDemonic (fun (s : Bool) (P : Pred Bool) => P = fun t => t = s)) ≠
          (fun (s : Bool) (P : Pred Bool) => P = fun t => t = s)) :=
  ⟨⟨upClosed_contains, (multirelOf_angelicDemonic_eq_iff _).mpr upClosed_contains⟩,
   not_upClosed_not_recovered_by_multirelOf⟩

/-- Non-vacuity of `monotone_iff_eq_angelicDemonic_multirelOf`: `eventually` is monotone and
equals the transformer of its own multirelation (both sides hold); negation is neither (both
sides fail). -/
theorem monotone_angelicDemonic_both_sides_occur :
    (Monotone eventually ∧ eventually = angelicDemonic (multirelOf eventually)) ∧
      (¬ Monotone (negT : Transformer Unit) ∧
        (negT : Transformer Unit) ≠ angelicDemonic (multirelOf (negT : Transformer Unit))) :=
  ⟨⟨monotone_eventually, (monotone_iff_eq_angelicDemonic_multirelOf _).mp monotone_eventually⟩,
   not_monotone_negT, fun h => negT_ne_angelicDemonic _ h⟩

/-- Up-closure does not make a multirelation the *only* one inducing its transformer: the
up-closed "all sets containing the current state" and the non-up-closed singleton
multirelation induce the same transformer.  Uniqueness holds only among up-closed
multirelations. -/
theorem upClosed_not_unique_among_all :
    UpClosed (fun (s : Bool) (P : Pred Bool) => P s) ∧
      ¬ UpClosed (fun (s : Bool) (P : Pred Bool) => P = fun t => t = s) ∧
      angelicDemonic (fun (s : Bool) (P : Pred Bool) => P s) =
        angelicDemonic (fun (s : Bool) (P : Pred Bool) => P = fun t => t = s) := by
  refine ⟨upClosed_contains, not_upClosed_singleton, ?_⟩
  apply trans_ext
  intro Q s
  constructor
  · intro h
    obtain ⟨P, hP, hPQ⟩ := h
    exact ⟨fun t => t = s, rfl, fun t ht => by
      rw [ht]
      exact hPQ s hP⟩
  · intro h
    obtain ⟨P, hP, hPQ⟩ := h
    have hP' : P = fun t => t = s := hP
    refine ⟨P, ?_, hPQ⟩
    rw [hP']

end Toy.PredTrans
