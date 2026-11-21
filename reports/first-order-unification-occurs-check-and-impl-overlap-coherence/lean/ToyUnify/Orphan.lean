import ToyUnify.Impls

/-!
# Stability of coherence verdicts under orphan-rule extensions

A toy crate graph: every trait and every constructor has an owning crate, and some constructors
are marked *fundamental* (transparent in their first argument for the orphan rule). A downstream
extension by crate `c` may add impls only where the trait is owned by `c` or the self type is
local to `c` (`isLocalTy`); `c` is *fresh* for the impl set and for the symbols of the query
(it owns none of them). A verdict about the impl set is *stable* (`StableUnderDownstream fund`) if
it holds in every such extension, under every ownership map whose set of fundamental constructors
is the fixed predicate `fund`.

* `overlapCheckSaysDisjoint_stable`: the unification-only "disjoint" verdict is stable (indeed it
  holds in every impl set).
* `implements_append_iff_of_orphanOK`: for constrained impl sets, a fresh crate's orphan-allowed
  impls change no ground fact `X: B` whose trait and constructors it does not own; so negative
  facts about such ground pairs are stable (`not_implements_stable_of_isGround`).
* `exists_orphanOK_overlapping_impl_iff_fundSpineVar`: a fresh crate can add an impl of `B` whose
  self type shares a ground instance with `X` iff `X`'s fundamental spine ends in a variable.
* `noInstanceImplements_stable_of_not_fundSpineVar`: if `X`'s fundamental spine does not end in a
  variable and no impl of `B` in the impl set has a self type sharing a ground instance with `X`,
  then "no ground instance of `X` implements `B`" is stable.
* `noInstanceImplements_vec_not_stable`: without the second condition this fails: negative
  reasoning over the open type `Vec<T>` (`Vec` not fundamental) is unstable when an impl of `B`
  for `Vec<T>` has a where-clause.
* `whereClause_disjointness_not_stable`: where-clause-based non-overlap is not stable.
-/

namespace Toy.Unify

/-- Ownership in a toy crate graph: the crate owning each trait and each constructor, and which
constructors are fundamental. -/
structure Owners where
  traitOwner : Nat → Nat
  ctorOwner : Nat → Nat
  fundamental : Nat → Bool

/-- `isLocalTy o c t`: the type `t` counts as local to crate `c` for the orphan rule — its head
constructor is owned by `c`, or its head is fundamental and its first argument is local to `c`.
A variable is never local. Arguments after the first of a fundamental constructor are not
inspected (there is no covered-parameter check; see
`orphanOK_uncovered_param_overlap_example`). -/
def isLocalTy (o : Owners) (c : Nat) : Term → Bool
  | .var _ => false
  | .con f [] => o.ctorOwner f == c
  | .con f (a :: _) => o.ctorOwner f == c || (o.fundamental f && isLocalTy o c a)

/-- Toy orphan rule: crate `c` may write impl `e` iff `c` owns `e`'s trait or `e`'s self type is
local to `c`. -/
def OrphanOK (o : Owners) (c : Nat) (e : Impl) : Prop :=
  o.traitOwner e.trait = c ∨ isLocalTy o c e.selfTy = true

instance (o : Owners) (c : Nat) (e : Impl) : Decidable (OrphanOK o c e) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Crate `c` is fresh for `I`: it owns no trait and no constructor mentioned by any impl of `I`
(a crate downstream of everything in `I`). -/
def FreshCrate (o : Owners) (c : Nat) (I : ImplSet) : Prop :=
  ∀ i ∈ I, (∀ tr ∈ i.traits, o.traitOwner tr ≠ c) ∧ (∀ f ∈ i.ctors, o.ctorOwner f ≠ c)

instance (o : Owners) (c : Nat) (I : ImplSet) : Decidable (FreshCrate o c I) :=
  inferInstanceAs (Decidable (∀ i ∈ I, _))

/-- Every where-clause variable of every impl occurs in that impl's self type (no unconstrained
generic parameters). -/
def Constrained (I : ImplSet) : Prop :=
  ∀ i ∈ I, ∀ b ∈ i.bounds, ∀ x ∈ b.ty.vars, x ∈ i.selfTy.vars

instance (I : ImplSet) : Decidable (Constrained I) :=
  inferInstanceAs (Decidable (∀ i ∈ I, _))

/-- Crate `c` is fresh for the impl set `I` and for the query symbols `trs` (traits) and `ctors`
(constructors): it owns no trait or constructor of `I`, no trait in `trs` and no constructor in
`ctors`. -/
def FreshFor (o : Owners) (c : Nat) (I : ImplSet) (trs ctors : List Nat) : Prop :=
  FreshCrate o c I ∧ (∀ tr ∈ trs, o.traitOwner tr ≠ c) ∧ (∀ f ∈ ctors, o.ctorOwner f ≠ c)

instance (o : Owners) (c : Nat) (I : ImplSet) (trs ctors : List Nat) :
    Decidable (FreshFor o c I trs ctors) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A predicate `P` on impl sets is stable for `I`, relative to the fundamental-constructor
predicate `fund` and the query symbols `trs` and `ctors`, if `P (I ++ E)` holds for every
ownership map `o` with `o.fundamental = fund`, every crate `c` that is fresh under `o` for `I` and
for the query symbols, and every list `E` of impls that `c` may write under the orphan rule.
Quantifying over `o` lets the new crate own any trait or constructor that is not mentioned in `I`
or the query; which constructors are fundamental is fixed by `fund` (for upstream constructors and
for constructors the new crate owns alike), so an extension cannot make an upstream constructor
fundamental. -/
def StableUnderDownstream (fund : Nat → Bool) (I : ImplSet) (trs ctors : List Nat)
    (P : ImplSet → Prop) : Prop :=
  ∀ (o : Owners) (c : Nat) (E : ImplSet), o.fundamental = fund → FreshFor o c I trs ctors →
    (∀ e ∈ E, OrphanOK o c e) → P (I ++ E)

/-- Stability includes the impl set itself (the empty extension, by a crate owning nothing). -/
theorem StableUnderDownstream.self {fund : Nat → Bool} {I : ImplSet} {trs ctors : List Nat}
    {P : ImplSet → Prop} (h : StableUnderDownstream fund I trs ctors P) : P I := by
  have := h ⟨fun _ => 0, fun _ => 0, fund⟩ 1 [] rfl
    ⟨fun _ _ => ⟨fun _ _ => Nat.zero_ne_one, fun _ _ => Nat.zero_ne_one⟩,
      fun _ _ => Nat.zero_ne_one, fun _ _ => Nat.zero_ne_one⟩ nofun
  simpa using this

/-- `fundSpineVar o X`: following first arguments through fundamental head constructors from the
root of `X` reaches a variable. -/
def fundSpineVar (o : Owners) : Term → Bool
  | .var _ => true
  | .con _ [] => false
  | .con f (a :: _) => o.fundamental f && fundSpineVar o a

/-- Negative reasoning over an open type: no ground instance of `X` implements `B` in `I`. -/
def NoInstanceImplements (I : ImplSet) (B : Nat) (X : Term) : Prop :=
  ∀ θ : Subst, ¬ Implements I B (subst θ X)

/-! ## Example crate graph

Crate 0 owns `u8, u32, Box, Vec, Pair` (`Box` is fundamental); crate 1 owns every trait;
crate 2 owns the constructor `L` (symbol 7). -/

/-- The example ownership assignment. -/
def ownersEx : Owners :=
  { traitOwner := fun _ => 1, ctorOwner := fun f => if f = 7 then 2 else 0,
    fundamental := fun f => f == 2 }

/-- The type `L`, owned by crate 2. -/
def localL : Term := .con 7 []

/-! ## Definition examples -/

theorem isLocalTy_example : isLocalTy ownersEx 2 localL = true := by decide
theorem isLocalTy_fundamental_example : isLocalTy ownersEx 2 (box localL) = true := by decide
theorem not_isLocalTy_example : isLocalTy ownersEx 2 (vec localL) = false := by decide
theorem not_isLocalTy_var_example : isLocalTy ownersEx 2 (.var 0) = false := by decide

theorem orphanOK_example : OrphanOK ownersEx 2 ⟨12, localL, []⟩ := by decide
theorem not_orphanOK_example : ¬ OrphanOK ownersEx 2 ⟨12, u8, []⟩ := by decide

theorem freshCrate_example : FreshCrate ownersEx 2 I_AB := by decide
theorem not_freshCrate_example : ¬ FreshCrate ownersEx 0 I_AB := by decide

theorem freshFor_example : FreshFor ownersEx 2 I_AB [12] (u8.ctors) := by decide
/-- Crate 2 is not fresh for a query mentioning its own constructor `L`. -/
theorem not_freshFor_example : ¬ FreshFor ownersEx 2 [] [] (localL.ctors) := by decide

theorem constrained_example : Constrained I_AB := by decide
theorem not_constrained_example : ¬ Constrained [⟨12, u8, [⟨13, .var 0⟩]⟩] := by decide

theorem fundSpineVar_example : fundSpineVar ownersEx (box (.var 0)) = true := by decide
theorem not_fundSpineVar_example : fundSpineVar ownersEx (vec (.var 0)) = false := by decide

/-- A verdict that holds in every impl set is stable: `impl Tr for Vec<T>` and `impl Tr for Box<U>`
overlap in no impl set. -/
theorem stableUnderDownstream_example :
    StableUnderDownstream ownersEx.fundamental I_AB [10] [3, 2]
      (fun I' => ¬ ImplsOverlapIn I' ⟨10, vec (.var 0), []⟩ ⟨10, box (.var 1), []⟩) := by
  intro o c E _ _ _
  rintro ⟨_, θ₁, θ₂, _, h, _⟩
  simp [vec, box, subst_con] at h

theorem noInstanceImplements_example : NoInstanceImplements I_AB 12 u8 := by
  intro θ h
  rw [subst_of_isGround (by decide) θ, implements_I_AB_B_iff] at h
  exact absurd h (by decide)
theorem not_noInstanceImplements_example : ¬ NoInstanceImplements I_AB 12 (.var 0) :=
  fun h => h [(0, u32)] ((implements_I_AB_B_iff _).2 (by decide))

/-! ## Helper lemmas -/

theorem isLocalTy_ctor_owned (o : Owners) (c : Nat) :
    ∀ t : Term, isLocalTy o c t = true → ∃ f ∈ t.ctors, o.ctorOwner f = c
  | .var _, h => by simp [isLocalTy] at h
  | .con f [], h => ⟨f, by simp [Term.ctors], by simpa [isLocalTy] using h⟩
  | .con f (a :: as), h => by
    simp only [isLocalTy, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨_, ha⟩
    · exact ⟨f, by simp [Term.ctors], h⟩
    · obtain ⟨g, hg, hgo⟩ := isLocalTy_ctor_owned o c a ha
      exact ⟨g, by simp [Term.ctors, Term.ctorsList, hg], hgo⟩

theorem subst_ctors_subset (θ : Subst) :
    ∀ (t : Term) (f : Nat), f ∈ t.ctors → f ∈ (subst θ t).ctors
  | .var _, _, hf => by simp [Term.ctors] at hf
  | .con _ ts, f, hf => by
    simp only [Term.ctors, List.mem_cons] at hf
    simp only [subst, Term.ctors, List.mem_cons]
    rcases hf with rfl | hf
    · exact Or.inl rfl
    · exact Or.inr (substList_ctors_subset θ ts f hf)
where
  substList_ctors_subset (θ : Subst) :
      ∀ (ts : List Term) (f : Nat), f ∈ Term.ctorsList ts → f ∈ Term.ctorsList (substList θ ts)
    | [], _, hf => by simp [Term.ctorsList] at hf
    | t :: ts, f, hf => by
      simp only [Term.ctorsList, List.mem_append] at hf
      simp only [substList, Term.ctorsList, List.mem_append]
      exact hf.elim (fun h => Or.inl (subst_ctors_subset θ t f h))
        (fun h => Or.inr (substList_ctors_subset θ ts f h))

theorem subst_ctors_decomp (θ : Subst) :
    ∀ (t : Term) (f : Nat), f ∈ (subst θ t).ctors →
      f ∈ t.ctors ∨ ∃ x ∈ t.vars, f ∈ (substVar θ x).ctors
  | .var x, f, hf => Or.inr ⟨x, by simp [Term.vars], hf⟩
  | .con _ ts, f, hf => by
    simp only [subst, Term.ctors, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact Or.inl (by simp [Term.ctors])
    · rcases substList_ctors_decomp θ ts f hf with h | ⟨x, hx, hfx⟩
      · exact Or.inl (by simp [Term.ctors, h])
      · exact Or.inr ⟨x, by simp [Term.vars, hx], hfx⟩
where
  substList_ctors_decomp (θ : Subst) :
      ∀ (ts : List Term) (f : Nat), f ∈ Term.ctorsList (substList θ ts) →
        f ∈ Term.ctorsList ts ∨ ∃ x ∈ Term.varsList ts, f ∈ (substVar θ x).ctors
    | [], _, hf => by simp [substList, Term.ctorsList] at hf
    | t :: ts, f, hf => by
      simp only [substList, Term.ctorsList, List.mem_append] at hf
      rcases hf with hf | hf
      · rcases subst_ctors_decomp θ t f hf with h | ⟨x, hx, hfx⟩
        · exact Or.inl (by simp [Term.ctorsList, h])
        · exact Or.inr ⟨x, by simp [Term.varsList, hx], hfx⟩
      · rcases substList_ctors_decomp θ ts f hf with h | ⟨x, hx, hfx⟩
        · exact Or.inl (by simp [Term.ctorsList, h])
        · exact Or.inr ⟨x, by simp [Term.varsList, hx], hfx⟩

theorem substVar_ctors_subset_subst (θ : Subst) :
    ∀ (t : Term) (x : Nat), x ∈ t.vars → ∀ f ∈ (substVar θ x).ctors, f ∈ (subst θ t).ctors
  | .var _, _, hx, _, hf => by
    simp only [Term.vars, List.mem_singleton] at hx
    subst hx; exact hf
  | .con _ ts, x, hx, f, hf => by
    simp only [Term.vars] at hx
    simp only [subst, Term.ctors, List.mem_cons]
    exact Or.inr (substVar_ctors_subset_substList θ ts x hx f hf)
where
  substVar_ctors_subset_substList (θ : Subst) :
      ∀ (ts : List Term) (x : Nat), x ∈ Term.varsList ts →
        ∀ f ∈ (substVar θ x).ctors, f ∈ Term.ctorsList (substList θ ts)
    | [], _, hx, _, _ => by simp [Term.varsList] at hx
    | t :: ts, x, hx, f, hf => by
      simp only [Term.varsList, List.mem_append] at hx
      simp only [substList, Term.ctorsList, List.mem_append]
      exact hx.elim (fun h => Or.inl (substVar_ctors_subset_subst θ t x h f hf))
        (fun h => Or.inr (substVar_ctors_subset_substList θ ts x h f hf))

theorem isLocalTy_subst (o : Owners) (c : Nat) (θ : Subst) :
    ∀ t : Term, isLocalTy o c t = true → isLocalTy o c (subst θ t) = true
  | .var _, h => by simp [isLocalTy] at h
  | .con _ [], h => by simpa [subst, substList] using h
  | .con _ (a :: _), h => by
    simp only [isLocalTy, Bool.or_eq_true, Bool.and_eq_true] at h
    simp only [subst, substList, isLocalTy, Bool.or_eq_true, Bool.and_eq_true]
    exact h.elim Or.inl (fun ⟨hf, ha⟩ => Or.inr ⟨hf, isLocalTy_subst o c θ a ha⟩)

theorem fundSpineVar_of_isLocalTy_subst (o : Owners) (c : Nat) (θ : Subst) :
    ∀ X : Term, (∀ f ∈ X.ctors, o.ctorOwner f ≠ c) →
      isLocalTy o c (subst θ X) = true → fundSpineVar o X = true
  | .var _, _, _ => rfl
  | .con f [], hX, hloc => by
    simp only [subst, substList, isLocalTy, beq_iff_eq] at hloc
    exact absurd hloc (hX f (by simp [Term.ctors]))
  | .con f (a :: _), hX, hloc => by
    simp only [subst, substList, isLocalTy, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hloc
    rcases hloc with hfc | ⟨hfund, ha⟩
    · exact absurd hfc (hX f (by simp [Term.ctors]))
    · simp only [fundSpineVar, Bool.and_eq_true]
      exact ⟨hfund, fundSpineVar_of_isLocalTy_subst o c θ a
        (fun g hg => hX g (by simp [Term.ctors, Term.ctorsList, hg])) ha⟩

theorem isLocalTy_subst_groundAllTo (o : Owners) (c L : Nat) (hL : o.ctorOwner L = c)
    (vs : List Nat) :
    ∀ Y : Term, (∀ x ∈ Y.vars, x ∈ vs) → fundSpineVar o Y = true →
      isLocalTy o c (subst (groundAllTo (.con L []) vs) Y) = true
  | .var x, hY, _ => by
    have hx : x ∈ vs := hY x (by simp [Term.vars])
    simp [subst, substVar_groundAllTo hx, isLocalTy, hL]
  | .con _ [], _, hf => by simp [fundSpineVar] at hf
  | .con _ (a :: _), hY, hf => by
    simp only [fundSpineVar, Bool.and_eq_true] at hf
    simp only [subst, substList, isLocalTy, Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨hf.1, isLocalTy_subst_groundAllTo o c L hL vs a
      (fun x hx => hY x (by simp [Term.vars, Term.varsList, hx])) hf.2⟩

/-- Ownership maps with the same fundamental constructors give the same `fundSpineVar`. -/
theorem fundSpineVar_congr {o o' : Owners} (h : o.fundamental = o'.fundamental) :
    ∀ X : Term, fundSpineVar o X = fundSpineVar o' X
  | .var _ => rfl
  | .con _ [] => rfl
  | .con f (a :: _) => by simp only [fundSpineVar, h, fundSpineVar_congr h a]

/-- On a non-ground type nothing is derivable, so the equivalence of
`implements_append_iff_of_orphanOK` holds trivially there (both sides are false). -/
theorem implements_append_iff_of_not_isGround (I E : ImplSet) (B : Nat) {X : Term}
    (hng : ¬ IsGround X) :
    (Implements (I ++ E) B X ↔ Implements I B X) ∧ ¬ Implements (I ++ E) B X ∧
      ¬ Implements I B X :=
  ⟨⟨fun h => absurd h.isGround hng, fun h => absurd h.isGround hng⟩,
   fun h => hng h.isGround, fun h => hng h.isGround⟩

/-! ## Results -/

/-- The unification-only verdict is stable: if the checker says `i`, `j` are disjoint (self types
renamed apart), they overlap in no impl set at all, so in particular the verdict is stable for
every `I`, every fundamental-constructor predicate and every choice of query symbols. -/
theorem overlapCheckSaysDisjoint_stable (fund : Nat → Bool) (I : ImplSet) (trs ctors : List Nat)
    {i j : Impl} (hdisj : VarsDisjoint i.selfTy j.selfTy) (h : overlapCheckSaysDisjoint i j = true) :
    StableUnderDownstream fund I trs ctors (fun I' => ¬ ImplsOverlapIn I' i j) :=
  fun _ _ E _ _ _ => not_implsOverlapIn_of_overlapCheckSaysDisjoint hdisj h (I ++ E)

/-- Ground facts over symbols a fresh crate does not own are unaffected by its orphan-allowed
impls: if `X` is ground, `I` is constrained, `c` is fresh for `I`, `c` owns neither `B` nor any
constructor of `X`, and every impl of `E` is orphan-allowed for `c`, then `X: B` is derivable from
`I ++ E` iff it is derivable from `I`. (`Implements` holds only at ground types, so for a
non-ground `X` both sides are false: `implements_append_iff_of_not_isGround`.) -/
theorem implements_append_iff_of_orphanOK (o : Owners) (c : Nat) (I E : ImplSet) (B : Nat)
    (X : Term) (hXg : IsGround X) (hcons : Constrained I) (hfresh : FreshCrate o c I)
    (hB : o.traitOwner B ≠ c) (hX : ∀ f ∈ X.ctors, o.ctorOwner f ≠ c)
    (hE : ∀ e ∈ E, OrphanOK o c e) :
    Implements (I ++ E) B X ↔ Implements I B X := by
  -- groundness is not used by the argument (both sides are false otherwise)
  have hXg' := hXg
  clear hXg hXg'
  constructor
  · intro h
    induction h with
    | intro i θ hi hg _ ih =>
      simp only [List.mem_append] at hi
      rcases hi with hiI | hiE
      · refine Implements.intro i θ hiI hg (fun b hb => ?_)
        have htr : o.traitOwner b.trait ≠ c :=
          (hfresh i hiI).1 b.trait (by
            simp only [Impl.traits, List.mem_cons, List.mem_map]
            exact Or.inr ⟨b, hb, rfl⟩)
        have hct : ∀ f ∈ (subst θ b.ty).ctors, o.ctorOwner f ≠ c := by
          intro f hf
          rcases subst_ctors_decomp θ b.ty f hf with hfb | ⟨x, hx, hfx⟩
          · exact (hfresh i hiI).2 f (by
              simp only [Impl.ctors, List.mem_append, List.mem_flatMap]
              exact Or.inr ⟨b, hb, hfb⟩)
          · exact hX f (substVar_ctors_subset_subst θ i.selfTy x (hcons i hiI b hb x hx) f hfx)
        exact ih b hb htr hct
      · exfalso
        rcases hE i hiE with htr | hloc
        · exact hB htr
        · obtain ⟨f, hf, hfo⟩ := isLocalTy_ctor_owned o c i.selfTy hloc
          exact hX f (subst_ctors_subset θ i.selfTy f hf) hfo
  · exact Implements.mono (fun i hi => List.mem_append_left E hi)

/-- Corollary: under the same hypotheses, a negative ground fact `¬ (X: B)` in `I` stays true in
`I ++ E`. -/
theorem not_implements_append_of_orphanOK (o : Owners) (c : Nat) (I E : ImplSet) (B : Nat)
    (X : Term) (hXg : IsGround X) (hcons : Constrained I) (hfresh : FreshCrate o c I)
    (hB : o.traitOwner B ≠ c) (hX : ∀ f ∈ X.ctors, o.ctorOwner f ≠ c)
    (hE : ∀ e ∈ E, OrphanOK o c e) (hneg : ¬ Implements I B X) : ¬ Implements (I ++ E) B X :=
  fun h => hneg ((implements_append_iff_of_orphanOK o c I E B X hXg hcons hfresh hB hX hE).1 h)

/-- Corollary in stability form: for a ground `X` and a constrained `I`, a negative fact
`¬ (X: B)` is stable relative to every fundamental-constructor predicate `fund`, the query symbols
`[B]` and the constructors of `X`. -/
theorem not_implements_stable_of_isGround (fund : Nat → Bool) (I : ImplSet) (B : Nat) (X : Term)
    (hXg : IsGround X) (hcons : Constrained I) (hneg : ¬ Implements I B X) :
    StableUnderDownstream fund I [B] X.ctors (fun I' => ¬ Implements I' B X) :=
  fun o c E _ ⟨hfresh, htrs, hcts⟩ hE =>
    not_implements_append_of_orphanOK o c I E B X hXg hcons hfresh (htrs B (by simp)) hcts hE hneg

/-- For a non-ground `X` the stability of `¬ (X: B)` holds trivially (nothing is derivable at a
non-ground type), so the groundness hypothesis of `not_implements_stable_of_isGround` is harmless. -/
theorem not_implements_stable_of_not_isGround (fund : Nat → Bool) (I : ImplSet)
    (trs ctors : List Nat) (B : Nat) {X : Term} (hng : ¬ IsGround X) :
    StableUnderDownstream fund I trs ctors (fun I' => ¬ Implements I' B X) :=
  fun _ _ _ _ _ _ h => hng h.isGround

/-- Which pairs a fresh crate can address directly: if crate `c` owns neither `B` nor any
constructor of `X`, and owns at least one constructor `L`, then some impl of `B` that `c` may
write under the orphan rule has a self type sharing a ground instance with `X` iff
`fundSpineVar o X`. -/
theorem exists_orphanOK_overlapping_impl_iff_fundSpineVar (o : Owners) (c B L : Nat) (X : Term)
    (hB : o.traitOwner B ≠ c) (hX : ∀ f ∈ X.ctors, o.ctorOwner f ≠ c) (hL : o.ctorOwner L = c) :
    (∃ e : Impl, OrphanOK o c e ∧ e.trait = B ∧ CommonGroundInstance e.selfTy X) ↔
      fundSpineVar o X = true := by
  constructor
  · rintro ⟨e, horph, htr, θ₁, θ₂, _, heq⟩
    subst htr
    rcases horph with hbo | hloc
    · exact absurd hbo hB
    · have hloc' := isLocalTy_subst o c θ₁ e.selfTy hloc
      rw [heq] at hloc'
      exact fundSpineVar_of_isLocalTy_subst o c θ₂ X hX hloc'
  · intro hf
    let θ := groundAllTo (.con L []) X.vars
    refine ⟨⟨B, subst θ X, []⟩, ?_, rfl, [], θ, ?_, ?_⟩
    · exact Or.inr (isLocalTy_subst_groundAllTo o c L hL X.vars X (fun _ h => h) hf)
    · rw [subst_nil]
      exact vars_subst_groundAllTo_nil rfl X.vars X (fun _ h => h)
    · exact subst_nil _

/-- Stability of negative reasoning over an open type off the fundamental spine: if no impl of `B`
in `I` has a self type sharing a ground instance with `X`, and following first arguments through
the fundamental constructors of `o₀` from the root of `X` does not reach a variable, then the
statement "no ground instance of `X` implements `B`" is stable relative to the fundamental
constructors of `o₀`, the query trait `B` and the constructors of `X`. -/
theorem noInstanceImplements_stable_of_not_fundSpineVar (o₀ : Owners) (I : ImplSet) (B : Nat)
    (X : Term) (hI : ∀ i ∈ I, i.trait = B → ¬ CommonGroundInstance i.selfTy X)
    (hspine : fundSpineVar o₀ X = false) :
    StableUnderDownstream o₀.fundamental I [B] X.ctors
      (fun I' => NoInstanceImplements I' B X) := by
  intro o c E hfund ⟨_, htrs, hcts⟩ hE θ himp
  obtain ⟨i, θ', hi, htr, hself, hg, _⟩ := himp.inv
  rcases List.mem_append.1 hi with hiI | hiE
  · exact hI i hiI htr ⟨θ', θ, hself ▸ hg, hself⟩
  · rcases hE i hiE with hown | hloc
    · exact htrs B (List.mem_singleton_self B) (htr ▸ hown)
    · have hloc' := isLocalTy_subst o c θ' i.selfTy hloc
      rw [hself] at hloc'
      have hsp := fundSpineVar_of_isLocalTy_subst o c θ X hcts hloc'
      rw [fundSpineVar_congr (o' := o₀) hfund, hspine] at hsp
      exact Bool.false_ne_true hsp

/-! ## Non-vacuity -/

/-- Hypotheses of `implements_append_iff_of_orphanOK` (and, with `¬ Implements I_AB 12 u8`, of
`not_implements_append_of_orphanOK` and `not_implements_stable_of_isGround`) hold together:
`I_AB`, crate 2, `E = [impl A for L, impl B for L]`, `B` (12), the ground type `X = u8`. -/
theorem implements_append_iff_of_orphanOK_nonvacuous :
    IsGround u8 ∧ Constrained I_AB ∧ FreshCrate ownersEx 2 I_AB ∧ ownersEx.traitOwner 12 ≠ 2 ∧
      (∀ f ∈ u8.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([⟨11, localL, []⟩, ⟨12, localL, []⟩] : ImplSet), OrphanOK ownersEx 2 e) ∧
      ¬ Implements I_AB 12 u8 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  rw [implements_I_AB_B_iff]
  decide

/-- Hypotheses of `exists_orphanOK_overlapping_impl_iff_fundSpineVar` hold for `ownersEx`,
crate 2, `B`, `L`, and `X = Box T` (where the criterion holds) and `X = Vec T` (where it fails). -/
theorem exists_orphanOK_overlapping_impl_iff_fundSpineVar_nonvacuous :
    ownersEx.traitOwner 12 ≠ 2 ∧ (∀ f ∈ (box (.var 0)).ctors, ownersEx.ctorOwner f ≠ 2) ∧
      (∀ f ∈ (vec (.var 0)).ctors, ownersEx.ctorOwner f ≠ 2) ∧ ownersEx.ctorOwner 7 = 2 := by
  decide

/-! ## Tightness counterexamples for `implements_append_iff_of_orphanOK` -/

/-- Without `hneg`, `not_implements_append_of_orphanOK`'s conclusion fails (instance: a one-impl
set and the empty extension): with `I = {impl B for u8}`, crate 2 and `E = []`, all other
hypotheses hold and `u8: B` is derivable from `I ++ E`. -/
theorem not_implements_append_needs_neg :
    IsGround u8 ∧ Constrained [⟨12, u8, []⟩] ∧ FreshCrate ownersEx 2 [⟨12, u8, []⟩] ∧
      ownersEx.traitOwner 12 ≠ 2 ∧ (∀ f ∈ u8.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([] : ImplSet), OrphanOK ownersEx 2 e) ∧
      Implements ([⟨12, u8, []⟩] ++ []) 12 u8 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact implements_of_mem_of_bounds_nil (i := ⟨12, u8, []⟩) (by simp) rfl (by decide)

/-- Non-vacuity for `not_implements_stable_of_isGround`: `u8` is ground, `I_AB` is constrained,
and `u8: B` is not derivable in `I_AB`. -/
theorem not_implements_stable_of_isGround_nonvacuous :
    IsGround u8 ∧ Constrained I_AB ∧ ¬ Implements I_AB 12 u8 :=
  ⟨implements_append_iff_of_orphanOK_nonvacuous.1, implements_append_iff_of_orphanOK_nonvacuous.2.1,
    implements_append_iff_of_orphanOK_nonvacuous.2.2.2.2.2.2⟩

/-- Without `hneg`, the conclusion of `not_implements_stable_of_isGround` fails (instance: a
one-impl set): `u8: B` already holds in `{impl B for u8}`, so its negation is not stable. -/
theorem not_implements_stable_needs_neg :
    IsGround u8 ∧ Constrained [⟨12, u8, []⟩] ∧ Implements [⟨12, u8, []⟩] 12 u8 ∧
      ¬ StableUnderDownstream ownersEx.fundamental [⟨12, u8, []⟩] [12] u8.ctors
          (fun I' => ¬ Implements I' 12 u8) := by
  have h : Implements [⟨12, u8, []⟩] 12 u8 :=
    implements_of_mem_of_bounds_nil (i := ⟨12, u8, []⟩) (by simp) rfl (by decide)
  exact ⟨by decide, by decide, h, fun hst => hst.self h⟩

/-- `impl<U: C> B for u8`: the where-clause variable `U` is unconstrained. -/
def I_unconstrained : ImplSet := [⟨12, u8, [⟨13, .var 0⟩]⟩]

/-- Without `hcons` (instance: one impl with an unconstrained where-clause variable, and a
one-impl extension): the fresh crate 2 supplies the witness `impl C for L`, after which `u8: B`
is derivable. -/
theorem implements_append_iff_needs_constrained :
    IsGround u8 ∧ ¬ Constrained I_unconstrained ∧ FreshCrate ownersEx 2 I_unconstrained ∧
      ownersEx.traitOwner 12 ≠ 2 ∧ (∀ f ∈ u8.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([⟨13, localL, []⟩] : ImplSet), OrphanOK ownersEx 2 e) ∧
      Implements (I_unconstrained ++ [⟨13, localL, []⟩]) 12 u8 ∧
      ¬ Implements I_unconstrained 12 u8 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · have h := Implements.intro (I := I_unconstrained ++ [⟨13, localL, []⟩]) ⟨12, u8, [⟨13, .var 0⟩]⟩
      [(0, localL)] (by simp [I_unconstrained]) (by decide) (by
        intro b hb
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        subst hb
        exact implements_of_mem_of_bounds_nil (i := ⟨13, localL, []⟩) (by simp) rfl (by decide))
    exact h
  · intro h
    obtain ⟨i, θ, hi, _, _, _, hb⟩ := h.inv
    simp only [I_unconstrained, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi
    have hC := hb ⟨13, .var 0⟩ (by simp)
    obtain ⟨i', _, hi', htr', _⟩ := hC.inv
    simp only [I_unconstrained, List.mem_cons, List.mem_nil_iff, or_false] at hi'
    subst hi'
    simp at htr'

/-- Without `hcons`, the conclusion of `not_implements_stable_of_isGround` fails (instance: one
impl with an unconstrained where-clause variable): `u8: B` is not derivable from
`I_unconstrained`, but crate 2 (fresh for it, for `B` and for `u8`) adds `impl C for L`. -/
theorem not_implements_stable_needs_constrained :
    IsGround u8 ∧ ¬ Constrained I_unconstrained ∧ ¬ Implements I_unconstrained 12 u8 ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_unconstrained [12] u8.ctors
          (fun I' => ¬ Implements I' 12 u8) := by
  obtain ⟨hg, hnc, _, _, _, horph, hyes, hno⟩ := implements_append_iff_needs_constrained
  refine ⟨hg, hnc, hno, fun hst => hst ownersEx 2 _ rfl (by decide) horph hyes⟩

/-- Ownership where crate 2 owns the trait `C` (13). -/
def ownersC : Owners :=
  { traitOwner := fun tr => if tr = 13 then 2 else 1, ctorOwner := fun f => if f = 7 then 2 else 0,
    fundamental := fun f => f == 2 }

/-- `impl<T: C> B for Vec<T>`. -/
def I_vecC : ImplSet := [⟨12, vec (.var 0), [⟨13, .var 0⟩]⟩]

/-- Without `hfresh` (instance: a one-impl set whose where-clause trait `C` is owned by the
extending crate): crate 2 adds `impl C for u8`, after which `Vec<u8>: B` is derivable. -/
theorem implements_append_iff_needs_fresh :
    IsGround (vec u8) ∧ Constrained I_vecC ∧ ¬ FreshCrate ownersC 2 I_vecC ∧
      ownersC.traitOwner 12 ≠ 2 ∧
      (∀ f ∈ (vec u8).ctors, ownersC.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([⟨13, u8, []⟩] : ImplSet), OrphanOK ownersC 2 e) ∧
      Implements (I_vecC ++ [⟨13, u8, []⟩]) 12 (vec u8) ∧ ¬ Implements I_vecC 12 (vec u8) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · have h := Implements.intro (I := I_vecC ++ [⟨13, u8, []⟩]) ⟨12, vec (.var 0), [⟨13, .var 0⟩]⟩
      [(0, u8)] (by simp [I_vecC]) (by decide) (by
        intro b hb
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        subst hb
        exact implements_of_mem_of_bounds_nil (i := ⟨13, u8, []⟩) (by simp) rfl (by decide))
    exact h
  · intro h
    obtain ⟨i, θ, hi, _, _, _, hb⟩ := h.inv
    simp only [I_vecC, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi
    have hC := hb ⟨13, .var 0⟩ (by simp)
    obtain ⟨i', _, hi', htr', _⟩ := hC.inv
    simp only [I_vecC, List.mem_cons, List.mem_nil_iff, or_false] at hi'
    subst hi'
    simp at htr'

/-- Ownership where crate 2 owns the trait `B` (12). -/
def ownersB : Owners :=
  { traitOwner := fun tr => if tr = 12 then 2 else 1, ctorOwner := fun f => if f = 7 then 2 else 0,
    fundamental := fun f => f == 2 }

/-- Without `hB` (instance: the empty impl set and a one-impl extension): crate 2 owns `B` and
writes `impl B for u8`. -/
theorem implements_append_iff_needs_trait_not_owned :
    IsGround u8 ∧ Constrained [] ∧ FreshCrate ownersB 2 [] ∧ ownersB.traitOwner 12 = 2 ∧
      (∀ f ∈ u8.ctors, ownersB.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([⟨12, u8, []⟩] : ImplSet), OrphanOK ownersB 2 e) ∧
      Implements ([] ++ [⟨12, u8, []⟩]) 12 u8 ∧ ¬ Implements [] 12 u8 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact implements_of_mem_of_bounds_nil (i := ⟨12, u8, []⟩) (by simp) rfl (by decide)
  · intro h
    obtain ⟨_, _, hi, _⟩ := h.inv
    simp at hi

/-- Without `hX` (instance: the empty impl set and a one-impl extension): `X = L` is owned by
crate 2, which writes `impl B for L`. -/
theorem implements_append_iff_needs_ctors_not_owned :
    IsGround localL ∧ Constrained [] ∧ FreshCrate ownersEx 2 [] ∧ ownersEx.traitOwner 12 ≠ 2 ∧
      ¬ (∀ f ∈ localL.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      (∀ e ∈ ([⟨12, localL, []⟩] : ImplSet), OrphanOK ownersEx 2 e) ∧
      Implements ([] ++ [⟨12, localL, []⟩]) 12 localL ∧ ¬ Implements [] 12 localL := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact implements_of_mem_of_bounds_nil (i := ⟨12, localL, []⟩) (by simp) rfl (by decide)
  · intro h
    obtain ⟨_, _, hi, _⟩ := h.inv
    simp at hi

/-- Without `hE` (instance: the empty impl set and a one-impl extension): the orphan-disallowed
`impl B for u8` makes `u8: B` derivable. -/
theorem implements_append_iff_needs_orphanOK :
    IsGround u8 ∧ Constrained [] ∧ FreshCrate ownersEx 2 [] ∧ ownersEx.traitOwner 12 ≠ 2 ∧
      (∀ f ∈ u8.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      ¬ (∀ e ∈ ([⟨12, u8, []⟩] : ImplSet), OrphanOK ownersEx 2 e) ∧
      Implements ([] ++ [⟨12, u8, []⟩]) 12 u8 ∧ ¬ Implements [] 12 u8 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact implements_of_mem_of_bounds_nil (i := ⟨12, u8, []⟩) (by simp) rfl (by decide)
  · intro h
    obtain ⟨_, _, hi, _⟩ := h.inv
    simp at hi

/-! ## Tightness counterexamples for `exists_orphanOK_overlapping_impl_iff_fundSpineVar` -/

/-- Without `hL`: crate 3 owns nothing in `ownersEx`; `X = T` satisfies the criterion, but no
impl of `B` is orphan-allowed for crate 3. -/
theorem exists_orphanOK_iff_needs_local_ctor :
    (∀ L, ownersEx.ctorOwner L ≠ 3) ∧ ownersEx.traitOwner 12 ≠ 3 ∧
      (∀ f ∈ (Term.var 0).ctors, ownersEx.ctorOwner f ≠ 3) ∧
      fundSpineVar ownersEx (.var 0) = true ∧
      ¬ (∃ e : Impl, OrphanOK ownersEx 3 e ∧ e.trait = 12 ∧ CommonGroundInstance e.selfTy (.var 0)) := by
  refine ⟨fun L => by simp only [ownersEx]; split <;> decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨e, he, htr, _⟩
  rcases he with h | h
  · simp [ownersEx] at h
  · obtain ⟨f, _, hf⟩ := isLocalTy_ctor_owned ownersEx 3 e.selfTy h
    revert hf
    simp only [ownersEx]
    split <;> decide

/-- Without `hB`: if crate 2 owns `B`, it may write `impl<T> B for T`, which overlaps `u8`,
although `u8` fails the criterion. -/
theorem exists_orphanOK_iff_needs_trait_not_owned :
    ownersB.traitOwner 12 = 2 ∧ (∀ f ∈ u8.ctors, ownersB.ctorOwner f ≠ 2) ∧
      ownersB.ctorOwner 7 = 2 ∧ fundSpineVar ownersB u8 = false ∧
      (∃ e : Impl, OrphanOK ownersB 2 e ∧ e.trait = 12 ∧ CommonGroundInstance e.selfTy u8) :=
  ⟨by decide, by decide, by decide, by decide,
    ⟨⟨12, .var 0, []⟩, by decide, rfl, [(0, u8)], [], by decide, by decide⟩⟩

/-- Without `hX`: `X = L` is owned by crate 2, which may write `impl B for L`, although `L` fails
the criterion. -/
theorem exists_orphanOK_iff_needs_ctors_not_owned :
    ownersEx.traitOwner 12 ≠ 2 ∧ ¬ (∀ f ∈ localL.ctors, ownersEx.ctorOwner f ≠ 2) ∧
      ownersEx.ctorOwner 7 = 2 ∧ fundSpineVar ownersEx localL = false ∧
      (∃ e : Impl, OrphanOK ownersEx 2 e ∧ e.trait = 12 ∧ CommonGroundInstance e.selfTy localL) :=
  ⟨by decide, by decide, by decide, by decide,
    ⟨⟨12, localL, []⟩, by decide, rfl, [], [], by decide, by decide⟩⟩

/-! ## Instability of negative reasoning with where-clauses -/

/-- `impl C for L` (crate 2). -/
def E_C : ImplSet := [⟨13, localL, []⟩]

/-- Negative reasoning over the open, non-fundamental foreign type `Vec<T>` is unstable even
though no orphan-allowed impl can target it directly: in `I_vecC = {impl<T: C> B for Vec<T>}` no
instance of `Vec<T>` implements `B`; no impl of `B` that crate 2 may write has a self type sharing
a ground instance with `Vec<T>`; yet crate 2 (fresh for `I_vecC`, `B` and `Vec`) may add
`impl C for L`, after which `Vec<L>: B`. -/
theorem noInstanceImplements_vec_not_stable :
    ownersEx.fundamental 3 = false ∧ fundSpineVar ownersEx (vec (.var 0)) = false ∧
      NoInstanceImplements I_vecC 12 (vec (.var 0)) ∧
      (¬ ∃ e : Impl, OrphanOK ownersEx 2 e ∧ e.trait = 12 ∧
        CommonGroundInstance e.selfTy (vec (.var 0))) ∧
      FreshFor ownersEx 2 I_vecC [12] (vec (.var 0)).ctors ∧
      (∀ e ∈ E_C, OrphanOK ownersEx 2 e) ∧ Implements (I_vecC ++ E_C) 12 (vec localL) ∧
      ¬ NoInstanceImplements (I_vecC ++ E_C) 12 (vec (.var 0)) ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_vecC [12] (vec (.var 0)).ctors
          (fun I' => NoInstanceImplements I' 12 (vec (.var 0))) := by
  have hC : Implements (I_vecC ++ E_C) 13 localL :=
    implements_of_mem_of_bounds_nil (i := ⟨13, localL, []⟩) (by simp [E_C]) rfl (by decide)
  have hVL : Implements (I_vecC ++ E_C) 12 (vec localL) := by
    have := Implements.intro (I := I_vecC ++ E_C) ⟨12, vec (.var 0), [⟨13, .var 0⟩]⟩ [(0, localL)]
      (by simp [I_vecC]) (by decide) (by
        intro b hb
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        subst hb
        exact hC)
    exact this
  have hnot : ¬ NoInstanceImplements (I_vecC ++ E_C) 12 (vec (.var 0)) :=
    fun h => h [(0, localL)] hVL
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide, hVL, hnot, ?_⟩
  · intro θ h
    obtain ⟨i, θ', hi, _, _, _, hb⟩ := h.inv
    simp only [I_vecC, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi
    have hC' := hb ⟨13, .var 0⟩ (by simp)
    obtain ⟨i', _, hi', htr', _⟩ := hC'.inv
    simp only [I_vecC, List.mem_cons, List.mem_nil_iff, or_false] at hi'
    subst hi'
    simp at htr'
  · intro h
    have := (exists_orphanOK_overlapping_impl_iff_fundSpineVar ownersEx 2 12 7 (vec (.var 0))
      (by decide) (by decide) (by decide)).1 h
    exact absurd this (by decide)
  · intro hst
    exact hnot (hst ownersEx 2 E_C rfl (by decide) (by decide))

/-! ## Witnesses for `noInstanceImplements_stable_of_not_fundSpineVar` -/

/-- Non-vacuity for `noInstanceImplements_stable_of_not_fundSpineVar`: the one impl of `B` in
`I_AB` is `impl B for u32`, whose self type shares no ground instance with `Vec<T>`, and the
fundamental spine of `Vec<T>` under `ownersEx` (`Vec` not fundamental) does not end in a variable. -/
theorem noInstanceImplements_stable_of_not_fundSpineVar_nonvacuous :
    (∀ i ∈ I_AB, i.trait = 12 → ¬ CommonGroundInstance i.selfTy (vec (.var 0))) ∧
      fundSpineVar ownersEx (vec (.var 0)) = false := by
  refine ⟨?_, by decide⟩
  intro i hi htr ⟨θ₁, θ₂, _, h⟩
  simp only [I_AB, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simp [implA_u8] at htr
  · simp [implB_u32, u32, vec, subst_con] at h
  · simp [i1] at htr
  · simp [i2] at htr

/-- The resulting instance: "no ground instance of `Vec<T>` implements `B`" is stable for `I_AB`
relative to `ownersEx.fundamental`. -/
theorem noInstanceImplements_vec_stable_example :
    NoInstanceImplements I_AB 12 (vec (.var 0)) ∧
      StableUnderDownstream ownersEx.fundamental I_AB [12] (vec (.var 0)).ctors
        (fun I' => NoInstanceImplements I' 12 (vec (.var 0))) :=
  have h := noInstanceImplements_stable_of_not_fundSpineVar ownersEx I_AB 12 (vec (.var 0))
    noInstanceImplements_stable_of_not_fundSpineVar_nonvacuous.1
    noInstanceImplements_stable_of_not_fundSpineVar_nonvacuous.2
  ⟨h.self, h⟩

/-- Without `hI` (instance: the one-impl set `I_vecC = {impl<T: C> B for Vec<T>}` and the open
type `Vec<T>` under `ownersEx`): the spine condition holds, the impl of `B` for `Vec<T>` shares the
ground instance `Vec<u8>` with `Vec<T>`, and the conclusion fails (crate 2 adds `impl C for L`). -/
theorem noInstanceImplements_stable_needs_no_matching_impl :
    fundSpineVar ownersEx (vec (.var 0)) = false ∧
      ¬ (∀ i ∈ I_vecC, i.trait = 12 → ¬ CommonGroundInstance i.selfTy (vec (.var 0))) ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_vecC [12] (vec (.var 0)).ctors
          (fun I' => NoInstanceImplements I' 12 (vec (.var 0))) := by
  refine ⟨by decide, fun h => ?_, noInstanceImplements_vec_not_stable.2.2.2.2.2.2.2.2⟩
  exact h ⟨12, vec (.var 0), [⟨13, .var 0⟩]⟩ (by simp [I_vecC]) rfl
    ⟨[(0, u8)], [(0, u8)], by decide, rfl⟩

/-- Without `hspine` (instance: the empty impl set and the open type `Box<T>` under `ownersEx`,
`Box` fundamental): no impl of `B` exists, the fundamental spine of `Box<T>` ends in a variable,
and the conclusion fails (crate 2 adds `impl B for Box<L>`). -/
theorem noInstanceImplements_stable_needs_not_fundSpineVar :
    (∀ i ∈ ([] : ImplSet), i.trait = 12 → ¬ CommonGroundInstance i.selfTy (box (.var 0))) ∧
      fundSpineVar ownersEx (box (.var 0)) = true ∧
      NoInstanceImplements [] 12 (box (.var 0)) ∧
      ¬ StableUnderDownstream ownersEx.fundamental [] [12] (box (.var 0)).ctors
          (fun I' => NoInstanceImplements I' 12 (box (.var 0))) := by
  refine ⟨nofun, by decide, fun θ h => ?_, fun hst => ?_⟩
  · obtain ⟨_, _, hi, _⟩ := h.inv
    simp at hi
  · have himp : Implements ([] ++ [⟨12, box localL, []⟩]) 12 (box localL) :=
      implements_of_mem_of_bounds_nil (i := ⟨12, box localL, []⟩) (by simp) rfl (by decide)
    exact hst ownersEx 2 [⟨12, box localL, []⟩] rfl (by decide) (by decide) [(0, localL)] himp

/-- `ownersEx` with every constructor fundamental. -/
def ownersAllFund : Owners := { ownersEx with fundamental := fun _ => true }

/-- The verdict depends on which constructors are fundamental (a second instance without
`hspine`): with every constructor fundamental (`ownersAllFund`), "no ground instance of `Vec<T>`
implements `B`" is not stable even for the empty impl set (crate 2 adds `impl B for Vec<L>`). -/
theorem noInstanceImplements_vec_not_stable_of_vec_fundamental :
    (∀ i ∈ ([] : ImplSet), i.trait = 12 → ¬ CommonGroundInstance i.selfTy (vec (.var 0))) ∧
      fundSpineVar ownersAllFund (vec (.var 0)) = true ∧
      NoInstanceImplements [] 12 (vec (.var 0)) ∧
      ¬ StableUnderDownstream ownersAllFund.fundamental [] [12] (vec (.var 0)).ctors
          (fun I' => NoInstanceImplements I' 12 (vec (.var 0))) := by
  refine ⟨nofun, by decide, fun θ h => ?_, fun hst => ?_⟩
  · obtain ⟨_, _, hi, _⟩ := h.inv
    simp at hi
  · have himp : Implements ([] ++ [⟨12, vec localL, []⟩]) 12 (vec localL) :=
      implements_of_mem_of_bounds_nil (i := ⟨12, vec localL, []⟩) (by simp) rfl (by decide)
    exact hst ownersAllFund 2 [⟨12, vec localL, []⟩] rfl (by decide) (by decide) [(0, localL)] himp

/-- `impl A for L` and `impl B for L` (crate 2). -/
def E_AB : ImplSet := [⟨11, localL, []⟩, ⟨12, localL, []⟩]

/-- Where-clause-based non-overlap is not stable: `impl<T: A> Tr for T` and `impl<U: B> Tr for U`
do not overlap in `I_AB`, but crate 2, fresh for `I_AB` and for the symbols of both impls, may add
`impl A for L` and `impl B for L`, after which they overlap at `L` (`T := L`, `U := L`, with
`L: A` and `L: B` derivable). -/
theorem whereClause_disjointness_not_stable :
    ¬ ImplsOverlapIn I_AB i1 i2 ∧
      FreshFor ownersEx 2 I_AB (i1.traits ++ i2.traits) (i1.ctors ++ i2.ctors) ∧
      (∀ e ∈ E_AB, OrphanOK ownersEx 2 e) ∧
      subst [(0, localL)] i1.selfTy = localL ∧ subst [(1, localL)] i2.selfTy = localL ∧
      Implements (I_AB ++ E_AB) 11 localL ∧ Implements (I_AB ++ E_AB) 12 localL ∧
      ImplsOverlapIn (I_AB ++ E_AB) i1 i2 ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_AB (i1.traits ++ i2.traits)
          (i1.ctors ++ i2.ctors) (fun I' => ¬ ImplsOverlapIn I' i1 i2) := by
  have hA : Implements (I_AB ++ E_AB) 11 localL :=
    implements_of_mem_of_bounds_nil (i := ⟨11, localL, []⟩) (by simp [E_AB]) rfl (by decide)
  have hB : Implements (I_AB ++ E_AB) 12 localL :=
    implements_of_mem_of_bounds_nil (i := ⟨12, localL, []⟩) (by simp [E_AB]) rfl (by decide)
  have hov : ImplsOverlapIn (I_AB ++ E_AB) i1 i2 := by
    refine ⟨rfl, [(0, localL)], [(1, localL)], by decide, by decide, ?_, ?_⟩
    · intro b hb
      simp only [i1, List.mem_cons, List.mem_nil_iff, or_false] at hb
      subst hb
      exact hA
    · intro b hb
      simp only [i2, List.mem_cons, List.mem_nil_iff, or_false] at hb
      subst hb
      exact hB
  refine ⟨headersOverlap_not_implsOverlapIn.2.2.2.2, by decide, by decide, by decide, by decide,
    hA, hB, hov, ?_⟩
  intro hst
  exact hst ownersEx 2 E_AB rfl (by decide) (by decide) hov

/-- Counterexample for `h` in `not_headersOverlap_of_overlapCheckSaysDisjoint`,
`not_implsOverlapIn_of_overlapCheckSaysDisjoint` and `overlapCheckSaysDisjoint_stable`
(instance: two one-bound blanket impls with renamed-apart self types): the self types of `i1`,
`i2` are renamed apart, the checker does not say disjoint, the headers overlap, the impls overlap
in `I_AB ++ E_AB`, and non-overlap is not stable for `I_AB`. -/
theorem overlapCheckSaysDisjoint_needs_verdict :
    VarsDisjoint i1.selfTy i2.selfTy ∧ overlapCheckSaysDisjoint i1 i2 = false ∧
      HeadersOverlap i1 i2 ∧ ImplsOverlapIn (I_AB ++ E_AB) i1 i2 ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_AB (i1.traits ++ i2.traits)
          (i1.ctors ++ i2.ctors) (fun I' => ¬ ImplsOverlapIn I' i1 i2) :=
  ⟨by decide, by decide, headersOverlap_example, whereClause_disjointness_not_stable.2.2.2.2.2.2.2.1,
    whereClause_disjointness_not_stable.2.2.2.2.2.2.2.2⟩

/-- Counterexample for `hdisj` in `overlapCheckSaysDisjoint_stable` (instance: two impls of one
trait without where-clauses whose self types share the variable name `T`): the checker says
disjoint, yet the impls overlap in every impl set, so non-overlap is not stable. -/
theorem overlapCheckSaysDisjoint_stable_needs_renaming_apart :
    ¬ VarsDisjoint iShared1.selfTy iShared2.selfTy ∧
      overlapCheckSaysDisjoint iShared1 iShared2 = true ∧
      ¬ StableUnderDownstream ownersEx.fundamental I_AB [] []
          (fun I' => ¬ ImplsOverlapIn I' iShared1 iShared2) := by
  refine ⟨by decide, by decide, ?_⟩
  intro hst
  exact hst.self (overlapCheck_needs_renaming_apart.2.2.2.1 I_AB)

/-! ## The orphan rule has no covered-parameter check -/

/-- An upstream non-blanket impl `impl<T> B for Box<T, u8>` (written with the fundamental `Box`
applied to two arguments; `Term` has no arity discipline).
-/
def iUpBox2 : Impl := ⟨12, .con 2 [.var 0, u8], []⟩
/-- A downstream impl `impl<A> B for Box<L, A>`, orphan-allowed for crate 2 because `isLocalTy`
inspects only the first argument of a fundamental constructor. -/
def eDownBox2 : Impl := ⟨12, .con 2 [localL, .var 1], []⟩

/-- `OrphanOK` does not prevent a fresh crate's impl from overlapping an upstream non-blanket
impl when a fundamental constructor is applied to two arguments: crate 2 is fresh for
`{iUpBox2}`, may write `eDownBox2`, and the two overlap at `Box<L, u8>`. (RFC 2451 requires every
type parameter before the local type to be covered; that check is not modeled.) -/
theorem orphanOK_uncovered_param_overlap_example :
    FreshCrate ownersEx 2 [iUpBox2] ∧ OrphanOK ownersEx 2 eDownBox2 ∧
      VarsDisjoint iUpBox2.selfTy eDownBox2.selfTy ∧
      subst [(0, localL)] iUpBox2.selfTy = .con 2 [localL, u8] ∧
      subst [(1, u8)] eDownBox2.selfTy = .con 2 [localL, u8] ∧
      ImplsOverlapIn [iUpBox2, eDownBox2] iUpBox2 eDownBox2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨rfl, [(0, localL)], [(1, u8)], by decide, by decide, ?_, ?_⟩ <;>
    (intro b hb; simp [iUpBox2, eDownBox2] at hb)

end Toy.Unify
