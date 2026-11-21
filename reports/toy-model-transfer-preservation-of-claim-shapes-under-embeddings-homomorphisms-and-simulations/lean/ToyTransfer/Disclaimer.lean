import ToyTransfer.Matrix

/-!
# What a model result licenses when no relation, or only a map kind, is known

* No relation: a model `T` drawn from a class `KM` and a system `R` drawn from a class
  `KS`, with no map between them. Each of the statements "for every model `T` of `KM` and
  every system `R` of `KS`, if `φ` holds in `T` then `φ` holds in `R`" (truth), "..., if
  `φ` fails in `T` then `φ` fails in `R`" (falsity) and "..., if `φ` holds in `T` then `φ`
  fails in `R`" (refutation) is true exactly when the model class or the system class
  settles `φ`: for truth, when `φ` is unsatisfiable in `KM` or valid in `KS`; for falsity,
  when `φ` is valid in `KM` or unsatisfiable in `KS`; for refutation, when `φ` is
  unsatisfiable in `KM` or unsatisfiable in `KS`.
* Unlicensed matrix cells: a cell of the transfer table is unlicensed exactly when, for
  some formula of the class and some fact at the known end, maps of the given kind that are not
  isomorphisms lead to both outcomes (`bothOutcomesNonIso_iff_unlicensed`). This does not
  mean that nothing transfers: falsity can transfer in an unlicensed truth cell, and
  proper subclasses can transfer.
* Exact licences: for each map kind and orientation, the exact list of classes whose
  model-side truth, or model-side falsity, is licensed for the system.
-/

namespace Toy.Transfer

/-! ## No relation between model and system -/

/-- `φ` holds in every structure of the class `K`. -/
def ValidIn (K : Str → Prop) (φ : Fml 0) : Prop := ∀ M, K M → SatS M φ

/-- `φ` holds in no structure of the class `K`. -/
def UnsatIn (K : Str → Prop) (φ : Fml 0) : Prop := ∀ M, K M → ¬ SatS M φ

/-- **Truth transfer with no relation.** For classes `KM` (models) and `KS` (systems) and a
sentence `φ`, with no relation between model and system assumed: "for every model `T` of
`KM` and every system `R` of `KS`, if `φ` holds in `T` then `φ` holds in `R`" is true if
and only if `φ` is unsatisfiable in `KM` or valid in `KS`. The left-hand side says: for each
model `T` of `KM` in which `φ` holds, `φ` holds in every system of `KS`. -/
theorem unrelated_truth_transfer_iff (KM KS : Str → Prop) (φ : Fml 0) :
    (∀ T R, KM T → KS R → SatS T φ → SatS R φ) ↔ (UnsatIn KM φ ∨ ValidIn KS φ) := by
  constructor
  · intro h
    refine Classical.byCases (p := ∃ T, KM T ∧ SatS T φ) (fun ⟨T, hT, hTφ⟩ => ?_) (fun hn => ?_)
    · exact .inr (fun R hR => h T R hT hR hTφ)
    · exact .inl (fun M hM hMφ => hn ⟨M, hM, hMφ⟩)
  · rintro (hu | hv) T R hT hR hTφ
    · exact absurd hTφ (hu T hT)
    · exact hv R hR

/-- **Falsity transfer with no relation.** "For every model `T` of `KM` and every system `R`
of `KS`, if `φ` fails in `T` then `φ` fails in `R`" is true if and only if `φ` is valid in
`KM` or unsatisfiable in `KS`. -/
theorem unrelated_falsity_transfer_iff (KM KS : Str → Prop) (φ : Fml 0) :
    (∀ T R, KM T → KS R → ¬ SatS T φ → ¬ SatS R φ) ↔ (ValidIn KM φ ∨ UnsatIn KS φ) := by
  constructor
  · intro h
    refine Classical.byCases (p := ∃ T, KM T ∧ ¬ SatS T φ) (fun ⟨T, hT, hTφ⟩ => ?_) (fun hn => ?_)
    · exact .inr (fun R hR => h T R hT hR hTφ)
    · exact .inl (fun M hM => Classical.byContradiction (fun hMφ => hn ⟨M, hM, hMφ⟩))
  · rintro (hv | hu) T R hT hR hTφ
    · exact absurd (hv T hT) hTφ
    · exact hu R hR

/-- **Reading a model result as a refutation, with no relation.** "For every model `T` of
`KM` and every system `R` of `KS`, if `φ` holds in `T` then `φ` fails in `R`" is true if
and only if `φ` is unsatisfiable in `KM` (the premise never holds) or unsatisfiable in `KS`
(the conclusion holds regardless of the model). -/
theorem unrelated_refutation_licensed_iff (KM KS : Str → Prop) (φ : Fml 0) :
    (∀ T R, KM T → KS R → SatS T φ → ¬ SatS R φ) ↔ (UnsatIn KM φ ∨ UnsatIn KS φ) := by
  constructor
  · intro h
    refine Classical.byCases (p := ∃ T, KM T ∧ SatS T φ) (fun ⟨T, hT, hTφ⟩ => ?_) (fun hn => ?_)
    · exact .inr (fun R hR => h T R hT hR hTφ)
    · exact .inl (fun M hM hMφ => hn ⟨M, hM, hMφ⟩)
  · rintro (hu | hu) T R hT hR hTφ
    · exact absurd hTφ (hu T hT)
    · exact hu R hR

/-- Same-class special case of `unrelated_refutation_licensed_iff`: when models and systems
range over the same class `K` (a model may also be the system), "for every `T` and every
`R` of `K`, if `φ` holds in `T` then `φ` fails in `R`" is true if and only if `φ` is
unsatisfiable in `K`. -/
theorem unrelated_refutation_licensed_iff_unsat_same_class (K : Str → Prop) (φ : Fml 0) :
    (∀ T R, K T → K R → SatS T φ → ¬ SatS R φ) ↔ UnsatIn K φ :=
  (unrelated_refutation_licensed_iff K K φ).trans ⟨fun h => h.elim id id, .inl⟩

/-- **Consistency form.** If `φ` holds in some model of `KM`, and `KS` contains both a
system satisfying `φ` and one falsifying it, then one and the same model satisfying `φ`
is consistent with a system satisfying `φ` and with a system falsifying it. -/
theorem unrelated_model_result_consistent_with_both (KM KS : Str → Prop) (φ : Fml 0)
    (hsatM : ∃ T, KM T ∧ SatS T φ) (hsatS : ∃ R, KS R ∧ SatS R φ)
    (hnvS : ∃ R, KS R ∧ ¬ SatS R φ) :
    ∃ T, KM T ∧ SatS T φ ∧ (∃ R, KS R ∧ SatS R φ) ∧ (∃ R, KS R ∧ ¬ SatS R φ) := by
  obtain ⟨T, hT, hTφ⟩ := hsatM
  exact ⟨T, hT, hTφ, hsatS, hnvS⟩

/-! ## Unlicensed cells: both outcomes along maps that are not isomorphisms -/

/-- The cell `(c, k, d)` admits both outcomes along non-isomorphisms: there is a formula `φ`
of class `c` and a fact where `φ` holds at the known end, together with two `k`-maps,
neither an isomorphism, one where `φ` holds at the other end and one where it fails.
For `fwd` the known end is a source `A` with environment `e`, pushed to each target as
`h ∘ e`. For `bwd` the known end is a target `B` with environment `b`; each of the two maps
comes with a source environment `e` that it sends to `b` pointwise (`∀ i, h (e i) = b i`),
and `φ` is evaluated at that `e`. The two maps need not be distinct: one map with two
different source environments is allowed (as in `both_eq`). -/
def BothOutcomesNonIso (c : Cls) (k : MapKind) : Dir → Prop
  | .fwd => ∃ (A : Str) (n : Nat) (φ : Fml n) (e : Fin n → A.carrier), c.Mem φ ∧ Sat A φ e ∧
      (∃ (B : Str) (h : A.carrier → B.carrier), k.Holds h ∧ ¬ IsIso h ∧ Sat B φ (h ∘ e)) ∧
      (∃ (B : Str) (h : A.carrier → B.carrier), k.Holds h ∧ ¬ IsIso h ∧ ¬ Sat B φ (h ∘ e))
  | .bwd => ∃ (B : Str) (n : Nat) (φ : Fml n) (b : Fin n → B.carrier), c.Mem φ ∧ Sat B φ b ∧
      (∃ (A : Str) (h : A.carrier → B.carrier) (e : Fin n → A.carrier),
        k.Holds h ∧ ¬ IsIso h ∧ (∀ i, h (e i) = b i) ∧ Sat A φ e) ∧
      (∃ (A : Str) (h : A.carrier → B.carrier) (e : Fin n → A.carrier),
        k.Holds h ∧ ¬ IsIso h ∧ (∀ i, h (e i) = b i) ∧ ¬ Sat A φ e)

/-- A cell admitting both outcomes along non-isomorphisms does not transfer. -/
theorem not_preserves_of_bothOutcomesNonIso {c : Cls} {k : MapKind} {d : Dir}
    (hb : BothOutcomesNonIso c k d) : ¬ Preserves c k d := by
  cases d with
  | fwd =>
    obtain ⟨A, n, φ, e, hc, hA, -, B, h, hk, -, hB⟩ := hb
    exact not_preserves_fwd h hk φ hc e hA hB
  | bwd =>
    obtain ⟨B, n, φ, b, hc, hB, -, A, h, e, hk, -, he, hA⟩ := hb
    have hb' : h ∘ e = b := funext he
    subst hb'
    exact not_preserves_bwd h hk φ hc e hB hA

theorem bothOutcomes_fwd_of {c : Cls} {k : MapKind} {A B₁ B₂ : Str} {n : Nat} (φ : Fml n)
    (e : Fin n → A.carrier) (h₁ : A.carrier → B₁.carrier) (h₂ : A.carrier → B₂.carrier)
    (hc : c.Mem φ) (hA : Sat A φ e)
    (hk₁ : k.Holds h₁) (hi₁ : ¬ IsIso h₁) (hB₁ : Sat B₁ φ (h₁ ∘ e))
    (hk₂ : k.Holds h₂) (hi₂ : ¬ IsIso h₂) (hB₂ : ¬ Sat B₂ φ (h₂ ∘ e)) :
    BothOutcomesNonIso c k .fwd :=
  ⟨A, n, φ, e, hc, hA, ⟨B₁, h₁, hk₁, hi₁, hB₁⟩, ⟨B₂, h₂, hk₂, hi₂, hB₂⟩⟩

theorem bothOutcomes_bwd_of {c : Cls} {k : MapKind} {B A₁ A₂ : Str} {n : Nat} (φ : Fml n)
    (b : Fin n → B.carrier) (h₁ : A₁.carrier → B.carrier) (e₁ : Fin n → A₁.carrier)
    (h₂ : A₂.carrier → B.carrier) (e₂ : Fin n → A₂.carrier) (hc : c.Mem φ) (hB : Sat B φ b)
    (hk₁ : k.Holds h₁) (hi₁ : ¬ IsIso h₁) (he₁ : ∀ i, h₁ (e₁ i) = b i) (hA₁ : Sat A₁ φ e₁)
    (hk₂ : k.Holds h₂) (hi₂ : ¬ IsIso h₂) (he₂ : ∀ i, h₂ (e₂ i) = b i) (hA₂ : ¬ Sat A₂ φ e₂) :
    BothOutcomesNonIso c k .bwd :=
  ⟨B, n, φ, b, hc, hB, ⟨A₁, h₁, e₁, hk₁, hi₁, he₁, hA₁⟩, ⟨A₂, h₂, e₂, hk₂, hi₂, he₂, hA₂⟩⟩

/-! ### Witnesses (all structures non-empty; every map is decided by evaluation) -/

/-- `∀x, P x` holds in `S1P`; it holds after the embedding `inclPP` into `S2PP` and fails
after the embedding `inclPN` into `S2PN`. -/
theorem both_allP {c : Cls} {k : MapKind} (hc : c.Mem allP) (hk₁ : k.Holds inclPP)
    (hk₂ : k.Holds inclPN) : BothOutcomesNonIso c k .fwd :=
  bothOutcomes_fwd_of allP Fin.elim0 inclPP inclPN hc (by decide) hk₁ (by decide) (by decide)
    hk₂ (by decide) (by decide)

/-- `∃x, ¬ P x` holds in `S1N`; it holds after the bijective homomorphism `raiseR` (which
does not reflect `R`) and fails after `raiseP`. -/
theorem both_exNotP {c : Cls} {k : MapKind} (hc : c.Mem exNotP) (hk₁ : k.Holds raiseR)
    (hk₂ : k.Holds raiseP) : BothOutcomesNonIso c k .fwd :=
  bothOutcomes_fwd_of exNotP Fin.elim0 raiseR raiseP hc (by decide) hk₁ (by decide) (by decide)
    hk₂ (by decide) (by decide)

/-- `∀x ∀y, R x y → x = y` holds in `S2E`; it holds after the non-injective `collapse` and
fails after `addEdge`. -/
theorem both_allRImpEq {c : Cls} {k : MapKind} (hc : c.Mem allRImpEq) (hk₁ : k.Holds collapse)
    (hk₂ : k.Holds addEdge) : BothOutcomesNonIso c k .fwd :=
  bothOutcomes_fwd_of allRImpEq Fin.elim0 collapse addEdge hc (by decide) hk₁ (by decide)
    (by decide) hk₂ (by decide) (by decide)

/-- `¬ P x₀` holds in `S1N` at `0`; it holds after `raiseR` and fails after `raiseP`. -/
theorem both_notP0 {c : Cls} {k : MapKind} (hc : c.Mem notP0) (hk₁ : k.Holds raiseR)
    (hk₂ : k.Holds raiseP) : BothOutcomesNonIso c k .fwd :=
  bothOutcomes_fwd_of (A := S1N.toStr) notP0 (env1 0) raiseR raiseP hc (by decide) hk₁ (by decide) (by decide)
    hk₂ (by decide) (by decide)

/-- `¬ x₀ = x₁` holds in `S2E` at `(0, 1)`; it holds after the non-surjective embedding
`inclE23` and fails after `collapse`. -/
theorem both_neq {c : Cls} {k : MapKind} (hc : c.Mem neq01) (hk₁ : k.Holds inclE23)
    (hk₂ : k.Holds collapse) : BothOutcomesNonIso c k .fwd :=
  bothOutcomes_fwd_of (A := S2E.toStr) neq01 (env2 0 1) inclE23 collapse hc (by decide) hk₁ (by decide)
    (by decide) hk₂ (by decide) (by decide)

/-- `∃x ∃y, ¬ x = y` holds in `S2E`; it holds after `inclE23` and fails after `collapse`. -/
theorem both_exExNeq {c : Cls} {k : MapKind} (hc : c.Mem exExNeq) (hk₁ : k.Holds inclE23)
    (hk₂ : k.Holds collapse) : BothOutcomesNonIso c k .fwd :=
  bothOutcomes_fwd_of exExNeq Fin.elim0 inclE23 collapse hc (by decide) hk₁ (by decide)
    (by decide) hk₂ (by decide) (by decide)

/-- `∃x, P x` holds in `S2NP`; it holds in `S1P`, embedded by `inclP1`, and fails in `S1N`,
embedded by `inclNP`. -/
theorem both_exP_sub {c : Cls} {k : MapKind} (hc : c.Mem exP) (hk₁ : k.Holds inclP1)
    (hk₂ : k.Holds inclNP) : BothOutcomesNonIso c k .bwd :=
  bothOutcomes_bwd_of exP Fin.elim0 inclP1 Fin.elim0 inclNP Fin.elim0 hc (by decide) hk₁
    (by decide) (by decide) (by decide) hk₂ (by decide) (by decide) (by decide)

/-- `∀x ∃y, R x y` holds in `S2Loop1`; it holds in `S1R`, embedded by `inclLoop`, and fails
in `S1N`, embedded by `inclNoLoop`. -/
theorem both_allExR {c : Cls} {k : MapKind} (hc : c.Mem allExR) (hk₁ : k.Holds inclLoop)
    (hk₂ : k.Holds inclNoLoop) : BothOutcomesNonIso c k .bwd :=
  bothOutcomes_bwd_of allExR Fin.elim0 inclLoop Fin.elim0 inclNoLoop Fin.elim0 hc (by decide)
    hk₁ (by decide) (by decide) (by decide) hk₂ (by decide) (by decide) (by decide)

/-- `x₀ = x₁` holds in `S1N` at `(0, 0)`; along `collapse` it holds in `S2E` at `(0, 0)` and
fails at `(0, 1)`. Both outcomes use the same map `collapse`, with the two source
environments `env2 0 0` and `env2 0 1`, each sent to `(0, 0)`. -/
theorem both_eq {c : Cls} {k : MapKind} (hc : c.Mem eq01) (hk₁ : k.Holds collapse)
    (hk₂ : k.Holds collapse) : BothOutcomesNonIso c k .bwd :=
  bothOutcomes_bwd_of (B := S1N.toStr) (A₁ := S2E.toStr) (A₂ := S2E.toStr) eq01
    (env2 0 0) collapse (env2 0 0) collapse (env2 0 1) hc (by decide)
    hk₁ (by decide) (by decide) (by decide) hk₂ (by decide) (by decide) (by decide)

/-- `∀x ∀y, x = y ∨ P x ∨ P y` holds in `S2PN`; it holds in `S1N`, embedded by `inclN1`, and
fails in `S2E`, mapped by the non-injective strong homomorphism `collapseTo1`. -/
theorem both_atMostOneNotP {c : Cls} {k : MapKind} (hc : c.Mem atMostOneNotP)
    (hk₁ : k.Holds inclN1) (hk₂ : k.Holds collapseTo1) : BothOutcomesNonIso c k .bwd :=
  bothOutcomes_bwd_of atMostOneNotP Fin.elim0 inclN1 Fin.elim0 collapseTo1 Fin.elim0 hc
    (by decide) hk₁ (by decide) (by decide) (by decide) hk₂ (by decide) (by decide) (by decide)

/-- `P x₀` holds in `S1P` at `0`; it holds in `S2NP` at `1` (mapped by `squashP`) and fails
in `S1N` at `0` (mapped by `raiseP`). -/
theorem both_P0 {c : Cls} {k : MapKind} (hc : c.Mem P0) (hk₁ : k.Holds squashP)
    (hk₂ : k.Holds raiseP) : BothOutcomesNonIso c k .bwd :=
  bothOutcomes_bwd_of (B := S1P.toStr) (A₁ := S2NP.toStr) (A₂ := S1N.toStr) P0
    (env1 0) squashP (env1 1) raiseP (env1 0) hc (by decide) hk₁
    (by decide) (by decide) (by decide) hk₂ (by decide) (by decide) (by decide)

/-- `∃x, P x` holds in `S1P`; it holds in `S2NP` (mapped by `squashP`) and fails in `S1N`
(mapped by `raiseP`). -/
theorem both_exP_surj {c : Cls} {k : MapKind} (hc : c.Mem exP) (hk₁ : k.Holds squashP)
    (hk₂ : k.Holds raiseP) : BothOutcomesNonIso c k .bwd :=
  bothOutcomes_bwd_of exP Fin.elim0 squashP Fin.elim0 raiseP Fin.elim0 hc (by decide) hk₁
    (by decide) (by decide) (by decide) hk₂ (by decide) (by decide) (by decide)

/-- `∀x, P x` holds in `S1P`; it holds in `S2PP` (mapped by `squashPP`) and fails in `S1N`
(mapped by `raiseP`). -/
theorem both_allP_surj {c : Cls} {k : MapKind} (hc : c.Mem allP) (hk₁ : k.Holds squashPP)
    (hk₂ : k.Holds raiseP) : BothOutcomesNonIso c k .bwd :=
  bothOutcomes_bwd_of allP Fin.elim0 squashPP Fin.elim0 raiseP Fin.elim0 hc (by decide) hk₁
    (by decide) (by decide) (by decide) hk₂ (by decide) (by decide) (by decide)

/-- Every unlicensed cell admits both outcomes along non-isomorphisms. One arm per cell. -/
theorem bothOutcomesNonIso_of_unlicensed : ∀ (c : Cls) (k : MapKind) (d : Dir),
    licensedB c k d = false → BothOutcomesNonIso c k d :=
  fun c k d => match c, k, d with
  -- qf
  | .qf, .hom, .fwd => fun _ => both_notP0 (by decide) (by decide) (by decide)
  | .qf, .hom, .bwd => fun _ => both_P0 (by decide) (by decide) (by decide)
  | .qf, .strong, .fwd => fun _ => both_neq (by decide) (by decide) (by decide)
  | .qf, .strong, .bwd => fun _ => both_eq (by decide) (by decide) (by decide)
  | .qf, .emb, .fwd => fun h => absurd h (by decide)
  | .qf, .emb, .bwd => fun h => absurd h (by decide)
  | .qf, .surj, .fwd => fun _ => both_notP0 (by decide) (by decide) (by decide)
  | .qf, .surj, .bwd => fun _ => both_P0 (by decide) (by decide) (by decide)
  -- univ
  | .univ, .hom, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .univ, .hom, .bwd => fun _ => both_atMostOneNotP (by decide) (by decide) (by decide)
  | .univ, .strong, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .univ, .strong, .bwd => fun _ => both_atMostOneNotP (by decide) (by decide) (by decide)
  | .univ, .emb, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .univ, .emb, .bwd => fun h => absurd h (by decide)
  | .univ, .surj, .fwd => fun _ => both_allRImpEq (by decide) (by decide) (by decide)
  | .univ, .surj, .bwd => fun _ => both_allP_surj (by decide) (by decide) (by decide)
  -- exist
  | .exist, .hom, .fwd => fun _ => both_exNotP (by decide) (by decide) (by decide)
  | .exist, .hom, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .exist, .strong, .fwd => fun _ => both_exExNeq (by decide) (by decide) (by decide)
  | .exist, .strong, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .exist, .emb, .fwd => fun h => absurd h (by decide)
  | .exist, .emb, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .exist, .surj, .fwd => fun _ => both_exNotP (by decide) (by decide) (by decide)
  | .exist, .surj, .bwd => fun _ => both_exP_surj (by decide) (by decide) (by decide)
  -- ae
  | .ae, .hom, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .ae, .hom, .bwd => fun _ => both_allExR (by decide) (by decide) (by decide)
  | .ae, .strong, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .ae, .strong, .bwd => fun _ => both_allExR (by decide) (by decide) (by decide)
  | .ae, .emb, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .ae, .emb, .bwd => fun _ => both_allExR (by decide) (by decide) (by decide)
  | .ae, .surj, .fwd => fun _ => both_allRImpEq (by decide) (by decide) (by decide)
  | .ae, .surj, .bwd => fun _ => both_allP_surj (by decide) (by decide) (by decide)
  -- ea
  | .ea, .hom, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .ea, .hom, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .ea, .strong, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .ea, .strong, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .ea, .emb, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .ea, .emb, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .ea, .surj, .fwd => fun _ => both_allRImpEq (by decide) (by decide) (by decide)
  | .ea, .surj, .bwd => fun _ => both_exP_surj (by decide) (by decide) (by decide)
  -- pos
  | .pos, .hom, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .pos, .hom, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .pos, .strong, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .pos, .strong, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .pos, .emb, .fwd => fun _ => both_allP (by decide) (by decide) (by decide)
  | .pos, .emb, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .pos, .surj, .fwd => fun h => absurd h (by decide)
  | .pos, .surj, .bwd => fun _ => both_exP_surj (by decide) (by decide) (by decide)
  -- posExist
  | .posExist, .hom, .fwd => fun h => absurd h (by decide)
  | .posExist, .hom, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .posExist, .strong, .fwd => fun h => absurd h (by decide)
  | .posExist, .strong, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .posExist, .emb, .fwd => fun h => absurd h (by decide)
  | .posExist, .emb, .bwd => fun _ => both_exP_sub (by decide) (by decide) (by decide)
  | .posExist, .surj, .fwd => fun h => absurd h (by decide)
  | .posExist, .surj, .bwd => fun _ => both_exP_surj (by decide) (by decide) (by decide)

/-- **Unlicensed cells admit both outcomes along non-isomorphisms.** For every class `c`,
map kind `k` and direction `d`: the cell admits both outcomes along maps of kind `k` that
are not isomorphisms (`BothOutcomesNonIso`) if and only if the transfer table marks it
unlicensed. -/
theorem bothOutcomesNonIso_iff_unlicensed (c : Cls) (k : MapKind) (d : Dir) :
    BothOutcomesNonIso c k d ↔ licensedB c k d = false := by
  refine ⟨fun hb => ?_, bothOutcomesNonIso_of_unlicensed c k d⟩
  cases hl : licensedB c k d with
  | false => rfl
  | true => exact absurd ((licensedB_iff c k d).1 hl) (not_preserves_of_bothOutcomesNonIso hb)

/-! ## The exact licences per map kind and orientation -/

/-- Which side of the map is the model. -/
inductive Orient where
  /-- `h : model → system` (e.g. the model embeds into the system). -/
  | modelToSystem
  /-- `h : system → model` (e.g. the system embeds into the model). -/
  | systemToModel
  deriving DecidableEq, Repr

/-- Truth of class-`c` formulas in the model is licensed for the system along every
`k`-map in orientation `o`, for formulas with parameters: the system-side environment is
`h ∘ e` (`modelToSystem`), or the model-side environment is the image `h ∘ e` of a
system environment `e` (`systemToModel`). -/
def TruthLicensed (c : Cls) (k : MapKind) : Orient → Prop
  | .modelToSystem => ∀ (M S : Str) (h : M.carrier → S.carrier), k.Holds h →
      ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → M.carrier, Sat M φ e → Sat S φ (h ∘ e)
  | .systemToModel => ∀ (S M : Str) (h : S.carrier → M.carrier), k.Holds h →
      ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → S.carrier, Sat M φ (h ∘ e) → Sat S φ e

/-- Falsity of class-`c` formulas in the model is licensed for the system along every
`k`-map in orientation `o` (formulas with parameters, as in `TruthLicensed`). -/
def FalsityLicensed (c : Cls) (k : MapKind) : Orient → Prop
  | .modelToSystem => ∀ (M S : Str) (h : M.carrier → S.carrier), k.Holds h →
      ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → M.carrier,
        ¬ Sat M φ e → ¬ Sat S φ (h ∘ e)
  | .systemToModel => ∀ (S M : Str) (h : S.carrier → M.carrier), k.Holds h →
      ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → S.carrier,
        ¬ Sat M φ (h ∘ e) → ¬ Sat S φ e

/-- The classes whose model-side truth is licensed, as an explicit list. -/
def truthList : MapKind → Orient → List Cls
  | .emb, .modelToSystem => [.qf, .exist, .posExist]
  | .strong, .modelToSystem => [.posExist]
  | .hom, .modelToSystem => [.posExist]
  | .surj, .modelToSystem => [.pos, .posExist]
  | .emb, .systemToModel => [.qf, .univ]
  | .strong, .systemToModel => []
  | .hom, .systemToModel => []
  | .surj, .systemToModel => []

/-- The classes whose model-side falsity is licensed, as an explicit list. -/
def falsityList : MapKind → Orient → List Cls
  | .emb, .modelToSystem => [.qf, .univ]
  | .strong, .modelToSystem => []
  | .hom, .modelToSystem => []
  | .surj, .modelToSystem => []
  | .emb, .systemToModel => [.qf, .exist, .posExist]
  | .strong, .systemToModel => [.posExist]
  | .hom, .systemToModel => [.posExist]
  | .surj, .systemToModel => [.pos, .posExist]

theorem truthLicensed_iff_preserves (c : Cls) (k : MapKind) (o : Orient) :
    TruthLicensed c k o ↔ Preserves c k (match o with | .modelToSystem => .fwd | .systemToModel => .bwd) := by
  cases o <;> exact Iff.rfl

theorem falsityLicensed_iff_preserves (c : Cls) (k : MapKind) (o : Orient) :
    FalsityLicensed c k o ↔ Preserves c k (match o with | .modelToSystem => .bwd | .systemToModel => .fwd) := by
  cases o with
  | modelToSystem =>
    constructor
    · intro h A B f hk n φ hc e hB
      exact Classical.byContradiction (fun hA => h A B f hk n φ hc e hA hB)
    · intro h A B f hk n φ hc e hA hB
      exact hA (h A B f hk n φ hc e hB)
  | systemToModel =>
    constructor
    · intro h A B f hk n φ hc e hA
      exact Classical.byContradiction (fun hB => h A B f hk n φ hc e hB hA)
    · intro h A B f hk n φ hc e hB hA
      exact hB (h A B f hk n φ hc e hA)

/-- **Exact licences.** For every map kind `k`, orientation `o` and class `c`: model-side
truth of class-`c` formulas (with parameters) is licensed for the system along every
`k`-map in orientation `o` exactly when `c ∈ truthList k o`, and model-side falsity
exactly when `c ∈ falsityList k o`. -/
theorem licences_exact (k : MapKind) (o : Orient) (c : Cls) :
    (TruthLicensed c k o ↔ c ∈ truthList k o) ∧ (FalsityLicensed c k o ↔ c ∈ falsityList k o) := by
  rw [truthLicensed_iff_preserves, falsityLicensed_iff_preserves, ← licensedB_iff, ← licensedB_iff]
  cases k <;> cases o <;> cases c <;> decide

/-! ## What an unlicensed truth cell does not rule out -/

/-- **Falsity can transfer where truth does not.** Model-side truth of class `c` is
unlicensed while model-side falsity is licensed exactly for these seven
(kind, orientation, class) triples. -/
theorem falsity_licensed_where_truth_unlicensed_iff (k : MapKind) (o : Orient) (c : Cls) :
    (¬ TruthLicensed c k o ∧ FalsityLicensed c k o) ↔
      (k, o, c) ∈ [(.emb, .modelToSystem, .univ), (.emb, .systemToModel, .exist),
        (.emb, .systemToModel, .posExist), (.strong, .systemToModel, .posExist),
        (.hom, .systemToModel, .posExist), (.surj, .systemToModel, .pos),
        (.surj, .systemToModel, .posExist)] := by
  rw [(licences_exact k o c).1, (licences_exact k o c).2]
  cases k <;> cases o <;> cases c <;> decide

/-- **Unlicensed cells can contain classes that transfer.** Each listed cell is unlicensed,
yet a proper subclass of its class transfers in that cell: quantifier-free ⊆ universal
(embeddings, forward), quantifier-free ⊆ existential (embeddings, backward),
existential ⊆ `∀∃` (embeddings, forward), universal ⊆ `∃∀` (embeddings, backward),
positive existential ⊆ positive (homomorphisms, forward). -/
theorem unlicensed_cells_contain_transferring_subclasses :
    (licensedB .univ .emb .fwd = false ∧ (∀ {n} (φ : Fml n), IsQF φ → IsUniv φ) ∧
      Preserves .qf .emb .fwd) ∧
    (licensedB .exist .emb .bwd = false ∧ (∀ {n} (φ : Fml n), IsQF φ → IsExist φ) ∧
      Preserves .qf .emb .bwd) ∧
    (licensedB .ae .emb .fwd = false ∧ (∀ {n} (φ : Fml n), IsExist φ → IsAE φ) ∧
      Preserves .exist .emb .fwd) ∧
    (licensedB .ea .emb .bwd = false ∧ (∀ {n} (φ : Fml n), IsUniv φ → IsEA φ) ∧
      Preserves .univ .emb .bwd) ∧
    (licensedB .pos .hom .fwd = false ∧ (∀ {n} (φ : Fml n), IsPosExist φ → IsPos φ) ∧
      Preserves .posExist .hom .fwd) := by
  have hpe : ∀ {n} (φ : Fml n), IsPosExist φ → IsPos φ := by
    intro n φ h
    induction h with
    | rel i j => exact .rel i j
    | pred i => exact .pred i
    | eq i j => exact .eq i j
    | and _ _ ih1 ih2 => exact .and ih1 ih2
    | or _ _ ih1 ih2 => exact .or ih1 ih2
    | ex _ ih => exact .ex ih
  exact ⟨⟨rfl, fun _ h => .qf h, preserves_qf_emb .fwd⟩, ⟨rfl, fun _ h => .qf h, preserves_qf_emb .bwd⟩,
    ⟨rfl, fun _ h => .exist h, preserves_exist_emb_fwd⟩, ⟨rfl, fun _ h => .univ h, preserves_univ_emb_bwd⟩,
    ⟨rfl, hpe, preserves_posExist_fwd .hom⟩⟩

end Toy.Transfer
