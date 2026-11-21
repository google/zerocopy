import ToyTransfer.Preservation
import ToyTransfer.FinModels

/-!
# Countermodels (all proved by evaluation)

Each theorem is in canonical form: a concrete instance (non-empty structures on at most two
elements, a map, a formula and an environment) satisfying the stated class
memberships and map laws, in which the transfer fails. The conjuncts list every law
that holds in the instance, so one instance can witness the tightness of several
hypotheses. Sentences use the empty environment `Fin.elim0`; the target side is
written `Sat B φ (h ∘ Fin.elim0)`, exactly as in the preservation theorems.
-/

namespace Toy.Transfer

/-! ## The five instances required by the transfer matrix -/

/-- `∀x, P x` is not preserved by extensions: it holds in the one-point structure
`S1P` and fails in its two-point extension `S2PN` along the embedding `inclPN`. -/
theorem allP_not_preserved_to_extension :
    IsUniv allP ∧ IsAE allP ∧ IsEA allP ∧ IsPos allP ∧ ¬ IsExist allP ∧ ¬ IsPosExist allP ∧
    IsEmbedding inclPN ∧ ¬ Function.Surjective inclPN ∧
    Sat S1P.toStr allP Fin.elim0 ∧ ¬ Sat S2PN.toStr allP (inclPN ∘ Fin.elim0) := by
  decide

/-- `∃x, P x` is not preserved by substructures: it holds in `S2NP` and fails in its
one-point substructure `S1N` (embedded by `inclNP`). -/
theorem exP_not_preserved_to_substructure :
    IsExist exP ∧ IsAE exP ∧ IsEA exP ∧ IsPos exP ∧ IsPosExist exP ∧ ¬ IsUniv exP ∧
    IsEmbedding inclNP ∧
    Sat S2NP.toStr exP (inclNP ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr exP Fin.elim0 := by
  decide

/-- `∀x ∃y, R x y` is not preserved by substructures: it holds in the 2-cycle `S2Cyc`
and fails in its one-point substructure `S1N` (embedded by `inclCyc`). -/
theorem allExR_not_preserved_to_substructure :
    IsAE allExR ∧ IsPos allExR ∧ ¬ IsUniv allExR ∧ ¬ IsExist allExR ∧
    IsEmbedding inclCyc ∧
    Sat S2Cyc.toStr allExR (inclCyc ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr allExR Fin.elim0 := by
  decide

/-- `∃x, ¬ P x` is not preserved by homomorphisms: it holds in `S1N` and fails in `S1P`
along `raiseP`, which is a bijective homomorphism that reflects `R` but not `P`. -/
theorem exNotP_not_preserved_by_hom :
    IsExist exNotP ∧ IsAE exNotP ∧ IsEA exNotP ∧ ¬ IsPos exNotP ∧ ¬ IsPosExist exNotP ∧
    IsSurjHom raiseP ∧ Function.Injective raiseP ∧ ReflectsR raiseP ∧ ¬ ReflectsP raiseP ∧
    Sat S1N.toStr exNotP Fin.elim0 ∧ ¬ Sat S1P.toStr exNotP (raiseP ∘ Fin.elim0) := by
  decide

/-- `∀x ∀y, R x y → x = y` is not preserved by surjective homomorphisms: it holds in
`S2E` (empty `R`) and fails in `S2R01` along the bijective homomorphism `addEdge`,
which reflects `P` but not `R`. -/
theorem allRImpEq_not_preserved_by_surjHom :
    IsUniv allRImpEq ∧ IsAE allRImpEq ∧ IsEA allRImpEq ∧ ¬ IsPos allRImpEq ∧
    IsSurjHom addEdge ∧ Function.Injective addEdge ∧ ReflectsP addEdge ∧ ¬ ReflectsR addEdge ∧
    Sat S2E.toStr allRImpEq Fin.elim0 ∧ ¬ Sat S2R01.toStr allRImpEq (addEdge ∘ Fin.elim0) := by
  decide

/-! ## Further matrix cells -/

/-- The quantifier-free `¬ P x₀` is not preserved by surjective homomorphisms. -/
theorem notP0_not_preserved_by_surjHom :
    IsQF notP0 ∧ IsSurjHom raiseP ∧ Function.Injective raiseP ∧
    Sat S1N.toStr notP0 (env1 0) ∧ ¬ Sat S1P.toStr notP0 (raiseP ∘ env1 0) := by
  decide

/-- The quantifier-free `¬ x₀ = x₁` is not preserved by (non-injective) strong
homomorphisms: `collapse` identifies the two points of `S2E`. -/
theorem neq_not_preserved_by_strongHom :
    IsQF neq01 ∧ IsStrongHom collapse ∧ Function.Surjective collapse ∧
    ¬ Function.Injective collapse ∧
    Sat S2E.toStr neq01 (env2 0 1) ∧ ¬ Sat S1N.toStr neq01 (collapse ∘ env2 0 1) := by
  decide

/-- The existential sentence `∃x ∃y, ¬ x = y` is not preserved by strong homomorphisms. -/
theorem exExNeq_not_preserved_by_strongHom :
    IsExist exExNeq ∧ IsAE exExNeq ∧ IsEA exExNeq ∧
    IsStrongHom collapse ∧ Function.Surjective collapse ∧ ¬ Function.Injective collapse ∧
    Sat S2E.toStr exExNeq Fin.elim0 ∧ ¬ Sat S1N.toStr exExNeq (collapse ∘ Fin.elim0) := by
  decide

/-- The quantifier-free `x₀ = x₁` is not reflected by strong homomorphisms. -/
theorem eq_not_reflected_by_strongHom :
    IsQF eq01 ∧ IsPos eq01 ∧ IsPosExist eq01 ∧
    IsStrongHom collapse ∧ Function.Surjective collapse ∧ ¬ Function.Injective collapse ∧
    Sat S1N.toStr eq01 (collapse ∘ env2 0 1) ∧ ¬ Sat S2E.toStr eq01 (env2 0 1) := by
  decide

/-- The universal sentence `∀x ∀y, x = y` is not reflected by strong homomorphisms. -/
theorem allAllEq_not_reflected_by_strongHom :
    IsUniv allAllEq ∧ IsAE allAllEq ∧ IsEA allAllEq ∧ IsPos allAllEq ∧
    IsStrongHom collapse ∧ Function.Surjective collapse ∧ ¬ Function.Injective collapse ∧
    Sat S1N.toStr allAllEq (collapse ∘ Fin.elim0) ∧ ¬ Sat S2E.toStr allAllEq Fin.elim0 := by
  decide

/-- The atom `P x₀`, which lies in every class, is not reflected by surjective
homomorphisms. -/
theorem P0_not_reflected_by_surjHom :
    IsQF P0 ∧ IsUniv P0 ∧ IsExist P0 ∧ IsAE P0 ∧ IsEA P0 ∧ IsPos P0 ∧ IsPosExist P0 ∧
    IsSurjHom raiseP ∧ Function.Injective raiseP ∧
    Sat S1P.toStr P0 (raiseP ∘ env1 0) ∧ ¬ Sat S1N.toStr P0 (env1 0) := by
  decide

/-- `∃x, P x` is not reflected by surjective homomorphisms. -/
theorem exP_not_reflected_by_surjHom :
    IsExist exP ∧ IsAE exP ∧ IsEA exP ∧ IsPos exP ∧ IsPosExist exP ∧
    IsSurjHom raiseP ∧ Function.Injective raiseP ∧
    Sat S1P.toStr exP (raiseP ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr exP Fin.elim0 := by
  decide

/-- `∀x, P x` is not reflected by bijective homomorphisms that also reflect `R`
(but not `P`). -/
theorem allP_not_reflected_by_surjHom :
    IsUniv allP ∧ IsAE allP ∧ IsEA allP ∧ IsPos allP ∧
    IsSurjHom raiseP ∧ Function.Injective raiseP ∧
    PreservesR raiseP ∧ PreservesP raiseP ∧ ReflectsR raiseP ∧ ¬ ReflectsP raiseP ∧
    Sat S1P.toStr allP (raiseP ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr allP Fin.elim0 := by
  decide

/-! ## Tightness of the individual map laws -/

/-- Dropping preservation of `R` from `univ_preserved_to_substructure_of_embedding`: all other laws hold, the universal
`∀x, ¬ R x x` holds in the target and fails in the source. -/
theorem allNotRxx_reflection_fails_without_presR :
    IsUniv allNotRxx ∧ Function.Injective lowerR ∧ Function.Surjective lowerR ∧
    ¬ PreservesR lowerR ∧ PreservesP lowerR ∧ ReflectsR lowerR ∧ ReflectsP lowerR ∧
    Sat S1N.toStr allNotRxx (lowerR ∘ Fin.elim0) ∧ ¬ Sat S1R.toStr allNotRxx Fin.elim0 := by
  decide

/-- Dropping preservation of `P` from `univ_preserved_to_substructure_of_embedding`. -/
theorem allNotP_reflection_fails_without_presP :
    IsUniv allNotP ∧ Function.Injective lowerP ∧ Function.Surjective lowerP ∧
    PreservesR lowerP ∧ ¬ PreservesP lowerP ∧ ReflectsR lowerP ∧ ReflectsP lowerP ∧
    Sat S1N.toStr allNotP (lowerP ∘ Fin.elim0) ∧ ¬ Sat S1P.toStr allNotP Fin.elim0 := by
  decide

/-- Dropping reflection of `R` from `univ_preserved_to_substructure_of_embedding`. -/
theorem allRxx_reflection_fails_without_reflR :
    IsUniv allRxx ∧ IsPos allRxx ∧ Function.Injective raiseR ∧ Function.Surjective raiseR ∧
    PreservesR raiseR ∧ PreservesP raiseR ∧ ¬ ReflectsR raiseR ∧ ReflectsP raiseR ∧
    Sat S1R.toStr allRxx (raiseR ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr allRxx Fin.elim0 := by
  decide

/-- Dropping preservation of `R` from `exist_preserved_to_extension_of_embedding`,
`posExist_preserved_forward_of_hom` and `pos_preserved_forward_of_surjHom`: all other laws hold
(including surjectivity), `∃x, R x x` holds in the source and fails in the target. -/
theorem exRxx_transfer_fails_without_presR :
    IsExist exRxx ∧ IsPosExist exRxx ∧ IsPos exRxx ∧
    Function.Injective lowerR ∧ Function.Surjective lowerR ∧
    ¬ PreservesR lowerR ∧ PreservesP lowerR ∧ ReflectsR lowerR ∧ ReflectsP lowerR ∧
    Sat S1R.toStr exRxx Fin.elim0 ∧ ¬ Sat S1N.toStr exRxx (lowerR ∘ Fin.elim0) := by
  decide

/-- Dropping preservation of `P` from `exist_preserved_to_extension_of_embedding`,
`posExist_preserved_forward_of_hom` and `pos_preserved_forward_of_surjHom`. -/
theorem exP_transfer_fails_without_presP :
    IsExist exP ∧ IsPosExist exP ∧ IsPos exP ∧
    Function.Injective lowerP ∧ Function.Surjective lowerP ∧
    PreservesR lowerP ∧ ¬ PreservesP lowerP ∧ ReflectsR lowerP ∧ ReflectsP lowerP ∧
    Sat S1P.toStr exP Fin.elim0 ∧ ¬ Sat S1N.toStr exP (lowerP ∘ Fin.elim0) := by
  decide

/-- Dropping reflection of `R` from `exist_preserved_to_extension_of_embedding`. -/
theorem exNotRxx_transfer_fails_without_reflR :
    IsExist exNotRxx ∧ Function.Injective raiseR ∧ Function.Surjective raiseR ∧
    PreservesR raiseR ∧ PreservesP raiseR ∧ ¬ ReflectsR raiseR ∧ ReflectsP raiseR ∧
    Sat S1N.toStr exNotRxx Fin.elim0 ∧ ¬ Sat S1R.toStr exNotRxx (raiseR ∘ Fin.elim0) := by
  decide

/-! ## Non-vacuity instances for the preservation theorems (all hypotheses and the premise hold) -/

/-- `S2NP → S1P`, both points to `0`: a surjective homomorphism that is neither
injective nor reflects `P`. -/
def squashP : S2NP.toStr.carrier → S1P.toStr.carrier := fun _ => 0

/-- `∀x ∃y, P y` (a positive sentence with both quantifiers). -/
def allExP : Fml 0 := .all (.ex (.pred 0))

/-- `univ_preserved_to_substructure_of_embedding` is non-vacuous: an embedding, a universal sentence, and the premise
(truth in the larger structure) holds. -/
theorem univ_preserved_to_substructure_nonvacuous :
    IsUniv allNotRxx ∧ IsEmbedding inclCyc ∧ Sat S2Cyc.toStr allNotRxx (inclCyc ∘ Fin.elim0) := by
  decide

/-- `exist_preserved_to_extension_of_embedding` is non-vacuous. -/
theorem exist_preserved_to_extension_nonvacuous :
    IsExist exP ∧ IsEmbedding inclPN ∧ Sat S1P.toStr exP Fin.elim0 := by
  decide

/-- `posExist_preserved_forward_of_hom` is non-vacuous, with a homomorphism that is neither injective nor
strong. -/
theorem posExist_preserved_forward_nonvacuous :
    IsPosExist exP ∧ PreservesR squashP ∧ PreservesP squashP ∧
    ¬ Function.Injective squashP ∧ ¬ ReflectsP squashP ∧ Sat S2NP.toStr exP Fin.elim0 := by
  decide

/-- `pos_preserved_forward_of_surjHom` is non-vacuous, with a positive sentence using both quantifiers. -/
theorem pos_preserved_forward_nonvacuous :
    IsPos allExP ∧ ¬ IsPosExist allExP ∧ Function.Surjective squashP ∧ PreservesR squashP ∧
    PreservesP squashP ∧ ¬ ReflectsP squashP ∧ Sat S2NP.toStr allExP Fin.elim0 := by
  decide

end Toy.Transfer
