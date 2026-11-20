# `toy-sepac`: Reflective AC Normalization for Separating Conjunction

Self-contained Lean 4 (`leanprover/lean4:v4.34.1`, core only, no external dependencies)
formalization in namespace `Toy.SepAC` analyzing the exact algebraic laws, extensions,
completeness boundaries, and algorithmic checks of reflective associative-commutative
normalization and frame cancellation for separating conjunction.

## Module layout

- `Toy/SepAC/Algebra.lean`: Unbundled algebraic laws (`SepAssoc`, `SepComm`, `LeftUnit`,
  `RightUnit`, `IdemElem`, `SepIdem`), unit-symmetry derivations, cardinality-`≤ 2`
  associativity lemma (`atMostTwo_comm_unital_sepAssoc`), concrete witness algebras
  (`NonAssocCarrier`, `leftProj`, `rightProj`, `CellModel`, `TwoCellModel`), and
  positive/negative examples.
- `Toy/SepAC/Syntax.lean`: Syntax trees (`Tree`), `Tree.unitFree`, `Tree.unitCount`,
  `Tree.denote`, `listEnv`, `Tree.atoms`, and canonical right-nested fold normal forms
  (`denoteAtoms`, `denoteNonEmpty`).
- `Toy/SepAC/Normalization.lean`: Monoid flattening (`denote_eq_denoteAtoms_of_assoc_units`),
  full ACU permutation soundness (`acu_denote_eq_of_isPerm`), equal-unit-count and unit-free
  AC soundness (`ac_denote_eq_of_unitCount_eq_of_isPerm`, `ac_denote_eq_of_unitFree_of_isPerm`),
  `↔` characterizations of exact algebraic laws, and proved canonical tightness counterexamples.
- `Toy/SepAC/FreeMonoid.lean`: Finitely supported multiplicity monoid (`Bag`), completeness
  and `↔` characterizations relative to `Bag` and all `Type`-level ACU models
  (`isPerm_of_bag_denote_eq`, `isPerm_iff_bag_denote_eq`,
  `isPerm_iff_forall_acu_denote_eq`), universal `unitCount` converse
  (`unitCount_eq_and_isPerm_of_forall_ac_denote_eq`, with fixed-model scope witness
  `unitCount_eq_not_necessary_in_fixed_model`), environment-aliasing/out-of-bounds
  witnesses, pointwise-idempotent incompleteness (`denote_eq_and_isPerm_false_of_idemElem`),
  non-idempotent conflict incompleteness (`cellModel_incomplete_without_sepIdem`,
  `twoCellModel_conflict_distinct_atoms_incomplete`), and set-check incompleteness
  (`boolOr_setCheck_incomplete`).
- `Toy/SepAC/Entailment.lean`: Entailment and compatibility laws (`EntailsRefl`, `EntailsTrans`,
  `SepMonoRight`, `SepMonoLeft`, `AffineEntails`, `Bientails`, `SepAssocBientails`,
  `SepCommBientails`, `RightUnitBientails`, `LeftUnitBientails`), executable sub-multiset
  cancellation (`cancelAtoms`) with full multiset-difference specification (`cancelAtoms_spec`,
  `cancelAtoms_count`, `cancelAtoms_disjoint`), arbitrary common sub-multiset frame cancellation
  under propositional and mutual-entailment ACU (`acu_entails_of_common_perm_of_sepMonoRight`,
  `bientails_acu_entails_of_common_perm_of_trans_sepMonoRight`) with `cancelAtoms` corollaries,
  non-monotonicity counterexample (`capOne_tight_commonPerm_sepMonoRight`), sufficiency-only
  witness (`totalRelation_cancel_sound_without_laws`), and linear, affine, and partial-vs-maximal
  converse-failure witnesses.
- `Toy/SepAC/Complexity.lean`: Tree size/atom counts, accumulator atom extraction
  (`atomsFast`), and fully proved equivalence of merge-sort permutation checking
  (`checkPermSort_eq_isPerm_and_size_bounds`).
- `Toy/SepAC/ScopeWitnesses.lean`: Concrete witnesses that delimit the scope of claims made
  about the other modules: two-element (`boolImp`-ordered `Bool`) and single-cell affine
  countermodels for non-invertible maximal cancellation, an absorbing-element model that is
  still complete for one environment (`optBagSep`, `optBag_absorbing_but_complete`), and the
  counterexamples and non-vacuity witnesses for the hypotheses of the `cancelAtoms`
  corollaries and of `unitCount_eq_and_isPerm_of_forall_ac_denote_eq`.

The probe `../support/KernelReductionProbe.lean` (outside the library target) records the
Lean `v4.34.1` kernel-reduction behavior of `List.isPerm`, `Lean.Data.AC.sort`,
`List.mergeSort`, and `checkPermSort` on fixed instances; run it from this directory with
`lake env lean ../support/KernelReductionProbe.lean` after `lake build`.
