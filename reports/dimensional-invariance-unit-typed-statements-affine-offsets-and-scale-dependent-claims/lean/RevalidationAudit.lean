import ToyUnits

/-!
Axiom audit of the sixteen result theorems of the package.

Run from the `lean/` directory after `lake build`:

    lake env lean RevalidationAudit.lean

Each reported axiom list should be a subset of `propext`, `Classical.choice`, `Quot.sound`.
This file is not part of the `ToyUnits` library target.
-/

#print axioms Toy.Units.hasPlainReading_iff_posUnitInvariant
#print axioms Toy.Units.evalIn_act_eq_scaleOf_mul
#print axioms Toy.Units.unitInvariant_of_wellTyped
#print axioms Toy.Units.invariantAt_of_wellTypedAt
#print axioms Toy.Units.sumMixed_not_wellTyped_not_posUnitInvariant
#print axioms Toy.Units.cubeSum_not_wellTyped_unitInvariant
#print axioms Toy.Units.invariantAt_of_wellTypedAt_noOrder_of_ne_zero
#print axioms Toy.Units.invariantAt_all_wellTypedAt_iff
#print axioms Toy.Units.sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant
#print axioms Toy.Units.affineInvariant_of_pointVectorTyped
#print axioms Toy.Units.oneVarLength_poly_eval_eq_mul
#print axioms Toy.Units.oneVarLength_eval_eq_mul
#print axioms Toy.Units.definableOnPos_iff
#print axioms Toy.Units.not_definableOnPos_add_one
#print axioms Toy.Units.not_definableOnPos_max_one
#print axioms Toy.Units.allHomogeneous_iff_invZero
