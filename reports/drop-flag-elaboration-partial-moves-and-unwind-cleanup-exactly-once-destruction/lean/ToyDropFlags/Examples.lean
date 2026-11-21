import ToyDropFlags.Elab

/-!
# Concrete programs and definition examples

Every theorem in this file is fully proved (by kernel evaluation). Programs here are the
witnesses used by the result cards.
-/

namespace Toy.DropFlags

/-! ## Places and types used below -/

/-- Local 0, whole. -/
def x : Place := ⟨0, []⟩
/-- Local 0, field `.0`. -/
def x0 : Place := ⟨0, [false]⟩
/-- Local 0, field `.1`. -/
def x1 : Place := ⟨0, [true]⟩
/-- Local 1, whole. -/
def y : Place := ⟨1, []⟩

/-- A struct with two leaf fields and no destructor of its own. -/
def pairT : Ty := .pair false .leaf .leaf
/-- A struct with two leaf fields and its own destructor. -/
def dropT : Ty := .pair true .leaf .leaf

/-! ## Example programs -/

/-- Conditional move: `x` is moved on one branch only; the two branches join at the `ret`. -/
def progJoin : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .branch 2 3, .move x 3, .ret] }

/-- Two calls share one cleanup node; the second call consumes `x`, the first does not. -/
def progCleanup : SProg :=
  { locals := [.leaf],
    nodes := [.init x 1, .call [] none 2 4, .call [x] none 3 4, .ret, .resume] }

/-- A partial move out of a struct without a destructor. -/
def progPartial : SProg :=
  { locals := [pairT], nodes := [.init x 1, .move x0 2, .ret] }

/-- A move followed, on one branch, by a re-initialization. -/
def progReinit : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .move x 2, .branch 3 4, .init x 4, .ret] }

/-- A call that may panic while `x` (a struct of two leaves) is live. -/
def progUnwind : SProg :=
  { locals := [pairT], nodes := [.init x 1, .call [] none 2 3, .ret, .resume] }

/-- A program with a back edge (node 1 may jump to node 0). -/
def progLoop : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .branch 0 2, .ret] }

/-- A move out of a field of a struct that has its own destructor. -/
def progDropStruct : SProg :=
  { locals := [dropT], nodes := [.init x 1, .move x0 2, .ret] }

/-- A use after move: `x` is moved twice. -/
def progUseAfterMove : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .move x 2, .move x 3, .ret] }

/-- An overwrite: `x` is initialized twice without an intervening move. -/
def progOverwrite : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .init x 2, .ret] }

/-- A `resume` node reached along a normal edge (no panic is in flight). -/
def progResumeNormal : SProg :=
  { locals := [.leaf, .leaf], nodes := [.init x 1, .init y 2, .resume] }

/-- Both fields of `x` are moved on one branch only. -/
def progShare : SProg :=
  { locals := [pairT], nodes := [.init x 1, .branch 2 4, .move x0 3, .move x1 4, .ret] }

/-- Multi-node cleanup code: the call's unwind edge leads to a `move` of field `.0`, which then
reaches the `resume` along a normal edge. -/
def progMultiStepCleanup : SProg :=
  { locals := [pairT],
    nodes := [.init x 1, .call [] none 4 2, .move x0 3, .resume, .ret] }

/-- A call whose unwind edge leads to the same `ret` as its normal edge. -/
def progUnwindToRet : SProg :=
  { locals := [pairT], nodes := [.init x 1, .call [] none 2 2, .ret] }

/-- A jump out of range: the `init` names node 99 as its successor. -/
def progOOB : SProg := { locals := [.leaf], nodes := [.init x 99] }

/-- The same value is passed twice to one call. -/
def progDuplicateCallArg : SProg :=
  { locals := [.leaf], nodes := [.init x 1, .call [x, x] none 2 3, .ret, .resume] }

/-! ## Elaboration correctness from exhaustive exploration -/

/-- If every run in the exploration tree of an elaborated program is good, the elaboration is
correct on every input. -/
theorem elabCorrect_of_explore (rule : PanicRule) (fc : FlagConfig)
    (d : Nat → Place → Decision) (s : SProg)
    (h : (explore rule (elaborate fc d s) (fuelFor s)).all goodRun = true) :
    ElabCorrect rule fc d s := by
  intro inp
  exact (goodRun_iff _).1 (forall_run_of_explore_all rule _ _ goodRun h inp)

/-! ## Definition examples: types and places -/

example : dropT.units = [[], [false], [true]] := by decide
example : dropT.atoms = [[]] := by decide
example : pairT.atoms = [[false], [true]] := by decide

/-- `isMovePath` admits a field of a struct without a destructor. -/
theorem isMovePath_pos : pairT.isMovePath [false] = true := by decide
/-- `isMovePath` rejects a field of a struct with a destructor. -/
theorem isMovePath_neg : dropT.isMovePath [false] = false := by decide

/-- `atomsOf` of a place strictly inside a struct with a destructor is that struct's atom. -/
theorem atomsOf_inside_dropStruct : atomsOf [dropT] x0 = [x] := by decide

/-! ## Definition examples: logs -/

/-- NoDoubleDrop admits one creation and one drop. -/
theorem noDoubleDrop_pos : NoDoubleDrop [.create 0, .drop 0] := by decide
/-- NoDoubleDrop rejects a drop after a hand-off to a consumer. -/
theorem noDoubleDrop_neg_afterConsume : ¬ NoDoubleDrop [.create 0, .consume 0, .drop 0] := by
  decide
/-- NoDoubleDrop rejects a destructor run on never-written memory. -/
theorem noDoubleDrop_neg_garbage : ¬ NoDoubleDrop [.garbage] := by decide
/-- NoDoubleDrop rejects the destruction of an id that is never created. -/
theorem noDoubleDrop_neg_uncreated : ¬ NoDoubleDrop [.drop 0] := by decide
/-- NoLeak admits a value handed to a consumer. -/
theorem noLeak_pos : NoLeak [.create 0, .consume 0] := by decide
/-- NoLeak rejects a value that is never destroyed. -/
theorem noLeak_neg : ¬ NoLeak [.create 0] := by decide
/-- ExactlyOnce admits a returned run that drops its value once. -/
theorem exactlyOnce_pos : ExactlyOnce ⟨.returned, [.create 0, .drop 0]⟩ := by decide
/-- ExactlyOnce exempts aborted runs from NoLeak. -/
theorem exactlyOnce_pos_aborted : ExactlyOnce ⟨.aborted, [.create 0]⟩ := by decide
/-- ExactlyOnce rejects a returned run that leaks. -/
theorem exactlyOnce_neg_leak : ¬ ExactlyOnce ⟨.returned, [.create 0]⟩ := by decide
/-- ExactlyOnce rejects a double drop even in an aborted run. -/
theorem exactlyOnce_neg_double : ¬ ExactlyOnce ⟨.aborted, [.create 0, .drop 0, .drop 0]⟩ := by
  decide

/-! ## Definition examples: source properties and analyses -/

theorem forward_pos : Forward progJoin := by decide
theorem forward_neg : ¬ Forward progLoop := by decide
theorem placesAreMovePaths_pos : PlacesAreMovePaths progPartial := by decide
theorem placesAreMovePaths_neg : ¬ PlacesAreMovePaths progDropStruct := by decide
theorem movesFromInit_pos : MovesFromInit progJoin := by decide
theorem movesFromInit_neg : ¬ MovesFromInit progUseAfterMove := by decide
theorem initsIntoUninit_pos : InitsIntoUninit progReinit := by decide
theorem initsIntoUninit_neg : ¬ InitsIntoUninit progOverwrite := by decide
/-- `MovesFromInit` rejects a call that receives the same value twice (the `pairwiseDisjoint`
conjunct), although the argument is must-init. -/
theorem movesFromInit_neg_duplicateCallArg :
    mustInit progDuplicateCallArg .fine 1 x = true ∧ ¬ MovesFromInit progDuplicateCallArg := by
  decide
/-- `NoNormalPathToResume` admits one shared cleanup node, multi-node cleanup code, and an
unwind edge into normal code. -/
theorem noNormalPathToResume_pos :
    NoNormalPathToResume progCleanup ∧ NoNormalPathToResume progMultiStepCleanup ∧
    NoNormalPathToResume progUnwindToRet := by decide
/-- `NoNormalPathToResume` rejects a `resume` reached without any panic. -/
theorem noNormalPathToResume_neg : ¬ NoNormalPathToResume progResumeNormal := by decide
/-- Normal reachability excludes nodes behind an unwind edge. -/
theorem normalReachable_examples :
    NormalReachable progCleanup 3 = true ∧ NormalReachable progCleanup 4 = false ∧
    ForwardReachable progCleanup 4 = true := by decide
theorem moveChecked_pos : MoveChecked progJoin := by decide
theorem moveChecked_neg : ¬ MoveChecked progUseAfterMove := by decide

/-- At the join of `progJoin`, `x` is may-init but not must-init. -/
theorem progJoin_join_disagrees :
    mayInit progJoin .fine 3 x = true ∧ mustInit progJoin .fine 3 x = false := by decide
/-- After the partial move in `progPartial`, field `.1` is must-init and field `.0` is not
may-init. -/
theorem progPartial_ret_static :
    mustInit progPartial .fine 2 x1 = true ∧ mayInit progPartial .fine 2 x0 = false := by decide
/-- Forward reachability: a node behind a branch is forward-reachable; a node with no incoming
edge is not. -/
theorem forwardReachable_pos : ForwardReachable progJoin 2 = true := by decide
theorem forwardReachable_neg :
    ForwardReachable { locals := [.leaf], nodes := [.ret, .init x 2, .ret] } 1 = false := by decide
/-- Forward reachability ignores edges to smaller indices: in this acyclic program, numbered out
of topological order, node 1 is reached on every run but is not forward-reachable. -/
theorem forwardReachable_ignores_backward_index_edges :
    ForwardReachable { locals := [.leaf], nodes := [.init x 2, .ret, .branch 1 3, .move x 1] } 1
      = false := by decide
/-- An unreachable node is must-init for every atom and may-init for none. -/
theorem unreachable_must_top_may_bot :
    mustInit { locals := [.leaf], nodes := [.ret, .init x 2, .ret] } .fine 1 x = true ∧
    mayInit { locals := [.leaf], nodes := [.ret, .init x 2, .ret] } .fine 1 x = false := by decide
/-- An unreachable node does not propagate: the `init` at unreachable node 1 does not make `x`
may-init at node 2. -/
theorem unreachable_does_not_propagate :
    mayInit { locals := [.leaf], nodes := [.ret, .init x 2, .ret] } .fine 2 x = false := by decide

/-! ## Definition examples: decisions, compatibility, flags -/

theorem stdDecision_examples :
    stdDecision true true = .drop ∧ stdDecision true false = .test ∧
    stdDecision false false = .skip ∧ stdDecision false true = .skip := by decide

/-- The standard map is compatible on `progJoin`. -/
theorem allCompatible_pos : AllCompatible progJoin (stdMap progJoin .fine) := by decide
/-- An unconditional drop at the join of `progJoin` is not compatible. -/
theorem allCompatible_neg :
    ¬ AllCompatible progJoin (overrideAt (stdMap progJoin .fine) 3 x .drop) := by decide

/-- The standard elaboration of `progJoin` needs exactly one flag, the flag of `x`. -/
theorem flagSet_progJoin : flagSet progJoin (stdMap progJoin .fine) = [x] := by decide
/-- The standard elaboration of `progPartial` needs no flag. -/
theorem flagSet_progPartial : flagSet progPartial (stdMap progPartial .fine) = [] := by decide
/-- The standard elaboration of `progShare` needs two flags. -/
theorem flagSet_progShare : flagSet progShare (stdMap progShare .fine) = [x0, x1] := by decide
/-- `flagSet` ignores tests at drop points that are not forward-reachable. -/
theorem flagSet_ignores_unreachable_test :
    flagSet { locals := [.leaf], nodes := [.ret, .ret] }
      (overrideAt (stdMap { locals := [.leaf], nodes := [.ret, .ret] } .fine) 1 x .test) = [] := by
  decide

/-- A jump out of range gets the elaborated program stuck (not aborted), so `ElabCorrect`
rejects it. -/
theorem progOOB_stuck :
    (runElab .abort .std (stdMap progOOB .fine) progOOB []).outcome = .stuck ∧
    ¬ ElabCorrect .abort .std (stdMap progOOB .fine) progOOB := by
  refine ⟨by decide, fun h => ?_⟩
  have := (h []).2
  revert this; decide

/-- The elaborated ladder at the join of `progJoin` starts with a flag test on `x`. -/
theorem stdElab_progJoin_ladder :
    (match (stdElab progJoin).node (.lad 3 0) with
     | .test a (.dropAt 3 0) (.lad 3 1) => a == x
     | _ => false) = true := by decide

/-- `ElabCorrect` admits the standard elaboration of `progJoin` (all runs checked). -/
theorem elabCorrect_pos : ElabCorrect .abort .std (stdMap progJoin .fine) progJoin :=
  elabCorrect_of_explore _ _ _ _ (by decide)

/-- `ElabCorrect` rejects an unconditional drop at the join of `progJoin`. -/
theorem elabCorrect_neg :
    ¬ ElabCorrect .abort .std (overrideAt (stdMap progJoin .fine) 3 x .drop) progJoin := by
  intro h
  have := (h [true]).1
  revert this
  decide

end Toy.DropFlags
