/-
Kernel-reduction probe for the `checkPermSort` / `List.mergeSort` observation (Lean v4.34.1).

Run from the package's `lean/` directory after `lake build`:

  lake env lean ../support/KernelReductionProbe.lean

For each closed Boolean term `t` below, the probe asks the Lean kernel directly (no elaborator
unfolding heuristics) two questions: does `Lean.Kernel.whnf` reduce `t` to the constructor
`Bool.true`, and does `Lean.Kernel.isDefEq` accept `t ≡ true` (the check the kernel performs when
`Eq.refl true` is offered as a proof of `t = true`)? It prints one `KERNEL_PROBE` line per term
and fails with an error if any answer differs from the expected answer recorded next to the term.

Expected on Lean v4.34.1: the structurally recursive `List.isPerm` and `Lean.Data.AC.sort` reduce;
the well-founded `List.mergeSort`, and hence `checkPermSort`, do not. The answers are specific to
this toolchain release.
-/
import Lean
import Toy

open Lean Elab Command Toy.SepAC

/-- Elaborate `stx` as a closed term and ask the kernel whether it reduces to `Bool.true`. -/
def kernelReducesToTrue (label : String) (stx : Term) (expected : Bool) :
    CommandElabM Bool := do
  let e ← liftTermElabM do
    let e ← Term.elabTerm stx (some (mkConst ``Bool))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let env ← getEnv
  -- A kernel exception (rather than a definite answer) is reported and counts as unexpected.
  let (whnfTrue, whnfErr) :=
    match Kernel.whnf env {} e with
    | .ok r => (r == mkConst ``Bool.true, false)
    | .error _ => (false, true)
  let (defeqTrue, defeqErr) :=
    match Kernel.isDefEq env {} e (mkConst ``Bool.true) with
    | .ok b => (b, false)
    | .error _ => (false, true)
  let ok := !whnfErr && !defeqErr && whnfTrue == expected && defeqTrue == expected
  logInfo m!"KERNEL_PROBE {label}: kernel whnf = true: {whnfTrue}; kernel isDefEq with true: {defeqTrue}; kernel exception: {whnfErr || defeqErr}; expected: {expected}; {if ok then "as expected" else "UNEXPECTED"}"
  return ok

run_cmd do
  let mut allOk := true
  allOk := (← kernelReducesToTrue "List.isPerm"
    (← `(([2, 0] : List Nat).isPerm [0, 2])) true) && allOk
  allOk := (← kernelReducesToTrue "Lean.Data.AC.sort"
    (← `(Lean.Data.AC.sort [3, 1, 2] == [1, 2, 3])) true) && allOk
  allOk := (← kernelReducesToTrue "List.mergeSort"
    (← `((([3, 1, 2] : List Nat).mergeSort (fun a b => decide (a ≤ b))) == [1, 2, 3])) false) && allOk
  allOk := (← kernelReducesToTrue "checkPermSort"
    (← `(checkPermSort (.node (.node (.atom 2) .unit) (.atom 0)) (.node (.atom 0) (.atom 2)))) false) && allOk
  if allOk then
    logInfo "KERNEL_PROBE summary: all answers as expected"
  else
    throwError "KERNEL_PROBE summary: some answers differ from the expected answers"

-- Elaborator-level sanity check: the same `checkPermSort` instance does evaluate to `true`
-- (by compiled evaluation, not by kernel reduction), and the proved bridge
-- `checkPermSort_eq_isPerm_and_size_bounds` lets a proof use `List.isPerm` instead.
#eval checkPermSort (.node (.node (.atom 2) .unit) (.atom 0)) (.node (.atom 0) (.atom 2))
example : checkPermSort (.node (.node (.atom 2) .unit) (.atom 0)) (.node (.atom 0) (.atom 2)) = true := by
  rw [(checkPermSort_eq_isPerm_and_size_bounds _ _).1]; rfl
