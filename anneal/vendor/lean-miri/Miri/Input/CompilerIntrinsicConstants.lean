import Miri.Input.CompilerIntrinsicFacts
import Miri.Interpreter.ExecutionMachine

/-! Direct source `const_at/expect_const`, `to_value`, `to_branch` and
`to_leaf` queries for atomic and SIMD intrinsics. These inspect canonical
compiler constants; they do not normalize aliases or invent const evaluation.
Source compiler invariants are explicit invalid-program errors, while absent
imported metadata remains unsupported. -/
namespace Miri.Input.CompilerIntrinsicConstants
open Miri.Interpreter Miri.MIR Miri.Memory Miri.ABI
private def invalid (message : String) : StepError :=
  .invalidProgram s!"intrinsic generic constant: {message}"
private def value (p : CompilerIntrinsicFacts.Prepared) (id : TypeConstId) :
    Except StepError ValTree := do
  let some constant := p.program.compilerTables.typeConstants[id]?
    | throw (.unsupported "intrinsic generic constant missing from compiler table")
  match constant with
  | .Value _ tree => pure tree
  | _ => throw (invalid "source to_value requires ConstKind::Value")
private def node (tree : ValTree) : Except StepError ValTreeNode := do
  let some result := tree.nodes[tree.root]? | throw (invalid "invalid ValTree root")
  pure result
private def branch (tree : ValTree) : Except StepError (Array TypeConstId) := do
  match ← node tree with
  | .Branch fields => pure fields
  | _ => throw (invalid "source to_branch requires a branch")
private def leaf (tree : ValTree) : Except StepError ScalarInt := do
  let .Leaf bits bytes ← node tree | throw (invalid "source to_leaf requires a leaf")
  unless bytes > 0 && bytes ≤ 16 && bits < 2 ^ (bytes * 8) do
    throw (invalid "invalid compiler ScalarInt representation")
  match ScalarInt.tryFromUInt (BitVec.ofNat 128 bits) (Size.ofBytes (UInt64.ofNat bytes)) with
  | .ok (some scalar) => pure scalar
  | _ => throw (invalid "invalid compiler ScalarInt width")
private def argument (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance)
    (index : Nat) : Except StepError ValTree := do
  unless p.entries.any (·.callee == callee) do
    throw (.unsupported "full intrinsic instance missing from compiler metadata")
  let some (.Const id) := callee.args[index]?
    | throw (invalid "const_at/expect_const requires a constant argument")
  value p id
private def firstLeaf (p : CompilerIntrinsicFacts.Prepared) (tree : ValTree) :
    Except StepError ScalarInt := do
  let fields ← branch tree
  let some first := fields[0]? | throw (invalid "enum ValTree has no discriminant")
  leaf (← value p first)
def ordering (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) (index : Nat) := do
  let scalar ← firstLeaf p (← argument p callee index)
  let result ← scalar.toAtomicOrdering.mapError (fun _ => invalid "invalid atomic ordering discriminant")
  pure (match result with
    | .relaxed => Miri.Concurrency.AtomicOrdering.Relaxed
    | .release => .Release
    | .acquire => .Acquire
    | .acqRel => .AcqRel
    | .seqCst => .SeqCst)
/-- Source atomic_load/store only calls to_value; the volatile value is ignored. -/
def volatile (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) (index : Nat) :
    Except StepError Unit := do
  let _ ← argument p callee index
  pure ()
def shuffle (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) (index : Nat) :
    Except StepError (Array UInt32) := do
  let fields ← branch (← argument p callee index)
  fields.mapM fun field => do
    let scalar ← leaf (← value p field)
    scalar.toUInt32.mapError (fun _ => invalid "shuffle index is not a u32 ScalarInt")
def alignment (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) (index : Nat) := do
  let scalar ← firstLeaf p (← argument p callee index)
  scalar.toSimdAlignment.mapError (fun _ => invalid "invalid SIMD alignment discriminant")
private def lift (result : Except StepError A) : MachineHooks.M K User A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

def hooks (p : CompilerIntrinsicFacts.Prepared)
    (base : ExecutionMachine.Config K User C Other Extern Host) :
    ExecutionMachine.Config K User C Other Extern Host :=
  {base with intrinsics := fun callee =>
    let context := base.intrinsics callee
    {context with
      atomicHooks := {context.atomicHooks with
        orderingConst := fun _ index => lift (ordering p callee index)
        volatileConst := fun _ index => lift (volatile p callee index)}
      simdHooks := {context.simdHooks with
        shuffleConst := fun _ index => lift (shuffle p callee index)
        alignmentConst := fun _ index => lift (alignment p callee index)}}}
end Miri.Input.CompilerIntrinsicConstants
