import ToyProphecy.Syntax

/-!
# Reference operational semantics

The ground-truth semantics: a mutable borrow is an *address* (the name of the
local it points to), writes through a borrow update the store in place, and
ending a borrow has no run-time effect (lifetimes are erased at run time). This
semantics performs **no** borrow checking; the borrow discipline is a separate,
static predicate (`ToyProphecy/Discipline.lean`). A run is stuck (`none`) only on
a scoping error: using a reference variable that was never bound, a local
operation inside a callee body, or a callee returning an unbound reference
variable.
-/

namespace Toy.Prophecy

/-- Point update of a function. -/
def fupd {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun j => if j = k then v else f j

/-- State of the reference semantics: the store and, for each reference
variable, the address (local) it points to. -/
structure RState where
  store : Store
  refs : RefVar → Option Var

/-- Expression evaluation in the reference semantics. `L` says whether the
current frame may access locals (true in the main program, false in callees). -/
def evalR (L : Bool) (s : RState) : Expr → Option Int
  | .lit n => some n
  | .var x => if L then some (s.store x) else none
  | .deref r => (s.refs r).map s.store
  | .add a b => do
      let u ← evalR L s a
      let v ← evalR L s b
      pure (u + v)

/-- One basic operation in the reference semantics. -/
def stepOpR (L : Bool) (s : RState) : Op → Option RState
  | .assign x e =>
      if L then (evalR L s e).map fun v => { s with store := s.store.set x v } else none
  | .borrow r x =>
      if L then some { s with refs := fupd s.refs r (some x) } else none
  | .borrowSel r c x y =>
      if L then (evalR L s c).map fun (v : Int) =>
        { s with refs := fupd s.refs r (some (if v ≠ 0 then x else y)) }
      else none
  | .reborrow t r => (s.refs r).map fun a => { s with refs := fupd s.refs t (some a) }
  | .write r e => do
      let a ← s.refs r
      let v ← evalR L s e
      pure { s with store := s.store.set a v }
  | .endBorrow r => (s.refs r).map fun _ => s

/-- Run a list of basic operations in the reference semantics. -/
def runOpsR (L : Bool) : RState → List Op → Option RState
  | s, [] => some s
  | s, o :: os => (stepOpR L s o).bind fun s' => runOpsR L s' os

/-- The callee frame at entry: parameter `0` points to address `a`. -/
def calleeRefsR (a : Var) : RefVar → Option Var := fupd (fun _ => none) Callee.param (some a)

/-- One main-program statement in the reference semantics. A call runs the callee
body on the shared store in a fresh reference frame whose parameter points to
the argument's address, and binds `s` to the address the callee returns. -/
def stepR (s : RState) : Stmt → Option RState
  | .op o => stepOpR true s o
  | .call t f r => do
      let a ← s.refs r
      let s' ← runOpsR false { store := s.store, refs := calleeRefsR a } f.body
      let b ← s'.refs f.ret
      pure { store := s'.store, refs := fupd s.refs t (some b) }

/-- Run a main program in the reference semantics. -/
def runR : RState → Prog → Option RState
  | s, [] => some s
  | s, c :: cs => (stepR s c).bind fun s' => runR s' cs

/-- The initial state of a main program: store `σ`, no reference bound. -/
def RState.init (σ : Store) : RState := { store := σ, refs := fun _ => none }

/-- The final store of a main program run from store `σ` in the reference
semantics, or `none` if the run is stuck. -/
def refSem (P : Prog) (σ : Store) : Option Store :=
  (runR (RState.init σ) P).map (·.store)

end Toy.Prophecy
