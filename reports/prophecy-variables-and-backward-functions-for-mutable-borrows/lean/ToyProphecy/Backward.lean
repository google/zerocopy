import ToyProphecy.RefSem

/-!
# Backward-function translation

The translation in the style of functional translations with *backward
functions*: a live mutable borrow is represented by its current value together
with a pure function from the borrow's final value to the new values of its
lenders. Ending the borrow applies that function to the borrow's current value
and writes the results into the lenders. A lender is a local (for `borrow` and
`borrowSel`) or the current value of the parent borrow (for `reborrow` and for a
borrow returned by a call).

A call `s = f(&mut *r)` is translated through the callee's *backward summary*:
a forward value `calleeFwd f a` (the returned borrow's current value when the
argument's current value is `a`) and a backward function `calleeBack f a v` (the
argument's final value when the returned borrow ends with final value `v`). The
summary is computed from the callee body alone, independently of any call site,
by running the same translation in a fresh frame and composing the backward
functions along the chain of reborrows from the returned borrow up to the
parameter.

The translation performs no borrow checking.
-/

namespace Toy.Prophecy

/-- What a backward function writes to: a local, or the current value of a
(parent) borrow. -/
inductive Target where
  | loc (x : Var)
  | ref (q : RefVar)
  deriving Repr, DecidableEq

/-- A live borrow in the backward-function translation: its current value and a
backward function mapping its final value to the assignments to perform on its
lenders (applied left to right). -/
structure BRef where
  cur : Int
  back : Int → List (Target × Int)

/-- State of the backward-function translation. Lent locals keep their value
from the moment they were lent until their borrow ends. -/
structure BState where
  store : Store
  refs : RefVar → Option BRef

/-- Expression evaluation: reading through a borrow reads its current value. -/
def evalB (L : Bool) (s : BState) : Expr → Option Int
  | .lit n => some n
  | .var x => if L then some (s.store x) else none
  | .deref r => (s.refs r).map (·.cur)
  | .add a b => do
      let u ← evalB L s a
      let v ← evalB L s b
      pure (u + v)

/-- Perform the lender assignments produced by a backward function, left to
right. Writing to the current value of an unbound reference variable is stuck. -/
def applyBack (s : BState) : List (Target × Int) → Option BState
  | [] => some s
  | (.loc x, v) :: rest => applyBack { s with store := s.store.set x v } rest
  | (.ref q, v) :: rest => do
      let p ← s.refs q
      applyBack { s with refs := fupd s.refs q (some { p with cur := v }) } rest

/-- The backward function of a borrow selected at run time between locals `x`
and `y` (`b` is the evaluated condition, `x0`, `y0` the lenders' values at the
borrow): it gives back both loans, the chosen lender receiving the final value
and the other its unchanged value. The chosen lender is written last, so the
degenerate case `x = y` is handled correctly. -/
def selBack (b : Bool) (x y : Var) (x0 y0 : Int) : Int → List (Target × Int) :=
  fun v => if b then [(.loc y, y0), (.loc x, v)] else [(.loc x, x0), (.loc y, v)]

/-- One basic operation in the backward-function translation. -/
def stepOpB (L : Bool) (s : BState) : Op → Option BState
  | .assign x e =>
      if L then (evalB L s e).map fun v => { s with store := s.store.set x v } else none
  | .borrow r x =>
      if L then
        some { s with refs := fupd s.refs r (some { cur := s.store x, back := fun v => [(.loc x, v)] }) }
      else none
  | .borrowSel r c x y =>
      if L then (evalB L s c).map fun cv =>
        let b := decide (cv ≠ 0)
        { s with refs := fupd s.refs r (some
            { cur := if b then s.store x else s.store y
              back := selBack b x y (s.store x) (s.store y) }) }
      else none
  | .reborrow t r => (s.refs r).map fun q =>
      { s with refs := fupd s.refs t (some { cur := q.cur, back := fun v => [(.ref r, v)] }) }
  | .write r e => do
      let q ← s.refs r
      let v ← evalB L s e
      pure { s with refs := fupd s.refs r (some { q with cur := v }) }
  | .endBorrow r => do
      let q ← s.refs r
      applyBack s (q.back q.cur)

/-- Run a list of basic operations in the backward-function translation. -/
def runOpsB (L : Bool) : BState → List Op → Option BState
  | s, [] => some s
  | s, o :: os => (stepOpB L s o).bind fun s' => runOpsB L s' os

/-- The callee frame at entry: the parameter has current value `a` and no lender
inside the frame. Callee frames have no locals; the store component is unused. -/
def calleeInitB (a : Int) : BState :=
  { store := fun _ => 0
    refs := fupd (fun _ => none) Callee.param (some { cur := a, back := fun _ => [] }) }

/-- Run the callee body from argument value `a`. -/
def calleeRunB (f : Callee) (a : Int) : Option BState :=
  runOpsB false (calleeInitB a) f.body

/-- Forward part of the backward summary: the returned borrow's current value. -/
def calleeFwd (f : Callee) (a : Int) : Option Int :=
  (calleeRunB f a).bind fun s => (s.refs f.ret).map (·.cur)

/-- Compose backward functions along the chain of parents, starting from
reference variable `k` whose current value has just been set to its final value,
until the parameter is reached; returns the parameter's final value. Each step
ends the current borrow by applying its backward function (which, in a callee
frame, writes the current value of its parent). `fuel` bounds the chain length. -/
def unwindB (s : BState) : Nat → RefVar → Option Int
  | 0, _ => none
  | fuel + 1, k =>
      if k = Callee.param then (s.refs k).map (·.cur)
      else do
        let q ← s.refs k
        match q.back q.cur with
        | [(.ref j, w)] => do
            let p ← s.refs j
            unwindB { s with refs := fupd s.refs j (some { p with cur := w }) } fuel j
        | _ => none

/-- Backward part of the backward summary, as a partial function: the argument's
final value when the returned borrow ends with final value `v`. -/
def calleeBack? (f : Callee) (a v : Int) : Option Int := do
  let s ← calleeRunB f a
  let q ← s.refs f.ret
  unwindB { s with refs := fupd s.refs f.ret (some { q with cur := v }) } (f.body.length + 1) f.ret

/-- Backward part of the backward summary as a total function (default `0` where
the partial function `calleeBack?` is undefined: when the callee body is stuck,
when the returned name is unbound at the end of the body, or when the chain of
parents from the returned borrow does not reach the parameter within
`f.body.length + 1` steps, e.g. because it is a cycle). -/
def calleeBack (f : Callee) (a v : Int) : Int := (calleeBack? f a v).getD 0

/-- One main-program statement in the backward-function translation. A call binds
`s` to a borrow whose current value is the callee's forward value and whose
backward function writes `calleeBack f a v` into the argument borrow `r`. -/
def stepB (s : BState) : Stmt → Option BState
  | .op o => stepOpB true s o
  | .call t f r => do
      let q ← s.refs r
      let c ← calleeFwd f q.cur
      pure { s with refs := fupd s.refs t (some
        { cur := c, back := fun v => [(.ref r, calleeBack f q.cur v)] }) }

/-- Run a main program in the backward-function translation. -/
def runB : BState → Prog → Option BState
  | s, [] => some s
  | s, c :: cs => (stepB s c).bind fun s' => runB s' cs

/-- The initial state: store `σ`, no borrow. -/
def BState.init (σ : Store) : BState := { store := σ, refs := fun _ => none }

/-- The final store computed by the backward-function translation of `P` from
store `σ`, or `none` if the translation is stuck. -/
def backSem (P : Prog) (σ : Store) : Option Store :=
  (runB (BState.init σ) P).map (·.store)

end Toy.Prophecy
