/-!
# Syntax of the toy contract-instrumentation language

A function is a control-flow graph (CFG) of basic blocks over one immutable natural-number
argument, a total store of natural-number locals, an observable event stream (`emit`), and a
contract given by two Boolean-valued clauses (`requires` and `ensures`).
-/

namespace Toy.Contracts

/-- Operands: the (single, immutable) argument, a literal, or a local. -/
inductive Operand where
  | arg
  | lit (n : Nat)
  | loc (i : Nat)
  deriving DecidableEq, Repr

/-- Right-hand sides. `sub` is truncated natural-number subtraction (`3 - 5 = 0`). -/
inductive Rvalue where
  | use (o : Operand)
  | add (a b : Operand)
  | sub (a b : Operand)
  deriving DecidableEq, Repr

/-- Which contract clause a failed runtime check belongs to. -/
inductive CheckKind where
  | pre
  | post
  deriving DecidableEq, Repr

/-- Statements. `checkReq` and `checkEns o` are runtime contract checks and `assumeReq` is the
UB-on-false assumption of the `requires` clause (executing it when the clause is false is undefined
behaviour). These three contract statements carry no predicate of their own: each evaluates a
clause of the contract under which the function is run, so a contract statement written in a
function as written tests the same clauses as the checks that instrumentation inserts. -/
inductive Stmt where
  | assign (i : Nat) (rv : Rvalue)
  | emit (o : Operand)
  | checkReq
  | checkEns (o : Operand)
  | assumeReq
  deriving DecidableEq, Repr

/-- Provenance of a return edge, recorded by lowering: the tail expression, an explicit early
`return`, or the error path of `?`. -/
inductive ExitKind where
  | tail
  | early
  | tryErr
  deriving DecidableEq, Repr

/-- Terminators. `branch o b₁ b₀` goes to `b₁` if `o ≠ 0` and to `b₀` if `o = 0`.
`tryQ o e b` is the source form of `?`: if `o ≠ 0` it continues at `b`, and if `o = 0` it
returns the value of `e` (the error path) without a separate return edge; `lower` turns it into a
`branch` to a fresh block ending in `ret .tryErr e`. `ret k o` is a normal return of the value of
`o` along a return edge of provenance `k`. `panic` ends the run with the outcome `panic`; it is not
a normal return, and no unwinding or cleanup is modelled. -/
inductive Term where
  | goto (b : Nat)
  | branch (o : Operand) (b₁ b₀ : Nat)
  | tryQ (o : Operand) (e : Operand) (b : Nat)
  | ret (k : ExitKind) (o : Operand)
  | panic
  deriving DecidableEq, Repr

/-- A basic block: straight-line statements followed by one terminator. -/
structure Block where
  stmts : List Stmt
  term : Term
  deriving DecidableEq, Repr

/-- A function: a prologue executed once on entry (any statement list; instrumentation puts the
`requires` check first in it, and no theorem requires it to be empty), an entry block index, and
the blocks, indexed by position in the list. A jump to an index outside the list makes the run
`stuck`. -/
structure Fn where
  prologue : List Stmt
  entry : Nat
  blocks : List Block
  deriving DecidableEq, Repr

/-- A contract: a decidable `requires` clause on the argument and a decidable `ensures` clause on
the argument and the returned value, both represented as Boolean-valued functions. -/
structure Contract where
  req : Nat → Bool
  ens : Nat → Nat → Bool

/-- How a run ends. `ret r` is a normal return; `panic` a panic exit (the run ends; no unwinding
is modelled); `checkFail k` a failed runtime contract check (an observable abort, not undefined
behaviour); `ub` undefined behaviour (produced by a failing `assumeReq`; no other statement or
terminator produces it); `stuck` a jump to a missing
block; `fuelOut` means the fuel ran out before the run ended. -/
inductive Outcome where
  | ret (r : Nat)
  | panic
  | checkFail (k : CheckKind)
  | ub
  | stuck
  | fuelOut
  deriving DecidableEq, Repr

/-- An observation: the emitted events (in order) and how the run ended. -/
structure Obs where
  events : List Nat
  outcome : Outcome
  deriving DecidableEq, Repr

end Toy.Contracts
