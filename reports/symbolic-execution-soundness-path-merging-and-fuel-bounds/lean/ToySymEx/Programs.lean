import ToySymEx.Basic

/-! Concrete example CFGs used by the examples and counterexamples. -/

namespace Toy.SymEx

open Term

/-- Straight-line, two blocks, three statements:
`b0: x1 := x0 + 1; assert (x1 == x1); goto b1` and `b1: x2 := x1 + x1; return`. -/
def exStraight : Cfg :=
  [ ⟨[.assign 1 (add (var 0) (int 1)), .assert (eq (var 1) (var 1))], .goto 1⟩,
    ⟨[.assign 2 (add (var 1) (var 1))], .ret⟩ ]

/-- A diamond: `b0: switchInt x0 [0 ↦ b1] otherwise b2`;
`b1: x1 := x0 + 1; goto b3`; `b2: x1 := x0 + 2; goto b3`; `b3: return`. -/
def exDiamond : Cfg :=
  [ ⟨[], .switchInt 0 [(.int 0, 1)] 2⟩,
    ⟨[.assign 1 (add (var 0) (int 1))], .goto 3⟩,
    ⟨[.assign 1 (add (var 0) (int 2))], .goto 3⟩,
    ⟨[], .ret⟩ ]

/-- Panics exactly when `x0 = 0`: `b0: assert (¬ (x0 == 0)); return`. -/
def exPanicIfZero : Cfg :=
  [ ⟨[.assert (Term.not (eq (var 0) (int 0)))], .ret⟩ ]

/-- `b0: assert true; return` — its symbolic panic leaf is infeasible. -/
def exAssertTrue : Cfg :=
  [ ⟨[.assert tt], .ret⟩ ]

/-- An infinite loop: `b0: goto b0`. -/
def exSelfLoop : Cfg :=
  [ ⟨[], .goto 0⟩ ]

/-- A loop that runs exactly three times, then fails an assertion:
`b0: x1 := 0; goto b1`; `b1: switchInt x1 [3 ↦ b3] otherwise b2`;
`b2: x1 := x1 + 1; goto b1`; `b3: assert false; return`. -/
def exLoopThenAssertFalse : Cfg :=
  [ ⟨[.assign 1 (int 0)], .goto 1⟩,
    ⟨[], .switchInt 1 [(.int 3, 3)] 2⟩,
    ⟨[.assign 1 (add (var 1) (int 1))], .goto 1⟩,
    ⟨[.assert ff], .ret⟩ ]

/-- The same three-iteration loop, but returning normally:
`b3: return`. Every input terminates after 13 steps. -/
def exLoop3 : Cfg :=
  [ ⟨[.assign 1 (int 0)], .goto 1⟩,
    ⟨[], .switchInt 1 [(.int 3, 3)] 2⟩,
    ⟨[.assign 1 (add (var 1) (int 1))], .goto 1⟩,
    ⟨[], .ret⟩ ]

/-- An acyclic CFG whose blocks are not numbered in topological order:
`b0: goto b2`; `b1: return`; `b2: goto b1`. -/
def exDag : Cfg :=
  [ ⟨[], .goto 2⟩,
    ⟨[], .ret⟩,
    ⟨[], .goto 1⟩ ]

/-- A CFG with an unreachable block: `b0: return`; `b1: return`. -/
def exDeadBlock : Cfg :=
  [ ⟨[], .ret⟩,
    ⟨[], .ret⟩ ]

/-- Returns quickly when `x0 = 0` and slowly otherwise:
`b0: switchInt x0 [0 ↦ b1] otherwise b2`; `b1: x1 := 1; return`;
`b2: x1 := 1; x2 := 2; return`. At fuel 3 the first branch returns and the
second runs out of fuel. -/
def exHalfDone : Cfg :=
  [ ⟨[], .switchInt 0 [(.int 0, 1)] 2⟩,
    ⟨[.assign 1 (int 1)], .ret⟩,
    ⟨[.assign 1 (int 1), .assign 2 (int 2)], .ret⟩ ]

/-- Valuation with every input `0`. -/
def ρ0 : Valuation := fun _ => .int 0
/-- Valuation with input `x0 = 5` and every other input `0`. -/
def ρ5 : Valuation := fun x => if x = 0 then .int 5 else .int 0

/-! Small decidable views of outcomes (stores are functions, so outcomes are
compared through these views). -/

/-- Constructor tag of an outcome: `0` ok, `1` panic, `2` out of fuel. -/
def Outcome.tag : Outcome → Nat
  | .ok _ => 0
  | .panic _ => 1
  | .outOfFuel => 2

/-- Value of local `x` if the outcome is `ok`. -/
def Outcome.get? (x : Var) : Outcome → Option Val
  | .ok st => some (st x)
  | _ => none

/-- Panic location, if any. -/
def Outcome.panicLoc? : Outcome → Option Loc
  | .panic l => some l
  | _ => none

/-- Constructor tag of a symbolic outcome: `0` ok, `1` panic, `2` out of fuel. -/
def SymOutcome.tag : SymOutcome → Nat
  | .ok _ => 0
  | .panic _ => 1
  | .outOfFuel => 2

end Toy.SymEx
