/-
Toy.SCT.Fixtures
================

Concrete programs used as examples, counterexamples and non-vacuity witnesses. Each comment gives
a first-order program the graphs abstract (over `Nat`, with the base-case guards such as
`if x = 0 then … else …` omitted from the comment). The graphs describe the calls only under those
guards: with truncated subtraction an unguarded call `f(x - 1)` at `x = 0` passes `0` and violates
`x' < x` (see `misfit_graphs_counterexample`).
-/
import Toy.SCT.Check
import Toy.SCT.Semantics

namespace Toy.SCT

/-- The only function of a one-function program. -/
def f0 : Fin 1 := 0

/-- `f(x) = f(x - 1)`: one call, `x' < x`. -/
def gDec : SCG 1 1 := arcsG f0 f0 [(0, 0, .strict)]
/-- One function `f(x)` with the single call `f(x - 1)`. -/
def decLoop : Prog 1 1 := ⟨[gDec]⟩

/-- `f(x) = f(x)`: one call, `x' ≤ x`. -/
def gId : SCG 1 1 := arcsG f0 f0 [(0, 0, .nonstrict)]
/-- One function `f(x)` with the single call `f(x)`. -/
def idLoop : Prog 1 1 := ⟨[gId]⟩

/-- `f(x, y) = f(y, x - 1)`: `x' ≤ y` and `y' < x` (the permuting call). -/
def gSwap : SCG 1 2 := arcsG f0 f0 [(1, 0, .nonstrict), (0, 1, .strict)]
/-- `gSwap ; gSwap`: both parameters strictly decrease. -/
def gSwap2 : SCG 1 2 := arcsG f0 f0 [(0, 0, .strict), (1, 1, .strict)]
/-- `gSwap ; gSwap ; gSwap`: strict arcs `x → y'` and `y → x'`. -/
def gSwap3 : SCG 1 2 := arcsG f0 f0 [(0, 1, .strict), (1, 0, .strict)]
/-- One function `f(x, y)` with the single call `f(y, x - 1)`. -/
def swapDec : Prog 1 2 := ⟨[gSwap]⟩

/-- `f(x, y) = f(x, x - 1)`: `x' ≤ x` and `y' < x`. -/
def gStall : SCG 1 2 := arcsG f0 f0 [(0, 0, .nonstrict), (0, 1, .strict)]
/-- One function `f(x, y)` with the single call `f(x, x - 1)`; its only graph is idempotent with
a nonstrict but no strict self-arc. -/
def stallProg : Prog 1 2 := ⟨[gStall]⟩

/-- A call `f(x - 1, ?)`: `x' < x`, the second argument unconstrained. -/
def gX : SCG 1 2 := arcsG f0 f0 [(0, 0, .strict)]
/-- A call `f(?, y - 1)`: `y' < y`, the first argument unconstrained. -/
def gY : SCG 1 2 := arcsG f0 f0 [(1, 1, .strict)]
/-- The empty graph (`gX ; gY`): no arcs at all. -/
def gEmpty2 : SCG 1 2 := arcsG f0 f0 []
/-- One function `f(x, y)` with two calls, `f(x - 1, ?)` and `f(?, y - 1)`. Each call has a strict
self-arc, but alternating them is unconstrained. -/
def altProg : Prog 1 2 := ⟨[gX, gY]⟩

/-- A call `f(x, y - 1)`: `x' ≤ x` and `y' < y`. -/
def gKeepX : SCG 1 2 := arcsG f0 f0 [(0, 0, .nonstrict), (1, 1, .strict)]
/-- The call structure of the Ackermann function: `f(x - 1, ?)` and `f(x, y - 1)`
(`A(m, n)` calls `A(m - 1, …)` and `A(m, n - 1)`). It has the lexicographic measure `(x, y)`. -/
def ackProg : Prog 1 2 := ⟨[gX, gKeepX]⟩
/-- The lexicographic measure `(x, y)` for `ackProg`. -/
def ackOrd : Fin 1 → Fin 2 → Fin 2 := fun _ l => l

/-- Two mutually recursive functions `f 0` and `f 1` with one parameter: `f0(x)` calls `f1(x - 1)`
and `f1(y)` calls `f0(y)`. -/
def gMut01 : SCG 2 1 := arcsG 0 1 [(0, 0, .strict)]
/-- `f1(y)` calls `f0(y)`. -/
def gMut10 : SCG 2 1 := arcsG 1 0 [(0, 0, .nonstrict)]
/-- The mutually recursive two-function program. -/
def mutProg : Prog 2 1 := ⟨[gMut01, gMut10]⟩
/-- Closure members of `mutProg`: `f0 → f0` with `x' < x`. -/
def gMut00 : SCG 2 1 := arcsG 0 0 [(0, 0, .strict)]
/-- Closure members of `mutProg`: `f1 → f1` with `y' < y`. -/
def gMut11 : SCG 2 1 := arcsG 1 1 [(0, 0, .strict)]
/-- Closure members of `mutProg`: `f1 → f0` with a strict arc. -/
def gMut10s : SCG 2 1 := arcsG 1 0 [(0, 0, .strict)]

/-- The empty one-parameter loop graph. -/
def gEmpty1 : SCG 1 1 := arcsG f0 f0 []

/-- A call from `f0` to `f1` with no size information. -/
def gAcyc : SCG 2 1 := arcsG 0 1 []
/-- Two functions, `f0` calls `f1` once and `f1` makes no calls: no recursion at all. -/
def acycProg : Prog 2 1 := ⟨[gAcyc]⟩

/-- A two-slot argument vector `(a, b)`. -/
def vec2 (a b : Nat) : Fin 2 → Nat := fun i => if i.val = 0 then a else b

/-- The model of `f(x) = f(x)`: every state calls itself. -/
def idStep : State 1 1 → State 1 1 → Prop := fun s t => t = s

/-- The model of `f(x) = if x = 0 then 0 else f(x - 1)`. -/
def decStep : State 1 1 → State 1 1 → Prop :=
  fun s t => t.1 = s.1 ∧ 0 < s.2 0 ∧ t.2 0 = s.2 0 - 1

/-- The model of `f(x, y) = if x = 0 then 0 else f(y, x - 1)`. -/
def swapStep : State 1 2 → State 1 2 → Prop :=
  fun s t => t.1 = s.1 ∧ 0 < s.2 0 ∧ t.2 0 = s.2 1 ∧ t.2 1 = s.2 0 - 1

/-- The model of `f(x) = if x < 100 then f(x + 1) else 0`, which terminates although its argument
grows. -/
def countUpStep : State 1 1 → State 1 1 → Prop :=
  fun s t => t.1 = s.1 ∧ s.2 0 < 100 ∧ t.2 0 = s.2 0 + 1

end Toy.SCT
