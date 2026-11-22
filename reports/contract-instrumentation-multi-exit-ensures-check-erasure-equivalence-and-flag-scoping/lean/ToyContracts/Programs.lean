import ToyContracts.Crates

/-!
# Concrete programs and contracts used by examples, counterexamples and non-vacuity witnesses
-/

namespace Toy.Contracts

/-- `requires x < 100`, `ensures r ≤ x`. -/
def c1 : Contract := ⟨fun x => decide (x < 100), fun x r => decide (r ≤ x)⟩

/-- `requires x = 1`, `ensures r ≤ x` (a single admitted input). -/
def cOne : Contract := ⟨fun x => x == 1, fun x r => decide (r ≤ x)⟩

/-- `requires x = 3`, `ensures r ≤ x` (a single admitted input). -/
def cThree : Contract := ⟨fun x => x == 3, fun x r => decide (r ≤ x)⟩

/-- Tail expression `x` (after emitting `x`) when `x ≠ 0`; early `return 7` when `x = 0`. -/
def gEarly : Fn :=
  { prologue := []
    entry := 0
    blocks := [ ⟨[], .branch .arg 1 2⟩,
                ⟨[.emit .arg], .ret .tail .arg⟩,
                ⟨[], .ret .early (.lit 7)⟩ ] }

/-- `let y = x - 1` (truncated subtraction); `y?` with error value `9` (taken when `y = 0`, i.e.
`x ≤ 1`); tail expression `y`. Written with the source form `tryQ` of `?`. -/
def gTry : Fn :=
  { prologue := []
    entry := 0
    blocks := [ ⟨[.assign 0 (.sub .arg (.lit 1))], .tryQ (.loc 0) (.lit 9) 1⟩,
                ⟨[], .ret .tail (.loc 0)⟩ ] }

/-- Emit `x`, then return `x` as the tail expression. -/
def gGood : Fn :=
  { prologue := [], entry := 0, blocks := [⟨[.emit .arg], .ret .tail .arg⟩] }

/-- A loop that emits `1` forever. -/
def gLoop : Fn :=
  { prologue := [], entry := 0, blocks := [⟨[.emit (.lit 1)], .goto 0⟩] }

/-- Emit `x`, then panic. -/
def gPanic : Fn :=
  { prologue := [], entry := 0, blocks := [⟨[.emit .arg], .panic⟩] }

/-- A function with no blocks: every run that gets past the prologue is `stuck`. -/
def gStuck : Fn := { prologue := [], entry := 0, blocks := [] }

/-- A function as written that already contains an `ensures` check on the constant `5`, then
returns `x`. -/
def gInt : Fn :=
  { prologue := [], entry := 0, blocks := [⟨[.checkEns (.lit 5)], .ret .tail .arg⟩] }

/-- A function as written that already contains a `requires` check, then returns `x`. -/
def gIntReq : Fn :=
  { prologue := [], entry := 0, blocks := [⟨[.checkReq], .ret .tail .arg⟩] }

/-- A two-block function whose entry jumps to the missing index `3`; block `1` is a `?`. After
lowering, index `3` is the fresh `ret .tryErr 5` block of block `1`. -/
def fOut : Fn :=
  { prologue := []
    entry := 0
    blocks := [ ⟨[], .goto 3⟩,
                ⟨[], .tryQ .arg (.lit 5) 0⟩ ] }

/-- A one-block function whose entry is the missing index `1` (its one jump target, `0`, is in
range); after lowering, index `1` is the fresh `ret .tryErr 5` block of block `0`. -/
def fBadEntry : Fn :=
  { prologue := [], entry := 1, blocks := [⟨[], .tryQ .arg (.lit 5) 0⟩] }

/-- A non-generic call from crate `0` to a function defined in crate `1`. -/
def cs1 : CallSite := ⟨0, 1, 0, false⟩

/-- A call from crate `0` to a generic function defined in crate `1` and instantiated in the
calling crate `0`. -/
def csGen : CallSite := ⟨0, 1, 0, true⟩

/-- A call from crate `0` to a generic function defined in crate `1` and instantiated in a third
crate `2`. -/
def csGen3 : CallSite := ⟨0, 1, 2, true⟩

/-- Flags: crate `0` (the caller) has checks on, every other crate off. -/
def flCallerOn : Nat → Bool := fun k => k == 0

/-- Flags: crate `1` (the defining crate) has checks on, every other crate off. -/
def flDefOn : Nat → Bool := fun k => k == 1

/-- Flags: crate `2` has checks on, every other crate off. -/
def flTwoOn : Nat → Bool := fun k => k == 2

/-- Flags: crates `0` and `1` have checks on, every other crate off. -/
def flZeroOneOn : Nat → Bool := fun k => k == 0 || k == 1

end Toy.Contracts
