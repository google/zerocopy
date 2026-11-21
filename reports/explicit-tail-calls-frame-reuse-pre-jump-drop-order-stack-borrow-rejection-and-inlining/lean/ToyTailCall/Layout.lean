/-!
# A toy argument-area layout for frame reuse

A separate, lower-level toy than the frame-stack machine (no proved relation connects the
two). Memory is a map from integer addresses to cells. The running function `g` has its
frame base at address `b`; its caller reserved `g`'s incoming-argument area of `inG` cells at
`[b - inG, b)`, at the top of the caller's own frame, and every address below `b - inG`
belongs to the caller's frame or to frames further down the stack.

Frame reuse for `become h(args)` writes `h`'s `inH` argument cells at `[b - inH, b)`, anchored
at the same boundary where `h` expects its incoming arguments (as a callee called from the
same place would), and `h` then runs in place of `g`. After `h` returns, the area is removed
either by the caller (`callerPops`, which removes the `inG` cells it reserved) or by the callee
(`calleePops`, which removes the `inH` cells it expects). `ReuseSound` is this fixed-boundary
model: the return address is not relocated and the stack pointer is not adjusted before the
jump. `ReuseSoundAt` adds a relocation of the boundary by `δ` cells.

Addresses are integers, so `b - inH` is ordinary (not truncated) subtraction even when it is
negative; areas may have size `0`.
-/

namespace Toy.TailCall.Layout

/-- Which side removes the incoming-argument area after the callee returns. -/
inductive Cleanup where
  | callerPops
  | calleePops
  deriving DecidableEq, Repr

abbrev Mem := Int → Nat

/-- Write `vs` at consecutive addresses starting at `a`. -/
def writeArgs (m : Mem) (a : Int) : List Nat → Mem
  | [] => m
  | v :: vs => writeArgs (fun x => if x = a then v else m x) (a + 1) vs

/-- Read `n` consecutive cells starting at `a`. -/
def readArgs (m : Mem) (a : Int) : Nat → List Nat
  | 0 => []
  | n + 1 => m a :: readArgs m (a + 1) n

/-- Writing at `[a, a + n)` leaves every address below `a` unchanged. -/
theorem writeArgs_eq_of_lt (m : Mem) (a : Int) (args : List Nat) (x : Int) (hx : x < a) :
    writeArgs m a args x = m x := by
  induction args generalizing m a with
  | nil => rfl
  | cons v vs ih =>
    simp only [writeArgs]
    rw [ih _ (a + 1) (by omega)]
    have : x ≠ a := by omega
    simp [this]

/-- Reading back what was written at `a` returns the written list. -/
theorem readArgs_writeArgs (m : Mem) (a : Int) (args : List Nat) :
    readArgs (writeArgs m a args) a args.length = args := by
  induction args generalizing m a with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.length_cons, readArgs, writeArgs]
    congr 1
    · rw [writeArgs_eq_of_lt _ (a + 1) vs a (by omega)]
      simp
    · exact ih _ (a + 1)

/-- Memory after frame reuse writes the callee's arguments below the boundary `b`. -/
def reuseWrite (m : Mem) (b : Int) (inH : Nat) (args : List Nat) : Mem :=
  writeArgs m (b - inH) args

/-- Conjunct (ii) of `ReuseSound` holds for all sizes: the callee reads back its arguments. -/
theorem readArgs_reuseWrite (m : Mem) (b : Int) (inH : Nat) (args : List Nat)
    (hlen : args.length = inH) : readArgs (reuseWrite m b inH args) (b - inH) inH = args := by
  subst hlen
  exact readArgs_writeArgs m _ args

/-- The stack pointer seen by `g`'s caller after the callee returns (it reserved the area at
`[b - inG, b)`, so it expects `b - inG`). -/
def spAfterReturn (cl : Cleanup) (b : Int) (inG inH : Nat) : Int :=
  match cl with
  | .callerPops => b - inG
  | .calleePops => b - inH

/-- **Frame reuse is sound** for incoming areas `inG` (current function) and `inH` (callee)
under cleanup convention `cl`, at the fixed boundary `b` (no return-address relocation): for
every memory, frame base and argument list of the callee's size, (i) no cell below `b - inG`
(the caller's frame and everything beneath) changes, (ii) the callee reads back exactly its
arguments from where it expects them, and (iii) after the callee returns the caller sees the
stack pointer it expects.

Conjunct (ii) holds for all sizes (`readArgs_reuseWrite`): the arguments are already-evaluated
numbers written into a fresh area, so copying arguments in place out of `g`'s own incoming
area (where an overlapping write can clobber an argument not yet read) is not modelled.
Conjunct (iii) is fixed by `spAfterReturn`, which stipulates each convention's stack pointer
after the return. -/
def ReuseSound (cl : Cleanup) (inG inH : Nat) : Prop :=
  ∀ (m : Mem) (b : Int) (args : List Nat), args.length = inH →
    (∀ x, x < b - inG → reuseWrite m b inH args x = m x) ∧
    readArgs (reuseWrite m b inH args) (b - inH) inH = args ∧
    spAfterReturn cl b inG inH = b - inG

/-! ### Frame reuse with return-address relocation

The boundary at which `h` expects its arguments (the position of the return address) may be
moved by `δ` cells before the jump: `h`'s area is written at `[b + δ - inH, b + δ)`. After `h`
returns, under caller cleanup the caller removes its `inG` cells below the moved boundary,
and under callee cleanup `h` removes its `inH` cells below it. `δ = 0` is the fixed-boundary
model above (`reuseSoundAt_zero_iff`). Writing the relocated return address itself is not
modelled. -/

/-- Memory after frame reuse with the boundary moved from `b` to `b + δ`. -/
def reuseWriteAt (m : Mem) (b δ : Int) (inH : Nat) (args : List Nat) : Mem :=
  writeArgs m (b + δ - inH) args

/-- With relocation too, the callee reads back its arguments. -/
theorem readArgs_reuseWriteAt (m : Mem) (b δ : Int) (inH : Nat) (args : List Nat)
    (hlen : args.length = inH) :
    readArgs (reuseWriteAt m b δ inH args) (b + δ - inH) inH = args := by
  subst hlen
  exact readArgs_writeArgs m _ args

/-- The stack pointer seen by `g`'s caller after the callee returns, boundary moved by `δ`. -/
def spAfterReturnAt (cl : Cleanup) (b δ : Int) (inG inH : Nat) : Int :=
  match cl with
  | .callerPops => b + δ - inG
  | .calleePops => b + δ - inH

/-- **Frame reuse with relocation `δ` is sound**: conditions (i)–(iii) of `ReuseSound`, with
`h`'s area at `[b + δ - inH, b + δ)`. -/
def ReuseSoundAt (cl : Cleanup) (δ : Int) (inG inH : Nat) : Prop :=
  ∀ (m : Mem) (b : Int) (args : List Nat), args.length = inH →
    (∀ x, x < b - inG → reuseWriteAt m b δ inH args x = m x) ∧
    readArgs (reuseWriteAt m b δ inH args) (b + δ - inH) inH = args ∧
    spAfterReturnAt cl b δ inG inH = b - inG

/-- A toy signature: cell counts of the explicit parameters, and whether the function takes
a hidden caller-location parameter (one cell, after the explicit ones; a hidden parameter
passed in a register, or one that shifts the positions of explicit parameters, is not
modelled). -/
structure Sig where
  explicit : List Nat
  callerLoc : Bool
  deriving DecidableEq, Repr

/-- Size of the incoming-argument area, hidden parameter included. -/
def Sig.areaSize (s : Sig) : Nat := s.explicit.sum + (if s.callerLoc then 1 else 0)

/-- Syntactic check: equal signatures, hidden parameter included. -/
def sigCheckFull (g h : Sig) : Bool := g == h

/-- Syntactic check that ignores the hidden parameter: equal explicit parameters. -/
def sigCheckExplicit (g h : Sig) : Bool := g.explicit == h.explicit

end Toy.TailCall.Layout
