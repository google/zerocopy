/-!
# Toy model of call-frame-information (CFI) style unwind tables

A function body is a straight-line list of frame-affecting operations.  The
stack grows downward and is addressed in words (one push moves the stack
pointer by one).  An unwind table maps each code offset `i` (the point after
the first `i` operations; offset `body.length` is the point after the whole
body) to a row: a CFA rule `CFA = sp + cfa` and, per register, a rule
`savedAt off` (the caller's value is in memory at `CFA - off`), `sameValue`
(the register still holds the caller's value), or `undefined` (not
recoverable).

The canonical frame address (CFA) is modeled as the stack pointer at function
entry, which is also the caller's stack pointer after return (the toy has no
return-address slot).

Sign conventions: the operation `saveAt r off` stores at `sp + off`, while the
rule `savedAt off` reads at `CFA - off`; DWARF's `offset(N)` reads at
`CFA + N`, so `savedAt off` corresponds to `offset(-off)`.

Table offsets count operations, not bytes: this model is independent of the
byte addresses of the relaxation model.
-/

namespace Toy.Unwind

/-- Frame-affecting operations.  `push r`: decrement `sp`, store `r` at the new
`sp`.  `subSp n` / `addSp n`: move `sp` down / up by `n` words.
`saveAt r off`: store `r` at `sp + off` without moving `sp`.  `pop r`: load
`r` from `sp`, increment `sp`.  `setReg r v`: overwrite register `r` with the
constant `v` (stands for any computation that clobbers `r`). -/
inductive Op where
  | push (r : Nat)
  | subSp (n : Nat)
  | saveAt (r : Nat) (off : Int)
  | pop (r : Nat)
  | addSp (n : Nat)
  | setReg (r : Nat) (v : Int)
deriving Repr, DecidableEq

/-- Machine state: stack pointer, registers, word-addressed memory. -/
structure MState where
  sp : Int
  regs : Nat → Int
  mem : Int → Int

/-- Point update of a function. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (x : α) (v : β) : α → β :=
  fun y => if y = x then v else f y

/-- Concrete semantics of one operation. -/
def execOp : Op → MState → MState
  | .push r, s => { sp := s.sp - 1, regs := s.regs, mem := upd s.mem (s.sp - 1) (s.regs r) }
  | .subSp n, s => { s with sp := s.sp - n }
  | .saveAt r off, s => { s with mem := upd s.mem (s.sp + off) (s.regs r) }
  | .pop r, s => { sp := s.sp + 1, regs := upd s.regs r (s.mem s.sp), mem := s.mem }
  | .addSp n, s => { s with sp := s.sp + n }
  | .setReg r v, s => { s with regs := upd s.regs r v }

/-- Run a list of operations from a state. -/
def run : List Op → MState → MState
  | [], s => s
  | o :: os, s => run os (execOp o s)

/-- Per-register unwind rule (DWARF CFI register rules `offset(N)`,
`same value`, `undefined`, in the toy's sign convention). -/
inductive RegRule where
  | savedAt (off : Int)
  | sameValue
  | undefined
deriving Repr, DecidableEq

/-- One table row: `CFA = sp + cfa`, plus a rule for every register. -/
structure Row where
  cfa : Int
  rule : Nat → RegRule

/-- An unwind table: one row per code offset. -/
abbrev Table := Nat → Row

/-- What an unwinder recovers for register `r` from row `row` in state `s`. -/
def recoverReg (row : Row) (s : MState) (r : Nat) : Option Int :=
  match row.rule r with
  | .savedAt off => some (s.mem (s.sp + row.cfa - off))
  | .sameValue => some (s.regs r)
  | .undefined => none

/-- **Table correctness.**  For every entry state `s0` and every code offset
`i ≤ body.length`, in the state reached by executing the first `i` operations
from `s0`, row `i` computes the caller's stack pointer (`CFA = s0.sp`) and
recovers the entry value of every register in the caller-visible
(callee-saved) set `cs`.  This is single-frame virtual unwinding only: it does
not forbid the body from writing into the caller's frame (addresses
`≥ s0.sp`), and it does not require the body to restore `sp` or any register
by its end. -/
def TableCorrect (body : List Op) (cs : List Nat) (tbl : Table) : Prop :=
  ∀ (s0 : MState) (i : Nat), i ≤ body.length →
    (run (body.take i) s0).sp + (tbl i).cfa = s0.sp ∧
    ∀ r ∈ cs, recoverReg (tbl i) (run (body.take i) s0) r = some (s0.regs r)

/-! ### Abstract interpretation -/

/-- Abstract value: the entry value of register `r`, or unknown. -/
inductive AVal where
  | entry (r : Nat)
  | unknown
deriving Repr, DecidableEq

/-- Abstract state: `d` with `sp = entrySp - d`; abstract register contents;
abstract contents of the word at `entrySp - k` (`slot k`); and the list of
slots written so far (most recent first). -/
structure AState where
  d : Int
  regs : Nat → AVal
  slot : Int → AVal
  written : List Int

/-- Abstract state at function entry. -/
def AState.init : AState := ⟨0, AVal.entry, fun _ => .unknown, []⟩

/-- Abstract transfer function of one operation. -/
def absOp : Op → AState → AState
  | .push r, A =>
    { d := A.d + 1, regs := A.regs, slot := upd A.slot (A.d + 1) (A.regs r),
      written := (A.d + 1) :: A.written }
  | .subSp n, A => { A with d := A.d + n }
  | .saveAt r off, A =>
    { A with slot := upd A.slot (A.d - off) (A.regs r), written := (A.d - off) :: A.written }
  | .pop r, A => { A with d := A.d - 1, regs := upd A.regs r (A.slot A.d) }
  | .addSp n, A => { A with d := A.d - n }
  | .setReg r _, A => { A with regs := upd A.regs r .unknown }

/-- Abstract run of a list of operations. -/
def absRun : List Op → AState → AState
  | [], A => A
  | o :: os, A => absRun os (absOp o A)

/-- Is a register rule justified by the abstract state? -/
def ruleOk (A : AState) (r : Nat) : RegRule → Bool
  | .savedAt off => A.slot off == .entry r
  | .sameValue => A.regs r == .entry r
  | .undefined => false

/-- Check one row against an abstract state. -/
def checkRow (A : AState) (cs : List Nat) (row : Row) : Bool :=
  row.cfa == A.d && cs.all (fun r => ruleOk A r (row.rule r))

/-- **The checker.**  Replays the abstract interpretation and checks every row
`0 … body.length`. -/
def checkTable (body : List Op) (cs : List Nat) (tbl : Table) : Bool :=
  (List.range (body.length + 1)).all
    (fun i => checkRow (absRun (body.take i) AState.init) cs (tbl i))

/-- Register rule generated from an abstract state: `sameValue` if the register
still holds its entry value, else `savedAt k` for the most recently written
slot holding it, else `undefined`. -/
def genRule (A : AState) (r : Nat) : RegRule :=
  if A.regs r = .entry r then .sameValue
  else match A.written.find? (fun k => A.slot k == .entry r) with
    | some k => .savedAt k
    | none => .undefined

/-- **The table generated by abstract interpretation** of the body. -/
def genTable (body : List Op) : Table := fun i =>
  let A := absRun (body.take i) AState.init
  { cfa := A.d, rule := genRule A }

end Toy.Unwind
