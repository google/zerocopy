import Toy.PlaceEval.Semantics

/-!
# Program transformations

`List.set` leaves a block list unchanged when the label is out of range.
-/

namespace Toy.PlaceEval

/-- Replace block `l` by `B`. -/
def Prog.setBlk (P : Prog) (l : Label) (B : Block) : Prog :=
  { P with blocks := P.blocks.set l B }

/-- Delete the `i`-th statement of block `l` (used to erase a `placeMention`). -/
def deleteStmt (P : Prog) (l : Label) (i : Nat) : Prog :=
  P.setBlk l { P.blk l with stmts := (P.blk l).stmts.eraseIdx i }

/-- Replace the terminator of block `l` (used to turn a `switchInt` into a `goto`). -/
def setTerm (P : Prog) (l : Label) (t : Term) : Prog :=
  P.setBlk l { P.blk l with term := t }

/-- Replace the `i`-th statement of block `l` (used to rewrite `&` and `&raw`). -/
def setStmt (P : Prog) (l : Label) (i : Nat) (s : Stmt) : Prog :=
  P.setBlk l { P.blk l with stmts := (P.blk l).stmts.set i s }

/-- Erase every `storageLive x` and `storageDead x` from every block. In the result `x`
has no markers, so if `x < P.locals.length` it is allocated at entry for the whole run; a
local `x ≥ P.locals.length` is never recorded in the frame, in either program. -/
def eraseMarkers (P : Prog) (x : Local) : Prog :=
  { P with blocks := P.blocks.map fun b =>
      { b with stmts := b.stmts.filter fun s => !s.isMarkerOf x } }

/-- An `Rvalue` that observes addresses: `ptrEq` or `addrOf`. -/
def Rvalue.observesAddr : Rvalue → Bool
  | .ptrEq _ _ => true
  | .addrOf _ => true
  | _ => false

/-- The right-hand side of a statement, if any. -/
def Stmt.rvalue? : Stmt → Option Rvalue
  | .assign _ _ rv => some rv
  | .emit rv => some rv
  | _ => none

/-- `NoAddrObs P`: no statement of `P` has a right-hand side that observes an address
(no `ptrEq`, no `addrOf`). Terminators only read operands, which never observe addresses. -/
def NoAddrObs (P : Prog) : Prop :=
  ∀ b ∈ P.blocks, ∀ s ∈ b.stmts, ∀ rv, s.rvalue? = some rv → rv.observesAddr = false

/-- An operand that is not a pointer constant carrying an allocation identifier. -/
def Operand.provFree : Operand → Bool
  | .const (.ptr q) => q.prov.isNone
  | _ => true

/-- No operand of the right-hand side is a pointer constant with provenance. -/
def Rvalue.provFree : Rvalue → Bool
  | .use o => o.provFree
  | .ptrEq a b => a.provFree && b.provFree
  | .addrOf a => a.provFree
  | _ => true

/-- No operand of the statement is a pointer constant with provenance. -/
def Stmt.provFree : Stmt → Bool
  | .assign _ _ rv => rv.provFree
  | .emit rv => rv.provFree
  | _ => true

/-- No operand of the terminator is a pointer constant with provenance. -/
def Term.provFree : Term → Bool
  | .switchInt o _ _ => o.provFree
  | _ => true

/-- `NoProvConst P`: no operand of `P` (in a statement or a `switchInt` terminator) is a
pointer constant `.const (.ptr ⟨some k, a⟩)` carrying an allocation identifier. Pointer
constants without provenance, such as the null pointer `.ptr ⟨none, 0⟩`, are allowed.
Allocation identifiers count the allocations made so far, so a constant that names one is
not preserved by an edit that adds or removes allocations. -/
def NoProvConst (P : Prog) : Prop :=
  ∀ b ∈ P.blocks, (∀ s ∈ b.stmts, s.provFree = true) ∧ b.term.provFree = true

instance (P : Prog) : Decidable (NoProvConst P) :=
  inferInstanceAs (Decidable (∀ b ∈ P.blocks, (∀ s ∈ b.stmts, s.provFree = true) ∧ b.term.provFree = true))

end Toy.PlaceEval
