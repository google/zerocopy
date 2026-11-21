import Toy.PlaceEval.Place

/-!
# The toy CFG language

Operands, right-hand sides, statements (`placeMention`, assignment, `emit`,
`storageLive`, `storageDead`), terminators (`goto`, `switchInt`, `halt`, `unreachable`),
blocks and programs, together with allocation of locals under two allocation modes:

* `fresh ω` — the address of the `k`-th allocation is `align * (ω k + 1)` (aligned, and
  non-zero when `align ≥ 1`); the
  allocation is refused (the run *blocks*, contributing no behaviour) if its range overlaps
  a live allocation. The oracle `ω` is existentially quantified in `HasBeh`, so this models
  a nondeterministic choice among non-overlapping aligned addresses.
* `slots s` — a static slot assignment: local `x` is always allocated at address `s x`,
  with no overlap check (two locals may share a slot). This mode is deterministic.
-/

namespace Toy.PlaceEval

/-- Basic-block labels. -/
abbrev Label := Nat

/-- Operands: a copy of the value stored in a place, at a type; or a constant. -/
inductive Operand where
  | copy (p : Place) (τ : Ty)
  | const (v : Val)
deriving DecidableEq, Repr

/-- Right-hand sides. `rawRef p` is `&raw p`; `ref p L` is `&p` for a pointee of layout `L`;
`ptrEq a b` compares two pointers by address (1 if equal, 0 otherwise); `addrOf a` casts a
pointer to its address (an integer). -/
inductive Rvalue where
  | use (o : Operand)
  | rawRef (p : Place)
  | ref (p : Place) (L : Layout)
  | ptrEq (a b : Operand)
  | addrOf (a : Operand)
deriving DecidableEq, Repr

/-- Statements. `assign dst τ rv` stores the value of `rv` at type `τ` into place `dst`;
`emit rv` appends the integer value of `rv` to the trace (the only observable event). -/
inductive Stmt where
  | placeMention (p : Place)
  | assign (dst : Place) (τ : Ty) (rv : Rvalue)
  | emit (rv : Rvalue)
  | storageLive (x : Local)
  | storageDead (x : Local)
deriving DecidableEq, Repr

/-- Terminators. `switchInt o arms ow` jumps to the label of the first arm whose value
equals the integer value of `o`, or to `ow`. -/
inductive Term where
  | goto (b : Label)
  | switchInt (o : Operand) (arms : List (Nat × Label)) (ow : Label)
  | halt
  | unreachable
deriving DecidableEq, Repr

/-- A basic block. -/
structure Block where
  stmts : List Stmt
  term : Term
deriving DecidableEq, Repr

/-- The block with no statements and an `unreachable` terminator. -/
def Block.unreach : Block := ⟨[], .unreachable⟩

/-- A program: the layouts of its locals (local `x` has layout `locals[x]`) and its
blocks (execution starts at label `0`). -/
structure Prog where
  locals : List Layout
  blocks : List Block
deriving DecidableEq, Repr

/-- The block at label `l`; a label outside the list denotes `Block.unreach`. -/
def Prog.blk (P : Prog) (l : Label) : Block := P.blocks.getD l Block.unreach

/-- The layout of local `x`; locals outside the list get the empty layout `⟨0, 1⟩`. -/
def Prog.layout (P : Prog) (x : Local) : Layout := P.locals.getD x ⟨0, 1⟩

/-- `s.isMarkerOf x`: `s` is `storageLive x` or `storageDead x`. -/
def Stmt.isMarkerOf (x : Local) : Stmt → Bool
  | .storageLive y => y == x
  | .storageDead y => y == x
  | _ => false

/-- `P.hasMarkers x`: some block of `P` contains a storage marker for `x`. Locals without
markers are allocated at function entry for the whole run. -/
def Prog.hasMarkers (P : Prog) (x : Local) : Bool :=
  P.blocks.any fun b => b.stmts.any (Stmt.isMarkerOf x)

/-! ## Allocation of locals -/

/-- Allocation modes (see the module comment). -/
inductive AllocMode where
  | fresh (ω : Nat → Nat)
  | slots (s : Local → Nat)

/-- The ranges `[a, a + n)` and `[b, b + m)` are disjoint (empty ranges are disjoint from
everything). -/
def disjointRanges (a n b m : Nat) : Bool :=
  n == 0 || m == 0 || decide (a + n ≤ b) || decide (b + m ≤ a)

/-- `allocate mode st x L`: allocate fresh uninitialized memory of layout `L` for local `x`
and record it in the frame. `none` means the oracle choice is refused (the run blocks):
under `fresh ω`, when the chosen range overlaps a live allocation. -/
def allocate (mode : AllocMode) (st : State) (x : Local) (L : Layout) : Option State :=
  let k := st.mem.allocs.length
  let a := match mode with
    | .fresh ω => L.align * (ω k + 1)
    | .slots s => s x
  let ok := match mode with
    | .fresh _ => st.mem.allocs.all fun al => !al.live || disjointRanges a L.size al.base al.size
    | .slots _ => true
  if ok then
    some { mem := { allocs := st.mem.allocs ++ [⟨a, L.size, true⟩],
                    cells := placeCells a (List.replicate L.size .uninit) ++ st.mem.cells },
           frame := st.frame.set x (some k) }
  else none

/-- `deallocate st x`: free the allocation backing `x` (mark it dead) and mark `x`
unallocated; a no-op if `x` is already unallocated. -/
def deallocate (st : State) (x : Local) : State :=
  match st.allocOf x with
  | none => st
  | some k =>
    { mem := { st.mem with allocs := st.mem.allocs.modify k fun al => { al with live := false } },
      frame := st.frame.set x none }

/-! ## Evaluation of operands and right-hand sides -/

/-- Evaluate an operand: `copy p τ` evaluates the place and loads a `τ` value from it. -/
def Operand.eval (st : State) : Operand → Option Val
  | .copy p τ => (evalPlace st p).bind fun q => st.mem.load q τ
  | .const v => some v

/-- `RefOk m q L`: creating a reference to a pointee of layout `L` at `q` is permitted:
`q` is non-null (address `≠ 0`), aligned for `L.align`, and dereferenceable for `L.size`
bytes. -/
def RefOk (m : Mem) (q : Ptr) (L : Layout) : Prop :=
  q.addr ≠ 0 ∧ aligned L.align q.addr = true ∧ m.dereferenceable q L.size = true

instance (m : Mem) (q : Ptr) (L : Layout) : Decidable (RefOk m q L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Evaluate a right-hand side. `rawRef p` needs exactly a successful place evaluation;
`ref p L` additionally needs `RefOk`. -/
def Rvalue.eval (st : State) : Rvalue → Option Val
  | .use o => o.eval st
  | .rawRef p => (evalPlace st p).map Val.ptr
  | .ref p L => (evalPlace st p).bind fun q => if RefOk st.mem q L then some (.ptr q) else none
  | .ptrEq a b =>
    match a.eval st, b.eval st with
    | some (.ptr q), some (.ptr r) => some (.int (if q.addr = r.addr then 1 else 0))
    | _, _ => none
  | .addrOf a =>
    match a.eval st with
    | some (.ptr q) => some (.int q.addr)
    | _ => none

/-- The integer value of an operand (`none` if evaluation fails or yields a pointer). -/
def Operand.evalInt (st : State) (o : Operand) : Option Nat :=
  match o.eval st with
  | some (.int n) => some n
  | _ => none

/-! ## Statement execution -/

/-- Result of executing a statement: continue with an optional emitted value and a new
state, UB, or block (a refused oracle choice). -/
inductive StmtResult where
  | ok (ev : Option Nat) (st : State)
  | ub
  | block

/-- Execute one statement. `placeMention p` evaluates `p` and discards the result.
`assign` evaluates the destination place, then the right-hand side, then stores.
`storageLive x` frees any allocation of `x` and allocates fresh uninitialized memory;
`storageDead x` frees `x` (a no-op if already unallocated). -/
def execStmt (mode : AllocMode) (P : Prog) (st : State) : Stmt → StmtResult
  | .placeMention p => if (evalPlace st p).isSome then .ok none st else .ub
  | .assign dst τ rv =>
    match evalPlace st dst with
    | none => .ub
    | some q =>
      match rv.eval st with
      | none => .ub
      | some v =>
        match st.mem.store q τ v with
        | some m => .ok none { st with mem := m }
        | none => .ub
  | .emit rv =>
    match rv.eval st with
    | some (.int n) => .ok (some n) st
    | _ => .ub
  | .storageLive x =>
    match allocate mode (deallocate st x) x (P.layout x) with
    | some st' => .ok none st'
    | none => .block
  | .storageDead x => .ok none (deallocate st x)

end Toy.PlaceEval
