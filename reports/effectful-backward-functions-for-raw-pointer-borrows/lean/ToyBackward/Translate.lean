import ToyBackward.Lang

/-!
# Translations into a functional target with forward and backward functions

The target mirrors how a functional translation of Rust treats a mutable borrow: creating the
borrow calls a *forward* function that returns the borrowed value; the program then works on that
value as an ordinary local (`lread`, `lwrite`); when the borrow's region ends, a *backward*
function is called with the final value of the borrow.

For `as_mut : *mut i32 → &mut i32` there is no owner value to hand the final value back to: the
owner is a memory cell reachable only through a raw pointer. The translations below differ only
in what the target's forward/backward calls may do:

* `effSem` — **effectful backward functions**: the target threads a heap model; the forward call
  of region `i` reads the heap, and its backward call `back i` writes the final value back to the
  heap. Where the backward calls go is a parameter (`Placement`). The write-back is *unchecked*:
  while a region is open its cell stays freely accessible in the heap model (copy-in/copy-out),
  and the region's local value stays readable and writable after its backward call.
* `lockSem` — **borrow-locking effectful backward functions**: as `effSem`, but the forward call
  lends the cell to the region (any other access to a lent cell, and any second loan of it, is
  stuck), the backward call returns the cell and closes the region (later uses of the region are
  stuck), and a run that ends with a cell still lent is stuck (the final observation is an access
  by the owner). This is the toy counterpart of heap models that mark a cell as borrowed until the
  backward function runs.
* `pureBackSem` — **pure backward functions**: as `effSem` (the forward call still reads the heap
  model), but backward functions have no effect, so they are simply absent.
* `statelessSem F B` — **stateless target**: no heap model at all; the forward call of `as_mut p`
  returns `F p` (or fails) and the backward call may fail (per `B`) but has no other effect, for
  arbitrary models `F` and `B`. It is meant to capture translations into a target whose only
  effects are failure and divergence (a diverging call is modelled like a failing one: it produces
  no observation) and that thread no state, where `as_mut` becomes an opaque
  `Ptr → Result (Int × (Int → Result Unit))` or `Ptr → Result (Int × (Int → Unit))`.
* `prophSem` — **prophecy encoding** in the style of RustHorn: creating the borrow hands the
  owner a prophesied final value `φ i`, and the end of the region *assumes* the borrow's final
  value equals the prophecy.
-/

namespace Toy.Backward

/-- Target statements.

* `fwd i p` — forward call of `as_mut p` for region `i`: binds slot `i` to `(p, value)`.
* `lread x i` / `lwrite i e` — pure reads/updates of the local value held in slot `i`.
* `back i` — backward call of region `i`, given the current value of slot `i`.
* `rawRead x p` / `rawWrite p e` — raw-pointer accesses, interpreted on the heap model. -/
inductive TStmt where
  | fwd (i : Nat) (p : Ptr)
  | lread (x : XVar) (i : Nat)
  | lwrite (i : Nat) (e : Expr)
  | back (i : Nat)
  | rawRead (x : XVar) (p : Ptr)
  | rawWrite (p : Ptr) (e : Expr)
  deriving DecidableEq, Repr

/-- State of the effectful target: a heap model, one slot per region holding the region's pointer
and the current local value of the borrow, and the local variables. -/
structure TState where
  heap : Heap
  slots : Nat → Option (Ptr × Int)
  vars : Env

/-- Initial target state. -/
def TState.init (h : Heap) : TState := ⟨h, fun _ => none, fun _ => 0⟩

/-- Observation of a target state. -/
def TState.obs (s : TState) : Obs := ⟨s.heap, s.vars⟩

/-- One step of the effectful target. The backward call `back i` writes the slot's current value
to the slot's address. A slot stays readable after its backward call (the forward value is an
ordinary immutable binding in the functional target). Using an unbound slot is stuck. -/
def tstep (s : TState) : TStmt → Option TState
  | .fwd i p => some { s with slots := upd s.slots i (some (p, s.heap p)) }
  | .lread x i =>
    match s.slots i with
    | some (_, v) => some { s with vars := upd s.vars x v }
    | none => none
  | .lwrite i e =>
    match s.slots i with
    | some (p, _) => some { s with slots := upd s.slots i (some (p, e.eval s.vars)) }
    | none => none
  | .back i =>
    match s.slots i with
    | some (p, v) => some { s with heap := upd s.heap p v }
    | none => none
  | .rawRead x p => some { s with vars := upd s.vars x (s.heap p) }
  | .rawWrite p e => some { s with heap := upd s.heap p (e.eval s.vars) }

/-- Run a target program. -/
def trun : List TStmt → TState → Option TState
  | [], s => some s
  | c :: cs, s =>
    match tstep s c with
    | some s' => trun cs s'
    | none => none

/-- Translation of one source statement at index `k` (region names are source indices). -/
def trStmt (k : Nat) : Stmt → TStmt
  | .asMut p => .fwd k p
  | .read x r => .lread x r
  | .write r e => .lwrite r e
  | .rawRead x p => .rawRead x p
  | .rawWrite p e => .rawWrite p e

/-- `isRegion P i`: statement `i` of `P` is an `asMut`, i.e. `i` names a region. -/
def isRegion (P : Prog) (i : Nat) : Bool :=
  match P[i]? with
  | some (.asMut _) => true
  | _ => false

/-- **Region end placement.** `π i = k` means: the backward function of region `i` is called
immediately before source statement `k` (`k = P.length` means at the end of the program; any
larger `k` means never). Only values at region indices matter. -/
abbrev Placement := Nat → Nat

/-- Backward calls scheduled immediately before statement `k`, in increasing region order. -/
def backsAt (P : Prog) (π : Placement) (k : Nat) : List TStmt :=
  ((List.range P.length).filter fun i => isRegion P i && π i == k).map TStmt.back

/-- Translate the statements from index `k` on, inserting the scheduled backward calls. -/
def translateFrom (P : Prog) (π : Placement) : Nat → List Stmt → List TStmt
  | _, [] => []
  | k, c :: cs => backsAt P π k ++ trStmt k c :: translateFrom P π (k + 1) cs

/-- **Effectful translation** of `P` with region ends placed by `π`. -/
def translate (P : Prog) (π : Placement) : List TStmt :=
  translateFrom P π 0 P ++ backsAt P π P.length

/-- **Semantics of the effectful-backward translation**: run the translated program on the heap
model and observe the final heap model and variables. -/
def effSem (P : Prog) (π : Placement) (h : Heap) : Option Obs :=
  (trun (translate P π) (TState.init h)).map TState.obs

/-- Translation with **pure (effect-free) backward functions**: a backward function returning
`Unit` with no effect contributes nothing, so no backward calls appear. -/
def translatePureBack : Nat → Prog → List TStmt
  | _, [] => []
  | k, c :: cs => trStmt k c :: translatePureBack (k + 1) cs

/-- **Semantics of the pure-backward translation.** Forward calls still read the heap model. -/
def pureBackSem (P : Prog) (h : Heap) : Option Obs :=
  (trun (translatePureBack 0 P) (TState.init h)).map TState.obs

/-! ## Borrow-locking target -/

/-- State of the borrow-locking target: a heap model, one slot per *open* region (its pointer and
the current local value of the borrow), which cells are currently lent to an open region, the
number of open regions, and the local variables. -/
structure LState where
  heap : Heap
  slots : Nat → Option (Ptr × Int)
  lent : Ptr → Bool
  openCount : Nat
  vars : Env

/-- Initial borrow-locking state: given memory, no open regions, nothing lent. -/
def LState.init (h : Heap) : LState := ⟨h, fun _ => none, fun _ => false, 0, fun _ => 0⟩

/-- One step of the borrow-locking target.

* `fwd i p` is stuck if `p` is already lent; otherwise it opens region `i` with the cell's current
  value and lends `p`.
* `lread`/`lwrite` act on an open region only (stuck after the region's backward call).
* `back i` writes the region's final value to the heap, returns the cell, and closes the region.
* raw reads and writes of a lent cell are stuck. -/
def lstep (s : LState) : TStmt → Option LState
  | .fwd i p =>
    if s.lent p then none
    else some { s with slots := upd s.slots i (some (p, s.heap p)), lent := upd s.lent p true,
                       openCount := s.openCount + 1 }
  | .lread x i =>
    match s.slots i with
    | some (_, v) => some { s with vars := upd s.vars x v }
    | none => none
  | .lwrite i e =>
    match s.slots i with
    | some (p, _) => some { s with slots := upd s.slots i (some (p, e.eval s.vars)) }
    | none => none
  | .back i =>
    match s.slots i with
    | some (p, v) =>
      some { s with heap := upd s.heap p v, slots := upd s.slots i none, lent := upd s.lent p false,
                    openCount := s.openCount - 1 }
    | none => none
  | .rawRead x p => if s.lent p then none else some { s with vars := upd s.vars x (s.heap p) }
  | .rawWrite p e => if s.lent p then none else some { s with heap := upd s.heap p (e.eval s.vars) }

/-- Run a borrow-locking target program. -/
def lrun : List TStmt → LState → Option LState
  | [], s => some s
  | c :: cs, s =>
    match lstep s c with
    | some s' => lrun cs s'
    | none => none

/-- **Semantics of the borrow-locking translation** with region ends placed by `π`: run the same
translated program as `effSem`, and observe the final heap and variables only if no region is
still open (a cell still lent at the end cannot be observed by its owner; the run is stuck). -/
def lockSem (P : Prog) (π : Placement) (h : Heap) : Option Obs :=
  match lrun (translate P π) (LState.init h) with
  | some s => if s.openCount = 0 then some ⟨s.heap, s.vars⟩ else none
  | none => none

/-! ## Stateless target -/

/-- State of a stateless target: per-region slots (pointer and current local value) and local
variables; no heap model. -/
structure SState where
  vals : Nat → Option (Ptr × Int)
  vars : Env

/-- Initial stateless state. -/
def SState.init : SState := ⟨fun _ => none, fun _ => 0⟩

/-- One step of a stateless target with forward model `F` and backward model `B`. The forward call
of `as_mut p` returns `F p` or fails (`F p = none`); the backward call of a region whose slot holds
`(p, v)` succeeds iff `B p v`, and has no other effect; raw reads return `F p` (or fail); raw writes
have nothing to act on. Meant to capture translations into a target whose only effect is failure
and that thread no state, where `as_mut` becomes an opaque `Ptr → Result (Int × (Int → Result Unit))`. -/
def sstep (F : Ptr → Option Int) (B : Ptr → Int → Bool) (s : SState) : TStmt → Option SState
  | .fwd i p =>
    match F p with
    | some v => some { s with vals := upd s.vals i (some (p, v)) }
    | none => none
  | .lread x i =>
    match s.vals i with
    | some (_, v) => some { s with vars := upd s.vars x v }
    | none => none
  | .lwrite i e =>
    match s.vals i with
    | some (p, _) => some { s with vals := upd s.vals i (some (p, e.eval s.vars)) }
    | none => none
  | .back i =>
    match s.vals i with
    | some (p, v) => if B p v then some s else none
    | none => none
  | .rawRead x p =>
    match F p with
    | some v => some { s with vars := upd s.vars x v }
    | none => none
  | .rawWrite _ _ => some s

/-- Run a stateless target program. -/
def srun (F : Ptr → Option Int) (B : Ptr → Int → Bool) : List TStmt → SState → Option SState
  | [], s => some s
  | c :: cs, s =>
    match sstep F B s c with
    | some s' => srun F B cs s'
    | none => none

/-- **Semantics of a stateless translation** with forward model `F`, backward model `B`, and region
ends placed by `π`: only local variables are observable (there is no heap model). -/
def statelessSem (F : Ptr → Option Int) (B : Ptr → Int → Bool) (P : Prog) (π : Placement) :
    Option Env :=
  (srun F B (translate P π) SState.init).map SState.vars

/-! ## Prophecy encoding -/

/-- State of the prophecy encoding: as `TState`, plus a flag recording whether every
resolution assumption so far held. -/
structure PState where
  heap : Heap
  slots : Nat → Option (Ptr × Int)
  vars : Env
  ok : Bool

/-- One step of the prophecy encoding with prophecy assignment `φ`. Creating region `i` binds the
borrow to the cell's current value and hands the owner (the cell) the prophecy `φ i`; ending the
region assumes the borrow's final value equals `φ i` (recorded in `ok`). -/
def pstep (φ : Nat → Int) (s : PState) : TStmt → Option PState
  | .fwd i p => some { s with slots := upd s.slots i (some (p, s.heap p)), heap := upd s.heap p (φ i) }
  | .lread x i =>
    match s.slots i with
    | some (_, v) => some { s with vars := upd s.vars x v }
    | none => none
  | .lwrite i e =>
    match s.slots i with
    | some (p, _) => some { s with slots := upd s.slots i (some (p, e.eval s.vars)) }
    | none => none
  | .back i =>
    match s.slots i with
    | some (_, v) => some { s with ok := s.ok && decide (v = φ i) }
    | none => none
  | .rawRead x p => some { s with vars := upd s.vars x (s.heap p) }
  | .rawWrite p e => some { s with heap := upd s.heap p (e.eval s.vars) }

/-- Run a program in the prophecy encoding. -/
def prun (φ : Nat → Int) : List TStmt → PState → Option PState
  | [], s => some s
  | c :: cs, s =>
    match pstep φ s c with
    | some s' => prun φ cs s'
    | none => none

/-- **Prophecy-encoding semantics** of the translated program for one prophecy assignment `φ`:
the observation and whether all resolution assumptions held. -/
def prophSem (P : Prog) (π : Placement) (h : Heap) (φ : Nat → Int) : Option (Obs × Bool) :=
  (prun φ (translate P π) ⟨h, fun _ => none, fun _ => 0, true⟩).map fun s => (⟨s.heap, s.vars⟩, s.ok)

/-- `o` is an outcome of the prophecy encoding: some prophecy assignment satisfies every
resolution assumption and produces `o`. -/
def ProphOutcome (P : Prog) (π : Placement) (h : Heap) (o : Obs) : Prop :=
  ∃ φ, prophSem P π h φ = some (o, true)

end Toy.Backward
