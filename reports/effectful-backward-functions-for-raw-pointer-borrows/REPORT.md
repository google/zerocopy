# Effectful backward functions for raw-pointer borrows: when write-back, borrow-locking, and prophecy translations agree with a heap semantics (Lean toy model)

## Summary

A Lean 4 model of translating unsafe-Rust raw-pointer reborrows (`&mut *p`, `p.as_mut()`) into a functional target with forward and backward functions. Every result below is kernel-checked in a toy model of straight-line programs over integer cells; nothing is proved about any real tool, and every connection to one is a separately labeled derived modeling bridge.

- **sound-lazy.** For every toy program that obeys the aliasing discipline and every initial heap, the effectful-backward (unchecked write-back) translation that ends each region at the owner's next access to its cell, or at the program end, has exactly the heap semantics' outcome: both succeed with the same final heap and local variables, or both are stuck.
- **sound-eager.** The same holds, for programs that obey the aliasing discipline, when each region ends immediately after the later of its creation and its last use (`max i (last use) + 1`).
- **pure-backward-unsound.** On the program `reborrowAfterWrite c`, which obeys the aliasing discipline, and for every initial heap `h` with `c ≠ h 0`, the translation whose backward functions have no effect succeeds with final heap `h` and binds the second reborrow's read to the stale `h 0`, while the heap semantics ends with `h[0 ↦ c]` and reads `c`.
- **stateless-unsound.** For every stateless model of `as_mut` (forward result a function of the pointer or a failure, backward calls that may fail but have no other effect, any placement of backward calls) and every `c ≠ h 0`, every successful run of the translated `reborrowAfterWrite c` gives the two `as_mut` calls equal results (`x0 = x1`, the equation duplicate-call merging relies on), the heap semantics has `x0 ≠ x1`, so the stateless translation fails or computes wrong local variables.
- **endpoint-window.** For every toy program and every placement that ends each region after its creation, after its last use, no later than the owner's next access to its cell, and no later than the program end, the unchecked write-back translation has exactly the heap semantics' outcome (both succeed with the same observation, or both are stuck); the aliasing discipline follows from these conditions and is not assumed.
- **endpoint-window-last-write.** For programs that obey the aliasing discipline, the same holds when "after its last use" is weakened to "after its last write" (reads through the reference may follow the region's end).
- **lock-complete.** For every placement meeting the four conditions of endpoint-window (after creation, after last use, no later than the owner's next access, no later than the program end), the borrow-locking translation (the forward call lends the cell to the region; other accesses to a lent cell, uses of a closed region, and a run ending with a lent cell are stuck) has exactly the heap semantics' outcome.
- **lock-success-in-window.** For every program, placement, and initial heap, if the borrow-locking translation succeeds, the placement meets all four of those conditions (it is liveness-respecting).
- **lock-sound.** For every program, every placement (inside or outside the window), and every initial heap, if the borrow-locking translation succeeds with observation `o`, the heap semantics succeeds with the same `o`: a placement can make it stuck, never wrong.
- **prophecy-agreement.** If every region ends no later than the owner's next access to its cell and no later than the program end, the outcomes of the prophecy encoding (over all prophecy assignments satisfying every resolution assumption) are exactly the unchecked write-back translation's outcome (a single outcome, or none if it is stuck).
- **prophecy-sound-wider-window.** For programs that obey the aliasing discipline and placements that end each region after its creation, after its last write, and no later than the program end, but possibly after the owner's next access, the prophecy encoding's outcomes are exactly the heap semantics' outcome (a single outcome, or none if the heap semantics is stuck).
- **aliasing-iff-placement.** For every toy program, the aliasing discipline holds iff the lazy placement is liveness-respecting, iff the eager placement is liveness-respecting, iff some placement is liveness-respecting.

Every result has non-claims that restrict how it may be read; they are listed first under **Boundaries**, per result. Every hypothesis of every result is shown necessary by a kernel-checked counterexample.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity.** A toy model. Straight-line programs over a flat heap of integer cells (`Heap := Nat → Int`); raw
pointers are bare addresses (`Ptr := Nat`); one reborrow operation `asMut p` (`&mut *p`,
`p.as_mut()`); reads and writes through references and through raw pointers. The *heap semantics*
`heapSem` is the ground truth: a reference denotes an address, every access goes to memory, and there
are no aliasing rules and no region ends. The aliasing rules enter only as the hypothesis
`AliasingDiscipline` (an ordering condition in the spirit of Stacked Borrows, specialised to this
fragment; it does not check reference scoping), and region ends only as a translation parameter
`Placement`.

Two effectful-backward translations share one target program and differ in how the target treats the
heap model while a region is open:

* `effSem` — **unchecked write-back** (copy-in/copy-out): the forward call copies the cell into the
  region, the cell stays freely accessible in the heap model, the backward call copies the region's
  final value back, and the region's local value stays readable and writable afterwards.
* `lockSem` — **borrow-locking write-back**: the forward call lends the cell to the region; any other
  access to a lent cell, any use of a closed region, and a run that ends with a cell still lent are
  stuck. This is the toy counterpart of heap models that mark a cell as borrowed until the backward
  function runs.

Soundness is stated either as equality of outcomes (`effSem P π h = heapSem P h`: both succeed with
the same observation, or both are stuck) or, for `lock-sound`, as partial refinement
(`lockSem P π h = some o → heapSem P h = some o`), under which a stuck translation is incomplete,
not unsound.

Absent: allocation and deallocation, pointer arithmetic, casts, typed or uninitialised memory,
provenance, control flow (branches, loops, joins), function calls and function boundaries, shared
references, reference-to-raw-pointer conversion (`from_mut`) as a region, reborrows of references,
interior mutability, concurrency, intermediate assertions or panics. No connection to any real tool
is kernel-checked; statements about Aeneas below are modeling bridges, not theorems.

**What the definitions are meant to capture.** `heapSem` captures the ground-truth behaviour of the reborrow pattern: a reference is an address and every access goes to memory. `effSem` captures translations in which `as_mut`'s backward function writes the borrow's final value back to a heap model without restricting the cell while the region is open; `lockSem` captures heap models that mark a cell as borrowed until the backward function runs; `pureBackSem` captures effect-free backward functions; `statelessSem F B` captures targets whose only effects are failure and divergence and that thread no state; `prophSem` captures prophecy encodings in the style of RustHorn. Known gaps are listed under **Boundaries**.

**Lean.** Toolchain `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean and `Std` only, **no Mathlib**, no Lake dependencies. Library `ToyBackward` in `lean/` (namespace `Toy.Backward`; proof infrastructure in `Toy.Backward.Sim`).

**Subjects.** `REPORT.json` lists the Lean toolchain release (the checker of every theorem), the published papers cited as prior art, and the Creusot source repository at commit 601d97891bb0bc0b569686cc946ef4980560b5d8 (a published revision on its main branch, cited under `prophecy-sound-wider-window` for its raw-pointer permission type). The papers and the Creusot source are compared with, not formalized: no theorem here restates a theorem of theirs, and no finding depends on their correctness. Aeneas pull requests (#1537 and companions) are unmerged proposals; they are cited as context in the prose, identified by head commit, and are not subjects.

## Findings

### Definitions

Notation used in the unfolded statements: `n = P.length`; *region i* means `i < n ∧ P[i] = asMut p`
for some `p` (`isRegion P i`); *owner(i, k)* means region `i` has pointer `p`, `i < k < n`, and
`P[k]` is `asMut p`, `rawRead _ p`, or `rawWrite p _` (`ownerAccessAfter P i k`); `obs s = ⟨s.heap, s.vars⟩`;
`⟨h, ∅, 0⟩` is the state with heap `h`, no references/slots, all variables `0`; `hc`, `hu`, `hw`,
`ho`, `he` abbreviate `EndsAfterCreation`, `EndsAfterLastUse`, `EndsAfterLastWrite`,
`EndsByNextOwnerAccess`, `EndsByProgramEnd`.


#### Source language and heap semantics (`ToyBackward/Lang.lean`)

```lean
/-- Raw pointers are opaque addresses. -/
abbrev Ptr := Nat

/-- Memory: every address holds an integer. Captures a flat, always-initialised address space. -/
abbrev Heap := Ptr → Int

/-- Names of integer local variables. -/
abbrev XVar := Nat

/-- Integer local-variable environments. -/
abbrev Env := XVar → Int

/-- Point update of a `Nat`-indexed map: `upd f k v` agrees with `f` except that it sends `k` to `v`.
Used for heaps, environments, and slot tables alike. -/
def upd {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun j => if j = k then v else f j

/-- Pure integer expressions over local variables. -/
inductive Expr where
  | lit (n : Int)
  | var (x : XVar)
  | add (a b : Expr)
  deriving DecidableEq, Repr

/-- Evaluation of expressions in an environment. -/
def Expr.eval (ρ : Env) : Expr → Int
  | .lit n => n
  | .var x => ρ x
  | .add a b => a.eval ρ + b.eval ρ

/-- Source statements.

* `asMut p` — `let r = unsafe { &mut *p }` (equivalently `p.as_mut()`): creates a mutable
  reference to the cell at address `p`. The reference is named by the index of this statement.
* `read x r` — `let x = *r`, through the reference created at index `r`.
* `write r e` — `*r = e`, through the reference created at index `r`.
* `rawRead x p` — `let x = unsafe { *p }`, through the raw pointer.
* `rawWrite p e` — `unsafe { *p = e }`, through the raw pointer. -/
inductive Stmt where
  | asMut (p : Ptr)
  | read (x : XVar) (r : Nat)
  | write (r : Nat) (e : Expr)
  | rawRead (x : XVar) (p : Ptr)
  | rawWrite (p : Ptr) (e : Expr)
  deriving DecidableEq, Repr

/-- Straight-line programs. Statement `i` of `P` is `P[i]`. -/
abbrev Prog := List Stmt

/-- What a run produces: the final heap and the final local variables. -/
structure Obs where
  heap : Heap
  vars : Env

/-- Machine state of the heap semantics: memory, the address each created reference denotes,
and the local variables. -/
structure HState where
  heap : Heap
  refs : Nat → Option Ptr
  vars : Env

/-- Initial heap-semantics state: given memory, no references, all variables `0`. -/
def HState.init (h : Heap) : HState := ⟨h, fun _ => none, fun _ => 0⟩

/-- One step of the heap semantics for the statement at index `i`. Using a reference that has
not been created (or a name that is not an `asMut` index) is stuck (`none`). -/
def hstep (i : Nat) (s : HState) : Stmt → Option HState
  | .asMut p => some { s with refs := upd s.refs i (some p) }
  | .read x r =>
    match s.refs r with
    | some p => some { s with vars := upd s.vars x (s.heap p) }
    | none => none
  | .write r e =>
    match s.refs r with
    | some p => some { s with heap := upd s.heap p (e.eval s.vars) }
    | none => none
  | .rawRead x p => some { s with vars := upd s.vars x (s.heap p) }
  | .rawWrite p e => some { s with heap := upd s.heap p (e.eval s.vars) }

/-- Run a statement list whose first statement has index `i`. -/
def hrun : Nat → List Stmt → HState → Option HState
  | _, [], s => some s
  | i, c :: cs, s =>
    match hstep i s c with
    | some s' => hrun (i + 1) cs s'
    | none => none

/-- **Heap semantics.** The reference semantics of the toy language: references are addresses,
every access goes to memory, region ends do not exist. `none` means the program used a reference
that does not exist (a scoping error), never an aliasing violation: this semantics has no aliasing
rules at all. -/
def heapSem (P : Prog) (h : Heap) : Option Obs :=
  (hrun 0 P (HState.init h)).map fun s => ⟨s.heap, s.vars⟩

```

#### Target and translations (`ToyBackward/Translate.lean`)

```lean
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

```

#### Aliasing discipline and placement conditions (`ToyBackward/Liveness.lean`)

```lean
/-- Statement reads or writes through reference `r`. -/
def Stmt.usesRef (r : Nat) : Stmt → Bool
  | .read _ r' => r' == r
  | .write r' _ => r' == r
  | _ => false

/-- Statement writes through reference `r`. -/
def Stmt.writesRef (r : Nat) : Stmt → Bool
  | .write r' _ => r' == r
  | _ => false

/-- Statement accesses the cell `p` other than through an existing reference:
`asMut p`, `rawRead _ p`, or `rawWrite p _`. -/
def Stmt.touchesOwner (p : Ptr) : Stmt → Bool
  | .asMut q => q == p
  | .rawRead _ q => q == p
  | .rawWrite q _ => q == p
  | _ => false

/-- `usesAt P j i`: statement `j` of `P` reads or writes through the reference created at `i`. -/
def usesAt (P : Prog) (j i : Nat) : Bool :=
  match P[j]? with
  | some c => c.usesRef i
  | none => false

/-- `writesAt P j i`: statement `j` of `P` writes through the reference created at `i`. -/
def writesAt (P : Prog) (j i : Nat) : Bool :=
  match P[j]? with
  | some c => c.writesRef i
  | none => false

/-- `ownerAccessAfter P i k`: statement `i` is `asMut p`, `i < k`, and statement `k` accesses the
cell `p` by another path (the *owner* — the raw pointer — accesses the cell again). -/
def ownerAccessAfter (P : Prog) (i k : Nat) : Bool :=
  match P[i]?, P[k]? with
  | some (.asMut p), some c => decide (i < k) && c.touchesOwner p
  | _, _ => false

/-- **Aliasing discipline.** Every use of the reference created at `i` precedes every later owner
access to its cell. This paraphrases the `as_mut` safety requirement (while the returned reference
is in use, the memory is not accessed through any other pointer), specialised to this fragment and
to *uses* of the reference rather than its existence. It is a property of the program only, not of
any translation. It does **not** check reference scoping (that every used reference name is an
earlier `asMut`): ill-scoped programs such as `[read 0 0]` satisfy it and are stuck in every
semantics of this package. -/
def AliasingDiscipline (P : Prog) : Prop :=
  ∀ i, i < P.length → ∀ j, j < P.length → ∀ k, k < P.length →
    usesAt P j i = true → ownerAccessAfter P i k = true → j < k

/-- **Region `i` ends after its creation**: its backward call is scheduled strictly after the
`asMut` statement that creates it. -/
def EndsAfterCreation (P : Prog) (π : Placement) : Prop :=
  ∀ i, i < P.length → isRegion P i = true → i < π i

/-- **Region `i` ends after its last use** (read or write) through its reference: every statement
that uses the reference precedes the region's backward call. (Says nothing about regions without
uses; see `EndsAfterCreation`.) -/
def EndsAfterLastUse (P : Prog) (π : Placement) : Prop :=
  ∀ i, i < P.length → isRegion P i = true →
    ∀ j, j < P.length → usesAt P j i = true → j < π i

/-- **Region `i` ends after its last write** through its reference (reads may follow the end). -/
def EndsAfterLastWrite (P : Prog) (π : Placement) : Prop :=
  ∀ i, i < P.length → isRegion P i = true →
    ∀ j, j < P.length → writesAt P j i = true → j < π i

/-- **Region `i` ends no later than the owner's next access** to its cell: for every later
statement `k` that accesses the cell by another path, the backward call of `i` is scheduled
at or before `k` (backward calls scheduled at `k` run before statement `k`). -/
def EndsByNextOwnerAccess (P : Prog) (π : Placement) : Prop :=
  ∀ i, i < P.length → ∀ k, k < P.length → ownerAccessAfter P i k = true → π i ≤ k

/-- **Region `i` ends no later than the end of the program**, where the final heap is observed
(the final observation is the owner's last access). -/
def EndsByProgramEnd (P : Prog) (π : Placement) : Prop :=
  ∀ i, i < P.length → isRegion P i = true → π i ≤ P.length

/-- **Liveness-respecting placement**: every region ends after its creation, after its last use,
no later than the owner's next access to its cell, and no later than the end of the program. A
named conjunction of four separate conditions, for prose and for the characterization below; the
main theorems list the conditions separately. -/
def RespectsLiveness (P : Prog) (π : Placement) : Prop :=
  EndsAfterCreation P π ∧ EndsAfterLastUse P π ∧ EndsByNextOwnerAccess P π ∧ EndsByProgramEnd P π

/-- Least `j < n` with `f j`, or `n` if there is none. -/
def firstBelow (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let m := firstBelow f n
    if m < n then m else if f n then n else n + 1

/-- Largest `j < n` with `f j`, or the default `d` if there is none. -/
def lastBelow (f : Nat → Bool) (d : Nat) : Nat → Nat
  | 0 => d
  | n + 1 => if f n then n else lastBelow f d n

/-- **Lazy placement**: end region `i` exactly at the owner's next access to its cell, or at the end
of the program if there is none ("end a borrow only when the owner needs the value back"). -/
def lazyPlacement (P : Prog) : Placement :=
  fun i => firstBelow (ownerAccessAfter P i) P.length

/-- **Eager placement**: end region `i` immediately after the later of its creation and its last
use, `max i (last use) + 1` (so after its last use if that use follows the creation, and right
after its creation if the region has no use after it). Uses that precede the creation (a scoping
error) do not pull the end before the creation. Approximately where non-lexical lifetimes would
end the region. -/
def eagerPlacement (P : Prog) : Placement :=
  fun i => max i (lastBelow (fun j => usesAt P j i) i P.length) + 1

/-- A placement that never schedules any backward call of `P`. -/
def neverEndPlacement (P : Prog) : Placement := fun _ => P.length + 1

```

#### Named programs and placements (`ToyBackward/Programs.lean`)

| Name | Program / placement | Rust reading |
| :--- | :--- | :--- |
| `reborrowAfterWrite c` | `[asMut 0, read 0 0, write 0 (lit c), asMut 0, read 1 3]` | `r0 = &mut *p; x0 = *r0; *r0 = c; r3 = &mut *p; x1 = *r3` (obeys the discipline) |
| `rawWriteDuringBorrow` | `[asMut 0, rawWrite 0 (lit 7), read 0 0]` | raw write while `r0` is in use (violates the discipline) |
| `writeThenRead c` | `[asMut 0, write 0 (lit c), read 0 0]` | write then read through one reference |
| `readAfterRawWrite` | `[asMut 0, write 0 (lit 5), rawWrite 0 (lit 7), read 0 0]` | read through `r0` after a raw write (violates the discipline) |
| `writeOnce` | `[asMut 0, write 0 (lit 5)]` | one write |
| `writeThenOtherThenRawRead` | `[asMut 0, write 0 (lit 5), rawRead 1 1, rawRead 2 0]` | liveness window of region 0 has two end points (before 2 and before 3) |
| `unusedRegion` | `[asMut 0]` | a reborrow that is never used |
| `ownerReadThenWriteBack` | `[asMut 0, rawRead 0 0, write 0 (add (var 0) (lit 1))]` | `r0 = &mut *p; x0 = *p; *r0 = x0 + 1` (violates the discipline) |
| `danglingUse` | `[read 0 0]` | use of a reference never created (scoping error) |
| `useBeforeCreation` | `[read 0 1, asMut 0]` | use of a reference before its creation (scoping error) |
| `zeroHeap` | `fun _ => 0` | |
| `endAt k` | `fun _ => k` | every region ends before statement `k` |
| `endBeforeWrite` | `fun i => if i = 0 then 2 else 5` | region 0 ends before its write (too early) |
| `endAfterReborrow` | `fun i => if i = 0 then 4 else 5` | region 0 ends after the second `asMut` of its pointer (too late) |

#### Definition examples (`ToyBackward/Examples.lean`, all fully proved)

| Definition | Captures | Positive (admits) | Negative (rejects) |
| :--- | :--- | :--- | :--- |
| `heapSem` | ground-truth reference semantics; no aliasing rules, no region ends | `heapSem_example_writeThenRead`, `heapSem_example_alias_visible` | `heapSem_example_danglingUse`, `heapSem_example_useBeforeCreation` (stuck) |
| `isRegion` | index of an `asMut` statement | `isRegion_examples` (first conjunct) | `isRegion_examples` (second and third conjuncts) |
| `translate`, `effSem` | unchecked effectful backward functions: `back i` writes the borrow's final value to the heap model | `translate_example_writeThenRead`, `effSem_example_writeThenRead`, `effSem_example_write_back_deferred`, `effSem_example_write_after_back_lost` | `translate_example_no_back_for_nonregion`, `effSem_example_end_before_creation` (stuck) |
| `lockSem` | borrow-locking effectful backward functions | `lockSem_example_writeThenRead`, `lockSem_example_reborrowAfterWrite` | `lockSem_example_owner_access_while_lent`, `lockSem_example_use_after_back`, `lockSem_example_second_loan`, `lockSem_example_never_returned` (all stuck) |
| `pureBackSem` | backward functions without effect (absent) | `pureBackSem_example_writeThenRead` (local write visible locally, never in memory) | `pureBackSem_example_danglingUse` |
| `statelessSem F B` | any translation whose only effects are failure (and divergence, modelled as failure): forward result a function of the pointer, backward calls may fail | `statelessSem_example_forward` | `statelessSem_example_forward_fails`, `statelessSem_example_backward_fails`, `statelessSem_example_rawWrite_invisible` |
| `prophSem`, `ProphOutcome` | RustHorn-style prophecy encoding: lender receives the prophecy, region end assumes final = current, filtered at the end of the run | `prophSem_example_correct_prophecy`, `prophOutcome_example` | `prophSem_example_wrong_prophecy`, `prophOutcome_example_neg` (every outcome has the written value) |
| `AliasingDiscipline` | uses of a reference precede the owner's next access to the cell (no scoping check) | `aliasingDiscipline_reborrowAfterWrite` | `not_aliasingDiscipline_rawWriteDuringBorrow`, `not_aliasingDiscipline_readAfterRawWrite`, `not_aliasingDiscipline_ownerReadThenWriteBack`; documented limitation `aliasingDiscipline_admits_ill_scoped` |
| `EndsAfterCreation` | the backward call follows the forward call | `endsAfterCreation_examples` (left) | `endsAfterCreation_examples` (right) |
| `EndsAfterLastUse`, `EndsByNextOwnerAccess`, `RespectsLiveness` | the liveness window | `respectsLiveness_example`, `endsByNextOwnerAccess_examples` (left), `endsAfterLastUse_example_unused` | `endsAfterLastUse_example_neg`, `endsByNextOwnerAccess_examples` (right), `respectsLiveness_example_neg` |
| `EndsAfterLastWrite` | a wider window: after the last write | `endsAfterLastWrite_example_pos` (and not `EndsAfterLastUse`) | `endsAfterLastWrite_example_neg` |
| `EndsByProgramEnd` | every region ends by the end of the program | `endsByProgramEnd_examples` (left) | `endsByProgramEnd_examples` (right) |
| `lazyPlacement`, `eagerPlacement` | end at owner's next access / right after the later of creation and last use | `lazyPlacement_example`, `eagerPlacement_example` | `lazyPlacement_example` (third conjunct), `eagerPlacement_example_neg` |
| `neverEndPlacement` | pure backward functions = regions that never end | `neverEndPlacement_example`, lemma `translate_neverEndPlacement` | `neverEndPlacement_example_neg` |

#### Supporting lemmas (fully proved)

* `aliasingDiscipline_of_endsAfterLastUse_of_endsByNextOwnerAccess` — `EndsAfterLastUse P π → EndsByNextOwnerAccess P π → AliasingDiscipline P` (why the discipline is not a hypothesis of `endpoint-window` or `lock-complete`).
* `endsAfterLastWrite_of_endsAfterLastUse` — `EndsAfterLastUse P π → EndsAfterLastWrite P π`.
* `lazyPlacement_endsAfterCreation`, `lazyPlacement_endsAfterLastUse_of_aliasingDiscipline`, `lazyPlacement_endsByNextOwnerAccess`, `lazyPlacement_endsByProgramEnd`, `eagerPlacement_endsAfterCreation`, `eagerPlacement_endsAfterLastUse`, `eagerPlacement_endsByNextOwnerAccess_of_aliasingDiscipline`, `eagerPlacement_endsByProgramEnd`, and their bundles `lazyPlacement_respectsLiveness_of_aliasingDiscipline`, `eagerPlacement_respectsLiveness_of_aliasingDiscipline`.
* `translate_neverEndPlacement`, `pureBackSem_eq_effSem_neverEndPlacement` — `pureBackSem P h = effSem P (neverEndPlacement P) h`.
* `translate_filter_not_isBack` — erasing backward calls from any effectful translation gives the pure-backward translation; `srun_filter_not_isBack` — in a stateless target a successful run is unchanged by deleting its backward calls.
* `statelessSem_reborrowAfterWrite_vars_eq` — every successful stateless run of `reborrowAfterWrite c` has `x0 = x1`.
* `effSem_eq_effSem_of_respectsLiveness` — any two liveness-respecting placements give `effSem` the same outcome (two rewrites with `endpoint-window`; no card).
* `prophOutcome_empty_ownerReadThenWriteBack` (`ToyBackward/Results.lean`) — on `ownerReadThenWriteBack` with `endAt 3` (which violates `AliasingDiscipline` and `EndsByNextOwnerAccess` but meets `EndsAfterCreation`, `EndsAfterLastWrite`, and `EndsByProgramEnd`), `heapSem` succeeds while `ProphOutcome` holds for no outcome (cited under **Boundaries** for `prophecy-agreement` and `prophecy-sound-wider-window`).

#### Proof infrastructure (fully proved, used only inside proofs)

* `ToyBackward/Simulation.lean` — run decomposition (`trun_append`, `lrun_append`, `prun_append`), reference tables `refOf`, a finite count of bound slots `cnt`, the simulation relation `EffRel` between `heapSem` and `effSem`, and `Sim.effSem_eq_heapSem` (endpoint-window-last-write).
* `ToyBackward/SimLock.lean` — the lockstep relation `LockRel` between `effSem` and `lockSem` runs and `Sim.lockSem_eq_effSem` (on placements meeting the four window conditions, `lockSem P π h = effSem P π h`); the invariant `LInv` of successful `lockSem` runs and `Sim.respectsLiveness_of_lockSem` (lock-success-in-window).
* `ToyBackward/SimProph.lean` — `Sim.endsAfterCreation_of_trun` (a successful `effSem` run ends every region after its creation); `Sim.shape_run` (`prophSem` is stuck exactly when `effSem` is); the look-ahead predicate `GoodFor` and `Sim.goodFor_exists` (a prophecy assignment satisfying every resolution assumption of a successful run exists); the lockstep relation `PRel` and `Sim.prophOutcome_iff_effSem` (prophecy-agreement); `Sim.prophSem_eq_of_move` (moving resolution points earlier, within a stretch where the region's local value no longer changes, does not change `prophSem`) and `Sim.prophOutcome_iff_heapSem` (prophecy-sound-wider-window).
* `ToyBackward/Results.lean` — `lockSem_none_of_ill_scoped_respectsLiveness`: on `danglingUse` with `endAt 0` and on `useBeforeCreation` with its lazy placement, `RespectsLiveness` holds and `lockSem` is stuck.

### Results

Each result: tier, the Lean statement (verbatim, with an informal unfolding of the key definitions), the plain claim, the hypothesis ledger with tightness, depth, non-vacuity witness, positive control for impossibility results, prior art, and the design question it informs. Non-claims are under **Boundaries**. Notation in unfoldings: `n = P.length`; `owner(i, k)` means statement `i` is `asMut p`, `i < k`, and statement `k` is `asMut p`, `rawRead _ p`, or `rawWrite p _`.

#### `sound-lazy` — theorem

**Lean:** `Toy.Backward.effSem_lazyPlacement_eq_heapSem_of_aliasingDiscipline` (`ToyBackward/Results.lean`). **Status:** proved (short derivation from endpoint-window-last-write).

```lean
theorem effSem_lazyPlacement_eq_heapSem_of_aliasingDiscipline (P : Prog) (h : Heap)
    (had : AliasingDiscipline P) :
    effSem P (lazyPlacement P) h = heapSem P h := …
```

Unfolded:

```
∀ (P : Prog) (h : Heap),
  (∀ i j k < n, P[j] ∈ {read _ i, write i _} → owner(i, k) → j < k) →
  effSem P (lazyPlacement P) h = heapSem P h
where lazyPlacement P i = least k < n with owner(i, k), or n if there is none
```

**Plain claim.** For every toy program that obeys the aliasing discipline (every use of a reference created from a raw pointer precedes the next access to that cell by any other path) and every initial heap, the unchecked effectful-backward translation that ends each region at the owner's next access (or at the program end) has exactly the heap semantics' outcome: both succeed with the same final heap and local variables, or both are stuck.

**Tier.** T1 — Folklore made precise: that write-back backward functions make raw-pointer reborrows translatable under an aliasing discipline is asserted informally (Aeneas pull request #1537); no mechanized statement for this translation was found.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `had : AliasingDiscipline P` | Rules out accesses to the cell (raw read/write or a new as_mut) while a reference to it is still used; otherwise the borrow's local copy and memory diverge. | tight: counterexample `effSem_lazyPlacement_eq_heapSem_tight_aliasingDiscipline` |

**Depth.** shallow — A three-line derivation from endpoint-window (the lazy placement respects liveness for programs obeying the aliasing discipline); all substance is in endpoint-window-last-write, a simulation invariant over the run.

**Non-vacuity witness.** reborrowAfterWrite 5 (two as_mut calls on one pointer) obeys the aliasing discipline and its lazy placement ends region 0 before the second as_mut; effSem with the lazy placement equals heapSem on reborrowAfterWrite c for every heap and c (proved independently). Lean: `effSem_lazyPlacement_nonvacuous`, `effSem_reborrowAfterWrite_positive_control`.

**Prior art.**

* Aeneas pull request AeneasVerif/aeneas#1537, 'Add alive hints to support raw-pointer functions eventually.' (opened 2026-11-05; open and unmerged when examined), head commit 5c28fe8def8db99041d22503175591ba1fa47915. In our words: it makes the backward functions of regions created by opaque raw-pointer conversions monadic ('effectful', returning `Result`) instead of pure or inlined. At the head commit the generated test output (tests/lean/StatefulLifetime.lean) declares `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` and `axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))`, and the test source (tests/src/stateful-lifetime.rs) uses the attribute `#[verify::stateful_lifetime(...)]`; the pull request description, written earlier, gives `from_mut` the type `T → Result ((Ptr T) × (Unit → Result T))` and calls the attribute `keep_alive`. It offers three heuristics for when such regions end (short: when the borrows held are dead according to a backward liveness analysis, src/interp/InterpLiveness.ml, which counts every dereference `*r`, read or write, as a use of `r`; regular; long: surviving joins), asserts that this timing 'should not matter for soundness, only completeness', and restricts the `simplify_duplicate_calls` pass (src/pure/PureMicroPassesGeneral.ml), whose previous comment said it 'will not be sound anymore once we allow stateful (backward) functions'. These are assertions in the pull request, not proofs.
* Son Ho and Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022. doi:10.1145/3547647 (arXiv:2206.07185). Each function with mutable borrows is translated to a forward function and backward functions per region; borrows are ended lazily ('we reorganize borrows in a lazy fashion, and don't terminate a borrow until we need to get the borrowed value back', Section 2); programs relying on interior mutability or unsafe code are out of scope (abstract); a proof of soundness of the semantics and translation is named as future work (Section 7). For code interacting with the outside world, the paragraph 'I/O and External Dependencies' lifts generated code into 'a combined-state + error monad' with an opaque `state` type (e.g. `val deserialize_fwd : state -> result (state & hash_map_t u64)`).
* Son Ho, Aymeric Fromherz, and Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024. doi:10.1145/3674640 (long version arXiv:2404.02680). Theorem 4.1: every run of the symbolic semantics LLBC# (which may end borrows at arbitrary points through reorganizations, rule E-Reorg: 'it is always possible to end a borrow early, but this may lead to an unnecessarily stuck execution') is matched by the concrete LLBC semantics; proved in the paper, with full proofs in the long version's appendices. Correctness of the functional translation is left to future work and unsafe code is not considered.
* Son Ho. Formal Verification of Rust Programs by Functional Translation. PhD thesis, Université PSL (prepared at Inria Paris), defended 2024-12-09. HAL tel-05004605. Its table of contents includes Chapter 11 'Soundness: LLBC# Defines a Borrow-Checker' (with Section 11.2 'A Heap-and-Addresses Interpretation of Valued Borrows' and 11.2.9 'The Pointer Language (PL)') and Chapter 13 'From Symbolic Semantics to Functional Code'. Only the table of contents and the abstract ('as long as they do not rely on interior mutability or unsafe code') were consulted; no claim about the chapters' content is made here.
* Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, and Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust. Proc. ACM Program. Lang. 4(POPL), Article 41, pp. 1-32, 2020. doi:10.1145/3371109. An operational semantics for memory accesses in Rust that 'defines an aliasing discipline and declares programs violating it to have undefined behavior' (abstract).
* Neven Villani, Johannes Hostert, Derek Dreyer, and Ralf Jung. Tree Borrows. Proc. ACM Program. Lang. 9(PLDI), Article 188, pp. 1019-1042, 2025. doi:10.1145/3735592. Mutable references 'start out as Reserved, not as Unique. Reserved allows local and foreign reads', until their first write through the reference (Section 2.2).

**Design question.** Is giving `as_mut`'s backward function the effect of writing the final value back to a heap model a sound way to translate raw-pointer reborrows, and what must the source program satisfy?

Basis: execution (Lean kernel check)

#### `sound-eager` — theorem

**Lean:** `Toy.Backward.effSem_eagerPlacement_eq_heapSem_of_aliasingDiscipline` (`ToyBackward/Results.lean`). **Status:** proved (short derivation from endpoint-window-last-write).

```lean
theorem effSem_eagerPlacement_eq_heapSem_of_aliasingDiscipline (P : Prog) (h : Heap)
    (had : AliasingDiscipline P) :
    effSem P (eagerPlacement P) h = heapSem P h := …
```

Unfolded:

```
∀ (P : Prog) (h : Heap),
  (∀ i j k < n, P[j] ∈ {read _ i, write i _} → owner(i, k) → j < k) →
  effSem P (eagerPlacement P) h = heapSem P h
where eagerPlacement P i = max i (largest j < n with P[j] ∈ {read _ i, write i _}, or i) + 1
```

**Plain claim.** For every toy program that obeys the aliasing discipline and every initial heap, the unchecked effectful-backward translation that ends each region immediately after the later of its creation and its last use (`max i (last use) + 1`: after the last use that follows the creation, or right after the creation if there is none) has exactly the heap semantics' outcome: both succeed with the same final heap and local variables, or both are stuck.

**Tier.** T1 — As sound-lazy; the eager placement approximates ending a region right after its last use (the 'short' heuristic of pull request #1537 ends a region when its borrows are dead according to a liveness analysis that counts reads and writes through the reference as uses).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `had : AliasingDiscipline P` | Without it the eager end can still precede an owner access that happens while the reference is used, and the local copy diverges from memory. | tight: counterexample `effSem_eagerPlacement_eq_heapSem_tight_aliasingDiscipline` |

**Depth.** shallow — A three-line derivation from endpoint-window; substance in endpoint-window-last-write.

**Non-vacuity witness.** writeThenOtherThenRawRead obeys the aliasing discipline, and its eager and lazy placements produce different target programs; on it the eager placement's outcome equals heapSem for every heap (proved independently). Lean: `effSem_eagerPlacement_nonvacuous`, `effSem_eagerPlacement_instance`.

**Prior art.**

* Aeneas pull request AeneasVerif/aeneas#1537, 'Add alive hints to support raw-pointer functions eventually.' (opened 2026-11-05; open and unmerged when examined), head commit 5c28fe8def8db99041d22503175591ba1fa47915. In our words: it makes the backward functions of regions created by opaque raw-pointer conversions monadic ('effectful', returning `Result`) instead of pure or inlined. At the head commit the generated test output (tests/lean/StatefulLifetime.lean) declares `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` and `axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))`, and the test source (tests/src/stateful-lifetime.rs) uses the attribute `#[verify::stateful_lifetime(...)]`; the pull request description, written earlier, gives `from_mut` the type `T → Result ((Ptr T) × (Unit → Result T))` and calls the attribute `keep_alive`. It offers three heuristics for when such regions end (short: when the borrows held are dead according to a backward liveness analysis, src/interp/InterpLiveness.ml, which counts every dereference `*r`, read or write, as a use of `r`; regular; long: surviving joins), asserts that this timing 'should not matter for soundness, only completeness', and restricts the `simplify_duplicate_calls` pass (src/pure/PureMicroPassesGeneral.ml), whose previous comment said it 'will not be sound anymore once we allow stateful (backward) functions'. These are assertions in the pull request, not proofs.
* Son Ho, Aymeric Fromherz, and Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024. doi:10.1145/3674640 (long version arXiv:2404.02680). Theorem 4.1: every run of the symbolic semantics LLBC# (which may end borrows at arbitrary points through reorganizations, rule E-Reorg: 'it is always possible to end a borrow early, but this may lead to an unnecessarily stuck execution') is matched by the concrete LLBC semantics; proved in the paper, with full proofs in the long version's appendices. Correctness of the functional translation is left to future work and unsafe code is not considered.

**Design question.** Is ending keep-alive regions as early as possible (at the last use) sound for raw-pointer reborrows?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — the reading of the pull request's region-end heuristics and its claim that timing affects only completeness is the second bullet of **Modeling bridges** below, with its reasoning.

#### `pure-backward-unsound` — impossibility

**Lean:** `Toy.Backward.pureBackSem_unsound_on_reborrowAfterWrite` (`ToyBackward/Results.lean`). **Status:** proved.

```lean
theorem pureBackSem_unsound_on_reborrowAfterWrite (h : Heap) (c : Int) (hc : c ≠ h 0) :
    AliasingDiscipline (reborrowAfterWrite c) ∧
    ∃ o₁ o₂, pureBackSem (reborrowAfterWrite c) h = some o₁ ∧
      heapSem (reborrowAfterWrite c) h = some o₂ ∧
      o₁.heap = h ∧ o₂.heap = upd h 0 c ∧
      o₁.vars 0 = h 0 ∧ o₁.vars 1 = h 0 ∧ o₂.vars 0 = h 0 ∧ o₂.vars 1 = c ∧
      o₁.heap 0 ≠ o₂.heap 0 ∧ o₁.vars 1 ≠ o₂.vars 1 ∧
      pureBackSem (reborrowAfterWrite c) h ≠ heapSem (reborrowAfterWrite c) h := …
```

Unfolded:

```
∀ (h : Heap) (c : Int), c ≠ h 0 →
  AliasingDiscipline [asMut 0, read 0 0, write 0 (lit c), asMut 0, read 1 3] ∧
  ∃ o₁ o₂, pureBackSem (reborrowAfterWrite c) h = some o₁ ∧ heapSem (reborrowAfterWrite c) h = some o₂ ∧
    o₁.heap = h ∧ o₂.heap = h[0 ↦ c] ∧
    o₁.vars 0 = h 0 ∧ o₁.vars 1 = h 0 ∧ o₂.vars 0 = h 0 ∧ o₂.vars 1 = c ∧
    o₁.heap 0 ≠ o₂.heap 0 ∧ o₁.vars 1 ≠ o₂.vars 1 ∧
    pureBackSem (reborrowAfterWrite c) h ≠ heapSem (reborrowAfterWrite c) h
```

**Plain claim.** On the program `reborrowAfterWrite c` (`r0 = &mut *p; x0 = *r0; *r0 = c; r3 = &mut *p; x1 = *r3`), which obeys the aliasing discipline, whenever `c` differs from the cell's initial content `h 0`, the translation whose backward functions have no effect succeeds with final heap exactly the initial heap `h` and binds the second reborrow's read `x1` to the stale `h 0`, while the heap semantics succeeds with final heap `h[0 ↦ c]` and `x1 = c`; the two outcomes differ in the final heap and in a local variable.

**Tier.** T1 — Folklore made precise: an effect-free backward function for `as_mut` cannot return the final value anywhere; noted informally in Aeneas (pull request #1537 description: current `as_mut : Ptr T -> Result (T x (T -> Unit))`).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hc : c ≠ h 0` | Makes the write through the first reference observable; if it writes the value already there, the two translations agree. | tight: counterexample `pureBackSem_unsound_tight_ne` |

**Depth.** definitional — Evaluation of a five-statement program plus one inequality.

**Non-vacuity witness.** c = 5, h = zeroHeap. Lean: `reborrowAfterWrite_ne_nonvacuous`.

**Positive control.** `effSem_reborrowAfterWrite_positive_control`, `lockSem_reborrowAfterWrite_positive_control`.

**Prior art.**

* Aeneas pull request AeneasVerif/aeneas#1537, 'Add alive hints to support raw-pointer functions eventually.' (opened 2026-11-05; open and unmerged when examined), head commit 5c28fe8def8db99041d22503175591ba1fa47915. In our words: it makes the backward functions of regions created by opaque raw-pointer conversions monadic ('effectful', returning `Result`) instead of pure or inlined. At the head commit the generated test output (tests/lean/StatefulLifetime.lean) declares `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` and `axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))`, and the test source (tests/src/stateful-lifetime.rs) uses the attribute `#[verify::stateful_lifetime(...)]`; the pull request description, written earlier, gives `from_mut` the type `T → Result ((Ptr T) × (Unit → Result T))` and calls the attribute `keep_alive`. It offers three heuristics for when such regions end (short: when the borrows held are dead according to a backward liveness analysis, src/interp/InterpLiveness.ml, which counts every dereference `*r`, read or write, as a use of `r`; regular; long: surviving joins), asserts that this timing 'should not matter for soundness, only completeness', and restricts the `simplify_duplicate_calls` pass (src/pure/PureMicroPassesGeneral.ml), whose previous comment said it 'will not be sound anymore once we allow stateful (backward) functions'. These are assertions in the pull request, not proofs.
* Son Ho and Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022. doi:10.1145/3547647 (arXiv:2206.07185). Each function with mutable borrows is translated to a forward function and backward functions per region; borrows are ended lazily ('we reorganize borrows in a lazy fashion, and don't terminate a borrow until we need to get the borrowed value back', Section 2); programs relying on interior mutability or unsafe code are out of scope (abstract); a proof of soundness of the semantics and translation is named as future work (Section 7). For code interacting with the outside world, the paragraph 'I/O and External Dependencies' lifts generated code into 'a combined-state + error monad' with an opaque `state` type (e.g. `val deserialize_fwd : state -> result (state & hash_map_t u64)`).

**Design question.** Why can the backward function of a raw-pointer reborrow not be pure?

Basis: execution (Lean kernel check)

#### `stateless-unsound` — impossibility

**Lean:** `Toy.Backward.statelessSem_validates_false_duplicate_call_equation` (`ToyBackward/Results.lean`). **Status:** proved.

```lean
theorem statelessSem_validates_false_duplicate_call_equation (F : Ptr → Option Int)
    (B : Ptr → Int → Bool) (π : Placement) (h : Heap) (c : Int) (hc : c ≠ h 0) :
    AliasingDiscipline (reborrowAfterWrite c) ∧
    (∀ ρ, statelessSem F B (reborrowAfterWrite c) π = some ρ → ρ 0 = ρ 1) ∧
    (∃ o, heapSem (reborrowAfterWrite c) h = some o ∧ o.vars 0 ≠ o.vars 1) ∧
    statelessSem F B (reborrowAfterWrite c) π ≠ (heapSem (reborrowAfterWrite c) h).map Obs.vars := …
```

Unfolded:

```
∀ (F : Ptr → Option Int) (B : Ptr → Int → Bool) (π : Placement) (h : Heap) (c : Int), c ≠ h 0 →
  AliasingDiscipline (reborrowAfterWrite c) ∧
  (∀ ρ, (srun F B (translate (reborrowAfterWrite c) π) ⟨∅, 0⟩).map vars = some ρ → ρ 0 = ρ 1) ∧
  (∃ o, heapSem (reborrowAfterWrite c) h = some o ∧ o.vars 0 ≠ o.vars 1) ∧
  statelessSem F B (reborrowAfterWrite c) π ≠ (heapSem (reborrowAfterWrite c) h).map vars
-- sstep F B: fwd i p binds slot i to (p, v) if F p = some v and fails otherwise; back i succeeds
-- iff B p v (slot i = (p, v)) and changes nothing; rawRead x p reads F p; rawWrite is a no-op
```

**Plain claim.** For every stateless model of `as_mut` — any forward model `F : Ptr → Option Int`, any backward model that may fail but has no other effect, and any placement of the backward calls — and every `c ≠ h 0`: every successful run of the translated `reborrowAfterWrite c` gives the two `as_mut` calls on the same pointer equal results (`x0 = x1`, the equation that merging duplicate calls relies on), the heap semantics succeeds with `x0 ≠ x1`, and therefore the stateless translation's outcome on local variables is not the heap semantics' outcome (it either fails or computes `x0 = x1`).

**Tier.** T1 — Folklore made precise and generalized: the unsoundness of merging duplicate calls once backward functions are stateful is noted informally in Aeneas (comment in src/pure/PureMicroPassesGeneral.ml; issue #1525 for Cell and atomics); here it is shown that every stateless model, whatever its forward model, failure behaviour, or backward-call placement, validates the merge equation and disagrees with the heap semantics.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hc : c ≠ h 0` | Makes the write between the two as_mut calls change the cell; otherwise the natural stateless model agrees with the heap semantics. | tight: counterexample `statelessSem_validates_false_tight_ne` |

**Depth.** shallow — One structural lemma (a stateless run is unchanged by deleting backward calls, which can only fail) plus evaluation with a case split on F 0.

**Non-vacuity witness.** c = 5, h = zeroHeap; the natural stateless model (forward some ∘ h, backward always succeeds) does succeed on the program, so the universally quantified second conjunct is not vacuous. Lean: `reborrowAfterWrite_ne_nonvacuous`.

**Positive control.** `effSem_distinguishes_duplicate_calls_positive_control`, `statelessSem_single_reborrow_positive_control`.

**Prior art.**

* Aeneas pull request AeneasVerif/aeneas#1537, 'Add alive hints to support raw-pointer functions eventually.' (opened 2026-11-05; open and unmerged when examined), head commit 5c28fe8def8db99041d22503175591ba1fa47915. In our words: it makes the backward functions of regions created by opaque raw-pointer conversions monadic ('effectful', returning `Result`) instead of pure or inlined. At the head commit the generated test output (tests/lean/StatefulLifetime.lean) declares `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` and `axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))`, and the test source (tests/src/stateful-lifetime.rs) uses the attribute `#[verify::stateful_lifetime(...)]`; the pull request description, written earlier, gives `from_mut` the type `T → Result ((Ptr T) × (Unit → Result T))` and calls the attribute `keep_alive`. It offers three heuristics for when such regions end (short: when the borrows held are dead according to a backward liveness analysis, src/interp/InterpLiveness.ml, which counts every dereference `*r`, read or write, as a use of `r`; regular; long: surviving joins), asserts that this timing 'should not matter for soundness, only completeness', and restricts the `simplify_duplicate_calls` pass (src/pure/PureMicroPassesGeneral.ml), whose previous comment said it 'will not be sound anymore once we allow stateful (backward) functions'. These are assertions in the pull request, not proofs.
* Open, draft, unmerged (when examined) Aeneas pull requests that give `Result` heap effects: #1454 'NonNull and borrows of values behind raw pointers' (head fc68273b75beebb7fd74f9c3130e857b232960db), #1497 'Fournet/wip memory model' (head d17ca83fc07d712d1785f650840cb2073c259e69), #1548 'Heap model for raw pointers (from fournet/wip-memory-model)' (head 561b806a70789e090e305d1d992f92cad1de7ce0), and #1551 'Separation logic over the byte heap' (head 1d8f9aa0121faca8ff113c1b9b742b333e3e1519). At each head, `RustEffect.Input` (backends/lean/Aeneas/Std/Primitives.lean) has a heap event `guardedModify` besides `fail`, while `Result α` remains `ITree RustEffect α` with no state argument. At #1454's head, backends/lean/Aeneas/Std/Core/Ptr.lean defines `RawPtr.as_mut_unchecked {T : Type} [Pointee T] (p : MutRawPtr T) : Result (T × (T → Result Unit))` as `p.borrow` followed by returning `p.endBorrow` as the backward function, where `borrow` gives the cell away 'so that every access to the cell through a raw pointer fails until the borrow is ended with `endBorrow`'. At #1551's head, tests/lean/SafeUnsafe/Proofs.lean models the extracted `as_mut` by such a borrow and proves `ptr_as_mut_write.incomplete`: the extracted code returns the `as_mut` borrow only after the owner's borrow has ended, so reading the cell fails; the file classifies this case as 'Sound, but the model rejects a valid program'. Proposals under development, not merged code.
* Aeneas issue AeneasVerif/aeneas#1525, 'Bug: Cell::set / Atomic*::fetch_add through &self are modelled as pure, so a second get/fetch_add is merged with the first' (opened 2026-11-03): a stateless model of interior mutability plus duplicate-call merging yields generated code `ok (a = a)` for a function whose Rust result is false. An instance of the same phenomenon outside raw pointers.
* Aeneas pull request AeneasVerif/aeneas#1431, 'Define the state effect and implement the raw-pointer functions' (closed unmerged 2026-10-15), head commit 11f641de522c26266aaf664f6ade85ea1642058d: proposed adding a heap operation (`guardedModify`) to `RustEffect`, the event type of Aeneas's `Result` monad. At the head commit of #1537, `RustEffect.Input` (backends/lean/Aeneas/Std/Primitives.lean) has the single constructor `fail`, whose answer type is empty, so `Result` there is a failure-and-divergence monad.
* Son Ho and Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022. doi:10.1145/3547647 (arXiv:2206.07185). Each function with mutable borrows is translated to a forward function and backward functions per region; borrows are ended lazily ('we reorganize borrows in a lazy fashion, and don't terminate a borrow until we need to get the borrowed value back', Section 2); programs relying on interior mutability or unsafe code are out of scope (abstract); a proof of soundness of the semantics and translation is named as future work (Section 7). For code interacting with the outside world, the paragraph 'I/O and External Dependencies' lifts generated code into 'a combined-state + error monad' with an opaque `state` type (e.g. `val deserialize_fwd : state -> result (state & hash_map_t u64)`).
* Faris Abou-Saleh, James Cheney, Jeremy Gibbons, James McKinna, and Perdita Stevens. Reflections on Monadic Lenses. In: S. Lindley, C. McBride, P. Trinder, D. Sannella (eds.), A List of Successes That Can Change the World, Lecture Notes in Computer Science, Springer, 2016, pp. 1-31. doi:10.1007/978-3-319-30936-1_1 (arXiv:1601.02484). Reviews formulations of bidirectional transformations 'that use monads to account for effects', attending to 'the obstacles to naively adding monadic effects to existing definitions of pure bx such as lenses' (abstract). Background for forward/backward pairs with effects; consulted only through its abstract.

**Design question.** Is it enough to make `as_mut`'s backward function return `Result Unit` in a failure-and-divergence-only monad (and to stop merging duplicate calls), or must the effect type carry heap state, whether as heap events inside the monad or as an explicitly threaded state?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — the application to Aeneas pull request #1537 is the first bullet of **Modeling bridges** below, with its reasoning.

#### `endpoint-window` — theorem

**Lean:** `Toy.Backward.effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd` (`ToyBackward/Results.lean`). **Status:** proved (short derivation from endpoint-window-last-write).

```lean
theorem effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd
    (P : Prog) (π : Placement) (h : Heap)
    (hc : EndsAfterCreation P π) (hu : EndsAfterLastUse P π) (ho : EndsByNextOwnerAccess P π)
    (he : EndsByProgramEnd P π) :
    effSem P π h = heapSem P h := …
```

Unfolded:

```
∀ (P : Prog) (π : Placement) (h : Heap),
  (∀ i < n, region i → i < π i) →                                          -- hc
  (∀ i < n, region i → ∀ j < n, P[j] ∈ {read _ i, write i _} → j < π i) →  -- hu
  (∀ i < n, ∀ k < n, owner(i, k) → π i ≤ k) →                              -- ho
  (∀ i < n, region i → π i ≤ n) →                                          -- he
  effSem P π h = heapSem P h
```

**Plain claim.** For every toy program and every placement of region ends that ends each region after its creation and after its last use, no later than the owner's next access to its cell (raw read, raw write, or a new `as_mut` of the same pointer), and no later than the program end, the unchecked effectful-backward translation has exactly the heap semantics' outcome (both succeed with the same final heap and local variables, or both are stuck); the aliasing discipline is implied, not assumed.

**Tier.** T1 — Asserted informally for Aeneas keep-alive regions (pull request #1537: timing 'should not matter for soundness, only completeness'); the analogous property for safe code's borrow-checking semantics is proved on paper (ICFP 2024, Theorem 4.1 covers every reorganization choice), but not for the synthesis of backward functions or for raw-pointer regions.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hc : EndsAfterCreation P π` | A backward call scheduled at or before its region's creation has no forward value: the translation is stuck while the heap semantics succeeds (matters only for regions without a later use; for regions with a later use it follows from hu). | tight: counterexample `effSem_respecting_tight_endsAfterCreation` |
| `hu : EndsAfterLastUse P π` | Writes through the reference after its backward call are lost. | tight: counterexample `effSem_respecting_tight_endsAfterLastUse` |
| `ho : EndsByNextOwnerAccess P π` | An owner access before the backward call reads (or is overwritten by) a stale heap model. | tight: counterexample `effSem_respecting_tight_endsByNextOwnerAccess` |
| `he : EndsByProgramEnd P π` | A region that never ends never writes back, so the final heap is stale. | tight: counterexample `effSem_respecting_tight_endsByProgramEnd` |

**Depth.** shallow — A three-line derivation from endpoint-window-last-write via aliasingDiscipline_of_endsAfterLastUse_of_endsByNextOwnerAccess and endsAfterLastWrite_of_endsAfterLastUse; substance in endpoint-window-last-write. The corollary effSem_eq_effSem_of_respectsLiveness (any two liveness-respecting placements give the same outcome) is two rewrites with this result and has no separate card.

**Non-vacuity witness.** writeThenOtherThenRawRead with its lazy and its eager placement (they differ: region 0 ends before index 3 resp. 2). Lean: `effSem_respecting_nonvacuous`.

**Prior art.**

* Aeneas pull request AeneasVerif/aeneas#1537, 'Add alive hints to support raw-pointer functions eventually.' (opened 2026-11-05; open and unmerged when examined), head commit 5c28fe8def8db99041d22503175591ba1fa47915. In our words: it makes the backward functions of regions created by opaque raw-pointer conversions monadic ('effectful', returning `Result`) instead of pure or inlined. At the head commit the generated test output (tests/lean/StatefulLifetime.lean) declares `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` and `axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))`, and the test source (tests/src/stateful-lifetime.rs) uses the attribute `#[verify::stateful_lifetime(...)]`; the pull request description, written earlier, gives `from_mut` the type `T → Result ((Ptr T) × (Unit → Result T))` and calls the attribute `keep_alive`. It offers three heuristics for when such regions end (short: when the borrows held are dead according to a backward liveness analysis, src/interp/InterpLiveness.ml, which counts every dereference `*r`, read or write, as a use of `r`; regular; long: surviving joins), asserts that this timing 'should not matter for soundness, only completeness', and restricts the `simplify_duplicate_calls` pass (src/pure/PureMicroPassesGeneral.ml), whose previous comment said it 'will not be sound anymore once we allow stateful (backward) functions'. These are assertions in the pull request, not proofs.
* Son Ho, Aymeric Fromherz, and Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024. doi:10.1145/3674640 (long version arXiv:2404.02680). Theorem 4.1: every run of the symbolic semantics LLBC# (which may end borrows at arbitrary points through reorganizations, rule E-Reorg: 'it is always possible to end a borrow early, but this may lead to an unnecessarily stuck execution') is matched by the concrete LLBC semantics; proved in the paper, with full proofs in the long version's appendices. Correctness of the functional translation is left to future work and unsafe code is not considered.
* Son Ho and Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022. doi:10.1145/3547647 (arXiv:2206.07185). Each function with mutable borrows is translated to a forward function and backward functions per region; borrows are ended lazily ('we reorganize borrows in a lazy fashion, and don't terminate a borrow until we need to get the borrowed value back', Section 2); programs relying on interior mutability or unsafe code are out of scope (abstract); a proof of soundness of the semantics and translation is named as future work (Section 7). For code interacting with the outside world, the paragraph 'I/O and External Dependencies' lifts generated code into 'a combined-state + error monad' with an opaque `state` type (e.g. `val deserialize_fwd : state -> result (state & hash_map_t u64)`).
* Son Ho. Formal Verification of Rust Programs by Functional Translation. PhD thesis, Université PSL (prepared at Inria Paris), defended 2024-12-09. HAL tel-05004605. Its table of contents includes Chapter 11 'Soundness: LLBC# Defines a Borrow-Checker' (with Section 11.2 'A Heap-and-Addresses Interpretation of Valued Borrows' and 11.2.9 'The Pointer Language (PL)') and Chapter 13 'From Symbolic Semantics to Functional Code'. Only the table of contents and the abstract ('as long as they do not rely on interior mutability or unsafe code') were consulted; no claim about the chapters' content is made here.

**Design question.** Does the point at which a keep-alive region of a raw-pointer reborrow ends affect soundness, or only completeness?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — the reading of the pull request's region-end heuristics and its claim that timing affects only completeness is the second bullet of **Modeling bridges** below, with its reasoning.

#### `endpoint-window-last-write` — theorem

**Lean:** `Toy.Backward.effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastWrite_of_endsByNextOwnerAccess_of_endsByProgramEnd_of_aliasingDiscipline` (`ToyBackward/Results.lean`). **Status:** proved.

```lean
theorem effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastWrite_of_endsByNextOwnerAccess_of_endsByProgramEnd_of_aliasingDiscipline
    (P : Prog) (π : Placement) (h : Heap)
    (hc : EndsAfterCreation P π) (hw : EndsAfterLastWrite P π) (ho : EndsByNextOwnerAccess P π)
    (he : EndsByProgramEnd P π) (had : AliasingDiscipline P) :
    effSem P π h = heapSem P h := …
```

Unfolded:

```
∀ (P : Prog) (π : Placement) (h : Heap),
  (∀ i < n, region i → i < π i) →                                     -- hc
  (∀ i < n, region i → ∀ j < n, P[j] = write i _ → j < π i) →         -- hw
  (∀ i < n, ∀ k < n, owner(i, k) → π i ≤ k) →                         -- ho
  (∀ i < n, region i → π i ≤ n) →                                     -- he
  (∀ i j k < n, P[j] ∈ {read _ i, write i _} → owner(i, k) → j < k) → -- had
  (trun (translate P π) ⟨h, ∅, 0⟩).map obs = (hrun 0 P ⟨h, ∅, 0⟩).map obs
```

**Plain claim.** For every toy program obeying the aliasing discipline and every placement that ends each region after its creation and after its last write through its reference (reads may follow), no later than the owner's next access to its cell, and no later than the program end, the unchecked effectful-backward translation has exactly the heap semantics' outcome (both succeed with the same final heap and local variables, or both are stuck).

**Tier.** T1 — A refinement of endpoint-window in the toy; no novelty is claimed (it depends on the target keeping the forward value readable after the backward call).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hc : EndsAfterCreation P π` | A backward call at or before its region's creation is stuck (no forward value); for regions with a later write it follows from hw. | tight: counterexample `effSem_generalized_tight_endsAfterCreation` |
| `hw : EndsAfterLastWrite P π` | Writes through the reference after its backward call are lost. | tight: counterexample `effSem_generalized_tight_endsAfterLastWrite` |
| `ho : EndsByNextOwnerAccess P π` | An owner access before the backward call reads a stale heap model. | tight: counterexample `effSem_generalized_tight_endsByNextOwnerAccess` |
| `he : EndsByProgramEnd P π` | A region that never ends never writes back. | tight: counterexample `effSem_generalized_tight_endsByProgramEnd` |
| `had : AliasingDiscipline P` | No longer implied once reads may follow the end: a read through the reference after an owner write sees the stale local copy. | tight: counterexample `effSem_generalized_tight_aliasingDiscipline` |

**Depth.** substantive — Simulation invariant over the run (relation EffRel in ToyBackward/Simulation.lean): the target's variables equal the heap semantics' variables; a region's slot is bound exactly when the region has been created, and holds the region's pointer; a slot's local value equals the heap semantics' cell while the region is open or still has a later use through its reference; and a target cell equals the heap semantics' cell whenever no open region points to it. EndsByNextOwnerAccess and the aliasing discipline keep every other path from touching a cell while one of these equalities is needed; EndsAfterLastWrite makes the written-back value the final one; EndsAfterCreation makes every backward call find a forward value; EndsByProgramEnd closes every region before the final observation.

**Non-vacuity witness.** writeThenRead 5 with the region ended between its last write and a later read (outside endpoint-window); the conclusion is proved independently on this instance for every heap. Lean: `effSem_generalized_nonvacuous`, `effSem_generalized_instance`.

**Prior art.**

* Aeneas pull request AeneasVerif/aeneas#1537, 'Add alive hints to support raw-pointer functions eventually.' (opened 2026-11-05; open and unmerged when examined), head commit 5c28fe8def8db99041d22503175591ba1fa47915. In our words: it makes the backward functions of regions created by opaque raw-pointer conversions monadic ('effectful', returning `Result`) instead of pure or inlined. At the head commit the generated test output (tests/lean/StatefulLifetime.lean) declares `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` and `axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))`, and the test source (tests/src/stateful-lifetime.rs) uses the attribute `#[verify::stateful_lifetime(...)]`; the pull request description, written earlier, gives `from_mut` the type `T → Result ((Ptr T) × (Unit → Result T))` and calls the attribute `keep_alive`. It offers three heuristics for when such regions end (short: when the borrows held are dead according to a backward liveness analysis, src/interp/InterpLiveness.ml, which counts every dereference `*r`, read or write, as a use of `r`; regular; long: surviving joins), asserts that this timing 'should not matter for soundness, only completeness', and restricts the `simplify_duplicate_calls` pass (src/pure/PureMicroPassesGeneral.ml), whose previous comment said it 'will not be sound anymore once we allow stateful (backward) functions'. These are assertions in the pull request, not proofs.
* Son Ho, Aymeric Fromherz, and Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024. doi:10.1145/3674640 (long version arXiv:2404.02680). Theorem 4.1: every run of the symbolic semantics LLBC# (which may end borrows at arbitrary points through reorganizations, rule E-Reorg: 'it is always possible to end a borrow early, but this may lead to an unnecessarily stuck execution') is matched by the concrete LLBC semantics; proved in the paper, with full proofs in the long version's appendices. Correctness of the functional translation is left to future work and unsafe code is not considered.

**Design question.** How early may a keep-alive region end: after the last use, or already after the last write?

Basis: execution (Lean kernel check)

#### `lock-complete` — theorem

**Lean:** `Toy.Backward.lockSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd` (`ToyBackward/Results.lean`). **Status:** proved.

```lean
theorem lockSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd
    (P : Prog) (π : Placement) (h : Heap)
    (hc : EndsAfterCreation P π) (hu : EndsAfterLastUse P π) (ho : EndsByNextOwnerAccess P π)
    (he : EndsByProgramEnd P π) :
    lockSem P π h = heapSem P h := …
```

Unfolded:

```
∀ (P : Prog) (π : Placement) (h : Heap),
  hc(π) → hu(π) → ho(π) → he(π) →            -- as in endpoint-window
  lockSem P π h = heapSem P h
-- lstep: fwd i p is stuck if p is lent, else opens slot i := (p, heap p) and lends p;
--        lread/lwrite need an open slot; back i writes slot i to the heap, closes slot i, returns p;
--        rawRead/rawWrite p are stuck if p is lent. lockSem is none if a slot is open at the end.
```

**Plain claim.** For every toy program and every placement that ends each region after its creation and after its last use, no later than the owner's next access to its cell, and no later than the program end, the borrow-locking effectful-backward translation (the forward call lends the cell to the region; other accesses to a lent cell, uses of a closed region, and a run ending with a lent cell are stuck) has exactly the heap semantics' outcome (both succeed with the same final heap and local variables, or both are stuck).

**Tier.** T1 — Folklore made precise: permission-tracking heap models in which a borrowed cell is inaccessible until the backward function runs are the design of the companion Aeneas pull requests (#1454, #1551); that they are complete on liveness-respecting placements was not found stated or mechanized.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hc : EndsAfterCreation P π` | A backward call before its forward call is stuck. | tight: counterexample `lockSem_complete_tight_endsAfterCreation` |
| `hu : EndsAfterLastUse P π` | A use (read or write) after the backward call is stuck, since the region is closed; ending after the last write is not enough here, unlike endpoint-window-last-write. | tight: counterexample `lockSem_complete_tight_endsAfterLastUse` |
| `ho : EndsByNextOwnerAccess P π` | An owner access (or a second loan) while the cell is lent is stuck. | tight: counterexample `lockSem_complete_tight_endsByNextOwnerAccess` |
| `he : EndsByProgramEnd P π` | A run that ends with a cell still lent is stuck. | tight: counterexample `lockSem_complete_tight_endsByProgramEnd` |

**Depth.** substantive — Lockstep simulation of the borrow-locking run against the unchecked run of the same target program (relation LockRel in ToyBackward/SimLock.lean): equal heaps and variables; a region's borrow-locking slot equals its unchecked slot while the region is open and is empty after its backward call; a cell is lent exactly when an open slot points to it, with at most one open slot per cell; the open-region count equals the number of open slots. Every potential stuck step of lockSem is excluded by one placement condition or is a step at which the unchecked run is stuck too, and no region is open at the end; so lockSem equals effSem on such placements (lockSem_eq_effSem), and endpoint-window gives the heap semantics' outcome.

**Non-vacuity witness.** writeThenOtherThenRawRead with its lazy and its eager placement (which differ); on reborrowAfterWrite c with the lazy placement the conclusion is proved independently for every heap and c. Lean: `effSem_respecting_nonvacuous`, `lockSem_reborrowAfterWrite_positive_control`.

**Prior art.**

* Open, draft, unmerged (when examined) Aeneas pull requests that give `Result` heap effects: #1454 'NonNull and borrows of values behind raw pointers' (head fc68273b75beebb7fd74f9c3130e857b232960db), #1497 'Fournet/wip memory model' (head d17ca83fc07d712d1785f650840cb2073c259e69), #1548 'Heap model for raw pointers (from fournet/wip-memory-model)' (head 561b806a70789e090e305d1d992f92cad1de7ce0), and #1551 'Separation logic over the byte heap' (head 1d8f9aa0121faca8ff113c1b9b742b333e3e1519). At each head, `RustEffect.Input` (backends/lean/Aeneas/Std/Primitives.lean) has a heap event `guardedModify` besides `fail`, while `Result α` remains `ITree RustEffect α` with no state argument. At #1454's head, backends/lean/Aeneas/Std/Core/Ptr.lean defines `RawPtr.as_mut_unchecked {T : Type} [Pointee T] (p : MutRawPtr T) : Result (T × (T → Result Unit))` as `p.borrow` followed by returning `p.endBorrow` as the backward function, where `borrow` gives the cell away 'so that every access to the cell through a raw pointer fails until the borrow is ended with `endBorrow`'. At #1551's head, tests/lean/SafeUnsafe/Proofs.lean models the extracted `as_mut` by such a borrow and proves `ptr_as_mut_write.incomplete`: the extracted code returns the `as_mut` borrow only after the owner's borrow has ended, so reading the cell fails; the file classifies this case as 'Sound, but the model rejects a valid program'. Proposals under development, not merged code.
* Aeneas pull request AeneasVerif/aeneas#1537, 'Add alive hints to support raw-pointer functions eventually.' (opened 2026-11-05; open and unmerged when examined), head commit 5c28fe8def8db99041d22503175591ba1fa47915. In our words: it makes the backward functions of regions created by opaque raw-pointer conversions monadic ('effectful', returning `Result`) instead of pure or inlined. At the head commit the generated test output (tests/lean/StatefulLifetime.lean) declares `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` and `axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))`, and the test source (tests/src/stateful-lifetime.rs) uses the attribute `#[verify::stateful_lifetime(...)]`; the pull request description, written earlier, gives `from_mut` the type `T → Result ((Ptr T) × (Unit → Result T))` and calls the attribute `keep_alive`. It offers three heuristics for when such regions end (short: when the borrows held are dead according to a backward liveness analysis, src/interp/InterpLiveness.ml, which counts every dereference `*r`, read or write, as a use of `r`; regular; long: surviving joins), asserts that this timing 'should not matter for soundness, only completeness', and restricts the `simplify_duplicate_calls` pass (src/pure/PureMicroPassesGeneral.ml), whose previous comment said it 'will not be sound anymore once we allow stateful (backward) functions'. These are assertions in the pull request, not proofs.
* Son Ho, Aymeric Fromherz, and Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024. doi:10.1145/3674640 (long version arXiv:2404.02680). Theorem 4.1: every run of the symbolic semantics LLBC# (which may end borrows at arbitrary points through reorganizations, rule E-Reorg: 'it is always possible to end a borrow early, but this may lead to an unnecessarily stuck execution') is matched by the concrete LLBC semantics; proved in the paper, with full proofs in the long version's appendices. Correctness of the functional translation is left to future work and unsafe code is not considered.

**Design question.** Under a borrow-locking model of effectful backward functions, which region end points lose nothing (give the heap semantics' outcome)?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — the reading of the pull request's region-end heuristics and its claim that timing affects only completeness is the second bullet of **Modeling bridges** below, with its reasoning.

#### `lock-success-in-window` — theorem

**Lean:** `Toy.Backward.respectsLiveness_of_lockSem_eq_some` (`ToyBackward/Results.lean`). **Status:** proved.

```lean
theorem respectsLiveness_of_lockSem_eq_some (P : Prog) (π : Placement) (h : Heap) (o : Obs)
    (hl : lockSem P π h = some o) :
    RespectsLiveness P π := …
```

Unfolded:

```
∀ (P : Prog) (π : Placement) (h : Heap) (o : Obs),
  lockSem P π h = some o → hc(π) ∧ hu(π) ∧ ho(π) ∧ he(π)
```

**Plain claim.** For every toy program, placement, and initial heap, if the borrow-locking translation succeeds, then the placement is liveness-respecting: every region ends after its creation and after its last use, no later than the owner's next access to its cell, and no later than the program end.

**Tier.** T1 — Converse of lock-complete in the toy; follows the same folklore design point (a borrow-locking model rejects out-of-window end points by getting stuck). Not found stated.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hl : lockSem P π h = some o` | The antecedent; without it the conclusion would claim that every placement respects liveness. | tight: counterexample `respectsLiveness_of_lockSem_tight_success` |

**Depth.** substantive — Invariant over a successful borrow-locking run (structure LInv in ToyBackward/SimLock.lean): before statement k, a region's slot is open exactly when the region was created before k and its backward call has not run; the lent flags, the uniqueness of the open region per cell, and the open-region count match the open slots; and no backward call of a region at or after k has run. Each violated placement condition forces a stuck step (a backward call without forward value, a use of a closed or never-opened region, an access to a lent cell, or a region still open at the end). Includes uses that precede a region's creation, which are stuck.

**Non-vacuity witness.** The borrow-locking translation succeeds on reborrowAfterWrite 5 with the lazy placement and on writeThenOtherThenRawRead with the eager placement. Lean: `lockSem_success_nonvacuous`.

**Prior art.**

* Open, draft, unmerged (when examined) Aeneas pull requests that give `Result` heap effects: #1454 'NonNull and borrows of values behind raw pointers' (head fc68273b75beebb7fd74f9c3130e857b232960db), #1497 'Fournet/wip memory model' (head d17ca83fc07d712d1785f650840cb2073c259e69), #1548 'Heap model for raw pointers (from fournet/wip-memory-model)' (head 561b806a70789e090e305d1d992f92cad1de7ce0), and #1551 'Separation logic over the byte heap' (head 1d8f9aa0121faca8ff113c1b9b742b333e3e1519). At each head, `RustEffect.Input` (backends/lean/Aeneas/Std/Primitives.lean) has a heap event `guardedModify` besides `fail`, while `Result α` remains `ITree RustEffect α` with no state argument. At #1454's head, backends/lean/Aeneas/Std/Core/Ptr.lean defines `RawPtr.as_mut_unchecked {T : Type} [Pointee T] (p : MutRawPtr T) : Result (T × (T → Result Unit))` as `p.borrow` followed by returning `p.endBorrow` as the backward function, where `borrow` gives the cell away 'so that every access to the cell through a raw pointer fails until the borrow is ended with `endBorrow`'. At #1551's head, tests/lean/SafeUnsafe/Proofs.lean models the extracted `as_mut` by such a borrow and proves `ptr_as_mut_write.incomplete`: the extracted code returns the `as_mut` borrow only after the owner's borrow has ended, so reading the cell fails; the file classifies this case as 'Sound, but the model rejects a valid program'. Proposals under development, not merged code.
* Son Ho, Aymeric Fromherz, and Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024. doi:10.1145/3674640 (long version arXiv:2404.02680). Theorem 4.1: every run of the symbolic semantics LLBC# (which may end borrows at arbitrary points through reorganizations, rule E-Reorg: 'it is always possible to end a borrow early, but this may lead to an unnecessarily stuck execution') is matched by the concrete LLBC semantics; proved in the paper, with full proofs in the long version's appendices. Correctness of the functional translation is left to future work and unsafe code is not considered.

**Design question.** Under a borrow-locking model, can a translator detect an unsuitable region end point by the translated program getting stuck?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — the reading of the pull request's region-end heuristics and its claim that timing affects only completeness is the second bullet of **Modeling bridges** below, with its reasoning.

#### `lock-sound` — theorem

**Lean:** `Toy.Backward.heapSem_eq_some_of_lockSem_eq_some` (`ToyBackward/Results.lean`). **Status:** proved (short derivation from lock-complete and lock-success-in-window).

```lean
theorem heapSem_eq_some_of_lockSem_eq_some (P : Prog) (π : Placement) (h : Heap) (o : Obs)
    (hl : lockSem P π h = some o) :
    heapSem P h = some o := …
```

Unfolded:

```
∀ (P : Prog) (π : Placement) (h : Heap) (o : Obs),
  lockSem P π h = some o → heapSem P h = some o      -- no condition on π
```

**Plain claim.** For every toy program, every placement of region ends (inside or outside the liveness window), and every initial heap, if the borrow-locking effectful-backward translation succeeds with an observation, the heap semantics succeeds with the same observation: an end point can make the translation stuck, never wrong.

**Tier.** T1 — The toy counterpart of the claim in Aeneas pull request #1537 that region-end timing 'should not matter for soundness, only completeness', made precise for a borrow-locking heap model; the companion pull request #1551 classifies its late-end example as 'Sound, but the model rejects a valid program'; the safe-code analogue for borrow-checking is ICFP 2024, Theorem 4.1. Not found mechanized for backward-function synthesis.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hl : lockSem P π h = some o` | The antecedent of partial refinement; the unchecked translation's outcome at a too-late placement is not the heap semantics' outcome, and lockSem does not produce it. | tight: counterexample `heapSem_eq_some_of_lockSem_tight_success` |

**Depth.** shallow — Two-line derivation: success implies the placement respects liveness (lock-success-in-window), where lockSem equals heapSem (lock-complete); substance in those two.

**Non-vacuity witness.** The borrow-locking translation succeeds on reborrowAfterWrite 5 (lazy placement), and on reborrowAfterWrite c the conclusion is proved independently; on three out-of-window instances it is stuck where the unchecked translation is wrong. Lean: `lockSem_success_nonvacuous`, `lockSem_reborrowAfterWrite_positive_control`, `outside_window_effSem_wrong_lockSem_stuck`.

**Prior art.**

* Aeneas pull request AeneasVerif/aeneas#1537, 'Add alive hints to support raw-pointer functions eventually.' (opened 2026-11-05; open and unmerged when examined), head commit 5c28fe8def8db99041d22503175591ba1fa47915. In our words: it makes the backward functions of regions created by opaque raw-pointer conversions monadic ('effectful', returning `Result`) instead of pure or inlined. At the head commit the generated test output (tests/lean/StatefulLifetime.lean) declares `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` and `axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))`, and the test source (tests/src/stateful-lifetime.rs) uses the attribute `#[verify::stateful_lifetime(...)]`; the pull request description, written earlier, gives `from_mut` the type `T → Result ((Ptr T) × (Unit → Result T))` and calls the attribute `keep_alive`. It offers three heuristics for when such regions end (short: when the borrows held are dead according to a backward liveness analysis, src/interp/InterpLiveness.ml, which counts every dereference `*r`, read or write, as a use of `r`; regular; long: surviving joins), asserts that this timing 'should not matter for soundness, only completeness', and restricts the `simplify_duplicate_calls` pass (src/pure/PureMicroPassesGeneral.ml), whose previous comment said it 'will not be sound anymore once we allow stateful (backward) functions'. These are assertions in the pull request, not proofs.
* Open, draft, unmerged (when examined) Aeneas pull requests that give `Result` heap effects: #1454 'NonNull and borrows of values behind raw pointers' (head fc68273b75beebb7fd74f9c3130e857b232960db), #1497 'Fournet/wip memory model' (head d17ca83fc07d712d1785f650840cb2073c259e69), #1548 'Heap model for raw pointers (from fournet/wip-memory-model)' (head 561b806a70789e090e305d1d992f92cad1de7ce0), and #1551 'Separation logic over the byte heap' (head 1d8f9aa0121faca8ff113c1b9b742b333e3e1519). At each head, `RustEffect.Input` (backends/lean/Aeneas/Std/Primitives.lean) has a heap event `guardedModify` besides `fail`, while `Result α` remains `ITree RustEffect α` with no state argument. At #1454's head, backends/lean/Aeneas/Std/Core/Ptr.lean defines `RawPtr.as_mut_unchecked {T : Type} [Pointee T] (p : MutRawPtr T) : Result (T × (T → Result Unit))` as `p.borrow` followed by returning `p.endBorrow` as the backward function, where `borrow` gives the cell away 'so that every access to the cell through a raw pointer fails until the borrow is ended with `endBorrow`'. At #1551's head, tests/lean/SafeUnsafe/Proofs.lean models the extracted `as_mut` by such a borrow and proves `ptr_as_mut_write.incomplete`: the extracted code returns the `as_mut` borrow only after the owner's borrow has ended, so reading the cell fails; the file classifies this case as 'Sound, but the model rejects a valid program'. Proposals under development, not merged code.
* Son Ho, Aymeric Fromherz, and Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024. doi:10.1145/3674640 (long version arXiv:2404.02680). Theorem 4.1: every run of the symbolic semantics LLBC# (which may end borrows at arbitrary points through reorganizations, rule E-Reorg: 'it is always possible to end a borrow early, but this may lead to an unnecessarily stuck execution') is matched by the concrete LLBC semantics; proved in the paper, with full proofs in the long version's appendices. Correctness of the functional translation is left to future work and unsafe code is not considered.

**Design question.** Is the claim that region-end timing affects only completeness true, and under what model of effectful backward functions?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — the reading of the pull request's region-end heuristics and its claim that timing affects only completeness is the second bullet of **Modeling bridges** below, with its reasoning.

#### `prophecy-agreement` — theorem

**Lean:** `Toy.Backward.prophOutcome_iff_effSem_of_endsByNextOwnerAccess_of_endsByProgramEnd` (`ToyBackward/Results.lean`). **Status:** proved.

```lean
theorem prophOutcome_iff_effSem_of_endsByNextOwnerAccess_of_endsByProgramEnd
    (P : Prog) (π : Placement) (h : Heap)
    (ho : EndsByNextOwnerAccess P π) (he : EndsByProgramEnd P π) :
    ∀ o, ProphOutcome P π h o ↔ effSem P π h = some o := …
```

Unfolded:

```
∀ (P : Prog) (π : Placement) (h : Heap),
  (∀ i < n, ∀ k < n, owner(i, k) → π i ≤ k) →          -- ho
  (∀ i < n, region i → π i ≤ n) →                       -- he
  ∀ o, (∃ φ : Nat → Int, prophSem P π h φ = some (o, true)) ↔ effSem P π h = some o
-- pstep φ: fwd i p binds slot i to (p, heap p) and sets heap p := φ i;
--          back i sets ok := ok && (snd (slot i) = φ i); everything else as in the effectful target
```

**Plain claim.** For every toy program and every placement that ends each region no later than the owner's next access to its cell and no later than the program end (with no condition relative to the region's creation or uses), the outcomes of the RustHorn-style prophecy encoding — over all prophecy assignments that satisfy every resolution assumption, checked at the end of the run — are exactly the unchecked effectful-backward translation's outcome (a single outcome, or none if it is stuck).

**Tier.** T1 — The prophecy encoding follows RustHorn and Creusot (lender receives the prophecy, region end assumes current = final); the agreement with write-back backward functions under these conditions is folklore-level and was not found stated.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `ho : EndsByNextOwnerAccess P π` | Between creation and resolution the owner holds the prophecy in the encoding but the old value in the write-back model; an owner access there distinguishes them. | tight: counterexample `prophOutcome_iff_effSem_tight_endsByNextOwnerAccess` |
| `he : EndsByProgramEnd P π` | An unresolved prophecy leaves the owner holding an arbitrary value. | tight: counterexample `prophOutcome_iff_effSem_tight_endsByProgramEnd` |

**Depth.** substantive — Lockstep simulation of the prophecy encoding against the unchecked run for a fixed prophecy assignment (relation PRel in ToyBackward/SimProph.lean): equal slots and variables; an open region's cell holds its prophecy and every other cell agrees. A run keeps its flag true exactly when every resolution assumption along the unchecked run holds (predicate GoodFor); a resolving assignment exists, built by recording each region's local value at its backward call along the unchecked run (goodFor_exists). Both semantics get stuck at the same steps (shape_run), and a successful unchecked run forces EndsAfterCreation (endsAfterCreation_of_trun), which is therefore not a hypothesis.

**Non-vacuity witness.** reborrowAfterWrite 5 with the lazy placement, and with a placement that ends region 0 too early for endpoint-window; the effectful translation succeeds on both. Lean: `prophOutcome_iff_effSem_nonvacuous`.

**Prior art.**

* Yusuke Matsushita, Takeshi Tsukada, and Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, LNCS, pp. 484-514, doi:10.1007/978-3-030-44914-8_18; journal version ACM TOPLAS 43(4), 2021, doi:10.1145/3462205. A mutable borrow is represented as the pair of the current target value and the target value at the end of the borrow (full version arXiv:2002.09002, Section 1.2, 'related to prophecy variables'); the borrow rule gives the lender the fresh end-of-borrow variable, and releasing the borrow checks the prophesied value (Section 3.2). The core language COR does not support unsafe code.
* Xavier Denis, Jacques-Henri Jourdan, and C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, LNCS, pp. 90-105, doi:10.1007/978-3-031-17244-1_6. Section 3.2: a mutable borrow is the record { current ; final }; creating it is 'y : borrow t <- { current = x ; final = any t }; x : t <- y.final', which is 'valid because the value of the lender cannot be observed before the lifetime's end'; ending it is 'assume { y.final = y.current }'. In that paper Creusot does not permit verification of unsafe code.
* Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, and Derek Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022, pp. 841-856, doi:10.1145/3519939.3523704. Machine-checked (Coq/Iris) soundness of RustHorn-style first-order specifications for safe APIs implemented with unsafe code (e.g. Vec, Cell, Mutex), via parametric prophecies; no treatment of raw-pointer-to-reference conversion as a translation rule was found in it.
* Ralf Jung, Rodolphe Lepigre, Gaurav Parthasarathy, Marianna Rapoport, Amin Timany, Derek Dreyer, and Bart Jacobs. The Future is Ours: Prophecy Variables in Separation Logic. Proc. ACM Program. Lang. 4(POPL), Article 45, pp. 1-32, 2020. doi:10.1145/3371113. Prophecy variables in a Hoare-style program logic, formalized in Iris in Coq (abstract). Background for prophecy encodings; it does not treat Rust borrows.

**Design question.** How does a write-back (effectful backward function) translation of raw-pointer reborrows relate to prophecy-based encodings?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — the relation to weakest-precondition and CHC-based verifiers is the third bullet of **Modeling bridges** below.

#### `prophecy-sound-wider-window` — theorem

**Lean:** `Toy.Backward.prophOutcome_iff_heapSem_of_aliasingDiscipline_of_endsAfterCreation_of_endsAfterLastWrite_of_endsByProgramEnd` (`ToyBackward/Results.lean`). **Status:** proved.

```lean
theorem prophOutcome_iff_heapSem_of_aliasingDiscipline_of_endsAfterCreation_of_endsAfterLastWrite_of_endsByProgramEnd
    (P : Prog) (π : Placement) (h : Heap)
    (had : AliasingDiscipline P) (hc : EndsAfterCreation P π) (hw : EndsAfterLastWrite P π)
    (he : EndsByProgramEnd P π) :
    ∀ o, ProphOutcome P π h o ↔ heapSem P h = some o := …
```

Unfolded:

```
∀ (P : Prog) (π : Placement) (h : Heap),
  (∀ i j k < n, P[j] ∈ {read _ i, write i _} → owner(i, k) → j < k) →  -- had
  (∀ i < n, region i → i < π i) →                                       -- hc
  (∀ i < n, region i → ∀ j < n, P[j] = write i _ → j < π i) →           -- hw
  (∀ i < n, region i → π i ≤ n) →                                       -- he
  ∀ o, (∃ φ : Nat → Int, prophSem P π h φ = some (o, true)) ↔ heapSem P h = some o
```

**Plain claim.** For every toy program obeying the aliasing discipline and every placement that ends each region after its creation and after its last write and no later than the program end — but possibly after the owner's next access — the prophecy encoding's end-of-run outcomes are exactly the heap semantics' outcome (a single outcome, or none if the heap semantics is stuck).

**Tier.** T1 — Exploratory; reflects the known design point that a lender holding a prophecy is valid 'because the value of the lender cannot be observed before the lifetime's end' (Creusot, Section 3.2), here checked against raw-pointer owner accesses.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `had : AliasingDiscipline P` | A read through the reference after an owner write sees the stale local value. | tight: counterexample `prophOutcome_iff_heapSem_tight_aliasingDiscipline` |
| `hc : EndsAfterCreation P π` | A resolution scheduled before its region's creation is stuck, so there is no outcome while the heap semantics succeeds. | tight: counterexample `prophOutcome_iff_heapSem_tight_endsAfterCreation` |
| `hw : EndsAfterLastWrite P π` | A write after resolution is not reflected in the prophecy. | tight: counterexample `prophOutcome_iff_heapSem_tight_endsAfterLastWrite` |
| `he : EndsByProgramEnd P π` | An unresolved prophecy leaves the owner holding an arbitrary value. | tight: counterexample `prophOutcome_iff_heapSem_tight_endsByProgramEnd` |

**Depth.** substantive — Reduction to the window: clamp the placement to π' i = min (π i) (lazyPlacement P i), the earlier of the given end and the owner's next access. Between π' i and π i no statement writes through region i (EndsAfterLastWrite and the aliasing discipline), and a resolution step changes only the check flag, so the prophecy encoding has the same end-of-run results under π and π' for every prophecy assignment (prophSem_eq_of_move in ToyBackward/SimProph.lean). π' satisfies all four window conditions, so prophecy-agreement and endpoint-window-last-write give the heap semantics' outcome. A region's prophecy can be observed by an owner access before its resolution step; the resolution fixes it to the region's final value, which by the aliasing discipline is already determined at that access.

**Non-vacuity witness.** reborrowAfterWrite 5 with region 0 ended after the second as_mut (outside endpoint-window and prophecy-agreement); on this instance the prophecy outcomes are proved to be exactly the heap semantics' outcome while the unchecked write-back translation effSem is proved wrong (the borrow-locking translation lockSem is stuck there instead; outside_window_effSem_wrong_lockSem_stuck). Lean: `prophOutcome_iff_heapSem_nonvacuous`, `prophecy_tolerates_late_end_instance`.

**Prior art.**

* Yusuke Matsushita, Takeshi Tsukada, and Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, LNCS, pp. 484-514, doi:10.1007/978-3-030-44914-8_18; journal version ACM TOPLAS 43(4), 2021, doi:10.1145/3462205. A mutable borrow is represented as the pair of the current target value and the target value at the end of the borrow (full version arXiv:2002.09002, Section 1.2, 'related to prophecy variables'); the borrow rule gives the lender the fresh end-of-borrow variable, and releasing the borrow checks the prophesied value (Section 3.2). The core language COR does not support unsafe code.
* Xavier Denis, Jacques-Henri Jourdan, and C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, LNCS, pp. 90-105, doi:10.1007/978-3-031-17244-1_6. Section 3.2: a mutable borrow is the record { current ; final }; creating it is 'y : borrow t <- { current = x ; final = any t }; x : t <- y.final', which is 'valid because the value of the lender cannot be observed before the lifetime's end'; ending it is 'assume { y.final = y.current }'. In that paper Creusot does not permit verification of unsafe code.
* Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers, and Derek Dreyer. RefinedRust: A Type System for High-Assurance Verification of Rust Programs. Proc. ACM Program. Lang. 8(PLDI), Article 192, pp. 1115-1139, 2024. doi:10.1145/3656422. Verification of 'both safe and unsafe Rust code' (abstract), including 'APIs that use raw pointers' (Section 3); mutable references carry 'borrow names, which are inspired by RustHorn's prophecy variables' (Section 1).
* Sacha-Élie Ayoun, Xavier Denis, Petar Maksimović, and Philippa Gardner. A Hybrid Approach to Semi-automated Rust Verification. Proc. ACM Program. Lang. 9(PLDI), Article 186, pp. 970-992, 2025. doi:10.1145/3729289 (extended version arXiv:2403.15122). Presents Gillian-Rust, which 'can reason about type safety and functional correctness of unsafe code' and embeds 'the parametric prophecies of RustHornBelt' (abstract).
* Creusot source repository github.com/creusot-rs/creusot at commit 601d97891bb0bc0b569686cc946ef4980560b5d8: the library defines a ghost permission type `Perm<C>` ('Generic permissions for accessing memory pointed to by pointers or within an interior mutable type', creusot-std/src/ghost/perm.rs) with an instance for raw pointers, `Perm<*const T>` (creusot-std/src/std/ptr.rs). Tool source code, not a publication.
* Ralf Jung, Rodolphe Lepigre, Gaurav Parthasarathy, Marianna Rapoport, Amin Timany, Derek Dreyer, and Bart Jacobs. The Future is Ours: Prophecy Variables in Separation Logic. Proc. ACM Program. Lang. 4(POPL), Article 45, pp. 1-32, 2020. doi:10.1145/3371113. Prophecy variables in a Hoare-style program logic, formalized in Iris in Coq (abstract). Background for prophecy encodings; it does not treat Rust borrows.

**Design question.** Is a prophecy encoding more robust than unchecked write-back (effSem) to imprecise region end placement for raw-pointer reborrows, and in what sense?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — the relation to weakest-precondition and CHC-based verifiers is the third bullet of **Modeling bridges** below.

#### `aliasing-iff-placement` — characterization

**Lean:** `Toy.Backward.aliasingDiscipline_iff_respectsLiveness_lazyPlacement` (`ToyBackward/Liveness.lean`). **Status:** proved.

```lean
theorem aliasingDiscipline_iff_respectsLiveness_lazyPlacement (P : Prog) :
    (AliasingDiscipline P ↔ RespectsLiveness P (lazyPlacement P)) ∧
    (AliasingDiscipline P ↔ RespectsLiveness P (eagerPlacement P)) ∧
    (AliasingDiscipline P ↔ ∃ π, RespectsLiveness P π) := …
```

Unfolded:

```
∀ (P : Prog),
  (AD P ↔ RL P (lazyPlacement P)) ∧ (AD P ↔ RL P (eagerPlacement P)) ∧ (AD P ↔ ∃ π, RL P π)
where AD P   = ∀ i j k < n, P[j] ∈ {read _ i, write i _} → owner(i, k) → j < k
      RL P π = hc(π) ∧ hu(π) ∧ ho(π) ∧ he(π)
```

**Plain claim.** For every toy program, the aliasing discipline holds if and only if the lazy placement is liveness-respecting, if and only if the eager placement is liveness-respecting, if and only if some placement is liveness-respecting (each region ends after its creation and after its last use, no later than the owner's next access to its cell, and no later than the program end).

**Tier.** T1 — Borrow checking as the existence of a consistent region assignment is a standard idea; here made precise for raw-pointer reborrows in the toy.

**Hypothesis ledger.** No hypotheses beyond the program `P` (a characterization; each direction is an implication between named properties).

**Depth.** shallow — Definition chasing plus first/last-index search lemmas. The right-to-left directions use only EndsAfterLastUse and EndsByNextOwnerAccess (lemma aliasingDiscipline_of_endsAfterLastUse_of_endsByNextOwnerAccess).

**Non-vacuity witness.** reborrowAfterWrite 5 (obeys the discipline; lazy and eager placements respect liveness) and rawWriteDuringBorrow (violates it; neither placement respects liveness). Lean: `aliasingDiscipline_iff_nonvacuous`.

**Prior art.**

* Son Ho and Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022. doi:10.1145/3547647 (arXiv:2206.07185). Each function with mutable borrows is translated to a forward function and backward functions per region; borrows are ended lazily ('we reorganize borrows in a lazy fashion, and don't terminate a borrow until we need to get the borrowed value back', Section 2); programs relying on interior mutability or unsafe code are out of scope (abstract); a proof of soundness of the semantics and translation is named as future work (Section 7). For code interacting with the outside world, the paragraph 'I/O and External Dependencies' lifts generated code into 'a combined-state + error monad' with an opaque `state` type (e.g. `val deserialize_fwd : state -> result (state & hash_map_t u64)`).
* Son Ho, Aymeric Fromherz, and Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024. doi:10.1145/3674640 (long version arXiv:2404.02680). Theorem 4.1: every run of the symbolic semantics LLBC# (which may end borrows at arbitrary points through reorganizations, rule E-Reorg: 'it is always possible to end a borrow early, but this may lead to an unnecessarily stuck execution') is matched by the concrete LLBC semantics; proved in the paper, with full proofs in the long version's appendices. Correctness of the functional translation is left to future work and unsafe code is not considered.

**Design question.** Can a translator decide whether a raw-pointer reborrow pattern is translatable by searching for region end points, and which canonical end points suffice?

Basis: execution (Lean kernel check)

### Modeling bridges

These connect the toy to a real system. They are reasoning, not theorems, and each is a separate claim.

* **Aeneas pull request #1537 and the stateless class.** At head commit
  `5c28fe8def8db99041d22503175591ba1fa47915` of Aeneas pull request #1537, considered *in isolation*,
  `Result` (`backends/lean/Aeneas/Std/Primitives.lean`) is an interaction tree whose only effects are
  failure and divergence (`RustEffect.Input` has the single constructor `fail`, with empty answer
  type), with no heap state; the generated test output `tests/lean/StatefulLifetime.lean` declares
  `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` and
  `axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))`. So that commit alone falls in
  the stateless class of `stateless-unsound` for the aliasing pattern of `reborrowAfterWrite`: every
  interpretation of the axioms fails or diverges on the Rust analogue of the program, or validates
  `x0 = x1`, whether or not duplicate calls are merged. However, the signature
  `MutRawPtr T → Result (T × (T → Result Unit))` is **not** inherently stateless. The companion open
  pull requests #1454, #1497, #1548 and #1551 thread heap state inside the effect type — at their head
  commits `RustEffect.Input` has a heap event `guardedModify` and `Result α` is still
  `ITree RustEffect α` — while keeping that signature: no state argument is added to `Result` or to
  function signatures (#1454 defines
  `RawPtr.as_mut_unchecked {T : Type} [Pointee T] (p : MutRawPtr T) : Result (T × (T → Result Unit))`),
  so the extracted code is unchanged. Under those designs the two `as_mut` calls run against different
  heaps (as in the toy's `effSem` and `lockSem`), and #1537's restriction on merging duplicate calls is
  soundness-critical. What puts a translation in the stateless class is a failure-and-divergence-only
  effect type — not the absence of an explicit state parameter, and not the fact that two occurrences
  of `Ptr.as_mut ptr` are the same term.

  Basis: derived (modeling bridge)

* **End points and the claim that timing affects only completeness.** The pull request's short /
  regular / long heuristics correspond, in the toy, to placements near `eagerPlacement` (the short
  heuristic ends a region when its borrows are dead according to a liveness analysis that counts every
  dereference `*r`, read or write, as a use), placements near `lazyPlacement`, and placements beyond the
  owner's next access, respectively; the heuristics' actual output depends on joins, loops, and function
  boundaries absent from the toy. The toy's unchecked translation `effSem` is unsound outside the
  liveness window (`effSem_respecting_tight_*`: wrong `some o` outcomes) because its write-back is
  unchecked copy-in/copy-out and soundness is stated as equality of outcomes. In the borrow-locking
  translation `lockSem` — the toy counterpart of the `borrow`/`endBorrow` heap models of #1454 and
  #1551, where a borrowed cell is inaccessible until the backward function runs — the same placements
  are stuck instead (`outside_window_effSem_wrong_lockSem_stuck`): every placement is sound under
  partial refinement (`lock-sound`), and the translation succeeds exactly on liveness-respecting
  placements of programs without scoping errors (`lock-complete`, `lock-success-in-window`). So the
  toy's out-of-window unsoundness of `effSem` does **not** refute #1537's claim that region-end timing
  affects only completeness, under borrow-locking semantics; #1551's test file likewise classifies its
  late-end example `ptr_as_mut_write.incomplete` as "Sound, but the model rejects a valid program".
  Under the lock model the window is "after the last use", not "after the last write"
  (`lockSem_complete_tight_endsAfterLastUse`), matching #1537's liveness analysis.

  Basis: derived (modeling bridge)

* **Prophecy encodings.** `prophSem` filters runs at the end; it has no intermediate assertions. Its
  tolerance of late region ends (`prophecy-sound-wider-window`) is a property of that end-of-run filter,
  not of weakest-precondition or CHC-based verifiers, where a check between an owner access and a late
  region end sees an unconstrained prophecy.

  Basis: derived (modeling bridge)

* **Liveness analysis.** `eagerPlacement` is computed syntactically on straight-line code; it is not
  a model of any liveness analysis implementation.

  Basis: derived (modeling bridge)

### Why merging duplicate calls is unsound once backward functions have effects

`reborrowAfterWrite c` calls `as_mut` twice on the same pointer with a write through the first
reference in between. In any stateless translation the two forward calls are applications of one
function to one argument, so the translated program satisfies `x0 = x1` in every successful run
(`statelessSem_reborrowAfterWrite_vars_eq`); a pass that merges the second call into the first
(common-subexpression elimination of duplicate calls) is semantics-preserving there — and the
equation it relies on is false of the program (`stateless-unsound`). In the effectful translations the
first region's backward call writes `c` to the heap model before the second forward call reads it, so
the calls return different values (`effSem_distinguishes_duplicate_calls_positive_control`: `x0 = h 0`,
`x1 = c`; `lockSem_reborrowAfterWrite_positive_control`). There, replacing the second call by the result
of the first changes the result, which is the unsoundness of duplicate-call merging with effectful
backward functions. Two consequences that the cards make precise: (i) restricting the merge pass is
necessary for an effectful translation, but (ii) for a stateless translation it is not sufficient,
because the false equation is valid in the stateless semantics itself, with or without the pass. No
duplicate-call merging transformation is defined in the Lean project; this section is a reading of the
theorems above.

Basis: derived (a reading of the kernel-checked theorems named above)

### Counterexample index (all fully proved; canonical form: all other hypotheses hold and the conclusion fails)

| Counterexample | Result / dropped hypothesis | Instance |
| :--- | :--- | :--- |
| `effSem_lazyPlacement_eq_heapSem_tight_aliasingDiscipline` | `sound-lazy` / `had` | rawWriteDuringBorrow; placements lazyPlacement |
| `effSem_eagerPlacement_eq_heapSem_tight_aliasingDiscipline` | `sound-eager` / `had` | rawWriteDuringBorrow; placements eagerPlacement |
| `pureBackSem_unsound_tight_ne` | `pure-backward-unsound` / `hc` | reborrowAfterWrite 0 |
| `statelessSem_validates_false_tight_ne` | `stateless-unsound` / `hc` | reborrowAfterWrite 0; placements lazyPlacement |
| `effSem_respecting_tight_endsAfterCreation` | `endpoint-window` / `hc` | unusedRegion; placements endAt 0 |
| `effSem_respecting_tight_endsAfterLastUse` | `endpoint-window` / `hu` | reborrowAfterWrite 5; placements endBeforeWrite |
| `effSem_respecting_tight_endsByNextOwnerAccess` | `endpoint-window` / `ho` | reborrowAfterWrite 5; placements endAfterReborrow |
| `effSem_respecting_tight_endsByProgramEnd` | `endpoint-window` / `he` | writeOnce; placements endAt 3 |
| `effSem_generalized_tight_endsAfterCreation` | `endpoint-window-last-write` / `hc` | unusedRegion; placements endAt 0 |
| `effSem_generalized_tight_endsAfterLastWrite` | `endpoint-window-last-write` / `hw` | reborrowAfterWrite 5; placements endBeforeWrite |
| `effSem_generalized_tight_endsByNextOwnerAccess` | `endpoint-window-last-write` / `ho` | reborrowAfterWrite 5; placements endAfterReborrow |
| `effSem_generalized_tight_endsByProgramEnd` | `endpoint-window-last-write` / `he` | writeOnce; placements endAt 3 |
| `effSem_generalized_tight_aliasingDiscipline` | `endpoint-window-last-write` / `had` | readAfterRawWrite; placements endAt 2 |
| `lockSem_complete_tight_endsAfterCreation` | `lock-complete` / `hc` | unusedRegion; placements endAt 0 |
| `lockSem_complete_tight_endsAfterLastUse` | `lock-complete` / `hu` | writeThenRead 5; placements endAt 2 |
| `lockSem_complete_tight_endsByNextOwnerAccess` | `lock-complete` / `ho` | reborrowAfterWrite 5; placements endAfterReborrow |
| `lockSem_complete_tight_endsByProgramEnd` | `lock-complete` / `he` | writeOnce; placements endAt 3 |
| `respectsLiveness_of_lockSem_tight_success` | `lock-success-in-window` / `hl` | reborrowAfterWrite 5; placements endAfterReborrow |
| `heapSem_eq_some_of_lockSem_tight_success` | `lock-sound` / `hl` | reborrowAfterWrite 5; placements endAfterReborrow |
| `prophOutcome_iff_effSem_tight_endsByNextOwnerAccess` | `prophecy-agreement` / `ho` | reborrowAfterWrite 5; placements endAfterReborrow |
| `prophOutcome_iff_effSem_tight_endsByProgramEnd` | `prophecy-agreement` / `he` | writeOnce; placements endAt 3 |
| `prophOutcome_iff_heapSem_tight_aliasingDiscipline` | `prophecy-sound-wider-window` / `had` | readAfterRawWrite; placements endAt 4 |
| `prophOutcome_iff_heapSem_tight_endsAfterCreation` | `prophecy-sound-wider-window` / `hc` | unusedRegion; placements endAt 0 |
| `prophOutcome_iff_heapSem_tight_endsAfterLastWrite` | `prophecy-sound-wider-window` / `hw` | reborrowAfterWrite 5; placements endBeforeWrite |
| `prophOutcome_iff_heapSem_tight_endsByProgramEnd` | `prophecy-sound-wider-window` / `he` | writeOnce; placements endAt 3 |

## Boundaries

### Non-claims, per result

**`sound-lazy`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* Nothing is proved about Aeneas itself (its symbolic interpreter, region-ending heuristics, joins, or generated code); any connection is a derived modeling bridge stated in the prose, not a kernel-checked fact.
* Refinement is stated as equality of outcomes (both succeed with the same observation, or both are stuck); this relies on both semantics being deterministic and is not a claim about nondeterministic or relational semantics. A stuck translation counts as disagreeing with a succeeding heap semantics; the partial-refinement reading (translation succeeds with o implies heap semantics succeeds with o) is the subject of lock-sound.
* AliasingDiscipline is a simplified condition in the spirit of Stacked Borrows (no other access of any kind to the cell while the reference is used). Aliasing models that permit some foreign accesses, e.g. Tree Borrows, where a mutable reference that has not yet been written allows foreign reads, are not examined; a program violating AliasingDiscipline is not 'undefined' in the toy, it is simply outside the theorem.
* AliasingDiscipline and RespectsLiveness constrain only the ordering between uses of an asMut reference and later owner accesses to the same cell; they do not check reference scoping (that every read or write names an earlier asMut). Ill-scoped programs such as danglingUse (`[read 0 0]`) and useBeforeCreation satisfy both and are stuck (`none`) in heapSem, effSem, and lockSem (aliasingDiscipline_admits_ill_scoped and lockSem_none_of_ill_scoped_respectsLiveness, with placements endAt 0 and lazyPlacement respectively); for them the equation holds only because both sides are stuck.
* Out-of-window placements give wrong `some o` outcomes in effSem specifically because its write-back is unchecked copy-in/copy-out (the cell stays freely accessible in the heap model while the region is open, and the region's local value stays writable and readable after its backward call) and because soundness is stated as equality of outcomes. In the borrow-locking translation lockSem, where the forward call lends the cell until the backward call and the backward call closes the region, the same placements are stuck (`none`) instead (outside_window_effSem_wrong_lockSem_stuck); there every placement is sound under partial refinement (lock-sound) and only completeness depends on the end point (lock-complete, lock-success-in-window). The toy's out-of-window failures of effSem do not refute the claim of Aeneas pull request #1537 that region-end timing affects only completeness, under borrow-locking semantics.
* The heap semantics is a reference semantics chosen for this package, not a formalization of the Rust abstract machine.

**`sound-eager`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* Nothing is proved about Aeneas itself (its symbolic interpreter, region-ending heuristics, joins, or generated code); any connection is a derived modeling bridge stated in the prose, not a kernel-checked fact.
* AliasingDiscipline and RespectsLiveness constrain only the ordering between uses of an asMut reference and later owner accesses to the same cell; they do not check reference scoping (that every read or write names an earlier asMut). Ill-scoped programs such as danglingUse (`[read 0 0]`) and useBeforeCreation satisfy both and are stuck (`none`) in heapSem, effSem, and lockSem (aliasingDiscipline_admits_ill_scoped and lockSem_none_of_ill_scoped_respectsLiveness, with placements endAt 0 and lazyPlacement respectively); for them the equation holds only because both sides are stuck.
* Out-of-window placements give wrong `some o` outcomes in effSem specifically because its write-back is unchecked copy-in/copy-out (the cell stays freely accessible in the heap model while the region is open, and the region's local value stays writable and readable after its backward call) and because soundness is stated as equality of outcomes. In the borrow-locking translation lockSem, where the forward call lends the cell until the backward call and the backward call closes the region, the same placements are stuck (`none`) instead (outside_window_effSem_wrong_lockSem_stuck); there every placement is sound under partial refinement (lock-sound) and only completeness depends on the end point (lock-complete, lock-success-in-window). The toy's out-of-window failures of effSem do not refute the claim of Aeneas pull request #1537 that region-end timing affects only completeness, under borrow-locking semantics.
* The eager placement is defined syntactically from the straight-line program; it is not a liveness analysis over control flow and says nothing about the correctness of any implementation of one.
* A use that precedes the creation (a scoping error) does not pull the eager end before the creation (eagerPlacement_example_neg); such programs are stuck on both sides.

**`pure-backward-unsound`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* The pure-backward translation here still reads the heap model in forward calls; the result is about this translation. The general statement for translations without any heap state is stateless-unsound.
* It does not say that every program is mistranslated: on programs that never write through an as_mut reference the two translations can agree.
* Pure backward functions coincide with never ending any region (lemma pureBackSem_eq_effSem_neverEndPlacement); this result is therefore also an instance of the EndsByProgramEnd/EndsByNextOwnerAccess failures of endpoint-window.

**`stateless-unsound`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* 'Stateless' means exactly statelessSem: the forward call's result is a function of the pointer alone (or a failure), and backward calls can only succeed or fail. Divergence is modelled like failure (no observation). Models in which an as_mut call's result can depend on earlier calls (a heap, a counter, an oracle consulted per call) are stateful by this definition and not covered.
* statelessSem F B assumes a deterministic forward model that depends only on the pointer, not on the call site or on earlier calls, and freely copied pointer values. Translations with nondeterministic or per-call-site choices (for example a prophecy per region, as in prophSem), or APIs that thread an unaliased pointer token (a `&mut` to a pointer wrapper whose backward function returns an updated token), lie outside statelessSem. On programs with raw reads or writes (none occur in reborrowAfterWrite c), sstep additionally reads raw cells through F and treats raw writes as no-ops.
* A stateless model can avoid validating a false statement on this program only by failing on it; the result does not say how often such models fail on other programs.
* Disabling a duplicate-call merging pass does not escape the result: the equation x0 = x1 holds in every successful run of the stateless semantics itself, so it is provable about the translated program whether or not a pass rewrites it.
* Derived modeling bridge, not kernel-checked. At head commit 5c28fe8def8db99041d22503175591ba1fa47915 of Aeneas pull request #1537, considered in isolation, `Result` (backends/lean/Aeneas/Std/Primitives.lean) is an interaction tree whose only effects are failure and divergence, with no heap state; so that commit alone falls in this result's stateless class for the aliasing pattern of reborrowAfterWrite: every interpretation of the generated `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` fails or diverges on the Rust analogue of the program, or validates `x0 = x1`. However, the signature `MutRawPtr T → Result (T × (T → Result Unit))` is not inherently stateless: the companion open pull requests #1454, #1497, #1548 and #1551 thread heap state inside the effect type (a heap event `guardedModify` in `RustEffect`) while keeping that signature (no state argument is added to `Result` or to function signatures; #1454 defines `RawPtr.as_mut_unchecked` with exactly this shape), so the extracted code is unchanged; under those designs the two `as_mut` calls run against different heaps, and #1537's restriction on merging duplicate calls is soundness-critical. Membership in the stateless class comes from a failure-and-divergence-only effect type, not from the absence of an explicit state parameter, and not from the fact that two occurrences of `Ptr.as_mut ptr` are the same term. The toy's effSem and lockSem are models of such stateful designs; this result says nothing about them.

**`endpoint-window`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* Nothing is proved about Aeneas itself (its symbolic interpreter, region-ending heuristics, joins, or generated code); any connection is a derived modeling bridge stated in the prose, not a kernel-checked fact.
* Refinement is stated as equality of outcomes (both succeed with the same observation, or both are stuck); this relies on both semantics being deterministic and is not a claim about nondeterministic or relational semantics. A stuck translation counts as disagreeing with a succeeding heap semantics; the partial-refinement reading (translation succeeds with o implies heap semantics succeeds with o) is the subject of lock-sound.
* AliasingDiscipline and RespectsLiveness constrain only the ordering between uses of an asMut reference and later owner accesses to the same cell; they do not check reference scoping (that every read or write names an earlier asMut). Ill-scoped programs such as danglingUse (`[read 0 0]`) and useBeforeCreation satisfy both and are stuck (`none`) in heapSem, effSem, and lockSem (aliasingDiscipline_admits_ill_scoped and lockSem_none_of_ill_scoped_respectsLiveness, with placements endAt 0 and lazyPlacement respectively); for them the equation holds only because both sides are stuck.
* EndsAfterLastUse cannot be dropped but can be weakened: ending after the last write suffices given the aliasing discipline (endpoint-window-last-write).
* 'Only completeness varies' is not modelled by this result: for effSem every liveness-respecting placement gives the same outcome (corollary effSem_eq_effSem_of_respectsLiveness), and completeness effects of real tools (stuck symbolic execution at joins, loops, function boundaries) are absent. The completeness side is modelled only by lockSem (lock-complete, lock-success-in-window).
* Out-of-window placements give wrong `some o` outcomes in effSem specifically because its write-back is unchecked copy-in/copy-out (the cell stays freely accessible in the heap model while the region is open, and the region's local value stays writable and readable after its backward call) and because soundness is stated as equality of outcomes. In the borrow-locking translation lockSem, where the forward call lends the cell until the backward call and the backward call closes the region, the same placements are stuck (`none`) instead (outside_window_effSem_wrong_lockSem_stuck); there every placement is sound under partial refinement (lock-sound) and only completeness depends on the end point (lock-complete, lock-success-in-window). The toy's out-of-window failures of effSem do not refute the claim of Aeneas pull request #1537 that region-end timing affects only completeness, under borrow-locking semantics.

**`endpoint-window-last-write`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* Nothing is proved about Aeneas itself (its symbolic interpreter, region-ending heuristics, joins, or generated code); any connection is a derived modeling bridge stated in the prose, not a kernel-checked fact.
* AliasingDiscipline and RespectsLiveness constrain only the ordering between uses of an asMut reference and later owner accesses to the same cell; they do not check reference scoping (that every read or write names an earlier asMut). Ill-scoped programs such as danglingUse (`[read 0 0]`) and useBeforeCreation satisfy both and are stuck (`none`) in heapSem, effSem, and lockSem (aliasingDiscipline_admits_ill_scoped and lockSem_none_of_ill_scoped_respectsLiveness, with placements endAt 0 and lazyPlacement respectively); for them the equation holds only because both sides are stuck.
* Out-of-window placements give wrong `some o` outcomes in effSem specifically because its write-back is unchecked copy-in/copy-out (the cell stays freely accessible in the heap model while the region is open, and the region's local value stays writable and readable after its backward call) and because soundness is stated as equality of outcomes. In the borrow-locking translation lockSem, where the forward call lends the cell until the backward call and the backward call closes the region, the same placements are stuck (`none`) instead (outside_window_effSem_wrong_lockSem_stuck); there every placement is sound under partial refinement (lock-sound) and only completeness depends on the end point (lock-complete, lock-success-in-window). The toy's out-of-window failures of effSem do not refute the claim of Aeneas pull request #1537 that region-end timing affects only completeness, under borrow-locking semantics.
* Ending a region between its last write and a later read relies on the target treating the borrow's forward value as an ordinary immutable local after the backward call. In a source-level or symbolic semantics where reading `*r` requires the borrow to be still alive (the liveness analysis src/interp/InterpLiveness.ml of Aeneas pull request #1537 counts every dereference of `r`, read or write, as a use), and in the toy's borrow-locking translation lockSem (lockSem_complete_tight_endsAfterLastUse), ending the region before a read gets stuck; this result gives no licence for such semantics.
* Not a characterization of all sound placements: finer conditions (e.g. owner reads that do not conflict with an unwritten reference) are not examined.

**`lock-complete`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* Nothing is proved about Aeneas itself (its symbolic interpreter, region-ending heuristics, joins, or generated code); any connection is a derived modeling bridge stated in the prose, not a kernel-checked fact.
* AliasingDiscipline and RespectsLiveness constrain only the ordering between uses of an asMut reference and later owner accesses to the same cell; they do not check reference scoping (that every read or write names an earlier asMut). Ill-scoped programs such as danglingUse (`[read 0 0]`) and useBeforeCreation satisfy both and are stuck (`none`) in heapSem, effSem, and lockSem (aliasingDiscipline_admits_ill_scoped and lockSem_none_of_ill_scoped_respectsLiveness, with placements endAt 0 and lazyPlacement respectively); for them the equation holds only because both sides are stuck.
* lockSem is a toy borrow-locking model (one lent flag per cell, an open-region count, stuck on any conflicting access); it is not the heap model, separation logic, or weakest-precondition calculus of any Aeneas pull request, and it does not model shared borrows, partial permissions, or byte-level cells.
* Completeness here means producing the heap semantics' outcome on the toy's straight-line programs; it says nothing about whether a verifier can prove properties of the translated program, or about joins, loops, and function boundaries.

**`lock-success-in-window`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* Nothing is proved about Aeneas itself (its symbolic interpreter, region-ending heuristics, joins, or generated code); any connection is a derived modeling bridge stated in the prose, not a kernel-checked fact.
* Says nothing about the unchecked translation effSem, which succeeds (with a wrong outcome) on some out-of-window placements (outside_window_effSem_wrong_lockSem_stuck).
* Stuckness is not a diagnosis of the placement: the converse of this result fails. Every out-of-window placement makes lockSem stuck (the contrapositive), but lockSem is also stuck on programs with reference scoping errors under liveness-respecting placements: danglingUse (`[read 0 0]`) with endAt 0 and useBeforeCreation with its lazy placement satisfy RespectsLiveness and have lockSem = none (lockSem_none_of_ill_scoped_respectsLiveness, aliasingDiscipline_admits_ill_scoped). A stuck borrow-locking translation therefore indicates an out-of-window placement or a scoping error.
* lockSem is a toy borrow-locking model (one lent flag per cell, an open-region count, stuck on any conflicting access); it is not the heap model, separation logic, or weakest-precondition calculus of any Aeneas pull request, and it does not model shared borrows, partial permissions, or byte-level cells.

**`lock-sound`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* Nothing is proved about Aeneas itself (its symbolic interpreter, region-ending heuristics, joins, or generated code); any connection is a derived modeling bridge stated in the prose, not a kernel-checked fact.
* Partial refinement only: lockSem may be stuck where the heap semantics succeeds (incompleteness); it is stuck exactly off the window for programs without scoping errors (lock-complete, lock-success-in-window).
* Derived modeling bridge, not kernel-checked: this is the toy's version of the claim that end-point timing matters only for completeness, for a model in which a lent cell is inaccessible until its backward call (as in the borrow/endBorrow models of the companion Aeneas pull requests #1454 and #1551). It is not a proof about those models, about Aeneas's heuristics, or about a translation whose write-back is unchecked (effSem, where out-of-window end points are unsound).

**`prophecy-agreement`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* Agreement is equality of end-of-run outcome sets of two toy semantics, not a correspondence between proofs, verification conditions, or CHC encodings.
* The prophecy encoding here (an up-front prophecy assignment and a flag recording resolution assumptions, filtered at the end of the run) is a toy; it is not RustHorn's CHC translation, Creusot's Why3 encoding, or RustHornBelt's Iris model.
* Agreement does not imply soundness: outside the endpoint-window conditions both encodings can be wrong together (e.g. ending before a write).
* Resolution is an assumption, not a proof obligation. Where a resolution can never hold, `ProphOutcome` is empty; in a verifier that encodes resolution by `assume`, that corresponds to `assume False`, which makes everything after it vacuously verified. Outside the aliasing discipline and the window this happens while the heap semantics succeeds (prophOutcome_empty_ownerReadThenWriteBack: `r0 = &mut *p; x0 = *p; *r0 = x0 + 1` with r0 ended at the program end requires `φ 0 = φ 0 + 1`).

**`prophecy-sound-wider-window`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* AliasingDiscipline and RespectsLiveness constrain only the ordering between uses of an asMut reference and later owner accesses to the same cell; they do not check reference scoping (that every read or write names an earlier asMut). Ill-scoped programs such as danglingUse (`[read 0 0]`) and useBeforeCreation satisfy both and are stuck (`none`) in heapSem, effSem, and lockSem (aliasingDiscipline_admits_ill_scoped and lockSem_none_of_ill_scoped_respectsLiveness, with placements endAt 0 and lazyPlacement respectively). RespectsLiveness implies this result's window hypotheses (EndsAfterLastUse implies EndsAfterLastWrite, endsAfterLastWrite_of_endsAfterLastUse), so the result applies to them; since heapSem is stuck, both sides of the equivalence are false for every o (no prophecy outcome exists), and the equivalence holds only for that reason.
* RustHorn's core calculus COR and Creusot as presented in its 2022 paper exclude unsafe code. Verification frameworks that combine prophecy-style reasoning with raw pointers (RefinedRust, whose borrow names are inspired by prophecy variables; Gillian-Rust, which embeds parametric prophecies; and Creusot's later ghost permissions for raw pointers) enforce aliasing through separation-logic or ghost ownership rather than the toy's unguarded flat heap; this result says nothing about them.
* `ProphOutcome` keeps a run only if every resolution assumption holds, checked at the end of the run, in a language without intermediate assertions or panics. When a region ends after an owner access (outside EndsByNextOwnerAccess), the owner reads the prophecy before the region-end resolution constrains it; in a weakest-precondition encoding (Why3/Creusot style) or a CHC encoding (RustHorn style), a safety check or assertion between that access and the region end sees an unconstrained prophecy and can fail verification even though the final outcome is right. Tolerance of late ends is a property of this end-of-run filter, not of prophecy-based verifiers.
* Resolution is an assumption, not a proof obligation: where a resolution can never hold, `ProphOutcome` is empty, which in an assume-based verifier corresponds to `assume False` and vacuous verification of everything after it. Outside the aliasing discipline and the window this happens while the heap semantics succeeds (prophOutcome_empty_ownerReadThenWriteBack).

**`aliasing-iff-placement`**

* Toy model only: straight-line programs over integer cells, raw pointers as bare addresses; no allocation, deallocation, pointer arithmetic, casts, typed memory, provenance, branches, loops, joins, function calls, shared references, `from_mut`-style (reference to raw pointer) regions, interior mutability, or concurrency.
* AliasingDiscipline and RespectsLiveness constrain only the ordering between uses of an asMut reference and later owner accesses to the same cell; they do not check reference scoping (that every read or write names an earlier asMut). Ill-scoped programs such as danglingUse (`[read 0 0]`) and useBeforeCreation satisfy both and are stuck (`none`) in heapSem, effSem, and lockSem (aliasingDiscipline_admits_ill_scoped and lockSem_none_of_ill_scoped_respectsLiveness, with placements endAt 0 and lazyPlacement respectively); for them both sides of each equivalence are true even though heapSem, effSem, and lockSem are stuck, so neither side implies that the program runs.
* Not a decision procedure for real Rust code; the toy's discipline is checked on straight-line programs with syntactic uses.

### Escape hatches of the impossibility results

* `pure-backward-unsound`: defeated by `c = h 0` (the write through the first reference does not change the cell; `pureBackSem_unsound_tight_ne`), by giving backward functions an effect on the heap model (`effSem_reborrowAfterWrite_positive_control`, `lockSem_reborrowAfterWrite_positive_control`), and it concerns one program: on programs that never write through an `as_mut` reference the pure and heap semantics can agree.
* `stateless-unsound`: defeated by `c = h 0` (`statelessSem_validates_false_tight_ne`); by any model outside `statelessSem` — a forward result that depends on earlier calls (a heap, a counter, an oracle consulted per call), per-call-site or nondeterministic choices (such as a prophecy per region, as in `prophSem`), or an unaliased pointer token threaded through backward functions; with a single `as_mut` call the natural stateless model is correct (`statelessSem_single_reborrow_positive_control`); and stateful effectful translations distinguish the duplicate calls (`effSem_distinguishes_duplicate_calls_positive_control`).

### Tightness status

Every hypothesis of every result is `tight`, with a fully proved counterexample named in its ledger. No hypothesis has `harmless` or `unknown` status.

### Disproved, unknown, or dropped statements

None. All twelve statements of the package, and every counterexample, non-vacuity witness, and positive control, are kernel-checked as stated; no statement was found false or left unresolved.

### Not examined

Control flow (branches, loops, joins) and function boundaries, where real translators' region-ending heuristics and completeness losses live; `from_mut`-style regions (reference to raw pointer); shared references and interior mutability; aliasing models other than the toy's ordering discipline (in particular Tree Borrows' tolerance of foreign reads before the first write); verifiers with intermediate assertions for the prophecy encoding; any implementation of a liveness analysis.

## Evidence

**Kernel check.** `lake build` of `lean/` under `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`; local toolchain reports `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`), observed 2026-11-20. An axiom audit with Lean's `collectAxioms` over all 755 declarations of the library's modules found no axioms other than `propext`, `Classical.choice`, `Quot.sound`, and no `axiom`/`opaque` declarations; the sources contain no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, or `unsafe`. The full per-declaration record is `audit/axioms.json`.

**Statement hashes.** For each card-referenced name, `statement sha256` is the SHA-256 of `toString (repr ci.type)` of the declaration, and `closure sha256` is the SHA-256 of the newline-joined, sorted list of `name : repr type` (followed by ` := repr value` for definitions; theorem bodies excluded) over every package-local constant reachable from the statement; `closure size` counts those constants. Recorded in `audit/statements.json` and recomputed by `support/revalidate.py`.

| Theorem | Role | Axioms | Statement sha256 | Closure sha256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `effSem_lazyPlacement_eq_heapSem_of_aliasingDiscipline` | sound-lazy: result | `Classical.choice`, `Quot.sound`, `propext` | `3f84c8023208083957dff21d74629db782abdd73d525c095b25f0924ef802fcd` | `fdace292ace81d3d8ca29aa1e86bb04e77915626fc4b642cb2863574bc0b1ed0` (96) |
| `effSem_lazyPlacement_eq_heapSem_tight_aliasingDiscipline` | sound-lazy: counterexample for `had` | `propext` | `ab0bfd07557c9371a6da335eaea3ad39b34ff4cb7b1931da8a91c85204603321` | `aed5bf2c4a77ca26da1029437acdd2b5aa12e92388a93d9d70a1ff904ad74c53` (98) |
| `effSem_lazyPlacement_nonvacuous` | sound-lazy: non-vacuity | `propext` | `6532227217f0192b2a4ecff7086143794b52bba95eee7fc986bbf7d9e981ab37` | `d2c71c6b862bb781d3084f0d751da2313bcc8c55fa7094adf6acdef594509ef3` (35) |
| `effSem_reborrowAfterWrite_positive_control` | sound-lazy: non-vacuity; pure-backward-unsound: positive control | `Quot.sound`, `propext` | `43a0b3c75f0afbdd43675ef3d5f69ba44b52a532cb4d1c20f50efc6da17f6a77` | `ccabc161032dd081f2f9b114726f4060f5a5655d80ebd89133958c810eed561b` (91) |
| `effSem_eagerPlacement_eq_heapSem_of_aliasingDiscipline` | sound-eager: result | `Classical.choice`, `Quot.sound`, `propext` | `96d51542e64cea0b8ed042790bef883634be447303148f082fb5f368878defd0` | `c117dd1ddec480b7b512d0e0525a8724950ab1a828c55343671982d3d4c8c8f7` (96) |
| `effSem_eagerPlacement_eq_heapSem_tight_aliasingDiscipline` | sound-eager: counterexample for `had` | `propext` | `902a7cf96a3b280d6857e7a16e2d946ca704baad0ff64da569a885ca8c424ed3` | `8525b880cec8df463cdc5b7bb2603df6c61c2d3d17cfffd49cad4b5518e97fe2` (98) |
| `effSem_eagerPlacement_nonvacuous` | sound-eager: non-vacuity | `propext` | `e4cdfbcfb96beeef36e68d6522b3af26034a70b86d67ab08622c22f1e1d95889` | `4906571d35bceff010c44bbac262d18277999442cd45ab8229d7fcfde41fa55e` (56) |
| `effSem_eagerPlacement_instance` | sound-eager: non-vacuity | `propext` | `4d93bdc4d7687bb8e43e4c527f33f0f9438037a64fed02e5769c450cee2a35c8` | `9e3c365392b0c624731d23760b669238b07a0462c0b0eacea98d273c33da573d` (89) |
| `pureBackSem_unsound_on_reborrowAfterWrite` | pure-backward-unsound: result | `propext` | `5c48e50a1bd93aee2e4e0ee005327406619ea7d0e47a53faa3123069cfe8c611` | `d999da369f1bd0a9335625b36e39a64a438b24331f66a8c35d345a2fecff9dd2` (88) |
| `pureBackSem_unsound_tight_ne` | pure-backward-unsound: counterexample for `hc` | `Quot.sound`, `propext` | `3c3b71ac1ac4a946449d49bae7e736826dfb904162fec5490890394d4d80dc49` | `274a8818596c3cb9faeb692a69fcf823b1c2469b23251ed15ca06dbfcb637901` (89) |
| `reborrowAfterWrite_ne_nonvacuous` | pure-backward-unsound: non-vacuity; stateless-unsound: non-vacuity | `propext` | `fee6d28de3112660d9ff38c32e6931f30a8042a927b5bf5e7cb4839865c799ea` | `f11f8acda192812aa4d3dcaa9eb57ff7b0daabe91f0f425cc3853d5bce9f117a` (75) |
| `lockSem_reborrowAfterWrite_positive_control` | pure-backward-unsound: positive control; lock-complete: non-vacuity; lock-sound: non-vacuity | `Quot.sound`, `propext` | `26606d8846382ed2f1f5299680dd908581d03a982c7f446a61917c05f26dce0f` | `3a11000a07728ea017361ddc8f91d1cdae6aade78fae7a049024268f4c830c0a` (92) |
| `statelessSem_validates_false_duplicate_call_equation` | stateless-unsound: result | `Classical.choice`, `Quot.sound`, `propext` | `c41acee9cacd8f264e622b11e121698ed00b80eda2d4232fe5c2658cfa2302c3` | `86513a54edc775639c6c75b4503572f32c25273b8f5ce1437d0ca0d4a2e1679c` (93) |
| `statelessSem_validates_false_tight_ne` | stateless-unsound: counterexample for `hc` | `propext` | `36f905627db9f8781ab14ed5adbe048221886bdaa2f6124c9ef383ab304a89aa` | `0a9cc969c77d0c46cf262ba49f79914f7cccfe4fabc2c951e63676d73acd347c` (98) |
| `effSem_distinguishes_duplicate_calls_positive_control` | stateless-unsound: positive control | `propext` | `7f7f6bc5f50de10bd6971ec1a8a51c7a4061e335802f7776f8a685a4f9549fad` | `1b808650f59ec514b457ca1afd3d7e8f12826e5085f85e61e26dd2695eee3889` (78) |
| `statelessSem_single_reborrow_positive_control` | stateless-unsound: positive control | `propext` | `82745682c9b93cc9c32dc28b1f6c9acd0bd74d887dad15a2c651f161cbbbc998` | `69d2253d757753e2748eb3db448eb2cec58eb38d8ecc2947ef7059572f05ac67` (81) |
| `effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd` | endpoint-window: result | `Classical.choice`, `Quot.sound`, `propext` | `aec5720b02e4519c3b3df628df11872fe3bf4c7de6b785da35097dd88bfe1b54` | `80efd1ef26797c615bb00ae4a4b032b06e9a8adc1583147e3561e824e3bb1c09` (95) |
| `effSem_respecting_tight_endsAfterCreation` | endpoint-window: counterexample for `hc` | `propext` | `7bb80c4f7899cf52912f94ee360a446d37f27a0ca6d3b4b55bf02d285cb1fbc8` | `8d4bb38a874b6c84fd1dac9e4c9e5f3428737f530c4bb47aeb66b0ba8940d434` (98) |
| `effSem_respecting_tight_endsAfterLastUse` | endpoint-window: counterexample for `hu` | `propext` | `7e1cc264447b3424d15a4cff14b80ff8d24f403a827305bb55728bca2fbf93fb` | `19909f1612d244251549906853432652386efe4c0f7cd561e2670e4c78d4be6a` (98) |
| `effSem_respecting_tight_endsByNextOwnerAccess` | endpoint-window: counterexample for `ho` | `propext` | `d93e2221dc79b23bde8816baa5e07c2ea4489939f721e09fab5a244faa4e3857` | `0d8b900b8d41711728e030b6330a7c05f94d3af3332b404ea1ff9675e846b044` (98) |
| `effSem_respecting_tight_endsByProgramEnd` | endpoint-window: counterexample for `he` | `propext` | `bff494b4435face9782d75e4d1146920b134c7ca4472540f2da3ed7f1764e910` | `1a616f2585ae990af66d29c621855fc2207f5239650bfac7eb1d74231c851f6d` (98) |
| `effSem_respecting_nonvacuous` | endpoint-window: non-vacuity; lock-complete: non-vacuity | `propext` | `5858e651e177f91cb4787408d5201f0047c45b318d16ebad19f8aea1f41afdac` | `8fb158e9cd0d3c5725d6abbfc05c65fc30dd878189c6c91177f362238606a63a` (46) |
| `effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastWrite_of_endsByNextOwnerAccess_of_endsByProgramEnd_of_aliasingDiscipline` | endpoint-window-last-write: result | `Classical.choice`, `Quot.sound`, `propext` | `c7091efb6a50d7f6687313317fc211fc88389940c71c861ccc0776777fd35d0d` | `e4b275685f8fa6746bfe08f01a3cfe68ec0dc57468ccb6a60e1a8803bdc9b2ba` (100) |
| `effSem_generalized_tight_endsAfterCreation` | endpoint-window-last-write: counterexample for `hc` | `propext` | `cfacd8799a94a369879f539929d4cd4679687a751787181e06b13e5ba60e0f83` | `a44fa06461fc9166cb0743bede151a05d2953d19df71d617097b40aab0cb11fd` (103) |
| `effSem_generalized_tight_endsAfterLastWrite` | endpoint-window-last-write: counterexample for `hw` | `propext` | `ea8373d4a81b329e791cb17e1063b21b97c7094102dec2d942ddd4ee23315d00` | `a52d3fd694dc25cb9e1336ab172ba22292b4beb5b42d2707bbd583a6183d2543` (103) |
| `effSem_generalized_tight_endsByNextOwnerAccess` | endpoint-window-last-write: counterexample for `ho` | `propext` | `eb0f0a5d31949774522cb1ff47212f643b34e5788461a1026abf1b6182b93266` | `ff566d10a72171316e83bbc362fb6850907fb4f63a3c01b0d946669bd6019e7b` (103) |
| `effSem_generalized_tight_endsByProgramEnd` | endpoint-window-last-write: counterexample for `he` | `propext` | `9588a19da6203fa3fe327d0e09dc09158519686dafd33cae9bf82b78089c78b8` | `c4fe2da8bd0098c9a634d56ae76d86448d310c7b5489713b629a0e6b88873a2d` (103) |
| `effSem_generalized_tight_aliasingDiscipline` | endpoint-window-last-write: counterexample for `had` | `propext` | `35333b3446142ef14fad541f869c071cb9f6ed2cd6580da4a3c1d6fb1d66f420` | `9c4375e3105bcb21772a985db8e72bce1343dfe5d414ce8df7ef04d94bb12d9c` (103) |
| `effSem_generalized_nonvacuous` | endpoint-window-last-write: non-vacuity | `propext` | `0581e0487b931bbeb5a0c88fe703e6f4169a6b80c48b2a18b1c452a07c9fda9f` | `d7d2937f854139c2a2a929552f0256dc46dba1df03f3c193fb8c1b870e83b7d6` (45) |
| `effSem_generalized_instance` | endpoint-window-last-write: non-vacuity | `propext` | `3114ea3a306809b9c0922e82e26ee3a06b8194f4a45ceb7fc443350113f0ad58` | `0ad3ed8d2ff04fa5c112480c7d39e0599a9a8069db09b93cafc4aa5f0f602661` (81) |
| `lockSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd` | lock-complete: result | `Classical.choice`, `Quot.sound`, `propext` | `0c7c06df3989178967b1599ff2e16adaae0c880c9a706712040f6f1dfe70bce8` | `7c2121223763aa2b5706d540231fe4a0ce53bfb1b2271a889183abb1902e9b6a` (96) |
| `lockSem_complete_tight_endsAfterCreation` | lock-complete: counterexample for `hc` | `propext` | `6745288ca9b0752b7309297d1a060e7bf2f2dd0a2018ed79fd5e9575d17695bd` | `7e660e431bd76edb8931b101123c60fe1882b9675ed7edcfa7fbe171b1e4300c` (99) |
| `lockSem_complete_tight_endsAfterLastUse` | lock-complete: counterexample for `hu` | `propext` | `6d92b1a4c6d29c44b097fe33d327081f6e776e12eaee08a7711a9caaed1b591a` | `04471459c3daf7cebd3a7b7bf2eca96079dcac12a4a686d0e6e2ac49faf584c1` (99) |
| `lockSem_complete_tight_endsByNextOwnerAccess` | lock-complete: counterexample for `ho` | `propext` | `e9379b39aa7e0538649fba1272f08591b48b6fca12932ef9669b054a412f1c23` | `de13ad7e0918fcbf3e5db29b1e9fefc3e64b9e87a0ade66a89866f6879b69d88` (99) |
| `lockSem_complete_tight_endsByProgramEnd` | lock-complete: counterexample for `he` | `propext` | `1119f073f1b8f4c2ee1a82e885eed9f4763015352ca573ee72198036ad0b980a` | `66d7a1b2d40de27401c53582184ea184f05d1c78df7e61a10c44bc876275765c` (99) |
| `respectsLiveness_of_lockSem_eq_some` | lock-success-in-window: result | `Classical.choice`, `Quot.sound`, `propext` | `77e46b686cfed34c7c93c2e73dd50cd058fb2455436dde96edf48fd66dff3634` | `37252d3d98410b47edd00f629459a184ab83d04052e45677dcf21ffbd8677506` (83) |
| `respectsLiveness_of_lockSem_tight_success` | lock-success-in-window: counterexample for `hl` | `propext` | `41f8c4136c1418819f390dd3248e3f0b5e20f10973abcdf830479c14aa5893b6` | `99968572d55976309586cd55dd53f9052272e8f6a99039bc89effa1c2a4f50c1` (86) |
| `lockSem_success_nonvacuous` | lock-success-in-window: non-vacuity; lock-sound: non-vacuity | `propext` | `d09c926440d3414c6418420fbd69f1462c0546473798e0fc7825bbf6ddffb847` | `747a360dd7a1d5064711d1811f7785ffe5c137814229681003323f4dfef7ba3a` (88) |
| `heapSem_eq_some_of_lockSem_eq_some` | lock-sound: result | `Classical.choice`, `Quot.sound`, `propext` | `c9002ea1acbe4cbf9ea919db54b612e3409bd5b09d6c957626dba37cb070a868` | `699a2ef079f1c14a0045e727a1c6a8b926cefb922df510299862c943eab7598f` (80) |
| `heapSem_eq_some_of_lockSem_tight_success` | lock-sound: counterexample for `hl` | `propext` | `79cbcd8484de30aff61988519212436eae2bb70b07e6c6f13047ced12ffa3fc3` | `4a6e6c90c8e90801f92c548faa47bb20538195c1f5d810599245b768a7d06fe1` (96) |
| `outside_window_effSem_wrong_lockSem_stuck` | lock-sound: non-vacuity | `propext` | `5576745bb8827fafcbc6f0e14507d3b7e19454d4537b3f44754c47c7c347ac23` | `32c304412f7ba38c1f2c28af839a6d3d9a8522486c919e334248e941b7669e2b` (100) |
| `prophOutcome_iff_effSem_of_endsByNextOwnerAccess_of_endsByProgramEnd` | prophecy-agreement: result | `Classical.choice`, `Quot.sound`, `propext` | `7f30ce765769054b164073354fd44ac7803b4a7b88c737e4fe3720016b373312` | `1bd41f2dc525ad9c76ef68b7d2b8126664e8d038ea539756d4e676a4dcdb6503` (87) |
| `prophOutcome_iff_effSem_tight_endsByNextOwnerAccess` | prophecy-agreement: counterexample for `ho` | `propext` | `2a6e9d7d30b5870eeb0b37a6d2ae61acb25cfdbcb009c65d320ea9e39e1a3c50` | `2348d9a5ffaa56b4b209a4a19f92ceb785307d5e044afbe527fb8bbaa07a0c11` (90) |
| `prophOutcome_iff_effSem_tight_endsByProgramEnd` | prophecy-agreement: counterexample for `he` | `propext` | `e80ec7963e151762da6c495f7d058ea5f06d3b9582b952df81afa7f748f28e93` | `058858f45e7e1a0aaac7ea0a88f09654adb8b2673e19a66ea2b6563da74163bf` (90) |
| `prophOutcome_iff_effSem_nonvacuous` | prophecy-agreement: non-vacuity | `propext` | `066190d1009be60999351e4ee54f09e7392f10972c84bf5fe8c1ddf9e9482961` | `1036bb61fb6688ea92205b652b0e1d065739e08ac5b097f9bfc251f741c24b93` (81) |
| `prophOutcome_iff_heapSem_of_aliasingDiscipline_of_endsAfterCreation_of_endsAfterLastWrite_of_endsByProgramEnd` | prophecy-sound-wider-window: result | `Classical.choice`, `Quot.sound`, `propext` | `e374eca8f09789ffa287b1ec97a9305f52a62f1b4427608b1974423b669324a3` | `7eba3aaf35c168d1f8620884b1d7eddcd350f6f63d6d95d9735172f4e493f8d7` (99) |
| `prophOutcome_iff_heapSem_tight_aliasingDiscipline` | prophecy-sound-wider-window: counterexample for `had` | `propext` | `b81f68c580eea0fd82a4ed0fd1cc0b42a975a7b8e66b3d3e6e3001e5025605f8` | `e19ac7986482efb2f572060a49312ee5303cc28d7b1bf4948d1aafbc07ac68a3` (102) |
| `prophOutcome_iff_heapSem_tight_endsAfterCreation` | prophecy-sound-wider-window: counterexample for `hc` | `propext` | `a2f5a45a4285148061163cfda3c8f06df2289894602dcf69ed7643870213400a` | `af550816a0b7dacdd991cfcbd9f5a0b5f3e425d8e2be5ebd4bf62ac555a6668c` (102) |
| `prophOutcome_iff_heapSem_tight_endsAfterLastWrite` | prophecy-sound-wider-window: counterexample for `hw` | `propext` | `76b972cccb73f9ffa168981320ad567de795931c0df43ff11a22f9054dc3bcb2` | `e728ced2530df4c376d1d697c4c742ccc107887713fe6768d5cd101fd0492667` (102) |
| `prophOutcome_iff_heapSem_tight_endsByProgramEnd` | prophecy-sound-wider-window: counterexample for `he` | `propext` | `ed8dcde5990f43bd65444b9f4c2f2aa5894e332f1ef7bbd94f5f54b96e446322` | `f7a69126838e0109e925f0335489aa8f65634c3048d3348a573e4eb24faf5c3e` (102) |
| `prophOutcome_iff_heapSem_nonvacuous` | prophecy-sound-wider-window: non-vacuity | `propext` | `65690ee974e3a47076b0f6a226a75d9b9d809584d6ba12b09f72468b4a8e677e` | `b3796b1b8d8b9f4c7cbd6aae812c01f218b52b30c069c1a2fa12fdb91ca67121` (44) |
| `prophecy_tolerates_late_end_instance` | prophecy-sound-wider-window: non-vacuity | `Quot.sound`, `propext` | `9cff71e5c7a06b0e1c933b19cb7e3422c0f12171c697f4e1817aab548961c0db` | `c9d75925fa3b22baa164458f7491f25c7019de3c6b787543ca8bebf3e56d0177` (95) |
| `aliasingDiscipline_iff_respectsLiveness_lazyPlacement` | aliasing-iff-placement: result | `Quot.sound`, `propext` | `b1aef9bfcd64c54129a9e13284237d15357da0d4fd5f18a7ccddbf5fe4bba9a5` | `13d9ffde5ccb68ccca17e8d666a0691e556b4fc07bd6e6119f84a5e1d8c79f77` (46) |
| `aliasingDiscipline_iff_nonvacuous` | aliasing-iff-placement: non-vacuity | `propext` | `25a7ce9d2bede9bb485d615522ceac7db5613a07b166fcea715825980edc9490` | `3de21c34c4f093c0911c328aada50ef20e18d9cbbaa0a814064e1e79fd3a9239` (48) |

Axioms of the proof infrastructure's main lemmas and of the supporting lemmas cited under **Boundaries** (from `audit/axioms.json`): `Sim.effSem_eq_heapSem`: `Classical.choice`, `Quot.sound`, `propext`; `Sim.lockSem_eq_effSem`: `Classical.choice`, `Quot.sound`, `propext`; `Sim.respectsLiveness_of_lockSem`: `Classical.choice`, `Quot.sound`, `propext`; `Sim.prophOutcome_iff_effSem`: `Classical.choice`, `Quot.sound`, `propext`; `Sim.prophSem_eq_of_move`: `Classical.choice`, `Quot.sound`, `propext`; `Sim.prophOutcome_iff_heapSem`: `Classical.choice`, `Quot.sound`, `propext`; `lockSem_none_of_ill_scoped_respectsLiveness`: `propext`; `aliasingDiscipline_admits_ill_scoped`: `propext`; `prophOutcome_empty_ownerReadThenWriteBack`: `Quot.sound`, `propext`.

**Primary sources** (exact records; what each is used for is stated where it is cited under **Findings**).

* Aeneas pull request AeneasVerif/aeneas#1537, 'Add alive hints to support raw-pointer functions eventually.' (opened 2026-11-05; open and unmerged when examined), head commit 5c28fe8def8db99041d22503175591ba1fa47915. In our words: it makes the backward functions of regions created by opaque raw-pointer conversions monadic ('effectful', returning `Result`) instead of pure or inlined. At the head commit the generated test output (tests/lean/StatefulLifetime.lean) declares `axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))` and `axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))`, and the test source (tests/src/stateful-lifetime.rs) uses the attribute `#[verify::stateful_lifetime(...)]`; the pull request description, written earlier, gives `from_mut` the type `T → Result ((Ptr T) × (Unit → Result T))` and calls the attribute `keep_alive`. It offers three heuristics for when such regions end (short: when the borrows held are dead according to a backward liveness analysis, src/interp/InterpLiveness.ml, which counts every dereference `*r`, read or write, as a use of `r`; regular; long: surviving joins), asserts that this timing 'should not matter for soundness, only completeness', and restricts the `simplify_duplicate_calls` pass (src/pure/PureMicroPassesGeneral.ml), whose previous comment said it 'will not be sound anymore once we allow stateful (backward) functions'. These are assertions in the pull request, not proofs.
* Son Ho and Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022. doi:10.1145/3547647 (arXiv:2206.07185). Each function with mutable borrows is translated to a forward function and backward functions per region; borrows are ended lazily ('we reorganize borrows in a lazy fashion, and don't terminate a borrow until we need to get the borrowed value back', Section 2); programs relying on interior mutability or unsafe code are out of scope (abstract); a proof of soundness of the semantics and translation is named as future work (Section 7). For code interacting with the outside world, the paragraph 'I/O and External Dependencies' lifts generated code into 'a combined-state + error monad' with an opaque `state` type (e.g. `val deserialize_fwd : state -> result (state & hash_map_t u64)`).
* Son Ho, Aymeric Fromherz, and Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024. doi:10.1145/3674640 (long version arXiv:2404.02680). Theorem 4.1: every run of the symbolic semantics LLBC# (which may end borrows at arbitrary points through reorganizations, rule E-Reorg: 'it is always possible to end a borrow early, but this may lead to an unnecessarily stuck execution') is matched by the concrete LLBC semantics; proved in the paper, with full proofs in the long version's appendices. Correctness of the functional translation is left to future work and unsafe code is not considered.
* Son Ho. Formal Verification of Rust Programs by Functional Translation. PhD thesis, Université PSL (prepared at Inria Paris), defended 2024-12-09. HAL tel-05004605. Its table of contents includes Chapter 11 'Soundness: LLBC# Defines a Borrow-Checker' (with Section 11.2 'A Heap-and-Addresses Interpretation of Valued Borrows' and 11.2.9 'The Pointer Language (PL)') and Chapter 13 'From Symbolic Semantics to Functional Code'. Only the table of contents and the abstract ('as long as they do not rely on interior mutability or unsafe code') were consulted; no claim about the chapters' content is made here.
* Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, and Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust. Proc. ACM Program. Lang. 4(POPL), Article 41, pp. 1-32, 2020. doi:10.1145/3371109. An operational semantics for memory accesses in Rust that 'defines an aliasing discipline and declares programs violating it to have undefined behavior' (abstract).
* Neven Villani, Johannes Hostert, Derek Dreyer, and Ralf Jung. Tree Borrows. Proc. ACM Program. Lang. 9(PLDI), Article 188, pp. 1019-1042, 2025. doi:10.1145/3735592. Mutable references 'start out as Reserved, not as Unique. Reserved allows local and foreign reads', until their first write through the reference (Section 2.2).
* Open, draft, unmerged (when examined) Aeneas pull requests that give `Result` heap effects: #1454 'NonNull and borrows of values behind raw pointers' (head fc68273b75beebb7fd74f9c3130e857b232960db), #1497 'Fournet/wip memory model' (head d17ca83fc07d712d1785f650840cb2073c259e69), #1548 'Heap model for raw pointers (from fournet/wip-memory-model)' (head 561b806a70789e090e305d1d992f92cad1de7ce0), and #1551 'Separation logic over the byte heap' (head 1d8f9aa0121faca8ff113c1b9b742b333e3e1519). At each head, `RustEffect.Input` (backends/lean/Aeneas/Std/Primitives.lean) has a heap event `guardedModify` besides `fail`, while `Result α` remains `ITree RustEffect α` with no state argument. At #1454's head, backends/lean/Aeneas/Std/Core/Ptr.lean defines `RawPtr.as_mut_unchecked {T : Type} [Pointee T] (p : MutRawPtr T) : Result (T × (T → Result Unit))` as `p.borrow` followed by returning `p.endBorrow` as the backward function, where `borrow` gives the cell away 'so that every access to the cell through a raw pointer fails until the borrow is ended with `endBorrow`'. At #1551's head, tests/lean/SafeUnsafe/Proofs.lean models the extracted `as_mut` by such a borrow and proves `ptr_as_mut_write.incomplete`: the extracted code returns the `as_mut` borrow only after the owner's borrow has ended, so reading the cell fails; the file classifies this case as 'Sound, but the model rejects a valid program'. Proposals under development, not merged code.
* Aeneas issue AeneasVerif/aeneas#1525, 'Bug: Cell::set / Atomic*::fetch_add through &self are modelled as pure, so a second get/fetch_add is merged with the first' (opened 2026-11-03): a stateless model of interior mutability plus duplicate-call merging yields generated code `ok (a = a)` for a function whose Rust result is false. An instance of the same phenomenon outside raw pointers.
* Aeneas pull request AeneasVerif/aeneas#1431, 'Define the state effect and implement the raw-pointer functions' (closed unmerged 2026-10-15), head commit 11f641de522c26266aaf664f6ade85ea1642058d: proposed adding a heap operation (`guardedModify`) to `RustEffect`, the event type of Aeneas's `Result` monad. At the head commit of #1537, `RustEffect.Input` (backends/lean/Aeneas/Std/Primitives.lean) has the single constructor `fail`, whose answer type is empty, so `Result` there is a failure-and-divergence monad.
* Faris Abou-Saleh, James Cheney, Jeremy Gibbons, James McKinna, and Perdita Stevens. Reflections on Monadic Lenses. In: S. Lindley, C. McBride, P. Trinder, D. Sannella (eds.), A List of Successes That Can Change the World, Lecture Notes in Computer Science, Springer, 2016, pp. 1-31. doi:10.1007/978-3-319-30936-1_1 (arXiv:1601.02484). Reviews formulations of bidirectional transformations 'that use monads to account for effects', attending to 'the obstacles to naively adding monadic effects to existing definitions of pure bx such as lenses' (abstract). Background for forward/backward pairs with effects; consulted only through its abstract.
* Yusuke Matsushita, Takeshi Tsukada, and Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, LNCS, pp. 484-514, doi:10.1007/978-3-030-44914-8_18; journal version ACM TOPLAS 43(4), 2021, doi:10.1145/3462205. A mutable borrow is represented as the pair of the current target value and the target value at the end of the borrow (full version arXiv:2002.09002, Section 1.2, 'related to prophecy variables'); the borrow rule gives the lender the fresh end-of-borrow variable, and releasing the borrow checks the prophesied value (Section 3.2). The core language COR does not support unsafe code.
* Xavier Denis, Jacques-Henri Jourdan, and C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, LNCS, pp. 90-105, doi:10.1007/978-3-031-17244-1_6. Section 3.2: a mutable borrow is the record { current ; final }; creating it is 'y : borrow t <- { current = x ; final = any t }; x : t <- y.final', which is 'valid because the value of the lender cannot be observed before the lifetime's end'; ending it is 'assume { y.final = y.current }'. In that paper Creusot does not permit verification of unsafe code.
* Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, and Derek Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022, pp. 841-856, doi:10.1145/3519939.3523704. Machine-checked (Coq/Iris) soundness of RustHorn-style first-order specifications for safe APIs implemented with unsafe code (e.g. Vec, Cell, Mutex), via parametric prophecies; no treatment of raw-pointer-to-reference conversion as a translation rule was found in it.
* Ralf Jung, Rodolphe Lepigre, Gaurav Parthasarathy, Marianna Rapoport, Amin Timany, Derek Dreyer, and Bart Jacobs. The Future is Ours: Prophecy Variables in Separation Logic. Proc. ACM Program. Lang. 4(POPL), Article 45, pp. 1-32, 2020. doi:10.1145/3371113. Prophecy variables in a Hoare-style program logic, formalized in Iris in Coq (abstract). Background for prophecy encodings; it does not treat Rust borrows.
* Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers, and Derek Dreyer. RefinedRust: A Type System for High-Assurance Verification of Rust Programs. Proc. ACM Program. Lang. 8(PLDI), Article 192, pp. 1115-1139, 2024. doi:10.1145/3656422. Verification of 'both safe and unsafe Rust code' (abstract), including 'APIs that use raw pointers' (Section 3); mutable references carry 'borrow names, which are inspired by RustHorn's prophecy variables' (Section 1).
* Sacha-Élie Ayoun, Xavier Denis, Petar Maksimović, and Philippa Gardner. A Hybrid Approach to Semi-automated Rust Verification. Proc. ACM Program. Lang. 9(PLDI), Article 186, pp. 970-992, 2025. doi:10.1145/3729289 (extended version arXiv:2403.15122). Presents Gillian-Rust, which 'can reason about type safety and functional correctness of unsafe code' and embeds 'the parametric prophecies of RustHornBelt' (abstract).
* Creusot source repository github.com/creusot-rs/creusot at commit 601d97891bb0bc0b569686cc946ef4980560b5d8: the library defines a ghost permission type `Perm<C>` ('Generic permissions for accessing memory pointed to by pointers or within an interior mutable type', creusot-std/src/ghost/perm.rs) with an instance for raw pointers, `Perm<*const T>` (creusot-std/src/std/ptr.rs). Tool source code, not a publication.

The Aeneas pull requests and issue cited above are unmerged or tracker items, recorded by number and head commit as observed; they are context for the modeling bridges, not subjects, and may change or be closed.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects `sorry`/`admit`/`native_decide`/`axiom` in the sources, checks with Lean's `collectAxioms` that every declaration of the library depends only on `propext`, `Classical.choice`, `Quot.sound`, and recomputes, for every Lean name referenced by `results.json` and every name in `audit/statements.json`, the statement and closure SHA-256 exactly as described under **Evidence** (statement: `repr` of the type; closure: sorted `name : repr type [:= repr value]` lines over every package-local constant reachable from the statement, theorem bodies excluded), comparing them with `audit/statements.json`. It prints `REVALIDATED` and exits 0 iff all checks pass. A hash mismatch means a statement or a definition it depends on changed; the result's card must then be re-reviewed.

Manual equivalent of the build and axiom audit:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is outside the library target; it imports `ToyBackward` and runs `#print axioms` on every card-referenced declaration. Every printed line must list only `propext`, `Classical.choice`, and `Quot.sound` (a subset, possibly none). To check a single result after a change, rerun the commands above; the build fails if any proof no longer checks.
