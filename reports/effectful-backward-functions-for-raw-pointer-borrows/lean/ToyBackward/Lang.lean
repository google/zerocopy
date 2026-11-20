/-!
# Toy source language: integer cells, raw pointers, `as_mut` reborrows

A deliberately tiny straight-line language that isolates one feature of unsafe Rust:
reborrowing a raw pointer `p : *mut i32` as a mutable reference (`&mut *p`, `p.as_mut()`),
using the reference, and accessing the same cell through the raw pointer again.

* Memory is a total map from addresses to integers (`Heap`). Raw pointers are bare addresses
  (`Ptr`); there is no allocation, deallocation, or pointer arithmetic.
* A reference is named by the program position of the `asMut` statement that created it,
  so every reference is bound exactly once and no renaming conventions are needed.
* The *heap semantics* `heapSem` is the ground truth: a reference is just the address it was
  created from, and every read or write through it goes straight to the heap. It has no notion
  of a region (lifetime) ending; it is the "machine" against which translations are judged.

Nothing here models Rust's aliasing rules; those enter only as hypotheses
(`AliasingDiscipline`, placement conditions) in `ToyBackward.Liveness`.

By inspection of `hstep`, a run of the heap semantics is stuck (`heapSem P h = none`) only when
it reads or writes through a reference name that no earlier `asMut` statement created (a scoping
error). The aliasing discipline does not exclude such programs; the main results cover them by
stating that both sides are stuck.
-/

namespace Toy.Backward

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

/-! ## Heap semantics (ground truth) -/

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

end Toy.Backward
