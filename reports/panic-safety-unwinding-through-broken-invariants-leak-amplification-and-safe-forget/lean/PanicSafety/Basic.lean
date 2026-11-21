/-!
# Toy model: containers, user code, unwinding, and leaking

This file defines a small, deterministic model of unsafe library code that temporarily
breaks a container's safety invariant while calling user code.

* A container owns a buffer of cells and a `len` field. Its drop glue drops the first
  `len` cells. A cell holds the bits of a value (a token `t : Tok`) or is uninitialized.
* Dropping a value runs its destructor once. Dropping an uninitialized cell, or dropping
  a value whose destructor already ran (a double drop), is undefined behaviour (UB).
* User code is supplied per run as behaviour tables: `Callback` gives the outcome of the
  `j`-th callback invocation (return a boolean, or panic), and `DtorTable` says which
  element destructors panic. Quantifying over all tables quantifies over every
  return/panic pattern of user code.
* Library operations are programs (`Prog`) over the container and a frame of live
  locals with drop glue (`Entry.value`) and drop guards (`Entry.guard`).
* Two panic semantics (`Mode`): under `abort` a panic stops the run (observable, not UB);
  under `unwind` the frame's drop glue runs (locals dropped, guards' fix-ups applied) and
  the panic propagates to the caller. A destructor panic during unwinding aborts.

The model is a toy. It is meant to capture the shape of Rust's panic-safety obligations
for unsafe collection code; it does not model Rust's type system, borrow checker,
allocator, or any real standard-library source.
-/

namespace Toy.PanicSafety

/-- Identity of an element value. Two cells holding the same token hold bitwise copies of
the same value; dropping both drops that value twice. -/
abbrev Tok := Nat

/-- A buffer cell: `some t` holds the bits of value `t`; `none` is uninitialized memory. -/
abbrev Cell := Option Tok

/-- The tokens held by a list of cells, skipping uninitialized cells. -/
def toks (cs : List Cell) : List Tok := cs.filterMap id

/-- Library-visible state: the container's buffer and `len` field, the log of values whose
destructor has run (most recent first), and two plain counters with no drop glue (used to
model a purely logical invariant). -/
structure Mem where
  buf : List Cell
  len : Nat
  dropped : List Tok
  ctrA : Nat
  ctrB : Nat
deriving DecidableEq, Repr

/-- The cells the container's drop glue will drop: the first `len` cells of the buffer. -/
def Mem.elems (m : Mem) : List Cell := m.buf.take m.len

/-- `OwnsUniquely d cs`: every cell of `cs` is initialized, the values held are pairwise
distinct, and none of them occurs in the drop log `d`. This is the drop-safety predicate
for a list of owned places: dropping them in order (with non-panicking destructors) is
UB-free exactly when it holds (`dropCells_noPanic_ne_ub_iff`). -/
def OwnsUniquely (d : List Tok) (cs : List Cell) : Prop :=
  (∀ c ∈ cs, c ≠ none) ∧ (toks cs).Nodup ∧ ∀ t ∈ toks cs, t ∉ d

instance (d : List Tok) (cs : List Cell) : Decidable (OwnsUniquely d cs) := by
  unfold OwnsUniquely; infer_instance

/-- The container's memory-safety invariant: `len` is within the buffer and the first
`len` cells are uniquely owned, initialized, not-yet-dropped values. It says nothing about
the counters `ctrA`, `ctrB` or about cells at index `len` and beyond. -/
def Inv (m : Mem) : Prop := m.len ≤ m.buf.length ∧ OwnsUniquely m.dropped m.elems

instance (m : Mem) : Decidable (Inv m) := by unfold Inv; infer_instance

/-- Outcome of one invocation of a user callback. -/
inductive Beh where
  | ret (b : Bool)
  | panic
deriving DecidableEq, Repr

/-- A callback behaviour table: the outcome of the `j`-th callback invocation of a run
(`j` counts from `0`). -/
abbrev Callback := Nat → Beh

/-- An element-destructor table: `dt t = true` means the destructor of value `t` panics
(after the value counts as dropped). -/
abbrev DtorTable := Tok → Bool

/-- The destructor table in which no destructor panics. -/
def noPanicDtors : DtorTable := fun _ => false

/-- No element destructor panics. -/
def NoPanickingDtors (dt : DtorTable) : Prop := ∀ t, dt t = false

/-- A drop guard. Its drop glue is a fix-up of the container's buffer and `len` (memory
moves and a `len` update, as in a back-shift guard or a set-len-on-drop guard). By
construction a fix-up cannot run destructors and cannot read or change the drop log. -/
structure Guard where
  fix : List Cell → Nat → List Cell × Nat

/-- An entry of the library frame that has drop glue. -/
inductive Entry where
  /-- A live local owning value `t` (for instance the result of `ptr::read`). -/
  | value (t : Tok)
  /-- A live drop guard. -/
  | guard (g : Guard)

/-- Library operations. Continuations are Lean functions, so loops are written by
recursion at the meta level. -/
inductive Prog where
  /-- Return to the caller. Returning with live frame entries is malformed (counted as UB);
  scope-exit drop glue is written explicitly with `dropVal` / `popGuard`. -/
  | done
  /-- Read the container's `len` field. -/
  | getLen (k : Nat → Prog)
  /-- Invoke the user callback (a closure, `clone`, comparison, ...). -/
  | call (k : Bool → Prog)
  /-- `ptr::copy` of one cell (bits only; the source keeps its bits). UB if out of bounds. -/
  | copy (src dst : Nat) (k : Prog)
  /-- `ptr::drop_in_place(&mut buf[i])`: run the destructor of the value in cell `i`. -/
  | dropCell (i : Nat) (k : Prog)
  /-- `set_len(n)`. -/
  | setLen (n : Nat) (k : Prog)
  /-- `let x = ptr::read(&buf[i])`: push a live local owning the value of cell `i`. -/
  | readOut (i : Nat) (k : Prog)
  /-- `ptr::write(&mut buf[i], x)`: move the top local into cell `i` (no drop). -/
  | writeBack (i : Nat) (k : Prog)
  /-- `drop(x)` for the top local. -/
  | dropVal (k : Prog)
  /-- `mem::forget(x)` for the top local. -/
  | forgetVal (k : Prog)
  /-- Create a drop guard. -/
  | pushGuard (g : Guard) (k : Prog)
  /-- Update the fields of the top guard (for instance `g.processed += 1`). -/
  | setGuard (g : Guard) (k : Prog)
  /-- End of the top guard's scope: its fix-up runs. -/
  | popGuard (k : Prog)
  /-- `mem::forget` of the top guard. -/
  | forgetGuard (k : Prog)
  /-- Increment counter `ctrA` / `ctrB` (no drop glue). -/
  | bumpA (k : Prog)
  | bumpB (k : Prog)

/-- Panic semantics. -/
inductive Mode where
  | abort
  | unwind
deriving DecidableEq, Repr

/-- Outcome of running an operation: normal return, unwound out of the operation's frame
(the panic propagates to the caller, who still owns the container), abort, or UB. -/
inductive Res where
  | ret (m : Mem)
  | unwound (m : Mem)
  | abort
  | ub
deriving DecidableEq, Repr

/-- Outcome of running drop glue while unwinding. -/
inductive URes where
  | ok (m : Mem)
  | abort
  | ub
deriving DecidableEq, Repr

/-- Unwinding the library frame: entries are processed most-recent first. A local's value
is dropped (UB if already dropped; a panicking destructor aborts, since a panic is already
in flight); a guard's fix-up is applied. -/
def unwindEntries (dt : DtorTable) : List Entry → Mem → URes
  | [], m => .ok m
  | .value t :: es, m =>
      if t ∈ m.dropped then .ub
      else if dt t then .abort
      else unwindEntries dt es { m with dropped := t :: m.dropped }
  | .guard g :: es, m =>
      unwindEntries dt es { m with buf := (g.fix m.buf m.len).1, len := (g.fix m.buf m.len).2 }

/-- What happens when user code panics with frame `es` and state `m`. -/
def panicFrom (mode : Mode) (dt : DtorTable) (es : List Entry) (m : Mem) : Res :=
  match mode with
  | .abort => .abort
  | .unwind =>
    match unwindEntries dt es m with
    | .ok m' => .unwound m'
    | .abort => .abort
    | .ub => .ub

/-- Kinds of user-code invocation sites. -/
inductive SiteKind where
  | callback
  | destructor
deriving DecidableEq, Repr

/-- A user-code invocation site reached by a run: the frame entries and state at the
moment user code runs. For a destructor site the value already counts as dropped. -/
structure Site where
  kind : SiteKind
  entries : List Entry
  mem : Mem

/-- The interpreter. `exec mode cb dt p j es m` runs `p` with `j` callback invocations
so far, frame `es` and state `m`. It returns the outcome and the list of user-code sites
reached before the run ended (in order). -/
def exec (mode : Mode) (cb : Callback) (dt : DtorTable) :
    Prog → Nat → List Entry → Mem → Res × List Site
  | .done, _, es, m => (if es.isEmpty then .ret m else .ub, [])
  | .getLen k, j, es, m => exec mode cb dt (k m.len) j es m
  | .call k, j, es, m =>
      match cb j with
      | .ret b =>
        let r := exec mode cb dt (k b) (j + 1) es m
        (r.1, ⟨.callback, es, m⟩ :: r.2)
      | .panic => (panicFrom mode dt es m, [⟨.callback, es, m⟩])
  | .copy s d k, j, es, m =>
      if s < m.buf.length ∧ d < m.buf.length then
        exec mode cb dt k j es { m with buf := m.buf.set d (m.buf.getD s none) }
      else (.ub, [])
  | .dropCell i k, j, es, m =>
      match m.buf[i]? with
      | some (some t) =>
        if t ∈ m.dropped then (.ub, [])
        else
          let m' := { m with dropped := t :: m.dropped }
          if dt t then (panicFrom mode dt es m', [⟨.destructor, es, m'⟩])
          else
            let r := exec mode cb dt k j es m'
            (r.1, ⟨.destructor, es, m'⟩ :: r.2)
      | _ => (.ub, [])
  | .setLen n k, j, es, m => exec mode cb dt k j es { m with len := n }
  | .readOut i k, j, es, m =>
      match m.buf[i]? with
      | some (some t) => exec mode cb dt k j (.value t :: es) m
      | _ => (.ub, [])
  | .writeBack i k, j, es, m =>
      match es with
      | .value t :: es' =>
        if i < m.buf.length then exec mode cb dt k j es' { m with buf := m.buf.set i (some t) }
        else (.ub, [])
      | _ => (.ub, [])
  | .dropVal k, j, es, m =>
      match es with
      | .value t :: es' =>
        if t ∈ m.dropped then (.ub, [])
        else
          let m' := { m with dropped := t :: m.dropped }
          if dt t then (panicFrom mode dt es' m', [⟨.destructor, es', m'⟩])
          else
            let r := exec mode cb dt k j es' m'
            (r.1, ⟨.destructor, es', m'⟩ :: r.2)
      | _ => (.ub, [])
  | .forgetVal k, j, es, m =>
      match es with
      | .value _ :: es' => exec mode cb dt k j es' m
      | _ => (.ub, [])
  | .pushGuard g k, j, es, m => exec mode cb dt k j (.guard g :: es) m
  | .setGuard g k, j, es, m =>
      match es with
      | .guard _ :: es' => exec mode cb dt k j (.guard g :: es') m
      | _ => (.ub, [])
  | .popGuard k, j, es, m =>
      match es with
      | .guard g :: es' =>
        exec mode cb dt k j es' { m with buf := (g.fix m.buf m.len).1, len := (g.fix m.buf m.len).2 }
      | _ => (.ub, [])
  | .forgetGuard k, j, es, m =>
      match es with
      | .guard _ :: es' => exec mode cb dt k j es' m
      | _ => (.ub, [])
  | .bumpA k, j, es, m => exec mode cb dt k j es { m with ctrA := m.ctrA + 1 }
  | .bumpB k, j, es, m => exec mode cb dt k j es { m with ctrB := m.ctrB + 1 }

/-- Running operation `p` on state `m`, entered with an empty frame. -/
def run (mode : Mode) (cb : Callback) (dt : DtorTable) (p : Prog) (m : Mem) : Res :=
  (exec mode cb dt p 0 [] m).1

/-- The user-code sites reached by running `p` on `m`, entered with an empty frame. They
do not depend on the panic mode (`exec_sites_mode_indep`). -/
def sites (cb : Callback) (dt : DtorTable) (p : Prog) (m : Mem) : List Site :=
  (exec .unwind cb dt p 0 [] m).2

/-- An outcome is acceptable for panic safety: no UB; a normal return or an unwind leaves
the container satisfying `Inv`; abort is acceptable. -/
def ResOk : Res → Prop
  | .ret m => Inv m
  | .unwound m => Inv m
  | .abort => True
  | .ub => False

instance (r : Res) : Decidable (ResOk r) := by
  cases r <;> unfold ResOk <;> infer_instance

/-- Panic safety of an operation under a panic mode: for every callback table, every
destructor table, and every entry state satisfying `Inv`, the run is acceptable. -/
def PanicSafe (mode : Mode) (p : Prog) : Prop :=
  ∀ (cb : Callback) (dt : DtorTable) (m : Mem), Inv m → ResOk (run mode cb dt p m)

/-- Panic safety restricted to destructor tables in which no destructor panics. -/
def PanicSafeAssumingNoDtorPanic (mode : Mode) (p : Prog) : Prop :=
  ∀ (cb : Callback) (dt : DtorTable) (m : Mem), NoPanickingDtors dt → Inv m →
    ResOk (run mode cb dt p m)

/-! ## The owner's drop glue -/

/-- Outcome of dropping a list of cells while a panic is in flight. -/
inductive DRes where
  | ok (d : List Tok)
  | abort
  | ub
deriving DecidableEq, Repr

/-- Drop cells in order, while a panic is in flight: an uninitialized cell or an already
dropped value is UB; a panicking destructor aborts. Returns the final drop log. -/
def dropCells (dt : DtorTable) : List Cell → List Tok → DRes
  | [], d => .ok d
  | none :: _, _ => .ub
  | some t :: cs, d =>
      if t ∈ d then .ub
      else if dt t then .abort
      else dropCells dt cs (t :: d)

/-- The container's drop glue, run by its owner while the panic propagates: drop the
first `len` cells in order. A `len` beyond the buffer is UB. -/
def containerDrop (dt : DtorTable) (m : Mem) : DRes :=
  if m.len ≤ m.buf.length then dropCells dt m.elems m.dropped else .ub

/-- Final outcome when the operation is called by an owner whose frame holds the container
and nothing else with drop glue: on an unwind, the owner's frame is unwound too, dropping
the container (`panicked d` carries the final drop log). -/
inductive Final where
  | returned (m : Mem)
  | panicked (d : List Tok)
  | aborted
  | ub
deriving DecidableEq, Repr

/-- The operation followed, on an unwind, by the owner's drop of the container. -/
def harness (mode : Mode) (cb : Callback) (dt : DtorTable) (p : Prog) (m : Mem) : Final :=
  match run mode cb dt p m with
  | .ret m' => .returned m'
  | .unwound m' =>
    match containerDrop dt m' with
    | .ok d => .panicked d
    | .abort => .aborted
    | .ub => .ub
  | .abort => .aborted
  | .ub => .ub

/-! ## Unwinding footprint: the drop-safety predicate at a site -/

/-- Apply the fix-ups of all guards in a frame, most-recent first, to `(buf, len)`. -/
def applyGuards : List Entry → List Cell × Nat → List Cell × Nat
  | [], bl => bl
  | .value _ :: es, bl => applyGuards es bl
  | .guard g :: es, bl => applyGuards es (g.fix bl.1 bl.2)

/-- The values owned by the live locals of a frame, most-recent first. -/
def valueToks : List Entry → List Tok
  | [] => []
  | .value t :: es => t :: valueToks es
  | .guard _ :: es => valueToks es

/-- `DropSafe es m`: the places that unwinding from frame `es` and state `m` will touch
are uniquely owned. These places are the values of the live locals, together with the
container's first `len` cells *after* all guard fix-ups have been applied; the container is
then left to its owner. The predicate also requires the fixed-up `len` to be within the
buffer. -/
def DropSafe (es : List Entry) (m : Mem) : Prop :=
  (applyGuards es (m.buf, m.len)).2 ≤ (applyGuards es (m.buf, m.len)).1.length ∧
  OwnsUniquely m.dropped
    ((valueToks es).map some ++
      (applyGuards es (m.buf, m.len)).1.take (applyGuards es (m.buf, m.len)).2)

instance (es : List Entry) (m : Mem) : Decidable (DropSafe es m) := by
  unfold DropSafe; infer_instance

end Toy.PanicSafety
