/-!
# Address-observed slot coalescing: the toy language and its semantics

A straight-line toy language over a frame of locals with per-local cell memory, field windows,
aggregates, pointers with per-local provenance, pointer comparisons that observe absolute
addresses, storage markers, a table of callees, and a destructor block run on return.

This is a toy model. It is meant to capture the shape of storage-merging optimizations (copy to
move upgrades, merging a local into a field of another local, staging of overlapping assignments)
once addresses can be observed. It does not model any real intermediate representation.

Modeling choices (each one is a choice, not a finding):
* A program is a straight-line `body` followed by a straight-line destructor block `dtors` (the
  return tail). There are no branches or loops.
* Memory is indexed by `(local, offset)`. A pointer value `Val.ptr l o` carries the local `l`
  (its provenance) and an offset; loads and stores through it access local `l` and are undefined
  behaviour unless `l` is allocated and the access is in bounds.
* A *layout* `A : Nat → Nat` gives each local one base address for the whole run (a static frame
  layout). Absolute addresses `A l + o` are observable through pointer comparisons and printed
  pointer values and through nothing else. Each allocation records the pairs (new local, currently allocated local)
  whose address ranges must be disjoint; a run whose layout violates a recorded pair is *excluded*
  (outcome `badLayout`). So distinct simultaneously allocated locals have disjoint address ranges,
  and every program has non-excluded layouts. Checking the recorded pairs once at the end is
  equivalent to checking each allocation when it happens, because execution stops at undefined
  behaviour and records no later allocations.
* Reading an uninitialized cell through `copy`, `move` or `load` is undefined behaviour.
* Every cell read and write is recorded in an access log; the resets performed by allocation and
  deallocation are recorded with their own kind (`AccKind.reset`).
-/

namespace Toy.Coalesce

/-- Cell values: uninitialized, an integer, or a pointer `ptr l o` to offset `o` of local `l`. -/
inductive Val where
  | uninit
  | int (n : Nat)
  | ptr (loc off : Nat)
  deriving DecidableEq, Repr

/-- A place: a local `base` and the flattened window `[off, off + len)` of a field projection path
inside it. A nested projection composes by adding offsets (see `Place.proj`). -/
structure Place where
  base : Nat
  off : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- The field of `q` at relative offset `o` with width `l`. -/
def Place.proj (q : Place) (o l : Nat) : Place := ⟨q.base, q.off + o, l⟩

/-- The whole of local `x`, given its size. -/
def Place.whole (x size : Nat) : Place := ⟨x, 0, size⟩

/-- Operands.
* `copy q`: reads the cells of `q`.
* `move q`: reads the cells of `q`; what else it does depends on the `MoveSem` parameter.
* `lit n`: a one-cell integer constant.
* `addrOf q`: a one-cell pointer to the first cell of `q`; taking it makes `q.base`
  *address-taken* (`AddrTaken`).
* `load p len`: reads a pointer from the one-cell place `p`, then reads `len` cells through it. -/
inductive Operand where
  | copy (q : Place)
  | move (q : Place)
  | lit (n : Nat)
  | addrOf (q : Place)
  | load (p : Place) (len : Nat)
  deriving DecidableEq, Repr

/-- The number of cells an operand denotes (a static quantity). -/
def Operand.len : Operand → Nat
  | .copy q => q.len
  | .move q => q.len
  | .lit _ => 1
  | .addrOf _ => 1
  | .load _ l => l

/-- Statements.
* `storageLive x` / `storageDead x`: allocate (fresh uninitialized cells) / deallocate local `x`.
* `assign lhs rhs`: `rhs` is an aggregate of operands; operand `i` initializes the field of `lhs`
  that follows the fields of operands `0 … i-1`. A one-operand `rhs` is a plain place read or use.
* `store p v`: writes the value of `v` through the pointer held in the one-cell place `p`.
* `ptrEq a b`, `ptrInRange a b n`: observable pointer comparisons on absolute addresses
  (`ptrInRange a b n` tests `b ≤ a < b + n`).
* `out o`: emits the value of `o` as an observable event (pointers are printed as addresses).
* `call fn arg`: runs callee `fn` from the program's callee table with the callee's parameter
  local bound to the argument; how the argument is passed depends on `MoveSem`.
* `nop`. -/
inductive Stmt where
  | storageLive (x : Nat)
  | storageDead (x : Nat)
  | assign (lhs : Place) (rhs : List Operand)
  | store (p : Place) (v : Operand)
  | ptrEq (a b : Operand)
  | ptrInRange (a b : Operand) (n : Nat)
  | out (o : Operand)
  | call (fn : Nat) (arg : Operand)
  | nop
  deriving DecidableEq, Repr

/-- A callee: its parameter local `prm` and its straight-line body. Callee bodies run in the
caller's frame (they may name any local, and they reach memory through pointers); storage
statements and nested calls inside a callee are undefined behaviour in this toy. -/
structure Callee where
  prm : Nat
  body : List Stmt
  deriving DecidableEq, Repr

/-- A program: local sizes (local `x` exists iff `x < sizes.length`), a straight-line body, a
straight-line destructor block run after the body (the return tail), and a callee table. -/
structure Prog where
  sizes : List Nat
  body : List Stmt
  dtors : List Stmt
  fns : List Callee
  deriving DecidableEq, Repr

/-- The size (number of cells) of local `x`; `0` for a non-existent local. -/
def Prog.size (P : Prog) (x : Nat) : Nat := P.sizes.getD x 0

/-- The number of locals. -/
def Prog.nloc (P : Prog) : Nat := P.sizes.length

/-- The top-level statement sequence: body, then destructors. Top-level statement `t` runs at
tick `t`. -/
def Prog.code (P : Prog) : List Stmt := P.body ++ P.dtors

/-- Callee `fn` (a callee with parameter `0` and an empty body if absent). -/
def Prog.fn (P : Prog) (fn : Nat) : Callee := P.fns.getD fn ⟨0, []⟩

/-! ## Semantics parameters -/

/-- The three candidate semantics of `move` (none is chosen).
* `asCopy`: `move` is `copy`.
* `deinit`: after the read, the source cells become uninitialized.
* `inPlaceCall`: outside call arguments `move` is `copy`; a call argument `move q` is passed in
  place: during the call the callee's parameter *is* the place `q` (its reads and writes go to
  `q`'s cells, and `q` keeps the callee's final parameter contents after the call). -/
inductive MoveSem where
  | asCopy
  | deinit
  | inPlaceCall
  deriving DecidableEq, Repr

/-- Evaluation order of an aggregate assignment.
* `atomic`: evaluate every operand, then write every field (a reference semantics in which an
  overlap between the left side and the places read on the right side is harmless).
* `inOrder`: evaluate operand `0`, write field `0`, evaluate operand `1`, write field `1`, …
  (in-order field writes). -/
inductive AssignMode where
  | atomic
  | inOrder
  deriving DecidableEq, Repr

/-- A semantics: a `move` semantics and an assignment evaluation order. -/
structure Sem where
  move : MoveSem
  assign : AssignMode
  deriving DecidableEq, Repr

/-- A layout: one base address per local (a static frame layout). -/
abbrev Layout := Nat → Nat

/-- Two address ranges `[a, a+m)` and `[b, b+n)` are disjoint (empty ranges are disjoint from
everything). -/
def Disj (a m b n : Nat) : Prop := m = 0 ∨ n = 0 ∨ a + m ≤ b ∨ b + n ≤ a

instance (a m b n : Nat) : Decidable (Disj a m b n) := by unfold Disj; infer_instance

/-! ## Observations, outcomes, access log -/

/-- Observable values: integers and absolute addresses. -/
inductive EVal where
  | int (n : Nat)
  | addr (a : Nat)
  deriving DecidableEq, Repr

/-- Observable events: emitted values (`out`) and pointer-comparison results. -/
inductive Event where
  | vals (vs : List EVal)
  | cmp (b : Bool)
  deriving DecidableEq, Repr

/-- The outcome of a run: normal completion with its event trace, undefined behaviour, or an
excluded run (the layout made two simultaneously allocated locals overlap). -/
inductive Outcome where
  | done (t : List Event)
  | ub
  | badLayout
  deriving DecidableEq, Repr

/-- Kinds of logged cell accesses: a read, a data write (assignment, store, call-parameter
initialization, or the uninitialized bytes written by a `deinit` move), or a reset performed by
allocation or deallocation. -/
inductive AccKind where
  | read
  | write
  | reset
  deriving DecidableEq, Repr

/-- One logged cell access: the top-level tick, whether it happened inside a callee, the cell
`(loc, off)`, and its kind. -/
structure Access where
  tick : Nat
  inCall : Bool
  loc : Nat
  off : Nat
  kind : AccKind
  deriving DecidableEq, Repr

/-- Run status. -/
inductive Status where
  | running
  | ub
  deriving DecidableEq, Repr

/-- Machine state. `alias = some (prm, q)` while an in-place call binds parameter `prm` to `q`. -/
structure St where
  mem : Nat → Nat → Val
  live : Nat → Bool
  alias : Option (Nat × Place)
  trace : List Event
  log : List Access
  tick : Nat
  inCall : Bool
  status : Status
  /-- Pairs of locals that were simultaneously allocated (recorded at allocation time). -/
  conflicts : List (Nat × Nat)

/-- The initial state: nothing allocated, all cells uninitialized. -/
def St.init : St :=
  ⟨fun _ _ => .uninit, fun _ => false, none, [], [], 0, false, .running, []⟩

def St.fail (s : St) (k : Status) : St := { s with status := k }

def St.logAcc (s : St) (loc off : Nat) (k : AccKind) : St :=
  { s with log := s.log ++ [⟨s.tick, s.inCall, loc, off, k⟩] }

def St.emit (s : St) (e : Event) : St := { s with trace := s.trace ++ [e] }

/-- Write one cell, logging an access of kind `k`. -/
def St.wr (s : St) (k : AccKind) (loc off : Nat) (v : Val) : St :=
  let s := s.logAcc loc off k
  { s with mem := fun l o => if l = loc ∧ o = off then v else s.mem l o }

/-- Write consecutive cells starting at `(loc, off)`, logging accesses of kind `k`. -/
def writeCellsK (k : AccKind) (s : St) (loc off : Nat) : List Val → St
  | [] => s
  | v :: vs => writeCellsK k (s.wr k loc off v) loc (off + 1) vs

/-- Data write of consecutive cells (logged as `write`). -/
def writeCells (s : St) (loc off : Nat) (vs : List Val) : St := writeCellsK .write s loc off vs

/-- Reset of consecutive cells to uninitialized by allocation or deallocation (logged as
`reset`). -/
def resetCells (s : St) (loc n : Nat) : St := writeCellsK .reset s loc 0 (List.replicate n .uninit)

/-- Read `n` consecutive cells starting at `(loc, off)` (logged); undefined behaviour on an
uninitialized cell. -/
def readCells (s : St) (loc off : Nat) : Nat → St × Option (List Val)
  | 0 => (s, some [])
  | n + 1 =>
    let v := s.mem loc off
    let s := s.logAcc loc off .read
    if v = .uninit then (s.fail .ub, none) else
    match readCells s loc (off + 1) n with
    | (s', some vs) => (s', some (v :: vs))
    | (s', none) => (s', none)

/-- Resolve a place: apply the in-place parameter alias, then require the target local to be
allocated and the window to be in bounds. -/
def resolvePlace (P : Prog) (s : St) (q : Place) : Option Place :=
  let q' : Option Place :=
    match s.alias with
    | some (prm, t) =>
      if q.base = prm then
        (if q.off + q.len ≤ t.len then some ⟨t.base, t.off + q.off, q.len⟩ else none)
      else some q
    | none => some q
  match q' with
  | some r => if s.live r.base = true ∧ r.off + r.len ≤ P.size r.base then some r else none
  | none => none

/-- Absolute address of a pointer value. -/
def Val.addr? (A : Layout) : Val → Option Nat
  | .ptr l o => some (A l + o)
  | _ => none

/-- Observable form of a (non-uninitialized) value. -/
def Val.obs (A : Layout) : Val → EVal
  | .int n => .int n
  | .ptr l o => .addr (A l + o)
  | .uninit => .int 0

/-- Evaluate an operand. Returns the (possibly failed) state and the value. -/
def evalOp (ms : MoveSem) (P : Prog) (s : St) : Operand → St × Option (List Val)
  | .lit n => (s, some [.int n])
  | .addrOf q =>
    match resolvePlace P s q with
    | some r => (s, some [.ptr r.base r.off])
    | none => (s.fail .ub, none)
  | .copy q =>
    match resolvePlace P s q with
    | some r => readCells s r.base r.off r.len
    | none => (s.fail .ub, none)
  | .move q =>
    match resolvePlace P s q with
    | some r =>
      match readCells s r.base r.off r.len with
      | (s', some vs) =>
        if ms = .deinit then (writeCells s' r.base r.off (List.replicate r.len .uninit), some vs)
        else (s', some vs)
      | (s', none) => (s', none)
    | none => (s.fail .ub, none)
  | .load p len =>
    match resolvePlace P s p with
    | some r =>
      if r.len = 1 then
        match readCells s r.base r.off 1 with
        | (s', some [.ptr l o]) =>
          if s'.live l = true ∧ o + len ≤ P.size l then readCells s' l o len
          else (s'.fail .ub, none)
        | (s', some _) => (s'.fail .ub, none)
        | (s', none) => (s', none)
      else (s.fail .ub, none)
    | none => (s.fail .ub, none)

/-- Evaluate a list of operands left to right (atomic aggregate evaluation). -/
def evalOps (ms : MoveSem) (P : Prog) (s : St) : List Operand → St × Option (List Val)
  | [] => (s, some [])
  | o :: os =>
    match evalOp ms P s o with
    | (s', some vs) =>
      match evalOps ms P s' os with
      | (s'', some ws) => (s'', some (vs ++ ws))
      | (s'', none) => (s'', none)
    | (s', none) => (s', none)

/-- In-order field writes: evaluate operand `i` and immediately write it at the next offset. -/
def writeInOrder (ms : MoveSem) (P : Prog) (s : St) (loc off : Nat) : List Operand → St
  | [] => s
  | o :: os =>
    match evalOp ms P s o with
    | (s', some vs) => writeInOrder ms P (writeCells s' loc off vs) loc (off + vs.length) os
    | (s', none) => s'

/-- The locals other than `x` that are allocated in `s`. -/
def liveOthers (P : Prog) (s : St) (x : Nat) : List Nat :=
  (List.range P.nloc).filter fun z => z != x && s.live z

/-- Allocate local `x`: undefined behaviour if `x` does not exist; otherwise record that `x` must
be disjoint from every other allocated local, mark it allocated, and reset its cells (logged). -/
def allocate (P : Prog) (s : St) (x : Nat) : St :=
  if x < P.nloc then
    let s := { s with conflicts := s.conflicts ++ (liveOthers P s x).map fun z => (x, z) }
    resetCells { s with live := fun z => if z = x then true else s.live z } x (P.size x)
  else s.fail .ub

/-- Deallocate local `x` (a no-op if it is not allocated); its cells are reset (logged). -/
def deallocate (P : Prog) (s : St) (x : Nat) : St :=
  if s.live x = true then
    let s := resetCells s x (P.size x)
    { s with live := fun z => if z = x then false else s.live z }
  else s

/-- Execute a pointer comparison. -/
def cmpOp (ms : MoveSem) (P : Prog) (A : Layout) (s : St) (a b : Operand)
    (f : Nat → Nat → Bool) : St :=
  match evalOp ms P s a with
  | (s1, some [va]) =>
    match evalOp ms P s1 b with
    | (s2, some [vb]) =>
      match va.addr? A, vb.addr? A with
      | some x, some y => s2.emit (.cmp (f x y))
      | _, _ => s2.fail .ub
    | (s2, some _) => s2.fail .ub
    | (s2, none) => s2
  | (s1, some _) => s1.fail .ub
  | (s1, none) => s1

/-- Execute one statement other than `call` (a `call` here is undefined behaviour: nested calls
are not supported). Storage statements inside a callee are undefined behaviour. Failed states are
left unchanged. -/
def execBasic (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt) : St :=
  if s.status ≠ .running then s else
  match st with
  | .storageLive x => if s.inCall then s.fail .ub else allocate P s x
  | .storageDead x => if s.inCall then s.fail .ub else deallocate P s x
  | .assign lhs rhs =>
    if (rhs.map Operand.len).sum ≠ lhs.len then s.fail .ub else
    match resolvePlace P s lhs with
    | none => s.fail .ub
    | some r =>
      match sem.assign with
      | .atomic =>
        match evalOps sem.move P s rhs with
        | (s', some vs) => writeCells s' r.base r.off vs
        | (s', none) => s'
      | .inOrder => writeInOrder sem.move P s r.base r.off rhs
  | .store p v =>
    match resolvePlace P s p with
    | some r =>
      if r.len = 1 then
        match readCells s r.base r.off 1 with
        | (s1, some [.ptr l o]) =>
          match evalOp sem.move P s1 v with
          | (s2, some vs) =>
            if s2.live l = true ∧ o + vs.length ≤ P.size l then writeCells s2 l o vs
            else s2.fail .ub
          | (s2, none) => s2
        | (s1, some _) => s1.fail .ub
        | (s1, none) => s1
      else s.fail .ub
    | none => s.fail .ub
  | .ptrEq a b => cmpOp sem.move P A s a b (fun x y => decide (x = y))
  | .ptrInRange a b n => cmpOp sem.move P A s a b (fun x y => decide (y ≤ x ∧ x < y + n))
  | .out o =>
    match evalOp sem.move P s o with
    | (s', some vs) => s'.emit (.vals (vs.map (Val.obs A)))
    | (s', none) => s'
  | .call _ _ => s.fail .ub
  | .nop => s

/-- Run a callee body (no nested calls). -/
def execCallee (sem : Sem) (P : Prog) (A : Layout) (s : St) (b : List Stmt) : St :=
  b.foldl (execBasic sem P A) s

/-- Execute one top-level statement (including `call`). -/
def execStmt (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt) : St :=
  if s.status ≠ .running then s else
  match st with
  | .call fn arg =>
    let c := P.fn fn
    match sem.move, arg with
    | .inPlaceCall, .move q =>
      match resolvePlace P s q with
      | none => s.fail .ub
      | some r =>
        if r.len ≠ P.size c.prm then s.fail .ub else
        let s1 := execCallee sem P A { s with alias := some (c.prm, r), inCall := true } c.body
        { s1 with alias := none, inCall := false }
    | _, _ =>
      match evalOp sem.move P s arg with
      | (s1, some vs) =>
        if vs.length ≠ P.size c.prm ∨ s1.live c.prm = true then s1.fail .ub else
        let s2 := allocate P s1 c.prm
        let s3 := writeCells s2 c.prm 0 vs
        let s4 := execCallee sem P A { s3 with inCall := true } c.body
        deallocate P { s4 with inCall := false } c.prm
      | (s1, none) => s1
  | st => execBasic sem P A s st

/-- Execute a top-level statement and advance the tick. -/
def execTop (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt) : St :=
  let s' := execStmt sem P A s st
  { s' with tick := s'.tick + 1 }

/-- The final state of the run of `P` under semantics `sem` and layout `A`. -/
def run (sem : Sem) (P : Prog) (A : Layout) : St :=
  P.code.foldl (execTop sem P A) St.init

/-- The layout respects every recorded pair of simultaneously allocated locals. -/
def layoutOK (P : Prog) (A : Layout) (cs : List (Nat × Nat)) : Bool :=
  cs.all fun c => decide (Disj (A c.1) (P.size c.1) (A c.2) (P.size c.2))

/-- The outcome of the run. -/
def outcome (sem : Sem) (P : Prog) (A : Layout) : Outcome :=
  let s := run sem P A
  if layoutOK P A s.conflicts then
    match s.status with
    | .running => .done s.trace
    | .ub => .ub
  else .badLayout

/-- The behaviours of `P`: outcomes of non-excluded runs. -/
def Beh (sem : Sem) (P : Prog) (o : Outcome) : Prop :=
  ∃ A : Layout, outcome sem P A = o ∧ o ≠ .badLayout

/-- Behavioural refinement: every behaviour of `T` (under `semT`) is a behaviour of `S` (under
`semS`), unless `S` has undefined behaviour on some non-excluded run. -/
def Refines (semT : Sem) (T : Prog) (semS : Sem) (S : Prog) : Prop :=
  ∀ o, Beh semT T o → Beh semS S .ub ∨ Beh semS S o

/-- Behavioural equivalence: equal behaviour sets. -/
def BehEq (semT : Sem) (T : Prog) (semS : Sem) (S : Prog) : Prop :=
  ∀ o, Beh semT T o ↔ Beh semS S o

/-! ## Address observation -/

/-- Local `u` is mentioned as the base of an `addrOf` operand. -/
def Operand.takesAddr (u : Nat) : Operand → Bool
  | .addrOf q => q.base == u
  | _ => false

/-- Statement `st` takes the address of a place based at `u`. -/
def Stmt.takesAddr (u : Nat) : Stmt → Bool
  | .assign _ rhs => rhs.any (Operand.takesAddr u)
  | .store _ v => v.takesAddr u
  | .ptrEq a b => a.takesAddr u || b.takesAddr u
  | .ptrInRange a b _ => a.takesAddr u || b.takesAddr u
  | .out o => o.takesAddr u
  | .call _ a => a.takesAddr u
  | _ => false

/-- Statement `st` is a call passing a place based at `u` by `move` to a callee that takes the
address of its own parameter (under in-place passing that address is an address inside `u`). -/
def Stmt.escapesInPlace (P : Prog) (u : Nat) : Stmt → Bool
  | .call fn (.move q) => q.base == u && (P.fns.getD fn ⟨0, []⟩).body.any
      (Stmt.takesAddr (P.fns.getD fn ⟨0, []⟩).prm)
  | _ => false

/-- Local `u` is *address-taken* in `P`: some statement of the body, the destructors or a callee
takes the address of a place based at `u`, or a place based at `u` is passed by `move` to a callee
that takes the address of its own parameter. This is a syntactic over-approximation of address
observation: it holds even when the address is never compared or printed, and even in a callee
that is never called. -/
def AddrTaken (P : Prog) (u : Nat) : Prop :=
  (P.code.any (Stmt.takesAddr u) || P.fns.any (fun c => c.body.any (Stmt.takesAddr u)) ||
    P.code.any (Stmt.escapesInPlace P u)) = true

instance (P : Prog) (u : Nat) : Decidable (AddrTaken P u) := by unfold AddrTaken; infer_instance

end Toy.Coalesce
