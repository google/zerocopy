# Pinning in a toy heap: structural projection, address stability, and the drop guarantee

## Summary

This package defines a small executable model of the memory-level content of Rust's `Pin`
contract (a heap of objects with field locations, self-pointers, and one external intrusive
list) and of structural pin projection for one toy struct type, and proves eleven results about
it in Lean 4 (namespace `Toy.Pin`, core Lean without Mathlib). These are statements about the toy model
(model–system relation: none proved); they neither establish nor refute the corresponding claims about Rust's `Pin` API, the Rust
standard library, the Rust compiler, or the `pin-project` crate. Every connection to those
systems is a separate claim labelled `derived (modeling bridge)`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The eleven results (R1–R11 under Findings), each with its key hypotheses. "Safe program" below
always means a list of `Op` accepted by `SafeProgram d` from the empty heap `State.init` and
run through `compile d`; `AddrInv` is `SelfRefOK ∧ ListOK` (every set self-pointer points at its
own field location; every list entry finds, at its address, the value that registered).

* **R1.** For every list of primitive actions run from `State.init`: if no action moves a value
  out of a pinned field location holding a non-`Unpin` value (`Always NoPinnedMove`) and no
  action deallocates or overwrites the memory of such a value before its destructor has run
  (`Always DropGuaranteeAct`), then every visited state satisfies `AddrInv`.
* **R2.** For every toy struct declaration `d` satisfying (a) `d` is declared `Unpin` only if
  every structurally projected field has an `Unpin` type, (b) its destructor does not move out
  of a structurally projected field of non-`Unpin` type, (c) neither its API nor its destructor
  overwrites such a field without dropping its value, (d) it offers no `Pin<&mut S> -> F`
  move-out of such a field, (e) it is not packed when it has such a field, and (f) such a field
  is not also offered through a non-structural projection: every safe program for `d` keeps
  `AddrInv` in every visited state.
* **R3.** For each of (a)–(f) there is a one-field toy declaration that satisfies the other
  five conditions and violates that one, together with a safe program of at most six
  operations along which `AddrInv` fails (`SelfRefOK` fails for (a), (b), (d), (e), (f);
  `ListOK` fails for (c), both via the API and via the destructor).
* **R4.** The one-field toy declaration `dF`, which offers both a structural and a
  non-structural projection of its non-`Unpin` field, satisfies (a)–(e), and the safe
  6-operation program `progF` for it breaks `SelfRefOK`; so not every safe program for `dF`
  keeps `AddrInv`.
* **R5.** For every toy struct declaration `d` declared `Unpin` (`d.unpin = true`), with no
  other hypothesis: every safe program for `d` keeps `AddrInv` in every visited state if and
  only if every structurally projected field of `d` has an `Unpin` type.
* **R6.** For every toy declaration `d` declared `Unpin` and every field index `i` that `d`
  projects structurally and whose type is not `Unpin`, with no other condition on `d`: the
  5-operation program `unpinWitness i` is a safe program for `d` and `SelfRefOK` fails in some
  visited state.
* **R7.** Call a rule `r : Decl → Bool` sound when, for every declaration satisfying (b)–(f),
  setting `unpin := r d` makes every safe program keep `AddrInv`. Then `r` is sound if and only
  if, on every declaration satisfying (b)–(f), `r` grants `Unpin` only when every structurally
  projected field has an `Unpin` type; `pinnedFieldsRule` is sound; and on declarations
  satisfying (b)–(f) every sound rule grants `Unpin` only where `pinnedFieldsRule` does.
* **R8.** For every toy declaration `d` satisfying (b)–(f), setting `d.unpin := autoUnpin d`
  (`Unpin` iff every field's type is `Unpin`) makes every safe program keep `AddrInv`; and for
  the two-field declaration `dConservative`, whose only non-`Unpin` field is offered only
  through a non-structural projection, `autoUnpin` refuses `Unpin` although `dConservative`,
  declared `Unpin`, keeps `AddrInv` for every safe program.
* **R9.** For every state and every address `b`, `Act.forget b` changes no leaf, pinned location, pinned flag, liveness or list entry,
  and a state satisfying `AddrInv` still satisfies it after `forget b`. For every declaration
  `d`, every state in which the object at `b` is leaked, and every program accepted by
  `SafeProgram d` from that state, the program contains no `Op.drop b` and the object keeps its
  liveness and stays leaked. For every declaration, every state with an object at `b`, and
  every program none of whose operations mentions `b` (no safety assumption), the object at `b`
  and every list entry into it are unchanged in every visited state.
* **R10.** On the 6-action trace `coreReuseActs` from `State.init` (pin a non-`Unpin` value,
  set its self-pointer, link it into the list, then overwrite its memory without running its
  destructor): no action moves a pinned non-`Unpin` value, the final write violates
  `DropGuaranteeAct`, `ListOK` fails in the final state, and `SelfRefOK` holds in every visited
  state.
* **R11.** For every toy declaration `d` and every safe program for `d`, in every visited state
  every self-pointer target and every list entry is a field location `(b, i)` with
  `ApiOp.projPin i ∈ d.api`; if `d` offers no structural projection, every visited state has an
  empty list and no self-pointer.

All 118 theorems referenced by `results.json` are fully proved and kernel-checked (no
`sorry`), using at most the axioms `propext`, `Classical.choice`, `Quot.sound`. What the results do not show is listed
under **Boundaries**, non-claims first; read them before applying any result.

## Applicability

**Model fidelity.** `Toy.Pin` is a toy model (model–system relation: none proved). Nothing in it
is extracted from, or mechanically tied to, the Rust compiler or standard library, so its theorems
neither establish nor refute the corresponding claims about Rust. Its definitions are meant to capture the
following parts of the documented `Pin` contract (each correspondence is a modeling bridge,
evidence role `derived`):

* the two parts of the pinning invariant in the `core::pin` documentation — a pinned value is
  not moved out of its location, and its memory is not invalidated or repurposed before its
  destructor runs (the drop guarantee) — as the action-level predicates `NoPinnedMove` and
  `DropGuaranteeAct`;
* what pinning protects, as two address-sensitive invariants: a value that stored its own
  address (`SelfRefOK`) and an external intrusive list whose entries hold the addresses of
  values (`ListOK`), such as a waiter queue;
* the author's choice, per field, between a structural projection
  `fn(Pin<&mut S>) -> Pin<&mut F>` (`ApiOp.projPin`) and a non-structural one
  `fn(Pin<&mut S>) -> &mut F` (`ApiOp.projMut`), an `Option::take`-like move-out
  (`ApiOp.take`), a `ptr::write`-like overwrite without drop (`ApiOp.overwrite`), a destructor
  given as a list of moves and overwrites (`DtorOp`), `#[repr(packed)]` (`Decl.packed`), and a
  struct-level `Unpin` boolean (`Decl.unpin`);
* what safe client code can do with these (`Op`, `SafeOp`): `&mut` access to a field or to the
  whole struct under the conditions in which Rust's rules provide it (the object is unpinned,
  `S` is declared `Unpin`, the field has a non-structural projection, or the field is a pinned
  field of `Unpin` type), `mem::replace`, `mem::swap`,
  assignment, dropping, and leaking.

Known gaps (each is also a non-claim under **Boundaries**):

* one struct type and one level of fields; a field is either empty or holds one value; no
  nested structural pinning, enums, shared pinning (`Pin<&T>`), interior mutability, panics or
  unwinding, or concurrency;
* `Unpin` is a single boolean per declaration and per field type; generic parameters, negative
  impls and `UnsafeUnpin`-style manual impls are not modelled;
* field alignment is not modelled (a packed declaration whose structurally projected fields all
  have `Unpin` types satisfies the conditions; Rust rejects references to possibly unaligned fields);
* pointers from one field to a sibling field of the same struct (as in compiler-generated async
  state machines), pointers between distinct values, interior pointers and pointer arithmetic
  are not modelled;
* built-in assumption: self-pointers and list entries are established only at a pinned field
  location holding a non-`Unpin` value (`Act.setSelf`/`Act.register` are no-ops otherwise;
  `setSelf_requires_pinned_nonUnpin`, `register_requires_pinned_nonUnpin`);
* pinning is per field location (`Act.pinField`); `Act.pinObj` is inert at the action level
  (`pinObj_inert_in_core`, `pinField_without_pinObj_protects`), and `SafeOp` requires it before
  a structural projection;
* `take`/`overwrite` are callable whether or not the object is pinned, and `Op.forget` leaves
  earlier references usable (closer to `Box::leak` than to a value-consuming `mem::forget`);
* `Act.dropTemp`/`Act.freeTemp` act on the most recently allocated object (the address
  `st.heap.length - 1`, with truncated subtraction; on the empty heap both are no-ops,
  `tempActs_noop_on_empty_heap`); compiled operations use them inside `moveDrop`, right after
  the move-out that created the temporary;
* every result starts from the empty heap `State.init`, except the frame and leak statements of
  R9, which hold for every state.

**Subjects and their relationship.** The Lean 4 toolchain `v4.34.1` (identified in
`REPORT.json`) checks every theorem. The three Rust sources in `REPORT.json` (the `core::pin`
module documentation at a pinned `rust-lang/rust` commit, RFC 2349 at a pinned `rust-lang/rfcs`
commit, and the `pin-project` 1.2.0 safety documentation at a pinned commit) are the documents
whose informal requirements the toy definitions are meant to formalize; they are interpreted
through the modeling bridges above, and no Rust code was compiled or run.

**Lean.** `leanprover/lean4:v4.34.1`; no Mathlib and no other dependency (the Lake project has
one `[[lean_lib]]` and no `[[require]]`); the sources import no module outside the package.

**Evidence roles.** Every Lean theorem is `execution (Lean kernel check)`. Every sentence
connecting the toy model to Rust is `derived (modeling bridge)` and is marked as such.

## Findings

Statement blocks below are verbatim quotes of the Lean sources in `lean/ToyPin/`, each labelled
with its `file:line` range; `:= …` marks an elided proof. A block whose cue says "Unfolded" is a
Lean term that elaborates in the quoted theorem's context (namespace `Toy.Pin`) and is
definitionally equal to the theorem's statement. All names are in namespace `Toy.Pin`.

### Model: heap, values and invariants

Memory is a list of objects; the address of an object is its index. A location is a field
location `(object address, field index)`.

```lean
-- ToyPin/Model.lean:33
abbrev Loc := Nat × Nat

-- ToyPin/Model.lean:41-45
structure Leaf where
  id : Nat
  unpin : Bool
  selfPtr : Option Loc
  deriving DecidableEq, Repr

-- ToyPin/Model.lean:58-64
structure Obj where
  fields : List (Option Leaf)
  live : Bool
  pinned : Bool
  pinnedFields : List Nat
  leaked : Bool
  deriving DecidableEq, Repr

-- ToyPin/Model.lean:78-82
structure State where
  heap : List Obj
  registry : List (Loc × Nat)
  nextId : Nat
  deriving DecidableEq, Repr
```

* No location denotes a whole object, so a struct as a whole never carries a self-pointer or a
  list entry.
* A leaf is the value in one field location; `id` is a ghost identity (fresh per allocation or
  write), `unpin` says whether its type is `Unpin`, and `selfPtr` is the location it stored as
  its own. Modeling bridge: a value that stored its own address.
* `registry` is an external intrusive list: an entry `(l, id)` means "a node holds address `l`
  and expects the value with identity `id` there". Modeling bridge: a waiter queue whose nodes
  live inside the waiting values.
* `pinnedFields`: the field indices for which a `Pin<&mut Field>` has been created; the list is
  not checked against the number of fields (see "Reading the heap" below). `pinned`: a `Pin`
  to the whole object has been created; at the level of primitive actions it is inert
  (`pinObj_inert_in_core`), and safe programs require it before a structural projection.
* `leaked`: the object was leaked by `forget`; afterwards `SafeOp` forbids dropping or leaking it
  again, while references obtained earlier stay usable.

Reading the heap. `Obj.leaf` returns the leaf in a field of an object; `State.leafAt`,
`State.width`, `State.isLive`, `State.isPinned`, `State.isLeaked` and `State.isPinnedLoc` look up
the object at an address (and, where applicable, a field index). Out-of-range addresses and
out-of-range field indices behave differently:

* At an address that holds no object (`st.heap.length ≤ b`), `State.leafAt` returns `none`,
  `State.width` returns `0`, and the four flags `State.isLive`, `State.isPinned`,
  `State.isLeaked` and `State.isPinnedLoc` return `false`, whatever the field index
  (`heap_reads_at_out_of_range_address`). The empty machine `State.init` has the empty heap, so
  every address is out of range in it (`heap_reads_in_init`).
* At an address that holds an object, a field index at or beyond the object's number of fields
  (`State.width`) gives `none` from `Obj.leaf` and `State.leafAt` (`Obj.leaf_of_out_of_range`,
  `leafAt_of_out_of_range_field`). `State.isPinnedLoc` checks no such bound: it tests whether the
  index is in the object's `pinnedFields` list, and `Act.pinField l` prepends `l.2` to that list
  without comparing it with the number of fields (`applyAct`, quoted below). So `isPinnedLoc l`
  is `true` after `Act.pinField l` whenever address `l.1` holds an object, whatever `l.2`
  (`isPinnedLoc_pinField_self`). The `.projPin b i` case of `SafeOp` (quoted below) does not
  compare `i` with the number of fields either. On the zero-field declaration
  `dZeroOutOfBounds`, the safe program `[.new, .pin 0, .projPin 0 0]` ends in a state in which
  object 0 has width `0` and `State.leafAt (0, 0)` is `none`, yet `State.isPinnedLoc (0, 0)` is
  `true` (`isPinnedLoc_at_out_of_range_field`).
* `PinnedNonUnpin st l` (below) requires both `State.isPinnedLoc st l = true` and a non-`Unpin`
  leaf at `l`, so it implies that address `l.1` holds an object and that `l.2` is below that
  object's width (`pinnedNonUnpin_in_range`); in the state just described it is `false` at
  `(0, 0)` (`isPinnedLoc_at_out_of_range_field`).

`Obj.fresh` builds a live, unpinned, unleaked object with the given fields. The declarations
quoted from `ToyPin/Model.lean:93-129` lie in namespace `State` (full names `State.init`,
`State.leafAt`, …).

```lean
-- ToyPin/Model.lean:67
def Obj.fresh (fs : List (Option Leaf)) : Obj := ⟨fs, true, false, [], false⟩

-- ToyPin/Model.lean:70-73
def Obj.leaf (o : Obj) (i : Nat) : Option Leaf :=
  match o.fields[i]? with
  | some x => x
  | none => none

-- ToyPin/Model.lean:93-129
def init : State := ⟨[], [], 0⟩

/-- The leaf at a location, if the location exists and is occupied. -/
def leafAt (st : State) (l : Loc) : Option Leaf :=
  match st.heap[l.1]? with
  | some o => o.leaf l.2
  | none => none

/-- Number of field locations of the object at `b` (0 if there is no such object). -/
def width (st : State) (b : Nat) : Nat :=
  match st.heap[b]? with
  | some o => o.fields.length
  | none => 0

/-- The object at `b` is allocated. -/
def isLive (st : State) (b : Nat) : Bool :=
  match st.heap[b]? with
  | some o => o.live
  | none => false

/-- The object at `b` has been pinned. -/
def isPinned (st : State) (b : Nat) : Bool :=
  match st.heap[b]? with
  | some o => o.pinned
  | none => false

/-- The owner of the object at `b` was leaked with `mem::forget`. -/
def isLeaked (st : State) (b : Nat) : Bool :=
  match st.heap[b]? with
  | some o => o.leaked
  | none => false

/-- A `Pin<&mut Field>` to location `l` has been created. -/
def isPinnedLoc (st : State) (l : Loc) : Bool :=
  match st.heap[l.1]? with
  | some o => decide (l.2 ∈ o.pinnedFields)
  | none => false
```

The two address-sensitive invariants and the protected locations:

```lean
-- ToyPin/Model.lean:274-275
def SelfRefOK (st : State) : Prop :=
  ∀ l v, st.leafAt l = some v → v.selfPtr = none ∨ v.selfPtr = some l

-- ToyPin/Model.lean:280-281
def ListOK (st : State) : Prop :=
  ∀ e ∈ st.registry, (st.leafAt e.1).map Leaf.id = some e.2

-- ToyPin/Model.lean:284
def AddrInv (st : State) : Prop := SelfRefOK st ∧ ListOK st

-- ToyPin/Model.lean:288-289
def PinnedNonUnpin (st : State) (l : Loc) : Prop :=
  st.isPinnedLoc l = true ∧ (st.leafAt l).map Leaf.unpin = some false
```

Primitive actions (`Act`). Their effect is given by `applyAct`, quoted verbatim below together
with its helpers; in prose: `alloc fs` appends a live object with fresh leaves; `pinObj b` sets `pinned`;
`pinField l` records `l` in `pinnedFields`; `setSelf l` and `register l` store the self-pointer
`l` in the leaf at `l`, respectively add the list entry `(l, id)`, and take effect only if `l` is
a pinned field location holding a non-`Unpin` leaf (built-in modeling assumption: a type relying
on its address is `!Unpin` and sets up that reliance only through `Pin<&mut Self>`); `moveOut l`
moves the leaf (identity and self-pointer unchanged) to a fresh temporary object and leaves `l`
empty; `moveObj b` moves all fields to a fresh object; `swap l l'` exchanges two leaves;
`dropLeaf l` runs the destructor in place (empties `l` and removes the list entry `(l, id)` of
the value at `l`, so the destructor unlinks by current address); `dropTemp i` and `freeTemp` drop field `i` of, respectively deallocate, the most recently
allocated object (on a non-empty heap; see Truncated subtraction below); `dealloc b` marks the object dead and invalidates its fields; `write l u`
writes a fresh value without dropping the old one; `forget b` sets `leaked`.

```lean
-- ToyPin/Model.lean:179-194
inductive Act where
  | alloc (fs : List (Option Bool))
  | pinObj (b : Nat)
  | pinField (l : Loc)
  | setSelf (l : Loc)
  | register (l : Loc)
  | moveOut (l : Loc)
  | moveObj (b : Nat)
  | swap (l l' : Loc)
  | dropLeaf (l : Loc)
  | dropTemp (i : Nat)
  | dealloc (b : Nat)
  | freeTemp
  | write (l : Loc) (u : Bool)
  | forget (b : Nat)
  deriving DecidableEq, Repr
```

The step function `applyAct`, its helpers, and `runActs`, which runs a list of actions and
returns the final state (`modifyAt f l n` changes the `n`-th element of `l` and is a no-op when
`n` is out of range). `modifyObj`, `setLeaf`, `push`, `dropAt` and `deallocAt` lie in namespace
`State` (full names `State.modifyObj`, …):

```lean
-- ToyPin/Model.lean:85-88
def modifyAt {α : Type} (f : α → α) : List α → Nat → List α
  | [], _ => []
  | a :: as, 0 => f a :: as
  | a :: as, n + 1 => a :: modifyAt f as n

-- ToyPin/Model.lean:132-133
def modifyObj (st : State) (b : Nat) (f : Obj → Obj) : State :=
  { st with heap := modifyAt f st.heap b }

-- ToyPin/Model.lean:136-137
def setLeaf (st : State) (l : Loc) (x : Option Leaf) : State :=
  st.modifyObj l.1 fun o => { o with fields := modifyAt (fun _ => x) o.fields l.2 }

-- ToyPin/Model.lean:140-141
def push (st : State) (o : Obj) : State :=
  { st with heap := st.heap ++ [o] }

-- ToyPin/Model.lean:147-149
def mkFields : Nat → List (Option Bool) → List (Option Leaf)
  | _, [] => []
  | n, u :: us => (u.map fun b => ⟨n, b, none⟩) :: mkFields (n + 1) us

-- ToyPin/Model.lean:153-154
def tempFields (i : Nat) (x : Option Leaf) : List (Option Leaf) :=
  List.replicate i none ++ [x]

-- ToyPin/Model.lean:199-204
def dropAt (st : State) (l : Loc) : State :=
  match st.leafAt l with
  | some v =>
    { st.setLeaf l none with
      registry := st.registry.filter fun e => decide (e ≠ (l, v.id)) }
  | none => st

-- ToyPin/Model.lean:207-208
def deallocAt (st : State) (b : Nat) : State :=
  st.modifyObj b fun o => { o with fields := o.fields.map fun _ => none, live := false }

-- ToyPin/Model.lean:213-244
def applyAct (st : State) : Act → State
  | .alloc fs =>
    { st.push (Obj.fresh (mkFields st.nextId fs)) with nextId := st.nextId + fs.length }
  | .pinObj b => st.modifyObj b fun o => { o with pinned := true }
  | .pinField l => st.modifyObj l.1 fun o => { o with pinnedFields := l.2 :: o.pinnedFields }
  | .setSelf l =>
    match st.leafAt l with
    | some v =>
      if st.isPinnedLoc l = true ∧ v.unpin = false then
        st.setLeaf l (some { v with selfPtr := some l })
      else st
    | none => st
  | .register l =>
    match st.leafAt l with
    | some v =>
      if st.isPinnedLoc l = true ∧ v.unpin = false then
        { st with registry := (l, v.id) :: st.registry }
      else st
    | none => st
  | .moveOut l => (st.setLeaf l none).push (Obj.fresh (tempFields l.2 (st.leafAt l)))
  | .moveObj b =>
    (st.modifyObj b fun o => { o with fields := o.fields.map fun _ => none }).push
      (Obj.fresh (match st.heap[b]? with
        | some o => o.fields
        | none => []))
  | .swap l l' => (st.setLeaf l (st.leafAt l')).setLeaf l' (st.leafAt l)
  | .dropLeaf l => st.dropAt l
  | .dropTemp i => st.dropAt (st.heap.length - 1, i)
  | .dealloc b => st.deallocAt b
  | .freeTemp => st.deallocAt (st.heap.length - 1)
  | .write l u => { st.setLeaf l (some ⟨st.nextId, u, none⟩) with nextId := st.nextId + 1 }
  | .forget b => st.modifyObj b fun o => { o with leaked := true }

-- ToyPin/Model.lean:247-249
def runActs : State → List Act → State
  | st, [] => st
  | st, a :: as => runActs (applyAct st a) as
```

Truncated subtraction. `dropTemp i` and `freeTemp` act on the object at address
`st.heap.length - 1`, where `-` is truncated subtraction on `Nat`. On a non-empty heap this is the
most recently allocated object. On the empty heap the address is `0`, which is out of range, so
both actions leave the state unchanged, and the `.freeTemp` case of `DropGuaranteeAct` below
quantifies over `i < st.width 0 = 0` and holds vacuously (`tempActs_noop_on_empty_heap`, quoted
under Auxiliary declarations cited by name).

The two parts of the pinning contract, as predicates on one action in the state where it runs,
and their lifting to traces:

```lean
-- ToyPin/Model.lean:350-354
def NoPinnedMove (st : State) : Act → Prop
  | .moveOut l => ¬ PinnedNonUnpin st l
  | .moveObj b => ∀ i < st.width b, ¬ PinnedNonUnpin st (b, i)
  | .swap l l' => ¬ PinnedNonUnpin st l ∧ ¬ PinnedNonUnpin st l'
  | _ => True

-- ToyPin/Model.lean:358-363
def DropGuaranteeAct (st : State) : Act → Prop
  | .write l _ => ¬ PinnedNonUnpin st l
  | .dealloc b => ∀ i < st.width b, ¬ PinnedNonUnpin st (b, i)
  | .freeTemp => ∀ i < st.width (st.heap.length - 1),
      ¬ PinnedNonUnpin st (st.heap.length - 1, i)
  | _ => True

-- ToyPin/Model.lean:257-259
def Always (P : State → Act → Prop) : State → List Act → Prop
  | _, [] => True
  | st, a :: as => P st a ∧ Always P (applyAct st a) as

-- ToyPin/Model.lean:252-254
def states : State → List Act → List State
  | st, [] => [st]
  | st, a :: as => st :: states (applyAct st a) as
```

### Model: struct declarations and safe programs

A declaration `Decl` describes one struct type `S`: the `Unpin`-ness of each field type, whether
`S` is declared `Unpin`, the safe operations `S` offers on `Pin<&mut S>`, its destructor, and
whether it is packed.

```lean
-- ToyPin/Structural.lean:27-36
inductive ApiOp where
  /-- Structural projection `Pin<&mut S> → Pin<&mut F_i>`. -/
  | projPin (i : Nat)
  /-- Non-structural projection `Pin<&mut S> → &mut F_i`. -/
  | projMut (i : Nat)
  /-- A move-out `Pin<&mut S> → F_i` that leaves the field empty (e.g. `Option::take`). -/
  | take (i : Nat)
  /-- `Pin<&mut S> → ()` writing a fresh value into field `i` without dropping the old one. -/
  | overwrite (i : Nat)
  deriving DecidableEq, Repr

-- ToyPin/Structural.lean:39-44
inductive DtorOp where
  /-- Move the value out of field `i` (e.g. `mem::replace`), then drop the moved value. -/
  | moveOut (i : Nat)
  /-- Write a fresh value into field `i` without dropping the old one (e.g. `ptr::write`). -/
  | overwrite (i : Nat)
  deriving DecidableEq, Repr

-- ToyPin/Structural.lean:47-58
structure Decl where
  /-- One entry per field: does the field's type implement `Unpin`? -/
  fieldUnpin : List Bool
  /-- Does `S` implement `Unpin`? -/
  unpin : Bool
  /-- Safe operations offered on `Pin<&mut S>`. -/
  api : List ApiOp
  /-- Actions of the destructor of `S`, in order. -/
  dtor : List DtorOp
  /-- Is `S` `#[repr(packed)]`? -/
  packed : Bool
  deriving DecidableEq, Repr

-- ToyPin/Structural.lean:63
def nfields (d : Decl) : Nat := d.fieldUnpin.length

-- ToyPin/Structural.lean:66
def fieldTy (d : Decl) (i : Nat) : Bool := (d.fieldUnpin[i]?).getD true

-- ToyPin/Structural.lean:70-71
def PinnedNonUnpinField (d : Decl) (i : Nat) : Prop :=
  ApiOp.projPin i ∈ d.api ∧ d.fieldTy i = false
```

Modeling bridge: `projPin i` is `fn(Pin<&mut S>) -> Pin<&mut F_i>` (structural); `projMut i` is
`fn(Pin<&mut S>) -> &mut F_i` (non-structural); `take i` is an `Option::take`-like move-out;
`overwrite i` is a `ptr::write`-like write without drop; `packed` is `#[repr(packed)]`. In this
package "structurally projected field" (also "structurally pinned field") means exactly
`ApiOp.projPin i ∈ d.api`. `d.unpin = true` means that `S` is *declared* `Unpin`;
`d.fieldTy i = true` means that field `i`'s *type* is `Unpin` (indices beyond the field list
count as `Unpin`); `d.nfields` is the number of fields.

The six conditions (a)–(f):

```lean
-- ToyPin/Structural.lean:100-101
def UnpinOnlyIfPinnedFieldsUnpin (d : Decl) : Prop :=
  d.unpin = true → ∀ i, ApiOp.projPin i ∈ d.api → d.fieldTy i = true

-- ToyPin/Structural.lean:105-106
def DtorNoMoveOutOfPinned (d : Decl) : Prop :=
  ∀ i, d.PinnedNonUnpinField i → DtorOp.moveOut i ∉ d.dtor

-- ToyPin/Structural.lean:110-111
def DropGuaranteeForPinned (d : Decl) : Prop :=
  ∀ i, d.PinnedNonUnpinField i → ApiOp.overwrite i ∉ d.api ∧ DtorOp.overwrite i ∉ d.dtor

-- ToyPin/Structural.lean:115-116
def NoPinnedTake (d : Decl) : Prop :=
  ∀ i, d.PinnedNonUnpinField i → ApiOp.take i ∉ d.api

-- ToyPin/Structural.lean:120-121
def NotPackedIfPinned (d : Decl) : Prop :=
  d.packed = true → ∀ i, ¬ d.PinnedNonUnpinField i

-- ToyPin/Structural.lean:125-126
def ProjectionConsistent (d : Decl) : Prop :=
  ∀ i, d.PinnedNonUnpinField i → ApiOp.projMut i ∉ d.api
```

Safe-code operations, when `SafeOp` allows them, and their compilation to primitive actions
(`dropActs`: the destructor of `S`, then the drop glue of every field — in place, or for a packed
struct via a move to a temporary — then deallocation):

```lean
-- ToyPin/Structural.lean:152-183
inductive Op where
  /-- `S::new()`: allocate an object whose every field holds a fresh value. -/
  | new
  /-- Pin the owned object at `b` (`Box::pin`, `pin!`). -/
  | pin (b : Nat)
  /-- Call the structural projection of field `i` on `Pin<&mut S>`. -/
  | projPin (b i : Nat)
  /-- `F::init(self: Pin<&mut F>)`: the value at `l` stores its own address. -/
  | initSelf (l : Loc)
  /-- `F::link(self: Pin<&mut F>)`: the value at `l` links itself into the external list. -/
  | link (l : Loc)
  /-- `drop(mem::replace(&mut s.f_i, F_i::new()))` through some `&mut F_i`. -/
  | replaceField (b i : Nat)
  /-- `mem::swap(&mut s.f_i, &mut t.f_i)` for two distinct objects `s` at `b`, `t` at `c`. -/
  | swapField (b c i : Nat)
  /-- `s.f_i = F_i::new()` (drops the old value in place, then writes). -/
  | assignField (b i : Nat)
  /-- `let old = mem::replace(&mut *s, S::new())` through some `&mut S`; `old` is kept, as a
  live unpinned object, at the next free address. -/
  | replaceStruct (b : Nat)
  /-- `drop(s.as_mut().take_i())` using `S`'s own move-out operation. -/
  | take (b i : Nat)
  /-- `s.as_mut().overwrite_i()` using `S`'s own overwrite-without-drop operation. -/
  | overwrite (b i : Nat)
  /-- Drop the owner of the object at `b`. -/
  | drop (b : Nat)
  /-- Leak the object at `b`. Afterwards `SafeOp` forbids `drop b` and `forget b`; other
  operations on `b` stay available (references obtained earlier survive, as with
  `Box::leak`). A value-consuming `mem::forget` of the only owner corresponds to
  continuations that never mention `b` (see `unmentioned_object_unchanged`). -/
  | forget (b : Nat)
  deriving DecidableEq, Repr

-- ToyPin/Structural.lean:189-192
def MutFieldAvail (d : Decl) (st : State) (b i : Nat) : Prop :=
  st.isLive b = true ∧
    (st.isPinned b = false ∨ d.unpin = true ∨ ApiOp.projMut i ∈ d.api ∨
      (st.isPinnedLoc (b, i) = true ∧ d.fieldTy i = true))

-- ToyPin/Structural.lean:195-196
def MutStructAvail (d : Decl) (st : State) (b : Nat) : Prop :=
  st.isLive b = true ∧ (st.isPinned b = false ∨ d.unpin = true)

-- ToyPin/Structural.lean:199-212
def SafeOp (d : Decl) (st : State) : Op → Prop
  | .new => True
  | .pin b => st.isLive b = true ∧ st.isPinned b = false
  | .projPin b i => st.isLive b = true ∧ st.isPinned b = true ∧ ApiOp.projPin i ∈ d.api
  | .initSelf l => st.isLive l.1 = true ∧ st.isPinnedLoc l = true
  | .link l => st.isLive l.1 = true ∧ st.isPinnedLoc l = true
  | .replaceField b i => MutFieldAvail d st b i
  | .swapField b c i => b ≠ c ∧ MutFieldAvail d st b i ∧ MutFieldAvail d st c i
  | .assignField b i => MutFieldAvail d st b i
  | .replaceStruct b => MutStructAvail d st b
  | .take b i => st.isLive b = true ∧ ApiOp.take i ∈ d.api
  | .overwrite b i => st.isLive b = true ∧ ApiOp.overwrite i ∈ d.api
  | .drop b => st.isLive b = true ∧ st.isLeaked b = false
  | .forget b => st.isLive b = true ∧ st.isLeaked b = false
```
```lean
-- ToyPin/Structural.lean:222
def moveDrop (l : Loc) : List Act := [.moveOut l, .dropTemp l.2, .freeTemp]

-- ToyPin/Structural.lean:225-227
def dtorActs (d : Decl) (b : Nat) : DtorOp → List Act
  | .moveOut i => moveDrop (b, i)
  | .overwrite i => [.write (b, i) (d.fieldTy i)]

-- ToyPin/Structural.lean:231-232
def glueActs (d : Decl) (b i : Nat) : List Act :=
  if d.packed then moveDrop (b, i) else [.dropLeaf (b, i)]

-- ToyPin/Structural.lean:236-238
def dropActs (d : Decl) (b : Nat) : List Act :=
  d.dtor.flatMap (dtorActs d b) ++ (List.range d.nfields).flatMap (glueActs d b) ++
    [.dealloc b]

-- ToyPin/Structural.lean:241-255
def expand (d : Decl) : Op → List Act
  | .new => [.alloc (d.fieldUnpin.map some)]
  | .pin b => [.pinObj b]
  | .projPin b i => [.pinField (b, i)]
  | .initSelf l => [.setSelf l]
  | .link l => [.register l]
  | .replaceField b i => moveDrop (b, i) ++ [.write (b, i) (d.fieldTy i)]
  | .swapField b c i => [.swap (b, i) (c, i)]
  | .assignField b i => [.dropLeaf (b, i), .write (b, i) (d.fieldTy i)]
  | .replaceStruct b =>
    .moveObj b :: (List.range d.nfields).map fun i => .write (b, i) (d.fieldTy i)
  | .take b i => moveDrop (b, i)
  | .overwrite b i => [.write (b, i) (d.fieldTy i)]
  | .drop b => dropActs d b
  | .forget b => [.forget b]

-- ToyPin/Structural.lean:258
def compile (d : Decl) (prog : List Op) : List Act := prog.flatMap (expand d)

-- ToyPin/Structural.lean:261-263
def SafeProgram (d : Decl) : State → List Op → Prop
  | _, [] => True
  | st, op :: ops => SafeOp d st op ∧ SafeProgram d (runActs st (expand d op)) ops

-- ToyPin/Structural.lean:273-274
def SafeProgramsKeepAddrInv (d : Decl) : Prop :=
  ∀ prog, SafeProgram d State.init prog → ∀ s ∈ states State.init (compile d prog), AddrInv s
```

`take` and `overwrite` are callable whether or not the object is pinned (this only adds safe
programs). After `forget b`, `SafeOp` forbids `drop b` and `forget b`; other operations on `b`
stay available. Claims quantifying over "safe programs" in this package always mean the
programs accepted by the generator `SafeProgram d` from the stated state and run through
`compile d`.

### Model: Unpin rules, scope and leaks

```lean
-- ToyPin/Unpin.lean:36-37
def PinnedFieldsUnpin (d : Decl) : Prop :=
  ∀ i, ApiOp.projPin i ∈ d.api → d.fieldTy i = true

-- ToyPin/Unpin.lean:40
def autoUnpin (d : Decl) : Bool := d.fieldUnpin.all id

-- ToyPin/Unpin.lean:248
def pinnedFieldsRule (d : Decl) : Bool := decide (PinnedFieldsUnpin d)

-- ToyPin/Unpin.lean:225-227
def SoundUnpinRule (r : Decl → Bool) : Prop :=
  ∀ d : Decl, DtorNoMoveOutOfPinned d → DropGuaranteeForPinned d → NoPinnedTake d →
    NotPackedIfPinned d → ProjectionConsistent d → SafeProgramsKeepAddrInv { d with unpin := r d }
```

`AddrStateAtProjected d st`: every self-pointer target and every list entry of `st` lies at a
field index that `d` projects structurally. `Op.Mentions b op`: the operation names object `b`
as its target, or as one of the two objects of a swap (a field index equal to `b` does not
count).

```lean
-- ToyPin/Scope.lean:251-253
def AddrStateAtProjected (d : Decl) (st : State) : Prop :=
  (∀ l v, st.leafAt l = some v → ∀ m, v.selfPtr = some m → ApiOp.projPin m.2 ∈ d.api) ∧
  (∀ e ∈ st.registry, ApiOp.projPin e.1.2 ∈ d.api)

-- ToyPin/Leak.lean:248-261
def Op.Mentions (b : Nat) : Op → Prop
  | .new => False
  | .pin c => c = b
  | .projPin c _ => c = b
  | .initSelf l => l.1 = b
  | .link l => l.1 = b
  | .replaceField c _ => c = b
  | .swapField c c' _ => c = b ∨ c' = b
  | .assignField c _ => c = b
  | .replaceStruct c => c = b
  | .take c _ => c = b
  | .overwrite c _ => c = b
  | .drop c => c = b
  | .forget c => c = b
```

### Model: named declarations, programs and traces

Every witness named in the cards, quoted verbatim.

```lean
-- ToyPin/Necessity.lean:21
def dBase : Decl := ⟨[false], false, [.projPin 0], [], false⟩

-- ToyPin/Necessity.lean:25
def pinAndInit : List Op := [.new, .pin 0, .projPin 0 0, .initSelf (0, 0)]

-- ToyPin/Necessity.lean:28
def pinAndLink : List Op := [.new, .pin 0, .projPin 0 0, .link (0, 0)]

-- ToyPin/Necessity.lean:37
def dA : Decl := { dBase with unpin := true }

-- ToyPin/Necessity.lean:39
def progA : List Op := pinAndInit ++ [.replaceStruct 0]

-- ToyPin/Necessity.lean:54
def dB : Decl := { dBase with dtor := [.moveOut 0] }

-- ToyPin/Necessity.lean:55
def progB : List Op := pinAndInit ++ [.drop 0]

-- ToyPin/Necessity.lean:68
def dC : Decl := { dBase with api := [.projPin 0, .overwrite 0] }

-- ToyPin/Necessity.lean:71
def progC : List Op := pinAndLink ++ [.overwrite 0 0]

-- ToyPin/Necessity.lean:84
def dC' : Decl := { dBase with dtor := [.overwrite 0] }

-- ToyPin/Necessity.lean:85
def progC' : List Op := pinAndLink ++ [.drop 0]

-- ToyPin/Necessity.lean:106
def dD : Decl := { dBase with api := [.projPin 0, .take 0] }

-- ToyPin/Necessity.lean:107
def progD : List Op := pinAndInit ++ [.take 0 0]

-- ToyPin/Necessity.lean:120
def dE : Decl := { dBase with packed := true }

-- ToyPin/Necessity.lean:121
def progE : List Op := pinAndInit ++ [.drop 0]

-- ToyPin/Necessity.lean:134
def dF : Decl := { dBase with api := [.projPin 0, .projMut 0] }

-- ToyPin/Necessity.lean:137
def progF : List Op := [.new, .new, .pin 0, .projPin 0 0, .initSelf (0, 0), .swapField 0 1 0]

-- ToyPin/Necessity.lean:189
def dFUnpin : Decl := ⟨[true], false, [.projPin 0, .projMut 0], [], false⟩

-- ToyPin/Necessity.lean:200
def dConservative : Decl := ⟨[false, true], true, [.projMut 0, .projPin 1], [], false⟩
```
```lean
-- ToyPin/Necessity.lean:251
def dNoProj : Decl := ⟨[false], true, [], [], false⟩

-- ToyPin/Necessity.lean:303
def dUnpinField : Decl := ⟨[true], true, [.projPin 0], [], false⟩

-- ToyPin/Necessity.lean:320
def dUnpinNonStructural : Decl := ⟨[false], true, [.projMut 0], [], false⟩

-- ToyPin/Examples.lean:108-110
def dPermissive : Decl :=
  ⟨[true, false], true, [.projPin 0, .projMut 0, .take 0, .overwrite 0, .projMut 1],
    [.moveOut 0, .overwrite 0, .moveOut 1], true⟩

-- ToyPin/Examples.lean:141-144
def dRich : Decl :=
  ⟨[false, false, true], false,
    [.projPin 0, .projMut 1, .take 1, .overwrite 1, .projPin 2, .projMut 2],
    [.moveOut 1, .overwrite 1], false⟩

-- ToyPin/Examples.lean:146-150
def progRich : List Op :=
  [.new, .new, .pin 0, .projPin 0 0, .projPin 0 2, .initSelf (0, 0), .link (0, 0),
    .replaceField 0 1, .swapField 0 1 1, .take 0 1, .overwrite 0 1, .assignField 0 2,
    .replaceField 0 2, .replaceStruct 1, .pin 1, .projPin 1 0, .link (1, 0), .forget 1,
    .drop 0, .drop 5]

-- ToyPin/Unpin.lean:78-79
def unpinWitness (i : Nat) : List Op :=
  [.new, .pin 0, .projPin 0 i, .initSelf (0, i), .replaceStruct 0]

-- ToyPin/Necessity.lean:342-345
def permissiveRule (d : Decl) : Bool :=
  pinnedFieldsRule d ||
    !decide (DtorNoMoveOutOfPinned d ∧ DropGuaranteeForPinned d ∧ NoPinnedTake d ∧
      NotPackedIfPinned d ∧ ProjectionConsistent d)

-- ToyPin/Necessity.lean:219
def rPackedOrPinned (d : Decl) : Bool := d.packed || pinnedFieldsRule d
```
```lean
-- ToyPin/CoreForget.lean:15-16
def coreMoveActs : List Act :=
  [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0), .moveOut (0, 0)]

-- ToyPin/CoreForget.lean:26-28
def coreReuseActs : List Act :=
  [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0), .register (0, 0),
    .write (0, 0) false]

-- ToyPin/CoreForget.lean:40-45
def coreNonVacuousActs : List Act :=
  [.alloc [some false, some true, some false], .pinObj 0, .pinField (0, 0), .pinField (0, 1),
    .setSelf (0, 0), .register (0, 0), .setSelf (0, 2), .moveOut (0, 1), .dropTemp 1,
    .freeTemp, .write (0, 1) true, .alloc [some false], .swap (0, 2) (2, 0),
    .moveObj 2, .dropLeaf (0, 0), .write (0, 0) false, .dropLeaf (0, 0), .dropLeaf (0, 1),
    .dropLeaf (0, 2), .dealloc 0, .forget 3]

-- ToyPin/CoreForget.lean:149
def leakProg : List Op := pinAndInit ++ [.link (0, 0), .forget 0]

-- ToyPin/CoreForget.lean:159
def stLeaked : State := runActs State.init (compile dBase leakProg)

-- ToyPin/Examples.lean:44-45
def stSelf : State :=
  runActs State.init [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0)]

-- ToyPin/Examples.lean:46
def stLinked : State := applyAct stSelf (.register (0, 0))

-- ToyPin/Companions.lean:150
def dZero : Decl := ⟨[], true, [], [], false⟩

-- ToyPin/Companions.lean:179-180
def dZeroOutOfBounds : Decl :=
  ⟨[], true, [.projPin 0, .projMut 0, .take 0, .overwrite 0], [.moveOut 0, .overwrite 0], true⟩

-- ToyPin/Companions.lean:183-185
def progZero : List Op :=
  [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .link (0, 0), .take 0 0,
    .overwrite 0 0, .replaceStruct 0, .drop 0]
```

| declaration | shape | status (with the theorem that shows it) |
|---|---|---|
| `dBase` | one non-`Unpin` field, structurally projected; not declared `Unpin` | satisfies (a)–(f) (`dBase_satisfies_all`); every safe program keeps `AddrInv` (`dBase_sound`); non-empty safe program: `pinAndInit ++ [.drop 0]` (`safeProgram_pos_neg`) |
| `dA`, `dB`, `dC`, `dC'`, `dD`, `dE`, `dF` | `dBase` changed in one place | each violates exactly one of (a)–(f) and satisfies the other five (R3 `_tight` theorems) |
| `dFUnpin` | like `dF` (both projections of field 0) but the field type is `Unpin` | (a)–(f) hold vacuously (no structurally projected non-`Unpin` field); every safe program keeps `AddrInv` (`projection_inconsistent_unpin_field_sound`); non-empty safe program using both projections (`dFUnpin_nonvacuous`) |
| `dConservative` | declared `Unpin`; non-`Unpin` field 0 non-structural, `Unpin` field 1 structural | every safe program keeps `AddrInv` (`autoUnpin_conservative`); non-empty safe program (`sound_declarations_nonvacuous`) |
| `dNoProj` | declared `Unpin`; one non-`Unpin` field; no projection at all | vacuous: no self-pointer or list entry can arise, so every safe program keeps `AddrInv` (`noProjection_unpin_vacuously_sound`); non-empty safe program (`noAddrState_nonvacuous_nonempty`) |
| `dUnpinField` | declared `Unpin`; one `Unpin` field, structurally projected | the witness program `unpinWitness 0` is safe and keeps `AddrInv` (`unpinWitness_fieldTy_tight`) |
| `dUnpinNonStructural` | declared `Unpin`; one non-`Unpin` field, non-structural | every safe program keeps `AddrInv` (`unpinWitness_projPin_tight`); non-empty safe program (`sound_declarations_nonvacuous`) |
| `dPermissive` | packed, declared `Unpin`; structurally projected field 0 is `Unpin`; moving destructor, take, overwrite | (a)–(f) hold vacuously (`conditions_vacuous_without_pinned_nonUnpin`) |
| `dRich` | three fields mixing structural and non-structural projections | satisfies (a)–(f); `progRich` is safe and establishes a self-pointer and two list entries (`structural_nonvacuous`) |
| `dZero`, `dZeroOutOfBounds` | zero fields (the second names the out-of-range index 0 in API and destructor) | satisfy (a)–(f); every safe program keeps `AddrInv` (`zero_field_declarations_sound`); non-empty safe programs (`zero_field_declarations_sound`, `sound_declarations_nonvacuous`) |

### Definition examples

Every core definition has proved positive examples (instances it must admit) and negative
examples (instances it must reject), in `ToyPin/Examples.lean` unless noted.

| definition | positive | negative |
|---|---|---|
| `setSelf`/`register` semantics | `setSelf_requires_pinned_nonUnpin`, `register_requires_pinned_nonUnpin` (pinned non-`Unpin`: takes effect) | same theorems (unpinned, or `Unpin`: no effect) |
| `pinObj` vs `pinField` | `pinField_without_pinObj_protects` (`CoreForget.lean`) | `pinObj_inert_in_core` (`CoreForget.lean`) |
| `SelfRefOK` | `selfRefOK_pos` | `selfRefOK_neg` (after a move) |
| `ListOK` | `listOK_pos`, `listOK_after_proper_drop` | `listOK_neg` (write, dealloc, move) |
| `AddrInv` | `addrInv_pos` | `addrInv_neg` |
| `PinnedNonUnpin` | `pinnedNonUnpin_pos` | `pinnedNonUnpin_neg` (unpinned; `Unpin`; dropped) |
| `NoPinnedMove` | `noPinnedMove_pos` | `noPinnedMove_neg` |
| `DropGuaranteeAct` | `dropGuaranteeAct_pos` | `dropGuaranteeAct_neg` (dealloc, write, freeTemp) |
| `PinnedNonUnpinField` | `pinnedNonUnpinField_pos` | `pinnedNonUnpinField_neg` |
| (a)–(f) | `conditions_pos_neg` (`dBase`) | `conditions_pos_neg` (`dA` … `dF`) |
| (a)–(f) without structurally projected non-`Unpin` fields | `conditions_vacuous_without_pinned_nonUnpin` (`dPermissive`; vacuous) | — |
| `SafeOp`, `SafeProgram` | `safeOp_pos_neg`, `safeProgram_pos_neg` | same theorems |
| `PinnedFieldsUnpin`, `autoUnpin` | `pinnedFieldsUnpin_pos_neg`, `autoUnpin_pos_neg` | same theorems |
| `SoundUnpinRule` | `pinnedFieldsRule_sound`, `autoUnpin_sound`, `neverUnpin_sound`, `permissiveRule_sound`, `rPackedOrPinned_sound` (the quantified domain is non-empty: `dBase` satisfies (b)–(f), `dBase_satisfies_all`) | `alwaysUnpin_unsound` |
| `AddrStateAtProjected` | `addrStateAtProjected_pos_neg` (`Companions.lean`; the final state of a safe program on `dBase` with a self-pointer and a list entry at structurally projected field 0); `addrState_only_at_structurally_projected_fields` (every visited state of every safe program) | `addrStateAtProjected_pos_neg` (the final state of the unsafe program `pinAndInit` on `dNoProj`); `addrState_hsafe_tight` |
| `Op.Mentions` | `op_mentions_pos_neg` (`Companions.lean`; `drop 0`, `swapField 1 0 0`, `initSelf (0, 2)` mention object 0) | same theorem (`new`, `projPin 1 0`, `link (1, 0)` do not mention object 0) |
| `forget` (leaked object) | `forget_keeps_addrInv_and_blocks_drop` (`CoreForget.lean`) | `forget_does_not_freeze_fields` (fields of a leaked object still change) |

### R1 `core-no-move-and-drop-guarantee-keep-address-invariants`

Kind: theorem. Tier: T1. Depth: shallow.

Lean statement (verbatim):

```lean
-- ToyPin/Core.lean:369-372
theorem addrInv_of_noPinnedMove_of_dropGuarantee (acts : List Act)
    (hmove : Always NoPinnedMove State.init acts)
    (hdrop : Always DropGuaranteeAct State.init acts) :
    ∀ s ∈ states State.init acts, AddrInv s := …
```

Unfolded statement of `addrInv_of_noPinnedMove_of_dropGuarantee`, with `AddrInv`, `SelfRefOK` and `ListOK` unfolded:

```lean
∀ (acts : List Act), Always NoPinnedMove State.init acts →
  Always DropGuaranteeAct State.init acts →
    ∀ s ∈ states State.init acts,
      (∀ l v, s.leafAt l = some v → v.selfPtr = none ∨ v.selfPtr = some l) ∧
        ∀ e ∈ s.registry, (s.leafAt e.1).map Leaf.id = some e.2
```

**Plain claim.** For every list acts of primitive actions run from the empty toy heap State.init (every list of Act is allowed): if no action moves a value out of a pinned field location holding a non-Unpin value (Always NoPinnedMove State.init acts) and no action deallocates or overwrites the memory of such a value before its destructor has run (Always DropGuaranteeAct State.init acts), then in every visited state every set self-pointer points at its own field location (SelfRefOK) and every intrusive-list entry finds, at its address, the value that registered (ListOK).

**Hypothesis ledger.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hmove : Always NoPinnedMove State.init acts` | No action moves a value out of a pinned field location whose value is not Unpin (compiler moves, such as packed drop glue, count as moves). | tight | `noPinnedMove_tight` | a one-object, one-field trace of 5 primitive actions from State.init (coreMoveActs) |
| `hdrop : Always DropGuaranteeAct State.init acts` | The drop guarantee: no deallocation or overwrite of a pinned non-Unpin value's memory before its destructor runs. | tight | `dropGuarantee_tight` | a one-object, one-field trace of 6 primitive actions from State.init (coreReuseActs) |

**Non-vacuity witness.** coreNonVacuousActs: 21 actions that pin a non-Unpin value, set its self-pointer, link it into the list, move a pinned Unpin value and an unpinned non-Unpin value, swap, drop in place, write into emptied locations, deallocate and leak; both hypotheses hold and the self-pointer and list entry are really established. (`core_nonvacuous`)

**Tier.** T1: The pinning contract (no move, and the drop guarantee) and its purpose (self-references, intrusive collections) are documented informally in core::pin and in Jung's 2018 posts; here the implication from the contract to two concrete address-sensitive invariants is made precise and mechanized for a toy heap.

**Prior art.** [S1] (the two parts of the pinning invariant, lines 521–535); [S2] (goal, line 29; the stricter guarantee as an unresolved question, lines 392–403); [S5] (the drop guarantee motivated by intrusive collections); [S4] (a pinned typestate on paper); [S6] (intrusive list and `ptr::write`); [S7] (a related but different use of "pinning"); [S13] (negative search for mechanizations). Full records under Evidence.

**Design question.** Which action-level discipline keeps self-pointers and intrusive-list entries of pinned values valid, and does dropping either part of the pinning contract (no moves; the drop guarantee) admit a trace that breaks them?

Basis: execution (Lean kernel check) — `addrInv_of_noPinnedMove_of_dropGuarantee` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — `NoPinnedMove` and `DropGuaranteeAct` are toy formalizations of the two parts of the pinning invariant quoted from [S1] (no move out of the location; no invalidation or repurposing before `drop`); `SelfRefOK` and `ListOK` stand for a self-referential value and an intrusive collection, the uses [S1] line 535 and [S5] name. The theorem therefore reads as: in the toy, these two parts suffice to keep those two invariants. The reading is an interpretation of informal text; it is not checked against Rust semantics.

Non-claims for R1 are listed under Boundaries.

### R2 `structural-pinning-sound-under-six-conditions`

Kind: theorem. Tier: T1. Depth: shallow.

Lean statement (verbatim):

```lean
-- ToyPin/Soundness.lean:644-648
theorem addrInv_of_structural_pinning_conditions (d : Decl)
    (ha : UnpinOnlyIfPinnedFieldsUnpin d) (hb : DtorNoMoveOutOfPinned d)
    (hc : DropGuaranteeForPinned d) (hd : NoPinnedTake d) (he : NotPackedIfPinned d)
    (hf : ProjectionConsistent d) (prog : List Op) (hsafe : SafeProgram d State.init prog) :
    ∀ s ∈ states State.init (compile d prog), AddrInv s := …
```

**Plain claim.** For every toy struct declaration d: if (a) d is declared Unpin (d.unpin = true) only when every structurally projected field (ApiOp.projPin i in d.api) has an Unpin type, (b) its destructor does not move out of a structurally projected field of non-Unpin type, (c) neither its API nor its destructor overwrites such a field without dropping its value, (d) it offers no Pin<&mut S> -> F move-out of such a field, (e) it is not packed when it has such a field, and (f) such a field is not also offered through a non-structural projection, then every program accepted by SafeProgram d from State.init (a list of Op, compiled to primitive actions by compile d) keeps SelfRefOK and ListOK in every visited state.

**Hypothesis ledger.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `ha : UnpinOnlyIfPinnedFieldsUnpin d` | (a) declared Unpin only if every structurally projected field's type is Unpin; otherwise Pin::get_mut yields &mut S and mem::replace moves the pinned field. | tight | `unpinOnlyIf_tight` | a one-field declaration (dA) and a 5-operation safe program |
| `hb : DtorNoMoveOutOfPinned d` | (b) The destructor (which receives &mut self) does not move out of a structurally projected non-Unpin field. | tight | `dtorNoMoveOut_tight` | a one-field declaration (dB) and a 5-operation safe program |
| `hc : DropGuaranteeForPinned d` | (c) Neither the API nor the destructor overwrites a structurally projected non-Unpin field without dropping its value. Both conjuncts are tight separately. | tight | `dropGuaranteeForPinned_api_tight`, `dropGuaranteeForPinned_dtor_tight` | one-field declarations (dC: API overwrite; dC': destructor overwrite) and 5-operation safe programs |
| `hd : NoPinnedTake d` | (d) No Pin<&mut S> -> F move-out (Option::take-like) for a structurally projected non-Unpin field. | tight | `noPinnedTake_tight` | a one-field declaration (dD) and a 5-operation safe program |
| `he : NotPackedIfPinned d` | (e) Not #[repr(packed)] when there is a structurally projected non-Unpin field (packed drop glue moves fields to aligned temporaries). | tight | `notPacked_tight` | a one-field declaration (dE) and a 5-operation safe program |
| `hf : ProjectionConsistent d` | (f) A structurally projected non-Unpin field is not also offered through a non-structural projection Pin<&mut S> -> &mut F. | tight | `projectionConsistent_tight` | a one-field declaration (dF) and a 6-operation safe program |
| `hsafe : SafeProgram d State.init prog` | Restricts to programs every operation of which SafeOp permits in the state where it runs (e.g. a &mut to a field or to S only when SafeOp provides one). | tight | `safeProgram_tight` | the one-field declaration dBase (satisfying (a)-(f)) and the 5-operation program progA |

**Non-vacuity witness.** dRich: three fields (non-Unpin structurally projected; non-Unpin non-structural with take, overwrite and a destructor that moves it out and overwrites it; Unpin with both projections); progRich: 20 safe operations including pinning, a self-reference, two list entries, replace/swap/take/overwrite/assign of non-structural fields, replacing an unpinned struct, leaking, and dropping. All six conditions and safety hold; the conclusion is also checked directly (structural_nonvacuous_conclusion). (`structural_nonvacuous`)

**Tier.** T1: The four requirements of core::pin (structural Unpin, pinned destruction including not packed, drop guarantee, no move-out operations) plus the documented consistency of the projection choice, made precise for a toy struct and mechanized; pin-project enforces the same list.

**Prior art.** [S1] (the four requirements of structural pinning, lines 791–847, and consistency of the projection choice, lines 722–725); [S3] (`#[pin_project]` enforces the same list, lines 87–159); [S12] (language-level pinned fields with checks on the containing type); [S8] (bug finding for pinning APIs, not proof); [S9] (safety-property annotations; its treatment of `core::pin` not examined); [S10] (a 2019 talk; content not examined); [S13]. Full records under Evidence.

**Design question.** Which conditions on a struct's declaration (Unpin, destructor, API, packedness, projection choice) make structural projection Pin<&mut S> -> Pin<&mut F> sound for every safe program?

Basis: execution (Lean kernel check) — `addrInv_of_structural_pinning_conditions` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — Conditions (a)–(e) are toy versions of the four requirements of [S1] lines 791–847 (structural `Unpin`; pinned destruction, including not packed; the drop guarantee; no other move-out operations), and (f) of the consistency rule of [S1] lines 722–725. `SafeOp` encodes which `&mut` accesses safe Rust provides on a pinned or unpinned `S`. Under these correspondences the theorem says the documented list suffices in the toy; whether `rustc`, the standard library or `pin-project` meet the model's assumptions is not examined.

Non-claims for R2 are listed under Boundaries.

### R3 `each-structural-pinning-condition-tight-with-one-field-witness`

Kind: counterexample. Tier: T1. Depth: definitional.

Lean statements (verbatim):

```lean
-- ToyPin/Necessity.lean:44-50
theorem unpinOnlyIf_tight :
    ¬ UnpinOnlyIfPinnedFieldsUnpin dA ∧ DtorNoMoveOutOfPinned dA ∧ DropGuaranteeForPinned dA ∧
      NoPinnedTake dA ∧ NotPackedIfPinned dA ∧ ProjectionConsistent dA ∧
      SafeProgram dA State.init progA ∧
      ¬ (∀ s ∈ states State.init (compile dA progA), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dA progA), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile dA progA), ListOK s) := …

-- ToyPin/Necessity.lean:58-64
theorem dtorNoMoveOut_tight :
    UnpinOnlyIfPinnedFieldsUnpin dB ∧ ¬ DtorNoMoveOutOfPinned dB ∧ DropGuaranteeForPinned dB ∧
      NoPinnedTake dB ∧ NotPackedIfPinned dB ∧ ProjectionConsistent dB ∧
      SafeProgram dB State.init progB ∧
      ¬ (∀ s ∈ states State.init (compile dB progB), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dB progB), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile dB progB), ListOK s) := …

-- ToyPin/Necessity.lean:75-81
theorem dropGuaranteeForPinned_api_tight :
    UnpinOnlyIfPinnedFieldsUnpin dC ∧ DtorNoMoveOutOfPinned dC ∧ ¬ DropGuaranteeForPinned dC ∧
      NoPinnedTake dC ∧ NotPackedIfPinned dC ∧ ProjectionConsistent dC ∧
      SafeProgram dC State.init progC ∧
      ¬ (∀ s ∈ states State.init (compile dC progC), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dC progC), ¬ ListOK s) ∧
      (∀ s ∈ states State.init (compile dC progC), SelfRefOK s) := …

-- ToyPin/Necessity.lean:89-95
theorem dropGuaranteeForPinned_dtor_tight :
    UnpinOnlyIfPinnedFieldsUnpin dC' ∧ DtorNoMoveOutOfPinned dC' ∧
      ¬ DropGuaranteeForPinned dC' ∧ NoPinnedTake dC' ∧ NotPackedIfPinned dC' ∧
      ProjectionConsistent dC' ∧ SafeProgram dC' State.init progC' ∧
      ¬ (∀ s ∈ states State.init (compile dC' progC'), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dC' progC'), ¬ ListOK s) ∧
      (∀ s ∈ states State.init (compile dC' progC'), SelfRefOK s) := …

-- ToyPin/Necessity.lean:110-116
theorem noPinnedTake_tight :
    UnpinOnlyIfPinnedFieldsUnpin dD ∧ DtorNoMoveOutOfPinned dD ∧ DropGuaranteeForPinned dD ∧
      ¬ NoPinnedTake dD ∧ NotPackedIfPinned dD ∧ ProjectionConsistent dD ∧
      SafeProgram dD State.init progD ∧
      ¬ (∀ s ∈ states State.init (compile dD progD), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dD progD), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile dD progD), ListOK s) := …

-- ToyPin/Necessity.lean:124-130
theorem notPacked_tight :
    UnpinOnlyIfPinnedFieldsUnpin dE ∧ DtorNoMoveOutOfPinned dE ∧ DropGuaranteeForPinned dE ∧
      NoPinnedTake dE ∧ ¬ NotPackedIfPinned dE ∧ ProjectionConsistent dE ∧
      SafeProgram dE State.init progE ∧
      ¬ (∀ s ∈ states State.init (compile dE progE), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dE progE), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile dE progE), ListOK s) := …

-- ToyPin/Necessity.lean:140-146
theorem projectionConsistent_tight :
    UnpinOnlyIfPinnedFieldsUnpin dF ∧ DtorNoMoveOutOfPinned dF ∧ DropGuaranteeForPinned dF ∧
      NoPinnedTake dF ∧ NotPackedIfPinned dF ∧ ¬ ProjectionConsistent dF ∧
      SafeProgram dF State.init progF ∧
      ¬ (∀ s ∈ states State.init (compile dF progF), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dF progF), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile dF progF), ListOK s) := …

-- ToyPin/Necessity.lean:151-163
theorem conditions_abdef_tight_via_list :
    (SafeProgram dA State.init (pinAndLink ++ [.replaceStruct 0]) ∧
      ∃ s ∈ states State.init (compile dA (pinAndLink ++ [.replaceStruct 0])), ¬ ListOK s) ∧
    (SafeProgram dB State.init (pinAndLink ++ [.drop 0]) ∧
      ∃ s ∈ states State.init (compile dB (pinAndLink ++ [.drop 0])), ¬ ListOK s) ∧
    (SafeProgram dD State.init (pinAndLink ++ [.take 0 0]) ∧
      ∃ s ∈ states State.init (compile dD (pinAndLink ++ [.take 0 0])), ¬ ListOK s) ∧
    (SafeProgram dE State.init (pinAndLink ++ [.drop 0]) ∧
      ∃ s ∈ states State.init (compile dE (pinAndLink ++ [.drop 0])), ¬ ListOK s) ∧
    (SafeProgram dF State.init [.new, .new, .pin 0, .projPin 0 0, .link (0, 0), .swapField 0 1 0] ∧
      ∃ s ∈ states State.init
        (compile dF [.new, .new, .pin 0, .projPin 0 0, .link (0, 0), .swapField 0 1 0]),
        ¬ ListOK s) := …

-- ToyPin/Necessity.lean:99-101
theorem dropGuaranteeForPinned_invisible_to_selfRef :
    SafeProgram dC State.init (pinAndInit ++ [.overwrite 0 0]) ∧
      ∀ s ∈ states State.init (compile dC (pinAndInit ++ [.overwrite 0 0])), AddrInv s := …
```

**Plain claim.** For each of (a)-(f) there is a one-field toy declaration that satisfies the other five conditions and violates that one, together with a program of at most six operations accepted by SafeProgram from State.init along which AddrInv fails: for (a), (b), (d), (e), (f) the program sets a self-pointer, SelfRefOK fails in some visited state and ListOK holds in all of them; for (c), both by S's API (dC) and by its destructor (dC'), the program links into the list, ListOK fails in some visited state and SelfRefOK holds in all of them. Replacing the self-pointer by a list link in the (a), (b), (d), (e), (f) programs gives programs accepted by SafeProgram along which ListOK fails; with a self-pointer only, the (c) overwrite keeps AddrInv.

**Hypothesis ledger.**

Hypotheses: none. Each theorem of this card is a closed statement about named one-field declarations (`dA`, `dB`, `dC`, `dC'`, `dD`, `dE`, `dF`) and explicit programs of at most six operations, checked by evaluation; it has no parameters, so there is no hypothesis to weaken.

**Non-vacuity witness.** Not applicable (closed statements without hypotheses); each theorem exhibits its declaration (dA, dB, dC, dC', dD, dE, dF) and program and checks every conjunct by evaluation. (`unpinOnlyIf_tight`)

**Positive controls.** `dBase_sound`

**Tier.** T1: Each failure mode is described informally in core::pin (the Option::take example, the packed-drop remark, the RefCell example); here each is a concrete, checked program in the toy model.

**Prior art.** [S1] (the `Option::take` example, the packed-drop remark, the `RefCell` example); [S11] (a destructor moving out of a pin-projected field). Full records under Evidence.

**Design question.** Is each of the six structural-pinning conditions tight (does dropping it, with the other five kept, admit a safe program that breaks an invariant), and which concrete invariant (self-reference or intrusive-list entry) breaks when it is dropped?

Basis: execution (Lean kernel check) — `unpinOnlyIf_tight`, `dtorNoMoveOut_tight`, `dropGuaranteeForPinned_api_tight`, `dropGuaranteeForPinned_dtor_tight`, `noPinnedTake_tight`, `notPacked_tight`, `projectionConsistent_tight`, `conditions_abdef_tight_via_list`, `dropGuaranteeForPinned_invisible_to_selfRef` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — Each witness program is a toy rendering of a failure mode described informally in [S1] (moving out through `Pin::get_mut` on an `Unpin` struct; a destructor moving a field; an overwrite without drop; an `Option::take`-like move-out; packed drop glue; a non-structural `&mut` to a structurally pinned field).

Non-claims for R3 are listed under Boundaries.

### R4 `conditions-a-to-e-insufficient-without-projection-consistency`

Kind: counterexample. Tier: T1. Depth: definitional.

Lean statements (verbatim):

```lean
-- ToyPin/Necessity.lean:168-173
theorem conditions_a_to_e_insufficient :
    UnpinOnlyIfPinnedFieldsUnpin dF ∧ DtorNoMoveOutOfPinned dF ∧ DropGuaranteeForPinned dF ∧
      NoPinnedTake dF ∧ NotPackedIfPinned dF ∧
      SafeProgram dF State.init progF ∧
      (∃ s ∈ states State.init (compile dF progF), ¬ SelfRefOK s) ∧
      ¬ SafeProgramsKeepAddrInv dF := …

-- ToyPin/Necessity.lean:181-184
theorem projection_inconsistent_assign_harmless :
    SafeProgram dF State.init (pinAndLink ++ [.initSelf (0, 0), .assignField 0 0]) ∧
      ∀ s ∈ states State.init (compile dF (pinAndLink ++ [.initSelf (0, 0), .assignField 0 0])),
        AddrInv s := …

-- ToyPin/Necessity.lean:191
theorem projection_inconsistent_unpin_field_sound : SafeProgramsKeepAddrInv dFUnpin := …
```

**Plain claim.** The one-field toy declaration dF, which offers both a structural projection Pin<&mut S> -> Pin<&mut F> and a non-structural projection Pin<&mut S> -> &mut F of its non-Unpin field, satisfies (a)-(e); the 6-operation program progF is accepted by SafeProgram dF from State.init, uses the non-structural &mut F with mem::swap, and breaks SelfRefOK, so not every program accepted by SafeProgram dF keeps AddrInv. On the same declaration, the one 6-operation program that uses the non-structural &mut F only to assign in place (drop, then write) is accepted by SafeProgram and keeps AddrInv; and the one-field declaration dFUnpin, identical except that the field's type is Unpin, keeps AddrInv for every program accepted by SafeProgram.

**Hypothesis ledger.**

Hypotheses: none. The three theorems are closed statements about the named declarations `dF` and `dFUnpin`, the named program `progF` and one explicit program on `dF`; they have no parameters, so there is no hypothesis to weaken.

**Non-vacuity witness.** Not applicable (closed statements); dF, progF and dFUnpin are exposed. The soundness statement for dFUnpin covers a non-empty set of programs: a 6-operation program using both projections of its Unpin field is accepted by SafeProgram dFUnpin (dFUnpin_nonvacuous). (`conditions_a_to_e_insufficient`, `dFUnpin_nonvacuous`)

**Positive controls.** `projection_inconsistent_assign_harmless`, `projection_inconsistent_unpin_field_sound`

**Tier.** T1: The documentation states that the projection choice must be consistent and gives a RefCell example of pinned and unpinned access to the same data; here the minimal toy instance and two controls are checked.

**Prior art.** [S1] (consistency of the projection choice, lines 722–725, and the `RefCell` example); [S6] (projection consistency). Full records under Evidence.

**Design question.** Are the four documented requirements enough without the consistency of the projection choice, and is it the &mut itself or the moves it enables that breaks pinned invariants?

Basis: execution (Lean kernel check) — `conditions_a_to_e_insufficient`, `projection_inconsistent_assign_harmless`, `projection_inconsistent_unpin_field_sound` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — `progF` renders a safe-Rust use of a public `fn(Pin<&mut S>) -> &mut F` with `mem::swap`. In Rust, for `F: Sized + !Unpin`, such an accessor lets any caller call `mem::swap` or `mem::replace`; keeping mutation to drop-then-write requires encapsulating `&mut F` in an operation such as `Pin::set` (not proved).

Non-claims for R4 are listed under Boundaries.

### R5 `unpin-sound-iff-pinned-fields-unpin`

Kind: characterization. Tier: T1. Depth: shallow.

Lean statement (verbatim):

```lean
-- ToyPin/Unpin.lean:197-198
theorem unpin_sound_iff_pinnedFieldsUnpin (d : Decl) (hu : d.unpin = true) :
    SafeProgramsKeepAddrInv d ↔ PinnedFieldsUnpin d := …
```

Unfolded statement of `unpin_sound_iff_pinnedFieldsUnpin`, with `SafeProgramsKeepAddrInv` and `PinnedFieldsUnpin` unfolded:

```lean
∀ (d : Decl), d.unpin = true →
  ((∀ prog, SafeProgram d State.init prog → ∀ s ∈ states State.init (compile d prog), AddrInv s) ↔
    ∀ i, ApiOp.projPin i ∈ d.api → d.fieldTy i = true)
```

**Plain claim.** For every toy struct declaration d declared Unpin (d.unpin = true), with no other hypothesis: every program accepted by SafeProgram d from State.init keeps SelfRefOK and ListOK in every visited state if and only if every structurally projected field of d (ApiOp.projPin i in d.api) has an Unpin type (d.fieldTy i = true).

**Hypothesis ledger.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hu : d.unpin = true` | The equivalence is about declaring S : Unpin; for a declaration not declared Unpin, soundness does not require its structurally projected fields to be Unpin. | tight | `unpin_iff_hu_tight` | the one-field declaration dBase |

**Non-vacuity witness.** dConservative (declared Unpin; its only structurally projected field is Unpin) satisfies the hypothesis and the right side; dA (declared Unpin; structurally projected non-Unpin field) satisfies the hypothesis and fails the right side. (`unpin_iff_nonvacuous`)

**Tier.** T1: Documented requirement 1 ('a struct can be Unpin only if all of its structurally-pinned fields are') and pin-project's generated Unpin bound, stated as an exact equivalence in the toy model and mechanized.

**Prior art.** [S1] (requirement 1, "A struct can be `Unpin` only if all of its structurally-pinned fields are, too", lines 793–794); [S3] (the generated `Unpin` impl requires the `#[pin]` fields to be `Unpin`, lines 96–108; `PhantomPinned` without `#[pin]` has no effect, lines 297–313); [S2] (`Unpin` semantics, lines 39–44; the `Unpin` auto trait, lines 63–75). Full records under Evidence.

**Design question.** When may a struct with structurally projected fields be declared Unpin, and does any condition other than the field types matter?

Basis: execution (Lean kernel check) — `unpin_sound_iff_pinnedFieldsUnpin` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — `d.unpin = true` stands for `impl Unpin for S`; with it, safe Rust can obtain `&mut S` from `Pin<&mut S>` (`Pin::get_mut`), which `MutStructAvail` encodes. The equivalence is the toy version of [S1] requirement 1 and of `pin-project`'s generated bound [S3].

Non-claims for R5 are listed under Boundaries.

### R6 `unpin-with-structural-non-unpin-field-witness-breaks-self-reference`

Kind: impossibility. Tier: T1. Depth: shallow.

Lean statement (verbatim):

```lean
-- ToyPin/Unpin.lean:96-101
theorem unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field (d : Decl)
    (hu : d.unpin = true) (i : Nat) (hproj : ApiOp.projPin i ∈ d.api)
    (hty : d.fieldTy i = false) :
    SafeProgram d State.init (unpinWitness i) ∧
      (∃ s ∈ states State.init (compile d (unpinWitness i)), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile d (unpinWitness i)), ListOK s) := …
```

**Plain claim.** For every toy struct declaration d declared Unpin (d.unpin = true) and every field index i such that d offers a structural projection of field i (ApiOp.projPin i in d.api) and field i's type is not Unpin (d.fieldTy i = false), with no other condition on d: the explicit 5-operation program unpinWitness i (create, pin, project field i structurally, let the field store its own address, then mem::replace the whole struct through the &mut S that Pin::get_mut provides) is accepted by SafeProgram d from State.init, SelfRefOK fails in some visited state, and ListOK holds in every visited state.

**Hypothesis ledger.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hu : d.unpin = true` | Declaring S : Unpin is what makes &mut S, hence the whole-struct replace, available to safe code on a pinned S. | tight | `unpinWitness_hu_tight` | the one-field declaration dBase with i = 0 |
| `hproj : ApiOp.projPin i ∈ d.api` | Field i is structurally projected, so the program can pin it and let it store its address. | tight | `unpinWitness_projPin_tight` | the one-field declaration dUnpinNonStructural with i = 0 |
| `hty : d.fieldTy i = false` | Field i's type is not Unpin, so its value can establish a self-pointer. | tight | `unpinWitness_fieldTy_tight` | the one-field declaration dUnpinField with i = 0 |

**Non-vacuity witness.** dA with i = 0. (`unpin_unsound_nonvacuous`)

**Positive controls.** `unpinWitness_fieldTy_tight`, `unpinWitness_projPin_tight`, `dBase_sound`

**Tier.** T1: Documented failure mode of requirement 1 (a manual impl Unpin plus a structural projection to a non-Unpin field), with an exposed witness program for every toy declaration.

**Prior art.** [S1] (requirement 1 and its warning against `impl<T> Unpin for Struct<T> {}` plus a structural projection to `T`, lines 793–800); [S2] (for `T: !Unpin`, `&mut T` access is unsafe because operations like `mem::replace` can move the referent, line 42). Full records under Evidence.

**Design question.** Can a struct declared Unpin offer a structural projection of a non-Unpin field under any other conditions?

Basis: execution (Lean kernel check) — `unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — `unpinWitness i` renders: create, pin, project field `i` structurally, let the field store its address, then `mem::replace` the whole struct through the `&mut S` that `Pin::get_mut` provides for an `Unpin` struct (in Rust this needs `S: Sized`).

Non-claims for R6 are listed under Boundaries.

### R7 `sound-unpin-rules-characterized-on-declarations-satisfying-b-to-f`

Kind: characterization. Tier: T1. Depth: shallow.

Lean statements (verbatim):

```lean
-- ToyPin/Unpin.lean:232-235
theorem soundUnpinRule_iff (r : Decl → Bool) :
    SoundUnpinRule r ↔ ∀ d : Decl, DtorNoMoveOutOfPinned d → DropGuaranteeForPinned d →
      NoPinnedTake d → NotPackedIfPinned d → ProjectionConsistent d → r d = true →
        PinnedFieldsUnpin d := …

-- ToyPin/Unpin.lean:250
theorem pinnedFieldsRule_sound : SoundUnpinRule pinnedFieldsRule := …

-- ToyPin/Unpin.lean:257-260
theorem pinnedFieldsRule_greatest_under_b_to_f (r : Decl → Bool) (hr : SoundUnpinRule r)
    (d : Decl) (hb : DtorNoMoveOutOfPinned d) (hc : DropGuaranteeForPinned d)
    (hd : NoPinnedTake d) (he : NotPackedIfPinned d) (hf : ProjectionConsistent d)
    (h : r d = true) : pinnedFieldsRule d = true := …

-- ToyPin/Unpin.lean:266-270
theorem soundUnpinRule_false_of_grants_structural_nonUnpin (r : Decl → Bool) (d : Decl)
    (hb : DtorNoMoveOutOfPinned d) (hc : DropGuaranteeForPinned d) (hd : NoPinnedTake d)
    (he : NotPackedIfPinned d) (hf : ProjectionConsistent d) (i : Nat)
    (hproj : ApiOp.projPin i ∈ d.api) (hty : d.fieldTy i = false) (h : r d = true) :
    ¬ SoundUnpinRule r := …
```

**Plain claim.** Call a rule r : Decl -> Bool (which may read the whole declaration, including the unpin value it replaces) sound (SoundUnpinRule r) when, for every declaration d satisfying (b)-(f), setting d.unpin := r d makes every program accepted by SafeProgram from State.init keep AddrInv in every visited state. Then: r is sound iff, on every declaration satisfying (b)-(f), r grants Unpin only when every structurally projected field has an Unpin type (soundUnpinRule_iff); pinnedFieldsRule is sound; for every sound r and every declaration d satisfying (b)-(f), r d = true implies pinnedFieldsRule d = true, so on declarations satisfying (b)-(f) pinnedFieldsRule is the most permissive sound rule; and every rule that grants Unpin to some declaration satisfying (b)-(f) that has a structurally projected field of non-Unpin type is not sound.

**Hypothesis ledger.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hr : SoundUnpinRule r (pinnedFieldsRule_greatest_under_b_to_f)` | Maximality is stated among sound rules; an unsound rule can grant Unpin where pinnedFieldsRule does not (pinnedFieldsRule_greatest_hr_tight). | tight | `pinnedFieldsRule_greatest_hr_tight` | the rule 'always Unpin' and the one-field declaration dBase |
| `hb hc hd he hf : (b)-(f) for d (pinnedFieldsRule_greatest_under_b_to_f and soundUnpinRule_false_of_grants_structural_nonUnpin)` | By its definition, SoundUnpinRule constrains rules on declarations satisfying (b)-(f) and on no others; each of the five is tight separately in both theorems. | tight | `ruleResults_b_to_f_tight` | the sound rule permissiveRule and the one-field declarations dB, dC, dD, dE, dF (field 0), each violating exactly one of (b)-(f) |
| `h : r d = true (both theorems)` | The conclusions concern declarations to which the rule grants Unpin. | tight | `ruleResults_h_tight` | the sound rule 'never Unpin' and the one-field declaration dBase (field 0) |
| `hproj : ApiOp.projPin i ∈ d.api (soundUnpinRule_false_of_grants_structural_nonUnpin)` | A structurally projected field of non-Unpin type is what makes granting Unpin unsound on declarations satisfying (b)-(f) (soundUnpinRule_iff). | tight | `soundUnpinRule_false_hproj_tight` | the sound rule pinnedFieldsRule and the two-field declaration dConservative, field 0 |
| `hty : d.fieldTy i = false (soundUnpinRule_false_of_grants_structural_nonUnpin)` | A structurally projected field of Unpin type does not make granting Unpin unsound. | tight | `soundUnpinRule_false_hty_tight` | the sound rule pinnedFieldsRule and the one-field declaration dUnpinField, field 0 |

**Non-vacuity witness.** pinnedFieldsRule (sound) and dConservative (satisfying (b)-(f), granted Unpin) satisfy the hypotheses of pinnedFieldsRule_greatest_under_b_to_f; the rule 'always Unpin', dBase and field 0 satisfy those of soundUnpinRule_false_of_grants_structural_nonUnpin. (`pinnedFieldsRule_greatest_nonvacuous`, `soundUnpinRule_false_nonvacuous`)

**Positive controls.** `alwaysUnpin_unsound`, `pinnedFieldsRule_not_greatest_without_b_to_f`

**Tier.** T1: pin-project derives Unpin from the #[pin] fields only and the documentation allows impl Unpin regardless of non-structural fields; here the rule-level statement is made exact on declarations satisfying (b)-(f).

**Prior art.** [S1] (requirement 1; a struct may `impl Unpin` even if the type of a non-structurally pinned field is not `Unpin`, lines 766–769); [S3] (`Unpin` derived from the `#[pin]` fields, lines 96–108). Full records under Evidence.

**Design question.** Which rules for deriving Unpin from a struct declaration are sound, and is the conjunction over structurally projected fields the most permissive one?

Basis: execution (Lean kernel check) — `soundUnpinRule_iff`, `pinnedFieldsRule_sound`, `pinnedFieldsRule_greatest_under_b_to_f`, `soundUnpinRule_false_of_grants_structural_nonUnpin` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — A rule `r : Decl → Bool` stands for a policy deciding `impl Unpin` from the declaration (an auto-trait-like rule, `pin-project`'s generated bound, or a manual decision). The characterization is about the toy's two invariants and the declarations satisfying (b)–(f).

Non-claims for R7 are listed under Boundaries.

### R8 `auto-unpin-sound-under-b-to-f-and-strictly-conservative-on-one-instance`

Kind: theorem. Tier: T1. Depth: definitional.

Lean statements (verbatim):

```lean
-- ToyPin/Unpin.lean:285
theorem autoUnpin_sound : SoundUnpinRule autoUnpin := …

-- ToyPin/Unpin.lean:53-54
theorem autoUnpin_implies_pinnedFieldsUnpin (d : Decl) (h : autoUnpin d = true) :
    PinnedFieldsUnpin d := …

-- ToyPin/Necessity.lean:205-207
theorem autoUnpin_conservative :
    autoUnpin dConservative = false ∧ PinnedFieldsUnpin dConservative ∧
      dConservative.unpin = true ∧ SafeProgramsKeepAddrInv dConservative := …
```

Unfolded statement of `autoUnpin_sound`, with `SoundUnpinRule` unfolded:

```lean
∀ d : Decl, DtorNoMoveOutOfPinned d → DropGuaranteeForPinned d → NoPinnedTake d →
  NotPackedIfPinned d → ProjectionConsistent d →
    SafeProgramsKeepAddrInv { d with unpin := autoUnpin d }
```

**Plain claim.** For every toy declaration d satisfying (b)-(f), setting d.unpin := autoUnpin d (Unpin iff every field's type is Unpin, as Rust's auto trait computes for a struct without a manual impl) makes every program accepted by SafeProgram from State.init keep AddrInv in every visited state (this is SoundUnpinRule autoUnpin with the definition of SoundUnpinRule substituted); for every declaration d, autoUnpin d = true implies that every structurally projected field has an Unpin type; and for the two-field declaration dConservative, whose only non-Unpin field is offered only through a non-structural projection, autoUnpin refuses Unpin although dConservative, declared Unpin, keeps AddrInv for every program accepted by SafeProgram.

**Hypothesis ledger.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `(b)-(f) for d, inside SoundUnpinRule autoUnpin` | SoundUnpinRule quantifies over the declarations satisfying (b)-(f); each is tight separately. | tight | `autoUnpin_sound_b_to_f_tight`, `autoUnpin_sound_b_to_f_tight_combined` | the one-field declarations dB, dC, dC', dD, dE, dF (each violating exactly one of (b)-(f)), with unpin := autoUnpin X = false. autoUnpin_sound_b_to_f_tight states autoUnpin X = false and the failure of SafeProgramsKeepAddrInv for dB, dC, dD, dE, dF; that the other four of (b)-(f) hold for each witness is in the companion theorems dtorNoMoveOut_tight, dropGuaranteeForPinned_api_tight, dropGuaranteeForPinned_dtor_tight, noPinnedTake_tight, notPacked_tight and projectionConsistent_tight; autoUnpin_sound_b_to_f_tight_combined states all of these conjuncts (including dC') in one theorem |
| `h : autoUnpin d = true (autoUnpin_implies_pinnedFieldsUnpin)` | The conclusion concerns declarations to which autoUnpin grants Unpin; without that, a structurally projected field may have a non-Unpin type. | tight | `autoUnpin_implies_h_tight` | the one-field declaration dBase |

The tightness witness for (b)–(f) spans several theorems: `autoUnpin_sound_b_to_f_tight` states
`autoUnpin X = false` and the failure of `SafeProgramsKeepAddrInv` for `dB`, `dC`, `dD`, `dE`,
`dF`; that each witness satisfies the other four of (b)–(f) is stated in R3's
`dtorNoMoveOut_tight`, `dropGuaranteeForPinned_api_tight`, `dropGuaranteeForPinned_dtor_tight`,
`noPinnedTake_tight`, `notPacked_tight` and `projectionConsistent_tight`;
`autoUnpin_sound_b_to_f_tight_combined` states all of these conjuncts, including `dC'`, in one
theorem.

**Non-vacuity witness.** dUnpinField satisfies (b)-(f) and autoUnpin dUnpinField = true; with unpin := autoUnpin dUnpinField every safe program keeps AddrInv (autoUnpin_true_witness). dConservative is exposed in autoUnpin_conservative, and a non-empty 7-operation program is accepted by SafeProgram dConservative (sound_declarations_nonvacuous). (`autoUnpin_true_witness`, `autoUnpin_conservative`, `sound_declarations_nonvacuous`)

**Tier.** T1: Follows the documentation's remark that a struct may impl Unpin even if a non-structurally pinned field's type is not Unpin; mechanized for the toy model.

**Prior art.** [S1] (lines 766–769, as for R7); [S3] (lines 96–108). Full records under Evidence.

**Design question.** Is the auto-trait rule (all fields Unpin) sound for structs with structural projections, and how much does it give up compared with the pinned-fields rule?

Basis: execution (Lean kernel check) — `autoUnpin_sound`, `autoUnpin_implies_pinnedFieldsUnpin`, `autoUnpin_conservative` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — `autoUnpin` mirrors Rust's auto-trait computation for a struct without a manual impl (all field types `Unpin`); Rust's auto-trait machinery is not modelled beyond this boolean conjunction.

Non-claims for R8 are listed under Boundaries.

### R9 `forget-frame-and-leaked-object-never-dropped-by-safe-continuations`

Kind: theorem. Tier: T1. Depth: shallow.

Lean statements (verbatim):

```lean
-- ToyPin/CoreForget.lean:130-131
theorem forget_preserves_addrInv (st : State) (b : Nat) (h : AddrInv st) :
    AddrInv (applyAct st (.forget b)) := …

-- ToyPin/CoreForget.lean:109-114
theorem forget_frame (st : State) (b : Nat) :
    (∀ l, (applyAct st (.forget b)).leafAt l = st.leafAt l) ∧
      (∀ l, (applyAct st (.forget b)).isPinnedLoc l = st.isPinnedLoc l) ∧
      (∀ c, (applyAct st (.forget b)).isPinned c = st.isPinned c) ∧
      (∀ c, (applyAct st (.forget b)).isLive c = st.isLive c) ∧
      (applyAct st (.forget b)).registry = st.registry := …

-- ToyPin/CoreForget.lean:145-146
theorem forget_respects_contract (st : State) (b : Nat) :
    NoPinnedMove st (.forget b) ∧ DropGuaranteeAct st (.forget b) := …

-- ToyPin/Leak.lean:202-206
theorem leaked_object_never_dropped_or_deallocated (d : Decl) :
    ∀ (rest : List Op) (st : State) (b : Nat), st.isLeaked b = true →
      SafeProgram d st rest →
      Op.drop b ∉ rest ∧
        ∀ s ∈ states st (compile d rest), s.isLive b = st.isLive b ∧ s.isLeaked b = true := …

-- ToyPin/Leak.lean:435-438
theorem unmentioned_object_unchanged (d : Decl) (rest : List Op) (st : State) (b : Nat)
    (hb : b < st.heap.length) (hmention : ∀ op ∈ rest, ¬ op.Mentions b) :
    ∀ s ∈ states st (compile d rest),
      s.heap[b]? = st.heap[b]? ∧ ∀ e ∈ st.registry, e.1.1 = b → e ∈ s.registry := …

-- ToyPin/Leak.lean:463-467
theorem unmentioned_object_leaves_and_entries (d : Decl) (rest : List Op) (st : State)
    (b : Nat) (hb : b < st.heap.length) (hmention : ∀ op ∈ rest, ¬ op.Mentions b) :
    ∀ s ∈ states st (compile d rest),
      (∀ i, s.leafAt (b, i) = st.leafAt (b, i)) ∧
        ∀ e ∈ st.registry, e.1.1 = b → e ∈ s.registry ∧ s.leafAt e.1 = st.leafAt e.1 := …
```

**Plain claim.** (1) For every toy state st and address b: Act.forget b changes no leaf, pinned location, pinned flag, liveness or list entry and satisfies NoPinnedMove and DropGuaranteeAct; if st satisfies AddrInv, so does the state after forget b. (2) For every declaration d, every state st in which the object at b is leaked, and every program rest accepted by SafeProgram d from st (compiled by compile d): rest contains no Op.drop b, and in every visited state the object at b has the liveness it had in st and is still leaked, so Op.drop b (S's struct destructor, struct drop glue, and deallocation of b) never runs; field-level in-place drops of b's fields (Act.dropLeaf, e.g. from Op.assignField) can still occur (forget_does_not_freeze_fields). (3) For every declaration d, every state st with an object at address b, and every program rest none of whose operations mentions b (compiled by compile d; no safety assumption): in every visited state the object at b (its leaves, self-pointers and flags) equals the one in st, and every list entry of st located in b is still present and finds the same leaf. The leaf-level statement of part (3) (unmentioned_object_leaves_and_entries) is a corollary of the object-level one (unmentioned_object_unchanged), with the same hypotheses.

**Hypothesis ledger.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `h : AddrInv st (forget_preserves_addrInv)` | Preservation needs the invariants before the leak. | tight | `forget_preserves_addrInv_h_tight` | the state reached by the 5-action trace coreMoveActs |
| `hleak : st.isLeaked b = true (leaked_object_never_dropped_or_deallocated)` | Without the leaked flag, SafeOp permits Op.drop b on a live object. | tight | `leaked_object_hleak_tight` | dBase, the state after pinAndInit, b = 0, the one-operation continuation [drop 0] |
| `hsafe : SafeProgram d st rest (leaked_object_never_dropped_or_deallocated)` | Unsafe continuations may drop the leaked object. | tight | `leaked_object_hsafe_tight` | dBase, stLeaked, b = 0, the one-operation continuation [drop 0] |
| `hb : b < st.heap.length (unmentioned_object_unchanged)` | An address beyond the heap gets an object at the next allocation. | tight | `unmentioned_object_hb_tight` | State.init, b = 0, the continuation [new] |
| `hmention : ∀ op ∈ rest, ¬ op.Mentions b (unmentioned_object_unchanged)` | Operations on b may change it. | tight | `unmentioned_object_hmention_tight` | dBase, stLeaked, b = 0, the continuation [assignField 0 0] |
| `hb : b < st.heap.length (unmentioned_object_leaves_and_entries)` | An address beyond the heap gets an object, with fresh leaves, at the next allocation. | tight | `unmentioned_leaves_hb_tight` | the one-field declaration dBase, State.init, b = 0, the continuation [new]. Within zero-field declarations the same violation is not a counterexample: for dZero the leaf-level conclusion still holds (unmentioned_leaves_hb_not_tight_on_zero_field) |
| `hmention : ∀ op ∈ rest, ¬ op.Mentions b (unmentioned_object_leaves_and_entries)` | Operations on b may replace its leaves. | tight | `unmentioned_leaves_hmention_tight` | the one-field declaration dBase, stLeaked, b = 0, the continuation [assignField 0 0] |

The leaf-level statement `unmentioned_object_leaves_and_entries` is a corollary of
`unmentioned_object_unchanged` (same hypotheses; its proof applies `unmentioned_object_unchanged`
and reads leaves off the unchanged object). Its hypotheses `hb` and `hmention` are tight in the
class of one-field declarations (witness `dBase`; `unmentioned_leaves_hb_tight`,
`unmentioned_leaves_hmention_tight`). On zero-field declarations a violation of `hb` is not a
counterexample to the corollary: for `dZero` the conclusion of `unmentioned_object_unchanged`
fails while the leaf-level conclusion still holds, because the new object has no fields
(`unmentioned_leaves_hb_not_tight_on_zero_field`). Part (2) concerns `Op.drop b` (the struct
destructor of `S`, the struct drop glue, and the deallocation of `b`); it does not exclude
field-level in-place drops `Act.dropLeaf (b, i)`, which safe continuations can still cause, for
example through `Op.assignField` (`forget_does_not_freeze_fields`).

**Non-vacuity witness.** leakProg on dBase (pin, self-reference, link, forget) is safe and keeps AddrInv; in its final state stLeaked object 0 is leaked, a 5-operation continuation using object 0 again is safe, and a safe 6-operation continuation that never mentions object 0 exists. (`forget_keeps_addrInv_and_blocks_drop`, `leaked_object_nonvacuous`, `unmentioned_object_nonvacuous`)

**Tier.** T1: The documentation and Jung's post state that leaking (mem::forget of a Box) satisfies the drop guarantee because the storage is never freed or reused; made precise for the toy model.

**Prior art.** [S1] (leaking memory satisfies the drop guarantee, lines 584–586); [S5] (`mem::forget` of a pinned box keeps the memory allocated); [S2] (the stricter guarantee allows leaking "unless the memory remains valid for the remainder of the program lifetime", lines 399–403). Full records under Evidence.

**Design question.** Does leaking a pinned value respect the drop guarantee, and what exactly can later safe code still do to the leaked object?

Basis: execution (Lean kernel check) — `forget_preserves_addrInv`, `forget_frame`, `forget_respects_contract`, `leaked_object_never_dropped_or_deallocated`, `unmentioned_object_unchanged`, `unmentioned_object_leaves_and_entries` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — `Op.forget` behaves like `Box::leak` (earlier references survive). Reading part (3) as describing what happens after a value-consuming `mem::forget` of the only owner (no handle to `b` remains) is an interpretation; raw pointers kept by unsafe code are not modelled.

Non-claims for R9 are listed under Boundaries.

### R10 `reuse-without-drop-breaks-list-not-self-reference-on-one-trace`

Kind: counterexample. Tier: T1. Depth: definitional.

Lean statement (verbatim):

```lean
-- ToyPin/CoreForget.lean:224-228
theorem reuse_breaks_list_not_selfRef :
    Always NoPinnedMove State.init coreReuseActs ∧
      ¬ Always DropGuaranteeAct State.init coreReuseActs ∧
      ¬ ListOK (runActs State.init coreReuseActs) ∧
      ∀ s ∈ states State.init coreReuseActs, SelfRefOK s := …
```

**Plain claim.** On the 6-action trace coreReuseActs from State.init (allocate a non-Unpin value, pin its object and field, set its self-pointer, link it into the list, then overwrite its memory without running its destructor): no action moves a pinned non-Unpin value, the final write violates DropGuaranteeAct, ListOK fails in the final state, and SelfRefOK holds in every visited state.

**Hypothesis ledger.**

Hypotheses: none. The theorem is a closed statement about the single named trace `coreReuseActs` run from `State.init`; it has no parameters, so there is no hypothesis to weaken.

**Non-vacuity witness.** Not applicable (closed statement exhibiting coreReuseActs). (`reuse_breaks_list_not_selfRef`)

**Positive controls.** `forget_instead_of_reuse_keeps_addrInv`

**Tier.** T1: The motivating example of the drop guarantee in Jung's intrusive-collections post and in core::pin; the observation that a self-reference alone does not detect the violation on this trace is made precise here.

**Prior art.** [S5] (deallocation of an entry while a collection points to it); [S1] (line 535); [S6] (`ptr::write` without drop in an intrusive list). Full records under Evidence.

**Design question.** Which invariant witnesses a violation of the drop guarantee: would a model with only self-referential values detect it?

Basis: execution (Lean kernel check) — `reuse_breaks_list_not_selfRef` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — `coreReuseActs` is a toy instance of the failure that [S5] and [S6] use to motivate the drop guarantee (memory of a linked entry reused without running its destructor). Which Rust operations (`ptr::write`, `set_len`, stack-frame reuse) correspond to `Act.write` is an interpretation.

Non-claims for R10 are listed under Boundaries.

### R11 `address-sensitive-state-only-at-structurally-projected-fields`

Kind: theorem. Tier: T1. Depth: shallow.

Lean statements (verbatim):

```lean
-- ToyPin/Scope.lean:271-273
theorem addrState_only_at_structurally_projected_fields (d : Decl) (prog : List Op)
    (hsafe : SafeProgram d State.init prog) :
    ∀ s ∈ states State.init (compile d prog), AddrStateAtProjected d s := …

-- ToyPin/Scope.lean:284-288
theorem no_addrState_without_structural_projection (d : Decl)
    (hno : ∀ i, ApiOp.projPin i ∉ d.api) (prog : List Op)
    (hsafe : SafeProgram d State.init prog) :
    ∀ s ∈ states State.init (compile d prog),
      s.registry = [] ∧ ∀ l v, s.leafAt l = some v → v.selfPtr = none := …
```

Unfolded statement of `addrState_only_at_structurally_projected_fields`, with `AddrStateAtProjected` unfolded:

```lean
∀ (d : Decl) (prog : List Op), SafeProgram d State.init prog →
  ∀ s ∈ states State.init (compile d prog),
    (∀ l v, s.leafAt l = some v → ∀ m, v.selfPtr = some m → ApiOp.projPin m.2 ∈ d.api) ∧
      ∀ e ∈ s.registry, ApiOp.projPin e.1.2 ∈ d.api
```

**Plain claim.** For every toy declaration d and every program accepted by SafeProgram d from State.init (compiled by compile d), in every visited state every self-pointer target and every intrusive-list entry is a field location (b, i) with ApiOp.projPin i in d.api; consequently, if d offers no structural projection, every visited state has an empty list and no leaf with a self-pointer. (Locations are field locations; no location denotes a whole struct.)

**Hypothesis ledger.**

| hypothesis | purpose | tightness | counterexample | witness class |
|---|---|---|---|---|
| `hsafe : SafeProgram d State.init prog (both theorems)` | Unsafe programs may pin and use fields that are not structurally projected. | tight | `addrState_hsafe_tight`, `noAddrState_hsafe_tight` | the one-field declaration dNoProj and the 4-operation program pinAndInit. For addrState_only_at_structurally_projected_fields, hsafe is its only hypothesis (addrState_hsafe_tight). For no_addrState_without_structural_projection, the other hypothesis hno : ∀ i, ApiOp.projPin i ∉ dNoProj.api is in the companion theorem noProjection_unpin_vacuously_sound; noAddrState_hsafe_tight states hno, the failure of hsafe and the failure of the conclusion in one theorem |
| `hno : ∀ i, ApiOp.projPin i ∉ d.api (no_addrState_without_structural_projection)` | With a structural projection, a safe program can set a self-pointer. | tight | `noAddrState_hno_tight` | the one-field declaration dBase and the 4-operation program pinAndInit |

The tightness witness for `hsafe` in `no_addrState_without_structural_projection` spans two
theorems: `addrState_hsafe_tight` (the program `pinAndInit` is not safe for `dNoProj` and the
conclusion fails along it) and `noProjection_unpin_vacuously_sound` (which states the other
hypothesis, `∀ i, ApiOp.projPin i ∉ dNoProj.api`); `noAddrState_hsafe_tight` states both in one
theorem.

**Non-vacuity witness.** dRich and progRich (safe; two list entries and a self-pointer are established) for the first theorem; dNoProj (no structural projection, declared Unpin, non-Unpin field) with the safe 5-operation program [new, pin 0, replaceField 0 0, replaceStruct 0, drop 0] for the second. (`structural_nonvacuous`, `noAddrState_nonvacuous_nonempty`, `noProjection_unpin_vacuously_sound`)

**Tier.** T1: Makes precise a scope fact of this toy model that bounds the Unpin results; the corresponding Rust practice (a struct that is itself address-sensitive must be !Unpin) is documented in core::pin and pin-project.

**Prior art.** [S3] (`PhantomPinned` without `#[pin]` has no effect, lines 297–313); [S1] ("Projections and Structural Pinning", lines 696–847). Full records under Evidence.

**Design question.** Where can address-sensitive state live in a struct whose author chooses structural projections, and what does that imply for the scope of the Unpin results?

Basis: execution (Lean kernel check) — `addrState_only_at_structurally_projected_fields`, `no_addrState_without_structural_projection` and every theorem named in this card.

Basis: derived (modeling bridge; model–system relation: none proved) — The theorem is a scope fact about the toy: in it, address-sensitive state can arise only at structurally projected fields. Real types can be address-sensitive as a whole or through private fields used by their own unsafe code; such types are outside the model.

Non-claims for R11 are listed under Boundaries.

### Auxiliary declarations cited by name

The theorems below are named in the cards, hypothesis ledgers, tables, non-claims or model
descriptions (non-vacuity witnesses, tightness counterexamples, definition examples, positive
controls and companion facts) without being quoted elsewhere in this report. Each is quoted
verbatim from its source with its `file:line` range and its proof elided. Every declaration
quoted in this report, here or above, is listed in `results.json` (fields `lean`,
`lean_names`, `nonvacuity_witness_lean`, `positive_control_lean` and the ledger
counterexamples), so its statement and closure hashes are recorded in `audit/statements.json` and
in the kernel-check record under Evidence.

From `ToyPin/Unpin.lean` (the general sufficiency fact for declarations whose structurally projected fields all have `Unpin` types, and two facts about the rules):

```lean
-- ToyPin/Unpin.lean:214-215
theorem sound_of_pinnedFieldsUnpin (d : Decl) (h : PinnedFieldsUnpin d) :
    SafeProgramsKeepAddrInv d := …

-- ToyPin/Unpin.lean:276-277
theorem pinnedFieldsRule_ignores_unpin (d : Decl) (u : Bool) :
    pinnedFieldsRule { d with unpin := u } = pinnedFieldsRule d := …

-- ToyPin/Unpin.lean:280-281
theorem autoUnpin_ignores_unpin (d : Decl) (u : Bool) :
    autoUnpin { d with unpin := u } = autoUnpin d := …
```

From `ToyPin/Necessity.lean` (tightness counterexamples, positive controls and facts about `Unpin` rules):

```lean
-- ToyPin/Necessity.lean:30-33
theorem dBase_satisfies_all :
    UnpinOnlyIfPinnedFieldsUnpin dBase ∧ DtorNoMoveOutOfPinned dBase ∧
      DropGuaranteeForPinned dBase ∧ NoPinnedTake dBase ∧ NotPackedIfPinned dBase ∧
      ProjectionConsistent dBase := …

-- ToyPin/Necessity.lean:213
theorem alwaysUnpin_unsound : ¬ SoundUnpinRule (fun _ => true) := …

-- ToyPin/Necessity.lean:221
theorem rPackedOrPinned_sound : SoundUnpinRule rPackedOrPinned := …

-- ToyPin/Necessity.lean:238-243
theorem pinnedFieldsRule_not_greatest_without_b_to_f :
    SoundUnpinRule rPackedOrPinned ∧
      (∀ d, pinnedFieldsRule d = true → rPackedOrPinned d = true) ∧
      DtorNoMoveOutOfPinned dE ∧ DropGuaranteeForPinned dE ∧ NoPinnedTake dE ∧
      ¬ NotPackedIfPinned dE ∧ ProjectionConsistent dE ∧ dE.PinnedNonUnpinField 0 ∧
      rPackedOrPinned dE = true ∧ pinnedFieldsRule dE = false := …

-- ToyPin/Necessity.lean:253-258
theorem noProjection_unpin_vacuously_sound :
    dNoProj.unpin = true ∧ (∀ i, ApiOp.projPin i ∉ dNoProj.api) ∧ dNoProj.fieldTy 0 = false ∧
      PinnedFieldsUnpin dNoProj ∧ SafeProgramsKeepAddrInv dNoProj ∧
      ∀ prog, SafeProgram dNoProj State.init prog →
        ∀ s ∈ states State.init (compile dNoProj prog),
          s.registry = [] ∧ ∀ l v, s.leafAt l = some v → v.selfPtr = none := …

-- ToyPin/Necessity.lean:272-276
theorem safeProgram_tight :
    UnpinOnlyIfPinnedFieldsUnpin dBase ∧ DtorNoMoveOutOfPinned dBase ∧
      DropGuaranteeForPinned dBase ∧ NoPinnedTake dBase ∧ NotPackedIfPinned dBase ∧
      ProjectionConsistent dBase ∧ ¬ SafeProgram dBase State.init progA ∧
      ¬ ∀ s ∈ states State.init (compile dBase progA), AddrInv s := …

-- ToyPin/Necessity.lean:279
theorem dBase_sound : SafeProgramsKeepAddrInv dBase := …

-- ToyPin/Necessity.lean:286-288
theorem unpin_iff_hu_tight :
    dBase.unpin = false ∧ ¬ (SafeProgramsKeepAddrInv dBase ↔ PinnedFieldsUnpin dBase) ∧
      SafeProgramsKeepAddrInv dBase ∧ ¬ PinnedFieldsUnpin dBase := …

-- ToyPin/Necessity.lean:296-300
theorem unpinWitness_hu_tight :
    dBase.unpin = false ∧ ApiOp.projPin 0 ∈ dBase.api ∧ dBase.fieldTy 0 = false ∧
      ¬ (SafeProgram dBase State.init (unpinWitness 0) ∧
        (∃ s ∈ states State.init (compile dBase (unpinWitness 0)), ¬ SelfRefOK s) ∧
        (∀ s ∈ states State.init (compile dBase (unpinWitness 0)), ListOK s)) := …

-- ToyPin/Necessity.lean:309-316
theorem unpinWitness_fieldTy_tight :
    dUnpinField.unpin = true ∧ ApiOp.projPin 0 ∈ dUnpinField.api ∧
      dUnpinField.fieldTy 0 = true ∧
      SafeProgram dUnpinField State.init (unpinWitness 0) ∧
      (∀ s ∈ states State.init (compile dUnpinField (unpinWitness 0)), AddrInv s) ∧
      ¬ (SafeProgram dUnpinField State.init (unpinWitness 0) ∧
        (∃ s ∈ states State.init (compile dUnpinField (unpinWitness 0)), ¬ SelfRefOK s) ∧
        (∀ s ∈ states State.init (compile dUnpinField (unpinWitness 0)), ListOK s)) := …

-- ToyPin/Necessity.lean:327-334
theorem unpinWitness_projPin_tight :
    dUnpinNonStructural.unpin = true ∧ ApiOp.projPin 0 ∉ dUnpinNonStructural.api ∧
      dUnpinNonStructural.fieldTy 0 = false ∧
      ¬ (SafeProgram dUnpinNonStructural State.init (unpinWitness 0) ∧
        (∃ s ∈ states State.init (compile dUnpinNonStructural (unpinWitness 0)),
          ¬ SelfRefOK s) ∧
        (∀ s ∈ states State.init (compile dUnpinNonStructural (unpinWitness 0)), ListOK s)) ∧
      SafeProgramsKeepAddrInv dUnpinNonStructural := …

-- ToyPin/Necessity.lean:347
theorem permissiveRule_sound : SoundUnpinRule permissiveRule := …

-- ToyPin/Necessity.lean:362-378
theorem ruleResults_b_to_f_tight :
    SoundUnpinRule permissiveRule ∧
    (¬ DtorNoMoveOutOfPinned dB ∧ DropGuaranteeForPinned dB ∧ NoPinnedTake dB ∧
      NotPackedIfPinned dB ∧ ProjectionConsistent dB ∧ ApiOp.projPin 0 ∈ dB.api ∧
      dB.fieldTy 0 = false ∧ permissiveRule dB = true ∧ pinnedFieldsRule dB = false) ∧
    (DtorNoMoveOutOfPinned dC ∧ ¬ DropGuaranteeForPinned dC ∧ NoPinnedTake dC ∧
      NotPackedIfPinned dC ∧ ProjectionConsistent dC ∧ ApiOp.projPin 0 ∈ dC.api ∧
      dC.fieldTy 0 = false ∧ permissiveRule dC = true ∧ pinnedFieldsRule dC = false) ∧
    (DtorNoMoveOutOfPinned dD ∧ DropGuaranteeForPinned dD ∧ ¬ NoPinnedTake dD ∧
      NotPackedIfPinned dD ∧ ProjectionConsistent dD ∧ ApiOp.projPin 0 ∈ dD.api ∧
      dD.fieldTy 0 = false ∧ permissiveRule dD = true ∧ pinnedFieldsRule dD = false) ∧
    (DtorNoMoveOutOfPinned dE ∧ DropGuaranteeForPinned dE ∧ NoPinnedTake dE ∧
      ¬ NotPackedIfPinned dE ∧ ProjectionConsistent dE ∧ ApiOp.projPin 0 ∈ dE.api ∧
      dE.fieldTy 0 = false ∧ permissiveRule dE = true ∧ pinnedFieldsRule dE = false) ∧
    (DtorNoMoveOutOfPinned dF ∧ DropGuaranteeForPinned dF ∧ NoPinnedTake dF ∧
      NotPackedIfPinned dF ∧ ¬ ProjectionConsistent dF ∧ ApiOp.projPin 0 ∈ dF.api ∧
      dF.fieldTy 0 = false ∧ permissiveRule dF = true ∧ pinnedFieldsRule dF = false) := …

-- ToyPin/Necessity.lean:384-388
theorem pinnedFieldsRule_greatest_hr_tight :
    ¬ SoundUnpinRule (fun _ => true) ∧ DtorNoMoveOutOfPinned dBase ∧
      DropGuaranteeForPinned dBase ∧ NoPinnedTake dBase ∧ NotPackedIfPinned dBase ∧
      ProjectionConsistent dBase ∧ (fun _ => true : Decl → Bool) dBase = true ∧
      pinnedFieldsRule dBase = false := …

-- ToyPin/Necessity.lean:392
theorem neverUnpin_sound : SoundUnpinRule (fun _ => false) := …

-- ToyPin/Necessity.lean:400-404
theorem ruleResults_h_tight :
    SoundUnpinRule (fun _ => false) ∧ DtorNoMoveOutOfPinned dBase ∧
      DropGuaranteeForPinned dBase ∧ NoPinnedTake dBase ∧ NotPackedIfPinned dBase ∧
      ProjectionConsistent dBase ∧ ApiOp.projPin 0 ∈ dBase.api ∧ dBase.fieldTy 0 = false ∧
      (fun _ => false : Decl → Bool) dBase = false ∧ pinnedFieldsRule dBase = false := …

-- ToyPin/Necessity.lean:412-417
theorem soundUnpinRule_false_hproj_tight :
    DtorNoMoveOutOfPinned dConservative ∧ DropGuaranteeForPinned dConservative ∧
      NoPinnedTake dConservative ∧ NotPackedIfPinned dConservative ∧
      ProjectionConsistent dConservative ∧ ApiOp.projPin 0 ∉ dConservative.api ∧
      dConservative.fieldTy 0 = false ∧ pinnedFieldsRule dConservative = true ∧
      SoundUnpinRule pinnedFieldsRule := …

-- ToyPin/Necessity.lean:425-430
theorem soundUnpinRule_false_hty_tight :
    DtorNoMoveOutOfPinned dUnpinField ∧ DropGuaranteeForPinned dUnpinField ∧
      NoPinnedTake dUnpinField ∧ NotPackedIfPinned dUnpinField ∧
      ProjectionConsistent dUnpinField ∧ ApiOp.projPin 0 ∈ dUnpinField.api ∧
      dUnpinField.fieldTy 0 = true ∧ pinnedFieldsRule dUnpinField = true ∧
      SoundUnpinRule pinnedFieldsRule := …

-- ToyPin/Necessity.lean:436-439
theorem soundUnpinRule_false_nonvacuous :
    DtorNoMoveOutOfPinned dBase ∧ DropGuaranteeForPinned dBase ∧ NoPinnedTake dBase ∧
      NotPackedIfPinned dBase ∧ ProjectionConsistent dBase ∧ ApiOp.projPin 0 ∈ dBase.api ∧
      dBase.fieldTy 0 = false ∧ (fun _ => true : Decl → Bool) dBase = true := …

-- ToyPin/Necessity.lean:443-444
theorem autoUnpin_implies_h_tight :
    autoUnpin dBase = false ∧ ¬ PinnedFieldsUnpin dBase := …
```

From `ToyPin/CoreForget.lean` (action-level tightness witnesses, the non-necessity facts on single traces, the `pinObj`/`pinField` examples and the `forget` witnesses):

```lean
-- ToyPin/CoreForget.lean:20-22
theorem noPinnedMove_tight :
    Always DropGuaranteeAct State.init coreMoveActs ∧
      ¬ ∀ s ∈ states State.init coreMoveActs, AddrInv s := …

-- ToyPin/CoreForget.lean:32-34
theorem dropGuarantee_tight :
    Always NoPinnedMove State.init coreReuseActs ∧
      ¬ ∀ s ∈ states State.init coreReuseActs, AddrInv s := …

-- ToyPin/CoreForget.lean:49-54
theorem core_nonvacuous :
    Always NoPinnedMove State.init coreNonVacuousActs ∧
      Always DropGuaranteeAct State.init coreNonVacuousActs ∧
      (runActs State.init (coreNonVacuousActs.take 6)).registry ≠ [] ∧
      (runActs State.init (coreNonVacuousActs.take 6)).leafAt (0, 0) =
        some ⟨0, false, some (0, 0)⟩ := …

-- ToyPin/CoreForget.lean:60-63
theorem noPinnedMove_not_necessary_on_a_trace :
    let acts : List Act := [.alloc [some false], .pinObj 0, .pinField (0, 0), .moveOut (0, 0)]
    ¬ Always NoPinnedMove State.init acts ∧ Always DropGuaranteeAct State.init acts ∧
      ∀ s ∈ states State.init acts, AddrInv s := …

-- ToyPin/CoreForget.lean:67-71
theorem dropGuaranteeAct_not_necessary_on_a_trace :
    let acts : List Act :=
      [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0), .write (0, 0) false]
    Always NoPinnedMove State.init acts ∧ ¬ Always DropGuaranteeAct State.init acts ∧
      ∀ s ∈ states State.init acts, AddrInv s := …

-- ToyPin/CoreForget.lean:75-77
theorem safeProgram_not_necessary_for_a_program :
    ¬ SafeProgram dBase State.init [.pin 0] ∧
      ∀ s ∈ states State.init (compile dBase [.pin 0]), AddrInv s := …

-- ToyPin/CoreForget.lean:84-88
theorem pinObj_inert_in_core (st : State) (b : Nat) (l : Loc) :
    (applyAct st (.pinObj b)).leafAt l = st.leafAt l ∧
      (applyAct st (.pinObj b)).isPinnedLoc l = st.isPinnedLoc l ∧
      (applyAct st (.pinObj b)).registry = st.registry ∧
      (PinnedNonUnpin (applyAct st (.pinObj b)) l ↔ PinnedNonUnpin st l) := …

-- ToyPin/CoreForget.lean:99-102
theorem pinField_without_pinObj_protects :
    PinnedNonUnpin (runActs State.init [.alloc [some false], .pinField (0, 0)]) (0, 0) ∧
      (runActs State.init [.alloc [some false], .pinField (0, 0)]).isPinned 0 = false ∧
      ¬ PinnedNonUnpin (runActs State.init [.alloc [some false], .pinObj 0]) (0, 0) := …

-- ToyPin/CoreForget.lean:140-142
theorem forget_preserves_addrInv_h_tight :
    ¬ AddrInv (runActs State.init coreMoveActs) ∧
      ¬ AddrInv (applyAct (runActs State.init coreMoveActs) (.forget 0)) := …

-- ToyPin/CoreForget.lean:153-156
theorem forget_keeps_addrInv_and_blocks_drop :
    SafeProgram dBase State.init leakProg ∧
      (∀ s ∈ states State.init (compile dBase leakProg), AddrInv s) ∧
      ¬ SafeOp dBase (runActs State.init (compile dBase leakProg)) (.drop 0) := …

-- ToyPin/CoreForget.lean:164-166
theorem leaked_object_nonvacuous :
    stLeaked.isLeaked 0 = true ∧
      SafeProgram dBase stLeaked [.link (0, 0), .new, .pin 1, .projPin 1 0, .drop 1] := …

-- ToyPin/CoreForget.lean:172-178
theorem leaked_object_hleak_tight :
    (runActs State.init (compile dBase pinAndInit)).isLeaked 0 = false ∧
      SafeProgram dBase (runActs State.init (compile dBase pinAndInit)) [.drop 0] ∧
      ¬ (Op.drop 0 ∉ [Op.drop 0] ∧
        ∀ s ∈ states (runActs State.init (compile dBase pinAndInit)) (compile dBase [.drop 0]),
          s.isLive 0 = (runActs State.init (compile dBase pinAndInit)).isLive 0 ∧
            s.isLeaked 0 = true) := …

-- ToyPin/CoreForget.lean:183-187
theorem leaked_object_hsafe_tight :
    stLeaked.isLeaked 0 = true ∧ ¬ SafeProgram dBase stLeaked [.drop 0] ∧
      ¬ (Op.drop 0 ∉ [Op.drop 0] ∧
        ∀ s ∈ states stLeaked (compile dBase [.drop 0]),
          s.isLive 0 = stLeaked.isLive 0 ∧ s.isLeaked 0 = true) := …

-- ToyPin/CoreForget.lean:192-197
theorem unmentioned_object_nonvacuous :
    0 < stLeaked.heap.length ∧
      (∀ op ∈ [Op.new, .pin 1, .projPin 1 0, .initSelf (1, 0), .link (1, 0), .drop 1],
        ¬ op.Mentions 0) ∧
      SafeProgram dBase stLeaked
        [.new, .pin 1, .projPin 1 0, .initSelf (1, 0), .link (1, 0), .drop 1] := …

-- ToyPin/CoreForget.lean:202-206
theorem unmentioned_object_hb_tight :
    ¬ (0 < State.init.heap.length) ∧ (∀ op ∈ [Op.new], ¬ op.Mentions 0) ∧
      ¬ ∀ s ∈ states State.init (compile dBase [.new]),
        s.heap[0]? = State.init.heap[0]? ∧
          ∀ e ∈ State.init.registry, e.1.1 = 0 → e ∈ s.registry := …

-- ToyPin/CoreForget.lean:211-215
theorem unmentioned_object_hmention_tight :
    0 < stLeaked.heap.length ∧ ¬ (∀ op ∈ [Op.assignField 0 0], ¬ op.Mentions 0) ∧
      ¬ ∀ s ∈ states stLeaked (compile dBase [.assignField 0 0]),
        s.heap[0]? = stLeaked.heap[0]? ∧
          ∀ e ∈ stLeaked.registry, e.1.1 = 0 → e ∈ s.registry := …

-- ToyPin/CoreForget.lean:232-236
theorem forget_instead_of_reuse_keeps_addrInv :
    let acts : List Act := [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0),
      .register (0, 0), .forget 0]
    Always NoPinnedMove State.init acts ∧ Always DropGuaranteeAct State.init acts ∧
      ∀ s ∈ states State.init acts, AddrInv s := …
```

From `ToyPin/Examples.lean` (definition examples, non-vacuity witnesses and tightness counterexamples):

```lean
-- ToyPin/Examples.lean:18-27
theorem setSelf_requires_pinned_nonUnpin :
    -- unpinned: no effect
    runActs State.init [.alloc [some false], .setSelf (0, 0)] =
      runActs State.init [.alloc [some false]] ∧
    -- pinned but `Unpin`: no effect
    runActs State.init [.alloc [some true], .pinObj 0, .pinField (0, 0), .setSelf (0, 0)] =
      runActs State.init [.alloc [some true], .pinObj 0, .pinField (0, 0)] ∧
    -- pinned and non-`Unpin`: the self-pointer is set
    (runActs State.init [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0)]).leafAt
      (0, 0) = some ⟨0, false, some (0, 0)⟩ := …

-- ToyPin/Examples.lean:30-34
theorem register_requires_pinned_nonUnpin :
    (runActs State.init [.alloc [some false], .register (0, 0)]).registry = [] ∧
    (runActs State.init [.alloc [some true], .pinObj 0, .pinField (0, 0), .register (0, 0)]).registry = [] ∧
    (runActs State.init [.alloc [some false], .pinObj 0, .pinField (0, 0), .register (0, 0)]).registry
      = [((0, 0), 0)] := …

-- ToyPin/Examples.lean:48
theorem selfRefOK_pos : SelfRefOK State.init ∧ SelfRefOK stSelf := …

-- ToyPin/Examples.lean:49
theorem selfRefOK_neg : ¬ SelfRefOK (applyAct stSelf (.moveOut (0, 0))) := …

-- ToyPin/Examples.lean:50
theorem listOK_pos : ListOK State.init ∧ ListOK stLinked := …

-- ToyPin/Examples.lean:51-52
theorem listOK_neg : ¬ ListOK (applyAct stLinked (.write (0, 0) false)) ∧
    ¬ ListOK (applyAct stLinked (.dealloc 0)) ∧ ¬ ListOK (applyAct stLinked (.moveOut (0, 0))) := …

-- ToyPin/Examples.lean:56-57
theorem listOK_after_proper_drop :
    ListOK (runActs stLinked [.dropLeaf (0, 0), .dealloc 0]) := …

-- ToyPin/Examples.lean:58
theorem addrInv_pos : AddrInv stLinked := …

-- ToyPin/Examples.lean:59
theorem addrInv_neg : ¬ AddrInv (applyAct stLinked (.moveOut (0, 0))) := …

-- ToyPin/Examples.lean:63
theorem pinnedNonUnpin_pos : PinnedNonUnpin stSelf (0, 0) := …

-- ToyPin/Examples.lean:64-67
theorem pinnedNonUnpin_neg :
    ¬ PinnedNonUnpin (runActs State.init [.alloc [some false]]) (0, 0) ∧
    ¬ PinnedNonUnpin (runActs State.init [.alloc [some true], .pinObj 0, .pinField (0, 0)]) (0, 0) ∧
    ¬ PinnedNonUnpin (applyAct stSelf (.dropLeaf (0, 0))) (0, 0) := …

-- ToyPin/Examples.lean:69-72
theorem noPinnedMove_pos :
    NoPinnedMove (runActs State.init [.alloc [some false]]) (.moveOut (0, 0)) ∧
    NoPinnedMove (runActs State.init [.alloc [some true], .pinObj 0, .pinField (0, 0)])
      (.moveOut (0, 0)) := …

-- ToyPin/Examples.lean:73-75
theorem noPinnedMove_neg :
    ¬ NoPinnedMove stSelf (.moveOut (0, 0)) ∧ ¬ NoPinnedMove stSelf (.moveObj 0) ∧
    ¬ NoPinnedMove stSelf (.swap (0, 0) (0, 0)) := …

-- ToyPin/Examples.lean:77-79
theorem dropGuaranteeAct_pos :
    DropGuaranteeAct (applyAct stSelf (.dropLeaf (0, 0))) (.dealloc 0) ∧
    DropGuaranteeAct (applyAct stSelf (.dropLeaf (0, 0))) (.write (0, 0) false) := …

-- ToyPin/Examples.lean:83-86
theorem dropGuaranteeAct_neg :
    ¬ DropGuaranteeAct stSelf (.dealloc 0) ∧ ¬ DropGuaranteeAct stSelf (.write (0, 0) true) ∧
      ¬ DropGuaranteeAct stSelf .freeTemp ∧ stSelf.heap.length = 1 ∧
      (applyAct stSelf .freeTemp).isLive 0 = false := …

-- ToyPin/Examples.lean:91
theorem pinnedNonUnpinField_pos : dBase.PinnedNonUnpinField 0 := …

-- ToyPin/Examples.lean:92-94
theorem pinnedNonUnpinField_neg :
    ¬ dBase.PinnedNonUnpinField 1 ∧ ¬ dFUnpin.PinnedNonUnpinField 0 ∧
    ¬ ({ dBase with api := [.projMut 0] } : Decl).PinnedNonUnpinField 0 := …

-- ToyPin/Examples.lean:97-103
theorem conditions_pos_neg :
    (UnpinOnlyIfPinnedFieldsUnpin dBase ∧ ¬ UnpinOnlyIfPinnedFieldsUnpin dA) ∧
    (DtorNoMoveOutOfPinned dBase ∧ ¬ DtorNoMoveOutOfPinned dB) ∧
    (DropGuaranteeForPinned dBase ∧ ¬ DropGuaranteeForPinned dC) ∧
    (NoPinnedTake dBase ∧ ¬ NoPinnedTake dD) ∧
    (NotPackedIfPinned dBase ∧ ¬ NotPackedIfPinned dE) ∧
    (ProjectionConsistent dBase ∧ ¬ ProjectionConsistent dF) := …

-- ToyPin/Examples.lean:112-115
theorem conditions_vacuous_without_pinned_nonUnpin :
    UnpinOnlyIfPinnedFieldsUnpin dPermissive ∧ DtorNoMoveOutOfPinned dPermissive ∧
    DropGuaranteeForPinned dPermissive ∧ NoPinnedTake dPermissive ∧
    NotPackedIfPinned dPermissive ∧ ProjectionConsistent dPermissive := …

-- ToyPin/Examples.lean:122-129
theorem safeOp_pos_neg :
    let st1 := runActs State.init (compile dBase [.new])
    let st2 := runActs State.init (compile dBase [.new, .pin 0])
    SafeOp dBase st1 (.replaceField 0 0) ∧ SafeOp dBase st1 (.replaceStruct 0) ∧
    ¬ SafeOp dBase st2 (.replaceField 0 0) ∧ ¬ SafeOp dBase st2 (.replaceStruct 0) ∧
    ¬ SafeOp dBase st2 (.pin 0) ∧ SafeOp dBase st2 (.projPin 0 0) ∧
    ¬ SafeOp dBase st1 (.projPin 0 0) ∧ ¬ SafeOp dBase st2 (.take 0 0) ∧
    SafeOp dD st2 (.take 0 0) := …

-- ToyPin/Examples.lean:131-134
theorem safeProgram_pos_neg :
    SafeProgram dBase State.init (pinAndInit ++ [.drop 0]) ∧
    ¬ SafeProgram dBase State.init (pinAndInit ++ [.replaceStruct 0]) ∧
    ¬ SafeProgram dBase State.init [.pin 0] := …

-- ToyPin/Examples.lean:155-159
theorem structural_nonvacuous :
    UnpinOnlyIfPinnedFieldsUnpin dRich ∧ DtorNoMoveOutOfPinned dRich ∧
    DropGuaranteeForPinned dRich ∧ NoPinnedTake dRich ∧ NotPackedIfPinned dRich ∧
    ProjectionConsistent dRich ∧ SafeProgram dRich State.init progRich ∧
    (runActs State.init (compile dRich (progRich.take 17))).registry.length = 2 := …

-- ToyPin/Examples.lean:162-163
theorem structural_nonvacuous_conclusion :
    ∀ s ∈ states State.init (compile dRich progRich), AddrInv s := …

-- ToyPin/Examples.lean:169-170
theorem unpin_unsound_nonvacuous :
    dA.unpin = true ∧ ApiOp.projPin 0 ∈ dA.api ∧ dA.fieldTy 0 = false := …

-- ToyPin/Examples.lean:174-176
theorem unpin_iff_nonvacuous :
    dConservative.unpin = true ∧ PinnedFieldsUnpin dConservative ∧
    dA.unpin = true ∧ ¬ PinnedFieldsUnpin dA := …

-- ToyPin/Examples.lean:178-179
theorem pinnedFieldsUnpin_pos_neg :
    PinnedFieldsUnpin dConservative ∧ PinnedFieldsUnpin dFUnpin ∧ ¬ PinnedFieldsUnpin dBase := …

-- ToyPin/Examples.lean:184-188
theorem pinnedFieldsRule_greatest_nonvacuous :
    SoundUnpinRule pinnedFieldsRule ∧ DtorNoMoveOutOfPinned dConservative ∧
      DropGuaranteeForPinned dConservative ∧ NoPinnedTake dConservative ∧
      NotPackedIfPinned dConservative ∧ ProjectionConsistent dConservative ∧
      pinnedFieldsRule dConservative = true := …

-- ToyPin/Examples.lean:194-198
theorem autoUnpin_true_witness :
    autoUnpin dUnpinField = true ∧ DtorNoMoveOutOfPinned dUnpinField ∧
      DropGuaranteeForPinned dUnpinField ∧ NoPinnedTake dUnpinField ∧
      NotPackedIfPinned dUnpinField ∧ ProjectionConsistent dUnpinField ∧
      SafeProgramsKeepAddrInv { dUnpinField with unpin := autoUnpin dUnpinField } := …

-- ToyPin/Examples.lean:205-207
theorem autoUnpin_does_not_rescue_dB :
    autoUnpin dB = false ∧ ¬ DtorNoMoveOutOfPinned dB ∧
      ¬ SafeProgramsKeepAddrInv { dB with unpin := autoUnpin dB } := …

-- ToyPin/Examples.lean:223-228
theorem autoUnpin_sound_b_to_f_tight :
    (autoUnpin dB = false ∧ ¬ SafeProgramsKeepAddrInv { dB with unpin := autoUnpin dB }) ∧
    (autoUnpin dC = false ∧ ¬ SafeProgramsKeepAddrInv { dC with unpin := autoUnpin dC }) ∧
    (autoUnpin dD = false ∧ ¬ SafeProgramsKeepAddrInv { dD with unpin := autoUnpin dD }) ∧
    (autoUnpin dE = false ∧ ¬ SafeProgramsKeepAddrInv { dE with unpin := autoUnpin dE }) ∧
    (autoUnpin dF = false ∧ ¬ SafeProgramsKeepAddrInv { dF with unpin := autoUnpin dF }) := …

-- ToyPin/Examples.lean:251-270
theorem forget_does_not_freeze_fields :
    SafeProgram dUnpinField State.init [.new, .pin 0, .projPin 0 0, .forget 0, .assignField 0 0] ∧
      (runActs State.init (compile dUnpinField [.new, .pin 0, .projPin 0 0, .forget 0])).isLeaked 0
        = true ∧
      (runActs State.init
          (compile dUnpinField [.new, .pin 0, .projPin 0 0, .forget 0, .assignField 0 0])).leafAt
          (0, 0) ≠
        (runActs State.init (compile dUnpinField [.new, .pin 0, .projPin 0 0, .forget 0])).leafAt
          (0, 0) ∧
      SafeProgram dRich State.init
        [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .link (0, 0), .forget 0, .overwrite 0 1] ∧
      (runActs State.init (compile dRich
          [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .link (0, 0), .forget 0])).isLeaked 0
        = true ∧
      (runActs State.init (compile dRich
          [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .link (0, 0), .forget 0,
            .overwrite 0 1])).leafAt (0, 1) ≠
        (runActs State.init (compile dRich
          [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .link (0, 0), .forget 0])).leafAt
          (0, 1) := …

-- ToyPin/Examples.lean:273-274
theorem autoUnpin_pos_neg :
    autoUnpin dFUnpin = true ∧ autoUnpin dConservative = false ∧ autoUnpin dBase = false := …

-- ToyPin/Examples.lean:283-287
theorem addrState_hsafe_tight :
    ¬ SafeProgram dNoProj State.init pinAndInit ∧
      ¬ (∀ s ∈ states State.init (compile dNoProj pinAndInit), AddrStateAtProjected dNoProj s) ∧
      ¬ (∀ s ∈ states State.init (compile dNoProj pinAndInit),
          s.registry = [] ∧ ∀ l v, s.leafAt l = some v → v.selfPtr = none) := …

-- ToyPin/Examples.lean:301-304
theorem noAddrState_hno_tight :
    ¬ (∀ i, ApiOp.projPin i ∉ dBase.api) ∧ SafeProgram dBase State.init pinAndInit ∧
      ¬ (∀ s ∈ states State.init (compile dBase pinAndInit),
          s.registry = [] ∧ ∀ l v, s.leafAt l = some v → v.selfPtr = none) := …
```

From `ToyPin/Companions.lean` (combined tightness witnesses, non-vacuity witnesses and definition examples):

```lean
-- ToyPin/Companions.lean:24-32
theorem addrStateAtProjected_pos_neg :
    SafeProgram dBase State.init (pinAndLink ++ [.initSelf (0, 0)]) ∧
      (runActs State.init (compile dBase (pinAndLink ++ [.initSelf (0, 0)]))).registry =
        [((0, 0), 0)] ∧
      (runActs State.init (compile dBase (pinAndLink ++ [.initSelf (0, 0)]))).leafAt (0, 0) =
        some ⟨0, false, some (0, 0)⟩ ∧
      AddrStateAtProjected dBase
        (runActs State.init (compile dBase (pinAndLink ++ [.initSelf (0, 0)]))) ∧
      ¬ AddrStateAtProjected dNoProj (runActs State.init (compile dNoProj pinAndInit)) := …

-- ToyPin/Companions.lean:46-48
theorem op_mentions_pos_neg :
    (Op.drop 0).Mentions 0 ∧ (Op.swapField 1 0 0).Mentions 0 ∧ (Op.initSelf (0, 2)).Mentions 0 ∧
      ¬ Op.new.Mentions 0 ∧ ¬ (Op.projPin 1 0).Mentions 0 ∧ ¬ (Op.link (1, 0)).Mentions 0 := …

-- ToyPin/Companions.lean:57-59
theorem dFUnpin_nonvacuous :
    SafeProgram dFUnpin State.init
      [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .replaceField 0 0, .drop 0] := …

-- ToyPin/Companions.lean:68-86
theorem autoUnpin_sound_b_to_f_tight_combined :
    (¬ DtorNoMoveOutOfPinned dB ∧ DropGuaranteeForPinned dB ∧ NoPinnedTake dB ∧
      NotPackedIfPinned dB ∧ ProjectionConsistent dB ∧
      autoUnpin dB = false ∧ ¬ SafeProgramsKeepAddrInv { dB with unpin := autoUnpin dB }) ∧
    (DtorNoMoveOutOfPinned dC ∧ ¬ DropGuaranteeForPinned dC ∧ NoPinnedTake dC ∧
      NotPackedIfPinned dC ∧ ProjectionConsistent dC ∧
      autoUnpin dC = false ∧ ¬ SafeProgramsKeepAddrInv { dC with unpin := autoUnpin dC }) ∧
    (DtorNoMoveOutOfPinned dC' ∧ ¬ DropGuaranteeForPinned dC' ∧ NoPinnedTake dC' ∧
      NotPackedIfPinned dC' ∧ ProjectionConsistent dC' ∧
      autoUnpin dC' = false ∧ ¬ SafeProgramsKeepAddrInv { dC' with unpin := autoUnpin dC' }) ∧
    (DtorNoMoveOutOfPinned dD ∧ DropGuaranteeForPinned dD ∧ ¬ NoPinnedTake dD ∧
      NotPackedIfPinned dD ∧ ProjectionConsistent dD ∧
      autoUnpin dD = false ∧ ¬ SafeProgramsKeepAddrInv { dD with unpin := autoUnpin dD }) ∧
    (DtorNoMoveOutOfPinned dE ∧ DropGuaranteeForPinned dE ∧ NoPinnedTake dE ∧
      ¬ NotPackedIfPinned dE ∧ ProjectionConsistent dE ∧
      autoUnpin dE = false ∧ ¬ SafeProgramsKeepAddrInv { dE with unpin := autoUnpin dE }) ∧
    (DtorNoMoveOutOfPinned dF ∧ DropGuaranteeForPinned dF ∧ NoPinnedTake dF ∧
      NotPackedIfPinned dF ∧ ¬ ProjectionConsistent dF ∧
      autoUnpin dF = false ∧ ¬ SafeProgramsKeepAddrInv { dF with unpin := autoUnpin dF }) := …

-- ToyPin/Companions.lean:103-106
theorem noAddrState_hsafe_tight :
    (∀ i, ApiOp.projPin i ∉ dNoProj.api) ∧ ¬ SafeProgram dNoProj State.init pinAndInit ∧
      ¬ (∀ s ∈ states State.init (compile dNoProj pinAndInit),
          s.registry = [] ∧ ∀ l v, s.leafAt l = some v → v.selfPtr = none) := …

-- ToyPin/Companions.lean:112-114
theorem noAddrState_nonvacuous_nonempty :
    (∀ i, ApiOp.projPin i ∉ dNoProj.api) ∧
      SafeProgram dNoProj State.init [.new, .pin 0, .replaceField 0 0, .replaceStruct 0, .drop 0] := …

-- ToyPin/Companions.lean:122-127
theorem unmentioned_leaves_hb_tight :
    ¬ (0 < State.init.heap.length) ∧ (∀ op ∈ [Op.new], ¬ op.Mentions 0) ∧
      ¬ ∀ s ∈ states State.init (compile dBase [.new]),
        (∀ i, s.leafAt (0, i) = State.init.leafAt (0, i)) ∧
          ∀ e ∈ State.init.registry, e.1.1 = 0 →
            e ∈ s.registry ∧ s.leafAt e.1 = State.init.leafAt e.1 := …

-- ToyPin/Companions.lean:137-142
theorem unmentioned_leaves_hmention_tight :
    0 < stLeaked.heap.length ∧ ¬ (∀ op ∈ [Op.assignField 0 0], ¬ op.Mentions 0) ∧
      ¬ ∀ s ∈ states stLeaked (compile dBase [.assignField 0 0]),
        (∀ i, s.leafAt (0, i) = stLeaked.leafAt (0, i)) ∧
          ∀ e ∈ stLeaked.registry, e.1.1 = 0 →
            e ∈ s.registry ∧ s.leafAt e.1 = stLeaked.leafAt e.1 := …

-- ToyPin/Companions.lean:157-165
theorem unmentioned_leaves_hb_not_tight_on_zero_field :
    ¬ (0 < State.init.heap.length) ∧ (∀ op ∈ [Op.new], ¬ op.Mentions 0) ∧
      (¬ ∀ s ∈ states State.init (compile dZero [.new]),
        s.heap[0]? = State.init.heap[0]? ∧
          ∀ e ∈ State.init.registry, e.1.1 = 0 → e ∈ s.registry) ∧
      (∀ s ∈ states State.init (compile dZero [.new]),
        (∀ i, s.leafAt (0, i) = State.init.leafAt (0, i)) ∧
          ∀ e ∈ State.init.registry, e.1.1 = 0 →
            e ∈ s.registry ∧ s.leafAt e.1 = State.init.leafAt e.1) := …

-- ToyPin/Companions.lean:191-203
theorem zero_field_declarations_sound :
    UnpinOnlyIfPinnedFieldsUnpin dZero ∧ DtorNoMoveOutOfPinned dZero ∧
    DropGuaranteeForPinned dZero ∧ NoPinnedTake dZero ∧
    NotPackedIfPinned dZero ∧ ProjectionConsistent dZero ∧
    autoUnpin dZero = true ∧ pinnedFieldsRule dZero = true ∧
    SafeProgramsKeepAddrInv dZero ∧
    UnpinOnlyIfPinnedFieldsUnpin dZeroOutOfBounds ∧ DtorNoMoveOutOfPinned dZeroOutOfBounds ∧
    DropGuaranteeForPinned dZeroOutOfBounds ∧ NoPinnedTake dZeroOutOfBounds ∧
    NotPackedIfPinned dZeroOutOfBounds ∧ ProjectionConsistent dZeroOutOfBounds ∧
    autoUnpin dZeroOutOfBounds = true ∧ pinnedFieldsRule dZeroOutOfBounds = true ∧
    SafeProgramsKeepAddrInv dZeroOutOfBounds ∧
    SafeProgram dZeroOutOfBounds State.init progZero ∧
    (∀ s ∈ states State.init (compile dZeroOutOfBounds progZero), AddrInv s) := …

-- ToyPin/Companions.lean:217-223
theorem sound_declarations_nonvacuous :
    SafeProgram dZero State.init [.new, .pin 0, .replaceStruct 0, .drop 0] ∧
      SafeProgram dConservative State.init
        [.new, .pin 0, .projPin 0 1, .initSelf (0, 1), .replaceField 0 0, .replaceStruct 0,
          .drop 0] ∧
      SafeProgram dUnpinNonStructural State.init
        [.new, .pin 0, .replaceField 0 0, .replaceStruct 0, .drop 0] := …
```

From `ToyPin/EdgeCases.lean` (the temporary-object actions on the empty heap):

```lean
-- ToyPin/EdgeCases.lean:18-20
theorem tempActs_noop_on_empty_heap (st : State) (h : st.heap = []) (i : Nat) :
    st.heap.length - 1 = 0 ∧ applyAct st (.dropTemp i) = st ∧ applyAct st .freeTemp = st ∧
      DropGuaranteeAct st .freeTemp := …
```

From `ToyPin/HeapReading.lean` (reading the heap at out-of-range addresses and field indices):

```lean
-- ToyPin/HeapReading.lean:23-25
theorem heap_reads_at_out_of_range_address (st : State) (l : Loc) (h : st.heap.length ≤ l.1) :
    st.leafAt l = none ∧ st.width l.1 = 0 ∧ st.isLive l.1 = false ∧ st.isPinned l.1 = false ∧
      st.isLeaked l.1 = false ∧ st.isPinnedLoc l = false := …
```

```lean
-- ToyPin/HeapReading.lean:32-35
theorem heap_reads_in_init (l : Loc) :
    State.init.leafAt l = none ∧ State.init.width l.1 = 0 ∧ State.init.isLive l.1 = false ∧
      State.init.isPinned l.1 = false ∧ State.init.isLeaked l.1 = false ∧
      State.init.isPinnedLoc l = false := …
```

```lean
-- ToyPin/HeapReading.lean:39-40
theorem Obj.leaf_of_out_of_range (o : Obj) (i : Nat) (h : o.fields.length ≤ i) :
    o.leaf i = none := …
```

```lean
-- ToyPin/HeapReading.lean:45-46
theorem leafAt_of_out_of_range_field (st : State) (l : Loc) (h : st.width l.1 ≤ l.2) :
    st.leafAt l = none := …
```

```lean
-- ToyPin/HeapReading.lean:55-56
theorem pinnedNonUnpin_in_range (st : State) (l : Loc) (h : PinnedNonUnpin st l) :
    l.1 < st.heap.length ∧ l.2 < st.width l.1 := …
```

```lean
-- ToyPin/HeapReading.lean:66-74
theorem isPinnedLoc_at_out_of_range_field :
    SafeProgram dZeroOutOfBounds State.init [.new, .pin 0, .projPin 0 0] ∧
      (runActs State.init (compile dZeroOutOfBounds [.new, .pin 0, .projPin 0 0])).width 0 = 0 ∧
      (runActs State.init (compile dZeroOutOfBounds [.new, .pin 0, .projPin 0 0])).leafAt
        (0, 0) = none ∧
      (runActs State.init (compile dZeroOutOfBounds [.new, .pin 0, .projPin 0 0])).isPinnedLoc
        (0, 0) = true ∧
      ¬ PinnedNonUnpin
        (runActs State.init (compile dZeroOutOfBounds [.new, .pin 0, .projPin 0 0])) (0, 0) := …
```

From `ToyPin/Unpin.lean` (`Act.pinField` sets `isPinnedLoc` at any field index of an existing object):

```lean
-- ToyPin/Unpin.lean:81-82
theorem isPinnedLoc_pinField_self (st : State) (l : Loc) (h : l.1 < st.heap.length) :
    (applyAct st (.pinField l)).isPinnedLoc l = true := …
```

## Boundaries

Non-claims come first, per result; then escape hatches, the tightness status of every
hypothesis, open questions, and disproved or dropped statements.

### Non-claims

Applying to every result:

* These are statements about the toy model (model–system relation: none proved); they neither
  establish nor refute the corresponding claims about Rust's `Pin` API, the Rust standard library, the Rust compiler, or the
  `pin-project` crate. Each reading of a toy definition as a Rust concept is a modeling bridge
  (`derived`), not a theorem.
* "Breaks an invariant" means that a stale pointer exists in the toy state. No claim is made
  about undefined behaviour under any Rust aliasing model.
* "Safe program" means a program accepted by the generator `SafeProgram d` (from the stated
  state, compiled by `compile d`). The safe API is closed: safe code can do exactly the `Op`
  constructors, `S`'s own operations are the four `ApiOp` forms, and its destructor is a list of
  the two `DtorOp` forms. Programs outside this generator (arbitrary unsafe code, other
  operations) are not covered.

**R1** (`core-no-move-and-drop-guarantee-keep-address-invariants`):

* These are statements about the toy model (model–system relation: none proved); they neither establish nor refute the corresponding claims about Rust's Pin API, the Rust standard library or the Rust compiler. Actions, invariants and states are a toy; the readings 'NoPinnedMove = no &mut to a pinned non-Unpin value is used to move it' and 'DropGuaranteeAct = the documented drop guarantee' are modeling bridges (derived), not theorems.
* The informal form 'no &mut to a pinned non-Unpin value is ever produced' is not the hypothesis. On one 6-operation program, producing a non-structural &mut and using it only to assign in place (drop, then write) keeps both invariants (projection_inconsistent_assign_harmless); no general statement about move-free uses of &mut is proved here.
* hmove and hdrop are tight for this universally quantified theorem, with one-object, one-field witness traces (noPinnedMove_tight, dropGuarantee_tight); in particular 'no moves' alone does not suffice (dropGuarantee_tight). They are not necessary on an individual trace: moving a pinned non-Unpin value that never stored its address or linked itself, or overwriting one that only set a self-pointer, keeps AddrInv on that trace (noPinnedMove_not_necessary_on_a_trace, dropGuaranteeAct_not_necessary_on_a_trace).
* 'Pinned' means that pinField has run on that field location. Pinning an object (Act.pinObj) by itself protects none of its fields under NoPinnedMove or DropGuaranteeAct, and pinField protects a field even if the object was never pinned (pinObj_inert_in_core, pinField_without_pinObj_protects); SafeOp, not the primitive actions, requires the object to be pinned before a structural projection.
* Built-in modeling assumption, not a hypothesis: self-pointers and list entries are established only at a pinned field location holding a non-Unpin value (setSelf and register are no-ops otherwise). Types that rely on their address while being Unpin, or that set up such reliance before being pinned, are outside the model.
* Two address-sensitive invariants are modelled: a field location's value pointing to that same location, and one external list holding field locations. Pointers from one field to a sibling field of the same struct (as in compiler-generated async state machines), pointers between distinct values, interior pointers and pointer arithmetic are not modelled.
* dropTemp and freeTemp act on the most recently allocated object whatever its origin (address heap.length - 1 with truncated subtraction; on the empty heap both are no-ops, tempActs_noop_on_empty_heap); on a heap whose last object is a pinned non-Unpin value, freeTemp is excluded by hdrop (dropGuaranteeAct_neg).
* Starts from the empty heap; no claim for arbitrary initial states.
* No claim about undefined behaviour under any Rust aliasing model: 'invariant broken' means a stale pointer exists in the toy state.

**R2** (`structural-pinning-sound-under-six-conditions`):

* (a)-(e) alone are not sufficient in this model (conditions_a_to_e_insufficient): for the one-field declaration dF a non-structural &mut to the structurally projected field lets mem::swap move it.
* The conditions constrain only structurally projected fields whose type is not Unpin; for Unpin fields they hold vacuously (conditions_vacuous_without_pinned_nonUnpin). For a generic field type T, a library must meet them for non-Unpin instantiations, which gives the documentation's unqualified requirements; this generic reading is a modeling bridge, not proved.
* 'Structurally pinned field' means exactly ApiOp.projPin i in d.api. Self-pointers and list entries arise only at such fields (addrState_only_at_structurally_projected_fields). Private fields whose address S's own unsafe code relies on without offering a structural projection, and pointers between sibling fields, are outside the model.
* Field alignment is not modelled: dPermissive is packed, has a structurally projected field of Unpin type and satisfies (a)-(f), whereas in Rust taking a reference to a possibly unaligned field of a #[repr(packed)] struct is rejected or undefined behaviour and core::pin says pinning cannot be used with packed types (pin.rs lines 630-633) (modeling bridge).
* Soundness for Unpin fields relies on the built-in modeling assumption that Unpin values never establish self-pointers or list entries (Act.setSelf and Act.register are no-ops on them).
* The safe API is closed: safe code can do exactly the Op constructors; S's own operations are the four ApiOp forms (take and overwrite are callable whether or not the object is pinned, which only adds programs) and its destructor is a list of the two DtorOp forms (move a field out; overwrite a field without drop). Destructors that drop a field in place and then reuse its storage, and arbitrary unsafe-implemented APIs (e.g. RefCell-like get_pin_mut plus borrow_mut), are covered insofar as they reduce to these forms and are not covered otherwise.
* After Op.forget b, references to b stay usable in this model (closer to Box::leak than to mem::forget); see forget-frame-and-leaked-object-never-dropped-by-safe-continuations.
* One struct type, one level of fields (no nested structural pinning), a field is either empty or occupied (no general enums), no shared pinning (Pin<&S>), no interior mutability, no panics or unwinding, no concurrency.
* Values moved out by replaceField/take are dropped immediately; packed drop glue is modelled as moving every field to a fresh temporary; which fields a real compiler moves is not examined.
* Not a soundness proof for pin-project, the standard library, or any crate.

**R3** (`each-structural-pinning-condition-tight-with-one-field-witness`):

* These theorems establish tightness of (a)-(f) in addrInv_of_structural_pinning_conditions within the class of one-field declarations and programs of at most six operations; they do not prove the universal converses (for every d, SafeProgramsKeepAddrInv d implies the condition) (not proved here), and they do not enumerate all exploitations.
* Condition (c) is invisible to the self-reference invariant on its witness: with only a self-reference the same overwrite keeps both invariants (dropGuaranteeForPinned_invisible_to_selfRef). A model with only self-referential values would make (c) look unneeded.
* Escape hatches that defeat the witnesses: if the projected field's type is Unpin, or ApiOp.projPin i is not offered, all six conditions hold vacuously (conditions_vacuous_without_pinned_nonUnpin and the definition of Decl.PinnedNonUnpinField); if the object is leaked instead of dropped, the destructor-triggered failures (b), (c)-destructor and (e) do not occur on it (leaked_object_never_dropped_or_deallocated).
* 'Breaks an invariant' means a stale pointer in the toy state; no claim that the corresponding Rust program has undefined behaviour under a particular aliasing model.
* The packed witness models the compiler moving the field before dropping it; whether a particular compiler version moves a particular (aligned) field is not examined.

**R4** (`conditions-a-to-e-insufficient-without-projection-consistency`):

* projection_inconsistent_assign_harmless checks a single program; that every move-free use of the non-structural &mut is harmless is not proved here.
* projection_inconsistent_unpin_field_sound checks the single declaration dFUnpin. The general fact that every declaration whose structurally projected fields all have Unpin types keeps AddrInv for every safe program, whatever projections it also offers, is sound_of_pinnedFieldsUnpin; nothing is claimed for structurally projected non-Unpin fields beyond conditions_a_to_e_insufficient.
* In safe Rust, a public fn(Pin<&mut S>) -> &mut F for F: Sized + !Unpin lets any caller use mem::swap or mem::replace; restricting mutation to drop-then-write requires keeping &mut F encapsulated in an operation such as Pin::set (modeling bridge, not proved).
* Interior mutability (the documentation's RefCell example) is not modelled; the modelled case is the direct one, with two projections of the same field.

**R5** (`unpin-sound-iff-pinned-fields-unpin`):

* Scope boundary: in this model a location is a field location (b, i); no location denotes a whole struct, so the struct itself never holds a self-pointer or list entry, and every self-pointer target and list entry created by a safe program lies at a field index with an offered structural projection (addrState_only_at_structurally_projected_fields). A declaration with no structural projection therefore satisfies PinnedFieldsUnpin vacuously and keeps AddrInv for every safe program whatever its unpin value, because it never has any address-sensitive state (sound_of_pinnedFieldsUnpin, no_addrState_without_structural_projection; instance noProjection_unpin_vacuously_sound).
* Do not apply this to conclude that a Rust type that is itself address-sensitive may implement Unpin, for example a self-referential leaf type with no projecting methods, or a #[pin_project] struct whose PhantomPinned marker lacks #[pin] (pin-project documents that PhantomPinned without #[pin] has no effect, lib.rs lines 297-313). Such types are outside the model; for them Unpin must be suppressed (modeling bridge).
* A declared-Unpin struct may not offer a structural projection of a non-Unpin field, whatever the other conditions: unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field gives a breaking safe program for every such declaration.
* The 'if' direction says nothing about structurally projected non-Unpin fields because, under its hypothesis, there are none; it is not a sufficient-conditions theorem for pinning such fields (see addrInv_of_structural_pinning_conditions).
* Relies on the built-in modeling assumption that Unpin values never establish self-pointers or list entries.
* Unpin is a single boolean of the declaration. For a generic struct S<T> with impl<T: Unpin> Unpin for S<T>, the vacuity of (b)-(f) applies only to instantiations with T: Unpin; S<T> must still meet (b)-(f) for non-Unpin T (modeling bridge, not proved). Negative impls and UnsafeUnpin-style manual impls are not modelled beyond that boolean.
* Field alignment is not modelled: a packed declaration whose structurally projected fields all have Unpin types satisfies PinnedFieldsUnpin (dPermissive is packed, declared Unpin, and its only structurally projected field is Unpin), whereas in Rust taking a reference to a possibly unaligned field of a #[repr(packed)] struct is rejected or undefined behaviour and core::pin says pinning cannot be used with packed types (pin.rs lines 630-633) (modeling bridge).

**R6** (`unpin-with-structural-non-unpin-field-witness-breaks-self-reference`):

* Does not show that every program over such a declaration misbehaves; one witness program per declaration and field.
* Escape hatches that defeat the conclusion: (1) offering field i through a non-structural projection and not through a structural one (dUnpinNonStructural is then sound for every safe program, unpinWitness_projPin_tight; also dConservative, autoUnpin_conservative); (2) not declaring S Unpin (dBase_sound, unpinWitness_hu_tight); (3) field i having an Unpin type (unpinWitness_fieldTy_tight), under the built-in assumption that Unpin values establish no address-sensitive state; (4) in Rust, a whole-struct mem::replace needs S: Sized, so unsized structs escape this witness (not modelled; modeling bridge).
* Field types are concrete booleans; structs whose Unpin depends on generic parameters are not modelled.

**R7** (`sound-unpin-rules-characterized-on-declarations-satisfying-b-to-f`):

* Off the (b)-(f) domain SoundUnpinRule imposes no constraint, so pinnedFieldsRule is not the most permissive sound rule over all declarations: rPackedOrPinned and permissiveRule are sound and grant Unpin to declarations violating (b)-(f) that pinnedFieldsRule refuses (pinnedFieldsRule_not_greatest_without_b_to_f, ruleResults_b_to_f_tight).
* Nothing is claimed about which unpin value, if any, makes a declaration violating (b)-(f) sound; for the witnesses dB, dC, dC', dD, dE, dF (each with unpin = false) some safe program breaks AddrInv (the _tight theorems of each-structural-pinning-condition-tight-with-one-field-witness).
* Rules may read the whole declaration, including the unpin value they replace; pinnedFieldsRule and autoUnpin do not read it (pinnedFieldsRule_ignores_unpin, autoUnpin_ignores_unpin). Rules that depend on information outside the declaration are not considered.
* Scope boundary: self-pointers and list entries arise only at field locations with an offered structural projection; no location denotes a whole struct, so the struct itself is never address-sensitive in this model (addrState_only_at_structurally_projected_fields). A declaration without structural projections keeps AddrInv for every safe program whatever its unpin value (sound_of_pinnedFieldsUnpin; instance noProjection_unpin_vacuously_sound). Do not conclude that a Rust type that is itself address-sensitive (a self-referential leaf type, or a #[pin_project] struct whose PhantomPinned marker lacks #[pin]) may implement Unpin: such types are outside the model, and for them refusing Unpin is required, not conservative (modeling bridge).
* Does not describe Rust's auto-trait machinery; autoUnpin is a toy rule mirroring it (modeling bridge).

**R8** (`auto-unpin-sound-under-b-to-f-and-strictly-conservative-on-one-instance`):

* autoUnpin does not repair declarations violating (b)-(f): for dB, dC, dC', dD, dE, dF, autoUnpin refuses Unpin and some safe program still breaks AddrInv (autoUnpin_sound_b_to_f_tight, autoUnpin_sound_b_to_f_tight_combined, autoUnpin_does_not_rescue_dB).
* Strict conservativeness is shown on the one declaration dConservative; it is relative to the two invariants of this model, and a type may have other reasons to stay !Unpin.
* Scope boundary: self-pointers and list entries arise only at field locations with an offered structural projection; no location denotes a whole struct, so the struct itself is never address-sensitive in this model (addrState_only_at_structurally_projected_fields). A declaration without structural projections keeps AddrInv for every safe program whatever its unpin value (sound_of_pinnedFieldsUnpin; instance noProjection_unpin_vacuously_sound). Do not conclude that a Rust type that is itself address-sensitive (a self-referential leaf type, or a #[pin_project] struct whose PhantomPinned marker lacks #[pin]) may implement Unpin: such types are outside the model, and for them refusing Unpin is required, not conservative (modeling bridge).
* Does not claim Rust's auto trait is exactly autoUnpin (modeling bridge).

**R9** (`forget-frame-and-leaked-object-never-dropped-by-safe-continuations`):

* In this model Op.forget leaves references usable (closer to Box::leak than to a value-consuming mem::forget): after forget b, safe continuations may still assign, replace or overwrite fields of b where SafeOp allows it, also for declarations satisfying (a)-(f) (forget_does_not_freeze_fields, on dUnpinField and dRich). Part (2) therefore says that Op.drop b (struct destructor, struct drop glue, deallocation) never runs, not that b's contents are frozen: a field of b can still be dropped in place (Act.dropLeaf) and rewritten.
* Part (3) does not assume ListOK at st; the entries it preserves are valid at the end exactly when they were valid at st. Reading part (3) as the continuations available after a value-consuming mem::forget of the only owner (which leaves safe code no handle to b) is a modeling bridge; raw pointers kept by unsafe code are not modelled.
* Forgetting a Pin<&mut T> to a stack-pinned value, which in Rust does not leak the value, is not modelled; the model's forget always leaks the object.
* Does not claim that leaking is free of other costs (memory leak) or preserves other invariants.

**R10** (`reuse-without-drop-breaks-list-not-self-reference-on-one-trace`):

* One trace; no general statement that reuse without drop always breaks ListOK or never breaks SelfRefOK is proved here (the one-field (c) witnesses dropGuaranteeForPinned_api_tight and dropGuaranteeForPinned_dtor_tight show the same pattern for two safe programs).
* SelfRefOK survives because the self-pointer lives inside the overwritten value itself. With a pointer from one field to a sibling field of the same struct (not modelled), overwriting or deallocating the target field without running the struct's destructor would leave that pointer dangling without any external list (not proved here).
* Does not say memory reuse is harmless for self-referential values in Rust: a real value may be referenced from elsewhere (wakers, other structures).
* Reuse is a primitive write action; which Rust operations (ptr::write, set_len, stack frame reuse) correspond to it is a modeling bridge.

**R11** (`address-sensitive-state-only-at-structurally-projected-fields`):

* This is a statement about the toy model (model–system relation: none proved); it neither establishes nor refutes the corresponding claim about Rust. Real types can be address-sensitive as a whole (a self-referential leaf type) or through private fields used by their own unsafe code; such types are outside the model, and the Unpin results of this package do not apply to them (modeling bridge).
* The theorems locate address-sensitive state; they say nothing about whether it stays valid (that is addrInv_of_structural_pinning_conditions).
* Relies on the built-in assumption that setSelf and register act only at pinned field locations holding non-Unpin values.

### Escape hatches

Hypotheses or settings that, when dropped or changed, defeat the impossibility and
counterexample results:

* **R6** (a declared-`Unpin` struct with a structurally projected non-`Unpin` field admits a
  breaking safe program): offering field `i` through a non-structural projection and not through a structural
  one (`dUnpinNonStructural` keeps `AddrInv` for every safe program, `unpinWitness_projPin_tight`;
  also `dConservative`, `autoUnpin_conservative`); not declaring `S` `Unpin` (`dBase_sound`,
  `unpinWitness_hu_tight`); giving field `i` an `Unpin` type (`unpinWitness_fieldTy_tight`),
  under the built-in assumption that `Unpin` values establish no address-sensitive state. In
  Rust a whole-struct `mem::replace` needs `S: Sized`, so unsized structs escape this witness
  (not modelled; modeling bridge).
* **R3** (each of (a)–(f) is tight with a one-field witness): if the projected field's type is
  `Unpin`, or `ApiOp.projPin i` is not offered, all six conditions hold vacuously
  (`conditions_vacuous_without_pinned_nonUnpin`, and the definition of
  `Decl.PinnedNonUnpinField`); if the object is leaked instead of dropped, the
  destructor-triggered failures for (b), (c) via the destructor, and (e) do not occur on it
  (`leaked_object_never_dropped_or_deallocated`).
* **R4** (`dF` satisfies (a)–(e) and admits a breaking safe program): giving the field an
  `Unpin` type (`dFUnpin`, `projection_inconsistent_unpin_field_sound`); on `dF`, using the
  non-structural `&mut F` only to assign in place keeps `AddrInv` on the one program checked
  (`projection_inconsistent_assign_harmless`; no general statement is proved).
* **R10** (reuse without drop breaks `ListOK` on `coreReuseActs`): leaking instead of reusing
  keeps `AddrInv` (`forget_instead_of_reuse_keeps_addrInv`).

### Tightness status

Every hypothesis in every ledger is `tight`: for each there is a fully proved Lean theorem
exhibiting an instance, in the recorded witness class, that satisfies all the other hypotheses
of the theorem and in which its conclusion fails. Where that statement is spread over several
theorems, the ledger names every companion (R8, R11). No hypothesis is labelled `harmless` or
`unknown`. Tightness is relative to the stated witness class and to the universally quantified
theorem; it is not necessity on an individual trace or program: on single traces or programs
the hypotheses can fail while the invariants hold (`noPinnedMove_not_necessary_on_a_trace`,
`dropGuaranteeAct_not_necessary_on_a_trace`, `safeProgram_not_necessary_for_a_program`). The
hypothesis `hb` of the corollary `unmentioned_object_leaves_and_entries` is tight among
one-field declarations but not among zero-field declarations
(`unmentioned_leaves_hb_not_tight_on_zero_field`).

### Open questions and cases not examined

* **unknown:** whether, for declarations satisfying (a)–(f), the fields of a leaked object that
  hold pinned non-`Unpin` values stay unchanged under every safe continuation (not proved
  here; `forget_does_not_freeze_fields` shows that other fields of a leaked object do change).
* **unknown:** the universal converses of R2 (for every declaration `d`, every safe program for
  `d` keeping `AddrInv` implies a given condition among (a)–(f)) (not proved here). R3 shows
  tightness through one-field witnesses; it does not prove these converses.
* **not examined:** generic declarations, nested structural pinning, enums, shared pinning
  (`Pin<&T>`), interior mutability (the documentation's `RefCell` example), panics and
  unwinding, concurrency, field alignment, pointers between sibling fields or between distinct
  values, and which fields a particular compiler version moves in packed drop glue.
* **not examined:** the content of the 2019 talk [S10]; the treatment of `core::pin` in [S9];
  the venue of [S8].

### Disproved or dropped statements

None. Every statement this package makes about `Toy.Pin` is a proved theorem, and none is
recorded as disproved; the open questions are listed above. The negative results of the package
are themselves proved theorems, not refuted conjectures:

* `conditions_a_to_e_insufficient`: the one-field declaration `dF` satisfies (a)–(e), `progF` is
  a safe program for `dF` along which `SelfRefOK` fails, and not every safe program for `dF`
  keeps `AddrInv`;
* `pinnedFieldsRule_not_greatest_without_b_to_f`: the sound rule `rPackedOrPinned` grants `Unpin`
  wherever `pinnedFieldsRule` does, and also to `dE`, which satisfies (b), (c), (d) and (f),
  violates (e), and is refused by `pinnedFieldsRule`;
* `forget_does_not_freeze_fields`: on `dUnpinField`, after `forget 0` a safe `assignField 0 0`
  changes the value in field 0 of the leaked object;
* the tightness counterexamples named in the hypothesis ledgers.

The theorems in `ToyPin/Companions.lean` restate facts spread over several theorems as single
conjunctions, or give definition examples and non-vacuity witnesses.

## Evidence

All evidence was acquired on 2026-11-21: the Lean build and axiom audit, the statement hashes,
and every source below (fetched and read at the cited revision or URL on that date).

### Toolchain and build

* Lean 4 `v4.34.1`: repository `leanprover/lean4`, tag `v4.34.1`, commit
  `5045d0056413266e57c625dcd7c365b10e377c52`. No Mathlib; no Lake dependencies.
* Lake project `lean/` (`lakefile.toml`: one `[[lean_lib]]` named `ToyPin`; `lean-toolchain`:
  `leanprover/lean4:v4.34.1`). Modules: `ToyPin.Model`, `Lemmas`, `Core`, `Structural`,
  `Soundness`, `Scope`, `Leak`, `Unpin`, `Necessity`, `CoreForget`, `Examples`, `Companions`,
  `EdgeCases`, `HeapReading`.
* `lake build` succeeds from a clean copy with Lake's artifact cache disabled, so every proof is
  re-elaborated and kernel-checked. The sources contain no `sorry`, `admit`, `native_decide`,
  `axiom` or `opaque` declaration, `implemented_by`, `extern` or `unsafe`.
* Axiom audit (`Lean.collectAxioms` over every declaration of the library, recorded in
  `audit/axioms.json`): all 857 declarations depend on at most `propext`, `Classical.choice`
  and `Quot.sound`.

### Kernel-check record

Basis: execution (Lean kernel check). One row per declaration referenced by `results.json`:
first the 75 theorems in the card roles (result, non-vacuity witness, counterexample, positive
control), then the 150 declarations listed in `lean_names` (50 theorems and 100
definitions, structures and inductive types). The statement hash is the SHA-256 of Lean's `repr`
of the declaration's type; the closure hash is the SHA-256 of the sorted, newline-joined texts
`name : type := value` of every package constant reachable from that type (theorem bodies
excluded); both are recorded in `audit/statements.json`, and `support/revalidate.py` recomputes
them.

| theorem | used as | axioms | statement SHA-256 | closure SHA-256 (closure size) |
|---|---|---|---|---|
| `addrInv_of_noPinnedMove_of_dropGuarantee` | R1 result | Classical.choice, Quot.sound, propext | `da3e91ea99753c456d34d39a03f1c3b5c9e03a4de89f7beb26b8808d18c17815` | `fb6926374d279d3867aac5a0085530165f8a8c09e2022251d4ea50536b72da08` (74) |
| `core_nonvacuous` | R1 non-vacuity | Quot.sound, propext | `9735ef6d6b42840ebb3e41835a361527c0740a175778e6358672722edf99cd49` | `4f92117a3d161beec65008f5038ca03a39149704ad79deb8bc85a20e1952e2a4` (71) |
| `noPinnedMove_tight` | R1 counterexample (hmove) | Quot.sound, propext | `1ca6f9fa8df85b24fbf847c6568d5cfd020be3148ff20edeb24bc12aa0426887` | `4bf51da5c2525c286970a682883b29ba978b223dc07f2cf588e5135715b50edf` (72) |
| `dropGuarantee_tight` | R1 counterexample (hdrop) | Quot.sound, propext | `212f9b61d4d162e681aef94e298b40020555461c6d8ceb1d73bac4ba7ecb972b` | `38f0a5e676b3ef9cb27701790abdff41b093e1f88ac8ba8cdc0864aaa25ffeb6` (72) |
| `addrInv_of_structural_pinning_conditions` | R2 result | Classical.choice, Quot.sound, propext | `2914c320ccf055c4d4fd800dae65b04b034c62ffd1dd324b7c37818f2c7af5e8` | `b23952b8a3db80f757e2de5bdd65d4e2f60dfd12f220358b588c312584d42443` (124) |
| `structural_nonvacuous` | R2 non-vacuity; R11 non-vacuity | Quot.sound, propext | `1c12cbb06560ae5711980097e9e46d4e11f3c0378b8eca1ddfde3d00291e52cc` | `407aebfde48151c34e62da3c520f3d47fdb2fe8994bd5425d57594c5523a07f8` (120) |
| `unpinOnlyIf_tight` | R2 counterexample (ha); R3 result; R3 non-vacuity | Quot.sound, propext | `b85bedfa3b31de4d898bc1d4f3b032306479226bbc61a44c1e8b12eca6907212` | `a4f99a5fb57f25a94a42cdffb19fd47871561670a7ede23d4eb6c83f6b4e8cec` (128) |
| `dtorNoMoveOut_tight` | R2 counterexample (hb); R3 result | Quot.sound, propext | `65adc9c61d1f92ba3e2cef044c3a3dc025263f72db4f46a193d5b946cdab0996` | `21eddec4d42b0c62dec6f58935ac9bda55e1f5e25ef3731ad9d11dc7d949ba65` (128) |
| `dropGuaranteeForPinned_api_tight` | R2 counterexample (hc); R3 result | Quot.sound, propext | `69bf9ae0009e069024f50e5f6efbfad430b30e4e77a14464cf8d70857af2b2ca` | `0a9d5dc4648c22883c9f84c9febd97bfcbde9f68e65369e9ce4d263fd5af2572` (128) |
| `dropGuaranteeForPinned_dtor_tight` | R2 counterexample (hc); R3 result | Quot.sound, propext | `929323887301894b8b359b096e77a0d115cebe24fbdd44bf59fb24f9016ea837` | `436ae08d79c5b633495405374181a921294063876f5b37bd6e82fb2a952649ba` (128) |
| `noPinnedTake_tight` | R2 counterexample (hd); R3 result | Quot.sound, propext | `2e72410c38fcb90f7cdb832879517e7156a4c8f701d26da7af4875bf16d9b4e7` | `2aafdb4b799e5e212564fa7d65adf93b2a7da6b7cec18e3c5e991829846ee0a0` (128) |
| `notPacked_tight` | R2 counterexample (he); R3 result | Quot.sound, propext | `9eb25f3ad7b72d1b66a12024c16454acb52e09212d1faa0f532d2a11d4652917` | `b923d83d08a7451b40cd77a7c6d5d133ae038a96f34691f2b6ae84937f4ad968` (128) |
| `projectionConsistent_tight` | R2 counterexample (hf); R3 result | Quot.sound, propext | `a661e1cbf7d3fb9dee47f7dcf60a5aa9d2a5bf75a9c60d9e365c0d19ef674346` | `8fab0e61eccd5af27b1340213fb1f27ea022f14cfa5a7a6d93b60633f514941c` (127) |
| `safeProgram_tight` | R2 counterexample (hsafe) | Quot.sound, propext | `eac87e2994f6209020e73e05435b400c15a8292429f7b219ae300d15f595a993` | `bb2c491b448fc672bfca019d2da14b7676bb23ad301deecd831f4350d3bbeca5` (127) |
| `conditions_abdef_tight_via_list` | R3 result | Quot.sound, propext | `cd6af6321896e7ca1860ba0bd9f3b579dc6f79b834a766de85d33a73897cbe36` | `208a06f9d7a7424c6bc5451eabf6a09b367dee3e21492b3695581b70693f348b` (121) |
| `dropGuaranteeForPinned_invisible_to_selfRef` | R3 result | Quot.sound, propext | `7be68fe1755d310aedf8d3d588ca9141a565c4f08d87c0674382a0d5893d0017` | `db3f389d5aa5f2b8bb751f3ad7d365bb4f3e49523572ae5c657c15a83bf54f51` (120) |
| `dBase_sound` | R3 positive control; R6 positive control | Classical.choice, Quot.sound, propext | `a829c69466cee555075359d5acce30b67c6dc7fef41a3d01c7e5ce04ac0dfa56` | `8af3620febbc559c35b04bc60dc845817e518c6d78029c7b374623ea9a5c2a88` (119) |
| `conditions_a_to_e_insufficient` | R4 result; R4 non-vacuity | Quot.sound, propext | `d0b3a9f4e36ac4664772b56c7a1aaccc1e187ffcbfc5c4ae3d2b1dee4b11a22f` | `ecf1b2f0a2a7412991337c5579432681020a42de44e5d65bce99f853779acc1e` (127) |
| `projection_inconsistent_assign_harmless` | R4 result; R4 positive control | Quot.sound, propext | `940765e8a35dfd1b34aae2b5118a3f645b3ab2e882db08762772c7ffe1812bf9` | `386c840420c9b9036b5ec764eacd47215df073f16f415cdb4bee06aadbe8f025` (120) |
| `projection_inconsistent_unpin_field_sound` | R4 result; R4 positive control | Classical.choice, Quot.sound, propext | `af812576d6288ae2e6359abc52a3e1178c60395b054acde8c1b6531a5ff17fbd` | `c86b1e462f02d87ff72e45d8f74424acfa110b86b95589acc3c4f3b1d0accb18` (119) |
| `dFUnpin_nonvacuous` | R4 non-vacuity | Quot.sound, propext | `63a1300820247876d58e116f5aba5087f0ca60088f2ef5710899cf4c833d03a2` | `bc72290a015b21c8c26730176d125487cbfaf70ddeda0f186a0c0b8018b91326` (111) |
| `unpin_sound_iff_pinnedFieldsUnpin` | R5 result | Classical.choice, Quot.sound, propext | `f2ae48bd63c50641bb4c2af3e2e0420ececd126677642d0ad4be99832e844029` | `3cd689bbb41e37add7c8b9e6b92bb989b370502a8eee2135e0463056733c0c79` (119) |
| `unpin_iff_nonvacuous` | R5 non-vacuity | Quot.sound, propext | `eed023c67cba681929014bdafda711b1ff8fdeb2723991ff340b14980c8d9d77` | `c98a179d3aa7e839a8da67f3fdd7449545731278dbc1820132541bf4420a33ed` (20) |
| `unpin_iff_hu_tight` | R5 counterexample (hu) | Classical.choice, Quot.sound, propext | `32a066b29d75b04f60bd7f556a4ce4ed9937ff58a6b84e8d4b06896b4b9a13d3` | `429e9ba86d02d254ee3aaaf014beb81ac4cf90e19d5fb585a428af6adf8b340f` (120) |
| `unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field` | R6 result | Classical.choice, Quot.sound, propext | `b006059e92cf07e9e9548c4cfc4ef5184c3409b256302df2e0d8cd333cd66995` | `3b120812d6af8483513005333f793769dd6c32bd49366c3313a8441d8ec611f3` (117) |
| `unpin_unsound_nonvacuous` | R6 non-vacuity | propext | `efddc4f394b95ce308b22614bd92d1ab5d4aa2de53a537b4cff4dd6b92425ee4` | `b6d16121696f9672f3b51df2e8d3e03ab8e158062281a0c3898dce3d06532db2` (18) |
| `unpinWitness_fieldTy_tight` | R6 positive control; R6 counterexample (hty) | Quot.sound, propext | `0388c7fbc3ac1f66ab5cfa9a4588a796944832caf478eaec2e73789edc7f572b` | `f77a72068641e3522e9784738551847a3f964729b4cd0e0528fac7e927df1e50` (119) |
| `unpinWitness_projPin_tight` | R6 positive control; R6 counterexample (hproj) | Classical.choice, Quot.sound, propext | `58aa6b19221140b977bffea05f93a05878db444d2e7703110b58134dc74cfc50` | `38cdfde37d7f5b7ab6a95416e3fe18b931cfbcc50654c5d82eca42de5cc53801` (120) |
| `unpinWitness_hu_tight` | R6 counterexample (hu) | Quot.sound, propext | `0fda379a8841c69321c5ae5800ffa7c71518ab097116c2fd4b4ddb9729307ba4` | `0b8dd9fc9708419b2f2e49782aed90c807c15e84f901cba5c6e2c35ca8fb2ad0` (118) |
| `soundUnpinRule_iff` | R7 result | Classical.choice, Quot.sound, propext | `d4d6376f5b3a4e4ff70bb2135e78a47f67570f9b1f7209af2054c794f544522c` | `fa6cd02ef808bc7a8e389918b611ec8e541e7263b119e65c2e854bacde890673` (126) |
| `pinnedFieldsRule_sound` | R7 result | Classical.choice, Quot.sound, propext | `b0911ee1173c3583ef8c26aa6ec5bc73ae4c121814e97c3d9ed5c55dbb245d7f` | `696d562dc27154017152d3ff45ee180e5d97e6528443e2c9b1ed4703bb39d872` (154) |
| `pinnedFieldsRule_greatest_under_b_to_f` | R7 result | Classical.choice, Quot.sound, propext | `d28df4ba875ac5ba670d3f31e578b0b9b5d8a809e075adf6860fcfa9f5cf0caa` | `696d562dc27154017152d3ff45ee180e5d97e6528443e2c9b1ed4703bb39d872` (154) |
| `soundUnpinRule_false_of_grants_structural_nonUnpin` | R7 result | Classical.choice, Quot.sound, propext | `0bdcaa41203a1c36c934a3faa141a52decd9479328fc1d4e25a04c05789d6532` | `95b015e67a3a0ce537f9b6b1ee94d25f87b770eb71962a71abd2eee1fbe530eb` (125) |
| `pinnedFieldsRule_greatest_nonvacuous` | R7 non-vacuity | Classical.choice, Quot.sound, propext | `40082ca2098854cf981887b60b43100110f28d70a05569c630eb4cce03f52249` | `6226f329e15dca8334534de5d456a34794a34d0172e77d923d91acd81278a035` (155) |
| `soundUnpinRule_false_nonvacuous` | R7 non-vacuity | propext | `b4ee0927f16997f00bad1bdc8ea57ff953f2e62b9927fb29b2fca68362b12cf2` | `39b17cbb3dd16094517585cf33deff228e9e74b61eadffdee43609599e672dfe` (22) |
| `alwaysUnpin_unsound` | R7 positive control | Classical.choice, Quot.sound, propext | `e286760de13b7bcd55e3dcafc43a8fab6fc981be3f3e1d0a0be40aa0b2be4e1c` | `95b015e67a3a0ce537f9b6b1ee94d25f87b770eb71962a71abd2eee1fbe530eb` (125) |
| `pinnedFieldsRule_not_greatest_without_b_to_f` | R7 positive control | Classical.choice, Quot.sound, propext | `68bae3d418a402b9db57be06f2b57db16ae28ff219859720c3fcc854d575e327` | `93aee4434dd63c9147475e80a3abe0a7a1599f4ded915837ad4e2cd803dd3738` (157) |
| `pinnedFieldsRule_greatest_hr_tight` | R7 counterexample (hr) | Classical.choice, Quot.sound, propext | `f99ae5201f6d36e0e1fbe6266c29cda26d48e5a3f5ba24d4703beb5dc3fcd8a4` | `20189ec087d3a9a51f73b677d079bfcae82f6cf6318c3b98bd577e887861dc4e` (155) |
| `ruleResults_b_to_f_tight` | R7 counterexample (hb hc hd he hf) | Classical.choice, Quot.sound, propext | `dd7ff0e979c708f7688cdbad7a58686206c2b2261f8aac4438da9fd22b96334e` | `6316f79d1d0d1c91f8b013a3e6071d3852ce092eb76ae90ed4230a03f0818b83` (182) |
| `ruleResults_h_tight` | R7 counterexample (h) | Classical.choice, Quot.sound, propext | `fb56030afd19c4dccceb9b7dc100f1878f596ff61530c7015c05fc7bec116285` | `20189ec087d3a9a51f73b677d079bfcae82f6cf6318c3b98bd577e887861dc4e` (155) |
| `soundUnpinRule_false_hproj_tight` | R7 counterexample (hproj) | Classical.choice, Quot.sound, propext | `4d588ac58095ee6ad4af6f970f4c0418a5c5d0ad7fe0297a9b3192468481b874` | `6226f329e15dca8334534de5d456a34794a34d0172e77d923d91acd81278a035` (155) |
| `soundUnpinRule_false_hty_tight` | R7 counterexample (hty) | Classical.choice, Quot.sound, propext | `a709193b748fcb1acf5a8c3be468fecdd146a916ea7194e141c4bb4848e71d56` | `91f4693e2800631ccb7da65e30b1e9ddc6d2553e2bfebecc1132aeb0b522f36d` (155) |
| `autoUnpin_sound` | R8 result | Classical.choice, Quot.sound, propext | `6f1eecc550d728dce59374a97a164da50407f1e8d01b65b04e32ded076c80b69` | `19f5f60febbdd1ccf7392c2111216aaa70b5fcb713759a773d4bb16b1e192205` (126) |
| `autoUnpin_implies_pinnedFieldsUnpin` | R8 result | Quot.sound, propext | `f333916d49c0392fed7e423334ee1ce615aee7ccf0b9dca0eb05cd87bd74e7ef` | `a7a102caf6d44492cfa64a997a5928e75424361cc36ebce02498c937eeeddba1` (15) |
| `autoUnpin_conservative` | R8 result; R8 non-vacuity | Classical.choice, Quot.sound, propext | `7158f72c81dad0d10a2d5234a9f70dea3465bc9ee1c56bfc211f66510bbd568f` | `157257a3bd5751a70a158c120189af75b6acc53c0c64b41e67fe7472341b7cfb` (121) |
| `autoUnpin_true_witness` | R8 non-vacuity | Classical.choice, Quot.sound, propext | `b933d4d2614c8c2797ef36abc56daf911b8c81dc296af25b6431396b230035d3` | `9709718327fb47761ff3e1b0a93d095d563e0587fa0bc2fdd0ee08d5c33177b6` (126) |
| `sound_declarations_nonvacuous` | R8 non-vacuity | Quot.sound, propext | `b2fb6bde4fd5bfebc31d7e9fa4519993ea9bac24baf057fd1f1a856cdc26aa90` | `b2086bd2ef45c40884ef847c2bba2261777c2a0cd86bb541726a110e02fde530` (113) |
| `autoUnpin_sound_b_to_f_tight` | R8 counterexample ((b)-(f) for d, inside SoundUnpinRule autoUnpin) | Quot.sound, propext | `87a2ec8598974345be386364e593bd70f81269a76832a10e17a3e4c780b8f331` | `872fe9c2d04394738f3c3e27df2f7ea7b23cbc6f97dc1b1966ff0a45b2d16a46` (125) |
| `autoUnpin_sound_b_to_f_tight_combined` | R8 counterexample ((b)-(f) for d, inside SoundUnpinRule autoUnpin) | Quot.sound, propext | `1a9cbed3e0d3b84ac6518cd2f9f2d15f415d81fbcc79b2c878a1c29be26c4a65` | `8e6076d25713ee689ffedf54d29f8f18947a60e3af047d956a0d5137d316c07e` (132) |
| `autoUnpin_implies_h_tight` | R8 counterexample (h) | Quot.sound, propext | `6e785f790f301e95512d52c3a8f67d49fb0bb9e2d017593366373c6364620a73` | `9bb2e68df36a618fa1063de373d48d8d5751bdf9bf301ade1992b39ecd7b250e` (16) |
| `forget_preserves_addrInv` | R9 result | Classical.choice, Quot.sound, propext | `dbe62aad2ac80b0091d34a5cb1b12b93d03c2942a596b570a8f91d1ea5df81d5` | `6a3ebeff191a45ffa677318042169751dee8917766eda497bd8d8b5bcab8addc` (59) |
| `forget_frame` | R9 result | Classical.choice, Quot.sound, propext | `518cb9d60e68a5c769671fbc7c4562213307b3f5f46a2c676fe3401aa5eac976` | `29cfe94c93b74f07b8f0071491d52658bb1ad168eb840cb04579484314a7826d` (57) |
| `forget_respects_contract` | R9 result | Quot.sound, propext | `9478fe988f62a8e8650c60926d4da36bbdb36c2eab11b8c35fc5dac423ce7543` | `f84c085d8da170b381bfc76c14c9d6a160dee6b7e0dda437f9ce0d096431c6ef` (42) |
| `leaked_object_never_dropped_or_deallocated` | R9 result | Classical.choice, Quot.sound, propext | `e0e600aa5b21fc5605b034f09f7368a359760b0652268eba7b9dfc057239c11b` | `8367acea728cd26c1caa74c27d232cca569df14280d2b44746705451ada99742` (112) |
| `unmentioned_object_unchanged` | R9 result | Classical.choice, Quot.sound, propext | `1bcbe2a086745a54c56b22a79ba6eaa0461c5c6fd35082cf1baf2e3618f99232` | `644f519f47856cb53903f4caf58d37bc9b6a07de842b70956df3898ba829fc83` (101) |
| `unmentioned_object_leaves_and_entries` | R9 result | Classical.choice, Quot.sound, propext | `707b5513db237d67d41b4f0f4c813cd2ddb650ef3263a58ae06996e698727bf0` | `644f519f47856cb53903f4caf58d37bc9b6a07de842b70956df3898ba829fc83` (101) |
| `forget_keeps_addrInv_and_blocks_drop` | R9 non-vacuity | Quot.sound, propext | `d37ca1b5140e0e269353cfc5a407626473b2b7d3e674db99b672fb0532b55f5a` | `bd1eaa83d7e264dde9ae94a4c18fea0daa700e53856d8ab566f85e7aab9940a0` (120) |
| `leaked_object_nonvacuous` | R9 non-vacuity | Quot.sound, propext | `7e67debce360fca3d390268203400148ff2bcc1a4421f1ab0e332623a7b5913a` | `c9eaad9c4efc9d52b858901663c99073f883d29656f68fa77bd29a015a474fd6` (115) |
| `unmentioned_object_nonvacuous` | R9 non-vacuity | Quot.sound, propext | `b5f1b16157c87da96f9e77fd2faac6477be3d9823c1657af549e458369143601` | `b13afd38f5b8f26b82f1d8a3ae5d3cebd7af8af5bb6456c599e65ad7eb41374f` (117) |
| `forget_preserves_addrInv_h_tight` | R9 counterexample (h) | Quot.sound, propext | `a15ac1ba38e810ceb9535194507784e5b05b838760c4f3c12b5c2e63c6ed5474` | `c7eddb0f21c188b74da786025946bd7dee84374c6084ead8ae865cafe13b450b` (64) |
| `leaked_object_hleak_tight` | R9 counterexample (hleak) | Quot.sound, propext | `c0961970d16a875d9eec31273556e8d0d1030359fe2fc09fb13c8baa8c70bf7c` | `a85590087b1f10e6ce705f4506a60b6656fc909e693eeb80faffac1844969da3` (115) |
| `leaked_object_hsafe_tight` | R9 counterexample (hsafe) | Quot.sound, propext | `9b947d1de72cc51a4664f6f3a8814a52c5a0a75f92e2e30cf0376d8b445e5812` | `9040dd777acdd0fad038ed5c8b3707ea553f9754915b4acdd5e047388cf846a2` (117) |
| `unmentioned_object_hb_tight` | R9 counterexample (hb) | Quot.sound, propext | `6a0265dd9c68f495646e1ce8b448524309a66d996ce713e4f5b09b47db9d56a0` | `4e36b7a0af64594aea641678c623bc5e9aec64fe5425bfead6cdf37c2229ecb6` (103) |
| `unmentioned_object_hmention_tight` | R9 counterexample (hmention) | Quot.sound, propext | `e22c3f87b6801ac8886b569e89a07a6a3db5a0db7d0fbbb68cc872f99f53aca9` | `2a6fc9023e84638d6849593afc78e5758b39aab9e1b538e51fb7f6619d4dcb43` (108) |
| `unmentioned_leaves_hb_tight` | R9 counterexample (hb) | Quot.sound, propext | `afe490c01c459b02fa6654164d0fe0aee5367c1d371e6eb23bd9acb58b15f4f5` | `4e36b7a0af64594aea641678c623bc5e9aec64fe5425bfead6cdf37c2229ecb6` (103) |
| `unmentioned_leaves_hmention_tight` | R9 counterexample (hmention) | Quot.sound, propext | `5577e6ba6b797455a1991eadd9e3c94468113bca48d9071d9b8d415d527e4ffb` | `2a6fc9023e84638d6849593afc78e5758b39aab9e1b538e51fb7f6619d4dcb43` (108) |
| `reuse_breaks_list_not_selfRef` | R10 result; R10 non-vacuity | Quot.sound, propext | `9be61307fca455a8af5e4ffab7ce958f0c3bdc1cf0ab2027eb602547ecf6cf12` | `14ee0e153729171c8b4c927f9dbefd16da0f54357a4dad7b85aa1c6803e3974b` (76) |
| `forget_instead_of_reuse_keeps_addrInv` | R10 positive control | Quot.sound, propext | `724a8a0bcc674b424f232d23e0ee2716e8283803656cdcda043dbdbecefe4862` | `fb6926374d279d3867aac5a0085530165f8a8c09e2022251d4ea50536b72da08` (74) |
| `addrState_only_at_structurally_projected_fields` | R11 result | Classical.choice, Quot.sound, propext | `b92112c9378ae40a5e261648a2d810eaea4e9330901d2be6d58340d4d39b6c49` | `0d96136d41090ccbe9fc5814454ebe765835bce513eb33a4a8841600334ec2b7` (115) |
| `no_addrState_without_structural_projection` | R11 result | Classical.choice, Quot.sound, propext | `c3806a1719f6215108299cdc7f76493db016d99321217e32037b318ba07f0d8d` | `aa29d0c5737ce5c35885d4dc0d05ca85d26ea76d1a5e42b3cbefa8c0dc279a83` (114) |
| `noAddrState_nonvacuous_nonempty` | R11 non-vacuity | Classical.choice, Quot.sound, propext | `3d01ea2c54c64d228ac5195e345d83c5943d3d1e8686e8f0af3c81c36fa580d7` | `691304cdc4cbcb2e6af86e54c87f85261fac35803fcd50c8c781690ecd8bb568` (111) |
| `noProjection_unpin_vacuously_sound` | R11 non-vacuity | Classical.choice, Quot.sound, propext | `47addf6d63329ba2637c928e9fce1af723a2654834693b4b7a396e5d7c9e2c16` | `0f28f76a258a5585675cbca51086398858fb123fcf972c3caf6a61379764a272` (120) |
| `addrState_hsafe_tight` | R11 counterexample (hsafe) | Quot.sound, propext | `c0e3f4674e1683b8697cd73fb5ea92a14b7fba9bdfe8fb9bfa28b96b0ed39cdb` | `622e012b4c1dd8bc49174cb752d5b1d0317a680fede7564f37116fec1be02516` (117) |
| `noAddrState_hsafe_tight` | R11 counterexample (hsafe) | Classical.choice, Quot.sound, propext | `f1a6847758e6e131e3af51810d2e7b825131cd9f53c895bb2c9ad17526282c23` | `6e302548a2dbbd66a7018aea3f4ee04829883f61b4593a28237e9a8469ed7ff4` (116) |
| `noAddrState_hno_tight` | R11 counterexample (hno) | Quot.sound, propext | `c02b7b5d74be7a409609c2bc5fcc51ed9738700cd7e822ebf64035fdae2aead8` | `842db53d221d9668826d26abf138dde27c80e2d253cf151d62f823e9392e0f60` (116) |

Declarations listed in `lean_names` (each quoted in this report: theorems with the proof
elided, definitions in full):

| declaration | kind | listed for | axioms | statement SHA-256 | closure SHA-256 (closure size) |
|---|---|---|---|---|---|
| `addrInv_neg` | theorem | R1 | Quot.sound, propext | `63a6b4331ff084c44f8179dd1ccc43b0f211529a5cc082a6775062b9c7da9eaa` | `ac5c722a1d57b684239b736d9fec9bfc77a0d3f1ddb887b216fff845cb4a715a` (65) |
| `addrInv_pos` | theorem | R1 | Quot.sound, propext | `6c4c73577f3f13e3fd6631c90672175bf082a4eb4a61c3ebb38f12f944ea5a94` | `ac5c722a1d57b684239b736d9fec9bfc77a0d3f1ddb887b216fff845cb4a715a` (65) |
| `addrStateAtProjected_pos_neg` | theorem | R11 | Classical.choice, Quot.sound, propext | `0d7a94e3e1632856590021cfbb1d927c04bd87a283f8813269854189f14d73c9` | `7600dfac84103c68c317a1793a670face5da5e47c6342bc997cd519306072449` (117) |
| `autoUnpin_does_not_rescue_dB` | theorem | R8 | Quot.sound, propext | `baac886e33cc945a9ed0596fd0471fa7c218663db37ef4806ae4bbfefaf56cf6` | `24c0ebe4c2a760dbb875269f54510fd5e5585a29244ee710ee213d7c87b9f28f` (123) |
| `autoUnpin_ignores_unpin` | theorem | R7 | none | `fe8644b9b02ff69d7e340a44559a44eabe812f14cebd9636a7d4f3f2b19258d3` | `75643fdd56ec4bb8098991cc8d12065bff9f3fe0a50bc419a8d8d2af184fe0ed` (15) |
| `autoUnpin_pos_neg` | theorem | R8 | none | `594ed5ae0be1b45378528eeeb41b72d5411664bcda2d5c777153321c81352ef6` | `c8964033e35d0d33ee8141dc8678ecd446005146c8a0fd856b31c8d1684101f5` (15) |
| `conditions_pos_neg` | theorem | R2 | Quot.sound, propext | `eb4ddcb9231f97220d7368fc9ec999b8e53bcd2295c1ee329fc79c81b9a72f65` | `d3addb779629b0104023e2fcbd24156c89625df8d9858923b4a367c2e105a608` (30) |
| `conditions_vacuous_without_pinned_nonUnpin` | theorem | R2, R3 | Quot.sound, propext | `18e95409f7e83ef16a849ca8f077bec55b6384520d3e58feb8fdf56d32afe3a3` | `ee6cb6ef5bd6e18d8b73afe7b840077fff931761ddd70a370367f542a6f43811` (24) |
| `dBase_satisfies_all` | theorem | R2 | Quot.sound, propext | `1773dcfb8a8acc5ecff2b6bda18a9b95e111499b86a2d7117f306d0230e63ea3` | `139b8fcd6d86d538e17e175a143ee31755723d693cf7376d12f0926a15027e78` (24) |
| `dropGuaranteeAct_neg` | theorem | R1 | Quot.sound, propext | `90e8a4285646957a8aae273ba208a9704c14df2c28bf99a059850c0b80ef753c` | `809f01de4a6ae5fcfb364c9e5c345cb0a05ddcd582e93b777bf1fcc06ad4813c` (67) |
| `dropGuaranteeAct_not_necessary_on_a_trace` | theorem | R1 | Quot.sound, propext | `55bf839b54025b0a0adca14e3fbd7d8e7330555f317e6ff130c10a756fc51e1d` | `fb6926374d279d3867aac5a0085530165f8a8c09e2022251d4ea50536b72da08` (74) |
| `dropGuaranteeAct_pos` | theorem | R1 | Quot.sound, propext | `3823160a6ea4345615ac20cde557f24895abf9a4bf6f4e63dd53c4c2ff76d5b3` | `3e500e97c860481501cd1579f1055068a2e568a3d0d387cc61ff226ff7bc1f8b` (66) |
| `forget_does_not_freeze_fields` | theorem | R9 | Quot.sound, propext | `b131ffbc381774d4f6d7d03f71ceb3435c9d0256a361a22b0053a07f9aae321d` | `6155c7984ab792120eea4093c5cff3482a8f40de946dda85d62c81b0a5f9ea92` (113) |
| `heap_reads_at_out_of_range_address` | theorem | R1 | Quot.sound, propext | `8f0e72337d853d7fd447cddc2e287e88f68781917fab3eb4201cde610d1fd145` | `c1a3b15373dd08bf44eb1f6c990c25200a7ed382210d07fca44c5f4b6f0770c9` (22) |
| `heap_reads_in_init` | theorem | R1 | Quot.sound, propext | `16b252ab1c29b2a71c381235a9652e95d528c0c355f141c637941216ca586d3e` | `4c8087618d6291654deb9316a5569fa862ccbd36898b5ad30d3a5d578186c640` (23) |
| `isPinnedLoc_at_out_of_range_field` | theorem | R2 | Quot.sound, propext | `9e7d667fa15f65fa4b9e26f0157a8e1cc2b82c8e9429136badc347e65d0180b5` | `bfe4bd5771faff7bda6641b8525b66202d346ec844996041f69861d54c161760` (114) |
| `isPinnedLoc_pinField_self` | theorem | R1 | Classical.choice, Quot.sound, propext | `95810a5f22e63171b1704c63755792dd945a26311da30d000e31833e969a9662` | `d9ac19686947a37be00aad0c1c45626c6baeaf08792e4dd8f2f5221605c56462` (55) |
| `leafAt_of_out_of_range_field` | theorem | R1 | Quot.sound, propext | `51e855cc068ebd5c42ca7db1e76c4f9f8759b98b6e65451d434c7c25de8d3702` | `825d03ba6e20b77e3c767fec2aaa2ed6d2fcefc6dc9219e3331e8c78df925bdc` (14) |
| `listOK_after_proper_drop` | theorem | R1 | Quot.sound, propext | `23ac0f5f03a31533f4fdffa0b0d1b542585374d0e2b96b3a77becb9f2fa20069` | `81fc98615cfbc064073b01906388eaf626ecf49b0806d93054bd9ae2dfbb5baf` (62) |
| `listOK_neg` | theorem | R1 | Quot.sound, propext | `b9e0fa80897c4308a270cd22d218638ac6bf570a2b50f1cc1ca07ce19c7ace2a` | `81fc98615cfbc064073b01906388eaf626ecf49b0806d93054bd9ae2dfbb5baf` (62) |
| `listOK_pos` | theorem | R1 | Quot.sound, propext | `3b410e8df5bc0ecd92804cc4c5ac9ed3c84e77a0d0a1e577da0bd553953b6579` | `81fc98615cfbc064073b01906388eaf626ecf49b0806d93054bd9ae2dfbb5baf` (62) |
| `neverUnpin_sound` | theorem | R7 | Classical.choice, Quot.sound, propext | `5b4549e1c89332fcd211bb6ee091f4a73c55bf665720839d1025a16dd126de12` | `95b015e67a3a0ce537f9b6b1ee94d25f87b770eb71962a71abd2eee1fbe530eb` (125) |
| `noPinnedMove_neg` | theorem | R1 | Quot.sound, propext | `9f5e7bd94d4f0bee4bbae419d9dab95dd4415535b915c4d880eb7dc956d2f1df` | `2d955161f08cb118f575c4da805db27e3db1c0bab45cdfd56781ba673f7f369c` (66) |
| `noPinnedMove_not_necessary_on_a_trace` | theorem | R1 | Quot.sound, propext | `687b2274902e5ae944e888e3cf120439d1cf44126cae049d58a4422a2e79d963` | `fb6926374d279d3867aac5a0085530165f8a8c09e2022251d4ea50536b72da08` (74) |
| `noPinnedMove_pos` | theorem | R1 | Quot.sound, propext | `1b99a492c44e97819cfbe5e11337db8b31d24b161eb3df5cfe6a3d2c48a3c97f` | `0ac2f9b07fb7d0261943e17131f44b30194beedc3913632c4677599a6ac7c6ce` (65) |
| `Obj.leaf_of_out_of_range` | theorem | R1 | propext | `39efe97981fea1d44fa78e43f46cbe62d050ebd117da6da25513230a7aa5901d` | `8842dc919e692827e05e36b292d98585c4e2030555e5ca1b70565a652ccae48e` (8) |
| `op_mentions_pos_neg` | theorem | R9 | none | `7a6e0bf390bb7350d3ce908a8bb18f40890acaac6cdfea708b4718fbc26c42e7` | `c5a9731213af82c90c5f4adc4c5eba0b44bddbc8de6560b85e6759271b1300ad` (19) |
| `permissiveRule_sound` | theorem | R7 | Classical.choice, Quot.sound, propext | `1cc522674f3cbf0ec470051ee0b408502930102f287ccde23e36b7f8b1a11c8d` | `9d49505876538f3af4358a4b58f2efaaf58a17c8b888f0d3cd1d0f75b1369702` (176) |
| `pinField_without_pinObj_protects` | theorem | R1 | Quot.sound, propext | `4ccd9c47e97be90a68764fd3b03c329f4d0e6b89a11d5065b087e61e6dd90202` | `5d7b53b74540f9477587ce19f1e0de53845b524bfebb4f77b46ac01c3a932701` (61) |
| `pinnedFieldsRule_ignores_unpin` | theorem | R7 | Quot.sound, propext | `414335db20b9054352d077734c437410b8ebd9bcad51030e25fdae808bed1607` | `e2aa5a266c0527ebceb30c9b8b04a46ba22fcbe9d2497635a125515739e894ac` (45) |
| `pinnedFieldsUnpin_pos_neg` | theorem | R5 | Quot.sound, propext | `4d293b89f3d4542ce8e9e640ba7df8064348c0374b59eea7d2f25f358850d752` | `08957a61774b1143c0e49583dd6f673357ca1a7d3181618a7b850e4dc127fef4` (17) |
| `pinnedNonUnpin_in_range` | theorem | R1 | Quot.sound, propext | `8effe0ad22d2da4722dc5a6df8c5f0e1537becf9482b74f69f11339daf25c50e` | `779f129f33acccde07de981d1bc4aaeb6e33992d4d025a552ed45865a444f021` (18) |
| `pinnedNonUnpin_neg` | theorem | R1 | Quot.sound, propext | `614e5e6383e0a80b0a7ea683af8d29d06a974efc8e1d4b745bdd2a1a782f504d` | `6ed7ad5b85c56d9390cf4e73113360e356fe7cfbc5a43e044c2ae5a71d39803e` (61) |
| `pinnedNonUnpin_pos` | theorem | R1 | Quot.sound, propext | `e20e06412af8fbe78822ff9d09049d7c0dcb7391f37fa991a0d9ab7053b9b545` | `6ed7ad5b85c56d9390cf4e73113360e356fe7cfbc5a43e044c2ae5a71d39803e` (61) |
| `pinnedNonUnpinField_neg` | theorem | R2 | propext | `f44120b8fa85285a5dc883301f3896d5eba37cf93569349102fc5c5ec2997030` | `9aaa11f9baf4235dcd4115b2e686cb3d66a03bf4e23422c217349d90a92f09e8` (19) |
| `pinnedNonUnpinField_pos` | theorem | R2 | propext | `f94c28632dc357a0ccfd3df06a8fcfbe528311351f5c17f4ed76bdc9de45625a` | `48f50d3b675352a8b635c3649fc9ecfbccfbc363fc1ac01976ed323325209ff7` (15) |
| `pinObj_inert_in_core` | theorem | R1 | Classical.choice, Quot.sound, propext | `9ea778e145c6c117b6dbc5ab31634f1b17ff747d59a6f8643d5ccefc299a5ca8` | `26039374bb2fcebbb9598d81ef4679eb42becad31c2703c706f23f38a05cc5d0` (56) |
| `register_requires_pinned_nonUnpin` | theorem | R1 | Quot.sound, propext | `642b6638b101d01fdefbf60349fde1aa7cb6326943f62a5730a0890e76ab33e6` | `9ab8c3673fcf5ff3365978a5f46ab10a1905b7913d08adac0a7c147ea1afb263` (59) |
| `rPackedOrPinned_sound` | theorem | R7 | Classical.choice, Quot.sound, propext | `e0d1faf9508d205baeb9a7473dc5a63cab568860f1464c85284a6acbfcd26dbe` | `eef74699c2021c7864ba662b6659d25d8f7a08273202505ad9acdbff6c659998` (155) |
| `safeOp_pos_neg` | theorem | R2 | Quot.sound, propext | `77dbc4a733451c61ca88ba6d8778b8c20345df56153c3b7feb60477c699252e3` | `b12ba48d27900e14fcf6957c0aeeab221810ad6c798eb5fb4d5254de30615ab9` (110) |
| `safeProgram_not_necessary_for_a_program` | theorem | R2 | Quot.sound, propext | `c16cb434d55b4d3c1d429763a6c0a6fa581f6a2e6fd810bb3a782c2ad9aef6ca` | `6d6dd5062f425b834a3ed4d99e129384466dac7ddf34094d00b5d060a1600e6b` (118) |
| `safeProgram_pos_neg` | theorem | R2 | Quot.sound, propext | `3fff4abd821c6b9d69161e545b135d37158739c8bbfca2eb595a96b743f2fd8d` | `f142c488dcc123f382e0a0c2ae54618b3c5358d816bf4b2745f59bcfd525b964` (112) |
| `selfRefOK_neg` | theorem | R1 | Quot.sound, propext | `e3e32797d29c64b89f0e075732da47b1a21b8f6448abe7f2e1bf3c11bc6564b1` | `3e80c750a5723b9f11a13dddab7256ab726923e82ec136d7caeed0d240472f37` (62) |
| `selfRefOK_pos` | theorem | R1 | Quot.sound, propext | `e5f1b5785d5284a3c3672fc2370c9ea56355af45a03065e94c52f2b0dde34dee` | `3e80c750a5723b9f11a13dddab7256ab726923e82ec136d7caeed0d240472f37` (62) |
| `setSelf_requires_pinned_nonUnpin` | theorem | R1 | Quot.sound, propext | `631a58c71f1ccf2ecc4150ee0f4e3b0cc19bb68def97beebf8effbcf91b63012` | `9ab8c3673fcf5ff3365978a5f46ab10a1905b7913d08adac0a7c147ea1afb263` (59) |
| `sound_of_pinnedFieldsUnpin` | theorem | R4, R5, R7, R8 | Classical.choice, Quot.sound, propext | `534b007483d0bd89520217b52250fe24de612f0625c48a1ad9c354b6229e8640` | `3cd689bbb41e37add7c8b9e6b92bb989b370502a8eee2135e0463056733c0c79` (119) |
| `structural_nonvacuous_conclusion` | theorem | R2 | Quot.sound, propext | `1b925178bd6367c82a11280a09309776de8311ea83cc5525537afa81de4af9b7` | `a6c80f077c7b7b74bf7411e70c5d6040ac341426489c5ccc231c0f97d4d39408` (106) |
| `tempActs_noop_on_empty_heap` | theorem | R1 | Quot.sound, propext | `0d86aabb21bbfd61fdcaf40f3102722a42760e5c79f805886b569442ec069939` | `a32e313979bf034c6577de6b8f6178df378b11d01022c72058dcb5e0e8080b54` (61) |
| `unmentioned_leaves_hb_not_tight_on_zero_field` | theorem | R9 | Quot.sound, propext | `4029f75776799bc812d3bb574aa890994c9e637f1c582b6c5e638d79370d2d4d` | `be88da40a35e058af82622c2408c424ea88cdfeee8dae6c98c928f32d8ecd58c` (103) |
| `zero_field_declarations_sound` | theorem | R2 | Classical.choice, Quot.sound, propext | `42ad2b170421946065fba2bbe898b60bcca24ec1476b6011fd04566a4e5d679b` | `689d419aeea7e212a2ed7a6e67425ea13747497095c855aaaea0b800d28fe3da` (158) |
| `Act` | inductive type | R1, R2, R9, R10 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `AddrInv` | definition | R1, R2, R3, R4, R5, R6, R7, R8, R9, R10 | propext | `f5788d642fa85e5f54a29b4d3ae21958bbdedee038ee9ac38858beb98510b09c` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `AddrStateAtProjected` | definition | R11 | propext | `9f69901a00291454ae52317286ab1e049f783ba8ab17a9a76e79979537f68b3f` | `7a123c3690500bc0ad668b71de72463a68a34b4f877751e383d5b45764f7e698` (17) |
| `Always` | definition | R1, R10 | Quot.sound, propext | `fd0babfb29a8b7f7fab5fc29cdefcb52e4fe58b4dc7ef0ee43f9c4f74b1e4839` | `2cda5f338da3b3ce13d9abad48ff169dee6e380bb160e9b954b6827720b0a32d` (22) |
| `ApiOp` | inductive type | R2, R3, R5, R6, R7, R11 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `applyAct` | definition | R9 | Quot.sound, propext | `a4c9964128b4455d73d21a58e3a56aa9fc9fcf68b704701f22b71ab5b889cc44` | `2cda5f338da3b3ce13d9abad48ff169dee6e380bb160e9b954b6827720b0a32d` (22) |
| `autoUnpin` | definition | R7, R8 | none | `0d2351a44fa561a91121e7e373f9201dbcc48fe61d82b94827ecf823b9a41dcb` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `compile` | definition | R2, R3, R4, R5, R6, R9, R11 | propext | `d6e027cb88bf96532ea39eaa9547ea17fe44e81665c6cc8fb8d322322f6a206d` | `8e8cf3917364fb2d6d29aa6d461b9484e53d12ba1fddc06bc6d7e8d70042c556` (40) |
| `coreMoveActs` | definition | R1, R9 | none | `0731dd0160bf5463f0f5eb46cf4f07c560d599581815cf261173052c77d900e2` | `57a2f3f30ea2ee585c7028281a0f88ce50b3a1fca7f46cadb19dbb7668d8a6c5` (16) |
| `coreNonVacuousActs` | definition | R1 | none | `0731dd0160bf5463f0f5eb46cf4f07c560d599581815cf261173052c77d900e2` | `57a2f3f30ea2ee585c7028281a0f88ce50b3a1fca7f46cadb19dbb7668d8a6c5` (16) |
| `coreReuseActs` | definition | R1, R4, R10 | none | `0731dd0160bf5463f0f5eb46cf4f07c560d599581815cf261173052c77d900e2` | `57a2f3f30ea2ee585c7028281a0f88ce50b3a1fca7f46cadb19dbb7668d8a6c5` (16) |
| `dA` | definition | R2, R3, R5, R6 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dB` | definition | R2, R3, R7, R8 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dBase` | definition | R2, R5, R6, R7, R8, R9, R11 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dC` | definition | R2, R3, R7, R8 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dC'` | definition | R2, R3, R7, R8 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dConservative` | definition | R5, R6, R7, R8 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dD` | definition | R2, R3, R7, R8 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dE` | definition | R2, R3, R7, R8 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `Decl` | structure | R2, R3, R5, R6, R7, R8, R9, R11 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Decl.fieldTy` | definition | R2 | propext | `ec178722a86528e5201dc360799de46ed2b69a5fbc39d44415121d9081f04160` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `Decl.nfields` | definition | R2 | none | `b089ff7279148c8a3a24993e11482799eefb8734cb444a03b40354af4e4d66e4` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `Decl.PinnedNonUnpinField` | definition | R3 | propext | `9268b5114f2e7a6016a79b861e54b3e0cad6797e076815895d08851133beac8b` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dF` | definition | R2, R3, R4, R7, R8 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dFUnpin` | definition | R4 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dNoProj` | definition | R11 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dPermissive` | definition | R2, R5 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dRich` | definition | R2, R9, R11 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dropActs` | definition | R2 | propext | `b112b8445ba6dce2c5d70bfd636139bd00e5aa2ab1a8b93c16ee8c57dadf1a57` | `95e699a4dee3c4cf48699c0c6031e759857a6384cedab4ca7b8aa80d03e8b1df` (26) |
| `DropGuaranteeAct` | definition | R1, R9, R10 | Quot.sound, propext | `d132d5bbce113a759475c5750db6a08ed9bde6c35c8d9af1564ec80b14d47a60` | `2cda5f338da3b3ce13d9abad48ff169dee6e380bb160e9b954b6827720b0a32d` (22) |
| `DropGuaranteeForPinned` | definition | R2, R3, R4, R7, R8 | propext | `3410de7ad67d2cd0b2781fed9fc3cfec66f6bc81ebf303ae385c2f7fd147b755` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dtorActs` | definition | R2 | propext | `ab4d32343c443b3c0be6a09ac31f0c8265f318ec68440ef8970fc3f89256a77c` | `95e699a4dee3c4cf48699c0c6031e759857a6384cedab4ca7b8aa80d03e8b1df` (26) |
| `DtorNoMoveOutOfPinned` | definition | R2, R3, R4, R7, R8 | propext | `3410de7ad67d2cd0b2781fed9fc3cfec66f6bc81ebf303ae385c2f7fd147b755` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `DtorOp` | inductive type | R2 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `dUnpinField` | definition | R6, R7, R8, R9 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dUnpinNonStructural` | definition | R6 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dZero` | definition | R9 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `dZeroOutOfBounds` | definition | R2 | none | `1f24a0073a43528bbe88d98718eb77d6cf705fe9e682cf2e759e7aba2a88cf99` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `expand` | definition | R2 | propext | `f4d75d5bc6248a7de0d1a545576aa9e71793cba70ddfe3479e9376748d17f4cb` | `8e8cf3917364fb2d6d29aa6d461b9484e53d12ba1fddc06bc6d7e8d70042c556` (40) |
| `glueActs` | definition | R2 | none | `a6497a8e03ca09a8e72dda3ab5846243ae8d30be3eab8f0c3980e464d86eda82` | `95e699a4dee3c4cf48699c0c6031e759857a6384cedab4ca7b8aa80d03e8b1df` (26) |
| `Leaf` | structure | R1 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `leakProg` | definition | R9 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `ListOK` | definition | R1, R2, R3, R5, R6, R9, R10 | propext | `f5788d642fa85e5f54a29b4d3ae21958bbdedee038ee9ac38858beb98510b09c` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `Loc` | definition | R1 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `mkFields` | definition | R1 | none | `a6375e1d64aee94b7b3a033c5e9d1e2ba5d8e18a8590459d1ed6bc3c21ef5312` | `d5be9e33e97910baff42a805bb16feba6c0782af6484b8a3dfc6080e925f328e` (3) |
| `modifyAt` | definition | R1 | none | `eaf52a4e50bcae53ba16785c062a4bbe2f6f9a8f03fc18056fbc7f2417c2f0ba` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `moveDrop` | definition | R2 | none | `db401011395d45ca1463334b414a90aec4ceb74c3c75f4350b957931699b4bb0` | `57a2f3f30ea2ee585c7028281a0f88ce50b3a1fca7f46cadb19dbb7668d8a6c5` (16) |
| `MutFieldAvail` | definition | R2 | Quot.sound, propext | `2d5b4d58d4590d87e8b50121982278f54c3d1e7fb60bbf60c7629b6b38d090c1` | `7a123c3690500bc0ad668b71de72463a68a34b4f877751e383d5b45764f7e698` (17) |
| `MutStructAvail` | definition | R5 | propext | `93a7400677b3555fcd28fea906c797e5f85f7f7ab94a0e9e082d6d3e021c9fff` | `7a123c3690500bc0ad668b71de72463a68a34b4f877751e383d5b45764f7e698` (17) |
| `NoPinnedMove` | definition | R1, R9, R10 | Quot.sound, propext | `d132d5bbce113a759475c5750db6a08ed9bde6c35c8d9af1564ec80b14d47a60` | `2cda5f338da3b3ce13d9abad48ff169dee6e380bb160e9b954b6827720b0a32d` (22) |
| `NoPinnedTake` | definition | R2, R3, R4, R7, R8 | propext | `3410de7ad67d2cd0b2781fed9fc3cfec66f6bc81ebf303ae385c2f7fd147b755` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `NotPackedIfPinned` | definition | R2, R3, R4, R7, R8 | propext | `3410de7ad67d2cd0b2781fed9fc3cfec66f6bc81ebf303ae385c2f7fd147b755` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `Obj` | structure | R1 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Obj.fresh` | definition | R2, R9 | none | `378acbf8c8333031014cad015650bd59301b0a56a7e22707bb0cc8bc3c0629a6` | `9a88c0c758c5f5183019e0a81e9163b9d02e752d1a7dfc60a89a6e1298033446` (5) |
| `Obj.leaf` | definition | R5, R7, R8, R9, R11 | propext | `c5b6b71c1c28d1ba7a4d8cb598b8812eee518b9c272f43e8ed1dda91ea4d9f9f` | `9a88c0c758c5f5183019e0a81e9163b9d02e752d1a7dfc60a89a6e1298033446` (5) |
| `Op` | inductive type | R2, R9, R11 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Op.Mentions` | definition | R9 | none | `d983d22b173cae14418e6de1532303973a4e77de15701ce4d198ba4bc0233a1f` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `permissiveRule` | definition | R7 | Quot.sound, propext | `0d2351a44fa561a91121e7e373f9201dbcc48fe61d82b94827ecf823b9a41dcb` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `pinAndInit` | definition | R3, R9, R11 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `pinAndLink` | definition | R3, R4 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `pinnedFieldsRule` | definition | R7 | Quot.sound, propext | `0d2351a44fa561a91121e7e373f9201dbcc48fe61d82b94827ecf823b9a41dcb` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `PinnedFieldsUnpin` | definition | R5, R7, R8 | propext | `3410de7ad67d2cd0b2781fed9fc3cfec66f6bc81ebf303ae385c2f7fd147b755` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `PinnedNonUnpin` | definition | R1 | Quot.sound, propext | `dcc3261db6f1ceaf7dfe8d776726477a24c8fd5b1a4bf8afc6d04a93287ee0d2` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `progA` | definition | R2, R3 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `progB` | definition | R3 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `progC` | definition | R3 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `progC'` | definition | R3 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `progD` | definition | R3 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `progE` | definition | R3 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `progF` | definition | R3, R4 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `progRich` | definition | R2, R11 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `progZero` | definition | R2 | none | `b3e3911961cf55f358d4e926f2e9f1c9da6e20f0e4e285a9e80ef7140f66696d` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |
| `ProjectionConsistent` | definition | R2, R3, R7, R8 | propext | `3410de7ad67d2cd0b2781fed9fc3cfec66f6bc81ebf303ae385c2f7fd147b755` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `rPackedOrPinned` | definition | R7 | Quot.sound, propext | `0d2351a44fa561a91121e7e373f9201dbcc48fe61d82b94827ecf823b9a41dcb` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `runActs` | definition | R10 | Quot.sound, propext | `1f784c07a8ec942d1670576e7a1dffaf26a4601f2f374f19ff52ea3b39934cc4` | `2cda5f338da3b3ce13d9abad48ff169dee6e380bb160e9b954b6827720b0a32d` (22) |
| `SafeOp` | definition | R1, R2, R9 | Quot.sound, propext | `83d580c5983e4c5d6bb6a5c6d6f16a4477f74533d25be9a745ac3b46cae70922` | `795349856a3f80b2af490c6f1aedb2fc6fd0cbf34c8d27f6b41381b60334425f` (31) |
| `SafeProgram` | definition | R2, R3, R4, R5, R6, R7, R8, R9, R11 | Quot.sound, propext | `8c0fd8e5bdc248b12e6bf9b9e4c4aee829eda85b1ff12d7bb100f5922ccd6cff` | `795349856a3f80b2af490c6f1aedb2fc6fd0cbf34c8d27f6b41381b60334425f` (31) |
| `SafeProgramsKeepAddrInv` | definition | R3, R4, R5, R8 | Quot.sound, propext | `3410de7ad67d2cd0b2781fed9fc3cfec66f6bc81ebf303ae385c2f7fd147b755` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `SelfRefOK` | definition | R1, R2, R3, R4, R5, R6, R10 | propext | `f5788d642fa85e5f54a29b4d3ae21958bbdedee038ee9ac38858beb98510b09c` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `SoundUnpinRule` | definition | R7, R8 | Quot.sound, propext | `d6b0b203922db166ae4d09da836da753e4c81a86371f58ff47d6a8af72a01d5c` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `State` | structure | R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `State.deallocAt` | definition | R1 | none | `db7bc3fea01376103fd685f7772dc3eb7407d10fd773d44e61fb0b20f44a56d9` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.dropAt` | definition | R1 | propext | `feb42afeaa80f5bf2cce64c81b852daa7040f55a9799574aa6c03f5556ec487a` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.init` | definition | R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11 | none | `4056c5749345492c198a7fa51bb7072361184ccae096d6badf418f595e9f20f4` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.isLeaked` | definition | R1 | propext | `d2f018a545ef88722c397731775a55974087c8ad03e242b0fbd5cd665e36b8a2` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.isLive` | definition | R1 | propext | `d2f018a545ef88722c397731775a55974087c8ad03e242b0fbd5cd665e36b8a2` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.isPinned` | definition | R1 | propext | `d2f018a545ef88722c397731775a55974087c8ad03e242b0fbd5cd665e36b8a2` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.isPinnedLoc` | definition | R1 | Quot.sound, propext | `2e0d8f480509fa6fec28291e263bb5cb6046c03708973ccf5eebee05cc30c05b` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.leafAt` | definition | R1 | propext | `c7f70ae794056fd5eb0ee9c419d028983966e7ad52590446ce802002788a4726` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.modifyObj` | definition | R1 | none | `d3da5b18f110ce2521e3865150b63ce26893b86b5f7076bf2657f9afde7c3842` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.push` | definition | R1 | none | `5d4ed7cf28916d3ece00e9e7cea7f1e876a54e827b3c12056fc4113d50f9374c` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.setLeaf` | definition | R1 | none | `6a9f494c9ac1f7addfd20d1052afd446f6de1bc828df3e67fbddd36107887d71` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `State.width` | definition | R1 | propext | `b7ac8fd89413ad0131024fc4cf53b796f3c976a46eaa4ad680b9b2622719c300` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `states` | definition | R1, R2, R3, R4, R5, R6, R8, R9, R10, R11 | Quot.sound, propext | `f0bca6bd44e15ad343dd38018f14e3b2588032ebe1f185fbd6f2ccf269180079` | `2cda5f338da3b3ce13d9abad48ff169dee6e380bb160e9b954b6827720b0a32d` (22) |
| `stLeaked` | definition | R9 | Quot.sound, propext | `4056c5749345492c198a7fa51bb7072361184ccae096d6badf418f595e9f20f4` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `stLinked` | definition | R1 | Quot.sound, propext | `4056c5749345492c198a7fa51bb7072361184ccae096d6badf418f595e9f20f4` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `stSelf` | definition | R1 | Quot.sound, propext | `4056c5749345492c198a7fa51bb7072361184ccae096d6badf418f595e9f20f4` | `85e96b2f9f2f6065a811f0f39e1fade079c439aea58412aa4f7a0a4373a03c0e` (7) |
| `tempFields` | definition | R1 | none | `5c789645843a0da7ba693432bff73e833711c5c5826bca6dd3cf8c617e70477a` | `d5be9e33e97910baff42a805bb16feba6c0782af6484b8a3dfc6080e925f328e` (3) |
| `UnpinOnlyIfPinnedFieldsUnpin` | definition | R2, R3, R4 | propext | `3410de7ad67d2cd0b2781fed9fc3cfec66f6bc81ebf303ae385c2f7fd147b755` | `2fdf851ebf47d9113c211a6b480f90af6c4ea7b3454fd8ca8f4a867166c53d82` (10) |
| `unpinWitness` | definition | R6 | none | `a021322e91832d97c48f98bf599ddaa82d0aab2023d4ca955e6c33344cdb72cf` | `9cac3441d440814e64179ec84c07b1478b9ac5f553505fe7f921920ec19469e8` (15) |

### Primary sources

**[S1]** Rust standard library, `core::pin` module documentation: repository `rust-lang/rust`,
commit `fafcb2be486f2c24bbeb8417e5d32335df5d9a34` (the most recent commit touching the file as
of 2026-11-21; committed 2026-08-13), path `library/core/src/pin.rs`. Sections used: "Subtle
details and the `Drop` guarantee" (lines 509–586), "Implementing `Drop` for types with
address-sensitive states" (lines 594–633), "Projections and Structural Pinning" (lines
696–847). Verbatim quotes:

Lines 521–523:

```text
//! From the moment a value is pinned by constructing a [`Pin`]ning pointer to it, that value
//! must *remain, **valid***, at that same address in memory, *until its [`drop`] handler is
//! called.*
```

Line 528:

```text
//! 1. The value must not be moved out of its location in memory
```

Lines 532–533:

```text
//! 2. The memory location that stores the value must not get invalidated or otherwise repurposed
//!    during the lifespan of the pinned value until its [`drop`] returns or panics
```

Line 535:

```text
//! This point is subtle but required for intrusive data structures to be implemented soundly.
```

Lines 584–586:

```text
//! Of course, *leaking* memory in such a way that its underlying storage will never get invalidated
//! or re-used is still fine: [`mem::forget`]ing a [`Box<T>`] prevents its storage from ever getting
//! re-used, so the [`drop`] guarantee is still satisfied.
```

Lines 630–633:

```text
//! Moreover, if your type is [`#[repr(packed)]`][packed], the compiler will automatically
//! move fields around to be able to drop them. It might even do
//! that for fields that happen to be sufficiently aligned. As a consequence, you cannot use
//! pinning with a [`#[repr(packed)]`][packed] type.
```

Lines 722–725:

```text
//! It turns out that it's up to the author of `Struct` to decide which type the "projection"
//! should produce. The choice must be *consistent* though: if a pin is projected to a field
//! in one place, then it should very likely not be exposed elsewhere without projecting the
//! pin.
```

Lines 793–794:

```text
//! 1.  *Structural [`Unpin`].* A struct can be [`Unpin`] only if all of its
//!     structurally-pinned fields are, too. This is [`Unpin`]'s behavior by default.
```

**[S2]** RFC 2349 "pin": repository `rust-lang/rfcs`, commit
`f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, path `text/2349-pin.md`. The stack-pinning API
sketch is at lines 341–366 and "Unresolved questions" at lines 392–403. Verbatim quotes:

Line 29:

```text
The core goal of this RFC is to **provide a reference type where the referent is guaranteed to never move before being dropped**. We want to do this with a minimum disruption to the type system, and in fact, this RFC shows that we can achieve the goal without *any* type system changes.
```

Lines 399–403:

```text
We may also choose to require that `Pin` uphold stricter guarantees, requiring
that `Unpin` data inside the `Pin` not leak unless the memory remains valid for
the remainder of the program lifetime. This would make the stack API documented
above unsound, but might also enable other APIs to make use of these guarantees
to ensure that a destructor always runs if the memory becomes invalid.
```

**[S3]** `pin-project` 1.2.0: repository `taiki-e/pin-project`, commit
`f49edb9596fdf8bb09d48091755e522bb4a119be` (release 1.2.0), path
`pin-project-internal/src/lib.rs`, section "Safety" (lines 87–159: generated `Unpin` impl, lines
96–108; `#[pinned_drop]` instead of `Drop`, lines 110–135; the drop guarantee, lines 137–147; no
move-out of `#[pin]` fields, lines 149–155; rejection of `#[repr(packed)]`, lines 157–159) and
section "`!Unpin`" (lines 283–313). Verbatim quotes:

Lines 93–101:

```text
/// This is accomplished by enforcing the four requirements for pin projection
/// stated in [the Rust documentation][pin-projection]:
///
/// 1. The struct must only be [`Unpin`] if all the structural fields are
///    [`Unpin`].
///
///    To enforce this, this attribute will automatically generate an [`Unpin`]
///    implementation for you, which will require that all structurally pinned
///    fields be [`Unpin`].
```

Line 313:

```text
/// Note that using [`PhantomPinned`] without `#[pin]` attribute has no effect.
```

**[S4]** R. Jung, "A Formal Look at Pinning", blog post, 2018-04-05,
https://www.ralfj.de/blog/2018/04/05/a-formal-look-at-pinning.html: extends a RustBelt-style
model of type invariants with a pinned typestate, on paper (not mechanized in the post).

**[S5]** R. Jung, "Safe Intrusive Collections with Pinning", blog post, 2018-04-10,
https://www.ralfj.de/blog/2018/04/10/safe-intrusive-collections-with-pinning.html: without a
drop guarantee an entry can be deallocated while a collection still points to it (section 1.2);
adopts the guarantee "If the memory a Pin<T> points to is ever deallocated or otherwise
invalidated, drop has been called on it.", credited to cramertj (section 1.3).

**[S6]** Rust for Linux project, "The Safe Pinned Initialization Problem", web page,
https://rust-for-linux.com/the-safe-pinned-initialization-problem (author attribution not
verified): motivates the drop guarantee with an intrusive doubly linked list whose memory must
not be deallocated or reused (for example by `ptr::write`) without dropping it first, and
discusses pin projections.

**[S7]** Y. Guan and C. Pit-Claudel, "Precise Reasoning About Container-Internal Pointers with
Logical Pinning", CPP 2026, https://doi.org/10.1145/3779031.3779096 (arXiv:2509.23229v2): a
separation-logic borrowing model ("logical pinning") for container-internal pointers of
sequential programs, mechanized in the Rocq proof assistant using CFML (per its abstract). A
related use of the word "pinning"; per its abstract it is not a model of Rust's `Pin` API.

**[S8]** Y. Dai and Y. Feng, "PinChecker: Identifying Unsound Safe Abstractions of Rust Pinning
APIs", arXiv:2504.14500v2 (2025), https://doi.org/10.48550/arXiv.2504.14500: an intermediate
representation of library functions' pinning behaviour and a tool that synthesizes client
programs violating the pinning contract (bug finding, not proof). Venue not verified here.

**[S9]** Z. Rao, J. Zhou, H. Tian, X. Wang, H. Xu, "Annotating and Auditing the Safety
Properties of Unsafe Rust", arXiv:2504.21312v2 (2026), https://doi.org/10.48550/arXiv.2504.21312:
a standard for documenting safety properties of unsafe Rust APIs, with tooling; its treatment of
`core::pin` was not examined here.

**[S10]** G. Pîrlea, "A Formal Model of Rust's Pinning", talk at the Max Planck Institute for
Software Systems, September 2019, listed on the author's homepage https://pirlea.net/; no paper
or public mechanization was found, and the talk's content was not examined here.

**[S11]** withoutboats, "Pin", blog post, 2024-07-19, https://without.boats/blog/pin/: history
and design of `Pin`; describes how a destructor that moves out of a pin-projected field
(`Drop::drop` takes `&mut self`) violates the pinning guarantee.

**[S12]** withoutboats, "Pinned places", blog post, 2024-07-23,
https://without.boats/blog/pinned-places/: proposes language-level pinned places and a pinned
field annotation for safe pinned projections, with checks on the containing type.

**[S13]** Search for mechanized treatments (2026-11-21; terms: Rust Pin, pinning, structural
pinning, Coq/Rocq, Iris, Lean, mechanized): no mechanized proof of the structural-pinning
requirements was found. This is a negative search result, not a claim that none exists.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and
`python3`. The cheapest complete check, run from the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory, runs `lake build`, rejects `sorry`, `admit`,
`native_decide` and `axiom` declarations in the sources, checks with `Lean.collectAxioms` that
every declaration of the library depends on at most `propext`, `Classical.choice` and
`Quot.sound`, and recomputes, for every Lean name referenced by `results.json`, the statement
hash and the closure hash and compares them with `audit/statements.json`. Its docstring states
precisely what is hashed: the SHA-256 of Lean's `repr` of the theorem's type, and the SHA-256 of
the sorted, newline-joined texts `name : type := value` of every package-local constant reachable
from that type, with theorem bodies excluded. It prints `REVALIDATED` and exits with status 0
when every check passes.

A narrower axiom check by hand, from the package directory:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is outside the library target; it runs `#print axioms` on every
declaration referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`,
`positive_control_lean` and the ledger counterexamples), and each output line must list a subset
of `propext`, `Classical.choice`, `Quot.sound` (a definition may depend on no axiom).

The theorems depend on nothing outside the Lean toolchain, so they need rechecking only for a
different toolchain or after a change to `lean/`. The modeling bridges depend on the cited Rust
texts: to re-assess them for a newer Rust release, compare `library/core/src/pin.rs` at the new
revision with lines 509–633 and 696–847 at commit `fafcb2be486f2c24bbeb8417e5d32335df5d9a34`,
and `pin-project-internal/src/lib.rs` with lines 87–159 and 283–313 at commit
`f49edb9596fdf8bb09d48091755e522bb4a119be`; a change there affects the derived readings, not the
kernel-checked statements.
