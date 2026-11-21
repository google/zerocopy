/-!
# A toy heap model of pinning

This file defines a small, executable model of the memory-level content of Rust's `Pin`
contract. It is a toy: nothing here is extracted from, or mechanically tied to, the Rust
compiler or standard library.

* Memory is a list of *objects* (allocations); the address of an object is its index.
  An object has a list of *field locations*; a location is a pair `(address, field index)`.
* A field location holds at most one *leaf* value. A leaf carries a ghost identity, a flag
  recording whether its type implements `Unpin`, and an optional *self-pointer*.
* Two address-sensitive invariants are modelled:
  - a **self-reference** (`selfPtr`): the value in a field location stored that location's
    address (a pointer from a field location to itself). Pointers from one field to a
    sibling field of the same struct (as in compiler-generated async state machines) are
    not modelled;
  - an **intrusive list** (`registry`): an external list node that holds the address of a
    value, like a waiter queue whose entries live inside the waiting values.
* Primitive actions (`Act`) are the machine-level effects: allocation, pinning, establishing
  an address-sensitive invariant, moves, destructor runs, deallocation, writes without drop,
  and leaking.

The address-sensitive invariants are only ever *established* through a pinned location
holding a non-`Unpin` leaf (`Act.setSelf`, `Act.register` are no-ops otherwise). This builds
in the type author's obligation that a type relying on its own address is `!Unpin` and sets
up that reliance only through `Pin<&mut Self>`.
-/

namespace Toy.Pin

/-- A field location: base address of an allocation (an index into the heap) and field
index. -/
abbrev Loc := Nat × Nat

/-- A value occupying one field location.

* `id` is a ghost identity, assigned freshly by the machine; it lets the intrusive-list
  invariant tell "the value that registered" apart from "some value now at that address".
* `unpin` records whether the value's type implements `Unpin`.
* `selfPtr` is the address the value stored as its own (the self-reference), if any. -/
structure Leaf where
  id : Nat
  unpin : Bool
  selfPtr : Option Loc
  deriving DecidableEq, Repr

/-- An allocation.

* `fields`: contents of the field locations (`none` = empty / moved-out / dropped).
* `live`: the memory is allocated (not yet deallocated).
* `pinned`: a `Pin` to the whole object has been created (the object was pinned). At the
  level of primitive actions this flag is inert: protection is per field location
  (`pinnedFields`), see `pinObj_inert_in_core`. Safe programs (`SafeOp`) require it before a
  structural projection.
* `pinnedFields`: field indices for which a `Pin<&mut Field>` has been created.
* `leaked`: the object was leaked (`Act.forget`); safe programs may no longer drop or leak
  it (`SafeOp`), but references obtained earlier stay usable. -/
structure Obj where
  fields : List (Option Leaf)
  live : Bool
  pinned : Bool
  pinnedFields : List Nat
  leaked : Bool
  deriving DecidableEq, Repr

/-- A freshly allocated, unpinned, live object with the given field contents. -/
def Obj.fresh (fs : List (Option Leaf)) : Obj := ⟨fs, true, false, [], false⟩

/-- The leaf in field `i` of an object, if that field exists and is occupied. -/
def Obj.leaf (o : Obj) (i : Nat) : Option Leaf :=
  match o.fields[i]? with
  | some x => x
  | none => none

/-- Machine state: the heap, the external intrusive list (entries `(location, id)` meaning
"the list node expects the value with identity `id` at `location`"), and the next fresh
identity. -/
structure State where
  heap : List Obj
  registry : List (Loc × Nat)
  nextId : Nat
  deriving DecidableEq, Repr

/-- `modifyAt f l n` applies `f` to the `n`-th element of `l` (no-op when out of range). -/
def modifyAt {α : Type} (f : α → α) : List α → Nat → List α
  | [], _ => []
  | a :: as, 0 => f a :: as
  | a :: as, n + 1 => a :: modifyAt f as n

namespace State

/-- The empty machine. -/
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

/-- Apply `f` to the object at `b`. -/
def modifyObj (st : State) (b : Nat) (f : Obj → Obj) : State :=
  { st with heap := modifyAt f st.heap b }

/-- Set the contents of location `l` (no-op if the location does not exist). -/
def setLeaf (st : State) (l : Loc) (x : Option Leaf) : State :=
  st.modifyObj l.1 fun o => { o with fields := modifyAt (fun _ => x) o.fields l.2 }

/-- Append an object at the next free address `st.heap.length`. -/
def push (st : State) (o : Obj) : State :=
  { st with heap := st.heap ++ [o] }

end State

/-- Fresh leaves for a new allocation: `none` gives an empty field, `some u` a fresh leaf
whose type has `Unpin` flag `u`; identities are `n, n+1, ...` by position. -/
def mkFields : Nat → List (Option Bool) → List (Option Leaf)
  | _, [] => []
  | n, u :: us => (u.map fun b => ⟨n, b, none⟩) :: mkFields (n + 1) us

/-- Fields of the temporary that receives a value moved out of field index `i`: the value
keeps its field index, so that field types stay attached to indices. -/
def tempFields (i : Nat) (x : Option Leaf) : List (Option Leaf) :=
  List.replicate i none ++ [x]

/-- Primitive machine actions.

* `alloc fs`: allocate a fresh object (see `mkFields`).
* `pinObj b`: pin the object at `b` (`Box::pin`, `pin!`); by itself it protects no field
  location (only `pinField` does).
* `pinField l`: create a `Pin<&mut Field>` to location `l` (the result of a structural
  projection).
* `setSelf l`: the value at `l` stores its own address (e.g. `init(self: Pin<&mut Self>)`);
  effective only if `l` is a pinned location holding a non-`Unpin` leaf.
* `register l`: the value at `l` links itself into the external intrusive list; effective
  only if `l` is a pinned location holding a non-`Unpin` leaf.
* `moveOut l`: move the value at `l` into a fresh temporary object, leaving `l` empty.
* `moveObj b`: move all fields of `b` into a fresh object, leaving `b`'s fields empty.
* `swap l l'`: exchange the contents of two locations (`mem::swap`).
* `dropLeaf l`: run the destructor of the value at `l` in place; the destructor unlinks the
  value from the intrusive list *by its current address*.
* `dropTemp i`: `dropLeaf` at field `i` of the most recently allocated object (whatever its
  origin; safe programs use it only right after `moveOut` created a temporary).
* `dealloc b`: deallocate the object at `b`; its field contents are invalidated.
* `freeTemp`: `dealloc` of the most recently allocated object (same remark).
* `write l u`: write a fresh value (type `Unpin` flag `u`) into `l` *without* running the
  destructor of the previous contents (memory reuse).
* `forget b`: leak the object at `b` (set its `leaked` flag; nothing else changes). -/
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

namespace State

/-- Run the destructor of the value at `l` in place. -/
def dropAt (st : State) (l : Loc) : State :=
  match st.leafAt l with
  | some v =>
    { st.setLeaf l none with
      registry := st.registry.filter fun e => decide (e ≠ (l, v.id)) }
  | none => st

/-- Deallocate the object at `b`. -/
def deallocAt (st : State) (b : Nat) : State :=
  st.modifyObj b fun o => { o with fields := o.fields.map fun _ => none, live := false }

end State

/-- One primitive step of the machine. -/
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

/-- Run a list of actions. -/
def runActs : State → List Act → State
  | st, [] => st
  | st, a :: as => runActs (applyAct st a) as

/-- All states visited by a list of actions, starting with the initial one. -/
def states : State → List Act → List State
  | st, [] => [st]
  | st, a :: as => st :: states (applyAct st a) as

/-- `Always P st as`: every action of `as` satisfies `P` in the state in which it runs. -/
def Always (P : State → Act → Prop) : State → List Act → Prop
  | _, [] => True
  | st, a :: as => P st a ∧ Always P (applyAct st a) as

instance decAlways (P : State → Act → Prop) [h : ∀ st a, Decidable (P st a)] :
    ∀ st as, Decidable (Always P st as)
  | _, [] => isTrue trivial
  | st, a :: as =>
    have := decAlways P (applyAct st a) as
    inferInstanceAs (Decidable (P st a ∧ Always P (applyAct st a) as))

/-! ## Address-sensitive invariants -/

/-- **Self-reference invariant.** Every value whose self-pointer is set is located exactly
at the address it stored. Captures: a value that stored its own field location is never
observed with a dangling self-pointer. Only pointers from a field location to itself are
modelled, not pointers between sibling fields. -/
def SelfRefOK (st : State) : Prop :=
  ∀ l v, st.leafAt l = some v → v.selfPtr = none ∨ v.selfPtr = some l

/-- **Intrusive-list invariant.** Every entry `(l, id)` of the external list finds the very
value it registered (identity `id`) at address `l`. Captures: an external node holding a
value's address never dangles and never points at a different value. -/
def ListOK (st : State) : Prop :=
  ∀ e ∈ st.registry, (st.leafAt e.1).map Leaf.id = some e.2

/-- Both address-sensitive invariants. -/
def AddrInv (st : State) : Prop := SelfRefOK st ∧ ListOK st

/-- Location `l` is pinned (a `Pin<&mut Field>` to it was created) and currently holds a
value whose type is not `Unpin`. These are the values the pinning contract protects. -/
def PinnedNonUnpin (st : State) (l : Loc) : Prop :=
  st.isPinnedLoc l = true ∧ (st.leafAt l).map Leaf.unpin = some false

instance (st : State) (l : Loc) : Decidable (PinnedNonUnpin st l) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (st : State) : Decidable (ListOK st) :=
  inferInstanceAs (Decidable (∀ e ∈ st.registry, _))

/-! ### Decidability of `SelfRefOK` via a bounded check -/

/-- Executable bounded check equivalent to `SelfRefOK` (see `selfRefOK_iff_check`). -/
def selfRefCheck (st : State) : Bool :=
  (List.range st.heap.length).all fun b =>
    (List.range (st.width b)).all fun i =>
      (st.leafAt (b, i)).all fun v => decide (v.selfPtr = none ∨ v.selfPtr = some (b, i))

theorem State.leafAt_some_bounds {st : State} {l : Loc} {v : Leaf}
    (h : st.leafAt l = some v) : l.1 < st.heap.length ∧ l.2 < st.width l.1 := by
  unfold State.leafAt at h
  unfold State.width
  cases hb : st.heap[l.1]? with
  | none => simp [hb] at h
  | some o =>
    simp only [hb, Obj.leaf] at h
    cases hi : o.fields[l.2]? with
    | none => simp [hi] at h
    | some x =>
      refine ⟨?_, ?_⟩
      · exact (List.getElem?_eq_some_iff.mp hb).1
      · simp only
        exact (List.getElem?_eq_some_iff.mp hi).1

theorem selfRefOK_iff_check (st : State) : SelfRefOK st ↔ selfRefCheck st = true := by
  unfold SelfRefOK selfRefCheck
  constructor
  · intro h
    simp only [List.all_eq_true, List.mem_range]
    intro b _ i _
    cases hv : st.leafAt (b, i) with
    | none => rfl
    | some v => simpa [Option.all] using h (b, i) v hv
  · intro h l v hv
    have hbd := State.leafAt_some_bounds hv
    simp only [List.all_eq_true, List.mem_range] at h
    have := h l.1 hbd.1 l.2 hbd.2
    rw [hv] at this
    simpa [Option.all] using this

instance (st : State) : Decidable (SelfRefOK st) :=
  decidable_of_iff _ (selfRefOK_iff_check st).symm

instance (st : State) : Decidable (AddrInv st) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## The pinning contract, as predicates on actions -/

/-- **No move of a pinned non-`Unpin` value.** The action does not move a value out of a
pinned location whose value is not `Unpin`. In the model every such move is either a move
through a `&mut` (swap, replace, take, moving the enclosing object) or a compiler-inserted
move (the drop glue of a packed struct); this is the formal counterpart of "no `&mut` to a
pinned non-`Unpin` value is used to move it". -/
def NoPinnedMove (st : State) : Act → Prop
  | .moveOut l => ¬ PinnedNonUnpin st l
  | .moveObj b => ∀ i < st.width b, ¬ PinnedNonUnpin st (b, i)
  | .swap l l' => ¬ PinnedNonUnpin st l ∧ ¬ PinnedNonUnpin st l'
  | _ => True

/-- **Drop guarantee.** The action does not invalidate (deallocate) or reuse (overwrite) the
memory of a pinned non-`Unpin` value whose destructor has not run. -/
def DropGuaranteeAct (st : State) : Act → Prop
  | .write l _ => ¬ PinnedNonUnpin st l
  | .dealloc b => ∀ i < st.width b, ¬ PinnedNonUnpin st (b, i)
  | .freeTemp => ∀ i < st.width (st.heap.length - 1),
      ¬ PinnedNonUnpin st (st.heap.length - 1, i)
  | _ => True

instance (st : State) (a : Act) : Decidable (NoPinnedMove st a) := by
  cases a <;> unfold NoPinnedMove <;> infer_instance

instance (st : State) (a : Act) : Decidable (DropGuaranteeAct st a) := by
  cases a <;> unfold DropGuaranteeAct <;> infer_instance

end Toy.Pin
