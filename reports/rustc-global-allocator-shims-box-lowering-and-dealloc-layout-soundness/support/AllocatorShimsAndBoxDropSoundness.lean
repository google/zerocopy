/-!
# Global allocator calls, `Box` construction and destruction, and deallocation layouts

A small, executable model of four layers of the Rust heap interface and of the cleanup code the
compiler emits for a `Box`, with kernel-checked statements about them. The file imports nothing.

Layers (bottom to top):

1. **The global allocator contract** (`rustAlloc`, `rustDealloc`). These stand for the symbols
   `__rust_alloc(size, align)` and `__rust_dealloc(ptr, size, align)`, whose contract is that of
   `GlobalAlloc::alloc` and `GlobalAlloc::dealloc`: a zero-sized request is undefined behaviour,
   and a deallocation must name a block that is currently allocated, with the same layout the block
   was allocated with.
2. **The `Global` allocator** (`globalAllocate`, `globalDeallocate`). It never forwards a
   zero-sized request: allocation returns a dangling, well-aligned address and deallocation does
   nothing.
3. **`Box` construction** (`boxNewUninit`, `BoxVal.writeAll`, `BoxVal.assumeInit`, `boxNew`).
   `Box::new(x)` is `box_new_uninit(LAYOUT)` followed by a store of `x` that drops nothing and
   cannot fail.
4. **`Box` destruction** (`dropWhere`, `boxFree`, `cleanupWith`). The cleanup for a box runs the
   destructors of some of the fields of the pointee and then gives the block back. Which fields is
   decided by a *flag policy*; three policies matter:
   * `dropLiveFieldsThenFreeBacking`: exactly the fields that currently hold a value (what drop
     elaboration emits for a `Box<T>` out of which fields may have been moved);
   * `freeBackingOnly`: no field (what is emitted for `Box<MaybeUninit<T>>`, whose pointee type
     has no drop glue);
   * `fullDropThenFreeBacking`: every field (the drop glue of a whole `T`; wrong whenever some
     field holds no value).

What is proved (section "Main statements" lists the theorem names):

* a flag policy causes no undefined behaviour exactly when it never selects a field without a
  value, and leaves no field undestroyed exactly when it selects every field with a value; the
  field-selective policy does both, runs each destructor exactly once, and gives the block back
  exactly once;
* a zero-sized box is created and destroyed without any allocator call, and its address is
  non-zero and a multiple of the alignment;
* in every well-formed heap history each deallocation event is preceded by an allocation event
  with the same block and the same `(size, align)`, and the destructor of a box deallocates with
  exactly the layout that `box_new_uninit` allocated with;
* two families of counterexamples: a whole-value drop after a field was moved out (or was never
  written), and a deallocation of a zero-sized box's address or with a different alignment.

Not modelled: reallocation, allocators other than the global one, unsized pointees, destructors
that unwind, and the contents of memory (only which fields hold a value).

Every definition is marked `noncomputable`. This only tells Lean to generate no compiled code
(and therefore none of the compiler's auxiliary recursive helpers) for it; the definitions are
ordinary structural recursions that the kernel unfolds, which is what the `decide` proofs in the
last section rely on.
-/

namespace AllocBox

/-! ## Two lemmas about conditionals

Stated here so that the file depends on no particular name in the core library. -/

theorem ifPos {c : Prop} [h : Decidable c] (hc : c) {α : Sort u} {t e : α} : (if c then t else e) = t :=
  match h with
  | isTrue _ => rfl
  | isFalse hn => absurd hc hn

theorem ifNeg {c : Prop} [h : Decidable c] (hnc : ¬c) {α : Sort u} {t e : α} : (if c then t else e) = e :=
  match h with
  | isTrue hc => absurd hc hnc
  | isFalse _ => rfl

/-! ## Outcomes -/

/-- The ways an operation of the model can be undefined behaviour. -/
inductive UB where
  /-- `__rust_alloc` called with size zero. -/
  | allocZeroSize
  /-- `__rust_alloc` called with a size that, rounded up to the alignment, exceeds `isize::MAX`. -/
  | allocInvalidLayout
  /-- `__rust_dealloc` called with size zero. -/
  | deallocZeroSize
  /-- `__rust_dealloc` called on an address that is not the start of a heap block. -/
  | deallocDangling
  /-- `__rust_dealloc` called on a block that is not currently allocated. -/
  | deallocNotLive
  /-- `__rust_dealloc` called with a layout other than the one the block was allocated with. -/
  | deallocLayoutMismatch
  /-- A destructor was run on, or a value was read from, a field that holds no value. -/
  | dropOfMovedOrUninit
  deriving DecidableEq

/-- Result of an operation: a value, undefined behaviour, or an abort after allocation failure. -/
inductive Outcome (α : Type) where
  | ok (a : α)
  | ub (e : UB)
  | oom
  deriving DecidableEq

namespace Outcome

noncomputable def map {α β : Type} (f : α → β) : Outcome α → Outcome β
  | ok a => ok (f a)
  | ub e => ub e
  | oom => oom

noncomputable def isOk {α : Type} : Outcome α → Bool
  | ok _ => true
  | _ => false

theorem map_ok_iff {α β : Type} (f : α → β) (o : Outcome α) (b : β) :
    o.map f = ok b ↔ ∃ a, o = ok a ∧ f a = b := by
  cases o with
  | ok a =>
    constructor
    · intro h; exact ⟨a, rfl, Outcome.ok.inj h⟩
    · intro ⟨a', ha, hf⟩; cases ha; exact congrArg ok hf
  | ub e =>
    constructor
    · intro h; cases h
    · intro ⟨_, ha, _⟩; cases ha
  | oom =>
    constructor
    · intro h; cases h
    · intro ⟨_, ha, _⟩; cases ha

end Outcome

/-! ## Layouts, pointers, blocks, events -/

/-- A layout: a size in bytes and an alignment given by its base-2 logarithm, so the alignment is
a power of two by construction (as with `core::mem::Alignment`). -/
structure Layout where
  size : Nat
  alignLog2 : Nat
  deriving DecidableEq

/-- The alignment in bytes. -/
noncomputable def Layout.align (l : Layout) : Nat := 2 ^ l.alignLog2

/-- The `Layout` invariant for a target whose `isize::MAX` is `imax`:
`size <= isize::MAX + 1 - align`, written without subtraction. -/
noncomputable def Layout.Valid (imax : Nat) (l : Layout) : Prop := l.size + l.align ≤ imax + 1

noncomputable instance (imax : Nat) (l : Layout) : Decidable (l.Valid imax) :=
  inferInstanceAs (Decidable (l.size + l.align ≤ imax + 1))

abbrev BlockId := Nat

/-- A pointer as the allocator interface sees it. -/
inductive Ptr where
  /-- The start of the heap block with this identity. -/
  | block (id : BlockId)
  /-- A bare address that belongs to no block. -/
  | dangling (addr : Nat)
  deriving DecidableEq

/-- A live heap block: identity and the layout it was allocated with. -/
structure Block where
  id : BlockId
  layout : Layout
  deriving DecidableEq

/-- What the allocator has been asked to do, in order. -/
inductive Event where
  | alloc (id : BlockId) (l : Layout)
  | dealloc (id : BlockId) (l : Layout)
  deriving DecidableEq

/-- The layout of the live block with identity `id`, if there is one. -/
noncomputable def find : List Block → BlockId → Option Layout
  | [], _ => none
  | b :: bs, id => if b.id = id then some b.layout else find bs id

/-- Removes every block with identity `id`. -/
noncomputable def remove : List Block → BlockId → List Block
  | [], _ => []
  | b :: bs, id => if b.id = id then remove bs id else b :: remove bs id

theorem find_remove_self (bs : List Block) (id : BlockId) : find (remove bs id) id = none := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show find (if b.id = id then remove bs id else b :: remove bs id) id = none
    cases hb : decide (b.id = id) with
    | true =>
      have h : b.id = id := of_decide_eq_true hb
      rw [ifPos h]; exact ih
    | false =>
      have h : ¬ b.id = id := of_decide_eq_false hb
      rw [ifNeg h]
      show (if b.id = id then some b.layout else find (remove bs id) id) = none
      rw [ifNeg h]; exact ih

theorem find_remove_other (bs : List Block) (id j : BlockId) (hne : j ≠ id) :
    find (remove bs id) j = find bs j := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show find (if b.id = id then remove bs id else b :: remove bs id) j
        = (if b.id = j then some b.layout else find bs j)
    cases hb : decide (b.id = id) with
    | true =>
      have h : b.id = id := of_decide_eq_true hb
      have hj : ¬ b.id = j := fun e => hne (e.symm.trans h)
      rw [ifPos h, ifNeg hj]; exact ih
    | false =>
      have h : ¬ b.id = id := of_decide_eq_false hb
      rw [ifNeg h]
      show (if b.id = j then some b.layout else find (remove bs id) j)
          = (if b.id = j then some b.layout else find bs j)
      rw [ih]

theorem find_remove_some (bs : List Block) (id j : BlockId) (l : Layout)
    (h : find (remove bs id) j = some l) : find bs j = some l := by
  cases hj : decide (j = id) with
  | true =>
    have e : j = id := of_decide_eq_true hj
    rw [e, find_remove_self] at h; cases h
  | false =>
    have e : j ≠ id := of_decide_eq_false hj
    rw [find_remove_other bs id j e] at h; exact h

/-! ## The heap and the global allocator contract -/

/-- The allocator state: target bound, live blocks, the next unused block identity, the history
of successful allocator operations (oldest first), and call counters. -/
structure Heap where
  /-- `isize::MAX` of the target. -/
  isizeMax : Nat
  live : List Block
  next : BlockId
  events : List Event
  /-- Calls of `__rust_alloc`, including calls that returned null. -/
  allocCalls : Nat
  /-- Calls of `__rust_dealloc`. -/
  deallocCalls : Nat
  deriving DecidableEq

/-- An empty heap for a target with the given `isize::MAX`. -/
noncomputable def Heap.empty (imax : Nat) : Heap :=
  { isizeMax := imax, live := [], next := 0, events := [], allocCalls := 0, deallocCalls := 0 }

/-- `__rust_alloc(size, align)` under the `GlobalAlloc::alloc` contract. `avail` is the
allocator's answer: `true` yields a fresh block, `false` yields null (`none`). -/
noncomputable def rustAlloc (h : Heap) (l : Layout) (avail : Bool) : Outcome (Option BlockId × Heap) :=
  if l.size = 0 then .ub .allocZeroSize
  else if l.Valid h.isizeMax then
    if avail then
      .ok (some h.next,
        { h with
          live := ⟨h.next, l⟩ :: h.live
          next := h.next + 1
          events := h.events ++ [Event.alloc h.next l]
          allocCalls := h.allocCalls + 1 })
    else
      .ok (none, { h with allocCalls := h.allocCalls + 1 })
  else .ub .allocInvalidLayout

/-- `__rust_dealloc(ptr, size, align)` under the `GlobalAlloc::dealloc` contract. -/
noncomputable def rustDealloc (h : Heap) (p : Ptr) (l : Layout) : Outcome Heap :=
  if l.size = 0 then .ub .deallocZeroSize
  else
    match p with
    | .dangling _ => .ub .deallocDangling
    | .block id =>
      match find h.live id with
      | none => .ub .deallocNotLive
      | some l₀ =>
        if l₀ = l then
          .ok { h with
                live := remove h.live id
                events := h.events ++ [Event.dealloc id l]
                deallocCalls := h.deallocCalls + 1 }
        else .ub .deallocLayoutMismatch

/-! ## The `Global` allocator: zero-sized requests never reach the contract above -/

/-- `Global.allocate(layout)`: a zero-sized request returns the dangling address `align` without
calling the allocator. `none` is a null result. -/
noncomputable def globalAllocate (h : Heap) (l : Layout) (avail : Bool) : Outcome (Option Ptr × Heap) :=
  if l.size = 0 then .ok (some (.dangling l.align), h)
  else
    match rustAlloc h l avail with
    | .ok (some id, h') => .ok (some (.block id), h')
    | .ok (none, h') => .ok (none, h')
    | .ub e => .ub e
    | .oom => .oom

/-- `Global.deallocate(ptr, layout)`: a zero-sized layout does nothing. -/
noncomputable def globalDeallocate (h : Heap) (p : Ptr) (l : Layout) : Outcome Heap :=
  if l.size = 0 then .ok h else rustDealloc h p l

/-! ## Boxes -/

/-- One field of the pointee: whether it currently holds a value the box is responsible for,
and how many times its destructor has run. -/
structure Slot where
  init : Bool
  runs : Nat
  deriving DecidableEq

/-- A box value: its pointer, the layout of its pointee type, the state of the pointee's fields,
and whether the pointee type has drop glue (`false` for `Box<MaybeUninit<T>>`). -/
structure BoxVal where
  ptr : Ptr
  layout : Layout
  slots : List Slot
  hasDropGlue : Bool
  deriving DecidableEq

/-- `box_new_uninit(LAYOUT)`, giving a `Box<MaybeUninit<T>>` for a `T` with `fields` fields.
A null result from the allocator becomes an abort (`handle_alloc_error`). -/
noncomputable def boxNewUninit (h : Heap) (l : Layout) (fields : Nat) (avail : Bool) : Outcome (BoxVal × Heap) :=
  match globalAllocate h l avail with
  | .ok (some p, h') =>
    .ok ({ ptr := p, layout := l, slots := List.replicate fields ⟨false, 0⟩, hasDropGlue := false }, h')
  | .ok (none, _) => .oom
  | .ub e => .ub e
  | .oom => .oom

/-- The store `*ptr = x` that `write_via_move(ptr, x)` becomes: every field now holds a value.
Nothing is dropped and nothing can fail. -/
noncomputable def BoxVal.writeAll (b : BoxVal) : BoxVal :=
  { b with slots := b.slots.map (fun s => { s with init := true }) }

/-- `assume_init` (or the transmute at the end of `Box::new`): the pointee type is now `T`. -/
noncomputable def BoxVal.assumeInit (b : BoxVal) : BoxVal := { b with hasDropGlue := true }

/-- `Box::new(x)`. -/
noncomputable def boxNew (h : Heap) (l : Layout) (fields : Nat) (avail : Bool) : Outcome (BoxVal × Heap) :=
  (boxNewUninit h l fields avail).map (fun r => (r.1.writeAll.assumeInit, r.2))

/-- State of field `i`. -/
noncomputable def getSlot : List Slot → Nat → Option Slot
  | [], _ => none
  | s :: _, 0 => some s
  | _ :: ss, i + 1 => getSlot ss i

/-- Replaces the state of field `i`. -/
noncomputable def setSlot : List Slot → Nat → Slot → List Slot
  | [], _, _ => []
  | _ :: ss, 0, t => t :: ss
  | s :: ss, i + 1, t => s :: setSlot ss i t

/-- Moves field `i` out of the box: the box is no longer responsible for it and its destructor
does not run. Reading a field that holds no value is undefined behaviour. -/
noncomputable def BoxVal.moveOutField (b : BoxVal) (i : Nat) : Outcome BoxVal :=
  match getSlot b.slots i with
  | some s =>
    if s.init then .ok { b with slots := setSlot b.slots i { s with init := false } }
    else .ub .dropOfMovedOrUninit
  | none => .ub .dropOfMovedOrUninit

/-- Writes field `i` through a raw pointer (no drop of what was there). -/
noncomputable def BoxVal.writeField (b : BoxVal) (i : Nat) : BoxVal :=
  match getSlot b.slots i with
  | some s => { b with slots := setSlot b.slots i { s with init := true } }
  | none => b

/-! ## Destruction -/

/-- Runs the destructor of one field. -/
noncomputable def Slot.runDtor (s : Slot) : Outcome Slot :=
  if s.init then .ok ⟨false, s.runs + 1⟩ else .ub .dropOfMovedOrUninit

/-- State of a field after the field-selective drop: its destructor has run if and only if it
held a value. -/
noncomputable def Slot.afterDrop (s : Slot) : Slot :=
  if s.init then ⟨false, s.runs + 1⟩ else s

/-- The drop ladder under a flag policy: visits the fields in order and runs the destructor of
each field the policy selects. -/
noncomputable def dropWhere (flag : Slot → Bool) : List Slot → Outcome (List Slot)
  | [] => .ok []
  | s :: ss =>
    if flag s then
      match s.runDtor with
      | .ok s' => (dropWhere flag ss).map (fun r => s' :: r)
      | .ub e => .ub e
      | .oom => .oom
    else (dropWhere flag ss).map (fun r => s :: r)

/-- `<Box<T> as Drop>::drop`: computes the layout from the pointee type and deallocates unless
the size is zero. It never touches the contents. -/
noncomputable def boxFree (h : Heap) (b : BoxVal) : Outcome Heap := globalDeallocate h b.ptr b.layout

/-- Cleanup of a box under a flag policy: the ladder, then the box destructor. -/
noncomputable def cleanupWith (flag : Slot → Bool) (h : Heap) (b : BoxVal) : Outcome (BoxVal × Heap) :=
  match dropWhere flag b.slots with
  | .ok ss => (boxFree h b).map (fun h' => ({ b with slots := ss }, h'))
  | .ub e => .ub e
  | .oom => .oom

/-- Field-selective cleanup: drop the fields that hold a value, then free the block. -/
noncomputable def dropLiveFieldsThenFreeBacking : Heap → BoxVal → Outcome (BoxVal × Heap) :=
  cleanupWith (fun s => s.init)

/-- Cleanup that runs no destructor: free the block only. -/
noncomputable def freeBackingOnly : Heap → BoxVal → Outcome (BoxVal × Heap) :=
  cleanupWith (fun _ => false)

/-- Whole-value cleanup: run every field's destructor, then free the block. -/
noncomputable def fullDropThenFreeBacking : Heap → BoxVal → Outcome (BoxVal × Heap) :=
  cleanupWith (fun _ => true)

/-- What is emitted where a box goes out of scope, on the normal path and on the unwind path
alike: field-selective cleanup if the pointee type has drop glue, otherwise the block only. -/
noncomputable def boxDrop (h : Heap) (b : BoxVal) : Outcome (BoxVal × Heap) :=
  if b.hasDropGlue then dropLiveFieldsThenFreeBacking h b else freeBackingOnly h b

/-- Number of destructor runs recorded in a field list. -/
noncomputable def totalRuns : List Slot → Nat
  | [] => 0
  | s :: ss => s.runs + totalRuns ss

/-- Number of fields that hold a value. -/
noncomputable def countInit : List Slot → Nat
  | [] => 0
  | s :: ss => (if s.init then 1 else 0) + countInit ss

/-! ## The ladder under an arbitrary flag policy -/

/-- A policy that never selects a field without a value. -/
noncomputable def FlagsSound (flag : Slot → Bool) (ss : List Slot) : Prop :=
  ∀ s, s ∈ ss → flag s = true → s.init = true

/-- A policy that selects every field with a value. -/
noncomputable def FlagsComplete (flag : Slot → Bool) (ss : List Slot) : Prop :=
  ∀ s, s ∈ ss → s.init = true → flag s = true

/-- State of a field after a sound policy has visited it. -/
noncomputable def Slot.afterFlag (flag : Slot → Bool) (s : Slot) : Slot :=
  if flag s then ⟨false, s.runs + 1⟩ else s

/-- A sound policy causes no undefined behaviour, and its effect on each field is `afterFlag`. -/
theorem dropWhere_of_sound (flag : Slot → Bool) (ss : List Slot) (hs : FlagsSound flag ss) :
    dropWhere flag ss = .ok (ss.map (Slot.afterFlag flag)) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have ih' := ih (fun t ht hf => hs t (List.mem_cons_of_mem s ht) hf)
    cases hf : flag s with
    | true =>
      have hi : s.init = true := hs s (List.mem_cons_self) hf
      show (if flag s = true then
              match s.runDtor with
              | .ok s' => (dropWhere flag ss).map (fun r => s' :: r)
              | .ub e => .ub e
              | .oom => .oom
            else (dropWhere flag ss).map (fun r => s :: r))
          = .ok (Slot.afterFlag flag s :: ss.map (Slot.afterFlag flag))
      rw [ifPos hf]
      have hr : s.runDtor = .ok ⟨false, s.runs + 1⟩ := by
        show (if s.init = true then Outcome.ok (⟨false, s.runs + 1⟩ : Slot) else .ub .dropOfMovedOrUninit) = _
        rw [ifPos hi]
      have ha : Slot.afterFlag flag s = ⟨false, s.runs + 1⟩ := by
        show (if flag s = true then (⟨false, s.runs + 1⟩ : Slot) else s) = _
        rw [ifPos hf]
      rw [hr, ih', ha]; rfl
    | false =>
      show (if flag s = true then
              match s.runDtor with
              | .ok s' => (dropWhere flag ss).map (fun r => s' :: r)
              | .ub e => .ub e
              | .oom => .oom
            else (dropWhere flag ss).map (fun r => s :: r))
          = .ok (Slot.afterFlag flag s :: ss.map (Slot.afterFlag flag))
      have hn : ¬ flag s = true := by rw [hf]; exact Bool.noConfusion
      rw [ifNeg hn]
      have ha : Slot.afterFlag flag s = s := by
        show (if flag s = true then (⟨false, s.runs + 1⟩ : Slot) else s) = _
        rw [ifNeg hn]
      rw [ih', ha]; rfl

/-- A policy that selects some field without a value is undefined behaviour. -/
theorem dropWhere_ub_of_not_sound (flag : Slot → Bool) (ss : List Slot)
    (hbad : ∃ s, s ∈ ss ∧ flag s = true ∧ s.init = false) :
    dropWhere flag ss = .ub .dropOfMovedOrUninit := by
  induction ss with
  | nil =>
    cases hbad with
    | intro s hs => cases hs.1
  | cons s ss ih =>
    show (if flag s = true then
            match s.runDtor with
            | .ok s' => (dropWhere flag ss).map (fun r => s' :: r)
            | .ub e => .ub e
            | .oom => .oom
          else (dropWhere flag ss).map (fun r => s :: r)) = .ub .dropOfMovedOrUninit
    cases hf : flag s with
    | true =>
      rw [ifPos rfl]
      cases hi : s.init with
      | false =>
        have hr : s.runDtor = .ub .dropOfMovedOrUninit := by
          show (if s.init = true then Outcome.ok (⟨false, s.runs + 1⟩ : Slot) else .ub .dropOfMovedOrUninit) = _
          rw [hi]; rfl
        rw [hr]
      | true =>
        have hr : s.runDtor = .ok ⟨false, s.runs + 1⟩ := by
          show (if s.init = true then Outcome.ok (⟨false, s.runs + 1⟩ : Slot) else .ub .dropOfMovedOrUninit) = _
          rw [hi]; rfl
        rw [hr]
        have hrest : ∃ t, t ∈ ss ∧ flag t = true ∧ t.init = false := by
          cases hbad with
          | intro t ht =>
            cases List.mem_cons.mp ht.1 with
            | inl e => rw [e, hi] at ht; cases ht.2.2
            | inr m => exact ⟨t, m, ht.2⟩
        show (dropWhere flag ss).map (fun r => (⟨false, s.runs + 1⟩ : Slot) :: r) = .ub .dropOfMovedOrUninit
        rw [ih hrest]; rfl
    | false =>
      have hn : ¬ (false = true) := Bool.noConfusion
      rw [ifNeg hn]
      have hrest : ∃ t, t ∈ ss ∧ flag t = true ∧ t.init = false := by
        cases hbad with
        | intro t ht =>
          cases List.mem_cons.mp ht.1 with
          | inl e => rw [e, hf] at ht; cases ht.2.1
          | inr m => exact ⟨t, m, ht.2⟩
      rw [ih hrest]; rfl

/-- Soundness of the flags is exactly absence of undefined behaviour in the ladder. -/
theorem dropWhere_ok_iff_sound (flag : Slot → Bool) (ss : List Slot) :
    (∃ r, dropWhere flag ss = .ok r) ↔ FlagsSound flag ss := by
  constructor
  · intro hok s hs hf
    cases hi : s.init with
    | true => rfl
    | false =>
      have hub := dropWhere_ub_of_not_sound flag ss ⟨s, hs, hf, hi⟩
      cases hok with
      | intro r hr => rw [hub] at hr; cases hr
  · intro hsound
    exact ⟨_, dropWhere_of_sound flag ss hsound⟩

/-- After a sound policy, a field still holds a value exactly when it held one and was not
selected. Such a field is never destroyed: the block is freed next. -/
theorem afterFlag_init (flag : Slot → Bool) (s : Slot) :
    (Slot.afterFlag flag s).init = (s.init && !flag s) := by
  show (if flag s = true then (⟨false, s.runs + 1⟩ : Slot) else s).init = (s.init && !flag s)
  cases hf : flag s with
  | true => rw [ifPos rfl]; show false = (s.init && !true); cases s.init <;> rfl
  | false =>
    have hn : ¬ (false = true) := Bool.noConfusion
    rw [ifNeg hn]; show s.init = (s.init && !false); cases s.init <;> rfl

/-- A sound and complete policy leaves no field holding a value. -/
theorem no_field_left_of_sound_complete (flag : Slot → Bool) (ss : List Slot)
    (hc : FlagsComplete flag ss) :
    ∀ t, t ∈ ss.map (Slot.afterFlag flag) → t.init = false := by
  intro t ht
  cases List.mem_map.mp ht with
  | intro s hs =>
    rw [← hs.2, afterFlag_init]
    cases hi : s.init with
    | false => rfl
    | true => rw [hc s hs.1 hi]; rfl

/-- A policy that misses a field with a value leaves that field undestroyed. -/
theorem field_left_of_not_complete (flag : Slot → Bool) (ss : List Slot)
    (hmiss : ∃ s, s ∈ ss ∧ s.init = true ∧ flag s = false) :
    ∃ t, t ∈ ss.map (Slot.afterFlag flag) ∧ t.init = true := by
  cases hmiss with
  | intro s hs =>
    refine ⟨Slot.afterFlag flag s, List.mem_map.mpr ⟨s, hs.1, rfl⟩, ?_⟩
    rw [afterFlag_init, hs.2.1, hs.2.2]; rfl

/-! ### The three policies -/

theorem afterFlag_init_eq_afterDrop (s : Slot) : Slot.afterFlag (fun t => t.init) s = s.afterDrop := rfl

theorem map_afterFlag_init (ss : List Slot) :
    ss.map (Slot.afterFlag (fun t => t.init)) = ss.map Slot.afterDrop := rfl

/-- The field-selective ladder never fails and has the effect `afterDrop` on every field. -/
theorem dropWhere_init (ss : List Slot) :
    dropWhere (fun s => s.init) ss = .ok (ss.map Slot.afterDrop) :=
  dropWhere_of_sound (fun s => s.init) ss (fun _ _ h => h)

theorem map_afterFlag_none (ss : List Slot) : ss.map (Slot.afterFlag (fun _ => false)) = ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show Slot.afterFlag (fun _ => false) s :: ss.map (Slot.afterFlag (fun _ => false)) = s :: ss
    rw [ih]; rfl

/-- The empty policy never fails and changes nothing. -/
theorem dropWhere_none (ss : List Slot) : dropWhere (fun _ => false) ss = .ok ss := by
  have h := dropWhere_of_sound (fun _ => false) ss (fun _ _ hf => Bool.noConfusion hf)
  rw [map_afterFlag_none] at h; exact h

/-- The whole-value ladder is undefined behaviour as soon as one field holds no value. -/
theorem dropWhere_all_ub (ss : List Slot) (h : ∃ s, s ∈ ss ∧ s.init = false) :
    dropWhere (fun _ => true) ss = .ub .dropOfMovedOrUninit := by
  cases h with
  | intro s hs => exact dropWhere_ub_of_not_sound (fun _ => true) ss ⟨s, hs.1, rfl, hs.2⟩

/-- The whole-value ladder succeeds exactly when every field holds a value. -/
theorem dropWhere_all_ok_iff (ss : List Slot) :
    (∃ r, dropWhere (fun _ => true) ss = .ok r) ↔ ∀ s, s ∈ ss → s.init = true := by
  rw [dropWhere_ok_iff_sound]
  constructor
  · intro h s hs; exact h s hs rfl
  · intro h s hs _; exact h s hs

theorem afterDrop_init (s : Slot) : s.afterDrop.init = false := by
  show (if s.init = true then (⟨false, s.runs + 1⟩ : Slot) else s).init = false
  cases hi : s.init with
  | true => rw [ifPos rfl]
  | false =>
    have hn : ¬ (false = true) := Bool.noConfusion
    rw [ifNeg hn]; exact hi

theorem afterDrop_runs (s : Slot) : s.afterDrop.runs = s.runs + (if s.init then 1 else 0) := by
  show (if s.init = true then (⟨false, s.runs + 1⟩ : Slot) else s).runs = s.runs + (if s.init = true then 1 else 0)
  cases hi : s.init with
  | true => rw [ifPos rfl, ifPos rfl]
  | false =>
    have hn : ¬ (false = true) := Bool.noConfusion
    rw [ifNeg hn, ifNeg hn]; rfl

/-- After the field-selective ladder no field holds a value. -/
theorem afterDrop_no_field_left (ss : List Slot) : ∀ t, t ∈ ss.map Slot.afterDrop → t.init = false := by
  intro t ht
  cases List.mem_map.mp ht with
  | intro s hs => rw [← hs.2]; exact afterDrop_init s

/-- Destructor runs added by the field-selective ladder: one per field that held a value. -/
theorem totalRuns_afterDrop (ss : List Slot) :
    totalRuns (ss.map Slot.afterDrop) = totalRuns ss + countInit ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show s.afterDrop.runs + totalRuns (ss.map Slot.afterDrop)
        = (s.runs + totalRuns ss) + ((if s.init = true then 1 else 0) + countInit ss)
    rw [ih, afterDrop_runs]
    exact Nat.add_add_add_comm _ _ _ _

/-- Running the field-selective ladder a second time runs no destructor. -/
theorem afterDrop_idempotent (s : Slot) : s.afterDrop.afterDrop = s.afterDrop := by
  show (if s.afterDrop.init = true then (⟨false, s.afterDrop.runs + 1⟩ : Slot) else s.afterDrop) = s.afterDrop
  have hn : ¬ (s.afterDrop.init = true) := by rw [afterDrop_init]; exact Bool.noConfusion
  rw [ifNeg hn]

/-! ## Ownership of a block by a box, and freeing it -/

/-- The box and the heap agree: a pointee of non-zero size lives in a live block allocated with
the pointee's layout; a zero-sized pointee has the dangling address `align`. -/
noncomputable def Owns (h : Heap) (b : BoxVal) : Prop :=
  match b.ptr with
  | .block id => find h.live id = some b.layout ∧ b.layout.size ≠ 0
  | .dangling a => b.layout.size = 0 ∧ a = b.layout.align

/-- The block of the box is no longer live. -/
noncomputable def Released (h : Heap) (b : BoxVal) : Prop :=
  match b.ptr with
  | .block id => find h.live id = none
  | .dangling _ => True

/-- Freeing an owned box succeeds; a non-zero-sized box causes exactly one deallocation call,
with the box's own layout, and its block is released; a zero-sized box leaves the heap as it is. -/
theorem boxFree_of_owns (h : Heap) (b : BoxVal) (ho : Owns h b) :
    ∃ h', boxFree h b = .ok h' ∧ Released h' b
      ∧ h'.allocCalls = h.allocCalls
      ∧ h'.deallocCalls = h.deallocCalls + (if b.layout.size = 0 then 0 else 1)
      ∧ (b.layout.size = 0 → h' = h)
      ∧ (∀ id, b.ptr = .block id → h'.events = h.events ++ [Event.dealloc id b.layout]) := by
  cases b with
  | mk ptr layout slots glue =>
    cases ptr with
    | dangling a =>
      have hz : layout.size = 0 := ho.1
      refine ⟨h, ?_, True.intro, rfl, ?_, fun _ => rfl, ?_⟩
      · show (if layout.size = 0 then Outcome.ok h else rustDealloc h (.dangling a) layout) = .ok h
        rw [ifPos hz]
      · show h.deallocCalls = h.deallocCalls + (if layout.size = 0 then 0 else 1)
        rw [ifPos hz]; rfl
      · intro id hid; cases hid
    | block id =>
      have hf : find h.live id = some layout := ho.1
      have hnz : layout.size ≠ 0 := ho.2
      refine ⟨{ h with live := remove h.live id
                       events := h.events ++ [Event.dealloc id layout]
                       deallocCalls := h.deallocCalls + 1 }, ?_, ?_, rfl, ?_, ?_, ?_⟩
      · show (if layout.size = 0 then Outcome.ok h else rustDealloc h (.block id) layout) = _
        rw [ifNeg hnz]
        show (if layout.size = 0 then Outcome.ub UB.deallocZeroSize
              else match find h.live id with
                | none => .ub .deallocNotLive
                | some l₀ =>
                  if l₀ = layout then
                    .ok { h with live := remove h.live id
                                 events := h.events ++ [Event.dealloc id layout]
                                 deallocCalls := h.deallocCalls + 1 }
                  else .ub .deallocLayoutMismatch) = _
        rw [ifNeg hnz, hf]
        show (if layout = layout then _ else _) = _
        rw [ifPos rfl]
      · exact find_remove_self h.live id
      · show h.deallocCalls + 1 = h.deallocCalls + (if layout.size = 0 then 0 else 1)
        rw [ifNeg hnz]
      · intro hz; exact absurd hz hnz
      · intro id' hid; cases hid; rfl

/-! ## Main statement 1: cleanup of a box with moved-out or never-written fields -/

/-- **Leak freedom and exactly-once destruction of the field-selective cleanup.**
For an owned box in any field state, `dropLiveFieldsThenFreeBacking` is defined; afterwards
* every field's destructor has run exactly once more if the field held a value, and not at all
  if it had been moved out or never written;
* no field holds a value;
* the block is released, by exactly one deallocation call if the size is non-zero and by none
  if it is zero; no allocation call is made. -/
theorem cleanup_selective_leak_free_exactly_once (h : Heap) (b : BoxVal) (ho : Owns h b) :
    ∃ b' h', dropLiveFieldsThenFreeBacking h b = .ok (b', h')
      ∧ b'.slots = b.slots.map Slot.afterDrop
      ∧ (∀ t, t ∈ b'.slots → t.init = false)
      ∧ totalRuns b'.slots = totalRuns b.slots + countInit b.slots
      ∧ Released h' b
      ∧ h'.allocCalls = h.allocCalls
      ∧ h'.deallocCalls = h.deallocCalls + (if b.layout.size = 0 then 0 else 1) := by
  cases boxFree_of_owns h b ho with
  | intro h' hh =>
    refine ⟨{ b with slots := b.slots.map Slot.afterDrop }, h', ?_, rfl,
      afterDrop_no_field_left b.slots, totalRuns_afterDrop b.slots, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    show (match dropWhere (fun s => s.init) b.slots with
          | .ok ss => (boxFree h b).map (fun h' => ({ b with slots := ss }, h'))
          | .ub e => .ub e
          | .oom => .oom) = _
    rw [dropWhere_init, hh.1]; rfl

/-- **Cleanup of a `Box<MaybeUninit<T>>`.** `freeBackingOnly` is defined for an owned box in any
field state; it runs no destructor, changes no field, and releases the block. -/
theorem cleanup_uninit_frees_block_runs_no_destructor (h : Heap) (b : BoxVal) (ho : Owns h b) :
    ∃ h', freeBackingOnly h b = .ok (b, h')
      ∧ Released h' b
      ∧ h'.allocCalls = h.allocCalls
      ∧ h'.deallocCalls = h.deallocCalls + (if b.layout.size = 0 then 0 else 1) := by
  cases boxFree_of_owns h b ho with
  | intro h' hh =>
    refine ⟨h', ?_, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
    show (match dropWhere (fun _ => false) b.slots with
          | .ok ss => (boxFree h b).map (fun h' => ({ b with slots := ss }, h'))
          | .ub e => .ub e
          | .oom => .oom) = _
    rw [dropWhere_none, hh.1]; rfl

/-- The price of the previous statement: a field that was written by hand before the cleanup
still holds its value afterwards, and the block that contained it is gone, so its destructor can
never run. This is a leak of whatever the field owns; it is not undefined behaviour. -/
theorem cleanup_uninit_leaves_written_fields (h : Heap) (b : BoxVal) (ho : Owns h b)
    (hw : ∃ s, s ∈ b.slots ∧ s.init = true) :
    ∃ b' h', freeBackingOnly h b = .ok (b', h') ∧ Released h' b
      ∧ (∃ t, t ∈ b'.slots ∧ t.init = true) ∧ totalRuns b'.slots = totalRuns b.slots := by
  cases cleanup_uninit_frees_block_runs_no_destructor h b ho with
  | intro h' hh => exact ⟨b, h', hh.1, hh.2.1, hw, rfl⟩

/-- **Sharpness (general form of the first counterexample).** If some field of the box holds no
value, the whole-value cleanup is undefined behaviour, in every heap. -/
theorem full_drop_ub_of_missing_field (h : Heap) (b : BoxVal)
    (hm : ∃ s, s ∈ b.slots ∧ s.init = false) :
    fullDropThenFreeBacking h b = .ub .dropOfMovedOrUninit := by
  show (match dropWhere (fun _ => true) b.slots with
        | .ok ss => (boxFree h b).map (fun h' => ({ b with slots := ss }, h'))
        | .ub e => .ub e
        | .oom => .oom) = _
  rw [dropWhere_all_ub b.slots hm]

/-- The whole-value cleanup agrees with the field-selective one when every field holds a value. -/
theorem full_drop_eq_selective_of_all_init (h : Heap) (b : BoxVal)
    (hall : ∀ s, s ∈ b.slots → s.init = true) :
    fullDropThenFreeBacking h b = dropLiveFieldsThenFreeBacking h b := by
  have h1 : dropWhere (fun _ => true) b.slots = .ok (b.slots.map (Slot.afterFlag (fun _ => true))) :=
    dropWhere_of_sound (fun _ => true) b.slots (fun s hs _ => hall s hs)
  have h2 : b.slots.map (Slot.afterFlag (fun _ => true)) = b.slots.map Slot.afterDrop := by
    apply List.map_congr_left
    intro s hs
    show (if true = true then (⟨false, s.runs + 1⟩ : Slot) else s)
        = (if s.init = true then (⟨false, s.runs + 1⟩ : Slot) else s)
    rw [hall s hs]
  show (match dropWhere (fun _ => true) b.slots with
        | .ok ss => (boxFree h b).map (fun h' => ({ b with slots := ss }, h'))
        | .ub e => .ub e
        | .oom => .oom)
      = (match dropWhere (fun s => s.init) b.slots with
        | .ok ss => (boxFree h b).map (fun h' => ({ b with slots := ss }, h'))
        | .ub e => .ub e
        | .oom => .oom)
  rw [h1, h2, dropWhere_init]

/-! ## Main statement 2: zero-sized boxes -/

/-- The dangling address of a layout is non-zero and a multiple of the alignment. -/
theorem dangling_address_nonzero_and_aligned (l : Layout) : 0 < l.align ∧ l.align % l.align = 0 :=
  ⟨Nat.two_pow_pos _, Nat.mod_self _⟩

/-- `box_new_uninit` for a zero-sized layout returns the dangling address `align` and leaves the
heap exactly as it was, whatever the allocator would have answered. -/
theorem boxNewUninit_zero_size (h : Heap) (l : Layout) (hz : l.size = 0) (n : Nat) (avail : Bool) :
    boxNewUninit h l n avail
      = .ok ({ ptr := .dangling l.align, layout := l,
               slots := List.replicate n ⟨false, 0⟩, hasDropGlue := false }, h) := by
  show (match globalAllocate h l avail with
        | .ok (some p, h') =>
          Outcome.ok (({ ptr := p, layout := l, slots := List.replicate n ⟨false, 0⟩,
                         hasDropGlue := false } : BoxVal), h')
        | .ok (none, _) => .oom
        | .ub e => .ub e
        | .oom => .oom) = _
  have hg : globalAllocate h l avail = .ok (some (.dangling l.align), h) := by
    show (if l.size = 0 then Outcome.ok (some (Ptr.dangling l.align), h) else _) = _
    rw [ifPos hz]
  rw [hg]

/-- **Zero-allocation soundness of a zero-sized `Box`.** `Box::new` of a zero-sized value
succeeds with the heap unchanged (no call, no event, no block), the box owns its address, and
dropping it again succeeds with the heap unchanged. -/
theorem zst_box_lifecycle_never_reaches_allocator (h : Heap) (l : Layout) (hz : l.size = 0)
    (n : Nat) (avail : Bool) :
    ∃ b, boxNew h l n avail = .ok (b, h)
      ∧ b.ptr = .dangling l.align
      ∧ Owns h b
      ∧ ∃ b', boxDrop h b = .ok (b', h) ∧ (∀ t, t ∈ b'.slots → t.init = false) := by
  let b₀ : BoxVal := { ptr := .dangling l.align, layout := l,
                       slots := List.replicate n ⟨false, 0⟩, hasDropGlue := false }
  let b₁ : BoxVal := b₀.writeAll.assumeInit
  have hnew : boxNew h l n avail = .ok (b₁, h) := by
    show (boxNewUninit h l n avail).map (fun r => (r.1.writeAll.assumeInit, r.2)) = _
    rw [boxNewUninit_zero_size h l hz n avail]; rfl
  have hown : Owns h b₁ := ⟨hz, rfl⟩
  cases boxFree_of_owns h b₁ hown with
  | intro h'' hf =>
    have e1 : h'' = h := hf.2.2.2.2.1 hz
    have hd : dropLiveFieldsThenFreeBacking h b₁
        = .ok ({ b₁ with slots := b₁.slots.map Slot.afterDrop }, h) := by
      show (match dropWhere (fun s => s.init) b₁.slots with
            | .ok ss => (boxFree h b₁).map (fun h' => ({ b₁ with slots := ss }, h'))
            | .ub e => .ub e
            | .oom => .oom) = _
      rw [dropWhere_init, hf.1, e1]; rfl
    have hdrop : boxDrop h b₁ = .ok ({ b₁ with slots := b₁.slots.map Slot.afterDrop }, h) := by
      show (if b₁.hasDropGlue = true then dropLiveFieldsThenFreeBacking h b₁ else freeBackingOnly h b₁) = _
      exact (ifPos (show b₁.hasDropGlue = true from rfl)).trans hd
    exact ⟨b₁, hnew, rfl, hown, { b₁ with slots := b₁.slots.map Slot.afterDrop }, hdrop,
      afterDrop_no_field_left b₁.slots⟩

/-- A dangling address can never be deallocated: `__rust_dealloc` on it is undefined behaviour
for every heap and every layout. -/
theorem rustDealloc_dangling_ub (h : Heap) (a : Nat) (l : Layout) :
    rustDealloc h (.dangling a) l = .ub .deallocZeroSize
      ∨ rustDealloc h (.dangling a) l = .ub .deallocDangling := by
  cases hz : decide (l.size = 0) with
  | true =>
    left
    show (if l.size = 0 then Outcome.ub UB.deallocZeroSize else _) = _
    rw [ifPos (of_decide_eq_true hz)]
  | false =>
    right
    show (if l.size = 0 then Outcome.ub UB.deallocZeroSize else .ub .deallocDangling) = _
    rw [ifNeg (of_decide_eq_false hz)]

/-- `__rust_alloc` with size zero is undefined behaviour for every heap. -/
theorem rustAlloc_zero_size_ub (h : Heap) (l : Layout) (hz : l.size = 0) (avail : Bool) :
    rustAlloc h l avail = .ub .allocZeroSize := by
  show (if l.size = 0 then Outcome.ub UB.allocZeroSize else _) = _
  rw [ifPos hz]

/-! ## Main statement 3: every deallocation carries the layout of its allocation -/

/-- Replays a history (oldest event first) from a set of live blocks. It fails (`none`) at an
allocation of size zero or of an identity that is live, and at a deallocation whose block is not
live or was allocated with a different layout. -/
noncomputable def replay : List Event → List Block → Option (List Block)
  | [], live => some live
  | .alloc id l :: es, live =>
    if l.size ≠ 0 ∧ find live id = none then replay es (⟨id, l⟩ :: live) else none
  | .dealloc id l :: es, live =>
    if find live id = some l then replay es (remove live id) else none

theorem replay_append (es₁ es₂ : List Event) (live : List Block) :
    replay (es₁ ++ es₂) live = (replay es₁ live).bind (replay es₂) := by
  induction es₁ generalizing live with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | alloc id l =>
      show (if l.size ≠ 0 ∧ find live id = none then replay (es ++ es₂) (⟨id, l⟩ :: live) else none)
          = (if l.size ≠ 0 ∧ find live id = none then replay es (⟨id, l⟩ :: live) else none).bind (replay es₂)
      cases hc : decide (l.size ≠ 0 ∧ find live id = none) with
      | true => rw [ifPos (of_decide_eq_true hc), ifPos (of_decide_eq_true hc)]; exact ih _
      | false => rw [ifNeg (of_decide_eq_false hc), ifNeg (of_decide_eq_false hc)]; rfl
    | dealloc id l =>
      show (if find live id = some l then replay (es ++ es₂) (remove live id) else none)
          = (if find live id = some l then replay es (remove live id) else none).bind (replay es₂)
      cases hc : decide (find live id = some l) with
      | true => rw [ifPos (of_decide_eq_true hc), ifPos (of_decide_eq_true hc)]; exact ih _
      | false => rw [ifNeg (of_decide_eq_false hc), ifNeg (of_decide_eq_false hc)]; rfl

/-- A block that is live after a replay was live before it with the same layout, or was allocated
with that layout by an event of the replayed history. -/
theorem live_after_replay (es : List Event) (live₀ live : List Block)
    (hr : replay es live₀ = some live) (id : BlockId) (l : Layout) (hf : find live id = some l) :
    find live₀ id = some l ∨ Event.alloc id l ∈ es := by
  induction es generalizing live₀ with
  | nil =>
    have e : live₀ = live := Option.some.inj hr
    rw [e]; exact Or.inl hf
  | cons e es ih =>
    cases e with
    | alloc i l' =>
      have hr' : (if l'.size ≠ 0 ∧ find live₀ i = none then replay es (⟨i, l'⟩ :: live₀) else none) = some live := hr
      cases hc : decide (l'.size ≠ 0 ∧ find live₀ i = none) with
      | false => rw [ifNeg (of_decide_eq_false hc)] at hr'; cases hr'
      | true =>
        rw [ifPos (of_decide_eq_true hc)] at hr'
        cases ih _ hr' with
        | inr m => exact Or.inr (List.mem_cons_of_mem _ m)
        | inl hfind =>
          have hfind' : (if i = id then some l' else find live₀ id) = some l := hfind
          cases hi : decide (i = id) with
          | true =>
            have ei : i = id := of_decide_eq_true hi
            rw [ifPos ei] at hfind'
            have el : l' = l := Option.some.inj hfind'
            rw [ei, el]; exact Or.inr (List.mem_cons_self)
          | false =>
            rw [ifNeg (of_decide_eq_false hi)] at hfind'
            exact Or.inl hfind'
    | dealloc i l' =>
      have hr' : (if find live₀ i = some l' then replay es (remove live₀ i) else none) = some live := hr
      cases hc : decide (find live₀ i = some l') with
      | false => rw [ifNeg (of_decide_eq_false hc)] at hr'; cases hr'
      | true =>
        rw [ifPos (of_decide_eq_true hc)] at hr'
        cases ih _ hr' with
        | inr m => exact Or.inr (List.mem_cons_of_mem _ m)
        | inl hfind => exact Or.inl (find_remove_some live₀ i id l hfind)

/-- **Trace form of the pairing invariant.** In a history that replays from the empty heap, every
deallocation event is preceded by an allocation event of the same block with the same layout. -/
theorem dealloc_event_has_matching_alloc (es₁ es₂ : List Event) (id : BlockId) (l : Layout)
    (live : List Block) (hr : replay (es₁ ++ Event.dealloc id l :: es₂) [] = some live) :
    Event.alloc id l ∈ es₁ := by
  rw [replay_append] at hr
  cases h1 : replay es₁ [] with
  | none => rw [h1] at hr; cases hr
  | some live₁ =>
    rw [h1] at hr
    have hr' : (if find live₁ id = some l then replay es₂ (remove live₁ id) else none) = some live := hr
    cases hc : decide (find live₁ id = some l) with
    | false => rw [ifNeg (of_decide_eq_false hc)] at hr'; cases hr'
    | true =>
      cases live_after_replay es₁ [] live₁ h1 id l (of_decide_eq_true hc) with
      | inl hnil => cases hnil
      | inr m => exact m

/-- Well-formed heaps: identities at or above `next` are unused, the history replays from the
empty heap to the live set, and no live block has size zero. -/
structure Heap.WF (h : Heap) : Prop where
  fresh : ∀ id, h.next ≤ id → find h.live id = none
  replays : replay h.events [] = some h.live
  nonzero : ∀ id l, find h.live id = some l → l.size ≠ 0

theorem Heap.empty_wf (imax : Nat) : (Heap.empty imax).WF :=
  ⟨fun _ _ => rfl, rfl, fun _ _ h => by cases h⟩

/-- What a successful `__rust_alloc` does. -/
theorem rustAlloc_ok_inv (h : Heap) (l : Layout) (avail : Bool) (r : Option BlockId × Heap)
    (hr : rustAlloc h l avail = .ok r) :
    l.size ≠ 0 ∧ l.Valid h.isizeMax ∧
    ((avail = true ∧ r = (some h.next,
        { h with live := ⟨h.next, l⟩ :: h.live, next := h.next + 1,
                 events := h.events ++ [Event.alloc h.next l], allocCalls := h.allocCalls + 1 }))
     ∨ (avail = false ∧ r = (none, { h with allocCalls := h.allocCalls + 1 }))) := by
  have hr' : (if l.size = 0 then Outcome.ub UB.allocZeroSize
      else if l.Valid h.isizeMax then
        if avail = true then
          .ok (some h.next,
            { h with live := ⟨h.next, l⟩ :: h.live, next := h.next + 1,
                     events := h.events ++ [Event.alloc h.next l], allocCalls := h.allocCalls + 1 })
        else .ok (none, { h with allocCalls := h.allocCalls + 1 })
      else .ub .allocInvalidLayout) = .ok r := hr
  cases hz : decide (l.size = 0) with
  | true => rw [ifPos (of_decide_eq_true hz)] at hr'; cases hr'
  | false =>
    have hnz : l.size ≠ 0 := of_decide_eq_false hz
    rw [ifNeg hnz] at hr'
    cases hv : decide (l.Valid h.isizeMax) with
    | false => rw [ifNeg (of_decide_eq_false hv)] at hr'; cases hr'
    | true =>
      have hval : l.Valid h.isizeMax := of_decide_eq_true hv
      rw [ifPos hval] at hr'
      cases avail with
      | true =>
        rw [ifPos rfl] at hr'
        exact ⟨hnz, hval, Or.inl ⟨rfl, (Outcome.ok.inj hr').symm⟩⟩
      | false =>
        have hn : ¬ (false = true) := Bool.noConfusion
        rw [ifNeg hn] at hr'
        exact ⟨hnz, hval, Or.inr ⟨rfl, (Outcome.ok.inj hr').symm⟩⟩

/-- `__rust_alloc` preserves well-formedness. -/
theorem rustAlloc_wf (h : Heap) (hwf : h.WF) (l : Layout) (avail : Bool)
    (r : Option BlockId × Heap) (hr : rustAlloc h l avail = .ok r) : r.2.WF := by
  have inv := rustAlloc_ok_inv h l avail r hr
  cases inv.2.2 with
  | inr hnull => rw [hnull.2]; exact ⟨hwf.fresh, hwf.replays, hwf.nonzero⟩
  | inl hsome =>
    rw [hsome.2]
    refine ⟨?_, ?_, ?_⟩
    · intro id hid
      have hlt : h.next < id := hid
      have hne : ¬ h.next = id := Nat.ne_of_lt hlt
      show (if h.next = id then some l else find h.live id) = none
      rw [ifNeg hne]
      exact hwf.fresh id (Nat.le_of_lt hlt)
    · show replay (h.events ++ [Event.alloc h.next l]) [] = some (⟨h.next, l⟩ :: h.live)
      rw [replay_append, hwf.replays]
      show (if l.size ≠ 0 ∧ find h.live h.next = none then replay [] (⟨h.next, l⟩ :: h.live) else none) = _
      rw [ifPos ⟨inv.1, hwf.fresh h.next (Nat.le_refl _)⟩]; rfl
    · intro id l' hf
      have hf' : (if h.next = id then some l else find h.live id) = some l' := hf
      cases hi : decide (h.next = id) with
      | true =>
        rw [ifPos (of_decide_eq_true hi)] at hf'
        rw [← Option.some.inj hf']; exact inv.1
      | false =>
        rw [ifNeg (of_decide_eq_false hi)] at hf'
        exact hwf.nonzero id l' hf'

/-- **Exact characterisation of a defined deallocation.** `__rust_dealloc(ptr, size, align)` is
defined if and only if `ptr` is the start of a live block that was allocated with exactly that
size and alignment, and the size is not zero. -/
theorem rustDealloc_ok_iff (h : Heap) (p : Ptr) (l : Layout) :
    (∃ h', rustDealloc h p l = .ok h') ↔ ∃ id, p = .block id ∧ find h.live id = some l ∧ l.size ≠ 0 := by
  constructor
  · intro hok
    cases hok with
    | intro h' hr =>
      have hr' : (if l.size = 0 then Outcome.ub UB.deallocZeroSize
          else match p with
            | .dangling _ => .ub .deallocDangling
            | .block id =>
              match find h.live id with
              | none => .ub .deallocNotLive
              | some l₀ =>
                if l₀ = l then
                  .ok { h with live := remove h.live id, events := h.events ++ [Event.dealloc id l],
                               deallocCalls := h.deallocCalls + 1 }
                else .ub .deallocLayoutMismatch) = .ok h' := hr
      cases hz : decide (l.size = 0) with
      | true => rw [ifPos (of_decide_eq_true hz)] at hr'; cases hr'
      | false =>
        have hnz : l.size ≠ 0 := of_decide_eq_false hz
        rw [ifNeg hnz] at hr'
        cases p with
        | dangling a => cases hr'
        | block id =>
          have hr2 : (match find h.live id with
              | none => Outcome.ub UB.deallocNotLive
              | some l₀ =>
                if l₀ = l then
                  .ok { h with live := remove h.live id, events := h.events ++ [Event.dealloc id l],
                               deallocCalls := h.deallocCalls + 1 }
                else .ub .deallocLayoutMismatch) = .ok h' := hr'
          cases hf : find h.live id with
          | none => rw [hf] at hr2; cases hr2
          | some l₀ =>
            rw [hf] at hr2
            have hr'' : (if l₀ = l then
                Outcome.ok { h with live := remove h.live id, events := h.events ++ [Event.dealloc id l],
                                    deallocCalls := h.deallocCalls + 1 }
                else .ub .deallocLayoutMismatch) = .ok h' := hr2
            cases he : decide (l₀ = l) with
            | false => rw [ifNeg (of_decide_eq_false he)] at hr''; cases hr''
            | true => exact ⟨id, rfl, by rw [hf, of_decide_eq_true he], hnz⟩
  · intro hex
    cases hex with
    | intro id hid =>
      cases hid with
      | intro hp hrest =>
        rw [hp]
        refine ⟨{ h with live := remove h.live id, events := h.events ++ [Event.dealloc id l],
                         deallocCalls := h.deallocCalls + 1 }, ?_⟩
        show (if l.size = 0 then Outcome.ub UB.deallocZeroSize
          else match find h.live id with
            | none => .ub .deallocNotLive
            | some l₀ =>
              if l₀ = l then
                .ok { h with live := remove h.live id, events := h.events ++ [Event.dealloc id l],
                             deallocCalls := h.deallocCalls + 1 }
              else .ub .deallocLayoutMismatch) = _
        rw [ifNeg hrest.2, hrest.1]
        show (if l = l then _ else _) = _
        rw [ifPos rfl]

/-- What a successful `__rust_dealloc` does. -/
theorem rustDealloc_ok_inv (h : Heap) (p : Ptr) (l : Layout) (h' : Heap)
    (hr : rustDealloc h p l = .ok h') :
    ∃ id, p = .block id ∧ find h.live id = some l ∧ l.size ≠ 0 ∧
      h' = { h with live := remove h.live id, events := h.events ++ [Event.dealloc id l],
                    deallocCalls := h.deallocCalls + 1 } := by
  cases (rustDealloc_ok_iff h p l).mp ⟨h', hr⟩ with
  | intro id hid =>
    refine ⟨id, hid.1, hid.2.1, hid.2.2, ?_⟩
    have hp := hid.1
    rw [hp] at hr
    have hr' : (if l.size = 0 then Outcome.ub UB.deallocZeroSize
          else match find h.live id with
            | none => .ub .deallocNotLive
            | some l₀ =>
              if l₀ = l then
                .ok { h with live := remove h.live id, events := h.events ++ [Event.dealloc id l],
                             deallocCalls := h.deallocCalls + 1 }
              else .ub .deallocLayoutMismatch) = .ok h' := hr
    rw [ifNeg hid.2.2, hid.2.1] at hr'
    have hr'' : (if l = l then
        Outcome.ok { h with live := remove h.live id, events := h.events ++ [Event.dealloc id l],
                            deallocCalls := h.deallocCalls + 1 }
        else .ub .deallocLayoutMismatch) = .ok h' := hr'
    rw [ifPos rfl] at hr''
    exact (Outcome.ok.inj hr'').symm

/-- `__rust_dealloc` preserves well-formedness. -/
theorem rustDealloc_wf (h : Heap) (hwf : h.WF) (p : Ptr) (l : Layout) (h' : Heap)
    (hr : rustDealloc h p l = .ok h') : h'.WF := by
  cases rustDealloc_ok_inv h p l h' hr with
  | intro id hid =>
    rw [hid.2.2.2]
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      show find (remove h.live id) j = none
      cases hji : decide (j = id) with
      | true => rw [of_decide_eq_true hji]; exact find_remove_self _ _
      | false => rw [find_remove_other _ _ _ (of_decide_eq_false hji)]; exact hwf.fresh j hj
    · show replay (h.events ++ [Event.dealloc id l]) [] = some (remove h.live id)
      rw [replay_append, hwf.replays]
      show (if find h.live id = some l then replay [] (remove h.live id) else none) = _
      rw [ifPos hid.2.1]; rfl
    · intro j l' hf
      exact hwf.nonzero j l' (find_remove_some h.live id j l' hf)

/-- Deallocating the same block twice: the second call is undefined behaviour. -/
theorem double_dealloc_ub (h : Heap) (id : BlockId) (l : Layout) (h' : Heap)
    (hr : rustDealloc h (.block id) l = .ok h') :
    rustDealloc h' (.block id) l = .ub .deallocNotLive := by
  cases rustDealloc_ok_inv h (.block id) l h' hr with
  | intro id' hid =>
    have e : id = id' := Ptr.block.inj hid.1
    have hnz : l.size ≠ 0 := hid.2.2.1
    have hgone : find h'.live id = none := by
      rw [hid.2.2.2, ← e]; exact find_remove_self h.live id
    show (if l.size = 0 then Outcome.ub UB.deallocZeroSize
          else match find h'.live id with
            | none => .ub .deallocNotLive
            | some l₀ =>
              if l₀ = l then
                .ok { h' with live := remove h'.live id, events := h'.events ++ [Event.dealloc id l],
                              deallocCalls := h'.deallocCalls + 1 }
              else .ub .deallocLayoutMismatch) = _
    rw [ifNeg hnz, hgone]

/-- Deallocating a live block with any other layout is undefined behaviour. -/
theorem rustDealloc_mismatch_ub (h : Heap) (id : BlockId) (l₀ l : Layout)
    (hf : find h.live id = some l₀) (hne : l₀ ≠ l) (hnz : l.size ≠ 0) :
    rustDealloc h (.block id) l = .ub .deallocLayoutMismatch := by
  show (if l.size = 0 then Outcome.ub UB.deallocZeroSize
        else match find h.live id with
          | none => .ub .deallocNotLive
          | some l₀ =>
            if l₀ = l then
              .ok { h with live := remove h.live id, events := h.events ++ [Event.dealloc id l],
                           deallocCalls := h.deallocCalls + 1 }
            else .ub .deallocLayoutMismatch) = _
  rw [ifNeg hnz, hf]
  show (if l₀ = l then _ else _) = _
  rw [ifNeg hne]

/-- What a successful `box_new_uninit` does. -/
theorem boxNewUninit_ok_inv (h : Heap) (l : Layout) (n : Nat) (avail : Bool) (b : BoxVal) (h₁ : Heap)
    (hnew : boxNewUninit h l n avail = .ok (b, h₁)) :
    b.layout = l ∧ b.slots = List.replicate n ⟨false, 0⟩ ∧ b.hasDropGlue = false ∧
    ((l.size = 0 ∧ b.ptr = .dangling l.align ∧ h₁ = h)
     ∨ (l.size ≠ 0 ∧ b.ptr = .block h.next ∧
        rustAlloc h l avail = .ok (some h.next, h₁) ∧
        h₁ = { h with live := ⟨h.next, l⟩ :: h.live, next := h.next + 1,
                      events := h.events ++ [Event.alloc h.next l], allocCalls := h.allocCalls + 1 })) := by
  cases hz : decide (l.size = 0) with
  | true =>
    have hz' : l.size = 0 := of_decide_eq_true hz
    rw [boxNewUninit_zero_size h l hz' n avail] at hnew
    have e := Outcome.ok.inj hnew
    have e1 : b = { ptr := .dangling l.align, layout := l,
                    slots := List.replicate n ⟨false, 0⟩, hasDropGlue := false } := (congrArg Prod.fst e).symm
    have e2 : h₁ = h := (congrArg Prod.snd e).symm
    rw [e1]
    exact ⟨rfl, rfl, rfl, Or.inl ⟨hz', rfl, e2⟩⟩
  | false =>
    have hnz : l.size ≠ 0 := of_decide_eq_false hz
    have hnew' : (match globalAllocate h l avail with
        | .ok (some p, h') =>
          Outcome.ok (({ ptr := p, layout := l, slots := List.replicate n ⟨false, 0⟩,
                         hasDropGlue := false } : BoxVal), h')
        | .ok (none, _) => .oom
        | .ub e => .ub e
        | .oom => .oom) = .ok (b, h₁) := hnew
    have hg : globalAllocate h l avail =
        (match rustAlloc h l avail with
          | .ok (some id, h') => .ok (some (.block id), h')
          | .ok (none, h') => .ok (none, h')
          | .ub e => .ub e
          | .oom => .oom) := by
      show (if l.size = 0 then Outcome.ok (some (Ptr.dangling l.align), h) else _) = _
      rw [ifNeg hnz]
    rw [hg] at hnew'
    cases hra : rustAlloc h l avail with
    | ub e => rw [hra] at hnew'; cases hnew'
    | oom => rw [hra] at hnew'; cases hnew'
    | ok r =>
      rw [hra] at hnew'
      have inv := rustAlloc_ok_inv h l avail r hra
      cases inv.2.2 with
      | inr hnull => rw [hnull.2] at hnew'; cases hnew'
      | inl hsome =>
        rw [hsome.2] at hnew'
        have e := Outcome.ok.inj hnew'
        have e1 : b = { ptr := .block h.next, layout := l,
                        slots := List.replicate n ⟨false, 0⟩, hasDropGlue := false } :=
          (congrArg Prod.fst e).symm
        have e2 : h₁ = { h with live := ⟨h.next, l⟩ :: h.live, next := h.next + 1,
                                events := h.events ++ [Event.alloc h.next l],
                                allocCalls := h.allocCalls + 1 } :=
          (congrArg Prod.snd e).symm
        rw [e1]
        refine ⟨rfl, rfl, rfl, Or.inr ⟨hnz, rfl, ?_, e2⟩⟩
        rw [hsome.2, e2]

/-- `box_new_uninit` preserves well-formedness and yields a box that owns its block. -/
theorem boxNewUninit_wf_owns (h : Heap) (hwf : h.WF) (l : Layout) (n : Nat) (avail : Bool)
    (b : BoxVal) (h₁ : Heap) (hnew : boxNewUninit h l n avail = .ok (b, h₁)) :
    h₁.WF ∧ Owns h₁ b := by
  have inv := boxNewUninit_ok_inv h l n avail b h₁ hnew
  cases inv.2.2.2 with
  | inl hzst =>
    refine ⟨by rw [hzst.2.2]; exact hwf, ?_⟩
    show (match b.ptr with
          | .block id => find h₁.live id = some b.layout ∧ b.layout.size ≠ 0
          | .dangling a => b.layout.size = 0 ∧ a = b.layout.align)
    rw [hzst.2.1, inv.1]; exact ⟨hzst.1, rfl⟩
  | inr hblk =>
    refine ⟨rustAlloc_wf h hwf l avail _ hblk.2.2.1, ?_⟩
    show (match b.ptr with
          | .block id => find h₁.live id = some b.layout ∧ b.layout.size ≠ 0
          | .dangling a => b.layout.size = 0 ∧ a = b.layout.align)
    rw [hblk.2.1, inv.1, hblk.2.2.2]
    refine ⟨?_, hblk.1⟩
    show (if h.next = h.next then some l else find h.live h.next) = some l
    rw [ifPos rfl]

/-- Ownership does not depend on the field state or on the drop-glue marker. -/
theorem owns_of_same_ptr_layout (h : Heap) (b c : BoxVal) (hp : c.ptr = b.ptr) (hl : c.layout = b.layout)
    (ho : Owns h b) : Owns h c := by
  show (match c.ptr with
        | .block id => find h.live id = some c.layout ∧ c.layout.size ≠ 0
        | .dangling a => c.layout.size = 0 ∧ a = c.layout.align)
  rw [hp, hl]; exact ho

/-- Frame: an allocation elsewhere does not disturb ownership. -/
theorem owns_after_rustAlloc (h : Heap) (hwf : h.WF) (b : BoxVal) (ho : Owns h b) (l : Layout)
    (avail : Bool) (r : Option BlockId × Heap) (hr : rustAlloc h l avail = .ok r) : Owns r.2 b := by
  have inv := rustAlloc_ok_inv h l avail r hr
  cases inv.2.2 with
  | inr hnull => rw [hnull.2]; exact ho
  | inl hsome =>
    rw [hsome.2]
    cases b with
    | mk ptr layout slots glue =>
      cases ptr with
      | dangling a => exact ho
      | block id =>
        have hf : find h.live id = some layout := ho.1
        have hne : ¬ h.next = id := by
          intro e
          have hnone := hwf.fresh id (Nat.le_of_eq e)
          rw [hnone] at hf; cases hf
        refine ⟨?_, ho.2⟩
        show (if h.next = id then some l else find h.live id) = some layout
        rw [ifNeg hne]; exact hf

/-- Frame: a deallocation of another block does not disturb ownership. -/
theorem owns_after_rustDealloc_other (h : Heap) (b : BoxVal) (ho : Owns h b) (id : BlockId)
    (l : Layout) (h' : Heap) (hr : rustDealloc h (.block id) l = .ok h')
    (hother : b.ptr ≠ .block id) : Owns h' b := by
  cases rustDealloc_ok_inv h (.block id) l h' hr with
  | intro id' hid =>
    have e : id = id' := Ptr.block.inj hid.1
    rw [hid.2.2.2, ← e]
    cases b with
    | mk ptr layout slots glue =>
      cases ptr with
      | dangling a => exact ho
      | block j =>
        have hne : j ≠ id := fun e' => hother (congrArg Ptr.block e')
        refine ⟨?_, ho.2⟩
        show find (remove h.live id) j = some layout
        rw [find_remove_other _ _ _ hne]; exact ho.1

/-- **Exact `(size, align)` pairing over the life of a box.** Let `box_new_uninit(l)` succeed on a
well-formed heap. Then the resulting heap is well formed and the box owns its block; if the size
is non-zero the allocator was asked for exactly `l`; and in every later heap in which the box
still owns its block, whatever happened to its fields, `<Box as Drop>::drop` is defined, keeps the
heap well formed, and (for a non-zero size) asks the allocator to free the same block with exactly
`l` again. -/
theorem box_lifecycle_dealloc_layout_eq_alloc_layout (h : Heap) (hwf : h.WF) (l : Layout) (n : Nat)
    (avail : Bool) (b : BoxVal) (h₁ : Heap) (hnew : boxNewUninit h l n avail = .ok (b, h₁)) :
    h₁.WF ∧ Owns h₁ b
    ∧ (l.size ≠ 0 → b.ptr = .block h.next ∧ h₁.events = h.events ++ [Event.alloc h.next l])
    ∧ ∀ (h₂ : Heap) (c : BoxVal), h₂.WF → c.ptr = b.ptr → c.layout = b.layout → Owns h₂ b →
        ∃ h₃, boxFree h₂ c = .ok h₃ ∧ h₃.WF ∧ Released h₃ c
          ∧ (l.size ≠ 0 → h₃.events = h₂.events ++ [Event.dealloc h.next l]) := by
  have inv := boxNewUninit_ok_inv h l n avail b h₁ hnew
  have wo := boxNewUninit_wf_owns h hwf l n avail b h₁ hnew
  refine ⟨wo.1, wo.2, ?_, ?_⟩
  · intro hnz
    cases inv.2.2.2 with
    | inl hzst => exact absurd hzst.1 hnz
    | inr hblk => exact ⟨hblk.2.1, by rw [hblk.2.2.2]⟩
  · intro h₂ c hwf₂ hp hl ho₂
    have hoc : Owns h₂ c := owns_of_same_ptr_layout h₂ b c hp hl ho₂
    cases boxFree_of_owns h₂ c hoc with
    | intro h₃ hf =>
      refine ⟨h₃, hf.1, ?_, hf.2.1, ?_⟩
      · cases hz : decide (c.layout.size = 0) with
        | true => rw [hf.2.2.2.2.1 (of_decide_eq_true hz)]; exact hwf₂
        | false =>
          have hnz : c.layout.size ≠ 0 := of_decide_eq_false hz
          have hfree : rustDealloc h₂ c.ptr c.layout = .ok h₃ := by
            have hbf : (if c.layout.size = 0 then Outcome.ok h₂ else rustDealloc h₂ c.ptr c.layout) = .ok h₃ := hf.1
            rw [ifNeg hnz] at hbf; exact hbf
          exact rustDealloc_wf h₂ hwf₂ c.ptr c.layout h₃ hfree
      · intro hnz
        cases inv.2.2.2 with
        | inl hzst => exact absurd hzst.1 hnz
        | inr hblk =>
          have hcp : c.ptr = .block h.next := by rw [hp, hblk.2.1]
          have hcl : c.layout = l := by rw [hl, inv.1]
          have := hf.2.2.2.2.2 h.next hcp
          rw [hcl] at this; exact this

/-- A box value whose layout differs from the layout its block was allocated with (for instance a
`Box::from_raw` at another pointee type) cannot be freed: its destructor is undefined behaviour. -/
theorem boxFree_wrong_layout_ub (h : Heap) (b : BoxVal) (id : BlockId) (l' : Layout)
    (hp : b.ptr = .block id) (hf : find h.live id = some b.layout) (hne : b.layout ≠ l') (hnz : l'.size ≠ 0) :
    boxFree h { b with layout := l' } = .ub .deallocLayoutMismatch := by
  show (if l'.size = 0 then Outcome.ok h else rustDealloc h b.ptr l') = _
  rw [ifNeg hnz, hp]
  exact rustDealloc_mismatch_ub h id b.layout l' hf hne hnz

/-! ## Allocation failure -/

/-- If the allocator returns null for a non-zero, valid layout, `box_new_uninit` aborts: no box
value exists afterwards. -/
theorem boxNewUninit_oom (h : Heap) (l : Layout) (n : Nat) (hnz : l.size ≠ 0) (hv : l.Valid h.isizeMax) :
    boxNewUninit h l n false = .oom := by
  have hra : rustAlloc h l false = .ok (none, { h with allocCalls := h.allocCalls + 1 }) := by
    show (if l.size = 0 then Outcome.ub UB.allocZeroSize
      else if l.Valid h.isizeMax then
        if false = true then
          .ok (some h.next,
            { h with live := ⟨h.next, l⟩ :: h.live, next := h.next + 1,
                     events := h.events ++ [Event.alloc h.next l], allocCalls := h.allocCalls + 1 })
        else .ok (none, { h with allocCalls := h.allocCalls + 1 })
      else .ub .allocInvalidLayout) = _
    have hn : ¬ (false = true) := Bool.noConfusion
    rw [ifNeg hnz, ifPos hv, ifNeg hn]
  show (match globalAllocate h l false with
        | .ok (some p, h') =>
          Outcome.ok (({ ptr := p, layout := l, slots := List.replicate n ⟨false, 0⟩,
                         hasDropGlue := false } : BoxVal), h')
        | .ok (none, _) => .oom
        | .ub e => .ub e
        | .oom => .oom) = _
  have hg : globalAllocate h l false = .ok (none, { h with allocCalls := h.allocCalls + 1 }) := by
    show (if l.size = 0 then Outcome.ok (some (Ptr.dangling l.align), h)
          else match rustAlloc h l false with
            | .ok (some id, h') => .ok (some (.block id), h')
            | .ok (none, h') => .ok (none, h')
            | .ub e => .ub e
            | .oom => .oom) = _
    rw [ifNeg hnz, hra]
  rw [hg]

/-! ## Concrete executions

Each statement below is decided by evaluation in the kernel. The scenarios mirror programs that
were run on a real compiler: a two-field pointee of size 128 and alignment 64 on a 64-bit target. -/

namespace Example

/-- `isize::MAX` on a 64-bit target. -/
noncomputable def imax : Nat := 9223372036854775807

/-- Size 128, alignment 64 (`2 ^ 6`). -/
noncomputable def pairLayout : Layout := ⟨128, 6⟩

/-- Size 0, alignment 64. -/
noncomputable def zstLayout : Layout := ⟨0, 6⟩

/-- Size 0, alignment 1. -/
noncomputable def unitLayout : Layout := ⟨0, 0⟩

noncomputable def h0 : Heap := Heap.empty imax

/-- Summary of a finished scenario: allocation calls, deallocation calls, destructor runs per
field, and whether a field still holds a value. -/
structure Summary where
  allocCalls : Nat
  deallocCalls : Nat
  runs : List Nat
  fieldLeft : Bool
  liveBlocks : Nat
  deriving DecidableEq

noncomputable def summarize (r : Outcome (BoxVal × Heap)) : Outcome Summary :=
  r.map (fun p =>
    { allocCalls := p.2.allocCalls, deallocCalls := p.2.deallocCalls,
      runs := p.1.slots.map (fun s => s.runs),
      fieldLeft := p.1.slots.any (fun s => s.init),
      liveBlocks := p.2.live.length })

/-- Sequencing for scenarios. -/
noncomputable def andThen {α β : Type} (o : Outcome α) (f : α → Outcome β) : Outcome β :=
  match o with
  | .ok a => f a
  | .ub e => .ub e
  | .oom => .oom

/-- `let b = Box::new(pair); drop(b)`. -/
noncomputable def sizedRoundTrip : Outcome (BoxVal × Heap) :=
  andThen (boxNew h0 pairLayout 2 true) (fun p => boxDrop p.2 p.1)

theorem sizedRoundTrip_summary :
    summarize sizedRoundTrip
      = .ok { allocCalls := 1, deallocCalls := 1, runs := [1, 1], fieldLeft := false, liveBlocks := 0 } := by
  decide

/-- `let b = Box::new(pair); let first = b.first; forget(first); panic!()`: cleanup of `b` on the
unwind path. One allocation, one deallocation, one destructor run (the remaining field). -/
noncomputable def moveFirstThenUnwind : Outcome (BoxVal × Heap) :=
  andThen (boxNew h0 pairLayout 2 true) (fun p =>
    andThen (p.1.moveOutField 0) (fun b => boxDrop p.2 b))

theorem moveFirstThenUnwind_summary :
    summarize moveFirstThenUnwind
      = .ok { allocCalls := 1, deallocCalls := 1, runs := [0, 1], fieldLeft := false, liveBlocks := 0 } := by
  decide

/-- Both fields moved out, then cleanup: the block is freed and no destructor runs. -/
noncomputable def moveBothThenUnwind : Outcome (BoxVal × Heap) :=
  andThen (boxNew h0 pairLayout 2 true) (fun p =>
    andThen (p.1.moveOutField 0) (fun b =>
      andThen (b.moveOutField 1) (fun b' => boxDrop p.2 b')))

theorem moveBothThenUnwind_summary :
    summarize moveBothThenUnwind
      = .ok { allocCalls := 1, deallocCalls := 1, runs := [0, 0], fieldLeft := false, liveBlocks := 0 } := by
  decide

/-- `let mut b = Box::<Pair>::new_uninit(); write first field; panic!()`: cleanup of the
`Box<MaybeUninit<Pair>>` on the unwind path. The block is freed, no destructor runs, and the
written field is left undestroyed. -/
noncomputable def uninitMidInitUnwind : Outcome (BoxVal × Heap) :=
  andThen (boxNewUninit h0 pairLayout 2 true) (fun p => boxDrop p.2 (p.1.writeField 0))

theorem uninitMidInitUnwind_summary :
    summarize uninitMidInitUnwind
      = .ok { allocCalls := 1, deallocCalls := 1, runs := [0, 0], fieldLeft := true, liveBlocks := 0 } := by
  decide

/-- The same box completed and converted with `assume_init` before it is dropped. -/
noncomputable def uninitCompleted : Outcome (BoxVal × Heap) :=
  andThen (boxNewUninit h0 pairLayout 2 true) (fun p =>
    boxDrop p.2 ((p.1.writeField 0).writeField 1).assumeInit)

theorem uninitCompleted_summary :
    summarize uninitCompleted
      = .ok { allocCalls := 1, deallocCalls := 1, runs := [1, 1], fieldLeft := false, liveBlocks := 0 } := by
  decide

/-- `Box::new` of a zero-sized value with alignment 64, then drop: no allocator call at all, and
the address is 64. -/
noncomputable def zstRoundTrip : Outcome (BoxVal × Heap) :=
  andThen (boxNew h0 zstLayout 0 true) (fun p => boxDrop p.2 p.1)

theorem zstRoundTrip_summary :
    summarize zstRoundTrip
      = .ok { allocCalls := 0, deallocCalls := 0, runs := [], fieldLeft := false, liveBlocks := 0 } := by
  decide

theorem zst_box_address :
    (boxNew h0 zstLayout 0 true).map (fun p => p.1.ptr) = .ok (.dangling 64)
      ∧ (boxNew h0 unitLayout 0 true).map (fun p => p.1.ptr) = .ok (.dangling 1) := by
  decide

/-- The allocator answers null: `Box::new` aborts. -/
theorem box_new_null_aborts : boxNew h0 pairLayout 2 false = .oom := by decide

/-- A request whose size exceeds `isize::MAX` is outside the allocator contract. -/
theorem oversize_request_ub : rustAlloc h0 ⟨imax + 1, 0⟩ true = .ub .allocInvalidLayout := by decide

/-- **Counterexample 1.** A whole-value drop where the field-selective drop was required reads
storage that holds no value: (a) field 0 was moved out of a `Box<Pair>`; (b) only field 0 of a
`Box<MaybeUninit<Pair>>` was written and the box is then treated as a `Box<Pair>`. In both states
the field-selective cleanup is defined. -/
theorem ce1_full_drop_after_partial_move_or_uninit_ub :
    andThen (boxNew h0 pairLayout 2 true) (fun p =>
        andThen (p.1.moveOutField 0) (fun b => fullDropThenFreeBacking p.2 b))
      = .ub .dropOfMovedOrUninit
    ∧ andThen (boxNewUninit h0 pairLayout 2 true) (fun p =>
        fullDropThenFreeBacking p.2 (p.1.writeField 0).assumeInit)
      = .ub .dropOfMovedOrUninit
    ∧ (andThen (boxNew h0 pairLayout 2 true) (fun p =>
        andThen (p.1.moveOutField 0) (fun b => dropLiveFieldsThenFreeBacking p.2 b))).isOk = true
    ∧ (andThen (boxNewUninit h0 pairLayout 2 true) (fun p =>
        dropLiveFieldsThenFreeBacking p.2 (p.1.writeField 0).assumeInit)).isOk = true := by
  decide

/-- The heap after one successful allocation of `pairLayout`. -/
noncomputable def h1 : Heap :=
  match rustAlloc h0 pairLayout true with
  | .ok r => r.2
  | _ => h0

/-- **Counterexample 2.** `__rust_dealloc` outside its contract: (a) on the dangling address of a
zero-sized box with its zero-sized layout; (b) on that address with a non-zero size; (c) on a live
block with the right size and another alignment; (d) on a live block with the right alignment and
another size. With the allocation layout the same call is defined. -/
theorem ce2_zst_or_mismatched_align_dealloc_ub :
    rustDealloc h0 (.dangling 1) unitLayout = .ub .deallocZeroSize
    ∧ rustDealloc h0 (.dangling 64) ⟨8, 6⟩ = .ub .deallocDangling
    ∧ rustDealloc h1 (.block 0) ⟨128, 3⟩ = .ub .deallocLayoutMismatch
    ∧ rustDealloc h1 (.block 0) ⟨64, 6⟩ = .ub .deallocLayoutMismatch
    ∧ (rustDealloc h1 (.block 0) pairLayout).isOk = true := by
  decide

/-- A box whose pointee type is swapped for one of another alignment cannot be freed, while the
unmodified box can. -/
theorem box_from_raw_at_wrong_type_ub :
    andThen (boxNew h0 pairLayout 2 true) (fun p => boxFree p.2 { p.1 with layout := ⟨128, 3⟩ })
      = .ub .deallocLayoutMismatch
    ∧ (andThen (boxNew h0 pairLayout 2 true) (fun p => boxFree p.2 p.1)).isOk = true := by
  decide

/-- A history with a mismatched deallocation does not replay; the matching one does. -/
theorem replay_rejects_mismatch :
    replay [Event.alloc 0 pairLayout, .dealloc 0 ⟨128, 3⟩] [] = none
      ∧ replay [Event.alloc 0 pairLayout, .dealloc 0 pairLayout] [] = some []
      ∧ replay [Event.alloc 0 pairLayout, .dealloc 0 pairLayout, .dealloc 0 pairLayout] [] = none := by
  decide

end Example

end AllocBox
