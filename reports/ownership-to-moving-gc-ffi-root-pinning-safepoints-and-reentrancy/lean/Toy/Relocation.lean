/-!
# Relocation: flat addresses versus root slots across a moving-collector safepoint

A deliberately small model of what native code can observe of a moving collector.

* `Heap.mem` is the flat store: which payload currently sits at which machine address.
* `Heap.roots` is the runtime-visible root table (a shadow root stack, a local-reference
  frame, a handle table): slot index `↦` current address of the designated object.
  A *handle* is a slot index; it never changes.
* `Heap.pin` is the set of addresses whose occupants are pinned.

A collector step `Moves f h h'` relocates objects along an address map `f`.  It must keep
every rooted object (at its new address `f a`), rewrite every root slot, and leave pinned
objects in place.  It promises nothing about addresses that are held only by native code.

Objects carry scalar payloads only: there is no object graph, so reachability is
"directly rooted or pinned".  Nothing here is connected by proof to any real runtime.
-/

namespace Toy

abbrev Addr := Nat
abbrev Slot := Nat
abbrev Val  := Nat

/-- Pointwise update of a function on naturals. -/
def upd {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun x => if x = k then v else f x

@[simp] theorem upd_same {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by
  simp [upd]

@[simp] theorem upd_other {α : Type} (f : Nat → α) {k x : Nat} (v : α) (h : x ≠ k) :
    upd f k v x = f x := by
  simp [upd, h]

/-- Runtime state as seen from native code. -/
structure Heap where
  /-- flat store: address `↦` payload of the object currently located there -/
  mem   : Addr → Option Val
  /-- root table: slot (handle) `↦` current address of the object it designates -/
  roots : Slot → Option Addr
  /-- addresses whose occupants are pinned -/
  pin   : Addr → Bool

/-- Dereference a flat address directly. -/
def readRaw (h : Heap) (a : Addr) : Option Val := h.mem a

/-- Dereference through a handle: look the slot up, then read. -/
def readHandle (h : Heap) (s : Slot) : Option Val := (h.roots s).bind h.mem

/-- One collector step that relocates along `f`. -/
structure Moves (f : Addr → Addr) (h h' : Heap) : Prop where
  /-- distinct live objects stay distinct -/
  inj          : ∀ a b, h.mem a ≠ none → h.mem b ≠ none → f a = f b → a = b
  /-- a rooted object is found, unchanged, at its new address -/
  rooted_kept  : ∀ s a, h.roots s = some a → h'.mem (f a) = h.mem a
  /-- every root slot is rewritten to the new address -/
  roots_fwd    : ∀ s, h'.roots s = (h.roots s).map f
  /-- a pinned object is not moved -/
  pinned_fixed : ∀ a, h.pin a = true → f a = a
  /-- a pinned object is kept -/
  pinned_kept  : ∀ a, h.pin a = true → h'.mem a = h.mem a
  /-- the collector does not change the pin set -/
  pin_same     : h'.pin = h.pin

/-- Reflexive-transitive closure. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star r a a
  | step {a b c : α} : r a b → Star r b c → Star r a c

/-- "Some collection happened." -/
def Gc (h h' : Heap) : Prop := ∃ f, Moves f h h'

/-- The identity relocation is always a legal collector step. -/
theorem Moves.id (h : Heap) : Moves (fun a => a) h h where
  inj := fun _ _ _ _ e => e
  rooted_kept := fun _ _ _ => rfl
  roots_fwd := fun s => by cases h.roots s <;> rfl
  pinned_fixed := fun _ _ => rfl
  pinned_kept := fun _ _ => rfl
  pin_same := rfl

/-! ## Handles survive relocation -/

/-- (b, part 1) A handle dereference returns the same payload after any collector step,
whatever the relocation map. -/
theorem handle_read_gc_stable {f : Addr → Addr} {h h' : Heap} (m : Moves f h h') (s : Slot) :
    readHandle h' s = readHandle h s := by
  unfold readHandle
  rw [m.roots_fwd s]
  cases hr : h.roots s with
  | none => rfl
  | some a => exact m.rooted_kept s a hr

/-- (b, part 1, iterated) The same across any number of collections. -/
theorem handle_read_gc_stable_star {h h' : Heap} (st : Star Gc h h') (s : Slot) :
    readHandle h' s = readHandle h s := by
  induction st with
  | refl _ => rfl
  | step hab _ ih =>
    obtain ⟨f, m⟩ := hab
    rw [ih, handle_read_gc_stable m s]

/-- Handle identity is relocation-invariant: two root slots designate the same live object
after a collection exactly when they did before. -/
theorem handle_identity_gc_stable {f : Addr → Addr} {h h' : Heap} (m : Moves f h h')
    {s₁ s₂ : Slot} {a₁ a₂ : Addr} (h₁ : h.roots s₁ = some a₁) (h₂ : h.roots s₂ = some a₂)
    (l₁ : h.mem a₁ ≠ none) (l₂ : h.mem a₂ ≠ none) :
    h'.roots s₁ = h'.roots s₂ ↔ a₁ = a₂ := by
  rw [m.roots_fwd s₁, m.roots_fwd s₂, h₁, h₂]
  constructor
  · intro e
    have e' : f a₁ = f a₂ := by simpa using e
    exact m.inj a₁ a₂ l₁ l₂ e'
  · intro e
    rw [e]

/-! ## Pinned flat addresses survive relocation -/

/-- A pinned object's flat address reads the same after a collector step. -/
theorem pinned_raw_gc_stable {f : Addr → Addr} {h h' : Heap} (m : Moves f h h')
    {a : Addr} (hp : h.pin a = true) : readRaw h' a = readRaw h a :=
  m.pinned_kept a hp

/-- The same across any number of collections. -/
theorem pinned_raw_gc_stable_star {h h' : Heap} (st : Star Gc h h')
    {a : Addr} (hp : h.pin a = true) : readRaw h' a = readRaw h a ∧ h'.pin a = true := by
  induction st with
  | refl _ => exact ⟨rfl, hp⟩
  | step hab _ ih =>
    obtain ⟨f, m⟩ := hab
    have hp' := hp
    rw [← m.pin_same] at hp'
    obtain ⟨e, p⟩ := ih hp'
    exact ⟨e.trans (pinned_raw_gc_stable m hp), p⟩

/-! ## Unpinned flat addresses do not -/

/-- The transposition of two addresses. -/
def swap (a b : Addr) : Addr → Addr :=
  fun x => if x = a then b else if x = b then a else x

theorem swap_inj (a b x y : Addr) (e : swap a b x = swap a b y) : x = y := by
  unfold swap at e
  by_cases hxa : x = a <;> by_cases hya : y = a <;> by_cases hxb : x = b <;>
    by_cases hyb : y = b <;> simp_all

/-- (a) **Unpinned flat address invalidation.**  Take any heap, any live unpinned object at
address `a`, and any free unpinned address `b`.  There is a legal collector step after which
the old flat address `a` holds nothing, the object sits at `b`, every root slot that
designated it designates `b`, and every handle dereference in the heap is unchanged. -/
theorem unpinned_raw_can_dangle (h : Heap) {a b : Addr} {v : Val}
    (live : h.mem a = some v) (unpinned : h.pin a = false)
    (free : h.mem b = none) (bunpinned : h.pin b = false) :
    ∃ f h', Moves f h h' ∧ readRaw h' a = none ∧ readRaw h' b = some v ∧
      (∀ s, h.roots s = some a → h'.roots s = some b) ∧
      (∀ s, readHandle h' s = readHandle h s) := by
  have hab : a ≠ b := by
    intro e
    rw [e, free] at live
    cases live
  let h' : Heap :=
    { mem := fun x => if x = a then none else if x = b then some v else h.mem x
      roots := fun s => (h.roots s).map (swap a b)
      pin := h.pin }
  have m : Moves (swap a b) h h' :=
    { inj := fun x y _ _ e => swap_inj a b x y e
      rooted_kept := by
        intro s x _
        show (if swap a b x = a then none else if swap a b x = b then some v
          else h.mem (swap a b x)) = h.mem x
        by_cases hxa : x = a
        · subst hxa
          have hsw : swap x b x = b := by simp [swap]
          rw [hsw]
          have hbx : b ≠ x := fun e => hab e.symm
          simp [hbx, live]
        · by_cases hxb : x = b
          · subst hxb
            have hsw : swap a x x = a := by simp [swap, hxa]
            rw [hsw]
            simp [free]
          · have hsw : swap a b x = x := by simp [swap, hxa, hxb]
            rw [hsw]
            simp [hxa, hxb]
      roots_fwd := fun _ => rfl
      pinned_fixed := by
        intro x hp
        have hxa : x ≠ a := by
          intro e
          rw [e, unpinned] at hp
          cases hp
        have hxb : x ≠ b := by
          intro e
          rw [e, bunpinned] at hp
          cases hp
        simp [swap, hxa, hxb]
      pinned_kept := by
        intro x hp
        have hxa : x ≠ a := by
          intro e
          rw [e, unpinned] at hp
          cases hp
        have hxb : x ≠ b := by
          intro e
          rw [e, bunpinned] at hp
          cases hp
        show (if x = a then none else if x = b then some v else h.mem x) = h.mem x
        simp [hxa, hxb]
      pin_same := rfl }
  refine ⟨swap a b, h', m, ?_, ?_, ?_, ?_⟩
  · show (if a = a then none else if a = b then some v else h.mem a) = none
    simp
  · show (if b = a then none else if b = b then some v else h.mem b) = some v
    have hba : b ≠ a := fun e => hab e.symm
    simp [hba]
  · intro s hs
    show (h.roots s).map (swap a b) = some b
    rw [hs]
    simp [swap]
  · intro s
    exact handle_read_gc_stable m s

/-- (a) **Silent aliasing after relocation.**  Two live unpinned objects with different
payloads, each designated by a root slot.  There is a legal collector step after which the
first object's old flat address reads the *second* object's payload, while both handles still
read their own object.  A stale flat address is therefore not only dangling: it can silently
denote a different live object. -/
theorem unpinned_raw_can_alias (h : Heap) {a b : Addr} {v w : Val} {s t : Slot}
    (la : h.mem a = some v) (lb : h.mem b = some w)
    (pa : h.pin a = false) (pb : h.pin b = false)
    (ra : h.roots s = some a) (rb : h.roots t = some b) :
    ∃ f h', Moves f h h' ∧ readRaw h' a = some w ∧
      readHandle h' s = some v ∧ readHandle h' t = some w ∧ h'.roots t = some a := by
  let h' : Heap :=
    { mem := fun x => if x = a then h.mem b else if x = b then h.mem a else h.mem x
      roots := fun s => (h.roots s).map (swap a b)
      pin := h.pin }
  have m : Moves (swap a b) h h' :=
    { inj := fun x y _ _ e => swap_inj a b x y e
      rooted_kept := by
        intro s x _
        show (if swap a b x = a then h.mem b else if swap a b x = b then h.mem a
          else h.mem (swap a b x)) = h.mem x
        by_cases hxa : x = a
        · subst hxa
          have hsw : swap x b x = b := by simp [swap]
          rw [hsw]
          by_cases hbx : b = x
          · simp [hbx]
          · simp [hbx]
        · by_cases hxb : x = b
          · subst hxb
            have hsw : swap a x x = a := by simp [swap, hxa]
            rw [hsw]
            simp
          · have hsw : swap a b x = x := by simp [swap, hxa, hxb]
            rw [hsw]
            simp [hxa, hxb]
      roots_fwd := fun _ => rfl
      pinned_fixed := by
        intro x hp
        have hxa : x ≠ a := by
          intro e
          rw [e, pa] at hp
          cases hp
        have hxb : x ≠ b := by
          intro e
          rw [e, pb] at hp
          cases hp
        simp [swap, hxa, hxb]
      pinned_kept := by
        intro x hp
        have hxa : x ≠ a := by
          intro e
          rw [e, pa] at hp
          cases hp
        have hxb : x ≠ b := by
          intro e
          rw [e, pb] at hp
          cases hp
        show (if x = a then h.mem b else if x = b then h.mem a else h.mem x) = h.mem x
        simp [hxa, hxb]
      pin_same := rfl }
  have hs : readHandle h' s = some v := by
    rw [handle_read_gc_stable m s]
    simp [readHandle, ra, la]
  have ht : readHandle h' t = some w := by
    rw [handle_read_gc_stable m t]
    simp [readHandle, rb, lb]
  refine ⟨swap a b, h', m, ?_, hs, ht, ?_⟩
  · show (if a = a then h.mem b else if a = b then h.mem a else h.mem a) = some w
    simp [lb]
  · show (h.roots t).map (swap a b) = some a
    rw [rb]
    by_cases hba : b = a
    · simp [swap, hba]
    · simp [swap, hba]

/-- **Registration is what keeps an object.**  A live object that no root slot designates and
that is not pinned may simply be reclaimed by a legal collector step (here one that moves
nothing), while every handle dereference in the heap is unchanged.  An unregistered flat
address is therefore exposed to reclamation as well as to relocation. -/
theorem unrooted_can_be_collected (h : Heap) {a : Addr}
    (unrooted : ∀ s, h.roots s ≠ some a) (unpinned : h.pin a = false) :
    ∃ h', Moves (fun x => x) h h' ∧ readRaw h' a = none ∧
      (∀ s, readHandle h' s = readHandle h s) := by
  let h' : Heap := { h with mem := upd h.mem a none }
  have m : Moves (fun x => x) h h' :=
    { inj := fun _ _ _ _ e => e
      rooted_kept := by
        intro s x hx
        have hxa : x ≠ a := by
          intro e
          rw [e] at hx
          exact unrooted s hx
        show upd h.mem a none x = h.mem x
        exact upd_other _ _ hxa
      roots_fwd := fun s => by
        show h.roots s = (h.roots s).map (fun x => x)
        cases h.roots s <;> rfl
      pinned_fixed := fun _ _ => rfl
      pinned_kept := by
        intro x hp
        have hxa : x ≠ a := by
          intro e
          rw [e, unpinned] at hp
          cases hp
        show upd h.mem a none x = h.mem x
        exact upd_other _ _ hxa
      pin_same := rfl }
  refine ⟨h', m, ?_, fun s => handle_read_gc_stable m s⟩
  show upd h.mem a none a = none
  exact upd_same _ _ _

/-- **Pinning is exactly what a flat address needs.**  For a live object at `a`, with some free
unpinned address available to move into, the flat address `a` reads the same after *every*
legal collector step if and only if the object is pinned. -/
theorem raw_stable_iff_pinned (h : Heap) {a b : Addr} {v : Val}
    (live : h.mem a = some v) (free : h.mem b = none) (bunpinned : h.pin b = false) :
    (∀ f h', Moves f h h' → readRaw h' a = readRaw h a) ↔ h.pin a = true := by
  constructor
  · intro stable
    cases hp : h.pin a with
    | true => rfl
    | false =>
      obtain ⟨f, h', m, gone, _, _, _⟩ := unpinned_raw_can_dangle h live hp free bunpinned
      have e := stable f h' m
      rw [gone] at e
      unfold readRaw at e
      rw [live] at e
      cases e
  · intro hp f h' m
    exact pinned_raw_gc_stable m hp

end Toy
