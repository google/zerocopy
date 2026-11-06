import Std

namespace PointerLease
abbrev Cell := Fin 4

structure Cap where
  ticket : Nat
  allocation : Nat
  lo : Nat
  hi : Nat
  expires : Nat
  alignment : Nat
  initialized : Bool
  valid : Bool
deriving DecidableEq, Repr

structure World where
  caps : Nat → Option Cap
  owner : Cell → Nat
  bytes : Cell → Fin 256
  allocation : Nat
  dies : Nat

def covers (c : Cap) (i : Cell) : Prop := c.lo ≤ i.val ∧ i.val < c.hi
def Owned (w : World) (c : Cap) : Prop :=
  w.caps c.ticket = some c ∧ c.allocation = w.allocation ∧
  c.lo ≤ c.hi ∧ c.hi ≤ 4 ∧ c.expires ≤ w.dies ∧
  ∀ i, covers c i → w.owner i = c.ticket

def reconstructByte (w : World) (c : Cap) (now : Nat) : Prop :=
  Owned w c ∧ now < c.expires ∧ 1 ≤ c.alignment ∧
  c.initialized = true ∧ c.valid = true
def reconstructWord (w : World) (c : Cap) (now : Nat) : Prop :=
  Owned w c ∧ now < c.expires ∧ 4 ≤ c.alignment ∧
  c.lo % 4 = 0 ∧ c.hi - c.lo = 4 ∧ c.initialized = true ∧ c.valid = true

def whole (ticket : Nat) : Cap := ⟨ticket, 7, 0, 4, 9, 1, true, true⟩
def initial (bytes : Cell → Fin 256) : World :=
  ⟨fun t => if t = 1 then some (whole 1) else none, fun _ => 1, bytes, 7, 10⟩
def left (k : Fin 5) : Cap := { whole 2 with hi := k.val }
def right (k : Fin 5) : Cap := { whole 3 with lo := k.val }
def split (bytes : Cell → Fin 256) (k : Fin 5) : World :=
  ⟨fun t => if t = 2 then some (left k) else if t = 3 then some (right k) else none,
   fun i => if i.val < k.val then 2 else 3, bytes, 7, 10⟩

theorem construction (bytes : Cell → Fin 256) : Owned (initial bytes) (whole 1) := by
  simp [Owned, initial, whole]

theorem split_left (bytes : Cell → Fin 256) (k : Fin 5) : Owned (split bytes k) (left k) := by
  have hk : k.val ≤ 4 := by omega
  simp [Owned, split, left, whole, hk, covers]

theorem split_right (bytes : Cell → Fin 256) (k : Fin 5) : Owned (split bytes k) (right k) := by
  have hk : k.val ≤ 4 := by omega
  simp [Owned, split, right, whole, hk, covers]

theorem split_disjoint (k : Fin 5) (i : Cell) :
    ¬ (covers (left k) i ∧ covers (right k) i) := by
  simp [covers, left, right, whole]

theorem split_covers (k : Fin 5) (i : Cell) :
    covers (left k) i ∨ covers (right k) i := by
  simp [covers, left, right, whole]
  omega

theorem stale_parent_rejected (bytes : Cell → Fin 256) (k : Fin 5) :
    ¬ Owned (split bytes k) (whole 1) := by
  simp [Owned, split, whole]

def consume (w : World) (c : Cap) : World :=
  { w with caps := fun t => if t = c.ticket then none else w.caps t }

theorem duplicate_reconstruction_rejected (w : World) (c : Cap) (now : Nat) :
    ¬ reconstructByte (consume w c) c now := by
  simp [reconstructByte, Owned, consume]

def projectCell (bytes : Cell → Fin 256) (i : Cell) : World × Cap :=
  let c : Cap := { whole 5 with lo := i.val, hi := i.val + 1 }
  (⟨fun t => if t = 5 then some c else none, fun _ => 5, bytes, 7, 10⟩, c)

theorem projection (bytes : Cell → Fin 256) (i : Cell) :
    Owned (projectCell bytes i).1 (projectCell bytes i).2 := by
  simp [Owned, projectCell, whole, covers]
  omega

theorem projection_preserves_bytes (bytes : Cell → Fin 256) (i j : Cell) :
    (projectCell bytes i).1.bytes j = bytes j := rfl

def restored (bytes : Cell → Fin 256) : World :=
  ⟨fun t => if t = 4 then some (whole 4) else none, fun _ => 4, bytes, 7, 10⟩

theorem restoration (bytes : Cell → Fin 256) : Owned (restored bytes) (whole 4) := by
  simp [Owned, restored, whole]

theorem retired_child_rejected (bytes : Cell → Fin 256) (k : Fin 5) :
    ¬ Owned (restored bytes) (left k) := by
  simp [Owned, restored, left, whole]

def lifetimeExtended : Cap := { whole 1 with expires := 20 }
def lifetimeExtendedWorld (bytes : Cell → Fin 256) : World :=
  { initial bytes with caps := fun t => if t = 1 then some lifetimeExtended else none }

def Geometry (w : World) (c : Cap) : Prop :=
  c.allocation = w.allocation ∧ c.lo ≤ c.hi ∧ c.hi ≤ 4

theorem geometry_misses_lifetime (bytes : Cell → Fin 256) :
    Geometry (lifetimeExtendedWorld bytes) lifetimeExtended := by
  simp [Geometry, lifetimeExtendedWorld, initial, lifetimeExtended, whole]

def lifetimeWeakened (w : World) (c : Cap) (now : Nat) : Prop :=
  w.caps c.ticket = some c ∧ Geometry w c ∧
  (∀ i, covers c i → w.owner i = c.ticket) ∧
  now < c.expires ∧ 1 ≤ c.alignment ∧ c.initialized = true ∧ c.valid = true

theorem weakened_gate_accepts_extension (bytes : Cell → Fin 256) :
    lifetimeWeakened (lifetimeExtendedWorld bytes) lifetimeExtended 11 := by
  simp [lifetimeWeakened, Geometry, lifetimeExtendedWorld, initial, lifetimeExtended, whole]

theorem lifetime_extension_rejected (bytes : Cell → Fin 256) :
    ¬ reconstructByte (lifetimeExtendedWorld bytes) lifetimeExtended 11 := by
  simp [reconstructByte, Owned, lifetimeExtendedWorld, initial, lifetimeExtended, whole]

theorem expired_rejected (bytes : Cell → Fin 256) :
    ¬ reconstructByte (initial bytes) (whole 1) 9 := by
  simp [reconstructByte, whole]

def overlapping (bytes : Cell → Fin 256) : World :=
  let l := { whole 2 with hi := 3 }
  let r := { whole 3 with lo := 2 }
  ⟨fun t => if t = 2 then some l else if t = 3 then some r else none,
   fun i => if i.val < 3 then 2 else 3, bytes, 7, 10⟩
theorem alias_overlap_rejected (bytes : Cell → Fin 256) :
    ¬ Owned (overlapping bytes) { whole 3 with lo := 2 } := by
  intro h
  have bad := h.2.2.2.2.2 ⟨2, by decide⟩ (by simp [covers, whole])
  simp [overlapping, whole] at bad

def castWorld (bytes : Cell → Fin 256) (alignment : Nat) : World × Cap :=
  let c : Cap := { whole 6 with alignment := alignment }
  (⟨fun t => if t = 6 then some c else none, fun _ => 6, bytes, 7, 10⟩, c)

theorem cast_without_alignment_rejected (bytes : Cell → Fin 256) :
    ¬ reconstructWord (castWorld bytes 1).1 (castWorld bytes 1).2 0 := by
  simp [reconstructWord, castWorld]

theorem reconstructed_byte (bytes : Cell → Fin 256) :
    reconstructByte (initial bytes) (whole 1) 0 := by
  simp [reconstructByte, Owned, initial, whole]

theorem reconstructed_word_after_alignment_evidence (bytes : Cell → Fin 256) :
    reconstructWord (castWorld bytes 4).1 (castWorld bytes 4).2 0 := by
  simp [reconstructWord, Owned, castWorld, whole]

#print axioms construction
#print axioms split_left
#print axioms split_right
#print axioms split_disjoint
#print axioms split_covers
#print axioms stale_parent_rejected
#print axioms duplicate_reconstruction_rejected
#print axioms projection
#print axioms projection_preserves_bytes
#print axioms restoration
#print axioms retired_child_rejected
#print axioms geometry_misses_lifetime
#print axioms weakened_gate_accepts_extension
#print axioms lifetime_extension_rejected
#print axioms expired_rejected
#print axioms alias_overlap_rejected
#print axioms cast_without_alignment_rejected
#print axioms reconstructed_byte
#print axioms reconstructed_word_after_alignment_evidence
end PointerLease
