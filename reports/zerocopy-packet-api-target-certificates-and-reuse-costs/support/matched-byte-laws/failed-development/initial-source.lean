import Std

namespace ByteLaws

abbrev Byte := Fin 256
abbrev Addr := Bool

structure Memory where
  b0 : Byte
  b1 : Byte
  init0 : Bool
  init1 : Bool
  read0 : Bool
  read1 : Bool
  write0 : Bool
  write1 : Bool
  deriving DecidableEq, Repr

def byteAt (s : Memory) (a : Addr) : Byte := if a then s.b1 else s.b0
def initialized (s : Memory) (a : Addr) : Bool := if a then s.init1 else s.init0
def readable (s : Memory) (a : Addr) : Bool := if a then s.read1 else s.read0
def writable (s : Memory) (a : Addr) : Bool := if a then s.write1 else s.write0
def ready (s : Memory) (a : Addr) : Prop := initialized s a = true ∧ readable s a = true
def allReady (s : Memory) : Prop := ready s false ∧ ready s true
def stable (s t : Memory) (a : Addr) : Prop := byteAt s a = byteAt t a
def boolValid (b : Byte) : Prop := b.val < 2
def bothValid (s : Memory) : Prop := boolValid s.b0 ∧ boolValid s.b1

instance (s : Memory) (a : Addr) : Decidable (ready s a) := inferInstanceAs (Decidable (_ ∧ _))
instance (s : Memory) : Decidable (allReady s) := inferInstanceAs (Decidable (_ ∧ _))
instance (s t : Memory) (a : Addr) : Decidable (stable s t a) := inferInstanceAs (Decidable (_ = _))
instance (b : Byte) : Decidable (boolValid b) := inferInstanceAs (Decidable (_ < _))
instance (s : Memory) : Decidable (bothValid s) := inferInstanceAs (Decidable (_ ∧ _))

-- A two-byte, padding-free representation. Every Byte value is an admissible byte;
-- initializedness and read authority are separate from its numerical value.
def observe (s : Memory) : Option (Byte × Byte) :=
  if allReady s then some (s.b0, s.b1) else none

def store (s : Memory) (a : Addr) (v : Byte) : Memory :=
  if a then { s with b1 := v, init1 := true }
  else { s with b0 := v, init0 := true }

def writeByte (s : Memory) (a : Addr) (v : Byte) : Option Memory :=
  if writable s a then some (store s a v) else none

def IntoLaw (s : Memory) : Prop :=
  allReady s → observe s = some (s.b0, s.b1)

def WriteLaw (s : Memory) (a frame : Addr) (v : Byte) : Prop :=
  writable s a = true → a ≠ frame →
    writeByte s a v = some (store s a v) ∧
    byteAt (store s a v) a = v ∧ initialized (store s a v) a = true ∧
    byteAt (store s a v) frame = byteAt s frame ∧
    initialized (store s a v) frame = initialized s frame

def BoolLaw (s t : Memory) (a : Addr) : Prop :=
  ready s a → ready t a → stable s t a → boolValid (byteAt s a) →
    ready t a ∧ boolValid (byteAt t a)

def ArrayLaw (s t : Memory) : Prop :=
  allReady s → allReady t → stable s t false → stable s t true →
    bothValid s → allReady t ∧ bothValid t

theorem into_direct (s : Memory) : IntoLaw s := by
  intro h
  simp [IntoLaw, observe, h]

theorem write_direct (s : Memory) (a frame : Addr) (v : Byte) : WriteLaw s a frame v := by
  intro hW hD
  cases a <;> cases frame <;>
    simp_all [writeByte, store, byteAt, initialized, writable]

theorem bool_direct (s t : Memory) (a : Addr) : BoolLaw s t a := by
  intro _ hR hS hV
  exact ⟨hR, hS ▸ hV⟩

theorem array_direct (s t : Memory) : ArrayLaw s t := by
  intro _ hR h0 h1 hV
  change s.b0 = t.b0 at h0
  change s.b1 = t.b1 at h1
  exact ⟨hR, h0 ▸ hV.1, h1 ▸ hV.2⟩

-- The reflected route decides the same concrete guarded judgments, not labels
-- claiming that a producer or a previous checking stage has succeeded.
inductive Query where
  | into (s : Memory)
  | write (s : Memory) (a frame : Addr) (v : Byte)
  | boolean (s t : Memory) (a : Addr)
  | array (s t : Memory)
  deriving DecidableEq, Repr

def meaning : Query → Prop
  | .into s => IntoLaw s
  | .write s a f v => WriteLaw s a f v
  | .boolean s t a => BoolLaw s t a
  | .array s t => ArrayLaw s t

instance (s : Memory) : Decidable (IntoLaw s) := inferInstanceAs (Decidable (_ → _))
instance (s : Memory) (a f : Addr) (v : Byte) : Decidable (WriteLaw s a f v) := inferInstanceAs (Decidable (_ → _ → _))
instance (s t : Memory) (a : Addr) : Decidable (BoolLaw s t a) := inferInstanceAs (Decidable (_ → _ → _ → _ → _))
instance (s t : Memory) : Decidable (ArrayLaw s t) := inferInstanceAs (Decidable (_ → _ → _ → _ → _ → _))
instance (q : Query) : Decidable (meaning q) := by cases q <;> unfold meaning <;> infer_instance

def check (q : Query) : Bool := decide (meaning q)

theorem check_sound (q : Query) (h : check q = true) : meaning q := of_decide_eq_true h

theorem all_reflected (q : Query) : check q = true := by
  apply decide_eq_true
  cases q with
  | into s => exact into_direct s
  | write s a f v => exact write_direct s a f v
  | boolean s t a => exact bool_direct s t a
  | array s t => exact array_direct s t

def base : Memory := ⟨0, 1, true, true, true, true, true, false⟩

-- Material wrong variants keep the fixed required conclusion.
def uninitialized : Memory := { base with init0 := false }
def intoWithoutInit (s : Memory) : Prop :=
  readable s false = true → readable s true = true → observe s = some (s.b0, s.b1)

def aliasedFrame : Prop :=
  byteAt (store base false 2) false = byteAt base false

def guardClaim (bound threshold : Nat) (b : Byte) : Prop :=
  b.val < bound → b.val < threshold → boolValid b

def unstable : Memory := { base with b0 := 2 }
def withoutStability (s t : Memory) (a : Addr) : Prop :=
  ready s a → ready t a → boolValid (byteAt s a) → boolValid (byteAt t a)

def omittedArray : Memory := { base with b1 := 2 }
def withoutArrayIndex (s : Memory) : Prop :=
  allReady s → boolValid s.b0 → bothValid s

theorem missing_init_bad : ¬ intoWithoutInit uninitialized := by decide
theorem aliased_frame_bad : ¬ aliasedFrame := by decide
theorem bool_two_bad : ¬ guardClaim 256 3 2 := by decide
theorem narrow_domain_hides (b : Byte) : guardClaim 2 3 b := by
  intro h _
  exact h
theorem original_domain_exposes : ¬ guardClaim 256 3 2 := by decide
theorem missing_stability_bad : ¬ withoutStability base unstable false := by decide
theorem missing_array_index_bad : ¬ withoutArrayIndex omittedArray := by decide

-- Definitional integer/address projections used by the explicit SMT predicate map.
def addrIndex (a : Addr) : Int := if a then 1 else 0
def byteInt (b : Byte) : Int := Int.ofNat b.val
theorem addr_domain (a : Addr) : addrIndex a = 0 ∨ addrIndex a = 1 := by cases a <;> simp [addrIndex]
theorem byte_domain (b : Byte) : 0 ≤ byteInt b ∧ byteInt b < 256 := by
  have h := b.isLt
  simp [byteInt]
  omega
theorem validity_integer_map (b : Byte) : boolValid b ↔ byteInt b < 2 := by
  simp [boolValid, byteInt]

#print axioms into_direct
#print axioms write_direct
#print axioms bool_direct
#print axioms array_direct
#print axioms check_sound
#print axioms all_reflected
#print axioms narrow_domain_hides
#print axioms missing_init_bad
#print axioms aliased_frame_bad
#print axioms bool_two_bad
#print axioms missing_stability_bad
#print axioms missing_array_index_bad
#print axioms byte_domain
#print axioms validity_integer_map

end ByteLaws
