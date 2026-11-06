import Std

/-!
Owned representation research model. Addresses are width-indexed byte vectors
in canonical least-significant-byte-first order; no numeric address denotation,
overflow law, Rust layout theorem, or dereference authority is claimed here.
Physical byte order follows the target's endian. Every provenance-bearing byte
stores only an allocation/generation/tag and its significance index, never an
entire pointer. The fragment compatibility and reborrow policies below are
explicit choices of this model, not an identification with Rust alias rules.
In particular, matching fragments copied from different pointers with the same
provenance may form a new byte vector. There is no original-pointer-value
identity in a fragment, so this does not establish a const-context criterion
that a decoded pointer must equal one original pointer value.
-/
namespace AnnealResearch.Representation

abbrev Byte := Fin 256

inductive Endian where
  | little
  | big
  deriving DecidableEq, Repr

structure Target where
  width : Nat
  width_pos : 0 < width
  endian : Endian

structure Provenance where
  allocation : Nat
  generation : Nat
  tag : Nat
  deriving DecidableEq, Repr

structure Fragment where
  provenance : Provenance
  significance : Nat
  deriving DecidableEq, Repr

inductive Cell where
  | uninit
  | init (value : Byte) (fragment : Option Fragment)
  deriving DecidableEq, Repr

structure Ptr (t : Target) where
  address : Fin t.width → Byte
  provenance : Option Provenance

abbrev Representation := Nat → Cell

def zeroByte : Byte := ⟨0, by decide⟩

def zeroIndex (t : Target) : Fin t.width := ⟨0, t.width_pos⟩

/-- Physical offset to canonical significance; the same map is its inverse. -/
def significance (t : Target) (i : Fin t.width) : Fin t.width :=
  match t.endian with
  | .little => i
  | .big => ⟨t.width - 1 - i.val, by have := i.isLt; omega⟩

@[simp] theorem significance_involution (t : Target) (i : Fin t.width) :
    significance t (significance t i) = i := by
  cases h : t.endian with
  | little => simp [significance, h]
  | big =>
    apply Fin.ext
    simp only [significance, h]
    have := i.isLt
    omega

def encodedCell (t : Target) (p : Ptr t) (i : Fin t.width) : Cell :=
  .init (p.address (significance t i))
    (p.provenance.map fun prov => ⟨prov, (significance t i).val⟩)

def encodePtr (t : Target) (p : Ptr t) : Representation :=
  fun i => if h : i < t.width then encodedCell t p ⟨i, h⟩ else .uninit

@[simp] theorem encodePtr_cell (t : Target) (p : Ptr t) (i : Fin t.width) :
    encodePtr t p i.val = encodedCell t p i := by
  simp [encodePtr, i.isLt]

@[simp] theorem encodePtr_outside (t : Target) (p : Ptr t) (i : Nat)
    (hi : t.width ≤ i) : encodePtr t p i = .uninit := by
  simp [encodePtr, show ¬ i < t.width by omega]

def Cell.byteValue : Cell → Option Byte
  | .uninit => none
  | .init b _ => some b

def Cell.byteOrZero : Cell → Byte
  | .uninit => zeroByte
  | .init b _ => b

def Cell.provenance : Cell → Option Provenance
  | .uninit => none
  | .init _ fragment => fragment.map Fragment.provenance

@[simp] theorem encodedCell_byteOrZero (t : Target) (p : Ptr t) (i : Fin t.width) :
    (encodedCell t p i).byteOrZero = p.address (significance t i) := rfl

@[simp] theorem encodedCell_provenance (t : Target) (p : Ptr t) (i : Fin t.width) :
    (encodedCell t p i).provenance = p.provenance := by
  cases hp : p.provenance <;> simp [encodedCell, Cell.provenance, hp]

/-- Candidate bytes are collected from all physical positions. This value is
    returned only after every byte and fragment passes the finite check. -/
def candidate (t : Target) (r : Representation) : Ptr t where
  address := fun j => (r (significance t j).val).byteOrZero
  provenance := (r 0).provenance

def PtrCoherent (t : Target) (r : Representation) (p : Ptr t) : Prop :=
  ∀ i : Fin t.width, r i.val = encodedCell t p i

instance (t : Target) (r : Representation) (p : Ptr t) :
    Decidable (PtrCoherent t r p) := by
  unfold PtrCoherent
  infer_instance

/-- Executable finite validation: uninitialized bytes, wrong-index fragments,
    mixed provenances, and mixtures of present/absent fragments are rejected.
    Uniformly absent fragments represent the explicitly supported no-provenance
    pointer case; this format cannot distinguish that case from total erasure.
    Default candidate bytes are never returned without validating every byte. -/
def decodePtr (t : Target) (r : Representation) : Option (Ptr t) :=
  if PtrCoherent t r (candidate t r) then some (candidate t r) else none

theorem ptr_ext (t : Target) (p q : Ptr t)
    (ha : p.address = q.address) (hp : p.provenance = q.provenance) : p = q := by
  cases p
  cases q
  simp_all

theorem candidate_of_coherent (t : Target) (r : Representation) (p : Ptr t)
    (h : PtrCoherent t r p) : candidate t r = p := by
  apply ptr_ext
  · funext j
    change (r (significance t j).val).byteOrZero = p.address j
    rw [h (significance t j), encodedCell_byteOrZero, significance_involution]
  · change (r 0).provenance = p.provenance
    have hz := h (zeroIndex t)
    change r 0 = encodedCell t p (zeroIndex t) at hz
    rw [hz, encodedCell_provenance]

theorem decodePtr_eq_some_iff (t : Target) (r : Representation) (p : Ptr t) :
    decodePtr t r = some p ↔ PtrCoherent t r p := by
  unfold decodePtr
  by_cases h : PtrCoherent t r (candidate t r)
  · simp only [ite_eq_left h, Option.some.injEq]
    constructor
    · intro he
      simpa [he] using h
    · exact candidate_of_coherent t r p
  · simp only [ite_eq_right h, reduceCtorEq, false_iff]
    intro hp
    exact h (by simpa [candidate_of_coherent t r p hp] using hp)

theorem decodePtr_encodePtr (t : Target) (p : Ptr t) :
    decodePtr t (encodePtr t p) = some p := by
  apply (decodePtr_eq_some_iff t _ p).2
  intro i
  exact encodePtr_cell t p i

theorem candidate_congr (t : Target) (r s : Representation)
    (h : ∀ i : Fin t.width, r i.val = s i.val) : candidate t r = candidate t s := by
  apply ptr_ext
  · funext j
    exact congrArg Cell.byteOrZero (h (significance t j))
  · exact congrArg Cell.provenance (h (zeroIndex t))

/-- Out-of-block bytes have no effect on decoding. -/
theorem decodePtr_congr (t : Target) (r s : Representation)
    (h : ∀ i : Fin t.width, r i.val = s i.val) : decodePtr t r = decodePtr t s := by
  have hc := candidate_congr t r s h
  have hp : PtrCoherent t r (candidate t r) ↔ PtrCoherent t s (candidate t s) := by
    rw [hc]
    unfold PtrCoherent
    constructor
    · intro hr i
      rw [← h i]
      exact hr i
    · intro hs i
      rw [h i]
      exact hs i
  unfold decodePtr
  by_cases hr : PtrCoherent t r (candidate t r)
  · have hs := hp.mp hr
    rw [ite_eq_left hr, ite_eq_left hs, hc]
  · have hs : ¬ PtrCoherent t s (candidate t s) := fun hs => hr (hp.mpr hs)
    rw [ite_eq_right hr, ite_eq_right hs]

theorem decodePtr_none_of_no_coherent (t : Target) (r : Representation)
    (h : ∀ p : Ptr t, ¬ PtrCoherent t r p) : decodePtr t r = none := by
  simp [decodePtr, h]

theorem decodePtr_reject_uninit (t : Target) (r : Representation) (i : Fin t.width)
    (hi : r i.val = .uninit) : decodePtr t r = none := by
  apply decodePtr_none_of_no_coherent
  intro p hp
  have he := hp i
  rw [hi] at he
  cases he

theorem coherent_fragment_provenance (t : Target) (r : Representation) (p : Ptr t)
    (hp : PtrCoherent t r p) (i : Fin t.width) (b : Byte) (f : Fragment)
    (hi : r i.val = .init b (some f)) : p.provenance = some f.provenance := by
  have he := hp i
  rw [hi] at he
  cases hv : p.provenance with
  | none => simp [encodedCell, hv] at he
  | some prov =>
    simp only [encodedCell, hv, Option.map_some, Cell.init.injEq, Option.some.injEq] at he
    have hf := congrArg Fragment.provenance he.2
    simp only [hf]

theorem decodePtr_reject_wrong_index (t : Target) (r : Representation)
    (i : Fin t.width) (b : Byte) (f : Fragment)
    (hi : r i.val = .init b (some f))
    (wrong : f.significance ≠ (significance t i).val) : decodePtr t r = none := by
  apply decodePtr_none_of_no_coherent
  intro p hp
  have he := hp i
  rw [hi] at he
  cases hv : p.provenance with
  | none => simp [encodedCell, hv] at he
  | some prov =>
    simp only [encodedCell, hv, Option.map_some, Cell.init.injEq, Option.some.injEq] at he
    exact wrong (congrArg Fragment.significance he.2)

theorem decodePtr_reject_mixed (t : Target) (r : Representation)
    (i j : Fin t.width) (a b : Byte) (f g : Fragment)
    (hi : r i.val = .init a (some f)) (hj : r j.val = .init b (some g))
    (mixed : f.provenance ≠ g.provenance) : decodePtr t r = none := by
  apply decodePtr_none_of_no_coherent
  intro p hp
  have hf := coherent_fragment_provenance t r p hp i a f hi
  have hg := coherent_fragment_provenance t r p hp j b g hj
  exact mixed (Option.some.inj (hf.symm.trans hg))

def readPtr (t : Target) (r : Representation) (base : Nat) : Option (Ptr t) :=
  decodePtr t (fun i => r (base + i))

def writePtr (t : Target) (r : Representation) (base : Nat) (p : Ptr t) : Representation :=
  fun i => if h : base ≤ i ∧ i < base + t.width then
    encodedCell t p ⟨i - base, by omega⟩ else r i

@[simp] theorem writePtr_cell (t : Target) (r : Representation) (base : Nat)
    (p : Ptr t) (i : Fin t.width) :
    writePtr t r base p (base + i.val) = encodedCell t p i := by
  have hi := i.isLt
  simp [writePtr, show base ≤ base + i.val by omega,
    show base + i.val < base + t.width by omega]

theorem readPtr_writePtr (t : Target) (r : Representation) (base : Nat) (p : Ptr t) :
    readPtr t (writePtr t r base p) base = some p := by
  apply (decodePtr_eq_some_iff t _ p).2
  intro i
  exact writePtr_cell t r base p i

/-- Alignment is explicit. There is no universal assumption that pointer
    alignment equals pointer width. Byte zero is a tag; all other non-field
    bytes, including trailing bytes, are padding. This generic record alone is
    not a certificate of agreement with any Rust target ABI. -/
structure Layout where
  ptrOffset : Nat
  extent : Nat
  alignment : Nat
  pointerAlignment : Nat
  deriving DecidableEq, Repr

def Admissible (t : Target) (l : Layout) : Prop :=
  0 < l.ptrOffset ∧ l.ptrOffset + t.width ≤ l.extent ∧
  0 < l.alignment ∧ 0 < l.pointerAlignment ∧
  l.ptrOffset % l.pointerAlignment = 0 ∧ l.extent % l.alignment = 0 ∧
  l.pointerAlignment ≤ l.alignment

/-- Conditional target assumptions for the usual C-layout Packet arithmetic:
    one alignment-one tag followed by a thin pointer of width `t.width` and
    alignment `a`. These assumptions are supplied, not inferred from Rust. -/
def PacketTarget (t : Target) (a : Nat) : Prop :=
  0 < a ∧ (∃ k : Nat, a = 2 ^ k) ∧ t.width % a = 0

def packetLayout (t : Target) (a : Nat) : Layout :=
  ⟨a, a + t.width, a, a⟩

/-- The conditional C-layout arithmetic satisfies the owned codec conditions.
    Matching an actual Rust target still requires an external ABI premise. -/
theorem packetLayout_admissible (t : Target) (a : Nat) (ha : PacketTarget t a) :
    Admissible t (packetLayout t a) := by
  obtain ⟨hpos, _, hmod⟩ := ha
  simp [Admissible, packetLayout, hpos, hmod]

instance (t : Target) (l : Layout) : Decidable (Admissible t l) := by
  unfold Admissible
  infer_instance

structure Aggregate (t : Target) where
  tag : Byte
  pointer : Ptr t

def NonPadding (t : Target) (l : Layout) (i : Nat) : Prop :=
  i = 0 ∨ l.ptrOffset ≤ i ∧ i < l.ptrOffset + t.width

instance (t : Target) (l : Layout) (i : Nat) : Decidable (NonPadding t l i) := by
  unfold NonPadding
  infer_instance

def encodeAggregate (t : Target) (l : Layout) (v : Aggregate t) : Representation :=
  fun i => if i = 0 then .init v.tag none
    else if h : l.ptrOffset ≤ i ∧ i < l.ptrOffset + t.width then
      encodedCell t v.pointer ⟨i - l.ptrOffset, by omega⟩
    else .uninit

def decodeAggregate (t : Target) (l : Layout) (r : Representation) : Option (Aggregate t) :=
  if Admissible t l then
    match r 0 with
    | .init tag none => (readPtr t r l.ptrOffset).map fun p => ⟨tag, p⟩
    | _ => none
  else none

@[simp] theorem encodeAggregate_tag (t : Target) (l : Layout) (v : Aggregate t) :
    encodeAggregate t l v 0 = .init v.tag none := by
  simp [encodeAggregate]

@[simp] theorem encodeAggregate_pointer_cell (t : Target) (l : Layout)
    (hl : 0 < l.ptrOffset) (v : Aggregate t) (i : Fin t.width) :
    encodeAggregate t l v (l.ptrOffset + i.val) = encodedCell t v.pointer i := by
  have hi := i.isLt
  have hn : l.ptrOffset + i.val ≠ 0 := by omega
  have hf : l.ptrOffset ≤ l.ptrOffset + i.val ∧
      l.ptrOffset + i.val < l.ptrOffset + t.width := by omega
  simp only [encodeAggregate, ite_eq_right hn, dite_eq_left hf, Nat.add_sub_cancel_left]

theorem readPtr_encodeAggregate (t : Target) (l : Layout) (hl : 0 < l.ptrOffset)
    (v : Aggregate t) : readPtr t (encodeAggregate t l v) l.ptrOffset = some v.pointer := by
  apply (decodePtr_eq_some_iff t _ v.pointer).2
  intro i
  exact encodeAggregate_pointer_cell t l hl v i

theorem decodeAggregate_encodeAggregate (t : Target) (l : Layout)
    (hl : Admissible t l) (v : Aggregate t) :
    decodeAggregate t l (encodeAggregate t l v) = some v := by
  unfold decodeAggregate
  rw [ite_eq_left hl, encodeAggregate_tag, readPtr_encodeAggregate t l hl.1]
  cases v
  rfl

theorem decodeAggregate_inadmissible (t : Target) (l : Layout)
    (hl : ¬ Admissible t l) (r : Representation) : decodeAggregate t l r = none := by
  simp [decodeAggregate, hl]

theorem encodeAggregate_padding (t : Target) (l : Layout) (v : Aggregate t) (i : Nat)
    (hi : ¬ NonPadding t l i) : encodeAggregate t l v i = .uninit := by
  simp only [NonPadding, not_or] at hi
  simp [encodeAggregate, hi.1, hi.2]

theorem decodeAggregate_sound (t : Target) (l : Layout) (r : Representation)
    (v : Aggregate t) (h : decodeAggregate t l r = some v) :
    Admissible t l ∧ r 0 = .init v.tag none ∧
      PtrCoherent t (fun i => r (l.ptrOffset + i)) v.pointer := by
  by_cases hl : Admissible t l
  · cases hc : r 0 with
    | uninit => simp [decodeAggregate, hl, hc] at h
    | init b fragment =>
      cases fragment with
      | some f => simp [decodeAggregate, hl, hc] at h
      | none =>
        cases hd : readPtr t r l.ptrOffset with
        | none => simp [decodeAggregate, hl, hc, hd] at h
        | some p =>
          have hv : (⟨b, p⟩ : Aggregate t) = v := by
            simpa [decodeAggregate, hl, hc, hd] using h
          cases hv
          exact ⟨hl, rfl, (decodePtr_eq_some_iff t _ p).1 hd⟩
  · simp [decodeAggregate, hl] at h

/-- An admitted layout's decoder depends only on its complete object extent. -/
theorem decodeAggregate_congr (t : Target) (l : Layout) (hl : Admissible t l)
    (r s : Representation) (h : ∀ i, i < l.extent → r i = s i) :
    decodeAggregate t l r = decodeAggregate t l s := by
  have hp := hl.1
  have he := hl.2.1
  have hw := t.width_pos
  have hz : r 0 = s 0 := h 0 (by omega)
  have hr : readPtr t r l.ptrOffset = readPtr t s l.ptrOffset := by
    apply decodePtr_congr
    intro i
    have hi := i.isLt
    exact h (l.ptrOffset + i.val) (by omega)
  simp only [decodeAggregate, ite_eq_left hl, hz, hr]

/-- Reborrowing is an explicit provenance map, separate from raw transfer.
    This API intentionally does not prescribe any Rust aliasing semantics. -/
abbrev ProvenancePolicy := Provenance → Provenance

def identityPolicy : ProvenancePolicy := id

def withTag (tag : Nat) : ProvenancePolicy := fun prov => { prov with tag := tag }

def PreservesOrigin (policy : ProvenancePolicy) : Prop :=
  ∀ p, (policy p).allocation = p.allocation ∧ (policy p).generation = p.generation

theorem withTag_preserves_origin (tag : Nat) : PreservesOrigin (withTag tag) := by
  intro p
  exact ⟨rfl, rfl⟩

def reborrowPtr (policy : ProvenancePolicy) (p : Ptr t) : Ptr t :=
  { p with provenance := p.provenance.map policy }

def reborrowAggregate (policy : ProvenancePolicy) (v : Aggregate t) : Aggregate t :=
  { v with pointer := reborrowPtr policy v.pointer }

def reborrowCell (policy : ProvenancePolicy) : Cell → Cell
  | .uninit => .uninit
  | .init b f => .init b (f.map fun fragment =>
      { fragment with provenance := policy fragment.provenance })

@[simp] theorem reborrowPtr_address (policy : ProvenancePolicy) (p : Ptr t) :
    (reborrowPtr policy p).address = p.address := rfl

@[simp] theorem reborrowCell_bytes (policy : ProvenancePolicy) (c : Cell) :
    (reborrowCell policy c).byteValue = c.byteValue := by
  cases c <;> rfl

theorem reborrow_encodedCell (t : Target) (policy : ProvenancePolicy)
    (p : Ptr t) (i : Fin t.width) :
    encodedCell t (reborrowPtr policy p) i = reborrowCell policy (encodedCell t p i) := by
  cases hp : p.provenance <;> simp [encodedCell, reborrowPtr, reborrowCell, hp]

def typedTransfer (policy : ProvenancePolicy) (t : Target) (l : Layout)
    (r : Representation) : Option Representation :=
  (decodeAggregate t l r).map fun v => encodeAggregate t l (reborrowAggregate policy v)

theorem typedTransfer_encoded (policy : ProvenancePolicy) (t : Target) (l : Layout)
    (hl : Admissible t l) (v : Aggregate t) :
    typedTransfer policy t l (encodeAggregate t l v) =
      some (encodeAggregate t l (reborrowAggregate policy v)) := by
  simp [typedTransfer, decodeAggregate_encodeAggregate t l hl v]

@[simp] theorem reborrowPtr_identity (p : Ptr t) : reborrowPtr identityPolicy p = p := by
  apply ptr_ext
  · rfl
  · cases hp : p.provenance <;> simp [reborrowPtr, identityPolicy, hp]

@[simp] theorem reborrowAggregate_identity (v : Aggregate t) :
    reborrowAggregate identityPolicy v = v := by
  cases v
  simp [reborrowAggregate]

/-- Use the identity policy for a raw-pointer payload. A nonidentity map is an
    explicit abstract reference-like extension, not raw-pointer copy behavior. -/
theorem rawTypedTransfer_encoded (t : Target) (l : Layout)
    (hl : Admissible t l) (v : Aggregate t) :
    typedTransfer identityPolicy t l (encodeAggregate t l v) =
      some (encodeAggregate t l v) := by
  simpa using typedTransfer_encoded identityPolicy t l hl v

theorem decode_reborrowedAggregate (policy : ProvenancePolicy) (t : Target) (l : Layout)
    (hl : Admissible t l) (v : Aggregate t) :
    decodeAggregate t l (encodeAggregate t l (reborrowAggregate policy v)) =
      some (reborrowAggregate policy v) :=
  decodeAggregate_encodeAggregate t l hl _

/-- Valid input bytes at non-padding offsets are retained modulo the explicitly
    named fragment map. Exact fragment preservation requires the identity map. -/
theorem typedTransfer_nonPadding (policy : ProvenancePolicy) (t : Target) (l : Layout)
    (r : Representation) (v : Aggregate t) (hd : decodeAggregate t l r = some v)
    (i : Nat) (hi : NonPadding t l i) :
    encodeAggregate t l (reborrowAggregate policy v) i = reborrowCell policy (r i) := by
  obtain ⟨hl, htag, hp⟩ := decodeAggregate_sound t l r v hd
  rcases hi with hzero | hfield
  · subst i
    rw [encodeAggregate_tag, htag]
    rfl
  · let j : Fin t.width := ⟨i - l.ptrOffset, by omega⟩
    have hj : l.ptrOffset + j.val = i := by dsimp [j]; omega
    rw [← hj, encodeAggregate_pointer_cell t l hl.1]
    change encodedCell t (reborrowPtr policy v.pointer) j =
      reborrowCell policy (r (l.ptrOffset + j.val))
    have hc := hp j
    change r (l.ptrOffset + j.val) = encodedCell t v.pointer j at hc
    rw [hc]
    exact reborrow_encodedCell t policy v.pointer j

theorem typedTransfer_padding (policy : ProvenancePolicy) (t : Target) (l : Layout)
    (v : Aggregate t) (i : Nat) (hi : ¬ NonPadding t l i) :
    encodeAggregate t l (reborrowAggregate policy v) i = .uninit :=
  encodeAggregate_padding t l _ i hi

/-- A raw transfer carries every byte's initialization and fragment unchanged. -/
def rawCopy (r : Representation) : Representation := r

@[simp] theorem rawCopy_exact (r : Representation) (i : Nat) : rawCopy r i = r i := rfl

def blank : Representation := fun _ => .uninit

/-- Partial copying at identical relative offsets. No typed decode occurs here. -/
def copySlice (destination source : Representation) (offset count : Nat) : Representation :=
  fun i => if offset ≤ i ∧ i < offset + count then source i else destination i

def target4LE : Target := ⟨4, by decide, .little⟩
def target4BE : Target := ⟨4, by decide, .big⟩
def target8LE : Target := ⟨8, by decide, .little⟩

theorem packetTarget4_4 : PacketTarget target4LE 4 :=
  ⟨by decide, ⟨2, rfl⟩, by decide⟩

theorem packetTarget8_8 : PacketTarget target8LE 8 :=
  ⟨by decide, ⟨3, rfl⟩, by decide⟩

theorem packetTarget8_4 : PacketTarget target8LE 4 :=
  ⟨by decide, ⟨2, rfl⟩, by decide⟩

theorem conditional_packet_layouts :
    Admissible target4LE (packetLayout target4LE 4) ∧
    Admissible target8LE (packetLayout target8LE 8) ∧
    Admissible target8LE (packetLayout target8LE 4) :=
  ⟨packetLayout_admissible _ _ packetTarget4_4,
    packetLayout_admissible _ _ packetTarget8_8,
    packetLayout_admissible _ _ packetTarget8_4⟩

def exampleProvenance : Provenance := ⟨11, 3, 7⟩
def otherProvenance : Provenance := ⟨12, 3, 7⟩

def examplePtr (t : Target) : Ptr t where
  address := fun i => ⟨i.val % 256, Nat.mod_lt _ (by decide)⟩
  provenance := some exampleProvenance

/-- Two separate half-copies collectively reconstruct a four-byte pointer. -/
def assembled4 : Representation :=
  copySlice (copySlice blank (encodePtr target4LE (examplePtr target4LE)) 0 2)
    (encodePtr target4LE (examplePtr target4LE)) 2 2

theorem assembled4_coherent :
    PtrCoherent target4LE assembled4 (examplePtr target4LE) := by
  intro i
  have hi : i.val < 4 := i.isLt
  by_cases h : i.val < 2
  · simp [assembled4, copySlice, h, show ¬ 2 ≤ i.val by omega, encodePtr_cell]
  · simp [assembled4, copySlice, show 2 ≤ i.val by omega, hi, encodePtr_cell]

theorem partial_copies_assemble_pointer :
    decodePtr target4LE assembled4 = some (examplePtr target4LE) :=
  (decodePtr_eq_some_iff _ _ _).2 assembled4_coherent

def half4 : Representation :=
  copySlice blank (encodePtr target4LE (examplePtr target4LE)) 0 2

theorem partial_copy_alone_rejected : decodePtr target4LE half4 = none := by
  apply decodePtr_reject_uninit target4LE half4 ⟨2, by decide⟩
  rfl

def scrambled4 : Representation := fun i =>
  if i = 1 then .init ⟨1, by decide⟩ (some ⟨exampleProvenance, 0⟩) else assembled4 i

theorem scrambled_fragment_rejected : decodePtr target4LE scrambled4 = none := by
  apply decodePtr_reject_wrong_index target4LE scrambled4 ⟨1, by decide⟩
    ⟨1, by decide⟩ ⟨exampleProvenance, 0⟩
  · rfl
  · decide

def mixed4 : Representation := fun i =>
  if i = 1 then .init ⟨1, by decide⟩ (some ⟨otherProvenance, 1⟩) else assembled4 i

theorem mixed_fragments_rejected : decodePtr target4LE mixed4 = none := by
  apply decodePtr_reject_mixed target4LE mixed4 ⟨0, by decide⟩ ⟨1, by decide⟩
    ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨exampleProvenance, 0⟩ ⟨otherProvenance, 1⟩
  · rfl
  · rfl
  · decide

def missing4 : Representation := fun i =>
  if i = 1 then .init ⟨1, by decide⟩ none else assembled4 i

theorem missing_fragment_rejected : decodePtr target4LE missing4 = none := by
  apply decodePtr_none_of_no_coherent
  intro p hp
  have hprov := coherent_fragment_provenance target4LE missing4 p hp
    ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨exampleProvenance, 0⟩ rfl
  have he := hp ⟨1, by decide⟩
  simp [missing4, encodedCell, hprov] at he

def paddedLayout4 : Layout := ⟨4, 8, 4, 4⟩

theorem paddedLayout4_eq_packetLayout : paddedLayout4 = packetLayout target4LE 4 := rfl

theorem paddedLayout4_admissible : Admissible target4LE paddedLayout4 := by decide

def exampleAggregate4 : Aggregate target4LE := ⟨⟨42, by decide⟩, examplePtr target4LE⟩

def paddedInput4 : Representation := fun i =>
  if NonPadding target4LE paddedLayout4 i then
    encodeAggregate target4LE paddedLayout4 exampleAggregate4 i
  else .init ⟨99, by decide⟩ none

theorem paddedInput4_decodes :
    decodeAggregate target4LE paddedLayout4 paddedInput4 = some exampleAggregate4 := by
  have hp : readPtr target4LE paddedInput4 paddedLayout4.ptrOffset =
      some exampleAggregate4.pointer := by
    apply (decodePtr_eq_some_iff _ _ _).2
    intro i
    have hi : i.val < 4 := i.isLt
    have hn : NonPadding target4LE paddedLayout4 (paddedLayout4.ptrOffset + i.val) := by
      apply Or.inr
      simp only [paddedLayout4, target4LE]
      omega
    change paddedInput4 (paddedLayout4.ptrOffset + i.val) = _
    simp only [paddedInput4, ite_eq_left hn]
    exact encodeAggregate_pointer_cell target4LE paddedLayout4 (by decide) exampleAggregate4 i
  have htag : paddedInput4 0 = .init exampleAggregate4.tag none := by
    simp only [paddedInput4, ite_eq_left (show NonPadding target4LE paddedLayout4 0 from Or.inl rfl)]
    exact encodeAggregate_tag _ _ _
  simp [decodeAggregate, paddedLayout4_admissible, htag, hp, exampleAggregate4]

theorem typed_transfer_resets_padding :
    typedTransfer identityPolicy target4LE paddedLayout4 paddedInput4 =
      some (encodeAggregate target4LE paddedLayout4
        (reborrowAggregate identityPolicy exampleAggregate4)) ∧
    encodeAggregate target4LE paddedLayout4
      (reborrowAggregate identityPolicy exampleAggregate4) 1 = .uninit ∧
    rawCopy paddedInput4 1 = .init ⟨99, by decide⟩ none := by
  constructor
  · simp [typedTransfer, paddedInput4_decodes]
  · constructor <;> rfl

theorem raw_and_reborrow_differ :
    rawCopy (encodePtr target4LE (examplePtr target4LE)) 0 ≠
      encodePtr target4LE (reborrowPtr (withTag 19) (examplePtr target4LE)) 0 := by
  decide

theorem incoherent_layout_rejected :
    decodeAggregate target4LE ⟨0, 16, 8, 8⟩
      (encodeAggregate target4LE paddedLayout4 exampleAggregate4) = none := by
  apply decodeAggregate_inadmissible
  decide

theorem both_endian_roundTrips :
    decodePtr target4LE (encodePtr target4LE (examplePtr target4LE)) =
      some (examplePtr target4LE) ∧
    decodePtr target4BE (encodePtr target4BE (examplePtr target4BE)) =
      some (examplePtr target4BE) :=
  ⟨decodePtr_encodePtr _ _, decodePtr_encodePtr _ _⟩

#print axioms significance_involution
#print axioms decodePtr_eq_some_iff
#print axioms decodePtr_encodePtr
#print axioms decodePtr_congr
#print axioms decodePtr_reject_uninit
#print axioms decodePtr_reject_wrong_index
#print axioms decodePtr_reject_mixed
#print axioms readPtr_writePtr
#print axioms packetLayout_admissible
#print axioms conditional_packet_layouts
#print axioms encodeAggregate_pointer_cell
#print axioms decodeAggregate_encodeAggregate
#print axioms decodeAggregate_inadmissible
#print axioms decodeAggregate_sound
#print axioms decodeAggregate_congr
#print axioms typedTransfer_encoded
#print axioms rawTypedTransfer_encoded
#print axioms decode_reborrowedAggregate
#print axioms withTag_preserves_origin
#print axioms reborrow_encodedCell
#print axioms reborrowAggregate_identity
#print axioms typedTransfer_nonPadding
#print axioms typedTransfer_padding
#print axioms partial_copies_assemble_pointer
#print axioms partial_copy_alone_rejected
#print axioms scrambled_fragment_rejected
#print axioms mixed_fragments_rejected
#print axioms missing_fragment_rejected
#print axioms typed_transfer_resets_padding
#print axioms paddedInput4_decodes
#print axioms raw_and_reborrow_differ
#print axioms incoherent_layout_rejected
#print axioms both_endian_roundTrips

end AnnealResearch.Representation
