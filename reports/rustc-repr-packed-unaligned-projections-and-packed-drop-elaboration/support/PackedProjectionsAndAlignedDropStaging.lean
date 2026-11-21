/-
  PackedProjectionsAndAlignedDropStaging.lean

  Self-contained, constructive Lean 4 (v4.34.1) formalization of:
  1. Byte-addressed memory with per-type power-of-two alignment invariants
     (`PtrValidAligned`, `alignUp`, `restrictForOffset`, byte read/write framing);
  2. `#[repr(packed(N))]` struct layout clamping (`min(field_align, pack)`),
     place projection chains, `mostPackedAfterLastDeref`, `placeUnaligned`
     (modeling `rustc_const_eval::util::place_unalignment`), and effective
     projection alignment `effAlign`;
  3. MIR operational semantics over both user functions and synthesized
     `DropGlue` / `VTable` shims, comparing strict Miri/Reference alignment UB
     semantics against dynamic `-Z ub-checks` (`CheckAlignment`) semantics;
  4. `checkPackedRef_E0793`, `addMovesForPackedDrops` aligned stack staging,
     and user-only vs. whole-program `CheckAlignment` instrumentation;
  5. Core theorems:
     - `addMovesForPackedDrops_alignment_sound`: alignment-preserving soundness
       and drop-payload preservation of `addMovesForPackedDrops`;
     - `e0793_and_copy_staging_no_misaligned_safe_refs`: static absence of
       misaligned safe references and drops under `E0793` + `Copy` staging +
       `addMovesForPackedDrops`;
     - `whole_program_ub_checks_complete_iff_shims_instrumented`: whole-program
       `-Z ub-checks` completeness iff synthesized shims are instrumented;
     - Constructive sharpness counterexamples:
       * `ce1_direct_packed_drop_passes_misaligned_self_ub`
       * `ce2_uninstrumented_drop_shim_escapes_ub_checks`
       * `ce3_unsized_generic_deref_escapes_user_ub_checks`

  Axiom discipline: zero `sorry`, zero `Classical.choice`, zero `omega`,
  zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `._unsafe_rec`.
-/

namespace PackedProjectionsAndAlignedDropStaging

/-! ## 1. Power-of-Two Alignments and Constructive Divisibility Arithmetic -/

/-- A power-of-two alignment `2^pow2` (matching `rustc_abi::Align`). -/
structure Align where
  pow2 : Nat
  deriving Repr, DecidableEq

namespace Align

def bytes (a : Align) : Nat := 2 ^ a.pow2

def align1 : Align := ⟨0⟩
def align2 : Align := ⟨1⟩
def align4 : Align := ⟨2⟩
def align8 : Align := ⟨3⟩
def align16 : Align := ⟨4⟩
def align64 : Align := ⟨6⟩

def minAlign (a b : Align) : Align :=
  ⟨Nat.min a.pow2 b.pow2⟩

def maxAlign (a b : Align) : Align :=
  ⟨Nat.max a.pow2 b.pow2⟩

def leBool (a b : Align) : Bool :=
  Nat.ble a.pow2 b.pow2

def ltBool (a b : Align) : Bool :=
  Nat.blt a.pow2 b.pow2

theorem pow2_pos (n : Nat) : 0 < 2 ^ n := by
  induction n with
  | zero => exact Nat.zero_lt_succ 0
  | succ k ih =>
    rw [Nat.pow_succ]
    have h2 : 0 < 2 := Nat.zero_lt_succ 1
    exact Nat.mul_pos ih h2

theorem bytes_pos (a : Align) : 0 < a.bytes :=
  pow2_pos a.pow2

theorem bytes_ne_zero (a : Align) : a.bytes ≠ 0 :=
  Nat.ne_of_gt (bytes_pos a)

/-- Constructive divisibility by a power-of-two alignment. -/
def Divides (a : Align) (n : Nat) : Prop :=
  ∃ k : Nat, n = a.bytes * k

/-- Executable alignment predicate `n % 2^pow2 == 0`. -/
def check (a : Align) (n : Nat) : Bool :=
  Nat.beq (n % a.bytes) 0

theorem check_eq_true_iff (a : Align) (n : Nat) :
    a.check n = true ↔ a.Divides n := by
  unfold check Divides
  constructor
  · intro h
    have hmod : n % a.bytes = 0 := Nat.eq_of_beq_eq_true h
    refine ⟨n / a.bytes, ?_⟩
    have hdiv := Nat.div_add_mod n a.bytes
    rw [hmod, Nat.add_zero] at hdiv
    exact hdiv.symm
  · intro h
    rcases h with ⟨k, rfl⟩
    have hmod : (a.bytes * k) % a.bytes = 0 := Nat.mul_mod_right a.bytes k
    rw [hmod]
    rfl

theorem check_eq_false_iff (a : Align) (n : Nat) :
    a.check n = false ↔ ¬ a.Divides n := by
  constructor
  · intro hf hd
    have ht : a.check n = true := (check_eq_true_iff a n).mpr hd
    rw [hf] at ht
    cases ht
  · intro hnd
    cases h : a.check n with
    | false => rfl
    | true =>
      exact False.elim (hnd ((check_eq_true_iff a n).mp h))

theorem pow2_dvd_pow2 {i j : Nat} (hle : i ≤ j) :
    ∃ m : Nat, 2 ^ j = 2 ^ i * m := by
  refine ⟨2 ^ (j - i), ?_⟩
  rw [← Nat.pow_add, Nat.add_sub_of_le hle]

theorem divides_mono {a b : Align} {n : Nat}
    (hle : a.pow2 ≤ b.pow2) (hb : b.Divides n) : a.Divides n := by
  rcases pow2_dvd_pow2 hle with ⟨m, hm⟩
  rcases hb with ⟨k, hk⟩
  refine ⟨m * k, ?_⟩
  rw [hk]
  unfold bytes
  rw [hm, Nat.mul_assoc]

theorem divides_zero (a : Align) : a.Divides 0 :=
  ⟨0, (Nat.mul_zero a.bytes).symm⟩

theorem divides_self (a : Align) : a.Divides a.bytes :=
  ⟨1, (Nat.mul_one a.bytes).symm⟩

theorem divides_add {a : Align} {x y : Nat}
    (hx : a.Divides x) (hy : a.Divides y) : a.Divides (x + y) := by
  rcases hx with ⟨kx, rfl⟩
  rcases hy with ⟨ky, rfl⟩
  exact ⟨kx + ky, (Nat.mul_add a.bytes kx ky).symm⟩

theorem divides_min_left (a b : Align) {n : Nat} (ha : a.Divides n) :
    (minAlign a b).Divides n :=
  divides_mono (Nat.min_le_left a.pow2 b.pow2) ha

theorem divides_min_right (a b : Align) {n : Nat} (hb : b.Divides n) :
    (minAlign a b).Divides n :=
  divides_mono (Nat.min_le_right a.pow2 b.pow2) hb

theorem divides_align1 (n : Nat) : align1.Divides n :=
  ⟨n, by unfold align1 bytes; exact (Nat.one_mul n).symm⟩

theorem check_align1 (n : Nat) : align1.check n = true :=
  (check_eq_true_iff align1 n).mpr (divides_align1 n)

theorem eq_align1_of_not_lt_align1 {a : Align} (h : ltBool align1 a = false) : a = align1 := by
  cases a with
  | mk p =>
    cases p with
    | zero => rfl
    | succ k =>
      have hlt : align1.pow2 < k + 1 := Nat.zero_lt_succ k
      have ht : ltBool align1 ⟨k + 1⟩ = true := (Iff.of_eq Nat.blt_eq).mpr hlt
      rw [h] at ht
      cases ht

theorem minAlign_le_left (a b : Align) : (minAlign a b).pow2 ≤ a.pow2 :=
  Nat.min_le_left a.pow2 b.pow2

theorem minAlign_le_right (a b : Align) : (minAlign a b).pow2 ≤ b.pow2 :=
  Nat.min_le_right a.pow2 b.pow2

theorem leBool_eq_true_iff (a b : Align) : a.leBool b = true ↔ a.pow2 ≤ b.pow2 :=
  Iff.of_eq Nat.ble_eq

theorem ltBool_eq_true_iff (a b : Align) : a.ltBool b = true ↔ a.pow2 < b.pow2 :=
  Iff.of_eq Nat.blt_eq

/-- Round `addr` up to the next multiple of `a.bytes`. -/
def alignUp (addr : Nat) (a : Align) : Nat :=
  match Nat.beq (addr % a.bytes) 0 with
  | true => addr
  | false => addr + (a.bytes - addr % a.bytes)

theorem le_alignUp (addr : Nat) (a : Align) : addr ≤ alignUp addr a := by
  unfold alignUp
  cases Nat.beq (addr % a.bytes) 0 with
  | true => exact Nat.le_refl addr
  | false => exact Nat.le_add_right addr (a.bytes - addr % a.bytes)

theorem divides_alignUp (addr : Nat) (a : Align) : a.Divides (alignUp addr a) := by
  unfold alignUp
  cases hbeq : Nat.beq (addr % a.bytes) 0 with
  | true =>
    have hmod : addr % a.bytes = 0 := Nat.eq_of_beq_eq_true hbeq
    refine ⟨addr / a.bytes, ?_⟩
    have hdiv := Nat.div_add_mod addr a.bytes
    rw [hmod, Nat.add_zero] at hdiv
    exact hdiv.symm
  | false =>
    refine ⟨addr / a.bytes + 1, ?_⟩
    have hlt : addr % a.bytes < a.bytes := Nat.mod_lt addr (bytes_pos a)
    have hle : addr % a.bytes ≤ a.bytes := Nat.le_of_lt hlt
    have hdiv := Nat.div_add_mod addr a.bytes
    calc
      addr + (a.bytes - addr % a.bytes)
          = (a.bytes * (addr / a.bytes) + addr % a.bytes) + (a.bytes - addr % a.bytes) := by
              rw [hdiv]
      _   = a.bytes * (addr / a.bytes) + (addr % a.bytes + (a.bytes - addr % a.bytes)) := by
              rw [Nat.add_assoc]
      _   = a.bytes * (addr / a.bytes) + a.bytes := by
              rw [Nat.add_sub_of_le hle]
      _   = a.bytes * (addr / a.bytes) + a.bytes * 1 := by
              rw [Nat.mul_one]
      _   = a.bytes * (addr / a.bytes + 1) := by
              rw [← Nat.mul_add]

/-- Largest power-of-two factor of `off` capped at `fuel` (models `Align::restrict_for_offset`). -/
def restrictAux (off : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    match (Align.mk (k + 1)).check off with
    | true => k + 1
    | false => restrictAux off k

/-- Effective alignment after adding byte offset `off` to a `base`-aligned pointer. -/
def restrictForOffset (base : Align) (off : Nat) : Align :=
  ⟨restrictAux off base.pow2⟩

theorem restrictAux_le (off : Nat) : ∀ k : Nat, restrictAux off k ≤ k
  | 0 => Nat.le_refl 0
  | k + 1 => by
    unfold restrictAux
    cases (Align.mk (k + 1)).check off with
    | true => exact Nat.le_refl (k + 1)
    | false => exact Nat.le_trans (restrictAux_le off k) (Nat.le_succ k)

theorem restrictAux_divides (off : Nat) : ∀ k : Nat, (Align.mk (restrictAux off k)).Divides off
  | 0 => divides_align1 off
  | k + 1 => by
    unfold restrictAux
    cases h : (Align.mk (k + 1)).check off with
    | true => exact (check_eq_true_iff ⟨k + 1⟩ off).mp h
    | false => exact restrictAux_divides off k

theorem restrictForOffset_le (base : Align) (off : Nat) :
    (restrictForOffset base off).pow2 ≤ base.pow2 :=
  restrictAux_le off base.pow2

theorem restrictForOffset_divides_offset (base : Align) (off : Nat) :
    (restrictForOffset base off).Divides off :=
  restrictAux_divides off base.pow2

theorem restrictForOffset_divides_addr {base : Align} {addr off : Nat}
    (haddr : base.Divides addr) :
    (restrictForOffset base off).Divides (addr + off) := by
  have h1 : (restrictForOffset base off).Divides addr :=
    divides_mono (restrictForOffset_le base off) haddr
  have h2 : (restrictForOffset base off).Divides off :=
    restrictForOffset_divides_offset base off
  exact divides_add h1 h2

end Align

/-! ## 2. Byte-Addressed Memory Model and Alignment Validity Invariants -/

/-- A single byte-addressed allocation in memory. -/
structure Alloc where
  baseAddr : Nat
  allocAlign : Align
  size : Nat
  bytes : List Nat
  live : Bool
  deriving Repr, DecidableEq

/-- Well-formedness of an allocation: aligned base and exact byte-length match. -/
def Alloc.WellFormed (al : Alloc) : Prop :=
  al.allocAlign.Divides al.baseAddr ∧ al.bytes.length = al.size

/-- Linear byte-addressed memory with a monotonic bump address watermark. -/
structure Memory where
  allocs : List Alloc
  nextAddr : Nat
  deriving Repr, DecidableEq

/-- An address range `[addr, addr + size)` lies inside a live allocation in `m`. -/
def InBounds (m : Memory) (addr size : Nat) : Prop :=
  ∃ al, al ∈ m.allocs ∧ al.live = true ∧ al.baseAddr ≤ addr ∧ addr + size ≤ al.baseAddr + al.size

/-- Core per-type alignment + liveness invariant for a pointer/reference `(addr, size, reqAlign)`. -/
def PtrValidAligned (m : Memory) (addr size : Nat) (reqAlign : Align) : Prop :=
  InBounds m addr size ∧ reqAlign.Divides addr

/-- Read `len` bytes starting at `offset` within a byte list. -/
def sliceBytes (bs : List Nat) (offset len : Nat) : List Nat :=
  (bs.drop offset).take len

/-- Overwrite bytes starting at `offset` within a byte list. -/
def patchBytes (bs : List Nat) (offset : Nat) (vals : List Nat) : List Nat :=
  bs.take offset ++ vals ++ bs.drop (offset + vals.length)

theorem sliceBytes_length {bs : List Nat} {off len : Nat} (h : off + len ≤ bs.length) :
    (sliceBytes bs off len).length = len := by
  unfold sliceBytes
  rw [List.length_take, List.length_drop]
  have hle : len ≤ bs.length - off := Nat.le_sub_of_add_le' h
  exact Nat.min_eq_left hle

theorem patchBytes_length {bs vals : List Nat} {off : Nat} (h : off + vals.length ≤ bs.length) :
    (patchBytes bs off vals).length = bs.length := by
  unfold patchBytes
  rw [List.length_append, List.length_append, List.length_take, List.length_drop]
  have hoff : off ≤ bs.length := Nat.le_trans (Nat.le_add_right off vals.length) h
  rw [Nat.min_eq_left hoff]
  exact Nat.add_sub_of_le h

theorem sliceBytes_patchBytes_same {bs vals : List Nat} {off : Nat}
    (h : off + vals.length ≤ bs.length) :
    sliceBytes (patchBytes bs off vals) off vals.length = vals := by
  unfold sliceBytes patchBytes
  have hoff : off ≤ bs.length := Nat.le_trans (Nat.le_add_right off vals.length) h
  have hlen : (bs.take off).length = off := by
    rw [List.length_take, Nat.min_eq_left hoff]
  rw [List.append_assoc, List.drop_append_of_le_length (Nat.le_of_eq hlen.symm)]
  rw [List.drop_eq_nil_of_le (Nat.le_of_eq hlen), List.nil_append]
  rw [List.take_append_of_le_length (Nat.le_refl vals.length)]
  exact List.take_length

/-- Executable byte read across live allocations. -/
def readMemBytes (m : Memory) (addr size : Nat) : Option (List Nat) :=
  match m.allocs.find? (fun al =>
      al.live && Nat.ble al.baseAddr addr && Nat.ble (addr + size) (al.baseAddr + al.size)) with
  | none => none
  | some al => some (sliceBytes al.bytes (addr - al.baseAddr) size)

/-- Executable byte write across live allocations. -/
def writeMemBytesGo (addr size : Nat) (vals : List Nat) : List Alloc → Option (List Alloc)
  | [] => none
  | al :: rest =>
    if al.live && Nat.ble al.baseAddr addr && Nat.ble (addr + size) (al.baseAddr + al.size) then
      some ({ al with bytes := patchBytes al.bytes (addr - al.baseAddr) vals } :: rest)
    else
      match writeMemBytesGo addr size vals rest with
      | none => none
      | some rest' => some (al :: rest')

def writeMemBytes (m : Memory) (addr : Nat) (vals : List Nat) : Option Memory :=
  match writeMemBytesGo addr vals.length vals m.allocs with
  | none => none
  | some allocs' => some { m with allocs := allocs' }

/-- Deterministic aligned stack slot allocation: guarantees `reqAlign.Divides baseAddr`. -/
def allocAligned (m : Memory) (size : Nat) (reqAlign : Align) (initByte : Nat := 0) :
    Memory × Nat :=
  let base := Align.alignUp m.nextAddr reqAlign
  let al : Alloc := {
    baseAddr := base
    allocAlign := reqAlign
    size := size
    bytes := List.replicate size initByte
    live := true
  }
  ({ allocs := al :: m.allocs, nextAddr := base + size }, base)

/-- Mark an allocation dead (`StorageDead`). -/
def deallocAt (m : Memory) (baseAddr : Nat) : Memory :=
  { m with allocs := m.allocs.map (fun al =>
      if Nat.beq al.baseAddr baseAddr then { al with live := false } else al) }

theorem allocAligned_aligned (m : Memory) (size : Nat) (reqAlign : Align) (b : Nat) :
    reqAlign.Divides (allocAligned m size reqAlign b).2 := by
  unfold allocAligned
  exact Align.divides_alignUp m.nextAddr reqAlign

theorem allocAligned_inBounds (m : Memory) (size : Nat) (reqAlign : Align) (b : Nat) :
    InBounds (allocAligned m size reqAlign b).1 (allocAligned m size reqAlign b).2 size := by
  unfold allocAligned InBounds
  refine ⟨{ baseAddr := Align.alignUp m.nextAddr reqAlign
            allocAlign := reqAlign
            size := size
            bytes := List.replicate size b
            live := true }, ?_, rfl, Nat.le_refl _, Nat.le_refl _⟩
  exact List.Mem.head _

theorem allocAligned_ptrValidAligned (m : Memory) (size : Nat) (reqAlign : Align) (b : Nat) :
    PtrValidAligned (allocAligned m size reqAlign b).1 (allocAligned m size reqAlign b).2 size reqAlign :=
  ⟨allocAligned_inBounds m size reqAlign b, allocAligned_aligned m size reqAlign b⟩

theorem ble_false_of_lt {a b : Nat} (hlt : b < a) : Nat.ble a b = false := by
  cases h : Nat.ble a b with
  | false => rfl
  | true =>
    have hle : a ≤ b := (Iff.of_eq Nat.ble_eq).mp h
    exact False.elim (Nat.not_lt_of_ge hle hlt)

theorem readMemBytes_allocAligned_below {m : Memory} {addr size allocSz : Nat} {a : Align} {b : Nat}
    (hlt : addr < m.nextAddr) :
    readMemBytes (allocAligned m allocSz a b).1 addr size = readMemBytes m addr size := by
  unfold allocAligned readMemBytes
  dsimp only
  have hlt' : addr < Align.alignUp m.nextAddr a :=
    Nat.lt_of_lt_of_le hlt (Align.le_alignUp m.nextAddr a)
  have hble : Nat.ble (Align.alignUp m.nextAddr a) addr = false := ble_false_of_lt hlt'
  simp only [List.find?, Bool.true_and, hble, Bool.false_and]

theorem allocAligned_write_read_same (m : Memory) (vals : List Nat) (reqAlign : Align) :
    let (m1, base) := allocAligned m vals.length reqAlign 0
    ∃ m2, writeMemBytes m1 base vals = some m2 ∧
          readMemBytes m2 base vals.length = some vals := by
  dsimp only [allocAligned, writeMemBytes, readMemBytes]
  have h1 : Nat.ble (Align.alignUp m.nextAddr reqAlign) (Align.alignUp m.nextAddr reqAlign) = true :=
    (Iff.of_eq Nat.ble_eq).mpr (Nat.le_refl _)
  have h2 : Nat.ble (Align.alignUp m.nextAddr reqAlign + vals.length)
                    (Align.alignUp m.nextAddr reqAlign + vals.length) = true :=
    (Iff.of_eq Nat.ble_eq).mpr (Nat.le_refl _)
  have hcond : (true && Nat.ble (Align.alignUp m.nextAddr reqAlign) (Align.alignUp m.nextAddr reqAlign)
      && Nat.ble (Align.alignUp m.nextAddr reqAlign + vals.length)
                 (Align.alignUp m.nextAddr reqAlign + vals.length)) = true := by
    rw [h1, h2]
    rfl
  dsimp only [writeMemBytesGo]
  simp only [hcond, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  dsimp only [List.find?]
  rw [hcond]
  dsimp only
  rw [Nat.sub_self]
  have hle : 0 + vals.length ≤ (List.replicate vals.length 0).length := by
    rw [Nat.zero_add, List.length_replicate]
    exact Nat.le_refl vals.length
  rw [sliceBytes_patchBytes_same hle]

/-! ## 3. `#[repr(packed(N))]` Struct Layout and Place Projection Alignment Algebra -/

/-- Type descriptor carrying natural ABI alignment, size, `Copy`, `Drop`, and `Sized` metadata. -/
structure Ty where
  name : String
  size : Nat
  abiAlign : Align
  isCopy : Bool
  needsDrop : Bool
  isSized : Bool := true
  deriving Repr, DecidableEq

/-- A field specification before struct layout calculation. -/
structure FieldSpec where
  fieldName : String
  ty : Ty
  deriving Repr, DecidableEq

/-- Placed field descriptor after struct layout calculation. -/
structure PlacedField where
  fieldName : String
  ty : Ty
  offset : Nat
  placementAlign : Align
  deriving Repr, DecidableEq

/-- Computed struct layout for `#[repr(C)]` or `#[repr(C, packed(N))]`. -/
structure StructLayout where
  pack : Option Align
  fields : List PlacedField
  outerAlign : Align
  size : Nat
  deriving Repr, DecidableEq

/-- Clamp a field's placement alignment by `pack`: `min(field.abiAlign, pack)`. -/
def clampAlign (fieldAlign : Align) (pack : Option Align) : Align :=
  match pack with
  | none => fieldAlign
  | some p => Align.minAlign fieldAlign p

theorem clampAlign_le_field (fa : Align) (pack : Option Align) :
    (clampAlign fa pack).pow2 ≤ fa.pow2 := by
  cases pack with
  | none => exact Nat.le_refl fa.pow2
  | some p => exact Align.minAlign_le_left fa p

theorem clampAlign_le_pack (fa p : Align) :
    (clampAlign fa (some p)).pow2 ≤ p.pow2 :=
  Align.minAlign_le_right fa p

/-- Sequential C-order struct layout calculator (models `rustc_abi::LayoutCalculator::univariant_biased`). -/
def placeFieldsAux (pack : Option Align) (curOff : Nat) (curAlign : Align) :
    List FieldSpec → List PlacedField × Nat × Align
  | [] => ([], curOff, curAlign)
  | f :: rest =>
    let fa := clampAlign f.ty.abiAlign pack
    let off := Align.alignUp curOff fa
    let pf : PlacedField := {
      fieldName := f.fieldName
      ty := f.ty
      offset := off
      placementAlign := fa
    }
    let nextAlign := Align.maxAlign curAlign fa
    let (pfs, endOff, finalAlign) := placeFieldsAux pack (off + f.ty.size) nextAlign rest
    (pf :: pfs, endOff, finalAlign)

def computeStructLayout (pack : Option Align) (fields : List FieldSpec) : StructLayout :=
  let (pfs, rawSize, outerAlign) := placeFieldsAux pack 0 Align.align1 fields
  {
    pack := pack
    fields := pfs
    outerAlign := outerAlign
    size := Align.alignUp rawSize outerAlign
  }

theorem placeFieldsAux_align_le_pack (p : Align) (curOff : Nat) (curAlign : Align)
    (hcur : curAlign.pow2 ≤ p.pow2) (fs : List FieldSpec) :
    (placeFieldsAux (some p) curOff curAlign fs).2.2.pow2 ≤ p.pow2 := by
  induction fs generalizing curOff curAlign with
  | nil => exact hcur
  | cons f rest ih =>
    unfold placeFieldsAux
    apply ih
    have hfa : (clampAlign f.ty.abiAlign (some p)).pow2 ≤ p.pow2 := clampAlign_le_pack _ _
    exact Nat.max_le.mpr ⟨hcur, hfa⟩

/-- Theorem: `#[repr(C, packed(P))]` caps the outer struct alignment at `≤ P`. -/
theorem layout_outer_align_le_pack (p : Align) (fields : List FieldSpec) :
    (computeStructLayout (some p) fields).outerAlign.pow2 ≤ p.pow2 := by
  unfold computeStructLayout
  exact placeFieldsAux_align_le_pack p 0 Align.align1 (Nat.zero_le p.pow2) fields

theorem placeFieldsAux_offsets_divisible (pack : Option Align) (curOff : Nat) (curAlign : Align)
    (fs : List FieldSpec) :
    ∀ pf, pf ∈ (placeFieldsAux pack curOff curAlign fs).1 →
      pf.placementAlign.Divides pf.offset := by
  induction fs generalizing curOff curAlign with
  | nil =>
    intro pf hmem
    cases hmem
  | cons f rest ih =>
    intro pf hmem
    unfold placeFieldsAux at hmem
    cases hmem with
    | head =>
      exact Align.divides_alignUp curOff (clampAlign f.ty.abiAlign pack)
    | tail _ htail =>
      exact ih _ _ pf htail

/-- Theorem: Every field placed by `computeStructLayout` has offset divisible by `min(field.align, pack)`. -/
theorem layout_field_offset_divisible (pack : Option Align) (fields : List FieldSpec) :
    ∀ pf, pf ∈ (computeStructLayout pack fields).fields →
      pf.placementAlign.Divides pf.offset :=
  placeFieldsAux_offsets_divisible pack 0 Align.align1 fields

/-! ## 4. Place Projections, `place_unalignment`, and `effAlign` -/

/-- MIR place projection element (`.deref` or `.field`). -/
inductive ProjElem where
  | deref (pointeeTy : Ty)
  | field (fieldIdx : Nat) (offset : Nat) (containerPack : Option Align) (fieldTy : Ty)
  deriving Repr, DecidableEq

/-- A MIR place rooted at `localId` with known local alignment `baseAlign`. -/
structure Place where
  localId : Nat
  baseAlign : Align
  projs : List ProjElem
  deriving Repr, DecidableEq

def Place.local (id : Nat) (a : Align) : Place :=
  { localId := id, baseAlign := a, projs := [] }

/-- Models `rustc_const_eval::util::most_packed_projection`:
    walks projections in reverse, stops at `Deref`, and takes the minimum enclosing `pack`. -/
def mostPackedRev : List ProjElem → Option Align
  | [] => none
  | .deref _ :: _ => none
  | .field _ _ pack _ :: rest =>
    match pack, mostPackedRev rest with
    | none, r => r
    | some p, none => some p
    | some p, some q => some (Align.minAlign p q)

def mostPackedAfterLastDeref (projs : List ProjElem) : Option Align :=
  mostPackedRev projs.reverse

/-- Models `rustc_const_eval::util::place_unalignment`:
    returns `true` iff the place crosses a packed container whose minimum pack alignment
    is strictly smaller than the required alignment `reqAlign` (or the type is unsized). -/
def placeUnaligned (p : Place) (reqAlign : Align) (isSized : Bool := true) : Bool :=
  match mostPackedAfterLastDeref p.projs with
  | none => false
  | some pack =>
    if isSized && Align.leBool reqAlign pack then false else true

theorem placeUnaligned_local (id : Nat) (a req : Align) (sz : Bool) :
    placeUnaligned (Place.local id a) req sz = false := rfl

/-- Codegen/semantic effective alignment across a projection chain:
    - `.deref pointeeTy` resets effective alignment to `pointeeTy.abiAlign`
      (matching `OperandRef::deref` in `rustc_codegen_ssa/src/mir/operand.rs:275-289`);
    - `.field offset containerPack _` clamps via `restrictForOffset` (matching
      `PlaceRef::project_field` in `rustc_codegen_ssa/src/mir/place.rs:173`) and `containerPack`. -/
def effAlignProjs (cur : Align) : List ProjElem → Align
  | [] => cur
  | .deref pointeeTy :: rest => effAlignProjs pointeeTy.abiAlign rest
  | .field _ off pack _ :: rest =>
    let a1 := Align.restrictForOffset cur off
    let a2 := clampAlign a1 pack
    effAlignProjs a2 rest

def Place.effAlign (p : Place) : Align :=
  effAlignProjs p.baseAlign p.projs

/-- Address offset of a deref-free projection chain starting from `baseAddr`. -/
def evalDerefFreeOffset : List ProjElem → Nat
  | [] => 0
  | .deref _ :: rest => evalDerefFreeOffset rest
  | .field _ off _ _ :: rest => off + evalDerefFreeOffset rest

def hasNoDeref : List ProjElem → Bool
  | [] => true
  | .deref _ :: _ => false
  | .field _ _ _ _ :: rest => hasNoDeref rest

theorem effAlignProjs_divides_derefFree :
    ∀ (projs : List ProjElem) (cur : Align) (addr : Nat),
      hasNoDeref projs = true →
      cur.Divides addr →
      (effAlignProjs cur projs).Divides (addr + evalDerefFreeOffset projs)
  | [], cur, addr, _, hcur => by
    unfold evalDerefFreeOffset effAlignProjs
    rw [Nat.add_zero]
    exact hcur
  | .deref _ :: _, _, _, hnd, _ => by
    unfold hasNoDeref at hnd
    cases hnd
  | .field _ off pack _ :: rest, cur, addr, hnd, hcur => by
    unfold hasNoDeref at hnd
    unfold evalDerefFreeOffset effAlignProjs
    rw [← Nat.add_assoc]
    have h1 : (Align.restrictForOffset cur off).Divides (addr + off) :=
      Align.restrictForOffset_divides_addr hcur
    have h2 : (clampAlign (Align.restrictForOffset cur off) pack).Divides (addr + off) :=
      Align.divides_mono (clampAlign_le_field _ pack) h1
    exact effAlignProjs_divides_derefFree rest _ (addr + off) hnd h2

/-- Layout-derived alignment witness along a deref-free projection chain. -/
def WellAlignedAtEnd (reqAlign : Align) : Align → List ProjElem → Prop
  | curAlign, [] => reqAlign.pow2 ≤ curAlign.pow2
  | _, .deref _ :: _ => False
  | curAlign, .field _ off pack fty :: rest =>
    (clampAlign fty.abiAlign pack).Divides off ∧
    (clampAlign fty.abiAlign pack).pow2 ≤ curAlign.pow2 ∧
    WellAlignedAtEnd reqAlign (clampAlign fty.abiAlign pack) rest

theorem wellAlignedAtEnd_divides :
    ∀ (projs : List ProjElem) (curAlign reqAlign : Align) (addr : Nat),
      curAlign.Divides addr →
      WellAlignedAtEnd reqAlign curAlign projs →
      reqAlign.Divides (addr + evalDerefFreeOffset projs)
  | [], curAlign, reqAlign, addr, hcur, hle => by
    unfold evalDerefFreeOffset
    rw [Nat.add_zero]
    exact Align.divides_mono hle hcur
  | .deref _ :: _, _, _, _, _, hwf => False.elim hwf
  | .field _ off pack fty :: rest, curAlign, reqAlign, addr, hcur, ⟨hoff, hle, hrest⟩ => by
    unfold evalDerefFreeOffset
    rw [← Nat.add_assoc]
    have ha : (clampAlign fty.abiAlign pack).Divides addr := Align.divides_mono hle hcur
    have hsum : (clampAlign fty.abiAlign pack).Divides (addr + off) := Align.divides_add ha hoff
    exact wellAlignedAtEnd_divides rest (clampAlign fty.abiAlign pack) reqAlign (addr + off) hsum hrest

theorem wellAlignedAtEnd_of_unpacked_or_sufficient_pack
    {baseAlign reqAlign : Align} {off : Nat} {pack : Option Align} {fty : Ty}
    (hpack : match pack with | none => True | some p => reqAlign.pow2 ≤ p.pow2)
    (hfty : reqAlign.pow2 ≤ fty.abiAlign.pow2)
    (hbase : (clampAlign fty.abiAlign pack).pow2 ≤ baseAlign.pow2)
    (hoff : (clampAlign fty.abiAlign pack).Divides off) :
    WellAlignedAtEnd reqAlign baseAlign [.field 0 off pack fty] := by
  refine ⟨hoff, hbase, ?_⟩
  cases pack with
  | none => exact hfty
  | some p => exact Nat.le_min.mpr ⟨hfty, hpack⟩

/-! ## 5. MIR Statements, User Bodies vs. Synthesized Shims, and Dual Semantics -/

/-- Classification of MIR bodies in `rustc`. -/
inductive BodyKind where
  | userFn
  | dropGlueShim
  | vtableShim
  deriving Repr, DecidableEq

/-- MIR statements modeling packed field access, borrows, raw pointers, drops,
    `AddMovesForPackedDrops` staging, and `CheckAlignment` assertions. -/
inductive Stmt where
  | storageLive (localId : Nat) (size : Nat) (align : Align)
  | storageDead (localId : Nat)
  | copyFromPlace (dstLocal : Nat) (src : Place) (ty : Ty)
  | moveUnaligned (dstLocal : Nat) (src : Place) (size : Nat)
  | mkRef (dstLocal : Nat) (src : Place) (ty : Ty)
  | mkRawPtr (dstLocal : Nat) (src : Place)
  | derefLoad (dstLocal : Nat) (ptrLocal : Nat) (ty : Ty)
  | derefMutRef (dstLocal : Nat) (ptrLocal : Nat) (ty : Ty)
  | checkAlignAssert (ptrLocal : Nat) (reqAlign : Align)
  | dropPlace (target : Place) (ty : Ty)
  | callDropInPlace (ptrLocal : Nat) (ty : Ty)
  deriving Repr, DecidableEq

/-- A single MIR body (user function or synthesized shim). -/
structure MirBody where
  name : String
  kind : BodyKind
  stmts : List Stmt
  deriving Repr, DecidableEq

/-- A synthesized `DropGlue` shim descriptor for a concrete type `ty`. -/
structure DropShimSpec where
  targetTy : Ty
  body : MirBody
  deriving Repr, DecidableEq

/-- A complete program: an entry user body plus a table of synthesized `DropGlue` shims. -/
structure Program where
  entry : MirBody
  dropShims : List DropShimSpec
  deriving Repr, DecidableEq

def Program.findDropShim (prog : Program) (ty : Ty) : Option MirBody :=
  match prog.dropShims.find? (fun s => decide (s.targetTy = ty)) with
  | none => none
  | some s => some s.body

/-- Canonical synthesized `DropGlue` shim for a type `ty`:
    takes pointer in local `0` (`_1` in rustc), creates `&mut (*_1)` and invokes `Drop::drop`. -/
def makeDropShimFor (ty : Ty) : DropShimSpec :=
  {
    targetTy := ty
    body := {
      name := s!"drop_glue<{ty.name}>"
      kind := .dropGlueShim
      stmts := [
        .derefMutRef 1 0 ty
      ]
    }
  }

/-! ## 6. Compiler Passes: `CheckPackedRef` (`E0793`), `AddMovesForPackedDrops`, `CheckAlignment` -/

/-- Static `CheckPackedRef` (`E0793`, `compiler/rustc_mir_transform/src/check_packed_ref.rs`):
    rejects any `mkRef` on a place where `placeUnaligned` is `true`, while allowing
    `copyFromPlace`, `mkRawPtr`, and sufficiently-aligned `mkRef`. -/
def checkPackedRefStmt : Stmt → Bool
  | .mkRef _ src ty => !(placeUnaligned src ty.abiAlign ty.isSized)
  | _ => true

def checkPackedRefBody (b : MirBody) : Bool :=
  b.stmts.all checkPackedRefStmt

/-- `AddMovesForPackedDrops` (`compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs`):
    rewrites every `dropPlace target ty` where `placeUnaligned target ty.abiAlign = true`
    into aligned stack staging:
      `StorageLive(tmp); tmp = move_unaligned(target); drop(tmp); StorageDead(tmp);` -/
def stagePackedDropsList (nextTemp : Nat) : List Stmt → List Stmt
  | [] => []
  | .dropPlace target ty :: rest =>
    if placeUnaligned target ty.abiAlign ty.isSized then
      [ .storageLive nextTemp ty.size ty.abiAlign,
        .moveUnaligned nextTemp target ty.size,
        .dropPlace (Place.local nextTemp ty.abiAlign) ty,
        .storageDead nextTemp ] ++ stagePackedDropsList (nextTemp + 1) rest
    else
      .dropPlace target ty :: stagePackedDropsList nextTemp rest
  | s :: rest => s :: stagePackedDropsList nextTemp rest

def addMovesForPackedDropsBody (freshBase : Nat) (b : MirBody) : MirBody :=
  { b with stmts := stagePackedDropsList freshBase b.stmts }

/-- `CheckAlignment` (`compiler/rustc_mir_transform/src/check_alignment.rs` + `check_pointers.rs`):
    inserts `checkAlignAssert` before every raw-pointer dereference of a **sized** type
    (`pointee_ty.is_sized`, `check_pointers.rs:209`) with `abiAlign > 1`
    (skipping `u8`/`i8`/`bool` at `check_alignment.rs:21`). -/
def checkAlignmentStmts : List Stmt → List Stmt
  | [] => []
  | (.derefLoad dst ptr ty) :: rest =>
    if ty.isSized && Align.ltBool Align.align1 ty.abiAlign then
      .checkAlignAssert ptr ty.abiAlign :: .derefLoad dst ptr ty :: checkAlignmentStmts rest
    else
      .derefLoad dst ptr ty :: checkAlignmentStmts rest
  | (.derefMutRef dst ptr ty) :: rest =>
    if ty.isSized && Align.ltBool Align.align1 ty.abiAlign then
      .checkAlignAssert ptr ty.abiAlign :: .derefMutRef dst ptr ty :: checkAlignmentStmts rest
    else
      .derefMutRef dst ptr ty :: checkAlignmentStmts rest
  | s :: rest => s :: checkAlignmentStmts rest

def checkAlignmentBody (b : MirBody) : MirBody :=
  { b with stmts := checkAlignmentStmts b.stmts }

/-- Policy A (`instrumentUserOnly`): models `rustc`'s actual pipeline (`lib.rs:695` + `shim.rs:231-246`),
    running `CheckAlignment` ONLY on `.userFn` bodies while leaving synthesized shims uninstrumented. -/
def instrumentUserOnly (prog : Program) : Program :=
  {
    entry := match prog.entry.kind with
             | .userFn => checkAlignmentBody prog.entry
             | _ => prog.entry
    dropShims := prog.dropShims
  }

/-- Policy B (`instrumentWholeProgram`): instruments BOTH `.userFn` bodies AND every
    synthesized `DropGlue` / `VTable` shim. -/
def instrumentWholeProgram (prog : Program) : Program :=
  {
    entry := checkAlignmentBody prog.entry
    dropShims := prog.dropShims.map (fun s => { s with body := checkAlignmentBody s.body })
  }

/-- Parameterized policy toggling whether synthesized shims are instrumented. -/
def policyOf (instrumentShims : Bool) : Program → Program :=
  match instrumentShims with
  | false => instrumentUserOnly
  | true => instrumentWholeProgram

/-! ## 7. Operational Semantics: Strict Miri UB vs. Native `-Z ub-checks` Execution -/

/-- A drop event recorded in the observable execution trace. -/
structure DropEvent where
  tyName : String
  selfAddr : Nat
  reqAlign : Align
  payload : List Nat
  deriving Repr, DecidableEq

/-- Machine state: byte-addressed memory, local -> address/value map, and recorded drops. -/
structure ExecState where
  mem : Memory
  localAddr : List (Nat × Nat)
  ptrVal : List (Nat × Nat)
  drops : List DropEvent
  deriving Repr, DecidableEq

def lookupNat (env : List (Nat × Nat)) (k : Nat) : Option Nat :=
  match env.find? (fun p => Nat.beq p.1 k) with
  | none => none
  | some (_, v) => some v

def setNat (env : List (Nat × Nat)) (k v : Nat) : List (Nat × Nat) :=
  (k, v) :: env

theorem lookupNat_setNat_same (env : List (Nat × Nat)) (k v : Nat) :
    lookupNat (setNat env k v) k = some v := by
  unfold lookupNat setNat
  simp only [List.find?]
  have h : Nat.beq k k = true := Nat.beq_refl k
  rw [h]

theorem lookupNat_setNat_ne (env : List (Nat × Nat)) {k1 k2 : Nat} (v : Nat)
    (hne : k1 ≠ k2) :
    lookupNat (setNat env k1 v) k2 = lookupNat env k2 := by
  unfold lookupNat setNat
  simp only [List.find?]
  have hbeq : Nat.beq k1 k2 = false := by
    cases h : Nat.beq k1 k2 with
    | false => rfl
    | true => exact False.elim (hne (Nat.eq_of_beq_eq_true h))
  rw [hbeq]

/-- Resolve the byte address of a deref-free place in `st`. -/
def evalPlaceAddr (st : ExecState) (p : Place) : Option Nat :=
  if hasNoDeref p.projs then
    match lookupNat st.localAddr p.localId with
    | none => none
    | some base => some (base + evalDerefFreeOffset p.projs)
  else
    none

/-- Outcome of executing a MIR body/program. -/
inductive Outcome where
  | ok (st : ExecState)
  | ubMisaligned (op : String) (addr : Nat) (reqAlign : Align)
  | ubTrap (addr : Nat) (reqAlign : Align)
  | silentMisalignedExec (op : String) (addr : Nat) (reqAlign : Align) (st : ExecState)
  | runtimeError (msg : String)
  deriving Repr, DecidableEq

/-- Execution mode:
    - `strictMiri`: immediately faults `.ubMisaligned` on any misaligned ref/deref/drop;
    - `nativeUbChecks`: traps `.ubTrap` ONLY at explicit `.checkAlignAssert` statements,
      otherwise records `.silentMisalignedExec` when a misaligned UB operation executes unchecked. -/
inductive ExecMode where
  | strictMiri
  | nativeUbChecks
  deriving Repr, DecidableEq

/-- Execute a synthesized shim statement list under `mode`. -/
def execShimStmts (mode : ExecMode) : List Stmt → ExecState → Outcome
  | [], st => .ok st
  | s :: rest, st =>
    match s with
    | .checkAlignAssert ptrLocal reqAlign =>
      match lookupNat st.ptrVal ptrLocal with
      | none => .runtimeError "missing pointer local"
      | some addr =>
        match reqAlign.check addr with
        | true => execShimStmts mode rest st
        | false => .ubTrap addr reqAlign
    | .derefMutRef dst ptrLocal ty =>
      match lookupNat st.ptrVal ptrLocal with
      | none => .runtimeError "missing pointer local in shim"
      | some addr =>
        match ty.abiAlign.check addr with
        | true =>
          let payload := (readMemBytes st.mem addr ty.size).getD []
          let ev : DropEvent := { tyName := ty.name, selfAddr := addr, reqAlign := ty.abiAlign, payload := payload }
          execShimStmts mode rest { st with ptrVal := setNat st.ptrVal dst addr, drops := st.drops ++ [ev] }
        | false =>
          match mode with
          | .strictMiri => .ubMisaligned "shim_deref_mut_ref" addr ty.abiAlign
          | .nativeUbChecks =>
            let payload := (readMemBytes st.mem addr ty.size).getD []
            let ev : DropEvent := { tyName := ty.name, selfAddr := addr, reqAlign := ty.abiAlign, payload := payload }
            .silentMisalignedExec "shim_deref_mut_ref" addr ty.abiAlign
              { st with ptrVal := setNat st.ptrVal dst addr, drops := st.drops ++ [ev] }
    | .derefLoad dst ptrLocal ty =>
      match lookupNat st.ptrVal ptrLocal with
      | none => .runtimeError "missing pointer local in shim"
      | some addr =>
        match ty.abiAlign.check addr with
        | true => execShimStmts mode rest { st with ptrVal := setNat st.ptrVal dst addr }
        | false =>
          match mode with
          | .strictMiri => .ubMisaligned "shim_deref_load" addr ty.abiAlign
          | .nativeUbChecks => .silentMisalignedExec "shim_deref_load" addr ty.abiAlign st
    | _ => .runtimeError "unsupported stmt inside shim"

/-- Execute a main body against a program's shim table under `mode`. -/
def execStmts (prog : Program) (mode : ExecMode) : List Stmt → ExecState → Outcome
  | [], st => .ok st
  | s :: rest, st =>
    match s with
    | .storageLive locId size align =>
      let (mem', base) := allocAligned st.mem size align 0
      execStmts prog mode rest { st with mem := mem', localAddr := setNat st.localAddr locId base }
    | .storageDead locId =>
      match lookupNat st.localAddr locId with
      | none => .runtimeError "storageDead unknown local"
      | some base => execStmts prog mode rest { st with mem := deallocAt st.mem base }
    | .copyFromPlace dst src ty =>
      match evalPlaceAddr st src, lookupNat st.localAddr dst with
      | some srcAddr, some dstAddr =>
        match readMemBytes st.mem srcAddr ty.size with
        | none => .runtimeError "copyFromPlace OOB read"
        | some bs =>
          match writeMemBytes st.mem dstAddr bs with
          | none => .runtimeError "copyFromPlace OOB write"
          | some mem' => execStmts prog mode rest { st with mem := mem' }
      | _, _ => .runtimeError "copyFromPlace missing local"
    | .moveUnaligned dst src size =>
      match evalPlaceAddr st src, lookupNat st.localAddr dst with
      | some srcAddr, some dstAddr =>
        match readMemBytes st.mem srcAddr size with
        | none => .runtimeError "moveUnaligned OOB read"
        | some bs =>
          match writeMemBytes st.mem dstAddr bs with
          | none => .runtimeError "moveUnaligned OOB write"
          | some mem' => execStmts prog mode rest { st with mem := mem' }
      | _, _ => .runtimeError "moveUnaligned missing local"
    | .mkRawPtr dst src =>
      match evalPlaceAddr st src with
      | none => .runtimeError "mkRawPtr missing local"
      | some addr => execStmts prog mode rest { st with ptrVal := setNat st.ptrVal dst addr }
    | .mkRef dst src ty =>
      match evalPlaceAddr st src with
      | none => .runtimeError "mkRef missing local"
      | some addr =>
        match ty.abiAlign.check addr with
        | true => execStmts prog mode rest { st with ptrVal := setNat st.ptrVal dst addr }
        | false =>
          match mode with
          | .strictMiri => .ubMisaligned "mk_ref" addr ty.abiAlign
          | .nativeUbChecks => .silentMisalignedExec "mk_ref" addr ty.abiAlign st
    | .checkAlignAssert ptrLocal reqAlign =>
      match lookupNat st.ptrVal ptrLocal with
      | none => .runtimeError "checkAlignAssert missing ptr"
      | some addr =>
        match reqAlign.check addr with
        | true => execStmts prog mode rest st
        | false => .ubTrap addr reqAlign
    | .derefLoad dst ptrLocal ty =>
      match lookupNat st.ptrVal ptrLocal with
      | none => .runtimeError "derefLoad missing ptr"
      | some addr =>
        match ty.abiAlign.check addr with
        | true =>
          match readMemBytes st.mem addr ty.size, lookupNat st.localAddr dst with
          | some bs, some dstAddr =>
            match writeMemBytes st.mem dstAddr bs with
            | some mem' => execStmts prog mode rest { st with mem := mem' }
            | none => .runtimeError "derefLoad OOB write"
          | _, _ => .runtimeError "derefLoad OOB read"
        | false =>
          match mode with
          | .strictMiri => .ubMisaligned "deref_load" addr ty.abiAlign
          | .nativeUbChecks => .silentMisalignedExec "deref_load" addr ty.abiAlign st
    | .derefMutRef dst ptrLocal ty =>
      match lookupNat st.ptrVal ptrLocal with
      | none => .runtimeError "derefMutRef missing ptr"
      | some addr =>
        match ty.abiAlign.check addr with
        | true => execStmts prog mode rest { st with ptrVal := setNat st.ptrVal dst addr }
        | false =>
          match mode with
          | .strictMiri => .ubMisaligned "deref_mut_ref" addr ty.abiAlign
          | .nativeUbChecks => .silentMisalignedExec "deref_mut_ref" addr ty.abiAlign st
    | .dropPlace target ty =>
      match evalPlaceAddr st target with
      | none => .runtimeError "dropPlace missing local"
      | some addr =>
        match ty.abiAlign.check addr with
        | true =>
          let payload := (readMemBytes st.mem addr ty.size).getD []
          let ev : DropEvent := { tyName := ty.name, selfAddr := addr, reqAlign := ty.abiAlign, payload := payload }
          execStmts prog mode rest { st with drops := st.drops ++ [ev] }
        | false =>
          match mode with
          | .strictMiri => .ubMisaligned "drop_place" addr ty.abiAlign
          | .nativeUbChecks => .silentMisalignedExec "drop_place" addr ty.abiAlign st
    | .callDropInPlace ptrLocal ty =>
      match lookupNat st.ptrVal ptrLocal, prog.findDropShim ty with
      | some addr, some shimBody =>
        let shimInit : ExecState := { st with ptrVal := setNat st.ptrVal 0 addr }
        match execShimStmts mode shimBody.stmts shimInit with
        | .ok st' => execStmts prog mode rest { st' with ptrVal := st.ptrVal }
        | other => other
      | _, _ => .runtimeError "callDropInPlace missing ptr or shim"

def execProgram (prog : Program) (mode : ExecMode) (init : ExecState) : Outcome :=
  execStmts prog mode prog.entry.stmts init

/-! ## 8. Core Theorem 1: Alignment-Preserving Soundness of `addMovesForPackedDrops` -/

/-- Every drop event in `st.drops` observed an aligned `selfAddr`. -/
def AllDropsAligned (st : ExecState) : Prop :=
  ∀ ev, ev ∈ st.drops → ev.reqAlign.Divides ev.selfAddr

theorem allDropsAligned_append {st : ExecState} {ev : DropEvent}
    (hprev : AllDropsAligned st) (hev : ev.reqAlign.Divides ev.selfAddr) :
    AllDropsAligned { st with drops := st.drops ++ [ev] } := by
  intro e he
  rcases List.mem_append.mp he with h1 | h2
  · exact hprev e h1
  · cases h2 with
    | head => exact hev
    | tail _ hnil => cases hnil

/-- Static completeness of `stagePackedDropsList`: ZERO unaligned `.dropPlace` statements
    remain after running `AddMovesForPackedDrops`. -/
def NoUnalignedDrops : List Stmt → Prop
  | [] => True
  | .dropPlace target ty :: rest =>
    placeUnaligned target ty.abiAlign ty.isSized = false ∧ NoUnalignedDrops rest
  | _ :: rest => NoUnalignedDrops rest

theorem stagePackedDropsList_no_unaligned_drops (nextTemp : Nat) (stmts : List Stmt) :
    NoUnalignedDrops (stagePackedDropsList nextTemp stmts) := by
  induction stmts generalizing nextTemp with
  | nil => trivial
  | cons s rest ih =>
    cases s with
    | dropPlace target ty =>
      unfold stagePackedDropsList
      cases hu : placeUnaligned target ty.abiAlign ty.isSized with
      | true =>
        simp only [↓reduceIte, List.cons_append, List.nil_append]
        unfold NoUnalignedDrops
        exact ⟨placeUnaligned_local nextTemp ty.abiAlign ty.abiAlign ty.isSized, ih (nextTemp + 1)⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        unfold NoUnalignedDrops
        exact ⟨hu, ih nextTemp⟩
    | storageLive _ _ _ => exact ih nextTemp
    | storageDead _ => exact ih nextTemp
    | copyFromPlace _ _ _ => exact ih nextTemp
    | moveUnaligned _ _ _ => exact ih nextTemp
    | mkRef _ _ _ => exact ih nextTemp
    | mkRawPtr _ _ => exact ih nextTemp
    | derefLoad _ _ _ => exact ih nextTemp
    | derefMutRef _ _ _ => exact ih nextTemp
    | checkAlignAssert _ _ => exact ih nextTemp
    | callDropInPlace _ _ => exact ih nextTemp

/-- Theorem 1: Alignment-preserving soundness & exact drop-payload preservation for every
    staged packed drop emitted by `addMovesForPackedDrops`. -/
theorem addMovesForPackedDrops_alignment_sound
    (prog : Program) (mode : ExecMode) (st : ExecState)
    (tmp : Nat) (target : Place) (ty : Ty)
    (srcAddr : Nat) (payload : List Nat) (rest : List Stmt)
    (haddr : evalPlaceAddr st target = some srcAddr)
    (hlt : srcAddr < st.mem.nextAddr)
    (hread : readMemBytes st.mem srcAddr ty.size = some payload)
    (hlen : payload.length = ty.size)
    (hfresh : tmp ≠ target.localId) :
    ∃ st_mid base,
      ty.abiAlign.Divides base ∧
      execStmts prog mode
        ([ .storageLive tmp ty.size ty.abiAlign,
           .moveUnaligned tmp target ty.size,
           .dropPlace (Place.local tmp ty.abiAlign) ty,
           .storageDead tmp ] ++ rest) st
      = execStmts prog mode rest st_mid ∧
      st_mid.drops = st.drops ++ [{ tyName := ty.name, selfAddr := base, reqAlign := ty.abiAlign, payload := payload }] := by
  have hbase_div : ty.abiAlign.Divides (allocAligned st.mem ty.size ty.abiAlign 0).2 :=
    allocAligned_aligned st.mem ty.size ty.abiAlign 0
  have hbase_chk : ty.abiAlign.check (allocAligned st.mem ty.size ty.abiAlign 0).2 = true :=
    (Align.check_eq_true_iff _ _).mpr hbase_div
  have hlookup_target :
      lookupNat (setNat st.localAddr tmp (allocAligned st.mem ty.size ty.abiAlign 0).2) target.localId =
      lookupNat st.localAddr target.localId :=
    lookupNat_setNat_ne st.localAddr _ hfresh
  have htarget_eq :
      evalPlaceAddr
        { st with
          mem := (allocAligned st.mem ty.size ty.abiAlign 0).1
          localAddr := setNat st.localAddr tmp (allocAligned st.mem ty.size ty.abiAlign 0).2 }
        target = some srcAddr := by
    unfold evalPlaceAddr at haddr ⊢
    rw [hlookup_target]
    exact haddr
  have hlookup_tmp :
      lookupNat (setNat st.localAddr tmp (allocAligned st.mem ty.size ty.abiAlign 0).2) tmp =
      some (allocAligned st.mem ty.size ty.abiAlign 0).2 :=
    lookupNat_setNat_same st.localAddr tmp _
  have hread_m1 :
      readMemBytes (allocAligned st.mem ty.size ty.abiAlign 0).1 srcAddr ty.size = some payload := by
    rw [readMemBytes_allocAligned_below hlt]
    exact hread
  have hwr_rd := allocAligned_write_read_same st.mem payload ty.abiAlign
  rw [hlen] at hwr_rd
  rcases hwr_rd with ⟨m2, hm2_write, hm2_read⟩
  have hdrop_place_addr :
      evalPlaceAddr
        { st with
          mem := m2
          localAddr := setNat st.localAddr tmp (allocAligned st.mem ty.size ty.abiAlign 0).2 }
        (Place.local tmp ty.abiAlign) =
      some (allocAligned st.mem ty.size ty.abiAlign 0).2 := by
    unfold evalPlaceAddr Place.local hasNoDeref evalDerefFreeOffset
    simp only [↓reduceIte, hlookup_tmp, Nat.add_zero]
  refine ⟨{ st with
            mem := deallocAt m2 (allocAligned st.mem ty.size ty.abiAlign 0).2
            localAddr := setNat st.localAddr tmp (allocAligned st.mem ty.size ty.abiAlign 0).2
            drops := st.drops ++ [{ tyName := ty.name, selfAddr := (allocAligned st.mem ty.size ty.abiAlign 0).2, reqAlign := ty.abiAlign, payload := payload }] },
          (allocAligned st.mem ty.size ty.abiAlign 0).2, hbase_div, ?_, rfl⟩
  have hm2_write' :
      writeMemBytes (allocAligned st.mem ty.size ty.abiAlign 0).1
        (allocAligned st.mem ty.size ty.abiAlign 0).2 payload = some m2 := hm2_write
  have hm2_read' :
      readMemBytes m2 (allocAligned st.mem ty.size ty.abiAlign 0).2 ty.size = some payload := hm2_read
  dsimp only [List.cons_append, List.nil_append, execStmts]
  rw [htarget_eq, hlookup_tmp]
  dsimp only
  rw [hread_m1]
  dsimp only
  rw [hm2_write']
  dsimp only
  rw [hdrop_place_addr]
  dsimp only
  rw [hbase_chk]
  dsimp only
  rw [hm2_read']
  dsimp only [Option.getD]

/-! ## 9. Core Theorem 2: Static Absence of Misaligned Safe References Under `E0793` + `Copy` Staging -/

/-- A statement belongs to the safe Rust MIR subset (no raw-pointer deref, no raw `drop_in_place`). -/
def IsSafeStmt : Stmt → Prop
  | .storageLive _ _ _ => True
  | .storageDead _ => True
  | .copyFromPlace _ _ _ => True
  | .moveUnaligned _ _ _ => True
  | .mkRef _ _ _ => True
  | .mkRawPtr _ _ => True
  | .dropPlace _ _ => True
  | .derefLoad _ _ _ => False
  | .derefMutRef _ _ _ => False
  | .checkAlignAssert _ _ => False
  | .callDropInPlace _ _ => False

def IsSafeBody (stmts : List Stmt) : Prop :=
  ∀ s, s ∈ stmts → IsSafeStmt s

/-- Soundness contract of `place_unalignment` (established structurally by
    `wellAlignedAtEnd_divides` + `computeStructLayout`): whenever `placeUnaligned`
    returns `false`, the runtime place address satisfies `ty.abiAlign.Divides addr`. -/
def PlaceUnalignmentSound : Prop :=
  ∀ (st : ExecState) (p : Place) (ty : Ty) (addr : Nat),
    placeUnaligned p ty.abiAlign ty.isSized = false →
    evalPlaceAddr st p = some addr →
    ty.abiAlign.Divides addr

/-- Outcome predicate asserting absence of alignment UB and alignment of all executed drops. -/
def NoAlignmentUb : Outcome → Prop
  | .ok st => AllDropsAligned st
  | .ubMisaligned _ _ _ => False
  | .ubTrap _ _ => True
  | .silentMisalignedExec _ _ _ _ => False
  | .runtimeError _ => True

theorem stagePackedDropsList_preserves_safe (nextTemp : Nat) (stmts : List Stmt)
    (hsafe : IsSafeBody stmts) :
    IsSafeBody (stagePackedDropsList nextTemp stmts) := by
  induction stmts generalizing nextTemp with
  | nil =>
    intro s hm
    cases hm
  | cons s rest ih =>
    have hs : IsSafeStmt s := hsafe s (List.Mem.head _)
    have hrest : IsSafeBody rest := fun x hx => hsafe x (List.Mem.tail _ hx)
    cases s with
    | dropPlace target ty =>
      unfold stagePackedDropsList
      cases placeUnaligned target ty.abiAlign ty.isSized with
      | true =>
        simp only [↓reduceIte, List.cons_append, List.nil_append]
        intro x hx
        cases hx with
        | head => trivial
        | tail _ hx =>
          cases hx with
          | head => trivial
          | tail _ hx =>
            cases hx with
            | head => trivial
            | tail _ hx =>
              cases hx with
              | head => trivial
              | tail _ hx => exact ih (nextTemp + 1) hrest x hx
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        intro x hx
        cases hx with
        | head => trivial
        | tail _ hx => exact ih nextTemp hrest x hx
    | storageLive _ _ _ =>
      intro x hx
      cases hx with
      | head => trivial
      | tail _ hx => exact ih nextTemp hrest x hx
    | storageDead _ =>
      intro x hx
      cases hx with
      | head => trivial
      | tail _ hx => exact ih nextTemp hrest x hx
    | copyFromPlace _ _ _ =>
      intro x hx
      cases hx with
      | head => trivial
      | tail _ hx => exact ih nextTemp hrest x hx
    | moveUnaligned _ _ _ =>
      intro x hx
      cases hx with
      | head => trivial
      | tail _ hx => exact ih nextTemp hrest x hx
    | mkRef _ _ _ =>
      intro x hx
      cases hx with
      | head => trivial
      | tail _ hx => exact ih nextTemp hrest x hx
    | mkRawPtr _ _ =>
      intro x hx
      cases hx with
      | head => trivial
      | tail _ hx => exact ih nextTemp hrest x hx
    | derefLoad _ _ _ => exact False.elim hs
    | derefMutRef _ _ _ => exact False.elim hs
    | checkAlignAssert _ _ => exact False.elim hs
    | callDropInPlace _ _ => exact False.elim hs

theorem stagePackedDropsList_preserves_e0793 (nextTemp : Nat) (stmts : List Stmt)
    (he : stmts.all checkPackedRefStmt = true) :
    (stagePackedDropsList nextTemp stmts).all checkPackedRefStmt = true := by
  induction stmts generalizing nextTemp with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at he
    cases s with
    | dropPlace target ty =>
      unfold stagePackedDropsList
      cases placeUnaligned target ty.abiAlign ty.isSized with
      | true =>
        simp only [↓reduceIte, List.cons_append, List.nil_append, List.all_cons, checkPackedRefStmt, Bool.true_and]
        exact ih (nextTemp + 1) he.2
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.all_cons, checkPackedRefStmt, Bool.true_and]
        exact ih nextTemp he.2
    | storageLive _ _ _ | storageDead _ | copyFromPlace _ _ _ | moveUnaligned _ _ _
    | mkRef _ _ _ | mkRawPtr _ _ | derefLoad _ _ _ | derefMutRef _ _ _
    | checkAlignAssert _ _ | callDropInPlace _ _ =>
      simp only [stagePackedDropsList, List.all_cons, Bool.and_eq_true]
      exact ⟨he.1, ih nextTemp he.2⟩

theorem safe_exec_no_alignment_ub
    (prog : Program) (mode : ExecMode)
    (hsound : PlaceUnalignmentSound)
    (stmts : List Stmt)
    (hsafe : IsSafeBody stmts)
    (he0793 : stmts.all checkPackedRefStmt = true)
    (hnodrop : NoUnalignedDrops stmts)
    (st : ExecState) (hdrops : AllDropsAligned st) :
    NoAlignmentUb (execStmts prog mode stmts st) := by
  induction stmts generalizing st with
  | nil =>
    dsimp only [execStmts, NoAlignmentUb]
    exact hdrops
  | cons s rest ih =>
    have hs : IsSafeStmt s := hsafe s (List.Mem.head _)
    have hrest_safe : IsSafeBody rest := fun x hx => hsafe x (List.Mem.tail _ hx)
    simp only [List.all_cons, Bool.and_eq_true] at he0793
    cases s with
    | storageLive locId size align =>
      dsimp only [execStmts]
      exact ih hrest_safe he0793.2 hnodrop _ hdrops
    | storageDead locId =>
      dsimp only [execStmts]
      cases lookupNat st.localAddr locId with
      | none => trivial
      | some base => exact ih hrest_safe he0793.2 hnodrop _ hdrops
    | copyFromPlace dst src ty =>
      dsimp only [execStmts]
      cases evalPlaceAddr st src with
      | none => trivial
      | some srcAddr =>
        cases lookupNat st.localAddr dst with
        | none => trivial
        | some dstAddr =>
          dsimp only
          cases readMemBytes st.mem srcAddr ty.size with
          | none => trivial
          | some bs =>
            dsimp only
            cases writeMemBytes st.mem dstAddr bs with
            | none => trivial
            | some mem' => exact ih hrest_safe he0793.2 hnodrop _ hdrops
    | moveUnaligned dst src size =>
      dsimp only [execStmts]
      cases evalPlaceAddr st src with
      | none => trivial
      | some srcAddr =>
        cases lookupNat st.localAddr dst with
        | none => trivial
        | some dstAddr =>
          dsimp only
          cases readMemBytes st.mem srcAddr size with
          | none => trivial
          | some bs =>
            dsimp only
            cases writeMemBytes st.mem dstAddr bs with
            | none => trivial
            | some mem' => exact ih hrest_safe he0793.2 hnodrop _ hdrops
    | mkRawPtr dst src =>
      dsimp only [execStmts]
      cases evalPlaceAddr st src with
      | none => trivial
      | some addr => exact ih hrest_safe he0793.2 hnodrop _ hdrops
    | mkRef dst src ty =>
      dsimp only [execStmts]
      have hnotunalign : placeUnaligned src ty.abiAlign ty.isSized = false := by
        have h := he0793.1
        dsimp only [checkPackedRefStmt] at h
        cases hu : placeUnaligned src ty.abiAlign ty.isSized with
        | false => rfl
        | true =>
          rw [hu] at h
          cases h
      cases haddr : evalPlaceAddr st src with
      | none => trivial
      | some addr =>
        dsimp only
        have hdiv : ty.abiAlign.Divides addr := hsound st src ty addr hnotunalign haddr
        have hchk : ty.abiAlign.check addr = true := (Align.check_eq_true_iff _ _).mpr hdiv
        rw [hchk]
        exact ih hrest_safe he0793.2 hnodrop _ hdrops
    | dropPlace target ty =>
      dsimp only [execStmts]
      dsimp only [NoUnalignedDrops] at hnodrop
      cases haddr : evalPlaceAddr st target with
      | none => trivial
      | some addr =>
        dsimp only
        have hdiv : ty.abiAlign.Divides addr := hsound st target ty addr hnodrop.1 haddr
        have hchk : ty.abiAlign.check addr = true := (Align.check_eq_true_iff _ _).mpr hdiv
        rw [hchk]
        exact ih hrest_safe he0793.2 hnodrop.2 _ (allDropsAligned_append hdrops hdiv)
    | derefLoad _ _ _ => exact False.elim hs
    | derefMutRef _ _ _ => exact False.elim hs
    | checkAlignAssert _ _ => exact False.elim hs
    | callDropInPlace _ _ => exact False.elim hs

/-- Theorem 2: Static absence of misaligned safe references and drops under `E0793` +
    `Copy` field staging + `AddMovesForPackedDrops`. -/
theorem e0793_and_copy_staging_no_misaligned_safe_refs
    (prog : Program) (freshBase : Nat) (init : ExecState)
    (hsound : PlaceUnalignmentSound)
    (hsafe : IsSafeBody prog.entry.stmts)
    (he0793 : checkPackedRefBody prog.entry = true)
    (hinitDrops : AllDropsAligned init) :
    NoAlignmentUb
      (execProgram { prog with entry := addMovesForPackedDropsBody freshBase prog.entry }
        .strictMiri init) := by
  unfold execProgram addMovesForPackedDropsBody
  exact safe_exec_no_alignment_ub
    { prog with entry := { prog.entry with stmts := stagePackedDropsList freshBase prog.entry.stmts } }
    .strictMiri
    hsound
    (stagePackedDropsList freshBase prog.entry.stmts)
    (stagePackedDropsList_preserves_safe freshBase prog.entry.stmts hsafe)
    (stagePackedDropsList_preserves_e0793 freshBase prog.entry.stmts he0793)
    (stagePackedDropsList_no_unaligned_drops freshBase prog.entry.stmts)
    init
    hinitDrops

/-! ## 10. Core Theorem 3: Whole-Program `-Z ub-checks` Completeness Iff Shims Instrumented -/

/-- A statement is in the sized raw-pointer dereference scope of `CheckAlignment`
    (`check_pointers.rs:209`, assuming `E0793` + `AddMovesForPackedDrops` already discharged
    safe borrows and safe drops, and no manual `checkAlignAssert` was pre-inserted). -/
def InCheckAlignmentScopeStmt : Stmt → Prop
  | .storageLive _ _ _ => True
  | .storageDead _ => True
  | .copyFromPlace _ _ _ => True
  | .moveUnaligned _ _ _ => True
  | .mkRawPtr _ _ => True
  | .derefLoad _ _ ty => ty.isSized = true
  | .derefMutRef _ _ ty => ty.isSized = true
  | .callDropInPlace _ _ => True
  | .mkRef _ _ _ => False
  | .dropPlace _ _ => False
  | .checkAlignAssert _ _ => False

def InCheckAlignmentScopeList (stmts : List Stmt) : Prop :=
  ∀ s, s ∈ stmts → InCheckAlignmentScopeStmt s

def ProgramInCheckAlignmentScope (prog : Program) : Prop :=
  prog.entry.kind = .userFn ∧
  InCheckAlignmentScopeList prog.entry.stmts ∧
  ∀ s, s ∈ prog.dropShims → InCheckAlignmentScopeList s.body.stmts

/-- Whole-program completeness of an alignment-check instrumentation policy:
    every alignment UB caught by strict Miri deterministically traps with `.ubTrap`
    under `-Z ub-checks` (zero silent misaligned escapes). -/
def UbChecksCompleteFor (policy : Program → Program) : Prop :=
  ∀ (prog : Program) (init : ExecState) (op : String) (addr : Nat) (reqAlign : Align),
    ProgramInCheckAlignmentScope prog →
    execProgram prog .strictMiri init = .ubMisaligned op addr reqAlign →
    execProgram (policy prog) .nativeUbChecks init = .ubTrap addr reqAlign

theorem findDropShim_map_checkAlignment (shims : List DropShimSpec) (ty : Ty) :
    (shims.map (fun s => { s with body := checkAlignmentBody s.body })).find?
      (fun s => decide (s.targetTy = ty)) =
    (shims.find? (fun s => decide (s.targetTy = ty))).map
      (fun s => { s with body := checkAlignmentBody s.body }) := by
  induction shims with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, List.find?]
    cases decide (s.targetTy = ty) with
    | true => rfl
    | false => exact ih

theorem findDropShim_instrumentWholeProgram (prog : Program) (ty : Ty) :
    (instrumentWholeProgram prog).findDropShim ty =
    (prog.findDropShim ty).map checkAlignmentBody := by
  unfold Program.findDropShim instrumentWholeProgram
  dsimp only
  rw [findDropShim_map_checkAlignment]
  cases prog.dropShims.find? (fun s => decide (s.targetTy = ty)) with
  | none => rfl
  | some s => rfl

theorem findDropShim_mem {prog : Program} {ty : Ty} {body : MirBody}
    (h : prog.findDropShim ty = some body) :
    ∃ s, s ∈ prog.dropShims ∧ s.body = body := by
  unfold Program.findDropShim at h
  cases hf : prog.dropShims.find? (fun s => decide (s.targetTy = ty)) with
  | none => rw [hf] at h; cases h
  | some s =>
    rw [hf] at h
    injection h with hb
    exact ⟨s, List.mem_of_find?_eq_some hf, hb⟩

/-- Exact simulation of `checkAlignmentStmts` over synthesized shims:
    - aligned `.ok st'` stays `.ok st'`;
    - misaligned `.ubMisaligned op addr req` becomes `.ubTrap addr req`. -/
theorem checkAlignmentStmts_shim_sim (stmts : List Stmt) (hscope : InCheckAlignmentScopeList stmts)
    (st : ExecState) :
    (∀ st', execShimStmts .strictMiri stmts st = .ok st' →
      execShimStmts .nativeUbChecks (checkAlignmentStmts stmts) st = .ok st') ∧
    (∀ op addr req, execShimStmts .strictMiri stmts st = .ubMisaligned op addr req →
      execShimStmts .nativeUbChecks (checkAlignmentStmts stmts) st = .ubTrap addr req) := by
  induction stmts generalizing st with
  | nil =>
    constructor
    · intro st' h; exact h
    · intro op addr req h; cases h
  | cons s rest ih =>
    have hs : InCheckAlignmentScopeStmt s := hscope s (List.Mem.head _)
    have hrest : InCheckAlignmentScopeList rest := fun x hx => hscope x (List.Mem.tail _ hx)
    cases s with
    | derefMutRef dst ptrLocal ty =>
      have hsz : ty.isSized = true := hs
      dsimp only [checkAlignmentStmts]
      rw [hsz, Bool.true_and]
      cases hlt : Align.ltBool Align.align1 ty.abiAlign with
      | true =>
        simp only [↓reduceIte]
        constructor
        · intro st' hok
          dsimp only [execShimStmts] at hok ⊢
          cases hptr : lookupNat st.ptrVal ptrLocal with
          | none => simp only [hptr] at hok; cases hok
          | some addr =>
            simp only [hptr] at hok
            cases hchk : ty.abiAlign.check addr with
            | false => simp only [hchk] at hok; cases hok
            | true =>
              simp only [hchk] at hok ⊢
              exact (ih hrest _).1 st' hok
        · intro op addr req hub
          dsimp only [execShimStmts] at hub ⊢
          cases hptr : lookupNat st.ptrVal ptrLocal with
          | none => simp only [hptr] at hub; cases hub
          | some a =>
            simp only [hptr] at hub
            cases hchk : ty.abiAlign.check a with
            | false =>
              simp only [hchk] at hub ⊢
              injection hub with _ ha hr
              rw [ha, hr]
            | true =>
              simp only [hchk] at hub ⊢
              exact (ih hrest _).2 op addr req hub
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have ha1 : ty.abiAlign = Align.align1 := Align.eq_align1_of_not_lt_align1 hlt
        constructor
        · intro st' hok
          dsimp only [execShimStmts] at hok ⊢
          cases hptr : lookupNat st.ptrVal ptrLocal with
          | none => simp only [hptr] at hok; cases hok
          | some addr =>
            simp only [hptr, ha1, Align.check_align1] at hok ⊢
            exact (ih hrest _).1 st' hok
        · intro op addr req hub
          dsimp only [execShimStmts] at hub ⊢
          cases hptr : lookupNat st.ptrVal ptrLocal with
          | none => simp only [hptr] at hub; cases hub
          | some a =>
            simp only [hptr, ha1, Align.check_align1] at hub ⊢
            exact (ih hrest _).2 op addr req hub
    | derefLoad dst ptrLocal ty =>
      have hsz : ty.isSized = true := hs
      dsimp only [checkAlignmentStmts]
      rw [hsz, Bool.true_and]
      cases hlt : Align.ltBool Align.align1 ty.abiAlign with
      | true =>
        simp only [↓reduceIte]
        constructor
        · intro st' hok
          dsimp only [execShimStmts] at hok ⊢
          cases hptr : lookupNat st.ptrVal ptrLocal with
          | none => simp only [hptr] at hok; cases hok
          | some addr =>
            simp only [hptr] at hok
            cases hchk : ty.abiAlign.check addr with
            | false => simp only [hchk] at hok; cases hok
            | true =>
              simp only [hchk] at hok ⊢
              exact (ih hrest _).1 st' hok
        · intro op addr req hub
          dsimp only [execShimStmts] at hub ⊢
          cases hptr : lookupNat st.ptrVal ptrLocal with
          | none => simp only [hptr] at hub; cases hub
          | some a =>
            simp only [hptr] at hub
            cases hchk : ty.abiAlign.check a with
            | false =>
              simp only [hchk] at hub ⊢
              injection hub with _ ha hr
              rw [ha, hr]
            | true =>
              simp only [hchk] at hub ⊢
              exact (ih hrest _).2 op addr req hub
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have ha1 : ty.abiAlign = Align.align1 := Align.eq_align1_of_not_lt_align1 hlt
        constructor
        · intro st' hok
          dsimp only [execShimStmts] at hok ⊢
          cases hptr : lookupNat st.ptrVal ptrLocal with
          | none => simp only [hptr] at hok; cases hok
          | some addr =>
            simp only [hptr, ha1, Align.check_align1] at hok ⊢
            exact (ih hrest _).1 st' hok
        · intro op addr req hub
          dsimp only [execShimStmts] at hub ⊢
          cases hptr : lookupNat st.ptrVal ptrLocal with
          | none => simp only [hptr] at hub; cases hub
          | some a =>
            simp only [hptr, ha1, Align.check_align1] at hub ⊢
            exact (ih hrest _).2 op addr req hub
    | storageLive _ _ _ | storageDead _ | copyFromPlace _ _ _ | moveUnaligned _ _ _
    | mkRawPtr _ _ | callDropInPlace _ _ =>
      constructor
      · intro st' h; dsimp only [execShimStmts] at h; cases h
      · intro op addr req h; dsimp only [execShimStmts] at h; cases h
    | mkRef _ _ _ | dropPlace _ _ | checkAlignAssert _ _ => exact False.elim hs

/-- Forward completeness direction: `instrumentWholeProgram` catches EVERY strict-Miri
    alignment UB with `.ubTrap` across both user bodies AND synthesized drop shims. -/
theorem instrumentWholeProgram_stmts_complete
    (prog : Program)
    (hshims : ∀ s, s ∈ prog.dropShims → InCheckAlignmentScopeList s.body.stmts)
    (stmts : List Stmt) (hscope : InCheckAlignmentScopeList stmts)
    (st : ExecState) (op : String) (addr : Nat) (req : Align)
    (hub : execStmts prog .strictMiri stmts st = .ubMisaligned op addr req) :
    execStmts (instrumentWholeProgram prog) .nativeUbChecks (checkAlignmentStmts stmts) st =
      .ubTrap addr req := by
  induction stmts generalizing st with
  | nil =>
    dsimp only [execStmts] at hub
    cases hub
  | cons s rest ih =>
    have hs : InCheckAlignmentScopeStmt s := hscope s (List.Mem.head _)
    have hrest : InCheckAlignmentScopeList rest := fun x hx => hscope x (List.Mem.tail _ hx)
    cases s with
    | storageLive locId size align =>
      dsimp only [checkAlignmentStmts]
      dsimp only [execStmts] at hub ⊢
      exact ih hrest _ hub
    | storageDead locId =>
      dsimp only [checkAlignmentStmts]
      dsimp only [execStmts] at hub ⊢
      cases hloc : lookupNat st.localAddr locId with
      | none => simp only [hloc] at hub; cases hub
      | some base =>
        simp only [hloc] at hub
        exact ih hrest _ hub
    | copyFromPlace dst src ty =>
      dsimp only [checkAlignmentStmts]
      dsimp only [execStmts] at hub ⊢
      cases h1 : evalPlaceAddr st src with
      | none => simp only [h1] at hub; cases hub
      | some sa =>
        cases h2 : lookupNat st.localAddr dst with
        | none => simp only [h1, h2] at hub; cases hub
        | some da =>
          simp only [h1, h2] at hub
          cases h3 : readMemBytes st.mem sa ty.size with
          | none => simp only [h3] at hub; cases hub
          | some bs =>
            simp only [h3] at hub ⊢
            cases h4 : writeMemBytes st.mem da bs with
            | none => simp only [h4] at hub; cases hub
            | some m' =>
              simp only [h4] at hub ⊢
              exact ih hrest _ hub
    | moveUnaligned dst src size =>
      dsimp only [checkAlignmentStmts]
      dsimp only [execStmts] at hub ⊢
      cases h1 : evalPlaceAddr st src with
      | none => simp only [h1] at hub; cases hub
      | some sa =>
        cases h2 : lookupNat st.localAddr dst with
        | none => simp only [h1, h2] at hub; cases hub
        | some da =>
          simp only [h1, h2] at hub
          cases h3 : readMemBytes st.mem sa size with
          | none => simp only [h3] at hub; cases hub
          | some bs =>
            simp only [h3] at hub ⊢
            cases h4 : writeMemBytes st.mem da bs with
            | none => simp only [h4] at hub; cases hub
            | some m' =>
              simp only [h4] at hub ⊢
              exact ih hrest _ hub
    | mkRawPtr dst src =>
      dsimp only [checkAlignmentStmts]
      dsimp only [execStmts] at hub ⊢
      cases h1 : evalPlaceAddr st src with
      | none => simp only [h1] at hub; cases hub
      | some a =>
        simp only [h1] at hub
        exact ih hrest _ hub
    | derefLoad dst ptrLocal ty =>
      have hsz : ty.isSized = true := hs
      dsimp only [checkAlignmentStmts]
      rw [hsz, Bool.true_and]
      cases hlt : Align.ltBool Align.align1 ty.abiAlign with
      | true =>
        simp only [↓reduceIte]
        dsimp only [execStmts] at hub ⊢
        cases hptr : lookupNat st.ptrVal ptrLocal with
        | none => simp only [hptr] at hub; cases hub
        | some a =>
          simp only [hptr] at hub
          cases hchk : ty.abiAlign.check a with
          | false =>
            simp only [hchk] at hub ⊢
            injection hub with _ ha hr
            rw [ha, hr]
          | true =>
            simp only [hchk] at hub ⊢
            cases hrm : readMemBytes st.mem a ty.size with
            | none => simp only [hrm] at hub; cases hub
            | some bs =>
              cases hdl : lookupNat st.localAddr dst with
              | none => simp only [hrm, hdl] at hub; cases hub
              | some da =>
                simp only [hrm, hdl] at hub ⊢
                cases hwm : writeMemBytes st.mem da bs with
                | none => simp only [hwm] at hub; cases hub
                | some m' =>
                  simp only [hwm] at hub ⊢
                  exact ih hrest _ hub
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have ha1 : ty.abiAlign = Align.align1 := Align.eq_align1_of_not_lt_align1 hlt
        dsimp only [execStmts] at hub ⊢
        cases hptr : lookupNat st.ptrVal ptrLocal with
        | none => simp only [hptr] at hub; cases hub
        | some a =>
          simp only [hptr, ha1, Align.check_align1] at hub ⊢
          cases hrm : readMemBytes st.mem a ty.size with
          | none => simp only [hrm] at hub; cases hub
          | some bs =>
            cases hdl : lookupNat st.localAddr dst with
            | none => simp only [hrm, hdl] at hub; cases hub
            | some da =>
              simp only [hrm, hdl] at hub ⊢
              cases hwm : writeMemBytes st.mem da bs with
              | none => simp only [hwm] at hub; cases hub
              | some m' =>
                simp only [hwm] at hub ⊢
                exact ih hrest _ hub
    | derefMutRef dst ptrLocal ty =>
      have hsz : ty.isSized = true := hs
      dsimp only [checkAlignmentStmts]
      rw [hsz, Bool.true_and]
      cases hlt : Align.ltBool Align.align1 ty.abiAlign with
      | true =>
        simp only [↓reduceIte]
        dsimp only [execStmts] at hub ⊢
        cases hptr : lookupNat st.ptrVal ptrLocal with
        | none => simp only [hptr] at hub; cases hub
        | some a =>
          simp only [hptr] at hub
          cases hchk : ty.abiAlign.check a with
          | false =>
            simp only [hchk] at hub ⊢
            injection hub with _ ha hr
            rw [ha, hr]
          | true =>
            simp only [hchk] at hub ⊢
            exact ih hrest _ hub
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have ha1 : ty.abiAlign = Align.align1 := Align.eq_align1_of_not_lt_align1 hlt
        dsimp only [execStmts] at hub ⊢
        cases hptr : lookupNat st.ptrVal ptrLocal with
        | none => simp only [hptr] at hub; cases hub
        | some a =>
          simp only [hptr, ha1, Align.check_align1] at hub ⊢
          exact ih hrest _ hub
    | callDropInPlace ptrLocal ty =>
      dsimp only [checkAlignmentStmts]
      dsimp only [execStmts] at hub ⊢
      rw [findDropShim_instrumentWholeProgram]
      cases hptr : lookupNat st.ptrVal ptrLocal with
      | none => simp only [hptr] at hub; cases hub
      | some a =>
        cases hsh : prog.findDropShim ty with
        | none => simp only [hptr, hsh] at hub; cases hub
        | some shimBody =>
          simp only [hptr, hsh] at hub
          dsimp only [Option.map, checkAlignmentBody]
          rcases findDropShim_mem hsh with ⟨spec, hspec_mem, hspec_body⟩
          have hshim_scope : InCheckAlignmentScopeList shimBody.stmts := by
            rw [← hspec_body]
            exact hshims spec hspec_mem
          have hsim := checkAlignmentStmts_shim_sim shimBody.stmts hshim_scope
            { st with ptrVal := setNat st.ptrVal 0 a }
          cases hres : execShimStmts .strictMiri shimBody.stmts { st with ptrVal := setNat st.ptrVal 0 a } with
          | ok st' =>
            simp only [hres] at hub
            rw [hsim.1 st' hres]
            exact ih hrest _ hub
          | ubMisaligned sop sa sr =>
            simp only [hres] at hub
            injection hub with _ ha hr
            rw [hsim.2 sop sa sr hres, ha, hr]
          | ubTrap _ _ => simp only [hres] at hub; cases hub
          | silentMisalignedExec _ _ _ _ => simp only [hres] at hub; cases hub
          | runtimeError _ => simp only [hres] at hub; cases hub
    | mkRef _ _ _ | dropPlace _ _ | checkAlignAssert _ _ => exact False.elim hs

theorem instrumentWholeProgram_complete : UbChecksCompleteFor instrumentWholeProgram := by
  intro prog init op addr req ⟨_, hentry, hshims⟩ hub
  unfold execProgram instrumentWholeProgram checkAlignmentBody
  exact instrumentWholeProgram_stmts_complete prog hshims prog.entry.stmts hentry init op addr req hub

/-! ## 11. Concrete Layouts, Sharpness Counterexamples, and the Main Iff Theorem -/

def tyU8 : Ty := { name := "u8", size := 1, abiAlign := Align.align1, isCopy := true, needsDrop := false }
def tyU32 : Ty := { name := "u32", size := 4, abiAlign := Align.align4, isCopy := true, needsDrop := false }
def tyU64 : Ty := { name := "u64", size := 8, abiAlign := Align.align8, isCopy := true, needsDrop := false }
def tyAligned64 : Ty := { name := "Aligned64", size := 64, abiAlign := Align.align64, isCopy := false, needsDrop := true }
def tyUnsizedAligned64 : Ty := { name := "T:PointeeSized(Aligned64)", size := 64, abiAlign := Align.align64, isCopy := false, needsDrop := true, isSized := false }

def packed1Layout : StructLayout :=
  computeStructLayout (some Align.align1) [⟨"tag", tyU8⟩, ⟨"x", tyU32⟩, ⟨"y", tyU64⟩]

def packed2Layout : StructLayout :=
  computeStructLayout (some Align.align2) [⟨"tag", tyU8⟩, ⟨"x", tyU32⟩, ⟨"y", tyU64⟩]

def packed4Layout : StructLayout :=
  computeStructLayout (some Align.align4) [⟨"tag", tyU8⟩, ⟨"x", tyU32⟩, ⟨"y", tyU64⟩]

def packedHolderLayout : StructLayout :=
  computeStructLayout (some Align.align1) [⟨"pad", tyU8⟩, ⟨"aligned", tyAligned64⟩]

/-- Verified layout calculations matching `rustc` empirical probe Experiment 1. -/
theorem verified_packed_layouts :
    packed1Layout.size = 13 ∧ packed1Layout.outerAlign = Align.align1 ∧
    packed2Layout.size = 14 ∧ packed2Layout.outerAlign = Align.align2 ∧
    packed4Layout.size = 16 ∧ packed4Layout.outerAlign = Align.align4 ∧
    packedHolderLayout.size = 65 ∧ packedHolderLayout.outerAlign = Align.align1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The misaligned packed field place `packed.aligned` at offset `1` inside `#[repr(C, packed)]`. -/
def packedAlignedFieldPlace : Place :=
  { localId := 0
    baseAlign := Align.align64
    projs := [.field 1 1 (some Align.align1) tyAligned64] }

def samplePayload64 : List Nat := List.replicate 64 42

/-- Initial memory holding `PackedHolder { pad: 7, aligned: [42; 64] }` at address `64`,
    so `packed.aligned` starts at address `65` (`65 % 64 = 1 ≠ 0`). -/
def ceInitialState : ExecState :=
  {
    mem := {
      allocs := [{
        baseAddr := 64
        allocAlign := Align.align64
        size := 65
        bytes := 7 :: samplePayload64
        live := true
      }]
      nextAddr := 129
    }
    localAddr := [(0, 64)]
    ptrVal := []
    drops := []
  }

/-- Counterexample 1 program: drops `packed.aligned` directly without staging. -/
def ce1DirectDropProg : Program :=
  {
    entry := {
      name := "drop_packed_direct"
      kind := .userFn
      stmts := [.dropPlace packedAlignedFieldPlace tyAligned64]
    }
    dropShims := [makeDropShimFor tyAligned64]
  }

/-- Counterexample 1 (Sharpness):
    (a) Without `AddMovesForPackedDrops`, direct drop passes misaligned address `65` (`65 % 64 = 1`)
        to `Drop::drop` and immediately faults `.ubMisaligned` in strict semantics;
    (b) With `AddMovesForPackedDrops`, the field is staged to aligned stack address `192` (`64 * 3`),
        succeeding cleanly with the exact 64-byte payload preserved. -/
theorem ce1_direct_packed_drop_passes_misaligned_self_ub :
    execProgram ce1DirectDropProg .strictMiri ceInitialState =
      .ubMisaligned "drop_place" 65 Align.align64 ∧
    (∃ st',
      execProgram
        { ce1DirectDropProg with entry := addMovesForPackedDropsBody 10 ce1DirectDropProg.entry }
        .strictMiri ceInitialState = .ok st' ∧
      st'.drops = [{ tyName := "Aligned64", selfAddr := 192, reqAlign := Align.align64, payload := samplePayload64 }] ∧
      Align.align64.Divides 192) := by
  refine ⟨rfl, ?_⟩
  refine ⟨_, rfl, rfl, ⟨3, rfl⟩⟩

/-- Counterexample 2a: direct user-MIR `&mut *(&raw mut packed.aligned)`. -/
def ce2UserDirectDerefProg : Program :=
  {
    entry := {
      name := "user_direct_mut_ref"
      kind := .userFn
      stmts := [
        .mkRawPtr 1 packedAlignedFieldPlace,
        .derefMutRef 2 1 tyAligned64
      ]
    }
    dropShims := [makeDropShimFor tyAligned64]
  }

/-- Counterexample 2b: `core::ptr::drop_in_place(&raw mut packed.aligned)` invoking `DropGlue` shim. -/
def ce2DropInPlaceProg : Program :=
  {
    entry := {
      name := "call_drop_in_place_on_packed_field"
      kind := .userFn
      stmts := [
        .mkRawPtr 1 packedAlignedFieldPlace,
        .callDropInPlace 1 tyAligned64
      ]
    }
    dropShims := [makeDropShimFor tyAligned64]
  }

theorem ce2DropInPlaceProg_in_scope : ProgramInCheckAlignmentScope ce2DropInPlaceProg := by
  refine ⟨rfl, ?_, ?_⟩
  · intro s hm
    cases hm with
    | head => trivial
    | tail _ hm =>
      cases hm with
      | head => trivial
      | tail _ hm => cases hm
  · intro sp hsp
    cases hsp with
    | head =>
      intro s hm
      cases hm with
      | head => rfl
      | tail _ hm => cases hm
    | tail _ hsp => cases hsp

/-- Counterexample 2 (Sharpness — the `make_shim` alignment-check blind spot):
    1. User-MIR `&mut *(&raw mut packed.aligned)` under `instrumentUserOnly` traps `.ubTrap 65 align64`;
    2. `drop_in_place(&raw mut packed.aligned)` under strict Miri faults `.ubMisaligned ... 65 align64`;
    3. `drop_in_place(&raw mut packed.aligned)` under `instrumentUserOnly` (real `rustc`: `make_shim`
       omits `CheckAlignment`) escapes `-Z ub-checks`, recording `.silentMisalignedExec` with `selfAddr = 65`;
    4. `drop_in_place(&raw mut packed.aligned)` under `instrumentWholeProgram` deterministically traps `.ubTrap 65 align64`. -/
theorem ce2_uninstrumented_drop_shim_escapes_ub_checks :
    execProgram (instrumentUserOnly ce2UserDirectDerefProg) .nativeUbChecks ceInitialState =
      .ubTrap 65 Align.align64 ∧
    execProgram ce2DropInPlaceProg .strictMiri ceInitialState =
      .ubMisaligned "shim_deref_mut_ref" 65 Align.align64 ∧
    (∃ st',
      execProgram (instrumentUserOnly ce2DropInPlaceProg) .nativeUbChecks ceInitialState =
        .silentMisalignedExec "shim_deref_mut_ref" 65 Align.align64 st' ∧
      st'.drops = [{ tyName := "Aligned64", selfAddr := 65, reqAlign := Align.align64, payload := samplePayload64 }]) ∧
    execProgram (instrumentWholeProgram ce2DropInPlaceProg) .nativeUbChecks ceInitialState =
      .ubTrap 65 Align.align64 := by
  refine ⟨rfl, rfl, ⟨_, rfl, rfl⟩, rfl⟩

/-- Negative direction of Core Theorem 3: `instrumentUserOnly` is NOT complete for `-Z ub-checks`. -/
theorem instrumentUserOnly_incomplete : ¬ UbChecksCompleteFor instrumentUserOnly := by
  intro hcomp
  have htrap :=
    hcomp ce2DropInPlaceProg ceInitialState "shim_deref_mut_ref" 65 Align.align64
      ce2DropInPlaceProg_in_scope ce2_uninstrumented_drop_shim_escapes_ub_checks.2.1
  rcases ce2_uninstrumented_drop_shim_escapes_ub_checks.2.2.1 with ⟨st', hsilent, _⟩
  rw [hsilent] at htrap
  cases htrap

/-- Core Theorem 3 (Biconditional): Whole-program `-Z ub-checks` alignment-check completeness
    holds **if and only if** synthesized shims are instrumented (`instrumentShims = true`). -/
theorem whole_program_ub_checks_complete_iff_shims_instrumented (instrumentShims : Bool) :
    UbChecksCompleteFor (policyOf instrumentShims) ↔ instrumentShims = true := by
  cases instrumentShims with
  | true =>
    constructor
    · intro _; rfl
    · intro _; exact instrumentWholeProgram_complete
  | false =>
    constructor
    · intro h; exact False.elim (instrumentUserOnly_incomplete h)
    · intro h; cases h

/-- Counterexample 3 (Bonus Sharpness — `?Sized` generic dereference blind spot, `check_pointers.rs:209`):
    Models polymorphic `core::ptr::drop_in_place<T: PointeeSized>(to_drop: *mut T)` and
    `generic_unsized_ref<T: ?Sized>(ptr: *mut T)`: even inside a `.userFn` body under
    `instrumentWholeProgram`, `ty.isSized = false` suppresses `CheckAlignment` insertion,
    so strict Miri faults `.ubMisaligned` while `-Z ub-checks` silently executes misaligned UB. -/
def ce3UnsizedGenericDerefProg : Program :=
  {
    entry := {
      name := "generic_unsized_ref_body"
      kind := .userFn
      stmts := [
        .mkRawPtr 1 packedAlignedFieldPlace,
        .derefMutRef 2 1 tyUnsizedAligned64
      ]
    }
    dropShims := []
  }

theorem ce3_unsized_generic_deref_escapes_user_ub_checks :
    execProgram ce3UnsizedGenericDerefProg .strictMiri ceInitialState =
      .ubMisaligned "deref_mut_ref" 65 Align.align64 ∧
    (∃ st',
      execProgram (instrumentWholeProgram ce3UnsizedGenericDerefProg) .nativeUbChecks ceInitialState =
        .silentMisalignedExec "deref_mut_ref" 65 Align.align64 st') := by
  exact ⟨rfl, _, rfl⟩

end PackedProjectionsAndAlignedDropStaging
