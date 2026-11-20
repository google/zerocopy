import Toy.ByteSL.PointsTo

/-!
# Result group 2: splitting and joining a `repr(C)`-style struct, padding included

A two-field struct layout `Layout2` places field 1 (`size₁` bytes) at offset `0` and field 2
(`size₂` bytes) at offset `off₂`, inside a struct of `size` bytes; both fields lie within the
struct (`size₁ ≤ size`, `off₂ + size₂ ≤ size`, fields of the structure, needed for the struct
representation to be well typed). The fields do **not** overlap when `L.NonOverlap`
(`size₁ ≤ off₂`); this is a separate, named hypothesis of the split/join laws (it fails for
union-like layouts, `ptsDec_struct_split_tight_hL`). No alignment is modeled and offsets are
given, not computed by a layout algorithm. Bytes in neither field — `[size₁, off₂)` (interior
padding) and `[off₂ + size₂, size)` (trailing padding) — are padding.

The struct representation `structRep L r₁ r₂` encodes each field at its offset and writes
`uninit` padding; it decodes each field from its own byte range and never reads padding (the
struct representation of MiniRust). It is the two-field, first-field-at-offset-0 instance of the
explicit-offset product of the published package
`byte-representation-galois-laws-and-transmute-composition` (`prodRep`), restated here with pairs
instead of dependent tuples (no equivalence with `prodRep` is claimed).

Two padding assertions own exactly the padding cells of the struct at base address `a`:

* `padAny p L a` — the padding cells hold *any* bytes;
* `padUninit p L a` — the padding cells hold `uninit`.

Results:

* `ptsDec_struct_iff_sep_fields_padAny_of_nonOverlap` (R2a): for a non-overlapping layout, the
  decode-based struct points-to is equivalent to decode-based field points-to for both fields,
  separated from `padAny`, all at one permission. No representation law is needed.
* `ptsEnc_struct_iff_sep_fields_padUninit_of_nonOverlap` (R2b): for a non-overlapping layout, the
  encode-based struct points-to is equivalent to encode-based field points-to for both fields,
  separated from `padUninit`. No law is needed.
* `ptsEnc_struct_join_padAny_fails`, `ptsDec_struct_split_padUninit_fails` (R2c,
  counterexamples): the mixed pairings fail — encode-based field points-to with `padAny` does not
  entail the encode-based struct points-to, and the decode-based struct points-to does not entail
  decode-based field points-to with `padUninit`.
-/

namespace Toy.ByteSL

open SepStruct

/-! ## Layouts, the struct representation, padding assertions -/

/-- A `repr(C)`-style two-field layout: field 1 of `size₁` bytes at offset `0`, field 2 of
`size₂` bytes at offset `off₂`, total size `size`. Both fields lie within the struct (`fits₁`,
`fits`); these in-bounds facts are what make `structRep` well typed. Non-overlap of the two
fields is *not* bundled: it is the separate hypothesis `Layout2.NonOverlap`. Offsets are given,
not computed (no alignment is modeled). -/
structure Layout2 where
  /-- Size of field 1 (placed at offset 0). -/
  size₁ : Nat
  /-- Size of field 2. -/
  size₂ : Nat
  /-- Offset of field 2. -/
  off₂ : Nat
  /-- Total size of the struct. -/
  size : Nat
  /-- Field 1 ends within the struct. -/
  fits₁ : size₁ ≤ size
  /-- Field 2 ends within the struct. -/
  fits : off₂ + size₂ ≤ size

namespace Layout2

/-- The two fields do not overlap: field 2 starts at or after the end of field 1. Every layout of
a real `repr(C)` struct satisfies this; union-like layouts do not. -/
def NonOverlap (L : Layout2) : Prop := L.size₁ ≤ L.off₂

instance (L : Layout2) : Decidable L.NonOverlap := Nat.decLe _ _

/-- Byte `i` of the struct is a padding byte: it lies within the struct and in neither field's
range. -/
def isPad (L : Layout2) (i : Nat) : Bool :=
  decide (i < L.size ∧ L.size₁ ≤ i ∧ ¬ (L.off₂ ≤ i ∧ i < L.off₂ + L.size₂))

/-- Field 1, read as the slice starting at offset `0`, lies within the struct. -/
theorem fits₁_zero (L : Layout2) : 0 + L.size₁ ≤ L.size := by
  have := L.fits₁; omega

end Layout2

/-- The `m` bytes of `x` starting at offset `o` (copied from the published package's
`Bytes.slice`). -/
def Bytes.slice {D : Type} {n : Nat} (x : Bytes D n) (o m : Nat) (h : o + m ≤ n) : Bytes D m :=
  Vector.ofFn fun t => x[o + t.val]

section StructRep

variable {D V₁ V₂ : Type}

/-- Encoder of the struct: field bytes at their offsets, `uninit` padding. -/
def structEncode (L : Layout2) (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂)
    (v : V₁ × V₂) : Bytes D L.size :=
  Vector.ofFn fun i =>
    if h₁ : i.val < L.size₁ then (r₁.encode v.1)[i.val]
    else if h₂ : L.off₂ ≤ i.val ∧ i.val < L.off₂ + L.size₂ then
      (r₂.encode v.2)[i.val - L.off₂]'(by omega)
    else .uninit

/-- Decoder of the struct: decode each field from its own byte range; succeed iff both succeed.
Padding bytes are never read. -/
def structDecode (L : Layout2) (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂)
    (x : Bytes D L.size) : Option (V₁ × V₂) :=
  match r₁.decode (x.slice 0 L.size₁ L.fits₁_zero), r₂.decode (x.slice L.off₂ L.size₂ L.fits) with
  | some v₁, some v₂ => some (v₁, v₂)
  | _, _ => none

/-- The `repr(C)`-style struct representation built from two field representations. -/
def structRep (L : Layout2) (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂) :
    Rep (Bytes D L.size) (V₁ × V₂) :=
  ⟨structEncode L r₁ r₂, structDecode L r₁ r₂⟩

end StructRep

/-- Ownership of the padding cells of a struct with layout `L` at base `a`, holding **any**
bytes (permission `p`): the heap is exactly the cells `a + i` with `L.isPad i` (so `i < L.size`). -/
def padAny {D : Type} (p : Perm) (L : Layout2) (a : Nat) : Assn (BHeap D) :=
  fun h => ∃ y : Bytes D L.size, h = Heap.blockOn p a y L.isPad

/-- Ownership of the padding cells of a struct with layout `L` at base `a`, all holding
**`uninit`** (permission `p`). -/
def padUninit {D : Type} (p : Perm) (L : Layout2) (a : Nat) : Assn (BHeap D) :=
  fun h => h = Heap.blockOn p a (Bytes.uninit L.size) L.isPad

/-! ## Gluing field bytes and padding bytes into one struct byte vector (proof helpers) -/

/-- Helper: two byte heaps are disjoint if at every address at least one is unallocated. -/
theorem disj_of_forall_none {D : Type} {h₁ h₂ : BHeap D}
    (H : ∀ k, h₁.val k = none ∨ h₂.val k = none) : disj h₁ h₂ := by
  intro k c₁ c₂ e1 e2
  rcases H k with e | e
  · rw [e] at e1; cases e1
  · rw [e] at e2; cases e2

/-- The struct byte vector whose first field bytes are `x₁`, whose second field bytes are `x₂`, and
whose remaining (padding) bytes are taken from `y`. -/
def glueBytes {D : Type} (L : Layout2) (x₁ : Bytes D L.size₁) (x₂ : Bytes D L.size₂)
    (y : Bytes D L.size) : Bytes D L.size :=
  Vector.ofFn fun i =>
    if h₁ : i.val < L.size₁ then x₁[i.val]
    else if h₂ : L.off₂ ≤ i.val ∧ i.val < L.off₂ + L.size₂ then
      x₂[i.val - L.off₂]'(by omega)
    else y[i.val]

/-- For non-overlapping fields, the block holding a glued struct byte vector is the disjoint union
of the two field blocks and the padding cells. -/
theorem block_glueBytes_eq_union_of_nonOverlap {D : Type} (L : Layout2) (hL : L.NonOverlap)
    (p : Perm) (a : Nat) (x₁ : Bytes D L.size₁) (x₂ : Bytes D L.size₂) (y : Bytes D L.size) :
    let x := glueBytes L x₁ x₂ y
    let h₁ := Heap.block p a x₁
    let h₂ := Heap.block p (a + L.off₂) x₂
    let h₃ := Heap.blockOn p a y L.isPad
    disj h₂ h₃ ∧ disj h₁ (union h₂ h₃) ∧ Heap.block p a x = union h₁ (union h₂ h₃) := by
  have : L.size₁ ≤ L.off₂ := hL
  have := L.fits
  refine ⟨?_, ?_, ?_⟩
  · apply disj_of_forall_none
    intro k
    by_cases hk : a + L.off₂ ≤ k ∧ k < a + L.off₂ + L.size₂
    · right
      rw [Heap.blockOn_val]
      split
      · simp [Layout2.isPad]; omega
      · rfl
    · left
      unfold Heap.block
      rw [Heap.blockOn_val]
      simp [hk]
  · apply disj_of_forall_none
    intro k
    by_cases hk : a ≤ k ∧ k < a + L.size₁
    · right
      simp only [BHeap.union_eq, Heap.join_val]
      have e2 : (Heap.block p (a + L.off₂) x₂).val k = none :=
        Heap.block_val_of_lt p (a + L.off₂) x₂ (by omega)
      have e3 : (Heap.blockOn p a y L.isPad).val k = none := by
        rw [Heap.blockOn_val]
        split
        · simp [Layout2.isPad]; omega
        · rfl
      simp [e2, e3]
    · left
      unfold Heap.block
      rw [Heap.blockOn_val]
      simp [hk]
  · apply Heap.ext
    intro k
    simp only [BHeap.union_eq, Heap.join_val]
    by_cases hk : a ≤ k ∧ k < a + L.size
    · obtain ⟨i, rfl⟩ : ∃ i, k = a + i := ⟨k - a, by omega⟩
      have hi : i < L.size := by omega
      rw [Heap.block_val_add p a _ hi]
      by_cases h1 : i < L.size₁
      · rw [Heap.block_val_add p a x₁ h1]
        simp [glueBytes, h1]
      · have e1 : (Heap.block p a x₁).val (a + i) = none :=
          Heap.block_val_of_ge p a x₁ (by omega)
        rw [e1, Option.none_or]
        by_cases h2 : L.off₂ ≤ i ∧ i < L.off₂ + L.size₂
        · have heq : a + i = (a + L.off₂) + (i - L.off₂) := by omega
          rw [heq, Heap.block_val_add p (a + L.off₂) x₂ (by omega)]
          simp [glueBytes, h1, h2]
        · have e2 : (Heap.block p (a + L.off₂) x₂).val (a + i) = none := by
            unfold Heap.block
            rw [Heap.blockOn_val]
            simp only [show ¬ (a + L.off₂ ≤ a + i ∧ a + i < a + L.off₂ + L.size₂) by omega,
              dite_false]
          rw [e2, Option.none_or, Heap.blockOn_val_add p a y L.isPad hi]
          have hpad : L.isPad i = true := by
            simp [Layout2.isPad]
            omega
          simp [hpad, glueBytes, h1, h2]
    · have e0 : (Heap.block p a (glueBytes L x₁ x₂ y)).val k = none := by
        unfold Heap.block
        rw [Heap.blockOn_val]
        simp [hk]
      have e1 : (Heap.block p a x₁).val k = none := by
        unfold Heap.block
        rw [Heap.blockOn_val]
        have hnot1 : ¬ (a ≤ k ∧ k < a + L.size₁) := by omega
        simp [hnot1]
      have e2 : (Heap.block p (a + L.off₂) x₂).val k = none := by
        unfold Heap.block
        rw [Heap.blockOn_val]
        have hnot2 : ¬ (a + L.off₂ ≤ k ∧ k < a + L.off₂ + L.size₂) := by omega
        simp [hnot2]
      have e3 : (Heap.blockOn p a y L.isPad).val k = none := by
        rw [Heap.blockOn_val]
        simp [hk]
      simp [e0, e1, e2, e3]

theorem glueBytes_slices_self {D : Type} (L : Layout2) (x : Bytes D L.size) :
    glueBytes L (x.slice 0 L.size₁ L.fits₁_zero) (x.slice L.off₂ L.size₂ L.fits) x = x := by
  apply Vector.ext
  intro i hi
  simp only [glueBytes, Bytes.slice, Vector.getElem_ofFn]
  split
  · simp
  · split
    · rename_i h1 h2
      have hidx : L.off₂ + (i - L.off₂) = i := by omega
      simp [hidx]
    · rfl

theorem slice_fst_glueBytes {D : Type} (L : Layout2) (x₁ : Bytes D L.size₁)
    (x₂ : Bytes D L.size₂) (y : Bytes D L.size) :
    (glueBytes L x₁ x₂ y).slice 0 L.size₁ L.fits₁_zero = x₁ := by
  apply Vector.ext
  intro i hi
  simp [Bytes.slice, glueBytes]

theorem slice_snd_glueBytes_of_nonOverlap {D : Type} (L : Layout2) (hL : L.NonOverlap)
    (x₁ : Bytes D L.size₁) (x₂ : Bytes D L.size₂) (y : Bytes D L.size) :
    (glueBytes L x₁ x₂ y).slice L.off₂ L.size₂ L.fits = x₂ := by
  have : L.size₁ ≤ L.off₂ := hL
  apply Vector.ext
  intro i hi
  have hnot1 : ¬ (L.off₂ + i < L.size₁) := by omega
  simp [Bytes.slice, glueBytes, hnot1]

/-! ## R2a, R2b: the split/join laws -/

/-- **R2a (decode-based split/join).** For every two-field layout `L` whose fields do not overlap
(`L.NonOverlap`), field representations `r₁`, `r₂` (no laws assumed), permission `p`, base address
`a`, values `v₁`, `v₂` and heap `h`: `h` satisfies the decode-based points-to of `(v₁, v₂)` at
`structRep L r₁ r₂` with permission `p` iff `h` splits into the decode-based points-to of `v₁` at
`a`, the decode-based points-to of `v₂` at `a + off₂`, and the padding cells holding any bytes,
all three with the same permission `p`. -/
theorem ptsDec_struct_iff_sep_fields_padAny_of_nonOverlap {D V₁ V₂ : Type} (L : Layout2)
    (hL : L.NonOverlap) (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂)
    (p : Perm) (a : Nat) (v₁ : V₁) (v₂ : V₂) (h : BHeap D) :
    ptsDec p (structRep L r₁ r₂) a (v₁, v₂) h ↔
      sep (ptsDec p r₁ a v₁) (sep (ptsDec p r₂ (a + L.off₂) v₂) (padAny p L a)) h := by
  constructor
  · rintro ⟨x, rfl, hd⟩
    change structDecode L r₁ r₂ x = some (v₁, v₂) at hd
    dsimp only [structDecode] at hd
    cases h1 : r₁.decode (x.slice 0 L.size₁ L.fits₁_zero) <;> rw [h1] at hd
    · cases hd
    · cases h2 : r₂.decode (x.slice L.off₂ L.size₂ L.fits) <;> rw [h2] at hd
      · cases hd
      · injection hd with hd
        cases hd
        obtain ⟨d23, d1, heq⟩ := block_glueBytes_eq_union_of_nonOverlap L hL p a
          (x.slice 0 L.size₁ L.fits₁_zero) (x.slice L.off₂ L.size₂ L.fits) x
        rw [glueBytes_slices_self L x] at heq
        exact ⟨_, _, d1, heq, ⟨_, rfl, h1⟩, ⟨_, _, d23, rfl, ⟨_, rfl, h2⟩, ⟨x, rfl⟩⟩⟩
  · rintro ⟨_, _, _, rfl, ⟨x₁, rfl, hd1⟩, ⟨_, _, _, rfl, ⟨x₂, rfl, hd2⟩, ⟨y, rfl⟩⟩⟩
    obtain ⟨_, _, heq⟩ := block_glueBytes_eq_union_of_nonOverlap L hL p a x₁ x₂ y
    refine ⟨glueBytes L x₁ x₂ y, heq.symm, ?_⟩
    change structDecode L r₁ r₂ (glueBytes L x₁ x₂ y) = some (v₁, v₂)
    dsimp only [structDecode]
    rw [slice_fst_glueBytes, slice_snd_glueBytes_of_nonOverlap L hL, hd1, hd2]

/-- **R2b (encode-based split/join).** For every two-field layout `L` whose fields do not overlap
(`L.NonOverlap`), field representations `r₁`, `r₂` (no laws assumed), permission `p`, base address
`a`, values `v₁`, `v₂` and heap `h`: `h` satisfies the encode-based points-to of `(v₁, v₂)` at
`structRep L r₁ r₂` with permission `p` iff `h` splits into the encode-based points-to of `v₁` at
`a`, the encode-based points-to of `v₂` at `a + off₂`, and the padding cells all holding `uninit`,
all three with the same permission `p`. -/
theorem ptsEnc_struct_iff_sep_fields_padUninit_of_nonOverlap {D V₁ V₂ : Type} (L : Layout2)
    (hL : L.NonOverlap) (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂)
    (p : Perm) (a : Nat) (v₁ : V₁) (v₂ : V₂) (h : BHeap D) :
    ptsEnc p (structRep L r₁ r₂) a (v₁, v₂) h ↔
      sep (ptsEnc p r₁ a v₁) (sep (ptsEnc p r₂ (a + L.off₂) v₂) (padUninit p L a)) h := by
  have hse : (structRep L r₁ r₂).encode (v₁, v₂) =
      glueBytes L (r₁.encode v₁) (r₂.encode v₂) (Bytes.uninit L.size) := by
    apply Vector.ext
    intro i hi
    simp [structRep, structEncode, glueBytes, Bytes.uninit]
  constructor
  · intro hh
    rw [ptsEnc, ptsB, hse] at hh
    subst hh
    obtain ⟨d23, d1, heq⟩ := block_glueBytes_eq_union_of_nonOverlap L hL p a (r₁.encode v₁)
      (r₂.encode v₂) (Bytes.uninit L.size)
    exact ⟨_, _, d1, heq, rfl, ⟨_, _, d23, rfl, rfl, rfl⟩⟩
  · rintro ⟨_, _, _, rfl, rfl, ⟨_, _, _, rfl, rfl, hp⟩⟩
    rw [padUninit] at hp
    subst hp
    obtain ⟨_, _, heq⟩ := block_glueBytes_eq_union_of_nonOverlap L hL p a (r₁.encode v₁)
      (r₂.encode v₂) (Bytes.uninit L.size)
    rw [ptsEnc, ptsB, hse, heq]

/-! ## A concrete struct: `#[repr(C)] struct S { a: u8, b: u16 }` -/

/-- The layout of `#[repr(C)] struct S { a: u8, b: u16 }` with a 2-byte-aligned `u16`: `a` at
offset 0, one padding byte at offset 1, `b` at offsets 2–3; size 4. -/
abbrev layoutS : Layout2 := ⟨1, 2, 2, 4, by decide, by decide⟩

theorem layoutS_nonOverlap : layoutS.NonOverlap := by decide

/-- The struct `S`: `u8Rep` for `a` and the two-byte integer `pairRep` for `b`. -/
abbrev structS : Rep (Bytes Byte 4) (Byte × (Byte × Byte)) :=
  structRep layoutS u8Rep pairRep

/-- A block holding `S { a: 1, b: (2, 3) }` whose padding byte is initialized to `9`. -/
abbrev heapS9 : BHeap Byte :=
  Heap.block .full 0 (#v[.init 1, .init 9, .init 2, .init 3] : Bytes Byte 4)

/-- `heapS9` splits into the field cells and the padding cell. -/
theorem heapS9_split :
    heapS9 = Heap.join (Heap.block .full 0 (#v[.init 1] : Bytes Byte 1))
      (Heap.join (Heap.block .full (0 + 2) (#v[.init 2, .init 3] : Bytes Byte 2))
        (Heap.blockOn .full 0 (#v[.init 1, .init 9, .init 2, .init 3] : Bytes Byte 4)
          layoutS.isPad)) := by
  apply Heap.ext
  intro k
  rcases k with _ | _ | _ | _ | k
  · decide
  · decide
  · decide
  · decide
  · simp only [Heap.join_val]
    rw [Heap.block_val_of_ge _ _ _ (by omega), Heap.block_val_of_ge _ _ _ (by omega),
      Heap.block_val_of_ge _ _ _ (by omega), Heap.blockOn_val_of_ge _ _ _ _ (by omega)]
    rfl

theorem heapS9_parts_disj :
    disj (Heap.block .full 0 (#v[.init 1] : Bytes Byte 1))
      (Heap.join (Heap.block .full (0 + 2) (#v[.init 2, .init 3] : Bytes Byte 2))
        (Heap.blockOn .full 0 (#v[.init 1, .init 9, .init 2, .init 3] : Bytes Byte 4)
          layoutS.isPad)) ∧
    disj (Heap.block .full (0 + 2) (#v[.init 2, .init 3] : Bytes Byte 2))
        (Heap.blockOn .full 0 (#v[.init 1, .init 9, .init 2, .init 3] : Bytes Byte 4)
          layoutS.isPad) := by
  constructor
  · apply disj_of_forall_none
    intro k
    rcases k with _ | k
    · right; decide
    · left; exact Heap.block_val_of_ge _ _ _ (by omega)
  · apply disj_of_forall_none
    intro k
    rcases k with _ | _ | _ | _ | k
    · left; decide
    · left; decide
    · right; decide
    · right; decide
    · left; exact Heap.block_val_of_ge _ _ _ (by omega)

/-! ## R2c: what fails for the mixed pairings (two counterexamples) -/

/-- **R2c, first counterexample (join, encode-based fields with arbitrary padding).** For `structS`
(`structRep layoutS u8Rep pairRep`, modeling `#[repr(C)] struct S { a: u8, b: u16 }` with one
interior padding byte), the heap `heapS9` (`a = 1`, `b = (2, 3)`, padding byte initialized to `9`)
satisfies the encode-based field points-to for both fields separated from `padAny`, but not the
encode-based struct points-to: the join law fails for the pairing "encode-based fields + padding
holding anything". Stated in canonical form: the general join entailment fails for this layout and
these field representations. -/
theorem ptsEnc_struct_join_padAny_fails :
    sep (ptsEnc .full u8Rep 0 1)
        (sep (ptsEnc .full pairRep (0 + layoutS.off₂) (2, 3)) (padAny .full layoutS 0)) heapS9 ∧
      ¬ ptsEnc .full structS 0 (1, (2, 3)) heapS9 ∧
      ¬ ∀ (p : Perm) (a : Nat) (v₁ : Byte) (v₂ : Byte × Byte) (h : BHeap Byte),
          sep (ptsEnc p u8Rep a v₁)
              (sep (ptsEnc p pairRep (a + layoutS.off₂) v₂) (padAny p layoutS a)) h →
            ptsEnc p structS a (v₁, v₂) h := by
  have hsep : sep (ptsEnc .full u8Rep 0 1)
      (sep (ptsEnc .full pairRep (0 + layoutS.off₂) (2, 3)) (padAny .full layoutS 0)) heapS9 :=
    ⟨_, _, heapS9_parts_disj.1, heapS9_split, rfl,
      ⟨_, _, heapS9_parts_disj.2, rfl, rfl, ⟨_, rfl⟩⟩⟩
  have hnot : ¬ ptsEnc .full structS 0 (1, (2, 3)) heapS9 := by
    intro he
    have := congrArg (fun x : Bytes Byte 4 => x[1]) (Heap.block_inj he)
    exact absurd this (by decide)
  exact ⟨hsep, hnot, fun H => hnot (H _ _ _ _ _ hsep)⟩

/-- **R2c, second counterexample (split, decode-based struct into uninit padding).** For
`structS`, the heap `heapS9` satisfies the decode-based struct points-to for `(1, (2, 3))` (the
decoder ignores the padding byte), but does not split into decode-based field points-to separated
from `padUninit`: the split law fails for the pairing "decode-based fields + `uninit` padding". -/
theorem ptsDec_struct_split_padUninit_fails :
    ptsDec .full structS 0 (1, (2, 3)) heapS9 ∧
      ¬ sep (ptsDec .full u8Rep 0 1)
          (sep (ptsDec .full pairRep (0 + layoutS.off₂) (2, 3)) (padUninit .full layoutS 0))
          heapS9 ∧
      ¬ ∀ (p : Perm) (a : Nat) (v₁ : Byte) (v₂ : Byte × Byte) (h : BHeap Byte),
          ptsDec p structS a (v₁, v₂) h →
            sep (ptsDec p u8Rep a v₁)
              (sep (ptsDec p pairRep (a + layoutS.off₂) v₂) (padUninit p layoutS a)) h := by
  have hdec : ptsDec .full structS 0 (1, (2, 3)) heapS9 := ⟨_, rfl, by decide⟩
  have hnot : ¬ sep (ptsDec .full u8Rep 0 1)
      (sep (ptsDec .full pairRep (0 + layoutS.off₂) (2, 3)) (padUninit .full layoutS 0))
      heapS9 := by
    rintro ⟨h₁, h₂₃, _, he, ⟨x₁, hx₁, _⟩, ⟨h₂, h₃, _, he₂₃, ⟨x₂, hx₂, _⟩, hp⟩⟩
    have e := congrArg (fun h : BHeap Byte => h.val 1) he
    have hx₁' : h₁ = Heap.block .full 0 x₁ := hx₁
    have hx₂' : h₂ = Heap.block .full (0 + layoutS.off₂) x₂ := hx₂
    have hp' : h₃ = Heap.blockOn .full 0 (Bytes.uninit layoutS.size) layoutS.isPad := hp
    subst hx₁' hx₂' hp' he₂₃
    have l : heapS9.val 1 = some ⟨.full, .init 9⟩ := by decide
    have r1 : (Heap.block .full 0 x₁).val 1 = none := Heap.block_val_of_ge _ _ _ (by decide)
    have r2 : (Heap.block .full (0 + layoutS.off₂) x₂).val 1 = none :=
      Heap.block_val_of_lt _ _ _ (by decide)
    have r3 : (Heap.blockOn .full 0 (Bytes.uninit layoutS.size) layoutS.isPad : BHeap Byte).val 1
        = some ⟨.full, .uninit⟩ := by decide
    rw [l, BHeap.union_eq, BHeap.union_eq, Heap.join_val, Heap.join_val, r1, r2, r3] at e
    exact absurd e (by decide)
  exact ⟨hdec, hnot, fun H => hnot (H _ _ _ _ _ hdec)⟩

/-! ## Non-vacuity -/

/-- Non-vacuity for R2a: `layoutS` is non-overlapping, and both sides of R2a hold for `structS` at
`heapS9` (padding initialized). -/
theorem ptsDec_struct_iff_sep_fields_padAny_nonvacuous :
    layoutS.NonOverlap ∧ ptsDec .full structS 0 (1, (2, 3)) heapS9 ∧
      sep (ptsDec .full u8Rep 0 1)
        (sep (ptsDec .full pairRep (0 + layoutS.off₂) (2, 3)) (padAny .full layoutS 0)) heapS9 :=
  ⟨layoutS_nonOverlap, ptsDec_struct_split_padUninit_fails.1,
    ⟨_, _, heapS9_parts_disj.1, heapS9_split, ⟨_, rfl, rfl⟩,
      ⟨_, _, heapS9_parts_disj.2, rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl⟩⟩⟩⟩

/-- A block holding the encoding of `S { a: 1, b: (2, 3) }` (padding `uninit`). -/
abbrev heapSU : BHeap Byte :=
  Heap.block .full 0 (#v[.init 1, .uninit, .init 2, .init 3] : Bytes Byte 4)

/-- `heapSU` splits into the field cells and the (uninit) padding cell. -/
theorem heapSU_split :
    heapSU = Heap.join (Heap.block .full 0 (#v[.init 1] : Bytes Byte 1))
      (Heap.join (Heap.block .full (0 + 2) (#v[.init 2, .init 3] : Bytes Byte 2))
        (Heap.blockOn .full 0 (Bytes.uninit 4 : Bytes Byte 4) layoutS.isPad)) := by
  apply Heap.ext
  intro k
  rcases k with _ | _ | _ | _ | k
  · decide
  · decide
  · decide
  · decide
  · simp only [Heap.join_val]
    rw [Heap.block_val_of_ge _ _ _ (by omega), Heap.block_val_of_ge _ _ _ (by omega),
      Heap.block_val_of_ge _ _ _ (by omega), Heap.blockOn_val_of_ge _ _ _ _ (by omega)]
    rfl

theorem heapSU_parts_disj :
    disj (Heap.block .full 0 (#v[.init 1] : Bytes Byte 1))
      (Heap.join (Heap.block .full (0 + 2) (#v[.init 2, .init 3] : Bytes Byte 2))
        (Heap.blockOn .full 0 (Bytes.uninit 4 : Bytes Byte 4) layoutS.isPad)) ∧
    disj (Heap.block .full (0 + 2) (#v[.init 2, .init 3] : Bytes Byte 2))
        (Heap.blockOn .full 0 (Bytes.uninit 4 : Bytes Byte 4) layoutS.isPad) := by
  constructor
  · apply disj_of_forall_none
    intro k
    rcases k with _ | k
    · right; decide
    · left; exact Heap.block_val_of_ge _ _ _ (by omega)
  · apply disj_of_forall_none
    intro k
    rcases k with _ | _ | _ | _ | k
    · left; decide
    · left; decide
    · right; decide
    · right; decide
    · left; exact Heap.block_val_of_ge _ _ _ (by omega)

/-- Non-vacuity for R2b: `layoutS` is non-overlapping, and both sides of R2b hold for `structS`
at the block holding the encoding of `(1, (2, 3))` (padding `uninit`). -/
theorem ptsEnc_struct_iff_sep_fields_padUninit_nonvacuous :
    layoutS.NonOverlap ∧ ptsEnc .full structS 0 (1, (2, 3)) heapSU ∧
      sep (ptsEnc .full u8Rep 0 1)
        (sep (ptsEnc .full pairRep (0 + layoutS.off₂) (2, 3)) (padUninit .full layoutS 0)) heapSU := by
  refine ⟨layoutS_nonOverlap, ?_, ⟨_, _, heapSU_parts_disj.1, heapSU_split, rfl,
      ⟨_, _, heapSU_parts_disj.2, rfl, rfl, rfl⟩⟩⟩
  show Heap.block .full 0 _ = Heap.block .full 0 _
  congr 1

/-! ## Tightness of `NonOverlap` -/

/-- A union-like layout: two one-byte fields both at offset `0` in a one-byte struct. -/
abbrev layoutU : Layout2 := ⟨1, 1, 0, 1, by decide, by decide⟩

/-- At full permission, the two field blocks of `layoutU` share cell `a`, so they cannot be
separated. -/
theorem not_sep_overlapping_fields {P₃ : Assn (BHeap Byte)} (x₁ x₂ : Bytes Byte 1) (h : BHeap Byte) :
    ¬ sep (ptsB .full 0 x₁) (sep (ptsB .full (0 + layoutU.off₂) x₂) P₃) h := by
  rintro ⟨h₁, h₂₃, hd, -, hx₁, ⟨h₂, h₃, -, he₂₃, hx₂, -⟩⟩
  have hx₁' : h₁ = Heap.block .full 0 x₁ := hx₁
  have hx₂' : h₂ = Heap.block .full 0 x₂ := hx₂
  subst hx₁' hx₂' he₂₃
  have e1 : (Heap.block .full 0 x₁).val 0 = some ⟨.full, x₁[0]⟩ :=
    Heap.block_val_add .full 0 x₁ (i := 0) (by decide)
  have e2 : (union (Heap.block .full 0 x₂) h₃).val 0 = some ⟨.full, x₂[0]⟩ := by
    rw [BHeap.union_eq, Heap.join_val, Heap.block_val_add .full 0 x₂ (i := 0) (by decide)]
    rfl
  have hro := (hd 0 _ _ e1 e2).1
  cases hro

/-- Tightness of `hL` in R2a: for the overlapping layout `layoutU` (both fields `u8Rep` at offset
`0`), the equivalence fails at full permission: the block `[init 7]` satisfies the decode-based
struct points-to of `(7, 7)`, but no heap satisfies the separated field points-to. -/
theorem ptsDec_struct_split_tight_hL :
    ¬ layoutU.NonOverlap ∧
      ¬ ∀ (p : Perm) (a : Nat) (v₁ v₂ : Byte) (h : BHeap Byte),
        (ptsDec p (structRep layoutU u8Rep u8Rep) a (v₁, v₂) h ↔
          sep (ptsDec p u8Rep a v₁) (sep (ptsDec p u8Rep (a + layoutU.off₂) v₂) (padAny p layoutU a)) h) := by
  refine ⟨by decide, fun H => ?_⟩
  have hl : ptsDec .full (structRep layoutU u8Rep u8Rep) 0 ((7 : Byte), (7 : Byte))
      (Heap.block .full 0 (#v[.init 7] : Bytes Byte 1)) := ⟨_, rfl, by decide⟩
  obtain ⟨h₁, h₂₃, hd, he, ⟨x₁, hx₁, -⟩, ⟨h₂, h₃, hd', he', ⟨x₂, hx₂, -⟩, hp⟩⟩ := (H _ _ _ _ _).mp hl
  exact not_sep_overlapping_fields x₁ x₂ _ ⟨h₁, h₂₃, hd, he, hx₁, ⟨h₂, h₃, hd', he', hx₂, hp⟩⟩

/-- Tightness of `hL` in R2b: for the overlapping layout `layoutU`, the encode-based struct
points-to of `(7, 7)` holds at the block `[init 7]`, but no heap satisfies the separated field
points-to at full permission. -/
theorem ptsEnc_struct_split_tight_hL :
    ¬ layoutU.NonOverlap ∧
      ¬ ∀ (p : Perm) (a : Nat) (v₁ v₂ : Byte) (h : BHeap Byte),
        (ptsEnc p (structRep layoutU u8Rep u8Rep) a (v₁, v₂) h ↔
          sep (ptsEnc p u8Rep a v₁) (sep (ptsEnc p u8Rep (a + layoutU.off₂) v₂) (padUninit p layoutU a)) h) := by
  refine ⟨by decide, fun H => ?_⟩
  have hl : ptsEnc .full (structRep layoutU u8Rep u8Rep) 0 ((7 : Byte), (7 : Byte))
      (Heap.block .full 0 (#v[.init 7] : Bytes Byte 1)) := by
    show Heap.block .full 0 _ = Heap.block .full 0 _
    congr 1
  exact not_sep_overlapping_fields _ _ _ ((H _ _ _ _ _).mp hl)

end Toy.ByteSL
