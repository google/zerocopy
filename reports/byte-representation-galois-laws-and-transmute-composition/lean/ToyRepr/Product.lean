import ToyRepr.Examples

/-!
# Result group 4: products with explicit field offsets

A `k`-field product of total size `n` is described by a `Layout n k`: per field `j`, a size
`L.size j` and an offset `L.off j` with `L.off j + L.size j ≤ n`. Offsets are arbitrary (any
order, no alignment), so a `Layout` describes the concrete placement chosen by `repr(C)`, by
`repr(packed)`, or by the compiler for a `repr(Rust)` struct or tuple once its layout is fixed.
Overlapping field ranges are allowed by the definition but do not model unions: `prodRep` decodes
*all* fields and writes *all* fields (first field wins on overlap), whereas a union holds one
active variant. Given a representation
`r j : Rep (Bytes D (L.size j)) (V j)` for each field, `prodRep L r` represents dependent
tuples `(j : Fin k) → V j`:

* `prodEncode` writes, at each byte `i`, the corresponding byte of the encoding of the field
  that owns `i` (the first field, in index order, whose range `[off j, off j + size j)`
  contains `i`), and `uninit` at bytes owned by no field (padding);
* `prodDecode` decodes every field from its own byte range and succeeds iff every field
  decodes; it never reads padding bytes.

Main statements: each law transfers from the fields to the product, and only
`DecodeEncode` needs the field ranges to be pairwise disjoint; `FromBytes` transfers; and
`IntoBytes` transfers when the fields cover every byte (no padding).
-/

namespace Toy.Repr

/-- Placement of `k` fields inside an `n`-byte product: sizes and offsets, with every field
inside the product. Field ranges may overlap unless `Disjoint` is assumed. -/
structure Layout (n k : Nat) where
  /-- Size in bytes of field `j`. -/
  size : Fin k → Nat
  /-- Offset in bytes of field `j`. -/
  off : Fin k → Nat
  /-- Every field lies within the product. -/
  fits : ∀ j, off j + size j ≤ n

namespace Layout

variable {n k : Nat} (L : Layout n k)

/-- Byte `i` lies in the range of field `j`. -/
def InField (j : Fin k) (i : Nat) : Prop := L.off j ≤ i ∧ i < L.off j + L.size j

instance (j : Fin k) (i : Nat) : Decidable (L.InField j i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The field owning byte `i`: the first field (in index order) whose range contains `i`,
or `none` if `i` is a padding byte. -/
def owner (i : Nat) : Option (Fin k) :=
  (List.finRange k).find? fun j => decide (L.InField j i)

/-- Field ranges are pairwise disjoint. -/
def Disjoint : Prop :=
  ∀ j j' : Fin k, j ≠ j' → ∀ i, L.InField j i → L.InField j' i → False

/-- Every byte of the product lies in some field (the layout has no padding). -/
def Covering : Prop := ∀ i, i < n → ∃ j, L.InField j i

theorem inField_of_owner {i : Nat} {j : Fin k} (h : L.owner i = some j) : L.InField j i := by
  have := List.find?_some h
  exact of_decide_eq_true this

theorem owner_eq_none_iff (i : Nat) : L.owner i = none ↔ ∀ j, ¬ L.InField j i := by
  unfold owner
  rw [List.find?_eq_none]
  constructor
  · intro h j hj
    have := h j (List.mem_finRange j)
    simp [hj] at this
  · intro h j _
    simp [h j]

theorem owner_eq_some_of_disjoint (hD : L.Disjoint) {i : Nat} {j : Fin k} (hj : L.InField j i) :
    L.owner i = some j := by
  cases ho : L.owner i with
  | none => exact absurd hj ((L.owner_eq_none_iff i).mp ho j)
  | some j' =>
    have hj' := L.inField_of_owner ho
    by_cases hjj : j' = j
    · rw [hjj]
    · exact (hD j' j hjj i hj' hj).elim

theorem sub_lt_of_owner {i : Nat} {j : Fin k} (h : L.owner i = some j) : i - L.off j < L.size j := by
  have := L.inField_of_owner h
  unfold InField at this
  omega

end Layout

/-- The `m` bytes of `x` starting at offset `o`. -/
def Bytes.slice {D : Type} {n : Nat} (x : Bytes D n) (o m : Nat) (h : o + m ≤ n) : Bytes D m :=
  Vector.ofFn fun t => x[o + t.val]

@[simp] theorem Bytes.getElem_slice {D : Type} {n : Nat} (x : Bytes D n) (o m : Nat) (h : o + m ≤ n)
    (t : Nat) (ht : t < m) : (x.slice o m h)[t] = x[o + t] := by
  simp [Bytes.slice]

section Product

variable {D : Type} {n k : Nat} {V : Fin k → Type}

/-- Encoder of the product: field bytes at the owning field's offset, `uninit` padding. -/
def prodEncode (L : Layout n k) (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (v : (j : Fin k) → V j) : Bytes D n :=
  Vector.ofFn fun i =>
    match h : L.owner i.val with
    | none => .uninit
    | some j => ((r j).encode (v j))[i.val - L.off j]'(L.sub_lt_of_owner h)

/-- Decoder of the product: decode each field from its own range; succeed iff all succeed. -/
def prodDecode (L : Layout n k) (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (x : Bytes D n) : Option ((j : Fin k) → V j) :=
  if h : ∀ j, ((r j).decode (x.slice (L.off j) (L.size j) (L.fits j))).isSome then
    some fun j => ((r j).decode (x.slice (L.off j) (L.size j) (L.fits j))).get (h j)
  else none

/-- The product representation built from field representations placed at the offsets of `L`
(padding bytes are written `uninit` and never read). -/
def prodRep (L : Layout n k) (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j)) :
    Rep (Bytes D n) ((j : Fin k) → V j) :=
  ⟨prodEncode L r, prodDecode L r⟩

@[simp] theorem prodRep_decode (L : Layout n k) (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (x : Bytes D n) : (prodRep L r).decode x = prodDecode L r x := rfl

@[simp] theorem prodRep_encode (L : Layout n k) (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (v : (j : Fin k) → V j) : (prodRep L r).encode v = prodEncode L r v := rfl

theorem getElem_prodEncode_of_owner_none (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j)) (v : (j : Fin k) → V j)
    {i : Nat} (hi : i < n) (h : L.owner i = none) : (prodEncode L r v)[i] = .uninit := by
  unfold prodEncode
  rw [Vector.getElem_ofFn]
  split
  · rfl
  · rename_i j hj
    simp only at hj
    rw [h] at hj
    cases hj

theorem getElem_prodEncode_of_owner_some (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j)) (v : (j : Fin k) → V j)
    {i : Nat} (hi : i < n) {j : Fin k} (h : L.owner i = some j) :
    (prodEncode L r v)[i] = ((r j).encode (v j))[i - L.off j]'(L.sub_lt_of_owner h) := by
  unfold prodEncode
  rw [Vector.getElem_ofFn]
  split
  · rename_i hj
    simp only at hj
    rw [h] at hj
    cases hj
  · rename_i j' hj'
    simp only at hj'
    rw [h] at hj'
    cases hj'
    rfl

theorem prodDecode_eq_some_iff (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j)) (x : Bytes D n) (v : (j : Fin k) → V j) :
    prodDecode L r x = some v ↔
      ∀ j, (r j).decode (x.slice (L.off j) (L.size j) (L.fits j)) = some (v j) := by
  unfold prodDecode
  split
  · rename_i h
    constructor
    · intro hv j
      cases hv
      exact (Option.some_get (h j)).symm
    · intro hv
      congr 1
      funext j
      have := hv j
      simp [this]
  · rename_i h
    constructor
    · intro hv
      cases hv
    · intro hv
      exact absurd (fun j => by rw [hv j]; rfl) h

theorem prodDecode_eq_none_iff (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j)) (x : Bytes D n) :
    prodDecode L r x = none ↔
      ∃ j, (r j).decode (x.slice (L.off j) (L.size j) (L.fits j)) = none := by
  unfold prodDecode
  split
  · rename_i h
    constructor
    · intro hv
      cases hv
    · intro ⟨j, hj⟩
      have := h j
      rw [hj] at this
      cases this
  · rename_i h
    constructor
    · intro _
      apply Classical.byContradiction
      intro hne
      apply h
      intro j
      cases hj : (r j).decode (x.slice (L.off j) (L.size j) (L.fits j)) with
      | none => exact absurd ⟨j, hj⟩ hne
      | some _ => rfl
    · intro _
      rfl

end Product

/-! ## R4 main statements -/

section R4

variable {D : Type} {n k : Nat} {V : Fin k → Type}

/-- Two reads of a byte vector at equal indices agree (helper for index arithmetic). -/
theorem Bytes.getElem_congr_idx (x : Bytes D n) {a b : Nat} (hab : a = b) (ha : a < n)
    (hb : b < n) : x[a] = x[b] := by
  subst hab
  rfl

/-- Slicing preserves the pointwise definedness order. -/
theorem Bytes.slice_le {x y : Bytes D n} (hxy : x ⊑ y) (o m : Nat) (h : o + m ≤ n) :
    x.slice o m h ⊑ y.slice o m h := by
  intro t ht
  rw [Bytes.getElem_slice, Bytes.getElem_slice]
  exact hxy _ _

/-- Slices of a fully initialized vector are fully initialized. -/
theorem Bytes.slice_isInit {x : Bytes D n} (hx : x.IsInit) (o m : Nat) (h : o + m ≤ n) :
    (x.slice o m h).IsInit := by
  intro t ht
  rw [Bytes.getElem_slice]
  exact hx _ _

/-- With pairwise disjoint field ranges, the slice of the product encoding at field `j` is the
encoding of field `j`. -/
theorem slice_prodEncode_of_disjoint (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j)) (v : (j : Fin k) → V j)
    (hD : L.Disjoint) (j : Fin k) :
    (prodEncode L r v).slice (L.off j) (L.size j) (L.fits j) = (r j).encode (v j) := by
  apply Vector.ext
  intro t ht
  rw [Bytes.getElem_slice]
  have hin : L.InField j (L.off j + t) := ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ht _⟩
  rw [getElem_prodEncode_of_owner_some L r v _ (L.owner_eq_some_of_disjoint hD hin)]
  exact Bytes.getElem_congr_idx _ (by omega) _ _

/-- **R4a.** If every field representation satisfies `DecodeMono`, so does the product, for any
layout (field ranges may overlap). -/
theorem prodRep_decodeMono_of_fields (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (hM : ∀ j, (r j).DecodeMono) : (prodRep L r).DecodeMono := by
  intro x y hxy
  show prodDecode L r x ⊑ prodDecode L r y
  cases hx : prodDecode L r x with
  | none => exact OptLe.none_le _
  | some v =>
    have hy : prodDecode L r y = some v := by
      rw [prodDecode_eq_some_iff] at hx ⊢
      intro j
      have hm := hM j _ _ (Bytes.slice_le hxy (L.off j) (L.size j) (L.fits j))
      rw [hx j] at hm
      exact OptLe.some_le_iff.mp hm
    rw [hy]
    exact OptLe.refl _

/-- **R4b.** If every field representation satisfies `DecodeEncode` and the field ranges are
pairwise disjoint, the product satisfies `DecodeEncode`. -/
theorem prodRep_decodeEncode_of_fields_of_disjoint (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (hDE : ∀ j, (r j).DecodeEncode) (hD : L.Disjoint) : (prodRep L r).DecodeEncode := by
  intro v
  show prodDecode L r (prodEncode L r v) = some v
  rw [prodDecode_eq_some_iff]
  intro j
  rw [slice_prodEncode_of_disjoint L r v hD j]
  exact hDE j (v j)

/-- **R4c.** If every field representation satisfies `EncodeLeast`, so does the product, for any
layout (field ranges may overlap). -/
theorem prodRep_encodeLeast_of_fields (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (hEL : ∀ j, (r j).EncodeLeast) : (prodRep L r).EncodeLeast := by
  intro x v hx i hi
  change prodDecode L r x = some v at hx
  rw [prodDecode_eq_some_iff] at hx
  change (prodEncode L r v)[i] ⊑ x[i]
  cases ho : L.owner i with
  | none =>
    rw [getElem_prodEncode_of_owner_none L r v hi ho]
    exact AByte.uninit_le _
  | some j =>
    rw [getElem_prodEncode_of_owner_some L r v hi ho]
    have h1 := hEL j _ (v j) (hx j) (i - L.off j) (L.sub_lt_of_owner ho)
    rw [Bytes.getElem_slice] at h1
    have hin := L.inField_of_owner ho
    unfold Layout.InField at hin
    rw [Bytes.getElem_congr_idx x (show L.off j + (i - L.off j) = i by omega) _ hi] at h1
    exact h1

/-- **R4d.** If every field representation is `IntoBytes` and the fields cover every byte of the
product (no padding), the product is `IntoBytes`. -/
theorem prodRep_intoBytes_of_fields_of_covering (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (hIB : ∀ j, (r j).IntoBytes) (hC : L.Covering) : (prodRep L r).IntoBytes := by
  intro v i hi
  change ((prodEncode L r v)[i]).isInit = true
  cases ho : L.owner i with
  | none =>
    obtain ⟨j, hj⟩ := hC i hi
    exact absurd hj ((L.owner_eq_none_iff i).mp ho j)
  | some j =>
    rw [getElem_prodEncode_of_owner_some L r v hi ho]
    exact hIB j (v j) _ _

/-- **R4e.** If every field representation is `FromBytes`, the product is `FromBytes`, for any
layout (padding bytes impose no constraint). -/
theorem prodRep_fromBytes_of_fields (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (hFB : ∀ j, (r j).FromBytes) : (prodRep L r).FromBytes := by
  intro x hx
  have h : ∀ j, ∃ w, (r j).decode (x.slice (L.off j) (L.size j) (L.fits j)) = some w :=
    fun j => hFB j _ (Bytes.slice_isInit hx (L.off j) (L.size j) (L.fits j))
  refine ⟨fun j => Classical.choose (h j), ?_⟩
  change prodDecode L r x = some _
  rw [prodDecode_eq_some_iff]
  intro j
  exact Classical.choose_spec (h j)

end R4

/-! ## Concrete layouts -/

/-- One one-byte field at offset 0 in a one-byte product. -/
abbrev layout1 : Layout 1 1 := ⟨fun _ => 1, fun _ => 0, fun _ => by decide⟩

/-- One one-byte field at offset 0 in a two-byte product (byte 1 is padding). -/
abbrev layoutPad : Layout 2 1 := ⟨fun _ => 1, fun _ => 0, fun _ => by decide⟩

/-- Two one-byte fields both at offset 0 in a one-byte product (overlapping). -/
abbrev layoutOverlap : Layout 1 2 := ⟨fun _ => 1, fun _ => 0, fun _ => by decide⟩

/-- Two one-byte fields at offsets 0 and 2 in a three-byte product (byte 1 is padding):
`repr(C)` layout of `struct { a: u8, b: u8 }` with an artificial 1-byte gap. -/
abbrev layout3 : Layout 3 2 := ⟨fun _ => 1, fun j => 2 * j.val, fun j => by have := j.isLt; omega⟩

/-- Two one-byte fields at offsets 0 and 1 in a two-byte product (no padding). -/
abbrev layout2 : Layout 2 2 := ⟨fun _ => 1, fun j => j.val, fun j => by have := j.isLt; omega⟩

theorem layout1_owner_zero : layout1.owner 0 = some 0 := by decide
theorem layoutOverlap_owner_zero : layoutOverlap.owner 0 = some 0 := by decide
theorem layoutPad_owner_one : layoutPad.owner 1 = none := by decide
theorem layout3_owner : layout3.owner 0 = some 0 ∧ layout3.owner 1 = none ∧ layout3.owner 2 = some 1 := by
  decide

theorem layout3_disjoint : layout3.Disjoint := by
  intro j j' hjj i hj hj'
  unfold Layout.InField layout3 at hj hj'
  simp only at hj hj'
  apply hjj
  apply Fin.ext
  omega

theorem layout2_disjoint : layout2.Disjoint := by
  intro j j' hjj i hj hj'
  unfold Layout.InField layout2 at hj hj'
  simp only at hj hj'
  apply hjj
  apply Fin.ext
  omega

theorem layout1_covering : layout1.Covering := fun i hi => ⟨0, by unfold Layout.InField layout1; simp only; omega⟩

theorem layout2_covering : layout2.Covering := by
  intro i hi
  refine ⟨⟨i, hi⟩, ?_⟩
  unfold Layout.InField layout2
  simp only
  omega

/-! ## Definition examples for layouts and products -/

theorem ex_disjoint_pos : layout3.Disjoint := layout3_disjoint

theorem ex_disjoint_neg : ¬ layoutOverlap.Disjoint := by
  intro h
  exact h 0 1 (by decide) 0 (by unfold Layout.InField layoutOverlap; decide)
    (by unfold Layout.InField layoutOverlap; decide)

theorem ex_covering_pos : layout2.Covering := layout2_covering

theorem ex_covering_neg : ¬ layout3.Covering := by
  intro h
  obtain ⟨j, hj⟩ := h 1 (by decide)
  unfold Layout.InField layout3 at hj
  simp only at hj
  omega

/-- Field representations for `layout3`/`layout2`: both fields are `u8`. -/
abbrev u8Fields3 : (j : Fin 2) → Rep (Bytes Byte (layout3.size j)) Byte := fun _ => u8Rep
/-- Field representations for `layout2`: both fields are `u8`. -/
abbrev u8Fields2 : (j : Fin 2) → Rep (Bytes Byte (layout2.size j)) Byte := fun _ => u8Rep

/-- Positive example for `prodEncode`: field bytes at their offsets, padding `uninit`. -/
theorem ex_prodEncode_pos (v : Fin 2 → Byte) :
    (prodEncode layout3 u8Fields3 v)[0] = .init (v 0) ∧
    (prodEncode layout3 u8Fields3 v)[1] = .uninit ∧
    (prodEncode layout3 u8Fields3 v)[2] = .init (v 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [getElem_prodEncode_of_owner_some _ _ _ (by decide) layout3_owner.1]
    rfl
  · exact getElem_prodEncode_of_owner_none _ _ _ (by decide) layout3_owner.2.1
  · rw [getElem_prodEncode_of_owner_some _ _ _ (by decide) layout3_owner.2.2]
    rfl

/-- Positive example for `prodDecode`: padding is ignored, fields are read at their offsets. -/
theorem ex_prodDecode_pos :
    prodDecode layout3 u8Fields3 #v[.init 7, .uninit, .init 9] = some (fun j => if j = 0 then 7 else 9) := by
  rw [prodDecode_eq_some_iff]
  intro j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- Negative example for `prodDecode`: an `uninit` byte inside a field makes decoding fail. -/
theorem ex_prodDecode_neg :
    prodDecode layout3 u8Fields3 #v[.init 7, .init 8, .uninit] = none := by
  rw [prodDecode_eq_none_iff]
  exact ⟨1, rfl⟩

/-- Negative example for `prodEncode`: the padding byte is never written as initialized (here:
the encoding differs from the vector with `init 0` in the padding byte). -/
theorem ex_prodEncode_neg (v : Fin 2 → Byte) :
    prodEncode layout3 u8Fields3 v ≠ #v[.init (v 0), .init 0, .init (v 1)] := by
  intro h
  have h1 := congrArg (fun x : Bytes Byte 3 => x[1]) h
  have h2 : (prodEncode layout3 u8Fields3 v)[1] = .uninit := (ex_prodEncode_pos v).2.1
  change (prodEncode layout3 u8Fields3 v)[1] = (AByte.init 0 : AByte Byte) at h1
  rw [h2] at h1
  cases h1

theorem ex_inField_pos : layout3.InField 1 2 := by
  unfold Layout.InField layout3; decide

theorem ex_inField_neg : ¬ layout3.InField 0 1 := by
  unfold Layout.InField layout3; decide

theorem ex_owner_pos : layout3.owner 2 = some 1 := layout3_owner.2.2

theorem ex_owner_neg : layout3.owner 1 = none := layout3_owner.2.1

/-! ## R4 counterexamples and non-vacuity -/

/-- Single field `exactUnitRep` (not monotone) on `layout1`. -/
abbrev exactUnitFields1 : (j : Fin 1) → Rep (Bytes Byte (layout1.size j)) Unit := fun _ => exactUnitRep
/-- Single `u8` field with an always-failing decoder on `layout1`. -/
abbrev noneU8Fields1 : (j : Fin 1) → Rep (Bytes Byte (layout1.size j)) Byte := fun _ => noneRep u8Rep.encode
/-- Two `u8` fields on the overlapping `layoutOverlap`. -/
abbrev u8FieldsOverlap : (j : Fin 2) → Rep (Bytes Byte (layoutOverlap.size j)) Byte := fun _ => u8Rep
/-- Single `boolNZRep` field on `layout1`. -/
abbrev boolNZFields1 : (j : Fin 1) → Rep (Bytes Byte (layout1.size j)) Bool := fun _ => boolNZRep
/-- Single padding-byte field on `layout1`. -/
abbrev padUnitFields1 : (j : Fin 1) → Rep (Bytes Byte (layout1.size j)) Unit := fun _ => padUnitRep
/-- Single `u8` field on `layoutPad` (followed by a padding byte). -/
abbrev u8FieldsPad : (j : Fin 1) → Rep (Bytes Byte (layoutPad.size j)) Byte := fun _ => u8Rep
/-- Single `boolRep` field on `layout1`. -/
abbrev boolFields1 : (j : Fin 1) → Rep (Bytes Byte (layout1.size j)) Bool := fun _ => boolRep

/-- Tightness of `hM` in R4a: a single field that is not monotone (`exactUnitRep`) gives a
non-monotone product. -/
theorem prodRep_decodeMono_tight_hM :
    ¬ (prodRep layout1 exactUnitFields1).DecodeMono := by
  intro h
  have hle : (#v[.uninit] : Bytes Byte 1) ⊑ #v[.init 0] := Bytes.le_one trivial
  have h1 := h _ _ hle
  have hx : prodDecode layout1 exactUnitFields1
      #v[.uninit] = some (fun _ => ()) := by
    rw [prodDecode_eq_some_iff]
    intro j
    rfl
  have hy : prodDecode layout1 exactUnitFields1
      #v[.init 0] = none := by
    rw [prodDecode_eq_none_iff]
    exact ⟨0, rfl⟩
  rw [prodRep_decode, prodRep_decode] at h1
  rw [hx, hy] at h1
  exact h1

/-- Tightness of `hDE` in R4b: a single field with an always-failing decoder (the layout is
trivially disjoint). -/
theorem prodRep_decodeEncode_tight_hDE :
    layout1.Disjoint ∧
    ¬ (prodRep layout1 noneU8Fields1).DecodeEncode := by
  refine ⟨fun j j' hjj => absurd (Subsingleton.elim j j') hjj, fun h => ?_⟩
  have := h (fun _ => 0)
  rw [prodRep_encode, prodRep_decode] at this
  rw [prodDecode_eq_some_iff] at this
  cases this 0

/-- Tightness of `hD` in R4b: two `u8` fields at the same offset; the encoder keeps only the first
field's byte, so decoding returns the first value for both fields. -/
theorem prodRep_decodeEncode_tight_hD :
    (∀ j, (u8FieldsOverlap j).DecodeEncode) ∧
    ¬ (prodRep layoutOverlap u8FieldsOverlap).DecodeEncode := by
  refine ⟨fun _ => u8Rep_decodeEncode, fun h => ?_⟩
  have := h (fun j => if j = 0 then 1 else 2)
  rw [prodRep_encode, prodRep_decode] at this
  rw [prodDecode_eq_some_iff] at this
  have h1 := this 1
  have hb : (prodEncode layoutOverlap u8FieldsOverlap
      (fun j => if j = 0 then 1 else 2))[0] = .init 1 := by
    rw [getElem_prodEncode_of_owner_some _ _ _ (by decide) layoutOverlap_owner_zero]
    rfl
  have hs : (u8Rep.decode ((prodEncode layoutOverlap u8FieldsOverlap
      (fun j => if j = 0 then 1 else 2)).slice 0 1 (by decide))) = some 1 := by
    rw [u8Rep, byteRep_decode, Bytes.getElem_slice, hb]
  change u8Rep.decode (Bytes.slice _ 0 1 _) = _ at h1
  rw [hs] at h1
  exact absurd h1 (by decide)

/-- Tightness of `hEL` in R4c: a single field violating `EncodeLeast` (`boolNZRep`). -/
theorem prodRep_encodeLeast_tight_hEL :
    ¬ (prodRep layout1 boolNZFields1).EncodeLeast := by
  intro h
  have hd : prodDecode layout1 boolNZFields1
      #v[.init 2] = some (fun _ => true) := by
    rw [prodDecode_eq_some_iff]
    intro j
    rfl
  have := h _ _ (by rw [prodRep_decode]; exact hd) 0 (by decide)
  rw [prodRep_encode] at this
  rw [getElem_prodEncode_of_owner_some _ _ _ (by decide) layout1_owner_zero] at this
  exact absurd this (by decide)

/-- Tightness of `hIB` in R4d: a single field of pure padding (`padUnitRep`) covering the whole
product. -/
theorem prodRep_intoBytes_tight_hIB :
    layout1.Covering ∧
    ¬ (prodRep layout1 padUnitFields1).IntoBytes := by
  refine ⟨layout1_covering, fun h => ?_⟩
  have := h (fun _ => ()) 0 (by decide)
  rw [prodRep_encode] at this
  rw [getElem_prodEncode_of_owner_some _ _ _ (by decide) layout1_owner_zero] at this
  cases this

/-- Tightness of `hC` in R4d: a `u8` field followed by a padding byte. -/
theorem prodRep_intoBytes_tight_hC :
    (∀ j, (u8FieldsPad j).IntoBytes) ∧
    ¬ (prodRep layoutPad u8FieldsPad).IntoBytes := by
  refine ⟨fun _ => u8Rep_intoBytes, fun h => ?_⟩
  have := h (fun _ => 0) 1 (by decide)
  rw [prodRep_encode] at this
  rw [getElem_prodEncode_of_owner_none _ _ _ (by decide) layoutPad_owner_one] at this
  cases this

/-- Tightness of `hFB` in R4e: a single niche-carrying field (`boolRep`). -/
theorem prodRep_fromBytes_tight_hFB :
    ¬ (prodRep layout1 boolFields1).FromBytes := by
  intro h
  obtain ⟨v, hv⟩ := h #v[.init 2] (Bytes.isInit_one rfl)
  rw [prodRep_decode] at hv
  rw [prodDecode_eq_some_iff] at hv
  have := hv 0
  change boolRep.decode (Bytes.slice _ 0 1 _) = _ at this
  rw [boolRep, byteRep_decode, Bytes.getElem_slice] at this
  generalize v 0 = w at this
  revert w
  decide

/-- Non-vacuity for R4a, R4b, R4c, R4e: two `u8` fields at offsets 0 and 2 with a padding byte
between them. -/
theorem prodRep_laws_nonvacuous :
    (∀ j, (u8Fields3 j).DecodeMono) ∧ (∀ j, (u8Fields3 j).DecodeEncode) ∧ layout3.Disjoint ∧
    (∀ j, (u8Fields3 j).EncodeLeast) ∧ (∀ j, (u8Fields3 j).FromBytes) :=
  ⟨fun _ => u8Rep_decodeMono, fun _ => u8Rep_decodeEncode, layout3_disjoint,
   fun _ => u8Rep_encodeLeast, fun _ => u8Rep_fromBytes⟩

/-- Non-vacuity for R4d: two `u8` fields at offsets 0 and 1 (no padding). -/
theorem prodRep_intoBytes_nonvacuous :
    (∀ j, (u8Fields2 j).IntoBytes) ∧ layout2.Covering :=
  ⟨fun _ => u8Rep_intoBytes, layout2_covering⟩

end Toy.Repr
