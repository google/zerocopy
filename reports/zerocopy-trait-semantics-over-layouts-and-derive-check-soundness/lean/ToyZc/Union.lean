import ToyZc.Lemmas

/-!
# Result group 4: unions and `IntoBytes` (fully proved)

Union values are values written through one field (`Val.union j v`): the encoding is field `j`'s
encoding at offset `0` followed by `uninit` bytes up to the union's size.

* `union_intoBytes_iff_fields_intoBytes_full_size_of_inhabited` (R4a): for inhabited field types, a union is
  `IntoBytes` iff every field is `IntoBytes` and has the union's full size.
* `union_intoBytes_of_fields_of_padding_check` (R4b): the derive's conditions (every field
  `IntoBytes` and `union_padding! == 0`) imply `IntoBytes` (no inhabitedness needed).
* `union_u8_u16_written_through_u8_leaves_uninit` (R4c): `union { a: u8, b: u16 }` written through
  `a` leaves an `uninit` byte, although both fields are `IntoBytes`.
* `permissive_union_validity_of_size_pos_not_intoBytes` (R4d): if a union's values were *all* byte vectors of
  its size (a validity admitting uninitialized bytes), no union of nonzero size would be
  `IntoBytes`, whatever the derive check says. Positive control:
  `pc_written_union_intoBytes`.
-/

namespace Toy.Zc

theorem Desc.layouts_eq_map (fs : List Desc) : Desc.layouts fs = fs.map Desc.layout := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [Desc.layouts, ih]

theorem le_alignUp (n a : Nat) : n ≤ alignUp n a := by
  unfold alignUp
  omega

theorem foldl_max_size_ge_init (l : List FieldLayout) (init : Nat) :
    init ≤ l.foldl (fun acc f => max acc f.size) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons f fs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldl_max_size_ge_mem (l : List FieldLayout) (init : Nat) (f : FieldLayout) (hf : f ∈ l) :
    f.size ≤ l.foldl (fun acc g => max acc g.size) init := by
  induction l generalizing init with
  | nil => cases hf
  | cons g gs ih =>
    simp only [List.foldl_cons]
    cases hf with
    | head => exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_size_ge_init _ _)
    | tail _ h => exact ih _ h

/-- Every field fits in the union. -/
theorem field_size_le_union_size (r : UnionRepr) (fs : List Desc) (f : Desc) (hf : f ∈ fs) :
    f.size ≤ (Desc.union r fs).size := by
  show f.layout.size ≤ (Toy.Zc.unionLayout r.modifier (Desc.layouts fs)).size
  unfold Toy.Zc.unionLayout
  simp only
  refine Nat.le_trans ?_ (le_alignUp _ _)
  apply foldl_max_size_ge_mem
  rw [Desc.layouts_eq_map]
  exact List.mem_map_of_mem hf

theorem writeField_eq : ∀ (fs : List Desc) (j : Nat) (v : Val) (buf : List AB),
    Desc.writeField fs j v buf = if h : j < fs.length then writeAt buf 0 ((fs[j]).encodeL v) else buf
  | [], j, v, buf => by simp [Desc.writeField]
  | f :: fs, 0, v, buf => by simp [Desc.writeField]
  | f :: fs, j + 1, v, buf => by simp [Desc.writeField, writeField_eq fs j v buf]

theorem hasTypeField_iff : ∀ (fs : List Desc) (j : Nat) (v : Val),
    Desc.hasTypeField fs j v = true ↔ ∃ h : j < fs.length, (fs[j]).hasType v = true
  | [], j, v => by simp [Desc.hasTypeField]
  | f :: fs, 0, v => by simp [Desc.hasTypeField]
  | f :: fs, j + 1, v => by simp [Desc.hasTypeField, hasTypeField_iff fs j v]

/-- The bytes of a union value written through field `j`. -/
theorem union_encodeL_getD (r : UnionRepr) (fs : List Desc) (j : Nat) (hj : j < fs.length)
    (w : Val) (i : Nat) (hi : i < (Desc.union r fs).size) :
    ((Desc.union r fs).encodeL (.union j w)).getD i .uninit =
      if i < fs[j].size then (fs[j].encodeL w).getD i .uninit else .uninit := by
  have hN : (Desc.union r fs).size = (Toy.Zc.unionLayout r.modifier (Desc.layouts fs)).size := rfl
  rw [hN] at hi
  simp only [Desc.encodeL]
  rw [writeField_eq]
  simp only [hj, ↓reduceDIte]
  rw [fit_of_length (by rw [writeAt_length]; simp)]
  rw [getD_writeAt_zero _ _ _ (by simpa using hi), encodeL_length]
  split
  · rfl
  · exact getD_replicate_uninit _ _

/-- The direction of R4a that needs no inhabitedness. -/
theorem union_intoBytes_of_fields_full_size (r : UnionRepr) (fs : List Desc)
    (h : ∀ f ∈ fs, SemIntoBytes f ∧ f.size = (Desc.union r fs).size) :
    SemIntoBytes (.union r fs) := by
  rw [semIntoBytes_iff_encodeL_init]
  intro v hv i hi
  cases v with
  | union j w =>
    obtain ⟨hj, hw⟩ := (hasTypeField_iff fs j w).mp hv
    obtain ⟨hIB, hsz⟩ := h _ (List.getElem_mem hj)
    rw [union_encodeL_getD r fs j hj w i hi]
    have hi' : i < fs[j].size := by omega
    simp only [hi', ↓reduceIte]
    exact (semIntoBytes_iff_encodeL_init _).mp hIB w hw i hi'
  | _ => simp [Desc.hasType] at hv

/-- **R4a.** For a union whose field types are inhabited, `IntoBytes` holds iff every field is
`IntoBytes` and every field has exactly the union's size. -/
theorem union_intoBytes_iff_fields_intoBytes_full_size_of_inhabited (r : UnionRepr) (fs : List Desc)
    (hInh : ∀ f ∈ fs, f.Inhabited) :
    SemIntoBytes (.union r fs) ↔ ∀ f ∈ fs, SemIntoBytes f ∧ f.size = (Desc.union r fs).size := by
  refine ⟨fun h => ?_, union_intoBytes_of_fields_full_size r fs⟩
  rw [semIntoBytes_iff_encodeL_init] at h
  intro f hf
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
  have hle := field_size_le_union_size r fs fs[j] hf
  have htyped : ∀ w, fs[j].hasType w = true → (Desc.union r fs).hasType (.union j w) = true :=
    fun w hw => (hasTypeField_iff fs j w).mpr ⟨hj, hw⟩
  refine ⟨?_, ?_⟩
  · rw [semIntoBytes_iff_encodeL_init]
    intro w hw i hi
    have := h (.union j w) (htyped w hw) i (Nat.lt_of_lt_of_le hi hle)
    rw [union_encodeL_getD r fs j hj w i (Nat.lt_of_lt_of_le hi hle)] at this
    simpa only [hi, ↓reduceIte] using this
  · obtain ⟨w, hw⟩ := hInh _ hf
    rcases Nat.lt_or_ge fs[j].size (Desc.union r fs).size with hlt | hge
    · exfalso
      have := h (.union j w) (htyped w hw) fs[j].size hlt
      rw [union_encodeL_getD r fs j hj w _ hlt] at this
      simp only [Nat.lt_irrefl, ↓reduceIte] at this
      cases this
    · exact Nat.le_antisymm hle hge

/-- **R4b.** Soundness of the union `IntoBytes` derive's semantic conditions: if every field is
`IntoBytes` and the padding check `union_padding! == 0` passes, the union is `IntoBytes`. -/
theorem union_intoBytes_of_fields_of_padding_check (r : UnionRepr) (fs : List Desc)
    (hF : ∀ f ∈ fs, SemIntoBytes f) (hP : unionPaddingOK r fs = true) :
    SemIntoBytes (.union r fs) := by
  apply union_intoBytes_of_fields_full_size
  intro f hf
  refine ⟨hF f hf, ?_⟩
  have h1 := field_size_le_union_size r fs f hf
  have h2 := List.all_eq_true.mp hP f hf
  have h3 : (Desc.unionLayout r fs).size - f.size = 0 := by simpa using h2
  have h4 : (Desc.union r fs).size = (Desc.unionLayout r fs).size := rfl
  omega

/-- **R4c (counterexample; a reference point).** `union { a: u8, b: u16 }` written through `a` has
bytes `[init 7, uninit]`; both fields are `IntoBytes`, but the union is not. (The same instance is
the tightness counterexample `ce_union_drop_full_size` of R4a/R4b.) -/
theorem union_u8_u16_written_through_u8_leaves_uninit :
    (Desc.union (.c .none) [.u8, .u16]).encodeL (.union 0 (.int [7])) = [.init 7, .uninit] ∧
    (∀ f ∈ [Desc.u8, Desc.u16], SemIntoBytes f) ∧
    ¬ SemIntoBytes (.union (.c .none) [.u8, .u16]) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact semIntoBytes_int _
  · rw [semIntoBytes_iff_encodeL_init]
    intro h
    have := h (.union 0 (.int [7])) (by decide) 1 (by decide)
    revert this
    decide

/-- The canonical counterexample for the "full size" hypothesis of R4a/R4b: every field is
`IntoBytes` and inhabited, the padding check fails, and the union is not `IntoBytes`. -/
theorem ce_union_drop_full_size :
    (∀ f ∈ [Desc.u8, Desc.u16], SemIntoBytes f ∧ f.Inhabited) ∧
    unionPaddingOK (.c .none) [.u8, .u16] = false ∧
    ¬ SemIntoBytes (.union (.c .none) [.u8, .u16]) := by
  refine ⟨?_, by decide, union_u8_u16_written_through_u8_leaves_uninit.2.2⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨semIntoBytes_int _, ⟨.int [0], by decide⟩⟩
  · exact ⟨semIntoBytes_int _, ⟨.int [0, 0], by decide⟩⟩

/-- The canonical counterexample for the "every field `IntoBytes`" hypothesis (R4b) and right-hand
conjunct (R4a): a union of two inhabited 2-byte fields, one of which (`#[repr(C, align(2))] struct
{ a: u8 }`, one trailing padding byte) is not `IntoBytes`. Field sizes match the union's size (so
the padding check passes), and the union is not `IntoBytes`. -/
theorem ce_union_drop_fields_intoBytes :
    let pad : Desc := .strct (.c (.aligned 2)) [.u8]
    (∀ f ∈ [Desc.u16, pad], f.Inhabited) ∧
    (∀ f ∈ [Desc.u16, pad], f.size = (Desc.union (.c .none) [.u16, pad]).size) ∧
    unionPaddingOK (.c .none) [.u16, pad] = true ∧
    ¬ (∀ f ∈ [Desc.u16, pad], SemIntoBytes f) ∧
    ¬ SemIntoBytes (.union (.c .none) [.u16, pad]) := by
  have hpad : ¬ SemIntoBytes (.strct (.c (.aligned 2)) [.u8]) := by
    rw [semIntoBytes_iff_encodeL_init]
    intro h
    have := h (.strct [.int [0]]) (by decide) 1 (by decide)
    revert this
    decide
  refine ⟨?_, by decide, by decide, ?_, ?_⟩
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨.int [0, 0], by decide⟩
    · exact ⟨.strct [.int [0]], by decide⟩
  · intro h
    exact hpad (h _ (by simp))
  · rw [semIntoBytes_iff_encodeL_init]
    intro h
    have := h (.union 1 (.strct [.int [0]])) (by decide) 1 (by decide)
    revert this
    decide

/-- A union with an uninhabited field (a zero-variant enum, which `Desc.wf` excludes) of smaller
size is `IntoBytes` (only the `u16` field can be written), although not every field has full size. -/
theorem union_with_uninhabited_field_intoBytes :
    let U : Desc := .union (.c .none) [.u16, .enm (.prim .u8) []]
    SemIntoBytes U ∧ ¬ (∀ f ∈ [Desc.u16, Desc.enm (.prim .u8) []], f.size = U.size) := by
  refine ⟨?_, by decide⟩
  rw [semIntoBytes_iff_encodeL_init]
  intro v hv i hi
  cases v with
  | union j w =>
    obtain ⟨hj, hw⟩ := (hasTypeField_iff _ j w).mp hv
    match j, hj with
    | 0, _ =>
      rw [union_encodeL_getD _ _ 0 (by decide) w i hi]
      have hU : (Desc.union (.c .none) [Desc.u16, Desc.enm (.prim .u8) []]).size = 2 := by decide
      have h2 : Desc.u16.size = 2 := rfl
      have hi' : i < Desc.u16.size := by omega
      simp only [List.getElem_cons_zero] at hw ⊢
      simp only [hi', ↓reduceIte]
      exact (semIntoBytes_iff_encodeL_init _).mp (semIntoBytes_int _) w hw i hi'
    | 1, _ =>
      exfalso
      cases w with
      | enm k fvs => simp [Desc.hasType, Desc.hasTypeVariant] at hw
      | _ => simp [Desc.hasType] at hw
  | _ => simp [Desc.hasType] at hv

/-- `u16` is inhabited (a positive example for `Desc.Inhabited`). -/
theorem ex_inhabited_pos : Desc.u16.Inhabited := ⟨.int [0, 0], by decide⟩

/-- The zero-variant enum is uninhabited (a negative example for `Desc.Inhabited`). -/
theorem not_inhabited_empty_enum : ¬ (Desc.enm (.prim .u8) []).Inhabited := by
  rintro ⟨v, hv⟩
  cases v with
  | enm k fvs => simp [Desc.hasType, Desc.hasTypeVariant] at hv
  | _ => simp [Desc.hasType] at hv

/-- **Tightness of `hInh` in R4a** (canonical form): the inhabitedness hypothesis fails and the
characterization fails (the union is `IntoBytes`, but not every field has full size). -/
theorem ce_union_iff_drop_inhabited :
    let fs : List Desc := [.u16, .enm (.prim .u8) []]
    ¬ (∀ f ∈ fs, f.Inhabited) ∧
    ¬ (SemIntoBytes (.union (.c .none) fs) ↔
        ∀ f ∈ fs, SemIntoBytes f ∧ f.size = (Desc.union (.c .none) fs).size) := by
  refine ⟨fun h => not_inhabited_empty_enum (h _ (by simp)), fun hiff => ?_⟩
  have hr := hiff.mp union_with_uninhabited_field_intoBytes.1
  exact union_with_uninhabited_field_intoBytes.2 (fun f hf => (hr f hf).2)

/-- Non-vacuity of R4a/R4b: `union { a: u16, b: i16 }` satisfies all hypotheses (and the derive
check with the `cfg` set). -/
theorem nv_union_intoBytes :
    let U : Desc := .union (.c .none) [.u16, .int .i16]
    (∀ f ∈ [Desc.u16, Desc.int .i16], SemIntoBytes f ∧ f.Inhabited ∧ f.size = U.size) ∧
    unionPaddingOK (.c .none) [.u16, .int .i16] = true ∧
    implIntoBytes cfgUnion U = true := by
  refine ⟨?_, by decide, by decide⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨semIntoBytes_int _, ⟨.int [0, 0], by decide⟩, by decide⟩
  · exact ⟨semIntoBytes_int _, ⟨.int [0, 0], by decide⟩, by decide⟩

/-! ## The `cfg` gate: what the model does and does not explain -/

/-- **Permissive union validity** (contrast model): the values of a union of size `n` are *all*
abstract byte vectors of length `n`, including partially or wholly uninitialized ones; encoding
is the identity. This is the reading under which "a bit-valid union value may contain
uninitialized bytes", which is the possibility that motivates zerocopy's `cfg` gate. -/
def permissiveUnionRep (n : Nat) : Rep (Bytes Byte n) (Bytes Byte n) := ⟨id, some⟩

/-- **R4d (impossibility).** Under permissive union validity, no union of nonzero size is
`IntoBytes`, regardless of its fields and of the derive check. -/
theorem permissive_union_validity_of_size_pos_not_intoBytes (r : UnionRepr) (fs : List Desc)
    (hn : 0 < (Desc.union r fs).size) :
    ¬ (permissiveUnionRep (Desc.union r fs).size).IntoBytes := by
  intro h
  have := h (Vector.replicate _ .uninit) 0 hn
  simp [permissiveUnionRep] at this

/-- **Tightness of `hn` in R4d.** A zero-size union (`union { a: [u8; 0] }`): under permissive
validity it is (vacuously) `IntoBytes`. -/
theorem ce_permissive_drop_size_pos :
    (Desc.union (.c .none) [.array .u8 0]).size = 0 ∧
    (permissiveUnionRep (Desc.union (.c .none) [.array .u8 0]).size).IntoBytes := by
  refine ⟨by decide, ?_⟩
  intro v i hi
  have h0 : (Desc.union (.c .none) [.array .u8 0]).size = 0 := by decide
  omega

/-- Positive control for R4d: in the written-through-a-field model, the union
`union { a: u16, b: i16 }` (nonzero size, accepted by the derive with the `cfg` set) *is*
`IntoBytes`. -/
theorem pc_written_union_intoBytes :
    0 < (Desc.union (.c .none) [.u16, .int .i16]).size ∧
    implIntoBytes cfgUnion (.union (.c .none) [.u16, .int .i16]) = true ∧
    SemIntoBytes (.union (.c .none) [.u16, .int .i16]) := by
  refine ⟨by decide, by decide, ?_⟩
  apply union_intoBytes_of_fields_of_padding_check _ _ _ (by decide)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> exact semIntoBytes_int _

/-- The `cfg` conjunct of the modeled check is not a semantic condition: with the `cfg` unset the
check rejects a union that is `IntoBytes` in the written-through-a-field model. -/
theorem union_gate_rejects_intoBytes_union :
    implIntoBytes cfgDefault (.union (.c .none) [.u16, .int .i16]) = false ∧
    SemIntoBytes (.union (.c .none) [.u16, .int .i16]) :=
  ⟨by decide, pc_written_union_intoBytes.2.2⟩

/-! ## What the union value model does not capture (fully proved observations) -/

/-- **The union decoder is not a left inverse of the encoder.** In `union { a: u8, b: u16 }`, the
bytes written through `b` (`[init 5, init 9]`, e.g. also the result of writing `b` and then
overwriting `a` with `5`) decode as the value written through `a`, whose encoding forgets byte 1.
So `Desc.rep` on unions violates the round-trip law "decode then encode returns the bytes", and
values produced by several successive field writes are not represented as distinct values. -/
theorem union_decode_encode_forgets_bytes :
    let U : Desc := .union (.c .none) [.u8, .u16]
    U.encodeL (.union 1 (.int [5, 9])) = [.init 5, .init 9] ∧
    U.decodeL [.init 5, .init 9] = some (.union 0 (.int [5])) ∧
    U.encodeL (.union 0 (.int [5])) = [.init 5, .uninit] :=
  ⟨rfl, rfl, rfl⟩

/-- **The union decoder is not monotone in definedness.** In `union { a: u16, b: u8 }`, the bytes
`[init 5, uninit]` decode as the value written through `b`; initializing the second byte changes the
decoded value to one written through `a`. (The decoder picks the first field, in declaration order,
that decodes the corresponding prefix.) -/
theorem union_decode_not_monotone :
    let U : Desc := .union (.c .none) [.u16, .u8]
    U.decodeL [.init 5, .uninit] = some (.union 1 (.int [5])) ∧
    U.decodeL [.init 5, .init 9] = some (.union 0 (.int [5, 9])) :=
  ⟨rfl, rfl⟩

end Toy.Zc
