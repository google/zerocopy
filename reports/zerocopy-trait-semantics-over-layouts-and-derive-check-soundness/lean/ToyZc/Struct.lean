import ToyZc.ProofSupport

/-!
# Result group 2: struct derives

* `struct_fromBytes_iff_fields_fromBytes` (R2a): a struct is `FromBytes` iff every field is,
  for every representation in the model, padding or not.
* `struct_fromZeros_iff_fields_fromZeros` (R2a, `FromZeros` half): likewise for `FromZeros`.
* `struct_intoBytes_iff_fields_intoBytes_no_padding_of_inhabited` (R2c): for inhabited field types, a struct
  is `IntoBytes` iff every field is `IntoBytes` and the struct's size is the sum of the field sizes.
* `structPaddingOK_sound` (R2d): for a well-formed struct, the derive's padding analysis
  (`repr(transparent)`, `repr(packed)`, the zero/one-field `repr(C)` case without `align(N > 1)`,
  or `struct_padding! == 0`) implies `size = Σ field sizes`.
-/

namespace Toy.Zc

/-- Sum of the sizes of a list of descriptions. -/
def Desc.fieldSizeSum (fs : List Desc) : Nat := (fs.map Desc.size).sum

/-! ### Auxiliary lemmas: struct decoding and encoding along the placement -/

theorem strct_size_eq (r : StructRepr) (fs : List Desc) (m : ReprModifier)
    (hm : ∀ ls, r.layout ls = reprCStruct m ls) :
    (Desc.strct r fs).size =
      alignUp (placeFields m 0 (Desc.layouts fs)).2 (structAlign m (Desc.layouts fs)) := by
  show (r.layout (Desc.layouts fs)).size = _
  rw [hm]
  rfl

theorem strct_end_le_size (r : StructRepr) (fs : List Desc) (m : ReprModifier)
    (hm : ∀ ls, r.layout ls = reprCStruct m ls) :
    (placeFields m 0 (Desc.layouts fs)).2 ≤ (Desc.strct r fs).size := by
  rw [strct_size_eq r fs m hm]
  exact le_alignUp _ _

theorem strct_sum_le_end (fs : List Desc) (m : ReprModifier) :
    Desc.fieldSizeSum fs ≤ (placeFields m 0 (Desc.layouts fs)).2 := by
  have := placeFields_end_ge m (Desc.layouts fs) 0
  rw [layouts_map_size] at this
  unfold Desc.fieldSizeSum
  omega

theorem strct_decodeL_isSome (r : StructRepr) (fs : List Desc) (m : ReprModifier)
    (hm : ∀ ls, r.layout ls = reprCStruct m ls) (x : List AB) :
    ((Desc.strct r fs).decodeL x).isSome =
      (decide (x.length = (Desc.strct r fs).size) &&
        (Desc.decodeFields fs (placeFields m 0 (Desc.layouts fs)).1 x).isSome) := by
  simp only [Desc.decodeL]
  rw [hm]
  show (if x.length = (reprCStruct m (Desc.layouts fs)).size then _ else none).isSome = _
  rw [show (Desc.strct r fs).size = (reprCStruct m (Desc.layouts fs)).size from by
    show (r.layout (Desc.layouts fs)).size = _; rw [hm]]
  split
  · rename_i h
    simp [h, reprCStruct_offsets]
  · rename_i h
    simp [h]

theorem strct_encodeL (r : StructRepr) (fs : List Desc) (m : ReprModifier)
    (hm : ∀ ls, r.layout ls = reprCStruct m ls) (vs : List Val) :
    (Desc.strct r fs).encodeL (.strct vs) =
      Desc.writeFields fs (placeFields m 0 (Desc.layouts fs)).1 vs
        (List.replicate (Desc.strct r fs).size .uninit) := by
  simp only [Desc.encodeL]
  rw [hm]
  rw [show (Desc.strct r fs).size = (reprCStruct m (Desc.layouts fs)).size from by
    show (r.layout (Desc.layouts fs)).size = _; rw [hm]]
  rw [fit_of_length (by rw [writeFields_length]; simp)]
  rfl

theorem slice_replicate_append (z : Byte) (o : Nat) (cs : List Byte) (k : Nat) :
    slice ((List.replicate o z ++ cs ++ List.replicate k z).map AByte.init) o cs.length =
      cs.map AByte.init := by
  simp [slice]

theorem slice_replicate (a : AB) (N o n : Nat) (h : o + n ≤ N) :
    slice (List.replicate N a) o n = List.replicate n a := by
  simp [slice, List.drop_replicate, List.take_replicate]
  omega

/-- **R2a.** A struct (any representation in the model) is `FromBytes` iff every field is
`FromBytes`. Padding bytes impose no constraint. -/
theorem struct_fromBytes_iff_fields_fromBytes (r : StructRepr) (fs : List Desc) :
    SemFromBytes (.strct r fs) ↔ ∀ f ∈ fs, SemFromBytes f := by
  obtain ⟨m, hm⟩ := structRepr_layout_eq r
  have hend := strct_end_le_size r fs m hm
  constructor
  · intro h f hf
    rw [semFromBytes_iff_validInit_total] at h ⊢
    intro cs hcs
    obtain ⟨o, _, ho2, ho3⟩ := decodeFields_field m fs 0 f hf
    have hlen : (List.replicate o (0 : Byte) ++ cs ++
        List.replicate ((Desc.strct r fs).size - o - f.size) 0).length = (Desc.strct r fs).size := by
      simp only [List.length_append, List.length_replicate, hcs]
      omega
    have hv := h _ hlen
    rw [validInit_eq_isSome, strct_decodeL_isSome r fs m hm] at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    have := ho3 _ hv.2
    rw [← hcs, slice_replicate_append] at this
    rw [validInit_eq_isSome]
    exact this
  · intro hF
    rw [semFromBytes_iff_validInit_total]
    intro bs hbs
    rw [validInit_eq_isSome, strct_decodeL_isSome r fs m hm]
    simp only [List.length_map, hbs, decide_true, Bool.true_and]
    refine decodeFields_isSome_of m (fun b => b.isInit = true) fs 0 _ (by simp; omega)
      (fun b hb => by
        simp only [List.mem_map] at hb
        obtain ⟨_, _, rfl⟩ := hb
        rfl) ?_
    intro f hf y hy hyI
    obtain ⟨cs, rfl⟩ := exists_map_init_of_forall_isInit y hyI
    have := (semFromBytes_iff_validInit_total f).mp (hF f hf) cs (by simpa using hy)
    rwa [validInit_eq_isSome] at this

/-- **R2a (`FromZeros` half).** A struct (any representation in the model) is `FromZeros` iff every
field is `FromZeros`. -/
theorem struct_fromZeros_iff_fields_fromZeros (r : StructRepr) (fs : List Desc) :
    SemFromZeros (.strct r fs) ↔ ∀ f ∈ fs, SemFromZeros f := by
  obtain ⟨m, hm⟩ := structRepr_layout_eq r
  have hend := strct_end_le_size r fs m hm
  constructor
  · intro h f hf
    rw [semFromZeros_iff_validInit_zeros] at h ⊢
    obtain ⟨o, _, ho2, ho3⟩ := decodeFields_field m fs 0 f hf
    rw [validInit_eq_isSome, strct_decodeL_isSome r fs m hm] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have := ho3 _ h.2
    rw [List.map_replicate, slice_replicate _ _ _ _ (by omega)] at this
    rw [validInit_eq_isSome, List.map_replicate]
    exact this
  · intro hF
    rw [semFromZeros_iff_validInit_zeros]
    rw [validInit_eq_isSome, strct_decodeL_isSome r fs m hm]
    simp only [List.length_map, List.length_replicate, decide_true, Bool.true_and]
    refine decodeFields_isSome_of m (fun b => b = .init 0) fs 0 _ (by simp; omega)
      (fun b hb => by
        simp only [List.map_replicate, List.mem_replicate] at hb
        exact hb.2) ?_
    intro f hf y hy hy0
    have hyr : y = (List.replicate f.size (0 : Byte)).map AByte.init := by
      rw [List.map_replicate, List.eq_replicate_iff]
      exact ⟨hy, hy0⟩
    have := (semFromZeros_iff_validInit_zeros f).mp (hF f hf)
    rw [validInit_eq_isSome] at this
    rw [hyr]
    exact this

/-- The direction of R2c that needs no inhabitedness: `IntoBytes` fields and no padding. -/
theorem struct_intoBytes_of_fields_of_no_padding (r : StructRepr) (fs : List Desc)
    (hF : ∀ f ∈ fs, SemIntoBytes f) (hsz : (Desc.strct r fs).size = Desc.fieldSizeSum fs) :
    SemIntoBytes (.strct r fs) := by
  obtain ⟨m, hm⟩ := structRepr_layout_eq r
  have hend := strct_end_le_size r fs m hm
  have hsum := strct_sum_le_end fs m
  rw [semIntoBytes_iff_encodeL_init]
  intro v hv i hi
  cases v with
  | strct vs =>
    simp only [Desc.hasType] at hv
    rw [strct_encodeL r fs m hm]
    refine writeFields_init_of_tight m fs 0 vs _ ?_ hF hv (by simp; omega) i (by simpa using hi) ?_
    · unfold Desc.fieldSizeSum at hsum hsz; omega
    · intro hcase; omega
  | _ => simp [Desc.hasType] at hv

/-- **R2c.** For a struct whose field types are inhabited, `IntoBytes` holds iff every field is
`IntoBytes` and the struct's size equals the sum of the field sizes (no padding). -/
theorem struct_intoBytes_iff_fields_intoBytes_no_padding_of_inhabited (r : StructRepr) (fs : List Desc)
    (hInh : ∀ f ∈ fs, f.Inhabited) :
    SemIntoBytes (.strct r fs) ↔
      (∀ f ∈ fs, SemIntoBytes f) ∧ (Desc.strct r fs).size = Desc.fieldSizeSum fs := by
  obtain ⟨m, hm⟩ := structRepr_layout_eq r
  have hend := strct_end_le_size r fs m hm
  have hsum := strct_sum_le_end fs m
  constructor
  · intro h
    rw [semIntoBytes_iff_encodeL_init] at h
    have H : ∀ vs, Desc.hasTypes fs vs = true → ∀ p, 0 ≤ p →
        p < (List.replicate (Desc.strct r fs).size (AByte.uninit : AB)).length →
        ((Desc.writeFields fs (placeFields m 0 (Desc.layouts fs)).1 vs
          (List.replicate (Desc.strct r fs).size .uninit)).getD p .uninit).isInit = true := by
      intro vs hvs p _ hp
      rw [← strct_encodeL r fs m hm]
      exact h (.strct vs) hvs p (by simpa using hp)
    refine ⟨fields_intoBytes_of_writeFields m fs 0 _ hInh (by simpa using hend) H, ?_⟩
    obtain ⟨vs, hvs⟩ := exists_hasTypes fs hInh
    have hsum' : Desc.fieldSizeSum fs = 0 + (fs.map Desc.size).sum := by
      unfold Desc.fieldSizeSum; omega
    rcases Nat.lt_or_ge (Desc.fieldSizeSum fs) (placeFields m 0 (Desc.layouts fs)).2 with hlt | hge
    · exfalso
      obtain ⟨p, _, hp2, hp3⟩ := writeFields_gap m fs 0 (by omega)
      have := H vs hvs p (Nat.zero_le _) (by simp; omega)
      rw [hp3, getD_replicate_uninit] at this
      cases this
    · rcases Nat.lt_or_ge (placeFields m 0 (Desc.layouts fs)).2 (Desc.strct r fs).size with hlt2 | hge2
      · exfalso
        have := H vs hvs (placeFields m 0 (Desc.layouts fs)).2 (Nat.zero_le _) (by simpa using hlt2)
        rw [writeFields_getD_ge m fs 0 vs _ _ (Nat.le_refl _), getD_replicate_uninit] at this
        cases this
      · omega
  · rintro ⟨hF, hsz⟩
    exact struct_intoBytes_of_fields_of_no_padding r fs hF hsz

/-! ### Auxiliary lemmas: alignment facts of descriptions -/

theorem foldl_max_ge_init {α : Type} (g : α → Nat) :
    ∀ (l : List α) (init : Nat), init ≤ l.foldl (fun acc x => max acc (g x)) init
  | [], _ => Nat.le_refl _
  | x :: l, init => Nat.le_trans (Nat.le_max_left init (g x)) (foldl_max_ge_init g l _)

theorem foldl_max_prop {α : Type} (g : α → Nat) (P : Nat → Prop)
    (hmax : ∀ a b, P a → P b → P (max a b)) :
    ∀ (l : List α) (init : Nat), P init → (∀ x ∈ l, P (g x)) →
      P (l.foldl (fun acc x => max acc (g x)) init)
  | [], _, h, _ => h
  | x :: l, _, h, hl => foldl_max_prop g P hmax l _ (hmax _ _ h (hl x List.mem_cons_self))
      (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem structAlign_pos (m : ReprModifier) (ls : List FieldLayout) : 0 < structAlign m ls := by
  have h := foldl_max_ge_init (fun f : FieldLayout => effFieldAlign m f.align) ls 1
  unfold structAlign fieldsMaxAlign
  cases m <;> simp only <;> omega

theorem unionLayout_align_pos (m : ReprModifier) (ls : List FieldLayout) :
    0 < (unionLayout m ls).align := by
  have h := foldl_max_ge_init (fun f : FieldLayout => effFieldAlign m f.align) ls 1
  unfold unionLayout
  cases m <;> simp only <;> omega

theorem reprCUnion_align_pos (ls : List FieldLayout) : 0 < (reprCUnion ls).align := by
  have h := foldl_max_ge_init (fun f : FieldLayout => f.align) ls 1
  unfold reprCUnion
  simp only
  omega

theorem Desc.align_pos : ∀ d : Desc, 0 < d.align := by
  refine Desc.induct' (fun d => 0 < d.align) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t; cases t <;> decide
  · decide
  · intro e n ih; exact ih
  · intro r fs _
    obtain ⟨m, hm⟩ := structRepr_layout_eq r
    show 0 < (r.layout (Desc.layouts fs)).align
    rw [hm, reprCStruct_align]
    exact structAlign_pos _ _
  · intro r vs _
    show 0 < (r.layout (Desc.variantLayouts vs)).align
    cases r with
    | c =>
      simp only [EnumRepr.layout, reprCEnum, reprCStruct]
      exact structAlign_pos _ _
    | prim t => exact reprCUnion_align_pos _
  · intro r fs _
    exact unionLayout_align_pos _ _
  · intro t ih; exact ih

theorem Desc.align_dvd_size : ∀ d : Desc, d.align ∣ d.size := by
  refine Desc.induct' (fun d => d.align ∣ d.size) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t; exact Nat.dvd_refl _
  · exact Nat.dvd_refl _
  · intro e n ih
    exact Nat.dvd_trans ih (Nat.dvd_mul_left _ _)
  · intro r fs _
    obtain ⟨m, hm⟩ := structRepr_layout_eq r
    show (r.layout (Desc.layouts fs)).align ∣ (r.layout (Desc.layouts fs)).size
    rw [hm, reprCStruct_align, reprCStruct_size]
    exact dvd_alignUp (structAlign_pos _ _)
  · intro r vs _
    show (r.layout (Desc.variantLayouts vs)).align ∣ (r.layout (Desc.variantLayouts vs)).size
    cases r with
    | c =>
      simp only [EnumRepr.layout, reprCEnum, reprCStruct]
      exact dvd_alignUp (structAlign_pos _ _)
    | prim t => exact dvd_alignUp (reprCUnion_align_pos _)
  · intro r fs _
    exact dvd_alignUp (unionLayout_align_pos _ _)
  · intro t ih; exact ih

theorem p2_max {a b : Nat} (ha : ∃ i, a = 2 ^ i) (hb : ∃ j, b = 2 ^ j) : ∃ k, max a b = 2 ^ k := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h]; exact hb
  · rw [Nat.max_eq_left h]; exact ha

theorem p2_min {a b : Nat} (ha : ∃ i, a = 2 ^ i) (hb : ∃ j, b = 2 ^ j) : ∃ k, min a b = 2 ^ k := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.min_eq_left h]; exact ha
  · rw [Nat.min_eq_right h]; exact hb

theorem p2_min_dvd_left {a b : Nat} (ha : ∃ i, a = 2 ^ i) (hb : ∃ j, b = 2 ^ j) : min a b ∣ a := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rcases Nat.le_total i j with h | h
  · rw [Nat.min_eq_left (Nat.pow_le_pow_right (by decide) h)]
    exact Nat.dvd_refl _
  · rw [Nat.min_eq_right (Nat.pow_le_pow_right (by decide) h)]
    exact Nat.pow_dvd_pow 2 h

theorem isPow2_spec {n : Nat} (h : isPow2 n = true) : ∃ k, n = 2 ^ k := by
  unfold isPow2 at h
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
  exact ⟨k, (beq_iff_eq.mp hk).symm⟩

theorem effFieldAlign_p2 (m : ReprModifier) (hm : m.wf = true) {a : Nat} (ha : ∃ i, a = 2 ^ i) :
    ∃ k, effFieldAlign m a = 2 ^ k := by
  cases m with
  | none => exact ha
  | packed p => exact p2_min ha (isPow2_spec hm)
  | aligned n => exact ha

theorem structAlign_p2 (m : ReprModifier) (hm : m.wf = true) (ls : List FieldLayout)
    (hls : ∀ l ∈ ls, ∃ i, l.align = 2 ^ i) : ∃ k, structAlign m ls = 2 ^ k := by
  have h := foldl_max_prop (fun f : FieldLayout => effFieldAlign m f.align) (fun n => ∃ k, n = 2 ^ k)
    (fun _ _ => p2_max) ls 1 ⟨0, rfl⟩ (fun l hl => effFieldAlign_p2 m hm (hls l hl))
  unfold structAlign fieldsMaxAlign
  cases m with
  | none => exact h
  | packed p => exact h
  | aligned n => exact p2_max h (isPow2_spec hm)

theorem unionLayout_align_p2 (m : ReprModifier) (hm : m.wf = true) (ls : List FieldLayout)
    (hls : ∀ l ∈ ls, ∃ i, l.align = 2 ^ i) : ∃ k, (unionLayout m ls).align = 2 ^ k := by
  have h := foldl_max_prop (fun f : FieldLayout => effFieldAlign m f.align) (fun n => ∃ k, n = 2 ^ k)
    (fun _ _ => p2_max) ls 1 ⟨0, rfl⟩ (fun l hl => effFieldAlign_p2 m hm (hls l hl))
  unfold unionLayout
  cases m with
  | none => exact h
  | packed p => exact h
  | aligned n => exact p2_max h (isPow2_spec hm)

theorem reprCUnion_align_p2 (ls : List FieldLayout) (hls : ∀ l ∈ ls, ∃ i, l.align = 2 ^ i) :
    ∃ k, (reprCUnion ls).align = 2 ^ k :=
  foldl_max_prop (fun f : FieldLayout => f.align) (fun n => ∃ k, n = 2 ^ k)
    (fun _ _ => p2_max) ls 1 ⟨0, rfl⟩ hls

theorem wfAll_iff : ∀ fs : List Desc, Desc.wfAll fs = true ↔ ∀ f ∈ fs, f.wf = true
  | [] => by simp [Desc.wfAll]
  | f :: fs => by simp [Desc.wfAll, wfAll_iff fs]

theorem wfVariants_iff : ∀ vs : List (DiscrSyn × List Desc),
    Desc.wfVariants vs = true ↔ ∀ v ∈ vs, ∀ f ∈ v.2, f.wf = true
  | [] => by simp [Desc.wfVariants]
  | (d, fs) :: vs => by simp [Desc.wfVariants, wfVariants_iff vs, wfAll_iff]

theorem variantLayouts_eq_map : ∀ vs : List (DiscrSyn × List Desc),
    Desc.variantLayouts vs = vs.map (fun v => Desc.layouts v.2)
  | [] => rfl
  | (d, fs) :: vs => by simp [Desc.variantLayouts, variantLayouts_eq_map vs]

theorem layouts_align_p2 (fs : List Desc) (h : ∀ f ∈ fs, ∃ k, f.align = 2 ^ k) :
    ∀ l ∈ Desc.layouts fs, ∃ i, l.align = 2 ^ i := by
  intro l hl
  rw [Desc.layouts_eq_map] at hl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hl
  exact h f hf

theorem Desc.wf_align_p2 : ∀ d : Desc, d.wf = true → ∃ k, d.align = 2 ^ k := by
  refine Desc.induct' (fun d => d.wf = true → ∃ k, d.align = 2 ^ k) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t _
    cases t
    all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩
  · intro _; exact ⟨0, rfl⟩
  · intro e n ih h; exact ih h
  · intro r fs ih h
    show ∃ k, (r.layout (Desc.layouts fs)).align = 2 ^ k
    cases r with
    | c m =>
      simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at h
      exact structAlign_p2 m h.1 _ (layouts_align_p2 fs (fun f hf => ih f hf (h.2 f hf)))
    | transparent =>
      simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at h
      exact structAlign_p2 .none rfl _ (layouts_align_p2 fs (fun f hf => ih f hf (h.1 f hf)))
  · intro r vs ih h
    simp only [Desc.wf, Bool.and_eq_true, wfVariants_iff] at h
    have hv : ∀ vl ∈ Desc.variantLayouts vs, ∀ l ∈ vl, ∃ i, l.align = 2 ^ i := by
      intro vl hvl
      rw [variantLayouts_eq_map] at hvl
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hvl
      exact layouts_align_p2 v.2 (fun f hf => ih v hv f hf (h.1.2 v hv f hf))
    show ∃ k, (r.layout (Desc.variantLayouts vs)).align = 2 ^ k
    cases r with
    | c =>
      simp only [EnumRepr.layout, reprCEnum, reprCStruct]
      apply structAlign_p2 .none rfl
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact ⟨2, rfl⟩
      · apply reprCUnion_align_p2
        intro l hl
        simp only [List.map_map, List.mem_map, Function.comp] at hl
        obtain ⟨vl, hvl, rfl⟩ := hl
        exact structAlign_p2 .none rfl vl (hv vl hvl)
    | prim t =>
      simp only [EnumRepr.layout, reprIntEnum]
      apply reprCUnion_align_p2
      intro l hl
      simp only [List.map_map, List.mem_map, Function.comp] at hl
      obtain ⟨vl, hvl, rfl⟩ := hl
      apply structAlign_p2 .none rfl
      intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · simp only [EnumRepr.tagLayout, EnumRepr.tagTy]
        cases t
        all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩
      · exact hv vl hvl l hl
  · intro r fs ih h
    cases r with
    | c m =>
      simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at h
      exact unionLayout_align_p2 m h.1.2 _ (layouts_align_p2 fs (fun f hf => ih f hf (h.2 f hf)))
  · intro t ih h; exact ih h

theorem alignUp_min_one (c a : Nat) : alignUp c (min a 1) = c := by
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; exact alignUp_zero_right c
  · rw [Nat.min_eq_right h]; exact alignUp_one c

theorem placeFields_packed1_end : ∀ (ls : List FieldLayout) (c : Nat),
    (placeFields (.packed 1) c ls).2 = c + (ls.map FieldLayout.size).sum
  | [], c => by simp [placeFields]
  | l :: ls, c => by
    rw [placeFields_cons]
    simp only [effFieldAlign, alignUp_min_one, List.map_cons, List.sum_cons]
    rw [placeFields_packed1_end ls]
    omega

theorem structAlign_packed1 (ls : List FieldLayout) : structAlign (.packed 1) ls = 1 := by
  have h1 := foldl_max_ge_init (fun f : FieldLayout => effFieldAlign (.packed 1) f.align) ls 1
  have h2 := foldl_max_prop (fun f : FieldLayout => effFieldAlign (.packed 1) f.align) (· ≤ 1)
    (fun a b ha hb => by omega) ls 1 (Nat.le_refl _)
    (fun l _ => by simp only [effFieldAlign]; omega)
  unfold structAlign fieldsMaxAlign
  simp only at h1 h2 ⊢
  omega

theorem placeFields_zst_end : ∀ (ls : List FieldLayout) (c : Nat),
    (∀ l ∈ ls, l.size = 0 ∧ l.align = 1) → (placeFields .none c ls).2 = c
  | [], c, _ => by simp [placeFields]
  | l :: ls, c, h => by
    rw [placeFields_cons]
    obtain ⟨h1, h2⟩ := h l List.mem_cons_self
    simp only [effFieldAlign, h1, h2, alignUp_one, Nat.add_zero]
    exact placeFields_zst_end ls c (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem sum_map_size_zero : ∀ (ls : List FieldLayout), (∀ l ∈ ls, l.size = 0) →
    (ls.map FieldLayout.size).sum = 0
  | [], _ => rfl
  | l :: ls, h => by
    simp only [List.map_cons, List.sum_cons, h l List.mem_cons_self,
      sum_map_size_zero ls (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))]

theorem transparent_layout_facts : ∀ (ls : List FieldLayout),
    ls.countP (fun l => !(l.size == 0 && l.align == 1)) ≤ 1 → (∀ l ∈ ls, l.align ∣ l.size) →
    (∀ l ∈ ls, l.align ∣ (ls.map FieldLayout.size).sum) ∧
      (placeFields .none 0 ls).2 = (ls.map FieldLayout.size).sum
  | [], _, _ => by simp [placeFields]
  | l :: ls, hc, hd => by
    rw [List.countP_cons] at hc
    rw [placeFields_cons]
    simp only [effFieldAlign, alignUp_zero_left, Nat.zero_add, List.map_cons, List.sum_cons]
    by_cases hz : l.size = 0 ∧ l.align = 1
    · have hp : (!(l.size == 0 && l.align == 1)) = false := by simp [hz.1, hz.2]
      simp only [hp, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc
      obtain ⟨ih1, ih2⟩ := transparent_layout_facts ls hc
        (fun l' hl' => hd l' (List.mem_cons_of_mem _ hl'))
      rw [hz.1, ih2]
      refine ⟨?_, by omega⟩
      intro l' hl'
      cases hl' with
      | head => rw [hz.2]; exact Nat.one_dvd _
      | tail _ h => rw [Nat.zero_add]; exact ih1 l' h
    · have hp : (!(l.size == 0 && l.align == 1)) = true := by
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        omega
      simp only [hp, ↓reduceIte] at hc
      have hz0 : ls.countP (fun l => !(l.size == 0 && l.align == 1)) = 0 := by omega
      have hall : ∀ l' ∈ ls, l'.size = 0 ∧ l'.align = 1 := by
        intro l' hl'
        have := List.countP_eq_zero.mp hz0 l' hl'
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
          Bool.not_eq_eq_eq_not, Bool.not_true] at this
        omega
      have hsum0 : (ls.map FieldLayout.size).sum = 0 :=
        sum_map_size_zero ls (fun l' hl' => (hall l' hl').1)
      rw [placeFields_zst_end ls _ hall, hsum0]
      refine ⟨?_, rfl⟩
      intro l' hl'
      cases hl' with
      | head => simpa using hd l List.mem_cons_self
      | tail _ h => rw [(hall l' h).2]; exact Nat.one_dvd _

/-- **R2d.** For a well-formed struct, the struct `IntoBytes` derive's padding analysis implies
that the struct has no padding: `size = Σ field sizes`. -/
theorem structPaddingOK_sound (r : StructRepr) (fs : List Desc)
    (hwf : (Desc.strct r fs).wf = true) (hP : structPaddingOK r fs = true) :
    (Desc.strct r fs).size = Desc.fieldSizeSum fs := by
  have hdvd : ∀ l ∈ Desc.layouts fs, l.align ∣ l.size := by
    intro l hl
    rw [Desc.layouts_eq_map] at hl
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hl
    exact Desc.align_dvd_size f
  have hmax_dvd : ∀ S, (fun n => n ∣ S) 1 →
      ∀ a b, (fun n => n ∣ S) a → (fun n => n ∣ S) b → (fun n => n ∣ S) (max a b) := by
    intro S _ a b ha hb
    rcases Nat.le_total a b with h | h
    · rw [Nat.max_eq_right h]; exact hb
    · rw [Nat.max_eq_left h]; exact ha
  cases r with
  | transparent =>
    have hm : ∀ ls, StructRepr.transparent.layout ls = reprCStruct .none ls := fun _ => rfl
    have hsz := strct_size_eq _ fs .none hm
    simp only [Desc.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨h1, h2⟩ := transparent_layout_facts _ hwf.2 hdvd
    unfold Desc.fieldSizeSum
    rw [← layouts_map_size, hsz, h2]
    apply alignUp_eq_of_dvd
    unfold structAlign fieldsMaxAlign
    exact foldl_max_prop (fun f : FieldLayout => effFieldAlign .none f.align)
      (· ∣ ((Desc.layouts fs).map FieldLayout.size).sum)
      (hmax_dvd _ (Nat.one_dvd _)) _ 1 (Nat.one_dvd _) h1
  | c m =>
    have hm : ∀ ls, (StructRepr.c m).layout ls = reprCStruct m ls := fun _ => rfl
    have hsz := strct_size_eq _ fs m hm
    have hend := strct_end_le_size _ fs m hm
    have hsum := strct_sum_le_end fs m
    simp only [structPaddingOK, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_true_eq, beq_iff_eq] at hP
    rcases hP with (hP | ⟨hA, hL⟩) | hP
    · -- `repr(C, packed(1))`
      have hm1 : m = .packed 1 := by
        cases m with
        | packed p =>
          match p, hP with
          | 1, _ => rfl
        | _ => simp [ReprModifier.isPacked1] at hP
      subst hm1
      rw [hsz, structAlign_packed1, alignUp_one, placeFields_packed1_end]
      unfold Desc.fieldSizeSum
      rw [layouts_map_size]
      omega
    · -- at most one field, no `align(N > 1)`
      match fs, hL with
      | [], _ =>
        rw [hsz]
        simp [Desc.layouts, placeFields, alignUp_zero_left, Desc.fieldSizeSum]
      | [f], _ =>
        rw [hsz]
        have hend1 : (placeFields m 0 (Desc.layouts [f])).2 = f.size := by
          simp only [layouts_cons, placeFields_cons, alignUp_zero_left, Nat.zero_add]
          rfl
        rw [hend1]
        have hfs : Desc.fieldSizeSum [f] = f.size := by simp [Desc.fieldSizeSum]
        rw [hfs]
        apply alignUp_eq_of_dvd
        have hpos := Desc.align_pos f
        have hfd := Desc.align_dvd_size f
        simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf
        have hfp := Desc.wf_align_p2 f (hwf.2 f List.mem_cons_self)
        cases m with
        | none =>
          show max 1 f.align ∣ f.size
          rw [Nat.max_eq_right hpos]
          exact hfd
        | packed p =>
          show max 1 (min f.align p) ∣ f.size
          have hpp := isPow2_spec hwf.1
          obtain ⟨k, hk⟩ := hpp
          have hp1 : 1 ≤ p := by rw [hk]; exact Nat.one_le_two_pow
          rw [Nat.max_eq_right (by omega)]
          exact Nat.dvd_trans (p2_min_dvd_left hfp ⟨k, hk⟩) hfd
        | aligned n =>
          show max (max 1 f.align) n ∣ f.size
          simp only [ReprModifier.isAlignGt1, decide_eq_false_iff_not, Nat.not_lt] at hA
          rw [Nat.max_eq_right hpos, Nat.max_eq_left (by omega)]
          exact hfd
    · -- `struct_padding! == 0`
      have hsz' : (Desc.strct (.c m) fs).size = (Desc.structLayout (.c m) fs).size := rfl
      unfold Desc.fieldSizeSum at *
      omega

/-! ## Non-vacuity -/

/-- Non-vacuity of R2a ("padding or not"): the padded struct `{ a: u8, b: u16 }` has `FromBytes`
and `FromZeros` fields and padding (`size 4 ≠ 1 + 2`). -/
theorem nv_struct_fromBytes_fromZeros_padded :
    (∀ f ∈ [Desc.u8, Desc.u16], SemFromBytes f ∧ SemFromZeros f) ∧
    Desc.paddedPair.size ≠ Desc.fieldSizeSum [.u8, .u16] := by
  refine ⟨?_, by decide⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> exact ⟨semFromBytes_int _, semFromZeros_int _⟩

/-- Non-vacuity of R2c: `{ a: u16, b: u8, c: u8 }` has inhabited `IntoBytes` fields and no padding. -/
theorem nv_struct_intoBytes :
    (∀ f ∈ [Desc.u16, Desc.u8, Desc.u8], f.Inhabited ∧ SemIntoBytes f) ∧
    Desc.fullTriple.size = Desc.fieldSizeSum [.u16, .u8, .u8] := by
  refine ⟨?_, by decide⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨⟨.int [0, 0], by decide⟩, semIntoBytes_int _⟩
  · exact ⟨⟨.int [0], by decide⟩, semIntoBytes_int _⟩
  · exact ⟨⟨.int [0], by decide⟩, semIntoBytes_int _⟩

/-- Non-vacuity of R2d: each shortcut of the padding analysis, on a well-formed struct. -/
theorem nv_structPaddingOK :
    (Desc.strct .transparent [.strct (.c .none) [], .u32]).wf = true ∧
      structPaddingOK .transparent [.strct (.c .none) [], .u32] = true ∧
    (Desc.strct (.c (.packed 1)) [.u8, .u16]).wf = true ∧
      structPaddingOK (.c (.packed 1)) [.u8, .u16] = true ∧
    (Desc.strct (.c (.packed 2)) [.u32]).wf = true ∧
      structPaddingOK (.c (.packed 2)) [.u32] = true ∧
    Desc.fullTriple.wf = true ∧ structPaddingOK (.c .none) [.u16, .u8, .u8] = true := by
  decide

/-! ## Tightness counterexamples -/

/-- **Tightness (padding).** The padded struct `{ a: u8, b: u16 }` has `IntoBytes`, inhabited
fields, its size differs from the sum of its field sizes (`4 ≠ 3`), the derive rejects it, and it is
not `IntoBytes`. This is the canonical counterexample for the no-padding conjunct of R2c. -/
theorem ce_padded_struct_of_intoBytes_fields_not_intoBytes :
    (∀ f ∈ [Desc.u8, Desc.u16], f.Inhabited ∧ SemIntoBytes f) ∧
    Desc.paddedPair.size ≠ Desc.fieldSizeSum [.u8, .u16] ∧
    structPaddingOK (.c .none) [.u8, .u16] = false ∧
    ¬ SemIntoBytes Desc.paddedPair := by
  refine ⟨?_, by decide, by decide, not_semIntoBytes_paddedPair⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨⟨.int [0], by decide⟩, semIntoBytes_int _⟩
  · exact ⟨⟨.int [0, 0], by decide⟩, semIntoBytes_int _⟩

/-- `#[repr(C, align(2))] struct { a: u8 }` (one byte of trailing padding). -/
abbrev Desc.alignedByte : Desc := .strct (.c (.aligned 2)) [.u8]

theorem not_semIntoBytes_alignedByte : ¬ SemIntoBytes Desc.alignedByte := by
  rw [semIntoBytes_iff_encodeL_init]
  intro h
  have := h (.strct [.int [0]]) (by decide) 1 (by decide)
  revert this
  decide

/-- **Tightness (the `!is_align_gt_1` conjunct of the one-field shortcut).** The well-formed
`#[repr(C, align(2))] struct { a: u8 }` is `repr(C)` with one `IntoBytes` field, so it satisfies
every other condition of the shortcut at `into_bytes.rs:119-123`; it has trailing padding
(`size 2 ≠ 1`), is not `IntoBytes`, and the derive rejects it. -/
theorem ce_one_field_align_gt_1_has_trailing_padding :
    Desc.alignedByte.wf = true ∧ [Desc.u8].length ≤ 1 ∧ SemIntoBytes Desc.u8 ∧
    (ReprModifier.aligned 2).isAlignGt1 = true ∧
    Desc.alignedByte.size ≠ Desc.fieldSizeSum [.u8] ∧
    ¬ SemIntoBytes Desc.alignedByte ∧
    structPaddingOK (.c (.aligned 2)) [.u8] = false :=
  ⟨by decide, by decide, semIntoBytes_int _, by decide, by decide, not_semIntoBytes_alignedByte,
    by decide⟩

/-- **Tightness of `hwf` in R2d.** A `repr(transparent)` "struct" with two non-ZST fields (rejected
by the compiler, so not well-formed) passes the padding analysis but has padding. -/
theorem ce_structPaddingOK_drop_wf :
    (Desc.strct .transparent [.u8, .u16]).wf = false ∧
    structPaddingOK .transparent [.u8, .u16] = true ∧
    (Desc.strct .transparent [.u8, .u16]).size ≠ Desc.fieldSizeSum [.u8, .u16] := by
  decide

/-- **Tightness of `hwf` in R2d (non-power-of-two `packed`).** `repr(C, packed(3))` (rejected by
the compiler) with one `u32` field passes the one-field shortcut but has trailing padding. -/
theorem ce_structPaddingOK_drop_wf_packed3 :
    (Desc.strct (.c (.packed 3)) [.u32]).wf = false ∧
    structPaddingOK (.c (.packed 3)) [.u32] = true ∧
    (Desc.strct (.c (.packed 3)) [.u32]).size ≠ Desc.fieldSizeSum [.u32] := by
  decide

/-- **Tightness of the field conjunct of R2c.** `#[repr(C)] struct { x: Inner }` where `Inner` is
the padded pair: no top-level padding, inhabited field, but the field (hence the struct) is not
`IntoBytes`. -/
theorem ce_struct_drop_fields_intoBytes :
    let S : Desc := .strct (.c .none) [Desc.paddedPair]
    S.size = Desc.fieldSizeSum [Desc.paddedPair] ∧ (∀ f ∈ [Desc.paddedPair], f.Inhabited) ∧
    ¬ (∀ f ∈ [Desc.paddedPair], SemIntoBytes f) ∧ ¬ SemIntoBytes S := by
  refine ⟨by decide, ?_, fun h => not_semIntoBytes_paddedPair (h _ (by simp)), ?_⟩
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact ⟨.strct [.int [0], .int [0, 0]], by decide⟩
  rw [semIntoBytes_iff_encodeL_init]
  intro h
  have := h (.strct [.strct [.int [0], .int [0, 0]]]) (by decide) 1 (by decide)
  revert this
  decide

/-- A padded struct with an uninhabited field (a zero-variant enum, excluded by `Desc.wf`) is
vacuously `IntoBytes` although it has padding. -/
theorem struct_with_uninhabited_field_intoBytes :
    let S : Desc := .strct (.c .none) [.u8, .u16, .enm (.prim .u8) []]
    SemIntoBytes S ∧ S.size ≠ Desc.fieldSizeSum [.u8, .u16, .enm (.prim .u8) []] := by
  refine ⟨?_, by decide⟩
  rw [semIntoBytes_iff_encodeL_init]
  intro v hv
  exfalso
  cases v with
  | strct vs =>
    match vs with
    | [a, b, c] =>
      cases c with
      | enm k fvs => simp [Desc.hasType, Desc.hasTypes, Desc.hasTypeVariant] at hv
      | _ => simp [Desc.hasType, Desc.hasTypes] at hv
    | [] => simp [Desc.hasType, Desc.hasTypes] at hv
    | [_] => simp [Desc.hasType, Desc.hasTypes] at hv
    | [_, _] => simp [Desc.hasType, Desc.hasTypes] at hv
    | _ :: _ :: _ :: _ :: _ => simp [Desc.hasType, Desc.hasTypes] at hv
  | _ => simp [Desc.hasType] at hv

/-- **Tightness of `hInh` in R2c** (canonical form): inhabitedness fails and the characterization
fails (the struct is `IntoBytes` but has padding). -/
theorem ce_struct_intoBytes_iff_drop_inhabited :
    let fs : List Desc := [.u8, .u16, .enm (.prim .u8) []]
    let S : Desc := .strct (.c .none) fs
    ¬ (∀ f ∈ fs, f.Inhabited) ∧
    ¬ (SemIntoBytes S ↔ (∀ f ∈ fs, SemIntoBytes f) ∧ S.size = Desc.fieldSizeSum fs) := by
  refine ⟨fun h => not_inhabited_empty_enum (h _ (by simp)), fun hiff => ?_⟩
  exact struct_with_uninhabited_field_intoBytes.2
    (hiff.mp struct_with_uninhabited_field_intoBytes.1).2

/-- **Tightness of `hwf` in R2d (inner well-formedness).** The outer modifier `packed(2)` is
well-formed, but the field `#[repr(C, align(3))] struct { a: u8 }` is not (non-power-of-two
`align`; the field has size 3 and alignment 3); the one-field shortcut passes, and the struct has
trailing padding: `packed(2)` caps the field's alignment at 2, so the size `3` rounds up to `4`. -/
theorem ce_structPaddingOK_drop_inner_wf :
    let badField : Desc := .strct (.c (.aligned 3)) [.u8]
    (ReprModifier.packed 2).wf = true ∧
    (Desc.strct (.c (.packed 2)) [badField]).wf = false ∧
    structPaddingOK (.c (.packed 2)) [badField] = true ∧
    (Desc.strct (.c (.packed 2)) [badField]).size ≠ Desc.fieldSizeSum [badField] := by
  decide

end Toy.Zc
