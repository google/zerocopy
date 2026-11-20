import ToyZc.NonClaims

/-!
# Result group 2 (closure): soundness of the modeled derives on all well-formed descriptions

The node-level results (R2a–R2d, R3b–R3g, R4b) combine by induction over descriptions into
global soundness statements (R2e): every well-formed description that the modeled derives (and
zerocopy's primitive impls) accept has the corresponding semantic property; `Unaligned` needs no
well-formedness. Separately (R2f), the modeled `is_safe` equals validity on well-formed descriptions
and bytes of the description's size.

On unions, validity (`Desc.decodeL`) is by definition zerocopy's disjunctive rule "some field is
valid" (`zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:292-296`), so R2f's union case
records agreement with that modeled rule, not exactness against Rust's (unsettled) union validity.
The model has no field invariants (`#[zerocopy(invariant)]`) either, so it does not exhibit the
`TryFromBytes`/`IntoBytes` asymmetry documented at `zerocopy/src/lib.rs:1865-1873`.
-/

namespace Toy.Zc

/-! ### Auxiliary lemmas: Boolean list checks -/

theorem allFromZeros_iff : ∀ fs : List Desc, allFromZeros fs = true ↔ ∀ f ∈ fs, implFromZeros f = true
  | [] => by simp [allFromZeros]
  | f :: fs => by simp [allFromZeros, allFromZeros_iff fs]

theorem allFromBytes_iff : ∀ fs : List Desc, allFromBytes fs = true ↔ ∀ f ∈ fs, implFromBytes f = true
  | [] => by simp [allFromBytes]
  | f :: fs => by simp [allFromBytes, allFromBytes_iff fs]

theorem allIntoBytes_iff (cfg : DeriveConfig) : ∀ fs : List Desc,
    allIntoBytes cfg fs = true ↔ ∀ f ∈ fs, implIntoBytes cfg f = true
  | [] => by simp [allIntoBytes]
  | f :: fs => by simp [allIntoBytes, allIntoBytes_iff cfg fs]

theorem allUnaligned_iff : ∀ fs : List Desc, allUnaligned fs = true ↔ ∀ f ∈ fs, implUnaligned f = true
  | [] => by simp [allUnaligned]
  | f :: fs => by simp [allUnaligned, allUnaligned_iff fs]

theorem variantsFromBytes_iff : ∀ vs : List (DiscrSyn × List Desc),
    variantsFromBytes vs = true ↔ ∀ v ∈ vs, ∀ f ∈ v.2, implFromBytes f = true
  | [] => by simp [variantsFromBytes]
  | (d, fs) :: vs => by simp [variantsFromBytes, variantsFromBytes_iff vs, allFromBytes_iff]

theorem variantsIntoBytes_iff (cfg : DeriveConfig) : ∀ vs : List (DiscrSyn × List Desc),
    variantsIntoBytes cfg vs = true ↔ ∀ v ∈ vs, ∀ f ∈ v.2, implIntoBytes cfg f = true
  | [] => by simp [variantsIntoBytes]
  | (d, fs) :: vs => by simp [variantsIntoBytes, variantsIntoBytes_iff cfg vs, allIntoBytes_iff]

theorem variantsUnaligned_iff : ∀ vs : List (DiscrSyn × List Desc),
    variantsUnaligned vs = true ↔ ∀ v ∈ vs, ∀ f ∈ v.2, implUnaligned f = true
  | [] => by simp [variantsUnaligned]
  | (d, fs) :: vs => by simp [variantsUnaligned, variantsUnaligned_iff vs, allUnaligned_iff]

theorem variantFromZeros_spec : ∀ (vs : List (DiscrSyn × List Desc)) (i : Nat),
    variantFromZeros vs i = true → ∀ fs, variantFields vs i = some fs → ∀ f ∈ fs, implFromZeros f = true
  | [], _, h => by simp [variantFromZeros] at h
  | (d, fs) :: vs, 0, h => by
    intro fs' hfs'
    simp only [variantFields, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hfs'
    subst hfs'
    exact (allFromZeros_iff _).mp h
  | (d, fs) :: vs, i + 1, h => by
    intro fs' hfs'
    simp only [variantFields, List.getElem?_cons_succ] at hfs'
    exact variantFromZeros_spec vs i h fs' hfs'

/-! ### Auxiliary lemmas: arrays -/

theorem slice_length_of_lt (bs : List Byte) (n s k : Nat) (hlen : bs.length = n * s) (hk : k < n) :
    (slice bs (k * s) s).length = s := by
  have : (k + 1) * s ≤ n * s := Nat.mul_le_mul_right s hk
  rw [Nat.succ_mul] at this
  simp only [slice, List.length_take, List.length_drop]
  omega

theorem array_validInit_iff (e : Desc) (n : Nat) (bs : List Byte) :
    validInit (.array e n) bs = true ↔
      bs.length = n * e.size ∧ ∀ k, k < n → validInit e (slice bs (k * e.size) e.size) = true := by
  rw [validInit_eq_isSome]
  simp only [Desc.decodeL, List.length_map]
  have hs : (Desc.array e n).size = n * e.size := rfl
  by_cases hl : bs.length = n * e.size
  · simp only [hl, ↓reduceIte, Option.isSome_map, true_and]
    rw [mapM_option_isSome]
    simp only [List.mem_range, slice_map_init, validInit_eq_isSome]
  · simp [hl]

theorem semFromBytes_array (e : Desc) (n : Nat) (h : SemFromBytes e) : SemFromBytes (.array e n) := by
  rw [semFromBytes_iff_validInit_total] at h ⊢
  intro bs hbs
  have hbs' : bs.length = n * e.size := hbs
  refine (array_validInit_iff e n bs).mpr ⟨hbs', fun k hk => h _ ?_⟩
  exact slice_length_of_lt bs n e.size k hbs' hk

theorem semFromZeros_array (e : Desc) (n : Nat) (h : SemFromZeros e) : SemFromZeros (.array e n) := by
  rw [semFromZeros_iff_validInit_zeros] at h ⊢
  refine (array_validInit_iff e n _).mpr ⟨by simp; rfl, fun k hk => ?_⟩
  have : (k + 1) * e.size ≤ n * e.size := Nat.mul_le_mul_right e.size hk
  rw [Nat.succ_mul] at this
  have hsl : slice (List.replicate (Desc.array e n).size (0 : Byte)) (k * e.size) e.size =
      List.replicate e.size 0 := by
    have hs : (Desc.array e n).size = n * e.size := rfl
    simp only [slice, List.drop_replicate, List.take_replicate, hs]
    congr 1
    omega
  rw [hsl]
  exact h

theorem flatMap_encodeL_length (e : Desc) : ∀ vs : List Val,
    (vs.flatMap fun v => e.encodeL v).length = vs.length * e.size
  | [] => by simp
  | v :: vs => by
    rw [List.flatMap_cons, List.length_append, encodeL_length, flatMap_encodeL_length e vs,
      List.length_cons, Nat.succ_mul]
    omega

theorem semIntoBytes_array (e : Desc) (n : Nat) (h : SemIntoBytes e) : SemIntoBytes (.array e n) := by
  rw [semIntoBytes_iff_encodeL_init]
  intro v hv i hi
  cases v with
  | array vs =>
    simp only [Desc.hasType, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hv
    have hlen : (vs.flatMap fun v => e.encodeL v).length = n * e.size := by
      rw [flatMap_encodeL_length, hv.1]
    simp only [Desc.encodeL]
    rw [fit_of_length hlen]
    have hi' : i < (vs.flatMap fun v => e.encodeL v).length := by rw [hlen]; exact hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    have hmem := List.getElem_mem hi'
    rw [List.mem_flatMap] at hmem
    obtain ⟨w, hw, hb⟩ := hmem
    exact encodeL_forall_isInit h (hv.2 w hw) _ hb
  | _ => simp [Desc.hasType] at hv

/-! ### Auxiliary lemmas: unions and cells -/

theorem decodeField_isSome_iff : ∀ (fs : List Desc) (j : Nat) (x : List AB),
    (Desc.decodeField fs j x).isSome = true ↔ ∃ f ∈ fs, (f.decodeL (x.take f.size)).isSome = true
  | [], _, _ => by simp [Desc.decodeField]
  | f :: fs, j, x => by
    simp only [Desc.decodeField, List.mem_cons, exists_eq_or_imp]
    cases hf : f.decodeL (x.take f.size) with
    | some v => simp
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_or]
      exact decodeField_isSome_iff fs (j + 1) x

theorem union_validInit_iff (r : UnionRepr) (fs : List Desc) (bs : List Byte) :
    validInit (.union r fs) bs = true ↔
      bs.length = (Desc.union r fs).size ∧ ∃ f ∈ fs, validInit f (bs.take f.size) = true := by
  rw [validInit_eq_isSome]
  simp only [Desc.decodeL, List.length_map]
  have hs : (Desc.union r fs).size = (Toy.Zc.unionLayout r.modifier (Desc.layouts fs)).size := rfl
  rw [hs]
  by_cases hl : bs.length = (Toy.Zc.unionLayout r.modifier (Desc.layouts fs)).size
  · simp only [hl, ↓reduceIte, true_and]
    rw [decodeField_isSome_iff]
    simp only [validInit_eq_isSome, List.map_take]
  · simp [hl]

theorem semFromBytes_union_cons (r : UnionRepr) (f : Desc) (fs : List Desc) (h : SemFromBytes f) :
    SemFromBytes (.union r (f :: fs)) := by
  rw [semFromBytes_iff_validInit_total] at h ⊢
  intro bs hbs
  have hle := field_size_le_union_size r (f :: fs) f List.mem_cons_self
  refine (union_validInit_iff r _ bs).mpr ⟨hbs, f, List.mem_cons_self, h _ ?_⟩
  simp only [List.length_take]
  omega

theorem semFromZeros_union_cons (r : UnionRepr) (f : Desc) (fs : List Desc) (h : SemFromZeros f) :
    SemFromZeros (.union r (f :: fs)) := by
  rw [semFromZeros_iff_validInit_zeros] at h ⊢
  have hle := field_size_le_union_size r (f :: fs) f List.mem_cons_self
  refine (union_validInit_iff r _ _).mpr ⟨by simp, f, List.mem_cons_self, ?_⟩
  rw [List.take_replicate, Nat.min_eq_left hle]
  exact h

theorem cell_validInit (t : Desc) (bs : List Byte) : validInit (.cell t) bs = validInit t bs := by
  simp [validInit, Desc.decodeL, Desc.hasType]

theorem semFromBytes_cell (t : Desc) : SemFromBytes (.cell t) ↔ SemFromBytes t := by
  rw [semFromBytes_iff_validInit_total, semFromBytes_iff_validInit_total]
  simp only [cell_validInit]
  rfl

theorem semFromZeros_cell (t : Desc) : SemFromZeros (.cell t) ↔ SemFromZeros t := by
  rw [semFromZeros_iff_validInit_zeros, semFromZeros_iff_validInit_zeros, cell_validInit]
  rfl

theorem semIntoBytes_cell (t : Desc) : SemIntoBytes (.cell t) ↔ SemIntoBytes t := by
  rw [semIntoBytes_iff_encodeL_init, semIntoBytes_iff_encodeL_init]
  simp only [Desc.hasType, Desc.encodeL]
  rfl

/-! ### Auxiliary lemmas: alignment bounds for `Unaligned` -/

theorem foldl_max_eq_one {α : Type} (g : α → Nat) (l : List α) (h : ∀ x ∈ l, g x ≤ 1) :
    l.foldl (fun acc x => max acc (g x)) 1 = 1 := by
  have h1 := foldl_max_ge_init g l 1
  have h2 := foldl_max_prop g (· ≤ 1) (fun a b ha hb => by omega) l 1 (Nat.le_refl _) h
  omega

theorem structAlign_eq_one (m : ReprModifier) (ls : List FieldLayout) (hm : m.isAlignGt1 = false)
    (h : m.isPacked1 = true ∨ ∀ l ∈ ls, l.align = 1) : structAlign m ls = 1 := by
  have hf : fieldsMaxAlign m ls = 1 := by
    unfold fieldsMaxAlign
    apply foldl_max_eq_one
    intro l hl
    rcases h with h | h
    · cases m with
      | packed p =>
        match p, h with
        | 1, _ => exact Nat.min_le_right _ _
      | _ => simp [ReprModifier.isPacked1] at h
    · rw [h l hl]
      cases m with
      | packed p => exact Nat.min_le_left _ _
      | none => exact Nat.le_refl _
      | aligned n => exact Nat.le_refl _
  unfold structAlign
  cases m with
  | aligned n =>
    simp only [ReprModifier.isAlignGt1, decide_eq_false_iff_not, Nat.not_lt] at hm
    rw [hf]; exact Nat.max_eq_left hm
  | none => exact hf
  | packed p => exact hf

theorem unionLayout_align_eq_one (m : ReprModifier) (ls : List FieldLayout) (hm : m.isAlignGt1 = false)
    (h : m.isPacked1 = true ∨ ∀ l ∈ ls, l.align = 1) : (unionLayout m ls).align = 1 := by
  have hs := structAlign_eq_one m ls hm h
  unfold structAlign fieldsMaxAlign at hs
  unfold unionLayout
  cases m <;> exact hs

theorem layouts_align_one (fs : List Desc) (h : ∀ f ∈ fs, f.align = 1) :
    ∀ l ∈ Desc.layouts fs, l.align = 1 := by
  intro l hl
  rw [Desc.layouts_eq_map] at hl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hl
  exact h f hf


theorem isSafeUnion_iff : ∀ (fs : List Desc) (bs : List Byte),
    isSafeUnion fs bs = true ↔ ∃ f ∈ fs, isSafe f (bs.take f.size) = true
  | [], _ => by simp [isSafeUnion]
  | f :: fs, bs => by simp [isSafeUnion, isSafeUnion_iff fs bs]

/-- **R2e (FromZeros).** Every well-formed description accepted by the modeled `FromZeros` derive
is semantically `FromZeros`. -/
theorem derive_fromZeros_sound_of_wf (d : Desc) (hwf : d.wf = true) (h : implFromZeros d = true) :
    SemFromZeros d := by
  revert hwf h
  refine Desc.induct' (fun d => d.wf = true → implFromZeros d = true → SemFromZeros d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ d
  · intro t _ _; exact semFromZeros_int t
  · intro _ _; exact semFromZeros_bool
  · intro e n ih hwf h
    exact semFromZeros_array e n (ih hwf h)
  · intro r fs ih hwf h
    have hwfs : ∀ f ∈ fs, f.wf = true := by
      cases r with
      | c m =>
        simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf; exact hwf.2
      | transparent =>
        simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf; exact hwf.1
    simp only [implFromZeros, allFromZeros_iff] at h
    exact (struct_fromZeros_iff_fields_fromZeros r fs).mpr (fun f hf => ih f hf (hwfs f hf) (h f hf))
  · intro r vs ih hwf h
    simp only [Desc.wf, Bool.and_eq_true, wfVariants_iff] at hwf
    simp only [implFromZeros] at h
    split at h
    · rename_i i hz
      refine enum_fromZeros_of_findZeroVariant r vs hwf.2 i hz (fun fs hfs f hf => ?_)
      have hfs' := hfs
      simp only [variantFields, Option.map_eq_some_iff] at hfs'
      obtain ⟨⟨a, fs'⟩, hget, rfl⟩ := hfs'
      have hmem := List.mem_of_getElem? hget
      exact ih _ hmem f hf (hwf.1.2 _ hmem f hf) (variantFromZeros_spec vs i h _ hfs f hf)
    · cases h
  · intro r fs ih hwf h
    cases r with
    | c m =>
      simp only [Desc.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, wfAll_iff,
        List.isEmpty_eq_false_iff] at hwf
      simp only [implFromZeros, allFromZeros_iff] at h
      match fs, hwf, ih, h with
      | f :: fs, hwf, ih, h =>
        exact semFromZeros_union_cons _ f fs (ih f List.mem_cons_self (hwf.2 f List.mem_cons_self)
          (h f List.mem_cons_self))
  · intro t ih hwf h
    exact (semFromZeros_cell t).mpr (ih hwf h)

/-- **R2e (FromBytes).** Every well-formed description accepted by the modeled `FromBytes` derive
is semantically `FromBytes`. -/
theorem derive_fromBytes_sound_of_wf (d : Desc) (hwf : d.wf = true) (h : implFromBytes d = true) :
    SemFromBytes d := by
  revert hwf h
  refine Desc.induct' (fun d => d.wf = true → implFromBytes d = true → SemFromBytes d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ d
  · intro t _ _; exact semFromBytes_int t
  · intro _ h; simp [implFromBytes] at h
  · intro e n ih hwf h
    exact semFromBytes_array e n (ih hwf h)
  · intro r fs ih hwf h
    have hwfs : ∀ f ∈ fs, f.wf = true := by
      cases r with
      | c m =>
        simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf; exact hwf.2
      | transparent =>
        simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf; exact hwf.1
    simp only [implFromBytes, Bool.and_eq_true, allFromBytes_iff] at h
    exact (struct_fromBytes_iff_fields_fromBytes r fs).mpr
      (fun f hf => ih f hf (hwfs f hf) (h.2 f hf))
  · intro r vs ih hwf h
    simp only [Desc.wf, Bool.and_eq_true, wfVariants_iff] at hwf
    simp only [implFromBytes, Bool.and_eq_true, variantsFromBytes_iff] at h
    exact enum_fromBytes_of_count_check r vs hwf.2 h.1.2
      (fun v hv f hf => ih v hv f hf (hwf.1.2 v hv f hf) (h.2 v hv f hf))
  · intro r fs ih hwf h
    cases r with
    | c m =>
      simp only [Desc.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, wfAll_iff,
        List.isEmpty_eq_false_iff] at hwf
      simp only [implFromBytes, Bool.and_eq_true, allFromBytes_iff] at h
      match fs, hwf, ih, h with
      | f :: fs, hwf, ih, h =>
        exact semFromBytes_union_cons _ f fs (ih f List.mem_cons_self (hwf.2 f List.mem_cons_self)
          (h.2 f List.mem_cons_self))
  · intro t ih hwf h
    exact (semFromBytes_cell t).mpr (ih hwf h)

/-- **R2e (IntoBytes).** Every well-formed description accepted by the modeled `IntoBytes` derive
(in any configuration) is semantically `IntoBytes`. -/
theorem derive_intoBytes_sound_of_wf (cfg : DeriveConfig) (d : Desc) (hwf : d.wf = true)
    (h : implIntoBytes cfg d = true) : SemIntoBytes d := by
  revert hwf h
  refine Desc.induct' (fun d => d.wf = true → implIntoBytes cfg d = true → SemIntoBytes d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ d
  · intro t _ _; exact semIntoBytes_int t
  · intro _ _; exact semIntoBytes_bool
  · intro e n ih hwf h
    exact semIntoBytes_array e n (ih hwf h)
  · intro r fs ih hwf h
    have hwfs : ∀ f ∈ fs, f.wf = true := by
      cases r with
      | c m =>
        simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf; exact hwf.2
      | transparent =>
        simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf; exact hwf.1
    simp only [implIntoBytes, Bool.and_eq_true, allIntoBytes_iff] at h
    exact struct_intoBytes_of_fields_of_no_padding r fs (fun f hf => ih f hf (hwfs f hf) (h.1 f hf))
      (structPaddingOK_sound r fs hwf h.2)
  · intro r vs ih hwf h
    simp only [Desc.wf, Bool.and_eq_true, wfVariants_iff] at hwf
    simp only [implIntoBytes, Bool.and_eq_true, variantsIntoBytes_iff] at h
    exact enum_intoBytes_of_fields_of_padding_check r vs
      (fun v hv f hf => ih v hv f hf (hwf.1.2 v hv f hf) (h.1 v hv f hf)) h.2
  · intro r fs ih hwf h
    cases r with
    | c m =>
      simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf
      simp only [implIntoBytes, Bool.and_eq_true, allIntoBytes_iff] at h
      exact union_intoBytes_of_fields_of_padding_check _ fs
        (fun f hf => ih f hf (hwf.2 f hf) (h.1.2 f hf)) h.2
  · intro t ih hwf h
    exact (semIntoBytes_cell t).mpr (ih hwf h)

/-- **R2e (Unaligned).** Every description accepted by the modeled `Unaligned` derive has
alignment `1`. -/
theorem derive_unaligned_sound (d : Desc) (h : implUnaligned d = true) : SemUnaligned d := by
  unfold SemUnaligned
  revert h
  refine Desc.induct' (fun d => implUnaligned d = true → d.align = 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ d
  · intro t h
    cases t <;> simp [implUnaligned] at h <;> rfl
  · intro _; rfl
  · intro e n ih h; exact ih h
  · intro r fs ih h
    show (r.layout (Desc.layouts fs)).align = 1
    cases r with
    | c m =>
      simp only [implUnaligned, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.or_eq_true, allUnaligned_iff] at h
      refine structAlign_eq_one m _ h.1 ?_
      rcases h.2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (layouts_align_one fs (fun f hf => ih f hf (h2 f hf)))
    | transparent =>
      simp only [implUnaligned, allUnaligned_iff] at h
      exact structAlign_eq_one .none _ rfl
        (Or.inr (layouts_align_one fs (fun f hf => ih f hf (h f hf))))
  · intro r vs ih h
    simp only [implUnaligned, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      variantsUnaligned_iff] at h
    show (r.layout (Desc.variantLayouts vs)).align = 1
    have hu : ∀ t, r = .prim t → t.width = 1 →
        (reprIntEnum (EnumRepr.prim t).tagLayout (Desc.variantLayouts vs)).align = 1 := by
      intro t _ ht
      simp only [reprIntEnum]
      apply foldl_max_eq_one
      intro l hl
      simp only [List.map_map, List.mem_map, Function.comp] at hl
      obtain ⟨vl, hvl, rfl⟩ := hl
      apply Nat.le_of_eq
      refine structAlign_eq_one .none _ rfl (Or.inr ?_)
      intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact ht
      · rw [variantLayouts_eq_map] at hvl
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hvl
        exact layouts_align_one v.2 (fun f hf => ih v hv f hf (h.2 v hv f hf)) l hl
    rcases h.1 with rfl | rfl
    · exact hu .u8 rfl rfl
    · exact hu .i8 rfl rfl
  · intro r fs ih h
    cases r with
    | c m =>
      simp only [implUnaligned, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.or_eq_true, allUnaligned_iff] at h
      refine unionLayout_align_eq_one m _ h.1 ?_
      rcases h.2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (layouts_align_one fs (fun f hf => ih f hf (h2 f hf)))
  · intro t ih h; exact ih h

/-- **R2f (TryFromBytes).** On every well-formed description, the modeled `is_safe` equals the
validity check on bytes of the description's size. -/
theorem derive_isSafe_eq_validInit_of_wf_of_length (d : Desc) (hwf : d.wf = true) (bs : List Byte)
    (hlen : bs.length = d.size) : isSafe d bs = validInit d bs := by
  revert hwf bs
  refine Desc.induct'
    (fun d => d.wf = true → ∀ bs : List Byte, bs.length = d.size → isSafe d bs = validInit d bs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ d
  · intro t _ bs hlen
    rw [validInit_int]
    have : bs.length = t.width := hlen
    simp [isSafe, this]
  · intro _ bs hlen
    exact isSafe_eq_validInit_bool bs hlen
  · intro e n ih hwf bs hlen
    have hlen' : bs.length = n * e.size := hlen
    apply Bool.eq_iff_iff.mpr
    rw [array_validInit_iff]
    simp only [isSafe, List.all_eq_true, List.mem_range]
    constructor
    · intro h
      refine ⟨hlen', fun k hk => ?_⟩
      rw [← ih hwf _ (slice_length_of_lt bs n e.size k hlen' hk)]
      exact h k hk
    · intro h k hk
      rw [ih hwf _ (slice_length_of_lt bs n e.size k hlen' hk)]
      exact h.2 k hk
  · intro r fs ih hwf bs hlen
    have hwfs : ∀ f ∈ fs, f.wf = true := by
      cases r with
      | c m =>
        simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf; exact hwf.2
      | transparent =>
        simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf; exact hwf.1
    obtain ⟨m, hm⟩ := structRepr_layout_eq r
    have hend := strct_end_le_size r fs m hm
    have hoffs : (Desc.structLayout r fs).offsets = (placeFields m 0 (Desc.layouts fs)).1 := by
      unfold Desc.structLayout; rw [hm]; rfl
    have hfit : fitsIn fs (placeFields m 0 (Desc.layouts fs)).1 bs.length := by
      have := fitsIn_placeFields m 0 bs.length fs 0 (by omega)
      simpa using this
    simp only [isSafe]
    rw [hoffs, isSafeFields_eq_validFields fs _ bs hfit
      (fun f hf bs' hbs' => ih f hf (hwfs f hf) bs' hbs'), validFields_eq_isSome,
      validInit_eq_isSome, strct_decodeL_isSome r fs m hm]
    simp [hlen]
  · intro r vs ih hwf bs hlen
    simp only [Desc.wf, Bool.and_eq_true, wfVariants_iff] at hwf
    exact isSafe_enm_eq_validInit r vs hwf.2
      (fun v hv f hf bs' hbs' => ih v hv f hf (hwf.1.2 v hv f hf) bs' hbs') bs hlen
  · intro r fs ih hwf bs hlen
    cases r with
    | c m =>
      simp only [Desc.wf, Bool.and_eq_true, wfAll_iff] at hwf
      apply Bool.eq_iff_iff.mpr
      simp only [isSafe]
      rw [isSafeUnion_iff, union_validInit_iff]
      have htake : ∀ f ∈ fs, (bs.take f.size).length = f.size := by
        intro f hf
        have := field_size_le_union_size (.c m) fs f hf
        simp only [List.length_take]
        omega
      constructor
      · rintro ⟨f, hf, h⟩
        refine ⟨hlen, f, hf, ?_⟩
        rw [← ih f hf (hwf.2 f hf) _ (htake f hf)]
        exact h
      · rintro ⟨_, f, hf, h⟩
        refine ⟨f, hf, ?_⟩
        rw [ih f hf (hwf.2 f hf) _ (htake f hf)]
        exact h
  · intro t ih hwf bs hlen
    rw [cell_validInit]
    simp only [isSafe]
    exact ih hwf bs hlen

/-! ## Non-vacuity -/

/-- Non-vacuity of R2e: well-formed descriptions accepted by each modeled derive. -/
theorem nv_derive_sound :
    Desc.paddedPair.wf = true ∧ implFromZeros Desc.paddedPair = true ∧
      implFromBytes Desc.paddedPair = true ∧
    Desc.fullTriple.wf = true ∧ implIntoBytes cfgDefault Desc.fullTriple = true ∧
    implUnaligned (.strct (.c (.packed 1)) [.u8, .u16]) = true := by
  decide

/-- Non-vacuity of R2f: a well-formed two-byte enum and a byte list of its size. -/
theorem nv_derive_isSafe :
    (Desc.enm (.prim .u8) [(.implicit, [.u8]), (.lit 5, [.bool])]).wf = true ∧
      ([5, 1] : List Byte).length =
        (Desc.enm (.prim .u8) [(.implicit, [.u8]), (.lit 5, [.bool])]).size := by
  decide

/-! ## Counterexamples (canonical form) -/

/-- **Tightness of `hwf` (FromBytes).** The field-less union `union {}` (rejected by the compiler)
passes the modeled check vacuously, but no byte vector decodes. -/
theorem ce_derive_fromBytes_drop_wf :
    (Desc.union (.c .none) []).wf = false ∧ implFromBytes (.union (.c .none) []) = true ∧
    ¬ SemFromBytes (.union (.c .none) []) := by
  refine ⟨by decide, by decide, ?_⟩
  rw [semFromBytes_iff_validInit_total]
  intro h
  have := h [] rfl
  revert this
  decide

/-- **Tightness of `hwf` (FromZeros).** See `ce_enum_fromZeros_iff_drop_wf`: a duplicate zero
discriminant, the first written as a non-literal expression. -/
theorem ce_derive_fromZeros_drop_wf :
    let E : Desc := .enm (.prim .u8) dupZeroNonLiteral
    E.wf = false ∧ implFromZeros E = true ∧ ¬ SemFromZeros E :=
  ⟨by decide, by decide, not_semFromZeros_dupZeroNonLiteral⟩

/-- **Tightness of `hwf` (IntoBytes).** A `repr(transparent)` "struct" with two non-ZST fields
(rejected by the compiler) passes the modeled check but has padding. -/
theorem ce_derive_intoBytes_drop_wf :
    (Desc.strct .transparent [.u8, .u16]).wf = false ∧
    implIntoBytes cfgDefault (.strct .transparent [.u8, .u16]) = true ∧
    ¬ SemIntoBytes (.strct .transparent [.u8, .u16]) := by
  refine ⟨by decide, by decide, ?_⟩
  rw [semIntoBytes_iff_encodeL_init]
  intro h
  have := h (.strct [.int [0], .int [0, 0]]) (by decide) 1 (by decide)
  revert this
  decide

set_option maxRecDepth 100000 in
/-- **Tightness of `hwf` in R2f.** See `ce_isSafe_enm_drop_wf`: the bytes have the right length,
the description is not well-formed, and `is_safe` disagrees with validity. -/
theorem ce_derive_isSafe_drop_wf :
    (Desc.enm (.prim .u8) dupZeroVariants).wf = false ∧
    ([1] : List Byte).length = (Desc.enm (.prim .u8) dupZeroVariants).size ∧
    isSafe (.enm (.prim .u8) dupZeroVariants) [1] ≠ validInit (.enm (.prim .u8) dupZeroVariants) [1] := by
  decide

/-- **Tightness of `hlen` in R2f.** `u8` is well-formed; on the empty byte list (wrong length) the
primitive `is_safe` (no validator for integers) returns `true` while validity is `false`. -/
theorem ce_derive_isSafe_drop_hlen :
    Desc.u8.wf = true ∧ ([] : List Byte).length ≠ Desc.u8.size ∧
    isSafe .u8 [] ≠ validInit .u8 [] := by
  decide

/-- **Tightness of the checks.** Well-formed descriptions rejected by each check that lack the
property: `bool` (not `FromBytes`), the enum without a zero discriminant (not `FromZeros`), the
padded pair (not `IntoBytes`, not `Unaligned`). -/
theorem ce_derive_drop_check :
    Desc.bool.wf = true ∧ implFromBytes .bool = false ∧ ¬ SemFromBytes .bool ∧
    Desc.noZero.wf = true ∧ implFromZeros Desc.noZero = false ∧ ¬ SemFromZeros Desc.noZero ∧
    Desc.paddedPair.wf = true ∧ implIntoBytes cfgUnion Desc.paddedPair = false ∧
      ¬ SemIntoBytes Desc.paddedPair ∧
    implUnaligned Desc.paddedPair = false ∧ ¬ SemUnaligned Desc.paddedPair :=
  ⟨by decide, by decide, not_semFromBytes_bool, by decide, by decide, not_semFromZeros_noZero,
    by decide, by decide, not_semIntoBytes_paddedPair, by decide, ex_semUnaligned_neg⟩

end Toy.Zc
