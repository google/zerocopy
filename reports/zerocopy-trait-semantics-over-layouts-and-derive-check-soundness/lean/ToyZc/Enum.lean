import ToyZc.Struct

/-!
# Result group 3: enum derives

* `fieldless_enum_fromBytes_iff_every_tag_is_discriminant` (R3a): a fieldless `repr(Int)` enum
  is `FromBytes` iff every one of the `2^(8·size)` tag values is the code of some discriminant.
* `enum_variant_count_check_sound` (R3b): under the compiler's discriminant rules (distinct,
  representable), the derive's count check `variants.len() == 2^bits` implies that every tag value
  is a discriminant.
* `enum_fromBytes_of_count_check` (R3c): data-carrying case: with `FromBytes` fields, the count
  check implies `FromBytes`.
* `enum_fromZeros_iff_zero_variant_fields_fromZeros_of_discrsWF` (R3d): under the discriminant rules, an enum is
  `FromZeros` iff some variant has discriminant `0` and its fields are `FromZeros`.
* `findZeroVariant_sound` / `findZeroVariant_complete_of_no_unknown` (R3e): the derive's syntactic
  zero-variant search is sound, and complete when every discriminant is an (optionally negated)
  literal or implicit.
* `enum_validInit_iff_first_matching_variant_valid` and `isSafe_enm_eq_validInit` (R3f):
  `TryFromBytes` validity of an enum is "the tag matches a discriminant, and that variant's fields
  are valid", and the derived `is_safe` computes exactly this predicate.
* `enum_intoBytes_of_fields_of_padding_check` (R3g): every field `IntoBytes` plus the derive's
  `enum_padding! == 0` check implies `IntoBytes`.
-/

namespace Toy.Zc

/-! ## Auxiliary predicates -/

/-- Every variant has no fields. -/
def Desc.Fieldless (vs : List (DiscrSyn × List Desc)) : Prop := ∀ v ∈ vs, v.2 = []

/-- The tag value of initialized enum bytes `bs` (little-endian, unsigned). -/
def enumTag (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) (bs : List Byte) : Nat :=
  leNat (slice bs (Desc.enumLayout r vs).tagOffset r.tagTy.width)

/-- Conjunction of the fields' validity on their byte ranges. -/
def validFields : List Desc → List Nat → List Byte → Bool
  | [], _, _ => true
  | f :: fs, o :: os, bs => validInit f (slice bs o f.size) && validFields fs os bs
  | _ :: _, [], _ => false

/-- Validity of the fields of variant `i` at their offsets. -/
def validVariant : List (DiscrSyn × List Desc) → Nat → List (List Nat) → List Byte → Bool
  | (_, fs) :: _, 0, os :: _, bs => validFields fs os bs
  | _ :: vs, i + 1, _ :: oss, bs => validVariant vs i oss bs
  | _, _, _, _ => false

/-- The fields of variant `i`, if it exists. -/
def variantFields (vs : List (DiscrSyn × List Desc)) (i : Nat) : Option (List Desc) :=
  vs[i]?.map Prod.snd

theorem ex_enumTag_pos : enumTag (.prim .u16) [(.implicit, [])] [1, 2] = 513 := rfl
theorem ex_validVariant_pos :
    validVariant [(.implicit, [.bool])] 0 [[1]] [0, 1] = true := by decide
theorem ex_validVariant_neg :
    validVariant [(.implicit, [.bool])] 0 [[1]] [0, 2] = false := by decide
theorem ex_Fieldless_pos : Desc.Fieldless [(.implicit, []), (.lit 5, [])] := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> rfl
theorem ex_Fieldless_neg : ¬ Desc.Fieldless [(.implicit, []), (.lit 5, [Desc.u8])] := by
  intro h
  have := h (.lit 5, [Desc.u8]) (by simp)
  cases this

/-! ## Auxiliary lemmas: the invariants of `find_zero_variant` -/

theorem findZeroVariantAux_sound : ∀ (ds : List DiscrSyn) (i : Nat) (next : Option Nat)
    (unk : Bool) (nxt : Int) (j : Nat), (∀ n, next = some n → nxt = -(n : Int)) →
    findZeroVariantAux ds i next unk = .ok j → i ≤ j ∧ (resolveAux ds nxt)[j - i]? = some 0
  | [], i, next, unk, nxt, j, _, h => by simp [findZeroVariantAux] at h
  | d :: ds, i, next, unk, nxt, j, hinv, h => by
    have step : ∀ (v : Int) (next' : Option Nat) (unk' : Bool),
        (∀ n, next' = some n → v + 1 = -(n : Int)) →
        findZeroVariantAux ds (i + 1) next' unk' = .ok j →
        i ≤ j ∧ (v :: resolveAux ds (v + 1))[j - i]? = some 0 := by
      intro v next' unk' hinv' h'
      obtain ⟨h1, h2⟩ := findZeroVariantAux_sound ds (i + 1) next' unk' (v + 1) j hinv' h'
      refine ⟨by omega, ?_⟩
      have : j - i = (j - (i + 1)) + 1 := by omega
      rw [this]
      simpa using h2
    cases d with
    | implicit =>
      cases next with
      | none =>
        simp only [findZeroVariantAux] at h
        exact step nxt none unk (by simp) h
      | some n =>
        cases n with
        | zero =>
          simp only [findZeroVariantAux, Except.ok.injEq] at h
          subst h
          have := hinv 0 rfl
          simp [resolveAux, this]
        | succ n =>
          simp only [findZeroVariantAux] at h
          refine step nxt (some n) unk ?_ h
          intro m hm
          cases hm
          have := hinv (n + 1) rfl
          push_cast at this
          omega
    | lit k =>
      cases k with
      | zero =>
        simp only [findZeroVariantAux, Except.ok.injEq] at h
        subst h
        simp [resolveAux]
      | succ k =>
        simp only [findZeroVariantAux] at h
        exact step ((k + 1 : Nat) : Int) none unk (by simp) h
    | negLit k =>
      cases k with
      | zero =>
        simp only [findZeroVariantAux, Except.ok.injEq] at h
        subst h
        simp [resolveAux]
      | succ k =>
        simp only [findZeroVariantAux] at h
        refine step (-((k + 1 : Nat) : Int)) (some k) unk ?_ h
        intro m hm
        cases hm
        push_cast
        omega
    | other w =>
      simp only [findZeroVariantAux] at h
      exact step w none true (by simp) h

theorem findZeroVariantAux_unk_true : ∀ (ds : List DiscrSyn) (i : Nat) (next : Option Nat),
    findZeroVariantAux ds i next true ≠ .error false
  | [], i, next => by simp [findZeroVariantAux]
  | d :: ds, i, next => by
    cases d with
    | implicit =>
      cases next with
      | none => simpa [findZeroVariantAux] using findZeroVariantAux_unk_true ds (i + 1) none
      | some n =>
        cases n with
        | zero => simp [findZeroVariantAux]
        | succ n => simpa [findZeroVariantAux] using findZeroVariantAux_unk_true ds (i + 1) (some n)
    | lit k =>
      cases k with
      | zero => simp [findZeroVariantAux]
      | succ k => simpa [findZeroVariantAux] using findZeroVariantAux_unk_true ds (i + 1) none
    | negLit k =>
      cases k with
      | zero => simp [findZeroVariantAux]
      | succ k => simpa [findZeroVariantAux] using findZeroVariantAux_unk_true ds (i + 1) (some k)
    | other w => simpa [findZeroVariantAux] using findZeroVariantAux_unk_true ds (i + 1) none

theorem findZeroVariantAux_complete : ∀ (ds : List DiscrSyn) (i : Nat) (next : Option Nat)
    (unk : Bool) (nxt : Int), (∀ n, next = some n → nxt = -(n : Int)) → (next = none → 0 < nxt) →
    findZeroVariantAux ds i next unk = .error false → 0 ∉ resolveAux ds nxt
  | [], _, _, _, _, _, _, _ => by simp [resolveAux]
  | d :: ds, i, next, unk, nxt, hs, hn, h => by
    cases d with
    | implicit =>
      cases next with
      | none =>
        simp only [findZeroVariantAux] at h
        have hp := hn rfl
        have := findZeroVariantAux_complete ds (i + 1) none unk (nxt + 1) (by simp)
          (fun _ => by omega) h
        simp only [resolveAux, List.mem_cons, not_or]
        exact ⟨by omega, this⟩
      | some n =>
        cases n with
        | zero => simp [findZeroVariantAux] at h
        | succ n =>
          simp only [findZeroVariantAux] at h
          have hv := hs (n + 1) rfl
          push_cast at hv
          have := findZeroVariantAux_complete ds (i + 1) (some n) unk (nxt + 1)
            (by intro m hm; cases hm; omega) (by simp) h
          simp only [resolveAux, List.mem_cons, not_or]
          exact ⟨by omega, this⟩
    | lit k =>
      cases k with
      | zero => simp [findZeroVariantAux] at h
      | succ k =>
        simp only [findZeroVariantAux] at h
        have := findZeroVariantAux_complete ds (i + 1) none unk (((k + 1 : Nat) : Int) + 1)
          (by simp) (fun _ => by omega) h
        simp only [resolveAux, List.mem_cons, not_or]
        exact ⟨by omega, this⟩
    | negLit k =>
      cases k with
      | zero => simp [findZeroVariantAux] at h
      | succ k =>
        simp only [findZeroVariantAux] at h
        have := findZeroVariantAux_complete ds (i + 1) (some k) unk (-((k + 1 : Nat) : Int) + 1)
          (by intro m hm; cases hm; push_cast; omega) (by simp) h
        simp only [resolveAux, List.mem_cons, not_or]
        exact ⟨by omega, this⟩
    | other w =>
      simp only [findZeroVariantAux] at h
      exact absurd h (findZeroVariantAux_unk_true ds (i + 1) none)

/-! ### Auxiliary definitions and lemmas: field offsets that fit in a byte range -/

/-- Every field `fs[k]` placed at `os[k]` ends within the first `N` bytes. -/
def fitsIn : List Desc → List Nat → Nat → Prop
  | [], _, _ => True
  | f :: fs, o :: os, N => o + f.size ≤ N ∧ fitsIn fs os N
  | _ :: _, [], _ => False

/-- Every variant's fields fit (in the sense of `fitsIn`) at the corresponding offsets. -/
def variantsFit : List (DiscrSyn × List Desc) → List (List Nat) → Nat → Prop
  | [], _, _ => True
  | v :: vs, os :: oss, N => fitsIn v.2 os N ∧ variantsFit vs oss N
  | _ :: _, [], _ => False

theorem fitsIn_placeFields (m : ReprModifier) (P N : Nat) : ∀ (fs : List Desc) (c : Nat),
    (placeFields m c (Desc.layouts fs)).2 + P ≤ N →
    fitsIn fs ((placeFields m c (Desc.layouts fs)).1.map (· + P)) N
  | [], _, _ => by simp [fitsIn]
  | f :: fs, c, h => by
    have hfs : f.layout.size = f.size := rfl
    have hend := placeFields_end_ge m (Desc.layouts fs)
      (alignUp c (effFieldAlign m f.layout.align) + f.layout.size)
    rw [layouts_cons, placeFields_cons] at *
    simp only [List.map_cons, fitsIn]
    exact ⟨by omega, fitsIn_placeFields m P N fs _ h⟩

theorem slice_map_init (bs : List Byte) (o n : Nat) :
    slice (bs.map AByte.init) o n = (slice bs o n).map AByte.init := by
  simp [slice, List.map_drop, List.map_take]

theorem decodeFields_isSome_of_fits (S : AB → Prop) : ∀ (fs : List Desc) (os : List Nat)
    (x : List AB), fitsIn fs os x.length → (∀ b ∈ x, S b) →
    (∀ f ∈ fs, ∀ y : List AB, y.length = f.size → (∀ b ∈ y, S b) → (f.decodeL y).isSome = true) →
    (Desc.decodeFields fs os x).isSome = true
  | [], _, _, _, _, _ => by simp [Desc.decodeFields]
  | _ :: _, [], _, h, _, _ => by simp [fitsIn] at h
  | f :: fs, o :: os, x, hfit, hS, hF => by
    simp only [fitsIn] at hfit
    simp only [Desc.decodeFields]
    have h1 : (f.decodeL (slice x o f.size)).isSome = true :=
      hF f List.mem_cons_self _ (by simp [slice]; omega)
        (fun b hb => hS b (List.mem_of_mem_drop (List.mem_of_mem_take hb)))
    have h2 := decodeFields_isSome_of_fits S fs os x hfit.2 hS
      (fun g hg => hF g (List.mem_cons_of_mem _ hg))
    revert h1 h2
    cases f.decodeL (slice x o f.size) <;> cases Desc.decodeFields fs os x <;> simp

theorem decodeFields_field_of_fits : ∀ (fs : List Desc) (os : List Nat) (N : Nat), fitsIn fs os N →
    ∀ f ∈ fs, ∃ o, o + f.size ≤ N ∧
      ∀ x, (Desc.decodeFields fs os x).isSome = true → (f.decodeL (slice x o f.size)).isSome = true
  | [], _, _, _ => fun _ h => nomatch h
  | _ :: _, [], _, h => by simp [fitsIn] at h
  | f :: fs, o :: os, N, hfit => by
    simp only [fitsIn] at hfit
    intro g hg
    cases hg with
    | head =>
      refine ⟨o, hfit.1, fun x hx => ?_⟩
      simp only [Desc.decodeFields] at hx
      revert hx
      cases f.decodeL (slice x o f.size) <;> cases Desc.decodeFields fs os x <;> simp
    | tail _ hg =>
      obtain ⟨o', ho1, ho2⟩ := decodeFields_field_of_fits fs os N hfit.2 g hg
      refine ⟨o', ho1, fun x hx => ho2 x ?_⟩
      simp only [Desc.decodeFields] at hx
      revert hx
      cases f.decodeL (slice x o f.size) <;> cases Desc.decodeFields fs os x <;> simp

theorem validFields_eq_isSome : ∀ (fs : List Desc) (os : List Nat) (bs : List Byte),
    validFields fs os bs = (Desc.decodeFields fs os (bs.map AByte.init)).isSome
  | [], _, _ => by simp [validFields, Desc.decodeFields]
  | _ :: _, [], _ => by simp [validFields, Desc.decodeFields]
  | f :: fs, o :: os, bs => by
    simp only [validFields, Desc.decodeFields]
    rw [validFields_eq_isSome fs os bs, validInit_eq_isSome, ← slice_map_init]
    cases f.decodeL (slice (bs.map AByte.init) o f.size) <;>
      cases Desc.decodeFields fs os (bs.map AByte.init) <;> simp

theorem isSafeFields_eq_validFields : ∀ (fs : List Desc) (os : List Nat) (bs : List Byte),
    fitsIn fs os bs.length →
    (∀ f ∈ fs, ∀ bs', bs'.length = f.size → isSafe f bs' = validInit f bs') →
    isSafeFields fs os bs = validFields fs os bs
  | [], _, _, _, _ => by simp [isSafeFields, validFields]
  | _ :: _, [], _, h, _ => by simp [fitsIn] at h
  | f :: fs, o :: os, bs, hfit, hF => by
    simp only [fitsIn] at hfit
    simp only [isSafeFields, validFields]
    rw [hF f List.mem_cons_self _ (by simp [slice]; omega),
      isSafeFields_eq_validFields fs os bs hfit.2 (fun g hg => hF g (List.mem_cons_of_mem _ hg))]

/-! ### Auxiliary lemmas: variant-indexed functions -/

theorem variantsFit_get : ∀ (vs : List (DiscrSyn × List Desc)) (oss : List (List Nat)) (N : Nat),
    variantsFit vs oss N → ∀ i (hi : i < vs.length), ∃ hi' : i < oss.length, fitsIn vs[i].2 oss[i] N
  | [], _, _, _, i, hi => by simp at hi
  | _ :: _, [], _, h, _, _ => by simp [variantsFit] at h
  | v :: vs, os :: oss, N, h, 0, _ => by
    simp only [variantsFit] at h
    exact ⟨by simp, h.1⟩
  | v :: vs, os :: oss, N, h, i + 1, hi => by
    simp only [variantsFit] at h
    obtain ⟨hi', hf⟩ := variantsFit_get vs oss N h.2 i (by simpa using hi)
    exact ⟨by simpa using hi', hf⟩

theorem variantsFit_map (N : Nat) (g : List Desc → List Nat) :
    ∀ vs : List (DiscrSyn × List Desc), (∀ v ∈ vs, fitsIn v.2 (g v.2) N) →
      variantsFit vs (vs.map (fun v => g v.2)) N
  | [], _ => by simp [variantsFit]
  | v :: vs, h => by
    simp only [List.map_cons, variantsFit]
    exact ⟨h v List.mem_cons_self, variantsFit_map N g vs (fun w hw => h w (List.mem_cons_of_mem _ hw))⟩

theorem decodeVariant_eq : ∀ (vs : List (DiscrSyn × List Desc)) (i : Nat) (oss : List (List Nat))
    (x : List AB) (hi : i < vs.length) (hi' : i < oss.length),
    Desc.decodeVariant vs i oss x = Desc.decodeFields vs[i].2 oss[i] x
  | [], _, _, _, hi, _ => by simp at hi
  | _ :: _, _, [], _, _, hi' => by simp at hi'
  | (d, fs) :: vs, 0, os :: oss, x, _, _ => by simp [Desc.decodeVariant]
  | (d, fs) :: vs, i + 1, os :: oss, x, hi, hi' => by
    simp only [Desc.decodeVariant, List.getElem_cons_succ]
    exact decodeVariant_eq vs i oss x (by simpa using hi) (by simpa using hi')

theorem decodeVariant_none_of_ge : ∀ (vs : List (DiscrSyn × List Desc)) (i : Nat)
    (oss : List (List Nat)) (x : List AB), ¬ (i < vs.length ∧ i < oss.length) →
    Desc.decodeVariant vs i oss x = none
  | [], _, _, _, _ => by simp [Desc.decodeVariant]
  | _ :: _, 0, [], _, _ => by simp [Desc.decodeVariant]
  | _ :: _, _ + 1, [], _, _ => by simp [Desc.decodeVariant]
  | (d, fs) :: vs, 0, os :: oss, x, h => by simp at h
  | (d, fs) :: vs, i + 1, os :: oss, x, h => by
    simp only [Desc.decodeVariant]
    exact decodeVariant_none_of_ge vs i oss x (by simp at h ⊢; omega)

theorem validVariant_eq_isSome : ∀ (vs : List (DiscrSyn × List Desc)) (i : Nat)
    (oss : List (List Nat)) (bs : List Byte),
    validVariant vs i oss bs = (Desc.decodeVariant vs i oss (bs.map AByte.init)).isSome
  | [], _, _, _ => by simp [validVariant, Desc.decodeVariant]
  | _ :: _, 0, [], _ => by simp [validVariant, Desc.decodeVariant]
  | _ :: _, _ + 1, [], _ => by simp [validVariant, Desc.decodeVariant]
  | (d, fs) :: vs, 0, os :: oss, bs => by
    simp [validVariant, Desc.decodeVariant, validFields_eq_isSome]
  | (d, fs) :: vs, i + 1, os :: oss, bs => by
    simp only [validVariant, Desc.decodeVariant]
    exact validVariant_eq_isSome vs i oss bs

theorem isSafeVariant_eq_validVariant : ∀ (vs : List (DiscrSyn × List Desc)) (i : Nat)
    (oss : List (List Nat)) (bs : List Byte), variantsFit vs oss bs.length →
    (∀ v ∈ vs, ∀ f ∈ v.2, ∀ bs', bs'.length = f.size → isSafe f bs' = validInit f bs') →
    isSafeVariant vs i oss bs = validVariant vs i oss bs
  | [], _, _, _, _, _ => by simp [isSafeVariant, validVariant]
  | _ :: _, _, [], _, h, _ => by simp [variantsFit] at h
  | (d, fs) :: vs, 0, os :: oss, bs, h, hF => by
    simp only [variantsFit] at h
    simp only [isSafeVariant, validVariant]
    exact isSafeFields_eq_validFields fs os bs h.1 (hF _ List.mem_cons_self)
  | (d, fs) :: vs, i + 1, os :: oss, bs, h, hF => by
    simp only [variantsFit] at h
    simp only [isSafeVariant, validVariant]
    exact isSafeVariant_eq_validVariant vs i oss bs h.2
      (fun v hv => hF v (List.mem_cons_of_mem _ hv))

theorem writeVariant_eq : ∀ (vs : List (DiscrSyn × List Desc)) (i : Nat) (oss : List (List Nat))
    (fvs : List Val) (buf : List AB) (hi : i < vs.length) (hi' : i < oss.length),
    Desc.writeVariant vs i oss fvs buf = Desc.writeFields vs[i].2 oss[i] fvs buf
  | [], _, _, _, _, hi, _ => by simp at hi
  | _ :: _, _, [], _, _, _, hi' => by simp at hi'
  | (d, fs) :: vs, 0, os :: oss, fvs, buf, _, _ => by simp [Desc.writeVariant]
  | (d, fs) :: vs, i + 1, os :: oss, fvs, buf, hi, hi' => by
    simp only [Desc.writeVariant, List.getElem_cons_succ]
    exact writeVariant_eq vs i oss fvs buf (by simpa using hi) (by simpa using hi')

theorem hasTypeVariant_iff : ∀ (vs : List (DiscrSyn × List Desc)) (i : Nat) (fvs : List Val),
    Desc.hasTypeVariant vs i fvs = true ↔ ∃ hi : i < vs.length, Desc.hasTypes vs[i].2 fvs = true
  | [], i, fvs => by simp [Desc.hasTypeVariant]
  | (d, fs) :: vs, 0, fvs => by simp [Desc.hasTypeVariant]
  | (d, fs) :: vs, i + 1, fvs => by
    simp only [Desc.hasTypeVariant, List.length_cons, List.getElem_cons_succ]
    rw [hasTypeVariant_iff vs i fvs]
    constructor
    · rintro ⟨hi, h⟩; exact ⟨by omega, h⟩
    · rintro ⟨hi, h⟩; exact ⟨by omega, h⟩

/-! ### Auxiliary lemmas: enum layouts -/

theorem reprIntEnum_offsets (tag : FieldLayout) (vls : List (List FieldLayout)) :
    (reprIntEnum tag vls).variantFieldOffsets =
      vls.map (fun vl => (placeFields .none tag.size vl).1) := by
  simp only [reprIntEnum, List.map_map]
  congr 1
  funext vl
  simp [reprCStruct, placeFields_cons, alignUp_zero_left]

theorem reprIntEnum_tagOffset (tag : FieldLayout) (vls : List (List FieldLayout)) :
    (reprIntEnum tag vls).tagOffset = 0 := by
  simp only [reprIntEnum]
  cases vls with
  | nil => rfl
  | cons vl vls => simp [reprCStruct, placeFields_cons, alignUp_zero_left]

theorem reprIntEnum_size_ge (tag : FieldLayout) (vls : List (List FieldLayout))
    (vl : List FieldLayout) (h : vl ∈ vls) :
    (placeFields .none tag.size vl).2 ≤ (reprIntEnum tag vls).size := by
  have h1 : (placeFields .none tag.size vl).2 ≤ (reprCStruct .none (tag :: vl)).size := by
    rw [reprCStruct_size, placeFields_cons]
    simp only [effFieldAlign, alignUp_zero_left, Nat.zero_add]
    exact le_alignUp _ _
  refine Nat.le_trans h1 (Nat.le_trans ?_ (le_alignUp _ _))
  apply foldl_max_size_ge_mem _ _ ⟨(reprCStruct .none (tag :: vl)).size, _⟩
  simp only [List.map_map, List.mem_map, Function.comp]
  exact ⟨vl, h, rfl⟩

/-- The byte offset of the payload of a `repr(C)` enum. -/
theorem reprCEnum_offsets (tag : FieldLayout) (vls : List (List FieldLayout)) :
    (reprCEnum tag vls).variantFieldOffsets =
      vls.map (fun vl => (placeFields .none 0 vl).1.map (· + alignUp tag.size
        (reprCUnion (vls.map fun vl => ⟨(reprCStruct .none vl).size,
          (reprCStruct .none vl).align⟩)).align)) := by
  simp only [reprCEnum, List.map_map]
  rfl

theorem reprCEnum_tagOffset (tag : FieldLayout) (vls : List (List FieldLayout)) :
    (reprCEnum tag vls).tagOffset = 0 := by
  simp [reprCEnum, reprCStruct, placeFields_cons, alignUp_zero_left]

theorem reprCEnum_size_ge (tag : FieldLayout) (vls : List (List FieldLayout))
    (vl : List FieldLayout) (h : vl ∈ vls) :
    (placeFields .none 0 vl).2 + alignUp tag.size
        (reprCUnion (vls.map fun vl => ⟨(reprCStruct .none vl).size,
          (reprCStruct .none vl).align⟩)).align ≤ (reprCEnum tag vls).size := by
  have h1 : (placeFields .none 0 vl).2 ≤ (reprCStruct .none vl).size := by
    rw [reprCStruct_size]; exact le_alignUp _ _
  have h2 : (reprCStruct .none vl).size ≤ (reprCUnion (vls.map fun vl =>
      (⟨(reprCStruct .none vl).size, (reprCStruct .none vl).align⟩ : FieldLayout))).size := by
    refine Nat.le_trans ?_ (le_alignUp _ _)
    apply foldl_max_size_ge_mem _ _ ⟨(reprCStruct .none vl).size, _⟩
    exact List.mem_map_of_mem h
  have h3 : ∀ (P : FieldLayout), alignUp tag.size P.align + P.size ≤
      (reprCStruct .none [tag, P]).size := by
    intro P
    rw [reprCStruct_size]
    refine Nat.le_trans (Nat.le_of_eq ?_) (le_alignUp _ _)
    simp [placeFields, effFieldAlign, alignUp_zero_left]
  have h4 := h3 ⟨(reprCUnion (vls.map fun vl => (⟨(reprCStruct .none vl).size,
      (reprCStruct .none vl).align⟩ : FieldLayout))).size,
    (reprCUnion (vls.map fun vl => (⟨(reprCStruct .none vl).size,
      (reprCStruct .none vl).align⟩ : FieldLayout))).align⟩
  have h5 : (reprCEnum tag vls).size = (reprCStruct .none [tag,
      ⟨(reprCUnion (vls.map fun vl => (⟨(reprCStruct .none vl).size,
        (reprCStruct .none vl).align⟩ : FieldLayout))).size,
      (reprCUnion (vls.map fun vl => (⟨(reprCStruct .none vl).size,
        (reprCStruct .none vl).align⟩ : FieldLayout))).align⟩]).size := by
    simp only [reprCEnum, List.map_map]; rfl
  dsimp only at h4
  omega

theorem enum_size_eq (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) :
    (Desc.enm r vs).size = (Desc.enumLayout r vs).size := rfl

theorem enum_tagOffset (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) :
    (Desc.enumLayout r vs).tagOffset = 0 := by
  unfold Desc.enumLayout
  cases r with
  | c => exact reprCEnum_tagOffset _ _
  | prim t => exact reprIntEnum_tagOffset _ _

theorem enum_variantsFit (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) :
    variantsFit vs (Desc.enumLayout r vs).variantFieldOffsets (Desc.enm r vs).size := by
  rw [enum_size_eq]
  unfold Desc.enumLayout
  rw [variantLayouts_eq_map]
  cases r with
  | prim t =>
    simp only [EnumRepr.layout]
    rw [reprIntEnum_offsets, List.map_map]
    apply variantsFit_map _ (fun fs => (placeFields .none (EnumRepr.prim t).tagLayout.size
      (Desc.layouts fs)).1)
    intro v hv
    have hb := reprIntEnum_size_ge (EnumRepr.prim t).tagLayout (vs.map fun v => Desc.layouts v.2)
      (Desc.layouts v.2) (List.mem_map_of_mem (f := fun v => Desc.layouts v.2) hv)
    have := fitsIn_placeFields .none 0 _ v.2 _ (Nat.le_trans (Nat.le_of_eq (Nat.add_zero _)) hb)
    simpa using this
  | c =>
    simp only [EnumRepr.layout]
    rw [reprCEnum_offsets, List.map_map]
    apply variantsFit_map _ (fun fs => (placeFields .none 0 (Desc.layouts fs)).1.map (· + _))
    intro v hv
    exact fitsIn_placeFields .none _ _ v.2 0
      (reprCEnum_size_ge _ _ _ (List.mem_map_of_mem (f := fun v => Desc.layouts v.2) hv))

/-! ### Auxiliary lemmas: little-endian tags -/

theorem leBytes_length : ∀ (w n : Nat), (leBytes w n).length = w
  | 0, _ => rfl
  | w + 1, n => by simp [leBytes, leBytes_length w]

theorem leNat_leBytes : ∀ (w n : Nat), leNat (leBytes w n) = n % 256 ^ w
  | 0, n => by simp [leBytes, leNat, Nat.mod_one]
  | w + 1, n => by
    simp only [leBytes, leNat, leNat_leBytes w, UInt8.toNat_ofNat']
    rw [show (256 : Nat) ^ (w + 1) = 256 * 256 ^ w from by rw [Nat.pow_succ, Nat.mul_comm],
      Nat.mod_mul]
    have : (2 : Nat) ^ 8 = 256 := rfl
    rw [this, Nat.mod_mod]

theorem leNat_lt : ∀ (l : List Byte), leNat l < 256 ^ l.length
  | [] => by simp [leNat]
  | b :: bs => by
    have h1 := UInt8.toNat_lt b
    have h2 := leNat_lt bs
    simp only [leNat, List.length_cons, Nat.pow_succ]
    omega

theorem leNat_replicate_zero : ∀ (k : Nat), leNat (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, leNat, leNat_replicate_zero k]

theorem enumTag_lt (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) (bs : List Byte) :
    enumTag r vs bs < 2 ^ (8 * r.tagTy.width) := by
  unfold enumTag
  have h1 := leNat_lt (slice bs (Desc.enumLayout r vs).tagOffset r.tagTy.width)
  have h2 : (slice bs (Desc.enumLayout r vs).tagOffset r.tagTy.width).length ≤ r.tagTy.width := by
    simp only [slice, List.length_take, List.length_drop]; exact Nat.min_le_left _ _
  have h3 : 256 ^ (slice bs (Desc.enumLayout r vs).tagOffset r.tagTy.width).length ≤
      256 ^ r.tagTy.width := Nat.pow_le_pow_right (by decide) h2
  rw [Nat.pow_mul]
  exact Nat.lt_of_lt_of_le h1 h3

/-! ### Auxiliary lemmas: enum validity -/

theorem enm_validInit_iff (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) (bs : List Byte) :
    validInit (.enm r vs) bs = true ↔ bs.length = (Desc.enm r vs).size ∧
      ∃ i, (Desc.codes r vs).findIdx? (· == enumTag r vs bs) = some i ∧
        validVariant vs i (Desc.enumLayout r vs).variantFieldOffsets bs = true := by
  rw [validInit_eq_isSome]
  simp only [Desc.decodeL, List.length_map]
  rw [slice_map_init, allInit_map_init]
  simp only
  by_cases hl : bs.length = (Desc.enm r vs).size
  · have hl' : bs.length = (r.layout (Desc.variantLayouts vs)).size := hl
    simp only [hl', ↓reduceIte]
    have htag : leNat (slice bs (r.layout (Desc.variantLayouts vs)).tagOffset r.tagTy.width) =
        enumTag r vs bs := rfl
    rw [htag]
    cases hf : (Desc.codes r vs).findIdx? (· == enumTag r vs bs) with
    | none => simp
    | some i =>
      simp only [Option.isSome_map, Option.some.injEq, exists_eq_left']
      rw [validVariant_eq_isSome]
      exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  · have hl' : ¬ bs.length = (r.layout (Desc.variantLayouts vs)).size := hl
    simp [hl']
    intro h
    exact absurd h hl

/-! ### Auxiliary lemmas: distinct representable discriminants and the count check -/

theorem nodupInt_iff : ∀ l : List Int, nodupInt l = true ↔ l.Nodup
  | [] => by simp [nodupInt]
  | x :: xs => by simp [nodupInt, nodupInt_iff xs, List.nodup_cons]

theorem card_bound : ∀ (N : Nat) (L : List Nat), L.Nodup → (∀ x ∈ L, x < N) → L.length ≤ N
  | 0, [], _, _ => Nat.le_refl _
  | 0, x :: _, _, h => absurd (h x List.mem_cons_self) (Nat.not_lt_zero _)
  | N + 1, L, hnd, h => by
    have h1 := card_bound N (L.erase N) (hnd.erase N) (by
      intro x hx
      have h2 := (hnd.mem_erase_iff).mp hx
      have := h x h2.2
      omega)
    rw [List.length_erase] at h1
    split at h1 <;> omega

theorem pigeonhole (N : Nat) (L : List Nat) (hnd : L.Nodup) (hlt : ∀ x ∈ L, x < N)
    (hlen : N ≤ L.length) : ∀ n, n < N → n ∈ L := by
  intro n hn
  apply Classical.byContradiction
  intro hc
  have := card_bound N (n :: L) (List.nodup_cons.mpr ⟨hc, hnd⟩) (by
    intro x hx
    cases hx with
    | head => exact hn
    | tail _ h => exact hlt x h)
  simp only [List.length_cons] at this
  omega

theorem nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α),
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hinj, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun b hb hfb => hnd.1 ?_, nodup_map_on f l (fun x hx y hy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hnd.2⟩
    have := hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb
    rw [← this]
    exact hb

theorem discrCode_inj (t : IntTy) (x y : Int) (hx : t.minVal ≤ x ∧ x ≤ t.maxVal)
    (hy : t.minVal ≤ y ∧ y ≤ t.maxVal) (h : discrCode t x = discrCode t y) : x = y := by
  cases t <;> simp [discrCode, IntTy.minVal, IntTy.maxVal, IntTy.width, IntTy.signed] at hx hy h <;>
    omega

theorem discrCode_lt (t : IntTy) (x : Int) : discrCode t x < 2 ^ (8 * t.width) := by
  cases t <;> simp [discrCode, IntTy.width] <;> omega

theorem discrCode_eq_zero_iff (t : IntTy) (x : Int) (hx : t.minVal ≤ x ∧ x ≤ t.maxVal) :
    discrCode t x = 0 ↔ x = 0 := by
  cases t <;> simp [discrCode, IntTy.minVal, IntTy.maxVal, IntTy.width, IntTy.signed] at hx ⊢ <;>
    omega

theorem resolveAux_length : ∀ (ds : List DiscrSyn) (n : Int), (resolveAux ds n).length = ds.length
  | [], _ => rfl
  | d :: ds, n => by simp [resolveAux, resolveAux_length ds]

theorem discrs_length (vs : List (DiscrSyn × List Desc)) : (Desc.discrs vs).length = vs.length := by
  simp [Desc.discrs, resolveDiscrs, resolveAux_length]

theorem codes_length (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) :
    (Desc.codes r vs).length = vs.length := by
  simp [Desc.codes, discrs_length]

theorem codes_cover (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hwf : discrsWF r (vs.map Prod.fst) = true) (hlen : 2 ^ (8 * r.tagTy.width) ≤ vs.length) :
    ∀ n, n < 2 ^ (8 * r.tagTy.width) → n ∈ Desc.codes r vs := by
  simp only [discrsWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, nodupInt_iff] at hwf
  apply pigeonhole
  · unfold Desc.codes Desc.discrs
    exact nodup_map_on _ _ (fun x hx y hy hxy => discrCode_inj _ x y (hwf.2 x hx) (hwf.2 y hy) hxy)
      hwf.1
  · intro x hx
    unfold Desc.codes at hx
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
    exact discrCode_lt _ _
  · rw [codes_length]; exact hlen

theorem count_check_len (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hc : enumVariantCountOK r vs = true) : 2 ^ (8 * r.tagTy.width) ≤ vs.length := by
  cases r with
  | c => simp [enumVariantCountOK, enumFromBytesBits] at hc
  | prim t =>
    cases t <;> simp [enumVariantCountOK, enumFromBytesBits, EnumRepr.tagTy, IntTy.width] at hc ⊢ <;>
      omega

/-! ### Auxiliary lemmas: enum validity under the count check -/

theorem validVariant_of_fieldless (vs : List (DiscrSyn × List Desc)) (hfl : Desc.Fieldless vs)
    (i : Nat) (hi : i < vs.length) (oss : List (List Nat)) (hoss : i < oss.length) (bs : List Byte) :
    validVariant vs i oss bs = true := by
  rw [validVariant_eq_isSome, decodeVariant_eq vs i oss _ hi hoss]
  have : vs[i].2 = [] := hfl _ (List.getElem_mem hi)
  rw [this]
  simp [Desc.decodeFields]

theorem validInit_enm_of_cover_fieldless (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hcov : ∀ n, n < 2 ^ (8 * r.tagTy.width) → n ∈ Desc.codes r vs) (hfl : Desc.Fieldless vs)
    (bs : List Byte) (hlen : bs.length = (Desc.enm r vs).size) :
    validInit (.enm r vs) bs = true := by
  rw [enm_validInit_iff]
  refine ⟨hlen, ?_⟩
  have hmem := hcov _ (enumTag_lt r vs bs)
  have hfi := List.findIdx?_eq_some_of_exists (p := fun x => x == enumTag r vs bs)
    ⟨_, hmem, beq_self_eq_true _⟩
  refine ⟨_, hfi, ?_⟩
  obtain ⟨hi, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
  rw [codes_length] at hi
  obtain ⟨hi', _⟩ := variantsFit_get vs _ _ (enum_variantsFit r vs) _ hi
  exact validVariant_of_fieldless vs hfl _ hi _ hi' bs

theorem enm_size_ge_width (t : IntTy) (v : DiscrSyn × List Desc) (vs : List (DiscrSyn × List Desc)) :
    t.width ≤ (Desc.enm (.prim t) (v :: vs)).size := by
  have h1 := reprIntEnum_size_ge (EnumRepr.prim t).tagLayout
    ((v :: vs).map fun v : DiscrSyn × List Desc => Desc.layouts v.2) (Desc.layouts v.2)
    (List.mem_map_of_mem (f := fun v : DiscrSyn × List Desc => Desc.layouts v.2) List.mem_cons_self)
  have h2 := placeFields_end_ge .none (Desc.layouts v.2) (EnumRepr.prim t).tagLayout.size
  rw [enum_size_eq]
  unfold Desc.enumLayout
  rw [variantLayouts_eq_map]
  show t.width ≤ (reprIntEnum (EnumRepr.prim t).tagLayout _).size
  have h3 : (EnumRepr.prim t).tagLayout.size = t.width := rfl
  omega

/-! ### Auxiliary lemmas: enum encodings -/

theorem writeFields_init_of_tight_shift (m : ReprModifier) (P : Nat) : ∀ (fs : List Desc) (c : Nat)
    (vs : List Val) (buf : List AB),
    (placeFields m c (Desc.layouts fs)).2 = c + (fs.map Desc.size).sum →
    (∀ f ∈ fs, SemIntoBytes f) → Desc.hasTypes fs vs = true →
    (placeFields m c (Desc.layouts fs)).2 + P ≤ buf.length →
    ∀ p, p < buf.length →
      (p < c + P ∨ (placeFields m c (Desc.layouts fs)).2 + P ≤ p →
        (buf.getD p .uninit).isInit = true) →
      ((Desc.writeFields fs ((placeFields m c (Desc.layouts fs)).1.map (· + P)) vs buf).getD p
        .uninit).isInit = true
  | [], c, vs, buf, ht, _, hty, _, p, _, hb => by
    cases vs with
    | nil =>
      simp only [Desc.writeFields]
      exact hb (by simp at ht ⊢; omega)
    | cons v vs => simp [Desc.hasTypes] at hty
  | f :: fs, c, [], buf, ht, _, hty, _, p, _, hb => by simp [Desc.hasTypes] at hty
  | f :: fs, c, v :: vs, buf, ht, hI, hty, hlen, p, hp, hb => by
    simp only [Desc.hasTypes, Bool.and_eq_true] at hty
    have hfs : f.layout.size = f.size := rfl
    have hle := le_alignUp c (effFieldAlign m f.layout.align)
    have hend := placeFields_end_ge m (Desc.layouts fs)
      (alignUp c (effFieldAlign m f.layout.align) + f.layout.size)
    rw [layouts_map_size] at hend
    rw [layouts_cons, placeFields_cons] at *
    simp only [List.map_cons, List.sum_cons] at ht
    simp only [List.map_cons, Desc.writeFields]
    have hfI := hI f List.mem_cons_self
    have hencI := (semIntoBytes_iff_encodeL_init f).mp hfI v hty.1
    refine writeFields_init_of_tight_shift m P fs _ vs _ (by omega)
      (fun g hg => hI g (List.mem_cons_of_mem _ hg)) hty.2 (by rw [writeAt_length]; omega) p
      (by rw [writeAt_length]; exact hp) ?_
    intro hcase
    by_cases hin : alignUp c (effFieldAlign m f.layout.align) + P ≤ p ∧
        p < alignUp c (effFieldAlign m f.layout.align) + P + f.size
    · rw [getD_writeAt_of_mem hin.1 (by rw [encodeL_length]; exact hin.2) hp]
      exact hencI _ (by omega)
    · rw [getD_writeAt]
      have : ¬ (alignUp c (effFieldAlign m f.layout.align) + P ≤ p ∧
          p < alignUp c (effFieldAlign m f.layout.align) + P + (f.encodeL v).length ∧
            p < buf.length) := by
        rw [encodeL_length]; omega
      simp only [this, ↓reduceIte]
      exact hb (by omega)

theorem enm_encodeL (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) (i : Nat) (fvs : List Val)
    (hi : i < vs.length) :
    ∃ (hi' : i < (Desc.enumLayout r vs).variantFieldOffsets.length) (buf : List AB),
      buf.length = (Desc.enm r vs).size ∧
      (∀ p, p < r.tagTy.width → p < (Desc.enm r vs).size → (buf.getD p .uninit).isInit = true) ∧
      (Desc.enm r vs).encodeL (.enm i fvs) =
        Desc.writeFields vs[i].2 (Desc.enumLayout r vs).variantFieldOffsets[i] fvs buf := by
  obtain ⟨hi', _⟩ := variantsFit_get vs _ _ (enum_variantsFit r vs) i hi
  refine ⟨hi', writeAt (List.replicate (Desc.enm r vs).size .uninit) 0
    ((leBytes r.tagTy.width (((Desc.codes r vs)[i]?).getD 0)).map .init), by simp [writeAt_length],
    ?_, ?_⟩
  · intro p hp1 hp2
    rw [getD_writeAt_of_mem (Nat.zero_le _) (by simp [leBytes_length]; exact hp1) (by simpa using hp2)]
    simp [List.getD_eq_getElem?_getD, leBytes_length, hp1]
  · simp only [Desc.encodeL]
    have hto : (r.layout (Desc.variantLayouts vs)).tagOffset = 0 := enum_tagOffset r vs
    rw [hto]
    show fit (Desc.enumLayout r vs).size (Desc.writeVariant vs i
      (Desc.enumLayout r vs).variantFieldOffsets fvs (writeAt (List.replicate (Desc.enm r vs).size .uninit) 0
        ((leBytes r.tagTy.width (((Desc.codes r vs)[i]?).getD 0)).map .init))) = _
    rw [writeVariant_eq vs i _ fvs _ hi hi',
      fit_of_length (by rw [writeFields_length, writeAt_length, List.length_replicate]; rfl)]

theorem reprC_enum_variant (vs : List (DiscrSyn × List Desc)) (i : Nat) (hi : i < vs.length)
    (hi' : i < (Desc.enumLayout .c vs).variantFieldOffsets.length) :
    ∃ PO, 4 ≤ PO ∧ (Desc.enumLayout .c vs).variantFieldOffsets[i] =
        (placeFields .none 0 (Desc.layouts vs[i].2)).1.map (· + PO) ∧
      (placeFields .none 0 (Desc.layouts vs[i].2)).2 + PO ≤ (Desc.enm .c vs).size := by
  have hmem : Desc.layouts vs[i].2 ∈ vs.map (fun v => Desc.layouts v.2) :=
    List.mem_map_of_mem (f := fun v : DiscrSyn × List Desc => Desc.layouts v.2) (List.getElem_mem hi)
  refine ⟨alignUp (EnumRepr.c).tagLayout.size (reprCUnion ((vs.map fun v => Desc.layouts v.2).map
    fun vl => (⟨(reprCStruct .none vl).size, (reprCStruct .none vl).align⟩ : FieldLayout))).align,
    le_alignUp _ _, ?_, ?_⟩
  · simp only [Desc.enumLayout, EnumRepr.layout, variantLayouts_eq_map, reprCEnum_offsets,
      List.getElem_map]
  · have := reprCEnum_size_ge (EnumRepr.c).tagLayout (vs.map fun v => Desc.layouts v.2) _ hmem
    show _ ≤ (reprCEnum _ (Desc.variantLayouts vs)).size
    rw [variantLayouts_eq_map]
    exact this

/-! ## Main statements -/

/-- **R3a.** A fieldless `repr(Int)` enum is `FromBytes` iff every tag value `n < 2^(8·width)` is
the code of some variant's discriminant. -/
theorem fieldless_enum_fromBytes_iff_every_tag_is_discriminant (t : IntTy)
    (vs : List (DiscrSyn × List Desc)) (hfl : Desc.Fieldless vs) :
    SemFromBytes (.enm (.prim t) vs) ↔
      ∀ n, n < 2 ^ (8 * t.width) → n ∈ Desc.codes (.prim t) vs := by
  rw [semFromBytes_iff_validInit_total]
  constructor
  · intro h n hn
    cases vs with
    | nil =>
      exfalso
      obtain ⟨_, i, hi, _⟩ := (enm_validInit_iff _ _ _).mp
        (h (List.replicate (Desc.enm (.prim t) []).size 0) (by simp))
      simp [Desc.codes, Desc.discrs, resolveDiscrs, resolveAux] at hi
    | cons v vs' =>
      have hw := enm_size_ge_width t v vs'
      have hbl : (leBytes t.width n ++ List.replicate ((Desc.enm (.prim t) (v :: vs')).size - t.width)
          0).length = (Desc.enm (.prim t) (v :: vs')).size := by
        simp only [List.length_append, leBytes_length, List.length_replicate]
        omega
      obtain ⟨_, i, hi, _⟩ := (enm_validInit_iff _ _ _).mp (h _ hbl)
      obtain ⟨hil, heq, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
      have htag : enumTag (.prim t) (v :: vs') (leBytes t.width n ++
          List.replicate ((Desc.enm (.prim t) (v :: vs')).size - t.width) 0) = n := by
        have hlt : n < 256 ^ t.width := by
          rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact hn
        show leNat (slice _ (Desc.enumLayout (.prim t) (v :: vs')).tagOffset t.width) = n
        rw [enum_tagOffset]
        unfold slice
        rw [List.drop_zero, List.take_append_of_le_length (by rw [leBytes_length]; exact Nat.le_refl _),
          List.take_of_length_le (by rw [leBytes_length]; exact Nat.le_refl _), leNat_leBytes,
          Nat.mod_eq_of_lt hlt]
      have := beq_iff_eq.mp heq
      rw [htag] at this
      rw [← this]
      exact List.getElem_mem hil
  · intro hcov bs hbs
    exact validInit_enm_of_cover_fieldless (.prim t) vs hcov hfl bs hbs

/-- **R3b.** If the resolved discriminants are pairwise distinct and representable in the tag type
(`discrsWF`), the derive's count check (`repr(u8/i8/u16/i16)` and `2^bits` variants) implies that
every tag value is the code of a discriminant. -/
theorem enum_variant_count_check_sound (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hwf : discrsWF r (vs.map Prod.fst) = true) (hc : enumVariantCountOK r vs = true) :
    ∀ n, n < 2 ^ (8 * r.tagTy.width) → n ∈ Desc.codes r vs :=
  codes_cover r vs hwf (count_check_len r vs hc)

/-- **R3c.** Soundness of the enum `FromBytes` derive's semantic conditions, data-carrying case:
distinct representable discriminants, the count check, and `FromBytes` fields imply `FromBytes`. -/
theorem enum_fromBytes_of_count_check (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hwf : discrsWF r (vs.map Prod.fst) = true) (hc : enumVariantCountOK r vs = true)
    (hF : ∀ v ∈ vs, ∀ f ∈ v.2, SemFromBytes f) :
    SemFromBytes (.enm r vs) := by
  rw [semFromBytes_iff_validInit_total]
  intro bs hbs
  rw [enm_validInit_iff]
  refine ⟨hbs, ?_⟩
  have hmem := enum_variant_count_check_sound r vs hwf hc _ (enumTag_lt r vs bs)
  have hfi := List.findIdx?_eq_some_of_exists (p := fun x => x == enumTag r vs bs)
    ⟨_, hmem, beq_self_eq_true _⟩
  refine ⟨_, hfi, ?_⟩
  obtain ⟨hi, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
  rw [codes_length] at hi
  obtain ⟨hi', hfit⟩ := variantsFit_get vs _ _ (enum_variantsFit r vs) _ hi
  rw [validVariant_eq_isSome, decodeVariant_eq vs _ _ _ hi hi']
  apply decodeFields_isSome_of_fits (fun b => b.isInit = true) _ _ _ (by simpa [hbs] using hfit)
  · intro b hb
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
    rfl
  · intro f hf y hy hyI
    obtain ⟨cs, rfl⟩ := exists_map_init_of_forall_isInit y hyI
    have := (semFromBytes_iff_validInit_total f).mp (hF _ (List.getElem_mem hi) f hf) cs
      (by simpa using hy)
    rwa [validInit_eq_isSome] at this

/-- **R3d.** Under distinct representable discriminants, an enum is `FromZeros` iff some variant has
discriminant `0` and every field of that variant is `FromZeros`. -/
theorem enum_fromZeros_iff_zero_variant_fields_fromZeros_of_discrsWF (r : EnumRepr)
    (vs : List (DiscrSyn × List Desc)) (hwf : discrsWF r (vs.map Prod.fst) = true) :
    SemFromZeros (.enm r vs) ↔
      ∃ i fs, (Desc.discrs vs)[i]? = some 0 ∧ variantFields vs i = some fs ∧
        ∀ f ∈ fs, SemFromZeros f := by
  have hwf' := hwf
  simp only [discrsWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, nodupInt_iff] at hwf'
  have hnd : (Desc.discrs vs).Nodup := hwf'.1
  have hrange : ∀ k (hk : k < (Desc.discrs vs).length),
      r.tagTy.minVal ≤ (Desc.discrs vs)[k] ∧ (Desc.discrs vs)[k] ≤ r.tagTy.maxVal :=
    fun k hk => hwf'.2 _ (List.getElem_mem hk)
  have hcode0 : ∀ k (hk : k < (Desc.codes r vs).length) (hk' : k < (Desc.discrs vs).length),
      (Desc.codes r vs)[k] = 0 ↔ (Desc.discrs vs)[k] = 0 := by
    intro k hk hk'
    simp only [Desc.codes, List.getElem_map]
    exact discrCode_eq_zero_iff _ _ (hrange k hk')
  have htag0 : enumTag r vs (List.replicate (Desc.enm r vs).size 0) = 0 := by
    unfold enumTag
    simp only [slice, List.drop_replicate, List.take_replicate, leNat_replicate_zero]
  rw [semFromZeros_iff_validInit_zeros, enm_validInit_iff, htag0]
  simp only [List.length_replicate, true_and]
  constructor
  · rintro ⟨i, hfi, hvv⟩
    obtain ⟨hi, heq, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hi2 : i < vs.length := by rwa [codes_length] at hi
    refine ⟨i, vs[i].2, ?_, by simp [variantFields, List.getElem?_eq_getElem hi2], ?_⟩
    · rw [List.getElem?_eq_getElem (by rw [discrs_length]; exact hi2)]
      rw [(hcode0 i hi (by rw [discrs_length]; exact hi2)).mp (beq_iff_eq.mp heq)]
    · intro f hf
      obtain ⟨hi', hfit⟩ := variantsFit_get vs _ _ (enum_variantsFit r vs) i hi2
      rw [validVariant_eq_isSome, decodeVariant_eq vs i _ _ hi2 hi'] at hvv
      obtain ⟨o, ho1, ho2⟩ := decodeFields_field_of_fits _ _ _ hfit f hf
      have := ho2 _ hvv
      rw [List.map_replicate, slice_replicate _ _ _ _ ho1] at this
      rw [semFromZeros_iff_validInit_zeros, validInit_eq_isSome, List.map_replicate]
      exact this
  · rintro ⟨i, fs, hd0, hfs, hF⟩
    have hd : i < (Desc.discrs vs).length := by
      rcases Nat.lt_or_ge i (Desc.discrs vs).length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hd0; cases hd0
    have hdi : (Desc.discrs vs)[i] = 0 := by
      rw [List.getElem?_eq_getElem hd] at hd0
      exact Option.some.inj hd0
    have hi2 : i < vs.length := by rwa [discrs_length] at hd
    have hci : i < (Desc.codes r vs).length := by rwa [codes_length]
    have hc0 : (Desc.codes r vs)[i] = 0 := (hcode0 i hci hd).mpr hdi
    have hfi := List.findIdx?_eq_some_of_exists (p := fun x => x == 0)
      ⟨_, List.getElem_mem hci, beq_iff_eq.mpr hc0⟩
    obtain ⟨hj, hjeq, hjmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hji : List.findIdx (fun x => x == 0) (Desc.codes r vs) = i := by
      apply Classical.byContradiction
      intro hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have hdj := (hcode0 _ hj (by rw [discrs_length]; rw [codes_length] at hj; exact hj)).mp
          (beq_iff_eq.mp hjeq)
        exact (List.pairwise_iff_getElem.mp hnd _ i _ hd h) (hdj.trans hdi.symm)
      · exact hjmin i h (beq_iff_eq.mpr hc0)
    rw [hji] at hfi
    refine ⟨i, hfi, ?_⟩
    have hfs' : vs[i].2 = fs := by
      simp only [variantFields, List.getElem?_eq_getElem hi2, Option.map_some, Option.some.injEq] at hfs
      exact hfs
    obtain ⟨hi', hfit⟩ := variantsFit_get vs _ _ (enum_variantsFit r vs) i hi2
    rw [validVariant_eq_isSome, decodeVariant_eq vs i _ _ hi2 hi']
    apply decodeFields_isSome_of_fits (fun b => b = .init 0) _ _ _ (by simpa using hfit)
    · intro b hb
      simp only [List.map_replicate, List.mem_replicate] at hb
      exact hb.2
    · intro f hf y hy hy0
      rw [hfs'] at hf
      have hyr : y = (List.replicate f.size (0 : Byte)).map AByte.init := by
        rw [List.map_replicate, List.eq_replicate_iff]
        exact ⟨hy, hy0⟩
      have := (semFromZeros_iff_validInit_zeros f).mp (hF f hf)
      rw [validInit_eq_isSome] at this
      rw [hyr]
      exact this

/-- **R3e (soundness of `find_zero_variant`).** If the syntactic search returns variant `i`, the
compiler resolves variant `i`'s discriminant to `0`. -/
theorem findZeroVariant_sound (ds : List DiscrSyn) (i : Nat) (h : findZeroVariant ds = .ok i) :
    (resolveDiscrs ds)[i]? = some 0 := by
  have := (findZeroVariantAux_sound ds 0 (some 0) false 0 i (by intro n hn; cases hn; simp) h).2
  simpa [resolveDiscrs] using this

/-- **R3e (completeness without unknown discriminants).** If the search fails without having seen a
non-literal discriminant, no variant has discriminant `0`. -/
theorem findZeroVariant_complete_of_no_unknown (ds : List DiscrSyn)
    (h : findZeroVariant ds = .error false) : 0 ∉ resolveDiscrs ds :=
  findZeroVariantAux_complete ds 0 (some 0) false 0 (by intro n hn; cases hn; simp) (by simp) h

/-- **R3e (node-level soundness of the enum `FromZeros` derive).** Distinct representable
discriminants, `find_zero_variant` returning `i`, and `FromZeros` fields of variant `i` imply
`FromZeros`. -/
theorem enum_fromZeros_of_findZeroVariant (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hwf : discrsWF r (vs.map Prod.fst) = true) (i : Nat)
    (hz : findZeroVariant (vs.map Prod.fst) = .ok i)
    (hF : ∀ fs, variantFields vs i = some fs → ∀ f ∈ fs, SemFromZeros f) :
    SemFromZeros (.enm r vs) := by
  have hd : (Desc.discrs vs)[i]? = some 0 := findZeroVariant_sound _ i hz
  have hi : i < vs.length := by
    rcases Nat.lt_or_ge i vs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none (by rw [discrs_length]; exact h)] at hd; cases hd
  have hv : variantFields vs i = some vs[i].2 := by simp [variantFields, List.getElem?_eq_getElem hi]
  exact (enum_fromZeros_iff_zero_variant_fields_fromZeros_of_discrsWF r vs hwf).mpr
    ⟨i, vs[i].2, hd, hv, hF _ hv⟩

/-- **R3f (characterization).** For bytes of the enum's size, `TryFromBytes` validity is: the tag
matches the code of some variant (the first such variant, `i`), and the fields of variant `i` are
valid at their offsets. -/
theorem enum_validInit_iff_first_matching_variant_valid (r : EnumRepr)
    (vs : List (DiscrSyn × List Desc)) (bs : List Byte) (hlen : bs.length = (Desc.enm r vs).size) :
    validInit (.enm r vs) bs = true ↔
      ∃ i, (Desc.codes r vs).findIdx? (· == enumTag r vs bs) = some i ∧
        validVariant vs i (Desc.enumLayout r vs).variantFieldOffsets bs = true := by
  rw [enm_validInit_iff]
  exact ⟨fun h => h.2, fun h => ⟨hlen, h⟩⟩

/-- **R3f (the derived check is exactly validity).** If the fields' `is_safe` agree with validity,
and the discriminants are distinct and representable, the derived enum `is_safe` (including its
`could_be_from_bytes` shortcut) equals validity on bytes of the enum's size. -/
theorem isSafe_enm_eq_validInit (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hwf : discrsWF r (vs.map Prod.fst) = true)
    (hfields : ∀ v ∈ vs, ∀ f ∈ v.2, ∀ bs, bs.length = f.size → isSafe f bs = validInit f bs)
    (bs : List Byte) (hlen : bs.length = (Desc.enm r vs).size) :
    isSafe (.enm r vs) bs = validInit (.enm r vs) bs := by
  unfold isSafe
  by_cases hcb : couldBeFromBytes r vs = true
  · simp only [hcb, ↓reduceIte]
    have hc : enumVariantCountOK r vs = true := by
      unfold couldBeFromBytes at hcb
      unfold enumVariantCountOK
      split at hcb
      · simp only [Bool.and_eq_true] at hcb
        exact hcb.2
      · cases hcb
    have hfl : Desc.Fieldless vs := by
      unfold couldBeFromBytes at hcb
      split at hcb
      · simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at hcb
        exact fun v hv => hcb.1 v hv
      · cases hcb
    exact (validInit_enm_of_cover_fieldless r vs (enum_variant_count_check_sound r vs hwf hc) hfl bs
      hlen).symm
  · simp only [Bool.not_eq_true] at hcb
    simp only [hcb, Bool.false_eq_true, ↓reduceIte]
    have hiff := enm_validInit_iff r vs bs
    have hfit : variantsFit vs (Desc.enumLayout r vs).variantFieldOffsets bs.length := by
      rw [hlen]; exact enum_variantsFit r vs
    show (match (Desc.codes r vs).findIdx? (· == enumTag r vs bs) with
      | some i => isSafeVariant vs i (Desc.enumLayout r vs).variantFieldOffsets bs
      | none => false) = validInit (.enm r vs) bs
    cases hfi : (Desc.codes r vs).findIdx? (· == enumTag r vs bs) with
    | none =>
      simp only
      cases hv : validInit (.enm r vs) bs
      · rfl
      · obtain ⟨_, i, hi, _⟩ := hiff.mp hv
        rw [hfi] at hi; cases hi
    | some i =>
      simp only
      rw [isSafeVariant_eq_validVariant vs i _ bs hfit hfields]
      cases hv : validVariant vs i (Desc.enumLayout r vs).variantFieldOffsets bs
      · cases hvi : validInit (.enm r vs) bs
        · rfl
        · obtain ⟨_, i', hi', hv'⟩ := hiff.mp hvi
          rw [hfi] at hi'
          cases hi'
          rw [hv] at hv'
          cases hv'
      · exact (hiff.mpr ⟨hlen, i, hfi, hv⟩).symm

/-- **R3g.** Soundness of the enum `IntoBytes` derive's semantic conditions: every field of every
variant `IntoBytes` and `enum_padding! == 0` imply `IntoBytes`. -/
theorem enum_intoBytes_of_fields_of_padding_check (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hF : ∀ v ∈ vs, ∀ f ∈ v.2, SemIntoBytes f) (hP : enumPaddingOK r vs = true) :
    SemIntoBytes (.enm r vs) := by
  rw [semIntoBytes_iff_encodeL_init]
  intro v hv p hp
  cases v with
  | enm i fvs =>
    simp only [Desc.hasType] at hv
    obtain ⟨hi, hty⟩ := (hasTypeVariant_iff vs i fvs).mp hv
    have hpad : (Desc.enm r vs).size ≤ r.tagTy.width + (vs[i].2.map Desc.size).sum := by
      have := List.all_eq_true.mp hP vs[i] (List.getElem_mem hi)
      simp only [beq_iff_eq] at this
      have h' : (Desc.enm r vs).size = (Desc.enumLayout r vs).size := rfl
      omega
    obtain ⟨hi', buf, hbl, htagI, henc⟩ := enm_encodeL r vs i fvs hi
    rw [henc]
    have hFi := hF vs[i] (List.getElem_mem hi)
    have hvl : (Desc.variantLayouts vs)[i]'(by rw [variantLayouts_eq_map]; simpa using hi) =
        Desc.layouts vs[i].2 := by
      simp [variantLayouts_eq_map]
    have hmem : Desc.layouts vs[i].2 ∈ vs.map (fun v => Desc.layouts v.2) :=
      List.mem_map_of_mem (f := fun v : DiscrSyn × List Desc => Desc.layouts v.2) (List.getElem_mem hi)
    cases r with
    | prim t =>
      have hoffs : (Desc.enumLayout (.prim t) vs).variantFieldOffsets[i] =
          (placeFields .none t.width (Desc.layouts vs[i].2)).1.map (· + 0) := by
        simp only [Desc.enumLayout, EnumRepr.layout, variantLayouts_eq_map, reprIntEnum_offsets,
          List.getElem_map, Nat.add_zero, List.map_id_fun', id]
        rfl
      rw [hoffs]
      have hge := reprIntEnum_size_ge (EnumRepr.prim t).tagLayout _ _ hmem
      have hend := placeFields_end_ge .none (Desc.layouts vs[i].2) t.width
      rw [layouts_map_size] at hend
      have hsz : (Desc.enm (.prim t) vs).size =
          (reprIntEnum (EnumRepr.prim t).tagLayout (vs.map fun v => Desc.layouts v.2)).size := by
        show (reprIntEnum _ (Desc.variantLayouts vs)).size = _
        rw [variantLayouts_eq_map]
      have htw : (EnumRepr.prim t).tagLayout.size = t.width := rfl
      have htt : (EnumRepr.prim t).tagTy.width = t.width := rfl
      rw [htw] at hge
      rw [htt] at hpad htagI
      refine writeFields_init_of_tight_shift .none 0 _ t.width fvs buf (by omega) hFi hty
        (by omega) p (by omega) ?_
      intro hcase
      exact htagI p (by omega) hp
    | c =>
      obtain ⟨PO, hPO4, hoffs, hge⟩ := reprC_enum_variant vs i hi hi'
      rw [hoffs]
      have hend := placeFields_end_ge .none (Desc.layouts vs[i].2) 0
      rw [layouts_map_size] at hend
      have htt : (EnumRepr.c).tagTy.width = 4 := rfl
      rw [htt] at hpad htagI
      refine writeFields_init_of_tight_shift .none PO _ 0 fvs buf (by omega) hFi hty (by omega) p
        (by omega) ?_
      intro hcase
      exact htagI p (by omega) hp
  | _ => simp [Desc.hasType] at hv

/-! ## Concrete enums used below -/

set_option maxRecDepth 100000

/-- 256 fieldless variants with implicit discriminants `0, …, 255`. -/
def fullU8Variants : List (DiscrSyn × List Desc) := List.replicate 256 (.implicit, [])

/-- 256 variants with discriminants `0, …, 255`; variant `0` carries a `bool`. -/
def fullU8BoolVariants : List (DiscrSyn × List Desc) :=
  (.implicit, [Desc.bool]) :: List.replicate 255 (.implicit, [])

/-- 256 fieldless variants all with discriminant `0` (rejected by the compiler, E0081). -/
def dupZeroVariants : List (DiscrSyn × List Desc) := List.replicate 256 (.lit 0, [])

/-! ## Non-vacuity -/

theorem ex_couldBeFromBytes_pos : couldBeFromBytes (.prim .u8) fullU8Variants = true := by decide

theorem nv_fieldless_full_u8 :
    Desc.Fieldless fullU8Variants ∧ discrsWF (.prim .u8) (fullU8Variants.map Prod.fst) = true ∧
    enumVariantCountOK (.prim .u8) fullU8Variants = true ∧
    implFromBytes (.enm (.prim .u8) fullU8Variants) = true := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro v hv
  simp only [fullU8Variants, List.mem_replicate] at hv
  rw [hv.2]

theorem nv_enum_fromBytes_data :
    let vs : List (DiscrSyn × List Desc) := (.implicit, [Desc.u8]) :: List.replicate 255 (.implicit, [])
    discrsWF (.prim .u8) (vs.map Prod.fst) = true ∧ enumVariantCountOK (.prim .u8) vs = true ∧
    (∀ v ∈ vs, ∀ f ∈ v.2, SemFromBytes f) := by
  refine ⟨by decide, by decide, ?_⟩
  intro v hv f hf
  simp only [List.mem_cons, List.mem_replicate] at hv
  rcases hv with rfl | ⟨_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact semFromBytes_int _
  · cases hf

/-- Non-vacuity of R3d: `#[repr(i8)] enum { A(bool) = 3, B = -1, C(u16) }` (`C` has discriminant
`0`) has distinct representable discriminants, and its zero variant has `FromZeros` fields. -/
theorem nv_enum_fromZeros :
    let vs : List (DiscrSyn × List Desc) := [(.lit 3, [Desc.bool]), (.negLit 1, []), (.implicit, [Desc.u16])]
    discrsWF (.prim .i8) (vs.map Prod.fst) = true ∧
    findZeroVariant (vs.map Prod.fst) = .ok 2 ∧
    (Desc.discrs vs)[2]? = some 0 ∧ variantFields vs 2 = some [Desc.u16] ∧
    (∀ f ∈ [Desc.u16], SemFromZeros f) := by
  refine ⟨by decide, rfl, by decide, rfl, ?_⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact semFromZeros_int _

/-- Non-vacuity of `findZeroVariant_sound` and `findZeroVariant_complete_of_no_unknown`. -/
theorem nv_findZeroVariant : findZeroVariant [.negLit 2, .implicit, .implicit] = .ok 2 ∧
    findZeroVariant [.lit 1, .implicit] = .error false := ⟨rfl, rfl⟩

/-- Non-vacuity of `enum_fromZeros_of_findZeroVariant`: all three hypotheses hold for the enum of
`nv_enum_fromZeros` with `i = 2`. -/
theorem nv_enum_fromZeros_of_findZeroVariant :
    let vs : List (DiscrSyn × List Desc) :=
      [(.lit 3, [Desc.bool]), (.negLit 1, []), (.implicit, [Desc.u16])]
    discrsWF (.prim .i8) (vs.map Prod.fst) = true ∧
    findZeroVariant (vs.map Prod.fst) = .ok 2 ∧
    (∀ fs, variantFields vs 2 = some fs → ∀ f ∈ fs, SemFromZeros f) := by
  refine ⟨by decide, rfl, ?_⟩
  intro fs hfs f hf
  simp only [variantFields, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, Option.some.injEq] at hfs
  subst hfs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact semFromZeros_int _

/-- `is_safe` agrees with validity on `u8` for byte lists of the right length. -/
theorem isSafe_eq_validInit_u8 (bs : List Byte) (h : bs.length = Desc.u8.size) :
    isSafe .u8 bs = validInit .u8 bs := by
  rw [validInit_int]
  simp only [Desc.size, Desc.layout, IntTy.width] at h
  simp [isSafe, IntTy.width, h]

/-- `is_safe` agrees with validity on `bool` for byte lists of the right length. -/
theorem isSafe_eq_validInit_bool (bs : List Byte) (h : bs.length = Desc.bool.size) :
    isSafe .bool bs = validInit .bool bs := by
  match bs, h with
  | [b], _ =>
    simp only [isSafe, validInit, Desc.decodeL]
    by_cases h0 : b = 0
    · subst h0; decide
    · by_cases h1 : b = 1
      · subst h1; decide
      · have hlt : ¬ (b < 2) := by
          intro hc
          have hv : b.toNat < 2 := hc
          have hbe : b = UInt8.ofNat b.toNat := UInt8.ofNat_toNat.symm
          have hb0 : b.toNat ≠ 0 := fun e => h0 (by rw [hbe, e]; rfl)
          have hb1 : b.toNat ≠ 1 := fun e => h1 (by rw [hbe, e]; rfl)
          omega
        simp [h0, h1, hlt]

/-- Non-vacuity of both theorems of R3f: for `#[repr(u8)] enum { A(u8), B(bool) = 5 }` and the bytes
`[5, 1]`, the discriminants are distinct and representable, the fields' `is_safe` agrees with
validity, and the bytes have the enum's size; the two sides evaluate as expected on three byte
lists. -/
theorem nv_enum_validInit :
    let vs : List (DiscrSyn × List Desc) := [(.implicit, [.u8]), (.lit 5, [.bool])]
    let E : Desc := .enm (.prim .u8) vs
    discrsWF (.prim .u8) (vs.map Prod.fst) = true ∧
    (∀ v ∈ vs, ∀ f ∈ v.2, ∀ bs, bs.length = f.size → isSafe f bs = validInit f bs) ∧
    ([5, 1] : List Byte).length = E.size ∧
    validInit E [5, 1] = true ∧ validInit E [5, 2] = false ∧ validInit E [4, 0] = false ∧
    isSafe E [5, 1] = true ∧ isSafe E [5, 2] = false ∧ isSafe E [4, 0] = false := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩
  intro v hv f hf bs hlen
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact isSafe_eq_validInit_u8 bs hlen
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact isSafe_eq_validInit_bool bs hlen

theorem nv_enum_intoBytes :
    let vs : List (DiscrSyn × List Desc) := [(.implicit, [.u8]), (.implicit, [.int .i8])]
    (∀ v ∈ vs, ∀ f ∈ v.2, SemIntoBytes f) ∧ enumPaddingOK (.prim .u8) vs = true := by
  refine ⟨?_, by decide⟩
  intro v hv f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact semIntoBytes_int _

/-! ## Counterexamples (canonical form: the other hypotheses hold, the dropped one fails, and the
conclusion fails) -/

/-- 256 variants with distinct discriminants `0, 256, 2, 3, …, 255` (`256` overflows `u8`, a compiler
error): distinct but not representable. -/
def overflowVariants : List (DiscrSyn × List Desc) :=
  (.lit 0, []) :: (.lit 256, []) :: (List.range 254).map fun k => (.lit (k + 2), [])

/-- The fields of `fullU8BoolVariants` are not all `FromBytes` (variant `0` carries a `bool`). -/
theorem not_all_fromBytes_fullU8BoolVariants :
    ¬ (∀ v ∈ fullU8BoolVariants, ∀ f ∈ v.2, SemFromBytes f) := fun h =>
  not_semFromBytes_bool (h (.implicit, [Desc.bool]) List.mem_cons_self .bool List.mem_cons_self)

/-- `fullU8BoolVariants` is not fieldless. -/
theorem not_fieldless_fullU8BoolVariants : ¬ Desc.Fieldless fullU8BoolVariants := fun h => by
  have := h (.implicit, [Desc.bool]) List.mem_cons_self
  cases this

theorem not_semFromBytes_fullU8BoolVariants :
    ¬ SemFromBytes (.enm (.prim .u8) fullU8BoolVariants) := by
  rw [semFromBytes_iff_validInit_total]
  intro h
  have := h [0, 2] (by decide)
  revert this
  decide

/-- **Tightness of `hfl` in R3a.** 256 variants with discriminants `0…255`, variant `0` carrying a
`bool`: not fieldless; every tag value is a discriminant, but the enum is not `FromBytes` (the bytes
`[0, 2]` are invalid), so the characterization fails. -/
theorem ce_fieldless_enum_fromBytes_iff_drop_fieldless :
    ¬ Desc.Fieldless fullU8BoolVariants ∧
    ¬ (SemFromBytes (.enm (.prim .u8) fullU8BoolVariants) ↔
        ∀ n, n < 2 ^ (8 * IntTy.u8.width) → n ∈ Desc.codes (.prim .u8) fullU8BoolVariants) :=
  ⟨not_fieldless_fullU8BoolVariants, fun hiff =>
    not_semFromBytes_fullU8BoolVariants (hiff.mpr (by decide))⟩

/-- **Tightness of `hwf` in R3b (distinctness).** 256 variants all with discriminant `0`
(representable, not distinct): the count check passes, but tag value `1` is not a discriminant. The
derive relies on the compiler rejecting duplicate discriminants (E0081). -/
theorem ce_count_check_drop_wf :
    discrsWF (.prim .u8) (dupZeroVariants.map Prod.fst) = false ∧
    enumVariantCountOK (.prim .u8) dupZeroVariants = true ∧
    ¬ (∀ n, n < 2 ^ (8 * (EnumRepr.prim .u8).tagTy.width) →
        n ∈ Desc.codes (.prim .u8) dupZeroVariants) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h 1 (by decide)
  revert this
  decide

/-- **Tightness of `hwf` in R3b (representability).** The 256 distinct discriminants
`0, 256, 2, …, 255` (`256` overflows `u8`): the count check passes, but tag value `1` is not the
code of any discriminant (`256` wraps to `0`). -/
theorem ce_count_check_drop_representable :
    nodupInt (resolveDiscrs (overflowVariants.map Prod.fst)) = true ∧
    discrsWF (.prim .u8) (overflowVariants.map Prod.fst) = false ∧
    enumVariantCountOK (.prim .u8) overflowVariants = true ∧
    ¬ (∀ n, n < 2 ^ (8 * (EnumRepr.prim .u8).tagTy.width) →
        n ∈ Desc.codes (.prim .u8) overflowVariants) := by
  refine ⟨by decide, by decide, by decide, fun h => ?_⟩
  have := h 1 (by decide)
  revert this
  decide

/-- **Tightness of `hc` in R3b.** One fieldless `repr(u8)` variant: well-formed, count check fails,
tag value `1` is not a discriminant. -/
theorem ce_count_check_drop_count :
    discrsWF (.prim .u8) ([(DiscrSyn.implicit, ([] : List Desc))].map Prod.fst) = true ∧
    enumVariantCountOK (.prim .u8) [(.implicit, [])] = false ∧
    ¬ (∀ n, n < 2 ^ (8 * (EnumRepr.prim .u8).tagTy.width) →
        n ∈ Desc.codes (.prim .u8) [(.implicit, [])]) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h 1 (by decide)
  revert this
  decide

/-- **Tightness of `hwf` in R3c (distinctness).** With 256 duplicate-`0` fieldless variants the count
check passes and all (zero) fields are `FromBytes`, but the enum is not `FromBytes`. -/
theorem ce_enum_fromBytes_drop_wf :
    discrsWF (.prim .u8) (dupZeroVariants.map Prod.fst) = false ∧
    enumVariantCountOK (.prim .u8) dupZeroVariants = true ∧
    (∀ v ∈ dupZeroVariants, ∀ f ∈ v.2, SemFromBytes f) ∧
    ¬ SemFromBytes (.enm (.prim .u8) dupZeroVariants) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro v hv f hf
    simp only [dupZeroVariants, List.mem_replicate] at hv
    rw [hv.2] at hf; cases hf
  · rw [semFromBytes_iff_validInit_total]
    intro h
    have := h [1] (by decide)
    revert this
    decide

/-- **Tightness of `hwf` in R3c (representability).** The distinct but overflowing discriminants
`0, 256, 2, …, 255`: the count check passes, there are no fields, but the byte `1` is not a valid
tag, so the enum is not `FromBytes`. -/
theorem ce_enum_fromBytes_drop_representable :
    discrsWF (.prim .u8) (overflowVariants.map Prod.fst) = false ∧
    enumVariantCountOK (.prim .u8) overflowVariants = true ∧
    (∀ v ∈ overflowVariants, ∀ f ∈ v.2, SemFromBytes f) ∧
    ¬ SemFromBytes (.enm (.prim .u8) overflowVariants) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro v hv f hf
    simp only [overflowVariants, List.mem_cons, List.mem_map, List.mem_range] at hv
    rcases hv with rfl | rfl | ⟨k, _, rfl⟩ <;> cases hf
  · rw [semFromBytes_iff_validInit_total]
    intro h
    have := h [1] (by decide)
    revert this
    decide

/-- **Tightness of `hc` in R3c.** One fieldless `repr(u8)` variant (well-formed, no fields): the
count check fails and the enum is not `FromBytes` (tag `1` is invalid). -/
theorem ce_enum_fromBytes_drop_count :
    discrsWF (.prim .u8) ([(DiscrSyn.implicit, ([] : List Desc))].map Prod.fst) = true ∧
    enumVariantCountOK (.prim .u8) [(.implicit, [])] = false ∧
    (∀ v ∈ [((.implicit : DiscrSyn), ([] : List Desc))], ∀ f ∈ v.2, SemFromBytes f) ∧
    ¬ SemFromBytes (.enm (.prim .u8) [(.implicit, [])]) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro v hv f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rw [hv] at hf; cases hf
  · rw [semFromBytes_iff_validInit_total]
    intro h
    have := h [1] (by decide)
    revert this
    decide

/-- **Tightness of `hF` in R3c.** 256 variants with discriminants `0…255`, variant `0` carrying a
`bool`: well-formed and the count check passes, but not every field is `FromBytes`, and the bytes
`[0, 2]` are invalid, so the enum is not `FromBytes`. -/
theorem ce_enum_fromBytes_drop_fields :
    discrsWF (.prim .u8) (fullU8BoolVariants.map Prod.fst) = true ∧
    enumVariantCountOK (.prim .u8) fullU8BoolVariants = true ∧
    ¬ (∀ v ∈ fullU8BoolVariants, ∀ f ∈ v.2, SemFromBytes f) ∧
    ¬ SemFromBytes (.enm (.prim .u8) fullU8BoolVariants) :=
  ⟨by decide, by decide, not_all_fromBytes_fullU8BoolVariants,
    not_semFromBytes_fullU8BoolVariants⟩

/-- The enum of the `hwf` counterexamples below: variants `= ZERO { x: E }` (a non-literal
expression evaluating to `0`) and `= 0`, with `E` lacking a zero discriminant. -/
abbrev dupZeroNonLiteral : List (DiscrSyn × List Desc) := [(.other 0, [Desc.noZero]), (.lit 0, [])]

theorem not_semFromZeros_dupZeroNonLiteral : ¬ SemFromZeros (.enm (.prim .u8) dupZeroNonLiteral) := by
  rw [semFromZeros_iff_validInit_zeros]
  decide

/-- **Tightness of `hwf` in R3d (distinctness), and unsoundness of the `FromZeros` derive check
without the compiler's E0081 rule.** For `dupZeroNonLiteral` the right-hand side of R3d holds
(variant `1` has discriminant `0` and no fields), and the modeled derive check accepts, but the enum
is not `FromZeros`, because decoding selects the first variant with tag `0`. -/
theorem ce_enum_fromZeros_iff_drop_wf :
    discrsWF (.prim .u8) (dupZeroNonLiteral.map Prod.fst) = false ∧
    implFromZeros (.enm (.prim .u8) dupZeroNonLiteral) = true ∧
    ¬ (SemFromZeros (.enm (.prim .u8) dupZeroNonLiteral) ↔
        ∃ i fs, (Desc.discrs dupZeroNonLiteral)[i]? = some 0 ∧
          variantFields dupZeroNonLiteral i = some fs ∧ ∀ f ∈ fs, SemFromZeros f) := by
  refine ⟨by decide, by decide, fun hiff => not_semFromZeros_dupZeroNonLiteral
    (hiff.mpr ⟨1, [], by decide, rfl, fun f hf => by cases hf⟩)⟩

/-- **Tightness of `hwf` in R3d (representability).** `#[repr(u8)] enum { A = 256 }` (`256`
overflows `u8`): its tag code is `0`, so it is `FromZeros`, but no variant has discriminant `0`. -/
theorem ce_enum_fromZeros_iff_drop_representable :
    nodupInt (resolveDiscrs [.lit 256]) = true ∧
    discrsWF (.prim .u8) [.lit 256] = false ∧
    ¬ (SemFromZeros (.enm (.prim .u8) [(.lit 256, [])]) ↔
        ∃ i fs, (Desc.discrs [((.lit 256 : DiscrSyn), ([] : List Desc))])[i]? = some 0 ∧
          variantFields [((.lit 256 : DiscrSyn), ([] : List Desc))] i = some fs ∧
          ∀ f ∈ fs, SemFromZeros f) := by
  refine ⟨by decide, by decide, fun hiff => ?_⟩
  have hz : SemFromZeros (.enm (.prim .u8) [(.lit 256, [])]) := by
    rw [semFromZeros_iff_validInit_zeros]; decide
  obtain ⟨i, fs, h0, _, _⟩ := hiff.mp hz
  cases i with
  | zero => simp [Desc.discrs, resolveDiscrs, resolveAux] at h0
  | succ k => simp [Desc.discrs, resolveDiscrs, resolveAux] at h0

/-- **Tightness of `hwf` in `enum_fromZeros_of_findZeroVariant` (distinctness).** For
`dupZeroNonLiteral` the search returns variant `1` (it skips the non-literal first discriminant),
whose (zero) fields are `FromZeros`, but the enum is not `FromZeros`. -/
theorem ce_enum_fromZeros_of_findZeroVariant_drop_wf :
    discrsWF (.prim .u8) (dupZeroNonLiteral.map Prod.fst) = false ∧
    findZeroVariant (dupZeroNonLiteral.map Prod.fst) = .ok 1 ∧
    (∀ fs, variantFields dupZeroNonLiteral 1 = some fs → ∀ f ∈ fs, SemFromZeros f) ∧
    ¬ SemFromZeros (.enm (.prim .u8) dupZeroNonLiteral) := by
  refine ⟨by decide, rfl, ?_, not_semFromZeros_dupZeroNonLiteral⟩
  intro fs hfs f hf
  simp only [variantFields, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, Option.some.injEq] at hfs
  subst hfs; cases hf

/-- **Tightness of `hwf` in `enum_fromZeros_of_findZeroVariant` (representability).** Variants
`= 256 { x: E }` and `= 0`: distinct, but `256` overflows `u8` and its tag code is `0`; the search
returns variant `1`, whose fields are `FromZeros`, but the all-zero bytes decode as variant `0`,
whose field is not `FromZeros`. -/
theorem ce_enum_fromZeros_of_findZeroVariant_drop_representable :
    let vs : List (DiscrSyn × List Desc) := [(.lit 256, [Desc.noZero]), (.lit 0, [])]
    nodupInt (resolveDiscrs (vs.map Prod.fst)) = true ∧
    discrsWF (.prim .u8) (vs.map Prod.fst) = false ∧
    findZeroVariant (vs.map Prod.fst) = .ok 1 ∧
    (∀ fs, variantFields vs 1 = some fs → ∀ f ∈ fs, SemFromZeros f) ∧
    ¬ SemFromZeros (.enm (.prim .u8) vs) := by
  refine ⟨by decide, by decide, rfl, ?_, ?_⟩
  · intro fs hfs f hf
    simp only [variantFields, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.some.injEq] at hfs
    subst hfs; cases hf
  · rw [semFromZeros_iff_validInit_zeros]; decide

/-- **Tightness of `hF` in `enum_fromZeros_of_findZeroVariant`.** `#[repr(u8)] enum { A(E) = 0 }`
with `E` lacking a zero discriminant: well-formed, the search returns variant `0`, but its field is
not `FromZeros`, and neither is the enum. -/
theorem ce_enum_fromZeros_drop_fields :
    let vs : List (DiscrSyn × List Desc) := [(.lit 0, [Desc.noZero])]
    discrsWF (.prim .u8) (vs.map Prod.fst) = true ∧ findZeroVariant (vs.map Prod.fst) = .ok 0 ∧
    ¬ (∀ fs, variantFields vs 0 = some fs → ∀ f ∈ fs, SemFromZeros f) ∧
    ¬ SemFromZeros (.enm (.prim .u8) vs) := by
  refine ⟨by decide, rfl, fun h => not_semFromZeros_noZero (h [Desc.noZero] rfl _ (by simp)), ?_⟩
  rw [semFromZeros_iff_validInit_zeros]
  decide

/-- **Tightness of `hz` in `enum_fromZeros_of_findZeroVariant`.** `#[repr(u8)] enum { A = 1 }`:
well-formed, the search fails for every index (it returns `Err(false)`), the (zero) fields of
variant `0` are `FromZeros`, and the enum is not `FromZeros`. -/
theorem ce_enum_fromZeros_drop_findZero :
    discrsWF (.prim .u8) [.lit 1] = true ∧ findZeroVariant [.lit 1] = .error false ∧
    (∀ fs, variantFields [((.lit 1 : DiscrSyn), ([] : List Desc))] 0 = some fs →
      ∀ f ∈ fs, SemFromZeros f) ∧
    ¬ SemFromZeros Desc.noZero := by
  refine ⟨by decide, rfl, ?_, not_semFromZeros_noZero⟩
  intro fs hfs f hf
  simp only [variantFields, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hfs
  subst hfs; cases hf

/-- **Tightness of `h` in `findZeroVariant_sound`.** For `[= 1]` the search does not return
variant `0`, and variant `0` does not have discriminant `0`. -/
theorem ce_findZeroVariant_sound_drop_h :
    findZeroVariant [.lit 1] ≠ .ok 0 ∧ (resolveDiscrs [.lit 1])[0]? ≠ some 0 := by
  refine ⟨?_, by decide⟩
  rw [show findZeroVariant [DiscrSyn.lit 1] = .error false from rfl]
  intro h
  cases h

/-- **`find_zero_variant` is incomplete; tightness of `h` in
`findZeroVariant_complete_of_no_unknown`.** A single variant `= ZERO` (a non-literal expression
evaluating to `0`) has discriminant `0`, the enum is `FromZeros`, but the syntactic search fails
with `Err(true)` (not `Err(false)`), so the derive rejects it. -/
theorem findZeroVariant_incomplete_with_unknown :
    findZeroVariant [.other 0] = .error true ∧ findZeroVariant [.other 0] ≠ .error false ∧
    0 ∈ resolveDiscrs [.other 0] ∧
    implFromZeros (.enm (.prim .u8) [(.other 0, [])]) = false ∧
    SemFromZeros (.enm (.prim .u8) [(.other 0, [])]) := by
  refine ⟨rfl, ?_, by decide, by decide, ?_⟩
  · rw [show findZeroVariant [DiscrSyn.other 0] = .error true from rfl]
    intro h
    injection h with h
    cases h
  · rw [semFromZeros_iff_validInit_zeros]
    decide

/-- **`find_zero_variant` is incomplete, second form.** A non-literal discriminant *before* an
implicit one: `enum { A = MINUS_ONE, B }` resolves to `[-1, 0]`, so `B` has discriminant `0` and the
enum is `FromZeros`, but the search cannot infer `B`'s value and fails with `Err(true)` (the source's
diagnostic says a non-literal discriminant may "define or imply" the zero variant). -/
theorem findZeroVariant_incomplete_nonliteral_before_implicit :
    findZeroVariant [.other (-1), .implicit] = .error true ∧
    resolveDiscrs [.other (-1), .implicit] = [-1, 0] ∧
    implFromZeros (.enm (.prim .i8) [(.other (-1), []), (.implicit, [])]) = false ∧
    SemFromZeros (.enm (.prim .i8) [(.other (-1), []), (.implicit, [])]) := by
  refine ⟨rfl, rfl, by decide, ?_⟩
  rw [semFromZeros_iff_validInit_zeros]
  decide

/-- **Tightness of `hlen` in `enum_validInit_iff_first_matching_variant_valid`.** On bytes of the
wrong length the right-hand side holds (the tag matches a fieldless variant) but validity fails. -/
theorem ce_enum_validInit_drop_hlen :
    ([0, 5] : List Byte).length ≠ (Desc.enm (.prim .u8) [(.implicit, [])]).size ∧
    ¬ (validInit (.enm (.prim .u8) [(.implicit, [])]) [0, 5] = true ↔
        ∃ i, (Desc.codes (.prim .u8) [(.implicit, [])]).findIdx?
            (· == enumTag (.prim .u8) [(.implicit, [])] [0, 5]) = some i ∧
          validVariant [(.implicit, [])] i
            (Desc.enumLayout (.prim .u8) [(.implicit, [])]).variantFieldOffsets [0, 5] = true) := by
  refine ⟨by decide, fun hiff => ?_⟩
  have := hiff.mpr ⟨0, by decide, by decide⟩
  revert this
  decide

/-- **Tightness of `hlen` in `isSafe_enm_eq_validInit`.** On bytes of the wrong length, `is_safe`
(which never checks the length; zerocopy only calls it on correctly sized candidates) accepts what
validity rejects; the other hypotheses hold. -/
theorem ce_isSafe_enm_drop_hlen :
    let vs : List (DiscrSyn × List Desc) := [(.implicit, [])]
    discrsWF (.prim .u8) (vs.map Prod.fst) = true ∧
    (∀ v ∈ vs, ∀ f ∈ v.2, ∀ bs, bs.length = f.size → isSafe f bs = validInit f bs) ∧
    ([0, 5] : List Byte).length ≠ (Desc.enm (.prim .u8) vs).size ∧
    isSafe (.enm (.prim .u8) vs) [0, 5] ≠ validInit (.enm (.prim .u8) vs) [0, 5] := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro v hv f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rw [hv] at hf; cases hf

/-- **Tightness of `hwf` in `isSafe_enm_eq_validInit`.** With 256 duplicate-`0` fieldless variants,
the `could_be_from_bytes` shortcut makes `is_safe` accept tag `1`, which is invalid; the other
hypotheses hold. -/
theorem ce_isSafe_enm_drop_wf :
    discrsWF (.prim .u8) (dupZeroVariants.map Prod.fst) = false ∧
    (∀ v ∈ dupZeroVariants, ∀ f ∈ v.2, ∀ bs, bs.length = f.size → isSafe f bs = validInit f bs) ∧
    ([1] : List Byte).length = (Desc.enm (.prim .u8) dupZeroVariants).size ∧
    isSafe (.enm (.prim .u8) dupZeroVariants) [1] ≠
      validInit (.enm (.prim .u8) dupZeroVariants) [1] := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro v hv f hf
  simp only [dupZeroVariants, List.mem_replicate] at hv
  rw [hv.2] at hf; cases hf

/-- **Tightness of `hfields` in `isSafe_enm_eq_validInit`.** A well-formed enum whose field type is
the (ill-formed) duplicate-discriminant enum, for which `is_safe` and validity disagree. -/
theorem ce_isSafe_enm_drop_fields :
    let inner : Desc := .enm (.prim .u8) dupZeroVariants
    let vs : List (DiscrSyn × List Desc) := [(.implicit, [inner])]
    discrsWF (.prim .u8) (vs.map Prod.fst) = true ∧
    ¬ (∀ v ∈ vs, ∀ f ∈ v.2, ∀ bs, bs.length = f.size → isSafe f bs = validInit f bs) ∧
    ([0, 1] : List Byte).length = (Desc.enm (.prim .u8) vs).size ∧
    isSafe (.enm (.prim .u8) vs) [0, 1] ≠ validInit (.enm (.prim .u8) vs) [0, 1] := by
  refine ⟨by decide, fun h => ?_, by decide, by decide⟩
  have h1 := h (.implicit, [.enm (.prim .u8) dupZeroVariants]) (by simp)
    (.enm (.prim .u8) dupZeroVariants) (by simp) [1] (by decide)
  revert h1
  decide

/-- **Tightness of `hP` in R3g.** `repr(u8) enum { A(u8), B(u16) }`: `IntoBytes` fields, padding in
variant `A`, not `IntoBytes`. -/
theorem ce_enum_intoBytes_drop_padding :
    let vs : List (DiscrSyn × List Desc) := [(.implicit, [.u8]), (.implicit, [.u16])]
    (∀ v ∈ vs, ∀ f ∈ v.2, SemIntoBytes f) ∧ enumPaddingOK (.prim .u8) vs = false ∧
    ¬ SemIntoBytes (.enm (.prim .u8) vs) := by
  refine ⟨?_, by decide, ?_⟩
  · intro v hv f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;>
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      exact semIntoBytes_int _
  · rw [semIntoBytes_iff_encodeL_init]
    intro h
    have := h (.enm 0 [.int [0]]) (by decide) 2 (by decide)
    revert this
    decide

/-- **Tightness of `hF` in R3g.** `repr(u16) enum { A(Inner) }` with `Inner` the padded pair: the
enum-level padding check passes (`6 = 2 + 4`) but the field, hence the enum, is not `IntoBytes`. -/
theorem ce_enum_intoBytes_drop_fields :
    let vs : List (DiscrSyn × List Desc) := [(.implicit, [Desc.paddedPair])]
    ¬ (∀ v ∈ vs, ∀ f ∈ v.2, SemIntoBytes f) ∧ enumPaddingOK (.prim .u16) vs = true ∧
    ¬ SemIntoBytes (.enm (.prim .u16) vs) := by
  refine ⟨fun h => not_semIntoBytes_paddedPair
    (h (.implicit, [Desc.paddedPair]) (by simp) Desc.paddedPair (by simp)), by decide, ?_⟩
  rw [semIntoBytes_iff_encodeL_init]
  intro h
  have := h (.enm 0 [.strct [.int [0], .int [0, 0]]]) (by decide) 3 (by decide)
  revert this
  decide

/-! ## `find_zero_variant` in the `FromBytes` derive -/

/-- 256 fieldless `repr(u8)` variants: the first `= ZERO` (a non-literal expression that the
compiler evaluates to `0`), the remaining 255 implicit (discriminants `1, …, 255`). -/
def nonLiteralZeroFullU8 : List (DiscrSyn × List Desc) :=
  (.other 0, []) :: List.replicate 255 (.implicit, [])

/-- **The `FromBytes` derive rejects a `FromBytes` enum because it runs `find_zero_variant`.** The
enum `nonLiteralZeroFullU8` is well-formed, passes the variant-count check, and is semantically
`FromBytes` (by R3c) and `FromZeros` (by R3d), but `find_zero_variant` cannot see the non-literal
zero discriminant (it returns `Err(true)`), so the modeled `FromZeros` check, which the `FromBytes`
derive runs first, rejects it. -/
theorem fromBytes_enum_rejected_by_findZeroVariant :
    (Desc.enm (.prim .u8) nonLiteralZeroFullU8).wf = true ∧
    enumVariantCountOK (.prim .u8) nonLiteralZeroFullU8 = true ∧
    findZeroVariant (nonLiteralZeroFullU8.map Prod.fst) = .error true ∧
    SemFromBytes (.enm (.prim .u8) nonLiteralZeroFullU8) ∧
    SemFromZeros (.enm (.prim .u8) nonLiteralZeroFullU8) ∧
    implFromBytes (.enm (.prim .u8) nonLiteralZeroFullU8) = false := by
  have hwf : discrsWF (.prim .u8) (nonLiteralZeroFullU8.map Prod.fst) = true := by decide
  have hnf : ∀ v ∈ nonLiteralZeroFullU8, v.2 = [] := by
    intro v hv
    simp only [nonLiteralZeroFullU8, List.mem_cons, List.mem_replicate] at hv
    rcases hv with rfl | ⟨_, rfl⟩ <;> rfl
  refine ⟨by decide, by decide, rfl, ?_, ?_, by decide⟩
  · refine enum_fromBytes_of_count_check _ _ hwf (by decide) (fun v hv f hf => ?_)
    rw [hnf v hv] at hf
    cases hf
  · exact (enum_fromZeros_iff_zero_variant_fields_fromZeros_of_discrsWF _ _ hwf).mpr
      ⟨0, [], by decide, rfl, fun f hf => by cases hf⟩

end Toy.Zc
