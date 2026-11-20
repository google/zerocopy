import ToyRepr.Examples

/-!
# Result groups 2, 3, 5: transmute totality, round trips, composition, and validity sets

Main statements:

* `transmuteTotal_of_intoBytes_of_fromBytes` (R2a) — `IntoBytes A` and `FromBytes B` make
  `transmute A → B` total.
* `transmute_bab_roundtrip_of_total_of_intoBytes_encodeLeast_decodeEncode` (R2b) — `B → A → B`
  returns the original value when `B → A` is total, `A` is `IntoBytes` with `EncodeLeast`, and
  `B` satisfies `DecodeEncode` (no `FromBytes B`, no other law for `B`).
* `transmute_comp_of_total_of_encodeLeast_of_intoBytes` (R3) — `B → C` after `A → B` equals
  `A → C` when `A → B` is total and the middle type satisfies `EncodeLeast` and `IntoBytes`.
* `transmuteTotal_iff_image_subset_valid` (R5a) — totality is exactly "every encoding of `A`
  is in the validity set of `B`".
* `transmuteTotal_iff_valid_subset_of_laws` (R5b) — under three laws it is exactly validity-set
  inclusion over *all* abstract byte vectors (including partially uninitialized ones).
* `transmuteTotal_iff_initValid_subset_of_intoBytes_decodeEncode_encodeLeast` (R5c) — when `A`
  is `IntoBytes` and satisfies `DecodeEncode` and `EncodeLeast`, it is exactly inclusion of
  validity sets restricted to fully initialized bytes.
-/

namespace Toy.Repr

/-! ## R2a: totality -/

/-- **R2a.** For representations of equal size, if no encoding of `A` contains `uninit`
(`IntoBytes A`) and every fully initialized byte vector decodes as `B` (`FromBytes B`), then
`transmute A → B` never fails. No representation laws are assumed. -/
theorem transmuteTotal_of_intoBytes_of_fromBytes {D A B : Type} {n : Nat}
    (ra : Rep (Bytes D n) A) (rb : Rep (Bytes D n) B)
    (hA : ra.IntoBytes) (hB : rb.FromBytes) : TransmuteTotal ra rb := by
  intro a
  exact hB _ (hA a)

/-- Tightness of `hA` in R2a: a byte of pure padding transmuted to `u8` fails (`u8` is
`FromBytes`). -/
theorem transmuteTotal_of_intoBytes_of_fromBytes_tight_hA :
    u8Rep.FromBytes ∧ ¬ TransmuteTotal padUnitRep u8Rep := by
  refine ⟨u8Rep_fromBytes, fun h => ?_⟩
  obtain ⟨b, hb⟩ := h ()
  cases hb

/-- Tightness of `hB` in R2a: `u8` (which is `IntoBytes`) transmuted to the niche-carrying
`bool`-like type fails at byte value `2`. -/
theorem transmuteTotal_of_intoBytes_of_fromBytes_tight_hB :
    u8Rep.IntoBytes ∧ ¬ TransmuteTotal u8Rep boolRep :=
  ⟨u8Rep_intoBytes, ex_transmuteTotal_neg⟩

/-- Non-vacuity for R2a: two-byte integer to the padded `u8` struct. -/
theorem transmuteTotal_of_intoBytes_of_fromBytes_nonvacuous :
    (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).IntoBytes ∧ u8PadRep.FromBytes :=
  ⟨pairRep_intoBytes, u8PadRep_fromBytes⟩

/-! ## R2b: round trip `B → A → B` -/

/-- **R2b.** Let `rb`, `ra` have equal size. If `transmute B → A` is total, `A` is `IntoBytes`
and satisfies `EncodeLeast`, and `B` satisfies `DecodeEncode`, then transmuting `B → A` and back
`A → B` returns the original value, for every `b`. No law on `A` other than `EncodeLeast` is
assumed, `FromBytes B` is not assumed, and no law of `B` other than `DecodeEncode` is assumed.
(`IntoBytes B` is not a hypothesis because it already follows from the three hypotheses on totality
and on `A`: every encoding of `B` equals a fully initialized encoding of `A`;
`intoBytes_of_transmuteTotal_of_intoBytes_of_encodeLeast`.) By R2a, totality of
`B → A` holds in particular when `B` is `IntoBytes` and `A` is `FromBytes`. -/
theorem transmute_bab_roundtrip_of_total_of_intoBytes_encodeLeast_decodeEncode {D A B : Type}
    {n : Nat} (rb : Rep (Bytes D n) B) (ra : Rep (Bytes D n) A)
    (htot : TransmuteTotal rb ra) (hIB_A : ra.IntoBytes) (hEL_A : ra.EncodeLeast)
    (hDE_B : rb.DecodeEncode) :
    ∀ b : B, (transmute rb ra b).bind (transmute ra rb) = some b := by
  intro b
  obtain ⟨a, ha⟩ := htot b
  have hle : ra.encode a ⊑ rb.encode b := hEL_A (rb.encode b) a ha
  have heq : rb.encode b = ra.encode a := Bytes.eq_of_le_of_isInit hle (hIB_A a)
  rw [ha, Option.bind_some]
  change rb.decode (ra.encode a) = some b
  rw [← heq]
  exact hDE_B b

/-- Tightness of `htot` in R2b: `B` = `u8`, `A` = niche-carrying `bool`-like type; the value
`2 : u8` has no `bool` image. -/
theorem transmute_roundtrip_tight_htot :
    boolRep.IntoBytes ∧ boolRep.EncodeLeast ∧ u8Rep.DecodeEncode ∧
    ¬ (∀ b : Byte, (transmute u8Rep boolRep b).bind (transmute boolRep u8Rep) = some b) := by
  refine ⟨boolRep_intoBytes, boolRep_encodeLeast, u8Rep_decodeEncode, fun h => ?_⟩
  have := h 2
  cases this

/-- Tightness of `hIB_A` in R2b: `B` = two-byte integer, `A` = padded `u8` struct: the second
byte is lost as padding. -/
theorem transmute_roundtrip_tight_hIB_A :
    TransmuteTotal (pairRep : Rep (Bytes Byte 2) (Byte × Byte)) u8PadRep ∧
    u8PadRep.EncodeLeast ∧ (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).DecodeEncode ∧
    ¬ (∀ b : Byte × Byte,
        (transmute pairRep u8PadRep b).bind (transmute u8PadRep pairRep) = some b) := by
  refine ⟨fun b => ⟨b.1, rfl⟩, u8PadRep_encodeLeast, pairRep_decodeEncode, fun h => ?_⟩
  have := h (1, 2)
  cases this

/-- Tightness of `hEL_A` in R2b: `B` = `u8`, `A` = `boolNZRep` (every nonzero byte decodes to
`true`, which encodes as `1`); `2 ↦ true ↦ 1`. All other hypotheses hold; moreover both
representations are `IntoBytes` and `FromBytes`, both satisfy `DecodeMono` and `DecodeEncode`, and
`u8Rep` satisfies all three laws. So `IntoBytes ∧ FromBytes` on both sides, even together with
`DecodeMono` and `DecodeEncode` on both sides, does not give a lossless round trip. -/
theorem transmute_roundtrip_tight_hEL_A :
    TransmuteTotal u8Rep boolNZRep ∧ boolNZRep.IntoBytes ∧ u8Rep.DecodeEncode ∧
    (u8Rep.IntoBytes ∧ u8Rep.FromBytes ∧ boolNZRep.FromBytes ∧
      u8Rep.DecodeMono ∧ u8Rep.EncodeLeast ∧ boolNZRep.DecodeMono ∧ boolNZRep.DecodeEncode) ∧
    (transmute u8Rep boolNZRep 2).bind (transmute boolNZRep u8Rep) = some 1 ∧
    ¬ (∀ b : Byte, (transmute u8Rep boolNZRep b).bind (transmute boolNZRep u8Rep) = some b) := by
  refine ⟨fun _ => ⟨_, rfl⟩, boolNZRep_intoBytes, u8Rep_decodeEncode,
    ⟨u8Rep_intoBytes, u8Rep_fromBytes, boolNZRep_fromBytes, u8Rep_decodeMono, u8Rep_encodeLeast,
      boolNZRep_decodeMono, boolNZRep_decodeEncode⟩, rfl, fun h => ?_⟩
  have := h 2
  exact absurd this (by decide)

/-- Tightness of `hDE_B` in R2b: `B` = `u8` encoder with an always-failing decoder, `A` = `u8`. -/
theorem transmute_roundtrip_tight_hDE_B :
    TransmuteTotal (noneRep u8Rep.encode) u8Rep ∧ u8Rep.IntoBytes ∧ u8Rep.EncodeLeast ∧
    ¬ (∀ b : Byte,
        (transmute (noneRep u8Rep.encode) u8Rep b).bind (transmute u8Rep (noneRep u8Rep.encode)) =
          some b) := by
  refine ⟨fun b => ⟨b, rfl⟩, u8Rep_intoBytes, u8Rep_encodeLeast, fun h => ?_⟩
  have := h 0
  cases this

/-- Non-vacuity for R2b: `B` = niche-carrying `bool`-like type, `A` = `u8` (`bool → u8 → bool`).
All hypotheses hold, and `B` is not `FromBytes`. -/
theorem transmute_roundtrip_nonvacuous :
    TransmuteTotal boolRep u8Rep ∧ u8Rep.IntoBytes ∧ u8Rep.EncodeLeast ∧ boolRep.DecodeEncode ∧
    ¬ boolRep.FromBytes :=
  ⟨fun b => ⟨boolEnc b, rfl⟩, u8Rep_intoBytes, u8Rep_encodeLeast, boolRep_decodeEncode,
   boolRep_not_fromBytes⟩

/-- The intermediate value of the round trip is `transmute rb ra b` itself (a function of `b`);
what need not be unique is a preimage of `b` under `transmute ra rb`: with `B` = `boolNZRep` and
`A` = `u8Rep` (all hypotheses of R2b hold), `true ↦ 1 ↦ true`, and also `2 ↦ true`. Here `A`
satisfies all three laws, including `DecodeEncode`; the non-injectivity comes from `B` = `boolNZRep`
violating `EncodeLeast`. See also `transmute_roundtrip_second_step_not_injective_of_not_decodeEncode`
(omitting `DecodeEncode A` instead) and `transmute_injective_of_bab_hyps_of_decodeEncode_of_encodeLeast`
(both laws added give injectivity). -/
theorem transmute_roundtrip_second_step_not_injective :
    TransmuteTotal boolNZRep u8Rep ∧ u8Rep.IntoBytes ∧ u8Rep.EncodeLeast ∧
    boolNZRep.DecodeEncode ∧
    transmute boolNZRep u8Rep true = some 1 ∧ transmute u8Rep boolNZRep 1 = some true ∧
    transmute u8Rep boolNZRep 2 = some true :=
  ⟨fun b => ⟨boolEnc b, rfl⟩, u8Rep_intoBytes, u8Rep_encodeLeast, boolNZRep_decodeEncode,
   rfl, rfl, rfl⟩

/-- Under the hypotheses of R2b on totality and on `A`, `B` is automatically `IntoBytes`: every
encoding of `B` equals a fully initialized encoding of `A`. (This is why `IntoBytes B` is not a
hypothesis of R2b.) -/
theorem intoBytes_of_transmuteTotal_of_intoBytes_of_encodeLeast {D A B : Type} {n : Nat}
    (rb : Rep (Bytes D n) B) (ra : Rep (Bytes D n) A)
    (htot : TransmuteTotal rb ra) (hIB_A : ra.IntoBytes) (hEL_A : ra.EncodeLeast) :
    rb.IntoBytes := by
  intro b
  obtain ⟨a, ha⟩ := htot b
  have heq : rb.encode b = ra.encode a := Bytes.eq_of_le_of_isInit (hEL_A _ a ha) (hIB_A a)
  rw [heq]
  exact hIB_A a

/-- Adding `DecodeEncode A` and `EncodeLeast B` to the hypotheses of R2b makes the second step
`transmute A → B` injective on successful results. -/
theorem transmute_injective_of_bab_hyps_of_decodeEncode_of_encodeLeast {D A B : Type} {n : Nat}
    (rb : Rep (Bytes D n) B) (ra : Rep (Bytes D n) A)
    (htot : TransmuteTotal rb ra) (hIB_A : ra.IntoBytes) (hEL_A : ra.EncodeLeast)
    (hDE_A : ra.DecodeEncode) (hEL_B : rb.EncodeLeast)
    {a₁ a₂ : A} {b : B}
    (h₁ : transmute ra rb a₁ = some b) (h₂ : transmute ra rb a₂ = some b) : a₁ = a₂ := by
  have hIB_B : rb.IntoBytes :=
    intoBytes_of_transmuteTotal_of_intoBytes_of_encodeLeast rb ra htot hIB_A hEL_A
  have e₁ : ra.encode a₁ = rb.encode b := Bytes.eq_of_le_of_isInit (hEL_B _ b h₁) (hIB_B b)
  have e₂ : ra.encode a₂ = rb.encode b := Bytes.eq_of_le_of_isInit (hEL_B _ b h₂) (hIB_B b)
  exact Rep.encode_injective_of_decodeEncode ra hDE_A (e₁.trans e₂.symm)

/-- A unit type stored as `[init 0]`; only `[init 0]` decodes. Satisfies all three laws. -/
def unitZeroRep : Rep (Bytes Byte 1) Unit :=
  ⟨fun _ => #v[.init 0], fun x => if x[0] = .init 0 then some () else none⟩

/-- A `bool`-like type whose encoder sends both values to `[init 0]` and whose decoder sends
`[init 0]` to `true`: `IntoBytes` and `EncodeLeast`, but not `DecodeEncode`. -/
def constBoolZeroRep : Rep (Bytes Byte 1) Bool :=
  ⟨fun _ => #v[.init 0], fun x => if x[0] = .init 0 then some true else none⟩

/-- Omitting `DecodeEncode A` also admits a non-injective second step: with `B` = `unitZeroRep`
(all three laws) and `A` = `constBoolZeroRep`, all hypotheses of R2b hold, `B` also satisfies
`EncodeLeast`, and both `true` and `false` transmute to `()`. -/
theorem transmute_roundtrip_second_step_not_injective_of_not_decodeEncode :
    TransmuteTotal unitZeroRep constBoolZeroRep ∧
    constBoolZeroRep.IntoBytes ∧ constBoolZeroRep.EncodeLeast ∧
    unitZeroRep.DecodeMono ∧ unitZeroRep.DecodeEncode ∧ unitZeroRep.EncodeLeast ∧
    ¬ constBoolZeroRep.DecodeEncode ∧
    transmute constBoolZeroRep unitZeroRep true = some () ∧
    transmute constBoolZeroRep unitZeroRep false = some () := by
  refine ⟨fun _ => ⟨true, rfl⟩, fun _ i hi => ?_, ?_, ?_, fun _ => rfl, ?_,
    fun h => ?_, rfl, rfl⟩
  · have h0 : i = 0 := by omega
    subst h0
    rfl
  · intro x v hx i hi
    have h0 : i = 0 := by omega
    subst h0
    change (if x[0] = .init 0 then some true else none) = some v at hx
    by_cases hx0 : x[0] = .init 0
    · show (AByte.init 0 : AByte Byte) ⊑ x[0]
      rw [hx0]
      exact AByte.le_refl _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx0)] at hx
      cases hx
  · intro x y hxy
    have h0 := hxy 0 (by decide)
    change (if x[0] = .init 0 then some () else none) ⊑ (if y[0] = .init 0 then some () else none)
    by_cases hx : x[0] = .init 0
    · rw [hx] at h0
      rw [AByte.init_le_iff.mp h0, hx]
      exact OptLe.refl _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
      exact OptLe.none_le _
  · intro x v hx i hi
    have h0 : i = 0 := by omega
    subst h0
    change (if x[0] = .init 0 then some () else none) = some v at hx
    by_cases hx0 : x[0] = .init 0
    · show (AByte.init 0 : AByte Byte) ⊑ x[0]
      rw [hx0]
      exact AByte.le_refl _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx0)] at hx
      cases hx
  · have hf := h false
    cases hf

/-! ## R3: composition -/

/-- **R3.** For three representations of equal size, if `transmute A → B` is total and `B`
satisfies `EncodeLeast` and `IntoBytes`, then transmuting `A → B` and then `B → C` agrees with
transmuting `A → C` directly, for every `a`. No hypothesis on `C` is needed. -/
theorem transmute_comp_of_total_of_encodeLeast_of_intoBytes {D A B C : Type} {n : Nat}
    (ra : Rep (Bytes D n) A) (rb : Rep (Bytes D n) B) (rc : Rep (Bytes D n) C)
    (htot : TransmuteTotal ra rb) (hEL : rb.EncodeLeast) (hIB : rb.IntoBytes) :
    ∀ a : A, (transmute ra rb a).bind (transmute rb rc) = transmute ra rc a := by
  intro a
  obtain ⟨b, hb⟩ := htot a
  have heq : ra.encode a = rb.encode b := Bytes.eq_of_le_of_isInit (hEL _ b hb) (hIB b)
  rw [hb, Option.bind_some]
  change rc.decode (rb.encode b) = rc.decode (ra.encode a)
  rw [heq]

/-- Tightness of `htot` in R3: `u8 → bool → u8` at `2` fails, while `u8 → u8` succeeds. -/
theorem transmute_comp_tight_htot :
    boolRep.EncodeLeast ∧ boolRep.IntoBytes ∧
    ¬ (∀ a : Byte, (transmute u8Rep boolRep a).bind (transmute boolRep u8Rep) = transmute u8Rep u8Rep a) := by
  refine ⟨boolRep_encodeLeast, boolRep_intoBytes, fun h => ?_⟩
  have := h 2
  cases this

/-- Tightness of `hEL` in R3: `u8 → boolNZ → u8` at `2` gives `1`, while `u8 → u8` gives `2`. -/
theorem transmute_comp_tight_hEL :
    TransmuteTotal u8Rep boolNZRep ∧ boolNZRep.IntoBytes ∧
    ¬ (∀ a : Byte, (transmute u8Rep boolNZRep a).bind (transmute boolNZRep u8Rep) = transmute u8Rep u8Rep a) := by
  refine ⟨fun a => ⟨_, rfl⟩, boolNZRep_intoBytes, fun h => ?_⟩
  have := h 2
  exact absurd this (by decide)

/-- Tightness of `hIB` in R3 ("`B` has padding that `C` reads"): two-byte integer → padded
`u8` struct → two-byte integer fails, while the direct transmute succeeds. -/
theorem transmute_comp_tight_hIB :
    TransmuteTotal (pairRep : Rep (Bytes Byte 2) (Byte × Byte)) u8PadRep ∧ u8PadRep.EncodeLeast ∧
    ¬ (∀ a : Byte × Byte,
        (transmute pairRep u8PadRep a).bind (transmute u8PadRep pairRep) = transmute pairRep pairRep a) := by
  refine ⟨fun a => ⟨a.1, rfl⟩, u8PadRep_encodeLeast, fun h => ?_⟩
  have := h (1, 2)
  cases this

/-- Non-vacuity for R3: `A` = niche-carrying `bool`-like type, `B` = `u8` (any `C`). -/
theorem transmute_comp_nonvacuous :
    TransmuteTotal boolRep u8Rep ∧ u8Rep.EncodeLeast ∧ u8Rep.IntoBytes :=
  ⟨fun b => ⟨boolEnc b, rfl⟩, u8Rep_encodeLeast, u8Rep_intoBytes⟩

/-! ## R5: totality versus validity sets -/

/-- **R5a** (definitional reference point for R5b and R5c). In any carrier, `transmute A → B` is
total iff every element of the image of `A`'s encoder lies in `B`'s validity set. The proof is a
reindexing of quantifiers; the statement fixes the baseline against which R5b and R5c say when
the image may be replaced by the whole validity set of `A`. -/
theorem transmuteTotal_iff_image_subset_valid {α A B : Type} (ra : Rep α A) (rb : Rep α B) :
    TransmuteTotal ra rb ↔ ∀ x : α, ra.Image x → rb.Valid x := by
  constructor
  · rintro h x ⟨a, rfl⟩
    exact h a
  · intro h a
    exact h _ ⟨a, rfl⟩

/-- Non-vacuity for R5a: both sides hold for `u8 → u8` and both fail for `u8 → bool`. -/
theorem transmuteTotal_iff_image_subset_valid_nonvacuous :
    (TransmuteTotal u8Rep u8Rep ∧ ∀ x, u8Rep.Image x → u8Rep.Valid x) ∧
    (¬ TransmuteTotal u8Rep boolRep ∧ ¬ ∀ x, u8Rep.Image x → boolRep.Valid x) := by
  refine ⟨⟨fun a => ⟨a, rfl⟩, fun x ⟨v, hv⟩ => ⟨v, by rw [← hv]; rfl⟩⟩,
    ⟨ex_transmuteTotal_neg, fun h => ?_⟩⟩
  obtain ⟨v, hv⟩ := h #v[.init 2] ⟨2, rfl⟩
  cases hv

/-- **R5b.** In any carrier with any definedness relation: if `A` satisfies `DecodeEncode` and
`EncodeLeast` and `B` satisfies `DecodeMono`, then `transmute A → B` is total iff `A`'s
validity set is contained in `B`'s validity set. -/
theorem transmuteTotal_iff_valid_subset_of_laws {α A B : Type} [Definedness α]
    (ra : Rep α A) (rb : Rep α B)
    (hDE_A : ra.DecodeEncode) (hEL_A : ra.EncodeLeast) (hM_B : rb.DecodeMono) :
    TransmuteTotal ra rb ↔ ∀ x : α, ra.Valid x → rb.Valid x := by
  constructor
  · rintro h x ⟨a, ha⟩
    obtain ⟨b, hb⟩ := h a
    have hm := hM_B _ _ (hEL_A x a ha)
    change rb.decode (ra.encode a) = some b at hb
    rw [hb] at hm
    exact ⟨b, OptLe.some_le_iff.mp hm⟩
  · intro h a
    exact h _ ⟨a, hDE_A a⟩

/-- Tightness of `hDE_A` in R5b: with always-failing decoders on both sides, validity-set
inclusion holds vacuously but the transmute is not total. -/
theorem transmuteTotal_iff_valid_subset_tight_hDE_A :
    (noneRep u8Rep.encode).EncodeLeast ∧ (noneRep u8Rep.encode).DecodeMono ∧
    ¬ (TransmuteTotal (noneRep u8Rep.encode) (noneRep u8Rep.encode) ↔
       ∀ x, (noneRep u8Rep.encode).Valid x → (noneRep u8Rep.encode).Valid x) := by
  refine ⟨noneRep_encodeLeast _, noneRep_decodeMono _, fun h => ?_⟩
  obtain ⟨b, hb⟩ := h.mpr (fun _ hx => hx) 0
  cases hb

/-- Tightness of `hEL_A` in R5b: `boolNZ → bool` is total (encodings are `0` and `1`), but
`boolNZ` accepts `[init 2]`, which `bool` rejects. -/
theorem transmuteTotal_iff_valid_subset_tight_hEL_A :
    boolNZRep.DecodeEncode ∧ boolRep.DecodeMono ∧
    ¬ (TransmuteTotal boolNZRep boolRep ↔ ∀ x, boolNZRep.Valid x → boolRep.Valid x) := by
  refine ⟨boolNZRep_decodeEncode, boolRep_decodeMono, fun h => ?_⟩
  have htot : TransmuteTotal boolNZRep boolRep := by
    intro a
    cases a
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  obtain ⟨v, hv⟩ := h.mp htot #v[.init 2] ⟨true, rfl⟩
  cases hv

/-- Tightness of `hM_B` in R5b: padding byte → exact unit is total (`[uninit] ↦ ()`), but the
padding byte accepts `[init 0]`, which the non-monotone exact decoder rejects. -/
theorem transmuteTotal_iff_valid_subset_tight_hM_B :
    padUnitRep.DecodeEncode ∧ padUnitRep.EncodeLeast ∧
    ¬ (TransmuteTotal padUnitRep exactUnitRep ↔ ∀ x, padUnitRep.Valid x → exactUnitRep.Valid x) := by
  refine ⟨padUnitRep_decodeEncode, padUnitRep_encodeLeast, fun h => ?_⟩
  obtain ⟨v, hv⟩ := h.mp (fun _ => ⟨(), rfl⟩) #v[.init 0] ⟨(), rfl⟩
  cases hv

/-- Non-vacuity for R5b: `A` = two-byte integer, `B` = padded `u8` struct. -/
theorem transmuteTotal_iff_valid_subset_nonvacuous :
    (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).DecodeEncode ∧
    (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).EncodeLeast ∧ u8PadRep.DecodeMono :=
  ⟨pairRep_decodeEncode, pairRep_encodeLeast, u8PadRep_decodeMono⟩

/-- **R5c.** For byte-vector representations of equal size: if `A` is `IntoBytes` and satisfies
`DecodeEncode` and `EncodeLeast`, then `transmute A → B` is total iff every fully initialized
byte pattern valid for `A` is valid for `B` (inclusion of `InitValid` sets). No law on `B` is
needed. -/
theorem transmuteTotal_iff_initValid_subset_of_intoBytes_decodeEncode_encodeLeast {D A B : Type} {n : Nat}
    (ra : Rep (Bytes D n) A) (rb : Rep (Bytes D n) B)
    (hIB_A : ra.IntoBytes) (hDE_A : ra.DecodeEncode) (hEL_A : ra.EncodeLeast) :
    TransmuteTotal ra rb ↔ ∀ ds : Vector D n, ra.InitValid ds → rb.InitValid ds := by
  constructor
  · rintro h ds ⟨a, ha⟩
    obtain ⟨b, hb⟩ := h a
    have heq : Bytes.ofData ds = ra.encode a :=
      Bytes.eq_of_le_of_isInit (hEL_A _ a ha) (hIB_A a)
    refine ⟨b, ?_⟩
    change rb.decode (Bytes.ofData ds) = some b
    rw [heq]
    exact hb
  · intro h a
    obtain ⟨ds, hds⟩ := Bytes.exists_ofData_of_isInit (hIB_A a)
    have hA : ra.InitValid ds := ⟨a, by
      change ra.decode (Bytes.ofData ds) = some a
      rw [← hds]
      exact hDE_A a⟩
    obtain ⟨b, hb⟩ := h ds hA
    refine ⟨b, ?_⟩
    change rb.decode (ra.encode a) = some b
    rw [hds]
    exact hb

/-- Tightness of `hIB_A` in R5c (the initialized-only criterion is unsound for padded sources):
every initialized pattern is valid for both the padded `u8` struct and the two-byte integer,
but transmuting the padded struct to the integer always fails. -/
theorem transmuteTotal_iff_initValid_subset_tight_hIB_A :
    u8PadRep.DecodeEncode ∧ u8PadRep.EncodeLeast ∧
    ¬ (TransmuteTotal u8PadRep (pairRep : Rep (Bytes Byte 2) (Byte × Byte)) ↔
       ∀ ds : Vector Byte 2, u8PadRep.InitValid ds → (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).InitValid ds) := by
  refine ⟨u8PadRep_decodeEncode, u8PadRep_encodeLeast, fun h => ?_⟩
  have hinc : ∀ ds : Vector Byte 2, u8PadRep.InitValid ds →
      (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).InitValid ds :=
    fun ds _ => ⟨(ds[0], ds[1]), pairRep_tryFrom ds⟩
  obtain ⟨b, hb⟩ := h.mpr hinc 0
  cases hb

/-- Tightness of `hDE_A` in R5c: always-failing decoders on both sides. -/
theorem transmuteTotal_iff_initValid_subset_tight_hDE_A :
    (noneRep u8Rep.encode).IntoBytes ∧ (noneRep u8Rep.encode).EncodeLeast ∧
    ¬ (TransmuteTotal (noneRep u8Rep.encode) (noneRep u8Rep.encode) ↔
       ∀ ds : Vector Byte 1, (noneRep u8Rep.encode).InitValid ds → (noneRep u8Rep.encode).InitValid ds) := by
  refine ⟨u8Rep_intoBytes, noneRep_encodeLeast _, fun h => ?_⟩
  obtain ⟨b, hb⟩ := h.mpr (fun _ hx => hx) 0
  cases hb

/-- Tightness of `hEL_A` in R5c: `boolNZ → bool` is total, but the initialized pattern `[2]` is
valid for `boolNZ` and not for `bool`. -/
theorem transmuteTotal_iff_initValid_subset_tight_hEL_A :
    boolNZRep.IntoBytes ∧ boolNZRep.DecodeEncode ∧
    ¬ (TransmuteTotal boolNZRep boolRep ↔ ∀ ds : Vector Byte 1, boolNZRep.InitValid ds → boolRep.InitValid ds) := by
  refine ⟨boolNZRep_intoBytes, boolNZRep_decodeEncode, fun h => ?_⟩
  have htot : TransmuteTotal boolNZRep boolRep := by
    intro a
    cases a
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  have h2 : boolNZRep.InitValid #v[2] := ⟨true, by rw [boolNZRep, byteRep_tryFrom]; rfl⟩
  obtain ⟨v, hv⟩ := h.mp htot #v[2] h2
  rw [boolRep, byteRep_tryFrom] at hv
  have h7 : boolDec #v[(2 : Byte)][0] = none := by decide
  rw [h7] at hv
  cases hv

/-- Non-vacuity for R5c: `A` = two-byte integer. -/
theorem transmuteTotal_iff_initValid_subset_nonvacuous :
    (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).IntoBytes ∧
    (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).DecodeEncode ∧
    (pairRep : Rep (Bytes Byte 2) (Byte × Byte)).EncodeLeast :=
  ⟨pairRep_intoBytes, pairRep_decodeEncode, pairRep_encodeLeast⟩

end Toy.Repr
