import ToyRepr.Examples

/-!
# Result group 1: the three laws as a lower adjoint, and what they determine

Main statements:

* `threeLaws_iff_lowerAdjoint` — `DecodeMono ∧ DecodeEncode ∧ EncodeLeast` holds iff
  `∀ v x, encode v ⊑ x ↔ decode x = some v`.
* `encode_eq_iff_decodeEncode_encodeLeast` — `DecodeEncode` and `EncodeLeast` pin the encoder
  down from the decoder (`DecodeMono` is not needed).
* `decode_eq_iff_threeLaws` — all three laws pin the decoder down from the encoder.
* `encode_getElem_eq_uninit_of_decodeEncode_encodeLeast_of_decodeIgnores` (R1d) — "padding is
  `uninit`": under `DecodeEncode` and `EncodeLeast`, a byte the decoder ignores is `uninit` in
  every encoding.
* `decodeIgnores_of_threeLaws_of_encode_getElem_eq_uninit` (R1d2) — the converse, under all three
  laws.
* `eq_of_encode_le_encode_of_decodeMono_decodeEncode` (R1e) — under `DecodeMono` and
  `DecodeEncode`, comparable encodings belong to equal values (in any carrier, with any relation).

R1b and R1c are uniqueness statements. Existence fails in general:
`no_lawful_encoder_for_monotone_orUnitRep` (a monotone decoder with non-empty preimages that has
no encoder satisfying `DecodeEncode` and `EncodeLeast`) and
`no_lawful_decoder_for_conflictBoolEnc` (an injective encoder with incomparable encodings that has
no decoder satisfying `DecodeMono` and `DecodeEncode`).

Every hypothesis believed necessary has a counterexample theorem `<result>_tight_<hyp>`
stating that a concrete instance satisfies all the other hypotheses and the conclusion fails;
every main result has a non-vacuity theorem `<result>_nonvacuous`.
-/

namespace Toy.Repr

/-! ## R1a: three laws ↔ lower adjoint -/

/-- **R1a.** For a representation in byte vectors (with the pointwise definedness order), the
three laws hold together iff `encode` is a lower adjoint of `decode` in the sense
`∀ v x, encode v ⊑ x ↔ decode x = some v`. -/
theorem threeLaws_iff_lowerAdjoint {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) :
    (r.DecodeMono ∧ r.DecodeEncode ∧ r.EncodeLeast) ↔ r.LowerAdjoint := by
  constructor
  · rintro ⟨hM, hDE, hEL⟩ v x
    constructor
    · intro h
      have hm := hM _ _ h
      rw [hDE v] at hm
      exact OptLe.some_le_iff.mp hm
    · exact hEL x v
  · intro h
    refine ⟨fun x y hxy => ?_, fun v => (h v _).mp (Bytes.le_refl _), fun x v hx => (h v x).mpr hx⟩
    cases hx : r.decode x with
    | none => exact OptLe.none_le _
    | some v =>
      have hy : r.decode y = some v := (h v y).mp (Bytes.le_trans ((h v x).mpr hx) hxy)
      rw [hy]
      exact OptLe.refl _

/-- Non-vacuity for R1a: both sides hold for `u8Rep`, and both sides fail for `boolNZRep`
(so the equivalence relates non-trivial properties). -/
theorem threeLaws_iff_lowerAdjoint_nonvacuous :
    ((u8Rep.DecodeMono ∧ u8Rep.DecodeEncode ∧ u8Rep.EncodeLeast) ∧ u8Rep.LowerAdjoint) ∧
    (¬ (boolNZRep.DecodeMono ∧ boolNZRep.DecodeEncode ∧ boolNZRep.EncodeLeast) ∧
      ¬ boolNZRep.LowerAdjoint) :=
  ⟨⟨⟨u8Rep_decodeMono, u8Rep_decodeEncode, u8Rep_encodeLeast⟩, ex_lowerAdjoint_pos⟩,
   ⟨fun h => boolNZRep_not_encodeLeast h.2.2, ex_lowerAdjoint_neg⟩⟩

/-! ## R1b: the encoder is determined by the decoder -/

/-- **R1b.** If `r` satisfies `DecodeEncode` and `EncodeLeast`, then an encoder `e` satisfies
both laws against the same decoder iff `e = r.encode`. So `encode v` is the unique
`⊑`-least byte vector that decodes to `v`; `DecodeMono` plays no role. -/
theorem encode_eq_iff_decodeEncode_encodeLeast {D V : Type} {n : Nat} (r : Rep (Bytes D n) V)
    (hDE : r.DecodeEncode) (hEL : r.EncodeLeast) (e : V → Bytes D n) :
    ((⟨e, r.decode⟩ : Rep (Bytes D n) V).DecodeEncode ∧
      (⟨e, r.decode⟩ : Rep (Bytes D n) V).EncodeLeast) ↔ e = r.encode := by
  constructor
  · rintro ⟨hDE', hEL'⟩
    funext v
    exact Bytes.le_antisymm (hEL' (r.encode v) v (hDE v)) (hEL (e v) v (hDE' v))
  · rintro rfl
    exact ⟨hDE, hEL⟩

/-- Tightness of `hDE` in R1b: the always-failing decoder satisfies `EncodeLeast` vacuously,
and for `e := r.encode` the right side holds while the left side fails. -/
theorem encode_eq_iff_decodeEncode_encodeLeast_tight_hDE :
    (noneRep u8Rep.encode).EncodeLeast ∧
    ¬ (((⟨u8Rep.encode, (noneRep u8Rep.encode).decode⟩ : Rep (Bytes Byte 1) Byte).DecodeEncode ∧
        (⟨u8Rep.encode, (noneRep u8Rep.encode).decode⟩ : Rep (Bytes Byte 1) Byte).EncodeLeast) ↔
       u8Rep.encode = (noneRep u8Rep.encode).encode) := by
  refine ⟨noneRep_encodeLeast _, fun h => ?_⟩
  have := (h.mpr rfl).1 0
  cases this

/-- Tightness of `hEL` in R1b: `u8PadInitRep` (padding written as `init 0`) satisfies
`DecodeEncode`; the encoder of `u8PadRep` (padding left `uninit`) satisfies both laws against the
same decoder but differs from `u8PadInitRep.encode`. -/
theorem encode_eq_iff_decodeEncode_encodeLeast_tight_hEL :
    u8PadInitRep.DecodeEncode ∧
    ¬ (((⟨u8PadRep.encode, u8PadInitRep.decode⟩ : Rep (Bytes Byte 2) Byte).DecodeEncode ∧
        (⟨u8PadRep.encode, u8PadInitRep.decode⟩ : Rep (Bytes Byte 2) Byte).EncodeLeast) ↔
       u8PadRep.encode = u8PadInitRep.encode) := by
  refine ⟨u8PadInitRep_decodeEncode, fun h => ?_⟩
  have heq := h.mp ⟨u8PadRep_decodeEncode, u8PadRep_encodeLeast⟩
  have := congrArg (fun f => (f (0 : Byte))[1]) heq
  cases this

/-- Non-vacuity for R1b: `u8PadRep` satisfies both hypotheses. -/
theorem encode_eq_iff_decodeEncode_encodeLeast_nonvacuous :
    u8PadRep.DecodeEncode ∧ u8PadRep.EncodeLeast :=
  ⟨u8PadRep_decodeEncode, u8PadRep_encodeLeast⟩

/-! ## R1c: the decoder is determined by the encoder -/

/-- **R1c.** If `r` satisfies all three laws, then a decoder `d` makes `⟨r.encode, d⟩` satisfy
all three laws iff `d = r.decode`. -/
theorem decode_eq_iff_threeLaws {D V : Type} {n : Nat} (r : Rep (Bytes D n) V)
    (hM : r.DecodeMono) (hDE : r.DecodeEncode) (hEL : r.EncodeLeast)
    (d : Bytes D n → Option V) :
    ((⟨r.encode, d⟩ : Rep (Bytes D n) V).DecodeMono ∧
      (⟨r.encode, d⟩ : Rep (Bytes D n) V).DecodeEncode ∧
      (⟨r.encode, d⟩ : Rep (Bytes D n) V).EncodeLeast) ↔ d = r.decode := by
  constructor
  · intro h'
    have hA := (threeLaws_iff_lowerAdjoint r).mp ⟨hM, hDE, hEL⟩
    have hA' := (threeLaws_iff_lowerAdjoint ⟨r.encode, d⟩).mp h'
    funext x
    apply Option.ext
    intro v
    exact (hA' v x).symm.trans (hA v x)
  · rintro rfl
    exact ⟨hM, hDE, hEL⟩

/-- Tightness of `hM` in R1c: `exactUnitRep` satisfies `DecodeEncode` and `EncodeLeast`; the
total decoder of `padUnitRep` is lawful with the same encoder but differs from
`exactUnitRep.decode`. -/
theorem decode_eq_iff_threeLaws_tight_hM :
    exactUnitRep.DecodeEncode ∧ exactUnitRep.EncodeLeast ∧
    ¬ (((⟨exactUnitRep.encode, padUnitRep.decode⟩ : Rep (Bytes Byte 1) Unit).DecodeMono ∧
        (⟨exactUnitRep.encode, padUnitRep.decode⟩ : Rep (Bytes Byte 1) Unit).DecodeEncode ∧
        (⟨exactUnitRep.encode, padUnitRep.decode⟩ : Rep (Bytes Byte 1) Unit).EncodeLeast) ↔
       padUnitRep.decode = exactUnitRep.decode) := by
  refine ⟨exactUnitRep_decodeEncode, exactUnitRep_encodeLeast, fun h => ?_⟩
  have heq := h.mp ⟨padUnitRep_decodeMono, padUnitRep_decodeEncode, padUnitRep_encodeLeast⟩
  have := congrFun heq #v[.init 0]
  cases this

/-- Tightness of `hEL` in R1c: `boolNZRep` satisfies `DecodeMono` and `DecodeEncode`; the
decoder of `boolRep` is lawful with the same encoder but differs from `boolNZRep.decode`. -/
theorem decode_eq_iff_threeLaws_tight_hEL :
    boolNZRep.DecodeMono ∧ boolNZRep.DecodeEncode ∧
    ¬ (((⟨boolNZRep.encode, boolRep.decode⟩ : Rep (Bytes Byte 1) Bool).DecodeMono ∧
        (⟨boolNZRep.encode, boolRep.decode⟩ : Rep (Bytes Byte 1) Bool).DecodeEncode ∧
        (⟨boolNZRep.encode, boolRep.decode⟩ : Rep (Bytes Byte 1) Bool).EncodeLeast) ↔
       boolRep.decode = boolNZRep.decode) := by
  refine ⟨boolNZRep_decodeMono, boolNZRep_decodeEncode, fun h => ?_⟩
  have heq := h.mp ⟨boolRep_decodeMono, boolRep_decodeEncode, boolRep_encodeLeast⟩
  have := congrFun heq #v[.init 2]
  exact absurd this (by decide)

/-- Tightness of `hDE` in R1c: the always-failing decoder with `boolRep`'s encoder satisfies
`DecodeMono` and `EncodeLeast`; `boolRep.decode` is lawful with that encoder but is not the
always-failing decoder. -/
theorem decode_eq_iff_threeLaws_tight_hDE :
    (noneRep boolRep.encode).DecodeMono ∧ (noneRep boolRep.encode).EncodeLeast ∧
    ¬ (((⟨(noneRep boolRep.encode).encode, boolRep.decode⟩ : Rep (Bytes Byte 1) Bool).DecodeMono ∧
        (⟨(noneRep boolRep.encode).encode, boolRep.decode⟩ : Rep (Bytes Byte 1) Bool).DecodeEncode ∧
        (⟨(noneRep boolRep.encode).encode, boolRep.decode⟩ : Rep (Bytes Byte 1) Bool).EncodeLeast) ↔
       boolRep.decode = (noneRep boolRep.encode).decode) := by
  refine ⟨noneRep_decodeMono _, noneRep_encodeLeast _, fun h => ?_⟩
  have heq := h.mp ⟨boolRep_decodeMono, boolRep_decodeEncode, boolRep_encodeLeast⟩
  have := congrFun heq #v[.init 0]
  exact absurd this (by decide)

/-- Non-vacuity for R1c: `boolRep` satisfies all three hypotheses. -/
theorem decode_eq_iff_threeLaws_nonvacuous :
    boolRep.DecodeMono ∧ boolRep.DecodeEncode ∧ boolRep.EncodeLeast :=
  ⟨boolRep_decodeMono, boolRep_decodeEncode, boolRep_encodeLeast⟩

/-! ## R1d: padding is `uninit` -/

/-- **R1d.** Under `DecodeEncode` and `EncodeLeast`, if `decode` ignores byte `i` (overwriting
byte `i` never changes the decoding), then byte `i` of every encoding is `uninit`. -/
theorem encode_getElem_eq_uninit_of_decodeEncode_encodeLeast_of_decodeIgnores {D V : Type} {n : Nat} (r : Rep (Bytes D n) V)
    (hDE : r.DecodeEncode) (hEL : r.EncodeLeast) (i : Nat) (hi : i < n)
    (hIgn : r.DecodeIgnores i hi) (v : V) : (r.encode v)[i] = .uninit := by
  have hd : r.decode ((r.encode v).set i .uninit hi) = some v := by
    rw [hIgn]
    exact hDE v
  have hle := hEL _ v hd i hi
  rw [Vector.getElem_set_self] at hle
  exact AByte.le_uninit_iff.mp hle

/-- Tightness of `hDE` in R1d: an always-failing decoder ignores every byte and satisfies
`EncodeLeast` vacuously, yet its encoder writes `init 0`. -/
theorem encode_getElem_eq_uninit_of_decodeIgnores_tight_hDE :
    (noneRep (fun _ : Unit => (#v[.init 0] : Bytes Byte 1))).EncodeLeast ∧
    (noneRep (fun _ : Unit => (#v[.init 0] : Bytes Byte 1))).DecodeIgnores 0 (by decide) ∧
    ((noneRep (fun _ : Unit => (#v[.init 0] : Bytes Byte 1))).encode ())[0] ≠ .uninit :=
  ⟨noneRep_encodeLeast _, fun _ _ => rfl, fun h => by cases h⟩

/-- Tightness of `hEL` in R1d: `u8PadInitRep` satisfies `DecodeEncode` and ignores byte 1, but
writes `init 0` there. -/
theorem encode_getElem_eq_uninit_of_decodeIgnores_tight_hEL :
    u8PadInitRep.DecodeEncode ∧ u8PadInitRep.DecodeIgnores 1 (by decide) ∧
    (u8PadInitRep.encode 0)[1] ≠ .uninit :=
  ⟨u8PadInitRep_decodeEncode, u8PadInitRep_decodeIgnores_one, fun h => by cases h⟩

/-- Tightness of `hIgn` in R1d: `u8Rep` satisfies `DecodeEncode` and `EncodeLeast`, and byte 0
(which its decoder reads) is initialized in every encoding. -/
theorem encode_getElem_eq_uninit_of_decodeIgnores_tight_hIgn :
    u8Rep.DecodeEncode ∧ u8Rep.EncodeLeast ∧ (u8Rep.encode 0)[0] ≠ .uninit :=
  ⟨u8Rep_decodeEncode, u8Rep_encodeLeast, fun h => by cases h⟩

/-- Non-vacuity for R1d: `u8PadRep` satisfies all hypotheses at `i = 1`. -/
theorem encode_getElem_eq_uninit_of_decodeIgnores_nonvacuous :
    u8PadRep.DecodeEncode ∧ u8PadRep.EncodeLeast ∧ u8PadRep.DecodeIgnores 1 (by decide) :=
  ⟨u8PadRep_decodeEncode, u8PadRep_encodeLeast, u8PadRep_decodeIgnores_one⟩

/-! ## R1d2: the converse, under all three laws -/

/-- **R1d2.** Under all three laws, if byte `i` is `uninit` in every encoding, then `decode`
ignores byte `i`. Together with R1d: for a lawful representation, the bytes the decoder ignores
are exactly the bytes that are `uninit` in every encoding. -/
theorem decodeIgnores_of_threeLaws_of_encode_getElem_eq_uninit {D V : Type} {n : Nat} (r : Rep (Bytes D n) V)
    (hM : r.DecodeMono) (hDE : r.DecodeEncode) (hEL : r.EncodeLeast) (i : Nat) (hi : i < n)
    (hU : ∀ v : V, (r.encode v)[i] = .uninit) : r.DecodeIgnores i hi := by
  have hA := (threeLaws_iff_lowerAdjoint r).mp ⟨hM, hDE, hEL⟩
  intro x b
  apply Option.ext
  intro v
  rw [← hA v, ← hA v]
  constructor
  · intro h j hj
    by_cases hij : i = j
    · subst hij
      rw [hU v]
      exact AByte.uninit_le _
    · have hj' := h j hj
      rwa [Vector.getElem_set_ne _ _ hij] at hj'
  · intro h j hj
    by_cases hij : i = j
    · subst hij
      rw [hU v]
      exact AByte.uninit_le _
    · rw [Vector.getElem_set_ne _ _ hij]
      exact h j hj

/-- A unit type whose encoding is `[uninit]` but whose decoder accepts only `[init 0]`:
monotone and `EncodeLeast`, not `DecodeEncode`. -/
def initZeroUnitRep : Rep (Bytes Byte 1) Unit :=
  ⟨fun _ => #v[.uninit], fun x => if x[0] = .init 0 then some () else none⟩

/-- A unit type encoded as `[init 0, uninit]` whose decoder accepts `[init 0, _]` and, in
addition, the single vector `[init 5, init 7]`: monotone and `DecodeEncode`, not `EncodeLeast`. -/
def extraUnitRep : Rep (Bytes Byte 2) Unit :=
  ⟨fun _ => #v[.init 0, .uninit],
   fun x => if x[0] = .init 0 then some ()
     else if x[0] = .init 5 ∧ x[1] = .init 7 then some () else none⟩

/-- Tightness of `hM` in R1d2: `exactUnitRep` satisfies `DecodeEncode` and `EncodeLeast`, its
encoding is `uninit` at byte 0, yet its decoder reads byte 0. -/
theorem decodeIgnores_of_encode_uninit_tight_hM :
    exactUnitRep.DecodeEncode ∧ exactUnitRep.EncodeLeast ∧
    (∀ v : Unit, (exactUnitRep.encode v)[0] = .uninit) ∧
    ¬ exactUnitRep.DecodeIgnores 0 (by decide) := by
  refine ⟨exactUnitRep_decodeEncode, exactUnitRep_encodeLeast, fun _ => rfl, fun h => ?_⟩
  have := h #v[.uninit] (.init 0)
  cases this

/-- Tightness of `hDE` in R1d2: `initZeroUnitRep`. -/
theorem decodeIgnores_of_encode_uninit_tight_hDE :
    initZeroUnitRep.DecodeMono ∧ initZeroUnitRep.EncodeLeast ∧
    (∀ v : Unit, (initZeroUnitRep.encode v)[0] = .uninit) ∧
    ¬ initZeroUnitRep.DecodeIgnores 0 (by decide) := by
  refine ⟨?_, fun x _ _ => Bytes.uninit_le x, fun _ => rfl, fun h => ?_⟩
  · intro x y hxy
    have h0 : x[0] ⊑ y[0] := hxy 0 (by decide)
    show (if x[0] = .init 0 then some () else none) ⊑ (if y[0] = .init 0 then some () else none)
    by_cases hx : x[0] = .init 0
    · rw [hx] at h0
      rw [AByte.init_le_iff.mp h0, hx]
      exact OptLe.refl _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
      exact OptLe.none_le _
  · have := h #v[.uninit] (.init 0)
    cases this

/-- Tightness of `hEL` in R1d2: `extraUnitRep` (byte 1 is `uninit` in the encoding, but the
extra accepted vector `[init 5, init 7]` makes the decoder read byte 1). -/
theorem decodeIgnores_of_encode_uninit_tight_hEL :
    extraUnitRep.DecodeMono ∧ extraUnitRep.DecodeEncode ∧
    (∀ v : Unit, (extraUnitRep.encode v)[1] = .uninit) ∧
    ¬ extraUnitRep.DecodeIgnores 1 (by decide) := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, fun h => ?_⟩
  · intro x y hxy
    have h0 : x[0] ⊑ y[0] := hxy 0 (by decide)
    have h1 : x[1] ⊑ y[1] := hxy 1 (by decide)
    show (if x[0] = .init 0 then some () else if x[0] = .init 5 ∧ x[1] = .init 7 then some () else none) ⊑
      (if y[0] = .init 0 then some () else if y[0] = .init 5 ∧ y[1] = .init 7 then some () else none)
    by_cases hx0 : x[0] = .init 0
    · rw [hx0] at h0
      rw [AByte.init_le_iff.mp h0, hx0]
      exact OptLe.refl _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx0)]
      by_cases hx : x[0] = .init 5 ∧ x[1] = .init 7
      · rw [hx.1] at h0
        rw [hx.2] at h1
        rw [AByte.init_le_iff.mp h0, AByte.init_le_iff.mp h1, hx.1, hx.2]
        exact OptLe.refl _
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
        exact OptLe.none_le _
  · have := h #v[.init 5, .init 7] (.init 8)
    revert this
    decide

/-- Tightness of `hU` in R1d2: `u8Rep` satisfies all three laws and its decoder reads byte 0
(which is initialized in every encoding). -/
theorem decodeIgnores_of_encode_uninit_tight_hU :
    u8Rep.DecodeMono ∧ u8Rep.DecodeEncode ∧ u8Rep.EncodeLeast ∧
    ¬ u8Rep.DecodeIgnores 0 (by decide) := by
  refine ⟨u8Rep_decodeMono, u8Rep_decodeEncode, u8Rep_encodeLeast, fun h => ?_⟩
  have := h #v[.init 1] .uninit
  cases this

/-- Non-vacuity for R1d2: `u8PadRep` at byte 1 satisfies all hypotheses. -/
theorem decodeIgnores_of_encode_uninit_nonvacuous :
    u8PadRep.DecodeMono ∧ u8PadRep.DecodeEncode ∧ u8PadRep.EncodeLeast ∧
    (∀ v : Byte, (u8PadRep.encode v)[1] = .uninit) :=
  ⟨u8PadRep_decodeMono, u8PadRep_decodeEncode, u8PadRep_encodeLeast, fun _ => rfl⟩

/-! ## R1e: comparable encodings belong to equal values -/

/-- **R1e.** In any carrier with any definedness relation, `DecodeMono` and `DecodeEncode`
imply that `encode v ⊑ encode w` only when `v = w`: distinct values have incomparable
encodings. (Injectivity of the encoder is a separate and weaker fact that follows from
`DecodeEncode` alone, `Rep.encode_injective_of_decodeEncode`; for a non-reflexive relation the
conclusion here does not imply it.) -/
theorem eq_of_encode_le_encode_of_decodeMono_decodeEncode {α V : Type} [Definedness α]
    (r : Rep α V) (hM : r.DecodeMono) (hDE : r.DecodeEncode) :
    ∀ v w : V, r.encode v ⊑ r.encode w → v = w := by
  intro v w h
  have hm := hM _ _ h
  rw [hDE v, hDE w] at hm
  exact (Option.some.inj (OptLe.some_le_iff.mp hm)).symm

/-- Tightness of `hM` in R1e: `boolUninitRep` satisfies `DecodeEncode`, and its encodings of
`false` and `true` are comparable. -/
theorem eq_of_encode_le_encode_tight_hM :
    boolUninitRep.DecodeEncode ∧
    ¬ (∀ v w : Bool, boolUninitRep.encode v ⊑ boolUninitRep.encode w → v = w) := by
  refine ⟨boolUninitRep_decodeEncode, fun h => ?_⟩
  have := h false true (Bytes.le_one trivial)
  cases this

/-- Tightness of `hDE` in R1e: the always-failing decoder with `boolUninitRep`'s encoder is
monotone, and the two encodings are comparable. -/
theorem eq_of_encode_le_encode_tight_hDE :
    (noneRep boolUninitRep.encode).DecodeMono ∧
    ¬ (∀ v w : Bool,
        (noneRep boolUninitRep.encode).encode v ⊑ (noneRep boolUninitRep.encode).encode w →
        v = w) := by
  refine ⟨noneRep_decodeMono _, fun h => ?_⟩
  have := h false true (Bytes.le_one trivial)
  cases this

/-- Non-vacuity for R1e: `u8Rep` satisfies both hypotheses. -/
theorem eq_of_encode_le_encode_nonvacuous : u8Rep.DecodeMono ∧ u8Rep.DecodeEncode :=
  ⟨u8Rep_decodeMono, u8Rep_decodeEncode⟩

/-! ## Boundaries of R1b, R1c, R1d2 (fully proved) -/

/-- Decoder of a two-byte unit type accepting a vector when either byte is `init 0` (a
disjunctive validity condition, as for an untagged union of two one-byte variants). -/
def orUnitDec (x : Bytes Byte 2) : Option Unit :=
  if x[0] = .init 0 ∨ x[1] = .init 0 then some () else none

/-- Positive example: `[init 0, uninit]` is accepted. -/
theorem ex_orUnitDec_pos : orUnitDec #v[.init 0, .uninit] = some () := by decide

/-- Negative example: `[uninit, uninit]` is rejected. -/
theorem ex_orUnitDec_neg : orUnitDec #v[.uninit, .uninit] = none := by decide

/-- Boundary of R1b (uniqueness, not existence): `orUnitDec` is monotone for every encoder and
has a non-empty preimage, yet no encoder satisfies `DecodeEncode` and `EncodeLeast` against it
(the two minimal accepted vectors `[init 0, uninit]` and `[uninit, init 0]` have no common lower
bound in the preimage). -/
theorem no_lawful_encoder_for_monotone_orUnitRep :
    (∀ e : Unit → Bytes Byte 2, (⟨e, orUnitDec⟩ : Rep (Bytes Byte 2) Unit).DecodeMono) ∧
    orUnitDec #v[.init 0, .uninit] = some () ∧
    ∀ e : Unit → Bytes Byte 2,
      ¬ ((⟨e, orUnitDec⟩ : Rep (Bytes Byte 2) Unit).DecodeEncode ∧
         (⟨e, orUnitDec⟩ : Rep (Bytes Byte 2) Unit).EncodeLeast) := by
  refine ⟨fun e x y hxy => ?_, ex_orUnitDec_pos, fun e ⟨hDE, hEL⟩ => ?_⟩
  · show orUnitDec x ⊑ orUnitDec y
    by_cases hx : x[0] = .init 0 ∨ x[1] = .init 0
    · have hy : y[0] = .init 0 ∨ y[1] = .init 0 := by
        rcases hx with h | h
        · have h0 := hxy 0 (by decide)
          rw [h] at h0
          exact Or.inl (AByte.init_le_iff.mp h0)
        · have h1 := hxy 1 (by decide)
          rw [h] at h1
          exact Or.inr (AByte.init_le_iff.mp h1)
      unfold orUnitDec
      rw [ite_eq_left_of_eq_true _ _ (eq_true hx), ite_eq_left_of_eq_true _ _ (eq_true hy)]
      exact OptLe.refl _
    · unfold orUnitDec
      rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
      exact OptLe.none_le _
  · have h1 : (e ())[1] ⊑ (AByte.uninit : AByte Byte) :=
      hEL #v[.init 0, .uninit] () ex_orUnitDec_pos 1 (by decide)
    have h0 : (e ())[0] ⊑ (AByte.uninit : AByte Byte) :=
      hEL #v[.uninit, .init 0] () (show orUnitDec #v[.uninit, .init 0] = some () by decide) 0 (by decide)
    have hd : orUnitDec (e ()) = some () := hDE ()
    unfold orUnitDec at hd
    rw [AByte.le_uninit_iff.mp h0, AByte.le_uninit_iff.mp h1] at hd
    exact absurd hd (by decide)

/-- An injective `bool` encoder with incomparable encodings that have a common upper bound. -/
def conflictBoolEnc (b : Bool) : Bytes Byte 2 :=
  if b then #v[.init 0, .uninit] else #v[.uninit, .init 0]

/-- Boundary of R1c (uniqueness, not existence): `conflictBoolEnc` is injective and its two
encodings are incomparable, yet no decoder satisfies `DecodeMono` and `DecodeEncode` with it,
because both encodings lie below `[init 0, init 0]`. -/
theorem no_lawful_decoder_for_conflictBoolEnc :
    Function.Injective conflictBoolEnc ∧
    (∀ v w : Bool, conflictBoolEnc v ⊑ conflictBoolEnc w → v = w) ∧
    ∀ d : Bytes Byte 2 → Option Bool,
      ¬ ((⟨conflictBoolEnc, d⟩ : Rep (Bytes Byte 2) Bool).DecodeMono ∧
         (⟨conflictBoolEnc, d⟩ : Rep (Bytes Byte 2) Bool).DecodeEncode) := by
  refine ⟨?_, by decide, fun d ⟨hM, hDE⟩ => ?_⟩
  · show ∀ a b : Bool, conflictBoolEnc a = conflictBoolEnc b → a = b
    decide
  · have ht := hM (conflictBoolEnc true) #v[.init 0, .init 0] (by decide)
    have hf := hM (conflictBoolEnc false) #v[.init 0, .init 0] (by decide)
    have ht' : d (conflictBoolEnc true) = some true := hDE true
    have hf' : d (conflictBoolEnc false) = some false := hDE false
    change d (conflictBoolEnc true) ⊑ d #v[.init 0, .init 0] at ht
    change d (conflictBoolEnc false) ⊑ d #v[.init 0, .init 0] at hf
    rw [ht'] at ht
    rw [hf'] at hf
    have e1 := OptLe.some_le_iff.mp ht
    have e2 := OptLe.some_le_iff.mp hf
    rw [e1] at e2
    cases e2

/-- Boundary of R1d2: for an uninhabited value type, every byte is ignored by every decoder
(and, vacuously, `uninit` in every encoding), independently of any field layout. -/
theorem decodeIgnores_of_empty {D : Type} {n : Nat} (r : Rep (Bytes D n) Empty) (i : Nat)
    (hi : i < n) : r.DecodeIgnores i hi := by
  intro x b
  cases h1 : r.decode (x.set i b hi) with
  | some e => exact e.elim
  | none =>
    cases h2 : r.decode x with
    | some e => exact e.elim
    | none => rfl

end Toy.Repr
