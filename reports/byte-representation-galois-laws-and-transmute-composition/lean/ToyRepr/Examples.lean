import ToyRepr.Basic

/-!
# Concrete representations used as examples, witnesses, and counterexamples

All concrete instances use `Byte := UInt8` as the payload of an initialized byte.

| name            | size | values         | encoder                         | decoder                                   | intent |
|-----------------|------|----------------|---------------------------------|-------------------------------------------|--------|
| `u8Rep`         | 1    | `UInt8`        | `[init b]`                      | `[init b] ↦ b`                            | an integer byte: lawful, `IntoBytes`, `FromBytes` |
| `boolRep`       | 1    | `Bool`         | `[init 0]`, `[init 1]`          | only `0`, `1` decode                      | a type with a niche: lawful, not `FromBytes` |
| `boolNZRep`     | 1    | `Bool`         | `[init 0]`, `[init 1]`          | `[init b] ↦ (b ≠ 0)`                      | violates `EncodeLeast` only |
| `padUnitRep`    | 1    | `Unit`         | `[uninit]`                      | always `some ()`                          | a byte of pure padding: lawful, not `IntoBytes` |
| `exactUnitRep`  | 1    | `Unit`         | `[uninit]`                      | only `[uninit]` decodes                   | violates `DecodeMono` only |
| `boolUninitRep` | 1    | `Bool`         | `[uninit]`, `[init 0]`          | exact inverse of the encoder              | comparable encodings; violates `DecodeMono` |
| `u8PadRep`      | 2    | `UInt8`        | `[init b, uninit]`              | reads byte 0, ignores byte 1              | a `repr(C)` struct `{u8}` padded to 2 bytes |
| `u8PadInitRep`  | 2    | `UInt8`        | `[init b, init 0]`              | as `u8PadRep`                             | padding written as zero: violates `EncodeLeast` |
| `pairRep`       | 2    | `UInt8 × UInt8`| `[init a, init b]`              | both bytes must be initialized            | a two-byte integer: lawful, `IntoBytes`, `FromBytes` |
| `noneRep enc`   | any  | any            | `enc`                           | always `none`                             | violates `DecodeEncode` (if `V` is inhabited) |
-/

namespace Toy.Repr

/-- The byte payload used by all concrete examples. -/
abbrev Byte := UInt8

/-! ## Generic single-byte representations -/

section ByteRep

variable {D V : Type}

/-- A one-byte representation given by a byte-level encoder `enc` and partial decoder `dec`;
an `uninit` byte never decodes. -/
def byteRep (enc : V → D) (dec : D → Option V) : Rep (Bytes D 1) V where
  encode v := #v[.init (enc v)]
  decode x := match x[0] with
    | .init b => dec b
    | .uninit => none

theorem byteRep_decode (enc : V → D) (dec : D → Option V) (x : Bytes D 1) :
    (byteRep enc dec).decode x = (match x[0] with | .init b => dec b | .uninit => none) := rfl

theorem byteRep_tryFrom (enc : V → D) (dec : D → Option V) (ds : Vector D 1) :
    (byteRep enc dec).tryFrom ds = dec ds[0] := by
  rw [Rep.tryFrom, byteRep_decode, Bytes.getElem_ofData]

theorem byteRep_decodeMono (enc : V → D) (dec : D → Option V) : (byteRep enc dec).DecodeMono := by
  intro x y hxy
  have h0 : x[0] ⊑ y[0] := hxy 0 (by decide)
  rw [byteRep_decode, byteRep_decode]
  cases hx : x[0] with
  | uninit => exact OptLe.none_le _
  | init b =>
    rw [hx] at h0
    rw [AByte.init_le_iff.mp h0]
    exact OptLe.refl _

theorem byteRep_decodeEncode_iff (enc : V → D) (dec : D → Option V) :
    (byteRep enc dec).DecodeEncode ↔ ∀ v, dec (enc v) = some v := Iff.rfl

theorem byteRep_encodeLeast_iff (enc : V → D) (dec : D → Option V) :
    (byteRep enc dec).EncodeLeast ↔ ∀ b v, dec b = some v → enc v = b := by
  constructor
  · intro h b v hb
    have := h #v[.init b] v hb 0 (by decide)
    exact (AByte.init_le_init_iff _ _).mp this
  · intro h x v hx i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [byteRep_decode] at hx
    show (AByte.init (enc v) : AByte D) ⊑ x[0]
    revert hx
    cases x[0] with
    | uninit => intro hx; cases hx
    | init b => intro hx; rw [h b v hx]; exact AByte.le_refl _

theorem byteRep_intoBytes (enc : V → D) (dec : D → Option V) : (byteRep enc dec).IntoBytes := by
  intro v i hi
  have hi0 : i = 0 := by omega
  subst hi0
  rfl

theorem byteRep_fromBytes_iff (enc : V → D) (dec : D → Option V) :
    (byteRep enc dec).FromBytes ↔ ∀ b, ∃ v, dec b = some v := by
  constructor
  · intro h b
    exact h #v[.init b] (Bytes.isInit_one rfl)
  · intro h x hx
    rw [byteRep_decode]
    have := hx 0 (by decide)
    revert this
    cases x[0] with
    | uninit => intro h'; cases h'
    | init b => intro _; exact h b

end ByteRep

/-! ## Concrete one-byte representations -/

/-- An integer byte (`u8`): every initialized byte is a valid value. -/
def u8Rep : Rep (Bytes Byte 1) Byte := byteRep id some

/-- Encoder for a `bool`-like type: `false ↦ 0`, `true ↦ 1`. -/
def boolEnc (b : Bool) : Byte := if b then 1 else 0

/-- Decoder for a `bool`-like type: only `0` and `1` are valid (the other 254 byte values are
a *niche*). -/
def boolDec (x : Byte) : Option Bool :=
  if x = 0 then some false else if x = 1 then some true else none

/-- A `bool`-like type with a niche. -/
def boolRep : Rep (Bytes Byte 1) Bool := byteRep boolEnc boolDec

/-- A deliberately non-canonical `bool`-like type: every nonzero byte decodes to `true`,
but `true` is encoded as `1`. -/
def boolNZRep : Rep (Bytes Byte 1) Bool := byteRep boolEnc (fun x => some (x != 0))

theorem u8Rep_decodeMono : u8Rep.DecodeMono := byteRep_decodeMono _ _
theorem u8Rep_decodeEncode : u8Rep.DecodeEncode := fun _ => rfl
theorem u8Rep_encodeLeast : u8Rep.EncodeLeast :=
  (byteRep_encodeLeast_iff _ _).mpr fun _ _ h => by cases h; rfl
theorem u8Rep_intoBytes : u8Rep.IntoBytes := byteRep_intoBytes _ _
theorem u8Rep_fromBytes : u8Rep.FromBytes :=
  (byteRep_fromBytes_iff _ _).mpr fun b => ⟨b, rfl⟩

theorem boolRep_decodeMono : boolRep.DecodeMono := byteRep_decodeMono _ _
theorem boolRep_decodeEncode : boolRep.DecodeEncode := by
  rw [boolRep, byteRep_decodeEncode_iff]
  decide
theorem boolRep_encodeLeast : boolRep.EncodeLeast := by
  rw [boolRep, byteRep_encodeLeast_iff]
  intro b v h
  unfold boolDec at h
  by_cases h0 : b = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)] at h
    cases h
    rw [h0]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)] at h
    by_cases h1 : b = 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at h
      cases h
      rw [h1]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at h
      cases h
theorem boolRep_intoBytes : boolRep.IntoBytes := byteRep_intoBytes _ _
theorem boolRep_not_fromBytes : ¬ boolRep.FromBytes := by
  intro h
  obtain ⟨v, hv⟩ := h #v[.init 2] (Bytes.isInit_one rfl)
  cases hv

theorem boolNZRep_decodeMono : boolNZRep.DecodeMono := byteRep_decodeMono _ _
theorem boolNZRep_decodeEncode : boolNZRep.DecodeEncode := by
  rw [boolNZRep, byteRep_decodeEncode_iff]
  decide
theorem boolNZRep_not_encodeLeast : ¬ boolNZRep.EncodeLeast := by
  intro h
  have := h #v[.init 2] true rfl 0 (by decide)
  exact absurd ((AByte.init_le_init_iff _ _).mp this) (by decide)
theorem boolNZRep_intoBytes : boolNZRep.IntoBytes := byteRep_intoBytes _ _
theorem boolNZRep_fromBytes : boolNZRep.FromBytes :=
  (byteRep_fromBytes_iff _ _).mpr fun _ => ⟨_, rfl⟩

/-- One byte of pure padding: the unit type stored in one byte that is never read. -/
def padUnitRep : Rep (Bytes Byte 1) Unit := ⟨fun _ => #v[.uninit], fun _ => some ()⟩

/-- Like `padUnitRep`, but the decoder accepts only the exact encoding `[uninit]`. -/
def exactUnitRep : Rep (Bytes Byte 1) Unit :=
  ⟨fun _ => #v[.uninit], fun x => match x[0] with | .uninit => some () | .init _ => none⟩

theorem padUnitRep_decodeMono : padUnitRep.DecodeMono := fun _ _ _ => OptLe.refl _
theorem padUnitRep_decodeEncode : padUnitRep.DecodeEncode := fun _ => rfl
theorem padUnitRep_encodeLeast : padUnitRep.EncodeLeast := fun x _ _ => Bytes.uninit_le x
theorem padUnitRep_not_intoBytes : ¬ padUnitRep.IntoBytes := fun h => by
  have := h () 0 (by decide)
  cases this
theorem padUnitRep_fromBytes : padUnitRep.FromBytes := fun _ _ => ⟨(), rfl⟩

theorem exactUnitRep_decodeEncode : exactUnitRep.DecodeEncode := fun _ => rfl
theorem exactUnitRep_encodeLeast : exactUnitRep.EncodeLeast := fun x _ _ => Bytes.uninit_le x
theorem exactUnitRep_not_decodeMono : ¬ exactUnitRep.DecodeMono := by
  intro h
  have := h #v[.uninit] #v[.init 0] (Bytes.le_one trivial)
  exact this

/-- A `bool`-like type whose two encodings are comparable: `false ↦ [uninit]`,
`true ↦ [init 0]`; the decoder is the exact inverse of the encoder. -/
def boolUninitRep : Rep (Bytes Byte 1) Bool :=
  ⟨fun b => if b then #v[.init 0] else #v[.uninit],
   fun x => match x[0] with
    | .uninit => some false
    | .init b => if b = 0 then some true else none⟩

theorem boolUninitRep_decodeEncode : boolUninitRep.DecodeEncode := by
  intro v
  cases v <;> rfl
theorem boolUninitRep_not_decodeMono : ¬ boolUninitRep.DecodeMono := by
  intro h
  have := h #v[.uninit] #v[.init 0] (Bytes.le_one trivial)
  exact absurd this (by decide)

/-! ## Two-byte representations -/

section PadRep

variable {D V : Type}

/-- A two-byte representation storing the value in byte 0; byte 1 is padding: the decoder
ignores it and the encoder writes `pad` there. -/
def padRep (enc : V → D) (dec : D → Option V) (pad : AByte D) : Rep (Bytes D 2) V where
  encode v := #v[.init (enc v), pad]
  decode x := match x[0] with
    | .init b => dec b
    | .uninit => none

theorem padRep_decode (enc : V → D) (dec : D → Option V) (pad : AByte D) (x : Bytes D 2) :
    (padRep enc dec pad).decode x = (match x[0] with | .init b => dec b | .uninit => none) := rfl

theorem padRep_tryFrom (enc : V → D) (dec : D → Option V) (pad : AByte D) (ds : Vector D 2) :
    (padRep enc dec pad).tryFrom ds = dec ds[0] := by
  rw [Rep.tryFrom, padRep_decode, Bytes.getElem_ofData]

theorem padRep_decodeMono (enc : V → D) (dec : D → Option V) (pad : AByte D) :
    (padRep enc dec pad).DecodeMono := by
  intro x y hxy
  have h0 : x[0] ⊑ y[0] := hxy 0 (by decide)
  rw [padRep_decode, padRep_decode]
  cases hx : x[0] with
  | uninit => exact OptLe.none_le _
  | init b =>
    rw [hx] at h0
    rw [AByte.init_le_iff.mp h0]
    exact OptLe.refl _

theorem padRep_decodeIgnores (enc : V → D) (dec : D → Option V) (pad : AByte D) :
    (padRep enc dec pad).DecodeIgnores 1 (by decide) := by
  intro x b
  rw [padRep_decode, padRep_decode]
  rw [Vector.getElem_set]
  rfl

end PadRep

/-- A `repr(C)`-style struct holding one `u8` followed by one byte of padding; the encoder
leaves the padding `uninit`. -/
def u8PadRep : Rep (Bytes Byte 2) Byte := padRep id some .uninit

/-- As `u8PadRep`, but the encoder writes the padding byte as `init 0`. -/
def u8PadInitRep : Rep (Bytes Byte 2) Byte := padRep id some (.init 0)

theorem u8PadRep_decodeMono : u8PadRep.DecodeMono := padRep_decodeMono _ _ _
theorem u8PadRep_decodeEncode : u8PadRep.DecodeEncode := fun _ => rfl
theorem u8PadRep_encodeLeast : u8PadRep.EncodeLeast := by
  intro x v hx i hi
  rw [u8PadRep, padRep_decode] at hx
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · show (AByte.init v : AByte Byte) ⊑ x[0]
    revert hx
    cases x[0] with
    | uninit => intro hx; cases hx
    | init b => intro hx; cases hx; exact AByte.le_refl _
  · exact AByte.uninit_le _
theorem u8PadRep_fromBytes : u8PadRep.FromBytes := by
  intro x hx
  rw [u8PadRep, padRep_decode]
  have := hx 0 (by decide)
  revert this
  cases x[0] with
  | uninit => intro h'; cases h'
  | init b => intro _; exact ⟨b, rfl⟩
theorem u8PadRep_not_intoBytes : ¬ u8PadRep.IntoBytes := fun h => by
  have := h 0 1 (by decide)
  cases this
theorem u8PadRep_decodeIgnores_one : u8PadRep.DecodeIgnores 1 (by decide) :=
  padRep_decodeIgnores _ _ _

theorem u8PadInitRep_decodeMono : u8PadInitRep.DecodeMono := padRep_decodeMono _ _ _
theorem u8PadInitRep_decodeEncode : u8PadInitRep.DecodeEncode := fun _ => rfl
theorem u8PadInitRep_not_encodeLeast : ¬ u8PadInitRep.EncodeLeast := by
  intro h
  have := h #v[.init 5, .uninit] 5 rfl 1 (by decide)
  exact this
theorem u8PadInitRep_decodeIgnores_one : u8PadInitRep.DecodeIgnores 1 (by decide) :=
  padRep_decodeIgnores _ _ _
theorem u8PadInitRep_intoBytes : u8PadInitRep.IntoBytes := by
  intro v i hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl

section PairRep

variable {D : Type}

/-- A two-byte value made of two initialized bytes (a two-byte integer; byte order is
irrelevant here). -/
def pairRep : Rep (Bytes D 2) (D × D) where
  encode p := #v[.init p.1, .init p.2]
  decode x := match x[0], x[1] with
    | .init a, .init b => some (a, b)
    | _, _ => none

theorem pairRep_decode (x : Bytes D 2) :
    (pairRep : Rep (Bytes D 2) (D × D)).decode x =
      (match x[0], x[1] with | .init a, .init b => some (a, b) | _, _ => none) := rfl

theorem pairRep_tryFrom (ds : Vector D 2) :
    (pairRep : Rep (Bytes D 2) (D × D)).tryFrom ds = some (ds[0], ds[1]) := by
  rw [Rep.tryFrom, pairRep_decode, Bytes.getElem_ofData, Bytes.getElem_ofData]

theorem pairRep_decodeMono : (pairRep : Rep (Bytes D 2) (D × D)).DecodeMono := by
  intro x y hxy
  have h0 : x[0] ⊑ y[0] := hxy 0 (by decide)
  have h1 : x[1] ⊑ y[1] := hxy 1 (by decide)
  rw [pairRep_decode, pairRep_decode]
  cases hx0 : x[0] with
  | uninit => exact OptLe.none_le _
  | init a =>
    cases hx1 : x[1] with
    | uninit => exact OptLe.none_le _
    | init b =>
      rw [hx0] at h0
      rw [hx1] at h1
      rw [AByte.init_le_iff.mp h0, AByte.init_le_iff.mp h1]
      exact OptLe.refl _

theorem pairRep_decodeEncode : (pairRep : Rep (Bytes D 2) (D × D)).DecodeEncode := fun _ => rfl

theorem pairRep_encodeLeast : (pairRep : Rep (Bytes D 2) (D × D)).EncodeLeast := by
  intro x v hx i hi
  rw [pairRep_decode] at hx
  have key : x[0] = .init v.1 ∧ x[1] = .init v.2 := by
    revert hx
    cases x[0] with
    | uninit => intro hx; cases hx
    | init a =>
      cases x[1] with
      | uninit => intro hx; cases hx
      | init b => intro hx; cases hx; exact ⟨rfl, rfl⟩
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · show (AByte.init v.1 : AByte D) ⊑ x[0]
    rw [key.1]
    exact AByte.le_refl _
  · show (AByte.init v.2 : AByte D) ⊑ x[1]
    rw [key.2]
    exact AByte.le_refl _

theorem pairRep_intoBytes : (pairRep : Rep (Bytes D 2) (D × D)).IntoBytes := by
  intro v i hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl

theorem pairRep_fromBytes : (pairRep : Rep (Bytes D 2) (D × D)).FromBytes := by
  intro x hx
  rw [pairRep_decode]
  have h0 := hx 0 (by decide)
  have h1 := hx 1 (by decide)
  revert h0 h1
  cases x[0] with
  | uninit => intro h0; cases h0
  | init a =>
    cases x[1] with
    | uninit => intro _ h1; cases h1
    | init b => intro _ _; exact ⟨(a, b), rfl⟩

end PairRep

/-- A representation whose decoder always fails. -/
def noneRep {α V : Type} (enc : V → α) : Rep α V := ⟨enc, fun _ => none⟩

theorem noneRep_decodeMono {α V : Type} [Definedness α] (enc : V → α) :
    (noneRep enc).DecodeMono := fun _ _ _ => trivial
theorem noneRep_encodeLeast {α V : Type} [Definedness α] (enc : V → α) :
    (noneRep enc).EncodeLeast := fun _ _ h => by cases h
theorem noneRep_not_decodeEncode {α V : Type} (enc : V → α) (v : V) :
    ¬ (noneRep enc).DecodeEncode := fun h => by cases h v

/-! ## Positive and negative examples for each definition -/

section DefinitionExamples

/-! ### `AByte.le` and the byte-vector order -/

theorem ex_abyte_le_pos : (AByte.uninit : AByte Byte) ⊑ .init 5 ∧ (AByte.init 5 : AByte Byte) ⊑ .init 5 :=
  ⟨trivial, rfl⟩

theorem ex_abyte_le_neg : ¬ ((AByte.init 5 : AByte Byte) ⊑ .init 6) ∧ ¬ ((AByte.init 5 : AByte Byte) ⊑ .uninit) :=
  ⟨by decide, fun h => h⟩

theorem ex_bytes_le_pos : (#v[.uninit, .init 1] : Bytes Byte 2) ⊑ #v[.init 0, .init 1] := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact trivial
  · exact rfl

theorem ex_bytes_le_neg : ¬ ((#v[.init 0, .uninit] : Bytes Byte 2) ⊑ #v[.uninit, .uninit]) :=
  fun h => h 0 (by decide)

/-! ### `Bytes.IsInit`, `Bytes.toData?` -/

theorem ex_isInit_pos : Bytes.IsInit (#v[.init 1, .init 2] : Bytes Byte 2) :=
  Bytes.isInit_two (x := (#v[.init 1, .init 2] : Bytes Byte 2)) rfl rfl

theorem ex_isInit_neg : ¬ Bytes.IsInit (#v[.init 1, .uninit] : Bytes Byte 2) :=
  fun h => by cases h 1 (by decide)

theorem ex_toData?_pos : Bytes.toData? (#v[.init 1, .init 2] : Bytes Byte 2) = some #v[1, 2] := by
  rw [← Bytes.ofData_pair]
  exact Bytes.toData?_ofData _

theorem ex_toData?_neg : Bytes.toData? (#v[.init 1, .uninit] : Bytes Byte 2) = none :=
  Bytes.toData?_eq_none_of_not_isInit ex_isInit_neg

/-! ### `OptLe` -/

theorem ex_optLe_pos : (none : Option Byte) ⊑ some 3 ∧ (some 3 : Option Byte) ⊑ some 3 :=
  ⟨trivial, rfl⟩

theorem ex_optLe_neg : ¬ ((some 3 : Option Byte) ⊑ some 4) ∧ ¬ ((some 3 : Option Byte) ⊑ none) :=
  ⟨by decide, fun h => h⟩

/-! ### The three laws and the lower-adjoint form -/

theorem ex_decodeMono_pos : u8Rep.DecodeMono := u8Rep_decodeMono
theorem ex_decodeMono_neg : ¬ exactUnitRep.DecodeMono := exactUnitRep_not_decodeMono

theorem ex_decodeMonoBy_pos : u8Rep.DecodeMonoBy (fun o o' => o ⊑ o') :=
  (Rep.decodeMono_iff_decodeMonoBy _).mp u8Rep_decodeMono
theorem ex_decodeMonoBy_neg : ¬ exactUnitRep.DecodeMonoBy (fun o o' => o ⊑ o') :=
  fun h => exactUnitRep_not_decodeMono ((Rep.decodeMono_iff_decodeMonoBy _).mpr h)

theorem ex_decodeEncode_pos : u8Rep.DecodeEncode := u8Rep_decodeEncode
theorem ex_decodeEncode_neg : ¬ (noneRep u8Rep.encode).DecodeEncode :=
  noneRep_not_decodeEncode _ 0

theorem ex_encodeLeast_pos : u8PadRep.EncodeLeast := u8PadRep_encodeLeast
theorem ex_encodeLeast_neg : ¬ u8PadInitRep.EncodeLeast := u8PadInitRep_not_encodeLeast

theorem ex_lowerAdjoint_pos : u8Rep.LowerAdjoint := by
  intro v x
  constructor
  · intro h
    have h0 := h 0 (by decide)
    rw [u8Rep, byteRep_decode]
    rw [AByte.init_le_iff.mp h0]
    rfl
  · intro h
    exact u8Rep_encodeLeast x v h

theorem ex_lowerAdjoint_neg : ¬ boolNZRep.LowerAdjoint := by
  intro h
  have := (h true #v[.init 2]).mpr rfl 0 (by decide)
  exact absurd ((AByte.init_le_init_iff _ _).mp this) (by decide)

theorem ex_liftEncode_pos : u8PadRep.liftEncode (some 7) = #v[.init 7, .uninit] := rfl

theorem ex_liftEncode_neg : u8PadRep.liftEncode none ≠ #v[.init 0, .uninit] := fun h => by
  have := congrArg (fun x : Bytes Byte 2 => x[0]) h
  simp [Rep.liftEncode, Bytes.uninit] at this

/-! ### `DecodeIgnores` -/

theorem ex_decodeIgnores_pos : u8PadRep.DecodeIgnores 1 (by decide) := u8PadRep_decodeIgnores_one

theorem ex_decodeIgnores_neg : ¬ u8PadRep.DecodeIgnores 0 (by decide) := by
  intro h
  have := h #v[.init 5, .uninit] .uninit
  cases this

/-! ### `IntoBytes`, `FromBytes`, `tryFrom`, `asBytes` -/

theorem ex_intoBytes_pos : u8Rep.IntoBytes ∧ (pairRep : Rep (Bytes Byte 2) _).IntoBytes :=
  ⟨u8Rep_intoBytes, pairRep_intoBytes⟩
theorem ex_intoBytes_neg : ¬ u8PadRep.IntoBytes ∧ ¬ padUnitRep.IntoBytes :=
  ⟨u8PadRep_not_intoBytes, padUnitRep_not_intoBytes⟩

theorem ex_fromBytes_pos : u8Rep.FromBytes ∧ u8PadRep.FromBytes := ⟨u8Rep_fromBytes, u8PadRep_fromBytes⟩
theorem ex_fromBytes_neg : ¬ boolRep.FromBytes := boolRep_not_fromBytes

theorem ex_tryFrom_pos : boolRep.tryFrom #v[1] = some true := by
  rw [Rep.tryFrom, boolRep, byteRep_decode, Bytes.getElem_ofData]
  decide
theorem ex_tryFrom_neg : boolRep.tryFrom #v[2] = none := by
  rw [Rep.tryFrom, boolRep, byteRep_decode, Bytes.getElem_ofData]
  decide

theorem ex_asBytes_pos : pairRep.asBytes pairRep_intoBytes ((7 : Byte), (9 : Byte)) = #v[7, 9] := rfl

/-! ### `Valid`, `InitValid`, `Image` -/

theorem ex_valid_pos : u8PadRep.Valid #v[.init 4, .init 9] := ⟨4, rfl⟩
theorem ex_valid_neg : ¬ u8PadRep.Valid #v[.uninit, .init 9] := fun ⟨_, h⟩ => by cases h

theorem ex_initValid_pos : boolRep.InitValid #v[0] := ⟨false, by
  rw [Rep.tryFrom, boolRep, byteRep_decode, Bytes.getElem_ofData]
  decide⟩
theorem ex_initValid_neg : ¬ boolRep.InitValid #v[7] := fun ⟨v, h⟩ => by
  rw [Rep.tryFrom, boolRep, byteRep_decode, Bytes.getElem_ofData] at h
  have h7 : boolDec #v[(7 : Byte)][0] = none := by decide
  simp only [h7] at h
  cases h

theorem ex_image_pos : u8PadRep.Image #v[.init 4, .uninit] := ⟨4, rfl⟩
theorem ex_image_neg : ¬ u8PadRep.Image #v[.init 4, .init 9] := fun ⟨_, h⟩ => by
  have := congrArg (fun x : Bytes Byte 2 => x[1]) h
  cases this

/-! ### `transmute` and `TransmuteTotal` -/

theorem ex_transmute_pos : transmute u8Rep boolRep 1 = some true := rfl
theorem ex_transmute_neg : transmute u8Rep boolRep 2 = none := rfl

theorem ex_transmuteTotal_pos : TransmuteTotal u8Rep u8Rep := fun a => ⟨a, rfl⟩
theorem ex_transmuteTotal_neg : ¬ TransmuteTotal u8Rep boolRep := fun h => by
  obtain ⟨b, hb⟩ := h 2
  cases hb

end DefinitionExamples

end Toy.Repr
