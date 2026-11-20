import ToyRepr.Examples

/-!
# Result group 6: bytes carrying provenance

Initialized bytes now carry a byte value and an optional provenance tag:
`AByte (β × Option P)`. An *integer* of `n` bytes is a `Vector β n`; a *pointer* of `n` bytes is
an address `Vector β n` together with an optional provenance `Option P` (a toy raw thin pointer;
a pointer without provenance is a valid value but grants no access). Pointer results are stated
for pointer sizes `n + 1 ≥ 1`: at size `0` the canonical pointer encoder forgets the provenance
(`no_ptr_decodeEncode_size_zero`).

Canonical encoders: `intEncode` writes the integer's bytes with no provenance; `ptrEncode`
writes the address bytes, each tagged with the pointer's provenance. Modeling gap: tags carry
no byte position (MiniRust records the position of each byte inside a pointer fragment, Cerberus
an index `0..sizeof-1`), so the strict pointer decoder accepts duplicated or permuted bytes of a
pointer (`ex_ptrDecodeStrict_accepts_duplicated_byte`).

Two ways to order provenance-carrying bytes:

* **Provenance as data** (`PBytes β P n = Bytes (β × Option P) n`, the flat order of
  `ToyRepr.Basic`): `init (b, q) ⊑ init (b', q')` iff `(b, q) = (b', q')`. All generic results of
  groups 1–5 apply verbatim, because they are stated for an arbitrary payload type `D`.
* **Provenance increases definedness** (`PBytesInc β P n`, order `AByte.leProvInc`):
  `init (b, none) ⊑ init (b', q)` iff `b = b'`, and `init (b, some p) ⊑ init (b', q)` iff
  `b = b' ∧ q = some p` — the byte order used by MiniRust (without byte positions).

Main statements:

* `int_ptr_int_roundtrip_of_decodeEncode` (R6a) — integer → pointer → integer is lossless
  whenever both decoders satisfy `DecodeEncode` (independent of the order).
* `ptr_intStrip_ptr_roundtrip_drops_provenance_of_decodeEncode` (R6b, fully proved) — with the
  provenance-stripping integer decoder and any pointer decoder satisfying `DecodeEncode`,
  pointer → integer → pointer replaces the provenance by `none`.
* `no_int_decoder_encodeLeast_fromBytes_of_provenance` (R6c, impossibility) — with provenance
  as data, no decoder for the canonical integer encoder satisfies both `EncodeLeast` and
  `FromBytes` (over bytes that may carry provenance).
* `no_optProvPtr_decoder_decodeMono_decodeEncode_of_provInc` (R6d, impossibility) — when
  provenance increases definedness, no decoder for the canonical encoder of pointers with
  *optional* provenance satisfies both `DecodeMono` (flat `Option` order) and `DecodeEncode`.
* `transmute_comp_fails_of_provInc` (R6e, fully proved counterexample) — with provenance
  increasing definedness, the composition law R3 fails although all three representations
  satisfy all three laws and the middle type's encodings are fully initialized.

Escape hatches, fully proved: integers whose values carry provenance (`provIntRep_escape_hatch`,
for R6c); pointers that always carry provenance (`reqProvPtrRepInc_threeLaws`, for R6d); and a
MiniRust-style non-flat value order with a decoder that degrades missing or mixed provenance to
`none` (`ptrDegradeRepInc_lawful_by_ptrValLe`, for R6d).
-/

namespace Toy.Repr

section Prov

variable {β P : Type} {n : Nat}

/-- Provenance-carrying byte vectors, ordered with provenance as part of the data (flat). -/
abbrev PBytes (β P : Type) (n : Nat) := Bytes (β × Option P) n

/-- Canonical integer encoder: the integer's bytes, without provenance. -/
def intEncode (x : Vector β n) : PBytes β P n := Bytes.ofData (x.map fun b => (b, none))

/-- Canonical pointer encoder: the address bytes, each tagged with the pointer's provenance. -/
def ptrEncode (p : Vector β n × Option P) : PBytes β P n := Bytes.ofData (p.1.map fun b => (b, p.2))

/-- Provenance-stripping integer decoder: succeeds on every fully initialized vector and
forgets provenance. -/
def intDecodeStrip (x : PBytes β P n) : Option (Vector β n) :=
  x.toData?.map (Vector.map Prod.fst)

/-- Provenance-rejecting integer decoder: succeeds only on fully initialized vectors whose bytes
carry no provenance. -/
def intDecodeStrict (x : PBytes β P n) : Option (Vector β n) :=
  match x.toData? with
  | some ds => if ∀ (i : Nat) (h : i < n), (ds[i].2).isNone = true then some (ds.map Prod.fst) else none
  | none => none

/-- Strict pointer decoder (size `n + 1`): succeeds iff all bytes are initialized and carry the
same provenance `q` (possibly `none`, giving a pointer without provenance); mixed provenance
fails. -/
def ptrDecodeStrict [DecidableEq P] (x : PBytes β P (n + 1)) : Option (Vector β (n + 1) × Option P) :=
  match x.toData? with
  | some ds => if ∀ (i : Nat) (h : i < n + 1), ds[i].2 = ds[0].2 then some (ds.map Prod.fst, ds[0].2) else none
  | none => none

/-- Pointer decoder that requires provenance (size `n + 1`): succeeds iff all bytes are initialized
and carry the same `some p`; bytes without provenance never decode as a pointer. -/
def ptrDecodeReqProv [DecidableEq P] (x : PBytes β P (n + 1)) : Option (Vector β (n + 1) × Option P) :=
  match x.toData? with
  | some ds =>
    if (ds[0].2).isSome = true ∧ ∀ (i : Nat) (h : i < n + 1), ds[i].2 = ds[0].2 then
      some (ds.map Prod.fst, ds[0].2) else none
  | none => none

/-- Integers with the provenance-stripping decoder. -/
def intStripRep : Rep (PBytes β P n) (Vector β n) := ⟨intEncode, intDecodeStrip⟩

/-- Integers with the provenance-rejecting decoder. -/
def intStrictRep : Rep (PBytes β P n) (Vector β n) := ⟨intEncode, intDecodeStrict⟩

/-- Pointers with the strict (uniform-provenance) decoder. -/
def ptrStrictRep [DecidableEq P] : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P) :=
  ⟨ptrEncode, ptrDecodeStrict⟩

/-- Pointers whose decoder requires provenance. -/
def ptrReqProvRep [DecidableEq P] : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P) :=
  ⟨ptrEncode, ptrDecodeReqProv⟩

/-! ### The provenance-increasing order -/

/-- Byte order in which adding provenance makes a byte more defined:
`uninit ⊑ x`; `init (b, none) ⊑ init (b', q)` iff `b = b'`;
`init (b, some p) ⊑ init (b', q)` iff `b = b' ∧ q = some p`; `init _ ⋢ uninit`. -/
def AByte.leProvInc : AByte (β × Option P) → AByte (β × Option P) → Prop
  | .uninit, _ => True
  | .init (a, none), .init (b, _) => a = b
  | .init (a, some p), .init (b, q) => a = b ∧ q = some p
  | .init _, .uninit => False

/-- Provenance-carrying byte vectors ordered pointwise by `AByte.leProvInc`. -/
structure PBytesInc (β P : Type) (n : Nat) where
  /-- The underlying byte vector. -/
  bytes : PBytes β P n

instance : Definedness (PBytesInc β P n) :=
  ⟨fun x y => ∀ (i : Nat) (h : i < n), AByte.leProvInc x.bytes[i] y.bytes[i]⟩

theorem PBytesInc.le_refl (x : PBytesInc β P n) : x ⊑ x := by
  intro i hi
  cases x.bytes[i] with
  | uninit => exact trivial
  | init d => obtain ⟨b, q⟩ := d; cases q <;> simp [AByte.leProvInc]

theorem PBytesInc.le_trans {x y z : PBytesInc β P n} (hxy : x ⊑ y) (hyz : y ⊑ z) : x ⊑ z := by
  intro i hi
  have h1 := hxy i hi
  have h2 := hyz i hi
  revert h1 h2
  cases x.bytes[i] with
  | uninit => intros; exact trivial
  | init dx =>
    cases y.bytes[i] with
    | uninit => obtain ⟨_, qx⟩ := dx; cases qx <;> simp [AByte.leProvInc]
    | init dy =>
      cases z.bytes[i] with
      | uninit =>
        obtain ⟨_, qx⟩ := dx; obtain ⟨_, qy⟩ := dy; cases qx <;> cases qy <;> simp [AByte.leProvInc]
      | init dz =>
        obtain ⟨bx, qx⟩ := dx; obtain ⟨by_, qy⟩ := dy; obtain ⟨bz, qz⟩ := dz
        cases qx <;> cases qy <;> cases qz <;> simp [AByte.leProvInc]
        · intro h1 h2; exact h1.trans h2
        · intro h1 h2; exact h1.trans h2
        · intro h1 h2 _; exact h1.trans h2
        · intro h1 hp1 h2 hp2; exact ⟨h1.trans h2, hp2.trans hp1⟩

theorem PBytesInc.le_antisymm {x y : PBytesInc β P n} (hxy : x ⊑ y) (hyx : y ⊑ x) : x = y := by
  cases x with | mk xb =>
  cases y with | mk yb =>
  congr 1
  apply Vector.ext
  intro i hi
  have h1 := hxy i hi
  have h2 := hyx i hi
  revert h1 h2
  cases xb[i] with
  | uninit =>
    cases yb[i] with
    | uninit => intros; rfl
    | init dy => obtain ⟨_, qy⟩ := dy; cases qy <;> simp [AByte.leProvInc]
  | init dx =>
    cases yb[i] with
    | uninit => obtain ⟨_, qx⟩ := dx; cases qx <;> simp [AByte.leProvInc]
    | init dy =>
      obtain ⟨bx, qx⟩ := dx; obtain ⟨by_, qy⟩ := dy
      cases qx with
      | none =>
        cases qy with
        | none => intro h1 _; simp [AByte.leProvInc] at h1; rw [h1]
        | some py => intro _ h2; simp [AByte.leProvInc] at h2
      | some px =>
        cases qy with
        | none => intro h1 _; simp [AByte.leProvInc] at h1
        | some py =>
          intro h1 _
          simp [AByte.leProvInc] at h1
          rcases h1 with ⟨hb, hp⟩
          rw [hb, hp]

/-- Canonical pointer encoder into `PBytesInc`. -/
def ptrEncodeInc (p : Vector β n × Option P) : PBytesInc β P n := ⟨ptrEncode p⟩

/-- Canonical integer encoder into `PBytesInc`. -/
def intEncodeInc (x : Vector β n) : PBytesInc β P n := ⟨intEncode x⟩

/-- Provenance-stripping integers over `PBytesInc`. -/
def intStripRepInc : Rep (PBytesInc β P n) (Vector β n) := ⟨intEncodeInc, fun x => intDecodeStrip x.bytes⟩

/-- Provenance-rejecting integers over `PBytesInc`. -/
def intStrictRepInc : Rep (PBytesInc β P n) (Vector β n) := ⟨intEncodeInc, fun x => intDecodeStrict x.bytes⟩

/-- Strict pointers over `PBytesInc`. -/
def ptrStrictRepInc [DecidableEq P] : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P) :=
  ⟨ptrEncodeInc, fun x => ptrDecodeStrict x.bytes⟩

/-! ### Basic lemmas (proved) -/

theorem toData?_eq_some_iff {D : Type} {m : Nat} (x : Bytes D m) (ds : Vector D m) :
    x.toData? = some ds ↔ x = Bytes.ofData ds :=
  ⟨Bytes.ofData_of_toData?, fun h => h ▸ Bytes.toData?_ofData ds⟩

theorem intEncode_eq_ptrEncode_none (x : Vector β n) :
    (intEncode x : PBytes β P n) = ptrEncode (x, none) := rfl

theorem intEncode_singleton (b : β) : (intEncode #v[b] : PBytes β P 1) = #v[.init (b, none)] := by
  apply Vector.ext
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp [intEncode]

theorem ptrEncode_singleton (b : β) (q : Option P) :
    (ptrEncode (#v[b], q) : PBytes β P 1) = #v[.init (b, q)] := by
  apply Vector.ext
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp [ptrEncode]

theorem intDecodeStrip_ofData (ds : Vector (β × Option P) n) :
    intDecodeStrip (Bytes.ofData ds) = some (ds.map Prod.fst) := by
  unfold intDecodeStrip
  rw [Bytes.toData?_ofData]
  rfl

theorem intDecodeStrip_ptrEncode (p : Vector β n × Option P) :
    intDecodeStrip (ptrEncode p : PBytes β P n) = some p.1 := by
  unfold ptrEncode
  rw [intDecodeStrip_ofData]
  congr 1
  apply Vector.ext
  intro i hi
  simp

theorem intDecodeStrip_eq_none_of_not_isInit {x : PBytes β P n} (h : ¬ x.IsInit) :
    intDecodeStrip x = none := by
  unfold intDecodeStrip
  rw [Bytes.toData?_eq_none_of_not_isInit h]
  rfl

/-- A decoder that succeeds only on fully initialized vectors is monotone for the flat order. -/
theorem decodeMono_of_decode_some_isInit {D V : Type} {m : Nat} (r : Rep (Bytes D m) V)
    (h : ∀ x v, r.decode x = some v → x.IsInit) : r.DecodeMono := by
  intro x y hxy
  cases hx : r.decode x with
  | none => exact OptLe.none_le _
  | some v =>
    have := Bytes.eq_of_le_of_isInit hxy (h x v hx)
    rw [this, hx]
    exact OptLe.refl _

theorem intDecodeStrip_some_isInit {x : PBytes β P n} {v : Vector β n} (h : intDecodeStrip x = some v) :
    x.IsInit := by
  apply Classical.byContradiction
  intro hn
  rw [intDecodeStrip_eq_none_of_not_isInit hn] at h
  cases h

theorem intStripRep_decodeEncode : (intStripRep : Rep (PBytes β P n) (Vector β n)).DecodeEncode := by
  intro x
  show intDecodeStrip (ptrEncode (x, none)) = some x
  exact intDecodeStrip_ptrEncode _

theorem intStripRep_decodeMono : (intStripRep : Rep (PBytes β P n) (Vector β n)).DecodeMono :=
  decodeMono_of_decode_some_isInit _ fun _ _ h => intDecodeStrip_some_isInit h

theorem intStripRep_fromBytes : (intStripRep : Rep (PBytes β P n) (Vector β n)).FromBytes := by
  intro x hx
  obtain ⟨ds, rfl⟩ := Bytes.exists_ofData_of_isInit hx
  exact ⟨_, intDecodeStrip_ofData ds⟩

theorem intDecodeStrict_eq_some_iff (x : PBytes β P n) (v : Vector β n) :
    intDecodeStrict x = some v ↔ x = intEncode v := by
  unfold intDecodeStrict
  cases hx : x.toData? with
  | none =>
    simp only
    constructor
    · intro h; cases h
    · intro h
      rw [h, intEncode, Bytes.toData?_ofData] at hx
      cases hx
  | some ds =>
    have hxe := Bytes.ofData_of_toData? hx
    simp only
    split
    · rename_i hnone
      constructor
      · intro h
        cases h
        rw [hxe, intEncode]
        congr 1
        apply Vector.ext
        intro i hi
        have := hnone i hi
        simp only [Vector.getElem_map]
        revert this
        cases ds[i] with
        | mk a q => cases q <;> simp
      · intro h
        rw [hxe, intEncode] at h
        have hds : ds = v.map fun b => (b, none) := by
          apply Vector.ext
          intro i hi
          have := congrArg (fun y : PBytes β P n => y[i]) h
          simp only [Bytes.getElem_ofData] at this
          injection this
        rw [hds]
        congr 1
        apply Vector.ext
        intro i hi
        simp
    · rename_i hnone
      constructor
      · intro h; cases h
      · intro h
        rw [hxe, intEncode] at h
        apply absurd _ hnone
        intro i hi
        have := congrArg (fun y : PBytes β P n => y[i]) h
        simp only [Bytes.getElem_ofData] at this
        injection this with h'
        rw [h']
        simp

theorem intStrictRep_decodeEncode : (intStrictRep : Rep (PBytes β P n) (Vector β n)).DecodeEncode :=
  fun v => (intDecodeStrict_eq_some_iff _ v).mpr rfl

theorem intStrictRep_encodeLeast : (intStrictRep : Rep (PBytes β P n) (Vector β n)).EncodeLeast := by
  intro x v h
  rw [(intDecodeStrict_eq_some_iff x v).mp h]
  exact Bytes.le_refl _

theorem intStrictRep_decodeMono : (intStrictRep : Rep (PBytes β P n) (Vector β n)).DecodeMono :=
  decodeMono_of_decode_some_isInit _ fun x v h => by
    rw [(intDecodeStrict_eq_some_iff x v).mp h]
    exact Bytes.isInit_ofData _

theorem ptrDecodeStrict_eq_some_iff [DecidableEq P] (x : PBytes β P (n + 1))
    (p : Vector β (n + 1) × Option P) : ptrDecodeStrict x = some p ↔ x = ptrEncode p := by
  unfold ptrDecodeStrict
  cases hx : x.toData? with
  | none =>
    simp only
    constructor
    · intro h; cases h
    · intro h
      rw [h, ptrEncode, Bytes.toData?_ofData] at hx
      cases hx
  | some ds =>
    have hxe := Bytes.ofData_of_toData? hx
    simp only
    split
    · rename_i hu
      constructor
      · intro h
        cases h
        rw [hxe, ptrEncode]
        congr 1
        apply Vector.ext
        intro i hi
        simp only [Vector.getElem_map]
        rw [← hu i hi]
      · intro h
        rw [hxe, ptrEncode] at h
        have hds : ds = p.1.map fun b => (b, p.2) := by
          apply Vector.ext
          intro i hi
          have := congrArg (fun y : PBytes β P (n + 1) => y[i]) h
          simp only [Bytes.getElem_ofData] at this
          injection this
        rw [hds]
        obtain ⟨a, q⟩ := p
        congr 1
        rw [Prod.mk.injEq]
        constructor
        · apply Vector.ext
          intro i hi
          simp
        · simp
    · rename_i hu
      constructor
      · intro h; cases h
      · intro h
        rw [hxe, ptrEncode] at h
        have hds : ds = p.1.map fun b => (b, p.2) := by
          apply Vector.ext
          intro i hi
          have := congrArg (fun y : PBytes β P (n + 1) => y[i]) h
          simp only [Bytes.getElem_ofData] at this
          injection this
        apply absurd _ hu
        intro i hi
        rw [hds]
        simp

theorem ptrStrictRep_decodeEncode [DecidableEq P] :
    (ptrStrictRep : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeEncode :=
  fun p => (ptrDecodeStrict_eq_some_iff _ p).mpr rfl

theorem ptrStrictRep_encodeLeast [DecidableEq P] :
    (ptrStrictRep : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P)).EncodeLeast := by
  intro x p h
  rw [(ptrDecodeStrict_eq_some_iff x p).mp h]
  exact Bytes.le_refl _

theorem ptrStrictRep_decodeMono [DecidableEq P] :
    (ptrStrictRep : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeMono :=
  decodeMono_of_decode_some_isInit _ fun x p h => by
    rw [(ptrDecodeStrict_eq_some_iff x p).mp h]
    exact Bytes.isInit_ofData _

/-! ### Lemmas for the provenance-increasing order -/

theorem leProvInc_init_iff (d : β × Option P) (y : AByte (β × Option P)) :
    AByte.leProvInc (.init d) y ↔ ∃ d' : β × Option P, y = .init d' ∧ d'.1 = d.1 ∧
      (d.2 = none ∨ d'.2 = d.2) := by
  obtain ⟨a, q⟩ := d
  cases y with
  | uninit =>
    cases q <;> simp [AByte.leProvInc]
  | init d' =>
    obtain ⟨b, q'⟩ := d'
    cases q with
    | none => simp [AByte.leProvInc, eq_comm]
    | some p =>
      simp only [AByte.leProvInc]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(b, q'), rfl, h1.symm, Or.inr h2⟩
      · rintro ⟨d'', hd, h1, h2⟩
        cases hd
        rcases h2 with h2 | h2
        · cases h2
        · exact ⟨h1.symm, h2⟩

theorem intStripRepInc_decodeEncode :
    (intStripRepInc : Rep (PBytesInc β P n) (Vector β n)).DecodeEncode :=
  fun x => intDecodeStrip_ptrEncode (x, none)

theorem intStripRepInc_encodeLeast :
    (intStripRepInc : Rep (PBytesInc β P n) (Vector β n)).EncodeLeast := by
  intro x v h
  change intDecodeStrip x.bytes = some v at h
  unfold intDecodeStrip at h
  cases hx : x.bytes.toData? with
  | none => rw [hx] at h; cases h
  | some ds =>
    rw [hx] at h
    cases h
    have hxe := Bytes.ofData_of_toData? hx
    intro i hi
    change AByte.leProvInc (intEncode (ds.map Prod.fst))[i] x.bytes[i]
    rw [hxe]
    simp only [intEncode, Bytes.getElem_ofData, Vector.getElem_map]
    exact rfl

theorem intStripRepInc_decodeMono :
    (intStripRepInc : Rep (PBytesInc β P n) (Vector β n)).DecodeMono := by
  intro x y hxy
  change intDecodeStrip x.bytes ⊑ intDecodeStrip y.bytes
  cases hx : intDecodeStrip x.bytes with
  | none => exact OptLe.none_le _
  | some v =>
    have hxi := intDecodeStrip_some_isInit hx
    obtain ⟨ds, hds⟩ := Bytes.exists_ofData_of_isInit hxi
    rw [hds, intDecodeStrip_ofData] at hx
    cases hx
    have hy : ∀ (i : Nat) (hi : i < n), ∃ d', y.bytes[i] = .init d' ∧ d'.1 = ds[i].1 := by
      intro i hi
      have := hxy i hi
      rw [hds, Bytes.getElem_ofData] at this
      obtain ⟨d', h1, h2, _⟩ := (leProvInc_init_iff _ _).mp this
      exact ⟨d', h1, h2⟩
    have hyi : y.bytes.IsInit := by
      intro i hi
      obtain ⟨d', h1, _⟩ := hy i hi
      rw [h1]
      rfl
    obtain ⟨es, hes⟩ := Bytes.exists_ofData_of_isInit hyi
    rw [hes, intDecodeStrip_ofData]
    show Vector.map Prod.fst ds = Vector.map Prod.fst es
    apply Vector.ext
    intro i hi
    obtain ⟨d', h1, h2⟩ := hy i hi
    rw [hes, Bytes.getElem_ofData] at h1
    injection h1 with h1
    simp only [Vector.getElem_map]
    rw [h1, h2]

theorem intStripRepInc_decodes_init (x : PBytesInc β P n) (hx : x.bytes.IsInit) :
    ∃ v, intStripRepInc.decode x = some v := by
  obtain ⟨ds, hds⟩ := Bytes.exists_ofData_of_isInit hx
  exact ⟨ds.map Prod.fst, by show intDecodeStrip x.bytes = _; rw [hds, intDecodeStrip_ofData]⟩

/-- Under the provenance-increasing order, the provenance-rejecting integer decoder is not
monotone: `[init (0, none)]` decodes, the more defined `[init (0, some ())]` does not. -/
theorem intStrictRepInc_not_decodeMono :
    ¬ (intStrictRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).DecodeMono := by
  intro h
  have hle : (⟨#v[.init ((0 : Byte), none)]⟩ : PBytesInc Byte Unit 1) ⊑ ⟨#v[.init (0, some ())]⟩ := by
    intro i hi
    have : i = 0 := by omega
    subst this
    exact rfl
  have h1 := h _ _ hle
  have hx : intDecodeStrict (#v[.init ((0 : Byte), none)] : PBytes Byte Unit 1) = some #v[0] :=
    (intDecodeStrict_eq_some_iff _ _).mpr (intEncode_singleton 0).symm
  have hy : intDecodeStrict (#v[.init ((0 : Byte), some ())] : PBytes Byte Unit 1) = none := by
    cases hc : intDecodeStrict (#v[.init ((0 : Byte), some ())] : PBytes Byte Unit 1) with
    | none => rfl
    | some w =>
      have := congrArg (fun y : PBytes Byte Unit 1 => y[0]) ((intDecodeStrict_eq_some_iff _ _).mp hc)
      simp only [intEncode, Bytes.getElem_ofData, Vector.getElem_map] at this
      injection this with h'
      injection h' with _ h''
      cases h''
  have h1' : intDecodeStrict (#v[.init ((0 : Byte), none)] : PBytes Byte Unit 1) ⊑
      intDecodeStrict (#v[.init ((0 : Byte), some ())] : PBytes Byte Unit 1) := h1
  rw [hx, hy] at h1'
  exact h1'

/-! ### Size zero, provenance-carrying integers, and further pointer representations -/

/-- At pointer size `0` the canonical pointer encoder forgets the provenance (`ptrEncode (#v[], q)`
is the empty vector for every `q`), so no pointer decoder satisfies `DecodeEncode` once some
provenance exists. This is why the pointer results are stated for sizes `n + 1`. -/
theorem no_ptr_decodeEncode_size_zero (p : P) (dp : PBytes β P 0 → Option (Vector β 0 × Option P)) :
    ¬ (⟨ptrEncode, dp⟩ : Rep (PBytes β P 0) (Vector β 0 × Option P)).DecodeEncode := by
  intro hDEp
  have hc : (ptrEncode (#v[], none) : PBytes β P 0) = ptrEncode (#v[], some p) := by
    apply Vector.ext
    intro i hi
    omega
  have hnone : dp (ptrEncode (#v[], none)) = some (#v[], none) := hDEp (#v[], none)
  have hsome : dp (ptrEncode (#v[], some p)) = some (#v[], some p) := hDEp (#v[], some p)
  rw [hc, hsome] at hnone
  injection hnone with hpair
  injection hpair with _ hq
  cases hq

/-- Integers whose *values* carry provenance (provenance via integers): the value of an `n`-byte
integer is its byte data together with the per-byte provenance tags. -/
def provIntRep : Rep (PBytes β P n) (Vector (β × Option P) n) := ⟨Bytes.ofData, Bytes.toData?⟩

theorem provIntRep_decodeEncode : (provIntRep : Rep (PBytes β P n) _).DecodeEncode :=
  fun ds => Bytes.toData?_ofData ds

theorem provIntRep_encodeLeast : (provIntRep : Rep (PBytes β P n) _).EncodeLeast := by
  intro x ds h
  have hx : x = Bytes.ofData ds := Bytes.ofData_of_toData? h
  rw [hx]
  exact Bytes.le_refl _

theorem provIntRep_decodeMono : (provIntRep : Rep (PBytes β P n) _).DecodeMono :=
  decodeMono_of_decode_some_isInit _ fun x ds h => by
    have hx : x = Bytes.ofData ds := Bytes.ofData_of_toData? h
    rw [hx]
    exact Bytes.isInit_ofData _

theorem provIntRep_fromBytes : (provIntRep : Rep (PBytes β P n) _).FromBytes := by
  intro x hx
  obtain ⟨ds, rfl⟩ := Bytes.exists_ofData_of_isInit hx
  exact ⟨ds, Bytes.toData?_ofData ds⟩

theorem provIntRep_intoBytes : (provIntRep : Rep (PBytes β P n) _).IntoBytes :=
  fun ds => Bytes.isInit_ofData ds

/-- Pointers that always carry provenance (value type `Vector β (n + 1) × P`), over the
provenance-increasing order: decode succeeds iff all bytes are initialized and carry the same
`some p`. -/
def reqProvPtrRepInc [DecidableEq P] : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × P) where
  encode vp := ⟨ptrEncode (vp.1, some vp.2)⟩
  decode x :=
    match ptrDecodeStrict x.bytes with
    | some (a, some p) => some (a, p)
    | _ => none

theorem reqProvPtrRepInc_decode_eq_some_iff [DecidableEq P]
    (x : PBytesInc β P (n + 1)) (vp : Vector β (n + 1) × P) :
    reqProvPtrRepInc.decode x = some vp ↔ x.bytes = ptrEncode (vp.1, some vp.2) := by
  unfold reqProvPtrRepInc
  dsimp only
  cases hs : ptrDecodeStrict x.bytes with
  | none =>
    simp only
    refine ⟨fun h => (by cases h), fun h => ?_⟩
    rw [(ptrDecodeStrict_eq_some_iff x.bytes (vp.1, some vp.2)).mpr h] at hs
    cases hs
  | some aq =>
    rcases aq with ⟨a, none | p⟩
    · simp only
      refine ⟨fun h => (by cases h), fun h => ?_⟩
      have h1 := (ptrDecodeStrict_eq_some_iff x.bytes (a, none)).mp hs
      rw [h] at h1
      have h0 := congrArg (fun y : PBytes β P (n + 1) => y[0]) h1
      simp only [ptrEncode, Bytes.getElem_ofData, Vector.getElem_map] at h0
      injection h0 with h0'
      injection h0' with _ hq
      cases hq
    · simp only [Option.some.injEq]
      constructor
      · intro h
        rw [← h]
        exact (ptrDecodeStrict_eq_some_iff x.bytes (a, some p)).mp hs
      · intro h
        have h2 := (ptrDecodeStrict_eq_some_iff x.bytes (vp.1, some vp.2)).mpr h
        rw [hs] at h2
        injection h2 with h2'
        rcases Prod.mk.inj h2' with ⟨ha, hp⟩
        injection hp with hp'
        obtain ⟨va, vp2⟩ := vp
        exact Prod.ext ha hp'

/-- Pointers that always carry provenance satisfy all three laws under the
provenance-increasing order, with the flat order on decoded values (every encoded byte carries
provenance and is therefore maximal). -/
theorem reqProvPtrRepInc_threeLaws [DecidableEq P] :
    (reqProvPtrRepInc : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × P)).DecodeMono ∧
    (reqProvPtrRepInc : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × P)).DecodeEncode ∧
    (reqProvPtrRepInc : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × P)).EncodeLeast := by
  refine ⟨?_, fun vp => (reqProvPtrRepInc_decode_eq_some_iff _ vp).mpr rfl, ?_⟩
  · intro x y hxy
    cases hx : reqProvPtrRepInc.decode x with
    | none => exact OptLe.none_le _
    | some vp =>
      have hxe := (reqProvPtrRepInc_decode_eq_some_iff x vp).mp hx
      have hye : y.bytes = ptrEncode (vp.1, some vp.2) := by
        apply Vector.ext
        intro i hi
        have hle := hxy i hi
        rw [hxe] at hle
        simp only [ptrEncode, Bytes.getElem_ofData, Vector.getElem_map] at hle ⊢
        obtain ⟨d', hd', h1, h2⟩ := (leProvInc_init_iff _ _).mp hle
        rw [hd']
        rcases h2 with h2 | h2
        · cases h2
        · obtain ⟨b', q'⟩ := d'
          simp only at h1 h2
          rw [h1, h2]
      rw [(reqProvPtrRepInc_decode_eq_some_iff y vp).mpr hye]
      exact OptLe.refl _
  · intro x vp hx i hi
    have hxe := (reqProvPtrRepInc_decode_eq_some_iff x vp).mp hx
    show AByte.leProvInc (ptrEncode (vp.1, some vp.2))[i] x.bytes[i]
    rw [hxe]
    simp [ptrEncode, AByte.leProvInc]

/-- A non-flat order on decoded pointers (MiniRust-style): `none` (failure) lies below
everything; a pointer without provenance lies below every pointer with the same address; a
pointer with provenance `p` lies only below pointers with the same address and provenance `p`. -/
def PtrValLe {m : Nat} : Option (Vector β m × Option P) → Option (Vector β m × Option P) → Prop
  | none, _ => True
  | some _, none => False
  | some (a, none), some (b, _) => a = b
  | some (a, some p), some (b, q) => a = b ∧ q = some p

/-- MiniRust-style pointer decoder (size `n + 1`): succeeds iff all bytes are initialized; the
address is the byte values; the provenance is the common provenance of the bytes if they all
agree, and `none` if provenance is missing or mixed (instead of failing). -/
def ptrDecodeDegrade [DecidableEq P] (x : PBytes β P (n + 1)) :
    Option (Vector β (n + 1) × Option P) :=
  match x.toData? with
  | some ds =>
    some (ds.map Prod.fst,
      if ∀ (i : Nat) (h : i < n + 1), ds[i].2 = ds[0].2 then ds[0].2 else none)
  | none => none

/-- Pointers with the degrading decoder over the provenance-increasing order. -/
def ptrDegradeRepInc [DecidableEq P] : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P) :=
  ⟨ptrEncodeInc, fun x => ptrDecodeDegrade x.bytes⟩

theorem ptrDecodeDegrade_ofData [DecidableEq P] (ds : Vector (β × Option P) (n + 1)) :
    ptrDecodeDegrade (Bytes.ofData ds) =
      some (ds.map Prod.fst,
        if ∀ (i : Nat) (h : i < n + 1), ds[i].2 = ds[0].2 then ds[0].2 else none) := by
  unfold ptrDecodeDegrade
  rw [Bytes.toData?_ofData]

theorem ptrDegradeRepInc_decodeEncode [DecidableEq P] :
    (ptrDegradeRepInc : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeEncode := by
  intro p
  obtain ⟨a, q⟩ := p
  show ptrDecodeDegrade (Bytes.ofData (a.map fun b => (b, q))) = some (a, q)
  rw [ptrDecodeDegrade_ofData]
  have hu : ∀ (i : Nat) (h : i < n + 1),
      ((a.map fun b => (b, q))[i]).2 = ((a.map fun b => (b, q))[0]).2 := by
    intro i h
    simp
  rw [ite_eq_left_of_eq_true _ _ (eq_true hu)]
  congr 1
  rw [Prod.mk.injEq]
  constructor
  · apply Vector.ext
    intro i hi
    simp
  · simp

/-- If `x ⊑ y` in the provenance-increasing order and `x` is `ofData ds`, then `y` is `ofData es`
with the same byte values, and every tag of `ds` that is not `none` reappears in `es`. -/
theorem exists_ofData_of_leProvInc_ofData {m : Nat} {ds : Vector (β × Option P) m}
    {y : PBytesInc β P m} (hxy : (⟨Bytes.ofData ds⟩ : PBytesInc β P m) ⊑ y) :
    ∃ es : Vector (β × Option P) m, y.bytes = Bytes.ofData es ∧
      ∀ (i : Nat) (hi : i < m), es[i].1 = ds[i].1 ∧ (ds[i].2 = none ∨ es[i].2 = ds[i].2) := by
  have hy : ∀ (i : Nat) (hi : i < m), ∃ d', y.bytes[i] = .init d' ∧ d'.1 = ds[i].1 ∧
      (ds[i].2 = none ∨ d'.2 = ds[i].2) := by
    intro i hi
    have := hxy i hi
    simp only [Bytes.getElem_ofData] at this
    exact (leProvInc_init_iff _ _).mp this
  have hyi : y.bytes.IsInit := by
    intro i hi
    obtain ⟨d', h1, _⟩ := hy i hi
    rw [h1]
    rfl
  obtain ⟨es, hes⟩ := Bytes.exists_ofData_of_isInit hyi
  refine ⟨es, hes, fun i hi => ?_⟩
  obtain ⟨d', h1, h2, h3⟩ := hy i hi
  rw [hes, Bytes.getElem_ofData] at h1
  injection h1 with h1
  rw [h1]
  exact ⟨h2, h3⟩

theorem ptrDegradeRepInc_decodeMonoBy_ptrValLe [DecidableEq P] :
    (ptrDegradeRepInc : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeMonoBy
      PtrValLe := by
  intro x y hxy
  change PtrValLe (ptrDecodeDegrade x.bytes) (ptrDecodeDegrade y.bytes)
  cases hx : x.bytes.toData? with
  | none =>
    have hnone : ptrDecodeDegrade x.bytes = none := by
      unfold ptrDecodeDegrade
      rw [hx]
    rw [hnone]
    exact trivial
  | some ds =>
    have hxe : x.bytes = Bytes.ofData ds := Bytes.ofData_of_toData? hx
    have hxy' : (⟨Bytes.ofData ds⟩ : PBytesInc β P (n + 1)) ⊑ y := by
      intro i hi
      have := hxy i hi
      rw [hxe] at this
      exact this
    obtain ⟨es, hes, hrel⟩ := exists_ofData_of_leProvInc_ofData hxy'
    rw [hxe, hes, ptrDecodeDegrade_ofData, ptrDecodeDegrade_ofData]
    have haddr : ds.map Prod.fst = es.map Prod.fst := by
      apply Vector.ext
      intro i hi
      simp [(hrel i hi).1]
    by_cases hu : ∀ (i : Nat) (h : i < n + 1), ds[i].2 = ds[0].2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hu)]
      cases hq : ds[0].2 with
      | none =>
        show ds.map Prod.fst = es.map Prod.fst
        exact haddr
      | some p =>
        have hall : ∀ (i : Nat) (hi : i < n + 1), es[i].2 = some p := by
          intro i hi
          rcases (hrel i hi).2 with h | h
          · rw [hu i hi, hq] at h
            cases h
          · rw [h, hu i hi, hq]
        have hu' : ∀ (i : Nat) (h : i < n + 1), es[i].2 = es[0].2 := fun i h => by
          rw [hall i h, hall 0 (by omega)]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hu')]
        exact ⟨haddr, hall 0 (by omega)⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hu)]
      show ds.map Prod.fst = es.map Prod.fst
      exact haddr

theorem ptrDegradeRepInc_encodeLeast [DecidableEq P] :
    (ptrDegradeRepInc : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P)).EncodeLeast := by
  intro x p h i hi
  change ptrDecodeDegrade x.bytes = some p at h
  cases hx : x.bytes.toData? with
  | none =>
    unfold ptrDecodeDegrade at h
    rw [hx] at h
    cases h
  | some ds =>
    have hxe : x.bytes = Bytes.ofData ds := Bytes.ofData_of_toData? hx
    rw [hxe, ptrDecodeDegrade_ofData] at h
    injection h with h
    subst h
    show AByte.leProvInc (ptrEncode _)[i] x.bytes[i]
    rw [hxe]
    simp only [ptrEncode, Bytes.getElem_ofData, Vector.getElem_map]
    by_cases hu : ∀ (i : Nat) (h : i < n + 1), ds[i].2 = ds[0].2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hu)]
      cases hq : ds[0].2 with
      | none => exact rfl
      | some p =>
        have hdi : ds[i] = (ds[i].1, some p) := by
          rw [← hq, ← hu i hi]
        rw [hdi]
        exact ⟨rfl, rfl⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hu)]
      exact rfl

/-- Escape hatch for R6d: with MiniRust's value order on pointers (`PtrValLe`) in place of the
flat order, the degrading pointer decoder is monotone, and satisfies `DecodeEncode` and
`EncodeLeast`, under the provenance-increasing byte order, at every pointer size `n + 1`. -/
theorem ptrDegradeRepInc_lawful_by_ptrValLe [DecidableEq P] :
    (ptrDegradeRepInc : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeMonoBy
      PtrValLe ∧
    (ptrDegradeRepInc : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeEncode ∧
    (ptrDegradeRepInc : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P)).EncodeLeast :=
  ⟨ptrDegradeRepInc_decodeMonoBy_ptrValLe, ptrDegradeRepInc_decodeEncode,
   ptrDegradeRepInc_encodeLeast⟩

end Prov

/-! ## R6a: integer → pointer → integer -/

/-- **R6a.** At any integer/pointer size `n + 1`, for any integer decoder `di` and pointer
decoder `dp` (with the canonical encoders) that both satisfy `DecodeEncode`, transmuting an
integer `x` to a pointer yields the pointer `(x, none)` (same address, no provenance), and
transmuting that pointer back yields `x`. -/
theorem int_ptr_int_roundtrip_of_decodeEncode {β P : Type} {n : Nat}
    (di : PBytes β P (n + 1) → Option (Vector β (n + 1)))
    (dp : PBytes β P (n + 1) → Option (Vector β (n + 1) × Option P))
    (hDEi : (⟨intEncode, di⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1))).DecodeEncode)
    (hDEp : (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeEncode)
    (x : Vector β (n + 1)) :
    transmute (⟨intEncode, di⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1))) ⟨ptrEncode, dp⟩ x =
      some (x, none) ∧
    transmute (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P))
      ⟨intEncode, di⟩ (x, none) = some x := by
  exact ⟨hDEp (x, none), hDEi x⟩

/-- Tightness of `hDEi` in R6a: the always-failing integer decoder, with the strict pointer
decoder (which satisfies `DecodeEncode`). -/
theorem int_ptr_int_roundtrip_tight_hDEi :
    (⟨ptrEncode, ptrDecodeStrict⟩ : Rep (PBytes Byte Unit 1) (Vector Byte 1 × Option Unit)).DecodeEncode ∧
    ¬ (∀ x : Vector Byte 1,
        transmute (⟨intEncode, fun _ => none⟩ : Rep (PBytes Byte Unit 1) (Vector Byte 1))
          ⟨ptrEncode, ptrDecodeStrict⟩ x = some (x, none) ∧
        transmute (⟨ptrEncode, ptrDecodeStrict⟩ : Rep (PBytes Byte Unit 1) (Vector Byte 1 × Option Unit))
          ⟨intEncode, fun _ => none⟩ (x, none) = some x) := by
  refine ⟨ptrStrictRep_decodeEncode, fun h => ?_⟩
  have := (h #v[0]).2
  cases this

/-- Tightness of `hDEp` in R6a: a pointer decoder that requires provenance (bytes without
provenance never decode as a pointer) violates `DecodeEncode` at provenance-free pointers, and
integer → pointer fails. The stripping integer decoder satisfies `DecodeEncode`. -/
theorem int_ptr_int_roundtrip_tight_hDEp :
    (⟨intEncode, intDecodeStrip⟩ : Rep (PBytes Byte Unit 1) (Vector Byte 1)).DecodeEncode ∧
    ¬ (∀ x : Vector Byte 1,
        transmute (⟨intEncode, intDecodeStrip⟩ : Rep (PBytes Byte Unit 1) (Vector Byte 1))
          ⟨ptrEncode, ptrDecodeReqProv⟩ x = some (x, none) ∧
        transmute (⟨ptrEncode, ptrDecodeReqProv⟩ : Rep (PBytes Byte Unit 1) (Vector Byte 1 × Option Unit))
          ⟨intEncode, intDecodeStrip⟩ (x, none) = some x) := by
  refine ⟨intStripRep_decodeEncode, fun h => ?_⟩
  have h1 := (h #v[0]).1
  change ptrDecodeReqProv (intEncode #v[(0 : Byte)] : PBytes Byte Unit 1) = _ at h1
  unfold ptrDecodeReqProv at h1
  rw [intEncode, Bytes.toData?_ofData] at h1
  simp at h1

/-- Non-vacuity for R6a: stripping integers and strict pointers (size 1, provenance `Unit`). -/
theorem int_ptr_int_roundtrip_nonvacuous :
    (⟨intEncode, intDecodeStrip⟩ : Rep (PBytes Byte Unit 1) (Vector Byte 1)).DecodeEncode ∧
    (⟨ptrEncode, ptrDecodeStrict⟩ : Rep (PBytes Byte Unit 1) (Vector Byte 1 × Option Unit)).DecodeEncode :=
  ⟨intStripRep_decodeEncode, ptrStrictRep_decodeEncode⟩

/-! ## R6b: pointer → integer → pointer drops provenance (fully proved) -/

/-- **R6b.** At any pointer size `n + 1`, for every pointer decoder `dp` satisfying
`DecodeEncode` with the canonical pointer encoder, and with the provenance-stripping integer
decoder: the pointer `(a, some p)` transmutes to the integer `a`, which transmutes back to the
pointer `(a, none)`, which differs from `(a, some p)`. -/
theorem ptr_intStrip_ptr_roundtrip_drops_provenance_of_decodeEncode {β P : Type} {n : Nat}
    (dp : PBytes β P (n + 1) → Option (Vector β (n + 1) × Option P))
    (hDEp : (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeEncode)
    (a : Vector β (n + 1)) (p : P) :
    transmute (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P))
      intStripRep (a, some p) = some a ∧
    transmute intStripRep (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P))
      a = some (a, none) ∧
    ((a, none) : Vector β (n + 1) × Option P) ≠ (a, some p) := by
  refine ⟨intDecodeStrip_ptrEncode (a, some p), hDEp (a, none), fun h => ?_⟩
  injection h with _ h2
  cases h2

/-- Tightness of `hDEp` in R6b: with the constant pointer decoder `fun _ => some (#v[0], some ())`
(which violates `DecodeEncode`), the conclusion fails at `a = #v[0]`, `p = ()`: the integer `#v[0]`
transmutes back to the pointer with provenance. -/
theorem ptr_intStrip_ptr_roundtrip_tight_hDEp :
    ¬ (transmute (⟨ptrEncode, fun _ => some (#v[0], some ())⟩ :
          Rep (PBytes Byte Unit 1) (Vector Byte 1 × Option Unit)) intStripRep (#v[0], some ()) =
          some #v[0] ∧
        transmute intStripRep (⟨ptrEncode, fun _ => some (#v[0], some ())⟩ :
          Rep (PBytes Byte Unit 1) (Vector Byte 1 × Option Unit)) #v[0] = some (#v[0], none) ∧
        ((#v[0], none) : Vector Byte 1 × Option Unit) ≠ (#v[0], some ())) := by
  rintro ⟨_, h2, _⟩
  injection h2 with h2
  injection h2 with _ h2
  cases h2

/-- Non-vacuity for R6b: at size 1 with provenance `Unit`, the strict pointer decoder satisfies
`DecodeEncode`, and an address and a provenance exist. -/
theorem ptr_intStrip_ptr_roundtrip_nonvacuous :
    (⟨ptrEncode, ptrDecodeStrict⟩ : Rep (PBytes Byte Unit 1) (Vector Byte 1 × Option Unit)).DecodeEncode ∧
    ∃ (_ : Vector Byte 1) (_ : Unit), True :=
  ⟨ptrStrictRep_decodeEncode, #v[0], (), trivial⟩

/-- With the provenance-rejecting integer decoder instead, pointer → integer fails outright for
pointers carrying provenance (fully proved). -/
theorem transmute_ptr_intStrict_eq_none {β P : Type} {n : Nat}
    (dp : PBytes β P (n + 1) → Option (Vector β (n + 1) × Option P)) (a : Vector β (n + 1)) (p : P) :
    transmute (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P)) intStrictRep (a, some p) = none := by
  change intDecodeStrict (ptrEncode (a, some p)) = none
  cases h : intDecodeStrict (ptrEncode (a, some p) : PBytes β P (n + 1)) with
  | none => rfl
  | some v =>
    have := congrArg (fun y : PBytes β P (n + 1) => y[0]) ((intDecodeStrict_eq_some_iff _ _).mp h)
    simp only [ptrEncode, intEncode, Bytes.getElem_ofData, Vector.getElem_map] at this
    injection this with h'
    injection h' with _ h''
    cases h''

/-! ## R6c: provenance as data — integers cannot be both `EncodeLeast` and `FromBytes` -/

/-- **R6c (impossibility).** Bytes carry provenance and are ordered with provenance as data
(flat). If some byte value `b0` and some provenance `p0` exist and `n ≥ 1`, then no decoder `d`
for the canonical integer encoder makes `⟨intEncode, d⟩` satisfy both `EncodeLeast` and
`FromBytes`. -/
theorem no_int_decoder_encodeLeast_fromBytes_of_provenance {β P : Type} {n : Nat}
    (b0 : β) (p0 : P) (hn : 0 < n) (d : PBytes β P n → Option (Vector β n)) :
    ¬ ((⟨intEncode, d⟩ : Rep (PBytes β P n) (Vector β n)).EncodeLeast ∧
       (⟨intEncode, d⟩ : Rep (PBytes β P n) (Vector β n)).FromBytes) := by
  rintro ⟨hEL, hFB⟩
  let x : PBytes β P n := Vector.replicate n (.init (b0, some p0))
  have hx : x.IsInit := by
    intro i hi
    simp [x]
  obtain ⟨v, hv⟩ := hFB x hx
  have h0 := hEL x v hv 0 hn
  simp [x, intEncode] at h0

/-- Positive controls for R6c: dropping `EncodeLeast`, the stripping decoder is `FromBytes`
(and satisfies `DecodeMono` and `DecodeEncode`); dropping `FromBytes`, the rejecting decoder
satisfies all three laws. -/
theorem no_int_decoder_positive_control :
    ((intStripRep : Rep (PBytes Byte Unit 1) (Vector Byte 1)).FromBytes ∧
      (intStripRep : Rep (PBytes Byte Unit 1) (Vector Byte 1)).DecodeMono ∧
      (intStripRep : Rep (PBytes Byte Unit 1) (Vector Byte 1)).DecodeEncode) ∧
    ((intStrictRep : Rep (PBytes Byte Unit 1) (Vector Byte 1)).DecodeMono ∧
      (intStrictRep : Rep (PBytes Byte Unit 1) (Vector Byte 1)).DecodeEncode ∧
      (intStrictRep : Rep (PBytes Byte Unit 1) (Vector Byte 1)).EncodeLeast) :=
  ⟨⟨intStripRep_fromBytes, intStripRep_decodeMono, intStripRep_decodeEncode⟩,
   ⟨intStrictRep_decodeMono, intStrictRep_decodeEncode, intStrictRep_encodeLeast⟩⟩

/-- Escape hatch for R6c: if the integer type's *values* carry provenance (provenance via
integers), the representation `provIntRep` satisfies all three laws and is both `FromBytes` and
`IntoBytes` over provenance-carrying bytes with provenance as data. R6c concerns only the
canonical integer encoder, whose values carry no provenance. Shown here at size 1; the component
lemmas `provIntRep_decodeMono`, `provIntRep_decodeEncode`, `provIntRep_encodeLeast`,
`provIntRep_fromBytes`, `provIntRep_intoBytes` hold at every size. At sizes `≥ 2` the escape relies
on the values carrying provenance *per byte* (`Vector (β × Option P) n`): integers whose values
carry a *single* provenance for the whole integer (`Vector β n × Option P`, written uniformly by
`ptrEncode`) still cannot be both `EncodeLeast` and `FromBytes` under this order
(`no_singleProvInt_decoder_encodeLeast_fromBytes_of_two_le`). -/
theorem provIntRep_escape_hatch :
    (provIntRep : Rep (PBytes Byte Unit 1) (Vector (Byte × Option Unit) 1)).DecodeMono ∧
    (provIntRep : Rep (PBytes Byte Unit 1) (Vector (Byte × Option Unit) 1)).DecodeEncode ∧
    (provIntRep : Rep (PBytes Byte Unit 1) (Vector (Byte × Option Unit) 1)).EncodeLeast ∧
    (provIntRep : Rep (PBytes Byte Unit 1) (Vector (Byte × Option Unit) 1)).FromBytes ∧
    (provIntRep : Rep (PBytes Byte Unit 1) (Vector (Byte × Option Unit) 1)).IntoBytes :=
  ⟨provIntRep_decodeMono, provIntRep_decodeEncode, provIntRep_encodeLeast, provIntRep_fromBytes,
   provIntRep_intoBytes⟩

/-- Boundary of the R6c escape hatch: with provenance as data, integers whose values carry a
single provenance for the whole integer (`Vector β (n + 2) × Option P`, encoded uniformly by
`ptrEncode`) admit no decoder that is both `EncodeLeast` and `FromBytes` at any size `n + 2 ≥ 2`,
once a byte value `b0` and a provenance `p0` exist: the initialized vector whose byte 0 carries
`p0` and whose other bytes carry no provenance must decode, and no uniformly tagged encoding lies
below it. -/
theorem no_singleProvInt_decoder_encodeLeast_fromBytes_of_two_le {β P : Type} {n : Nat}
    (b0 : β) (p0 : P) (d : PBytes β P (n + 2) → Option (Vector β (n + 2) × Option P)) :
    ¬ ((⟨ptrEncode, d⟩ : Rep (PBytes β P (n + 2)) (Vector β (n + 2) × Option P)).EncodeLeast ∧
       (⟨ptrEncode, d⟩ : Rep (PBytes β P (n + 2)) (Vector β (n + 2) × Option P)).FromBytes) := by
  rintro ⟨hEL, hFB⟩
  let x : PBytes β P (n + 2) :=
    Vector.ofFn fun i => .init (b0, if i.val = 0 then some p0 else none)
  have hxInit : x.IsInit := by
    intro i hi
    simp [x]
  obtain ⟨⟨a, q⟩, hdx⟩ := hFB x hxInit
  have hle := hEL x (a, q) hdx
  have h0 := hle 0 (by omega)
  have h1 := hle 1 (by omega)
  simp only [ptrEncode, x, Bytes.getElem_ofData, Vector.getElem_map, Vector.getElem_ofFn,
    AByte.init_le_init_iff, Prod.mk.injEq] at h0 h1
  have hq0 : q = some p0 := h0.2
  have hq1 : q = none := h1.2
  rw [hq0] at hq1
  cases hq1

/-- The stripping integer decoder at provenance type `Empty`: `EncodeLeast` holds. -/
theorem intStripRep_encodeLeast_of_empty {β : Type} {n : Nat} :
    (intStripRep : Rep (PBytes β Empty n) (Vector β n)).EncodeLeast := by
  intro x v h
  change intDecodeStrip x = some v at h
  have hxi := intDecodeStrip_some_isInit h
  obtain ⟨ds, rfl⟩ := Bytes.exists_ofData_of_isInit hxi
  rw [intDecodeStrip_ofData] at h
  cases h
  intro i hi
  simp only [intStripRep, intEncode, Bytes.getElem_ofData, Vector.getElem_map]
  obtain ⟨b, q⟩ := ds[i]
  cases q with
  | none => exact rfl
  | some e => exact e.elim

/-- Tightness of `p0` in R6c: with provenance type `Empty`, the stripping decoder satisfies both
`EncodeLeast` and `FromBytes` (`b0 := 0`, `n := 1`). -/
theorem no_int_decoder_tight_p0 :
    (0 : Nat) < 1 ∧
    ¬ (∀ d : PBytes Byte Empty 1 → Option (Vector Byte 1),
        ¬ ((⟨intEncode, d⟩ : Rep (PBytes Byte Empty 1) (Vector Byte 1)).EncodeLeast ∧
           (⟨intEncode, d⟩ : Rep (PBytes Byte Empty 1) (Vector Byte 1)).FromBytes)) :=
  ⟨by decide, fun h => h intDecodeStrip ⟨intStripRep_encodeLeast_of_empty, intStripRep_fromBytes⟩⟩

/-- Tightness of `hn` in R6c: at size `0` the stripping decoder satisfies both `EncodeLeast` and
`FromBytes` (`b0 := 0`, `p0 := ()`). -/
theorem no_int_decoder_tight_hn :
    ¬ (∀ d : PBytes Byte Unit 0 → Option (Vector Byte 0),
        ¬ ((⟨intEncode, d⟩ : Rep (PBytes Byte Unit 0) (Vector Byte 0)).EncodeLeast ∧
           (⟨intEncode, d⟩ : Rep (PBytes Byte Unit 0) (Vector Byte 0)).FromBytes)) := by
  intro h
  apply h intDecodeStrip
  refine ⟨fun x v _ i hi => absurd hi (Nat.not_lt_zero i), intStripRep_fromBytes⟩

/-- Tightness of `b0` in R6c: with byte type `Empty` (no initialized byte exists), an
always-failing decoder satisfies `EncodeLeast` and, vacuously, `FromBytes` (`p0 := ()`,
`n := 1`). -/
theorem no_int_decoder_tight_b0 :
    (0 : Nat) < 1 ∧
    ¬ (∀ d : PBytes Empty Unit 1 → Option (Vector Empty 1),
        ¬ ((⟨intEncode, d⟩ : Rep (PBytes Empty Unit 1) (Vector Empty 1)).EncodeLeast ∧
           (⟨intEncode, d⟩ : Rep (PBytes Empty Unit 1) (Vector Empty 1)).FromBytes)) := by
  refine ⟨by decide, fun h => h (fun _ => none) ⟨fun _ _ hv => (by cases hv), fun x hx => ?_⟩⟩
  have := hx 0 (by decide)
  revert this
  cases x[0] with
  | uninit => intro h'; cases h'
  | init d => exact d.1.elim

/-- Non-vacuity for R6c: the hypotheses `b0`, `p0`, `n ≥ 1` hold for `Byte`, `Unit`, `n = 1`. -/
theorem no_int_decoder_nonvacuous : ∃ (_ : Byte) (_ : Unit), (0 : Nat) < 1 :=
  ⟨0, (), by decide⟩

/-! ## R6d: provenance increasing definedness — no lawful pointers with optional provenance -/

/-- **R6d (impossibility).** Bytes carry provenance and adding provenance makes a byte more
defined (`PBytesInc`). Pointer values have *optional* provenance (`Vector β (n + 1) × Option P`,
pointer size `n + 1`). If some byte value `b0` and some provenance `p0` exist, then no decoder `d`
for the canonical pointer encoder makes `⟨ptrEncodeInc, d⟩` satisfy both `DecodeMono` (with the
flat order on decoded values) and `DecodeEncode`. -/
theorem no_optProvPtr_decoder_decodeMono_decodeEncode_of_provInc {β P : Type} {n : Nat}
    (b0 : β) (p0 : P) (d : PBytesInc β P (n + 1) → Option (Vector β (n + 1) × Option P)) :
    ¬ ((⟨ptrEncodeInc, d⟩ : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeMono ∧
       (⟨ptrEncodeInc, d⟩ : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeEncode) := by
  rintro ⟨hM, hDE⟩
  let a0 : Vector β (n + 1) := Vector.replicate (n + 1) b0
  have hle : (ptrEncodeInc (a0, none) : PBytesInc β P (n + 1)) ⊑ ptrEncodeInc (a0, some p0) := by
    intro i hi
    show AByte.leProvInc (ptrEncode (a0, none))[i] (ptrEncode (a0, some p0))[i]
    simp [ptrEncode, AByte.leProvInc]
  have hm := hM _ _ hle
  have h1 : d (ptrEncodeInc (a0, none)) = some (a0, none) := hDE (a0, none)
  have h2 : d (ptrEncodeInc (a0, some p0)) = some (a0, some p0) := hDE (a0, some p0)
  change d (ptrEncodeInc (a0, none)) ⊑ d (ptrEncodeInc (a0, some p0)) at hm
  rw [h1, h2] at hm
  have heq : (a0, (none : Option P)) = (a0, some p0) := hm
  injection heq with _ hq
  cases hq

/-- Positive controls for R6d (each a nearby setting where the conclusion fails):
(1) with provenance as data (flat byte order) the strict pointer representation satisfies all
three laws; (2) under the provenance-increasing order each of the two laws alone is satisfiable
for the canonical pointer encoder (`DecodeMono` by the always-failing decoder; `DecodeEncode`,
together with `EncodeLeast`, by the strict decoder); (3) under the provenance-increasing order,
pointers that always carry provenance satisfy all three laws; (4) under the provenance-increasing
order with MiniRust's value order `PtrValLe` instead of the flat one, the degrading decoder is
monotone and satisfies `DecodeEncode` and `EncodeLeast` (shown at the two-byte size, where mixed
provenance can occur); (5) the stripping integer representation satisfies all three laws under
the provenance-increasing order. -/
theorem no_ptr_decoder_positive_control :
    ((ptrStrictRep : Rep (PBytes Byte Unit 1) (Vector Byte 1 × Option Unit)).DecodeMono ∧
      (ptrStrictRep : Rep (PBytes Byte Unit 1) (Vector Byte 1 × Option Unit)).DecodeEncode ∧
      (ptrStrictRep : Rep (PBytes Byte Unit 1) (Vector Byte 1 × Option Unit)).EncodeLeast) ∧
    ((noneRep (ptrEncodeInc : Vector Byte 1 × Option Unit → PBytesInc Byte Unit 1)).DecodeMono ∧
      (ptrStrictRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Option Unit)).DecodeEncode ∧
      (ptrStrictRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Option Unit)).EncodeLeast) ∧
    ((reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).DecodeMono ∧
      (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).DecodeEncode ∧
      (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).EncodeLeast) ∧
    ((ptrDegradeRepInc : Rep (PBytesInc Byte Unit 2) (Vector Byte 2 × Option Unit)).DecodeMonoBy
        PtrValLe ∧
      (ptrDegradeRepInc : Rep (PBytesInc Byte Unit 2) (Vector Byte 2 × Option Unit)).DecodeEncode ∧
      (ptrDegradeRepInc : Rep (PBytesInc Byte Unit 2) (Vector Byte 2 × Option Unit)).EncodeLeast) ∧
    ((intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).DecodeMono ∧
      (intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).DecodeEncode ∧
      (intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).EncodeLeast) := by
  refine ⟨⟨ptrStrictRep_decodeMono, ptrStrictRep_decodeEncode, ptrStrictRep_encodeLeast⟩,
    ⟨noneRep_decodeMono _, fun p => ptrStrictRep_decodeEncode p, ?_⟩,
    reqProvPtrRepInc_threeLaws, ptrDegradeRepInc_lawful_by_ptrValLe,
    ⟨intStripRepInc_decodeMono, intStripRepInc_decodeEncode, intStripRepInc_encodeLeast⟩⟩
  intro x p hx i hi
  have hxe : x.bytes = ptrEncode p := (ptrDecodeStrict_eq_some_iff x.bytes p).mp hx
  show AByte.leProvInc (ptrEncode p)[i] x.bytes[i]
  rw [hxe]
  obtain ⟨a, q⟩ := p
  cases q <;> simp [ptrEncode, AByte.leProvInc]

/-- Tightness of `b0` in R6d: with byte type `Empty` and size 1 there are no pointer values, so
the always-failing decoder satisfies both laws (`p0 := ()`). -/
theorem no_ptr_decoder_tight_b0 :
    ¬ (∀ d : PBytesInc Empty Unit 1 → Option (Vector Empty 1 × Option Unit),
        ¬ ((⟨ptrEncodeInc, d⟩ : Rep (PBytesInc Empty Unit 1) (Vector Empty 1 × Option Unit)).DecodeMono ∧
           (⟨ptrEncodeInc, d⟩ : Rep (PBytesInc Empty Unit 1) (Vector Empty 1 × Option Unit)).DecodeEncode)) := by
  intro h
  exact h (fun _ => none) ⟨fun _ _ _ => trivial, fun p => (p.1[0]).elim⟩

/-- With provenance type `Empty`, the provenance-increasing order relates only equal vectors
above initialized bytes. -/
theorem eq_of_leProvInc_empty {β : Type} {m : Nat} {x y : PBytesInc β Empty m} (hxy : x ⊑ y)
    (hx : x.bytes.IsInit) : y.bytes = x.bytes := by
  apply Vector.ext
  intro i hi
  have h1 := hxy i hi
  have h2 := hx i hi
  revert h1 h2
  cases x.bytes[i] with
  | uninit => intro _ h2; cases h2
  | init d =>
    intro h1 _
    obtain ⟨d', hd', h1', _⟩ := (leProvInc_init_iff _ _).mp h1
    rw [hd']
    obtain ⟨a, q⟩ := d
    obtain ⟨b, q'⟩ := d'
    cases q with
    | some e => exact e.elim
    | none =>
      cases q' with
      | some e => exact e.elim
      | none => simp only at h1'; rw [h1']

/-- Tightness of `p0` in R6d: with provenance type `Empty`, the strict pointer decoder satisfies
`DecodeMono` and `DecodeEncode` under the provenance-increasing order (`b0 := 0`, size 1). -/
theorem no_ptr_decoder_tight_p0 :
    ¬ (∀ d : PBytesInc Byte Empty 1 → Option (Vector Byte 1 × Option Empty),
        ¬ ((⟨ptrEncodeInc, d⟩ : Rep (PBytesInc Byte Empty 1) (Vector Byte 1 × Option Empty)).DecodeMono ∧
           (⟨ptrEncodeInc, d⟩ : Rep (PBytesInc Byte Empty 1) (Vector Byte 1 × Option Empty)).DecodeEncode)) := by
  intro h
  apply h (fun x => ptrDecodeStrict x.bytes)
  refine ⟨?_, fun p => ptrStrictRep_decodeEncode p⟩
  intro x y hxy
  change ptrDecodeStrict x.bytes ⊑ ptrDecodeStrict y.bytes
  cases hx : ptrDecodeStrict x.bytes with
  | none => exact OptLe.none_le _
  | some p =>
    have hxe := (ptrDecodeStrict_eq_some_iff _ _).mp hx
    have hxi : x.bytes.IsInit := by rw [hxe]; exact Bytes.isInit_ofData _
    rw [eq_of_leProvInc_empty hxy hxi, hx]
    exact OptLe.refl _

/-- Non-vacuity for R6d: a byte value and a provenance exist for `Byte`, `Unit`. -/
theorem no_ptr_decoder_nonvacuous : ∃ (_ : Byte) (_ : Unit), True :=
  ⟨0, (), trivial⟩

/-! ## R6e: composition (R3) fails when provenance increases definedness (fully proved) -/

/-- **R6e (counterexample).** Under the provenance-increasing order, take `A = C` = pointers that
always carry provenance and `B` = provenance-stripping integers (size 1, provenance `Unit`).
All three representations satisfy all three laws (flat order on decoded values), every encoding
of `B` is fully initialized, and `A → B` is total; yet `A → B → C` differs from the direct
`A → C` transmute at `(#v[0], ())`: the composite fails, the direct transmute succeeds. The
analogue of R3's `IntoBytes B` does not help here because fully initialized bytes without
provenance are not maximal in this order. -/
theorem transmute_comp_fails_of_provInc :
    ((reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).DecodeMono ∧
      (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).DecodeEncode ∧
      (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).EncodeLeast) ∧
    ((intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).DecodeMono ∧
      (intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).DecodeEncode ∧
      (intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).EncodeLeast) ∧
    (∀ x : Vector Byte 1,
      ((intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).encode x).bytes.IsInit) ∧
    TransmuteTotal (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit))
      intStripRepInc ∧
    (transmute (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit))
        intStripRepInc (#v[0], ())).bind
        (transmute (intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1))
          (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit))) = none ∧
    transmute (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit))
        reqProvPtrRepInc (#v[0], ()) = some (#v[0], ()) := by
  have h1 : transmute (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit))
      intStripRepInc (#v[0], ()) = some #v[0] := intDecodeStrip_ptrEncode _
  have h2 : transmute (intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1))
      reqProvPtrRepInc #v[0] = none := by
    cases hc : transmute (intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1))
        (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)) #v[0] with
    | none => rfl
    | some vp =>
      have he := (reqProvPtrRepInc_decode_eq_some_iff _ vp).mp hc
      have h0 := congrArg (fun y : PBytes Byte Unit 1 => y[0]) he
      simp only [intStripRepInc, intEncodeInc, intEncode, ptrEncode, Bytes.getElem_ofData,
        Vector.getElem_map] at h0
      injection h0 with h0
      injection h0 with _ h0
      cases h0
  refine ⟨reqProvPtrRepInc_threeLaws,
    ⟨intStripRepInc_decodeMono, intStripRepInc_decodeEncode, intStripRepInc_encodeLeast⟩,
    fun x => Bytes.isInit_ofData _, fun vp => ⟨vp.1, intDecodeStrip_ptrEncode _⟩, ?_,
    reqProvPtrRepInc_threeLaws.2.1 _⟩
  rw [h1, Option.bind_some, h2]

/-! ## Definition examples for the provenance model -/

theorem ex_leProvInc_pos :
    AByte.leProvInc (.init ((5 : Byte), (none : Option Unit))) (.init (5, some ())) ∧
    AByte.leProvInc (.init ((5 : Byte), some ())) (.init (5, some ())) :=
  ⟨rfl, ⟨rfl, rfl⟩⟩

theorem ex_leProvInc_neg :
    ¬ AByte.leProvInc (.init ((5 : Byte), some ())) (.init (5, none)) ∧
    ¬ AByte.leProvInc (.init ((5 : Byte), (none : Option Unit))) (.init (6, none)) :=
  ⟨fun h => (by cases h.2), fun h => (by decide : ¬ ((5 : Byte) = 6)) h⟩

theorem ex_intDecodeStrip_pos :
    intDecodeStrip (#v[.init ((7 : Byte), some ())] : PBytes Byte Unit 1) = some #v[7] := by
  rw [← ptrEncode_singleton]
  exact intDecodeStrip_ptrEncode (#v[7], some ())

theorem ex_intDecodeStrict_neg :
    intDecodeStrict (#v[.init ((7 : Byte), some ())] : PBytes Byte Unit 1) = none := by
  rw [← ptrEncode_singleton]
  exact transmute_ptr_intStrict_eq_none (n := 0) ptrDecodeStrict #v[7] ()

theorem ex_intDecodeStrict_pos :
    intDecodeStrict (#v[.init ((7 : Byte), none)] : PBytes Byte Unit 1) = some #v[7] :=
  (intDecodeStrict_eq_some_iff _ _).mpr (intEncode_singleton 7).symm

theorem ex_ptrDecodeStrict_pos :
    ptrDecodeStrict (#v[.init ((7 : Byte), some ())] : PBytes Byte Unit 1) = some (#v[7], some ()) :=
  (ptrDecodeStrict_eq_some_iff _ _).mpr (ptrEncode_singleton 7 (some ())).symm

theorem ex_ptrDecodeStrict_neg :
    ptrDecodeStrict (#v[.init ((7 : Byte), some ()), .init (8, none)] : PBytes Byte Unit 2) = none := by
  cases h : ptrDecodeStrict (#v[.init ((7 : Byte), some ()), .init (8, none)] : PBytes Byte Unit 2) with
  | none => rfl
  | some p =>
    have h' := (ptrDecodeStrict_eq_some_iff _ _).mp h
    have e0 := congrArg (fun y : PBytes Byte Unit 2 => y[0]) h'
    have e1 := congrArg (fun y : PBytes Byte Unit 2 => y[1]) h'
    simp only [ptrEncode, Bytes.getElem_ofData, Vector.getElem_map] at e0 e1
    injection e0 with e0
    injection e1 with e1
    injection e0 with _ e0
    injection e1 with _ e1
    rw [← e0] at e1
    cases e1

theorem ex_ptrDecodeReqProv_neg :
    ptrDecodeReqProv (#v[.init ((7 : Byte), none)] : PBytes Byte Unit 1) = none := by
  unfold ptrDecodeReqProv
  rw [show (#v[.init ((7 : Byte), none)] : PBytes Byte Unit 1) = Bytes.ofData #v[(7, none)] from
    (Bytes.ofData_singleton _).symm, Bytes.toData?_ofData]
  simp

theorem ex_intDecodeStrip_neg :
    intDecodeStrip (#v[.uninit] : PBytes Byte Unit 1) = none := rfl

theorem ex_ptrDecodeReqProv_pos :
    ptrDecodeReqProv (#v[.init ((7 : Byte), some ())] : PBytes Byte Unit 1) =
      some (#v[7], some ()) := by
  unfold ptrDecodeReqProv
  rw [show (#v[.init ((7 : Byte), some ())] : PBytes Byte Unit 1) = Bytes.ofData #v[(7, some ())] from
    (Bytes.ofData_singleton _).symm, Bytes.toData?_ofData]
  simp

theorem ex_reqProvPtrRepInc_pos :
    (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).decode
      ⟨#v[.init (7, some ())]⟩ = some (#v[7], ()) :=
  (reqProvPtrRepInc_decode_eq_some_iff _ _).mpr (ptrEncode_singleton 7 (some ())).symm

theorem ex_reqProvPtrRepInc_neg :
    (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).decode
      ⟨#v[.init (7, none)]⟩ = none := by
  cases hc : (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).decode
      ⟨#v[.init (7, none)]⟩ with
  | none => rfl
  | some vp =>
    have he := (reqProvPtrRepInc_decode_eq_some_iff _ vp).mp hc
    have h0 := congrArg (fun y : PBytes Byte Unit 1 => y[0]) he
    simp only [ptrEncode, Bytes.getElem_ofData, Vector.getElem_map] at h0
    injection h0 with h0
    injection h0 with _ h0
    cases h0

theorem ex_ptrValLe_pos :
    PtrValLe (some ((#v[7] : Vector Byte 1), (none : Option Unit))) (some (#v[7], some ())) ∧
    PtrValLe (some ((#v[7] : Vector Byte 1), some ())) (some (#v[7], some ())) :=
  ⟨rfl, ⟨rfl, rfl⟩⟩

theorem ex_ptrValLe_neg :
    ¬ PtrValLe (some ((#v[7] : Vector Byte 1), some ())) (some (#v[7], (none : Option Unit))) ∧
    ¬ PtrValLe (some ((#v[7] : Vector Byte 1), (none : Option Unit))) none :=
  ⟨fun h => (by cases h.2), fun h => h⟩

theorem ex_ptrDecodeDegrade_pos :
    ptrDecodeDegrade (#v[.init ((7 : Byte), some ()), .init (8, none)] : PBytes Byte Unit 2) =
      some (#v[7, 8], none) := by
  rw [show (#v[.init ((7 : Byte), some ()), .init (8, none)] : PBytes Byte Unit 2) =
      Bytes.ofData #v[(7, some ()), (8, none)] from (Bytes.ofData_pair _ _).symm,
    ptrDecodeDegrade_ofData]
  have hn : ¬ ∀ (i : Nat) (h : i < 1 + 1),
      (#v[((7 : Byte), some ()), (8, none)] : Vector (Byte × Option Unit) 2)[i].2 =
        (#v[((7 : Byte), some ()), (8, none)] : Vector (Byte × Option Unit) 2)[0].2 := by
    intro h
    have := h 1 (by decide)
    simp at this
  rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
  congr 2
  apply Vector.ext
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem ex_ptrDecodeDegrade_neg :
    ptrDecodeDegrade (#v[.init ((7 : Byte), some ()), .uninit] : PBytes Byte Unit 2) = none := by
  unfold ptrDecodeDegrade
  rw [Bytes.toData?_eq_none_of_not_isInit (fun h => by cases h 1 (by decide))]

theorem ex_provIntRep_pos :
    (provIntRep : Rep (PBytes Byte Unit 1) (Vector (Byte × Option Unit) 1)).decode
      #v[.init (7, some ())] = some #v[(7, some ())] := by
  rw [← Bytes.ofData_singleton]
  exact Bytes.toData?_ofData _

theorem ex_provIntRep_neg :
    (provIntRep : Rep (PBytes Byte Unit 1) (Vector (Byte × Option Unit) 1)).decode
      #v[.uninit] = none := rfl

/-- Modeling gap (no byte positions in provenance tags): duplicating byte 0 of the two-byte
pointer `(#v[16, 32], some ())` gives bytes that the strict decoder accepts as the pointer
`(#v[16, 16], some ())`, i.e. a different address with the same provenance. -/
theorem ex_ptrDecodeStrict_accepts_duplicated_byte :
    ptrDecodeStrict (#v[.init ((16 : Byte), some ()), .init (32, some ())] : PBytes Byte Unit 2) =
      some (#v[16, 32], some ()) ∧
    ptrDecodeStrict (#v[.init ((16 : Byte), some ()), .init (16, some ())] : PBytes Byte Unit 2) =
      some (#v[16, 16], some ()) := by
  constructor <;>
  · apply (ptrDecodeStrict_eq_some_iff _ _).mpr
    apply Vector.ext
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [ptrEncode]

/-! ## Boundary of the MiniRust escape hatch for R6d -/

/-- MiniRust's value order alone does not rescue the strict decoder at multi-byte sizes: at size
2, `[init (7, none), init (8, none)] ⊑ [init (7, some ()), init (8, none)]`, the first decodes to
the pointer `(#v[7, 8], none)` and the second (mixed provenance) fails, so the strict decoder is
not monotone even for `PtrValLe`. A lawful decoder must degrade mixed provenance to `none` as
`ptrDecodeDegrade` does. -/
theorem ptrStrictRepInc_not_decodeMonoBy_ptrValLe :
    ¬ (ptrStrictRepInc : Rep (PBytesInc Byte Unit 2) (Vector Byte 2 × Option Unit)).DecodeMonoBy
      PtrValLe := by
  intro h
  have hle : (⟨#v[.init ((7 : Byte), none), .init (8, none)]⟩ : PBytesInc Byte Unit 2) ⊑
      ⟨#v[.init (7, some ()), .init (8, none)]⟩ := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact rfl
    · exact rfl
  have h1 := h _ _ hle
  have hx : ptrDecodeStrict (#v[.init ((7 : Byte), none), .init (8, none)] : PBytes Byte Unit 2) =
      some (#v[7, 8], none) := by
    apply (ptrDecodeStrict_eq_some_iff _ _).mpr
    apply Vector.ext
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [ptrEncode]
  change PtrValLe (ptrDecodeStrict (#v[.init ((7 : Byte), none), .init (8, none)] : PBytes Byte Unit 2))
    (ptrDecodeStrict (#v[.init ((7 : Byte), some ()), .init (8, none)] : PBytes Byte Unit 2)) at h1
  rw [hx, ex_ptrDecodeStrict_neg] at h1
  exact h1

end Toy.Repr
