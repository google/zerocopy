import ToyZc.KnownLayout

/-!
# Result group 7: what the checks and the model do not capture (fully proved evidence)

* `immutable_not_byte_determined` (R7a, impossibility): no property of descriptions that depends
  only on their byte-level semantics (layout, typing, encoder, decoder) coincides with zerocopy's
  `Immutable`; `UnsafeCell<u8>` and `u8` have the same byte semantics but differ in `Immutable`.
  Positive control `pc_fromBytes_byte_determined`: semantic `FromBytes` *is* byte-determined.
* `union_fromBytes_derive_not_necessary` / `union_fromZeros_derive_not_necessary` (R7b): in the
  model, the union derives' requirement that *every* field be `FromBytes` (`FromZeros`) is not
  necessary: one suitable field suffices for the semantic property.
* `unaligned_check_conjuncts_necessary` (R7c): each conjunct of the modeled `Unaligned` derive's
  struct (`repr(C)` and `repr(transparent)`), enum, and union checks is needed: for each conjunct
  there is a description that fails only that conjunct and has alignment ≠ `1`.

Not formalized at all (see the report's boundaries): pointer provenance (the model's bytes carry no
provenance, and at the pinned commit zerocopy implements neither `FromBytes` nor `IntoBytes` for raw
pointers, `zerocopy/src/impls.rs:951-954`), generic types (the `IntoBytes` derive's generic paths,
`zerocopy/zerocopy-derive/src/derive/into_bytes.rs:145-181`), field invariants, and slice DSTs inside
derived types.
-/

namespace Toy.Zc

/-- Two descriptions have the same byte-level semantics: same layout, same typing judgment, same
encoder, and same decoder. -/
def SameBytes (d₁ d₂ : Desc) : Prop :=
  d₁.layout = d₂.layout ∧ (∀ v, d₁.hasType v = d₂.hasType v) ∧
    (∀ v, d₁.encodeL v = d₂.encodeL v) ∧ (∀ x, d₁.decodeL x = d₂.decodeL x)

/-- A property of descriptions is determined by their byte-level semantics. -/
def ByteDetermined (P : Desc → Prop) : Prop := ∀ d₁ d₂, SameBytes d₁ d₂ → (P d₁ ↔ P d₂)

theorem sameBytes_refl (d : Desc) : SameBytes d d :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- `UnsafeCell<T>` has the byte semantics of `T`. -/
theorem sameBytes_cell (t : Desc) : SameBytes (.cell t) t :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem ex_sameBytes_neg : ¬ SameBytes .u8 .bool := by
  intro h
  have := h.2.1 (.int [0])
  revert this
  decide

theorem ex_byteDetermined_neg : ¬ ByteDetermined (fun d => implImmutable d = true) := by
  intro h
  have := (h _ _ (sameBytes_cell .u8)).mpr rfl
  revert this
  decide

theorem validInit_congr {d₁ d₂ : Desc} (h : SameBytes d₁ d₂) (bs : List Byte) :
    validInit d₁ bs = validInit d₂ bs := by
  unfold validInit
  rw [h.2.2.2]
  cases d₂.decodeL (bs.map AByte.init) with
  | none => rfl
  | some v => exact h.2.1 v

/-- **R7a (impossibility).** No byte-determined property of descriptions coincides with zerocopy's
`Immutable` (as modeled by `implImmutable`). The contrast is with the semantic byte-level predicates
(`SemFromBytes` is byte-determined, `pc_fromBytes_byte_determined`); the syntactic derive checks
`implFromBytes`/`implFromZeros` are not byte-determined either (they reject some semantically
qualifying types, R7b), so the point is that `Immutable` has no byte-level semantic counterpart. -/
theorem immutable_not_byte_determined :
    ¬ ∃ P : Desc → Prop, ByteDetermined P ∧ ∀ d, P d ↔ implImmutable d = true := by
  rintro ⟨P, hP, hiff⟩
  have h1 : P Desc.u8 := (hiff _).mpr rfl
  have h2 : P (.cell Desc.u8) := (hP _ _ (sameBytes_cell _)).mpr h1
  have h3 := (hiff _).mp h2
  revert h3
  decide

/-- Positive control for R7a: semantic `FromBytes` is byte-determined (so the byte-level view does
decide the byte-level traits). -/
theorem pc_fromBytes_byte_determined :
    ∃ P : Desc → Prop, ByteDetermined P ∧ ∀ d, P d ↔ SemFromBytes d := by
  refine ⟨SemFromBytes, fun d₁ d₂ h => ?_, fun _ => Iff.rfl⟩
  rw [semFromBytes_iff_validInit_total, semFromBytes_iff_validInit_total]
  have hs : d₁.size = d₂.size := by simp only [Desc.size, h.1]
  simp only [hs, validInit_congr h]

/-- Non-vacuity for R7a: the witness pair `UnsafeCell<u8>` / `u8`. -/
theorem nv_immutable_witness :
    SameBytes (.cell .u8) .u8 ∧ implImmutable (.cell .u8) = false ∧ implImmutable .u8 = true :=
  ⟨sameBytes_cell _, rfl, rfl⟩

/-- **R7b (FromBytes).** `union { a: u8, b: bool }` is semantically `FromBytes` (every byte is a
valid `a`, and the union's validity is "some field is valid"), but the derive rejects it because
`bool` is not `FromBytes`. -/
theorem union_fromBytes_derive_not_necessary :
    SemFromBytes (.union (.c .none) [.u8, .bool]) ∧
    implFromBytes (.union (.c .none) [.u8, .bool]) = false := by
  refine ⟨?_, by decide⟩
  rw [semFromBytes_iff_validInit_total]
  intro bs h
  match bs, h with
  | [_], _ => rfl

/-- **R7b (FromZeros).** `union { a: u8, b: E }` with `E` lacking a zero discriminant is
semantically `FromZeros`, but the derive rejects it. -/
theorem union_fromZeros_derive_not_necessary :
    SemFromZeros (.union (.c .none) [.u8, Desc.noZero]) ∧
    implFromZeros (.union (.c .none) [.u8, Desc.noZero]) = false := by
  refine ⟨?_, by decide⟩
  rw [semFromZeros_iff_validInit_zeros]
  decide

/-- **R7c.** Each conjunct of the modeled `Unaligned` derive's checks (`implUnaligned`) is necessary:
for each conjunct, there is a description (listed below) that satisfies every other conjunct of its
check, fails that one, is rejected by the check, and has alignment ≠ `1`. The checks are
`strct (.c m) fs`: `!m.isAlignGt1 && (m.isPacked1 || allUnaligned fs)`;
`strct .transparent fs`: `allUnaligned fs`;
`enm r vs`: `(r == .prim .u8 || r == .prim .i8) && variantsUnaligned vs`;
`union (.c m) fs`: `!m.isAlignGt1 && (m.isPacked1 || allUnaligned fs)`.
1. struct, `!is_align_gt_1`: `#[repr(C, align(2))] struct { a: u8 }`;
2. struct, "`is_packed_1` or all fields `Unaligned`": `#[repr(C)] struct { a: u8, b: u16 }`;
3. `repr(transparent)` struct, all fields `Unaligned`: `#[repr(transparent)] struct { a: u16 }`;
4. enum, `repr(u8)`/`repr(i8)`: `#[repr(u16)] enum { A }` and `#[repr(C)] enum { A }`;
5. enum, all fields `Unaligned`: `#[repr(u8)] enum { A(u16) }`;
6. union, `!is_align_gt_1`: `#[repr(C, align(2))] union { a: u8 }`;
7. union, "`is_packed_1` or all fields `Unaligned`": `#[repr(C)] union { a: u8, b: u16 }`. -/
theorem unaligned_check_conjuncts_necessary :
    -- 1
    ((ReprModifier.aligned 2).isAlignGt1 = true ∧
      ((ReprModifier.aligned 2).isPacked1 || allUnaligned [.u8]) = true ∧
      implUnaligned (.strct (.c (.aligned 2)) [.u8]) = false ∧
      ¬ SemUnaligned (.strct (.c (.aligned 2)) [.u8])) ∧
    -- 2
    ((ReprModifier.none).isAlignGt1 = false ∧ (ReprModifier.none).isPacked1 = false ∧
      allUnaligned [.u8, .u16] = false ∧
      implUnaligned (.strct (.c .none) [.u8, .u16]) = false ∧
      ¬ SemUnaligned (.strct (.c .none) [.u8, .u16])) ∧
    -- 3
    (allUnaligned [.u16] = false ∧
      implUnaligned (.strct .transparent [.u16]) = false ∧
      ¬ SemUnaligned (.strct .transparent [.u16])) ∧
    -- 4
    (variantsUnaligned [(.implicit, [])] = true ∧
      EnumRepr.prim .u16 ≠ .prim .u8 ∧ EnumRepr.prim .u16 ≠ .prim .i8 ∧
      implUnaligned (.enm (.prim .u16) [(.implicit, [])]) = false ∧
      ¬ SemUnaligned (.enm (.prim .u16) [(.implicit, [])]) ∧
      EnumRepr.c ≠ .prim .u8 ∧ EnumRepr.c ≠ .prim .i8 ∧
      implUnaligned (.enm .c [(.implicit, [])]) = false ∧
      ¬ SemUnaligned (.enm .c [(.implicit, [])])) ∧
    -- 5
    (variantsUnaligned [(.implicit, [.u16])] = false ∧
      implUnaligned (.enm (.prim .u8) [(.implicit, [.u16])]) = false ∧
      ¬ SemUnaligned (.enm (.prim .u8) [(.implicit, [.u16])])) ∧
    -- 6
    ((ReprModifier.aligned 2).isAlignGt1 = true ∧
      ((ReprModifier.aligned 2).isPacked1 || allUnaligned [.u8]) = true ∧
      implUnaligned (.union (.c (.aligned 2)) [.u8]) = false ∧
      ¬ SemUnaligned (.union (.c (.aligned 2)) [.u8])) ∧
    -- 7
    ((ReprModifier.none).isAlignGt1 = false ∧ (ReprModifier.none).isPacked1 = false ∧
      allUnaligned [.u8, .u16] = false ∧
      implUnaligned (.union (.c .none) [.u8, .u16]) = false ∧
      ¬ SemUnaligned (.union (.c .none) [.u8, .u16])) := by
  unfold SemUnaligned
  decide

end Toy.Zc
