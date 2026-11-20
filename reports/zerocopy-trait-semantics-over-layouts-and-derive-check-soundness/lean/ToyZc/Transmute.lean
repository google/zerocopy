import ToyZc.Enum

/-!
# Result group 5: transmutation

zerocopy's `transmute!` behaves like `fn transmute<Src: IntoBytes, Dst: FromBytes>(src: Src) -> Dst`
with `size_of::<Src>() == size_of::<Dst>()` (`zerocopy/src/macros.rs:15-28`); with
`#![allow(shrink)]` it also accepts `size_of::<Src>() >= size_of::<Dst>()`
(`zerocopy/src/macros.rs:40-49`), implemented by transmuting the source into a
`#[repr(C, packed)]` union and reading the destination field (`zerocopy/src/macros.rs:106-146`).
`transmuteVal` models that union-transmute: the destination reads the first `size Dst` bytes of the
source's encoding, with bytes past the end of the source `uninit`. (`core::mem::TransmuteFrom` uses
the same union-transmute notion of soundness and additionally permits a larger destination whose
extra bytes are trailing padding; `transmute_extend_into_trailing_padding_example` shows the model
agrees.)

* `transmuteTotal_of_intoBytes_of_fromBytes` (R5a): for representations in the same carrier,
  `IntoBytes A` and `FromBytes B` make `decode_B ∘ encode_A` total.
* `desc_transmute_total_of_size_ge` (R5b): over descriptions, `IntoBytes Src`, `FromBytes Dst` and
  `size Dst ≤ size Src` make the transmute total (reading the destination from the start of the
  source's bytes).
* `desc_transmute_total_of_size_eq`: the special case `size Src = size Dst` (the bounds of
  `transmute!`), a one-line corollary of R5b kept as a reference point.
* `ce_transmute_drop_size`: `size Dst ≤ size Src` cannot be dropped from the uniform statement
  (`u8 → u16` fails).
-/

namespace Toy.Zc

/-- **R5a.** For representations of equal size, if no encoding of `A` contains `uninit`
(`IntoBytes A`) and every fully initialized byte vector decodes as `B` (`FromBytes B`), then
`transmute A → B` never fails. -/
theorem transmuteTotal_of_intoBytes_of_fromBytes {D A B : Type} {n : Nat}
    (ra : Rep (Bytes D n) A) (rb : Rep (Bytes D n) B)
    (hA : ra.IntoBytes) (hB : rb.FromBytes) : TransmuteTotal ra rb := fun a => hB _ (hA a)

/-- Transmute a value `v` of `s` to `d`: the destination reads `d.size` bytes from the start of the
source's bytes; bytes past the end of the source are `uninit` (as when the source is written into
one field of a `repr(C)` union and the destination is read from another). The result is kept only
if it is a well-typed value of `d`. -/
def transmuteVal (s d : Desc) (v : Val) : Option Val :=
  match d.decodeL (fit d.size (s.encodeL v)) with
  | some w => if d.hasType w then some w else none
  | none => none

theorem ex_transmuteVal_pos : transmuteVal .u16 (.array .u8 2) (.int [1, 2]) =
    some (.array [.int [1], .int [2]]) := rfl
theorem ex_transmuteVal_neg : transmuteVal .u8 .bool (.int [2]) = none := by decide

/-- **R5b.** If `Src` is `IntoBytes`, `Dst` is `FromBytes`, and `Dst` is no larger than `Src`,
transmuting any value of `Src` to `Dst` succeeds. -/
theorem desc_transmute_total_of_size_ge (s d : Desc) (hsz : d.size ≤ s.size)
    (hI : SemIntoBytes s) (hF : SemFromBytes d) :
    ∀ v, s.hasType v = true → (transmuteVal s d v).isSome = true := by
  intro v hv
  have hlen := encodeL_length s v
  have hfit : fit d.size (s.encodeL v) = (s.encodeL v).take d.size := fit_eq_take (by omega)
  obtain ⟨bs, hbs⟩ := exists_map_init_of_forall_isInit ((s.encodeL v).take d.size)
    (fun b hb => encodeL_forall_isInit hI hv b (List.mem_of_mem_take hb))
  have hbl : bs.length = d.size := by
    have := congrArg List.length hbs
    simp at this
    omega
  have hval := (semFromBytes_iff_validInit_total d).mp hF bs hbl
  unfold transmuteVal
  rw [hfit, hbs]
  unfold validInit at hval
  split at hval
  · rename_i w hw
    rw [hw]
    simp [hval]
  · cases hval

/-- The `transmute!` case (reference point): `IntoBytes Src`, `FromBytes Dst`, and equal sizes make
the transmute total. A one-line corollary of R5b; equality is stronger than needed
(`transmute_shrink_example`). -/
theorem desc_transmute_total_of_size_eq (s d : Desc) (hsz : s.size = d.size)
    (hI : SemIntoBytes s) (hF : SemFromBytes d) :
    ∀ v, s.hasType v = true → (transmuteVal s d v).isSome = true :=
  desc_transmute_total_of_size_ge s d (Nat.le_of_eq hsz.symm) hI hF

/-! ## Non-vacuity and counterexamples -/

/-- Non-vacuity of R5a: `u16 → i16` in the `Desc.rep` representations (same carrier). -/
theorem nv_transmuteTotal_rep :
    (Desc.int .u16).rep.IntoBytes ∧ (Desc.int .i16).rep.FromBytes :=
  ⟨semIntoBytes_int _, semFromBytes_int _⟩

/-- Non-vacuity of R5b (and of its equal-size corollary `desc_transmute_total_of_size_eq`):
`u16 → i16` (equal sizes) and `u32 → u16` (shrinking). -/
theorem nv_desc_transmute :
    (Desc.u16).size = (Desc.int .i16).size ∧ SemIntoBytes .u16 ∧ SemFromBytes (.int .i16) ∧
    (Desc.u16).size ≤ (Desc.u32).size ∧ SemIntoBytes .u32 ∧ SemFromBytes .u16 :=
  ⟨rfl, semIntoBytes_int _, semFromBytes_int _, by decide, semIntoBytes_int _, semFromBytes_int _⟩

/-- Equality of sizes is not necessary: shrinking `u32 → u16` keeps the low-address bytes. -/
theorem transmute_shrink_example :
    transmuteVal .u32 .u16 (.int [1, 2, 3, 4]) = some (.int [1, 2]) := rfl

/-- **`size Dst ≤ size Src` is not necessary for a fixed pair** (the size-extension case of
`core::mem::TransmuteFrom`). `u8` (size 1) to `#[repr(C, align(2))] struct { a: u8 }` (size 2):
every `u8` value transmutes, because the destination's second byte is trailing padding that the
decoder never reads. So `hsz` in R5b is necessary only for the statement quantified over all
`FromBytes` destinations (`ce_transmute_drop_size`), not for each pair. -/
theorem transmute_extend_into_trailing_padding_example :
    Desc.u8.size < Desc.alignedByte.size ∧ SemIntoBytes .u8 ∧
    ∀ v, Desc.u8.hasType v = true → (transmuteVal .u8 Desc.alignedByte v).isSome = true := by
  refine ⟨by decide, semIntoBytes_int _, ?_⟩
  intro v hv
  cases v with
  | int bs =>
    simp only [Desc.hasType, IntTy.width, beq_iff_eq] at hv
    match bs, hv with
    | [b], _ => rfl
  | _ => simp [Desc.hasType] at hv

/-- **Tightness of `hsz` in R5b.** `u8 → u16`: `u8` is `IntoBytes`, `u16` is `FromBytes`, but the
destination's second byte is `uninit`, so the transmute fails. -/
theorem ce_transmute_drop_size :
    ¬ (Desc.u16.size ≤ Desc.u8.size) ∧ SemIntoBytes .u8 ∧ SemFromBytes .u16 ∧
    Desc.u8.hasType (.int [7]) = true ∧ transmuteVal .u8 .u16 (.int [7]) = none :=
  ⟨by decide, semIntoBytes_int _, semFromBytes_int _, by decide, by decide⟩

/-- **Tightness of `hI` in R5b (and its equal-size corollary `desc_transmute_total_of_size_eq`).** The padded pair `{ u8, u16 }` (4 bytes, not `IntoBytes`) to
`u32` (`FromBytes`) fails on the padding byte. -/
theorem ce_transmute_drop_intoBytes :
    Desc.paddedPair.size = Desc.u32.size ∧ ¬ SemIntoBytes Desc.paddedPair ∧ SemFromBytes .u32 ∧
    Desc.paddedPair.hasType (.strct [.int [1], .int [2, 3]]) = true ∧
    transmuteVal Desc.paddedPair .u32 (.strct [.int [1], .int [2, 3]]) = none :=
  ⟨by decide, not_semIntoBytes_paddedPair, semFromBytes_int _, by decide, by decide⟩

/-- **Tightness of `hF` in R5b (and its equal-size corollary `desc_transmute_total_of_size_eq`).** `u8 → bool` fails on the byte `2`. -/
theorem ce_transmute_drop_fromBytes :
    Desc.u8.size = Desc.bool.size ∧ SemIntoBytes .u8 ∧ ¬ SemFromBytes .bool ∧
    Desc.u8.hasType (.int [2]) = true ∧ transmuteVal .u8 .bool (.int [2]) = none :=
  ⟨rfl, semIntoBytes_int _, not_semFromBytes_bool, by decide, by decide⟩

/-- **Tightness of `hA` in R5a** (in the `Desc.rep` representations): the padded pair to `u32`. -/
theorem ce_transmuteTotal_drop_intoBytes :
    ∃ (ra : Rep (Bytes Byte 4) (TVal Desc.paddedPair)) (rb : Rep (Bytes Byte 4) (TVal Desc.u32)),
      ¬ ra.IntoBytes ∧ rb.FromBytes ∧ ¬ TransmuteTotal ra rb := by
  refine ⟨Desc.paddedPair.rep, Desc.u32.rep, not_semIntoBytes_paddedPair, semFromBytes_int _, ?_⟩
  intro h
  obtain ⟨b, hb⟩ := h ⟨.strct [.int [1], .int [2, 3]], by decide⟩
  revert hb
  simp only [transmute]
  intro hb
  have : (Desc.u32.rep.decode (Desc.paddedPair.rep.encode
      ⟨.strct [.int [1], .int [2, 3]], by decide⟩)).isSome = false := by decide
  rw [hb] at this
  cases this

/-- **Tightness of `hB` in R5a** (in the `Desc.rep` representations): `u8` to `bool`. -/
theorem ce_transmuteTotal_drop_fromBytes :
    ∃ (ra : Rep (Bytes Byte 1) (TVal Desc.u8)) (rb : Rep (Bytes Byte 1) (TVal Desc.bool)),
      ra.IntoBytes ∧ ¬ rb.FromBytes ∧ ¬ TransmuteTotal ra rb := by
  refine ⟨Desc.u8.rep, Desc.bool.rep, semIntoBytes_int _, not_semFromBytes_bool, ?_⟩
  intro h
  obtain ⟨b, hb⟩ := h ⟨.int [2], by decide⟩
  revert hb
  simp only [transmute]
  intro hb
  have : (Desc.bool.rep.decode (Desc.u8.rep.encode ⟨.int [2], by decide⟩)).isSome = false := by
    decide
  rw [hb] at this
  cases this

end Toy.Zc
