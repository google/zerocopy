import Toy.WrapNiche.Op

/-!
# Definition examples (fully proved)

For each definition: intended positive examples it admits and negative examples it rejects
(for functions: evaluation examples, including the wrapping and degenerate cases).
-/

namespace Toy.WrapNiche

open Imported

/-! ## Concrete objects used throughout the examples and witnesses -/

/-- Valid set `{0, 2}` in `Fin 4` (fragmented: its hull `[0, 2]` contains the niche `1`). -/
def V02 : Fin 4 → Bool := fun x => x.val == 0 || x.val == 2

/-- Valid set `{0, 1}` in `Fin 4` (an interval). -/
def V01 : Fin 4 → Bool := fun x => decide (x.val < 2)

/-- Valid set `{0}` in `Fin 4`. -/
def V0 : Fin 4 → Bool := fun x => x.val == 0

/-- One-byte payload with valid values `0..=252` (niches `253, 254, 255`). -/
def Vlow : Validity 1 := fun x => decide (x.val < 253)

/-- One-byte payload with valid values `0..=253` (niches `254, 255`). -/
def Vlt254 : Validity 1 := fun x => decide (x.val < 254)

/-- One-byte payload with valid values `1..=253` (niches `254, 255, 0`; they wrap). -/
def Vmid : Validity 1 := fun x => decide (1 ≤ x.val ∧ x.val ≤ 253)

/-- An affine encoding whose three tags `254, 255, 0` wrap around. -/
def A0 : AffineNiche 256 := ⟨0, 2, 254⟩

/-- An affine encoding with tags `253, 254, 255` for variants `0, 1, 2`. -/
def Ag : AffineNiche 256 := ⟨0, 2, 253⟩

/-- Three variants, the untagged variant in the middle (`u = 1`), all inhabited. -/
def E1 : EnumSpec := ⟨3, 1, fun _ => true⟩

/-- Three variants, `u = 0`, variant `1` uninhabited. -/
def E2 : EnumSpec := ⟨3, 0, fun i => i != 1⟩

/-- The operational layout: a 1-byte niche field at byte offset 1, enum `E1`, encoding `Ag`
(tag `253` = variant 0, `254` = dead slot of `u`, `255` = variant 2), valid values `0..=252`. -/
def Lop : OpLayout := ⟨1, 1, E1, Ag, Vlow⟩

/-- Three uninitialized bytes. -/
def uninit3 : Bytes := [none, none, none]

/-! ## Decidability of quantifiers over live variants -/

instance decForallLive (E : EnumSpec) (P : {i : Nat // E.Live i} → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) :=
  decidable_of_iff (∀ i, i < E.k → (h : E.Live i) → P ⟨i, h⟩)
    ⟨fun h i => h i.1 i.2.1 i.2, fun h i _ hl => h ⟨i, hl⟩⟩

/-! ## Wrapping arithmetic -/

theorem ex_wrapAdd : wrapAdd (255 : Fin 256) 3 = 2 ∧ wrapAdd (5 : Fin 256) 3 = 8 := by decide

theorem ex_wrapSub : wrapSub (1 : Fin 256) 3 = 254 ∧ wrapSub (5 : Fin 256) 3 = 2 := by decide

theorem ex_offset : offset (250 : Fin 256) 3 = 9 ∧ offset (3 : Fin 256) 250 = 247 ∧
    offset (7 : Fin 256) 7 = 0 := by decide

/-! ## Wrapping intervals -/

/-- `[255, 0]` mod 256 wraps: it contains `255` and `0`. -/
theorem ex_mem_pos : (⟨255, 0⟩ : WrapInterval 256).Mem 255 ∧
    (⟨255, 0⟩ : WrapInterval 256).Mem 0 ∧ (⟨2, 5⟩ : WrapInterval 8).Mem 3 := by decide

/-- `[255, 0]` mod 256 does not contain `1` or `254`; `[2, 5]` does not contain `6`. -/
theorem ex_mem_neg : ¬ (⟨255, 0⟩ : WrapInterval 256).Mem 1 ∧
    ¬ (⟨255, 0⟩ : WrapInterval 256).Mem 254 ∧ ¬ (⟨2, 5⟩ : WrapInterval 8).Mem 6 := by decide

theorem ex_size : (⟨255, 0⟩ : WrapInterval 256).size = 2 ∧
    (⟨0, 255⟩ : WrapInterval 256).size = 256 ∧ (⟨1, 0⟩ : WrapInterval 256).size = 256 ∧
    (⟨7, 7⟩ : WrapInterval 256).size = 1 := by decide

theorem ex_compl : (⟨255, 0⟩ : WrapInterval 256).compl = ⟨1, 254⟩ ∧
    (⟨0, 3⟩ : WrapInterval 4).compl = ⟨0, 3⟩ := by decide

/-! ## Range tests -/

theorem ex_toI8 : toI8 127 = 127 ∧ toI8 128 = -128 ∧ toI8 255 = -1 := by decide

theorem ex_tests : subTest (⟨255, 0⟩ : WrapInterval 256) 0 ∧
    ¬ unsignedTest (⟨255, 0⟩ : WrapInterval 256) 0 ∧
    signedTestI8 (⟨255, 0⟩ : WrapInterval 256) 0 ∧
    ¬ signedTestI8 (⟨127, 128⟩ : WrapInterval 256) 128 ∧
    originTest (128 : Fin 256) ⟨255, 0⟩ 0 := by decide

/-- The single-subtraction test is exact for `[255, 0]` mod 256. -/
theorem ex_exactFor_pos : ExactFor subTest (⟨255, 0⟩ : WrapInterval 256) := by decide +kernel

/-- The two-branch test at origin `0` accepts `255` and rejects `1` for `[255, 0]` mod 256. -/
theorem ex_twoBranchTest : twoBranchTest (0 : Fin 256) ⟨255, 0⟩ 255 ∧
    ¬ twoBranchTest (0 : Fin 256) ⟨255, 0⟩ 1 := by decide

/-- The unsigned test is not exact for `[255, 0]` mod 256. -/
theorem ex_exactFor_neg : ¬ ExactFor unsignedTest (⟨255, 0⟩ : WrapInterval 256) := by
  decide +kernel

/-! ## Covers, hulls, interval sets, niche counts -/

theorem ex_covers_pos : Covers (⟨0, 2⟩ : WrapInterval 4) V02 ∧
    Covers (⟨2, 0⟩ : WrapInterval 4) V02 := by decide

theorem ex_covers_neg : ¬ Covers (⟨0, 1⟩ : WrapInterval 4) V02 := by decide

/-- `{0, 2}` in `Fin 4` has two hulls of size 3, `[0, 2]` and `[2, 0]`; `{3, 0}` has the
wrapping hull `[3, 0]`. -/
theorem ex_isHull_pos : IsHull V02 ⟨0, 2⟩ ∧ IsHull V02 ⟨2, 0⟩ ∧
    IsHull (fun x : Fin 4 => x.val == 3 || x.val == 0) ⟨3, 0⟩ := by decide

/-- `[0, 3]` covers `{0, 2}` but is not smallest; `[0, 1]` does not cover it. -/
theorem ex_isHull_neg : ¬ IsHull V02 ⟨0, 3⟩ ∧ ¬ IsHull V02 ⟨0, 1⟩ := by decide

theorem ex_isWrapIntervalSet_pos : IsWrapIntervalSet (intervalV (⟨3, 1⟩ : WrapInterval 4)) ∧
    IsWrapIntervalSet V01 := by decide

theorem ex_isWrapIntervalSet_neg : ¬ IsWrapIntervalSet V02 := by decide

theorem ex_intervalV : intervalV (⟨3, 0⟩ : WrapInterval 4) 3 = true ∧
    intervalV (⟨3, 0⟩ : WrapInterval 4) 1 = false := by decide

theorem ex_nichesCount : nichesCount V02 = 2 ∧ nichesCount V01 = 2 ∧
    nichesCount (fun _ : Fin 4 => true) = 0 := by decide

/-! ## Affine encodings -/

theorem ex_affine : A0.tagOf 0 = 254 ∧ A0.tagOf 2 = 0 ∧ A0.tagInterval = ⟨254, 0⟩ ∧
    A0.last = 2 ∧ affineTags A0 ⟨2, by decide⟩ = 0 := by decide

/-- Degenerate edge: for `span = M = 256` the tag interval collapses to the singleton `[0, 0]`,
although the tags `tagOf r`, `r ≤ 256`, cover every value (here `tagOf 1 = 1`). -/
theorem ex_tagInterval_collapses : (⟨0, 256, 0⟩ : AffineNiche 256).tagInterval = ⟨0, 0⟩ ∧
    (⟨0, 256, 0⟩ : AffineNiche 256).tagOf 1 = 1 ∧
    ¬ (⟨0, 256, 0⟩ : AffineNiche 256).tagInterval.Mem 1 := by decide

/-- The decoder: tag `0` (wrapped) decodes to relative index 2; `1` is outside the tag
interval and decodes to the untagged variant (here `5`); `254` decodes to 0. -/
theorem ex_decodeIdx : decodeIdx 5 A0 0 = 2 ∧ decodeIdx 5 A0 1 = 5 ∧ decodeIdx 5 A0 254 = 0 :=
  by decide

theorem ex_tagsDisjoint_pos : TagsDisjoint Vmid 254 2 := by decide

theorem ex_tagsDisjoint_neg : ¬ TagsDisjoint Vmid 253 2 := by decide

/-- The affine layout with wrapping tags `254, 255, 0` over valid values `1..=253` is lawful. -/
theorem ex_affineLayout_pos : Lawful (affineLayout Vmid A0) :=
  ⟨by unfold DecEnc; decide +kernel, canonical_of_forall_pat _ (by decide +kernel)⟩

/-- With every value valid, the same encoding is not lawful. -/
theorem ex_affineLayout_neg : ¬ Lawful (affineLayout (allV 1) A0) := by
  intro h
  have h1 := h.1 (.inr ⟨254, rfl⟩)
  revert h1
  decide

theorem ex_live_pos : E1.Live 0 ∧ E1.Live 2 ∧ E2.Live 2 := by decide

/-- The untagged variant, an index `≥ k`, and an uninhabited variant are not live. -/
theorem ex_live_neg : ¬ E1.Live 1 ∧ ¬ E1.Live 3 ∧ ¬ E2.Live 1 := by decide

/-- Degenerate edge: with `u ≥ k` (here `k = 2`, `u = 5`) both variants `0` and `1` are live
dataless variants. -/
theorem ex_live_u_ge_k : (⟨2, 5, fun _ => true⟩ : EnumSpec).Live 0 ∧
    (⟨2, 5, fun _ => true⟩ : EnumSpec).Live 1 := by decide

theorem ex_liveInRange_pos : LiveInRange E1 Ag := by decide

theorem ex_liveInRange_neg : LiveInRange E1 (⟨1, 1, 253⟩ : AffineNiche 256) → False := by
  decide

/-- The general layout with the dead slot of `u` inside the range (tag `254`) is lawful. -/
theorem ex_genLayout_pos : Lawful (genLayout E1 Ag Vlow) :=
  ⟨by unfold DecEnc; decide +kernel, canonical_of_forall_pat _ (by decide +kernel)⟩

theorem ex_genLayout_neg : ¬ Lawful (genLayout E1 Ag (allV 1)) := by
  intro h
  have h1 := h.1 (.inr ⟨253, rfl⟩)
  revert h1
  decide

/-- All four classes occur (valid values `0..=249`, tags `253, 254, 255`, `254` dead). -/
theorem ex_classify : classify E1 Ag (fun x => decide (x.val < 250)) 0 = .valid ∧
    classify E1 Ag (fun x => decide (x.val < 250)) 253 = .liveTag ∧
    classify E1 Ag (fun x => decide (x.val < 250)) 254 = .deadTag ∧
    classify E1 Ag (fun x => decide (x.val < 250)) 251 = .unusedNiche := by decide

/-! ## Variant order -/

theorem ex_naturalSpan : naturalSpan 3 0 = 1 ∧ naturalSpan 3 2 = 1 ∧ naturalSpan 3 1 = 2 ∧
    naturalFirst 0 = 1 ∧ naturalLast 3 2 = 1 := by decide

/-- With `k = 3`, `u = 1`: variant 2 gets rotated index 0, variant 0 gets 1, `u` gets 2; the
rotated decoder maps tags `254, 255` back to variants `2, 0` and the valid value `5` to `u`. -/
theorem ex_rotated : rotIdx 3 1 2 = 0 ∧ rotIdx 3 1 0 = 1 ∧ rotIdx 3 1 1 = 2 ∧
    rotTag 3 1 (254 : Fin 256) 0 = 255 ∧ rotDecodeIdx 3 1 (254 : Fin 256) 254 = 2 ∧
    rotDecodeIdx 3 1 (254 : Fin 256) 255 = 0 ∧ rotDecodeIdx 3 1 (254 : Fin 256) 5 = 1 := by
  decide

/-- The rotated tags of `k = 3` variants at start `254` (`254`, `255`) are invalid for `Vlt254`;
for `k = 1` there is no rotated tag, so the condition holds even when every value is valid. -/
theorem ex_rotTagsInvalid_pos : RotTagsInvalid Vlt254 3 254 ∧
    RotTagsInvalid (fun _ : Fin 2 => true) 1 0 := by decide

/-- At start `253` the first rotated tag `253` is valid for `Vlt254`. -/
theorem ex_rotTagsInvalid_neg : ¬ RotTagsInvalid Vlt254 3 253 := by decide

/-! ## Nesting -/

/-- Adjacent reservation at the wrap point: extending `[250, 255]` upward gives `[250, 0]`;
the value below `[0, 5]` is `255`. -/
theorem ex_extend : extend (⟨250, 255⟩ : WrapInterval 256) .high = ⟨250, 0⟩ ∧
    adjNiche (⟨0, 5⟩ : WrapInterval 256) .low = 255 ∧
    nest (⟨1, 1⟩ : WrapInterval 8) [.low, .high] = ⟨0, 2⟩ := by decide

/-- Degenerate edge: extending the full interval `[0, 3]` of `Fin 4` upward wraps past its start
and collapses to the singleton `[0, 0]`. -/
theorem ex_extend_full : extend (⟨0, 3⟩ : WrapInterval 4) .high = ⟨0, 0⟩ ∧
    (extend (⟨0, 3⟩ : WrapInterval 4) .high).size = 1 := by decide

theorem ex_levelsReserveNiches_pos :
    LevelsReserveNiches (⟨1, 1⟩ : WrapInterval 4) [.low, .high, .high] := by decide

theorem ex_levelsReserveNiches_neg :
    ¬ LevelsReserveNiches (⟨1, 1⟩ : WrapInterval 4) [.low, .high, .high, .low] := by decide

/-! ## Bytes and the operational semantics -/

/-- The helper `writeBytes` keeps the place's length and drops bytes past its end; reads fail on
uninitialized bytes and past the end. -/
theorem ex_bytes : writeBytes uninit3 1 [7] = [none, some 7, none] ∧
    writeBytes [none] 0 [1, 2] = [some 1] ∧
    readBytes [none, some 7, none] 1 1 = some [7] ∧
    readBytes [none, some 7, none] 0 2 = none ∧ readBytes [some 7] 0 2 = none ∧
    leVal [1, 2] = 513 ∧ leBytes 2 513 = [1, 2] := by decide

/-- In the semantics, a write that does not fit in the place is undefined behaviour; an in-bounds
write is performed. -/
theorem ex_run_write_oob : run .operational Lop [.write 2 [7, 8]] (uninit3, []) = none ∧
    run .operational Lop [.write 1 [7]] (uninit3, []) = some ([none, some 7, none], []) := by
  decide

theorem ex_readNiche : Lop.readNiche [none, some 5, none] = some 5 ∧
    Lop.readNiche [some 5, none, none] = none := by decide

/-- `readDisc`: a valid value reads as `u`; a live tag as its variant; the dead slot of `u` is
undefined behaviour (uninitialized bytes: `ex_run`; unused niches: `ex_readDisc_unusedNiche`). -/
theorem ex_readDisc : Lop.readDisc [none, some 5, none] = some 1 ∧
    Lop.readDisc [none, some 253, none] = some 0 ∧
    Lop.readDisc [none, some 255, none] = some 2 ∧
    Lop.readDisc [none, some 254, none] = none ∧
    Lop.readDisc [none, some 252, none] = some 1 := by decide

/-- With valid values `0..=249`, the unused niche `251` (outside the tag interval) is undefined
behaviour for `readDisc`. -/
theorem ex_readDisc_unusedNiche :
    ({ Lop with V := fun x => decide (x.val < 250) } : OpLayout).readDisc [none, some 251, none] =
      none := by decide

theorem ex_encodable : Lop.Encodable 0 ∧ Lop.Encodable 2 ∧ ¬ Lop.Encodable 1 ∧
    ¬ Lop.Encodable 3 := by decide

theorem ex_disjointFromNiche : Lop.DisjointFromNiche 0 1 ∧ Lop.DisjointFromNiche 2 1 ∧
    ¬ Lop.DisjointFromNiche 0 2 ∧ ¬ Lop.DisjointFromNiche 1 1 := by decide

/-- `SetDiscriminant`: an encodable variant `v ≠ u` writes its tag; operational `SetDiscriminant u`
on uninitialized bytes is undefined behaviour, erased `SetDiscriminant u` is a no-op; an
unencodable variant is undefined behaviour in both. -/
theorem ex_setDisc : setDisc .operational Lop 2 uninit3 = some [none, some 255, none] ∧
    setDisc .operational Lop 1 uninit3 = none ∧ setDisc .erased Lop 1 uninit3 = some uninit3 ∧
    setDisc .operational Lop 1 [none, some 5, none] = some [none, some 5, none] ∧
    setDisc .erased Lop 3 uninit3 = none := by decide

/-- Writing a tag into a niche field that does not lie inside the place is undefined behaviour
(the niche byte of `Lop` is byte `1`; the place has one byte). -/
theorem ex_setDisc_oob : setDisc .operational Lop 0 [none] = none ∧
    setDisc .erased Lop 2 [none] = none := by decide

theorem ex_run : run .operational Lop [.write 0 [9], .setDisc 0, .readDisc] (uninit3, []) =
      some ([some 9, some 253, none], [0]) ∧
    run .operational Lop [.readDisc] (uninit3, []) = none := by decide

end Toy.WrapNiche
