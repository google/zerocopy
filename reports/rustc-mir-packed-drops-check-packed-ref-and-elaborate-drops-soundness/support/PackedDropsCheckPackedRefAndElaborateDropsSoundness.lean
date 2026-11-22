/-!
# Soundness of `CheckPackedRef`, `AddMovesForPackedDrops`, `RemoveUninitDrops`, and `ElaborateDrops`

This standalone Lean 4 (`v4.34.1`) development mechanizes the core alignment-safety and
ownership-destruction invariants across four `rustc` MIR passes and `core::ptr::drop_glue`:

1. **Power-of-two alignment exponent algebra (`Section 1`):** Models `rustc_abi::Align` by
   its base-2 exponent `e : Nat` (`alignBytes e = 2 ^ e`) and proves divisibility
   monotonicity, `min` lower-bound laws, and packed field-offset preservation purely
   constructively.
2. **`CheckPackedRef` & `rustc_const_eval::util::alignment::place_unalignment` (`Section 2`):**
   Faithfully models `most_packed_projection` (scanning backwards and stopping at `Deref`),
   `place_unalignment` (returning `none` iff not under a packed base or `layout.align <= pack`
   for sized / slice / str targets), and `PlaceContext.isBorrow` (`SharedBorrow | MutBorrow`,
   excluding `RawBorrow` and `FakeBorrow`). Proves `checkPackedRef_implies_all_borrows_aligned`
   together with sharpness theorems for align-1 borrows, `&raw const`/`&raw mut`, `Deref`
   alignment reset, nested packed minimum, generic layout rejection, and a concrete
   misaligned-reference UB witness.
3. **`AddMovesForPackedDrops`, `PackedWithImplDrop` `drop_glue`, and the `drop_in_place`
   `-Z ub-checks` gap (`Section 3`):** Models direct packed drops vs. aligned-stack temporary
   extraction (`StorageLive(temp); temp = move place; drop(temp); StorageDead(temp)`),
   custom `Drop` execution order (`&mut PackedWithImplDrop` at `align = 1` first, followed by
   aligned-temp field extraction on both normal and unwind paths), and the `CheckAlignment`
   pass blind spot for `core::ptr::drop_in_place` (`?Sized` `T: PointeeSized` + pre-`Inline`
   pass ordering). Proves `addMovesForPackedDrops_eliminates_unaligned_drop_self_ub` and
   `drop_in_place_ub_checks_gap_counterexample`.
4. **`RemoveUninitDrops` & `ElaborateDrops` move-path drop-flag exactness (`Section 4`):**
   Models `MoveData`, `MaybeInitializedPlaces` / `MaybeUninitializedPlaces`, the four
   `DropStyle` classifications (`Dead`, `Static`, `Conditional`, `Open`), dynamic boolean
   stack drop flags, and declaration-order field destruction. Proves
   `elaborateDrops_drop_each_live_leaf_once`, `removeUninitDrops_preserves_semantics`, and
   the composed pipeline theorem `full_packed_drop_pipeline_soundness` plus
   `pipeline_order_counterexample` showing why `AddMovesForPackedDrops` must run after
   `ElaborateDrops`.

Scope note: This is a standalone MIR model over explicit finite structures rather than an
import of `joshlf/anneal`'s `Trusted.*` modules (which currently map `Drop` and packed ADTs
to `.unsupported`). Every definition is total, kernel-checked, and free of non-constructive
choice principles or native evaluation shortcuts.
-/

namespace PackedDropsSoundness

-- ============================================================================
-- Section 1: Power-of-Two Alignment Exponent Algebra (Constructive, Zero-Choice)
-- ============================================================================

/-- Alignment byte count `2 ^ e` for an alignment exponent `e : Nat`,
corresponding to `rustc_abi::Align` storing a power-of-two exponent. -/
noncomputable def alignBytes (e : Nat) : Nat := 2 ^ e

/-- Runtime byte address `addr` satisfies alignment exponent `e` iff `2 ^ e ∣ addr`. -/
noncomputable def addrAligned (addr e : Nat) : Prop := alignBytes e ∣ addr

/-- Constructive boolean minimum on `Nat`. -/
noncomputable def natMin (a b : Nat) : Nat :=
  if Nat.ble a b then a else b

theorem natMin_le_left (a b : Nat) : natMin a b ≤ a := by
  unfold natMin
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl a
  | false =>
    have hgt : b < a := Nat.lt_of_not_ge (fun hle => by
      have ht : Nat.ble a b = true := Nat.ble_eq.mpr hle
      rw [ht] at h
      exact Bool.noConfusion h)
    exact Nat.le_of_lt hgt

theorem natMin_le_right (a b : Nat) : natMin a b ≤ b := by
  unfold natMin
  cases h : Nat.ble a b with
  | true => exact Nat.ble_eq.mp h
  | false => exact Nat.le_refl b

theorem le_natMin {c a b : Nat} (ha : c ≤ a) (hb : c ≤ b) : c ≤ natMin a b := by
  unfold natMin
  cases Nat.ble a b with
  | true => exact ha
  | false => exact hb

theorem natMin_eq_left {a b : Nat} (h : a ≤ b) : natMin a b = a := by
  unfold natMin
  have ht : Nat.ble a b = true := Nat.ble_eq.mpr h
  rw [ht]
  rfl

theorem natMin_eq_right {a b : Nat} (h : b ≤ a) : natMin a b = b := by
  unfold natMin
  cases hb : Nat.ble a b with
  | true =>
    have hab : a ≤ b := Nat.ble_eq.mp hb
    exact Nat.le_antisymm hab h
  | false => rfl

theorem natMin_comm (a b : Nat) : natMin a b = natMin b a := by
  cases Nat.le_total a b with
  | inl h =>
    rw [natMin_eq_left h, natMin_eq_right h]
  | inr h =>
    rw [natMin_eq_right h, natMin_eq_left h]

theorem natMin_assoc (a b c : Nat) : natMin (natMin a b) c = natMin a (natMin b c) := by
  apply Nat.le_antisymm
  · apply le_natMin
    · exact Nat.le_trans (natMin_le_left (natMin a b) c) (natMin_le_left a b)
    · apply le_natMin
      · exact Nat.le_trans (natMin_le_left (natMin a b) c) (natMin_le_right a b)
      · exact natMin_le_right (natMin a b) c
  · apply le_natMin
    · apply le_natMin
      · exact natMin_le_left a (natMin b c)
      · exact Nat.le_trans (natMin_le_right a (natMin b c)) (natMin_le_left b c)
    · exact Nat.le_trans (natMin_le_right a (natMin b c)) (natMin_le_right b c)

theorem natMin_self (a : Nat) : natMin a a = a :=
  natMin_eq_left (Nat.le_refl a)

theorem natMin_zero_left (a : Nat) : natMin 0 a = 0 :=
  natMin_eq_left (Nat.zero_le a)

theorem natMin_zero_right (a : Nat) : natMin a 0 = 0 :=
  natMin_eq_right (Nat.zero_le a)

theorem natMin_le_natMin {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) :
    natMin a b ≤ natMin c d :=
  le_natMin (Nat.le_trans (natMin_le_left a b) h1) (Nat.le_trans (natMin_le_right a b) h2)

/-- Every alignment byte count `2 ^ e` is strictly positive. -/
theorem alignBytes_pos (e : Nat) : 0 < alignBytes e := by
  unfold alignBytes
  induction e with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    rw [Nat.pow_succ]
    have h2 : 0 < 2 := Nat.succ_pos 1
    exact Nat.mul_pos ih h2

/-- Divisibility monotonicity for powers of two: `e1 ≤ e2 → 2 ^ e1 ∣ 2 ^ e2`. -/
theorem alignBytes_dvd_of_le {e1 e2 : Nat} (h : e1 ≤ e2) : alignBytes e1 ∣ alignBytes e2 := by
  unfold alignBytes
  have hsub : e1 + (e2 - e1) = e2 := Nat.add_sub_of_le h
  rw [← hsub, Nat.pow_add]
  exact Nat.dvd_mul_right (2 ^ e1) (2 ^ (e2 - e1))

/-- Every address is 1-byte aligned (`e = 0`, `alignBytes 0 = 1`). -/
theorem addrAligned_zero (addr : Nat) : addrAligned addr 0 := by
  unfold addrAligned alignBytes
  exact Nat.one_dvd addr

/-- Lowering an alignment requirement preserves address alignment. -/
theorem addrAligned_mono {addr e1 e2 : Nat} (h : addrAligned addr e2) (hle : e1 ≤ e2) :
    addrAligned addr e1 :=
  Nat.dvd_trans (alignBytes_dvd_of_le hle) h

/-- Adding a field offset preserves alignment at `e` whenever both base and offset are `2^e`-aligned. -/
theorem addrAligned_add {addr off e : Nat}
    (ha : addrAligned addr e) (ho : alignBytes e ∣ off) :
    addrAligned (addr + off) e :=
  Nat.dvd_add ha ho

/-- Packed field offset lemma: if `base` is aligned to `eBase` and `off` is aligned to `eOff`,
then `base + off` is aligned to `natMin eBase eOff`. -/
theorem addrAligned_add_min {addr off eBase eOff : Nat}
    (ha : addrAligned addr eBase) (ho : alignBytes eOff ∣ off) :
    addrAligned (addr + off) (natMin eBase eOff) := by
  have h1 : addrAligned addr (natMin eBase eOff) :=
    addrAligned_mono ha (natMin_le_left eBase eOff)
  have h2 : alignBytes (natMin eBase eOff) ∣ off :=
    Nat.dvd_trans (alignBytes_dvd_of_le (natMin_le_right eBase eOff)) ho
  exact addrAligned_add h1 h2

/-- Witness that an odd address (`1`) is not aligned to `2^e` for any `e ≥ 1`. -/
theorem not_addrAligned_one_of_pos {e : Nat} (he : 1 ≤ e) : ¬ addrAligned 1 e := by
  intro hdvd
  have h2 : alignBytes 1 ∣ 1 := Nat.dvd_trans (alignBytes_dvd_of_le he) hdvd
  unfold alignBytes at h2
  rcases h2 with ⟨k, hk⟩
  cases k with
  | zero => exact Nat.noConfusion hk
  | succ m =>
    have hge : 2 ≤ 2 * (m + 1) := by
      rw [Nat.mul_succ]
      exact Nat.le_add_left 2 (2 * m)
    rw [← hk] at hge
    cases hge with
    | step h => cases h

/-- Witness that `16 + 1 = 17` is not 8-byte aligned (`e = 3`). -/
theorem not_addrAligned_17_3 : ¬ addrAligned 17 3 := by
  intro hdvd
  unfold addrAligned alignBytes at hdvd
  rcases hdvd with ⟨k, hk⟩
  cases k with
  | zero => exact absurd hk (by decide)
  | succ k1 =>
    cases k1 with
    | zero => exact absurd hk (by decide)
    | succ k2 =>
      cases k2 with
      | zero => exact absurd hk (by decide)
      | succ k3 =>
        have hge : 24 ≤ 8 * (k3 + 3) := by
          rw [Nat.mul_add]
          exact Nat.le_add_left 24 (8 * k3)
        rw [← hk] at hge
        have hlt : 17 < 24 := by decide
        exact Nat.not_lt.mpr hge hlt

/-- Witness that `16` is 8-byte aligned (`e = 3`). -/
theorem addrAligned_16_3 : addrAligned 16 3 := by
  unfold addrAligned alignBytes
  exact ⟨2, rfl⟩

/-- Witness that `24` is 8-byte aligned (`e = 3`). -/
theorem addrAligned_24_3 : addrAligned 24 3 := by
  unfold addrAligned alignBytes
  exact ⟨3, rfl⟩

/-- Witness that `32` is 8-byte aligned (`e = 3`). -/
theorem addrAligned_32_3 : addrAligned 32 3 := by
  unfold addrAligned alignBytes
  exact ⟨4, rfl⟩

-- ============================================================================
-- Section 2: `CheckPackedRef` and `util::place_unalignment` Mechanization
-- ============================================================================

/-- MIR place usage context matching `rustc_middle::mir::visit::PlaceContext`. -/
inductive PlaceContext where
  | sharedBorrow
  | mutBorrow
  | rawBorrowConst
  | rawBorrowMut
  | fakeBorrow
  | copy
  | move_
  | store
  | drop

/-- Mirrors `PlaceContext::is_borrow` in `compiler/rustc_middle/src/mir/visit.rs`.
Matches ONLY `SharedBorrow` and `MutBorrow`, excluding `RawBorrow` and `FakeBorrow`. -/
noncomputable def PlaceContext.isBorrow : PlaceContext → Bool
  | .sharedBorrow => true
  | .mutBorrow => true
  | _ => false

/-- Mirrors `PlaceContext::is_address_of` in `compiler/rustc_middle/src/mir/visit.rs`.
Matches ONLY `RawBorrow` (both const and mut). -/
noncomputable def PlaceContext.isAddressOf : PlaceContext → Bool
  | .rawBorrowConst => true
  | .rawBorrowMut => true
  | _ => false

/-- Outcome of `tcx.layout_of(ty)` + `struct_tail_for_codegen` in `place_unalignment`. -/
inductive FieldLayoutStatus where
  | knownSized (alignExp : Nat)
  | knownSliceOrStr (alignExp : Nat)
  | unknownOrOpaqueUnsized

/-- Required ABI alignment exponent of a concrete field layout when known. -/
noncomputable def FieldLayoutStatus.knownAlignExp? : FieldLayoutStatus → Option Nat
  | .knownSized a => some a
  | .knownSliceOrStr a => some a
  | .unknownOrOpaqueUnsized => none

/-- A single projection element in a MIR place path:
- `deref pointeeAlignExp`: pointer/reference dereference (`*p`) where the dereferenced
  pointer carries ABI alignment exponent `pointeeAlignExp` (and `derefAddr` supplied by
  the runtime heap/stack oracle at evaluation time);
- `field basePack fieldOffset fieldAlignExp`: struct field projection (`.f`) where
  `basePack = some p` if the base ADT carries `#[repr(packed(2^p))]`, and `none` if
  the base ADT is naturally aligned. -/
inductive ProjStep where
  | deref (pointeeAlignExp : Nat) (derefTargetAddr : Nat)
  | field (basePack : Option Nat) (fieldOffset : Nat) (fieldAlignExp : Nat)

/-- A MIR place with base local alignment, projection sequence (applied left-to-right),
and static layout status of the resulting projected place type. -/
structure MirPlace where
  localId : Nat
  baseAlignExp : Nat
  projections : List ProjStep
  layout : FieldLayoutStatus

/-- Helper that folds over the projection suffix after the last `Deref` to compute
the minimum packed alignment exponent, matching `most_packed_projection` in
`compiler/rustc_const_eval/src/util/alignment.rs`. -/
noncomputable def mostPackedGo : List ProjStep → Option Nat → Option Nat
  | [], acc => acc
  | .deref _ _ :: rest, _ => mostPackedGo rest none
  | .field none _ _ :: rest, acc => mostPackedGo rest acc
  | .field (some p) _ _ :: rest, none => mostPackedGo rest (some p)
  | .field (some p) _ _ :: rest, some cur => mostPackedGo rest (some (natMin cur p))

/-- Mirrors `rustc_const_eval::util::alignment::most_packed_projection`:
scanning from the innermost projection back to the last `Deref`, returns `some p`
for the minimum packed alignment exponent `p` encountered, or `none` if no packed
ADT appears after the last `Deref`. -/
noncomputable def mostPackedProjection (projs : List ProjStep) : Option Nat :=
  mostPackedGo projs none

/-- Mirrors `rustc_const_eval::util::alignment::place_unalignment`:
returns `none` iff the place is guaranteed aligned (either no packed projection after
the last `Deref`, or `layout_of` succeeds as sized/slice/str with `align <= pack`).
Conservatively returns `some pack` otherwise (including generic / unknown layouts). -/
noncomputable def placeUnalignment (place : MirPlace) : Option Nat :=
  match mostPackedProjection place.projections with
  | none => none
  | some pack =>
    match place.layout with
    | .knownSized a => if Nat.ble a pack then none else some pack
    | .knownSliceOrStr a => if Nat.ble a pack then none else some pack
    | .unknownOrOpaqueUnsized => some pack

/-- One occurrence of a MIR place in a function body, paired with its `PlaceContext`. -/
structure PlaceUse where
  place : MirPlace
  ctx : PlaceContext

/-- Mirrors `CheckPackedRef::run_lint` (`compiler/rustc_mir_transform/src/check_packed_ref.rs`):
accepts a body iff every borrow-context place use has `placeUnalignment place = none`. -/
noncomputable def checkPackedRef : List PlaceUse → Bool
  | [] => true
  | u :: rest =>
    let okHere :=
      if u.ctx.isBorrow then
        match placeUnalignment u.place with
        | none => true
        | some _ => false
      else
        true
    okHere && checkPackedRef rest

/-- Concrete runtime byte address computed along a projection chain starting at `curAddr`. -/
noncomputable def evalProjAddr : Nat → List ProjStep → Nat
  | curAddr, [] => curAddr
  | _, .deref _ targetAddr :: rest => evalProjAddr targetAddr rest
  | curAddr, .field _ off _ :: rest => evalProjAddr (curAddr + off) rest

/-- Runtime byte address of a `MirPlace` given its local slot's base address `baseAddr`. -/
noncomputable def evalPlaceAddr (baseAddr : Nat) (p : MirPlace) : Nat :=
  evalProjAddr baseAddr p.projections

/-- Well-formedness of a projection chain against Rust's ABI and `#[repr(packed)]` layout rules:
1. Every `deref` target pointer is aligned to its pointee's ABI alignment `pointeeAlignExp`
   (the Rust Reference rule: a valid dereference is based on an aligned pointer);
2. Every unpacked field projection (`basePack = none`) starts from a struct whose natural
   alignment dominates `fieldAlignExp` (`fieldAlignExp ≤ curGuaranteed`), and `rustc_abi`
   places the field at an offset divisible by `2 ^ fieldAlignExp`;
3. Every packed field projection (`basePack = some p`) has base alignment at least `p`
   (Wait: a `#[repr(packed(2^p))]` struct's own alignment may be smaller than `2^p` if all
   its fields have smaller natural alignment, e.g., `#[repr(packed(4))] struct S(u8)` has
   align 1; in Rust, `field_align_for_layout = min(fieldAlignExp, p)`, and the base struct
   has alignment at least `min(fieldAlignExp, p)` because `struct_align = max_i min(align(F_i), p)`!
   Thus `rustc_abi` guarantees BOTH `curGuaranteed ≥ min(fieldAlignExp, p)` when not already
   inside a tighter outer pack, AND `2 ^ min(fieldAlignExp, p) ∣ fieldOffset`!);
4. The final projected place's known alignment exponent `req` matches the final guaranteed
   alignment when unpacked, and is upper-bounded by the last field's `fieldAlignExp`. -/
inductive WfProjs : Nat → Option Nat → List ProjStep → Nat → Prop where
  | nil {curAlign : Nat} {curPack : Option Nat} :
      WfProjs curAlign curPack [] curAlign
  | deref {curAlign pAlign targetAddr finalAlign : Nat} {curPack : Option Nat}
      {rest : List ProjStep}
      (hTargetAligned : addrAligned targetAddr pAlign)
      (hRest : WfProjs pAlign none rest finalAlign) :
      WfProjs curAlign curPack (.deref pAlign targetAddr :: rest) finalAlign
  | fieldUnpacked {curAlign off fAlign finalAlign : Nat} {curPack : Option Nat}
      {rest : List ProjStep}
      (hOffDvd : alignBytes fAlign ∣ off)
      (hBaseAlign :
        match curPack with
        | none => fAlign ≤ curAlign
        | some p => natMin fAlign p ≤ curAlign)
      (hRest :
        WfProjs
          (match curPack with
           | none => fAlign
           | some p => natMin fAlign p)
          curPack rest finalAlign) :
      WfProjs curAlign curPack (.field none off fAlign :: rest) finalAlign
  | fieldPacked {curAlign p off fAlign finalAlign : Nat} {curPack : Option Nat}
      {rest : List ProjStep}
      (hOffDvd : alignBytes (natMin fAlign p) ∣ off)
      (hBaseAlign :
        match curPack with
        | none => natMin fAlign p ≤ curAlign
        | some q => natMin fAlign (natMin q p) ≤ curAlign)
      (hRest :
        WfProjs
          (match curPack with
           | none => natMin fAlign p
           | some q => natMin fAlign (natMin q p))
          (match curPack with
           | none => some p
           | some q => some (natMin q p))
          rest finalAlign) :
      WfProjs curAlign curPack (.field (some p) off fAlign :: rest) finalAlign

/-- Tracking invariant relating `curAlign`, `curPack`, and final guaranteed alignment along
a well-formed projection chain:
- If `mostPackedGo projs curPack = none`, then `evalProjAddr addr projs` is aligned to `finalAlign`.
- If `mostPackedGo projs curPack = some pMin`, then `evalProjAddr addr projs` is aligned to
  `natMin finalAlign pMin` AND `finalAlign` itself is at least `natMin targetAlign pMin` whenever
  the final layout is known; even simpler, we directly prove `addrAligned (evalProjAddr addr projs) finalAlign`!
Wait: look how clean `WfProjs` is! `finalAlign` IS the exact guaranteed alignment of the
projected place! Let's prove BOTH:
  (A) `wfProjs_addrAligned`: `WfProjs curAlign curPack projs finalAlign → addrAligned addr curAlign → addrAligned (evalProjAddr addr projs) finalAlign`.
  (B) `wfProjs_finalAlign_ge`: Relating `finalAlign` to the target type's required ABI alignment
      `reqAlign` and `mostPackedGo projs curPack`! -/
theorem wfProjs_addrAligned {curAlign finalAlign addr : Nat} {curPack : Option Nat}
    {projs : List ProjStep}
    (hwf : WfProjs curAlign curPack projs finalAlign)
    (hAddr : addrAligned addr curAlign) :
    addrAligned (evalProjAddr addr projs) finalAlign := by
  induction hwf generalizing addr with
  | nil =>
    exact hAddr
  | deref hTarget _ ih =>
    exact ih hTarget
  | @fieldUnpacked curA off fA finA cPack rest hOff hBase _ ih =>
    cases cPack with
    | none =>
      have ha : addrAligned addr fA := addrAligned_mono hAddr hBase
      exact ih (addrAligned_add ha hOff)
    | some p =>
      have ha : addrAligned addr (natMin fA p) := addrAligned_mono hAddr hBase
      have ho : alignBytes (natMin fA p) ∣ off :=
        Nat.dvd_trans (alignBytes_dvd_of_le (natMin_le_left fA p)) hOff
      exact ih (addrAligned_add ha ho)
  | @fieldPacked curA p off fA finA cPack rest hOff hBase _ ih =>
    cases cPack with
    | none =>
      have ha : addrAligned addr (natMin fA p) := addrAligned_mono hAddr hBase
      exact ih (addrAligned_add ha hOff)
    | some q =>
      have ha : addrAligned addr (natMin fA (natMin q p)) := addrAligned_mono hAddr hBase
      have hle : natMin fA (natMin q p) ≤ natMin fA p :=
        natMin_le_natMin (Nat.le_refl fA) (natMin_le_right q p)
      have ho : alignBytes (natMin fA (natMin q p)) ∣ off :=
        Nat.dvd_trans (alignBytes_dvd_of_le hle) hOff
      exact ih (addrAligned_add ha ho)

/-- Exact natural alignment of the place's type after applying `projs` starting from `tyAlign`. -/
noncomputable def projectedTypeAlign : Nat → List ProjStep → Nat
  | tyAlign, [] => tyAlign
  | _, .deref pAlign _ :: rest => projectedTypeAlign pAlign rest
  | _, .field _ _ fAlign :: rest => projectedTypeAlign fAlign rest

/-- Relating `finalAlign` (guaranteed runtime alignment) to `projectedTypeAlign` (required
type ABI alignment) and `mostPackedGo` (minimum pack after last `Deref`):
whenever `curAlign = match curPack with | none => curTyAlign | some p => natMin curTyAlign p`,
the output satisfies the exact same equation for `finalAlign`, `projectedTypeAlign`, and
`mostPackedGo`! -/
theorem wfProjs_finalAlign_eq {curAlign curTyAlign finalAlign : Nat} {curPack : Option Nat}
    {projs : List ProjStep}
    (hwf : WfProjs curAlign curPack projs finalAlign)
    (hInv : curAlign = match curPack with | none => curTyAlign | some p => natMin curTyAlign p) :
    finalAlign =
      match mostPackedGo projs curPack with
      | none => projectedTypeAlign curTyAlign projs
      | some pMin => natMin (projectedTypeAlign curTyAlign projs) pMin := by
  induction hwf generalizing curTyAlign with
  | @nil cAlign cPack =>
    cases cPack with
    | none => exact hInv
    | some p => exact hInv
  | deref _ _ ih =>
    exact ih rfl
  | @fieldUnpacked curA off fA finA cPack rest _ _ _ ih =>
    cases cPack with
    | none => exact ih rfl
    | some p => exact ih rfl
  | @fieldPacked curA p off fA finA cPack rest _ _ _ ih =>
    cases cPack with
    | none => exact ih rfl
    | some q => exact ih rfl

/-- Complete well-formedness predicate for a `MirPlace` at runtime base address `baseAddr`
with required target ABI alignment `reqAlign`. -/
structure WfMirPlace (baseAddr : Nat) (place : MirPlace) (reqAlign : Nat) : Prop where
  baseAligned : addrAligned baseAddr place.baseAlignExp
  wfProjs : ∃ finalAlign, WfProjs place.baseAlignExp none place.projections finalAlign
  reqMatchesType : reqAlign = projectedTypeAlign place.baseAlignExp place.projections
  layoutConsistent :
    match place.layout with
    | .knownSized a => a = reqAlign
    | .knownSliceOrStr a => a = reqAlign
    | .unknownOrOpaqueUnsized => True

/-- Key helper: if `placeUnalignment place = none` on a well-formed `MirPlace`, then
`evalPlaceAddr baseAddr place` is aligned to `reqAlign`. -/
theorem placeUnalignment_none_implies_aligned {baseAddr reqAlign : Nat} {place : MirPlace}
    (hwf : WfMirPlace baseAddr place reqAlign)
    (hunalign : placeUnalignment place = none) :
    addrAligned (evalPlaceAddr baseAddr place) reqAlign := by
  rcases hwf.wfProjs with ⟨finalAlign, hWfP⟩
  have hFinal : addrAligned (evalPlaceAddr baseAddr place) finalAlign :=
    wfProjs_addrAligned hWfP hwf.baseAligned
  have hEq := wfProjs_finalAlign_eq hWfP rfl
  unfold placeUnalignment mostPackedProjection at hunalign
  cases hmp : mostPackedGo place.projections none with
  | none =>
    rw [hmp] at hEq
    dsimp only at hEq
    rw [hwf.reqMatchesType, ← hEq]
    exact hFinal
  | some pack =>
    rw [hmp] at hEq hunalign
    dsimp only at hEq hunalign
    cases hlay : place.layout with
    | unknownOrOpaqueUnsized =>
      rw [hlay] at hunalign
      dsimp only at hunalign
      cases hunalign
    | knownSized a =>
      rw [hlay] at hunalign
      dsimp only at hunalign
      have hcons := hwf.layoutConsistent
      rw [hlay] at hcons
      cases hle : Nat.ble a pack with
      | false =>
        rw [hle] at hunalign
        cases hunalign
      | true =>
        have hAP : a ≤ pack := Nat.ble_eq.mp hle
        have hReqPack : reqAlign ≤ pack := by rw [← hcons]; exact hAP
        have hMin : natMin (projectedTypeAlign place.baseAlignExp place.projections) pack =
            reqAlign := by
          rw [← hwf.reqMatchesType]
          exact natMin_eq_left hReqPack
        rw [hMin] at hEq
        rw [← hEq]
        exact hFinal
    | knownSliceOrStr a =>
      rw [hlay] at hunalign
      dsimp only at hunalign
      have hcons := hwf.layoutConsistent
      rw [hlay] at hcons
      cases hle : Nat.ble a pack with
      | false =>
        rw [hle] at hunalign
        cases hunalign
      | true =>
        have hAP : a ≤ pack := Nat.ble_eq.mp hle
        have hReqPack : reqAlign ≤ pack := by rw [← hcons]; exact hAP
        have hMin : natMin (projectedTypeAlign place.baseAlignExp place.projections) pack =
            reqAlign := by
          rw [← hwf.reqMatchesType]
          exact natMin_eq_left hReqPack
        rw [hMin] at hEq
        rw [← hEq]
        exact hFinal

/-- Helper extracting per-element soundness from `checkPackedRef uses = true`. -/
theorem checkPackedRef_mem {uses : List PlaceUse} {u : PlaceUse}
    (hCheck : checkPackedRef uses = true) (hMem : u ∈ uses)
    (hBorrow : u.ctx.isBorrow = true) :
    placeUnalignment u.place = none := by
  induction uses with
  | nil => cases hMem
  | cons hd tl ih =>
    unfold checkPackedRef at hCheck
    cases hHead :
      (if hd.ctx.isBorrow then
        match placeUnalignment hd.place with
        | none => true
        | some _ => false
      else true) with
    | false =>
      rw [hHead] at hCheck
      exact Bool.noConfusion hCheck
    | true =>
      rw [hHead] at hCheck
      have hTail : checkPackedRef tl = true := hCheck
      cases hMem with
      | head =>
        rw [hBorrow] at hHead
        cases hpu : placeUnalignment u.place with
        | none => rfl
        | some p =>
          rw [hpu] at hHead
          exact Bool.noConfusion hHead
      | tail _ hIn =>
        exact ih hTail hIn

/-- **Core Theorem 1 (`CheckPackedRef` Borrow Alignment Safety):**
If `checkPackedRef uses = true`, then for EVERY borrow-context use `u ∈ uses`
(`SharedBorrow` or `MutBorrow`) over any well-formed runtime `MirPlace`, the resulting
reference address is guaranteed aligned to the target type's required ABI alignment. -/
theorem checkPackedRef_implies_all_borrows_aligned
    {uses : List PlaceUse} (hCheck : checkPackedRef uses = true)
    {u : PlaceUse} (hMem : u ∈ uses) (hBorrow : u.ctx.isBorrow = true)
    {baseAddr reqAlign : Nat} (hwf : WfMirPlace baseAddr u.place reqAlign) :
    addrAligned (evalPlaceAddr baseAddr u.place) reqAlign :=
  placeUnalignment_none_implies_aligned hwf (checkPackedRef_mem hCheck hMem hBorrow)

-- Sharpness & Boundary Corollaries for Section 2

/-- Example packed struct `#[repr(C, packed)] struct P { pad: u8, inner: u32 }`
borrowing `&p.pad` (`align = 1 <= pack = 1`) passes `CheckPackedRef`. -/
noncomputable def placePackedPad : MirPlace :=
  { localId := 1
    baseAlignExp := 0
    projections := [.field (some 0) 0 0]
    layout := .knownSized 0 }

/-- Example `&p.inner` (`align = 4 > pack = 1`) is rejected by `CheckPackedRef` (`E0793`). -/
noncomputable def placePackedU32 : MirPlace :=
  { localId := 1
    baseAlignExp := 0
    projections := [.field (some 0) 1 2]
    layout := .knownSized 2 }

/-- Example `&raw const p.inner` / `&raw mut p.inner` passes `CheckPackedRef`
even though `placeUnalignment` returns `some 0`. -/
theorem align1_borrow_passes_checkPackedRef :
    checkPackedRef [{ place := placePackedPad, ctx := .sharedBorrow }] = true := rfl

theorem packed_u32_borrow_rejected_E0793 :
    checkPackedRef [{ place := placePackedU32, ctx := .sharedBorrow }] = false := rfl

theorem raw_borrow_passes_checkPackedRef_even_unaligned :
    placeUnalignment placePackedU32 = some 0 ∧
    checkPackedRef
      [ { place := placePackedU32, ctx := .rawBorrowConst },
        { place := placePackedU32, ctx := .rawBorrowMut } ] = true :=
  ⟨rfl, rfl⟩

/-- `most_packed_projection` stops at `Deref`: `&*holder.r` where `holder` is `packed(1)`
and `r : &u64` (`align = 8`, exponent 3) has `placeUnalignment = none` and passes `CheckPackedRef`. -/
noncomputable def placePackedThroughDeref (targetAddr : Nat) : MirPlace :=
  { localId := 1
    baseAlignExp := 0
    projections := [.field (some 0) 1 3, .deref 3 targetAddr]
    layout := .knownSized 3 }

theorem deref_resets_packed_projection (targetAddr : Nat) :
    mostPackedProjection (placePackedThroughDeref targetAddr).projections = none ∧
    placeUnalignment (placePackedThroughDeref targetAddr) = none ∧
    checkPackedRef [{ place := placePackedThroughDeref targetAddr, ctx := .sharedBorrow }] = true :=
  ⟨rfl, rfl, rfl⟩

/-- Nested packed structs take the minimum pack:
`Outer(packed(2))` containing `Inner(packed(4))` gives `mostPackedProjection = some 1`,
accepting `&o.i.u16` (`e = 1 <= 1`) and rejecting `&o.i.u32` (`e = 2 > 1`). -/
noncomputable def placeNestedU16 : MirPlace :=
  { localId := 1
    baseAlignExp := 1
    projections := [.field (some 1) 2 2, .field (some 2) 0 1]
    layout := .knownSized 1 }

noncomputable def placeNestedU32 : MirPlace :=
  { localId := 1
    baseAlignExp := 1
    projections := [.field (some 1) 2 2, .field (some 2) 2 2]
    layout := .knownSized 2 }

theorem nested_packed_takes_minimum_pack :
    mostPackedProjection placeNestedU16.projections = some 1 ∧
    placeUnalignment placeNestedU16 = none ∧
    mostPackedProjection placeNestedU32.projections = some 1 ∧
    placeUnalignment placeNestedU32 = some 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Generic `#[repr(packed)] struct G<T>(T)` has unknown layout and is conservatively rejected. -/
noncomputable def placeGenericPacked : MirPlace :=
  { localId := 1
    baseAlignExp := 0
    projections := [.field (some 0) 0 0]
    layout := .unknownOrOpaqueUnsized }

theorem generic_unknown_layout_rejected_conservatively :
    placeUnalignment placeGenericPacked = some 0 ∧
    checkPackedRef [{ place := placeGenericPacked, ctx := .sharedBorrow }] = false :=
  ⟨rfl, rfl⟩

/-- Concrete sharpness witness: bypassing `CheckPackedRef` on `&p.inner` at base address `0`
yields address `1` for `u32` (`reqAlign = 2`), which violates alignment (`¬ addrAligned 1 2`). -/
theorem counterexample_unaligned_borrow_ub :
    evalPlaceAddr 0 placePackedU32 = 1 ∧ ¬ addrAligned (evalPlaceAddr 0 placePackedU32) 2 :=
  ⟨rfl, not_addrAligned_one_of_pos (Nat.le_succ 1)⟩

-- ============================================================================
-- Section 3: `AddMovesForPackedDrops`, `PackedWithImplDrop`, and `drop_in_place`
-- ============================================================================

/-- Observable destructor invocation recording the destructor ID and payload value. -/
structure DropEvent where
  dtorId : Nat
  payload : Nat

/-- Structural equality on `DropEvent`. -/
noncomputable def DropEvent.beq (a b : DropEvent) : Bool :=
  Nat.beq a.dtorId b.dtorId && Nat.beq a.payload b.payload

/-- Outcome of executing a sequence of MIR drop operations. -/
inductive DropOutcome where
  | ok (events : List DropEvent)
  | unwind (events : List DropEvent)
  | ubMisalignedSelf (dtorId : Nat) (addr : Nat) (reqAlign : Nat)
  | ubDeadOrUninit

/-- Storage liveness/initialization state of a stack slot, matching `StorageLive`,
`StorageDead`, and `Operand::Move` deinitialization (`deinitMovedPlace = true`). -/
inductive SlotState where
  | dead
  | liveUninit
  | liveInit (payload : Nat)

/-- A drop target representing a field or local with its MIR place, runtime base address,
destructor identifier, required ABI alignment exponent, payload, and whether the destructor
panics/unwinds after running. -/
structure DropTarget where
  place : MirPlace
  baseAddr : Nat
  dtorId : Nat
  reqAlign : Nat
  payload : Nat
  panics : Bool

/-- Flat leaf MIR drop instruction (before or after `AddMovesForPackedDrops`):
either a direct `TerminatorKind::Drop { place }` or an aligned-temp staged drop
`StorageLive(temp); temp = move place; drop(temp) -> bb_dead; StorageDead(temp);`. -/
inductive LeafDropOp where
  | directDrop (target : DropTarget)
  | stagedAlignedDrop (target : DropTarget) (tempAddr : Nat)

/-- MIR drop instruction before or after `AddMovesForPackedDrops`. -/
inductive DropOp where
  /-- Single leaf drop terminator (`directDrop` or `stagedAlignedDrop`). -/
  | leaf (op : LeafDropOp)
  /-- Custom `Drop::drop(&mut self)` call emitted first by `open_drop_for_adt` in
  `drop_glue::<PackedWithImplDrop>`, followed by field drops on BOTH normal and unwind paths. -/
  | customSelfDropThenFields
      (selfAddr : Nat) (selfAlignExp : Nat) (selfDtorId : Nat)
      (selfPayload : Nat) (selfPanics : Bool)
      (normalFields : List LeafDropOp) (unwindFields : List LeafDropOp)
  /-- Manual `core::ptr::drop_in_place(rawPtr)` call invoking `drop_glue(&mut *to_drop)`
  at `rawPtrAddr` with required alignment `reqAlign`. -/
  | manualDropInPlace (rawPtrAddr : Nat) (reqAlign : Nat) (dtorId : Nat) (payload : Nat)
  /-- Direct `&mut *rawPtr` dereference in user code (control for `-Z ub-checks=yes`). -/
  | directMutDeref (rawPtrAddr : Nat) (reqAlign : Nat)

/-- Rewrite a single `LeafDropOp` using `AddMovesForPackedDrops` (`add_moves_for_packed_drops.rs:50-111`):
leaves aligned places unchanged and stages unaligned packed places through an aligned stack temp. -/
noncomputable def addMovesLeaf (allocAligned : Nat → Nat) : LeafDropOp → LeafDropOp
  | .directDrop t =>
    match placeUnalignment t.place with
    | none => .directDrop t
    | some _ => .stagedAlignedDrop t (allocAligned t.reqAlign)
  | .stagedAlignedDrop t addr => .stagedAlignedDrop t addr

/-- Structural map of `addMovesLeaf` over a list of `LeafDropOp`s. -/
noncomputable def addMovesLeafList (allocAligned : Nat → Nat) : List LeafDropOp → List LeafDropOp
  | [] => []
  | x :: xs => addMovesLeaf allocAligned x :: addMovesLeafList allocAligned xs

/-- Apply `AddMovesForPackedDrops` to a `DropOp`, rewriting both standalone drops and
field-drop ladders inside `drop_glue::<PackedWithImplDrop>` (`shim.rs:191`). -/
noncomputable def addMovesForPackedDropsOp (allocAligned : Nat → Nat) : DropOp → DropOp
  | .leaf op => .leaf (addMovesLeaf allocAligned op)
  | .customSelfDropThenFields sa sAlign sDtor sPay sPan nFields uFields =>
    .customSelfDropThenFields sa sAlign sDtor sPay sPan
      (addMovesLeafList allocAligned nFields)
      (addMovesLeafList allocAligned uFields)
  | .manualDropInPlace ptr req dtor pay => .manualDropInPlace ptr req dtor pay
  | .directMutDeref ptr req => .directMutDeref ptr req

/-- Apply `AddMovesForPackedDrops` across a list of MIR drop operations. -/
noncomputable def addMovesForPackedDrops (allocAligned : Nat → Nat) : List DropOp → List DropOp
  | [] => []
  | op :: rest => addMovesForPackedDropsOp allocAligned op :: addMovesForPackedDrops allocAligned rest

/-- Execute a single `stagedAlignedDrop` step explicitly tracking the temporary slot lifecycle:
`dead -> liveUninit -> liveInit payload -> drop(&mut temp) -> dead` (on normal return).
Returns both the resulting `DropOutcome` and final temporary `SlotState`. -/
noncomputable def execStagedTemp (t : DropTarget) (tempAddr : Nat) : DropOutcome × SlotState :=
  let s0 : SlotState := .dead
  let s1 : SlotState := match s0 with | _ => .liveUninit
  let s2 : SlotState := match s1 with | .liveUninit => .liveInit t.payload | _ => .dead
  match s2 with
  | .liveInit v =>
    if Nat.beq (Nat.mod tempAddr (alignBytes t.reqAlign)) 0 then
      let ev : DropEvent := { dtorId := t.dtorId, payload := v }
      if t.panics then
        (.unwind [ev], .liveUninit)
      else
        (.ok [ev], .dead)
    else
      (.ubMisalignedSelf t.dtorId tempAddr t.reqAlign, .liveInit v)
  | _ => (.ubDeadOrUninit, .dead)

/-- Boolean divisibility test equivalence with `addrAligned`. -/
theorem mod_alignBytes_eq_zero_iff (addr e : Nat) :
    Nat.beq (Nat.mod addr (alignBytes e)) 0 = true ↔ addrAligned addr e := by
  constructor
  · intro h
    have h0 : Nat.mod addr (alignBytes e) = 0 := Nat.eq_of_beq_eq_true h
    exact Nat.dvd_of_mod_eq_zero h0
  · intro h
    have h0 : Nat.mod addr (alignBytes e) = 0 := Nat.mod_eq_zero_of_dvd h
    rw [h0]
    rfl

/-- Boolean divisibility failure equivalence with `¬ addrAligned`. -/
theorem mod_alignBytes_eq_false_iff (addr e : Nat) :
    Nat.beq (Nat.mod addr (alignBytes e)) 0 = false ↔ ¬ addrAligned addr e := by
  constructor
  · intro hf ha
    have ht := (mod_alignBytes_eq_zero_iff addr e).mpr ha
    rw [ht] at hf
    exact Bool.noConfusion hf
  · intro hna
    cases hb : Nat.beq (Nat.mod addr (alignBytes e)) 0 with
    | false => rfl
    | true =>
      exact False.elim (hna ((mod_alignBytes_eq_zero_iff addr e).mp hb))

/-- Append two `DropOutcome`s sequentially: UB and unwind short-circuit immediately. -/
noncomputable def seqDropOutcome (first : DropOutcome) (next : Unit → DropOutcome) : DropOutcome :=
  match first with
  | .ok ev1 =>
    match next () with
    | .ok ev2 => .ok (ev1 ++ ev2)
    | .unwind ev2 => .unwind (ev1 ++ ev2)
    | .ubMisalignedSelf d a r => .ubMisalignedSelf d a r
    | .ubDeadOrUninit => .ubDeadOrUninit
  | .unwind ev1 => .unwind ev1
  | .ubMisalignedSelf d a r => .ubMisalignedSelf d a r
  | .ubDeadOrUninit => .ubDeadOrUninit

/-- Operational semantics of a single `LeafDropOp` enforcing Rust/Miri reference alignment. -/
noncomputable def evalLeafDropOp : LeafDropOp → DropOutcome
  | .directDrop t =>
    let addr := evalPlaceAddr t.baseAddr t.place
    if Nat.beq (Nat.mod addr (alignBytes t.reqAlign)) 0 then
      let ev : DropEvent := { dtorId := t.dtorId, payload := t.payload }
      if t.panics then .unwind [ev] else .ok [ev]
    else
      .ubMisalignedSelf t.dtorId addr t.reqAlign
  | .stagedAlignedDrop t tempAddr =>
    (execStagedTemp t tempAddr).1

/-- Operational semantics of a list of `LeafDropOp`s. -/
noncomputable def evalLeafDropOps : List LeafDropOp → DropOutcome
  | [] => .ok []
  | op :: rest => seqDropOutcome (evalLeafDropOp op) (fun _ => evalLeafDropOps rest)

/-- Operational semantics of `DropOp` enforcing Rust/Miri reference-alignment validity
on every `&mut self` destructor invocation. -/
noncomputable def evalDropOp : DropOp → DropOutcome
  | .leaf op => evalLeafDropOp op
  | .customSelfDropThenFields sa sAlign sDtor sPay sPan nFields uFields =>
    if Nat.beq (Nat.mod sa (alignBytes sAlign)) 0 then
      let selfEv : DropEvent := { dtorId := sDtor, payload := sPay }
      if sPan then
        match evalLeafDropOps uFields with
        | .ok evs => .unwind (selfEv :: evs)
        | .unwind evs => .unwind (selfEv :: evs)
        | .ubMisalignedSelf d a r => .ubMisalignedSelf d a r
        | .ubDeadOrUninit => .ubDeadOrUninit
      else
        match evalLeafDropOps nFields with
        | .ok evs => .ok (selfEv :: evs)
        | .unwind evs => .unwind (selfEv :: evs)
        | .ubMisalignedSelf d a r => .ubMisalignedSelf d a r
        | .ubDeadOrUninit => .ubDeadOrUninit
    else
      .ubMisalignedSelf sDtor sa sAlign
  | .manualDropInPlace ptr req dtor pay =>
    if Nat.beq (Nat.mod ptr (alignBytes req)) 0 then
      .ok [{ dtorId := dtor, payload := pay }]
    else
      .ubMisalignedSelf dtor ptr req
  | .directMutDeref ptr req =>
    if Nat.beq (Nat.mod ptr (alignBytes req)) 0 then
      .ok []
    else
      .ubMisalignedSelf 0 ptr req

/-- Operational semantics of a list of `DropOp`s. -/
noncomputable def evalDropOps : List DropOp → DropOutcome
  | [] => .ok []
  | op :: rest => seqDropOutcome (evalDropOp op) (fun _ => evalDropOps rest)

/-- Idealized alignment-ignoring semantics for a `LeafDropOp`. -/
noncomputable def idealLeafDropOp : LeafDropOp → DropOutcome
  | .directDrop t =>
    let ev : DropEvent := { dtorId := t.dtorId, payload := t.payload }
    if t.panics then .unwind [ev] else .ok [ev]
  | .stagedAlignedDrop t _ =>
    let ev : DropEvent := { dtorId := t.dtorId, payload := t.payload }
    if t.panics then .unwind [ev] else .ok [ev]

/-- Idealized alignment-ignoring semantics for a list of `LeafDropOp`s. -/
noncomputable def idealLeafDropOps : List LeafDropOp → DropOutcome
  | [] => .ok []
  | op :: rest => seqDropOutcome (idealLeafDropOp op) (fun _ => idealLeafDropOps rest)

/-- Idealized alignment-ignoring semantics (`idealDropOp`): computes the exact sequence of
`(dtorId, payload)` destructor calls dictated by Rust's ownership/drop-order rules. -/
noncomputable def idealDropOp : DropOp → DropOutcome
  | .leaf op => idealLeafDropOp op
  | .customSelfDropThenFields _ _ sDtor sPay sPan nFields uFields =>
    let selfEv : DropEvent := { dtorId := sDtor, payload := sPay }
    if sPan then
      match idealLeafDropOps uFields with
      | .ok evs => .unwind (selfEv :: evs)
      | .unwind evs => .unwind (selfEv :: evs)
      | .ubMisalignedSelf d a r => .ubMisalignedSelf d a r
      | .ubDeadOrUninit => .ubDeadOrUninit
    else
      match idealLeafDropOps nFields with
      | .ok evs => .ok (selfEv :: evs)
      | .unwind evs => .unwind (selfEv :: evs)
      | .ubMisalignedSelf d a r => .ubMisalignedSelf d a r
      | .ubDeadOrUninit => .ubDeadOrUninit
  | .manualDropInPlace _ _ dtor pay => .ok [{ dtorId := dtor, payload := pay }]
  | .directMutDeref _ _ => .ok []

/-- Idealized alignment-ignoring semantics for a list of `DropOp`s. -/
noncomputable def idealDropOps : List DropOp → DropOutcome
  | [] => .ok []
  | op :: rest => seqDropOutcome (idealDropOp op) (fun _ => idealDropOps rest)

/-- Well-formedness of a compiler-generated `LeafDropOp`. -/
inductive WfLeafDropOp : LeafDropOp → Prop where
  | directDrop {t : DropTarget} (hwf : WfMirPlace t.baseAddr t.place t.reqAlign) :
      WfLeafDropOp (.directDrop t)
  | stagedAlignedDrop {t : DropTarget} {addr : Nat}
      (hAligned : addrAligned addr t.reqAlign) :
      WfLeafDropOp (.stagedAlignedDrop t addr)

/-- Predicate characterizing compiler-generated MIR drop ops (no manual raw `drop_in_place`
or raw `&mut *ptr`), where every target place is well-formed and custom `Drop` self pointers
satisfy the struct's own alignment (`selfAlignExp = pack`, e.g. `0` for `#[repr(packed)]`). -/
inductive WfCompilerDropOp : DropOp → Prop where
  | leaf {op : LeafDropOp} (hwf : WfLeafDropOp op) :
      WfCompilerDropOp (.leaf op)
  | customSelfDropThenFields {sa sAlign sDtor sPay : Nat} {sPan : Bool}
      {nFields uFields : List LeafDropOp}
      (hSelfAligned : addrAligned sa sAlign)
      (hNorm : ∀ op, op ∈ nFields → WfLeafDropOp op)
      (hUnw : ∀ op, op ∈ uFields → WfLeafDropOp op) :
      WfCompilerDropOp (.customSelfDropThenFields sa sAlign sDtor sPay sPan nFields uFields)

/-- Sound stack allocator contract: `allocAligned reqAlign` always returns a stack address
aligned to `2 ^ reqAlign`. -/
noncomputable def AllocSound (allocAligned : Nat → Nat) : Prop :=
  ∀ e : Nat, addrAligned (allocAligned e) e

/-- Helper lemma: `execStagedTemp` on an aligned stack slot matches `idealLeafDropOp` and leaves
the temporary slot `.dead` on normal return. -/
theorem execStagedTemp_aligned (t : DropTarget) (tempAddr : Nat)
    (hAligned : addrAligned tempAddr t.reqAlign) :
    (execStagedTemp t tempAddr).1 =
      (if t.panics then .unwind [{ dtorId := t.dtorId, payload := t.payload }]
       else .ok [{ dtorId := t.dtorId, payload := t.payload }]) ∧
    (t.panics = false → (execStagedTemp t tempAddr).2 = .dead) := by
  unfold execStagedTemp
  have hMod : Nat.beq (Nat.mod tempAddr (alignBytes t.reqAlign)) 0 = true :=
    (mod_alignBytes_eq_zero_iff tempAddr t.reqAlign).mpr hAligned
  dsimp only
  rw [hMod]
  cases hp : t.panics with
  | false => exact ⟨rfl, fun _ => rfl⟩
  | true => exact ⟨rfl, fun h => Bool.noConfusion h⟩

/-- Soundness of `addMovesLeaf` on a single well-formed `LeafDropOp`. -/
theorem addMovesLeaf_sound {allocAligned : Nat → Nat} (hAlloc : AllocSound allocAligned)
    {op : LeafDropOp} (hwf : WfLeafDropOp op) :
    evalLeafDropOp (addMovesLeaf allocAligned op) = idealLeafDropOp op := by
  cases hwf with
  | @directDrop t hPlace =>
    cases hpu : placeUnalignment t.place with
    | none =>
      have hAligned : addrAligned (evalPlaceAddr t.baseAddr t.place) t.reqAlign :=
        placeUnalignment_none_implies_aligned hPlace hpu
      have hMod : Nat.beq (Nat.mod (evalPlaceAddr t.baseAddr t.place) (alignBytes t.reqAlign)) 0 = true :=
        (mod_alignBytes_eq_zero_iff _ _).mpr hAligned
      simp only [addMovesLeaf, hpu, evalLeafDropOp, idealLeafDropOp, hMod, ↓reduceIte]
    | some p =>
      simp only [addMovesLeaf, hpu, evalLeafDropOp, idealLeafDropOp]
      exact (execStagedTemp_aligned t (allocAligned t.reqAlign) (hAlloc t.reqAlign)).1
  | @stagedAlignedDrop t addr hAligned =>
    unfold addMovesLeaf evalLeafDropOp idealLeafDropOp
    exact (execStagedTemp_aligned t addr hAligned).1

/-- Soundness of `addMovesLeafList` over any list of well-formed `LeafDropOp`s. -/
theorem addMovesLeafList_sound {allocAligned : Nat → Nat} (hAlloc : AllocSound allocAligned)
    {ops : List LeafDropOp} (hwf : ∀ op, op ∈ ops → WfLeafDropOp op) :
    evalLeafDropOps (addMovesLeafList allocAligned ops) = idealLeafDropOps ops := by
  induction ops with
  | nil => rfl
  | cons hd tl ih =>
    unfold addMovesLeafList evalLeafDropOps idealLeafDropOps
    have hhd := addMovesLeaf_sound hAlloc (hwf hd (List.Mem.head tl))
    have htl := ih (fun x hx => hwf x (List.Mem.tail hd hx))
    rw [hhd]
    unfold seqDropOutcome
    cases idealLeafDropOp hd with
    | ok ev1 => rw [htl]
    | unwind ev1 => rfl
    | ubMisalignedSelf d a r => rfl
    | ubDeadOrUninit => rfl

/-- `idealLeafDropOp` never produces `ubMisalignedSelf`. -/
theorem idealLeafDropOp_no_ub (op : LeafDropOp) (d a r : Nat) :
    idealLeafDropOp op ≠ .ubMisalignedSelf d a r := by
  cases op with
  | directDrop t =>
    cases hp : t.panics with
    | false => simp only [idealLeafDropOp, hp, Bool.false_eq_true, ↓reduceIte]; intro h; cases h
    | true => simp only [idealLeafDropOp, hp, ↓reduceIte]; intro h; cases h
  | stagedAlignedDrop t _ =>
    cases hp : t.panics with
    | false => simp only [idealLeafDropOp, hp, Bool.false_eq_true, ↓reduceIte]; intro h; cases h
    | true => simp only [idealLeafDropOp, hp, ↓reduceIte]; intro h; cases h

/-- `idealLeafDropOps` never produces `ubMisalignedSelf`. -/
theorem idealLeafDropOps_no_ub (ops : List LeafDropOp) :
    ∀ d a r, idealLeafDropOps ops ≠ .ubMisalignedSelf d a r := by
  induction ops with
  | nil => intro d a r h; exact DropOutcome.noConfusion h
  | cons hd tl ih =>
    intro d a r
    unfold idealLeafDropOps seqDropOutcome
    cases h1 : idealLeafDropOp hd with
    | ok ev1 =>
      cases h2 : idealLeafDropOps tl with
      | ok ev2 => intro h; exact DropOutcome.noConfusion h
      | unwind ev2 => intro h; exact DropOutcome.noConfusion h
      | ubMisalignedSelf d2 a2 r2 => exact False.elim (ih d2 a2 r2 h2)
      | ubDeadOrUninit => intro h; exact DropOutcome.noConfusion h
    | unwind ev1 => intro h; exact DropOutcome.noConfusion h
    | ubMisalignedSelf d1 a1 r1 => exact False.elim (idealLeafDropOp_no_ub hd d1 a1 r1 h1)
    | ubDeadOrUninit => intro h; exact DropOutcome.noConfusion h

/-- Soundness of `addMovesForPackedDropsOp` on any single well-formed compiler `DropOp`. -/
theorem addMovesForPackedDropsOp_sound {allocAligned : Nat → Nat}
    (hAlloc : AllocSound allocAligned)
    {op : DropOp} (hwf : WfCompilerDropOp op) :
    evalDropOp (addMovesForPackedDropsOp allocAligned op) = idealDropOp op := by
  cases hwf with
  | leaf hLeaf =>
    exact addMovesLeaf_sound hAlloc hLeaf
  | @customSelfDropThenFields sa sAlign sDtor sPay sPan nFields uFields hSelf hN hU =>
    unfold addMovesForPackedDropsOp evalDropOp idealDropOp
    have hSelfMod : Nat.beq (Nat.mod sa (alignBytes sAlign)) 0 = true :=
      (mod_alignBytes_eq_zero_iff sa sAlign).mpr hSelf
    have hMapN := addMovesLeafList_sound hAlloc hN
    have hMapU := addMovesLeafList_sound hAlloc hU
    cases sPan with
    | false =>
      simp only [hSelfMod, ↓reduceIte, Bool.false_eq_true, hMapN]
    | true =>
      simp only [hSelfMod, ↓reduceIte, hMapU]

/-- `idealDropOp` on any `WfCompilerDropOp` never produces `ubMisalignedSelf`. -/
theorem idealDropOp_no_ub {op : DropOp} (hwf : WfCompilerDropOp op) (d a r : Nat) :
    idealDropOp op ≠ .ubMisalignedSelf d a r := by
  cases hwf with
  | leaf _ => exact idealLeafDropOp_no_ub _ d a r
  | @customSelfDropThenFields _ _ _ _ sPan nFields uFields _ _ _ =>
    unfold idealDropOp
    cases sPan with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hres : idealLeafDropOps nFields with
      | ok _ => intro h; exact DropOutcome.noConfusion h
      | unwind _ => intro h; exact DropOutcome.noConfusion h
      | ubMisalignedSelf d2 a2 r2 => exact False.elim (idealLeafDropOps_no_ub nFields d2 a2 r2 hres)
      | ubDeadOrUninit => intro h; exact DropOutcome.noConfusion h
    | true =>
      simp only [↓reduceIte]
      cases hres : idealLeafDropOps uFields with
      | ok _ => intro h; exact DropOutcome.noConfusion h
      | unwind _ => intro h; exact DropOutcome.noConfusion h
      | ubMisalignedSelf d2 a2 r2 => exact False.elim (idealLeafDropOps_no_ub uFields d2 a2 r2 hres)
      | ubDeadOrUninit => intro h; exact DropOutcome.noConfusion h

/-- **Core Theorem 2 (`AddMovesForPackedDrops` Alignment-UB Elimination & Trace Equivalence):**
For every list of well-formed compiler drop operations (covering `PackedNoImplDrop`,
`PackedWithImplDrop` custom `Drop` + field drops, normal paths, and unwind cleanup paths),
applying `addMovesForPackedDrops` with any sound aligned stack allocator:
1. Matches the idealized alignment-independent destructor semantics (`evalDropOps ... = idealDropOps ops`),
2. Never faults with `DropOutcome.ubMisalignedSelf` at ANY struct base address. -/
theorem addMovesForPackedDrops_eliminates_unaligned_drop_self_ub
    {allocAligned : Nat → Nat} (hAlloc : AllocSound allocAligned)
    {ops : List DropOp} (hwf : ∀ op, op ∈ ops → WfCompilerDropOp op) :
    evalDropOps (addMovesForPackedDrops allocAligned ops) = idealDropOps ops ∧
    (∀ d a r, evalDropOps (addMovesForPackedDrops allocAligned ops) ≠ .ubMisalignedSelf d a r) := by
  have hEq : evalDropOps (addMovesForPackedDrops allocAligned ops) = idealDropOps ops := by
    induction ops with
    | nil => rfl
    | cons hd tl ih =>
      unfold addMovesForPackedDrops evalDropOps idealDropOps
      have hhd := addMovesForPackedDropsOp_sound hAlloc (hwf hd (List.Mem.head tl))
      have htl := ih (fun x hx => hwf x (List.Mem.tail hd hx))
      rw [hhd]
      unfold seqDropOutcome
      cases idealDropOp hd with
      | ok ev1 => rw [htl]
      | unwind ev1 => rfl
      | ubMisalignedSelf d a r => rfl
      | ubDeadOrUninit => rfl
  have hNoUb : ∀ d a r, idealDropOps ops ≠ .ubMisalignedSelf d a r := by
    clear hEq
    induction ops with
    | nil => intro d a r h; exact DropOutcome.noConfusion h
    | cons hd tl ih =>
      intro d a r
      unfold idealDropOps seqDropOutcome
      cases h1 : idealDropOp hd with
      | ok ev1 =>
        cases h2 : idealDropOps tl with
        | ok ev2 => intro hc; exact DropOutcome.noConfusion hc
        | unwind ev2 => intro hc; exact DropOutcome.noConfusion hc
        | ubMisalignedSelf d2 a2 r2 =>
          exact False.elim (ih (fun x hx => hwf x (List.Mem.tail hd hx)) d2 a2 r2 h2)
        | ubDeadOrUninit => intro hc; exact DropOutcome.noConfusion hc
      | unwind ev1 => intro hc; exact DropOutcome.noConfusion hc
      | ubMisalignedSelf d1 a1 r1 =>
        exact False.elim (idealDropOp_no_ub (hwf hd (List.Mem.head tl)) d1 a1 r1 h1)
      | ubDeadOrUninit => intro hc; exact DropOutcome.noConfusion hc
  exact ⟨hEq, fun d a r h => hNoUb d a r (hEq ▸ h)⟩

/-- Model of `rustc`'s `CheckAlignment` (`-Z ub-checks=yes`) pass (`check_alignment.rs`,
`check_pointers.rs:75-87, 231`, `lib.rs:711, 725`):
- Catches `directMutDeref` in user-crate MIR statements when pointee is known `Sized` (`req > 0`);
- Does **NOT** catch `manualDropInPlace` because `CheckAlignment` runs before `Inline`
  (`lib.rs:711` vs `725`), `core::ptr::drop_in_place<T: PointeeSized>` has `!is_sized`
  (`check_pointers.rs:231`), and `check_pointers` never visits terminators or `DropGlue` shims. -/
noncomputable def checkAlignmentCatchesOp : DropOp → Bool
  | .directMutDeref ptr req =>
    if Nat.beq req 0 then false
    else !Nat.beq (Nat.mod ptr (alignBytes req)) 0
  | .manualDropInPlace _ _ _ _ => false
  | .leaf _ => false
  | .customSelfDropThenFields _ _ _ _ _ _ _ => false

/-- Concrete witness for the `ptr::drop_in_place(&raw mut p.b)` `-Z ub-checks` gap
(base address `16`, `#[repr(C, packed)] struct P { a: u8, b: AlignedDrop(42) }`, so
`&raw mut p.b` is at address `17`, required alignment `2^3 = 8`):
1. `CheckAlignment` (`-Z ub-checks=yes`) fails to catch `manualDropInPlace 17 3 1 42` (`false`);
2. Miri/Rust operational semantics immediately faults `.ubMisalignedSelf 1 17 3`;
3. Control `directMutDeref 17 3` IS caught by `CheckAlignment` (`true`);
4. Safe `read_unaligned` + aligned-temp `drop` (`stagedAlignedDrop` at aligned stack slot `32`)
   succeeds UB-free with exact event `{ dtorId := 1, payload := 42 }`. -/
noncomputable def targetPackedB : DropTarget :=
  { place := { localId := 1, baseAlignExp := 0, projections := [.field (some 0) 1 3], layout := .knownSized 3 }
    baseAddr := 16
    dtorId := 1
    reqAlign := 3
    payload := 42
    panics := false }

theorem drop_in_place_ub_checks_gap_counterexample :
    checkAlignmentCatchesOp (.manualDropInPlace 17 3 1 42) = false ∧
    evalDropOp (.manualDropInPlace 17 3 1 42) = .ubMisalignedSelf 1 17 3 ∧
    checkAlignmentCatchesOp (.directMutDeref 17 3) = true ∧
    evalDropOp (.leaf (.stagedAlignedDrop targetPackedB 32)) = .ok [{ dtorId := 1, payload := 42 }] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Concrete witness for `PackedWithImplDrop`: at base address `17` (odd, `align = 1`),
custom `Drop` runs FIRST (`dtorId = 1000` at `align = 2^0 = 1`), then `AddMovesForPackedDrops`
extracts `self.inner` (`offset 1`, address `18`, `reqAlign = 3`) to aligned stack temp `24`
and runs `<AlignedDrop as Drop>::drop` (`dtorId = 300`), succeeding UB-free in exact order
`[1000, 300]` (whereas without `AddMovesForPackedDrops`, direct drop of `self.inner` at
address `18` faults `.ubMisalignedSelf 300 18 3`). -/
noncomputable def packedWithImplDropExample : DropOp :=
  let innerTarget : DropTarget :=
    { place := { localId := 1, baseAlignExp := 0, projections := [.field (some 0) 1 3], layout := .knownSized 3 }
      baseAddr := 17
      dtorId := 300
      reqAlign := 3
      payload := 33
      panics := false }
  .customSelfDropThenFields 17 0 1000 1 false
    [.directDrop innerTarget] [.directDrop innerTarget]

theorem packedWithImplDrop_before_vs_after_addMoves :
    evalDropOp packedWithImplDropExample = .ubMisalignedSelf 300 18 3 ∧
    evalDropOp (addMovesForPackedDropsOp (fun _ => 24) packedWithImplDropExample) =
      .ok [{ dtorId := 1000, payload := 1 }, { dtorId := 300, payload := 33 }] :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- Section 4: `RemoveUninitDrops` & `ElaborateDrops` Move-Path Drop-Flag Exactness
-- ============================================================================

/-- The four drop styles decided by `ElaborateDropsCtxt::drop_style`
(`compiler/rustc_mir_transform/src/elaborate_drops.rs:165-188`). -/
inductive DropStyle where
  | dead
  | static_
  | conditional
  | open_

/-- Mirrors `ElaborateDropsCtxt::drop_style` decision table on `(maybeInit, maybeUninit, multipart)`. -/
noncomputable def classifyDropStyle (maybeInit maybeUninit multipart : Bool) : DropStyle :=
  match maybeInit, maybeUninit, multipart with
  | false, _, _ => .dead
  | true, false, _ => .static_
  | true, true, false => .conditional
  | true, true, true => .open_

/-- Per-field descriptor of a struct (possibly `#[repr(C, packed)]`) whose fields
are dropped in declaration order `0, 1, ..., n-1`. -/
structure FieldSpec where
  fieldId : Nat
  needsDrop : Bool
  offset : Nat
  reqAlign : Nat
  dtorId : Nat
  payload : Nat

/-- Dataflow analysis fact computed for one field move path at a `Drop` terminator by
`MaybeInitializedPlaces` and `MaybeUninitializedPlaces`. -/
structure FieldDataflow where
  maybeInit : Bool
  maybeUninit : Bool

/-- Runtime dynamic ownership state of one field at a `Drop` terminator:
`live` is the true dynamic initialization bit; `flag` is the dynamic boolean stack drop flag
maintained by `ElaborateDrops` (`false` at `Location::START`, `true` on init, `false` on move). -/
structure FieldDynState where
  spec : FieldSpec
  df : FieldDataflow
  live : Bool
  flag : Bool

/-- Soundness invariant connecting static dataflow (`MaybeInitializedPlaces` /
`MaybeUninitializedPlaces`) and dynamic drop-flag maintenance to true runtime liveness `live`:
1. If `live = true`, then `maybeInit = true` (`MaybeInitializedPlaces` is an over-approximation);
2. If `live = false`, then `maybeUninit = true` (`MaybeUninitializedPlaces` is an over-approximation);
3. Whenever a drop flag is allocated (`maybeInit = true ∧ maybeUninit = true`), the flag equals `live`. -/
noncomputable def FieldInvariant (st : FieldDynState) : Prop :=
  (st.live = true → st.df.maybeInit = true) ∧
  (st.live = false → st.df.maybeUninit = true) ∧
  (st.df.maybeInit = true → st.df.maybeUninit = true → st.flag = st.live)

/-- Pairwise distinctness of field IDs in a struct (no two fields share the same `fieldId`). -/
noncomputable def fieldIdsNodup : List FieldDynState → Prop
  | [] => True
  | s :: rest => (∀ r, r ∈ rest → r.spec.fieldId ≠ s.spec.fieldId) ∧ fieldIdsNodup rest

/-- Ideal source-language drop semantics: drops every field with `needsDrop = true ∧ live = true`
in declaration order. -/
noncomputable def sourceDroppedIds : List FieldDynState → List Nat
  | [] => []
  | s :: rest =>
    if s.spec.needsDrop && s.live then
      s.spec.fieldId :: sourceDroppedIds rest
    else
      sourceDroppedIds rest

/-- `RemoveUninitDrops` (`remove_uninit_drops.rs:75-148`) decision on a struct:
keeps `drop(p)` iff at least one `needsDrop` field has `maybeInit = true`. -/
noncomputable def removeUninitDropsShouldKeep : List FieldDynState → Bool
  | [] => false
  | s :: rest =>
    (s.spec.needsDrop && s.df.maybeInit) || removeUninitDropsShouldKeep rest

/-- `ElaborateDrops` per-field drop emission:
- If `!needsDrop`: skip (erased);
- Else classify `(maybeInit, maybeUninit, false)`:
  - `.dead`: emit nothing (erased to `goto`);
  - `.static_`: emit unconditional `drop(p.f)` (no flag test);
  - `.conditional`: test dynamic stack drop flag `s.flag`; emit `drop(p.f)` iff `s.flag = true`. -/
noncomputable def elaboratedDroppedIds : List FieldDynState → List Nat
  | [] => []
  | s :: rest =>
    if s.spec.needsDrop then
      match classifyDropStyle s.df.maybeInit s.df.maybeUninit false with
      | .dead => elaboratedDroppedIds rest
      | .static_ => s.spec.fieldId :: elaboratedDroppedIds rest
      | .conditional =>
        if s.flag then s.spec.fieldId :: elaboratedDroppedIds rest
        else elaboratedDroppedIds rest
      | .open_ =>
        if s.flag then s.spec.fieldId :: elaboratedDroppedIds rest
        else elaboratedDroppedIds rest
    else
      elaboratedDroppedIds rest

/-- Count how many times `fid` appears in a list of dropped field IDs. -/
noncomputable def countId (fid : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if Nat.beq x fid then 1 else 0) + countId fid xs

/-- Every element in `sourceDroppedIds fields` comes from a member of `fields`. -/
theorem mem_sourceDroppedIds_imp {fid : Nat} {fields : List FieldDynState}
    (hMem : fid ∈ sourceDroppedIds fields) :
    ∃ s, s ∈ fields ∧ s.spec.fieldId = fid ∧ s.spec.needsDrop = true ∧ s.live = true := by
  induction fields with
  | nil => cases hMem
  | cons hd tl ih =>
    unfold sourceDroppedIds at hMem
    cases hnd : hd.spec.needsDrop with
    | false =>
      rw [hnd] at hMem
      rcases ih hMem with ⟨s, hs, hid, h1, h2⟩
      exact ⟨s, List.Mem.tail hd hs, hid, h1, h2⟩
    | true =>
      cases hlv : hd.live with
      | false =>
        rw [hnd, hlv] at hMem
        rcases ih hMem with ⟨s, hs, hid, h1, h2⟩
        exact ⟨s, List.Mem.tail hd hs, hid, h1, h2⟩
      | true =>
        rw [hnd, hlv] at hMem
        cases hMem with
        | head => exact ⟨hd, List.Mem.head tl, rfl, hnd, hlv⟩
        | tail _ hIn =>
          rcases ih hIn with ⟨s, hs, hid, h1, h2⟩
          exact ⟨s, List.Mem.tail hd hs, hid, h1, h2⟩

/-- `countId fid xs = 0` whenever `fid ∉ xs`. -/
theorem countId_eq_zero_of_not_mem {fid : Nat} {xs : List Nat} (h : fid ∉ xs) :
    countId fid xs = 0 := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    unfold countId
    have hne : hd ≠ fid := fun heq => h (heq ▸ List.Mem.head tl)
    have hbeq : Nat.beq hd fid = false := by
      cases hb : Nat.beq hd fid with
      | false => rfl
      | true => exact False.elim (hne (Nat.eq_of_beq_eq_true hb))
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact ih (fun hIn => h (List.Mem.tail hd hIn))

/-- Under `FieldInvariant`, per-field elaborated drop behavior equals source behavior. -/
theorem elaborated_step_eq_source (s : FieldDynState) (hInv : FieldInvariant s) :
    (match classifyDropStyle s.df.maybeInit s.df.maybeUninit false with
     | .dead => false
     | .static_ => true
     | .conditional => s.flag
     | .open_ => s.flag) = s.live := by
  rcases hInv with ⟨hLiveInit, hDeadUninit, hFlag⟩
  cases hmi : s.df.maybeInit with
  | false =>
    unfold classifyDropStyle
    cases hlv : s.live with
    | false => rfl
    | true =>
      have ht := hLiveInit hlv
      rw [hmi] at ht
      exact Bool.noConfusion ht
  | true =>
    cases hmu : s.df.maybeUninit with
    | false =>
      unfold classifyDropStyle
      cases hlv : s.live with
      | true => rfl
      | false =>
        have ht := hDeadUninit hlv
        rw [hmu] at ht
        exact Bool.noConfusion ht
    | true =>
      unfold classifyDropStyle
      exact hFlag hmi hmu

/-- Exact list-level equivalence between `elaboratedDroppedIds` and `sourceDroppedIds`. -/
theorem elaboratedDroppedIds_eq_source {fields : List FieldDynState}
    (hInv : ∀ s, s ∈ fields → FieldInvariant s) :
    elaboratedDroppedIds fields = sourceDroppedIds fields := by
  induction fields with
  | nil => rfl
  | cons hd tl ih =>
    unfold elaboratedDroppedIds sourceDroppedIds
    have htl := ih (fun s hs => hInv s (List.Mem.tail hd hs))
    cases hnd : hd.spec.needsDrop with
    | false =>
      exact htl
    | true =>
      have hStep := elaborated_step_eq_source hd (hInv hd (List.Mem.head tl))
      cases hcs : classifyDropStyle hd.df.maybeInit hd.df.maybeUninit false with
      | dead =>
        rw [hcs] at hStep
        rw [← hStep]
        exact htl
      | static_ =>
        rw [hcs] at hStep
        rw [← hStep]
        exact congrArg (List.cons hd.spec.fieldId) htl
      | conditional =>
        rw [hcs] at hStep
        rw [← hStep]
        cases hd.flag with
        | false => exact htl
        | true => exact congrArg (List.cons hd.spec.fieldId) htl
      | open_ =>
        rw [hcs] at hStep
        rw [← hStep]
        cases hd.flag with
        | false => exact htl
        | true => exact congrArg (List.cons hd.spec.fieldId) htl

/-- **Core Theorem 3 (`ElaborateDrops` Exactness — Every Live Leaf Dropped Exactly Once):**
Under the dataflow & drop-flag soundness invariant (`FieldInvariant`) and distinct field IDs:
1. `elaboratedDroppedIds fields = sourceDroppedIds fields` (exact declaration-order trace);
2. For every field `s ∈ fields`, `countId s.spec.fieldId (elaboratedDroppedIds fields)` equals
   `1` iff `s.spec.needsDrop = true ∧ s.live = true`, and `0` otherwise (zero double-drops,
   zero uninitialized drops, zero resource leaks). -/
theorem elaborateDrops_drop_each_live_leaf_once
    {fields : List FieldDynState}
    (hInv : ∀ s, s ∈ fields → FieldInvariant s)
    (hNodup : fieldIdsNodup fields) :
    elaboratedDroppedIds fields = sourceDroppedIds fields ∧
    ∀ s, s ∈ fields →
      countId s.spec.fieldId (elaboratedDroppedIds fields) =
        if s.spec.needsDrop && s.live then 1 else 0 := by
  have hEq := elaboratedDroppedIds_eq_source hInv
  refine ⟨hEq, ?_⟩
  rw [hEq]
  clear hEq hInv
  induction fields with
  | nil => intro s hs; cases hs
  | cons hd tl ih =>
    rcases hNodup with ⟨hHeadFresh, hTlNodup⟩
    intro s hs
    cases hs with
    | head =>
      have hNotInTail : hd.spec.fieldId ∉ sourceDroppedIds tl := by
        intro hIn
        rcases mem_sourceDroppedIds_imp hIn with ⟨r, hr, hrid, _, _⟩
        exact hHeadFresh r hr hrid
      have hCountZero : countId hd.spec.fieldId (sourceDroppedIds tl) = 0 :=
        countId_eq_zero_of_not_mem hNotInTail
      unfold sourceDroppedIds
      cases hcond : (hd.spec.needsDrop && hd.live) with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hCountZero
      | true =>
        simp only [↓reduceIte]
        unfold countId
        have hself : Nat.beq hd.spec.fieldId hd.spec.fieldId = true := Nat.beq_refl _
        simp only [hself, ↓reduceIte, hCountZero]
    | tail _ hInTl =>
      have hNe : hd.spec.fieldId ≠ s.spec.fieldId :=
        fun heq => hHeadFresh s hInTl (Eq.symm heq)
      have hBeqFalse : Nat.beq hd.spec.fieldId s.spec.fieldId = false := by
        cases hb : Nat.beq hd.spec.fieldId s.spec.fieldId with
        | false => rfl
        | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hb))
      have hRec := ih hTlNodup s hInTl
      unfold sourceDroppedIds
      cases hcond : (hd.spec.needsDrop && hd.live) with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hRec
      | true =>
        simp only [↓reduceIte]
        unfold countId
        simp only [hBeqFalse, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        exact hRec

/-- **`RemoveUninitDrops` Soundness Theorem:**
Whenever `removeUninitDropsShouldKeep fields = false` (no `needsDrop` field is `maybeInit`),
erasing `drop(p)` to `goto` drops `[]`, matching `sourceDroppedIds fields = []`. -/
theorem removeUninitDrops_preserves_semantics
    {fields : List FieldDynState}
    (hInv : ∀ s, s ∈ fields → FieldInvariant s)
    (hErase : removeUninitDropsShouldKeep fields = false) :
    sourceDroppedIds fields = [] := by
  induction fields with
  | nil => rfl
  | cons hd tl ih =>
    unfold removeUninitDropsShouldKeep at hErase
    cases hhd : (hd.spec.needsDrop && hd.df.maybeInit) with
    | true =>
      rw [hhd] at hErase
      exact Bool.noConfusion hErase
    | false =>
      rw [hhd] at hErase
      have htl := ih (fun s hs => hInv s (List.Mem.tail hd hs)) hErase
      unfold sourceDroppedIds
      cases hnd : hd.spec.needsDrop with
      | false =>
        exact htl
      | true =>
        rw [hnd] at hhd
        cases hlv : hd.live with
        | false =>
          exact htl
        | true =>
          have hmi := (hInv hd (List.Mem.head tl)).1 hlv
          rw [hmi] at hhd
          exact Bool.noConfusion hhd

-- ============================================================================
-- Section 5: Composed Pipeline Soundness & Pass-Ordering Counterexample
-- ============================================================================

/-- Convert a list of elaborated live packed fields (produced by `ElaborateDrops` opening
a partially-moved `#[repr(C, packed(2^pack))]` struct at `baseAddr`) into MIR `DropOp`s. -/
noncomputable def fieldStateToDropOps (baseAddr pack : Nat) : List FieldDynState → List DropOp
  | [] => []
  | s :: rest =>
    let tail := fieldStateToDropOps baseAddr pack rest
    if s.spec.needsDrop then
      let shouldDrop :=
        match classifyDropStyle s.df.maybeInit s.df.maybeUninit false with
        | .dead => false
        | .static_ => true
        | .conditional => s.flag
        | .open_ => s.flag
      if shouldDrop then
        let pl : MirPlace :=
          { localId := 4
            baseAlignExp := pack
            projections := [.field (some pack) s.spec.offset s.spec.reqAlign]
            layout := .knownSized s.spec.reqAlign }
        let tgt : DropTarget :=
          { place := pl
            baseAddr := baseAddr
            dtorId := s.spec.dtorId
            reqAlign := s.spec.reqAlign
            payload := s.spec.payload
            panics := false }
        .leaf (.directDrop tgt) :: tail
      else
        tail
    else
      tail

/-- Idealized destructor event list for all live `needsDrop` fields of a struct. -/
noncomputable def sourceDropEvents : List FieldDynState → List DropEvent
  | [] => []
  | s :: rest =>
    if s.spec.needsDrop && s.live then
      { dtorId := s.spec.dtorId, payload := s.spec.payload } :: sourceDropEvents rest
    else
      sourceDropEvents rest

/-- Well-formedness of a packed struct's field offsets at `baseAddr` with pack exponent `pack`. -/
noncomputable def WfPackedFields (baseAddr pack : Nat) (fields : List FieldDynState) : Prop :=
  addrAligned baseAddr pack ∧
  ∀ s, s ∈ fields → alignBytes (natMin s.spec.reqAlign pack) ∣ s.spec.offset

/-- Every `DropOp` emitted by `fieldStateToDropOps` on well-formed packed fields satisfies
`WfCompilerDropOp`. -/
theorem fieldStateToDropOps_wf {baseAddr pack : Nat} {fields : List FieldDynState}
    (hwf : WfPackedFields baseAddr pack fields) :
    ∀ op, op ∈ fieldStateToDropOps baseAddr pack fields → WfCompilerDropOp op := by
  rcases hwf with ⟨hBase, hOffs⟩
  induction fields with
  | nil => intro op hop; cases hop
  | cons hd tl ih =>
    intro op hop
    unfold fieldStateToDropOps at hop
    have hTl := ih (fun s hs => hOffs s (List.Mem.tail hd hs))
    cases hnd : hd.spec.needsDrop with
    | false =>
      rw [hnd] at hop
      exact hTl op hop
    | true =>
      rw [hnd] at hop
      cases hsd :
        (match classifyDropStyle hd.df.maybeInit hd.df.maybeUninit false with
         | .dead => false
         | .static_ => true
         | .conditional => hd.flag
         | .open_ => hd.flag) with
      | false =>
        rw [hsd] at hop
        exact hTl op hop
      | true =>
        rw [hsd] at hop
        cases hop with
        | head =>
          apply WfCompilerDropOp.leaf
          apply WfLeafDropOp.directDrop
          have hOff := hOffs hd (List.Mem.head tl)
          refine
            { baseAligned := hBase
              wfProjs := ⟨natMin hd.spec.reqAlign pack,
                WfProjs.fieldPacked hOff (natMin_le_right hd.spec.reqAlign pack) WfProjs.nil⟩
              reqMatchesType := rfl
              layoutConsistent := rfl }
        | tail _ hIn =>
          exact hTl op hIn

/-- Under `FieldInvariant`, `idealDropOps (fieldStateToDropOps baseAddr pack fields)` equals
`.ok (sourceDropEvents fields)`. -/
theorem idealDropOps_fieldStateToDropOps {baseAddr pack : Nat} {fields : List FieldDynState}
    (hInv : ∀ s, s ∈ fields → FieldInvariant s) :
    idealDropOps (fieldStateToDropOps baseAddr pack fields) = .ok (sourceDropEvents fields) := by
  induction fields with
  | nil => rfl
  | cons hd tl ih =>
    unfold fieldStateToDropOps sourceDropEvents
    have hTl := ih (fun s hs => hInv s (List.Mem.tail hd hs))
    cases hnd : hd.spec.needsDrop with
    | false =>
      exact hTl
    | true =>
      have hStep := elaborated_step_eq_source hd (hInv hd (List.Mem.head tl))
      rw [hStep]
      cases hd.live with
      | false =>
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact hTl
      | true =>
        simp only [Bool.and_true, ↓reduceIte]
        unfold idealDropOps seqDropOutcome idealDropOp idealLeafDropOp
        simp only [Bool.false_eq_true, ↓reduceIte, hTl]
        rfl

/-- **Composed End-to-End Pipeline Theorem (`ElaborateDrops` followed by `AddMovesForPackedDrops`):**
For ANY packed struct (`#[repr(C, packed(2^pack))]`) at ANY aligned base address `baseAddr`
(including odd addresses when `pack = 0`) and ANY conditional-move path satisfying `FieldInvariant`:
1. Running `ElaborateDrops` followed by `AddMovesForPackedDrops` produces the exact
   declaration-order destructor trace `.ok (sourceDropEvents fields)`;
2. Zero misaligned-`self` UB ever occurs;
3. Every live `needsDrop` leaf is dropped exactly once (`count = 1`) and every moved-out or
   non-dropping field is dropped zero times (`count = 0`). -/
theorem full_packed_drop_pipeline_soundness
    {baseAddr pack : Nat} {allocAligned : Nat → Nat} {fields : List FieldDynState}
    (hAlloc : AllocSound allocAligned)
    (hWf : WfPackedFields baseAddr pack fields)
    (hInv : ∀ s, s ∈ fields → FieldInvariant s)
    (hNodup : fieldIdsNodup fields) :
    evalDropOps (addMovesForPackedDrops allocAligned (fieldStateToDropOps baseAddr pack fields)) =
      .ok (sourceDropEvents fields) ∧
    elaboratedDroppedIds fields = sourceDroppedIds fields ∧
    ∀ s, s ∈ fields →
      countId s.spec.fieldId (elaboratedDroppedIds fields) =
        if s.spec.needsDrop && s.live then 1 else 0 := by
  have hPipe := addMovesForPackedDrops_eliminates_unaligned_drop_self_ub hAlloc
    (fieldStateToDropOps_wf hWf)
  have hIdeal := idealDropOps_fieldStateToDropOps (baseAddr := baseAddr) (pack := pack) hInv
  have hElab := elaborateDrops_drop_each_live_leaf_once hInv hNodup
  exact ⟨Eq.trans hPipe.1 hIdeal, hElab.1, hElab.2⟩

-- ============================================================================
-- Section 6: Concrete Instantiations Matching Live `rustc` / Miri Probe
-- (`partial_move_and_dynamic_drop_flag` & Pipeline-Order Counterexample)
-- ============================================================================

/-- Exact model of `partial_move_and_dynamic_drop_flag(take_first, first_tag, second_tag)`
on `#[repr(C, packed)] struct PackedNoImplDrop { pad: u8, first: AlignedDrop, second: AlignedDrop }`
at odd base address `17`:
- Field 0 (`pad: u8`): `needsDrop = false`, offset `0`, align `2^0 = 1`;
- Field 1 (`first: AlignedDrop`): `needsDrop = true`, offset `1`, align `2^3 = 8`,
  dataflow `(maybeInit = true, maybeUninit = true)` -> `DropStyle.conditional` (guarded by `_13`);
- Field 2 (`second: AlignedDrop`): `needsDrop = true`, offset `17`, align `2^3 = 8`,
  dataflow `(maybeInit = true, maybeUninit = false)` -> `DropStyle.static_` (no drop flag!). -/
noncomputable def partialMoveFields (takeFirst : Bool) (firstTag secondTag : Nat) : List FieldDynState :=
  [ { spec := { fieldId := 0, needsDrop := false, offset := 0, reqAlign := 0, dtorId := 0, payload := 3 }
      df := { maybeInit := true, maybeUninit := false }
      live := true
      flag := true },
    { spec := { fieldId := 1, needsDrop := true, offset := 1, reqAlign := 3, dtorId := 1, payload := firstTag }
      df := { maybeInit := true, maybeUninit := true }
      live := !takeFirst
      flag := !takeFirst },
    { spec := { fieldId := 2, needsDrop := true, offset := 17, reqAlign := 3, dtorId := 2, payload := secondTag }
      df := { maybeInit := true, maybeUninit := false }
      live := true
      flag := true } ]

/-- When `takeFirst = true` (first moved out and dropped early with tag 20), scope exit drops
ONLY field 2 (`second`, tag 10) at an aligned stack slot, never double-dropping field 1! -/
theorem partialMove_takeFirst_true_exact :
    elaboratedDroppedIds (partialMoveFields true 20 10) = [2] ∧
    evalDropOps (addMovesForPackedDrops (fun _ => 32) (fieldStateToDropOps 17 0 (partialMoveFields true 20 10))) =
      .ok [{ dtorId := 2, payload := 10 }] :=
  ⟨rfl, rfl⟩

/-- When `takeFirst = false`, scope exit drops field 1 (`first`, tag 2) then field 2
(`second`, tag 5) in declaration order, both extracted to aligned stack slots! -/
theorem partialMove_takeFirst_false_exact :
    elaboratedDroppedIds (partialMoveFields false 2 5) = [1, 2] ∧
    evalDropOps (addMovesForPackedDrops (fun _ => 32) (fieldStateToDropOps 17 0 (partialMoveFields false 2 5))) =
      .ok [{ dtorId := 1, payload := 2 }, { dtorId := 2, payload := 5 }] :=
  ⟨rfl, rfl⟩

/-- **Pipeline-Order Counterexample (Why `AddMovesForPackedDrops` MUST Run AFTER `ElaborateDrops`):**
1. Before `ElaborateDrops`, the whole local `p : PackedNoImplDrop` has `projections = []` and
   `align = 1` (`baseAlignExp = 0`), so `placeUnalignment wholePackedLocal = none`: running
   `AddMovesForPackedDrops` *before* `ElaborateDrops` is a complete no-op on `drop(p)`!
2. Once `ElaborateDrops` opens `drop(p)` into per-field drops `drop(p.1)` and `drop(p.2)`
   at base address `17`, executing those field drops *without* a subsequent
   `AddMovesForPackedDrops` pass immediately faults `.ubMisalignedSelf 2 34 3` (`34 % 8 = 2 ≠ 0`)!
3. Running `AddMovesForPackedDrops` *after* `ElaborateDrops` (`lib.rs:665 -> 674`) eliminates
   that UB completely and produces `.ok [{ dtorId := 2, payload := 10 }]`. -/
noncomputable def wholePackedLocal : MirPlace :=
  { localId := 4
    baseAlignExp := 0
    projections := []
    layout := .knownSized 0 }

theorem pipeline_order_counterexample :
    placeUnalignment wholePackedLocal = none ∧
    evalDropOps (fieldStateToDropOps 17 0 (partialMoveFields true 20 10)) =
      .ubMisalignedSelf 2 34 3 ∧
    evalDropOps (addMovesForPackedDrops (fun _ => 32) (fieldStateToDropOps 17 0 (partialMoveFields true 20 10))) =
      .ok [{ dtorId := 2, payload := 10 }] :=
  ⟨rfl, rfl, rfl⟩

/-- **Stale-Flag Counterexample (`const_extract_both` vs broken drop flag):**
1. When both fields of `PackedPair` are moved out (`live = false, maybeInit = false`),
   `removeUninitDropsShouldKeep = false` and `sourceDroppedIds = []` (matching `const_extract_both`).
2. Conversely, if a broken pass leaves `_flag_1 = true` after moving out field 1 (`live = false`),
   `elaboratedDroppedIds` emits `[1, 2]` — double-dropping moved-out field 1! -/
noncomputable def constExtractBothFields : List FieldDynState :=
  [ { spec := { fieldId := 0, needsDrop := false, offset := 0, reqAlign := 0, dtorId := 0, payload := 1 }
      df := { maybeInit := true, maybeUninit := false }
      live := true
      flag := true },
    { spec := { fieldId := 1, needsDrop := true, offset := 1, reqAlign := 2, dtorId := 1, payload := 10 }
      df := { maybeInit := false, maybeUninit := true }
      live := false
      flag := false },
    { spec := { fieldId := 2, needsDrop := true, offset := 5, reqAlign := 2, dtorId := 2, payload := 20 }
      df := { maybeInit := false, maybeUninit := true }
      live := false
      flag := false } ]

noncomputable def staleFlagBrokenFields : List FieldDynState :=
  [ { spec := { fieldId := 1, needsDrop := true, offset := 1, reqAlign := 3, dtorId := 1, payload := 20 }
      df := { maybeInit := true, maybeUninit := true }
      live := false
      flag := true },
    { spec := { fieldId := 2, needsDrop := true, offset := 17, reqAlign := 3, dtorId := 2, payload := 10 }
      df := { maybeInit := true, maybeUninit := false }
      live := true
      flag := true } ]

theorem constExtractBoth_and_staleFlag_counterexample :
    removeUninitDropsShouldKeep constExtractBothFields = false ∧
    sourceDroppedIds constExtractBothFields = [] ∧
    sourceDroppedIds staleFlagBrokenFields = [2] ∧
    elaboratedDroppedIds staleFlagBrokenFields = [1, 2] :=
  ⟨rfl, rfl, rfl, rfl⟩

end PackedDropsSoundness
