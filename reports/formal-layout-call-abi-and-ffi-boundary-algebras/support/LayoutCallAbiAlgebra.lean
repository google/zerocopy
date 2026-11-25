prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.List.Basic
import Init.SimpLemmas

/-!
# Formal Object Geometry, Call-ABI, and Sub-Register Boundary Algebra

Self-contained `prelude` + `Init.*` Lean 4 formalization establishing:
1. Unbundled data/proof geometry carriers (`GeometryData`, `ValidGeometry`, computable
   validator `validGeometryBool`, and `validGeometryBool_sound`).
2. Dynamic shape `σ` dependent extent-rounding Kleisli calculus (`DynamicStrategy`,
   `alignUp`, `evalDynamic`, divisibility/bounds theorems, and padding-absorption
   non-additivity witness).
3. Exact non-congruence witnesses for `(size, align)`:
   - Itanium C++ `dsize` tail-padding reuse (`podRec` vs `nonPodRec` equal `(size, align)`
     diverging under appending).
   - Interior mutability (`hideNiches`) breaking covariant niche monotonicity (`Option` size `1` vs `2`).
4. Call-ABI sequence state machine (`PassMode`, `ArgAbi`, `BankState`, `allocAbiSeq`) plus
   kernel-checked witnesses that call ABI is neither functorial in geometry (`i128C` vs `i128T`)
   nor a commutative monoid over arguments (`[TwoReg, OneReg]` vs `[OneReg, TwoReg]`),
   alongside CompCertO-style Kripke simulation-convention composition (`SimConv`, `scId`,
   `scComp`, `scRef`) with associativity, unit, and refinement preorder laws.
5. Sub-register partial lenses: preserving sub-views satisfy `GetPut`/`PutGet`/`PutPut` +
   upper-lane framing, while zero-extending narrow writes (`W32 -> X64`, `EAX -> RAX`) satisfy
   `PutGet` and scoped `PutPut` yet refute `GetPut` and overwrite caller upper halves.
6. Environment-family stability (`∀ env ∈ Family`) invariant preservation across FFI/asm frames.
-/

namespace FormalLayoutAbiAlgebra

/-! ## 1. Arithmetic & List Helpers (Pure `Init.*`, Zero `omega`) -/

def natBeq (a b : Nat) : Bool := Nat.beq a b
def natBle (a b : Nat) : Bool := Nat.ble a b
def natBlt (a b : Nat) : Bool := Nat.blt a b

theorem natEq_of_beq : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (natEq_of_beq h)

theorem natBle_iff_le : ∀ (a b : Nat), Nat.ble a b = true ↔ a ≤ b
  | 0, _ => ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
  | _ + 1, 0 => ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_succ_le_zero _ h)⟩
  | a + 1, b + 1 => by
    have ih := natBle_iff_le a b
    exact ⟨fun h => Nat.succ_le_succ (ih.mp h), fun h => ih.mpr (Nat.le_of_succ_le_succ h)⟩

theorem natBlt_iff_lt (a b : Nat) : Nat.blt a b = true ↔ a < b :=
  natBle_iff_le (a + 1) b

def natMax (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => b
  | false => a

def natMin (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => a
  | false => b

theorem natMax_pos_left {a b : Nat} (ha : 0 < a) : 0 < natMax a b := by
  unfold natMax
  cases h : Nat.ble a b with
  | false => exact ha
  | true => exact Nat.lt_of_lt_of_le ha ((natBle_iff_le a b).mp h)

/-- Ceil `n` up to a multiple of `a` (for `a = 0`, yields `0`). -/
def alignUp (n a : Nat) : Nat :=
  match Nat.beq a 0 with
  | true => 0
  | false => ((n + (a - 1)) / a) * a

theorem alignUp_dvd (n a : Nat) : a ∣ alignUp n a := by
  unfold alignUp
  cases h : Nat.beq a 0 with
  | true =>
    have ha : a = 0 := natEq_of_beq h
    subst ha
    exact ⟨0, rfl⟩
  | false =>
    exact ⟨(n + (a - 1)) / a, Nat.mul_comm _ _⟩

theorem alignUp_ge {n a : Nat} (ha : 0 < a) : n ≤ alignUp n a := by
  unfold alignUp
  have hneq : Nat.beq a 0 = false := by
    cases h : Nat.beq a 0 with
    | false => rfl
    | true =>
      have hz : a = 0 := natEq_of_beq h
      subst hz
      exact False.elim (Nat.lt_irrefl 0 ha)
  rw [hneq]
  dsimp only
  have hdiv : n + (a - 1) = ((n + (a - 1)) / a) * a + (n + (a - 1)) % a := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod (n + (a - 1)) a).symm
  have hmod_lt : (n + (a - 1)) % a < a := Nat.mod_lt (n + (a - 1)) ha
  have hmod_le : (n + (a - 1)) % a ≤ a - 1 := by
    cases a with
    | zero => exact False.elim (Nat.lt_irrefl 0 ha)
    | succ a' => exact Nat.le_of_lt_succ hmod_lt
  have hsum : n + (a - 1) ≤ ((n + (a - 1)) / a) * a + (a - 1) :=
    Nat.le_trans (Nat.le_of_eq hdiv) (Nat.add_le_add_left hmod_le _)
  exact Nat.le_of_add_le_add_right hsum

/-! ## 2. Unbundled Geometry Carrier vs Proof Invariant (`Data/Proof Split`) -/

inductive LayoutKind where
  | scalar
  | product
  | unionOverlay
  | taggedSum
  deriving DecidableEq

structure Span where
  offset : Nat
  size   : Nat
  align  : Nat
  deriving DecidableEq

/-- Proof-free object geometry carrier (`0` Prop fields -> avoids WHNF proof bloat). -/
structure GeometryData where
  kind            : LayoutKind
  dataSize        : Nat
  totalSize       : Nat
  align           : Nat
  unadjustedAlign : Nat
  nicheCount      : Nat
  reprC           : Bool
  spans           : List Span
  deriving DecidableEq

def spanNonOverlap (a b : Span) : Prop :=
  a.offset + a.size ≤ b.offset ∨ b.offset + b.size ≤ a.offset

def spansAllNonOverlap : List Span → Prop
  | [] => True
  | s :: ss => (∀ t, t ∈ ss → spanNonOverlap s t) ∧ spansAllNonOverlap ss

def spansWithin (total : Nat) : List Span → Prop
  | [] => True
  | s :: ss => s.offset + s.size ≤ total ∧ 0 < s.align ∧ (s.align ∣ s.offset) ∧ spansWithin total ss

/-- Unbundled validity invariant over `GeometryData`. -/
structure ValidGeometry (g : GeometryData) : Prop where
  alignPos         : 0 < g.align
  unadjPos         : 0 < g.unadjustedAlign
  alignDivSize     : g.align ∣ g.totalSize
  dataLeTotal      : g.dataSize ≤ g.totalSize
  spansInBounds    : spansWithin g.totalSize g.spans
  productDisjoint  : g.kind = .product → spansAllNonOverlap g.spans

def spanNonOverlapBool (a b : Span) : Bool :=
  Nat.ble (a.offset + a.size) b.offset || Nat.ble (b.offset + b.size) a.offset

def spansAllNonOverlapWith (s : Span) : List Span → Bool
  | [] => true
  | t :: ts => spanNonOverlapBool s t && spansAllNonOverlapWith s ts

def spansAllNonOverlapBool : List Span → Bool
  | [] => true
  | s :: ss => spansAllNonOverlapWith s ss && spansAllNonOverlapBool ss

def spansWithinBool (total : Nat) : List Span → Bool
  | [] => true
  | s :: ss =>
    Nat.ble (s.offset + s.size) total &&
    Nat.blt 0 s.align &&
    Nat.beq (s.offset % s.align) 0 &&
    spansWithinBool total ss

def validGeometryBool (g : GeometryData) : Bool :=
  Nat.blt 0 g.align &&
  Nat.blt 0 g.unadjustedAlign &&
  Nat.beq (g.totalSize % g.align) 0 &&
  Nat.ble g.dataSize g.totalSize &&
  spansWithinBool g.totalSize g.spans &&
  (match g.kind with
   | .product => spansAllNonOverlapBool g.spans
   | _ => true)

private theorem band_true_elim {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => exact ⟨rfl, h⟩

private theorem bor_true_elim {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

private theorem spanNonOverlap_of_bool {a b : Span} (h : spanNonOverlapBool a b = true) :
    spanNonOverlap a b := by
  cases bor_true_elim h with
  | inl hl => exact Or.inl ((natBle_iff_le _ _).mp hl)
  | inr hr => exact Or.inr ((natBle_iff_le _ _).mp hr)

private theorem spansAllNonOverlapWith_sound (s : Span) :
    ∀ ss, spansAllNonOverlapWith s ss = true → ∀ t, t ∈ ss → spanNonOverlap s t
  | [], _, _, hmem => by cases hmem
  | u :: us, h, t, hmem => by
    have ⟨h1, h2⟩ := band_true_elim h
    cases hmem with
    | head _ => exact spanNonOverlap_of_bool h1
    | tail _ hm => exact spansAllNonOverlapWith_sound s us h2 t hm

private theorem spansAllNonOverlap_of_bool :
    ∀ ss, spansAllNonOverlapBool ss = true → spansAllNonOverlap ss
  | [], _ => True.intro
  | s :: ss, h => by
    have ⟨h1, h2⟩ := band_true_elim h
    exact ⟨spansAllNonOverlapWith_sound s ss h1, spansAllNonOverlap_of_bool ss h2⟩

private theorem dvd_of_mod_beq_zero {n a : Nat} (h : Nat.beq (n % a) 0 = true) : a ∣ n := by
  have hm : n % a = 0 := natEq_of_beq h
  have hdiv : a * (n / a) + n % a = n := Nat.div_add_mod n a
  rw [hm, Nat.add_zero] at hdiv
  exact ⟨n / a, hdiv.symm⟩

private theorem spansWithin_of_bool (total : Nat) :
    ∀ ss, spansWithinBool total ss = true → spansWithin total ss
  | [], _ => True.intro
  | s :: ss, h => by
    have ⟨h123, h4⟩ := band_true_elim h
    have ⟨h12, h3⟩ := band_true_elim h123
    have ⟨h1, h2⟩ := band_true_elim h12
    exact ⟨(natBle_iff_le _ _).mp h1, (natBlt_iff_lt _ _).mp h2, dvd_of_mod_beq_zero h3,
      spansWithin_of_bool total ss h4⟩

theorem validGeometryBool_sound (g : GeometryData) (h : validGeometryBool g = true) :
    ValidGeometry g := by
  unfold validGeometryBool at h
  have ⟨h12345, h6⟩ := band_true_elim h
  have ⟨h1234, h5⟩ := band_true_elim h12345
  have ⟨h123, h4⟩ := band_true_elim h1234
  have ⟨h12, h3⟩ := band_true_elim h123
  have ⟨h1, h2⟩ := band_true_elim h12
  refine ⟨(natBlt_iff_lt _ _).mp h1, (natBlt_iff_lt _ _).mp h2, dvd_of_mod_beq_zero h3,
    (natBle_iff_le _ _).mp h4, spansWithin_of_bool g.totalSize g.spans h5, ?_⟩
  intro hk
  rw [hk] at h6
  exact spansAllNonOverlap_of_bool g.spans h6

def overlappingRec : GeometryData :=
  { kind := .product, dataSize := 6, totalSize := 8, align := 4, unadjustedAlign := 4,
    nicheCount := 0, reprC := true, spans := [⟨0, 4, 4⟩, ⟨2, 4, 2⟩] }

theorem validGeometryBool_rejects_overlap_canary :
    validGeometryBool overlappingRec = false := by
  decide

/-! ### 2.1 Route-Sensitive Projection Tree (Products vs Overlays) -/

inductive DesignatorStep where
  | field (idx : Nat)
  | unionMember (idx : Nat)
  | enumVariant (idx : Nat)
  deriving DecidableEq

inductive GeoNode where
  | leaf (g : GeometryData)
  | record (g : GeometryData) (children : List (Nat × GeoNode))
  | union (g : GeometryData) (members : List GeoNode)

def nodeGeom : GeoNode → GeometryData
  | .leaf g | .record g _ | .union g _ => g

def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

def projectStep (baseOff : Nat) (step : DesignatorStep) : GeoNode → Option (Nat × GeoNode)
  | .record _ children =>
    match step with
    | .field idx =>
      match listGet? children idx with
      | some (relOff, child) => some (baseOff + relOff, child)
      | none => none
    | _ => none
  | .union _ members =>
    match step with
    | .unionMember idx =>
      match listGet? members idx with
      | some child => some (baseOff, child)
      | none => none
    | _ => none
  | .leaf _ => none

def samplePairLeafA : GeometryData :=
  { kind := .scalar, dataSize := 4, totalSize := 4, align := 4, unadjustedAlign := 4,
    nicheCount := 0, reprC := true, spans := [⟨0, 4, 4⟩] }

def samplePairLeafB : GeometryData :=
  { kind := .scalar, dataSize := 1, totalSize := 1, align := 1, unadjustedAlign := 1,
    nicheCount := 0, reprC := true, spans := [⟨0, 1, 1⟩] }

def sampleRecordNode (parentGeom : GeometryData) : GeoNode :=
  .record parentGeom [(0, .leaf samplePairLeafA), (4, .leaf samplePairLeafB)]

def sampleUnionNode (parentGeom : GeometryData) : GeoNode :=
  .union parentGeom [.leaf samplePairLeafA, .leaf samplePairLeafB]

theorem record_siblings_disjoint (pg : GeometryData) :
    match projectStep 0 (.field 0) (sampleRecordNode pg), projectStep 0 (.field 1) (sampleRecordNode pg) with
    | some (o1, n1), some (o2, n2) =>
      spanNonOverlap ⟨o1, (nodeGeom n1).totalSize, (nodeGeom n1).align⟩
                     ⟨o2, (nodeGeom n2).totalSize, (nodeGeom n2).align⟩
    | _, _ => False := by
  exact Or.inl (Nat.le_refl 4)

theorem union_members_overlap_at_zero (pg : GeometryData) :
    match projectStep 0 (.unionMember 0) (sampleUnionNode pg), projectStep 0 (.unionMember 1) (sampleUnionNode pg) with
    | some (o1, n1), some (o2, n2) =>
      ¬ spanNonOverlap ⟨o1, (nodeGeom n1).totalSize, (nodeGeom n1).align⟩
                       ⟨o2, (nodeGeom n2).totalSize, (nodeGeom n2).align⟩
    | _, _ => False := by
  intro h
  cases h with
  | inl h1 => exact Nat.not_succ_le_zero 3 h1
  | inr h2 => exact Nat.not_succ_le_zero 0 h2

/-! ## 3. Dynamic Shape `σ` Kleisli Layout Calculus -/

structure DynamicTailSpec where
  prefixEnd   : Nat
  prefixAlign : Nat
  packedCap   : Option Nat
  elemSize    : Nat
  elemAlign   : Nat

def effectiveTailAlign (d : DynamicTailSpec) : Nat :=
  match d.packedCap with
  | none => d.elemAlign
  | some cap => natMin cap d.elemAlign

def dynamicAlign (d : DynamicTailSpec) : Nat :=
  natMax d.prefixAlign (effectiveTailAlign d)

def dynamicTailOffset (d : DynamicTailSpec) : Nat :=
  alignUp d.prefixEnd (effectiveTailAlign d)

def dynamicSize (d : DynamicTailSpec) (sigma : Nat) : Nat :=
  alignUp (dynamicTailOffset d + sigma * d.elemSize) (dynamicAlign d)

theorem dynamicAlign_pos (d : DynamicTailSpec) (hp : 0 < d.prefixAlign) :
    0 < dynamicAlign d :=
  natMax_pos_left hp

theorem dynamicSize_align_dvd (d : DynamicTailSpec) (sigma : Nat) :
    dynamicAlign d ∣ dynamicSize d sigma :=
  alignUp_dvd _ _

theorem dynamicSize_ge_payload (d : DynamicTailSpec) (sigma : Nat) (hp : 0 < d.prefixAlign) :
    dynamicTailOffset d + sigma * d.elemSize ≤ dynamicSize d sigma :=
  alignUp_ge (dynamicAlign_pos d hp)

def trailingSliceExample : DynamicTailSpec :=
  { prefixEnd := 5, prefixAlign := 4, packedCap := none, elemSize := 1, elemAlign := 1 }

/-- Dynamic extent rounding is NOT additive: head padding absorbs the `1`-aligned tail! -/
theorem dynamic_extent_not_naive_sum :
    let headSize := alignUp trailingSliceExample.prefixEnd trailingSliceExample.prefixAlign
    dynamicSize trailingSliceExample 1 = 8 ∧
    headSize + 1 * trailingSliceExample.elemSize = 9 ∧
    dynamicSize trailingSliceExample 1 < headSize + 1 * trailingSliceExample.elemSize := by
  decide

/-! ## 4. Algebraic Non-Compositionality Witnesses for `(size, align)` -/

/-- Appending field `(fSize, fAlign)` ignoring tail-padding reuse (`POD` / C `repr(C)`). -/
def appendNoDsize (baseTotal baseAlign fSize fAlign : Nat) : Nat × Nat :=
  let off := alignUp baseTotal fAlign
  let al  := natMax baseAlign fAlign
  (alignUp (off + fSize) al, al)

/-- Appending field `(fSize, fAlign)` reusing base tail padding (`Itanium` non-POD `dsize`). -/
def appendWithDsize (baseData baseAlign fSize fAlign : Nat) : Nat × Nat :=
  let off := alignUp baseData fAlign
  let al  := natMax baseAlign fAlign
  (alignUp (off + fSize) al, al)

def podRec : GeometryData :=
  { kind := .product, dataSize := 8, totalSize := 8, align := 4, unadjustedAlign := 4,
    nicheCount := 0, reprC := true, spans := [⟨0, 4, 4⟩, ⟨4, 1, 1⟩] }

def nonPodRec : GeometryData :=
  { kind := .product, dataSize := 5, totalSize := 8, align := 4, unadjustedAlign := 4,
    nicheCount := 0, reprC := true, spans := [⟨0, 4, 4⟩, ⟨4, 1, 1⟩] }

theorem sizeAlign_not_layout_congruence :
    podRec.totalSize = nonPodRec.totalSize ∧
    podRec.align = nonPodRec.align ∧
    (appendWithDsize podRec.dataSize podRec.align 1 1).1 = 12 ∧
    (appendWithDsize nonPodRec.dataSize nonPodRec.align 1 1).1 = 8 := by
  decide

/-- Wrapper modeling `UnsafeCell` disabling niche optimizations while preserving `(size, align)`. -/
def wrapUnsafeCell (g : GeometryData) : GeometryData :=
  { g with nicheCount := 0 }

def optionSize (payload : GeometryData) : Nat :=
  if Nat.blt 0 payload.nicheCount then payload.totalSize
  else alignUp (1 + payload.totalSize) payload.align

def boolGeom : GeometryData :=
  { kind := .scalar, dataSize := 1, totalSize := 1, align := 1, unadjustedAlign := 1,
    nicheCount := 254, reprC := true, spans := [⟨0, 1, 1⟩] }

theorem niche_suppressed_by_interior_mut :
    boolGeom.totalSize = (wrapUnsafeCell boolGeom).totalSize ∧
    boolGeom.align = (wrapUnsafeCell boolGeom).align ∧
    optionSize boolGeom = 1 ∧
    optionSize (wrapUnsafeCell boolGeom) = 2 := by
  decide

/-! ## 5. Call-ABI State Monad, Non-Functoriality, & CompCertO Preorder -/

inductive PassMode where
  | direct
  | castPair
  | indirectStack
  deriving DecidableEq

structure AbiTypeDesc where
  totalSize : Nat
  align     : Nat
  reprC     : Bool
  isPair16  : Bool -- requires 2 GP registers atomically (e.g., 16-byte struct)
  deriving DecidableEq

structure BankState where
  gpLeft     : Nat
  stackSlots : Nat
  deriving DecidableEq

def allocOneArg (st : BankState) (ty : AbiTypeDesc) : PassMode × BankState :=
  if ty.isPair16 then
    if Nat.ble 2 st.gpLeft then
      if ty.reprC then (.castPair, { st with gpLeft := st.gpLeft - 2 })
      else (.direct, { st with gpLeft := st.gpLeft - 2 })
    else
      (.indirectStack, { st with stackSlots := st.stackSlots + 2 })
  else
    if Nat.ble 1 st.gpLeft then
      (.direct, { st with gpLeft := st.gpLeft - 1 })
    else
      (.indirectStack, { st with stackSlots := st.stackSlots + 1 })

def allocAbiSeq (st : BankState) : List AbiTypeDesc → List PassMode × BankState
  | [] => ([], st)
  | t :: ts =>
    let (m, st1) := allocOneArg st t
    let (ms, st2) := allocAbiSeq st1 ts
    (m :: ms, st2)

def i128CDesc : AbiTypeDesc := { totalSize := 16, align := 16, reprC := true, isPair16 := true }
def i128TDesc : AbiTypeDesc := { totalSize := 16, align := 16, reprC := false, isPair16 := true }
def u64Desc   : AbiTypeDesc := { totalSize := 8, align := 8, reprC := true, isPair16 := false }

theorem callAbi_not_geometry_functor :
    i128CDesc.totalSize = i128TDesc.totalSize ∧
    i128CDesc.align = i128TDesc.align ∧
    (allocOneArg { gpLeft := 6, stackSlots := 0 } i128CDesc).1 = .castPair ∧
    (allocOneArg { gpLeft := 6, stackSlots := 0 } i128TDesc).1 = .direct := by
  decide

/-- Stateful order sensitivity + all-or-nothing rollback breaks monoidality over argument lists. -/
theorem callAbi_not_argument_monoid :
    let init : BankState := { gpLeft := 2, stackSlots := 0 }
    allocAbiSeq init [i128CDesc, u64Desc] = ([.castPair, .indirectStack], { gpLeft := 0, stackSlots := 1 }) ∧
    allocAbiSeq init [u64Desc, i128CDesc] = ([.direct, .indirectStack], { gpLeft := 1, stackSlots := 2 }) := by
  decide

theorem no_functor_of_sizeAlign_to_callAbi :
    ∃ (t1 t2 : AbiTypeDesc) (st : BankState),
      t1.totalSize = t2.totalSize ∧ t1.align = t2.align ∧
      (allocOneArg st t1).1 ≠ (allocOneArg st t2).1 := by
  refine ⟨i128CDesc, i128TDesc, { gpLeft := 6, stackSlots := 0 }, rfl, rfl, ?_⟩
  intro h
  exact PassMode.noConfusion h

/-- Minimal Kripke Simulation Convention (`CompCertO` `CallconvAlgebra.v`) in `Prop`/`Type`. -/
structure LangIface where
  Query : Type
  Reply : Type

structure SimConv (A B : LangIface) where
  World      : Type
  matchQuery : World → A.Query → B.Query → Prop
  matchReply : World → A.Reply → B.Reply → Prop

def scId (A : LangIface) : SimConv A A where
  World := Unit
  matchQuery _ q1 q2 := q1 = q2
  matchReply _ r1 r2 := r1 = r2

def scComp {A B C : LangIface} (c1 : SimConv A B) (c2 : SimConv B C) : SimConv A C where
  World := c1.World × c2.World
  matchQuery w qA qC := ∃ qB, c1.matchQuery w.1 qA qB ∧ c2.matchQuery w.2 qB qC
  matchReply w rA rC := ∃ rB, c1.matchReply w.1 rA rB ∧ c2.matchReply w.2 rB rC

def scRef {A B : LangIface} (c c' : SimConv A B) : Prop :=
  ∀ w q1 q2, c.matchQuery w q1 q2 →
    ∃ w', c'.matchQuery w' q1 q2 ∧ ∀ r1 r2, c'.matchReply w' r1 r2 → c.matchReply w r1 r2

theorem scRef_refl {A B : LangIface} (c : SimConv A B) : scRef c c :=
  fun w _ _ hq => ⟨w, hq, fun _ _ hr => hr⟩

theorem scRef_trans {A B : LangIface} {c1 c2 c3 : SimConv A B}
    (h12 : scRef c1 c2) (h23 : scRef c2 c3) : scRef c1 c3 := by
  intro w q1 q2 hq1
  have ⟨w2, hq2, hr21⟩ := h12 w q1 q2 hq1
  have ⟨w3, hq3, hr32⟩ := h23 w2 q1 q2 hq2
  exact ⟨w3, hq3, fun r1 r2 hr3 => hr21 r1 r2 (hr32 r1 r2 hr3)⟩

theorem scComp_id_left {A B : LangIface} (c : SimConv A B) :
    scRef (scComp (scId A) c) c ∧ scRef c (scComp (scId A) c) := by
  refine ⟨?_, ?_⟩
  · intro ⟨_, wc⟩ q1 q2 ⟨qm, hqm, hq2⟩
    subst hqm
    refine ⟨wc, hq2, ?_⟩
    intro r1 r2 hr
    exact ⟨r1, rfl, hr⟩
  · intro wc q1 q2 hq
    refine ⟨((), wc), ⟨q1, rfl, hq⟩, ?_⟩
    intro r1 r2 ⟨rm, hrm, hrc⟩
    subst hrm
    exact hrc

theorem scComp_id_right {A B : LangIface} (c : SimConv A B) :
    scRef (scComp c (scId B)) c ∧ scRef c (scComp c (scId B)) := by
  refine ⟨?_, ?_⟩
  · intro ⟨wc, _⟩ q1 q2 ⟨qm, hq1, hqm⟩
    subst hqm
    refine ⟨wc, hq1, ?_⟩
    intro r1 r2 hr
    exact ⟨r2, hr, rfl⟩
  · intro wc q1 q2 hq
    refine ⟨(wc, ()), ⟨q2, hq, rfl⟩, ?_⟩
    intro r1 r2 ⟨rm, hrc, hrm⟩
    subst hrm
    exact hrc

theorem scComp_assoc {A B C D : LangIface}
    (c1 : SimConv A B) (c2 : SimConv B C) (c3 : SimConv C D) :
    scRef (scComp (scComp c1 c2) c3) (scComp c1 (scComp c2 c3)) := by
  intro ⟨⟨w1, w2⟩, w3⟩ qA qD ⟨qC, ⟨qB, h1, h2⟩, h3⟩
  refine ⟨(w1, (w2, w3)), ⟨qB, h1, ⟨qC, h2, h3⟩⟩, ?_⟩
  intro rA rD ⟨rB, hr1, ⟨rC, hr2, hr3⟩⟩
  exact ⟨rC, ⟨rB, hr1, hr2⟩, hr3⟩

/-! ## 6. Partial-Width Sub-Register Lenses & Environment-Polymorphic Frame Framing -/

/-- 2-half register (`lo` = narrow view such as `w0` or legacy `al`/`ax`; `hi` = upper lane bits). -/
structure SplitReg where
  lo : Nat
  hi : Nat
  deriving DecidableEq

def getLow (r : SplitReg) : Nat := r.lo
def getHigh (r : SplitReg) : Nat := r.hi

/-- Width-preserving partial write (e.g. `al`/`ax` into `rax`, or legacy scalar SSE on preserved lanes). -/
def putLowPreserve (r : SplitReg) (v : Nat) : SplitReg := ⟨v, r.hi⟩

/-- Zero-extending narrow write (AArch64 `W32 -> X64`, x86-64 `EAX -> RAX`, VEX/EVEX 128b write zeroing upper `YMM`/`ZMM`). -/
def putLowZeroHi (_r : SplitReg) (v : Nat) : SplitReg := ⟨v, 0⟩

theorem putLowPreserve_getPut (r : SplitReg) : putLowPreserve r (getLow r) = r := by
  cases r; rfl

theorem putLowPreserve_putGet (r : SplitReg) (v : Nat) : getLow (putLowPreserve r v) = v := rfl

theorem putLowPreserve_putPut (r : SplitReg) (v1 v2 : Nat) :
    putLowPreserve (putLowPreserve r v1) v2 = putLowPreserve r v2 := rfl

theorem putLowPreserve_frames_hi (r : SplitReg) (v : Nat) :
    getHigh (putLowPreserve r v) = getHigh r := rfl

theorem putLowZeroHi_putGet (r : SplitReg) (v : Nat) : getLow (putLowZeroHi r v) = v := rfl

theorem putLowZeroHi_putPut (r : SplitReg) (v1 v2 : Nat) :
    putLowZeroHi (putLowZeroHi r v1) v2 = putLowZeroHi r v2 := rfl

theorem putLowZeroHi_refutes_getPut :
    putLowZeroHi ⟨1, 42⟩ (getLow ⟨1, 42⟩) ≠ ⟨1, 42⟩ ∧
    getHigh (putLowZeroHi ⟨1, 42⟩ 7) = 0 := by
  decide

/-- Machine envelope separating return, callee-saved frame, invariant control flags, and scratch. -/
structure MachineState where
  retVal      : Nat
  calleeFrame : Nat
  invFlags    : Nat   -- e.g. DF=0, vstart=0, FPCR
  scratch     : Nat
  deriving DecidableEq

def AsmPreservesCallerFrame (pre post : MachineState) : Prop :=
  post.calleeFrame = pre.calleeFrame ∧ post.invFlags = pre.invFlags

/-- Environment-polymorphic stability: holds uniformly over any environment family `Admissible`. -/
def StableAcrossEnvFamily {Env : Type} (Admissible : Env → Prop)
    (step : Env → MachineState → MachineState) : Prop :=
  ∀ env, Admissible env → ∀ s, AsmPreservesCallerFrame s (step env s)

theorem compose_env_frame_stable {Env : Type} {Admissible : Env → Prop}
    {f g : Env → MachineState → MachineState}
    (hf : StableAcrossEnvFamily Admissible f)
    (hg : StableAcrossEnvFamily Admissible g) :
    StableAcrossEnvFamily Admissible (fun env s => g env (f env s)) := by
  intro env hadm s
  have h1 := hf env hadm s
  have h2 := hg env hadm (f env s)
  exact ⟨Eq.trans h2.1 h1.1, Eq.trans h2.2 h1.2⟩

end FormalLayoutAbiAlgebra
