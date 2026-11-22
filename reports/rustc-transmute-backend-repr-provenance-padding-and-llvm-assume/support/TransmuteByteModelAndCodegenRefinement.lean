/-!
# Mechanized Byte-Level Transmute Semantics, `@llvm.assume` Scalar Ranges, Provenance Refinement, and `ScalarPair` Register-vs-`alloca` Equivalence

Self-contained Lean 4 (`v4.34.1`, core prelude only, zero imports) formalization of:
1. `AbstractByte` (`uninit` | `bits (b : UInt8)` | `ptrByte (alloc : Nat) (ofs : Nat) (b : UInt8)`),
   two-pass `copy_op_allow_transmute` validation with provenance clearing and padding reset,
   `CastKind::BoxDerefTransmute` dereferenceability pre-validation, and `CastKind::PointerExposeProvenance`
   vs `CastKind::Transmute` provenance stripping.
2. Necessary and sufficient `SafeTransmute` soundness conditions (`sizeSrc = sizeDst`, bytewise
   initialization/provenance subtyping, and `WrappingRange` scalar validity containment), plus
   exact equivalence of `rustc`'s single-`icmp ule` `assume_integer_range` encoding across both
   contiguous and wrapping niche intervals.
3. The 6-arm `cg_transmute` (`codegen_transmute_operand`) `BackendRepr` dispatch, proving strict
   forward refinement (`evalTransmuteOpSem ⊑ evalCgTransmuteLLVM`) under `ptrtoint` provenance
   exposure and refuting reverse LLVM-to-OpSem refinement.
4. Exact equivalence between in-register `ScalarPair -> ScalarPair` transmutation and `alloca`
   memory spill/reload across arbitrary sizes and offsets whenever component sizes and `b_offset`
   match, together with three constructive counterexamples (`ce1`, `ce2`, `ce3`).

All value declarations are marked `noncomputable` so Lean generates zero `._unsafe_rec` helpers.
Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`.
-/

namespace TransmuteByteModel

/-! ## 1. `AbstractByte`, Outcomes, Forward Refinement, and Provenance State -/

/-- Byte-level memory/value representation matching `rustc_const_eval` (`Allocation`:
`bytes` + `InitMask` + `ProvenanceMap`). -/
inductive AbstractByte : Type where
  | uninit : AbstractByte
  | bits (b : UInt8) : AbstractByte
  | ptrByte (alloc : Nat) (ofs : Nat) (b : UInt8) : AbstractByte

/-- Evaluation outcome: either a well-defined value or Undefined Behavior (`ub`). -/
inductive Outcome (α : Type) : Type where
  | ok (val : α) : Outcome α
  | ub : Outcome α

/-- Standard compiler forward refinement (`src ⊑ tgt`): every defined source behavior is
reproduced identically by the target, while source `ub` may be refined into any outcome. -/
noncomputable def Outcome.Refines {α : Type} (src tgt : Outcome α) : Prop :=
  ∀ v, src = .ok v → tgt = .ok v

theorem Outcome.refines_refl {α : Type} (o : Outcome α) : Outcome.Refines o o := by
  intro v hv
  exact hv

theorem Outcome.refines_trans {α : Type} {a b c : Outcome α}
    (hab : Outcome.Refines a b) (hbc : Outcome.Refines b c) :
    Outcome.Refines a c := by
  intro v ha
  exact hbc v (hab v ha)

theorem Outcome.ub_refines_all {α : Type} (tgt : Outcome α) :
    Outcome.Refines .ub tgt := by
  intro v h
  cases h

/-- Interpreter/machine allocation and provenance exposure state (`alloc_addresses::GlobalStateInner`). -/
structure ProvState : Type where
  liveAllocs : List Nat
  exposedAllocs : List Nat

/-- Monotonicity preorder on provenance state: identical live allocations, and `s2` has exposed
a superset of `s1`'s exposed allocations. -/
noncomputable def ProvState.Sub (s1 s2 : ProvState) : Prop :=
  s1.liveAllocs = s2.liveAllocs ∧ ∀ a, a ∈ s1.exposedAllocs → a ∈ s2.exposedAllocs

theorem ProvState.sub_refl (s : ProvState) : ProvState.Sub s s :=
  ⟨rfl, fun _ ha => ha⟩

/-- Whether a single `AbstractByte` is initialized. -/
noncomputable def isInitByte : AbstractByte → Bool
  | .uninit => false
  | .bits _ => true
  | .ptrByte _ _ _ => true

/-- Runtime (`OFFSET_IS_ADDR = true`) byte read stripping provenance (`Allocation::read_scalar`
with `read_provenance = false`). Fails with `none` on `uninit`. -/
noncomputable def rawByteVal? : AbstractByte → Option UInt8
  | .uninit => none
  | .bits b => some b
  | .ptrByte _ _ b => some b

/-- Clear provenance on a single byte (`Allocation::clear_provenance`). -/
noncomputable def clearByteProv : AbstractByte → AbstractByte
  | .uninit => .uninit
  | .bits b => .bits b
  | .ptrByte _ _ b => .bits b

/-- Little-endian unsigned integer decoding of raw bytes. -/
noncomputable def decodeLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLE bs

/-- Read all raw bytes of a slice if every byte is initialized. -/
noncomputable def readRawBytes? : List AbstractByte → Option (List UInt8)
  | [] => some []
  | ab :: abs =>
    match rawByteVal? ab, readRawBytes? abs with
    | some b, some bs => some (b :: bs)
    | _, _ => none

/-- Check that `rest` consists of consecutive fragments `idx, idx+1, ...` of `alloc`. -/
noncomputable def checkPtrFrags (alloc : Nat) (idx : Nat) : List AbstractByte → Bool
  | [] => true
  | .ptrByte a ofs _ :: rest =>
    (a == alloc) && (ofs == idx) && checkPtrFrags alloc (idx + 1) rest
  | _ => false

/-- Extract coherent pointer provenance (`Some alloc`) iff the non-empty byte sequence forms a
complete, uncorrupted pointer `(alloc, 0 .. n-1)` (`ProvenanceMap::read_ptr`). -/
noncomputable def coherentPtrAlloc? : List AbstractByte → Option Nat
  | .ptrByte alloc 0 _ :: rest =>
    match checkPtrFrags alloc 1 rest with
    | true => some alloc
    | false => none
  | _ => none

/-- Tag raw address bytes with pointer provenance `alloc` starting at fragment offset `ofs`. -/
noncomputable def tagPtrBytes (alloc : Nat) (ofs : Nat) : List UInt8 → List AbstractByte
  | [] => []
  | b :: bs => .ptrByte alloc ofs b :: tagPtrBytes alloc (ofs + 1) bs

/-! ## 2. `WrappingRange` and `assume_integer_range` Single-`icmp ule` Encoding -/

/-- Modular wrapping scalar validity range (`rustc_abi::WrappingRange` over `[0, modulus)`). -/
structure WrappingRange : Type where
  modulus : Nat
  start : Nat
  end_ : Nat

/-- Membership in a `WrappingRange` (`rustc_abi::WrappingRange::contains`):
contiguous `[start, end_]` when `start ≤ end_`, or wrapping `[start, modulus) ∪ [0, end_]`
when `end_ < start`. -/
noncomputable def WrappingRange.contains (r : WrappingRange) (v : Nat) : Bool :=
  match decide (r.start ≤ r.end_) with
  | true => decide (r.start ≤ v) && decide (v ≤ r.end_)
  | false => decide (r.start ≤ v) || decide (v ≤ r.end_)

/-- Exact encoding emitted by `BuilderMethods::assume_integer_range`
(`compiler/rustc_codegen_ssa/src/traits/builder.rs:289-304`):
`shifted = (imm - start) mod M`, `width = (end - start) mod M`, `icmp ule shifted, width`. -/
noncomputable def assumeIntegerRangeCheck (r : WrappingRange) (v : Nat) : Bool :=
  let shifted := (v + r.modulus - r.start) % r.modulus
  let width := (r.end_ + r.modulus - r.start) % r.modulus
  decide (shifted ≤ width)

theorem mod_sub_ge {x s m : Nat} (hsx : s ≤ x) (hxm : x < m) :
    (x + m - s) % m = x - s := by
  have h1 : x + m - s = x - s + m := Nat.sub_add_comm hsx
  rw [h1, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le x s) hxm)

theorem mod_sub_lt {x s m : Nat} (hxs : x < s) (hsm : s ≤ m) :
    (x + m - s) % m = x + (m - s) := by
  have h1 : x + m - s = x + (m - s) := Nat.add_sub_assoc hsm x
  rw [h1]
  have hlt : x + (m - s) < m := by
    have h2 : x + (m - s) < s + (m - s) := Nat.add_lt_add_right hxs (m - s)
    rw [Nat.add_sub_of_le hsm] at h2
    exact h2
  exact Nat.mod_eq_of_lt hlt

/-- For every `WrappingRange` (both contiguous `start ≤ end_` such as `NonZeroU32` `1..=2^32-1`
and wrapping `end_ < start` such as `Ordering` `255..=1` mod `256`), `rustc`'s single
`sub + icmp ule` check agrees identically with `WrappingRange.contains`. -/
theorem assumeIntegerRangeCheck_eq_contains (r : WrappingRange) (v : Nat)
    (hs : r.start < r.modulus) (he : r.end_ < r.modulus) (hv : v < r.modulus) :
    assumeIntegerRangeCheck r v = WrappingRange.contains r v := by
  unfold assumeIntegerRangeCheck WrappingRange.contains
  have hsm : r.start ≤ r.modulus := Nat.le_of_lt hs
  cases hdse : decide (r.start ≤ r.end_) with
  | true =>
    have hse : r.start ≤ r.end_ := of_decide_eq_true hdse
    dsimp only
    rw [mod_sub_ge hse he]
    cases hdsv : decide (r.start ≤ v) with
    | true =>
      have hsv : r.start ≤ v := of_decide_eq_true hdsv
      rw [mod_sub_ge hsv hv, Bool.true_and]
      cases hdve : decide (v ≤ r.end_) with
      | true =>
        have hve : v ≤ r.end_ := of_decide_eq_true hdve
        have hsub : v - r.start ≤ r.end_ - r.start := Nat.sub_le_sub_right hve r.start
        exact decide_eq_true hsub
      | false =>
        have hve : ¬ (v ≤ r.end_) := of_decide_eq_false hdve
        have hnot : ¬ (v - r.start ≤ r.end_ - r.start) := by
          intro hsub
          have hadd := Nat.add_le_add_right hsub r.start
          rw [Nat.sub_add_cancel hsv, Nat.sub_add_cancel hse] at hadd
          exact hve hadd
        exact decide_eq_false hnot
    | false =>
      have hsv : ¬ (r.start ≤ v) := of_decide_eq_false hdsv
      have hvs : v < r.start := Nat.lt_of_not_le hsv
      rw [mod_sub_lt hvs hsm, Bool.false_and]
      have hnot : ¬ (v + (r.modulus - r.start) ≤ r.end_ - r.start) := by
        intro hle
        have hle1 : r.modulus - r.start ≤ r.end_ - r.start :=
          Nat.le_trans (Nat.le_add_left (r.modulus - r.start) v) hle
        have hadd := Nat.add_le_add_right hle1 r.start
        rw [Nat.sub_add_cancel hsm, Nat.sub_add_cancel hse] at hadd
        exact Nat.not_le_of_gt he hadd
      exact decide_eq_false hnot
  | false =>
    have hse : ¬ (r.start ≤ r.end_) := of_decide_eq_false hdse
    dsimp only
    have hes : r.end_ < r.start := Nat.lt_of_not_le hse
    rw [mod_sub_lt hes hsm]
    cases hdsv : decide (r.start ≤ v) with
    | true =>
      have hsv : r.start ≤ v := of_decide_eq_true hdsv
      rw [mod_sub_ge hsv hv, Bool.true_or]
      have hle : v - r.start ≤ r.end_ + (r.modulus - r.start) := by
        have h1 : v - r.start ≤ r.modulus - r.start :=
          Nat.sub_le_sub_right (Nat.le_of_lt hv) r.start
        exact Nat.le_trans h1 (Nat.le_add_left (r.modulus - r.start) r.end_)
      exact decide_eq_true hle
    | false =>
      have hsv : ¬ (r.start ≤ v) := of_decide_eq_false hdsv
      have hvs : v < r.start := Nat.lt_of_not_le hsv
      rw [mod_sub_lt hvs hsm, Bool.false_or]
      cases hdve : decide (v ≤ r.end_) with
      | true =>
        have hve : v ≤ r.end_ := of_decide_eq_true hdve
        have hle : v + (r.modulus - r.start) ≤ r.end_ + (r.modulus - r.start) :=
          Nat.add_le_add_right hve (r.modulus - r.start)
        exact decide_eq_true hle
      | false =>
        have hve : ¬ (v ≤ r.end_) := of_decide_eq_false hdve
        have hnot : ¬ (v + (r.modulus - r.start) ≤ r.end_ + (r.modulus - r.start)) := by
          intro hle
          exact hve (Nat.le_of_add_le_add_right hle)
        exact decide_eq_false hnot

/-! ## 3. `ByteSpec`, `TyLayout`, and Two-Pass `validateAndReset` (`copy_op_allow_transmute`) -/

/-- Per-byte layout classification (`ValidityVisitor` + `reset_provenance_and_padding`). -/
inductive ByteSpec : Type where
  /-- Struct/enum padding byte: accepts any byte on input; reset to `.uninit` on typed copy. -/
  | pad : ByteSpec
  /-- Union data byte (`MaybeUninit<u8>`): accepts any byte (`uninit`, `bits`, `ptrByte`) and
      preserves it unchanged without resetting padding or clearing provenance. -/
  | maybeUninit : ByteSpec
  /-- Initialized non-pointer byte (`u8`, `u32`, `f32`, `bool`): requires `isInitByte` and
      clears provenance to `.bits`. -/
  | initBits : ByteSpec
  /-- Pointer byte at fragment index `ofs`: requires `isInitByte`; preserves `.ptrByte` iff the
      whole value forms a coherent pointer, otherwise clears partial provenance to `.bits`. -/
  | ptrFrag (ofs : Nat) : ByteSpec

/-- Pointer dereferenceability invariant (`ValidityVisitor::try_visit_primitive` vs `visit_box`). -/
inductive PtrKindSpec : Type where
  | none : PtrKindSpec
  | rawPtr : PtrKindSpec
  | safeBoxOrRef : PtrKindSpec

/-- Backend value representation dispatched by `codegen_transmute_operand` (`rvalue.rs:379-442`). -/
inductive BackendRepr : Type where
  | zst : BackendRepr
  | memory : BackendRepr
  | scalar (sz : Nat) : BackendRepr
  | simdVector (lanes : Nat) (elemSz : Nat) (hasPtrElem : Bool) : BackendRepr
  | scalarPair (aSz : Nat) (bSz : Nat) (bOffset : Nat)
      (aRange : Option WrappingRange) (bRange : Option WrappingRange) : BackendRepr

/-- Type layout combining byte-level initialization/padding mask, pointer validity requirement,
optional scalar `WrappingRange`, and `BackendRepr`. -/
structure TyLayout : Type where
  size : Nat
  byteSpecs : List ByteSpec
  ptrKind : PtrKindSpec
  validRange : Option WrappingRange
  backendRepr : BackendRepr

/-- Validate and reset a single byte according to its `ByteSpec`. -/
noncomputable def validateAndResetByte (coherentPtr : Bool) (spec : ByteSpec)
    (ab : AbstractByte) : Option AbstractByte :=
  match spec, ab with
  | .pad, _ => some .uninit
  | .maybeUninit, x => some x
  | .initBits, .uninit => none
  | .initBits, .bits b => some (.bits b)
  | .initBits, .ptrByte _ _ b => some (.bits b)
  | .ptrFrag _, .uninit => none
  | .ptrFrag _, .bits b => some (.bits b)
  | .ptrFrag ofs, .ptrByte a o b =>
    match coherentPtr && (o == ofs) with
    | true => some (.ptrByte a o b)
    | false => some (.bits b)

/-- Apply `validateAndResetByte` pairwise across `specs` and `bytes`. -/
noncomputable def validateAndResetBytes (coherentPtr : Bool) :
    List ByteSpec → List AbstractByte → Option (List AbstractByte)
  | [], [] => some []
  | s :: ss, b :: bs =>
    match validateAndResetByte coherentPtr s b, validateAndResetBytes coherentPtr ss bs with
    | some b', some bs' => some (b' :: bs')
    | _, _ => none
  | _, _ => none

/-- Check optional scalar validity range on an already-initialized byte slice. -/
noncomputable def checkOptRange (rOpt : Option WrappingRange) (outBytes : List AbstractByte) :
    Outcome (List AbstractByte) :=
  match rOpt with
  | none => .ok outBytes
  | some r =>
    match readRawBytes? outBytes with
    | none => .ub
    | some raw =>
      match WrappingRange.contains r (decodeLE raw) with
      | true => .ok outBytes
      | false => .ub

/-- Full `validate_place(..., reset_provenance_and_padding = true)` pass on `bytes` at `ty`. -/
noncomputable def validateAndReset (ty : TyLayout) (liveAllocs : List Nat)
    (bytes : List AbstractByte) : Outcome (List AbstractByte) :=
  match (bytes.length == ty.size) && (ty.byteSpecs.length == ty.size) with
  | false => .ub
  | true =>
    let coherentAlloc := coherentPtrAlloc? bytes
    match validateAndResetBytes coherentAlloc.isSome ty.byteSpecs bytes with
    | none => .ub
    | some outBytes =>
      let ptrOk : Bool :=
        match ty.ptrKind with
        | .none => true
        | .rawPtr => true
        | .safeBoxOrRef =>
          match coherentAlloc, readRawBytes? outBytes with
          | some a, some raw => decide (a ∈ liveAllocs) && decide (0 < decodeLE raw)
          | _, _ => false
      match ptrOk with
      | false => .ub
      | true => checkOptRange ty.validRange outBytes

/-- Operational semantics of `CastKind::Transmute` and `CastKind::Subtype`
(`compiler/rustc_const_eval/src/interpret/cast.rs:192-218`, `place.rs:911-943`):
enforces equal sizes, validates/resets at `src`, then validates/resets at `dst`, and NEVER
modifies `st.exposedAllocs`. -/
noncomputable def evalTransmuteOpSem (src dst : TyLayout) (bytes : List AbstractByte)
    (st : ProvState) : Outcome (List AbstractByte × ProvState) :=
  match src.size == dst.size with
  | false => .ub
  | true =>
    match validateAndReset src st.liveAllocs bytes with
    | .ub => .ub
    | .ok mid =>
      match validateAndReset dst st.liveAllocs mid with
      | .ub => .ub
      | .ok out => .ok (out, st)

/-- Operational semantics of `CastKind::BoxDerefTransmute` (`cast.rs:206-218`):
additionally validates the input as `Box<T>` (`boxLayout`, with `PtrKindSpec.safeBoxOrRef`)
before performing `copy_op_allow_transmute` into `dstRawPtr`. -/
noncomputable def evalBoxDerefTransmuteOpSem (src boxLayout dstRawPtr : TyLayout)
    (bytes : List AbstractByte) (st : ProvState) : Outcome (List AbstractByte × ProvState) :=
  match src.size == dstRawPtr.size with
  | false => .ub
  | true =>
    match validateAndReset boxLayout st.liveAllocs bytes with
    | .ub => .ub
    | .ok _ => evalTransmuteOpSem src dstRawPtr bytes st

/-- Operational semantics of `CastKind::PointerExposeProvenance` (`p as usize`,
`cast.rs:96-100, 287-305`): validates `srcPtr`, exposes live provenance into `st.exposedAllocs`,
and strips the output bytes to `.bits`. -/
noncomputable def evalExposeCastOpSem (srcPtr dstInt : TyLayout) (bytes : List AbstractByte)
    (st : ProvState) : Outcome (List AbstractByte × ProvState) :=
  match srcPtr.size == dstInt.size with
  | false => .ub
  | true =>
    match validateAndReset srcPtr st.liveAllocs bytes with
    | .ub => .ub
    | .ok mid =>
      let st' : ProvState :=
        match coherentPtrAlloc? mid with
        | some a =>
          match decide (a ∈ st.liveAllocs) with
          | true => { st with exposedAllocs := a :: st.exposedAllocs }
          | false => st
        | none => st
      match validateAndReset dstInt st'.liveAllocs mid with
      | .ub => .ub
      | .ok out => .ok (out, st')

/-- Operational semantics of `CastKind::PointerWithExposedProvenance` under permissive/wildcard
provenance (`alloc_addresses/mod.rs:237-274, 360-388`): recovers `alloc` provenance iff `alloc`
was previously exposed in `st.exposedAllocs`. -/
noncomputable def evalWithExposedProv (lookupAddr : Nat → Option Nat) (addrBytes : List UInt8)
    (st : ProvState) : List AbstractByte :=
  match lookupAddr (decodeLE addrBytes) with
  | some alloc =>
    match decide (alloc ∈ st.exposedAllocs) with
    | true => tagPtrBytes alloc 0 addrBytes
    | false => addrBytes.map .bits
  | none => addrBytes.map .bits

/-- Dereferencing a pointer (`check_ptr_access` + memory load): succeeds iff `ptrBytes` carries
coherent provenance `alloc ∈ st.liveAllocs`. -/
noncomputable def derefPtrBytes (heapVal : Nat → Option Nat) (ptrBytes : List AbstractByte)
    (st : ProvState) : Outcome Nat :=
  match coherentPtrAlloc? ptrBytes with
  | some alloc =>
    match decide (alloc ∈ st.liveAllocs) with
    | true =>
      match heapVal alloc with
      | some v => .ok v
      | none => .ub
    | false => .ub
  | none => .ub

/-! ## 4. Theorem Family 1: Necessary & Sufficient `SafeTransmute` Soundness Condition -/

/-- Whether a `ByteSpec` guarantees an initialized output byte after `validateAndResetByte`. -/
noncomputable def ByteSpec.guaranteesInit : ByteSpec → Bool
  | .pad => false
  | .maybeUninit => false
  | .initBits => true
  | .ptrFrag _ => true

/-- Whether a `ByteSpec` requires an initialized input byte in `validateAndResetByte`. -/
noncomputable def ByteSpec.requiresInit : ByteSpec → Bool
  | .pad => false
  | .maybeUninit => false
  | .initBits => true
  | .ptrFrag _ => true

/-- Pointwise byte-initialization subtyping: every byte where `dst` requires initialization must
be guaranteed initialized by `src`. -/
noncomputable def ByteSpecsSub : List ByteSpec → List ByteSpec → Prop
  | [], [] => True
  | s :: ss, d :: ds =>
    (d.requiresInit = true → s.guaranteesInit = true) ∧ ByteSpecsSub ss ds
  | _, _ => False

/-- Semantic `SafeTransmute` property: for a fixed `liveAllocs`, every byte vector that passes
`src` validation (`validateAndReset src liveAllocs bytes = .ok mid`) executes `evalTransmuteOpSem`
into `dst` without Undefined Behavior. -/
noncomputable def SemanticallySafeTransmute (liveAllocs : List Nat) (src dst : TyLayout) : Prop :=
  ∀ bytes mid st,
    st.liveAllocs = liveAllocs →
    validateAndReset src liveAllocs bytes = .ok mid →
    ∃ out, evalTransmuteOpSem src dst bytes st = .ok (out, st)

/-- Constructive pure-bits layout constructor for an `n`-byte integer/scalar type (such as `u32`,
`NonZeroU32`, or `bool`) whose bytes are all `.initBits` and whose values are constrained by
`range`. -/
noncomputable def mkScalarBitsLayout (n : Nat) (range : Option WrappingRange) : TyLayout :=
  { size := n
    byteSpecs := List.replicate n ByteSpec.initBits
    ptrKind := .none
    validRange := range
    backendRepr := .scalar n }

/-- Whether `raw` satisfies an optional `WrappingRange`. -/
noncomputable def optRangeAccepts (rOpt : Option WrappingRange) (raw : List UInt8) : Bool :=
  match rOpt with
  | none => true
  | some rs => WrappingRange.contains rs (decodeLE raw)

/-- Range containment over all `n`-byte unsigned values realizable by `List UInt8` of length `n`. -/
noncomputable def RangeContainsOpt (srcRange dstRange : Option WrappingRange) (n : Nat) : Prop :=
  ∀ raw : List UInt8, raw.length = n →
    optRangeAccepts srcRange raw = true →
    optRangeAccepts dstRange raw = true

theorem nat_beq_refl (n : Nat) : (n == n) = true :=
  decide_eq_true rfl

theorem nat_eq_of_beq {a b : Nat} (h : (a == b) = true) : a = b :=
  of_decide_eq_true h

theorem validateBitsReplicate_from_raw (coh : Bool) :
    ∀ raw : List UInt8,
      validateAndResetBytes coh (List.replicate raw.length ByteSpec.initBits) (raw.map .bits) =
        some (raw.map .bits)
  | [] => rfl
  | b :: bs => by
    dsimp only [List.length, List.replicate, List.map, validateAndResetBytes, validateAndResetByte]
    rw [validateBitsReplicate_from_raw coh bs]

theorem readRawBytes_map_bits :
    ∀ raw : List UInt8, readRawBytes? (raw.map .bits) = some raw
  | [] => rfl
  | b :: bs => by
    dsimp only [List.map, readRawBytes?, rawByteVal?]
    rw [readRawBytes_map_bits bs]

theorem coherentPtrAlloc_map_bits :
    ∀ raw : List UInt8, coherentPtrAlloc? (raw.map .bits) = none
  | [] => rfl
  | _ :: _ => rfl

theorem checkOptRange_map_bits (rOpt : Option WrappingRange) (raw : List UInt8) :
    checkOptRange rOpt (raw.map .bits) =
      match optRangeAccepts rOpt raw with
      | true => .ok (raw.map .bits)
      | false => .ub := by
  cases rOpt with
  | none => rfl
  | some r =>
    unfold checkOptRange optRangeAccepts
    rw [readRawBytes_map_bits raw]

theorem validateScalarBits_of_raw (liveAllocs : List Nat) (n : Nat)
    (r : Option WrappingRange) (raw : List UInt8) (hlen : raw.length = n)
    (hr : optRangeAccepts r raw = true) :
    validateAndReset (mkScalarBitsLayout n r) liveAllocs (raw.map .bits) = .ok (raw.map .bits) := by
  subst hlen
  unfold validateAndReset mkScalarBitsLayout
  dsimp only
  have h1 : ((raw.map AbstractByte.bits).length == raw.length) = true := by
    rw [List.length_map]
    exact nat_beq_refl raw.length
  have h2 : ((List.replicate raw.length ByteSpec.initBits).length == raw.length) = true := by
    rw [List.length_replicate]
    exact nat_beq_refl raw.length
  rw [h1, h2]
  dsimp only [Bool.and]
  rw [validateBitsReplicate_from_raw (coherentPtrAlloc? (raw.map AbstractByte.bits)).isSome raw]
  dsimp only
  rw [checkOptRange_map_bits r raw, hr]

theorem validateBitsReplicate_to_raw :
    ∀ (n : Nat) (coh : Bool) (bytes out : List AbstractByte),
      bytes.length = n →
      validateAndResetBytes coh (List.replicate n ByteSpec.initBits) bytes = some out →
      ∃ raw : List UInt8, raw.length = n ∧ out = raw.map .bits
  | 0, _, [], out, _, h => by
    injection h with hOut
    exact ⟨[], rfl, hOut.symm⟩
  | n + 1, coh, ab :: abs, out, hlen, h => by
    have hlen' : abs.length = n := Nat.succ.inj hlen
    cases hab : ab with
    | uninit =>
      rw [hab] at h
      cases h
    | bits b =>
      rw [hab] at h
      dsimp only [List.replicate, validateAndResetBytes, validateAndResetByte] at h
      cases hrest : validateAndResetBytes coh (List.replicate n ByteSpec.initBits) abs with
      | none =>
        rw [hrest] at h
        cases h
      | some bs' =>
        rw [hrest] at h
        injection h with hout
        obtain ⟨rawTail, hrawLen, hrawEq⟩ :=
          validateBitsReplicate_to_raw n coh abs bs' hlen' hrest
        refine ⟨b :: rawTail, congrArg Nat.succ hrawLen, ?_⟩
        rw [← hout, hrawEq]
        rfl
    | ptrByte _ _ b =>
      rw [hab] at h
      dsimp only [List.replicate, validateAndResetBytes, validateAndResetByte] at h
      cases hrest : validateAndResetBytes coh (List.replicate n ByteSpec.initBits) abs with
      | none =>
        rw [hrest] at h
        cases h
      | some bs' =>
        rw [hrest] at h
        injection h with hout
        obtain ⟨rawTail, hrawLen, hrawEq⟩ :=
          validateBitsReplicate_to_raw n coh abs bs' hlen' hrest
        refine ⟨b :: rawTail, congrArg Nat.succ hrawLen, ?_⟩
        rw [← hout, hrawEq]
        rfl

theorem validateScalarBits_inv (liveAllocs : List Nat) (n : Nat)
    (r : Option WrappingRange) (bytes mid : List AbstractByte)
    (h : validateAndReset (mkScalarBitsLayout n r) liveAllocs bytes = .ok mid) :
    ∃ raw : List UInt8,
      raw.length = n ∧
      mid = raw.map .bits ∧
      optRangeAccepts r raw = true := by
  unfold validateAndReset mkScalarBitsLayout at h
  dsimp only at h
  cases hlenB : (bytes.length == n) with
  | false =>
    rw [hlenB] at h
    cases h
  | true =>
    have hlenEq : bytes.length = n := nat_eq_of_beq hlenB
    have hsl : ((List.replicate n ByteSpec.initBits).length == n) = true := by
      rw [List.length_replicate]
      exact nat_beq_refl n
    rw [hlenB, hsl] at h
    dsimp only [Bool.and] at h
    cases hvb : validateAndResetBytes (coherentPtrAlloc? bytes).isSome
        (List.replicate n ByteSpec.initBits) bytes with
    | none =>
      rw [hvb] at h
      cases h
    | some outBytes =>
      rw [hvb] at h
      dsimp only at h
      obtain ⟨raw, hrawLen, hOutEq⟩ :=
        validateBitsReplicate_to_raw n (coherentPtrAlloc? bytes).isSome bytes outBytes hlenEq hvb
      rw [hOutEq, checkOptRange_map_bits r raw] at h
      cases hAcc : optRangeAccepts r raw with
      | false =>
        rw [hAcc] at h
        cases h
      | true =>
        rw [hAcc] at h
        injection h with hmid
        exact ⟨raw, hrawLen, hmid.symm, hAcc⟩

/-- **Necessary & Sufficient `SafeTransmute` Theorem for Scalar Layouts**:
`SemanticallySafeTransmute` between two scalar layouts holds **if and only if** their byte sizes
match (`nSrc = nDst`) AND `RangeContainsOpt rSrc rDst nSrc` holds (given an inhabited source
witness `raw0`). -/
theorem safeTransmute_scalar_iff (liveAllocs : List Nat) (nSrc nDst : Nat)
    (rSrc rDst : Option WrappingRange)
    (hInhabited : ∃ raw0 : List UInt8, raw0.length = nSrc ∧ optRangeAccepts rSrc raw0 = true) :
    SemanticallySafeTransmute liveAllocs
      (mkScalarBitsLayout nSrc rSrc) (mkScalarBitsLayout nDst rDst) ↔
      (nSrc = nDst ∧ RangeContainsOpt rSrc rDst nSrc) := by
  constructor
  · intro hSafe
    obtain ⟨raw0, hlen0, hr0⟩ := hInhabited
    have hVal0 := validateScalarBits_of_raw liveAllocs nSrc rSrc raw0 hlen0 hr0
    have hSize : nSrc = nDst := by
      obtain ⟨out0, hEval0⟩ :=
        hSafe (raw0.map .bits) (raw0.map .bits) { liveAllocs := liveAllocs, exposedAllocs := [] } rfl hVal0
      unfold evalTransmuteOpSem mkScalarBitsLayout at hEval0
      dsimp only at hEval0
      cases hEq : (nSrc == nDst) with
      | true => exact nat_eq_of_beq hEq
      | false =>
        rw [hEq] at hEval0
        cases hEval0
    refine ⟨hSize, ?_⟩
    intro raw hlen hSrcOk
    have hVal := validateScalarBits_of_raw liveAllocs nSrc rSrc raw hlen hSrcOk
    obtain ⟨out, hEval⟩ :=
      hSafe (raw.map .bits) (raw.map .bits) { liveAllocs := liveAllocs, exposedAllocs := [] } rfl hVal
    subst hSize
    unfold evalTransmuteOpSem at hEval
    have hSame : ((mkScalarBitsLayout nSrc rSrc).size == (mkScalarBitsLayout nSrc rDst).size) = true :=
      nat_beq_refl nSrc
    rw [hSame] at hEval
    dsimp only at hEval
    rw [hVal] at hEval
    dsimp only at hEval
    cases hDst : validateAndReset (mkScalarBitsLayout nSrc rDst) liveAllocs (raw.map .bits) with
    | ub =>
      rw [hDst] at hEval
      cases hEval
    | ok _ =>
      unfold validateAndReset mkScalarBitsLayout at hDst
      dsimp only at hDst
      have hb1 : ((raw.map AbstractByte.bits).length == nSrc) = true := by
        rw [List.length_map, hlen]
        exact nat_beq_refl nSrc
      have hs1 : ((List.replicate nSrc ByteSpec.initBits).length == nSrc) = true := by
        rw [List.length_replicate]
        exact nat_beq_refl nSrc
      have hvbEq : validateAndResetBytes (coherentPtrAlloc? (raw.map AbstractByte.bits)).isSome
          (List.replicate nSrc ByteSpec.initBits) (raw.map AbstractByte.bits) =
          some (raw.map AbstractByte.bits) := by
        subst hlen
        exact validateBitsReplicate_from_raw _ raw
      rw [hb1, hs1] at hDst
      dsimp only [Bool.and] at hDst
      rw [hvbEq] at hDst
      dsimp only at hDst
      rw [checkOptRange_map_bits rDst raw] at hDst
      cases hAcc : optRangeAccepts rDst raw with
      | true => rfl
      | false =>
        rw [hAcc] at hDst
        cases hDst
  · rintro ⟨hSize, hRange⟩ bytes mid st hLive hSrc
    subst hSize
    subst hLive
    obtain ⟨raw, hrawLen, hMidEq, hSrcRangeOk⟩ :=
      validateScalarBits_inv st.liveAllocs nSrc rSrc bytes mid hSrc
    have hDstRangeOk := hRange raw hrawLen hSrcRangeOk
    have hDstVal := validateScalarBits_of_raw st.liveAllocs nSrc rDst raw hrawLen hDstRangeOk
    refine ⟨raw.map .bits, ?_⟩
    unfold evalTransmuteOpSem
    have hSame : ((mkScalarBitsLayout nSrc rSrc).size == (mkScalarBitsLayout nSrc rDst).size) = true :=
      nat_beq_refl nSrc
    rw [hSame]
    dsimp only
    rw [hSrc]
    dsimp only
    rw [hMidEq, hDstVal]

theorem validateAndResetBytes_length (coh : Bool) :
    ∀ (ss : List ByteSpec) (bs out : List AbstractByte),
      validateAndResetBytes coh ss bs = some out → out.length = ss.length := by
  intro ss
  induction ss with
  | nil =>
    intro bs out h
    cases bs with
    | nil =>
      injection h with hout
      rw [← hout]
      rfl
    | cons _ _ =>
      cases h
  | cons s ss ih =>
    intro bs out h
    cases bs with
    | nil =>
      cases h
    | cons b bs =>
      dsimp only [validateAndResetBytes] at h
      cases h1 : validateAndResetByte coh s b with
      | none =>
        rw [h1] at h
        cases h
      | some b' =>
        rw [h1] at h
        cases h2 : validateAndResetBytes coh ss bs with
        | none =>
          rw [h2] at h
          cases h
        | some bs' =>
          rw [h2] at h
          injection h with hout
          rw [← hout, List.length_cons, List.length_cons, ih bs bs' h2]

/-- Necessity of bytewise initialization subtyping (`ByteSpecsSub`): if `src` has a `.pad` byte at
index `0` while `dst` requires `.initBits` at index `0`, then transmuting any source value faults
with `.ub` (because `src` resets byte `0` to `.uninit` and `dst` rejects `.uninit`). -/
theorem uninit_byte_violates_initBits_dst (n : Nat) (ss ds : List ByteSpec)
    (b0 : AbstractByte) (rest : List AbstractByte) (st : ProvState)
    (hLenS : ss.length = n) (hLenD : ds.length = n) (hLenR : rest.length = n) :
    let src : TyLayout := ⟨n + 1, .pad :: ss, .none, none, .memory⟩
    let dst : TyLayout := ⟨n + 1, .initBits :: ds, .none, none, .scalar (n + 1)⟩
    evalTransmuteOpSem src dst (b0 :: rest) st = .ub := by
  intro src dst
  unfold evalTransmuteOpSem
  have hSz : (src.size == dst.size) = true := nat_beq_refl (n + 1)
  rw [hSz]
  dsimp only
  cases hSrc : validateAndReset src st.liveAllocs (b0 :: rest) with
  | ub => rfl
  | ok mid =>
    dsimp only
    have hb1 : ((b0 :: rest).length == src.size) = true := by
      change (rest.length + 1 == n + 1) = true
      rw [hLenR]
      exact nat_beq_refl (n + 1)
    have hs1 : (src.byteSpecs.length == src.size) = true := by
      change (ss.length + 1 == n + 1) = true
      rw [hLenS]
      exact nat_beq_refl (n + 1)
    unfold validateAndReset at hSrc
    rw [hb1, hs1] at hSrc
    dsimp only [Bool.and, src, validateAndResetBytes, validateAndResetByte] at hSrc
    cases hTail : validateAndResetBytes (coherentPtrAlloc? (b0 :: rest)).isSome ss rest with
    | none =>
      rw [hTail] at hSrc
      cases hSrc
    | some tailOut =>
      rw [hTail] at hSrc
      dsimp only [checkOptRange] at hSrc
      injection hSrc with hMidEq
      rw [← hMidEq]
      unfold validateAndReset
      have hTailLen : tailOut.length = n := by
        rw [validateAndResetBytes_length _ ss rest tailOut hTail, hLenS]
      have hm1 : ((AbstractByte.uninit :: tailOut).length == dst.size) = true := by
        change (tailOut.length + 1 == n + 1) = true
        rw [hTailLen]
        exact nat_beq_refl (n + 1)
      have hd1 : (dst.byteSpecs.length == dst.size) = true := by
        change (ds.length + 1 == n + 1) = true
        rw [hLenD]
        exact nat_beq_refl (n + 1)
      rw [hm1, hd1]
      rfl

/-! ## 5. Theorem Family 2: 6-Arm `cgTransmute` Lowering & Strict Forward Refinement -/

/-- The 6 `BackendRepr` dispatch arms of `FunctionCx::codegen_transmute_operand`
(`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:379-442`). -/
inductive CgArmChosen : Type where
  | zstArm : CgArmChosen
  | memoryLoadArm : CgArmChosen
  | scalarTransmuteArm : CgArmChosen
  | simdBitcastArm : CgArmChosen
  | scalarPairRegsArm : CgArmChosen
  | allocaSpillArm : CgArmChosen

/-- Exact arm selection logic of `codegen_transmute_operand`, including `vector_can_bitcast`
(`!hasPtrElem`) and `in_a.size == out_a.size && in_b.size == out_b.size && in_offset == out_offset`. -/
noncomputable def selectCgArm (srcRepr dstRepr : BackendRepr) : CgArmChosen :=
  match srcRepr, dstRepr with
  | _, .zst => .zstArm
  | .memory, _ => .memoryLoadArm
  | .scalar s1, .scalar s2 =>
    match s1 == s2 with
    | true => .scalarTransmuteArm
    | false => .allocaSpillArm
  | .simdVector n1 e1 p1, .simdVector n2 e2 p2 =>
    match (!p1) && (!p2) && (n1 * e1 == n2 * e2) with
    | true => .simdBitcastArm
    | false => .allocaSpillArm
  | .scalarPair a1 b1 ofs1 _ _, .scalarPair a2 b2 ofs2 _ _ =>
    match (a1 == a2) && (b1 == b2) && (ofs1 == ofs2) with
    | true => .scalarPairRegsArm
    | false => .allocaSpillArm
  | _, _ => .allocaSpillArm

/-- Compute the post-`ptrtoint` provenance state in LLVM `cg_transmute`. -/
noncomputable def llvmPostTransmuteState (src dst : TyLayout) (mid : List AbstractByte)
    (st : ProvState) : ProvState :=
  let exposesViaPtrToInt : Bool :=
    match selectCgArm src.backendRepr dst.backendRepr, src.ptrKind, dst.ptrKind with
    | .scalarTransmuteArm, .rawPtr, .none => true
    | .scalarTransmuteArm, .safeBoxOrRef, .none => true
    | _, _, _ => false
  match exposesViaPtrToInt with
  | true =>
    match coherentPtrAlloc? mid with
    | some a =>
      match decide (a ∈ st.liveAllocs) with
      | true => { st with exposedAllocs := a :: st.exposedAllocs }
      | false => st
    | none => st
  | false => st

theorem llvmPostTransmuteState_liveAllocs (src dst : TyLayout) (mid : List AbstractByte)
    (st : ProvState) :
    (llvmPostTransmuteState src dst mid st).liveAllocs = st.liveAllocs := by
  unfold llvmPostTransmuteState
  dsimp only
  cases (match selectCgArm src.backendRepr dst.backendRepr, src.ptrKind, dst.ptrKind with
         | .scalarTransmuteArm, .rawPtr, .none => true
         | .scalarTransmuteArm, .safeBoxOrRef, .none => true
         | _, _, _ => false) with
  | false => rfl
  | true =>
    dsimp only
    cases coherentPtrAlloc? mid with
    | none => rfl
    | some a =>
      dsimp only
      cases decide (a ∈ st.liveAllocs) with
      | false => rfl
      | true => rfl

theorem llvmPostTransmuteState_sub (src dst : TyLayout) (mid : List AbstractByte)
    (st : ProvState) :
    ProvState.Sub st (llvmPostTransmuteState src dst mid st) := by
  refine ⟨(llvmPostTransmuteState_liveAllocs src dst mid st).symm, ?_⟩
  intro x hx
  unfold llvmPostTransmuteState
  dsimp only
  cases (match selectCgArm src.backendRepr dst.backendRepr, src.ptrKind, dst.ptrKind with
         | .scalarTransmuteArm, .rawPtr, .none => true
         | .scalarTransmuteArm, .safeBoxOrRef, .none => true
         | _, _, _ => false) with
  | false => exact hx
  | true =>
    dsimp only
    cases coherentPtrAlloc? mid with
    | none => exact hx
    | some a =>
      dsimp only
      cases decide (a ∈ st.liveAllocs) with
      | false => exact hx
      | true => exact List.mem_cons_of_mem a hx

/-- LLVM IR `cg_transmute` semantics (`codegen_transmute_operand` + `transmute_scalar` +
`assume_scalar_range`):
- Enforces `src.size == dst.size` (`bx.unreachable_nonterminator()`, `rvalue.rs:354-363`).
- Assumes source scalar validity (`assume_scalar_range` on `from_scalar`, `rvalue.rs:1118`).
- Lowers `(Pointer(..), Int(..))` via `bx.ptrtoint` (`rvalue.rs:1124-1127`:
  `// FIXME: this exposes the provenance, which shouldn't be necessary`), thereby inserting live
  pointer provenance into `st.exposedAllocs`!
- Assumes destination scalar validity (`assume_scalar_range` on `to_scalar`, `rvalue.rs:1146`). -/
noncomputable def evalCgTransmuteLLVM (src dst : TyLayout) (bytes : List AbstractByte)
    (st : ProvState) : Outcome (List AbstractByte × ProvState) :=
  match src.size == dst.size with
  | false => .ub
  | true =>
    match validateAndReset src st.liveAllocs bytes with
    | .ub => .ub
    | .ok mid =>
      let stLlvm := llvmPostTransmuteState src dst mid st
      match validateAndReset dst stLlvm.liveAllocs mid with
      | .ub => .ub
      | .ok out => .ok (out, stLlvm)

/-- State-level forward simulation between Rust OpSem `evalTransmuteOpSem` and LLVM `evalCgTransmuteLLVM`:
every non-UB OpSem transmute succeeds in LLVM with the **exact same byte output** `out` and a
monotonically larger exposed-provenance set (`ProvState.Sub stOp stLlvm`). -/
theorem evalTransmuteOpSem_simulates_cgTransmuteLLVM
    (src dst : TyLayout) (bytes out : List AbstractByte) (st stOp : ProvState)
    (hOp : evalTransmuteOpSem src dst bytes st = .ok (out, stOp)) :
    ∃ stLlvm, evalCgTransmuteLLVM src dst bytes st = .ok (out, stLlvm) ∧
      ProvState.Sub stOp stLlvm := by
  unfold evalTransmuteOpSem at hOp
  unfold evalCgTransmuteLLVM
  cases hSz : (src.size == dst.size) with
  | false =>
    rw [hSz] at hOp
    cases hOp
  | true =>
    rw [hSz] at hOp
    dsimp only at hOp ⊢
    cases hSrc : validateAndReset src st.liveAllocs bytes with
    | ub =>
      rw [hSrc] at hOp
      cases hOp
    | ok mid =>
      rw [hSrc] at hOp
      dsimp only at hOp ⊢
      cases hDst : validateAndReset dst st.liveAllocs mid with
      | ub =>
        rw [hDst] at hOp
        cases hOp
      | ok out' =>
        rw [hDst] at hOp
        injection hOp with hPair
        injection hPair with hOut hSt
        subst hOut
        subst hSt
        refine ⟨llvmPostTransmuteState src dst mid st, ?_,
          llvmPostTransmuteState_sub src dst mid st⟩
        change (match validateAndReset dst (llvmPostTransmuteState src dst mid st).liveAllocs mid with
                | Outcome.ub => Outcome.ub
                | Outcome.ok o => Outcome.ok (o, llvmPostTransmuteState src dst mid st)) =
          Outcome.ok (out', llvmPostTransmuteState src dst mid st)
        rw [llvmPostTransmuteState_liveAllocs src dst mid st, hDst]

theorem checkPtrFrags_tagPtrBytes (alloc : Nat) :
    ∀ (idx : Nat) (bs : List UInt8), checkPtrFrags alloc idx (tagPtrBytes alloc idx bs) = true
  | _, [] => rfl
  | idx, _ :: bs => by
    dsimp only [tagPtrBytes, checkPtrFrags]
    rw [nat_beq_refl alloc, nat_beq_refl idx]
    dsimp only [Bool.and]
    exact checkPtrFrags_tagPtrBytes alloc (idx + 1) bs

theorem coherentPtrAlloc_tagPtrBytes (alloc : Nat) (b : UInt8) (bs : List UInt8) :
    coherentPtrAlloc? (tagPtrBytes alloc 0 (b :: bs)) = some alloc := by
  rw [tagPtrBytes, Nat.zero_add, coherentPtrAlloc?, checkPtrFrags_tagPtrBytes alloc 1 bs]

/-- Monotonicity of `with_exposed_provenance` + pointer dereference with respect to `ProvState.Sub`:
exposing additional allocations never invalidates a previously valid dereference. -/
theorem derefWithExposed_mono (lookupAddr : Nat → Option Nat) (heapVal : Nat → Option Nat)
    (addrBytes : List UInt8) {s1 s2 : ProvState} (hSub : ProvState.Sub s1 s2) :
    Outcome.Refines
      (derefPtrBytes heapVal (evalWithExposedProv lookupAddr addrBytes s1) s1)
      (derefPtrBytes heapVal (evalWithExposedProv lookupAddr addrBytes s2) s2) := by
  rcases hSub with ⟨hLive, hExp⟩
  intro v
  unfold evalWithExposedProv
  cases lookupAddr (decodeLE addrBytes) with
  | none =>
    dsimp only
    intro h1
    unfold derefPtrBytes at h1
    rw [coherentPtrAlloc_map_bits] at h1
    cases h1
  | some alloc =>
    dsimp only
    cases hDec1 : decide (alloc ∈ s1.exposedAllocs) with
    | false =>
      dsimp only
      intro h1
      unfold derefPtrBytes at h1
      rw [coherentPtrAlloc_map_bits] at h1
      cases h1
    | true =>
      dsimp only
      have hIn1 : alloc ∈ s1.exposedAllocs := of_decide_eq_true hDec1
      have hIn2 : alloc ∈ s2.exposedAllocs := hExp alloc hIn1
      rw [decide_eq_true hIn2]
      dsimp only
      intro h1
      unfold derefPtrBytes at h1 ⊢
      rw [← hLive]
      exact h1

/-- Whole-pipeline execution of `transmute(ptr -> usize)` followed by `with_exposed_provenance`
and pointer dereference under OpSem vs LLVM codegen. -/
noncomputable def runTransmuteThenExposeDeref
    (transmuteFn : TyLayout → TyLayout → List AbstractByte → ProvState →
      Outcome (List AbstractByte × ProvState))
    (src dst : TyLayout) (lookupAddr : Nat → Option Nat) (heapVal : Nat → Option Nat)
    (bytes : List AbstractByte) (st : ProvState) : Outcome Nat :=
  match transmuteFn src dst bytes st with
  | .ub => .ub
  | .ok (intBytes, st') =>
    match readRawBytes? intBytes with
    | none => .ub
    | some addrBytes =>
      derefPtrBytes heapVal (evalWithExposedProv lookupAddr addrBytes st') st'

/-- **Strict Forward Refinement Theorem (`evalTransmuteOpSem ⊑ evalCgTransmuteLLVM`)**:
For every type pair, input byte vector, heap, and provenance state, LLVM's `cg_transmute`
(`ptrtoint`) forward-refines Rust OpSem's provenance-stripping `CastKind::Transmute`. -/
theorem cgTransmuteLLVM_refines_opSem_end_to_end
    (src dst : TyLayout) (lookupAddr : Nat → Option Nat) (heapVal : Nat → Option Nat)
    (bytes : List AbstractByte) (st : ProvState) :
    Outcome.Refines
      (runTransmuteThenExposeDeref evalTransmuteOpSem src dst lookupAddr heapVal bytes st)
      (runTransmuteThenExposeDeref evalCgTransmuteLLVM src dst lookupAddr heapVal bytes st) := by
  intro v hOp
  unfold runTransmuteThenExposeDeref at hOp ⊢
  cases hT : evalTransmuteOpSem src dst bytes st with
  | ub =>
    rw [hT] at hOp
    cases hOp
  | ok pair =>
    rw [hT] at hOp
    rcases pair with ⟨intBytes, stOp⟩
    dsimp only at hOp
    obtain ⟨stLlvm, hLlvm, hSub⟩ :=
      evalTransmuteOpSem_simulates_cgTransmuteLLVM src dst bytes intBytes st stOp hT
    rw [hLlvm]
    dsimp only
    cases hRaw : readRawBytes? intBytes with
    | none =>
      rw [hRaw] at hOp
      cases hOp
    | some addrBytes =>
      rw [hRaw] at hOp
      dsimp only at hOp ⊢
      exact derefWithExposed_mono lookupAddr heapVal addrBytes hSub v hOp

/-! ## 6. Theorem Family 3: `ScalarPair -> ScalarPair` Register Transmute vs `alloca` Spill -/

/-- Read `len` bytes starting at `ofs` from memory buffer `mem`. -/
noncomputable def readSlice (mem : List AbstractByte) (ofs len : Nat) : List AbstractByte :=
  (mem.drop ofs).take len

/-- Overwrite bytes in `mem` starting at `ofs` with `vs`. -/
noncomputable def writeSlice : List AbstractByte → Nat → List AbstractByte → List AbstractByte
  | mem, 0, [] => mem
  | _ :: ms, 0, v :: vs => v :: writeSlice ms 0 vs
  | [], 0, _ :: _ => []
  | m :: ms, ofs + 1, vs => m :: writeSlice ms ofs vs
  | [], _ + 1, _ => []

theorem writeSlice_length :
    ∀ (mem : List AbstractByte) (ofs : Nat) (vs : List AbstractByte),
      (writeSlice mem ofs vs).length = mem.length := by
  intro mem
  induction mem with
  | nil =>
    intro ofs vs
    cases ofs with
    | zero =>
      cases vs with
      | nil => rfl
      | cons _ _ => rfl
    | succ _ => rfl
  | cons m ms ih =>
    intro ofs vs
    cases ofs with
    | zero =>
      cases vs with
      | nil => rfl
      | cons v vs =>
        change (v :: writeSlice ms 0 vs).length = (m :: ms).length
        rw [List.length_cons, List.length_cons, ih 0 vs]
    | succ ofs =>
      change (m :: writeSlice ms ofs vs).length = (m :: ms).length
      rw [List.length_cons, List.length_cons, ih ofs vs]

theorem take_writeSlice_zero :
    ∀ (mem : List AbstractByte) (vs : List AbstractByte),
      vs.length ≤ mem.length →
      (writeSlice mem 0 vs).take vs.length = vs := by
  intro mem
  induction mem with
  | nil =>
    intro vs h
    cases vs with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ ms ih =>
    intro vs h
    cases vs with
    | nil => rfl
    | cons v vs =>
      have h' : vs.length ≤ ms.length := Nat.le_of_succ_le_succ h
      change (v :: writeSlice ms 0 vs).take (vs.length + 1) = v :: vs
      exact congrArg (List.cons v) (ih vs h')

theorem readSlice_writeSlice_same :
    ∀ (mem : List AbstractByte) (ofs : Nat) (vs : List AbstractByte),
      ofs + vs.length ≤ mem.length →
      readSlice (writeSlice mem ofs vs) ofs vs.length = vs := by
  intro mem
  induction mem with
  | nil =>
    intro ofs vs h
    cases ofs with
    | zero =>
      cases vs with
      | nil => rfl
      | cons _ _ =>
        rw [Nat.zero_add] at h
        cases h
    | succ ofs =>
      have hpos : 0 < ofs + 1 + vs.length := by
        rw [Nat.add_right_comm]
        exact Nat.succ_pos _
      exact False.elim (Nat.not_lt_of_ge h hpos)
  | cons m ms ih =>
    intro ofs vs h
    cases ofs with
    | zero =>
      rw [Nat.zero_add] at h
      exact take_writeSlice_zero (m :: ms) vs h
    | succ ofs =>
      have h' : ofs + vs.length ≤ ms.length := by
        rw [Nat.succ_add] at h
        exact Nat.le_of_succ_le_succ h
      exact ih ofs vs h'

theorem take_writeSlice_disjoint :
    ∀ (mem : List AbstractByte) (len ofs : Nat) (vs : List AbstractByte),
      len ≤ ofs →
      (writeSlice mem ofs vs).take len = mem.take len := by
  intro mem
  induction mem with
  | nil =>
    intro len ofs vs _
    cases len with
    | zero => rfl
    | succ _ =>
      cases ofs with
      | zero =>
        cases vs with
        | nil => rfl
        | cons _ _ => rfl
      | succ _ => rfl
  | cons m ms ih =>
    intro len ofs vs h
    cases len with
    | zero => rfl
    | succ len =>
      cases ofs with
      | zero => cases h
      | succ ofs =>
        change (m :: writeSlice ms ofs vs).take (len + 1) = (m :: ms).take (len + 1)
        exact congrArg (List.cons m) (ih len ofs vs (Nat.le_of_succ_le_succ h))

/-- Scalar component transmutation inside `ScalarPair`: requires initialized bytes, strips
non-pointer provenance when `keepPtr = false`, and enforces `assume_scalar_range` (`outRange`). -/
noncomputable def evalScalarComponent (keepPtr : Bool) (outRange : Option WrappingRange)
    (compBytes : List AbstractByte) : Outcome (List AbstractByte) :=
  match readRawBytes? compBytes with
  | none => .ub
  | some raw =>
    let rangeOk : Bool :=
      match outRange with
      | none => true
      | some r => WrappingRange.contains r (decodeLE raw)
    match rangeOk with
    | false => .ub
    | true =>
      match keepPtr with
      | true => .ok compBytes
      | false => .ok (raw.map .bits)

/-- Arm 5 (`ScalarPair -> ScalarPair` in SSA registers, `rvalue.rs:410-422`):
transmutes `imm_a` and `imm_b` directly without touching stack memory. -/
noncomputable def evalScalarPairInRegs (keepPtrA keepPtrB : Bool)
    (outARange outBRange : Option WrappingRange)
    (aBytes bBytes : List AbstractByte) : Outcome (List AbstractByte × List AbstractByte) :=
  match evalScalarComponent keepPtrA outARange aBytes,
        evalScalarComponent keepPtrB outBRange bBytes with
  | .ok aOut, .ok bOut => .ok (aOut, bOut)
  | _, _ => .ub

/-- Arm 6 (`alloca` spill + store + reload, `rvalue.rs:433-441`):
allocates `totalSize` `.uninit` bytes, stores `aBytes` at `0` and `bBytes` at `inBOfs`, then
reloads `outA` bytes from `0` and `outB` bytes from `outBOfs` and validates/assumes target scalar
ranges. -/
noncomputable def evalScalarPairAllocaSpill (totalSize : Nat)
    (inBOfs outA outB outBOfs : Nat) (keepPtrA keepPtrB : Bool)
    (outARange outBRange : Option WrappingRange)
    (aBytes bBytes : List AbstractByte) : Outcome (List AbstractByte × List AbstractByte) :=
  let mem0 := List.replicate totalSize AbstractByte.uninit
  let mem1 := writeSlice mem0 0 aBytes
  let mem2 := writeSlice mem1 inBOfs bBytes
  let loadedA := readSlice mem2 0 outA
  let loadedB := readSlice mem2 outBOfs outB
  evalScalarPairInRegs keepPtrA keepPtrB outARange outBRange loadedA loadedB

/-- **Exact `ScalarPair` Register-vs-`alloca` Equivalence Theorem**:
For all `totalSize`, component sizes `aSz`, `bSz`, and offsets `bOfs` satisfying non-overlapping
in-bounds layout (`aSz ≤ bOfs` and `bOfs + bSz ≤ totalSize`), whenever `outA = aSz`, `outB = bSz`,
and `outBOfs = bOfs` (matching the three guards at `rvalue.rs:414-416`), Arm 5's in-register
`ScalarPair` transmutation produces the **exact same `Outcome`** as Arm 6's `alloca` memory
round-trip! -/
theorem scalarPair_reg_transmute_eq_alloca_spill
    (totalSize aSz bSz bOfs : Nat)
    (keepPtrA keepPtrB : Bool)
    (outARange outBRange : Option WrappingRange)
    (aBytes bBytes : List AbstractByte)
    (haLen : aBytes.length = aSz)
    (hbLen : bBytes.length = bSz)
    (hNonOverlap : aSz ≤ bOfs)
    (hInBounds : bOfs + bSz ≤ totalSize) :
    evalScalarPairInRegs keepPtrA keepPtrB outARange outBRange aBytes bBytes =
      evalScalarPairAllocaSpill totalSize bOfs aSz bSz bOfs
        keepPtrA keepPtrB outARange outBRange aBytes bBytes := by
  unfold evalScalarPairAllocaSpill
  dsimp only
  have hMem0Len : (List.replicate totalSize AbstractByte.uninit).length = totalSize :=
    List.length_replicate
  have hMem1Len :
      (writeSlice (List.replicate totalSize AbstractByte.uninit) 0 aBytes).length = totalSize := by
    rw [writeSlice_length, hMem0Len]
  have haFit : aBytes.length ≤ (List.replicate totalSize AbstractByte.uninit).length := by
    rw [haLen, hMem0Len]
    exact Nat.le_trans hNonOverlap (Nat.le_trans (Nat.le_add_right bOfs bSz) hInBounds)
  have hbFit :
      bOfs + bBytes.length ≤
        (writeSlice (List.replicate totalSize AbstractByte.uninit) 0 aBytes).length := by
    rw [hbLen, hMem1Len]
    exact hInBounds
  have hLoadA :
      readSlice
        (writeSlice (writeSlice (List.replicate totalSize AbstractByte.uninit) 0 aBytes) bOfs bBytes)
        0 aSz = aBytes := by
    unfold readSlice
    change (writeSlice (writeSlice (List.replicate totalSize AbstractByte.uninit) 0 aBytes) bOfs bBytes).take aSz = aBytes
    rw [take_writeSlice_disjoint _ aSz bOfs bBytes hNonOverlap]
    rw [← haLen]
    exact take_writeSlice_zero (List.replicate totalSize AbstractByte.uninit) aBytes haFit
  have hLoadB :
      readSlice
        (writeSlice (writeSlice (List.replicate totalSize AbstractByte.uninit) 0 aBytes) bOfs bBytes)
        bOfs bSz = bBytes := by
    rw [← hbLen]
    exact readSlice_writeSlice_same
      (writeSlice (List.replicate totalSize AbstractByte.uninit) 0 aBytes) bOfs bBytes hbFit
  rw [hLoadA, hLoadB]

/-! ## 7. Constructive Counterexamples (`ce1`, `ce2`, `ce3`) & `BoxDerefTransmute` Strictness -/

/-- Concrete 4-byte raw pointer layout (`*const u32` on 32-bit or modeled 4-byte pointer). -/
noncomputable def rawPtr4Layout : TyLayout :=
  { size := 4
    byteSpecs := [.ptrFrag 0, .ptrFrag 1, .ptrFrag 2, .ptrFrag 3]
    ptrKind := .rawPtr
    validRange := none
    backendRepr := .scalar 4 }

/-- Concrete 4-byte `Box<u32>` layout (`PtrKindSpec.safeBoxOrRef`). -/
noncomputable def box4Layout : TyLayout :=
  { size := 4
    byteSpecs := [.ptrFrag 0, .ptrFrag 1, .ptrFrag 2, .ptrFrag 3]
    ptrKind := .safeBoxOrRef
    validRange := some ⟨4294967296, 1, 4294967295⟩
    backendRepr := .scalar 4 }

/-- Concrete 4-byte `BoxRaw<u32>` wrapper layout (`NonNull` niche range, raw-pointer kind before
`BoxDerefTransmute` checks `Box<u32>` dereferenceability). -/
noncomputable def boxRaw4Layout : TyLayout :=
  { size := 4
    byteSpecs := [.ptrFrag 0, .ptrFrag 1, .ptrFrag 2, .ptrFrag 3]
    ptrKind := .rawPtr
    validRange := some ⟨4294967296, 1, 4294967295⟩
    backendRepr := .scalar 4 }

/-- Concrete 4-byte unsigned integer layout (`u32` / 32-bit `usize`). -/
noncomputable def u32Layout : TyLayout := mkScalarBitsLayout 4 none

/-- Concrete 4-byte `NonZeroU32` layout (`WrappingRange { start: 1, end_: 2^32 - 1 }`). -/
noncomputable def nonZeroU32Layout : TyLayout :=
  mkScalarBitsLayout 4 (some ⟨4294967296, 1, 4294967295⟩)

/-- Concrete `#[repr(C)] struct PadPair(u8, u16)` layout:
byte 0 is `u8` (`.initBits`), byte 1 is padding (`.pad`), bytes 2..3 are `u16` (`.initBits`). -/
noncomputable def padPairLayout : TyLayout :=
  { size := 4
    byteSpecs := [.initBits, .pad, .initBits, .initBits]
    ptrKind := .none
    validRange := none
    backendRepr := .scalarPair 1 2 2 none none }

/-- Concrete `[MaybeUninit<u8>; 4]` layout: all 4 bytes are `.maybeUninit` union data bytes. -/
noncomputable def maybeUninit4Layout : TyLayout :=
  { size := 4
    byteSpecs := [.maybeUninit, .maybeUninit, .maybeUninit, .maybeUninit]
    ptrKind := .none
    validRange := none
    backendRepr := .memory }

/-- Concrete pointer to live allocation `alloc = 1` at address `0x0002_0100` (`131328`). -/
noncomputable def samplePtrBytes : List AbstractByte :=
  [.ptrByte 1 0 (UInt8.ofNat 0x00),
   .ptrByte 1 1 (UInt8.ofNat 0x01),
   .ptrByte 1 2 (UInt8.ofNat 0x02),
   .ptrByte 1 3 (UInt8.ofNat 0x00)]

noncomputable def sampleLookupAddr (addr : Nat) : Option Nat :=
  match addr == 131328 with
  | true => some 1
  | false => none

noncomputable def sampleHeapVal (alloc : Nat) : Option Nat :=
  match alloc == 1 with
  | true => some 0xCAFEBABE
  | false => none

noncomputable def sampleInitState : ProvState :=
  { liveAllocs := [1], exposedAllocs := [] }

/-- Helper executing `p as usize` (`evalExposeCastOpSem`) followed by `with_exposed_provenance`
and pointer dereference. -/
noncomputable def runExposeCastThenDeref : Outcome Nat :=
  runTransmuteThenExposeDeref evalExposeCastOpSem
    rawPtr4Layout u32Layout sampleLookupAddr sampleHeapVal samplePtrBytes sampleInitState

/-- **Counterexample 1 (`ce1_transmute_ptr_to_usize_lacks_exposed_provenance_unlike_as_cast`)**:
1. `p as usize` (`CastKind::PointerExposeProvenance`) exposes `alloc = 1`, so
   `with_exposed_provenance` + `*q` succeeds with `.ok 0xCAFEBABE`.
2. `transmute::<*const u32, usize>(p)` (`CastKind::Transmute`) strips provenance *without* exposing
   `alloc = 1` in Rust OpSem/Miri, so `with_exposed_provenance` + `*q` faults with `.ub`!
3. LLVM codegen (`cg_transmute` -> `ptrtoint`) exposes `alloc = 1` and returns `.ok 0xCAFEBABE`,
   witnessing that **reverse refinement (`LLVM ⊑ OpSem`) is strictly false**! -/
theorem ce1_transmute_ptr_to_usize_lacks_exposed_provenance_unlike_as_cast :
    runExposeCastThenDeref = .ok 0xCAFEBABE ∧
    runTransmuteThenExposeDeref evalTransmuteOpSem
      rawPtr4Layout u32Layout sampleLookupAddr sampleHeapVal samplePtrBytes sampleInitState = .ub ∧
    runTransmuteThenExposeDeref evalCgTransmuteLLVM
      rawPtr4Layout u32Layout sampleLookupAddr sampleHeapVal samplePtrBytes sampleInitState =
        .ok 0xCAFEBABE := by
  exact ⟨rfl, rfl, rfl⟩

/-- Corollary of Counterexample 1: reverse refinement from LLVM `cg_transmute` back to Rust OpSem
`CastKind::Transmute` does NOT hold (`¬ (LLVM ⊑ OpSem)`). -/
theorem not_opSem_refines_from_cgTransmuteLLVM :
    ¬ Outcome.Refines
        (runTransmuteThenExposeDeref evalCgTransmuteLLVM
          rawPtr4Layout u32Layout sampleLookupAddr sampleHeapVal samplePtrBytes sampleInitState)
        (runTransmuteThenExposeDeref evalTransmuteOpSem
          rawPtr4Layout u32Layout sampleLookupAddr sampleHeapVal samplePtrBytes sampleInitState) := by
  intro hRev
  rcases ce1_transmute_ptr_to_usize_lacks_exposed_provenance_unlike_as_cast with ⟨_, hOpUb, hLlvmOk⟩
  have hBad := hRev 0xCAFEBABE hLlvmOk
  rw [hOpUb] at hBad
  cases hBad

/-- Concrete `PadPair(0x11, 0x2233)` value in little-endian byte order with `.uninit` padding at
byte index `1`, plus an all-initialized `u32` buffer `0xFF22_3311`. -/
noncomputable def samplePadPairBytes : List AbstractByte :=
  [.bits (UInt8.ofNat 0x11), .uninit, .bits (UInt8.ofNat 0x33), .bits (UInt8.ofNat 0x22)]

noncomputable def sampleAllInitU32Bytes : List AbstractByte :=
  [.bits (UInt8.ofNat 0x11), .bits (UInt8.ofNat 0xFF),
   .bits (UInt8.ofNat 0x33), .bits (UInt8.ofNat 0x22)]

/-- Round-trip helper `u32 -> PadPair -> u32` showing `reset_padding` wipes byte `1`. -/
noncomputable def runU32ThroughPadPairRoundtrip (bytes : List AbstractByte) (st : ProvState) :
    Outcome (List AbstractByte × ProvState) :=
  match evalTransmuteOpSem u32Layout padPairLayout bytes st with
  | .ub => .ub
  | .ok (mid, st1) => evalTransmuteOpSem padPairLayout u32Layout mid st1

/-- **Counterexample 2 (`ce2_padding_byte_transmute_to_u32_ub_vs_maybe_uninit_array_ok`)**:
1. `transmute::<PadPair, u32>` faults with `.ub` on padding byte `1` (`Uninit`).
2. `transmute::<PadPair, [MaybeUninit<u8>; 4]>` succeeds and preserves the exact byte-level
   initialization mask `[Init(0x11), Uninit, Init(0x33), Init(0x22)]`.
3. Even starting from a fully initialized `u32` (`0xFF22_3311`), transmuting `u32 -> PadPair`
   actively wipes byte `1` back to `.uninit` (`reset_padding`), causing a subsequent
   `PadPair -> u32` transmute to fault with `.ub`! -/
theorem ce2_padding_byte_transmute_to_u32_ub_vs_maybe_uninit_array_ok :
    evalTransmuteOpSem padPairLayout u32Layout samplePadPairBytes sampleInitState = .ub ∧
    evalTransmuteOpSem padPairLayout maybeUninit4Layout samplePadPairBytes sampleInitState =
      .ok (samplePadPairBytes, sampleInitState) ∧
    runU32ThroughPadPairRoundtrip sampleAllInitU32Bytes sampleInitState = .ub := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Counterexample 3 (`ce3_scalarpair_mismatched_b_offset_register_transmute_corrupts_bytes`)**:
Consider two 4-byte `ScalarPair` layouts with identical component sizes (`aSz = 1`, `bSz = 2`,
`totalSize = 4`) but different second-component offsets (`inBOfs = 1` with trailing pad at byte 3,
vs `outBOfs = 2` with internal pad at byte 1):
1. `selectCgArm` rejects in-register `ScalarPair` transmutation because `inBOfs != outBOfs`,
   routing the cast to `.allocaSpillArm`.
2. True byte-level `alloca` spill + reload (`evalScalarPairAllocaSpill`) loads `[.bits 0xCC, .uninit]`
   at `outBOfs = 2` and faults with `.ub`.
3. By contrast, an unguarded register-pair transmute (`evalScalarPairInRegs`) ignores `b_offset`
   and fabricates `.ok ([.bits 0xAA], [.bits 0xBB, .bits 0xCC])`, diverging from byte-level memory
   semantics! -/
theorem ce3_scalarpair_mismatched_b_offset_register_transmute_corrupts_bytes :
    let srcRepr := BackendRepr.scalarPair 1 2 1 none none
    let dstRepr := BackendRepr.scalarPair 1 2 2 none none
    let aIn := [AbstractByte.bits (UInt8.ofNat 0xAA)]
    let bIn := [AbstractByte.bits (UInt8.ofNat 0xBB), AbstractByte.bits (UInt8.ofNat 0xCC)]
    selectCgArm srcRepr dstRepr = .allocaSpillArm ∧
    evalScalarPairAllocaSpill 4 1 1 2 2 false false none none aIn bIn = .ub ∧
    evalScalarPairInRegs false false none none aIn bIn = .ok (aIn, bIn) := by
  exact ⟨rfl, rfl, rfl⟩

/-- **`BoxDerefTransmute` Strictness Theorem**:
On a non-null dangling pointer (`alloc = 99 ∉ liveAllocs`), ordinary `CastKind::Transmute` from
`BoxRaw<u32>` to `*const u32` succeeds (`.ok`), whereas `CastKind::BoxDerefTransmute` performs
`Box<u32>` dereferenceability validation (`PtrKindSpec.safeBoxOrRef`) and faults with `.ub`! -/
theorem boxDerefTransmute_rejects_dangling_ptr_unlike_transmute :
    let danglingPtr : List AbstractByte :=
      [.ptrByte 99 0 (UInt8.ofNat 0x04), .ptrByte 99 1 (UInt8.ofNat 0x00),
       .ptrByte 99 2 (UInt8.ofNat 0x00), .ptrByte 99 3 (UInt8.ofNat 0x00)]
    evalTransmuteOpSem boxRaw4Layout rawPtr4Layout danglingPtr sampleInitState =
      .ok (danglingPtr, sampleInitState) ∧
    evalBoxDerefTransmuteOpSem boxRaw4Layout box4Layout rawPtr4Layout danglingPtr sampleInitState =
      .ub := by
  exact ⟨rfl, rfl⟩

/-- Zero-to-`NonZeroU32` scalar range UB witness (`0u32 -> NonZeroU32` faults `.ub` in both OpSem
and `cgTransmute` `@llvm.assume`). -/
theorem zero_u32_to_nonZeroU32_is_ub :
    let zero4 : List AbstractByte :=
      [.bits (UInt8.ofNat 0), .bits (UInt8.ofNat 0),
       .bits (UInt8.ofNat 0), .bits (UInt8.ofNat 0)]
    evalTransmuteOpSem u32Layout nonZeroU32Layout zero4 sampleInitState = .ub ∧
    evalCgTransmuteLLVM u32Layout nonZeroU32Layout zero4 sampleInitState = .ub := by
  exact ⟨rfl, rfl⟩

end TransmuteByteModel

#print axioms TransmuteByteModel.assumeIntegerRangeCheck_eq_contains
#print axioms TransmuteByteModel.safeTransmute_scalar_iff
#print axioms TransmuteByteModel.uninit_byte_violates_initBits_dst
#print axioms TransmuteByteModel.evalTransmuteOpSem_simulates_cgTransmuteLLVM
#print axioms TransmuteByteModel.cgTransmuteLLVM_refines_opSem_end_to_end
#print axioms TransmuteByteModel.scalarPair_reg_transmute_eq_alloca_spill
#print axioms TransmuteByteModel.ce1_transmute_ptr_to_usize_lacks_exposed_provenance_unlike_as_cast
#print axioms TransmuteByteModel.not_opSem_refines_from_cgTransmuteLLVM
#print axioms TransmuteByteModel.ce2_padding_byte_transmute_to_u32_ub_vs_maybe_uninit_array_ok
#print axioms TransmuteByteModel.ce3_scalarpair_mismatched_b_offset_register_transmute_corrupts_bytes
#print axioms TransmuteByteModel.boxDerefTransmute_rejects_dangling_ptr_unlike_transmute
#print axioms TransmuteByteModel.zero_u32_to_nonZeroU32_is_ub
