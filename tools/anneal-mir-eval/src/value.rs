// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Concrete runtime values, fault classifications, and MIR type predicates
//! matching `Trusted.MirModel` and `Trusted.MirSemantics.Enum`.

use alloc::{collections::BTreeSet, string::String, vec, vec::Vec};
use core::fmt;

use serde::{Deserialize, Serialize};

use crate::ir::{EnumTagRepr, EnumTy, IntTy, IntWidth, Mutability, Ty};

/// Operational fault classification matching `Trusted.MirSemantics.FaultKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FaultKind {
    /// Modeled Rust Undefined Behavior.
    Undefined,
    /// Unmodeled MIR construct, type, invariant violation, or profile boundary.
    Unsupported,
}

impl fmt::Display for FaultKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Undefined => f.write_str("undefined"),
            Self::Unsupported => f.write_str("unsupported"),
        }
    }
}

/// Classification of an Undefined Behavior witness for replay gating.
///
/// Distinguishes concrete Rust/Miri Undefined Behavior from conservative
/// over-approximations documented in `Trusted.MirSemantics` so replay gates
/// never silently skip or misclassify model-only failures as confirmed Miri UB.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum WitnessClass {
    /// Concrete Rust/Miri Undefined Behavior expected to reproduce under Miri.
    ReplayableMiriUb,
    /// Conservative model-only or synthetic check that Miri does not
    /// necessarily reject as UB; must be reported as `model_only_unreplayed`.
    ModelOnlyUnreplayed,
}

impl fmt::Display for WitnessClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReplayableMiriUb => f.write_str("replayable_miri_ub"),
            Self::ModelOnlyUnreplayed => f.write_str("model_only_unreplayed"),
        }
    }
}

/// Specific Undefined Behavior cause recorded on [`FaultDetail`] for replay
/// classification and diagnostics.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UbClass {
    /// Integer division or remainder by zero.
    DivByZero,
    /// Signed integer `MIN / -1` or `MIN % -1` overflow.
    SignedDivOverflow,
    /// Unchecked arithmetic (`AddUnchecked`/`SubUnchecked`/`MulUnchecked`,
    /// `unchecked_*`) overflow or underflow.
    UncheckedArithOverflow,
    /// Unchecked shift amount outside `0..bit_width`.
    UncheckedShiftOverflow,
    /// Reached `Terminator::Unreachable`.
    UnreachableExecuted,
    /// Diverging call (`target = None`) returned to caller.
    DivergingCallReturned,
    /// Read or write of a storage-dead local.
    DeadLocalAccess,
    /// Read of an uninitialized local immediate slot.
    UninitLocalRead,
    /// Read of uninitialized memory bytes into a value requiring init bytes.
    UninitMemoryRead,
    /// Invalid scalar bit pattern decoded from memory (bool/char/enum).
    InvalidMemoryValue,
    /// Non-zero-sized access through a null or provenance-free pointer.
    NullOrNoProvPtrAccess,
    /// Non-zero-sized access or deallocation on an unknown or dead allocation.
    DanglingOrUnknownAllocAccess,
    /// Non-zero-sized memory access out of allocation bounds.
    OutOfBoundsMemoryAccess,
    /// Memory access violating ABI alignment.
    MisalignedMemoryAccess,
    /// Non-zero-sized write to an immutable allocation or via shared pointer.
    WriteToReadOnlyMemory,
    /// `BinOp::Offset` or `CoreCallOp::PtrAdd` overflow or out-of-bounds.
    PtrOffsetOverflowOrOob,
    /// `slice::get_unchecked` range out of bounds (`start > end || end > len`).
    SliceGetUncheckedOutOfBounds,
    /// Non-zero-sized `BackendRepr::Memory` or padded `Assign` copy with
    /// overlapping source and destination places (`copy_nonoverlapping` UB).
    OverlappingMemoryCopy,
    /// Invalid reference produced (null, unaligned, dangling, OOB, read-only).
    InvalidReferenceProduced,
    /// Returned references violate pairwise `&mut` span disjointness.
    OverlappingMutRefsReturned,
    /// Non-ZST reference to callee stack storage escaped across return.
    StackRefEscaped,
    /// Conservative model-only: zero-byte offset on a dead or OOB provenance
    /// pointer (accepted by `rustc`/`Miri` `check_and_deref_ptr`).
    ZeroOffsetDeadOrOobPtr,
    /// Conservative model-only: zero-sized access via a null raw pointer
    /// (follows `core::ptr` docs; stricter than the Reference's ZST exception).
    ZstNullRawPtrDeref,
    /// Conservative model-only: zero-sized reference with provenance into a
    /// dead or OOB allocation (zero-size ranges never dangle in Rust/Miri).
    ZstProvenanceDeadOrOob,
    /// Conservative model-only: zero-sized `&mut` into a shared allocation
    /// (skipped by `rustc` CTFE validity checks).
    ZstMutRefImmutableAlloc,
    /// Conservative model-only: reference pointing to uninitialized or invalid
    /// pointee bytes (debated upstream; not recursively checked by Miri).
    RefPointeeUninitOrInvalid,
    /// Conservative model-only: second read after `Operand::Move`
    /// deinitialization (currently a no-op for locals in `rustc`/Miri).
    MoveDeinitLocalRead,
    /// Conservative model-only: `-Zub-checks` `NullPtrDeref` or
    /// `MisalignedPtrDeref` assert (panics at runtime with ub-checks enabled
    /// rather than direct UB).
    CheckPtrAssertOnly,
    /// Conservative model-only: returning a reference to a zero-sized callee
    /// stack local (never dangles in Rust/Miri).
    ZstStackRefEscape,
    /// Conservative model-only: allocation-relative alignment failure
    /// (`alloc.align < access_align`), which requires Miri
    /// `-Zmiri-symbolic-alignment-check` and may succeed under concrete base
    /// addresses in default Miri.
    SymbolicAllocAlignment,
    /// Conservative model-only: overlapping `Assign` copy on a non-`Memory`
    /// type that does not invoke `copy_nonoverlapping` in Miri — specifically
    /// an immediate (non-address-taken) padded `ScalarPair` local (e.g.
    /// `(u32, bool)`) where `rustc_const_eval`/`lean-miri` take the immediate
    /// fast path, or an unmodeled type conservatively classified as
    /// `MemoryCopy`.
    ConservativeOverlappingAssignCopy,
    /// Entry boundary violation: caller passed an invalid or aliasing reference
    /// outside `ValidEntryArgsV2` before entering the body.
    EntryInvalidRefArg,
    /// Synthetic MIR invalid constant literal or `SwitchInt` branch tag.
    SyntheticInvalidConstOrSwitch,
}

impl UbClass {
    /// Whether this UB class is directly replayable under Miri or is a
    /// documented conservative model-only over-approximation.
    pub const fn witness_class(self) -> WitnessClass {
        match self {
            Self::DivByZero
            | Self::SignedDivOverflow
            | Self::UncheckedArithOverflow
            | Self::UncheckedShiftOverflow
            | Self::UnreachableExecuted
            | Self::DeadLocalAccess
            | Self::UninitLocalRead
            | Self::UninitMemoryRead
            | Self::InvalidMemoryValue
            | Self::NullOrNoProvPtrAccess
            | Self::DanglingOrUnknownAllocAccess
            | Self::OutOfBoundsMemoryAccess
            | Self::MisalignedMemoryAccess
            | Self::WriteToReadOnlyMemory
            | Self::PtrOffsetOverflowOrOob
            | Self::SliceGetUncheckedOutOfBounds
            | Self::OverlappingMemoryCopy
            | Self::InvalidReferenceProduced
            | Self::OverlappingMutRefsReturned
            | Self::StackRefEscaped => WitnessClass::ReplayableMiriUb,

            Self::ZeroOffsetDeadOrOobPtr
            | Self::ZstNullRawPtrDeref
            | Self::ZstProvenanceDeadOrOob
            | Self::ZstMutRefImmutableAlloc
            | Self::RefPointeeUninitOrInvalid
            | Self::MoveDeinitLocalRead
            | Self::CheckPtrAssertOnly
            | Self::ZstStackRefEscape
            | Self::SymbolicAllocAlignment
            | Self::ConservativeOverlappingAssignCopy
            | Self::DivergingCallReturned
            | Self::EntryInvalidRefArg
            | Self::SyntheticInvalidConstOrSwitch => WitnessClass::ModelOnlyUnreplayed,
        }
    }

    /// Diagnostic explanation for `ModelOnlyUnreplayed` classes (`None` for
    /// directly replayable Rust/Miri UB).
    pub const fn model_only_note(self) -> Option<&'static str> {
        match self {
            Self::ZeroOffsetDeadOrOobPtr => Some(
                "conservative Trusted.MirSemantics check: zero-byte offset on a dead or \
                 out-of-bounds provenance pointer is accepted by rustc/Miri check_and_deref_ptr",
            ),
            Self::ZstNullRawPtrDeref => Some(
                "conservative Trusted.MirSemantics check: zero-sized access on a null raw pointer \
                 follows core::ptr non-null docs rather than the Reference's ZST exception",
            ),
            Self::ZstProvenanceDeadOrOob => Some(
                "conservative Trusted.MirSemantics check: zero-sized reference with provenance \
                 into a dead or out-of-bounds allocation never dangles in Rust/Miri",
            ),
            Self::ZstMutRefImmutableAlloc => Some(
                "conservative Trusted.MirSemantics check: zero-sized &mut into a shared \
                 allocation is skipped by rustc's CTFE validity check",
            ),
            Self::RefPointeeUninitOrInvalid => Some(
                "conservative Trusted.MirSemantics check: recursive reference pointee validity is \
                 debated upstream and not enforced recursively by default in Miri",
            ),
            Self::MoveDeinitLocalRead => Some(
                "conservative Trusted.MirSemantics check: Move deinitializes locals in Anneal \
                 whereas rustc/Miri currently leaves moved locals readable",
            ),
            Self::CheckPtrAssertOnly => Some(
                "conservative Trusted.MirSemantics check: -Zub-checks pointer asserts panic at \
                 runtime with ub-checks enabled instead of directly invoking language UB",
            ),
            Self::ZstStackRefEscape => Some(
                "conservative Trusted.MirSemantics check: returning a reference to a zero-sized \
                 callee stack local never dangles in Rust/Miri",
            ),
            Self::SymbolicAllocAlignment => Some(
                "conservative Trusted.MirSemantics check: allocation-relative alignment \
                 (alloc.align < access_align) requires Miri -Zmiri-symbolic-alignment-check and \
                 may succeed under concrete base addresses in default Miri",
            ),
            Self::ConservativeOverlappingAssignCopy => Some(
                "conservative Trusted.MirSemantics check: overlapping Assign copy on an \
                 immediate (non-address-taken) padded ScalarPair local (or an unmodeled \
                 type) does not take Miri's copy_nonoverlapping memory-copy path",
            ),
            Self::DivergingCallReturned => Some(
                "synthetic MIR artifact: a diverging call terminator (target = None) returning \
                 to its caller cannot arise from standalone safe/unsafe Rust source replay",
            ),
            Self::EntryInvalidRefArg => Some(
                "entry boundary violation: caller passed an invalid or aliasing reference outside \
                 ValidEntryArgsV2 before executing the body",
            ),
            Self::SyntheticInvalidConstOrSwitch => Some(
                "synthetic MIR artifact: invalid constant literal or SwitchInt branch tag cannot \
                 be emitted by normal Rust source replay",
            ),
            _ => None,
        }
    }
}

/// Fault outcome enriched with diagnostic explanation and replay classification
/// while keeping [`FaultKind`] primary for semantic comparisons.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaultDetail {
    pub kind: FaultKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ub_class: Option<UbClass>,
    pub reason: String,
}

impl FaultDetail {
    /// Construct an unclassified `Undefined` fault (fail-closed classified as
    /// [`WitnessClass::ModelOnlyUnreplayed`] for replay gating).
    pub fn undefined(reason: impl Into<String>) -> Self {
        Self { kind: FaultKind::Undefined, ub_class: None, reason: reason.into() }
    }

    /// Construct a classified `Undefined` fault with an explicit [`UbClass`].
    pub fn undefined_classified(ub_class: UbClass, reason: impl Into<String>) -> Self {
        Self { kind: FaultKind::Undefined, ub_class: Some(ub_class), reason: reason.into() }
    }

    /// Construct an `Unsupported` fault.
    pub fn unsupported(reason: impl Into<String>) -> Self {
        Self { kind: FaultKind::Unsupported, ub_class: None, reason: reason.into() }
    }

    /// Replay witness class when `self.kind == FaultKind::Undefined`.
    ///
    /// Unclassified `Undefined` faults fail closed to
    /// [`WitnessClass::ModelOnlyUnreplayed`] so replay gates never assume a
    /// witness is replayable without an explicit classification.
    pub const fn witness_class(&self) -> Option<WitnessClass> {
        match self.kind {
            FaultKind::Undefined => match self.ub_class {
                Some(class) => Some(class.witness_class()),
                None => Some(WitnessClass::ModelOnlyUnreplayed),
            },
            FaultKind::Unsupported => None,
        }
    }

    /// Explanatory note for model-only witnesses (`None` for replayable UB or
    /// `Unsupported` faults).
    pub const fn model_only_note(&self) -> Option<&'static str> {
        match (self.kind, self.ub_class) {
            (FaultKind::Undefined, Some(class)) => class.model_only_note(),
            (FaultKind::Undefined, None) => {
                Some("unclassified model UB witness defaults fail-closed to model_only_unreplayed")
            }
            (FaultKind::Unsupported, _) => None,
        }
    }
}

impl fmt::Display for FaultDetail {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.kind, self.reason)
    }
}

/// Canonical scalar value with explicit width, signedness, and 128-bit payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ScalarVal {
    pub width: IntWidth,
    pub signed: bool,
    #[serde(
        serialize_with = "crate::ir::serialize_u128_decimal",
        deserialize_with = "crate::ir::deserialize_u128_decimal"
    )]
    pub bits: u128,
}

impl ScalarVal {
    /// Construct a scalar value truncating `bits` to `width`.
    pub const fn new(width: IntWidth, signed: bool, bits: u128) -> Self {
        Self { width, signed, bits: bits & width.mask() }
    }

    /// Construct a scalar value from raw bits without truncating (useful for
    /// negative `wf()` validation tests).
    pub const fn from_raw_untruncated(width: IntWidth, signed: bool, bits: u128) -> Self {
        Self { width, signed, bits }
    }

    /// Whether `bits` fits inside `width` bits (`ScalarVal.wf`).
    pub const fn wf(self) -> bool {
        (self.bits & self.width.mask()) == self.bits
    }

    /// Mask raw bits to `self.width`.
    pub const fn truncated_bits(self) -> u128 {
        self.bits & self.width.mask()
    }

    /// Sign-extended `i128` interpretation when `self.signed == true`.
    pub const fn to_signed_i128(self) -> i128 {
        let masked = self.truncated_bits();
        let shift = 128 - self.width.bits();
        ((masked << shift) as i128) >> shift
    }
}

/// Canonical pointer/reference value (`alloc_id` provenance + byte offset).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PtrVal {
    pub alloc_id: Option<u64>,
    pub offset_bytes: u64,
    pub width: IntWidth,
}

/// Abstract memory byte: uninitialized or initialized byte with optional
/// provenance allocation id.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AllocByte {
    Uninit,
    Init { byte: u8, prov: Option<u64> },
}

/// Runtime value of `core::cmp::Ordering` matching `OrderingVal`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OrderingVal {
    Less,
    Equal,
    Greater,
}

impl OrderingVal {
    /// Canonical `#[repr(i8)]` tag bit pattern (`255`, `0`, `1`).
    pub const fn tag_bits(self) -> u128 {
        match self {
            Self::Less => 255,
            Self::Equal => 0,
            Self::Greater => 1,
        }
    }

    /// Decode an 8-bit `Ordering` tag pattern, or `None` on invalid tags.
    pub const fn from_tag_bits(bits: u128) -> Option<Self> {
        match bits {
            255 => Some(Self::Less),
            0 => Some(Self::Equal),
            1 => Some(Self::Greater),
            _ => None,
        }
    }
}

/// Canonical boundary and runtime value matching `Trusted.MirModel.Val`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub enum Val {
    Scalar(ScalarVal),
    Ptr(PtrVal),
    SlicePtr { ptr: PtrVal, len: u64 },
    Bool(bool),
    Char(char),
    Ordering(OrderingVal),
    Unit,
    EnumVal { ty: EnumTy, variant: usize },
    Tuple(Vec<Val>),
    RangeTo(u64),
    RangeFrom(u64),
    Bytes(Vec<AllocByte>),
}

impl Val {
    pub const fn u8(v: u8) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I8, false, v as u128))
    }

    pub const fn u16(v: u16) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I16, false, v as u128))
    }

    pub const fn u32(v: u32) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I32, false, v as u128))
    }

    pub const fn u64(v: u64) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I64, false, v as u128))
    }

    pub const fn u128(v: u128) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I128, false, v))
    }

    pub const fn usize_val(v: u64) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::Isize, false, v as u128))
    }

    pub const fn i8(v: i8) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I8, true, (v as i128) as u128))
    }

    pub const fn i16(v: i16) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I16, true, (v as i128) as u128))
    }

    pub const fn i32(v: i32) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I32, true, (v as i128) as u128))
    }

    pub const fn i64(v: i64) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I64, true, (v as i128) as u128))
    }

    pub const fn i128(v: i128) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::I128, true, v as u128))
    }

    pub const fn isize_val(v: i64) -> Self {
        Self::Scalar(ScalarVal::new(IntWidth::Isize, true, (v as i128) as u128))
    }

    /// Construct a wide slice pointer `(ptr, len)` value.
    pub const fn slice_ptr(ptr: PtrVal, len: u64) -> Self {
        Self::SlicePtr { ptr, len }
    }

    /// Construct a `core::ops::RangeTo<usize>` value (`..end`).
    pub const fn range_to(end: u64) -> Self {
        Self::RangeTo(end)
    }

    /// Construct a `core::ops::RangeFrom<usize>` value (`start..`).
    pub const fn range_from(start: u64) -> Self {
        Self::RangeFrom(start)
    }

    /// Construct an `(T, bool)` overflow pair runtime tuple.
    pub fn overflow_pair(sv: ScalarVal, overflowed: bool) -> Self {
        Self::Tuple(vec![Self::Scalar(sv), Self::Bool(overflowed)])
    }
}

/// Recover discriminant bits from raw tag bits following `rustc`'s
/// `TagEncoding::Direct` sign/zero-extension rule.
pub const fn tag_bits_to_discr_bits(tag: IntTy, discr_width: IntWidth, raw_tag: u128) -> u128 {
    let masked_tag = raw_tag & tag.width.mask();
    let extended = if tag.signed {
        let shift = 128 - tag.width.bits();
        (((masked_tag << shift) as i128) >> shift) as u128
    } else {
        masked_tag
    };
    extended & discr_width.mask()
}

/// Check `Trusted.MirSemantics.enumAdmitted` invariants on a fieldless enum
/// descriptor.
pub fn enum_admitted(ety: &EnumTy) -> bool {
    if ety.discriminants.is_empty() {
        return false;
    }
    if u64::try_from(ety.discriminants.len()).unwrap_or(u64::MAX) >= (1u64 << 32) {
        return false;
    }
    let discr_mask = ety.discr_width.mask();
    let mut seen = BTreeSet::new();
    for &d in &ety.discriminants {
        if d > discr_mask || !seen.insert(d) {
            return false;
        }
    }
    match ety.tag_repr {
        EnumTagRepr::ZeroSized => ety.discriminants.len() == 1,
        EnumTagRepr::Scalar(tag) => ety
            .discriminants
            .iter()
            .all(|&d| tag_bits_to_discr_bits(tag, ety.discr_width, d & tag.width.mask()) == d),
    }
}

/// Whether `ety` is an admitted 1-variant 0-byte ZST enum.
pub fn is_zst_enum_ty(ety: &EnumTy) -> bool {
    matches!(ety.tag_repr, EnumTagRepr::ZeroSized) && enum_admitted(ety)
}

/// Resolve a discriminant bit pattern to its 0-based declaration variant index.
pub fn find_discr_variant(discr_bits: u128, discriminants: &[u128]) -> Option<usize> {
    discriminants.iter().position(|&d| d == discr_bits)
}

/// Whether `bits` is a valid Unicode scalar value (`0x0000..=0xD7FF` or
/// `0xE000..=0x10FFFF`).
pub const fn is_unicode_scalar(bits: u128) -> bool {
    bits <= 0x10_FFFF && !(0xD800 <= bits && bits <= 0xDFFF)
}

/// Intrinsic well-formed Profile v1 type of a runtime [`Val`] (`Val.ty?`).
pub fn val_ty(val: &Val) -> Option<Ty> {
    match val {
        Val::Scalar(sv) => sv.wf().then_some(Ty::Int(IntTy { width: sv.width, signed: sv.signed })),
        Val::Bool(_) => Some(Ty::Bool),
        Val::Char(_) => Some(Ty::Char),
        Val::Ordering(_) => Some(Ty::Ordering),
        Val::Unit => Some(Ty::Unit),
        Val::EnumVal { ty, variant } => {
            (enum_admitted(ty) && *variant < ty.discriminants.len()).then(|| Ty::Enum(ty.clone()))
        }
        Val::Tuple(fields) if fields.len() == 2 => match (&fields[0], &fields[1]) {
            (Val::Scalar(sv), Val::Bool(_)) if sv.wf() => {
                Some(Ty::OverflowPair(IntTy { width: sv.width, signed: sv.signed }))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Check that runtime value `val` is a well-formed instance of `ty`,
/// matching `Trusted.MirSemantics.checkVal` (Profile v1) and `checkValV2`
/// (Profile v2).
pub fn check_val(val: &Val, ty: &Ty, enable_profile_v2: bool) -> bool {
    if !enable_profile_v2 {
        return val_ty(val).is_some_and(|inferred| inferred.structural_eq(ty));
    }
    match (val, ty) {
        (Val::Scalar(sv), Ty::Int(ity)) => {
            sv.wf() && sv.width == ity.width && sv.signed == ity.signed
        }
        (Val::Bool(_), Ty::Bool)
        | (Val::Char(_), Ty::Char)
        | (Val::Ordering(_), Ty::Ordering)
        | (Val::Unit, Ty::Unit) => true,
        (Val::EnumVal { ty: v_ety, variant }, Ty::Enum(t_ety)) => {
            v_ety == t_ety && enum_admitted(v_ety) && *variant < v_ety.discriminants.len()
        }
        (Val::Ptr(p), Ty::RawPtr { pointee, .. } | Ty::Ref { pointee, .. }) => {
            !pointee.is_unsized() && p.width == IntWidth::Isize
        }
        (Val::SlicePtr { ptr, .. }, Ty::Ref { mutability: Mutability::Shared, pointee })
            if **pointee == Ty::Str =>
        {
            ptr.width == IntWidth::Isize
        }
        (Val::SlicePtr { ptr, .. }, Ty::RawPtr { pointee, .. } | Ty::Ref { pointee, .. }) => {
            matches!(pointee.as_ref(), Ty::Slice { .. }) && ptr.width == IntWidth::Isize
        }
        (Val::RangeTo(_), Ty::RangeTo { elem }) | (Val::RangeFrom(_), Ty::RangeFrom { elem }) => {
            elem.is_usize()
        }
        (Val::Tuple(vals), Ty::Tuple { fields }) if vals.len() == fields.len() => {
            vals.iter().zip(fields.iter()).all(|(v, elem_ty)| check_val(v, elem_ty, true))
        }
        (Val::Tuple(vals), Ty::OverflowPair(ity)) if vals.len() == 2 => {
            check_val(&vals[0], &Ty::Int(*ity), true) && check_val(&vals[1], &Ty::Bool, true)
        }
        _ => false,
    }
}

/// Check whether `args` matches `param_tys` pairwise under [`check_val`].
pub fn check_args_match(args: &[Val], param_tys: &[Ty], enable_profile_v2: bool) -> bool {
    args.len() == param_tys.len()
        && args.iter().zip(param_tys.iter()).all(|(v, ty)| check_val(v, ty, enable_profile_v2))
}

/// Whether `ty` belongs to the Profile v1 local type fragment, matching
/// `Trusted.MirSemantics.isSupportedScalarOrUnitTy`.
pub fn is_supported_v1_local_ty(ty: &Ty) -> bool {
    match ty {
        Ty::Bool | Ty::Int(_) | Ty::Char | Ty::Ordering | Ty::Unit | Ty::Never => true,
        Ty::Enum(ety) => enum_admitted(ety),
        Ty::OverflowPair(_) => true,
        Ty::Tuple { .. } => ty.as_overflow_pair().is_some(),
        _ => false,
    }
}

/// Whether `ty` belongs to the Profile v2 local type fragment, matching
/// `Trusted.MirSemantics.isSupportedV2LocalTy`.
pub fn is_supported_v2_local_ty(ty: &Ty) -> bool {
    match ty {
        Ty::Bool | Ty::Int(_) | Ty::Char | Ty::Ordering | Ty::Unit | Ty::Never => true,
        Ty::Enum(ety) => enum_admitted(ety),
        Ty::OverflowPair(_) => true,
        Ty::Tuple { fields } => fields.iter().all(is_supported_v2_local_ty),
        Ty::Ref { mutability: Mutability::Shared, pointee } if **pointee == Ty::Str => true,
        Ty::Ref { pointee, .. } | Ty::RawPtr { pointee, .. } => match pointee.as_ref() {
            Ty::Slice { elem } => matches!(elem.as_ref(), Ty::Int(_)),
            other => other.as_overflow_pair().is_none() && is_supported_v1_local_ty(other),
        },
        Ty::RangeTo { elem } | Ty::RangeFrom { elem } => elem.is_usize(),
        _ => false,
    }
}

/// Whether `ty` is executable in locals under the selected profile.
pub fn is_supported_local_ty(ty: &Ty, enable_profile_v2: bool) -> bool {
    if enable_profile_v2 { is_supported_v2_local_ty(ty) } else { is_supported_v1_local_ty(ty) }
}

/// Whether `ty` is primitive-readable (`bool`, `int`, `char`, overflow pair).
/// Notice `Enum` and `Ordering` are NOT primitive-readable.
pub fn is_primitive_readable_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Int(_) | Ty::Char) || ty.as_overflow_pair().is_some()
}

/// Whether `ty` is an integer-like source for `CastKind::IntToInt`.
pub fn is_int_like_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Int(_) | Ty::Char)
}
