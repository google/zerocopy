// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Canonical outcome algebra, caller-frame preservation laws, and 4-way
//! differential mismatch taxonomy.

use std::{
    collections::BTreeMap,
    fmt::{self, Write as _},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::trace_observer::{ObservableEvent, ObservableSpine};

/// Integer width and signedness matching `Trusted.MirAst.IntWidth × Bool`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IntKind {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
}

impl IntKind {
    pub fn rust_name(self) -> &'static str {
        match self {
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::U128 => "u128",
            Self::Usize => "usize",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::I128 => "i128",
            Self::Isize => "isize",
        }
    }

    pub fn lean_width(self) -> &'static str {
        match self {
            Self::U8 | Self::I8 => ".i8",
            Self::U16 | Self::I16 => ".i16",
            Self::U32 | Self::I32 => ".i32",
            Self::U64 | Self::I64 => ".i64",
            Self::U128 | Self::I128 => ".i128",
            Self::Usize | Self::Isize => ".isize",
        }
    }

    pub fn is_signed(self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::I128 | Self::Isize)
    }

    pub fn bit_width(self) -> u32 {
        match self {
            Self::U8 | Self::I8 => 8,
            Self::U16 | Self::I16 => 16,
            Self::U32 | Self::I32 => 32,
            Self::U64 | Self::I64 | Self::Usize | Self::Isize => 64,
            Self::U128 | Self::I128 => 128,
        }
    }

    pub fn byte_width(self) -> usize {
        (self.bit_width() / 8) as usize
    }

    pub fn mask_bits(self, raw: u128) -> u128 {
        match self.bit_width() {
            128 => raw,
            w => raw & ((1u128 << w) - 1),
        }
    }

    pub fn to_lean_scalar(self, bits: u128) -> String {
        let masked = self.mask_bits(bits);
        let signed = if self.is_signed() { "true" } else { "false" };
        format!("⟨{}, {}, BitVec.ofNat 128 {}⟩", self.lean_width(), signed, masked)
    }

    pub fn format_rust_literal(self, bits: u128) -> String {
        let masked = self.mask_bits(bits);
        match self {
            Self::U8 => format!("{masked}u8"),
            Self::U16 => format!("{masked}u16"),
            Self::U32 => format!("{masked}u32"),
            Self::U64 => format!("{masked}u64"),
            Self::U128 => format!("{masked}u128"),
            Self::Usize => format!("{masked}usize"),
            Self::I8 => format!("({masked}u8 as i8)"),
            Self::I16 => format!("({masked}u16 as i16)"),
            Self::I32 => format!("({masked}u32 as i32)"),
            Self::I64 => format!("({masked}u64 as i64)"),
            Self::I128 => format!("({masked}u128 as i128)"),
            Self::Isize => format!("({masked}usize as isize)"),
        }
    }

    pub fn to_mir_eval_arg(self, bits: u128) -> String {
        let masked = self.mask_bits(bits);
        match self {
            Self::U8 => format!("u8:{masked}"),
            Self::U16 => format!("u16:{masked}"),
            Self::U32 => format!("u32:{masked}"),
            Self::U64 => format!("u64:{masked}"),
            Self::U128 => format!("u128:{masked}"),
            Self::Usize => format!("usize:{masked}"),
            Self::I8 => format!("i8:{}", masked as u8 as i8),
            Self::I16 => format!("i16:{}", masked as u16 as i16),
            Self::I32 => format!("i32:{}", masked as u32 as i32),
            Self::I64 => format!("i64:{}", masked as u64 as i64),
            Self::I128 => format!("i128:{}", masked as i128),
            Self::Isize => format!("isize:{}", masked as u64 as i64),
        }
    }

    pub fn from_width_signed(width: &str, signed: bool) -> Option<Self> {
        match (width, signed) {
            ("i8", false) => Some(Self::U8),
            ("i8", true) => Some(Self::I8),
            ("i16", false) => Some(Self::U16),
            ("i16", true) => Some(Self::I16),
            ("i32", false) => Some(Self::U32),
            ("i32", true) => Some(Self::I32),
            ("i64", false) => Some(Self::U64),
            ("i64", true) => Some(Self::I64),
            ("i128", false) => Some(Self::U128),
            ("i128", true) => Some(Self::I128),
            ("isize", false) => Some(Self::Usize),
            ("isize", true) => Some(Self::Isize),
            _ => None,
        }
    }
}

/// Mirror of `core::cmp::Ordering` / `Trusted.MirSemantics.OrderingVal`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OrderingVal {
    Less,
    Equal,
    Greater,
}

impl OrderingVal {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Less => "less",
            Self::Equal => "equal",
            Self::Greater => "greater",
        }
    }

    pub fn to_lean_val(self) -> &'static str {
        match self {
            Self::Less => ".ordering .less",
            Self::Equal => ".ordering .equal",
            Self::Greater => ".ordering .greater",
        }
    }

    pub fn to_rust_expr(self) -> &'static str {
        match self {
            Self::Less => "core::cmp::Ordering::Less",
            Self::Equal => "core::cmp::Ordering::Equal",
            Self::Greater => "core::cmp::Ordering::Greater",
        }
    }
}

mod u128_as_string {
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S: Serializer>(val: &u128, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&val.to_string())
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<u128, D::Error> {
        let s = String::deserialize(deserializer)?;
        s.parse::<u128>().map_err(serde::de::Error::custom)
    }
}

/// Canonical boundary value exchanged between Rust, Miri, Lean, and `mir-eval`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "val_kind", rename_all = "snake_case")]
pub enum TraceVal {
    Scalar {
        kind: IntKind,
        #[serde(with = "u128_as_string")]
        bits: u128,
    },
    Bool {
        value: bool,
    },
    Char {
        scalar: u32,
    },
    Ordering {
        value: OrderingVal,
    },
    Unit,
    Enum {
        type_name: String,
        variant_name: String,
        variant_index: usize,
        #[serde(with = "u128_as_string")]
        discriminant: u128,
        #[serde(default)]
        tag_bytes: Option<usize>,
    },
    Tuple {
        fields: Vec<TraceVal>,
    },
    PaddedBytes {
        type_name: String,
        bytes: Vec<Option<u8>>,
    },
}

impl TraceVal {
    pub fn u32(v: u32) -> Self {
        Self::Scalar { kind: IntKind::U32, bits: u128::from(v) }
    }

    pub fn i32(v: i32) -> Self {
        Self::Scalar { kind: IntKind::I32, bits: u128::from(v as u32) }
    }

    pub fn u16(v: u16) -> Self {
        Self::Scalar { kind: IntKind::U16, bits: u128::from(v) }
    }

    pub fn u8(v: u8) -> Self {
        Self::Scalar { kind: IntKind::U8, bits: u128::from(v) }
    }

    pub fn usize_val(v: usize) -> Self {
        Self::Scalar { kind: IntKind::Usize, bits: v as u128 }
    }

    pub fn bool_val(value: bool) -> Self {
        Self::Bool { value }
    }

    /// Encode this [`TraceVal`] into canonical layout-aware boundary bytes
    /// (`Some(byte)` vs `None` padding), matching `capture_value_bytes` and
    /// `ITreeDriver.encodeBoundaryValBytes`.
    pub fn encode_boundary_bytes(&self) -> Vec<Option<u8>> {
        match self {
            Self::Scalar { kind, bits } => {
                let masked = kind.mask_bits(*bits);
                let le = masked.to_le_bytes();
                le[..kind.byte_width()].iter().copied().map(Some).collect()
            }
            Self::Bool { value } => vec![Some(u8::from(*value))],
            Self::Char { scalar } => scalar.to_le_bytes().into_iter().map(Some).collect(),
            Self::Ordering { value } => {
                let b: i8 = match value {
                    OrderingVal::Less => -1,
                    OrderingVal::Equal => 0,
                    OrderingVal::Greater => 1,
                };
                vec![Some(b as u8)]
            }
            Self::Unit => Vec::new(),
            Self::Enum { discriminant, tag_bytes, .. } => {
                let width = tag_bytes.unwrap_or(1).min(16);
                let le = discriminant.to_le_bytes();
                le[..width].iter().copied().map(Some).collect()
            }
            Self::Tuple { fields } => fields.iter().flat_map(Self::encode_boundary_bytes).collect(),
            Self::PaddedBytes { bytes, .. } => bytes.clone(),
        }
    }

    /// Compare two `TraceVal`s with canonical bit-masking and padding-mask
    /// semantics (`None` padding offsets never trigger spurious inequality).
    pub fn semantically_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Scalar { kind: k1, bits: b1 }, Self::Scalar { kind: k2, bits: b2 }) => {
                k1 == k2 && k1.mask_bits(*b1) == k2.mask_bits(*b2)
            }
            (Self::Bool { value: a }, Self::Bool { value: b }) => a == b,
            (Self::Char { scalar: a }, Self::Char { scalar: b }) => a == b,
            (Self::Ordering { value: a }, Self::Ordering { value: b }) => a == b,
            (Self::Unit, Self::Unit) => true,
            (
                Self::Enum { variant_index: i1, discriminant: d1, .. },
                Self::Enum { variant_index: i2, discriminant: d2, .. },
            ) => i1 == i2 && d1 == d2,
            (Self::Tuple { fields: f1 }, Self::Tuple { fields: f2 }) => {
                f1.len() == f2.len() && f1.iter().zip(f2.iter()).all(|(a, b)| a.semantically_eq(b))
            }
            (Self::PaddedBytes { bytes: b1, .. }, Self::PaddedBytes { bytes: b2, .. }) => {
                b1.len() == b2.len()
                    && b1.iter().zip(b2.iter()).all(|(a, b)| match (a, b) {
                        (Some(x), Some(y)) => x == y,
                        (None, None) => true,
                        _ => false,
                    })
            }
            _ => false,
        }
    }
}

/// Canonical terminal outcome of an execution authority.
///
/// On terminating runs (`Returned`, `Unwound`, `Aborted`), `mem_digest` is the
/// 64-character SHA-256 hex digest of `boundary_slots` (the entry argument
/// byte encodings followed by the post-execution terminal boundary slot:
/// `[0x10, ...ret_bytes]` on `Returned`, `[0x20]` on `Unwound`, or `[0x30]` on
/// `Aborted`; for value-only single-body `anneal-mir-eval` runs whose JSON
/// omits `boundary_slots`, `mir_eval_adapter` hashes the post-execution
/// terminal slot parsed strictly from `mir_eval`'s own JSON output).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "outcome", rename_all = "snake_case")]
pub enum TerminalOutcome {
    /// Normal return with boundary value and SHA-256 entry+post-state digest.
    Returned { ret: TraceVal, mem_digest: String },
    /// Unwound via panic propagation out of the root frame.
    Unwound { mem_digest: String },
    /// Aborted immediately via `std::process::abort()` / scheduled abort.
    Aborted { mem_digest: String },
    /// Reached deterministic step-fuel limit without terminating or faulting.
    Diverged { fuel: u64 },
    /// Detected Undefined Behavior (`FaultKind.undefined` or Miri UB).
    FaultUb { detail: String },
    /// Capture or strict single-body evaluator conservatively refused / faulted
    /// `.unsupported` on an unmodeled MIR feature.
    CaptureRefused { reason: String },
}

impl TerminalOutcome {
    pub fn is_accepting(&self) -> bool {
        matches!(
            self,
            Self::Returned { .. }
                | Self::Unwound { .. }
                | Self::Aborted { .. }
                | Self::Diverged { .. }
        )
    }

    pub fn kind_tag(&self) -> &'static str {
        match self {
            Self::Returned { .. } => "returned",
            Self::Unwound { .. } => "unwound",
            Self::Aborted { .. } => "aborted",
            Self::Diverged { .. } => "diverged",
            Self::FaultUb { .. } => "fault_ub",
            Self::CaptureRefused { .. } => "capture_refused",
        }
    }

    pub fn semantically_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Returned { ret: r1, mem_digest: m1 },
                Self::Returned { ret: r2, mem_digest: m2 },
            ) => r1.semantically_eq(r2) && m1 == m2,
            (Self::Unwound { mem_digest: m1 }, Self::Unwound { mem_digest: m2 }) => m1 == m2,
            (Self::Aborted { mem_digest: m1 }, Self::Aborted { mem_digest: m2 }) => m1 == m2,
            (Self::Diverged { fuel: f1 }, Self::Diverged { fuel: f2 }) => f1 == f2,
            (Self::FaultUb { detail: d1 }, Self::FaultUb { detail: d2 }) => {
                ub_fault_causes_compatible(d1, d2)
            }
            (Self::CaptureRefused { .. }, Self::CaptureRefused { .. }) => true,
            _ => false,
        }
    }

    /// Post-execution terminal boundary slot (`[0x10, ...ret_bytes]` on
    /// `Returned`, `[0x20]` on `Unwound`, `[0x30]` on `Aborted`).
    pub fn post_state_slot(&self) -> Option<Vec<Option<u8>>> {
        match self {
            Self::Returned { ret, .. } => {
                let rb = ret.encode_boundary_bytes();
                let mut slot = Vec::with_capacity(1 + rb.len());
                slot.push(Some(0x10));
                slot.extend(rb);
                Some(slot)
            }
            Self::Unwound { .. } => Some(vec![Some(0x20)]),
            Self::Aborted { .. } => Some(vec![Some(0x30)]),
            Self::Diverged { .. } | Self::FaultUb { .. } | Self::CaptureRefused { .. } => None,
        }
    }

    /// Compare `self` (full entry+post-state authority) against `other`
    /// (value-only `anneal-mir-eval` authority whose JSON omitted entry
    /// `boundary_slots`, so `other.mem_digest` hashes only its post-state).
    pub fn semantically_eq_post_only(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Returned { ret: r1, .. }, Self::Returned { ret: r2, mem_digest: m2 }) => {
                let expected = self
                    .post_state_slot()
                    .map(|s| compute_boundary_mem_digest(&[s]))
                    .unwrap_or_default();
                r1.semantically_eq(r2) && &expected == m2
            }
            (Self::Unwound { .. }, Self::Unwound { mem_digest: m2 })
            | (Self::Aborted { .. }, Self::Aborted { mem_digest: m2 }) => {
                let expected = self
                    .post_state_slot()
                    .map(|s| compute_boundary_mem_digest(&[s]))
                    .unwrap_or_default();
                &expected == m2
            }
            _ => self.semantically_eq(other),
        }
    }
}

/// Compute a canonical 64-character SHA-256 hex digest over observed boundary
/// byte slots (`Some(byte)` vs `None` padding).
pub fn compute_boundary_mem_digest(slots: &[Vec<Option<u8>>]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-boundary-mem-v1:");
    hasher.update((slots.len() as u64).to_le_bytes());
    for slot in slots {
        hasher.update((slot.len() as u64).to_le_bytes());
        for b in slot {
            match b {
                Some(v) => {
                    hasher.update([1u8, *v]);
                }
                None => {
                    hasher.update([0u8, 0u8]);
                }
            }
        }
    }
    let digest = hasher.finalize();
    let mut hex = String::with_capacity(64);
    for b in digest {
        let _ = write!(hex, "{b:02x}");
    }
    hex
}

/// Validate that terminating authority trace payloads carry the mandatory
/// post-execution terminal boundary slot (`[0x10, ...ret_bytes]` for
/// `"returned"`, `[0x20]` for `"unwound"`, `[0x30]` for `"aborted"`).
pub fn validate_terminal_boundary_slots(
    authority: &str,
    outcome_kind: &str,
    boundary_slots: &[Vec<Option<u8>>],
) -> Result<(), String> {
    validate_boundary_slots_for_outcome(authority, outcome_kind, None, None, boundary_slots)
}

/// Validate complete `boundary_slots` framing, including entry-argument slot
/// count (when `expected_entry_slots` is known) and exact post-return byte
/// parity against `parsed_ret` on `"returned"`.
pub fn validate_boundary_slots_for_outcome(
    authority: &str,
    outcome_kind: &str,
    parsed_ret: Option<&TraceVal>,
    expected_entry_slots: Option<usize>,
    boundary_slots: &[Vec<Option<u8>>],
) -> Result<(), String> {
    let check_total_slots = |expected_total: usize| -> Result<(), String> {
        if boundary_slots.len() != expected_total {
            return Err(format!(
                "{authority} `{outcome_kind}` trace boundary_slots count mismatch: expected {expected_total}, got {}",
                boundary_slots.len()
            ));
        }
        Ok(())
    };

    match outcome_kind {
        "returned" => {
            if let Some(n) = expected_entry_slots {
                check_total_slots(n + 1)?;
            }
            match (boundary_slots.last(), parsed_ret) {
                (Some(last), Some(ret)) => {
                    let expected_last: Vec<Option<u8>> =
                        std::iter::once(Some(0x10)).chain(ret.encode_boundary_bytes()).collect();
                    if last != &expected_last {
                        return Err(format!(
                            "{authority} `returned` trace post-return boundary slot mismatch: expected {expected_last:?}, got {last:?}"
                        ));
                    }
                    Ok(())
                }
                (Some(last), None) if last.first() == Some(&Some(0x10)) => Ok(()),
                (other, _) => Err(format!(
                    "{authority} `returned` trace missing post-return boundary slot tag 0x10 (last={other:?})"
                )),
            }
        }
        "unwound" => {
            if let Some(n) = expected_entry_slots {
                check_total_slots(n + 1)?;
            }
            match boundary_slots.last() {
                Some(last) if last.as_slice() == [Some(0x20)] => Ok(()),
                other => Err(format!(
                    "{authority} `unwound` trace missing post-unwind boundary slot [0x20] (last={other:?})"
                )),
            }
        }
        "aborted" => {
            if let Some(n) = expected_entry_slots {
                check_total_slots(n + 1)?;
            }
            match boundary_slots.last() {
                Some(last) if last.as_slice() == [Some(0x30)] => Ok(()),
                other => Err(format!(
                    "{authority} `aborted` trace missing post-abort boundary slot [0x30] (last={other:?})"
                )),
            }
        }
        "pre_entry" | "fault_ub" | "fault_undefined" | "fault_unsupported" | "diverged"
        | "init_unsupported" => {
            if let Some(n) = expected_entry_slots {
                check_total_slots(n)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Snapshot of caller-frame local slots and caller-visible allocation bytes
/// taken immediately before and after a callee invocation or unwind cleanup.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallerFrameSnapshot {
    /// Named/indexed local slots mapped to layout-aware byte views (`None` =
    /// padding or uninit).
    pub locals: BTreeMap<String, Vec<Option<u8>>>,
    /// Allocation IDs mapped to layout-aware byte views (`None` = padding or
    /// uninit).
    pub allocs: BTreeMap<u64, Vec<Option<u8>>>,
}

impl CallerFrameSnapshot {
    pub fn locals_digest(&self) -> String {
        let json = serde_json::to_string(&self.locals).unwrap_or_default();
        sha256_hex(json.as_bytes())
    }

    pub fn mem_digest(&self) -> String {
        let slots: Vec<Vec<Option<u8>>> = self.allocs.values().cloned().collect();
        compute_boundary_mem_digest(&slots)
    }
}

/// Verification receipt for the caller-frame preservation law across call and
/// cleanup-unwind boundaries.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallerFrameLaw {
    pub caller_locals_preserved: bool,
    pub untouched_alloc_bytes_preserved: bool,
    pub padding_mask_respected: bool,
    pub violations: Vec<String>,
}

impl Default for CallerFrameLaw {
    fn default() -> Self {
        Self::all_satisfied()
    }
}

impl CallerFrameLaw {
    pub fn all_satisfied() -> Self {
        Self {
            caller_locals_preserved: true,
            untouched_alloc_bytes_preserved: true,
            padding_mask_respected: true,
            violations: Vec::new(),
        }
    }

    pub fn is_satisfied(&self) -> bool {
        self.caller_locals_preserved
            && self.untouched_alloc_bytes_preserved
            && self.padding_mask_respected
            && self.violations.is_empty()
    }

    /// Compare `before` and `after` caller snapshots, verifying:
    /// 1. Every local not listed in `allowed_modified_locals` is preserved.
    /// 2. Every allocation not listed in `allowed_modified_allocs` has every
    ///    initialized byte preserved.
    /// 3. Padding offsets (`None` in `before`) are never silently treated as
    ///    initialized mismatches or overwritten with spurious bytes on
    ///    untouched slots.
    pub fn verify(
        before: &CallerFrameSnapshot,
        after: &CallerFrameSnapshot,
        allowed_modified_locals: &[&str],
        allowed_modified_allocs: &[u64],
    ) -> Self {
        let mut caller_locals_preserved = true;
        let mut untouched_alloc_bytes_preserved = true;
        let mut padding_mask_respected = true;
        let mut violations = Vec::new();

        for (local_name, before_bytes) in &before.locals {
            if allowed_modified_locals.contains(&local_name.as_str()) {
                continue;
            }
            match after.locals.get(local_name) {
                None => {
                    caller_locals_preserved = false;
                    violations.push(format!("caller local `{local_name}` disappeared after call"));
                }
                Some(after_bytes) => {
                    if before_bytes.len() != after_bytes.len() {
                        caller_locals_preserved = false;
                        violations.push(format!(
                            "caller local `{local_name}` size changed: {} -> {}",
                            before_bytes.len(),
                            after_bytes.len()
                        ));
                    } else {
                        for (idx, (b, a)) in before_bytes.iter().zip(after_bytes.iter()).enumerate()
                        {
                            match (b, a) {
                                (Some(x), Some(y)) if x != y => {
                                    caller_locals_preserved = false;
                                    violations.push(format!(
                                        "caller local `{local_name}` byte[{idx}] mutated: {x:#04x} -> {y:#04x}"
                                    ));
                                }
                                (None, Some(y)) => {
                                    padding_mask_respected = false;
                                    violations.push(format!(
                                        "caller local `{local_name}` padding byte[{idx}] leaked/initialized to {y:#04x}"
                                    ));
                                }
                                (Some(x), None) => {
                                    caller_locals_preserved = false;
                                    padding_mask_respected = false;
                                    violations.push(format!(
                                        "caller local `{local_name}` initialized byte[{idx}] ({x:#04x}) cleared to padding/uninit"
                                    ));
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }

        for (alloc_id, before_bytes) in &before.allocs {
            if allowed_modified_allocs.contains(alloc_id) {
                continue;
            }
            match after.allocs.get(alloc_id) {
                None => {
                    untouched_alloc_bytes_preserved = false;
                    violations.push(format!("untouched allocation #{alloc_id} disappeared"));
                }
                Some(after_bytes) => {
                    if before_bytes.len() != after_bytes.len() {
                        untouched_alloc_bytes_preserved = false;
                        violations.push(format!(
                            "untouched allocation #{alloc_id} length changed: {} -> {}",
                            before_bytes.len(),
                            after_bytes.len()
                        ));
                    } else {
                        for (idx, (b, a)) in before_bytes.iter().zip(after_bytes.iter()).enumerate()
                        {
                            match (b, a) {
                                (Some(x), Some(y)) if x != y => {
                                    untouched_alloc_bytes_preserved = false;
                                    violations.push(format!(
                                        "untouched allocation #{alloc_id} byte[{idx}] mutated: {x:#04x} -> {y:#04x}"
                                    ));
                                }
                                (None, Some(y)) => {
                                    padding_mask_respected = false;
                                    violations.push(format!(
                                        "untouched allocation #{alloc_id} padding byte[{idx}] leaked value {y:#04x}"
                                    ));
                                }
                                (Some(x), None) => {
                                    untouched_alloc_bytes_preserved = false;
                                    padding_mask_respected = false;
                                    violations.push(format!(
                                        "untouched allocation #{alloc_id} byte[{idx}] ({x:#04x}) cleared"
                                    ));
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }

        Self {
            caller_locals_preserved,
            untouched_alloc_bytes_preserved,
            padding_mask_respected,
            violations,
        }
    }

    pub fn merge(&mut self, other: &Self) {
        self.caller_locals_preserved &= other.caller_locals_preserved;
        self.untouched_alloc_bytes_preserved &= other.untouched_alloc_bytes_preserved;
        self.padding_mask_respected &= other.padding_mask_respected;
        self.violations.extend(other.violations.iter().cloned());
    }
}

mod authority_and_ub;
mod classify;

pub use self::{
    authority_and_ub::{
        AuthorityRunResult, ConservativeRefKind, DisclosedGapKind, DisclosedGapSpec,
        ExpectedConservativeSpec, ExpectedUbSpec, MetamorphicStatus, SpineCompareMode,
        UbFaultClass, classify_ub_fault_detail, is_rust_scheduled_return_decode_fault,
        ub_fault_causes_compatible,
    },
    classify::{
        TraceVerdict, classify_four_way, classify_four_way_with_ub_guard, compare_spines,
        compare_ub_fault_results, normalize_unwind_reason, sha256_hex,
    },
};
