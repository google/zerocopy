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

/// How strictly observable spines should be compared between authorities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SpineCompareMode {
    /// Compare full `CallEnter`/`CallReturn`/`CallUnwind`, `CallerFrameCheck`,
    /// AND `BranchTag` sequences.
    FullBranchesAndCalls,
    /// Compare branch-erased call events and `CallerFrameCheck` checkpoints in
    /// exact relative interleaving order (ignoring `BranchTag` transitions).
    ObsErasedCallsOnly,
    /// Compare only terminal outcome + caller-frame preservation flags.
    OutcomeOnly,
}

/// Complete receipt returned by a single execution authority (`rustc`, `miri`,
/// `lean`, or `anneal-mir-eval`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthorityRunResult {
    pub authority: String,
    pub outcome: TerminalOutcome,
    pub spine: ObservableSpine,
    pub caller_frame_law: CallerFrameLaw,
    pub tool_error: Option<String>,
    pub raw_diagnostics: String,
    pub elapsed_ms: u64,
    #[serde(default)]
    pub post_only_mem_digest: bool,
    /// SHA-256 hex digest of entry-argument `boundary_slots` captured before
    /// executing the subject body (`None` only in value-only / synthetic unit
    /// fixtures omitting entry slots).
    #[serde(default)]
    pub entry_mem_digest: Option<String>,
}

impl AuthorityRunResult {
    pub fn tool_error(authority: impl Into<String>, detail: impl Into<String>) -> Self {
        let d = detail.into();
        Self {
            authority: authority.into(),
            outcome: TerminalOutcome::CaptureRefused { reason: d.clone() },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::all_satisfied(),
            tool_error: Some(d),
            raw_diagnostics: String::new(),
            elapsed_ms: 0,
            post_only_mem_digest: false,
            entry_mem_digest: None,
        }
    }

    pub fn skipped_for_ub(authority: impl Into<String>, reason: impl Into<String>) -> Self {
        Self {
            authority: authority.into(),
            outcome: TerminalOutcome::CaptureRefused { reason: reason.into() },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::all_satisfied(),
            tool_error: None,
            raw_diagnostics: String::new(),
            elapsed_ms: 0,
            post_only_mem_digest: false,
            entry_mem_digest: None,
        }
    }
}

/// Explicit disclosed semantic gap categories documented at Anneal's boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DisclosedGapKind {
    /// Caller-supplied raw pointer aliasing outside value-only entry memory.
    CallerRawPtrAliasing,
    /// Selected-unit scope (`VerificationScope.unit`) omitting external
    /// callees.
    SelectedUnitScope,
    /// Unbridged Rust construct intentionally outside the modeled MIR fragment.
    UnbridgedSemantics,
}

/// Specification pairing a [`DisclosedGapKind`] with the exact Lean or capture
/// boundary diagnostic marker required to admit a discrepancy as a
/// [`TraceVerdict::DisclosedGapArtifact`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DisclosedGapSpec {
    pub kind: DisclosedGapKind,
    pub expected_fault_marker: String,
}

impl DisclosedGapSpec {
    pub fn new(kind: DisclosedGapKind, expected_fault_marker: impl Into<String>) -> Self {
        Self { kind, expected_fault_marker: expected_fault_marker.into() }
    }

    /// Return `true` only when `outcome` is a Lean `CaptureRefused` or
    /// `FaultUb` whose diagnostic contains `self.expected_fault_marker` and
    /// carries no unrelated arithmetic, division, unreachable, or generic step
    /// UB markers.
    pub fn matches_lean_outcome(&self, outcome: &TerminalOutcome) -> bool {
        let marker = self.expected_fault_marker.trim();
        if marker.is_empty() {
            return false;
        }
        let detail = match outcome {
            TerminalOutcome::CaptureRefused { reason } => reason.as_str(),
            TerminalOutcome::FaultUb { detail } => detail.as_str(),
            TerminalOutcome::Returned { .. }
            | TerminalOutcome::Unwound { .. }
            | TerminalOutcome::Aborted { .. }
            | TerminalOutcome::Diverged { .. } => return false,
        };
        if !detail.contains(marker) {
            return false;
        }
        let lower = detail.to_ascii_lowercase();
        const UNRELATED_FAULT_MARKERS: &[&str] = &[
            "overflow",
            "division by zero",
            "div by zero",
            "divide by zero",
            "remainder by zero",
            "unreachable",
            "uninitialized return",
            "uninit return",
            "assert condition undefined",
            "diverging call",
            "trusted.mirsemantics.faultkind.undefined",
        ];
        if UNRELATED_FAULT_MARKERS.iter().any(|bad| lower.contains(bad)) {
            return false;
        }
        if self.kind == DisclosedGapKind::CallerRawPtrAliasing {
            let marker_lower = marker.to_ascii_lowercase();
            const PTR_MARKERS: &[&str] =
                &["*const", "*mut", "ptr", "pointer", "deref", "addr", "alias", "provenance"];
            if !PTR_MARKERS.iter().any(|p| marker_lower.contains(p)) {
                return false;
            }
        }
        true
    }
}

/// Normalized Undefined Behavior cause category used to verify that two
/// authorities reporting [`TerminalOutcome::FaultUb`] faulted for compatible
/// semantic reasons (preventing an earlier unrelated UB in Miri from silently
/// matching a later UB in Lean or `anneal-mir-eval`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UbFaultClass {
    /// Invalid scheduled boundary return payload (`ReturnBytes` bit pattern or
    /// byte length rejected before resuming caller).
    ScheduledReturnDecode,
    /// Execution entered `unreachable_unchecked` or
    /// `TerminatorKind.unreachable`, unwound into `UnwindAction.unreachable` or
    /// a `nounwind` frame, or returned from a diverging `!` call.
    UnreachableOrNoUnwind,
    /// Unchecked shift overflow (`unchecked_shl` / `unchecked_shr` /
    /// `.shlUnchecked` / `.shrUnchecked`).
    UncheckedShiftOverflow,
    /// Unchecked integer arithmetic overflow (`unchecked_add`/`sub`/`mul`) or
    /// division/remainder UB (division by zero or `MIN / -1`).
    UncheckedArithOrDivOverflow,
    /// Pointer dereference, alignment, null, out-of-bounds, provenance,
    /// deallocation, or borrow-stack / Tree Borrows violation.
    PointerOrMemoryAccess,
    /// Invalid scalar/enum/bool/char bit pattern, uninitialized read, or dead
    /// local access outside scheduled return decoding.
    InvalidValueOrUninit,
    /// Uncategorized / synthetic UB diagnostic.
    Unclassified,
}

fn extract_rust_scheduled_decode_callee(detail: &str) -> Option<&str> {
    if let Some(rest) = detail.strip_prefix("callee `")
        && let Some((callee, reason)) = rest.split_once("` scheduled ReturnBytes invalid: ")
        && !callee.is_empty()
        && !reason.trim().is_empty()
    {
        return Some(callee);
    }
    None
}

/// Return `true` only when `detail` matches the standalone Rust/Miri harness
/// `anneal_rt::ScheduleDecodeFailed` message emitted on zero-exit
/// `ANNEAL_ITREE_TRACE_JSON` `fault_ub` output.
pub fn is_rust_scheduled_return_decode_fault(detail: &str) -> bool {
    extract_rust_scheduled_decode_callee(detail).is_some()
}

fn extract_scheduled_decode_callee(detail: &str) -> Option<&str> {
    if let Some(callee) = extract_rust_scheduled_decode_callee(detail) {
        return Some(callee);
    }
    if let Some(callee) = detail.strip_prefix("invalid scheduled ReturnBytes for ") {
        let trimmed = callee.trim();
        if !trimmed.is_empty() {
            return Some(trimmed);
        }
    }
    None
}

/// Normalize a Miri, Lean `ITreeDriver`, `anneal-mir-eval`, or standalone Rust
/// harness `FaultUb` diagnostic into a canonical [`UbFaultClass`].
pub fn classify_ub_fault_detail(detail: &str) -> UbFaultClass {
    let lower = detail.to_ascii_lowercase();
    if lower.contains("scheduled returnbytes") {
        UbFaultClass::ScheduledReturnDecode
    } else if lower.contains("unreachable")
        || lower.contains("does not allow unwinding")
        || lower.contains("from diverging call")
    {
        UbFaultClass::UnreachableOrNoUnwind
    } else if lower.contains("overflowing shift")
        || lower.contains("unchecked_shl")
        || lower.contains("unchecked_shr")
        || lower.contains("unchecked shift")
        || lower.contains("shift overflow")
    {
        UbFaultClass::UncheckedShiftOverflow
    } else if lower.contains("unchecked_add")
        || lower.contains("unchecked_sub")
        || lower.contains("unchecked_mul")
        || lower.contains("unchecked arithmetic")
        || lower.contains("unchecked signed arithmetic")
        || lower.contains("unchecked unsigned arithmetic")
        || lower.contains("overflowing arithmetic")
        || lower.contains("division by zero")
        || lower.contains("dividing by zero")
        || lower.contains("remainder by zero")
        || lower.contains("divisor of zero")
        || lower.contains("division or remainder")
        || lower.contains("min / -1")
        || lower.contains("overflow in signed")
    {
        UbFaultClass::UncheckedArithOrDivOverflow
    } else if lower.contains("dereferencing pointer")
        || lower.contains("pointer dereference")
        || lower.contains("pointer arithmetic")
        || lower.contains("pointer or memory access")
        || lower.contains("memory access")
        || lower.contains("memory read")
        || lower.contains("memory write")
        || lower.contains("misaligned")
        || lower.contains("with alignment")
        || lower.contains("null pointer")
        || lower.contains("dangling")
        || lower.contains("use-after-free")
        || lower.contains("deallocating")
        || lower.contains("immutable allocation")
        || lower.contains("out-of-bounds")
        || lower.contains("borrow stack")
        || lower.contains("tree borrows")
        || lower.contains("is forbidden")
    {
        UbFaultClass::PointerOrMemoryAccess
    } else if lower.contains("constructing invalid value")
        || lower.contains("using uninitialized")
        || lower.contains("uninitialized")
        || lower.contains("dead local")
        || lower.contains("dead _0")
        || lower.contains("dead destination")
        || lower.contains("entry argument bit-validity")
        || lower.contains("invalid boolean")
        || lower.contains("invalid char")
        || lower.contains("surrogate")
        || lower.contains("invalid ordering")
        || lower.contains("invalid fieldless enum")
        || lower.contains("invalid tag")
        || lower.contains("invalid discriminant")
        || lower.contains("invalid value")
        || lower.contains("validation failure")
        || lower.contains("writeplace undefined")
        || lower.contains("call argument eval undefined")
        || lower.contains("assert condition undefined")
    {
        UbFaultClass::InvalidValueOrUninit
    } else {
        UbFaultClass::Unclassified
    }
}

/// Return `true` only when two `FaultUb` diagnostics denote compatible UB fault
/// causes (matching [`UbFaultClass`] and, for `ScheduledReturnDecode`, matching
/// callee identity whenever both diagnostics name a callee; `Unclassified`
/// strings match only identical non-empty synthetic tokens and never match a
/// classified UB category).
pub fn ub_fault_causes_compatible(ref_detail: &str, cand_detail: &str) -> bool {
    let c1 = classify_ub_fault_detail(ref_detail);
    let c2 = classify_ub_fault_detail(cand_detail);
    match (c1, c2) {
        (UbFaultClass::Unclassified, UbFaultClass::Unclassified) => {
            let t1 = ref_detail.trim();
            !t1.is_empty() && t1 == cand_detail.trim()
        }
        (UbFaultClass::ScheduledReturnDecode, UbFaultClass::ScheduledReturnDecode) => {
            if let (Some(cal1), Some(cal2)) = (
                extract_scheduled_decode_callee(ref_detail),
                extract_scheduled_decode_callee(cand_detail),
            ) {
                cal1 == cal2
            } else {
                true
            }
        }
        (a, b) if a != UbFaultClass::Unclassified && b != UbFaultClass::Unclassified => a == b,
        _ => false,
    }
}

/// Expected Undefined Behavior fault cause and authority diagnostic markers
/// required on [`crate::spec::ExpectedCaseClass::UndefinedBehavior`] cases so
/// negative UB tests cannot pass for an unrelated fault.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpectedUbSpec {
    pub class: UbFaultClass,
    pub miri_marker: String,
    #[serde(default)]
    pub lean_marker: Option<String>,
    #[serde(default)]
    pub lean_refusal_marker: Option<String>,
    #[serde(default)]
    pub mir_eval_marker: Option<String>,
}

impl ExpectedUbSpec {
    pub fn new(
        class: UbFaultClass,
        miri_marker: impl Into<String>,
        lean_marker: Option<&str>,
    ) -> Self {
        Self {
            class,
            miri_marker: miri_marker.into(),
            lean_marker: lean_marker.map(str::to_owned),
            lean_refusal_marker: None,
            mir_eval_marker: None,
        }
    }

    /// Require conservative Lean `CaptureRefused` outcomes on this UB case (or
    /// in `StrictVerbatim` when the spec also requires strict-mode refusal) to
    /// contain `marker` instead of accepting unrelated refusals.
    pub fn with_lean_refusal_marker(mut self, marker: impl Into<String>) -> Self {
        self.lean_refusal_marker = Some(marker.into());
        self
    }

    /// Require `anneal-mir-eval` `FaultUb` diagnostics to match `marker`.
    pub fn with_mir_eval_marker(mut self, marker: impl Into<String>) -> Self {
        self.mir_eval_marker = Some(marker.into());
        self
    }
}

/// Expected reference outcome shape on
/// [`crate::spec::ExpectedCaseClass::ConservativeOverApprox`] cases.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ConservativeRefKind {
    /// Reference (`rustc`/`miri`) returns normally (`Returned`).
    Returned,
    /// Reference (`rustc`/`miri`) panics/unwinds (`Unwound`).
    Unwound,
    /// Reference (`rustc`/`miri`) aborts (`Aborted`).
    Aborted,
}

impl ConservativeRefKind {
    /// Return `true` when `outcome` matches the expected reference kind.
    pub fn matches_outcome(self, outcome: Option<&TerminalOutcome>) -> bool {
        match self {
            Self::Returned => matches!(outcome, Some(TerminalOutcome::Returned { .. })),
            Self::Unwound => matches!(outcome, Some(TerminalOutcome::Unwound { .. })),
            Self::Aborted => matches!(outcome, Some(TerminalOutcome::Aborted { .. })),
        }
    }
}

/// Expected conservative refusal cause and reference outcome binding
/// required on [`crate::spec::ExpectedCaseClass::ConservativeOverApprox`]
/// cases so negative tests cannot pass vacuously via unrelated refusals or
/// step-fuel exhaustion.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpectedConservativeSpec {
    pub ref_kind: ConservativeRefKind,
    pub lean_marker: String,
}

impl ExpectedConservativeSpec {
    pub fn new(ref_kind: ConservativeRefKind, lean_marker: impl Into<String>) -> Self {
        Self { ref_kind, lean_marker: lean_marker.into() }
    }
}

/// Disposition of a metamorphic multi-call vs source-inlined twin check.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum MetamorphicStatus {
    /// Both multi-call (`CompositionalITree`) and source-inlined
    /// (`StrictVerbatim`) Lean executions completed non-conservatively and
    /// matched across all active authorities.
    Passed,
    /// Either the multi-call or source-inlined Lean leg conservatively refused
    /// (`CaptureRefused`) or exhausted step fuel (`Diverged`), while all
    /// non-conservative compiler and Miri checks succeeded.
    SkippedConservative { reason: String },
    /// Semantic disagreement, `CallerFrameLaw` failure, or `ToolError` between
    /// the multi-call and source-inlined twins.
    Failed,
}

/// Final differential classification across execution authorities.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "verdict", rename_all = "snake_case")]
pub enum TraceVerdict {
    /// Full 4-way agreement with both Miri UB authority and Lean
    /// `Trusted.MirSemantics` active on `TerminalOutcome`, `ObservableSpine`,
    /// and `CallerFrameLaw`. Never emitted when Miri or Lean is unavailable or
    /// disabled.
    Agree,
    /// Degraded parity check without Miri (`miri == None`, e.g. inside trimmed
    /// archive `workspace-tests`): `rustc O0 == O2` and Lean agree (or Lean
    /// conservatively faults on an `expected_ub` case), but Miri UB oracle
    /// confirmation was not run. Excluded from clean `Agree` admission and
    /// fails closed when `--require-miri` / `ANNEAL_ITREE_REQUIRE_MIRI=1` is
    /// set.
    DegradedNoMiri { detail: String },
    /// Degraded parity check without Lean (`lean == None`, e.g. under
    /// `--no-lean`): `rustc O0 == O2` and Miri agreed without critical
    /// failures, but Lean semantic verification was disabled. Excluded from
    /// clean `Agree` admission.
    DegradedNoLean { detail: String },
    /// CRITICAL (P0): Reference authority reports UB or disagrees on terminal
    /// outcome, observable spine, or caller-frame preservation while Lean
    /// accepts.
    UnsoundAccept { detail: String },
    /// Valid forward-simulation conservative over-approximation (`forwardSim`
    /// holds; `biFaultEquiv` gap): Lean faults `.undefined`/`.unsupported`,
    /// exhausts step fuel, or capture refuses where Miri/rustc succeeds.
    /// Explicitly flagged as NEVER licensing UB refutation, and
    /// `undeclared_ub_fault` fails CI gates when Lean reports
    /// `.fault .undefined` on an accepting Miri run without a matching
    /// [`DisclosedGapSpec`] (`docs/testing-architecture.md` §4.2).
    ConservativeOverApprox {
        reason: String,
        ub_refutation_disallowed: bool,
        undeclared_ub_fault: bool,
    },
    /// Expected discrepancy matching an explicitly declared boundary gap.
    DisclosedGapArtifact { gap: DisclosedGapKind, detail: String },
    /// Harness, toolchain, timeout, or protocol failure (never silently
    /// downgraded to `Agree` or `ConservativeOverApprox`).
    ToolError { authority: String, detail: String },
}

impl TraceVerdict {
    pub fn is_critical_failure(&self) -> bool {
        matches!(
            self,
            Self::UnsoundAccept { .. }
                | Self::ToolError { .. }
                | Self::ConservativeOverApprox { undeclared_ub_fault: true, .. }
        )
    }

    pub fn label(&self) -> &'static str {
        match self {
            Self::Agree => "AGREE",
            Self::DegradedNoMiri { .. } => "DEGRADED_NO_MIRI",
            Self::DegradedNoLean { .. } => "DEGRADED_NO_LEAN",
            Self::UnsoundAccept { .. } => "UNSOUND_ACCEPT_P0",
            Self::ConservativeOverApprox { undeclared_ub_fault: true, .. } => {
                "UNDECLARED_UB_FAULT_REGRESSION"
            }
            Self::ConservativeOverApprox { undeclared_ub_fault: false, .. } => {
                "CONSERVATIVE_OVER_APPROX"
            }
            Self::DisclosedGapArtifact { .. } => "DISCLOSED_GAP_ARTIFACT",
            Self::ToolError { .. } => "TOOL_ERROR",
        }
    }
}

impl fmt::Display for TraceVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Agree => write!(f, "Agree"),
            Self::DegradedNoMiri { detail } => write!(f, "DegradedNoMiri: {detail}"),
            Self::DegradedNoLean { detail } => write!(f, "DegradedNoLean: {detail}"),
            Self::UnsoundAccept { detail } => write!(f, "UnsoundAccept(P0): {detail}"),
            Self::ConservativeOverApprox {
                reason,
                ub_refutation_disallowed,
                undeclared_ub_fault,
            } => write!(
                f,
                "ConservativeOverApprox(ub_refutation_disallowed={ub_refutation_disallowed}, undeclared_ub_fault={undeclared_ub_fault}): {reason}"
            ),
            Self::DisclosedGapArtifact { gap, detail } => {
                write!(f, "DisclosedGapArtifact({gap:?}): {detail}")
            }
            Self::ToolError { authority, detail } => {
                write!(f, "ToolError({authority}): {detail}")
            }
        }
    }
}

/// Compare two observable spines according to `mode`, checking call events,
/// `CallerFrameCheck` checkpoints, and (in `FullBranchesAndCalls`) `BranchTag`
/// transitions.
pub fn compare_spines(
    reference_name: &str,
    reference: &ObservableSpine,
    candidate_name: &str,
    candidate: &ObservableSpine,
    mode: SpineCompareMode,
) -> Result<(), String> {
    match mode {
        SpineCompareMode::OutcomeOnly => Ok(()),
        SpineCompareMode::ObsErasedCallsOnly => {
            let ref_stream = normalize_call_events(&reference.erased_branch_spine());
            let cand_stream = normalize_call_events(&candidate.erased_branch_spine());
            if ref_stream != cand_stream {
                return Err(format!(
                    "obs-erased observable spine mismatch: {reference_name}={ref_stream:?} vs {candidate_name}={cand_stream:?}"
                ));
            }
            Ok(())
        }
        SpineCompareMode::FullBranchesAndCalls => {
            let ref_calls = reference.erased_call_spine();
            let cand_calls = candidate.erased_call_spine();
            if ref_calls != cand_calls {
                return Err(format!(
                    "full call spine mismatch: {reference_name}={ref_calls:?} vs {candidate_name}={cand_calls:?}"
                ));
            }
            let ref_frames = reference.caller_frame_checks();
            let cand_frames = candidate.caller_frame_checks();
            if ref_frames != cand_frames {
                return Err(format!(
                    "caller-frame checkpoint spine mismatch: {reference_name}={ref_frames:?} vs {candidate_name}={cand_frames:?}"
                ));
            }
            let ref_branches = reference.branch_tags();
            let cand_branches = candidate.branch_tags();
            if ref_branches != cand_branches {
                return Err(format!(
                    "branch tag spine mismatch: {reference_name}={ref_branches:?} vs {candidate_name}={cand_branches:?}"
                ));
            }
            if reference.events != candidate.events {
                return Err(format!(
                    "full event interleaving spine mismatch: {reference_name}={:?} vs {candidate_name}={:?}",
                    reference.events, candidate.events
                ));
            }
            Ok(())
        }
    }
}

fn format_masked_bytes(bytes: &[Option<u8>]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2 + 2);
    out.push('[');
    for b in bytes {
        match b {
            Some(v) => {
                let _ = write!(out, "{v:02x}");
            }
            None => out.push_str("__"),
        }
    }
    out.push(']');
    out
}

fn normalize_call_events(events: &[ObservableEvent]) -> Vec<String> {
    events
        .iter()
        .map(|ev| match ev {
            ObservableEvent::CallEnter { callee, arg_bytes, arg_reprs } => {
                let bytes_part = arg_bytes
                    .iter()
                    .map(|slot| format_masked_bytes(slot))
                    .collect::<Vec<_>>()
                    .join(",");
                format!("ENTER:{callee}({})[{bytes_part}]", arg_reprs.join(","))
            }
            ObservableEvent::CallReturn { callee, ret_bytes, ret_repr } => {
                format!("RETURN:{callee}={ret_repr}@{}", format_masked_bytes(ret_bytes))
            }
            ObservableEvent::CallUnwind { callee, reason } => {
                format!("UNWIND:{callee}:{}", normalize_unwind_reason(reason))
            }
            ObservableEvent::BranchTag { block, discr, target } => {
                format!("BRANCH:bb{block}({discr})->bb{target}")
            }
            ObservableEvent::CallerFrameCheck {
                point,
                locals_preserved,
                allocs_preserved,
                preserved,
            } => {
                format!("FRAME:{point}:{locals_preserved}:{allocs_preserved}:{preserved}")
            }
        })
        .collect()
}

/// Normalize `CallUnwind.reason` across Rust/Miri panic messages, Lean MIR
/// `.assert` unwind tags, and scheduled `EnvAction::{Unwind,Abort}` payloads so
/// `ObsErasedCallsOnly` preserves unwind causes without coupling to dynamic
/// Rust bounds-check indices.
pub fn normalize_unwind_reason(reason: &str) -> String {
    let trimmed = reason.trim();
    if let Some(rest) = trimmed.strip_prefix("abort:") {
        format!("abort:{rest}")
    } else if trimmed == "assert:div_by_zero" || trimmed.contains("attempt to divide by zero") {
        "panic:div_by_zero".to_string()
    } else if trimmed == "assert:rem_by_zero"
        || trimmed.contains("attempt to calculate the remainder with a divisor of zero")
    {
        "panic:rem_by_zero".to_string()
    } else if trimmed == "assert:bounds_check" || trimmed.starts_with("index out of bounds:") {
        "panic:bounds_check".to_string()
    } else if trimmed == "assert:overflow"
        || (trimmed.starts_with("attempt to ") && trimmed.ends_with(" with overflow"))
    {
        "panic:overflow".to_string()
    } else {
        format!("unwind:{trimmed}")
    }
}

/// Classify a 4-way differential run across `rustc -O0`, `rustc -O2`, `miri`,
/// `lean`, and optional `anneal-mir-eval`.
///
/// Enforces:
/// 1. When Miri reports `FaultUb` (or when `rustc_skipped_for_ub` is set),
///    native `rustc` results/errors are never consulted as UB ground truth.
/// 2. When `miri` is `None`, `TraceVerdict::Agree` is NEVER returned; clean
///    non-Miri runs classify as `TraceVerdict::DegradedNoMiri`.
/// 3. When `lean` is `None`, `TraceVerdict::Agree` is NEVER returned; clean
///    Miri-backed runs without Lean classify as `TraceVerdict::DegradedNoLean`.
#[allow(clippy::too_many_arguments)]
pub fn classify_four_way(
    rustc_o0: &AuthorityRunResult,
    rustc_o2: &AuthorityRunResult,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    mir_eval: Option<&AuthorityRunResult>,
    spine_mode: SpineCompareMode,
    disclosed_gap: Option<&DisclosedGapSpec>,
) -> TraceVerdict {
    classify_four_way_with_ub_guard(
        rustc_o0,
        rustc_o2,
        false,
        miri,
        lean,
        mir_eval,
        spine_mode,
        disclosed_gap,
    )
}

/// Full 4-way classifier accepting `rustc_skipped_for_ub` (set when Miri was
/// unavailable on a known `expected_ub` case so host `rustc` was intentionally
/// not executed on undefined behavior).
#[allow(clippy::too_many_arguments)]
pub fn classify_four_way_with_ub_guard(
    rustc_o0: &AuthorityRunResult,
    rustc_o2: &AuthorityRunResult,
    rustc_skipped_for_ub: bool,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    mir_eval: Option<&AuthorityRunResult>,
    spine_mode: SpineCompareMode,
    disclosed_gap: Option<&DisclosedGapSpec>,
) -> TraceVerdict {
    let miri_reports_ub =
        miri.is_some_and(|m| matches!(m.outcome, TerminalOutcome::FaultUb { .. }));
    let ignore_host_rustc = miri_reports_ub || rustc_skipped_for_ub;

    // 1. Check tool errors on non-ignored legs (never downgrade ToolError).
    let checked_for_tool_err: [Option<&AuthorityRunResult>; 5] = [
        if ignore_host_rustc { None } else { Some(rustc_o0) },
        if ignore_host_rustc { None } else { Some(rustc_o2) },
        miri,
        lean,
        mir_eval,
    ];
    for auth in checked_for_tool_err.into_iter().flatten() {
        if let Some(detail) = &auth.tool_error {
            return TraceVerdict::ToolError {
                authority: auth.authority.clone(),
                detail: detail.clone(),
            };
        }
    }

    // 2. Caller-frame preservation law check on every non-UB accepting run.
    let checked_for_frame: [Option<&AuthorityRunResult>; 5] = [
        if ignore_host_rustc { None } else { Some(rustc_o0) },
        if ignore_host_rustc { None } else { Some(rustc_o2) },
        miri,
        lean,
        mir_eval,
    ];
    for auth in checked_for_frame.into_iter().flatten() {
        if auth.outcome.is_accepting() && !auth.caller_frame_law.is_satisfied() {
            return TraceVerdict::UnsoundAccept {
                detail: format!(
                    "{} violated CallerFrameLaw: {:?}",
                    auth.authority, auth.caller_frame_law.violations
                ),
            };
        }
    }

    // 3. When host rustc ran on defined-behavior inputs, require O0 == O2.
    if !ignore_host_rustc {
        if !rustc_o0.outcome.semantically_eq(&rustc_o2.outcome) {
            return TraceVerdict::UnsoundAccept {
                detail: format!(
                    "rustc O0 vs O2 terminal outcome divergence: O0={:?} vs O2={:?}",
                    rustc_o0.outcome, rustc_o2.outcome
                ),
            };
        }
        if let Err(msg) =
            compare_spines("rustc-O0", &rustc_o0.spine, "rustc-O2", &rustc_o2.spine, spine_mode)
        {
            return TraceVerdict::UnsoundAccept { detail: format!("rustc O0 vs O2: {msg}") };
        }
    }

    // 4. Branch on Miri availability.
    if let Some(m) = miri {
        // When Miri succeeds cleanly (no UB), cross-check Miri vs rustc-O0.
        if !miri_reports_ub && m.outcome.is_accepting() {
            if !m.outcome.semantically_eq(&rustc_o0.outcome) {
                return TraceVerdict::UnsoundAccept {
                    detail: format!(
                        "miri vs rustc-O0 outcome divergence: miri={:?} vs rustc-O0={:?}",
                        m.outcome, rustc_o0.outcome
                    ),
                };
            }
            if let Err(msg) =
                compare_spines("miri", &m.spine, "rustc-O0", &rustc_o0.spine, spine_mode)
            {
                return TraceVerdict::UnsoundAccept { detail: format!("miri vs rustc-O0: {msg}") };
            }
        }

        let lean_verdict =
            lean.map(|lean_res| classify_pair(m, lean_res, spine_mode, disclosed_gap));
        if let Some(lv) = &lean_verdict
            && lv.is_critical_failure()
        {
            return lv.clone();
        }

        let me_verdict = mir_eval
            .map(|me_res| classify_pair(m, me_res, SpineCompareMode::OutcomeOnly, disclosed_gap));
        if let Some(mv) = &me_verdict
            && mv.is_critical_failure()
        {
            return mv.clone();
        }

        if let Some(lv) = lean_verdict
            && !matches!(lv, TraceVerdict::Agree)
        {
            return lv;
        }

        if let Some(mv) = me_verdict
            && !matches!(mv, TraceVerdict::Agree)
        {
            return mv;
        }

        if lean.is_some() {
            return TraceVerdict::Agree;
        }

        let detail = if miri_reports_ub {
            "Miri detected Undefined Behavior, but Lean authority was disabled".to_string()
        } else {
            "rustc-O0, rustc-O2, and Miri agreed on outcome and spine, but Lean authority was disabled".to_string()
        };
        return TraceVerdict::DegradedNoLean { detail };
    }

    // 5. Degraded mode (`miri == None`): NEVER return `TraceVerdict::Agree`!
    if rustc_skipped_for_ub {
        // Expected-UB case without Miri: host rustc was skipped to avoid UB;
        // verify Lean (and mir_eval) did NOT accept or exhaust step fuel!
        for cand in [lean, mir_eval].into_iter().flatten() {
            if cand.outcome.is_accepting() {
                return TraceVerdict::UnsoundAccept {
                    detail: format!(
                        "expected-UB case accepted by {} ({:?}) while Miri was unavailable",
                        cand.authority, cand.outcome
                    ),
                };
            }
        }
        if let (Some(lean_res), Some(me_res)) = (lean, mir_eval)
            && matches!(lean_res.outcome, TerminalOutcome::FaultUb { .. })
            && matches!(me_res.outcome, TerminalOutcome::FaultUb { .. })
            && let Err(detail) = compare_ub_fault_results(lean_res, me_res)
        {
            return TraceVerdict::UnsoundAccept { detail };
        }
        if let (Some(gap_spec), Some(lean_res)) = (disclosed_gap, lean)
            && gap_spec.matches_lean_outcome(&lean_res.outcome)
        {
            return TraceVerdict::DisclosedGapArtifact {
                gap: gap_spec.kind,
                detail: "expected-UB disclosed gap verified conservatively without Miri"
                    .to_string(),
            };
        }
        let detail = if lean.is_some() {
            "expected-UB probe rejected conservatively by Lean; Miri unavailable"
        } else {
            "expected-UB probe skipped host rustc while both Miri and Lean were unavailable or disabled"
        };
        return TraceVerdict::DegradedNoMiri { detail: detail.to_string() };
    }

    // Defined-behavior case without Miri: check rustc_o0 vs Lean & mir_eval,
    // downgrading `Agree` to `DegradedNoMiri` while ensuring non-critical Lean
    // verdicts never mask critical `mir_eval` failures.
    let lean_verdict =
        lean.map(|lean_res| classify_pair(rustc_o0, lean_res, spine_mode, disclosed_gap));
    if let Some(lv) = &lean_verdict
        && lv.is_critical_failure()
    {
        return lv.clone();
    }

    let me_verdict = mir_eval.map(|me_res| {
        classify_pair(rustc_o0, me_res, SpineCompareMode::OutcomeOnly, disclosed_gap)
    });
    if let Some(mv) = &me_verdict
        && mv.is_critical_failure()
    {
        return mv.clone();
    }

    if let Some(lv) = lean_verdict
        && !matches!(lv, TraceVerdict::Agree)
    {
        return lv;
    }

    if let Some(mv) = me_verdict
        && !matches!(mv, TraceVerdict::Agree)
    {
        return mv;
    }

    let detail = if lean.is_some() {
        "rustc-O0, rustc-O2, and Lean agreed on outcome and spine, but Miri was unavailable"
    } else {
        "rustc-O0 and rustc-O2 agreed on outcome and spine, but Miri and Lean were unavailable or disabled"
    };
    TraceVerdict::DegradedNoMiri { detail: detail.to_string() }
}

/// Compare two `FaultUb` authority results, requiring authenticated
/// entry-input `boundary_slots` parity whenever entry digests are present (and
/// rejecting asymmetric missing entry digests unless a leg omitted
/// `boundary_slots` in value-only mode) alongside compatible UB fault causes.
pub fn compare_ub_fault_results(
    reference: &AuthorityRunResult,
    candidate: &AuthorityRunResult,
) -> Result<(), String> {
    let (
        TerminalOutcome::FaultUb { detail: ref_detail },
        TerminalOutcome::FaultUb { detail: cand_detail },
    ) = (&reference.outcome, &candidate.outcome)
    else {
        return Err(format!(
            "internal error: expected FaultUb outcomes, got {:?} vs {:?}",
            reference.outcome, candidate.outcome
        ));
    };

    match (&reference.entry_mem_digest, &candidate.entry_mem_digest) {
        (Some(r_dig), Some(c_dig)) if r_dig != c_dig => {
            return Err(format!(
                "UB entry-input boundary digest mismatch: {} ({r_dig}) vs {} ({c_dig})",
                reference.authority, candidate.authority
            ));
        }
        (Some(_), Some(_)) | (None, None) => {}
        (Some(_), None) | (None, Some(_)) => {
            let ref_omitted =
                reference.entry_mem_digest.is_none() && reference.post_only_mem_digest;
            let cand_omitted =
                candidate.entry_mem_digest.is_none() && candidate.post_only_mem_digest;
            if !(ref_omitted || cand_omitted) {
                return Err(format!(
                    "UB fault missing authenticated entry-input digest on one authority: {}={:?} vs {}={:?}",
                    reference.authority,
                    reference.entry_mem_digest,
                    candidate.authority,
                    candidate.entry_mem_digest,
                ));
            }
        }
    }

    if ub_fault_causes_compatible(ref_detail, cand_detail) {
        Ok(())
    } else {
        Err(format!(
            "UB fault cause mismatch: {} reported {:?} ({ref_detail}) while {} reported {:?} ({cand_detail})",
            reference.authority,
            classify_ub_fault_detail(ref_detail),
            candidate.authority,
            classify_ub_fault_detail(cand_detail),
        ))
    }
}

fn classify_pair(
    reference: &AuthorityRunResult,
    candidate: &AuthorityRunResult,
    spine_mode: SpineCompareMode,
    disclosed_gap: Option<&DisclosedGapSpec>,
) -> TraceVerdict {
    match (&reference.outcome, &candidate.outcome) {
        // Both hit UB -> require matching entry inputs + compatible UB causes!
        (TerminalOutcome::FaultUb { .. }, TerminalOutcome::FaultUb { .. }) => {
            match compare_ub_fault_results(reference, candidate) {
                Ok(()) => TraceVerdict::Agree,
                Err(detail) => TraceVerdict::UnsoundAccept { detail },
            }
        }
        // Both diverged at the same fuel -> compare spines -> Agree!
        (TerminalOutcome::Diverged { fuel: f1 }, TerminalOutcome::Diverged { fuel: f2 })
            if f1 == f2 =>
        {
            if let Err(msg) = compare_spines(
                &reference.authority,
                &reference.spine,
                &candidate.authority,
                &candidate.spine,
                spine_mode,
            ) {
                TraceVerdict::UnsoundAccept { detail: msg }
            } else {
                TraceVerdict::Agree
            }
        }
        // Candidate exhausted step fuel while reference terminated or hit UB ->
        // conservative fuel incompleteness (never UnsoundAccept).
        (ref_out, TerminalOutcome::Diverged { fuel }) => TraceVerdict::ConservativeOverApprox {
            reason: format!(
                "{} exhausted step fuel ({fuel}) while {} produced {ref_out:?}",
                candidate.authority, reference.authority
            ),
            ub_refutation_disallowed: true,
            undeclared_ub_fault: false,
        },
        // Reference hit UB, Lean refused capture/unsupported -> conservative
        // (does not accept UB).
        (TerminalOutcome::FaultUb { detail }, TerminalOutcome::CaptureRefused { reason }) => {
            if let Some(gap_spec) = disclosed_gap
                && gap_spec.matches_lean_outcome(&candidate.outcome)
            {
                TraceVerdict::DisclosedGapArtifact {
                    gap: gap_spec.kind,
                    detail: format!(
                        "{} reported UB ({detail}) while {} refused ({reason})",
                        reference.authority, candidate.authority
                    ),
                }
            } else {
                TraceVerdict::ConservativeOverApprox {
                    reason: format!(
                        "{} reported UB ({detail}); {} conservatively refused/unsupported ({reason})",
                        reference.authority, candidate.authority
                    ),
                    ub_refutation_disallowed: true,
                    undeclared_ub_fault: false,
                }
            }
        }
        // CRITICAL P0: Reference hit UB, candidate accepted!
        (TerminalOutcome::FaultUb { detail }, _) => TraceVerdict::UnsoundAccept {
            detail: format!(
                "{} detected UB ({detail}) while {} accepted with {:?}",
                reference.authority, candidate.authority, candidate.outcome
            ),
        },
        // Reference succeeded/unwound/aborted, candidate refused capture or
        // faulted `.unsupported`.
        (ref_out, TerminalOutcome::CaptureRefused { reason }) if ref_out.is_accepting() => {
            if let Some(gap_spec) = disclosed_gap
                && gap_spec.matches_lean_outcome(&candidate.outcome)
            {
                TraceVerdict::DisclosedGapArtifact { gap: gap_spec.kind, detail: reason.clone() }
            } else {
                TraceVerdict::ConservativeOverApprox {
                    reason: format!(
                        "{} succeeded ({ref_out:?}) while {} conservatively refused/unsupported: {reason}",
                        reference.authority, candidate.authority
                    ),
                    ub_refutation_disallowed: true,
                    undeclared_ub_fault: false,
                }
            }
        }
        // Reference succeeded, candidate faulted `.undefined` -> allowed only
        // when `disclosed_gap` matches the specific boundary fault
        // (`docs/testing-architecture.md` §4.2); unmatched or undeclared UB
        // faults set `undeclared_ub_fault: true` and fail CI gates so
        // completeness regressions are never masked.
        (ref_out, TerminalOutcome::FaultUb { detail }) if ref_out.is_accepting() => {
            if let Some(gap_spec) = disclosed_gap
                && gap_spec.matches_lean_outcome(&candidate.outcome)
            {
                TraceVerdict::DisclosedGapArtifact {
                    gap: gap_spec.kind,
                    detail: format!(
                        "{} accepted ({ref_out:?}) while {} faulted declared conservative gap ({detail})",
                        reference.authority, candidate.authority
                    ),
                }
            } else {
                TraceVerdict::ConservativeOverApprox {
                    reason: format!(
                        "{} accepted ({ref_out:?}) while {} faulted undeclared UB ({detail})",
                        reference.authority, candidate.authority
                    ),
                    ub_refutation_disallowed: true,
                    undeclared_ub_fault: true,
                }
            }
        }
        // Both accepted: require exact outcome and spine parity.
        (ref_out, cand_out) => {
            let outcome_matches =
                if candidate.post_only_mem_digest && !reference.post_only_mem_digest {
                    ref_out.semantically_eq_post_only(cand_out)
                } else {
                    ref_out.semantically_eq(cand_out)
                };
            if !outcome_matches {
                return TraceVerdict::UnsoundAccept {
                    detail: format!(
                        "terminal outcome mismatch: {}={ref_out:?} vs {}={cand_out:?}",
                        reference.authority, candidate.authority
                    ),
                };
            }
            if let Err(msg) = compare_spines(
                &reference.authority,
                &reference.spine,
                &candidate.authority,
                &candidate.spine,
                spine_mode,
            ) {
                return TraceVerdict::UnsoundAccept { detail: msg };
            }
            TraceVerdict::Agree
        }
    }
}

/// Compute lowercase 64-char SHA-256 hex digest of `bytes`.
pub fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(64);
    for b in digest {
        let _ = write!(hex, "{b:02x}");
    }
    hex
}
