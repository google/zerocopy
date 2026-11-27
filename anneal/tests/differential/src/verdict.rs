// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Verdict algebra, canonical MIR value representation, and red-flag guards
//! for the Stage-1 and Stage-2 multi-leg differential oracle.

use std::fmt;

use serde::{Deserialize, Serialize};

/// Canonical integer widths and signedness admitted in Profile v1 (`x86_64`).
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
    /// Bit width on the Stage-1 pinned target (`x86_64`, 64-bit pointer width).
    pub const fn bits(self) -> u32 {
        match self {
            Self::U8 | Self::I8 => 8,
            Self::U16 | Self::I16 => 16,
            Self::U32 | Self::I32 => 32,
            Self::U64 | Self::I64 | Self::Usize | Self::Isize => 64,
            Self::U128 | Self::I128 => 128,
        }
    }

    pub const fn is_signed(self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::I128 | Self::Isize)
    }

    pub const fn mask(self) -> u128 {
        match self.bits() {
            128 => u128::MAX,
            n => (1u128 << n) - 1,
        }
    }

    pub const fn rust_name(self) -> &'static str {
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

    pub const fn lean_width(self) -> &'static str {
        match self {
            Self::U8 | Self::I8 => ".i8",
            Self::U16 | Self::I16 => ".i16",
            Self::U32 | Self::I32 => ".i32",
            Self::U64 | Self::I64 => ".i64",
            Self::U128 | Self::I128 => ".i128",
            Self::Usize | Self::Isize => ".isize",
        }
    }

    pub fn parse_rust_name(raw: &str) -> Result<Self, String> {
        match raw.trim() {
            "u8" => Ok(Self::U8),
            "u16" => Ok(Self::U16),
            "u32" => Ok(Self::U32),
            "u64" => Ok(Self::U64),
            "u128" => Ok(Self::U128),
            "usize" => Ok(Self::Usize),
            "i8" => Ok(Self::I8),
            "i16" => Ok(Self::I16),
            "i32" => Ok(Self::I32),
            "i64" => Ok(Self::I64),
            "i128" => Ok(Self::I128),
            "isize" => Ok(Self::Isize),
            other => Err(format!("unknown integer kind {other:?}")),
        }
    }

    pub fn from_lean_parts(width: &str, signed: bool) -> Result<Self, String> {
        match (width, signed) {
            ("i8", false) => Ok(Self::U8),
            ("i8", true) => Ok(Self::I8),
            ("i16", false) => Ok(Self::U16),
            ("i16", true) => Ok(Self::I16),
            ("i32", false) => Ok(Self::U32),
            ("i32", true) => Ok(Self::I32),
            ("i64", false) => Ok(Self::U64),
            ("i64", true) => Ok(Self::I64),
            ("i128", false) => Ok(Self::U128),
            ("i128", true) => Ok(Self::I128),
            ("isize", false) => Ok(Self::Usize),
            ("isize", true) => Ok(Self::Isize),
            _ => Err(format!("invalid Lean scalar descriptor ({width:?}, signed={signed})")),
        }
    }

    pub const fn to_signed_i128(self, bits: u128) -> i128 {
        let masked = bits & self.mask();
        let shift = 128 - self.bits();
        ((masked << shift) as i128) >> shift
    }

    /// Parse a decimal literal into canonical low `bits`, rejecting overflow.
    pub fn parse_decimal_bits(self, raw: &str) -> Result<u128, String> {
        let s = raw.trim();
        if self.is_signed() {
            let parsed = s
                .parse::<i128>()
                .map_err(|e| format!("invalid {} literal {raw:?}: {e}", self.rust_name()))?;
            let min = match self.bits() {
                128 => i128::MIN,
                n => -(1i128 << (n - 1)),
            };
            let max = match self.bits() {
                128 => i128::MAX,
                n => (1i128 << (n - 1)) - 1,
            };
            if parsed < min || parsed > max {
                return Err(format!(
                    "literal {parsed} out of range [{min}..={max}] for {}",
                    self.rust_name()
                ));
            }
            Ok((parsed as u128) & self.mask())
        } else {
            let parsed = s
                .parse::<u128>()
                .map_err(|e| format!("invalid {} literal {raw:?}: {e}", self.rust_name()))?;
            if parsed > self.mask() {
                return Err(format!(
                    "literal {parsed} exceeds {} max {}",
                    self.rust_name(),
                    self.mask()
                ));
            }
            Ok(parsed)
        }
    }

    /// Format canonical bits as decimal matching the integer's signedness.
    pub fn format_decimal(self, bits: u128) -> String {
        if self.is_signed() {
            self.to_signed_i128(bits).to_string()
        } else {
            (bits & self.mask()).to_string()
        }
    }

    /// Format a valid Rust literal expression with explicit type suffix.
    pub fn format_rust_literal(self, bits: u128) -> String {
        if self.is_signed() {
            let signed = self.to_signed_i128(bits);
            match self {
                Self::I8 if signed == i8::MIN as i128 => return "i8::MIN".to_owned(),
                Self::I16 if signed == i16::MIN as i128 => return "i16::MIN".to_owned(),
                Self::I32 if signed == i32::MIN as i128 => return "i32::MIN".to_owned(),
                Self::I64 if signed == i64::MIN as i128 => return "i64::MIN".to_owned(),
                Self::I128 if signed == i128::MIN => return "i128::MIN".to_owned(),
                Self::Isize if signed == i64::MIN as i128 => return "isize::MIN".to_owned(),
                _ => {}
            }
            format!("({signed}{})", self.rust_name())
        } else {
            format!("{}{}", bits & self.mask(), self.rust_name())
        }
    }

    pub fn to_lean_scalar(self, bits: u128) -> String {
        let masked = bits & self.mask();
        let signed = if self.is_signed() { "true" } else { "false" };
        format!("⟨{}, {}, BitVec.ofNat 128 {}⟩", self.lean_width(), signed, masked)
    }

    pub fn to_mir_eval_arg(self, bits: u128) -> String {
        format!("{}:{}", self.rust_name(), self.format_decimal(bits))
    }
}

/// Canonical `core::cmp::Ordering` runtime value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OrderingKind {
    Less,
    Equal,
    Greater,
}

impl OrderingKind {
    pub fn parse(raw: &str) -> Result<Self, String> {
        match raw.trim().to_ascii_lowercase().as_str() {
            "less" => Ok(Self::Less),
            "equal" => Ok(Self::Equal),
            "greater" => Ok(Self::Greater),
            _ => Err(format!("invalid Ordering value {raw:?}")),
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Less => "less",
            Self::Equal => "equal",
            Self::Greater => "greater",
        }
    }

    pub const fn to_lean_val(self) -> &'static str {
        match self {
            Self::Less => ".ordering .less",
            Self::Equal => ".ordering .equal",
            Self::Greater => ".ordering .greater",
        }
    }

    pub const fn to_rust_expr(self) -> &'static str {
        match self {
            Self::Less => "core::cmp::Ordering::Less",
            Self::Equal => "core::cmp::Ordering::Equal",
            Self::Greater => "core::cmp::Ordering::Greater",
        }
    }
}

/// Canonical Profile v1 runtime boundary value comparable across all legs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum MirValue {
    Int {
        int_kind: IntKind,
        /// Low `int_kind.bits()` canonically masked in decimal or `u128`.
        #[serde(serialize_with = "serialize_u128_str", deserialize_with = "deserialize_u128_str")]
        bits: u128,
    },
    Bool {
        value: bool,
    },
    Char {
        scalar: u32,
    },
    Ordering {
        value: OrderingKind,
    },
    Unit,
    OverflowPair {
        int_kind: IntKind,
        #[serde(serialize_with = "serialize_u128_str", deserialize_with = "deserialize_u128_str")]
        bits: u128,
        overflow: bool,
    },
    Enum {
        enum_type: String,
        variant: String,
        variant_index: usize,
    },
}

fn serialize_u128_str<S: serde::Serializer>(val: &u128, ser: S) -> Result<S::Ok, S::Error> {
    ser.serialize_str(&val.to_string())
}

fn deserialize_u128_str<'de, D: serde::Deserializer<'de>>(de: D) -> Result<u128, D::Error> {
    let raw = String::deserialize(de)?;
    raw.parse::<u128>().map_err(serde::de::Error::custom)
}

impl fmt::Display for MirValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int { int_kind, bits } => {
                write!(f, "{}:{}", int_kind.rust_name(), int_kind.format_decimal(*bits))
            }
            Self::Bool { value } => write!(f, "bool:{value}"),
            Self::Char { scalar } => write!(f, "char:U+{scalar:04X}"),
            Self::Ordering { value } => write!(f, "ordering:{}", value.as_str()),
            Self::Unit => f.write_str("unit:()"),
            Self::OverflowPair { int_kind, bits, overflow } => {
                write!(f, "({}, {})", int_kind.format_rust_literal(*bits), overflow)
            }
            Self::Enum { enum_type, variant, variant_index } => {
                write!(f, "{enum_type}::{variant}#v{variant_index}")
            }
        }
    }
}

/// Normalized execution outcome from a single oracle leg.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ObservedOutcome {
    Returned { value: MirValue },
    UndefinedBehavior { detail: String },
    InitUnsupported { detail: String },
    Unsupported { detail: String },
    Unwound { detail: String },
    AbnormalAbort { detail: String },
    Panic { detail: String },
    OutOfFuel { detail: String },
    ToolError { detail: String },
}

/// Expected semantic polarity declared by a corpus case.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Expectation {
    Pass,
    Ub,
    UnsupportedControl,
}

/// Optional pin on Miri's concrete reference outcome for `unsupported_control`
/// cases so CLI runs verify Miri behaves as expected rather than masking an
/// unexpected abort/UB/return flip.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExpectedMiriOutcome {
    Returned,
    Ub,
    AbnormalAbort,
    Panic,
    Unsupported,
}

impl ExpectedMiriOutcome {
    pub const fn matches_outcome(self, miri: &ObservedOutcome) -> bool {
        matches!(
            (self, miri),
            (Self::Returned, ObservedOutcome::Returned { .. })
                | (Self::Ub, ObservedOutcome::UndefinedBehavior { .. })
                | (Self::AbnormalAbort, ObservedOutcome::AbnormalAbort { .. })
                | (Self::Panic, ObservedOutcome::Panic { .. })
                | (Self::Unsupported, ObservedOutcome::Unsupported { .. })
        )
    }
}

/// Stage-1 multi-leg differential oracle verdict for a single litmus case.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Verdict {
    AgreeValue { value: MirValue },
    AgreeUndefinedBehavior,
    SoundConservativeAbstraction { miri: Box<ObservedOutcome>, lean_detail: String },
    UnsoundMissedFault { miri: Box<ObservedOutcome>, lean: Box<ObservedOutcome> },
    ValueMismatch { expected: Option<MirValue>, miri: MirValue, lean: Box<ObservedOutcome> },
    ConservativeRejection { detail: String },
    LegDivergence { detail: String },
}

impl Verdict {
    /// Whether this verdict is admitted by the Stage-1 oracle gate.
    pub const fn is_ok(&self) -> bool {
        matches!(
            self,
            Self::AgreeValue { .. }
                | Self::AgreeUndefinedBehavior
                | Self::SoundConservativeAbstraction { .. }
        )
    }

    pub const fn label(&self) -> &'static str {
        match self {
            Self::AgreeValue { .. } => "AgreeValue",
            Self::AgreeUndefinedBehavior => "AgreeUndefinedBehavior",
            Self::SoundConservativeAbstraction { .. } => "SoundConservativeAbstraction",
            Self::UnsoundMissedFault { .. } => "UnsoundMissedFault",
            Self::ValueMismatch { .. } => "ValueMismatch",
            Self::ConservativeRejection { .. } => "ConservativeRejection",
            Self::LegDivergence { .. } => "LegDivergence",
        }
    }
}

/// Compare all active oracle legs against a case's declared expectation.
///
/// Soundness invariants enforced unconditionally:
/// - Primary Miri-versus-Lean failures (`UnsoundMissedFault`, `ValueMismatch`,
///   `ConservativeRejection`, and reference `LegDivergence`) take precedence
///   over optional Leg 3 (`mir_eval`) comparisons so secondary Leg 3
///   disagreements never mask a missed UB/fault or value mismatch in Lean.
/// - Any `Returned` value from Lean when Miri observed `UndefinedBehavior`,
///   `AbnormalAbort`, `Panic`, or `Unwound` is classified as
///   [`Verdict::UnsoundMissedFault`].
/// - Once Miri and Lean agree on an admissible primary verdict, any present
///   Leg 3 (`mir_eval`) tool error, fuel exhaustion, or outcome discrepancy
///   against Lean triggers [`Verdict::LegDivergence`].
/// - Step-time `Unsupported` from Lean is admitted as
///   [`Verdict::SoundConservativeAbstraction`] if and only if
///   `expected == Expectation::UnsupportedControl`, Miri completed cleanly
///   without a tooling error, fuel exhaustion, or init failure, and any
///   optional `expected_miri` pin matches; init-time `InitUnsupported` always
///   fails closed so `initStateBy` failures cannot satisfy
///   `unsupported_control`.
/// - When `expected == Expectation::Ub` and `miri_ub_contains` is supplied,
///   Miri's UB headline must contain that substring or the case fails closed
///   with [`Verdict::LegDivergence`].
pub fn evaluate_case(
    expected: Expectation,
    expected_return: Option<&MirValue>,
    miri_ub_contains: Option<&str>,
    expected_miri: Option<ExpectedMiriOutcome>,
    miri: &ObservedOutcome,
    lean: &ObservedOutcome,
    mir_eval: Option<&ObservedOutcome>,
) -> Verdict {
    if let Some(leg_err) = [miri, lean].into_iter().find_map(|o| match o {
        ObservedOutcome::ToolError { detail } => Some(format!("tool error: {detail}")),
        ObservedOutcome::OutOfFuel { detail } => Some(format!("out of fuel: {detail}")),
        _ => None,
    }) {
        return Verdict::LegDivergence { detail: leg_err };
    }

    let primary = match lean {
        ObservedOutcome::Returned { value: lean_val } => match miri {
            ObservedOutcome::UndefinedBehavior { .. }
            | ObservedOutcome::AbnormalAbort { .. }
            | ObservedOutcome::Panic { .. }
            | ObservedOutcome::Unwound { .. } => Verdict::UnsoundMissedFault {
                miri: Box::new(miri.clone()),
                lean: Box::new(lean.clone()),
            },
            ObservedOutcome::Returned { value: miri_val } => {
                if expected != Expectation::Pass {
                    Verdict::LegDivergence {
                        detail: format!(
                            "expected {expected:?} but both Miri and Lean returned {miri_val}"
                        ),
                    }
                } else if lean_val != miri_val {
                    Verdict::ValueMismatch {
                        expected: expected_return.cloned(),
                        miri: miri_val.clone(),
                        lean: Box::new(lean.clone()),
                    }
                } else if let Some(exp) = expected_return
                    && miri_val != exp
                {
                    Verdict::ValueMismatch {
                        expected: Some(exp.clone()),
                        miri: miri_val.clone(),
                        lean: Box::new(lean.clone()),
                    }
                } else {
                    Verdict::AgreeValue { value: miri_val.clone() }
                }
            }
            other => Verdict::LegDivergence {
                detail: format!("Miri reported {other:?} while Lean returned {lean_val}"),
            },
        },
        ObservedOutcome::UndefinedBehavior { detail: lean_detail } => match miri {
            ObservedOutcome::UndefinedBehavior { detail: miri_detail } => {
                if expected != Expectation::Ub {
                    Verdict::LegDivergence {
                        detail: format!(
                            "both legs hit UB ({lean_detail}) on non-UB case (expected {expected:?})"
                        ),
                    }
                } else if let Some(needle) = miri_ub_contains
                    && !miri_detail.contains(needle)
                {
                    Verdict::LegDivergence {
                        detail: format!(
                            "Miri UB headline {miri_detail:?} missed expected cause substring {needle:?}"
                        ),
                    }
                } else {
                    Verdict::AgreeUndefinedBehavior
                }
            }
            ObservedOutcome::Returned { value: miri_val } => Verdict::LegDivergence {
                detail: format!(
                    "false-positive UB in Lean ({lean_detail}) where Miri returned {miri_val}"
                ),
            },
            other => Verdict::LegDivergence {
                detail: format!("Lean reported UB ({lean_detail}) while Miri reported {other:?}"),
            },
        },
        ObservedOutcome::InitUnsupported { detail } => Verdict::LegDivergence {
            detail: format!(
                "Lean initStateBy rejected inputs before stepping (expected={expected:?}): {detail}"
            ),
        },
        ObservedOutcome::Unsupported { detail } => {
            if expected == Expectation::UnsupportedControl {
                match miri {
                    ObservedOutcome::Returned { .. }
                    | ObservedOutcome::UndefinedBehavior { .. }
                    | ObservedOutcome::AbnormalAbort { .. }
                    | ObservedOutcome::Panic { .. }
                    | ObservedOutcome::Unwound { .. }
                    | ObservedOutcome::Unsupported { .. } => {
                        if let Some(pin) = expected_miri
                            && !pin.matches_outcome(miri)
                        {
                            Verdict::LegDivergence {
                                detail: format!(
                                    "expected Miri outcome {pin:?} on unsupported_control case, got {miri:?}"
                                ),
                            }
                        } else {
                            Verdict::SoundConservativeAbstraction {
                                miri: Box::new(miri.clone()),
                                lean_detail: detail.clone(),
                            }
                        }
                    }
                    other => Verdict::LegDivergence {
                        detail: format!("unexpected Miri state on unsupported control: {other:?}"),
                    },
                }
            } else {
                Verdict::ConservativeRejection {
                    detail: format!(
                        "disallowed step-time .unsupported rejection (expected={expected:?}): {detail}"
                    ),
                }
            }
        }
        ObservedOutcome::AbnormalAbort { detail }
        | ObservedOutcome::Panic { detail }
        | ObservedOutcome::Unwound { detail } => Verdict::LegDivergence {
            detail: format!(
                "unexpected unwind outcome (expected={expected:?}, lean={detail}, miri={miri:?})"
            ),
        },
        other => {
            Verdict::LegDivergence { detail: format!("unexpected Lean outcome state: {other:?}") }
        }
    };

    if !primary.is_ok() {
        return primary;
    }

    if let Some(eval_outcome) = mir_eval {
        match eval_outcome {
            ObservedOutcome::ToolError { detail } => {
                return Verdict::LegDivergence { detail: format!("tool error: {detail}") };
            }
            ObservedOutcome::OutOfFuel { detail } => {
                return Verdict::LegDivergence { detail: format!("out of fuel: {detail}") };
            }
            _ if !outcomes_agree_mir(lean, eval_outcome) => {
                return Verdict::LegDivergence {
                    detail: format!(
                        "Leg 2 (Lean StepCore) and Leg 3 (anneal-mir-eval) disagreed: lean={lean:?}, mir_eval={eval_outcome:?}"
                    ),
                };
            }
            _ => {}
        }
    }

    primary
}

pub(crate) fn outcomes_agree_mir(lean: &ObservedOutcome, mir_eval: &ObservedOutcome) -> bool {
    match (lean, mir_eval) {
        (ObservedOutcome::Returned { value: a }, ObservedOutcome::Returned { value: b }) => a == b,
        (ObservedOutcome::UndefinedBehavior { .. }, ObservedOutcome::UndefinedBehavior { .. }) => {
            true
        }
        // `anneal-mir-eval` maps init unsupported to `FaultKind::Unsupported`;
        // keeping `InitUnsupported` distinct here prevents init rejection from
        // passing `evaluate_case` later (step 3 rejects it unconditionally).
        (ObservedOutcome::InitUnsupported { .. }, ObservedOutcome::Unsupported { .. })
        | (ObservedOutcome::Unsupported { .. }, ObservedOutcome::Unsupported { .. }) => true,
        (ObservedOutcome::OutOfFuel { .. }, ObservedOutcome::OutOfFuel { .. }) => true,
        (
            ObservedOutcome::Unwound { .. } | ObservedOutcome::Panic { .. },
            ObservedOutcome::Unwound { .. } | ObservedOutcome::Panic { .. },
        ) => true,
        (ObservedOutcome::AbnormalAbort { .. }, ObservedOutcome::AbnormalAbort { .. }) => true,
        _ => false,
    }
}

/// Summary metrics and red-flag checks over a full differential suite run.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SuiteMetrics {
    pub compared_count: usize,
    pub pass_agreed_count: usize,
    pub ub_agreed_count: usize,
    pub conservative_unsupported_count: usize,
    pub kernel_checked_pass_count: usize,
    pub kernel_checked_ub_count: usize,
    pub unsound_missed_fault_count: usize,
    pub value_mismatch_count: usize,
    pub unexpected_conservative_count: usize,
    pub leg_divergence_count: usize,
}

impl SuiteMetrics {
    /// Summarize case verdicts paired with whether each case passed a Lean
    /// kernel proof theorem (`wpProg_of_evalMirFuelTotal` /
    /// `wpFaultProg_of_evalMirFuelTotal`).
    pub fn from_outcomes<'a>(items: impl IntoIterator<Item = (&'a Verdict, bool)>) -> Self {
        let mut out = Self {
            compared_count: 0,
            pass_agreed_count: 0,
            ub_agreed_count: 0,
            conservative_unsupported_count: 0,
            kernel_checked_pass_count: 0,
            kernel_checked_ub_count: 0,
            unsound_missed_fault_count: 0,
            value_mismatch_count: 0,
            unexpected_conservative_count: 0,
            leg_divergence_count: 0,
        };
        for (v, kernel_checked) in items {
            out.compared_count += 1;
            match v {
                Verdict::AgreeValue { .. } => {
                    out.pass_agreed_count += 1;
                    if kernel_checked {
                        out.kernel_checked_pass_count += 1;
                    }
                }
                Verdict::AgreeUndefinedBehavior => {
                    out.ub_agreed_count += 1;
                    if kernel_checked {
                        out.kernel_checked_ub_count += 1;
                    }
                }
                Verdict::SoundConservativeAbstraction { .. } => {
                    out.conservative_unsupported_count += 1;
                }
                Verdict::UnsoundMissedFault { .. } => out.unsound_missed_fault_count += 1,
                Verdict::ValueMismatch { .. } => out.value_mismatch_count += 1,
                Verdict::ConservativeRejection { .. } => {
                    out.unexpected_conservative_count += 1;
                }
                Verdict::LegDivergence { .. } => out.leg_divergence_count += 1,
            }
        }
        out
    }

    /// Enforce anti-vacuity red flags preventing empty, UB-free, or
    /// kernel-unchecked runs.
    pub fn check_red_flags(&self) -> Result<usize, String> {
        let mut checks_passed = 0usize;
        if self.compared_count == 0 {
            return Err("red flag: compared_count == 0 (vacuous suite)".to_owned());
        }
        checks_passed += 1;
        if self.pass_agreed_count == 0 {
            return Err("red flag: pass_agreed_count == 0 (no verified pass cases)".to_owned());
        }
        checks_passed += 1;
        if self.ub_agreed_count == 0 {
            return Err("red flag: ub_agreed_count == 0 (no caught UB cases)".to_owned());
        }
        checks_passed += 1;
        if self.conservative_unsupported_count == 0 {
            return Err(
                "red flag: conservative_unsupported_count == 0 (no conservative control cases)"
                    .to_owned(),
            );
        }
        checks_passed += 1;
        if self.kernel_checked_pass_count == 0 {
            return Err(
                "red flag: kernel_checked_pass_count == 0 (no kernel-checked pass theorems)"
                    .to_owned(),
            );
        }
        checks_passed += 1;
        if self.kernel_checked_ub_count == 0 {
            return Err(
                "red flag: kernel_checked_ub_count == 0 (no kernel-checked UB theorems)".to_owned()
            );
        }
        checks_passed += 1;
        if self.unsound_missed_fault_count > 0
            || self.value_mismatch_count > 0
            || self.unexpected_conservative_count > 0
            || self.leg_divergence_count > 0
        {
            return Err(format!(
                "red flag: failing verdicts present (unsound={}, mismatch={}, conservative_rej={}, leg_div={})",
                self.unsound_missed_fault_count,
                self.value_mismatch_count,
                self.unexpected_conservative_count,
                self.leg_divergence_count
            ));
        }
        checks_passed += 1;
        Ok(checks_passed)
    }
}

/// Canonical terminal execution outcome shared across Leg 0 (`rustc`), Leg 1
/// (Miri), Leg 2 (Lean `MirSemantics`), and optional Leg 3 (`anneal-mir-eval`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TerminalOutcome {
    Returned { value: MirValue },
    Unwound { detail: String },
    Aborted { detail: String },
    UndefinedBehavior { detail: String },
    Unsupported { detail: String },
    OutOfFuel { detail: String },
}

impl ObservedOutcome {
    /// Project an [`ObservedOutcome`] onto its canonical [`TerminalOutcome`],
    /// returning `Err(detail)` for infrastructure
    /// [`ObservedOutcome::ToolError`].
    pub fn to_terminal_outcome(&self) -> Result<TerminalOutcome, String> {
        match self {
            Self::Returned { value } => Ok(TerminalOutcome::Returned { value: value.clone() }),
            Self::Panic { detail } | Self::Unwound { detail } => {
                Ok(TerminalOutcome::Unwound { detail: detail.clone() })
            }
            Self::AbnormalAbort { detail } => {
                Ok(TerminalOutcome::Aborted { detail: detail.clone() })
            }
            Self::UndefinedBehavior { detail } => {
                Ok(TerminalOutcome::UndefinedBehavior { detail: detail.clone() })
            }
            Self::Unsupported { detail } | Self::InitUnsupported { detail } => {
                Ok(TerminalOutcome::Unsupported { detail: detail.clone() })
            }
            Self::OutOfFuel { detail } => Ok(TerminalOutcome::OutOfFuel { detail: detail.clone() }),
            Self::ToolError { detail } => Err(detail.clone()),
        }
    }
}

/// Four-way Stage-2 differential oracle agreement / failure classification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OracleAgreementClass {
    /// Authority (Miri + compiled `rustc` on UB-free cases) and Lean agree on
    /// the exact [`TerminalOutcome`], including `UB == UB` and
    /// `Unwound == Unwound`.
    BiFaultEquivAgreement,
    /// Authority completes or faults while Lean conservatively faults
    /// (`Unsupported`, `OutOfFuel`, or false-positive `UndefinedBehavior`).
    /// Preserves universal forward-simulation safety (`WellFormed` soundness)
    /// but does NOT certify existential UB refutation / bi-fault equivalence.
    ConservativeOverApproxForwardSimOnly,
    /// P0 hard soundness failure: authority faults (UB/panic/abort) or returns
    /// `v1`, while Lean accepts or returns `v2 != v1` (or mismatches unwind vs
    /// abort/return). Never suppressible as a disclosed gap.
    UnsoundAcceptCritical,
    /// Hard authority/infrastructure failure: compiled `rustc` disagrees with
    /// Miri on a UB-free case, optional `anneal-mir-eval` disagrees with Lean
    /// on an admitted case, `initStateBy` rejects a captured body, or an oracle
    /// leg hit a tool error.
    AuthorityDisagreement,
}

impl OracleAgreementClass {
    /// Whether this class is a hard failure that must fail CI and trigger
    /// counterexample shrinking.
    pub const fn is_hard_failure(self) -> bool {
        matches!(self, Self::UnsoundAcceptCritical | Self::AuthorityDisagreement)
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::BiFaultEquivAgreement => "bi_fault_equiv_agreement",
            Self::ConservativeOverApproxForwardSimOnly => {
                "conservative_over_approx_forward_sim_only"
            }
            Self::UnsoundAcceptCritical => "unsound_accept_critical",
            Self::AuthorityDisagreement => "authority_disagreement",
        }
    }
}

/// Explicit model/scope boundary classification for conservative gaps.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DisclosedGapKind {
    SelectedUnitScope,
    CallerRawPtrAliasing,
    UnbridgedSemantics,
    FuelExhausted,
}

impl DisclosedGapKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SelectedUnitScope => "selected_unit_scope",
            Self::CallerRawPtrAliasing => "caller_raw_ptr_aliasing",
            Self::UnbridgedSemantics => "unbridged_semantics",
            Self::FuelExhausted => "fuel_exhausted",
        }
    }
}

/// Result of cross-checking Leg 0 compiled host `rustc` against Leg 1 Miri.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum RustcCheckStatus {
    NotRun,
    Agreed,
    /// Strict UB authority rule: Miri observed UB, so compiled host `rustc`
    /// output is informational only and never treated as an authority conflict.
    IgnoredDueToMiriUb,
    Disagreement {
        detail: String,
    },
}

/// Full Stage-2 multi-leg evaluation result for a single generated case.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FuzzCaseEvaluation {
    pub agreement: OracleAgreementClass,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub disclosed_gap: Option<DisclosedGapKind>,
    pub rustc_status: RustcCheckStatus,
    #[serde(default)]
    pub is_spurious_lean_ub: bool,
    pub detail: String,
}

impl FuzzCaseEvaluation {
    /// Whether this case violates zero-tolerance gates
    /// (`UnsoundAcceptCritical`, `AuthorityDisagreement`, or spurious Lean UB
    /// on UB-free execution) and must fail CI and trigger counterexample
    /// shrinking.
    pub const fn is_shrinkable_failure(&self) -> bool {
        self.agreement.is_hard_failure() || self.is_spurious_lean_ub
    }
}

fn check_rustc_against_miri(
    miri: &ObservedOutcome,
    rustc: Option<&ObservedOutcome>,
    rustc_leg_active: bool,
) -> RustcCheckStatus {
    if matches!(miri, ObservedOutcome::UndefinedBehavior { .. })
        && (rustc_leg_active || rustc.is_some())
    {
        return RustcCheckStatus::IgnoredDueToMiriUb;
    }
    let Some(rustc_out) = rustc else {
        return RustcCheckStatus::NotRun;
    };
    let miri_term = match miri.to_terminal_outcome() {
        Ok(t) => t,
        Err(detail) => {
            return RustcCheckStatus::Disagreement {
                detail: format!("cannot compare rustc against Miri tool error: {detail}"),
            };
        }
    };
    let rustc_term = match rustc_out.to_terminal_outcome() {
        Ok(t) => t,
        Err(detail) => {
            return RustcCheckStatus::Disagreement {
                detail: format!("compiled rustc tool error on UB-free case: {detail}"),
            };
        }
    };
    match (&miri_term, &rustc_term) {
        (TerminalOutcome::Returned { value: m }, TerminalOutcome::Returned { value: r }) => {
            if m == r {
                RustcCheckStatus::Agreed
            } else {
                RustcCheckStatus::Disagreement {
                    detail: format!(
                        "compiled rustc returned {r} while Miri returned {m} on UB-free case"
                    ),
                }
            }
        }
        (TerminalOutcome::Unwound { .. }, TerminalOutcome::Unwound { .. })
        | (TerminalOutcome::Aborted { .. }, TerminalOutcome::Aborted { .. }) => {
            RustcCheckStatus::Agreed
        }
        _ => RustcCheckStatus::Disagreement {
            detail: format!(
                "compiled rustc outcome {rustc_term:?} disagreed with Miri {miri_term:?} on UB-free case"
            ),
        },
    }
}

/// Evaluate a Stage-2 fuzz case across Leg 0 (`rustc`), Leg 1 (`miri`),
/// Leg 2 (captured Lean `StepCore`), and optional Leg 3 (`anneal-mir-eval`).
pub fn evaluate_fuzz_case(
    miri: &ObservedOutcome,
    lean: &ObservedOutcome,
    rustc: Option<&ObservedOutcome>,
    mir_eval: Option<&ObservedOutcome>,
    capture_rejected: Option<&str>,
) -> FuzzCaseEvaluation {
    evaluate_fuzz_case_with_rustc_leg(miri, lean, rustc, mir_eval, capture_rejected, false)
}

/// Variant of [`evaluate_fuzz_case`] aware of whether Leg 0 (`rustc`) is
/// enabled for the campaign so Miri-established UB skipped before host
/// execution records [`RustcCheckStatus::IgnoredDueToMiriUb`].
pub fn evaluate_fuzz_case_with_rustc_leg(
    miri: &ObservedOutcome,
    lean: &ObservedOutcome,
    rustc: Option<&ObservedOutcome>,
    mir_eval: Option<&ObservedOutcome>,
    capture_rejected: Option<&str>,
    rustc_leg_active: bool,
) -> FuzzCaseEvaluation {
    let rustc_status = check_rustc_against_miri(miri, rustc, rustc_leg_active);

    let miri_term = match miri.to_terminal_outcome() {
        Ok(t) => t,
        Err(detail) => {
            return FuzzCaseEvaluation {
                agreement: OracleAgreementClass::AuthorityDisagreement,
                disclosed_gap: None,
                rustc_status,
                is_spurious_lean_ub: false,
                detail: format!("Miri tool error: {detail}"),
            };
        }
    };

    if let RustcCheckStatus::Disagreement { detail } = &rustc_status {
        return FuzzCaseEvaluation {
            agreement: OracleAgreementClass::AuthorityDisagreement,
            disclosed_gap: None,
            rustc_status: rustc_status.clone(),
            is_spurious_lean_ub: false,
            detail: detail.clone(),
        };
    }

    if let TerminalOutcome::Unsupported { detail } | TerminalOutcome::OutOfFuel { detail } =
        &miri_term
    {
        return FuzzCaseEvaluation {
            agreement: OracleAgreementClass::AuthorityDisagreement,
            disclosed_gap: None,
            rustc_status,
            is_spurious_lean_ub: false,
            detail: format!("Miri authority could not evaluate case: {detail}"),
        };
    }

    if let Some(cap_err) = capture_rejected {
        return FuzzCaseEvaluation {
            agreement: OracleAgreementClass::ConservativeOverApproxForwardSimOnly,
            disclosed_gap: Some(DisclosedGapKind::UnbridgedSemantics),
            rustc_status,
            is_spurious_lean_ub: false,
            detail: format!("capture refused candidate fail-closed: {cap_err}"),
        };
    }

    if let ObservedOutcome::InitUnsupported { detail } = lean {
        return FuzzCaseEvaluation {
            agreement: OracleAgreementClass::AuthorityDisagreement,
            disclosed_gap: None,
            rustc_status,
            is_spurious_lean_ub: false,
            detail: format!("Lean initStateBy rejected captured body before stepping: {detail}"),
        };
    }

    let lean_term = match lean.to_terminal_outcome() {
        Ok(t) => t,
        Err(detail) => {
            return FuzzCaseEvaluation {
                agreement: OracleAgreementClass::AuthorityDisagreement,
                disclosed_gap: None,
                rustc_status,
                is_spurious_lean_ub: false,
                detail: format!("Lean tool error: {detail}"),
            };
        }
    };

    let primary = match (&miri_term, &lean_term) {
        (TerminalOutcome::Returned { value: mv }, TerminalOutcome::Returned { value: lv }) => {
            if mv == lv {
                FuzzCaseEvaluation {
                    agreement: OracleAgreementClass::BiFaultEquivAgreement,
                    disclosed_gap: None,
                    rustc_status: rustc_status.clone(),
                    is_spurious_lean_ub: false,
                    detail: format!("exact value agreement: {mv}"),
                }
            } else {
                FuzzCaseEvaluation {
                    agreement: OracleAgreementClass::UnsoundAcceptCritical,
                    disclosed_gap: None,
                    rustc_status: rustc_status.clone(),
                    is_spurious_lean_ub: false,
                    detail: format!("value mismatch: Miri returned {mv}, Lean returned {lv}"),
                }
            }
        }
        (
            TerminalOutcome::UndefinedBehavior { detail: md },
            TerminalOutcome::UndefinedBehavior { detail: ld },
        ) => FuzzCaseEvaluation {
            agreement: OracleAgreementClass::BiFaultEquivAgreement,
            disclosed_gap: None,
            rustc_status: rustc_status.clone(),
            is_spurious_lean_ub: false,
            detail: format!("exact UB agreement: miri={md}; lean={ld}"),
        },
        (TerminalOutcome::Unwound { detail: md }, TerminalOutcome::Unwound { detail: ld }) => {
            FuzzCaseEvaluation {
                agreement: OracleAgreementClass::BiFaultEquivAgreement,
                disclosed_gap: None,
                rustc_status: rustc_status.clone(),
                is_spurious_lean_ub: false,
                detail: format!("exact unwind agreement: miri={md}; lean={ld}"),
            }
        }
        (TerminalOutcome::Aborted { detail: md }, TerminalOutcome::Aborted { detail: ld }) => {
            FuzzCaseEvaluation {
                agreement: OracleAgreementClass::BiFaultEquivAgreement,
                disclosed_gap: None,
                rustc_status: rustc_status.clone(),
                is_spurious_lean_ub: false,
                detail: format!("exact abort agreement: miri={md}; lean={ld}"),
            }
        }
        (
            TerminalOutcome::UndefinedBehavior { detail: md },
            TerminalOutcome::Returned { value: lv },
        ) => FuzzCaseEvaluation {
            agreement: OracleAgreementClass::UnsoundAcceptCritical,
            disclosed_gap: None,
            rustc_status: rustc_status.clone(),
            is_spurious_lean_ub: false,
            detail: format!("P0 unsound missed UB: Miri hit UB ({md}), Lean returned {lv}"),
        },
        (
            TerminalOutcome::UndefinedBehavior { detail: md },
            TerminalOutcome::Unwound { detail: ld } | TerminalOutcome::Aborted { detail: ld },
        ) => FuzzCaseEvaluation {
            agreement: OracleAgreementClass::UnsoundAcceptCritical,
            disclosed_gap: None,
            rustc_status: rustc_status.clone(),
            is_spurious_lean_ub: false,
            detail: format!(
                "P0 unsound missed UB: Miri hit UB ({md}), Lean claimed non-UB termination ({ld})"
            ),
        },
        (
            TerminalOutcome::Unwound { detail: md } | TerminalOutcome::Aborted { detail: md },
            TerminalOutcome::Returned { value: lv },
        ) => FuzzCaseEvaluation {
            agreement: OracleAgreementClass::UnsoundAcceptCritical,
            disclosed_gap: None,
            rustc_status: rustc_status.clone(),
            is_spurious_lean_ub: false,
            detail: format!("P0 unsound missed fault: Miri faulted ({md}), Lean returned {lv}"),
        },
        (TerminalOutcome::Unwound { detail: md }, TerminalOutcome::Aborted { detail: ld })
        | (TerminalOutcome::Aborted { detail: md }, TerminalOutcome::Unwound { detail: ld }) => {
            FuzzCaseEvaluation {
                agreement: OracleAgreementClass::UnsoundAcceptCritical,
                disclosed_gap: None,
                rustc_status: rustc_status.clone(),
                is_spurious_lean_ub: false,
                detail: format!("P0 unwind/abort mismatch: Miri ({md}) disagreed with Lean ({ld})"),
            }
        }
        (
            TerminalOutcome::Returned { value: mv },
            TerminalOutcome::Unwound { detail: ld } | TerminalOutcome::Aborted { detail: ld },
        ) => FuzzCaseEvaluation {
            agreement: OracleAgreementClass::UnsoundAcceptCritical,
            disclosed_gap: None,
            rustc_status: rustc_status.clone(),
            is_spurious_lean_ub: false,
            detail: format!(
                "P0 spurious unwind/abort: Miri returned {mv}, Lean claimed termination ({ld})"
            ),
        },
        (TerminalOutcome::Unsupported { detail } | TerminalOutcome::OutOfFuel { detail }, _) => {
            FuzzCaseEvaluation {
                agreement: OracleAgreementClass::AuthorityDisagreement,
                disclosed_gap: None,
                rustc_status: rustc_status.clone(),
                is_spurious_lean_ub: false,
                detail: format!("Miri authority could not evaluate case: {detail}"),
            }
        }
        (_, TerminalOutcome::OutOfFuel { detail }) => FuzzCaseEvaluation {
            agreement: OracleAgreementClass::ConservativeOverApproxForwardSimOnly,
            disclosed_gap: Some(DisclosedGapKind::FuelExhausted),
            rustc_status: rustc_status.clone(),
            is_spurious_lean_ub: false,
            detail: format!("Lean out of fuel (forward-sim safe only): {detail}"),
        },
        (_, TerminalOutcome::Unsupported { detail }) => FuzzCaseEvaluation {
            agreement: OracleAgreementClass::ConservativeOverApproxForwardSimOnly,
            disclosed_gap: Some(DisclosedGapKind::UnbridgedSemantics),
            rustc_status: rustc_status.clone(),
            is_spurious_lean_ub: false,
            detail: format!("Lean conservative .unsupported (forward-sim safe only): {detail}"),
        },
        (
            TerminalOutcome::Returned { .. }
            | TerminalOutcome::Unwound { .. }
            | TerminalOutcome::Aborted { .. },
            TerminalOutcome::UndefinedBehavior { detail },
        ) => FuzzCaseEvaluation {
            agreement: OracleAgreementClass::ConservativeOverApproxForwardSimOnly,
            disclosed_gap: None,
            rustc_status: rustc_status.clone(),
            is_spurious_lean_ub: true,
            detail: format!("spurious Lean UB on UB-free authority execution: {detail}"),
        },
    };

    // Primary Miri-vs-Lean failures (`UnsoundAcceptCritical` and spurious Lean
    // UB) always take precedence over secondary Leg 3 (`anneal-mir-eval`) so a
    // P0 soundness defect is never downgraded to `AuthorityDisagreement`.
    if primary.is_shrinkable_failure() {
        return primary;
    }

    if let Some(eval_out) = mir_eval {
        if let ObservedOutcome::ToolError { detail } = eval_out {
            return FuzzCaseEvaluation {
                agreement: OracleAgreementClass::AuthorityDisagreement,
                disclosed_gap: None,
                rustc_status,
                is_spurious_lean_ub: false,
                detail: format!("anneal-mir-eval tool error: {detail}"),
            };
        }
        if !outcomes_agree_mir(lean, eval_out) {
            return FuzzCaseEvaluation {
                agreement: OracleAgreementClass::AuthorityDisagreement,
                disclosed_gap: None,
                rustc_status,
                is_spurious_lean_ub: false,
                detail: format!(
                    "Leg 2 (Lean) and Leg 3 (anneal-mir-eval) disagreed: lean={lean:?}, mir_eval={eval_out:?}"
                ),
            };
        }
    }

    primary
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_u32(v: u32) -> MirValue {
        MirValue::Int { int_kind: IntKind::U32, bits: u128::from(v) }
    }

    fn ret_u32(v: u32) -> ObservedOutcome {
        ObservedOutcome::Returned { value: int_u32(v) }
    }

    #[test]
    fn pass_agreement_and_mismatch_classified() {
        let ok = evaluate_case(
            Expectation::Pass,
            Some(&int_u32(42)),
            None,
            None,
            &ret_u32(42),
            &ret_u32(42),
            Some(&ret_u32(42)),
        );
        assert_eq!(ok, Verdict::AgreeValue { value: int_u32(42) });
        assert!(ok.is_ok());

        let mismatch = evaluate_case(
            Expectation::Pass,
            Some(&int_u32(42)),
            None,
            None,
            &ret_u32(42),
            &ret_u32(43),
            None,
        );
        assert!(matches!(mismatch, Verdict::ValueMismatch { .. }));
        assert!(!mismatch.is_ok());

        let leg3_div = evaluate_case(
            Expectation::Pass,
            Some(&int_u32(42)),
            None,
            None,
            &ret_u32(42),
            &ret_u32(42),
            Some(&ret_u32(99)),
        );
        assert!(matches!(leg3_div, Verdict::LegDivergence { .. }));
        assert!(!leg3_div.is_ok());
    }

    #[test]
    fn missed_ub_or_panic_is_unsound() {
        let missed_ub = evaluate_case(
            Expectation::UnsupportedControl,
            None,
            None,
            None,
            &ObservedOutcome::UndefinedBehavior { detail: "div by zero".to_owned() },
            &ret_u32(0),
            None,
        );
        assert!(matches!(missed_ub, Verdict::UnsoundMissedFault { .. }));
        assert!(!missed_ub.is_ok());

        let missed_panic = evaluate_case(
            Expectation::Pass,
            None,
            None,
            None,
            &ObservedOutcome::Panic { detail: "panicked at explicit panic".to_owned() },
            &ret_u32(0),
            None,
        );
        assert!(matches!(missed_panic, Verdict::UnsoundMissedFault { .. }));
        assert!(!missed_panic.is_ok());

        let unexpected_unwind = evaluate_case(
            Expectation::Pass,
            None,
            None,
            None,
            &ObservedOutcome::Panic { detail: "panicked at explicit panic".to_owned() },
            &ObservedOutcome::AbnormalAbort { detail: "TerminalOut.unwound".to_owned() },
            Some(&ObservedOutcome::AbnormalAbort { detail: "unwound".to_owned() }),
        );
        assert!(matches!(unexpected_unwind, Verdict::LegDivergence { .. }));
        assert!(!unexpected_unwind.is_ok());
    }

    #[test]
    fn conservative_unsupported_requires_step_time_and_control_expectation() {
        let disallowed = evaluate_case(
            Expectation::Pass,
            Some(&int_u32(1)),
            None,
            None,
            &ret_u32(1),
            &ObservedOutcome::Unsupported { detail: "unmodeled call".to_owned() },
            None,
        );
        assert!(matches!(disallowed, Verdict::ConservativeRejection { .. }));
        assert!(!disallowed.is_ok());

        let init_rej = evaluate_case(
            Expectation::UnsupportedControl,
            None,
            None,
            None,
            &ObservedOutcome::AbnormalAbort { detail: "aborted".to_owned() },
            &ObservedOutcome::InitUnsupported { detail: "initStateBy unsupported".to_owned() },
            Some(&ObservedOutcome::Unsupported { detail: "init".to_owned() }),
        );
        assert!(matches!(init_rej, Verdict::LegDivergence { .. }));
        assert!(!init_rej.is_ok());

        let allowed = evaluate_case(
            Expectation::UnsupportedControl,
            None,
            None,
            Some(ExpectedMiriOutcome::AbnormalAbort),
            &ObservedOutcome::AbnormalAbort { detail: "aborted".to_owned() },
            &ObservedOutcome::Unsupported { detail: "unsupported terminator".to_owned() },
            Some(&ObservedOutcome::Unsupported { detail: "unsupported terminator".to_owned() }),
        );
        assert!(matches!(allowed, Verdict::SoundConservativeAbstraction { .. }));
        assert!(allowed.is_ok());

        let wrong_miri_pin = evaluate_case(
            Expectation::UnsupportedControl,
            None,
            None,
            Some(ExpectedMiriOutcome::AbnormalAbort),
            &ret_u32(2),
            &ObservedOutcome::Unsupported { detail: "unsupported terminator".to_owned() },
            None,
        );
        assert!(matches!(wrong_miri_pin, Verdict::LegDivergence { .. }));
        assert!(!wrong_miri_pin.is_ok());

        let miri_init_err = evaluate_case(
            Expectation::UnsupportedControl,
            None,
            None,
            None,
            &ObservedOutcome::InitUnsupported { detail: "unexpected Miri init error".to_owned() },
            &ObservedOutcome::Unsupported { detail: "unsupported terminator".to_owned() },
            None,
        );
        assert!(matches!(miri_init_err, Verdict::LegDivergence { .. }));
        assert!(!miri_init_err.is_ok());
    }

    #[test]
    fn ub_cause_substring_and_false_positive_checked() {
        let wrong_cause = evaluate_case(
            Expectation::Ub,
            None,
            Some("overflow in signed division"),
            None,
            &ObservedOutcome::UndefinedBehavior {
                detail: "error: Undefined Behavior: dividing by zero".to_owned(),
            },
            &ObservedOutcome::UndefinedBehavior { detail: "undefined".to_owned() },
            None,
        );
        assert!(matches!(wrong_cause, Verdict::LegDivergence { .. }));

        let right_cause = evaluate_case(
            Expectation::Ub,
            None,
            Some("dividing by zero"),
            None,
            &ObservedOutcome::UndefinedBehavior {
                detail: "error: Undefined Behavior: dividing by zero".to_owned(),
            },
            &ObservedOutcome::UndefinedBehavior { detail: "undefined".to_owned() },
            None,
        );
        assert_eq!(right_cause, Verdict::AgreeUndefinedBehavior);

        let false_pos = evaluate_case(
            Expectation::Pass,
            Some(&int_u32(7)),
            None,
            None,
            &ret_u32(7),
            &ObservedOutcome::UndefinedBehavior { detail: "spurious UB".to_owned() },
            None,
        );
        assert!(matches!(false_pos, Verdict::LegDivergence { .. }));
        assert!(!false_pos.is_ok());
    }

    #[test]
    fn red_flags_reject_empty_missing_polarities_or_zero_kernel_checks() {
        let empty = SuiteMetrics::from_outcomes([]);
        assert!(empty.check_red_flags().is_err());

        let only_pass =
            SuiteMetrics::from_outcomes([(&Verdict::AgreeValue { value: int_u32(1) }, true)]);
        assert!(only_pass.check_red_flags().is_err());

        let missing_kernel_ub = SuiteMetrics::from_outcomes([
            (&Verdict::AgreeValue { value: int_u32(1) }, true),
            (&Verdict::AgreeUndefinedBehavior, false),
            (
                &Verdict::SoundConservativeAbstraction {
                    miri: Box::new(ObservedOutcome::AbnormalAbort { detail: "abort".to_owned() }),
                    lean_detail: "unsupported".to_owned(),
                },
                false,
            ),
        ]);
        assert!(missing_kernel_ub.check_red_flags().is_err());

        let complete = SuiteMetrics::from_outcomes([
            (&Verdict::AgreeValue { value: int_u32(1) }, true),
            (&Verdict::AgreeUndefinedBehavior, true),
            (
                &Verdict::SoundConservativeAbstraction {
                    miri: Box::new(ObservedOutcome::AbnormalAbort { detail: "abort".to_owned() }),
                    lean_detail: "unsupported".to_owned(),
                },
                false,
            ),
        ]);
        assert_eq!(complete.check_red_flags().unwrap(), 7);
    }

    #[test]
    fn observed_outcome_json_has_no_duplicate_kind_keys_and_round_trips() {
        let returned = ret_u32(42);
        let serialized = serde_json::to_string(&returned).expect("serialize ObservedOutcome");
        assert_eq!(
            serialized.matches("\"kind\"").count(),
            2,
            "expected outer outcome kind + nested value.kind in {serialized}"
        );
        let top_val: serde_json::Value = serde_json::from_str(&serialized).unwrap();
        assert_eq!(top_val["kind"], "returned");
        assert_eq!(top_val["value"]["kind"], "int");
        let parsed: ObservedOutcome =
            serde_json::from_str(&serialized).expect("round-trip ObservedOutcome");
        assert_eq!(parsed, returned);
    }

    #[test]
    fn scalar_range_validation_enforced() {
        assert_eq!(IntKind::I8.parse_decimal_bits("-128").unwrap(), 128);
        assert!(IntKind::I8.parse_decimal_bits("-129").is_err());
        assert!(IntKind::U8.parse_decimal_bits("256").is_err());
        assert_eq!(
            IntKind::I32.format_decimal(IntKind::I32.parse_decimal_bits("-2147483648").unwrap()),
            "-2147483648"
        );
        assert_eq!(IntKind::Isize.format_rust_literal((i64::MIN as u64) as u128), "isize::MIN");
    }

    #[test]
    fn stage2_fuzz_agreement_taxonomy_and_rustc_ub_authority_rule() {
        let eq = evaluate_fuzz_case(&ret_u32(9), &ret_u32(9), Some(&ret_u32(9)), None, None);
        assert_eq!(eq.agreement, OracleAgreementClass::BiFaultEquivAgreement);
        assert_eq!(eq.rustc_status, RustcCheckStatus::Agreed);
        assert!(eq.disclosed_gap.is_none());

        // Strict UB authority rule: Miri UB yields `IgnoredDueToMiriUb` when
        // Leg 0 is active or pre-populated; disabling Leg 0 keeps `NotRun`.
        let ub_skipped = evaluate_fuzz_case_with_rustc_leg(
            &ObservedOutcome::UndefinedBehavior { detail: "div by zero".to_owned() },
            &ObservedOutcome::UndefinedBehavior { detail: "undefined".to_owned() },
            None,
            None,
            None,
            true,
        );
        assert_eq!(ub_skipped.agreement, OracleAgreementClass::BiFaultEquivAgreement);
        assert_eq!(ub_skipped.rustc_status, RustcCheckStatus::IgnoredDueToMiriUb);
        assert!(!ub_skipped.is_spurious_lean_ub);

        let ub_disabled = evaluate_fuzz_case(
            &ObservedOutcome::UndefinedBehavior { detail: "div by zero".to_owned() },
            &ObservedOutcome::UndefinedBehavior { detail: "undefined".to_owned() },
            None,
            None,
            None,
        );
        assert_eq!(ub_disabled.rustc_status, RustcCheckStatus::NotRun);

        let ub_ok = evaluate_fuzz_case(
            &ObservedOutcome::UndefinedBehavior { detail: "div by zero".to_owned() },
            &ObservedOutcome::UndefinedBehavior { detail: "undefined".to_owned() },
            Some(&ret_u32(0)),
            None,
            None,
        );
        assert_eq!(ub_ok.agreement, OracleAgreementClass::BiFaultEquivAgreement);
        assert_eq!(ub_ok.rustc_status, RustcCheckStatus::IgnoredDueToMiriUb);
        assert!(!ub_ok.is_spurious_lean_ub);

        // Compiled rustc disagreeing with Miri on a UB-free case is an
        // AuthorityDisagreement.
        let auth_disagree =
            evaluate_fuzz_case(&ret_u32(9), &ret_u32(9), Some(&ret_u32(10)), None, None);
        assert_eq!(auth_disagree.agreement, OracleAgreementClass::AuthorityDisagreement);
        assert!(matches!(auth_disagree.rustc_status, RustcCheckStatus::Disagreement { .. }));
        assert!(auth_disagree.agreement.is_hard_failure());

        // Missed UB is P0 UnsoundAcceptCritical (never suppressible as a gap).
        let missed_ub = evaluate_fuzz_case(
            &ObservedOutcome::UndefinedBehavior { detail: "div by zero".to_owned() },
            &ret_u32(0),
            Some(&ObservedOutcome::AbnormalAbort { detail: "SIGFPE".to_owned() }),
            None,
            None,
        );
        assert_eq!(missed_ub.agreement, OracleAgreementClass::UnsoundAcceptCritical);
        assert!(missed_ub.disclosed_gap.is_none());
        assert!(missed_ub.agreement.is_hard_failure());

        // Value mismatch is P0 UnsoundAcceptCritical.
        let val_mismatch =
            evaluate_fuzz_case(&ret_u32(7), &ret_u32(8), Some(&ret_u32(7)), None, None);
        assert_eq!(val_mismatch.agreement, OracleAgreementClass::UnsoundAcceptCritical);
        assert!(val_mismatch.agreement.is_hard_failure());

        // Conservative unsupported / fuel exhaustion preserve forward
        // simulation only, and Leg 3 OutOfFuel agrees with Lean OutOfFuel.
        let fuel = evaluate_fuzz_case(
            &ret_u32(1),
            &ObservedOutcome::OutOfFuel { detail: "fuel".to_owned() },
            Some(&ret_u32(1)),
            Some(&ObservedOutcome::OutOfFuel { detail: "mir-eval fuel".to_owned() }),
            None,
        );
        assert_eq!(fuel.agreement, OracleAgreementClass::ConservativeOverApproxForwardSimOnly);
        assert_eq!(fuel.disclosed_gap, Some(DisclosedGapKind::FuelExhausted));
        assert!(!fuel.is_shrinkable_failure());

        // Lean false-positive UB on UB-free Miri execution flags
        // `is_spurious_lean_ub`, carries no disclosed conservative gap, and
        // triggers a shrinkable gate failure.
        let spurious_ub = evaluate_fuzz_case(
            &ret_u32(1),
            &ObservedOutcome::UndefinedBehavior { detail: "oversized shift".to_owned() },
            Some(&ret_u32(1)),
            None,
            None,
        );
        assert!(spurious_ub.is_spurious_lean_ub);
        assert!(spurious_ub.disclosed_gap.is_none());
        assert!(spurious_ub.is_shrinkable_failure());

        // Miri authority `Unsupported` / `OutOfFuel` must be caught before
        // `capture_rejected` can mask it as conservative.
        let miri_unsup_masked = evaluate_fuzz_case(
            &ObservedOutcome::Unsupported { detail: "foreign call".to_owned() },
            &ObservedOutcome::Unsupported { detail: "capture rejected".to_owned() },
            None,
            None,
            Some("unsupported item"),
        );
        assert_eq!(miri_unsup_masked.agreement, OracleAgreementClass::AuthorityDisagreement);

        // Explicit `ObservedOutcome::Unwound` maps cleanly without substring
        // matching on `AbnormalAbort`.
        let unwound_agree = evaluate_fuzz_case(
            &ObservedOutcome::Panic { detail: "panicked".to_owned() },
            &ObservedOutcome::Unwound { detail: "TerminalOut.unwound".to_owned() },
            Some(&ObservedOutcome::Panic { detail: "panicked".to_owned() }),
            Some(&ObservedOutcome::Unwound { detail: "mir-eval unwound".to_owned() }),
            None,
        );
        assert_eq!(unwound_agree.agreement, OracleAgreementClass::BiFaultEquivAgreement);

        let unsup = evaluate_fuzz_case(
            &ObservedOutcome::AbnormalAbort { detail: "aborted".to_owned() },
            &ObservedOutcome::Unsupported { detail: "abort call".to_owned() },
            Some(&ObservedOutcome::AbnormalAbort { detail: "signal 6".to_owned() }),
            None,
            None,
        );
        assert_eq!(unsup.agreement, OracleAgreementClass::ConservativeOverApproxForwardSimOnly);
        assert_eq!(unsup.disclosed_gap, Some(DisclosedGapKind::UnbridgedSemantics));
        assert_eq!(unsup.rustc_status, RustcCheckStatus::Agreed);

        // Leg 3 mir_eval disagreement with Lean triggers AuthorityDisagreement
        // when the primary Miri-vs-Lean pair agreed.
        let leg3_div = evaluate_fuzz_case(
            &ret_u32(7),
            &ret_u32(7),
            Some(&ret_u32(7)),
            Some(&ret_u32(99)),
            None,
        );
        assert_eq!(leg3_div.agreement, OracleAgreementClass::AuthorityDisagreement);

        // Primary Miri-vs-Lean P0 unsoundness (`UnsoundAcceptCritical`) and
        // `is_spurious_lean_ub` take precedence over Leg 3 (`anneal-mir-eval`).
        let ub_missed_with_leg3 = evaluate_fuzz_case(
            &ObservedOutcome::UndefinedBehavior { detail: "dividing by zero".to_owned() },
            &ret_u32(0),
            Some(&ret_u32(0)),
            Some(&ObservedOutcome::UndefinedBehavior { detail: "dividing by zero".to_owned() }),
            None,
        );
        assert_eq!(ub_missed_with_leg3.agreement, OracleAgreementClass::UnsoundAcceptCritical);

        let val_mis_with_leg3 = evaluate_fuzz_case(
            &ret_u32(7),
            &ret_u32(8),
            Some(&ret_u32(7)),
            Some(&ret_u32(7)),
            None,
        );
        assert_eq!(val_mis_with_leg3.agreement, OracleAgreementClass::UnsoundAcceptCritical);

        let spurious_ub_with_leg3 = evaluate_fuzz_case(
            &ret_u32(7),
            &ObservedOutcome::UndefinedBehavior { detail: "overflowing shift".to_owned() },
            Some(&ret_u32(7)),
            Some(&ret_u32(7)),
            None,
        );
        assert!(spurious_ub_with_leg3.is_spurious_lean_ub);
    }

    #[test]
    fn primary_miri_vs_lean_failures_take_precedence_over_leg3_disagreement() {
        // Missed Miri UB in Lean must stay `UnsoundMissedFault` even when Leg 3
        // (`anneal-mir-eval`) agrees with Miri (disagreeing with Lean).
        let missed_ub = evaluate_case(
            Expectation::Ub,
            None,
            Some("dividing by zero"),
            None,
            &ObservedOutcome::UndefinedBehavior {
                detail: "Undefined Behavior: dividing by zero".to_owned(),
            },
            &ret_u32(0),
            Some(&ObservedOutcome::UndefinedBehavior { detail: "ub".to_owned() }),
        );
        assert!(matches!(missed_ub, Verdict::UnsoundMissedFault { .. }), "{missed_ub:?}");

        // Value mismatch between Miri and Lean must stay `ValueMismatch` even
        // when Leg 3 agrees with Miri.
        let val_mismatch = evaluate_case(
            Expectation::Pass,
            Some(&int_u32(7)),
            None,
            None,
            &ret_u32(7),
            &ret_u32(9),
            Some(&ret_u32(7)),
        );
        assert!(matches!(val_mismatch, Verdict::ValueMismatch { .. }), "{val_mismatch:?}");

        // Disallowed step-time `.unsupported` in Lean must stay
        // `ConservativeRejection` even when Leg 3 returned a value.
        let cons_rej = evaluate_case(
            Expectation::Pass,
            Some(&int_u32(7)),
            None,
            None,
            &ret_u32(7),
            &ObservedOutcome::Unsupported { detail: "step unsupported".to_owned() },
            Some(&ret_u32(7)),
        );
        assert!(matches!(cons_rej, Verdict::ConservativeRejection { .. }), "{cons_rej:?}");

        // When Miri and Lean agree, a Leg 3 disagreement still triggers
        // `LegDivergence`.
        let leg3_div = evaluate_case(
            Expectation::Pass,
            Some(&int_u32(7)),
            None,
            None,
            &ret_u32(7),
            &ret_u32(7),
            Some(&ret_u32(9)),
        );
        assert!(matches!(leg3_div, Verdict::LegDivergence { .. }), "{leg3_div:?}");
    }
}
