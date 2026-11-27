// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Verdict algebra, canonical MIR value representation, and red-flag guards
//! for the Stage-1 multi-leg differential oracle.

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
        if self == Self::I128 && self.to_signed_i128(bits) == i128::MIN {
            return "i128::MIN".to_owned();
        }
        if self == Self::I64 && self.to_signed_i128(bits) == i64::MIN as i128 {
            return "i64::MIN".to_owned();
        }
        if self.is_signed() {
            format!("({}{})", self.to_signed_i128(bits), self.rust_name())
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
///   `AbnormalAbort`, or `Panic` is classified as
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
            | ObservedOutcome::Panic { .. } => Verdict::UnsoundMissedFault {
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
        ObservedOutcome::AbnormalAbort { detail } | ObservedOutcome::Panic { detail } => {
            Verdict::LegDivergence {
                detail: format!(
                    "unexpected unwind outcome (expected={expected:?}, lean={detail}, miri={miri:?})"
                ),
            }
        }
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

fn outcomes_agree_mir(lean: &ObservedOutcome, mir_eval: &ObservedOutcome) -> bool {
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
        (
            ObservedOutcome::AbnormalAbort { .. } | ObservedOutcome::Panic { .. },
            ObservedOutcome::AbnormalAbort { .. } | ObservedOutcome::Panic { .. },
        ) => true,
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

#[cfg(test)]
mod tests;
