// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deterministic seeded Profile-v1 admitted-subset MIR program generator.
//!
//! Produces typed, syntactically and type-valid Rust programs (`GenProgram`)
//! paired with concrete [`MirValue`] inputs and a semantic [`GenCategory`]
//! calibrated to the real Profile v1 fragment admitted by
//! `anneal-rustc-capture` and `Trusted.MirSemantics` (all 12 integer widths,
//! `bool`, `char`, `core::cmp::Ordering`, `()`, crate-local fieldless enums,
//! `core::num` `wrapping_*`/`unchecked_*` ops, bitwise/shift ops, `IntToInt`
//! casts, `let mut` locals, `if`/`else`, `match`, bounded `while` loops,
//! move+reinit, and explicit `ScopeControl` probes).

use std::{collections::BTreeSet, fmt::Write as _};

use serde::{Deserialize, Serialize};

use crate::verdict::{IntKind, MirValue, OrderingKind};

/// Crate-level attributes shared by generated Profile v1 Rust modules.
pub const GEN_CRATE_HEADER: &str = "\
#![allow(dead_code, unused_variables, unused_mut, unused_assignments, unused_parens, unreachable_code, unreachable_patterns, arithmetic_overflow, unconditional_panic, unused_unsafe)]
";

/// Shared crate-local fieldless enum, unit, and `Ordering` declarations
/// admitted by Profile v1. Enum constants lower via
/// `Rvalue::Use(Operand::Constant)` rather than `Rvalue::Aggregate`, and
/// multi-variant enums omit `Copy`/`Clone` so `MoveReinit` emits real non-ZST
/// `Operand::Move` + reinitialization.
pub const GEN_ENUM_PREAMBLE: &str = "\
pub const GEN_UNIT: () = ();

#[repr(i16)]
pub enum GenSignedTag {
    NegFive = -5,
    Zero = 0,
    Four = 4,
    ThreeHundred = 300,
}

pub const GEN_SIGNED_NEG_FIVE: GenSignedTag = GenSignedTag::NegFive;
pub const GEN_SIGNED_ZERO: GenSignedTag = GenSignedTag::Zero;
pub const GEN_SIGNED_FOUR: GenSignedTag = GenSignedTag::Four;
pub const GEN_SIGNED_THREE_HUNDRED: GenSignedTag = GenSignedTag::ThreeHundred;

#[repr(u8)]
pub enum GenUnsignedTag {
    Alpha = 0,
    Beta = 7,
    Gamma = 250,
}

pub const GEN_UNSIGNED_ALPHA: GenUnsignedTag = GenUnsignedTag::Alpha;
pub const GEN_UNSIGNED_BETA: GenUnsignedTag = GenUnsignedTag::Beta;
pub const GEN_UNSIGNED_GAMMA: GenUnsignedTag = GenUnsignedTag::Gamma;

#[repr(u8)]
pub enum GenSoloRepr {
    Only = 42,
}

pub const GEN_SOLO_ONLY: GenSoloRepr = GenSoloRepr::Only;

pub enum GenZstUnit {
    Only,
}

pub const GEN_ZST_ONLY: GenZstUnit = GenZstUnit::Only;

pub const GEN_ORD_LESS: core::cmp::Ordering = core::cmp::Ordering::Less;
pub const GEN_ORD_EQUAL: core::cmp::Ordering = core::cmp::Ordering::Equal;
pub const GEN_ORD_GREATER: core::cmp::Ordering = core::cmp::Ordering::Greater;
";

/// Deterministic SplitMix64 PRNG with zero external dependencies.
#[derive(Clone, Debug)]
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    /// Construct a deterministic PRNG stream keyed by
    /// `(master_seed, case_index)` so every generated case is independently
    /// reproducible.
    pub fn for_case(master_seed: u64, case_index: usize) -> Self {
        let mixed = master_seed
            ^ (case_index as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
            ^ 0xD1B5_4A32_D192_ED03;
        let mut rng = Self { state: mixed };
        // Warm up two rounds to diffuse small seed/index differences.
        let _ = rng.next_u64();
        let _ = rng.next_u64();
        rng
    }

    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn next_u128(&mut self) -> u128 {
        let hi = u128::from(self.next_u64());
        let lo = u128::from(self.next_u64());
        (hi << 64) | lo
    }

    pub fn gen_range(&mut self, upper: usize) -> usize {
        if upper <= 1 { 0 } else { gen_range_from_word(self.next_u64(), upper) }
    }

    pub fn coin(&mut self, num: u64, den: u64) -> bool {
        if den == 0 {
            return false;
        }
        (self.next_u64() % den) < num
    }

    pub fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.gen_range(items.len())]
    }
}

/// Reduce a 64-bit SplitMix word modulo `upper` before narrowing to `usize` so
/// 32-bit hosts (`--no-rustc`) sample the exact same sequence as 64-bit hosts
/// and Python validators.
fn gen_range_from_word(word: u64, upper: usize) -> usize {
    if upper <= 1 {
        0
    } else {
        let upper_u64 = u64::try_from(upper).expect("SplitMix64 range bound fits in u64");
        (word % upper_u64) as usize
    }
}

/// All 12 Profile v1 integer kinds (`x86_64`).
pub const ALL_INT_KINDS: [IntKind; 12] = [
    IntKind::U8,
    IntKind::U16,
    IntKind::U32,
    IntKind::U64,
    IntKind::U128,
    IntKind::Usize,
    IntKind::I8,
    IntKind::I16,
    IntKind::I32,
    IntKind::I64,
    IntKind::I128,
    IntKind::Isize,
];

/// All 6 signed Profile v1 integer kinds.
pub const SIGNED_INT_KINDS: [IntKind; 6] =
    [IntKind::I8, IntKind::I16, IntKind::I32, IntKind::I64, IntKind::I128, IntKind::Isize];

/// All 5 unsigned Profile v1 integer kinds excluding `usize` (because
/// `usize::unchecked_sub` lowers to Profile v2 `CoreCall` rather than Profile
/// v1 `SysrootCall`).
pub const UNSIGNED_NON_USIZE_INT_KINDS: [IntKind; 5] =
    [IntKind::U8, IntKind::U16, IntKind::U32, IntKind::U64, IntKind::U128];

/// Interesting Unicode scalar values including ASCII, multi-byte, and
/// UTF-16 surrogate boundaries (`0xD7FF` / `0xE000`) plus `char::MAX`.
pub const BOUNDARY_CHARS: [u32; 8] =
    [0x0000, 0x0041, 0x007F, 0x00FF, 0x03BB, 0xD7FF, 0xE000, 0x10_FFFF];

/// Semantic category of a generated program case.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GenCategory {
    /// Cleanly admitted well-defined program expected to return a value.
    SafeAdmitted,
    /// Well-defined program targeting overflow/shift/cast/enum/char/loop edges.
    BoundaryEdgeCase,
    /// Admitted program deliberately triggering Profile v1 UB (`unchecked_add`,
    /// `unchecked_sub`, or `unchecked_mul`) to hammer soundness.
    TargetedUbProbe,
    /// Deliberate scope boundary (`abort`, `hint::unreachable_unchecked`, or
    /// fuel exhaustion) exercising `ConservativeOverApproxForwardSimOnly`.
    ScopeControl,
}

impl GenCategory {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SafeAdmitted => "safe_admitted",
            Self::BoundaryEdgeCase => "boundary_edge_case",
            Self::TargetedUbProbe => "targeted_ub_probe",
            Self::ScopeControl => "scope_control",
        }
    }

    /// Whether this category targets the admitted Profile v1 subset for
    /// non-vacuity `admission_rate` accounting (any step-budget exhaustion or
    /// conservative `.unsupported` lowers `admission_rate` fail-closed).
    pub const fn counts_toward_admission(self) -> bool {
        matches!(self, Self::SafeAdmitted | Self::BoundaryEdgeCase)
    }
}

/// Crate-local fieldless enum kind declared in [`GEN_ENUM_PREAMBLE`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GenEnumKind {
    SignedTag,
    UnsignedTag,
    SoloRepr,
    ZstUnit,
}

impl GenEnumKind {
    pub const ALL: [Self; 4] = [Self::SignedTag, Self::UnsignedTag, Self::SoloRepr, Self::ZstUnit];

    pub const fn rust_name(self) -> &'static str {
        match self {
            Self::SignedTag => "GenSignedTag",
            Self::UnsignedTag => "GenUnsignedTag",
            Self::SoloRepr => "GenSoloRepr",
            Self::ZstUnit => "GenZstUnit",
        }
    }

    pub const fn variants(self) -> &'static [&'static str] {
        match self {
            Self::SignedTag => &["NegFive", "Zero", "Four", "ThreeHundred"],
            Self::UnsignedTag => &["Alpha", "Beta", "Gamma"],
            Self::SoloRepr => &["Only"],
            Self::ZstUnit => &["Only"],
        }
    }

    pub fn mir_value(self, variant_index: usize) -> MirValue {
        let variants = self.variants();
        let idx = variant_index % variants.len();
        MirValue::Enum {
            enum_type: self.rust_name().to_owned(),
            variant: variants[idx].to_owned(),
            variant_index: idx,
        }
    }
}

/// Profile v1 typed value/expression kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GenType {
    Int(IntKind),
    Bool,
    Char,
    Ordering,
    Unit,
    Enum(GenEnumKind),
}

impl GenType {
    pub fn rust_name(self) -> String {
        match self {
            Self::Int(k) => k.rust_name().to_owned(),
            Self::Bool => "bool".to_owned(),
            Self::Char => "char".to_owned(),
            Self::Ordering => "core::cmp::Ordering".to_owned(),
            Self::Unit => "()".to_owned(),
            Self::Enum(e) => e.rust_name().to_owned(),
        }
    }

    /// Construct a canonical zero/default [`MirValue`] shape for return-type
    /// printing and literal simplification.
    pub fn default_mir_value(self) -> MirValue {
        match self {
            Self::Int(int_kind) => MirValue::Int { int_kind, bits: 0 },
            Self::Bool => MirValue::Bool { value: false },
            Self::Char => MirValue::Char { scalar: u32::from(b'A') },
            Self::Ordering => MirValue::Ordering { value: OrderingKind::Equal },
            Self::Unit => MirValue::Unit,
            Self::Enum(e) => e.mir_value(0),
        }
    }

    pub const fn is_int_like(self) -> bool {
        matches!(self, Self::Int(_) | Self::Bool | Self::Char)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GenArithOp {
    Add,
    Sub,
    Mul,
    BitAnd,
    BitOr,
    BitXor,
}

impl GenArithOp {
    pub const ALL: [Self; 6] =
        [Self::Add, Self::Sub, Self::Mul, Self::BitAnd, Self::BitOr, Self::BitXor];

    pub const fn rust_sym(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::BitAnd => "&",
            Self::BitOr => "|",
            Self::BitXor => "^",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GenShiftOp {
    Shl,
    Shr,
}

impl GenShiftOp {
    pub const fn rust_sym(self) -> &'static str {
        match self {
            Self::Shl => "<<",
            Self::Shr => ">>",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GenSysrootNumOp {
    UncheckedAdd,
    UncheckedSub,
    UncheckedMul,
    WrappingAdd,
    WrappingSub,
    WrappingMul,
}

impl GenSysrootNumOp {
    pub const ALL: [Self; 6] = [
        Self::UncheckedAdd,
        Self::UncheckedSub,
        Self::UncheckedMul,
        Self::WrappingAdd,
        Self::WrappingSub,
        Self::WrappingMul,
    ];

    pub const USIZE_SAFE: [Self; 5] = [
        Self::UncheckedAdd,
        Self::UncheckedMul,
        Self::WrappingAdd,
        Self::WrappingSub,
        Self::WrappingMul,
    ];

    pub const fn is_unchecked(self) -> bool {
        matches!(self, Self::UncheckedAdd | Self::UncheckedSub | Self::UncheckedMul)
    }

    pub const fn method_name(self) -> &'static str {
        match self {
            Self::UncheckedAdd => "unchecked_add",
            Self::UncheckedSub => "unchecked_sub",
            Self::UncheckedMul => "unchecked_mul",
            Self::WrappingAdd => "wrapping_add",
            Self::WrappingSub => "wrapping_sub",
            Self::WrappingMul => "wrapping_mul",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GenUnOp {
    Not,
    Neg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GenCmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl GenCmpOp {
    pub const ALL: [Self; 6] = [Self::Eq, Self::Ne, Self::Lt, Self::Le, Self::Gt, Self::Ge];

    pub const fn rust_sym(self) -> &'static str {
        match self {
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GenBoolBinOp {
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
}

impl GenBoolBinOp {
    pub const ALL: [Self; 5] = [Self::And, Self::Or, Self::BitAnd, Self::BitOr, Self::BitXor];

    pub const fn rust_sym(self) -> &'static str {
        match self {
            Self::And => "&&",
            Self::Or => "||",
            Self::BitAnd => "&",
            Self::BitOr => "|",
            Self::BitXor => "^",
        }
    }
}

/// Typed Profile v1 expression IR.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GenExpr {
    Lit(MirValue),
    Param(usize),
    Local(usize),
    BinArith {
        op: GenArithOp,
        ty: IntKind,
        lhs: Box<GenExpr>,
        rhs: Box<GenExpr>,
    },
    Shift {
        op: GenShiftOp,
        lhs_ty: IntKind,
        rhs_ty: IntKind,
        lhs: Box<GenExpr>,
        rhs: Box<GenExpr>,
    },
    SysrootNum {
        op: GenSysrootNumOp,
        ty: IntKind,
        lhs: Box<GenExpr>,
        rhs: Box<GenExpr>,
        /// When `true` on `unchecked_*`, clamps operands with `& 7` (and
        /// orders unsigned `unchecked_sub` operands) so execution stays
        /// well-defined while still lowering via `SysrootCall`.
        guarded: bool,
    },
    Unary {
        op: GenUnOp,
        ty: GenType,
        operand: Box<GenExpr>,
    },
    Cmp {
        op: GenCmpOp,
        lhs: Box<GenExpr>,
        rhs: Box<GenExpr>,
    },
    BoolLogic {
        op: GenBoolBinOp,
        lhs: Box<GenExpr>,
        rhs: Box<GenExpr>,
    },
    ThreeWayCmp {
        lhs: Box<GenExpr>,
        rhs: Box<GenExpr>,
    },
    Cast {
        expr: Box<GenExpr>,
        src_ty: GenType,
        dst_ty: GenType,
    },
    MatchOrdering {
        scrutinee: Box<GenExpr>,
        ty: GenType,
        less: Box<GenExpr>,
        equal: Box<GenExpr>,
        greater: Box<GenExpr>,
    },
    MatchEnum {
        param_idx: usize,
        enum_kind: GenEnumKind,
        ty: GenType,
        arms: Vec<GenExpr>,
    },
    MatchInt {
        scrutinee: Box<GenExpr>,
        scrutinee_ty: IntKind,
        ty: GenType,
        arms: Vec<(u128, GenExpr)>,
        otherwise: Box<GenExpr>,
    },
    MatchChar {
        scrutinee: Box<GenExpr>,
        ty: GenType,
        arms: Vec<(u32, GenExpr)>,
        otherwise: Box<GenExpr>,
    },
}

impl GenExpr {
    /// Count AST nodes in this expression (used by the 1-minimal shrinker).
    pub fn node_count(&self) -> usize {
        match self {
            Self::Lit(_) | Self::Param(_) | Self::Local(_) => 1,
            Self::BinArith { lhs, rhs, .. }
            | Self::Shift { lhs, rhs, .. }
            | Self::SysrootNum { lhs, rhs, .. }
            | Self::Cmp { lhs, rhs, .. }
            | Self::BoolLogic { lhs, rhs, .. }
            | Self::ThreeWayCmp { lhs, rhs } => 1 + lhs.node_count() + rhs.node_count(),
            Self::Unary { operand, .. } => 1 + operand.node_count(),
            Self::Cast { expr, .. } => 1 + expr.node_count(),
            Self::MatchOrdering { scrutinee, less, equal, greater, .. } => {
                1 + scrutinee.node_count()
                    + less.node_count()
                    + equal.node_count()
                    + greater.node_count()
            }
            Self::MatchEnum { arms, .. } => 1 + arms.iter().map(Self::node_count).sum::<usize>(),
            Self::MatchInt { scrutinee, arms, otherwise, .. } => {
                1 + scrutinee.node_count()
                    + arms.iter().map(|(_, e)| e.node_count()).sum::<usize>()
                    + otherwise.node_count()
            }
            Self::MatchChar { scrutinee, arms, otherwise, .. } => {
                1 + scrutinee.node_count()
                    + arms.iter().map(|(_, e)| e.node_count()).sum::<usize>()
                    + otherwise.node_count()
            }
        }
    }

    /// Infer the [`GenType`] of this expression given parameter and local
    /// types.
    pub fn ty(&self, params: &[GenParam], locals: &[GenLocal]) -> GenType {
        match self {
            Self::Lit(v) => mir_value_gen_type(v),
            Self::Param(idx) => params[*idx].ty,
            Self::Local(idx) => locals[*idx].ty,
            Self::BinArith { ty, .. } | Self::SysrootNum { ty, .. } => GenType::Int(*ty),
            Self::Shift { lhs_ty, .. } => GenType::Int(*lhs_ty),
            Self::Unary { ty, .. }
            | Self::MatchOrdering { ty, .. }
            | Self::MatchEnum { ty, .. }
            | Self::MatchInt { ty, .. }
            | Self::MatchChar { ty, .. } => *ty,
            Self::Cmp { .. } | Self::BoolLogic { .. } => GenType::Bool,
            Self::ThreeWayCmp { .. } => GenType::Ordering,
            Self::Cast { dst_ty, .. } => *dst_ty,
        }
    }

    pub fn uses_unsafe(&self) -> bool {
        match self {
            Self::Lit(_) | Self::Param(_) | Self::Local(_) => false,
            Self::SysrootNum { op, lhs, rhs, .. } => {
                op.is_unchecked() || lhs.uses_unsafe() || rhs.uses_unsafe()
            }
            Self::BinArith { lhs, rhs, .. }
            | Self::Shift { lhs, rhs, .. }
            | Self::Cmp { lhs, rhs, .. }
            | Self::BoolLogic { lhs, rhs, .. }
            | Self::ThreeWayCmp { lhs, rhs } => lhs.uses_unsafe() || rhs.uses_unsafe(),
            Self::Unary { operand, .. } => operand.uses_unsafe(),
            Self::Cast { expr, .. } => expr.uses_unsafe(),
            Self::MatchOrdering { scrutinee, less, equal, greater, .. } => {
                scrutinee.uses_unsafe()
                    || less.uses_unsafe()
                    || equal.uses_unsafe()
                    || greater.uses_unsafe()
            }
            Self::MatchEnum { arms, .. } => arms.iter().any(Self::uses_unsafe),
            Self::MatchInt { scrutinee, arms, otherwise, .. } => {
                scrutinee.uses_unsafe()
                    || arms.iter().any(|(_, e)| e.uses_unsafe())
                    || otherwise.uses_unsafe()
            }
            Self::MatchChar { scrutinee, arms, otherwise, .. } => {
                scrutinee.uses_unsafe()
                    || arms.iter().any(|(_, e)| e.uses_unsafe())
                    || otherwise.uses_unsafe()
            }
        }
    }

    pub fn collect_refs(
        &self,
        params_used: &mut BTreeSet<usize>,
        locals_used: &mut BTreeSet<usize>,
    ) {
        match self {
            Self::Lit(_) => {}
            Self::Param(i) => {
                params_used.insert(*i);
            }
            Self::Local(i) => {
                locals_used.insert(*i);
            }
            Self::BinArith { lhs, rhs, .. }
            | Self::Shift { lhs, rhs, .. }
            | Self::SysrootNum { lhs, rhs, .. }
            | Self::Cmp { lhs, rhs, .. }
            | Self::BoolLogic { lhs, rhs, .. }
            | Self::ThreeWayCmp { lhs, rhs } => {
                lhs.collect_refs(params_used, locals_used);
                rhs.collect_refs(params_used, locals_used);
            }
            Self::Unary { operand, .. } => operand.collect_refs(params_used, locals_used),
            Self::Cast { expr, .. } => expr.collect_refs(params_used, locals_used),
            Self::MatchOrdering { scrutinee, less, equal, greater, .. } => {
                scrutinee.collect_refs(params_used, locals_used);
                less.collect_refs(params_used, locals_used);
                equal.collect_refs(params_used, locals_used);
                greater.collect_refs(params_used, locals_used);
            }
            Self::MatchEnum { param_idx, arms, .. } => {
                params_used.insert(*param_idx);
                for arm in arms {
                    arm.collect_refs(params_used, locals_used);
                }
            }
            Self::MatchInt { scrutinee, arms, otherwise, .. } => {
                scrutinee.collect_refs(params_used, locals_used);
                for (_, e) in arms {
                    e.collect_refs(params_used, locals_used);
                }
                otherwise.collect_refs(params_used, locals_used);
            }
            Self::MatchChar { scrutinee, arms, otherwise, .. } => {
                scrutinee.collect_refs(params_used, locals_used);
                for (_, e) in arms {
                    e.collect_refs(params_used, locals_used);
                }
                otherwise.collect_refs(params_used, locals_used);
            }
        }
    }

    pub fn remap_indices(&mut self, param_map: &[Option<usize>], local_map: &[Option<usize>]) {
        match self {
            Self::Lit(_) => {}
            Self::Param(i) => *i = param_map[*i].expect("param remap missing live param"),
            Self::Local(i) => *i = local_map[*i].expect("local remap missing live local"),
            Self::BinArith { lhs, rhs, .. }
            | Self::Shift { lhs, rhs, .. }
            | Self::SysrootNum { lhs, rhs, .. }
            | Self::Cmp { lhs, rhs, .. }
            | Self::BoolLogic { lhs, rhs, .. }
            | Self::ThreeWayCmp { lhs, rhs } => {
                lhs.remap_indices(param_map, local_map);
                rhs.remap_indices(param_map, local_map);
            }
            Self::Unary { operand, .. } => operand.remap_indices(param_map, local_map),
            Self::Cast { expr, .. } => expr.remap_indices(param_map, local_map),
            Self::MatchOrdering { scrutinee, less, equal, greater, .. } => {
                scrutinee.remap_indices(param_map, local_map);
                less.remap_indices(param_map, local_map);
                equal.remap_indices(param_map, local_map);
                greater.remap_indices(param_map, local_map);
            }
            Self::MatchEnum { param_idx, arms, .. } => {
                *param_idx = param_map[*param_idx].expect("param remap missing enum param");
                for arm in arms {
                    arm.remap_indices(param_map, local_map);
                }
            }
            Self::MatchInt { scrutinee, arms, otherwise, .. } => {
                scrutinee.remap_indices(param_map, local_map);
                for (_, e) in arms {
                    e.remap_indices(param_map, local_map);
                }
                otherwise.remap_indices(param_map, local_map);
            }
            Self::MatchChar { scrutinee, arms, otherwise, .. } => {
                scrutinee.remap_indices(param_map, local_map);
                for (_, e) in arms {
                    e.remap_indices(param_map, local_map);
                }
                otherwise.remap_indices(param_map, local_map);
            }
        }
    }

    pub fn render(&self) -> String {
        match self {
            Self::Lit(v) => format_rust_value_expr(v),
            Self::Param(i) => format!("p{i}"),
            Self::Local(i) => format!("v{i}"),
            Self::BinArith { op, lhs, rhs, .. } => {
                format!("(({}) {} ({}))", lhs.render(), op.rust_sym(), rhs.render())
            }
            Self::Shift { op, lhs, rhs, .. } => {
                format!("(({}) {} ({}))", lhs.render(), op.rust_sym(), rhs.render())
            }
            Self::SysrootNum { op, ty, lhs, rhs, guarded } => {
                let method = op.method_name();
                let ty_name = ty.rust_name();
                if !op.is_unchecked() {
                    format!(
                        "{{ let __a: {ty_name} = {}; let __b: {ty_name} = {}; __a.{method}(__b) }}",
                        lhs.render(),
                        rhs.render(),
                    )
                } else if !guarded {
                    format!(
                        "{{ let __a: {ty_name} = {}; let __b: {ty_name} = {}; unsafe {{ __a.{method}(__b) }} }}",
                        lhs.render(),
                        rhs.render(),
                    )
                } else {
                    let seven = ty.format_rust_literal(7);
                    if *op == GenSysrootNumOp::UncheckedSub && !ty.is_signed() {
                        format!(
                            "{{ let __sa: {ty_name} = ({}) & {seven}; let __sb: {ty_name} = ({}) & {seven}; if __sa >= __sb {{ unsafe {{ __sa.unchecked_sub(__sb) }} }} else {{ unsafe {{ __sb.unchecked_sub(__sa) }} }} }}",
                            lhs.render(),
                            rhs.render(),
                        )
                    } else {
                        format!(
                            "{{ let __sa: {ty_name} = ({}) & {seven}; let __sb: {ty_name} = ({}) & {seven}; unsafe {{ __sa.{method}(__sb) }} }}",
                            lhs.render(),
                            rhs.render(),
                        )
                    }
                }
            }
            Self::Unary { op, operand, .. } => match op {
                GenUnOp::Not => format!("(!({}))", operand.render()),
                GenUnOp::Neg => format!("(-({}))", operand.render()),
            },
            Self::Cmp { op, lhs, rhs } => {
                format!("(({}) {} ({}))", lhs.render(), op.rust_sym(), rhs.render())
            }
            Self::BoolLogic { op, lhs, rhs } => {
                format!("(({}) {} ({}))", lhs.render(), op.rust_sym(), rhs.render())
            }
            Self::ThreeWayCmp { lhs, rhs } => {
                format!(
                    "{{ let __cmp_l = {}; let __cmp_r = {}; if __cmp_l < __cmp_r {{ GEN_ORD_LESS }} else if __cmp_l > __cmp_r {{ GEN_ORD_GREATER }} else {{ GEN_ORD_EQUAL }} }}",
                    lhs.render(),
                    rhs.render(),
                )
            }
            Self::Cast { expr, dst_ty, .. } => {
                format!("(({}) as {})", expr.render(), dst_ty.rust_name())
            }
            Self::MatchOrdering { scrutinee, less, equal, greater, .. } => {
                format!(
                    "match {} {{ core::cmp::Ordering::Less => {}, core::cmp::Ordering::Equal => {}, core::cmp::Ordering::Greater => {} }}",
                    scrutinee.render(),
                    less.render(),
                    equal.render(),
                    greater.render()
                )
            }
            Self::MatchEnum { param_idx, enum_kind, arms, .. } => {
                let mut s = format!("match p{param_idx} {{ ");
                for (variant, arm) in enum_kind.variants().iter().zip(arms.iter()) {
                    let _ = write!(s, "{}::{variant} => {}, ", enum_kind.rust_name(), arm.render());
                }
                s.push('}');
                s
            }
            Self::MatchInt { scrutinee, scrutinee_ty, arms, otherwise, .. } => {
                let mut s = format!("match {} {{ ", scrutinee.render());
                for (bits, arm) in arms {
                    let _ = write!(
                        s,
                        "{} => {}, ",
                        format_rust_int_pattern(*scrutinee_ty, *bits),
                        arm.render()
                    );
                }
                let _ = write!(s, "_ => {} }}", otherwise.render());
                s
            }
            Self::MatchChar { scrutinee, arms, otherwise, .. } => {
                let mut s = format!("match {} {{ ", scrutinee.render());
                for (scalar, arm) in arms {
                    let _ = write!(s, "'\\u{{{scalar:x}}}' => {}, ", arm.render());
                }
                let _ = write!(s, "_ => {} }}", otherwise.render());
                s
            }
        }
    }
}

/// Typed Profile v1 statement IR.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GenStmt {
    Assign {
        local: usize,
        expr: GenExpr,
    },
    MoveReinit {
        local: usize,
        expr: GenExpr,
    },
    IfElse {
        cond: GenExpr,
        then_body: Vec<GenStmt>,
        else_body: Vec<GenStmt>,
    },
    WhileLoop {
        bound: u32,
        body: Vec<GenStmt>,
        break_cond: Option<GenExpr>,
        continue_cond: Option<GenExpr>,
    },
    Abort,
    HintUnreachable,
}

impl GenStmt {
    /// Count rendered Rust body statements recursively across this statement,
    /// expanded move/reinit blocks (`let __moved`, cast/use, reinitialization),
    /// loop counter/continue/break scaffolding, and nested branch/loop blocks.
    pub fn stmt_count(&self) -> usize {
        match self {
            Self::Assign { .. } | Self::Abort | Self::HintUnreachable => 1,
            Self::MoveReinit { .. } => 3,
            Self::IfElse { then_body, else_body, .. } => {
                1 + then_body.iter().map(Self::stmt_count).sum::<usize>()
                    + else_body.iter().map(Self::stmt_count).sum::<usize>()
            }
            Self::WhileLoop { body, break_cond, continue_cond, .. } => {
                3 + 2 * usize::from(continue_cond.is_some())
                    + 2 * usize::from(break_cond.is_some())
                    + body.iter().map(Self::stmt_count).sum::<usize>()
            }
        }
    }

    pub fn node_count(&self) -> usize {
        match self {
            Self::Assign { expr, .. } | Self::MoveReinit { expr, .. } => 1 + expr.node_count(),
            Self::IfElse { cond, then_body, else_body } => {
                1 + cond.node_count()
                    + then_body.iter().map(Self::node_count).sum::<usize>()
                    + else_body.iter().map(Self::node_count).sum::<usize>()
            }
            Self::WhileLoop { body, break_cond, continue_cond, .. } => {
                1 + body.iter().map(Self::node_count).sum::<usize>()
                    + break_cond.as_ref().map_or(0, GenExpr::node_count)
                    + continue_cond.as_ref().map_or(0, GenExpr::node_count)
            }
            Self::Abort | Self::HintUnreachable => 1,
        }
    }

    pub fn uses_unsafe(&self) -> bool {
        match self {
            Self::Assign { expr, .. } | Self::MoveReinit { expr, .. } => expr.uses_unsafe(),
            Self::IfElse { cond, then_body, else_body } => {
                cond.uses_unsafe()
                    || then_body.iter().any(Self::uses_unsafe)
                    || else_body.iter().any(Self::uses_unsafe)
            }
            Self::WhileLoop { body, break_cond, continue_cond, .. } => {
                body.iter().any(Self::uses_unsafe)
                    || break_cond.as_ref().is_some_and(GenExpr::uses_unsafe)
                    || continue_cond.as_ref().is_some_and(GenExpr::uses_unsafe)
            }
            Self::HintUnreachable => true,
            Self::Abort => false,
        }
    }

    pub fn collect_refs(
        &self,
        params_used: &mut BTreeSet<usize>,
        locals_used: &mut BTreeSet<usize>,
    ) {
        match self {
            Self::Assign { local, expr } | Self::MoveReinit { local, expr } => {
                locals_used.insert(*local);
                expr.collect_refs(params_used, locals_used);
            }
            Self::IfElse { cond, then_body, else_body } => {
                cond.collect_refs(params_used, locals_used);
                for s in then_body {
                    s.collect_refs(params_used, locals_used);
                }
                for s in else_body {
                    s.collect_refs(params_used, locals_used);
                }
            }
            Self::WhileLoop { body, break_cond, continue_cond, .. } => {
                if let Some(c) = break_cond {
                    c.collect_refs(params_used, locals_used);
                }
                if let Some(c) = continue_cond {
                    c.collect_refs(params_used, locals_used);
                }
                for s in body {
                    s.collect_refs(params_used, locals_used);
                }
            }
            Self::Abort | Self::HintUnreachable => {}
        }
    }

    pub fn remap_indices(&mut self, param_map: &[Option<usize>], local_map: &[Option<usize>]) {
        match self {
            Self::Assign { local, expr } | Self::MoveReinit { local, expr } => {
                *local = local_map[*local].expect("local remap missing target local");
                expr.remap_indices(param_map, local_map);
            }
            Self::IfElse { cond, then_body, else_body } => {
                cond.remap_indices(param_map, local_map);
                for s in then_body {
                    s.remap_indices(param_map, local_map);
                }
                for s in else_body {
                    s.remap_indices(param_map, local_map);
                }
            }
            Self::WhileLoop { body, break_cond, continue_cond, .. } => {
                if let Some(c) = break_cond {
                    c.remap_indices(param_map, local_map);
                }
                if let Some(c) = continue_cond {
                    c.remap_indices(param_map, local_map);
                }
                for s in body {
                    s.remap_indices(param_map, local_map);
                }
            }
            Self::Abort | Self::HintUnreachable => {}
        }
    }

    fn render_into(&self, out: &mut String, indent: usize, loop_counter: &mut usize) {
        let pad = " ".repeat(indent);
        match self {
            Self::Assign { local, expr } => {
                let _ = writeln!(out, "{pad}v{local} = {};", expr.render());
            }
            Self::MoveReinit { local, expr } => {
                let _ = writeln!(out, "{pad}{{");
                let _ = writeln!(out, "{pad}    let __moved = v{local};");
                let _ = writeln!(out, "{pad}    let _ = __moved as isize;");
                let _ = writeln!(out, "{pad}    v{local} = {};", expr.render());
                let _ = writeln!(out, "{pad}}}");
            }
            Self::IfElse { cond, then_body, else_body } => {
                let _ = writeln!(out, "{pad}if {} {{", cond.render());
                for stmt in then_body {
                    stmt.render_into(out, indent + 4, loop_counter);
                }
                if else_body.is_empty() {
                    let _ = writeln!(out, "{pad}}}");
                } else {
                    let _ = writeln!(out, "{pad}}} else {{");
                    for stmt in else_body {
                        stmt.render_into(out, indent + 4, loop_counter);
                    }
                    let _ = writeln!(out, "{pad}}}");
                }
            }
            Self::WhileLoop { bound, body, break_cond, continue_cond } => {
                let id = *loop_counter;
                *loop_counter += 1;
                let _ = writeln!(out, "{pad}let mut __loop_i_{id}: u32 = 0u32;");
                let _ = writeln!(out, "{pad}while __loop_i_{id} < {bound}u32 {{");
                let _ = writeln!(out, "{pad}    __loop_i_{id} = __loop_i_{id} + 1u32;");
                if let Some(cc) = continue_cond {
                    let _ = writeln!(out, "{pad}    if {} {{ continue; }}", cc.render());
                }
                for stmt in body {
                    stmt.render_into(out, indent + 4, loop_counter);
                }
                if let Some(bc) = break_cond {
                    let _ = writeln!(out, "{pad}    if {} {{ break; }}", bc.render());
                }
                let _ = writeln!(out, "{pad}}}");
            }
            Self::Abort => {
                let _ = writeln!(out, "{pad}std::process::abort();");
            }
            Self::HintUnreachable => {
                let _ = writeln!(out, "{pad}unsafe {{ core::hint::unreachable_unchecked() }};");
            }
        }
    }
}

/// Function parameter descriptor paired with its concrete test input value.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenParam {
    pub ty: GenType,
    pub value: MirValue,
}

/// Mutable local variable declared at function entry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenLocal {
    pub ty: GenType,
    pub init: GenExpr,
}

/// Complete typed, shrinkable, reproducible Profile v1 generated program.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenProgram {
    pub case_id: String,
    pub fn_name: String,
    pub master_seed: u64,
    pub case_index: usize,
    pub category: GenCategory,
    pub is_unsafe: bool,
    pub params: Vec<GenParam>,
    pub locals: Vec<GenLocal>,
    pub body: Vec<GenStmt>,
    pub ret_ty: GenType,
    pub ret_expr: GenExpr,
    pub fuel: usize,
}

impl GenProgram {
    /// Concrete argument vector corresponding to `self.params`.
    pub fn args(&self) -> Vec<MirValue> {
        self.params.iter().map(|p| p.value.clone()).collect()
    }

    /// Canonical [`MirValue`] shape matching `self.ret_ty` for return printing.
    pub fn ret_shape(&self) -> MirValue {
        self.ret_ty.default_mir_value()
    }

    /// Total recursive statement count across `self.body` (including nested
    /// `if`/`else` and `while` blocks and any post-body mixer assignments).
    pub fn total_stmt_count(&self) -> usize {
        self.body.iter().map(GenStmt::stmt_count).sum()
    }

    /// Total AST node count (params + locals + body + return expression).
    pub fn node_count(&self) -> usize {
        self.params.len()
            + self.locals.iter().map(|l| 1 + l.init.node_count()).sum::<usize>()
            + self.body.iter().map(GenStmt::node_count).sum::<usize>()
            + self.ret_expr.node_count()
    }

    /// Whether any local initializer, body statement, or return expression
    /// syntactically emits an `unsafe` construct.
    pub fn has_syntactic_unsafe(&self) -> bool {
        self.locals.iter().any(|l| l.init.uses_unsafe())
            || self.body.iter().any(GenStmt::uses_unsafe)
            || self.ret_expr.uses_unsafe()
    }

    /// Whether this function item requires an `unsafe fn` signature.
    pub fn needs_unsafe(&self) -> bool {
        self.is_unsafe || self.has_syntactic_unsafe()
    }

    /// Render the `pub [unsafe] fn <fn_name>(...) -> ... { ... }` item alone.
    pub fn render_fn_item(&self) -> String {
        let mut out = String::new();
        let unsafe_kw = if self.needs_unsafe() { "unsafe " } else { "" };
        let _ = write!(out, "pub {unsafe_kw}fn {}(", self.fn_name);
        for (idx, p) in self.params.iter().enumerate() {
            if idx > 0 {
                out.push_str(", ");
            }
            let _ = write!(out, "p{idx}: {}", p.ty.rust_name());
        }
        let _ = writeln!(out, ") -> {} {{", self.ret_ty.rust_name());
        for (idx, local) in self.locals.iter().enumerate() {
            let _ = writeln!(
                out,
                "    let mut v{idx}: {} = {};",
                local.ty.rust_name(),
                local.init.render()
            );
        }
        let mut loop_counter = 0usize;
        for stmt in &self.body {
            stmt.render_into(&mut out, 4, &mut loop_counter);
        }
        let _ = writeln!(out, "    {}", self.ret_expr.render());
        out.push_str("}\n");
        out
    }

    /// Render a complete standalone Rust crate file containing shared enum and
    /// `Ordering` constant declarations plus this function.
    pub fn render_standalone(&self) -> String {
        format!("{GEN_CRATE_HEADER}\n{GEN_ENUM_PREAMBLE}\n{}", self.render_fn_item())
    }

    /// Deterministic SHA-256 hex digest of [`Self::render_standalone`].
    pub fn program_sha256(&self) -> String {
        crate::lean_runner::sha256_bytes_hex(self.render_standalone().as_bytes())
    }
}

/// Render a batch of generated functions into a single Rust crate.
pub fn render_batch_crate(programs: &[&GenProgram]) -> String {
    let mut out = String::from(GEN_CRATE_HEADER);
    out.push('\n');
    out.push_str(GEN_ENUM_PREAMBLE);
    out.push('\n');
    for prog in programs {
        out.push_str(&prog.render_fn_item());
        out.push('\n');
    }
    out
}

/// Generator configuration for seeded Stage-2 fuzz campaigns.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct GenConfig {
    pub master_seed: u64,
    pub max_stmts: usize,
    pub ub_ratio: f64,
    pub default_fuel: usize,
}

impl Default for GenConfig {
    fn default() -> Self {
        Self { master_seed: 20_261_124, max_stmts: 6, ub_ratio: 0.20, default_fuel: 1_500 }
    }
}

impl GenConfig {
    /// Validate generator bounds (`max_stmts` in `1..=20`, finite `ub_ratio` in
    /// `0.0..=0.85`, and `default_fuel >= 1`).
    pub fn validate(&self) -> Result<(), String> {
        if !(1..=20).contains(&self.max_stmts) {
            return Err(format!("`--max-stmts` must be in 1..=20, got {}", self.max_stmts));
        }
        if !self.ub_ratio.is_finite() || !(0.0..=0.85).contains(&self.ub_ratio) {
            return Err(format!("`--ub-ratio` must be in 0.0..=0.85, got {}", self.ub_ratio));
        }
        if self.default_fuel == 0 {
            return Err("`--fuel` must be >= 1".to_owned());
        }
        Ok(())
    }
}

/// Generate a deterministic batch of `count` Profile v1 programs keyed by
/// `(config.master_seed, 0..count)`.
///
/// Panics if `config.validate()` fails; CLI and campaign entrypoints validate
/// `config` beforehand via [`GenConfig::validate`].
pub fn generate_campaign(config: &GenConfig, count: usize) -> Vec<GenProgram> {
    config.validate().expect("invalid GenConfig passed to generate_campaign");
    (0..count).map(|idx| generate_case(config, idx)).collect()
}

/// Generate one deterministic Profile v1 program for
/// `(config.master_seed, case_index)`.
pub fn generate_case(config: &GenConfig, case_index: usize) -> GenProgram {
    config.validate().expect("invalid GenConfig passed to generate_case");
    let mut rng = SplitMix64::for_case(config.master_seed, case_index);
    let category = choose_category(&mut rng, config, case_index);
    let max_stmts = config.max_stmts;
    let case_id = format!("fuzz_s{}_c{case_index:04}", config.master_seed);
    let fn_name = format!("fuzz_case_{case_index:04}");

    let prog = match category {
        GenCategory::SafeAdmitted => {
            gen_safe_program(&mut rng, config, case_index, case_id, fn_name, max_stmts, false)
        }
        GenCategory::BoundaryEdgeCase => {
            gen_boundary_program(&mut rng, config, case_index, case_id, fn_name, max_stmts)
        }
        GenCategory::TargetedUbProbe => {
            gen_ub_probe_program(&mut rng, config, case_index, case_id, fn_name, max_stmts)
        }
        GenCategory::ScopeControl => {
            gen_scope_control_program(&mut rng, config, case_index, case_id, fn_name, max_stmts)
        }
    };
    assert!(
        prog.total_stmt_count() <= max_stmts,
        "generated {} statements exceeding max_stmts={max_stmts} for {}",
        prog.total_stmt_count(),
        prog.case_id
    );
    prog
}

fn choose_category(rng: &mut SplitMix64, config: &GenConfig, case_index: usize) -> GenCategory {
    const SCALE: u64 = 1_000_000_000;
    let ub_ppb = if config.ub_ratio <= 0.0 {
        0
    } else {
        ((config.ub_ratio * (SCALE as f64)).round() as u64).clamp(1, 850_000_000)
    };
    // Guarantee deterministic early coverage of every category even on small
    // CI runs (e.g. 16-32 cases) while respecting `ub_ratio == 0.0` and
    // preserving sub-percent positive `ub_ratio` values (e.g. `0.001`).
    match case_index {
        0 => return GenCategory::SafeAdmitted,
        1 => return GenCategory::BoundaryEdgeCase,
        2 if ub_ppb > 0 => return GenCategory::TargetedUbProbe,
        3 => return GenCategory::ScopeControl,
        _ => {}
    }
    let roll = rng.next_u64() % SCALE;
    if roll < ub_ppb {
        GenCategory::TargetedUbProbe
    } else if roll < ub_ppb.saturating_add(50_000_000).min(950_000_000) {
        GenCategory::ScopeControl
    } else if roll < ub_ppb.saturating_add(350_000_000).min(980_000_000) {
        GenCategory::BoundaryEdgeCase
    } else {
        GenCategory::SafeAdmitted
    }
}

fn format_rust_int_pattern(kind: IntKind, bits: u128) -> String {
    if kind.is_signed() {
        let signed = kind.to_signed_i128(bits);
        match kind {
            IntKind::I8 if signed == i8::MIN as i128 => return "i8::MIN".to_owned(),
            IntKind::I16 if signed == i16::MIN as i128 => return "i16::MIN".to_owned(),
            IntKind::I32 if signed == i32::MIN as i128 => return "i32::MIN".to_owned(),
            IntKind::I64 if signed == i64::MIN as i128 => return "i64::MIN".to_owned(),
            IntKind::I128 if signed == i128::MIN => return "i128::MIN".to_owned(),
            IntKind::Isize if signed == i64::MIN as i128 => return "isize::MIN".to_owned(),
            _ => {}
        }
        format!("{signed}{}", kind.rust_name())
    } else {
        format!("{}{}", bits & kind.mask(), kind.rust_name())
    }
}

fn format_rust_value_expr(v: &MirValue) -> String {
    match v {
        MirValue::Int { int_kind, bits } => int_kind.format_rust_literal(*bits),
        MirValue::Bool { value } => value.to_string(),
        MirValue::Char { scalar } => format!("'\\u{{{scalar:x}}}'"),
        MirValue::Ordering { value } => match value {
            OrderingKind::Less => "GEN_ORD_LESS".to_owned(),
            OrderingKind::Equal => "GEN_ORD_EQUAL".to_owned(),
            OrderingKind::Greater => "GEN_ORD_GREATER".to_owned(),
        },
        MirValue::Unit => "GEN_UNIT".to_owned(),
        MirValue::OverflowPair { int_kind, bits, overflow } => {
            format!("({}, {overflow})", int_kind.format_rust_literal(*bits))
        }
        MirValue::Enum { enum_type, variant, .. } => match (enum_type.as_str(), variant.as_str()) {
            ("GenSignedTag", "NegFive") => "GEN_SIGNED_NEG_FIVE".to_owned(),
            ("GenSignedTag", "Zero") => "GEN_SIGNED_ZERO".to_owned(),
            ("GenSignedTag", "Four") => "GEN_SIGNED_FOUR".to_owned(),
            ("GenSignedTag", "ThreeHundred") => "GEN_SIGNED_THREE_HUNDRED".to_owned(),
            ("GenUnsignedTag", "Alpha") => "GEN_UNSIGNED_ALPHA".to_owned(),
            ("GenUnsignedTag", "Beta") => "GEN_UNSIGNED_BETA".to_owned(),
            ("GenUnsignedTag", "Gamma") => "GEN_UNSIGNED_GAMMA".to_owned(),
            ("GenSoloRepr", "Only") => "GEN_SOLO_ONLY".to_owned(),
            ("GenZstUnit", "Only") => "GEN_ZST_ONLY".to_owned(),
            _ => format!("{enum_type}::{variant}"),
        },
    }
}

fn mir_value_gen_type(v: &MirValue) -> GenType {
    match v {
        MirValue::Int { int_kind, .. } => GenType::Int(*int_kind),
        MirValue::Bool { .. } => GenType::Bool,
        MirValue::Char { .. } => GenType::Char,
        MirValue::Ordering { .. } => GenType::Ordering,
        MirValue::Unit => GenType::Unit,
        MirValue::OverflowPair { .. } => unreachable!("GenType does not generate overflow_pair"),
        MirValue::Enum { enum_type, .. } => match enum_type.as_str() {
            "GenSignedTag" => GenType::Enum(GenEnumKind::SignedTag),
            "GenUnsignedTag" => GenType::Enum(GenEnumKind::UnsignedTag),
            "GenSoloRepr" => GenType::Enum(GenEnumKind::SoloRepr),
            _ => GenType::Enum(GenEnumKind::ZstUnit),
        },
    }
}

/// Boundary bit patterns for `kind`: `0`, `1`, `2`, `MAX`, `MAX-1`, and shift
/// probes `W-1`, `W`, `W+3` (plus `MIN`, `MIN+1`, `-1`, `-2`, `-W` for signed
/// widths).
pub fn boundary_bits_for_int(kind: IntKind) -> Vec<u128> {
    let mask = kind.mask();
    let w = kind.bits();
    let mut vals = vec![0u128, 1u128 & mask, 2u128 & mask, mask, mask.saturating_sub(1)];
    if kind.is_signed() {
        let min_bits = 1u128 << (w - 1);
        let max_bits = min_bits - 1;
        let neg_one = mask;
        vals.extend_from_slice(&[
            min_bits,
            (min_bits + 1) & mask,
            max_bits,
            max_bits.saturating_sub(1),
            neg_one,
            (-2i128 as u128) & mask,
            (-(w as i128) as u128) & mask,
        ]);
    }
    vals.push((u128::from(w.saturating_sub(1))) & mask);
    vals.push((u128::from(w)) & mask);
    vals.push((u128::from(w + 3)) & mask);
    let mut dedup = Vec::new();
    for v in vals {
        if !dedup.contains(&v) {
            dedup.push(v);
        }
    }
    dedup
}

fn gen_int_value(rng: &mut SplitMix64, kind: IntKind, boundary_bias: bool) -> MirValue {
    let bits = if boundary_bias || rng.coin(3, 5) {
        let pool = boundary_bits_for_int(kind);
        *rng.pick(&pool)
    } else {
        rng.next_u128() & kind.mask()
    };
    MirValue::Int { int_kind: kind, bits }
}

fn gen_value_for_type(rng: &mut SplitMix64, ty: GenType, boundary_bias: bool) -> MirValue {
    match ty {
        GenType::Int(k) => gen_int_value(rng, k, boundary_bias),
        GenType::Bool => MirValue::Bool { value: rng.coin(1, 2) },
        GenType::Char => {
            let scalar = if boundary_bias || rng.coin(3, 4) {
                *rng.pick(&BOUNDARY_CHARS)
            } else {
                // Sample across ASCII + BMP + SMP avoiding UTF-16 surrogates.
                let raw = (rng.next_u64() as u32) % 0x10_FFFF;
                if (0xD800..=0xDFFF).contains(&raw) { 0x03BB } else { raw }
            };
            MirValue::Char { scalar }
        }
        GenType::Ordering => MirValue::Ordering {
            value: *rng.pick(&[OrderingKind::Less, OrderingKind::Equal, OrderingKind::Greater]),
        },
        GenType::Unit => MirValue::Unit,
        GenType::Enum(e) => e.mir_value(rng.gen_range(e.variants().len())),
    }
}

fn gen_safe_program(
    rng: &mut SplitMix64,
    config: &GenConfig,
    case_index: usize,
    case_id: String,
    fn_name: String,
    max_stmts: usize,
    boundary_bias: bool,
) -> GenProgram {
    let primary_int = *rng.pick(&ALL_INT_KINDS);
    let secondary_int = *rng.pick(&ALL_INT_KINDS);
    let mut params = vec![
        GenParam {
            ty: GenType::Int(primary_int),
            value: gen_value_for_type(rng, GenType::Int(primary_int), boundary_bias),
        },
        GenParam {
            ty: GenType::Int(primary_int),
            value: gen_value_for_type(rng, GenType::Int(primary_int), boundary_bias),
        },
    ];
    // Add `1..=3` extra heterogeneous parameters (secondary int, bool, char,
    // ordering, or enum).
    let extra_count = 1 + rng.gen_range(3);
    for _ in 0..extra_count {
        let extra_ty = match rng.gen_range(6) {
            0 => GenType::Int(secondary_int),
            1 => GenType::Bool,
            2 => GenType::Char,
            3 => GenType::Ordering,
            4 => GenType::Enum(*rng.pick(&GenEnumKind::ALL)),
            _ => GenType::Int(*rng.pick(&ALL_INT_KINDS)),
        };
        params.push(GenParam {
            ty: extra_ty,
            value: gen_value_for_type(rng, extra_ty, boundary_bias),
        });
    }

    let mut locals = vec![
        GenLocal { ty: GenType::Int(primary_int), init: GenExpr::Param(0) },
        GenLocal { ty: GenType::Int(primary_int), init: GenExpr::Param(1) },
        GenLocal {
            ty: GenType::Bool,
            init: GenExpr::Lit(gen_value_for_type(rng, GenType::Bool, boundary_bias)),
        },
    ];
    if let Some((idx, _)) =
        params.iter().enumerate().find(|(_, p)| p.ty == GenType::Int(secondary_int))
    {
        locals.push(GenLocal { ty: GenType::Int(secondary_int), init: GenExpr::Param(idx) });
    } else {
        locals.push(GenLocal {
            ty: GenType::Int(secondary_int),
            init: GenExpr::Lit(gen_value_for_type(rng, GenType::Int(secondary_int), boundary_bias)),
        });
    }
    // Dedicated non-Copy, non-ZST multi-variant enum slot for `MoveReinit` so
    // `let __moved = v_slot; v_slot = ...;` emits real `Operand::Move` +
    // reinit.
    let move_enum = *rng.pick(&[GenEnumKind::SignedTag, GenEnumKind::UnsignedTag]);
    locals.push(GenLocal {
        ty: GenType::Enum(move_enum),
        init: GenExpr::Lit(gen_value_for_type(rng, GenType::Enum(move_enum), boundary_bias)),
    });

    // Reserve 1 statement for `v_mix` materialization when `max_stmts >= 2`
    // (at `max_stmts == 1`, `gen_safe_return` folds pre-mixer locals inline in
    // `ret_expr` with zero extra statements so total statements stay `<= 1`).
    let reserve_mixer_stmt = usize::from(max_stmts >= 2);
    let body_budget = max_stmts - reserve_mixer_stmt;
    let target_body_stmts = 1 + rng.gen_range(body_budget);
    let mut remaining = target_body_stmts;
    let mut body = Vec::with_capacity(target_body_stmts + reserve_mixer_stmt);
    while remaining > 0 {
        body.push(gen_safe_stmt(rng, &params, &locals, boundary_bias, 2, &mut remaining));
    }

    let (ret_ty, ret_expr) = gen_safe_return(
        rng,
        &params,
        &mut locals,
        &mut body,
        primary_int,
        boundary_bias,
        reserve_mixer_stmt > 0,
    );
    let is_unsafe = locals.iter().any(|l| l.init.uses_unsafe())
        || body.iter().any(GenStmt::uses_unsafe)
        || ret_expr.uses_unsafe();

    GenProgram {
        case_id,
        fn_name,
        master_seed: config.master_seed,
        case_index,
        category: if boundary_bias {
            GenCategory::BoundaryEdgeCase
        } else {
            GenCategory::SafeAdmitted
        },
        is_unsafe,
        params,
        locals,
        body,
        ret_ty,
        ret_expr,
        fuel: config.default_fuel,
    }
}

fn pick_sysroot_op_for_kind(rng: &mut SplitMix64, kind: IntKind) -> GenSysrootNumOp {
    if kind == IntKind::Usize {
        *rng.pick(&GenSysrootNumOp::USIZE_SAFE)
    } else {
        *rng.pick(&GenSysrootNumOp::ALL)
    }
}

fn gen_boundary_program(
    rng: &mut SplitMix64,
    config: &GenConfig,
    case_index: usize,
    case_id: String,
    fn_name: String,
    max_stmts: usize,
) -> GenProgram {
    // Rotate through dedicated Profile v1 boundary templates whose rendered
    // body statement counts fit within `max_stmts` (`arm 3`: 0, `arm 4`: 1,
    // `arm 0`: 2, `arm 2`: 3, `arm 1`: 4, `arm 5`: 6, `arm 6`: `<= max_stmts`).
    let candidates: &[usize] = match max_stmts {
        1 => &[3, 4, 6],
        2 => &[0, 3, 4, 6],
        3 => &[0, 2, 3, 4, 6],
        4 | 5 => &[0, 1, 2, 3, 4, 6],
        _ => &[0, 1, 2, 3, 4, 5, 6],
    };
    let arm = candidates[case_index % candidates.len()];
    match arm {
        0 => gen_boundary_shift_matrix(rng, config, case_index, case_id, fn_name),
        1 => gen_boundary_sysroot_num(rng, config, case_index, case_id, fn_name),
        2 => gen_boundary_cast_chain(rng, config, case_index, case_id, fn_name),
        3 => gen_boundary_char_and_ordering(rng, config, case_index, case_id, fn_name),
        4 => gen_boundary_enum_and_match(rng, config, case_index, case_id, fn_name),
        5 => gen_boundary_signed_wrapping_loop(rng, config, case_index, case_id, fn_name),
        _ => gen_safe_program(rng, config, case_index, case_id, fn_name, max_stmts, true),
    }
}

fn gen_boundary_shift_matrix(
    rng: &mut SplitMix64,
    config: &GenConfig,
    case_index: usize,
    case_id: String,
    fn_name: String,
) -> GenProgram {
    let lhs_ty = *rng.pick(&ALL_INT_KINDS);
    let rhs_ty = *rng.pick(&ALL_INT_KINDS);
    let lhs_val = gen_int_value(rng, lhs_ty, true);
    // Explicitly hit `0`, `1`, `W-1`, `W`, `W+5`, and signed `-1`, `-W`,
    // `MIN` (or unsigned `MAX`) shift amounts.
    let w = lhs_ty.bits();
    let mut rhs_candidates = vec![0u128, 1, u128::from(w - 1), u128::from(w), u128::from(w + 5)];
    if rhs_ty.is_signed() {
        rhs_candidates.push((-1i128 as u128) & rhs_ty.mask());
        rhs_candidates.push((-(w as i128) as u128) & rhs_ty.mask());
        rhs_candidates.push(1u128 << (rhs_ty.bits() - 1));
    } else {
        rhs_candidates.push(rhs_ty.mask());
    }
    let rhs_bits = *rng.pick(&rhs_candidates) & rhs_ty.mask();
    let rhs_val = MirValue::Int { int_kind: rhs_ty, bits: rhs_bits };

    let params = vec![
        GenParam { ty: GenType::Int(lhs_ty), value: lhs_val },
        GenParam { ty: GenType::Int(rhs_ty), value: rhs_val },
    ];
    let locals = vec![
        GenLocal { ty: GenType::Int(lhs_ty), init: GenExpr::Param(0) },
        GenLocal {
            ty: GenType::Int(lhs_ty),
            init: GenExpr::Lit(MirValue::Int { int_kind: lhs_ty, bits: 0 }),
        },
    ];
    let body = vec![
        GenStmt::Assign {
            local: 1,
            expr: GenExpr::Shift {
                op: GenShiftOp::Shl,
                lhs_ty,
                rhs_ty,
                lhs: Box::new(GenExpr::Local(0)),
                rhs: Box::new(GenExpr::Param(1)),
            },
        },
        GenStmt::Assign {
            local: 0,
            expr: GenExpr::Shift {
                op: GenShiftOp::Shr,
                lhs_ty,
                rhs_ty,
                lhs: Box::new(GenExpr::Local(0)),
                rhs: Box::new(GenExpr::Param(1)),
            },
        },
    ];
    let ret_expr = GenExpr::BinArith {
        op: GenArithOp::BitXor,
        ty: lhs_ty,
        lhs: Box::new(GenExpr::Local(0)),
        rhs: Box::new(GenExpr::Local(1)),
    };
    GenProgram {
        case_id,
        fn_name,
        master_seed: config.master_seed,
        case_index,
        category: GenCategory::BoundaryEdgeCase,
        is_unsafe: false,
        params,
        locals,
        body,
        ret_ty: GenType::Int(lhs_ty),
        ret_expr,
        fuel: config.default_fuel,
    }
}

fn gen_boundary_sysroot_num(
    rng: &mut SplitMix64,
    config: &GenConfig,
    case_index: usize,
    case_id: String,
    fn_name: String,
) -> GenProgram {
    let kind = *rng.pick(&ALL_INT_KINDS);
    let op = pick_sysroot_op_for_kind(rng, kind);
    let a = gen_int_value(rng, kind, true);
    let b = gen_int_value(rng, kind, true);
    let params = vec![
        GenParam { ty: GenType::Int(kind), value: a },
        GenParam { ty: GenType::Int(kind), value: b },
    ];
    let locals = vec![
        GenLocal { ty: GenType::Int(kind), init: GenExpr::Param(0) },
        GenLocal {
            ty: GenType::Enum(GenEnumKind::SignedTag),
            init: GenExpr::Lit(GenEnumKind::SignedTag.mir_value(0)),
        },
    ];
    let body = vec![
        GenStmt::MoveReinit { local: 1, expr: GenExpr::Lit(GenEnumKind::SignedTag.mir_value(2)) },
        GenStmt::Assign {
            local: 0,
            expr: GenExpr::BinArith {
                op: GenArithOp::BitXor,
                ty: kind,
                lhs: Box::new(GenExpr::Local(0)),
                rhs: Box::new(GenExpr::Cast {
                    expr: Box::new(GenExpr::Local(1)),
                    src_ty: GenType::Enum(GenEnumKind::SignedTag),
                    dst_ty: GenType::Int(kind),
                }),
            },
        },
    ];
    let ret_expr = GenExpr::SysrootNum {
        op,
        ty: kind,
        lhs: Box::new(GenExpr::Local(0)),
        rhs: Box::new(GenExpr::Param(1)),
        guarded: op.is_unchecked(),
    };
    GenProgram {
        case_id,
        fn_name,
        master_seed: config.master_seed,
        case_index,
        category: GenCategory::BoundaryEdgeCase,
        is_unsafe: op.is_unchecked(),
        params,
        locals,
        body,
        ret_ty: GenType::Int(kind),
        ret_expr,
        fuel: config.default_fuel,
    }
}

fn gen_boundary_cast_chain(
    rng: &mut SplitMix64,
    config: &GenConfig,
    case_index: usize,
    case_id: String,
    fn_name: String,
) -> GenProgram {
    let src_int = *rng.pick(&ALL_INT_KINDS);
    let mid_int = *rng.pick(&ALL_INT_KINDS);
    let dst_int = *rng.pick(&ALL_INT_KINDS);
    let params = vec![
        GenParam { ty: GenType::Int(src_int), value: gen_int_value(rng, src_int, true) },
        GenParam { ty: GenType::Bool, value: gen_value_for_type(rng, GenType::Bool, true) },
        GenParam { ty: GenType::Char, value: gen_value_for_type(rng, GenType::Char, true) },
        GenParam { ty: GenType::Int(IntKind::U8), value: gen_int_value(rng, IntKind::U8, true) },
    ];
    let locals = vec![
        GenLocal {
            ty: GenType::Int(mid_int),
            init: GenExpr::Cast {
                expr: Box::new(GenExpr::Param(0)),
                src_ty: GenType::Int(src_int),
                dst_ty: GenType::Int(mid_int),
            },
        },
        GenLocal {
            ty: GenType::Char,
            init: GenExpr::Cast {
                expr: Box::new(GenExpr::Param(3)),
                src_ty: GenType::Int(IntKind::U8),
                dst_ty: GenType::Char,
            },
        },
        GenLocal {
            ty: GenType::Int(dst_int),
            init: GenExpr::Cast {
                expr: Box::new(GenExpr::Param(1)),
                src_ty: GenType::Bool,
                dst_ty: GenType::Int(dst_int),
            },
        },
    ];
    let body = vec![GenStmt::IfElse {
        cond: GenExpr::Cmp {
            op: GenCmpOp::Lt,
            lhs: Box::new(GenExpr::Param(2)),
            rhs: Box::new(GenExpr::Local(1)),
        },
        then_body: vec![GenStmt::Assign {
            local: 2,
            expr: GenExpr::BinArith {
                op: GenArithOp::BitXor,
                ty: dst_int,
                lhs: Box::new(GenExpr::Local(2)),
                rhs: Box::new(GenExpr::Cast {
                    expr: Box::new(GenExpr::Local(0)),
                    src_ty: GenType::Int(mid_int),
                    dst_ty: GenType::Int(dst_int),
                }),
            },
        }],
        else_body: vec![GenStmt::Assign {
            local: 2,
            expr: GenExpr::BinArith {
                op: GenArithOp::Add,
                ty: dst_int,
                lhs: Box::new(GenExpr::Cast {
                    expr: Box::new(GenExpr::Param(2)),
                    src_ty: GenType::Char,
                    dst_ty: GenType::Int(dst_int),
                }),
                rhs: Box::new(GenExpr::Cast {
                    expr: Box::new(GenExpr::Local(0)),
                    src_ty: GenType::Int(mid_int),
                    dst_ty: GenType::Int(dst_int),
                }),
            },
        }],
    }];
    GenProgram {
        case_id,
        fn_name,
        master_seed: config.master_seed,
        case_index,
        category: GenCategory::BoundaryEdgeCase,
        is_unsafe: false,
        params,
        locals,
        body,
        ret_ty: GenType::Int(dst_int),
        ret_expr: GenExpr::Local(2),
        fuel: config.default_fuel,
    }
}

fn gen_boundary_char_and_ordering(
    rng: &mut SplitMix64,
    config: &GenConfig,
    case_index: usize,
    case_id: String,
    fn_name: String,
) -> GenProgram {
    let params = vec![
        GenParam { ty: GenType::Char, value: gen_value_for_type(rng, GenType::Char, true) },
        GenParam { ty: GenType::Char, value: gen_value_for_type(rng, GenType::Char, true) },
    ];
    let locals = vec![GenLocal {
        ty: GenType::Ordering,
        init: GenExpr::ThreeWayCmp {
            lhs: Box::new(GenExpr::Param(0)),
            rhs: Box::new(GenExpr::Param(1)),
        },
    }];
    if rng.coin(1, 3) {
        return GenProgram {
            case_id,
            fn_name,
            master_seed: config.master_seed,
            case_index,
            category: GenCategory::BoundaryEdgeCase,
            is_unsafe: false,
            params,
            locals,
            body: vec![],
            ret_ty: GenType::Ordering,
            ret_expr: GenExpr::Local(0),
            fuel: config.default_fuel,
        };
    }
    let body = vec![];
    let ret_expr = GenExpr::MatchOrdering {
        scrutinee: Box::new(GenExpr::Local(0)),
        ty: GenType::Int(IntKind::I32),
        less: Box::new(GenExpr::MatchChar {
            scrutinee: Box::new(GenExpr::Param(0)),
            ty: GenType::Int(IntKind::I32),
            arms: vec![
                (
                    0x0000,
                    GenExpr::Lit(MirValue::Int {
                        int_kind: IntKind::I32,
                        bits: (-10i32 as u32) as u128,
                    }),
                ),
                (0xD7FF, GenExpr::Lit(MirValue::Int { int_kind: IntKind::I32, bits: 77 })),
            ],
            otherwise: Box::new(GenExpr::Cast {
                expr: Box::new(GenExpr::Param(0)),
                src_ty: GenType::Char,
                dst_ty: GenType::Int(IntKind::I32),
            }),
        }),
        equal: Box::new(GenExpr::Lit(MirValue::Int { int_kind: IntKind::I32, bits: 0 })),
        greater: Box::new(GenExpr::Cast {
            expr: Box::new(GenExpr::Param(1)),
            src_ty: GenType::Char,
            dst_ty: GenType::Int(IntKind::I32),
        }),
    };
    GenProgram {
        case_id,
        fn_name,
        master_seed: config.master_seed,
        case_index,
        category: GenCategory::BoundaryEdgeCase,
        is_unsafe: false,
        params,
        locals,
        body,
        ret_ty: GenType::Int(IntKind::I32),
        ret_expr,
        fuel: config.default_fuel,
    }
}

fn gen_boundary_enum_and_match(
    rng: &mut SplitMix64,
    config: &GenConfig,
    case_index: usize,
    case_id: String,
    fn_name: String,
) -> GenProgram {
    let enum_kind = *rng.pick(&GenEnumKind::ALL);
    let int_kind = *rng.pick(&SIGNED_INT_KINDS);
    let params = vec![
        GenParam {
            ty: GenType::Enum(enum_kind),
            value: gen_value_for_type(rng, GenType::Enum(enum_kind), true),
        },
        GenParam { ty: GenType::Int(int_kind), value: gen_int_value(rng, int_kind, true) },
    ];
    let locals = vec![GenLocal { ty: GenType::Int(int_kind), init: GenExpr::Param(1) }];
    let arms: Vec<GenExpr> = (0..enum_kind.variants().len())
        .map(|i| {
            let delta =
                MirValue::Int { int_kind, bits: ((i as i128 - 2) as u128) & int_kind.mask() };
            GenExpr::BinArith {
                op: if i % 2 == 0 { GenArithOp::Add } else { GenArithOp::BitXor },
                ty: int_kind,
                lhs: Box::new(GenExpr::Local(0)),
                rhs: Box::new(GenExpr::Lit(delta)),
            }
        })
        .collect();
    let body = vec![GenStmt::Assign {
        local: 0,
        expr: GenExpr::MatchEnum { param_idx: 0, enum_kind, ty: GenType::Int(int_kind), arms },
    }];
    let ret_expr = GenExpr::Unary {
        op: GenUnOp::Neg,
        ty: GenType::Int(int_kind),
        operand: Box::new(GenExpr::Local(0)),
    };
    GenProgram {
        case_id,
        fn_name,
        master_seed: config.master_seed,
        case_index,
        category: GenCategory::BoundaryEdgeCase,
        is_unsafe: false,
        params,
        locals,
        body,
        ret_ty: GenType::Int(int_kind),
        ret_expr,
        fuel: config.default_fuel,
    }
}

fn gen_boundary_signed_wrapping_loop(
    rng: &mut SplitMix64,
    config: &GenConfig,
    case_index: usize,
    case_id: String,
    fn_name: String,
) -> GenProgram {
    let kind = *rng.pick(&SIGNED_INT_KINDS);
    let bound = *rng.pick(&[0u32, 1, 2, 4, 7]);
    let params = vec![
        GenParam { ty: GenType::Int(kind), value: gen_int_value(rng, kind, true) },
        GenParam { ty: GenType::Int(kind), value: gen_int_value(rng, kind, true) },
    ];
    let locals = vec![GenLocal { ty: GenType::Int(kind), init: GenExpr::Param(0) }];
    let body = vec![GenStmt::WhileLoop {
        bound,
        body: vec![GenStmt::Assign {
            local: 0,
            expr: GenExpr::BinArith {
                op: *rng.pick(&[GenArithOp::Add, GenArithOp::Sub, GenArithOp::Mul]),
                ty: kind,
                lhs: Box::new(GenExpr::Local(0)),
                rhs: Box::new(GenExpr::Param(1)),
            },
        }],
        break_cond: Some(GenExpr::Cmp {
            op: GenCmpOp::Eq,
            lhs: Box::new(GenExpr::Local(0)),
            rhs: Box::new(GenExpr::Lit(MirValue::Int { int_kind: kind, bits: 0 })),
        }),
        continue_cond: None,
    }];
    let op = *rng.pick(&GenSysrootNumOp::ALL);
    let ret_expr = GenExpr::SysrootNum {
        op,
        ty: kind,
        lhs: Box::new(GenExpr::Local(0)),
        rhs: Box::new(GenExpr::Param(1)),
        guarded: op.is_unchecked(),
    };
    GenProgram {
        case_id,
        fn_name,
        master_seed: config.master_seed,
        case_index,
        category: GenCategory::BoundaryEdgeCase,
        is_unsafe: op.is_unchecked(),
        params,
        locals,
        body,
        ret_ty: GenType::Int(kind),
        ret_expr,
        fuel: config.default_fuel,
    }
}

fn gen_ub_probe_program(
    rng: &mut SplitMix64,
    config: &GenConfig,
    case_index: usize,
    case_id: String,
    fn_name: String,
    max_stmts: usize,
) -> GenProgram {
    let variant = (case_index + rng.gen_range(5)) % 5;
    match variant {
        0 => {
            // `unchecked_add(MAX, delta)` across any integer width (direct or
            // with bounded decoy loop keeping `delta in 1..=9`).
            let kind = *rng.pick(&ALL_INT_KINDS);
            let max_bits = if kind.is_signed() { kind.mask() >> 1 } else { kind.mask() };
            let params = vec![
                GenParam {
                    ty: GenType::Int(kind),
                    value: MirValue::Int { int_kind: kind, bits: max_bits },
                },
                GenParam {
                    ty: GenType::Int(kind),
                    value: MirValue::Int { int_kind: kind, bits: 1 },
                },
            ];
            let locals = vec![
                GenLocal { ty: GenType::Int(kind), init: GenExpr::Param(0) },
                GenLocal { ty: GenType::Int(kind), init: GenExpr::Param(1) },
            ];
            let want_loop = max_stmts >= 4 && rng.coin(1, 2);
            let loop_cost = if want_loop { 4 } else { 0 };
            let decoy_stmts = rng.gen_range((max_stmts - loop_cost).min(2) + 1);
            let mut body = Vec::new();
            for _ in 0..decoy_stmts {
                body.push(GenStmt::Assign {
                    local: 1,
                    expr: GenExpr::BinArith {
                        op: GenArithOp::Add,
                        ty: kind,
                        lhs: Box::new(GenExpr::Local(1)),
                        rhs: Box::new(GenExpr::Lit(MirValue::Int { int_kind: kind, bits: 2 })),
                    },
                });
            }
            if want_loop {
                body.push(GenStmt::WhileLoop {
                    bound: 2,
                    body: vec![GenStmt::Assign {
                        local: 1,
                        expr: GenExpr::BinArith {
                            op: GenArithOp::Add,
                            ty: kind,
                            lhs: Box::new(GenExpr::Local(1)),
                            rhs: Box::new(GenExpr::Lit(MirValue::Int { int_kind: kind, bits: 2 })),
                        },
                    }],
                    break_cond: None,
                    continue_cond: None,
                });
            }
            let ret_expr = GenExpr::SysrootNum {
                op: GenSysrootNumOp::UncheckedAdd,
                ty: kind,
                lhs: Box::new(GenExpr::Local(0)),
                rhs: Box::new(GenExpr::Local(1)),
                guarded: false,
            };
            GenProgram {
                case_id,
                fn_name,
                master_seed: config.master_seed,
                case_index,
                category: GenCategory::TargetedUbProbe,
                is_unsafe: true,
                params,
                locals,
                body,
                ret_ty: GenType::Int(kind),
                ret_expr,
                fuel: config.default_fuel,
            }
        }
        1 => {
            // Signed `unchecked_sub(MIN, 1)` across all 6 signed integer
            // widths with non-Copy MoveReinit decoy.
            let kind = *rng.pick(&SIGNED_INT_KINDS);
            let min_bits = 1u128 << (kind.bits() - 1);
            let params = vec![
                GenParam {
                    ty: GenType::Int(kind),
                    value: MirValue::Int { int_kind: kind, bits: min_bits },
                },
                GenParam {
                    ty: GenType::Int(kind),
                    value: MirValue::Int { int_kind: kind, bits: 1 },
                },
            ];
            let locals = vec![
                GenLocal { ty: GenType::Int(kind), init: GenExpr::Param(0) },
                GenLocal { ty: GenType::Int(kind), init: GenExpr::Param(1) },
                GenLocal {
                    ty: GenType::Enum(GenEnumKind::SignedTag),
                    init: GenExpr::Lit(GenEnumKind::SignedTag.mir_value(0)),
                },
            ];
            let decoy_stmts = rng.gen_range((max_stmts / 3).min(2) + 1);
            let mut body = Vec::new();
            for _ in 0..decoy_stmts {
                body.push(GenStmt::MoveReinit {
                    local: 2,
                    expr: GenExpr::Lit(GenEnumKind::SignedTag.mir_value(1)),
                });
            }
            let ret_expr = GenExpr::SysrootNum {
                op: GenSysrootNumOp::UncheckedSub,
                ty: kind,
                lhs: Box::new(GenExpr::Local(0)),
                rhs: Box::new(GenExpr::Local(1)),
                guarded: false,
            };
            GenProgram {
                case_id,
                fn_name,
                master_seed: config.master_seed,
                case_index,
                category: GenCategory::TargetedUbProbe,
                is_unsafe: true,
                params,
                locals,
                body,
                ret_ty: GenType::Int(kind),
                ret_expr,
                fuel: config.default_fuel,
            }
        }
        2 => {
            // Unsigned `unchecked_sub(0, 1)` across non-usize unsigned widths.
            let kind = *rng.pick(&UNSIGNED_NON_USIZE_INT_KINDS);
            let params = vec![
                GenParam {
                    ty: GenType::Int(kind),
                    value: MirValue::Int { int_kind: kind, bits: 0 },
                },
                GenParam {
                    ty: GenType::Int(kind),
                    value: MirValue::Int { int_kind: kind, bits: 1 },
                },
            ];
            let locals = vec![GenLocal { ty: GenType::Int(kind), init: GenExpr::Param(0) }];
            let ret_expr = GenExpr::SysrootNum {
                op: GenSysrootNumOp::UncheckedSub,
                ty: kind,
                lhs: Box::new(GenExpr::Local(0)),
                rhs: Box::new(GenExpr::Param(1)),
                guarded: false,
            };
            GenProgram {
                case_id,
                fn_name,
                master_seed: config.master_seed,
                case_index,
                category: GenCategory::TargetedUbProbe,
                is_unsafe: true,
                params,
                locals,
                body: vec![],
                ret_ty: GenType::Int(kind),
                ret_expr,
                fuel: config.default_fuel,
            }
        }
        3 => {
            // `unchecked_mul(2^(W-2), 4)` across all 12 integer widths.
            let kind = *rng.pick(&ALL_INT_KINDS);
            let lhs_bits = 1u128 << (kind.bits() - 2);
            let params = vec![
                GenParam {
                    ty: GenType::Int(kind),
                    value: MirValue::Int { int_kind: kind, bits: lhs_bits },
                },
                GenParam {
                    ty: GenType::Int(kind),
                    value: MirValue::Int { int_kind: kind, bits: 4 },
                },
            ];
            let locals = vec![GenLocal { ty: GenType::Int(kind), init: GenExpr::Param(0) }];
            let ret_expr = GenExpr::SysrootNum {
                op: GenSysrootNumOp::UncheckedMul,
                ty: kind,
                lhs: Box::new(GenExpr::Local(0)),
                rhs: Box::new(GenExpr::Param(1)),
                guarded: false,
            };
            GenProgram {
                case_id,
                fn_name,
                master_seed: config.master_seed,
                case_index,
                category: GenCategory::TargetedUbProbe,
                is_unsafe: true,
                params,
                locals,
                body: vec![],
                ret_ty: GenType::Int(kind),
                ret_expr,
                fuel: config.default_fuel,
            }
        }
        _ => {
            // Branch- or direct `unchecked_add(MAX, 1)`.
            let kind = *rng.pick(&ALL_INT_KINDS);
            let max_bits = if kind.is_signed() { kind.mask() >> 1 } else { kind.mask() };
            let params = vec![
                GenParam {
                    ty: GenType::Int(kind),
                    value: MirValue::Int { int_kind: kind, bits: max_bits },
                },
                GenParam { ty: GenType::Bool, value: MirValue::Bool { value: true } },
            ];
            let locals = vec![
                GenLocal { ty: GenType::Int(kind), init: GenExpr::Param(0) },
                GenLocal {
                    ty: GenType::Int(kind),
                    init: GenExpr::Lit(MirValue::Int { int_kind: kind, bits: 1 }),
                },
            ];
            let ovf_stmt = GenStmt::Assign {
                local: 0,
                expr: GenExpr::SysrootNum {
                    op: GenSysrootNumOp::UncheckedAdd,
                    ty: kind,
                    lhs: Box::new(GenExpr::Local(0)),
                    rhs: Box::new(GenExpr::Lit(MirValue::Int { int_kind: kind, bits: 1 })),
                    guarded: false,
                },
            };
            let body = if max_stmts < 2 {
                vec![ovf_stmt]
            } else {
                let decoy_stmts = rng.gen_range((max_stmts - 2).min(2) + 1);
                let mut b = Vec::new();
                for _ in 0..decoy_stmts {
                    b.push(GenStmt::Assign {
                        local: 1,
                        expr: GenExpr::BinArith {
                            op: GenArithOp::BitXor,
                            ty: kind,
                            lhs: Box::new(GenExpr::Local(1)),
                            rhs: Box::new(GenExpr::Lit(MirValue::Int { int_kind: kind, bits: 1 })),
                        },
                    });
                }
                b.push(GenStmt::IfElse {
                    cond: GenExpr::Param(1),
                    then_body: vec![ovf_stmt],
                    else_body: vec![],
                });
                b
            };
            GenProgram {
                case_id,
                fn_name,
                master_seed: config.master_seed,
                case_index,
                category: GenCategory::TargetedUbProbe,
                is_unsafe: true,
                params,
                locals,
                body,
                ret_ty: GenType::Int(kind),
                ret_expr: GenExpr::Local(0),
                fuel: config.default_fuel,
            }
        }
    }
}

fn gen_scope_control_program(
    rng: &mut SplitMix64,
    config: &GenConfig,
    case_index: usize,
    case_id: String,
    fn_name: String,
    max_stmts: usize,
) -> GenProgram {
    let variant = if max_stmts < 4 {
        (case_index + rng.gen_range(2)) % 2
    } else {
        (case_index + rng.gen_range(3)) % 3
    };
    match variant {
        0 => {
            // Taken `std::process::abort()` -> Miri Aborted, rustc Aborted,
            // Lean Unsupported.
            let params = vec![GenParam {
                ty: GenType::Int(IntKind::U32),
                value: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
            }];
            let locals = vec![GenLocal { ty: GenType::Int(IntKind::U32), init: GenExpr::Param(0) }];
            let body = if max_stmts < 2 {
                vec![GenStmt::Abort]
            } else {
                vec![GenStmt::IfElse {
                    cond: GenExpr::Cmp {
                        op: GenCmpOp::Eq,
                        lhs: Box::new(GenExpr::Local(0)),
                        rhs: Box::new(GenExpr::Lit(MirValue::Int {
                            int_kind: IntKind::U32,
                            bits: 0,
                        })),
                    },
                    then_body: vec![GenStmt::Abort],
                    else_body: vec![],
                }]
            };
            GenProgram {
                case_id,
                fn_name,
                master_seed: config.master_seed,
                case_index,
                category: GenCategory::ScopeControl,
                is_unsafe: false,
                params,
                locals,
                body,
                ret_ty: GenType::Int(IntKind::U32),
                ret_expr: GenExpr::Local(0),
                fuel: config.default_fuel,
            }
        }
        1 => {
            // Taken `core::hint::unreachable_unchecked()` -> Miri UB, Lean
            // Unsupported (Call { target: None }).
            let params =
                vec![GenParam { ty: GenType::Bool, value: MirValue::Bool { value: true } }];
            let locals = vec![GenLocal {
                ty: GenType::Int(IntKind::U32),
                init: GenExpr::Lit(MirValue::Int { int_kind: IntKind::U32, bits: 7 }),
            }];
            let body = if max_stmts < 2 {
                vec![GenStmt::HintUnreachable]
            } else {
                vec![GenStmt::IfElse {
                    cond: GenExpr::Param(0),
                    then_body: vec![GenStmt::HintUnreachable],
                    else_body: vec![],
                }]
            };
            GenProgram {
                case_id,
                fn_name,
                master_seed: config.master_seed,
                case_index,
                category: GenCategory::ScopeControl,
                is_unsafe: true,
                params,
                locals,
                body,
                ret_ty: GenType::Int(IntKind::U32),
                ret_expr: GenExpr::Local(0),
                fuel: config.default_fuel,
            }
        }
        _ => {
            // Bounded loop exceeding small fuel budget -> Miri+rustc return,
            // Lean OutOfFuel.
            let params = vec![GenParam {
                ty: GenType::Int(IntKind::U32),
                value: MirValue::Int { int_kind: IntKind::U32, bits: 1 },
            }];
            let locals = vec![GenLocal { ty: GenType::Int(IntKind::U32), init: GenExpr::Param(0) }];
            let body = vec![GenStmt::WhileLoop {
                bound: 120,
                body: vec![GenStmt::Assign {
                    local: 0,
                    expr: GenExpr::BinArith {
                        op: GenArithOp::Add,
                        ty: IntKind::U32,
                        lhs: Box::new(GenExpr::Local(0)),
                        rhs: Box::new(GenExpr::Lit(MirValue::Int {
                            int_kind: IntKind::U32,
                            bits: 1,
                        })),
                    },
                }],
                break_cond: None,
                continue_cond: None,
            }];
            GenProgram {
                case_id,
                fn_name,
                master_seed: config.master_seed,
                case_index,
                category: GenCategory::ScopeControl,
                is_unsafe: false,
                params,
                locals,
                body,
                ret_ty: GenType::Int(IntKind::U32),
                ret_expr: GenExpr::Local(0),
                fuel: config.default_fuel.min(40),
            }
        }
    }
}

fn pick_copy_local(rng: &mut SplitMix64, locals: &[GenLocal]) -> usize {
    let copy_indices: Vec<usize> = locals
        .iter()
        .enumerate()
        .filter_map(|(i, l)| (!matches!(l.ty, GenType::Enum(_))).then_some(i))
        .collect();
    if copy_indices.is_empty() { 0 } else { *rng.pick(&copy_indices) }
}

fn pick_move_enum_local(locals: &[GenLocal]) -> usize {
    locals.iter().position(|l| matches!(l.ty, GenType::Enum(_))).unwrap_or(0)
}

fn gen_safe_stmt(
    rng: &mut SplitMix64,
    params: &[GenParam],
    locals: &[GenLocal],
    boundary_bias: bool,
    depth: usize,
    remaining: &mut usize,
) -> GenStmt {
    debug_assert!(*remaining >= 1);
    let can_move_reinit = *remaining >= 3;
    let can_branch = depth > 0 && *remaining >= 2;
    let can_loop = depth > 0 && *remaining >= 4;
    let mut choices: [u8; 5] = [0; 5];
    let mut n_choices = 0usize;
    choices[n_choices] = 0;
    n_choices += 1;
    if can_move_reinit {
        choices[n_choices] = 1;
        n_choices += 1;
    }
    if can_branch {
        choices[n_choices] = 2;
        n_choices += 1;
    }
    if can_loop {
        choices[n_choices] = 3;
        n_choices += 1;
    }
    if n_choices > 1 {
        choices[n_choices] = 4;
        n_choices += 1;
    }
    let roll = choices[rng.gen_range(n_choices)];
    match roll {
        1 => {
            *remaining -= 3;
            let local = pick_move_enum_local(locals);
            let target_ty = locals[local].ty;
            let expr = gen_expr_of_type(rng, target_ty, params, locals, boundary_bias, 1);
            GenStmt::MoveReinit { local, expr }
        }
        2 => {
            *remaining -= 1;
            let cond = gen_expr_of_type(rng, GenType::Bool, params, locals, boundary_bias, 2);
            let then_len = 1 + rng.gen_range((*remaining).min(2));
            let mut then_body = Vec::with_capacity(then_len);
            for _ in 0..then_len {
                if *remaining == 0 {
                    break;
                }
                then_body.push(gen_safe_stmt(
                    rng,
                    params,
                    locals,
                    boundary_bias,
                    depth - 1,
                    remaining,
                ));
            }
            let else_len = if *remaining > 0 { rng.gen_range((*remaining).min(1) + 1) } else { 0 };
            let mut else_body = Vec::with_capacity(else_len);
            for _ in 0..else_len {
                if *remaining == 0 {
                    break;
                }
                else_body.push(gen_safe_stmt(
                    rng,
                    params,
                    locals,
                    boundary_bias,
                    depth - 1,
                    remaining,
                ));
            }
            GenStmt::IfElse { cond, then_body, else_body }
        }
        3 => {
            // Base loop scaffolding renders `let mut __loop_i`, `while`, and
            // `__loop_i = __loop_i + 1` (3 statements), plus body and optional
            // `if ... { continue; }` / `if ... { break; }` (2 statements each).
            *remaining -= 3;
            let bound = if depth < 2 {
                (rng.gen_range(2) + 1) as u32
            } else {
                (rng.gen_range(6) + 1) as u32
            };
            let body_len = 1 + rng.gen_range((*remaining).min(2));
            let mut body = Vec::with_capacity(body_len);
            for _ in 0..body_len {
                if *remaining == 0 {
                    break;
                }
                body.push(gen_safe_stmt(rng, params, locals, boundary_bias, depth - 1, remaining));
            }
            let break_cond = if *remaining >= 2 && rng.coin(1, 3) {
                *remaining -= 2;
                Some(gen_expr_of_type(rng, GenType::Bool, params, locals, boundary_bias, 1))
            } else {
                None
            };
            let continue_cond = if *remaining >= 2 && rng.coin(1, 4) {
                *remaining -= 2;
                Some(gen_expr_of_type(rng, GenType::Bool, params, locals, boundary_bias, 1))
            } else {
                None
            };
            GenStmt::WhileLoop { bound, body, break_cond, continue_cond }
        }
        _ => {
            *remaining -= 1;
            let local = pick_copy_local(rng, locals);
            let target_ty = locals[local].ty;
            let expr = gen_expr_of_type(rng, target_ty, params, locals, boundary_bias, 2);
            GenStmt::Assign { local, expr }
        }
    }
}

/// Build an expression folding the post-body value of every local
/// `v0..v_{k-1}` into a single `u128` expression (referencing each local at
/// most once so non-`Copy` enum slots are never moved twice).
fn build_initial_u128_mix_expr(locals: &[GenLocal]) -> GenExpr {
    let u128_ty = GenType::Int(IntKind::U128);
    let mut acc: Option<GenExpr> = None;
    for (idx, loc) in locals.iter().enumerate() {
        let term = if loc.ty == u128_ty {
            GenExpr::Local(idx)
        } else {
            GenExpr::Cast { expr: Box::new(GenExpr::Local(idx)), src_ty: loc.ty, dst_ty: u128_ty }
        };
        acc = Some(match acc {
            None => term,
            Some(prev) => GenExpr::BinArith {
                op: if idx % 2 == 0 { GenArithOp::Add } else { GenArithOp::BitXor },
                ty: IntKind::U128,
                lhs: Box::new(prev),
                rhs: Box::new(term),
            },
        });
    }
    acc.unwrap_or(GenExpr::Lit(MirValue::Int { int_kind: IntKind::U128, bits: 0 }))
}

/// Xor-fold all 16 byte lanes (`>> 8`, `>> 16`, ..., `>> 64`, ..., `>> 120`) of
/// `Copy` `u128` local `mix_idx` in a single expression without emitting extra
/// body statements so flipping any bit `0..127` toggles bit `b % 8` of byte 0.
fn fold_u128_bytes_expr(mix_idx: usize) -> GenExpr {
    let mut acc = GenExpr::Local(mix_idx);
    for shift_amt in [64u128, 32, 16, 8, 24, 40, 48, 56, 72, 80, 88, 96, 104, 112, 120] {
        let shifted = GenExpr::Shift {
            op: GenShiftOp::Shr,
            lhs_ty: IntKind::U128,
            rhs_ty: IntKind::U32,
            lhs: Box::new(GenExpr::Local(mix_idx)),
            rhs: Box::new(GenExpr::Lit(MirValue::Int { int_kind: IntKind::U32, bits: shift_amt })),
        };
        acc = GenExpr::BinArith {
            op: GenArithOp::BitXor,
            ty: IntKind::U128,
            lhs: Box::new(acc),
            rhs: Box::new(shifted),
        };
    }
    acc
}

/// Materialize the post-body `u128` local mixer via a single `GenStmt::Assign`
/// when `emit_mixer_stmt` is true (`max_stmts >= 2`), or inline with zero added
/// statements when `max_stmts == 1`.
fn materialize_u128_mix_expr(
    locals: &mut Vec<GenLocal>,
    body: &mut Vec<GenStmt>,
    emit_mixer_stmt: bool,
) -> GenExpr {
    let initial_fold = build_initial_u128_mix_expr(locals);
    if !emit_mixer_stmt {
        return initial_fold;
    }
    let u128_ty = GenType::Int(IntKind::U128);
    let mix_idx = locals.len();
    locals.push(GenLocal {
        ty: u128_ty,
        init: GenExpr::Lit(MirValue::Int { int_kind: IntKind::U128, bits: 0 }),
    });
    body.push(GenStmt::Assign { local: mix_idx, expr: initial_fold });
    fold_u128_bytes_expr(mix_idx)
}

fn project_expr_to_int(expr: GenExpr, dst: IntKind) -> GenExpr {
    if dst == IntKind::U128 {
        expr
    } else {
        GenExpr::Cast {
            expr: Box::new(expr),
            src_ty: GenType::Int(IntKind::U128),
            dst_ty: GenType::Int(dst),
        }
    }
}

fn gen_safe_return(
    rng: &mut SplitMix64,
    params: &[GenParam],
    locals: &mut Vec<GenLocal>,
    body: &mut Vec<GenStmt>,
    primary_int: IntKind,
    boundary_bias: bool,
    emit_mixer_stmt: bool,
) -> (GenType, GenExpr) {
    // Keep `GEN_UNIT` returns rare (`1/32` of the `% 7 == 6` boundary arm, i.e.
    // `1/224` of `BoundaryEdgeCase` and `0%` of `SafeAdmitted`) so non-unit
    // returns observe the post-body `u128` local accumulator.
    if boundary_bias && rng.gen_range(32) == 0 {
        return (GenType::Unit, GenExpr::Lit(MirValue::Unit));
    }
    let roll = rng.gen_range(10);
    // Generate the base return expression against pre-mixer locals before
    // appending `v_mix` so random `Local(i)` picks never bypass `v_mix`.
    match roll {
        0..=5 => {
            let ret_ty = GenType::Int(primary_int);
            let expr = gen_expr_of_type(rng, ret_ty, params, locals, boundary_bias, 2);
            let mix_expr = materialize_u128_mix_expr(locals, body, emit_mixer_stmt);
            let live_mix = project_expr_to_int(mix_expr, primary_int);
            (
                ret_ty,
                GenExpr::BinArith {
                    op: GenArithOp::BitXor,
                    ty: primary_int,
                    lhs: Box::new(expr),
                    rhs: Box::new(live_mix),
                },
            )
        }
        6 => {
            let ret_ty = GenType::Bool;
            let expr = gen_expr_of_type(rng, ret_ty, params, locals, boundary_bias, 2);
            let mix_expr = materialize_u128_mix_expr(locals, body, emit_mixer_stmt);
            let mix_bool = if emit_mixer_stmt {
                // `mix_expr` references `Copy` `v_mix`, so nibble/bit folding
                // is copy-safe and toggles bit 0 on any single-bit flip across
                // all 128 bits.
                let mut parity = project_expr_to_int(mix_expr, IntKind::U8);
                for s in [4u128, 2, 1] {
                    let sh = GenExpr::Shift {
                        op: GenShiftOp::Shr,
                        lhs_ty: IntKind::U8,
                        rhs_ty: IntKind::U32,
                        lhs: Box::new(parity.clone()),
                        rhs: Box::new(GenExpr::Lit(MirValue::Int {
                            int_kind: IntKind::U32,
                            bits: s,
                        })),
                    };
                    parity = GenExpr::BinArith {
                        op: GenArithOp::BitXor,
                        ty: IntKind::U8,
                        lhs: Box::new(parity),
                        rhs: Box::new(sh),
                    };
                }
                let low_bit = GenExpr::BinArith {
                    op: GenArithOp::BitAnd,
                    ty: IntKind::U8,
                    lhs: Box::new(parity),
                    rhs: Box::new(GenExpr::Lit(MirValue::Int { int_kind: IntKind::U8, bits: 1 })),
                };
                GenExpr::Cmp {
                    op: GenCmpOp::Ne,
                    lhs: Box::new(low_bit),
                    rhs: Box::new(GenExpr::Lit(MirValue::Int { int_kind: IntKind::U8, bits: 0 })),
                }
            } else {
                // At `max_stmts == 1`, `mix_expr` moves non-`Copy` enum locals
                // inline, so evaluate `mix_expr` once.
                GenExpr::Cmp {
                    op: GenCmpOp::Ne,
                    lhs: Box::new(mix_expr),
                    rhs: Box::new(GenExpr::Lit(MirValue::Int { int_kind: IntKind::U128, bits: 0 })),
                }
            };
            (
                ret_ty,
                GenExpr::BoolLogic {
                    op: GenBoolBinOp::BitXor,
                    lhs: Box::new(expr),
                    rhs: Box::new(mix_bool),
                },
            )
        }
        7 => {
            let ret_ty = GenType::Int(primary_int);
            let op = pick_sysroot_op_for_kind(rng, primary_int);
            let rhs =
                gen_expr_of_type(rng, GenType::Int(primary_int), params, locals, boundary_bias, 1);
            let mix_expr = materialize_u128_mix_expr(locals, body, emit_mixer_stmt);
            let live_mix = project_expr_to_int(mix_expr, primary_int);
            (
                ret_ty,
                GenExpr::SysrootNum {
                    op,
                    ty: primary_int,
                    lhs: Box::new(live_mix),
                    rhs: Box::new(rhs),
                    guarded: op.is_unchecked(),
                },
            )
        }
        8 => {
            let ret_ty = GenType::Ordering;
            let rhs = gen_expr_of_type(
                rng,
                GenType::Int(IntKind::U128),
                params,
                locals,
                boundary_bias,
                1,
            );
            let mix_expr = materialize_u128_mix_expr(locals, body, emit_mixer_stmt);
            (ret_ty, GenExpr::ThreeWayCmp { lhs: Box::new(mix_expr), rhs: Box::new(rhs) })
        }
        _ => {
            let ret_ty = GenType::Char;
            let base = gen_expr_of_type(rng, ret_ty, params, locals, boundary_bias, 1);
            let mix_expr = materialize_u128_mix_expr(locals, body, emit_mixer_stmt);
            let base_u8 = GenExpr::Cast {
                expr: Box::new(base),
                src_ty: GenType::Char,
                dst_ty: GenType::Int(IntKind::U8),
            };
            let mixed_u8 = GenExpr::BinArith {
                op: GenArithOp::BitXor,
                ty: IntKind::U8,
                lhs: Box::new(base_u8),
                rhs: Box::new(project_expr_to_int(mix_expr, IntKind::U8)),
            };
            (
                ret_ty,
                GenExpr::Cast {
                    expr: Box::new(mixed_u8),
                    src_ty: GenType::Int(IntKind::U8),
                    dst_ty: GenType::Char,
                },
            )
        }
    }
}

fn gen_atom_of_type(
    rng: &mut SplitMix64,
    ty: GenType,
    params: &[GenParam],
    locals: &[GenLocal],
    boundary_bias: bool,
) -> GenExpr {
    // Non-`Copy` enum values inside expressions always materialize via `const`
    // items (`GEN_SIGNED_*`, `GEN_UNSIGNED_*`) so parameters and locals are
    // never moved twice across loop iterations or branches.
    if matches!(ty, GenType::Enum(_)) {
        return GenExpr::Lit(gen_value_for_type(rng, ty, boundary_bias));
    }
    let mut candidates = Vec::new();
    for (idx, p) in params.iter().enumerate() {
        if p.ty == ty {
            candidates.push(GenExpr::Param(idx));
        }
    }
    for (idx, l) in locals.iter().enumerate() {
        if l.ty == ty {
            candidates.push(GenExpr::Local(idx));
        }
    }
    if !candidates.is_empty() && rng.coin(3, 4) {
        return rng.pick(&candidates).clone();
    }
    GenExpr::Lit(gen_value_for_type(rng, ty, boundary_bias))
}

fn gen_expr_of_type(
    rng: &mut SplitMix64,
    ty: GenType,
    params: &[GenParam],
    locals: &[GenLocal],
    boundary_bias: bool,
    depth: usize,
) -> GenExpr {
    if depth == 0 {
        return gen_atom_of_type(rng, ty, params, locals, boundary_bias);
    }
    match ty {
        GenType::Int(kind) => match rng.gen_range(11) {
            0 => gen_atom_of_type(rng, ty, params, locals, boundary_bias),
            1..=3 => {
                let op = *rng.pick(&GenArithOp::ALL);
                let lhs = gen_expr_of_type(rng, ty, params, locals, boundary_bias, depth - 1);
                let rhs = gen_expr_of_type(rng, ty, params, locals, boundary_bias, depth - 1);
                GenExpr::BinArith { op, ty: kind, lhs: Box::new(lhs), rhs: Box::new(rhs) }
            }
            4 => {
                let op = if rng.coin(1, 2) { GenShiftOp::Shl } else { GenShiftOp::Shr };
                let rhs_ty = *rng.pick(&ALL_INT_KINDS);
                let lhs = gen_expr_of_type(rng, ty, params, locals, boundary_bias, depth - 1);
                let rhs = gen_expr_of_type(
                    rng,
                    GenType::Int(rhs_ty),
                    params,
                    locals,
                    boundary_bias,
                    depth - 1,
                );
                GenExpr::Shift { op, lhs_ty: kind, rhs_ty, lhs: Box::new(lhs), rhs: Box::new(rhs) }
            }
            5 => {
                let op = pick_sysroot_op_for_kind(rng, kind);
                let lhs = gen_expr_of_type(rng, ty, params, locals, boundary_bias, depth - 1);
                let rhs = gen_expr_of_type(rng, ty, params, locals, boundary_bias, depth - 1);
                GenExpr::SysrootNum {
                    op,
                    ty: kind,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    guarded: op.is_unchecked(),
                }
            }
            6 => {
                let op =
                    if kind.is_signed() && rng.coin(1, 2) { GenUnOp::Neg } else { GenUnOp::Not };
                let operand = gen_expr_of_type(rng, ty, params, locals, boundary_bias, depth - 1);
                GenExpr::Unary { op, ty, operand: Box::new(operand) }
            }
            7 => {
                // `IntToInt` cast from another integer, `bool`, or `char`.
                let src_ty = match rng.gen_range(4) {
                    0 => GenType::Bool,
                    1 => GenType::Char,
                    _ => GenType::Int(*rng.pick(&ALL_INT_KINDS)),
                };
                let inner = gen_expr_of_type(rng, src_ty, params, locals, boundary_bias, depth - 1);
                GenExpr::Cast { expr: Box::new(inner), src_ty, dst_ty: ty }
            }
            8 => {
                // Match on an enum parameter if one exists, otherwise
                // `MatchOrdering`.
                if let Some((pidx, enum_kind)) = params.iter().enumerate().find_map(|(i, p)| {
                    if let GenType::Enum(e) = p.ty { Some((i, e)) } else { None }
                }) {
                    let arms = (0..enum_kind.variants().len())
                        .map(|_| {
                            gen_expr_of_type(rng, ty, params, locals, boundary_bias, depth - 1)
                        })
                        .collect();
                    GenExpr::MatchEnum { param_idx: pidx, enum_kind, ty, arms }
                } else {
                    let scrutinee = gen_expr_of_type(
                        rng,
                        GenType::Ordering,
                        params,
                        locals,
                        boundary_bias,
                        depth - 1,
                    );
                    GenExpr::MatchOrdering {
                        scrutinee: Box::new(scrutinee),
                        ty,
                        less: Box::new(gen_expr_of_type(
                            rng,
                            ty,
                            params,
                            locals,
                            boundary_bias,
                            depth - 1,
                        )),
                        equal: Box::new(gen_expr_of_type(
                            rng,
                            ty,
                            params,
                            locals,
                            boundary_bias,
                            depth - 1,
                        )),
                        greater: Box::new(gen_expr_of_type(
                            rng,
                            ty,
                            params,
                            locals,
                            boundary_bias,
                            depth - 1,
                        )),
                    }
                }
            }
            9 => {
                let scrutinee = gen_expr_of_type(rng, ty, params, locals, boundary_bias, depth - 1);
                let pool = boundary_bits_for_int(kind);
                let mut seen = BTreeSet::new();
                let mut arms = Vec::new();
                for _ in 0..2 {
                    let pat = *rng.pick(&pool);
                    if seen.insert(pat) {
                        arms.push((
                            pat,
                            gen_expr_of_type(rng, ty, params, locals, boundary_bias, depth - 1),
                        ));
                    }
                }
                let otherwise = gen_expr_of_type(rng, ty, params, locals, boundary_bias, depth - 1);
                GenExpr::MatchInt {
                    scrutinee: Box::new(scrutinee),
                    scrutinee_ty: kind,
                    ty,
                    arms,
                    otherwise: Box::new(otherwise),
                }
            }
            _ => gen_atom_of_type(rng, ty, params, locals, boundary_bias),
        },
        GenType::Bool => match rng.gen_range(5) {
            0 => gen_atom_of_type(rng, GenType::Bool, params, locals, boundary_bias),
            1 => {
                let operand =
                    gen_expr_of_type(rng, GenType::Bool, params, locals, boundary_bias, depth - 1);
                GenExpr::Unary { op: GenUnOp::Not, ty: GenType::Bool, operand: Box::new(operand) }
            }
            2 => {
                let op = *rng.pick(&GenBoolBinOp::ALL);
                let lhs =
                    gen_expr_of_type(rng, GenType::Bool, params, locals, boundary_bias, depth - 1);
                let rhs =
                    gen_expr_of_type(rng, GenType::Bool, params, locals, boundary_bias, depth - 1);
                GenExpr::BoolLogic { op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
            }
            _ => {
                let cmp_ty = match rng.gen_range(4) {
                    0 => GenType::Bool,
                    1 => GenType::Char,
                    _ => GenType::Int(
                        locals
                            .first()
                            .and_then(|l| match l.ty {
                                GenType::Int(k) => Some(k),
                                _ => None,
                            })
                            .unwrap_or(IntKind::U32),
                    ),
                };
                let op = *rng.pick(&GenCmpOp::ALL);
                let lhs = gen_expr_of_type(rng, cmp_ty, params, locals, boundary_bias, depth - 1);
                let rhs = gen_expr_of_type(rng, cmp_ty, params, locals, boundary_bias, depth - 1);
                GenExpr::Cmp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
            }
        },
        GenType::Char => match rng.gen_range(3) {
            0 => gen_atom_of_type(rng, GenType::Char, params, locals, boundary_bias),
            1 => {
                let byte = gen_expr_of_type(
                    rng,
                    GenType::Int(IntKind::U8),
                    params,
                    locals,
                    boundary_bias,
                    depth - 1,
                );
                GenExpr::Cast {
                    expr: Box::new(byte),
                    src_ty: GenType::Int(IntKind::U8),
                    dst_ty: GenType::Char,
                }
            }
            _ => gen_atom_of_type(rng, GenType::Char, params, locals, boundary_bias),
        },
        GenType::Ordering => {
            if rng.coin(1, 2) {
                let cmp_ty = if rng.coin(1, 4) {
                    GenType::Char
                } else {
                    GenType::Int(*rng.pick(&ALL_INT_KINDS))
                };
                let lhs = gen_expr_of_type(rng, cmp_ty, params, locals, boundary_bias, depth - 1);
                let rhs = gen_expr_of_type(rng, cmp_ty, params, locals, boundary_bias, depth - 1);
                GenExpr::ThreeWayCmp { lhs: Box::new(lhs), rhs: Box::new(rhs) }
            } else {
                gen_atom_of_type(rng, GenType::Ordering, params, locals, boundary_bias)
            }
        }
        GenType::Unit => GenExpr::Lit(MirValue::Unit),
        GenType::Enum(_) => gen_atom_of_type(rng, ty, params, locals, boundary_bias),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splitmix64_case_generation_is_deterministic_and_independent() {
        let cfg = GenConfig { master_seed: 4242, max_stmts: 6, ub_ratio: 0.25, default_fuel: 500 };
        let a = generate_case(&cfg, 17);
        let b = generate_case(&cfg, 17);
        assert_eq!(a, b);
        assert_eq!(a.render_standalone(), b.render_standalone());

        let c = generate_case(&cfg, 18);
        assert_ne!(a.render_fn_item(), c.render_fn_item());

        assert!(GenConfig { max_stmts: 0, ..cfg.clone() }.validate().is_err());
        assert!(GenConfig { max_stmts: 21, ..cfg.clone() }.validate().is_err());
        assert!(GenConfig { ub_ratio: 0.90, ..cfg.clone() }.validate().is_err());
        assert!(GenConfig { default_fuel: 0, ..cfg }.validate().is_err());

        // Find a ScopeControl loop-variant case and verify effective fuel
        // is capped at `min(default_fuel, 40)` both above and below `40`.
        let hi_cfg = GenConfig {
            master_seed: 20_261_124,
            max_stmts: 6,
            ub_ratio: 0.20,
            default_fuel: 1_500,
        };
        let lo_cfg = GenConfig { default_fuel: 12, ..hi_cfg };
        let mut saw_loop_scope = false;
        for idx in 0..64 {
            let hi_p = generate_case(&hi_cfg, idx);
            if hi_p.category == GenCategory::ScopeControl && hi_p.fuel != hi_cfg.default_fuel {
                assert_eq!(hi_p.fuel, 40);
                let lo_p = generate_case(&lo_cfg, idx);
                assert_eq!(lo_p.fuel, 12);
                saw_loop_scope = true;
                break;
            }
        }
        assert!(saw_loop_scope, "expected ScopeControl fuel-exhaustion case");
    }

    #[test]
    fn campaign_covers_all_four_categories_and_renders_valid_rust_items() {
        let cfg = GenConfig::default();
        let progs = generate_campaign(&cfg, 64);
        assert_eq!(progs.len(), 64);

        let safe = progs.iter().filter(|p| p.category == GenCategory::SafeAdmitted).count();
        let boundary = progs.iter().filter(|p| p.category == GenCategory::BoundaryEdgeCase).count();
        let ub = progs.iter().filter(|p| p.category == GenCategory::TargetedUbProbe).count();
        let scope = progs.iter().filter(|p| p.category == GenCategory::ScopeControl).count();

        assert!(safe > 0, "expected SafeAdmitted cases");
        assert!(boundary > 0, "expected BoundaryEdgeCase cases");
        assert!(ub > 0, "expected TargetedUbProbe cases");
        assert!(scope > 0, "expected ScopeControl cases");

        let refs: Vec<&GenProgram> = progs.iter().collect();
        let batch_src = render_batch_crate(&refs);
        assert!(batch_src.contains("#![allow("));
        assert!(!batch_src.contains("core_intrinsics"));
        assert!(batch_src.contains("pub enum GenSignedTag"));
        assert!(batch_src.contains("pub enum GenZstUnit"));
        for p in &progs {
            assert!(batch_src.contains(&format!("fn {}(", p.fn_name)));
            assert!(p.node_count() >= 1);
        }
    }

    #[test]
    fn safe_admitted_programs_keep_locals_live_in_return_and_use_non_copy_move_reinit() {
        let cfg = GenConfig {
            master_seed: 20_261_124,
            max_stmts: 8,
            ub_ratio: 0.20,
            default_fuel: 1_500,
        };
        let progs = generate_campaign(&cfg, 200);
        let safe_progs: Vec<&GenProgram> =
            progs.iter().filter(|p| p.category == GenCategory::SafeAdmitted).collect();
        assert!(!safe_progs.is_empty());

        let unit_returns = progs
            .iter()
            .filter(|p| p.category.counts_toward_admission() && p.ret_ty == GenType::Unit)
            .count();
        let eligible = progs.iter().filter(|p| p.category.counts_toward_admission()).count();
        assert!(
            (unit_returns as f64) <= (eligible as f64) * 0.02 + 1.0,
            "unit return rate too high: {unit_returns}/{eligible}"
        );

        let mut saw_move_reinit = false;
        for p in safe_progs {
            assert_ne!(p.ret_ty, GenType::Unit, "SafeAdmitted must return a value");
            let mix_idx = p.locals.len() - 1;
            assert_eq!(p.locals[mix_idx].ty, GenType::Int(IntKind::U128));
            let mut p_ret = BTreeSet::new();
            let mut l_ret = BTreeSet::new();
            p.ret_expr.collect_refs(&mut p_ret, &mut l_ret);
            assert!(
                l_ret.contains(&mix_idx),
                "{}: return expression must consume u128 mixer local v{mix_idx}",
                p.case_id
            );

            let mut p_body = BTreeSet::new();
            let mut l_body = BTreeSet::new();
            for s in &p.body {
                s.collect_refs(&mut p_body, &mut l_body);
            }
            for idx in 0..mix_idx {
                assert!(
                    l_body.contains(&idx),
                    "{}: local v{idx} missing from post-body u128 mixer fold",
                    p.case_id
                );
            }
            let rendered = p.render_fn_item();
            assert!(
                rendered.contains(">> (64u32)"),
                "{}: expected u128 high-bit xor-fold in rendered function",
                p.case_id
            );
            fn check_stmt_moves(s: &GenStmt, locals: &[GenLocal], saw: &mut bool) {
                match s {
                    GenStmt::MoveReinit { local, .. } => {
                        *saw = true;
                        assert!(
                            matches!(
                                locals[*local].ty,
                                GenType::Enum(GenEnumKind::SignedTag | GenEnumKind::UnsignedTag)
                            ),
                            "MoveReinit must target a non-Copy, non-ZST multi-variant enum local"
                        );
                    }
                    GenStmt::IfElse { then_body, else_body, .. } => {
                        for inner in then_body.iter().chain(else_body.iter()) {
                            check_stmt_moves(inner, locals, saw);
                        }
                    }
                    GenStmt::WhileLoop { body, .. } => {
                        for inner in body {
                            check_stmt_moves(inner, locals, saw);
                        }
                    }
                    _ => {}
                }
            }
            for s in &p.body {
                check_stmt_moves(s, &p.locals, &mut saw_move_reinit);
            }
        }
        assert!(saw_move_reinit, "expected SafeAdmitted campaign to emit MoveReinit");
    }

    #[test]
    fn sub_percent_nonzero_ub_ratio_preserves_forced_and_sampled_probes() {
        let sub_pct_cfg = GenConfig {
            master_seed: 20_261_124,
            max_stmts: 4,
            ub_ratio: 0.001,
            default_fuel: 1_500,
        };
        let small = generate_campaign(&sub_pct_cfg, 8);
        assert_eq!(small[2].category, GenCategory::TargetedUbProbe);

        let sampled_tail_probes = (4..5_000)
            .filter(|&idx| {
                let mut rng = SplitMix64::for_case(sub_pct_cfg.master_seed, idx);
                choose_category(&mut rng, &sub_pct_cfg, idx) == GenCategory::TargetedUbProbe
            })
            .count();
        assert!(
            sampled_tail_probes > 0,
            "expected random tail to sample TargetedUbProbe at ub_ratio=0.001"
        );

        let tiny_pos_cfg = GenConfig { ub_ratio: f64::MIN_POSITIVE, ..sub_pct_cfg };
        assert_eq!(generate_case(&tiny_pos_cfg, 2).category, GenCategory::TargetedUbProbe);

        let zero_cfg = GenConfig { ub_ratio: 0.0, ..sub_pct_cfg };
        let zero_cases = generate_campaign(&zero_cfg, 64);
        assert!(zero_cases.iter().all(|p| p.category != GenCategory::TargetedUbProbe));
    }

    #[test]
    fn max_stmts_bounds_total_nested_and_mixer_statements_across_all_categories() {
        fn count_rendered_body_stmts(prog: &GenProgram) -> usize {
            let mut out = String::new();
            let mut loop_counter = 0usize;
            for s in &prog.body {
                s.render_into(&mut out, 0, &mut loop_counter);
            }
            let mut count = 0usize;
            for raw in out.lines() {
                let t = raw.trim();
                if t.is_empty() || t == "{" || t == "}" || t == "} else {" {
                    continue;
                }
                if t.ends_with("{ continue; }") || t.ends_with("{ break; }") {
                    count += 2;
                } else {
                    count += 1;
                }
            }
            count
        }

        assert_eq!(GenStmt::MoveReinit { local: 0, expr: GenExpr::Local(0) }.stmt_count(), 3);

        for max_stmts in 1..=20 {
            let cfg = GenConfig {
                master_seed: 20_261_125,
                max_stmts,
                ub_ratio: 0.25,
                default_fuel: 1_500,
            };
            let progs = generate_campaign(&cfg, 64);
            for p in &progs {
                let count = p.total_stmt_count();
                let rendered = count_rendered_body_stmts(p);
                assert_eq!(
                    count, rendered,
                    "{} stmt_count ({count}) != rendered body stmts ({rendered})",
                    p.case_id
                );
                assert!(
                    rendered <= max_stmts,
                    "{} ({:?}) emitted {rendered} rendered body statements > max_stmts={max_stmts}",
                    p.case_id,
                    p.category
                );
            }
        }
    }

    #[test]
    fn golden_program_digests_match_validator_mirror() {
        let vectors: &[(u64, usize, f64, usize, &str, &str, usize)] = &[
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                0_usize,
                "safe_admitted",
                "e2fd491696d6681001803da57fdb27583286c5f63c65c3a5aa2ab78b3f4ba25c",
                5_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                1_usize,
                "boundary_edge_case",
                "1336e54688c1a79fc73cfcab3fb9728864384b5e6eeb6187906d138efeb10509",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                2_usize,
                "targeted_ub_probe",
                "6ce98615e3c587ef8276dca58c32b0384cd7b2005f2dd4d8afacbcc0e8f0b4e8",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                3_usize,
                "scope_control",
                "5a9874d0bb7a05f49ee57b82aa7dc57a31d241059ce7bebf691c102317c866d4",
                1_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                4_usize,
                "targeted_ub_probe",
                "a1d81c15a46b55610147c18eaab347859a64c7be5c8f91dfe5756f5464d2b968",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                5_usize,
                "safe_admitted",
                "c3200ddef18d41e6a26c901fcf5112760fc94fa7a620f0b387aac2f8ee9c06ec",
                3_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                6_usize,
                "boundary_edge_case",
                "a5d194cdbd598e8ed29d0f1c78b4bbd23b5bace9438685ca9cb6705556cf6964",
                4_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                7_usize,
                "safe_admitted",
                "ac8b9290d50e5d2f5ab89d9c1188c932be4278f51fa22ab1e024b5987fa1e924",
                5_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                8_usize,
                "targeted_ub_probe",
                "c711c8928b038f93370fb1460cf9f864ac6ae6953ada4d50bcdc32531e369f57",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                9_usize,
                "safe_admitted",
                "558cd52f05552e0306373964895a61a8a8d74bdc5e80b7bd584b2e944117dd56",
                5_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                10_usize,
                "safe_admitted",
                "84eadd2cc0bd8491b19998d04453e825218b7d3ad45155544d7e5aa9ff708768",
                4_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                11_usize,
                "safe_admitted",
                "b414419809c9b3cc52fad66d8da5129817dc40626c2d1af461a832ef3ed1e21b",
                3_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                12_usize,
                "targeted_ub_probe",
                "7ff22e7f75e9b9a895510ceb9846728d53cb14fea1241f8e37d061a2727d7361",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                13_usize,
                "safe_admitted",
                "3ff14ea53d66b0bf89eca6e53e6fcf36b5e3832fe6e9594539388b0fe779735c",
                4_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                14_usize,
                "boundary_edge_case",
                "8a0bc0f6335dd2d1314951fb2d65ff74239f73c6acc2e8e6ff28b025308eae1b",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                15_usize,
                "safe_admitted",
                "a986a7d1336427f663e5254c5f50728a8b05ed42f4155084291276a27d7d7273",
                5_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                16_usize,
                "safe_admitted",
                "024320010d274c70890dbe363f0acdb278195003830fb75af260d6b2d36474f4",
                5_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                17_usize,
                "targeted_ub_probe",
                "2287244d23fd055b28bb05fcd2bbb56b455f2cf66f46d733ad7857989d8de9ba",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                18_usize,
                "boundary_edge_case",
                "6405c981706b1fccf09cb9d83ef2ca54b39b3d96114a0a63bf6b5f105ebf7278",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                19_usize,
                "boundary_edge_case",
                "c599b92722d75f009edefc827398e7b584efe101999a6b37f01f3283e500b12c",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                20_usize,
                "safe_admitted",
                "f76446e1650e061b713eeb474388673174669d045a41e354a2d15d489f80bd3a",
                4_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                21_usize,
                "boundary_edge_case",
                "1bce866c5bfa17f8e7a8c939d887345ed4ea5f6aab2bffbdd812ca2c509c2c85",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                22_usize,
                "boundary_edge_case",
                "00be3a41577cd7fe729adab19c4c8a62d662622c32bd3f297b313d1181e2b6b1",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                23_usize,
                "boundary_edge_case",
                "2fe0cb1cdd9a17d21a5a753e04e3cf6f7c5dfaee029cef2b5d402eec9be08112",
                4_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                24_usize,
                "boundary_edge_case",
                "7cac59cf085608b26db5aa39b814e2ab5953b5b39050af158e9c4828368e89ec",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                25_usize,
                "targeted_ub_probe",
                "63b93911b351072306e5f6d3d8c2c35338374077f02928f9526fc142b0f6f685",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                26_usize,
                "boundary_edge_case",
                "a5027eb31f6347f21794987520fcb5e6a7db29e6940c09be91656e200058cdd2",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                27_usize,
                "boundary_edge_case",
                "5af4dd81d9787c001bb5b672efea23a5841b902d015a86932447883d0f5dfb42",
                3_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                28_usize,
                "targeted_ub_probe",
                "f2d629538ed1f275f7a41c468df3e55260db4028822ca3806610a3788e3fb553",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                29_usize,
                "safe_admitted",
                "06830ce55a390e393d96d7243874b3da66b6641dcbd0ace70be5ab41e219a64a",
                5_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                30_usize,
                "targeted_ub_probe",
                "aefb874b32365c9a1a7ea090d8c30422edc375d6fe3e71827700db6850fb80dc",
                2_usize,
            ),
            (
                20261124_u64,
                6_usize,
                0.2_f64,
                31_usize,
                "safe_admitted",
                "55cb06b68d05b6ec896ff651b6e37eb206fe3ab40a2fc15aae02c747f474b1d7",
                4_usize,
            ),
            (
                20261125_u64,
                1_usize,
                0.0_f64,
                0_usize,
                "safe_admitted",
                "d27a9bc278ad6ec255c932c4a189994bcf5f08ca2e6081543b564c41cfc6d554",
                4_usize,
            ),
            (
                20261125_u64,
                1_usize,
                0.0_f64,
                1_usize,
                "boundary_edge_case",
                "408a8e8c9a4b4eda02d74bc79eedf7b8818f1bae5f78607eeda328e31ffb9612",
                2_usize,
            ),
            (
                20261125_u64,
                1_usize,
                0.0_f64,
                2_usize,
                "safe_admitted",
                "916f021f63d3a42f547d643ebe6d94292ec7224f92492e2ad314c88eecc62715",
                4_usize,
            ),
            (
                20261125_u64,
                1_usize,
                0.0_f64,
                3_usize,
                "scope_control",
                "6d557494a145f837870b1dbee0c6e35bacb2e08a97493f6eed8a46742cc56fa0",
                1_usize,
            ),
            (
                20261125_u64,
                1_usize,
                0.0_f64,
                4_usize,
                "safe_admitted",
                "64bcd37be9b647b9a4f00c52458444dfbe823954ec943040ca01ee051b09ce6c",
                3_usize,
            ),
            (
                20261125_u64,
                1_usize,
                0.0_f64,
                5_usize,
                "boundary_edge_case",
                "a4427e9e3140b2a6f98b0fa9244c235dc0db09612ac40966f062f7d79bdc863c",
                3_usize,
            ),
            (
                20261125_u64,
                1_usize,
                0.0_f64,
                6_usize,
                "boundary_edge_case",
                "36017791ed46dd531e3b4f62ad08ddc7473791daa5932e4febe87d6a14e7b0af",
                2_usize,
            ),
            (
                20261125_u64,
                1_usize,
                0.0_f64,
                7_usize,
                "safe_admitted",
                "a32ec68abad7bf8f3637a6a0d94973b7fc97c693449cbfca4653cab319a32278",
                3_usize,
            ),
            (
                9001_u64,
                3_usize,
                0.85_f64,
                0_usize,
                "safe_admitted",
                "4184c0d3fe1bd55e5af67c53c739030620e808e4bba8a7dc1f4c8bbe4a832856",
                5_usize,
            ),
            (
                9001_u64,
                3_usize,
                0.85_f64,
                1_usize,
                "boundary_edge_case",
                "bb5fe843aaae862ab016b85c57a740bb4e1675f3662ac8cb543f5d25de4422cd",
                4_usize,
            ),
            (
                9001_u64,
                3_usize,
                0.85_f64,
                2_usize,
                "targeted_ub_probe",
                "e974fe7feb377aae812eb186a1f3d4481a415090523394c5d1ac458f3ad42021",
                2_usize,
            ),
            (
                9001_u64,
                3_usize,
                0.85_f64,
                3_usize,
                "scope_control",
                "1300903d43628a3dc12f4ba976c37fd193cc1ebff81b92454eeef83aef89726c",
                1_usize,
            ),
            (
                9001_u64,
                3_usize,
                0.85_f64,
                4_usize,
                "targeted_ub_probe",
                "5af8e6cd599284f0dfc22602c2ee3483008338f790236e043640d90cfd2446a9",
                2_usize,
            ),
            (
                9001_u64,
                3_usize,
                0.85_f64,
                5_usize,
                "targeted_ub_probe",
                "1b53fd1418fb87f93048391c9af510a83c424a8c33822c27e2223e58938089ac",
                2_usize,
            ),
            (
                9001_u64,
                3_usize,
                0.85_f64,
                6_usize,
                "targeted_ub_probe",
                "55d27f7ae0a70d7c908a013aeade23e9dae74ee82d0beba4c1c92b7b2e0f9c8d",
                2_usize,
            ),
            (
                9001_u64,
                3_usize,
                0.85_f64,
                7_usize,
                "targeted_ub_probe",
                "76ec1369abe677a7aa2f399a2ff61cf9de6f8b28fa5fd715f112f1f4e82ce7b8",
                2_usize,
            ),
            (
                314159_u64,
                12_usize,
                0.2_f64,
                0_usize,
                "safe_admitted",
                "9953702f5c9b04428987a0edb8a728d22013b258135df008dc6cd5a331694eaa",
                3_usize,
            ),
            (
                314159_u64,
                12_usize,
                0.2_f64,
                1_usize,
                "boundary_edge_case",
                "93ab39d8065e382a34a46fb47e6fa4550df04d7f265c4842793b23e6738d319c",
                2_usize,
            ),
            (
                314159_u64,
                12_usize,
                0.2_f64,
                2_usize,
                "targeted_ub_probe",
                "c785134e5afaabf6a5e51d580ece57b626f93a4d46ea01c0ef871f6bdd64b705",
                2_usize,
            ),
            (
                314159_u64,
                12_usize,
                0.2_f64,
                3_usize,
                "scope_control",
                "551cbfc99b5c8750d078a6862f99830e91d9944baab1d94a1f7351e6fc39c069",
                1_usize,
            ),
            (
                314159_u64,
                12_usize,
                0.2_f64,
                4_usize,
                "targeted_ub_probe",
                "9c75313fdb200e7272b9589c0599004fd8345197e7e92073f93d9da614e47deb",
                2_usize,
            ),
            (
                314159_u64,
                12_usize,
                0.2_f64,
                5_usize,
                "safe_admitted",
                "97ff81dff28ecc698e6c5b98f96aedc100854f3c6e7cf9fe84bd1f15f3312c22",
                3_usize,
            ),
            (
                314159_u64,
                12_usize,
                0.2_f64,
                6_usize,
                "boundary_edge_case",
                "8c710f7b792be8722b61d1993bfa50b979dcc1b7bd7442483e1b7780a4d5166c",
                3_usize,
            ),
            (
                314159_u64,
                12_usize,
                0.2_f64,
                7_usize,
                "targeted_ub_probe",
                "5ca8c2797a463acd0f0392cc5296a6ee3dd27d3664571fd3efc130fad65f8d6d",
                2_usize,
            ),
        ];
        let mut seen = BTreeSet::new();
        for &(seed, max_stmts, ub_ratio, idx, exp_cat, exp_sha, exp_argc) in vectors {
            let cfg = GenConfig { master_seed: seed, max_stmts, ub_ratio, default_fuel: 1_500 };
            let prog = generate_case(&cfg, idx);
            assert_eq!(prog.category.as_str(), exp_cat, "seed={seed} idx={idx}");
            assert_eq!(prog.args().len(), exp_argc, "seed={seed} idx={idx}");
            let actual_sha = prog.program_sha256();
            assert_eq!(actual_sha, exp_sha, "seed={seed} max_stmts={max_stmts} idx={idx}");
            assert!(seen.insert(actual_sha));
        }
    }

    #[test]
    fn gen_range_reduces_full_u64_before_narrowing() {
        // High 32 bits nonzero while low 32 bits are zero: truncating to u32
        // before `% 3` returns 0, whereas full u64 modulo preserves 1 and 2.
        let word = 0x0000_0001_0000_0000_u64;
        assert_eq!(word % 3, 1);
        assert_eq!(gen_range_from_word(word, 3), 1);
        let word2 = 0x0000_0002_0000_0000_u64;
        assert_eq!(word2 % 3, 2);
        assert_eq!(gen_range_from_word(word2, 3), 2);
        assert_eq!(gen_range_from_word(word2, 0), 0);
        assert_eq!(gen_range_from_word(word2, 1), 0);
    }
}
