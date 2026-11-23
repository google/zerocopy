// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Syntax trees shared by the inline-attribute and `external_spec!` forms.
//!
//! Both attachment forms produce the same [`SpecUnit`], so they lower through
//! the same checker and emitter to byte-identical `Spec.lean`.

use proc_macro2::Span;

/// Fixed-width Rust integer types admitted by MIR profile v1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IntTy {
    pub bits: u32,
    pub signed: bool,
    /// Whether the type is `usize`/`isize` (64 bits on the profile v1 target).
    pub pointer_sized: bool,
}

impl IntTy {
    pub fn rust_name(self) -> String {
        match (self.signed, self.pointer_sized) {
            (false, true) => "usize".into(),
            (true, true) => "isize".into(),
            (false, false) => format!("u{}", self.bits),
            (true, false) => format!("i{}", self.bits),
        }
    }

    /// The inclusive range of mathematical values the type represents.
    pub fn range(self) -> (i128, u128) {
        if self.signed {
            let half = 1u128 << (self.bits - 1);
            (if self.bits == 128 { i128::MIN } else { -(half as i128) }, half - 1)
        } else {
            (0, if self.bits == 128 { u128::MAX } else { (1u128 << self.bits) - 1 })
        }
    }
}

/// Types of specification expressions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Unit,
    /// A Rust machine integer. Arithmetic on it must say whether it wraps
    /// (`wrapping_*`) or is mathematical (`math`).
    Int(IntTy),
    /// An unbounded mathematical integer, produced only inside `math`.
    Math,
    /// Never return type (`-> !`), valid only as a specified function's output.
    Never,
}

impl Ty {
    pub fn describe(self) -> String {
        match self {
            Ty::Bool => "bool".into(),
            Ty::Unit => "()".into(),
            Ty::Int(t) => t.rust_name(),
            Ty::Math => "math integer".into(),
            Ty::Never => "!".into(),
        }
    }

    pub fn is_integer(self) -> bool {
        matches!(self, Ty::Int(_) | Ty::Math)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Iff,
    Implies,
    Or,
    And,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    BitOr,
    BitXor,
    BitAnd,
    Shl,
    Shr,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

impl BinOp {
    pub fn rust(self) -> &'static str {
        match self {
            BinOp::Iff => "<==>",
            BinOp::Implies => "==>",
            BinOp::Or => "||",
            BinOp::And => "&&",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^",
            BinOp::BitAnd => "&",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
        }
    }

    pub fn is_comparison(self) -> bool {
        matches!(self, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
    }

    pub fn is_arith(self) -> bool {
        matches!(self, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Bool(bool),
    /// An integer literal and its optional type suffix (`5u8`).
    Int(u128, Option<IntTy>),
    Unit,
    Ident(String),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// `name(args)`: a `#[anneal::pure]` helper or a built-in intrinsic.
    Call(String, Vec<Expr>),
    /// `math(e)` or `math { e }`.
    Math(Box<Expr>),
    /// `old(e)`; rejected by profile v1 lowering.
    Old(Box<Expr>),
    /// A parenthesized expression, kept so `(!a) == b` is distinguishable
    /// from the ambiguous `!a == b`.
    Paren(Box<Expr>),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Effect {
    Total,
    Terminates,
    NoPanic,
    NoUnwind,
    MayDiverge,
    MayUnwind,
    MayPanic,
}

#[derive(Clone, Debug)]
pub enum Clause {
    /// `requires(P)`: the caller safety obligation on an `unsafe fn` and the
    /// behavioral domain on every function.
    Requires(Expr),
    /// `safety_requires(P)`: a caller safety obligation on an `unsafe fn`
    /// that does not restrict the behavioral domain.
    SafetyRequires(Expr),
    /// `ensures(|ret| Q)`; `binder` is `None` for `|_|` or a missing closure.
    Ensures {
        binder: Option<String>,
        body: Expr,
    },
    Effect(Effect),
    /// `target = "path"`: overrides the derived item path.
    Target(String),
}

#[derive(Clone, Debug)]
pub struct SpannedClause {
    pub clause: Clause,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ty: Ty,
    pub span: Span,
}

/// One specified function.
#[derive(Clone, Debug)]
pub struct SpecFn {
    /// The `rust-path-v1` item path (without the scheme prefix).
    pub path: String,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub is_unsafe: bool,
    pub clauses: Vec<SpannedClause>,
    /// `Some(reason)` when `#[anneal::vacuous_ok(reason = ...)]` waives the
    /// non-vacuity obligation.
    pub vacuous_ok: Option<String>,
    /// The span of the function signature.
    pub sig_span: Span,
    /// The span of the `anneal::spec(...)` attribute.
    pub attr_span: Span,
    /// Index of the source file the item came from.
    pub file: usize,
}

/// One `#[anneal::pure]` specification helper.
#[derive(Clone, Debug)]
pub struct PureFn {
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub body: Expr,
    pub span: Span,
    /// Index of the source file the item came from.
    pub file: usize,
}

#[derive(Clone, Debug, Default)]
pub struct SpecUnit {
    pub fns: Vec<SpecFn>,
    pub helpers: Vec<PureFn>,
}
