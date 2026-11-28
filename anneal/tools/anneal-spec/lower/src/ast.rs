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

/// An integer associated constant that a specification may name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntConst {
    /// `T::MIN`, of type `T`.
    Min,
    /// `T::MAX`, of type `T`.
    Max,
    /// `T::BITS`, of type `u32`.
    Bits,
}

impl IntConst {
    pub fn rust_name(self) -> &'static str {
        match self {
            IntConst::Min => "MIN",
            IntConst::Max => "MAX",
            IntConst::Bits => "BITS",
        }
    }

    pub fn from_rust_name(name: &str) -> Option<Self> {
        match name {
            "MIN" => Some(IntConst::Min),
            "MAX" => Some(IntConst::Max),
            "BITS" => Some(IntConst::Bits),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Bool(bool),
    /// An integer literal and its optional type suffix (`5u8`).
    Int(u128, Option<IntTy>),
    /// An integer associated constant such as `usize::MAX`, whose value is
    /// fixed by the profile v1 target (64-bit `usize` and `isize`).
    IntConst(IntTy, IntConst),
    Unit,
    Ident(String),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// `e as T`, a cast to the fixed-width integer type `T`.
    Cast(Box<Expr>, IntTy),
    /// `name(args)`: a `#[anneal::pure]` helper or a built-in intrinsic.
    Call(String, Vec<Expr>),
    /// `receiver.name(args)`: an integer method.
    Method(String, Box<Expr>, Vec<Expr>),
    /// `math(e)` or `math { e }`.
    Math(Box<Expr>),
    /// `old(e)`; rejected by profile v1 lowering.
    Old(Box<Expr>),
    /// A parenthesized expression, kept so `(!a) == b` is distinguishable
    /// from the ambiguous `!a == b`.
    Paren(Box<Expr>),
    /// `if cond { then } else { otherwise }`, where an `else if` chain nests
    /// another `If` as `otherwise`. The `else` branch is required.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `let name [: ty] = init;` followed by `body`, the rest of its block.
    /// A block `{ let a = x; let b = y; e }` nests as `Let(a, Let(b, e))`.
    Let(Box<LetBinding>, Box<Expr>),
    /// `match scrutinee { arms }`.
    Match(Box<Expr>, Vec<Arm>),
}

/// One `match` arm: `pats => body`, where `pats` are the alternatives of an
/// or-pattern.
#[derive(Clone, Debug)]
pub struct Arm {
    pub pats: Vec<Pat>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum PatKind {
    /// `_`.
    Wild,
    /// A name that binds the scrutinee.
    Bind(String),
    Bool(bool),
    /// An integer literal: its sign, magnitude, and optional suffix.
    Int {
        neg: bool,
        mag: u128,
        suffix: Option<IntTy>,
    },
    /// `T::MIN`, `T::MAX`, or `T::BITS`.
    IntConst(IntTy, IntConst),
    /// `lo..=hi`, whose bounds are `Int` or `IntConst` patterns.
    Range(Box<Pat>, Box<Pat>),
}

/// The binding of one `let` statement.
#[derive(Clone, Debug)]
pub struct LetBinding {
    pub name: String,
    /// The type annotation, if any.
    pub ty: Option<Ty>,
    pub init: Expr,
    /// The span of the bound name.
    pub name_span: Span,
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
    /// `max_steps = E`: deterministic MIR small-step upper bound over entry
    /// arguments (counts abstract `Step` transitions, not wall-clock time).
    MaxSteps(Expr),
    /// `target = "path"`: overrides the derived item path.
    Target(String),
    /// `claim = "id"`: groups the item into the verification claim `id`
    /// instead of its singleton claim.
    Claim(String),
    /// `instantiate = [["u8"], ["u32"]]`: generic instantiations to verify.
    /// Profile v1 has no generics, so the lowering rejects it.
    Instantiate(Vec<Vec<String>>),
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
    /// The `claim = "..."` clause, if any; see [`SpecFn::claim_id`].
    pub claim: Option<String>,
    /// Whether the item was declared in `anneal::external_spec!` rather than
    /// by an inline attribute on the function itself.
    pub external: bool,
    /// The span of the function signature.
    pub sig_span: Span,
    /// The span of the `anneal::spec(...)` attribute.
    pub attr_span: Span,
    /// Index of the source file the item came from.
    pub file: usize,
}

impl SpecFn {
    /// The verification claim the item belongs to: its `claim = "..."`
    /// clause, or else its singleton claim [`mangle_slug`]`(path)`.
    pub fn claim_id(&self) -> String {
        self.claim.clone().unwrap_or_else(|| mangle_slug(&self.path))
    }
}

/// The singleton claim identifier of item `path`: `<T as Tr>::f` becomes
/// `impl_Tr_for_T__f` (with `unit` for a `()` self type), `::` becomes `__`,
/// and any other character that cannot appear in a Lean identifier becomes
/// `_`. A result that does not start with a letter gets a `c_` prefix.
pub fn mangle_slug(path: &str) -> String {
    let mut out = mangle_path(path);
    if !out.starts_with(|c: char| c.is_ascii_alphabetic()) {
        out.insert_str(0, "c_");
    }
    out
}

fn mangle_path(path: &str) -> String {
    if path == "()" {
        return "unit".to_string();
    }
    let mut out = String::new();
    let mut rest = path;
    while !rest.is_empty() {
        if let Some(stripped) = rest.strip_prefix("::") {
            out.push_str("__");
            rest = stripped;
        } else if let Some(inner) = rest.strip_prefix('<').and_then(|r| {
            // `<T as Tr>`: the qualified self type of a trait impl item.
            let end = r.find('>')?;
            let (ty, tr) = r[..end].split_once(" as ")?;
            Some((ty.to_string(), tr.to_string(), &r[end + 1..]))
        }) {
            let (ty, tr, after) = inner;
            out.push_str(&format!("impl_{}_for_{}", mangle_path(&tr), mangle_path(&ty)));
            rest = after;
        } else {
            let c = rest.chars().next().expect("non-empty");
            out.push(if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' });
            rest = &rest[c.len_utf8()..];
        }
    }
    out
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
