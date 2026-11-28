// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Type checking and lowering of checked specifications to Lean terms.
//!
//! Every specification boolean lowers to a Lean `Prop` and every integer to a
//! Lean `Int` holding its mathematical value, so the generated `Spec.lean`
//! never relies on coercions, saturating `Nat` subtraction, or totalized
//! division. The Rust type of each integer is still tracked here so that
//! arithmetic whose wrap-versus-mathematical meaning is ambiguous is
//! rejected rather than guessed.

use std::{cell::Cell, collections::BTreeMap};

use proc_macro2::Span;

use crate::{
    ast::{
        BinOp, Clause, Effect, Expr, ExprKind, IntConst, IntTy, LetBinding, Param, PureFn, SpecFn,
        Ty, UnOp,
    },
    diag::Diagnostic,
};

#[derive(Clone, Copy, Debug)]
struct IntLit {
    neg: bool,
    mag: u128,
}

impl IntLit {
    fn new(neg: bool, mag: u128) -> Self {
        Self { neg: neg && mag != 0, mag }
    }

    fn negate(self) -> Self {
        Self::new(!self.neg, self.mag)
    }

    fn to_lean(self) -> String {
        if self.neg {
            format!("({INT_NEG} {})", self.mag)
        } else {
            format!("({} : {INT})", self.mag)
        }
    }

    fn in_range(self, t: IntTy) -> bool {
        let (lo, hi) = t.range();
        if self.neg {
            t.signed && self.mag <= lo.unsigned_abs()
        } else {
            self.mag <= hi
        }
    }
}

impl std::fmt::Display for IntLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.neg {
            write!(f, "-{}", self.mag)
        } else {
            write!(f, "{}", self.mag)
        }
    }
}

/// A lowered `bool` expression (which lowers to a Lean `Prop`), paired with
/// its decidability status for value-choosing `if` and the nonzero facts it
/// establishes in true/false branches.
#[derive(Clone, Debug)]
struct Prop {
    term: String,
    undecidable: Option<(Span, String)>,
    on_true: Vec<String>,
    on_false: Vec<String>,
}

impl Prop {
    fn pure(term: impl Into<String>) -> Self {
        Self { term: term.into(), undecidable: None, on_true: Vec::new(), on_false: Vec::new() }
    }
}

/// A lowered expression.
#[derive(Clone, Debug)]
enum Low {
    Prop(Prop),
    Int(String, Ty),
    Unit(String),
    /// An integer literal whose type is fixed by context.
    Lit(IntLit, Span),
    /// An integer-valued `if` whose branches are all untyped literals, such
    /// as `if c { 1 } else { 0 }`: the lowered term, and each literal leaf
    /// to range-check once context fixes the type.
    UntypedIf(String, Vec<(IntLit, Span)>),
}

/// Which runtime helpers and binders the lowered text referenced.
#[derive(Default)]
pub struct Uses {
    pub q: Cell<bool>,
    pub out: Cell<bool>,
    pub val_int: Cell<bool>,
    pub val_nat: Cell<bool>,
    pub val_bool: Cell<bool>,
    pub arg: Cell<bool>,
}

pub struct HelperSig {
    pub lean_name: String,
    pub params: Vec<Ty>,
    pub ret: Ty,
}

#[derive(Clone)]
enum Binding {
    /// The `i`-th argument of the specified function.
    Arg(usize, Ty),
    /// The return value bound by `ensures(|ret| ...)`.
    Ret(Ty),
    /// A `#[anneal::pure]` helper parameter.
    HelperParam(String, Ty),
    /// A `let` binding: its Lean binder name and what it holds.
    Local(String, LocalKind),
}

/// What a `let` binding holds, as its Lean binder sees it.
#[derive(Clone)]
enum LocalKind {
    /// A `bool`, bound as a `Prop`. `decidable` is whether Lean can decide
    /// it, which an `if` that chooses a value needs of its condition.
    /// `when_true` and `when_false` are the nonzero facts that its
    /// initializer establishes when it holds and when it fails.
    Prop { decidable: bool, when_true: Vec<String>, when_false: Vec<String> },
    /// An integer of type `ty` (a machine type or `Ty::Math`), bound as an
    /// `Int`, with its value if its initializer is a constant.
    Int { ty: Ty, value: Option<IntLit> },
    /// A `()`, bound as a `Val`.
    Unit,
    /// A `max_steps` step count, bound as a `Nat`, with its value if its
    /// initializer is a constant.
    Nat { value: Option<IntLit> },
}

pub struct Env<'a> {
    pub helpers: &'a BTreeMap<String, HelperSig>,
    names: BTreeMap<String, Binding>,
    pub uses: &'a Uses,
    in_requires: bool,
}

impl<'a> Env<'a> {
    pub fn for_fn(f: &SpecFn, helpers: &'a BTreeMap<String, HelperSig>, uses: &'a Uses) -> Self {
        let names = f
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| (p.name.clone(), Binding::Arg(i, p.ty)))
            .collect();
        Env { helpers, names, uses, in_requires: false }
    }

    pub fn for_helper(
        params: &[Param],
        helpers: &'a BTreeMap<String, HelperSig>,
        uses: &'a Uses,
    ) -> Self {
        let names = params
            .iter()
            .map(|p| (p.name.clone(), Binding::HelperParam(lean_ident(&p.name), p.ty)))
            .collect();
        Env { helpers, names, uses, in_requires: false }
    }
}

/// Lean identifier for an arbitrary Rust identifier; guillemets make every
/// name valid even when it collides with a Lean keyword.
pub fn lean_ident(name: &str) -> String {
    format!("«{name}»")
}

/// Unqualified names that lowered clause text references besides
/// [`GLOBALS`]. A `let` binder named after one would capture it.
const CLAUSE_NAMES: &[&str] = &["Nat", "q", "out", "specArg", "specBool", "specInt", "specNat"];

// Every global the lowering references is qualified from one of a few root
// names (`Int`, `True`, `False`, `Trusted`, and the output namespace's root,
// `Spec` or `Specs`). Helper parameters become
// Lean binders, and a binder captures any unqualified reference with the same
// name (`pure_g`) and any qualified reference whose first component it names
// (a binder `Trusted` turns `Trusted.MirSemantics.intTdiv` into a field
// access). `lower_helper` therefore rejects exactly those root names as
// parameter names. Qualifying from `_root_` would make every reference
// capture-proof, but the `Spec.lean` policy in `TrustedBoundary.lean` rejects
// any identifier with a `_root_` component, binders included.
//
// Division and modular arithmetic use `Trusted.MirSemantics`'s own Rust
// operator helpers: `Int.tdiv`, `Int.tmod`, and `Int.emod` live in
// `Init.Data.Int.DivMod.Basic`, which the `Spec.lean` header (`prelude`
// and `import Trusted.MirSemantics`) does not load.

/// The Lean type of every lowered integer.
pub const INT: &str = "Int";
const INT_NEG: &str = "Int.neg";
const TRUE: &str = "True";
const FALSE: &str = "False";
/// The Lean type of `()` values.
pub const VAL: &str = "Trusted.MirSemantics.Val";
const VAL_UNIT: &str = "Trusted.MirSemantics.Val.unit";
/// Rust's truncating `/` (`Int.tdiv`).
const INT_TDIV: &str = "Trusted.MirSemantics.intTdiv";
/// Rust's truncating `%` (`Int.tmod`).
const INT_TMOD: &str = "Trusted.MirSemantics.intTmod";
/// Euclidean remainder (`Int.emod`), for wrapping arithmetic.
const INT_EMOD: &str = "Trusted.MirSemantics.intEmod";
/// The namespace `emit` defines everything in for `--format v1`.
pub const SPEC_NAMESPACE: &str = "Spec";
/// The root of the `Specs.<crate>.<claim>` namespaces of `--format v2-module`.
pub const SPECS_ROOT: &str = "Specs";

/// Every global name that lowered helper text references.
const GLOBALS: &[&str] = &[
    INT,
    INT_NEG,
    TRUE,
    FALSE,
    VAL,
    VAL_UNIT,
    INT_TDIV,
    INT_TMOD,
    INT_EMOD,
    SPEC_NAMESPACE,
    SPECS_ROOT,
];

/// The Lean name of `#[anneal::pure]` helper `name`, which `emit` defines
/// as `pure_<name>` in namespace `namespace`.
pub fn helper_lean_name(namespace: &str, name: &str) -> String {
    format!("{namespace}.pure_{name}")
}

/// Whether `name` cannot be a helper binder: it would capture a reference in
/// `GLOBALS`, or it is `_root_`, which the `Spec.lean` policy rejects.
fn reserved_param_name(name: &str) -> bool {
    name == "_root_" || GLOBALS.iter().any(|g| g.split('.').next() == Some(name))
}

const INTRINSICS: &[&str] = &[
    "math",
    "wrapping_add",
    "wrapping_sub",
    "wrapping_mul",
    "no_overflow_add",
    "no_overflow_sub",
    "no_overflow_mul",
];

/// `2^bits` in decimal. `u128` cannot hold `2^128`, so that case is spelled
/// out.
fn modulus(t: IntTy) -> String {
    if t.bits == 128 {
        "340282366920938463463374607431768211456".into()
    } else {
        (1u128 << t.bits).to_string()
    }
}

/// `2^(bits - 1)`, the magnitude of a signed type's minimum.
fn half_modulus(t: IntTy) -> u128 {
    1u128 << (t.bits - 1)
}

fn int_lit(v: IntLit) -> String {
    v.to_lean()
}

/// The value and type of the integer constant `t::c` on the profile v1
/// target, where `usize` and `isize` are 64 bits wide. As in Rust, `T::MIN`
/// and `T::MAX` have type `T`, and `T::BITS` has type `u32`.
fn int_const(t: IntTy, c: IntConst) -> (IntLit, IntTy) {
    let (lo, hi) = t.range();
    match c {
        IntConst::Min => (IntLit::new(lo < 0, lo.unsigned_abs()), t),
        IntConst::Max => (IntLit::new(false, hi), t),
        IntConst::Bits => (
            IntLit::new(false, u128::from(t.bits)),
            IntTy { bits: 32, signed: false, pointer_sized: false },
        ),
    }
}

fn type_error(span: Span, msg: impl Into<String>) -> Diagnostic {
    Diagnostic::new("E_ANNEAL_SPEC_TYPE_MISMATCH", span, msg)
}

fn levenshtein(a: &str, b: &str) -> usize {
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    for (i, ca) in a.chars().enumerate() {
        let mut cur = vec![i + 1];
        for (j, cb) in b.iter().enumerate() {
            cur.push((prev[j] + usize::from(ca != *cb)).min(prev[j + 1] + 1).min(cur[j] + 1));
        }
        prev = cur;
    }
    prev[b.len()]
}

fn suggest<'b>(name: &str, candidates: impl Iterator<Item = &'b String>) -> Option<String> {
    candidates
        .map(|c| (levenshtein(name, c), c))
        .filter(|(d, _)| *d <= 2)
        .min()
        .map(|(_, c)| c.clone())
}

impl<'a> Env<'a> {
    fn ident(&self, name: &str, span: Span, math: bool) -> Result<Low, Diagnostic> {
        let Some(b) = self.names.get(name) else {
            let mut d = Diagnostic::new(
                "E_ANNEAL_SPEC_UNKNOWN_IDENT",
                span,
                format!("cannot find `{name}` in this specification"),
            );
            if let Some(s) = suggest(name, self.names.keys()) {
                d = d.help(format!("a binding with a similar name exists: `{s}`"));
            } else if self.in_requires && name == "ret" {
                d = d.help("the return value is only in scope inside `ensures(|ret| ...)`");
            }
            return Err(d);
        };
        let lift = |t: Ty| if math && t.is_integer() { Ty::Math } else { t };
        let (term, ty) = match b {
            Binding::Arg(i, ty) => {
                self.uses.q.set(true);
                self.uses.arg.set(true);
                (format!("(specArg q {i})"), *ty)
            }
            Binding::Ret(ty) => {
                self.uses.out.set(true);
                ("out.ret".to_string(), *ty)
            }
            Binding::HelperParam(lean, ty) => {
                return Ok(match ty {
                    Ty::Bool => Low::Prop(Prop {
                        term: lean.clone(),
                        undecidable: Some((
                            span,
                            format!(
                                "`{name}` is a `bool` helper parameter, which lowers to a `Prop`"
                            ),
                        )),
                        on_true: Vec::new(),
                        on_false: Vec::new(),
                    }),
                    Ty::Unit => Low::Unit(lean.clone()),
                    t => Low::Int(lean.clone(), lift(*t)),
                });
            }
            Binding::Local(lean, kind) => {
                return Ok(match kind {
                    // A `bool` binding carries what its initializer
                    // establishes, and is as decidable as it.
                    LocalKind::Prop { decidable, when_true, when_false } => Low::Prop(Prop {
                        term: lean.clone(),
                        undecidable: (!decidable).then(|| {
                            (span, format!("`{name}` is bound to a `bool` that Lean cannot decide"))
                        }),
                        on_true: when_true.clone(),
                        on_false: when_false.clone(),
                    }),
                    LocalKind::Int { ty, .. } => Low::Int(lean.clone(), lift(*ty)),
                    LocalKind::Unit => Low::Unit(lean.clone()),
                    // A step count compared in a `max_steps` condition is a
                    // non-negative mathematical integer.
                    LocalKind::Nat { .. } => Low::Int(format!("({INT}.ofNat {lean})"), Ty::Math),
                });
            }
        };
        Ok(match ty {
            Ty::Bool => {
                self.uses.val_bool.set(true);
                Low::Prop(Prop::pure(format!("(specBool {term} = true)")))
            }
            Ty::Unit => Low::Unit(term),
            Ty::Int(_) | Ty::Math => {
                self.uses.val_int.set(true);
                Low::Int(format!("(specInt {term})"), lift(ty))
            }
            Ty::Never => {
                return Err(Diagnostic::new(
                    "E_ANNEAL_UNSUPPORTED_TYPE",
                    span,
                    "`-> !` functions never return normally",
                ));
            }
        })
    }

    pub fn lower_prop(&self, e: &Expr, facts: &mut Vec<String>) -> Result<String, Diagnostic> {
        self.lower_prop_in(e, false, facts).map(|p| p.term)
    }

    /// Type-checks and lowers a `max_steps` expression to a non-negative `Nat`
    /// term over entry arguments. Arithmetic in `max_steps` is mathematical
    /// (`Nat` step count, never wrapping machine width), while signed values,
    /// unary negation, and subtraction are rejected fail-closed so `Spec.lean`
    /// never silently clamps or saturates a negative bound to `0`.
    pub fn lower_nat(&self, e: &Expr, facts: &mut Vec<String>) -> Result<String, Diagnostic> {
        match &e.kind {
            ExprKind::Int(v, suffix) => {
                let lit = IntLit::new(false, *v);
                if let Some(t) = suffix {
                    check_range(lit, *t, e.span)?;
                    if t.signed {
                        return Err(type_error(
                            e.span,
                            format!(
                                "`max_steps` requires a non-negative integer, found signed `{}`",
                                t.rust_name()
                            ),
                        )
                        .help("use an unsuffixed or unsigned integer literal"));
                    }
                }
                Ok(format!("({v} : Nat)"))
            }
            ExprKind::IntConst(t, c) => {
                let (lit, ty) = int_const(*t, *c);
                if ty.signed {
                    return Err(type_error(
                        e.span,
                        format!(
                            "`max_steps` requires a non-negative integer, found signed `{}::{}`",
                            t.rust_name(),
                            c.rust_name()
                        ),
                    )
                    .help("use an unsigned integer constant or literal"));
                }
                Ok(format!("({} : Nat)", lit.mag))
            }
            ExprKind::Ident(name) => {
                let Some(b) = self.names.get(name) else {
                    let mut d = Diagnostic::new(
                        "E_ANNEAL_SPEC_UNKNOWN_IDENT",
                        e.span,
                        format!("cannot find `{name}` in this specification"),
                    );
                    if let Some(s) = suggest(name, self.names.keys()) {
                        d = d.help(format!("a binding with a similar name exists: `{s}`"));
                    } else if name == "ret" {
                        d = d.help("the return value is only in scope inside `ensures(|ret| ...)`");
                    }
                    return Err(d);
                };
                match b {
                    Binding::Arg(i, Ty::Int(t)) if !t.signed => {
                        self.uses.q.set(true);
                        self.uses.arg.set(true);
                        self.uses.val_nat.set(true);
                        Ok(format!("(specNat (specArg q {i}))"))
                    }
                    Binding::Arg(_, ty @ Ty::Int(_)) => Err(type_error(
                        e.span,
                        format!(
                            "`max_steps` requires a non-negative integer, but `{name}` has signed \
                             type `{}`",
                            ty.describe()
                        ),
                    )
                    .help("step bounds may only depend on unsigned integer parameters")),
                    Binding::Arg(_, ty) | Binding::Ret(ty) | Binding::HelperParam(_, ty) => {
                        Err(type_error(
                            e.span,
                            format!(
                                "`max_steps` expects a non-negative integer, found `{}`",
                                ty.describe()
                            ),
                        ))
                    }
                    Binding::Local(lean, LocalKind::Nat { .. }) => Ok(lean.clone()),
                    Binding::Local(_, kind) => Err(type_error(
                        e.span,
                        format!(
                            "`max_steps` expects a non-negative integer, found `{}`",
                            match kind {
                                LocalKind::Prop { .. } => "bool".to_string(),
                                LocalKind::Unit => "()".to_string(),
                                LocalKind::Int { ty, .. } => ty.describe(),
                                LocalKind::Nat { .. } => unreachable!("handled above"),
                            }
                        ),
                    )),
                }
            }
            ExprKind::Paren(inner) | ExprKind::Math(inner) => self.lower_nat(inner, facts),
            ExprKind::Let(b, body) => {
                let (env, prefix, extra) = self.bind(b, body, false, true, facts)?;
                let mut body_facts = facts.clone();
                body_facts.extend(extra);
                Ok(format!("({prefix}{})", env.lower_nat(body, &mut body_facts)?))
            }
            ExprKind::If(c, t, f) => {
                let cond = self.lower_prop_in(c, false, facts)?;
                require_decidable(&cond)?;
                let mut then_facts = facts.clone();
                then_facts.extend(cond.on_true);
                let mut else_facts = facts.clone();
                else_facts.extend(cond.on_false);
                let a = self.lower_nat(t, &mut then_facts)?;
                let b = self.lower_nat(f, &mut else_facts)?;
                Ok(format!("(if {} then {a} else {b})", cond.term))
            }
            ExprKind::Old(_) => Err(Diagnostic::new(
                "E_ANNEAL_OLD_IN_PRECONDITION",
                e.span,
                "`old(...)` is meaningless in `max_steps`, which is already evaluated in the \
                 entry state",
            )),
            ExprKind::Bool(_) => Err(type_error(
                e.span,
                "expected a non-negative integer for `max_steps`, found `bool`",
            )),
            ExprKind::Unit => Err(type_error(
                e.span,
                "expected a non-negative integer for `max_steps`, found `()`",
            )),
            ExprKind::Unary(UnOp::Neg, _) => Err(type_error(
                e.span,
                "unary `-` is not allowed in `max_steps`: step bounds must be non-negative",
            )),
            ExprKind::Unary(UnOp::Not, _) => {
                let _ = self.lower(e, false, facts)?;
                Err(type_error(
                    e.span,
                    "expected a non-negative integer for `max_steps`, found `bool`",
                ))
            }
            ExprKind::Binary(op, l, r) => match op {
                BinOp::Add | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                    let a = self.lower_nat(l, facts)?;
                    let b = self.lower_nat(r, facts)?;
                    if matches!(op, BinOp::Div | BinOp::Rem) {
                        let guarded = self.const_value(r).is_some_and(|v| !v.neg && v.mag != 0)
                            || {
                                let mut scratch = Vec::new();
                                matches!(
                                    self.lower(r, true, &mut scratch),
                                    Ok(Low::Int(t, _)) if facts.contains(&t)
                                )
                            };
                        if !guarded {
                            return Err(Diagnostic::new(
                                "E_ANNEAL_UNGUARDED_SPEC_DIV",
                                r.span,
                                format!("the divisor of `{}` may be zero", op.rust()),
                            )
                            .help("guard it in `requires`, e.g. `requires(d != 0usize)`"));
                        }
                    }
                    Ok(match op {
                        BinOp::Add => format!("({a} + {b})"),
                        BinOp::Mul => format!("({a} * {b})"),
                        BinOp::Div => format!("(Nat.div {a} {b})"),
                        _ => format!("(Nat.mod {a} {b})"),
                    })
                }
                BinOp::Sub => {
                    let _ = self.lower_nat(l, facts)?;
                    let _ = self.lower_nat(r, facts)?;
                    Err(type_error(
                        e.span,
                        "subtraction `-` is not allowed in `max_steps`: step bounds must be \
                         syntactically non-negative",
                    )
                    .help("rewrite the bound using `+`, `*`, `/`, and `%` over non-negative terms"))
                }
                BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                    let _ = self.binary(*op, l, r, e.span, true, facts)?;
                    unreachable!("bitwise operators are rejected above")
                }
                _ => {
                    let _ = self.binary(*op, l, r, e.span, false, facts)?;
                    Err(type_error(
                        e.span,
                        "expected a non-negative integer for `max_steps`, found `bool`",
                    ))
                }
            },
            ExprKind::Call(name, args) => match self.call(name, args, e.span, false, facts)? {
                Low::Int(term, Ty::Int(t)) if !t.signed => Ok(format!("(Int.toNat {term})")),
                Low::Int(_, Ty::Int(t)) => Err(type_error(
                    e.span,
                    format!(
                        "`max_steps` requires a non-negative integer, but `{name}` returns signed \
                         `{}`",
                        t.rust_name()
                    ),
                )),
                other => Err(type_error(
                    e.span,
                    format!(
                        "`max_steps` expects a non-negative integer, found {}",
                        describe(&other)
                    ),
                )),
            },
        }
    }

    fn lower(&self, e: &Expr, math: bool, facts: &mut Vec<String>) -> Result<Low, Diagnostic> {
        match &e.kind {
            ExprKind::Bool(b) => Ok(Low::Prop(Prop::pure(if *b { TRUE } else { FALSE }))),
            ExprKind::Unit => Ok(Low::Unit(VAL_UNIT.into())),
            ExprKind::Int(v, suffix) => {
                let lit = IntLit::new(false, *v);
                match suffix {
                    Some(t) => {
                        check_range(lit, *t, e.span)?;
                        Ok(Low::Int(int_lit(lit), if math { Ty::Math } else { Ty::Int(*t) }))
                    }
                    None => Ok(Low::Lit(lit, e.span)),
                }
            }
            ExprKind::IntConst(t, c) => {
                let (lit, ty) = int_const(*t, *c);
                Ok(Low::Int(int_lit(lit), if math { Ty::Math } else { Ty::Int(ty) }))
            }
            ExprKind::Ident(name) => self.ident(name, e.span, math),
            ExprKind::Paren(inner) => self.lower(inner, math, facts),
            ExprKind::Math(inner) => {
                let low = self.lower(inner, true, facts)?;
                Ok(match low {
                    Low::Lit(v, _) => Low::Int(int_lit(v), Ty::Math),
                    Low::Int(t, _) | Low::UntypedIf(t, _) => Low::Int(t, Ty::Math),
                    other => other,
                })
            }
            ExprKind::Old(_) => Err(if self.in_requires {
                Diagnostic::new(
                    "E_ANNEAL_OLD_IN_PRECONDITION",
                    e.span,
                    "`old(...)` is meaningless in a precondition, which is already evaluated \
                     in the entry state",
                )
            } else {
                Diagnostic::new(
                    "E_ANNEAL_UNSUPPORTED_OLD",
                    e.span,
                    "`old(...)` is not supported by the profile v1 lowering",
                )
                .help("profile v1 parameters are passed by value, so `old(x)` would equal `x`")
            }),
            ExprKind::Unary(UnOp::Not, inner) => match self.lower(inner, math, facts)? {
                Low::Prop(p) => Ok(Low::Prop(Prop {
                    term: format!("(¬ {})", p.term),
                    undecidable: p.undecidable,
                    on_true: p.on_false,
                    on_false: p.on_true,
                })),
                other => Err(type_error(
                    inner.span,
                    format!("`!` expects `bool`, found {}", describe(&other)),
                )
                .help("bitwise negation of integers is not supported in profile v1")),
            },
            ExprKind::Unary(UnOp::Neg, inner) => {
                if let ExprKind::Int(mag, Some(t)) = inner.kind {
                    if !t.signed {
                        return Err(if math {
                            type_error(
                                e.span,
                                format!("cannot apply unary `-` to unsigned `{}`", t.rust_name()),
                            )
                        } else {
                            ambiguous_arith(e.span, "-", Ty::Int(t))
                        });
                    }
                    let lit = IntLit::new(true, mag);
                    check_range(lit, t, e.span)?;
                    return Ok(Low::Int(int_lit(lit), if math { Ty::Math } else { Ty::Int(t) }));
                }
                let low = self.lower(inner, math, facts)?;
                match low {
                    Low::Lit(v, s) => Ok(Low::Lit(v.negate(), s)),
                    Low::UntypedIf(t, leaves) => Ok(Low::UntypedIf(
                        format!("({INT_NEG} {t})"),
                        leaves.into_iter().map(|(v, s)| (v.negate(), s)).collect(),
                    )),
                    Low::Int(t, Ty::Math) => Ok(Low::Int(format!("({INT_NEG} {t})"), Ty::Math)),
                    Low::Int(_, ty) => Err(ambiguous_arith(e.span, "-", ty)),
                    other => Err(type_error(
                        inner.span,
                        format!("`-` expects an integer, found {}", describe(&other)),
                    )),
                }
            }
            ExprKind::Binary(op, l, r) => self.binary(*op, l, r, e.span, math, facts),
            ExprKind::Call(name, args) => self.call(name, args, e.span, math, facts),
            ExprKind::If(c, t, f) => self.lower_if(c, t, f, math, facts),
            ExprKind::Let(b, body) => {
                let (env, prefix, extra) = self.bind(b, body, math, false, facts)?;
                let mut body_facts = facts.clone();
                body_facts.extend(extra);
                Ok(match env.lower(body, math, &mut body_facts)? {
                    // A fact that names the block's own binding does not
                    // leave the block, where the binding is out of scope.
                    Low::Prop(p) => {
                        let lean = lean_ident(&b.name);
                        let outside = |fs: Vec<String>| -> Vec<String> {
                            fs.into_iter().filter(|f| !f.contains(&lean)).collect()
                        };
                        Low::Prop(Prop {
                            term: format!("({prefix}{})", p.term),
                            undecidable: p.undecidable,
                            on_true: outside(p.on_true),
                            on_false: outside(p.on_false),
                        })
                    }
                    Low::Int(t, ty) => Low::Int(format!("({prefix}{t})"), ty),
                    Low::Unit(u) => Low::Unit(format!("({prefix}{u})")),
                    untyped @ (Low::Lit(..) | Low::UntypedIf(..)) => {
                        let (t, leaves) = untyped_parts(untyped);
                        Low::UntypedIf(format!("({prefix}{t})"), leaves)
                    }
                })
            }
        }
    }

    /// This environment with `name` bound to `binding`.
    fn with(&self, name: &str, binding: Binding) -> Env<'a> {
        let mut names = self.names.clone();
        names.insert(name.to_string(), binding);
        Env { helpers: self.helpers, names, uses: self.uses, in_requires: self.in_requires }
    }

    /// This environment recording uses in `uses`, for lowering an
    /// expression only to learn its type without affecting what the
    /// generated Lean declares.
    fn probe<'b>(&'b self, uses: &'b Uses) -> Env<'b> {
        Env {
            helpers: self.helpers,
            names: self.names.clone(),
            uses,
            in_requires: self.in_requires,
        }
    }

    /// The value of `e` if it is an integer literal or constant, or a `let`
    /// binding of one.
    fn const_value(&self, e: &Expr) -> Option<IntLit> {
        match &e.kind {
            ExprKind::Ident(name) => match self.names.get(name) {
                Some(Binding::Local(
                    _,
                    LocalKind::Int { value, .. } | LocalKind::Nat { value },
                )) => *value,
                _ => None,
            },
            ExprKind::Paren(inner) | ExprKind::Math(inner) => self.const_value(inner),
            _ => const_int_lit(e),
        }
    }

    /// Checks and lowers `let` binding `b`, whose block continues with
    /// `body`. Returns the environment of the rest of the block, the Lean
    /// `let .. := ..; ` prefix that binds `b`, and the nonzero facts that the
    /// binding adds there. In `max_steps` (`nat`), an integer binding is a
    /// `Nat` step count.
    fn bind(
        &self,
        b: &LetBinding,
        body: &Expr,
        math: bool,
        nat: bool,
        facts: &mut Vec<String>,
    ) -> Result<(Env<'a>, String, Vec<String>), Diagnostic> {
        let name = b.name.as_str();
        let intrinsic = INTRINSICS.contains(&name)
            || name == "old"
            || name.starts_with("wrapping_")
            || name.starts_with("no_overflow_");
        if reserved_param_name(name) || CLAUSE_NAMES.contains(&name) || intrinsic {
            return Err(Diagnostic::new(
                "E_ANNEAL_RESERVED_PARAM_NAME",
                b.name_span,
                format!(
                    "`{name}` cannot name a `let` binding: it is reserved by the generated Lean \
                     or names an intrinsic"
                ),
            )
            .help("rename the binding"));
        }
        let shadowed = match self.names.get(name) {
            Some(Binding::Arg(..) | Binding::HelperParam(..)) => Some("a parameter"),
            Some(Binding::Ret(_)) => Some("the `ensures` return binder"),
            Some(Binding::Local(..)) => Some("an enclosing `let` binding"),
            None if self.helpers.contains_key(name) => Some("a `#[anneal::pure]` helper"),
            None => None,
        };
        if let Some(what) = shadowed {
            return Err(Diagnostic::new(
                "E_ANNEAL_SPEC_SHADOWING",
                b.name_span,
                format!("the `let` binding `{name}` shadows {what}"),
            )
            .help("choose a name that is not already in scope"));
        }
        let init = &b.init;
        let lean = lean_ident(name);
        let mismatch = |found: &Low, want: Ty| {
            type_error(
                init.span,
                format!(
                    "`{name}` is declared `{}`, but its initializer has {}",
                    want.describe(),
                    describe(found)
                ),
            )
        };
        // The kind of an unannotated `max_steps` binding: a `bool` or `()`
        // as anywhere else, and otherwise a step count.
        let nat_kind = |env: &Self| {
            let scratch = Uses::default();
            match env.probe(&scratch).lower(init, true, &mut facts.clone()) {
                Ok(Low::Prop(_)) => Some(Ty::Bool),
                Ok(Low::Unit(_)) => Some(Ty::Unit),
                _ => None,
            }
        };
        let ty = match b.ty {
            Some(Ty::Int(t)) if nat && t.signed => {
                return Err(type_error(
                    b.name_span,
                    format!(
                        "`max_steps` requires non-negative integers, but `{name}` is declared \
                         signed `{}`",
                        t.rust_name()
                    ),
                ));
            }
            Some(ty) => Some(ty),
            None if nat => nat_kind(self),
            None => None,
        };
        let (term, kind, lean_ty) = match ty {
            Some(Ty::Bool) => {
                let p = self.lower_prop_in(init, math, facts)?;
                let kind = prop_local(&p);
                (p.term, kind, "Prop".to_string())
            }
            Some(Ty::Unit) => match self.lower(init, math, facts)? {
                Low::Unit(u) => (u, LocalKind::Unit, VAL.to_string()),
                other => return Err(mismatch(&other, Ty::Unit)),
            },
            Some(Ty::Int(t)) if nat => {
                let value = self.const_value(init);
                if let Some(v) = value {
                    check_range(v, t, init.span)?;
                }
                // Step arithmetic is mathematical, but a machine-typed value
                // must have the declared type.
                let scratch = Uses::default();
                if let Ok(found @ Low::Int(_, Ty::Int(found_t))) =
                    self.probe(&scratch).lower(init, false, &mut facts.clone())
                {
                    if found_t != t {
                        return Err(mismatch(&found, Ty::Int(t)));
                    }
                }
                (self.lower_nat(init, facts)?, LocalKind::Nat { value }, "Nat".to_string())
            }
            None if nat => {
                let value = self.const_value(init);
                (self.lower_nat(init, facts)?, LocalKind::Nat { value }, "Nat".to_string())
            }
            // An annotated integer binding has that machine type, so its
            // initializer is a machine-typed expression even inside `math`.
            Some(Ty::Int(t)) => match settle(self.lower(init, false, facts)?, Ty::Int(t))? {
                Low::Int(term, ty) if ty == Ty::Int(t) => {
                    (term, LocalKind::Int { ty, value: self.const_value(init) }, INT.to_string())
                }
                other => return Err(mismatch(&other, Ty::Int(t))),
            },
            None => match self.lower(init, math, facts)? {
                Low::Prop(p) => {
                    let kind = prop_local(&p);
                    (p.term, kind, "Prop".to_string())
                }
                Low::Unit(u) => (u, LocalKind::Unit, VAL.to_string()),
                Low::Int(term, ty) => {
                    (term, LocalKind::Int { ty, value: self.const_value(init) }, INT.to_string())
                }
                untyped @ (Low::Lit(..) | Low::UntypedIf(..)) if math => {
                    let Low::Int(term, ty) = settle(untyped, Ty::Math)? else { unreachable!() };
                    (term, LocalKind::Int { ty, value: self.const_value(init) }, INT.to_string())
                }
                Low::Lit(..) | Low::UntypedIf(..) => {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED",
                        init.span,
                        format!("the type of `{name}` cannot be inferred from an untyped integer"),
                    )
                    .help(format!(
                        "annotate it, as in `let {name}: u64 = ..;`, or bind a `math(..)` value"
                    )));
                }
            },
            Some(Ty::Math | Ty::Never) => unreachable!("not a `let` annotation"),
        };
        // A name bound to a nonzero value may divide the rest of its block.
        let mut extra = Vec::new();
        if let LocalKind::Int { value, .. } | LocalKind::Nat { value } = &kind {
            let scratch = Uses::default();
            let nonzero = value.is_some_and(|v| v.mag != 0)
                || matches!(
                    self.probe(&scratch).lower(init, true, &mut facts.clone()),
                    Ok(Low::Int(t, _)) if facts.contains(&t)
                );
            if nonzero {
                extra.push(match kind {
                    LocalKind::Nat { .. } => format!("({INT}.ofNat {lean})"),
                    _ => lean.clone(),
                });
            }
        }
        // Lean warns about an unused binder, and an unused binding is likely
        // a mistake.
        if !mentions(body, name) {
            return Err(Diagnostic::new(
                "E_ANNEAL_UNUSED_LET",
                b.name_span,
                format!("the `let` binding `{name}` is never used"),
            )
            .help("remove the binding, or use its value in the rest of the block"));
        }
        let prefix = format!("let {lean} : {lean_ty} := {term}; ");
        Ok((self.with(name, Binding::Local(lean, kind)), prefix, extra))
    }

    /// Lowers `if c { t } else { f }`. A `bool`-valued `if` lowers to
    /// `((c → t) ∧ (¬ c → f))`, which needs no `Decidable` instance for `c`.
    /// An `if` that chooses an integer or `()` value lowers to Lean's
    /// `if c then t else f`, so `c` must be decidable (see
    /// [`require_decidable`]). Each branch may rely on the nonzero facts
    /// that the condition establishes on its side.
    fn lower_if(
        &self,
        c: &Expr,
        t: &Expr,
        f: &Expr,
        math: bool,
        facts: &mut Vec<String>,
    ) -> Result<Low, Diagnostic> {
        let cond = self.lower_prop_in(c, math, facts)?;
        let undecidable = cond.undecidable;
        let mut then_facts = facts.clone();
        then_facts.extend(cond.on_true);
        let mut else_facts = facts.clone();
        else_facts.extend(cond.on_false);
        let a = self.lower(t, math, &mut then_facts)?;
        let b = self.lower(f, math, &mut else_facts)?;
        let cond_term = cond.term.as_str();
        let ite = |x: &str, y: &str| format!("(if {cond_term} then {x} else {y})");
        let (a, b) = match (a, b) {
            (Low::Prop(x), Low::Prop(y)) => {
                return Ok(Low::Prop(Prop {
                    term: format!("(({cond_term} → {}) ∧ (¬ {cond_term} → {}))", x.term, y.term),
                    undecidable: undecidable.or(x.undecidable).or(y.undecidable),
                    on_true: Vec::new(),
                    on_false: Vec::new(),
                }));
            }
            (x, y) if is_untyped(&x) && is_untyped(&y) => {
                require_decidable_reason(undecidable.as_ref())?;
                let (xt, mut leaves) = untyped_parts(x);
                let (yt, more) = untyped_parts(y);
                leaves.extend(more);
                return Ok(if math {
                    Low::Int(ite(&xt, &yt), Ty::Math)
                } else {
                    Low::UntypedIf(ite(&xt, &yt), leaves)
                });
            }
            (x, Low::Int(yt, ty)) if is_untyped(&x) => (settle(x, ty)?, Low::Int(yt, ty)),
            (Low::Int(xt, ty), y) if is_untyped(&y) => (Low::Int(xt, ty), settle(y, ty)?),
            pair => pair,
        };
        match (a, b) {
            (Low::Int(x, tx), Low::Int(y, ty)) => {
                if tx != ty {
                    return Err(type_error(
                        f.span,
                        format!(
                            "`if` and `else` have mismatched types `{}` and `{}`",
                            tx.describe(),
                            ty.describe()
                        ),
                    )
                    .help("give both branches one type, e.g. by wrapping both in `math(..)`"));
                }
                require_decidable_reason(undecidable.as_ref())?;
                Ok(Low::Int(ite(&x, &y), tx))
            }
            (Low::Unit(x), Low::Unit(y)) => {
                require_decidable_reason(undecidable.as_ref())?;
                Ok(Low::Unit(ite(&x, &y)))
            }
            (a, b) => Err(type_error(
                f.span,
                format!(
                    "`if` and `else` have incompatible types: {} and {}",
                    describe(&a),
                    describe(&b)
                ),
            )),
        }
    }

    fn binary(
        &self,
        op: BinOp,
        l: &Expr,
        r: &Expr,
        span: Span,
        math: bool,
        facts: &mut Vec<String>,
    ) -> Result<Low, Diagnostic> {
        match op {
            BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Iff => {
                let a = self.lower_prop_in(l, math, facts)?;
                // `a && b` and `a ==> b` evaluate `b` only when `a` holds, so
                // `a`'s nonzero facts may guard divisions in `b`.
                let mark = facts.len();
                if matches!(op, BinOp::And | BinOp::Implies) {
                    facts.extend(a.on_true.iter().cloned());
                }
                let b = self.lower_prop_in(r, math, facts);
                facts.truncate(mark);
                let b = b?;
                let sym = match op {
                    BinOp::And => "∧",
                    BinOp::Or => "∨",
                    BinOp::Implies => "→",
                    _ => "↔",
                };
                let (on_true, on_false) = match op {
                    BinOp::And => {
                        let mut on_true = a.on_true;
                        on_true.extend(b.on_true);
                        (on_true, Vec::new())
                    }
                    BinOp::Or => {
                        let mut on_false = a.on_false;
                        on_false.extend(b.on_false);
                        (Vec::new(), on_false)
                    }
                    _ => (Vec::new(), Vec::new()),
                };
                Ok(Low::Prop(Prop {
                    term: format!("({} {sym} {})", a.term, b.term),
                    undecidable: a.undecidable.or(b.undecidable),
                    on_true,
                    on_false,
                }))
            }
            _ if op.is_comparison() => {
                let (a, b) = self.lower_pair(l, r, math, facts)?;
                self.compare(op, l, r, a, b, span)
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                let a = self.lower(l, math, facts)?;
                if matches!(a, Low::Prop(_)) {
                    let d = match op {
                        BinOp::BitAnd => Diagnostic::new(
                            "E_ANNEAL_EAGER_CLAUSE_JOIN",
                            span,
                            "`&` evaluates both operands eagerly",
                        )
                        .help(
                            "use `&&` so the right operand is only evaluated when the left holds",
                        ),
                        BinOp::BitOr => Diagnostic::new(
                            "E_ANNEAL_EAGER_CLAUSE_JOIN",
                            span,
                            "`|` evaluates both operands eagerly",
                        )
                        .help("use `||`"),
                        _ => Diagnostic::new(
                            "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
                            span,
                            "`^` on `bool` is not supported",
                        )
                        .help("use `!=`"),
                    };
                    return Err(d);
                }
                Err(unsupported_bitwise(op, span))
            }
            BinOp::Shl | BinOp::Shr => Err(unsupported_bitwise(op, span)),
            _ => {
                let (a, b) = self.lower_pair(l, r, math, facts)?;
                // Arithmetic is unambiguous only when no operand is a machine
                // integer: inside `math`, every integer is already lifted, and
                // outside it the operands must be lifted with `math(..)`.
                let machine = [&a, &b].into_iter().find_map(|x| match x {
                    Low::Int(_, t @ Ty::Int(_)) => Some(*t),
                    _ => None,
                });
                if let Some(ty) = machine {
                    return Err(ambiguous_arith(span, op.rust(), ty));
                }
                let a = int_term(a, l.span, op)?;
                let b = int_term(b, r.span, op)?;
                if matches!(op, BinOp::Div | BinOp::Rem) {
                    let nonzero_lit = self.const_value(r).is_some_and(|v| v.mag != 0);
                    if !nonzero_lit && !facts.contains(&b) {
                        return Err(Diagnostic::new(
                            "E_ANNEAL_UNGUARDED_SPEC_DIV",
                            r.span,
                            format!("the divisor of `{}` may be zero", op.rust()),
                        )
                        .help("guard it, e.g. `d != 0 ==> math(a / d) == ...`"));
                    }
                }
                let term = match op {
                    BinOp::Add => format!("({a} + {b})"),
                    BinOp::Sub => format!("({a} - {b})"),
                    BinOp::Mul => format!("({a} * {b})"),
                    BinOp::Div => format!("({INT_TDIV} {a} {b})"),
                    _ => format!("({INT_TMOD} {a} {b})"),
                };
                Ok(Low::Int(term, Ty::Math))
            }
        }
    }

    fn lower_prop_in(
        &self,
        e: &Expr,
        math: bool,
        facts: &mut Vec<String>,
    ) -> Result<Prop, Diagnostic> {
        match self.lower(e, math, facts)? {
            Low::Prop(p) => Ok(p),
            other => {
                Err(type_error(e.span, format!("expected `bool`, found {}", describe(&other))))
            }
        }
    }

    /// Lowers two operands whose types must agree, letting an untyped
    /// literal take its type from the other side.
    fn lower_pair(
        &self,
        l: &Expr,
        r: &Expr,
        math: bool,
        facts: &mut Vec<String>,
    ) -> Result<(Low, Low), Diagnostic> {
        let a = self.lower(l, math, facts)?;
        let b = self.lower(r, math, facts)?;
        let (a, b) = match (a, b) {
            (x, Low::Int(t, ty)) if is_untyped(&x) => (settle(x, ty)?, Low::Int(t, ty)),
            (Low::Int(t, ty), y) if is_untyped(&y) => (Low::Int(t, ty), settle(y, ty)?),
            (x, y) if math && is_untyped(&x) && is_untyped(&y) => {
                (settle(x, Ty::Math)?, settle(y, Ty::Math)?)
            }
            (x, y) if is_untyped(&x) && is_untyped(&y) => {
                let s = if let Low::Lit(_, s) = x { s } else { l.span };
                return Err(Diagnostic::new(
                    "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED",
                    s,
                    "the type of this integer literal cannot be inferred",
                )
                .help("add a suffix such as `5usize`, or use `math(...)`"));
            }
            pair => pair,
        };
        if let (Low::Int(_, ta), Low::Int(_, tb)) = (&a, &b) {
            if let (Ty::Int(x), Ty::Int(y)) = (ta, tb) {
                if x != y {
                    return Err(type_error(
                        r.span,
                        format!(
                            "mismatched integer types `{}` and `{}`",
                            ta.describe(),
                            tb.describe()
                        ),
                    )
                    .help("compare the mathematical values with `math(a) == math(b)`"));
                }
            }
        }
        Ok((a, b))
    }

    fn compare(
        &self,
        op: BinOp,
        l: &Expr,
        r: &Expr,
        a: Low,
        b: Low,
        span: Span,
    ) -> Result<Low, Diagnostic> {
        let sym = match op {
            BinOp::Eq => "=",
            BinOp::Ne => "≠",
            BinOp::Lt => "<",
            BinOp::Le => "≤",
            BinOp::Gt => ">",
            _ => "≥",
        };
        let zero = |x: &Expr| self.const_value(x).is_some_and(|v| v.mag == 0);
        match (a, b) {
            (Low::Prop(x), Low::Prop(y)) => match op {
                BinOp::Eq | BinOp::Ne => Ok(Low::Prop(Prop {
                    term: if matches!(op, BinOp::Eq) {
                        format!("({} ↔ {})", x.term, y.term)
                    } else {
                        format!("(¬ ({} ↔ {}))", x.term, y.term)
                    },
                    undecidable: x.undecidable.or(y.undecidable),
                    on_true: Vec::new(),
                    on_false: Vec::new(),
                })),
                _ => Err(type_error(span, "ordering comparisons on `bool` are not supported")),
            },
            (Low::Unit(x), Low::Unit(y)) if matches!(op, BinOp::Eq | BinOp::Ne) => {
                Ok(Low::Prop(Prop {
                    term: format!("({x} {sym} {y})"),
                    undecidable: Some((span, "`()` values have no decidable equality".into())),
                    on_true: Vec::new(),
                    on_false: Vec::new(),
                }))
            }
            (Low::Int(x, _), Low::Int(y, _)) => {
                let mut on_true = Vec::new();
                let mut on_false = Vec::new();
                match op {
                    BinOp::Ne if zero(r) => on_true.push(x.clone()),
                    BinOp::Ne if zero(l) => on_true.push(y.clone()),
                    BinOp::Gt if zero(r) => on_true.push(x.clone()),
                    BinOp::Lt if zero(l) => on_true.push(y.clone()),
                    BinOp::Eq if zero(r) => on_false.push(x.clone()),
                    BinOp::Eq if zero(l) => on_false.push(y.clone()),
                    BinOp::Le if zero(r) => on_false.push(x.clone()),
                    BinOp::Ge if zero(l) => on_false.push(y.clone()),
                    _ => {}
                }
                Ok(Low::Prop(Prop {
                    term: format!("({x} {sym} {y})"),
                    undecidable: None,
                    on_true,
                    on_false,
                }))
            }
            (a, b) => Err(type_error(
                span,
                format!("cannot compare {} with {}", describe(&a), describe(&b)),
            )),
        }
    }

    fn call(
        &self,
        name: &str,
        args: &[Expr],
        span: Span,
        math: bool,
        facts: &mut Vec<String>,
    ) -> Result<Low, Diagnostic> {
        let arity = |n: usize| {
            if args.len() == n {
                Ok(())
            } else {
                Err(Diagnostic::new(
                    "E_ANNEAL_SPEC_ARITY",
                    span,
                    format!("`{name}` takes {n} argument(s), but {} were given", args.len()),
                ))
            }
        };
        if let Some(kind) =
            name.strip_prefix("wrapping_").or_else(|| name.strip_prefix("no_overflow_"))
        {
            let sym = match kind {
                "add" => "+",
                "sub" => "-",
                "mul" => "*",
                _ => return Err(unknown_fn(name, span, self.helpers)),
            };
            arity(2)?;
            // Wrapping and overflow intrinsics take machine-typed operands even
            // inside `math`, since their meaning depends on the type's width.
            let (a, b) = self.lower_pair(&args[0], &args[1], false, facts)?;
            let t = match (&a, &b) {
                (Low::Int(_, Ty::Int(t)), Low::Int(_, Ty::Int(_))) => *t,
                _ => {
                    return Err(type_error(
                        span,
                        format!("`{name}` needs two operands of one fixed-width integer type"),
                    ))
                }
            };
            let (Low::Int(a, _), Low::Int(b, _)) = (a, b) else { unreachable!() };
            let sum = format!("{a} {sym} {b}");
            let m = modulus(t);
            let h = half_modulus(t);
            if name.starts_with("wrapping_") {
                let term = if t.signed {
                    format!("({INT_EMOD} ({sum} + {h}) {m} - {h})")
                } else {
                    format!("({INT_EMOD} ({sum}) {m})")
                };
                return Ok(Low::Int(term, if math { Ty::Math } else { Ty::Int(t) }));
            }
            let (lo, hi) = if t.signed {
                (format!("({INT_NEG} {h})"), h.to_string())
            } else {
                (format!("(0 : {INT})"), m)
            };
            return Ok(Low::Prop(Prop::pure(format!("({lo} ≤ {sum} ∧ {sum} < {hi})"))));
        }
        let Some(sig) = self.helpers.get(name) else {
            return Err(unknown_fn(name, span, self.helpers));
        };
        arity(sig.params.len())?;
        let mut lowered = Vec::new();
        for (arg, pty) in args.iter().zip(&sig.params) {
            let mut low = self.lower(arg, false, facts)?;
            if let (Low::UntypedIf(..), Ty::Int(_)) = (&low, pty) {
                low = settle(low, *pty)?;
            }
            let term = match (low, pty) {
                (Low::Prop(p), Ty::Bool) => p.term,
                (Low::Int(t, Ty::Int(a)), Ty::Int(b)) if a == *b => t,
                (Low::Lit(v, s), Ty::Int(b)) => {
                    check_range(v, *b, s)?;
                    int_lit(v)
                }
                (low, pty) => {
                    return Err(type_error(
                        arg.span,
                        format!("expected `{}`, found {}", pty.describe(), describe(&low)),
                    ))
                }
            };
            lowered.push(term);
        }
        let app = if lowered.is_empty() {
            sig.lean_name.clone()
        } else {
            format!("({} {})", sig.lean_name, lowered.join(" "))
        };
        Ok(match sig.ret {
            Ty::Bool => Low::Prop(Prop {
                term: app,
                undecidable: Some((
                    span,
                    format!("`{name}` is a `bool` helper, which lowers to a `Prop`"),
                )),
                on_true: Vec::new(),
                on_false: Vec::new(),
            }),
            Ty::Unit => Low::Unit(app),
            t => Low::Int(app, if math { Ty::Math } else { t }),
        })
    }
}

/// The `LocalKind` of a `bool` binding whose initializer lowered to `p`.
fn prop_local(p: &Prop) -> LocalKind {
    LocalKind::Prop {
        decidable: p.undecidable.is_none(),
        when_true: p.on_true.clone(),
        when_false: p.on_false.clone(),
    }
}

/// Rejects an `if` condition whose lowered proposition has no Lean
/// `Decidable` instance (arbitrary `Prop` from `bool` helpers, or `()`
/// equality).
fn require_decidable(cond: &Prop) -> Result<(), Diagnostic> {
    require_decidable_reason(cond.undecidable.as_ref())
}

fn require_decidable_reason(undecidable: Option<&(Span, String)>) -> Result<(), Diagnostic> {
    match undecidable {
        None => Ok(()),
        Some((span, why)) => Err(Diagnostic::new(
            "E_ANNEAL_UNDECIDABLE_SPEC_IF",
            *span,
            format!("an `if` that chooses a value needs a decidable condition, but {why}"),
        )
        .help(
            "choose between `bool` facts instead, as in `if c { ret == a } else { ret == b }`, \
             or test integer values in the condition",
        )),
    }
}

fn unknown_fn(name: &str, span: Span, helpers: &BTreeMap<String, HelperSig>) -> Diagnostic {
    let known: Vec<String> =
        helpers.keys().cloned().chain(INTRINSICS.iter().map(|s| s.to_string())).collect();
    let mut d = Diagnostic::new(
        "E_ANNEAL_SPEC_UNKNOWN_FN",
        span,
        format!("`{name}` is neither a `#[anneal::pure]` helper nor a built-in intrinsic"),
    );
    if let Some(s) = suggest(name, known.iter()) {
        d = d.help(format!("did you mean `{s}`?"));
    }
    d
}

fn ambiguous_arith(span: Span, op: &str, ty: Ty) -> Diagnostic {
    Diagnostic::new(
        "E_ANNEAL_AMBIGUOUS_SPEC_ARITH",
        span,
        format!(
            "`{op}` on `{}` is ambiguous: Rust arithmetic wraps or panics, but a specification \
             may mean the mathematical result",
            ty.describe()
        ),
    )
    .help(
        "write `math(a) + math(b)` (or `math { ... }`) for unbounded arithmetic, or \
           `wrapping_add(a, b)` / `no_overflow_add(a, b)` for machine arithmetic",
    )
}

fn unsupported_bitwise(op: BinOp, span: Span) -> Diagnostic {
    Diagnostic::new(
        "E_ANNEAL_UNSUPPORTED_BITWISE",
        span,
        format!("integer `{}` is not supported by the profile v1 lowering", op.rust()),
    )
}

fn describe(l: &Low) -> String {
    match l {
        Low::Prop(_) => "`bool`".into(),
        Low::Int(_, t) => format!("`{}`", t.describe()),
        Low::Unit(_) => "`()`".into(),
        Low::Lit(..) => "an integer literal".into(),
        Low::UntypedIf(..) => "an `if` of integer literals".into(),
    }
}

fn is_untyped(l: &Low) -> bool {
    matches!(l, Low::Lit(..) | Low::UntypedIf(..))
}

/// The term and the literal leaves of an untyped integer.
fn untyped_parts(l: Low) -> (String, Vec<(IntLit, Span)>) {
    match l {
        Low::Lit(v, s) => (int_lit(v), vec![(v, s)]),
        Low::UntypedIf(t, leaves) => (t, leaves),
        other => unreachable!("not an untyped integer: {other:?}"),
    }
}

/// Gives an untyped integer the type `ty`, range-checking its literals.
/// Every other lowered value is returned unchanged.
fn settle(l: Low, ty: Ty) -> Result<Low, Diagnostic> {
    match l {
        Low::Lit(v, s) => lit_at(v, s, ty),
        Low::UntypedIf(t, leaves) => {
            if let Ty::Int(it) = ty {
                for (v, s) in leaves {
                    check_range(v, it, s)?;
                }
            }
            Ok(Low::Int(t, ty))
        }
        other => Ok(other),
    }
}

fn check_range(v: IntLit, t: IntTy, span: Span) -> Result<(), Diagnostic> {
    if v.in_range(t) {
        Ok(())
    } else {
        Err(Diagnostic::new(
            "E_ANNEAL_SPEC_LITERAL_RANGE",
            span,
            format!("literal `{v}` is out of range for `{}`", t.rust_name()),
        ))
    }
}

fn lit_at(v: IntLit, span: Span, ty: Ty) -> Result<Low, Diagnostic> {
    if let Ty::Int(t) = ty {
        check_range(v, t, span)?;
    }
    Ok(Low::Int(int_lit(v), ty))
}

fn int_term(l: Low, span: Span, op: BinOp) -> Result<String, Diagnostic> {
    match l {
        Low::Int(t, _) => Ok(t),
        Low::Lit(v, _) => Ok(int_lit(v)),
        other => Err(type_error(
            span,
            format!("`{}` expects integers, found {}", op.rust(), describe(&other)),
        )),
    }
}

/// Returns the constant integer value of `e` when `e` is a literal or
/// associated integer constant (possibly parenthesized or wrapped in `math`).
fn const_int_lit(e: &Expr) -> Option<IntLit> {
    match &e.kind {
        ExprKind::Int(v, _) => Some(IntLit::new(false, *v)),
        ExprKind::IntConst(t, c) => Some(int_const(*t, *c).0),
        ExprKind::Paren(inner) | ExprKind::Math(inner) => const_int_lit(inner),
        _ => None,
    }
}

/// The lowered pieces of one specified function.
pub struct LoweredFn {
    pub behavior_pre: Option<String>,
    pub safety_pre: Option<String>,
    pub post: Option<String>,
    pub max_steps: Option<String>,
    pub uses_pre_q: bool,
    pub uses_safety_q: bool,
    pub uses_post_q: bool,
    pub uses_post_out: bool,
    pub uses_max_steps_q: bool,
    pub terminates: bool,
    pub no_unwind: bool,
}

fn conj(parts: &[String]) -> Option<String> {
    match parts {
        [] => None,
        [one] => Some(one.clone()),
        many => Some(format!("({})", many.join(" ∧ "))),
    }
}

/// Layer-2 surface default for `EffectMask.terminates`: total normal return
/// by default, with `may_diverge` as explicit opt-out.
pub const DEFAULT_TERMINATES: bool = true;

/// Layer-2 surface default for `EffectMask.noUnwind`: normal return (no
/// unwinding) by default, with `may_unwind` / `may_panic` as explicit opt-outs.
pub const DEFAULT_NO_UNWIND: bool = true;

/// Checks and lowers one specified function.
pub fn lower_fn(
    f: &SpecFn,
    helpers: &BTreeMap<String, HelperSig>,
    runtime: &Uses,
) -> Result<LoweredFn, Vec<Diagnostic>> {
    let mut errors = Vec::new();
    let mut requires = Vec::new();
    let mut safety_only = Vec::new();
    let mut ensures = Vec::new();
    let (mut terminates, mut no_unwind) = (DEFAULT_TERMINATES, DEFAULT_NO_UNWIND);
    let mut terminates_claim: Option<&'static str> = None;
    let mut may_diverge_span: Option<Span> = None;
    let mut no_unwind_claim: Option<&'static str> = None;
    let mut may_unwind_claim: Option<(&'static str, Span)> = None;
    let mut max_steps: Option<(&Expr, Span)> = None;
    let mut targets = 0;
    let mut claims = 0;
    for c in &f.clauses {
        match &c.clause {
            Clause::Requires(e) => requires.push(e),
            Clause::SafetyRequires(e) => {
                if f.is_unsafe {
                    safety_only.push(e);
                } else {
                    errors.push(
                        Diagnostic::new(
                            "E_ANNEAL_SAFETY_REQUIRES_ON_SAFE_FN",
                            c.span,
                            "`safety_requires` on a safe function cannot excuse undefined \
                             behavior",
                        )
                        .help(
                            "a safe function must be free of undefined behavior on every \
                               input; use `requires` to restrict the behavioral domain",
                        ),
                    );
                }
            }
            Clause::Ensures { binder, body } => ensures.push((binder, body, c.span)),
            Clause::MaxSteps(e) => {
                if max_steps.is_some() {
                    errors.push(Diagnostic::new(
                        "E_ANNEAL_DUPLICATE_CLAUSE",
                        c.span,
                        "at most one `max_steps` clause is allowed",
                    ));
                } else {
                    max_steps = Some((e, c.span));
                }
            }
            Clause::Effect(e) => match e {
                Effect::Total => {
                    (terminates, no_unwind) = (true, true);
                    terminates_claim.get_or_insert("total");
                    no_unwind_claim.get_or_insert("total");
                }
                Effect::Terminates => {
                    terminates = true;
                    terminates_claim.get_or_insert("terminates");
                }
                Effect::NoPanic => {
                    no_unwind = true;
                    no_unwind_claim.get_or_insert("no_panic");
                }
                Effect::NoUnwind => {
                    no_unwind = true;
                    no_unwind_claim.get_or_insert("no_unwind");
                }
                Effect::MayDiverge => {
                    terminates = false;
                    may_diverge_span.get_or_insert(c.span);
                }
                Effect::MayUnwind => {
                    no_unwind = false;
                    may_unwind_claim.get_or_insert(("may_unwind", c.span));
                }
                Effect::MayPanic => {
                    no_unwind = false;
                    may_unwind_claim.get_or_insert(("may_panic", c.span));
                }
            },
            Clause::Target(_) => {
                targets += 1;
                if targets > 1 {
                    errors.push(Diagnostic::new(
                        "E_ANNEAL_DUPLICATE_CLAUSE",
                        c.span,
                        "at most one `target` clause is allowed",
                    ));
                }
            }
            Clause::Claim(_) => {
                claims += 1;
                if claims > 1 {
                    errors.push(Diagnostic::new(
                        "E_ANNEAL_DUPLICATE_CLAUSE",
                        c.span,
                        "at most one `claim` clause is allowed",
                    ));
                }
            }
            Clause::Instantiate(_) => errors.push(Diagnostic::new(
                "E_ANNEAL_UNSUPPORTED_CLAUSE",
                c.span,
                "`instantiate` is not supported by the profile v1 lowering, which has no generics",
            )),
        }
    }
    if let (Some(pos_name), Some(md_span)) = (terminates_claim, may_diverge_span) {
        errors.push(Diagnostic::new(
            "E_ANNEAL_CONFLICTING_EFFECTS",
            md_span,
            format!("`may_diverge` conflicts with `{pos_name}` in the same contract"),
        ));
    }
    if let (Some((_, ms_span)), Some(md_span)) = (max_steps, may_diverge_span) {
        let span = if terminates_claim.is_some() { ms_span } else { md_span };
        errors.push(Diagnostic::new(
            "E_ANNEAL_CONFLICTING_EFFECTS",
            span,
            "`max_steps` conflicts with `may_diverge` in the same contract",
        ));
    } else if max_steps.is_some() {
        terminates = true;
    }
    if let (Some(pos_name), Some((neg_name, mw_span))) = (no_unwind_claim, may_unwind_claim) {
        errors.push(Diagnostic::new(
            "E_ANNEAL_CONFLICTING_EFFECTS",
            mw_span,
            format!("`{neg_name}` conflicts with `{pos_name}` in the same contract"),
        ));
    }
    if f.ret == Ty::Never
        && terminates
        && no_unwind
        && requires.is_empty()
        && safety_only.is_empty()
    {
        errors.push(
            Diagnostic::new(
                "E_ANNEAL_UNSATISFIABLE_NEVER_EFFECTS",
                f.attr_span,
                "`-> !` function cannot return normally",
            )
            .help(
                "add `may_panic` (or `may_unwind`) for a panic sink, `may_diverge` for an \
                 infinite loop, or `requires`/`safety_requires` if entry is constrained",
            ),
        );
    }
    let mut facts = Vec::new();
    let pre_uses = Uses::default();
    let mut env = Env::for_fn(f, helpers, &pre_uses);
    env.in_requires = true;
    let mut lower_all = |exprs: &[&Expr], env: &Env<'_>, facts: &mut Vec<String>| -> Vec<String> {
        let mut out = Vec::new();
        for e in exprs {
            match env.lower_prop_in(e, false, facts) {
                Ok(p) => {
                    facts.extend(p.on_true);
                    out.push(p.term);
                }
                Err(d) => errors.push(d),
            }
        }
        out
    };
    // Each precondition kind starts from its own facts: a `safety_requires`
    // guard does not protect `requires`, because `safetyPre` is not part of
    // the behavioral precondition of a body that is not actually `unsafe`.
    // Postconditions may rely on `requires` facts, which `behaviorPre`
    // always contributes.
    let safety_parts = lower_all(&safety_only, &env, &mut Vec::new());
    let safety_q = pre_uses.q.replace(false);
    let req_parts = lower_all(&requires, &env, &mut facts);
    let pre_q = pre_uses.q.get();
    let post_uses = Uses::default();
    let mut post_env = Env::for_fn(f, helpers, &post_uses);
    let mut post_parts = Vec::new();
    for (binder, body, span) in &ensures {
        if let Some(b) = binder {
            if f.ret == Ty::Never {
                errors.push(Diagnostic::new(
                    "E_ANNEAL_UNSUPPORTED_TYPE",
                    *span,
                    "`-> !` functions never return normally, so `ensures` cannot bind a return value",
                ));
                continue;
            }
            if post_env.names.contains_key(b.as_str()) {
                errors.push(Diagnostic::new(
                    "E_ANNEAL_SPEC_SHADOWING",
                    *span,
                    format!("the return binder `{b}` shadows a parameter"),
                ));
                continue;
            }
            post_env.names.insert(b.clone(), Binding::Ret(f.ret));
        }
        match post_env.lower_prop(body, &mut facts.clone()) {
            Ok(p) => post_parts.push(p),
            Err(d) => errors.push(d),
        }
        if let Some(b) = binder {
            post_env.names.remove(b.as_str());
        }
    }
    for u in [&pre_uses, &post_uses] {
        runtime.val_int.set(runtime.val_int.get() | u.val_int.get());
        runtime.val_nat.set(runtime.val_nat.get() | u.val_nat.get());
        runtime.val_bool.set(runtime.val_bool.get() | u.val_bool.get());
        runtime.arg.set(runtime.arg.get() | u.arg.get());
    }
    let steps_uses = Uses::default();
    let mut steps_env = Env::for_fn(f, helpers, &steps_uses);
    steps_env.in_requires = true;
    let lowered_max_steps = match max_steps {
        Some((e, _)) => match steps_env.lower_nat(e, &mut facts.clone()) {
            Ok(t) => Some(t),
            Err(d) => {
                errors.push(d);
                None
            }
        },
        None => None,
    };
    runtime.val_int.set(runtime.val_int.get() | steps_uses.val_int.get());
    runtime.val_nat.set(runtime.val_nat.get() | steps_uses.val_nat.get());
    runtime.val_bool.set(runtime.val_bool.get() | steps_uses.val_bool.get());
    runtime.arg.set(runtime.arg.get() | steps_uses.arg.get());
    if !errors.is_empty() {
        return Err(errors);
    }
    let behavior_pre = conj(&req_parts);
    let safety_pre = if f.is_unsafe {
        conj(&safety_parts.iter().chain(&req_parts).cloned().collect::<Vec<_>>())
    } else {
        None
    };
    Ok(LoweredFn {
        behavior_pre,
        safety_pre,
        post: conj(&post_parts),
        max_steps: lowered_max_steps,
        uses_pre_q: pre_q,
        uses_safety_q: safety_q || pre_q,
        uses_post_q: post_uses.q.get(),
        uses_post_out: post_uses.out.get(),
        uses_max_steps_q: steps_uses.q.get(),
        terminates,
        no_unwind,
    })
}

/// Checks and lowers one helper body, returning its Lean body text.
pub fn lower_helper(
    h: &PureFn,
    helpers: &BTreeMap<String, HelperSig>,
    runtime: &Uses,
) -> Result<String, Diagnostic> {
    for p in &h.params {
        if p.ty == Ty::Unit {
            return Err(type_error(p.span, "`()` parameters are not supported in helpers"));
        }
        if reserved_param_name(&p.name) {
            return Err(Diagnostic::new(
                "E_ANNEAL_RESERVED_PARAM_NAME",
                p.span,
                format!(
                    "`{}` cannot name a `#[anneal::pure]` helper parameter: it is reserved \
                     by the generated Lean",
                    p.name
                ),
            )
            .help("rename the parameter"));
        }
    }
    let env = Env::for_helper(&h.params, helpers, runtime);
    let mut low = env.lower(&h.body, false, &mut Vec::new())?;
    if let (Low::UntypedIf(..), Ty::Int(_)) = (&low, h.ret) {
        low = settle(low, h.ret)?;
    }
    match (low, h.ret) {
        (Low::Prop(p), Ty::Bool) => Ok(p.term),
        (Low::Int(t, Ty::Int(a)), Ty::Int(b)) if a == b => Ok(t),
        (Low::Lit(v, s), Ty::Int(b)) => {
            check_range(v, b, s)?;
            Ok(int_lit(v))
        }
        (low, ret) => Err(type_error(
            h.body.span,
            format!(
                "helper `{}` returns `{}`, but its body has {}",
                h.name,
                ret.describe(),
                describe(&low)
            ),
        )
        .help("a mathematical result cannot be returned as a fixed-width integer implicitly")),
    }
}

/// Whether `e` refers to the variable `name`. Bindings may not shadow, so
/// every `name` in `e` is that variable.
fn mentions(e: &Expr, name: &str) -> bool {
    match &e.kind {
        ExprKind::Ident(n) => n == name,
        ExprKind::Call(_, args) => args.iter().any(|a| mentions(a, name)),
        ExprKind::Unary(_, x) | ExprKind::Math(x) | ExprKind::Old(x) | ExprKind::Paren(x) => {
            mentions(x, name)
        }
        ExprKind::Binary(_, a, b) => mentions(a, name) || mentions(b, name),
        ExprKind::If(c, t, f) => mentions(c, name) || mentions(t, name) || mentions(f, name),
        ExprKind::Let(b, body) => mentions(&b.init, name) || mentions(body, name),
        ExprKind::Bool(_) | ExprKind::Int(..) | ExprKind::IntConst(..) | ExprKind::Unit => false,
    }
}

/// Helper names called (directly) by `e`.
pub fn calls_in(e: &Expr, out: &mut Vec<String>) {
    match &e.kind {
        ExprKind::Call(n, args) => {
            out.push(n.clone());
            args.iter().for_each(|a| calls_in(a, out));
        }
        ExprKind::Unary(_, x) | ExprKind::Math(x) | ExprKind::Old(x) | ExprKind::Paren(x) => {
            calls_in(x, out)
        }
        ExprKind::Binary(_, a, b) => {
            calls_in(a, out);
            calls_in(b, out);
        }
        ExprKind::If(c, t, f) => {
            calls_in(c, out);
            calls_in(t, out);
            calls_in(f, out);
        }
        ExprKind::Let(b, body) => {
            calls_in(&b.init, out);
            calls_in(body, out);
        }
        _ => {}
    }
}
