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
        Arm, BinOp, Clause, Effect, Expr, ExprKind, IntConst, IntTy, LetBinding, Param, PatKind,
        PureFn, SpecFn, Ty, UnOp,
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

/// The Lean binder of a `match` scrutinee. `match` is a Rust keyword, so no
/// specification name can capture it or be captured by it.
const MATCH_BINDER: &str = "«match»";

/// What a `match` scrutinee is, as its Lean binder sees it.
#[derive(Clone, Copy)]
enum ScrutKind {
    /// A `bool`, bound as a `Prop`.
    Prop,
    /// An integer of type `ty` (a machine type or `Ty::Math`), bound as an
    /// `Int`.
    Int(Ty),
    /// A `max_steps` step count, bound as a `Nat`.
    Nat,
}

/// One checked `match` arm.
struct ArmPlan<'e, 'a> {
    arm: &'e Arm,
    /// The condition under which the arm is taken, if earlier arms are not;
    /// `None` for a catch-all.
    cond: Option<String>,
    /// The environment and facts of the arm's body.
    env: Env<'a>,
    facts: Vec<String>,
    /// The Lean `let` that binds the arm's pattern name, if any.
    prefix: String,
    /// The Lean name of the arm's pattern binding, if any.
    binder: Option<String>,
}

/// A checked `match`.
struct MatchPlan<'e, 'a> {
    term: String,
    kind: ScrutKind,
    /// Why a `bool` scrutinee is undecidable, if it is.
    undecidable: Option<(Span, String)>,
    arms: Vec<ArmPlan<'e, 'a>>,
    /// Whether any condition or pattern binding refers to the scrutinee.
    binder_used: bool,
}

impl MatchPlan<'_, '_> {
    /// The Lean `let` that binds the scrutinee, if anything uses it.
    fn binder_prefix(&self) -> Option<String> {
        let ty = match self.kind {
            ScrutKind::Prop => "Prop",
            ScrutKind::Int(_) => INT,
            ScrutKind::Nat => "Nat",
        };
        self.binder_used.then(|| format!("let {MATCH_BINDER} : {ty} := {}; ", self.term))
    }

    /// Requires the scrutinee of a `match` whose arms choose a value to be
    /// decidable, as an `if` condition must be.
    fn require_decidable(&self) -> Result<(), Diagnostic> {
        require_decidable_reason(self.undecidable.as_ref())
    }
}

/// Unqualified names that lowered clause text references besides
/// [`GLOBALS`]. A `let` binder named after one would capture it.
const CLAUSE_NAMES: &[&str] = &["q", "out", "specArg", "specBool", "specInt", "specNat"];

// Every global the lowering references is qualified from one of a few root
// names (`Int`, `Nat`, `True`, `False`, `Trusted`, `Min`, `Max`, and the
// output namespace's root, `Spec` or `Specs`). Helper parameters become
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
/// The Lean type of bit patterns and step counts.
const NAT: &str = "Nat";
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
/// Rust's `<<` on a mathematical integer, before truncation to a width.
const INT_SHIFT_LEFT: &str = "Trusted.MirSemantics.intShiftLeft";
/// Rust's arithmetic `>>` on a mathematical integer.
/// Lean's `min` and `max`, which on `Int` are `if a ≤ b then a else b` and
/// `if a ≤ b then b else a`.
const MIN: &str = "Min.min";
const MAX: &str = "Max.max";
const INT_SHIFT_RIGHT: &str = "Trusted.MirSemantics.intShiftRight";
/// The namespace `emit` defines everything in for `--format v1`.
pub const SPEC_NAMESPACE: &str = "Spec";
/// The root of the `Specs.<crate>.<claim>` namespaces of `--format v2-module`.
pub const SPECS_ROOT: &str = "Specs";

/// Every global name that lowered helper text references.
const GLOBALS: &[&str] = &[
    INT,
    NAT,
    INT_NEG,
    TRUE,
    FALSE,
    VAL,
    VAL_UNIT,
    INT_TDIV,
    INT_TMOD,
    INT_EMOD,
    INT_SHIFT_LEFT,
    INT_SHIFT_RIGHT,
    MIN,
    MAX,
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
    "wrapping_neg",
    "wrapping_shl",
    "wrapping_shr",
    "no_overflow_add",
    "no_overflow_sub",
    "no_overflow_mul",
    "no_overflow_neg",
    "saturating_add",
    "saturating_sub",
    "saturating_mul",
    "saturating_neg",
    "abs_diff",
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

/// The Lean binder of a saturating intrinsic's exact result. The `let` body
/// that binds it mentions only it and literals, so it captures no
/// specification name; it need only not be a root of a name in [`GLOBALS`].
const SATURATE_BINDER: &str = "«saturating»";

/// The Lean binder of the `Nat` value that `is_power_of_two` tests. As with
/// [`SATURATE_BINDER`], the body that binds it mentions only it and
/// literals.
const POWER_OF_TWO_BINDER: &str = "«power_of_two»";

/// `exact`, the mathematical result of an operation on `t`, clamped to `t`'s
/// range, as Rust's `saturating_*` methods compute it. `exact` is bound once
/// so that nested saturating intrinsics do not duplicate their operands.
fn saturate(exact: &str, t: IntTy) -> String {
    let (lo, hi) = t.range();
    let lo = IntLit::new(lo < 0, lo.unsigned_abs()).to_lean();
    let hi = IntLit::new(false, hi).to_lean();
    let s = SATURATE_BINDER;
    format!(
        "(let {s} : {INT} := {exact}; \
         if {s} < {lo} then {lo} else if {hi} < {s} then {hi} else {s})"
    )
}

/// `u32`, the type of the amount of Rust's `wrapping_shl` and
/// `wrapping_shr`.
const U32: IntTy = IntTy { bits: 32, signed: false, pointer_sized: false };

/// `i32`, Rust's default type for an integer literal, which an unsuffixed
/// literal cast with `as` has.
const I32: IntTy = IntTy { bits: 32, signed: true, pointer_sized: false };

/// Whether every value of `s` is a value of `t`.
fn fits(s: IntTy, t: IntTy) -> bool {
    let ((s_lo, s_hi), (t_lo, t_hi)) = (s.range(), t.range());
    t_lo <= s_lo && s_hi <= t_hi
}

/// `body`, a function of `params` of Lean type `ty`, applied to `args`. The
/// arguments lie outside the `fun`, so each is evaluated once and none is in
/// the scope of a parameter, which `body` alone mentions.
fn apply_fun(params: &[&str], ty: &str, body: &str, args: &[String]) -> String {
    format!("((fun ({} : {ty}) => {body}) {})", params.join(" "), args.join(" "))
}

/// Whether `a <= b`.
fn lit_le(a: IntLit, b: IntLit) -> bool {
    match (a.neg && a.mag != 0, b.neg && b.mag != 0) {
        (false, false) => a.mag <= b.mag,
        (true, true) => b.mag <= a.mag,
        (a_neg, _) => a_neg,
    }
}

/// The integer `a` reduced into `t`'s range modulo `2^bits`, as Rust's
/// `as` and wrapping arithmetic compute it.
fn wrap_into(a: &str, t: IntTy) -> String {
    let m = modulus(t);
    if t.signed {
        let h = half_modulus(t);
        format!("({INT_EMOD} ({a} + {h}) {m} - {h})")
    } else {
        format!("({INT_EMOD} {a} {m})")
    }
}

/// `a` shifted by `amount` (a Lean `Nat` term below the bit width of `t`)
/// as Rust's `<<` or `>>` on `t` computes it. A left shift drops the bits
/// shifted past the width, and a right shift is arithmetic on a signed `t`.
fn shift_term(op: BinOp, a: &str, amount: &str, t: IntTy) -> String {
    if matches!(op, BinOp::Shr) {
        return format!("({INT_SHIFT_RIGHT} {a} {amount})");
    }
    let m = modulus(t);
    if t.signed {
        let h = half_modulus(t);
        format!("({INT_EMOD} ({INT_SHIFT_LEFT} {a} {amount} + {h}) {m} - {h})")
    } else {
        format!("({INT_EMOD} ({INT_SHIFT_LEFT} {a} {amount}) {m})")
    }
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
        IntConst::Bits => (IntLit::new(false, u128::from(t.bits)), U32),
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
            ExprKind::Match(s, arms) => {
                let plan = self.plan_match(s, arms, e.span, false, true, facts)?;
                let mut terms = Vec::new();
                for arm in &plan.arms {
                    let t = arm.env.lower_nat(&arm.arm.body, &mut arm.facts.clone())?;
                    terms.push(if arm.prefix.is_empty() {
                        t
                    } else {
                        format!("({}{t})", arm.prefix)
                    });
                }
                if terms.len() > 1 {
                    plan.require_decidable()?;
                }
                let mut acc = terms.pop().expect("a `match` has at least one arm");
                for (i, t) in terms.into_iter().enumerate().rev() {
                    let cond =
                        plan.arms[i].cond.as_deref().expect("only the last arm is a catch-all");
                    acc = format!("(if {cond} then {t} else {acc})");
                }
                Ok(match plan.binder_prefix() {
                    Some(prefix) => format!("({prefix}{acc})"),
                    None => acc,
                })
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
                let low = self.lower(e, false, facts)?;
                self.machine_step_count(low, e.span, "`!`")
            }
            // A cast to an unsigned type is a step count.
            ExprKind::Cast(..) => {
                let low = self.lower(e, false, facts)?;
                self.machine_step_count(low, e.span, "`as`")
            }
            // So is an unsigned result of an integer method.
            ExprKind::Method(name, ..) => {
                let low = self.lower(e, false, facts)?;
                self.machine_step_count(low, e.span, &format!("`.{name}()`"))
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
                // Bitwise operators and shifts act on machine integers, so a
                // step count may use their unsigned results.
                BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                    let low = self.binary(*op, l, r, e.span, false, facts)?;
                    self.machine_step_count(low, e.span, &format!("`{}`", op.rust()))
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
                // `!x` on an integer flips its bits: `-x - 1` in two's
                // complement, which for an unsigned `x` is `MAX - x`.
                Low::Int(a, Ty::Int(t)) => {
                    let term = if t.signed {
                        format!("({INT_NEG} {a} - 1)")
                    } else {
                        format!("({} - {a})", IntLit::new(false, t.range().1).to_lean())
                    };
                    Ok(Low::Int(term, Ty::Int(t)))
                }
                Low::Int(_, _) => Err(type_error(
                    inner.span,
                    "`!` on an integer inside `math` is ambiguous: its result depends on the \
                     operand's width",
                )
                .help(
                    "give it a machine type first, as in `let n: u8 = !a;`, or apply `!` \
                     outside `math`",
                )),
                other @ (Low::Lit(..) | Low::UntypedIf(..)) => Err(Diagnostic::new(
                    "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED",
                    inner.span,
                    format!(
                        "the type of the operand of `!` cannot be inferred from {}",
                        describe(&other)
                    ),
                )
                .help("add a suffix such as `5u8`")),
                other => Err(type_error(
                    inner.span,
                    format!(
                        "`!` expects `bool` or a fixed-width integer, found {}",
                        describe(&other)
                    ),
                )),
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
            ExprKind::Cast(inner, t) => self.cast(inner, *t, math, facts),
            ExprKind::Call(name, args) => self.call(name, args, e.span, math, facts),
            ExprKind::Method(name, recv, args) => {
                self.method(name, recv, args, e.span, math, facts)
            }
            ExprKind::If(c, t, f) => self.lower_if(c, t, f, math, facts),
            ExprKind::Let(b, body) => {
                let (env, prefix, extra) = self.bind(b, body, math, false, facts)?;
                let mut body_facts = facts.clone();
                body_facts.extend(extra);
                let low = env.lower(body, math, &mut body_facts)?;
                Ok(wrap_low(&prefix, &lean_ident(&b.name), low))
            }
            ExprKind::Match(s, arms) => {
                let plan = self.plan_match(s, arms, e.span, math, false, facts)?;
                let mut lows = Vec::new();
                for arm in &plan.arms {
                    let low = arm.env.lower(&arm.arm.body, math, &mut arm.facts.clone())?;
                    lows.push(match &arm.binder {
                        Some(lean) => wrap_low(&arm.prefix, lean, low),
                        None => low,
                    });
                }
                let mut acc = lows.pop().expect("a `match` has at least one arm");
                for (i, low) in lows.into_iter().enumerate().rev() {
                    let cond =
                        plan.arms[i].cond.as_deref().expect("only the last arm is a catch-all");
                    acc = self.combine_branches(
                        cond,
                        plan.undecidable.as_ref(),
                        low,
                        acc,
                        plan.arms[i + 1].arm.body.span,
                        math,
                        "`match` arms",
                    )?;
                }
                Ok(match plan.binder_prefix() {
                    Some(prefix) => wrap_low(&prefix, MATCH_BINDER, acc),
                    None => acc,
                })
            }
        }
    }

    /// A copy of this environment.
    fn scope(&self) -> Env<'a> {
        Env {
            helpers: self.helpers,
            names: self.names.clone(),
            uses: self.uses,
            in_requires: self.in_requires,
        }
    }

    /// Checks `match s { arms }` (at `span`) and plans its lowering: the
    /// scrutinee's Lean term and kind, and for each arm the condition under
    /// which it is taken, the environment and facts of its body, and the
    /// binding of its pattern name. Each arm's facts are those that hold when
    /// the earlier arms are not taken and it is. In `max_steps` (`nat`), an
    /// integer scrutinee is a step count. Integer patterns are checked
    /// against the scrutinee's machine type, if it has one, and against
    /// their own suffixes.
    fn plan_match<'e>(
        &self,
        s: &Expr,
        arms: &'e [Arm],
        span: Span,
        math: bool,
        nat: bool,
        facts: &[String],
    ) -> Result<MatchPlan<'e, 'a>, Diagnostic> {
        let scratch = Uses::default();
        let probe = self.probe(&scratch);
        let no_unit = || type_error(s.span, "a `match` cannot examine a `()`");
        // A `bool` scrutinee, which carries its decidability and the facts it
        // establishes when it holds and when it fails.
        let mut prop = None;
        let (term, kind) = if nat {
            match probe.lower(s, true, &mut facts.to_vec()) {
                Ok(Low::Prop(_)) => {
                    let p = self.lower_prop_in(s, false, &mut facts.to_vec())?;
                    let term = p.term.clone();
                    prop = Some(p);
                    (term, ScrutKind::Prop)
                }
                Ok(Low::Unit(_)) => return Err(no_unit()),
                _ => (self.lower_nat(s, &mut facts.to_vec())?, ScrutKind::Nat),
            }
        } else {
            match self.lower(s, math, &mut facts.to_vec())? {
                Low::Prop(p) => {
                    let term = p.term.clone();
                    prop = Some(p);
                    (term, ScrutKind::Prop)
                }
                Low::Int(t, ty) => (t, ScrutKind::Int(ty)),
                Low::Unit(_) => return Err(no_unit()),
                untyped => {
                    // An untyped scrutinee takes its type from a typed pattern.
                    let typed = arms.iter().flat_map(|a| &a.pats).find_map(|p| match p.kind {
                        PatKind::Int { suffix: Some(t), .. } => Some(Ty::Int(t)),
                        PatKind::IntConst(t, c) => Some(Ty::Int(int_const(t, c).1)),
                        _ => None,
                    });
                    let Some(ty) = typed.or(math.then_some(Ty::Math)) else {
                        return Err(Diagnostic::new(
                            "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED",
                            s.span,
                            "the type of this `match` scrutinee cannot be inferred",
                        )
                        .help("add a suffix such as `5usize`, or use `math(...)`"));
                    };
                    let Low::Int(t, ty) = settle(untyped, ty)? else { unreachable!() };
                    (t, ScrutKind::Int(ty))
                }
            }
        };
        // The scrutinee's machine integer type, if it has one. A `max_steps`
        // scrutinee is compared as in a `max_steps` `if` condition, where
        // values keep their machine types, so it has the type it has there.
        // A `math` scrutinee has none.
        let machine = match kind {
            ScrutKind::Int(Ty::Int(t)) => Some(t),
            ScrutKind::Nat => match probe.lower(s, false, &mut facts.to_vec()) {
                Ok(Low::Int(_, Ty::Int(t))) => Some(t),
                _ => None,
            },
            ScrutKind::Prop | ScrutKind::Int(_) => None,
        };
        let describe_kind = match (kind, machine) {
            (ScrutKind::Prop, _) => "bool".to_string(),
            (ScrutKind::Int(ty), _) => ty.describe(),
            (ScrutKind::Nat, Some(t)) => t.rust_name(),
            (ScrutKind::Nat, None) => "step count".to_string(),
        };
        // The scrutinee's term in divisor facts, and its `bool` facts.
        let nonzero_fact = match probe.lower(s, true, &mut facts.to_vec()) {
            Ok(Low::Int(t, _)) => Some(t),
            _ => None,
        };
        let (undecidable, when_true, when_false) = match prop {
            Some(p) => (p.undecidable, p.on_true, p.on_false),
            None => (None, Vec::new(), Vec::new()),
        };
        let unreachable_arm = |span: Span, msg: &str| {
            Diagnostic::new("E_ANNEAL_UNREACHABLE_MATCH_ARM", span, msg)
                .help("remove the pattern or arm that can never be reached")
        };
        let mut seen: Vec<IntLit> = Vec::new();
        let mut seen_bools = [false; 2];
        let mut catch_all = false;
        let mut not_taken: Vec<String> = Vec::new();
        let mut plans = Vec::new();
        let mut binder_used = false;
        for (i, arm) in arms.iter().enumerate() {
            if catch_all || seen_bools == [true, true] {
                return Err(unreachable_arm(arm.span, "earlier arms already match every value"));
            }
            let mut conds = Vec::new();
            let mut taken = Vec::new();
            let mut not_taken_here = Vec::new();
            let (mut has_zero, mut all_nonzero) = (false, true);
            let mut binding = None;
            for p in &arm.pats {
                match &p.kind {
                    PatKind::Wild => {
                        catch_all = true;
                        all_nonzero = false;
                    }
                    PatKind::Bind(name) => {
                        catch_all = true;
                        all_nonzero = false;
                        binding = Some((name.as_str(), p.span));
                    }
                    PatKind::Bool(b) => {
                        if !matches!(kind, ScrutKind::Prop) {
                            return Err(type_error(
                                p.span,
                                format!("a `bool` pattern cannot match `{describe_kind}`"),
                            ));
                        }
                        if std::mem::replace(&mut seen_bools[usize::from(*b)], true) {
                            return Err(unreachable_arm(
                                p.span,
                                &format!("`{b}` is already matched"),
                            ));
                        }
                        conds.push(if *b {
                            MATCH_BINDER.to_string()
                        } else {
                            format!("(¬ {MATCH_BINDER})")
                        });
                        let (yes, no) =
                            if *b { (&when_true, &when_false) } else { (&when_false, &when_true) };
                        taken.extend(yes.iter().cloned());
                        not_taken_here.extend(no.iter().cloned());
                    }
                    PatKind::Int { .. } | PatKind::IntConst(..) => {
                        let (v, pty) = match p.kind {
                            PatKind::Int { neg, mag, suffix } => (IntLit::new(neg, mag), suffix),
                            PatKind::IntConst(t, c) => {
                                let (v, ty) = int_const(t, c);
                                (v, Some(ty))
                            }
                            _ => unreachable!(),
                        };
                        let mismatch = |found: &str| {
                            type_error(p.span, format!("{found} cannot match `{describe_kind}`"))
                        };
                        match kind {
                            ScrutKind::Prop => {
                                return Err(mismatch(
                                    &pty.map_or("an integer pattern".into(), |t| {
                                        format!("a `{}` pattern", t.rust_name())
                                    }),
                                ))
                            }
                            ScrutKind::Nat if v.neg || pty.is_some_and(|t| t.signed) => {
                                return Err(type_error(
                                    p.span,
                                    "`max_steps` patterns must be non-negative and unsigned",
                                ));
                            }
                            ScrutKind::Int(_) | ScrutKind::Nat => {
                                if let Some(pt) = pty.filter(|pt| machine.is_some_and(|t| t != *pt))
                                {
                                    return Err(mismatch(&format!(
                                        "a `{}` pattern",
                                        pt.rust_name()
                                    )));
                                }
                                // As with a suffixed literal in `math(..)`, a
                                // suffixed pattern is in range for its suffix
                                // even where the scrutinee has no machine type.
                                if let Some(t) = machine.or(pty) {
                                    check_range(v, t, p.span)?;
                                }
                            }
                        }
                        if seen.iter().any(|w| w.neg == v.neg && w.mag == v.mag) {
                            return Err(unreachable_arm(
                                p.span,
                                &format!("`{v}` is already matched"),
                            ));
                        }
                        seen.push(v);
                        conds.push(match kind {
                            ScrutKind::Nat => format!("({MATCH_BINDER} = ({} : Nat))", v.mag),
                            _ => format!("({MATCH_BINDER} = {})", int_lit(v)),
                        });
                        has_zero |= v.mag == 0;
                        all_nonzero &= v.mag != 0;
                    }
                }
            }
            // The arm is taken when the earlier arms are not and its pattern
            // matches.
            let mut arm_facts = facts.to_vec();
            arm_facts.extend(not_taken.iter().cloned());
            arm_facts.extend(taken);
            if all_nonzero && !conds.is_empty() {
                arm_facts.extend(nonzero_fact.clone());
            }
            not_taken.extend(not_taken_here);
            if has_zero {
                not_taken.extend(nonzero_fact.clone());
            }
            let cond = match conds.len() {
                0 => None,
                1 => conds.pop(),
                _ => Some(format!("({})", conds.join(" ∨ "))),
            };
            binder_used |= cond.is_some() && i + 1 < arms.len();
            let (env, prefix, binder) = match binding {
                None => (self.scope(), String::new(), None),
                Some((name, span)) => {
                    self.check_binder(name, span, "pattern binding")?;
                    if !mentions(&arm.body, name) {
                        return Err(Diagnostic::new(
                            "E_ANNEAL_UNUSED_LET",
                            span,
                            format!("the pattern binding `{name}` is never used"),
                        )
                        .help("write `_` instead"));
                    }
                    let lean = lean_ident(name);
                    if nonzero_fact.as_ref().is_some_and(|t| arm_facts.contains(t)) {
                        arm_facts.push(match kind {
                            ScrutKind::Nat => format!("({INT}.ofNat {lean})"),
                            _ => lean.clone(),
                        });
                    }
                    let (local, ty) = match kind {
                        ScrutKind::Prop => {
                            let decidable = undecidable.is_none();
                            let (when_true, when_false) = (when_true.clone(), when_false.clone());
                            (LocalKind::Prop { decidable, when_true, when_false }, "Prop")
                        }
                        ScrutKind::Int(ty) => (LocalKind::Int { ty, value: None }, INT),
                        ScrutKind::Nat => (LocalKind::Nat { value: None }, "Nat"),
                    };
                    binder_used = true;
                    let prefix = format!("let {lean} : {ty} := {MATCH_BINDER}; ");
                    (self.with(name, Binding::Local(lean.clone(), local)), prefix, Some(lean))
                }
            };
            plans.push(ArmPlan { arm, cond, env, facts: arm_facts, prefix, binder });
        }
        if !catch_all && seen_bools != [true, true] {
            let msg = match kind {
                ScrutKind::Prop => {
                    format!(
                        "this `match` does not match `{}`",
                        if seen_bools[1] { "false" } else { "true" }
                    )
                }
                _ => "a `match` on an integer must end with a `_` or name arm".to_string(),
            };
            return Err(Diagnostic::new("E_ANNEAL_NON_EXHAUSTIVE_MATCH", span, msg)
                .help("add a final `_ => ..` arm"));
        }
        Ok(MatchPlan { term, kind, undecidable, arms: plans, binder_used })
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
        self.check_binder(name, b.name_span, "`let` binding")?;
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

    /// Rejects a binder `name` (a `let` binding or a `match` pattern
    /// binding, as `what` says) that is reserved or that shadows a name in
    /// scope.
    fn check_binder(&self, name: &str, span: Span, what: &str) -> Result<(), Diagnostic> {
        let intrinsic = INTRINSICS.contains(&name)
            || name == "old"
            || name.starts_with("wrapping_")
            || name.starts_with("no_overflow_")
            || name.starts_with("saturating_");
        if reserved_param_name(name) || CLAUSE_NAMES.contains(&name) || intrinsic {
            return Err(Diagnostic::new(
                "E_ANNEAL_RESERVED_PARAM_NAME",
                span,
                format!(
                    "`{name}` cannot name a {what}: it is reserved by the generated Lean or \
                     names an intrinsic"
                ),
            )
            .help("rename the binding"));
        }
        let shadowed = match self.names.get(name) {
            Some(Binding::Arg(..) | Binding::HelperParam(..)) => Some("a parameter"),
            Some(Binding::Ret(_)) => Some("the `ensures` return binder"),
            Some(Binding::Local(..)) => Some("an enclosing binding"),
            None if self.helpers.contains_key(name) => Some("a `#[anneal::pure]` helper"),
            None => None,
        };
        if let Some(shadowed) = shadowed {
            return Err(Diagnostic::new(
                "E_ANNEAL_SPEC_SHADOWING",
                span,
                format!("the {what} `{name}` shadows {shadowed}"),
            )
            .help("choose a name that is not already in scope"));
        }
        Ok(())
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
        let mut then_facts = facts.clone();
        then_facts.extend(cond.on_true);
        let mut else_facts = facts.clone();
        else_facts.extend(cond.on_false);
        let a = self.lower(t, math, &mut then_facts)?;
        let b = self.lower(f, math, &mut else_facts)?;
        self.combine_branches(
            &cond.term,
            cond.undecidable.as_ref(),
            a,
            b,
            f.span,
            math,
            "`if` and `else`",
        )
    }

    /// Joins `a` and `b`, the values of the two sides of condition `cond`,
    /// which is undecidable for the reason `undecidable`, if any. `bool`s
    /// join as `((cond → a) ∧ (¬ cond → b))`, which needs no `Decidable`
    /// instance but is decidable only if `cond`, `a`, and `b` are. Other
    /// values must have one type, which an untyped integer takes from the
    /// other side, and join as Lean's `if cond then a else b`, which needs
    /// `cond` to be decidable. `b_span` and `what` (such as "`if` and
    /// `else`") locate type errors.
    #[allow(clippy::too_many_arguments)]
    fn combine_branches(
        &self,
        cond: &str,
        undecidable: Option<&(Span, String)>,
        a: Low,
        b: Low,
        b_span: Span,
        math: bool,
        what: &str,
    ) -> Result<Low, Diagnostic> {
        let ite = |x: &str, y: &str| format!("(if {cond} then {x} else {y})");
        let (a, b) = match (a, b) {
            (Low::Prop(x), Low::Prop(y)) => {
                return Ok(Low::Prop(Prop {
                    term: format!("(({cond} → {}) ∧ (¬ {cond} → {}))", x.term, y.term),
                    undecidable: undecidable.cloned().or(x.undecidable).or(y.undecidable),
                    on_true: Vec::new(),
                    on_false: Vec::new(),
                }));
            }
            (x, y) if is_untyped(&x) && is_untyped(&y) => {
                require_decidable_reason(undecidable)?;
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
                        b_span,
                        format!(
                            "{what} have mismatched types `{}` and `{}`",
                            tx.describe(),
                            ty.describe()
                        ),
                    )
                    .help("give both branches one type, e.g. by wrapping both in `math(..)`"));
                }
                require_decidable_reason(undecidable)?;
                Ok(Low::Int(ite(&x, &y), tx))
            }
            (Low::Unit(x), Low::Unit(y)) => {
                require_decidable_reason(undecidable)?;
                Ok(Low::Unit(ite(&x, &y)))
            }
            (a, b) => Err(type_error(
                b_span,
                format!("{what} have incompatible types: {} and {}", describe(&a), describe(&b)),
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
                // Like the wrapping intrinsics, bitwise operators take
                // machine-typed operands even inside `math`, since their
                // meaning depends on the type's width.
                let a = self.lower(l, false, facts)?;
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
                let b = self.lower(r, false, facts)?;
                let (a, b, t) = match Self::unify_pair(a, b, l, r, false)? {
                    (Low::Int(a, Ty::Int(t)), Low::Int(b, Ty::Int(_))) => (a, b, t),
                    _ => {
                        return Err(type_error(
                            span,
                            format!(
                                "`{}` needs two operands of one fixed-width integer type",
                                op.rust()
                            ),
                        ));
                    }
                };
                let sym = match op {
                    BinOp::BitAnd => "&&&",
                    BinOp::BitOr => "|||",
                    _ => "^^^",
                };
                let ty = if math { Ty::Math } else { Ty::Int(t) };
                // The operation acts on the two's-complement bits, which are
                // an unsigned value's own and a signed value's remainder
                // modulo `2^bits`.
                let term = if t.signed {
                    let m = modulus(t);
                    let h = half_modulus(t);
                    let bits = |x: &str| format!("({INT}.toNat ({INT_EMOD} {x} {m}))");
                    format!(
                        "({INT_EMOD} ({INT}.ofNat ({} {sym} {}) + {h}) {m} - {h})",
                        bits(&a),
                        bits(&b)
                    )
                } else {
                    format!("({INT}.ofNat (({INT}.toNat {a}) {sym} ({INT}.toNat {b})))")
                };
                Ok(Low::Int(term, ty))
            }
            BinOp::Shl | BinOp::Shr => self.shift(op, l, r, math, facts),
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

    /// Lowers `l << r` or `l >> r`. As with the other bitwise operators,
    /// `l` is machine-typed even inside `math`. Rust panics on, or masks,
    /// an amount that is not below the bit width of `l`, so `r` must be a
    /// constant that is. Its type, as in Rust, may be any integer type.
    fn shift(
        &self,
        op: BinOp,
        l: &Expr,
        r: &Expr,
        math: bool,
        facts: &mut Vec<String>,
    ) -> Result<Low, Diagnostic> {
        let sym = op.rust();
        let (a, t) = match self.lower(l, false, facts)? {
            Low::Int(a, Ty::Int(t)) => (a, t),
            low @ (Low::Lit(..) | Low::UntypedIf(..)) => {
                return Err(Diagnostic::new(
                    "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED",
                    l.span,
                    format!(
                        "the type of the left operand of `{sym}` cannot be inferred from {}",
                        describe(&low)
                    ),
                )
                .help("add a suffix such as `1u32`"));
            }
            low => {
                return Err(type_error(
                    l.span,
                    format!(
                        "`{sym}` needs a fixed-width integer to shift, found {}",
                        describe(&low)
                    ),
                ));
            }
        };
        let amount = match self.lower(r, false, facts)? {
            Low::Int(term, _) => Some(term),
            Low::Lit(..) | Low::UntypedIf(..) => None,
            low => {
                return Err(type_error(
                    r.span,
                    format!("a shift amount must be an integer, found {}", describe(&low)),
                ));
            }
        };
        let Some(k) = self.const_value(r) else {
            return Err(Diagnostic::new(
                "E_ANNEAL_AMBIGUOUS_SPEC_ARITH",
                r.span,
                format!(
                    "`{sym}` by an amount that is not a constant is ambiguous: Rust panics on, or \
                     masks, an amount that is not below the bit width"
                ),
            )
            .help(format!(
                "shift by a constant, or write `wrapping_{}(a, n)` for the masked shift",
                if matches!(op, BinOp::Shl) { "shl" } else { "shr" }
            )));
        };
        if k.neg || k.mag >= u128::from(t.bits) {
            return Err(Diagnostic::new(
                "E_ANNEAL_SPEC_LITERAL_RANGE",
                r.span,
                format!(
                    "shift amount `{k}` is out of range for `{}`, which shifts by less than {}",
                    t.rust_name(),
                    t.bits
                ),
            ));
        }
        // A literal amount is written as the number. Any other constant
        // amount, such as a `let`-bound one, is written as its lowered term,
        // so the Lean term uses the binding the specification names; its
        // value is `k`, which the check above keeps in range.
        let amount = match (const_int_lit(r), amount) {
            (None, Some(term)) => format!("({INT}.toNat {term})"),
            _ => k.mag.to_string(),
        };
        let term = shift_term(op, &a, &amount, t);
        Ok(Low::Int(term, if math { Ty::Math } else { Ty::Int(t) }))
    }

    /// Rejects `arg` (lowered to `term`) as the divisor of method `name`
    /// unless it is a nonzero constant or `facts` says it is nonzero, as for
    /// `/`.
    fn require_nonzero_divisor(
        &self,
        name: &str,
        arg: &Expr,
        term: &str,
        facts: &[String],
    ) -> Result<(), Diagnostic> {
        let nonzero_lit = self.const_value(arg).is_some_and(|v| v.mag != 0);
        if nonzero_lit || facts.iter().any(|f| f == term) {
            return Ok(());
        }
        Err(Diagnostic::new(
            "E_ANNEAL_UNGUARDED_SPEC_DIV",
            arg.span,
            format!("the divisor of `{name}` may be zero"),
        )
        .help(format!("guard it, e.g. `d != 0 ==> a.{name}(d) == ...`")))
    }

    /// Lowers `arg`, the `u32` amount of method `name`, which as in Rust may
    /// be an untyped literal.
    fn u32_amount(
        &self,
        name: &str,
        arg: &Expr,
        facts: &mut Vec<String>,
    ) -> Result<String, Diagnostic> {
        match self.lower(arg, false, facts)? {
            Low::Int(n, Ty::Int(u)) if u == U32 => Ok(n),
            low @ Low::Lit(..) => {
                let Low::Int(n, _) = settle(low, Ty::Int(U32))? else { unreachable!() };
                Ok(n)
            }
            low => Err(type_error(
                arg.span,
                format!("`{name}` takes a `u32` amount, found {}", describe(&low)),
            )),
        }
    }

    /// Lowers the integer method call `recv.name(args)` at `span`. A method
    /// named like an intrinsic is that intrinsic with `recv` as its first
    /// operand. `min`, `max`, and `clamp` take operands of `recv`'s
    /// fixed-width integer type, even inside `math`, where their result is
    /// mathematical, and lower to Lean's `min` and `max`, which evaluate
    /// each operand once. Rust panics when the bounds of `clamp` are out of
    /// order, so they must be constants in order. `is_power_of_two` takes an
    /// unsigned `recv`, as in Rust, and is a decidable `bool`, as is
    /// `is_multiple_of`. `div_ceil` takes unsigned operands and a divisor
    /// guarded as for `/`. `rotate_left` and `rotate_right` rotate the bits
    /// of `recv` by a `u32` amount modulo the bit width. The sign tests,
    /// `signum`, and the `_abs` methods take a signed `recv`, and
    /// `cast_signed` and `cast_unsigned` reinterpret its bits as the
    /// same-width type of the other signedness. The mixed-signedness
    /// methods, such as `wrapping_add_signed`, take an operand of `recv`'s
    /// width and the other signedness. `unbounded_shl` and `unbounded_shr`
    /// shift by any `u32` amount, and `midpoint` averages toward zero. The
    /// division methods take a divisor guarded as for `/`. An operation that
    /// needs an operand more than once applies a Lean `fun` to the operands,
    /// which evaluates each once and keeps every specification name out of
    /// the scope of its binders.
    fn method(
        &self,
        name: &str,
        recv: &Expr,
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
                    format!("`.{name}()` takes {n} argument(s), but {} were given", args.len()),
                ))
            }
        };
        let ty = |t: IntTy| if math { Ty::Math } else { Ty::Int(t) };
        // Rust defines some methods only on unsigned, or only on signed,
        // integer types.
        let signedness = |t: IntTy, signed: bool| {
            if t.signed == signed {
                return Ok(());
            }
            let kind = if signed { "signed" } else { "unsigned" };
            Err(type_error(
                span,
                format!(
                    "`{name}` needs {} {kind} integer, found `{}`",
                    if signed { "a" } else { "an" },
                    t.rust_name()
                ),
            )
            .help(format!("Rust defines `{name}` only on {kind} integer types")))
        };
        let unsigned = |t: IntTy| signedness(t, false);
        let signed = |t: IntTy| signedness(t, true);
        if name != "math" && INTRINSICS.contains(&name) {
            arity(if name.ends_with("_neg") { 0 } else { 1 })?;
            let operands: Vec<Expr> = std::iter::once(recv).chain(args).cloned().collect();
            return self.call(name, &operands, span, math, facts);
        }
        match name {
            "min" | "max" => {
                arity(1)?;
                let operands = [recv.clone(), args[0].clone()];
                let (a, b, t) = self.int_pair(name, &operands, span, facts)?;
                let f = if name == "min" { MIN } else { MAX };
                Ok(Low::Int(format!("({f} {a} {b})"), ty(t)))
            }
            "clamp" => {
                arity(2)?;
                let (a, lo, t) =
                    self.int_pair(name, &[recv.clone(), args[0].clone()], span, facts)?;
                let hi = match self.lower(&args[1], false, facts)? {
                    Low::Int(hi, Ty::Int(u)) if u == t => hi,
                    low @ (Low::Lit(..) | Low::UntypedIf(..)) => {
                        let Low::Int(hi, _) = settle(low, Ty::Int(t))? else { unreachable!() };
                        hi
                    }
                    low => {
                        return Err(type_error(
                            args[1].span,
                            format!("expected `{}`, found {}", t.rust_name(), describe(&low)),
                        ));
                    }
                };
                let (Some(l), Some(h)) = (self.const_value(&args[0]), self.const_value(&args[1]))
                else {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_AMBIGUOUS_SPEC_ARITH",
                        span,
                        "`clamp` with bounds that are not constants is ambiguous: Rust panics when \
                         `min > max`",
                    )
                    .help(
                        "clamp to constant bounds, or write `x.max(lo).min(hi)`, which equals \
                         `x.clamp(lo, hi)` whenever `lo <= hi`",
                    ));
                };
                if !lit_le(l, h) {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_SPEC_LITERAL_RANGE",
                        span,
                        format!("`clamp` bounds `{l}` and `{h}` are out of order, so Rust panics"),
                    ));
                }
                Ok(Low::Int(format!("({MIN} ({MAX} {a} {lo}) {hi})"), ty(t)))
            }
            "is_power_of_two" => {
                arity(0)?;
                let (a, t) = self.int_operand(name, recv, facts)?;
                unsigned(t)?;
                let p = POWER_OF_TWO_BINDER;
                Ok(Low::Prop(Prop::pure(format!(
                    "(let {p} := {INT}.toNat {a}; 0 < {p} ∧ {p} &&& ({p} - 1) = 0)"
                ))))
            }
            // As in Rust, `a.is_multiple_of(0)` holds exactly when `a` is
            // `0`, which is `intTmod a 0 = 0`, since `intTmod a 0` is `a`.
            "is_multiple_of" => {
                arity(1)?;
                let (a, b, t) =
                    self.int_pair(name, &[recv.clone(), args[0].clone()], span, facts)?;
                unsigned(t)?;
                Ok(Low::Prop(Prop::pure(format!("({INT_TMOD} {a} {b} = 0)"))))
            }
            "div_ceil" => {
                arity(1)?;
                let (a, b, t) =
                    self.int_pair(name, &[recv.clone(), args[0].clone()], span, facts)?;
                unsigned(t)?;
                self.require_nonzero_divisor(name, &args[0], &b, facts)?;
                // The quotient of non-negative `n` by positive `d`, rounded
                // up, which fits in `t`.
                let term = apply_fun(
                    &["«n»", "«d»"],
                    INT,
                    &format!("{INT_TDIV} («n» + «d» - 1) «d»"),
                    &[a, b],
                );
                Ok(Low::Int(term, ty(t)))
            }
            "rotate_left" | "rotate_right" => {
                arity(1)?;
                let (a, t) = self.int_operand(name, recv, facts)?;
                // As in Rust, the amount is taken modulo the width.
                let n = self.u32_amount(name, &args[0], facts)?;
                // Rotate the `Nat` value of `a`'s bits: the bits shifted out
                // of one end come back in at the other.
                let (m, bits) = (modulus(t), t.bits);
                let (head, tail) =
                    if name == "rotate_left" { ("<<<", ">>>") } else { (">>>", "<<<") };
                let rotated = apply_fun(
                    &["«x»", "«k»"],
                    NAT,
                    &format!("(«x» {head} «k» ||| «x» {tail} ({bits} - «k»)) % {m}"),
                    &[
                        format!("({INT}.toNat ({INT_EMOD} {a} {m}))"),
                        format!("({INT}.toNat ({INT_EMOD} {n} {bits}))"),
                    ],
                );
                let value = format!("({INT}.ofNat {rotated})");
                Ok(Low::Int(if t.signed { wrap_into(&value, t) } else { value }, ty(t)))
            }
            "is_positive" | "is_negative" => {
                arity(0)?;
                let (a, t) = self.int_operand(name, recv, facts)?;
                signed(t)?;
                let zero = int_lit(IntLit::new(false, 0));
                Ok(Low::Prop(Prop::pure(if name == "is_positive" {
                    format!("({zero} < {a})")
                } else {
                    format!("({a} < {zero})")
                })))
            }
            "signum" => {
                arity(0)?;
                let (a, t) = self.int_operand(name, recv, facts)?;
                signed(t)?;
                let [one, zero, minus_one] = [(false, 1), (false, 0), (true, 1)]
                    .map(|(neg, mag)| int_lit(IntLit::new(neg, mag)));
                let term = apply_fun(
                    &["«x»"],
                    INT,
                    &format!(
                        "if {zero} < «x» then {one} else if «x» < {zero} then {minus_one} else {zero}"
                    ),
                    &[a],
                );
                Ok(Low::Int(term, ty(t)))
            }
            // The magnitude of a signed `a` fits in the unsigned type of its
            // width, and in `a`'s own type except at `MIN`.
            "unsigned_abs" | "saturating_abs" | "wrapping_abs" => {
                arity(0)?;
                let (a, t) = self.int_operand(name, recv, facts)?;
                signed(t)?;
                let abs = format!("({INT}.ofNat ({INT}.natAbs {a}))");
                let (term, result) = match name {
                    "unsigned_abs" => (abs, IntTy { signed: false, ..t }),
                    "saturating_abs" => {
                        let max = int_lit(IntLit::new(false, t.range().1));
                        (format!("({MIN} {abs} {max})"), t)
                    }
                    _ => (wrap_into(&abs, t), t),
                };
                Ok(Low::Int(term, ty(result)))
            }
            // A same-width bit cast, which is `a as T` for the type of the
            // other signedness.
            "cast_signed" | "cast_unsigned" => {
                arity(0)?;
                let (a, t) = self.int_operand(name, recv, facts)?;
                let to_signed = name == "cast_signed";
                signedness(t, !to_signed)?;
                let target = IntTy { signed: to_signed, ..t };
                Ok(Low::Int(wrap_into(&a, target), ty(target)))
            }
            // Division and remainder, truncating or Euclidean. Rust panics
            // on a zero divisor, so the divisor must be guarded as for `/`.
            // The `wrapping_` forms wrap the one quotient that overflows,
            // `MIN / -1`, back to `MIN`; the others exist only on unsigned
            // types, where no quotient overflows. No remainder overflows.
            "wrapping_div" | "wrapping_rem" | "wrapping_div_euclid" | "wrapping_rem_euclid"
            | "div_euclid" | "rem_euclid" => {
                arity(1)?;
                let (a, b, t) = self.int_pair(name, &[recv.clone(), args[0].clone()], span, facts)?;
                if !name.starts_with("wrapping_") {
                    unsigned(t)?;
                }
                self.require_nonzero_divisor(name, &args[0], &b, facts)?;
                let euclid = name.ends_with("_euclid");
                let term = if name.contains("rem") {
                    format!("({} {a} {b})", if euclid { INT_EMOD } else { INT_TMOD })
                } else {
                    // A Euclidean quotient differs from the truncated one only
                    // for a negative dividend, where the Euclidean remainder
                    // `intEmod` makes `n - r` an exact multiple of `d`.
                    let quotient = if euclid && t.signed {
                        apply_fun(
                            &["«n»", "«d»"],
                            INT,
                            &format!("{INT_TDIV} («n» - {INT_EMOD} «n» «d») «d»"),
                            &[a, b],
                        )
                    } else {
                        format!("({INT_TDIV} {a} {b})")
                    };
                    if t.signed { wrap_into(&quotient, t) } else { quotient }
                };
                Ok(Low::Int(term, ty(t)))
            }
            // Unlike `<<` and `>>`, these shift by any `u32` amount: one
            // that is not below the width shifts every bit out, leaving `0`,
            // or `-1` for a negative operand of a signed right shift.
            "unbounded_shl" | "unbounded_shr" => {
                arity(1)?;
                let (a, t) = self.int_operand(name, recv, facts)?;
                let n = self.u32_amount(name, &args[0], facts)?;
                let op = if name == "unbounded_shl" { BinOp::Shl } else { BinOp::Shr };
                let zero = int_lit(IntLit::new(false, 0));
                let shifted = shift_term(op, "«x»", &format!("({INT}.toNat «n»)"), t);
                let out = if matches!(op, BinOp::Shr) && t.signed {
                    format!("if «x» < {zero} then {} else {zero}", int_lit(IntLit::new(true, 1)))
                } else {
                    zero
                };
                let bits = int_lit(IntLit::new(false, u128::from(t.bits)));
                let term = apply_fun(
                    &["«x»", "«n»"],
                    INT,
                    &format!("if «n» < {bits} then {shifted} else {out}"),
                    &[a, n],
                );
                Ok(Low::Int(term, ty(t)))
            }
            // As in Rust, the average rounds toward zero; it lies between the
            // operands, so it is in their type.
            "midpoint" => {
                arity(1)?;
                let (a, b, t) =
                    self.int_pair(name, &[recv.clone(), args[0].clone()], span, facts)?;
                let two = int_lit(IntLit::new(false, 2));
                Ok(Low::Int(format!("({INT_TDIV} ({a} + {b}) {two})"), ty(t)))
            }
            // Rust's mixed-signedness arithmetic adds or subtracts an
            // operand of the receiver's width and the other signedness, and
            // wraps or saturates the exact result into the receiver's type.
            "wrapping_add_signed"
            | "wrapping_sub_signed"
            | "saturating_add_signed"
            | "saturating_sub_signed"
            | "wrapping_add_unsigned"
            | "wrapping_sub_unsigned"
            | "saturating_add_unsigned"
            | "saturating_sub_unsigned" => {
                arity(1)?;
                let (a, t) = self.int_operand(name, recv, facts)?;
                let operand_signed = !name.ends_with("_unsigned");
                signedness(t, !operand_signed)?;
                let u = IntTy { signed: operand_signed, ..t };
                let b = match self.lower(&args[0], false, facts)? {
                    Low::Int(b, Ty::Int(v)) if v == u => b,
                    low @ (Low::Lit(..) | Low::UntypedIf(..)) => {
                        let Low::Int(b, _) = settle(low, Ty::Int(u))? else { unreachable!() };
                        b
                    }
                    low => {
                        return Err(type_error(
                            args[0].span,
                            format!(
                                "`{name}` takes a `{}`, found {}",
                                u.rust_name(),
                                describe(&low)
                            ),
                        ));
                    }
                };
                let sym = if name.contains("_sub_") { "-" } else { "+" };
                let exact = format!("{a} {sym} {b}");
                let term = if name.starts_with("wrapping_") {
                    wrap_into(&format!("({exact})"), t)
                } else {
                    saturate(&exact, t)
                };
                Ok(Low::Int(term, ty(t)))
            }
            _ => Err(Diagnostic::new(
                "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
                span,
                format!("`.{name}()` is not a supported integer method"),
            )
            .help(
                "the integer methods are `min`, `max`, `clamp`, `is_power_of_two`, \
                 `is_multiple_of`, `div_ceil`, `rotate_left`, `rotate_right`, `is_positive`, \
                 `is_negative`, `signum`, `unsigned_abs`, `saturating_abs`, `wrapping_abs`, \
                 `cast_signed`, `cast_unsigned`, `unbounded_shl`, `unbounded_shr`, \
                 `midpoint`, `wrapping_div`, `wrapping_rem`, `wrapping_div_euclid`, \
                 `wrapping_rem_euclid`, `div_euclid`, `rem_euclid`, `abs_diff`, the mixed-signedness \
                 `wrapping_add_signed` and its kin, and the `wrapping_*`, `saturating_*`, and \
                 `no_overflow_*` intrinsics",
            )),
        }
    }

    /// Lowers `e as t`. Rust's integer casts keep the value of `e` when it
    /// fits in `t` and otherwise reduce it into `t`'s range modulo `2^bits`,
    /// so the result depends only on that value; `e` may therefore also be
    /// mathematical, as in `math(a + b) as u8`. As with the bitwise
    /// operators, `e` keeps its machine type even inside `math`, where the
    /// result is mathematical. A `bool` casts to `1` or `0` through an `if`,
    /// so it must be decidable, and an untyped integer has Rust's default
    /// type, `i32`.
    fn cast(
        &self,
        inner: &Expr,
        t: IntTy,
        math: bool,
        facts: &mut Vec<String>,
    ) -> Result<Low, Diagnostic> {
        let term = match self.lower(inner, false, facts)? {
            Low::Prop(p) => {
                if let Some((span, why)) = p.undecidable {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_UNDECIDABLE_SPEC_IF",
                        span,
                        format!(
                            "casting a `bool` to an integer needs a decidable `bool`, but {why}"
                        ),
                    )
                    .help(
                        "cast a `bool` that tests integers or `bool` arguments and return values",
                    ));
                }
                let (one, zero) = (IntLit::new(false, 1), IntLit::new(false, 0));
                format!("(if {} then {} else {})", p.term, int_lit(one), int_lit(zero))
            }
            Low::Int(a, Ty::Int(s)) if fits(s, t) => a,
            Low::Int(a, _) => wrap_into(&a, t),
            Low::Lit(v, span) => {
                check_range(v, I32, span)?;
                if v.in_range(t) {
                    int_lit(v)
                } else {
                    wrap_into(&int_lit(v), t)
                }
            }
            untyped @ Low::UntypedIf(..) => match settle(untyped, Ty::Int(I32))? {
                Low::Int(a, _) if fits(I32, t) => a,
                Low::Int(a, _) => wrap_into(&a, t),
                _ => unreachable!("`settle` gives an untyped `if` a type"),
            },
            Low::Unit(_) => {
                return Err(type_error(inner.span, "cannot cast `()` to an integer"));
            }
        };
        Ok(Low::Int(term, if math { Ty::Math } else { Ty::Int(t) }))
    }

    /// The `max_steps` step count of `low`, the value of `what` (an
    /// operator or call) in a step count, which must be an unsigned machine
    /// integer.
    fn machine_step_count(&self, low: Low, span: Span, what: &str) -> Result<String, Diagnostic> {
        match low {
            Low::Int(term, Ty::Int(t)) if !t.signed => Ok(format!("({INT}.toNat {term})")),
            Low::Int(_, Ty::Int(t)) => Err(type_error(
                span,
                format!(
                    "`max_steps` requires a non-negative integer, but this {what} has signed \
                     type `{}`",
                    t.rust_name()
                ),
            )),
            other => Err(type_error(
                span,
                format!(
                    "expected a non-negative integer for `max_steps`, found {}",
                    describe(&other)
                ),
            )),
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
        Self::unify_pair(a, b, l, r, math)
    }

    /// Unifies `a` and `b`, the lowered operands `l` and `r` of an operator
    /// whose operand types must agree, letting an untyped literal take its
    /// type from the other side.
    fn unify_pair(
        a: Low,
        b: Low,
        l: &Expr,
        r: &Expr,
        math: bool,
    ) -> Result<(Low, Low), Diagnostic> {
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
        let family = ["wrapping_", "no_overflow_", "saturating_"]
            .into_iter()
            .find_map(|f| name.strip_prefix(f).map(|op| (f, op)));
        if let Some((family @ "wrapping_", op @ ("shl" | "shr"))) = family {
            arity(2)?;
            let (a, t) = self.int_operand(name, &args[0], facts)?;
            // As in Rust, the amount is a `u32`, taken modulo the bit width.
            let n = match self.lower(&args[1], false, facts)? {
                Low::Int(n, Ty::Int(u)) if u == U32 => n,
                low @ Low::Lit(..) => {
                    let Low::Int(n, _) = settle(low, Ty::Int(U32))? else { unreachable!() };
                    n
                }
                low => {
                    return Err(type_error(
                        args[1].span,
                        format!("`{family}{op}` shifts by a `u32`, found {}", describe(&low)),
                    ));
                }
            };
            let amount = format!("({INT}.toNat ({INT_EMOD} {n} {}))", t.bits);
            let bin = if op == "shl" { BinOp::Shl } else { BinOp::Shr };
            let term = shift_term(bin, &a, &amount, t);
            return Ok(Low::Int(term, if math { Ty::Math } else { Ty::Int(t) }));
        }
        if let Some((family, op)) = family {
            // These intrinsics take machine-typed operands even inside
            // `math`, since their meaning depends on the type's width. `t` is
            // the operands' type, and `exact` is the mathematical result of
            // the operation.
            let (t, exact) = match op {
                "add" | "sub" | "mul" => {
                    arity(2)?;
                    let (a, b, t) = self.int_pair(name, args, span, facts)?;
                    let sym = match op {
                        "add" => "+",
                        "sub" => "-",
                        _ => "*",
                    };
                    (t, format!("{a} {sym} {b}"))
                }
                "neg" => {
                    arity(1)?;
                    let (a, t) = self.int_operand(name, &args[0], facts)?;
                    if family == "saturating_" && !t.signed {
                        return Err(type_error(
                            span,
                            format!(
                                "`saturating_neg` needs a signed integer, found `{}`",
                                t.rust_name()
                            ),
                        )
                        .help("Rust defines `saturating_neg` only on signed integer types"));
                    }
                    (t, format!("{INT_NEG} {a}"))
                }
                _ => return Err(unknown_fn(name, span, self.helpers)),
            };
            let m = modulus(t);
            let h = half_modulus(t);
            let ty = if math { Ty::Math } else { Ty::Int(t) };
            return Ok(match family {
                "wrapping_" => Low::Int(
                    if t.signed {
                        format!("({INT_EMOD} ({exact} + {h}) {m} - {h})")
                    } else {
                        format!("({INT_EMOD} ({exact}) {m})")
                    },
                    ty,
                ),
                "no_overflow_" => {
                    let (lo, hi) = if t.signed {
                        (format!("({INT_NEG} {h})"), h.to_string())
                    } else {
                        (format!("(0 : {INT})"), m)
                    };
                    Low::Prop(Prop::pure(format!("({lo} ≤ {exact} ∧ {exact} < {hi})")))
                }
                _ => Low::Int(saturate(&exact, t), ty),
            });
        }
        if name == "abs_diff" {
            arity(2)?;
            let (a, b, t) = self.int_pair(name, args, span, facts)?;
            // `abs_diff` returns the unsigned type of the operands' width,
            // whose range holds the distance between any two of their values.
            let unsigned = IntTy { signed: false, ..t };
            let term = format!("({INT}.ofNat ({INT}.natAbs ({a} - {b})))");
            return Ok(Low::Int(term, if math { Ty::Math } else { Ty::Int(unsigned) }));
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

    /// Lowers the two operands of intrinsic `name`, which must have one
    /// fixed-width integer type, returning their terms and that type.
    fn int_pair(
        &self,
        name: &str,
        args: &[Expr],
        span: Span,
        facts: &mut Vec<String>,
    ) -> Result<(String, String, IntTy), Diagnostic> {
        match self.lower_pair(&args[0], &args[1], false, facts)? {
            (Low::Int(a, Ty::Int(t)), Low::Int(b, Ty::Int(_))) => Ok((a, b, t)),
            _ => Err(type_error(
                span,
                format!("`{name}` needs two operands of one fixed-width integer type"),
            )),
        }
    }

    /// Lowers the operand of unary intrinsic `name`, which must have a
    /// fixed-width integer type, returning its term and that type.
    fn int_operand(
        &self,
        name: &str,
        arg: &Expr,
        facts: &mut Vec<String>,
    ) -> Result<(String, IntTy), Diagnostic> {
        match self.lower(arg, false, facts)? {
            Low::Int(a, Ty::Int(t)) => Ok((a, t)),
            low @ (Low::Lit(..) | Low::UntypedIf(..)) => Err(Diagnostic::new(
                "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED",
                arg.span,
                format!(
                    "the type of the operand of `{name}` cannot be inferred from {}",
                    describe(&low)
                ),
            )
            .help("add a suffix such as `5i8`")),
            low => Err(type_error(
                arg.span,
                format!("`{name}` needs a fixed-width integer operand, found {}", describe(&low)),
            )),
        }
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

fn describe(l: &Low) -> String {
    match l {
        Low::Prop(_) => "`bool`".into(),
        Low::Int(_, t) => format!("`{}`", t.describe()),
        Low::Unit(_) => "`()`".into(),
        Low::Lit(..) => "an integer literal".into(),
        Low::UntypedIf(..) => "an `if` of integer literals".into(),
    }
}

/// `low` with the Lean `let` prefix `prefix`, which binds `binder`,
/// around it. A fact that names `binder` does not leave the `let`, where
/// `binder` is out of scope.
fn wrap_low(prefix: &str, binder: &str, low: Low) -> Low {
    if prefix.is_empty() {
        return low;
    }
    match low {
        Low::Prop(p) => {
            let outside = |fs: Vec<String>| -> Vec<String> {
                fs.into_iter().filter(|f| !f.contains(binder)).collect()
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
/// associated integer constant (possibly negated, parenthesized, or wrapped
/// in `math`).
fn const_int_lit(e: &Expr) -> Option<IntLit> {
    match &e.kind {
        ExprKind::Int(v, _) => Some(IntLit::new(false, *v)),
        ExprKind::IntConst(t, c) => Some(int_const(*t, *c).0),
        ExprKind::Paren(inner) | ExprKind::Math(inner) => const_int_lit(inner),
        ExprKind::Unary(UnOp::Neg, inner) => const_int_lit(inner).map(IntLit::negate),
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
        ExprKind::Method(_, recv, args) => {
            mentions(recv, name) || args.iter().any(|a| mentions(a, name))
        }
        ExprKind::Unary(_, x)
        | ExprKind::Cast(x, _)
        | ExprKind::Math(x)
        | ExprKind::Old(x)
        | ExprKind::Paren(x) => mentions(x, name),
        ExprKind::Binary(_, a, b) => mentions(a, name) || mentions(b, name),
        ExprKind::If(c, t, f) => mentions(c, name) || mentions(t, name) || mentions(f, name),
        ExprKind::Let(b, body) => mentions(&b.init, name) || mentions(body, name),
        ExprKind::Match(s, arms) => {
            mentions(s, name) || arms.iter().any(|a| mentions(&a.body, name))
        }
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
        ExprKind::Method(_, recv, args) => {
            calls_in(recv, out);
            args.iter().for_each(|a| calls_in(a, out));
        }
        ExprKind::Unary(_, x)
        | ExprKind::Cast(x, _)
        | ExprKind::Math(x)
        | ExprKind::Old(x)
        | ExprKind::Paren(x) => calls_in(x, out),
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
        ExprKind::Match(s, arms) => {
            calls_in(s, out);
            arms.iter().for_each(|a| calls_in(&a.body, out));
        }
        _ => {}
    }
}
