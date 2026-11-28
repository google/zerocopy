// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Lowering from the structured Clang AST in a `RawCppBundle` to the
//! basic-block CFG of `Trusted.CppAst`.
//!
//! Invariants of the output:
//!
//! * Local `0` is the return slot, locals `1..=K` are the `K` parameters, and
//!   user locals and compiler temporaries follow.
//! * All control flow (`if`, loops, `switch`, `goto`, `&&`, `||`, `?:`, calls)
//!   is explicit in block terminators; `CppExpr` is side-effect free.
//! * Every full-expression has passed the SSENF gate (`crate::ssenf`), so the
//!   single evaluation order chosen here is observationally equivalent to
//!   every order C11 permits. Expressions returned by `rvalue` read places
//!   lazily (when the consuming statement executes); the gate guarantees no
//!   intervening write to those places, and values that a later sequenced
//!   effect could change (`x++`, `++x` and assignments used as values, call
//!   results, `&&`/`||`/`?:` results) are materialized into fresh temporaries.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::{
    error::{malformed, unsupported, LowerError, Result},
    ir::{
        BinOp, Block, Body, Expr, FieldDecl, LangPolicy, LocalDecl, Place, Program, Proj,
        RecordDef, Sign, Signature, SignedOverflowMode, Stmt, Terminator, Ty, UnOp, Width,
    },
    raw::{
        ArithOp, BinaryOp, CastKind, MethodKind, RawBundle, RawCtorInit, RawExpr, RawExprKind,
        RawFunction, RawLangPolicy, RawPassing, RawStmt, RawType, UnaryOp,
    },
    ssenf::{
        children, collect_escaped, collect_written_vars_expr, collect_written_vars_stmt,
        glvalue_root_var, Ssenf,
    },
};

#[derive(Debug, Clone, Default)]
pub struct Options {
    /// Symbol of the entry function. Defaults to the bundle's first function
    /// (the extractor lists `--entry` roots first).
    pub entry: Option<String>,
}

// -------------------------------------------------------------------------
// Policy, types, ABI
// -------------------------------------------------------------------------

/// Enforces the admission policy on the sealed `LangOptions`: Rung-0 C11, or
/// Rung-1 C++ (`-std=c++17`/`c++20`) without exceptions.
pub fn check_policy(lp: &RawLangPolicy) -> Result<LangPolicy> {
    let reject = |detail: String| Err(LowerError::UnsupportedLangPolicy { detail });
    if lp.exceptions_enabled {
        return reject(
            "exceptions are enabled (-fexceptions); Rungs 0 and 1 require -fno-exceptions".into(),
        );
    }
    if lp.fast_math {
        return reject("fast-math is enabled".into());
    }
    if lp.is_cplusplus
        && !matches!(lp.lang_standard.as_str(), "c++17" | "c++20" | "gnu++17" | "gnu++20")
    {
        return reject(format!(
            "C++ dialect `{}` (Rung 1 admits C++17 and C++20)",
            lp.lang_standard
        ));
    }
    if lp.pointer_width_bits != 64 {
        return reject(format!("pointer width {} (Rung 0 requires 64)", lp.pointer_width_bits));
    }
    let signed_overflow = match lp.signed_overflow.as_str() {
        "iso_ub" => SignedOverflowMode::IsoUB,
        "wrapv" => SignedOverflowMode::Wrapv,
        other => return reject(format!("signed overflow behavior `{other}`")),
    };
    Ok(LangPolicy {
        pointer_width_bits: lp.pointer_width_bits,
        char_is_signed: lp.char_is_signed,
        strict_aliasing: lp.strict_aliasing,
        signed_overflow,
        exceptions_off: true,
    })
}

pub fn lower_ty(t: &RawType, used: &mut BTreeSet<String>) -> Result<Ty> {
    Ok(match t {
        RawType::Void => Ty::Void,
        RawType::Bool => Ty::Bool,
        RawType::Int { bits, signed, is_char_like } => match Width::from_bits(*bits) {
            Some(w) => {
                Ty::Int(w, if *signed { Sign::Signed } else { Sign::Unsigned }, *is_char_like)
            }
            None => return unsupported(format!("{bits}-bit integer type")),
        },
        RawType::Ptr { pointee, is_const, is_restrict, may_alias } => {
            Ty::Ptr(Box::new(lower_ty(pointee, used)?), *is_const, *is_restrict, *may_alias)
        }
        RawType::Array { elem, len } => Ty::Array(Box::new(lower_ty(elem, used)?), *len),
        RawType::Record { id } => {
            used.insert(id.clone());
            Ty::Record(id.clone())
        }
        // C++ references are non-null pointers; every use dereferences them.
        RawType::Ref { pointee, is_const, may_alias, .. } => {
            Ty::Ptr(Box::new(lower_ty(pointee, used)?), *is_const, false, *may_alias)
        }
        // `std::nullptr_t` has the size and alignment of `void *`; reads of
        // it never access memory (see `FnLower::cast`).
        RawType::NullPtrT => Ty::Ptr(Box::new(Ty::Void), false, false, false),
        RawType::Unsupported { desc } => return unsupported(format!("type `{desc}`")),
    })
}

fn ptr_to(ty: &Ty) -> Ty {
    Ty::Ptr(Box::new(ty.clone()), false, false, false)
}

/// The extractor marks destructors it cannot name with `<...>`.
fn checked_dtor(sym: &str) -> Result<String> {
    if sym.starts_with('<') {
        return unsupported(format!("non-trivial destructor `{sym}` cannot be called"));
    }
    Ok(sym.to_owned())
}

/// The destructor of the temporary that `e` initializes, if it is bound.
fn bound_dtor(e: &RawExpr) -> Option<&str> {
    match &e.kind {
        RawExprKind::Paren { sub } | RawExprKind::ExprWithCleanups { sub } => bound_dtor(sub),
        RawExprKind::Cast { kind: CastKind::Noop | CastKind::ConstructorConversion, sub }
            if !e.is_lvalue =>
        {
            bound_dtor(sub)
        }
        RawExprKind::BindTemporary { dtor_symbol, .. } => Some(dtor_symbol),
        _ => None,
    }
}

fn passing_matches(ty: &Ty, p: &RawPassing) -> bool {
    match (ty, p) {
        (Ty::Void, RawPassing::Ignore) => true,
        (Ty::Int(w, ..), RawPassing::DirectInt { bits }) => u64::from(w.bits()) == *bits,
        (Ty::Int(w, ..), RawPassing::ExtendInt { bits }) => {
            u64::from(w.bits()) == *bits && w.bits() < 32
        }
        (Ty::Bool, RawPassing::ExtendInt { bits: 1 } | RawPassing::DirectInt { bits: 1 }) => true,
        (Ty::Ptr(..), RawPassing::DirectPtr) => true,
        _ => false,
    }
}

/// Cross-checks Clang CodeGen's ABI classification against the declared
/// signature: scalars must be passed directly in registers. C admits no
/// by-value aggregates; C++ admits by-value records only if they are
/// trivially copyable (`not_copyable` lists the others), because a call
/// copies the callee's `_0` into the caller's destination instead of
/// constructing the result in place.
pub fn check_abi(
    f: &RawFunction,
    params: &[Ty],
    ret: &Ty,
    cxx: bool,
    not_copyable: &HashSet<String>,
) -> Result<()> {
    let mismatch = |detail: String| Err(LowerError::AbiMismatch { detail });
    let w = &f.abi_witness;
    if w.cc != "c" {
        return mismatch(format!("`{}`: calling convention `{}`", f.symbol, w.cc));
    }
    for (i, t) in params.iter().chain(std::iter::once(ret)).enumerate() {
        // C++ passes trivially copyable records (spans, views, PODs) by value;
        // their CodeGen classification (coerced registers or memory) does not
        // change the by-value semantics, so it is not cross-checked.
        if let (true, Ty::Record(id)) = (cxx, t) {
            if not_copyable.contains(id) {
                return unsupported(format!(
                    "`{}`: by-value record `{id}` that is not trivially copyable or has an address-dependent constructor",
                    f.symbol
                ));
            }
            continue;
        }
        if matches!(t, Ty::Record(_) | Ty::Array(..)) {
            return unsupported(format!(
                "`{}`: by-value aggregate in signature position {i}",
                f.symbol
            ));
        }
    }
    if w.param_passing.len() != params.len() {
        return mismatch(format!(
            "`{}`: {} parameters but {} ABI classifications",
            f.symbol,
            params.len(),
            w.param_passing.len()
        ));
    }
    for (i, (t, p)) in params.iter().zip(&w.param_passing).enumerate() {
        if !passing_matches(t, p) && !(cxx && matches!(t, Ty::Record(_))) {
            return mismatch(format!(
                "`{}`: parameter {i} of type {t:?} classified as {p:?}",
                f.symbol
            ));
        }
    }
    if !passing_matches(ret, &w.return_passing) && !(cxx && matches!(ret, Ty::Record(_))) {
        return mismatch(format!(
            "`{}`: return type {ret:?} classified as {:?}",
            f.symbol, w.return_passing
        ));
    }
    Ok(())
}

fn int_fits(v: i128, w: Width, s: Sign) -> bool {
    let bits = w.bits();
    match (s, bits) {
        (_, 128) => s == Sign::Signed || v >= 0,
        (Sign::Signed, b) => {
            let lim = 1i128 << (b - 1);
            v >= -lim && v < lim
        }
        (Sign::Unsigned, b) => v >= 0 && v < (1i128 << b),
    }
}

/// Inserts the C conversion from `from` to `to` (integer, bool, or identity).
fn convert(e: Expr, from: &Ty, to: &Ty) -> Result<Expr> {
    if from == to {
        return Ok(e);
    }
    match (from, to) {
        (Ty::Int(fw, fs, _), Ty::Int(tw, ts, tc)) => {
            Ok(Expr::IntCast(*fw, *fs, *tw, *ts, *tc, Box::new(e)))
        }
        (Ty::Int(..), Ty::Bool) => Ok(Expr::IntToBool(Box::new(e))),
        (Ty::Bool, Ty::Int(w, s, _)) => Ok(Expr::BoolToInt(*w, *s, Box::new(e))),
        _ => unsupported(format!("implicit conversion from {from:?} to {to:?}")),
    }
}

fn expect_same(what: &str, got: &Ty, want: &Ty) -> Result<()> {
    if got == want {
        Ok(())
    } else {
        malformed(format!("{what}: operand type {got:?} differs from expected {want:?}"))
    }
}

fn arith_binop(a: ArithOp) -> BinOp {
    match a {
        ArithOp::Add => BinOp::Add,
        ArithOp::Sub => BinOp::Sub,
        ArithOp::Mul => BinOp::Mul,
        ArithOp::Div => BinOp::Div,
        ArithOp::Rem => BinOp::Rem,
        ArithOp::Shl => BinOp::Shl,
        ArithOp::Shr => BinOp::Shr,
        ArithOp::BitAnd => BinOp::BitAnd,
        ArithOp::BitOr => BinOp::BitOr,
        ArithOp::BitXor => BinOp::BitXor,
    }
}

/// Pure integer constant expressions (as accepted for the ignored second
/// argument of `__builtin_expect`).
fn is_pure_int_const(e: &RawExpr) -> bool {
    match &e.kind {
        RawExprKind::IntLit { .. } | RawExprKind::SizeofOrAlignof { .. } => true,
        RawExprKind::Paren { sub } => is_pure_int_const(sub),
        RawExprKind::Cast { kind: CastKind::IntegralCast | CastKind::Noop, sub } => {
            is_pure_int_const(sub)
        }
        RawExprKind::Unary { op: UnaryOp::Minus | UnaryOp::Plus | UnaryOp::BitNot, sub } => {
            is_pure_int_const(sub)
        }
        _ => false,
    }
}

fn strip_parens(e: &RawExpr) -> &RawExpr {
    match &e.kind {
        RawExprKind::Paren { sub } => strip_parens(sub),
        _ => e,
    }
}

/// `p - n` as `p + (-n)`: the offset is widened to `int64_t` and negated.
/// An unsigned 64-bit or a 128-bit offset is rejected, since widening could
/// change its value (`(size_t)-1` would become `-1`) and so turn an
/// out-of-bounds subtraction into an in-bounds one. Negating `INT64_MIN`
/// overflows (undefined under ISO rules), and under `-fwrapv` yields an
/// offset of the same magnitude, which no allocation can accommodate in
/// either direction.
fn negated_offset(n: Expr, nt: &Ty) -> Result<Expr> {
    match nt {
        Ty::Int(Width::W128, ..) | Ty::Int(Width::W64, Sign::Unsigned, _) => {
            unsupported(format!("pointer subtraction of a {nt:?} offset"))
        }
        _ => Ok(Expr::Unary(UnOp::Neg, Ty::I64, Box::new(convert(n, nt, &Ty::I64)?))),
    }
}

/// A null pointer constant with no side effects: `nullptr`, a pure integer
/// constant, or such a constant under no-op or null conversions.
fn is_null_pointer_constant(e: &RawExpr) -> bool {
    match &e.kind {
        RawExprKind::NullptrLit => true,
        RawExprKind::Paren { sub }
        | RawExprKind::Cast { kind: CastKind::Noop | CastKind::NullToPointer, sub } => {
            is_null_pointer_constant(sub)
        }
        _ => is_pure_int_const(e),
    }
}

/// The comparison operator of a relational or equality expression.
fn comparison_op(op: BinaryOp) -> Option<BinOp> {
    Some(match op {
        BinaryOp::Eq => BinOp::Eq,
        BinaryOp::Ne => BinOp::Ne,
        BinaryOp::Lt => BinOp::Lt,
        BinaryOp::Le => BinOp::Le,
        BinaryOp::Gt => BinOp::Gt,
        BinaryOp::Ge => BinOp::Ge,
        _ => return None,
    })
}

/// Initializers a function-local `static` may have: literals combined by
/// pure operators and conversions, possibly in (nested) initializer lists.
/// The extractor already requires a constant initializer; this re-checks
/// that the lowered initializer reads no object and calls nothing.
fn is_constant_init(e: &RawExpr) -> bool {
    match &e.kind {
        RawExprKind::IntLit { .. }
        | RawExprKind::BoolLit { .. }
        | RawExprKind::SizeofOrAlignof { .. }
        | RawExprKind::NullptrLit
        | RawExprKind::ImplicitValueInit => true,
        RawExprKind::Paren { sub } => is_constant_init(sub),
        RawExprKind::Cast {
            kind:
                CastKind::IntegralCast
                | CastKind::IntToBool
                | CastKind::BoolToInt
                | CastKind::NullToPointer
                | CastKind::Noop,
            sub,
        } => !e.is_lvalue && is_constant_init(sub),
        RawExprKind::Unary {
            op: UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot | UnaryOp::LogNot,
            sub,
        } => is_constant_init(sub),
        RawExprKind::Binary { op, lhs, rhs, .. } => {
            !matches!(op, BinaryOp::Assign | BinaryOp::CompoundAssign(_) | BinaryOp::Comma)
                && is_constant_init(lhs)
                && is_constant_init(rhs)
        }
        RawExprKind::Conditional { cond, then_expr, else_expr } => {
            is_constant_init(cond) && is_constant_init(then_expr) && is_constant_init(else_expr)
        }
        RawExprKind::InitList { inits, array_filler, .. } => {
            inits.iter().all(is_constant_init)
                && array_filler.as_deref().is_none_or(is_constant_init)
        }
        _ => false,
    }
}

/// Function-local `static const` declarations of a body, in source order.
fn collect_static_consts<'r>(s: &'r RawStmt, out: &mut Vec<&'r RawStmt>) {
    match s {
        RawStmt::Compound(v) => {
            for s in v {
                collect_static_consts(s, out);
            }
        }
        RawStmt::Decl { is_static_const: true, .. } => out.push(s),
        RawStmt::If { then_branch, else_branch, .. } => {
            collect_static_consts(then_branch, out);
            if let Some(b) = else_branch {
                collect_static_consts(b, out);
            }
        }
        RawStmt::For { init, body, .. } => {
            if let Some(i) = init {
                collect_static_consts(i, out);
            }
            collect_static_consts(body, out);
        }
        RawStmt::While { body, .. }
        | RawStmt::DoWhile { body, .. }
        | RawStmt::Switch { body, .. }
        | RawStmt::Case { sub: body, .. }
        | RawStmt::Default { sub: body }
        | RawStmt::Label { sub: body, .. } => collect_static_consts(body, out),
        RawStmt::Decl { .. }
        | RawStmt::Expr(_)
        | RawStmt::Break
        | RawStmt::Continue
        | RawStmt::Goto { .. }
        | RawStmt::Return(_)
        | RawStmt::Null
        | RawStmt::Unsupported { .. } => {}
    }
}

fn raw_type_has_mutable(ty: &RawType, mutable_records: &HashSet<String>) -> bool {
    match ty {
        RawType::Record { id } => mutable_records.contains(id),
        RawType::Array { elem, .. } => raw_type_has_mutable(elem, mutable_records),
        _ => false,
    }
}

fn raw_type_record_ids(ty: &RawType, out: &mut Vec<String>) {
    match ty {
        RawType::Record { id } => out.push(id.clone()),
        RawType::Array { elem, .. } => raw_type_record_ids(elem, out),
        _ => {}
    }
}

fn contains_cxx_this(e: &RawExpr) -> bool {
    matches!(e.kind, RawExprKind::CxxThis) || children(e).into_iter().any(contains_cxx_this)
}

/// Whether `e` inside a constructor may observe `this` as an address (rather
/// than reading or writing direct `this->field` subobjects by value).
fn expr_observes_this(e: &RawExpr) -> bool {
    match &e.kind {
        RawExprKind::CxxThis => true,
        RawExprKind::Member { base, is_arrow: true, .. }
            if matches!(strip_parens(base).kind, RawExprKind::CxxThis) =>
        {
            false
        }
        RawExprKind::ArraySubscript { base, idx } => {
            if let RawExprKind::Cast { kind: CastKind::ArrayToPointerDecay, sub } =
                &strip_parens(base).kind
            {
                return expr_observes_this(sub) || expr_observes_this(idx);
            }
            expr_observes_this(base) || expr_observes_this(idx)
        }
        RawExprKind::Unary { op: UnaryOp::AddrOf, sub }
        | RawExprKind::Cast { kind: CastKind::ArrayToPointerDecay, sub } => {
            contains_cxx_this(sub) || expr_observes_this(sub)
        }
        RawExprKind::Call {
            is_indirect,
            implicit_object,
            implicit_object_is_ptr,
            args,
            param_is_ref,
            ..
        } => {
            if *is_indirect && args.iter().any(contains_cxx_this) {
                return true;
            }
            if let Some(o) = implicit_object {
                if !*implicit_object_is_ptr && contains_cxx_this(o) {
                    return true;
                }
                if *implicit_object_is_ptr && expr_observes_this(o) {
                    return true;
                }
            }
            for (i, a) in args.iter().enumerate() {
                if param_is_ref.get(i).copied().unwrap_or(false) && contains_cxx_this(a) {
                    return true;
                }
                if expr_observes_this(a) {
                    return true;
                }
            }
            false
        }
        RawExprKind::Construct { args, param_is_ref, .. } => {
            for (i, a) in args.iter().enumerate() {
                if param_is_ref.get(i).copied().unwrap_or(false) && contains_cxx_this(a) {
                    return true;
                }
                if expr_observes_this(a) {
                    return true;
                }
            }
            false
        }
        _ => children(e).into_iter().any(expr_observes_this),
    }
}

fn stmt_observes_this(s: &RawStmt) -> bool {
    match s {
        RawStmt::Compound(v) => v.iter().any(stmt_observes_this),
        RawStmt::Decl { init: Some(i), is_ref, .. } => {
            (*is_ref && contains_cxx_this(i)) || expr_observes_this(i)
        }
        RawStmt::Expr(x) | RawStmt::Return(Some(x)) => expr_observes_this(x),
        RawStmt::If { cond, then_branch, else_branch } => {
            expr_observes_this(cond)
                || stmt_observes_this(then_branch)
                || else_branch.as_deref().is_some_and(stmt_observes_this)
        }
        RawStmt::While { cond, body } | RawStmt::DoWhile { body, cond } => {
            expr_observes_this(cond) || stmt_observes_this(body)
        }
        RawStmt::For { init, cond, inc, body } => {
            init.as_deref().is_some_and(stmt_observes_this)
                || cond.as_ref().is_some_and(expr_observes_this)
                || inc.as_ref().is_some_and(expr_observes_this)
                || stmt_observes_this(body)
        }
        RawStmt::Switch { cond, body } => expr_observes_this(cond) || stmt_observes_this(body),
        RawStmt::Case { sub, .. } | RawStmt::Default { sub } | RawStmt::Label { sub, .. } => {
            stmt_observes_this(sub)
        }
        RawStmt::Decl { init: None, .. }
        | RawStmt::Return(None)
        | RawStmt::Break
        | RawStmt::Continue
        | RawStmt::Goto { .. }
        | RawStmt::Null
        | RawStmt::Unsupported { .. } => false,
    }
}

/// Whether a constructor in `bundle.functions` may observe `this` (or has no
/// body to inspect), making by-value copies unfaithful to C++17/C++20
/// guaranteed copy elision.
fn ctor_observes_this(f: &RawFunction) -> bool {
    if f.method_kind != MethodKind::Ctor || f.is_trivial {
        return false;
    }
    let Some(body) = &f.body else {
        return true;
    };
    for ci in &f.ctor_inits {
        match ci {
            RawCtorInit::Field { init, .. } => {
                if expr_observes_this(init) {
                    return true;
                }
            }
            RawCtorInit::Base { offset_bytes: 0, init, .. } => {
                if expr_observes_this(init) {
                    return true;
                }
            }
            _ => return true,
        }
    }
    stmt_observes_this(body)
}

// -------------------------------------------------------------------------
// Function lowering
// -------------------------------------------------------------------------

struct FnSig {
    params: Vec<Ty>,
    ret: Ty,
    is_variadic: bool,
    abi_cxx: bool,
    param_non_null: Vec<bool>,
}

struct Shared<'a> {
    /// The translation unit is C++ (Rung 1): scopes run destructors and
    /// C++-only constructs are admitted.
    cxx: bool,
    /// Non-trivial destructor of each C++ record, by record id.
    record_dtors: &'a HashMap<String, Option<String>>,
    /// Records that contain a `mutable` field in themselves or a subobject.
    mutable_records: &'a HashSet<String>,
    records: &'a HashMap<String, Result<(RecordDef, BTreeSet<String>)>>,
    sigs: &'a HashMap<String, FnSig>,
    /// Why a function's signature could not be lowered; reported only if
    /// the function is lowered or called.
    sig_errors: &'a HashMap<String, LowerError>,
    used_records: BTreeSet<String>,
    /// Synthesized external load stubs for scalar globals, by stub symbol.
    global_stubs: BTreeMap<String, Ty>,
}

impl Shared<'_> {
    fn sig(&self, sym: &str) -> Result<&FnSig> {
        match (self.sigs.get(sym), self.sig_errors.get(sym)) {
            (Some(s), _) => Ok(s),
            (None, Some(e)) => Err(e.clone()),
            (None, None) => malformed(format!("callee `{sym}` is not declared in the bundle")),
        }
    }
}

/// Prefix of the synthesized external callee that models reading a global.
pub const GLOBAL_LOAD_STUB_PREFIX: &str = "anneal.global_load.";

struct Targets {
    brk: usize,
    cont: Option<usize>,
    /// Number of enclosing scopes outside the loop or switch; a jump to
    /// `brk`/`cont` ends the lifetimes of the scopes above it.
    depth: usize,
}

struct SwitchCtx {
    blocks: Vec<usize>,
    labels: Vec<Option<i128>>,
    next: usize,
    /// Number of scopes open outside the `switch` body.
    depth: usize,
}

/// A `goto` whose target is resolved once every label is known. It jumps to
/// `block`, which `finish` fills with the `storageDead`s of the scopes the
/// jump leaves and a jump to the label.
struct PendingGoto {
    block: usize,
    label: String,
    /// Open scopes at the `goto` (outermost first), with their live locals.
    scopes: Vec<(usize, Vec<usize>)>,
}

struct FnLower<'s, 'a> {
    shared: &'s mut Shared<'a>,
    symbol: String,
    ret_ty: Ty,
    num_params: usize,
    locals: Vec<LocalDecl>,
    var_map: HashMap<u32, usize>,
    blocks: Vec<(Vec<Stmt>, Option<Terminator>)>,
    cur: usize,
    targets: Vec<Targets>,
    switches: Vec<SwitchCtx>,
    labels: HashMap<String, usize>,
    defined_labels: HashSet<String>,
    /// Open scopes at each label (outermost first), with how many locals
    /// each had declared before the label.
    label_scopes: HashMap<String, Vec<(usize, usize)>>,
    pending_gotos: Vec<PendingGoto>,
    /// A unique id for each entry of `scopes`.
    scope_ids: Vec<usize>,
    next_scope_id: usize,
    escaped: HashSet<u32>,
    written_vars: HashSet<u32>,
    top_level_vars: HashSet<u32>,
    temp_counter: usize,
    /// Locals of each open scope in declaration order, with their
    /// non-trivial destructors (always `None` in C).
    scopes: Vec<Vec<(usize, Option<String>)>>,
    /// C++ temporaries of the current full-expression.
    fe_temps: Vec<(usize, Option<String>)>,
    /// Dominating entry block of the current full-expression.
    fe_entry_bb: Option<usize>,
    /// Nesting depth of conditionally evaluated operands (`&&`, `||`, `?:`).
    cond_depth: usize,
    /// True while lowering a branch/switch controlling expression.
    in_cond: bool,
    has_this: bool,
    ret_is_ref: bool,
    /// Destructors only: member and base destructor calls that follow the
    /// body on every exit.
    dtor_epilogue: Vec<(Expr, String)>,
    abi_cxx: bool,
    param_non_null: Vec<bool>,
}

/// Whether initializing an object from `e` (as `FnLower::init_into` does)
/// calls a non-trivial constructor on the object or one of its subobjects,
/// which receives its address as `this` and may store it anywhere.
fn init_constructs_in_place(e: &RawExpr) -> bool {
    match &e.kind {
        RawExprKind::Construct { is_trivial, .. } => !*is_trivial,
        RawExprKind::Paren { sub }
        | RawExprKind::ExprWithCleanups { sub }
        | RawExprKind::BindTemporary { sub, .. } => init_constructs_in_place(sub),
        RawExprKind::Cast { kind: CastKind::Noop | CastKind::ConstructorConversion, sub }
            if !e.is_lvalue =>
        {
            init_constructs_in_place(sub)
        }
        RawExprKind::CompoundLiteral { init, is_file_scope: false } if !e.is_lvalue => {
            init_constructs_in_place(init)
        }
        RawExprKind::InitList { inits, array_filler, .. } => {
            inits.iter().any(init_constructs_in_place)
                || array_filler.as_deref().is_some_and(init_constructs_in_place)
        }
        _ => false,
    }
}

fn collect_escaped_stmt(s: &RawStmt, out: &mut HashSet<u32>) {
    let mut e = |x: &RawExpr| collect_escaped(x, out);
    match s {
        RawStmt::Compound(v) => {
            for s in v {
                collect_escaped_stmt(s, out);
            }
        }
        RawStmt::Decl { var_id, init, is_ref, dtor_symbol, .. } => {
            if let Some(i) = init {
                e(i);
                // C++: a reference aliases its referent, and a constructor
                // receives the object's address.
                if *is_ref {
                    if let Some(v) = glvalue_root_var(i) {
                        out.insert(v);
                    }
                }
                if init_constructs_in_place(i) {
                    out.insert(*var_id);
                }
            }
            if dtor_symbol.is_some() {
                out.insert(*var_id);
            }
        }
        RawStmt::Expr(x) => e(x),
        RawStmt::If { cond, then_branch, else_branch } => {
            e(cond);
            collect_escaped_stmt(then_branch, out);
            if let Some(b) = else_branch {
                collect_escaped_stmt(b, out);
            }
        }
        RawStmt::While { cond, body } | RawStmt::DoWhile { body, cond } => {
            e(cond);
            collect_escaped_stmt(body, out);
        }
        RawStmt::For { init, cond, inc, body } => {
            if let Some(c) = cond {
                e(c);
            }
            if let Some(i) = inc {
                e(i);
            }
            if let Some(i) = init {
                collect_escaped_stmt(i, out);
            }
            collect_escaped_stmt(body, out);
        }
        RawStmt::Switch { cond, body } => {
            e(cond);
            collect_escaped_stmt(body, out);
        }
        RawStmt::Case { sub, .. } | RawStmt::Default { sub } | RawStmt::Label { sub, .. } => {
            collect_escaped_stmt(sub, out)
        }
        RawStmt::Return(Some(x)) => e(x),
        RawStmt::Return(None)
        | RawStmt::Break
        | RawStmt::Continue
        | RawStmt::Goto { .. }
        | RawStmt::Null
        | RawStmt::Unsupported { .. } => {}
    }
}

/// Case labels of a `switch` body in source order (not descending into nested
/// switches); `None` denotes `default`.
fn collect_case_labels(s: &RawStmt, out: &mut Vec<Option<i128>>) {
    match s {
        RawStmt::Compound(v) => {
            for s in v {
                collect_case_labels(s, out);
            }
        }
        RawStmt::Case { value, sub } => {
            out.push(Some(*value));
            collect_case_labels(sub, out);
        }
        RawStmt::Default { sub } => {
            out.push(None);
            collect_case_labels(sub, out);
        }
        RawStmt::If { then_branch, else_branch, .. } => {
            collect_case_labels(then_branch, out);
            if let Some(b) = else_branch {
                collect_case_labels(b, out);
            }
        }
        RawStmt::While { body, .. } | RawStmt::DoWhile { body, .. } | RawStmt::For { body, .. } => {
            collect_case_labels(body, out)
        }
        RawStmt::Label { sub, .. } => collect_case_labels(sub, out),
        RawStmt::Switch { .. }
        | RawStmt::Decl { .. }
        | RawStmt::Expr(_)
        | RawStmt::Break
        | RawStmt::Continue
        | RawStmt::Goto { .. }
        | RawStmt::Return(_)
        | RawStmt::Null
        | RawStmt::Unsupported { .. } => {}
    }
}

impl<'s, 'a> FnLower<'s, 'a> {
    fn ty(&mut self, t: &RawType) -> Result<Ty> {
        lower_ty(t, &mut self.shared.used_records)
    }

    fn new_block(&mut self) -> usize {
        self.blocks.push((Vec::new(), None));
        self.blocks.len() - 1
    }

    fn emit(&mut self, s: Stmt) {
        self.blocks[self.cur].0.push(s);
    }

    fn terminate(&mut self, t: Terminator) -> Result<()> {
        let slot = &mut self.blocks[self.cur].1;
        if slot.is_some() {
            return malformed(format!("internal: block bb{} terminated twice", self.cur));
        }
        *slot = Some(t);
        Ok(())
    }

    /// Terminates the current block with a jump and continues in a fresh,
    /// unreachable block (pruned later).
    fn jump(&mut self, t: Terminator) -> Result<()> {
        self.terminate(t)?;
        self.cur = self.new_block();
        Ok(())
    }

    fn new_temp(&mut self, ty: Ty) -> usize {
        self.temp_counter += 1;
        self.locals.push(LocalDecl {
            ty,
            is_param: false,
            debug_name: format!("tmp{}", self.temp_counter),
        });
        self.locals.len() - 1
    }

    fn materialize(&mut self, ty: Ty, e: Expr) -> usize {
        let t = self.new_temp(ty.clone());
        self.emit(Stmt::Assign(Place::local(t), ty, e));
        t
    }

    fn record_field(&mut self, rid: &str, idx: u32, name: &str) -> Result<Ty> {
        let rec = match self.shared.records.get(rid) {
            None => return malformed(format!("unknown record `{rid}`")),
            Some(Err(e)) => return Err(e.clone()),
            Some(Ok((r, _))) => r,
        };
        let f = match rec.fields.get(idx as usize) {
            None => return malformed(format!("record `{rid}` has no field #{idx}")),
            Some(f) => f,
        };
        if f.name != name {
            return malformed(format!("record `{rid}` field #{idx} is `{}`, not `{name}`", f.name));
        }
        if f.bit_width.is_some() {
            return unsupported(format!("bit-field access `{rid}.{name}`"));
        }
        self.shared.used_records.insert(rid.to_owned());
        Ok(f.ty.clone())
    }

    fn ssenf(&self, e: &RawExpr) -> Result<()> {
        Ssenf::new(&self.escaped).check_full_expr(e).map(|_| ())
    }

    // --------------------- C++ objects and lifetimes ---------------------

    fn record_def(&mut self, rid: &str) -> Result<RecordDef> {
        match self.shared.records.get(rid) {
            None => malformed(format!("unknown record `{rid}`")),
            Some(Err(e)) => Err(e.clone()),
            Some(Ok((r, _))) => {
                self.shared.used_records.insert(rid.to_owned());
                Ok(r.clone())
            }
        }
    }

    fn record_dtor(&self, rid: &str) -> Result<Option<String>> {
        match self.shared.record_dtors.get(rid) {
            Some(Some(d)) => Ok(Some(checked_dtor(d)?)),
            _ => Ok(None),
        }
    }

    /// The place of field `idx` of the record object at `base`; bit-fields
    /// become a final `Bitfield` projection.
    fn field_place(&mut self, base: Place, rid: &str, idx: u32) -> Result<(Place, Ty)> {
        let rec = self.record_def(rid)?;
        let f = match rec.fields.get(idx as usize) {
            Some(f) => f.clone(),
            None => return malformed(format!("record `{rid}` has no field #{idx}")),
        };
        match f.bit_width {
            None => Ok((base.with(Proj::Field(rid.to_owned(), idx, f.ty.clone())), f.ty)),
            Some(w) => match f.ty {
                Ty::Int(_, sign, _) => Ok((
                    base.with(Proj::Bitfield(
                        rid.to_owned(),
                        idx,
                        f.offset_bits,
                        w,
                        sign == Sign::Signed,
                    )),
                    f.ty,
                )),
                _ => unsupported(format!("non-integer bit-field `{rid}.{}`", f.name)),
            },
        }
    }

    /// Size in bits of `ty` if every bit belongs to some scalar value (no
    /// padding), so zero-filling it first and then initializing each member
    /// is exactly C++ aggregate initialization.
    fn dense_bits(&mut self, ty: &Ty) -> Option<u64> {
        match ty {
            Ty::Void => None,
            Ty::Bool => Some(8),
            Ty::Int(w, ..) => Some(u64::from(w.bits())),
            Ty::Ptr(..) => Some(64),
            Ty::Array(e, n) => self.dense_bits(e).map(|b| b * n),
            Ty::Record(rid) => {
                let rec = self.record_def(rid).ok()?;
                if rec.is_union {
                    return None;
                }
                let mut spans = Vec::with_capacity(rec.fields.len());
                for f in &rec.fields {
                    let len = match f.bit_width {
                        Some(_) if f.name.is_empty() => continue,
                        Some(w) => w,
                        None => self.dense_bits(&f.ty)?,
                    };
                    spans.push((f.offset_bits, f.offset_bits + len));
                }
                spans.sort_unstable();
                let mut end = 0;
                for (start, stop) in spans {
                    if start != end {
                        return None;
                    }
                    end = stop;
                }
                (end == rec.size_bytes * 8).then_some(end)
            }
        }
    }

    fn emit_dtor_call(&mut self, this_arg: Expr, dtor: &str) -> Result<()> {
        let next = self.new_block();
        self.terminate(Terminator::Call(dtor.to_owned(), vec![this_arg], None, next))?;
        self.cur = next;
        Ok(())
    }

    /// Ends the lifetimes of `entries` in reverse declaration order: each
    /// object's destructor (if any) runs, then its storage dies.
    fn cleanup(&mut self, entries: Vec<(usize, Option<String>)>) -> Result<()> {
        for (l, dtor) in entries.into_iter().rev() {
            if let Some(d) = dtor {
                let ty = self.locals[l].ty.clone();
                self.emit_dtor_call(Expr::AddrOf(Place::local(l), ptr_to(&ty)), &d)?;
            }
            self.emit(Stmt::StorageDead(l));
        }
        Ok(())
    }

    /// Cleans up (without closing) every open scope at index `depth` or
    /// deeper, innermost first.
    fn cleanup_scopes_from(&mut self, depth: usize) -> Result<()> {
        let scopes: Vec<_> = self.scopes[depth..].iter().rev().cloned().collect();
        for s in scopes {
            self.cleanup(s)?;
        }
        Ok(())
    }

    /// Starts lowering a full-expression, recording its dominating entry block
    /// and running the SSENF gate.
    fn begin_full_expr(&mut self, e: &RawExpr) -> Result<()> {
        self.fe_entry_bb = Some(self.cur);
        self.ssenf(e)
    }

    /// End of a full-expression: its temporaries are destroyed in reverse
    /// order of construction.
    fn end_full_expr(&mut self) -> Result<()> {
        self.fe_entry_bb = None;
        let temps = std::mem::take(&mut self.fe_temps);
        self.cleanup(temps)
    }

    /// A condition ends in a branch, so its temporaries could not be cleaned
    /// up on a single path; Rung 1 rejects them.
    fn no_cond_temps(&mut self) -> Result<()> {
        self.fe_entry_bb = None;
        if self.fe_temps.is_empty() {
            Ok(())
        } else {
            unsupported("C++ temporary in a condition")
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
        self.scope_ids.push(self.next_scope_id);
        self.next_scope_id += 1;
    }

    fn pop_scope(&mut self) -> Vec<(usize, Option<String>)> {
        self.scope_ids.pop();
        self.scopes.pop().expect("scope pushed by push_scope")
    }

    fn register(&mut self, l: usize, dtor: Option<String>) {
        if let Some(s) = self.scopes.last_mut() {
            s.push((l, dtor));
        }
    }

    fn epilogue(&mut self) -> Result<()> {
        for (arg, d) in self.dtor_epilogue.clone() {
            self.emit_dtor_call(arg, &d)?;
        }
        Ok(())
    }

    fn this_ty(&self) -> Result<Ty> {
        if self.has_this {
            Ok(self.locals[1].ty.clone())
        } else {
            malformed("`this` outside a non-static member function")
        }
    }

    /// Creates a temporary initialized by the prvalue `sub`. Unless its
    /// lifetime is extended to the enclosing scope, it dies at the end of the
    /// full-expression.
    fn materialize_temp(&mut self, sub: &RawExpr, lifetime_extended: bool) -> Result<(Place, Ty)> {
        let ty = self.ty(&sub.ty)?;
        let dtor = match bound_dtor(sub) {
            Some(d) => Some(checked_dtor(d)?),
            None => match &ty {
                Ty::Record(rid) => self.record_dtor(rid)?,
                _ => None,
            },
        };
        if self.cond_depth > 0 && (dtor.is_some() || lifetime_extended) {
            return unsupported(if lifetime_extended {
                "conditionally evaluated lifetime-extended C++ temporary"
            } else {
                "conditionally evaluated C++ temporary with a destructor"
            });
        }
        let t = self.new_temp(ty.clone());
        if self.cond_depth > 0 {
            let entry_bb = self.fe_entry_bb.ok_or_else(|| LowerError::Malformed {
                detail: "internal: conditional temporary outside a full-expression".into(),
            })?;
            self.blocks[entry_bb].0.push(Stmt::StorageLive(t));
        } else {
            self.emit(Stmt::StorageLive(t));
        }
        self.init_into(Place::local(t), &ty, sub)?;
        if lifetime_extended {
            self.register(t, dtor);
        } else {
            self.fe_temps.push((t, dtor));
        }
        Ok((Place::local(t), ty))
    }

    /// A prvalue of class type used as a value: a temporary that dies at the
    /// end of the full-expression.
    fn temp_value(&mut self, e: &RawExpr, ty: &Ty) -> Result<Expr> {
        let (p, _) = self.materialize_temp(e, false)?;
        Ok(Expr::ReadPlace(p, ty.clone()))
    }

    /// Initializes the object at `place` (of type `ty`) from `e`.
    fn init_into(&mut self, place: Place, ty: &Ty, e: &RawExpr) -> Result<()> {
        match &e.kind {
            // A bound temporary that directly initializes an object is elided
            // into it (C++17 guaranteed copy elision); the object's own
            // lifetime owns the destructor.
            RawExprKind::Paren { sub }
            | RawExprKind::ExprWithCleanups { sub }
            | RawExprKind::BindTemporary { sub, .. } => self.init_into(place, ty, sub),
            RawExprKind::Cast { kind: CastKind::Noop | CastKind::ConstructorConversion, sub }
                if !e.is_lvalue && matches!(ty, Ty::Record(_)) =>
            {
                self.init_into(place, ty, sub)
            }
            RawExprKind::Construct { .. } => self.construct_into(place, ty, e),
            RawExprKind::InitList { .. } => self.init_list_into(place, ty, e),
            RawExprKind::CompoundLiteral { init, is_file_scope: false } if !e.is_lvalue => {
                self.init_into(place, ty, init)
            }
            RawExprKind::ImplicitValueInit => {
                self.emit(Stmt::ZeroInit(place, ty.clone()));
                Ok(())
            }
            _ => {
                let v = self.rvalue(e)?;
                expect_same("initializer", &self.ty(&e.ty)?, ty)?;
                self.emit(Stmt::Assign(place, ty.clone(), v));
                Ok(())
            }
        }
    }

    fn construct_into(&mut self, place: Place, ty: &Ty, e: &RawExpr) -> Result<()> {
        let RawExprKind::Construct {
            ctor_symbol,
            args,
            param_is_ref,
            is_trivial,
            is_copy_or_move,
            is_default,
            zero_init,
            is_array_construct,
            is_complete,
            ..
        } = &e.kind
        else {
            return malformed("internal: construct_into on a non-construct");
        };
        if *is_array_construct || !*is_complete {
            return unsupported(format!(
                "constructor `{ctor_symbol}` for an array element, base, or delegation"
            ));
        }
        if *is_trivial {
            if args.is_empty() || *is_default {
                if *zero_init {
                    self.emit(Stmt::ZeroInit(place, ty.clone()));
                }
                return Ok(());
            }
            if *is_copy_or_move && args.len() == 1 {
                let (sp, sty) = self.place(&args[0])?;
                expect_same("trivial copy", &sty, ty)?;
                self.emit(Stmt::Assign(place, ty.clone(), Expr::ReadPlace(sp, sty)));
                return Ok(());
            }
            return unsupported(format!("trivial constructor `{ctor_symbol}` with arguments"));
        }
        if *zero_init {
            // Value-initialization zero-fills before the constructor runs.
            self.emit(Stmt::ZeroInit(place.clone(), ty.clone()));
        }
        let this_ty = match self.shared.sig(ctor_symbol)?.params.first() {
            Some(t) => t.clone(),
            None => return malformed(format!("constructor `{ctor_symbol}` without `this`")),
        };
        let mut vals = vec![Expr::AddrOf(place, this_ty)];
        vals.extend(self.call_args(ctor_symbol, args, param_is_ref, 1)?);
        let next = self.new_block();
        self.terminate(Terminator::Call(ctor_symbol.clone(), vals, None, next))?;
        self.cur = next;
        Ok(())
    }

    fn is_escaped_local(&self, local: usize) -> bool {
        self.var_map.iter().any(|(vid, &lid)| lid == local && self.escaped.contains(vid))
    }

    fn expr_mentions_local(&self, e: &RawExpr, local: usize) -> bool {
        if let RawExprKind::VarRef { var_id, is_param, param_idx, .. } = &e.kind {
            let mapped = if *is_param {
                param_idx.map(|i| (i as usize) + 1)
            } else {
                self.var_map.get(var_id).copied()
            };
            if mapped == Some(local) {
                return true;
            }
        }
        children(e).into_iter().any(|c| self.expr_mentions_local(c, local))
    }

    /// True if evaluating `inits` might read `place` before `place` is
    /// initialized (e.g. `struct S s = { s.y };` or `int a[3] = { 1, a[2] };`).
    fn can_aliased_read_occur(&self, place: &Place, inits: &[RawExpr]) -> bool {
        if inits.iter().all(|i| matches!(i.kind, RawExprKind::ImplicitValueInit)) {
            return false;
        }
        if inits.iter().any(|i| self.expr_mentions_local(i, place.base)) {
            return true;
        }
        if !place.projs.is_empty() || self.is_escaped_local(place.base) {
            return inits.iter().any(|i| {
                Ssenf::new(&self.escaped)
                    .check_full_expr(i)
                    .map_or(true, |fp| fp.mem_reads || fp.calls > 0)
            });
        }
        false
    }

    fn init_list_into(&mut self, place: Place, ty: &Ty, e: &RawExpr) -> Result<()> {
        let RawExprKind::InitList { inits, is_transparent, has_union_field, array_filler } =
            &e.kind
        else {
            return malformed("internal: init_list_into on a non-initializer-list");
        };
        if *is_transparent && inits.len() == 1 {
            return self.init_into(place, ty, &inits[0]);
        }
        let rid = match ty {
            Ty::Record(r) => r.clone(),
            Ty::Array(elem, len) if !*has_union_field => {
                return self.array_init_into(place, ty, elem, *len, inits, array_filler.as_deref())
            }
            _ => return unsupported(format!("initializer list for {ty:?}")),
        };
        if *has_union_field || array_filler.is_some() {
            return unsupported(format!("initializer list for `{rid}` (union or array filler)"));
        };
        let rec = self.record_def(&rid)?;
        if rec.is_union {
            return unsupported(format!("initializer list for union `{rid}`"));
        }
        // Unnamed bit-fields are padding and take no initializer.
        let named: Vec<u32> = (0..rec.fields.len() as u32)
            .filter(|i| {
                let f = &rec.fields[*i as usize];
                !(f.name.is_empty() && f.bit_width.is_some())
            })
            .collect();
        if named.len() != inits.len() {
            return malformed(format!(
                "initializer list for `{rid}` has {} elements for {} members",
                inits.len(),
                named.len()
            ));
        }
        let any_implicit = inits.iter().any(|i| matches!(i.kind, RawExprKind::ImplicitValueInit));
        let aliased = self.can_aliased_read_occur(&place, inits);
        let is_dense = self.dense_bits(ty) == Some(rec.size_bytes * 8);
        if any_implicit && aliased {
            if !is_dense {
                return unsupported("self-referential partial initializer on padded record");
            }
            if rec.fields.iter().any(|f| f.bit_width.is_some()) {
                return unsupported("self-referential partial initializer on bit-field record");
            }
        }
        let dense = any_implicit && !aliased && is_dense;
        if dense {
            self.emit(Stmt::ZeroInit(place.clone(), ty.clone()));
        }
        for (idx, init) in named.into_iter().zip(inits) {
            if dense && matches!(init.kind, RawExprKind::ImplicitValueInit) {
                continue;
            }
            let (fp, fty) = self.field_place(place.clone(), &rid, idx)?;
            if matches!(fp.projs.last(), Some(Proj::Bitfield(..))) {
                let v = self.rvalue(init)?;
                expect_same("bit-field initializer", &self.ty(&init.ty)?, &fty)?;
                self.emit(Stmt::Assign(fp, fty, v));
            } else {
                self.init_into(fp, &fty, init)?;
            }
        }
        Ok(())
    }

    /// Initializes the array at `place` element by element in index order
    /// (any order is equivalent: the SSENF gate rejects initializer lists
    /// whose elements conflict). Elements after `inits` are
    /// value-initialized (C11 6.7.9p21, C++ [dcl.init.aggr]p5), which zeroes
    /// their padding too.
    fn array_init_into(
        &mut self,
        place: Place,
        ty: &Ty,
        elem: &Ty,
        len: u64,
        inits: &[RawExpr],
        filler: Option<&RawExpr>,
    ) -> Result<()> {
        let explicit = inits.len() as u64;
        if explicit > len {
            return malformed(format!("{explicit} initializers for an array of {len}"));
        }
        let fill = explicit < len;
        match filler {
            Some(f) if fill && matches!(f.kind, RawExprKind::ImplicitValueInit) => {}
            Some(_) if fill => return unsupported("array filler other than value-initialization"),
            None if fill => return malformed("short array initializer list without a filler"),
            _ => {}
        }
        // Without padding or potential self-reads, zero-filling first and then
        // storing each explicit element is the required initialization.
        let aliased = self.can_aliased_read_occur(&place, inits);
        let dense = fill && !aliased && self.dense_bits(ty).is_some();
        if dense {
            self.emit(Stmt::ZeroInit(place.clone(), ty.clone()));
        }
        let idx = self.new_temp(Ty::I64);
        let at = |fl: &mut Self, i: u64| {
            let k = i128::from(i);
            fl.emit(Stmt::Assign(
                Place::local(idx),
                Ty::I64,
                Expr::ConstInt(Width::W64, Sign::Signed, false, k),
            ));
            place.clone().with(Proj::Index(elem.clone(), idx))
        };
        for (i, init) in (0u64..).zip(inits) {
            if dense && matches!(init.kind, RawExprKind::ImplicitValueInit) {
                continue;
            }
            let ep = at(self, i);
            self.init_into(ep, elem, init)?;
        }
        if fill && !dense {
            for i in explicit..len {
                let ep = at(self, i);
                self.emit(Stmt::ZeroInit(ep, elem.clone()));
            }
        }
        Ok(())
    }

    /// Hoists a function-local `static const` object to the start of the
    /// body. It is constant-initialized and never written (const, and its
    /// address never escapes), so a per-call copy initialized on entry is
    /// observationally equivalent to the single static object.
    fn hoist_static_const(&mut self, s: &RawStmt) -> Result<()> {
        let RawStmt::Decl { var_id, name, ty, init, is_ref, .. } = s else {
            return malformed("internal: hoist_static_const on a non-declaration");
        };
        if *is_ref {
            return unsupported(format!("static local reference `{name}`"));
        }
        if raw_type_has_mutable(ty, self.shared.mutable_records) {
            return unsupported(format!("static local `{name}` has a `mutable` subobject"));
        }
        if self.written_vars.contains(var_id) {
            return unsupported(format!("static local `{name}` is modified"));
        }
        if self.escaped.contains(var_id) {
            return unsupported(format!("address of static local `{name}` escapes"));
        }
        let init = match init {
            Some(i) if is_constant_init(i) => i,
            _ => {
                return unsupported(format!("static local `{name}` without a constant initializer"))
            }
        };
        let lt = self.ty(ty)?;
        if lt == Ty::Void {
            return malformed(format!("local `{name}` of void type"));
        }
        self.locals.push(LocalDecl { ty: lt.clone(), is_param: false, debug_name: name.clone() });
        let l = self.locals.len() - 1;
        if self.var_map.insert(*var_id, l).is_some() {
            return malformed(format!("local #{var_id} declared twice"));
        }
        self.emit(Stmt::StorageLive(l));
        self.begin_full_expr(init)?;
        self.init_into(Place::local(l), &lt, init)?;
        self.end_full_expr()
    }

    /// Lowers call arguments for parameters `offset..` of `sym`, binding
    /// reference parameters to the addresses of their glvalue arguments.
    fn call_args(
        &mut self,
        sym: &str,
        args: &[RawExpr],
        param_is_ref: &[bool],
        offset: usize,
    ) -> Result<Vec<Expr>> {
        let (params, is_variadic) = {
            let s = self.shared.sig(sym)?;
            (s.params.clone(), s.is_variadic)
        };
        if is_variadic {
            return unsupported(format!("call to variadic function `{sym}`"));
        }
        if params.len() != args.len() + offset {
            return malformed(format!(
                "call to `{sym}` with {} arguments, expected {}",
                args.len() + offset,
                params.len()
            ));
        }
        let mut vals = Vec::with_capacity(args.len());
        for (i, (a, pt)) in args.iter().zip(&params[offset..]).enumerate() {
            if param_is_ref.get(i).copied().unwrap_or(false) {
                let (p, aty) = self.place(a)?;
                if pt.pointee() != Some(&aty) {
                    return malformed(format!(
                        "reference argument of type {aty:?} bound to parameter {pt:?}"
                    ));
                }
                vals.push(Expr::AddrOf(p, pt.clone()));
            } else {
                let v = self.rvalue(a)?;
                expect_same("call argument", &self.ty(&a.ty)?, pt)?;
                vals.push(v);
            }
        }
        Ok(vals)
    }

    fn ctor_inits(&mut self, inits: &[RawCtorInit]) -> Result<()> {
        let this_ty = self.this_ty()?;
        for ci in inits {
            match ci {
                RawCtorInit::Field { record_id, field_idx, init } => {
                    self.begin_full_expr(init)?;
                    let base = Place::local(1).with(Proj::Deref);
                    let (fp, fty) = self.field_place(base, record_id, *field_idx)?;
                    if matches!(fp.projs.last(), Some(Proj::Bitfield(..))) {
                        let v = self.rvalue(init)?;
                        expect_same("bit-field initializer", &self.ty(&init.ty)?, &fty)?;
                        self.emit(Stmt::Assign(fp, fty, v));
                    } else {
                        self.init_into(fp, &fty, init)?;
                    }
                    self.end_full_expr()?;
                }
                RawCtorInit::Base { record_id, offset_bytes, init } => {
                    if *offset_bytes != 0 {
                        return unsupported(format!("base `{record_id}` at a non-zero offset"));
                    }
                    self.begin_full_expr(init)?;
                    let bty = Ty::Record(record_id.clone());
                    let addr = Expr::PtrCast(
                        ptr_to(&bty),
                        Box::new(Expr::ReadPlace(Place::local(1), this_ty.clone())),
                    );
                    let (bp, _) = self.place_of_ptr(addr, &ptr_to(&bty))?;
                    self.init_into(bp, &bty, init)?;
                    self.end_full_expr()?;
                }
                RawCtorInit::Unsupported { desc } => {
                    return unsupported(format!("constructor initializer: {desc}"))
                }
            }
        }
        Ok(())
    }

    /// Assignment used as an lvalue (C++): performs the store and designates
    /// the assigned object.
    fn assign_place(&mut self, lhs: &RawExpr, rhs: &RawExpr) -> Result<(Place, Ty)> {
        let (p, pty) = self.place(lhs)?;
        if matches!(pty, Ty::Array(..) | Ty::Void) {
            return unsupported(format!("assignment to {pty:?}"));
        }
        let v = self.rvalue(rhs)?;
        expect_same("assignment", &self.ty(&rhs.ty)?, &pty)?;
        self.emit(Stmt::Assign(p.clone(), pty.clone(), v));
        Ok((p, pty))
    }

    // ----------------------------- places -----------------------------

    fn place_of_ptr(&mut self, pv: Expr, pty: &Ty) -> Result<(Place, Ty)> {
        let pointee = match pty.pointee() {
            Some(Ty::Void) | None => {
                return unsupported(format!("dereference of non-object pointer {pty:?}"))
            }
            Some(p) => p.clone(),
        };
        let place = match pv {
            Expr::ReadPlace(p, _) => p.with(Proj::Deref),
            other => Place::local(self.materialize(pty.clone(), other)).with(Proj::Deref),
        };
        Ok((place, pointee))
    }

    fn local_of(&mut self, v: Expr, ty: &Ty) -> usize {
        match v {
            Expr::ReadPlace(Place { base, projs }, _) if projs.is_empty() => base,
            other => self.materialize(ty.clone(), other),
        }
    }

    fn var_local(&mut self, var_id: u32, is_param: bool, param_idx: Option<u32>) -> Result<usize> {
        if is_param {
            let idx = match param_idx {
                Some(i) if (i as usize) < self.num_params => i as usize,
                _ => {
                    return malformed(format!("parameter reference #{var_id} without valid index"))
                }
            };
            let local = idx + 1;
            match self.var_map.insert(var_id, local) {
                Some(prev) if prev != local => {
                    malformed(format!("variable #{var_id} maps to two parameters"))
                }
                _ => Ok(local),
            }
        } else {
            match self.var_map.get(&var_id) {
                Some(l) => Ok(*l),
                None => malformed(format!("reference to undeclared local #{var_id}")),
            }
        }
    }

    fn place(&mut self, e: &RawExpr) -> Result<(Place, Ty)> {
        match &e.kind {
            RawExprKind::VarRef { var_id, is_param, param_idx, is_ref_binding: false } => {
                let l = self.var_local(*var_id, *is_param, *param_idx)?;
                Ok((Place::local(l), self.locals[l].ty.clone()))
            }
            RawExprKind::VarRef { var_id, is_param, param_idx, is_ref_binding: true } => {
                let l = self.var_local(*var_id, *is_param, *param_idx)?;
                let rty = self.locals[l].ty.clone();
                match rty.pointee() {
                    Some(p) => Ok((Place::local(l).with(Proj::Deref), p.clone())),
                    None => malformed(format!("reference variable #{var_id} of type {rty:?}")),
                }
            }
            RawExprKind::Paren { sub } => self.place(sub),
            RawExprKind::Cast { kind: CastKind::Noop, sub } if e.is_lvalue => self.place(sub),
            RawExprKind::Cast { kind: CastKind::DerivedToBase { offset_bytes }, sub }
                if e.is_lvalue =>
            {
                if *offset_bytes != 0 {
                    return unsupported("base subobject at a non-zero offset");
                }
                let (p, dty) = self.place(sub)?;
                let bty = self.ty(&e.ty)?;
                let addr = Expr::PtrCast(ptr_to(&bty), Box::new(Expr::AddrOf(p, ptr_to(&dty))));
                self.place_of_ptr(addr, &ptr_to(&bty))
            }
            RawExprKind::ExprWithCleanups { sub } => self.place(sub),
            RawExprKind::MaterializeTemporary { sub, lifetime_extended } => {
                self.materialize_temp(sub, *lifetime_extended)
            }
            RawExprKind::Call {
                callee_symbol: Some(sym),
                returns_ref: true,
                trivial_assign,
                ..
            } => {
                let rty = if *trivial_assign {
                    ptr_to(&self.ty(&e.ty)?)
                } else {
                    self.shared.sig(sym)?.ret.clone()
                };
                match self.call(e, true)? {
                    Some(v) => self.place_of_ptr(v, &rty),
                    None => malformed("reference-returning call without a result"),
                }
            }
            RawExprKind::Binary { op: BinaryOp::Assign, lhs, rhs, .. } if self.shared.cxx => {
                self.assign_place(lhs, rhs)
            }
            RawExprKind::Unary { op: UnaryOp::Deref, sub } => {
                let pty = self.ty(&sub.ty)?;
                let pv = self.rvalue(sub)?;
                self.place_of_ptr(pv, &pty)
            }
            RawExprKind::ArraySubscript { base, idx } => {
                let ity = self.ty(&idx.ty)?;
                if ity.int_parts().is_none() {
                    return unsupported(format!("array index of type {ity:?}"));
                }
                if let RawExprKind::Cast { kind: CastKind::ArrayToPointerDecay, sub } =
                    &strip_parens(base).kind
                {
                    let (ap, aty) = self.place(sub)?;
                    let elem = match aty {
                        Ty::Array(elem, _) => *elem,
                        other => return malformed(format!("array decay of {other:?}")),
                    };
                    let iv = self.rvalue(idx)?;
                    let il = self.local_of(iv, &ity);
                    return Ok((ap.with(Proj::Index(elem.clone(), il)), elem));
                }
                let bty = self.ty(&base.ty)?;
                let elem = match bty.pointee() {
                    Some(Ty::Void) | None => return unsupported(format!("subscript of {bty:?}")),
                    Some(p) => p.clone(),
                };
                let bv = self.rvalue(base)?;
                let iv = self.rvalue(idx)?;
                let addr = match iv {
                    Expr::ConstInt(_, _, _, 0) => bv,
                    iv => Expr::PtrAdd(elem, bty.clone(), Box::new(bv), Box::new(iv)),
                };
                self.place_of_ptr(addr, &bty)
            }
            RawExprKind::Member {
                base,
                is_arrow,
                field_name,
                record_id,
                field_idx,
                is_bitfield,
            } => {
                let fty = if *is_bitfield {
                    match self.record_def(record_id)?.fields.get(*field_idx as usize) {
                        Some(f) if &f.name == field_name => f.ty.clone(),
                        _ => {
                            return malformed(format!(
                                "record `{record_id}` has no bit-field `{field_name}`"
                            ))
                        }
                    }
                } else {
                    self.record_field(record_id, *field_idx, field_name)?
                };
                let bp = if *is_arrow {
                    let pty = self.ty(&base.ty)?;
                    match pty.pointee() {
                        Some(Ty::Record(r)) if r == record_id => {}
                        _ => return malformed(format!("`->{field_name}` on {pty:?}")),
                    }
                    let pv = self.rvalue(base)?;
                    self.place_of_ptr(pv, &pty)?.0
                } else {
                    let (bp, bty) = self.place(base)?;
                    if bty != Ty::Record(record_id.clone()) {
                        return malformed(format!("`.{field_name}` on {bty:?}"));
                    }
                    bp
                };
                if *is_bitfield {
                    return self.field_place(bp, record_id, *field_idx);
                }
                Ok((bp.with(Proj::Field(record_id.clone(), *field_idx, fty.clone())), fty))
            }
            RawExprKind::GlobalRef { symbol } => {
                unsupported(format!("address of, or store to, global `{symbol}`"))
            }
            RawExprKind::CompoundLiteral { init, is_file_scope } if e.is_lvalue => {
                if *is_file_scope {
                    return unsupported("file-scope compound literal");
                }
                if self.cond_depth > 0 {
                    return unsupported("conditionally evaluated compound literal");
                }
                if self.in_cond {
                    return unsupported("compound literal in a condition");
                }
                let ty = self.ty(&e.ty)?;
                if let Ty::Record(rid) = &ty {
                    if self.record_dtor(rid)?.is_some() {
                        return unsupported("compound literal with a non-trivial destructor");
                    }
                }
                // C11 6.5.2.5p5: an unnamed object whose lifetime is the
                // enclosing block.
                let t = self.new_temp(ty.clone());
                self.emit(Stmt::StorageLive(t));
                self.init_into(Place::local(t), &ty, init)?;
                self.register(t, None);
                Ok((Place::local(t), ty))
            }
            RawExprKind::Unsupported { desc } => unsupported(desc.clone()),
            _ => unsupported(format!("lvalue form {:?}", std::mem::discriminant(&e.kind))),
        }
    }

    // ----------------------------- rvalues -----------------------------

    fn rvalue(&mut self, e: &RawExpr) -> Result<Expr> {
        if let RawExprKind::Unsupported { desc } = &e.kind {
            return unsupported(desc.clone());
        }
        if e.is_lvalue {
            return malformed("lvalue used as a value without lvalue-to-rvalue conversion");
        }
        let ty = self.ty(&e.ty)?;
        match &e.kind {
            RawExprKind::IntLit { value } => match ty {
                Ty::Int(w, s, c) if int_fits(*value, w, s) => Ok(Expr::ConstInt(w, s, c, *value)),
                _ => malformed(format!("integer literal {value} does not fit {ty:?}")),
            },
            RawExprKind::BoolLit { value } => Ok(Expr::ConstBool(*value)),
            RawExprKind::SizeofOrAlignof { value_bytes } => match ty {
                Ty::Int(w, s, c) if int_fits(i128::from(*value_bytes), w, s) => {
                    Ok(Expr::ConstInt(w, s, c, i128::from(*value_bytes)))
                }
                _ => malformed("sizeof/alignof of non-integer type"),
            },
            RawExprKind::Paren { sub } => self.rvalue(sub),
            RawExprKind::Cast { kind, sub } => self.cast(*kind, sub, &ty),
            RawExprKind::Unary { op, sub } => match op {
                UnaryOp::Plus => {
                    let v = self.rvalue(sub)?;
                    expect_same("unary +", &self.ty(&sub.ty)?, &ty)?;
                    Ok(v)
                }
                UnaryOp::Minus | UnaryOp::BitNot => {
                    if ty.int_parts().is_none() {
                        return unsupported(format!("unary arithmetic on {ty:?}"));
                    }
                    let v = self.rvalue(sub)?;
                    expect_same("unary operator", &self.ty(&sub.ty)?, &ty)?;
                    let op = if *op == UnaryOp::Minus { UnOp::Neg } else { UnOp::BitNot };
                    Ok(Expr::Unary(op, ty, Box::new(v)))
                }
                UnaryOp::LogNot if ty == Ty::Bool => {
                    // C++: `!` yields `bool`.
                    let b = self.cond_bool(sub)?;
                    Ok(Expr::Unary(UnOp::LogNot, Ty::Bool, Box::new(b)))
                }
                UnaryOp::LogNot => {
                    let (w, s, _) = match ty.int_parts() {
                        Some(p) => p,
                        None => return malformed("`!` result is not an integer"),
                    };
                    let b = self.cond_bool(sub)?;
                    Ok(Expr::BoolToInt(
                        w,
                        s,
                        Box::new(Expr::Unary(UnOp::LogNot, Ty::Bool, Box::new(b))),
                    ))
                }
                UnaryOp::AddrOf => {
                    let (p, _) = self.place(sub)?;
                    Ok(Expr::AddrOf(p, ty))
                }
                UnaryOp::Deref => malformed("dereference used as a prvalue"),
                UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec => {
                    Ok(self.incdec(*op, sub, true)?.expect("value requested"))
                }
            },
            RawExprKind::Binary { op, lhs, rhs, compute_tys } => match op {
                BinaryOp::LogAnd | BinaryOp::LogOr => {
                    // C11 yields `int`; C++ yields `bool`.
                    let (one, zero) = match ty.int_parts() {
                        Some((w, s, c)) => (Expr::ConstInt(w, s, c, 1), Expr::ConstInt(w, s, c, 0)),
                        None if ty == Ty::Bool => (Expr::ConstBool(true), Expr::ConstBool(false)),
                        None => return malformed("`&&`/`||` result is not an integer"),
                    };
                    let t = self.new_temp(ty.clone());
                    let (tb, fb, join) = (self.new_block(), self.new_block(), self.new_block());
                    self.lower_branch(e, tb, fb)?;
                    self.cur = tb;
                    self.emit(Stmt::Assign(Place::local(t), ty.clone(), one));
                    self.terminate(Terminator::Goto(join))?;
                    self.cur = fb;
                    self.emit(Stmt::Assign(Place::local(t), ty.clone(), zero));
                    self.terminate(Terminator::Goto(join))?;
                    self.cur = join;
                    Ok(Expr::ReadPlace(Place::local(t), ty))
                }
                BinaryOp::Comma => {
                    self.discard(lhs)?;
                    self.rvalue(rhs)
                }
                BinaryOp::Assign => Ok(self.assign(lhs, rhs, true)?.expect("value requested")),
                BinaryOp::CompoundAssign(a) => Ok(self
                    .compound_assign(*a, lhs, rhs, compute_tys.as_ref(), true)?
                    .expect("value requested")),
                _ => self.arith(*op, lhs, rhs, ty),
            },
            RawExprKind::Conditional { cond, then_expr, else_expr } => {
                if ty == Ty::Void {
                    return malformed("void conditional used as a value");
                }
                let t = self.new_temp(ty.clone());
                let (tb, fb, join) = (self.new_block(), self.new_block(), self.new_block());
                self.lower_branch(cond, tb, fb)?;
                for (bb, arm) in [(tb, then_expr), (fb, else_expr)] {
                    self.cur = bb;
                    self.cond_depth += 1;
                    let v = self.rvalue(arm)?;
                    self.cond_depth -= 1;
                    expect_same("conditional arm", &self.ty(&arm.ty)?, &ty)?;
                    self.emit(Stmt::Assign(Place::local(t), ty.clone(), v));
                    self.terminate(Terminator::Goto(join))?;
                }
                self.cur = join;
                Ok(Expr::ReadPlace(Place::local(t), ty))
            }
            RawExprKind::Call { .. } => match self.call(e, true)? {
                Some(v) => Ok(v),
                None => malformed("void call used as a value"),
            },
            RawExprKind::InitList { .. } | RawExprKind::CompoundLiteral { .. }
                if self.shared.cxx && matches!(ty, Ty::Record(_)) =>
            {
                self.temp_value(e, &ty)
            }
            RawExprKind::InitList { .. } => unsupported("initializer list used as a value"),
            RawExprKind::CompoundLiteral { .. } => unsupported("compound literal used as a value"),
            RawExprKind::CxxThis => Ok(Expr::ReadPlace(Place::local(1), self.this_ty()?)),
            RawExprKind::NullptrLit => match &e.ty {
                RawType::NullPtrT => Ok(Expr::NullPtr(ty)),
                _ => malformed("`nullptr` literal whose type is not `std::nullptr_t`"),
            },
            RawExprKind::ImplicitValueInit => match &ty {
                Ty::Int(w, s, c) => Ok(Expr::ConstInt(*w, *s, *c, 0)),
                Ty::Bool => Ok(Expr::ConstBool(false)),
                Ty::Ptr(..) => Ok(Expr::NullPtr(ty.clone())),
                Ty::Record(_) => self.temp_value(e, &ty),
                other => unsupported(format!("value-initialization of {other:?}")),
            },
            RawExprKind::ExprWithCleanups { sub } => self.rvalue(sub),
            RawExprKind::BindTemporary { .. } | RawExprKind::Construct { .. } => {
                self.temp_value(e, &ty)
            }
            RawExprKind::BuiltinBitCast { sub, from_ty } => {
                let from = self.ty(from_ty)?;
                let (p, pty) = self.place(sub)?;
                expect_same("bit_cast operand", &pty, &from)?;
                Ok(Expr::BitCast(from.clone(), ty, Box::new(Expr::ReadPlace(p, from))))
            }
            RawExprKind::MaterializeTemporary { .. } => {
                malformed("materialized temporary with prvalue category")
            }
            RawExprKind::VarRef { .. }
            | RawExprKind::GlobalRef { .. }
            | RawExprKind::ArraySubscript { .. }
            | RawExprKind::Member { .. } => malformed("lvalue node with prvalue category"),
            RawExprKind::Unsupported { .. } => unreachable!("handled above"),
        }
    }

    /// A relational or equality comparison as a `CppTy.bool`-valued
    /// expression (`Trusted.CppAst` comparisons always produce `bool`).
    fn compare(&mut self, bop: BinOp, lhs: &RawExpr, rhs: &RawExpr) -> Result<Expr> {
        let lt = self.ty(&lhs.ty)?;
        let rt = self.ty(&rhs.ty)?;
        let l = self.rvalue(lhs)?;
        let r = self.rvalue(rhs)?;
        match (&lt, &rt) {
            (Ty::Ptr(..), Ty::Ptr(..)) => {}
            (Ty::Int(..), Ty::Int(..)) => expect_same("comparison", &rt, &lt)?,
            _ => return unsupported(format!("comparison {bop:?} of {lt:?} and {rt:?}")),
        }
        Ok(Expr::Binary(bop, Ty::Bool, Box::new(l), Box::new(r)))
    }

    fn arith(&mut self, op: BinaryOp, lhs: &RawExpr, rhs: &RawExpr, ty: Ty) -> Result<Expr> {
        if let Some(bop) = comparison_op(op) {
            let c = self.compare(bop, lhs, rhs)?;
            // C11 6.5.8p6 / 6.5.9p3: the result has type `int` (0 or 1); in
            // C++ it is `bool`.
            return match ty {
                Ty::Bool => Ok(c),
                Ty::Int(w, s, _) => Ok(Expr::BoolToInt(w, s, Box::new(c))),
                _ => malformed("comparison result is neither an integer nor bool"),
            };
        }
        let lt = self.ty(&lhs.ty)?;
        let rt = self.ty(&rhs.ty)?;
        let l = self.rvalue(lhs)?;
        let r = self.rvalue(rhs)?;
        let bop = match op {
            BinaryOp::Add => BinOp::Add,
            BinaryOp::Sub => BinOp::Sub,
            BinaryOp::Mul => BinOp::Mul,
            BinaryOp::Div => BinOp::Div,
            BinaryOp::Rem => BinOp::Rem,
            BinaryOp::Shl => BinOp::Shl,
            BinaryOp::Shr => BinOp::Shr,
            BinaryOp::BitAnd => BinOp::BitAnd,
            BinaryOp::BitOr => BinOp::BitOr,
            BinaryOp::BitXor => BinOp::BitXor,
            _ => return malformed(format!("unexpected operator {op:?}")),
        };
        match (&lt, &rt) {
            (Ty::Ptr(..), Ty::Ptr(..)) => unsupported("pointer difference"),
            (Ty::Ptr(..), Ty::Int(..)) | (Ty::Int(..), Ty::Ptr(..)) => {
                let (p, pt, n, nt) =
                    if lt.pointee().is_some() { (l, &lt, r, &rt) } else { (r, &rt, l, &lt) };
                let elem = match pt.pointee() {
                    Some(Ty::Void) | None => return unsupported("arithmetic on `void *`"),
                    Some(e) => e.clone(),
                };
                expect_same("pointer arithmetic", pt, &ty)?;
                match bop {
                    BinOp::Add => Ok(Expr::PtrAdd(elem, ty, Box::new(p), Box::new(n))),
                    BinOp::Sub if lt.pointee().is_some() => {
                        let neg = negated_offset(n, nt)?;
                        Ok(Expr::PtrAdd(elem, ty, Box::new(p), Box::new(neg)))
                    }
                    _ => unsupported(format!("pointer operator {bop:?}")),
                }
            }
            (Ty::Int(..), Ty::Int(..)) => {
                if matches!(bop, BinOp::Shl | BinOp::Shr) {
                    expect_same("shift", &lt, &ty)?;
                } else {
                    expect_same("arithmetic lhs", &lt, &ty)?;
                    expect_same("arithmetic rhs", &rt, &ty)?;
                }
                Ok(Expr::Binary(bop, ty, Box::new(l), Box::new(r)))
            }
            _ => unsupported(format!("operator {bop:?} on {lt:?} and {rt:?}")),
        }
    }

    fn cast(&mut self, kind: CastKind, sub: &RawExpr, ty: &Ty) -> Result<Expr> {
        match kind {
            CastKind::LvalueToRvalue => {
                if let RawExprKind::GlobalRef { symbol } = &strip_parens(sub).kind {
                    return self.global_load(symbol, ty);
                }
                if sub.ty == RawType::NullPtrT {
                    // C++ [conv.lval]p3.1: converting a `std::nullptr_t`
                    // glvalue yields a null pointer constant without
                    // accessing the object.
                    if !matches!(
                        strip_parens(sub).kind,
                        RawExprKind::VarRef { is_ref_binding: false, .. }
                    ) {
                        return unsupported("read of a `std::nullptr_t` that is not a variable");
                    }
                    self.place(sub)?;
                    return Ok(Expr::NullPtr(ty.clone()));
                }
                let (p, pty) = self.place(sub)?;
                if matches!(pty, Ty::Array(..) | Ty::Void) {
                    return malformed(format!("lvalue-to-rvalue of {pty:?}"));
                }
                expect_same("lvalue-to-rvalue", &pty, ty)?;
                Ok(Expr::ReadPlace(p, pty))
            }
            CastKind::IntegralCast | CastKind::IntToBool | CastKind::BoolToInt => {
                let st = self.ty(&sub.ty)?;
                let v = self.rvalue(sub)?;
                match (&st, ty) {
                    (Ty::Int(..) | Ty::Bool, Ty::Int(..) | Ty::Bool) => convert(v, &st, ty),
                    _ => unsupported(format!("integral cast from {st:?} to {ty:?}")),
                }
            }
            CastKind::PointerCast | CastKind::BitCast | CastKind::Noop => {
                let st = self.ty(&sub.ty)?;
                let v = self.rvalue(sub)?;
                if &st == ty {
                    Ok(v)
                } else if st.pointee().is_some() && ty.pointee().is_some() {
                    Ok(Expr::PtrCast(ty.clone(), Box::new(v)))
                } else {
                    unsupported(format!("{kind:?} cast from {st:?} to {ty:?}"))
                }
            }
            CastKind::NullToPointer => {
                let s = strip_parens(sub);
                if s.ty == RawType::NullPtrT
                    && matches!(s.kind, RawExprKind::VarRef { is_ref_binding: false, .. })
                {
                    // Converting a `std::nullptr_t` variable reads nothing
                    // (C++ [conv.ptr]p1, [conv.lval]p3.1).
                    self.place(sub)?;
                } else if !is_null_pointer_constant(sub) {
                    return unsupported("null pointer constant with side effects");
                }
                if ty.pointee().is_none() {
                    return malformed("null-to-pointer cast to non-pointer type");
                }
                Ok(Expr::NullPtr(ty.clone()))
            }
            CastKind::ArrayToPointerDecay => {
                let (p, aty) = self.place(sub)?;
                let is_const = matches!(ty, Ty::Ptr(_, true, ..));
                match &aty {
                    Ty::Array(elem, _) if ty.pointee() == Some(&**elem) => {}
                    _ => return malformed(format!("array decay of {aty:?} to {ty:?}")),
                }
                let arr_ptr = Ty::Ptr(Box::new(aty), is_const, false, false);
                Ok(Expr::PtrCast(ty.clone(), Box::new(Expr::AddrOf(p, arr_ptr))))
            }
            CastKind::PtrToBool => {
                let st = self.ty(&sub.ty)?;
                let v = self.rvalue(sub)?;
                if st.pointee().is_none() || ty != &Ty::Bool {
                    return malformed("pointer-to-bool cast on non-pointer");
                }
                Ok(Expr::Binary(BinOp::Ne, Ty::Bool, Box::new(v), Box::new(Expr::NullPtr(st))))
            }
            CastKind::ToVoid => malformed("cast to void used as a value"),
            CastKind::DerivedToBase { offset_bytes } => {
                if offset_bytes != 0 {
                    return unsupported("base subobject at a non-zero offset");
                }
                let v = self.rvalue(sub)?;
                if ty.pointee().is_none() {
                    return malformed("derived-to-base prvalue cast of a non-pointer");
                }
                Ok(Expr::PtrCast(ty.clone(), Box::new(v)))
            }
            CastKind::ConstructorConversion | CastKind::UserDefinedConversion => {
                let st = self.ty(&sub.ty)?;
                expect_same("conversion", &st, ty)?;
                self.rvalue(sub)
            }
        }
    }

    /// Converts a scalar expression to a `CppTy.bool`-valued branch condition
    /// (C11 6.8.4.1p2: compares unequal to 0).
    fn cond_bool(&mut self, e: &RawExpr) -> Result<Expr> {
        // A comparison already is a truth value; skip the C `int` round trip.
        if let RawExprKind::Binary { op, lhs, rhs, .. } = &strip_parens(e).kind {
            if let Some(bop) = comparison_op(*op) {
                return self.compare(bop, lhs, rhs);
            }
        }
        let t = self.ty(&e.ty)?;
        let v = self.rvalue(e)?;
        match &t {
            Ty::Bool => Ok(v),
            Ty::Int(..) => Ok(Expr::IntToBool(Box::new(v))),
            Ty::Ptr(..) => Ok(Expr::Binary(
                BinOp::Ne,
                Ty::Bool,
                Box::new(v),
                Box::new(Expr::NullPtr(t.clone())),
            )),
            other => unsupported(format!("condition of type {other:?}")),
        }
    }

    /// Lowers `e` as a branch condition, terminating the current block with
    /// edges to `t` (nonzero) and `f` (zero); short-circuits `&&`, `||`, `!`.
    fn lower_branch(&mut self, e: &RawExpr, t: usize, f: usize) -> Result<()> {
        match &e.kind {
            RawExprKind::Paren { sub } => self.lower_branch(sub, t, f),
            RawExprKind::Binary { op: BinaryOp::LogAnd, lhs, rhs, .. } => {
                let mid = self.new_block();
                self.lower_branch(lhs, mid, f)?;
                self.cur = mid;
                self.cond_depth += 1;
                self.lower_branch(rhs, t, f)?;
                self.cond_depth -= 1;
                Ok(())
            }
            RawExprKind::Binary { op: BinaryOp::LogOr, lhs, rhs, .. } => {
                let mid = self.new_block();
                self.lower_branch(lhs, t, mid)?;
                self.cur = mid;
                self.cond_depth += 1;
                self.lower_branch(rhs, t, f)?;
                self.cond_depth -= 1;
                Ok(())
            }
            RawExprKind::Unary { op: UnaryOp::LogNot, sub } => self.lower_branch(sub, f, t),
            _ => {
                let c = self.cond_bool(e)?;
                self.terminate(Terminator::Branch(c, t, f))
            }
        }
    }

    fn store(&mut self, p: Place, ty: Ty, v: Expr, want_value: bool) -> Option<Expr> {
        if want_value {
            if matches!(p.projs.last(), Some(Proj::Bitfield(..))) {
                self.emit(Stmt::Assign(p.clone(), ty.clone(), v));
                let t = self.materialize(ty.clone(), Expr::ReadPlace(p, ty.clone()));
                Some(Expr::ReadPlace(Place::local(t), ty))
            } else {
                let t = self.materialize(ty.clone(), v);
                self.emit(Stmt::Assign(
                    p,
                    ty.clone(),
                    Expr::ReadPlace(Place::local(t), ty.clone()),
                ));
                Some(Expr::ReadPlace(Place::local(t), ty))
            }
        } else {
            self.emit(Stmt::Assign(p, ty, v));
            None
        }
    }

    fn assign(&mut self, lhs: &RawExpr, rhs: &RawExpr, want_value: bool) -> Result<Option<Expr>> {
        let (p, pty) = self.place(lhs)?;
        if matches!(pty, Ty::Array(..) | Ty::Void) {
            return unsupported(format!("assignment to {pty:?}"));
        }
        let v = self.rvalue(rhs)?;
        expect_same("assignment", &self.ty(&rhs.ty)?, &pty)?;
        Ok(self.store(p, pty, v, want_value))
    }

    fn compound_assign(
        &mut self,
        a: ArithOp,
        lhs: &RawExpr,
        rhs: &RawExpr,
        compute: Option<&(RawType, RawType)>,
        want_value: bool,
    ) -> Result<Option<Expr>> {
        let (p, pty) = self.place(lhs)?;
        let rty = self.ty(&rhs.ty)?;
        let r = self.rvalue(rhs)?;
        let old = Expr::ReadPlace(p.clone(), pty.clone());
        let new = match &pty {
            Ty::Ptr(elem, ..) => {
                if matches!(**elem, Ty::Void) || rty.int_parts().is_none() {
                    return unsupported(
                        "compound assignment on `void *` or with non-integer offset",
                    );
                }
                let off = match a {
                    ArithOp::Add => r,
                    ArithOp::Sub => negated_offset(r, &rty)?,
                    _ => return unsupported(format!("pointer compound assignment {a:?}")),
                };
                Expr::PtrAdd((**elem).clone(), pty.clone(), Box::new(old), Box::new(off))
            }
            Ty::Int(..) => {
                let (cl, cr) = match compute {
                    Some((cl, cr)) => (self.ty(cl)?, self.ty(cr)?),
                    None => return malformed("compound assignment without computation types"),
                };
                if cl != cr {
                    return unsupported(format!("compound assignment computing {cl:?} in {cr:?}"));
                }
                let lv = convert(old, &pty, &cl)?;
                let rv = if matches!(a, ArithOp::Shl | ArithOp::Shr) {
                    if rty.int_parts().is_none() {
                        return malformed("shift count is not an integer");
                    }
                    r
                } else {
                    expect_same("compound assignment rhs", &rty, &cr)?;
                    r
                };
                let res = Expr::Binary(arith_binop(a), cr.clone(), Box::new(lv), Box::new(rv));
                convert(res, &cr, &pty)?
            }
            other => return unsupported(format!("compound assignment to {other:?}")),
        };
        Ok(self.store(p, pty, new, want_value))
    }

    fn incdec(&mut self, op: UnaryOp, sub: &RawExpr, want_value: bool) -> Result<Option<Expr>> {
        let (p, pty) = self.place(sub)?;
        let is_inc = matches!(op, UnaryOp::PreInc | UnaryOp::PostInc);
        let is_post = matches!(op, UnaryOp::PostInc | UnaryOp::PostDec);
        let bf_proj = match p.projs.last() {
            Some(&Proj::Bitfield(_, _, _, bf_w, bf_signed)) => Some((bf_w, bf_signed)),
            _ => None,
        };
        let step = |old: Expr| -> Result<Expr> {
            match &pty {
                Ty::Int(w, s, c) => {
                    let bop = if is_inc { BinOp::Add } else { BinOp::Sub };
                    let prom_ty = match bf_proj {
                        Some((bf_w, bf_signed)) => {
                            if bf_w < 32 || (bf_w == 32 && bf_signed) {
                                Some(Ty::I32)
                            } else if bf_w == 32 && !bf_signed {
                                Some(Ty::U32)
                            } else {
                                None
                            }
                        }
                        None if w.bits() < 32 => Some(Ty::I32),
                        None => None,
                    };
                    if let Some(prom) = prom_ty {
                        // C11 6.3.1.1p2, 6.5.2.4p2 / 6.5.3.1p2: `E++` is
                        // `E += 1`, computed after integer promotion (using
                        // the bit-field width when `E` is a bit-field).
                        let (pw, ps, pc) = prom.int_parts().expect("integer promotion type");
                        let sum = Expr::Binary(
                            bop,
                            prom.clone(),
                            Box::new(convert(old, &pty, &prom)?),
                            Box::new(Expr::ConstInt(pw, ps, pc, 1)),
                        );
                        convert(sum, &prom, &pty)
                    } else {
                        Ok(Expr::Binary(
                            bop,
                            pty.clone(),
                            Box::new(old),
                            Box::new(Expr::ConstInt(*w, *s, *c, 1)),
                        ))
                    }
                }
                Ty::Ptr(elem, ..) if !matches!(**elem, Ty::Void) => Ok(Expr::PtrAdd(
                    (**elem).clone(),
                    pty.clone(),
                    Box::new(old),
                    Box::new(Expr::ConstInt(
                        Width::W64,
                        Sign::Signed,
                        false,
                        if is_inc { 1 } else { -1 },
                    )),
                )),
                other => unsupported(format!("increment/decrement of {other:?}")),
            }
        };
        if !want_value {
            let new = step(Expr::ReadPlace(p.clone(), pty.clone()))?;
            self.emit(Stmt::Assign(p, pty, new));
            return Ok(None);
        }
        if is_post {
            let t = self.materialize(pty.clone(), Expr::ReadPlace(p.clone(), pty.clone()));
            let new = step(Expr::ReadPlace(Place::local(t), pty.clone()))?;
            self.emit(Stmt::Assign(p, pty.clone(), new));
            Ok(Some(Expr::ReadPlace(Place::local(t), pty)))
        } else {
            let new = step(Expr::ReadPlace(p.clone(), pty.clone()))?;
            Ok(self.store(p, pty, new, true))
        }
    }

    /// `Trusted.CppAst` has no global objects, so a read of a scalar global
    /// is lowered to a call of a synthesized, bodiless external callee
    /// `anneal.global_load.<symbol>` returning the global's type. This is a
    /// disclosed over-approximation: the program becomes `isPartial`, the
    /// semantics cannot execute the stub until a contract (any value of the
    /// type, no memory effects) is linked, and two reads are not assumed
    /// equal. Writes to, and addresses of, globals remain unsupported.
    fn global_load(&mut self, symbol: &str, ty: &Ty) -> Result<Expr> {
        if !matches!(ty, Ty::Int(..) | Ty::Bool | Ty::Ptr(..)) {
            return unsupported(format!("read of non-scalar global `{symbol}`"));
        }
        let stub = format!("{GLOBAL_LOAD_STUB_PREFIX}{symbol}");
        match self.shared.global_stubs.get(&stub) {
            Some(prev) if prev != ty => {
                return malformed(format!("global `{symbol}` read at two types"))
            }
            Some(_) => {}
            None => {
                self.shared.global_stubs.insert(stub.clone(), ty.clone());
            }
        }
        let t = self.new_temp(ty.clone());
        let next = self.new_block();
        self.terminate(Terminator::Call(stub, vec![], Some((Place::local(t), ty.clone())), next))?;
        self.cur = next;
        Ok(Expr::ReadPlace(Place::local(t), ty.clone()))
    }

    fn call(&mut self, e: &RawExpr, want_value: bool) -> Result<Option<Expr>> {
        let RawExprKind::Call {
            callee_symbol: callee,
            args,
            is_indirect,
            is_builtin,
            implicit_object,
            implicit_object_is_ptr,
            is_virtual,
            param_is_ref,
            returns_ref,
            trivial_assign,
        } = &e.kind
        else {
            return malformed("internal: call() on non-call");
        };
        let (is_indirect, is_builtin) = (*is_indirect, *is_builtin);
        let sym = match (callee, is_indirect) {
            (Some(s), false) => s.clone(),
            _ => return unsupported("indirect call through a function pointer"),
        };
        if *is_virtual {
            return unsupported(format!("virtual call to `{sym}` (Rung 2)"));
        }
        if *trivial_assign {
            // A trivial copy/move assignment operator copies the object
            // representation.
            let obj = match (implicit_object, args.as_slice()) {
                (Some(o), [_]) if !*implicit_object_is_ptr => o,
                _ => return malformed(format!("trivial assignment `{sym}` without an object")),
            };
            let (op, oty) = self.place(obj)?;
            let (sp, sty) = self.place(&args[0])?;
            expect_same("trivial assignment", &sty, &oty)?;
            self.emit(Stmt::Assign(op.clone(), oty.clone(), Expr::ReadPlace(sp, sty)));
            return Ok((want_value && *returns_ref).then(|| Expr::AddrOf(op, ptr_to(&oty))));
        }
        if is_builtin {
            if sym == "__builtin_expect" && args.len() == 2 && is_pure_int_const(&args[1]) {
                // `__builtin_expect(e, c)` evaluates to `e`; `c` is a pure
                // hint.
                return Ok(Some(self.rvalue(&args[0])?));
            }
            return unsupported(format!("compiler builtin `{sym}`"));
        }
        let (this_ty, ret) = {
            let s = self.shared.sig(&sym)?;
            (s.params.first().cloned(), s.ret.clone())
        };
        let mut vals = Vec::with_capacity(args.len() + 1);
        if let Some(obj) = implicit_object {
            let this_ty = match this_ty {
                Some(t) => t,
                None => return malformed(format!("member call to `{sym}` without `this`")),
            };
            vals.push(if *implicit_object_is_ptr {
                self.rvalue(obj)?
            } else {
                let (p, _) = self.place(obj)?;
                Expr::AddrOf(p, this_ty)
            });
        }
        let offset = usize::from(implicit_object.is_some());
        vals.extend(self.call_args(&sym, args, param_is_ref, offset)?);
        let next = self.new_block();
        let (dst, result) = if ret != Ty::Void && want_value {
            let t = self.new_temp(ret.clone());
            (Some((Place::local(t), ret.clone())), Some(Expr::ReadPlace(Place::local(t), ret)))
        } else {
            (None, None)
        };
        self.terminate(Terminator::Call(sym, vals, dst, next))?;
        self.cur = next;
        Ok(result)
    }

    /// Evaluates `e` for its side effects only.
    fn discard(&mut self, e: &RawExpr) -> Result<()> {
        match &e.kind {
            RawExprKind::Paren { sub } | RawExprKind::Cast { kind: CastKind::ToVoid, sub } => {
                self.discard(sub)
            }
            RawExprKind::Binary { op: BinaryOp::Assign, lhs, rhs, .. } => {
                self.assign(lhs, rhs, false).map(|_| ())
            }
            RawExprKind::Binary { op: BinaryOp::CompoundAssign(a), lhs, rhs, compute_tys } => {
                self.compound_assign(*a, lhs, rhs, compute_tys.as_ref(), false).map(|_| ())
            }
            RawExprKind::Binary { op: BinaryOp::Comma, lhs, rhs, .. } => {
                self.discard(lhs)?;
                self.discard(rhs)
            }
            RawExprKind::Binary {
                op: op @ (BinaryOp::LogAnd | BinaryOp::LogOr), lhs, rhs, ..
            } => {
                let (rhs_bb, join) = (self.new_block(), self.new_block());
                if *op == BinaryOp::LogAnd {
                    self.lower_branch(lhs, rhs_bb, join)?;
                } else {
                    self.lower_branch(lhs, join, rhs_bb)?;
                }
                self.cur = rhs_bb;
                self.cond_depth += 1;
                self.discard(rhs)?;
                self.cond_depth -= 1;
                self.terminate(Terminator::Goto(join))?;
                self.cur = join;
                Ok(())
            }
            RawExprKind::Unary {
                op: op @ (UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec),
                sub,
            } => self.incdec(*op, sub, false).map(|_| ()),
            RawExprKind::Call { .. } => self.call(e, false).map(|_| ()),
            RawExprKind::ExprWithCleanups { sub } => self.discard(sub),
            // `void()` (for example, what a disabled assertion macro expands
            // to) does nothing.
            RawExprKind::ImplicitValueInit if e.ty == RawType::Void => Ok(()),
            RawExprKind::BindTemporary { .. }
            | RawExprKind::Construct { .. }
            | RawExprKind::InitList { .. }
                if self.shared.cxx && !e.is_lvalue =>
            {
                let ty = self.ty(&e.ty)?;
                self.temp_value(e, &ty).map(|_| ())
            }
            RawExprKind::Conditional { cond, then_expr, else_expr } => {
                let (tb, fb, join) = (self.new_block(), self.new_block(), self.new_block());
                self.lower_branch(cond, tb, fb)?;
                for (bb, arm) in [(tb, then_expr), (fb, else_expr)] {
                    self.cur = bb;
                    self.cond_depth += 1;
                    self.discard(arm)?;
                    self.cond_depth -= 1;
                    self.terminate(Terminator::Goto(join))?;
                }
                self.cur = join;
                Ok(())
            }
            _ if e.is_lvalue => self.place(e).map(|_| ()),
            _ => {
                // Keep the evaluation (and any undefined behavior it has).
                let ty = self.ty(&e.ty)?;
                if ty == Ty::Void {
                    return malformed("discarded void expression without effects");
                }
                let v = self.rvalue(e)?;
                self.materialize(ty, v);
                Ok(())
            }
        }
    }

    // ----------------------------- statements -----------------------------

    fn label_block(&mut self, label: &str) -> usize {
        if let Some(b) = self.labels.get(label) {
            return *b;
        }
        let b = self.new_block();
        self.labels.insert(label.to_owned(), b);
        b
    }

    fn lower_cond_branch(&mut self, cond: &RawExpr, t: usize, f: usize) -> Result<()> {
        self.begin_full_expr(cond)?;
        self.in_cond = true;
        let res = self.lower_branch(cond, t, f);
        self.in_cond = false;
        res?;
        self.no_cond_temps()
    }

    /// Lowers a selection or iteration substatement, which forms its own block
    /// scope even without `{ ... }` braces (C11 6.8.4p3, 6.8.5p5; C++20
    /// [stmt.select]p1, [stmt.iter]p1).
    fn scoped_stmt(&mut self, s: &RawStmt) -> Result<()> {
        if matches!(s, RawStmt::Compound(_)) {
            self.stmt(s)
        } else {
            self.push_scope();
            self.stmt(s)?;
            let scope = self.pop_scope();
            self.cleanup(scope)
        }
    }

    fn stmt(&mut self, s: &RawStmt) -> Result<()> {
        match s {
            RawStmt::Compound(v) => {
                // Leaving a block ends the lifetimes of its locals (C11
                // 6.2.4p6), so a block re-entered on every loop iteration
                // reuses rather than accumulates their storage.
                self.push_scope();
                for s in v {
                    self.stmt(s)?;
                }
                let scope = self.pop_scope();
                self.cleanup(scope)
            }
            RawStmt::Decl { var_id, is_static_const: true, .. } => {
                // Hoisted to the start of the body by `hoist_static_const`.
                if self.var_map.contains_key(var_id) {
                    Ok(())
                } else {
                    malformed(format!("static local #{var_id} was not hoisted"))
                }
            }
            RawStmt::Decl { var_id, name, ty, init, is_ref, dtor_symbol, is_nrvo, .. }
                if self.shared.cxx =>
            {
                let lt = self.ty(ty)?;
                if lt == Ty::Void {
                    return malformed(format!("local `{name}` of void type"));
                }
                let dtor = match dtor_symbol {
                    Some(d) => Some(checked_dtor(d)?),
                    None => None,
                };
                if *is_nrvo && dtor.is_some() {
                    return unsupported(format!(
                        "named-return-value local `{name}` with a non-trivial destructor"
                    ));
                }
                self.locals.push(LocalDecl {
                    ty: lt.clone(),
                    is_param: false,
                    debug_name: name.clone(),
                });
                let l = self.locals.len() - 1;
                if self.var_map.insert(*var_id, l).is_some() {
                    return malformed(format!("local #{var_id} declared twice"));
                }
                self.emit(Stmt::StorageLive(l));
                match init {
                    Some(init) => {
                        self.begin_full_expr(init)?;
                        if *is_ref {
                            let (p, pty) = self.place(init)?;
                            if lt.pointee() != Some(&pty) {
                                return malformed(format!("reference `{name}` bound to {pty:?}"));
                            }
                            self.emit(Stmt::Assign(
                                Place::local(l),
                                lt.clone(),
                                Expr::AddrOf(p, lt),
                            ));
                        } else {
                            self.init_into(Place::local(l), &lt, init)?;
                        }
                        self.end_full_expr()?;
                    }
                    None if *is_ref => {
                        return malformed(format!("reference `{name}` without initializer"))
                    }
                    None => {}
                }
                // The object's lifetime (and destructor obligation) starts
                // once it is initialized.
                self.register(l, dtor);
                Ok(())
            }
            RawStmt::Decl { var_id, name, ty, init, .. } => {
                let lt = self.ty(ty)?;
                if lt == Ty::Void {
                    return malformed(format!("local `{name}` of void type"));
                }
                if self.escaped.contains(var_id) && !self.top_level_vars.contains(var_id) {
                    return unsupported(format!(
                        "address-taken local `{name}` declared in a nested scope"
                    ));
                }
                self.locals.push(LocalDecl {
                    ty: lt.clone(),
                    is_param: false,
                    debug_name: name.clone(),
                });
                let l = self.locals.len() - 1;
                if self.var_map.insert(*var_id, l).is_some() {
                    return malformed(format!("local #{var_id} declared twice"));
                }
                self.emit(Stmt::StorageLive(l));
                if let Some(init) = init {
                    self.begin_full_expr(init)?;
                    self.init_into(Place::local(l), &lt, init)?;
                    self.end_full_expr()?;
                }
                self.register(l, None);
                Ok(())
            }
            RawStmt::Expr(e) => {
                self.begin_full_expr(e)?;
                self.discard(e)?;
                self.end_full_expr()
            }
            RawStmt::If { cond, then_branch, else_branch } => {
                let tb = self.new_block();
                let join = self.new_block();
                let fb = if else_branch.is_some() { self.new_block() } else { join };
                self.lower_cond_branch(cond, tb, fb)?;
                self.cur = tb;
                self.scoped_stmt(then_branch)?;
                self.terminate(Terminator::Goto(join))?;
                if let Some(e) = else_branch {
                    self.cur = fb;
                    self.scoped_stmt(e)?;
                    self.terminate(Terminator::Goto(join))?;
                }
                self.cur = join;
                Ok(())
            }
            RawStmt::While { cond, body } => {
                let (header, body_bb, exit) =
                    (self.new_block(), self.new_block(), self.new_block());
                self.terminate(Terminator::Goto(header))?;
                self.cur = header;
                self.lower_cond_branch(cond, body_bb, exit)?;
                self.cur = body_bb;
                let depth = self.scopes.len();
                self.targets.push(Targets { brk: exit, cont: Some(header), depth });
                self.scoped_stmt(body)?;
                self.targets.pop();
                self.terminate(Terminator::Goto(header))?;
                self.cur = exit;
                Ok(())
            }
            RawStmt::DoWhile { body, cond } => {
                let (body_bb, cond_bb, exit) =
                    (self.new_block(), self.new_block(), self.new_block());
                self.terminate(Terminator::Goto(body_bb))?;
                self.cur = body_bb;
                let depth = self.scopes.len();
                self.targets.push(Targets { brk: exit, cont: Some(cond_bb), depth });
                self.scoped_stmt(body)?;
                self.targets.pop();
                self.terminate(Terminator::Goto(cond_bb))?;
                self.cur = cond_bb;
                self.lower_cond_branch(cond, body_bb, exit)?;
                self.cur = exit;
                Ok(())
            }
            RawStmt::For { init, cond, inc, body } => {
                // The init-statement's variables live until the loop ends.
                self.push_scope();
                if let Some(i) = init {
                    self.stmt(i)?;
                }
                let (header, body_bb, inc_bb, exit) =
                    (self.new_block(), self.new_block(), self.new_block(), self.new_block());
                self.terminate(Terminator::Goto(header))?;
                self.cur = header;
                match cond {
                    Some(c) => self.lower_cond_branch(c, body_bb, exit)?,
                    None => self.terminate(Terminator::Goto(body_bb))?,
                }
                self.cur = body_bb;
                let depth = self.scopes.len();
                self.targets.push(Targets { brk: exit, cont: Some(inc_bb), depth });
                self.scoped_stmt(body)?;
                self.targets.pop();
                self.terminate(Terminator::Goto(inc_bb))?;
                self.cur = inc_bb;
                if let Some(i) = inc {
                    self.push_scope();
                    self.begin_full_expr(i)?;
                    self.discard(i)?;
                    self.end_full_expr()?;
                    let inc_scope = self.pop_scope();
                    self.cleanup(inc_scope)?;
                }
                self.terminate(Terminator::Goto(header))?;
                self.cur = exit;
                let scope = self.pop_scope();
                self.cleanup(scope)
            }
            RawStmt::Switch { cond, body } => {
                self.begin_full_expr(cond)?;
                let cty = self.ty(&cond.ty)?;
                let (w, sg, ch) = match cty.int_parts() {
                    Some(p) => p,
                    None => return malformed("switch on a non-integer"),
                };
                self.in_cond = true;
                let v = self.rvalue(cond);
                self.in_cond = false;
                let v = v?;
                self.no_cond_temps()?;
                let t = self.materialize(cty.clone(), v);
                let mut labels = Vec::new();
                collect_case_labels(body, &mut labels);
                let blocks: Vec<usize> = labels.iter().map(|_| self.new_block()).collect();
                let exit = self.new_block();
                let mut default = None;
                for (i, lab) in labels.iter().enumerate() {
                    match lab {
                        None => {
                            if default.replace(blocks[i]).is_some() {
                                return malformed("switch with two default labels");
                            }
                        }
                        Some(val) => {
                            if !int_fits(*val, w, sg) {
                                return malformed(format!("case value {val} does not fit {cty:?}"));
                            }
                            let test = Expr::Binary(
                                BinOp::Eq,
                                Ty::Bool,
                                Box::new(Expr::ReadPlace(Place::local(t), cty.clone())),
                                Box::new(Expr::ConstInt(w, sg, ch, *val)),
                            );
                            let next = self.new_block();
                            self.terminate(Terminator::Branch(test, blocks[i], next))?;
                            self.cur = next;
                        }
                    }
                }
                self.jump(Terminator::Goto(default.unwrap_or(exit)))?;
                let depth = self.scopes.len();
                self.targets.push(Targets { brk: exit, cont: None, depth });
                self.switches.push(SwitchCtx { blocks, labels, next: 0, depth });
                self.scoped_stmt(body)?;
                let ctx = self.switches.pop().expect("pushed above");
                self.targets.pop();
                if ctx.next != ctx.labels.len() {
                    return malformed("switch case labels visited out of order");
                }
                self.terminate(Terminator::Goto(exit))?;
                self.cur = exit;
                Ok(())
            }
            RawStmt::Case { value, sub } => self.case_label(Some(*value), sub),
            RawStmt::Default { sub } => self.case_label(None, sub),
            RawStmt::Break => match self.targets.last() {
                Some(t) => {
                    let (b, depth) = (t.brk, t.depth);
                    self.cleanup_scopes_from(depth)?;
                    self.jump(Terminator::Goto(b))
                }
                None => malformed("`break` outside a loop or switch"),
            },
            RawStmt::Continue => {
                match self.targets.iter().rev().find_map(|t| t.cont.map(|c| (c, t.depth))) {
                    Some((c, depth)) => {
                        self.cleanup_scopes_from(depth)?;
                        self.jump(Terminator::Goto(c))
                    }
                    None => malformed("`continue` outside a loop"),
                }
            }
            RawStmt::Goto { .. }
                if self.scopes.iter().flatten().any(|(_, dtor)| dtor.is_some()) =>
            {
                unsupported("`goto` while an object with a non-trivial destructor is live")
            }
            RawStmt::Goto { label } => {
                let block = self.new_block();
                let scopes = self
                    .scope_ids
                    .iter()
                    .zip(&self.scopes)
                    .map(|(id, s)| (*id, s.iter().map(|(l, _)| *l).collect()))
                    .collect();
                self.pending_gotos.push(PendingGoto { block, label: label.clone(), scopes });
                self.jump(Terminator::Goto(block))
            }
            RawStmt::Label { label, sub } => {
                if !self.defined_labels.insert(label.clone()) {
                    return malformed(format!("label `{label}` defined twice"));
                }
                let at = self.scope_ids.iter().zip(&self.scopes).map(|(id, s)| (*id, s.len()));
                self.label_scopes.insert(label.clone(), at.collect());
                let b = self.label_block(label);
                self.terminate(Terminator::Goto(b))?;
                self.cur = b;
                self.stmt(sub)
            }
            RawStmt::Return(e) if self.shared.cxx => {
                // Return-slot normalization: initialize `_0` while every
                // local is still alive, destroy the full-expression's
                // temporaries, then end every open scope innermost first
                // (destructor, then storage), and only then return.
                if let Some(e) = e {
                    self.begin_full_expr(e)?;
                    let rt = self.ret_ty.clone();
                    if rt == Ty::Void {
                        self.discard(e)?;
                    } else if self.ret_is_ref {
                        let (p, pty) = self.place(e)?;
                        if rt.pointee() != Some(&pty) {
                            return malformed(format!("returned reference to {pty:?}"));
                        }
                        self.emit(Stmt::Assign(Place::local(0), rt.clone(), Expr::AddrOf(p, rt)));
                    } else if matches!(rt, Ty::Record(_)) {
                        self.init_into(Place::local(0), &rt, e)?;
                    } else {
                        let v = self.rvalue(e)?;
                        expect_same("return value", &self.ty(&e.ty)?, &rt)?;
                        self.emit(Stmt::Assign(Place::local(0), rt, v));
                    }
                    self.end_full_expr()?;
                }
                self.cleanup_scopes_from(0)?;
                self.epilogue()?;
                self.jump(Terminator::Ret)
            }
            RawStmt::Return(e) => {
                if let Some(e) = e {
                    self.begin_full_expr(e)?;
                    if self.ret_ty == Ty::Void {
                        self.discard(e)?;
                    } else {
                        let v = self.rvalue(e)?;
                        expect_same("return value", &self.ty(&e.ty)?, &self.ret_ty.clone())?;
                        let rt = self.ret_ty.clone();
                        self.emit(Stmt::Assign(Place::local(0), rt, v));
                    }
                    self.end_full_expr()?;
                }
                self.cleanup_scopes_from(0)?;
                self.jump(Terminator::Ret)
            }
            RawStmt::Null => Ok(()),
            RawStmt::Unsupported { desc } => unsupported(desc.clone()),
        }
    }

    fn case_label(&mut self, value: Option<i128>, sub: &RawStmt) -> Result<()> {
        let depth = match self.switches.last() {
            Some(c) => c.depth,
            None => return malformed("case label outside a switch"),
        };
        // Jumping to the label would skip the `storageLive` of a local
        // declared earlier in the `switch` body.
        if self.scopes[depth..].iter().any(|s| !s.is_empty()) {
            return unsupported("`case` or `default` label after a declaration in its `switch`");
        }
        let ctx = self.switches.last_mut().expect("checked above");
        if ctx.next >= ctx.labels.len() || ctx.labels[ctx.next] != value {
            return malformed("switch case labels visited out of order");
        }
        let b = ctx.blocks[ctx.next];
        ctx.next += 1;
        self.terminate(Terminator::Goto(b))?;
        self.cur = b;
        self.stmt(sub)
    }

    fn finish(mut self) -> Result<Body> {
        let fall_off =
            if self.ret_ty == Ty::Void { Terminator::Ret } else { Terminator::Unreachable };
        if self.blocks[self.cur].1.is_none() {
            self.blocks[self.cur].1 = Some(fall_off);
        }
        for l in self.labels.keys() {
            if !self.defined_labels.contains(l) {
                return malformed(format!("`goto {l}` without a matching label"));
            }
        }
        for g in std::mem::take(&mut self.pending_gotos) {
            let Some(at) = self.label_scopes.get(&g.label) else {
                return malformed(format!("`goto {}` without a matching label", g.label));
            };
            let common = g.scopes.iter().zip(at).take_while(|(s, l)| s.0 == l.0).count();
            // A jump into a block past one of its declarations, or across a
            // declaration in the innermost block it stays in, would skip a
            // `storageLive` or repeat one on a live local.
            if at[common..].iter().any(|(_, n)| *n > 0) {
                return unsupported(format!("`goto {}` into a block past a declaration", g.label));
            }
            if common == 0 || g.scopes[common - 1].1.len() != at[common - 1].1 {
                return unsupported(format!("`goto {}` across a declaration", g.label));
            }
            // Leaving a block ends the lifetimes of its live locals.
            let mut stmts = Vec::new();
            for (_, locals) in g.scopes[common..].iter().rev() {
                stmts.extend(locals.iter().rev().map(|l| Stmt::StorageDead(*l)));
            }
            self.blocks[g.block] = (stmts, Some(Terminator::Goto(self.labels[&g.label])));
        }
        let blocks: Vec<Block> = self
            .blocks
            .into_iter()
            .map(|(stmts, term)| Block { stmts, term: term.unwrap_or(Terminator::Unreachable) })
            .collect();
        let blocks = prune(blocks);
        let params = self.locals[1..=self.num_params].iter().map(|l| l.ty.clone()).collect();
        Ok(Body {
            identity: self.symbol,
            is_external: false,
            sig: Signature {
                params,
                ret: self.ret_ty,
                abi_cxx: self.abi_cxx,
                param_non_null: self.param_non_null,
            },
            locals: self.locals,
            blocks,
            entry_block: 0,
        })
    }
}

fn successors(t: &Terminator) -> Vec<usize> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::Branch(_, a, b) => vec![*a, *b],
        Terminator::Call(_, _, _, n) => vec![*n],
        Terminator::Ret | Terminator::Unreachable => vec![],
    }
}

/// Drops blocks unreachable from `bb0`, renumbering the rest in their
/// original relative order.
fn prune(blocks: Vec<Block>) -> Vec<Block> {
    let mut live = vec![false; blocks.len()];
    let mut work = vec![0usize];
    while let Some(b) = work.pop() {
        if live[b] {
            continue;
        }
        live[b] = true;
        work.extend(successors(&blocks[b].term));
    }
    let mut remap = vec![usize::MAX; blocks.len()];
    let mut n = 0;
    for (i, l) in live.iter().enumerate() {
        if *l {
            remap[i] = n;
            n += 1;
        }
    }
    let r = |b: usize| remap[b];
    blocks
        .into_iter()
        .enumerate()
        .filter(|(i, _)| live[*i])
        .map(|(_, b)| Block {
            stmts: b.stmts,
            term: match b.term {
                Terminator::Goto(t) => Terminator::Goto(r(t)),
                Terminator::Branch(c, t, f) => Terminator::Branch(c, r(t), r(f)),
                Terminator::Call(s, a, d, nx) => Terminator::Call(s, a, d, r(nx)),
                other => other,
            },
        })
        .collect()
}

fn lower_function(shared: &mut Shared<'_>, f: &RawFunction) -> Result<Body> {
    let sig = shared.sig(&f.symbol)?;
    let (params, ret) = (sig.params.clone(), sig.ret.clone());
    let (abi_cxx, param_non_null) = (sig.abi_cxx, sig.param_non_null.clone());
    if !f.is_definition {
        return Ok(Body {
            identity: f.symbol.clone(),
            is_external: true,
            sig: Signature { params, ret, abi_cxx, param_non_null },
            locals: vec![],
            blocks: vec![],
            entry_block: 0,
        });
    }
    if sig.is_variadic {
        return unsupported(format!("variadic definition `{}`", f.symbol));
    }
    let body = f.body.as_ref().expect("definitions have bodies (checked at parse)");
    for p in &f.params {
        if p.dtor_symbol.is_some() {
            return unsupported(format!(
                "`{}`: by-value parameter `{}` with a non-trivial destructor",
                f.symbol, p.name
            ));
        }
    }
    let mut escaped = HashSet::new();
    collect_escaped_stmt(body, &mut escaped);
    let mut written_vars = HashSet::new();
    collect_written_vars_stmt(body, &mut written_vars);
    for ci in &f.ctor_inits {
        if let RawCtorInit::Field { init, .. } | RawCtorInit::Base { init, .. } = ci {
            collect_escaped(init, &mut escaped);
            collect_written_vars_expr(init, &mut written_vars);
        }
    }
    let mut top_level_vars = HashSet::new();
    if let RawStmt::Compound(v) = body {
        for s in v {
            if let RawStmt::Decl { var_id, .. } = s {
                top_level_vars.insert(*var_id);
            }
        }
    }
    let mut locals =
        vec![LocalDecl { ty: ret.clone(), is_param: false, debug_name: "return".into() }];
    for (p, t) in f.params.iter().zip(&params) {
        locals.push(LocalDecl { ty: t.clone(), is_param: true, debug_name: p.name.clone() });
    }
    let mut fl = FnLower {
        shared,
        symbol: f.symbol.clone(),
        ret_ty: ret,
        num_params: params.len(),
        locals,
        var_map: HashMap::new(),
        blocks: vec![(Vec::new(), None)],
        cur: 0,
        targets: Vec::new(),
        switches: Vec::new(),
        labels: HashMap::new(),
        defined_labels: HashSet::new(),
        label_scopes: HashMap::new(),
        pending_gotos: Vec::new(),
        scope_ids: Vec::new(),
        next_scope_id: 0,
        escaped,
        written_vars,
        top_level_vars,
        temp_counter: 0,
        scopes: Vec::new(),
        fe_temps: Vec::new(),
        fe_entry_bb: None,
        cond_depth: 0,
        in_cond: false,
        has_this: f.params.first().is_some_and(|p| p.is_this),
        ret_is_ref: matches!(f.return_ty, RawType::Ref { .. }),
        dtor_epilogue: Vec::new(),
        abi_cxx,
        param_non_null,
    };
    let mut statics = Vec::new();
    collect_static_consts(body, &mut statics);
    for s in statics {
        fl.hoist_static_const(s)?;
    }
    if fl.shared.cxx {
        // A virtual method's body is ordinary code; virtual dispatch is Rung 2
        // and is rejected at every call site (and every polymorphic record).
        if !f.ctor_inits.is_empty() {
            fl.ctor_inits(&f.ctor_inits)?;
        }
        if f.method_kind == MethodKind::Dtor {
            let this_ty = fl.this_ty()?;
            for d in &f.subobject_dtors {
                let dtor = checked_dtor(&d.dtor_symbol)?;
                let arg = match (d.field_idx, d.offset_bytes) {
                    (Some(idx), _) => {
                        let base = Place::local(1).with(Proj::Deref);
                        let (fp, fty) = fl.field_place(base, &d.record_id, idx)?;
                        Expr::AddrOf(fp, ptr_to(&fty))
                    }
                    (None, Some(0)) => {
                        let bty = Ty::Record(d.record_id.clone());
                        Expr::PtrCast(
                            ptr_to(&bty),
                            Box::new(Expr::ReadPlace(Place::local(1), this_ty.clone())),
                        )
                    }
                    _ => {
                        return unsupported(format!(
                            "destructor of base `{}` at a non-zero or virtual offset",
                            d.record_id
                        ))
                    }
                };
                fl.dtor_epilogue.push((arg, dtor));
            }
        }
    } else if f.method_kind != MethodKind::Free || !f.ctor_inits.is_empty() {
        return malformed(format!("C++ member function `{}` in a C bundle", f.symbol));
    }
    fl.stmt(body)?;
    if fl.shared.cxx && fl.ret_ty == Ty::Void && fl.blocks[fl.cur].1.is_none() {
        fl.epilogue()?;
    }
    fl.finish()
}

/// Records whose layout the program depends on: every record type that
/// appears in a lowered body other than as the pointee of a pointer type,
/// closed under by-value fields.
fn records_used_by_value(
    bodies: &[Body],
    records: &HashMap<String, Result<(RecordDef, BTreeSet<String>)>>,
) -> BTreeSet<String> {
    fn ty(t: &Ty, out: &mut BTreeSet<String>) {
        match t {
            Ty::Record(r) => {
                out.insert(r.clone());
            }
            Ty::Array(e, _) => ty(e, out),
            Ty::Void | Ty::Bool | Ty::Int(..) | Ty::Ptr(..) => {}
        }
    }
    fn place(p: &Place, out: &mut BTreeSet<String>) {
        for proj in &p.projs {
            match proj {
                Proj::Deref => {}
                Proj::Field(r, _, t) => {
                    out.insert(r.clone());
                    ty(t, out);
                }
                Proj::Index(t, _) => ty(t, out),
                Proj::Bitfield(r, ..) => {
                    out.insert(r.clone());
                }
            }
        }
    }
    fn expr(e: &Expr, out: &mut BTreeSet<String>) {
        match e {
            Expr::ConstInt(..) | Expr::ConstBool(_) => {}
            Expr::NullPtr(t) => ty(t, out),
            Expr::ReadPlace(p, t) | Expr::AddrOf(p, t) => {
                place(p, out);
                ty(t, out);
            }
            Expr::Unary(_, t, a) | Expr::PtrCast(t, a) => {
                ty(t, out);
                expr(a, out);
            }
            Expr::Binary(_, t, a, b) => {
                ty(t, out);
                expr(a, out);
                expr(b, out);
            }
            Expr::IntCast(.., a) | Expr::IntToBool(a) | Expr::BoolToInt(_, _, a) => expr(a, out),
            Expr::PtrAdd(el, t, a, b) => {
                ty(el, out);
                ty(t, out);
                expr(a, out);
                expr(b, out);
            }
            Expr::BitCast(f, t, a) => {
                ty(f, out);
                ty(t, out);
                expr(a, out);
            }
        }
    }
    let mut out = BTreeSet::new();
    for b in bodies {
        for t in b.sig.params.iter().chain([&b.sig.ret]).chain(b.locals.iter().map(|l| &l.ty)) {
            ty(t, &mut out);
        }
        for blk in &b.blocks {
            for st in &blk.stmts {
                match st {
                    Stmt::StorageLive(_) | Stmt::StorageDead(_) => {}
                    Stmt::Assign(p, t, e) => {
                        place(p, &mut out);
                        ty(t, &mut out);
                        expr(e, &mut out);
                    }
                    Stmt::ZeroInit(p, t) => {
                        place(p, &mut out);
                        ty(t, &mut out);
                    }
                }
            }
            match &blk.term {
                Terminator::Branch(c, ..) => expr(c, &mut out),
                Terminator::Call(_, args, dst, _) => {
                    for a in args {
                        expr(a, &mut out);
                    }
                    if let Some((p, t)) = dst {
                        place(p, &mut out);
                        ty(t, &mut out);
                    }
                }
                Terminator::Goto(_) | Terminator::Ret | Terminator::Unreachable => {}
            }
        }
    }
    let mut work: Vec<String> = out.iter().cloned().collect();
    while let Some(id) = work.pop() {
        if let Some(Ok((def, _))) = records.get(&id) {
            let mut fields = BTreeSet::new();
            for f in &def.fields {
                ty(&f.ty, &mut fields);
            }
            for r in fields {
                if out.insert(r.clone()) {
                    work.push(r);
                }
            }
        }
    }
    out
}

fn lower_record(r: &crate::raw::RawRecord) -> Result<(RecordDef, BTreeSet<String>)> {
    if r.is_polymorphic {
        return unsupported(format!("polymorphic record `{}` (virtual dispatch is Rung 2)", r.id));
    }
    let mut used = BTreeSet::new();
    let mut fields = Vec::with_capacity(r.fields.len());
    for f in &r.fields {
        let ty = match lower_ty(&f.ty, &mut used) {
            Ok(t) => t,
            Err(e) => return unsupported(format!("record `{}` field `{}`: {e}", r.id, f.name)),
        };
        fields.push(FieldDecl {
            name: f.name.clone(),
            offset_bits: f.offset_bits,
            bit_width: f.bit_width,
            ty,
        });
    }
    Ok((
        RecordDef {
            record_id: r.id.clone(),
            is_union: r.is_union,
            size_bytes: r.size_bytes,
            align_bytes: r.align_bytes,
            fields,
        },
        used,
    ))
}

/// A lowered function with the records it names and the global-load stubs
/// it calls.
type LoweredFn = (Body, BTreeSet<String>, BTreeMap<String, Ty>);

pub fn lower_bundle(b: &RawBundle, opts: &Options) -> Result<Program> {
    let policy = check_policy(&b.lang_policy)?;

    let mut records = HashMap::new();
    for r in &b.records {
        if records.insert(r.id.clone(), lower_record(r)).is_some() {
            return malformed(format!("duplicate record id `{}`", r.id));
        }
    }

    let cxx = b.lang_policy.is_cplusplus;
    let record_dtors: HashMap<String, Option<String>> =
        b.records.iter().map(|r| (r.id.clone(), r.dtor_symbol.clone())).collect();
    let record_subobjects: HashMap<&str, Vec<String>> = b
        .records
        .iter()
        .map(|r| {
            let mut subs = r.base_ids.clone();
            for f in &r.fields {
                raw_type_record_ids(&f.ty, &mut subs);
            }
            (r.id.as_str(), subs)
        })
        .collect();
    let close_records = |mut set: HashSet<String>| -> HashSet<String> {
        let mut changed = true;
        while changed {
            changed = false;
            for r in &b.records {
                if !set.contains(&r.id)
                    && record_subobjects
                        .get(r.id.as_str())
                        .is_some_and(|subs| subs.iter().any(|s| set.contains(s)))
                {
                    set.insert(r.id.clone());
                    changed = true;
                }
            }
        }
        set
    };
    let mutable_records =
        close_records(b.records.iter().filter(|r| r.has_mutable).map(|r| r.id.clone()).collect());
    let mut not_copyable_seed: HashSet<String> = b
        .records
        .iter()
        .filter(|r| {
            !r.is_trivially_copyable || r.dtor_symbol.is_some() || r.has_address_dependent_ctor
        })
        .map(|r| r.id.clone())
        .collect();
    if cxx {
        for f in &b.functions {
            if ctor_observes_this(f) {
                if let Some(p0) = f.params.first() {
                    if let RawType::Ptr { pointee, .. } = &p0.ty {
                        if let RawType::Record { id } = &**pointee {
                            not_copyable_seed.insert(id.clone());
                        }
                    }
                }
            }
        }
    }
    let not_copyable = close_records(not_copyable_seed);
    let mut sigs = HashMap::new();
    let mut sig_errors = HashMap::new();
    // Records named by each function's signature.
    let mut sig_records: HashMap<&str, BTreeSet<String>> = HashMap::new();
    for f in &b.functions {
        let mut used = BTreeSet::new();
        let sig = (|| {
            let mut params = Vec::with_capacity(f.params.len());
            let mut param_non_null = Vec::with_capacity(f.params.len());
            for p in &f.params {
                params.push(lower_ty(&p.ty, &mut used)?);
                param_non_null.push(p.is_this || matches!(p.ty, RawType::Ref { .. }));
            }
            let ret = lower_ty(&f.return_ty, &mut used)?;
            check_abi(f, &params, &ret, cxx, &not_copyable)?;
            Ok(FnSig {
                params,
                ret,
                is_variadic: f.is_variadic,
                abi_cxx: cxx && !f.is_extern_c,
                param_non_null,
            })
        })();
        let fresh = match sig {
            Ok(sig) => sigs.insert(f.symbol.clone(), sig).is_none(),
            Err(e) => sig_errors.insert(f.symbol.clone(), e).is_none(),
        };
        if !fresh || sig_records.insert(&f.symbol, used).is_some() {
            return malformed(format!("duplicate function symbol `{}`", f.symbol));
        }
    }

    let entry_def_id = match &opts.entry {
        None => 0,
        Some(sym) => {
            match b.functions.iter().position(|f| &f.symbol == sym || &f.unmangled_name == sym) {
                Some(i) => i,
                None => return malformed(format!("entry `{sym}` is not in the bundle")),
            }
        }
    };
    match b.functions.get(entry_def_id) {
        Some(f) if f.is_definition => {}
        _ => return malformed("entry function is missing or has no definition"),
    }

    let mut shared = Shared {
        cxx,
        record_dtors: &record_dtors,
        mutable_records: &mutable_records,
        records: &records,
        sigs: &sigs,
        sig_errors: &sig_errors,
        used_records: BTreeSet::new(),
        global_stubs: BTreeMap::new(),
    };
    // Each function is lowered with its own record and global-stub
    // accumulators so that functions left out below contribute nothing.
    let mut lower_one = |f: &RawFunction| -> Result<LoweredFn> {
        shared.used_records = sig_records[f.symbol.as_str()].clone();
        shared.global_stubs = BTreeMap::new();
        let body = lower_function(&mut shared, f)?;
        Ok((
            body,
            std::mem::take(&mut shared.used_records),
            std::mem::take(&mut shared.global_stubs),
        ))
    };
    let mut lowered: Vec<Option<LoweredFn>> = b.functions.iter().map(|_| None).collect();
    if opts.entry.is_none() {
        for (i, f) in b.functions.iter().enumerate() {
            lowered[i] = Some(lower_one(f)?);
        }
    } else {
        // With an explicit entry, lower only the functions its lowered body
        // can call, transitively. Edges are read from the lowered IR, so
        // they include implicit constructor and destructor calls; a
        // function outside this set can never run, and constructs it alone
        // uses cannot block the entry.
        let index: HashMap<&str, usize> =
            b.functions.iter().enumerate().map(|(i, f)| (f.symbol.as_str(), i)).collect();
        let mut work = vec![entry_def_id];
        while let Some(i) = work.pop() {
            if lowered[i].is_some() {
                continue;
            }
            let l = lower_one(&b.functions[i])?;
            for blk in &l.0.blocks {
                if let Terminator::Call(sym, ..) = &blk.term {
                    match index.get(sym.as_str()) {
                        Some(j) => work.push(*j),
                        None if sym.starts_with(GLOBAL_LOAD_STUB_PREFIX) => {}
                        None => return malformed(format!("call to `{sym}` outside the bundle")),
                    }
                }
            }
            lowered[i] = Some(l);
        }
    }
    let mut bodies = Vec::with_capacity(b.functions.len());
    let mut used_records = BTreeSet::new();
    let mut global_stubs: BTreeMap<String, Ty> = BTreeMap::new();
    let mut entry_out = 0;
    for (i, l) in lowered.into_iter().enumerate() {
        let Some((body, used, stubs)) = l else { continue };
        if i == entry_def_id {
            entry_out = bodies.len();
        }
        bodies.push(body);
        used_records.extend(used);
        for (stub, ty) in stubs {
            match global_stubs.get(&stub) {
                Some(prev) if *prev != ty => {
                    return malformed(format!("global `{stub}` read at two types"))
                }
                _ => {
                    global_stubs.insert(stub, ty);
                }
            }
        }
    }
    for (stub, ty) in &global_stubs {
        if sigs.contains_key(stub) || sig_errors.contains_key(stub) {
            return malformed(format!("synthesized stub `{stub}` collides with a function"));
        }
        bodies.push(Body {
            identity: stub.clone(),
            is_external: true,
            sig: Signature::c(vec![], ty.clone()),
            locals: vec![],
            blocks: vec![],
            entry_block: 0,
        });
    }

    // Transitive closure of referenced records, emitted in bundle order. A
    // non-polymorphic record that cannot be lowered (for example, one with a
    // function-pointer field) is left out when the program only ever names
    // it as a pointee: no lowered operation needs its layout, and the
    // semantics fails closed on an unknown record if one ever does.
    let by_value = records_used_by_value(&bodies, &records);
    let polymorphic: BTreeSet<&str> =
        b.records.iter().filter(|r| r.is_polymorphic).map(|r| r.id.as_str()).collect();
    let mut needed = BTreeSet::new();
    let mut opaque = BTreeSet::new();
    let mut work: Vec<String> = used_records.into_iter().collect();
    while let Some(id) = work.pop() {
        if !needed.insert(id.clone()) {
            continue;
        }
        match records.get(&id) {
            None => return malformed(format!("reference to unknown record `{id}`")),
            Some(Err(e)) if by_value.contains(&id) || polymorphic.contains(id.as_str()) => {
                return Err(e.clone())
            }
            Some(Err(_)) => {
                opaque.insert(id);
            }
            Some(Ok((_, deps))) => work.extend(deps.iter().cloned()),
        }
    }
    let records_out = b
        .records
        .iter()
        .filter(|r| needed.contains(&r.id) && !opaque.contains(&r.id))
        .map(|r| match &records[&r.id] {
            Ok((def, _)) => def.clone(),
            Err(_) => unreachable!("checked during closure"),
        })
        .collect();

    Ok(Program {
        policy,
        is_partial: bodies.iter().any(|b| b.is_external),
        records: records_out,
        bodies,
        entry_def_id: entry_out,
    })
}
