// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Single-Side-Effect Normal Form (SSENF) sequencing gate.
//!
//! Clang's AST fixes no evaluation order for unsequenced operands (C11 6.5p2,
//! 6.5.2.2p10), but `Trusted.CppAst` is a linear three-address IR. Lowering
//! an expression to a single order is exact only if every order the C
//! abstract machine permits yields the same observable result. This module
//! proves that syntactically, failing closed otherwise:
//!
//! * Operands of every operator except `&&`, `||`, `,`, and `?:` are
//!   unsequenced siblings, as are the left (address) and right (value)
//!   operands of `=` / `op=`, the base and index of `[]`, and all call
//!   arguments (indeterminately sequenced when they contain calls).
//! * Two siblings conflict if one writes a local the other reads or writes,
//!   or if one performs a memory write or call while the other performs a
//!   memory read, memory write, or call. Locals whose address is taken
//!   anywhere in the function are also treated as memory.
//! * The store performed by `=`, `op=`, `++`, or `--` is unsequenced with the
//!   side effects (but not the value computations) of its operands, so the
//!   stored location must not also be written by an operand (`x = x++`,
//!   `x = (x = 1) + 1`).
//!
//! This is deliberately stricter than C11 (for example it rejects
//! `f() + g()`, whose behavior is merely unspecified, and `x = f(x++)`), so
//! acceptance implies every permitted order agrees on every state.

use std::collections::{BTreeSet, HashSet};

use crate::{
    error::{LowerError, Result},
    raw::{BinaryOp, CastKind, RawExpr, RawExprKind, RawStmt, UnaryOp},
};

/// Effects of evaluating one subexpression.
#[derive(Debug, Clone, Default)]
pub struct Footprint {
    pub reads: BTreeSet<u32>,
    pub writes: BTreeSet<u32>,
    /// Number of non-call memory writes.
    pub mem_writes: usize,
    /// Number of calls (each may read and write arbitrary memory).
    pub calls: usize,
    pub mem_reads: bool,
}

impl Footprint {
    pub fn mem_writes_or_calls(&self) -> usize {
        self.mem_writes + self.calls
    }

    fn union(mut self, other: Footprint) -> Footprint {
        self.reads.extend(other.reads);
        self.writes.extend(other.writes);
        self.mem_writes += other.mem_writes;
        self.calls += other.calls;
        self.mem_reads |= other.mem_reads;
        self
    }
}

/// The storage location designated by an lvalue.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Loc {
    Var(u32),
    Mem,
}

pub struct Ssenf<'a> {
    /// Locals whose address is taken somewhere in the function.
    escaped: &'a HashSet<u32>,
}

fn conflict(a: &Footprint, b: &Footprint) -> Option<String> {
    if let Some(v) = a.writes.intersection(&b.writes).next() {
        return Some(format!("both operands write variable #{v}"));
    }
    if let Some(v) = a.writes.intersection(&b.reads).next() {
        return Some(format!("one operand writes variable #{v} that the other reads"));
    }
    if let Some(v) = b.writes.intersection(&a.reads).next() {
        return Some(format!("one operand writes variable #{v} that the other reads"));
    }
    if a.mem_writes_or_calls() > 0 && b.mem_writes_or_calls() > 0 {
        return Some("both operands write memory or call functions".to_owned());
    }
    if (a.mem_writes_or_calls() > 0 && b.mem_reads) || (b.mem_writes_or_calls() > 0 && a.mem_reads)
    {
        return Some("one operand writes memory or calls while the other reads memory".to_owned());
    }
    None
}

fn reject<T>(what: &str, why: String) -> Result<T> {
    Err(LowerError::UnsequencedSideEffects { detail: format!("{what}: {why}") })
}

fn check_siblings(what: &str, fps: &[Footprint]) -> Result<()> {
    for i in 0..fps.len() {
        for j in (i + 1)..fps.len() {
            if let Some(why) = conflict(&fps[i], &fps[j]) {
                return reject(what, why);
            }
        }
    }
    Ok(())
}

/// Collects every local whose address may escape: operands of `&` and arrays
/// that decay to pointers (rooted at a local).
pub fn collect_escaped(e: &RawExpr, out: &mut HashSet<u32>) {
    let root_var = glvalue_root_var;
    match &e.kind {
        // `local_array[i]` decays the array only to index it; that is not an
        // escape of its address.
        RawExprKind::ArraySubscript { base, idx } => {
            if let RawExprKind::Cast { kind: CastKind::ArrayToPointerDecay, sub } =
                &strip_parens(base).kind
            {
                // Skip only the decay itself: `sub` may still escape locals
                // (a reference-returning call, a nested subscript, ...).
                collect_escaped(sub, out);
                collect_escaped(idx, out);
                return;
            }
        }
        RawExprKind::Unary { op: UnaryOp::AddrOf, sub } => {
            if let Some(v) = root_var(sub) {
                out.insert(v);
            }
        }
        RawExprKind::Cast { kind: CastKind::ArrayToPointerDecay, sub } => {
            if let Some(v) = root_var(sub) {
                out.insert(v);
            }
        }
        // C++: binding a reference or the implicit object parameter passes
        // the object's address.
        RawExprKind::Call {
            implicit_object, implicit_object_is_ptr, args, param_is_ref, ..
        } => {
            if let (Some(o), false) = (implicit_object, implicit_object_is_ptr) {
                if let Some(v) = root_var(o) {
                    out.insert(v);
                }
            }
            for (a, r) in args.iter().zip(param_is_ref) {
                if let (true, Some(v)) = (*r, root_var(a)) {
                    out.insert(v);
                }
            }
        }
        RawExprKind::Construct { args, param_is_ref, .. } => {
            for (a, r) in args.iter().zip(param_is_ref) {
                if let (true, Some(v)) = (*r, root_var(a)) {
                    out.insert(v);
                }
            }
        }
        _ => {}
    }
    for child in children(e) {
        collect_escaped(child, out);
    }
}

/// The local variable a glvalue designates (or a subobject of), if any:
/// taking its address, or binding a reference to it, lets the local be
/// accessed through memory.
pub fn glvalue_root_var(e: &RawExpr) -> Option<u32> {
    match &e.kind {
        RawExprKind::VarRef { var_id, is_ref_binding: false, .. } => Some(*var_id),
        RawExprKind::Paren { sub } | RawExprKind::ExprWithCleanups { sub } => glvalue_root_var(sub),
        RawExprKind::Cast { kind: CastKind::Noop | CastKind::DerivedToBase { .. }, sub }
            if e.is_lvalue =>
        {
            glvalue_root_var(sub)
        }
        RawExprKind::Member { base, is_arrow: false, .. } => glvalue_root_var(base),
        RawExprKind::ArraySubscript { base, .. } => match &strip_parens(base).kind {
            RawExprKind::Cast { kind: CastKind::ArrayToPointerDecay, sub } => glvalue_root_var(sub),
            _ => None,
        },
        // C++: an assignment designates its left operand.
        RawExprKind::Binary { op: BinaryOp::Assign | BinaryOp::CompoundAssign(_), lhs, .. }
            if e.is_lvalue =>
        {
            glvalue_root_var(lhs)
        }
        _ => None,
    }
}

fn strip_parens(e: &RawExpr) -> &RawExpr {
    match &e.kind {
        RawExprKind::Paren { sub } => strip_parens(sub),
        _ => e,
    }
}

pub fn children(e: &RawExpr) -> Vec<&RawExpr> {
    match &e.kind {
        RawExprKind::IntLit { .. }
        | RawExprKind::BoolLit { .. }
        | RawExprKind::VarRef { .. }
        | RawExprKind::GlobalRef { .. }
        | RawExprKind::SizeofOrAlignof { .. }
        | RawExprKind::CxxThis
        | RawExprKind::NullptrLit
        | RawExprKind::ImplicitValueInit
        | RawExprKind::Unsupported { .. } => vec![],
        RawExprKind::Unary { sub, .. }
        | RawExprKind::Cast { sub, .. }
        | RawExprKind::ExprWithCleanups { sub }
        | RawExprKind::MaterializeTemporary { sub, .. }
        | RawExprKind::BindTemporary { sub, .. }
        | RawExprKind::BuiltinBitCast { sub, .. }
        | RawExprKind::Paren { sub } => vec![sub],
        RawExprKind::Construct { args, .. } => args.iter().collect(),
        RawExprKind::Binary { lhs, rhs, .. } => vec![lhs, rhs],
        RawExprKind::Conditional { cond, then_expr, else_expr } => {
            vec![cond, then_expr, else_expr]
        }
        RawExprKind::ArraySubscript { base, idx } => vec![base, idx],
        RawExprKind::Member { base, .. } => vec![base],
        RawExprKind::Call { args, implicit_object, .. } => {
            implicit_object.iter().map(|b| &**b).chain(args.iter()).collect()
        }
        RawExprKind::InitList { inits, .. } => inits.iter().collect(),
        RawExprKind::CompoundLiteral { init, .. } => vec![init],
    }
}

/// Collects every local variable directly written (whole or through a
/// subobject projection) inside `e`.
pub fn collect_written_vars_expr(e: &RawExpr, out: &mut HashSet<u32>) {
    fn collect_target_vars(target: &RawExpr, out: &mut HashSet<u32>) {
        match &target.kind {
            RawExprKind::VarRef { var_id, is_ref_binding: false, .. } => {
                out.insert(*var_id);
            }
            RawExprKind::Paren { sub }
            | RawExprKind::ExprWithCleanups { sub }
            | RawExprKind::MaterializeTemporary { sub, .. }
            | RawExprKind::BindTemporary { sub, .. } => collect_target_vars(sub, out),
            RawExprKind::Cast { sub, .. } if target.is_lvalue => collect_target_vars(sub, out),
            RawExprKind::Member { base, is_arrow: false, .. } => collect_target_vars(base, out),
            RawExprKind::ArraySubscript { base, .. } => {
                if let RawExprKind::Cast { kind: CastKind::ArrayToPointerDecay, sub } =
                    &strip_parens(base).kind
                {
                    collect_target_vars(sub, out);
                }
            }
            RawExprKind::Binary {
                op: BinaryOp::Assign | BinaryOp::CompoundAssign(_), lhs, ..
            } if target.is_lvalue => collect_target_vars(lhs, out),
            RawExprKind::Binary { op: BinaryOp::Comma, rhs, .. } if target.is_lvalue => {
                collect_target_vars(rhs, out)
            }
            RawExprKind::Conditional { then_expr, else_expr, .. } if target.is_lvalue => {
                collect_target_vars(then_expr, out);
                collect_target_vars(else_expr, out);
            }
            RawExprKind::Unary { op: UnaryOp::PreInc | UnaryOp::PreDec, sub }
                if target.is_lvalue =>
            {
                collect_target_vars(sub, out)
            }
            _ => {}
        }
    }

    match &e.kind {
        RawExprKind::Binary { op: BinaryOp::Assign | BinaryOp::CompoundAssign(_), lhs, .. } => {
            collect_target_vars(lhs, out);
        }
        RawExprKind::Unary {
            op: UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec,
            sub,
        } => {
            collect_target_vars(sub, out);
        }
        RawExprKind::Call {
            trivial_assign: true,
            implicit_object: Some(obj),
            implicit_object_is_ptr: false,
            ..
        } => {
            collect_target_vars(obj, out);
        }
        _ => {}
    }
    for child in children(e) {
        collect_written_vars_expr(child, out);
    }
}

/// Collects every local variable directly written inside `s`.
pub fn collect_written_vars_stmt(s: &RawStmt, out: &mut HashSet<u32>) {
    match s {
        RawStmt::Compound(v) => {
            for sub in v {
                collect_written_vars_stmt(sub, out);
            }
        }
        RawStmt::Decl { init: Some(i), .. } => collect_written_vars_expr(i, out),
        RawStmt::Expr(x) | RawStmt::Return(Some(x)) => collect_written_vars_expr(x, out),
        RawStmt::If { cond, then_branch, else_branch } => {
            collect_written_vars_expr(cond, out);
            collect_written_vars_stmt(then_branch, out);
            if let Some(b) = else_branch {
                collect_written_vars_stmt(b, out);
            }
        }
        RawStmt::While { cond, body } | RawStmt::DoWhile { body, cond } => {
            collect_written_vars_expr(cond, out);
            collect_written_vars_stmt(body, out);
        }
        RawStmt::For { init, cond, inc, body } => {
            if let Some(i) = init {
                collect_written_vars_stmt(i, out);
            }
            if let Some(c) = cond {
                collect_written_vars_expr(c, out);
            }
            if let Some(i) = inc {
                collect_written_vars_expr(i, out);
            }
            collect_written_vars_stmt(body, out);
        }
        RawStmt::Switch { cond, body } => {
            collect_written_vars_expr(cond, out);
            collect_written_vars_stmt(body, out);
        }
        RawStmt::Case { sub, .. } | RawStmt::Default { sub } | RawStmt::Label { sub, .. } => {
            collect_written_vars_stmt(sub, out)
        }
        RawStmt::Decl { init: None, .. }
        | RawStmt::Return(None)
        | RawStmt::Break
        | RawStmt::Continue
        | RawStmt::Goto { .. }
        | RawStmt::Null
        | RawStmt::Unsupported { .. } => {}
    }
}

impl<'a> Ssenf<'a> {
    pub fn new(escaped: &'a HashSet<u32>) -> Self {
        Ssenf { escaped }
    }

    /// Checks one full-expression, returning its footprint.
    pub fn check_full_expr(&self, e: &RawExpr) -> Result<Footprint> {
        self.value(e)
    }

    fn read(&self, fp: &mut Footprint, loc: Loc) {
        match loc {
            Loc::Var(v) => {
                fp.reads.insert(v);
                if self.escaped.contains(&v) {
                    fp.mem_reads = true;
                }
            }
            Loc::Mem => fp.mem_reads = true,
        }
    }

    fn write(&self, fp: &mut Footprint, loc: Loc) {
        match loc {
            Loc::Var(v) => {
                fp.writes.insert(v);
                if self.escaped.contains(&v) {
                    fp.mem_writes += 1;
                }
            }
            Loc::Mem => fp.mem_writes += 1,
        }
    }

    /// The store to `loc` must not coincide with a write performed by an
    /// operand (C11 6.5.16p3: the store is sequenced only after the operands'
    /// value computations).
    fn check_store(&self, what: &str, loc: Loc, operands: &Footprint) -> Result<()> {
        match loc {
            Loc::Var(v) => {
                if operands.writes.contains(&v) {
                    return reject(
                        what,
                        format!(
                            "the store to variable #{v} is unsequenced with another write of it"
                        ),
                    );
                }
                if self.escaped.contains(&v) && operands.mem_writes > 0 {
                    return reject(
                        what,
                        format!("the store to address-taken variable #{v} is unsequenced with a memory write"),
                    );
                }
            }
            Loc::Mem => {
                if operands.mem_writes > 0 {
                    return reject(
                        what,
                        "a memory store is unsequenced with another memory write".to_owned(),
                    );
                }
                if operands.writes.iter().any(|v| self.escaped.contains(v)) {
                    return reject(
                        what,
                        "a memory store is unsequenced with a write to an address-taken local"
                            .to_owned(),
                    );
                }
            }
        }
        Ok(())
    }

    /// Footprint of computing the address designated by an lvalue.
    fn lvalue(&self, e: &RawExpr) -> Result<(Footprint, Loc)> {
        match &e.kind {
            // A reference designates some object in memory.
            RawExprKind::VarRef { is_ref_binding: true, .. } => {
                Ok((Footprint::default(), Loc::Mem))
            }
            RawExprKind::VarRef { var_id, .. } => Ok((Footprint::default(), Loc::Var(*var_id))),
            RawExprKind::Cast { kind: CastKind::Noop | CastKind::DerivedToBase { .. }, sub }
                if e.is_lvalue =>
            {
                self.lvalue(sub)
            }
            RawExprKind::MaterializeTemporary { sub, .. } => Ok((self.value(sub)?, Loc::Mem)),
            // A fresh unnamed object, conservatively treated as memory.
            RawExprKind::CompoundLiteral { init, .. } => Ok((self.value(init)?, Loc::Mem)),
            RawExprKind::GlobalRef { .. } => Ok((Footprint::default(), Loc::Mem)),
            RawExprKind::Paren { sub } | RawExprKind::ExprWithCleanups { sub } => self.lvalue(sub),
            RawExprKind::Unary { op: UnaryOp::Deref, sub } => Ok((self.value(sub)?, Loc::Mem)),
            RawExprKind::ArraySubscript { base, idx } => {
                let (b, loc) = match &strip_parens(base).kind {
                    // `local_array[i]` designates (part of) the local itself.
                    RawExprKind::Cast { kind: CastKind::ArrayToPointerDecay, sub } => {
                        let (fp, loc) = self.lvalue(sub)?;
                        (
                            fp,
                            match loc {
                                Loc::Var(v) if !self.escaped.contains(&v) => Loc::Var(v),
                                _ => Loc::Mem,
                            },
                        )
                    }
                    _ => (self.value(base)?, Loc::Mem),
                };
                let i = self.value(idx)?;
                check_siblings("array subscript", &[b.clone(), i.clone()])?;
                Ok((b.union(i), loc))
            }
            RawExprKind::Member { base, is_arrow, .. } => {
                if *is_arrow {
                    Ok((self.value(base)?, Loc::Mem))
                } else {
                    self.lvalue(base)
                }
            }
            // C++: an assignment is an lvalue designating its left operand,
            // after the store.
            RawExprKind::Binary {
                op: BinaryOp::Assign | BinaryOp::CompoundAssign(_), lhs, ..
            } if e.is_lvalue => {
                let fp = self.value(e)?;
                Ok((fp, self.lvalue(lhs)?.1))
            }
            // Any other lvalue form is rejected later by lowering; treat it as
            // an opaque memory location here.
            _ => Ok((self.value(e)?, Loc::Mem)),
        }
    }

    fn value(&self, e: &RawExpr) -> Result<Footprint> {
        match &e.kind {
            RawExprKind::IntLit { .. }
            | RawExprKind::BoolLit { .. }
            | RawExprKind::SizeofOrAlignof { .. }
            | RawExprKind::CxxThis
            | RawExprKind::NullptrLit
            | RawExprKind::ImplicitValueInit
            | RawExprKind::Unsupported { .. } => Ok(Footprint::default()),
            RawExprKind::ExprWithCleanups { sub }
            | RawExprKind::MaterializeTemporary { sub, .. }
            | RawExprKind::CompoundLiteral { init: sub, .. } => self.value(sub),
            RawExprKind::BindTemporary { sub, .. } => {
                let mut fp = self.value(sub)?;
                fp.calls += 1;
                fp.mem_reads = true;
                Ok(fp)
            }
            RawExprKind::BuiltinBitCast { sub, .. } => {
                let (mut fp, loc) = self.lvalue(sub)?;
                self.read(&mut fp, loc);
                Ok(fp)
            }
            RawExprKind::Construct { args, param_is_ref, is_trivial, is_copy_or_move, .. } => {
                let mut fps = Vec::with_capacity(args.len());
                for (i, a) in args.iter().enumerate() {
                    let by_ref = param_is_ref.get(i).copied().unwrap_or(false);
                    fps.push(if by_ref || (*is_trivial && *is_copy_or_move) {
                        let (mut fp, loc) = self.lvalue(a)?;
                        self.read(&mut fp, loc);
                        fp
                    } else {
                        self.value(a)?
                    });
                }
                check_siblings("constructor arguments", &fps)?;
                let mut fp = fps.into_iter().fold(Footprint::default(), Footprint::union);
                if !*is_trivial {
                    fp.calls += 1;
                    fp.mem_reads = true;
                }
                Ok(fp)
            }
            // An lvalue used without conversion contributes only its address.
            RawExprKind::VarRef { .. } | RawExprKind::GlobalRef { .. } => Ok(Footprint::default()),
            RawExprKind::Paren { sub } => self.value(sub),
            RawExprKind::Cast { kind, sub } => match kind {
                CastKind::LvalueToRvalue => {
                    let (mut fp, loc) = self.lvalue(sub)?;
                    self.read(&mut fp, loc);
                    Ok(fp)
                }
                CastKind::ArrayToPointerDecay => Ok(self.lvalue(sub)?.0),
                _ => self.value(sub),
            },
            RawExprKind::Unary { op, sub } => match op {
                UnaryOp::AddrOf => Ok(self.lvalue(sub)?.0),
                UnaryOp::Deref => self.value(sub),
                UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec => {
                    let (mut fp, loc) = self.lvalue(sub)?;
                    self.check_store("increment/decrement", loc, &fp)?;
                    self.read(&mut fp, loc);
                    self.write(&mut fp, loc);
                    Ok(fp)
                }
                UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot | UnaryOp::LogNot => {
                    self.value(sub)
                }
            },
            RawExprKind::Binary { op, lhs, rhs, .. } => match op {
                BinaryOp::LogAnd | BinaryOp::LogOr | BinaryOp::Comma => {
                    Ok(self.value(lhs)?.union(self.value(rhs)?))
                }
                BinaryOp::Assign | BinaryOp::CompoundAssign(_) => {
                    let (mut l, loc) = self.lvalue(lhs)?;
                    if matches!(op, BinaryOp::CompoundAssign(_)) {
                        self.read(&mut l, loc);
                    }
                    let r = self.value(rhs)?;
                    check_siblings("assignment", &[l.clone(), r.clone()])?;
                    let mut fp = l.union(r);
                    self.check_store("assignment", loc, &fp)?;
                    self.write(&mut fp, loc);
                    Ok(fp)
                }
                _ => {
                    let l = self.value(lhs)?;
                    let r = self.value(rhs)?;
                    check_siblings("binary operator", &[l.clone(), r.clone()])?;
                    Ok(l.union(r))
                }
            },
            RawExprKind::Conditional { cond, then_expr, else_expr } => {
                Ok(self.value(cond)?.union(self.value(then_expr)?).union(self.value(else_expr)?))
            }
            RawExprKind::ArraySubscript { .. } | RawExprKind::Member { .. } => {
                Ok(self.lvalue(e)?.0)
            }
            RawExprKind::Call {
                args,
                implicit_object,
                implicit_object_is_ptr,
                param_is_ref,
                ..
            } => {
                let mut fps = Vec::with_capacity(args.len() + 1);
                if let Some(o) = implicit_object {
                    fps.push(if *implicit_object_is_ptr {
                        self.value(o)?
                    } else {
                        self.lvalue(o)?.0
                    });
                }
                for (i, a) in args.iter().enumerate() {
                    if param_is_ref.get(i).copied().unwrap_or(false) {
                        fps.push(self.lvalue(a)?.0);
                    } else {
                        fps.push(self.value(a)?);
                    }
                }
                check_siblings("call arguments", &fps)?;
                let mut fp = fps.into_iter().fold(Footprint::default(), Footprint::union);
                fp.calls += 1;
                fp.mem_reads = true;
                Ok(fp)
            }
            RawExprKind::InitList { inits, .. } => {
                let mut fps = Vec::with_capacity(inits.len());
                for i in inits {
                    fps.push(self.value(i)?);
                }
                check_siblings("initializer list", &fps)?;
                Ok(fps.into_iter().fold(Footprint::default(), Footprint::union))
            }
        }
    }
}
