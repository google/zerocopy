// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure scalar arithmetic, bitwise, shift, unary, comparison, and cast
//! semantics matching `Trusted.MirSemantics.Ops`.

use crate::{
    ir::{BinOp, CastKind, IntWidth, Ty, UnOp},
    value::{FaultDetail, OrderingVal, ScalarVal, Val},
};

/// Exact mathematical integer decoded from a `ScalarVal`.
/// Using a tagged representation avoids truncating unsigned `u128` values above
/// `i128::MAX` while supporting full signed `i128` arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DecodedInt {
    Signed(i128),
    Unsigned(u128),
}

impl DecodedInt {
    fn from_scalar(sv: ScalarVal) -> Self {
        if sv.signed {
            Self::Signed(sv.to_signed_i128())
        } else {
            Self::Unsigned(sv.truncated_bits())
        }
    }

    fn cmp_vals(self, rhs: Self) -> OrderingVal {
        let ord = match (self, rhs) {
            (Self::Signed(a), Self::Signed(b)) => a.cmp(&b),
            (Self::Unsigned(a), Self::Unsigned(b)) => a.cmp(&b),
            (Self::Signed(a), Self::Unsigned(b)) => {
                if a < 0 {
                    core::cmp::Ordering::Less
                } else {
                    (a as u128).cmp(&b)
                }
            }
            (Self::Unsigned(a), Self::Signed(b)) => {
                if b < 0 {
                    core::cmp::Ordering::Greater
                } else {
                    a.cmp(&(b as u128))
                }
            }
        };
        match ord {
            core::cmp::Ordering::Less => OrderingVal::Less,
            core::cmp::Ordering::Equal => OrderingVal::Equal,
            core::cmp::Ordering::Greater => OrderingVal::Greater,
        }
    }
}

/// Truncate signed `value : i128` to `(w, true)` and report whether the value
/// wrapped outside `w`'s signed range.
const fn truncate_signed(w: IntWidth, value: i128) -> (ScalarVal, bool) {
    let raw = (value as u128) & w.mask();
    let sv = ScalarVal { width: w, signed: true, bits: raw };
    let decoded = sv.to_signed_i128();
    (sv, decoded != value)
}

/// Truncate unsigned `value : u128` to `(w, false)` and report whether the
/// value exceeded `w`'s unsigned range.
const fn truncate_unsigned(w: IntWidth, value: u128) -> (ScalarVal, bool) {
    let raw = value & w.mask();
    let sv = ScalarVal { width: w, signed: false, bits: raw };
    (sv, raw != value)
}

const fn signed_min_i128(w: IntWidth) -> i128 {
    let bits = w.bits();
    if bits == 128 { i128::MIN } else { -(1i128 << (bits - 1)) }
}

/// Evaluate a shift operator (`.shl`, `.shr`, `.shl_unchecked`,
/// `.shr_unchecked`) matching `Trusted.MirSemantics.evalShiftOp`.
fn eval_shift_op(
    op: BinOp,
    w: IntWidth,
    signed: bool,
    lhs: ScalarVal,
    rhs: ScalarVal,
) -> Result<Val, FaultDetail> {
    let bit_width = u128::from(w.bits());
    let (amount, overflow) = match DecodedInt::from_scalar(rhs) {
        DecodedInt::Signed(r) => {
            let bw = bit_width as i128;
            let rem = r.rem_euclid(bw);
            (rem as u32, rem != r)
        }
        DecodedInt::Unsigned(r) => {
            let rem = r % bit_width;
            (rem as u32, rem != r)
        }
    };

    let sv = if signed {
        let l = lhs.to_signed_i128();
        let shifted = match op {
            BinOp::Shl | BinOp::ShlUnchecked => l.wrapping_shl(amount),
            BinOp::Shr | BinOp::ShrUnchecked => l.wrapping_shr(amount),
            _ => {
                return Err(FaultDetail::unsupported("non-shift op dispatched to shift evaluator"));
            }
        };
        // Wrap to `w`: note `truncate_scalar` in Lean returns `sv` regardless
        // of signed/lossy shift truncation, and only `overflow && isUnchecked`
        // faults with `Undefined`.
        ScalarVal::new(w, true, shifted as u128)
    } else {
        let l = lhs.truncated_bits();
        let shifted = match op {
            BinOp::Shl | BinOp::ShlUnchecked => l.wrapping_shl(amount),
            BinOp::Shr | BinOp::ShrUnchecked => l.wrapping_shr(amount),
            _ => {
                return Err(FaultDetail::unsupported("non-shift op dispatched to shift evaluator"));
            }
        };
        ScalarVal::new(w, false, shifted)
    };

    if overflow && op.is_unchecked() {
        Err(FaultDetail::undefined("unchecked shift amount out of range"))
    } else {
        Ok(Val::Scalar(sv))
    }
}

/// Evaluate integer arithmetic (`.add`, `.sub`, `.mul`, `.div`, `.rem`,
/// `*_unchecked`, `*_with_overflow`) matching `Trusted.MirSemantics.evalArithOp`.
fn eval_arith_op(
    op: BinOp,
    w: IntWidth,
    signed: bool,
    lhs: ScalarVal,
    rhs: ScalarVal,
) -> Result<Val, FaultDetail> {
    let is_div_or_rem = matches!(op, BinOp::Div | BinOp::Rem);
    if signed {
        let l = lhs.to_signed_i128();
        let r = rhs.to_signed_i128();
        if is_div_or_rem && r == 0 {
            return Err(FaultDetail::undefined("signed integer division or remainder by zero"));
        }
        if is_div_or_rem && l == signed_min_i128(w) && r == -1 {
            return Err(FaultDetail::undefined("signed integer MIN / -1 or MIN % -1 overflow"));
        }
        let (raw_128, host_overflow) = match op {
            BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => l.overflowing_add(r),
            BinOp::Sub | BinOp::SubUnchecked | BinOp::SubWithOverflow => l.overflowing_sub(r),
            BinOp::Mul | BinOp::MulUnchecked | BinOp::MulWithOverflow => l.overflowing_mul(r),
            BinOp::Div => l.overflowing_div(r),
            BinOp::Rem => l.overflowing_rem(r),
            _ => return Err(FaultDetail::unsupported("unsupported arithmetic operator")),
        };
        let (sv, lossy) = truncate_signed(w, raw_128);
        let overflowed = host_overflow || lossy;
        if overflowed && op.is_unchecked() {
            Err(FaultDetail::undefined("unchecked signed arithmetic overflow"))
        } else if op.is_overflowing() {
            Ok(Val::overflow_pair(sv, overflowed))
        } else {
            Ok(Val::Scalar(sv))
        }
    } else {
        let l = lhs.truncated_bits();
        let r = rhs.truncated_bits();
        if is_div_or_rem && r == 0 {
            return Err(FaultDetail::undefined("unsigned integer division or remainder by zero"));
        }
        let (raw_128, host_overflow) = match op {
            BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => l.overflowing_add(r),
            BinOp::Sub | BinOp::SubUnchecked | BinOp::SubWithOverflow => l.overflowing_sub(r),
            BinOp::Mul | BinOp::MulUnchecked | BinOp::MulWithOverflow => l.overflowing_mul(r),
            BinOp::Div => l.overflowing_div(r),
            BinOp::Rem => l.overflowing_rem(r),
            _ => return Err(FaultDetail::unsupported("unsupported arithmetic operator")),
        };
        let (sv, lossy) = truncate_unsigned(w, raw_128);
        let overflowed = host_overflow || lossy;
        if overflowed && op.is_unchecked() {
            Err(FaultDetail::undefined("unchecked unsigned arithmetic overflow"))
        } else if op.is_overflowing() {
            Ok(Val::overflow_pair(sv, overflowed))
        } else {
            Ok(Val::Scalar(sv))
        }
    }
}

/// Evaluate a MIR binary operator matching `Trusted.MirSemantics.evalBinOp`.
pub fn eval_bin_op(op: BinOp, lhs: &Val, rhs: &Val) -> Result<Val, FaultDetail> {
    match (lhs, rhs) {
        (Val::Scalar(l), Val::Scalar(r)) => {
            let w = l.width;
            let s = l.signed;
            if op.is_shift() {
                return eval_shift_op(op, w, s, *l, *r);
            }
            if l.width != r.width || l.signed != r.signed {
                return Err(FaultDetail::unsupported(
                    "non-shift scalar binary op requires matching operand types",
                ));
            }
            let l_int = DecodedInt::from_scalar(*l);
            let r_int = DecodedInt::from_scalar(*r);
            match op {
                BinOp::Eq => Ok(Val::Bool(l_int == r_int)),
                BinOp::Ne => Ok(Val::Bool(l_int != r_int)),
                BinOp::Lt => Ok(Val::Bool(l_int.cmp_vals(r_int) == OrderingVal::Less)),
                BinOp::Le => Ok(Val::Bool(l_int.cmp_vals(r_int) != OrderingVal::Greater)),
                BinOp::Gt => Ok(Val::Bool(l_int.cmp_vals(r_int) == OrderingVal::Greater)),
                BinOp::Ge => Ok(Val::Bool(l_int.cmp_vals(r_int) != OrderingVal::Less)),
                BinOp::Cmp => Ok(Val::Ordering(l_int.cmp_vals(r_int))),
                BinOp::BitAnd => {
                    Ok(Val::Scalar(ScalarVal::new(w, s, l.truncated_bits() & r.truncated_bits())))
                }
                BinOp::BitOr => {
                    Ok(Val::Scalar(ScalarVal::new(w, s, l.truncated_bits() | r.truncated_bits())))
                }
                BinOp::BitXor => {
                    Ok(Val::Scalar(ScalarVal::new(w, s, l.truncated_bits() ^ r.truncated_bits())))
                }
                BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Rem
                | BinOp::AddUnchecked
                | BinOp::SubUnchecked
                | BinOp::MulUnchecked
                | BinOp::AddWithOverflow
                | BinOp::SubWithOverflow
                | BinOp::MulWithOverflow => eval_arith_op(op, w, s, *l, *r),
                BinOp::Offset
                | BinOp::Shl
                | BinOp::ShlUnchecked
                | BinOp::Shr
                | BinOp::ShrUnchecked => {
                    Err(FaultDetail::unsupported("unsupported scalar binary operator"))
                }
            }
        }
        (Val::Bool(l), Val::Bool(r)) => match op {
            BinOp::Eq => Ok(Val::Bool(l == r)),
            BinOp::Ne => Ok(Val::Bool(l != r)),
            BinOp::Lt => Ok(Val::Bool(!l && *r)),
            BinOp::Le => Ok(Val::Bool(!l || *r)),
            BinOp::Gt => Ok(Val::Bool(*l && !r)),
            BinOp::Ge => Ok(Val::Bool(*l || !r)),
            BinOp::BitAnd => Ok(Val::Bool(*l && *r)),
            BinOp::BitOr => Ok(Val::Bool(*l || *r)),
            BinOp::BitXor => Ok(Val::Bool(*l ^ *r)),
            _ => Err(FaultDetail::unsupported("unsupported binary operator on bool")),
        },
        (Val::Char(l), Val::Char(r)) => match op {
            BinOp::Eq => Ok(Val::Bool(l == r)),
            BinOp::Ne => Ok(Val::Bool(l != r)),
            BinOp::Lt => Ok(Val::Bool(l < r)),
            BinOp::Le => Ok(Val::Bool(l <= r)),
            BinOp::Gt => Ok(Val::Bool(l > r)),
            BinOp::Ge => Ok(Val::Bool(l >= r)),
            BinOp::Cmp => Ok(Val::Ordering(match l.cmp(r) {
                core::cmp::Ordering::Less => OrderingVal::Less,
                core::cmp::Ordering::Equal => OrderingVal::Equal,
                core::cmp::Ordering::Greater => OrderingVal::Greater,
            })),
            _ => Err(FaultDetail::unsupported("unsupported binary operator on char")),
        },
        _ => Err(FaultDetail::unsupported("mismatched or non-primitive binary op operands")),
    }
}

/// Evaluate a MIR unary operator matching `Trusted.MirSemantics.evalUnOp`.
pub fn eval_un_op(op: UnOp, val: &Val) -> Result<Val, FaultDetail> {
    match (op, val) {
        (UnOp::Not, Val::Bool(b)) => Ok(Val::Bool(!b)),
        (UnOp::Not, Val::Scalar(sv)) => {
            Ok(Val::Scalar(ScalarVal::new(sv.width, sv.signed, !sv.truncated_bits())))
        }
        (UnOp::Neg, Val::Scalar(sv)) => {
            if sv.signed {
                Ok(Val::Scalar(ScalarVal::new(sv.width, true, sv.truncated_bits().wrapping_neg())))
            } else {
                Err(FaultDetail::unsupported("UnOp::Neg requires a signed integer"))
            }
        }
        _ => Err(FaultDetail::unsupported("unsupported unary operator or operand type")),
    }
}

/// Extract the `u128` intermediate of an integer-like cast source (`Scalar`,
/// `Bool`, or `Char`), sign-extending signed integers to 128 bits.
pub fn int_like_bits(val: &Val) -> Option<u128> {
    match val {
        Val::Scalar(sv) => {
            if sv.signed {
                Some(sv.to_signed_i128() as u128)
            } else {
                Some(sv.truncated_bits())
            }
        }
        Val::Bool(b) => Some(if *b { 1 } else { 0 }),
        Val::Char(c) => Some(u128::from(u32::from(*c))),
        _ => None,
    }
}

/// Evaluate `CastKind::IntToInt` matching `Trusted.MirSemantics.evalIntToIntCast`.
pub fn eval_int_to_int_cast(kind: CastKind, val: &Val, cast_ty: &Ty) -> Result<Val, FaultDetail> {
    if kind != CastKind::IntToInt {
        return Err(FaultDetail::unsupported("cast kind outside IntToInt"));
    }
    let Some(bits) = int_like_bits(val) else {
        return Err(FaultDetail::unsupported("cast source is not integer-like"));
    };
    match cast_ty {
        Ty::Int(ity) => Ok(Val::Scalar(ScalarVal::new(ity.width, ity.signed, bits))),
        Ty::Char => {
            if bits <= 255 {
                Ok(Val::Char(char::from(bits as u8)))
            } else {
                Err(FaultDetail::unsupported("IntToInt cast to char requires u8-range value"))
            }
        }
        _ => Err(FaultDetail::unsupported("IntToInt target type is not integer or char")),
    }
}
