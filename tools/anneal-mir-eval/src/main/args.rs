// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Command-line argument and flag parsing.

use anneal_mir_eval::{
    AllocByte, Allocation, EnumTy, IntTy, IntWidth, Mutability, OrderingVal, PtrVal, ScalarVal,
    TargetEndian, Ty, Val, int_layout,
};

use super::format::format_ty;

fn parse_int_bits(raw: &str, ity: IntTy) -> Result<ScalarVal, String> {
    let s = raw.trim();
    if ity.signed {
        if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
            let bits = u128::from_str_radix(hex, 16)
                .map_err(|e| format!("invalid signed hex '{raw}': {e}"))?;
            if bits > ity.width.mask() {
                return Err(format!("value {raw} out of range for {}", ity.width.rust_name(true)));
            }
            return Ok(ScalarVal::new(ity.width, true, bits));
        }
        let parsed =
            s.parse::<i128>().map_err(|e| format!("invalid signed integer '{raw}': {e}"))?;
        let sv = ScalarVal::new(ity.width, true, parsed as u128);
        if sv.to_signed_i128() != parsed {
            return Err(format!("value {parsed} out of range for {}", ity.width.rust_name(true)));
        }
        Ok(sv)
    } else {
        let parsed = if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
            u128::from_str_radix(hex, 16)
                .map_err(|e| format!("invalid unsigned hex '{raw}': {e}"))?
        } else {
            s.parse::<u128>().map_err(|e| format!("invalid unsigned integer '{raw}': {e}"))?
        };
        if parsed > ity.width.mask() {
            return Err(format!("value {parsed} out of range for {}", ity.width.rust_name(false)));
        }
        Ok(ScalarVal::new(ity.width, false, parsed))
    }
}

fn parse_enum_arg(raw: &str, ety: &EnumTy) -> Result<Val, String> {
    if let Some(v_str) = raw.strip_prefix("variant:").or_else(|| raw.strip_prefix('v')) {
        let variant =
            v_str.parse::<usize>().map_err(|e| format!("invalid enum variant '{raw}': {e}"))?;
        if variant >= ety.discriminants.len() {
            return Err(format!(
                "variant index {variant} out of bounds (len={})",
                ety.discriminants.len()
            ));
        }
        return Ok(Val::EnumVal { ty: ety.clone(), variant });
    }
    let sv = parse_int_bits(raw, ety.discr())?;
    let variant = ety
        .discriminants
        .iter()
        .position(|&d| d == sv.bits)
        .ok_or_else(|| format!("discriminant '{raw}' not declared in enum#{}", ety.id))?;
    Ok(Val::EnumVal { ty: ety.clone(), variant })
}

fn parse_byte_slice_arg(
    raw: &str,
    mutability: Mutability,
    allocations: &mut Vec<Allocation>,
    next_alloc_id: &mut u64,
) -> Result<Val, String> {
    let trimmed = raw.trim();
    let inner = trimmed
        .strip_prefix("bytes:")
        .or_else(|| trimmed.strip_prefix('[').and_then(|s| s.strip_suffix(']')))
        .ok_or_else(|| format!("expected byte slice as '[1,2,3]' or 'bytes:1,2,3', got '{raw}'"))?
        .trim();
    let mut bytes = Vec::new();
    if !inner.is_empty() {
        for elem in inner.split(',') {
            let sv = parse_int_bits(elem, IntTy { width: IntWidth::I8, signed: false })?;
            bytes.push(AllocByte::Init { byte: sv.bits as u8, prov: None });
        }
    }
    let aid = *next_alloc_id;
    *next_alloc_id += 1;
    let len = bytes.len() as u64;
    let lay = int_layout(IntWidth::I8);
    allocations.push(Allocation {
        alloc_id: aid,
        align_log2: lay.align_log2,
        mutability,
        bytes,
        live: true,
    });
    Ok(Val::SlicePtr {
        ptr: PtrVal { alloc_id: Some(aid), offset_bytes: 0, width: IntWidth::Isize },
        len,
    })
}

pub(super) fn parse_arg_spec(
    raw: &str,
    expected_ty: Option<&Ty>,
    allocations: &mut Vec<Allocation>,
    next_alloc_id: &mut u64,
) -> Result<Val, String> {
    if let Some((prefix, rest)) = raw.split_once(':') {
        let typed = match prefix {
            "u8" => Some(Ty::Int(IntTy { width: IntWidth::I8, signed: false })),
            "u16" => Some(Ty::Int(IntTy { width: IntWidth::I16, signed: false })),
            "u32" => Some(Ty::Int(IntTy { width: IntWidth::I32, signed: false })),
            "u64" => Some(Ty::Int(IntTy { width: IntWidth::I64, signed: false })),
            "u128" => Some(Ty::Int(IntTy { width: IntWidth::I128, signed: false })),
            "usize" => Some(Ty::Int(IntTy { width: IntWidth::Isize, signed: false })),
            "i8" => Some(Ty::Int(IntTy { width: IntWidth::I8, signed: true })),
            "i16" => Some(Ty::Int(IntTy { width: IntWidth::I16, signed: true })),
            "i32" => Some(Ty::Int(IntTy { width: IntWidth::I32, signed: true })),
            "i64" => Some(Ty::Int(IntTy { width: IntWidth::I64, signed: true })),
            "i128" => Some(Ty::Int(IntTy { width: IntWidth::I128, signed: true })),
            "isize" => Some(Ty::Int(IntTy { width: IntWidth::Isize, signed: true })),
            "bool" => Some(Ty::Bool),
            "char" => Some(Ty::Char),
            "ordering" => Some(Ty::Ordering),
            "unit" => Some(Ty::Unit),
            _ => None,
        };
        if let Some(ty) = typed {
            return parse_arg_for_ty(rest, &ty, allocations, next_alloc_id);
        }
    }
    let Some(ty) = expected_ty else {
        if raw == "()" || raw == "unit" {
            return Ok(Val::Unit);
        }
        return Err(format!("cannot infer type for argument '{raw}'; add a prefix like u32:{raw}"));
    };
    parse_arg_for_ty(raw, ty, allocations, next_alloc_id)
}

fn parse_arg_for_ty(
    raw: &str,
    ty: &Ty,
    allocations: &mut Vec<Allocation>,
    next_alloc_id: &mut u64,
) -> Result<Val, String> {
    match ty {
        Ty::Unit => {
            if raw.is_empty() || raw == "()" || raw == "unit" {
                Ok(Val::Unit)
            } else {
                Err(format!("expected unit argument, got '{raw}'"))
            }
        }
        Ty::Bool => match raw {
            "true" | "1" => Ok(Val::Bool(true)),
            "false" | "0" => Ok(Val::Bool(false)),
            _ => Err(format!("expected bool, got '{raw}'")),
        },
        Ty::Char => {
            let mut chars = raw.chars();
            if let (Some(c), None) = (chars.next(), chars.next()) {
                return Ok(Val::Char(c));
            }
            if let Some(hex) = raw.strip_prefix("U+").or_else(|| raw.strip_prefix("0x")) {
                let cp = u32::from_str_radix(hex, 16)
                    .map_err(|e| format!("invalid char scalar '{raw}': {e}"))?;
                let c = char::from_u32(cp)
                    .ok_or_else(|| format!("'{raw}' is not a Unicode scalar value"))?;
                return Ok(Val::Char(c));
            }
            Err(format!("expected single char or U+XXXX, got '{raw}'"))
        }
        Ty::Ordering => match raw {
            "less" | "Less" | "-1" => Ok(Val::Ordering(OrderingVal::Less)),
            "equal" | "Equal" | "0" => Ok(Val::Ordering(OrderingVal::Equal)),
            "greater" | "Greater" | "1" => Ok(Val::Ordering(OrderingVal::Greater)),
            _ => Err(format!("expected Ordering (less|equal|greater), got '{raw}'")),
        },
        Ty::Int(ity) => Ok(Val::Scalar(parse_int_bits(raw, *ity)?)),
        Ty::Enum(ety) => parse_enum_arg(raw, ety),
        Ty::RangeTo { elem } if elem.is_usize() => {
            let num = raw.trim().strip_prefix("..").unwrap_or(raw.trim());
            let sv = parse_int_bits(num, IntTy { width: IntWidth::Isize, signed: false })?;
            Ok(Val::RangeTo(sv.bits as u64))
        }
        Ty::RangeFrom { elem } if elem.is_usize() => {
            let num = raw.trim().strip_suffix("..").unwrap_or(raw.trim());
            let sv = parse_int_bits(num, IntTy { width: IntWidth::Isize, signed: false })?;
            Ok(Val::RangeFrom(sv.bits as u64))
        }
        Ty::Ref { mutability, pointee }
            if matches!(
                pointee.as_ref(),
                Ty::Slice { elem }
                    if matches!(
                        elem.as_ref(),
                        Ty::Int(IntTy { width: IntWidth::I8, signed: false })
                    )
            ) =>
        {
            parse_byte_slice_arg(raw, *mutability, allocations, next_alloc_id)
        }
        other => Err(format!(
            "CLI --arg parsing unsupported for parameter type {} (pass --query <query.json>)",
            format_ty(other)
        )),
    }
}

pub(super) fn next_flag_val<'a>(
    args: &'a [String],
    idx: &mut usize,
    flag: &str,
) -> Result<&'a str, String> {
    *idx += 1;
    args.get(*idx).map(String::as_str).ok_or_else(|| format!("missing value after '{flag}'"))
}

pub(super) fn parse_endian(raw: &str) -> Result<TargetEndian, String> {
    TargetEndian::from_manifest_str(raw)
        .ok_or_else(|| format!("expected 'big' or 'little' for --endian, got '{raw}'"))
}
