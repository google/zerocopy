// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Human-readable rendering of captured types and runtime values.

use anneal_mir_eval::{Mutability, OrderingVal, Ty, Val};

pub(super) fn format_ty(ty: &Ty) -> String {
    match ty {
        Ty::Bool => "bool".into(),
        Ty::Char => "char".into(),
        Ty::Ordering => "Ordering".into(),
        Ty::Unit => "()".into(),
        Ty::Never => "!".into(),
        Ty::Int(ity) => ity.width.rust_name(ity.signed).into(),
        Ty::Enum(ety) => format!("enum#{}", ety.id),
        Ty::OverflowPair(ity) => format!("({}, bool)", ity.width.rust_name(ity.signed)),
        Ty::Tuple { fields } => {
            let inner: Vec<String> = fields.iter().map(format_ty).collect();
            format!("({})", inner.join(", "))
        }
        Ty::Ref { mutability, pointee } => {
            let prefix = match mutability {
                Mutability::Shared => "&",
                Mutability::Mut => "&mut ",
            };
            format!("{prefix}{}", format_ty(pointee))
        }
        Ty::RawPtr { mutability, pointee } => {
            let prefix = match mutability {
                Mutability::Shared => "*const ",
                Mutability::Mut => "*mut ",
            };
            format!("{prefix}{}", format_ty(pointee))
        }
        Ty::Slice { elem } => format!("[{}]", format_ty(elem)),
        Ty::Str => "str".into(),
        Ty::RangeTo { elem } => format!("RangeTo<{}>", format_ty(elem)),
        Ty::RangeFrom { elem } => format!("RangeFrom<{}>", format_ty(elem)),
        Ty::Range { elem } => format!("Range<{}>", format_ty(elem)),
        Ty::Option { elem } => format!("Option<{}>", format_ty(elem)),
        Ty::Array { elem, len } => format!("[{}; {len}]", format_ty(elem)),
        Ty::Unsupported => "<unsupported>".into(),
    }
}

pub(super) fn format_val(val: &Val) -> String {
    match val {
        Val::Scalar(sv) => {
            if sv.signed {
                format!("{}{}", sv.to_signed_i128(), sv.width.rust_name(true))
            } else {
                format!("{}{}", sv.truncated_bits(), sv.width.rust_name(false))
            }
        }
        Val::Ptr(p) => match p.alloc_id {
            Some(aid) => format!("ptr(alloc#{aid}+{})", p.offset_bytes),
            None => format!("ptr(addr={:#x})", p.offset_bytes),
        },
        Val::SlicePtr { ptr, len } => match ptr.alloc_id {
            Some(aid) => format!("slice(alloc#{aid}+{}, len={len})", ptr.offset_bytes),
            None => format!("slice(addr={:#x}, len={len})", ptr.offset_bytes),
        },
        Val::Bool(b) => b.to_string(),
        Val::Char(c) => format!("{c:?}"),
        Val::Ordering(OrderingVal::Less) => "Ordering::Less".into(),
        Val::Ordering(OrderingVal::Equal) => "Ordering::Equal".into(),
        Val::Ordering(OrderingVal::Greater) => "Ordering::Greater".into(),
        Val::Unit => "()".into(),
        Val::EnumVal { ty, variant } => {
            let discr = ty.discriminants.get(*variant).copied().unwrap_or(0);
            format!("enum#{}::v{}(discr={discr})", ty.id, variant)
        }
        Val::Tuple(fields) => {
            let parts: Vec<String> = fields.iter().map(format_val).collect();
            format!("({})", parts.join(", "))
        }
        Val::RangeTo(end) => format!("..{end}"),
        Val::RangeFrom(start) => format!("{start}.."),
        Val::OptionVal(None) => "None".into(),
        Val::OptionVal(Some(inner)) => format!("Some({})", format_val(inner)),
        Val::Bytes(bs) => format!("[{} bytes]", bs.len()),
    }
}
