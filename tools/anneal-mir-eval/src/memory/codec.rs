// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Typed constant literals, integer byte orders, and value byte codecs with
//! indirect loads and stores, aligned with `Trusted.MirSemantics`'s
//! `evalConstLit`, `encodeVal`/`decodeVal`, and `loadIndirect`/`storeIndirect`.

use alloc::{vec, vec::Vec};

use super::{
    MemPlace, MemoryState, TargetEndian, layout_of_ty, overflow_pair_layout,
    refs::is_shared_str_ref,
};
use crate::{
    ir::{ConstLit, EnumTagRepr, IntWidth, Ty},
    value::{
        AllocByte, FaultDetail, OrderingVal, PtrVal, ScalarVal, UbClass, Val, check_val,
        enum_admitted, find_discr_variant, is_unicode_scalar, is_zst_enum_ty,
        tag_bits_to_discr_bits,
    },
};

/// Decode a typed constant literal matching `Trusted.MirSemantics.evalConstLit`.
pub fn eval_const_lit(ty: &Ty, lit: &ConstLit) -> Result<Val, FaultDetail> {
    eval_const_lit_with_class(ty, lit, UbClass::SyntheticInvalidConstOrSwitch)
}

fn eval_const_lit_with_class(
    ty: &Ty,
    lit: &ConstLit,
    invalid_val_class: UbClass,
) -> Result<Val, FaultDetail> {
    match (ty, lit) {
        (Ty::Int(ity), ConstLit::Scalar { bits }) => {
            if (*bits & ity.width.mask()) != *bits {
                Err(FaultDetail::unsupported("scalar constant exceeds declared width"))
            } else {
                Ok(Val::Scalar(ScalarVal::new(ity.width, ity.signed, *bits)))
            }
        }
        (Ty::Bool, ConstLit::Scalar { bits }) => {
            if (*bits & 0xff) != *bits {
                Err(FaultDetail::unsupported("bool constant exceeds 8-bit scalar"))
            } else if *bits == 0 {
                Ok(Val::Bool(false))
            } else if *bits == 1 {
                Ok(Val::Bool(true))
            } else {
                Err(FaultDetail::undefined_classified(
                    invalid_val_class,
                    "invalid boolean bit pattern",
                ))
            }
        }
        (Ty::Unit, ConstLit::ZeroSized) => Ok(Val::Unit),
        (Ty::Char, ConstLit::Scalar { bits }) => {
            if (*bits & 0xffff_ffff) != *bits {
                Err(FaultDetail::unsupported("char constant exceeds 32 bits"))
            } else if is_unicode_scalar(*bits) {
                let c = char::from_u32(*bits as u32).ok_or_else(|| {
                    FaultDetail::undefined_classified(invalid_val_class, "invalid char scalar")
                })?;
                Ok(Val::Char(c))
            } else {
                Err(FaultDetail::undefined_classified(
                    invalid_val_class,
                    "surrogate or out-of-range char scalar",
                ))
            }
        }
        (Ty::Ordering, ConstLit::Scalar { bits }) => {
            if (*bits & 0xff) != *bits {
                Err(FaultDetail::unsupported("Ordering constant exceeds 8 bits"))
            } else {
                OrderingVal::from_tag_bits(*bits).map(Val::Ordering).ok_or_else(|| {
                    FaultDetail::undefined_classified(
                        invalid_val_class,
                        "invalid Ordering discriminant tag",
                    )
                })
            }
        }
        (Ty::Enum(ety), ConstLit::ZeroSized) => {
            if is_zst_enum_ty(ety) {
                Ok(Val::EnumVal { ty: ety.clone(), variant: 0 })
            } else {
                Err(FaultDetail::unsupported("ZeroSized constant on non-ZST or unadmitted enum"))
            }
        }
        (Ty::Enum(ety), ConstLit::Scalar { bits }) => match ety.tag_repr {
            EnumTagRepr::ZeroSized => {
                Err(FaultDetail::unsupported("scalar constant for zero-sized enum"))
            }
            EnumTagRepr::Scalar(tag) => {
                if !enum_admitted(ety) || (*bits & tag.width.mask()) != *bits {
                    return Err(FaultDetail::unsupported(
                        "unadmitted enum or constant exceeding tag width",
                    ));
                }
                let discr_bits = tag_bits_to_discr_bits(tag, ety.discr_width, *bits);
                find_discr_variant(discr_bits, &ety.discriminants)
                    .map(|variant| Val::EnumVal { ty: ety.clone(), variant })
                    .ok_or_else(|| {
                        FaultDetail::undefined_classified(
                            invalid_val_class,
                            "invalid fieldless enum tag",
                        )
                    })
            }
        },
        _ => Err(FaultDetail::unsupported("unsupported constant type/literal combination")),
    }
}

/// Encode the low `n` bytes (`<= 16`) of `value` in byte order `endian`.
pub fn encode_uint(endian: TargetEndian, n: usize, value: u128) -> Vec<u8> {
    let le = value.to_le_bytes();
    let mut out: Vec<u8> = (0..n).map(|i| *le.get(i).unwrap_or(&0)).collect();
    if endian == TargetEndian::Big {
        out.reverse();
    }
    out
}

/// Decode up to 16 bytes in byte order `endian` into an unsigned `u128`.
pub fn decode_uint(endian: TargetEndian, bytes: &[u8]) -> u128 {
    let mut acc = 0u128;
    match endian {
        TargetEndian::Little => {
            for (idx, &b) in bytes.iter().enumerate() {
                if idx < 16 {
                    acc |= u128::from(b) << (idx * 8);
                }
            }
        }
        TargetEndian::Big => {
            for &b in bytes {
                acc = (acc << 8) | u128::from(b);
            }
        }
    }
    acc
}

fn init_bytes(bytes: &[AllocByte]) -> Option<Vec<u8>> {
    let mut out = Vec::with_capacity(bytes.len());
    for byte in bytes {
        match byte {
            AllocByte::Uninit => return None,
            AllocByte::Init { byte, .. } => out.push(*byte),
        }
    }
    Some(out)
}

fn init_alloc_bytes(raw: Vec<u8>, prov: Option<u64>) -> Vec<AllocByte> {
    raw.into_iter().map(|byte| AllocByte::Init { byte, prov }).collect()
}

/// Check initialization and extract uniform provenance across `bytes`,
/// matching `Trusted.MirSemantics.readPtrProv?`.
pub fn read_ptr_prov(bytes: &[AllocByte]) -> Option<Option<u64>> {
    let (first, rest) = bytes.split_first()?;
    let AllocByte::Init { prov: mut cur, .. } = *first else {
        return None;
    };
    for byte in rest {
        let AllocByte::Init { prov, .. } = *byte else {
            return None;
        };
        cur = match (cur, prov) {
            (Some(a), Some(b)) if a == b => Some(a),
            _ => None,
        };
    }
    Some(cur)
}

/// Encode runtime value `val` of type `ty` into bytes matching
/// `Trusted.MirSemantics`'s `encodeVal` (v1) and `encodeValV2` (v2).
pub fn encode_val(
    endian: TargetEndian,
    ty: &Ty,
    val: &Val,
    enable_profile_v2: bool,
) -> Result<Vec<AllocByte>, FaultDetail> {
    if !check_val(val, ty, enable_profile_v2) {
        return Err(FaultDetail::unsupported("value does not match declared storage type"));
    }
    if enable_profile_v2 {
        match (ty, val) {
            (Ty::RawPtr { pointee, .. } | Ty::Ref { pointee, .. }, Val::Ptr(p)) => {
                if pointee.is_unsized() {
                    return Err(FaultDetail::unsupported(
                        "cannot encode thin pointer for unsized pointee",
                    ));
                }
                return Ok(init_alloc_bytes(
                    encode_uint(endian, 8, u128::from(p.offset_bytes)),
                    p.alloc_id,
                ));
            }
            (Ty::RawPtr { pointee, .. } | Ty::Ref { pointee, .. }, Val::SlicePtr { ptr, len })
                if matches!(pointee.as_ref(), Ty::Slice { .. }) || is_shared_str_ref(ty) =>
            {
                let mut out = init_alloc_bytes(
                    encode_uint(endian, 8, u128::from(ptr.offset_bytes)),
                    ptr.alloc_id,
                );
                out.extend(init_alloc_bytes(encode_uint(endian, 8, u128::from(*len)), None));
                return Ok(out);
            }
            (Ty::RangeTo { elem }, Val::RangeTo(bound))
            | (Ty::RangeFrom { elem }, Val::RangeFrom(bound))
                if elem.is_usize() =>
            {
                return Ok(init_alloc_bytes(encode_uint(endian, 8, u128::from(*bound)), None));
            }
            _ => {}
        }
    }
    if let (Some(ity), Val::Tuple(fields)) = (ty.as_overflow_pair(), val)
        && fields.len() == 2
        && let (Val::Scalar(sv), Val::Bool(overflowed)) = (&fields[0], &fields[1])
    {
        let width_bytes = ity.width.byte_size();
        let mut out = init_alloc_bytes(encode_uint(endian, width_bytes, sv.bits), None);
        out.push(AllocByte::Init { byte: u8::from(*overflowed), prov: None });
        out.resize(out.len() + width_bytes - 1, AllocByte::Uninit);
        return Ok(out);
    }
    match (ty, val) {
        (Ty::Int(ity), Val::Scalar(sv)) => {
            Ok(init_alloc_bytes(encode_uint(endian, ity.width.byte_size(), sv.bits), None))
        }
        (Ty::Bool, Val::Bool(b)) => Ok(vec![AllocByte::Init { byte: u8::from(*b), prov: None }]),
        (Ty::Char, Val::Char(c)) => {
            Ok(init_alloc_bytes(encode_uint(endian, 4, u128::from(u32::from(*c))), None))
        }
        (Ty::Ordering, Val::Ordering(ord)) => {
            Ok(init_alloc_bytes(encode_uint(endian, 1, ord.tag_bits()), None))
        }
        (Ty::Unit, Val::Unit) => Ok(Vec::new()),
        (Ty::Enum(ety), Val::EnumVal { variant, .. }) => match ety.tag_repr {
            EnumTagRepr::ZeroSized => Ok(Vec::new()),
            EnumTagRepr::Scalar(tag) => {
                let Some(&disc) = ety.discriminants.get(*variant) else {
                    return Err(FaultDetail::unsupported("enum variant index out of bounds"));
                };
                Ok(init_alloc_bytes(encode_uint(endian, tag.width.byte_size(), disc), None))
            }
        },
        _ => Err(FaultDetail::unsupported("cannot encode unsupported (ty, val) pair to bytes")),
    }
}

/// Decode `bytes` of type `ty` matching `Trusted.MirSemantics.decodeVal`
/// (Profile v1) and `decodeValV2` (Profile v2).
pub fn decode_val(
    endian: TargetEndian,
    ty: &Ty,
    bytes: &[AllocByte],
    enable_profile_v2: bool,
) -> Result<Option<Val>, FaultDetail> {
    if enable_profile_v2 {
        match ty {
            Ty::RawPtr { pointee, .. } | Ty::Ref { pointee, .. } => {
                if pointee.is_unsized() {
                    if !matches!(pointee.as_ref(), Ty::Slice { .. }) && !is_shared_str_ref(ty) {
                        return Err(FaultDetail::unsupported(
                            "unsupported unsized pointer pointee",
                        ));
                    }
                    if bytes.len() != 16 {
                        return Err(FaultDetail::unsupported(
                            "wide slice pointer byte length mismatch",
                        ));
                    }
                    let (p_bytes, l_bytes) = bytes.split_at(8);
                    return match (init_bytes(p_bytes), read_ptr_prov(p_bytes), init_bytes(l_bytes))
                    {
                        (Some(p_raw), Some(prov), Some(l_raw)) => {
                            let ptr = PtrVal {
                                alloc_id: prov,
                                offset_bytes: decode_uint(endian, &p_raw) as u64,
                                width: IntWidth::Isize,
                            };
                            let len = decode_uint(endian, &l_raw) as u64;
                            Ok(Some(Val::SlicePtr { ptr, len }))
                        }
                        _ => Ok(None),
                    };
                }
                if bytes.len() != 8 {
                    return Err(FaultDetail::unsupported("thin pointer byte length mismatch"));
                }
                return match (init_bytes(bytes), read_ptr_prov(bytes)) {
                    (Some(p_raw), Some(prov)) => Ok(Some(Val::Ptr(PtrVal {
                        alloc_id: prov,
                        offset_bytes: decode_uint(endian, &p_raw) as u64,
                        width: IntWidth::Isize,
                    }))),
                    _ => Ok(None),
                };
            }
            Ty::RangeTo { elem } if elem.is_usize() => {
                if bytes.len() != 8 {
                    return Err(FaultDetail::unsupported("RangeTo byte length mismatch"));
                }
                return Ok(
                    init_bytes(bytes).map(|raw| Val::RangeTo(decode_uint(endian, &raw) as u64))
                );
            }
            Ty::RangeFrom { elem } if elem.is_usize() => {
                if bytes.len() != 8 {
                    return Err(FaultDetail::unsupported("RangeFrom byte length mismatch"));
                }
                return Ok(
                    init_bytes(bytes).map(|raw| Val::RangeFrom(decode_uint(endian, &raw) as u64))
                );
            }
            _ => {}
        }
    }
    if matches!(ty, Ty::Never) {
        return Ok(None);
    }
    if let Some(ity) = ty.as_overflow_pair() {
        let pair_layout = overflow_pair_layout(ity.width);
        if (bytes.len() as u64) != pair_layout.size {
            return Err(FaultDetail::unsupported("overflow pair byte length mismatch"));
        }
        let width_bytes = ity.width.byte_size();
        let (Some(int_raw), Some(bool_raw)) =
            (init_bytes(&bytes[..width_bytes]), init_bytes(&bytes[width_bytes..width_bytes + 1]))
        else {
            return Ok(None);
        };
        let int_val = eval_const_lit_with_class(
            &Ty::Int(ity),
            &ConstLit::Scalar { bits: decode_uint(endian, &int_raw) },
            UbClass::InvalidMemoryValue,
        )?;
        let bool_val = eval_const_lit_with_class(
            &Ty::Bool,
            &ConstLit::Scalar { bits: decode_uint(endian, &bool_raw) },
            UbClass::InvalidMemoryValue,
        )?;
        return Ok(Some(Val::Tuple(vec![int_val, bool_val])));
    }
    let Some(layout) = layout_of_ty(ty, false) else {
        return Err(FaultDetail::unsupported("type has no layout"));
    };
    if (bytes.len() as u64) != layout.size {
        return Err(FaultDetail::unsupported("byte length differs from type layout"));
    }
    if layout.size == 0 {
        let val = eval_const_lit_with_class(ty, &ConstLit::ZeroSized, UbClass::InvalidMemoryValue)?;
        return Ok(Some(val));
    }
    let Some(raw) = init_bytes(bytes) else {
        return Ok(None);
    };
    let val = eval_const_lit_with_class(
        ty,
        &ConstLit::Scalar { bits: decode_uint(endian, &raw) },
        UbClass::InvalidMemoryValue,
    )?;
    Ok(Some(val))
}

/// Load an indirect value from memory matching
/// `Trusted.MirSemantics.loadIndirect` (Profile v1) and `loadIndirectV2`
/// (Profile v2).
pub fn load_indirect(
    mem: &MemoryState,
    endian: TargetEndian,
    ty: &Ty,
    place: MemPlace,
    enable_profile_v2: bool,
) -> Result<Option<Val>, FaultDetail> {
    let Some(layout) = layout_of_ty(ty, enable_profile_v2) else {
        return Err(FaultDetail::unsupported("cannot load indirect local without layout"));
    };
    let bytes = mem.read_bytes(place, layout.size, layout.align_log2)?;
    decode_val(endian, ty, &bytes, enable_profile_v2)
}

/// Store `val` of type `ty` into an indirect memory place matching
/// `Trusted.MirSemantics.storeIndirect` / `storeIndirectV2`.
pub fn store_indirect(
    mem: &mut MemoryState,
    endian: TargetEndian,
    ty: &Ty,
    place: MemPlace,
    val: &Val,
    enable_profile_v2: bool,
) -> Result<(), FaultDetail> {
    let Some(layout) = layout_of_ty(ty, enable_profile_v2) else {
        return Err(FaultDetail::unsupported("cannot store indirect local without layout"));
    };
    let bytes = encode_val(endian, ty, val, enable_profile_v2)?;
    mem.write_bytes(place, layout.align_log2, &bytes)
}

/// Mark bytes of `ty` at `place` uninitialized (`deinitIndirect` /
/// `deinitIndirectV2`).
pub fn deinit_indirect(
    mem: &mut MemoryState,
    ty: &Ty,
    place: MemPlace,
    enable_profile_v2: bool,
) -> Result<(), FaultDetail> {
    let Some(layout) = layout_of_ty(ty, enable_profile_v2) else {
        return Err(FaultDetail::unsupported("cannot deinitialize indirect local without layout"));
    };
    mem.write_uninit(place, layout.size, layout.align_log2)
}
