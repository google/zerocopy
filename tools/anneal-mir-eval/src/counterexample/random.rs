// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! SplitMix64 pseudorandom candidate arguments for probed parameter types.

use alloc::{boxed::Box, string::String, vec, vec::Vec};

use super::{
    ArgCandidate, boundary::boundary_candidates_for_ty, materialize_case, shift_val_allocs_down,
};
use crate::{
    ir::{IntWidth, Ty},
    memory::{Allocation, TargetEndian, int_layout},
    value::{
        AllocByte, OrderingVal, PtrVal, ScalarVal, Val, enum_admitted, is_supported_v2_local_ty,
    },
};

pub(super) struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    pub(super) const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    pub(super) fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub(super) fn next_u128(&mut self) -> u128 {
        let hi = u128::from(self.next_u64());
        let lo = u128::from(self.next_u64());
        (hi << 64) | lo
    }

    pub(super) fn choose_index(&mut self, len: usize) -> usize {
        if len <= 1 { 0 } else { (self.next_u64() % (len as u64)) as usize }
    }
}

pub(super) fn random_candidate_for_ty(
    ty: &Ty,
    boundary_pool: &[ArgCandidate],
    rng: &mut SplitMix64,
    enable_profile_v2: bool,
    endian: TargetEndian,
) -> Option<ArgCandidate> {
    if !boundary_pool.is_empty() && (rng.next_u64() & 1) == 0 {
        return Some(boundary_pool[rng.choose_index(boundary_pool.len())].clone());
    }
    if let Some(ity) = ty.as_overflow_pair() {
        let bits = rng.next_u128() & ity.width.mask();
        let sv = ScalarVal::new(ity.width, ity.signed, bits);
        return Some(ArgCandidate::pure(Val::overflow_pair(sv, (rng.next_u64() & 1) == 1)));
    }
    match ty {
        Ty::Never => None,
        Ty::Unit => Some(ArgCandidate::pure(Val::Unit)),
        Ty::Bool => Some(ArgCandidate::pure(Val::Bool((rng.next_u64() & 1) == 1))),
        Ty::Ordering => Some(ArgCandidate::pure(match rng.next_u64() % 3 {
            0 => Val::Ordering(OrderingVal::Less),
            1 => Val::Ordering(OrderingVal::Equal),
            _ => Val::Ordering(OrderingVal::Greater),
        })),
        Ty::Char => {
            let candidate = rng.next_u64() % 0x11_0000;
            let val = char::from_u32(candidate as u32).unwrap_or('a');
            Some(ArgCandidate::pure(Val::Char(val)))
        }
        Ty::Int(ity) => Some(ArgCandidate::pure(Val::Scalar(ScalarVal::new(
            ity.width,
            ity.signed,
            rng.next_u128(),
        )))),
        Ty::Enum(ety) if enum_admitted(ety) => {
            let idx = rng.choose_index(ety.discriminants.len());
            Some(ArgCandidate::pure(Val::EnumVal { ty: ety.clone(), variant: idx }))
        }
        Ty::RangeTo { elem } if enable_profile_v2 && elem.is_usize() => {
            Some(ArgCandidate::pure(Val::RangeTo(rng.next_u64() % 16)))
        }
        Ty::RangeFrom { elem } if enable_profile_v2 && elem.is_usize() => {
            Some(ArgCandidate::pure(Val::RangeFrom(rng.next_u64() % 16)))
        }
        Ty::Ref { mutability, pointee } if enable_profile_v2 && is_supported_v2_local_ty(ty) => {
            if let Ty::Slice { elem } = pointee.as_ref()
                && let Ty::Int(ity) = elem.as_ref()
            {
                let lay = int_layout(ity.width);
                let count = (rng.next_u64() % 9) as usize;
                let total = (lay.size as usize) * count;
                let bytes: Vec<AllocByte> = (0..total)
                    .map(|_| AllocByte::Init { byte: (rng.next_u64() & 0xff) as u8, prov: None })
                    .collect();
                return Some(ArgCandidate {
                    val: Val::SlicePtr {
                        ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
                        len: count as u64,
                    },
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability: *mutability,
                        bytes,
                        live: true,
                    }],
                });
            }
            if **pointee == Ty::Str {
                // A random valid UTF-8 string of up to 8 one- to four-byte
                // characters.
                const CHARS: [char; 5] = ['a', 'Z', '\u{e9}', '\u{20ac}', '\u{1f600}'];
                let count = (rng.next_u64() % 9) as usize;
                let mut text = String::new();
                for _ in 0..count {
                    text.push(CHARS[rng.choose_index(CHARS.len())]);
                }
                return Some(ArgCandidate {
                    val: Val::SlicePtr {
                        ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
                        len: text.len() as u64,
                    },
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: 0,
                        mutability: *mutability,
                        bytes: text
                            .bytes()
                            .map(|byte| AllocByte::Init { byte, prov: None })
                            .collect(),
                        live: true,
                    }],
                });
            }
            (!boundary_pool.is_empty())
                .then(|| boundary_pool[rng.choose_index(boundary_pool.len())].clone())
        }
        Ty::RawPtr { .. } if enable_profile_v2 && is_supported_v2_local_ty(ty) => (!boundary_pool
            .is_empty())
        .then(|| boundary_pool[rng.choose_index(boundary_pool.len())].clone()),
        Ty::Tuple { fields } if enable_profile_v2 => {
            let mut field_cands = Vec::with_capacity(fields.len());
            for f in fields {
                let pool = boundary_candidates_for_ty(f, true, endian)?;
                field_cands.push(random_candidate_for_ty(f, &pool, rng, true, endian)?);
            }
            let (vals, cm) = materialize_case(&field_cands);
            let norm_vals: Vec<Val> =
                vals.into_iter().map(|v| shift_val_allocs_down(&v, 1)).collect();
            let norm_allocs: Vec<Allocation> = cm
                .allocations
                .into_iter()
                .map(|mut a| {
                    a.alloc_id -= 1;
                    a
                })
                .collect();
            Some(ArgCandidate { val: Val::Tuple(norm_vals), allocs: norm_allocs })
        }
        Ty::Option { elem } if enable_profile_v2 && is_supported_v2_local_ty(ty) => {
            if (rng.next_u64() & 3) == 0 {
                return Some(ArgCandidate::pure(Val::OptionVal(None)));
            }
            let pool = boundary_candidates_for_ty(elem, true, endian)?;
            if pool.is_empty() {
                return Some(ArgCandidate::pure(Val::OptionVal(None)));
            }
            let inner = random_candidate_for_ty(elem, &pool, rng, true, endian)?;
            Some(ArgCandidate {
                val: Val::OptionVal(Some(Box::new(inner.val))),
                allocs: inner.allocs,
            })
        }
        _ => None,
    }
}
