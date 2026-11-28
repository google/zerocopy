// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Boundary candidate arguments for each probed parameter type.

use alloc::{boxed::Box, vec, vec::Vec};

use super::{ArgCandidate, materialize_case, shift_val_allocs_down};
use crate::{
    ir::{IntTy, IntWidth, Mutability, Ty},
    memory::{Allocation, TargetEndian, encode_val, int_layout, layout_of_ty},
    value::{
        AllocByte, OrderingVal, PtrVal, ScalarVal, Val, enum_admitted, is_supported_v2_local_ty,
    },
};

fn boundary_values_for_int(ity: IntTy) -> Vec<Val> {
    let bits = ity.width.bits();
    let mask = ity.width.mask();
    let mut raw_candidates: Vec<u128> = Vec::new();
    let mut push = |raw: u128| {
        let masked = raw & mask;
        if !raw_candidates.contains(&masked) {
            raw_candidates.push(masked);
        }
    };

    push(0);
    push(1);
    push(2);
    push(u128::from(bits.saturating_sub(1)));
    push(u128::from(bits));
    if ity.signed {
        let smin_bits = if bits == 128 { 1u128 << 127 } else { 1u128 << (bits - 1) };
        let smax_bits = smin_bits - 1;
        push(u128::MAX); // -1
        push(mask.wrapping_sub(1)); // -2
        push(smin_bits);
        push(smin_bits.wrapping_add(1));
        push(smax_bits);
        push(smax_bits.saturating_sub(1));
        push((-(bits as i128)) as u128);
    } else {
        push(mask);
        push(mask.saturating_sub(1));
        push(mask / 2);
        push((mask / 2).saturating_add(1));
    }
    for shift in [4u32, 7, 8, 15, 16, 31, 32, 63, 64] {
        if shift < bits {
            push(1u128 << shift);
            push((1u128 << shift) - 1);
        }
    }

    raw_candidates
        .into_iter()
        .map(|raw| Val::Scalar(ScalarVal::new(ity.width, ity.signed, raw)))
        .collect()
}

fn sample_slice_bytes(elem_size: usize, elem_count: usize) -> Vec<AllocByte> {
    let total = elem_size * elem_count;
    (0..total)
        .map(|i| AllocByte::Init { byte: ((i * 37 + 0x11) & 0xff) as u8, prov: None })
        .collect()
}

fn boundary_candidates_for_ref(
    mutability: Mutability,
    pointee: &Ty,
    endian: TargetEndian,
) -> Option<Vec<ArgCandidate>> {
    match pointee {
        Ty::Slice { elem } => {
            let Ty::Int(ity) = elem.as_ref() else {
                return None;
            };
            let lay = int_layout(ity.width);
            let elem_size = lay.size as usize;
            let align_addr = 1u64 << lay.align_log2;
            let mut out = Vec::new();
            // 1. Empty dangling slice (`NonNull::dangling()`, `len = 0`).
            out.push(ArgCandidate::pure(Val::SlicePtr {
                ptr: PtrVal { alloc_id: None, offset_bytes: align_addr, width: IntWidth::Isize },
                len: 0,
            }));
            // 2. Empty live allocation slice (`len = 0`).
            out.push(ArgCandidate {
                val: Val::SlicePtr {
                    ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
                    len: 0,
                },
                allocs: vec![Allocation {
                    alloc_id: 1,
                    align_log2: lay.align_log2,
                    mutability,
                    bytes: Vec::new(),
                    live: true,
                }],
            });
            // 3. Single-element and 4-element initialized slices.
            for count in [1usize, 4usize] {
                out.push(ArgCandidate {
                    val: Val::SlicePtr {
                        ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
                        len: count as u64,
                    },
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability,
                        bytes: sample_slice_bytes(elem_size, count),
                        live: true,
                    }],
                });
            }
            // 4. Non-zero offset subslice (offset = elem_size, len = 2 of 4).
            out.push(ArgCandidate {
                val: Val::SlicePtr {
                    ptr: PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: lay.size,
                        width: IntWidth::Isize,
                    },
                    len: 2,
                },
                allocs: vec![Allocation {
                    alloc_id: 1,
                    align_log2: lay.align_log2,
                    mutability,
                    bytes: sample_slice_bytes(elem_size, 4),
                    live: true,
                }],
            });
            Some(out)
        }
        Ty::Str => {
            // Shared `&str`: an empty dangling string, ASCII, multi-byte
            // UTF-8, a substring at a non-zero offset, and initialized
            // non-UTF-8 bytes. `ValidEntryArgsV2` admits the last one because
            // `refValidInMem` requires only initialized bytes.
            let mut out = vec![ArgCandidate::pure(Val::SlicePtr {
                ptr: PtrVal { alloc_id: None, offset_bytes: 1, width: IntWidth::Isize },
                len: 0,
            })];
            let multi_byte = "\u{e9}\u{1f600}".as_bytes();
            let offset = "xy\u{20ac}".as_bytes();
            for (bytes, offset_bytes, len) in
                [(&b"a"[..], 0, 1), (multi_byte, 0, 6), (offset, 2, 3), (&[0xFF, 0xC0][..], 0, 2)]
            {
                out.push(ArgCandidate {
                    val: Val::SlicePtr {
                        ptr: PtrVal { alloc_id: Some(1), offset_bytes, width: IntWidth::Isize },
                        len,
                    },
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: 0,
                        mutability,
                        bytes: bytes
                            .iter()
                            .map(|&byte| AllocByte::Init { byte, prov: None })
                            .collect(),
                        live: true,
                    }],
                });
            }
            Some(out)
        }
        other => {
            let lay = layout_of_ty(other, true)?;
            let pointee_vals = boundary_candidates_for_ty(other, true, endian)?;
            if pointee_vals.is_empty() {
                // `&!` / `&mut !` is uninhabited because `refValidInMem`
                // requires a valid pointee value.
                return Some(Vec::new());
            }
            let mut out = Vec::new();
            if lay.size == 0 {
                // Valid dangling ZST reference (`NonNull::dangling()`).
                out.push(ArgCandidate::pure(Val::Ptr(PtrVal {
                    alloc_id: None,
                    offset_bytes: 1u64 << lay.align_log2,
                    width: IntWidth::Isize,
                })));
            }
            for cand in pointee_vals.into_iter().take(4) {
                let bytes = encode_val(endian, other, &cand.val, true).ok()?;
                out.push(ArgCandidate {
                    val: Val::Ptr(PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: 0,
                        width: IntWidth::Isize,
                    }),
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability,
                        bytes,
                        live: true,
                    }],
                });
            }
            Some(out)
        }
    }
}

fn boundary_candidates_for_raw_ptr(
    mutability: Mutability,
    pointee: &Ty,
    endian: TargetEndian,
) -> Option<Vec<ArgCandidate>> {
    match pointee {
        Ty::Slice { elem } => {
            let Ty::Int(ity) = elem.as_ref() else {
                return None;
            };
            let lay = int_layout(ity.width);
            let elem_size = lay.size as usize;
            let mut out = Vec::new();
            // Valid live 4-element raw slice pointer.
            out.push(ArgCandidate {
                val: Val::SlicePtr {
                    ptr: PtrVal { alloc_id: Some(1), offset_bytes: 0, width: IntWidth::Isize },
                    len: 4,
                },
                allocs: vec![Allocation {
                    alloc_id: 1,
                    align_log2: lay.align_log2,
                    mutability: Mutability::Mut,
                    bytes: sample_slice_bytes(elem_size, 4),
                    live: true,
                }],
            });
            // Null raw slice pointers (empty and non-empty).
            for len in [0u64, 4u64] {
                out.push(ArgCandidate::pure(Val::SlicePtr {
                    ptr: PtrVal { alloc_id: None, offset_bytes: 0, width: IntWidth::Isize },
                    len,
                }));
            }
            // Dangling provenance-free raw slice pointer.
            out.push(ArgCandidate::pure(Val::SlicePtr {
                ptr: PtrVal {
                    alloc_id: None,
                    offset_bytes: 1u64 << lay.align_log2,
                    width: IntWidth::Isize,
                },
                len: 0,
            }));
            Some(out)
        }
        other => {
            let lay = layout_of_ty(other, true)?;
            let mut out = Vec::new();
            // 1. Valid live mutable aligned allocation (for inhabited pointee).
            if let Some(pointee_cands) = boundary_candidates_for_ty(other, true, endian)
                && let Some(first) = pointee_cands.first()
                && let Ok(bytes) = encode_val(endian, other, &first.val, true)
            {
                let mut padded = bytes.clone();
                if lay.size > 0 {
                    padded.extend_from_slice(&bytes);
                }
                out.push(ArgCandidate {
                    val: Val::Ptr(PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: 0,
                        width: IntWidth::Isize,
                    }),
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability: Mutability::Mut,
                        bytes: padded,
                        live: true,
                    }],
                });
            }
            // 2. Null raw pointer.
            out.push(ArgCandidate::pure(Val::Ptr(PtrVal {
                alloc_id: None,
                offset_bytes: 0,
                width: IntWidth::Isize,
            })));
            // 3. Non-null dangling aligned provenance-free pointer.
            out.push(ArgCandidate::pure(Val::Ptr(PtrVal {
                alloc_id: None,
                offset_bytes: 1u64 << lay.align_log2,
                width: IntWidth::Isize,
            })));
            // 4. Dead (deallocated) allocation.
            out.push(ArgCandidate {
                val: Val::Ptr(PtrVal {
                    alloc_id: Some(1),
                    offset_bytes: 0,
                    width: IntWidth::Isize,
                }),
                allocs: vec![Allocation {
                    alloc_id: 1,
                    align_log2: lay.align_log2,
                    mutability: Mutability::Mut,
                    bytes: vec![AllocByte::Init { byte: 0, prov: None }; lay.size as usize],
                    live: false,
                }],
            });
            // 5. Out-of-bounds offset inside live allocation.
            out.push(ArgCandidate {
                val: Val::Ptr(PtrVal {
                    alloc_id: Some(1),
                    offset_bytes: lay.size.max(1),
                    width: IntWidth::Isize,
                }),
                allocs: vec![Allocation {
                    alloc_id: 1,
                    align_log2: lay.align_log2,
                    mutability: Mutability::Mut,
                    bytes: vec![AllocByte::Init { byte: 0, prov: None }; lay.size as usize],
                    live: true,
                }],
            });
            // 6. Misaligned pointer when ABI alignment > 1.
            if lay.align_log2 > 0 {
                out.push(ArgCandidate {
                    val: Val::Ptr(PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: 1,
                        width: IntWidth::Isize,
                    }),
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability: Mutability::Mut,
                        bytes: vec![
                            AllocByte::Init { byte: 0, prov: None };
                            (lay.size as usize) + 4
                        ],
                        live: true,
                    }],
                });
            }
            // 7. Immutable allocation for `*mut T` (catches WriteToReadOnly).
            if mutability == Mutability::Mut && lay.size > 0 {
                out.push(ArgCandidate {
                    val: Val::Ptr(PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: 0,
                        width: IntWidth::Isize,
                    }),
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability: Mutability::Shared,
                        bytes: vec![AllocByte::Init { byte: 0, prov: None }; lay.size as usize],
                        live: true,
                    }],
                });
            }
            // 8. Uninitialized allocation for non-ZST pointee.
            if lay.size > 0 {
                out.push(ArgCandidate {
                    val: Val::Ptr(PtrVal {
                        alloc_id: Some(1),
                        offset_bytes: 0,
                        width: IntWidth::Isize,
                    }),
                    allocs: vec![Allocation {
                        alloc_id: 1,
                        align_log2: lay.align_log2,
                        mutability: Mutability::Mut,
                        bytes: vec![AllocByte::Uninit; lay.size as usize],
                        live: true,
                    }],
                });
            }
            Some(out)
        }
    }
}

pub(super) fn boundary_candidates_for_ty(
    ty: &Ty,
    enable_profile_v2: bool,
    endian: TargetEndian,
) -> Option<Vec<ArgCandidate>> {
    if let Some(ity) = ty.as_overflow_pair() {
        let mut out = Vec::new();
        for int_val in boundary_values_for_int(ity) {
            if let Val::Scalar(sv) = int_val {
                out.push(ArgCandidate::pure(Val::overflow_pair(sv, false)));
                out.push(ArgCandidate::pure(Val::overflow_pair(sv, true)));
            }
        }
        return Some(out);
    }
    match ty {
        Ty::Never => Some(Vec::new()),
        Ty::Unit => Some(vec![ArgCandidate::pure(Val::Unit)]),
        Ty::Bool => {
            Some(vec![ArgCandidate::pure(Val::Bool(false)), ArgCandidate::pure(Val::Bool(true))])
        }
        Ty::Ordering => Some(vec![
            ArgCandidate::pure(Val::Ordering(OrderingVal::Less)),
            ArgCandidate::pure(Val::Ordering(OrderingVal::Equal)),
            ArgCandidate::pure(Val::Ordering(OrderingVal::Greater)),
        ]),
        Ty::Char => Some(
            ['\0', 'a', 'A', '\u{7f}', '\u{80}', '\u{d7ff}', '\u{e000}', '\u{10ffff}']
                .into_iter()
                .map(|c| ArgCandidate::pure(Val::Char(c)))
                .collect(),
        ),
        Ty::Int(ity) => {
            Some(boundary_values_for_int(*ity).into_iter().map(ArgCandidate::pure).collect())
        }
        Ty::Enum(ety) => {
            if !enum_admitted(ety) {
                return None;
            }
            let cap = ety.discriminants.len().min(16);
            Some(
                (0..cap)
                    .map(|variant| ArgCandidate::pure(Val::EnumVal { ty: ety.clone(), variant }))
                    .collect(),
            )
        }
        Ty::RangeTo { elem } if enable_profile_v2 && elem.is_usize() => Some(
            [0u64, 1, 2, 4, u64::MAX / 2, u64::MAX]
                .into_iter()
                .map(|end| ArgCandidate::pure(Val::RangeTo(end)))
                .collect(),
        ),
        Ty::RangeFrom { elem } if enable_profile_v2 && elem.is_usize() => Some(
            [0u64, 1, 2, 4, u64::MAX / 2, u64::MAX]
                .into_iter()
                .map(|start| ArgCandidate::pure(Val::RangeFrom(start)))
                .collect(),
        ),
        Ty::Ref { mutability, pointee } if enable_profile_v2 && is_supported_v2_local_ty(ty) => {
            boundary_candidates_for_ref(*mutability, pointee, endian)
        }
        Ty::RawPtr { mutability, pointee } if enable_profile_v2 && is_supported_v2_local_ty(ty) => {
            boundary_candidates_for_raw_ptr(*mutability, pointee, endian)
        }
        Ty::Tuple { fields } if enable_profile_v2 => {
            if fields.is_empty() {
                return Some(vec![ArgCandidate::pure(Val::Tuple(Vec::new()))]);
            }
            let mut per_field = Vec::with_capacity(fields.len());
            let mut uninhabited = false;
            for f in fields {
                // Validate every field shape before short-circuiting on an
                // uninhabited field (so `(Never, Unsupported)` returns `None`,
                // not `Some([])`).
                let vals = boundary_candidates_for_ty(f, true, endian)?;
                if vals.is_empty() {
                    uninhabited = true;
                }
                per_field.push(vals);
            }
            if uninhabited {
                return Some(Vec::new());
            }
            let max_len = per_field.iter().map(Vec::len).max().unwrap_or(1);
            let mut tuples = Vec::with_capacity(max_len);
            for i in 0..max_len {
                let mut field_cands = Vec::with_capacity(per_field.len());
                for vs in &per_field {
                    field_cands.push(vs[i % vs.len()].clone());
                }
                let (vals, cm) = materialize_case(&field_cands);
                // Re-base allocation ids back to `1..=k` for template storage.
                let base_shift = 1u64;
                let norm_vals: Vec<Val> =
                    vals.into_iter().map(|v| shift_val_allocs_down(&v, base_shift)).collect();
                let norm_allocs: Vec<Allocation> = cm
                    .allocations
                    .into_iter()
                    .map(|mut a| {
                        a.alloc_id -= base_shift;
                        a
                    })
                    .collect();
                tuples.push(ArgCandidate { val: Val::Tuple(norm_vals), allocs: norm_allocs });
            }
            Some(tuples)
        }
        Ty::Option { elem } if enable_profile_v2 && is_supported_v2_local_ty(ty) => {
            let inner_cands = boundary_candidates_for_ty(elem, true, endian)?;
            let mut out = Vec::with_capacity(1 + inner_cands.len());
            out.push(ArgCandidate::pure(Val::OptionVal(None)));
            for cand in inner_cands {
                out.push(ArgCandidate {
                    val: Val::OptionVal(Some(Box::new(cand.val))),
                    allocs: cand.allocs,
                });
            }
            Some(out)
        }
        _ => None,
    }
}
