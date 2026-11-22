#!/usr/bin/env python3
"""Real rustc + Miri probe for the sizedness hierarchy and `extern type` tails.

Every observation in the emitted JSON comes from a subprocess run of the selected
`rustc` / `miri` binaries on Rust sources embedded in this file.  Nothing is
replayed from a table: the `EXPECT` dictionaries below are *pins* that the fresh
observations are compared against, and a mismatch is reported (exit code 1 under
`--check`) instead of being overwritten.

Parts
  A1  one program that compiles tier witnesses for `Sized < MetaSized <
      PointeeSized`, prints pointer widths, dynamic size/align of `MetaSized`
      DSTs, zero-offset `extern type` projections, and an `&Opaque` reborrow;
      run natively and under Miri (Stacked Borrows, Tree Borrows, Tree Borrows
      without precise interior mutability, no borrow tracker).
  A2  a scenario matrix around field projection to an `extern type` tail.  The
      projecting functions live in a `#[forbid(unsafe_code)]` module (single
      file, used for Miri) and in a `#![forbid(unsafe_code)]` rlib (two-crate
      native build, at opt-level 0 and 3).  Also captures MIR and LLVM IR for
      the projecting functions.
  B   compile-only cases (accepted and rejected programs).

Usage
  python3 probe_sized_hierarchy_and_extern_types.py \
      [--toolchain nightly-YYYY-MM-DD] [--out results.json] [--check] [--no-miri]

Requirements: a nightly toolchain with the `miri` component and a built Miri
sysroot (`cargo +<toolchain> miri setup`).  Python 3.10+, standard library only.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

TIMEOUT_S = 180

# --------------------------------------------------------------------------- #
# Rust sources
# --------------------------------------------------------------------------- #

PART_A1 = r'''
#![feature(extern_types, sized_hierarchy)]
#![allow(dead_code)]
use core::marker::{MetaSized, PointeeSized};
use core::mem::{align_of_val, size_of, size_of_val};

unsafe extern "C" {
    type OpaqueExtern;
}

#[repr(C)]
struct HeaderWithExtern {
    magic: u32,
    flags: u16,
    tail: OpaqueExtern,
}

#[repr(transparent)]
struct WrapExtern {
    inner: OpaqueExtern,
}

#[repr(C)]
struct ZeroPrefixExtern {
    unit: (),
    tail: OpaqueExtern,
}

trait Tr {
    fn get(&self) -> u32;
}
impl Tr for u64 {
    fn get(&self) -> u32 {
        *self as u32
    }
}

// Tier witnesses: each call is a compile-time proof obligation.
fn needs_sized<T: Sized>() {}
fn needs_meta<T: MetaSized>() {}
fn needs_pointee<T: PointeeSized>() {}

// The implication chain Sized => MetaSized => PointeeSized, checked generically.
fn sized_implies_meta<T: Sized>() {
    needs_meta::<T>()
}
fn meta_implies_pointee<T: MetaSized>() {
    needs_pointee::<T>()
}

fn main() {
    // Tier 1: Sized (and therefore MetaSized and PointeeSized).
    needs_sized::<u32>();
    sized_implies_meta::<u32>();
    meta_implies_pointee::<u32>();
    // Tier 2: MetaSized but not Sized.
    needs_meta::<[u32]>();
    needs_meta::<str>();
    needs_meta::<dyn Tr>();
    needs_meta::<(u8, [u32])>();
    meta_implies_pointee::<[u32]>();
    // Tier 3: PointeeSized only.
    needs_pointee::<OpaqueExtern>();
    needs_pointee::<HeaderWithExtern>();
    needs_pointee::<WrapExtern>();

    // Pointer widths: thin for extern tails, wide for slice / dyn / str tails.
    let widths = (
        size_of::<*const OpaqueExtern>(),
        size_of::<*const HeaderWithExtern>(),
        size_of::<*const WrapExtern>(),
        size_of::<*const u32>(),
        size_of::<*const [u32]>(),
        size_of::<*const str>(),
        size_of::<*const dyn Tr>(),
        size_of::<*const (u8, [u32])>(),
    );
    println!("PTR_WIDTHS_EXTERN_HEADER_WRAP_U32_SLICE_STR_DYN_TUPLE={widths:?}");

    // MetaSized DSTs: size and alignment are functions of the pointer metadata.
    let words16: [u16; 4] = [1, 2, 3, 4];
    let t16: &(u8, [u16]) =
        unsafe { &*(core::ptr::slice_from_raw_parts(words16.as_ptr(), 3) as *const (u8, [u16])) };
    println!("TUPLE_U8_SLICE_U16_LEN3_SIZE_ALIGN={:?}", (size_of_val(t16), align_of_val(t16)));
    let words32: [u32; 2] = [5, 6];
    let t32: &(u8, [u32]) =
        unsafe { &*(core::ptr::slice_from_raw_parts(words32.as_ptr(), 0) as *const (u8, [u32])) };
    println!("TUPLE_U8_SLICE_U32_LEN0_SIZE_ALIGN={:?}", (size_of_val(t32), align_of_val(t32)));
    let d: &dyn Tr = &7u64;
    println!("DYN_TR_U64_SIZE_ALIGN_GET={:?}", (size_of_val(d), align_of_val(d), d.get()));
    let s: &[u32] = &words32;
    println!("SLICE_U32_LEN2_SIZE_ALIGN={:?}", (size_of_val(s), align_of_val(s)));

    let backing: [u32; 4] = [0xdead_beef, 0x1234, 0, 0];
    let base = (&raw const backing) as *const u8;

    // Sized prefix fields of a header with an extern tail, read through a raw
    // pointer (no reference to the header is created here).
    let hp = base as *const HeaderWithExtern;
    let (magic, flags) = unsafe { ((*hp).magic, (*hp).flags) };
    println!("HEADER_PREFIX_VIA_RAW=({magic:#x}, {flags:#x})");

    // Reference to a bare extern type, then a reborrow of it.
    let opaque: &OpaqueExtern = unsafe { &*(base as *const OpaqueExtern) };
    let reborrowed: &OpaqueExtern = &*opaque;
    println!(
        "OPAQUE_REBORROW_SAME_ADDR={}",
        core::ptr::eq(opaque as *const OpaqueExtern as *const u8, reborrowed as *const OpaqueExtern as *const u8)
    );

    // Offset-0 projections to an extern tail are static and succeed.
    let w: &WrapExtern = unsafe { &*(base as *const WrapExtern) };
    let inner: &OpaqueExtern = &w.inner;
    println!("WRAP_ZERO_OFFSET_SAME_ADDR={}", inner as *const OpaqueExtern as *const u8 == base);
    let z: &ZeroPrefixExtern = unsafe { &*(base as *const ZeroPrefixExtern) };
    let ztail: &OpaqueExtern = &z.tail;
    println!("ZST_PREFIX_ZERO_OFFSET_SAME_ADDR={}", ztail as *const OpaqueExtern as *const u8 == base);
    println!("A1_DONE");
}
'''

# Shared type and function definitions for part A2.  Contains no `unsafe` token:
# edition 2021 accepts a plain `extern "C" { type ... }` block.
A2_SAFE_ITEMS = r'''
extern "C" {
    pub type OpaqueExtern;
}

#[repr(C)]
pub struct HeaderWithExtern {
    pub magic: u32,
    pub flags: u16,
    pub tail: OpaqueExtern,
}

#[repr(C, packed)]
pub struct PackedHeaderWithExtern {
    pub magic: u32,
    pub flags: u16,
    pub tail: OpaqueExtern,
}

#[repr(transparent)]
pub struct WrapExtern {
    pub inner: OpaqueExtern,
}

#[repr(C)]
pub struct ZeroPrefixExtern {
    pub unit: (),
    pub tail: OpaqueExtern,
}

#[repr(C)]
pub struct SliceHeader {
    pub magic: u32,
    pub flags: u16,
    pub tail: [u16],
}

pub trait Tr {
    fn get(&self) -> u32;
}
impl Tr for u64 {
    fn get(&self) -> u32 {
        *self as u32
    }
}

#[repr(C)]
pub struct GenericHeader<T: ?Sized> {
    pub magic: u8,
    pub tail: T,
}

pub fn magic_of_header(h: &HeaderWithExtern) -> u32 {
    h.magic
}

/// Non-zero static offset, unknown tail alignment.
pub fn tail_of_header(h: &HeaderWithExtern) -> &OpaqueExtern {
    &h.tail
}

/// `packed(1)`: the tail offset is the static offset for every possible tail
/// alignment, yet the same dynamic-alignment path is taken.
pub fn tail_of_packed(h: &PackedHeaderWithExtern) -> *const OpaqueExtern {
    &raw const h.tail
}

/// Static offset 0.
pub fn tail_of_transparent(w: &WrapExtern) -> &OpaqueExtern {
    &w.inner
}

/// Static offset 0 behind a zero-sized prefix field.
pub fn tail_of_zero_prefix(z: &ZeroPrefixExtern) -> &OpaqueExtern {
    &z.tail
}

/// `MetaSized` control: slice tails have a statically known alignment.
pub fn tail_of_slice_header(h: &SliceHeader) -> &[u16] {
    &h.tail
}

/// `MetaSized` control: `dyn` tails read their alignment from the vtable.
pub fn tail_of_dyn_header(h: &GenericHeader<dyn Tr>) -> &dyn Tr {
    &h.tail
}
'''

A2_MAIN = r'''
fn addr<T: core::marker::PointeeSized>(p: *const T) -> usize {
    p as *const u8 as usize
}

fn main() {
    let backing: [u32; 4] = [0xdead_beef, 0x1234, 0, 0];
    let base = (&raw const backing) as *const u8;
    let scenario = std::env::args().nth(1).unwrap_or_default();
    match scenario.as_str() {
        "header_ref_only" => {
            let h: &safe::HeaderWithExtern = unsafe { &*(base as *const safe::HeaderWithExtern) };
            println!("RESULT header_ref_only magic={:#x}", safe::magic_of_header(h));
        }
        "header_tail_ref" => {
            let h: &safe::HeaderWithExtern = unsafe { &*(base as *const safe::HeaderWithExtern) };
            let t = safe::tail_of_header(h);
            println!("RESULT header_tail_ref offset={}", addr(t) - addr(base));
        }
        "header_tail_raw_no_ref" => {
            let hp = base as *const safe::HeaderWithExtern;
            let t = unsafe { &raw const (*hp).tail };
            println!("RESULT header_tail_raw_no_ref offset={}", addr(t) - addr(base));
        }
        "packed_tail_raw" => {
            let h: &safe::PackedHeaderWithExtern =
                unsafe { &*(base as *const safe::PackedHeaderWithExtern) };
            let t = safe::tail_of_packed(h);
            println!("RESULT packed_tail_raw offset={}", addr(t) - addr(base));
        }
        "transparent_tail_ref" => {
            let w: &safe::WrapExtern = unsafe { &*(base as *const safe::WrapExtern) };
            let t = safe::tail_of_transparent(w);
            println!("RESULT transparent_tail_ref offset={}", addr(t) - addr(base));
        }
        "zero_prefix_tail_ref" => {
            let z: &safe::ZeroPrefixExtern = unsafe { &*(base as *const safe::ZeroPrefixExtern) };
            let t = safe::tail_of_zero_prefix(z);
            println!("RESULT zero_prefix_tail_ref offset={}", addr(t) - addr(base));
        }
        "opaque_reborrow" => {
            let o: &safe::OpaqueExtern = unsafe { &*(base as *const safe::OpaqueExtern) };
            let o2: &safe::OpaqueExtern = &*o;
            println!("RESULT opaque_reborrow same={}", addr(o) == addr(o2));
        }
        "opaque_mut_reborrow" => {
            let mut scratch: [u32; 4] = [1, 2, 3, 4];
            let o: &mut safe::OpaqueExtern =
                unsafe { &mut *((&raw mut scratch) as *mut safe::OpaqueExtern) };
            let before = addr(&raw const *o);
            let o2: &mut safe::OpaqueExtern = &mut *o;
            println!("RESULT opaque_mut_reborrow same={}", before == addr(&raw const *o2));
        }
        "slice_tail_control" => {
            let words: [u16; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
            let h: &safe::SliceHeader = unsafe {
                &*(core::ptr::slice_from_raw_parts(words.as_ptr(), 2) as *const safe::SliceHeader)
            };
            let t = safe::tail_of_slice_header(h);
            println!(
                "RESULT slice_tail_control offset={} len={}",
                addr(t.as_ptr()) - addr(words.as_ptr()),
                t.len()
            );
        }
        "dyn_tail_control" => {
            let concrete = safe::GenericHeader { magic: 1u8, tail: 7u64 };
            let h: &safe::GenericHeader<dyn safe::Tr> = &concrete;
            let t = safe::tail_of_dyn_header(h);
            println!(
                "RESULT dyn_tail_control offset={} get={}",
                addr(t as *const dyn safe::Tr) - addr(&raw const concrete),
                safe::Tr::get(t)
            );
        }
        other => {
            println!("RESULT unknown_scenario {other:?}");
            std::process::exit(2);
        }
    }
    println!("A2_DONE");
}
'''

A2_SCENARIOS = [
    "header_ref_only",
    "header_tail_ref",
    "header_tail_raw_no_ref",
    "packed_tail_raw",
    "transparent_tail_ref",
    "zero_prefix_tail_ref",
    "opaque_reborrow",
    "opaque_mut_reborrow",
    "slice_tail_control",
    "dyn_tail_control",
]

A2_SINGLE_FILE = (
    "#![feature(extern_types, sized_hierarchy)]\n#![allow(dead_code)]\n"
    "#[forbid(unsafe_code)]\nmod safe {\n" + A2_SAFE_ITEMS + "}\n" + A2_MAIN
)
A2_LIB = "#![forbid(unsafe_code)]\n#![feature(extern_types)]\n#![allow(dead_code)]\n" + A2_SAFE_ITEMS
A2_BIN = (
    "#![feature(extern_types, sized_hierarchy)]\n#![allow(dead_code)]\n"
    "extern crate a2_safe_lib as safe;\n" + A2_MAIN
)

EXT = 'extern "C" { pub type OpaqueExtern; }\n'

PART_B: dict[str, str] = {
    "b01_size_of_val_on_extern_type": "#![feature(extern_types)]\n" + EXT
    + "pub fn f(p: &OpaqueExtern) -> usize { core::mem::size_of_val(p) }\n",
    "b02_align_of_val_on_extern_type": "#![feature(extern_types)]\n" + EXT
    + "pub fn f(p: &OpaqueExtern) -> usize { core::mem::align_of_val(p) }\n",
    "b03_question_sized_generic_rejects_extern_type": "#![feature(extern_types)]\n" + EXT
    + "pub fn legacy_qsized<T: ?Sized>(_: &T) {}\npub fn caller(p: &OpaqueExtern) { legacy_qsized(p); }\n",
    "b04_metasized_bound_rejects_header_with_extern_tail": "#![feature(extern_types, sized_hierarchy)]\n" + EXT
    + "#[repr(C)] pub struct Hdr { pub tag: u32, pub tail: OpaqueExtern }\n"
    + "pub fn need_meta<T: core::marker::MetaSized>(_: &T) {}\npub fn caller(h: &Hdr) { need_meta(h); }\n",
    "b05_pointee_sized_bound_accepts_extern_type_and_header": "#![feature(extern_types, sized_hierarchy)]\n" + EXT
    + "#[repr(C)] pub struct Hdr { pub tag: u32, pub tail: OpaqueExtern }\n"
    + "pub fn need_pointee<T: core::marker::PointeeSized>(_: &T) {}\n"
    + "pub fn caller(h: &Hdr, o: &OpaqueExtern) { need_pointee(h); need_pointee(o); }\n",
    "b06_non_tail_extern_type_field_rejected": "#![feature(extern_types)]\n" + EXT
    + "#[repr(C)] pub struct Bad { pub first: OpaqueExtern, pub second: u32 }\n",
    "b07_unsized_tuple_coercion_feature_removed": "#![feature(unsized_tuple_coercion)]\n"
    + "pub fn f(t: &(u8, [u32; 2])) -> &(u8, [u32]) { t }\n",
    "b08_unsized_tuple_coercion_without_feature": "pub fn f(t: &(u8, [u32; 2])) -> &(u8, [u32]) { t }\n",
    "b09_repr_packed_with_extern_tail_definition": "#![feature(extern_types)]\n" + EXT
    + "#[repr(C, packed)] pub struct P { pub tag: u32, pub tail: OpaqueExtern }\n",
    "b10_reference_to_packed_extern_tail": "#![feature(extern_types)]\n" + EXT
    + "#[repr(C, packed)] pub struct P { pub tag: u32, pub tail: OpaqueExtern }\n"
    + "pub fn f(p: &P) -> &OpaqueExtern { &p.tail }\n",
    "b11_raw_borrow_of_packed_extern_tail": "#![forbid(unsafe_code)]\n#![feature(extern_types)]\n" + EXT
    + "#[repr(C, packed)] pub struct P { pub tag: u32, pub tail: OpaqueExtern }\n"
    + "pub fn f(p: &P) -> *const OpaqueExtern { &raw const p.tail }\n",
    "b12_pointee_sized_does_not_imply_meta_sized": "#![feature(sized_hierarchy)]\n"
    + "use core::marker::{MetaSized, PointeeSized};\npub fn need_meta<T: MetaSized>() {}\n"
    + "pub fn f<T: PointeeSized>() { need_meta::<T>() }\n",
    "b13_meta_sized_does_not_imply_sized": "#![feature(sized_hierarchy)]\n"
    + "use core::marker::MetaSized;\npub fn need_sized<T: Sized>() {}\n"
    + "pub fn f<T: MetaSized>() { need_sized::<T>() }\n",
    "b14_question_sized_param_satisfies_meta_sized": "#![feature(sized_hierarchy)]\n"
    + "use core::marker::MetaSized;\npub fn need_meta<T: MetaSized>() {}\n"
    + "pub fn f<T: ?Sized>() { need_meta::<T>() }\n",
    "b15_default_trait_supertrait_rejects_impl_for_extern_type": "#![feature(extern_types)]\n" + EXT
    + "pub trait Describe { fn describe(&self) -> u32; }\n"
    + "impl Describe for OpaqueExtern { fn describe(&self) -> u32 { 0 } }\n",
    "b16_pointee_sized_supertrait_accepts_impl_for_extern_type": "#![feature(extern_types, sized_hierarchy)]\n" + EXT
    + "pub trait Describe: core::marker::PointeeSized { fn describe(&self) -> u32; }\n"
    + "impl Describe for OpaqueExtern { fn describe(&self) -> u32 { 0 } }\n",
    "b17_sized_hierarchy_feature_gate_required": "pub fn need_meta<T: core::marker::MetaSized>() {}\n",
    "b18_forbid_unsafe_lib_with_extern_tail_projections": A2_LIB,
    "b19_box_of_extern_type": "#![feature(extern_types)]\n" + EXT
    + "pub fn f(_: Box<OpaqueExtern>) {}\n",
    "b20_size_of_on_extern_type": "#![feature(extern_types)]\n" + EXT
    + "pub fn f() -> usize { core::mem::size_of::<OpaqueExtern>() }\n",
    "b21_extern_types_feature_gate_required": EXT,
    "b22_size_of_val_on_header_with_extern_tail": "#![feature(extern_types)]\n" + EXT
    + "#[repr(C)] pub struct Hdr { pub tag: u32, pub tail: OpaqueExtern }\n"
    + "pub fn f(h: &Hdr) -> usize { core::mem::size_of_val(h) }\n",
    "b23_extern_type_is_not_unpin": "#![feature(extern_types, sized_hierarchy)]\n" + EXT
    + "pub fn need<T: Unpin + core::marker::PointeeSized>() {}\npub fn f() { need::<OpaqueExtern>() }\n",
    "b24_extern_type_is_not_freeze": "#![feature(extern_types, sized_hierarchy, freeze)]\n" + EXT
    + "pub fn need<T: core::marker::Freeze + core::marker::PointeeSized>() {}\n"
    + "pub fn f() { need::<OpaqueExtern>() }\n",
    "b25_extern_type_is_not_send": "#![feature(extern_types, sized_hierarchy)]\n" + EXT
    + "pub fn need<T: Send + core::marker::PointeeSized>() {}\npub fn f() { need::<OpaqueExtern>() }\n",
    "b26_extern_type_is_not_sync": "#![feature(extern_types, sized_hierarchy)]\n" + EXT
    + "pub fn need<T: Sync + core::marker::PointeeSized>() {}\npub fn f() { need::<OpaqueExtern>() }\n",
    "b27_slice_is_unpin_freeze_send_sync_control": "#![feature(sized_hierarchy, freeze)]\n"
    + "pub fn need<T: Unpin + core::marker::Freeze + Send + Sync + core::marker::PointeeSized>() {}\n"
    + "pub fn f() { need::<[u32]>() }\n",
    "b28_offset_of_extern_tail_field": "#![feature(extern_types)]\n" + EXT
    + "#[repr(C)] pub struct Hdr { pub magic: u32, pub flags: u16, pub tail: OpaqueExtern }\n"
    + "pub fn f() -> usize { core::mem::offset_of!(Hdr, tail) }\n",
    "b29_offset_of_sized_prefix_field_of_extern_tailed_struct": "#![feature(extern_types)]\n" + EXT
    + "#[repr(C)] pub struct Hdr { pub magic: u32, pub flags: u16, pub tail: OpaqueExtern }\n"
    + "pub const FLAGS_OFFSET: usize = core::mem::offset_of!(Hdr, flags);\n"
    + "const _: () = assert!(FLAGS_OFFSET == 4);\n",
    "b30_offset_of_slice_tail_field": "#[repr(C)] pub struct Hdr { pub magic: u32, pub flags: u16, pub tail: [u16] }\n"
    + "pub fn f() -> usize { core::mem::offset_of!(Hdr, tail) }\n",
    "b31_forbid_unsafe_code_rejects_unsafe_extern_block": "#![forbid(unsafe_code)]\n#![feature(extern_types)]\n"
    + "unsafe extern \"C\" { pub type OpaqueExtern; }\n",
    "b32_edition_2024_requires_unsafe_extern_block": "#![feature(extern_types)]\n" + EXT,
    "b33_edition_2024_forbid_unsafe_module_projects_foreign_declared_tail": "#![feature(extern_types)]\n"
    + "pub mod decl {\n    unsafe extern \"C\" { pub type OpaqueExtern; }\n"
    + "    #[repr(C)] pub struct Hdr { pub magic: u32, pub flags: u16, pub tail: OpaqueExtern }\n}\n"
    + "#[forbid(unsafe_code)]\npub mod safe {\n"
    + "    pub fn tail(h: &super::decl::Hdr) -> &super::decl::OpaqueExtern { &h.tail }\n}\n",
    "b34_struct_with_extern_tail_is_not_unpin": "#![feature(extern_types, sized_hierarchy)]\n" + EXT
    + "#[repr(C)] pub struct Hdr { pub magic: u32, pub flags: u16, pub tail: OpaqueExtern }\n"
    + "pub fn need<T: Unpin + core::marker::PointeeSized>() {}\npub fn f() { need::<Hdr>() }\n",
    "b35_struct_with_extern_tail_is_not_freeze": "#![feature(extern_types, sized_hierarchy, freeze)]\n" + EXT
    + "#[repr(C)] pub struct Hdr { pub magic: u32, pub flags: u16, pub tail: OpaqueExtern }\n"
    + "pub fn need<T: core::marker::Freeze + core::marker::PointeeSized>() {}\n"
    + "pub fn f() { need::<Hdr>() }\n",
}

# Cases compiled with an edition other than 2021.
PART_B_EDITION = {
    "b32_edition_2024_requires_unsafe_extern_block": "2024",
    "b33_edition_2024_forbid_unsafe_module_projects_foreign_declared_tail": "2024",
}

# --------------------------------------------------------------------------- #
# Pins (compared against fresh observations; never substituted for them)
# --------------------------------------------------------------------------- #

EXPECT_B = {
    "b01_size_of_val_on_extern_type": (1, ["E0277"], "`MetaSized` is not implemented for `OpaqueExtern`"),
    "b02_align_of_val_on_extern_type": (1, ["E0277"], "`MetaSized` is not implemented for `OpaqueExtern`"),
    "b03_question_sized_generic_rejects_extern_type": (1, ["E0277"], "`MetaSized` is not implemented for `OpaqueExtern`"),
    "b04_metasized_bound_rejects_header_with_extern_tail": (1, ["E0277"], "`MetaSized` is not implemented for `OpaqueExtern`"),
    "b05_pointee_sized_bound_accepts_extern_type_and_header": (0, [], ""),
    "b06_non_tail_extern_type_field_rejected": (1, ["E0277"], "`Sized` is not implemented for `OpaqueExtern`"),
    "b07_unsized_tuple_coercion_feature_removed": (1, ["E0557"], "removed in 1.87.0"),
    "b08_unsized_tuple_coercion_without_feature": (1, ["E0308"], "expected `&(u8, [u32])`"),
    "b09_repr_packed_with_extern_tail_definition": (0, [], ""),
    "b10_reference_to_packed_extern_tail": (1, ["E0793"], "reference to field of packed struct is unaligned"),
    "b11_raw_borrow_of_packed_extern_tail": (0, [], ""),
    "b12_pointee_sized_does_not_imply_meta_sized": (1, ["E0277"], "`MetaSized`"),
    "b13_meta_sized_does_not_imply_sized": (1, ["E0277"], "`Sized`"),
    "b14_question_sized_param_satisfies_meta_sized": (0, [], ""),
    "b15_default_trait_supertrait_rejects_impl_for_extern_type": (1, ["E0277"], "`MetaSized` is not implemented for `OpaqueExtern`"),
    "b16_pointee_sized_supertrait_accepts_impl_for_extern_type": (0, [], ""),
    "b17_sized_hierarchy_feature_gate_required": (1, ["E0658"], "sized_hierarchy"),
    "b18_forbid_unsafe_lib_with_extern_tail_projections": (0, [], ""),
    "b19_box_of_extern_type": (1, ["E0277"], "`MetaSized` is not implemented for `OpaqueExtern`"),
    "b20_size_of_on_extern_type": (1, ["E0277"], "`Sized` is not implemented for `OpaqueExtern`"),
    "b21_extern_types_feature_gate_required": (1, ["E0658"], "extern types are experimental"),
    "b22_size_of_val_on_header_with_extern_tail": (1, ["E0277"], "`MetaSized` is not implemented for `OpaqueExtern`"),
    "b23_extern_type_is_not_unpin": (1, ["E0277"], "`Unpin` is not implemented for `OpaqueExtern`"),
    "b24_extern_type_is_not_freeze": (1, ["E0277"], "`Freeze` is not implemented for `OpaqueExtern`"),
    "b25_extern_type_is_not_send": (1, ["E0277"], "`Send` is not implemented for `OpaqueExtern`"),
    "b26_extern_type_is_not_sync": (1, ["E0277"], "`Sync` is not implemented for `OpaqueExtern`"),
    "b27_slice_is_unpin_freeze_send_sync_control": (0, [], ""),
    "b28_offset_of_extern_tail_field": (1, ["E0277"], "`Sized` is not implemented for `OpaqueExtern`"),
    "b29_offset_of_sized_prefix_field_of_extern_tailed_struct": (0, [], ""),
    "b30_offset_of_slice_tail_field": (1, ["E0277"], "`Sized` is not implemented for `[u16]`"),
    "b31_forbid_unsafe_code_rejects_unsafe_extern_block": (1, [], "usage of an `unsafe extern` block"),
    "b32_edition_2024_requires_unsafe_extern_block": (1, [], "extern blocks must be unsafe"),
    "b33_edition_2024_forbid_unsafe_module_projects_foreign_declared_tail": (0, [], ""),
    "b34_struct_with_extern_tail_is_not_unpin": (1, ["E0277"], "`Unpin` is not implemented for `OpaqueExtern`"),
    "b35_struct_with_extern_tail_is_not_freeze": (1, ["E0277"], "`Freeze` is not implemented for `OpaqueExtern`"),
}

ABORT_MSG = "attempted to compute the size or alignment of extern type"
# The type is printed without a crate prefix when the projection is codegen'd in
# the crate that declares it, and as `<crate>::OpaqueExtern` otherwise.
ABORT_RE = re.compile(r"attempted to compute the size or alignment of extern type `(?:[A-Za-z0-9_]+::)*OpaqueExtern`")
MIRI_OFFSET_MSG = "`extern type` field does not have a known offset"
MIRI_SB_WARNING = "reborrow of a reference to `extern type` is not properly supported"

# scenario -> (native class, stdout substring)
EXPECT_A2_NATIVE = {
    "header_ref_only": ("ok", "magic=0xdeadbeef"),
    "header_tail_ref": ("abort", ""),
    "header_tail_raw_no_ref": ("abort", ""),
    "packed_tail_raw": ("abort", ""),
    "transparent_tail_ref": ("ok", "offset=0"),
    "zero_prefix_tail_ref": ("ok", "offset=0"),
    "opaque_reborrow": ("ok", "same=true"),
    "opaque_mut_reborrow": ("ok", "same=true"),
    "slice_tail_control": ("ok", "offset=6 len=2"),
    "dyn_tail_control": ("ok", "offset=8 get=7"),
}

# scenario -> {miri mode -> class}; classes: ok | ok_sb_warning | unsupported_offset
EXPECT_A2_MIRI = {
    "header_ref_only": {"sb": "ok_sb_warning", "tb": "unsupported_offset", "tb_no_precise_im": "ok", "no_bt": "ok"},
    "header_tail_ref": {"sb": "unsupported_offset", "tb": "unsupported_offset", "tb_no_precise_im": "unsupported_offset", "no_bt": "unsupported_offset"},
    "header_tail_raw_no_ref": {"sb": "unsupported_offset", "tb": "unsupported_offset", "tb_no_precise_im": "unsupported_offset", "no_bt": "unsupported_offset"},
    "packed_tail_raw": {"sb": "unsupported_offset", "tb": "unsupported_offset", "tb_no_precise_im": "unsupported_offset", "no_bt": "unsupported_offset"},
    "transparent_tail_ref": {"sb": "ok_sb_warning", "tb": "ok", "tb_no_precise_im": "ok", "no_bt": "ok"},
    "zero_prefix_tail_ref": {"sb": "ok_sb_warning", "tb": "ok", "tb_no_precise_im": "ok", "no_bt": "ok"},
    "opaque_reborrow": {"sb": "ok_sb_warning", "tb": "ok", "tb_no_precise_im": "ok", "no_bt": "ok"},
    "opaque_mut_reborrow": {"sb": "ok_sb_warning", "tb": "ok", "tb_no_precise_im": "ok", "no_bt": "ok"},
    "slice_tail_control": {"sb": "ok", "tb": "ok", "tb_no_precise_im": "ok", "no_bt": "ok"},
    "dyn_tail_control": {"sb": "ok", "tb": "ok", "tb_no_precise_im": "ok", "no_bt": "ok"},
}

EXPECT_A1_STDOUT = [
    "PTR_WIDTHS_EXTERN_HEADER_WRAP_U32_SLICE_STR_DYN_TUPLE=(8, 8, 8, 8, 16, 16, 16, 16)",
    "TUPLE_U8_SLICE_U16_LEN3_SIZE_ALIGN=(8, 2)",
    "TUPLE_U8_SLICE_U32_LEN0_SIZE_ALIGN=(4, 4)",
    "DYN_TR_U64_SIZE_ALIGN_GET=(8, 8, 7)",
    "SLICE_U32_LEN2_SIZE_ALIGN=(8, 4)",
    "HEADER_PREFIX_VIA_RAW=(0xdeadbeef, 0x1234)",
    "OPAQUE_REBORROW_SAME_ADDR=true",
    "WRAP_ZERO_OFFSET_SAME_ADDR=true",
    "ZST_PREFIX_ZERO_OFFSET_SAME_ADDR=true",
    "A1_DONE",
]
EXPECT_A1_MIRI = {"sb": "ok_sb_warning", "tb": "ok", "tb_no_precise_im": "ok", "no_bt": "ok"}

MIRI_MODES = {
    "sb": [],
    "tb": ["-Zmiri-tree-borrows"],
    "tb_no_precise_im": ["-Zmiri-tree-borrows", "-Zmiri-tree-borrows-no-precise-interior-mut"],
    "no_bt": ["-Zmiri-disable-stacked-borrows"],
}

# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #


class Normalizer:
    """Replace host-specific path prefixes so results are comparable across hosts."""

    def __init__(self, tmp: str, sysroot: str, miri_sysroot: str | None):
        pairs = [(tmp, "<TMP>"), (sysroot, "<SYSROOT>")]
        if miri_sysroot:
            pairs.append((miri_sysroot, "<MIRI_SYSROOT>"))
        home = os.path.expanduser("~")
        if home and home != "/":
            pairs.append((home, "<HOME>"))
        self.pairs = sorted(pairs, key=lambda kv: -len(kv[0]))

    def __call__(self, text: str) -> str:
        for needle, repl in self.pairs:
            text = text.replace(needle, repl)
        text = re.sub(r"thread '([^']*)' \(\d+\)", r"thread '\1' (<TID>)", text)
        return text


def run(cmd: list[str], cwd: str, env: dict[str, str] | None = None) -> dict:
    try:
        p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True,
                           timeout=TIMEOUT_S, errors="replace")
        return {"rc": p.returncode, "stdout": p.stdout, "stderr": p.stderr, "timed_out": False}
    except subprocess.TimeoutExpired as exc:
        out = exc.stdout if isinstance(exc.stdout, str) else ""
        err = exc.stderr if isinstance(exc.stderr, str) else ""
        return {"rc": None, "stdout": out, "stderr": err, "timed_out": True}


def clip(text: str, limit: int = 1800) -> str:
    return text if len(text) <= limit else text[:limit] + f"\n...<clipped {len(text) - limit} bytes>"


def classify_native(res: dict) -> str:
    if res["timed_out"]:
        return "timeout"
    if res["rc"] == 0:
        return "ok"
    if res["rc"] == -signal.SIGABRT and ABORT_RE.search(res["stderr"]) \
            and "thread caused non-unwinding panic. aborting." in res["stderr"]:
        return "abort"
    return f"other_rc_{res['rc']}"


def classify_miri(res: dict) -> str:
    if res["timed_out"]:
        return "timeout"
    warned = MIRI_SB_WARNING in res["stderr"]
    if res["rc"] == 0:
        return "ok_sb_warning" if warned else "ok"
    if "unsupported operation: " + MIRI_OFFSET_MSG in res["stderr"]:
        return "unsupported_offset"
    return f"other_rc_{res['rc']}"


def diagnostics_summary(stderr: str) -> dict:
    return {
        "error_codes": sorted(set(re.findall(r"error\[(E\d{4})\]", stderr))),
        "warning_count": len(re.findall(r"(?m)^warning(?:\[|:)", stderr)),
        "error_count": len(re.findall(r"(?m)^error(?:\[|:)", stderr)),
    }


def error_site(stderr: str) -> str | None:
    """Source line of the first `error:` diagnostic (the line after `-->`)."""
    m = re.search(r"(?m)^error.*\n\s*--> ([^\n]+)", stderr)
    return m.group(1).strip() if m else None


def function_bodies(ir: str, name_fragment: str) -> list[str]:
    bodies = []
    for m in re.finditer(r"(?m)^define [^\n]*@[^\s(]*" + re.escape(name_fragment) + r"[^\n]*\{\n(.*?)^\}", ir, re.S):
        bodies.append(m.group(0))
    return bodies


# --------------------------------------------------------------------------- #
# Main
# --------------------------------------------------------------------------- #


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--toolchain", default=None, help="rustup toolchain name (default: active toolchain)")
    ap.add_argument("--out", default=None, help="write the JSON result here (default: stdout)")
    ap.add_argument("--check", action="store_true", help="exit 1 if any observation differs from its pin")
    ap.add_argument("--no-miri", action="store_true", help="skip the Miri runs")
    args = ap.parse_args()

    plus = [f"+{args.toolchain}"] if args.toolchain else []
    rustc_probe = subprocess.run(["rustc", *plus, "--print", "sysroot"], capture_output=True, text=True)
    if rustc_probe.returncode != 0:
        print("cannot locate rustc sysroot:", rustc_probe.stderr, file=sys.stderr)
        return 2
    sysroot = rustc_probe.stdout.strip()
    rustc = str(Path(sysroot) / "bin" / "rustc")
    miri = str(Path(sysroot) / "bin" / "miri")
    version = subprocess.run([rustc, "-vV"], capture_output=True, text=True).stdout.strip()

    miri_sysroot = None
    miri_version = None
    if not args.no_miri:
        if not Path(miri).exists():
            print("miri binary not found in the toolchain; rerun with --no-miri", file=sys.stderr)
            return 2
        miri_version = subprocess.run([miri, "--version"], capture_output=True, text=True).stdout.strip()
        setup = subprocess.run(["cargo", *plus, "miri", "setup", "--print-sysroot"],
                               capture_output=True, text=True)
        if setup.returncode != 0:
            print("cargo miri setup failed:", setup.stderr[-2000:], file=sys.stderr)
            return 2
        miri_sysroot = setup.stdout.strip().splitlines()[-1]

    mismatches: list[str] = []
    result: dict = {
        "schema": "sized-hierarchy-extern-types-probe/1",
        "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "probe_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "rustc_version_verbose": version,
        "miri_version": miri_version,
        "host_python": sys.version.split()[0],
        "edition": "2021 (part B cases record their own edition)",
        "miri_modes": MIRI_MODES,
    }

    with tempfile.TemporaryDirectory(prefix="sized_probe_") as tmp:
        norm = Normalizer(tmp, sysroot, miri_sysroot)
        common = ["--edition", "2021"]

        def miri_cmd(mode: str, src: str, prog_args: list[str]) -> list[str]:
            return [miri, "--sysroot", miri_sysroot, *MIRI_MODES[mode], *common, src, "--", *prog_args]

        # ----------------------------- Part A1 ----------------------------- #
        a1_src = str(Path(tmp) / "part_a1.rs")
        Path(a1_src).write_text(PART_A1)
        a1: dict = {}
        comp = run([rustc, *common, a1_src, "-o", str(Path(tmp) / "part_a1")], tmp)
        a1["compile"] = {"rc": comp["rc"], "stderr": clip(norm(comp["stderr"])),
                         **diagnostics_summary(comp["stderr"])}
        if comp["rc"] == 0:
            nat = run([str(Path(tmp) / "part_a1")], tmp)
            a1["native"] = {"rc": nat["rc"], "class": classify_native(nat),
                            "stdout_lines": norm(nat["stdout"]).splitlines(),
                            "stderr": clip(norm(nat["stderr"]))}
            if a1["native"]["stdout_lines"] != EXPECT_A1_STDOUT:
                mismatches.append("A1 native stdout differs from pin")
        else:
            mismatches.append("A1 failed to compile")
        if not args.no_miri:
            a1["miri"] = {}
            for mode in MIRI_MODES:
                res = run(miri_cmd(mode, a1_src, []), tmp)
                cls = classify_miri(res)
                a1["miri"][mode] = {
                    "rc": res["rc"], "class": cls,
                    "stdout_lines": norm(res["stdout"]).splitlines(),
                    "stderr": clip(norm(res["stderr"])),
                    **diagnostics_summary(res["stderr"]),
                }
                if cls != EXPECT_A1_MIRI[mode]:
                    mismatches.append(f"A1 miri[{mode}] class {cls} != pin {EXPECT_A1_MIRI[mode]}")
                if res["rc"] == 0 and norm(res["stdout"]).splitlines() != EXPECT_A1_STDOUT:
                    mismatches.append(f"A1 miri[{mode}] stdout differs from pin")
        result["part_a1_hierarchy_thin_pointers_and_zero_offset_projection"] = a1

        # ----------------------------- Part A2 ----------------------------- #
        a2: dict = {"scenarios": {}}
        lib_src = str(Path(tmp) / "a2_safe_lib.rs")
        bin_src = str(Path(tmp) / "a2_bin.rs")
        one_src = str(Path(tmp) / "part_a2.rs")
        Path(lib_src).write_text(A2_LIB)
        Path(bin_src).write_text(A2_BIN)
        Path(one_src).write_text(A2_SINGLE_FILE)

        lib = run([rustc, *common, "--crate-type", "rlib", "--crate-name", "a2_safe_lib", lib_src,
                   "--out-dir", tmp], tmp)
        a2["forbid_unsafe_rlib_compile"] = {"rc": lib["rc"], "stderr": clip(norm(lib["stderr"])),
                                            **diagnostics_summary(lib["stderr"]),
                                            "source_contains_unsafe_token": "unsafe {" in A2_LIB or "unsafe fn" in A2_LIB}
        bin_ = run([rustc, *common, bin_src, "-L", tmp, "-o", str(Path(tmp) / "a2_bin")], tmp)
        a2["two_crate_bin_compile"] = {"rc": bin_["rc"], "stderr": clip(norm(bin_["stderr"])),
                                       **diagnostics_summary(bin_["stderr"])}
        if lib["rc"] != 0 or bin_["rc"] != 0:
            mismatches.append("A2 two-crate build failed")
        # The same two crates at opt-level 3: the abort is not a debug-build artifact.
        opt3_dir = Path(tmp) / "opt3"
        opt3_dir.mkdir()
        lib3 = run([rustc, *common, "-C", "opt-level=3", "--crate-type", "rlib", "--crate-name",
                    "a2_safe_lib", lib_src, "--out-dir", str(opt3_dir)], tmp)
        bin3 = run([rustc, *common, "-C", "opt-level=3", bin_src, "-L", str(opt3_dir),
                    "-o", str(opt3_dir / "a2_bin")], tmp)
        a2["two_crate_opt3_compile"] = {"lib_rc": lib3["rc"], "bin_rc": bin3["rc"],
                                        "stderr": clip(norm(lib3["stderr"] + bin3["stderr"]))}
        if lib3["rc"] != 0 or bin3["rc"] != 0:
            mismatches.append("A2 two-crate opt-level=3 build failed")

        for sc in A2_SCENARIOS:
            entry: dict = {}
            if bin_["rc"] == 0:
                nat = run([str(Path(tmp) / "a2_bin"), sc], tmp)
                cls = classify_native(nat)
                entry["native_two_crate"] = {"rc": nat["rc"], "class": cls,
                                             "stdout_lines": norm(nat["stdout"]).splitlines(),
                                             "stderr": clip(norm(nat["stderr"]))}
                want_cls, want_out = EXPECT_A2_NATIVE[sc]
                if cls != want_cls or want_out not in nat["stdout"]:
                    mismatches.append(f"A2 native[{sc}] class {cls} / stdout differs from pin {want_cls}")
            if bin3["rc"] == 0:
                nat3 = run([str(opt3_dir / "a2_bin"), sc], tmp)
                cls3 = classify_native(nat3)
                entry["native_two_crate_opt3"] = {"rc": nat3["rc"], "class": cls3,
                                                  "stdout_lines": norm(nat3["stdout"]).splitlines(),
                                                  "stderr": clip(norm(nat3["stderr"]))}
                want_cls, want_out = EXPECT_A2_NATIVE[sc]
                if cls3 != want_cls or want_out not in nat3["stdout"]:
                    mismatches.append(f"A2 native-opt3[{sc}] class {cls3} / stdout differs from pin {want_cls}")
            if not args.no_miri:
                entry["miri_single_file"] = {}
                for mode in MIRI_MODES:
                    res = run(miri_cmd(mode, one_src, [sc]), tmp)
                    cls = classify_miri(res)
                    entry["miri_single_file"][mode] = {
                        "rc": res["rc"], "class": cls,
                        "stdout_lines": norm(res["stdout"]).splitlines(),
                        "first_error_site": error_site(norm(res["stderr"])),
                        "stderr": clip(norm(res["stderr"]), 1400),
                        **diagnostics_summary(res["stderr"]),
                    }
                    if cls != EXPECT_A2_MIRI[sc][mode]:
                        mismatches.append(f"A2 miri[{sc}][{mode}] class {cls} != pin {EXPECT_A2_MIRI[sc][mode]}")
            a2["scenarios"][sc] = entry

        # MIR and LLVM IR of the safe projecting functions.
        mir = run([rustc, *common, "--crate-type", "rlib", "--crate-name", "a2_safe_lib", lib_src,
                   "-Zunpretty=mir"], tmp)
        mir_lines = [ln.strip() for ln in mir["stdout"].splitlines() if "OpaqueExtern" in ln and "=" in ln and "//" not in ln]
        a2["mir_statements_mentioning_extern_tail"] = mir_lines
        ir_path = str(Path(tmp) / "a2_safe_lib.ll")
        ir = run([rustc, *common, "--crate-type", "rlib", "--crate-name", "a2_safe_lib", lib_src,
                  "--emit=llvm-ir", "-C", "opt-level=0", "-C", "no-prepopulate-passes", "-o", ir_path], tmp)
        ir_summary: dict = {"emit_rc": ir["rc"]}
        if ir["rc"] == 0 and Path(ir_path).exists():
            text = Path(ir_path).read_text(errors="replace")
            ir_summary["module_mentions_abort_message"] = ABORT_MSG in text
            for fn in ["tail_of_header", "tail_of_packed", "tail_of_transparent", "tail_of_zero_prefix",
                       "tail_of_slice_header", "tail_of_dyn_header", "magic_of_header"]:
                bodies = function_bodies(text, fn)
                calls = [ln.strip() for b in bodies for ln in b.splitlines()
                         if "call " in ln and not ln.lstrip().startswith(";")]
                ir_summary[fn] = {
                    "definitions_found": len(bodies),
                    "calls_panic_nounwind": any("panic_nounwind" in c for c in calls),
                    "call_instructions": [clip(norm(c), 260) for c in calls][:6],
                }
                if fn in ("tail_of_header", "tail_of_packed", "tail_of_transparent") and bodies:
                    ir_summary[fn]["body"] = clip(norm(bodies[0]), 2600).splitlines()
            want = {"tail_of_header": True, "tail_of_packed": True, "tail_of_transparent": False,
                    "tail_of_zero_prefix": False, "tail_of_slice_header": False,
                    "tail_of_dyn_header": False, "magic_of_header": False}
            for fn, flag in want.items():
                got = ir_summary[fn]
                if got["definitions_found"] != 1 or got["calls_panic_nounwind"] != flag:
                    mismatches.append(f"A2 llvm-ir[{fn}] panic_nounwind={got['calls_panic_nounwind']} "
                                      f"defs={got['definitions_found']} != pin {flag}")
        else:
            mismatches.append("A2 llvm-ir emission failed")
        a2["llvm_ir_opt0_safe_lib"] = ir_summary
        result["part_a2_extern_tail_projection_matrix"] = a2

        # ----------------------------- Part B ------------------------------ #
        b: dict = {}
        for name, src in PART_B.items():
            path = str(Path(tmp) / f"{name}.rs")
            Path(path).write_text(src)
            edition = PART_B_EDITION.get(name, "2021")
            res = run([rustc, "--edition", edition, "--crate-type", "lib", "--emit=metadata",
                       "--crate-name", name, path, "-o", str(Path(tmp) / f"{name}.rmeta")], tmp)
            summ = diagnostics_summary(res["stderr"])
            b[name] = {"rc": res["rc"], **summ, "edition": edition, "source": src,
                       "stderr": clip(norm(res["stderr"]), 1500)}
            want_rc, want_codes, want_sub = EXPECT_B[name]
            ok = res["rc"] == want_rc and all(c in summ["error_codes"] for c in want_codes) \
                and (want_sub in res["stderr"])
            if want_rc == 0 and summ["error_count"] != 0:
                ok = False
            if not ok:
                mismatches.append(f"B[{name}] rc={res['rc']} codes={summ['error_codes']} differs from pin "
                                  f"(rc={want_rc}, codes={want_codes}, substring={want_sub!r})")
        result["part_b_compile_time_cases"] = b

    result["pin_mismatches"] = mismatches
    result["all_pins_match"] = not mismatches
    text = json.dumps(result, indent=1, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(text)
        print(f"wrote {args.out}; pin mismatches: {len(mismatches)}")
    else:
        sys.stdout.write(text)
    for m in mismatches:
        print("MISMATCH:", m, file=sys.stderr)
    return 1 if (args.check and mismatches) else 0


if __name__ == "__main__":
    raise SystemExit(main())
