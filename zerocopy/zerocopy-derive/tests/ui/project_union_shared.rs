// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code)]

extern crate zerocopy_renamed;

use std::{cell::Cell, mem::ManuallyDrop};

use zerocopy_renamed::{
    invariant::{Aligned, Initialized, Shared, Uninit},
    project_clients::{ProjectDerive, TryFromBytesDerive},
    Project, Ptr, TryFromBytes, REPR_C_UNION_VARIANT_ID,
};

#[derive(Project, TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
union Overlapping {
    cell: ManuallyDrop<Cell<u8>>,
    byte: u8,
}

const BYTE: i128 = zerocopy_renamed::ident_id!(byte);

fn uninit(ptr: Ptr<'_, Overlapping, (Shared, Aligned, Uninit)>) {
    let _ = ptr.project::<ProjectDerive, _, { REPR_C_UNION_VARIANT_ID }, { BYTE }>();
    //~[msrv, stable, nightly]^ ERROR: the method `project` exists
    let _ = ptr.project::<TryFromBytesDerive, _, { REPR_C_UNION_VARIANT_ID }, { BYTE }>();
    //~[msrv, stable, nightly]^ ERROR: the method `project` exists
}

fn initialized(ptr: Ptr<'_, Overlapping, (Shared, Aligned, Initialized)>) {
    let _ = ptr.project::<ProjectDerive, _, { REPR_C_UNION_VARIANT_ID }, { BYTE }>();
    //~[msrv, stable, nightly]^ ERROR: the method `project` exists
    let _ = ptr.project::<TryFromBytesDerive, _, { REPR_C_UNION_VARIANT_ID }, { BYTE }>();
    //~[msrv, stable, nightly]^ ERROR: the method `project` exists
}

fn main() {}
