// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[macro_use]
extern crate zerocopy_renamed;

fn main() {}

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum FacadeSelf {
    A = Self::TAG,
    //~^ ERROR: `Self` is not supported in enum discriminants
}

impl FacadeSelf {
    const TAG: u8 = 0;
}

#[derive(zerocopy_derive::TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum DirectSelf {
    A = Self::TAG,
    //~^ ERROR: `Self` is not supported in enum discriminants
}

impl DirectSelf {
    const TAG: u8 = 0;
}

#[derive(IntoBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum IntoBytesSelf {
    A = <Self>::TAG,
    //~^ ERROR: `Self` is not supported in enum discriminants
}

impl IntoBytesSelf {
    const TAG: u8 = 0;
}

macro_rules! contextual_tag {
    () => {
        Self::TAG
    };
}

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum MacroDiscriminant {
    A = contextual_tag!(),
    //~^ ERROR: macros are not supported in enum discriminants
}

impl MacroDiscriminant {
    const TAG: u8 = 0;
}

const TAG: u8 = 0;

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum RootedConstant {
    A = crate::TAG,
    //~^ ERROR: paths are not supported in enum discriminants
}

// The path leaf is rejected even below an otherwise-supported operator. In
// particular, such a leaf could have a caller-defined type and select a
// caller-defined operator implementation.
#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum RootedOperatorOperand {
    A = crate::TAG + 1,
    //~^ ERROR: paths are not supported in enum discriminants
}

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum UnqualifiedDiscriminant {
    A = TAG,
    //~^ ERROR: paths are not supported in enum discriminants
}

trait DefaultTag {
    const TAG: u8 = 0;
}

impl<T> DefaultTag for T {}

struct ___ZerocopyTag;

impl ___ZerocopyTag {
    const TAG: u8 = 1;
}

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum GeneratedNameCollision {
    A = ___ZerocopyTag::TAG,
    //~^ ERROR: paths are not supported in enum discriminants
    B = 2,
}

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum PatternNameCollision {
    A = match 0 {
        //~^ ERROR: this expression is not supported in enum discriminants
        ___ZEROCOPY_TAG_Raw if true => 0,
        _ => 1,
    },
    Raw = 2,
}

#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum TypeRelativePath {
    A = crate::TypeRelativePath::TAG,
    //~^ ERROR: paths are not supported in enum discriminants
}

impl TypeRelativePath {
    const TAG: u8 = 0;
}

#[cfg(not(msrv))]
#[derive(TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum ReportShape {
    Flag(bool) = Self::TAG,
    //~[stable, nightly]^ ERROR: `Self` is not supported in enum discriminants
    Raw(u8) = 1 - Self::TAG,
}

#[cfg(not(msrv))]
impl ReportShape {
    const TAG: u8 = 1;
}
