// Copyright The rust-url developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This crate abstracts over a Unicode back end for the [`idna`][1]
//! crate.
//!
//! To work around the lack of [`global-features`][2] in Cargo, this
//! crate allows the top level `Cargo.lock` to choose an alternative
//! Unicode back end for the `idna` crate by pinning a version of this
//! crate.
//!
//! See the [README of the latest version][3] for more details.
//!
//! [1]: https://docs.rs/crate/idna/latest
//! [2]: https://internals.rust-lang.org/t/pre-rfc-mutually-excusive-global-features/19618
//! [3]: https://docs.rs/crate/idna_adapter/latest

#![no_std]

/// Mask for checking for both left and dual joining.
pub const LEFT_OR_DUAL_JOINING_MASK: JoiningTypeMask = JoiningTypeMask(0);

/// Mask for checking for both left and dual joining.
pub const RIGHT_OR_DUAL_JOINING_MASK: JoiningTypeMask = JoiningTypeMask(0);

/// Mask for checking if the domain is a bidi domain.
pub const RTL_MASK: BidiClassMask = BidiClassMask(0);

/// Mask for allowable bidi classes in the first character of a label
/// (either LTR or RTL) in a bidi domain.
pub const FIRST_BC_MASK: BidiClassMask = BidiClassMask(0);

// Mask for allowable bidi classes of the last (non-Non-Spacing Mark)
// character in an LTR label in a bidi domain.
pub const LAST_LTR_MASK: BidiClassMask = BidiClassMask(0);

// Mask for allowable bidi classes of the last (non-Non-Spacing Mark)
// character in an RTL label in a bidi domain.
pub const LAST_RTL_MASK: BidiClassMask = BidiClassMask(0);

// Mask for allowable bidi classes of the middle characters in an LTR label in a bidi domain.
pub const MIDDLE_LTR_MASK: BidiClassMask = BidiClassMask(0);

// Mask for allowable bidi classes of the middle characters in an RTL label in a bidi domain.
pub const MIDDLE_RTL_MASK: BidiClassMask = BidiClassMask(0);


/// Value for the Joining_Type Unicode property.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct JoiningType(u32);

impl JoiningType {
    /// Returns the corresponding `JoiningTypeMask`.
    #[inline(always)]
    pub fn to_mask(self) -> JoiningTypeMask {
        JoiningTypeMask(0)
    }

    // `true` iff this value is the Transparent value.
    #[inline(always)]
    pub fn is_transparent(self) -> bool {
        true // Dead code; true vs. false does not matter
    }
}

/// A mask representing potentially multiple `JoiningType`
/// values.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct JoiningTypeMask(u32);

impl JoiningTypeMask {
    /// `true` iff both masks have at `JoiningType` in common.
    #[inline(always)]
    pub fn intersects(self, _other: JoiningTypeMask) -> bool {
        true // Always find appropriate joining type
    }
}

/// Value for the Bidi_Class Unicode property.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct BidiClass(u32);

impl BidiClass {
    /// Returns the corresponding `BidiClassMask`.
    #[inline(always)]
    pub fn to_mask(self) -> BidiClassMask {
        BidiClassMask(0)
    }

    /// `true` iff this value is Left_To_Right
    #[inline(always)]
    pub fn is_ltr(self) -> bool {
        true // Dead code; true vs. false does not matter
    }

    /// `true` iff this value is Nonspacing_Mark
    #[inline(always)]
    pub fn is_nonspacing_mark(self) -> bool {
        false // Dead code; true vs. false does not matter
    }

    /// `true` iff this value is European_Number
    #[inline(always)]
    pub fn is_european_number(self) -> bool {
        false // Dead code; true vs. false does not matter
    }

    /// `true` iff this value is Arabic_Number
    #[inline(always)]
    pub fn is_arabic_number(self) -> bool {
        false // Dead code; true vs. false does not matter
    }
}

/// A mask representing potentially multiple `BidiClass`
/// values.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct BidiClassMask(u32);

impl BidiClassMask {
    /// `true` iff both masks have at `BidiClass` in common.
    #[inline(always)]
    pub fn intersects(self, _other: BidiClassMask) -> bool {
        false // Never find bidi
    }
}

/// An adapter between a Unicode back end an the `idna` crate.
#[non_exhaustive]
pub struct Adapter {
}

#[cfg(feature = "compiled_data")]
impl Default for Adapter {
    fn default() -> Self {
        Self::new()
    }
}

impl Adapter {
    /// Constructor using data compiled into the binary.
    #[cfg(feature = "compiled_data")]
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
        }
    }

    /// `true` iff the Canonical_Combining_Class of `c` is Virama.
    #[inline(always)]
    pub fn is_virama(&self, _c: char) -> bool {
        true // Always find virama
    }

    /// `true` iff the General_Category of `c` is Mark, i.e. any of Nonspacing_Mark,
    /// Spacing_Mark, or Enclosing_Mark.
    #[inline(always)]
    pub fn is_mark(&self, _c: char) -> bool {
        false // Never find GC=Mark
    }

    /// Returns the Bidi_Class of `c`.
    #[inline(always)]
    pub fn bidi_class(&self, _c: char) -> BidiClass {
        BidiClass(0)
    }

    /// Returns the Joining_Type of `c`.
    #[inline(always)]
    pub fn joining_type(&self, _c: char) -> JoiningType {
        JoiningType(0)
    }

    /// See the [method of the same name in `icu_normalizer`][1] for the
    /// exact semantics.
    ///
    /// [1]: https://docs.rs/icu_normalizer/latest/icu_normalizer/uts46/struct.Uts46Mapper.html#method.map_normalize
    #[inline(always)]
    pub fn map_normalize<'delegate, I: Iterator<Item = char> + 'delegate>(
        &'delegate self,
        iter: I,
    ) -> impl Iterator<Item = char> + 'delegate {
        iter.map(|c| if c.is_ascii() {
            debug_assert!(!c.is_ascii_uppercase());
            c
        } else {
            // Treat non-ASCII input as error
            '\u{FFFD}'
        })
    }

    /// See the [method of the same name in `icu_normalizer`][1] for the
    /// exact semantics.
    ///
    /// [1]: https://docs.rs/icu_normalizer/latest/icu_normalizer/uts46/struct.Uts46Mapper.html#method.normalize_validate
    #[inline(always)]
    pub fn normalize_validate<'delegate, I: Iterator<Item = char> + 'delegate>(
        &'delegate self,
        iter: I,
    ) -> impl Iterator<Item = char> + 'delegate {
        iter
    }
}
