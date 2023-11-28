// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! This module exists to hold this doc comment, which provides lemmas which can
//! be used in soundness proofs.
//!
//! # Definitions
//!
//! ## transparent-layout-validity
//!
//! A type, `T`, has the property `transparent-layout-validity(U)` if the
//! following all hold:
//! - `T` and `U` have the same alignment
//! - For all `t: *const T`, `let u = t as *const U` is valid and
//!   `size_of_val_raw(t) == size_of_val_raw(u)`.
//! - For all `u: *const U`, `let t = *const T` is valid and `size_of_val_raw(u)
//!   == size_of_val_raw(t)`.
//! - For all `(t, u): (*const T, *const U)` where `size_of_val_raw(t) ==
//!   size_of_val_raw(u)`:
//!   - `t` and `u` refer to `UnsafeCell`s at the same byte ranges.
//!   - If `*t` contains a valid `T`, that implies that `*u` contains a valid
//!     `U`.
//!   - If `*u` contains a valid `U`, that implies that `*t` contains a valid
//!     `T`.
//!
//! # Axioms
//!
//! These are statements which are not technically logically bulletproof, but
//! capture the way that language is used in practice in the Rust Reference and
//! standard library documentation.
//!
//! ## axiom-transparent-layout-validity
//!
//! Given types `T` and `U`, the phrase "`T` is guaranteed to have the same
//! layout and bit validity as `U`" is taken to imply that `T` has the property
//! `transparent-layout-validity(U)`.
//!
//! The term "layout" is used in Rust documentation to refer to a type's size
//! and alignment and the sizes, alignments, and byte offsets of each of the
//! type's fields. In practice, phrases like the above are only ever used in
//! contexts where the following additional properties also hold:
//! - `T` and `U` have the same vtable kinds. `T`'s and `U`'s pointer metadata
//!   is such that raw pointer casts preserve size and field placement.
//! - `T` and `U` have `UnsafeCell`s at the same byte ranges.
//!
//! ## axiom-repr-transparent-layout-validity
//!
//! Given types `T` and `U`, if `T` is a `#[repr(transparent)]` struct with a
//! `pub` field of type `U`, and `T` does not contain any other fields, then
//! `T` has the property `transparent-layout-validity(U)`.
//!
//! Per the [Rust Reference][repr-transparent]:
//!
//! > \[`repr(transparent)`\] is only considered part of the public ABI of a
//! > type if either its single field is `pub`, or if its layout is documented
//! > in prose.
//!
//! [repr-transparent]: https://doc.rust-lang.org/nomicon/other-reprs.html#reprtransparent
//!
//! # Lemmas
//!
//! ## lemma-repr-transparent-zerocopy-traits
//!
//! - Lemma: Given types `T` and `U` where `T` is
//!   `transparent-layout-validity(U)`, for each `Trait` in `FromZeroes`,
//!   `FromBytes`, `AsBytes`, and `Unaligned`, if `U` satisfies the safety
//!   preconditions of `Trait`, then `T` does as well.
//! - Proof:
//!   - `FromZeroes`, `FromBytes`, and `AsBytes` all require that a type not
//!     contain any `UnsafeCell`s. `T: transparent-layout-validity(U)`
//!     guarantees that, for all pairs of `t: *const T` and `u: *const U` of
//!     equal size, `t` and `u` refer to `UnsafeCell`s at the same byte ranges.
//!     If `U: FromZeroes`, `U: FromBytes`, or `U: AsBytes`, no instance of `U`
//!     contains `UnsafeCell`s at any byte ranges. Thus, no instance of `T`
//!     contains `UnsafeCell`s at any byte ranges.
//!   - `U: FromZeroes` additionally requires that, given `u: *const U`, it is
//!     sound to initialize `*u` to contain all zero bytes. Since, for all `t:
//!     *const T` and `u: *const U` of equal size, `*t` and `*u` have equal bit
//!     validity, then it must also be the case that, given `t: *const T`, it is
//!     sound to initialize `*t` to contain all zero bytes.
//!   - `U: FromBytes` additionally requires that, given `u: *const U`, it is
//!     sound to initialize `*u` to contain any sequence of `u8`s. Since, for
//!     all `t: *const T` and `u: *const U` of equal size, `*t` and `*u` have
//!     equal bit validity, then it must also be the case that, given `t: *const
//!     T`, it is sound to initialize `*t` to contain any sequence of `u8`s.
//!   - `U: AsBytes` additionally requires that, given `u: &U`, it is sound to
//!     treat `t` as an immutable `[u8]` of length `size_of_val(u)`. This is
//!     equivalent to saying that no instance of `U` can contain bytes which are
//!     invalid for `u8`. Since, for all `t: *const T` and `u: *const U` of
//!     equal size, `*t` and `*u` have equal bit validity, then it must also be
//!     the case that no instance of `T` can contain bytes which are invalid for
//!     `u8`.
//!   - `U: Unaligned` requires that `U`'s alignment is 1. `T:
//!     transparent-layout-validity(U)` guarantees that `T`'s alignment is equal
//!     to `U`'s, and is thus also 1.
//!
//! ## lemma-transparent-layout-validity-is-bit-valid
//!
//! - Lemma: Given `T` and `U` where `T` is `transparent-layout-validity(U)`,
//!   given `t: Ptr<'a, T>` which satisfies the safety preconditions of
//!   `TryFromBytes::<T>::is_bit_valid`, and given `u: Ptr<'a, U>` which
//!   addresses the same range as `t`, `u` satisfies the safety preconditions of
//!   `TryFromBytes::<U>::is_bit_valid`.
//! - Proof: TODO
//!
//! WARNING: This might not actually be sound! In particular, `T:
//! transparent-layout-validity(U)` doesn't guarantee that, given an enum
//! discriminant with a particular value, the subset of values of `T` which are
//! valid for that discriminant is the same as the subset of values of `U` which
//! are valid for that discriminant. As a result, it may be possible to pass a
//! `Ptr<T>` which has uninitialized bytes which are not problematic for `T` but
//! which are problematic for `U`.
