// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use zerocopy::{AsBytes, FromBytes, Unaligned};

// These derives do not result in E0446 as of Rust 1.59.0, because of
// https://github.com/rust-lang/rust/pull/90586.
//
// This change eliminates one of the major downsides of emitting `where`
// bounds for field types (i.e., the emission of E0446 for private field
// types).

#[derive(AsBytes, FromBytes, Unaligned)]
#[repr(C)]
pub struct Public(Private);

#[derive(AsBytes, FromBytes, Unaligned)]
#[repr(C)]
struct Private(());
