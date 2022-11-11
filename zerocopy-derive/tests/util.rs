// Copyright 2022 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use zerocopy::{AsBytes, FromBytes};

/// A type that doesn't implement any zerocopy traits.
pub struct NotZerocopy(());

/// A `u16` with alignment 2.
///
/// Though `u16` has alignment 2 on some platforms, it's not guaranteed. By
/// contrast, `AU16` is guaranteed to have alignment 2.
#[derive(FromBytes, AsBytes, Copy, Clone)]
#[repr(C, align(2))]
pub struct AU16(u16);
