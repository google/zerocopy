// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

#[cfg(not(target_endian = "little"))]
compile_error!("this concrete byte-conversion probe supports little-endian targets only");

#[allow(unnecessary_transmutes)]
pub fn to_bytes(value: u32) -> [u8; 4] {
    unsafe { core::mem::transmute::<u32, [u8; 4]>(value) }
}

#[allow(unnecessary_transmutes)]
pub fn from_bytes(value: [u8; 4]) -> u32 {
    unsafe { core::mem::transmute::<[u8; 4], u32>(value) }
}

pub fn guarded_bool(value: u8) -> bool {
    assert!(value < 2);
    unsafe { core::mem::transmute::<u8, bool>(value) }
}
