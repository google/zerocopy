// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Concrete owned conversions through the standard transmute primitive.
//!
//! This private verification module is selected only on little-endian targets.
//! Verification separately checks the original compiler target and rejects
//! unsupported target overrides. These types have no padding or pointer fields.

/// Preserves all four bytes of the original integer.
///
/// ```aeneas
/// spec owned_transmute_to_bytes_spec
///   ensures bytes => bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)) =
///     Rust.Bytes.encodeLE 4 (value : Nat)
/// ```
fn to_bytes(value: u32) -> [u8; 4] {
    to_bytes_native(value)
}

// This unannotated helper remains in the checked execution closure.
#[allow(unknown_lints)] // unnecessary_transmutes is newer than the MSRV.
#[allow(unnecessary_transmutes)]
fn to_bytes_native(value: u32) -> [u8; 4] {
    // SAFETY: Both types have size four, contain no padding, and accept every
    // bit pattern. Transmute moves the representation into the owned result.
    unsafe { core::mem::transmute::<u32, [u8; 4]>(value) }
}

/// Interprets every initialized four-byte representation as an integer.
///
/// ```aeneas
/// spec owned_transmute_from_bytes_spec
///   ensures value => (value : Nat) = Rust.Bytes.decodeLE
///     (bytes.val.map (fun b => BitVec.ofNat 8 (b : Nat)))
/// ```
#[allow(unknown_lints)] // unnecessary_transmutes is newer than the MSRV.
#[allow(unnecessary_transmutes)]
fn from_bytes(bytes: [u8; 4]) -> u32 {
    // SAFETY: Both types have size four, contain no padding, and accept every
    // bit pattern. No pointer, borrow, or destructor crosses this conversion.
    unsafe { core::mem::transmute::<[u8; 4], u32>(bytes) }
}

/// Checks Boolean validity before invoking the standard primitive.
///
/// ```aeneas
/// spec owned_transmute_bool_spec
///   ensures output => match output with
///     | none => 2 ≤ (byte : Nat)
///     | some value => (byte : Nat) < 2 ∧ value = decide ((byte : Nat) = 1)
/// ```
#[allow(clippy::transmute_int_to_bool)] // Exercise the standard primitive itself.
fn checked_bool(byte: u8) -> Option<bool> {
    if byte < 2 {
        // SAFETY: u8 and bool have size one and no padding. The guard admits
        // exactly Boolean representations zero and one before construction.
        Some(unsafe { core::mem::transmute::<u8, bool>(byte) })
    } else {
        None
    }
}

/// Checks the complete owned integer round trip.
///
/// ```aeneas
/// spec owned_transmute_round_trip_checks_spec
///   ensures _ => True
/// ```
fn round_trip_checks(value: u32) {
    let bytes = to_bytes(value);
    let restored = from_bytes(bytes);
    assert!(restored == value);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concrete_examples() {
        for value in [0, 1, 0x1234_5678, u32::MAX] {
            assert_eq!(to_bytes(value), value.to_le_bytes());
            assert_eq!(from_bytes(value.to_le_bytes()), value);
            round_trip_checks(value);
        }
        for byte in 0..=u8::MAX {
            assert_eq!(
                checked_bool(byte),
                match byte {
                    0 => Some(false),
                    1 => Some(true),
                    _ => None,
                }
            );
        }
    }
}
