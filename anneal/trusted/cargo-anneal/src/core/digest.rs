// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure FIPS 180-4 SHA-256 helpers shared across host and `wasm32` targets.
//!
//! `src/trusted_bundle.rs` keeps standalone copies of `sha256_bytes` and
//! `is_sha256_hex` because `build.rs` includes it directly via `#[path]`
//! outside the `cargo-anneal` crate.

use std::fmt::Write as _;

use sha2::{Digest as _, Sha256};

/// Format raw digest bytes as lowercase hexadecimal.
pub fn digest_to_hex(bytes: &[u8]) -> String {
    let mut hex = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        let _ = write!(&mut hex, "{byte:02x}");
    }
    hex
}

/// Compute the lowercase hex-encoded FIPS 180-4 SHA-256 digest of `data`.
pub fn sha256_bytes(data: &[u8]) -> String {
    digest_to_hex(Sha256::digest(data).as_ref())
}

/// Return `true` if `s` is a 64-character ASCII hex digest.
pub fn is_sha256_hex(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_bytes_and_hex_validation() {
        let empty = sha256_bytes(b"");
        assert_eq!(empty, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
        assert!(is_sha256_hex(&empty));
        assert!(is_sha256_hex(&empty.to_ascii_uppercase()));
        assert!(!is_sha256_hex(&empty[..63]));
        assert!(!is_sha256_hex(&format!("{}z", &empty[..63])));
    }
}
