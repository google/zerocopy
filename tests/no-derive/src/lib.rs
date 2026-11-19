// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[cfg(test)]
mod tests {
    #[derive(
        zerocopy_derive::FromBytes,
        zerocopy_derive::IntoBytes,
        zerocopy_derive::Immutable,
        zerocopy_derive::KnownLayout,
    )]
    #[repr(C)]
    struct Header {
        tag: u16,
        length: u16,
    }

    #[test]
    fn derives_work_without_zerocopy_derive_feature() {
        let bytes = [1, 0, 2, 0];
        let header = <Header as zerocopy::FromBytes>::read_from_bytes(&bytes).unwrap();
        assert_eq!(zerocopy::IntoBytes::as_bytes(&header), bytes);
    }
}
