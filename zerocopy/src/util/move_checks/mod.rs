// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exercise ownership transfer without assuming that `T` has no destructor.
//!
//! Early MIR retains conditional drops of the argument and its temporary even
//! after both have moved. CI must prove those slots empty before ignoring the
//! drops. Neither the generic caller nor its callee may execute a destructor.

#![allow(dead_code)]

/// Returns the original value through an ordinary generic call.
///
/// ```aeneas
/// spec move_through_call_spec
///   ensures(raw) result => result = value
/// ```
fn move_through_call<T>(value: T) -> T {
    forward(value)
}

fn forward<T>(value: T) -> T {
    value
}

#[cfg(test)]
mod tests {
    use core::cell::Cell;

    use super::move_through_call;

    #[test]
    fn destructor_stays_with_returned_value() {
        struct CountDrop<'a>(&'a Cell<usize>);
        impl Drop for CountDrop<'_> {
            fn drop(&mut self) {
                self.0.set(self.0.get().saturating_add(1));
            }
        }
        let drops = Cell::new(0);
        let returned = move_through_call(CountDrop(&drops));
        assert_eq!(drops.get(), 0);
        drop(returned);
        assert_eq!(drops.get(), 1);
    }
}
