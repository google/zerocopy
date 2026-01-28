// Copyright (c) The future-queue Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::{cmp::Reverse, collections::BinaryHeap};

/// A model for slot indexes currently in use.
///
/// The semantics are:
///
/// * When `reserve` is called, a new slot is assigned. The slot is the smallest
///   number possible.
/// * Slots are reserved until `release` is called, at which point the slot is
///   available for reuse.
///
/// `SlotReservations` is implemented via a simple heap.
#[derive(Debug)]
pub(crate) struct SlotReservations {
    next: u64,
    // BinaryHeap is a max-heap, but we care about the smallest slot: use
    // Reverse to turn it into a min-heap.
    free: BinaryHeap<Reverse<u64>>,
    check_reserved: bool,
}

impl SlotReservations {
    /// Create a new `SlotReservations` with no slots reserved.
    #[allow(unused)]
    pub(crate) fn new() -> Self {
        Self {
            next: 0,
            free: BinaryHeap::new(),
            check_reserved: false,
        }
    }

    /// Create a new `SlotReservations` with an initial free-heap capacity
    /// allocated.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            next: 0,
            free: BinaryHeap::with_capacity(capacity),
            check_reserved: false,
        }
    }

    /// Set the `check_reserved` flag: useful for testing.
    pub(crate) fn set_check_reserved(&mut self, check_reserved: bool) {
        self.check_reserved = check_reserved;
    }

    /// Reserve a new slot.
    #[inline]
    pub(crate) fn reserve(&mut self) -> u64 {
        if let Some(slot) = self.free.pop() {
            slot.0
        } else {
            let slot = self.next;
            self.next += 1;
            slot
        }
    }

    /// Release a slot.
    ///
    /// This does not check if the slot is reserved by default. But it does if
    /// [`Self::set_check_reserved`] is called.
    #[inline]
    pub(crate) fn release(&mut self, slot: u64) {
        if self.check_reserved {
            assert!(self.check_reserved(slot), "slot {slot} is reserved");
        }
        self.free.push(Reverse(slot));
    }

    /// Check if a slot is reserved.
    #[must_use]
    pub(crate) fn check_reserved(&self, slot: u64) -> bool {
        if slot >= self.next {
            return false;
        }
        if self.free.iter().any(|s| s.0 == slot) {
            return false;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn release_in_order() {
        let mut slots = SlotReservations::new();
        slots.set_check_reserved(true);
        assert_reserved(&slots, &[]);

        let slot1 = slots.reserve();
        assert_eq!(slot1, 0);
        assert_reserved(&slots, &[0]);

        let slot2 = slots.reserve();
        assert_eq!(slot2, 1);
        assert_reserved(&slots, &[0, 1]);

        slots.release(slot1);
        assert_reserved(&slots, &[1]);
        slots.release(slot2);
        assert_reserved(&slots, &[]);

        assert_eq!(slots.reserve(), 0);
        assert_reserved(&slots, &[0]);

        assert_eq!(slots.reserve(), 1);
        assert_reserved(&slots, &[0, 1]);
    }

    #[test]
    fn release_out_of_order() {
        let mut slots = SlotReservations::new();
        slots.set_check_reserved(true);
        assert_reserved(&slots, &[]);

        let slot1 = slots.reserve();
        assert_eq!(slot1, 0);
        assert_reserved(&slots, &[0]);

        let slot2 = slots.reserve();
        assert_eq!(slot2, 1);
        assert_reserved(&slots, &[0, 1]);

        slots.release(slot2);
        assert_reserved(&slots, &[0]);

        slots.release(slot1);
        assert_reserved(&slots, &[]);

        assert_eq!(slots.reserve(), slot1);
        assert_reserved(&slots, &[0]);
        assert_eq!(slots.reserve(), slot2);
        assert_reserved(&slots, &[0, 1]);
    }

    fn assert_reserved(slots: &SlotReservations, expected: &[u64]) {
        for &slot in expected {
            assert!(slots.check_reserved(slot), "slot {} is not reserved", slot);
        }

        // Also check slots from max to 64 or so to make sure they are not reserved.
        for slot in (expected.iter().max().map_or(0, |max| max + 1))..64 {
            assert!(
                !slots.check_reserved(slot),
                "slot {slot} is not reserved (slots: {slots:?})",
            );
        }
    }
}
