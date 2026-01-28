// Copyright (c) The future-queue Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

/// Global weight implementation, shared between FutureQueue and FutureQueueGrouped.
#[derive(Debug)]
pub(crate) struct GlobalWeight {
    max: usize,
    current: usize,
}

impl GlobalWeight {
    pub(crate) fn new(max: usize) -> Self {
        Self { max, current: 0 }
    }

    #[inline]
    pub(crate) fn max(&self) -> usize {
        self.max
    }

    #[inline]
    pub(crate) fn current(&self) -> usize {
        self.current
    }

    #[inline]
    pub(crate) fn has_space_for(&self, weight: usize) -> bool {
        let weight = weight.min(self.max);
        self.current <= self.max - weight
    }

    pub(crate) fn add_weight(&mut self, weight: usize) {
        let weight = weight.min(self.max);
        self.current = self.current.checked_add(weight).unwrap_or_else(|| {
            panic!(
                "future_queue_grouped: added weight {} to current {}, overflowed",
                weight, self.current,
            )
        });
    }

    pub(crate) fn sub_weight(&mut self, weight: usize) {
        let weight = weight.min(self.max);
        self.current = self.current.checked_sub(weight).unwrap_or_else(|| {
            panic!(
                "future_queue_grouped: subtracted weight {} from current {}, overflowed",
                weight, self.current,
            )
        });
    }
}
