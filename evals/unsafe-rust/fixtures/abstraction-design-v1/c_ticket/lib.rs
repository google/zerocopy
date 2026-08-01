#![allow(dead_code)]

use core::num::NonZeroUsize;

pub struct Ticket(NonZeroUsize);

/// Returns a ticket containing `id`; panics when `id == 0`.
pub fn ticket(id: usize) -> Ticket {
    debug_assert!(id != 0);
    Ticket(unsafe { NonZeroUsize::new_unchecked(id) })
}

