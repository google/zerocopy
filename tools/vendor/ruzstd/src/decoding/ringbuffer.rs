use alloc::alloc::{alloc, dealloc};
use core::{alloc::Layout, ptr::NonNull, slice};

pub struct RingBuffer {
    // Safety invariants:
    //
    // 1.
    //    a.`buf` must be a valid allocation of capacity `cap`
    //    b. ...unless `cap=0`, in which case it is dangling
    // 2. If tail≥head
    //    a. `head..tail` must contain initialized memory.
    //    b. Else, `head..` and `..tail` must be initialized
    // 3. `head` and `tail` are in bounds (≥ 0 and < cap)
    // 4. `tail` is never `cap` except for a full buffer, and instead uses the value `0`. In other words, `tail` always points to the place
    //    where the next element would go (if there is space)
    buf: NonNull<u8>,
    cap: usize,
    head: usize,
    tail: usize,
}

// SAFETY: RingBuffer does not hold any thread specific values -> it can be sent to another thread -> RingBuffer is Send
unsafe impl Send for RingBuffer {}

// SAFETY: Ringbuffer does not provide unsyncronized interior mutability which makes &RingBuffer Send -> RingBuffer is Sync
unsafe impl Sync for RingBuffer {}

impl RingBuffer {
    pub fn new() -> Self {
        RingBuffer {
            // SAFETY: Upholds invariant 1a as stated
            buf: NonNull::dangling(),
            cap: 0,
            // SAFETY: Upholds invariant 2-4
            head: 0,
            tail: 0,
        }
    }

    /// Return the number of bytes in the buffer.
    pub fn len(&self) -> usize {
        let (x, y) = self.data_slice_lengths();
        x + y
    }

    /// Return the amount of available space (in bytes) of the buffer.
    pub fn free(&self) -> usize {
        let (x, y) = self.free_slice_lengths();
        (x + y).saturating_sub(1)
    }

    /// Empty the buffer and reset the head and tail.
    pub fn clear(&mut self) {
        // SAFETY: Upholds invariant 2, trivially
        // SAFETY: Upholds invariant 3; 0 is always valid
        self.head = 0;
        self.tail = 0;
    }

    /// Ensure that there's space for `amount` elements in the buffer.
    pub fn reserve(&mut self, amount: usize) {
        let free = self.free();
        if free >= amount {
            return;
        }

        self.reserve_amortized(amount - free);
    }

    #[inline(never)]
    #[cold]
    fn reserve_amortized(&mut self, amount: usize) {
        // SAFETY: if we were succesfully able to construct this layout when we allocated then it's also valid do so now
        let current_layout = unsafe { Layout::array::<u8>(self.cap).unwrap_unchecked() };

        // Always have at least 1 unused element as the sentinel.
        let new_cap = usize::max(
            self.cap.next_power_of_two(),
            (self.cap + amount).next_power_of_two(),
        ) + 1;

        // Check that the capacity isn't bigger than isize::MAX, which is the max allowed by LLVM, or that
        // we are on a >= 64 bit system which will never allow that much memory to be allocated
        #[allow(clippy::assertions_on_constants)]
        {
            debug_assert!(usize::BITS >= 64 || new_cap < isize::MAX as usize);
        }

        let new_layout = Layout::array::<u8>(new_cap)
            .unwrap_or_else(|_| panic!("Could not create layout for u8 array of size {}", new_cap));

        // alloc the new memory region and panic if alloc fails
        // TODO maybe rework this to generate an error?
        let new_buf = unsafe {
            let new_buf = alloc(new_layout);

            NonNull::new(new_buf).expect("Allocating new space for the ringbuffer failed")
        };

        // If we had data before, copy it over to the newly alloced memory region
        if self.cap > 0 {
            let ((s1_ptr, s1_len), (s2_ptr, s2_len)) = self.data_slice_parts();

            unsafe {
                // SAFETY: Upholds invariant 2, we end up populating (0..(len₁ + len₂))
                new_buf.as_ptr().copy_from_nonoverlapping(s1_ptr, s1_len);
                new_buf
                    .as_ptr()
                    .add(s1_len)
                    .copy_from_nonoverlapping(s2_ptr, s2_len);
                dealloc(self.buf.as_ptr(), current_layout);
            }

            // SAFETY: Upholds invariant 3, head is 0 and in bounds, tail is only ever `cap` if the buffer
            // is entirely full
            self.tail = s1_len + s2_len;
            self.head = 0;
        }
        // SAFETY: Upholds invariant 1: the buffer was just allocated correctly
        self.buf = new_buf;
        self.cap = new_cap;
    }

    #[allow(dead_code)]
    pub fn push_back(&mut self, byte: u8) {
        self.reserve(1);

        // SAFETY: Upholds invariant 2 by writing initialized memory
        unsafe { self.buf.as_ptr().add(self.tail).write(byte) };
        // SAFETY: Upholds invariant 3 by wrapping `tail` around
        self.tail = (self.tail + 1) % self.cap;
    }

    /// Fetch the byte stored at the selected index from the buffer, returning it, or
    /// `None` if the index is out of bounds.
    #[allow(dead_code)]
    pub fn get(&self, idx: usize) -> Option<u8> {
        if idx < self.len() {
            // SAFETY: Establishes invariants on memory being initialized and the range being in-bounds
            // (Invariants 2 & 3)
            let idx = (self.head + idx) % self.cap;
            Some(unsafe { self.buf.as_ptr().add(idx).read() })
        } else {
            None
        }
    }
    /// Append the provided data to the end of `self`.
    pub fn extend(&mut self, data: &[u8]) {
        let len = data.len();
        let ptr = data.as_ptr();
        if len == 0 {
            return;
        }

        self.reserve(len);

        debug_assert!(self.len() + len <= self.cap - 1);
        debug_assert!(self.free() >= len, "free: {} len: {}", self.free(), len);

        let ((f1_ptr, f1_len), (f2_ptr, f2_len)) = self.free_slice_parts();
        debug_assert!(f1_len + f2_len >= len, "{} + {} < {}", f1_len, f2_len, len);

        let in_f1 = usize::min(len, f1_len);

        let in_f2 = len - in_f1;

        debug_assert!(in_f1 + in_f2 == len);

        unsafe {
            // SAFETY: `in_f₁ + in_f₂ = len`, so this writes `len` bytes total
            // upholding invariant 2
            if in_f1 > 0 {
                f1_ptr.copy_from_nonoverlapping(ptr, in_f1);
            }
            if in_f2 > 0 {
                f2_ptr.copy_from_nonoverlapping(ptr.add(in_f1), in_f2);
            }
        }
        // SAFETY: Upholds invariant 3 by wrapping `tail` around.
        self.tail = (self.tail + len) % self.cap;
    }

    /// Advance head past `amount` elements, effectively removing
    /// them from the buffer.
    pub fn drop_first_n(&mut self, amount: usize) {
        debug_assert!(amount <= self.len());
        let amount = usize::min(amount, self.len());
        // SAFETY: we maintain invariant 2 here since this will always lead to a smaller buffer
        // for amount≤len
        self.head = (self.head + amount) % self.cap;
    }

    /// Return the size of the two contiguous occupied sections of memory used
    /// by the buffer.
    // SAFETY: other code relies on this pointing to initialized halves of the buffer only
    fn data_slice_lengths(&self) -> (usize, usize) {
        let len_after_head;
        let len_to_tail;

        // TODO can we do this branchless?
        if self.tail >= self.head {
            len_after_head = self.tail - self.head;
            len_to_tail = 0;
        } else {
            len_after_head = self.cap - self.head;
            len_to_tail = self.tail;
        }
        (len_after_head, len_to_tail)
    }

    // SAFETY: other code relies on this pointing to initialized halves of the buffer only
    /// Return pointers to the head and tail, and the length of each section.
    fn data_slice_parts(&self) -> ((*const u8, usize), (*const u8, usize)) {
        let (len_after_head, len_to_tail) = self.data_slice_lengths();

        (
            (unsafe { self.buf.as_ptr().add(self.head) }, len_after_head),
            (self.buf.as_ptr(), len_to_tail),
        )
    }

    /// Return references to each part of the ring buffer.
    pub fn as_slices(&self) -> (&[u8], &[u8]) {
        let (s1, s2) = self.data_slice_parts();
        unsafe {
            // SAFETY: relies on the behavior of data_slice_parts for producing initialized memory
            let s1 = slice::from_raw_parts(s1.0, s1.1);
            let s2 = slice::from_raw_parts(s2.0, s2.1);
            (s1, s2)
        }
    }

    // SAFETY: other code relies on this producing the lengths of free zones
    // at the beginning/end of the buffer. Everything else must be initialized
    /// Returns the size of the two unoccupied sections of memory used by the buffer.
    fn free_slice_lengths(&self) -> (usize, usize) {
        let len_to_head;
        let len_after_tail;

        // TODO can we do this branchless?
        if self.tail < self.head {
            len_after_tail = self.head - self.tail;
            len_to_head = 0;
        } else {
            len_after_tail = self.cap - self.tail;
            len_to_head = self.head;
        }
        (len_to_head, len_after_tail)
    }

    /// Returns mutable references to the available space and the size of that available space,
    /// for the two sections in the buffer.
    // SAFETY: Other code relies on this pointing to the free zones, data after the first and before the second must
    // be valid
    fn free_slice_parts(&self) -> ((*mut u8, usize), (*mut u8, usize)) {
        let (len_to_head, len_after_tail) = self.free_slice_lengths();

        (
            (unsafe { self.buf.as_ptr().add(self.tail) }, len_after_tail),
            (self.buf.as_ptr(), len_to_head),
        )
    }

    /// Copies elements from the provided range to the end of the buffer.
    #[allow(dead_code)]
    pub fn extend_from_within(&mut self, start: usize, len: usize) {
        if start + len > self.len() {
            panic!(
                "Calls to this functions must respect start ({}) + len ({}) <= self.len() ({})!",
                start,
                len,
                self.len()
            );
        }

        self.reserve(len);

        // SAFETY: Requirements checked:
        // 1. explicitly checked above, resulting in a panic if it does not hold
        // 2. explicitly reserved enough memory
        unsafe { self.extend_from_within_unchecked(start, len) }
    }

    /// Copies data from the provided range to the end of the buffer, without
    /// first verifying that the unoccupied capacity is available.
    ///
    /// SAFETY:
    /// For this to be safe two requirements need to hold:
    /// 1. start + len <= self.len() so we do not copy uninitialised memory
    /// 2. More then len reserved space so we do not write out-of-bounds
    #[warn(unsafe_op_in_unsafe_fn)]
    pub unsafe fn extend_from_within_unchecked(&mut self, start: usize, len: usize) {
        debug_assert!(start + len <= self.len());
        debug_assert!(self.free() >= len);

        if self.head < self.tail {
            // Continuous source section and possibly non continuous write section:
            //
            //            H           T
            // Read:  ____XXXXSSSSXXXX________
            // Write: ________________DDDD____
            //
            // H: Head position (first readable byte)
            // T: Tail position (first writable byte)
            // X: Uninvolved bytes in the readable section
            // S: Source bytes, to be copied to D bytes
            // D: Destination bytes, going to be copied from S bytes
            // _: Uninvolved bytes in the writable section
            let after_tail = usize::min(len, self.cap - self.tail);

            let src = (
                // SAFETY: `len <= isize::MAX` and fits the memory range of `buf`
                unsafe { self.buf.as_ptr().add(self.head + start) }.cast_const(),
                // Src length (see above diagram)
                self.tail - self.head - start,
            );

            let dst = (
                // SAFETY: `len <= isize::MAX` and fits the memory range of `buf`
                unsafe { self.buf.as_ptr().add(self.tail) },
                // Dst length (see above diagram)
                self.cap - self.tail,
            );

            // SAFETY: `src` points at initialized data, `dst` points to writable memory
            // and does not overlap `src`.
            unsafe { copy_bytes_overshooting(src, dst, after_tail) }

            if after_tail < len {
                // The write section was not continuous:
                //
                //            H           T
                // Read:  ____XXXXSSSSXXXX__
                // Write: DD______________DD
                //
                // H: Head position (first readable byte)
                // T: Tail position (first writable byte)
                // X: Uninvolved bytes in the readable section
                // S: Source bytes, to be copied to D bytes
                // D: Destination bytes, going to be copied from S bytes
                // _: Uninvolved bytes in the writable section

                let src = (
                    // SAFETY: we are still within the memory range of `buf`
                    unsafe { src.0.add(after_tail) },
                    // Src length (see above diagram)
                    src.1 - after_tail,
                );
                let dst = (
                    self.buf.as_ptr(),
                    // Dst length overflowing (see above diagram)
                    self.head,
                );

                // SAFETY: `src` points at initialized data, `dst` points to writable memory
                // and does not overlap `src`.
                unsafe { copy_bytes_overshooting(src, dst, len - after_tail) }
            }
        } else {
            #[allow(clippy::collapsible_else_if)]
            if self.head + start > self.cap {
                // Continuous read section and destination section:
                //
                //                  T           H
                // Read:  XXSSSSXXXX____________XX
                // Write: __________DDDD__________
                //
                // H: Head position (first readable byte)
                // T: Tail position (first writable byte)
                // X: Uninvolved bytes in the readable section
                // S: Source bytes, to be copied to D bytes
                // D: Destination bytes, going to be copied from S bytes
                // _: Uninvolved bytes in the writable section

                let start = (self.head + start) % self.cap;

                let src = (
                    // SAFETY: `len <= isize::MAX` and fits the memory range of `buf`
                    unsafe { self.buf.as_ptr().add(start) }.cast_const(),
                    // Src length (see above diagram)
                    self.tail - start,
                );

                let dst = (
                    // SAFETY: `len <= isize::MAX` and fits the memory range of `buf`
                    unsafe { self.buf.as_ptr().add(self.tail) }, // Dst length (see above diagram)
                    // Dst length (see above diagram)
                    self.head - self.tail,
                );

                // SAFETY: `src` points at initialized data, `dst` points to writable memory
                // and does not overlap `src`.
                unsafe { copy_bytes_overshooting(src, dst, len) }
            } else {
                // Possibly non continuous read section and continuous destination section:
                //
                //            T           H
                // Read:  XXXX____________XXSSSSXX
                // Write: ____DDDD________________
                //
                // H: Head position (first readable byte)
                // T: Tail position (first writable byte)
                // X: Uninvolved bytes in the readable section
                // S: Source bytes, to be copied to D bytes
                // D: Destination bytes, going to be copied from S bytes
                // _: Uninvolved bytes in the writable section

                let after_start = usize::min(len, self.cap - self.head - start);

                let src = (
                    // SAFETY: `len <= isize::MAX` and fits the memory range of `buf`
                    unsafe { self.buf.as_ptr().add(self.head + start) }.cast_const(),
                    // Src length - chunk 1 (see above diagram on the right)
                    self.cap - self.head - start,
                );

                let dst = (
                    // SAFETY: `len <= isize::MAX` and fits the memory range of `buf`
                    unsafe { self.buf.as_ptr().add(self.tail) },
                    // Dst length (see above diagram)
                    self.head - self.tail,
                );

                // SAFETY: `src` points at initialized data, `dst` points to writable memory
                // and does not overlap `src`.
                unsafe { copy_bytes_overshooting(src, dst, after_start) }

                if after_start < len {
                    // The read section was not continuous:
                    //
                    //                T           H
                    // Read:  SSXXXXXX____________XXSS
                    // Write: ________DDDD____________
                    //
                    // H: Head position (first readable byte)
                    // T: Tail position (first writable byte)
                    // X: Uninvolved bytes in the readable section
                    // S: Source bytes, to be copied to D bytes
                    // D: Destination bytes, going to be copied from S bytes
                    // _: Uninvolved bytes in the writable section

                    let src = (
                        self.buf.as_ptr().cast_const(),
                        // Src length - chunk 2 (see above diagram on the left)
                        self.tail,
                    );

                    let dst = (
                        // SAFETY: we are still within the memory range of `buf`
                        unsafe { dst.0.add(after_start) },
                        // Dst length (see above diagram)
                        dst.1 - after_start,
                    );

                    // SAFETY: `src` points at initialized data, `dst` points to writable memory
                    // and does not overlap `src`.
                    unsafe { copy_bytes_overshooting(src, dst, len - after_start) }
                }
            }
        }

        self.tail = (self.tail + len) % self.cap;
    }

    #[allow(dead_code)]
    /// This function is functionally the same as [RingBuffer::extend_from_within_unchecked],
    /// but it does not contain any branching operations.
    ///
    /// SAFETY:
    /// Needs start + len <= self.len()
    /// And more then len reserved space
    pub unsafe fn extend_from_within_unchecked_branchless(&mut self, start: usize, len: usize) {
        // data slices in raw parts
        let ((s1_ptr, s1_len), (s2_ptr, s2_len)) = self.data_slice_parts();

        debug_assert!(len <= s1_len + s2_len, "{} > {} + {}", len, s1_len, s2_len);

        // calc the actually wanted slices in raw parts
        let start_in_s1 = usize::min(s1_len, start);
        let end_in_s1 = usize::min(s1_len, start + len);
        let m1_ptr = s1_ptr.add(start_in_s1);
        let m1_len = end_in_s1 - start_in_s1;

        debug_assert!(end_in_s1 <= s1_len);
        debug_assert!(start_in_s1 <= s1_len);

        let start_in_s2 = start.saturating_sub(s1_len);
        let end_in_s2 = start_in_s2 + (len - m1_len);
        let m2_ptr = s2_ptr.add(start_in_s2);
        let m2_len = end_in_s2 - start_in_s2;

        debug_assert!(start_in_s2 <= s2_len);
        debug_assert!(end_in_s2 <= s2_len);

        debug_assert_eq!(len, m1_len + m2_len);

        // the free slices, must hold: f1_len + f2_len >= m1_len + m2_len
        let ((f1_ptr, f1_len), (f2_ptr, f2_len)) = self.free_slice_parts();

        debug_assert!(f1_len + f2_len >= m1_len + m2_len);

        // calc how many from where bytes go where
        let m1_in_f1 = usize::min(m1_len, f1_len);
        let m1_in_f2 = m1_len - m1_in_f1;
        let m2_in_f1 = usize::min(f1_len - m1_in_f1, m2_len);
        let m2_in_f2 = m2_len - m2_in_f1;

        debug_assert_eq!(m1_len, m1_in_f1 + m1_in_f2);
        debug_assert_eq!(m2_len, m2_in_f1 + m2_in_f2);
        debug_assert!(f1_len >= m1_in_f1 + m2_in_f1);
        debug_assert!(f2_len >= m1_in_f2 + m2_in_f2);
        debug_assert_eq!(len, m1_in_f1 + m2_in_f1 + m1_in_f2 + m2_in_f2);

        debug_assert!(self.buf.as_ptr().add(self.cap) > f1_ptr.add(m1_in_f1 + m2_in_f1));
        debug_assert!(self.buf.as_ptr().add(self.cap) > f2_ptr.add(m1_in_f2 + m2_in_f2));

        debug_assert!((m1_in_f2 > 0) ^ (m2_in_f1 > 0) || (m1_in_f2 == 0 && m2_in_f1 == 0));

        copy_with_checks(
            m1_ptr, m2_ptr, f1_ptr, f2_ptr, m1_in_f1, m2_in_f1, m1_in_f2, m2_in_f2,
        );
        self.tail = (self.tail + len) % self.cap;
    }
}

impl Drop for RingBuffer {
    fn drop(&mut self) {
        if self.cap == 0 {
            return;
        }

        // SAFETY: is we were succesfully able to construct this layout when we allocated then it's also valid do so now
        // Relies on / establishes invariant 1
        let current_layout = unsafe { Layout::array::<u8>(self.cap).unwrap_unchecked() };

        unsafe {
            dealloc(self.buf.as_ptr(), current_layout);
        }
    }
}

/// Similar to ptr::copy_nonoverlapping
///
/// But it might overshoot the desired copy length if deemed useful
///
/// src and dst specify the entire length they are eligible for reading/writing respectively
/// in addition to the desired copy length.
///
/// This function will then copy in chunks and might copy up to chunk size - 1 more bytes from src to dst
/// if that operation does not read/write memory that does not belong to src/dst.
///
/// The chunk size is not part of the contract and may change depending on the target platform.
///
/// If that isn't possible we just fall back to ptr::copy_nonoverlapping
#[inline(always)]
unsafe fn copy_bytes_overshooting(
    src: (*const u8, usize),
    dst: (*mut u8, usize),
    copy_at_least: usize,
) {
    // By default use usize as the copy size
    #[cfg(all(not(target_feature = "sse2"), not(target_feature = "neon")))]
    type CopyType = usize;

    // Use u128 if we detect a simd feature
    #[cfg(target_feature = "neon")]
    type CopyType = u128;
    #[cfg(target_feature = "sse2")]
    type CopyType = u128;

    const COPY_AT_ONCE_SIZE: usize = core::mem::size_of::<CopyType>();
    let min_buffer_size = usize::min(src.1, dst.1);

    // Can copy in just one read+write, very common case
    if min_buffer_size >= COPY_AT_ONCE_SIZE && copy_at_least <= COPY_AT_ONCE_SIZE {
        dst.0
            .cast::<CopyType>()
            .write_unaligned(src.0.cast::<CopyType>().read_unaligned())
    } else {
        let copy_multiple = copy_at_least.next_multiple_of(COPY_AT_ONCE_SIZE);
        // Can copy in multiple simple instructions
        if min_buffer_size >= copy_multiple {
            let mut src_ptr = src.0.cast::<CopyType>();
            let src_ptr_end = src.0.add(copy_multiple).cast::<CopyType>();
            let mut dst_ptr = dst.0.cast::<CopyType>();

            while src_ptr < src_ptr_end {
                dst_ptr.write_unaligned(src_ptr.read_unaligned());
                src_ptr = src_ptr.add(1);
                dst_ptr = dst_ptr.add(1);
            }
        } else {
            // Fall back to standard memcopy
            dst.0.copy_from_nonoverlapping(src.0, copy_at_least);
        }
    }

    debug_assert_eq!(
        slice::from_raw_parts(src.0, copy_at_least),
        slice::from_raw_parts(dst.0, copy_at_least)
    );
}

#[allow(dead_code)]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
unsafe fn copy_without_checks(
    m1_ptr: *const u8,
    m2_ptr: *const u8,
    f1_ptr: *mut u8,
    f2_ptr: *mut u8,
    m1_in_f1: usize,
    m2_in_f1: usize,
    m1_in_f2: usize,
    m2_in_f2: usize,
) {
    f1_ptr.copy_from_nonoverlapping(m1_ptr, m1_in_f1);
    f1_ptr
        .add(m1_in_f1)
        .copy_from_nonoverlapping(m2_ptr, m2_in_f1);

    f2_ptr.copy_from_nonoverlapping(m1_ptr.add(m1_in_f1), m1_in_f2);
    f2_ptr
        .add(m1_in_f2)
        .copy_from_nonoverlapping(m2_ptr.add(m2_in_f1), m2_in_f2);
}

#[allow(dead_code)]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
unsafe fn copy_with_checks(
    m1_ptr: *const u8,
    m2_ptr: *const u8,
    f1_ptr: *mut u8,
    f2_ptr: *mut u8,
    m1_in_f1: usize,
    m2_in_f1: usize,
    m1_in_f2: usize,
    m2_in_f2: usize,
) {
    if m1_in_f1 != 0 {
        f1_ptr.copy_from_nonoverlapping(m1_ptr, m1_in_f1);
    }
    if m2_in_f1 != 0 {
        f1_ptr
            .add(m1_in_f1)
            .copy_from_nonoverlapping(m2_ptr, m2_in_f1);
    }

    if m1_in_f2 != 0 {
        f2_ptr.copy_from_nonoverlapping(m1_ptr.add(m1_in_f1), m1_in_f2);
    }
    if m2_in_f2 != 0 {
        f2_ptr
            .add(m1_in_f2)
            .copy_from_nonoverlapping(m2_ptr.add(m2_in_f1), m2_in_f2);
    }
}

#[allow(dead_code)]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
unsafe fn copy_with_nobranch_check(
    m1_ptr: *const u8,
    m2_ptr: *const u8,
    f1_ptr: *mut u8,
    f2_ptr: *mut u8,
    m1_in_f1: usize,
    m2_in_f1: usize,
    m1_in_f2: usize,
    m2_in_f2: usize,
) {
    let case = (m1_in_f1 > 0) as usize
        | (((m2_in_f1 > 0) as usize) << 1)
        | (((m1_in_f2 > 0) as usize) << 2)
        | (((m2_in_f2 > 0) as usize) << 3);

    match case {
        0 => {}

        // one bit set
        1 => {
            f1_ptr.copy_from_nonoverlapping(m1_ptr, m1_in_f1);
        }
        2 => {
            f1_ptr.copy_from_nonoverlapping(m2_ptr, m2_in_f1);
        }
        4 => {
            f2_ptr.copy_from_nonoverlapping(m1_ptr, m1_in_f2);
        }
        8 => {
            f2_ptr.copy_from_nonoverlapping(m2_ptr, m2_in_f2);
        }

        // two bit set
        3 => {
            f1_ptr.copy_from_nonoverlapping(m1_ptr, m1_in_f1);
            f1_ptr
                .add(m1_in_f1)
                .copy_from_nonoverlapping(m2_ptr, m2_in_f1);
        }
        5 => {
            f1_ptr.copy_from_nonoverlapping(m1_ptr, m1_in_f1);
            f2_ptr.copy_from_nonoverlapping(m1_ptr.add(m1_in_f1), m1_in_f2);
        }
        6 => core::hint::unreachable_unchecked(),
        7 => core::hint::unreachable_unchecked(),
        9 => {
            f1_ptr.copy_from_nonoverlapping(m1_ptr, m1_in_f1);
            f2_ptr.copy_from_nonoverlapping(m2_ptr, m2_in_f2);
        }
        10 => {
            f1_ptr.copy_from_nonoverlapping(m2_ptr, m2_in_f1);
            f2_ptr.copy_from_nonoverlapping(m2_ptr.add(m2_in_f1), m2_in_f2);
        }
        12 => {
            f2_ptr.copy_from_nonoverlapping(m1_ptr, m1_in_f2);
            f2_ptr
                .add(m1_in_f2)
                .copy_from_nonoverlapping(m2_ptr, m2_in_f2);
        }

        // three bit set
        11 => {
            f1_ptr.copy_from_nonoverlapping(m1_ptr, m1_in_f1);
            f1_ptr
                .add(m1_in_f1)
                .copy_from_nonoverlapping(m2_ptr, m2_in_f1);
            f2_ptr.copy_from_nonoverlapping(m2_ptr.add(m2_in_f1), m2_in_f2);
        }
        13 => {
            f1_ptr.copy_from_nonoverlapping(m1_ptr, m1_in_f1);
            f2_ptr.copy_from_nonoverlapping(m1_ptr.add(m1_in_f1), m1_in_f2);
            f2_ptr
                .add(m1_in_f2)
                .copy_from_nonoverlapping(m2_ptr, m2_in_f2);
        }
        14 => core::hint::unreachable_unchecked(),
        15 => core::hint::unreachable_unchecked(),
        _ => core::hint::unreachable_unchecked(),
    }
}

#[cfg(test)]
mod tests {
    use super::RingBuffer;

    #[test]
    fn smoke() {
        let mut rb = RingBuffer::new();

        rb.reserve(15);
        assert_eq!(17, rb.cap);

        rb.extend(b"0123456789");
        assert_eq!(rb.len(), 10);
        assert_eq!(rb.as_slices().0, b"0123456789");
        assert_eq!(rb.as_slices().1, b"");

        rb.drop_first_n(5);
        assert_eq!(rb.len(), 5);
        assert_eq!(rb.as_slices().0, b"56789");
        assert_eq!(rb.as_slices().1, b"");

        rb.extend_from_within(2, 3);
        assert_eq!(rb.len(), 8);
        assert_eq!(rb.as_slices().0, b"56789789");
        assert_eq!(rb.as_slices().1, b"");

        rb.extend_from_within(0, 3);
        assert_eq!(rb.len(), 11);
        assert_eq!(rb.as_slices().0, b"56789789567");
        assert_eq!(rb.as_slices().1, b"");

        rb.extend_from_within(0, 2);
        assert_eq!(rb.len(), 13);
        assert_eq!(rb.as_slices().0, b"567897895675");
        assert_eq!(rb.as_slices().1, b"6");

        rb.drop_first_n(11);
        assert_eq!(rb.len(), 2);
        assert_eq!(rb.as_slices().0, b"5");
        assert_eq!(rb.as_slices().1, b"6");

        rb.extend(b"0123456789");
        assert_eq!(rb.len(), 12);
        assert_eq!(rb.as_slices().0, b"5");
        assert_eq!(rb.as_slices().1, b"60123456789");

        rb.drop_first_n(11);
        assert_eq!(rb.len(), 1);
        assert_eq!(rb.as_slices().0, b"9");
        assert_eq!(rb.as_slices().1, b"");

        rb.extend(b"0123456789");
        assert_eq!(rb.len(), 11);
        assert_eq!(rb.as_slices().0, b"9012345");
        assert_eq!(rb.as_slices().1, b"6789");
    }

    #[test]
    fn edge_cases() {
        // Fill exactly, then empty then fill again
        let mut rb = RingBuffer::new();
        rb.reserve(16);
        assert_eq!(17, rb.cap);
        rb.extend(b"0123456789012345");
        assert_eq!(17, rb.cap);
        assert_eq!(16, rb.len());
        assert_eq!(0, rb.free());
        rb.drop_first_n(16);
        assert_eq!(0, rb.len());
        assert_eq!(16, rb.free());
        rb.extend(b"0123456789012345");
        assert_eq!(16, rb.len());
        assert_eq!(0, rb.free());
        assert_eq!(17, rb.cap);
        assert_eq!(1, rb.as_slices().0.len());
        assert_eq!(15, rb.as_slices().1.len());

        rb.clear();

        // data in both slices and then reserve
        rb.extend(b"0123456789012345");
        rb.drop_first_n(8);
        rb.extend(b"67890123");
        assert_eq!(16, rb.len());
        assert_eq!(0, rb.free());
        assert_eq!(17, rb.cap);
        assert_eq!(9, rb.as_slices().0.len());
        assert_eq!(7, rb.as_slices().1.len());
        rb.reserve(1);
        assert_eq!(16, rb.len());
        assert_eq!(16, rb.free());
        assert_eq!(33, rb.cap);
        assert_eq!(16, rb.as_slices().0.len());
        assert_eq!(0, rb.as_slices().1.len());

        rb.clear();

        // fill exactly, then extend from within
        rb.extend(b"0123456789012345");
        rb.extend_from_within(0, 16);
        assert_eq!(32, rb.len());
        assert_eq!(0, rb.free());
        assert_eq!(33, rb.cap);
        assert_eq!(32, rb.as_slices().0.len());
        assert_eq!(0, rb.as_slices().1.len());

        // extend from within cases
        let mut rb = RingBuffer::new();
        rb.reserve(8);
        rb.extend(b"01234567");
        rb.drop_first_n(5);
        rb.extend_from_within(0, 3);
        assert_eq!(4, rb.as_slices().0.len());
        assert_eq!(2, rb.as_slices().1.len());

        rb.drop_first_n(2);
        assert_eq!(2, rb.as_slices().0.len());
        assert_eq!(2, rb.as_slices().1.len());
        rb.extend_from_within(0, 4);
        assert_eq!(2, rb.as_slices().0.len());
        assert_eq!(6, rb.as_slices().1.len());

        rb.drop_first_n(2);
        assert_eq!(6, rb.as_slices().0.len());
        assert_eq!(0, rb.as_slices().1.len());
        rb.drop_first_n(2);
        assert_eq!(4, rb.as_slices().0.len());
        assert_eq!(0, rb.as_slices().1.len());
        rb.extend_from_within(0, 4);
        assert_eq!(7, rb.as_slices().0.len());
        assert_eq!(1, rb.as_slices().1.len());

        let mut rb = RingBuffer::new();
        rb.reserve(8);
        rb.extend(b"11111111");
        rb.drop_first_n(7);
        rb.extend(b"111");
        assert_eq!(2, rb.as_slices().0.len());
        assert_eq!(2, rb.as_slices().1.len());
        rb.extend_from_within(0, 4);
        assert_eq!(b"11", rb.as_slices().0);
        assert_eq!(b"111111", rb.as_slices().1);
    }
}
