#![allow(dead_code)]

static BYTE: u8 = 7;

pub struct Buffer {
    ptr: *mut u8,
    shared: Option<&'static u8>,
}

impl Buffer {
    /// # Safety
    ///
    /// `ptr` must remain non-null, aligned, and valid for writes of one `u8`
    /// for as long as the returned `Buffer` may be used. No access may
    /// conflict with writes through the returned `Buffer`.
    pub unsafe fn from_writable(ptr: *mut u8) -> Self {
        Self { ptr, shared: None }
    }

    pub fn from_static() -> Self {
        let shared = &BYTE;
        Self {
            ptr: (shared as *const u8) as *mut u8,
            shared: Some(shared),
        }
    }

    pub fn overwrite(&mut self, value: u8) {
        if let Some(shared) = self.shared {
            with_live(shared, || {
                // SAFETY: `from_writable` requires `ptr` to remain valid for
                // writes.
                unsafe { self.ptr.write(value) }
            });
        } else {
            // SAFETY: `from_writable` requires `ptr` to remain valid for
            // writes.
            unsafe { self.ptr.write(value) }
        }
    }
}

fn with_live<T>(shared: &T, operation: impl FnOnce()) {
    operation();
    let _ = shared;
}
