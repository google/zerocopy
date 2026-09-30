// although unsafe function's don't need unsafe blocks, it helps readability
#![allow(unused_unsafe)]
use crate::traits::{RRefable, TypeIdentifiable, CustomCleanup};

use alloc::boxed::Box;
use core::ops::{Deref, DerefMut, Drop};
use core::alloc::Layout;
use spin::Once;

// #[cfg(features = "rref_dbg")]
use console::println;

static HEAP: Once<Box<dyn syscalls::Heap + Send + Sync>> = Once::new();
static CRATE_DOMAIN_ID: Once<u64> = Once::new();

pub fn init(heap: Box<dyn syscalls::Heap + Send + Sync>, domain_id: u64) {
    HEAP.call_once(|| heap);
    CRATE_DOMAIN_ID.call_once(|| domain_id);
}

// RRef (remote reference) is an owned reference to an object on shared heap.
// Only one domain can hold an RRef at a single time, so therefore we can "safely" mutate it.
// A global table retains all memory allocated on the shared heap. When a domain dies, all of
//   its shared heap objects are dropped, which gives us the guarantee that RRef's
//   owned reference will be safe to dereference as long as its domain is alive.
pub struct RRef<T> where T: 'static + RRefable {
    domain_id_pointer: *mut u64,
    pub(crate) borrow_count_pointer: *mut u64,
    pub(crate) value_pointer: *mut T
}

unsafe impl<T: RRefable> RRefable for RRef<T> {}
unsafe impl<T: RRefable> Send for RRef<T> where T: Send {}

impl<T: RRefable> RRef<T> where T: TypeIdentifiable {
    pub(crate) unsafe fn new_with_layout(value: T, layout: Layout) -> RRef<T> {
        // We allocate the shared heap memory by hand. It will be deallocated in one of two cases:
        //   1. RRef<T> gets dropped, and so the memory under it should be freed.
        //   2. The domain owning the RRef dies, and so the shared heap gets cleaned,
        //        and the memory under this RRef is wiped.
        let type_id = T::type_id();

        // the heap interface allocates both a pointer to T, and a pointer to the domain id
        // when we move the rref, we change the value of the domain id pointer
        // when we modify the rref, we dereference the value pointer
        let allocation = match unsafe { HEAP.force_get().alloc(layout, type_id) } {
            Some(allocation) => allocation,
            None => panic!("{} is not a registered RRef type", core::any::type_name::<T>())
        };

        // the memory we get back has size and alignment of T, so this cast is safe
        let value_pointer = allocation.value_pointer as *mut T;

        // set initial domain id
        *allocation.domain_id_pointer = *CRATE_DOMAIN_ID.force_get();
        // borrow count to 0
        *allocation.borrow_count_pointer = 0;
        // copy value to shared heap
        core::ptr::write(value_pointer, value);

        RRef {
            domain_id_pointer: allocation.domain_id_pointer,
            borrow_count_pointer: allocation.borrow_count_pointer,
            value_pointer
        }
    }

    pub fn new(value: T) -> RRef<T> {
        let layout = Layout::new::<T>();
        unsafe { Self::new_with_layout(value, layout) }
    }

    pub fn new_aligned(value: T, align: usize) -> RRef<T> {
        let size = core::mem::size_of::<T>();
        let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
        unsafe { Self::new_with_layout(value, layout) }
    }
}

impl<T: RRefable> RRef<T> {
    pub fn borrow(&self) {
        unsafe {
            *self.borrow_count_pointer += 1;
        }
    }

    pub fn forfeit(&self) {
        unsafe {
            debug_assert_ne!(*self.borrow_count_pointer, 0);
            *self.borrow_count_pointer -= 1;
        }
    }

    pub fn borrow_count(&self) -> u64 {
        unsafe { *self.borrow_count_pointer }
    }

    // TODO: move to kernel if possible
    // TODO: mark unsafe
    pub fn move_to(&self, new_domain_id: u64) {
        // TODO: race here
        unsafe {
            *self.domain_id_pointer = new_domain_id
        };
    }

    pub unsafe fn move_to_current(&self) {
        unsafe { self.move_to(*CRATE_DOMAIN_ID.force_get()) };
    }

    // Super unsafe from an ownership perspective
    pub(crate) unsafe fn ptr_mut(&self) -> &mut T {
        unsafe {
            &mut *self.value_pointer
        }
    }
}

impl<T: RRefable> Drop for RRef<T> {
    fn drop(&mut self) {
        self.cleanup();
    }
}

impl<T: 'static + RRefable> CustomCleanup for RRef<T> {
    fn cleanup(&mut self) {
        unsafe {
            #[cfg(features = "rref_dbg")]
            println!("CustomCleanup::<{}>::cleanup() dom id {:?} heap? {:?}", core::any::type_name_of_val(self), CRATE_DOMAIN_ID.r#try(), HEAP.r#try().is_some());
            // "drop" the contents, only interesting for recursive cases
            // self.ptr_mut().cleanup();
            HEAP.force_get().dealloc(self.value_pointer as *mut u8);
        }
    }
}

impl<T: RRefable> Deref for RRef<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { & *self.value_pointer}
    }
}

impl<T: RRefable> DerefMut for RRef<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.value_pointer }
    }
}
