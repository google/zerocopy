use alloc::vec::Vec;
use core::alloc::{GlobalAlloc, Layout};
use spin::Mutex;
use crate::interrupt::{disable_irq, enable_irq};
use crate::memory::MEM_PROVIDER;
use hashbrown::HashMap;
use crate::dropper::DROPPER;
use syscalls::SharedHeapAllocation;

lazy_static! {
    // key of this HashMap is SharedHeapAllocation.ptr
    static ref allocations: Mutex<HashMap<usize, SharedHeapAllocation>> = Mutex::new(HashMap::new());
}

pub struct PHeap();

impl PHeap {
    pub fn new() -> PHeap {
        PHeap {}
    }
}

impl syscalls::Heap for PHeap {
    unsafe fn alloc(&self, layout: Layout, type_id: u64) -> Option<SharedHeapAllocation> {
        disable_irq();
        let allocation = alloc_heap(layout, type_id);
        enable_irq();
        allocation
    }

    unsafe fn dealloc(&self, ptr: *mut u8) {
        disable_irq();
        dealloc_heap(ptr);
        enable_irq();
    }
}

unsafe fn alloc_heap(layout: Layout, type_id: u64) -> Option<SharedHeapAllocation> {

    if !DROPPER.has_type(type_id) {
        return None
    }

    let domain_id_pointer = MEM_PROVIDER.alloc(Layout::new::<u64>()) as *mut u64;
    let borrow_count_pointer = MEM_PROVIDER.alloc(Layout::new::<u64>()) as *mut u64;
    let value_pointer = MEM_PROVIDER.alloc(layout);

    let allocation = SharedHeapAllocation {
        value_pointer,
        domain_id_pointer,
        borrow_count_pointer,
        layout,
        type_id,
    };
    unsafe { &mut allocations.lock() }.insert(value_pointer as usize, allocation);

    Some(allocation)
}

unsafe fn dealloc_heap(ptr: *mut u8) {
    let allocation = {
        allocations.lock().remove(&(ptr as usize))
    };

    match allocation {
        None => println!("Already deallocated shared heap value at address {}", ptr as u64),
        Some(allocation) => {

            // recursively invoke the cleanup methods
            DROPPER.drop(allocation.type_id, allocation.value_pointer);

            unsafe {
                MEM_PROVIDER.dealloc(allocation.value_pointer, allocation.layout);
                MEM_PROVIDER.dealloc(allocation.domain_id_pointer as *mut u8, Layout::new::<u64>());
                MEM_PROVIDER.dealloc(allocation.borrow_count_pointer as *mut u8, Layout::new::<u64>());
            }
        }
    }
}

pub unsafe fn drop_domain(domain_id: u64) {

    // the list of allocations belonging to the domain
    let mut queue = Vec::<SharedHeapAllocation>::new();

    // remove all allocations from list that belong to the exited domain
    allocations.lock().retain(|_, allocation| {
        if *(allocation.domain_id_pointer) == domain_id {
            queue.push(*allocation);
            false
        } else {
            true
        }
    });

    for allocation in queue {
        // recursively invoke the cleanup methods
        DROPPER.drop(allocation.type_id, allocation.value_pointer);

        unsafe {
            MEM_PROVIDER.dealloc(allocation.value_pointer, allocation.layout);
            MEM_PROVIDER.dealloc(allocation.domain_id_pointer as *mut u8, Layout::new::<u64>());
            MEM_PROVIDER.dealloc(allocation.borrow_count_pointer as *mut u8, Layout::new::<u64>());
        }
    }
}
