#![allow(invalid_reference_casting, unused, dangling_pointers_from_temporaries)]
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomPinned;
use std::mem::MaybeUninit;
use std::ptr;

fn touch_mut(_x: &mut u32) {}
fn touch_ref(_x: &u32) {}

// C01: Well-typed safe/unsafe split_at_mut (Valid in all 4)
fn c01_valid_split_at_mut() {
    let mut arr = [1u32, 2, 3, 4];
    let ptr = arr.as_mut_ptr();
    unsafe {
        let s1 = std::slice::from_raw_parts_mut(ptr, 2);
        let s2 = std::slice::from_raw_parts_mut(ptr.add(2), 2);
        s1[0] += s2[1];
        assert_eq!(arr[0], 5);
    }
}

// C02: Unused &mut T created from raw pointer, then raw read, then &mut passed to fn (SB fails, TB passes!)
fn c02_unused_mut_reborrow_then_raw_read() {
    let mut data = 10u32;
    let raw: *mut u32 = &mut data;
    let r: &mut u32 = unsafe { &mut *raw };
    let _val = unsafe { *raw };
    touch_mut(r);
}

// C03: Protected Reserved &mut T sees foreign read and returns WITHOUT writing (SB fails, TB passes!)
fn c03_callee(_x: &mut u32, raw: *const u32) -> u32 {
    unsafe { *raw }
}
fn c03_protected_reserved_foreign_read_no_write() {
    let mut data = 7u32;
    let raw: *mut u32 = &mut data;
    let r = unsafe { &mut *raw };
    let v = c03_callee(r, raw);
    assert_eq!(v, 7);
}

// C04: Protected Reserved &mut T sees foreign read AND then performs local write (Both SB and TB fail!)
fn c04_callee(x: &mut u32, raw: *const u32) {
    let _v = unsafe { *raw };
    *x = 42;
}
fn c04_protected_reserved_foreign_read_then_write() {
    let mut data = 0u32;
    let raw: *mut u32 = &mut data;
    let r = unsafe { &mut *raw };
    c04_callee(r, raw);
}

// C05: Parent read freezes child raw mut pointer derived from &mut T (SB passes, TB fails!)
fn c05_parent_read_freezes_child_raw_mut() {
    unsafe {
        let mut root = 6u32;
        let mref = &mut root;
        let ptr = mref as *mut u32;
        *ptr = 1;
        assert_eq!(root, 1);
        *ptr = 2;
    }
}

// C06: Int2ptr exposed provenance round-trip (`expose_provenance` + `with_exposed_provenance_mut`)
// Fails under Strict provenance, Passes under Permissive provenance!
fn c06_exposed_provenance_roundtrip() {
    let mut data = 10u32;
    let addr = (&mut data as *mut u32).expose_provenance();
    let ptr: *mut u32 = ptr::with_exposed_provenance_mut(addr);
    unsafe { *ptr = 20; }
    assert_eq!(data, 20);
}

// C07: Tagged pointer packing in lower 2 alignment bits via expose_provenance (crossbeam-epoch style)
fn c07_tagged_pointer_expose_provenance() {
    #[repr(align(8))]
    struct Node(u64);
    let mut n = Node(99);
    let tagged = (&mut n as *mut Node).expose_provenance() | 0x3;
    let untagged: *mut Node = ptr::with_exposed_provenance_mut(tagged & !0x7);
    unsafe { (*untagged).0 += 1; }
    assert_eq!(n.0, 100);
}

// C08: Subslice provenance shrinking (`&arr[0..1]` cast to raw ptr and offset to index 1)
// Fails in SB (subslice retag shrinks range to 1 element), Passes in TB (reborrow is Reserved/Frozen only on accessed range; wait: let's test read vs write!)
fn c08_subslice_oob_read_via_shrunk_ref() {
    let arr = [10u32, 20u32];
    let sub: &u32 = &arr[0];
    let p = sub as *const u32;
    let v = unsafe { *p.add(1) };
    assert_eq!(v, 20);
}

// C09: Subslice out-of-bounds WRITE via `&mut arr[0]` cast to `*mut u32`
fn c09_subslice_oob_write_via_shrunk_mut_ref() {
    let mut arr = [10u32, 20u32];
    let sub: &mut u32 = &mut arr[0];
    let p = sub as *mut u32;
    unsafe { *p.add(1) = 99; }
}

// C10: Struct field projection `&s.a` cast to raw ptr to read sibling field `s.b` (container_of / offset_of style)
fn c10_sibling_field_read_from_field_ref() {
    #[repr(C)]
    struct Pair { a: u32, b: u32 }
    let s = Pair { a: 1, b: 2 };
    let pa: *const u32 = &s.a;
    let pb = unsafe { *pa.add(1) };
    assert_eq!(pb, 2);
}

// C11: Struct with UnsafeCell field: shared ref `&Pair(u32, UnsafeCell<u32>)` writing to the UnsafeCell field
fn c11_shared_ref_write_unsafecell_field() {
    #[repr(C)]
    struct Pair(u32, UnsafeCell<u32>);
    let p = Pair(1, UnsafeCell::new(2));
    let r: &Pair = &p;
    unsafe { *r.1.get() = 42; }
    assert_eq!(unsafe { *p.1.get() }, 42);
}

// C12: Struct with UnsafeCell field: shared ref `&Pair(u32, UnsafeCell<u32>)` casting base to write non-UnsafeCell field
// SB shrinks Frozen to just field 0; TB treats UnsafeCell precision per field. Both fail on writing field 0!
fn c12_shared_ref_write_non_cell_field() {
    #[repr(C)]
    struct Pair(u32, UnsafeCell<u32>);
    let p = Pair(1, UnsafeCell::new(2));
    let r: &Pair = &p;
    let base = r as *const Pair as *mut u32;
    unsafe { *base = 99; }
}

// C13: Struct with UnsafeCell field: `&Pair(u32, UnsafeCell<u32>) -> &u32 -> *const u32` then offset into UnsafeCell field and write
fn c13_field_ref_offset_into_unsafecell_write() {
    #[repr(C)]
    struct Pair { a: u32, b: UnsafeCell<u32> }
    let p = Pair { a: 1, b: UnsafeCell::new(2) };
    let ra: &u32 = &p.a;
    let ptr_b = (ra as *const u32 as *mut u32).wrapping_add(1);
    unsafe { *ptr_b = 55; }
}

// C14: `!Unpin` mutable reference (`Pin<&mut SelfReferential>`) aliased by raw pointer read while `&mut` is live
fn c14_unpin_phantom_pinned_mut_aliasing() {
    struct SelfRef {
        val: u32,
        ptr: *const u32,
        _pin: PhantomPinned,
    }
    let mut s = SelfRef { val: 42, ptr: ptr::null(), _pin: PhantomPinned };
    s.ptr = &s.val as *const u32;
    let mut_ref: &mut SelfRef = &mut s;
    let v = unsafe { *mut_ref.ptr };
    mut_ref.val = v + 1;
    assert_eq!(s.val, 43);
}

// C15: Intrusive linked-list node aliasing (creating `&mut Node` while sibling holds `*mut Node` to same node and reads it before write)
fn c15_intrusive_list_aliasing() {
    struct Node { next: *mut Node, val: u32 }
    let mut n = Node { next: ptr::null_mut(), val: 1 };
    let raw: *mut Node = &mut n;
    let mref: &mut Node = unsafe { &mut *raw };
    let obs = unsafe { (*raw).val };
    mref.val = obs + 10;
}

// C16: Zerocopy-style transmutation of initialized `[u8; 8]` to `&u64` and `&mut [u8; 8]` reborrow
fn c16_zerocopy_transmute_and_reborrow() {
    #[repr(C, align(8))]
    struct AlignedBytes([u8; 8]);
    let mut buf = AlignedBytes([1, 0, 0, 0, 0, 0, 0, 0]);
    let p = buf.0.as_mut_ptr();
    let u64_ref: &u64 = unsafe { &*(p as *const u64) };
    assert_eq!(*u64_ref, 1);
    unsafe { *p = 2; }
    assert_eq!(buf.0[0], 2);
}

// C17: Reading uninitialized padding bytes via `MaybeUninit<u8>` vs typed `u8` (Typed read is UB in all 4)
fn c17_uninit_typed_u8_read() {
    #[repr(C)]
    struct Padded { a: u8, b: u32 }
    let s = Padded { a: 1, b: 2 };
    let p = &s as *const Padded as *const u8;
    let _pad: u8 = unsafe { *p.add(1) };
}

// C18: Misaligned reference creation (`&*(ptr.add(1) as *const u32)`)
fn c18_misaligned_ref_creation() {
    let arr = [0u32; 4];
    let p = (arr.as_ptr() as *const u8).wrapping_add(1) as *const u32;
    let _r: &u32 = unsafe { &*p };
}

// C19: `ptr::without_provenance_mut` dereference (always UB)
fn c19_without_provenance_deref() {
    let mut x = 1u32;
    let addr = (&mut x as *mut u32).addr();
    let p: *mut u32 = ptr::without_provenance_mut(addr);
    unsafe { *p = 2; }
}

// C20: `Arc`/`SmallVec` pattern: raw pointer derived from `&mut Vec`, reallocation check, then read through `&mut` before raw read
fn c20_smallvec_raw_mut_interleaved_read() {
    let mut buf = [10u32, 20, 30, 40];
    let mref: &mut [u32] = &mut buf[..];
    let raw = mref.as_mut_ptr();
    let first = mref[0];
    let second = unsafe { *raw.add(1) };
    assert_eq!(first + second, 30);
}

fn main() {
    #[cfg(case = "c01")] c01_valid_split_at_mut();
    #[cfg(case = "c02")] c02_unused_mut_reborrow_then_raw_read();
    #[cfg(case = "c03")] c03_protected_reserved_foreign_read_no_write();
    #[cfg(case = "c04")] c04_protected_reserved_foreign_read_then_write();
    #[cfg(case = "c05")] c05_parent_read_freezes_child_raw_mut();
    #[cfg(case = "c06")] c06_exposed_provenance_roundtrip();
    #[cfg(case = "c07")] c07_tagged_pointer_expose_provenance();
    #[cfg(case = "c08")] c08_subslice_oob_read_via_shrunk_ref();
    #[cfg(case = "c09")] c09_subslice_oob_write_via_shrunk_mut_ref();
    #[cfg(case = "c10")] c10_sibling_field_read_from_field_ref();
    #[cfg(case = "c11")] c11_shared_ref_write_unsafecell_field();
    #[cfg(case = "c12")] c12_shared_ref_write_non_cell_field();
    #[cfg(case = "c13")] c13_field_ref_offset_into_unsafecell_write();
    #[cfg(case = "c14")] c14_unpin_phantom_pinned_mut_aliasing();
    #[cfg(case = "c15")] c15_intrusive_list_aliasing();
    #[cfg(case = "c16")] c16_zerocopy_transmute_and_reborrow();
    #[cfg(case = "c17")] c17_uninit_typed_u8_read();
    #[cfg(case = "c18")] c18_misaligned_ref_creation();
    #[cfg(case = "c19")] c19_without_provenance_deref();
    #[cfg(case = "c20")] c20_smallvec_raw_mut_interleaved_read();
}
