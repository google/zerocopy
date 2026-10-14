use crate::Harness;
use std::cell::Cell;
use std::mem::{align_of, size_of};

#[repr(C)]
#[derive(Clone, Copy)]
union WideCopy { ptr: *const [u8] }

#[repr(C)]
#[derive(Clone, Copy)]
union WideWords { ptr: *const [u8], words: [usize; 2] }

#[inline(never)]
fn copy_wide(value: WideCopy) -> WideCopy { value }
#[inline(never)]
fn copy_words(value: WideWords) -> WideWords { value }

struct DropMark<'a>(&'a Cell<u32>);
impl Drop for DropMark<'_> {
    fn drop(&mut self) { self.0.set(self.0.get() + 1); }
}

pub fn run(h: &mut Harness) {
    let storage = [11_u8, 22, 33, 44];
    let source: &[u8] = &storage[1..4];
    let original = source as *const [u8];
    let copied = copy_wide(WideCopy { ptr: original });
    let wider = copy_words(WideWords { ptr: original });
    // SAFETY: each union was initialized at ptr, copied without modification,
    // and is read only at ptr. The recovered pointer still refers to the same
    // live, initialized, shared-borrowed slice; storage outlives both reads.
    // No inactive words, union padding, fabricated metadata, or uninit bytes are read.
    let (recovered, recovered_words) = unsafe { (copied.ptr, wider.ptr) };
    h.check("wide_union.pointer_identity", std::ptr::eq(original, recovered) && std::ptr::eq(original, recovered_words));
    // SAFETY: exactly the live shared pointers justified above, in scope.
    let (view, view_words) = unsafe { (&*recovered, &*recovered_words) };
    h.check("wide_union.slice_value_and_len", view == [22, 33, 44] && view_words == source && view.len() == 3);
    println!("OBS wide_union.pointer_size={} pointer_align={} one_field_size={} one_field_align={} with_words_size={} with_words_align={}", size_of::<*const [u8]>(), align_of::<*const [u8]>(), size_of::<WideCopy>(), align_of::<WideCopy>(), size_of::<WideWords>(), align_of::<WideWords>());

    let drops = Cell::new(0_u32);
    {
        let original = DropMark(&drops);
        let moved = original;
        h.check("drop.move_not_drop", drops.get() == 0);
        drop(moved);
        h.check("drop.explicit_once", drops.get() == 1);
    }
    h.check("drop.no_double_drop_after_move", drops.get() == 1);
    {
        let _at_scope_end = DropMark(&drops);
        h.check("drop.live_scope", drops.get() == 1);
    }
    h.check("drop.normal_scope_once", drops.get() == 2);
    println!("OBS drop.normal_source_count={}", drops.get());
}
