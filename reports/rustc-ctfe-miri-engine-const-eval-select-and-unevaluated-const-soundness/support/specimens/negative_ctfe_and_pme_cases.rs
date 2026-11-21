// Negative compile-fail specimens partitioned via `--cfg case_*`:
// - `case_ptr_to_int`: static `check_consts` rejects `(&raw const x) as usize` (`PointerExposeProvenance`).
// - `case_ptr_read_as_int`: dynamic `CompileTimeMachine` rejects reading pointer bytes as `usize` (`E0080: unable to turn pointer into integer`).
// - `case_raw_ptr_cmp`: static `check_consts` rejects raw pointer `<` comparison during const eval.
// - `case_inner_unsafecell`: `const_validate_mplace` (`validity.rs:1391`) rejects non-ZST `UnsafeCell<u32>` behind `&` in `const` (`UnsafeCell in read-only memory`).
// - `case_pme_ok_u32`: generic associated `const` instantiated only at `T = u32` succeeds (`T = u64` never monomorphized).
// - `case_pme_dead_branch`: generic associated `const` panicking for `T = u64` inside `if false` at `-O0` fails when `MirUsedCollector` walks the unpruned call (`E0080`), vs `-O3` where `SimplifyConstCondition` prunes the dead call before collection!
// - `case_inline_const_dead_branch`: `const { 1_u32 / 0 }` inside `if false` is recorded in `body.required_consts` (`RequiredConstsVisitor` BEFORE dead-branch pruning) and therefore fails with `E0080` EVEN AT `-O3`!

#[cfg(case_ptr_to_int)]
pub const BAD_PTR_INT: usize = {
    let x = 10_u32;
    (&raw const x) as usize
};

#[cfg(case_ptr_read_as_int)]
pub const BAD_READ_PTR_AS_INT: usize = {
    let x = 10_u32;
    let p = &raw const x;
    unsafe { *(&raw const p as *const usize) }
};

#[cfg(case_raw_ptr_cmp)]
pub const BAD_RAW_CMP: bool = {
    let a = [1_u8, 2];
    let p = a.as_ptr();
    let q = unsafe { p.add(1) };
    p < q
};

#[cfg(case_inner_unsafecell)]
const fn leak_cell_ref() -> &'static core::cell::Cell<u32> {
    union Trans {
        r_u32: &'static u32,
        r_cell: &'static core::cell::Cell<u32>,
    }
    static IMMUT: u32 = 7;
    unsafe { Trans { r_u32: &IMMUT }.r_cell }
}

#[cfg(case_inner_unsafecell)]
pub const BAD_CELL_REF: &core::cell::Cell<u32> = leak_cell_ref();

pub trait SizeBound {
    const CHECK: usize;
}

impl<T> SizeBound for T {
    const CHECK: usize = {
        assert!(core::mem::size_of::<T>() <= 4, "PME: T exceeds 4 bytes");
        core::mem::size_of::<T>()
    };
}

#[inline(never)]
pub fn generic_pme_gate<T>() -> usize {
    <T as SizeBound>::CHECK
}

fn main() {
    #[cfg(case_pme_ok_u32)]
    {
        let _ = generic_pme_gate::<u32>();
    }

    #[cfg(case_pme_dead_branch)]
    {
        if false {
            let _ = generic_pme_gate::<u64>();
        }
    }

    #[cfg(case_inline_const_dead_branch)]
    {
        if false {
            let _ = const { 1_u32 / 0 };
        }
    }
}
