#![allow(dead_code)]

use core::cell::{Cell, UnsafeCell};

#[repr(transparent)]
pub struct SyncUnsafeU64(pub UnsafeCell<u64>);
unsafe impl Sync for SyncUnsafeU64 {}

// 1. Immutable `static` of `Freeze` type -> interned with `Mutability::Not` -> LLVM `constant` (.rodata).
#[used]
pub static FROZEN_STATIC: u64 = 0x1122_3344_5566_7788;

// 2. Immutable `static` of `!Freeze` type (`UnsafeCell`) -> `intern_const_alloc_recursive` sets
//    `base_mutability = Mutability::Mut` (`intern.rs:224-228`) -> LLVM `global` (writable .data).
#[used]
pub static INTERIOR_MUT_STATIC: SyncUnsafeU64 = SyncUnsafeU64(UnsafeCell::new(0x55AA_55AA));

// 3. Top-level `const` with outer `UnsafeCell`: allowed by `CtfeValidationMode::Const {
//    allow_immutable_unsafe_cell: !inner }` (`eval_queries.rs:448`) because each mention copies
//    into a fresh local rather than sharing one static place, and `promote_consts` (`HasMutInterior`)
//    refuses to promote `&CELL_CONST` or `&BIG_CELL_CONST` to `'static`.
pub const CELL_CONST: Cell<u64> = Cell::new(100);

pub struct BigCellStruct {
    pub cell: Cell<u64>,
    pub payload: [u64; 6],
}

pub const BIG_CELL_CONST: BigCellStruct = BigCellStruct {
    cell: Cell::new(400),
    payload: [1, 2, 3, 4, 5, 6],
};

// 4. Zero-sized interior-mutable slice `&[Cell<u32>] = &[]`: explicitly permitted by BOTH
//    `promote_consts.rs:411-419` (zero-length array carve-out from `HasMutInterior`) and
//    `validity.rs:1383-1384` (`let zst = ... s.bytes() == 0; if !zst ...`) because a 0-byte
//    allocation has no mutable bytes in read-only memory (`machine.rs:985`), whereas `&Cell::new(())`
//    on a temporary is rejected earlier by front-end lifetime extension (`E0492`).
pub const EMPTY_CELL_SLICE: &[Cell<u32>] = &[];

const fn zst_cell_ref_via_union() -> &'static Cell<()> {
    union ZstTrans {
        r_unit: &'static (),
        r_cell: &'static Cell<()>,
    }
    static UNIT: () = ();
    unsafe { ZstTrans { r_unit: &UNIT }.r_cell }
}

pub const ZST_CELL_REF: &Cell<()> = zst_cell_ref_via_union();

#[inline(never)]
pub fn exercise_const_cells() -> (u64, u64, u64, u64) {
    let a = CELL_CONST;
    a.set(999);
    let b = CELL_CONST;

    // Borrowing `CELL_CONST` creates a stack temporary (NOT promoted to `.rodata`), so `.set` is sound.
    let temp_ref = &CELL_CONST;
    temp_ref.set(777);
    let after_temp = temp_ref.get();
    let fresh_again = CELL_CONST.get();

    let big = BIG_CELL_CONST;
    big.cell.set(888);
    let big_fresh = BIG_CELL_CONST.cell.get();

    let zst_len = EMPTY_CELL_SLICE.len() as u64;
    ZST_CELL_REF.set(());

    unsafe {
        *INTERIOR_MUT_STATIC.0.get() = 1234;
    }
    let static_now = unsafe { *INTERIOR_MUT_STATIC.0.get() };

    (b.get() + fresh_again + zst_len, after_temp, big_fresh + big.payload[5], static_now)
}

fn main() {
    let (fresh_sum, temp_mut, big_check, static_now) = exercise_const_cells();
    assert_eq!(fresh_sum, 200);
    assert_eq!(temp_mut, 777);
    assert_eq!(big_check, 406);
    assert_eq!(static_now, 1234);
    println!(
        "FRESH_SUM={} TEMP_MUT={} BIG_CHECK={} STATIC_NOW={}",
        fresh_sum, temp_mut, big_check, static_now
    );
}
