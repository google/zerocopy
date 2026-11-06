#![crate_type = "lib"]
use std::arch::asm;

// complete: compiler observation only; wrong_* contracts are never executed.
#[no_mangle]
pub unsafe extern "C" fn annotation_complete(cell: &mut u32) -> u32 {
    *cell = 7;
    asm!("str {value:w}, [{pointer}]", pointer=in(reg) cell as *mut u32,
        value=in(reg) 9u32, options(nostack, preserves_flags));
    *cell
}

// wrong_nomem: compiler observation only; wrong_* contracts are never executed.
#[no_mangle]
pub unsafe extern "C" fn annotation_wrong_nomem(cell: &mut u32) -> u32 {
    *cell = 7;
    asm!("str {value:w}, [{pointer}]", pointer=in(reg) cell as *mut u32,
        value=in(reg) 9u32, options(nomem, nostack, preserves_flags));
    *cell
}

// wrong_readonly: compiler observation only; wrong_* contracts are never executed.
#[no_mangle]
pub unsafe extern "C" fn annotation_wrong_readonly(cell: &mut u32) -> u32 {
    *cell = 7;
    asm!("str {value:w}, [{pointer}]", pointer=in(reg) cell as *mut u32,
        value=in(reg) 9u32, options(readonly, nostack, preserves_flags));
    *cell
}
