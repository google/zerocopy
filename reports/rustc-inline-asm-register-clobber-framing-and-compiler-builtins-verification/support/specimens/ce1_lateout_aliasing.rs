use core::arch::asm;
use core::hint::black_box;

#[inline(never)]
fn id_eax(v: u32) -> u32 {
    black_box(v)
}

#[inline(never)]
pub unsafe fn buggy_lateout_zero_add(v: u32) -> u32 {
    let x = id_eax(v);
    let out: u32;
    unsafe {
        asm!(
            "mov {out:e}, 0",
            "add {out:e}, {inp:e}",
            inp = in(reg) x,
            out = lateout(reg) out,
            options(pure, nomem, nostack),
        );
    }
    out
}

#[inline(never)]
pub unsafe fn safe_early_out_zero_add(v: u32) -> u32 {
    let x = id_eax(v);
    let out: u32;
    unsafe {
        asm!(
            "mov {out:e}, 0",
            "add {out:e}, {inp:e}",
            inp = in(reg) x,
            out = out(reg) out,
            options(pure, nomem, nostack),
        );
    }
    out
}

fn main() {
    let x = black_box(42u32);
    let late = unsafe { buggy_lateout_zero_add(x) };
    let early = unsafe { safe_early_out_zero_add(x) };
    println!("LATEOUT={} OUT={}", late, early);
}
