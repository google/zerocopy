use core::arch::naked_asm;

#[unsafe(no_mangle)]
#[unsafe(naked)]
pub extern "C" fn naked_add_mul(a: u64, b: u64, c: u64) -> u64 {
    naked_asm!(
        "lea rax, [rdi + rsi]",
        "imul rax, rdx",
        "ret",
    )
}

fn main() {
    let v1 = naked_add_mul(3, 4, 5);
    println!("NAKED_OK={v1}");
}
