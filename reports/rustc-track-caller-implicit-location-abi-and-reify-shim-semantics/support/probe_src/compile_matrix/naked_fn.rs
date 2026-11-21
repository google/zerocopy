#[track_caller]
#[unsafe(naked)]
extern "C" fn f() {
    core::arch::naked_asm!("ret")
}
fn main() {}
