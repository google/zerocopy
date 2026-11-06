//#![feature(asm)]
//#![feature(llvm_asm)]

use super::thread::pop_continuation;
use syscalls::Continuation;

extern "C" {
    fn __unwind(cont: &Continuation);
}

pub fn unwind() {
    unsafe {
        let continuation = pop_continuation();
        println!("Unwinding continuation: {:#x?}", continuation);
        __unwind(continuation);
    }
}

/*
 * Restore register and stack state right before the invocation
 * make sure that all registers are restored (specifically, caller
 * registers may be used for passing arguments). Hence we save the
 * function pointer right below the stack (esp - 8) and jump to
 * it from there.
 *
 * Note: interrupts are disabled in the kernel, NMIs are handled on a
 * separate IST stack, so nothing should overwrite memory below the
 * stack (i.e., esp - 8).
 *
 * %rdi -- pointer to Continuation
 */

global_asm!(
    "  
    .text 
    .align  16              
__unwind:
    movq 16(%rdi), %rcx
    movq 24(%rdi), %rdx
    movq 32(%rdi), %rsi

    movq 48(%rdi), %r8
    movq 56(%rdi), %r9
    movq 64(%rdi), %r10


    movq 136(%rdi), %rsp
    movq 128(%rdi), %rbp
    movq 120(%rdi), %rbx
    movq 112(%rdi), %r11
    movq 104(%rdi), %r12
    movq 96(%rdi), %r13
    movq 88(%rdi), %r14
    movq 80(%rdi), %r15
    pushq 72(%rdi)
    popfq

    movq (%rdi), %rax
    movq %rax, -8(%rsp)
    movq 8(%rdi), %rax

    movq 40(%rdi), %rdi

    jmpq *-8(%rsp) ",
    options(att_syntax)
);

/*
 * Unwind test with simple functions
 */
#[no_mangle]
pub fn foo(_x: u64, _y: u64) {
    //unwind();
    println!("you shouldn't see this");
}

#[no_mangle]
pub fn foo_err(x: u64, y: u64) {
    println!("foo was aborted, x:{}, y:{}", x, y);
}

extern "C" {
    fn foo_tramp(x: u64, y: u64);
}

//trampoline!(foo);

/*
 * Unwind test with traits
 */

pub trait FooTrait {
    fn simple_result(&self, x: u64) -> Result<u64, i64>;
}

pub struct Foo {
    id: u64,
}

impl FooTrait for Foo {
    fn simple_result(&self, _x: u64) -> Result<u64, i64> {
        let r = self.id;
        unwind();
        Ok(r)
    }
}

static FOO: Foo = Foo { id: 55 };

#[no_mangle]
pub extern "C" fn simple_result(s: &Foo, x: u64) -> Result<u64, i64> {
    println!("simple_result: s.id:{}, x:{}", s.id, x);
    let r = s.simple_result(x);
    println!("simple_result: you shouldn't see this");
    r
}

#[no_mangle]
pub extern "C" fn simple_result_err(s: &Foo, x: u64) -> Result<u64, i64> {
    println!("simple_result was aborted, s.id:{}, x:{}", s.id, x);
    Err(-1)
}

extern "C" {
    fn simple_result_tramp(s: &Foo, x: u64) -> Result<u64, i64>;
}

//trampoline!(simple_result);

pub fn unwind_test() {
    unsafe {
        /*
        foo_tramp(1, 2);
        let r = simple_result_tramp(&FOO, 3);
        match r {
            Ok(n)  => println!("simple_result (ok):{}", n),
            Err(e) => println!("simple_result, err: {}", e),
        }
        */
    }
}
