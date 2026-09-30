//#![feature(asm)]
//#![feature(llvm_asm)]

use syscalls::Continuation;

static mut CONT: Continuation 
    = Continuation { 
        func: 0, rflags: 0, r15: 0, r14: 0, r13: 0, r12: 0, r11: 0, rbx: 0, rbp: 0, rsp:0,
        rax: 0, rcx: 0, rdx: 0, rsi: 0, rdi: 0, r8: 0, r9: 0, r10: 0,
    };

pub fn register_cont(cont: &Continuation)  {
    unsafe {
        //CONT = *cont;
        /* memcpy is slower than field copy by 50 cycles */
        CONT.func = cont.func;
        CONT.rflags = cont.rflags;
        CONT.r15 = cont.r15;
        CONT.r14 = cont.r14;
        CONT.r13 = cont.r13;
        CONT.r12 = cont.r12;
        CONT.r11 = cont.r11;
        CONT.rbx = cont.rbx;
        CONT.rbp = cont.rbp;
        CONT.rsp = cont.rsp; 
        CONT.rax = cont.rax;
        CONT.rcx = cont.rcx;
        CONT.rdx = cont.rdx;
        CONT.rsi = cont.rsi;
        CONT.rdi = cont.rdi;
        CONT.r8 = cont.r8;
        CONT.r9 = cont.r9; 
        CONT.r10 = cont.r10;
    }
}

extern {
    fn __unwind(cont: &Continuation);
}

pub fn unwind() {
    unsafe {
        println!("Unwinding continuation: {:#x?}", CONT);
        __unwind(&CONT);
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

global_asm!("  
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

    jmpq *-8(%rsp) ");



/* 
 * Unwind test with simple functions 
 */
#[no_mangle]
pub fn foo(x: u64, y: u64) {
    //unwind();
    println!("you shouldn't see this"); 
}

#[no_mangle]
pub fn foo_err(x: u64, y: u64) {
    println!("foo was aborted, x:{}, y:{}", x, y); 
}

extern {
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
    fn simple_result(&self, x: u64) -> Result<u64, i64> {
        let r = self.id; 
        unwind();
        Ok(r)
    }
}

static FOO: Foo = Foo {id: 55};

#[no_mangle]
pub extern fn simple_result(s: &Foo, x: u64) -> Result<u64, i64> {
    println!("simple_result: s.id:{}, x:{}", s.id, x);
    let r = s.simple_result(x);
    println!("simple_result: you shouldn't see this");
    r
}

#[no_mangle]
pub extern fn simple_result_err(s: &Foo, x: u64) -> Result<u64, i64> {
    println!("simple_result was aborted, s.id:{}, x:{}", s.id, x);
    Err(-1)
}

extern {
    fn simple_result_tramp(s:&Foo, x: u64) -> Result<u64, i64>;
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


