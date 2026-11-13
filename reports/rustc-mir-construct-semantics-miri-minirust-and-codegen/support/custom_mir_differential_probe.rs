#![feature(custom_mir, core_intrinsics, rustc_attrs)]
#![allow(internal_features, unused_assignments, incomplete_features)]
#![cfg_attr(not(miri), no_std)]
#![cfg_attr(not(miri), no_main)]

use core::intrinsics::mir::*;

#[cfg(not(miri))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(u8)]
#[derive(Copy, Clone)]
pub enum TagEnum {
    A = 10,
    B = 20,
    C = 250,
}

#[repr(u8)]
#[derive(Copy, Clone)]
pub enum PayloadEnum {
    Left(u32) = 1,
    Right(u32, u32) = 2,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Pair(pub u32, pub u32);

// 1. Move-then-Copy of a Copy local in PostCleanup MIR
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn mir_move_then_copy(x: i32) -> i32 {
    mir! {
        let a: i32;
        let b: i32;
        {
            StorageLive(a);
            StorageLive(b);
            a = Move(x);
            b = x;
            RET = a + b;
            StorageDead(b);
            StorageDead(a);
            Return()
        }
    }
}

// 2. CheckedBinaryOp (AddWithOverflow) + Field projection + SwitchInt
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn mir_checked_add_overflow(x: u8, y: u8) -> u16 {
    mir! {
        let res: (u8, bool);
        let sum: u8;
        let sum16: u16;
        let ovf: bool;
        {
            res = Checked(x + y);
            sum = res.0;
            ovf = res.1;
            match ovf {
                false => bb_ok,
                _ => bb_ovf,
            }
        }
        bb_ok = {
            RET = sum as u16;
            Return()
        }
        bb_ovf = {
            sum16 = sum as u16;
            RET = sum16 | 0x0100_u16;
            Return()
        }
    }
}

// 3. Variant + Field projection + SetDiscriminant + Discriminant on payload enum
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn mir_enum_variant_downcast(x: u32, y: u32) -> u32 {
    mir! {
        let e: PayloadEnum;
        let d: u8;
        let d32: u32;
        let f0: u32;
        let f1: u32;
        let fsum: u32;
        {
            StorageLive(e);
            place!(Field(Variant(e, 1), 0)) = x;
            place!(Field(Variant(e, 1), 1)) = y;
            SetDiscriminant(e, 1);
            d = Discriminant(e);
            d32 = d as u32;
            f0 = Field::<u32>(Variant(e, 1), 0);
            f1 = Field::<u32>(Variant(e, 1), 1);
            fsum = f0 + f1;
            RET = fsum + d32;
            StorageDead(e);
            Return()
        }
    }
}

// 4. PtrOffset + Deref + CastUnsize + PtrMetadata + CastTransmute
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub unsafe fn mir_ptr_offset_unsize_metadata(arr: &[u32; 4]) -> u32 {
    mir! {
        let raw_arr: *const [u32; 4];
        let raw_slice: *const [u32];
        let len: usize;
        let len32: u32;
        let idx0: usize;
        let base_ptr: *const u32;
        let elem2_ptr: *const u32;
        let elem2_val: u32;
        let val: i32;
        let trans: u32;
        let tmp: u32;
        {
            raw_arr = &raw const (*arr);
            raw_slice = CastUnsize(raw_arr);
            len = PtrMetadata(raw_slice);
            len32 = len as u32;
            idx0 = 0_usize;
            base_ptr = &raw const (*raw_arr)[idx0];
            elem2_ptr = Offset(base_ptr, 2_usize);
            elem2_val = *elem2_ptr;
            val = -30_i32;
            trans = CastTransmute(val);
            tmp = elem2_val + len32;
            RET = tmp + trans;
            Return()
        }
    }
}

// 5. StatementKind::Intrinsic(Assume) + Repeat + Index
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn mir_assume_and_repeat(v: u32, idx: usize) -> u32 {
    mir! {
        let arr: [u32; 4];
        let ok: bool;
        {
            StorageLive(arr);
            arr = [v; 4];
            ok = idx < 4_usize;
            Assume(ok);
            RET = arr[idx];
            StorageDead(arr);
            Return()
        }
    }
}

// 6. TerminatorKind::Call + TerminatorKind::TailCall
#[inline(never)]
pub fn callee_double(x: u32) -> u32 {
    x.wrapping_mul(2)
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn mir_call_and_tailcall(x: u32) -> u32 {
    mir! {
        let tmp: u32;
        {
            Call(tmp = callee_double(x), ReturnTo(bb_next), UnwindUnreachable())
        }
        bb_next = {
            TailCall(callee_double(tmp))
        }
    }
}

pub fn run_all_checks() -> u32 {
    let mut mask: u32 = 0;
    if mir_move_then_copy(21) == 42 && mir_move_then_copy(-128) == -256 {
        mask |= 1 << 0;
    }
    if mir_checked_add_overflow(200, 50) == 250 && mir_checked_add_overflow(200, 100) == (0x0100 | 44) {
        mask |= 1 << 1;
    }
    if mir_enum_variant_downcast(10, 20) == 32 {
        mask |= 1 << 2;
    }
    let arr = [10_u32, 20, 30, 40];
    if unsafe { mir_ptr_offset_unsize_metadata(&arr) } == 4 {
        mask |= 1 << 3;
    }
    if mir_assume_and_repeat(77, 2) == 77 {
        mask |= 1 << 4;
    }
    if mir_call_and_tailcall(11) == 44 {
        mask |= 1 << 5;
    }
    mask
}

#[cfg(miri)]
fn main() {
    let mask = run_all_checks();
    assert_eq!(mask, 0x3f);
}

#[cfg(not(miri))]
#[no_mangle]
pub unsafe extern "C" fn _start() -> ! {
    let mask = run_all_checks();
    let code: usize = if mask == 0x3f { 0 } else { 1 };
    let msg: &[u8; 21] = if mask == 0x3f { b"CUSTOM_MIR_PASS:0x3f\n" } else { b"CUSTOM_MIR_FAIL:0x00\n" };
    #[cfg(target_arch = "aarch64")]
    core::arch::asm!(
        "mov x8, #64",
        "mov x0, #1",
        "svc #0",
        "mov x8, #94",
        "mov x0, {code:x}",
        "svc #0",
        in("x1") msg.as_ptr(),
        in("x2") msg.len(),
        code = in(reg) code,
        options(noreturn)
    );
    #[cfg(target_arch = "x86")]
    core::arch::asm!(
        "mov eax, 4",
        "mov ebx, 1",
        "int 0x80",
        "mov eax, 252",
        "mov ebx, {code:e}",
        "int 0x80",
        in("ecx") msg.as_ptr(),
        in("edx") msg.len(),
        code = in(reg) code,
        options(noreturn)
    );
    #[cfg(target_arch = "x86_64")]
    core::arch::asm!(
        "mov rax, 1",
        "mov rdi, 1",
        "syscall",
        "mov rax, 231",
        "mov rdi, {code:r}",
        "syscall",
        in("rsi") msg.as_ptr(),
        in("rdx") msg.len(),
        code = in(reg) code,
        options(noreturn)
    );
}
