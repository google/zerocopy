#![no_main]
#![allow(unsafe_op_in_unsafe_fn)]

#[repr(C)]
#[derive(Copy, Clone)]
pub struct NullableI64 {
    pub val: i64,
    pub is_null: bool,
}

unsafe extern "C" {
    fn mlir_trunc_ret_i1(a: i64, flags: i64) -> NullableI64;
    fn mlir_ext_ret_i8(a: i64, flags: i64) -> NullableI64;
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    fn mprotect(addr: *mut u8, len: usize, prot: i32) -> i32;
    fn munmap(addr: *mut u8, len: usize) -> i32;
    fn fork() -> i32;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    fn write(fd: i32, buf: *const core::ffi::c_void, count: usize) -> isize;
    fn _exit(code: i32) -> !;
}

fn xxh64_seed0(input: &[u8]) -> u64 {
    const P1: u64 = 11400714785074694791;
    const P2: u64 = 14029467366897019727;
    const P3: u64 = 1609587929392839161;
    const P4: u64 = 9650029242287828579;
    const P5: u64 = 2870177450012600261;
    let mut i = 0usize;
    let mut h: u64 = P5.wrapping_add(input.len() as u64);
    while i + 8 <= input.len() {
        let k1 = u64::from_le_bytes(input[i..i + 8].try_into().unwrap())
            .wrapping_mul(P2)
            .rotate_left(31)
            .wrapping_mul(P1);
        h = (h ^ k1).rotate_left(27).wrapping_mul(P1).wrapping_add(P4);
        i += 8;
    }
    if i + 4 <= input.len() {
        let k1 = (u32::from_le_bytes(input[i..i + 4].try_into().unwrap()) as u64).wrapping_mul(P1);
        h = (h ^ k1).rotate_left(23).wrapping_mul(P2).wrapping_add(P3);
        i += 4;
    }
    while i < input.len() {
        let k1 = (input[i] as u64).wrapping_mul(P5);
        h = (h ^ k1).rotate_left(11).wrapping_mul(P1);
        i += 1;
    }
    h ^= h >> 33;
    h = h.wrapping_mul(P2);
    h ^= h >> 29;
    h = h.wrapping_mul(P3);
    h ^= h >> 32;
    h
}

#[inline(never)]
pub fn count_true_and_false(f_is_i8: bool, flags: i64) -> (u32, u32, u32) {
    unsafe {
        let r = if f_is_i8 { mlir_ext_ret_i8(32, flags) } else { mlir_trunc_ret_i1(32, flags) };
        let mut t = 0u32;
        let mut f = 0u32;
        if core::hint::black_box(r.is_null) {
            t += 1;
        }
        if core::hint::black_box(!r.is_null) {
            f += 1;
        }
        let mut slot: Option<NullableI64> = None;
        core::ptr::write_volatile(&mut slot, Some(r));
        let is_none = core::ptr::read_volatile(&slot).is_none() as u32;
        (t, f, is_none)
    }
}

unsafe extern "C" fn ref_batch(a: *const i64, b: *const i64, out: *mut i64, n: usize) {
    if n > 0 {
        *out = *a + *b;
    }
}

unsafe extern "C" fn ref_div(a: *const i64, b: *const i64) -> i64 {
    *a + *b
}

fn puts_hex32(prefix: &[u8], v: u32) {
    unsafe {
        let _ = write(1, prefix.as_ptr() as *const _, prefix.len());
        let mut buf = [0u8; 11];
        buf[0] = b'0';
        buf[1] = b'x';
        for i in 0..8 {
            let nib = ((v >> (28 - i * 4)) & 0xf) as u8;
            buf[2 + i] = if nib < 10 { b'0' + nib } else { b'a' + (nib - 10) };
        }
        buf[10] = b'\n';
        let _ = write(1, buf.as_ptr() as *const _, 11);
    }
}

unsafe fn seal_rx_page(tag: u32, code: &[u8]) -> *mut u8 {
    let page = mmap(core::ptr::null_mut(), 4096, 1 | 2, 2 | 0x20, -1, 0);
    core::ptr::write_bytes(page, 0x90, 11);
    *page.add(11) = 0xb8;
    let tb = tag.to_le_bytes();
    *page.add(12) = tb[0];
    *page.add(13) = tb[1];
    *page.add(14) = tb[2];
    *page.add(15) = tb[3];
    core::ptr::copy_nonoverlapping(code.as_ptr(), page.add(16), code.len());
    let _ = mprotect(page, 4096, 1 | 4);
    page
}

unsafe fn run_in_child_signal(f: impl FnOnce()) -> u32 {
    let pid = fork();
    if pid == 0 {
        f();
        _exit(0);
    }
    let mut st = 0i32;
    waitpid(pid, &mut st, 0);
    (st & 0x7f) as u32
}

#[unsafe(no_mangle)]
pub extern "C" fn main() -> i32 {
    unsafe {
        // 1. SysV AMD64 {i64, i1} vs {i64, i8} struct return into #[repr(C)] NullableI64:
        let (ct, cf, cnone) = count_true_and_false(true, 2);
        let (dt, df, dnone) = count_true_and_false(false, 2);
        puts_hex32(b"clean_i8 (t,f,some_is_none) = ", (ct << 16) | (cf << 8) | cnone);
        puts_hex32(b"dirty_i1 (t,f,some_is_none) = ", (dt << 16) | (df << 8) | dnone);

        // 2. KCFI preamble tag verification for void-return and i64-return C signatures:
        let rb = (core::hint::black_box(
            ref_batch as unsafe extern "C" fn(*const i64, *const i64, *mut i64, usize),
        )) as *const u8;
        let emitted_batch_tag = u32::from_le_bytes([*rb.sub(4), *rb.sub(3), *rb.sub(2), *rb.sub(1)]);
        let computed_batch_tag = xxh64_seed0(b"_ZTSFvPKu3i64S1_PS_u5usizeE") as u32;

        let rd = (core::hint::black_box(
            ref_div as unsafe extern "C" fn(*const i64, *const i64) -> i64,
        )) as *const u8;
        let emitted_div_tag = u32::from_le_bytes([*rd.sub(4), *rd.sub(3), *rd.sub(2), *rd.sub(1)]);
        let computed_div_tag = xxh64_seed0(b"_ZTSFu3i64PKS_S1_E") as u32;

        puts_hex32(b"emitted_batch_kcfi_tag      = ", emitted_batch_tag);
        puts_hex32(b"computed_batch_kcfi_tag     = ", computed_batch_tag);
        puts_hex32(b"emitted_div_kcfi_tag        = ", emitted_div_tag);
        puts_hex32(b"computed_div_kcfi_tag       = ", computed_div_tag);

        // 3. KCFI indirect call check: valid tag (rc=0) vs mismatched tag (SIGILL=4):
        let ret_only: &[u8] = &[0x48, 0x8b, 0x07, 0x48, 0x03, 0x06, 0xc3]; // mov rax,[rdi]; add rax,[rsi]; ret
        let ok_page = seal_rx_page(computed_div_tag, ret_only);
        let bad_page = seal_rx_page(computed_div_tag ^ 1, ret_only);
        let fn_ok: unsafe extern "C" fn(*const i64, *const i64) -> i64 =
            core::mem::transmute(ok_page.add(16));
        let fn_bad: unsafe extern "C" fn(*const i64, *const i64) -> i64 =
            core::mem::transmute(bad_page.add(16));
        let sum_ok = (core::hint::black_box(fn_ok))(&19, &23);
        let bad_sig = run_in_child_signal(|| {
            let _ = (core::hint::black_box(fn_bad))(&19, &23);
        });
        munmap(ok_page, 4096);
        munmap(bad_page, 4096);
        puts_hex32(b"kcfi_tagged_call_sum        = ", sum_ok as u32);
        puts_hex32(b"kcfi_wrong_tag_sig(SIGILL)  = ", bad_sig);

        // 4. Unblended cqo;idiv (SIGFPE=8) vs 16-insn branchless cmov+idiv (trap-free):
        let raw_idiv: &[u8] = &[0x48, 0x8b, 0x07, 0x48, 0x99, 0x48, 0xf7, 0x3e, 0xc3];
        let blended_idiv: &[u8] = &[
            0x48, 0x8b, 0x07,                                           // mov rax, [rdi]
            0x48, 0x8b, 0x0e,                                           // mov rcx, [rsi]
            0x41, 0xb8, 0x01, 0x00, 0x00, 0x00,                         // mov r8d, 1
            0x48, 0x85, 0xc9,                                           // test rcx, rcx
            0x49, 0x0f, 0x44, 0xc8,                                     // cmove rcx, r8
            0x49, 0xb9, 00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80,   // movabs r9, -2^63
            0x45, 0x31, 0xd2,                                           // xor r10d, r10d
            0x4c, 0x39, 0xc8,                                           // cmp rax, r9
            0x41, 0x0f, 0x94, 0xc2,                                     // sete r10b
            0x45, 0x31, 0xdb,                                           // xor r11d, r11d
            0x48, 0x83, 0xf9, 0xff,                                     // cmp rcx, -1
            0x41, 0x0f, 0x94, 0xc3,                                     // sete r11b
            0x45, 0x84, 0xda,                                           // test r10b, r11b
            0x49, 0x0f, 0x45, 0xc8,                                     // cmovne rcx, r8
            0x48, 0x99,                                                 // cqo
            0x48, 0xf7, 0xf9,                                           // idiv rcx
            0xc3,                                                       // ret
        ];
        let raw_page = seal_rx_page(computed_div_tag, raw_idiv);
        let safe_page = seal_rx_page(computed_div_tag, blended_idiv);
        let fn_raw: unsafe extern "C" fn(*const i64, *const i64) -> i64 =
            core::mem::transmute(raw_page.add(16));
        let fn_safe: unsafe extern "C" fn(*const i64, *const i64) -> i64 =
            core::mem::transmute(safe_page.add(16));

        let sig_div0 = run_in_child_signal(|| {
            let _ = (core::hint::black_box(fn_raw))(&42, &0);
        });
        let sig_min = run_in_child_signal(|| {
            let _ = (core::hint::black_box(fn_raw))(&i64::MIN, &-1);
        });
        let q_div0 = (core::hint::black_box(fn_safe))(&42, &0);
        let q_min = (core::hint::black_box(fn_safe))(&i64::MIN, &-1);
        let q_42_6 = (core::hint::black_box(fn_safe))(&42, &6);

        munmap(raw_page, 4096);
        munmap(safe_page, 4096);

        puts_hex32(b"raw_idiv_div0_sig(SIGFPE)   = ", sig_div0);
        puts_hex32(b"raw_idiv_min_neg1_sig       = ", sig_min);
        puts_hex32(b"blended_idiv_div0_quot      = ", q_div0 as u32);
        puts_hex32(b"blended_idiv_min_neg1_lo32  = ", q_min as u32);
        puts_hex32(b"blended_idiv_42_div_6_quot  = ", q_42_6 as u32);
        0
    }
}
