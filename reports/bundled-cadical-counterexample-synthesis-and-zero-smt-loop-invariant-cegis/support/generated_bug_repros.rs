// Auto-generated standalone runnable Rust 1.99.1 `--test` suite catching all 12/12
// SIMD and `asm!` optimization bugs using exact synthesized minimal counterexamples,
// `mmap` + `mprotect(PROT_NONE)` guard pages, and demonic out-of-slice slack poisoning.

use std::arch::asm;
use std::arch::x86_64::*;
use std::sync::atomic::{AtomicUsize, Ordering};

#[repr(C)]
struct SigJmpBuf([u64; 32]);

#[repr(C)]
struct SigInfo {
    si_signo: i32,
    si_errno: i32,
    si_code: i32,
    _pad0: i32,
    si_addr: usize,
    _rest: [u8; 104],
}

#[repr(C)]
struct SigAction {
    sa_sigaction: usize,
    sa_mask: [u64; 16],
    sa_flags: i32,
    sa_restorer: usize,
}

unsafe extern "C" {
    fn mmap(addr: *mut core::ffi::c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut core::ffi::c_void;
    fn munmap(addr: *mut core::ffi::c_void, len: usize) -> i32;
    fn mprotect(addr: *mut core::ffi::c_void, len: usize, prot: i32) -> i32;
    fn __sigsetjmp(env: *mut SigJmpBuf, savemask: i32) -> i32;
    fn siglongjmp(env: *mut SigJmpBuf, val: i32) -> !;
    fn sigaction(signum: i32, act: *const SigAction, oldact: *mut SigAction) -> i32;
}

static mut JMP_ENV: SigJmpBuf = SigJmpBuf([0; 32]);
static FAULT_ADDR: AtomicUsize = AtomicUsize::new(0);

extern "C" fn segv_handler(sig: i32, info: *const SigInfo, _uctx: *mut core::ffi::c_void) {
    unsafe {
        if !info.is_null() {
            FAULT_ADDR.store((*info).si_addr, Ordering::SeqCst);
        }
        siglongjmp(&raw mut JMP_ENV, sig);
    }
}

#[test]
fn bug01_vpmaddubsw_i16_saturation() {
    unsafe {
        let u0: u8 = 255;
        let u1: u8 = 254;
        let s0: i8 = 64;
        let s1: i8 = 65;
        let mut u_arr = [0u8; 16];
        let mut s_arr = [0i8; 16];
        u_arr[0] = u0;
        u_arr[1] = u1;
        s_arr[0] = s0;
        s_arr[1] = s1;
        let vu = _mm_loadu_si128(u_arr.as_ptr() as *const __m128i);
        let vs = _mm_loadu_si128(s_arr.as_ptr() as *const __m128i);
        let ones = _mm_set1_epi16(1);
        let prod16 = _mm_maddubs_epi16(vu, vs);
        let prod32 = _mm_madd_epi16(prod16, ones);
        let simd_val = _mm_cvtsi128_si32(prod32);
        let ref_val = (u0 as i32) * (s0 as i32) + (u1 as i32) * (s1 as i32);
        assert_ne!(simd_val, ref_val, "caught vpmaddubsw signed i16 saturation!");
    }
}

#[test]
fn bug02_swar_mycroft_borrow_bleed() {
    let x: u64 = 0x100;
    let mask = x.wrapping_sub(0x0101_0101_0101_0101) & !x & 0x8080_8080_8080_8080;
    let swar_zero_count = mask.count_ones();
    let ref_zero_count = x.to_le_bytes().iter().filter(|&&b| b == 0).count() as u32;
    assert_ne!(swar_zero_count, ref_zero_count, "caught Mycroft SWAR cross-byte borrow bleed!");
}

#[test]
fn bug03_bsf_zero_undef_dst() {
    unsafe {
        let src: u64 = 0;
        let poison: u64 = 0xdead_beef_cafe_0000 | (0u64);
        let mut out_dst: u64 = poison;
        asm!(
            "bsf {dst}, {src}",
            dst = inout(reg) out_dst,
            src = in(reg) src,
            options(nomem, nostack)
        );
        let ref_tzcnt = src.trailing_zeros() as u64;
        assert_ne!(out_dst, ref_tzcnt, "caught bsf undefined destination register on src == 0!");
    }
}

#[test]
fn bug04_imul_zf_undef_branch() {
    unsafe {
        let a: u64 = 0;
        let b: u64 = 0;
        let prod: u64;
        let zf_after: u8;
        asm!(
            "xor eax, eax",
            "imul {p}, {rhs}",
            "sete {z}",
            p = inout(reg) a => prod,
            rhs = in(reg) b,
            z = out(reg_byte) zf_after,
            out("eax") _,
            options(nomem, nostack)
        );
        let ref_is_zero = prod == 0;
        assert_ne!(zf_after != 0, ref_is_zero, "caught branching on undefined ZF after imul!");
    }
}

#[test]
fn bug05_vmovdqu_cross_page_prot_none_sigsegv() {
    unsafe {
        let slice_len: usize = 0;
        let base = mmap(core::ptr::null_mut(), 8192, 3, 0x22, -1, 0) as *mut u8;
        assert!((base as isize) != -1);
        let guard_page = base.add(4096);
        assert_eq!(mprotect(guard_page as *mut _, 4096, 0), 0);

        let act = SigAction {
            sa_sigaction: segv_handler as *const () as usize,
            sa_mask: [0; 16],
            sa_flags: 0x0000_0004 | 0x4000_0000,
            sa_restorer: 0,
        };
        let mut old: SigAction = core::mem::zeroed();
        assert_eq!(sigaction(11, &act, &mut old), 0);

        // Place valid slice `[ptr, ptr + slice_len)` flush against `guard_page`
        let ptr = base.add(4096 - slice_len.max(1));
        FAULT_ADDR.store(0, Ordering::SeqCst);
        let sig = __sigsetjmp(&raw mut JMP_ENV, 1);
        if sig == 0 {
            let v = _mm256_loadu_si256(ptr as *const __m256i);
            core::hint::black_box(v);
            panic!("expected hardware SIGSEGV on unguarded cross-page vmovdqu!");
        }
        sigaction(11, &old, core::ptr::null_mut());
        munmap(base as *mut _, 8192);
        assert_eq!(sig, 11, "caught hardware SIGSEGV (signal 11)!");
        assert_eq!(FAULT_ADDR.load(Ordering::SeqCst), guard_page as usize);
    }
}

#[test]
fn bug06_off_by_one_tail_mask_demonic_slack() {
    unsafe {
        let base = mmap(core::ptr::null_mut(), 4096, 3, 0x22, -1, 0) as *mut u8;
        assert!((base as isize) != -1);
        let slice_data: [u8; 1] = [0];
        core::ptr::copy_nonoverlapping(slice_data.as_ptr(), base, slice_data.len());
        // Poison out-of-slice slack bytes with synthesized demonic byte `1`
        core::ptr::write_bytes(base.add(slice_data.len()), 1u8, 16);

        let raw64 = core::ptr::read_unaligned(base as *const u64);
        let len = slice_data.len();
        let buggy_masked = raw64 & (!0u64 >> ((7 - len) * 8));
        let mut ref_val = 0u64;
        for (i, &b) in slice_data.iter().enumerate() {
            ref_val |= (b as u64) << (8 * i);
        }
        munmap(base as *mut _, 4096);
        assert_ne!(buggy_masked, ref_val, "caught off-by-one shift mask reading demonic slack byte!");
    }
}

#[test]
fn bug07_ct_vpmovmskb_early_exit_2safety_leak() {
    unsafe {
        let pub_tag: [u8; 16] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let sec1: [u8; 16] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let sec2: [u8; 16] = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

        let run_opt_with_trace = |p: &[u8; 16], s: &[u8; 16]| -> (bool, &'static str) {
            let vp = _mm_loadu_si128(p.as_ptr() as *const __m128i);
            let vs = _mm_loadu_si128(s.as_ptr() as *const __m128i);
            let mask = _mm_movemask_epi8(_mm_cmpeq_epi8(vp, vs));
            if mask == 0xffff {
                (true, "fast_branch_taken")
            } else {
                (false, "fast_branch_not_taken")
            }
        };

        let (out1, trace1) = run_opt_with_trace(&pub_tag, &sec1);
        let (out2, trace2) = run_opt_with_trace(&pub_tag, &sec2);
        assert_eq!(out1, pub_tag == sec1);
        assert_eq!(out2, pub_tag == sec2);
        assert_ne!(trace1, trace2, "caught 2-safety LeakTrace divergence on functionally exact fast-path!");
    }
}

#[test]
fn bug08_pclmulqdq_crc64_poly_bitflip() {
    unsafe {
        let h: u64 = 0;
        let l: u64 = 1;
        let k1: u64 = 0x42f0_e1eb_a9ea_3693;
        let k2_ref: u64 = 0x9d6c_9823_6f55_2e17;
        let k2_bug: u64 = 0xdd6c_9823_6f55_2e17;

        let vh = _mm_set_epi64x(0, h as i64);
        let vl = _mm_set_epi64x(0, l as i64);
        let ref_fold = _mm_xor_si128(
            _mm_clmulepi64_si128(vh, _mm_set_epi64x(0, k1 as i64), 0x00),
            _mm_clmulepi64_si128(vl, _mm_set_epi64x(0, k2_ref as i64), 0x00),
        );
        let bug_fold = _mm_xor_si128(
            _mm_clmulepi64_si128(vh, _mm_set_epi64x(0, k1 as i64), 0x00),
            _mm_clmulepi64_si128(vl, _mm_set_epi64x(0, k2_bug as i64), 0x00),
        );
        let mut r_bytes = [0u128; 1];
        let mut b_bytes = [0u128; 1];
        _mm_storeu_si128(r_bytes.as_mut_ptr() as *mut __m128i, ref_fold);
        _mm_storeu_si128(b_bytes.as_mut_ptr() as *mut __m128i, bug_fold);
        assert_ne!(b_bytes[0], r_bytes[0], "caught pclmulqdq CRC-64 polynomial bit-flip at weight-1 basis!");
    }
}

#[test]
fn bug09_adcx_adox_carry_flag_swap() {
    unsafe {
        let t0: u64 = 0;
        let t1: u64 = 0;
        let a0: u64 = 1229782938247303442;
        let a1: u64 = 1229782938247303441;
        let b: u64 = 15;

        let mut out0 = t0;
        let mut out1 = t1;
        let out2: u64;
        asm!(
            "xor eax, eax",
            "mulx {hi0}, {lo0}, {a0}",
            "adcx {out0}, {lo0}",
            "mulx {hi1}, {lo1}, {a1}",
            "adcx {hi0}, {lo1}",
            "adox {out1}, {hi0}",
            // Bug: uses `adox` instead of `adcx` for `hi1`, dropping `CF` carry!
            "adox {hi1}, rax",
            out0 = inout(reg) out0,
            out1 = inout(reg) out1,
            a0 = in(reg) a0,
            a1 = in(reg) a1,
            in("rdx") b,
            lo0 = out(reg) _,
            hi0 = out(reg) _,
            lo1 = out(reg) _,
            hi1 = out(reg) out2,
            out("rax") _,
            options(nomem, nostack)
        );

        let w = 1u128 << 64;
        let p0 = (a0 as u128) * (b as u128) + (t0 as u128);
        let ref0 = p0 as u64;
        let p1 = (a1 as u128) * (b as u128) + (t1 as u128) + (p0 >> 64);
        let ref1 = p1 as u64;
        let ref2 = (p1 >> 64) as u64;
        let _ = w;
        assert_ne!((out0, out1, out2), (ref0, ref1, ref2), "caught mulx+adcx/adox carry-flag swap!");
    }
}

#[test]
fn bug10_vpshufb_bit7_zeroing() {
    unsafe {
        let mut lut = [0u8; 16];
        lut[0] = 1;
        let mut idx = [0u8; 16];
        idx[0] = 128;
        let vlut = _mm_loadu_si128(lut.as_ptr() as *const __m128i);
        let vidx = _mm_loadu_si128(idx.as_ptr() as *const __m128i);
        let vbug = _mm_shuffle_epi8(vlut, vidx);
        let vref = _mm_shuffle_epi8(vlut, _mm_and_si128(vidx, _mm_set1_epi8(0x0f)));
        let bug0 = (_mm_cvtsi128_si32(vbug) & 0xff) as u8;
        let ref0 = (_mm_cvtsi128_si32(vref) & 0xff) as u8;
        assert_ne!(bug0, ref0, "caught vpshufb bit-7 lane zeroing!");
    }
}

#[test]
fn bug11_vminss_nan_and_signed_zero_swap() {
    unsafe {
        // 11a: Signed-zero tie (`-0.0` vs `+0.0`)
        let a_sz = f32::from_bits(0x80000000);
        let b_sz = f32::from_bits(0x0);
        let r_ab = _mm_cvtss_f32(_mm_min_ss(_mm_set_ss(a_sz), _mm_set_ss(b_sz)));
        let r_ba = _mm_cvtss_f32(_mm_min_ss(_mm_set_ss(b_sz), _mm_set_ss(a_sz)));
        assert_ne!(r_ab.to_bits(), r_ba.to_bits(), "caught vminss signed-zero operand swap!");

        // 11b: NaN propagation (`NaN` vs `+0.0`)
        let a_nan = f32::from_bits(0x7f800001);
        let b_nan = f32::from_bits(0x0);
        let n_ab = _mm_cvtss_f32(_mm_min_ss(_mm_set_ss(a_nan), _mm_set_ss(b_nan)));
        let n_ba = _mm_cvtss_f32(_mm_min_ss(_mm_set_ss(b_nan), _mm_set_ss(a_nan)));
        assert_ne!(n_ab.is_nan(), n_ba.is_nan(), "caught vminss NaN operand-order asymmetry!");
    }
}

#[test]
fn bug12_bzhi_count_ge64_vs_shift() {
    unsafe {
        let x: u64 = 1;
        let n: u32 = 64;
        let ref_bzhi = _bzhi_u64(x, n);
        let bug_shift = x & (1u64.wrapping_shl(n).wrapping_sub(1));
        assert_ne!(bug_shift, ref_bzhi, "caught bzhi >= 64 saturation vs wrapping shift!");
    }
}
