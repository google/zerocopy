// E46 proposed positive fixture, Rust 1.89.0 / edition 2021, Linux little endian.
// PREPARATION ONLY: not yet compiled or executed. See PLAN.md and CONTRACTS.md.
#![deny(unsafe_op_in_unsafe_fn)]
#![cfg_attr(not(any(target_arch = "aarch64", target_arch = "x86_64")), allow(unused))]
#[cfg(not(all(target_os = "linux", target_env = "gnu", target_endian = "little",
              target_pointer_width = "64",
              any(target_arch = "aarch64", target_arch = "x86_64"))))]
compile_error!("E46 admits only 64-bit little-endian GNU/Linux AArch64 and x86_64");

use std::sync::atomic::{AtomicUsize, Ordering};
use zerocopy::{FromBytes, IntoBytes};
use zerocopy::byteorder::{BigEndian, U64};
mod vectors;
use vectors::*;

#[cfg(target_arch = "aarch64")]
core::arch::global_asm!(include_str!("aarch64.s"));
#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(include_str!("x86_64.s"));

// Declaration contract: CONTRACTS.md fixes the exact ELF definitions and C ABI.
// No caller grants permission for any access outside the spans listed there.
unsafe extern "C" {
    /// # Safety
    /// `out` exclusively permits two initialized, writable aligned u64 words
    /// in one allocation for this call; no retained pointer or other access.
    fn pilot_mul(a: u64, b: u64, out: *mut u64);
    /// # Safety
    /// a/b each permit two initialized readable aligned u64 words; out permits
    /// two writable initialized u64 words, disjoint from both inputs. Inputs
    /// may alias each other. All allocations remain live for the whole call.
    fn pilot_add128(a: *const u64, b: *const u64, out: *mut u64) -> u64;
    fn pilot_bswap(x: u64) -> u64;
    /// # Safety
    /// p permits one initialized aligned u64 read for the duration of the call.
    fn pilot_load(p: *const u64) -> u64;
    /// # Safety
    /// p exclusively permits one aligned initialized u64 write during the call.
    fn pilot_store(p: *mut u64, value: u64);
    /// # Safety
    /// src/dst permit 16 initialized bytes read/write respectively, aligned16,
    /// live throughout the call and disjoint; no pointer is retained.
    fn pilot_copy16(dst: *mut u8, src: *const u8);
    /// # Safety
    /// p comes from a live 16-byte array; offset <=16. Return preserves that
    /// provenance; offset16 is one-past and must never be dereferenced.
    fn pilot_ptr(p: *const u8, offset: usize) -> *const u8;
    fn pilot_call_helper(a: u64, b: u64) -> u64;
    /// # Safety
    /// Same spans/alignment/disjointness as pilot_copy16; NEON/SSE2 present.
    fn pilot_simd_copy16(dst: *mut u8, src: *const u8);
    /// # Safety
    /// dst/a/b each permits exactly16 initialized bytes, aligned16 and live;
    /// dst is exclusive and disjoint from a/b. a and b may alias each other.
    /// NEON/SSE2 present. No FP/SIMD value crosses the function ABI.
    fn pilot_simd_add16(dst: *mut u8, a: *const u8, b: *const u8);
}

static HELPER_CALLS: AtomicUsize = AtomicUsize::new(0);

fn helper_math(a: u64, b: u64) -> u64 {
    a.rotate_left(13) ^ b.wrapping_mul(0x9e3779b185ebca87)
}

// Sole exported definition. No panicking operation and no unwinding through C.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn pilot_helper(a: u64, b: u64) -> u64 {
    HELPER_CALLS.fetch_add(1, Ordering::Relaxed);
    helper_math(a, b)
}

// These Rust baselines remain separately named for compiler/object inspection.
// Their source contracts are typed references/values, not raw foreign spans.
// Agreement on the fixed corpus is not a proof that these ABI domains coincide.
#[inline(never)]
fn rust_mul(a: u64, b: u64) -> (u64, u64) {
    let n = u128::from(a) * u128::from(b);
    (n as u64, (n >> 64) as u64)
}
#[inline(never)]
fn rust_add128(a: &[u64; 2], b: &[u64; 2]) -> (u64, u64, u64) {
    let x = u128::from(a[0]) | (u128::from(a[1]) << 64);
    let y = u128::from(b[0]) | (u128::from(b[1]) << 64);
    let (n, c) = x.overflowing_add(y);
    (n as u64, (n >> 64) as u64, u64::from(c))
}
#[inline(never)]
fn rust_carry(a: u64, b: u64, cin: u64) -> (u64, u64) {
    let n = u128::from(a) + u128::from(b) + u128::from(cin);
    (n as u64, (n >> 64) as u64)
}
#[inline(never)]
fn rust_swap(x: u64) -> u64 { x.swap_bytes() }
#[inline(never)]
fn rust_load(p: &u64) -> u64 { *p }
#[inline(never)]
fn rust_store(p: &mut u64, x: u64) { *p = x; }
#[inline(never)]
fn rust_copy16(source: &[u8; 16], dst: &mut [u8; 16]) { dst.copy_from_slice(source); }
#[inline(never)]
fn rust_ptr(source: &[u8; 16], offset: usize) -> *const u8 {
    source.as_ptr().wrapping_add(offset)
}
#[inline(never)]
fn rust_label(value: u64) -> u64 { if value == 0 { 17 } else { 41 } }
#[inline(never)]
fn rust_add16(a: &[u8; 16], b: &[u8; 16]) -> [u8; 16] {
    std::array::from_fn(|i| a[i].wrapping_add(b[i]))
}
#[inline(never)]
fn rust_call_helper(a: u64, b: u64) -> u64 { pilot_helper(a, b).wrapping_add(1) }

// Same scalar mathematical behavior as the full-function add, with incoming
// carry separately exposed. Domain cin in {0,1} is fixed in generated data.
#[inline(never)]
fn inline_carry(mut a: u64, b: u64, cin: u64) -> (u64, u64) {
    #[cfg(target_arch = "aarch64")]
    {
        let carry: u64;
        // SAFETY: Only declared register operands and flags change. CMP sets
        // C iff cin>=1; for the admitted cin0/1 this is exactly incoming carry.
        // ADCS consumes it then CSET materializes outgoing carry. No memory,
        // stack, call, privileged instruction or feature-dependent instruction.
        unsafe { core::arch::asm!(
            "cmp {cin}, #1", "adcs {a}, {a}, {b}", "cset {carry}, cs",
            a = inout(reg) a, b = in(reg) b, cin = in(reg) cin,
            carry = lateout(reg) carry, options(nomem, nostack)
        ); }
        (a, carry)
    }
    #[cfg(target_arch = "x86_64")]
    {
        let carry: u8;
        // SAFETY: BT reads register bit0, ADC consumes CF, SETC writes the
        // declared byte register only after both inputs have been read. All
        // flags may change; DF is not changed. No memory/stack/call occurs.
        unsafe { core::arch::asm!(
            "bt {cin}, 0", "adc {a}, {b}", "setc {carry}",
            a = inout(reg) a, b = in(reg) b, cin = in(reg) cin,
            carry = lateout(reg_byte) carry, options(nomem, nostack)
        ); }
        (a, u64::from(carry))
    }
}

#[inline(never)]
fn inline_label(value: u64) -> u64 {
    let mut answer = 41_u64;
    // SAFETY: Both paths exit this asm through its fallthrough/declared direct
    // label. Only input register/flags are used, no register is modified by the
    // A64 CBZ; x86 TEST flags are not promised preserved. No asm outputs are
    // combined with labels (that separate feature is not assumed stable).
    // Label's safe assignment is ordinary Rust, not a jump to an arbitrary PC.
    #[cfg(target_arch = "aarch64")]
    unsafe { core::arch::asm!("cbz {value}, {zero}", value = in(reg) value,
        zero = label { answer = 17; }); }
    #[cfg(target_arch = "x86_64")]
    unsafe { core::arch::asm!("test {value}, {value}", "jz {zero}",
        value = in(reg) value, zero = label { answer = 17; }); }
    answer
}

/// # Safety
/// p comes from an initialized u64 borrow, aligned8/readable8 in one allocation;
/// the allocation stays live and no writer acts for this call. No pointer kept.
#[inline(never)]
unsafe fn inline_load(p: *const u64) -> u64 {
    let out: u64;
    // SAFETY: The function's contract supplies the only eight-byte read below.
    // LDR/MOV uses no stack and changes no flag; the pointer operand is read
    // before the late output may reuse its register. Readonly permits this read.
    #[cfg(target_arch = "aarch64")]
    unsafe { core::arch::asm!("ldr {out}, [{p}]", out = lateout(reg) out,
        p = in(reg) p, options(readonly, nostack, preserves_flags)); }
    #[cfg(target_arch = "x86_64")]
    unsafe { core::arch::asm!("mov {out}, [{p}]", out = lateout(reg) out,
        p = in(reg) p, options(readonly, nostack, preserves_flags)); }
    out
}

/// # Safety
/// p derives from an exclusive initialized u64 borrow, aligned8/writable8 in
/// one live allocation, with no competing access until this call returns.
#[inline(never)]
unsafe fn inline_store(p: *mut u64, value: u64) {
    // SAFETY: The contract supplies the sole eight-byte write. No readonly,
    // nomem or pure promise is made; both operands are inputs, no flags/stack
    // change and the pointer does not escape the asm.
    #[cfg(target_arch = "aarch64")]
    unsafe { core::arch::asm!("str {value}, [{p}]", value = in(reg) value,
        p = in(reg) p, options(nostack, preserves_flags)); }
    #[cfg(target_arch = "x86_64")]
    unsafe { core::arch::asm!("mov [{p}], {value}", value = in(reg) value,
        p = in(reg) p, options(nostack, preserves_flags)); }
}

#[repr(C, align(16))]
struct Guard16 { before: [u8; 16], data: [u8; 16], after: [u8; 16] }
impl Guard16 {
    fn new(data: [u8; 16]) -> Self {
        Self { before: [0xa5; 16], data, after: [0x5a; 16] }
    }
    fn intact(&self) -> bool { self.before == [0xa5; 16] && self.after == [0x5a; 16] }
}

// This baseline calls actual pinned zerocopy implementations, not lookalikes.
#[inline(never)]
fn zc_decode(bytes: &[u8; 8]) -> u64 {
    U64::<BigEndian>::read_from_bytes(bytes).expect("exact8 source").get()
}
#[inline(never)]
fn zc_encode(value: u64, bytes: &mut [u8; 8]) {
    let mut wire = U64::<BigEndian>::new(0);
    wire.set(value);
    wire.write_to(bytes).expect("exact8 destination");
}
#[inline(never)]
fn zc_copy16(source: &[u8; 16], dst: &mut [u8; 16]) {
    let copy = <[u8; 16]>::read_from_bytes(source).expect("exact16 source");
    copy.write_to(dst).expect("exact16 destination");
}

fn check(ok: bool, what: &str, count: &mut u64) {
    if !ok {
        eprintln!("E46_MISMATCH case={what} check={count}");
        std::process::exit(2);
    }
    *count += 1;
}

fn main() {
    let mut checks = 0_u64;
    check(std::mem::size_of::<Guard16>() == 48 &&
          std::mem::align_of::<Guard16>() == 16 &&
          std::mem::offset_of!(Guard16, data) == 16, "guard-layout", &mut checks);
    let sentinels = [0x1122334455667788_u64, 0x8877665544332211];
    for [a, b, low, high] in MULTIPLY {
        let mut out = [sentinels[0], 0, 0, sentinels[1]];
        // SAFETY: out is a live initialized [u64;4]. The derived pointer at
        // index1 spans two aligned exclusive words; guards at0/3 stay outside.
        unsafe { pilot_mul(a, b, out.as_mut_ptr().add(1)); }
        check(out == [sentinels[0], low, high, sentinels[1]], "mul-asm", &mut checks);
        check(rust_mul(a, b) == (low, high), "mul-rust", &mut checks);
    }
    for [al, ah, bl, bh, low, high, carry] in ADD128 {
        let a = [al, ah]; let b = [bl, bh];
        let mut out = [sentinels[0], 0, 0, sentinels[1]];
        let b_ptr = if al == bl && ah == bh { a.as_ptr() } else { b.as_ptr() };
        // SAFETY: a/b each initialized aligned [u64;2], immutable for the
        // call; out[1..3] is initialized, exclusive and separately allocated.
        let c = unsafe { pilot_add128(a.as_ptr(), b_ptr, out.as_mut_ptr().add(1)) };
        check(out == [sentinels[0], low, high, sentinels[1]] && c == carry,
              "add128-asm", &mut checks);
        check(rust_add128(&a, &b) == (low, high, carry),
              "add128-rust", &mut checks);
    }
    for [a, b, cin, low, carry] in CARRY {
        check(cin <= 1, "carry-domain", &mut checks);
        check(inline_carry(a, b, cin) == (low, carry), "carry-inline", &mut checks);
        check(rust_carry(a, b, cin) == (low, carry), "carry-rust", &mut checks);
    }
    for [x, expected] in SWAP {
        // SAFETY: exact C ABI definition is register-only; all u64 bits valid.
        check(unsafe { pilot_bswap(x) } == expected, "swap-asm", &mut checks);
        check(rust_swap(x) == expected, "swap-rust", &mut checks);
        let mut encoded = [0; 8]; zc_encode(x, &mut encoded);
        check(encoded == x.to_be_bytes() && zc_decode(&encoded) == x,
              "zerocopy-wire", &mut checks);
        let host_word = u64::from_ne_bytes(encoded);
        check(host_word == expected, "zerocopy-rev-relation", &mut checks);
        let native_read = u64::read_from_bytes(&encoded).expect("exact8 source");
        check(native_read == expected, "zerocopy-native-read", &mut checks);
    }
    for x in WORDS {
        let source = [sentinels[0], x, sentinels[1]];
        let mut dst = [sentinels[0], 0, sentinels[1]];
        // SAFETY: source[1] is one live initialized aligned u64 with immutable
        // read permission; source is unchanged until both load calls return.
        let a = unsafe { pilot_load(source.as_ptr().add(1)) };
        // SAFETY: same live immutable aligned8/readable8 source as above.
        let b = unsafe { inline_load(source.as_ptr().add(1)) };
        check(a == x && b == x && rust_load(&source[1]) == x &&
              source == [sentinels[0], x, sentinels[1]],
              "load-and-source-frame", &mut checks);
        // SAFETY: dst[1] is one live initialized aligned exclusive u64. No
        // Rust access to dst occurs during the foreign call; no pointer kept.
        unsafe { pilot_store(dst.as_mut_ptr().add(1), x); }
        check(dst == [sentinels[0], x, sentinels[1]], "store-and-guards", &mut checks);
        dst[1] = 0;
        // SAFETY: fresh exclusive derived pointer to the same dst[1] span.
        unsafe { inline_store(dst.as_mut_ptr().add(1), x); }
        check(dst == [sentinels[0], x, sentinels[1]], "inline-store-and-guards", &mut checks);
        let mut baseline = [sentinels[0], 0, sentinels[1]];
        rust_store(&mut baseline[1], x);
        check(dst == baseline, "store-rust-baseline", &mut checks);
        check(inline_label(x) == rust_label(x) && rust_label(x) ==
              if x == 0 { 17 } else { 41 }, "inline-label", &mut checks);
    }
    for bytes in VECTORS16 {
        let source = Guard16::new(bytes);
        let mut scalar = Guard16::new([0xcc; 16]);
        let mut simd = Guard16::new([0xcc; 16]);
        let mut zc = Guard16::new([0xcc; 16]);
        let mut baseline = Guard16::new([0xcc; 16]);
        check((source.data.as_ptr() as usize) % 16 == 0 &&
              (scalar.data.as_ptr() as usize) % 16 == 0 &&
              (simd.data.as_ptr() as usize) % 16 == 0, "copy-alignment", &mut checks);
        // SAFETY: repr(C,align16) places each data field at16; source and
        // destinations are separate live initialized Guard16 allocations.
        // Each call has one exact16 read and a disjoint exclusive exact16 write.
        unsafe { pilot_copy16(scalar.data.as_mut_ptr(), source.data.as_ptr()); }
        // SAFETY: same separate aligned16/read16/write16 construction, using
        // baseline NEON (A64) or SSE2 (x86_64); no vector value crosses the ABI.
        unsafe { pilot_simd_copy16(simd.data.as_mut_ptr(), source.data.as_ptr()); }
        zc_copy16(&source.data, &mut zc.data);
        rust_copy16(&source.data, &mut baseline.data);
        check(scalar.data == bytes && simd.data == bytes && zc.data == bytes &&
              baseline.data == bytes, "copy16-four-implementations", &mut checks);
        check(scalar.intact() && simd.intact() && zc.intact() && baseline.intact() && source.intact() &&
              source.data == bytes, "copy16-frame", &mut checks);
        let view = <[u8; 16]>::ref_from_bytes(&source.data).expect("exact16 bytes");
        check(view.as_ptr() == source.data.as_ptr(), "zerocopy-view-pointer", &mut checks);
        for offset in 0..=16 {
            // SAFETY: source.data is a live16-byte array; offset0..16 permits
            // an in-allocation or one-past pointer. Neither result is loaded.
            let got = unsafe { pilot_ptr(source.data.as_ptr(), offset) };
            // SAFETY: same array and bounded offset; add preserves provenance.
            let expected = unsafe { source.data.as_ptr().add(offset) };
            check(got == expected && rust_ptr(&source.data, offset) == expected,
                  "pointer-return-no-dereference", &mut checks);
        }
    }
    for (ai, bi, expected) in SIMD_ADD {
        let a = Guard16::new(VECTORS16[ai]); let b = Guard16::new(VECTORS16[bi]);
        let mut out = Guard16::new([0xcc; 16]);
        let b_ptr = if ai == bi { a.data.as_ptr() } else { b.data.as_ptr() };
        check((a.data.as_ptr() as usize) % 16 == 0 &&
              (b.data.as_ptr() as usize) % 16 == 0 &&
              (out.data.as_ptr() as usize) % 16 == 0, "simd-add-alignment", &mut checks);
        // SAFETY: live initialized aligned16 data fields; input pointers are
        // shared reads (the diagonal aliases a); out is distinct and exclusive.
        // The template performs exactly two16-byte reads and one16-byte write.
        unsafe { pilot_simd_add16(out.data.as_mut_ptr(), a.data.as_ptr(), b_ptr); }
        let baseline = rust_add16(&a.data, &b.data);
        check(out.data == expected && baseline == expected, "simd-add-lanes", &mut checks);
        check(out.intact() && a.intact() && b.intact() &&
              a.data == VECTORS16[ai] && b.data == VECTORS16[bi], "simd-add-frame", &mut checks);
    }
    for [a, b, expected] in HELPER {
        HELPER_CALLS.store(0, Ordering::Relaxed);
        // SAFETY: exact whole function passes the two u64 C arguments to the
        // unique Rust C helper with required stack alignment, returns normally
        // and restores saved state. It has no pointer arguments; helper's only
        // memory effect is the live atomic counter, accurately part of contract.
        let got = unsafe { pilot_call_helper(a, b) };
        check(got == expected && helper_math(a, b).wrapping_add(1) == expected,
              "c-abi-helper-return", &mut checks);
        check(HELPER_CALLS.load(Ordering::Relaxed) == 1, "c-abi-helper-once", &mut checks);
        HELPER_CALLS.store(0, Ordering::Relaxed);
        check(rust_call_helper(a, b) == expected, "c-abi-rust-bounce", &mut checks);
        check(HELPER_CALLS.load(Ordering::Relaxed) == 1, "c-abi-rust-helper-once", &mut checks);
    }
    // Valid safe API error paths. These do not pass short buffers to assembly.
    for len in [7_usize, 9] {
        let source = [0x3c; 9];
        check(U64::<BigEndian>::read_from_bytes(&source[..len]).is_err(),
              "zerocopy-size-rejection", &mut checks);
        let mut dst = [0xa6; 9];
        let wire = U64::<BigEndian>::new(0x1234);
        let result = wire.write_to(&mut dst[..len]);
        check(result.is_err(), "zerocopy-write-size-rejection", &mut checks);
        check(dst == [0xa6; 9], "zerocopy-rejected-write-frame", &mut checks);
    }
    println!("E46_OK arch={} checks={} native_or_emulated=external_receipt",
             std::env::consts::ARCH, checks);
}
