/* Copyright 2026 The Fuchsia Authors
 *
 * Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
 * <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
 * license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
 * This file may not be copied, modified, or distributed except according to
 * those terms.
 */

#include <stddef.h>
#include <stdint.h>

/* Bug 1: Classic `int len` vs Rust `usize` FFI mismatch.
 * GCC 15.2.0 `-O2` emits `test esi, esi; jle ...` and `sub esi, 1; movsxd rsi, esi`
 * (`48 63 f6`), truncating 64-bit `rsi` to signed 32-bit `esi`. When Rust passes a
 * valid 64-bit slice length `len >= 2^31` (e.g., `0x80000000`), `esi` is negative
 * (`-2147483648 <= 0`) and the C function silently returns `0` instead of
 * `buf[0] + buf[len - 1]`.
 */
uint64_t c_bug1_int_len_endpoints(const uint8_t *buf, int len) {
    if (len <= 0) {
        return 0;
    }
    int last = len - 1;
    return (uint64_t)buf[0] + (uint64_t)buf[last];
}

/* Bug 2: Classic C `char` (signed on System V x86-64!) vs Rust `u8` sign-extension bug.
 * GCC 15.2.0 `-O2` emits `48 0f be 17` (`movsx rdx, BYTE PTR [rdi]`), sign-extending
 * any byte `b >= 0x80` to `0xffffffffffffff80..ff` before XORing into the 64-bit FNV-1a
 * accumulator, diverging from safe-Rust `u8 as u64` zero-extension (`0f b6`).
 */
uint64_t c_bug2_signed_char_fnv1a(const char *buf, size_t len) {
    uint64_t h = 0xcbf29ce484222325ULL;
    for (size_t i = 0; i < len; ++i) {
        h ^= (uint64_t)buf[i];
        h *= 0x100000001b3ULL;
    }
    return h;
}

/* Bug 3: Classic off-by-one `i <= len` loop bound (`jae` instead of `jne`),
 * reading `src[len]` out of bounds and overwriting `dst[len]` past the caller's slice!
 */
void c_bug3_off_by_one_xor(uint8_t *dst, const uint8_t *src, size_t len, uint8_t key) {
    for (size_t i = 0; i <= len; ++i) {
        dst[i] = src[i] ^ key;
    }
}

/* Bug 4: Hand-patched C inline `asm` omitting callee-saved `%rbx`/`%r12` from its
 * clobber list AND omitting `vzeroupper` after dirtying `YMM0[255:128]`.
 * Returns the exact right `rax` sum on every input, yet corrupts Rust caller `%rbx`,
 * `%r12`, and leaves `YMM0[255:128] = 0xffff...ffff` dirty across Legacy SSE2!
 */
uint64_t c_bug4_asm_clobber_abi(const uint8_t *buf, size_t len) {
    uint64_t acc = 0;
    __asm__ volatile (
        "movq $0xdeadbeefcafebabe, %%rbx\n\t"
        "incq %%r12\n\t"
        "vpcmpeqd %%ymm0, %%ymm0, %%ymm0\n\t"
        : "+r"(acc)
        : "r"(buf), "r"(len)
        : "xmm0", "memory"
    );
    for (size_t i = 0; i < len; ++i) {
        acc += buf[i];
    }
    return acc;
}
