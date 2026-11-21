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

/* Kernel 1: 64-bit FNV-1a byte-slice hash.
 * GCC -O2/-O3 emits: counterless pointer-bump loop (`add rsi, rdi` ... `add rdi, 1;
 * cmp rsi, rdi; jne`), 10-byte `movabs r64, imm64` (`48 b8`/`48 b9`), 4-byte/11-byte
 * ModR/M `NOP` (`0f 1f`), `movzx edx, BYTE PTR [rdi]` (`0f b6`), and `imul rax, rcx`
 * with demonic `{SF, ZF, AF, PF}` flags.
 */
uint64_t c_fnv1a64(const uint8_t *buf, size_t len) {
    uint64_t h = 0xcbf29ce484222325ULL;
    for (size_t i = 0; i < len; ++i) {
        h ^= (uint64_t)buf[i];
        h *= 0x100000001b3ULL;
    }
    return h;
}

/* Kernel 2: Adler-32 chunk update (modulo 65521).
 * GCC -O2/-O3 emits: 16-bit sub-register `movzx ecx, dx` (`0f b7 ca`), magic-constant
 * Barrett reduction (`mov r8d, 0x80078071; imul rcx, r8; shr rcx, 47; imul r9d, ecx,
 * 0xfff1; sub eax, r9d`), 6-byte and 11-byte `0f 1f` alignment NOPs, and a counterless
 * pointer-bump loop.
 */
uint32_t c_adler32_chunk(const uint8_t *buf, size_t len, uint32_t init) {
    uint32_t a = init & 0xffffu;
    uint32_t b = init >> 16;
    for (size_t i = 0; i < len; ++i) {
        a = (a + buf[i]) % 65521u;
        b = (b + a) % 65521u;
    }
    return (b << 16) | a;
}

/* Kernel 3: Rolling 32-bit rotate-XOR byte checksum.
 * GCC -O2/-O3 fuses `((acc << 5) | (acc >> 27))` into hardware 32-bit `rol eax, 0x5`
 * (`c1 c0 05`) inside a counterless pointer-bump loop.
 */
uint32_t c_checksum_rol_u8(const uint8_t *buf, size_t len) {
    uint32_t acc = 0;
    for (size_t i = 0; i < len; ++i) {
        acc = ((acc << 5) | (acc >> 27)) ^ (uint32_t)buf[i];
    }
    return acc;
}

/* Kernel 4: In-place ASCII uppercase-to-lowercase conversion.
 * GCC -O2/-O3 emits: 32-bit operand-size `lea edx, [rax - 0x41]` (`8d 50 bf`),
 * 8-bit sub-register `cmp dl, 0x19` (`80 fa 19`), in-loop conditional store diamond
 * (`ja` + `mov BYTE PTR [rdi], al` `88 07`), and counterless pointer-bump schedule.
 */
void c_ascii_tolower(uint8_t *buf, size_t len) {
    for (size_t i = 0; i < len; ++i) {
        uint8_t c = buf[i];
        if ((uint8_t)(c - 65u) < 26u) {
            buf[i] = (uint8_t)(c + 32u);
        }
    }
}

/* Kernel 5: Mixed-width unsigned dot product (`u8` x `u16` -> wrapping `u32`).
 * At `-O2`, GCC auto-vectorizes using 16-element Legacy Non-VEX SSE2 (`66 0f` / `f3 0f`
 * `movdqu`, `punpcklbw`/`hbw`, `pmullw`, `pmulhuw`, `punpcklwd`/`hwd`, `paddd`,
 * `psrldq`, `movd`, preserving caller `YMM[255:128]`) plus a `movzx` (`0f b6`/`0f b7`)
 * scalar tail. At `-O3 -mavx2`, GCC emits 32-element VEX AVX2 -> `vzeroupper` ->
 * 16-element VEX SSE2 -> 8-element `vpmulld` -> 7-way unrolled scalar tail.
 */
uint32_t c_dot_u8_u16(const uint8_t *a, const uint16_t *b, size_t len) {
    uint32_t sum = 0;
    for (size_t i = 0; i < len; ++i) {
        sum += (uint32_t)a[i] * (uint32_t)b[i];
    }
    return sum;
}

/* Kernel 6: Streaming byte-slice XOR cipher (`dst[i] = src[i] ^ key`, non-`restrict`).
 * At `-O2`, GCC emits an indexed scalar loop (`mov [rdi + rax], dl`).
 * At `-O3 -mavx2`, GCC emits:
 *   1. Non-`restrict` runtime pointer-overlap check `((dst - 1) - src) <= 30`,
 *   2. 32-byte AVX2 `vpxor ymm` hot loop running at `sp_delta == 0` (`rsp == rsp_0`),
 *   3. `vzeroupper` + 16-byte VEX SSE2 epilogue at `sp_delta == 0`,
 *   4. Mid-function shrink-wrapped `push rbp; mov rbp, rsp; push rbx` (`sp_delta = -16`),
 *   5. High-byte sub-register `88 df` (`mov bh, bl`) splatting `key` into 16 bits for
 *      8-byte `vpshuflw` + `vpxor` + `vmovq`,
 *   6. Unrolled 1..7-byte scalar tail + `mov rbx, [rbp-8]; leave; ret` (`sp_delta = 0`),
 *   7. Scalar alias fallback loop at `sp_delta == 0`.
 */
void c_xor_stream(uint8_t *dst, const uint8_t *src, size_t len, uint8_t key) {
    for (size_t i = 0; i < len; ++i) {
        dst[i] = src[i] ^ key;
    }
}
