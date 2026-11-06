// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply-add modulo the order of the curve25519/edwards25519 basepoint
// Inputs x[4], y[4], c[4]; output z[4]
//
//    extern void bignum_madd_n25519_alt(uint64_t z[static 4],
//                                       const uint64_t x[static 4],
//                                       const uint64_t y[static 4],
//                                       const uint64_t c[static 4]);
//
// Performs z := (x * y + c) mod n_25519, where the modulus is
// n_25519 = 2^252 + 27742317777372353535851937790883648493, the
// order of the curve25519/edwards25519 basepoint. The result z
// and the inputs x, y and c are all 4 digits (256 bits).
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y, RCX = c
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y, R9 = c
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_madd_n25519_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_madd_n25519_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_madd_n25519_alt)
        .text

// Single round of modular reduction mod_n25519, mapping
// [m4;m3;m2;m1;m0] = m to [m3;m2;m1;m0] = m mod n_25519,
// *assuming* the input m < 2^64 * n_25519. This is very
// close to the loop body of the bignum_mod_n25519 function.

#define reduce(m4,m3,m2,m1,m0)                                  \
        mov     rbx, m4;                                        \
        shld    rbx, m3, 0x4;                                   \
        shr     m4, 0x3c;                                       \
        sub     rbx, m4;                                        \
        shl     m3, 0x4;                                        \
        shrd    m3, m4, 0x4;                                    \
        movabs  rax, 0x5812631a5cf5d3ed;                        \
        mul     rbx;                                            \
        mov     rbp, rax;                                       \
        mov     rcx, rdx;                                       \
        movabs  rax, 0x14def9dea2f79cd6;                        \
        mul     rbx;                                            \
        add     rcx, rax;                                       \
        adc     rdx, 0x0;                                       \
        sub     m0, rbp;                                        \
        sbb     m1, rcx;                                        \
        sbb     m2, rdx;                                        \
        sbb     m3, 0x0;                                        \
        sbb     rbx, rbx;                                       \
        movabs  rax, 0x5812631a5cf5d3ed;                        \
        and     rax, rbx;                                       \
        movabs  rdx, 0x14def9dea2f79cd6;                        \
        and     rdx, rbx;                                       \
        movabs  rbx, 0x1000000000000000;                        \
        and     rbx, rax;                                       \
        add     m0, rax;                                        \
        adc     m1, rdx;                                        \
        adc     m2, 0x0;                                        \
        adc     m3, rbx

// Special case of "reduce" with m4 = 0. As well as not using m4,
// the quotient selection is slightly simpler, just floor(m/2^252)
// versus min (floor(m/2^252)) (2^63-1).

#define reduce0(m3,m2,m1,m0)                                    \
        mov     rbx, m3;                                        \
        shr     rbx, 60;                                        \
        shl     m3, 4;                                          \
        shr     m3, 4;                                          \
        movabs  rax, 0x5812631a5cf5d3ed;                        \
        mul     rbx;                                            \
        mov     rbp, rax;                                       \
        mov     rcx, rdx;                                       \
        movabs  rax, 0x14def9dea2f79cd6;                        \
        mul     rbx;                                            \
        add     rcx, rax;                                       \
        adc     rdx, 0x0;                                       \
        sub     m0, rbp;                                        \
        sbb     m1, rcx;                                        \
        sbb     m2, rdx;                                        \
        sbb     m3, 0x0;                                        \
        sbb     rbx, rbx;                                       \
        movabs  rax, 0x5812631a5cf5d3ed;                        \
        and     rax, rbx;                                       \
        movabs  rdx, 0x14def9dea2f79cd6;                        \
        and     rdx, rbx;                                       \
        movabs  rbx, 0x1000000000000000;                        \
        and     rbx, rax;                                       \
        add     m0, rax;                                        \
        adc     m1, rdx;                                        \
        adc     m2, 0x0;                                        \
        adc     m3, rbx

S2N_BN_SYMBOL(bignum_madd_n25519_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Save some additional registers for use

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// First compute [r15;r14;r13;r12;r11;r10;r9;r8] = x * y + c. This inserts
// some addition terms for c into a core Comba multiplier similar to
// the start of bignum_mul_p256k1_alt.

        mov     rbp, rdx
        mov     rax, [rsi]
        mul     QWORD PTR [rbp]
        add     rax, [rcx]
        adc     rdx, 0
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsi]
        mul     QWORD PTR [rbp+0x8]
        add     rax, [rcx+8]
        adc     rdx, 0
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rbp]
        add     r9, rax
        adc     r10, rdx
        adc     r11, 0x0
        xor     r12, r12
        mov     rax, [rsi]
        mul     QWORD PTR [rbp+0x10]
        add     rax, [rcx+16]
        adc     rdx, 0
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rbp+0x8]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rbp]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsi]
        mul     QWORD PTR [rbp+0x18]
        add     rax, [rcx+24]
        adc     rdx, 0
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rbp+0x10]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rbp+0x8]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rbp]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rbp+0x18]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rbp+0x10]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rbp+0x8]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rbp+0x18]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rbp+0x10]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rbp+0x18]
        add     r14, rax
        adc     r15, rdx


// Now do the modular reduction and write back

        reduce0(r15,r14,r13,r12)
        reduce(r15,r14,r13,r12,r11)
        reduce(r14,r13,r12,r11,r10)
        reduce(r13,r12,r11,r10,r9)
        reduce(r12,r11,r10,r9,r8)

        mov     [rdi], r8
        mov     [rdi+8], r9
        mov     [rdi+16], r10
        mov     [rdi+24], r11

// Restore registers and return

        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_madd_n25519_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
