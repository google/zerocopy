// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery multiply, z := (x * y / 2^256) mod p_sm2
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_montmul_sm2_alt(uint64_t z[static 4],
//                                       const uint64_t x[static 4],
//                                       const uint64_t y[static 4]);
//
// Does z := (2^{-256} * x * y) mod p_sm2, assuming that the inputs x and y
// satisfy x * y <= 2^256 * p_sm2 (in particular this is true if we are in
// the "usual" case x < p_sm2 and y < p_sm2).
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montmul_sm2_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montmul_sm2_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montmul_sm2_alt)
        .text

#define z rdi
#define x rsi

// We move the y argument here so we can use rdx for multipliers

#define y rcx

// Macro for the key "multiply and add to (c,h,l)" step

#define combadd(c,h,l,numa,numb)                \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, 0

// A minutely shorter form for when c = 0 initially

#define combadz(c,h,l,numa,numb)                \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, c

// A short form where we don't expect a top carry

#define combads(h,l,numa,numb)                  \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx

// ---------------------------------------------------------------------------
// Core one-step "short" Montgomery reduction macro. Takes input in
// [d3;d2;d1;d0] and returns result in [d0;d3;d2;d1], adding to the
// existing contents of [d3;d2;d1], and using rax, rcx, rdx and rbx
// as temporaries.
// ---------------------------------------------------------------------------

#define montreds(d3,d2,d1,d0)                                               \
        mov     rax, d0;                                                    \
        shl     rax, 32;                                                    \
        mov     rcx, d0;                                                    \
        shr     rcx, 32;                                                    \
        mov     rdx, rax;                                                   \
        mov     rbx, rcx;                                                   \
        sub     rax, d0;                                                    \
        sbb     rcx, 0;                                                     \
        sub     d1, rax;                                                    \
        sbb     d2, rcx;                                                    \
        sbb     d3, rdx;                                                    \
        sbb     d0, rbx

S2N_BN_SYMBOL(bignum_montmul_sm2_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save more registers to play with

        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Copy y into a safe register to start with

        mov     y, rdx

// Start the window as [r10;r9;r8] with 00 product

        mov     rax, [x]
        mul     QWORD PTR [y]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10

// Column 1

        xor     r11, r11
        combads(r10,r9,[x],[y+8])
        combadz(r11,r10,r9,[x+8],[y])

// Column 2

        xor     r12, r12
        combadz(r12,r11,r10,[x],[y+16])
        combadd(r12,r11,r10,[x+8],[y+8])
        combadd(r12,r11,r10,[x+16],[y])

// Column 3

        xor     r13, r13
        combadz(r13,r12,r11,[x],[y+24])
        combadd(r13,r12,r11,[x+8],[y+16])
        combadd(r13,r12,r11,[x+16],[y+8])
        combadd(r13,r12,r11,[x+24],[y])

// Column 4

        xor     r14, r14
        combadz(r14,r13,r12,[x+8],[y+24])
        combadd(r14,r13,r12,[x+16],[y+16])
        combadd(r14,r13,r12,[x+24],[y+8])

// Column 5

        xor     r15, r15
        combadz(r15,r14,r13,[x+16],[y+24])
        combadd(r15,r14,r13,[x+24],[y+16])

// Final work for columns 6 and 7

        mov     rax, [x+24]
        mul     QWORD PTR [y+24]
        add     r14, rax
        adc     r15, rdx

// Multiplication complete. Perform 4 Montgomery steps to rotate the lower half

        montreds(r11,r10,r9,r8)
        montreds(r8,r11,r10,r9)
        montreds(r9,r8,r11,r10)
        montreds(r10,r9,r8,r11)

// Add high and low parts, catching carry in rax

        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax

// Load [r8;r11;rbx;rdx;rcx] = 2^320 - p_sm2 then do
// [r8;r11;rbx;rdx;rcx] = [rax;r15;r14;r13;r12] + (2^320 - p_sm2)

        mov     ecx, 1
        mov     edx, 0x00000000FFFFFFFF
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+1]
        adc     rdx, r13
        lea     r8, [rbx-1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax

// Now carry is set if r + (2^320 - p_sm2) >= 2^320, i.e. r >= p_sm2
// where r is the pre-reduced form. So conditionally select the
// output accordingly.

        cmovc   r12, rcx
        cmovc   r13, rdx
        cmovc   r14, rbx
        cmovc   r15, r11

// Write back reduced value

        mov     [z], r12
        mov     [z+8], r13
        mov     [z+16], r14
        mov     [z+24], r15

// Restore saved registers and return

        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_montmul_sm2_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
