// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery square, z := (x^2 / 2^256) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_montsqr_p256_alt(uint64_t z[static 4],
//                                        const uint64_t x[static 4]);
//
// Does z := (x^2 / 2^256) mod p_256, assuming x^2 <= 2^256 * p_256, which is
// guaranteed in particular if x < p_256 initially (the "intended" case).
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montsqr_p256_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montsqr_p256_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montsqr_p256_alt)
        .text

#define z rdi
#define x rsi

// Add rbx * m into a register-pair (high,low) maintaining consistent
// carry-catching with carry (negated, as bitmask) and using rax and rdx
// as temporaries

#define mulpadd(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rbx;                    \
        sub     rdx, carry;             \
        add     low, rax;               \
        adc     high, rdx;              \
        sbb     carry, carry

// Initial version assuming no carry-in

#define mulpadi(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rbx;                    \
        add     low, rax;               \
        adc     high, rdx;              \
        sbb     carry, carry

// End version not catching the top carry-out

#define mulpade(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rbx;                    \
        sub     rdx, carry;             \
        add     low, rax;               \
        adc     high, rdx

S2N_BN_SYMBOL(bignum_montsqr_p256_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save more registers to play with

        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Compute [r15;r8] = [00] which we use later, but mainly
// set up an initial window [r14;...;r9] = [23;03;01]

        mov     rax, [x]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [x+8]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [x+24]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [x+16]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx

// Chain in the addition of 02 + 12 + 13 to that window (no carry-out possible)
// This gives all the "heterogeneous" terms of the squaring ready to double

        mulpadi(rcx,r11,r10,[x])
        mulpadd(rcx,r12,r11,[x+8])
        mov     rbx, [x+24]
        mulpade(rcx,r13,r12,[x+8])
        adc     r14, 0

// Double the window [r14;...;r9], catching top carry in rcx

        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx

// Add to the 00 + 11 + 22 + 33 terms

        mov     rax, [x+8]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [x+16]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [x+24]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx

// First two waves of Montgomery reduction, now re-using r8 for top carry

        mov     rbx, 0x0000000100000000
        mulpadi(rcx,r10,r9,r8)
        mulpadd(rcx,r11,r10,r9)
        not     rbx
        lea     rbx, [rbx+2]
        mulpadd(rcx,r12,r11,r8)
        xor     r8d, r8d
        mulpade(rcx,r13,r12,r9)
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8

// Now two more steps of Montgomery reduction, again with r8 = top carry

        mov     rbx, 0x0000000100000000
        mulpadi(rcx,r12,r11,r10)
        mulpadd(rcx,r13,r12,r11)
        not     rbx
        lea     rbx, [rbx+2]
        mulpadd(rcx,r14,r13,r10)
        xor     r9d, r9d
        mulpade(rcx,r15,r14,r11)
        adc     r8, r9

// Load [rax;r11;r9;rbx;rcx] = 2^320 - p_256, re-using earlier numbers a bit
// Do [rax;r11;r9;rbx;rcx] = [r8;r15;r14;r13;r12] + (2^320 - p_256)

        mov     ecx, 1
        add     rcx, r12
        lea     rbx, [rbx-1]
        adc     rbx, r13
        lea     r9, [r9-1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d,  0x00000000fffffffe
        adc     r11, r15
        adc     rax, r8

// Now carry is set if r + (2^320 - p_256) >= 2^320, i.e. r >= p_256
// where r is the pre-reduced form. So conditionally select the
// output accordingly.

        cmovc   r12, rcx
        cmovc   r13, rbx
        cmovc   r14, r9
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

S2N_BN_SIZE_DIRECTIVE(bignum_montsqr_p256_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
