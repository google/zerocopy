// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert from almost-Montgomery form, z := (x / 2^256) mod p_sm2
// Input x[4]; output z[4]
//
//    extern void bignum_deamont_sm2(uint64_t z[static 4],
//                                   const uint64_t x[static 4]);
//
// Convert a 4-digit bignum x out of its (optionally almost) Montgomery form,
// "almost" meaning any 4-digit input will work, with no range restriction.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_deamont_sm2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_deamont_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_deamont_sm2)
        .text

#define z rdi
#define x rsi

#define c rcx
#define n1 rax
#define n3 rdx

// ---------------------------------------------------------------------------
// Core one-step "short" Montgomery reduction macro. Takes input in
// [d3;d2;d1;d0] and returns result in [d0;d3;d2;d1], adding to the
// existing contents of [d3;d2;d1], and using rax, rcx, rdx and rsi
// as temporaries.
// ---------------------------------------------------------------------------

#define montreds(d3,d2,d1,d0)                                               \
        mov     rax, d0;                                                    \
        shl     rax, 32;                                                    \
        mov     rcx, d0;                                                    \
        shr     rcx, 32;                                                    \
        mov     rdx, rax;                                                   \
        mov     rsi, rcx;                                                   \
        sub     rax, d0;                                                    \
        sbb     rcx, 0;                                                     \
        sub     d1, rax;                                                    \
        sbb     d2, rcx;                                                    \
        sbb     d3, rdx;                                                    \
        sbb     d0, rsi

S2N_BN_SYMBOL(bignum_deamont_sm2):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Set up an initial 4-word window [r11,r10,r9,r8] = x

        mov     r8, [x]
        mov     r9, [x+8]
        mov     r10, [x+16]
        mov     r11, [x+24]

// Systematically scroll left doing 1-step reductions. This process
// keeps things inside 4 digits (i.e. < 2^256) at each stage, since
// we have w * p_sm2 + x <= (2^64 - 1) * p_sm2 + (2 EXP 256 - 1)
// <= (2^64 - 1) * (2^256 - 1) + (2 EXP 256 - 1) <= 2^64 * (2^256 - 1)

        montreds(r11,r10,r9,r8)

        montreds(r8,r11,r10,r9)

        montreds(r9,r8,r11,r10)

        montreds(r10,r9,r8,r11)

// Let [r11;r10;r9;r8] := [r11;r10;r9;r8] - p_sm2, saving constants
// n1 and n3 in [n3; -1; n1; -1] = p_sm2 for later use.

        sub     r8, -1
        mov     n1, 0xffffffff00000000
        sbb     r9, n1
        sbb     r10, -1
        mov     n3, 0xfffffffeffffffff
        sbb     r11, n3

// Capture the carry to determine whether to add back p_sm2, and use
// it to create a masked p_sm2' = [n3; c; n1; c]

        sbb     c, c
        and     n1, c
        and     n3, c

// Do the corrective addition and copy to output

        add     r8, c
        mov     [z], r8
        adc     r9, n1
        mov     [z+8], r9
        adc     r10, c
        mov     [z+16], r10
        adc     r11, n3
        mov     [z+24], r11

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_deamont_sm2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
