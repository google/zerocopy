// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert from Montgomery form z := (x / 2^256) mod p_256k1,
// assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_demont_p256k1(uint64_t z[static 4],
//                                     const uint64_t x[static 4]);
//
// This assumes the input is < p_256k1 for correctness. If this is not the
// case, use the variant "bignum_deamont_p256k1" instead.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_demont_p256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_demont_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_demont_p256k1)
        .text

#define z rdi
#define x rsi

// Re-use x variable for the negated multiplicative inverse of p_256k1

#define w rsi

// The rotating registers for the 4 digits

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

// Other variables. We need d == rdx for mulx instructions

#define a rax
#define d rdx
#define c rcx

S2N_BN_SYMBOL(bignum_demont_p256k1):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Set up an initial 4-word window [d3,d2,d1,d0] = x

        mov     d0, [x]
        mov     d1, [x+8]
        mov     d2, [x+16]
        mov     d3, [x+24]

// Set w to negated multiplicative inverse p_256k1 * w == -1 (mod 2^64).

        mov     w, 0xd838091dd2253531

// Four stages of Montgomery reduction, rotating the register window.
// Use c as a carry-catcher since the imul destroys the flags in general.

        imul    d0, w
        mov     a, 4294968273
        mul     d0
        sub     d1, d
        sbb     c, c

        imul    d1, w
        mov     a, 4294968273
        mul     d1
        neg     c
        sbb     d2, d
        sbb     c, c

        imul    d2, w
        mov     a, 4294968273
        mul     d2
        neg     c
        sbb     d3, d
        sbb     c, c

        imul    d3, w
        mov     a, 4294968273
        mul     d3
        neg     c
        sbb     d0, d

// Finish propagating carry through new top part, write back and return

        mov     [z], d0
        sbb     d1, 0
        mov     [z+8], d1
        sbb     d2, 0
        mov     [z+16], d2
        sbb     d3, 0
        mov     [z+24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_demont_p256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
