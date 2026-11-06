// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Halve modulo p_256k1, z := (x / 2) mod p_256k1, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_half_p256k1(uint64_t z[static 4],
//                                   const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_half_p256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_half_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_half_p256k1)
        .text

#define z rdi
#define x rsi

#define d0 rcx
#define d1 rdx
#define d2 r8
#define d3 r9

#define c rax

S2N_BN_SYMBOL(bignum_half_p256k1):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the 4 digits of x, and letting b be the LSB (whether it's odd)
// construct the constant c = 4294968273 * b

        mov     d0, [x]
        mov     c, 4294968273
        mov     d1, [x+8]
        mov     d3, 1
        and     d3, d0
        mov     d2, [x+16]
        cmovz   c, d3
        mov     d3, [x+24]

// We want (x + b * p_256k1) / 2 where b is that LSB, in {0,1}.
// That amounts to (2^256 * b + x - 4294968273 * b) / 2, and
// modulo 4 words that's the same as ([2^256 * c + x] - c) / 2.
// So do that subtraction and shift a place right as we go.

        sub     d0, c
        sbb     d1, 0
        sbb     d2, 0
        sbb     d3, 0
        sbb     c, 0

// Shift right, pushing the carry back down, and store back

        shrd    d0, d1, 1
        mov     [z], d0
        shrd    d1, d2, 1
        mov     [z+8], d1
        shrd    d2, d3, 1
        mov     [z+16], d2
        shrd    d3, c, 1
        mov     [z+24], d3

// Return

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_half_p256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
