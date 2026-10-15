// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Negate modulo p_256, z := (-x) mod p_256, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_neg_p256(uint64_t z[static 4], const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_neg_p256)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_neg_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_neg_p256)
        .text

#define z rdi
#define x rsi

#define q rdx

#define d0 rax
#define d1 rcx
#define d2 r8
#define d3 r9

#define n1 r10
#define n3 r11

#define d0short eax
#define n1short r10d

S2N_BN_SYMBOL(bignum_neg_p256):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the input digits as [d3;d2;d1;d0] and also set a bitmask q
// for the input being nonzero, so that we avoid doing -0 = p_256
// and hence maintain strict modular reduction

        mov     d0, [x]
        mov     d1, [x+8]
        mov     n1, d0
        or      n1, d1
        mov     d2, [x+16]
        mov     d3, [x+24]
        mov     n3, d2
        or      n3, d3
        or      n3, n1
        neg     n3
        sbb     q, q

// Load the non-trivial words of p_256 = [n3;0;n1;-1] and mask them with q

        mov     n1short, 0x00000000ffffffff
        mov     n3, 0xffffffff00000001
        and     n1, q
        and     n3, q

// Do the subtraction, getting it as [n3;d0;n1;q] to avoid moves

        sub     q, d0
        mov     d0short, 0
        sbb     n1, d1
        sbb     d0, d2
        sbb     n3, d3

// Write back

        mov     [z], q
        mov     [z+8], n1
        mov     [z+16], d0
        mov     [z+24], n3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_neg_p256)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
