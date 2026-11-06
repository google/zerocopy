// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Negate modulo p_sm2, z := (-x) mod p_sm2, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_neg_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_neg_sm2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_neg_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_neg_sm2)
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

S2N_BN_SYMBOL(bignum_neg_sm2):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the input digits as [d3;d2;d1;d0] and also set a bitmask q
// for the input being nonzero, so that we avoid doing -0 = p_sm2
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

// Load the non-trivial words of p_sm2 = [n3;-1;n1;-1] and mask them with q

        mov     n1, 0xffffffff00000000
        mov     n3, 0xfffffffeffffffff
        and     n1, q
        and     n3, q

// Do the subtraction, using an xor for the first digit and getting the
// overall result as [n3;q;n1;d0], all these tweaks just to avoid moves

        xor     d0, q
        sub     n1, d1
        sbb     q, d2
        sbb     n3, d3

// Write back

        mov     [z], d0
        mov     [z+8], n1
        mov     [z+16], q
        mov     [z+24], n3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_neg_sm2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
