// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Negate modulo p_256k1, z := (-x) mod p_256k1, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_neg_p256k1(uint64_t z[static 4], const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_neg_p256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_neg_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_neg_p256k1)
        .text

#define z rdi
#define x rsi

#define q rdx
#define n0 rax
#define n1 rcx
#define n2 r8
#define n3 r9

#define c r10

#define qshort esi

S2N_BN_SYMBOL(bignum_neg_p256k1):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the 4 digits of x and let q be an OR of all the digits

        mov     n0, [x]
        mov     q, n0
        mov     n1, [x+8]
        or      q, n1
        mov     n2, [x+16]
        or      q, n2
        mov     n3, [x+24]
        or      q, n3

// Turn q into a strict bitmask, and c a masked constant -4294968273

        neg     q
        sbb     q, q
        mov     c, -4294968273
        and     c, q

// Now just do [2^256 - 4294968273] - x where the constant is masked

        sub     c, n0
        mov     [z], c
        mov     c, q
        sbb     c, n1
        mov     [z+8], c
        mov     c, q
        sbb     c, n2
        mov     [z+16], c
        sbb     q, n3
        mov     [z+24], q

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_neg_p256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
