// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Optionally negate modulo p_256k1, z := (-x) mod p_256k1 (if p nonzero) or
// z := x (if p zero), assuming x reduced
// Inputs p, x[4]; output z[4]
//
//    extern void bignum_optneg_p256k1(uint64_t z[static 4], uint64_t p,
//                                     const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = p, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = p, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optneg_p256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_optneg_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optneg_p256k1)
        .text

#define z rdi
#define q rsi
#define x rdx

#define n0 rax
#define n1 rcx
#define n2 r8
#define n3 r9

#define c r10

#define qshort esi

S2N_BN_SYMBOL(bignum_optneg_p256k1):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Load the 4 digits of x and let c be an OR of all the digits

        mov     n0, [x]
        mov     c, n0
        mov     n1, [x+8]
        or      c, n1
        mov     n2, [x+16]
        or      c, n2
        mov     n3, [x+24]
        or      c, n3

// Turn q into a strict bitmask. Force it to zero if the input is zero,
// to avoid giving -0 = p_256k1, which is not reduced though correct modulo.

        cmovz   q, c
        neg     q
        sbb     q, q

// We want z := if q then (2^256 - 4294968273) - x else x
// which is: [if q then ~x else x] - [if q then 4294968272 else 0]

        xor     n0, q
        xor     n1, q
        xor     n2, q
        xor     n3, q

        mov     c, 4294968272
        and     c, q
        xor     qshort, qshort

        sub     n0, c
        mov     [z], n0
        sbb     n1, q
        mov     [z+8], n1
        sbb     n2, q
        mov     [z+16], n2
        sbb     n3, q
        mov     [z+24], n3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_optneg_p256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
