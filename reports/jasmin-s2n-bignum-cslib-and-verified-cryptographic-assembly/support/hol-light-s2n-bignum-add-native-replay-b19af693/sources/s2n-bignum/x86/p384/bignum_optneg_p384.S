// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Optionally negate modulo p_384, z := (-x) mod p_384 (if p nonzero) or
// z := x (if p zero), assuming x reduced
// Inputs p, x[6]; output z[6]
//
//    extern void bignum_optneg_p384(uint64_t z[static 6], uint64_t p,
//                                   const uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = p, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = p, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optneg_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_optneg_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optneg_p384)
        .text

#define z rdi
#define q rsi
#define x rdx

#define n0 rax
#define n1 rcx
#define n2 r8
#define n3 r9
#define n4 r10
#define n5 r11

#define n0short eax

S2N_BN_SYMBOL(bignum_optneg_p384):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Adjust q by zeroing it if the input is zero (to avoid giving -0 = p_384,
// which is not strictly reduced even though it's correct modulo p_384).
// This step is redundant if we know a priori that the input is nonzero, which
// is the case for the y coordinate of points on the P-384 curve, for example.

        mov     n0, [x]
        or      n0, [x+8]
        mov     n1, [x+16]
        or      n1, [x+24]
        mov     n2, [x+32]
        or      n2, [x+40]
        or      n0, n1
        or      n0, n2
        neg     n0
        sbb     n0, n0
        and     q, n0

// Turn q into a bitmask, all 1s for q=false, all 0s for q=true

        neg     q
        sbb     q, q
        not     q

// Let [n5;n4;n3;n2;n1] = if q then p_384 else -1

        mov     n0short, 0x00000000ffffffff
        or      n0, q
        mov     n1, 0xffffffff00000000
        or      n1, q
        mov     n2, 0xfffffffffffffffe
        or      n2, q
        mov     n3, 0xffffffffffffffff
        mov     n4, n3
        mov     n5, n3

// Subtract so [n5;n4;n3;n2;n1;n0] = if q then p_384 - x else -1 - x

        sub     n0, [x]
        sbb     n1, [x+8]
        sbb     n2, [x+16]
        sbb     n3, [x+24]
        sbb     n4, [x+32]
        sbb     n5, [x+40]

// XOR the words with the bitmask, which in the case q = false has the
// effect of restoring ~(-1 - x) = -(-1 - x) - 1 = 1 + x - 1 = x
// and write back the digits to the output

        xor     n0, q
        mov     [z], n0
        xor     n1, q
        mov     [z+8], n1
        xor     n2, q
        mov     [z+16], n2
        xor     n3, q
        mov     [z+24], n3
        xor     n4, q
        mov     [z+32], n4
        xor     n5, q
        mov     [z+40], n5

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_optneg_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
