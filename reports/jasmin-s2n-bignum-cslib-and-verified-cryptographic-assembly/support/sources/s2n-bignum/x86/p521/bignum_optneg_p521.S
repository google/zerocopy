// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Optionally negate modulo p_521, z := (-x) mod p_521 (if p nonzero) or
// z := x (if p zero), assuming x reduced
// Inputs p, x[9]; output z[9]
//
//    extern void bignum_optneg_p521(uint64_t z[static 9], uint64_t p,
//                                   const uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = p, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = p, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optneg_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_optneg_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optneg_p521)
        .text

#define z rdi
#define p rsi
#define x rdx

#define q rax
#define d0 rcx
#define d1 r8
#define d2 r9
#define d3 r10
#define d4 r11

S2N_BN_SYMBOL(bignum_optneg_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Load most inputs (into the limited registers) and OR all of them to get q

        mov     d0, [x]
        mov     q, d0
        mov     d1, [x+8]
        or      q, d1
        mov     d2, [x+16]
        or      q, d2
        mov     d3, [x+24]
        or      q, d3
        mov     d4, [x+32]
        or      q, d4
        or      q, [x+40]
        or      q, [x+48]
        or      q, [x+56]
        or      q, [x+64]

// Turn q into a bitmask for "input is nonzero and p is nonzero", so that
// we avoid doing -0 = p_521 and hence maintain strict modular reduction

        neg     q
        sbb     q, q
        test    p, p
        cmovz   q, p

// Since p_521 is all 1s, the subtraction is just an exclusive-or with q
// to give an optional inversion, with a slight fiddle for the top digit.

        xor     d0, q
        mov     [z], d0
        xor     d1, q
        mov     [z+8], d1
        xor     d2, q
        mov     [z+16], d2
        xor     d3, q
        mov     [z+24], d3
        xor     d4, q
        mov     [z+32], d4
        mov     d0, [x+40]
        xor     d0, q
        mov     [z+40], d0
        mov     d1, [x+48]
        xor     d1, q
        mov     [z+48], d1
        mov     d2, [x+56]
        xor     d2, q
        mov     [z+56], d2
        mov     d3, [x+64]
        and     q, 0x1FF
        xor     d3, q
        mov     [z+64], d3

// Return

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_optneg_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
