// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Negate modulo p_521, z := (-x) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_neg_p521(uint64_t z[static 9], const uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_neg_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_neg_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_neg_p521)
        .text

#define z rdi
#define x rsi

#define p rax
#define d0 rcx
#define d1 rdx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11

S2N_BN_SYMBOL(bignum_neg_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load most inputs (into the limited registers) and OR all of them to get p

        mov     d0, [x]
        mov     p, d0
        mov     d1, [x+8]
        or      p, d1
        mov     d2, [x+16]
        or      p, d2
        mov     d3, [x+24]
        or      p, d3
        mov     d4, [x+32]
        or      p, d4
        mov     d5, [x+40]
        or      p, d5
        or      p, [x+48]
        or      p, [x+56]
        or      p, [x+64]

// Turn p into a bitmask for "input is nonzero", so that we avoid doing
// -0 = p_521 and hence maintain strict modular reduction

        neg     p
        sbb     p, p

// Since p_521 is all 1s, the subtraction is just an exclusive-or with p
// to give an optional inversion, with a slight fiddle for the top digit.

        xor     d0, p
        mov     [z], d0
        xor     d1, p
        mov     [z+8], d1
        xor     d2, p
        mov     [z+16], d2
        xor     d3, p
        mov     [z+24], d3
        xor     d4, p
        mov     [z+32], d4
        xor     d5, p
        mov     [z+40], d5
        mov     d0, [x+48]
        xor     d0, p
        mov     [z+48], d0
        mov     d1, [x+56]
        xor     d1, p
        mov     [z+56], d1
        mov     d2, [x+64]
        and     p, 0x1FF
        xor     d2, p
        mov     [z+64], d2

// Return

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_neg_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
