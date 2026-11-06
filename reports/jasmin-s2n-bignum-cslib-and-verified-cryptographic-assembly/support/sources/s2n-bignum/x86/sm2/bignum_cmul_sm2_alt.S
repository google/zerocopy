// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply by a single word modulo p_sm2, z := (c * x) mod p_sm2, assuming
// x reduced
// Inputs c, x[4]; output z[4]
//
//    extern void bignum_cmul_sm2_alt(uint64_t z[static 4], uint64_t c,
//                                    const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = c, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cmul_sm2_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cmul_sm2_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cmul_sm2_alt)
        .text

#define z rdi

// Temporarily moved here for initial multiply then thrown away

#define x rcx
#define m rsi

// Other variables

#define d rdx
#define a rax
#define c rcx

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11
#define h rsi

#define hshort esi

// Multiplier again for second stage
#define q rdx
#define qshort edx

S2N_BN_SYMBOL(bignum_cmul_sm2_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Shuffle inputs (since we want rdx for the high parts of products)

        mov     x, rdx

// Multiply, accumulating the result as ca = 2^256 * h + [d3;d2;d1;d0]

        mov     a, [x]
        mul     m
        mov     d0, a
        mov     d1, d

        mov     a, [x+8]
        mul     m
        xor     d2, d2
        add     d1, a
        adc     d2, d

        mov     a, [x+16]
        mul     m
        xor     d3, d3
        add     d2, a
        adc     d3, d

        mov     a, [x+24]
        mul     m
        xor     hshort, hshort
        add     d3, a
        adc     h, d

// Quotient approximation is (h * (1 + 2^32 + 2^64) + d3 + 2^64) >> 64.
// Note that by hypothesis our product is <= (2^64 - 1) * (p_sm2 - 1),
// so there is no need to max this out to avoid wrapping, unlike in the
// more general case of bignum_mod_sm2.

        mov     a, d3
        mov     qshort, 1
        add     a, h
        adc     q, h

        shr     a, 32
        add     a, h
        shr     a, 32
        add     q, a

// Now compute the initial pre-reduced [h;d3;d2;d1;d0] = ca - p_sm2 * q
// = ca - (2^256 - 2^224 - 2^96 + 2^64 - 1) * q

        mov     a, q
        mov     c, q
        shl     a, 32
        shr     c, 32

        add     d3, a
        adc     h, c

        sub     a, q
        sbb     c, 0

        sub     h, q

        add     d0, q
        adc     d1, a
        adc     d2, c
        adc     d3, 0
        adc     h, 0

// Now our top word h is either zero or all 1s, and we use this to discriminate
// whether a correction is needed because our result is negative, as a bitmask
// Do a masked addition of p_sm2

        mov     a, 0xffffffff00000000
        and     a, h
        mov     c, 0xfffffffeffffffff
        and     c, h
        add     d0, h
        mov     [z], d0
        adc     d1, a
        mov     [z+8], d1
        adc     d2, h
        mov     [z+16],d2
        adc     d3, c
        mov     [z+24],d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_cmul_sm2_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
