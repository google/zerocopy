// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply by a single word modulo p_256, z := (c * x) mod p_256, assuming
// x reduced
// Inputs c, x[4]; output z[4]
//
//    extern void bignum_cmul_p256_alt(uint64_t z[static 4], uint64_t c,
//                                     const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = c, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cmul_p256_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cmul_p256_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cmul_p256_alt)
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

#define ashort eax
#define hshort esi

// Multiplier again for second stage

#define q rcx

S2N_BN_SYMBOL(bignum_cmul_p256_alt):
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

// Multiply, accumulating the result as 2^256 * h + [d3;d2;d1;d0]

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

// Writing the product as z = 2^256 * h + 2^192 * d3 + t = 2^192 * hl + t, our
// intended quotient approximation is (hl + hl>>32 + 1)>>64. Note that by
// hypothesis our product is <= (2^64 - 1) * (p_256 - 1), so there is no need
// to max this out to avoid wrapping.

        mov     a, h
        shld    a, d3, 32
        mov     q, h
        shr     q, 32
        xor     d, d
        sub     d, 1
        adc     a, d3
        adc     q, h

// Now compute the initial pre-reduced result z - p_256 * q
// = z - (2^256 - 2^224 + 2^192 + 2^96 - 1) * q
// = z - 2^192 * 0xffffffff00000001 * q - 2^64 * 0x0000000100000000 * q + q

        mov     a, 0x0000000100000000
        mul     q
        add     d0, q
        sbb     a, 0
        sbb     d, 0
        sub     d1, a
        sbb     d2, d
        sbb     d3, 0
        sbb     h, 0
        mov     a, 0xffffffff00000001
        mul     q
        sub     d3, a
        sbb     h, d

// Now our top word h is either zero or all 1s, and we use this to discriminate
// whether a correction is needed because our result is negative, as a bitmask
// Do a masked addition of p_256 and write back

        mov     ashort, 0x00000000ffffffff
        and     a, h
        xor     c, c
        sub     c, a
        add     d0, h
        mov     [z], d0
        adc     d1, a
        mov     [z+8], d1
        adc     d2, 0
        mov     [z+16],d2
        adc     d3, c
        mov     [z+24],d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_cmul_p256_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
