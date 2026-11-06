// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply by a single word modulo p_384, z := (c * x) mod p_384, assuming
// x reduced
// Inputs c, x[6]; output z[6]
//
//    extern void bignum_cmul_p384_alt(uint64_t z[static 6], uint64_t c,
//                                     const uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = c, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cmul_p384_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cmul_p384_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cmul_p384_alt)
        .text

#define z rdi

// Temporarily moved here for initial multiply
#define x rcx

// Likewise this is thrown away after initial multiply
#define m rsi

#define a rax
#define c rcx
#define d rdx

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11
#define d4 r12
#define d5 rsi

// Multiplier again for second stage
#define q rcx

#define ashort eax
#define dshort edx

#define cshort ecx
#define qshort ecx

S2N_BN_SYMBOL(bignum_cmul_p384_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// We seem to need (just!) one extra register, which we need to save and restore

        CFI_PUSH(r12)

// Shuffle inputs (since we want rdx for the high parts of products)

        mov     x, rdx

// Multiply, accumulating the result as 2^384 * h + [d5;d4;d3;d2;d1;d0]
// but actually immediately producing q = h + 1, our quotient approximation,
// by adding 1 to it. Note that by hypothesis x is reduced mod p_384, so our
// product is <= (2^64 - 1) * (p_384 - 1) and hence  h <= 2^64 - 2, meaning
// there is no danger this addition of 1 could wrap.

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
        xor     d4, d4
        add     d3, a
        adc     d4, d

        mov     a, [x+32]
        mul     m
        add     d4, a
        adc     d, 0

        mov     a, m
        mov     d5, d
        mul     QWORD PTR [x+40]
        mov     qshort, 1

        add     d5, a
        adc     q, d

// It's easy to see -p_384 <= z - q * p_384 < p_384, so we just need to
// subtract q * p_384 and then correct if that is negative by adding p_384.
//
// Write p_384 = 2^384 - r where r = 2^128 + 2^96 - 2^32 + 1
//
// We want z - q * (2^384 - r)
//       = (2^384 * h + l) - q * (2^384 - r)
//       = 2^384 * (h - q) + (l + q * r)
//       = 2^384 * (-1) + (l + q * r)

        mov     a, 0xffffffff00000001
        mul     q
        add     d0, a
        adc     d1, d
        adc     d2, q
        mov     a, q
        sbb     c, c
        mov     dshort, 0x00000000ffffffff
        neg     c
        mul     d
        add     d1, a
        adc     d2, d
        adc     d3, c
        adc     d4, 0
        adc     d5, 0
        sbb     c, c
        not     c

// The net c value is now the top word of the 7-word answer, hence will
// be -1 if we need a corrective addition, 0 otherwise, usable as a mask.
// Now use that mask for a masked addition of p_384, which again is in
// fact done by a masked subtraction of 2^384 - p_384, so that we only
// have three nonzero digits and so can avoid using another register.

        mov     dshort, 0x00000000ffffffff
        xor     a, a
        and     d, c
        sub     a, d
        and     c, 1

        sub     d0, a
        mov     [z], d0
        sbb     d1, d
        mov     [z+8], d1
        sbb     d2, c
        mov     [z+16], d2
        sbb     d3, 0
        mov     [z+24], d3
        sbb     d4, 0
        mov     [z+32], d4
        sbb     d5, 0
        mov     [z+40], d5

// Return

        CFI_POP(r12)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_cmul_p384_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
