// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply by a single word modulo p_25519, z := (c * x) mod p_25519, assuming
// x reduced
// Inputs c, x[4]; output z[4]
//
//    extern void bignum_cmul_p25519_alt(uint64_t z[static 4], uint64_t c,
//                                       const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = c, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cmul_p25519_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cmul_p25519_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cmul_p25519_alt)
        .text

#define z rdi

// Temporarily moved here for initial multiply

#define x rcx

// Used as a zero register after the initial move

#define zero rsi
#define zeroe esi

// Likewise this is thrown away after initial multiply

#define d rdx
#define a rax
#define ashort eax

#define c rcx
#define cshort ecx

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11
#define d4 rdx

S2N_BN_SYMBOL(bignum_cmul_p25519_alt):
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

// Multiply, accumulating the result as [d4;d3;d2;d1;d0]

        mov     a, [x]
        mul     rsi
        mov     d0, a
        mov     d1, d

        mov     a, [x+8]
        xor     d2, d2
        mul     rsi
        add     d1, a
        adc     d2, d

        mov     a, [x+16]
        mul     rsi
        add     d2, a
        adc     d, 0

        mov     a, [x+24]
        mov     d3, d
        mul     rsi
        xor     zeroe, zeroe
        add     d3, a
        adc     d4, zero

// Let [d4;d3;d2;d1;d0] = 2^255 * h + l, and use q = h + 1 as the initial
// quotient estimate, which is either right or 1 too big.

        shld    d4, d3, 1
        mov     cshort, 19
        lea     a, [d4+1]
        bts     d3, 63
        mul     c
        add     d0, a
        adc     d1, d
        adc     d2, zero
        adc     d3, zero

// Correct if CF = 0 by subtracting 19, either way masking to
// 255 bits, i.e. by effectively adding p_25519 to the "full" answer

        cmovc   c, zero
        sub     d0, c
        sbb     d1, zero
        sbb     d2, zero
        sbb     d3, zero
        btr     d3, 63

// Write everything back

        mov     [z], d0
        mov     [z+8], d1
        mov     [z+16], d2
        mov     [z+24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_cmul_p25519_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
