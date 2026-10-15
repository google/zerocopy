// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply by a single word modulo p_25519, z := (c * x) mod p_25519, assuming
// x reduced
// Inputs c, x[4]; output z[4]
//
//    extern void bignum_cmul_p25519(uint64_t z[static 4], uint64_t c,
//                                   const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = c, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cmul_p25519)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cmul_p25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cmul_p25519)
        .text

#define z rdi

// Temporarily moved here for initial multiply

#define x rcx
#define c rcx
#define cshort ecx

// Used as a zero register after the initial move

#define zero rsi
#define zeroe esi

// Likewise this is thrown away after initial multiply

#define d rdx
#define a rax
#define ashort eax

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

S2N_BN_SYMBOL(bignum_cmul_p25519):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Shuffle inputs (since we want multiplier in rdx)

        mov     x, rdx
        mov     d, rsi

// Multiply, accumulating the result as [d4;d3;d2;d1;d0]

        mulx    d1, d0, [x]
        mulx    d2, a, [x+8]
        add     d1, a
        mulx    d3, a, [x+16]
        adc     d2, a
        mulx    a, d, [x+24]
        adc     d3, d
        adc     a, 0

// Let [d4;d3;d2;d1;d0] = 2^255 * h + l, and use q = h + 1 as the initial
// quotient estimate, which is either right or 1 too big.

        shld    a, d3, 1
        mov     cshort, 19
        inc     a
        bts     d3, 63
        mul     c
        xor     zeroe, zeroe
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

S2N_BN_SIZE_DIRECTIVE(bignum_cmul_p25519)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
