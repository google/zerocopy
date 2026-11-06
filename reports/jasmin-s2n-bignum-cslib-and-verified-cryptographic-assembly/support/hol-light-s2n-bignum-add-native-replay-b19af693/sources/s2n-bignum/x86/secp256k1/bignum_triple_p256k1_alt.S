// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Triple modulo p_256k1, z := (3 * x) mod p_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_triple_p256k1_alt(uint64_t z[static 4],
//                                         const uint64_t x[static 4]);
//
// The input x can be any 4-digit bignum, not necessarily reduced modulo
// p_256k1, and the result is always fully reduced, z = (3 * x) mod p_256k1.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_triple_p256k1_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_triple_p256k1_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_triple_p256k1_alt)
        .text

#define z rdi
#define x rsi

// Main digits of intermediate results

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

// Quotient estimate = top of product + 1

#define d rdx
#define h rdx
#define q rdx

// Other temporary variables and their short version

#define a rax
#define c rcx

#define ashort eax
#define qshort edx

S2N_BN_SYMBOL(bignum_triple_p256k1_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// First do the multiplication by 3, getting z = [h; d3; ...; d0]
// but immediately form the quotient estimate q = h + 1

        mov     c, 3

        mov     a, [x]
        mul     c
        mov     d0, a
        mov     d1, d

        mov     a, [x+8]
        xor     d2, d2
        mul     c
        add     d1, a
        adc     d2, d

        mov     a, [x+16]
        mul     c
        add     d2, a
        adc     d, 0

        mov     a, [x+24]
        mov     d3, d
        mul     c
        add     d3, a
        adc     h, 1

// For this limited range a simple quotient estimate of q = h + 1 works, where
// h = floor(z / 2^256). Then -p_256k1 <= z - q * p_256k1 < p_256k1.
// Initial subtraction of z - q * p_256k1, actually by adding q * 4294968273.

        mov     c, 4294968273
        xor     a, a
        imul    q, c
        add     d0, q
        adc     d1, a
        adc     d2, a
        adc     d3, a

// With z = 2^256 * h + l, the underlying result z' is actually
// (2^256 * h + l) - q * (2^256 - 4294968273) = (l + q * 4294968273) - 2^256
// so carry-clear <=> z' is negative. Correct by subtracting in that case.
// In any case, write final result to z as we go.

        cmovc   c, a

        sub     d0, c
        mov     [z], d0
        sbb     d1, a
        mov     [z+8], d1
        sbb     d2, a
        mov     [z+16],d2
        sbb     d3, a
        mov     [z+24],d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_triple_p256k1_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
