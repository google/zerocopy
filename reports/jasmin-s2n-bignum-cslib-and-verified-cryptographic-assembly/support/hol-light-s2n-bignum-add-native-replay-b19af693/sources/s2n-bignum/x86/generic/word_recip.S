// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Single-word reciprocal, underestimate of 2^128 / a with implicit 1 added
// Input a; output function return
//
//    extern uint64_t word_recip(uint64_t a);
//
// Given an input word "a" with its top bit set (i.e. 2^63 <= a < 2^64), the
// result "x" is implicitly augmented with a leading 1 giving x' = 2^64 + x.
// The result is x' = ceil(2^128 / a) - 1, which except for the single
// special case a = 2^63 is the same thing as x' = floor(2^128 / a).
//
// Standard x86-64 ABI: RDI = a, returns RAX
// Microsoft x64 ABI:   RCX = a, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(word_recip)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(word_recip)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(word_recip)
        .text

#define a rdi
#define x rcx
#define b rsi

# Some aliasing here

#define t rax
#define l rax

#define d rdx
#define h rdx

S2N_BN_SYMBOL(word_recip):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
#endif

// Scale the input down: b overestimates a/2^16 with b <= 2^48 and
// x underestimates 2^64/b with b * x =~= 2^64, accurate to ~2 bits.

        mov     b, a
        mov     x, 0x1FFFFFFFFFFFF
        shr     b, 16
        xor     x, b
        inc     b
        shr     x, 32

// Suppose x = 2^64/b * (1 - e). and get scaled error d = 2^64 * e

        mov     d, b
        imul    d, x
        neg     d

// Rescale to give c = 2^15 * e (so c <= 2^13) and compute
// e + e^2 + e^3 + e^4 = (1 + e^2) (e + e^2)
// = (2^30 + c^2) * (2^15 * c + c^2) / 2^60
// and then x * (1 + e + e^2 + e^3 + e^4)
// = (2^30 * x + x * (2^30 + c^2) * (2^30 * c + c^2) / 2^30) / 2^30

        mov     t, d
        shr     t, 49
        imul    t, t
        shr     d, 34
        add     d, t
        or      t, 0x40000000
        imul    t, d
        shr     t, 30
        imul    t, x
        shl     x, 30
        add     x, t
        shr     x, 30

// Now b * x =~= 2^64, accurate to ~10 bits.
// Do a 64-bit Newton step, scaling up x by 16 bits in the process.

        mov     d, b
        imul    d, x
        neg     d
        shr     d, 24
        imul    d, x
        shl     x, 16
        shr     d, 24
        add     x, d

// Now b * x =~= 2^80, accurate to ~20 bits.
// Do a 64-bit Newton step, scaling up x by 31 bits in the process

        mov     d, b
        imul    d, x
        neg     d
        shr     d, 32
        imul    d, x
        shl     x, 31
        shr     d, 17
        add     x, d

// Now a * x =~= 2^127, accurate to ~40 bits. Do a Newton step at full size.
// Instead of literally negating the product (h,l) we complement bits in
// the extracted bitfield, which is close enough and a bit faster.
// At the end we also shift x one more bit left, losing the known-1 top bit
// so that a * (2^64 + x) =~= 2^128.

        mov     l, a
        mul     x
        shrd    l, h, 60
        mov     h, x
        shr     h, 33
        not     l
        imul    l, h
        shl     x, 1
        shr     l, 33
        add     x, l

// Test if (x' + 1) * a < 2^128 where x' = 2^64 + x, catching the special
// case where x + 1 would wrap, corresponding to input a = 2^63.

        add     x, 1
        mov     l, a
        sbb     x, 0
        mul     x
        mov     rax, x
        add     h, a

// Select either x or x + 1 accordingly as the final answer

        sbb     rax, 0
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(word_recip)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
