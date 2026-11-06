// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo group order, z := x mod n_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_mod_n256k1_4(uint64_t z[static 4],
//                                    const uint64_t x[static 4]);
//
// Reduction is modulo the group order of the secp256k1 curve.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_n256k1_4)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_n256k1_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_n256k1_4)
        .text

#define z rdi
#define x rsi

#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9

#define n0 rax
#define n1 r10
#define n2 r11

#define n2short r11d

// Can re-use this as a temporary once we've loaded the input

#define c rsi

S2N_BN_SYMBOL(bignum_mod_n256k1_4):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load a set of registers [0; n2; n1; n0] = 2^256 - n_256k1

        mov     n0, 0x402da1732fc9bebf
        mov     n1, 0x4551231950b75fc4
        mov     n2short, 1

// Load the input and compute x + (2^256 - n_256k1)

        mov     d0, [x]
        add     d0, n0
        mov     d1, [x+8]
        adc     d1, n1
        mov     d2, [x+16]
        adc     d2, n2
        mov     d3, [x+24]
        adc     d3, 0

// Now CF is set iff 2^256 <= x + (2^256 - n_256k1), i.e. iff n_256k1 <= x.
// Create a mask for the condition x < n, and mask the three nontrivial digits
// ready to undo the previous addition with a compensating subtraction

        sbb     c, c
        not     c
        and     n0, c
        and     n1, c
        and     n2, c

// Now subtract mask * (2^256 - n_256k1) again and store

        sub     d0, n0
        mov     [z], d0
        sbb     d1, n1
        mov     [z+8], d1
        sbb     d2, n2
        mov     [z+16], d2
        sbb     d3, 0
        mov     [z + 24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod_n256k1_4)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
