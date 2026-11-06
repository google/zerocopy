// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Double modulo p_256k1, z := (2 * x) mod p_256k1, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_double_p256k1(uint64_t z[static 4],
//                                     const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_double_p256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_double_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_double_p256k1)
        .text

#define z rdi
#define x rsi

#define d0 rcx
#define d1 r8
#define d2 r9
#define d3 r10

#define dd rax
#define c rdx

// Re-uses the input x when safe to do so

#define l rsi

S2N_BN_SYMBOL(bignum_double_p256k1):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the inputs and double top-down as z = 2^256 * c + [d3;d2;d1;d0]
// While doing this, create an AND dd of [d3;d2;d1] to condense comparison

        mov     d3, [x+24]
        mov     c, d3
        mov     d2, [x+16]
        shr     c, 63
        shld    d3, d2, 1
        mov     dd, d3
        mov     d1, [x+8]
        shld    d2, d1, 1
        and     dd, d2
        mov     d0, [x]
        shld    d1, d0, 1
        and     dd, d1
        shl     d0, 1

// Decide whether z >= p_256k1 <=> z + 4294968273 >= 2^256.
// For the lowest word use d0 + 4294968273 >= 2^64 <=> ~4294968273 < d0

        mov     l, ~4294968273
        cmp     l, d0
        adc     dd, 0
        adc     c, 0

// Now c <> 0 <=> z >= p_256k1, so mask the constant l accordingly

        not     l
        cmovz   l, c

// If z >= p_256k1 do z := z - p_256k1, i.e. add l in 4 digits

        add     d0, l
        mov     [z], d0
        adc     d1, 0
        mov     [z+8], d1
        adc     d2, 0
        mov     [z+16], d2
        adc     d3, 0
        mov     [z+24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_double_p256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
