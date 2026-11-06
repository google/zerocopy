// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo group order, z := x mod m_25519
// Input x[4]; output z[4]
//
//    extern void bignum_mod_m25519_4(uint64_t z[static 4],
//                                    const uint64_t x[static 4]);
//
// Reduction is modulo the group order of curve25519/edwards25519.
// This is the full group order, 8 * the standard basepoint order.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_m25519_4)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_m25519_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_m25519_4)
        .text

#define z rdi
#define x rsi

#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9

#define n0 rax
#define n1 r10
#define n3 r11

// Can re-use this as a temporary once we've loaded the input

#define c rsi

S2N_BN_SYMBOL(bignum_mod_m25519_4):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load a set of registers [n3; 0; n1; n0] = m_25519

        mov     n0, 0xc09318d2e7ae9f68
        mov     n1, 0xa6f7cef517bce6b2
        mov     n3, 0x8000000000000000

// Load the input and compute x - m_25519

        mov     d0, [x]
        sub     d0, n0
        mov     d1, [x+8]
        sbb     d1, n1
        mov     d2, [x+16]
        sbb     d2, 0
        mov     d3, [x+24]
        sbb     d3, n3

// Now CF is set iff x < m_25519. Create a mask for that condition and mask
// the three nontrivial digits ready to undo the previous subtraction with
// a compensating addition

        sbb     c, c
        and     n0, c
        and     n1, c
        and     n3, c

// Now add mask * m_25519 again and store

        add     d0, n0
        mov     [z], d0
        adc     d1, n1
        mov     [z+8], d1
        adc     d2, 0
        mov     [z+16], d2
        adc     d3, n3
        mov     [z + 24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod_m25519_4)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
