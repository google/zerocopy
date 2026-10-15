// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo basepoint order, z := x mod n_25519
// Input x[4]; output z[4]
//
//    extern void bignum_mod_n25519_4(uint64_t z[static 4],
//                                    const uint64_t x[static 4]);
//
// Reduction is modulo the order of the curve25519/edwards25519 basepoint.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_n25519_4)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_n25519_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_n25519_4)
        .text

#define z rdi
#define x rsi

#define q rcx

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

S2N_BN_SYMBOL(bignum_mod_n25519_4):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the top digit first, get the quotient estimate q = floor(x/2^252)
// and delete it from that digit, in effect doing x' = x - q * 2^252.
// Now we only need x' - q * n_25519' where n_25519' = n_25519 - 2^252

        mov     q, [x+24]
        mov     d3, q
        shr     q, 60
        shl     d3, 4
        shr     d3, 4

// Compute [rdx;d2;d1] = q * n_25519'

        mov     rax, 0x5812631a5cf5d3ed
        mul     q
        mov     d1, rax
        mov     d2, rdx

        mov     rax, 0x14def9dea2f79cd6
        mul     q
        add     d2, rax
        adc     rdx, 0

// Subtract to get [d3;d2;d1;d0] = x - q * n_25519

        mov     d0, [x]
        sub     d0, d1
        mov     d1, [x+8]
        sbb     d1, d2
        mov     d2, [x+16]
        sbb     d2, rdx
        sbb     d3, 0

// Get a bitmask q for the borrow and create masked version of
// non-trivial digits of [rcx;0;rdx;rax] = n_25519. Note that
// rcx = q but we can get it from the corresponding bit of rax.

        sbb     q, q

        mov     rax, 0x5812631a5cf5d3ed
        and     rax, q
        mov     rdx, 0x14def9dea2f79cd6
        and     rdx, q
        mov     rcx, 0x1000000000000000
        and     rcx, rax

// Do compensating addition (iff subtraction borrowed) and store

        add     d0, rax
        mov     [z], d0
        adc     d1, rdx
        mov     [z+8], d1
        adc     d2, 0
        mov     [z+16], d2
        adc     d3, rcx
        mov     [z+24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)

#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod_n25519_4)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
