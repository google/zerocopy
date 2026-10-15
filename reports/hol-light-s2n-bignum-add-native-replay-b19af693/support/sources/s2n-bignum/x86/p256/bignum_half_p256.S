// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Halve modulo p_256, z := (x / 2) mod p_256, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_half_p256(uint64_t z[static 4], const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_half_p256)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_half_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_half_p256)
        .text

#define z rdi
#define x rsi

#define a rax
#define d0 rcx
#define d1 rdx
#define d2 r8
#define d3 r9

#define d0short ecx
#define d1short edx



S2N_BN_SYMBOL(bignum_half_p256):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load lowest digit and get a mask for its lowest bit in d0

        mov     a, [x]
        mov     d0short, 1
        and     d0, a
        neg     d0

// Create a masked version of p_256

        mov     d1short, 0x00000000ffffffff
        xor     d3, d3
        and     d1, d0
        sub     d3, d1
        xor     d2, d2

// Perform addition with masked p_256. Catch the carry in a, as a bitmask
// for convenience though we only use its LSB below with SHRD

        add     d0, a
        adc     d1, [x+8]
        adc     d2, [x+16]
        adc     d3, [x+24]
        sbb     a, a

// Shift right, pushing the carry back down, and store back

        shrd    d0, d1, 1
        mov     [z], d0
        shrd    d1, d2, 1
        mov     [z+8], d1
        shrd    d2, d3, 1
        mov     [z+16], d2
        shrd    d3, a, 1
        mov     [z+24], d3

// Return

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_half_p256)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
