// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Add modulo p_25519, z := (x + y) mod p_25519, assuming x and y reduced
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_add_p25519(uint64_t z[static 4], const uint64_t x[static 4],
//                                  const uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_add_p25519)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_add_p25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_add_p25519)
        .text

#define z rdi
#define x rsi
#define y rdx

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

// These also re-use inputs x and y when safe to do so

#define c0 rax
#define c1 rcx
#define c2 rsi
#define c3 rdx
#define c0short eax
#define c1short ecx
#define c2short esi
#define c3short edx

S2N_BN_SYMBOL(bignum_add_p25519):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Add as [d3; d2; d1; d0] = x + y; since we assume x, y < 2^255 - 19
// this sum fits in 256 bits.

        mov     d0, [x]
        add     d0, [y]
        mov     d1, [x+8]
        adc     d1, [y+8]
        mov     d2, [x+16]
        adc     d2, [y+16]
        mov     d3, [x+24]
        adc     d3, [y+24]

// Now x + y >= 2^255 - 19 <=> x + y + 19 >= 2^255.
// Form [c3; c2; c1; c0] = (x + y) + 19

        mov     c0short, 19
        xor     c1short, c1short
        xor     c2short, c2short
        xor     c3short, c3short

        add     c0, d0
        adc     c1, d1
        adc     c2, d2
        adc     c3, d3

// Test the top bit to see if this is >= 2^255, and clear it as a masking
// so that in that case the result is exactly (x + y) - (2^255 - 19).
// Then select the output according to that top bit as that or just x + y.

        btr     c3, 63
        cmovc   d0, c0
        cmovc   d1, c1
        cmovc   d2, c2
        cmovc   d3, c3

// Store the result

        mov     [z], d0
        mov     [z+8], d1
        mov     [z+16], d2
        mov     [z+24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_add_p25519)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
