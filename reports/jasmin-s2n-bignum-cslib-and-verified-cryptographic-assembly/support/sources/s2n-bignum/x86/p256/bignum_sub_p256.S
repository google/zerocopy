// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Subtract modulo p_256, z := (x - y) mod p_256
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_sub_p256(uint64_t z[static 4], const uint64_t x[static 4],
//                                const uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sub_p256)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_sub_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sub_p256)
        .text

#define z rdi
#define x rsi
#define y rdx

#define d0 rax
#define d1 rcx
#define d2 r8
#define d3 r9

#define n1 r10
#define n3 rdx
#define c r11

#define n1short r10d



S2N_BN_SYMBOL(bignum_sub_p256):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Load and subtract the two inputs as [d3;d2;d1;d0] = x - y (modulo 2^256)

        mov     d0, [x]
        sub     d0, [y]
        mov     d1, [x+8]
        sbb     d1, [y+8]
        mov     d2, [x+16]
        sbb     d2, [y+16]
        mov     d3, [x+24]
        sbb     d3, [y+24]

// Capture the carry, which indicates x < y, and create corresponding masked
// correction p_256' = [n3; 0; n1; c] to add

        mov     n1short, 0x00000000ffffffff
        sbb     c, c
        xor     n3, n3
        and     n1, c
        sub     n3, n1

// Do the corrective addition and copy to output

        add     d0, c
        mov     [z], d0
        adc     d1, n1
        mov     [z+8], d1
        adc     d2, 0
        mov     [z+16], d2
        adc     d3, n3
        mov     [z+24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_sub_p256)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
