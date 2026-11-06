// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Subtract modulo p_256k1, z := (x - y) mod p_256k1
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_sub_p256k1(uint64_t z[static 4], const uint64_t x[static 4],
//                                  const uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sub_p256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_sub_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sub_p256k1)
        .text

#define z rdi
#define x rsi
#define y rdx

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

#define zero rax
#define zeroe eax
#define c rcx

S2N_BN_SYMBOL(bignum_sub_p256k1):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Zero a register first

        xor     zeroe, zeroe

// Load and subtract the two inputs as [d3;d2;d1;d0] = x - y (modulo 2^256)

        mov     d0, [x]
        sub     d0, [y]
        mov     d1, [x+8]
        sbb     d1, [y+8]
        mov     d2, [x+16]
        sbb     d2, [y+16]
        mov     d3, [x+24]
        sbb     d3, [y+24]

// Now if x < y we want to add back p_256k1, which staying within 4 digits
// means subtracting 4294968273, since p_256k1 = 2^256 - 4294968273.
// Let c be that constant 4294968273 when x < y, zero otherwise.

        mov     c, 4294968273
        cmovnc  c, zero

// Now correct by adding masked p_256k1, i.e. subtracting c, and write back

        sub     d0, c
        mov     [z], d0
        sbb     d1, zero
        mov     [z+8], d1
        sbb     d2, zero
        mov     [z+16], d2
        sbb     d3, zero
        mov     [z+24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_sub_p256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
