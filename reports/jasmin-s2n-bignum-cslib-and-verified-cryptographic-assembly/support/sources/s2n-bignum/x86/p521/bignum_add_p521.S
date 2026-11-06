// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Add modulo p_521, z := (x + y) mod p_521, assuming x and y reduced
// Inputs x[9], y[9]; output z[9]
//
//    extern void bignum_add_p521(uint64_t z[static 9], const uint64_t x[static 9],
//                                const uint64_t y[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_add_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_add_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_add_p521)
        .text

#define z rdi
#define x rsi
#define y rdx

#define d0 rax
#define d1 rcx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11
#define d6 r12
#define d7 rbx

// Re-use the input pointers as other variables once safe to do so

#define d8 rsi
#define m rdx



S2N_BN_SYMBOL(bignum_add_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save more registers to play with

        CFI_PUSH(rbx)
        CFI_PUSH(r12)

// Force carry-in to get s = [d8;d7;d6;d5;d4;d3;d2;d1;d0] = x + y + 1.
// We ignore the carry-out, assuming inputs are reduced so there is none.

        stc
        mov     d0, [x]
        adc     d0, [y]
        mov     d1, [x+8]
        adc     d1, [y+8]
        mov     d2, [x+16]
        adc     d2, [y+16]
        mov     d3, [x+24]
        adc     d3, [y+24]
        mov     d4, [x+32]
        adc     d4, [y+32]
        mov     d5, [x+40]
        adc     d5, [y+40]
        mov     d6, [x+48]
        adc     d6, [y+48]
        mov     d7, [x+56]
        adc     d7, [y+56]
        mov     d8, [x+64]
        adc     d8, [y+64]

// Now x + y >= p_521 <=> s = x + y + 1 >= 2^521
// Make m = 512 * [x + y >= p_521]

        mov     m, 512
        and     m, d8

// Now if x + y >= p_521, we want (x + y) - p_521 = s - 2^521
// while otherwise we want x + y = s - 1
// We use the mask m both as an operand and to generate the dual carry
// Write back the results as generated

        cmp     m, 512

        sbb     d0, 0
        mov     [z], d0
        sbb     d1, 0
        mov     [z+8],  d1
        sbb     d2, 0
        mov     [z+16], d2
        sbb     d3, 0
        mov     [z+24], d3
        sbb     d4, 0
        mov     [z+32], d4
        sbb     d5, 0
        mov     [z+40], d5
        sbb     d6, 0
        mov     [z+48], d6
        sbb     d7, 0
        mov     [z+56], d7
        sbb     d8, m
        mov     [z+64], d8

// Restore registers and return

        CFI_POP(r12)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_add_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
