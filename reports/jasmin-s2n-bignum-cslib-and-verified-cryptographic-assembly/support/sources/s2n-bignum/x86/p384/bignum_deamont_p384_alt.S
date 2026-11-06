// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert from almost-Montgomery form, z := (x / 2^384) mod p_384
// Input x[6]; output z[6]
//
//    extern void bignum_deamont_p384_alt(uint64_t z[static 6],
//                                        const uint64_t x[static 6]);
//
// Convert a 6-digit bignum x out of its (optionally almost) Montgomery form,
// "almost" meaning any 6-digit input will work, with no range restriction.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_deamont_p384_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_deamont_p384_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_deamont_p384_alt)
        .text

#define z rdi
#define x rsi

// Additional temps in the correction phase

#define u rax
#define v rcx
#define w rdx

#define vshort ecx

// Core one-step "short" Montgomery reduction macro. Takes input in
// [d5;d4;d3;d2;d1;d0] and returns result in [d6;d5;d4;d3;d2;d1],
// adding to the existing [d5;d4;d3;d2;d1] and re-using d0 as a
// temporary internally, as well as rax, rcx and rdx.
// It is OK for d6 and d0 to be the same register (they often are)
//
// We want to add (2^384 - 2^128 - 2^96 + 2^32 - 1) * w
// where w = [d0 + (d0<<32)] mod 2^64
//
//       montreds(d6,d5,d4,d3,d2,d1,d0)

#define montreds(d6,d5,d4,d3,d2,d1,d0)                                  \
/* Our correction multiplier is w = [d0 + (d0<<32)] mod 2^64 */         \
        mov     rcx, d0;                                        \
        shl     rcx, 32;                                        \
        add     rcx, d0;                                        \
/* Construct [rax;rdx;d0;-] = (2^384 - p_384) * w            */         \
/* We know the lowest word will cancel so we can re-use d0   */         \
/* and rcx as temps.                                         */         \
        mov     rax, 0xffffffff00000001;                        \
        mul     rcx;                                            \
        mov     d0, rdx;                                        \
        mov     rax, 0x00000000ffffffff;                        \
        mul     rcx;                                            \
        add     d0, rax;                                        \
        mov     eax, 0;                                         \
        adc     rdx, rcx;                                       \
        adc     eax, eax;                                       \
/* Now subtract that and add 2^384 * w                       */         \
        sub     d1, d0;                                         \
        sbb     d2, rdx;                                        \
        sbb     d3, rax;                                        \
        sbb     d4, 0;                                          \
        sbb     d5, 0;                                          \
        mov     d6, rcx;                                        \
        sbb     d6, 0

S2N_BN_SYMBOL(bignum_deamont_p384_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save more registers to play with

        CFI_PUSH(r12)
        CFI_PUSH(r13)

// Set up an initial window [r13,r12,r11,r10,r9,r8] = x

        mov     r8, [x]
        mov     r9, [x+8]
        mov     r10, [x+16]
        mov     r11, [x+24]
        mov     r12, [x+32]
        mov     r13, [x+40]

// Montgomery reduce window 0

        montreds(r8,r13,r12,r11,r10,r9,r8)

// Montgomery reduce window 1

        montreds(r9,r8,r13,r12,r11,r10,r9)

// Montgomery reduce window 2

        montreds(r10,r9,r8,r13,r12,r11,r10)

// Montgomery reduce window 3

        montreds(r11,r10,r9,r8,r13,r12,r11)

// Montgomery reduce window 4

        montreds(r12,r11,r10,r9,r8,r13,r12)

// Montgomery reduce window 5

        montreds(r13,r12,r11,r10,r9,r8,r13)

// Do a test addition of dd = [r13;r12;r11;r10;r9;r8] and
// 2^384 - p_384 = [0;0;0;1;v;u], hence setting CF iff
// dd + (2^384 - p_384) >= 2^384, hence iff dd >= p_384.

        mov     u, 0xffffffff00000001
        mov     vshort, 0x00000000ffffffff

        mov     w, r8
        add     w, u
        mov     w, r9
        adc     w, v
        mov     w, r10
        adc     w, 1
        mov     w, r11
        adc     w, 0
        mov     w, r12
        adc     w, 0
        mov     w, r13
        adc     w, 0

// Convert CF to a bitmask in w

        sbb     w, w

// Masked addition of 2^384 - p_384, hence subtraction of p_384

        and     u, w
        and     v, w
        and     w, 1

        add    r8, u
        adc    r9, v
        adc    r10, w
        adc    r11, 0
        adc    r12, 0
        adc    r13, 0

// Write back the result

        mov     [z], r8
        mov     [z+8], r9
        mov     [z+16], r10
        mov     [z+24], r11
        mov     [z+32], r12
        mov     [z+40], r13

// Restore registers and return

        CFI_POP(r13)
        CFI_POP(r12)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_deamont_p384_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
