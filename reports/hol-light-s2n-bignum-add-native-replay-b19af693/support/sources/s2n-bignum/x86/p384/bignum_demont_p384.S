// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert from Montgomery form z := (x / 2^384) mod p_384, assuming x reduced
// Input x[6]; output z[6]
//
//    extern void bignum_demont_p384(uint64_t z[static 6],
//                                   const uint64_t x[static 6]);
//
// This assumes the input is < p_384 for correctness. If this is not the case,
// use the variant "bignum_deamont_p384" instead.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_demont_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_demont_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_demont_p384)
        .text

#define z rdi
#define x rsi

// Core one-step "short" Montgomery reduction macro. Takes input in
// [d5;d4;d3;d2;d1;d0] and returns result in [d6;d5;d4;d3;d2;d1],
// adding to the existing contents of [d5;d4;d3;d2;d1;d0]. This
// is intended only for 6-word inputs as in mapping out of Montgomery,
// not for the general case of Montgomery multiplication. It is fine
// for d6 to be the same register as d0.
//
// Parms:  montreds(d6,d5,d4,d3,d2,d1,d0)
//
// We want to add (2^384 - 2^128 - 2^96 + 2^32 - 1) * w
// where w = [d0 + (d0<<32)] mod 2^64

#define montreds(d6,d5,d4,d3,d2,d1,d0)                                  \
/* Our correction multiplier is w = [d0 + (d0<<32)] mod 2^64 */         \
        mov     rdx, d0;                                        \
        shl     rdx, 32;                                        \
        add     rdx, d0;                                        \
/* Construct [rsi;rcx;rax;-] = (2^384 - p_384) * w           */         \
/* We know the lowest word will cancel so we can re-use d0   */         \
/* as a temp.                                                */         \
        xor     rsi, rsi;                                       \
        mov     rax, 0xffffffff00000001;                        \
        mulx    rax, rcx, rax;                                  \
        mov     ecx, 0x00000000ffffffff;                        \
        mulx    rcx, d0, rcx;                                   \
        adc     rax, d0;                                        \
        adc     rcx, rdx;                                       \
        adc     rsi, 0;                                         \
/* Now subtract that and add 2^384 * w                       */         \
        sub     d1, rax;                                        \
        sbb     d2, rcx;                                        \
        sbb     d3, rsi;                                        \
        sbb     d4, 0;                                          \
        sbb     d5, 0;                                          \
        mov     d6, rdx;                                        \
        sbb     d6, 0

S2N_BN_SYMBOL(bignum_demont_p384):
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

S2N_BN_SIZE_DIRECTIVE(bignum_demont_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
