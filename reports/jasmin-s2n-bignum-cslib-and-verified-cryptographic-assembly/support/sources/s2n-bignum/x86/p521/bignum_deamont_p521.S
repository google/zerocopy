// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert from Montgomery form z := (x / 2^576) mod p_521
// Input x[9]; output z[9]
//
//    extern void bignum_deamont_p521(uint64_t z[static 9],
//                                    const uint64_t x[static 9]);
//
// Convert a 9-digit bignum x out of its (optionally almost) Montgomery form,
// "almost" meaning any 9-digit input will work, with no range restriction.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_deamont_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_deamont_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_deamont_p521)
        .text

#define z rdi
#define x rsi

#define c rax
#define h rax
#define l rbx

#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11
#define d6 r12
#define d7 r13
#define d8 rbp

S2N_BN_SYMBOL(bignum_deamont_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save more registers to play with

        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(rbp)

// Stash the lowest 55 bits at the top of c, then shift the whole 576-bit
// input right by 9*64 - 521 = 576 - 521 = 55 bits.

        mov     d0, [x]
        mov     c, d0
        shl     c, 9
        mov     d1, [x+8]
        shrd    d0, d1, 55
        mov     d2, [x+16]
        shrd    d1, d2, 55
        mov     d3, [x+24]
        shrd    d2, d3, 55
        mov     d4, [x+32]
        shrd    d3, d4, 55
        mov     d5, [x+40]
        shrd    d4, d5, 55
        mov     d6, [x+48]
        shrd    d5, d6, 55
        mov     d7, [x+56]
        shrd    d6, d7, 55
        mov     d8, [x+64]
        shrd    d7, d8, 55
        shr     d8, 55

// Now writing x = 2^55 * h + l (so here [d8;..d0] = h and c = 2^9 * l)
// we want (h + 2^{521-55} * l) mod p_521 = s mod p_521. Since s < 2 * p_521
// this is just "if s >= p_521 then s - p_521 else s". First get
// s + 1, but pad up the top to get a top-bit carry-out from it, so now
// CF <=> s + 1 >= 2^521 <=> s >= p_521, while the digits [d8;...d0] are
// now s + 1 except for bits above 521.

        mov     l, c
        shr     h, 55
        shl     l, 9
        or      d8, ~0x1FF
        add     d0, 1
        adc     d1, 0
        adc     d2, 0
        adc     d3, 0
        adc     d4, 0
        adc     d5, 0
        adc     d6, 0
        adc     d7, l
        adc     d8, h

// We want "if CF then (s + 1) - 2^521 else (s + 1) - 1" so subtract ~CF
// and mask to 521 bits, writing digits back as they are created.

        cmc
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
        sbb     d8, 0
        and     d8, 0x1FF
        mov     [z+64], d8

// Restore registers and return

        CFI_POP(rbp)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_deamont_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
