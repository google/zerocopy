// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Triple modulo p_521, z := (3 * x) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_triple_p521_alt(uint64_t z[static 9],
//                                       const uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_triple_p521_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_triple_p521_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_triple_p521_alt)
        .text

#define z rdi
#define x rsi

// Digits; d8 is safely also used for the multiplier 3

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11
#define d4 rbx
#define d5 rbp
#define d6 r12
#define d7 rcx // Also used for multiplier m = 3
#define d8 rsi // Overwrites input pointer

// Other variables

#define m rcx
#define a rax
#define d rdx

S2N_BN_SYMBOL(bignum_triple_p521_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save additional registers to use

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)

// Let [d8;...;d0] = x' + x + 1 where x' is a rotation left by 1 bit
// as a 521-bit quantity. This is == 3 * x + 1 (mod p_521) and keeps
// in a more limited range so that the correction is easier. Mostly
// we do just multiply by 3, except that 2 * bit_520 is stuffed in
// at the bottom instead of the top, so the top two digits are a bit
// more intricate.

        mov     m, 3
        mov     d0, [x+64]
        shr     d0, 8
        inc     d0

        mov     a, [x]
        mul     m
        xor     d1, d1
        add     d0, a
        adc     d1, d

        mov     a, [x+8]
        mul     m
        xor     d2, d2
        add     d1, a
        adc     d2, d

        mov     a, [x+16]
        mul     m
        xor     d3, d3
        add     d2, a
        adc     d3, d

        mov     a, [x+24]
        mul     m
        xor     d4, d4
        add     d3, a
        adc     d4, d

        mov     a, [x+32]
        mul     m
        xor     d5, d5
        add     d4, a
        adc     d5, d

        mov     a, [x+40]
        mul     m
        xor     d6, d6
        add     d5, a
        adc     d6, d

        mov     a, [x+48]
        mul     m
        mov     d7, [x+56]
        mov     d8, [x+64]
        add     d6, a
        adc     d, 0

        mov     a, 0xFF
        and     a, d8
        lea     d8, [d8+2*a]

        xor     eax, eax
        add     d, d7
        adc     d8, a
        add     d7, d7
        adc     d8, a
        add     d7, d
        adc     d8, a

// Now d8 >= 2^9 <=> x' + x + 1 >= 2^521 <=> x' + x >= p_521.
// If that is the case we want (x' + x) - p_521 = (x' + x + 1) - 2^521
// while otherwise we want just x' + x = (x' + x + 1) - 1.

        cmp     d8, 0x200

        sbb     d0, a
        mov     [z], d0
        sbb     d1, a
        mov     [z+8], d1
        sbb     d2, a
        mov     [z+16], d2
        sbb     d3, a
        mov     [z+24], d3
        sbb     d4, a
        mov     [z+32], d4
        sbb     d5, a
        mov     [z+40], d5
        sbb     d6, a
        mov     [z+48], d6
        sbb     d7, a
        mov     [z+56], d7
        sbb     d8, a
        and     d8, 0x1FF
        mov     [z+64], d8

// Restore registers and return

        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_triple_p521_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
