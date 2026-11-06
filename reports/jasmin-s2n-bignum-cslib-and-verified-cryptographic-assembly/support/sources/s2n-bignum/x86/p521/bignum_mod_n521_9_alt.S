// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo group order, z := x mod n_521
// Input x[9]; output z[9]
//
//    extern void bignum_mod_n521_9_alt(uint64_t z[static 9],
//                                      const uint64_t x[static 9]);
//
// Reduction is modulo the group order of the NIST curve P-521.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_n521_9_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_n521_9_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_n521_9_alt)
        .text

#define z rdi
#define x rsi

#define q rcx
#define a rax
#define d rdx

#define c rcx

#define n0 r8
#define n1 r9
#define n2 r10
#define n3 r11

#define ashort eax
#define cshort ecx
#define qshort edx

S2N_BN_SYMBOL(bignum_mod_n521_9_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the top digit, putting a bit-stuffed version in output buffer.
// The initial quotient estimate is q = h + 1 where x = 2^521 * h + t
// The last add also clears the CF and OF flags ready for the carry chain.

        mov     q, [x+64]
        mov     a, ~0x1FF
        or      a, q
        mov     [z+64], a
        shr     q, 9
        add     q, 1

// Now load other digits and form r = x - q * n_521 = (q * r_521 + t) - 2^521,
// which is stored in the output buffer. Thanks to the bit-stuffing at the
// start, we get r' = (q * r_521 + t) + (2^576 - 2^521) = r + 2^576 as the
// computed result including the top carry. Hence CF <=> r >= 0, while
// r' == r (mod 2^521) because things below bit 521 are uncorrupted. We
// keep the top word in the register c since we at least have that one free.

        mov     rax, 0x449048e16ec79bf7
        mul     q
        mov     n0, rax
        mov     n1, rdx

        mov     rax, 0xc44a36477663b851
        mul     q
        xor     n2, n2
        add     n1, rax
        adc     n2, rdx

        mov     rax, 0x8033feb708f65a2f
        mul     q
        xor     n3, n3
        add     n2, rax
        adc     n3, rdx

        mov     rax, 0xae79787c40d06994
        mul     q
        imul    q, 5
        add     n3, rax
        adc     q, rdx
        sbb     rdx, rdx
        neg     rdx

// [rdx;q;n3;n2;n1;n0] = q * r_521

        xor     eax, eax        // rax is used as a zero hereafter
        add     n0, [x]
        mov     [z], n0
        adc     n1, [x+8]
        mov     [z+8], n1
        adc     n2, [x+16]
        mov     [z+16],n2
        adc     n3, [x+24]
        mov     [z+24],n3
        adc     q, [x+32]
        mov     [z+32], q
        adc     rdx, [x+40]
        mov     [z+40], rdx
        mov     d, [x+48]
        adc     d, rax
        mov     [z+48], d
        mov     d, [x+56]
        adc     d, rax
        mov     [z+56], d
        mov     c, [z+64]
        adc     c, rax

// We already know r < n_521, but if it actually went negative then
// we need to add back n_521 again. Use d as a bitmask for r < n_521,
// and just subtract r_521 and mask rather than literally adding 2^521.
// This also gets rid of the bit-stuffing above.

        cmc
        sbb     d, d

        mov     n0, 0x449048e16ec79bf7
        and     n0, d
        mov     n1, 0xc44a36477663b851
        and     n1, d
        mov     n2, 0x8033feb708f65a2f
        and     n2, d
        mov     n3, 0xae79787c40d06994
        and     n3, d
        and     d, 5

        sub     [z], n0
        sbb     [z+8], n1
        sbb     [z+16], n2
        sbb     [z+24], n3
        sbb     [z+32], d
        sbb     [z+40], rax
        sbb     [z+48], rax
        sbb     [z+56], rax
        sbb     cshort, ashort
        and     cshort, 0x1FF
        mov     [z+64], c

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod_n521_9_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
