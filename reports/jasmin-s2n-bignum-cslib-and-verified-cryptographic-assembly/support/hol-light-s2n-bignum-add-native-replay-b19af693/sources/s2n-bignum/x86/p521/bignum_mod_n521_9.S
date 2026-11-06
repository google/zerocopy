// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo group order, z := x mod n_521
// Input x[9]; output z[9]
//
//    extern void bignum_mod_n521_9(uint64_t z[static 9], const uint64_t x[static 9]);
//
// Reduction is modulo the group order of the NIST curve P-521.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_n521_9)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_n521_9)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_n521_9)
        .text

#define z rdi
#define x rsi

#define q rdx
#define a rax

#define c rcx
#define d r8

#define n0 r9
#define n1 r10
#define n2 r11
#define n3 d

#define ashort eax
#define cshort ecx
#define qshort edx

S2N_BN_SYMBOL(bignum_mod_n521_9):
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

        mov     n0, 0x449048e16ec79bf7
        mulx    c, a, n0
        adcx    a, [x]
        mov     [z], a

        mov     n1, 0xc44a36477663b851
        mulx    d, a, n1
        adcx    a, [x+8]
        adox    a, c
        mov     [z+8],a

        mov     n2, 0x8033feb708f65a2f
        mulx    c, a, n2
        adcx    a, [x+16]
        adox    a, d
        mov     [z+16],a

        mov     a, 0xae79787c40d06994
        mulx    d, a, a
        adcx    a, [x+24]
        adox    a, c
        mov     [z+24],a

        mov     ashort, 5
        mulx    c, a, a
        adcx    a, [x+32]
        adox    a, d
        mov     [z+32], a

        mov     a, c                    // a is now used for zero hereafter
        adox    c, c
        adc     c, [x+40]
        mov     [z+40], c

        mov     c, [x+48]
        adc     c, a
        mov     [z+48], c

        mov     c, [x+56]
        adc     c, a
        mov     [z+56], c

        mov     c, [z+64]
        adc     c, a

// We already know r < n_521, but if it actually went negative then
// we need to add back n_521 again. Recycle q as a bitmask for r < n_521,
// and just subtract r_521 and mask rather than literally adding 2^521.
// This also gets rid of the bit-stuffing above.

        cmc
        sbb     q, q
        and     n0, q
        and     n1, q
        and     n2, q
        mov     n3, 0xae79787c40d06994
        and     n3, q
        and     qshort, 5
        sub     [z], n0
        sbb     [z+8], n1
        sbb     [z+16], n2
        sbb     [z+24], n3
        sbb     [z+32], q
        sbb     [z+40], a
        sbb     [z+48], a
        sbb     [z+56], a
        sbb     cshort, ashort
        and     cshort, 0x1FF
        mov     [z+64], c

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod_n521_9)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
