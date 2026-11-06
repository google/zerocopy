// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Triple modulo p_256, z := (3 * x) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_triple_p256(uint64_t z[static 4],
//                                   const uint64_t x[static 4]);
//
// The input x can be any 4-digit bignum, not necessarily reduced modulo p_256,
// and the result is always fully reduced, i.e. z = (3 * x) mod p_256.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_triple_p256)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_triple_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_triple_p256)
        .text

#define z rdi
#define x rsi

// Main digits of intermediate results

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

// Quotient estimate = top of product + 1

#define q rdx

// Other temporary variables and their short version

#define a rax
#define c rcx

#define ashort eax
#define cshort ecx
#define qshort edx

S2N_BN_SYMBOL(bignum_triple_p256):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// First do the multiplication by 3, getting z = [h; d3; ...; d0]
// but immediately form the quotient estimate q = h + 1

        xor     ashort, ashort

        mov     q, [x]
        mov     d0, q
        adcx    q, q
        adox    d0, q
        mov     q, [x+8]
        mov     d1, q
        adcx    q, q
        adox    d1, q
        mov     q, [x+16]
        mov     d2, q
        adcx    q, q
        adox    d2, q
        mov     q, [x+24]
        mov     d3, q
        adcx    q, q
        adox    d3, q

// For this limited range a simple quotient estimate of q = h + 1 works, where
// h = floor(z / 2^256). Then -p_256 <= z - q * p_256 < p_256, so we just need
// to subtract q * p_256 and then if that's negative, add back p_256.

        mov     qshort, 1
        adcx    q, a
        adox    q, a

// Now compute the initial pre-reduced result z - p_256 * q
// = z - (2^256 - 2^224 + 2^192 + 2^96 - 1) * q
// = z - 2^192 * 0xffffffff00000001 * q - 2^64 * 0x0000000100000000 * q + q

        add     d0, q
        mov     a, 0x0000000100000000
        mulx    c, a, a
        sbb     a, 0
        sbb     c, 0
        sub     d1, a
        sbb     d2, c
        mov     a, 0xffffffff00000001
        mulx    c, a, a
        sbb     d3, a
        sbb     q, c

// q is now effectively the top word of the 5-digits result; this step
// compensates for q = h + 1

        dec     q

// Use that as a bitmask for a masked addition of p_256 and write back

        mov     ashort, 0x00000000ffffffff
        and     a, q
        xor     cshort, cshort
        sub     c, a
        add     d0, q
        mov     [z], d0
        adc     d1, a
        mov     [z+8], d1
        adc     d2, 0
        mov     [z+16],d2
        adc     d3, c
        mov     [z+24],d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_triple_p256)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
