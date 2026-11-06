// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Triple modulo p_384, z := (3 * x) mod p_384
// Input x[6]; output z[6]
//
//    extern void bignum_triple_p384(uint64_t z[static 6],
//                                   const uint64_t x[static 6]);
//
// The input x can be any 6-digit bignum, not necessarily reduced modulo p_384,
// and the result is always fully reduced, i.e. z = (3 * x) mod p_384.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_triple_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_triple_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_triple_p384)
        .text

#define z rdi
#define x rsi

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11
#define d4 rbx
#define d5 rsi

#define a rax
#define c rcx
#define q rdx

#define ashort eax
#define qshort edx

S2N_BN_SYMBOL(bignum_triple_p384):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// We seem to need (just!) one extra register, which we need to save and restore

        CFI_PUSH(rbx)

// Multiply, accumulating the result as 2^384 * h + [d5;d4;d3;d2;d1;d0]
// but actually immediately producing q = h + 1, our quotient approximation,
// by adding 1 to it.

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
        mov     q, [x+32]
        mov     d4, q
        adcx    q, q
        adox    d4, q
        mov     q, [x+40]
        mov     d5, q
        adcx    q, q
        adox    d5, q

        mov     qshort, 1
        adcx    q, a
        adox    q, a

// Initial subtraction of z - q * p_384, with bitmask c for the carry
// Actually done as an addition of (z - 2^384 * h) + q * (2^384 - p_384)
// which, because q = h + 1, is exactly 2^384 + (z - q * p_384), and
// therefore CF <=> 2^384 + (z - q * p_384) >= 2^384 <=> z >= q * p_384.

        mov     c, q
        shl     c, 32
        mov     a, q
        sub     a, c
        sbb     c, 0

        add     d0, a
        adc     d1, c
        adc     d2, q
        adc     d3, 0
        adc     d4, 0
        adc     d5, 0
        sbb     c, c
        not     c

// Now use that mask for a masked addition of p_384, which again is in
// fact done by a masked subtraction of 2^384 - p_384, so that we only
// have three nonzero digits and so can avoid using another register.

        mov     qshort, 0x00000000ffffffff
        xor     ashort, ashort
        and     q, c
        sub     a, q
        neg     c

        sub     d0, a
        mov     [z], d0
        sbb     d1, q
        mov     [z+8], d1
        sbb     d2, c
        mov     [z+16], d2
        sbb     d3, 0
        mov     [z+24], d3
        sbb     d4, 0
        mov     [z+32], d4
        sbb     d5, 0
        mov     [z+40], d5

// Return

        CFI_POP(rbx)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_triple_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
