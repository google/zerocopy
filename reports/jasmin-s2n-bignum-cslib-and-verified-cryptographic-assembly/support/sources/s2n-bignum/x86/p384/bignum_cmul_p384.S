// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply by a single word modulo p_384, z := (c * x) mod p_384, assuming
// x reduced
// Inputs c, x[6]; output z[6]
//
//    extern void bignum_cmul_p384(uint64_t z[static 6], uint64_t c,
//                                 const uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = c, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cmul_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cmul_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cmul_p384)
        .text

#define z rdi

// Temporarily moved here for initial multiply
#define x rcx
// Likewise this is thrown away after initial multiply
#define m rdx

#define a rax
#define c rcx

#define d0 rsi
#define d1 r8
#define d2 r9
#define d3 r10
#define d4 r11
#define d5 r12
// Multiplier again for second stage
#define q rdx

#define ashort eax
#define cshort ecx
#define qshort edx


S2N_BN_SYMBOL(bignum_cmul_p384):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// We seem to need (just!) one extra register, which we need to save and restore

        CFI_PUSH(r12)

// Shuffle inputs (since we want multiplier in rdx)

        mov     x, rdx
        mov     m, rsi

// Multiply, accumulating the result as 2^384 * h + [d5;d4;d3;d2;d1;d0]
// but actually immediately producing q = h + 1, our quotient approximation,
// by adding 1 to it. Note that by hypothesis x is reduced mod p_384, so our
// product is <= (2^64 - 1) * (p_384 - 1) and hence  h <= 2^64 - 2, meaning
// there is no danger this addition of 1 could wrap.

        mulx    d1, d0, [x]
        mulx    d2, a, [x+8]
        add     d1, a
        mulx    d3,a, [x+16]
        adc     d2, a
        mulx    d4,a, [x+24]
        adc     d3, a
        mulx    d5,a, [x+32]
        adc     d4, a
        mulx    q,a, [x+40]
        adc     d5, a
        adc     q, 1

// It's easy to see -p_384 <= z - q * p_384 < p_384, so we just need to
// subtract q * p_384 and then correct if that is negative by adding p_384.
//
// Write p_384 = 2^384 - r where r = 2^128 + 2^96 - 2^32 + 1
//
// We want z - q * (2^384 - r)
//       = (2^384 * h + l) - q * (2^384 - r)
//       = 2^384 * (h - q) + (l + q * r)
//       = 2^384 * (-1) + (l + q * r)

        xor     c, c
        mov     a, 0xffffffff00000001
        mulx    c, a, a
        adcx    d0, a
        adox    d1, c
        mov     ashort, 0x00000000ffffffff
        mulx    c, a, a
        adcx    d1, a
        adox    d2, c
        adcx    d2, q
        mov     ashort, 0
        mov     cshort, 0
        adox    a, a
        adc     d3, a
        adc     d4, c
        adc     d5, c
        adc     c, c
        sub     c, 1

// The net c value is now the top word of the 7-word answer, hence will
// be -1 if we need a corrective addition, 0 otherwise, usable as a mask.
// Now use that mask for a masked addition of p_384, which again is in
// fact done by a masked subtraction of 2^384 - p_384, so that we only
// have three nonzero digits and so can avoid using another register.

        mov     qshort, 0x00000000ffffffff
        xor     a, a
        and     q, c
        sub     a, q
        and     c, 1

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

        CFI_POP(r12)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_cmul_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
