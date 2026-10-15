// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert to Montgomery form z := (2^256 * x) mod p_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_tomont_p256k1_alt(uint64_t z[static 4],
//                                         const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_p256k1_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tomont_p256k1_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_p256k1_alt)
        .text

#define z rdi
#define x rsi

#define c rcx
#define d rdx
#define h rdx

#define a rax
#define ashort eax
#define q rax

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 rsi

S2N_BN_SYMBOL(bignum_tomont_p256k1_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Since 2^256 == 4294968273 (mod p_256k1) we more or less just set
// m = 4294968273 then devolve to a variant of bignum_cmul_p256k1;
// the logic that q = h + 1 < 2^64 and hence doesn't wrap still holds
// since the multiplier 4294968273 is known to be much less than 2^64.
// We keep this constant in rcx throughout as it's used repeatedly.

        mov     c, 4294968273

// Multiply, accumulating the result as 2^256 * h + [d3;d2;d1;d0]

        mov     a, [x]
        mul     c
        mov     d0, a
        mov     d1, d

        mov     a, [x+8]
        xor     d2, d2
        mul     c
        add     d1, a
        adc     d2, d

        mov     a, [x+16]
        mul     c
        add     d2, a
        adc     d, 0

        mov     a, [x+24]
        mov     d3, d
        mul     c
        add     d3, a
        adc     h, 0

// Now the quotient estimate is q = h + 1, and then we do the reduction,
// writing z = [d3;d2;d1;d0], as z' = (2^256 * h + z) - q * p_256k1 =
// (2^256 * h + z) - q * (2^256 - 4294968273) = -2^256 + (z + 4294968273 * q)

        lea     q, [h+1]
        mul     c

        add     d0, rax
        adc     d1, rdx
        adc     d2, 0
        adc     d3, 0

// Because of the implicit -2^256, CF means >= 0 so z' is the answer; ~CF
// means z' < 0 so we add p_256k1, which in 4 digits means subtracting c.

        mov     a, 0
        cmovc   c, a

        sub     d0, c
        mov     [z], d0
        sbb     d1, a
        mov     [z+8], d1
        sbb     d2, a
        mov     [z+16],d2
        sbb     d3, a
        mov     [z+24],d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_tomont_p256k1_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
