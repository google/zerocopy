// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert to Montgomery form z := (2^256 * x) mod p_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_tomont_p256k1(uint64_t z[static 4],
//                                     const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_p256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tomont_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_p256k1)
        .text

#define z rdi
#define x rsi

#define d rdx

#define a rax
#define ashort eax
#define q rax

#define d0 rcx
#define d1 r8
#define d2 r9
#define d3 r10

// Re-use the x argument later on when it's no longer needed

#define h rsi
#define c rsi

S2N_BN_SYMBOL(bignum_tomont_p256k1):
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
// We keep this constant in rdx throughout as it's used repeatedly.

        mov     d, 4294968273

// Multiply, accumulating the result as 2^256 * h + [d3;d2;d1;d0]
// But immediately add 1 to h to get q = h + 1 as the quotient estimate.

        mulx    d1, d0, [x]
        mulx    d2, a, [x+8]
        add     d1, a
        mulx    d3, a, [x+16]
        adc     d2, a
        mulx    h, a, [x+24]
        adc     d3, a
        adc     h, 1

// Now the quotient estimate is q = h + 1, and then we do the reduction,
// writing z = [d3;d2;d1;d0], as z' = (2^256 * h + z) - q * p_256k1 =
// (2^256 * h + z) - q * (2^256 - 4294968273) = -2^256 + (z + 4294968273 * q)

        mulx    c, a, h

        add     d0, a
        adc     d1, c
        adc     d2, 0
        adc     d3, 0

// Because of the implicit -2^256, CF means >= 0 so z' is the answer; ~CF
// means z' < 0 so we add p_256k1, which in 4 digits means subtracting c.

        mov     a, 0
        cmovc   d, a

        sub     d0, d
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

S2N_BN_SIZE_DIRECTIVE(bignum_tomont_p256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
