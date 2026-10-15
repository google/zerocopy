// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Double modulo p_521, z := (2 * x) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_double_p521(uint64_t z[static 9],
//                                   const uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_double_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_double_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_double_p521)
        .text

#define z rdi
#define x rsi

#define a rax
#define c rcx



S2N_BN_SYMBOL(bignum_double_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// We can decide whether 2 * x >= p_521 just by 2 * x >= 2^521, which
// as we assume x < p_521 amounts to looking at bit 8 of the top word

        mov     c, [x+64]
        bt      c, 8

// Now if 2 * x >= p_521 we want 2 * x - p_521 = (2 * x + 1) - 2^521
// and otherwise just 2 * x. Feed in the condition as the carry bit
// to get 2 * x + [2 * x >= p_521] then just mask it off to 521 bits.

        mov     a, [x]
        adc     a, a
        mov     [z], a

        mov     a, [x+8]
        adc     a, a
        mov     [z+8], a

        mov     a, [x+16]
        adc     a, a
        mov     [z+16], a

        mov     a, [x+24]
        adc     a, a
        mov     [z+24], a

        mov     a, [x+32]
        adc     a, a
        mov     [z+32], a

        mov     a, [x+40]
        adc     a, a
        mov     [z+40], a

        mov     a, [x+48]
        adc     a, a
        mov     [z+48], a

        mov     a, [x+56]
        adc     a, a
        mov     [z+56], a

        adc     c, c
        and     c, 0x1FF
        mov     [z+64], c

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_double_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
