// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert to Montgomery form z := (2^576 * x) mod p_521
// Input x[9]; output z[9]
//
//    extern void bignum_tomont_p521(uint64_t z[static 9],
//                                   const uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tomont_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_p521)
        .text

#define z rdi
#define x rsi

#define d0 rax
#define d1 rcx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11
#define d6 rbx

#define d8 rdx

#define d8short edx

// Re-use the input pointer as other variable once safe to do so

#define d7 rsi

S2N_BN_SYMBOL(bignum_tomont_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save one more register

        CFI_PUSH(rbx)

// Separate out the input into x = 2^521 * H + L, so that x mod p_521 =
// (H + L) mod p_521 = if H + L >= p_521 then H + L - p_521 else H + L.

        mov     d0, [x+64]
        mov     d8short, 0x1FF
        and     d8, d0
        shr     d0, 9

// Force carry-in to get s = [d8;d7;d6;d5;d4;d3;d2;d1;d0] = H + L + 1.

        stc
        adc     d0, [x]
        mov     d1, [x+8]
        adc     d1, 0
        mov     d2, [x+16]
        adc     d2, 0
        mov     d3, [x+24]
        adc     d3, 0
        mov     d4, [x+32]
        adc     d4, 0
        mov     d5, [x+40]
        adc     d5, 0
        mov     d6, [x+48]
        adc     d6, 0
        mov     d7, [x+56]
        adc     d7, 0
        adc     d8, 0

// Set CF <=> s < 2^521 <=> H + L < p_521, so that if CF is set
// we want H + L = s - 1, otherwise (H + L) - p_521 = s - 2^521.
// This is done with just s - CF then masking to 521 bits.

        cmp     d8, 512

        sbb     d0, 0
        sbb     d1, 0
        sbb     d2, 0
        sbb     d3, 0
        sbb     d4, 0
        sbb     d5, 0
        sbb     d6, 0
        sbb     d7, 0
        sbb     d8, 0

// So far, this is just a modular reduction as in bignum_mod_p521_9,
// except that the final masking of d8 is skipped since that comes out
// in the wash anyway from the next block, which is the Montgomery map,
// multiplying by 2^576 modulo p_521. Because 2^521 == 1 (mod p_521)
// this is just rotation left by 576 - 521 = 55 bits. Store back
// digits as created, though in a slightly peculiar order because we
// want to avoid using another register.

        shld    d8, d7, 55
        shld    d7, d6, 55
        mov     [z+56], d7
        shld    d6, d5, 55
        mov     [z+48], d6
        shld    d5, d4, 55
        mov     [z+40], d5
        shld    d4, d3, 55
        mov     [z+32], d4
        shld    d3, d2, 55
        mov     [z+24], d3
        shld    d2, d1, 55
        mov     [z+16], d2
        shld    d1, d0, 55
        mov     [z+8],  d1
        shld    d0, d8, 55
        mov     [z], d0
        and     d8, 0x1FF
        mov     [z+64], d8

// Restore register

        CFI_POP(rbx)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_tomont_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
