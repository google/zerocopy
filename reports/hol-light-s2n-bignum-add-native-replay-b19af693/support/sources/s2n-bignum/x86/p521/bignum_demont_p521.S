// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert from Montgomery form z := (x / 2^576) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_demont_p521(uint64_t z[static 9],
//                                   const uint64_t x[static 9]);
//
// This assumes the input is < p_521 for correctness. If this is not the case,
// use the variant "bignum_deamont_p521" instead.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_demont_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_demont_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_demont_p521)
        .text

#define z rdi
#define x rsi

// Rotating (aliased) registers for the digits

#define c rax
#define d0 rdx
#define d1 rcx

#define d2 rdx
#define d3 rcx
#define d4 rdx
#define d5 rcx
#define d6 rdx
#define d7 rcx
#define d8 rdx

S2N_BN_SYMBOL(bignum_demont_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Rotate, as a 521-bit quantity, by 9*64 - 521 = 55 bits right.

        mov     d0, [x]
        mov     c, d0
        mov     d1, [x+8]
        shrd    d0, d1, 55
        mov     [z], d0
        mov     d2, [x+16]
        shrd    d1, d2, 55
        mov     [z+8],  d1
        mov     d3, [x+24]
        shrd    d2, d3, 55
        shl     c, 9
        mov     [z+16], d2
        mov     d4, [x+32]
        shrd    d3, d4, 55
        mov     [z+24], d3
        mov     d5, [x+40]
        shrd    d4, d5, 55
        mov     [z+32], d4
        mov     d6, [x+48]
        shrd    d5, d6, 55
        mov     [z+40], d5
        mov     d7, [x+56]
        shrd    d6, d7, 55
        mov     [z+48], d6
        mov     d8, [x+64]
        or      d8, c
        shrd    d7, d8, 55
        mov     [z+56], d7
        shr     d8, 55
        mov     [z+64], d8
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_demont_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
