// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Optionally negate, z := -x (if p nonzero) or z := x (if p zero)
// Inputs p, x[k]; outputs function return (nonzero input) and z[k]
//
//    extern uint64_t bignum_optneg(uint64_t k, uint64_t *z, uint64_t p,
//                                  const uint64_t *x);
//
// It is assumed that both numbers x and z have the same size k digits.
// Returns a carry, which is equivalent to "x is nonzero".
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = p, RCX = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = p, R9 = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optneg)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_optneg)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optneg)
        .text
        .balign 32

#define k rdi
#define z rsi
#define p rdx
#define x rcx

#define c rax
#define a r8
#define i r9

#define cshort eax

S2N_BN_SYMBOL(bignum_optneg):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// If k = 0 do nothing, but need to set zero return for the carry (c = rax)

        xor     c, c
        test    k, k
        jz      Lbignum_optneg_end

// Convert p into a strict bitmask and set initial carry-in in c

        neg     p
        sbb     p, p
        sub     c, p

// Main loop

        xor     i, i
Lbignum_optneg_loop:

        mov     a, [x+8*i]
        xor     a, p
        add     a, c
        mov     cshort, 0
        mov     [z+8*i], a
        adc     c, 0
        inc     i
        cmp     i, k
        jc      Lbignum_optneg_loop

// Return carry flag, fixing up inversion for negative case

        xor     rax, p
        and     rax, 1

Lbignum_optneg_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_optneg)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
