// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Optionally negate modulo m, z := (-x) mod m (if p nonzero) or z := x
// (if p zero), assuming x reduced
// Inputs p, x[k], m[k]; output z[k]
//
//    extern void bignum_modoptneg(uint64_t k, uint64_t *z, uint64_t p,
//                                 const uint64_t *x, const uint64_t *m);
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = p, RCX = x, R8 = m
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = p, R9 = x, [RSP+40] = m
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_modoptneg)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_modoptneg)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_modoptneg)
        .text
        .balign 32

#define k rdi
#define z rsi
#define p rdx
#define x rcx
#define m r8

#define a r9
#define c rax
#define b r10
#define i r11

S2N_BN_SYMBOL(bignum_modoptneg):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        mov     r8, [rsp+56]
#endif

// Do nothing if k = 0

        test    k, k
        jz      Lbignum_modoptneg_end

// Make an additional check for zero input, and force p to zero in this case.
// This can be skipped if the input is known not to be zero a priori.

        xor     i, i
        xor     a, a
Lbignum_modoptneg_cmploop:
        or      a, [x+8*i]
        inc     i
        cmp     i, k
        jc      Lbignum_modoptneg_cmploop

        cmp     a, 0
        cmovz   p, a

// Turn the input p into a strict bitmask

        neg     p
        sbb     p, p

// Main loop

        xor     i, i
        mov     c, p
Lbignum_modoptneg_mainloop:
        mov     a, [m+8*i]
        and     a, p
        mov     b, [x+8*i]
        xor     b, p
        neg     c
        adc     a, b
        sbb     c, c
        mov     [z+8*i], a
        inc     i
        cmp     i, k
        jc      Lbignum_modoptneg_mainloop

Lbignum_modoptneg_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_modoptneg)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
