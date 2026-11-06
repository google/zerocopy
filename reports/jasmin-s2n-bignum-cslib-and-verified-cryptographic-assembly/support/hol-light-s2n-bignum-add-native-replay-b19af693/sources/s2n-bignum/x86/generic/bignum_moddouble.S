// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Double modulo m, z := (2 * x) mod m, assuming x reduced
// Inputs x[k], m[k]; output z[k]
//
//    extern void bignum_moddouble(uint64_t k, uint64_t *z, const uint64_t *x,
//                                 const uint64_t *m);
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = m
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = x, R9 = m
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_moddouble)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_moddouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_moddouble)
        .text
        .balign 32

#define k rdi
#define z rsi
#define x rdx
#define m rcx
#define i r8
#define a r9
#define c rax
#define b r10

S2N_BN_SYMBOL(bignum_moddouble):
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

// If k = 0 do nothing

        test    k, k
        jz      Lbignum_moddouble_end

// Do (_::z) = 2 * x - m and generate a mask in c for 2 * x < m

        xor     c, c
        xor     i, i
        xor     b, b

Lbignum_moddouble_dubloop:
        mov     a, [x+8*i]
        shrd    c, a, 63
        neg     b
        sbb     c, [m+8*i]
        sbb     b, b
        mov     [z+8*i],c
        mov     c, a
        inc     i
        cmp     i, k
        jc      Lbignum_moddouble_dubloop
        shr     c, 63

        add     c, b

// Now do a corrective masked addition z := z + [c] * m

        xor     i, i
        xor     b, b
Lbignum_moddouble_corrloop:
        mov     a, [m+8*i]
        and     a, c
        neg     b
        adc     a, [z+8*i]
        sbb     b, b
        mov     [z+8*i], a
        inc     i
        cmp     i, k
        jc      Lbignum_moddouble_corrloop

Lbignum_moddouble_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_moddouble)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
