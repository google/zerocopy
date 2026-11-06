// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert from (almost-)Montgomery form z := (x / 2^{64k}) mod m
// Inputs x[k], m[k]; output z[k]
//
//    extern void bignum_demont(uint64_t k, uint64_t *z, const uint64_t *x,
//                              const uint64_t *m);
//
// Does z := (x / 2^{64k}) mod m, hence mapping out of Montgomery domain.
// In other words, this is a k-fold Montgomery reduction with same-size input.
// This can handle almost-Montgomery inputs, i.e. any k-digit bignum.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = m
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = x, R9 = m
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_demont)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_demont)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_demont)
        .text
        .balign 32

#define k rdi
#define z rsi
#define x rdx
#define m rcx

// General temp, low part of product and mul input
#define a rax
// General temp, high part of product (no longer x)
#define b rdx
// Negated modular inverse
#define w r8
// Outer loop counter
#define i r9
// Inner loop counter
#define j rbx
// Home for Montgomery multiplier
#define d rbp
#define h r10
#define e r11
#define n r12

// A temp reg in the initial word-level negmodinv, same as j

#define t rbx

#define ashort eax
#define jshort ebx


S2N_BN_SYMBOL(bignum_demont):
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

// Save registers

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)

// If k = 0 the whole operation is trivial

        test    k, k
        jz      Lbignum_demont_end

// Compute word-level negated modular inverse w for m == m[0].

        mov     a, [m]

        mov     t, a
        mov     w, a
        shl     t, 2
        sub     w, t
        xor     w, 2

        mov     t, w
        imul    t, a
        mov     ashort, 2
        add     a, t
        add     t, 1

        imul    w, a

        imul    t, t
        mov     ashort, 1
        add     a, t
        imul    w, a

        imul    t, t
        mov     ashort, 1
        add     a, t
        imul    w, a

        imul    t, t
        mov     ashort, 1
        add     a, t
        imul    w, a

// Initially just copy the input to the output. It would be a little more
// efficient but somewhat fiddlier to tweak the zeroth iteration below instead.
// After this we never use x again and can safely recycle RDX for muls

        xor     j, j
Lbignum_demont_iloop:
        mov     a, [x+8*j]
        mov     [z+8*j], a
        inc     j
        cmp     j, k
        jc      Lbignum_demont_iloop

// Outer loop, just doing a standard Montgomery reduction on z

        xor     i, i

Lbignum_demont_outerloop:
        mov     e, [z]
        mov     d, w
        imul    d, e
        mov     a, [m]
        mul     d
        add     a, e            // Will be zero but want the carry
        mov     h, rdx
        mov     jshort, 1
        mov     n, k
        dec     n
        jz      Lbignum_demont_montend

Lbignum_demont_montloop:
        adc     h, [z+8*j]
        sbb     e, e
        mov     a, [m+8*j]
        mul     d
        sub     rdx, e
        add     a, h
        mov     [z+8*j-8], a
        mov     h, rdx
        inc     j
        dec     n
        jnz     Lbignum_demont_montloop

Lbignum_demont_montend:
        adc     h, 0
        mov     [z+8*j-8], h

// End of outer loop.

        inc     i
        cmp     i, k
        jc      Lbignum_demont_outerloop

// Now do a comparison of z with m to set a final correction mask
// indicating that z >= m and so we need to subtract m.

        xor     j, j
        mov     n, k
Lbignum_demont_cmploop:
        mov     a, [z+8*j]
        sbb     a, [m+8*j]
        inc     j
        dec     n
        jnz     Lbignum_demont_cmploop
        sbb     d, d
        not     d

// Now do a masked subtraction of m for the final reduced result.

        xor     e, e
        xor     j, j
Lbignum_demont_corrloop:
        mov     a, [m+8*j]
        and     a, d
        neg     e
        sbb     [z+8*j], a
        sbb     e, e
        inc     j
        cmp     j, k
        jc      Lbignum_demont_corrloop

Lbignum_demont_end:
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_demont)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
