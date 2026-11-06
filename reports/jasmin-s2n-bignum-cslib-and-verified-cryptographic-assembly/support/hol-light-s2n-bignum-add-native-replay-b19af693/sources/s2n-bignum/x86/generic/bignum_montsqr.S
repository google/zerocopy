// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery square, z := (x^2 / 2^{64k}) mod m
// Inputs x[k], m[k]; output z[k]
//
//    extern void bignum_montsqr(uint64_t k, uint64_t *z, const uint64_t *x,
//                               const uint64_t *m);
//
// Does z := (x^2 / 2^{64k}) mod m, assuming x^2 <= 2^{64k} * m, which is
// guaranteed in particular if x < m initially (the "intended" case).
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = m
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = x, R9 = m
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montsqr)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montsqr)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montsqr)
        .text
        .balign 32

// We copy x into r9 but it comes in in rdx originally

#define k rdi
#define z rsi
#define x r9
#define m rcx

// General temp, low part of product and mul input
#define a rax
// General temp, High part of product
#define b rdx
// Negated modular inverse
#define w r8
// Inner loop counter
#define j rbx
// Home for i'th digit or Montgomery multiplier
#define d rbp
#define h r10
#define e r11
#define n r12
#define i r13
#define c0 r14
#define c1 r15

// A temp reg in the initial word-level negmodinv.

#define t2 rdx

#define ashort eax
#define jshort ebx


S2N_BN_SYMBOL(bignum_montsqr):
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
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// If k = 0 the whole operation is trivial

        test    k, k
        jz      Lbignum_montsqr_end

// Move x input into its permanent home, since we need rdx for multiplications

        mov     x, rdx

// Compute word-level negated modular inverse w for m == m[0].

        mov     a, [m]

        mov     t2, a
        mov     w, a
        shl     t2, 2
        sub     w, t2
        xor     w, 2

        mov     t2, w
        imul    t2, a
        mov     ashort, 2
        add     a, t2
        add     t2, 1

        imul    w, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    w, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    w, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    w, a

// Initialize the output c0::z to zero so we can then consistently add rows.
// It would be a bit more efficient to special-case the zeroth row, but
// this keeps the code slightly simpler.

        xor     i, i            // Also initializes i for main loop
        xor     j, j
Lbignum_montsqr_zoop:
        mov     [z+8*j], i
        inc     j
        cmp     j, k
        jc      Lbignum_montsqr_zoop

        xor     c0, c0

// Outer loop pulling down digits d=x[i], multiplying by x and reducing

Lbignum_montsqr_outerloop:

// Multiply-add loop where we always have CF + previous high part h to add in.
// Note that in general we do need yet one more carry in this phase and hence
// initialize c1 with the top carry.

        mov     d, [x+8*i]
        xor     j, j
        xor     h, h
        xor     c1, c1
        mov     n, k

Lbignum_montsqr_maddloop:
        adc     h, [z+8*j]
        sbb     e, e
        mov     a, [x+8*j]
        mul     d
        sub     rdx, e
        add     a, h
        mov     [z+8*j], a
        mov     h, rdx
        inc     j
        dec     n
        jnz     Lbignum_montsqr_maddloop
        adc     c0, h
        adc     c1, c1

// Montgomery reduction loop, similar but offsetting writebacks

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
        jz      Lbignum_montsqr_montend

Lbignum_montsqr_montloop:
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
        jnz     Lbignum_montsqr_montloop

Lbignum_montsqr_montend:
        adc     h, c0
        adc     c1, 0
        mov     c0, c1
        mov     [z+8*j-8], h

// End of outer loop.

        inc     i
        cmp     i, k
        jc      Lbignum_montsqr_outerloop

// Now do a comparison of (c0::z) with (0::m) to set a final correction mask
// indicating that (c0::z) >= m and so we need to subtract m.

        xor     j, j
        mov     n, k
Lbignum_montsqr_cmploop:
        mov     a, [z+8*j]
        sbb     a, [m+8*j]
        inc     j
        dec     n
        jnz     Lbignum_montsqr_cmploop

        sbb     c0, 0
        sbb     d, d
        not     d

// Now do a masked subtraction of m for the final reduced result.

        xor     e, e
        xor     j, j
Lbignum_montsqr_corrloop:
        mov     a, [m+8*j]
        and     a, d
        neg     e
        sbb     [z+8*j], a
        sbb     e, e
        inc     j
        cmp     j, k
        jc      Lbignum_montsqr_corrloop

Lbignum_montsqr_end:
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_montsqr)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
