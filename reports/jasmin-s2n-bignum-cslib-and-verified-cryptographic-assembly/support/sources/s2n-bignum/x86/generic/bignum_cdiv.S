// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Divide by a single (nonzero) word, z := x / m and return x mod m
// Inputs x[n], m; outputs function return (remainder) and z[k]
//
//    extern uint64_t bignum_cdiv(uint64_t k, uint64_t *z, uint64_t n,
//                                const uint64_t *x, uint64_t m);
//
// Does the "z := x / m" operation where x is n digits, result z is k.
// Truncates the quotient in general, but always (for nonzero m) returns
// the true remainder x mod m.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x, R8 = m
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n, R9 = x, [RSP+40] = m
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cdiv)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cdiv)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cdiv)
        .text
        .balign 32

#define k rdi
#define z rsi
#define m r8

// These parameters get moved because of special uses for rcx, rdx

#define n r9
#define x r10

// This needs to be in rcx for variable shifts with cl

#define e rcx

// Other variables

#define w r11
#define d r12
#define i rbx
#define c r13
#define l r14

#define a rax
#define h rdx

#define ashort eax
#define ishort ebx
#define hshort edx

// The remainder

#define r r15

S2N_BN_SYMBOL(bignum_cdiv):
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

        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Move parameters that need a new home

        mov     n, rdx
        mov     x, rcx

// First do a modulus computation, slightly tweaked from bignum_cmod,
// changing variables and avoiding modification of the size parameter.
// Initialize l = 0 now for convenience (we eventually need to do it).
// If the bignum is zero-length, l is already the right answer of 0

        xor     l, l
        test    n, n
        jz      Lbignum_cdiv_nomodulus

        bsr     e, m
        xor     e, 63
        shl     m, cl

        mov    r, m
        mov    w, 0x1FFFFFFFFFFFF
        shr    r, 16
        xor    w, r
        inc    r
        shr    w, 32
        mov    h, r
        imul   h, w
        neg    h
        mov    a, h
        shr    a, 49
        imul   a, a
        shr    h, 34
        add    h, a
        or     a, 0x40000000
        imul   a, h
        shr    a, 30
        imul   a, w
        shl    w, 30
        add    w, a
        shr    w, 30
        mov    h, r
        imul   h, w
        neg    h
        shr    h, 24
        imul   h, w
        shl    w, 16
        shr    h, 24
        add    w, h
        mov    h, r
        imul   h, w
        neg    h
        shr    h, 32
        imul   h, w
        shl    w, 31
        shr    h, 17
        add    w, h
        mov    a, m
        mul    w
        shrd   a, h, 60
        mov    h, w
        shr    h, 33
        not    a
        imul   a, h
        shl    w, 1
        shr    a, 33
        add    w, a
        add    w, 1
        mov    a, m
        sbb    w, 0
        mul    w
        add    h, m
        sbb    w, 0

        mov     r, m
        imul    r, w
        neg     r

        xor     hshort, hshort
        mov     i, n
Lbignum_cdiv_modloop:
        mov     a, h
        mul     r
        add     a, [x+8*i-8]
        adc     h, l
        mov     l, a
        sbb     a, a
        and     a, r
        add     l, a
        adc     h, 0
        dec     i
        jnz     Lbignum_cdiv_modloop

        mov     i, h
        mov     a, w
        mul     h
        add     h, i
        sbb     r, r
        and     r, m

        mov     a, h
        mul     m
        add     h, r
        xor     r, r
        sub     l, a
        sbb     i, h

        cmovnz  r, m
        xor     ashort, ashort
        sub     l, r
        sbb     i, a

        cmovnz  a, m
        sub     l, a

        mov     a, w
        mul     l
        add     h, l
        rcr     h, 1

        shr     m, cl
        xor     e, 63
        shr     h, cl

        imul    h, m
        sub     l, h

        mov     r, l
        sub     l, m
Lbignum_cdiv_nomodulus:
        cmovnc  r, l

// If k = 0 then there's no more to be done

        test    k, k
        jz      Lbignum_cdiv_end

// Let e be the number of trailing zeros in m (we can ignore m = 0)

        bsf     e, m

// Now just shift m right by e bits. So hereafter we can assume m is odd
// but we first need to shift the input right by e bits then divide by m.

        shr    m, cl

// Compute the negated modular inverse w with w * m + 1 == 0 (mod 2^64)
// This is essentially the same as word_negmodinv.

        mov     a, m
        mov     w, m
        shl     a, 2
        sub     w, a
        xor     w, 2
        mov     a, w
        imul    a, m
        mov     hshort, 2
        add     h, a
        add     a, 1
        imul    w, h
        imul    a, a
        mov     hshort, 1
        add     h, a
        imul    w, h
        imul    a, a
        mov     hshort, 1
        add     h, a
        imul    w, h
        imul    a, a
        mov     hshort, 1
        add     h, a
        imul    w, h

// We have the remainder r, so now x = m * y + r for some quotient y
// to be computed. Consider x' = x + (m - r) = m * (y + 1) and do a
// Montgomery reduction, keeping the cofactor z. This gives us
// x' + m * z = 2^{64k} * c where c <= m. Thus since x' = m * (y + 1)
// we have
//
//     m * (y + z + 1) = 2^{64k} * c
//
// This means m * (y + z + 1) == 0 (mod 2^{64k}), even when we truncate
// x to k digits (if in fact k < n). Since m is odd, it's coprime to
// 2^{64k} so we can cancel and get y + z + 1 == 0 (mod 2^{64k}), and
// hence using logical complement y == ~z (mod 2^{64k}). Thus we can
// write back the logical complements of the cofactor as the answer.
// Start with carry word c = m - r/2^e to make the initial tweak
// x' = x + (m - r); since we've shifted everything initially by e
// we need to shift the remainder too before subtracting from the
// shifted m.

        mov     d, r
        shr     d, cl
        mov     c, m
        sub     c, d
        xor     ishort, ishort

// Unless n = 0, preload the zeroth digit and bump up the x pointer by
// 8 and n down by 1, to ease indexing and comparison using the same
// variable i in the main loop. When n = 0 we leave it alone, as the
// comparison i < n will always fail and the x pointer is unused.

        xor     d, d
        test    n, n
        jz      Lbignum_cdiv_loop
        mov     d, [x]
        add     x, 8
        dec     n

Lbignum_cdiv_loop:

// Load the next digit up to get [l,d] then shift right e places

        xor     l, l
        cmp     i, n
        jnc     Lbignum_cdiv_noload
        mov     l, [x+8*i]
Lbignum_cdiv_noload:
        shrd    d, l, cl
        add     d, c
        sbb     c, c
        neg     c

// Now the effective sum is [c,a] where the carry-in has been absorbed.
// Do the main Montgomery step with the (odd) m, writing back ~q. Finally
// set d to the next digit ready for the following iteration.

        mov     a, w
        imul    a, d
        not     a
        mov     [z+8*i], a
        not     a

        mul     m
        add     a, d
        adc     c, h

        mov     d, l

        inc     i
        cmp     i, k
        jc      Lbignum_cdiv_loop

// Return the modulus

Lbignum_cdiv_end:
        mov     rax, r

        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_cdiv)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
