// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Divide by a single word, z := x / m *when known to be exact*
// Inputs x[n], m; output z[k]
//
//    extern void bignum_cdiv_exact(uint64_t k, uint64_t *z, uint64_t n,
//                                  const uint64_t *x, uint64_t m);
//
// Does the "z := x / m" operation where x is n digits and result z is k,
// *assuming* that m is nonzero and that the input x is in fact an
// exact multiple of m. (If this isn't known, use the general bignum_cdiv
// function instead.) In general the result is truncated to k digits.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x, R8 = m
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n, R9 = x, [RSP+40] = m
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cdiv_exact)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cdiv_exact)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cdiv_exact)
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
#define t r14

#define a rax
#define h rdx

#define ishort ebx
#define hshort edx

S2N_BN_SYMBOL(bignum_cdiv_exact):
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

// If k = 0 then there's nothing to be done

        test    k, k
        jz      Lbignum_cdiv_exact_end

// Move parameters that need a new home

        mov     n, rdx
        mov     x, rcx

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

// Consider x' = x + m and do a Montgomery reduction, keeping the cofactor z.
// This gives us x' + m * z = 2^{64k} * c where c <= m. Assuming x = m * y
// we then have m * y + m + m * z = 2^{64k} * c, i.e.
//
//     m * (y + z + 1) = 2^{64k} * c
//
// This means m * (y + z + 1) == 0 (mod 2^{64k}), even when we truncate
// x to k digits (if in fact k < n). Since m is odd, it's coprime to
// 2^{64k} so we can cancel and get y + z + 1 == 0 (mod 2^{64k}), and
// hence using logical complement y == ~z (mod 2^{64k}). Thus we can
// write back the logical complements of the cofactor as the answer.
// Start with carry word c = m to make the initial tweak x' = x + m.

        mov     c, m
        xor     ishort, ishort

// Unless n = 0, preload the zeroth digit and bump up the x pointer by
// 8 and n down by 1, to ease indexing and comparison using the same
// variable i in the main loop. When n = 0 we leave it alone, as the
// comparison i < n will always fail and the x pointer is unused.

        xor     d, d
        test    n, n
        jz      Lbignum_cdiv_exact_loop
        mov     d, [x]
        add     x, 8
        dec     n

Lbignum_cdiv_exact_loop:

// Load the next digit up to get [t,d] then shift right e places

        xor     t, t
        cmp     i, n
        jnc     Lbignum_cdiv_exact_noload
        mov     t, [x+8*i]
Lbignum_cdiv_exact_noload:
        shrd    d, t, cl
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

        mov     d, t

        inc     i
        cmp     i, k
        jc      Lbignum_cdiv_exact_loop

Lbignum_cdiv_exact_end:
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_cdiv_exact)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
