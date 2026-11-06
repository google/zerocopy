// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery reduce, z := (x' / 2^{64p}) MOD m
// Inputs x[n], m[k], p; output z[k]
//
//    extern void bignum_montredc(uint64_t k, uint64_t *z, uint64_t n,
//                                const uint64_t *x, const uint64_t *m, uint64_t p);
//
// Does a := (x' / 2^{64p}) mod m where x' = x if n <= p + k and in general
// is the lowest (p+k) digits of x, assuming x' <= 2^{64p} * m. That is,
// p-fold Montgomery reduction w.r.t. a k-digit modulus m giving a k-digit
// answer.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x, R8 = m, R9 = p
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n, R9 = x, [RSP+40] = m, [RSP+48] = p
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montredc)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montredc)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montredc)
        .text
        .balign 32

 // We copy n into r10 but it comes in in rdx originally

#define k rdi
#define z rsi
#define n r10
#define x rcx
#define m r8
#define p r9

// General temp, low part of product and mul input
#define a rax
// General temp, High part of product
#define b rdx
// Negated modular inverse
#define w QWORD PTR [rsp]
// Inner loop counter
#define j rbx
// Home for i'th digit or Montgomery multiplier
#define d rbp
#define h r11
#define e r12
#define t r13
#define i r14
#define c r15

// Some more intuitive names for temp regs in initial word-level negmodinv.

#define t1 rbx
#define t2 r14

#define ashort eax
#define cshort r15d
#define jshort ebx


S2N_BN_SYMBOL(bignum_montredc):
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
        mov     r9, [rsp+64]
#endif

// Save registers and allocate space on stack for non-register variable w

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(8)

// If k = 0 the whole operation is trivial

        test    k, k
        jz      Lbignum_montredc_end

// Move n input into its permanent home, since we need rdx for multiplications

        mov     n, rdx

// Compute word-level negated modular inverse w for m == m[0].

        mov     a, [m]

        mov     t2, a
        mov     t1, a
        shl     t2, 2
        sub     t1, t2
        xor     t1, 2

        mov     t2, t1
        imul    t2, a
        mov     ashort, 2
        add     a, t2
        add     t2, 1

        imul    t1, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    t1, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    t1, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    t1, a

        mov     w, t1

// Initialize z to the lowest k digits of the input, zero-padding if n < k.

        mov     j, k
        cmp     n, k
        cmovc   j, n
        xor     i, i
        test    j, j
        jz      Lbignum_montredc_padloop
Lbignum_montredc_copyloop:
        mov     a, [x+8*i]
        mov     [z+8*i], a
        inc     i
        cmp     i, j
        jc      Lbignum_montredc_copyloop

        cmp     i, k
        jnc     Lbignum_montredc_initialized

        xor     j, j
Lbignum_montredc_padloop:
        mov     [z+8*i], j
        inc     i
        cmp     i, k
        jc      Lbignum_montredc_padloop

Lbignum_montredc_initialized:
        xor     c, c

// Now if p = 0 we just need the corrective tail, and even that is
// only needed for the case when the input is exactly the modulus,
// to maintain the <= 2^64p * n precondition

        test    p, p
        jz      Lbignum_montredc_corrective

// Outer loop, just doing a standard Montgomery reduction on z

        xor     i, i
Lbignum_montredc_outerloop:
        mov     e, [z]
        mov     d, w
        imul    d, e
        mov     a, [m]
        mul     d
        add     a, e            // Will be zero but want the carry
        mov     h, rdx
        mov     jshort, 1
        mov     t, k
        dec     t
        jz      Lbignum_montredc_montend

Lbignum_montredc_montloop:
        adc     h, [z+8*j]
        sbb     e, e
        mov     a, [m+8*j]
        mul     d
        sub     rdx, e
        add     a, h
        mov     [z+8*j-8], a
        mov     h, rdx
        inc     j
        dec     t
        jnz     Lbignum_montredc_montloop

Lbignum_montredc_montend:
        adc     h, c
        mov     cshort, 0
        adc     c, 0

        add     j, i
        cmp     j, n
        jnc     Lbignum_montredc_offtheend
        mov     a, [x+8*j]
        add     h, a
        adc     c, 0
Lbignum_montredc_offtheend:
        mov     [z+8*k-8], h

// End of outer loop.

        inc     i
        cmp     i, p
        jc      Lbignum_montredc_outerloop

// Now do a comparison of (c::z) with (0::m) to set a final correction mask
// indicating that (c::z) >= m and so we need to subtract m.

Lbignum_montredc_corrective:

        xor     j, j
        mov     n, k
Lbignum_montredc_cmploop:
        mov     a, [z+8*j]
        sbb     a, [m+8*j]
        inc     j
        dec     n
        jnz     Lbignum_montredc_cmploop

        sbb     c, 0
        sbb     d, d
        not     d

// Now do a masked subtraction of m for the final reduced result.

        xor     e, e
        xor     j, j
Lbignum_montredc_corrloop:
        mov     a, [m+8*j]
        and     a, d
        neg     e
        sbb     [z+8*j], a
        sbb     e, e
        inc     j
        cmp     j, k
        jc      Lbignum_montredc_corrloop

Lbignum_montredc_end:
        CFI_INC_RSP(8)
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

S2N_BN_SIZE_DIRECTIVE(bignum_montredc)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
