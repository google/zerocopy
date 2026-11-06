// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply-add, z := z + x * y
// Inputs x[m], y[n]; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_madd(uint64_t k, uint64_t *z, uint64_t m,
//                                const uint64_t *x, uint64_t n, const uint64_t *y);
//
// Does the "z := x * y + z" operation, while also returning a "next" or
// "carry" word. In the case where m + n <= p (i.e. the pure product would
// fit in the destination) this is the remainder for the exact result.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = m, RCX = x, R8 = n, R9 = y, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = m, R9 = x, [RSP+40] = n, [RSP+48] = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_madd)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_madd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_madd)
        .text
        .balign 32

// These are actually right

#define p rdi
#define z rsi
#define n r8

// These are not

#define c r15
#define h r14
#define l r13
#define x r12
#define y r11
#define i rbx
#define k r10
#define m rbp

// These are always local scratch since multiplier result is in these

#define a rax
#define d rdx



S2N_BN_SYMBOL(bignum_madd):
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

// We use too many registers, and also we need rax:rdx for multiplications

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        mov     m, rdx

// If the result size is zero, just return rax = 0
// We could also do this if either input is size 0.

        xor     rax, rax
        test    p, p
        jz      Lbignum_madd_end

// Set initial 2-part sum to zero (we zero c inside the body)

        xor     h,h
        xor     l,l

// Otherwise do outer loop k = 0 ... k = p - 1

        xor     k, k

Lbignum_madd_outerloop:

// Zero our carry term first; we eventually want it and a zero is useful now
// Set a =  max 0 (k + 1 - n), i = min (k + 1) m
// This defines the range a <= j < i for the inner summation
// Note that since k < p < 2^64 we can assume k + 1 doesn't overflow
// And since we want to increment it anyway, we might as well do it now

        xor     c, c            // c = 0
        inc     k               // k = k + 1

        mov     a, k            // a = k + 1
        sub     a, n            // a = k + 1 - n
        cmovc   a, c            // a = max 0 (k + 1 - n)

        mov     i, m            // i = m
        cmp     k, m            // CF <=> k + 1 < m
        cmovc   i, k            // i = min (k + 1) m

// Turn i into a loop count, and skip things if it's <= 0
// Otherwise set up initial pointers x -> x0[a] and y -> y0[k - a]
// and then launch into the main inner loop, postdecrementing i

        mov     d, k
        sub     d, i
        sub     i, a
        jbe     Lbignum_madd_innerend
        lea     x,[rcx+8*a]
        lea     y,[r9+8*d-8]

Lbignum_madd_innerloop:
        mov     rax, [y+8*i]
        mul     QWORD PTR  [x]
        add     x, 8
        add     l, rax
        adc     h, rdx
        adc     c, 0
        dec     i
        jnz     Lbignum_madd_innerloop

Lbignum_madd_innerend:

        add     [z], l
        adc     h, 0
        adc     c, 0
        mov     l, h
        mov     h, c
        add     z, 8

        cmp     k, p
        jc      Lbignum_madd_outerloop

// Move the carry term into the return value

        mov     rax, l

Lbignum_madd_end:
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

S2N_BN_SIZE_DIRECTIVE(bignum_madd)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
