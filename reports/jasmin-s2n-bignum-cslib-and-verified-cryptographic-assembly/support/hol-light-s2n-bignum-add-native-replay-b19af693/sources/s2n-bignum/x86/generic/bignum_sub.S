// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Subtract, z := x - y
// Inputs x[m], y[n]; outputs function return (carry-out) and z[p]
//
//    extern uint64_t bignum_sub(uint64_t p, uint64_t *z, uint64_t m,
//                               const uint64_t *x, uint64_t n, const uint64_t *y);
//
// Does the z := x - y operation, truncating modulo p words in general and
// returning a top borrow (0 or 1) in the p'th place, only subtracting input
// words below p (as well as m and n respectively) to get the diff and borrow.
//
// Standard x86-64 ABI: RDI = p, RSI = z, RDX = m, RCX = x, R8 = n, R9 = y, returns RAX
// Microsoft x64 ABI:   RCX = p, RDX = z, R8 = m, R9 = x, [RSP+40] = n, [RSP+48] = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sub)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_sub)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sub)
        .text
        .balign 32

#define p rdi
#define z rsi
#define m rdx
#define x rcx
#define n r8
#define y r9
#define i r10
#define a rax

#define ashort eax



S2N_BN_SYMBOL(bignum_sub):
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

// Zero the main index counter for both branches

        xor     i, i

// First clamp the two input sizes m := min(p,m) and n := min(p,n) since
// we'll never need words past the p'th. Can now assume m <= p and n <= p.
// Then compare the modified m and n and branch accordingly

        cmp     p, m
        cmovc   m, p
        cmp     p, n
        cmovc   n, p
        cmp     m, n
        jc      Lbignum_sub_ylonger

// The case where x is longer or of the same size (p >= m >= n)

        sub     p, m
        sub     m, n
        inc     m
        test    n, n
        jz      Lbignum_sub_xtest
Lbignum_sub_xmainloop:
        mov     a, [x+8*i]
        sbb     a, [y+8*i]
        mov     [z+8*i],a
        inc     i
        dec     n
        jnz     Lbignum_sub_xmainloop
        jmp     Lbignum_sub_xtest
Lbignum_sub_xtoploop:
        mov     a, [x+8*i]
        sbb     a, 0
        mov     [z+8*i],a
        inc     i
Lbignum_sub_xtest:
        dec     m
        jnz     Lbignum_sub_xtoploop
        sbb     a, a
        test    p, p
        jz      Lbignum_sub_tailskip
Lbignum_sub_tailloop:
        mov     [z+8*i],a
        inc     i
        dec     p
        jnz     Lbignum_sub_tailloop
Lbignum_sub_tailskip:
        neg     a
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        ret

// The case where y is longer (p >= n > m)

Lbignum_sub_ylonger:

        sub     p, n
        sub     n, m
        test    m, m
        jz      Lbignum_sub_ytoploop
Lbignum_sub_ymainloop:
        mov     a, [x+8*i]
        sbb     a, [y+8*i]
        mov     [z+8*i],a
        inc     i
        dec     m
        jnz     Lbignum_sub_ymainloop
Lbignum_sub_ytoploop:
        mov     ashort, 0
        sbb     a, [y+8*i]
        mov     [z+8*i],a
        inc     i
        dec     n
        jnz     Lbignum_sub_ytoploop
        sbb     a, a
        test    p, p
        jnz     Lbignum_sub_tailloop
        neg     a
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_sub)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
