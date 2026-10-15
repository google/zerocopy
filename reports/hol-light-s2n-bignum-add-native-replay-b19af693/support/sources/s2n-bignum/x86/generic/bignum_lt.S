// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compare bignums, x < y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_lt(uint64_t m, const uint64_t *x, uint64_t n,
//                              const uint64_t *y);
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, returns RAX
// Microsoft x64 ABI:   RCX = m, RDX = x, R8 = n, R9 = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_lt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_lt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_lt)
        .text
        .balign 32

#define m rdi
#define x rsi
#define n rdx
#define y rcx
#define i r8
#define a rax

#define ashort eax



S2N_BN_SYMBOL(bignum_lt):
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

// Zero the main index counter for both branches

        xor     i, i

// Speculatively form m := m - n and do case split

        sub     m, n
        jc      Lbignum_lt_ylonger

// The case where x is longer or of the same size (m >= n)

        inc     m
        test    n, n
        jz      Lbignum_lt_xtest
Lbignum_lt_xmainloop:
        mov     a, [x+8*i]
        sbb     a, [y+8*i]
        inc     i
        dec     n
        jnz     Lbignum_lt_xmainloop
        jmp     Lbignum_lt_xtest
Lbignum_lt_xtoploop:
        mov     a, [x+8*i]
        sbb     a, 0
        inc     i
Lbignum_lt_xtest:
        dec     m
        jnz     Lbignum_lt_xtoploop
        sbb     a, a
        neg     a
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        ret

// The case where y is longer (n > m)

Lbignum_lt_ylonger:
        add     m, n
        sub     n, m
        test    m, m
        jz      Lbignum_lt_ytoploop
Lbignum_lt_ymainloop:
        mov     a, [x+8*i]
        sbb     a, [y+8*i]
        inc     i
        dec     m
        jnz     Lbignum_lt_ymainloop
Lbignum_lt_ytoploop:
        mov     ashort, 0
        sbb     a, [y+8*i]
        inc     i
        dec     n
        jnz     Lbignum_lt_ytoploop

        sbb     a, a
        neg     a
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_lt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
