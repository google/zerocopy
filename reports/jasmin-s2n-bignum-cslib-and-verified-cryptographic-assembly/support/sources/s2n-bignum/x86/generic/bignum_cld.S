// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Count leading zero digits (64-bit words)
// Input x[k]; output function return
//
//    extern uint64_t bignum_cld(uint64_t k, const uint64_t *x);
//
// In the case of a zero bignum as input the result is k
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cld)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cld)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cld)
        .text
        .balign 32

#define k rdi
#define x rsi
#define i rax
#define a rcx
#define j rdx



S2N_BN_SYMBOL(bignum_cld):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Initialize the index i and also prepare default return value of 0 (i = rax)

        xor     i, i

// If the bignum is zero-length, just return k = 0

        test    k, k
        jz      Lbignum_cld_end

// Run over the words j = 0..i-1, and set i := j + 1 when hitting nonzero a[j]

        xor     j, j
Lbignum_cld_loop:
        mov     a, [x+8*j]
        inc     j
        test    a, a
        cmovnz  i, j
        cmp     j, k
        jnz     Lbignum_cld_loop

        neg     rax
        add     rax, rdi

Lbignum_cld_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_cld)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
