// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Return bignum of power of 2, z := 2^n
// Input n; output z[k]
//
//    extern void bignum_pow2(uint64_t k, uint64_t *z, uint64_t n);
//
// The result is as usual mod 2^{64*k}, so will be zero if n >= 64*k.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_pow2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_pow2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_pow2)
        .text
        .balign 32

#define k rdi
#define z rsi
#define n rdx

#define i rcx
#define w rax
#define a r8

#define wshort eax



S2N_BN_SYMBOL(bignum_pow2):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// If k = 0 do nothing

        test    k, k
        jz      Lbignum_pow2_end

// Create the index n at which to write the nonzero word and the word w itself
// Note that the x86 manual explicitly says that shift counts are taken modulo
// the datasize, so we don't need to mask the lower 6 bits of n ourselves.

        mov     wshort, 1
        mov     rcx, n
        shl     w, cl
        shr     n, 6

// Now in a constant-time fashion set the n'th word to w and others to zero

        xor     i, i
Lbignum_pow2_loop:
        xor     a, a
        cmp     i, n
        cmovz   a, w
        mov     [z+8*i],a
        inc     i
        cmp     i, k
        jc      Lbignum_pow2_loop

Lbignum_pow2_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_pow2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
