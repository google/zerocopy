// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Copy bignum with zero-extension or truncation, z := x
// Input x[n]; output z[k]
//
//    extern void bignum_copy(uint64_t k, uint64_t *z, uint64_t n, const uint64_t *x);
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n, R9 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_copy)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_copy)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_copy)
        .text
        .balign 32

#define k rdi
#define z rsi
#define n rdx
#define x rcx

#define i r8
#define a rax



S2N_BN_SYMBOL(bignum_copy):
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

// Replace RDX = n with RDX = min(k,n) so we are definitely safe copying those
// Initialize the element counter to 0

        cmp     k, n
        cmovc   n, k
        xor     i, i

// If min(k,n) = 0 jump to the padding stage

        test    n, n
        jz      Lbignum_copy_padding

Lbignum_copy_copyloop:
        mov     a, [x+8*i]
        mov     [z+8*i], a
        inc     i
        cmp     i, n
        jc      Lbignum_copy_copyloop

Lbignum_copy_padding:
        cmp     i, k
        jnc     Lbignum_copy_end
        xor     a, a

Lbignum_copy_padloop:
        mov     [z+8*i], a
        inc     i
        cmp     i, k
        jc      Lbignum_copy_padloop

Lbignum_copy_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_copy)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
