// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Divide bignum by 10: z' := z div 10, returning remainder z mod 10
// Inputs z[k]; outputs function return (remainder) and z[k]
//
//    extern uint64_t bignum_divmod10(uint64_t k, uint64_t *z);
//
// Standard x86-64 ABI: RDI = k, RSI = z, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = z, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_divmod10)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_divmod10)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_divmod10)
        .text
        .balign 32

#define k rdi
#define z rsi

#define d rcx

#define l rdx
#define r rax

#define q r8
#define h r8

#define s r9
#define w r10

#define rshort eax
#define wshort r10d

S2N_BN_SYMBOL(bignum_divmod10):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Initialize remainder to 0 and if k = 0 return

        xor     rshort, rshort
        test    k, k
        jz      Lbignum_divmod10_end

// Straightforward top-down loop doing 10 * q + r' := 2^64 * r + d

        mov     s, 0x3333333333333334
        mov     wshort, 0x3333333

Lbignum_divmod10_divloop:
        mov     d, [z+8*k-8]

// First re-split and shift so 2^28 * h + l = (2^64 * r + d) / 2
// Then (2^64 * r + d) / 10 = [(2^28 - 1) / 5] * h + (h + l) / 5

        mov     l, d
        shl     l, 35
        shld    r, d, 35
        shr     l, 36
        mov     h, r

        add     r, l
        mul     s
        imul    h, w
        add     q, l
        mov     [z+8*k-8], q

// Generate the new remainder r = d - 10 * q
// Since r <= 9 we only need the low part computation ignoring carries

        lea     q, [q+4*q]
        neg     q
        lea     r, [d+2*q]

        dec     k
        jnz     Lbignum_divmod10_divloop

// Return rax = r as the final remainder

Lbignum_divmod10_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_divmod10)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
