// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Shift bignum right by c < 64 bits z := floor(x / 2^c)
// Inputs x[n], c; outputs function return (bits shifted out) and z[k]
//
//    extern uint64_t bignum_shr_small(uint64_t k, uint64_t *z, uint64_t n,
//                                     const uint64_t *x, uint64_t c);
//
// Does the "z := x >> c" operation where x is n digits, result z is p.
// The shift count c is masked to 6 bits so it actually uses c' = c mod 64.
// The return value is the inout mod 2^c'.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x, R8 = c, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n, R9 = x, [RSP+40] = c, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_shr_small)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_shr_small)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_shr_small)
        .text
        .balign 32

#define p rdi
#define z rsi
#define n rdx

// These get moved from their initial positions

#define c rcx
#define x r9

// Other variables

#define b rax
#define t r8
#define a r10

#define ashort r10d



S2N_BN_SYMBOL(bignum_shr_small):
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

// Reshuffle registers to put the shift count into CL

        mov     x, rcx
        mov     c, r8

// Set default carry-in word to 0, useful for other things too

        xor     b, b

// First, if p > n then pad output on the left with p-n zeros

        cmp     n, p
        jnc     Lbignum_shr_small_nopad
Lbignum_shr_small_padloop:
        dec     p
        mov     [z+8*p],b
        cmp     n, p
        jc      Lbignum_shr_small_padloop
Lbignum_shr_small_nopad:

// We now know that p <= n. If in fact p < n let carry word = x[p] instead of 0

        jz      Lbignum_shr_small_shiftstart
        mov     b,[x+8*p]
Lbignum_shr_small_shiftstart:
        test    p, p
        jz      Lbignum_shr_small_trivial

// Now the main loop

Lbignum_shr_small_loop:
        mov     a, [x+8*p-8]
        mov     t, a
        shrd    a, b, cl
        mov     [z+8*p-8],a
        mov     b, t
        dec     p
        jnz     Lbignum_shr_small_loop

// Mask the carry word and return with that as RAX = b

Lbignum_shr_small_trivial:
        mov     ashort, 1
        shl     a, cl
        dec     a
        and     b, a

Lbignum_shr_small_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_shr_small)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
