// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Negated modular inverse, z := (-1/x) mod 2^{64k}
// Input x[k]; output z[k]
//
//    extern void bignum_negmodinv(uint64_t k, uint64_t *z, const uint64_t *x);
//
// Assuming x is odd (otherwise nothing makes sense) the result satisfies
//
//       x * z + 1 == 0 (mod 2^{64 * k})
//
// but is not necessarily reduced mod x.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_negmodinv)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_negmodinv)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_negmodinv)
        .text
        .balign 32

#define k rdi
#define z rsi
// Moved from initial location to free rdx
#define x rcx

#define a rax
#define d rdx
#define i r8
#define m r9
#define h r10
#define w r11
#define t r12
#define e rbx

#define ashort eax
#define ishort r8d

S2N_BN_SYMBOL(bignum_negmodinv):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        CFI_PUSH(rbx)
        CFI_PUSH(r12)

// If k = 0 do nothing (actually we could have avoiding the pushes and pops)

        test    k, k
        jz      Lbignum_negmodinv_end

// Move the x pointer into its permanent home (rdx is needed for muls)

        mov     x, rdx

// Compute word-level negated modular inverse w for x[0].

        mov     a, [x]

        mov     d, a
        mov     w, a
        shl     d, 2
        sub     w, d
        xor     w, 2

        mov     d, w
        imul    d, a
        mov     ashort, 2
        add     a, d
        add     d, 1

        imul    w, a

        imul    d, d
        mov     ashort, 1
        add     a, d
        imul    w, a

        imul    d, d
        mov     ashort, 1
        add     a, d
        imul    w, a

        imul    d, d
        mov     ashort, 1
        add     a, d
        imul    w, a

// Write that as lowest word of the output, then if k = 1 we're finished

        mov     [z], w
        cmp     k, 1
        jz      Lbignum_negmodinv_end

// Otherwise compute and write the other digits (1..k-1) of w * x + 1

        mov     a, [x]
        xor     h, h
        mul     w
        add     a, 1
        adc     h, d
        mov     ishort, 1
Lbignum_negmodinv_initloop:
        mov     a, [x+8*i]
        mul     w
        add     a, h
        adc     d, 0
        mov     [z+8*i], a
        mov     h, d
        inc     i
        cmp     i, k
        jc      Lbignum_negmodinv_initloop

// For simpler indexing, z := z + 8 and k := k - 1 per outer iteration
// Then we can use the same index for x and for z and effective size k.
//
// But we also offset k by 1 so the "real" size is k + 1; after doing
// the special zeroth bit we count with t through k more digits, so
// getting k + 1 total as required.
//
// This lets us avoid some special cases inside the loop at the cost
// of needing the additional "finale" tail for the final iteration
// since we do one outer loop iteration too few.

        sub     k, 2
        jz      Lbignum_negmodinv_finale

Lbignum_negmodinv_outerloop:
        add     z, 8

        mov     h, [z]
        mov     m, w
        imul    m, h
        mov     [z], m
        mov     a, [x]
        mul     m
        add     a, h
        adc     d, 0
        mov     h, d
        mov     ishort, 1
        mov     t, k
        .byte 0x0f,0x1f,0x40,0x00  // JCC erratum (SKX102): pad so this loop's
        // back-edge does not straddle a 32-byte boundary at 0-mod-32 entry
Lbignum_negmodinv_innerloop:
        adc     h, [z+8*i]
        sbb     e, e
        mov     a, [x+8*i]
        mul     m
        sub     d, e
        add     a, h
        mov     [z+8*i], a
        mov     h, d
        inc     i
        dec     t
        jnz     Lbignum_negmodinv_innerloop

        dec     k
        jnz     Lbignum_negmodinv_outerloop

Lbignum_negmodinv_finale:
        mov     a, [z+8]
        imul    a, w
        mov     [z+8], a

Lbignum_negmodinv_end:
        CFI_POP(r12)
        CFI_POP(rbx)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_negmodinv)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
