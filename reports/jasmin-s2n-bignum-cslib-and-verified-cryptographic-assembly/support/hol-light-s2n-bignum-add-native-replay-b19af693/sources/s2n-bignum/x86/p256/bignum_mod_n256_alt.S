// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo group order, z := x mod n_256
// Input x[k]; output z[4]
//
//    extern void bignum_mod_n256_alt(uint64_t z[static 4], uint64_t k,
//                                    const uint64_t *x);
//
// Reduction is modulo the group order of the NIST curve P-256.
//
// Standard x86-64 ABI: RDI = z, RSI = k, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = k, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_n256_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_n256_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_n256_alt)
        .text
        .balign 32

#define z rdi
#define k rsi
#define x rcx

#define m0 r8
#define m1 r9
#define m2 r10
#define m3 r11
#define d r12

#define n0 rax
#define n1 rbx
#define n3 rdx

#define q rbx

#define n0short eax
#define n3short edx


S2N_BN_SYMBOL(bignum_mod_n256_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save extra registers

        CFI_PUSH(rbx)
        CFI_PUSH(r12)

// If the input is already <= 3 words long, go to a trivial "copy" path

        cmp     k, 4
        jc      Lbignum_mod_n256_alt_shortinput

// Otherwise load the top 4 digits (top-down) and reduce k by 4

        sub     k, 4
        mov     m3, [rdx+8*k+24]
        mov     m2, [rdx+8*k+16]
        mov     m1, [rdx+8*k+8]
        mov     m0, [rdx+8*k]

// Move x into another register to leave rdx free for multiplies and use of n3

        mov     x, rdx

// Reduce the top 4 digits mod n_256 (a conditional subtraction of n_256)

        mov     n0, 0x0c46353d039cdaaf
        mov     n1, 0x4319055258e8617b
        mov     n3short, 0x00000000ffffffff

        add     m0, n0
        adc     m1, n1
        adc     m2, 0
        adc     m3, n3
        sbb     d, d
        not     d
        and     n0, d
        and     n1, d
        and     n3, d
        sub     m0, n0
        sbb     m1, n1
        sbb     m2, 0
        sbb     m3, n3

// Now do (k-4) iterations of 5->4 word modular reduction

        test    k, k
        jz      Lbignum_mod_n256_alt_writeback

Lbignum_mod_n256_alt_loop:

// Writing the input as z = 2^256 * m3 + 2^192 * m2 + t = 2^192 * h + t, our
// intended quotient approximation is MIN ((h + h>>32 + 1)>>64) (2^64 - 1).

        mov     n0, m3
        shld    n0, m2, 32
        mov     q, m3
        shr     q, 32

        xor     rdx, rdx
        sub     rdx, 1

        adc     n0, m2
        adc     q, m3
        sbb     n0, n0
        or      q, n0

// Load the next digit so current m to reduce = [m3;m2;m1;m0;d]

        mov     d, [x+8*k-8]

// Now form [m3;m2;m1;m0;d] = m - q * n_256

        sub     m3, q

        mov     rax, 0x0c46353d039cdaaf
        mul     q
        add     d, rax
        adc     m0, rdx
        adc     m1, 0
        adc     m2, 0
        adc     m3, 0

        mov     rax, 0x4319055258e8617b
        mul     q
        add     m0, rax
        adc     m1, rdx
        adc     m2, 0
        adc     m3, 0

        mov     rax, 0x00000000ffffffff
        mul     q
        add     m2, rax
        adc     m3, rdx

// Now our top word m3 is either zero or all 1s. Use it for a masked
// addition of n_256, which we can do by a *subtraction* of
// 2^256 - n_256 from our portion

        mov     n0, 0x0c46353d039cdaaf
        and     n0, m3
        mov     n1, 0x4319055258e8617b
        and     n1, m3
        mov     n3short, 0x00000000ffffffff
        and     n3, m3

        sub     d, n0
        sbb     m0, n1
        sbb     m1, 0
        sbb     m2, n3

// Now shuffle registers up and loop

        mov     m3, m2
        mov     m2, m1
        mov     m1, m0
        mov     m0, d

        dec     k
        jnz     Lbignum_mod_n256_alt_loop

// Write back

Lbignum_mod_n256_alt_writeback:

        mov     [z], m0
        mov     [z+8], m1
        mov     [z+16], m2
        mov     [z+24], m3

// Restore registers and return

        CFI_POP(r12)
        CFI_POP(rbx)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

Lbignum_mod_n256_alt_shortinput:

        xor     m0, m0
        xor     m1, m1
        xor     m2, m2
        xor     m3, m3

        test    k, k
        jz      Lbignum_mod_n256_alt_writeback
        mov     m0, [rdx]
        dec     k
        jz      Lbignum_mod_n256_alt_writeback
        mov     m1, [rdx + 8]
        dec     k
        jz      Lbignum_mod_n256_alt_writeback
        mov     m2, [rdx + 16]
        jmp     Lbignum_mod_n256_alt_writeback

S2N_BN_SIZE_DIRECTIVE(bignum_mod_n256_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
