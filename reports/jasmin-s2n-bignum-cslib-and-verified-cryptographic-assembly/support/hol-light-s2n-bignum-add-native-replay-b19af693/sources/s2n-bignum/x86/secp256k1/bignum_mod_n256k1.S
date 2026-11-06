// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo group order, z := x mod n_256k1
// Input x[k]; output z[4]
//
//    extern void bignum_mod_n256k1(uint64_t z[static 4], uint64_t k,
//                                  const uint64_t *x);
//
// Reduction is modulo the group order of the secp256k1 curve.
//
// Standard x86-64 ABI: RDI = z, RSI = k, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = k, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_n256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_n256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_n256k1)
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

#define q rbx
#define t r13

S2N_BN_SYMBOL(bignum_mod_n256k1):
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
        CFI_PUSH(r13)

// If the input is already <= 3 words long, go to a trivial "copy" path

        cmp     k, 4
        jc      Lbignum_mod_n256k1_shortinput

// Otherwise load the top 4 digits (top-down) and reduce k by 4

        sub     k, 4
        mov     m3, [rdx+8*k+24]
        mov     m2, [rdx+8*k+16]
        mov     m1, [rdx+8*k+8]
        mov     m0, [rdx+8*k]

// Move x into another register to leave rdx free for multiplies

        mov     x, rdx

// Reduce the top 4 digits mod n_256k1 (conditional subtraction of n_256k1).
// We add 2^256 - n_256k1 = [0; 1; 0x4551231950b75fc4; 0x402da1732fc9bebf];
// if this carries, value >= n_256k1 so keep the reduced value.

        mov     rax, 0x402da1732fc9bebf
        mov     q, 0x4551231950b75fc4

        add     m0, rax
        adc     m1, q
        adc     m2, 1
        adc     m3, 0
        sbb     d, d
        not     d
        and     rax, d
        and     q, d
        and     d, 1
        sub     m0, rax
        sbb     m1, q
        sbb     m2, d
        sbb     m3, 0

// Now do (k-4) iterations of 5->4 word modular reduction

        test    k, k
        jz      Lbignum_mod_n256k1_writeback

Lbignum_mod_n256k1_loop:

// Writing the input as z = 2^256 * m3 + rest, our quotient approximation is
// q = min(m3 + 1, 2^64 - 1). This is accurate because 2^256 - n_256k1 is
// only about 2^129, so the true quotient is m3 or m3 + 1.

        mov     rax, m3
        add     rax, 1
        sbb     rdx, rdx
        or      rax, rdx
        mov     q, rax

// Load the next digit so current m to reduce = [m3;m2;m1;m0;d]

        mov     d, [x+8*k-8]

// Compensate m3 for 2^256 * q

        sub     m3, q

// Compute [t3;t2;t1;t0] = q * (2^256 - n_256k1) = q * [0; 1; n1; n0]
// First multiply: q * n0

        mov     rax, 0x402da1732fc9bebf
        mul     q
        mov     t, rdx
        add     d, rax
        adc     t, 0

// Second multiply: q * n1

        mov     rax, 0x4551231950b75fc4
        mul     q
        add     t, rax
        adc     rdx, 0
        add     rdx, q
        mov     eax, 0
        adc     rax, 0

// Add product to residue [m3;m2;m1;m0] (t0 already added to d)

        add     m0, t
        adc     m1, rdx
        adc     m2, rax
        adc     m3, 0

// Now our top word m3 is either zero or all 1s. Use it for a masked
// addition of n_256k1, which we can do by a *subtraction* of
// 2^256 - n_256k1 from our portion. Compute all masks first since
// AND clears CF, which would break the sub/sbb borrow chain.

        mov     rax, 0x402da1732fc9bebf
        and     rax, m3
        mov     rdx, 0x4551231950b75fc4
        and     rdx, m3
        mov     t, 1
        and     t, m3

        sub     d, rax
        sbb     m0, rdx
        sbb     m1, t
        sbb     m2, 0

// Shuffle registers up and loop

        mov     m3, m2
        mov     m2, m1
        mov     m1, m0
        mov     m0, d

        dec     k
        jnz     Lbignum_mod_n256k1_loop

// Write back

Lbignum_mod_n256k1_writeback:

        mov     [z], m0
        mov     [z+8], m1
        mov     [z+16], m2
        mov     [z+24], m3

// Restore registers and return

        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

Lbignum_mod_n256k1_shortinput:

        xor     m0, m0
        xor     m1, m1
        xor     m2, m2
        xor     m3, m3

        test    k, k
        jz      Lbignum_mod_n256k1_writeback
        mov     m0, [rdx]
        dec     k
        jz      Lbignum_mod_n256k1_writeback
        mov     m1, [rdx + 8]
        dec     k
        jz      Lbignum_mod_n256k1_writeback
        mov     m2, [rdx + 16]
        jmp     Lbignum_mod_n256k1_writeback

S2N_BN_SIZE_DIRECTIVE(bignum_mod_n256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
