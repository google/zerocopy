// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo field characteristic, z := x mod p_256k1
// Input x[k]; output z[4]
//
//    extern void bignum_mod_p256k1(uint64_t z[static 4], uint64_t k,
//                                  const uint64_t *x);
//
// Standard x86-64 ABI: RDI = z, RSI = k, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = k, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_p256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_p256k1)
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

#define c rbx

S2N_BN_SYMBOL(bignum_mod_p256k1):
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
        jc      Lbignum_mod_p256k1_shortinput

// Otherwise load the top 4 digits (top-down) and reduce k by 4

        sub     k, 4
        mov     m3, [rdx+8*k+24]
        mov     m2, [rdx+8*k+16]
        mov     m1, [rdx+8*k+8]
        mov     m0, [rdx+8*k]

// Move x into another register to leave rdx free for multiplies

        mov     x, rdx

// Load the constant c = 4294968273, i.e. p_256k1 = 2^256 - c

        mov     c, 0x1000003D1

// Reduce the top 4 digits mod p_256k1 (conditional subtraction of p_256k1).
// We add c = 2^256 - p_256k1; if this carries, value >= p_256k1 so keep.

        add     m0, c
        adc     m1, 0
        adc     m2, 0
        adc     m3, 0

// If no carry (CF=0), the value was < p_256k1, so undo the addition

        sbb     rax, rax
        not     rax
        and     rax, c
        sub     m0, rax
        sbb     m1, 0
        sbb     m2, 0
        sbb     m3, 0

// Now do (k-4) iterations of 5->4 word modular reduction

        test    k, k
        jz      Lbignum_mod_p256k1_writeback

Lbignum_mod_p256k1_loop:

// Writing the input as z = 2^256 * m3 + rest, our quotient approximation is
// q = min(m3 + 1, 2^64 - 1). This is accurate because p_256k1 = 2^256 - c
// with c only 33 bits, so the true quotient is m3 or m3 + 1.

        mov     rax, m3
        add     rax, 1
        sbb     rdx, rdx
        or      rax, rdx

// Load the next digit so current m to reduce = [m3;m2;m1;m0;d]

        mov     d, [x+8*k-8]

// Now form [m3;m2;m1;m0;d] = m - q * p_256k1
// = m - q * (2^256 - c) = m - q*2^256 + q*c
// First compensate for the 2^256 * q term

        sub     m3, rax

// Now [rdx;rax] = q * c (mul uses rax as implicit source, q is still in rax)

        mul     c

// [m3;m2;m1;m0;d] += [0;0;0;rdx;rax]

        add     d, rax
        adc     m0, rdx
        adc     m1, 0
        adc     m2, 0
        adc     m3, 0

// Now our top word m3 is either zero or all 1s. Use it for a masked
// subtraction of c (equivalently a masked addition of p_256k1)

        mov     rax, c
        and     rax, m3
        sub     d, rax
        sbb     m0, 0
        sbb     m1, 0
        sbb     m2, 0

// Shuffle registers up and loop

        mov     m3, m2
        mov     m2, m1
        mov     m1, m0
        mov     m0, d

        dec     k
        jnz     Lbignum_mod_p256k1_loop

// Write back

Lbignum_mod_p256k1_writeback:

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

Lbignum_mod_p256k1_shortinput:

        xor     m0, m0
        xor     m1, m1
        xor     m2, m2
        xor     m3, m3

        test    k, k
        jz      Lbignum_mod_p256k1_writeback
        mov     m0, [rdx]
        dec     k
        jz      Lbignum_mod_p256k1_writeback
        mov     m1, [rdx + 8]
        dec     k
        jz      Lbignum_mod_p256k1_writeback
        mov     m2, [rdx + 16]
        jmp     Lbignum_mod_p256k1_writeback

S2N_BN_SIZE_DIRECTIVE(bignum_mod_p256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
