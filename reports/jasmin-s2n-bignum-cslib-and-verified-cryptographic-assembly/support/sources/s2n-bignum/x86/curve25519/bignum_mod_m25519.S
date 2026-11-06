// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo group order, z := x mod m_25519
// Input x[k]; output z[4]
//
//    extern void bignum_mod_m25519(uint64_t z[static 4], uint64_t k,
//                                  const uint64_t *x);
//
// Reduction is modulo the group order of curve25519/edwards25519.
// This is the full group order, 8 * the standard basepoint order.
//
// Standard x86-64 ABI: RDI = z, RSI = k, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = k, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_m25519)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_m25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_m25519)
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

S2N_BN_SYMBOL(bignum_mod_m25519):
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
        CFI_PUSH(rbp)
        CFI_PUSH(r12)

// If the input is already <= 3 words long, go to a trivial "copy" path

        cmp     k, 4
        jc      Lbignum_mod_m25519_shortinput

// Otherwise load the top 4 digits (top-down) and reduce k by 4
// This [m3;m2;m1;m0] is the initial x where we begin reduction.

        sub     k, 4
        mov     m3, [rdx+8*k+24]
        mov     m2, [rdx+8*k+16]
        mov     m1, [rdx+8*k+8]
        mov     m0, [rdx+8*k]

// Move x into another register to leave rdx free for multiplies

        mov     x, rdx

// Load a set of registers [rbx; 0; rdx; rax] = m_25519

        mov     rax, 0xc09318d2e7ae9f68
        mov     rdx, 0xa6f7cef517bce6b2
        mov     rbx, 0x8000000000000000

// Do the subtraction; since m_25519 > 2^255 we only need either
// subtraction of m_25519 or nothing to reduce it modulo.

        sub     m0, rax
        sbb     m1, rdx
        sbb     m2, 0
        sbb     m3, rbx

// Now CF is set iff x < m_25519. Create a mask for that condition and mask
// the three nontrivial digits ready to undo the previous subtraction with
// a compensating addition

        sbb     rbx, rbx
        and     rax, rbx
        and     rdx, rbx
        shl     rbx, 63

// Now add mask * m_25519 again

        add     m0, rax
        adc     m1, rdx
        adc     m2, 0
        adc     m3, rbx

// Now do (k-4) iterations of 5->4 word modular reduction. Each one
// is similar to the sequence above except for the more refined quotient
// estimation process.

        test    k, k
        jz      Lbignum_mod_m25519_writeback

Lbignum_mod_m25519_loop:

// Assume that the new 5-digit x is 2^64 * previous_x + next_digit.
// Get the quotient estimate q = max (floor(x/2^255)) (2^64 - 1)
// and first compute x' = x - 2^255 * q.

        mov     q, m3
        shld    q, m2, 1
        shr     m3, 63
        sub     q, m3
        shl     m2, 1
        shrd    m2, m3, 1

// Let [rdx;m3;rbp] = q * (m_25519 - 2^255)

        mov     rax, 0xc09318d2e7ae9f68
        mul     q
        mov     rbp, rax
        mov     m3, rdx

        mov     rax, 0xa6f7cef517bce6b2
        mul     q
        add     m3, rax
        adc     rdx, 0

// Load the next digit

        mov     d, [x+8*k-8]

// Subtract to get x' - q * (m_25519 - 2^255) = x - q * m_25519

        sub     d, rbp
        sbb     m0, m3
        sbb     m1, rdx
        sbb     m2, 0

// Get a bitmask for the borrow and create a masked version of
// non-trivial digits of [rbx;0;rdx;rax] = m_25519, then add it.
// The masked n3 digit exploits the fact that bit 63 of n0 is set.

        sbb     rbx, rbx

        mov     rax, 0xc09318d2e7ae9f68
        and     rax, rbx
        mov     rdx, 0xa6f7cef517bce6b2
        and     rdx, rbx
        mov     rbx, 0x8000000000000000
        and     rbx, rax

        add     d, rax
        adc     m0, rdx
        adc     m1, 0
        adc     m2, rbx

// Now shuffle registers up and loop

        mov     m3, m2
        mov     m2, m1
        mov     m1, m0
        mov     m0, d

        dec     k
        jnz     Lbignum_mod_m25519_loop
        jmp     Lbignum_mod_m25519_writeback

Lbignum_mod_m25519_shortinput:

        xor     m0, m0
        xor     m1, m1
        xor     m2, m2
        xor     m3, m3

        test    k, k
        jz      Lbignum_mod_m25519_writeback
        mov     m0, [rdx]
        dec     k
        jz      Lbignum_mod_m25519_writeback
        mov     m1, [rdx + 8]
        dec     k
        jz      Lbignum_mod_m25519_writeback
        mov     m2, [rdx + 16]

// Write back

Lbignum_mod_m25519_writeback:

        mov     [z], m0
        mov     [z+8], m1
        mov     [z+16], m2
        mov     [z+24], m3

// Restore registers and return

        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod_m25519)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
