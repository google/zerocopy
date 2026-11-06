// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo field characteristic, z := x mod p_sm2
// Input x[k]; output z[4]
//
//    extern void bignum_mod_sm2(uint64_t z[static 4], uint64_t k, const uint64_t *x);
//
// Standard x86-64 ABI: RDI = z, RSI = k, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = k, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_sm2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_sm2)
        .text
        .balign 32

#define z rdi
#define k rsi
#define x rdx

#define m0 r8
#define m1 r9
#define m2 r10
#define m3 r11
#define d r12

#define n0 rax
#define n1 rbx
#define n3 rcx
#define q rcx

#define qshort ecx

S2N_BN_SYMBOL(bignum_mod_sm2):
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
        jc      Lbignum_mod_sm2_shortinput

// Otherwise load the top 4 digits (top-down) and reduce k by 4

        sub     k, 4
        mov     m3, [x+8*k+24]
        mov     m2, [x+8*k+16]
        mov     m1, [x+8*k+8]
        mov     m0, [x+8*k]

// Load non-trivial digits [n3; -1; n1; -1] = p_sm2 and do a conditional
// subtraction to reduce the four starting digits [m3;m2;m1;m0] modulo p_sm2

        sub     m0, -1
        mov     n1, 0xffffffff00000000
        sbb     m1, n1
        mov     n3, 0xfffffffeffffffff
        sbb     m2, -1
        sbb     m3, n3

        sbb     n0, n0

        and     n1, n0
        and     n3, n0
        add     m0, n0
        adc     m1, n1
        adc     m2, n0
        adc     m3, n3

// Now do (k-4) iterations of 5->4 word modular reduction

        test    k, k
        jz      Lbignum_mod_sm2_writeback

Lbignum_mod_sm2_loop:

// Writing the input, with the new zeroth digit implicitly appended, as
// z = 2^256 * m3 + 2^192 * m2 + t, our intended quotient approximation is
// MIN ((m3 * (1 + 2^32 + 2^64) + m2 + 2^64) >> 64) (2^64 - 1)

        mov     d, m2
        mov     qshort, 1
        add     d, m3
        adc     q, m3

        shr     d, 32
        add     d, m3

        shr     d, 32
        add     q, d
        sbb     q, 0

// Load the next digit so current m to reduce = [m3;m2;m1;m0;d]

        mov     d, [x+8*k-8]

// Now compute the initial pre-reduced [m3;m2;m1;m0;d] = m - p_sm2 * q
// = z - (2^256 - 2^224 - 2^96 + 2^64 - 1) * q

        mov     n0, q
        mov     n1, q
        shl     n0, 32
        shr     n1, 32

        add     m2, n0
        adc     m3, n1

        sub     n0, q
        sbb     n1, 0

        sub     m3, q

        add     d, q
        adc     m0, n0
        adc     m1, n1
        adc     m2, 0
        adc     m3, 0

// Now our top word m3 is either zero or all 1s, and we use this to discriminate
// whether a correction is needed because our result is negative, as a bitmask
// Do a masked addition of p_sm2

        mov     n1, 0xffffffff00000000
        and     n1, m3
        mov     n3, 0xfffffffeffffffff
        and     n3, m3
        add     d, m3
        adc     m0, n1
        adc     m1, m3
        adc     m2, n3

// Shuffle registers up and loop

        mov     m3, m2
        mov     m2, m1
        mov     m1, m0
        mov     m0, d

        dec     k
        jnz     Lbignum_mod_sm2_loop

// Write back

Lbignum_mod_sm2_writeback:

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

Lbignum_mod_sm2_shortinput:

        xor     m0, m0
        xor     m1, m1
        xor     m2, m2
        xor     m3, m3

        test    k, k
        jz      Lbignum_mod_sm2_writeback
        mov     m0, [rdx]
        dec     k
        jz      Lbignum_mod_sm2_writeback
        mov     m1, [rdx + 8]
        dec     k
        jz      Lbignum_mod_sm2_writeback
        mov     m2, [rdx + 16]
        jmp     Lbignum_mod_sm2_writeback

S2N_BN_SIZE_DIRECTIVE(bignum_mod_sm2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
