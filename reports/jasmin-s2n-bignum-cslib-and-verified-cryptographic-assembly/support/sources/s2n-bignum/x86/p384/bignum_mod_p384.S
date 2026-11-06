// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo field characteristic, z := x mod p_384
// Input x[k]; output z[6]
//
//    extern void bignum_mod_p384(uint64_t z[static 6], uint64_t k,
//                                const uint64_t *x);
//
// Standard x86-64 ABI: RDI = z, RSI = k, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = k, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_p384)
        .text
        .balign 32

#define z rdi
#define k rsi
#define x rcx

#define m0 r8
#define m1 r9
#define m2 r10
#define m3 r11
#define m4 r12
#define m5 r13
#define d r14

#define n0 rax
#define n1 rbx
#define n2 rdx
#define q rdx

#define n0short eax
#define n1short ebx
#define qshort edx


S2N_BN_SYMBOL(bignum_mod_p384):
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
        CFI_PUSH(r14)

// If the input is already <= 5 words long, go to a trivial "copy" path

        cmp     k, 6
        jc      Lbignum_mod_p384_shortinput

// Otherwise load the top 6 digits (top-down) and reduce k by 6

        sub     k, 6
        mov     m5, [rdx+8*k+40]
        mov     m4, [rdx+8*k+32]
        mov     m3, [rdx+8*k+24]
        mov     m2, [rdx+8*k+16]
        mov     m1, [rdx+8*k+8]
        mov     m0, [rdx+8*k]

// Move x into another register to leave rdx free for multiplies and use of n2

        mov     x, rdx

// Reduce the top 6 digits mod p_384 (a conditional subtraction of p_384)

        mov     n0short, 0x00000000ffffffff
        mov     n1, 0xffffffff00000000
        mov     n2, 0xfffffffffffffffe

        sub     m0, n0
        sbb     m1, n1
        sbb     m2, n2
        sbb     m3, -1
        sbb     m4, -1
        sbb     m5, -1

        sbb     d, d
        and     n0, d
        and     n1, d
        and     n2, d
        add     m0, n0
        adc     m1, n1
        adc     m2, n2
        adc     m3, d
        adc     m4, d
        adc     m5, d

// Now do (k-6) iterations of 7->6 word modular reduction

        test    k, k
        jz      Lbignum_mod_p384_writeback

Lbignum_mod_p384_loop:

// Compute q = min (m5 + 1) (2^64 - 1)

        mov     qshort, 1
        add     q, m5
        sbb     d, d
        or      q, d

// Load the next digit so current m to reduce = [m5;m4;m3;m2;m1;m0;d]

        mov     d, [x+8*k-8]

// Now form [m5;m4;m3;m2;m1;m0;d] = m - q * p_384. To use an addition for
// the main calculation we do (m - 2^384 * q) + q * (2^384 - p_384)
// where 2^384 - p_384 = [0;0;0;1;0x00000000ffffffff;0xffffffff00000001].
// The extra subtraction of 2^384 * q is the first instruction.

        sub     m5, q
        xor     n0, n0
        mov     n0, 0xffffffff00000001
        mulx    n1, n0, n0
        adcx    d, n0
        adox    m0, n1
        mov     n0short, 0x00000000ffffffff
        mulx    n1, n0, n0
        adcx    m0, n0
        adox    m1, n1
        adcx    m1, q
        mov     n0short, 0
        adox    n0, n0
        adcx    m2, n0
        adc     m3, 0
        adc     m4, 0
        adc     m5, 0

// Now our top word m5 is either zero or all 1s. Use it for a masked
// addition of p_384, which we can do by a *subtraction* of
// 2^384 - p_384 from our portion

        mov     n0, 0xffffffff00000001
        and     n0, m5
        mov     n1short, 0x00000000ffffffff
        and     n1, m5
        and     m5, 1

        sub     d, n0
        sbb     m0, n1
        sbb     m1, m5
        sbb     m2, 0
        sbb     m3, 0
        sbb     m4, 0

// Now shuffle registers up and loop

        mov     m5, m4
        mov     m4, m3
        mov     m3, m2
        mov     m2, m1
        mov     m1, m0
        mov     m0, d

        dec     k
        jnz     Lbignum_mod_p384_loop

// Write back

Lbignum_mod_p384_writeback:

        mov     [z], m0
        mov     [z+8], m1
        mov     [z+16], m2
        mov     [z+24], m3
        mov     [z+32], m4
        mov     [z+40], m5

// Restore registers and return

        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

Lbignum_mod_p384_shortinput:

        xor     m0, m0
        xor     m1, m1
        xor     m2, m2
        xor     m3, m3
        xor     m4, m4
        xor     m5, m5

        test    k, k
        jz      Lbignum_mod_p384_writeback
        mov     m0, [rdx]
        dec     k
        jz      Lbignum_mod_p384_writeback
        mov     m1, [rdx + 8]
        dec     k
        jz      Lbignum_mod_p384_writeback
        mov     m2, [rdx + 16]
        dec     k
        jz      Lbignum_mod_p384_writeback
        mov     m3, [rdx + 24]
        dec     k
        jz      Lbignum_mod_p384_writeback
        mov     m4, [rdx + 32]
        jmp     Lbignum_mod_p384_writeback

S2N_BN_SIZE_DIRECTIVE(bignum_mod_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
