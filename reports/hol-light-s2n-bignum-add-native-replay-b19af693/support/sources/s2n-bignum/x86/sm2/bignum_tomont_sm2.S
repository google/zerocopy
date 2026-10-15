// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert to Montgomery form z := (2^256 * x) mod p_sm2
// Input x[4]; output z[4]
//
//    extern void bignum_tomont_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_sm2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tomont_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_sm2)
        .text

#define z rdi
#define x rsi

#define m0 r8
#define m1 r9
#define m2 r10
#define m3 r11

#define q rax
#define n1 rcx
#define n3 rdx
#define qshort eax

// ----------------------------------------------------------------------------
// Core "x |-> (2^64 * x) mod p_sm2" macro, with x assumed to be < p_sm2.
// Input is [d3;d2;d1;d0] and output is [d2;d1;d0;q] where q is a fixed
// quotient estimate register (rax), so the registers get shuffled.
// ----------------------------------------------------------------------------

#define modstep_sm2(d3,d2,d1,d0)                                        \
/* Writing the input, with lower zero digit appended, as        */      \
/* z = 2^256 * d3 + 2^192 * d2 + t, quotient approximation is   */      \
/* MIN ((d3 * (1 + 2^32 + 2^64) + d2 + 2^64) >> 64) (2^64 - 1)  */      \
        mov     n1, d2;                                                 \
        mov     qshort, 1;                                              \
        add     n1, d3;                                                 \
        adc     q, d3;                                                  \
        shr     n1, 32;                                                 \
        add     n1, d3;                                                 \
        shr     n1, 32;                                                 \
        add     q, n1;                                                  \
        sbb     q, 0;                                                   \
/* Compute the pre-reduced [d3;d2;d1;d0;q] = m - p_sm2 * q      */      \
/* = z - (2^256 - 2^224 - 2^96 + 2^64 - 1) * q                  */      \
        mov     n1, q;                                                  \
        mov     n3, q;                                                  \
        shl     n1, 32;                                                 \
        shr     n3, 32;                                                 \
        add     d2, n1;                                                 \
        adc     d3, n3;                                                 \
        sub     n1, q;                                                  \
        sbb     n3, 0;                                                  \
        sub     d3, q;                                                  \
        add     d0, n1;                                                 \
        adc     d1, n3;                                                 \
        adc     d2, 0;                                                  \
        adc     d3, 0;                                                  \
/* Corrective addition with top word d3 as a bitmask            */      \
        mov     n1, 0xffffffff00000000;                                 \
        and     n1, d3;                                                 \
        mov     n3, 0xfffffffeffffffff;                                 \
        and     n3, d3;                                                 \
        add     q, d3;                                                  \
        adc     d0, n1;                                                 \
        adc     d1, d3;                                                 \
        adc     d2, n3

S2N_BN_SYMBOL(bignum_tomont_sm2):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the inputs

        mov     m0, [x]
        mov     m1, [x+8]
        mov     m2, [x+16]
        mov     m3, [x+24]

// Load non-trivial digits [n3; -1; n1; -1] = p_sm2 and do a conditional
// subtraction to reduce the four starting digits [m3;m2;m1;m0] modulo p_sm2

        sub     m0, -1
        mov     n1, 0xffffffff00000000
        sbb     m1, n1
        mov     n3, 0xfffffffeffffffff
        sbb     m2, -1
        sbb     m3, n3
        sbb     q, q
        and     n1, q
        and     n3, q
        add     m0, q
        adc     m1, n1
        adc     m2, q
        adc     m3, n3

// Now do 4 iterations of 5->4 word modular reduction

        modstep_sm2(m3,m2,m1,m0)

        mov     m3, q

        modstep_sm2(m2,m1,m0,m3)

        mov     m2, q

        modstep_sm2(m1,m0,m3,m2)

        mov     m1, q

        modstep_sm2(m0,m3,m2,m1)

// Write back result and return

        mov     [z], q
        mov     [z+8], m1
        mov     [z+16], m2
        mov     [z+24], m3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_tomont_sm2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
