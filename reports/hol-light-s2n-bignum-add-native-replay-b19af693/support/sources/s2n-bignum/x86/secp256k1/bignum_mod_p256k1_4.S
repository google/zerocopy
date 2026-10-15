// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo field characteristic, z := x mod p_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_mod_p256k1_4(uint64_t z[static 4],
//                                    const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_p256k1_4)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_p256k1_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_p256k1_4)
        .text

#define z rdi
#define x rsi

#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9
#define c r10

#define d rax


S2N_BN_SYMBOL(bignum_mod_p256k1_4):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the inputs as [d3;d2;d1;d0] and let d be an AND of [d3;d2;d1] to
// condense the comparison below.

        mov     d0, [x]
        mov     d1, [x+8]
        mov     d, d1
        mov     d2, [x+16]
        and     d, d2
        mov     d3, [x+24]
        and     d, d3

// Compare x >= p_256k1 = 2^256 - 4294968273 using condensed carry:
// we get a carry from the lowest digit and all other digits are 1.
// We end up with c and d as adjusted digits for x - p_256k1 if so.

        mov     c, 4294968273
        add     c, d0
        adc     d, 0

// If indeed x >= p_256k1 then x := x - p_256k1, using c and d
// Either way, write back to z

        cmovc   d0, c
        mov     [z], d0
        cmovc   d1, d
        mov     [z+8], d1
        cmovc   d2, d
        mov     [z+16], d2
        cmovc   d3, d
        mov     [z+24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod_p256k1_4)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
