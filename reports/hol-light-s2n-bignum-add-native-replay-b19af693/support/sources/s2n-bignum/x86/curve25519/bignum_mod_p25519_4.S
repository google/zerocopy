// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo field characteristic, z := x mod p_25519
// Input x[4]; output z[4]
//
//    extern void bignum_mod_p25519_4(uint64_t z[static 4],
//                                    const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_p25519_4)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mod_p25519_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_p25519_4)
        .text

#define z rdi
#define x rsi

#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9
#define c r10

#define q rax

#define qshort eax
#define cshort r10d

S2N_BN_SYMBOL(bignum_mod_p25519_4):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the inputs as [d3;d2;d1;d0]

        mov     d0, [x]
        mov     d1, [x+8]
        mov     d2, [x+16]
        mov     d3, [x+24]

// Letting x = 2^255 * h + l where h is the top bit, the provisional quotient
// is q = h + 1, which is either correct or 1 too high.

        mov     qshort, 1
        xor     cshort, cshort
        bts     d3, 63
        adc     q, c
        imul    q, 19

// Writing the provisional remainder as r = x - (2^255 - 19) * q we
// compute r' = (2^255 + l) + 19 * q = r + 2^256

        add     d0, q
        adc     d1, c
        adc     d2, c
        adc     d3, c

// Now r < 0 <=> r' < 2^256 <=> ~CF and in this case we correct by adding
// 2^255 - 19, or in fact subtracting 19 and masking to 255 bits.

        mov     qshort, 19
        cmovc   q, c

        sub     d0, q
        sbb     d1, c
        sbb     d2, c
        sbb     d3, c
        btr     d3, 63

// Store the end result

        mov     [z], d0
        mov     [z+8], d1
        mov     [z+16], d2
        mov     [z+24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mod_p25519_4)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
