// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert 9-digit 528-bit bignum to little-endian bytes
//
//    extern void bignum_tolebytes_p521(uint8_t z[static 66],
//                                      const uint64_t x[static 9]);
//
// This is assuming the input x is < 2^528 so that it fits in 66 bytes.
// In particular this holds if x < p_521 < 2^521 < 2^528.
//
// Since x86 is little-endian, this is just copying.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tolebytes_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tolebytes_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tolebytes_p521)
        .text

#define z rdi
#define x rsi
#define a rax

S2N_BN_SYMBOL(bignum_tolebytes_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

        mov     a, [x]
        mov     [z], a

        mov     a, [x+8]
        mov     [z+8], a

        mov     a, [x+16]
        mov     [z+16], a

        mov     a, [x+24]
        mov     [z+24], a

        mov     a, [x+32]
        mov     [z+32], a

        mov     a, [x+40]
        mov     [z+40], a

        mov     a, [x+48]
        mov     [z+48], a

        mov     a, [x+56]
        mov     [z+56], a

        mov     a, [x+64]
        mov     [z+64], ax

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_tolebytes_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
