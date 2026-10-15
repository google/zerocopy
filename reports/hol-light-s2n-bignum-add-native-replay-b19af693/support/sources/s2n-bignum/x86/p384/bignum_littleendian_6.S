// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert 6-digit (384-bit) bignum to/from little-endian form
// Input x[6]; output z[6]
//
//    extern void bignum_littleendian_6(uint64_t z[static 6],
//                                      const uint64_t x[static 6]);
//
// The same function is given two other prototypes whose names reflect the
// treatment of one or other argument as a byte array rather than word array:
//
//    extern void bignum_fromlebytes_6(uint64_t z[static 6],
//                                     const uint8_t x[static 48]);
//
//    extern void bignum_tolebytes_6(uint8_t z[static 48],
//                                   const uint64_t x[static 6]);
//
// Since x86 is little-endian, this is just copying.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_littleendian_6)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_littleendian_6)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_littleendian_6)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_fromlebytes_6)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_fromlebytes_6)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_fromlebytes_6)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tolebytes_6)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tolebytes_6)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tolebytes_6)

        .text

#define z rdi
#define x rsi
#define a rax

S2N_BN_SYMBOL(bignum_littleendian_6):
S2N_BN_SYMBOL(bignum_fromlebytes_6):
S2N_BN_SYMBOL(bignum_tolebytes_6):
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

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_littleendian_6)
S2N_BN_SIZE_DIRECTIVE(bignum_fromlebytes_6)
S2N_BN_SIZE_DIRECTIVE(bignum_tolebytes_6)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
