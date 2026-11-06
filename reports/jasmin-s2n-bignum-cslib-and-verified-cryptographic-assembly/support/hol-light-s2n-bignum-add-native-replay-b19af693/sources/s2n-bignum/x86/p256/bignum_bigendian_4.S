// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert 4-digit (256-bit) bignum to/from big-endian form
// Input x[4]; output z[4]
//
//    extern void bignum_bigendian_4(uint64_t z[static 4],
//                                   const uint64_t x[static 4]);
//
// The same function is given two other prototypes whose names reflect the
// treatment of one or other argument as a byte array rather than word array:
//
//    extern void bignum_frombebytes_4(uint64_t z[static 4],
//                                     const uint8_t x[static 32]);
//
//    extern void bignum_tobebytes_4(uint8_t z[static 32],
//                                   const uint64_t x[static 4]);
//
// Since x86 is little-endian, and bignums are stored with little-endian
// word order, this is simply byte reversal and is implemented as such.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_bigendian_4)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_bigendian_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_bigendian_4)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_frombebytes_4)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_frombebytes_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_frombebytes_4)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tobebytes_4)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tobebytes_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tobebytes_4)

        .text

#define z rdi
#define x rsi
#define a rax
#define b rdx

// All loads and stores are word-sized, then we use BSWAP to
// reverse the byte order, as well as switching round the word order
// when writing back. The reads and writes are organized in mirror-image
// pairs (0-3 and 1-2) to allow x and z to point to the same buffer
// without using more intermediate registers.

S2N_BN_SYMBOL(bignum_bigendian_4):
S2N_BN_SYMBOL(bignum_frombebytes_4):
S2N_BN_SYMBOL(bignum_tobebytes_4):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// 0 and 3 words

        mov     a, [x]
        mov     b, [x+24]
        bswap   a
        bswap   b
        mov     [z+24], a
        mov     [z], b

// 1 and 2 words

        mov     a, [x+8]
        mov     b, [x+16]
        bswap   a
        bswap   b
        mov     [z+16], a
        mov     [z+8], b

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_bigendian_4)
S2N_BN_SIZE_DIRECTIVE(bignum_frombebytes_4)
S2N_BN_SIZE_DIRECTIVE(bignum_tobebytes_4)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
