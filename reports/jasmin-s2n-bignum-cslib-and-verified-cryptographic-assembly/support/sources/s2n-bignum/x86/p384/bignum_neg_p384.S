// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Negate modulo p_384, z := (-x) mod p_384, assuming x reduced
// Input x[6]; output z[6]
//
//    extern void bignum_neg_p384(uint64_t z[static 6], const uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_neg_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_neg_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_neg_p384)
        .text

#define z rdi
#define x rsi

#define n0 rax
#define n1 rcx
#define n2 rdx
#define n3 r8
#define n4 r9
#define q r10

#define n0short eax

S2N_BN_SYMBOL(bignum_neg_p384):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Or together the input digits and create a bitmask q if this is nonzero, so
// that we avoid doing -0 = p_384 and hence maintain strict modular reduction

        mov     n0, [x]
        or      n0, [x+8]
        mov     n1, [x+16]
        or      n1, [x+24]
        mov     n2, [x+32]
        or      n2, [x+40]
        or      n0, n1
        or      n0, n2
        neg     n0
        sbb     q, q

// Let [q;n4;n3;n2;n1;n0] = if q then p_384 else 0

        mov     n0short, 0x00000000ffffffff
        and     n0, q
        mov     n1, 0xffffffff00000000
        and     n1, q
        mov     n2, 0xfffffffffffffffe
        and     n2, q
        mov     n3, q
        mov     n4, q

// Do the subtraction

        sub     n0, [x]
        sbb     n1, [x+8]
        sbb     n2, [x+16]
        sbb     n3, [x+24]
        sbb     n4, [x+32]
        sbb     q, [x+40]

// Write back

        mov     [z], n0
        mov     [z+8], n1
        mov     [z+16], n2
        mov     [z+24], n3
        mov     [z+32], n4
        mov     [z+40], q

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_neg_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
