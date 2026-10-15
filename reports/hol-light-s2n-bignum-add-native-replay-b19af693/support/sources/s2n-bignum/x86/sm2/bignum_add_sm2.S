// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Add modulo p_sm2, z := (x + y) mod p_sm2, assuming x and y reduced
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_add_sm2(uint64_t z[static 4], const uint64_t x[static 4],
//                               const uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_add_sm2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_add_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_add_sm2)
        .text

#define z rdi
#define x rsi
#define y rdx

#define d0 rax
#define d1 rcx
#define d2 r8
#define d3 r9

#define n1 r10
#define n3 rdx
#define c r11

#define n1short r10d



S2N_BN_SYMBOL(bignum_add_sm2):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Load and add the two inputs as 2^256 * c + [d3;d2;d1;d0] = x + y

        xor     c, c
        mov     d0, [x]
        add     d0, [y]
        mov     d1, [x+8]
        adc     d1, [y+8]
        mov     d2, [x+16]
        adc     d2, [y+16]
        mov     d3, [x+24]
        adc     d3, [y+24]
        adc     c, c

// Now subtract 2^256 * c + [d3;d3;d1;d1] = x + y - p_sm2
// The constants n1 and n3 in [n3; 0; n1; -1] = p_sm2 are saved for later

        sub     d0, -1
        mov     n1, 0xffffffff00000000
        sbb     d1, n1
        sbb     d2, -1
        mov     n3, 0xfffffffeffffffff
        sbb     d3, n3

// Since by hypothesis x < p_sm2 we know x + y - p_sm2 < 2^256, so the top
// carry c actually gives us a bitmask for x + y - p_sm2 < 0, which we
// now use to make a masked p_sm2' = [n3; 0; n1; c]

        sbb     c, 0
        and     n1, c
        and     n3, c

// Do the corrective addition and copy to output

        add     d0, c
        mov     [z], d0
        adc     d1, n1
        mov     [z+8], d1
        adc     d2, c
        mov     [z+16], d2
        adc     d3, n3
        mov     [z+24], d3

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_add_sm2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
