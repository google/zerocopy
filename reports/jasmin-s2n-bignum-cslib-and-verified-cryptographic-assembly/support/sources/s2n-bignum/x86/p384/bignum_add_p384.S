// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Add modulo p_384, z := (x + y) mod p_384, assuming x and y reduced
// Inputs x[6], y[6]; output z[6]
//
//    extern void bignum_add_p384(uint64_t z[static 6], const uint64_t x[static 6],
//                                const uint64_t y[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_add_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_add_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_add_p384)
        .text

#define z rdi
#define x rsi
#define y rdx

#define d0 rax
#define d1 rcx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11

// Re-use the input pointers as temporaries once we're done

#define a rsi
#define c rdx

#define ashort esi
#define cshort edx



S2N_BN_SYMBOL(bignum_add_p384):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Add the inputs as 2^384 * c + [d5;d4;d3;d2;d1;d0] = x + y
// This could be combined with the next block using ADCX and ADOX.

        mov     d0, [x]
        add     d0, [y]
        mov     d1, [x+8]
        adc     d1, [y+8]
        mov     d2, [x+16]
        adc     d2, [y+16]
        mov     d3, [x+24]
        adc     d3, [y+24]
        mov     d4, [x+32]
        adc     d4, [y+32]
        mov     d5, [x+40]
        adc     d5, [y+40]
        mov     cshort, 0
        adc     c, c

// Now subtract p_384 from 2^384 * c + [d5;d4;d3;d2;d1;d0] to get x + y - p_384
// This is actually done by *adding* the 7-word negation r_384 = 2^448 - p_384
// where r_384 = [-1; 0; 0; 0; 1; 0x00000000ffffffff; 0xffffffff00000001]

        mov     a, 0xffffffff00000001
        add     d0, a
        mov     ashort, 0x00000000ffffffff
        adc     d1, a
        adc     d2, 1
        adc     d3, 0
        adc     d4, 0
        adc     d5, 0
        adc     c, -1

// Since by hypothesis x < p_384 we know x + y - p_384 < 2^384, so the top
// carry c actually gives us a bitmask for x + y - p_384 < 0, which we
// now use to make r' = mask * (2^384 - p_384) for a compensating subtraction.
// We don't quite have enough ABI-modifiable registers to create all three
// nonzero digits of r while maintaining d0..d5, but make the first two now.

        and     c, a                    // c = masked 0x00000000ffffffff
        xor     a, a
        sub     a, c                    // a = masked 0xffffffff00000001

// Do the first two digits of addition and writeback

        sub     d0, a
        mov     [z], d0
        sbb     d1, c
        mov     [z+8], d1

// Preserve the carry chain while creating the extra masked digit since
// the logical operation will clear CF

        sbb     d0, d0
        and     c, a                    // c = masked 0x0000000000000001
        neg     d0

// Do the rest of the addition and writeback

        sbb     d2, c
        mov     [z+16], d2
        sbb     d3, 0
        mov     [z+24], d3
        sbb     d4, 0
        mov     [z+32], d4
        sbb     d5, 0
        mov     [z+40], d5

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_add_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
