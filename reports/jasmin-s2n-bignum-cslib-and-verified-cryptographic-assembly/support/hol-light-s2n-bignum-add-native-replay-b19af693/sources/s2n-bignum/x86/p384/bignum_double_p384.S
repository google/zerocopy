// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Double modulo p_384, z := (2 * x) mod p_384, assuming x reduced
// Input x[6]; output z[6]
//
//    extern void bignum_double_p384(uint64_t z[static 6],
//                                   const uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_double_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_double_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_double_p384)
        .text

#define z rdi
#define x rsi

#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11
#define c rax

// Re-use the input pointer as a temporary once we're done

#define a rsi

#define ashort esi



S2N_BN_SYMBOL(bignum_double_p384):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the input and double it so that 2^384 * c + [d5;d4;d3;d2;d1;d0] = 2 * x
// Could also consider using shld to decouple carries *or* combining this
// and the next block into a double carry chain with ADCX and ADOX.

        xor     c, c
        mov     d0, [x]
        add     d0, d0
        mov     d1, [x+8]
        adc     d1, d1
        mov     d2, [x+16]
        adc     d2, d2
        mov     d3, [x+24]
        adc     d3, d3
        mov     d4, [x+32]
        adc     d4, d4
        mov     d5, [x+40]
        adc     d5, d5
        adc     c, c

// Now subtract p_384 from 2^384 * c + [d5;d4;d3;d2;d1;d0] to get 2 * x - p_384
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

// Since by hypothesis x < p_384 we know 2 * x - p_384 < 2^384, so the top
// carry c actually gives us a bitmask for 2 * x - p_384 < 0, which we
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

S2N_BN_SIZE_DIRECTIVE(bignum_double_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
