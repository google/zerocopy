// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply by a single word modulo p_521, z := (c * x) mod p_521, assuming
// x reduced
// Inputs c, x[9]; output z[9]
//
//    extern void bignum_cmul_p521(uint64_t z[static 9], uint64_t c,
//                                 const uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = c, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cmul_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cmul_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cmul_p521)
        .text

#define z rdi

// Temporarily moved here for initial multiply

#define x rcx

// Likewise this is thrown away after initial multiply

#define c rdx
#define cshort edx

#define a rax
#define dd rax

// Digits: last one aliased to the local x pointer that's no longer needed

#define d0 rsi
#define d1 r8
#define d2 r9
#define d3 r10
#define d4 r11
#define d5 rbx
#define d6 rbp
#define d7 r12
#define d8 r13
#define d9 rcx

// Same as d9

#define h d9

S2N_BN_SYMBOL(bignum_cmul_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save additional registers to use

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)

// Shuffle inputs (since we want the multiplier in rdx)

        mov     x, rdx
        mov     c, rsi

// Multiply as [d9; ...; d0] = c * x.

        mulx    d1, d0, [x]
        mulx    d2, a, [x+8]
        add     d1, a
        mulx    d3, a, [x+16]
        adc     d2, a
        mulx    d4, a, [x+24]
        adc     d3, a
        mulx    d5, a, [x+32]
        adc     d4, a
        mulx    d6, a, [x+40]
        adc     d5, a
        mulx    d7, a, [x+48]
        adc     d6, a
        mulx    d8, a, [x+56]
        adc     d7, a
        mulx    d9, a, [x+64]
        adc     d8, a
        adc     d9, 0

// Create an AND "dd" of digits d7,...,d1, a computation we hope will
// get nicely interleaved with the multiplication chain above.
// From the point of view of architectural dependencies we have to
// bunch it up here since AND destroys the flags and we overwrite the
// register used as a stage temporary variable for the multiplications.

        mov     dd, d1
        and     dd, d2
        and     dd, d3
        and     dd, d4
        and     dd, d5
        and     dd, d6
        and     dd, d7

// Extract the high part h==d9 and mask off the low part l = [d8;d7;...;d0]
// but stuff d8 with 1 bits at the left to ease a comparison below

        shld    h, d8, 55
        or      d8, ~0x1FF

// Decide whether h + l >= p_521 <=> h + l + 1 >= 2^521. Since this can only
// happen if digits d7,...d1 are all 1s, we use the AND of them "dd" to
// condense the carry chain, and since we stuffed 1 bits into d8 we get
// the result in CF without an additional comparison. Hereafter we use c = 0.
// Since x was assumed reduced, h cannot be maximal, so the "lea" is safe,
// i.e. does not carry or wrap round.

        lea     c, [h+1]
        add     c, d0
        mov     cshort, 0
        adc     dd, c
        mov     a, d8
        adc     a, c

// Now if CF is set we want (h + l) - p_521 = (h + l + 1) - 2^521
// while otherwise we want just h + l. So mask h + l + CF to 521 bits.
// This masking also gets rid of the stuffing with 1s we did above.
// Write back the digits as they are generated.

        adc     d0, h
        mov     [z], d0
        adc     d1, c
        mov     [z+8], d1
        adc     d2, c
        mov     [z+16], d2
        adc     d3, c
        mov     [z+24], d3
        adc     d4, c
        mov     [z+32], d4
        adc     d5, c
        mov     [z+40], d5
        adc     d6, c
        mov     [z+48], d6
        adc     d7, c
        mov     [z+56], d7
        adc     d8, c
        and     d8, 0x1FF
        mov     [z+64], d8

// Restore registers and return

        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_cmul_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
