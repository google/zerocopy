// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery multiply, z := (x * y / 2^384) mod p_384
// Inputs x[6], y[6]; output z[6]
//
//    extern void bignum_montmul_p384_alt(uint64_t z[static 6],
//                                        const uint64_t x[static 6],
//                                        const uint64_t y[static 6]);
//
// Does z := (2^{-384} * x * y) mod p_384, assuming that the inputs x and y
// satisfy x * y <= 2^384 * p_384 (in particular this is true if we are in
// the "usual" case x < p_384 and y < p_384).
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// -----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montmul_p384_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montmul_p384_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montmul_p384_alt)
        .text

#define z rdi
#define x rsi

// We move the y argument here so we can use rdx for multipliers

#define y rcx

// Some temp registers for the last correction stage

#define d rax
#define u rdx
#define v rcx
#define w rbx

// Add rbx * m into a register-pair (high,low) maintaining consistent
// carry-catching with carry (negated, as bitmask) and using rax and rdx
// as temporaries

#define mulpadd(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rbx;                    \
        sub     rdx, carry;             \
        add     low, rax;               \
        adc     high, rdx;              \
        sbb     carry, carry

// Initial version assuming no carry-in

#define mulpadi(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rbx;                    \
        add     low, rax;               \
        adc     high, rdx;              \
        sbb     carry, carry

// End version not catching the top carry-out

#define mulpade(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rbx;                    \
        sub     rdx, carry;             \
        add     low, rax;               \
        adc     high, rdx

// Core one-step Montgomery reduction macro. Takes input in
// [d7;d6;d5;d4;d3;d2;d1;d0] and returns result in [d7;d6;d5;d4;d3;d2;d1],
// adding to the existing contents, re-using d0 as a temporary internally
//
// We want to add (2^384 - 2^128 - 2^96 + 2^32 - 1) * w
// where w = [d0 + (d0<<32)] mod 2^64
//
//       montredc(d7,d6,d5,d4,d3,d2,d1,d0)
//
// This particular variant, with its mix of addition and subtraction
// at the top, is not intended to maintain a coherent carry or borrow out.
// It is assumed the final result would fit in [d7;d6;d5;d4;d3;d2;d1].
// which is always the case here as the top word is even always in {0,1}

#define montredc(d7,d6,d5,d4,d3,d2,d1,d0)                               \
/* Our correction multiplier is w = [d0 + (d0<<32)] mod 2^64 */         \
        mov     rbx, d0;                                        \
        shl     rbx, 32;                                        \
        add     rbx, d0;                                        \
/* Construct [rbp;rdx;rax;-] = (2^384 - p_384) * w */                   \
/* We know the lowest word will cancel so we can re-use d0 as a temp */ \
        xor     ebp, ebp;                                       \
        mov     rax, 0xffffffff00000001;                        \
        mul     rbx;                                            \
        mov     d0, rdx;                                        \
        mov     rax, 0x00000000ffffffff;                        \
        mul     rbx;                                            \
        add     rax, d0;                                        \
        adc     rdx, rbx;                                       \
        adc     ebp, ebp;                                       \
/*  Now subtract that and add 2^384 * w */                              \
        sub     d1, rax;                                        \
        sbb     d2, rdx;                                        \
        sbb     d3, rbp;                                        \
        sbb     d4, 0;                                          \
        sbb     d5, 0;                                          \
        sbb     rbx, 0;                                         \
        add     d6, rbx;                                        \
        adc     d7, 0

S2N_BN_SYMBOL(bignum_montmul_p384_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save more registers to play with

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Copy y into a safe register to start with

        mov     y, rdx

// Do row 0 computation, which is a bit different:
// set up initial window [r14,r13,r12,r11,r10,r9,r8] = y[0] * x
// Unlike later, we only need a single carry chain

        mov     rbx, [y]
        mov     rax, [x]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx

        mov     rax, [x+8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx

        mov     rax, [x+16]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx

        mov     rax, [x+24]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx

        mov     rax, [x+32]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx

        mov     rax, [x+40]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx

        xor     r15d, r15d

// Montgomery reduce the zeroth window

        montredc(r15, r14,r13,r12,r11,r10,r9,r8)

// Add row 1

        mov     rbx, [y+8]
        mulpadi(r8,r10,r9,[x])
        mulpadd(r8,r11,r10,[x+8])
        mulpadd(r8,r12,r11,[x+16])
        mulpadd(r8,r13,r12,[x+24])
        mulpadd(r8,r14,r13,[x+32])
        mulpadd(r8,r15,r14,[x+40])
        neg     r8

// Montgomery reduce window 1

        montredc(r8, r15,r14,r13,r12,r11,r10,r9)

// Add row 2

        mov     rbx, [y+16]
        mulpadi(r9,r11,r10,[x])
        mulpadd(r9,r12,r11,[x+8])
        mulpadd(r9,r13,r12,[x+16])
        mulpadd(r9,r14,r13,[x+24])
        mulpadd(r9,r15,r14,[x+32])
        mulpadd(r9,r8,r15,[x+40])
        neg     r9

// Montgomery reduce window 2

        montredc(r9, r8,r15,r14,r13,r12,r11,r10)

// Add row 3

        mov     rbx, [y+24]
        mulpadi(r10,r12,r11,[x])
        mulpadd(r10,r13,r12,[x+8])
        mulpadd(r10,r14,r13,[x+16])
        mulpadd(r10,r15,r14,[x+24])
        mulpadd(r10,r8,r15,[x+32])
        mulpadd(r10,r9,r8,[x+40])
        neg     r10

// Montgomery reduce window 3

        montredc(r10, r9,r8,r15,r14,r13,r12,r11)

// Add row 4

        mov     rbx, [y+32]
        mulpadi(r11,r13,r12,[x])
        mulpadd(r11,r14,r13,[x+8])
        mulpadd(r11,r15,r14,[x+16])
        mulpadd(r11,r8,r15,[x+24])
        mulpadd(r11,r9,r8,[x+32])
        mulpadd(r11,r10,r9,[x+40])
        neg     r11

// Montgomery reduce window 4

        montredc(r11, r10,r9,r8,r15,r14,r13,r12)

// Add row 5

        mov     rbx, [y+40]
        mulpadi(r12,r14,r13,[x])
        mulpadd(r12,r15,r14,[x+8])
        mulpadd(r12,r8,r15,[x+16])
        mulpadd(r12,r9,r8,[x+24])
        mulpadd(r12,r10,r9,[x+32])
        mulpadd(r12,r11,r10,[x+40])
        neg     r12

// Montgomery reduce window 5

        montredc(r12, r11,r10,r9,r8,r15,r14,r13)

// We now have a pre-reduced 7-word form z = [r12; r11;r10;r9;r8;r15;r14]
// Next, accumulate in different registers z - p_384, or more precisely
//
//   [r12; r13;rbp;rdx;rcx;rbx;rax] = z + (2^384 - p_384)

        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d

        mov     rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0x00000000ffffffff
        adc     rbx, r15
        mov     ecx, 0x0000000000000001
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0

// ~ZF <=> r12 >= 1 <=> z + (2^384 - p_384) >= 2^384 <=> z >= p_384, which
// determines whether to use the further reduced argument or the original z.

        cmovnz  r14, rax
        cmovnz  r15, rbx
        cmovnz  r8, rcx
        cmovnz  r9, rdx
        cmovnz  r10, rbp
        cmovnz  r11, r13

// Write back the result

        mov     [z], r14
        mov     [z+8], r15
        mov     [z+16], r8
        mov     [z+24], r9
        mov     [z+32], r10
        mov     [z+40], r11

// Restore registers and return

        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_montmul_p384_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
