// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery square, z := (x^2 / 2^384) mod p_384
// Input x[6]; output z[6]
//
//    extern void bignum_montsqr_p384_alt(uint64_t z[static 6],
//                                        const uint64_t x[static 6]);
//
// Does z := (x^2 / 2^384) mod p_384, assuming x^2 <= 2^384 * p_384, which is
// guaranteed in particular if x < p_384 initially (the "intended" case).
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montsqr_p384_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montsqr_p384_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montsqr_p384_alt)
        .text

#define z rdi
#define x rsi

// Some temp registers for the last correction stage

#define d rax
#define u rdx
#define v r10
#define w r11

// A zero register, very often

#define zero rbp
#define zeroe ebp

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

// Core one-step "short" Montgomery reduction macro. Takes input in
// [d5;d4;d3;d2;d1;d0] and returns result in [d6;d5;d4;d3;d2;d1],
// adding to the existing [d5;d4;d3;d2;d1] and re-using d0 as a
// temporary internally, as well as rax, rbx and rdx.
// It is OK for d6 and d0 to be the same register (they often are)
//
// We want to add (2^384 - 2^128 - 2^96 + 2^32 - 1) * w
// where w = [d0 + (d0<<32)] mod 2^64
//
//       montreds(d6,d5,d4,d3,d2,d1,d0)

#define montreds(d6,d5,d4,d3,d2,d1,d0)                                  \
/* Our correction multiplier is w = [d0 + (d0<<32)] mod 2^64 */         \
        mov     rbx, d0;                                        \
        shl     rbx, 32;                                        \
        add     rbx, d0;                                        \
/* Construct [rax;rdx;d0;-] = (2^384 - p_384) * w            */         \
/* We know the lowest word will cancel so we can re-use d0   */         \
/* and rbx as temps.                                         */         \
        mov     rax, 0xffffffff00000001;                        \
        mul     rbx;                                            \
        mov     d0, rdx;                                        \
        mov     rax, 0x00000000ffffffff;                        \
        mul     rbx;                                            \
        add     d0, rax;                                        \
        mov     eax, 0;                                         \
        adc     rdx, rbx;                                       \
        adc     eax, eax;                                       \
/* Now subtract that and add 2^384 * w                       */         \
        sub     d1, d0;                                         \
        sbb     d2, rdx;                                        \
        sbb     d3, rax;                                        \
        sbb     d4, 0;                                          \
        sbb     d5, 0;                                          \
        mov     d6, rbx;                                        \
        sbb     d6, 0

S2N_BN_SYMBOL(bignum_montsqr_p384_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save more registers to play with

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Set up an initial window [rcx;r15;...r9] = [34;05;03;01]
// Note that we are using rcx as the first step past the rotating window

        mov     rbx, [x]
        mov     rax, [x+8]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx

        mov     rax, [x+24]
        mul     rbx
        mov     r11, rax
        mov     r12, rdx

        mov     rax, [x+40]
        mul     rbx
        mov     r13, rax
        mov     r14, rdx

        mov     rax, [x+24]
        mul     QWORD PTR [x+32]
        mov     r15, rax
        mov     rcx, rdx

// Chain in the addition of 02 + 12 + 13 + 14 + 15 to that window
// (no carry-out possible)

        mov     rbx, [x+16]
        mulpadi(rbp,r11,r10,[x])
        mulpadd(rbp,r12,r11,[x+8])
        mov     rbx, [x+8]
        mulpadd(rbp,r13,r12,[x+24])
        mulpadd(rbp,r14,r13,[x+32])
        mulpade(rbp,r15,r14,[x+40])
        adc     rcx, 0

// Now chain in the 04 + 23 + 24 + 25 + 35 + 45 terms
// We are running out of registers in our rotating window, so we start
// using rbx (and hence need care with using mulpadd after this). Thus
// our result so far is in [rbp;rbx;rcx;r15;...r9]

        mov     rbx, [x+32]
        mulpadi(rbp,r13,r12,[x])
        mov     rbx, [x+16]
        mulpadd(rbp,r14,r13,[x+24])
        mulpadd(rbp,r15,r14,[x+32])
        mulpadd(rbp,rcx,r15,[x+40])

        xor     ebx, ebx
        mov     rax, [x+24]
        mul     QWORD PTR [x+40]
        sub     rdx, rbp
        xor     ebp, ebp
        add     rcx, rax
        adc     rbx, rdx
        adc     ebp, ebp
        mov     rax, [x+32]
        mul     QWORD PTR [x+40]
        add     rbx, rax
        adc     rbp, rdx

// Double the window as [r8;rbp;rbx;rcx;r15;...r9]

        xor     r8d, r8d
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     r15, r15
        adc     rcx, rcx
        adc     rbx, rbx
        adc     rbp, rbp
        adc     r8d, r8d

// Add the doubled window to the 00 + 11 + 22 + 33 + 44 + 55 terms
// For one glorious moment the entire squaring result is all in the
// register file as [rsi;rbp;rbx;rcx;r15;...;r8]
// (since we've now finished with x we can re-use rsi). But since
// we are so close to running out of registers, we do a bit of
// reshuffling and temporary storage in the output buffer.

        mov     rax, [x]
        mul     rax
        mov     [z], r8
        mov     r8, rax
        mov     rax, [x+8]
        mov     [z+8], rbp
        add     r9, rdx
        sbb     rbp, rbp

        mul     rax
        neg     rbp
        adc     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp

        mov     rax, [x+16]
        mul     rax
        neg     rbp
        adc     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp

        mov     rax, [x+24]
        mul     rax
        neg     rbp
        adc     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp

        mov     rax, [x+32]
        mul     rax
        neg     rbp
        adc     rcx, rax
        adc     rbx, rdx
        sbb     rbp, rbp

        mov     rax, [x+40]
        mul     rax
        neg     rbp
        adc     rax, [z+8]
        adc     rdx, [z]
        mov     rbp, rax
        mov     rsi, rdx

// We need just *one* more register as a temp for the Montgomery steps.
// Since we are writing to the z buffer anyway, make use of that again
// to stash rbx.

        mov     [z], rbx

// Montgomery reduce the r13,...,r8 window 6 times

        montreds(r8,r13,r12,r11,r10,r9,r8)
        montreds(r9,r8,r13,r12,r11,r10,r9)
        montreds(r10,r9,r8,r13,r12,r11,r10)
        montreds(r11,r10,r9,r8,r13,r12,r11)
        montreds(r12,r11,r10,r9,r8,r13,r12)
        montreds(r13,r12,r11,r10,r9,r8,r13)

// Now we can safely restore rbx before accumulating

        mov     rbx, [z]

        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rsi, r13
        mov     r8d, 0
        adc     r8, r8

// We now have a pre-reduced 7-word form z = [r8; rsi;rbp;rbx;rcx;r15;r14]
// Next, accumulate in different registers z - p_384, or more precisely
//
//   [r8; r13;r12;r11;r10;r9;rax] = z + (2^384 - p_384)

        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        mov     rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0x00000000ffffffff
        adc     r9, r15
        mov     r10d, 0x0000000000000001
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rsi
        adc     r8, 0

// ~ZF <=> r12 >= 1 <=> z + (2^384 - p_384) >= 2^384 <=> z >= p_384, which
// determines whether to use the further reduced argument or the original z.

        cmovnz  r14, rax
        cmovnz  r15, r9
        cmovnz  rcx, r10
        cmovnz  rbx, r11
        cmovnz  rbp, r12
        cmovnz  rsi, r13

// Write back the result

        mov     [z], r14
        mov     [z+8], r15
        mov     [z+16], rcx
        mov     [z+24], rbx
        mov     [z+32], rbp
        mov     [z+40], rsi

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

S2N_BN_SIZE_DIRECTIVE(bignum_montsqr_p384_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
