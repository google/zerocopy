// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert to Montgomery form z := (2^384 * x) mod p_384
// Input x[6]; output z[6]
//
//    extern void bignum_tomont_p384_alt(uint64_t z[static 6],
//                                       const uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_p384_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tomont_p384_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_p384_alt)
        .text

#define z rdi
#define x rsi

// Some temp registers for the last correction stage

#define d rax
#define u rdx
#define v rcx
#define w rsi

#define vshort ecx
#define wshort esi

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
/* Construct [rcx;rdx;rax;-] = (2^384 - p_384) * w */                   \
/* We know the lowest word will cancel so we can re-use d0 as a temp */ \
        xor     ecx, ecx;                                       \
        mov     rax, 0xffffffff00000001;                        \
        mul     rbx;                                            \
        mov     d0, rdx;                                        \
        mov     rax, 0x00000000ffffffff;                        \
        mul     rbx;                                            \
        add     rax, d0;                                        \
        adc     rdx, rbx;                                       \
        adc     ecx, ecx;                                       \
/*  Now subtract that and add 2^384 * w */                              \
        sub     d1, rax;                                        \
        sbb     d2, rdx;                                        \
        sbb     d3, rcx;                                        \
        sbb     d4, 0;                                          \
        sbb     d5, 0;                                          \
        sbb     rbx, 0;                                         \
        add     d6, rbx;                                        \
        adc     d7, 0

S2N_BN_SYMBOL(bignum_tomont_p384_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// We are essentially just doing a Montgomery multiplication of x and the
// precomputed constant y = 2^768 mod p, so the code is almost the same
// modulo a few registers and the change from loading y[i] to using constants,
// plus the easy digits y[4] = 1 and y[5] = 0 being treated specially.
// Because there is no y pointer to keep, we use one register less.

        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Do row 0 computation, which is a bit different:
// set up initial window [r14,r13,r12,r11,r10,r9,r8] = y[0] * x
// Unlike later, we only need a single carry chain

        mov     rbx, 0xfffffffe00000001
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

        mov     rbx, 0x0000000200000000
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

        mov     rbx, 0xfffffffe00000000
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

        mov     rbx, 0x0000000200000000
        mulpadi(r10,r12,r11,[x])
        mulpadd(r10,r13,r12,[x+8])
        mulpadd(r10,r14,r13,[x+16])
        mulpadd(r10,r15,r14,[x+24])
        mulpadd(r10,r8,r15,[x+32])
        mulpadd(r10,r9,r8,[x+40])
        neg     r10

// Montgomery reduce window 3

        montredc(r10, r9,r8,r15,r14,r13,r12,r11)

// Add row 4. The multiplier y[4] = 1, so we just add x to the window
// while extending it with one more digit, initially this carry

        xor     r11, r11
        add     r12, [x]
        adc     r13, [x+8]
        adc     r14, [x+16]
        adc     r15, [x+24]
        adc     r8, [x+32]
        adc     r9, [x+40]
        adc     r10, r11
        adc     r11, r11

// Montgomery reduce window 4

        montredc(r11, r10,r9,r8,r15,r14,r13,r12)

// Add row 5, The multiplier y[5] = 0, so this is trivial: all we do is
// bring down another zero digit into the window.

        xor     r12, r12

// Montgomery reduce window 5

        montredc(r12, r11,r10,r9,r8,r15,r14,r13)

// We now have a pre-reduced 7-word form [r12;r11;r10;r9;r8;r15;r14]

// We know, writing B = 2^{6*64} that the full implicit result is
// B^2 c <= z + (B - 1) * p < B * p + (B - 1) * p < 2 * B * p,
// so the top half is certainly < 2 * p. If c = 1 already, we know
// subtracting p will give the reduced modulus. But now we do a
// comparison to catch cases where the residue is >= p.
// First set [0;0;0;w;v;u] = 2^384 - p_384

        mov     u, 0xffffffff00000001
        mov     vshort, 0x00000000ffffffff
        mov     wshort, 0x0000000000000001

// Let dd = [r11;r10;r9;r8;r15;r14] be the topless 6-word intermediate result.
// Set CF if the addition dd + (2^384 - p_384) >= 2^384, hence iff dd >= p_384.

        mov     d, r14
        add     d, u
        mov     d, r15
        adc     d, v
        mov     d, r8
        adc     d, w
        mov     d, r9
        adc     d, 0
        mov     d, r10
        adc     d, 0
        mov     d, r11
        adc     d, 0

// Now just add this new carry into the existing r12. It's easy to see they
// can't both be 1 by our range assumptions, so this gives us a {0,1} flag

        adc     r12, 0

// Now convert it into a bitmask

        neg     r12

// Masked addition of 2^384 - p_384, hence subtraction of p_384

        and     u, r12
        and     v, r12
        and     w, r12

        add    r14, u
        adc    r15, v
        adc    r8, w
        adc    r9, 0
        adc    r10, 0
        adc    r11, 0

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
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_tomont_p384_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
