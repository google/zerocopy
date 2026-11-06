// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert to Montgomery form z := (2^384 * x) mod p_384
// Input x[6]; output z[6]
//
//    extern void bignum_tomont_p384(uint64_t z[static 6],
//                                   const uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tomont_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_p384)
        .text

#define z rdi
#define x rsi

// Fairly consistently used as a zero register

#define zero rbp

// Some temp registers for the last correction stage

#define d rax
#define u rdx
#define v rcx
#define w rsi

#define vshort ecx
#define wshort esi

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rcx as temporaries

#define mulpadd(high,low,m)             \
        mulx    rcx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rcx

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
        mov     rdx, d0;                                        \
        shl     rdx, 32;                                        \
        add     rdx, d0;                                        \
/* Construct [rbp;rcx;rax;-] = (2^384 - p_384) * w */                   \
/* We know the lowest word will cancel so we can re-use d0 as a temp */ \
        xor     ebp, ebp;                                       \
        mov     rax, 0xffffffff00000001;                        \
        mulx    rax, rcx, rax;                                  \
        mov     ecx, 0x00000000ffffffff;                        \
        mulx    rcx, d0, rcx;                                   \
        adc     rax, d0;                                        \
        adc     rcx, rdx;                                       \
        adc     ebp, ebp;                                       \
/*  Now subtract that and add 2^384 * w */                              \
        sub     d1, rax;                                        \
        sbb     d2, rcx;                                        \
        sbb     d3, rbp;                                        \
        sbb     d4, 0;                                          \
        sbb     d5, 0;                                          \
        sbb     rdx, 0;                                         \
        add     d6, rdx;                                        \
        adc     d7, 0

S2N_BN_SYMBOL(bignum_tomont_p384):
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

        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Do row 0 computation, which is a bit different:
// set up initial window [r14,r13,r12,r11,r10,r9,r8] = y[0] * x
// Unlike later, we only need a single carry chain

        mov     rdx, 0xfffffffe00000001
        mulx    r9, r8, [x]
        mulx    r10, rcx, [x+8]
        add     r9, rcx
        mulx    r11, rcx, [x+16]
        adc     r10, rcx
        mulx    r12, rcx, [x+24]
        adc     r11, rcx
        mulx    r13, rcx, [x+32]
        adc     r12, rcx
        mulx    r14, rcx, [x+40]
        adc     r13, rcx
        adc     r14, 0

// Montgomery reduce the zeroth window

        xor     r15, r15
        montredc(r15, r14,r13,r12,r11,r10,r9,r8)

// Add row 1

        xor     zero, zero
        mov     rdx, 0x0000000200000000
        xor     r8, r8
        mulpadd(r10,r9,[x])
        mulpadd(r11,r10,[x+8])
        mulpadd(r12,r11,[x+16])
        mulpadd(r13,r12,[x+24])
        mulpadd(r14,r13,[x+32])
        mulpadd(r15,r14,[x+40])
        adcx    r15, zero
        adox    r8, zero
        adcx    r8, zero

// Montgomery reduce window 1

        montredc(r8, r15,r14,r13,r12,r11,r10,r9)

// Add row 2

        xor     zero, zero
        mov     rdx, 0xfffffffe00000000
        xor     r9, r9
        mulpadd(r11,r10,[x])
        mulpadd(r12,r11,[x+8])
        mulpadd(r13,r12,[x+16])
        mulpadd(r14,r13,[x+24])
        mulpadd(r15,r14,[x+32])
        mulpadd(r8,r15,[x+40])
        adcx    r8, zero
        adox    r9, zero
        adcx    r9, zero

// Montgomery reduce window 2

        montredc(r9, r8,r15,r14,r13,r12,r11,r10)

// Add row 3

        xor     zero, zero
        mov     rdx, 0x0000000200000000
        xor     r10, r10
        mulpadd(r12,r11,[x])
        mulpadd(r13,r12,[x+8])
        mulpadd(r14,r13,[x+16])
        mulpadd(r15,r14,[x+24])
        mulpadd(r8,r15,[x+32])
        mulpadd(r9,r8,[x+40])
        adcx    r9, zero
        adox    r10, zero
        adcx    r10, zero

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
        adc     r10, 0
        adc     r11, 0

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
        CFI_POP(rbp)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_tomont_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
