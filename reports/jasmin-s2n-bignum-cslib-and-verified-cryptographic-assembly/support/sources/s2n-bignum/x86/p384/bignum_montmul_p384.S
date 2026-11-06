// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery multiply, z := (x * y / 2^384) mod p_384
// Inputs x[6], y[6]; output z[6]
//
//    extern void bignum_montmul_p384(uint64_t z[static 6],
//                                    const uint64_t x[static 6],
//                                    const uint64_t y[static 6]);
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
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montmul_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montmul_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montmul_p384)
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

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rbx as temporaries

#define mulpadd(high,low,m)             \
        mulx    rbx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rbx

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
/* Construct [rbp;rbx;rax;-] = (2^384 - p_384) * w */                   \
/* We know the lowest word will cancel so we can re-use d0 as a temp */ \
        xor     ebp, ebp;                                       \
        mov     rax, 0xffffffff00000001;                        \
        mulx    rax, rbx, rax;                                  \
        mov     ebx, 0x00000000ffffffff;                        \
        mulx    rbx, d0, rbx;                                   \
        adc     rax, d0;                                        \
        adc     rbx, rdx;                                       \
        adc     ebp, ebp;                                       \
/*  Now subtract that and add 2^384 * w */                              \
        sub     d1, rax;                                        \
        sbb     d2, rbx;                                        \
        sbb     d3, rbp;                                        \
        sbb     d4, 0;                                          \
        sbb     d5, 0;                                          \
        sbb     rdx, 0;                                         \
        add     d6, rdx;                                        \
        adc     d7, 0

S2N_BN_SYMBOL(bignum_montmul_p384):
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

        mov     rdx, [y]
        xor     r15d, r15d
        mulx    r9, r8, [x]
        mulx    r10, rbx, [x+8]
        add     r9, rbx
        mulx    r11, rbx, [x+16]
        adc     r10, rbx
        mulx    r12, rbx, [x+24]
        adc     r11, rbx
        mulx    r13, rbx, [x+32]
        adc     r12, rbx
        mulx    r14, rbx, [x+40]
        adc     r13, rbx
        adc     r14, r15

// Montgomery reduce the zeroth window

        montredc(r15, r14,r13,r12,r11,r10,r9,r8)

// Add row 1

        mov     rdx, [y+8]
        xor     r8d, r8d
        mulpadd(r10,r9,[x])
        mulpadd(r11,r10, [x+8])
        mulpadd(r12,r11,[x+16])
        mulpadd(r13,r12,[x+24])
        mulpadd(r14,r13,[x+32])
        adox    r15, r8
        mulx    rbx, rax, [x+40]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r8

// Montgomery reduce window 1

        montredc(r8, r15,r14,r13,r12,r11,r10,r9)

// Add row 2

        mov     rdx, [y+16]
        xor     r9d, r9d
        mulpadd(r11,r10,[x])
        mulpadd(r12,r11,[x+8])
        mulpadd(r13,r12,[x+16])
        mulpadd(r14,r13,[x+24])
        mulpadd(r15,r14,[x+32])
        adox    r8, r9
        mulx    rbx, rax, [x+40]
        adc     r15, rax
        adc     r8, rbx
        adc     r9, r9

// Montgomery reduce window 2

        montredc(r9, r8,r15,r14,r13,r12,r11,r10)

// Add row 3

        mov     rdx, [y+24]
        xor     r10d, r10d
        mulpadd(r12,r11,[x])
        mulpadd(r13,r12,[x+8])
        mulpadd(r14,r13,[x+16])
        mulpadd(r15,r14,[x+24])
        mulpadd(r8,r15,[x+32])
        adox    r9, r10
        mulx    rbx, rax, [x+40]
        adc     r8, rax
        adc     r9, rbx
        adc     r10, r10

// Montgomery reduce window 3

        montredc(r10, r9,r8,r15,r14,r13,r12,r11)

// Add row 4

        mov     rdx, [y+32]
        xor     r11d, r11d
        mulpadd(r13,r12,[x])
        mulpadd(r14,r13,[x+8])
        mulpadd(r15,r14,[x+16])
        mulpadd(r8,r15,[x+24])
        mulpadd(r9,r8,[x+32])
        adox    r10, r11
        mulx    rbx, rax, [x+40]
        adc     r9, rax
        adc     r10, rbx
        adc     r11, r11

// Montgomery reduce window 4

        montredc(r11, r10,r9,r8,r15,r14,r13,r12)

// Add row 5

        mov     rdx, [y+40]
        xor     r12d, r12d
        mulpadd(r14,r13,[x])
        mulpadd(r15,r14,[x+8])
        mulpadd(r8,r15,[x+16])
        mulpadd(r9,r8,[x+24])
        mulpadd(r10,r9,[x+32])
        adox    r11, r12
        mulx    rbx, rax, [x+40]
        adc     r10, rax
        adc     r11, rbx
        adc     r12, r12

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

S2N_BN_SIZE_DIRECTIVE(bignum_montmul_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
