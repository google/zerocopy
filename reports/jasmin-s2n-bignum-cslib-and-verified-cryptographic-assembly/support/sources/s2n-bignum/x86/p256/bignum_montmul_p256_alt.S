// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery multiply, z := (x * y / 2^256) mod p_256
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_montmul_p256_alt(uint64_t z[static 4],
//                                        const uint64_t x[static 4],
//                                        const uint64_t y[static 4]);
//
// Does z := (2^{-256} * x * y) mod p_256, assuming that the inputs x and y
// satisfy x * y <= 2^256 * p_256 (in particular this is true if we are in
// the "usual" case x < p_256 and y < p_256).
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montmul_p256_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montmul_p256_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montmul_p256_alt)
        .text

#define z rdi
#define x rsi

// We move the y argument here so we can use rdx for multipliers

#define y rcx

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

S2N_BN_SYMBOL(bignum_montmul_p256_alt):
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
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Copy y into a safe register to start with

        mov     y, rdx

// Do row 0 computation, which is a bit different:
// set up initial window [r12,r11,r10,r9,r8] = y[0] * x
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

// Add row 1

        mov     rbx, [y+8]
        xor     r13d, r13d
        mulpadi(r14,r10,r9,[x])
        mulpadd(r14,r11,r10,[x+8])
        mulpadd(r14,r12,r11,[x+16])
        mulpade(r14,r13,r12,[x+24])

// Montgomery reduce windows 0 and 1 together

        xor     r14d, r14d
        mov     rbx, 0x0000000100000000
        mulpadi(r15,r10,r9,r8)
        mulpadd(r15,r11,r10,r9)
        not     rbx
        lea     rbx, [rbx+2]
        mulpadd(r15,r12,r11,r8)
        mulpade(r15,r13,r12,r9)
        adc     r14, r14

// Add row 2

        mov     rbx, [y+16]
        xor     r15d, r15d
        mulpadi(r8,r11,r10,[x])
        mulpadd(r8,r12,r11,[x+8])
        mulpadd(r8,r13,r12,[x+16])
        mulpade(r8,r14,r13,[x+24])
        adc     r15, r15

// Add row 3

        mov     rbx, [y+24]
        xor     r8d, r8d
        mulpadi(r9,r12,r11,[x])
        mulpadd(r9,r13,r12,[x+8])
        mulpadd(r9,r14,r13,[x+16])
        mulpade(r9,r15,r14,[x+24])
        adc     r8, r8

// Montgomery reduce windows 2 and 3 together

        xor     r9d, r9d
        mov     rbx, 0x0000000100000000
        mulpadi(rcx,r12,r11,r10)
        mulpadd(rcx,r13,r12,r11)
        not     rbx
        lea     rbx, [rbx+2]
        mulpadd(rcx,r14,r13,r10)
        mulpade(rcx,r15,r14,r11)
        adc     r8, r9

// We now have a pre-reduced 5-word form [r8; r15;r14;r13;r12]
// Load [rax;r11;r9;rbx;rcx] = 2^320 - p_256, re-using earlier numbers a bit
// Do [rax;r11;r9;rbx;rcx] = [r8;r15;r14;r13;r12] + (2^320 - p_256)

        mov     ecx, 1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0x00000000fffffffe
        adc     r11, r15
        adc     rax, r8

// Now carry is set if r + (2^320 - p_256) >= 2^320, i.e. r >= p_256
// where r is the pre-reduced form. So conditionally select the
// output accordingly.

        cmovc   r12, rcx
        cmovc   r13, rbx
        cmovc   r14, r9
        cmovc   r15, r11

// Write back reduced value

        mov     [z], r12
        mov     [z+8], r13
        mov     [z+16], r14
        mov     [z+24], r15

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

S2N_BN_SIZE_DIRECTIVE(bignum_montmul_p256_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
