// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert to Montgomery form z := (2^256 * x) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_tomont_p256_alt(uint64_t z[static 4],
//                                       const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_p256_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tomont_p256_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_p256_alt)
        .text

#define z rdi
#define x rsi

// Add rcx * m into a register-pair (high,low) maintaining consistent
// carry-catching with carry (negated, as bitmask) and using rax and rdx
// as temporaries

#define mulpadd(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rcx;                    \
        sub     rdx, carry;             \
        add     low, rax;               \
        adc     high, rdx;              \
        sbb     carry, carry

// Initial version assuming no carry-in

#define mulpadi(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rcx;                    \
        add     low, rax;               \
        adc     high, rdx;              \
        sbb     carry, carry

// End version not catching the top carry-out

#define mulpade(carry,high,low,m)       \
        mov     rax, m;                 \
        mul     rcx;                    \
        sub     rdx, carry;             \
        add     low, rax;               \
        adc     high, rdx

S2N_BN_SYMBOL(bignum_tomont_p256_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save more registers to play with

        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Do row 0 computation, which is a bit different:
// set up initial window [r12,r11,r10,r9,r8] = y[0] * x
// Unlike later, we only need a single carry chain

        mov     ecx, 0x0000000000000003
        mov     rax, [x]
        mul     rcx
        mov     r8, rax
        mov     r9, rdx

        mov     rax, [x+8]
        mul     rcx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx

        mov     rax, [x+16]
        mul     rcx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx

        mov     rax, [x+24]
        mul     rcx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx

// Add row 1

        mov     rcx, 0xfffffffbffffffff
        xor     r13d, r13d
        mulpadi(r14,r10,r9,[x])
        mulpadd(r14,r11,r10,[x+8])
        mulpadd(r14,r12,r11,[x+16])
        mulpade(r14,r13,r12,[x+24])

// Montgomery reduce windows 0 and 1 together

        xor     r14d, r14d
        mov     rcx, 0x0000000100000000
        mulpadi(r15,r10,r9,r8)
        mulpadd(r15,r11,r10,r9)
        not     rcx
        lea     rcx, [rcx+2]
        mulpadd(r15,r12,r11,r8)
        mulpade(r15,r13,r12,r9)
        adc     r14, r14

// Add row 2

        mov     rcx, 0xfffffffffffffffe
        xor     r15d, r15d
        mulpadi(r8,r11,r10,[x])
        mulpadd(r8,r12,r11,[x+8])
        mulpadd(r8,r13,r12,[x+16])
        mulpade(r8,r14,r13,[x+24])
        adc     r15, r15

// Add row 3

        mov     rcx, 0x00000004fffffffd
        xor     r8d, r8d
        mulpadi(r9,r12,r11,[x])
        mulpadd(r9,r13,r12,[x+8])
        mulpadd(r9,r14,r13,[x+16])
        mulpade(r9,r15,r14,[x+24])
        adc     r8, r8

// Montgomery reduce windows 2 and 3 together

        mov     rcx, 0x0000000100000000
        mulpadi(r9,r12,r11,r10)
        mulpadd(r9,r13,r12,r11)
        not     rcx
        lea     rcx, [rcx+2]
        mulpadd(r9,r14,r13,r10)
        mulpadd(r9,r15,r14,r11)
        sub     r8, r9

// We now have a pre-reduced 5-word form [r8; r15;r14;r13;r12]
// Load [rax;r11;r9;rcx;rdx] = 2^320 - p_256, re-using earlier numbers a bit
// Do [rax;r11;r9;rcx;rdx] = [r8;r15;r14;r13;r12] + (2^320 - p_256)

        xor     edx, edx
        lea     r9, [rdx-1]
        inc     rdx
        add     rdx, r12
        dec     rcx
        adc     rcx, r13
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0x00000000fffffffe
        adc     r11, r15
        adc     rax, r8

// Now carry is set if r + (2^320 - p_256) >= 2^320, i.e. r >= p_256
// where r is the pre-reduced form. So conditionally select the
// output accordingly.

        cmovc   r12, rdx
        cmovc   r13, rcx
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

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_tomont_p256_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
