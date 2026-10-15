// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery multiply, z := (x * y / 2^256) mod p_256
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_montmul_p256(uint64_t z[static 4],
//                                    const uint64_t x[static 4],
//                                    const uint64_t y[static 4]);
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
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montmul_p256)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montmul_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montmul_p256)
        .text

#define z rdi
#define x rsi

// We move the y argument here so we can use rdx for multipliers

#define y rcx

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rbx as temporaries

#define mulpadd(high,low,m)             \
        mulx    rbx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rbx

S2N_BN_SYMBOL(bignum_montmul_p256):
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

        xor     r13d, r13d
        mov     rdx, [y]
        mulx    r9, r8, [x]
        mulx    r10, rbx, [x+8]
        adc     r9, rbx
        mulx    r11, rbx, [x+16]
        adc     r10, rbx
        mulx    r12, rbx, [x+24]
        adc     r11, rbx
        adc     r12, r13

// Add row 1

        mov     rdx, [y+8]
        xor     r14d, r14d
        mulpadd(r10,r9,[x])
        mulpadd(r11,r10,[x+8])
        mulpadd(r12,r11,[x+16])
        mulpadd(r13,r12,[x+24])
        adc    r13, r14

// Montgomery reduce windows 0 and 1 together

        xor     r15d, r15d
        mov     rdx, 0x0000000100000000
        mulpadd(r10,r9,r8)
        mulpadd(r11,r10,r9)
        not     rdx
        lea     rdx, [rdx+2]
        mulpadd(r12,r11,r8)
        mulpadd(r13,r12,r9)
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15

// Add row 2

        mov     rdx, [y+16]
        xor     r8d, r8d
        mulpadd(r11,r10,[x])
        mulpadd(r12,r11,[x+8])
        mulpadd(r13,r12,[x+16])
        adox    r14, r8
        mulx    rbx, rax, [x+24]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8

// Add row 3

        mov     rdx, [y+24]
        xor     r9d, r9d
        mulpadd(r12,r11,[x])
        mulpadd(r13,r12,[x+8])
        mulpadd(r14,r13,[x+16])
        adox    r15, r9
        mulx    rbx, rax, [x+24]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9

// Montgomery reduce windows 2 and 3 together

        xor     r9d, r9d
        mov     rdx, 0x0000000100000000
        mulpadd(r12,r11,r10)
        mulpadd(r13,r12,r11)
        not     rdx
        lea     rdx, [rdx+2]
        mulpadd(r14,r13,r10)
        mulpadd(r15,r14,r11)
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9

// We now have a pre-reduced 5-word form [r8; r15;r14;r13;r12]
// Load [rax;r11;rbx;rdx;rcx] = 2^320 - p_256, re-using earlier numbers a bit
// Do [rax;r11;rbx;rdx;rcx] = [r8;r15;r14;r13;r12] + (2^320 - p_256)

        mov     ecx, 1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
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
        cmovc   r13, rdx
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

S2N_BN_SIZE_DIRECTIVE(bignum_montmul_p256)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
