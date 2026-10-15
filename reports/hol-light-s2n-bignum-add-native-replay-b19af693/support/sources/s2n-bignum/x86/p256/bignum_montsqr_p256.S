// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery square, z := (x^2 / 2^256) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_montsqr_p256(uint64_t z[static 4],
//                                    const uint64_t x[static 4]);
//
// Does z := (x^2 / 2^256) mod p_256, assuming x^2 <= 2^256 * p_256, which is
// guaranteed in particular if x < p_256 initially (the "intended" case).
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montsqr_p256)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montsqr_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montsqr_p256)
        .text

#define z rdi
#define x rsi

// Use this fairly consistently for a zero

#define zero rbp
#define zeroe ebp

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rbx as temporaries

#define mulpadd(high,low,m)             \
        mulx    rbx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rbx

S2N_BN_SYMBOL(bignum_montsqr_p256):
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

// Compute [r15;r8] = [00] which we use later, but mainly
// set up an initial window [r14;...;r9] = [23;03;01]

        mov     rdx, [x]
        mulx    r15, r8, rdx
        mulx    r10, r9, [x+8]
        mulx    r12, r11, [x+24]
        mov     rdx, [x+16]
        mulx    r14, r13, [x+24]

// Clear our zero register, and also initialize the flags for the carry chain

        xor     zeroe, zeroe

// Chain in the addition of 02 + 12 + 13 to that window (no carry-out possible)
// This gives all the "heterogeneous" terms of the squaring ready to double

        mulpadd(r11,r10,[x])
        mulpadd(r12,r11,[x+8])
        mov     rdx, [x+24]
        mulpadd(r13,r12,[x+8])
        adcx    r13, zero
        adox    r14, zero
        adc     r14, zero

// Double and add to the 00 + 11 + 22 + 33 terms

        xor     zeroe, zeroe
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [x+8]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [x+16]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [x+24]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, zero
        adox    r15, zero

// First two waves of Montgomery reduction. Consolidate the double carries
// in r9 and propagate up to the top in r8, which is no longer needed otherwise.

        xor     zeroe, zeroe
        mov     rdx, 0x0000000100000000
        mulpadd(r10,r9,r8)
        mulpadd(r11,r10,r9)
        mov     rdx, 0xffffffff00000001
        mulpadd(r12,r11,r8)
        mulpadd(r13,r12,r9)
        adcx    r13, zero
        mov     r9d, zeroe
        adox    r9, zero
        adcx    r9, zero
        add     r14, r9
        adc     r15, zero
        mov     r8d, zeroe
        adc     r8, zero

// Now two more steps of Montgomery reduction, again with r8 = top carry

        xor     zeroe, zeroe
        mov     rdx, 0x0000000100000000
        mulpadd(r12,r11,r10)
        mulpadd(r13,r12,r11)
        mov     rdx, 0xffffffff00000001
        mulpadd(r14,r13,r10)
        mulpadd(r15,r14,r11)
        adcx    r15, zero
        adox    r8, zero
        adc     r8, zero

// Load [rax;r11;rbp;rdx;rcx] = 2^320 - p_256, re-using earlier numbers a bit
// Do [rax;r11;rbp;rdx;rcx] = [r8;r15;r14;r13;r12] + (2^320 - p_256)

        mov     ecx, 1
        add     rcx, r12
        lea     rdx, [rdx-1]
        adc     rdx, r13
        lea     rbp, [rbp-1]
        mov     rax, rbp
        adc     rbp, r14
        mov     r11d,  0x00000000fffffffe
        adc     r11, r15
        adc     rax, r8

// Now carry is set if r + (2^320 - p_256) >= 2^320, i.e. r >= p_256
// where r is the pre-reduced form. So conditionally select the
// output accordingly.

        cmovc   r12, rcx
        cmovc   r13, rdx
        cmovc   r14, rbp
        cmovc   r15, r11

// Write back reduced value

        mov     [z], r12
        mov     [z+8], r13
        mov     [z+16], r14
        mov     [z+24], r15

// Restore saved registers and return

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

S2N_BN_SIZE_DIRECTIVE(bignum_montsqr_p256)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
