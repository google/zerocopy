// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery square, z := (x^2 / 2^256) mod p_sm2
// Input x[4]; output z[4]
//
//    extern void bignum_montsqr_sm2(uint64_t z[static 4],
//                                   const uint64_t x[static 4]);
//
// Does z := (x^2 / 2^256) mod p_sm2, assuming x^2 <= 2^256 * p_sm2, which is
// guaranteed in particular if x < p_sm2 initially (the "intended" case).
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montsqr_sm2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montsqr_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montsqr_sm2)
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

// ---------------------------------------------------------------------------
// Core one-step "short" Montgomery reduction macro. Takes input in
// [d3;d2;d1;d0] and returns result in [d0;d3;d2;d1], adding to the
// existing contents of [d3;d2;d1], and using rax, rcx, rdx and rbx
// as temporaries.
// ---------------------------------------------------------------------------

#define montreds(d3,d2,d1,d0)                                               \
        mov     rax, d0;                                                    \
        shl     rax, 32;                                                    \
        mov     rcx, d0;                                                    \
        shr     rcx, 32;                                                    \
        mov     rdx, rax;                                                   \
        mov     rbx, rcx;                                                   \
        sub     rax, d0;                                                    \
        sbb     rcx, 0;                                                     \
        sub     d1, rax;                                                    \
        sbb     d2, rcx;                                                    \
        sbb     d3, rdx;                                                    \
        sbb     d0, rbx

S2N_BN_SYMBOL(bignum_montsqr_sm2):
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

// Squaring complete. Perform 4 Montgomery steps to rotate the lower half

        montreds(r11,r10,r9,r8)
        montreds(r8,r11,r10,r9)
        montreds(r9,r8,r11,r10)
        montreds(r10,r9,r8,r11)

// Add high and low parts, catching carry in rax

        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax

// Load [r8;r11;rbp;rdx;rcx] = 2^320 - p_sm2 then do
// [r8;r11;rbp;rdx;rcx] = [rax;r15;r14;r13;r12] + (2^320 - p_sm2)

        mov     ecx, 1
        mov     edx, 0x00000000FFFFFFFF
        xor     ebp, ebp
        add     rcx, r12
        lea     r11, [rdx+1]
        adc     rdx, r13
        lea     r8, [rbp-1]
        adc     rbp, r14
        adc     r11, r15
        adc     r8, rax

// Now carry is set if r + (2^320 - p_sm2) >= 2^320, i.e. r >= p_sm2
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

S2N_BN_SIZE_DIRECTIVE(bignum_montsqr_sm2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
