// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery square, z := (x^2 / 2^256) mod p_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_montsqr_p256k1(uint64_t z[static 4],
//                                      const uint64_t x[static 4]);
//
// Does z := (x^2 / 2^256) mod p_256k1, assuming x^2 <= 2^256 * p_256k1, which
// is guaranteed in particular if x < p_256k1 initially (the "intended" case).
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montsqr_p256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montsqr_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montsqr_p256k1)
        .text

#define z rdi
#define x rsi

// Use this fairly consistently for a zero

#define zero rbp
#define zeroe ebp

// Also use the same register for multiplicative inverse in Montgomery stage

#define w rbp

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rbx as temporaries

#define mulpadd(high,low,m)             \
        mulx    rbx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rbx

S2N_BN_SYMBOL(bignum_montsqr_p256k1):
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

// Now we have the full 8-digit square 2^256 * h + l where
// h = [r15,r14,r13,r12] and l = [r11,r10,r9,r8]
// Do Montgomery reductions, now using rcx as a carry save

        mov     w, 0xd838091dd2253531
        mov     rbx, 4294968273

// Montgomery reduce row 0

        mov     rax, rbx
        imul    r8, w
        mul     r8
        sub     r9, rdx
        sbb     rcx, rcx

// Montgomery reduce row 1

        mov     rax, rbx
        imul    r9, w
        mul     r9
        neg     rcx
        sbb     r10, rdx
        sbb     rcx, rcx

// Montgomery reduce row 2

        mov     rax, rbx
        imul    r10, w
        mul     r10
        neg     rcx
        sbb     r11, rdx
        sbb     rcx, rcx

// Montgomery reduce row 3

        mov     rax, rbx
        imul    r11, w
        mul     r11
        neg     rcx

// Now [r15,r14,r13,r12] := [r15,r14,r13,r12] + [r11,r10,r9,r8] - (rdx + CF)

        sbb     r8, rdx
        sbb     r9, 0
        sbb     r10, 0
        sbb     r11, 0

        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        sbb     w, w

// Let b be the top carry captured just above as w = (2^64-1) * b
// Now if [b,r15,r14,r13,r12] >= p_256k1, subtract p_256k1, i.e. add 4294968273
// and either way throw away the top word. [b,r15,r14,r13,r12] - p_256k1 =
// [(b - 1),r15,r14,r13,r12] + 4294968273. If [r15,r14,r13,r12] + 4294968273
// gives carry flag CF then >= comparison is top = 0 <=> b - 1 + CF = 0 which
// is equivalent to b \/ CF, and so to (2^64-1) * b + (2^64 - 1) + CF >= 2^64

        mov     r8, r12
        add     r8, rbx
        mov     r9, r13
        adc     r9, 0
        mov     r10, r14
        adc     r10, 0
        mov     r11, r15
        adc     r11, 0

        adc     w, -1

// Write everything back

        cmovc   r12, r8
        mov     [z], r12
        cmovc   r13, r9
        mov     [z+8], r13
        cmovc   r14, r10
        mov     [z+16], r14
        cmovc   r15, r11
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

S2N_BN_SIZE_DIRECTIVE(bignum_montsqr_p256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
