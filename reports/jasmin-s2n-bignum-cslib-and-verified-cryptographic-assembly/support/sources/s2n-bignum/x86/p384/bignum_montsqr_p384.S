// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery square, z := (x^2 / 2^384) mod p_384
// Input x[6]; output z[6]
//
//    extern void bignum_montsqr_p384(uint64_t z[static 6],
//                                    const uint64_t x[static 6]);
//
// Does z := (x^2 / 2^384) mod p_384, assuming x^2 <= 2^384 * p_384, which is
// guaranteed in particular if x < p_384 initially (the "intended" case).
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montsqr_p384)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montsqr_p384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montsqr_p384)
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

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rbx as temporaries

#define mulpadd(high,low,m)             \
        mulx    rbx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rbx

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
        mov     rdx, d0;                                        \
        shl     rdx, 32;                                        \
        add     rdx, d0;                                        \
/* Construct [rbx;d0;rax;-] = (2^384 - p_384) * w            */         \
/* We know the lowest word will cancel so we can re-use d0   */         \
/* and rbx as temps.                                         */         \
        mov     rax, 0xffffffff00000001;                        \
        mulx    rax, d0, rax;                                   \
        mov     ebx, 0x00000000ffffffff;                        \
        mulx    d0, rbx, rbx;                                   \
        add     rax, rbx;                                       \
        adc     d0, rdx;                                        \
        mov     ebx, 0;                                         \
        adc     rbx, rbx;                                       \
/* Now subtract that and add 2^384 * w                       */         \
        sub     d1, rax;                                        \
        sbb     d2, d0;                                         \
        sbb     d3, rbx;                                        \
        sbb     d4, 0;                                          \
        sbb     d5, 0;                                          \
        mov     d6, rdx;                                        \
        sbb     d6, 0

S2N_BN_SYMBOL(bignum_montsqr_p384):
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

        mov     rdx, [x]
        mulx    r10, r9, [x+8]
        mulx    r12, r11, [x+24]
        mulx    r14, r13, [x+40]
        mov     rdx, [x+24]
        mulx    rcx, r15, [x+32]

// Clear our zero register, and also initialize the flags for the carry chain

        xor     zeroe, zeroe

// Chain in the addition of 02 + 12 + 13 + 14 + 15 to that window
// (no carry-out possible)

        mov     rdx, [x+16]
        mulpadd(r11,r10,[x])
        mulpadd(r12,r11,[x+8])
        mov     rdx, [x+8]
        mulpadd(r13,r12,[x+24])
        mulpadd(r14,r13,[x+32])
        mulpadd(r15,r14,[x+40])
        adcx    r15, zero
        adox    rcx, zero
        adc     rcx, zero

// Again zero out the flags. Actually they are already cleared but it may
// help decouple these in the OOO engine not to wait for the chain above

        xor     zeroe, zeroe

// Now chain in the 04 + 23 + 24 + 25 + 35 + 45 terms
// We are running out of registers in our rotating window, so we start
// using rbx (and hence need care with using mulpadd after this). Thus
// our result so far is in [rbp;rbx;rcx;r15;...r9]

        mov     rdx, [x+32]
        mulpadd(r13,r12,[x])
        mov     rdx, [x+16]
        mulpadd(r14,r13,[x+24])
        mulpadd(r15,r14,[x+32])
        mulx    rdx, rax, [x+40]
        adcx    r15, rax
        adox    rcx, rdx

// First set up the last couple of spots in our window, [rbp;rbx] = 45
// then add the last other term 35

        mov     rdx, [x+40]
        mulx    rbp, rbx, [x+32]
        mulx    rdx, rax, [x+24]
        adcx    rcx, rax
        adox    rbx, rdx
        mov     eax, 0
        adcx    rbx, rax
        adox    rbp, rax
        adc     rbp, rax

// Just for a clear fresh start for the flags; we don't use the zero

        xor     rax, rax

// Double and add to the 00 + 11 + 22 + 33 + 44 + 55 terms
// For one glorious moment the entire squaring result is all in the
// register file as [rsi;rbp;rbx;rcx;r15;...;r8]
// (since we've now finished with x we can re-use rsi)

        mov     rdx, [x]
        mulx    rax, r8, [x]
        adcx    r9, r9
        adox    r9, rax
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
        mulx    rdx, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, r15
        adox    r15, rdx
        mov     rdx, [x+32]
        mulx    rdx, rax, rdx
        adcx    rcx, rcx
        adox    rcx, rax
        adcx    rbx, rbx
        adox    rbx, rdx
        mov     rdx, [x+40]
        mulx    rsi, rax, rdx
        adcx    rbp, rbp
        adox    rbp, rax
        mov     eax, 0
        adcx    rsi, rax
        adox    rsi, rax

// We need just *one* more register as a temp for the Montgomery steps.
// Since we are writing to the z buffer anyway, make use of that to stash rbx.

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

S2N_BN_SIZE_DIRECTIVE(bignum_montsqr_p384)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
