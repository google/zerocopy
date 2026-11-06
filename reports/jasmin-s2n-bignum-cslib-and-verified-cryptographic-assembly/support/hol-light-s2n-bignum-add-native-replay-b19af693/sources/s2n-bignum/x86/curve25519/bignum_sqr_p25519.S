// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square modulo p_25519, z := (x^2) mod p_25519
// Input x[4]; output z[4]
//
//    extern void bignum_sqr_p25519(uint64_t z[static 4], const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sqr_p25519)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_sqr_p25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sqr_p25519)
        .text

#define z rdi
#define x rsi

// Use this fairly consistently for a zero

#define zero rbx
#define zeroe ebx

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rcx as temporaries

#define mulpadd(high,low,m)             \
        mulx    rcx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rcx

// mulpade(high,low,m) adds rdx * m to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax as a temporary, assuming high created from scratch
// and that zero has value zero.

#define mulpade(high,low,m)             \
        mulx    high, rax, m;           \
        adcx    low, rax;               \
        adox    high, zero

S2N_BN_SYMBOL(bignum_sqr_p25519):
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

// Double and add to the 00 + 11 + 22 + 33 terms, while also
// pre-estimating the quotient from early results.

        xor     zeroe, zeroe
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [x+8]
        mulx    rcx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rcx
        mov     rdx, [x+16]
        mulx    rcx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rcx
        mov     rdx, [x+24]
        mulx    r15, rax, rdx

        mov     edx, 38
        mulx    rcx, rdx, r15

        adcx    r14, r14
        adox    r14, rax
        adcx    r15, zero
        adox    r15, zero

        add     rdx, r11
        adc     rcx, zero
        shld    rcx, rdx, 1
        lea     rbx, [rcx+1]
        imul    rbx, 19

// Now we have the full 8-digit product 2^256 * h + l where
// h = [r15,r14,r13,r12] and l = [r11,r10,r9,r8]
// and this is == 38 * h + l (mod p_25519)
// We add in the precalculated 19 * q as well.
// This is kept in 4 words since we have enough information there.

        xor     eax, eax
        adox    r8, rbx
        mov     edx, 38
        mulpadd(r9,r8,r12)
        mulpadd(r10,r9,r13)
        mulpadd(r11,r10,r14)
        mulx    rcx, rax, r15
        adc     r11, rax

// We still haven't made the -2^255 * q contribution yet. Since we
// are now safely in 4 words we just need a single bit of q, and we
// can actually use the LSB of rcx = 19 * q since 19 is odd. And we
// don't literally need to subtract, just to see whether we would
// have a top 1 bit if we did, meaning we need to correct in the
// last step by adding 2^255 - 19.

        xor     ecx, ecx
        shl     rbx, 63
        cmp     r11, rbx
        mov     eax, 19
        cmovns  rax, rcx

// Now make that possible correction and finally mask to 255 bits

        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rcx
        sbb     r11, rcx
        btr     r11, 63

// Write everything back

        mov     [z], r8
        mov     [z+8], r9
        mov     [z+16], r10
        mov     [z+24], r11

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

S2N_BN_SIZE_DIRECTIVE(bignum_sqr_p25519)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
