// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery multiply, z := (x * y / 2^256) mod p_256k1
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_montmul_p256k1(uint64_t z[static 4],
//                                      const uint64_t x[static 4],
//                                      const uint64_t y[static 4]);
//
// Does z := (2^{-256} * x * y) mod p_256k1, assuming that the inputs x and y
// satisfy x * y <= 2^256 * p_256k2 (in particular this is true if we are in
// the "usual" case x < p_256k1 and y < p_256k1).
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montmul_p256k1)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_montmul_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montmul_p256k1)
        .text

// These are actually right

#define z rdi
#define x rsi

// Copied in or set up

#define y rcx

// A zero register

#define zero rbp
#define zeroe ebp

// Also used for multiplicative inverse in second part

#define w rbp

// mulpadd(high,low,m) adds rdx * m to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rbx as temporaries.

#define mulpadd(high,low,m)             \
        mulx    rbx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rbx

// mulpade(high,low,i) adds rdx * x[i] to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax as a temporary, assuming high created from scratch
// and that zero has value zero.

#define mulpade(high,low,m)             \
        mulx    high, rax, m;           \
        adcx    low, rax;               \
        adox    high, zero

S2N_BN_SYMBOL(bignum_montmul_p256k1):
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

// Zero a register, which also makes sure we don't get a fake carry-in

        xor     zeroe, zeroe

// Do the zeroth row, which is a bit different

        mov     rdx, [y]

        mulx    r9, r8, [x]
        mulx    r10, rax, [x+8]
        add     r9, rax
        mulx    r11, rax, [x+16]
        adc     r10, rax
        mulx    r12, rax, [x+24]
        adc     r11, rax
        adc     r12, zero

// Add row 1

        xor     zeroe, zeroe
        mov     rdx, [y+8]
        mulpadd(r10,r9,[x])
        mulpadd(r11,r10,[x+8])
        mulpadd(r12,r11,[x+16])
        mulpade(r13,r12,[x+24])
        adcx    r13, zero

// Add row 2

        xor     zeroe, zeroe
        mov     rdx, [y+16]
        mulpadd(r11,r10,[x])
        mulpadd(r12,r11,[x+8])
        mulpadd(r13,r12,[x+16])
        mulpade(r14,r13,[x+24]);
        adcx    r14, zero

// Add row 3

        xor     zeroe, zeroe
        mov     rdx, [y+24]
        mulpadd(r12,r11,[x])
        mulpadd(r13,r12,[x+8])
        mulpadd(r14,r13,[x+16]);
        mulpade(r15,r14,[x+24]);
        adcx    r15, zero

// Now we have the full 8-digit product 2^256 * h + l where
// h = [r15,r14,r13,r12] and l = [r11,r10,r9,r8]
// Do Montgomery reductions, now using rcx as a carry-saver.
// A direct carry chain is possible using mulx exclusively, but it
// requires more moves and overall seems to have lower performance.

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

S2N_BN_SIZE_DIRECTIVE(bignum_montmul_p256k1)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
