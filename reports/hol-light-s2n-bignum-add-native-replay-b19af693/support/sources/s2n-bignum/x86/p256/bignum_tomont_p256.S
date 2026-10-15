// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert to Montgomery form z := (2^256 * x) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_tomont_p256(uint64_t z[static 4],
//                                   const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_p256)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_tomont_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_p256)
        .text

#define z rdi
#define x rsi

// Some temp registers for the last correction stage

#define d rax
#define u rdx
#define v rcx

#define dshort eax
#define ushort edx

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rbx as temporaries

#define mulpadd(high,low,m)             \
        mulx    rcx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rcx

S2N_BN_SYMBOL(bignum_tomont_p256):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// We are essentially just doing a Montgomery multiplication of x and the
// precomputed constant y = 2^512 mod p, so the code is almost the same
// modulo a few registers and the change from loading y[i] to using constants.
// Because there is no y pointer to keep, we use one register less.

        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Do row 0 computation, which is a bit different:
// set up initial window [r12,r11,r10,r9,r8] = y[0] * x
// Unlike later, we only need a single carry chain

        xor     r13, r13
        mov     edx, 0x0000000000000003
        mulx    r9, r8, [x]
        mulx    r10, rcx, [x+8]
        adcx    r9, rcx
        mulx    r11, rcx, [x+16]
        adcx    r10, rcx
        mulx    r12, rcx, [x+24]
        adcx    r11, rcx
        adcx    r12, r13

// Add row 1

        mov     rdx, 0xfffffffbffffffff
        xor     r14, r14
        mulpadd(r10,r9,[x])
        mulpadd(r11,r10,[x+8])
        mulpadd(r12,r11,[x+16])
        mulpadd(r13,r12,[x+24])
        adc    r13, r14

// Montgomery reduce windows 0 and 1 together

        xor     r15, r15
        mov     rdx, 0x0000000100000000
        mulpadd(r10,r9,r8)
        mulpadd(r11,r10,r9)
        mov     rdx, 0xffffffff00000001
        mulpadd(r12,r11,r8)
        mulpadd(r13,r12,r9)
        adcx    r13, r15
        adox    r14, r15
        adcx    r14, r15

// Add row 2

        mov     rdx, 0xfffffffffffffffe
        xor     r8, r8
        mulpadd(r11,r10,[x])
        mulpadd(r12,r11,[x+8])
        mulpadd(r13,r12,[x+16])
        mulpadd(r14,r13,[x+24])
        adcx    r14, r8
        adox    r15, r8
        adcx    r15, r8

// Add row 3

        mov     rdx, 0x00000004fffffffd
        xor     r9, r9
        mulpadd(r12,r11,[x])
        mulpadd(r13,r12,[x+8])
        mulpadd(r14,r13,[x+16])
        mulpadd(r15,r14,[x+24])
        adcx    r15, r9
        adox    r8, r9
        adcx    r8, r9

// Montgomery reduce windows 2 and 3 together

        xor     r9, r9
        mov     rdx, 0x0000000100000000
        mulpadd(r12,r11,r10)
        mulpadd(r13,r12,r11)
        mov     rdx, 0xffffffff00000001
        mulpadd(r14,r13,r10)
        mulpadd(r15,r14,r11)
        adcx    r15, r9
        adox    r8, r9
        adcx    r8, r9

// We now have a pre-reduced 5-word form [r8; r15;r14;r13;r12]
// Load non-trivial digits of p_256 = [v; 0; u; -1]

        mov     ushort, 0x00000000ffffffff
        mov     v, 0xffffffff00000001

// Now do the subtraction (0,p_256-1) - (r8,r15,r14,r13,r12) to get the carry

        mov     d, -2
        sub     d, r12
        mov     d, u
        sbb     d, r13
        mov     dshort, 0
        sbb     d, r14
        mov     d, v
        sbb     d, r15

// This last comparison in the chain will actually even set the mask
// for us, so we don't need to separately create it from the carry.
// This means p_256 - 1 < (c,d1,d0,d5,d4), i.e. we are so far >= p_256

        mov     dshort, 0
        sbb     d, r8
        and     u, d
        and     v, d

// Do a masked subtraction of p_256 and write back

        sub     r12, d
        sbb     r13, u
        sbb     r14, 0
        sbb     r15, v

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

S2N_BN_SIZE_DIRECTIVE(bignum_tomont_p256)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
