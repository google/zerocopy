// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Triple modulo p_521, z := (3 * x) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_triple_p521(uint64_t z[static 9],
//                                   const uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_triple_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_triple_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_triple_p521)
        .text

#define z rdi
#define x rsi

// d7 re-uses the input pointer when safe to do so

#define d0 rax
#define d1 rcx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11
#define d6 r12
#define d7 rsi
#define d8 rdx

#define m rbx
#define mshort ebx



S2N_BN_SYMBOL(bignum_triple_p521):
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

// Load the top (short) word first to compute the initial carry-in
// Set OF according to bit 520, but *always* set CF to get a +1 bump

        mov     m, [x+64]
        mov     d8, m
        shl     m, 54
        add     m, m
        stc

// Use a double carry chain to compute x' + x + 1 where x' is a
// 1-bit left rotation of x; this is then == 3 * x + 1 (mod p_521)
// This gives us s = [d8;d7;d6;d5;d4;d3;d2;d1;d0] = x + x' + 1.

        mov     m, [x]
        mov     d0, m
        adcx    m, m
        adox    d0, m
        mov     m, [x+8]
        mov     d1, m
        adcx    m, m
        adox    d1, m
        mov     m, [x+16]
        mov     d2, m
        adcx    m, m
        adox    d2, m
        mov     m, [x+24]
        mov     d3, m
        adcx    m, m
        adox    d3, m
        mov     m, [x+32]
        mov     d4, m
        adcx    m, m
        adox    d4, m
        mov     m, [x+40]
        mov     d5, m
        adcx    m, m
        adox    d5, m
        mov     m, [x+48]
        mov     d6, m
        adcx    m, m
        adox    d6, m
        mov     m, [x+56]
        mov     d7, m
        adcx    m, m
        adox    d7, m

// The last word is slightly more intricate: we naturally end up adding
// 2 * top bit when we shouldn't (because it's a rotation and we've already
// added it at the LSB position) but then compensate by subtracting it.

        mov     m, d8
        adcx    m, m
        adox    d8, m
        and     m, 0x200
        sub     d8, m

// Now x + x' >= p_521 <=> s = x + x' + 1 >= 2^521
// Make m = 512 * [x + x' >= p_521]

        mov     mshort, 512
        and     m, d8

// Now if x + x' >= p_521, we want (x + x') - p_521 = s - 2^521
// while otherwise we want x + x' = s - 1
// We use the mask m both as an operand and to generate the dual carry
// Write back the results as generated

        cmp     m, 512

        sbb     d0, 0
        mov     [z], d0
        sbb     d1, 0
        mov     [z+8],  d1
        sbb     d2, 0
        mov     [z+16], d2
        sbb     d3, 0
        mov     [z+24], d3
        sbb     d4, 0
        mov     [z+32], d4
        sbb     d5, 0
        mov     [z+40], d5
        sbb     d6, 0
        mov     [z+48], d6
        sbb     d7, 0
        mov     [z+56], d7
        sbb     d8, m
        mov     [z+64], d8

// Restore registers and return

        CFI_POP(r12)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_triple_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
