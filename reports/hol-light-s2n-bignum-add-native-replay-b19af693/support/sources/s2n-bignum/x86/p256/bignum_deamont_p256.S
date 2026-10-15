// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert from almost-Montgomery form, z := (x / 2^256) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_deamont_p256(uint64_t z[static 4],
//                                    const uint64_t x[static 4]);
//
// Convert a 4-digit bignum x out of its (optionally almost) Montgomery form,
// "almost" meaning any 4-digit input will work, with no range restriction.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_deamont_p256)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_deamont_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_deamont_p256)
        .text

#define z rdi
#define x rsi

// Re-use these as temporaries in the correction phase

#define d rdx
#define u r10
#define v r11

#define dshort edx
#define ushort r10d

// Add rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rcx as temporaries

#define mulpadd(high,low,m)             \
        mulx    rcx, rax, m;            \
        adcx    low, rax;               \
        adox    high, rcx

S2N_BN_SYMBOL(bignum_deamont_p256):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save one more register to play with

        CFI_PUSH(rbx)

// Set up an initial 4-word window [r11,r10,r9,r8] = x

        mov     r8, [x]
        mov     r9, [x+8]
        mov     r10, [x+16]
        mov     r11, [x+24]

// Fill in two zeros to the left

        xor     rbx, rbx
        xor     rsi, rsi

// Montgomery reduce windows 0 and 1 together

        mov     rdx, 0x0000000100000000
        mulpadd(r10,r9,r8)
        mulpadd(r11,r10,r9)
        mov     rdx, 0xffffffff00000001
        mulpadd(rbx,r11,r8)
        mulpadd(rsi,rbx,r9)
        mov     r8d, 0
        adcx    rsi, r8

// Append just one more leading zero (by the above r8 = 0 already).

        xor     r9, r9

// Montgomery reduce windows 2 and 3 together

        mov     rdx, 0x0000000100000000
        mulpadd(rbx,r11,r10)
        mulpadd(rsi,rbx,r11)
        mov     rdx, 0xffffffff00000001
        mulpadd(r8,rsi,r10)
        mulpadd(r9,r8,r11)
        mov     r10d, 0
        adcx    r9, r10

// We now have a pre-reduced dd = [r9;r8;rsi;rbx]. Load non-trivial digits
// of p_256 = [v; 0; u; -1]

        mov     ushort, 0x00000000ffffffff
        mov     v, 0xffffffff00000001

// Now do the subtraction (p_256-1) - (r9;r8;rsi;rbx) to get the carry

        mov     d, -2
        sub     d, rbx
        mov     d, u
        sbb     d, rsi
        mov     dshort, 0
        sbb     d, r8
        mov     d, v
        sbb     d, r9

// Convert the carry CF <=> dd >= p_256 to a bitmask and do a masked subtraction

        sbb     d, d
        and     u, d
        and     v, d

        sub     rbx, d
        sbb     rsi, u
        sbb     r8, 0
        sbb     r9, v

// Write back

        mov     [z], rbx
        mov     [z+8], rsi
        mov     [z+16], r8
        mov     [z+24], r9

// Restore saved register and return

        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_deamont_p256)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
