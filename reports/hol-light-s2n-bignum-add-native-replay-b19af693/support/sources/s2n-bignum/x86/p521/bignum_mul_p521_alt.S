// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply modulo p_521, z := (x * y) mod p_521, assuming x and y reduced
// Inputs x[9], y[9]; output z[9]
//
//    extern void bignum_mul_p521_alt(uint64_t z[static 9],
//                                    const uint64_t x[static 9],
//                                    const uint64_t y[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mul_p521_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mul_p521_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mul_p521_alt)
        .text

#define z rdi
#define x rsi

// This is moved from rdx to free it for muls

#define y rcx

// Macro for the key "multiply and add to (c,h,l)" step

#define combadd(c,h,l,numa,numb)                \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, 0

// A minutely shorter form for when c = 0 initially

#define combadz(c,h,l,numa,numb)                \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, c

// A short form where we don't expect a top carry

#define combads(h,l,numa,numb)                  \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx

S2N_BN_SYMBOL(bignum_mul_p521_alt):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Make more registers available and make temporary space on stack

        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(72)

// Copy y into a safe register to start with

        mov     y, rdx

// Start doing a conventional columnwise multiplication,
// temporarily storing the lower 9 digits to the stack.
// Start with result term 0

        mov     rax, [x]
        mul     QWORD PTR [y]

        mov     [rsp], rax
        mov     r9, rdx
        xor     r10, r10

// Result term 1

        xor     r11, r11
        combads(r10,r9,[x],[y+8])
        combadz(r11,r10,r9,[x+8],[y])
        mov     [rsp+8], r9

// Result term 2

        xor     r12, r12
        combadz(r12,r11,r10,[x],[y+16])
        combadd(r12,r11,r10,[x+8],[y+8])
        combadd(r12,r11,r10,[x+16],[y])
        mov     [rsp+16], r10

// Result term 3

        xor     r13, r13
        combadz(r13,r12,r11,[x],[y+24])
        combadd(r13,r12,r11,[x+8],[y+16])
        combadd(r13,r12,r11,[x+16],[y+8])
        combadd(r13,r12,r11,[x+24],[y])
        mov     [rsp+24], r11

// Result term 4

        xor     r14, r14
        combadz(r14,r13,r12,[x],[y+32])
        combadd(r14,r13,r12,[x+8],[y+24])
        combadd(r14,r13,r12,[x+16],[y+16])
        combadd(r14,r13,r12,[x+24],[y+8])
        combadd(r14,r13,r12,[x+32],[y])
        mov     [rsp+32], r12

// Result term 5

        xor     r15, r15
        combadz(r15,r14,r13,[x],[y+40])
        combadd(r15,r14,r13,[x+8],[y+32])
        combadd(r15,r14,r13,[x+16],[y+24])
        combadd(r15,r14,r13,[x+24],[y+16])
        combadd(r15,r14,r13,[x+32],[y+8])
        combadd(r15,r14,r13,[x+40],[y])
        mov     [rsp+40], r13

// Result term 6

        xor     r8, r8
        combadz(r8,r15,r14,[x],[y+48])
        combadd(r8,r15,r14,[x+8],[y+40])
        combadd(r8,r15,r14,[x+16],[y+32])
        combadd(r8,r15,r14,[x+24],[y+24])
        combadd(r8,r15,r14,[x+32],[y+16])
        combadd(r8,r15,r14,[x+40],[y+8])
        combadd(r8,r15,r14,[x+48],[y])
        mov     [rsp+48], r14

// Result term 7

        xor     r9, r9
        combadz(r9,r8,r15,[x],[y+56])
        combadd(r9,r8,r15,[x+8],[y+48])
        combadd(r9,r8,r15,[x+16],[y+40])
        combadd(r9,r8,r15,[x+24],[y+32])
        combadd(r9,r8,r15,[x+32],[y+24])
        combadd(r9,r8,r15,[x+40],[y+16])
        combadd(r9,r8,r15,[x+48],[y+8])
        combadd(r9,r8,r15,[x+56],[y])
        mov     [rsp+56], r15

// Result term 8

        xor     r10, r10
        combadz(r10,r9,r8,[x],[y+64])
        combadd(r10,r9,r8,[x+8],[y+56])
        combadd(r10,r9,r8,[x+16],[y+48])
        combadd(r10,r9,r8,[x+24],[y+40])
        combadd(r10,r9,r8,[x+32],[y+32])
        combadd(r10,r9,r8,[x+40],[y+24])
        combadd(r10,r9,r8,[x+48],[y+16])
        combadd(r10,r9,r8,[x+56],[y+8])
        combadd(r10,r9,r8,[x+64],[y])
        mov     [rsp+64], r8

// At this point we suspend writing back results and collect them
// in a register window. Next is result term 9

        xor     r11, r11
        combadz(r11,r10,r9,[x+8],[y+64])
        combadd(r11,r10,r9,[x+16],[y+56])
        combadd(r11,r10,r9,[x+24],[y+48])
        combadd(r11,r10,r9,[x+32],[y+40])
        combadd(r11,r10,r9,[x+40],[y+32])
        combadd(r11,r10,r9,[x+48],[y+24])
        combadd(r11,r10,r9,[x+56],[y+16])
        combadd(r11,r10,r9,[x+64],[y+8])

// Result term 10

        xor     r12, r12
        combadz(r12,r11,r10,[x+16],[y+64])
        combadd(r12,r11,r10,[x+24],[y+56])
        combadd(r12,r11,r10,[x+32],[y+48])
        combadd(r12,r11,r10,[x+40],[y+40])
        combadd(r12,r11,r10,[x+48],[y+32])
        combadd(r12,r11,r10,[x+56],[y+24])
        combadd(r12,r11,r10,[x+64],[y+16])

// Result term 11

        xor     r13, r13
        combadz(r13,r12,r11,[x+24],[y+64])
        combadd(r13,r12,r11,[x+32],[y+56])
        combadd(r13,r12,r11,[x+40],[y+48])
        combadd(r13,r12,r11,[x+48],[y+40])
        combadd(r13,r12,r11,[x+56],[y+32])
        combadd(r13,r12,r11,[x+64],[y+24])

// Result term 12

        xor     r14, r14
        combadz(r14,r13,r12,[x+32],[y+64])
        combadd(r14,r13,r12,[x+40],[y+56])
        combadd(r14,r13,r12,[x+48],[y+48])
        combadd(r14,r13,r12,[x+56],[y+40])
        combadd(r14,r13,r12,[x+64],[y+32])

// Result term 13

        xor     r15, r15
        combadz(r15,r14,r13,[x+40],[y+64])
        combadd(r15,r14,r13,[x+48],[y+56])
        combadd(r15,r14,r13,[x+56],[y+48])
        combadd(r15,r14,r13,[x+64],[y+40])

// Result term 14

        xor     r8, r8
        combadz(r8,r15,r14,[x+48],[y+64])
        combadd(r8,r15,r14,[x+56],[y+56])
        combadd(r8,r15,r14,[x+64],[y+48])

// Result term 15

        combads(r8,r15,[x+56],[y+64])
        combads(r8,r15,[x+64],[y+56])

// Result term 16

        mov     rax, [x+64]
        imul    rax, [y+64]
        add     rax, r8

// Now the upper portion is [rax;r15;r14;r13;r12;r11;r10;r9;[rsp+64]].
// Rotate the upper portion right 9 bits since 2^512 == 2^-9 (mod p_521)
// Let rotated result rdx,r15,r14,...,r8 be h (high) and rsp[0..7] be l (low)

        mov     r8, [rsp+64]
        mov     rdx, r8
        and     rdx, 0x1FF
        shrd    r8, r9, 9
        shrd    r9, r10, 9
        shrd    r10, r11, 9
        shrd    r11, r12, 9
        shrd    r12, r13, 9
        shrd    r13, r14, 9
        shrd    r14, r15, 9
        shrd    r15, rax, 9
        shr     rax, 9
        add     rdx, rax

// Force carry-in then add to get s = h + l + 1
// but actually add all 1s in the top 53 bits to get simple carry out

        stc
        adc     r8, [rsp]
        adc     r9, [rsp+8]
        adc     r10,[rsp+16]
        adc     r11,[rsp+24]
        adc     r12,[rsp+32]
        adc     r13,[rsp+40]
        adc     r14,[rsp+48]
        adc     r15,[rsp+56]
        adc     rdx, ~0x1FF

// Now CF is set <=> h + l + 1 >= 2^521 <=> h + l >= p_521,
// in which case the lower 521 bits are already right. Otherwise if
// CF is clear, we want to subtract 1. Hence subtract the complement
// of the carry flag then mask the top word, which scrubs the
// padding in either case. Write digits back as they are created.

        cmc
        sbb     r8, 0
        mov     [z], r8
        sbb     r9, 0
        mov     [z+8],  r9
        sbb     r10, 0
        mov     [z+16], r10
        sbb     r11, 0
        mov     [z+24], r11
        sbb     r12, 0
        mov     [z+32], r12
        sbb     r13, 0
        mov     [z+40], r13
        sbb     r14, 0
        mov     [z+48], r14
        sbb     r15, 0
        mov     [z+56], r15
        sbb     rdx, 0
        and     rdx, 0x1FF
        mov     [z+64], rdx

// Restore registers and return

        CFI_INC_RSP(72)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mul_p521_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
