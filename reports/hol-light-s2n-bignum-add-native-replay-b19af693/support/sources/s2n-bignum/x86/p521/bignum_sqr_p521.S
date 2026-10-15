// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square modulo p_521, z := (x^2) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_sqr_p521(uint64_t z[static 9], const uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sqr_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_sqr_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sqr_p521)
        .text

#define z rdi
#define x rsi

// A zero register

#define zero rbp
#define zeroe ebp

// mulpadd(high,low,i) adds rdx * x[i] to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rcx as temporaries.

#define mulpadd(high,low,I)             \
        mulx    rcx, rax, [x+I];        \
        adcx    low, rax;               \
        adox    high, rcx

// mulpade(high,low,i) adds rdx * x[i] to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax as a temporary, assuming high created from scratch
// and that zero has value zero.

#define mulpade(high,low,I)             \
        mulx    high, rax, [x+I];       \
        adcx    low, rax;               \
        adox    high, zero

S2N_BN_SYMBOL(bignum_sqr_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save more registers to play with and make temporary space on stack

        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(64)

// Do a basic 8x8 squaring stashing in rsp[0..7] but keeping the
// top half in the usual rotating register window r15,...,r8. Except
// for the lack of full writeback this is the same as bignum_sqr_8_16.

        xor     zeroe, zeroe

        mov     rdx, [x]
        mulx    rax, r9, [x+8]
        mov     [rsp+8], r9
        mulx    rcx, r10, [x+16]
        adcx    r10, rax
        mov     [rsp+16], r10
        mulx    rax, r11, [x+24]
        adcx    r11, rcx
        mulx    rcx, r12, [x+32]
        adcx    r12, rax
        mulx    rax, r13, [x+40]
        adcx    r13, rcx
        mulx    rcx, r14, [x+48]
        adcx    r14, rax
        mulx    r8, r15, [x+56]
        adcx    r15, rcx
        adcx    r8, zero

        xor     zeroe, zeroe
        mov     rdx, [x+8]
        mulpadd(r12,r11,16)
        mov     [rsp+24], r11
        mulpadd(r13,r12,24)
        mov     [rsp+32], r12
        mulpadd(r14,r13,32)
        mulpadd(r15,r14,40)
        mulpadd(r8,r15,48)
        mulpade(r9,r8,56)
        mov     rdx, [x+32]
        mulpade(r10,r9,40)
        adcx    r10, zero

        xor     zeroe, zeroe
        mov     rdx, [x+16]
        mulpadd(r14,r13,24)
        mov     [rsp+40], r13
        mulpadd(r15,r14,32)
        mov     [rsp+48], r14
        mulpadd(r8,r15,40)
        mulpadd(r9,r8,48)
        mulpadd(r10,r9,56)
        mov     rdx, [x+48]
        mulpade(r11,r10,32)
        mulpade(r12,r11,40)
        adcx    r12, zero

        xor     zeroe, zeroe
        mov     rdx, [x+24]
        mulpadd(r8,r15,32)
        mov     [rsp+56], r15
        mulpadd(r9,r8,40)
        mulpadd(r10,r9,48)
        mulpadd(r11,r10,56)
        mov     rdx, [x+56]
        mulpadd(r12,r11,32)
        mulpade(r13,r12,40)
        mulpade(r14,r13,48)
        adcx    r14, zero

        xor     zeroe, zeroe
        mov     rdx, [x]
        mulx    rcx, rax, rdx
        mov     [rsp], rax
        mov     rax, [rsp+8]
        adcx    rax, rax
        adox    rax, rcx
        mov     [rsp+8], rax

        mov     rax, [rsp+16]
        mov     rdx, [x+8]
        mulx    rcx, rdx, rdx
        adcx    rax, rax
        adox    rax, rdx
        mov     [rsp+16], rax
        mov     rax, [rsp+24]
        adcx    rax, rax
        adox    rax, rcx
        mov     [rsp+24], rax

        mov     rax, [rsp+32]
        mov     rdx, [x+16]
        mulx    rcx, rdx, rdx
        adcx    rax, rax
        adox    rax, rdx
        mov     [rsp+32], rax
        mov     rax, [rsp+40]
        adcx    rax, rax
        adox    rax, rcx
        mov     [rsp+40], rax

        mov     rax, [rsp+48]
        mov     rdx, [x+24]
        mulx    rcx, rdx, rdx
        adcx    rax, rax
        adox    rax, rdx
        mov     [rsp+48], rax
        mov     rax, [rsp+56]
        adcx    rax, rax
        adox    rax, rcx
        mov     [rsp+56], rax

        mov     rdx, [x+32]
        mulx    rcx, rdx, rdx
        adcx    r8, r8
        adox    r8, rdx
        adcx    r9, r9
        adox    r9, rcx

        mov     rdx, [x+40]
        mulx    rcx, rdx, rdx
        adcx    r10, r10
        adox    r10, rdx
        adcx    r11, r11
        adox    r11, rcx

        mov     rdx, [x+48]
        mulx    rcx, rdx, rdx
        adcx    r12, r12
        adox    r12, rdx
        adcx    r13, r13
        adox    r13, rcx

        mov     rdx, [x+56]
        mulx    r15, rdx, rdx
        adcx    r14, r14
        adox    r14, rdx
        adcx    r15, zero
        adox    r15, zero

// Augment the high part with the contribution from the top little word C.
// If we write the input as 2^512 * C + x then we are otherwise just doing
// x^2, so we need to add to the high part 2^512 * C^2 + (2 * C) * x.
// The initial doubling add of C also clears the CF and OF flags as desired.
// We extend the window now to the 9-element rbp,r15,r14,...,r8.

        mov     rdx, [x+64]
        mov     rbp, rdx
        imul    rbp, rbp
        add     rdx, rdx
        mulpadd(r9,r8,0)
        mulpadd(r10,r9,8)
        mulpadd(r11,r10,16)
        mulpadd(r12,r11,24)
        mulpadd(r13,r12,32)
        mulpadd(r14,r13,40)
        mulpadd(r15,r14,48)
        mulx   rcx, rax, [x+56]
        adcx   r15, rax
        adox   rbp, rcx
        adc    rbp, 0

// Rotate the upper portion right 9 bits since 2^512 == 2^-9 (mod p_521)
// Let rotated result rbp,r15,r14,...,r8 be h (high) and rsp[0..7] be l (low)

        mov     rax, r8
        and     rax, 0x1FF
        shrd    r8, r9, 9
        shrd    r9, r10, 9
        shrd    r10, r11, 9
        shrd    r11, r12, 9
        shrd    r12, r13, 9
        shrd    r13, r14, 9
        shrd    r14, r15, 9
        shrd    r15, rbp, 9
        shr     rbp, 9
        add     rbp, rax

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
        adc     rbp, ~0x1FF

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
        sbb     rbp, 0
        and     rbp, 0x1FF
        mov     [z+64], rbp

// Restore registers and return

        CFI_INC_RSP(64)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_sqr_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
