// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply modulo p_521, z := (x * y) mod p_521, assuming x and y reduced
// Inputs x[9], y[9]; output z[9]
//
//    extern void bignum_mul_p521(uint64_t z[static 9], const uint64_t x[static 9],
//                                const uint64_t y[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mul_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_mul_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mul_p521)
        .text

#define z rdi
#define x rsi

// Copied in

#define y rcx

// mulpadd (high,low,x) adds rdx * x to a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using rax and rbx as temporaries.

#define mulpadd(high,low,x)             \
        mulx    rbx, rax, x;            \
        adcx    low, rax;               \
        adox    high, rbx

S2N_BN_SYMBOL(bignum_mul_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save more registers to play with and make temporary space on stack

        CFI_PUSH(rbp)
        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(64)

// Copy y into a safe register to start with

        mov     y, rdx

// Clone of the main body of bignum_8_16, writing back the low 8 words to
// the temporary buffer on the stack and keeping the top half in r15,...,r8

        xor    ebp,ebp
        mov    rdx, [y]
        mulx   r9, r8, [x]
        mov    [rsp], r8
        mulx   r10, rbx, [x+0x8]
        adc    r9, rbx
        mulx   r11, rbx, [x+0x10]
        adc    r10, rbx
        mulx   r12, rbx, [x+0x18]
        adc    r11, rbx
        mulx   r13, rbx, [x+0x20]
        adc    r12, rbx
        mulx   r14, rbx, [x+0x28]
        adc    r13, rbx
        mulx   r15, rbx, [x+0x30]
        adc    r14, rbx
        mulx   r8, rbx, [x+0x38]
        adc    r15, rbx
        adc    r8, rbp
        mov    rdx, [y+0x8]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r9, rax
        adox   r10, rbx
        mov    [rsp+0x8], r9
        mulx   rbx, rax, [x+0x8]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r15, rax
        adox   r8, rbx
        mulx   r9, rax, [x+0x38]
        adcx   r8, rax
        adox   r9, rbp
        adc    r9, rbp
        mov    rdx, [y+0x10]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r10, rax
        adox   r11, rbx
        mov    [rsp+0x10], r10
        mulx   rbx, rax, [x+0x8]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r8, rax
        adox   r9, rbx
        mulx   r10, rax, [x+0x38]
        adcx   r9, rax
        adox   r10, rbp
        adc    r10, rbp
        mov    rdx, [y+0x18]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r11, rax
        adox   r12, rbx
        mov    [rsp+0x18], r11
        mulx   rbx, rax, [x+0x8]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r9, rax
        adox   r10, rbx
        mulx   r11, rax, [x+0x38]
        adcx   r10, rax
        adox   r11, rbp
        adc    r11, rbp
        mov    rdx, [y+0x20]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r12, rax
        adox   r13, rbx
        mov    [rsp+0x20], r12
        mulx   rbx, rax, [x+0x8]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r10, rax
        adox   r11, rbx
        mulx   r12, rax, [x+0x38]
        adcx   r11, rax
        adox   r12, rbp
        adc    r12, rbp
        mov    rdx, [y+0x28]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r13, rax
        adox   r14, rbx
        mov    [rsp+0x28], r13
        mulx   rbx, rax, [x+0x8]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r11, rax
        adox   r12, rbx
        mulx   r13, rax, [x+0x38]
        adcx   r12, rax
        adox   r13, rbp
        adc    r13, rbp
        mov    rdx, [y+0x30]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r14, rax
        adox   r15, rbx
        mov    [rsp+0x30], r14
        mulx   rbx, rax, [x+0x8]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r12, rax
        adox   r13, rbx
        mulx   r14, rax, [x+0x38]
        adcx   r13, rax
        adox   r14, rbp
        adc    r14, rbp
        mov    rdx, [y+0x38]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r15, rax
        adox   r8, rbx
        mov    [rsp+0x38], r15
        mulx   rbx, rax, [x+0x8]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r13, rax
        adox   r14, rbx
        mulx   r15, rax, [x+0x38]
        adcx   r14, rax
        adox   r15, rbp
        adc    r15, rbp

// Accumulate x[8] * y[0..7], extending the window to rbp,r15,...,r8

        mov     rdx, [x+64]
        xor     ebp, ebp
        mulpadd(r9,r8,[y])
        mulpadd(r10,r9,[y+8])
        mulpadd(r11,r10,[y+16])
        mulpadd(r12,r11,[y+24])
        mulpadd(r13,r12,[y+32])
        mulpadd(r14,r13,[y+40])
        mulpadd(r15,r14,[y+48])
        mulx    rbx, rax, [y+56]
        adcx    r15, rax
        adox    rbx, rbp
        adc     rbp, rbx

// Accumulate y[8] * x[0..8] within this extended window rbp,r15,...,r8

        mov     rdx, [y+64]
        xor     eax, eax
        mulpadd(r9,r8,[x])
        mulpadd(r10,r9,[x+8])
        mulpadd(r11,r10,[x+16])
        mulpadd(r12,r11,[x+24])
        mulpadd(r13,r12,[x+32])
        mulpadd(r14,r13,[x+40])
        mulpadd(r15,r14,[x+48])
        mulx    rbx, rax, [x+56]
        adcx    r15, rax
        adox    rbp, rbx
        mulx    rbx, rax, [x+64]
        adc     rbp, rax

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
        CFI_POP(rbx)
        CFI_POP(rbp)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_mul_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
