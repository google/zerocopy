// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square, z := x^2
// Input x[32]; output z[64]; temporary buffer t[>=72]
//
//    extern void bignum_ksqr_32_64(uint64_t z[static 64],
//                                  const uint64_t x[static 32],
//                                  uint64_t t[static 72]);
//
// This is a Karatsuba-style function squaring half-sized results
// and using temporary buffer t for intermediate results. The size of 72
// is an overstatement for compatibility with the ARM version; it actually
// only uses 65 elements of t (64 + 1 for a suspended carry).
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = t
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = t
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_ksqr_32_64)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_ksqr_32_64)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_ksqr_32_64)

        .text

#define K 16

#define z rdi
#define x rsi
#define t rcx

S2N_BN_SYMBOL(bignum_ksqr_32_64):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save callee-preserved registers once and for all at the outset
// Later we further reshuffle the input arguments to avoid extra saves

        CFI_PUSH(rbp)
        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Move the temp space pointer since we need rdx for multiplications

        mov     t, rdx

// Square the low half

        CFI_CALL(Lbignum_ksqr_32_64_local_bignum_sqr_16_32)

// Square the high half; from here on x and z are modified

        lea     x,[x+8*K]               // input at x+8*K
        lea     z,[z+16*K]             // result at z+16*K
        CFI_CALL(Lbignum_ksqr_32_64_local_bignum_sqr_16_32)

// Form |x_lo - x_hi|, stored at t

        mov     rax, [x-8*K]
        sub     rax, [x]
        mov     [t], rax
        .set I,  1
        .rep K-1
        mov     rax, [x-8*K+8*I]
        sbb     rax, [x+8*I]
        mov     [t+8*I], rax
        .set I,  (I+1)
        .endr

        mov     ebx, 0
        sbb     rax, rax                // Maintain CF, set ZF for cmovs

        .set I,  0
        .rep K
        mov     rdx, [t+8*I]
        mov     rax, rdx
        not     rdx
        adcx    rdx, rbx
        cmovz   rdx, rax
        mov     [t+8*I], rdx
        .set I,  (I+1)
        .endr

// Compose the middle parts [2,1] + [1,0] + [3,2]
// Put the low half of this at t[K] and the top half in place at z[2*K]; a
// fully in-place version is awkward with the otherwise beneficial double
// carry chain. Stash the carry suspended from the 3k position at the end of
// the temp buffer t[4*K].

        xor     edx, edx
        .set I,  0
        .rep K
        mov     rax, [z-16*K+8*K+8*I]
        adcx    rax, [z-16*K+8*I]
        adox    rax, [z-16*K+16*K+8*I]
        mov     [t+8*K+8*I], rax
        .set I,  (I+1)
        .endr

        .rep K
        mov     rax, [z-16*K+8*K+8*I]
        adcx    rax, [z-16*K+8*I]
        adox    rax, [z-16*K+16*K+8*I]
        mov     [z-16*K+8*K+8*I], rax
        .set I,  (I+1)
        .endr

        adox    rdx, rdx
        adc     rdx, 0
        mov     [t+32*K], rdx

// Square the absolute difference, putting the result M at t[2*K].
// This involves another shuffle so now t' = z_orig and x' = t_orig
// while z' points within the temp buffer to the product M itself

        mov     x, t
        lea     t, [z-16*K]
        lea     z, [x+16*K]
        CFI_CALL(Lbignum_ksqr_32_64_local_bignum_sqr_16_32)

// Subtract M, pausing at the 3k position to bump down accumulated carry.
// The carry cannot go negative since it's the top word of a value
// of the form ... + h^2 + l^2 - (h - l)^2 >= 0

        mov     rax, [x+8*K]
        sub     rax, [z]
        mov     [t+8*K], rax

        .set I,  1

        .rep (K-1)
        mov     rax, [x+8*K+8*I]
        sbb     rax, [z+8*I]
        mov     [t+8*K+8*I], rax
        .set I,  (I+1)
        .endr

        .rep K
        mov     rax, [t+8*K+8*I]
        sbb     rax, [z+8*I]
        mov     [t+8*K+8*I], rax
        .set I,  (I+1)
        .endr

        mov     rdx, [x+32*K]
        sbb     rdx, 0

// Finally propagate the carry to the top quarter

        xor     eax, eax
        add     [t+24*K],rdx
        .set I,  1
        .rep K-1
        adc     [t+24*K+8*I], rax
        .set I,  (I+1)
        .endr

// Restore registers and return

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

// Local copy of the half-length subroutine

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lbignum_ksqr_32_64_local_bignum_sqr_16_32)

Lbignum_ksqr_32_64_local_bignum_sqr_16_32:
        CFI_START
        xor    ebp, ebp
        mov    rdx, [x]
        mulx   rax, r9, [x+0x8]
        mov    [z+0x8], r9
        mulx   rbx, r10, [x+0x10]
        adcx   r10, rax
        mov    [z+0x10], r10
        mulx   rax, r11, [x+0x18]
        adcx   r11, rbx
        mulx   rbx, r12, [x+0x20]
        adcx   r12, rax
        mulx   rax, r13, [x+0x28]
        adcx   r13, rbx
        mulx   rbx, r14, [x+0x30]
        adcx   r14, rax
        mulx   r8, r15, [x+0x38]
        adcx   r15, rbx
        adcx   r8, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x8]
        mulx   rbx, rax, [x+0x10]
        adcx   r11, rax
        adox   r12, rbx
        mov    [z+0x18], r11
        mulx   rbx, rax, [x+0x18]
        adcx   r12, rax
        adox   r13, rbx
        mov    [z+0x20], r12
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
        mov    rdx, [x+0x20]
        mulx   r10, rax, [x+0x28]
        adcx   r9, rax
        adox   r10, rbp
        adcx   r10, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x10]
        mulx   rbx, rax, [x+0x18]
        adcx   r13, rax
        adox   r14, rbx
        mov    [z+0x28], r13
        mulx   rbx, rax, [x+0x20]
        adcx   r14, rax
        adox   r15, rbx
        mov    [z+0x30], r14
        mulx   rbx, rax, [x+0x28]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x38]
        adcx   r9, rax
        adox   r10, rbx
        mov    rdx, [x+0x30]
        mulx   r11, rax, [x+0x20]
        adcx   r10, rax
        adox   r11, rbp
        mulx   r12, rax, [x+0x28]
        adcx   r11, rax
        adox   r12, rbp
        adcx   r12, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x18]
        mulx   rbx, rax, [x+0x20]
        adcx   r15, rax
        adox   r8, rbx
        mov    [z+0x38], r15
        mulx   rbx, rax, [x+0x28]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x30]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x38]
        adcx   r10, rax
        adox   r11, rbx
        mov    rdx, [x+0x38]
        mulx   rbx, rax, [x+0x20]
        adcx   r11, rax
        adox   r12, rbx
        mulx   r13, rax, [x+0x28]
        adcx   r12, rax
        adox   r13, rbp
        mulx   r14, rax, [x+0x30]
        adcx   r13, rax
        adox   r14, rbp
        adcx   r14, rbp
        mov    rdx, [x+0x40]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r8, rax
        adox   r9, rbx
        mov    [z+0x40], r8
        mulx   rbx, rax, [x+0x8]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x10]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [x+0x18]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x20]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x28]
        adcx   r13, rax
        adox   r14, rbx
        mulx   r15, rax, [x+0x30]
        adcx   r14, rax
        adox   r15, rbp
        mulx   r8, rax, [x+0x38]
        adcx   r15, rax
        adox   r8, rbp
        adcx   r8, rbp
        mov    rdx, [x+0x48]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r9, rax
        adox   r10, rbx
        mov    [z+0x48], r9
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
        adcx   r9, rbp
        mov    rdx, [x+0x50]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r10, rax
        adox   r11, rbx
        mov    [z+0x50], r10
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
        adcx   r10, rbp
        mov    rdx, [x+0x58]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r11, rax
        adox   r12, rbx
        mov    [z+0x58], r11
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
        adcx   r11, rbp
        mov    rdx, [x+0x60]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r12, rax
        adox   r13, rbx
        mov    [z+0x60], r12
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
        adcx   r12, rbp
        mov    rdx, [x+0x68]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r13, rax
        adox   r14, rbx
        mov    [z+0x68], r13
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
        adcx   r13, rbp
        mov    rdx, [x+0x70]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r14, rax
        adox   r15, rbx
        mov    [z+0x70], r14
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
        adcx   r14, rbp
        mov    rdx, [x+0x78]
        xor    ebp, ebp
        mulx   rbx, rax, [x]
        adcx   r15, rax
        adox   r8, rbx
        mov    [z+0x78], r15
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
        adcx   r15, rbp
        mov    [z+0x80], r8
        mov    [z+0x88], r9
        mov    [z+0x90], r10
        mov    [z+0x98], r11
        mov    [z+0xa0], r12
        mov    [z+0xa8], r13
        mov    [z+0xb0], r14
        mov    [z+0xb8], r15
        xor    ebp, ebp
        mov    r9, [z+0x88]
        mov    r10, [z+0x90]
        mov    r11, [z+0x98]
        mov    r12, [z+0xa0]
        mov    r13, [z+0xa8]
        mov    r14, [z+0xb0]
        mov    r15, [z+0xb8]
        mov    rdx, [x+0x40]
        mulx   rbx, rax, [x+0x48]
        adcx   r9, rax
        adox   r10, rbx
        mov    [z+0x88], r9
        mulx   rbx, rax, [x+0x50]
        adcx   r10, rax
        adox   r11, rbx
        mov    [z+0x90], r10
        mulx   rbx, rax, [x+0x58]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [x+0x60]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [x+0x68]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x70]
        adcx   r14, rax
        adox   r15, rbx
        mulx   r8, rax, [x+0x78]
        adcx   r15, rax
        adox   r8, rbp
        adcx   r8, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x48]
        mulx   rbx, rax, [x+0x50]
        adcx   r11, rax
        adox   r12, rbx
        mov    [z+0x98], r11
        mulx   rbx, rax, [x+0x58]
        adcx   r12, rax
        adox   r13, rbx
        mov    [z+0xa0], r12
        mulx   rbx, rax, [x+0x60]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [x+0x68]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [x+0x70]
        adcx   r15, rax
        adox   r8, rbx
        mulx   r9, rax, [x+0x78]
        adcx   r8, rax
        adox   r9, rbp
        mov    rdx, [x+0x60]
        mulx   r10, rax, [x+0x68]
        adcx   r9, rax
        adox   r10, rbp
        adcx   r10, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x50]
        mulx   rbx, rax, [x+0x58]
        adcx   r13, rax
        adox   r14, rbx
        mov    [z+0xa8], r13
        mulx   rbx, rax, [x+0x60]
        adcx   r14, rax
        adox   r15, rbx
        mov    [z+0xb0], r14
        mulx   rbx, rax, [x+0x68]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [x+0x70]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x78]
        adcx   r9, rax
        adox   r10, rbx
        mov    rdx, [x+0x70]
        mulx   r11, rax, [x+0x60]
        adcx   r10, rax
        adox   r11, rbp
        mulx   r12, rax, [x+0x68]
        adcx   r11, rax
        adox   r12, rbp
        adcx   r12, rbp
        xor    ebp, ebp
        mov    rdx, [x+0x58]
        mulx   rbx, rax, [x+0x60]
        adcx   r15, rax
        adox   r8, rbx
        mov    [z+0xb8], r15
        mulx   rbx, rax, [x+0x68]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [x+0x70]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [x+0x78]
        adcx   r10, rax
        adox   r11, rbx
        mov    rdx, [x+0x78]
        mulx   rbx, rax, [x+0x60]
        adcx   r11, rax
        adox   r12, rbx
        mulx   r13, rax, [x+0x68]
        adcx   r12, rax
        adox   r13, rbp
        mulx   r14, rax, [x+0x70]
        adcx   r13, rax
        adox   r14, rbp
        adcx   r14, rbp
        mov    [z+0xc0], r8
        mov    [z+0xc8], r9
        mov    [z+0xd0], r10
        mov    [z+0xd8], r11
        mov    [z+0xe0], r12
        mov    [z+0xe8], r13
        mov    [z+0xf0], r14
        xor    ebp, ebp
        mov    rdx, [x]
        mulx   rbx, rax, rdx
        mov    [z], rax
        mov    rdx, [z+0x8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x8], rdx
        mov    rdx, [x+0x8]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x10]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x10], rdx
        mov    rdx, [z+0x18]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x18], rdx
        mov    rdx, [x+0x10]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x20]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x20], rdx
        mov    rdx, [z+0x28]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x28], rdx
        mov    rdx, [x+0x18]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x30]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x30], rdx
        mov    rdx, [z+0x38]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x38], rdx
        mov    rdx, [x+0x20]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x40]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x40], rdx
        mov    rdx, [z+0x48]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x48], rdx
        mov    rdx, [x+0x28]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x50]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x50], rdx
        mov    rdx, [z+0x58]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x58], rdx
        mov    rdx, [x+0x30]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x60]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x60], rdx
        mov    rdx, [z+0x68]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x68], rdx
        mov    rdx, [x+0x38]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x70]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x70], rdx
        mov    rdx, [z+0x78]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x78], rdx
        mov    rdx, [x+0x40]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x80]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x80], rdx
        mov    rdx, [z+0x88]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x88], rdx
        mov    rdx, [x+0x48]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0x90]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0x90], rdx
        mov    rdx, [z+0x98]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0x98], rdx
        mov    rdx, [x+0x50]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xa0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xa0], rdx
        mov    rdx, [z+0xa8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0xa8], rdx
        mov    rdx, [x+0x58]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xb0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xb0], rdx
        mov    rdx, [z+0xb8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0xb8], rdx
        mov    rdx, [x+0x60]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xc0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xc0], rdx
        mov    rdx, [z+0xc8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0xc8], rdx
        mov    rdx, [x+0x68]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xd0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xd0], rdx
        mov    rdx, [z+0xd8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0xd8], rdx
        mov    rdx, [x+0x70]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xe0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xe0], rdx
        mov    rdx, [z+0xe8]
        adcx   rdx, rdx
        adox   rdx, rbx
        mov    [z+0xe8], rdx
        mov    rdx, [x+0x78]
        mulx   rbx, rax, rdx
        mov    rdx, [z+0xf0]
        adcx   rdx, rdx
        adox   rdx, rax
        mov    [z+0xf0], rdx
        adcx   rbx, rbp
        adox   rbx, rbp
        mov    [z+0xf8], rbx
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lbignum_ksqr_32_64_local_bignum_sqr_16_32)

S2N_BN_SIZE_DIRECTIVE(bignum_ksqr_32_64)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
