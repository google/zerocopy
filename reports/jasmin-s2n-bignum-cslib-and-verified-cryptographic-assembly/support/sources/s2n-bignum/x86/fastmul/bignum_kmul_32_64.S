// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[32], y[32]; output z[64]; temporary buffer t[>=96]
//
//    extern void bignum_kmul_32_64(uint64_t z[static 64],
//                                  const uint64_t x[static 32],
//                                  const uint64_t y[static 32],
//                                  uint64_t t[static 96]);
//
// This is a Karatsuba-style function multiplying half-sized results
// internally and using temporary buffer t for intermediate results. The size
// of 96 is an overstatement for compatibility with the ARM version; it
// actually only uses 65 elements of t (64 + 1 for a stashed sign).
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y, RCX = t
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y, R9 = t
// -----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_kmul_32_64)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_kmul_32_64)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_kmul_32_64)


        .text

#define K 16

#define z rdi
#define x rsi
#define y rcx

#define s r9

// We re-use the y variable to point at t later on, when this seems clearer

#define t rcx

S2N_BN_SYMBOL(bignum_kmul_32_64):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Save callee-saved registers and also push t onto the stack; we'll
// use this space to back up both t and later z. Then move the y variable
// into its longer-term home for the first few stages.

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_PUSH(rcx)
        mov     y, rdx

// Multiply the low halves

        CFI_CALL(Lbignum_kmul_32_64_local_bignum_kmul_16_32)

// Multiply the high halves

        lea     rdi,[rdi+16*K-0x40]
        lea     rsi,[rsi+8*K-0x40]
        lea     rcx,[rcx+8*K]
        CFI_CALL(Lbignum_kmul_32_64_local_bignum_kmul_16_32)

// Establish r8 as the t pointer and use the cell to back up z now

        mov     r8, [rsp]
        sub     rdi, 16*K+0x40
        mov     [rsp], rdi

// Form |x_lo - x_hi| starting at t

        mov     rax, [rsi-8*K-0x40]
        sub     rax, [rsi-8*K-0x40+8*K]
        mov     [r8], rax
        .set I,  1
        .rep K-1
        mov     rax, [rsi-8*K-0x40+8*I]
        sbb     rax, [rsi-8*K-0x40+8*K+8*I]
        mov     [r8+8*I], rax
        .set I,  (I+1)
        .endr

        mov     ebx, 0
        sbb     s, s          // Maintain CF, set ZF for cmovs, record sign

        .set I,  0
        .rep K
        mov     rdx, [r8+8*I]
        mov     rax, rdx
        not     rdx
        cmovz   rdx, rax
        adcx    rdx, rbx
        mov     [r8+8*I], rdx
        .set I,  (I+1)
        .endr

// Form |y_hi - y_lo| (note opposite order) starting at t[K]

        mov     rax, [rcx-8*K+8*K]
        sub     rax, [rcx-8*K]
        mov     [r8+8*K], rax
        .set I,  1
        .rep K-1
        mov     rax, [rcx-8*K+8*K+8*I]
        sbb     rax, [rcx-8*K+8*I]
        mov     [r8+8*K+8*I], rax
        .set I,  (I+1)
        .endr

        mov     ebx, 0
        sbb     rbp, rbp                // Maintain CF, set ZF for cmovs

        .set I,  0
        .rep K
        mov     rdx, [r8+8*K+8*I]
        mov     rax, rdx
        not     rdx
        cmovz   rdx, rax
        adcx    rdx, rbx
        mov     [r8+8*K+8*I], rdx
        .set I,  (I+1)
        .endr

// Stash the final sign with which to add things at t[4*K]

        xor     s, rbp
        mov     [r8+32*K], s

// Multiply the absolute differences, putting the result at t[2*K]
// This has the side-effect of putting t in the "right" register rcx
// so after the load of z, we have both z and t pointers straight.

        mov     rcx, r8
        lea     rsi, [r8+8*K]
        lea     rdi, [r8+16*K]
        CFI_CALL(Lbignum_kmul_32_64_local_bignum_kmul_16_32)
        mov     z, [rsp]

// Compose the middle parts [2,1] + [1,0] + [3,2], saving carry in rbx.
// Put the sum at t, overwriting the absolute differences we no longer need.

        xor     ebx, ebx
        .set I,  0
        .rep 2*K
        mov     rax, [z+8*K+8*I]
        adcx    rax, [z+8*I]
        adox    rax, [z+16*K+8*I]
        mov     [t+8*I], rax
        .set I,  (I+1)
        .endr
        adox    rbx, rbx
        adc     rbx, 0

// Sign-aware addition or subtraction of the complicated term.
// We double-negate it to set CF/ZF while not spoiling its
// actual form: note that we eventually adcx to it below.

        mov     s, [t+32*K]
        neg     s
        neg     s

        .set I,  0
        .rep 2*K
        mov     rdx, [t+16*K+8*I]
        mov     rax, rdx
        not     rdx
        cmovz   rdx, rax
        adcx    rdx, [t+8*I]
        mov     [z+8*K+8*I], rdx
        .set I,  (I+1)
        .endr

// Bump the accumulated carry. This must end up >= 0 because it's the top
// word of a value of the form ... + h * h' + l * l' - (h - l) * (h' - l') >= 0

        adcx    rbx, s

// Finally propagate the carry to the top part

        xor     eax, eax
        add     [z+24*K],rbx
        .set I,  1
        .rep K-1
        adc     [z+24*K+8*I], rax
        .set I,  (I+1)
        .endr

// Restore and return. The first pop is not needed for the ABI but
// we need to adjust the stack anyway so it seems reasonable.

        CFI_POP(rcx)

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

// Local copy of half-length subroutine. This has a slightly different
// interface, expecting y argument in rcx directly, and not doing any
// save-restore of the other registers. It naturally moves z and x on by
// 0x40, which we compensate for when it is called by adjusting offsets.

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lbignum_kmul_32_64_local_bignum_kmul_16_32)

Lbignum_kmul_32_64_local_bignum_kmul_16_32:
        CFI_START
        mov    rdx, [rcx]
        xor    ebp, ebp
        mulx   r9, rax, [rsi]
        mov    [rdi], rax
        mulx   r10, rax, [rsi+0x8]
        adcx   r9, rax
        mulx   r11, rax, [rsi+0x10]
        adcx   r10, rax
        mulx   r12, rax, [rsi+0x18]
        adcx   r11, rax
        mulx   r13, rax, [rsi+0x20]
        adcx   r12, rax
        mulx   r14, rax, [rsi+0x28]
        adcx   r13, rax
        mulx   r15, rax, [rsi+0x30]
        adcx   r14, rax
        mulx   r8, rax, [rsi+0x38]
        adcx   r15, rax
        adc    r8, rbp
        mov    rdx, [rcx+0x8]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r9, rax
        adox   r10, rbx
        mov    [rdi+0x8], r9
        mulx   rbx, rax, [rsi+0x8]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r15, rax
        adox   r8, rbx
        mulx   r9, rax, [rsi+0x38]
        adcx   r8, rax
        adox   r9, rbp
        adc    r9, rbp
        mov    rdx, [rcx+0x10]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r10, rax
        adox   r11, rbx
        mov    [rdi+0x10], r10
        mulx   rbx, rax, [rsi+0x8]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r8, rax
        adox   r9, rbx
        mulx   r10, rax, [rsi+0x38]
        adcx   r9, rax
        adox   r10, rbp
        adc    r10, rbp
        mov    rdx, [rcx+0x18]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r11, rax
        adox   r12, rbx
        mov    [rdi+0x18], r11
        mulx   rbx, rax, [rsi+0x8]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r9, rax
        adox   r10, rbx
        mulx   r11, rax, [rsi+0x38]
        adcx   r10, rax
        adox   r11, rbp
        adc    r11, rbp
        mov    rdx, [rcx+0x20]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r12, rax
        adox   r13, rbx
        mov    [rdi+0x20], r12
        mulx   rbx, rax, [rsi+0x8]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r10, rax
        adox   r11, rbx
        mulx   r12, rax, [rsi+0x38]
        adcx   r11, rax
        adox   r12, rbp
        adc    r12, rbp
        mov    rdx, [rcx+0x28]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r13, rax
        adox   r14, rbx
        mov    [rdi+0x28], r13
        mulx   rbx, rax, [rsi+0x8]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r11, rax
        adox   r12, rbx
        mulx   r13, rax, [rsi+0x38]
        adcx   r12, rax
        adox   r13, rbp
        adc    r13, rbp
        mov    rdx, [rcx+0x30]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r14, rax
        adox   r15, rbx
        mov    [rdi+0x30], r14
        mulx   rbx, rax, [rsi+0x8]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r12, rax
        adox   r13, rbx
        mulx   r14, rax, [rsi+0x38]
        adcx   r13, rax
        adox   r14, rbp
        adc    r14, rbp
        mov    rdx, [rcx+0x38]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r15, rax
        adox   r8, rbx
        mov    [rdi+0x38], r15
        mulx   rbx, rax, [rsi+0x8]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r13, rax
        adox   r14, rbx
        mulx   r15, rax, [rsi+0x38]
        adcx   r14, rax
        adox   r15, rbp
        adc    r15, rbp
        mov    rdx, [rcx+0x40]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r8, rax
        adox   r9, rbx
        mov    [rdi+0x40], r8
        mulx   rbx, rax, [rsi+0x8]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r14, rax
        adox   r15, rbx
        mulx   r8, rax, [rsi+0x38]
        adcx   r15, rax
        adox   r8, rbp
        adc    r8, rbp
        mov    rdx, [rcx+0x48]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r9, rax
        adox   r10, rbx
        mov    [rdi+0x48], r9
        mulx   rbx, rax, [rsi+0x8]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r15, rax
        adox   r8, rbx
        mulx   r9, rax, [rsi+0x38]
        adcx   r8, rax
        adox   r9, rbp
        adc    r9, rbp
        mov    rdx, [rcx+0x50]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r10, rax
        adox   r11, rbx
        mov    [rdi+0x50], r10
        mulx   rbx, rax, [rsi+0x8]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r8, rax
        adox   r9, rbx
        mulx   r10, rax, [rsi+0x38]
        adcx   r9, rax
        adox   r10, rbp
        adc    r10, rbp
        mov    rdx, [rcx+0x58]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r11, rax
        adox   r12, rbx
        mov    [rdi+0x58], r11
        mulx   rbx, rax, [rsi+0x8]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r9, rax
        adox   r10, rbx
        mulx   r11, rax, [rsi+0x38]
        adcx   r10, rax
        adox   r11, rbp
        adc    r11, rbp
        mov    rdx, [rcx+0x60]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r12, rax
        adox   r13, rbx
        mov    [rdi+0x60], r12
        mulx   rbx, rax, [rsi+0x8]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r10, rax
        adox   r11, rbx
        mulx   r12, rax, [rsi+0x38]
        adcx   r11, rax
        adox   r12, rbp
        adc    r12, rbp
        mov    rdx, [rcx+0x68]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r13, rax
        adox   r14, rbx
        mov    [rdi+0x68], r13
        mulx   rbx, rax, [rsi+0x8]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r11, rax
        adox   r12, rbx
        mulx   r13, rax, [rsi+0x38]
        adcx   r12, rax
        adox   r13, rbp
        adc    r13, rbp
        mov    rdx, [rcx+0x70]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r14, rax
        adox   r15, rbx
        mov    [rdi+0x70], r14
        mulx   rbx, rax, [rsi+0x8]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r12, rax
        adox   r13, rbx
        mulx   r14, rax, [rsi+0x38]
        adcx   r13, rax
        adox   r14, rbp
        adc    r14, rbp
        mov    rdx, [rcx+0x78]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r15, rax
        adox   r8, rbx
        mov    [rdi+0x78], r15
        mulx   rbx, rax, [rsi+0x8]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r13, rax
        adox   r14, rbx
        mulx   r15, rax, [rsi+0x38]
        adcx   r14, rax
        adox   r15, rbp
        adc    r15, rbp
        mov    [rdi+0x80], r8
        mov    [rdi+0x88], r9
        mov    [rdi+0x90], r10
        mov    [rdi+0x98], r11
        mov    [rdi+0xa0], r12
        mov    [rdi+0xa8], r13
        mov    [rdi+0xb0], r14
        mov    [rdi+0xb8], r15
        add    rdi, 0x40
        add    rsi, 0x40
        mov    rdx, [rcx]
        xor    ebp, ebp
        mov    r8, [rdi]
        mov    r9, [rdi+0x8]
        mulx   rbx, rax, [rsi]
        adcx   r8, rax
        adox   r9, rbx
        mov    [rdi], r8
        mov    r10, [rdi+0x10]
        mulx   rbx, rax, [rsi+0x8]
        adcx   r9, rax
        adox   r10, rbx
        mov    r11, [rdi+0x18]
        mulx   rbx, rax, [rsi+0x10]
        adcx   r10, rax
        adox   r11, rbx
        mov    r12, [rdi+0x20]
        mulx   rbx, rax, [rsi+0x18]
        adcx   r11, rax
        adox   r12, rbx
        mov    r13, [rdi+0x28]
        mulx   rbx, rax, [rsi+0x20]
        adcx   r12, rax
        adox   r13, rbx
        mov    r14, [rdi+0x30]
        mulx   rbx, rax, [rsi+0x28]
        adcx   r13, rax
        adox   r14, rbx
        mov    r15, [rdi+0x38]
        mulx   rbx, rax, [rsi+0x30]
        adcx   r14, rax
        adox   r15, rbx
        mulx   r8, rax, [rsi+0x38]
        adcx   r15, rax
        adox   r8, rbp
        adcx   r8, rbp
        mov    rdx, [rcx+0x8]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r9, rax
        adox   r10, rbx
        mov    [rdi+0x8], r9
        mulx   rbx, rax, [rsi+0x8]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r15, rax
        adox   r8, rbx
        mulx   r9, rax, [rsi+0x38]
        adcx   r8, rax
        adox   r9, rbp
        adc    r9, rbp
        mov    rdx, [rcx+0x10]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r10, rax
        adox   r11, rbx
        mov    [rdi+0x10], r10
        mulx   rbx, rax, [rsi+0x8]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r8, rax
        adox   r9, rbx
        mulx   r10, rax, [rsi+0x38]
        adcx   r9, rax
        adox   r10, rbp
        adc    r10, rbp
        mov    rdx, [rcx+0x18]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r11, rax
        adox   r12, rbx
        mov    [rdi+0x18], r11
        mulx   rbx, rax, [rsi+0x8]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r9, rax
        adox   r10, rbx
        mulx   r11, rax, [rsi+0x38]
        adcx   r10, rax
        adox   r11, rbp
        adc    r11, rbp
        mov    rdx, [rcx+0x20]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r12, rax
        adox   r13, rbx
        mov    [rdi+0x20], r12
        mulx   rbx, rax, [rsi+0x8]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r10, rax
        adox   r11, rbx
        mulx   r12, rax, [rsi+0x38]
        adcx   r11, rax
        adox   r12, rbp
        adc    r12, rbp
        mov    rdx, [rcx+0x28]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r13, rax
        adox   r14, rbx
        mov    [rdi+0x28], r13
        mulx   rbx, rax, [rsi+0x8]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r11, rax
        adox   r12, rbx
        mulx   r13, rax, [rsi+0x38]
        adcx   r12, rax
        adox   r13, rbp
        adc    r13, rbp
        mov    rdx, [rcx+0x30]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r14, rax
        adox   r15, rbx
        mov    [rdi+0x30], r14
        mulx   rbx, rax, [rsi+0x8]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r12, rax
        adox   r13, rbx
        mulx   r14, rax, [rsi+0x38]
        adcx   r13, rax
        adox   r14, rbp
        adc    r14, rbp
        mov    rdx, [rcx+0x38]
        xor    ebp, ebp
        mulx   rbx, rax, [rsi]
        adcx   r15, rax
        adox   r8, rbx
        mov    [rdi+0x38], r15
        mulx   rbx, rax, [rsi+0x8]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r13, rax
        adox   r14, rbx
        mulx   r15, rax, [rsi+0x38]
        adcx   r14, rax
        adox   r15, rbp
        adc    r15, rbp
        mov    rdx, [rcx+0x40]
        xor    ebp, ebp
        adox   r8, [rdi+0x40]
        mulx   rbx, rax, [rsi]
        adcx   r8, rax
        adox   r9, rbx
        mov    [rdi+0x40], r8
        mulx   rbx, rax, [rsi+0x8]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r14, rax
        adox   r15, rbx
        mulx   r8, rax, [rsi+0x38]
        adcx   r15, rax
        adox   r8, rbp
        adc    r8, rbp
        mov    rdx, [rcx+0x48]
        xor    ebp, ebp
        adox   r9, [rdi+0x48]
        mulx   rbx, rax, [rsi]
        adcx   r9, rax
        adox   r10, rbx
        mov    [rdi+0x48], r9
        mulx   rbx, rax, [rsi+0x8]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r15, rax
        adox   r8, rbx
        mulx   r9, rax, [rsi+0x38]
        adcx   r8, rax
        adox   r9, rbp
        adc    r9, rbp
        mov    rdx, [rcx+0x50]
        xor    ebp, ebp
        adox   r10, [rdi+0x50]
        mulx   rbx, rax, [rsi]
        adcx   r10, rax
        adox   r11, rbx
        mov    [rdi+0x50], r10
        mulx   rbx, rax, [rsi+0x8]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r8, rax
        adox   r9, rbx
        mulx   r10, rax, [rsi+0x38]
        adcx   r9, rax
        adox   r10, rbp
        adc    r10, rbp
        mov    rdx, [rcx+0x58]
        xor    ebp, ebp
        adox   r11, [rdi+0x58]
        mulx   rbx, rax, [rsi]
        adcx   r11, rax
        adox   r12, rbx
        mov    [rdi+0x58], r11
        mulx   rbx, rax, [rsi+0x8]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r9, rax
        adox   r10, rbx
        mulx   r11, rax, [rsi+0x38]
        adcx   r10, rax
        adox   r11, rbp
        adc    r11, rbp
        mov    rdx, [rcx+0x60]
        xor    ebp, ebp
        adox   r12, [rdi+0x60]
        mulx   rbx, rax, [rsi]
        adcx   r12, rax
        adox   r13, rbx
        mov    [rdi+0x60], r12
        mulx   rbx, rax, [rsi+0x8]
        adcx   r13, rax
        adox   r14, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r10, rax
        adox   r11, rbx
        mulx   r12, rax, [rsi+0x38]
        adcx   r11, rax
        adox   r12, rbp
        adc    r12, rbp
        mov    rdx, [rcx+0x68]
        xor    ebp, ebp
        adox   r13, [rdi+0x68]
        mulx   rbx, rax, [rsi]
        adcx   r13, rax
        adox   r14, rbx
        mov    [rdi+0x68], r13
        mulx   rbx, rax, [rsi+0x8]
        adcx   r14, rax
        adox   r15, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r11, rax
        adox   r12, rbx
        mulx   r13, rax, [rsi+0x38]
        adcx   r12, rax
        adox   r13, rbp
        adc    r13, rbp
        mov    rdx, [rcx+0x70]
        xor    ebp, ebp
        adox   r14, [rdi+0x70]
        mulx   rbx, rax, [rsi]
        adcx   r14, rax
        adox   r15, rbx
        mov    [rdi+0x70], r14
        mulx   rbx, rax, [rsi+0x8]
        adcx   r15, rax
        adox   r8, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r12, rax
        adox   r13, rbx
        mulx   r14, rax, [rsi+0x38]
        adcx   r13, rax
        adox   r14, rbp
        adc    r14, rbp
        mov    rdx, [rcx+0x78]
        xor    ebp, ebp
        adox   r15, [rdi+0x78]
        mulx   rbx, rax, [rsi]
        adcx   r15, rax
        adox   r8, rbx
        mov    [rdi+0x78], r15
        mulx   rbx, rax, [rsi+0x8]
        adcx   r8, rax
        adox   r9, rbx
        mulx   rbx, rax, [rsi+0x10]
        adcx   r9, rax
        adox   r10, rbx
        mulx   rbx, rax, [rsi+0x18]
        adcx   r10, rax
        adox   r11, rbx
        mulx   rbx, rax, [rsi+0x20]
        adcx   r11, rax
        adox   r12, rbx
        mulx   rbx, rax, [rsi+0x28]
        adcx   r12, rax
        adox   r13, rbx
        mulx   rbx, rax, [rsi+0x30]
        adcx   r13, rax
        adox   r14, rbx
        mulx   r15, rax, [rsi+0x38]
        adcx   r14, rax
        adox   r15, rbp
        adc    r15, rbp
        mov    [rdi+0x80], r8
        mov    [rdi+0x88], r9
        mov    [rdi+0x90], r10
        mov    [rdi+0x98], r11
        mov    [rdi+0xa0], r12
        mov    [rdi+0xa8], r13
        mov    [rdi+0xb0], r14
        mov    [rdi+0xb8], r15
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lbignum_kmul_32_64_local_bignum_kmul_16_32)

S2N_BN_SIZE_DIRECTIVE(bignum_kmul_32_64)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
