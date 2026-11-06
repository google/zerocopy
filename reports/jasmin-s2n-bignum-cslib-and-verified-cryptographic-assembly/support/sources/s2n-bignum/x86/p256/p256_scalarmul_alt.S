// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Scalar multiplication for P-256
// Input scalar[4], point[8]; output res[8]
//
// extern void p256_scalarmul_alt
//   (uint64_t res[static 8],const uint64_t scalar[static 4],
//     const uint64_t point[static 8]);
//
// Given scalar = n and point = P, assumed to be on the NIST elliptic
// curve P-256, returns the point (X,Y) = n * P. The input and output
// are affine points, and in the case of the point at infinity as
// the result, (0,0) is returned.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p256_scalarmul_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p256_scalarmul_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p256_scalarmul_alt)

        .text
        .balign 32

// Size of individual field elements

#define NUMSIZE 32

// Intermediate variables on the stack. The last z2, z3 values can
// safely be overlaid on the table, which is no longer needed at the end.
// Uppercase syntactic variants make x86_att version simpler to generate

#define SCALARB (0*NUMSIZE)
#define scalarb rsp+(0*NUMSIZE)
#define ACC (1*NUMSIZE)
#define acc rsp+(1*NUMSIZE)
#define TABENT (4*NUMSIZE)
#define tabent rsp+(4*NUMSIZE)

#define TAB (7*NUMSIZE)
#define tab rsp+(7*NUMSIZE)

#define Z2 (7*NUMSIZE)
#define z2 rsp+(7*NUMSIZE)
#define Z3 (8*NUMSIZE)
#define z3 rsp+(8*NUMSIZE)

#define res [rsp+(31*NUMSIZE)]

#define NSPACE 32*NUMSIZE

S2N_BN_SYMBOL(p256_scalarmul_alt):
        CFI_START
        _CET_ENDBR

// The Windows version literally calls the standard ABI version.
// This simplifies the proofs since subroutine offsets are fixed.

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        CFI_CALL(Lp256_scalarmul_alt_standard)
        CFI_POP(rsi)
        CFI_POP(rdi)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(p256_scalarmul_alt)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp256_scalarmul_alt_standard)

Lp256_scalarmul_alt_standard:
        CFI_START
#endif

// Real start of the standard ABI code.

        CFI_PUSH(r15)
        CFI_PUSH(r14)
        CFI_PUSH(r13)
        CFI_PUSH(r12)
        CFI_PUSH(rbp)
        CFI_PUSH(rbx)

        CFI_DEC_RSP(NSPACE)

// Preserve the "res" and "point" input arguments. We load and process the
// scalar immediately so we don't bother preserving that input argument.
// Also, "point" is only needed early on and so its register gets re-used.

        mov     rbx, rdx
        mov     res, rdi

// Load the digits of group order n_256 = [r15;r14;r13;r12]

        mov     r12, 0xf3b9cac2fc632551
        mov     r13, 0xbce6faada7179e84
        mov     r14, 0xffffffffffffffff
        mov     r15, 0xffffffff00000000

// First, reduce the input scalar mod n_256, i.e. conditionally subtract n_256

        mov     r8, [rsi]
        sub     r8, r12
        mov     r9, [rsi+8]
        sbb     r9, r13
        mov     r10, [rsi+16]
        sbb     r10, r14
        mov     r11, [rsi+24]
        sbb     r11, r15

        cmovc   r8, [rsi]
        cmovc   r9, [rsi+8]
        cmovc   r10, [rsi+16]
        cmovc   r11, [rsi+24]

// Now if the top bit of the reduced scalar is set, negate it mod n_256,
// i.e. do n |-> n_256 - n. Remember the sign in rbp so we can
// correspondingly negate the point below.

        sub     r12, r8
        sbb     r13, r9
        sbb     r14, r10
        sbb     r15, r11

        mov     rbp, r11
        shr     rbp, 63
        cmovnz  r8, r12
        cmovnz  r9, r13
        cmovnz  r10, r14
        cmovnz  r11, r15

// In either case then add the recoding constant 0x08888...888 to allow
// signed digits.

        mov     rax, 0x8888888888888888
        add     r8, rax
        adc     r9, rax
        adc     r10, rax
        adc     r11, rax
        btc     r11, 63

        mov     [rsp+SCALARB], r8
        mov     [rsp+SCALARB+8], r9
        mov     [rsp+SCALARB+16], r10
        mov     [rsp+SCALARB+24], r11

// Set the tab[0] table entry to Montgomery-Jacobian point = 1 * P
// The z coordinate is just the Montgomery form of the constant 1.

        lea     rdi, [rsp+TAB]
        mov     rsi, rbx
        CFI_CALL(Lp256_scalarmul_alt_local_tomont_p256)

        lea     rsi, [rbx+32]
        lea     rdi, [rsp+TAB+32]
        CFI_CALL(Lp256_scalarmul_alt_local_tomont_p256)

        mov     eax, 1
        mov     [rsp+TAB+64], rax
        mov     rdx, 0xffffffff00000000
        mov     [rsp+TAB+72], rdx
        sub     rax, 2
        mov     [rsp+TAB+80], rax
        mov     rax, 0x00000000fffffffe
        mov     [rsp+TAB+88], rax

// If the top bit of the scalar was set, negate (y coordinate of) the point

        mov     r12, [rsp+TAB+32]
        mov     r13, [rsp+TAB+40]
        mov     r14, [rsp+TAB+48]
        mov     r15, [rsp+TAB+56]

        xor     r10d, r10d
        lea     r8, [r10-1]
        mov     r11, 0x00000000ffffffff
        mov     r9, r11
        neg     r11

        sub     r8, r12
        sbb     r9, r13
        sbb     r10, r14
        sbb     r11, r15

        test    rbp, rbp
        cmovz   r8, r12
        cmovz   r9, r13
        cmovz   r10, r14
        cmovz   r11, r15

        mov     [rsp+TAB+32], r8
        mov     [rsp+TAB+40], r9
        mov     [rsp+TAB+48], r10
        mov     [rsp+TAB+56], r11

// Compute and record tab[1] = 2 * p, ..., tab[7] = 8 * P

        lea     rdi, [rsp+TAB+96*1]
        lea     rsi, [rsp+TAB]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjdouble)

        lea     rdi, [rsp+TAB+96*2]
        lea     rsi, [rsp+TAB+96*1]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjmixadd)

        lea     rdi, [rsp+TAB+96*3]
        lea     rsi, [rsp+TAB+96*1]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjdouble)

        lea     rdi, [rsp+TAB+96*4]
        lea     rsi, [rsp+TAB+96*3]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjmixadd)

        lea     rdi, [rsp+TAB+96*5]
        lea     rsi, [rsp+TAB+96*2]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjdouble)

        lea     rdi, [rsp+TAB+96*6]
        lea     rsi, [rsp+TAB+96*5]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjmixadd)

        lea     rdi, [rsp+TAB+96*7]
        lea     rsi, [rsp+TAB+96*3]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjdouble)

// Set up accumulator as table entry for top 4 bits (constant-time indexing)

        mov     rdi, [rsp+SCALARB+24]
        shr     rdi, 60

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        xor     r13d, r13d
        xor     r14d, r14d
        xor     r15d, r15d

        .set I, 1
.rep 8
        cmp     rdi, I

        cmovz   rax, [rsp+TAB+96*(I-1)]
        cmovz   rbx, [rsp+TAB+96*(I-1)+8]
        cmovz   rcx, [rsp+TAB+96*(I-1)+16]
        cmovz   rdx, [rsp+TAB+96*(I-1)+24]
        cmovz   r8, [rsp+TAB+96*(I-1)+32]
        cmovz   r9, [rsp+TAB+96*(I-1)+40]
        cmovz   r10, [rsp+TAB+96*(I-1)+48]
        cmovz   r11, [rsp+TAB+96*(I-1)+56]
        cmovz   r12, [rsp+TAB+96*(I-1)+64]
        cmovz   r13, [rsp+TAB+96*(I-1)+72]
        cmovz   r14, [rsp+TAB+96*(I-1)+80]
        cmovz   r15, [rsp+TAB+96*(I-1)+88]
        .set    I, (I+1)
.endr
        mov      [rsp+ACC], rax
        mov      [rsp+ACC+8], rbx
        mov      [rsp+ACC+16], rcx
        mov      [rsp+ACC+24], rdx
        mov      [rsp+ACC+32], r8
        mov      [rsp+ACC+40], r9
        mov      [rsp+ACC+48], r10
        mov      [rsp+ACC+56], r11
        mov      [rsp+ACC+64], r12
        mov      [rsp+ACC+72], r13
        mov      [rsp+ACC+80], r14
        mov      [rsp+ACC+88], r15

// Main loop over size-4 bitfield

        mov     ebp, 252

Lp256_scalarmul_alt_loop:
        sub     rbp, 4

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjdouble)

        mov     rax, rbp
        shr     rax, 6
        mov     rdi, [rsp+8*rax]
        mov     rcx, rbp
        shr     rdi, cl
        and     rdi, 15

        sub     rdi, 8
        sbb     rsi, rsi        // rsi = sign of digit (-1 = negative)
        xor     rdi, rsi
        sub     rdi, rsi        // rdi = absolute value of digit

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        xor     r13d, r13d
        xor     r14d, r14d
        xor     r15d, r15d

        .set I, 1
.rep 8
        cmp     rdi, I

        cmovz   rax, [rsp+TAB+96*(I-1)]
        cmovz   rbx, [rsp+TAB+96*(I-1)+8]
        cmovz   rcx, [rsp+TAB+96*(I-1)+16]
        cmovz   rdx, [rsp+TAB+96*(I-1)+24]
        cmovz   r8, [rsp+TAB+96*(I-1)+32]
        cmovz   r9, [rsp+TAB+96*(I-1)+40]
        cmovz   r10, [rsp+TAB+96*(I-1)+48]
        cmovz   r11, [rsp+TAB+96*(I-1)+56]
        cmovz   r12, [rsp+TAB+96*(I-1)+64]
        cmovz   r13, [rsp+TAB+96*(I-1)+72]
        cmovz   r14, [rsp+TAB+96*(I-1)+80]
        cmovz   r15, [rsp+TAB+96*(I-1)+88]
        .set    I, (I+1)
.endr

        mov      [rsp+TABENT+64], r12
        mov      [rsp+TABENT+72], r13
        mov      [rsp+TABENT+80], r14
        mov      [rsp+TABENT+88], r15

        xor     r14d, r14d
        lea     r12, [r14-1]
        mov     r15, 0x00000000ffffffff
        mov     r13, r15
        neg     r15

        sub     r12, r8
        sbb     r13, r9
        sbb     r14, r10
        sbb     r15, r11

        test     rsi, rsi
        cmovnz   r8, r12
        cmovnz   r9, r13
        cmovnz   r10, r14
        cmovnz   r11, r15

        mov      [rsp+TABENT], rax
        mov      [rsp+TABENT+8], rbx
        mov      [rsp+TABENT+16], rcx
        mov      [rsp+TABENT+24], rdx

        mov      [rsp+TABENT+32], r8
        mov      [rsp+TABENT+40], r9
        mov      [rsp+TABENT+48], r10
        mov      [rsp+TABENT+56], r11

        lea     rdx, [rsp+TABENT]
        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp256_scalarmul_alt_local_p256_montjadd)

        test    rbp, rbp
        jne     Lp256_scalarmul_alt_loop

// Let z2 = 1/z^2 and z3 = 1/z^3, both without Montgomery form

        lea     rdi, [rsp+Z2]
        lea     rsi, [rsp+ACC+64]
        CFI_CALL(Lp256_scalarmul_alt_local_montsqr_p256)

        lea     rdi, [rsp+Z3]
        lea     rsi, [rsp+ACC+64]
        lea     rdx, [rsp+Z2]
        CFI_CALL(Lp256_scalarmul_alt_local_montmul_p256)

        lea     rdi, [rsp+Z2]
        lea     rsi, [rsp+Z3]
        CFI_CALL(Lp256_scalarmul_alt_local_demont_p256)

        lea     rdi, [rsp+Z3]
        lea     rsi, [rsp+Z2]
        CFI_CALL(Lp256_scalarmul_alt_local_inv_p256)

        lea     rdi, [rsp+Z2]
        lea     rsi, [rsp+ACC+64]
        lea     rdx, [rsp+Z3]
        CFI_CALL(Lp256_scalarmul_alt_local_montmul_p256)

// Convert back from Jacobian (X, Y, Z) |-> (X/Z^2, Y/Z^3)

        mov     rdi, res
        lea     rsi, [rsp+ACC]
        lea     rdx, [rsp+Z2]
        mov     rbx, rdi
        CFI_CALL(Lp256_scalarmul_alt_local_montmul_p256)

        lea     rdi, [rbx+32]
        lea     rsi, [rsp+ACC+32]
        lea     rdx, [rsp+Z3]
        CFI_CALL(Lp256_scalarmul_alt_local_montmul_p256)

// Restore stack and registers and return

        CFI_INC_RSP(NSPACE)
        CFI_POP(rbx)
        CFI_POP(rbp)
        CFI_POP(r12)
        CFI_POP(r13)
        CFI_POP(r14)
        CFI_POP(r15)
        CFI_RET

#if WINDOWS_ABI
S2N_BN_SIZE_DIRECTIVE(Lp256_scalarmul_alt_standard)
#else
S2N_BN_SIZE_DIRECTIVE(p256_scalarmul_alt)
#endif

// Local copies of subroutines, complete clones at the moment

Lp256_scalarmul_alt_local_demont_p256:
        CFI_START
        mov     r8, [rsi]
        mov     r9, [rsi+0x8]
        mov     r10, [rsi+0x10]
        mov     r11, [rsi+0x18]
        movabs  rcx, 0x100000000
        mov     rax, r8
        mul     rcx
        add     r9, rax
        adc     r10, rdx
        sbb     rsi, rsi
        mov     rax, r9
        mul     rcx
        sub     rdx, rsi
        add     r10, rax
        adc     r11, rdx
        sbb     rsi, rsi
        neg     rcx
        neg     rsi
        inc     rcx
        mov     rax, r8
        mul     rcx
        add     r11, rax
        adc     rsi, rdx
        sbb     r8, r8
        neg     r8
        mov     rax, r9
        mul     rcx
        add     rsi, rax
        adc     r8, rdx
        neg     rcx
        inc     rcx
        mov     rax, r10
        mul     rcx
        add     r11, rax
        adc     rsi, rdx
        sbb     r9, r9
        mov     rax, r11
        mul     rcx
        sub     rdx, r9
        add     rsi, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     rcx
        neg     r9
        inc     rcx
        mov     rax, r10
        mul     rcx
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rax, r11
        mul     rcx
        add     r9, rax
        adc     r10, rdx
        mov     [rdi], rsi
        mov     [rdi+0x8], r8
        mov     [rdi+0x10], r9
        mov     [rdi+0x18], r10
        CFI_RET

Lp256_scalarmul_alt_local_inv_p256:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(240)
        mov     [rsp+0xe0], rdi
        xor     ecx, ecx
        mov     edx, 0xffffffff
        mov     rbx, rdx
        lea     rax, [rcx-0x1]
        neg     rdx
        mov     [rsp], rax
        mov     [rsp+0x8], rbx
        mov     [rsp+0x10], rcx
        mov     [rsp+0x18], rdx
        mov     [rsp+0x20], rcx
        mov     r8, [rsi]
        mov     r9, [rsi+0x8]
        mov     r10, [rsi+0x10]
        mov     r11, [rsi+0x18]
        lea     rax, [rcx+0x1]
        add     rax, r8
        lea     rbx, [rdx-0x1]
        adc     rbx, r9
        not     rcx
        adc     rcx, r10
        not     rdx
        adc     rdx, r11
        cmovae  rax, r8
        cmovae  rbx, r9
        cmovae  rcx, r10
        cmovae  rdx, r11
        mov     [rsp+0x28], rax
        mov     [rsp+0x30], rbx
        mov     [rsp+0x38], rcx
        mov     [rsp+0x40], rdx
        xor     eax, eax
        mov     [rsp+0x48], rax
        xor     eax, eax
        mov     [rsp+0x50], rax
        mov     [rsp+0x58], rax
        mov     [rsp+0x60], rax
        mov     [rsp+0x68], rax
        movabs  rcx, 0x4000000000000
        mov     [rsp+0x78], rcx
        mov     [rsp+0x80], rax
        mov     [rsp+0x88], rax
        mov     [rsp+0x90], rax
        mov     QWORD PTR [rsp+0xb0], 0xa
        mov     QWORD PTR [rsp+0xb8], 0x1
        jmp     Lp256_scalarmul_alt_inv_midloop
Lp256_scalarmul_alt_inv_loop:
        mov     r9, r8
        sar     r9, 0x3f
        xor     r8, r9
        sub     r8, r9
        mov     r11, r10
        sar     r11, 0x3f
        xor     r10, r11
        sub     r10, r11
        mov     r13, r12
        sar     r13, 0x3f
        xor     r12, r13
        sub     r12, r13
        mov     r15, r14
        sar     r15, 0x3f
        xor     r14, r15
        sub     r14, r15
        mov     rax, r8
        and     rax, r9
        mov     rdi, r10
        and     rdi, r11
        add     rdi, rax
        mov     [rsp+0xa0], rdi
        mov     rax, r12
        and     rax, r13
        mov     rsi, r14
        and     rsi, r15
        add     rsi, rax
        mov     [rsp+0xa8], rsi
        xor     ebx, ebx
        mov     rax, [rsp]
        xor     rax, r9
        mul     r8
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x28]
        xor     rax, r11
        mul     r10
        add     rdi, rax
        adc     rbx, rdx
        xor     ebp, ebp
        mov     rax, [rsp]
        xor     rax, r13
        mul     r12
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+0x28]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        xor     ecx, ecx
        mov     rax, [rsp+0x8]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+0x30]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx
        shrd    rdi, rbx, 0x3b
        mov     [rsp], rdi
        xor     edi, edi
        mov     rax, [rsp+0x8]
        xor     rax, r13
        mul     r12
        add     rbp, rax
        adc     rdi, rdx
        mov     rax, [rsp+0x30]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rdi, rdx
        shrd    rsi, rbp, 0x3b
        mov     [rsp+0x28], rsi
        xor     esi, esi
        mov     rax, [rsp+0x10]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rsi, rdx
        mov     rax, [rsp+0x38]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rsi, rdx
        shrd    rbx, rcx, 0x3b
        mov     [rsp+0x8], rbx
        xor     ebx, ebx
        mov     rax, [rsp+0x10]
        xor     rax, r13
        mul     r12
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x38]
        xor     rax, r15
        mul     r14
        add     rdi, rax
        adc     rbx, rdx
        shrd    rbp, rdi, 0x3b
        mov     [rsp+0x30], rbp
        mov     rax, [rsp+0x18]
        xor     rax, r9
        mov     rbp, [rsp+0x20]
        xor     rbp, r9
        and     rbp, r8
        neg     rbp
        mul     r8
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+0x40]
        xor     rax, r11
        mov     rdx, [rsp+0x48]
        xor     rdx, r11
        and     rdx, r10
        sub     rbp, rdx
        mul     r10
        add     rsi, rax
        adc     rbp, rdx
        shrd    rcx, rsi, 0x3b
        mov     [rsp+0x10], rcx
        shrd    rsi, rbp, 0x3b
        sar     rbp, 0x3b
        mov     rax, [rsp+0x18]
        mov     [rsp+0x18], rsi
        mov     rsi, [rsp+0x20]
        mov     [rsp+0x20], rbp
        xor     rax, r13
        xor     rsi, r13
        and     rsi, r12
        neg     rsi
        mul     r12
        add     rbx, rax
        adc     rsi, rdx
        mov     rax, [rsp+0x40]
        xor     rax, r15
        mov     rdx, [rsp+0x48]
        xor     rdx, r15
        and     rdx, r14
        sub     rsi, rdx
        mul     r14
        add     rbx, rax
        adc     rsi, rdx
        shrd    rdi, rbx, 0x3b
        mov     [rsp+0x38], rdi
        shrd    rbx, rsi, 0x3b
        mov     [rsp+0x40], rbx
        sar     rsi, 0x3b
        mov     [rsp+0x48], rsi
        mov     rbx, [rsp+0xa0]
        mov     rbp, [rsp+0xa8]
        xor     ecx, ecx
        mov     rax, [rsp+0x50]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+0x78]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx
        xor     esi, esi
        mov     rax, [rsp+0x50]
        xor     rax, r13
        mul     r12
        mov     [rsp+0x50], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+0x78]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+0x78], rbp
        xor     ebx, ebx
        mov     rax, [rsp+0x58]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x80]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rbx, rdx
        xor     ebp, ebp
        mov     rax, [rsp+0x58]
        xor     rax, r13
        mul     r12
        mov     [rsp+0x58], rcx
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+0x80]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        mov     [rsp+0x80], rsi
        xor     ecx, ecx
        mov     rax, [rsp+0x60]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+0x88]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx
        xor     esi, esi
        mov     rax, [rsp+0x60]
        xor     rax, r13
        mul     r12
        mov     [rsp+0x60], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+0x88]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+0x88], rbp
        mov     rax, [rsp+0x68]
        xor     rax, r9
        mov     rbx, r9
        and     rbx, r8
        neg     rbx
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x90]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     rbx, rdx
        mul     r10
        add     rcx, rax
        adc     rdx, rbx
        mov     rax, [rsp+0x68]
        mov     [rsp+0x68], rcx
        mov     [rsp+0x70], rdx
        xor     rax, r13
        mov     rcx, r13
        and     rcx, r12
        neg     rcx
        mul     r12
        add     rsi, rax
        adc     rcx, rdx
        mov     rax, [rsp+0x90]
        xor     rax, r15
        mov     rdx, r15
        and     rdx, r14
        sub     rcx, rdx
        mul     r14
        add     rsi, rax
        adc     rdx, rcx
        mov     [rsp+0x90], rsi
        mov     [rsp+0x98], rdx
        movabs  r8, 0xe000000000000000
        add     r8, [rsp+0x50]
        mov     r9, 0xffffffffffffffff
        adc     r9, [rsp+0x58]
        mov     r10, 0x1fffffff
        adc     r10, [rsp+0x60]
        movabs  r11, 0x2000000000000000
        adc     r11, [rsp+0x68]
        movabs  r12, 0x1fffffffe0000000
        adc     r12, [rsp+0x70]
        mov     rbx, r8
        shl     rbx, 0x20
        movabs  rax, 0xffffffff00000001
        mul     r8
        shr     r8, 0x20
        add     r9, rbx
        adc     r10, r8
        adc     r11, rax
        adc     r12, rdx
        sbb     rax, rax
        mov     ebx, 0xffffffff
        and     rbx, rax
        movabs  rdx, 0xffffffff00000001
        and     rdx, rax
        sub     r9, rax
        mov     [rsp+0x50], r9
        sbb     r10, rbx
        mov     [rsp+0x58], r10
        sbb     r11, 0x0
        mov     [rsp+0x60], r11
        sbb     r12, rdx
        mov     [rsp+0x68], r12
        movabs  r8, 0xe000000000000000
        add     r8, [rsp+0x78]
        mov     r9, 0xffffffffffffffff
        adc     r9, [rsp+0x80]
        mov     r10, 0x1fffffff
        adc     r10, [rsp+0x88]
        movabs  r11, 0x2000000000000000
        adc     r11, [rsp+0x90]
        movabs  r12, 0x1fffffffe0000000
        adc     r12, [rsp+0x98]
        mov     rbx, r8
        shl     rbx, 0x20
        movabs  rax, 0xffffffff00000001
        mul     r8
        shr     r8, 0x20
        add     r9, rbx
        adc     r10, r8
        adc     r11, rax
        adc     r12, rdx
        sbb     rax, rax
        mov     ebx, 0xffffffff
        and     rbx, rax
        movabs  rdx, 0xffffffff00000001
        and     rdx, rax
        sub     r9, rax
        mov     [rsp+0x78], r9
        sbb     r10, rbx
        mov     [rsp+0x80], r10
        sbb     r11, 0x0
        mov     [rsp+0x88], r11
        sbb     r12, rdx
        mov     [rsp+0x90], r12
Lp256_scalarmul_alt_inv_midloop:
        mov     rsi, [rsp+0xb8]
        mov     rdx, [rsp]
        mov     rcx, [rsp+0x28]
        mov     rbx, rdx
        and     rbx, 0xfffff
        movabs  rax, 0xfffffe0000000000
        or      rbx, rax
        and     rcx, 0xfffff
        movabs  rax, 0xc000000000000000
        or      rcx, rax
        mov     rax, 0xfffffffffffffffe
        xor     ebp, ebp
        mov     edx, 0x2
        mov     rdi, rbx
        mov     r8, rax
        test    rsi, rsi
        cmovs   r8, rbp
        test    rcx, 0x1
        cmove   r8, rbp
        cmove   rdi, rbp
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        sar     rcx, 1
        mov     eax, 0x100000
        lea     rdx, [rbx+rax]
        lea     rdi, [rcx+rax]
        shl     rdx, 0x16
        shl     rdi, 0x16
        sar     rdx, 0x2b
        sar     rdi, 0x2b
        movabs  rax, 0x20000100000
        lea     rbx, [rbx+rax]
        lea     rcx, [rcx+rax]
        sar     rbx, 0x2a
        sar     rcx, 0x2a
        mov     [rsp+0xc0], rdx
        mov     [rsp+0xc8], rbx
        mov     [rsp+0xd0], rdi
        mov     [rsp+0xd8], rcx
        mov     r12, [rsp]
        imul    rdi, r12
        imul    r12, rdx
        mov     r13, [rsp+0x28]
        imul    rbx, r13
        imul    r13, rcx
        add     r12, rbx
        add     r13, rdi
        sar     r12, 0x14
        sar     r13, 0x14
        mov     rbx, r12
        and     rbx, 0xfffff
        movabs  rax, 0xfffffe0000000000
        or      rbx, rax
        mov     rcx, r13
        and     rcx, 0xfffff
        movabs  rax, 0xc000000000000000
        or      rcx, rax
        mov     rax, 0xfffffffffffffffe
        mov     edx, 0x2
        mov     rdi, rbx
        mov     r8, rax
        test    rsi, rsi
        cmovs   r8, rbp
        test    rcx, 0x1
        cmove   r8, rbp
        cmove   rdi, rbp
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        sar     rcx, 1
        mov     eax, 0x100000
        lea     r8, [rbx+rax]
        lea     r10, [rcx+rax]
        shl     r8, 0x16
        shl     r10, 0x16
        sar     r8, 0x2b
        sar     r10, 0x2b
        movabs  rax, 0x20000100000
        lea     r15, [rbx+rax]
        lea     r11, [rcx+rax]
        sar     r15, 0x2a
        sar     r11, 0x2a
        mov     rbx, r13
        mov     rcx, r12
        imul    r12, r8
        imul    rbx, r15
        add     r12, rbx
        imul    r13, r11
        imul    rcx, r10
        add     r13, rcx
        sar     r12, 0x14
        sar     r13, 0x14
        mov     rbx, r12
        and     rbx, 0xfffff
        movabs  rax, 0xfffffe0000000000
        or      rbx, rax
        mov     rcx, r13
        and     rcx, 0xfffff
        movabs  rax, 0xc000000000000000
        or      rcx, rax
        mov     rax, [rsp+0xc0]
        imul    rax, r8
        mov     rdx, [rsp+0xd0]
        imul    rdx, r15
        imul    r8, [rsp+0xc8]
        imul    r15, [rsp+0xd8]
        add     r15, r8
        lea     r9, [rax+rdx]
        mov     rax, [rsp+0xc0]
        imul    rax, r10
        mov     rdx, [rsp+0xd0]
        imul    rdx, r11
        imul    r10, [rsp+0xc8]
        imul    r11, [rsp+0xd8]
        add     r11, r10
        lea     r13, [rax+rdx]
        mov     rax, 0xfffffffffffffffe
        mov     edx, 0x2
        mov     rdi, rbx
        mov     r8, rax
        test    rsi, rsi
        cmovs   r8, rbp
        test    rcx, 0x1
        cmove   r8, rbp
        cmove   rdi, rbp
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        cmovs   r8, rbp
        mov     rdi, rbx
        test    rcx, rdx
        cmove   r8, rbp
        cmove   rdi, rbp
        sar     rcx, 1
        xor     rdi, r8
        xor     rsi, r8
        bt      r8, 0x3f
        cmovb   rbx, rcx
        mov     r8, rax
        sub     rsi, rax
        lea     rcx, [rcx+rdi]
        sar     rcx, 1
        mov     eax, 0x100000
        lea     r8, [rbx+rax]
        lea     r12, [rcx+rax]
        shl     r8, 0x15
        shl     r12, 0x15
        sar     r8, 0x2b
        sar     r12, 0x2b
        movabs  rax, 0x20000100000
        lea     r10, [rbx+rax]
        lea     r14, [rcx+rax]
        sar     r10, 0x2b
        sar     r14, 0x2b
        mov     rax, r9
        imul    rax, r8
        mov     rdx, r13
        imul    rdx, r10
        imul    r8, r15
        imul    r10, r11
        add     r10, r8
        lea     r8, [rax+rdx]
        mov     rax, r9
        imul    rax, r12
        mov     rdx, r13
        imul    rdx, r14
        imul    r12, r15
        imul    r14, r11
        add     r14, r12
        lea     r12, [rax+rdx]
        mov     [rsp+0xb8], rsi
        dec     QWORD PTR [rsp+0xb0]
        jne     Lp256_scalarmul_alt_inv_loop
        mov     rax, [rsp]
        mov     rcx, [rsp+0x28]
        imul    rax, r8
        imul    rcx, r10
        add     rax, rcx
        sar     rax, 0x3f
        mov     r9, r8
        sar     r9, 0x3f
        xor     r8, r9
        sub     r8, r9
        xor     r9, rax
        mov     r11, r10
        sar     r11, 0x3f
        xor     r10, r11
        sub     r10, r11
        xor     r11, rax
        mov     r13, r12
        sar     r13, 0x3f
        xor     r12, r13
        sub     r12, r13
        xor     r13, rax
        mov     r15, r14
        sar     r15, 0x3f
        xor     r14, r15
        sub     r14, r15
        xor     r15, rax
        mov     rax, r8
        and     rax, r9
        mov     r12, r10
        and     r12, r11
        add     r12, rax
        xor     r13d, r13d
        mov     rax, [rsp+0x50]
        xor     rax, r9
        mul     r8
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x78]
        xor     rax, r11
        mul     r10
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        mov     rax, [rsp+0x58]
        xor     rax, r9
        mul     r8
        add     r13, rax
        adc     r14, rdx
        mov     rax, [rsp+0x80]
        xor     rax, r11
        mul     r10
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        xor     rax, r9
        mul     r8
        add     r14, rax
        adc     r15, rdx
        mov     rax, [rsp+0x88]
        xor     rax, r11
        mul     r10
        add     r14, rax
        adc     r15, rdx
        mov     rax, [rsp+0x68]
        xor     rax, r9
        and     r9, r8
        neg     r9
        mul     r8
        add     r15, rax
        adc     r9, rdx
        mov     rax, [rsp+0x90]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     r9, rdx
        mul     r10
        add     r15, rax
        adc     r9, rdx
        mov     [rsp+0x50], r12
        mov     [rsp+0x58], r13
        mov     [rsp+0x60], r14
        mov     [rsp+0x68], r15
        mov     [rsp+0x70], r9
        movabs  r8, 0xe000000000000000
        add     r8, [rsp+0x50]
        mov     r9, 0xffffffffffffffff
        adc     r9, [rsp+0x58]
        mov     r10, 0x1fffffff
        adc     r10, [rsp+0x60]
        movabs  r11, 0x2000000000000000
        adc     r11, [rsp+0x68]
        movabs  r12, 0x1fffffffe0000000
        adc     r12, [rsp+0x70]
        mov     rbx, r8
        shl     rbx, 0x20
        movabs  rax, 0xffffffff00000001
        mul     r8
        shr     r8, 0x20
        add     r9, rbx
        adc     r10, r8
        adc     r11, rax
        adc     r12, rdx
        sbb     rax, rax
        mov     ebx, 0xffffffff
        and     rbx, rax
        movabs  rdx, 0xffffffff00000001
        and     rdx, rax
        sub     r9, rax
        mov     [rsp+0x50], r9
        sbb     r10, rbx
        mov     [rsp+0x58], r10
        sbb     r11, 0x0
        mov     [rsp+0x60], r11
        sbb     r12, rdx
        mov     [rsp+0x68], r12
        mov     r8, [rsp+0x50]
        mov     r9, [rsp+0x58]
        mov     r10, [rsp+0x60]
        mov     r11, [rsp+0x68]
        mov     eax, 0x1
        mov     ebx, 0xffffffff
        lea     rcx, [rax-0x2]
        lea     rdx, [rbx-0x1]
        not     rbx
        add     rax, r8
        adc     rbx, r9
        adc     rcx, r10
        adc     rdx, r11
        cmovae  rax, r8
        cmovae  rbx, r9
        cmovae  rcx, r10
        cmovae  rdx, r11
        mov     rdi, [rsp+0xe0]
        mov     [rdi], rax
        mov     [rdi+0x8], rbx
        mov     [rdi+0x10], rcx
        mov     [rdi+0x18], rdx
        CFI_INC_RSP(240)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

Lp256_scalarmul_alt_local_montmul_p256:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        mov     rcx, rdx
        mov     rbx, [rcx]
        mov     rax, [rsi]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsi+0x8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x10]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsi+0x18]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rcx+0x8]
        xor     r13d, r13d
        mov     rax, [rsi]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rcx+0x10]
        xor     r15d, r15d
        mov     rax, [rsi]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rcx+0x18]
        xor     r8d, r8d
        mov     rax, [rsi]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rdi], r12
        mov     [rdi+0x8], r13
        mov     [rdi+0x10], r14
        mov     [rdi+0x18], r15
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
        CFI_RET

Lp256_scalarmul_alt_local_montsqr_p256:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        mov     rax, [rsi]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsi+0x8]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x18]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x10]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsi+0x18]
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsi+0x8]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x10]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x18]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rdi], r12
        mov     [rdi+0x8], r13
        mov     [rdi+0x10], r14
        mov     [rdi+0x18], r15
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
        CFI_RET


Lp256_scalarmul_alt_local_tomont_p256:
        CFI_START
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        mov     ecx, 0x3
        mov     rax, [rsi]
        mul     rcx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsi+0x8]
        mul     rcx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x10]
        mul     rcx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsi+0x18]
        mul     rcx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        movabs  rcx, 0xfffffffbffffffff
        xor     r13d, r13d
        mov     rax, [rsi]
        mul     rcx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x8]
        mul     rcx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x10]
        mul     rcx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x18]
        mul     rcx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rcx, 0x100000000
        mov     rax, r8
        mul     rcx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rcx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rcx
        lea     rcx, [rcx+0x2]
        mov     rax, r8
        mul     rcx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rcx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rcx, 0xfffffffffffffffe
        xor     r15d, r15d
        mov     rax, [rsi]
        mul     rcx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x8]
        mul     rcx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x10]
        mul     rcx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x18]
        mul     rcx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        movabs  rcx, 0x4fffffffd
        xor     r8d, r8d
        mov     rax, [rsi]
        mul     rcx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x8]
        mul     rcx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x10]
        mul     rcx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x18]
        mul     rcx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        movabs  rcx, 0x100000000
        mov     rax, r10
        mul     rcx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, r11
        mul     rcx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        not     rcx
        lea     rcx, [rcx+0x2]
        mov     rax, r10
        mul     rcx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, r11
        mul     rcx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        sub     r8, r9
        xor     edx, edx
        lea     r9, [rdx-0x1]
        inc     rdx
        add     rdx, r12
        dec     rcx
        adc     rcx, r13
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rdx
        cmovb   r13, rcx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rdi], r12
        mov     [rdi+0x8], r13
        mov     [rdi+0x10], r14
        mov     [rdi+0x18], r15
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_RET

Lp256_scalarmul_alt_local_p256_montjadd:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(224)
        mov     rbp, rdx
        mov     rax, [rsi+0x40]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsi+0x48]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x58]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x50]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsi+0x58]
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsi+0x48]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x50]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x58]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rax, [rbp+0x40]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rbp+0x48]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rbp+0x58]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rbp+0x50]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rbp+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rbp+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rbp+0x58]
        mov     rax, [rbp+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rbp+0x48]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rbp+0x50]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rbp+0x58]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        mov     rbx, [rsi+0x20]
        mov     rax, [rbp+0x40]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rbp+0x48]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rbp+0x50]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rbp+0x58]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsi+0x28]
        xor     r13d, r13d
        mov     rax, [rbp+0x40]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rbp+0x48]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rbp+0x50]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rbp+0x58]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsi+0x30]
        xor     r15d, r15d
        mov     rax, [rbp+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rbp+0x48]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rbp+0x50]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rbp+0x58]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsi+0x38]
        xor     r8d, r8d
        mov     rax, [rbp+0x40]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rbp+0x48]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rbp+0x50]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rbp+0x58]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0xc0], r12
        mov     [rsp+0xc8], r13
        mov     [rsp+0xd0], r14
        mov     [rsp+0xd8], r15
        mov     rbx, [rbp+0x20]
        mov     rax, [rsi+0x40]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsi+0x48]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x50]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsi+0x58]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rbp+0x28]
        xor     r13d, r13d
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rbp+0x30]
        xor     r15d, r15d
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rbp+0x38]
        xor     r8d, r8d
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     rbx, [rbp+0x0]
        mov     rax, [rsp]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x10]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x18]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rbp+0x8]
        xor     r13d, r13d
        mov     rax, [rsp]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rbp+0x10]
        xor     r15d, r15d
        mov     rax, [rsp]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rbp+0x18]
        xor     r8d, r8d
        mov     rax, [rsp]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        mov     rbx, [rsi]
        mov     rax, [rsp+0xa0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xb0]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0xb8]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsi+0x8]
        xor     r13d, r13d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsi+0x10]
        xor     r15d, r15d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsi+0x18]
        xor     r8d, r8d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rbx, [rsp+0x20]
        mov     rax, [rsp]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x10]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x18]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x28]
        xor     r13d, r13d
        mov     rax, [rsp]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x30]
        xor     r15d, r15d
        mov     rax, [rsp]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x38]
        xor     r8d, r8d
        mov     rax, [rsp]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     rbx, [rsp+0xc0]
        mov     rax, [rsp+0xa0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xb0]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0xb8]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0xc8]
        xor     r13d, r13d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0xd0]
        xor     r15d, r15d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0xd8]
        xor     r8d, r8d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0xc0], r12
        mov     [rsp+0xc8], r13
        mov     [rsp+0xd0], r14
        mov     [rsp+0xd8], r15
        mov     rax, [rsp+0x40]
        sub     rax, [rsp+0x80]
        mov     rcx, [rsp+0x48]
        sbb     rcx, [rsp+0x88]
        mov     r8, [rsp+0x50]
        sbb     r8, [rsp+0x90]
        mov     r9, [rsp+0x58]
        sbb     r9, [rsp+0x98]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0xa0], rax
        adc     rcx, r10
        mov     [rsp+0xa8], rcx
        adc     r8, 0x0
        mov     [rsp+0xb0], r8
        adc     r9, rdx
        mov     [rsp+0xb8], r9
        mov     rax, [rsp+0x20]
        sub     rax, [rsp+0xc0]
        mov     rcx, [rsp+0x28]
        sbb     rcx, [rsp+0xc8]
        mov     r8, [rsp+0x30]
        sbb     r8, [rsp+0xd0]
        mov     r9, [rsp+0x38]
        sbb     r9, [rsp+0xd8]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x20], rax
        adc     rcx, r10
        mov     [rsp+0x28], rcx
        adc     r8, 0x0
        mov     [rsp+0x30], r8
        adc     r9, rdx
        mov     [rsp+0x38], r9
        mov     rax, [rsp+0xa0]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0xb8]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0xb0]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsp+0xb8]
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsp+0xa8]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsp+0xb0]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsp+0xb8]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        mov     rax, [rsp+0x20]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsp+0x28]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x38]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x30]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsp+0x38]
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsp+0x28]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x30]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x38]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rbx, [rsp+0x80]
        mov     rax, [rsp+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x88]
        xor     r13d, r13d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x90]
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x98]
        xor     r8d, r8d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rbx, [rsp+0x40]
        mov     rax, [rsp+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x48]
        xor     r13d, r13d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x50]
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x58]
        xor     r8d, r8d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        mov     rax, [rsp]
        sub     rax, [rsp+0x80]
        mov     rcx, [rsp+0x8]
        sbb     rcx, [rsp+0x88]
        mov     r8, [rsp+0x10]
        sbb     r8, [rsp+0x90]
        mov     r9, [rsp+0x18]
        sbb     r9, [rsp+0x98]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp], rax
        adc     rcx, r10
        mov     [rsp+0x8], rcx
        adc     r8, 0x0
        mov     [rsp+0x10], r8
        adc     r9, rdx
        mov     [rsp+0x18], r9
        mov     rax, [rsp+0x40]
        sub     rax, [rsp+0x80]
        mov     rcx, [rsp+0x48]
        sbb     rcx, [rsp+0x88]
        mov     r8, [rsp+0x50]
        sbb     r8, [rsp+0x90]
        mov     r9, [rsp+0x58]
        sbb     r9, [rsp+0x98]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x60], rax
        adc     rcx, r10
        mov     [rsp+0x68], rcx
        adc     r8, 0x0
        mov     [rsp+0x70], r8
        adc     r9, rdx
        mov     [rsp+0x78], r9
        mov     rbx, [rsi+0x40]
        mov     rax, [rsp+0xa0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xb0]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0xb8]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsi+0x48]
        xor     r13d, r13d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsi+0x50]
        xor     r15d, r15d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsi+0x58]
        xor     r8d, r8d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        mov     rax, [rsp]
        sub     rax, [rsp+0x40]
        mov     rcx, [rsp+0x8]
        sbb     rcx, [rsp+0x48]
        mov     r8, [rsp+0x10]
        sbb     r8, [rsp+0x50]
        mov     r9, [rsp+0x18]
        sbb     r9, [rsp+0x58]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp], rax
        adc     rcx, r10
        mov     [rsp+0x8], rcx
        adc     r8, 0x0
        mov     [rsp+0x10], r8
        adc     r9, rdx
        mov     [rsp+0x18], r9
        mov     rax, [rsp+0x80]
        sub     rax, [rsp]
        mov     rcx, [rsp+0x88]
        sbb     rcx, [rsp+0x8]
        mov     r8, [rsp+0x90]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsp+0x98]
        sbb     r9, [rsp+0x18]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x80], rax
        adc     rcx, r10
        mov     [rsp+0x88], rcx
        adc     r8, 0x0
        mov     [rsp+0x90], r8
        adc     r9, rdx
        mov     [rsp+0x98], r9
        mov     rbx, [rsp+0xc0]
        mov     rax, [rsp+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0xc8]
        xor     r13d, r13d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0xd0]
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0xd8]
        xor     r8d, r8d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        mov     rbx, [rbp+0x40]
        mov     rax, [rsp+0xa0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xb0]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0xb8]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rbp+0x48]
        xor     r13d, r13d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rbp+0x50]
        xor     r15d, r15d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rbp+0x58]
        xor     r8d, r8d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        mov     rbx, [rsp+0x80]
        mov     rax, [rsp+0x20]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x28]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x30]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x38]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x88]
        xor     r13d, r13d
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x30]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x90]
        xor     r15d, r15d
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x30]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x98]
        xor     r8d, r8d
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x30]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rax, [rsp+0x80]
        sub     rax, [rsp+0x60]
        mov     rcx, [rsp+0x88]
        sbb     rcx, [rsp+0x68]
        mov     r8, [rsp+0x90]
        sbb     r8, [rsp+0x70]
        mov     r9, [rsp+0x98]
        sbb     r9, [rsp+0x78]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x80], rax
        adc     rcx, r10
        mov     [rsp+0x88], rcx
        adc     r8, 0x0
        mov     [rsp+0x90], r8
        adc     r9, rdx
        mov     [rsp+0x98], r9
        mov     r8, [rsi+0x40]
        mov     r9, [rsi+0x48]
        mov     r10, [rsi+0x50]
        mov     r11, [rsi+0x58]
        mov     rax, r8
        mov     rdx, r9
        or      rax, r10
        or      rdx, r11
        or      rax, rdx
        neg     rax
        sbb     rax, rax
        mov     r12, [rbp+0x40]
        mov     r13, [rbp+0x48]
        mov     r14, [rbp+0x50]
        mov     r15, [rbp+0x58]
        mov     rbx, r12
        mov     rdx, r13
        or      rbx, r14
        or      rdx, r15
        or      rbx, rdx
        neg     rbx
        sbb     rbx, rbx
        cmp     rbx, rax
        cmovb   r12, r8
        cmovb   r13, r9
        cmovb   r14, r10
        cmovb   r15, r11
        cmove   r12, [rsp+0xa0]
        cmove   r13, [rsp+0xa8]
        cmove   r14, [rsp+0xb0]
        cmove   r15, [rsp+0xb8]
        mov     rax, [rsp]
        cmovb   rax, [rsi]
        cmova   rax, [rbp+0x0]
        mov     rbx, [rsp+0x8]
        cmovb   rbx, [rsi+0x8]
        cmova   rbx, [rbp+0x8]
        mov     rcx, [rsp+0x10]
        cmovb   rcx, [rsi+0x10]
        cmova   rcx, [rbp+0x10]
        mov     rdx, [rsp+0x18]
        cmovb   rdx, [rsi+0x18]
        cmova   rdx, [rbp+0x18]
        mov     r8, [rsp+0x80]
        cmovb   r8, [rsi+0x20]
        cmova   r8, [rbp+0x20]
        mov     r9, [rsp+0x88]
        cmovb   r9, [rsi+0x28]
        cmova   r9, [rbp+0x28]
        mov     r10, [rsp+0x90]
        cmovb   r10, [rsi+0x30]
        cmova   r10, [rbp+0x30]
        mov     r11, [rsp+0x98]
        cmovb   r11, [rsi+0x38]
        cmova   r11, [rbp+0x38]
        mov     [rdi], rax
        mov     [rdi+0x8], rbx
        mov     [rdi+0x10], rcx
        mov     [rdi+0x18], rdx
        mov     [rdi+0x20], r8
        mov     [rdi+0x28], r9
        mov     [rdi+0x30], r10
        mov     [rdi+0x38], r11
        mov     [rdi+0x40], r12
        mov     [rdi+0x48], r13
        mov     [rdi+0x50], r14
        mov     [rdi+0x58], r15
        CFI_INC_RSP(224)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

Lp256_scalarmul_alt_local_p256_montjdouble:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(192)
        mov     rax, [rsi+0x40]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsi+0x48]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x58]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x50]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsi+0x58]
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsi+0x48]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x50]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x58]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rax, [rsi+0x20]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsi+0x28]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x38]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x30]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi+0x20]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsi+0x28]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsi+0x38]
        mov     rax, [rsi+0x28]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsi+0x28]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x30]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x38]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     rax, [rsi]
        sub     rax, [rsp]
        mov     rcx, [rsi+0x8]
        sbb     rcx, [rsp+0x8]
        mov     r8, [rsi+0x10]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsi+0x18]
        sbb     r9, [rsp+0x18]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x60], rax
        adc     rcx, r10
        mov     [rsp+0x68], rcx
        adc     r8, 0x0
        mov     [rsp+0x70], r8
        adc     r9, rdx
        mov     [rsp+0x78], r9
        mov     rax, [rsi]
        add     rax, [rsp]
        mov     rcx, [rsi+0x8]
        adc     rcx, [rsp+0x8]
        mov     r8, [rsi+0x10]
        adc     r8, [rsp+0x10]
        mov     r9, [rsi+0x18]
        adc     r9, [rsp+0x18]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        sub     rax, r11
        mov     [rsp+0x40], rax
        sbb     rcx, r10
        mov     [rsp+0x48], rcx
        sbb     r8, 0x0
        mov     [rsp+0x50], r8
        sbb     r9, rdx
        mov     [rsp+0x58], r9
        mov     rbx, [rsp+0x60]
        mov     rax, [rsp+0x40]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x48]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x50]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x58]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x68]
        xor     r13d, r13d
        mov     rax, [rsp+0x40]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x70]
        xor     r15d, r15d
        mov     rax, [rsp+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x78]
        xor     r8d, r8d
        mov     rax, [rsp+0x40]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        xor     r11, r11
        mov     rax, [rsi+0x20]
        add     rax, [rsi+0x40]
        mov     rcx, [rsi+0x28]
        adc     rcx, [rsi+0x48]
        mov     r8, [rsi+0x30]
        adc     r8, [rsi+0x50]
        mov     r9, [rsi+0x38]
        adc     r9, [rsi+0x58]
        adc     r11, r11
        sub     rax, 0xffffffffffffffff
        mov     r10d, 0xffffffff
        sbb     rcx, r10
        sbb     r8, 0x0
        movabs  rdx, 0xffffffff00000001
        sbb     r9, rdx
        sbb     r11, 0x0
        and     r10, r11
        and     rdx, r11
        add     rax, r11
        mov     [rsp+0x40], rax
        adc     rcx, r10
        mov     [rsp+0x48], rcx
        adc     r8, 0x0
        mov     [rsp+0x50], r8
        adc     r9, rdx
        mov     [rsp+0x58], r9
        mov     rbx, [rsp+0x20]
        mov     rax, [rsi]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsi+0x8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x10]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsi+0x18]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x28]
        xor     r13d, r13d
        mov     rax, [rsi]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x30]
        xor     r15d, r15d
        mov     rax, [rsi]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x38]
        xor     r8d, r8d
        mov     rax, [rsi]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rax, [rsp+0x60]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsp+0x68]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x78]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x70]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsp+0x78]
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsp+0x68]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x70]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x78]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        mov     rax, [rsp+0x40]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsp+0x48]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x58]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x50]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsp+0x58]
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsp+0x48]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x50]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x58]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        mov     r9, 0xffffffffffffffff
        xor     r11d, r11d
        sub     r9, [rsp+0xa0]
        movabs  r10, 0xffffffff
        sbb     r10, [rsp+0xa8]
        sbb     r11, [rsp+0xb0]
        movabs  r12, 0xffffffff00000001
        sbb     r12, [rsp+0xb8]
        mov     rcx, 0x9
        mov     rax, r9
        mul     rcx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, r10
        xor     r10d, r10d
        mul     rcx
        add     r9, rax
        adc     r10, rdx
        mov     rax, r11
        xor     r11d, r11d
        mul     rcx
        add     r10, rax
        adc     r11, rdx
        mov     rax, r12
        xor     r12d, r12d
        mul     rcx
        add     r11, rax
        adc     r12, rdx
        mov     ecx, 0xc
        mov     rax, [rsp+0x80]
        mul     rcx
        add     r8, rax
        adc     r9, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x88]
        mul     rcx
        sub     rdx, rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x90]
        mul     rcx
        sub     rdx, rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x98]
        mul     rcx
        sub     rdx, rbx
        add     r11, rax
        adc     r12, rdx
        lea     rcx, [r12+0x1]
        movabs  rax, 0xffffffff00000001
        mul     rcx
        mov     rbx, rcx
        shl     rbx, 0x20
        add     r8, rcx
        sbb     rbx, 0x0
        sub     r9, rbx
        sbb     r10, 0x0
        sbb     r11, rax
        sbb     rcx, rdx
        dec     rcx
        mov     eax, 0xffffffff
        and     rax, rcx
        xor     edx, edx
        sub     rdx, rax
        add     r8, rcx
        mov     [rsp+0xa0], r8
        adc     r9, rax
        mov     [rsp+0xa8], r9
        adc     r10, 0x0
        mov     [rsp+0xb0], r10
        adc     r11, rdx
        mov     [rsp+0xb8], r11
        mov     rax, [rsp+0x40]
        sub     rax, [rsp]
        mov     rcx, [rsp+0x48]
        sbb     rcx, [rsp+0x8]
        mov     r8, [rsp+0x50]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsp+0x58]
        sbb     r9, [rsp+0x18]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x40], rax
        adc     rcx, r10
        mov     [rsp+0x48], rcx
        adc     r8, 0x0
        mov     [rsp+0x50], r8
        adc     r9, rdx
        mov     [rsp+0x58], r9
        mov     rax, [rsp+0x20]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsp+0x28]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x38]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x30]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsp+0x38]
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsp+0x28]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x30]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x38]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rbx, [rsp+0x60]
        mov     rax, [rsp+0xa0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xb0]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0xb8]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x68]
        xor     r13d, r13d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x70]
        xor     r15d, r15d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x78]
        xor     r8d, r8d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        mov     rax, [rsp+0x40]
        sub     rax, [rsp+0x20]
        mov     rcx, [rsp+0x48]
        sbb     rcx, [rsp+0x28]
        mov     r8, [rsp+0x50]
        sbb     r8, [rsp+0x30]
        mov     r9, [rsp+0x58]
        sbb     r9, [rsp+0x38]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rdi+0x40], rax
        adc     rcx, r10
        mov     [rdi+0x48], rcx
        adc     r8, 0x0
        mov     [rdi+0x50], r8
        adc     r9, rdx
        mov     [rdi+0x58], r9
        mov     r11, [rsp+0x98]
        mov     rcx, r11
        mov     r10, [rsp+0x90]
        shld    r11, r10, 0x2
        mov     r9, [rsp+0x88]
        shld    r10, r9, 0x2
        mov     r8, [rsp+0x80]
        shld    r9, r8, 0x2
        shl     r8, 0x2
        shr     rcx, 0x3e
        add     rcx, 0x1
        sub     r8, [rsp+0xa0]
        sbb     r9, [rsp+0xa8]
        sbb     r10, [rsp+0xb0]
        sbb     r11, [rsp+0xb8]
        sbb     rcx, 0x0
        movabs  rax, 0xffffffff00000001
        mul     rcx
        mov     rbx, rcx
        shl     rbx, 0x20
        add     r8, rcx
        sbb     rbx, 0x0
        sub     r9, rbx
        sbb     r10, 0x0
        sbb     r11, rax
        sbb     rcx, rdx
        dec     rcx
        mov     eax, 0xffffffff
        and     rax, rcx
        xor     edx, edx
        sub     rdx, rax
        add     r8, rcx
        mov     [rdi], r8
        adc     r9, rax
        mov     [rdi+0x8], r9
        adc     r10, 0x0
        mov     [rdi+0x10], r10
        adc     r11, rdx
        mov     [rdi+0x18], r11
        mov     r8, 0xffffffffffffffff
        xor     r10d, r10d
        sub     r8, [rsp]
        movabs  r9, 0xffffffff
        sbb     r9, [rsp+0x8]
        sbb     r10, [rsp+0x10]
        movabs  r11, 0xffffffff00000001
        sbb     r11, [rsp+0x18]
        mov     r12, r11
        shld    r11, r10, 0x3
        shld    r10, r9, 0x3
        shld    r9, r8, 0x3
        shl     r8, 0x3
        shr     r12, 0x3d
        mov     ecx, 0x3
        mov     rax, [rsp+0x60]
        mul     rcx
        add     r8, rax
        adc     r9, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x68]
        mul     rcx
        sub     rdx, rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x70]
        mul     rcx
        sub     rdx, rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x78]
        mul     rcx
        sub     rdx, rbx
        add     r11, rax
        adc     r12, rdx
        lea     rcx, [r12+0x1]
        movabs  rax, 0xffffffff00000001
        mul     rcx
        mov     rbx, rcx
        shl     rbx, 0x20
        add     r8, rcx
        sbb     rbx, 0x0
        sub     r9, rbx
        sbb     r10, 0x0
        sbb     r11, rax
        sbb     rcx, rdx
        dec     rcx
        mov     eax, 0xffffffff
        and     rax, rcx
        xor     edx, edx
        sub     rdx, rax
        add     r8, rcx
        mov     [rdi+0x20], r8
        adc     r9, rax
        mov     [rdi+0x28], r9
        adc     r10, 0x0
        mov     [rdi+0x30], r10
        adc     r11, rdx
        mov     [rdi+0x38], r11
        CFI_INC_RSP(192)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
        CFI_RET

Lp256_scalarmul_alt_local_p256_montjmixadd:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(192)
        mov     rbp, rdx
        mov     rax, [rsi+0x40]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsi+0x48]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x58]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x50]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsi+0x58]
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsi+0x48]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x50]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x58]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rbx, [rbp+0x20]
        mov     rax, [rsi+0x40]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsi+0x48]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x50]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsi+0x58]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rbp+0x28]
        xor     r13d, r13d
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rbp+0x30]
        xor     r15d, r15d
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rbp+0x38]
        xor     r8d, r8d
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     rbx, [rbp+0x0]
        mov     rax, [rsp]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x10]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x18]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rbp+0x8]
        xor     r13d, r13d
        mov     rax, [rsp]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rbp+0x10]
        xor     r15d, r15d
        mov     rax, [rsp]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rbp+0x18]
        xor     r8d, r8d
        mov     rax, [rsp]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        mov     rbx, [rsp+0x20]
        mov     rax, [rsp]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x10]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x18]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x28]
        xor     r13d, r13d
        mov     rax, [rsp]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x30]
        xor     r15d, r15d
        mov     rax, [rsp]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x38]
        xor     r8d, r8d
        mov     rax, [rsp]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     rax, [rsp+0x40]
        sub     rax, [rsi]
        mov     rcx, [rsp+0x48]
        sbb     rcx, [rsi+0x8]
        mov     r8, [rsp+0x50]
        sbb     r8, [rsi+0x10]
        mov     r9, [rsp+0x58]
        sbb     r9, [rsi+0x18]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0xa0], rax
        adc     rcx, r10
        mov     [rsp+0xa8], rcx
        adc     r8, 0x0
        mov     [rsp+0xb0], r8
        adc     r9, rdx
        mov     [rsp+0xb8], r9
        mov     rax, [rsp+0x20]
        sub     rax, [rsi+0x20]
        mov     rcx, [rsp+0x28]
        sbb     rcx, [rsi+0x28]
        mov     r8, [rsp+0x30]
        sbb     r8, [rsi+0x30]
        mov     r9, [rsp+0x38]
        sbb     r9, [rsi+0x38]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x20], rax
        adc     rcx, r10
        mov     [rsp+0x28], rcx
        adc     r8, 0x0
        mov     [rsp+0x30], r8
        adc     r9, rdx
        mov     [rsp+0x38], r9
        mov     rax, [rsp+0xa0]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0xb8]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0xb0]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsp+0xb8]
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsp+0xa8]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsp+0xb0]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsp+0xb8]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        mov     rax, [rsp+0x20]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsp+0x28]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x38]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x30]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsp+0x38]
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsp+0x28]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x30]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x38]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rbx, [rsi]
        mov     rax, [rsp+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsi+0x8]
        xor     r13d, r13d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsi+0x10]
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsi+0x18]
        xor     r8d, r8d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rbx, [rsp+0x40]
        mov     rax, [rsp+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x48]
        xor     r13d, r13d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x50]
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x58]
        xor     r8d, r8d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        mov     rax, [rsp]
        sub     rax, [rsp+0x80]
        mov     rcx, [rsp+0x8]
        sbb     rcx, [rsp+0x88]
        mov     r8, [rsp+0x10]
        sbb     r8, [rsp+0x90]
        mov     r9, [rsp+0x18]
        sbb     r9, [rsp+0x98]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp], rax
        adc     rcx, r10
        mov     [rsp+0x8], rcx
        adc     r8, 0x0
        mov     [rsp+0x10], r8
        adc     r9, rdx
        mov     [rsp+0x18], r9
        mov     rax, [rsp+0x40]
        sub     rax, [rsp+0x80]
        mov     rcx, [rsp+0x48]
        sbb     rcx, [rsp+0x88]
        mov     r8, [rsp+0x50]
        sbb     r8, [rsp+0x90]
        mov     r9, [rsp+0x58]
        sbb     r9, [rsp+0x98]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x60], rax
        adc     rcx, r10
        mov     [rsp+0x68], rcx
        adc     r8, 0x0
        mov     [rsp+0x70], r8
        adc     r9, rdx
        mov     [rsp+0x78], r9
        mov     rbx, [rsi+0x40]
        mov     rax, [rsp+0xa0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xb0]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0xb8]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsi+0x48]
        xor     r13d, r13d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsi+0x50]
        xor     r15d, r15d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsi+0x58]
        xor     r8d, r8d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        mov     rax, [rsp]
        sub     rax, [rsp+0x40]
        mov     rcx, [rsp+0x8]
        sbb     rcx, [rsp+0x48]
        mov     r8, [rsp+0x10]
        sbb     r8, [rsp+0x50]
        mov     r9, [rsp+0x18]
        sbb     r9, [rsp+0x58]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp], rax
        adc     rcx, r10
        mov     [rsp+0x8], rcx
        adc     r8, 0x0
        mov     [rsp+0x10], r8
        adc     r9, rdx
        mov     [rsp+0x18], r9
        mov     rax, [rsp+0x80]
        sub     rax, [rsp]
        mov     rcx, [rsp+0x88]
        sbb     rcx, [rsp+0x8]
        mov     r8, [rsp+0x90]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsp+0x98]
        sbb     r9, [rsp+0x18]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x80], rax
        adc     rcx, r10
        mov     [rsp+0x88], rcx
        adc     r8, 0x0
        mov     [rsp+0x90], r8
        adc     r9, rdx
        mov     [rsp+0x98], r9
        mov     rbx, [rsi+0x20]
        mov     rax, [rsp+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsi+0x28]
        xor     r13d, r13d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsi+0x30]
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsi+0x38]
        xor     r8d, r8d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        mov     rbx, [rsp+0x80]
        mov     rax, [rsp+0x20]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x28]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x30]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x38]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x88]
        xor     r13d, r13d
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x30]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x90]
        xor     r15d, r15d
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x30]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x98]
        xor     r8d, r8d
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x30]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rax, [rsp+0x80]
        sub     rax, [rsp+0x60]
        mov     rcx, [rsp+0x88]
        sbb     rcx, [rsp+0x68]
        mov     r8, [rsp+0x90]
        sbb     r8, [rsp+0x70]
        mov     r9, [rsp+0x98]
        sbb     r9, [rsp+0x78]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x80], rax
        adc     rcx, r10
        mov     [rsp+0x88], rcx
        adc     r8, 0x0
        mov     [rsp+0x90], r8
        adc     r9, rdx
        mov     [rsp+0x98], r9
        mov     rax, [rsi+0x40]
        mov     rdx, [rsi+0x48]
        or      rax, [rsi+0x50]
        or      rdx, [rsi+0x58]
        or      rax, rdx
        mov     r8, [rsp]
        mov     rax, [rbp+0x0]
        cmove   r8, rax
        mov     r9, [rsp+0x8]
        mov     rax, [rbp+0x8]
        cmove   r9, rax
        mov     r10, [rsp+0x10]
        mov     rax, [rbp+0x10]
        cmove   r10, rax
        mov     r11, [rsp+0x18]
        mov     rax, [rbp+0x18]
        cmove   r11, rax
        mov     r12, [rsp+0x80]
        mov     rax, [rbp+0x20]
        cmove   r12, rax
        mov     r13, [rsp+0x88]
        mov     rax, [rbp+0x28]
        cmove   r13, rax
        mov     r14, [rsp+0x90]
        mov     rax, [rbp+0x30]
        cmove   r14, rax
        mov     r15, [rsp+0x98]
        mov     rax, [rbp+0x38]
        cmove   r15, rax
        mov     [rdi], r8
        mov     [rdi+0x8], r9
        mov     [rdi+0x10], r10
        mov     [rdi+0x18], r11
        mov     [rdi+0x20], r12
        mov     [rdi+0x28], r13
        mov     [rdi+0x30], r14
        mov     [rdi+0x38], r15
        mov     r8, [rsp+0xa0]
        mov     r9, [rsp+0xa8]
        mov     r10, [rsp+0xb0]
        mov     r11, [rsp+0xb8]
        mov     eax, 0x1
        cmove   r8, rax
        movabs  rax, 0xffffffff00000000
        cmove   r9, rax
        mov     rax, 0xffffffffffffffff
        cmove   r10, rax
        mov     eax, 0xfffffffe
        cmove   r11, rax
        mov     [rdi+0x40], r8
        mov     [rdi+0x48], r9
        mov     [rdi+0x50], r10
        mov     [rdi+0x58], r11
        CFI_INC_RSP(192)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
