// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery-Jacobian form scalar multiplication for GM/T 0003-2012 curve SM2
// Input scalar[4], point[12]; output res[12]
//
// extern void sm2_montjscalarmul_alt
//   (uint64_t res[static 12],
//    const uint64_t scalar[static 4],
//    const uint64_t point[static 12]);
//
// This function is a variant of its affine point version sm2_scalarmul.
// Here, input and output points are assumed to be in Jacobian form with
// their coordinates in the Montgomery domain. Thus, if priming indicates
// Montgomery form, x' = (2^256 * x) mod p_sm2 etc., each point argument
// is a triple (x',y',z') representing the affine point (x/z^2,y/z^3) when
// z' is nonzero or the point at infinity (group identity) if z' = 0.
//
// Given scalar = n and point = P, assumed to be on the NIST elliptic
// curve SM2, returns a representation of n * P. If the result is the
// point at infinity (either because the input point was or because the
// scalar was a multiple of p_sm2) then the output is guaranteed to
// represent the point at infinity, i.e. to have its z coordinate zero.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sm2_montjscalarmul_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sm2_montjscalarmul_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sm2_montjscalarmul_alt)


        .text
        .balign 32

// Size of individual field elements

#define NUMSIZE 32

// Intermediate variables on the stack. Uppercase syntactic variants
// make x86_att version simpler to generate.

#define SCALARB (0*NUMSIZE)
#define scalarb rsp+(0*NUMSIZE)
#define ACC (1*NUMSIZE)
#define acc rsp+(1*NUMSIZE)
#define TABENT (4*NUMSIZE)
#define tabent rsp+(4*NUMSIZE)

#define TAB (7*NUMSIZE)
#define tab rsp+(7*NUMSIZE)

#define res [rsp+(31*NUMSIZE)]

#define NSPACE 32*NUMSIZE

// Avoid using .rep for the sake of the BoringSSL/AWS-LC delocator,
// which doesn't accept repetitions, assembler macros etc.

#define selectblock(I)                          \
        cmp     rdi, I;                         \
        cmovz   rax, [rsp+TAB+96*(I-1)];        \
        cmovz   rbx, [rsp+TAB+96*(I-1)+8];      \
        cmovz   rcx, [rsp+TAB+96*(I-1)+16];     \
        cmovz   rdx, [rsp+TAB+96*(I-1)+24];     \
        cmovz   r8, [rsp+TAB+96*(I-1)+32];      \
        cmovz   r9, [rsp+TAB+96*(I-1)+40];      \
        cmovz   r10, [rsp+TAB+96*(I-1)+48];     \
        cmovz   r11, [rsp+TAB+96*(I-1)+56];     \
        cmovz   r12, [rsp+TAB+96*(I-1)+64];     \
        cmovz   r13, [rsp+TAB+96*(I-1)+72];     \
        cmovz   r14, [rsp+TAB+96*(I-1)+80];     \
        cmovz   r15, [rsp+TAB+96*(I-1)+88]

S2N_BN_SYMBOL(sm2_montjscalarmul_alt):
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
        CFI_CALL(Lsm2_montjscalarmul_alt_standard)
        CFI_POP(rsi)
        CFI_POP(rdi)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(sm2_montjscalarmul_alt)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lsm2_montjscalarmul_alt_standard)

Lsm2_montjscalarmul_alt_standard:
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

// Load the digits of group order n_sm2 = [r15;r14;r13;r12]

        mov     r12, 0x53bbf40939d54123
        mov     r13, 0x7203df6b21c6052b
        mov     r14, 0xffffffffffffffff
        mov     r15, 0xfffffffeffffffff

// First, reduce the input scalar mod n_sm2, i.e. conditionally subtract n_sm2

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

// Now if the top bit of the reduced scalar is set, negate it mod n_sm2,
// i.e. do n |-> n_sm2 - n. Remember the sign in rbp so we can
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

// Set the tab[0] table entry to the input point = 1 * P, except
// that we negate it if the top bit of the scalar was set. This
// negation takes care over the y = 0 case to maintain all the
// coordinates < p_sm2 throughout, even though triples (x,y,z)
// with y = 0 can only represent a point on the curve when z = 0
// and it represents the point at infinity regardless of x and y.

        mov     rax, [rbx]
        mov     [rsp+TAB], rax
        mov     rax, [rbx+8]
        mov     [rsp+TAB+8], rax
        mov     rax, [rbx+16]
        mov     [rsp+TAB+16], rax
        mov     rax, [rbx+24]
        mov     [rsp+TAB+24], rax

        mov     r12, [rbx+32]
        mov     rax, r12
        mov     r13, [rbx+40]
        or      rax, r13
        mov     r14, [rbx+48]
        mov     rcx, r14
        mov     r15, [rbx+56]
        or      rcx, r15
        or      rax, rcx
        cmovz   rbp, rax

        xor     r11d, r11d
        mov     r9d, 0x00000000ffffffff
        not     r11
        mov     r8, r11
        mov     r10, r11
        xor     r9, r8
        btr     r11, 32

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

        mov     rax, [rbx+64]
        mov     [rsp+TAB+64], rax
        mov     rax, [rbx+72]
        mov     [rsp+TAB+72], rax
        mov     rax, [rbx+80]
        mov     [rsp+TAB+80], rax
        mov     rax, [rbx+88]
        mov     [rsp+TAB+88], rax

// Compute and record tab[1] = 2 * p, ..., tab[7] = 8 * P

        lea     rdi, [rsp+TAB+96*1]
        lea     rsi, [rsp+TAB]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjdouble)

        lea     rdi, [rsp+TAB+96*2]
        lea     rsi, [rsp+TAB+96*1]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjadd)

        lea     rdi, [rsp+TAB+96*3]
        lea     rsi, [rsp+TAB+96*1]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjdouble)

        lea     rdi, [rsp+TAB+96*4]
        lea     rsi, [rsp+TAB+96*3]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjadd)

        lea     rdi, [rsp+TAB+96*5]
        lea     rsi, [rsp+TAB+96*2]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjdouble)

        lea     rdi, [rsp+TAB+96*6]
        lea     rsi, [rsp+TAB+96*5]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjadd)

        lea     rdi, [rsp+TAB+96*7]
        lea     rsi, [rsp+TAB+96*3]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjdouble)

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

        selectblock(1)
        selectblock(2)
        selectblock(3)
        selectblock(4)
        selectblock(5)
        selectblock(6)
        selectblock(7)
        selectblock(8)

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

Lsm2_montjscalarmul_alt_mainloop:
        sub     rbp, 4

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjdouble)

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

        selectblock(1)
        selectblock(2)
        selectblock(3)
        selectblock(4)
        selectblock(5)
        selectblock(6)
        selectblock(7)
        selectblock(8)

// Store it to "tabent" with the y coordinate optionally negated
// Again, do it carefully to give coordinates < p_sm2 even in
// the degenerate case y = 0 (when z = 0 for points on the curve).

        mov      [rsp+TABENT], rax
        mov      [rsp+TABENT+8], rbx
        mov      [rsp+TABENT+16], rcx
        mov      [rsp+TABENT+24], rdx

        mov      [rsp+TABENT+64], r12
        mov      [rsp+TABENT+72], r13
        mov      [rsp+TABENT+80], r14
        mov      [rsp+TABENT+88], r15

        xor     r15d, r15d
        mov     rax, r8
        mov     r13d, 0x00000000ffffffff
        or      rax, r9
        not     r15
        mov     rcx, r10
        mov     r12, r15
        or      rcx, r11
        mov     r14, r15
        xor     r13, r12
        btr     r15, 32
        or      rax, rcx
        cmovz   rsi, rax

        sub     r12, r8
        sbb     r13, r9
        sbb     r14, r10
        sbb     r15, r11

        test    rsi, rsi
        cmovnz   r8, r12
        cmovnz   r9, r13
        cmovnz   r10, r14
        cmovnz   r11, r15

        mov      [rsp+TABENT+32], r8
        mov      [rsp+TABENT+40], r9
        mov      [rsp+TABENT+48], r10
        mov      [rsp+TABENT+56], r11

        lea     rdx, [rsp+TABENT]
        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lsm2_montjscalarmul_alt_sm2_montjadd)

        test    rbp, rbp
        jne     Lsm2_montjscalarmul_alt_mainloop

// That's the end of the main loop, and we just need to copy the
// result in "acc" to the output.

        mov     rdi, res
        mov     rax, [rsp+ACC]
        mov     [rdi], rax
        mov     rax, [rsp+ACC+8]
        mov     [rdi+8], rax
        mov     rax, [rsp+ACC+16]
        mov     [rdi+16], rax
        mov     rax, [rsp+ACC+24]
        mov     [rdi+24], rax

        mov     rax, [rsp+ACC+32]
        mov     [rdi+32], rax
        mov     rax, [rsp+ACC+40]
        mov     [rdi+40], rax
        mov     rax, [rsp+ACC+48]
        mov     [rdi+48], rax
        mov     rax, [rsp+ACC+56]
        mov     [rdi+56], rax

        mov     rax, [rsp+ACC+64]
        mov     [rdi+64], rax
        mov     rax, [rsp+ACC+72]
        mov     [rdi+72], rax
        mov     rax, [rsp+ACC+80]
        mov     [rdi+80], rax
        mov     rax, [rsp+ACC+88]
        mov     [rdi+88], rax

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
S2N_BN_SIZE_DIRECTIVE(Lsm2_montjscalarmul_alt_standard)
#else
S2N_BN_SIZE_DIRECTIVE(sm2_montjscalarmul_alt)
#endif

// Local copies of subroutines, complete clones at the moment

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lsm2_montjscalarmul_alt_sm2_montjadd)

Lsm2_montjscalarmul_alt_sm2_montjadd:
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
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        mov     rax, [rbp+0x40]
        mul     QWORD PTR [rsi+0x20]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rbp+0x40]
        mul     QWORD PTR [rsi+0x28]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rbp+0x48]
        mul     QWORD PTR [rsi+0x20]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rbp+0x40]
        mul     QWORD PTR [rsi+0x30]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rbp+0x48]
        mul     QWORD PTR [rsi+0x28]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rbp+0x50]
        mul     QWORD PTR [rsi+0x20]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rbp+0x40]
        mul     QWORD PTR [rsi+0x38]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rbp+0x48]
        mul     QWORD PTR [rsi+0x30]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rbp+0x50]
        mul     QWORD PTR [rsi+0x28]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rbp+0x58]
        mul     QWORD PTR [rsi+0x20]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rbp+0x48]
        mul     QWORD PTR [rsi+0x38]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rbp+0x50]
        mul     QWORD PTR [rsi+0x30]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rbp+0x58]
        mul     QWORD PTR [rsi+0x28]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rbp+0x50]
        mul     QWORD PTR [rsi+0x38]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rbp+0x58]
        mul     QWORD PTR [rsi+0x30]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rbp+0x58]
        mul     QWORD PTR [rsi+0x38]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp+0xc0], r12
        mov     [rsp+0xc8], r13
        mov     [rsp+0xd0], r14
        mov     [rsp+0xd8], r15
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rbp+0x20]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rbp+0x28]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x48]
        mul     QWORD PTR [rbp+0x20]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rbp+0x30]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsi+0x48]
        mul     QWORD PTR [rbp+0x28]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x50]
        mul     QWORD PTR [rbp+0x20]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rbp+0x38]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsi+0x48]
        mul     QWORD PTR [rbp+0x30]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x50]
        mul     QWORD PTR [rbp+0x28]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x58]
        mul     QWORD PTR [rbp+0x20]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsi+0x48]
        mul     QWORD PTR [rbp+0x38]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsi+0x50]
        mul     QWORD PTR [rbp+0x30]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x58]
        mul     QWORD PTR [rbp+0x28]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsi+0x50]
        mul     QWORD PTR [rbp+0x38]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsi+0x58]
        mul     QWORD PTR [rbp+0x30]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x58]
        mul     QWORD PTR [rbp+0x38]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     rax, [rsp]
        mul     QWORD PTR [rbp+0x0]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp]
        mul     QWORD PTR [rbp+0x8]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x8]
        mul     QWORD PTR [rbp+0x0]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp]
        mul     QWORD PTR [rbp+0x10]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0x8]
        mul     QWORD PTR [rbp+0x8]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0x10]
        mul     QWORD PTR [rbp+0x0]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp]
        mul     QWORD PTR [rbp+0x18]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0x8]
        mul     QWORD PTR [rbp+0x10]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x10]
        mul     QWORD PTR [rbp+0x8]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x18]
        mul     QWORD PTR [rbp+0x0]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0x8]
        mul     QWORD PTR [rbp+0x18]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0x10]
        mul     QWORD PTR [rbp+0x10]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0x18]
        mul     QWORD PTR [rbp+0x8]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0x10]
        mul     QWORD PTR [rbp+0x18]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0x18]
        mul     QWORD PTR [rbp+0x10]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0x18]
        mul     QWORD PTR [rbp+0x18]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsi]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsi+0x8]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsi]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsi+0x10]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsi+0x8]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsi]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsi+0x18]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsi+0x10]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsi+0x8]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsi]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsi+0x18]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsi+0x10]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsi+0x8]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsi+0x18]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsi+0x10]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsi+0x18]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rax, [rsp]
        mul     QWORD PTR [rsp+0x20]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp]
        mul     QWORD PTR [rsp+0x28]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x8]
        mul     QWORD PTR [rsp+0x20]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp]
        mul     QWORD PTR [rsp+0x30]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0x8]
        mul     QWORD PTR [rsp+0x28]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0x10]
        mul     QWORD PTR [rsp+0x20]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp]
        mul     QWORD PTR [rsp+0x38]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0x8]
        mul     QWORD PTR [rsp+0x30]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x10]
        mul     QWORD PTR [rsp+0x28]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x18]
        mul     QWORD PTR [rsp+0x20]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0x8]
        mul     QWORD PTR [rsp+0x38]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0x10]
        mul     QWORD PTR [rsp+0x30]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0x18]
        mul     QWORD PTR [rsp+0x28]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0x10]
        mul     QWORD PTR [rsp+0x38]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0x18]
        mul     QWORD PTR [rsp+0x30]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0x18]
        mul     QWORD PTR [rsp+0x38]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsp+0xc0]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsp+0xc8]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsp+0xc0]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsp+0xd0]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsp+0xc8]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsp+0xc0]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsp+0xd8]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsp+0xd0]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsp+0xc8]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsp+0xc0]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsp+0xd8]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsp+0xd0]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsp+0xc8]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsp+0xd8]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsp+0xd0]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsp+0xd8]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        add     rax, r11
        mov     [rsp+0xa0], rax
        adc     rcx, r10
        mov     [rsp+0xa8], rcx
        adc     r8, r11
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
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        add     rax, r11
        mov     [rsp+0x20], rax
        adc     rcx, r10
        mov     [rsp+0x28], rcx
        adc     r8, r11
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
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0x80]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0x88]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0x80]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0x90]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0x88]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0x80]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0x98]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0x90]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0x88]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0x80]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0x98]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0x90]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0x88]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0x98]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0x90]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0x98]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0x40]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0x48]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0x40]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0x50]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0x48]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0x40]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0x58]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0x50]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0x48]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0x40]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0x58]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0x50]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0x48]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0x58]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0x50]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0x58]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        add     rax, r11
        mov     [rsp], rax
        adc     rcx, r10
        mov     [rsp+0x8], rcx
        adc     r8, r11
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
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        add     rax, r11
        mov     [rsp+0x60], rax
        adc     rcx, r10
        mov     [rsp+0x68], rcx
        adc     r8, r11
        mov     [rsp+0x70], r8
        adc     r9, rdx
        mov     [rsp+0x78], r9
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsi+0x40]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsi+0x48]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsi+0x40]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsi+0x50]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsi+0x48]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsi+0x40]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsi+0x58]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsi+0x50]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsi+0x48]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsi+0x40]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsi+0x58]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsi+0x50]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsi+0x48]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsi+0x58]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsi+0x50]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsi+0x58]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        add     rax, r11
        mov     [rsp], rax
        adc     rcx, r10
        mov     [rsp+0x8], rcx
        adc     r8, r11
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
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        add     rax, r11
        mov     [rsp+0x80], rax
        adc     rcx, r10
        mov     [rsp+0x88], rcx
        adc     r8, r11
        mov     [rsp+0x90], r8
        adc     r9, rdx
        mov     [rsp+0x98], r9
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0xc0]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0xc8]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0xc0]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0xd0]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0xc8]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0xc0]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp+0x60]
        mul     QWORD PTR [rsp+0xd8]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0xd0]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0xc8]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0xc0]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0x68]
        mul     QWORD PTR [rsp+0xd8]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0xd0]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0xc8]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0x70]
        mul     QWORD PTR [rsp+0xd8]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0xd0]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0xd8]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rbp+0x40]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rbp+0x48]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rbp+0x40]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rbp+0x50]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rbp+0x48]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rbp+0x40]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rbp+0x58]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rbp+0x50]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rbp+0x48]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rbp+0x40]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rbp+0x58]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rbp+0x50]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rbp+0x48]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rbp+0x58]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rbp+0x50]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rbp+0x58]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        mov     rax, [rsp+0x20]
        mul     QWORD PTR [rsp+0x80]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp+0x20]
        mul     QWORD PTR [rsp+0x88]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x28]
        mul     QWORD PTR [rsp+0x80]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp+0x20]
        mul     QWORD PTR [rsp+0x90]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0x28]
        mul     QWORD PTR [rsp+0x88]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0x30]
        mul     QWORD PTR [rsp+0x80]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp+0x20]
        mul     QWORD PTR [rsp+0x98]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0x28]
        mul     QWORD PTR [rsp+0x90]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x30]
        mul     QWORD PTR [rsp+0x88]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x38]
        mul     QWORD PTR [rsp+0x80]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0x28]
        mul     QWORD PTR [rsp+0x98]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0x30]
        mul     QWORD PTR [rsp+0x90]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0x38]
        mul     QWORD PTR [rsp+0x88]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0x30]
        mul     QWORD PTR [rsp+0x98]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0x38]
        mul     QWORD PTR [rsp+0x90]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0x38]
        mul     QWORD PTR [rsp+0x98]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        add     rax, r11
        mov     [rsp+0x80], rax
        adc     rcx, r10
        mov     [rsp+0x88], rcx
        adc     r8, r11
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

S2N_BN_SIZE_DIRECTIVE(Lsm2_montjscalarmul_alt_sm2_montjadd)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lsm2_montjscalarmul_alt_sm2_montjdouble)

Lsm2_montjscalarmul_alt_sm2_montjdouble:
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
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        add     rax, r11
        mov     [rsp+0x60], rax
        adc     rcx, r10
        mov     [rsp+0x68], rcx
        adc     r8, r11
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
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        sub     rax, r11
        mov     [rsp+0x40], rax
        sbb     rcx, r10
        mov     [rsp+0x48], rcx
        sbb     r8, r11
        mov     [rsp+0x50], r8
        sbb     r9, rdx
        mov     [rsp+0x58], r9
        mov     rax, [rsp+0x40]
        mul     QWORD PTR [rsp+0x60]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp+0x40]
        mul     QWORD PTR [rsp+0x68]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x48]
        mul     QWORD PTR [rsp+0x60]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp+0x40]
        mul     QWORD PTR [rsp+0x70]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0x48]
        mul     QWORD PTR [rsp+0x68]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0x50]
        mul     QWORD PTR [rsp+0x60]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp+0x40]
        mul     QWORD PTR [rsp+0x78]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0x48]
        mul     QWORD PTR [rsp+0x70]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x50]
        mul     QWORD PTR [rsp+0x68]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0x58]
        mul     QWORD PTR [rsp+0x60]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0x48]
        mul     QWORD PTR [rsp+0x78]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0x50]
        mul     QWORD PTR [rsp+0x70]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0x58]
        mul     QWORD PTR [rsp+0x68]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0x50]
        mul     QWORD PTR [rsp+0x78]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0x58]
        mul     QWORD PTR [rsp+0x70]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0x58]
        mul     QWORD PTR [rsp+0x78]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        movabs  r10, 0xffffffff00000000
        sbb     rcx, r10
        sbb     r8, 0xffffffffffffffff
        movabs  rdx, 0xfffffffeffffffff
        sbb     r9, rdx
        sbb     r11, 0x0
        and     r10, r11
        and     rdx, r11
        add     rax, r11
        mov     [rsp+0x40], rax
        adc     rcx, r10
        mov     [rsp+0x48], rcx
        adc     r8, r11
        mov     [rsp+0x50], r8
        adc     r9, rdx
        mov     [rsp+0x58], r9
        mov     rax, [rsi]
        mul     QWORD PTR [rsp+0x20]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsi]
        mul     QWORD PTR [rsp+0x28]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsp+0x20]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsi]
        mul     QWORD PTR [rsp+0x30]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsp+0x28]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rsp+0x20]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsi]
        mul     QWORD PTR [rsp+0x38]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsp+0x30]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rsp+0x28]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rsp+0x20]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsp+0x38]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rsp+0x30]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rsp+0x28]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rsp+0x38]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rsp+0x30]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rsp+0x38]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        mov     r9, 0xffffffffffffffff
        mov     r11, r9
        sub     r9, [rsp+0xa0]
        movabs  r10, 0xffffffff00000000
        sbb     r10, [rsp+0xa8]
        sbb     r11, [rsp+0xb0]
        movabs  r12, 0xfffffffeffffffff
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
        lea     rdx, [r12+0x1]
        mov     rax, rdx
        shl     rax, 0x20
        mov     rcx, rax
        sub     rax, rdx
        add     r8, rdx
        adc     r9, rax
        adc     r10, 0x0
        adc     r11, rcx
        sbb     rdx, rdx
        not     rdx
        movabs  rax, 0xffffffff00000000
        and     rax, rdx
        mov     rcx, rdx
        btr     rcx, 0x20
        add     r8, rdx
        mov     [rsp+0xa0], r8
        adc     r9, rax
        mov     [rsp+0xa8], r9
        adc     r10, rdx
        mov     [rsp+0xb0], r10
        adc     r11, rcx
        mov     [rsp+0xb8], r11
        mov     rax, [rsp+0x40]
        sub     rax, [rsp]
        mov     rcx, [rsp+0x48]
        sbb     rcx, [rsp+0x8]
        mov     r8, [rsp+0x50]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsp+0x58]
        sbb     r9, [rsp+0x18]
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        add     rax, r11
        mov     [rsp+0x40], rax
        adc     rcx, r10
        mov     [rsp+0x48], rcx
        adc     r8, r11
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
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsp+0x60]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsp+0x68]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsp+0x60]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        xor     r12, r12
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsp+0x70]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsp+0x68]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsp+0x60]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsp+0xa0]
        mul     QWORD PTR [rsp+0x78]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsp+0x70]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsp+0x68]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsp+0x60]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsp+0xa8]
        mul     QWORD PTR [rsp+0x78]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsp+0x70]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsp+0x68]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsp+0xb0]
        mul     QWORD PTR [rsp+0x78]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsp+0x70]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsp+0xb8]
        mul     QWORD PTR [rsp+0x78]
        add     r14, rax
        adc     r15, rdx
        mov     rax, r8
        shl     rax, 0x20
        mov     rcx, r8
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r8
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        sbb     r11, rdx
        sbb     r8, rbx
        mov     rax, r9
        shl     rax, 0x20
        mov     rcx, r9
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r9
        sbb     rcx, 0x0
        sub     r10, rax
        sbb     r11, rcx
        sbb     r8, rdx
        sbb     r9, rbx
        mov     rax, r10
        shl     rax, 0x20
        mov     rcx, r10
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r10
        sbb     rcx, 0x0
        sub     r11, rax
        sbb     r8, rcx
        sbb     r9, rdx
        sbb     r10, rbx
        mov     rax, r11
        shl     rax, 0x20
        mov     rcx, r11
        shr     rcx, 0x20
        mov     rdx, rax
        mov     rbx, rcx
        sub     rax, r11
        sbb     rcx, 0x0
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rdx
        sbb     r11, rbx
        xor     eax, eax
        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        adc     rax, rax
        mov     ecx, 0x1
        mov     edx, 0xffffffff
        xor     ebx, ebx
        add     rcx, r12
        lea     r11, [rdx+0x1]
        adc     rdx, r13
        lea     r8, [rbx-0x1]
        adc     rbx, r14
        adc     r11, r15
        adc     r8, rax
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbx
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
        movabs  r10, 0xffffffff00000000
        sbb     r11, r11
        and     r10, r11
        mov     rdx, r11
        btr     rdx, 0x20
        add     rax, r11
        mov     [rdi+0x40], rax
        adc     rcx, r10
        mov     [rdi+0x48], rcx
        adc     r8, r11
        mov     [rdi+0x50], r8
        adc     r9, rdx
        mov     [rdi+0x58], r9
        mov     r11, [rsp+0x98]
        mov     rdx, r11
        mov     r10, [rsp+0x90]
        shld    r11, r10, 0x2
        mov     r9, [rsp+0x88]
        shld    r10, r9, 0x2
        mov     r8, [rsp+0x80]
        shld    r9, r8, 0x2
        shl     r8, 0x2
        shr     rdx, 0x3e
        add     rdx, 0x1
        sub     r8, [rsp+0xa0]
        sbb     r9, [rsp+0xa8]
        sbb     r10, [rsp+0xb0]
        sbb     r11, [rsp+0xb8]
        sbb     rdx, 0x0
        mov     rax, rdx
        shl     rax, 0x20
        mov     rcx, rax
        sub     rax, rdx
        add     r8, rdx
        adc     r9, rax
        adc     r10, 0x0
        adc     r11, rcx
        sbb     rdx, rdx
        not     rdx
        movabs  rax, 0xffffffff00000000
        and     rax, rdx
        mov     rcx, rdx
        btr     rcx, 0x20
        add     r8, rdx
        mov     [rdi], r8
        adc     r9, rax
        mov     [rdi+0x8], r9
        adc     r10, rdx
        mov     [rdi+0x10], r10
        adc     r11, rcx
        mov     [rdi+0x18], r11
        mov     r8, 0xffffffffffffffff
        mov     r10, r8
        sub     r8, [rsp]
        movabs  r9, 0xffffffff00000000
        sbb     r9, [rsp+0x8]
        sbb     r10, [rsp+0x10]
        movabs  r11, 0xfffffffeffffffff
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
        lea     rdx, [r12+0x1]
        mov     rax, rdx
        shl     rax, 0x20
        mov     rcx, rax
        sub     rax, rdx
        add     r8, rdx
        adc     r9, rax
        adc     r10, 0x0
        adc     r11, rcx
        sbb     rdx, rdx
        not     rdx
        movabs  rax, 0xffffffff00000000
        and     rax, rdx
        mov     rcx, rdx
        btr     rcx, 0x20
        add     r8, rdx
        mov     [rdi+0x20], r8
        adc     r9, rax
        mov     [rdi+0x28], r9
        adc     r10, rdx
        mov     [rdi+0x30], r10
        adc     r11, rcx
        mov     [rdi+0x38], r11
        CFI_INC_RSP(192)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lsm2_montjscalarmul_alt_sm2_montjdouble)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
