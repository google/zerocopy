// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery-Jacobian form scalar multiplication for P-256
// Input scalar[4], point[12]; output res[12]
//
// extern void p256_montjscalarmul
//   (uint64_t res[static 12],
//    const uint64_t scalar[static 4],
//    const uint64_t point[static 12]);
//
// This function is a variant of its affine point version p256_scalarmul.
// Here, input and output points are assumed to be in Jacobian form with
// their coordinates in the Montgomery domain. Thus, if priming indicates
// Montgomery form, x' = (2^256 * x) mod p_256 etc., each point argument
// is a triple (x',y',z') representing the affine point (x/z^2,y/z^3) when
// z' is nonzero or the point at infinity (group identity) if z' = 0.
//
// Given scalar = n and point = P, assumed to be on the NIST elliptic
// curve P-256, returns a representation of n * P. If the result is the
// point at infinity (either because the input point was or because the
// scalar was a multiple of p_256) then the output is guaranteed to
// represent the point at infinity, i.e. to have its z coordinate zero.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p256_montjscalarmul)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p256_montjscalarmul)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p256_montjscalarmul)


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

S2N_BN_SYMBOL(p256_montjscalarmul):
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
        CFI_CALL(Lp256_montjscalarmul_standard)
        CFI_POP(rsi)
        CFI_POP(rdi)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(p256_montjscalarmul)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp256_montjscalarmul_standard)

Lp256_montjscalarmul_standard:
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

// Set the tab[0] table entry to the input point = 1 * P, except
// that we negate it if the top bit of the scalar was set. This
// negation takes care over the y = 0 case to maintain all the
// coordinates < p_256 throughout, even though triples (x,y,z)
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
        CFI_CALL(Lp256_montjscalarmul_p256_montjdouble)

        lea     rdi, [rsp+TAB+96*2]
        lea     rsi, [rsp+TAB+96*1]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp256_montjscalarmul_p256_montjadd)

        lea     rdi, [rsp+TAB+96*3]
        lea     rsi, [rsp+TAB+96*1]
        CFI_CALL(Lp256_montjscalarmul_p256_montjdouble)

        lea     rdi, [rsp+TAB+96*4]
        lea     rsi, [rsp+TAB+96*3]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp256_montjscalarmul_p256_montjadd)

        lea     rdi, [rsp+TAB+96*5]
        lea     rsi, [rsp+TAB+96*2]
        CFI_CALL(Lp256_montjscalarmul_p256_montjdouble)

        lea     rdi, [rsp+TAB+96*6]
        lea     rsi, [rsp+TAB+96*5]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp256_montjscalarmul_p256_montjadd)

        lea     rdi, [rsp+TAB+96*7]
        lea     rsi, [rsp+TAB+96*3]
        CFI_CALL(Lp256_montjscalarmul_p256_montjdouble)

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

Lp256_montjscalarmul_mainloop:
        sub     rbp, 4

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp256_montjscalarmul_p256_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp256_montjscalarmul_p256_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp256_montjscalarmul_p256_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp256_montjscalarmul_p256_montjdouble)

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
// Again, do it carefully to give coordinates < p_256 even in
// the degenerate case y = 0 (when z = 0 for points on the curve).

        mov      [rsp+TABENT], rax
        mov      [rsp+TABENT+8], rbx
        mov      [rsp+TABENT+16], rcx
        mov      [rsp+TABENT+24], rdx

        mov      [rsp+TABENT+64], r12
        mov      [rsp+TABENT+72], r13
        mov      [rsp+TABENT+80], r14
        mov      [rsp+TABENT+88], r15

        mov     rax, r8
        xor     r14d, r14d
        or      rax, r9
        lea     r12, [r14-1]
        mov     rcx, r10
        mov     r15, 0x00000000ffffffff
        or      rcx, r11
        mov     r13, r15
        neg     r15
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
        CFI_CALL(Lp256_montjscalarmul_p256_montjadd)

        test    rbp, rbp
        jne     Lp256_montjscalarmul_mainloop

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
S2N_BN_SIZE_DIRECTIVE(Lp256_montjscalarmul_standard)
#else
S2N_BN_SIZE_DIRECTIVE(p256_montjscalarmul)
#endif

// Local copies of subroutines, complete clones at the moment

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp256_montjscalarmul_p256_montjadd)

Lp256_montjscalarmul_p256_montjadd:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(224)
        mov     rbp, rdx
        mov     rdx, [rsi+0x40]
        mulx    r15, r8, rdx
        mulx    r10, r9, [rsi+0x48]
        mulx    r12, r11, [rsi+0x58]
        mov     rdx, [rsi+0x50]
        mulx    r14, r13, [rsi+0x58]
        xor     ecx, ecx
        mulx    rbx, rax, [rsi+0x40]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsi+0x48]
        adcx    r11, rax
        adox    r12, rbx
        mov     rdx, [rsi+0x58]
        mulx    rbx, rax, [rsi+0x48]
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rcx
        adox    r14, rcx
        adc     r14, rcx
        xor     ecx, ecx
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [rsi+0x48]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [rsi+0x50]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [rsi+0x58]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, rcx
        adox    r15, rcx
        xor     ecx, ecx
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rcx
        mov     r9d, ecx
        adox    r9, rcx
        adcx    r9, rcx
        add     r14, r9
        adc     r15, rcx
        mov     r8d, ecx
        adc     r8, rcx
        xor     ecx, ecx
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, rcx
        adox    r8, rcx
        adc     r8, rcx
        mov     r8d, 0x1
        lea     rdx, [rdx-0x1]
        lea     rax, [rcx-0x1]
        mov     r11d, 0xfffffffe
        cmove   r8, rcx
        cmove   rdx, rcx
        cmove   rax, rcx
        cmove   r11, rcx
        add     r12, r8
        adc     r13, rdx
        adc     r14, rax
        adc     r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rdx, [rbp+0x40]
        mulx    r15, r8, rdx
        mulx    r10, r9, [rbp+0x48]
        mulx    r12, r11, [rbp+0x58]
        mov     rdx, [rbp+0x50]
        mulx    r14, r13, [rbp+0x58]
        xor     ecx, ecx
        mulx    rbx, rax, [rbp+0x40]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rbp+0x48]
        adcx    r11, rax
        adox    r12, rbx
        mov     rdx, [rbp+0x58]
        mulx    rbx, rax, [rbp+0x48]
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rcx
        adox    r14, rcx
        adc     r14, rcx
        xor     ecx, ecx
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [rbp+0x48]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [rbp+0x50]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [rbp+0x58]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, rcx
        adox    r15, rcx
        xor     ecx, ecx
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rcx
        mov     r9d, ecx
        adox    r9, rcx
        adcx    r9, rcx
        add     r14, r9
        adc     r15, rcx
        mov     r8d, ecx
        adc     r8, rcx
        xor     ecx, ecx
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, rcx
        adox    r8, rcx
        adc     r8, rcx
        mov     r8d, 0x1
        lea     rdx, [rdx-0x1]
        lea     rax, [rcx-0x1]
        mov     r11d, 0xfffffffe
        cmove   r8, rcx
        cmove   rdx, rcx
        cmove   rax, rcx
        cmove   r11, rcx
        add     r12, r8
        adc     r13, rdx
        adc     r14, rax
        adc     r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        xor     r13d, r13d
        mov     rdx, [rsi+0x20]
        mulx    r9, r8, [rbp+0x40]
        mulx    r10, rbx, [rbp+0x48]
        adc     r9, rbx
        mulx    r11, rbx, [rbp+0x50]
        adc     r10, rbx
        mulx    r12, rbx, [rbp+0x58]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsi+0x28]
        xor     r14d, r14d
        mulx    rbx, rax, [rbp+0x40]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rbp+0x48]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rbp+0x50]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rbp+0x58]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsi+0x30]
        xor     r8d, r8d
        mulx    rbx, rax, [rbp+0x40]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rbp+0x48]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rbp+0x50]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rbp+0x58]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsi+0x38]
        xor     r9d, r9d
        mulx    rbx, rax, [rbp+0x40]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rbp+0x48]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rbp+0x50]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rbp+0x58]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0xc0], r12
        mov     [rsp+0xc8], r13
        mov     [rsp+0xd0], r14
        mov     [rsp+0xd8], r15
        xor     r13d, r13d
        mov     rdx, [rbp+0x20]
        mulx    r9, r8, [rsi+0x40]
        mulx    r10, rbx, [rsi+0x48]
        adc     r9, rbx
        mulx    r11, rbx, [rsi+0x50]
        adc     r10, rbx
        mulx    r12, rbx, [rsi+0x58]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rbp+0x28]
        xor     r14d, r14d
        mulx    rbx, rax, [rsi+0x40]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsi+0x48]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsi+0x50]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsi+0x58]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rbp+0x30]
        xor     r8d, r8d
        mulx    rbx, rax, [rsi+0x40]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsi+0x48]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsi+0x50]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsi+0x58]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rbp+0x38]
        xor     r9d, r9d
        mulx    rbx, rax, [rsi+0x40]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsi+0x48]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsi+0x50]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsi+0x58]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        xor     r13d, r13d
        mov     rdx, [rbp+0x0]
        mulx    r9, r8, [rsp]
        mulx    r10, rbx, [rsp+0x8]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0x10]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0x18]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rbp+0x8]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0x8]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x10]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x18]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rbp+0x10]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x8]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x10]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0x18]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rbp+0x18]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x8]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0x10]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0x18]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        xor     r13d, r13d
        mov     rdx, [rsi]
        mulx    r9, r8, [rsp+0xa0]
        mulx    r10, rbx, [rsp+0xa8]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0xb0]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0xb8]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsi+0x8]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xb8]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsi+0x10]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0xb8]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsi+0x18]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0xb8]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        xor     r13d, r13d
        mov     rdx, [rsp+0x20]
        mulx    r9, r8, [rsp]
        mulx    r10, rbx, [rsp+0x8]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0x10]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0x18]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsp+0x28]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0x8]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x10]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x18]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsp+0x30]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x8]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x10]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0x18]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsp+0x38]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x8]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0x10]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0x18]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        xor     r13d, r13d
        mov     rdx, [rsp+0xc0]
        mulx    r9, r8, [rsp+0xa0]
        mulx    r10, rbx, [rsp+0xa8]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0xb0]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0xb8]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsp+0xc8]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xb8]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsp+0xd0]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0xb8]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsp+0xd8]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0xb8]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
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
        mov     rdx, [rsp+0xa0]
        mulx    r15, r8, rdx
        mulx    r10, r9, [rsp+0xa8]
        mulx    r12, r11, [rsp+0xb8]
        mov     rdx, [rsp+0xb0]
        mulx    r14, r13, [rsp+0xb8]
        xor     ecx, ecx
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r11, rax
        adox    r12, rbx
        mov     rdx, [rsp+0xb8]
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rcx
        adox    r14, rcx
        adc     r14, rcx
        xor     ecx, ecx
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [rsp+0xa8]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [rsp+0xb0]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [rsp+0xb8]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, rcx
        adox    r15, rcx
        xor     ecx, ecx
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rcx
        mov     r9d, ecx
        adox    r9, rcx
        adcx    r9, rcx
        add     r14, r9
        adc     r15, rcx
        mov     r8d, ecx
        adc     r8, rcx
        xor     ecx, ecx
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, rcx
        adox    r8, rcx
        adc     r8, rcx
        mov     r8d, 0x1
        lea     rdx, [rdx-0x1]
        lea     rax, [rcx-0x1]
        mov     r11d, 0xfffffffe
        cmove   r8, rcx
        cmove   rdx, rcx
        cmove   rax, rcx
        cmove   r11, rcx
        add     r12, r8
        adc     r13, rdx
        adc     r14, rax
        adc     r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        mov     rdx, [rsp+0x20]
        mulx    r15, r8, rdx
        mulx    r10, r9, [rsp+0x28]
        mulx    r12, r11, [rsp+0x38]
        mov     rdx, [rsp+0x30]
        mulx    r14, r13, [rsp+0x38]
        xor     ecx, ecx
        mulx    rbx, rax, [rsp+0x20]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x28]
        adcx    r11, rax
        adox    r12, rbx
        mov     rdx, [rsp+0x38]
        mulx    rbx, rax, [rsp+0x28]
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rcx
        adox    r14, rcx
        adc     r14, rcx
        xor     ecx, ecx
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [rsp+0x28]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [rsp+0x30]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [rsp+0x38]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, rcx
        adox    r15, rcx
        xor     ecx, ecx
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rcx
        mov     r9d, ecx
        adox    r9, rcx
        adcx    r9, rcx
        add     r14, r9
        adc     r15, rcx
        mov     r8d, ecx
        adc     r8, rcx
        xor     ecx, ecx
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, rcx
        adox    r8, rcx
        adc     r8, rcx
        mov     ebx, 0x1
        add     rbx, r12
        lea     rdx, [rdx-0x1]
        adc     rdx, r13
        lea     rcx, [rcx-0x1]
        mov     rax, rcx
        adc     rcx, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rbx
        cmovb   r13, rdx
        cmovb   r14, rcx
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        xor     r13d, r13d
        mov     rdx, [rsp+0x80]
        mulx    r9, r8, [rsp+0x60]
        mulx    r10, rbx, [rsp+0x68]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0x70]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0x78]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsp+0x88]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp+0x60]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0x68]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x70]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x78]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsp+0x90]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp+0x60]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x68]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x70]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0x78]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsp+0x98]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp+0x60]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x68]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0x70]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0x78]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        xor     r13d, r13d
        mov     rdx, [rsp+0x40]
        mulx    r9, r8, [rsp+0x60]
        mulx    r10, rbx, [rsp+0x68]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0x70]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0x78]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsp+0x48]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp+0x60]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0x68]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x70]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x78]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsp+0x50]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp+0x60]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x68]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x70]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0x78]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsp+0x58]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp+0x60]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x68]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0x70]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0x78]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
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
        xor     r13d, r13d
        mov     rdx, [rsi+0x40]
        mulx    r9, r8, [rsp+0xa0]
        mulx    r10, rbx, [rsp+0xa8]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0xb0]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0xb8]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsi+0x48]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xb8]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsi+0x50]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0xb8]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsi+0x58]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0xb8]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
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
        xor     r13d, r13d
        mov     rdx, [rsp+0xc0]
        mulx    r9, r8, [rsp+0x60]
        mulx    r10, rbx, [rsp+0x68]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0x70]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0x78]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsp+0xc8]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp+0x60]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0x68]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x70]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x78]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsp+0xd0]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp+0x60]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x68]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x70]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0x78]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsp+0xd8]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp+0x60]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x68]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0x70]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0x78]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        xor     r13d, r13d
        mov     rdx, [rbp+0x40]
        mulx    r9, r8, [rsp+0xa0]
        mulx    r10, rbx, [rsp+0xa8]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0xb0]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0xb8]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rbp+0x48]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xb8]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rbp+0x50]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0xb8]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rbp+0x58]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0xb8]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        xor     r13d, r13d
        mov     rdx, [rsp+0x80]
        mulx    r9, r8, [rsp+0x20]
        mulx    r10, rbx, [rsp+0x28]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0x30]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0x38]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsp+0x88]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp+0x20]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0x28]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x30]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x38]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsp+0x90]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp+0x20]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x28]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x30]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0x38]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsp+0x98]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp+0x20]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x28]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0x30]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0x38]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
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

S2N_BN_SIZE_DIRECTIVE(Lp256_montjscalarmul_p256_montjadd)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp256_montjscalarmul_p256_montjdouble)

Lp256_montjscalarmul_p256_montjdouble:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(192)
        mov     rdx, [rsi+0x40]
        mulx    r15, r8, rdx
        mulx    r10, r9, [rsi+0x48]
        mulx    r12, r11, [rsi+0x58]
        mov     rdx, [rsi+0x50]
        mulx    r14, r13, [rsi+0x58]
        xor     ebp, ebp
        mulx    rbx, rax, [rsi+0x40]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsi+0x48]
        adcx    r11, rax
        adox    r12, rbx
        mov     rdx, [rsi+0x58]
        mulx    rbx, rax, [rsi+0x48]
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rbp
        adox    r14, rbp
        adc     r14, rbp
        xor     ebp, ebp
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [rsi+0x48]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [rsi+0x50]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [rsi+0x58]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, rbp
        adox    r15, rbp
        xor     ebp, ebp
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rbp
        mov     r9d, ebp
        adox    r9, rbp
        adcx    r9, rbp
        add     r14, r9
        adc     r15, rbp
        mov     r8d, ebp
        adc     r8, rbp
        xor     ebp, ebp
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, rbp
        adox    r8, rbp
        adc     r8, rbp
        mov     ecx, 0x1
        add     rcx, r12
        lea     rdx, [rdx-0x1]
        adc     rdx, r13
        lea     rbp, [rbp-0x1]
        mov     rax, rbp
        adc     rbp, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbp
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rdx, [rsi+0x20]
        mulx    r15, r8, rdx
        mulx    r10, r9, [rsi+0x28]
        mulx    r12, r11, [rsi+0x38]
        mov     rdx, [rsi+0x30]
        mulx    r14, r13, [rsi+0x38]
        xor     ebp, ebp
        mulx    rbx, rax, [rsi+0x20]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsi+0x28]
        adcx    r11, rax
        adox    r12, rbx
        mov     rdx, [rsi+0x38]
        mulx    rbx, rax, [rsi+0x28]
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rbp
        adox    r14, rbp
        adc     r14, rbp
        xor     ebp, ebp
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [rsi+0x28]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [rsi+0x30]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [rsi+0x38]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, rbp
        adox    r15, rbp
        xor     ebp, ebp
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rbp
        mov     r9d, ebp
        adox    r9, rbp
        adcx    r9, rbp
        add     r14, r9
        adc     r15, rbp
        mov     r8d, ebp
        adc     r8, rbp
        xor     ebp, ebp
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, rbp
        adox    r8, rbp
        adc     r8, rbp
        mov     ecx, 0x1
        add     rcx, r12
        lea     rdx, [rdx-0x1]
        adc     rdx, r13
        lea     rbp, [rbp-0x1]
        mov     rax, rbp
        adc     rbp, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbp
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
        xor     r13d, r13d
        mov     rdx, [rsp+0x60]
        mulx    r9, r8, [rsp+0x40]
        mulx    r10, rbx, [rsp+0x48]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0x50]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0x58]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsp+0x68]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp+0x40]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0x48]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x50]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x58]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsp+0x70]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp+0x40]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x48]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x50]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0x58]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsp+0x78]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp+0x40]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0x48]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0x50]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0x58]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
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
        mov     rdx, 0xffffffff00000001
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
        xor     r13d, r13d
        mov     rdx, [rsp+0x20]
        mulx    r9, r8, [rsi]
        mulx    r10, rbx, [rsi+0x8]
        adc     r9, rbx
        mulx    r11, rbx, [rsi+0x10]
        adc     r10, rbx
        mulx    r12, rbx, [rsi+0x18]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsp+0x28]
        xor     r14d, r14d
        mulx    rbx, rax, [rsi]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsi+0x8]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsi+0x10]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsi+0x18]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsp+0x30]
        xor     r8d, r8d
        mulx    rbx, rax, [rsi]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsi+0x8]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsi+0x10]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsi+0x18]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsp+0x38]
        xor     r9d, r9d
        mulx    rbx, rax, [rsi]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsi+0x8]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsi+0x10]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsi+0x18]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rdx, [rsp+0x60]
        mulx    r15, r8, rdx
        mulx    r10, r9, [rsp+0x68]
        mulx    r12, r11, [rsp+0x78]
        mov     rdx, [rsp+0x70]
        mulx    r14, r13, [rsp+0x78]
        xor     ebp, ebp
        mulx    rbx, rax, [rsp+0x60]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x68]
        adcx    r11, rax
        adox    r12, rbx
        mov     rdx, [rsp+0x78]
        mulx    rbx, rax, [rsp+0x68]
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rbp
        adox    r14, rbp
        adc     r14, rbp
        xor     ebp, ebp
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [rsp+0x68]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [rsp+0x70]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [rsp+0x78]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, rbp
        adox    r15, rbp
        xor     ebp, ebp
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rbp
        mov     r9d, ebp
        adox    r9, rbp
        adcx    r9, rbp
        add     r14, r9
        adc     r15, rbp
        mov     r8d, ebp
        adc     r8, rbp
        xor     ebp, ebp
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, rbp
        adox    r8, rbp
        adc     r8, rbp
        mov     ecx, 0x1
        add     rcx, r12
        lea     rdx, [rdx-0x1]
        adc     rdx, r13
        lea     rbp, [rbp-0x1]
        mov     rax, rbp
        adc     rbp, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbp
        cmovb   r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        mov     rdx, [rsp+0x40]
        mulx    r15, r8, rdx
        mulx    r10, r9, [rsp+0x48]
        mulx    r12, r11, [rsp+0x58]
        mov     rdx, [rsp+0x50]
        mulx    r14, r13, [rsp+0x58]
        xor     ebp, ebp
        mulx    rbx, rax, [rsp+0x40]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x48]
        adcx    r11, rax
        adox    r12, rbx
        mov     rdx, [rsp+0x58]
        mulx    rbx, rax, [rsp+0x48]
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rbp
        adox    r14, rbp
        adc     r14, rbp
        xor     ebp, ebp
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [rsp+0x48]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [rsp+0x50]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [rsp+0x58]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, rbp
        adox    r15, rbp
        xor     ebp, ebp
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rbp
        mov     r9d, ebp
        adox    r9, rbp
        adcx    r9, rbp
        add     r14, r9
        adc     r15, rbp
        mov     r8d, ebp
        adc     r8, rbp
        xor     ebp, ebp
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, rbp
        adox    r8, rbp
        adc     r8, rbp
        mov     ecx, 0x1
        add     rcx, r12
        lea     rdx, [rdx-0x1]
        adc     rdx, r13
        lea     rbp, [rbp-0x1]
        mov     rax, rbp
        adc     rbp, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbp
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        mov     r8, 0xffffffffffffffff
        xor     r10d, r10d
        sub     r8, [rsp+0xa0]
        mov     r9, 0xffffffff
        sbb     r9, [rsp+0xa8]
        sbb     r10, [rsp+0xb0]
        mov     r11, 0xffffffff00000001
        sbb     r11, [rsp+0xb8]
        xor     r12d, r12d
        mov     rdx, 0x9
        mulx    rax, r8, r8
        mulx    rcx, r9, r9
        add     r9, rax
        mulx    rax, r10, r10
        adc     r10, rcx
        mulx    rcx, r11, r11
        adc     r11, rax
        adc     r12, rcx
        mov     rdx, 0xc
        xor     eax, eax
        mulx    rcx, rax, [rsp+0x80]
        adcx    r8, rax
        adox    r9, rcx
        mulx    rcx, rax, [rsp+0x88]
        adcx    r9, rax
        adox    r10, rcx
        mulx    rcx, rax, [rsp+0x90]
        adcx    r10, rax
        adox    r11, rcx
        mulx    rdx, rax, [rsp+0x98]
        adcx    r11, rax
        adox    rdx, r12
        adc     rdx, 0x1
        add     r8, rdx
        mov     rax, 0x100000000
        mulx    rcx, rax, rax
        sbb     rax, 0x0
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        mov     rax, 0xffffffff00000001
        mulx    rcx, rax, rax
        sbb     r11, rax
        sbb     rdx, rcx
        dec     rdx
        mov     eax, 0xffffffff
        and     rax, rdx
        xor     ecx, ecx
        sub     rcx, rax
        add     r8, rdx
        mov     [rsp+0xa0], r8
        adc     r9, rax
        mov     [rsp+0xa8], r9
        adc     r10, 0x0
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
        mov     rdx, [rsp+0x20]
        mulx    r15, r8, rdx
        mulx    r10, r9, [rsp+0x28]
        mulx    r12, r11, [rsp+0x38]
        mov     rdx, [rsp+0x30]
        mulx    r14, r13, [rsp+0x38]
        xor     ebp, ebp
        mulx    rbx, rax, [rsp+0x20]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0x28]
        adcx    r11, rax
        adox    r12, rbx
        mov     rdx, [rsp+0x38]
        mulx    rbx, rax, [rsp+0x28]
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rbp
        adox    r14, rbp
        adc     r14, rbp
        xor     ebp, ebp
        adcx    r9, r9
        adox    r9, r15
        mov     rdx, [rsp+0x28]
        mulx    rdx, rax, rdx
        adcx    r10, r10
        adox    r10, rax
        adcx    r11, r11
        adox    r11, rdx
        mov     rdx, [rsp+0x30]
        mulx    rdx, rax, rdx
        adcx    r12, r12
        adox    r12, rax
        adcx    r13, r13
        adox    r13, rdx
        mov     rdx, [rsp+0x38]
        mulx    r15, rax, rdx
        adcx    r14, r14
        adox    r14, rax
        adcx    r15, rbp
        adox    r15, rbp
        xor     ebp, ebp
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, rbp
        mov     r9d, ebp
        adox    r9, rbp
        adcx    r9, rbp
        add     r14, r9
        adc     r15, rbp
        mov     r8d, ebp
        adc     r8, rbp
        xor     ebp, ebp
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        mov     rdx, 0xffffffff00000001
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, rbp
        adox    r8, rbp
        adc     r8, rbp
        mov     ecx, 0x1
        add     rcx, r12
        lea     rdx, [rdx-0x1]
        adc     rdx, r13
        lea     rbp, [rbp-0x1]
        mov     rax, rbp
        adc     rbp, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
        cmovb   r14, rbp
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        xor     r13d, r13d
        mov     rdx, [rsp+0x60]
        mulx    r9, r8, [rsp+0xa0]
        mulx    r10, rbx, [rsp+0xa8]
        adc     r9, rbx
        mulx    r11, rbx, [rsp+0xb0]
        adc     r10, rbx
        mulx    r12, rbx, [rsp+0xb8]
        adc     r11, rbx
        adc     r12, r13
        mov     rdx, [rsp+0x68]
        xor     r14d, r14d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xb8]
        adcx    r12, rax
        adox    r13, rbx
        adc     r13, r14
        xor     r15d, r15d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r8
        adcx    r9, rax
        adox    r10, rbx
        mulx    rbx, rax, r9
        adcx    r10, rax
        adox    r11, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r8
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r9
        adcx    r12, rax
        adox    r13, rbx
        adcx    r13, r15
        adox    r14, r15
        adc     r14, r15
        mov     rdx, [rsp+0x70]
        xor     r8d, r8d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r10, rax
        adox    r11, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r12, rax
        adox    r13, rbx
        adox    r14, r8
        mulx    rbx, rax, [rsp+0xb8]
        adc     r13, rax
        adc     r14, rbx
        adc     r15, r8
        mov     rdx, [rsp+0x78]
        xor     r9d, r9d
        mulx    rbx, rax, [rsp+0xa0]
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, [rsp+0xa8]
        adcx    r12, rax
        adox    r13, rbx
        mulx    rbx, rax, [rsp+0xb0]
        adcx    r13, rax
        adox    r14, rbx
        adox    r15, r9
        mulx    rbx, rax, [rsp+0xb8]
        adc     r14, rax
        adc     r15, rbx
        adc     r8, r9
        xor     r9d, r9d
        mov     rdx, 0x100000000
        mulx    rbx, rax, r10
        adcx    r11, rax
        adox    r12, rbx
        mulx    rbx, rax, r11
        adcx    r12, rax
        adox    r13, rbx
        not     rdx
        lea     rdx, [rdx+0x2]
        mulx    rbx, rax, r10
        adcx    r13, rax
        adox    r14, rbx
        mulx    rbx, rax, r11
        adcx    r14, rax
        adox    r15, rbx
        adcx    r15, r9
        adox    r8, r9
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rdx
        adc     rdx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rdx
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
        add     r8, rdx
        mov     rax, 0x100000000
        mulx    rcx, rax, rax
        sbb     rax, 0x0
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        mov     rax, 0xffffffff00000001
        mulx    rcx, rax, rax
        sbb     r11, rax
        sbb     rdx, rcx
        dec     rdx
        mov     eax, 0xffffffff
        and     rax, rdx
        xor     ecx, ecx
        sub     rcx, rax
        add     r8, rdx
        mov     [rdi], r8
        adc     r9, rax
        mov     [rdi+0x8], r9
        adc     r10, 0x0
        mov     [rdi+0x10], r10
        adc     r11, rcx
        mov     [rdi+0x18], r11
        mov     r8, 0xffffffffffffffff
        xor     r10d, r10d
        sub     r8, [rsp]
        mov     r9, 0xffffffff
        sbb     r9, [rsp+0x8]
        sbb     r10, [rsp+0x10]
        mov     r11, 0xffffffff00000001
        sbb     r11, [rsp+0x18]
        mov     r12, r11
        shld    r11, r10, 0x3
        shld    r10, r9, 0x3
        shld    r9, r8, 0x3
        shl     r8, 0x3
        shr     r12, 0x3d
        mov     rdx, 0x3
        xor     eax, eax
        mulx    rcx, rax, [rsp+0x60]
        adcx    r8, rax
        adox    r9, rcx
        mulx    rcx, rax, [rsp+0x68]
        adcx    r9, rax
        adox    r10, rcx
        mulx    rcx, rax, [rsp+0x70]
        adcx    r10, rax
        adox    r11, rcx
        mulx    rdx, rax, [rsp+0x78]
        adcx    r11, rax
        adox    rdx, r12
        adc     rdx, 0x1
        add     r8, rdx
        mov     rax, 0x100000000
        mulx    rcx, rax, rax
        sbb     rax, 0x0
        sbb     rcx, 0x0
        sub     r9, rax
        sbb     r10, rcx
        mov     rax, 0xffffffff00000001
        mulx    rcx, rax, rax
        sbb     r11, rax
        sbb     rdx, rcx
        dec     rdx
        mov     eax, 0xffffffff
        and     rax, rdx
        xor     ecx, ecx
        sub     rcx, rax
        add     r8, rdx
        mov     [rdi+0x20], r8
        adc     r9, rax
        mov     [rdi+0x28], r9
        adc     r10, 0x0
        mov     [rdi+0x30], r10
        adc     r11, rcx
        mov     [rdi+0x38], r11
        CFI_INC_RSP(192)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp256_montjscalarmul_p256_montjdouble)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
