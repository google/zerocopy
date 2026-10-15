// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Modular inverse modulo p_521 =  2^521 - 1
// Input x[9]; output z[9]
//
// extern void bignum_inv_p521(uint64_t z[static 9],const uint64_t x[static 9]);
//
// Assuming the 9-digit input x is coprime to p_521, i.e. is not divisible
// by it, returns z < p_521 such that x * z == 1 (mod p_521). Note that
// x does not need to be reduced modulo p_521, but the output always is.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_inv_p521)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_inv_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_inv_p521)
        .text
        .balign 32

// Size in bytes of a 64-bit word

#define N 8

// Pointer-offset pairs for temporaries on stack

#define f rsp+0
#define g rsp+(9*N)
#define u rsp+(18*N)
#define v rsp+(27*N)
#define tmp QWORD PTR [rsp+(36*N)]
#define tmp2 QWORD PTR [rsp+(37*N)]
#define i QWORD PTR [rsp+(38*N)]
#define d QWORD PTR [rsp+(39*N)]

#define mat rsp+(40*N)

// Backup for the input pointer

#define res QWORD PTR [rsp+(44*N)]

// Total size to reserve on the stack

#define NSPACE 45*N

// Syntactic variants to make x86_att version simpler to generate

#define F 0
#define G (9*N)
#define U (18*N)
#define V (27*N)
#define MAT (40*N)

#define ff QWORD PTR [rsp]
#define gg QWORD PTR [rsp+(9*N)]

// Very similar to a subroutine call to the s2n-bignum word_divstep59.
// But different in register usage and returning the final matrix as
//
// [ r8   r10]
// [ r12  r14]
//
// and also returning the matrix still negated (which doesn't matter)

#define divstep59(din,fin,gin)                                          \
        mov     rsi, din;                                               \
        mov     rdx, fin;                                               \
        mov     rcx, gin;                                               \
        mov     rbx, rdx;                                               \
        and     rbx, 0xfffff;                                           \
        movabs  rax, 0xfffffe0000000000;                                \
        or      rbx, rax;                                               \
        and     rcx, 0xfffff;                                           \
        movabs  rax, 0xc000000000000000;                                \
        or      rcx, rax;                                               \
        mov     rax, 0xfffffffffffffffe;                                \
        xor     ebp, ebp;                                               \
        mov     edx, 0x2;                                               \
        mov     rdi, rbx;                                               \
        mov     r8, rax;                                                \
        test    rsi, rsi;                                               \
        cmovs   r8, rbp;                                                \
        test    rcx, 0x1;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        sar     rcx, 1;                                                 \
        mov     eax, 0x100000;                                          \
        lea     rdx, [rbx+rax];                                         \
        lea     rdi, [rcx+rax];                                         \
        shl     rdx, 0x16;                                              \
        shl     rdi, 0x16;                                              \
        sar     rdx, 0x2b;                                              \
        sar     rdi, 0x2b;                                              \
        movabs  rax, 0x20000100000;                                     \
        lea     rbx, [rbx+rax];                                         \
        lea     rcx, [rcx+rax];                                         \
        sar     rbx, 0x2a;                                              \
        sar     rcx, 0x2a;                                              \
        mov     [rsp+MAT], rdx;                                         \
        mov     [rsp+MAT+0x8], rbx;                                     \
        mov     [rsp+MAT+0x10], rdi;                                    \
        mov     [rsp+MAT+0x18], rcx;                                    \
        mov     r12, fin;                                               \
        imul    rdi, r12;                                               \
        imul    r12, rdx;                                               \
        mov     r13, gin;                                               \
        imul    rbx, r13;                                               \
        imul    r13, rcx;                                               \
        add     r12, rbx;                                               \
        add     r13, rdi;                                               \
        sar     r12, 0x14;                                              \
        sar     r13, 0x14;                                              \
        mov     rbx, r12;                                               \
        and     rbx, 0xfffff;                                           \
        movabs  rax, 0xfffffe0000000000;                                \
        or      rbx, rax;                                               \
        mov     rcx, r13;                                               \
        and     rcx, 0xfffff;                                           \
        movabs  rax, 0xc000000000000000;                                \
        or      rcx, rax;                                               \
        mov     rax, 0xfffffffffffffffe;                                \
        mov     edx, 0x2;                                               \
        mov     rdi, rbx;                                               \
        mov     r8, rax;                                                \
        test    rsi, rsi;                                               \
        cmovs   r8, rbp;                                                \
        test    rcx, 0x1;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        sar     rcx, 1;                                                 \
        mov     eax, 0x100000;                                          \
        lea     r8, [rbx+rax];                                          \
        lea     r10, [rcx+rax];                                         \
        shl     r8, 0x16;                                               \
        shl     r10, 0x16;                                              \
        sar     r8, 0x2b;                                               \
        sar     r10, 0x2b;                                              \
        movabs  rax, 0x20000100000;                                     \
        lea     r15, [rbx+rax];                                         \
        lea     r11, [rcx+rax];                                         \
        sar     r15, 0x2a;                                              \
        sar     r11, 0x2a;                                              \
        mov     rbx, r13;                                               \
        mov     rcx, r12;                                               \
        imul    r12, r8;                                                \
        imul    rbx, r15;                                               \
        add     r12, rbx;                                               \
        imul    r13, r11;                                               \
        imul    rcx, r10;                                               \
        add     r13, rcx;                                               \
        sar     r12, 0x14;                                              \
        sar     r13, 0x14;                                              \
        mov     rbx, r12;                                               \
        and     rbx, 0xfffff;                                           \
        movabs  rax, 0xfffffe0000000000;                                \
        or      rbx, rax;                                               \
        mov     rcx, r13;                                               \
        and     rcx, 0xfffff;                                           \
        movabs  rax, 0xc000000000000000;                                \
        or      rcx, rax;                                               \
        mov     rax, [rsp+MAT];                                         \
        imul    rax, r8;                                                \
        mov     rdx, [rsp+MAT+0x10];                                    \
        imul    rdx, r15;                                               \
        imul    r8, [rsp+MAT+0x8];                                      \
        imul    r15, [rsp+MAT+0x18];                                    \
        add     r15, r8;                                                \
        lea     r9, [rax+rdx];                                          \
        mov     rax, [rsp+MAT];                                         \
        imul    rax, r10;                                               \
        mov     rdx, [rsp+MAT+0x10];                                    \
        imul    rdx, r11;                                               \
        imul    r10, [rsp+MAT+0x8];                                     \
        imul    r11, [rsp+MAT+0x18];                                    \
        add     r11, r10;                                               \
        lea     r13, [rax+rdx];                                         \
        mov     rax, 0xfffffffffffffffe;                                \
        mov     edx, 0x2;                                               \
        mov     rdi, rbx;                                               \
        mov     r8, rax;                                                \
        test    rsi, rsi;                                               \
        cmovs   r8, rbp;                                                \
        test    rcx, 0x1;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        cmovs   r8, rbp;                                                \
        mov     rdi, rbx;                                               \
        test    rcx, rdx;                                               \
        cmove   r8, rbp;                                                \
        cmove   rdi, rbp;                                               \
        sar     rcx, 1;                                                 \
        xor     rdi, r8;                                                \
        xor     rsi, r8;                                                \
        bt      r8, 0x3f;                                               \
        cmovb   rbx, rcx;                                               \
        mov     r8, rax;                                                \
        sub     rsi, rax;                                               \
        lea     rcx, [rcx+rdi];                                         \
        sar     rcx, 1;                                                 \
        mov     eax, 0x100000;                                          \
        lea     r8, [rbx+rax];                                          \
        lea     r12, [rcx+rax];                                         \
        shl     r8, 0x15;                                               \
        shl     r12, 0x15;                                              \
        sar     r8, 0x2b;                                               \
        sar     r12, 0x2b;                                              \
        movabs  rax, 0x20000100000;                                     \
        lea     r10, [rbx+rax];                                         \
        lea     r14, [rcx+rax];                                         \
        sar     r10, 0x2b;                                              \
        sar     r14, 0x2b;                                              \
        mov     rax, r9;                                                \
        imul    rax, r8;                                                \
        mov     rdx, r13;                                               \
        imul    rdx, r10;                                               \
        imul    r8, r15;                                                \
        imul    r10, r11;                                               \
        add     r10, r8;                                                \
        lea     r8, [rax+rdx];                                          \
        mov     rax, r9;                                                \
        imul    rax, r12;                                               \
        mov     rdx, r13;                                               \
        imul    rdx, r14;                                               \
        imul    r12, r15;                                               \
        imul    r14, r11;                                               \
        add     r14, r12;                                               \
        lea     r12, [rax+rdx]

S2N_BN_SYMBOL(bignum_inv_p521):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save registers and make room for temporaries

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

// Save the return pointer for the end so we can overwrite rdi later

        mov     res, rdi

// Copy the prime p_521 = 2^521 - 1 into the f variable

        xor     eax, eax
        not     rax
        mov     [rsp+F], rax
        mov     [rsp+F+8], rax
        mov     [rsp+F+16], rax
        mov     [rsp+F+24], rax
        mov     [rsp+F+32], rax
        mov     [rsp+F+40], rax
        mov     [rsp+F+48], rax
        mov     [rsp+F+56], rax
        mov     eax, 0x1FF
        mov     [rsp+F+64], rax

// Copy the input into the g variable, but reduce it strictly mod p_521
// so that g <= f as assumed in the bound proof. This code fragment is
// very similar to bignum_mod_p521_9.

        mov     r8, [rsi+64]
        mov     ebx, 0x1FF
        and     rbx, r8
        shr     r8, 9

        stc
        adc     r8, [rsi]
        mov     r9, [rsi+8]
        adc     r9, 0
        mov     r10, [rsi+16]
        adc     r10, 0
        mov     r11, [rsi+24]
        adc     r11, 0
        mov     r12, [rsi+32]
        adc     r12, 0
        mov     r13, [rsi+40]
        adc     r13, 0
        mov     r14, [rsi+48]
        adc     r14, 0
        mov     r15, [rsi+56]
        adc     r15, 0
        adc     rbx, 0

        cmp     rbx, 512

        sbb     r8, 0
        mov     [rsp+G], r8
        sbb     r9, 0
        mov     [rsp+G+8],  r9
        sbb     r10, 0
        mov     [rsp+G+16], r10
        sbb     r11, 0
        mov     [rsp+G+24], r11
        sbb     r12, 0
        mov     [rsp+G+32], r12
        sbb     r13, 0
        mov     [rsp+G+40], r13
        sbb     r14, 0
        mov     [rsp+G+48], r14
        sbb     r15, 0
        mov     [rsp+G+56], r15
        sbb     rbx, 0
        and     rbx, 0x1FF
        mov     [rsp+G+64], rbx

// Also maintain weakly reduced < 2*p_521 vector [u,v] such that
// [f,g] == x * 2^{1239-59*i} * [u,v] (mod p_521)
// starting with [p_521,x] == x * 2^{1239-59*0} * [0,2^-1239] (mod p_521)
// Note that because (2^{a+521} == 2^a) (mod p_521) we simply have
// (2^-1239 == 2^324) (mod p_521) so the constant initializer is simple.
//
// Based on the standard divstep bound, for inputs <= 2^b we need at least
// n >= (9437 * b + 1) / 4096. Since b is 521, that means 1201 iterations.
// Since we package divstep in multiples of 59 bits, we do 21 blocks of 59
// making *1239* total. (With a bit more effort we could avoid the full 59
// divsteps and use a shorter tail computation, but we keep it simple.)
// Hence, after the 21st iteration we have [f,g] == x * [u,v] and since
// |f| = 1 we get the modular inverse from u by flipping its sign with f.

        xor     eax, eax
        mov     [rsp+U], rax
        mov     [rsp+U+8], rax
        mov     [rsp+U+16], rax
        mov     [rsp+U+24], rax
        mov     [rsp+U+32], rax
        mov     [rsp+U+40], rax
        mov     [rsp+U+48], rax
        mov     [rsp+U+56], rax
        mov     [rsp+U+64], rax

        mov     ebx, 16
        mov     [rsp+V], rax
        mov     [rsp+V+8], rax
        mov     [rsp+V+16], rax
        mov     [rsp+V+24], rax
        mov     [rsp+V+32], rax
        mov     [rsp+V+40], rbx
        mov     [rsp+V+48], rax
        mov     [rsp+V+56], rax
        mov     [rsp+V+64], rax

// Start of main loop. We jump into the middle so that the divstep
// portion is common to the special 21st iteration after a uniform
// first 20.

        mov     i, 21
        mov     d, 1
        jmp     Lbignum_inv_p521_midloop

Lbignum_inv_p521_loop:

// Separate out the matrix into sign-magnitude pairs

        mov     r9, r8
        sar     r9, 63
        xor     r8, r9
        sub     r8, r9

        mov     r11, r10
        sar     r11, 63
        xor     r10, r11
        sub     r10, r11

        mov     r13, r12
        sar     r13, 63
        xor     r12, r13
        sub     r12, r13

        mov     r15, r14
        sar     r15, 63
        xor     r14, r15
        sub     r14, r15

// Adjust the initial values to allow for complement instead of negation
// This initial offset is the same for [f,g] and [u,v] compositions.
// Save it in temporary storage for the [u,v] part and do [f,g] first.

        mov     rax, r8
        and     rax, r9
        mov     rdi, r10
        and     rdi, r11
        add     rdi, rax
        mov     tmp, rdi

        mov     rax, r12
        and     rax, r13
        mov     rsi, r14
        and     rsi, r15
        add     rsi, rax
        mov     tmp2, rsi

// Now the computation of the updated f and g values. This maintains a
// 2-word carry between stages so we can conveniently insert the shift
// right by 59 before storing back, and not overwrite digits we need
// again of the old f and g values.
//
// Digit 0 of [f,g]

        xor     ebx, ebx
        mov     rax, [rsp+F]
        xor     rax, r9
        mul     r8
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+G]
        xor     rax, r11
        mul     r10
        add     rdi, rax
        adc     rbx, rdx

        xor     ebp, ebp
        mov     rax, [rsp+F]
        xor     rax, r13
        mul     r12
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+G]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx

// Digit 1 of [f,g]

        xor     ecx, ecx
        mov     rax, [rsp+F+N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+G+N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx
        shrd    rdi, rbx, 59
        mov     [rsp+F], rdi

        xor     edi, edi
        mov     rax, [rsp+F+N]
        xor     rax, r13
        mul     r12
        add     rbp, rax
        adc     rdi, rdx
        mov     rax, [rsp+G+N]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rdi, rdx
        shrd    rsi, rbp, 59
        mov     [rsp+G], rsi

// Digit 2 of [f,g]

        xor     esi, esi
        mov     rax, [rsp+F+2*N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rsi, rdx
        mov     rax, [rsp+G+2*N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rsi, rdx
        shrd    rbx, rcx, 59
        mov     [rsp+F+N], rbx

        xor     ebx, ebx
        mov     rax, [rsp+F+2*N]
        xor     rax, r13
        mul     r12
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+G+2*N]
        xor     rax, r15
        mul     r14
        add     rdi, rax
        adc     rbx, rdx
        shrd    rbp, rdi, 59
        mov     [rsp+G+N], rbp

// Digit 3 of [f,g]

        xor     ebp, ebp
        mov     rax, [rsp+F+3*N]
        xor     rax, r9
        mul     r8
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+G+3*N]
        xor     rax, r11
        mul     r10
        add     rsi, rax
        adc     rbp, rdx
        shrd    rcx, rsi, 59
        mov     [rsp+F+2*N], rcx

        xor     ecx, ecx
        mov     rax, [rsp+F+3*N]
        xor     rax, r13
        mul     r12
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+G+3*N]
        xor     rax, r15
        mul     r14
        add     rbx, rax
        adc     rcx, rdx
        shrd    rdi, rbx, 59
        mov     [rsp+G+2*N], rdi

// Digit 4 of [f,g]

        xor     edi, edi
        mov     rax, [rsp+F+4*N]
        xor     rax, r9
        mul     r8
        add     rbp, rax
        adc     rdi, rdx
        mov     rax, [rsp+G+4*N]
        xor     rax, r11
        mul     r10
        add     rbp, rax
        adc     rdi, rdx
        shrd    rsi, rbp, 59
        mov     [rsp+F+3*N], rsi

        xor     esi, esi
        mov     rax, [rsp+F+4*N]
        xor     rax, r13
        mul     r12
        add     rcx, rax
        adc     rsi, rdx
        mov     rax, [rsp+G+4*N]
        xor     rax, r15
        mul     r14
        add     rcx, rax
        adc     rsi, rdx
        shrd    rbx, rcx, 59
        mov     [rsp+G+3*N], rbx

// Digit 5 of [f,g]

        xor     ebx, ebx
        mov     rax, [rsp+F+5*N]
        xor     rax, r9
        mul     r8
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+G+5*N]
        xor     rax, r11
        mul     r10
        add     rdi, rax
        adc     rbx, rdx
        shrd    rbp, rdi, 59
        mov     [rsp+F+4*N], rbp

        xor     ebp, ebp
        mov     rax, [rsp+F+5*N]
        xor     rax, r13
        mul     r12
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+G+5*N]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        shrd    rcx, rsi, 59
        mov     [rsp+G+4*N], rcx

// Digit 6 of [f,g]

        xor     ecx, ecx
        mov     rax, [rsp+F+6*N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+G+6*N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx
        shrd    rdi, rbx, 59
        mov     [rsp+F+5*N], rdi

        xor     edi, edi
        mov     rax, [rsp+F+6*N]
        xor     rax, r13
        mul     r12
        add     rbp, rax
        adc     rdi, rdx
        mov     rax, [rsp+G+6*N]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rdi, rdx
        shrd    rsi, rbp, 59
        mov     [rsp+G+5*N], rsi

// Digit 7 of [f,g]

        xor     esi, esi
        mov     rax, [rsp+F+7*N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rsi, rdx
        mov     rax, [rsp+G+7*N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rsi, rdx
        shrd    rbx, rcx, 59
        mov     [rsp+F+6*N], rbx

        xor     ebx, ebx
        mov     rax, [rsp+F+7*N]
        xor     rax, r13
        mul     r12
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+G+7*N]
        xor     rax, r15
        mul     r14
        add     rdi, rax
        adc     rbx, rdx
        shrd    rbp, rdi, 59
        mov     [rsp+G+6*N], rbp

// Digits 8 and 9 of [f,g]

        mov     rax, [rsp+F+8*N]
        xor     rax, r9
        mov     rbp, rax
        sar     rbp, 63
        and     rbp, r8
        neg     rbp
        mul     r8
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+G+8*N]
        xor     rax, r11
        mov     rdx, rax
        sar     rdx, 63
        and     rdx, r10
        sub     rbp, rdx
        mul     r10
        add     rsi, rax
        adc     rbp, rdx
        shrd    rcx, rsi, 59
        mov     [rsp+F+7*N], rcx
        shrd    rsi, rbp, 59

        mov     rax, [rsp+F+8*N]
        mov     [rsp+F+8*N], rsi

        xor     rax, r13
        mov     rsi, rax
        sar     rsi, 63
        and     rsi, r12
        neg     rsi
        mul     r12
        add     rbx, rax
        adc     rsi, rdx
        mov     rax, [rsp+G+8*N]
        xor     rax, r15
        mov     rdx, rax
        sar     rdx, 63
        and     rdx, r14
        sub     rsi, rdx
        mul     r14
        add     rbx, rax
        adc     rsi, rdx
        shrd    rdi, rbx, 59
        mov     [rsp+G+7*N], rdi
        shrd    rbx, rsi, 59
        mov     [rsp+G+8*N], rbx

// Get the initial carries back from storage and do the [u,v] accumulation

        mov     rbx, tmp
        mov     rbp, tmp2

// Digit 0 of [u,v]

        xor     ecx, ecx
        mov     rax, [rsp+U]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx

        xor     esi, esi
        mov     rax, [rsp+U]
        xor     rax, r13
        mul     r12
        mov     [rsp+U], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+V]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+V], rbp

// Digit 1 of [u,v]

        xor     ebx, ebx
        mov     rax, [rsp+U+N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rbx, rdx

        xor     ebp, ebp
        mov     rax, [rsp+U+N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+N], rcx
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+V+N]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        mov     [rsp+V+N], rsi

// Digit 2 of [u,v]

        xor     ecx, ecx
        mov     rax, [rsp+U+2*N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+2*N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx

        xor     esi, esi
        mov     rax, [rsp+U+2*N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+2*N], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+V+2*N]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+V+2*N], rbp

// Digit 3 of [u,v]

        xor     ebx, ebx
        mov     rax, [rsp+U+3*N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+3*N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rbx, rdx

        xor     ebp, ebp
        mov     rax, [rsp+U+3*N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+3*N], rcx
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+V+3*N]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        mov     [rsp+V+3*N], rsi

// Digit 4 of [u,v]

        xor     ecx, ecx
        mov     rax, [rsp+U+4*N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+4*N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx

        xor     esi, esi
        mov     rax, [rsp+U+4*N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+4*N], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+V+4*N]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+V+4*N], rbp

// Digit 5 of [u,v]

        xor     ebx, ebx
        mov     rax, [rsp+U+5*N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+5*N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rbx, rdx

        xor     ebp, ebp
        mov     rax, [rsp+U+5*N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+5*N], rcx
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+V+5*N]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        mov     [rsp+V+5*N], rsi

// Digit 6 of [u,v]

        xor     ecx, ecx
        mov     rax, [rsp+U+6*N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+6*N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx

        xor     esi, esi
        mov     rax, [rsp+U+6*N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+6*N], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+V+6*N]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+V+6*N], rbp

// Digit 7 of [u,v]

        xor     ebx, ebx
        mov     rax, [rsp+U+7*N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+7*N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rbx, rdx

        xor     ebp, ebp
        mov     rax, [rsp+U+7*N]
        xor     rax, r13
        mul     r12
        mov     [rsp+U+7*N], rcx
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+V+7*N]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        mov     [rsp+V+7*N], rsi

// Digits 8 and 9 of u (top is unsigned)

        mov     rax, [rsp+U+8*N]
        xor     rax, r9
        mov     rcx, r9
        and     rcx, r8
        neg     rcx
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+8*N]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     rcx, rdx
        mul     r10
        add     rbx, rax
        adc     rdx, rcx

// Modular reduction of u

        mov     rax, rdx
        shld    rdx, rbx, 55
        sar     rax, 63
        add     rdx, rax
        mov     rax, rdx
        shl     rdx, 9
        sub     rbx, rdx
        mov     rdx, rax
        sar     rax, 63
        mov     rcx, [rsp+U]
        add     rcx, rdx
        mov     [rsp+U], rcx
        mov     rcx, [rsp+U+N]
        adc     rcx, rax
        mov     [rsp+U+N], rcx
        mov     rcx, [rsp+U+2*N]
        adc     rcx, rax
        mov     [rsp+U+2*N], rcx
        mov     rcx, [rsp+U+3*N]
        adc     rcx, rax
        mov     [rsp+U+3*N], rcx
        mov     rcx, [rsp+U+4*N]
        adc     rcx, rax
        mov     [rsp+U+4*N], rcx
        mov     rcx, [rsp+U+5*N]
        adc     rcx, rax
        mov     [rsp+U+5*N], rcx
        mov     rcx, [rsp+U+6*N]
        adc     rcx, rax
        mov     [rsp+U+6*N], rcx
        mov     rcx, [rsp+U+7*N]
        adc     rcx, rax
        mov     [rsp+U+7*N], rcx
        adc     rbx, rax

// Preload for last use of old u digit 8

        mov     rax, [rsp+U+8*N]
        mov     [rsp+U+8*N], rbx

// Digits 8 and 9 of v (top is unsigned)

        xor     rax, r13
        mov     rbx, r13
        and     rbx, r12
        neg     rbx
        mul     r12
        add     rbp, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+8*N]
        xor     rax, r15
        mov     rdx, r15
        and     rdx, r14
        sub     rbx, rdx
        mul     r14
        add     rbp, rax
        adc     rdx, rbx

// Modular reduction of v

        mov     rax, rdx
        shld    rdx, rbp, 55
        sar     rax, 63
        add     rdx, rax
        mov     rax, rdx
        shl     rdx, 9
        sub     rbp, rdx
        mov     rdx, rax
        sar     rax, 63
        mov     rcx, [rsp+V]
        add     rcx, rdx
        mov     [rsp+V], rcx
        mov     rcx, [rsp+V+N]
        adc     rcx, rax
        mov     [rsp+V+N], rcx
        mov     rcx, [rsp+V+2*N]
        adc     rcx, rax
        mov     [rsp+V+2*N], rcx
        mov     rcx, [rsp+V+3*N]
        adc     rcx, rax
        mov     [rsp+V+3*N], rcx
        mov     rcx, [rsp+V+4*N]
        adc     rcx, rax
        mov     [rsp+V+4*N], rcx
        mov     rcx, [rsp+V+5*N]
        adc     rcx, rax
        mov     [rsp+V+5*N], rcx
        mov     rcx, [rsp+V+6*N]
        adc     rcx, rax
        mov     [rsp+V+6*N], rcx
        mov     rcx, [rsp+V+7*N]
        adc     rcx, rax
        mov     [rsp+V+7*N], rcx
        adc     rbp, rax
        mov     [rsp+V+8*N], rbp

Lbignum_inv_p521_midloop:

        divstep59(d,ff,gg)
        mov     d, rsi

// Next iteration

        dec     i
        jnz     Lbignum_inv_p521_loop

// The 21st and last iteration does not need anything except the
// u value and the sign of f; the latter can be obtained from the
// lowest word of f. So it's done differently from the main loop.
// Find the sign of the new f. For this we just need one digit
// since we know (for in-scope cases) that f is either +1 or -1.
// We don't explicitly shift right by 59 either, but looking at
// bit 63 (or any bit >= 60) of the unshifted result is enough
// to distinguish -1 from +1; this is then made into a mask.

        mov     rax, [rsp+F]
        mov     rcx, [rsp+G]
        imul    rax, r8
        imul    rcx, r10
        add     rax, rcx
        sar     rax, 63

// Now separate out the matrix into sign-magnitude pairs
// and adjust each one based on the sign of f.
//
// Note that at this point we expect |f|=1 and we got its
// sign above, so then since [f,0] == x * [u,v] (mod p_521)
// we want to flip the sign of u according to that of f.

        mov     r9, r8
        sar     r9, 63
        xor     r8, r9
        sub     r8, r9
        xor     r9, rax

        mov     r11, r10
        sar     r11, 63
        xor     r10, r11
        sub     r10, r11
        xor     r11, rax

        mov     r13, r12
        sar     r13, 63
        xor     r12, r13
        sub     r12, r13
        xor     r13, rax

        mov     r15, r14
        sar     r15, 63
        xor     r14, r15
        sub     r14, r15
        xor     r15, rax

// Adjust the initial value to allow for complement instead of negation

        mov     rax, r8
        and     rax, r9
        mov     rbx, r10
        and     rbx, r11
        add     rbx, rax

// Digit 0 of u

        xor     ecx, ecx
        mov     rax, [rsp+U]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        mov     [rsp+U], rbx
        adc     rcx, rdx

// Digit 1 of u

        xor     ebx, ebx
        mov     rax, [rsp+U+N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        mov     [rsp+U+N], rcx
        adc     rbx, rdx

// Digit 2 of u

        xor     ecx, ecx
        mov     rax, [rsp+U+2*N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+2*N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        mov     [rsp+U+2*N], rbx
        adc     rcx, rdx

// Digit 3 of u

        xor     ebx, ebx
        mov     rax, [rsp+U+3*N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+3*N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        mov     [rsp+U+3*N], rcx
        adc     rbx, rdx

// Digit 4 of u

        xor     ecx, ecx
        mov     rax, [rsp+U+4*N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+4*N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        mov     [rsp+U+4*N], rbx
        adc     rcx, rdx

// Digit 5 of u

        xor     ebx, ebx
        mov     rax, [rsp+U+5*N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+5*N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        mov     [rsp+U+5*N], rcx
        adc     rbx, rdx

// Digit 6 of u

        xor     ecx, ecx
        mov     rax, [rsp+U+6*N]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+6*N]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        mov     [rsp+U+6*N], rbx
        adc     rcx, rdx

// Digit 7 of u

        xor     ebx, ebx
        mov     rax, [rsp+U+7*N]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+V+7*N]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        mov     [rsp+U+7*N], rcx
        adc     rbx, rdx

// Digits 8 and 9 of u (top is unsigned)

        mov     rax, [rsp+U+8*N]
        xor     rax, r9
        mov     rcx, r9
        and     rcx, r8
        neg     rcx
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+V+8*N]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     rcx, rdx
        mul     r10
        add     rbx, rax
        adc     rdx, rcx

// Modular reduction of u

        mov     rax, rdx
        shld    rdx, rbx, 55
        sar     rax, 63
        add     rdx, rax
        mov     rax, rdx
        shl     rdx, 9
        sub     rbx, rdx
        mov     rdx, rax
        sar     rax, 63
        mov     rcx, [rsp+U]
        add     rcx, rdx
        mov     [rsp+U], rcx
        mov     rcx, [rsp+U+N]
        adc     rcx, rax
        mov     [rsp+U+N], rcx
        mov     rcx, [rsp+U+2*N]
        adc     rcx, rax
        mov     [rsp+U+2*N], rcx
        mov     rcx, [rsp+U+3*N]
        adc     rcx, rax
        mov     [rsp+U+3*N], rcx
        mov     rcx, [rsp+U+4*N]
        adc     rcx, rax
        mov     [rsp+U+4*N], rcx
        mov     rcx, [rsp+U+5*N]
        adc     rcx, rax
        mov     [rsp+U+5*N], rcx
        mov     rcx, [rsp+U+6*N]
        adc     rcx, rax
        mov     [rsp+U+6*N], rcx
        mov     rcx, [rsp+U+7*N]
        adc     rcx, rax
        mov     [rsp+U+7*N], rcx
        adc     rbx, rax
        mov     [rsp+U+8*N], rbx

// Further strict reduction ready for the output, which just means
// a conditional subtraction of p_521

        xor     eax, eax
        not     rax
        mov     r8, [rsp+U]
        sub     r8, rax
        mov     r9, [rsp+U+N]
        sbb     r9, rax
        mov     r10, [rsp+U+2*N]
        sbb     r10, rax
        mov     r11, [rsp+U+3*N]
        sbb     r11, rax
        mov     r12, [rsp+U+4*N]
        sbb     r12, rax
        mov     r13, [rsp+U+5*N]
        sbb     r13, rax
        mov     r14, [rsp+U+6*N]
        sbb     r14, rax
        mov     r15, [rsp+U+7*N]
        sbb     r15, rax
        mov     eax, 0x1FF
        mov     rbp, [rsp+U+8*N]
        sbb     rbp, rax

        cmovc   r8, [rsp+U]
        cmovc   r9, [rsp+U+N]
        cmovc   r10, [rsp+U+2*N]
        cmovc   r11, [rsp+U+3*N]
        cmovc   r12, [rsp+U+4*N]
        cmovc   r13, [rsp+U+5*N]
        cmovc   r14, [rsp+U+6*N]
        cmovc   r15, [rsp+U+7*N]
        cmovc   rbp, [rsp+U+8*N]

// Store it back to the final output

        mov     rdi, res
        mov     [rdi], r8
        mov     [rdi+N], r9
        mov     [rdi+2*N], r10
        mov     [rdi+3*N], r11
        mov     [rdi+4*N], r12
        mov     [rdi+5*N], r13
        mov     [rdi+6*N], r14
        mov     [rdi+7*N], r15
        mov     [rdi+8*N], rbp

// Restore stack and registers

        CFI_INC_RSP(NSPACE)

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

S2N_BN_SIZE_DIRECTIVE(bignum_inv_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
