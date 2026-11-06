// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point mixed addition on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates
//
//    extern void sm2_montjmixadd(uint64_t p3[static 12],
//                                const uint64_t p1[static 12],
//                                const uint64_t p2[static 8]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
// The "mixed" part means that p2 only has x and y coordinates, with the
// implicit z coordinate assumed to be the identity.
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sm2_montjmixadd)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sm2_montjmixadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sm2_montjmixadd)
        .text

// Size of individual field elements

#define NUMSIZE 32

// Pointer-offset pairs for inputs and outputs
// These assume rdi = p3, rsi = p1 and rbp = p2,
// which needs to be set up explicitly before use.
// By design, none of the code macros modify any of
// these, so we maintain the assignments throughout.

#define x_1 rsi+0
#define y_1 rsi+NUMSIZE
#define z_1 rsi+(2*NUMSIZE)

#define x_2 rbp+0
#define y_2 rbp+NUMSIZE

#define x_3 rdi+0
#define y_3 rdi+NUMSIZE
#define z_3 rdi+(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define zp2 rsp+(NUMSIZE*0)
#define ww rsp+(NUMSIZE*0)
#define resx rsp+(NUMSIZE*0)

#define yd rsp+(NUMSIZE*1)
#define y2a rsp+(NUMSIZE*1)

#define x2a rsp+(NUMSIZE*2)
#define zzx2 rsp+(NUMSIZE*2)

#define zz rsp+(NUMSIZE*3)
#define t1 rsp+(NUMSIZE*3)

#define t2 rsp+(NUMSIZE*4)
#define zzx1 rsp+(NUMSIZE*4)
#define resy rsp+(NUMSIZE*4)

#define xd rsp+(NUMSIZE*5)
#define resz rsp+(NUMSIZE*5)

#define NSPACE NUMSIZE*6

// Corresponds to bignum_montmul_sm2 except for registers

#define montmul_sm2(P0,P1,P2)                   \
        xor     ecx, ecx;                       \
        mov     rdx, [P2];                      \
        mulx    r9, r8, [P1];                   \
        mulx    r10, rax, [P1+0x8];             \
        add     r9, rax;                        \
        mulx    r11, rax, [P1+0x10];            \
        adc     r10, rax;                       \
        mulx    r12, rax, [P1+0x18];            \
        adc     r11, rax;                       \
        adc     r12, rcx;                       \
        xor     ecx, ecx;                       \
        mov     rdx, [P2+0x8];                  \
        mulx    rbx, rax, [P1];                 \
        adcx    r9, rax;                        \
        adox    r10, rbx;                       \
        mulx    rbx, rax, [P1+0x8];             \
        adcx    r10, rax;                       \
        adox    r11, rbx;                       \
        mulx    rbx, rax, [P1+0x10];            \
        adcx    r11, rax;                       \
        adox    r12, rbx;                       \
        mulx    r13, rax, [P1+0x18];            \
        adcx    r12, rax;                       \
        adox    r13, rcx;                       \
        adcx    r13, rcx;                       \
        xor     ecx, ecx;                       \
        mov     rdx, [P2+0x10];                 \
        mulx    rbx, rax, [P1];                 \
        adcx    r10, rax;                       \
        adox    r11, rbx;                       \
        mulx    rbx, rax, [P1+0x8];             \
        adcx    r11, rax;                       \
        adox    r12, rbx;                       \
        mulx    rbx, rax, [P1+0x10];            \
        adcx    r12, rax;                       \
        adox    r13, rbx;                       \
        mulx    r14, rax, [P1+0x18];            \
        adcx    r13, rax;                       \
        adox    r14, rcx;                       \
        adcx    r14, rcx;                       \
        xor     ecx, ecx;                       \
        mov     rdx, [P2+0x18];                 \
        mulx    rbx, rax, [P1];                 \
        adcx    r11, rax;                       \
        adox    r12, rbx;                       \
        mulx    rbx, rax, [P1+0x8];             \
        adcx    r12, rax;                       \
        adox    r13, rbx;                       \
        mulx    rbx, rax, [P1+0x10];            \
        adcx    r13, rax;                       \
        adox    r14, rbx;                       \
        mulx    r15, rax, [P1+0x18];            \
        adcx    r14, rax;                       \
        adox    r15, rcx;                       \
        adcx    r15, rcx;                       \
        mov     rax, r8;                        \
        shl     rax, 0x20;                      \
        mov     rcx, r8;                        \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r8;                        \
        sbb     rcx, 0x0;                       \
        sub     r9, rax;                        \
        sbb     r10, rcx;                       \
        sbb     r11, rdx;                       \
        sbb     r8, rbx;                        \
        mov     rax, r9;                        \
        shl     rax, 0x20;                      \
        mov     rcx, r9;                        \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r9;                        \
        sbb     rcx, 0x0;                       \
        sub     r10, rax;                       \
        sbb     r11, rcx;                       \
        sbb     r8, rdx;                        \
        sbb     r9, rbx;                        \
        mov     rax, r10;                       \
        shl     rax, 0x20;                      \
        mov     rcx, r10;                       \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r10;                       \
        sbb     rcx, 0x0;                       \
        sub     r11, rax;                       \
        sbb     r8, rcx;                        \
        sbb     r9, rdx;                        \
        sbb     r10, rbx;                       \
        mov     rax, r11;                       \
        shl     rax, 0x20;                      \
        mov     rcx, r11;                       \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r11;                       \
        sbb     rcx, 0x0;                       \
        sub     r8, rax;                        \
        sbb     r9, rcx;                        \
        sbb     r10, rdx;                       \
        sbb     r11, rbx;                       \
        xor     eax, eax;                       \
        add     r12, r8;                        \
        adc     r13, r9;                        \
        adc     r14, r10;                       \
        adc     r15, r11;                       \
        adc     rax, rax;                       \
        mov     ecx, 0x1;                       \
        mov     edx, 0xffffffff;                \
        xor     ebx, ebx;                       \
        add     rcx, r12;                       \
        lea     r11, [rdx+0x1];                 \
        adc     rdx, r13;                       \
        lea     r8, [rbx-0x1];                  \
        adc     rbx, r14;                       \
        adc     r11, r15;                       \
        adc     r8, rax;                        \
        cmovb   r12, rcx;                       \
        cmovb   r13, rdx;                       \
        cmovb   r14, rbx;                       \
        cmovb   r15, r11;                       \
        mov     [P0], r12;                      \
        mov     [P0+0x8], r13;                  \
        mov     [P0+0x10], r14;                 \
        mov     [P0+0x18], r15

// Corresponds to bignum_montsqr_sm2 except for registers

#define montsqr_sm2(P0,P1)                      \
        mov     rdx, [P1];                      \
        mulx    r15, r8, rdx;                   \
        mulx    r10, r9, [P1+0x8];              \
        mulx    r12, r11, [P1+0x18];            \
        mov     rdx, [P1+0x10];                 \
        mulx    r14, r13, [P1+0x18];            \
        xor     ecx, ecx;                       \
        mulx    rbx, rax, [P1];                 \
        adcx    r10, rax;                       \
        adox    r11, rbx;                       \
        mulx    rbx, rax, [P1+0x8];             \
        adcx    r11, rax;                       \
        adox    r12, rbx;                       \
        mov     rdx, [P1+0x18];                 \
        mulx    rbx, rax, [P1+0x8];             \
        adcx    r12, rax;                       \
        adox    r13, rbx;                       \
        adcx    r13, rcx;                       \
        adox    r14, rcx;                       \
        adc     r14, rcx;                       \
        xor     ecx, ecx;                       \
        adcx    r9, r9;                         \
        adox    r9, r15;                        \
        mov     rdx, [P1+0x8];                  \
        mulx    rdx, rax, rdx;                  \
        adcx    r10, r10;                       \
        adox    r10, rax;                       \
        adcx    r11, r11;                       \
        adox    r11, rdx;                       \
        mov     rdx, [P1+0x10];                 \
        mulx    rdx, rax, rdx;                  \
        adcx    r12, r12;                       \
        adox    r12, rax;                       \
        adcx    r13, r13;                       \
        adox    r13, rdx;                       \
        mov     rdx, [P1+0x18];                 \
        mulx    r15, rax, rdx;                  \
        adcx    r14, r14;                       \
        adox    r14, rax;                       \
        adcx    r15, rcx;                       \
        adox    r15, rcx;                       \
        mov     rax, r8;                        \
        shl     rax, 0x20;                      \
        mov     rcx, r8;                        \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r8;                        \
        sbb     rcx, 0x0;                       \
        sub     r9, rax;                        \
        sbb     r10, rcx;                       \
        sbb     r11, rdx;                       \
        sbb     r8, rbx;                        \
        mov     rax, r9;                        \
        shl     rax, 0x20;                      \
        mov     rcx, r9;                        \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r9;                        \
        sbb     rcx, 0x0;                       \
        sub     r10, rax;                       \
        sbb     r11, rcx;                       \
        sbb     r8, rdx;                        \
        sbb     r9, rbx;                        \
        mov     rax, r10;                       \
        shl     rax, 0x20;                      \
        mov     rcx, r10;                       \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r10;                       \
        sbb     rcx, 0x0;                       \
        sub     r11, rax;                       \
        sbb     r8, rcx;                        \
        sbb     r9, rdx;                        \
        sbb     r10, rbx;                       \
        mov     rax, r11;                       \
        shl     rax, 0x20;                      \
        mov     rcx, r11;                       \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r11;                       \
        sbb     rcx, 0x0;                       \
        sub     r8, rax;                        \
        sbb     r9, rcx;                        \
        sbb     r10, rdx;                       \
        sbb     r11, rbx;                       \
        xor     eax, eax;                       \
        add     r12, r8;                        \
        adc     r13, r9;                        \
        adc     r14, r10;                       \
        adc     r15, r11;                       \
        adc     rax, rax;                       \
        mov     ecx, 0x1;                       \
        mov     edx, 0xffffffff;                \
        xor     ebx, ebx;                       \
        add     rcx, r12;                       \
        lea     r11, [rdx+0x1];                 \
        adc     rdx, r13;                       \
        lea     r8, [rbx-0x1];                  \
        adc     rbx, r14;                       \
        adc     r11, r15;                       \
        adc     r8, rax;                        \
        cmovb   r12, rcx;                       \
        cmovb   r13, rdx;                       \
        cmovb   r14, rbx;                       \
        cmovb   r15, r11;                       \
        mov     [P0], r12;                      \
        mov     [P0+0x8], r13;                  \
        mov     [P0+0x10], r14;                 \
        mov     [P0+0x18], r15

// Almost-Montgomery variant which we use when an input to other muls
// with the other argument fully reduced (which is always safe).

#define amontsqr_sm2(P0,P1)                     \
        mov     rdx, [P1];                      \
        mulx    r15, r8, rdx;                   \
        mulx    r10, r9, [P1+0x8];              \
        mulx    r12, r11, [P1+0x18];            \
        mov     rdx, [P1+0x10];                 \
        mulx    r14, r13, [P1+0x18];            \
        xor     ecx, ecx;                       \
        mulx    rbx, rax, [P1];                 \
        adcx    r10, rax;                       \
        adox    r11, rbx;                       \
        mulx    rbx, rax, [P1+0x8];             \
        adcx    r11, rax;                       \
        adox    r12, rbx;                       \
        mov     rdx, [P1+0x18];                 \
        mulx    rbx, rax, [P1+0x8];             \
        adcx    r12, rax;                       \
        adox    r13, rbx;                       \
        adcx    r13, rcx;                       \
        adox    r14, rcx;                       \
        adc     r14, rcx;                       \
        xor     ecx, ecx;                       \
        adcx    r9, r9;                         \
        adox    r9, r15;                        \
        mov     rdx, [P1+0x8];                  \
        mulx    rdx, rax, rdx;                  \
        adcx    r10, r10;                       \
        adox    r10, rax;                       \
        adcx    r11, r11;                       \
        adox    r11, rdx;                       \
        mov     rdx, [P1+0x10];                 \
        mulx    rdx, rax, rdx;                  \
        adcx    r12, r12;                       \
        adox    r12, rax;                       \
        adcx    r13, r13;                       \
        adox    r13, rdx;                       \
        mov     rdx, [P1+0x18];                 \
        mulx    r15, rax, rdx;                  \
        adcx    r14, r14;                       \
        adox    r14, rax;                       \
        adcx    r15, rcx;                       \
        adox    r15, rcx;                       \
        mov     rax, r8;                        \
        shl     rax, 0x20;                      \
        mov     rcx, r8;                        \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r8;                        \
        sbb     rcx, 0x0;                       \
        sub     r9, rax;                        \
        sbb     r10, rcx;                       \
        sbb     r11, rdx;                       \
        sbb     r8, rbx;                        \
        mov     rax, r9;                        \
        shl     rax, 0x20;                      \
        mov     rcx, r9;                        \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r9;                        \
        sbb     rcx, 0x0;                       \
        sub     r10, rax;                       \
        sbb     r11, rcx;                       \
        sbb     r8, rdx;                        \
        sbb     r9, rbx;                        \
        mov     rax, r10;                       \
        shl     rax, 0x20;                      \
        mov     rcx, r10;                       \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r10;                       \
        sbb     rcx, 0x0;                       \
        sub     r11, rax;                       \
        sbb     r8, rcx;                        \
        sbb     r9, rdx;                        \
        sbb     r10, rbx;                       \
        mov     rax, r11;                       \
        shl     rax, 0x20;                      \
        mov     rcx, r11;                       \
        shr     rcx, 0x20;                      \
        mov     rdx, rax;                       \
        mov     rbx, rcx;                       \
        sub     rax, r11;                       \
        sbb     rcx, 0x0;                       \
        sub     r8, rax;                        \
        sbb     r9, rcx;                        \
        sbb     r10, rdx;                       \
        sbb     r11, rbx;                       \
        add     r12, r8;                        \
        adc     r13, r9;                        \
        adc     r14, r10;                       \
        adc     r15, r11;                       \
        sbb     rax, rax;                       \
        mov     rbx, 0xffffffff00000000;        \
        mov     rcx, rax;                       \
        and     rbx, rax;                       \
        btr     rcx, 32;                        \
        sub     r12, rax;                       \
        sbb     r13, rbx;                       \
        sbb     r14, rax;                       \
        sbb     r15, rcx;                       \
        mov     [P0], r12;                      \
        mov     [P0+0x8], r13;                  \
        mov     [P0+0x10], r14;                 \
        mov     [P0+0x18], r15

// Corresponds exactly to bignum_sub_sm2

#define sub_sm2(P0,P1,P2)                       \
        mov     rax, [P1];                      \
        sub     rax, [P2];                      \
        mov     rcx, [P1+0x8];                  \
        sbb     rcx, [P2+0x8];                  \
        mov     r8, [P1+0x10];                  \
        sbb     r8, [P2+0x10];                  \
        mov     r9, [P1+0x18];                  \
        sbb     r9, [P2+0x18];                  \
        mov     r10, 0xffffffff00000000;        \
        sbb     r11, r11;                       \
        and     r10, r11;                       \
        mov     rdx, r11;                       \
        btr     rdx, 0x20;                      \
        add     rax, r11;                       \
        mov     [P0], rax;                      \
        adc     rcx, r10;                       \
        mov     [P0+0x8], rcx;                  \
        adc     r8, r11;                        \
        mov     [P0+0x10], r8;                  \
        adc     r9, rdx;                        \
        mov     [P0+0x18], r9

// Additional macros to help with final multiplexing

#define testzero4(P)                            \
        mov     rax, [P];                       \
        mov     rdx, [P+8];                     \
        or      rax, [P+16];                    \
        or      rdx, [P+24];                    \
        or      rax, rdx

#define mux4(r0,r1,r2,r3,PNE,PEQ)               \
        mov     r0, [PNE];                      \
        mov     rax, [PEQ];                     \
        cmovz   r0, rax;                        \
        mov     r1, [PNE+8];                    \
        mov     rax, [PEQ+8];                   \
        cmovz   r1, rax;                        \
        mov     r2, [PNE+16];                   \
        mov     rax, [PEQ+16];                  \
        cmovz   r2, rax;                        \
        mov     r3, [PNE+24];                   \
        mov     rax, [PEQ+24];                  \
        cmovz   r3, rax

#define load4(r0,r1,r2,r3,P)                    \
        mov     r0, [P];                        \
        mov     r1, [P+8];                      \
        mov     r2, [P+16];                     \
        mov     r3, [P+24]

#define store4(P,r0,r1,r2,r3)                   \
        mov     [P], r0;                        \
        mov     [P+8], r1;                      \
        mov     [P+16], r2;                     \
        mov     [P+24], r3

S2N_BN_SYMBOL(sm2_montjmixadd):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save registers and make room on stack for temporary variables
// Put the input y in rbp where it lasts throughout the main code.

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

        mov     rbp, rdx

// Main code, just a sequence of basic field operations
// 8 * multiply + 3 * square + 7 * subtract

        amontsqr_sm2(zp2,z_1)

        montmul_sm2(y2a,z_1,y_2)
        montmul_sm2(x2a,zp2,x_2)
        montmul_sm2(y2a,zp2,y2a)

        sub_sm2(xd,x2a,x_1)

        sub_sm2(yd,y2a,y_1)

        amontsqr_sm2(zz,xd)
        montsqr_sm2(ww,yd)

        montmul_sm2(zzx1,zz,x_1)
        montmul_sm2(zzx2,zz,x2a)

        sub_sm2(resx,ww,zzx1)
        sub_sm2(t1,zzx2,zzx1)

        montmul_sm2(resz,xd,z_1)

        sub_sm2(resx,resx,zzx2)

        sub_sm2(t2,zzx1,resx)

        montmul_sm2(t1,t1,y_1)
        montmul_sm2(t2,yd,t2)

        sub_sm2(resy,t2,t1)

// Test if z_1 = 0 to decide if p1 = 0 (up to projective equivalence)

        testzero4(z_1)

// Multiplex: if p1 <> 0 just copy the computed result from the staging area.
// If p1 = 0 then return the point p2 augmented with a z = 1 coordinate (in
// Montgomery form so not the simple constant 1 but rather 2^256 - p_sm2),
// hence giving 0 + p2 = p2 for the final result.

        mux4(r8,r9,r10,r11,resx,x_2)
        mux4(r12,r13,r14,r15,resy,y_2)

        store4(x_3,r8,r9,r10,r11)
        store4(y_3,r12,r13,r14,r15)

        load4(r8,r9,r10,r11,resz)
        mov     eax, 1
        cmovz   r8, rax
        mov     eax, 0x00000000ffffffff
        cmovz   r9, rax
        mov     eax, 0
        cmovz   r10, rax
        mov     rax, 0x0000000100000000
        cmovz   r11, rax

        store4(z_3,r8,r9,r10,r11)

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

S2N_BN_SIZE_DIRECTIVE(sm2_montjmixadd)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
