// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point addition on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates
//
//    extern void sm2_montjadd(uint64_t p3[static 12], const uint64_t p1[static 12],
//                             const uint64_t p2[static 12]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sm2_montjadd)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sm2_montjadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sm2_montjadd)
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
#define z_2 rbp+(2*NUMSIZE)

#define x_3 rdi+0
#define y_3 rdi+NUMSIZE
#define z_3 rdi+(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define z1sq rsp+(NUMSIZE*0)
#define ww rsp+(NUMSIZE*0)
#define resx rsp+(NUMSIZE*0)

#define yd rsp+(NUMSIZE*1)
#define y2a rsp+(NUMSIZE*1)

#define x2a rsp+(NUMSIZE*2)
#define zzx2 rsp+(NUMSIZE*2)

#define zz rsp+(NUMSIZE*3)
#define t1 rsp+(NUMSIZE*3)

#define t2 rsp+(NUMSIZE*4)
#define x1a rsp+(NUMSIZE*4)
#define zzx1 rsp+(NUMSIZE*4)
#define resy rsp+(NUMSIZE*4)

#define xd rsp+(NUMSIZE*5)
#define z2sq rsp+(NUMSIZE*5)
#define resz rsp+(NUMSIZE*5)

#define y1a rsp+(NUMSIZE*6)

#define NSPACE NUMSIZE*7

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

#define czload4(r0,r1,r2,r3,P)                  \
        cmovz   r0, [P];                        \
        cmovz   r1, [P+8];                      \
        cmovz   r2, [P+16];                     \
        cmovz   r3, [P+24]

#define muxload4(r0,r1,r2,r3,P0,P1,P2)          \
        mov     r0, [P0];                       \
        cmovb   r0, [P1];                       \
        cmovnbe r0, [P2];                       \
        mov     r1, [P0+8];                     \
        cmovb   r1, [P1+8];                     \
        cmovnbe r1, [P2+8];                     \
        mov     r2, [P0+16];                    \
        cmovb   r2, [P1+16];                    \
        cmovnbe r2, [P2+16];                    \
        mov     r3, [P0+24];                    \
        cmovb   r3, [P1+24];                    \
        cmovnbe r3, [P2+24]

S2N_BN_SYMBOL(sm2_montjadd):
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
// 12 * multiply + 4 * square + 7 * subtract

        amontsqr_sm2(z1sq,z_1)
        amontsqr_sm2(z2sq,z_2)

        montmul_sm2(y1a,z_2,y_1)
        montmul_sm2(y2a,z_1,y_2)

        montmul_sm2(x2a,z1sq,x_2)
        montmul_sm2(x1a,z2sq,x_1)
        montmul_sm2(y2a,z1sq,y2a)
        montmul_sm2(y1a,z2sq,y1a)

        sub_sm2(xd,x2a,x1a)
        sub_sm2(yd,y2a,y1a)

        amontsqr_sm2(zz,xd)
        montsqr_sm2(ww,yd)

        montmul_sm2(zzx1,zz,x1a)
        montmul_sm2(zzx2,zz,x2a)

        sub_sm2(resx,ww,zzx1)
        sub_sm2(t1,zzx2,zzx1)

        montmul_sm2(xd,xd,z_1)

        sub_sm2(resx,resx,zzx2)

        sub_sm2(t2,zzx1,resx)

        montmul_sm2(t1,t1,y1a)

        montmul_sm2(resz,xd,z_2)
        montmul_sm2(t2,yd,t2)

        sub_sm2(resy,t2,t1)

// Load in the z coordinates of the inputs to check for P1 = 0 and P2 = 0
// The condition codes get set by a comparison (P2 != 0) - (P1 != 0)
// So "NBE" <=> ~(CF \/ ZF) <=> P1 = 0 /\ ~(P2 = 0)
// and "B"  <=> CF          <=> ~(P1 = 0) /\ P2 = 0
// and "Z"  <=> ZF          <=> (P1 = 0 <=> P2 = 0)

        load4(r8,r9,r10,r11,z_1)

        mov     rax, r8
        mov     rdx, r9
        or      rax, r10
        or      rdx, r11
        or      rax, rdx
        neg     rax
        sbb     rax, rax

        load4(r12,r13,r14,r15,z_2)

        mov     rbx, r12
        mov     rdx, r13
        or      rbx, r14
        or      rdx, r15
        or      rbx, rdx
        neg     rbx
        sbb     rbx, rbx

        cmp     rbx, rax

// Multiplex the outputs accordingly, re-using the z's in registers

        cmovb   r12, r8
        cmovb   r13, r9
        cmovb   r14, r10
        cmovb   r15, r11

        czload4(r12,r13,r14,r15,resz)

        muxload4(rax,rbx,rcx,rdx,resx,x_1,x_2)
        muxload4(r8,r9,r10,r11,resy,y_1,y_2)

// Finally store back the multiplexed values

        store4(x_3,rax,rbx,rcx,rdx)
        store4(y_3,r8,r9,r10,r11)
        store4(z_3,r12,r13,r14,r15)

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

S2N_BN_SIZE_DIRECTIVE(sm2_montjadd)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
