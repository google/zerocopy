// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point mixed addition on NIST curve P-521 in Jacobian coordinates
//
//    extern void p521_jmixadd(uint64_t p3[static 27], const uint64_t p1[static 27],
//                             const uint64_t p2[static 18]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples.
// A Jacobian triple (x,y,z) represents affine point (x/z^2,y/z^3).
// The "mixed" part means that p2 only has x and y coordinates, with the
// implicit z coordinate assumed to be the identity. It is assumed that
// all the coordinates of the input points p1 and p2 are fully reduced
// mod p_521, that the z coordinate of p1 is nonzero and that neither
// p1 =~= p2 or p1 =~= -p2, where "=~=" means "represents the same affine
// point as".
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p521_jmixadd)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p521_jmixadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p521_jmixadd)
        .text

// Size of individual field elements

#define NUMSIZE 72

// Stable homes for input arguments during main code sequence
// These are where they arrive except for input_y, initially in rdx

#define input_z rdi
#define input_x rsi
#define input_y rcx

// Pointer-offset pairs for inputs and outputs

#define x_1 input_x+0
#define y_1 input_x+NUMSIZE
#define z_1 input_x+(2*NUMSIZE)

#define x_2 input_y+0
#define y_2 input_y+NUMSIZE

#define x_3 input_z+0
#define y_3 input_z+NUMSIZE
#define z_3 input_z+(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// The tmp field is internal storage for field mul and sqr.
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

#define tmp rsp+(NUMSIZE*6)

#define NSPACE 496

// Corresponds exactly to bignum_mul_p521

#define mul_p521(P0,P1,P2)                      \
        xor     ebp,ebp;                        \
        mov     rdx,[P2];                       \
        mulx    r9,r8,[P1];                     \
        mov     [rsp+432],r8;                   \
        mulx    r10,rbx,[P1+0x8];               \
        adc     r9,rbx;                         \
        mulx    r11,rbx,[P1+0x10];              \
        adc     r10,rbx;                        \
        mulx    r12,rbx,[P1+0x18];              \
        adc     r11,rbx;                        \
        mulx    r13,rbx,[P1+0x20];              \
        adc     r12,rbx;                        \
        mulx    r14,rbx,[P1+0x28];              \
        adc     r13,rbx;                        \
        mulx    r15,rbx,[P1+0x30];              \
        adc     r14,rbx;                        \
        mulx    r8,rbx,[P1+0x38];               \
        adc     r15,rbx;                        \
        adc     r8,rbp;                         \
        mov     rdx,[P2+0x8];                   \
        xor     ebp,ebp;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mov     [rsp+440],r9;                   \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r15,rax;                        \
        adox    r8,rbx;                         \
        mulx    r9,rax,[P1+0x38];               \
        adcx    r8,rax;                         \
        adox    r9,rbp;                         \
        adc     r9,rbp;                         \
        mov     rdx,[P2+0x10];                  \
        xor     ebp,ebp;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mov     [rsp+448],r10;                  \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r15,rax;                        \
        adox    r8,rbx;                         \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    r10,rax,[P1+0x38];              \
        adcx    r9,rax;                         \
        adox    r10,rbp;                        \
        adc     r10,rbp;                        \
        mov     rdx,[P2+0x18];                  \
        xor     ebp,ebp;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mov     [rsp+456],r11;                  \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r15,rax;                        \
        adox    r8,rbx;                         \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    r11,rax,[P1+0x38];              \
        adcx    r10,rax;                        \
        adox    r11,rbp;                        \
        adc     r11,rbp;                        \
        mov     rdx,[P2+0x20];                  \
        xor     ebp,ebp;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mov     [rsp+464],r12;                  \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r15,rax;                        \
        adox    r8,rbx;                         \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    r12,rax,[P1+0x38];              \
        adcx    r11,rax;                        \
        adox    r12,rbp;                        \
        adc     r12,rbp;                        \
        mov     rdx,[P2+0x28];                  \
        xor     ebp,ebp;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mov     [rsp+472],r13;                  \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r15,rax;                        \
        adox    r8,rbx;                         \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    r13,rax,[P1+0x38];              \
        adcx    r12,rax;                        \
        adox    r13,rbp;                        \
        adc     r13,rbp;                        \
        mov     rdx,[P2+0x30];                  \
        xor     ebp,ebp;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mov     [rsp+480],r14;                  \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r15,rax;                        \
        adox    r8,rbx;                         \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mulx    r14,rax,[P1+0x38];              \
        adcx    r13,rax;                        \
        adox    r14,rbp;                        \
        adc     r14,rbp;                        \
        mov     rdx,[P2+0x38];                  \
        xor     ebp,ebp;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r15,rax;                        \
        adox    r8,rbx;                         \
        mov     [rsp+488],r15;                  \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    r15,rax,[P1+0x38];              \
        adcx    r14,rax;                        \
        adox    r15,rbp;                        \
        adc     r15,rbp;                        \
        mov     rdx,[P1+0x40];                  \
        xor     ebp,ebp;                        \
        mulx    rbx,rax,[P2];                   \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    rbx,rax,[P2+0x8];               \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,[P2+0x10];              \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    rbx,rax,[P2+0x18];              \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,[P2+0x20];              \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mulx    rbx,rax,[P2+0x28];              \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    rbx,rax,[P2+0x30];              \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mulx    rbx,rax,[P2+0x38];              \
        adcx    r15,rax;                        \
        adox    rbx,rbp;                        \
        adc     rbp,rbx;                        \
        mov     rdx,[P2+0x40];                  \
        xor     eax,eax;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mulx    rbx,rax,[P1+0x38];              \
        adcx    r15,rax;                        \
        adox    rbp,rbx;                        \
        mulx    rbx,rax,[P1+0x40];              \
        adc     rbp,rax;                        \
        mov     rax,r8;                         \
        and     rax,0x1ff;                      \
        shrd    r8,r9,0x9;                      \
        shrd    r9,r10,0x9;                     \
        shrd    r10,r11,0x9;                    \
        shrd    r11,r12,0x9;                    \
        shrd    r12,r13,0x9;                    \
        shrd    r13,r14,0x9;                    \
        shrd    r14,r15,0x9;                    \
        shrd    r15,rbp,0x9;                    \
        shr     rbp,0x9;                        \
        add     rbp,rax;                        \
        stc;                                    \
        adc     r8,[rsp+432];                   \
        adc     r9,[rsp+440];                   \
        adc     r10,[rsp+448];                  \
        adc     r11,[rsp+456];                  \
        adc     r12,[rsp+464];                  \
        adc     r13,[rsp+472];                  \
        adc     r14,[rsp+480];                  \
        adc     r15,[rsp+488];                  \
        adc     rbp,0xfffffffffffffe00;         \
        cmc;                                    \
        sbb     r8,0x0;                         \
        mov     [P0],r8;                        \
        sbb     r9,0x0;                         \
        mov     [P0+0x8],r9;                    \
        sbb     r10,0x0;                        \
        mov     [P0+0x10],r10;                  \
        sbb     r11,0x0;                        \
        mov     [P0+0x18],r11;                  \
        sbb     r12,0x0;                        \
        mov     [P0+0x20],r12;                  \
        sbb     r13,0x0;                        \
        mov     [P0+0x28],r13;                  \
        sbb     r14,0x0;                        \
        mov     [P0+0x30],r14;                  \
        sbb     r15,0x0;                        \
        mov     [P0+0x38],r15;                  \
        sbb     rbp,0x0;                        \
        and     rbp,0x1ff;                      \
        mov     [P0+0x40],rbp

// Corresponds exactly to bignum_sqr_p521

#define sqr_p521(P0,P1)                         \
        xor     ebp,ebp;                        \
        mov     rdx,[P1];                       \
        mulx    rax,r9,[P1+0x8];                \
        mov     [rsp+440],r9;                   \
        mulx    rbx,r10,[P1+0x10];              \
        adcx    r10,rax;                        \
        mov     [rsp+448],r10;                  \
        mulx    rax,r11,[P1+0x18];              \
        adcx    r11,rbx;                        \
        mulx    rbx,r12,[P1+0x20];              \
        adcx    r12,rax;                        \
        mulx    rax,r13,[P1+0x28];              \
        adcx    r13,rbx;                        \
        mulx    rbx,r14,[P1+0x30];              \
        adcx    r14,rax;                        \
        mulx    r8,r15,[P1+0x38];               \
        adcx    r15,rbx;                        \
        adcx    r8,rbp;                         \
        xor     ebp,ebp;                        \
        mov     rdx,[P1+0x8];                   \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mov     [rsp+456],r11;                  \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mov     [rsp+464],r12;                  \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r15,rax;                        \
        adox    r8,rbx;                         \
        mulx    r9,rax,[P1+0x38];               \
        adcx    r8,rax;                         \
        adox    r9,rbp;                         \
        mov     rdx,[P1+0x20];                  \
        mulx    r10,rax,[P1+0x28];              \
        adcx    r9,rax;                         \
        adox    r10,rbp;                        \
        adcx    r10,rbp;                        \
        xor     ebp,ebp;                        \
        mov     rdx,[P1+0x10];                  \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mov     [rsp+472],r13;                  \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mov     [rsp+480],r14;                  \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r15,rax;                        \
        adox    r8,rbx;                         \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    rbx,rax,[P1+0x38];              \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mov     rdx,[P1+0x30];                  \
        mulx    r11,rax,[P1+0x20];              \
        adcx    r10,rax;                        \
        adox    r11,rbp;                        \
        mulx    r12,rax,[P1+0x28];              \
        adcx    r11,rax;                        \
        adox    r12,rbp;                        \
        adcx    r12,rbp;                        \
        xor     ebp,ebp;                        \
        mov     rdx,[P1+0x18];                  \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r15,rax;                        \
        adox    r8,rbx;                         \
        mov     [rsp+488],r15;                  \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,[P1+0x38];              \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mov     rdx,[P1+0x38];                  \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    r13,rax,[P1+0x28];              \
        adcx    r12,rax;                        \
        adox    r13,rbp;                        \
        mulx    r14,rax,[P1+0x30];              \
        adcx    r13,rax;                        \
        adox    r14,rbp;                        \
        adcx    r14,rbp;                        \
        xor     ebp,ebp;                        \
        mov     rdx,[P1];                       \
        mulx    rbx,rax,rdx;                    \
        mov     [rsp+432],rax;                  \
        mov     rax,[rsp+440];                  \
        adcx    rax,rax;                        \
        adox    rax,rbx;                        \
        mov     [rsp+440],rax;                  \
        mov     rax,[rsp+448];                  \
        mov     rdx,[P1+0x8];                   \
        mulx    rbx,rdx,rdx;                    \
        adcx    rax,rax;                        \
        adox    rax,rdx;                        \
        mov     [rsp+448],rax;                  \
        mov     rax,[rsp+456];                  \
        adcx    rax,rax;                        \
        adox    rax,rbx;                        \
        mov     [rsp+456],rax;                  \
        mov     rax,[rsp+464];                  \
        mov     rdx,[P1+0x10];                  \
        mulx    rbx,rdx,rdx;                    \
        adcx    rax,rax;                        \
        adox    rax,rdx;                        \
        mov     [rsp+464],rax;                  \
        mov     rax,[rsp+472];                  \
        adcx    rax,rax;                        \
        adox    rax,rbx;                        \
        mov     [rsp+472],rax;                  \
        mov     rax,[rsp+480];                  \
        mov     rdx,[P1+0x18];                  \
        mulx    rbx,rdx,rdx;                    \
        adcx    rax,rax;                        \
        adox    rax,rdx;                        \
        mov     [rsp+480],rax;                  \
        mov     rax,[rsp+488];                  \
        adcx    rax,rax;                        \
        adox    rax,rbx;                        \
        mov     [rsp+488],rax;                  \
        mov     rdx,[P1+0x20];                  \
        mulx    rbx,rdx,rdx;                    \
        adcx    r8,r8;                          \
        adox    r8,rdx;                         \
        adcx    r9,r9;                          \
        adox    r9,rbx;                         \
        mov     rdx,[P1+0x28];                  \
        mulx    rbx,rdx,rdx;                    \
        adcx    r10,r10;                        \
        adox    r10,rdx;                        \
        adcx    r11,r11;                        \
        adox    r11,rbx;                        \
        mov     rdx,[P1+0x30];                  \
        mulx    rbx,rdx,rdx;                    \
        adcx    r12,r12;                        \
        adox    r12,rdx;                        \
        adcx    r13,r13;                        \
        adox    r13,rbx;                        \
        mov     rdx,[P1+0x38];                  \
        mulx    r15,rdx,rdx;                    \
        adcx    r14,r14;                        \
        adox    r14,rdx;                        \
        adcx    r15,rbp;                        \
        adox    r15,rbp;                        \
        mov     rdx,[P1+0x40];                  \
        mov     rbp,rdx;                        \
        imul    rbp,rbp;                        \
        add     rdx,rdx;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r8,rax;                         \
        adox    r9,rbx;                         \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,[P1+0x20];              \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mulx    rbx,rax,[P1+0x28];              \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    rbx,rax,[P1+0x30];              \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        mulx    rbx,rax,[P1+0x38];              \
        adcx    r15,rax;                        \
        adox    rbp,rbx;                        \
        adc     rbp,0x0;                        \
        mov     rax,r8;                         \
        and     rax,0x1ff;                      \
        shrd    r8,r9,0x9;                      \
        shrd    r9,r10,0x9;                     \
        shrd    r10,r11,0x9;                    \
        shrd    r11,r12,0x9;                    \
        shrd    r12,r13,0x9;                    \
        shrd    r13,r14,0x9;                    \
        shrd    r14,r15,0x9;                    \
        shrd    r15,rbp,0x9;                    \
        shr     rbp,0x9;                        \
        add     rbp,rax;                        \
        stc;                                    \
        adc     r8,[rsp+432];                   \
        adc     r9,[rsp+440];                   \
        adc     r10,[rsp+448];                  \
        adc     r11,[rsp+456];                  \
        adc     r12,[rsp+464];                  \
        adc     r13,[rsp+472];                  \
        adc     r14,[rsp+480];                  \
        adc     r15,[rsp+488];                  \
        adc     rbp,0xfffffffffffffe00;         \
        cmc;                                    \
        sbb     r8,0x0;                         \
        mov     [P0],r8;                        \
        sbb     r9,0x0;                         \
        mov     [P0+0x8],r9;                    \
        sbb     r10,0x0;                        \
        mov     [P0+0x10],r10;                  \
        sbb     r11,0x0;                        \
        mov     [P0+0x18],r11;                  \
        sbb     r12,0x0;                        \
        mov     [P0+0x20],r12;                  \
        sbb     r13,0x0;                        \
        mov     [P0+0x28],r13;                  \
        sbb     r14,0x0;                        \
        mov     [P0+0x30],r14;                  \
        sbb     r15,0x0;                        \
        mov     [P0+0x38],r15;                  \
        sbb     rbp,0x0;                        \
        and     rbp,0x1ff;                      \
        mov     [P0+0x40],rbp

// Corresponds exactly to bignum_sub_p521

#define sub_p521(P0,P1,P2)                      \
        mov     rax,[P1];                       \
        sub     rax,[P2];                       \
        mov     rdx,[P1+0x8];                   \
        sbb     rdx,[P2+0x8];                   \
        mov     r8,[P1+0x10];                   \
        sbb     r8,[P2+0x10];                   \
        mov     r9,[P1+0x18];                   \
        sbb     r9,[P2+0x18];                   \
        mov     r10,[P1+0x20];                  \
        sbb     r10,[P2+0x20];                  \
        mov     r11,[P1+0x28];                  \
        sbb     r11,[P2+0x28];                  \
        mov     r12,[P1+0x30];                  \
        sbb     r12,[P2+0x30];                  \
        mov     r13,[P1+0x38];                  \
        sbb     r13,[P2+0x38];                  \
        mov     r14,[P1+0x40];                  \
        sbb     r14,[P2+0x40];                  \
        sbb     rax,0x0;                        \
        mov     [P0],rax;                       \
        sbb     rdx,0x0;                        \
        mov     [P0+0x8],rdx;                   \
        sbb     r8,0x0;                         \
        mov     [P0+0x10],r8;                   \
        sbb     r9,0x0;                         \
        mov     [P0+0x18],r9;                   \
        sbb     r10,0x0;                        \
        mov     [P0+0x20],r10;                  \
        sbb     r11,0x0;                        \
        mov     [P0+0x28],r11;                  \
        sbb     r12,0x0;                        \
        mov     [P0+0x30],r12;                  \
        sbb     r13,0x0;                        \
        mov     [P0+0x38],r13;                  \
        sbb     r14,0x0;                        \
        and     r14,0x1ff;                      \
        mov     [P0+0x40],r14

// Additional macros to help with final multiplexing

#define testzero9(P)                            \
        mov     rax, [P];                       \
        mov     rbx, [P+8];                     \
        mov     rdx, [P+16];                    \
        mov     rbp, [P+24];                    \
        or      rax, [P+32];                    \
        or      rbx, [P+40];                    \
        or      rdx, [P+48];                    \
        or      rbp, [P+56];                    \
        or      rax, rbx;                       \
        or      rdx, rbp;                       \
        or      rax, [P+64];                    \
        or      rax, rdx

#define mux9(P0,PNE,PEQ)                        \
        mov     rax, [PNE];                     \
        mov     rbx, [PEQ];                     \
        cmovz   rax, rbx;                       \
        mov     [P0], rax;                      \
        mov     rax, [PNE+8];                   \
        mov     rbx, [PEQ+8];                   \
        cmovz   rax, rbx;                       \
        mov     [P0+8], rax;                    \
        mov     rax, [PNE+16];                  \
        mov     rbx, [PEQ+16];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+16], rax;                   \
        mov     rax, [PNE+24];                  \
        mov     rbx, [PEQ+24];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+24], rax;                   \
        mov     rax, [PNE+32];                  \
        mov     rbx, [PEQ+32];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+32], rax;                   \
        mov     rax, [PNE+40];                  \
        mov     rbx, [PEQ+40];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+40], rax;                   \
        mov     rax, [PNE+48];                  \
        mov     rbx, [PEQ+48];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+48], rax;                   \
        mov     rax, [PNE+56];                  \
        mov     rbx, [PEQ+56];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+56], rax;                   \
        mov     rax, [PNE+64];                  \
        mov     rbx, [PEQ+64];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+64], rax

#define mux9c(P0,PNE)                           \
        mov     rax, [PNE];                     \
        mov     ebx, 1;                         \
        cmovz   rax, rbx;                       \
        mov     [P0], rax;                      \
        mov     rax, [PNE+8];                   \
        mov     ebx, 0;                         \
        cmovz   rax, rbx;                       \
        mov     [P0+8], rax;                    \
        mov     rax, [PNE+16];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+16], rax;                   \
        mov     rax, [PNE+24];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+24], rax;                   \
        mov     rax, [PNE+32];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+32], rax;                   \
        mov     rax, [PNE+40];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+40], rax;                   \
        mov     rax, [PNE+48];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+48], rax;                   \
        mov     rax, [PNE+56];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+56], rax;                   \
        mov     rax, [PNE+64];                  \
        cmovz   rax, rbx;                       \
        mov     [P0+64], rax

#define copy9(P0,P1)                            \
        mov     rax,[P1];                       \
        mov     [P0],rax;                       \
        mov     rax,[P1+8];                     \
        mov     [P0+8],rax;                     \
        mov     rax,[P1+16];                    \
        mov     [P0+16],rax;                    \
        mov     rax,[P1+24];                    \
        mov     [P0+24],rax;                    \
        mov     rax,[P1+32];                    \
        mov     [P0+32],rax;                    \
        mov     rax,[P1+40];                    \
        mov     [P0+40],rax;                    \
        mov     rax,[P1+48];                    \
        mov     [P0+48],rax;                    \
        mov     rax,[P1+56];                    \
        mov     [P0+56],rax;                    \
        mov     rax,[P1+64];                    \
        mov     [P0+64],rax

S2N_BN_SYMBOL(p521_jmixadd):
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

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

// Move the input arguments to stable places (two are already there)

        mov     input_y, rdx

// Main code, just a sequence of basic field operations

        sqr_p521(zp2,z_1)
        mul_p521(y2a,z_1,y_2)

        mul_p521(x2a,zp2,x_2)
        mul_p521(y2a,zp2,y2a)

        sub_p521(xd,x2a,x_1)
        sub_p521(yd,y2a,y_1)

        sqr_p521(zz,xd)
        sqr_p521(ww,yd)

        mul_p521(zzx1,zz,x_1)
        mul_p521(zzx2,zz,x2a)

        sub_p521(resx,ww,zzx1)
        sub_p521(t1,zzx2,zzx1)

        mul_p521(resz,xd,z_1)

        sub_p521(resx,resx,zzx2)

        sub_p521(t2,zzx1,resx)

        mul_p521(t1,t1,y_1)
        mul_p521(t2,yd,t2)

        sub_p521(resy,t2,t1)

// Test if z_1 = 0 to decide if p1 = 0 (up to projective equivalence)

        testzero9(z_1)

// Multiplex: if p1 <> 0 just copy the computed result from the staging area.
// If p1 = 0 then return the point p2 augmented with an extra z = 1
// coordinate, hence giving 0 + p2 = p2 for the final result.

        mux9    (resx,resx,x_2)
        mux9    (resy,resy,y_2)

        copy9(x_3,resx)
        copy9(y_3,resy)

        mux9c(z_3,resz)

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

S2N_BN_SIZE_DIRECTIVE(p521_jmixadd)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
