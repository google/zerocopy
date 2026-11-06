// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point addition on NIST curve P-384 in Montgomery-Jacobian coordinates
//
//    extern void p384_montjadd(uint64_t p3[static 18], const uint64_t p1[static 18],
//                              const uint64_t p2[static 18]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^384 * x) mod p_384.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjadd)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p384_montjadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjadd)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 48

// Pointer-offset pairs for inputs and outputs
// These assume rdi = p3, rsi = p1 and rcx = p2,
// which needs to be set up explicitly before use.
// The rdi value never changes, however.

#define x_1 rsi+0
#define y_1 rsi+NUMSIZE
#define z_1 rsi+(2*NUMSIZE)

#define x_2 rcx+0
#define y_2 rcx+NUMSIZE
#define z_2 rcx+(2*NUMSIZE)

#define x_3 rdi+0
#define y_3 rdi+NUMSIZE
#define z_3 rdi+(2*NUMSIZE)

// In one place it's convenient to use another register
// since the squaring function overwrites rcx

#define z_2_alt rsi+(2*NUMSIZE)

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

// Temporaries for the actual input pointers

#define input_x [rsp+(NUMSIZE*7)]
#define input_y [rsp+(NUMSIZE*7+8)]

#define NSPACE 352

// Corresponds exactly to bignum_montmul_p384

#define montmul_p384(P0,P1,P2)                  \
        mov    rdx,[P2];                        \
        xor    r15d,r15d;                       \
        mulx   r9,r8,[P1];                      \
        mulx   r10,rbx,[P1+0x8];                \
        add    r9,rbx;                          \
        mulx   r11,rbx,[P1+0x10];               \
        adc    r10,rbx;                         \
        mulx   r12,rbx,[P1+0x18];               \
        adc    r11,rbx;                         \
        mulx   r13,rbx,[P1+0x20];               \
        adc    r12,rbx;                         \
        mulx   r14,rbx,[P1+0x28];               \
        adc    r13,rbx;                         \
        adc    r14,r15;                         \
        mov    rdx,r8;                          \
        shl    rdx,0x20;                        \
        add    rdx,r8;                          \
        xor    ebp,ebp;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,rbx,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   rbx,r8,rbx;                      \
        adc    rax,r8;                          \
        adc    rbx,rdx;                         \
        adc    ebp,ebp;                         \
        sub    r9,rax;                          \
        sbb    r10,rbx;                         \
        sbb    r11,rbp;                         \
        sbb    r12,0x0;                         \
        sbb    r13,0x0;                         \
        sbb    rdx,0x0;                         \
        add    r14,rdx;                         \
        adc    r15,0x0;                         \
        mov    rdx,[P2+0x8];                    \
        xor    r8d,r8d;                         \
        mulx   rbx,rax,[P1];                    \
        adcx   r9,rax;                          \
        adox   r10,rbx;                         \
        mulx   rbx,rax,[P1+0x8];                \
        adcx   r10,rax;                         \
        adox   r11,rbx;                         \
        mulx   rbx,rax,[P1+0x10];               \
        adcx   r11,rax;                         \
        adox   r12,rbx;                         \
        mulx   rbx,rax,[P1+0x18];               \
        adcx   r12,rax;                         \
        adox   r13,rbx;                         \
        mulx   rbx,rax,[P1+0x20];               \
        adcx   r13,rax;                         \
        adox   r14,rbx;                         \
        adox   r15,r8;                          \
        mulx   rbx,rax,[P1+0x28];               \
        adc    r14,rax;                         \
        adc    r15,rbx;                         \
        adc    r8,r8;                           \
        mov    rdx,r9;                          \
        shl    rdx,0x20;                        \
        add    rdx,r9;                          \
        xor    ebp,ebp;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,rbx,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   rbx,r9,rbx;                      \
        adc    rax,r9;                          \
        adc    rbx,rdx;                         \
        adc    ebp,ebp;                         \
        sub    r10,rax;                         \
        sbb    r11,rbx;                         \
        sbb    r12,rbp;                         \
        sbb    r13,0x0;                         \
        sbb    r14,0x0;                         \
        sbb    rdx,0x0;                         \
        add    r15,rdx;                         \
        adc    r8,0x0;                          \
        mov    rdx,[P2+0x10];                   \
        xor    r9d,r9d;                         \
        mulx   rbx,rax,[P1];                    \
        adcx   r10,rax;                         \
        adox   r11,rbx;                         \
        mulx   rbx,rax,[P1+0x8];                \
        adcx   r11,rax;                         \
        adox   r12,rbx;                         \
        mulx   rbx,rax,[P1+0x10];               \
        adcx   r12,rax;                         \
        adox   r13,rbx;                         \
        mulx   rbx,rax,[P1+0x18];               \
        adcx   r13,rax;                         \
        adox   r14,rbx;                         \
        mulx   rbx,rax,[P1+0x20];               \
        adcx   r14,rax;                         \
        adox   r15,rbx;                         \
        adox   r8,r9;                           \
        mulx   rbx,rax,[P1+0x28];               \
        adc    r15,rax;                         \
        adc    r8,rbx;                          \
        adc    r9,r9;                           \
        mov    rdx,r10;                         \
        shl    rdx,0x20;                        \
        add    rdx,r10;                         \
        xor    ebp,ebp;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,rbx,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   rbx,r10,rbx;                     \
        adc    rax,r10;                         \
        adc    rbx,rdx;                         \
        adc    ebp,ebp;                         \
        sub    r11,rax;                         \
        sbb    r12,rbx;                         \
        sbb    r13,rbp;                         \
        sbb    r14,0x0;                         \
        sbb    r15,0x0;                         \
        sbb    rdx,0x0;                         \
        add    r8,rdx;                          \
        adc    r9,0x0;                          \
        mov    rdx,[P2+0x18];                   \
        xor    r10d,r10d;                       \
        mulx   rbx,rax,[P1];                    \
        adcx   r11,rax;                         \
        adox   r12,rbx;                         \
        mulx   rbx,rax,[P1+0x8];                \
        adcx   r12,rax;                         \
        adox   r13,rbx;                         \
        mulx   rbx,rax,[P1+0x10];               \
        adcx   r13,rax;                         \
        adox   r14,rbx;                         \
        mulx   rbx,rax,[P1+0x18];               \
        adcx   r14,rax;                         \
        adox   r15,rbx;                         \
        mulx   rbx,rax,[P1+0x20];               \
        adcx   r15,rax;                         \
        adox   r8,rbx;                          \
        adox   r9,r10;                          \
        mulx   rbx,rax,[P1+0x28];               \
        adc    r8,rax;                          \
        adc    r9,rbx;                          \
        adc    r10,r10;                         \
        mov    rdx,r11;                         \
        shl    rdx,0x20;                        \
        add    rdx,r11;                         \
        xor    ebp,ebp;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,rbx,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   rbx,r11,rbx;                     \
        adc    rax,r11;                         \
        adc    rbx,rdx;                         \
        adc    ebp,ebp;                         \
        sub    r12,rax;                         \
        sbb    r13,rbx;                         \
        sbb    r14,rbp;                         \
        sbb    r15,0x0;                         \
        sbb    r8,0x0;                          \
        sbb    rdx,0x0;                         \
        add    r9,rdx;                          \
        adc    r10,0x0;                         \
        mov    rdx,[P2+0x20];                   \
        xor    r11d,r11d;                       \
        mulx   rbx,rax,[P1];                    \
        adcx   r12,rax;                         \
        adox   r13,rbx;                         \
        mulx   rbx,rax,[P1+0x8];                \
        adcx   r13,rax;                         \
        adox   r14,rbx;                         \
        mulx   rbx,rax,[P1+0x10];               \
        adcx   r14,rax;                         \
        adox   r15,rbx;                         \
        mulx   rbx,rax,[P1+0x18];               \
        adcx   r15,rax;                         \
        adox   r8,rbx;                          \
        mulx   rbx,rax,[P1+0x20];               \
        adcx   r8,rax;                          \
        adox   r9,rbx;                          \
        adox   r10,r11;                         \
        mulx   rbx,rax,[P1+0x28];               \
        adc    r9,rax;                          \
        adc    r10,rbx;                         \
        adc    r11,r11;                         \
        mov    rdx,r12;                         \
        shl    rdx,0x20;                        \
        add    rdx,r12;                         \
        xor    ebp,ebp;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,rbx,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   rbx,r12,rbx;                     \
        adc    rax,r12;                         \
        adc    rbx,rdx;                         \
        adc    ebp,ebp;                         \
        sub    r13,rax;                         \
        sbb    r14,rbx;                         \
        sbb    r15,rbp;                         \
        sbb    r8,0x0;                          \
        sbb    r9,0x0;                          \
        sbb    rdx,0x0;                         \
        add    r10,rdx;                         \
        adc    r11,0x0;                         \
        mov    rdx,[P2+0x28];                   \
        xor    r12d,r12d;                       \
        mulx   rbx,rax,[P1];                    \
        adcx   r13,rax;                         \
        adox   r14,rbx;                         \
        mulx   rbx,rax,[P1+0x8];                \
        adcx   r14,rax;                         \
        adox   r15,rbx;                         \
        mulx   rbx,rax,[P1+0x10];               \
        adcx   r15,rax;                         \
        adox   r8,rbx;                          \
        mulx   rbx,rax,[P1+0x18];               \
        adcx   r8,rax;                          \
        adox   r9,rbx;                          \
        mulx   rbx,rax,[P1+0x20];               \
        adcx   r9,rax;                          \
        adox   r10,rbx;                         \
        adox   r11,r12;                         \
        mulx   rbx,rax,[P1+0x28];               \
        adc    r10,rax;                         \
        adc    r11,rbx;                         \
        adc    r12,r12;                         \
        mov    rdx,r13;                         \
        shl    rdx,0x20;                        \
        add    rdx,r13;                         \
        xor    ebp,ebp;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,rbx,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   rbx,r13,rbx;                     \
        adc    rax,r13;                         \
        adc    rbx,rdx;                         \
        adc    ebp,ebp;                         \
        sub    r14,rax;                         \
        sbb    r15,rbx;                         \
        sbb    r8,rbp;                          \
        sbb    r9,0x0;                          \
        sbb    r10,0x0;                         \
        sbb    rdx,0x0;                         \
        add    r11,rdx;                         \
        adc    r12,0x0;                         \
        xor    edx,edx;                         \
        xor    ebp,ebp;                         \
        xor    r13d,r13d;                       \
        mov    rax,0xffffffff00000001;          \
        add    rax,r14;                         \
        mov    ebx,0xffffffff;                  \
        adc    rbx,r15;                         \
        mov    ecx,0x1;                         \
        adc    rcx,r8;                          \
        adc    rdx,r9;                          \
        adc    rbp,r10;                         \
        adc    r13,r11;                         \
        adc    r12,0x0;                         \
        cmovne r14,rax;                         \
        cmovne r15,rbx;                         \
        cmovne r8,rcx;                          \
        cmovne r9,rdx;                          \
        cmovne r10,rbp;                         \
        cmovne r11,r13;                         \
        mov    [P0],r14;                        \
        mov    [P0+0x8],r15;                    \
        mov    [P0+0x10],r8;                    \
        mov    [P0+0x18],r9;                    \
        mov    [P0+0x20],r10;                   \
        mov    [P0+0x28],r11

// Corresponds exactly to bignum_montsqr_p384

#define montsqr_p384(P0,P1)                     \
        mov    rdx,[P1];                        \
        mulx   r10,r9,[P1+0x8];                 \
        mulx   r12,r11,[P1+0x18];               \
        mulx   r14,r13,[P1+0x28];               \
        mov    rdx,[P1+0x18];                   \
        mulx   rcx,r15,[P1+0x20];               \
        xor    ebp,ebp;                         \
        mov    rdx,[P1+0x10];                   \
        mulx   rbx,rax,[P1];                    \
        adcx   r10,rax;                         \
        adox   r11,rbx;                         \
        mulx   rbx,rax,[P1+0x8];                \
        adcx   r11,rax;                         \
        adox   r12,rbx;                         \
        mov    rdx,[P1+0x8];                    \
        mulx   rbx,rax,[P1+0x18];               \
        adcx   r12,rax;                         \
        adox   r13,rbx;                         \
        mulx   rbx,rax,[P1+0x20];               \
        adcx   r13,rax;                         \
        adox   r14,rbx;                         \
        mulx   rbx,rax,[P1+0x28];               \
        adcx   r14,rax;                         \
        adox   r15,rbx;                         \
        adcx   r15,rbp;                         \
        adox   rcx,rbp;                         \
        adc    rcx,rbp;                         \
        xor    ebp,ebp;                         \
        mov    rdx,[P1+0x20];                   \
        mulx   rbx,rax,[P1];                    \
        adcx   r12,rax;                         \
        adox   r13,rbx;                         \
        mov    rdx,[P1+0x10];                   \
        mulx   rbx,rax,[P1+0x18];               \
        adcx   r13,rax;                         \
        adox   r14,rbx;                         \
        mulx   rbx,rax,[P1+0x20];               \
        adcx   r14,rax;                         \
        adox   r15,rbx;                         \
        mulx   rdx,rax,[P1+0x28];               \
        adcx   r15,rax;                         \
        adox   rcx,rdx;                         \
        mov    rdx,[P1+0x28];                   \
        mulx   rbp,rbx,[P1+0x20];               \
        mulx   rdx,rax,[P1+0x18];               \
        adcx   rcx,rax;                         \
        adox   rbx,rdx;                         \
        mov    eax,0x0;                         \
        adcx   rbx,rax;                         \
        adox   rbp,rax;                         \
        adc    rbp,rax;                         \
        xor    rax,rax;                         \
        mov    rdx,[P1];                        \
        mulx   rax,r8,[P1];                     \
        adcx   r9,r9;                           \
        adox   r9,rax;                          \
        mov    rdx,[P1+0x8];                    \
        mulx   rdx,rax,rdx;                     \
        adcx   r10,r10;                         \
        adox   r10,rax;                         \
        adcx   r11,r11;                         \
        adox   r11,rdx;                         \
        mov    rdx,[P1+0x10];                   \
        mulx   rdx,rax,rdx;                     \
        adcx   r12,r12;                         \
        adox   r12,rax;                         \
        adcx   r13,r13;                         \
        adox   r13,rdx;                         \
        mov    rdx,[P1+0x18];                   \
        mulx   rdx,rax,rdx;                     \
        adcx   r14,r14;                         \
        adox   r14,rax;                         \
        adcx   r15,r15;                         \
        adox   r15,rdx;                         \
        mov    rdx,[P1+0x20];                   \
        mulx   rdx,rax,rdx;                     \
        adcx   rcx,rcx;                         \
        adox   rcx,rax;                         \
        adcx   rbx,rbx;                         \
        adox   rbx,rdx;                         \
        mov    rdx,[P1+0x28];                   \
        mulx   rsi,rax,rdx;                     \
        adcx   rbp,rbp;                         \
        adox   rbp,rax;                         \
        mov    eax,0x0;                         \
        adcx   rsi,rax;                         \
        adox   rsi,rax;                         \
        mov    [P0],rbx;                        \
        mov    rdx,r8;                          \
        shl    rdx,0x20;                        \
        add    rdx,r8;                          \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r8,rax;                      \
        mov    ebx,0xffffffff;                  \
        mulx   r8,rbx,rbx;                      \
        add    rax,rbx;                         \
        adc    r8,rdx;                          \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r9,rax;                          \
        sbb    r10,r8;                          \
        sbb    r11,rbx;                         \
        sbb    r12,0x0;                         \
        sbb    r13,0x0;                         \
        mov    r8,rdx;                          \
        sbb    r8,0x0;                          \
        mov    rdx,r9;                          \
        shl    rdx,0x20;                        \
        add    rdx,r9;                          \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r9,rax;                      \
        mov    ebx,0xffffffff;                  \
        mulx   r9,rbx,rbx;                      \
        add    rax,rbx;                         \
        adc    r9,rdx;                          \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r10,rax;                         \
        sbb    r11,r9;                          \
        sbb    r12,rbx;                         \
        sbb    r13,0x0;                         \
        sbb    r8,0x0;                          \
        mov    r9,rdx;                          \
        sbb    r9,0x0;                          \
        mov    rdx,r10;                         \
        shl    rdx,0x20;                        \
        add    rdx,r10;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r10,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   r10,rbx,rbx;                     \
        add    rax,rbx;                         \
        adc    r10,rdx;                         \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r11,rax;                         \
        sbb    r12,r10;                         \
        sbb    r13,rbx;                         \
        sbb    r8,0x0;                          \
        sbb    r9,0x0;                          \
        mov    r10,rdx;                         \
        sbb    r10,0x0;                         \
        mov    rdx,r11;                         \
        shl    rdx,0x20;                        \
        add    rdx,r11;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r11,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   r11,rbx,rbx;                     \
        add    rax,rbx;                         \
        adc    r11,rdx;                         \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r12,rax;                         \
        sbb    r13,r11;                         \
        sbb    r8,rbx;                          \
        sbb    r9,0x0;                          \
        sbb    r10,0x0;                         \
        mov    r11,rdx;                         \
        sbb    r11,0x0;                         \
        mov    rdx,r12;                         \
        shl    rdx,0x20;                        \
        add    rdx,r12;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r12,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   r12,rbx,rbx;                     \
        add    rax,rbx;                         \
        adc    r12,rdx;                         \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r13,rax;                         \
        sbb    r8,r12;                          \
        sbb    r9,rbx;                          \
        sbb    r10,0x0;                         \
        sbb    r11,0x0;                         \
        mov    r12,rdx;                         \
        sbb    r12,0x0;                         \
        mov    rdx,r13;                         \
        shl    rdx,0x20;                        \
        add    rdx,r13;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r13,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   r13,rbx,rbx;                     \
        add    rax,rbx;                         \
        adc    r13,rdx;                         \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r8,rax;                          \
        sbb    r9,r13;                          \
        sbb    r10,rbx;                         \
        sbb    r11,0x0;                         \
        sbb    r12,0x0;                         \
        mov    r13,rdx;                         \
        sbb    r13,0x0;                         \
        mov    rbx,[P0];                        \
        add    r14,r8;                          \
        adc    r15,r9;                          \
        adc    rcx,r10;                         \
        adc    rbx,r11;                         \
        adc    rbp,r12;                         \
        adc    rsi,r13;                         \
        mov    r8d,0x0;                         \
        adc    r8,r8;                           \
        xor    r11,r11;                         \
        xor    r12,r12;                         \
        xor    r13,r13;                         \
        mov    rax,0xffffffff00000001;          \
        add    rax,r14;                         \
        mov    r9d,0xffffffff;                  \
        adc    r9,r15;                          \
        mov    r10d,0x1;                        \
        adc    r10,rcx;                         \
        adc    r11,rbx;                         \
        adc    r12,rbp;                         \
        adc    r13,rsi;                         \
        adc    r8,0x0;                          \
        cmovne r14,rax;                         \
        cmovne r15,r9;                          \
        cmovne rcx,r10;                         \
        cmovne rbx,r11;                         \
        cmovne rbp,r12;                         \
        cmovne rsi,r13;                         \
        mov    [P0],r14;                        \
        mov    [P0+0x8],r15;                    \
        mov    [P0+0x10],rcx;                   \
        mov    [P0+0x18],rbx;                   \
        mov    [P0+0x20],rbp;                   \
        mov    [P0+0x28],rsi

// Almost-Montgomery variant which we use when an input to other muls
// with the other argument fully reduced (which is always safe).

#define amontsqr_p384(P0,P1)                    \
        mov    rdx,[P1];                        \
        mulx   r10,r9,[P1+0x8];                 \
        mulx   r12,r11,[P1+0x18];               \
        mulx   r14,r13,[P1+0x28];               \
        mov    rdx,[P1+0x18];                   \
        mulx   rcx,r15,[P1+0x20];               \
        xor    ebp,ebp;                         \
        mov    rdx,[P1+0x10];                   \
        mulx   rbx,rax,[P1];                    \
        adcx   r10,rax;                         \
        adox   r11,rbx;                         \
        mulx   rbx,rax,[P1+0x8];                \
        adcx   r11,rax;                         \
        adox   r12,rbx;                         \
        mov    rdx,[P1+0x8];                    \
        mulx   rbx,rax,[P1+0x18];               \
        adcx   r12,rax;                         \
        adox   r13,rbx;                         \
        mulx   rbx,rax,[P1+0x20];               \
        adcx   r13,rax;                         \
        adox   r14,rbx;                         \
        mulx   rbx,rax,[P1+0x28];               \
        adcx   r14,rax;                         \
        adox   r15,rbx;                         \
        adcx   r15,rbp;                         \
        adox   rcx,rbp;                         \
        adc    rcx,rbp;                         \
        xor    ebp,ebp;                         \
        mov    rdx,[P1+0x20];                   \
        mulx   rbx,rax,[P1];                    \
        adcx   r12,rax;                         \
        adox   r13,rbx;                         \
        mov    rdx,[P1+0x10];                   \
        mulx   rbx,rax,[P1+0x18];               \
        adcx   r13,rax;                         \
        adox   r14,rbx;                         \
        mulx   rbx,rax,[P1+0x20];               \
        adcx   r14,rax;                         \
        adox   r15,rbx;                         \
        mulx   rdx,rax,[P1+0x28];               \
        adcx   r15,rax;                         \
        adox   rcx,rdx;                         \
        mov    rdx,[P1+0x28];                   \
        mulx   rbp,rbx,[P1+0x20];               \
        mulx   rdx,rax,[P1+0x18];               \
        adcx   rcx,rax;                         \
        adox   rbx,rdx;                         \
        mov    eax,0x0;                         \
        adcx   rbx,rax;                         \
        adox   rbp,rax;                         \
        adc    rbp,rax;                         \
        xor    rax,rax;                         \
        mov    rdx,[P1];                        \
        mulx   rax,r8,[P1];                     \
        adcx   r9,r9;                           \
        adox   r9,rax;                          \
        mov    rdx,[P1+0x8];                    \
        mulx   rdx,rax,rdx;                     \
        adcx   r10,r10;                         \
        adox   r10,rax;                         \
        adcx   r11,r11;                         \
        adox   r11,rdx;                         \
        mov    rdx,[P1+0x10];                   \
        mulx   rdx,rax,rdx;                     \
        adcx   r12,r12;                         \
        adox   r12,rax;                         \
        adcx   r13,r13;                         \
        adox   r13,rdx;                         \
        mov    rdx,[P1+0x18];                   \
        mulx   rdx,rax,rdx;                     \
        adcx   r14,r14;                         \
        adox   r14,rax;                         \
        adcx   r15,r15;                         \
        adox   r15,rdx;                         \
        mov    rdx,[P1+0x20];                   \
        mulx   rdx,rax,rdx;                     \
        adcx   rcx,rcx;                         \
        adox   rcx,rax;                         \
        adcx   rbx,rbx;                         \
        adox   rbx,rdx;                         \
        mov    rdx,[P1+0x28];                   \
        mulx   rsi,rax,rdx;                     \
        adcx   rbp,rbp;                         \
        adox   rbp,rax;                         \
        mov    eax,0x0;                         \
        adcx   rsi,rax;                         \
        adox   rsi,rax;                         \
        mov    [P0],rbx;                        \
        mov    rdx,r8;                          \
        shl    rdx,0x20;                        \
        add    rdx,r8;                          \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r8,rax;                      \
        mov    ebx,0xffffffff;                  \
        mulx   r8,rbx,rbx;                      \
        add    rax,rbx;                         \
        adc    r8,rdx;                          \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r9,rax;                          \
        sbb    r10,r8;                          \
        sbb    r11,rbx;                         \
        sbb    r12,0x0;                         \
        sbb    r13,0x0;                         \
        mov    r8,rdx;                          \
        sbb    r8,0x0;                          \
        mov    rdx,r9;                          \
        shl    rdx,0x20;                        \
        add    rdx,r9;                          \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r9,rax;                      \
        mov    ebx,0xffffffff;                  \
        mulx   r9,rbx,rbx;                      \
        add    rax,rbx;                         \
        adc    r9,rdx;                          \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r10,rax;                         \
        sbb    r11,r9;                          \
        sbb    r12,rbx;                         \
        sbb    r13,0x0;                         \
        sbb    r8,0x0;                          \
        mov    r9,rdx;                          \
        sbb    r9,0x0;                          \
        mov    rdx,r10;                         \
        shl    rdx,0x20;                        \
        add    rdx,r10;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r10,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   r10,rbx,rbx;                     \
        add    rax,rbx;                         \
        adc    r10,rdx;                         \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r11,rax;                         \
        sbb    r12,r10;                         \
        sbb    r13,rbx;                         \
        sbb    r8,0x0;                          \
        sbb    r9,0x0;                          \
        mov    r10,rdx;                         \
        sbb    r10,0x0;                         \
        mov    rdx,r11;                         \
        shl    rdx,0x20;                        \
        add    rdx,r11;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r11,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   r11,rbx,rbx;                     \
        add    rax,rbx;                         \
        adc    r11,rdx;                         \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r12,rax;                         \
        sbb    r13,r11;                         \
        sbb    r8,rbx;                          \
        sbb    r9,0x0;                          \
        sbb    r10,0x0;                         \
        mov    r11,rdx;                         \
        sbb    r11,0x0;                         \
        mov    rdx,r12;                         \
        shl    rdx,0x20;                        \
        add    rdx,r12;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r12,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   r12,rbx,rbx;                     \
        add    rax,rbx;                         \
        adc    r12,rdx;                         \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r13,rax;                         \
        sbb    r8,r12;                          \
        sbb    r9,rbx;                          \
        sbb    r10,0x0;                         \
        sbb    r11,0x0;                         \
        mov    r12,rdx;                         \
        sbb    r12,0x0;                         \
        mov    rdx,r13;                         \
        shl    rdx,0x20;                        \
        add    rdx,r13;                         \
        mov    rax,0xffffffff00000001;          \
        mulx   rax,r13,rax;                     \
        mov    ebx,0xffffffff;                  \
        mulx   r13,rbx,rbx;                     \
        add    rax,rbx;                         \
        adc    r13,rdx;                         \
        mov    ebx,0x0;                         \
        adc    rbx,rbx;                         \
        sub    r8,rax;                          \
        sbb    r9,r13;                          \
        sbb    r10,rbx;                         \
        sbb    r11,0x0;                         \
        sbb    r12,0x0;                         \
        mov    r13,rdx;                         \
        sbb    r13,0x0;                         \
        mov    rbx,[P0];                        \
        add    r14,r8;                          \
        adc    r15,r9;                          \
        adc    rcx,r10;                         \
        adc    rbx,r11;                         \
        adc    rbp,r12;                         \
        adc    rsi,r13;                         \
        mov    r8d,0x0;                         \
        mov    rax,0xffffffff00000001;          \
        mov    r9d,0xffffffff;                  \
        mov    r10d,0x1;                        \
        cmovnc rax, r8;                         \
        cmovnc r9, r8;                          \
        cmovnc r10, r8;                         \
        add    r14, rax;                        \
        adc    r15, r9;                         \
        adc    rcx, r10;                        \
        adc    rbx, r8;                         \
        adc    rbp, r8;                         \
        adc    rsi, r8;                         \
        mov    [P0],r14;                        \
        mov    [P0+0x8],r15;                    \
        mov    [P0+0x10],rcx;                   \
        mov    [P0+0x18],rbx;                   \
        mov    [P0+0x20],rbp;                   \
        mov    [P0+0x28],rsi

// Corresponds exactly to bignum_sub_p384

#define sub_p384(P0,P1,P2)                      \
        mov    rax,[P1];                        \
        sub    rax,[P2];                        \
        mov    rdx,[P1+0x8];                    \
        sbb    rdx,[P2+0x8];                    \
        mov    r8,[P1+0x10];                    \
        sbb    r8,[P2+0x10];                    \
        mov    r9,[P1+0x18];                    \
        sbb    r9,[P2+0x18];                    \
        mov    r10,[P1+0x20];                   \
        sbb    r10,[P2+0x20];                   \
        mov    r11,[P1+0x28];                   \
        sbb    r11,[P2+0x28];                   \
        sbb    rcx,rcx;                         \
        mov    esi,0xffffffff;                  \
        and    rcx,rsi;                         \
        xor    rsi,rsi;                         \
        sub    rsi,rcx;                         \
        sub    rax,rsi;                         \
        mov    [P0],rax;                        \
        sbb    rdx,rcx;                         \
        mov    [P0+0x8],rdx;                    \
        sbb    rax,rax;                         \
        and    rcx,rsi;                         \
        neg    rax;                             \
        sbb    r8,rcx;                          \
        mov    [P0+0x10],r8;                    \
        sbb    r9,0x0;                          \
        mov    [P0+0x18],r9;                    \
        sbb    r10,0x0;                         \
        mov    [P0+0x20],r10;                   \
        sbb    r11,0x0;                         \
        mov    [P0+0x28],r11

// Additional macros to help with final multiplexing

#define load6(r0,r1,r2,r3,r4,r5,P)              \
        mov     r0, [P];                        \
        mov     r1, [P+8];                      \
        mov     r2, [P+16];                     \
        mov     r3, [P+24];                     \
        mov     r4, [P+32];                     \
        mov     r5, [P+40]

#define store6(P,r0,r1,r2,r3,r4,r5)             \
        mov     [P], r0;                        \
        mov     [P+8], r1;                      \
        mov     [P+16], r2;                     \
        mov     [P+24], r3;                     \
        mov     [P+32], r4;                     \
        mov     [P+40], r5;                     \

#define czload6(r0,r1,r2,r3,r4,r5,P)            \
        cmovz   r0, [P];                        \
        cmovz   r1, [P+8];                      \
        cmovz   r2, [P+16];                     \
        cmovz   r3, [P+24];                     \
        cmovz   r4, [P+32];                     \
        cmovz   r5, [P+40]

#define muxload6(r0,r1,r2,r3,r4,r5,P0,P1,P2)    \
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
        cmovnbe r3, [P2+24];                    \
        mov     r4, [P0+32];                    \
        cmovb   r4, [P1+32];                    \
        cmovnbe r4, [P2+32];                    \
        mov     r5, [P0+40];                    \
        cmovb   r5, [P1+40];                    \
        cmovnbe r5, [P2+40]

S2N_BN_SYMBOL(p384_montjadd):
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
// Put the input arguments in non-volatile places on the stack

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

        mov     input_x, rsi
        mov     input_y, rdx

// Main code, just a sequence of basic field operations
// 8 * multiply + 3 * square + 7 * subtract

        amontsqr_p384(z1sq,z_1)
        mov     rsi, input_y
        amontsqr_p384(z2sq,z_2_alt)

        mov     rsi, input_x
        mov     rcx, input_y
        montmul_p384(y1a,z_2,y_1)
        mov     rsi, input_x
        mov     rcx, input_y
        montmul_p384(y2a,z_1,y_2)

        mov     rcx, input_y
        montmul_p384(x2a,z1sq,x_2)
        mov     rsi, input_x
        montmul_p384(x1a,z2sq,x_1)
        montmul_p384(y2a,z1sq,y2a)
        montmul_p384(y1a,z2sq,y1a)

        sub_p384(xd,x2a,x1a)
        sub_p384(yd,y2a,y1a)

        amontsqr_p384(zz,xd)
        montsqr_p384(ww,yd)

        montmul_p384(zzx1,zz,x1a)
        montmul_p384(zzx2,zz,x2a)

        sub_p384(resx,ww,zzx1)
        sub_p384(t1,zzx2,zzx1)

        mov     rsi, input_x
        montmul_p384(xd,xd,z_1)

        sub_p384(resx,resx,zzx2)

        sub_p384(t2,zzx1,resx)

        montmul_p384(t1,t1,y1a)

        mov     rcx, input_y
        montmul_p384(resz,xd,z_2)
        montmul_p384(t2,yd,t2)

        sub_p384(resy,t2,t1)

// Load in the z coordinates of the inputs to check for P1 = 0 and P2 = 0
// The condition codes get set by a comparison (P2 != 0) - (P1 != 0)
// So "NBE" <=> ~(CF \/ ZF) <=> P1 = 0 /\ ~(P2 = 0)
// and "B"  <=> CF          <=> ~(P1 = 0) /\ P2 = 0
// and "Z"  <=> ZF          <=> (P1 = 0 <=> P2 = 0)
// Multiplex the z outputs accordingly and re-store in resz

        mov     rcx, input_y
        load6(r8,r9,r10,r11,rbx,rbp,z_2)
        mov     rax, r8
        mov     rdx, r9
        or      rax, r10
        or      rdx, r11
        or      rax, rbx
        or      rdx, rbp
        or      rax, rdx
        neg     rax
        sbb     rax, rax

        mov     rsi, input_x
        load6(r12,r13,r14,r15,rdx,rcx,z_1)
        cmovz   r8, r12
        cmovz   r9, r13
        cmovz   r10, r14
        cmovz   r11, r15
        cmovz   rbx, rdx
        cmovz   rbp, rcx
        or      r12, r13
        or      r14, r15
        or      rdx, rcx
        or      r12, r14
        or      rdx, r12
        neg     rdx
        sbb     rdx, rdx

        cmp     rax, rdx

        czload6(r8,r9,r10,r11,rbx,rbp,resz)
        store6(resz,r8,r9,r10,r11,rbx,rbp)

// Multiplex the x and y outputs too, keeping the results in registers

        mov     rcx, input_y
        mov     rsi, input_x
        muxload6(r8,r9,r10,r11,rbx,rbp,resx,x_1,x_2)
        muxload6(r12,r13,r14,r15,rdx,rax,resy,y_1,y_2)

// Finally store back the multiplexed values

        store6(x_3,r8,r9,r10,r11,rbx,rbp)
        load6(r8,r9,r10,r11,rbx,rbp,resz)
        store6(y_3,r12,r13,r14,r15,rdx,rax)
        store6(z_3,r8,r9,r10,r11,rbx,rbp)

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

S2N_BN_SIZE_DIRECTIVE(p384_montjadd)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
