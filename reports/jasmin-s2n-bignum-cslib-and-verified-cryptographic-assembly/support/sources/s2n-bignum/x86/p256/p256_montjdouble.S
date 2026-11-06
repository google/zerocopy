// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on NIST curve P-256 in Montgomery-Jacobian coordinates
//
//    extern void p256_montjdouble(uint64_t p3[static 12],
//                                 const uint64_t p1[static 12]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p256_montjdouble)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p256_montjdouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p256_montjdouble)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Pointer-offset pairs for inputs and outputs
// These assume rdi = p3, rsi = p1, which is true when the
// arguments come in initially and is not disturbed throughout.

#define x_1 rsi+0
#define y_1 rsi+NUMSIZE
#define z_1 rsi+(2*NUMSIZE)

#define x_3 rdi+0
#define y_3 rdi+NUMSIZE
#define z_3 rdi+(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define z2 rsp+(NUMSIZE*0)
#define y4 rsp+(NUMSIZE*0)

#define y2 rsp+(NUMSIZE*1)

#define t1 rsp+(NUMSIZE*2)

#define t2 rsp+(NUMSIZE*3)
#define x2p rsp+(NUMSIZE*3)
#define dx2 rsp+(NUMSIZE*3)

#define xy2 rsp+(NUMSIZE*4)

#define x4p rsp+(NUMSIZE*5)
#define d rsp+(NUMSIZE*5)

#define NSPACE NUMSIZE*6

// Corresponds exactly to bignum_montmul_p256

#define montmul_p256(P0,P1,P2)                  \
        xor     r13d,r13d;                      \
        mov     rdx,[P2];                       \
        mulx    r9,r8,[P1];                     \
        mulx    r10,rbx,[P1+0x8];               \
        adc     r9,rbx;                         \
        mulx    r11,rbx,[P1+0x10];              \
        adc     r10,rbx;                        \
        mulx    r12,rbx,[P1+0x18];              \
        adc     r11,rbx;                        \
        adc     r12,r13;                        \
        mov     rdx,[P2+0x8];                   \
        xor     r14d,r14d;                      \
        mulx    rbx,rax,[P1];                   \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,[P1+0x18];              \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        adc     r13,r14;                        \
        xor     r15d,r15d;                      \
        movabs  rdx,0x100000000;                \
        mulx    rbx,rax,r8;                     \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,r9;                     \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        not     rdx;                            \
        lea     rdx,[rdx+0x2];                  \
        mulx    rbx,rax,r8;                     \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,r9;                     \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        adcx    r13,r15;                        \
        adox    r14,r15;                        \
        adc     r14,r15;                        \
        mov     rdx,[P2+0x10];                  \
        xor     r8d,r8d;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        adox    r14,r8;                         \
        mulx    rbx,rax,[P1+0x18];              \
        adc     r13,rax;                        \
        adc     r14,rbx;                        \
        adc     r15,r8;                         \
        mov     rdx,[P2+0x18];                  \
        xor     r9d,r9d;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        mulx    rbx,rax,[P1+0x10];              \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        adox    r15,r9;                         \
        mulx    rbx,rax,[P1+0x18];              \
        adc     r14,rax;                        \
        adc     r15,rbx;                        \
        adc     r8,r9;                          \
        xor     r9d,r9d;                        \
        movabs  rdx,0x100000000;                \
        mulx    rbx,rax,r10;                    \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,r11;                    \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        not     rdx;                            \
        lea     rdx,[rdx+0x2];                  \
        mulx    rbx,rax,r10;                    \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    rbx,rax,r11;                    \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        adcx    r15,r9;                         \
        adox    r8,r9;                          \
        adc     r8,r9;                          \
        mov     ecx,0x1;                        \
        add     rcx,r12;                        \
        dec     rdx;                            \
        adc     rdx,r13;                        \
        dec     r9;                             \
        mov     rax,r9;                         \
        adc     r9,r14;                         \
        mov     r11d,0xfffffffe;                \
        adc     r11,r15;                        \
        adc     rax,r8;                         \
        cmovb   r12,rcx;                        \
        cmovb   r13,rdx;                        \
        cmovb   r14,r9;                         \
        cmovb   r15,r11;                        \
        mov     [P0],r12;                       \
        mov     [P0+0x8],r13;                   \
        mov     [P0+0x10],r14;                  \
        mov     [P0+0x18],r15

// Corresponds exactly to bignum_montsqr_p256

#define montsqr_p256(P0,P1)                     \
        mov     rdx,[P1];                       \
        mulx    r15,r8,rdx;                     \
        mulx    r10,r9,[P1+0x8];                \
        mulx    r12,r11,[P1+0x18];              \
        mov     rdx,[P1+0x10];                  \
        mulx    r14,r13,[P1+0x18];              \
        xor     ebp,ebp;                        \
        mulx    rbx,rax,[P1];                   \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mov     rdx,[P1+0x18];                  \
        mulx    rbx,rax,[P1+0x8];               \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        adcx    r13,rbp;                        \
        adox    r14,rbp;                        \
        adc     r14,rbp;                        \
        xor     ebp,ebp;                        \
        adcx    r9,r9;                          \
        adox    r9,r15;                         \
        mov     rdx,[P1+0x8];                   \
        mulx    rdx,rax,rdx;                    \
        adcx    r10,r10;                        \
        adox    r10,rax;                        \
        adcx    r11,r11;                        \
        adox    r11,rdx;                        \
        mov     rdx,[P1+0x10];                  \
        mulx    rdx,rax,rdx;                    \
        adcx    r12,r12;                        \
        adox    r12,rax;                        \
        adcx    r13,r13;                        \
        adox    r13,rdx;                        \
        mov     rdx,[P1+0x18];                  \
        mulx    r15,rax,rdx;                    \
        adcx    r14,r14;                        \
        adox    r14,rax;                        \
        adcx    r15,rbp;                        \
        adox    r15,rbp;                        \
        xor     ebp,ebp;                        \
        movabs  rdx,0x100000000;                \
        mulx    rbx,rax,r8;                     \
        adcx    r9,rax;                         \
        adox    r10,rbx;                        \
        mulx    rbx,rax,r9;                     \
        adcx    r10,rax;                        \
        adox    r11,rbx;                        \
        movabs  rdx,0xffffffff00000001;         \
        mulx    rbx,rax,r8;                     \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,r9;                     \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        adcx    r13,rbp;                        \
        mov     r9d,ebp;                        \
        adox    r9,rbp;                         \
        adcx    r9,rbp;                         \
        add     r14,r9;                         \
        adc     r15,rbp;                        \
        mov     r8d,ebp;                        \
        adc     r8,rbp;                         \
        xor     ebp,ebp;                        \
        movabs  rdx,0x100000000;                \
        mulx    rbx,rax,r10;                    \
        adcx    r11,rax;                        \
        adox    r12,rbx;                        \
        mulx    rbx,rax,r11;                    \
        adcx    r12,rax;                        \
        adox    r13,rbx;                        \
        movabs  rdx,0xffffffff00000001;         \
        mulx    rbx,rax,r10;                    \
        adcx    r13,rax;                        \
        adox    r14,rbx;                        \
        mulx    rbx,rax,r11;                    \
        adcx    r14,rax;                        \
        adox    r15,rbx;                        \
        adcx    r15,rbp;                        \
        adox    r8,rbp;                         \
        adc     r8,rbp;                         \
        mov     ecx,0x1;                        \
        add     rcx,r12;                        \
        lea     rdx,[rdx-0x1];                  \
        adc     rdx,r13;                        \
        lea     rbp,[rbp-0x1];                  \
        mov     rax,rbp;                        \
        adc     rbp,r14;                        \
        mov     r11d,0xfffffffe;                \
        adc     r11,r15;                        \
        adc     rax,r8;                         \
        cmovb   r12,rcx;                        \
        cmovb   r13,rdx;                        \
        cmovb   r14,rbp;                        \
        cmovb   r15,r11;                        \
        mov     [P0],r12;                       \
        mov     [P0+0x8],r13;                   \
        mov     [P0+0x10],r14;                  \
        mov     [P0+0x18],r15

// Corresponds exactly to bignum_sub_p256

#define sub_p256(P0,P1,P2)                      \
        mov     rax,[P1];                       \
        sub     rax,[P2];                       \
        mov     rcx,[P1+0x8];                   \
        sbb     rcx,[P2+0x8];                   \
        mov     r8,[P1+0x10];                   \
        sbb     r8,[P2+0x10];                   \
        mov     r9,[P1+0x18];                   \
        sbb     r9,[P2+0x18];                   \
        mov     r10d,0xffffffff;                \
        sbb     r11,r11;                        \
        xor     rdx,rdx;                        \
        and     r10,r11;                        \
        sub     rdx,r10;                        \
        add     rax,r11;                        \
        mov     [P0],rax;                       \
        adc     rcx,r10;                        \
        mov     [P0+0x8],rcx;                   \
        adc     r8,0x0;                         \
        mov     [P0+0x10],r8;                   \
        adc     r9,rdx;                         \
        mov     [P0+0x18],r9

// Corresponds exactly to bignum_add_p256

#define add_p256(P0,P1,P2)                      \
        xor     r11,r11;                        \
        mov     rax,[P1];                       \
        add     rax,[P2];                       \
        mov     rcx,[P1+0x8];                   \
        adc     rcx,[P2+0x8];                   \
        mov     r8,[P1+0x10];                   \
        adc     r8,[P2+0x10];                   \
        mov     r9,[P1+0x18];                   \
        adc     r9,[P2+0x18];                   \
        adc     r11,r11;                        \
        sub     rax,0xffffffffffffffff;         \
        mov     r10d,0xffffffff;                \
        sbb     rcx,r10;                        \
        sbb     r8,0x0;                         \
        mov     rdx,0xffffffff00000001;         \
        sbb     r9,rdx;                         \
        sbb     r11,0x0;                        \
        and     r10,r11;                        \
        and     rdx,r11;                        \
        add     rax,r11;                        \
        mov     [P0],rax;                       \
        adc     rcx,r10;                        \
        mov     [P0+0x8],rcx;                   \
        adc     r8,0x0;                         \
        mov     [P0+0x10],r8;                   \
        adc     r9,rdx;                         \
        mov     [P0+0x18],r9

// A weak version of add that only guarantees sum in 4 digits

#define weakadd_p256(P0,P1,P2)                  \
        mov     rax,[P1];                       \
        add     rax,[P2];                       \
        mov     rcx,[P1+0x8];                   \
        adc     rcx,[P2+0x8];                   \
        mov     r8,[P1+0x10];                   \
        adc     r8,[P2+0x10];                   \
        mov     r9,[P1+0x18];                   \
        adc     r9,[P2+0x18];                   \
        mov     r10d,0xffffffff;                \
        sbb     r11,r11;                        \
        xor     rdx,rdx;                        \
        and     r10,r11;                        \
        sub     rdx,r10;                        \
        sub     rax,r11;                        \
        mov     [P0],rax;                       \
        sbb     rcx,r10;                        \
        mov     [P0+0x8],rcx;                   \
        sbb     r8,0x0;                         \
        mov     [P0+0x10],r8;                   \
        sbb     r9,rdx;                         \
        mov     [P0+0x18],r9

// P0 = C * P1 - D * P2  computed as d * (p_256 - P2) + c * P1
// Quotient estimation is done just as q = h + 1 as in bignum_triple_p256
// This also applies to the other functions following.

#define cmsub_p256(P0,C,P1,D,P2)                \
        /* First [r11;r10;r9;r8] = p_256 - P2 */ \
        mov     r8,0xffffffffffffffff;          \
        xor     r10d,r10d;                      \
        sub     r8,[P2];                        \
        mov     r9,0x00000000ffffffff;          \
        sbb     r9,[P2+0x8];                    \
        sbb     r10,[P2+0x10];                  \
        mov     r11,0xffffffff00000001;         \
        sbb     r11,[P2+0x18];                  \
        /* [r12;r11;r10;r9;r8] = D * (p_256 - P2) */  \
        xor     r12d,r12d;                      \
        mov     rdx, D;                         \
        mulx    rax, r8, r8;                    \
        mulx    rcx, r9, r9;                    \
        add     r9, rax;                        \
        mulx    rax, r10, r10;                  \
        adc     r10, rcx;                       \
        mulx    rcx, r11, r11;                  \
        adc     r11, rax;                       \
        adc     r12, rcx;                       \
        /* [rdx;r11;r10;r9;r8] = 2^256 + C * P1 + D * (p_256 - P2) */ \
        mov     rdx, C;                         \
        xor     eax, eax;                       \
        mulx    rcx, rax, [P1];                 \
        adcx    r8, rax;                        \
        adox    r9, rcx;                        \
        mulx    rcx, rax, [P1+0x8];             \
        adcx    r9, rax;                        \
        adox    r10, rcx;                       \
        mulx    rcx, rax, [P1+0x10];            \
        adcx    r10, rax;                       \
        adox    r11, rcx;                       \
        mulx    rdx, rax, [P1+0x18];            \
        adcx    r11, rax;                       \
        adox    rdx, r12;                       \
        adc     rdx, 1;                         \
        /* Now the tail for modular reduction from tripling */ \
        add     r8,rdx;                         \
        mov     rax,0x100000000;                \
        mulx    rcx,rax,rax;                    \
        sbb     rax,0x0;                        \
        sbb     rcx,0x0;                        \
        sub     r9,rax;                         \
        sbb     r10,rcx;                        \
        mov     rax,0xffffffff00000001;         \
        mulx    rcx,rax,rax;                    \
        sbb     r11,rax;                        \
        sbb     rdx,rcx;                        \
        dec     rdx;                            \
        mov     eax,0xffffffff;                 \
        and     rax,rdx;                        \
        xor     ecx,ecx;                        \
        sub     rcx,rax;                        \
        add     r8,rdx;                         \
        mov     [P0],r8;                        \
        adc     r9,rax;                         \
        mov     [P0+0x8],r9;                    \
        adc     r10,0x0;                        \
        mov     [P0+0x10],r10;                  \
        adc     r11,rcx;                        \
        mov     [P0+0x18],r11

// P0 = 3 * P1 - 8 * P2, computed as (p_256 - P2) << 3 + 3 * P1

#define cmsub38_p256(P0,P1,P2)                  \
        /* First [r11;r10;r9;r8] = p_256 - P2 */ \
        mov     r8,0xffffffffffffffff;          \
        xor     r10d,r10d;                      \
        sub     r8,[P2];                        \
        mov     r9,0x00000000ffffffff;          \
        sbb     r9,[P2+0x8];                    \
        sbb     r10,[P2+0x10];                  \
        mov     r11,0xffffffff00000001;         \
        sbb     r11,[P2+0x18];                  \
        /* [r12;r11;r10;r9;r8] = (p_256 - P2) << 3 */  \
        mov     r12, r11;                       \
        shld    r11, r10, 3;                    \
        shld    r10, r9, 3;                     \
        shld    r9, r8, 3;                      \
        shl     r8, 3;                          \
        shr     r12, 61;                        \
        /* [rdx;r11;r10;r9;r8] = 2^256 + 3 * P1 + 8 * (p_256 - P2) */ \
        mov     rdx, 3;                         \
        xor     eax, eax;                       \
        mulx    rcx, rax, [P1];                 \
        adcx    r8, rax;                        \
        adox    r9, rcx;                        \
        mulx    rcx, rax, [P1+0x8];             \
        adcx    r9, rax;                        \
        adox    r10, rcx;                       \
        mulx    rcx, rax, [P1+0x10];            \
        adcx    r10, rax;                       \
        adox    r11, rcx;                       \
        mulx    rdx, rax, [P1+0x18];            \
        adcx    r11, rax;                       \
        adox    rdx, r12;                       \
        adc     rdx, 1;                         \
        /* Now the tail for modular reduction from tripling */ \
        add     r8,rdx;                         \
        mov     rax,0x100000000;                \
        mulx    rcx,rax,rax;                    \
        sbb     rax,0x0;                        \
        sbb     rcx,0x0;                        \
        sub     r9,rax;                         \
        sbb     r10,rcx;                        \
        mov     rax,0xffffffff00000001;         \
        mulx    rcx,rax,rax;                    \
        sbb     r11,rax;                        \
        sbb     rdx,rcx;                        \
        dec     rdx;                            \
        mov     eax,0xffffffff;                 \
        and     rax,rdx;                        \
        xor     ecx,ecx;                        \
        sub     rcx,rax;                        \
        add     r8,rdx;                         \
        mov     [P0],r8;                        \
        adc     r9,rax;                         \
        mov     [P0+0x8],r9;                    \
        adc     r10,0x0;                        \
        mov     [P0+0x10],r10;                  \
        adc     r11,rcx;                        \
        mov     [P0+0x18],r11

// P0 = 4 * P1 - P2, by direct subtraction of P2,
// since the quotient estimate still works safely
// for initial value > -p_256

#define cmsub41_p256(P0,P1,P2)                  \
        mov     r11,[P1+0x18];                  \
        mov     rdx, r11;                       \
        mov     r10,[P1+0x10];                  \
        shld    r11, r10, 2;                    \
        mov     r9,[P1+0x8];                    \
        shld    r10, r9, 2;                     \
        mov     r8,[P1];                        \
        shld    r9, r8, 2;                      \
        shl     r8, 2;                          \
        shr     rdx, 62;                        \
        add     rdx, 1;                         \
        sub     r8, [P2];                       \
        sbb     r9, [P2+0x8];                   \
        sbb     r10, [P2+0x10];                 \
        sbb     r11, [P2+0x18];                 \
        sbb     rdx, 0;                         \
        /* Now the tail for modular reduction from tripling */ \
        add     r8,rdx;                         \
        mov     rax,0x100000000;                \
        mulx    rcx,rax,rax;                    \
        sbb     rax,0x0;                        \
        sbb     rcx,0x0;                        \
        sub     r9,rax;                         \
        sbb     r10,rcx;                        \
        mov     rax,0xffffffff00000001;         \
        mulx    rcx,rax,rax;                    \
        sbb     r11,rax;                        \
        sbb     rdx,rcx;                        \
        dec     rdx;                            \
        mov     eax,0xffffffff;                 \
        and     rax,rdx;                        \
        xor     ecx,ecx;                        \
        sub     rcx,rax;                        \
        add     r8,rdx;                         \
        mov     [P0],r8;                        \
        adc     r9,rax;                         \
        mov     [P0+0x8],r9;                    \
        adc     r10,0x0;                        \
        mov     [P0+0x10],r10;                  \
        adc     r11,rcx;                        \
        mov     [P0+0x18],r11

S2N_BN_SYMBOL(p256_montjdouble):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save registers and make room on stack for temporary variables

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        montsqr_p256(z2,z_1)
        montsqr_p256(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        sub_p256(t2,x_1,z2)
        weakadd_p256(t1,x_1,z2)
        montmul_p256(x2p,t1,t2)

// t1 = y + z
// xy2 = x * y^2
// x4p = x2p^2

        add_p256(t1,y_1,z_1)
        montmul_p256(xy2,x_1,y2)
        montsqr_p256(x4p,x2p)

// t1 = (y + z)^2

        montsqr_p256(t1,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_p256(d,12,xy2,9,x4p)
        sub_p256(t1,t1,z2)

// y4 = y^4

        montsqr_p256(y4,y2)

// dx2 = d * x2p

        montmul_p256(dx2,d,x2p)

// z_3' = 2 * y * z

        sub_p256(z_3,t1,y2)

// x' = 4 * xy2 - d

        cmsub41_p256(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_p256(y_3,dx2,y4)

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

S2N_BN_SIZE_DIRECTIVE(p256_montjdouble)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
