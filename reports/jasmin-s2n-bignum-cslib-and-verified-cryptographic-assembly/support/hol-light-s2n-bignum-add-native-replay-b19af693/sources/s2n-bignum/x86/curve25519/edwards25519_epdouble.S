// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Extended projective doubling for edwards25519
// Input p1[12]; output p3[16]
//
// extern void edwards25519_epdouble
//   (uint64_t p3[static 16],const uint64_t p1[static 12]);
//
// If p1 is a point on edwards25519, returns its double p3 = 2 * p1.
// The output p3 is in extended projective coordinates, representing
// affine (x,y) by a quadruple (X,Y,Z,T) where x = X / Z, y = Y / Z
// and x * y = T / Z. The input p1 may also be in the same extended
// projective representation, but the final T field is not used so
// a more basic projective triple (X,Y,Z) suffices.
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(edwards25519_epdouble)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(edwards25519_epdouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(edwards25519_epdouble)
        .text

// Size of individual field elements

#define NUMSIZE 32

// Registers used for inputs and outputs within basic operations.
// Here p1 and p3 are where the parameters come in anyway.

#define p3 rdi
#define p1 rsi

// Pointers to input and output coordinates

#define x_1 p1+0
#define y_1 p1+NUMSIZE
#define z_1 p1+(2*NUMSIZE)

#define x_3 p3+0
#define y_3 p3+NUMSIZE
#define z_3 p3+(2*NUMSIZE)
#define w_3 p3+(3*NUMSIZE)

// Pointer-offset pairs for temporaries on stack

#define t0 rsp+(0*NUMSIZE)
#define t1 rsp+(1*NUMSIZE)
#define t2 rsp+(2*NUMSIZE)
#define t3 rsp+(3*NUMSIZE)
#define t4 rsp+(4*NUMSIZE)

// Total size to reserve on the stack

#define NSPACE 5*NUMSIZE

// Macro wrapping up the basic field multiplication, only trivially
// different from a pure function call to bignum_mul_p25519.

#define mul_p25519(P0,P1,P2)                    \
        xor    esi, esi;                        \
        mov    rdx, [P2];                       \
        mulx   r9, r8, [P1];                    \
        mulx   r10, rax, [P1+0x8];              \
        add    r9, rax;                         \
        mulx   r11, rax, [P1+0x10];             \
        adc    r10, rax;                        \
        mulx   r12, rax, [P1+0x18];             \
        adc    r11, rax;                        \
        adc    r12, rsi;                        \
        xor    esi, esi;                        \
        mov    rdx, [P2+0x8];                   \
        mulx   rbx, rax, [P1];                  \
        adcx   r9, rax;                         \
        adox   r10, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   r13, rax, [P1+0x18];             \
        adcx   r12, rax;                        \
        adox   r13, rsi;                        \
        adcx   r13, rsi;                        \
        xor    esi, esi;                        \
        mov    rdx, [P2+0x10];                  \
        mulx   rbx, rax, [P1];                  \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r12, rax;                        \
        adox   r13, rbx;                        \
        mulx   r14, rax, [P1+0x18];             \
        adcx   r13, rax;                        \
        adox   r14, rsi;                        \
        adcx   r14, rsi;                        \
        xor    esi, esi;                        \
        mov    rdx, [P2+0x18];                  \
        mulx   rbx, rax, [P1];                  \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r12, rax;                        \
        adox   r13, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r13, rax;                        \
        adox   r14, rbx;                        \
        mulx   r15, rax, [P1+0x18];             \
        adcx   r14, rax;                        \
        adox   r15, rsi;                        \
        adcx   r15, rsi;                        \
        mov    edx, 0x26;                       \
        xor    esi, esi;                        \
        mulx   rbx, rax, r12;                   \
        adcx   r8, rax;                         \
        adox   r9, rbx;                         \
        mulx   rbx, rax, r13;                   \
        adcx   r9, rax;                         \
        adox   r10, rbx;                        \
        mulx   rbx, rax, r14;                   \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   r12, rax, r15;                   \
        adcx   r11, rax;                        \
        adox   r12, rsi;                        \
        adcx   r12, rsi;                        \
        shld   r12, r11, 0x1;                   \
        mov    edx, 0x13;                       \
        inc    r12;                             \
        bts    r11, 63;                         \
        mulx   rbx, rax, r12;                   \
        add    r8, rax;                         \
        adc    r9, rbx;                         \
        adc    r10, rsi;                        \
        adc    r11, rsi;                        \
        sbb    rax, rax;                        \
        not    rax;                             \
        and    rax, rdx;                        \
        sub    r8, rax;                         \
        sbb    r9, rsi;                         \
        sbb    r10, rsi;                        \
        sbb    r11, rsi;                        \
        btr    r11, 63;                         \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

#define sqr_4(P0,P1)                            \
        mov    rdx, [P1];                       \
        mulx   r15, r8, rdx;                    \
        mulx   r10, r9, [P1+0x8];               \
        mulx   r12, r11, [P1+0x18];             \
        mov    rdx, [P1+0x10];                  \
        mulx   r14, r13, [P1+0x18];             \
        xor    ebx, ebx;                        \
        mulx   rcx, rax, [P1];                  \
        adcx   r10, rax;                        \
        adox   r11, rcx;                        \
        mulx   rcx, rax, [P1+0x8];              \
        adcx   r11, rax;                        \
        adox   r12, rcx;                        \
        mov    rdx, [P1+0x18];                  \
        mulx   rcx, rax, [P1+0x8];              \
        adcx   r12, rax;                        \
        adox   r13, rcx;                        \
        adcx   r13, rbx;                        \
        adox   r14, rbx;                        \
        adc    r14, rbx;                        \
        xor    ebx, ebx;                        \
        adcx   r9, r9;                          \
        adox   r9, r15;                         \
        mov    rdx, [P1+0x8];                   \
        mulx   rdx, rax, rdx;                   \
        adcx   r10, r10;                        \
        adox   r10, rax;                        \
        adcx   r11, r11;                        \
        adox   r11, rdx;                        \
        mov    rdx, [P1+0x10];                  \
        mulx   rdx, rax, rdx;                   \
        adcx   r12, r12;                        \
        adox   r12, rax;                        \
        adcx   r13, r13;                        \
        adox   r13, rdx;                        \
        mov    rdx, [P1+0x18];                  \
        mulx   r15, rax, rdx;                   \
        adcx   r14, r14;                        \
        adox   r14, rax;                        \
        adcx   r15, rbx;                        \
        adox   r15, rbx;                        \
        mov    edx, 0x26;                       \
        xor    ebx, ebx;                        \
        mulx   rcx, rax, r12;                   \
        adcx   r8, rax;                         \
        adox   r9, rcx;                         \
        mulx   rcx, rax, r13;                   \
        adcx   r9, rax;                         \
        adox   r10, rcx;                        \
        mulx   rcx, rax, r14;                   \
        adcx   r10, rax;                        \
        adox   r11, rcx;                        \
        mulx   r12, rax, r15;                   \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        adcx   r12, rbx;                        \
        shld   r12, r11, 0x1;                   \
        btr    r11, 0x3f;                       \
        mov    edx, 0x13;                       \
        imul   rdx, r12;                        \
        add    r8, rdx;                         \
        adc    r9, rbx;                         \
        adc    r10, rbx;                        \
        adc    r11, rbx;                        \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// Plain 4-digit add without any normalization
// With inputs < p_25519 (indeed < 2^255) it still gives a 4-digit result,
// indeed one < 2 * p_25519 for normalized inputs.

#define add_4(P0,P1,P2)                         \
        mov     rax, [P1];                      \
        add     rax, [P2];                      \
        mov     [P0], rax;                      \
        mov     rax, [P1+8];                    \
        adc     rax, [P2+8];                    \
        mov     [P0+8], rax;                    \
        mov     rax, [P1+16];                   \
        adc     rax, [P2+16];                   \
        mov     [P0+16], rax;                   \
        mov     rax, [P1+24];                   \
        adc     rax, [P2+24];                   \
        mov     [P0+24], rax

// Modular subtraction with double modulus 2 * p_25519 = 2^256 - 38

#define sub_twice4(P0,P1,P2)                    \
        mov     r8, [P1];                       \
        xor     ebx, ebx;                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     ecx, 38;                        \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     rax, [P1+24];                   \
        sbb     rax, [P2+24];                   \
        cmovnc  rcx, rbx;                       \
        sub     r8, rcx;                        \
        sbb     r9, rbx;                        \
        sbb     r10, rbx;                       \
        sbb     rax, rbx;                       \
        mov     [P0], r8;                       \
        mov     [P0+8], r9;                     \
        mov     [P0+16], r10;                   \
        mov     [P0+24], rax

// Modular addition and doubling with double modulus 2 * p_25519 = 2^256 - 38.
// This only ensures that the result fits in 4 digits, not that it is reduced
// even w.r.t. double modulus. The result is always correct modulo provided
// the sum of the inputs is < 2^256 + 2^256 - 38, so in particular provided
// at least one of them is reduced double modulo.

#define add_twice4(P0,P1,P2)                    \
        mov     r8, [P1];                       \
        xor     ecx, ecx;                       \
        add     r8, [P2];                       \
        mov     r9, [P1+0x8];                   \
        adc     r9, [P2+0x8];                   \
        mov     r10, [P1+0x10];                 \
        adc     r10, [P2+0x10];                 \
        mov     r11, [P1+0x18];                 \
        adc     r11, [P2+0x18];                 \
        mov     eax, 38;                        \
        cmovnc  rax, rcx;                       \
        add     r8, rax;                        \
        adc     r9, rcx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

#define double_twice4(P0,P1)                    \
        mov     r8, [P1];                       \
        xor     ecx, ecx;                       \
        add     r8, r8;                         \
        mov     r9, [P1+0x8];                   \
        adc     r9, r9;                         \
        mov     r10, [P1+0x10];                 \
        adc     r10, r10;                       \
        mov     r11, [P1+0x18];                 \
        adc     r11, r11;                       \
        mov     eax, 38;                        \
        cmovnc  rax, rcx;                       \
        add     r8, rax;                        \
        adc     r9, rcx;                        \
        adc     r10, rcx;                       \
        adc     r11, rcx;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

S2N_BN_SYMBOL(edwards25519_epdouble):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Save registers, make room for temps, preserve input arguments.

        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

        CFI_DEC_RSP(NSPACE)

// Main sequence

        add_4(t0,x_1,y_1)
        sqr_4(t1,z_1)
        sqr_4(t2,x_1)
        sqr_4(t3,y_1)
        double_twice4(t1,t1)
        sqr_4(t0,t0)
        add_twice4(t4,t2,t3)
        sub_twice4(t2,t2,t3)
        add_twice4(t3,t1,t2)
        sub_twice4(t1,t4,t0)
        mul_p25519(y_3,t2,t4)
        mul_p25519(z_3,t3,t2)
        mul_p25519(w_3,t1,t4)
        mul_p25519(x_3,t1,t3)

// Restore stack and registers

        CFI_INC_RSP(NSPACE)

        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(edwards25519_epdouble)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
