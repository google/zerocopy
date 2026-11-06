// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// The x25519 function for curve25519
// Inputs scalar[4], point[4]; output res[4]
//
// extern void curve25519_x25519
//   (uint64_t res[static 4],const uint64_t scalar[static 4],
//    const uint64_t point[static 4]);
//
// The function has a second prototype considering the arguments as arrays
// of bytes rather than 64-bit words. The underlying code is the same, since
// the x86 platform is little-endian.
//
// extern void curve25519_x25519_byte
//   (uint8_t res[static 32],const uint8_t scalar[static 32],
//    const uint8_t point[static 32]);
//
// Given a scalar n and the X coordinate of an input point P = (X,Y) on
// curve25519 (Y can live in any extension field of characteristic 2^255-19),
// this returns the X coordinate of n * P = (X, Y), or 0 when n * P is the
// point at infinity. Both n and X inputs are first slightly modified/mangled
// as specified in the relevant RFC (https://www.rfc-editor.org/rfc/rfc7748);
// in particular the lower three bits of n are set to zero. Does not implement
// the zero-check specified in Section 6.1.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_x25519)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(curve25519_x25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_x25519)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_x25519_byte)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(curve25519_x25519_byte)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_x25519_byte)
        .text
        .balign 32

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for the input result argument during the whole body
// and other variables that are only needed prior to the modular inverse.

#define res QWORD PTR [rsp+12*NUMSIZE]
#define i QWORD PTR [rsp+12*NUMSIZE+8]
#define swap QWORD PTR [rsp+12*NUMSIZE+16]

// Pointers to result x coord to be written, assuming the base "res"
// has been loaded into rbp

#define resx rbp+0

// Pointer-offset pairs for temporaries on stack with some aliasing.
// Both dmsn and dnsm need space for >= 5 digits, and we allocate 8

#define scalar rsp+(0*NUMSIZE)

#define pointx rsp+(1*NUMSIZE)

#define dm rsp+(2*NUMSIZE)

#define zm rsp+(3*NUMSIZE)
#define sm rsp+(3*NUMSIZE)
#define dpro rsp+(3*NUMSIZE)

#define sn rsp+(4*NUMSIZE)

#define dn rsp+(5*NUMSIZE)
#define e rsp+(5*NUMSIZE)

#define dmsn rsp+(6*NUMSIZE)
#define p rsp+(6*NUMSIZE)
#define zn rsp+(7*NUMSIZE)

#define xm rsp+(8*NUMSIZE)
#define dnsm rsp+(8*NUMSIZE)
#define spro rsp+(8*NUMSIZE)

#define xn rsp+(10*NUMSIZE)
#define s rsp+(10*NUMSIZE)

#define d rsp+(11*NUMSIZE)

// Total size to reserve on the stack
// This includes space for the 3 other variables above
// and rounds up to a multiple of 32

#define NSPACE 13*NUMSIZE

// Macro wrapping up the basic field operation bignum_mul_p25519, only
// trivially different from a pure function call to that subroutine.

#define mul_p25519(P0,P1,P2)                    \
        xor    edi, edi;                        \
        mov    rdx, [P2];                       \
        mulx   r9, r8, [P1];                    \
        mulx   r10, rax, [P1+0x8];              \
        add    r9, rax;                         \
        mulx   r11, rax, [P1+0x10];             \
        adc    r10, rax;                        \
        mulx   r12, rax, [P1+0x18];             \
        adc    r11, rax;                        \
        adc    r12, rdi;                        \
        xor    edi, edi;                        \
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
        adox   r13, rdi;                        \
        adcx   r13, rdi;                        \
        xor    edi, edi;                        \
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
        adox   r14, rdi;                        \
        adcx   r14, rdi;                        \
        xor    edi, edi;                        \
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
        adox   r15, rdi;                        \
        adcx   r15, rdi;                        \
        mov    edx, 0x26;                       \
        xor    edi, edi;                        \
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
        adox   r12, rdi;                        \
        adcx   r12, rdi;                        \
        shld   r12, r11, 0x1;                   \
        mov    edx, 0x13;                       \
        inc    r12;                             \
        bts    r11, 63;                         \
        mulx   rbx, rax, r12;                   \
        add    r8, rax;                         \
        adc    r9, rbx;                         \
        adc    r10, rdi;                        \
        adc    r11, rdi;                        \
        sbb    rax, rax;                        \
        not    rax;                             \
        and    rax, rdx;                        \
        sub    r8, rax;                         \
        sbb    r9, rdi;                         \
        sbb    r10, rdi;                        \
        sbb    r11, rdi;                        \
        btr    r11, 63;                         \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// A version of multiplication that only guarantees output < 2 * p_25519.
// This basically skips the +1 and final correction in quotient estimation.

#define mul_4(P0,P1,P2)                         \
        xor    ecx, ecx;                        \
        mov    rdx, [P2];                       \
        mulx   r9, r8, [P1];                    \
        mulx   r10, rax, [P1+0x8];              \
        add    r9, rax;                         \
        mulx   r11, rax, [P1+0x10];             \
        adc    r10, rax;                        \
        mulx   r12, rax, [P1+0x18];             \
        adc    r11, rax;                        \
        adc    r12, rcx;                        \
        xor    ecx, ecx;                        \
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
        adox   r13, rcx;                        \
        adcx   r13, rcx;                        \
        xor    ecx, ecx;                        \
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
        adox   r14, rcx;                        \
        adcx   r14, rcx;                        \
        xor    ecx, ecx;                        \
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
        adox   r15, rcx;                        \
        adcx   r15, rcx;                        \
        mov    edx, 0x26;                       \
        xor    ecx, ecx;                        \
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
        adox   r12, rcx;                        \
        adcx   r12, rcx;                        \
        shld   r12, r11, 0x1;                   \
        btr    r11, 0x3f;                       \
        mov    edx, 0x13;                       \
        imul   rdx, r12;                        \
        add    r8, rdx;                         \
        adc    r9, rcx;                         \
        adc    r10, rcx;                        \
        adc    r11, rcx;                        \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// Multiplication just giving a 5-digit result (actually < 39 * p_25519)
// by not doing anything beyond the first stage of reduction

#define mul_5(P0,P1,P2)                         \
        xor    edi, edi;                        \
        mov    rdx, [P2];                       \
        mulx   r9, r8, [P1];                    \
        mulx   r10, rax, [P1+0x8];              \
        add    r9, rax;                         \
        mulx   r11, rax, [P1+0x10];             \
        adc    r10, rax;                        \
        mulx   r12, rax, [P1+0x18];             \
        adc    r11, rax;                        \
        adc    r12, rdi;                        \
        xor    edi, edi;                        \
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
        adox   r13, rdi;                        \
        adcx   r13, rdi;                        \
        xor    edi, edi;                        \
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
        adox   r14, rdi;                        \
        adcx   r14, rdi;                        \
        xor    edi, edi;                        \
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
        adox   r15, rdi;                        \
        adcx   r15, rdi;                        \
        mov    edx, 0x26;                       \
        xor    edi, edi;                        \
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
        adox   r12, rdi;                        \
        adcx   r12, rdi;                        \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11;                  \
        mov    [P0+0x20], r12

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

// Add 5-digit inputs and normalize to 4 digits

#define add5_4(P0,P1,P2)                        \
        mov     r8, [P1];                       \
        add     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        adc     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        adc     r10, [P2+16];                   \
        mov     r11, [P1+24];                   \
        adc     r11, [P2+24];                   \
        mov     r12, [P1+32];                   \
        adc     r12, [P2+32];                   \
        xor     ebx, ebx;                       \
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

// Modular addition with double modulus 2 * p_25519 = 2^256 - 38.
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

// 5-digit subtraction with upward bias to make it positive, adding
// 1000 * (2^255 - 19) = 2^256 * 500 - 19000, then normalizing to 4 digits

#define sub5_4(P0,P1,P2)                        \
        mov     r8, [P1];                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     r11, [P1+24];                   \
        sbb     r11, [P2+24];                   \
        mov     r12, [P1+32];                   \
        sbb     r12, [P2+32];                   \
        xor     ebx, ebx;                       \
        sub     r8, 19000;                      \
        sbb     r9, rbx;                        \
        sbb     r10, rbx;                       \
        sbb     r11, rbx;                       \
        sbb     r12, rbx;                       \
        add     r12, 500;                       \
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

// Combined z = c * x + y with reduction only < 2 * p_25519
// It is assumed that 19 * (c * x + y) < 2^60 * 2^256 so we
// don't need a high mul in the final part.

#define cmadd_4(P0,C1,P2,P3)                    \
        mov     r8, [P3];                       \
        mov     r9, [P3+8];                     \
        mov     r10, [P3+16];                   \
        mov     r11, [P3+24];                   \
        xor     edi, edi;                       \
        mov     rdx, C1;                        \
        mulx    rbx, rax, [P2];                 \
        adcx    r8, rax;                        \
        adox    r9, rbx;                        \
        mulx    rbx, rax, [P2+8];               \
        adcx    r9, rax;                        \
        adox    r10, rbx;                       \
        mulx    rbx, rax, [P2+16];              \
        adcx    r10, rax;                       \
        adox    r11, rbx;                       \
        mulx    rbx, rax, [P2+24];              \
        adcx    r11, rax;                       \
        adox    rbx, rdi;                       \
        adcx    rbx, rdi;                       \
        shld    rbx, r11, 0x1;                  \
        btr     r11, 63;                        \
        mov     edx, 0x13;                      \
        imul    rbx, rdx;                       \
        add     r8, rbx;                        \
        adc     r9, rdi;                        \
        adc     r10, rdi;                       \
        adc     r11, rdi;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Multiplex: z := if NZ then x else y

#define mux_4(P0,P1,P2)                         \
        mov     rax, [P1];                      \
        mov     rcx, [P2];                      \
        cmovz   rax, rcx;                       \
        mov     [P0], rax;                      \
        mov     rax, [P1+8];                    \
        mov     rcx, [P2+8];                    \
        cmovz   rax, rcx;                       \
        mov     [P0+8], rax;                    \
        mov     rax, [P1+16];                   \
        mov     rcx, [P2+16];                   \
        cmovz   rax, rcx;                       \
        mov     [P0+16], rax;                   \
        mov     rax, [P1+24];                   \
        mov     rcx, [P2+24];                   \
        cmovz   rax, rcx;                       \
        mov     [P0+24], rax

S2N_BN_SYMBOL(curve25519_x25519):
S2N_BN_SYMBOL(curve25519_x25519_byte):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save registers, make room for temps, preserve input arguments.

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(NSPACE)

// Move the output pointer to a stable place

        mov     res, rdi

// Copy the inputs to the local variables with minimal mangling:
//
//  - The scalar is in principle turned into 01xxx...xxx000 but
//    in the structure below the special handling of these bits is
//    explicit in the main computation; the scalar is just copied.
//
//  - The point x coord is reduced mod 2^255 by masking off the
//    top bit. In the main loop we only need reduction < 2 * p_25519.

        mov     rax, [rsi]
        mov     [rsp], rax
        mov     rax, [rsi+8]
        mov     [rsp+8], rax
        mov     rax, [rsi+16]
        mov     [rsp+16], rax
        mov     rax, [rsi+24]
        mov     [rsp+24], rax

        mov     r8, [rdx]
        mov     r9, [rdx+8]
        mov     r10, [rdx+16]
        mov     r11, [rdx+24]
        btr     r11, 63
        mov     [rsp+32], r8
        mov     [rsp+40], r9
        mov     [rsp+48], r10
        mov     [rsp+56], r11

// Initialize with explicit doubling in order to handle set bit 254.
// Set swap = 1 and (xm,zm) = (x,1) then double as (xn,zn) = 2 * (x,1).
// We use the fact that the point x coordinate is still in registers.
// Since zm = 1 we could do the doubling with an operation count of
// 2 * S + M instead of 2 * S + 2 * M, but it doesn't seem worth
// the slight complication arising from a different linear combination.

        mov     eax, 1
        mov     swap, rax
        mov     [rsp+256], r8
        mov     [rsp+96], rax
        xor     eax, eax
        mov     [rsp+264], r9
        mov     [rsp+104], rax
        mov     [rsp+272], r10
        mov     [rsp+112], rax
        mov     [rsp+280], r11
        mov     [rsp+120], rax

        sub_twice4(d,xm,zm)
        add_twice4(s,xm,zm)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        cmadd_4(e,0x1db42,p,d)
        mul_4(xn,s,d)
        mul_4(zn,p,e)

// The main loop over unmodified bits from i = 253, ..., i = 3 (inclusive).
// This is a classic Montgomery ladder, with the main coordinates only
// reduced mod 2 * p_25519, some intermediate results even more loosely.

        mov     eax, 253
        mov     i, rax

Lcurve25519_x25519_scalarloop:

// sm = xm + zm; sn = xn + zn; dm = xm - zm; dn = xn - zn

        sub_twice4(dm,xm,zm)
        add_twice4(sn,xn,zn)
        sub_twice4(dn,xn,zn)
        add_twice4(sm,xm,zm)

// DOUBLING: mux d = xt - zt and s = xt + zt for appropriate choice of (xt,zt)

        mov     rdx, i
        mov     rcx, rdx
        shr     rdx, 6
        mov     rdx, [rsp+8*rdx]
        shr     rdx, cl
        and     rdx, 1
        cmp     rdx, swap
        mov     swap, rdx
        mux_4(d,dm,dn)
        mux_4(s,sm,sn)

// ADDING: dmsn = dm * sn; dnsm = sm * dn

        mul_5(dnsm,sm,dn)
        mul_5(dmsn,sn,dm)

// DOUBLING: d = (xt - zt)^2

        sqr_4(d,d)

// ADDING: dpro = (dmsn - dnsm)^2, spro = (dmsn + dnsm)^2
// DOUBLING: s = (xt + zt)^2

        sub5_4(dpro,dmsn,dnsm)
        add5_4(spro,dmsn,dnsm)
        sqr_4(s,s)
        sqr_4(dpro,dpro)

// DOUBLING: p = 4 * xt * zt = s - d

        sub_twice4(p,s,d)

// ADDING: xm' = (dmsn + dnsm)^2

        sqr_4(xm,spro)

// DOUBLING: e = 121666 * p + d

        cmadd_4(e,0x1db42,p,d)

// DOUBLING: xn' = (xt + zt)^2 * (xt - zt)^2 = s * d

        mul_4(xn,s,d)

// DOUBLING: zn' = (4 * xt * zt) * ((xt - zt)^2 + 121666 * (4 * xt * zt))
//               = p * (d + 121666 * p)

        mul_4(zn,p,e)

// ADDING: zm' = x * (dmsn - dnsm)^2

        mul_4(zm,dpro,pointx)

// Loop down as far as 3 (inclusive)

        mov     rax, i
        sub     rax, 1
        mov     i, rax
        cmp     rax, 3
        jnc     Lcurve25519_x25519_scalarloop

// Multiplex directly into (xn,zn) then do three pure doubling steps;
// this accounts for the implicit zeroing of the three lowest bits
// of the scalar.

        mov     rdx, swap
        test    rdx, rdx
        mux_4(xn,xm,xn)
        mux_4(zn,zm,zn)

        sub_twice4(d,xn,zn)
        add_twice4(s,xn,zn)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        cmadd_4(e,0x1db42,p,d)
        mul_4(xn,s,d)
        mul_4(zn,p,e)

        sub_twice4(d,xn,zn)
        add_twice4(s,xn,zn)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        cmadd_4(e,0x1db42,p,d)
        mul_4(xn,s,d)
        mul_4(zn,p,e)

        sub_twice4(d,xn,zn)
        add_twice4(s,xn,zn)
        sqr_4(d,d)
        sqr_4(s,s)
        sub_twice4(p,s,d)
        cmadd_4(e,0x1db42,p,d)
        mul_4(xn,s,d)
        mul_4(zn,p,e)

// The projective result of the scalar multiplication is now (xn,zn).
// Prepare to call the modular inverse function to get zn' = 1/zn

        lea     rdi, [rsp+224]
        lea     rsi, [rsp+224]

// Inline copy of bignum_inv_p25519, identical except for stripping out
// the prologue and epilogue saving and restoring registers and making
// and reclaiming room on the stack. For more details and explanations see
// "x86/curve25519/bignum_inv_p25519.S". Note that the stack it uses for
// its own temporaries is 208 bytes, so it has no effect on variables
// that are needed in the rest of our computation here: res, xn and zn.

        mov     [rsp+0xc0], rdi
        xor     eax, eax
        lea     rcx, [rax-0x13]
        not     rax
        mov     [rsp], rcx
        mov     [rsp+0x8], rax
        mov     [rsp+0x10], rax
        btr     rax, 0x3f
        mov     [rsp+0x18], rax
        mov     rdx, [rsi]
        mov     rcx, [rsi+0x8]
        mov     r8, [rsi+0x10]
        mov     r9, [rsi+0x18]
        mov     eax, 0x1
        xor     r10d, r10d
        bts     r9, 0x3f
        adc     rax, r10
        imul    rax, rax, 0x13
        add     rdx, rax
        adc     rcx, r10
        adc     r8, r10
        adc     r9, r10
        mov     eax, 0x13
        cmovb   rax, r10
        sub     rdx, rax
        sbb     rcx, r10
        sbb     r8, r10
        sbb     r9, r10
        btr     r9, 0x3f
        mov     [rsp+0x20], rdx
        mov     [rsp+0x28], rcx
        mov     [rsp+0x30], r8
        mov     [rsp+0x38], r9
        xor     eax, eax
        mov     [rsp+0x40], rax
        mov     [rsp+0x48], rax
        mov     [rsp+0x50], rax
        mov     [rsp+0x58], rax
        movabs  rax, 0xa0f99e2375022099
        mov     [rsp+0x60], rax
        movabs  rax, 0xa8c68f3f1d132595
        mov     [rsp+0x68], rax
        movabs  rax, 0x6c6c893805ac5242
        mov     [rsp+0x70], rax
        movabs  rax, 0x276508b241770615
        mov     [rsp+0x78], rax
        mov     QWORD PTR [rsp+0x90], 0xa
        mov     QWORD PTR [rsp+0x98], 0x1
        jmp     Lcurve25519_x25519_midloop
Lcurve25519_x25519_inverseloop:
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
        mov     [rsp+0x80], rdi
        mov     rax, r12
        and     rax, r13
        mov     rsi, r14
        and     rsi, r15
        add     rsi, rax
        mov     [rsp+0x88], rsi
        xor     ebx, ebx
        mov     rax, [rsp]
        xor     rax, r9
        mul     r8
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x20]
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
        mov     rax, [rsp+0x20]
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
        mov     rax, [rsp+0x28]
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
        mov     rax, [rsp+0x28]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rdi, rdx
        shrd    rsi, rbp, 0x3b
        mov     [rsp+0x20], rsi
        xor     esi, esi
        mov     rax, [rsp+0x10]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rsi, rdx
        mov     rax, [rsp+0x30]
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
        mov     rax, [rsp+0x30]
        xor     rax, r15
        mul     r14
        add     rdi, rax
        adc     rbx, rdx
        shrd    rbp, rdi, 0x3b
        mov     [rsp+0x28], rbp
        mov     rax, [rsp+0x18]
        xor     rax, r9
        mov     rbp, rax
        sar     rbp, 0x3f
        and     rbp, r8
        neg     rbp
        mul     r8
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+0x38]
        xor     rax, r11
        mov     rdx, rax
        sar     rdx, 0x3f
        and     rdx, r10
        sub     rbp, rdx
        mul     r10
        add     rsi, rax
        adc     rbp, rdx
        shrd    rcx, rsi, 0x3b
        mov     [rsp+0x10], rcx
        shrd    rsi, rbp, 0x3b
        mov     rax, [rsp+0x18]
        mov     [rsp+0x18], rsi
        xor     rax, r13
        mov     rsi, rax
        sar     rsi, 0x3f
        and     rsi, r12
        neg     rsi
        mul     r12
        add     rbx, rax
        adc     rsi, rdx
        mov     rax, [rsp+0x38]
        xor     rax, r15
        mov     rdx, rax
        sar     rdx, 0x3f
        and     rdx, r14
        sub     rsi, rdx
        mul     r14
        add     rbx, rax
        adc     rsi, rdx
        shrd    rdi, rbx, 0x3b
        mov     [rsp+0x30], rdi
        shrd    rbx, rsi, 0x3b
        mov     [rsp+0x38], rbx
        mov     rbx, [rsp+0x80]
        mov     rbp, [rsp+0x88]
        xor     ecx, ecx
        mov     rax, [rsp+0x40]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+0x60]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx
        xor     esi, esi
        mov     rax, [rsp+0x40]
        xor     rax, r13
        mul     r12
        mov     [rsp+0x40], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+0x60]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+0x60], rbp
        xor     ebx, ebx
        mov     rax, [rsp+0x48]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x68]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rbx, rdx
        xor     ebp, ebp
        mov     rax, [rsp+0x48]
        xor     rax, r13
        mul     r12
        mov     [rsp+0x48], rcx
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+0x68]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        mov     [rsp+0x68], rsi
        xor     ecx, ecx
        mov     rax, [rsp+0x50]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+0x70]
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
        mov     rax, [rsp+0x70]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+0x70], rbp
        mov     rax, [rsp+0x58]
        xor     rax, r9
        mov     rbx, r9
        and     rbx, r8
        neg     rbx
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x78]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     rbx, rdx
        mul     r10
        add     rcx, rax
        adc     rdx, rbx
        mov     rbx, rdx
        shld    rdx, rcx, 0x1
        sar     rbx, 0x3f
        add     rdx, rbx
        mov     eax, 0x13
        imul    rdx
        mov     r8, [rsp+0x40]
        add     r8, rax
        mov     [rsp+0x40], r8
        mov     r8, [rsp+0x48]
        adc     r8, rdx
        mov     [rsp+0x48], r8
        mov     r8, [rsp+0x50]
        adc     r8, rbx
        mov     [rsp+0x50], r8
        adc     rcx, rbx
        shl     rax, 0x3f
        add     rcx, rax
        mov     rax, [rsp+0x58]
        mov     [rsp+0x58], rcx
        xor     rax, r13
        mov     rcx, r13
        and     rcx, r12
        neg     rcx
        mul     r12
        add     rsi, rax
        adc     rcx, rdx
        mov     rax, [rsp+0x78]
        xor     rax, r15
        mov     rdx, r15
        and     rdx, r14
        sub     rcx, rdx
        mul     r14
        add     rsi, rax
        adc     rdx, rcx
        mov     rcx, rdx
        shld    rdx, rsi, 0x1
        sar     rcx, 0x3f
        mov     eax, 0x13
        add     rdx, rcx
        imul    rdx
        mov     r8, [rsp+0x60]
        add     r8, rax
        mov     [rsp+0x60], r8
        mov     r8, [rsp+0x68]
        adc     r8, rdx
        mov     [rsp+0x68], r8
        mov     r8, [rsp+0x70]
        adc     r8, rcx
        mov     [rsp+0x70], r8
        adc     rsi, rcx
        shl     rax, 0x3f
        add     rsi, rax
        mov     [rsp+0x78], rsi
Lcurve25519_x25519_midloop:
        mov     rsi, [rsp+0x98]
        mov     rdx, [rsp]
        mov     rcx, [rsp+0x20]
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
        mov     [rsp+0xa0], rdx
        mov     [rsp+0xa8], rbx
        mov     [rsp+0xb0], rdi
        mov     [rsp+0xb8], rcx
        mov     r12, [rsp]
        imul    rdi, r12
        imul    r12, rdx
        mov     r13, [rsp+0x20]
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
        mov     rax, [rsp+0xa0]
        imul    rax, r8
        mov     rdx, [rsp+0xb0]
        imul    rdx, r15
        imul    r8, [rsp+0xa8]
        imul    r15, [rsp+0xb8]
        add     r15, r8
        lea     r9, [rax+rdx]
        mov     rax, [rsp+0xa0]
        imul    rax, r10
        mov     rdx, [rsp+0xb0]
        imul    rdx, r11
        imul    r10, [rsp+0xa8]
        imul    r11, [rsp+0xb8]
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
        mov     [rsp+0x98], rsi
        dec     QWORD PTR [rsp+0x90]
        jne     Lcurve25519_x25519_inverseloop
        mov     rax, [rsp]
        mov     rcx, [rsp+0x20]
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
        mov     rax, [rsp+0x40]
        xor     rax, r9
        mul     r8
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x60]
        xor     rax, r11
        mul     r10
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        mov     rax, [rsp+0x48]
        xor     rax, r9
        mul     r8
        add     r13, rax
        adc     r14, rdx
        mov     rax, [rsp+0x68]
        xor     rax, r11
        mul     r10
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rax, [rsp+0x50]
        xor     rax, r9
        mul     r8
        add     r14, rax
        adc     r15, rdx
        mov     rax, [rsp+0x70]
        xor     rax, r11
        mul     r10
        add     r14, rax
        adc     r15, rdx
        mov     rax, [rsp+0x58]
        xor     rax, r9
        and     r9, r8
        neg     r9
        mul     r8
        add     r15, rax
        adc     r9, rdx
        mov     rax, [rsp+0x78]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     r9, rdx
        mul     r10
        add     r15, rax
        adc     r9, rdx
        mov     rax, r9
        shld    rax, r15, 0x1
        sar     r9, 0x3f
        mov     ebx, 0x13
        lea     rax, [rax+r9+0x1]
        imul    rbx
        xor     ebp, ebp
        add     r12, rax
        adc     r13, rdx
        adc     r14, r9
        adc     r15, r9
        shl     rax, 0x3f
        add     r15, rax
        cmovns  rbx, rbp
        sub     r12, rbx
        sbb     r13, rbp
        sbb     r14, rbp
        sbb     r15, rbp
        btr     r15, 0x3f
        mov     rdi, [rsp+0xc0]
        mov     [rdi], r12
        mov     [rdi+0x8], r13
        mov     [rdi+0x10], r14
        mov     [rdi+0x18], r15

// Now the result is xn * (1/zn), fully reduced modulo p.
// Note that in the degenerate case zn = 0 (mod p_25519), the
// modular inverse code above will produce 1/zn = 0, giving
// the correct overall X25519 result of zero for the point at
// infinity.

        mov     rbp, res
        mul_p25519(resx,xn,zn)

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

S2N_BN_SIZE_DIRECTIVE(curve25519_x25519)
S2N_BN_SIZE_DIRECTIVE(curve25519_x25519_byte)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
