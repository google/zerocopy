// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Double scalar multiplication for edwards25519, fresh and base point
// Input scalar[4], point[8], bscalar[4]; output res[8]
//
// extern void edwards25519_scalarmuldouble
//   (uint64_t res[static 8],const uint64_t scalar[static 4],
//    const uint64_t point[static 8],const uint64_t bscalar[static 4]);
//
// Given scalar = n, point = P and bscalar = m, returns in res
// the point (X,Y) = n * P + m * B where B = (...,4/5) is
// the standard basepoint for the edwards25519 (Ed25519) curve.
//
// Both 256-bit coordinates of the input point P are implicitly
// reduced modulo 2^255-19 if they are not already in reduced form,
// but the conventional usage is that they *are* already reduced.
// The scalars can be arbitrary 256-bit numbers but may also be
// considered as implicitly reduced modulo the group order.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point, RCX = bscalar
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point, R9 = bscalar
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(edwards25519_scalarmuldouble)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(edwards25519_scalarmuldouble)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(edwards25519_scalarmuldouble)


        .text
        .balign 32

// Size of individual field elements

#define NUMSIZE 32

// Pointer-offset pairs for result and temporaries on stack with some aliasing.
// Both "resx" and "resy" assume the "res" pointer has been preloaded into rbp.

#define resx rbp+(0*NUMSIZE)
#define resy rbp+(1*NUMSIZE)

#define scalar rsp+(0*NUMSIZE)
#define bscalar rsp+(1*NUMSIZE)

#define tabent rsp+(2*NUMSIZE)
#define btabent rsp+(6*NUMSIZE)

#define acc rsp+(9*NUMSIZE)

#define tab rsp+(13*NUMSIZE)

// Additional variables kept on the stack

#define bf QWORD PTR [rsp+45*NUMSIZE]
#define cf QWORD PTR [rsp+45*NUMSIZE+8]
#define i QWORD PTR [rsp+45*NUMSIZE+16]
#define res QWORD PTR [rsp+45*NUMSIZE+24]

// Total size to reserve on the stack (excluding local subroutines)

#define NSPACE 46*NUMSIZE

// Syntactic variants to make x86_att forms easier to generate

#define SCALAR (0*NUMSIZE)
#define BSCALAR (1*NUMSIZE)
#define TABENT (2*NUMSIZE)
#define BTABENT (6*NUMSIZE)
#define ACC (9*NUMSIZE)
#define TAB (13*NUMSIZE)

// Sub-references used in local subroutines with local stack

#define x_0 rdi+0
#define y_0 rdi+NUMSIZE
#define z_0 rdi+(2*NUMSIZE)
#define w_0 rdi+(3*NUMSIZE)

#define x_1 rsi+0
#define y_1 rsi+NUMSIZE
#define z_1 rsi+(2*NUMSIZE)
#define w_1 rsi+(3*NUMSIZE)

#define x_2 rbp+0
#define y_2 rbp+NUMSIZE
#define z_2 rbp+(2*NUMSIZE)
#define w_2 rbp+(3*NUMSIZE)

#define t0 rsp+(0*NUMSIZE)
#define t1 rsp+(1*NUMSIZE)
#define t2 rsp+(2*NUMSIZE)
#define t3 rsp+(3*NUMSIZE)
#define t4 rsp+(4*NUMSIZE)
#define t5 rsp+(5*NUMSIZE)

// Macro wrapping up the basic field multiplication, only trivially
// different from a pure function call to bignum_mul_p25519.

#define mul_p25519(P0,P1,P2)                    \
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
        mov    edx, 0x13;                       \
        inc    r12;                             \
        bts    r11, 63;                         \
        mulx   rbx, rax, r12;                   \
        add    r8, rax;                         \
        adc    r9, rbx;                         \
        adc    r10, rcx;                        \
        adc    r11, rcx;                        \
        sbb    rax, rax;                        \
        not    rax;                             \
        and    rax, rdx;                        \
        sub    r8, rax;                         \
        sbb    r9, rcx;                         \
        sbb    r10, rcx;                        \
        sbb    r11, rcx;                        \
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

// Load the constant k_25519 = 2 * d_25519 using immediate operations

#define load_k25519(P0)                         \
        mov     rax, 0xebd69b9426b2f159;        \
        mov     [P0], rax;                      \
        mov     rax, 0x00e0149a8283b156;        \
        mov     [P0+8], rax;                    \
        mov     rax, 0x198e80f2eef3d130;        \
        mov     [P0+16], rax;                   \
        mov     rax, 0x2406d9dc56dffce7;        \
        mov     [P0+24], rax

S2N_BN_SYMBOL(edwards25519_scalarmuldouble):
        CFI_START
        _CET_ENDBR

// In this case the Windows form literally makes a subroutine call.
// This avoids hassle arising from keeping code and data together.

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        CFI_CALL(Ledwards25519_scalarmuldouble_standard)
        CFI_POP(rsi)
        CFI_POP(rdi)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(edwards25519_scalarmuldouble)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Ledwards25519_scalarmuldouble_standard)

Ledwards25519_scalarmuldouble_standard:
        CFI_START
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

// Copy scalars while recoding all 4-bit nybbles except the top
// one (bits 252..255) into signed 4-bit digits. This is essentially
// done just by adding the recoding constant 0x0888..888, after
// which all digits except the first have an implicit bias of -8,
// so 0 -> -8, 1 -> -7, ... 7 -> -1, 8 -> 0, 9 -> 1, ... 15 -> 7.
// (We could literally create 2s complement signed nybbles by
// XORing with the same constant 0x0888..888 afterwards, but it
// doesn't seem to make the end usage any simpler.)
//
// In order to ensure that the unrecoded top nybble (bits 252..255)
// does not become > 8 as a result of carries lower down from the
// recoding, we first (conceptually) subtract the group order iff
// the top digit of the scalar is > 2^63. In the implementation the
// reduction and recoding are combined by optionally using the
// modified recoding constant 0x0888...888 + (2^256 - group_order).

        mov     r8, [rcx]
        mov     r9, [rcx+8]
        mov     r10, [rcx+16]
        mov     r11, [rcx+24]
        mov     r12, 0xc7f56fb5a0d9e920
        mov     r13, 0xe190b99370cba1d5
        mov     r14, 0x8888888888888887
        mov     r15, 0x8888888888888888
        mov     rax, 0x8000000000000000
        mov     rbx, 0x0888888888888888
        cmp     rax, r11
        cmovnc  r12, r15
        cmovnc  r13, r15
        cmovnc  r14, r15
        cmovnc  r15, rbx
        add     r8, r12
        adc     r9, r13
        adc     r10, r14
        adc     r11, r15
        mov     [rsp+BSCALAR], r8
        mov     [rsp+BSCALAR+8], r9
        mov     [rsp+BSCALAR+16], r10
        mov     [rsp+BSCALAR+24], r11

        mov     r8, [rsi]
        mov     r9, [rsi+8]
        mov     r10, [rsi+16]
        mov     r11, [rsi+24]
        mov     r12, 0xc7f56fb5a0d9e920
        mov     r13, 0xe190b99370cba1d5
        mov     r14, 0x8888888888888887
        mov     r15, 0x8888888888888888
        mov     rax, 0x8000000000000000
        mov     rbx, 0x0888888888888888
        cmp     rax, r11
        cmovnc  r12, r15
        cmovnc  r13, r15
        cmovnc  r14, r15
        cmovnc  r15, rbx
        add     r8, r12
        adc     r9, r13
        adc     r10, r14
        adc     r11, r15
        mov     [rsp+SCALAR], r8
        mov     [rsp+SCALAR+8], r9
        mov     [rsp+SCALAR+16], r10
        mov     [rsp+SCALAR+24], r11

// Create table of multiples 1..8 of the general input point at "tab".
// Reduce the input coordinates x and y modulo 2^256 - 38 first, for the
// sake of definiteness; this is the reduction that will be maintained.
// We could slightly optimize the additions because we know the input
// point is affine (so Z = 1), but it doesn't seem worth the complication.

        mov     eax, 38
        mov     r8, [rdx]
        xor     ebx, ebx
        mov     r9, [rdx+8]
        xor     ecx, ecx
        mov     r10, [rdx+16]
        xor     esi, esi
        mov     r11, [rdx+24]
        add     rax, r8
        adc     rbx, r9
        adc     rcx, r10
        adc     rsi, r11
        cmovnc  rax, r8
        mov     [rsp+TAB], rax
        cmovnc  rbx, r9
        mov     [rsp+TAB+8], rbx
        cmovnc  rcx, r10
        mov     [rsp+TAB+16], rcx
        cmovnc  rsi, r11
        mov     [rsp+TAB+24], rsi

        mov     eax, 38
        mov     r8, [rdx+32]
        xor     ebx, ebx
        mov     r9, [rdx+40]
        xor     ecx, ecx
        mov     r10, [rdx+48]
        xor     esi, esi
        mov     r11, [rdx+56]
        add     rax, r8
        adc     rbx, r9
        adc     rcx, r10
        adc     rsi, r11
        cmovnc  rax, r8
        mov     [rsp+TAB+32], rax
        cmovnc  rbx, r9
        mov     [rsp+TAB+40], rbx
        cmovnc  rcx, r10
        mov     [rsp+TAB+48], rcx
        cmovnc  rsi, r11
        mov     [rsp+TAB+56], rsi

        mov     eax, 1
        mov     [rsp+TAB+64], rax
        xor     eax, eax
        mov     [rsp+TAB+72], rax
        mov     [rsp+TAB+80], rax
        mov     [rsp+TAB+88], rax

        lea     rdi, [rsp+TAB+96]
        lea     rsi, [rsp+TAB]
        lea     rbp, [rsp+TAB+32]
        mul_4(x_0,x_1,x_2)

// Multiple 2

        lea     rdi, [rsp+TAB+1*128]
        lea     rsi, [rsp+TAB]
        CFI_CALL(Ledwards25519_scalarmuldouble_epdouble)

// Multiple 3

        lea     rdi, [rsp+TAB+2*128]
        lea     rsi, [rsp+TAB]
        lea     rbp, [rsp+TAB+1*128]
        CFI_CALL(Ledwards25519_scalarmuldouble_epadd)

// Multiple 4

        lea     rdi, [rsp+TAB+3*128]
        lea     rsi, [rsp+TAB+1*128]
        CFI_CALL(Ledwards25519_scalarmuldouble_epdouble)

// Multiple 5

        lea     rdi, [rsp+TAB+4*128]
        lea     rsi, [rsp+TAB]
        lea     rbp, [rsp+TAB+3*128]
        CFI_CALL(Ledwards25519_scalarmuldouble_epadd)

// Multiple 6

        lea     rdi, [rsp+TAB+5*128]
        lea     rsi, [rsp+TAB+2*128]
        CFI_CALL(Ledwards25519_scalarmuldouble_epdouble)

// Multiple 7

        lea     rdi, [rsp+TAB+6*128]
        lea     rsi, [rsp+TAB]
        lea     rbp, [rsp+TAB+5*128]
        CFI_CALL(Ledwards25519_scalarmuldouble_epadd)

// Multiple 8

        lea     rdi, [rsp+TAB+7*128]
        lea     rsi, [rsp+TAB+3*128]
        CFI_CALL(Ledwards25519_scalarmuldouble_epdouble)

// Handle the initialization, starting the loop counter at i = 252
// and initializing acc to the sum of the table entries for the
// top nybbles of the scalars (the ones with no implicit -8 bias).

        mov     rax, 252
        mov     i, rax

// Index for btable entry...

        mov     rax, [rsp+BSCALAR+24]
        shr     rax, 60
        mov     bf, rax

// ...and constant-time indexing based on that index

        mov     eax, 1
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        mov     r8d, 1
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        xor     r13d, r13d
        xor     r14d, r14d
        xor     r15d, r15d

        lea     rbp, [rip+S2N_BN_SYMBOL(edwards25519_scalarmuldouble_constant)]

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi

        mov     [rsp+BTABENT], rax
        mov     [rsp+BTABENT+8], rbx
        mov     [rsp+BTABENT+16], rcx
        mov     [rsp+BTABENT+24], rdx
        mov     [rsp+BTABENT+32], r8
        mov     [rsp+BTABENT+40], r9
        mov     [rsp+BTABENT+48], r10
        mov     [rsp+BTABENT+56], r11
        mov     [rsp+BTABENT+64], r12
        mov     [rsp+BTABENT+72], r13
        mov     [rsp+BTABENT+80], r14
        mov     [rsp+BTABENT+88], r15

// Index for table entry...

        mov     rax, [rsp+SCALAR+24]
        shr     rax, 60
        mov     bf, rax

// ...and constant-time indexing based on that index.
// Do the Y and Z fields first, to save on registers...

        mov     eax, 1
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        mov     r8d, 1
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d

        lea     rbp, [rsp+TAB+32]

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi

        mov     [rsp+TABENT+32], rax
        mov     [rsp+TABENT+40], rbx
        mov     [rsp+TABENT+48], rcx
        mov     [rsp+TABENT+56], rdx
        mov     [rsp+TABENT+64], r8
        mov     [rsp+TABENT+72], r9
        mov     [rsp+TABENT+80], r10
        mov     [rsp+TABENT+88], r11

// ...followed by the X and W fields

        lea     rbp, [rsp+TAB]

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi

        mov     [rsp+TABENT], rax
        mov     [rsp+TABENT+8], rbx
        mov     [rsp+TABENT+16], rcx
        mov     [rsp+TABENT+24], rdx
        mov     [rsp+TABENT+96], r8
        mov     [rsp+TABENT+104], r9
        mov     [rsp+TABENT+112], r10
        mov     [rsp+TABENT+120], r11

// Add those elements to initialize the accumulator for bit position 252

        lea     rdi, [rsp+ACC]
        lea     rsi, [rsp+TABENT]
        lea     rbp, [rsp+BTABENT]
        CFI_CALL(Ledwards25519_scalarmuldouble_pepadd)

// Main loop with acc = [scalar/2^i] * point + [bscalar/2^i] * basepoint
// Start with i = 252 for bits 248..251 and go down four at a time to 3..0

Ledwards25519_scalarmuldouble_loop:

        mov     rax, i
        sub     rax, 4
        mov     i, rax

// Double to acc' = 2 * acc

        lea     rdi, [rsp+ACC]
        lea     rsi, [rsp+ACC]
        CFI_CALL(Ledwards25519_scalarmuldouble_pdouble)

// Get btable entry, first getting the adjusted bitfield...

        mov     rax, i
        mov     rcx, rax
        shr     rax, 6
        mov     rax, [rsp+8*rax+32]
        shr     rax, cl
        and     rax, 15

        sub     rax, 8
        sbb     rcx, rcx
        xor     rax, rcx
        sub     rax, rcx
        mov     cf, rcx
        mov     bf, rax

// ... then doing constant-time lookup with the appropriate index...

        mov     eax, 1
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        mov     r8d, 1
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        xor     r13d, r13d
        xor     r14d, r14d
        xor     r15d, r15d

        lea     rbp, [rip+S2N_BN_SYMBOL(edwards25519_scalarmuldouble_constant)]

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi
        add     rbp, 96

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        mov     rsi, [rbp+64]
        cmovz   r12, rsi
        mov     rsi, [rbp+72]
        cmovz   r13, rsi
        mov     rsi, [rbp+80]
        cmovz   r14, rsi
        mov     rsi, [rbp+88]
        cmovz   r15, rsi

// ... then optionally negating before storing. The table entry
// is in precomputed form and we currently have
//
//      [rdx;rcx;rbx;rax] = y - x
//      [r11;r10;r9;r8] = x + y
//      [r15;r14;r13;r12] = 2 * d * x * y
//
// Negation for Edwards curves is -(x,y) = (-x,y), which in this modified
// form amounts to swapping the first two fields and negating the third.
// The negation does not always fully reduce even mod 2^256-38 in the zero
// case, instead giving -0 = 2^256-38. But that is fine since the result is
// always fed to a multiplication inside the "pepadd" function below that
// handles any 256-bit input.

        mov     rdi, cf
        test    rdi, rdi

        mov     rsi, rax
        cmovnz  rsi, r8
        cmovnz  r8, rax
        mov     [rsp+BTABENT], rsi
        mov     [rsp+BTABENT+32], r8

        mov     rsi, rbx
        cmovnz  rsi, r9
        cmovnz  r9, rbx
        mov     [rsp+BTABENT+8], rsi
        mov     [rsp+BTABENT+40], r9

        mov     rsi, rcx
        cmovnz  rsi, r10
        cmovnz  r10, rcx
        mov     [rsp+BTABENT+16], rsi
        mov     [rsp+BTABENT+48], r10

        mov     rsi, rdx
        cmovnz  rsi, r11
        cmovnz  r11, rdx
        mov     [rsp+BTABENT+24], rsi
        mov     [rsp+BTABENT+56], r11

        xor     r12, rdi
        xor     r13, rdi
        xor     r14, rdi
        xor     r15, rdi
        and     rdi, 37
        sub     r12, rdi
        sbb     r13, 0
        sbb     r14, 0
        sbb     r15, 0
        mov     [rsp+BTABENT+64], r12
        mov     [rsp+BTABENT+72], r13
        mov     [rsp+BTABENT+80], r14
        mov     [rsp+BTABENT+88], r15

// Get table entry, first getting the adjusted bitfield...

        mov     rax, i
        mov     rcx, rax
        shr     rax, 6
        mov     rax, [rsp+8*rax]
        shr     rax, cl
        and     rax, 15

        sub     rax, 8
        sbb     rcx, rcx
        xor     rax, rcx
        sub     rax, rcx
        mov     cf, rcx
        mov     bf, rax

// ...and constant-time indexing based on that index
// Do the Y and Z fields first, to save on registers
// and store them back (they don't need any modification)

        mov     eax, 1
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        mov     r8d, 1
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d

        lea     rbp, [rsp+TAB+32]

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+32]
        cmovz   r8, rsi
        mov     rsi, [rbp+40]
        cmovz   r9, rsi
        mov     rsi, [rbp+48]
        cmovz   r10, rsi
        mov     rsi, [rbp+56]
        cmovz   r11, rsi

        mov     [rsp+TABENT+32], rax
        mov     [rsp+TABENT+40], rbx
        mov     [rsp+TABENT+48], rcx
        mov     [rsp+TABENT+56], rdx
        mov     [rsp+TABENT+64], r8
        mov     [rsp+TABENT+72], r9
        mov     [rsp+TABENT+80], r10
        mov     [rsp+TABENT+88], r11

// Now do the X and W fields...

        lea     rbp, [rsp+TAB]

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d

        cmp     bf, 1
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 2
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 3
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 4
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 5
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 6
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 7
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi
        add     rbp, 128

        cmp     bf, 8
        mov     rsi, [rbp]
        cmovz   rax, rsi
        mov     rsi, [rbp+8]
        cmovz   rbx, rsi
        mov     rsi, [rbp+16]
        cmovz   rcx, rsi
        mov     rsi, [rbp+24]
        cmovz   rdx, rsi
        mov     rsi, [rbp+96]
        cmovz   r8, rsi
        mov     rsi, [rbp+104]
        cmovz   r9, rsi
        mov     rsi, [rbp+112]
        cmovz   r10, rsi
        mov     rsi, [rbp+120]
        cmovz   r11, rsi

// ... then optionally negate before storing the X and W fields. This
// time the table entry is extended-projective, and is here:
//
//      [rdx;rcx;rbx;rax] = X
//      [tabent+32] = Y
//      [tabent+64] = Z
//      [r11;r10;r9;r8] = W
//
// This time we just need to negate the X and the W fields.
// The crude way negation is done can result in values of X or W
// (when initially zero before negation) being exactly equal to
// 2^256-38, but the "pepadd" function handles that correctly.

        mov     rdi, cf

        xor     rax, rdi
        xor     rbx, rdi
        xor     rcx, rdi
        xor     rdx, rdi

        xor     r8, rdi
        xor     r9, rdi
        xor     r10, rdi
        xor     r11, rdi

        and     rdi, 37

        sub     rax, rdi
        sbb     rbx, 0
        sbb     rcx, 0
        sbb     rdx, 0

        mov     [rsp+TABENT], rax
        mov     [rsp+TABENT+8], rbx
        mov     [rsp+TABENT+16], rcx
        mov     [rsp+TABENT+24], rdx

        sub     r8, rdi
        sbb     r9, 0
        sbb     r10, 0
        sbb     r11, 0

        mov     [rsp+TABENT+96], r8
        mov     [rsp+TABENT+104], r9
        mov     [rsp+TABENT+112], r10
        mov     [rsp+TABENT+120], r11

// Double to acc' = 4 * acc

        lea     rdi, [rsp+ACC]
        lea     rsi, [rsp+ACC]
        CFI_CALL(Ledwards25519_scalarmuldouble_pdouble)

// Add tabent := tabent + btabent

        lea     rdi, [rsp+TABENT]
        lea     rsi, [rsp+TABENT]
        lea     rbp, [rsp+BTABENT]
        CFI_CALL(Ledwards25519_scalarmuldouble_pepadd)

// Double to acc' = 8 * acc

        lea     rdi, [rsp+ACC]
        lea     rsi, [rsp+ACC]
        CFI_CALL(Ledwards25519_scalarmuldouble_pdouble)

// Double to acc' = 16 * acc

        lea     rdi, [rsp+ACC]
        lea     rsi, [rsp+ACC]
        CFI_CALL(Ledwards25519_scalarmuldouble_epdouble)

// Add table entry, acc := acc + tabent

        lea     rdi, [rsp+ACC]
        lea     rsi, [rsp+ACC]
        lea     rbp, [rsp+TABENT]
        CFI_CALL(Ledwards25519_scalarmuldouble_epadd)

// Loop down

        mov     rax, i
        test    rax, rax
        jnz     Ledwards25519_scalarmuldouble_loop

// Prepare to call the modular inverse function to get tab = 1/z

        lea     rdi, [rsp+TAB]
        lea     rsi, [rsp+ACC+64]

// Inline copy of bignum_inv_p25519, identical except for stripping out
// the prologue and epilogue saving and restoring registers and making
// and reclaiming room on the stack. For more details and explanations see
// "x86/curve25519/bignum_inv_p25519.S". Note that the stack it uses for
// its own temporaries is 208 bytes, so it has no effect on variables
// that are needed in the rest of our computation here: res, tab and acc.

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
        jmp     Ledwards25519_scalarmuldouble_midloop
Ledwards25519_scalarmuldouble_inverseloop:
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
Ledwards25519_scalarmuldouble_midloop:
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
        jne     Ledwards25519_scalarmuldouble_inverseloop
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

// Store result

        mov     rdi, res
        lea     rsi, [rsp+ACC]
        lea     rbp, [rsp+TAB]
        mul_p25519(x_0,x_1,x_2)

        mov     rdi, res
        add     rdi, 32
        lea     rsi, [rsp+ACC+32]
        lea     rbp, [rsp+TAB]
        mul_p25519(x_0,x_1,x_2)

// Restore stack and registers

        CFI_INC_RSP(NSPACE)

        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

#if WINDOWS_ABI
S2N_BN_SIZE_DIRECTIVE(Ledwards25519_scalarmuldouble_standard)
#else
S2N_BN_SIZE_DIRECTIVE(edwards25519_scalarmuldouble)
#endif

// ****************************************************************************
// Localized versions of subroutines.
// These are close to the standalone functions "edwards25519_epdouble" etc.,
// but are only maintaining reduction modulo 2^256 - 38, not 2^255 - 19.
// ****************************************************************************

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Ledwards25519_scalarmuldouble_epdouble)

Ledwards25519_scalarmuldouble_epdouble:
        CFI_START
        CFI_DEC_RSP(5*NUMSIZE)
        add_twice4(t0,x_1,y_1)
        sqr_4(t1,z_1)
        sqr_4(t2,x_1)
        sqr_4(t3,y_1)
        double_twice4(t1,t1)
        sqr_4(t0,t0)
        add_twice4(t4,t2,t3)
        sub_twice4(t2,t2,t3)
        add_twice4(t3,t1,t2)
        sub_twice4(t1,t4,t0)
        mul_4(y_0,t2,t4)
        mul_4(z_0,t3,t2)
        mul_4(w_0,t1,t4)
        mul_4(x_0,t1,t3)
        CFI_INC_RSP(5*NUMSIZE)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Ledwards25519_scalarmuldouble_epdouble)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Ledwards25519_scalarmuldouble_pdouble)

Ledwards25519_scalarmuldouble_pdouble:
        CFI_START
        CFI_DEC_RSP(5*NUMSIZE)
        add_twice4(t0,x_1,y_1)
        sqr_4(t1,z_1)
        sqr_4(t2,x_1)
        sqr_4(t3,y_1)
        double_twice4(t1,t1)
        sqr_4(t0,t0)
        add_twice4(t4,t2,t3)
        sub_twice4(t2,t2,t3)
        add_twice4(t3,t1,t2)
        sub_twice4(t1,t4,t0)
        mul_4(y_0,t2,t4)
        mul_4(z_0,t3,t2)
        mul_4(x_0,t1,t3)
        CFI_INC_RSP(5*NUMSIZE)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Ledwards25519_scalarmuldouble_pdouble)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Ledwards25519_scalarmuldouble_epadd)

Ledwards25519_scalarmuldouble_epadd:
        CFI_START
        CFI_DEC_RSP(6*NUMSIZE)
        mul_4(t0,w_1,w_2)
        sub_twice4(t1,y_1,x_1)
        sub_twice4(t2,y_2,x_2)
        add_twice4(t3,y_1,x_1)
        add_twice4(t4,y_2,x_2)
        double_twice4(t5,z_2)
        mul_4(t1,t1,t2)
        mul_4(t3,t3,t4)
        load_k25519(t2)
        mul_4(t2,t2,t0)
        mul_4(t4,z_1,t5)
        sub_twice4(t0,t3,t1)
        add_twice4(t5,t3,t1)
        sub_twice4(t1,t4,t2)
        add_twice4(t3,t4,t2)
        mul_4(w_0,t0,t5)
        mul_4(x_0,t0,t1)
        mul_4(y_0,t3,t5)
        mul_4(z_0,t1,t3)
        CFI_INC_RSP(6*NUMSIZE)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Ledwards25519_scalarmuldouble_epadd)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Ledwards25519_scalarmuldouble_pepadd)

Ledwards25519_scalarmuldouble_pepadd:
        CFI_START
        CFI_DEC_RSP(6*NUMSIZE)
        double_twice4(t0,z_1);
        sub_twice4(t1,y_1,x_1);
        add_twice4(t2,y_1,x_1);
        mul_4(t3,w_1,z_2);
        mul_4(t1,t1,x_2);
        mul_4(t2,t2,y_2);
        sub_twice4(t4,t0,t3);
        add_twice4(t0,t0,t3);
        sub_twice4(t5,t2,t1);
        add_twice4(t1,t2,t1);
        mul_4(z_0,t4,t0);
        mul_4(x_0,t5,t4);
        mul_4(y_0,t0,t1);
        mul_4(w_0,t5,t1);
        CFI_INC_RSP(6*NUMSIZE)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Ledwards25519_scalarmuldouble_pepadd)

S2N_BN_SIZE_DIRECTIVE(edwards25519_scalarmuldouble)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif

// ****************************************************************************
// The precomputed data (all read-only).
// ****************************************************************************

#if defined(__ELF__)
.section .rodata
.type S2N_BN_SYMBOL(edwards25519_scalarmuldouble_constant), %object
.size S2N_BN_SYMBOL(edwards25519_scalarmuldouble_constant), 768
#elif defined(__APPLE__)
.const_data
#endif

// Precomputed table of multiples of generator for edwards25519
// all in precomputed extended-projective (y-x,x+y,2*d*x*y) triples.

S2N_BN_SYMBOL(edwards25519_scalarmuldouble_constant):

        // 1 * G

        .quad   0x9d103905d740913e
        .quad   0xfd399f05d140beb3
        .quad   0xa5c18434688f8a09
        .quad   0x44fd2f9298f81267
        .quad   0x2fbc93c6f58c3b85
        .quad   0xcf932dc6fb8c0e19
        .quad   0x270b4898643d42c2
        .quad   0x07cf9d3a33d4ba65
        .quad   0xabc91205877aaa68
        .quad   0x26d9e823ccaac49e
        .quad   0x5a1b7dcbdd43598c
        .quad   0x6f117b689f0c65a8

        // 2 * G

        .quad   0x8a99a56042b4d5a8
        .quad   0x8f2b810c4e60acf6
        .quad   0xe09e236bb16e37aa
        .quad   0x6bb595a669c92555
        .quad   0x9224e7fc933c71d7
        .quad   0x9f469d967a0ff5b5
        .quad   0x5aa69a65e1d60702
        .quad   0x590c063fa87d2e2e
        .quad   0x43faa8b3a59b7a5f
        .quad   0x36c16bdd5d9acf78
        .quad   0x500fa0840b3d6a31
        .quad   0x701af5b13ea50b73

        // 3 * G

        .quad   0x56611fe8a4fcd265
        .quad   0x3bd353fde5c1ba7d
        .quad   0x8131f31a214bd6bd
        .quad   0x2ab91587555bda62
        .quad   0xaf25b0a84cee9730
        .quad   0x025a8430e8864b8a
        .quad   0xc11b50029f016732
        .quad   0x7a164e1b9a80f8f4
        .quad   0x14ae933f0dd0d889
        .quad   0x589423221c35da62
        .quad   0xd170e5458cf2db4c
        .quad   0x5a2826af12b9b4c6

        // 4 * G

        .quad   0x95fe050a056818bf
        .quad   0x327e89715660faa9
        .quad   0xc3e8e3cd06a05073
        .quad   0x27933f4c7445a49a
        .quad   0x287351b98efc099f
        .quad   0x6765c6f47dfd2538
        .quad   0xca348d3dfb0a9265
        .quad   0x680e910321e58727
        .quad   0x5a13fbe9c476ff09
        .quad   0x6e9e39457b5cc172
        .quad   0x5ddbdcf9102b4494
        .quad   0x7f9d0cbf63553e2b

        // 5 * G

        .quad   0x7f9182c3a447d6ba
        .quad   0xd50014d14b2729b7
        .quad   0xe33cf11cb864a087
        .quad   0x154a7e73eb1b55f3
        .quad   0xa212bc4408a5bb33
        .quad   0x8d5048c3c75eed02
        .quad   0xdd1beb0c5abfec44
        .quad   0x2945ccf146e206eb
        .quad   0xbcbbdbf1812a8285
        .quad   0x270e0807d0bdd1fc
        .quad   0xb41b670b1bbda72d
        .quad   0x43aabe696b3bb69a

        // 6 * G

        .quad   0x499806b67b7d8ca4
        .quad   0x575be28427d22739
        .quad   0xbb085ce7204553b9
        .quad   0x38b64c41ae417884
        .quad   0x3a0ceeeb77157131
        .quad   0x9b27158900c8af88
        .quad   0x8065b668da59a736
        .quad   0x51e57bb6a2cc38bd
        .quad   0x85ac326702ea4b71
        .quad   0xbe70e00341a1bb01
        .quad   0x53e4a24b083bc144
        .quad   0x10b8e91a9f0d61e3

        // 7 * G

        .quad   0xba6f2c9aaa3221b1
        .quad   0x6ca021533bba23a7
        .quad   0x9dea764f92192c3a
        .quad   0x1d6edd5d2e5317e0
        .quad   0x6b1a5cd0944ea3bf
        .quad   0x7470353ab39dc0d2
        .quad   0x71b2528228542e49
        .quad   0x461bea69283c927e
        .quad   0xf1836dc801b8b3a2
        .quad   0xb3035f47053ea49a
        .quad   0x529c41ba5877adf3
        .quad   0x7a9fbb1c6a0f90a7

        // 8 * G

        .quad   0xe2a75dedf39234d9
        .quad   0x963d7680e1b558f9
        .quad   0x2c2741ac6e3c23fb
        .quad   0x3a9024a1320e01c3
        .quad   0x59b7596604dd3e8f
        .quad   0x6cb30377e288702c
        .quad   0xb1339c665ed9c323
        .quad   0x0915e76061bce52f
        .quad   0xe7c1f5d9c9a2911a
        .quad   0xb8a371788bcca7d7
        .quad   0x636412190eb62a32
        .quad   0x26907c5c2ecc4e95
