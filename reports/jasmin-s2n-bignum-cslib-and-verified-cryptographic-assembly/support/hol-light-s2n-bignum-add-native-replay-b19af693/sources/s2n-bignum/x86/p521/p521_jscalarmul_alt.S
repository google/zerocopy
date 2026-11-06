// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Jacobian form scalar multiplication for P-521
// Input scalar[9], point[27]; output res[27]
//
// extern void p521_jscalarmul_alt
//   (uint64_t res[static 27],
//    const uint64_t scalar[static 9],
//    const uint64_t point[static 27]);
//
// This function is a variant of its affine point version p521_scalarmul.
// Here, input and output points are assumed to be in Jacobian form with
// a triple (x,y,z) representing the affine point (x/z^2,y/z^3) when
// z is nonzero or the point at infinity (group identity) if z = 0.
//
// Given scalar = n and point = P, assumed to be on the NIST elliptic
// curve P-521, returns a representation of n * P. If the result is the
// point at infinity (either because the input point was or because the
// scalar was a multiple of p_521) then the output is guaranteed to
// represent the point at infinity, i.e. to have its z coordinate zero.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p521_jscalarmul_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p521_jscalarmul_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p521_jscalarmul_alt)


        .text
        .balign 32

// Size of individual field elements

#define NUMSIZE 72
#define JACSIZE (3*NUMSIZE)

// Intermediate variables on the stack.
// The table is 16 entries, each of size JACSIZE = 3 * NUMSIZE
// Uppercase syntactic variants make x86_att version simpler to generate.

#define SCALARB (0*NUMSIZE)
#define scalarb rsp+(0*NUMSIZE)
#define ACC (1*NUMSIZE)
#define acc rsp+(1*NUMSIZE)
#define TABENT (4*NUMSIZE)
#define tabent rsp+(4*NUMSIZE)

#define TAB (7*NUMSIZE)
#define tab rsp+(7*NUMSIZE)

#define res [rsp+(55*NUMSIZE)]

#define NSPACE 56*NUMSIZE

// Avoid using .rep for the sake of the BoringSSL/AWS-LC delocator,
// which doesn't accept repetitions, assembler macros etc.

#define selectblock(I,C)                                        \
        cmp     rdi, I;                                         \
        cmovz   rax, [rsp+TAB+JACSIZE*(I-1)+C*NUMSIZE];         \
        cmovz   rbx, [rsp+TAB+JACSIZE*(I-1)+8+C*NUMSIZE];       \
        cmovz   rcx, [rsp+TAB+JACSIZE*(I-1)+16+C*NUMSIZE];      \
        cmovz   rdx, [rsp+TAB+JACSIZE*(I-1)+24+C*NUMSIZE];      \
        cmovz   r8, [rsp+TAB+JACSIZE*(I-1)+32+C*NUMSIZE];       \
        cmovz   r9, [rsp+TAB+JACSIZE*(I-1)+40+C*NUMSIZE];       \
        cmovz   r10, [rsp+TAB+JACSIZE*(I-1)+48+C*NUMSIZE];      \
        cmovz   r11, [rsp+TAB+JACSIZE*(I-1)+56+C*NUMSIZE];      \
        cmovz   r12, [rsp+TAB+JACSIZE*(I-1)+64+C*NUMSIZE]

S2N_BN_SYMBOL(p521_jscalarmul_alt):
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
        CFI_CALL(Lp521_jscalarmul_alt_standard)
        CFI_POP(rsi)
        CFI_POP(rdi)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(p521_jscalarmul_alt)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp521_jscalarmul_alt_standard)

Lp521_jscalarmul_alt_standard:
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

// Preserve the "res" input argument; others get processed early.

        mov     res, rdi

// Reduce the input scalar mod n_521 and store it to "scalarb".

        mov     rbx, rdx
        lea     rdi, [rsp+SCALARB]
        CFI_CALL(Lp521_jscalarmul_alt_bignum_mod_n521_9)

// Set the tab[0] table entry to the input point = 1 * P, but also
// reduce all coordinates modulo p. In principle we assume reduction
// as a precondition, but this reduces the scope for surprise, e.g.
// making sure that any input with z = 0 is treated as zero, even
// if the other coordinates are not in fact reduced.

        lea     rdi, [rsp+TAB]
        mov     rsi, rbx
        CFI_CALL(Lp521_jscalarmul_alt_bignum_mod_p521_9)

        lea     rdi, [rsp+TAB+NUMSIZE]
        lea     rsi, [rbx+NUMSIZE]
        CFI_CALL(Lp521_jscalarmul_alt_bignum_mod_p521_9)

        lea     rdi, [rsp+TAB+2*NUMSIZE]
        lea     rsi, [rbx+2*NUMSIZE]
        CFI_CALL(Lp521_jscalarmul_alt_bignum_mod_p521_9)

// If bit 520 of the scalar is set, then negate the scalar mod n_521,
// i.e. do scalar |-> n_521 - scalar, and also the point to compensate
// by negating its y coordinate. This further step is not needed by
// the indexing scheme (the top window is only a couple of bits either
// way), but is convenient to exclude a problem with the specific value
// scalar = n_521 - 18, where the last Jacobian addition is of the form
// (n_521 - 9) * P + -(9 * P) and hence is a degenerate doubling case.

        xor     eax, eax
        not     rax
        mov     r8, 0xbb6fb71e91386409
        sub     r8, [rsp+SCALARB]
        mov     r9, 0x3bb5c9b8899c47ae
        sbb     r9, [rsp+SCALARB+8]
        mov     r10, 0x7fcc0148f709a5d0
        sbb     r10, [rsp+SCALARB+16]
        mov     r11, 0x51868783bf2f966b
        sbb     r11, [rsp+SCALARB+24]
        lea     r12, [rax-5]
        sbb     r12, [rsp+SCALARB+32]
        mov     r13, rax
        sbb     r13, [rsp+SCALARB+40]
        mov     r14, rax
        sbb     r14, [rsp+SCALARB+48]
        mov     r15, rax
        sbb     r15, [rsp+SCALARB+56]
        mov     rax, 0x1ff
        mov     rcx, [rsp+SCALARB+64]
        sbb     rax, rcx

        bt      rcx, 8
        sbb     rcx, rcx

        cmovnc  r8, [rsp+SCALARB]
        cmovnc  r9, [rsp+SCALARB+8]
        cmovnc  r10, [rsp+SCALARB+16]
        cmovnc  r11, [rsp+SCALARB+24]
        cmovnc  r12, [rsp+SCALARB+32]
        cmovnc  r13, [rsp+SCALARB+40]
        cmovnc  r14, [rsp+SCALARB+48]
        cmovnc  r15, [rsp+SCALARB+56]
        cmovnc  rax, [rsp+SCALARB+64]

        mov     [rsp+SCALARB], r8
        mov     [rsp+SCALARB+8], r9
        mov     [rsp+SCALARB+16], r10
        mov     [rsp+SCALARB+24], r11
        mov     [rsp+SCALARB+32], r12
        mov     [rsp+SCALARB+40], r13
        mov     [rsp+SCALARB+48], r14
        mov     [rsp+SCALARB+56], r15
        mov     [rsp+SCALARB+64], rax

        mov     r8, [rsp+TAB+NUMSIZE]
        mov     r9, [rsp+TAB+NUMSIZE+8]
        mov     r10, [rsp+TAB+NUMSIZE+16]
        mov     r11, [rsp+TAB+NUMSIZE+24]
        mov     r12, [rsp+TAB+NUMSIZE+32]
        mov     r13, [rsp+TAB+NUMSIZE+40]
        mov     r14, [rsp+TAB+NUMSIZE+48]
        mov     r15, [rsp+TAB+NUMSIZE+56]
        mov     rax, [rsp+TAB+NUMSIZE+64]

        mov     rbx, r8
        mov     rbp, r12
        or      rbx, r9
        or      rbp, r13
        or      rbx, r10
        or      rbp, r14
        or      rbx, r11
        or      rbp, r15
        or      rbx, rbp
        or      rbx, rax
        cmovz   rcx, rbx

        xor     r8, rcx
        xor     r9, rcx
        xor     r10, rcx
        xor     r11, rcx
        xor     r12, rcx
        xor     r13, rcx
        xor     r14, rcx
        xor     r15, rcx
        and     rcx, 0x1FF
        xor     rax, rcx

        mov     [rsp+TAB+NUMSIZE], r8
        mov     [rsp+TAB+NUMSIZE+8], r9
        mov     [rsp+TAB+NUMSIZE+16], r10
        mov     [rsp+TAB+NUMSIZE+24], r11
        mov     [rsp+TAB+NUMSIZE+32], r12
        mov     [rsp+TAB+NUMSIZE+40], r13
        mov     [rsp+TAB+NUMSIZE+48], r14
        mov     [rsp+TAB+NUMSIZE+56], r15
        mov     [rsp+TAB+NUMSIZE+64], rax

// Compute and record tab[1] = 2 * p, ..., tab[15] = 16 * P

        lea     rdi, [rsp+TAB+JACSIZE*1]
        lea     rsi, [rsp+TAB]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rdi, [rsp+TAB+JACSIZE*2]
        lea     rsi, [rsp+TAB+JACSIZE*1]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp521_jscalarmul_alt_jadd)

        lea     rdi, [rsp+TAB+JACSIZE*3]
        lea     rsi, [rsp+TAB+JACSIZE*1]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rdi, [rsp+TAB+JACSIZE*4]
        lea     rsi, [rsp+TAB+JACSIZE*3]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp521_jscalarmul_alt_jadd)

        lea     rdi, [rsp+TAB+JACSIZE*5]
        lea     rsi, [rsp+TAB+JACSIZE*2]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rdi, [rsp+TAB+JACSIZE*6]
        lea     rsi, [rsp+TAB+JACSIZE*5]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp521_jscalarmul_alt_jadd)

        lea     rdi, [rsp+TAB+JACSIZE*7]
        lea     rsi, [rsp+TAB+JACSIZE*3]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rdi, [rsp+TAB+JACSIZE*8]
        lea     rsi, [rsp+TAB+JACSIZE*7]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp521_jscalarmul_alt_jadd)

        lea     rdi, [rsp+TAB+JACSIZE*9]
        lea     rsi, [rsp+TAB+JACSIZE*4]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rdi, [rsp+TAB+JACSIZE*10]
        lea     rsi, [rsp+TAB+JACSIZE*9]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp521_jscalarmul_alt_jadd)

        lea     rdi, [rsp+TAB+JACSIZE*11]
        lea     rsi, [rsp+TAB+JACSIZE*5]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rdi, [rsp+TAB+JACSIZE*12]
        lea     rsi, [rsp+TAB+JACSIZE*11]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp521_jscalarmul_alt_jadd)

        lea     rdi, [rsp+TAB+JACSIZE*13]
        lea     rsi, [rsp+TAB+JACSIZE*6]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rdi, [rsp+TAB+JACSIZE*14]
        lea     rsi, [rsp+TAB+JACSIZE*13]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp521_jscalarmul_alt_jadd)

        lea     rdi, [rsp+TAB+JACSIZE*15]
        lea     rsi, [rsp+TAB+JACSIZE*7]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

// Add the recoding constant sum_i(16 * 32^i) to the scalar to allow signed
// digits. The digits of the constant, in lowest-to-highest order, are as
// follows; they are generated dynamically to use fewer large constant loads.
//
// 0x0842108421084210 rax
// 0x1084210842108421 rbx
// 0x2108421084210842 rbx<<1
// 0x4210842108421084 rbx<<2
// 0x8421084210842108 rbx<<3
// 0x0842108421084210 rax
// 0x1084210842108421 rbx
// 0x2108421084210842 rbx<<1
// 0x0000000000000084

        mov     rax, 0x1084210842108421
        mov     rbx, rax
        shr     rax, 1
        mov     r8, [rsp+SCALARB]
        add     r8, rax
        mov     r9, [rsp+SCALARB+8]
        adc     r9, rbx
        lea     rcx, [rbx+rbx]
        mov     r10, [rsp+SCALARB+16]
        adc     r10, rcx
        lea     rcx, [rcx+rcx]
        mov     r11, [rsp+SCALARB+24]
        adc     r11, rcx
        lea     rcx, [rcx+rcx]
        mov     r12, [rsp+SCALARB+32]
        adc     r12, rcx
        mov     r13, [rsp+SCALARB+40]
        adc     r13, rax
        mov     r14, [rsp+SCALARB+48]
        adc     r14, rbx
        mov     r15, [rsp+SCALARB+56]
        lea     rcx, [rbx+rbx]
        adc     r15, rcx
        mov     rax, [rsp+SCALARB+64]
        adc     rax, 0x84

// Because of the initial reduction the top bitfield (>= bits 520) is <= 1,
// i.e. just a single bit. Record that in rdi, then shift the whole
// scalar left 56 bits to align the top of the next bitfield with the MSB
// (bits 571..575).

        mov     rdi, rax
        shr     rdi, 8
        shld    rax, r15, 56
        shld    r15, r14, 56
        shld    r14, r13, 56
        shld    r13, r12, 56
        shld    r12, r11, 56
        shld    r11, r10, 56
        shld    r10, r9, 56
        shld    r9, r8, 56
        shl     r8, 56

        mov     [rsp+SCALARB], r8
        mov     [rsp+SCALARB+8], r9
        mov     [rsp+SCALARB+16], r10
        mov     [rsp+SCALARB+24], r11
        mov     [rsp+SCALARB+32], r12
        mov     [rsp+SCALARB+40], r13
        mov     [rsp+SCALARB+48], r14
        mov     [rsp+SCALARB+56], r15
        mov     [rsp+SCALARB+64], rax

// According to the top bit, initialize the accumulator to P or 0. This top
// digit, uniquely, is not recoded so there is no sign adjustment to make.
// We only really need to adjust the z coordinate to zero, but do all three.

        xor     ecx, ecx
        test    rdi, rdi

        mov     rax, [rsp+TAB]
        cmovz   rax, rcx
        mov     [rsp+ACC], rax
        mov     rax, [rsp+TAB+8]
        cmovz   rax, rcx
        mov     [rsp+ACC+8], rax
        mov     rax, [rsp+TAB+16]
        cmovz   rax, rcx
        mov     [rsp+ACC+16], rax
        mov     rax, [rsp+TAB+24]
        cmovz   rax, rcx
        mov     [rsp+ACC+24], rax
        mov     rax, [rsp+TAB+32]
        cmovz   rax, rcx
        mov     [rsp+ACC+32], rax
        mov     rax, [rsp+TAB+40]
        cmovz   rax, rcx
        mov     [rsp+ACC+40], rax
        mov     rax, [rsp+TAB+48]
        cmovz   rax, rcx
        mov     [rsp+ACC+48], rax
        mov     rax, [rsp+TAB+56]
        cmovz   rax, rcx
        mov     [rsp+ACC+56], rax
        mov     rax, [rsp+TAB+64]
        cmovz   rax, rcx
        mov     [rsp+ACC+64], rax
        mov     rax, [rsp+TAB+72]
        cmovz   rax, rcx
        mov     [rsp+ACC+72], rax
        mov     rax, [rsp+TAB+80]
        cmovz   rax, rcx
        mov     [rsp+ACC+80], rax
        mov     rax, [rsp+TAB+88]
        cmovz   rax, rcx
        mov     [rsp+ACC+88], rax
        mov     rax, [rsp+TAB+96]
        cmovz   rax, rcx
        mov     [rsp+ACC+96], rax
        mov     rax, [rsp+TAB+104]
        cmovz   rax, rcx
        mov     [rsp+ACC+104], rax
        mov     rax, [rsp+TAB+112]
        cmovz   rax, rcx
        mov     [rsp+ACC+112], rax
        mov     rax, [rsp+TAB+120]
        cmovz   rax, rcx
        mov     [rsp+ACC+120], rax
        mov     rax, [rsp+TAB+128]
        cmovz   rax, rcx
        mov     [rsp+ACC+128], rax
        mov     rax, [rsp+TAB+136]
        cmovz   rax, rcx
        mov     [rsp+ACC+136], rax
        mov     rax, [rsp+TAB+144]
        cmovz   rax, rcx
        mov     [rsp+ACC+144], rax
        mov     rax, [rsp+TAB+152]
        cmovz   rax, rcx
        mov     [rsp+ACC+152], rax
        mov     rax, [rsp+TAB+160]
        cmovz   rax, rcx
        mov     [rsp+ACC+160], rax
        mov     rax, [rsp+TAB+168]
        cmovz   rax, rcx
        mov     [rsp+ACC+168], rax
        mov     rax, [rsp+TAB+176]
        cmovz   rax, rcx
        mov     [rsp+ACC+176], rax
        mov     rax, [rsp+TAB+184]
        cmovz   rax, rcx
        mov     [rsp+ACC+184], rax
        mov     rax, [rsp+TAB+192]
        cmovz   rax, rcx
        mov     [rsp+ACC+192], rax
        mov     rax, [rsp+TAB+200]
        cmovz   rax, rcx
        mov     [rsp+ACC+200], rax
        mov     rax, [rsp+TAB+208]
        cmovz   rax, rcx
        mov     [rsp+ACC+208], rax

// Main loop over size-5 bitfields: double 5 times then add signed digit
// At each stage we shift the scalar left by 5 bits so we can simply pick
// the top 5 bits as the bitfield, saving some fiddle over indexing.

        mov     ebp, 520

Lp521_jscalarmul_alt_mainloop:
        sub     rbp, 5

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp521_jscalarmul_alt_jdouble)

// Choose the bitfield and adjust it to sign and magnitude

        mov     r8, [rsp+SCALARB]
        mov     r9, [rsp+SCALARB+8]
        mov     r10, [rsp+SCALARB+16]
        mov     r11, [rsp+SCALARB+24]
        mov     r12, [rsp+SCALARB+32]
        mov     r13, [rsp+SCALARB+40]
        mov     r14, [rsp+SCALARB+48]
        mov     r15, [rsp+SCALARB+56]
        mov     rax, [rsp+SCALARB+64]


        mov     rdi, rax
        shr     rdi, 59

        shld    rax, r15, 5
        shld    r15, r14, 5
        shld    r14, r13, 5
        shld    r13, r12, 5
        shld    r12, r11, 5
        shld    r11, r10, 5
        shld    r10, r9, 5
        shld    r9, r8, 5
        shl     r8, 5

        mov     [rsp+SCALARB], r8
        mov     [rsp+SCALARB+8], r9
        mov     [rsp+SCALARB+16], r10
        mov     [rsp+SCALARB+24], r11
        mov     [rsp+SCALARB+32], r12
        mov     [rsp+SCALARB+40], r13
        mov     [rsp+SCALARB+48], r14
        mov     [rsp+SCALARB+56], r15
        mov     [rsp+SCALARB+64], rax

        sub     rdi, 16
        sbb     rsi, rsi        // rsi = sign of digit (-1 = negative)
        xor     rdi, rsi
        sub     rdi, rsi        // rdi = absolute value of digit

// Conditionally select the table entry tab[i-1] = i * P in constant time
// Again, this is done in separate sweeps per coordinate, doing y last.

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        selectblock(1,0)
        selectblock(2,0)
        selectblock(3,0)
        selectblock(4,0)
        selectblock(5,0)
        selectblock(6,0)
        selectblock(7,0)
        selectblock(8,0)
        selectblock(9,0)
        selectblock(10,0)
        selectblock(11,0)
        selectblock(12,0)
        selectblock(13,0)
        selectblock(14,0)
        selectblock(15,0)
        selectblock(16,0)
        mov     [rsp+TABENT], rax
        mov     [rsp+TABENT+8], rbx
        mov     [rsp+TABENT+16], rcx
        mov     [rsp+TABENT+24], rdx
        mov     [rsp+TABENT+32], r8
        mov     [rsp+TABENT+40], r9
        mov     [rsp+TABENT+48], r10
        mov     [rsp+TABENT+56], r11
        mov     [rsp+TABENT+64], r12

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        selectblock(1,2)
        selectblock(2,2)
        selectblock(3,2)
        selectblock(4,2)
        selectblock(5,2)
        selectblock(6,2)
        selectblock(7,2)
        selectblock(8,2)
        selectblock(9,2)
        selectblock(10,2)
        selectblock(11,2)
        selectblock(12,2)
        selectblock(13,2)
        selectblock(14,2)
        selectblock(15,2)
        selectblock(16,2)
        mov     [rsp+TABENT+2*NUMSIZE], rax
        mov     [rsp+TABENT+2*NUMSIZE+8], rbx
        mov     [rsp+TABENT+2*NUMSIZE+16], rcx
        mov     [rsp+TABENT+2*NUMSIZE+24], rdx
        mov     [rsp+TABENT+2*NUMSIZE+32], r8
        mov     [rsp+TABENT+2*NUMSIZE+40], r9
        mov     [rsp+TABENT+2*NUMSIZE+48], r10
        mov     [rsp+TABENT+2*NUMSIZE+56], r11
        mov     [rsp+TABENT+2*NUMSIZE+64], r12

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        selectblock(1,1)
        selectblock(2,1)
        selectblock(3,1)
        selectblock(4,1)
        selectblock(5,1)
        selectblock(6,1)
        selectblock(7,1)
        selectblock(8,1)
        selectblock(9,1)
        selectblock(10,1)
        selectblock(11,1)
        selectblock(12,1)
        selectblock(13,1)
        selectblock(14,1)
        selectblock(15,1)
        selectblock(16,1)

// Store it to "tabent" with the y coordinate optionally negated.
// This is done carefully to give coordinates < p_521 even in
// the degenerate case y = 0 (when z = 0 for points on the curve).

        mov     r13, rax
        or      r13, rbx
        mov     r14, rcx
        or      r14, rdx
        mov     r15, r8
        or      r15, r9
        mov     rdi, r10
        or      rdi, r11
        or      r13, r14
        or      r15, rdi
        or      r15, r12
        or      r13, r15
        cmovz   rsi, r13

        xor     rax, rsi
        xor     rbx, rsi
        xor     rcx, rsi
        xor     rdx, rsi
        xor     r8, rsi
        xor     r9, rsi
        xor     r10, rsi
        xor     r11, rsi
        and     rsi, 0x1FF
        xor     r12, rsi

        mov     [rsp+TABENT+NUMSIZE], rax
        mov     [rsp+TABENT+NUMSIZE+8], rbx
        mov     [rsp+TABENT+NUMSIZE+16], rcx
        mov     [rsp+TABENT+NUMSIZE+24], rdx
        mov     [rsp+TABENT+NUMSIZE+32], r8
        mov     [rsp+TABENT+NUMSIZE+40], r9
        mov     [rsp+TABENT+NUMSIZE+48], r10
        mov     [rsp+TABENT+NUMSIZE+56], r11
        mov     [rsp+TABENT+NUMSIZE+64], r12

// Add to the accumulator

        lea     rdx, [rsp+TABENT]
        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp521_jscalarmul_alt_jadd)

        test    rbp, rbp
        jne     Lp521_jscalarmul_alt_mainloop

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
        mov     rax, [rsp+ACC+96]
        mov     [rdi+96], rax
        mov     rax, [rsp+ACC+104]
        mov     [rdi+104], rax
        mov     rax, [rsp+ACC+112]
        mov     [rdi+112], rax
        mov     rax, [rsp+ACC+120]
        mov     [rdi+120], rax
        mov     rax, [rsp+ACC+128]
        mov     [rdi+128], rax
        mov     rax, [rsp+ACC+136]
        mov     [rdi+136], rax
        mov     rax, [rsp+ACC+144]
        mov     [rdi+144], rax
        mov     rax, [rsp+ACC+152]
        mov     [rdi+152], rax
        mov     rax, [rsp+ACC+160]
        mov     [rdi+160], rax
        mov     rax, [rsp+ACC+168]
        mov     [rdi+168], rax
        mov     rax, [rsp+ACC+176]
        mov     [rdi+176], rax
        mov     rax, [rsp+ACC+184]
        mov     [rdi+184], rax
        mov     rax, [rsp+ACC+192]
        mov     [rdi+192], rax
        mov     rax, [rsp+ACC+200]
        mov     [rdi+200], rax
        mov     rax, [rsp+ACC+208]
        mov     [rdi+208], rax

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
S2N_BN_SIZE_DIRECTIVE(Lp521_jscalarmul_alt_standard)
#else
S2N_BN_SIZE_DIRECTIVE(p521_jscalarmul_alt)
#endif

// Local copies of subroutines, complete clones at the moment

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp521_jscalarmul_alt_bignum_mod_p521_9)

Lp521_jscalarmul_alt_bignum_mod_p521_9:
        CFI_START
        CFI_PUSH(rbx)
        mov     rax, [rsi+0x40]
        mov     edx, 0x1ff
        and     rdx, rax
        shr     rax, 0x9
        stc
        adc     rax, [rsi]
        mov     rcx, [rsi+0x8]
        adc     rcx, 0x0
        mov     r8, [rsi+0x10]
        adc     r8, 0x0
        mov     r9, [rsi+0x18]
        adc     r9, 0x0
        mov     r10, [rsi+0x20]
        adc     r10, 0x0
        mov     r11, [rsi+0x28]
        adc     r11, 0x0
        mov     rbx, [rsi+0x30]
        adc     rbx, 0x0
        mov     rsi, [rsi+0x38]
        adc     rsi, 0x0
        adc     rdx, 0x0
        cmp     rdx, 0x200
        sbb     rax, 0x0
        mov     [rdi], rax
        sbb     rcx, 0x0
        mov     [rdi+0x8], rcx
        sbb     r8, 0x0
        mov     [rdi+0x10], r8
        sbb     r9, 0x0
        mov     [rdi+0x18], r9
        sbb     r10, 0x0
        mov     [rdi+0x20], r10
        sbb     r11, 0x0
        mov     [rdi+0x28], r11
        sbb     rbx, 0x0
        mov     [rdi+0x30], rbx
        sbb     rsi, 0x0
        mov     [rdi+0x38], rsi
        sbb     rdx, 0x0
        and     rdx, 0x1ff
        mov     [rdi+0x40], rdx
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp521_jscalarmul_alt_bignum_mod_p521_9)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp521_jscalarmul_alt_bignum_mod_n521_9)

Lp521_jscalarmul_alt_bignum_mod_n521_9:
        CFI_START
        mov     rcx, [rsi+0x40]
        mov     rax, 0xfffffffffffffe00
        or      rax, rcx
        mov     [rdi+0x40], rax
        shr     rcx, 0x9
        add     rcx, 0x1
        mov     rax, 0x449048e16ec79bf7
        mul     rcx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, 0xc44a36477663b851
        mul     rcx
        xor     r10, r10
        add     r9, rax
        adc     r10, rdx
        mov     rax, 0x8033feb708f65a2f
        mul     rcx
        xor     r11, r11
        add     r10, rax
        adc     r11, rdx
        mov     rax, 0xae79787c40d06994
        mul     rcx
        imul    rcx, rcx, 0x5
        add     r11, rax
        adc     rcx, rdx
        sbb     rdx, rdx
        neg     rdx
        xor     eax, eax
        add     r8, [rsi]
        mov     [rdi], r8
        adc     r9, [rsi+0x8]
        mov     [rdi+0x8], r9
        adc     r10, [rsi+0x10]
        mov     [rdi+0x10], r10
        adc     r11, [rsi+0x18]
        mov     [rdi+0x18], r11
        adc     rcx, [rsi+0x20]
        mov     [rdi+0x20], rcx
        adc     rdx, [rsi+0x28]
        mov     [rdi+0x28], rdx
        mov     rdx, [rsi+0x30]
        adc     rdx, rax
        mov     [rdi+0x30], rdx
        mov     rdx, [rsi+0x38]
        adc     rdx, rax
        mov     [rdi+0x38], rdx
        mov     rcx, [rdi+0x40]
        adc     rcx, rax
        cmc
        sbb     rdx, rdx
        mov     r8, 0x449048e16ec79bf7
        and     r8, rdx
        mov     r9, 0xc44a36477663b851
        and     r9, rdx
        mov     r10, 0x8033feb708f65a2f
        and     r10, rdx
        mov     r11, 0xae79787c40d06994
        and     r11, rdx
        and     rdx, 0x5
        sub     [rdi], r8
        sbb     [rdi+0x8], r9
        sbb     [rdi+0x10], r10
        sbb     [rdi+0x18], r11
        sbb     [rdi+0x20], rdx
        sbb     [rdi+0x28], rax
        sbb     [rdi+0x30], rax
        sbb     [rdi+0x38], rax
        sbb     ecx, eax
        and     ecx, 0x1ff
        mov     [rdi+0x40], rcx
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp521_jscalarmul_alt_bignum_mod_n521_9)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp521_jscalarmul_alt_jadd)

Lp521_jscalarmul_alt_jadd:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(528)
        mov     [rsp+0x1f8], rdi
        mov     [rsp+0x200], rsi
        mov     [rsp+0x208], rdx
        mov     rsi, [rsp+0x200]
        lea     rsi, [rsi+0x90]
        lea     rdi, [rsp]
        CFI_CALL(Lp521_jscalarmul_alt_sqr_p521)
        mov     rdi, [rsp+0x208]
        lea     rsi, [rdi+0x90]
        lea     rdi, [rsp+0x168]
        CFI_CALL(Lp521_jscalarmul_alt_sqr_p521)
        mov     rsi, [rsp+0x200]
        mov     rdi, [rsp+0x208]
        lea     rdx, [rsi+0x48]
        lea     rsi, [rdi+0x90]
        lea     rdi, [rsp+0x1b0]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        mov     rsi, [rsp+0x200]
        mov     rdi, [rsp+0x208]
        lea     rdx, [rdi+0x48]
        lea     rsi, [rsi+0x90]
        lea     rdi, [rsp+0x48]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        mov     rdi, [rsp+0x208]
        lea     rdx, [rdi]
        lea     rsi, [rsp]
        lea     rdi, [rsp+0x90]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        mov     rsi, [rsp+0x200]
        lea     rdx, [rsi]
        lea     rsi, [rsp+0x168]
        lea     rdi, [rsp+0x120]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        lea     rdx, [rsp+0x48]
        lea     rsi, [rsp]
        lea     rdi, [rsp+0x48]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        lea     rdx, [rsp+0x1b0]
        lea     rsi, [rsp+0x168]
        lea     rdi, [rsp+0x1b0]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        mov     rax, [rsp+0x90]
        sub     rax, [rsp+0x120]
        mov     rdx, [rsp+0x98]
        sbb     rdx, [rsp+0x128]
        mov     r8, [rsp+0xa0]
        sbb     r8, [rsp+0x130]
        mov     r9, [rsp+0xa8]
        sbb     r9, [rsp+0x138]
        mov     r10, [rsp+0xb0]
        sbb     r10, [rsp+0x140]
        mov     r11, [rsp+0xb8]
        sbb     r11, [rsp+0x148]
        mov     r12, [rsp+0xc0]
        sbb     r12, [rsp+0x150]
        mov     r13, [rsp+0xc8]
        sbb     r13, [rsp+0x158]
        mov     r14, [rsp+0xd0]
        sbb     r14, [rsp+0x160]
        sbb     rax, 0x0
        mov     [rsp+0x168], rax
        sbb     rdx, 0x0
        mov     [rsp+0x170], rdx
        sbb     r8, 0x0
        mov     [rsp+0x178], r8
        sbb     r9, 0x0
        mov     [rsp+0x180], r9
        sbb     r10, 0x0
        mov     [rsp+0x188], r10
        sbb     r11, 0x0
        mov     [rsp+0x190], r11
        sbb     r12, 0x0
        mov     [rsp+0x198], r12
        sbb     r13, 0x0
        mov     [rsp+0x1a0], r13
        sbb     r14, 0x0
        and     r14, 0x1ff
        mov     [rsp+0x1a8], r14
        mov     rax, [rsp+0x48]
        sub     rax, [rsp+0x1b0]
        mov     rdx, [rsp+0x50]
        sbb     rdx, [rsp+0x1b8]
        mov     r8, [rsp+0x58]
        sbb     r8, [rsp+0x1c0]
        mov     r9, [rsp+0x60]
        sbb     r9, [rsp+0x1c8]
        mov     r10, [rsp+0x68]
        sbb     r10, [rsp+0x1d0]
        mov     r11, [rsp+0x70]
        sbb     r11, [rsp+0x1d8]
        mov     r12, [rsp+0x78]
        sbb     r12, [rsp+0x1e0]
        mov     r13, [rsp+0x80]
        sbb     r13, [rsp+0x1e8]
        mov     r14, [rsp+0x88]
        sbb     r14, [rsp+0x1f0]
        sbb     rax, 0x0
        mov     [rsp+0x48], rax
        sbb     rdx, 0x0
        mov     [rsp+0x50], rdx
        sbb     r8, 0x0
        mov     [rsp+0x58], r8
        sbb     r9, 0x0
        mov     [rsp+0x60], r9
        sbb     r10, 0x0
        mov     [rsp+0x68], r10
        sbb     r11, 0x0
        mov     [rsp+0x70], r11
        sbb     r12, 0x0
        mov     [rsp+0x78], r12
        sbb     r13, 0x0
        mov     [rsp+0x80], r13
        sbb     r14, 0x0
        and     r14, 0x1ff
        mov     [rsp+0x88], r14
        lea     rsi, [rsp+0x168]
        lea     rdi, [rsp+0xd8]
        CFI_CALL(Lp521_jscalarmul_alt_sqr_p521)
        lea     rsi, [rsp+0x48]
        lea     rdi, [rsp]
        CFI_CALL(Lp521_jscalarmul_alt_sqr_p521)
        lea     rdx, [rsp+0x120]
        lea     rsi, [rsp+0xd8]
        lea     rdi, [rsp+0x120]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        lea     rdx, [rsp+0x90]
        lea     rsi, [rsp+0xd8]
        lea     rdi, [rsp+0x90]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        mov     rax, [rsp]
        sub     rax, [rsp+0x120]
        mov     rdx, [rsp+0x8]
        sbb     rdx, [rsp+0x128]
        mov     r8, [rsp+0x10]
        sbb     r8, [rsp+0x130]
        mov     r9, [rsp+0x18]
        sbb     r9, [rsp+0x138]
        mov     r10, [rsp+0x20]
        sbb     r10, [rsp+0x140]
        mov     r11, [rsp+0x28]
        sbb     r11, [rsp+0x148]
        mov     r12, [rsp+0x30]
        sbb     r12, [rsp+0x150]
        mov     r13, [rsp+0x38]
        sbb     r13, [rsp+0x158]
        mov     r14, [rsp+0x40]
        sbb     r14, [rsp+0x160]
        sbb     rax, 0x0
        mov     [rsp], rax
        sbb     rdx, 0x0
        mov     [rsp+0x8], rdx
        sbb     r8, 0x0
        mov     [rsp+0x10], r8
        sbb     r9, 0x0
        mov     [rsp+0x18], r9
        sbb     r10, 0x0
        mov     [rsp+0x20], r10
        sbb     r11, 0x0
        mov     [rsp+0x28], r11
        sbb     r12, 0x0
        mov     [rsp+0x30], r12
        sbb     r13, 0x0
        mov     [rsp+0x38], r13
        sbb     r14, 0x0
        and     r14, 0x1ff
        mov     [rsp+0x40], r14
        mov     rax, [rsp+0x90]
        sub     rax, [rsp+0x120]
        mov     rdx, [rsp+0x98]
        sbb     rdx, [rsp+0x128]
        mov     r8, [rsp+0xa0]
        sbb     r8, [rsp+0x130]
        mov     r9, [rsp+0xa8]
        sbb     r9, [rsp+0x138]
        mov     r10, [rsp+0xb0]
        sbb     r10, [rsp+0x140]
        mov     r11, [rsp+0xb8]
        sbb     r11, [rsp+0x148]
        mov     r12, [rsp+0xc0]
        sbb     r12, [rsp+0x150]
        mov     r13, [rsp+0xc8]
        sbb     r13, [rsp+0x158]
        mov     r14, [rsp+0xd0]
        sbb     r14, [rsp+0x160]
        sbb     rax, 0x0
        mov     [rsp+0xd8], rax
        sbb     rdx, 0x0
        mov     [rsp+0xe0], rdx
        sbb     r8, 0x0
        mov     [rsp+0xe8], r8
        sbb     r9, 0x0
        mov     [rsp+0xf0], r9
        sbb     r10, 0x0
        mov     [rsp+0xf8], r10
        sbb     r11, 0x0
        mov     [rsp+0x100], r11
        sbb     r12, 0x0
        mov     [rsp+0x108], r12
        sbb     r13, 0x0
        mov     [rsp+0x110], r13
        sbb     r14, 0x0
        and     r14, 0x1ff
        mov     [rsp+0x118], r14
        mov     rsi, [rsp+0x200]
        lea     rdx, [rsi+0x90]
        lea     rsi, [rsp+0x168]
        lea     rdi, [rsp+0x168]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        mov     rax, [rsp]
        sub     rax, [rsp+0x90]
        mov     rdx, [rsp+0x8]
        sbb     rdx, [rsp+0x98]
        mov     r8, [rsp+0x10]
        sbb     r8, [rsp+0xa0]
        mov     r9, [rsp+0x18]
        sbb     r9, [rsp+0xa8]
        mov     r10, [rsp+0x20]
        sbb     r10, [rsp+0xb0]
        mov     r11, [rsp+0x28]
        sbb     r11, [rsp+0xb8]
        mov     r12, [rsp+0x30]
        sbb     r12, [rsp+0xc0]
        mov     r13, [rsp+0x38]
        sbb     r13, [rsp+0xc8]
        mov     r14, [rsp+0x40]
        sbb     r14, [rsp+0xd0]
        sbb     rax, 0x0
        mov     [rsp], rax
        sbb     rdx, 0x0
        mov     [rsp+0x8], rdx
        sbb     r8, 0x0
        mov     [rsp+0x10], r8
        sbb     r9, 0x0
        mov     [rsp+0x18], r9
        sbb     r10, 0x0
        mov     [rsp+0x20], r10
        sbb     r11, 0x0
        mov     [rsp+0x28], r11
        sbb     r12, 0x0
        mov     [rsp+0x30], r12
        sbb     r13, 0x0
        mov     [rsp+0x38], r13
        sbb     r14, 0x0
        and     r14, 0x1ff
        mov     [rsp+0x40], r14
        mov     rax, [rsp+0x120]
        sub     rax, [rsp]
        mov     rdx, [rsp+0x128]
        sbb     rdx, [rsp+0x8]
        mov     r8, [rsp+0x130]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsp+0x138]
        sbb     r9, [rsp+0x18]
        mov     r10, [rsp+0x140]
        sbb     r10, [rsp+0x20]
        mov     r11, [rsp+0x148]
        sbb     r11, [rsp+0x28]
        mov     r12, [rsp+0x150]
        sbb     r12, [rsp+0x30]
        mov     r13, [rsp+0x158]
        sbb     r13, [rsp+0x38]
        mov     r14, [rsp+0x160]
        sbb     r14, [rsp+0x40]
        sbb     rax, 0x0
        mov     [rsp+0x120], rax
        sbb     rdx, 0x0
        mov     [rsp+0x128], rdx
        sbb     r8, 0x0
        mov     [rsp+0x130], r8
        sbb     r9, 0x0
        mov     [rsp+0x138], r9
        sbb     r10, 0x0
        mov     [rsp+0x140], r10
        sbb     r11, 0x0
        mov     [rsp+0x148], r11
        sbb     r12, 0x0
        mov     [rsp+0x150], r12
        sbb     r13, 0x0
        mov     [rsp+0x158], r13
        sbb     r14, 0x0
        and     r14, 0x1ff
        mov     [rsp+0x160], r14
        lea     rdx, [rsp+0x1b0]
        lea     rsi, [rsp+0xd8]
        lea     rdi, [rsp+0xd8]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        mov     rdi, [rsp+0x208]
        lea     rdx, [rdi+0x90]
        lea     rsi, [rsp+0x168]
        lea     rdi, [rsp+0x168]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        lea     rdx, [rsp+0x120]
        lea     rsi, [rsp+0x48]
        lea     rdi, [rsp+0x120]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        mov     rax, [rsp+0x120]
        sub     rax, [rsp+0xd8]
        mov     rdx, [rsp+0x128]
        sbb     rdx, [rsp+0xe0]
        mov     r8, [rsp+0x130]
        sbb     r8, [rsp+0xe8]
        mov     r9, [rsp+0x138]
        sbb     r9, [rsp+0xf0]
        mov     r10, [rsp+0x140]
        sbb     r10, [rsp+0xf8]
        mov     r11, [rsp+0x148]
        sbb     r11, [rsp+0x100]
        mov     r12, [rsp+0x150]
        sbb     r12, [rsp+0x108]
        mov     r13, [rsp+0x158]
        sbb     r13, [rsp+0x110]
        mov     r14, [rsp+0x160]
        sbb     r14, [rsp+0x118]
        sbb     rax, 0x0
        mov     [rsp+0x120], rax
        sbb     rdx, 0x0
        mov     [rsp+0x128], rdx
        sbb     r8, 0x0
        mov     [rsp+0x130], r8
        sbb     r9, 0x0
        mov     [rsp+0x138], r9
        sbb     r10, 0x0
        mov     [rsp+0x140], r10
        sbb     r11, 0x0
        mov     [rsp+0x148], r11
        sbb     r12, 0x0
        mov     [rsp+0x150], r12
        sbb     r13, 0x0
        mov     [rsp+0x158], r13
        sbb     r14, 0x0
        and     r14, 0x1ff
        mov     [rsp+0x160], r14
        mov     rsi, [rsp+0x200]
        mov     r8, [rsi+0x90]
        mov     r9, [rsi+0x98]
        mov     r10, [rsi+0xa0]
        mov     r11, [rsi+0xa8]
        mov     r12, [rsi+0xb0]
        mov     r13, [rsi+0xb8]
        mov     r14, [rsi+0xc0]
        mov     r15, [rsi+0xc8]
        mov     rbp, [rsi+0xd0]
        or      r8, r9
        or      r10, r11
        or      r12, r13
        or      r14, r15
        or      r8, r10
        or      r12, r14
        or      r8, rbp
        or      r8, r12
        neg     r8
        sbb     rax, rax
        mov     rdi, [rsp+0x208]
        mov     r8, [rdi+0x90]
        mov     r9, [rdi+0x98]
        mov     r10, [rdi+0xa0]
        mov     r11, [rdi+0xa8]
        mov     r12, [rdi+0xb0]
        mov     r13, [rdi+0xb8]
        mov     r14, [rdi+0xc0]
        mov     r15, [rdi+0xc8]
        mov     rbp, [rdi+0xd0]
        or      r8, r9
        or      r10, r11
        or      r12, r13
        or      r14, r15
        or      r8, r10
        or      r12, r14
        or      r8, rbp
        or      r8, r12
        neg     r8
        sbb     rdx, rdx
        cmp     rdx, rax
        mov     r8, [rsp+0x120]
        cmovb   r8, [rsi+0x48]
        cmova   r8, [rdi+0x48]
        mov     r9, [rsp+0x128]
        cmovb   r9, [rsi+0x50]
        cmova   r9, [rdi+0x50]
        mov     r10, [rsp+0x130]
        cmovb   r10, [rsi+0x58]
        cmova   r10, [rdi+0x58]
        mov     r11, [rsp+0x138]
        cmovb   r11, [rsi+0x60]
        cmova   r11, [rdi+0x60]
        mov     r12, [rsp+0x140]
        cmovb   r12, [rsi+0x68]
        cmova   r12, [rdi+0x68]
        mov     r13, [rsp+0x148]
        cmovb   r13, [rsi+0x70]
        cmova   r13, [rdi+0x70]
        mov     r14, [rsp+0x150]
        cmovb   r14, [rsi+0x78]
        cmova   r14, [rdi+0x78]
        mov     r15, [rsp+0x158]
        cmovb   r15, [rsi+0x80]
        cmova   r15, [rdi+0x80]
        mov     rbp, [rsp+0x160]
        cmovb   rbp, [rsi+0x88]
        cmova   rbp, [rdi+0x88]
        mov     [rsp+0x120], r8
        mov     [rsp+0x128], r9
        mov     [rsp+0x130], r10
        mov     [rsp+0x138], r11
        mov     [rsp+0x140], r12
        mov     [rsp+0x148], r13
        mov     [rsp+0x150], r14
        mov     [rsp+0x158], r15
        mov     [rsp+0x160], rbp
        mov     r8, [rsp+0x168]
        cmovb   r8, [rsi+0x90]
        cmova   r8, [rdi+0x90]
        mov     r9, [rsp+0x170]
        cmovb   r9, [rsi+0x98]
        cmova   r9, [rdi+0x98]
        mov     r10, [rsp+0x178]
        cmovb   r10, [rsi+0xa0]
        cmova   r10, [rdi+0xa0]
        mov     r11, [rsp+0x180]
        cmovb   r11, [rsi+0xa8]
        cmova   r11, [rdi+0xa8]
        mov     r12, [rsp+0x188]
        cmovb   r12, [rsi+0xb0]
        cmova   r12, [rdi+0xb0]
        mov     r13, [rsp+0x190]
        cmovb   r13, [rsi+0xb8]
        cmova   r13, [rdi+0xb8]
        mov     r14, [rsp+0x198]
        cmovb   r14, [rsi+0xc0]
        cmova   r14, [rdi+0xc0]
        mov     r15, [rsp+0x1a0]
        cmovb   r15, [rsi+0xc8]
        cmova   r15, [rdi+0xc8]
        mov     rbp, [rsp+0x1a8]
        cmovb   rbp, [rsi+0xd0]
        cmova   rbp, [rdi+0xd0]
        mov     [rsp+0x168], r8
        mov     [rsp+0x170], r9
        mov     [rsp+0x178], r10
        mov     [rsp+0x180], r11
        mov     [rsp+0x188], r12
        mov     [rsp+0x190], r13
        mov     [rsp+0x198], r14
        mov     [rsp+0x1a0], r15
        mov     [rsp+0x1a8], rbp
        mov     r8, [rsp]
        cmovb   r8, [rsi]
        cmova   r8, [rdi]
        mov     r9, [rsp+0x8]
        cmovb   r9, [rsi+0x8]
        cmova   r9, [rdi+0x8]
        mov     r10, [rsp+0x10]
        cmovb   r10, [rsi+0x10]
        cmova   r10, [rdi+0x10]
        mov     r11, [rsp+0x18]
        cmovb   r11, [rsi+0x18]
        cmova   r11, [rdi+0x18]
        mov     r12, [rsp+0x20]
        cmovb   r12, [rsi+0x20]
        cmova   r12, [rdi+0x20]
        mov     r13, [rsp+0x28]
        cmovb   r13, [rsi+0x28]
        cmova   r13, [rdi+0x28]
        mov     r14, [rsp+0x30]
        cmovb   r14, [rsi+0x30]
        cmova   r14, [rdi+0x30]
        mov     r15, [rsp+0x38]
        cmovb   r15, [rsi+0x38]
        cmova   r15, [rdi+0x38]
        mov     rbp, [rsp+0x40]
        cmovb   rbp, [rsi+0x40]
        cmova   rbp, [rdi+0x40]
        mov     rdi, [rsp+0x1f8]
        mov     [rdi], r8
        mov     [rdi+0x8], r9
        mov     [rdi+0x10], r10
        mov     [rdi+0x18], r11
        mov     [rdi+0x20], r12
        mov     [rdi+0x28], r13
        mov     [rdi+0x30], r14
        mov     [rdi+0x38], r15
        mov     [rdi+0x40], rbp
        mov     rax, [rsp+0x120]
        mov     [rdi+0x48], rax
        mov     rax, [rsp+0x128]
        mov     [rdi+0x50], rax
        mov     rax, [rsp+0x130]
        mov     [rdi+0x58], rax
        mov     rax, [rsp+0x138]
        mov     [rdi+0x60], rax
        mov     rax, [rsp+0x140]
        mov     [rdi+0x68], rax
        mov     rax, [rsp+0x148]
        mov     [rdi+0x70], rax
        mov     rax, [rsp+0x150]
        mov     [rdi+0x78], rax
        mov     rax, [rsp+0x158]
        mov     [rdi+0x80], rax
        mov     rax, [rsp+0x160]
        mov     [rdi+0x88], rax
        mov     rax, [rsp+0x168]
        mov     [rdi+0x90], rax
        mov     rax, [rsp+0x170]
        mov     [rdi+0x98], rax
        mov     rax, [rsp+0x178]
        mov     [rdi+0xa0], rax
        mov     rax, [rsp+0x180]
        mov     [rdi+0xa8], rax
        mov     rax, [rsp+0x188]
        mov     [rdi+0xb0], rax
        mov     rax, [rsp+0x190]
        mov     [rdi+0xb8], rax
        mov     rax, [rsp+0x198]
        mov     [rdi+0xc0], rax
        mov     rax, [rsp+0x1a0]
        mov     [rdi+0xc8], rax
        mov     rax, [rsp+0x1a8]
        mov     [rdi+0xd0], rax
        CFI_INC_RSP(528)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp521_jscalarmul_alt_jadd)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp521_jscalarmul_alt_jdouble)

Lp521_jscalarmul_alt_jdouble:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(520)
        mov     [rsp+0x1f8], rdi
        mov     [rsp+0x200], rsi
        mov     rdi, [rsp+0x200]
        lea     rsi, [rdi+0x90]
        lea     rdi, [rsp]
        CFI_CALL(Lp521_jscalarmul_alt_sqr_p521)
        mov     rdi, [rsp+0x200]
        lea     rsi, [rdi+0x48]
        lea     rdi, [rsp+0x48]
        CFI_CALL(Lp521_jscalarmul_alt_sqr_p521)
        mov     rdi, [rsp+0x200]
        stc
        mov     rax, [rdi]
        adc     rax, [rsp]
        mov     rbx, [rdi+0x8]
        adc     rbx, [rsp+0x8]
        mov     r8, [rdi+0x10]
        adc     r8, [rsp+0x10]
        mov     r9, [rdi+0x18]
        adc     r9, [rsp+0x18]
        mov     r10, [rdi+0x20]
        adc     r10, [rsp+0x20]
        mov     r11, [rdi+0x28]
        adc     r11, [rsp+0x28]
        mov     r12, [rdi+0x30]
        adc     r12, [rsp+0x30]
        mov     r13, [rdi+0x38]
        adc     r13, [rsp+0x38]
        mov     r14, [rdi+0x40]
        adc     r14, [rsp+0x40]
        mov     rdx, 0x200
        and     rdx, r14
        cmp     rdx, 0x200
        sbb     rax, 0x0
        mov     [rsp+0x168], rax
        sbb     rbx, 0x0
        mov     [rsp+0x170], rbx
        sbb     r8, 0x0
        mov     [rsp+0x178], r8
        sbb     r9, 0x0
        mov     [rsp+0x180], r9
        sbb     r10, 0x0
        mov     [rsp+0x188], r10
        sbb     r11, 0x0
        mov     [rsp+0x190], r11
        sbb     r12, 0x0
        mov     [rsp+0x198], r12
        sbb     r13, 0x0
        mov     [rsp+0x1a0], r13
        sbb     r14, rdx
        mov     [rsp+0x1a8], r14
        mov     rdi, [rsp+0x200]
        mov     rax, [rdi]
        sub     rax, [rsp]
        mov     rdx, [rdi+0x8]
        sbb     rdx, [rsp+0x8]
        mov     r8, [rdi+0x10]
        sbb     r8, [rsp+0x10]
        mov     r9, [rdi+0x18]
        sbb     r9, [rsp+0x18]
        mov     r10, [rdi+0x20]
        sbb     r10, [rsp+0x20]
        mov     r11, [rdi+0x28]
        sbb     r11, [rsp+0x28]
        mov     r12, [rdi+0x30]
        sbb     r12, [rsp+0x30]
        mov     r13, [rdi+0x38]
        sbb     r13, [rsp+0x38]
        mov     r14, [rdi+0x40]
        sbb     r14, [rsp+0x40]
        sbb     rax, 0x0
        mov     [rsp+0x120], rax
        sbb     rdx, 0x0
        mov     [rsp+0x128], rdx
        sbb     r8, 0x0
        mov     [rsp+0x130], r8
        sbb     r9, 0x0
        mov     [rsp+0x138], r9
        sbb     r10, 0x0
        mov     [rsp+0x140], r10
        sbb     r11, 0x0
        mov     [rsp+0x148], r11
        sbb     r12, 0x0
        mov     [rsp+0x150], r12
        sbb     r13, 0x0
        mov     [rsp+0x158], r13
        sbb     r14, 0x0
        and     r14, 0x1ff
        mov     [rsp+0x160], r14
        lea     rdx, [rsp+0x120]
        lea     rsi, [rsp+0x168]
        lea     rdi, [rsp+0x90]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        mov     rdi, [rsp+0x200]
        stc
        mov     rax, [rdi+0x48]
        adc     rax, [rdi+0x90]
        mov     rbx, [rdi+0x50]
        adc     rbx, [rdi+0x98]
        mov     r8, [rdi+0x58]
        adc     r8, [rdi+0xa0]
        mov     r9, [rdi+0x60]
        adc     r9, [rdi+0xa8]
        mov     r10, [rdi+0x68]
        adc     r10, [rdi+0xb0]
        mov     r11, [rdi+0x70]
        adc     r11, [rdi+0xb8]
        mov     r12, [rdi+0x78]
        adc     r12, [rdi+0xc0]
        mov     r13, [rdi+0x80]
        adc     r13, [rdi+0xc8]
        mov     r14, [rdi+0x88]
        adc     r14, [rdi+0xd0]
        mov     rdx, 0x200
        and     rdx, r14
        cmp     rdx, 0x200
        sbb     rax, 0x0
        mov     [rsp+0x168], rax
        sbb     rbx, 0x0
        mov     [rsp+0x170], rbx
        sbb     r8, 0x0
        mov     [rsp+0x178], r8
        sbb     r9, 0x0
        mov     [rsp+0x180], r9
        sbb     r10, 0x0
        mov     [rsp+0x188], r10
        sbb     r11, 0x0
        mov     [rsp+0x190], r11
        sbb     r12, 0x0
        mov     [rsp+0x198], r12
        sbb     r13, 0x0
        mov     [rsp+0x1a0], r13
        sbb     r14, rdx
        mov     [rsp+0x1a8], r14
        lea     rsi, [rsp+0x90]
        lea     rdi, [rsp+0x1b0]
        CFI_CALL(Lp521_jscalarmul_alt_sqr_p521)
        mov     rdi, [rsp+0x200]
        lea     rdx, [rsp+0x48]
        lea     rsi, [rdi]
        lea     rdi, [rsp+0xd8]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        lea     rsi, [rsp+0x168]
        lea     rdi, [rsp+0x120]
        CFI_CALL(Lp521_jscalarmul_alt_sqr_p521)
        mov     rcx, 0x9
        mov     rax, [rsp+0x1b0]
        not     rax
        mul     rcx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x1b8]
        not     rax
        mul     rcx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x1c0]
        not     rax
        mul     rcx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x1c8]
        not     rax
        mul     rcx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0x1d0]
        not     rax
        mul     rcx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x1d8]
        not     rax
        mul     rcx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        mov     rax, [rsp+0x1e0]
        not     rax
        mul     rcx
        xor     r15d, r15d
        add     r14, rax
        adc     r15, rdx
        mov     rax, [rsp+0x1e8]
        not     rax
        mul     rcx
        xor     ebx, ebx
        add     r15, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x1f0]
        xor     rax, 0x1ff
        imul    rax, rcx
        add     rbx, rax
        xor     eax, eax
        mov     ecx, 0xc
        mov     rax, [rsp+0xd8]
        mul     rcx
        add     r8, rax
        adc     r9, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0xe0]
        mul     rcx
        sub     rdx, rbp
        add     r9, rax
        adc     r10, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0xe8]
        mul     rcx
        sub     rdx, rbp
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0xf0]
        mul     rcx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0xf8]
        mul     rcx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x100]
        mul     rcx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x108]
        mul     rcx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x110]
        mul     rcx
        sub     rdx, rbp
        add     r15, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x118]
        imul    rax, rcx
        add     rbx, rax
        mov     rax, r9
        and     rax, r10
        and     rax, r11
        and     rax, r12
        and     rax, r13
        and     rax, r14
        and     rax, r15
        mov     rdx, rbx
        shr     rdx, 0x9
        or      rbx, 0xfffffffffffffe00
        lea     rcx, [rdx+0x1]
        add     rcx, r8
        mov     ecx, 0x0
        adc     rax, rcx
        mov     rax, rbx
        adc     rax, rcx
        adc     r8, rdx
        mov     [rsp+0x1b0], r8
        adc     r9, rcx
        mov     [rsp+0x1b8], r9
        adc     r10, rcx
        mov     [rsp+0x1c0], r10
        adc     r11, rcx
        mov     [rsp+0x1c8], r11
        adc     r12, rcx
        mov     [rsp+0x1d0], r12
        adc     r13, rcx
        mov     [rsp+0x1d8], r13
        adc     r14, rcx
        mov     [rsp+0x1e0], r14
        adc     r15, rcx
        mov     [rsp+0x1e8], r15
        adc     rbx, rcx
        and     rbx, 0x1ff
        mov     [rsp+0x1f0], rbx
        mov     rax, [rsp+0x120]
        sub     rax, [rsp]
        mov     rdx, [rsp+0x128]
        sbb     rdx, [rsp+0x8]
        mov     r8, [rsp+0x130]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsp+0x138]
        sbb     r9, [rsp+0x18]
        mov     r10, [rsp+0x140]
        sbb     r10, [rsp+0x20]
        mov     r11, [rsp+0x148]
        sbb     r11, [rsp+0x28]
        mov     r12, [rsp+0x150]
        sbb     r12, [rsp+0x30]
        mov     r13, [rsp+0x158]
        sbb     r13, [rsp+0x38]
        mov     r14, [rsp+0x160]
        sbb     r14, [rsp+0x40]
        sbb     rax, 0x0
        mov     [rsp+0x168], rax
        sbb     rdx, 0x0
        mov     [rsp+0x170], rdx
        sbb     r8, 0x0
        mov     [rsp+0x178], r8
        sbb     r9, 0x0
        mov     [rsp+0x180], r9
        sbb     r10, 0x0
        mov     [rsp+0x188], r10
        sbb     r11, 0x0
        mov     [rsp+0x190], r11
        sbb     r12, 0x0
        mov     [rsp+0x198], r12
        sbb     r13, 0x0
        mov     [rsp+0x1a0], r13
        sbb     r14, 0x0
        and     r14, 0x1ff
        mov     [rsp+0x1a8], r14
        lea     rsi, [rsp+0x48]
        lea     rdi, [rsp+0x120]
        CFI_CALL(Lp521_jscalarmul_alt_sqr_p521)
        mov     rdi, [rsp+0x1f8]
        mov     rax, [rsp+0x168]
        sub     rax, [rsp+0x48]
        mov     rdx, [rsp+0x170]
        sbb     rdx, [rsp+0x50]
        mov     r8, [rsp+0x178]
        sbb     r8, [rsp+0x58]
        mov     r9, [rsp+0x180]
        sbb     r9, [rsp+0x60]
        mov     r10, [rsp+0x188]
        sbb     r10, [rsp+0x68]
        mov     r11, [rsp+0x190]
        sbb     r11, [rsp+0x70]
        mov     r12, [rsp+0x198]
        sbb     r12, [rsp+0x78]
        mov     r13, [rsp+0x1a0]
        sbb     r13, [rsp+0x80]
        mov     r14, [rsp+0x1a8]
        sbb     r14, [rsp+0x88]
        sbb     rax, 0x0
        mov     [rdi+0x90], rax
        sbb     rdx, 0x0
        mov     [rdi+0x98], rdx
        sbb     r8, 0x0
        mov     [rdi+0xa0], r8
        sbb     r9, 0x0
        mov     [rdi+0xa8], r9
        sbb     r10, 0x0
        mov     [rdi+0xb0], r10
        sbb     r11, 0x0
        mov     [rdi+0xb8], r11
        sbb     r12, 0x0
        mov     [rdi+0xc0], r12
        sbb     r13, 0x0
        mov     [rdi+0xc8], r13
        sbb     r14, 0x0
        and     r14, 0x1ff
        mov     [rdi+0xd0], r14
        lea     rdx, [rsp+0x90]
        lea     rsi, [rsp+0x1b0]
        lea     rdi, [rsp+0x168]
        CFI_CALL(Lp521_jscalarmul_alt_mul_p521)
        mov     rdi, [rsp+0x1f8]
        mov     rbx, [rsp+0x118]
        mov     r15, [rsp+0x110]
        shld    rbx, r15, 0x2
        mov     r14, [rsp+0x108]
        shld    r15, r14, 0x2
        mov     r13, [rsp+0x100]
        shld    r14, r13, 0x2
        mov     r12, [rsp+0xf8]
        shld    r13, r12, 0x2
        mov     r11, [rsp+0xf0]
        shld    r12, r11, 0x2
        mov     r10, [rsp+0xe8]
        shld    r11, r10, 0x2
        mov     r9, [rsp+0xe0]
        shld    r10, r9, 0x2
        mov     r8, [rsp+0xd8]
        shld    r9, r8, 0x2
        shl     r8, 0x2
        mov     rcx, [rsp+0x1f0]
        xor     rcx, 0x1ff
        mov     rax, [rsp+0x1b0]
        not     rax
        add     r8, rax
        mov     rax, [rsp+0x1b8]
        not     rax
        adc     r9, rax
        mov     rax, [rsp+0x1c0]
        not     rax
        adc     r10, rax
        mov     rax, [rsp+0x1c8]
        not     rax
        adc     r11, rax
        mov     rax, [rsp+0x1d0]
        not     rax
        adc     r12, rax
        mov     rax, [rsp+0x1d8]
        not     rax
        adc     r13, rax
        mov     rax, [rsp+0x1e0]
        not     rax
        adc     r14, rax
        mov     rax, [rsp+0x1e8]
        not     rax
        adc     r15, rax
        adc     rbx, rcx
        mov     rax, r9
        and     rax, r10
        and     rax, r11
        and     rax, r12
        and     rax, r13
        and     rax, r14
        and     rax, r15
        mov     rdx, rbx
        shr     rdx, 0x9
        or      rbx, 0xfffffffffffffe00
        lea     rcx, [rdx+0x1]
        add     rcx, r8
        mov     ecx, 0x0
        adc     rax, rcx
        mov     rax, rbx
        adc     rax, rcx
        adc     r8, rdx
        mov     [rdi], r8
        adc     r9, rcx
        mov     [rdi+0x8], r9
        adc     r10, rcx
        mov     [rdi+0x10], r10
        adc     r11, rcx
        mov     [rdi+0x18], r11
        adc     r12, rcx
        mov     [rdi+0x20], r12
        adc     r13, rcx
        mov     [rdi+0x28], r13
        adc     r14, rcx
        mov     [rdi+0x30], r14
        adc     r15, rcx
        mov     [rdi+0x38], r15
        adc     rbx, rcx
        and     rbx, 0x1ff
        mov     [rdi+0x40], rbx
        mov     rdi, [rsp+0x1f8]
        mov     rbx, [rsp+0x160]
        xor     rbx, 0x1ff
        mov     r15, [rsp+0x158]
        not     r15
        shld    rbx, r15, 0x3
        mov     r14, [rsp+0x150]
        not     r14
        shld    r15, r14, 0x3
        mov     r13, [rsp+0x148]
        not     r13
        shld    r14, r13, 0x3
        mov     r12, [rsp+0x140]
        not     r12
        shld    r13, r12, 0x3
        mov     r11, [rsp+0x138]
        not     r11
        shld    r12, r11, 0x3
        mov     r10, [rsp+0x130]
        not     r10
        shld    r11, r10, 0x3
        mov     r9, [rsp+0x128]
        not     r9
        shld    r10, r9, 0x3
        mov     r8, [rsp+0x120]
        not     r8
        shld    r9, r8, 0x3
        shl     r8, 0x3
        mov     ecx, 0x3
        mov     rax, [rsp+0x168]
        mul     rcx
        add     r8, rax
        adc     r9, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x170]
        mul     rcx
        sub     rdx, rbp
        add     r9, rax
        adc     r10, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x178]
        mul     rcx
        sub     rdx, rbp
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x180]
        mul     rcx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x188]
        mul     rcx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x190]
        mul     rcx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x198]
        mul     rcx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x1a0]
        mul     rcx
        sub     rdx, rbp
        add     r15, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x1a8]
        imul    rax, rcx
        add     rbx, rax
        mov     rax, r9
        and     rax, r10
        and     rax, r11
        and     rax, r12
        and     rax, r13
        and     rax, r14
        and     rax, r15
        mov     rdx, rbx
        shr     rdx, 0x9
        or      rbx, 0xfffffffffffffe00
        lea     rcx, [rdx+0x1]
        add     rcx, r8
        mov     ecx, 0x0
        adc     rax, rcx
        mov     rax, rbx
        adc     rax, rcx
        adc     r8, rdx
        mov     [rdi+0x48], r8
        adc     r9, rcx
        mov     [rdi+0x50], r9
        adc     r10, rcx
        mov     [rdi+0x58], r10
        adc     r11, rcx
        mov     [rdi+0x60], r11
        adc     r12, rcx
        mov     [rdi+0x68], r12
        adc     r13, rcx
        mov     [rdi+0x70], r13
        adc     r14, rcx
        mov     [rdi+0x78], r14
        adc     r15, rcx
        mov     [rdi+0x80], r15
        adc     rbx, rcx
        and     rbx, 0x1ff
        mov     [rdi+0x88], rbx
        CFI_INC_RSP(520)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp521_jscalarmul_alt_jdouble)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp521_jscalarmul_alt_mul_p521)

Lp521_jscalarmul_alt_mul_p521:
        CFI_START
        CFI_DEC_RSP(72)
        mov     rcx, rdx
        mov     rax, [rsi]
        mul     QWORD PTR [rcx]
        mov     [rsp], rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x8]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        mov     [rsp+0x8], r9
        xor     r12, r12
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x10]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x8]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     [rsp+0x10], r10
        xor     r13, r13
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x18]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x10]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x8]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     [rsp+0x18], r11
        xor     r14, r14
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x20]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x18]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x10]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x8]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rcx]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     [rsp+0x20], r12
        xor     r15, r15
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x28]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x20]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x18]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x10]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rcx+0x8]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rcx]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     [rsp+0x28], r13
        xor     r8, r8
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x30]
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x28]
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x20]
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x18]
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rcx+0x10]
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rcx+0x8]
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rcx]
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     [rsp+0x30], r14
        xor     r9, r9
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x38]
        add     r15, rax
        adc     r8, rdx
        adc     r9, r9
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x30]
        add     r15, rax
        adc     r8, rdx
        adc     r9, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x28]
        add     r15, rax
        adc     r8, rdx
        adc     r9, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x20]
        add     r15, rax
        adc     r8, rdx
        adc     r9, 0x0
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rcx+0x18]
        add     r15, rax
        adc     r8, rdx
        adc     r9, 0x0
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rcx+0x10]
        add     r15, rax
        adc     r8, rdx
        adc     r9, 0x0
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rcx+0x8]
        add     r15, rax
        adc     r8, rdx
        adc     r9, 0x0
        mov     rax, [rsi+0x38]
        mul     QWORD PTR [rcx]
        add     r15, rax
        adc     r8, rdx
        adc     r9, 0x0
        mov     [rsp+0x38], r15
        xor     r10, r10
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x40]
        add     r8, rax
        adc     r9, rdx
        adc     r10, r10
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x38]
        add     r8, rax
        adc     r9, rdx
        adc     r10, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x30]
        add     r8, rax
        adc     r9, rdx
        adc     r10, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x28]
        add     r8, rax
        adc     r9, rdx
        adc     r10, 0x0
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rcx+0x20]
        add     r8, rax
        adc     r9, rdx
        adc     r10, 0x0
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rcx+0x18]
        add     r8, rax
        adc     r9, rdx
        adc     r10, 0x0
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rcx+0x10]
        add     r8, rax
        adc     r9, rdx
        adc     r10, 0x0
        mov     rax, [rsi+0x38]
        mul     QWORD PTR [rcx+0x8]
        add     r8, rax
        adc     r9, rdx
        adc     r10, 0x0
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rcx]
        add     r8, rax
        adc     r9, rdx
        adc     r10, 0x0
        mov     [rsp+0x40], r8
        xor     r11, r11
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x40]
        add     r9, rax
        adc     r10, rdx
        adc     r11, r11
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x38]
        add     r9, rax
        adc     r10, rdx
        adc     r11, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x30]
        add     r9, rax
        adc     r10, rdx
        adc     r11, 0x0
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rcx+0x28]
        add     r9, rax
        adc     r10, rdx
        adc     r11, 0x0
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rcx+0x20]
        add     r9, rax
        adc     r10, rdx
        adc     r11, 0x0
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rcx+0x18]
        add     r9, rax
        adc     r10, rdx
        adc     r11, 0x0
        mov     rax, [rsi+0x38]
        mul     QWORD PTR [rcx+0x10]
        add     r9, rax
        adc     r10, rdx
        adc     r11, 0x0
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rcx+0x8]
        add     r9, rax
        adc     r10, rdx
        adc     r11, 0x0
        xor     r12, r12
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x40]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x38]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rcx+0x30]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rcx+0x28]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rcx+0x20]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x38]
        mul     QWORD PTR [rcx+0x18]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rcx+0x10]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x40]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rcx+0x38]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rcx+0x30]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rcx+0x28]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x38]
        mul     QWORD PTR [rcx+0x20]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rcx+0x18]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rcx+0x40]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rcx+0x38]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rcx+0x30]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x38]
        mul     QWORD PTR [rcx+0x28]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rcx+0x20]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rcx+0x40]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rcx+0x38]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x38]
        mul     QWORD PTR [rcx+0x30]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rcx+0x28]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        xor     r8, r8
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rcx+0x40]
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        mov     rax, [rsi+0x38]
        mul     QWORD PTR [rcx+0x38]
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rcx+0x30]
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     rax, [rsi+0x38]
        mul     QWORD PTR [rcx+0x40]
        add     r15, rax
        adc     r8, rdx
        mov     rax, [rsi+0x40]
        mul     QWORD PTR [rcx+0x38]
        add     r15, rax
        adc     r8, rdx
        mov     rax, [rsi+0x40]
        imul    rax, [rcx+0x40]
        add     rax, r8
        mov     r8, [rsp+0x40]
        mov     rdx, r8
        and     rdx, 0x1ff
        shrd    r8, r9, 0x9
        shrd    r9, r10, 0x9
        shrd    r10, r11, 0x9
        shrd    r11, r12, 0x9
        shrd    r12, r13, 0x9
        shrd    r13, r14, 0x9
        shrd    r14, r15, 0x9
        shrd    r15, rax, 0x9
        shr     rax, 0x9
        add     rdx, rax
        stc
        adc     r8, [rsp]
        adc     r9, [rsp+0x8]
        adc     r10, [rsp+0x10]
        adc     r11, [rsp+0x18]
        adc     r12, [rsp+0x20]
        adc     r13, [rsp+0x28]
        adc     r14, [rsp+0x30]
        adc     r15, [rsp+0x38]
        adc     rdx, 0xfffffffffffffe00
        cmc
        sbb     r8, 0x0
        mov     [rdi], r8
        sbb     r9, 0x0
        mov     [rdi+0x8], r9
        sbb     r10, 0x0
        mov     [rdi+0x10], r10
        sbb     r11, 0x0
        mov     [rdi+0x18], r11
        sbb     r12, 0x0
        mov     [rdi+0x20], r12
        sbb     r13, 0x0
        mov     [rdi+0x28], r13
        sbb     r14, 0x0
        mov     [rdi+0x30], r14
        sbb     r15, 0x0
        mov     [rdi+0x38], r15
        sbb     rdx, 0x0
        and     rdx, 0x1ff
        mov     [rdi+0x40], rdx
        CFI_INC_RSP(72)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp521_jscalarmul_alt_mul_p521)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp521_jscalarmul_alt_sqr_p521)

Lp521_jscalarmul_alt_sqr_p521:
        CFI_START
        CFI_DEC_RSP(72)
        mov     rax, [rsi]
        mul     rax
        mov     [rsp], rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsi]
        mul     QWORD PTR [rsi+0x8]
        add     rax, rax
        adc     rdx, rdx
        adc     r11, 0x0
        add     r9, rax
        adc     r10, rdx
        adc     r11, 0x0
        mov     [rsp+0x8], r9
        xor     r12, r12
        mov     rax, [rsi+0x8]
        mul     rax
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi]
        mul     QWORD PTR [rsi+0x10]
        add     rax, rax
        adc     rdx, rdx
        adc     r12, 0x0
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     [rsp+0x10], r10
        mov     rax, [rsi]
        mul     QWORD PTR [rsi+0x18]
        xor     r13, r13
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsi+0x10]
        add     rbx, rax
        adc     rcx, rdx
        adc     r13, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r13, r13
        add     r11, rbx
        adc     r12, rcx
        adc     r13, 0x0
        mov     [rsp+0x18], r11
        mov     rax, [rsi]
        mul     QWORD PTR [rsi+0x20]
        xor     r14, r14
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsi+0x18]
        add     rbx, rax
        adc     rcx, rdx
        adc     r14, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r14, r14
        add     r12, rbx
        adc     r13, rcx
        adc     r14, 0x0
        mov     rax, [rsi+0x10]
        mul     rax
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     [rsp+0x20], r12
        mov     rax, [rsi]
        mul     QWORD PTR [rsi+0x28]
        xor     r15, r15
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsi+0x20]
        add     rbx, rax
        adc     rcx, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rsi+0x18]
        add     rbx, rax
        adc     rcx, rdx
        adc     r15, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r15, r15
        add     r13, rbx
        adc     r14, rcx
        adc     r15, 0x0
        mov     [rsp+0x28], r13
        mov     rax, [rsi]
        mul     QWORD PTR [rsi+0x30]
        xor     r8, r8
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsi+0x28]
        add     rbx, rax
        adc     rcx, rdx
        adc     r8, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rsi+0x20]
        add     rbx, rax
        adc     rcx, rdx
        adc     r8, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r8, r8
        add     r14, rbx
        adc     r15, rcx
        adc     r8, 0x0
        mov     rax, [rsi+0x18]
        mul     rax
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     [rsp+0x30], r14
        mov     rax, [rsi]
        mul     QWORD PTR [rsi+0x38]
        xor     r9, r9
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsi+0x30]
        add     rbx, rax
        adc     rcx, rdx
        adc     r9, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rsi+0x28]
        add     rbx, rax
        adc     rcx, rdx
        adc     r9, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rsi+0x20]
        add     rbx, rax
        adc     rcx, rdx
        adc     r9, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r9, r9
        add     r15, rbx
        adc     r8, rcx
        adc     r9, 0x0
        mov     [rsp+0x38], r15
        mov     rax, [rsi]
        mul     QWORD PTR [rsi+0x40]
        xor     r10, r10
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsi+0x38]
        add     rbx, rax
        adc     rcx, rdx
        adc     r10, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rsi+0x30]
        add     rbx, rax
        adc     rcx, rdx
        adc     r10, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rsi+0x28]
        add     rbx, rax
        adc     rcx, rdx
        adc     r10, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r10, r10
        add     r8, rbx
        adc     r9, rcx
        adc     r10, 0x0
        mov     rax, [rsi+0x20]
        mul     rax
        add     r8, rax
        adc     r9, rdx
        adc     r10, 0x0
        mov     [rsp+0x40], r8
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rsi+0x40]
        xor     r11, r11
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rsi+0x38]
        add     rbx, rax
        adc     rcx, rdx
        adc     r11, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rsi+0x30]
        add     rbx, rax
        adc     rcx, rdx
        adc     r11, 0x0
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rsi+0x28]
        add     rbx, rax
        adc     rcx, rdx
        adc     r11, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r11, r11
        add     r9, rbx
        adc     r10, rcx
        adc     r11, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rsi+0x40]
        xor     r12, r12
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rsi+0x38]
        add     rbx, rax
        adc     rcx, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rsi+0x30]
        add     rbx, rax
        adc     rcx, rdx
        adc     r12, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r12, r12
        add     r10, rbx
        adc     r11, rcx
        adc     r12, 0x0
        mov     rax, [rsi+0x28]
        mul     rax
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rsi+0x40]
        xor     r13, r13
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rsi+0x38]
        add     rbx, rax
        adc     rcx, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rsi+0x30]
        add     rbx, rax
        adc     rcx, rdx
        adc     r13, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r13, r13
        add     r11, rbx
        adc     r12, rcx
        adc     r13, 0x0
        mov     rax, [rsi+0x20]
        mul     QWORD PTR [rsi+0x40]
        xor     r14, r14
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rsi+0x38]
        add     rbx, rax
        adc     rcx, rdx
        adc     r14, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r14, r14
        add     r12, rbx
        adc     r13, rcx
        adc     r14, 0x0
        mov     rax, [rsi+0x30]
        mul     rax
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x28]
        mul     QWORD PTR [rsi+0x40]
        xor     r15, r15
        mov     rbx, rax
        mov     rcx, rdx
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rsi+0x38]
        add     rbx, rax
        adc     rcx, rdx
        adc     r15, 0x0
        add     rbx, rbx
        adc     rcx, rcx
        adc     r15, r15
        add     r13, rbx
        adc     r14, rcx
        adc     r15, 0x0
        xor     r8, r8
        mov     rax, [rsi+0x38]
        mul     rax
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     rax, [rsi+0x30]
        mul     QWORD PTR [rsi+0x40]
        add     rax, rax
        adc     rdx, rdx
        adc     r8, 0x0
        add     r14, rax
        adc     r15, rdx
        adc     r8, 0x0
        mov     rax, [rsi+0x38]
        mul     QWORD PTR [rsi+0x40]
        add     rax, rax
        adc     rdx, rdx
        add     r15, rax
        adc     r8, rdx
        mov     rax, [rsi+0x40]
        imul    rax, rax
        add     rax, r8
        mov     r8, [rsp+0x40]
        mov     rdx, r8
        and     rdx, 0x1ff
        shrd    r8, r9, 0x9
        shrd    r9, r10, 0x9
        shrd    r10, r11, 0x9
        shrd    r11, r12, 0x9
        shrd    r12, r13, 0x9
        shrd    r13, r14, 0x9
        shrd    r14, r15, 0x9
        shrd    r15, rax, 0x9
        shr     rax, 0x9
        add     rdx, rax
        stc
        adc     r8, [rsp]
        adc     r9, [rsp+0x8]
        adc     r10, [rsp+0x10]
        adc     r11, [rsp+0x18]
        adc     r12, [rsp+0x20]
        adc     r13, [rsp+0x28]
        adc     r14, [rsp+0x30]
        adc     r15, [rsp+0x38]
        adc     rdx, 0xfffffffffffffe00
        cmc
        sbb     r8, 0x0
        mov     [rdi], r8
        sbb     r9, 0x0
        mov     [rdi+0x8], r9
        sbb     r10, 0x0
        mov     [rdi+0x10], r10
        sbb     r11, 0x0
        mov     [rdi+0x18], r11
        sbb     r12, 0x0
        mov     [rdi+0x20], r12
        sbb     r13, 0x0
        mov     [rdi+0x28], r13
        sbb     r14, 0x0
        mov     [rdi+0x30], r14
        sbb     r15, 0x0
        mov     [rdi+0x38], r15
        sbb     rdx, 0x0
        and     rdx, 0x1ff
        mov     [rdi+0x40], rdx
        CFI_INC_RSP(72)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp521_jscalarmul_alt_sqr_p521)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
