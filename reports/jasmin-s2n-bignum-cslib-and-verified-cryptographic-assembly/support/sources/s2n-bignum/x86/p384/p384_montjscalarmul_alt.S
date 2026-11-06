// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery-Jacobian form scalar multiplication for P-384
// Input scalar[6], point[18]; output res[18]
//
// extern void p384_montjscalarmul_alt
//   (uint64_t res[static 18],
//    const uint64_t scalar[static 6],
//    const uint64_t point[static 18]);
//
// This function is a variant of its affine point version p384_scalarmul.
// Here, input and output points are assumed to be in Jacobian form with
// their coordinates in the Montgomery domain. Thus, if priming indicates
// Montgomery form, x' = (2^384 * x) mod p_384 etc., each point argument
// is a triple (x',y',z') representing the affine point (x/z^2,y/z^3) when
// z' is nonzero or the point at infinity (group identity) if z' = 0.
//
// Given scalar = n and point = P, assumed to be on the NIST elliptic
// curve P-384, returns a representation of n * P. If the result is the
// point at infinity (either because the input point was or because the
// scalar was a multiple of p_384) then the output is guaranteed to
// represent the point at infinity, i.e. to have its z coordinate zero.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p384_montjscalarmul_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p384_montjscalarmul_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p384_montjscalarmul_alt)


        .text
        .balign 32

// Size of individual field elements

#define NUMSIZE 48
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

#define selectblock_xz(I)                         \
        cmp     rdi, I;                           \
        cmovz   rax, [rsp+TAB+JACSIZE*(I-1)];     \
        cmovz   rbx, [rsp+TAB+JACSIZE*(I-1)+8];   \
        cmovz   rcx, [rsp+TAB+JACSIZE*(I-1)+16];  \
        cmovz   rdx, [rsp+TAB+JACSIZE*(I-1)+24];  \
        cmovz   r8, [rsp+TAB+JACSIZE*(I-1)+32];   \
        cmovz   r9, [rsp+TAB+JACSIZE*(I-1)+40];   \
        cmovz   r10, [rsp+TAB+JACSIZE*(I-1)+96];  \
        cmovz   r11, [rsp+TAB+JACSIZE*(I-1)+104]; \
        cmovz   r12, [rsp+TAB+JACSIZE*(I-1)+112]; \
        cmovz   r13, [rsp+TAB+JACSIZE*(I-1)+120]; \
        cmovz   r14, [rsp+TAB+JACSIZE*(I-1)+128]; \
        cmovz   r15, [rsp+TAB+JACSIZE*(I-1)+136]

#define selectblock_y(I)                          \
        cmp     rdi, I;                           \
        cmovz   rax, [rsp+TAB+JACSIZE*(I-1)+48];  \
        cmovz   rbx, [rsp+TAB+JACSIZE*(I-1)+56];  \
        cmovz   rcx, [rsp+TAB+JACSIZE*(I-1)+64];  \
        cmovz   rdx, [rsp+TAB+JACSIZE*(I-1)+72];  \
        cmovz   r8, [rsp+TAB+JACSIZE*(I-1)+80];   \
        cmovz   r9, [rsp+TAB+JACSIZE*(I-1)+88]

S2N_BN_SYMBOL(p384_montjscalarmul_alt):
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
        CFI_CALL(Lp384_montjscalarmul_alt_standard)
        CFI_POP(rsi)
        CFI_POP(rdi)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(p384_montjscalarmul_alt)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp384_montjscalarmul_alt_standard)

Lp384_montjscalarmul_alt_standard:
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

// Reduce the input scalar mod n_384, i.e. conditionally subtract n_384.
// Store it to "scalarb".

        mov     r8, [rsi]
        mov     rax, 0xecec196accc52973
        sub     r8, rax
        mov     r9, [rsi+8]
        mov     rax, 0x581a0db248b0a77a
        sbb     r9, rax
        mov     r10, [rsi+16]
        mov     rax, 0xc7634d81f4372ddf
        sbb     r10, rax
        mov     r11, [rsi+24]
        mov     rax, 0xffffffffffffffff
        sbb     r11, rax
        mov     r12, [rsi+32]
        sbb     r12, rax
        mov     r13, [rsi+40]
        sbb     r13, rax

        cmovc   r8, [rsi]
        cmovc   r9, [rsi+8]
        cmovc   r10, [rsi+16]
        cmovc   r11, [rsi+24]
        cmovc   r12, [rsi+32]
        cmovc   r13, [rsi+40]

        mov     [rsp+SCALARB], r8
        mov     [rsp+SCALARB+8], r9
        mov     [rsp+SCALARB+16], r10
        mov     [rsp+SCALARB+24], r11
        mov     [rsp+SCALARB+32], r12
        mov     [rsp+SCALARB+40], r13

// Set the tab[0] table entry to the input point = 1 * P

        mov     rax, [rdx]
        mov     [rsp+TAB], rax
        mov     rax, [rdx+8]
        mov     [rsp+TAB+8], rax
        mov     rax, [rdx+16]
        mov     [rsp+TAB+16], rax
        mov     rax, [rdx+24]
        mov     [rsp+TAB+24], rax
        mov     rax, [rdx+32]
        mov     [rsp+TAB+32], rax
        mov     rax, [rdx+40]
        mov     [rsp+TAB+40], rax

        mov     rax, [rdx+48]
        mov     [rsp+TAB+48], rax
        mov     rax, [rdx+56]
        mov     [rsp+TAB+56], rax
        mov     rax, [rdx+64]
        mov     [rsp+TAB+64], rax
        mov     rax, [rdx+72]
        mov     [rsp+TAB+72], rax
        mov     rax, [rdx+80]
        mov     [rsp+TAB+80], rax
        mov     rax, [rdx+88]
        mov     [rsp+TAB+88], rax

        mov     rax, [rdx+96]
        mov     [rsp+TAB+96], rax
        mov     rax, [rdx+104]
        mov     [rsp+TAB+104], rax
        mov     rax, [rdx+112]
        mov     [rsp+TAB+112], rax
        mov     rax, [rdx+120]
        mov     [rsp+TAB+120], rax
        mov     rax, [rdx+128]
        mov     [rsp+TAB+128], rax
        mov     rax, [rdx+136]
        mov     [rsp+TAB+136], rax

// Compute and record tab[1] = 2 * p, ..., tab[15] = 16 * P

        lea     rdi, [rsp+TAB+JACSIZE*1]
        lea     rsi, [rsp+TAB]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rdi, [rsp+TAB+JACSIZE*2]
        lea     rsi, [rsp+TAB+JACSIZE*1]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjadd)

        lea     rdi, [rsp+TAB+JACSIZE*3]
        lea     rsi, [rsp+TAB+JACSIZE*1]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rdi, [rsp+TAB+JACSIZE*4]
        lea     rsi, [rsp+TAB+JACSIZE*3]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjadd)

        lea     rdi, [rsp+TAB+JACSIZE*5]
        lea     rsi, [rsp+TAB+JACSIZE*2]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rdi, [rsp+TAB+JACSIZE*6]
        lea     rsi, [rsp+TAB+JACSIZE*5]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjadd)

        lea     rdi, [rsp+TAB+JACSIZE*7]
        lea     rsi, [rsp+TAB+JACSIZE*3]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rdi, [rsp+TAB+JACSIZE*8]
        lea     rsi, [rsp+TAB+JACSIZE*7]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjadd)

        lea     rdi, [rsp+TAB+JACSIZE*9]
        lea     rsi, [rsp+TAB+JACSIZE*4]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rdi, [rsp+TAB+JACSIZE*10]
        lea     rsi, [rsp+TAB+JACSIZE*9]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjadd)

        lea     rdi, [rsp+TAB+JACSIZE*11]
        lea     rsi, [rsp+TAB+JACSIZE*5]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rdi, [rsp+TAB+JACSIZE*12]
        lea     rsi, [rsp+TAB+JACSIZE*11]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjadd)

        lea     rdi, [rsp+TAB+JACSIZE*13]
        lea     rsi, [rsp+TAB+JACSIZE*6]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rdi, [rsp+TAB+JACSIZE*14]
        lea     rsi, [rsp+TAB+JACSIZE*13]
        lea     rdx, [rsp+TAB]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjadd)

        lea     rdi, [rsp+TAB+JACSIZE*15]
        lea     rsi, [rsp+TAB+JACSIZE*7]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

// Add the recoding constant sum_i(16 * 32^i) to the scalar to allow signed
// digits. The digits of the constant, in lowest-to-highest order, are as
// follows; they are generated dynamically to use fewer large constant loads.
//
// 0x0842108421084210
// 0x1084210842108421
// 0x2108421084210842
// 0x4210842108421084
// 0x8421084210842108
// 0x0842108421084210

        mov     rax, 0x1084210842108421
        mov     rcx, rax
        shr     rax, 1
        mov     r8, [rsp+SCALARB]
        add     r8, rax
        mov     r9, [rsp+SCALARB+8]
        adc     r9, rcx
        lea     rcx, [rcx+rcx]
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
        sbb     rdi, rdi
        neg     rdi

// Record the top bitfield in rdi then shift the whole scalar left 4 bits
// to align the top of the next bitfield with the MSB (bits 379..383).

        shld    rdi, r13, 4
        shld    r13, r12, 4
        shld    r12, r11, 4
        shld    r11, r10, 4
        shld    r10, r9, 4
        shld    r9, r8, 4
        shl     r8, 4

        mov     [rsp+SCALARB], r8
        mov     [rsp+SCALARB+8], r9
        mov     [rsp+SCALARB+16], r10
        mov     [rsp+SCALARB+24], r11
        mov     [rsp+SCALARB+32], r12
        mov     [rsp+SCALARB+40], r13

// Initialize the accumulator to the corresponding entry using constant-time
// lookup in the table. This top digit, uniquely, is not recoded so there is
// no sign adjustment to make. On the x86 integer side we don't have enough
// registers to hold all the fields; this could be better done with SIMD
// registers anyway. So we do x and z coordinates in one sweep, y in another
// (this is a rehearsal for below where we might need to negate the y).

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        xor     r13d, r13d
        xor     r14d, r14d
        xor     r15d, r15d

        selectblock_xz(1)
        selectblock_xz(2)
        selectblock_xz(3)
        selectblock_xz(4)
        selectblock_xz(5)
        selectblock_xz(6)
        selectblock_xz(7)
        selectblock_xz(8)
        selectblock_xz(9)
        selectblock_xz(10)
        selectblock_xz(11)
        selectblock_xz(12)
        selectblock_xz(13)
        selectblock_xz(14)
        selectblock_xz(15)
        selectblock_xz(16)

        mov      [rsp+ACC], rax
        mov      [rsp+ACC+8], rbx
        mov      [rsp+ACC+16], rcx
        mov      [rsp+ACC+24], rdx
        mov      [rsp+ACC+32], r8
        mov      [rsp+ACC+40], r9
        mov      [rsp+ACC+96], r10
        mov      [rsp+ACC+104], r11
        mov      [rsp+ACC+112], r12
        mov      [rsp+ACC+120], r13
        mov      [rsp+ACC+128], r14
        mov      [rsp+ACC+136], r15

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d

        selectblock_y(1)
        selectblock_y(2)
        selectblock_y(3)
        selectblock_y(4)
        selectblock_y(5)
        selectblock_y(6)
        selectblock_y(7)
        selectblock_y(8)
        selectblock_y(9)
        selectblock_y(10)
        selectblock_y(11)
        selectblock_y(12)
        selectblock_y(13)
        selectblock_y(14)
        selectblock_y(15)
        selectblock_y(16)

        mov      [rsp+ACC+48], rax
        mov      [rsp+ACC+56], rbx
        mov      [rsp+ACC+64], rcx
        mov      [rsp+ACC+72], rdx
        mov      [rsp+ACC+80], r8
        mov      [rsp+ACC+88], r9

// Main loop over size-5 bitfields: double 5 times then add signed digit
// At each stage we shift the scalar left by 5 bits so we can simply pick
// the top 5 bits as the bitfield, saving some fiddle over indexing.

        mov     ebp, 380

Lp384_montjscalarmul_alt_mainloop:
        sub     rbp, 5

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjdouble)

// Choose the bitfield and adjust it to sign and magnitude

        mov     r8, [rsp+SCALARB]
        mov     r9, [rsp+SCALARB+8]
        mov     r10, [rsp+SCALARB+16]
        mov     r11, [rsp+SCALARB+24]
        mov     r12, [rsp+SCALARB+32]
        mov     r13, [rsp+SCALARB+40]

        mov     rdi, r13
        shr     rdi, 59
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

        sub     rdi, 16
        sbb     rsi, rsi        // rsi = sign of digit (-1 = negative)
        xor     rdi, rsi
        sub     rdi, rsi        // rdi = absolute value of digit

// Conditionally select the table entry tab[i-1] = i * P in constant time
// Again, this is done in two sweeps, first doing x and z then y.

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d
        xor     r10d, r10d
        xor     r11d, r11d
        xor     r12d, r12d
        xor     r13d, r13d
        xor     r14d, r14d
        xor     r15d, r15d

selectblock_xz(1)
        selectblock_xz(2)
        selectblock_xz(3)
        selectblock_xz(4)
        selectblock_xz(5)
        selectblock_xz(6)
        selectblock_xz(7)
        selectblock_xz(8)
        selectblock_xz(9)
        selectblock_xz(10)
        selectblock_xz(11)
        selectblock_xz(12)
        selectblock_xz(13)
        selectblock_xz(14)
        selectblock_xz(15)
        selectblock_xz(16)

        mov      [rsp+TABENT], rax
        mov      [rsp+TABENT+8], rbx
        mov      [rsp+TABENT+16], rcx
        mov      [rsp+TABENT+24], rdx
        mov      [rsp+TABENT+32], r8
        mov      [rsp+TABENT+40], r9
        mov      [rsp+TABENT+96], r10
        mov      [rsp+TABENT+104], r11
        mov      [rsp+TABENT+112], r12
        mov      [rsp+TABENT+120], r13
        mov      [rsp+TABENT+128], r14
        mov      [rsp+TABENT+136], r15

        xor     eax, eax
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        xor     r8d, r8d
        xor     r9d, r9d

        selectblock_y(1)
        selectblock_y(2)
        selectblock_y(3)
        selectblock_y(4)
        selectblock_y(5)
        selectblock_y(6)
        selectblock_y(7)
        selectblock_y(8)
        selectblock_y(9)
        selectblock_y(10)
        selectblock_y(11)
        selectblock_y(12)
        selectblock_y(13)
        selectblock_y(14)
        selectblock_y(15)
        selectblock_y(16)

// Store it to "tabent" with the y coordinate optionally negated.
// This is done carefully to give coordinates < p_384 even in
// the degenerate case y = 0 (when z = 0 for points on the curve).
// The digits of the prime p_384 are generated dynamically from
// the zeroth via not/lea to reduce the number of constant loads.

        mov     r10, rax
        or      r10, rbx
        mov     r11, rcx
        or      r11, rdx
        mov     r12, r8
        or      r12, r9
        or      r10, r11
        or      r10, r12
        cmovz   rsi, r10

        mov     r10d, 0xffffffff
        mov     r11, r10
        not     r11
        lea     r13, [r10+r11]
        sub     r10, rax
        lea     r12, [r13-1]
        sbb     r11, rbx
        mov     r14, r13
        sbb     r12, rcx
        sbb     r13, rdx
        mov     r15, r14
        sbb     r14, r8
        sbb     r15, r9

        test    rsi, rsi
        cmovnz   rax, r10
        cmovnz   rbx, r11
        cmovnz   rcx, r12
        cmovnz   rdx, r13
        cmovnz   r8, r14
        cmovnz   r9, r15

        mov     [rsp+TABENT+48], rax
        mov     [rsp+TABENT+56], rbx
        mov     [rsp+TABENT+64], rcx
        mov     [rsp+TABENT+72], rdx
        mov     [rsp+TABENT+80], r8
        mov     [rsp+TABENT+88], r9

// Add to the accumulator

        lea     rdx, [rsp+TABENT]
        lea     rsi, [rsp+ACC]
        lea     rdi, [rsp+ACC]
        CFI_CALL(Lp384_montjscalarmul_alt_p384_montjadd)

        test    rbp, rbp
        jne     Lp384_montjscalarmul_alt_mainloop

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
S2N_BN_SIZE_DIRECTIVE(Lp384_montjscalarmul_alt_standard)
#else
S2N_BN_SIZE_DIRECTIVE(p384_montjscalarmul_alt)
#endif

// Local copies of subroutines, complete clones at the moment

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp384_montjscalarmul_alt_p384_montjadd)

Lp384_montjscalarmul_alt_p384_montjadd:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(352)
        mov     [rsp+0x150], rsi
        mov     [rsp+0x158], rdx
        mov     rbx, [rsi+0x60]
        mov     rax, [rsi+0x68]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x78]
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x88]
        mul     rbx
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi+0x78]
        mul     QWORD PTR [rsi+0x80]
        mov     r15, rax
        mov     rcx, rdx
        mov     rbx, [rsi+0x70]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x68]
        mul     rbx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rbx, [rsi+0x68]
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        adc     rcx, 0x0
        mov     rbx, [rsi+0x80]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rbx, [rsi+0x70]
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, rbp
        add     r15, rax
        adc     rcx, rdx
        sbb     rbp, rbp
        xor     ebx, ebx
        mov     rax, [rsi+0x78]
        mul     QWORD PTR [rsi+0x88]
        sub     rdx, rbp
        xor     ebp, ebp
        add     rcx, rax
        adc     rbx, rdx
        adc     ebp, ebp
        mov     rax, [rsi+0x80]
        mul     QWORD PTR [rsi+0x88]
        add     rbx, rax
        adc     rbp, rdx
        xor     r8d, r8d
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     r15, r15
        adc     rcx, rcx
        adc     rbx, rbx
        adc     rbp, rbp
        adc     r8d, r8d
        mov     rax, [rsi+0x60]
        mul     rax
        mov     [rsp], r8
        mov     r8, rax
        mov     rax, [rsi+0x68]
        mov     [rsp+0x8], rbp
        add     r9, rdx
        sbb     rbp, rbp
        mul     rax
        neg     rbp
        adc     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x70]
        mul     rax
        neg     rbp
        adc     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x78]
        mul     rax
        neg     rbp
        adc     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x80]
        mul     rax
        neg     rbp
        adc     rcx, rax
        adc     rbx, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x88]
        mul     rax
        neg     rbp
        adc     rax, [rsp+0x8]
        adc     rdx, [rsp]
        mov     rbp, rax
        mov     rsi, rdx
        mov     [rsp], rbx
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r8, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r9, r8
        sbb     r10, rdx
        sbb     r11, rax
        sbb     r12, 0x0
        sbb     r13, 0x0
        mov     r8, rbx
        sbb     r8, 0x0
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r9, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r10, r9
        sbb     r11, rdx
        sbb     r12, rax
        sbb     r13, 0x0
        sbb     r8, 0x0
        mov     r9, rbx
        sbb     r9, 0x0
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r10, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r11, r10
        sbb     r12, rdx
        sbb     r13, rax
        sbb     r8, 0x0
        sbb     r9, 0x0
        mov     r10, rbx
        sbb     r10, 0x0
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r11, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r12, r11
        sbb     r13, rdx
        sbb     r8, rax
        sbb     r9, 0x0
        sbb     r10, 0x0
        mov     r11, rbx
        sbb     r11, 0x0
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r12, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r13, r12
        sbb     r8, rdx
        sbb     r9, rax
        sbb     r10, 0x0
        sbb     r11, 0x0
        mov     r12, rbx
        sbb     r12, 0x0
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r13, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r8, r13
        sbb     r9, rdx
        sbb     r10, rax
        sbb     r11, 0x0
        sbb     r12, 0x0
        mov     r13, rbx
        sbb     r13, 0x0
        mov     rbx, [rsp]
        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rsi, r13
        mov     r8d, 0x0
        adc     r8, r8
        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0xffffffff
        adc     r9, r15
        mov     r10d, 0x1
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rsi
        adc     r8, 0x0
        cmovne  r14, rax
        cmovne  r15, r9
        cmovne  rcx, r10
        cmovne  rbx, r11
        cmovne  rbp, r12
        cmovne  rsi, r13
        mov     [rsp], r14
        mov     [rsp+0x8], r15
        mov     [rsp+0x10], rcx
        mov     [rsp+0x18], rbx
        mov     [rsp+0x20], rbp
        mov     [rsp+0x28], rsi
        mov     rsi, [rsp+0x158]
        mov     rbx, [rsi+0x60]
        mov     rax, [rsi+0x68]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x78]
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x88]
        mul     rbx
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi+0x78]
        mul     QWORD PTR [rsi+0x80]
        mov     r15, rax
        mov     rcx, rdx
        mov     rbx, [rsi+0x70]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x68]
        mul     rbx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rbx, [rsi+0x68]
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        adc     rcx, 0x0
        mov     rbx, [rsi+0x80]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rbx, [rsi+0x70]
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, rbp
        add     r15, rax
        adc     rcx, rdx
        sbb     rbp, rbp
        xor     ebx, ebx
        mov     rax, [rsi+0x78]
        mul     QWORD PTR [rsi+0x88]
        sub     rdx, rbp
        xor     ebp, ebp
        add     rcx, rax
        adc     rbx, rdx
        adc     ebp, ebp
        mov     rax, [rsi+0x80]
        mul     QWORD PTR [rsi+0x88]
        add     rbx, rax
        adc     rbp, rdx
        xor     r8d, r8d
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     r15, r15
        adc     rcx, rcx
        adc     rbx, rbx
        adc     rbp, rbp
        adc     r8d, r8d
        mov     rax, [rsi+0x60]
        mul     rax
        mov     [rsp+0xf0], r8
        mov     r8, rax
        mov     rax, [rsi+0x68]
        mov     [rsp+0xf8], rbp
        add     r9, rdx
        sbb     rbp, rbp
        mul     rax
        neg     rbp
        adc     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x70]
        mul     rax
        neg     rbp
        adc     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x78]
        mul     rax
        neg     rbp
        adc     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x80]
        mul     rax
        neg     rbp
        adc     rcx, rax
        adc     rbx, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x88]
        mul     rax
        neg     rbp
        adc     rax, [rsp+0xf8]
        adc     rdx, [rsp+0xf0]
        mov     rbp, rax
        mov     rsi, rdx
        mov     [rsp+0xf0], rbx
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r8, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r9, r8
        sbb     r10, rdx
        sbb     r11, rax
        sbb     r12, 0x0
        sbb     r13, 0x0
        mov     r8, rbx
        sbb     r8, 0x0
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r9, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r10, r9
        sbb     r11, rdx
        sbb     r12, rax
        sbb     r13, 0x0
        sbb     r8, 0x0
        mov     r9, rbx
        sbb     r9, 0x0
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r10, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r11, r10
        sbb     r12, rdx
        sbb     r13, rax
        sbb     r8, 0x0
        sbb     r9, 0x0
        mov     r10, rbx
        sbb     r10, 0x0
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r11, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r12, r11
        sbb     r13, rdx
        sbb     r8, rax
        sbb     r9, 0x0
        sbb     r10, 0x0
        mov     r11, rbx
        sbb     r11, 0x0
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r12, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r13, r12
        sbb     r8, rdx
        sbb     r9, rax
        sbb     r10, 0x0
        sbb     r11, 0x0
        mov     r12, rbx
        sbb     r12, 0x0
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r13, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r8, r13
        sbb     r9, rdx
        sbb     r10, rax
        sbb     r11, 0x0
        sbb     r12, 0x0
        mov     r13, rbx
        sbb     r13, 0x0
        mov     rbx, [rsp+0xf0]
        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rsi, r13
        mov     r8d, 0x0
        adc     r8, r8
        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0xffffffff
        adc     r9, r15
        mov     r10d, 0x1
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rsi
        adc     r8, 0x0
        cmovne  r14, rax
        cmovne  r15, r9
        cmovne  rcx, r10
        cmovne  rbx, r11
        cmovne  rbp, r12
        cmovne  rsi, r13
        mov     [rsp+0xf0], r14
        mov     [rsp+0xf8], r15
        mov     [rsp+0x100], rcx
        mov     [rsp+0x108], rbx
        mov     [rsp+0x110], rbp
        mov     [rsp+0x118], rsi
        mov     rsi, [rsp+0x150]
        mov     rcx, [rsp+0x158]
        mov     rbx, [rsi+0x30]
        mov     rax, [rcx+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rcx+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rcx+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rcx+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rcx+0x80]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rcx+0x88]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsi+0x38]
        mov     rax, [rcx+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rcx+0x68]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rcx+0x70]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rcx+0x78]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rcx+0x80]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rcx+0x88]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsi+0x40]
        mov     rax, [rcx+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rcx+0x68]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rcx+0x70]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rcx+0x78]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rcx+0x80]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rcx+0x88]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsi+0x48]
        mov     rax, [rcx+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rcx+0x68]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rcx+0x70]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rcx+0x78]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rcx+0x80]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rcx+0x88]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsi+0x50]
        mov     rax, [rcx+0x60]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rcx+0x68]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rcx+0x70]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rcx+0x78]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rcx+0x80]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rcx+0x88]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsi+0x58]
        mov     rax, [rcx+0x60]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rcx+0x68]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rcx+0x70]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rcx+0x78]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rcx+0x80]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rcx+0x88]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0x120], r14
        mov     [rsp+0x128], r15
        mov     [rsp+0x130], r8
        mov     [rsp+0x138], r9
        mov     [rsp+0x140], r10
        mov     [rsp+0x148], r11
        mov     rsi, [rsp+0x150]
        mov     rcx, [rsp+0x158]
        mov     rbx, [rcx+0x30]
        mov     rax, [rsi+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsi+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsi+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsi+0x80]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsi+0x88]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rcx+0x38]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x68]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x70]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rcx+0x40]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x68]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x70]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rcx+0x48]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsi+0x68]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsi+0x70]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rcx+0x50]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsi+0x68]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsi+0x70]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rcx+0x58]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsi+0x68]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsi+0x70]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     [rsp+0x40], r8
        mov     [rsp+0x48], r9
        mov     [rsp+0x50], r10
        mov     [rsp+0x58], r11
        mov     rcx, [rsp+0x158]
        mov     rbx, [rcx]
        mov     rax, [rsp]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x10]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x18]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0x20]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x28]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rcx+0x8]
        mov     rax, [rsp]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x20]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rcx+0x10]
        mov     rax, [rsp]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x20]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rcx+0x18]
        mov     rax, [rsp]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x20]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rcx+0x20]
        mov     rax, [rsp]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x20]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rcx+0x28]
        mov     rax, [rsp]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x20]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0x60], r14
        mov     [rsp+0x68], r15
        mov     [rsp+0x70], r8
        mov     [rsp+0x78], r9
        mov     [rsp+0x80], r10
        mov     [rsp+0x88], r11
        mov     rsi, [rsp+0x150]
        mov     rbx, [rsi]
        mov     rax, [rsp+0xf0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xf8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x100]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x108]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0x110]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x118]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsi+0x8]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsi+0x10]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsi+0x18]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsi+0x20]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsi+0x28]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0xc0], r14
        mov     [rsp+0xc8], r15
        mov     [rsp+0xd0], r8
        mov     [rsp+0xd8], r9
        mov     [rsp+0xe0], r10
        mov     [rsp+0xe8], r11
        mov     rbx, [rsp+0x30]
        mov     rax, [rsp]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x10]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x18]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0x20]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x28]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsp+0x38]
        mov     rax, [rsp]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x20]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsp+0x40]
        mov     rax, [rsp]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x20]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsp+0x48]
        mov     rax, [rsp]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x20]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsp+0x50]
        mov     rax, [rsp]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x20]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsp+0x58]
        mov     rax, [rsp]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x20]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     [rsp+0x40], r8
        mov     [rsp+0x48], r9
        mov     [rsp+0x50], r10
        mov     [rsp+0x58], r11
        mov     rbx, [rsp+0x120]
        mov     rax, [rsp+0xf0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xf8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x100]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x108]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0x110]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x118]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsp+0x128]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsp+0x130]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsp+0x138]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsp+0x140]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsp+0x148]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0x120], r14
        mov     [rsp+0x128], r15
        mov     [rsp+0x130], r8
        mov     [rsp+0x138], r9
        mov     [rsp+0x140], r10
        mov     [rsp+0x148], r11
        mov     rax, [rsp+0x60]
        sub     rax, [rsp+0xc0]
        mov     rdx, [rsp+0x68]
        sbb     rdx, [rsp+0xc8]
        mov     r8, [rsp+0x70]
        sbb     r8, [rsp+0xd0]
        mov     r9, [rsp+0x78]
        sbb     r9, [rsp+0xd8]
        mov     r10, [rsp+0x80]
        sbb     r10, [rsp+0xe0]
        mov     r11, [rsp+0x88]
        sbb     r11, [rsp+0xe8]
        sbb     rcx, rcx
        mov     esi, 0xffffffff
        and     rcx, rsi
        xor     rsi, rsi
        sub     rsi, rcx
        sub     rax, rsi
        mov     [rsp+0xf0], rax
        sbb     rdx, rcx
        mov     [rsp+0xf8], rdx
        sbb     rax, rax
        and     rcx, rsi
        neg     rax
        sbb     r8, rcx
        mov     [rsp+0x100], r8
        sbb     r9, 0x0
        mov     [rsp+0x108], r9
        sbb     r10, 0x0
        mov     [rsp+0x110], r10
        sbb     r11, 0x0
        mov     [rsp+0x118], r11
        mov     rax, [rsp+0x30]
        sub     rax, [rsp+0x120]
        mov     rdx, [rsp+0x38]
        sbb     rdx, [rsp+0x128]
        mov     r8, [rsp+0x40]
        sbb     r8, [rsp+0x130]
        mov     r9, [rsp+0x48]
        sbb     r9, [rsp+0x138]
        mov     r10, [rsp+0x50]
        sbb     r10, [rsp+0x140]
        mov     r11, [rsp+0x58]
        sbb     r11, [rsp+0x148]
        sbb     rcx, rcx
        mov     esi, 0xffffffff
        and     rcx, rsi
        xor     rsi, rsi
        sub     rsi, rcx
        sub     rax, rsi
        mov     [rsp+0x30], rax
        sbb     rdx, rcx
        mov     [rsp+0x38], rdx
        sbb     rax, rax
        and     rcx, rsi
        neg     rax
        sbb     r8, rcx
        mov     [rsp+0x40], r8
        sbb     r9, 0x0
        mov     [rsp+0x48], r9
        sbb     r10, 0x0
        mov     [rsp+0x50], r10
        sbb     r11, 0x0
        mov     [rsp+0x58], r11
        mov     rbx, [rsp+0xf0]
        mov     rax, [rsp+0xf8]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x108]
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x118]
        mul     rbx
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x108]
        mul     QWORD PTR [rsp+0x110]
        mov     r15, rax
        mov     rcx, rdx
        mov     rbx, [rsp+0x100]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rbx, [rsp+0xf8]
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        adc     rcx, 0x0
        mov     rbx, [rsp+0x110]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rbx, [rsp+0x100]
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, rbp
        add     r15, rax
        adc     rcx, rdx
        sbb     rbp, rbp
        xor     ebx, ebx
        mov     rax, [rsp+0x108]
        mul     QWORD PTR [rsp+0x118]
        sub     rdx, rbp
        xor     ebp, ebp
        add     rcx, rax
        adc     rbx, rdx
        adc     ebp, ebp
        mov     rax, [rsp+0x110]
        mul     QWORD PTR [rsp+0x118]
        add     rbx, rax
        adc     rbp, rdx
        xor     r8d, r8d
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     r15, r15
        adc     rcx, rcx
        adc     rbx, rbx
        adc     rbp, rbp
        adc     r8d, r8d
        mov     rax, [rsp+0xf0]
        mul     rax
        mov     [rsp+0x90], r8
        mov     r8, rax
        mov     rax, [rsp+0xf8]
        mov     [rsp+0x98], rbp
        add     r9, rdx
        sbb     rbp, rbp
        mul     rax
        neg     rbp
        adc     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x100]
        mul     rax
        neg     rbp
        adc     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x108]
        mul     rax
        neg     rbp
        adc     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x110]
        mul     rax
        neg     rbp
        adc     rcx, rax
        adc     rbx, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x118]
        mul     rax
        neg     rbp
        adc     rax, [rsp+0x98]
        adc     rdx, [rsp+0x90]
        mov     rbp, rax
        mov     rsi, rdx
        mov     [rsp+0x90], rbx
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r8, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r9, r8
        sbb     r10, rdx
        sbb     r11, rax
        sbb     r12, 0x0
        sbb     r13, 0x0
        mov     r8, rbx
        sbb     r8, 0x0
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r9, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r10, r9
        sbb     r11, rdx
        sbb     r12, rax
        sbb     r13, 0x0
        sbb     r8, 0x0
        mov     r9, rbx
        sbb     r9, 0x0
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r10, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r11, r10
        sbb     r12, rdx
        sbb     r13, rax
        sbb     r8, 0x0
        sbb     r9, 0x0
        mov     r10, rbx
        sbb     r10, 0x0
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r11, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r12, r11
        sbb     r13, rdx
        sbb     r8, rax
        sbb     r9, 0x0
        sbb     r10, 0x0
        mov     r11, rbx
        sbb     r11, 0x0
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r12, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r13, r12
        sbb     r8, rdx
        sbb     r9, rax
        sbb     r10, 0x0
        sbb     r11, 0x0
        mov     r12, rbx
        sbb     r12, 0x0
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r13, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r8, r13
        sbb     r9, rdx
        sbb     r10, rax
        sbb     r11, 0x0
        sbb     r12, 0x0
        mov     r13, rbx
        sbb     r13, 0x0
        mov     rbx, [rsp+0x90]
        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rsi, r13
        mov     r8d, 0x0
        adc     r8, r8
        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0xffffffff
        adc     r9, r15
        mov     r10d, 0x1
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rsi
        adc     r8, 0x0
        cmovne  r14, rax
        cmovne  r15, r9
        cmovne  rcx, r10
        cmovne  rbx, r11
        cmovne  rbp, r12
        cmovne  rsi, r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     [rsp+0xa0], rcx
        mov     [rsp+0xa8], rbx
        mov     [rsp+0xb0], rbp
        mov     [rsp+0xb8], rsi
        mov     rbx, [rsp+0x30]
        mov     rax, [rsp+0x38]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x48]
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x58]
        mul     rbx
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x48]
        mul     QWORD PTR [rsp+0x50]
        mov     r15, rax
        mov     rcx, rdx
        mov     rbx, [rsp+0x40]
        mov     rax, [rsp+0x30]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rbx, [rsp+0x38]
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        adc     rcx, 0x0
        mov     rbx, [rsp+0x50]
        mov     rax, [rsp+0x30]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rbx, [rsp+0x40]
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, rbp
        add     r15, rax
        adc     rcx, rdx
        sbb     rbp, rbp
        xor     ebx, ebx
        mov     rax, [rsp+0x48]
        mul     QWORD PTR [rsp+0x58]
        sub     rdx, rbp
        xor     ebp, ebp
        add     rcx, rax
        adc     rbx, rdx
        adc     ebp, ebp
        mov     rax, [rsp+0x50]
        mul     QWORD PTR [rsp+0x58]
        add     rbx, rax
        adc     rbp, rdx
        xor     r8d, r8d
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     r15, r15
        adc     rcx, rcx
        adc     rbx, rbx
        adc     rbp, rbp
        adc     r8d, r8d
        mov     rax, [rsp+0x30]
        mul     rax
        mov     [rsp], r8
        mov     r8, rax
        mov     rax, [rsp+0x38]
        mov     [rsp+0x8], rbp
        add     r9, rdx
        sbb     rbp, rbp
        mul     rax
        neg     rbp
        adc     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x40]
        mul     rax
        neg     rbp
        adc     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x48]
        mul     rax
        neg     rbp
        adc     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x50]
        mul     rax
        neg     rbp
        adc     rcx, rax
        adc     rbx, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x58]
        mul     rax
        neg     rbp
        adc     rax, [rsp+0x8]
        adc     rdx, [rsp]
        mov     rbp, rax
        mov     rsi, rdx
        mov     [rsp], rbx
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r8, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r9, r8
        sbb     r10, rdx
        sbb     r11, rax
        sbb     r12, 0x0
        sbb     r13, 0x0
        mov     r8, rbx
        sbb     r8, 0x0
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r9, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r10, r9
        sbb     r11, rdx
        sbb     r12, rax
        sbb     r13, 0x0
        sbb     r8, 0x0
        mov     r9, rbx
        sbb     r9, 0x0
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r10, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r11, r10
        sbb     r12, rdx
        sbb     r13, rax
        sbb     r8, 0x0
        sbb     r9, 0x0
        mov     r10, rbx
        sbb     r10, 0x0
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r11, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r12, r11
        sbb     r13, rdx
        sbb     r8, rax
        sbb     r9, 0x0
        sbb     r10, 0x0
        mov     r11, rbx
        sbb     r11, 0x0
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r12, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r13, r12
        sbb     r8, rdx
        sbb     r9, rax
        sbb     r10, 0x0
        sbb     r11, 0x0
        mov     r12, rbx
        sbb     r12, 0x0
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r13, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r8, r13
        sbb     r9, rdx
        sbb     r10, rax
        sbb     r11, 0x0
        sbb     r12, 0x0
        mov     r13, rbx
        sbb     r13, 0x0
        mov     rbx, [rsp]
        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rsi, r13
        mov     r8d, 0x0
        adc     r8, r8
        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0xffffffff
        adc     r9, r15
        mov     r10d, 0x1
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rsi
        adc     r8, 0x0
        cmovne  r14, rax
        cmovne  r15, r9
        cmovne  rcx, r10
        cmovne  rbx, r11
        cmovne  rbp, r12
        cmovne  rsi, r13
        mov     [rsp], r14
        mov     [rsp+0x8], r15
        mov     [rsp+0x10], rcx
        mov     [rsp+0x18], rbx
        mov     [rsp+0x20], rbp
        mov     [rsp+0x28], rsi
        mov     rbx, [rsp+0xc0]
        mov     rax, [rsp+0x90]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x98]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xa0]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0xb0]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0xb8]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsp+0xc8]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsp+0xd0]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsp+0xd8]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsp+0xe0]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsp+0xe8]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0xc0], r14
        mov     [rsp+0xc8], r15
        mov     [rsp+0xd0], r8
        mov     [rsp+0xd8], r9
        mov     [rsp+0xe0], r10
        mov     [rsp+0xe8], r11
        mov     rbx, [rsp+0x60]
        mov     rax, [rsp+0x90]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x98]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xa0]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0xb0]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0xb8]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsp+0x68]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsp+0x70]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsp+0x78]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsp+0x80]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsp+0x88]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0x60], r14
        mov     [rsp+0x68], r15
        mov     [rsp+0x70], r8
        mov     [rsp+0x78], r9
        mov     [rsp+0x80], r10
        mov     [rsp+0x88], r11
        mov     rax, [rsp]
        sub     rax, [rsp+0xc0]
        mov     rdx, [rsp+0x8]
        sbb     rdx, [rsp+0xc8]
        mov     r8, [rsp+0x10]
        sbb     r8, [rsp+0xd0]
        mov     r9, [rsp+0x18]
        sbb     r9, [rsp+0xd8]
        mov     r10, [rsp+0x20]
        sbb     r10, [rsp+0xe0]
        mov     r11, [rsp+0x28]
        sbb     r11, [rsp+0xe8]
        sbb     rcx, rcx
        mov     esi, 0xffffffff
        and     rcx, rsi
        xor     rsi, rsi
        sub     rsi, rcx
        sub     rax, rsi
        mov     [rsp], rax
        sbb     rdx, rcx
        mov     [rsp+0x8], rdx
        sbb     rax, rax
        and     rcx, rsi
        neg     rax
        sbb     r8, rcx
        mov     [rsp+0x10], r8
        sbb     r9, 0x0
        mov     [rsp+0x18], r9
        sbb     r10, 0x0
        mov     [rsp+0x20], r10
        sbb     r11, 0x0
        mov     [rsp+0x28], r11
        mov     rax, [rsp+0x60]
        sub     rax, [rsp+0xc0]
        mov     rdx, [rsp+0x68]
        sbb     rdx, [rsp+0xc8]
        mov     r8, [rsp+0x70]
        sbb     r8, [rsp+0xd0]
        mov     r9, [rsp+0x78]
        sbb     r9, [rsp+0xd8]
        mov     r10, [rsp+0x80]
        sbb     r10, [rsp+0xe0]
        mov     r11, [rsp+0x88]
        sbb     r11, [rsp+0xe8]
        sbb     rcx, rcx
        mov     esi, 0xffffffff
        and     rcx, rsi
        xor     rsi, rsi
        sub     rsi, rcx
        sub     rax, rsi
        mov     [rsp+0x90], rax
        sbb     rdx, rcx
        mov     [rsp+0x98], rdx
        sbb     rax, rax
        and     rcx, rsi
        neg     rax
        sbb     r8, rcx
        mov     [rsp+0xa0], r8
        sbb     r9, 0x0
        mov     [rsp+0xa8], r9
        sbb     r10, 0x0
        mov     [rsp+0xb0], r10
        sbb     r11, 0x0
        mov     [rsp+0xb8], r11
        mov     rsi, [rsp+0x150]
        mov     rbx, [rsi+0x60]
        mov     rax, [rsp+0xf0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xf8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x100]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x108]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0x110]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x118]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsi+0x68]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsi+0x70]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsi+0x78]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsi+0x80]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsi+0x88]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0xf0], r14
        mov     [rsp+0xf8], r15
        mov     [rsp+0x100], r8
        mov     [rsp+0x108], r9
        mov     [rsp+0x110], r10
        mov     [rsp+0x118], r11
        mov     rax, [rsp]
        sub     rax, [rsp+0x60]
        mov     rdx, [rsp+0x8]
        sbb     rdx, [rsp+0x68]
        mov     r8, [rsp+0x10]
        sbb     r8, [rsp+0x70]
        mov     r9, [rsp+0x18]
        sbb     r9, [rsp+0x78]
        mov     r10, [rsp+0x20]
        sbb     r10, [rsp+0x80]
        mov     r11, [rsp+0x28]
        sbb     r11, [rsp+0x88]
        sbb     rcx, rcx
        mov     esi, 0xffffffff
        and     rcx, rsi
        xor     rsi, rsi
        sub     rsi, rcx
        sub     rax, rsi
        mov     [rsp], rax
        sbb     rdx, rcx
        mov     [rsp+0x8], rdx
        sbb     rax, rax
        and     rcx, rsi
        neg     rax
        sbb     r8, rcx
        mov     [rsp+0x10], r8
        sbb     r9, 0x0
        mov     [rsp+0x18], r9
        sbb     r10, 0x0
        mov     [rsp+0x20], r10
        sbb     r11, 0x0
        mov     [rsp+0x28], r11
        mov     rax, [rsp+0xc0]
        sub     rax, [rsp]
        mov     rdx, [rsp+0xc8]
        sbb     rdx, [rsp+0x8]
        mov     r8, [rsp+0xd0]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsp+0xd8]
        sbb     r9, [rsp+0x18]
        mov     r10, [rsp+0xe0]
        sbb     r10, [rsp+0x20]
        mov     r11, [rsp+0xe8]
        sbb     r11, [rsp+0x28]
        sbb     rcx, rcx
        mov     esi, 0xffffffff
        and     rcx, rsi
        xor     rsi, rsi
        sub     rsi, rcx
        sub     rax, rsi
        mov     [rsp+0xc0], rax
        sbb     rdx, rcx
        mov     [rsp+0xc8], rdx
        sbb     rax, rax
        and     rcx, rsi
        neg     rax
        sbb     r8, rcx
        mov     [rsp+0xd0], r8
        sbb     r9, 0x0
        mov     [rsp+0xd8], r9
        sbb     r10, 0x0
        mov     [rsp+0xe0], r10
        sbb     r11, 0x0
        mov     [rsp+0xe8], r11
        mov     rbx, [rsp+0x120]
        mov     rax, [rsp+0x90]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x98]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xa0]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0xb0]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0xb8]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsp+0x128]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsp+0x130]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsp+0x138]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsp+0x140]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsp+0x148]
        mov     rax, [rsp+0x90]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x98]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xa0]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     [rsp+0xa0], r8
        mov     [rsp+0xa8], r9
        mov     [rsp+0xb0], r10
        mov     [rsp+0xb8], r11
        mov     rcx, [rsp+0x158]
        mov     rbx, [rcx+0x60]
        mov     rax, [rsp+0xf0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xf8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x100]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x108]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0x110]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x118]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rcx+0x68]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rcx+0x70]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rcx+0x78]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rcx+0x80]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rcx+0x88]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0xf0], r14
        mov     [rsp+0xf8], r15
        mov     [rsp+0x100], r8
        mov     [rsp+0x108], r9
        mov     [rsp+0x110], r10
        mov     [rsp+0x118], r11
        mov     rbx, [rsp+0xc0]
        mov     rax, [rsp+0x30]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x38]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x40]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x48]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0x50]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x58]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsp+0xc8]
        mov     rax, [rsp+0x30]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x40]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsp+0xd0]
        mov     rax, [rsp+0x30]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x40]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsp+0xd8]
        mov     rax, [rsp+0x30]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x40]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsp+0xe0]
        mov     rax, [rsp+0x30]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x40]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsp+0xe8]
        mov     rax, [rsp+0x30]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x40]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0xc0], r14
        mov     [rsp+0xc8], r15
        mov     [rsp+0xd0], r8
        mov     [rsp+0xd8], r9
        mov     [rsp+0xe0], r10
        mov     [rsp+0xe8], r11
        mov     rax, [rsp+0xc0]
        sub     rax, [rsp+0x90]
        mov     rdx, [rsp+0xc8]
        sbb     rdx, [rsp+0x98]
        mov     r8, [rsp+0xd0]
        sbb     r8, [rsp+0xa0]
        mov     r9, [rsp+0xd8]
        sbb     r9, [rsp+0xa8]
        mov     r10, [rsp+0xe0]
        sbb     r10, [rsp+0xb0]
        mov     r11, [rsp+0xe8]
        sbb     r11, [rsp+0xb8]
        sbb     rcx, rcx
        mov     esi, 0xffffffff
        and     rcx, rsi
        xor     rsi, rsi
        sub     rsi, rcx
        sub     rax, rsi
        mov     [rsp+0xc0], rax
        sbb     rdx, rcx
        mov     [rsp+0xc8], rdx
        sbb     rax, rax
        and     rcx, rsi
        neg     rax
        sbb     r8, rcx
        mov     [rsp+0xd0], r8
        sbb     r9, 0x0
        mov     [rsp+0xd8], r9
        sbb     r10, 0x0
        mov     [rsp+0xe0], r10
        sbb     r11, 0x0
        mov     [rsp+0xe8], r11
        mov     rcx, [rsp+0x158]
        mov     r8, [rcx+0x60]
        mov     r9, [rcx+0x68]
        mov     r10, [rcx+0x70]
        mov     r11, [rcx+0x78]
        mov     rbx, [rcx+0x80]
        mov     rbp, [rcx+0x88]
        mov     rax, r8
        mov     rdx, r9
        or      rax, r10
        or      rdx, r11
        or      rax, rbx
        or      rdx, rbp
        or      rax, rdx
        neg     rax
        sbb     rax, rax
        mov     rsi, [rsp+0x150]
        mov     r12, [rsi+0x60]
        mov     r13, [rsi+0x68]
        mov     r14, [rsi+0x70]
        mov     r15, [rsi+0x78]
        mov     rdx, [rsi+0x80]
        mov     rcx, [rsi+0x88]
        cmove   r8, r12
        cmove   r9, r13
        cmove   r10, r14
        cmove   r11, r15
        cmove   rbx, rdx
        cmove   rbp, rcx
        or      r12, r13
        or      r14, r15
        or      rdx, rcx
        or      r12, r14
        or      rdx, r12
        neg     rdx
        sbb     rdx, rdx
        cmp     rax, rdx
        cmove   r8, [rsp+0xf0]
        cmove   r9, [rsp+0xf8]
        cmove   r10, [rsp+0x100]
        cmove   r11, [rsp+0x108]
        cmove   rbx, [rsp+0x110]
        cmove   rbp, [rsp+0x118]
        mov     [rsp+0xf0], r8
        mov     [rsp+0xf8], r9
        mov     [rsp+0x100], r10
        mov     [rsp+0x108], r11
        mov     [rsp+0x110], rbx
        mov     [rsp+0x118], rbp
        mov     rcx, [rsp+0x158]
        mov     rsi, [rsp+0x150]
        mov     r8, [rsp]
        cmovb   r8, [rsi]
        cmova   r8, [rcx]
        mov     r9, [rsp+0x8]
        cmovb   r9, [rsi+0x8]
        cmova   r9, [rcx+0x8]
        mov     r10, [rsp+0x10]
        cmovb   r10, [rsi+0x10]
        cmova   r10, [rcx+0x10]
        mov     r11, [rsp+0x18]
        cmovb   r11, [rsi+0x18]
        cmova   r11, [rcx+0x18]
        mov     rbx, [rsp+0x20]
        cmovb   rbx, [rsi+0x20]
        cmova   rbx, [rcx+0x20]
        mov     rbp, [rsp+0x28]
        cmovb   rbp, [rsi+0x28]
        cmova   rbp, [rcx+0x28]
        mov     r12, [rsp+0xc0]
        cmovb   r12, [rsi+0x30]
        cmova   r12, [rcx+0x30]
        mov     r13, [rsp+0xc8]
        cmovb   r13, [rsi+0x38]
        cmova   r13, [rcx+0x38]
        mov     r14, [rsp+0xd0]
        cmovb   r14, [rsi+0x40]
        cmova   r14, [rcx+0x40]
        mov     r15, [rsp+0xd8]
        cmovb   r15, [rsi+0x48]
        cmova   r15, [rcx+0x48]
        mov     rdx, [rsp+0xe0]
        cmovb   rdx, [rsi+0x50]
        cmova   rdx, [rcx+0x50]
        mov     rax, [rsp+0xe8]
        cmovb   rax, [rsi+0x58]
        cmova   rax, [rcx+0x58]
        mov     [rdi], r8
        mov     [rdi+0x8], r9
        mov     [rdi+0x10], r10
        mov     [rdi+0x18], r11
        mov     [rdi+0x20], rbx
        mov     [rdi+0x28], rbp
        mov     r8, [rsp+0xf0]
        mov     r9, [rsp+0xf8]
        mov     r10, [rsp+0x100]
        mov     r11, [rsp+0x108]
        mov     rbx, [rsp+0x110]
        mov     rbp, [rsp+0x118]
        mov     [rdi+0x30], r12
        mov     [rdi+0x38], r13
        mov     [rdi+0x40], r14
        mov     [rdi+0x48], r15
        mov     [rdi+0x50], rdx
        mov     [rdi+0x58], rax
        mov     [rdi+0x60], r8
        mov     [rdi+0x68], r9
        mov     [rdi+0x70], r10
        mov     [rdi+0x78], r11
        mov     [rdi+0x80], rbx
        mov     [rdi+0x88], rbp
        CFI_INC_RSP(352)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp384_montjscalarmul_alt_p384_montjadd)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp384_montjscalarmul_alt_p384_montjdouble)

Lp384_montjscalarmul_alt_p384_montjdouble:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(344)
        mov     [rsp+0x150], rdi
        mov     rbx, [rsi+0x60]
        mov     rax, [rsi+0x68]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x78]
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x88]
        mul     rbx
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi+0x78]
        mul     QWORD PTR [rsi+0x80]
        mov     r15, rax
        mov     rcx, rdx
        mov     rbx, [rsi+0x70]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x68]
        mul     rbx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rbx, [rsi+0x68]
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        adc     rcx, 0x0
        mov     rbx, [rsi+0x80]
        mov     rax, [rsi+0x60]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rbx, [rsi+0x70]
        mov     rax, [rsi+0x78]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x80]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x88]
        mul     rbx
        sub     rdx, rbp
        add     r15, rax
        adc     rcx, rdx
        sbb     rbp, rbp
        xor     ebx, ebx
        mov     rax, [rsi+0x78]
        mul     QWORD PTR [rsi+0x88]
        sub     rdx, rbp
        xor     ebp, ebp
        add     rcx, rax
        adc     rbx, rdx
        adc     ebp, ebp
        mov     rax, [rsi+0x80]
        mul     QWORD PTR [rsi+0x88]
        add     rbx, rax
        adc     rbp, rdx
        xor     r8d, r8d
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     r15, r15
        adc     rcx, rcx
        adc     rbx, rbx
        adc     rbp, rbp
        adc     r8d, r8d
        mov     rax, [rsi+0x60]
        mul     rax
        mov     [rsp], r8
        mov     r8, rax
        mov     rax, [rsi+0x68]
        mov     [rsp+0x8], rbp
        add     r9, rdx
        sbb     rbp, rbp
        mul     rax
        neg     rbp
        adc     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x70]
        mul     rax
        neg     rbp
        adc     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x78]
        mul     rax
        neg     rbp
        adc     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x80]
        mul     rax
        neg     rbp
        adc     rcx, rax
        adc     rbx, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x88]
        mul     rax
        neg     rbp
        adc     rax, [rsp+0x8]
        adc     rdx, [rsp]
        mov     rbp, rax
        mov     rdi, rdx
        mov     [rsp], rbx
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r8, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r9, r8
        sbb     r10, rdx
        sbb     r11, rax
        sbb     r12, 0x0
        sbb     r13, 0x0
        mov     r8, rbx
        sbb     r8, 0x0
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r9, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r10, r9
        sbb     r11, rdx
        sbb     r12, rax
        sbb     r13, 0x0
        sbb     r8, 0x0
        mov     r9, rbx
        sbb     r9, 0x0
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r10, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r11, r10
        sbb     r12, rdx
        sbb     r13, rax
        sbb     r8, 0x0
        sbb     r9, 0x0
        mov     r10, rbx
        sbb     r10, 0x0
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r11, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r12, r11
        sbb     r13, rdx
        sbb     r8, rax
        sbb     r9, 0x0
        sbb     r10, 0x0
        mov     r11, rbx
        sbb     r11, 0x0
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r12, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r13, r12
        sbb     r8, rdx
        sbb     r9, rax
        sbb     r10, 0x0
        sbb     r11, 0x0
        mov     r12, rbx
        sbb     r12, 0x0
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r13, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r8, r13
        sbb     r9, rdx
        sbb     r10, rax
        sbb     r11, 0x0
        sbb     r12, 0x0
        mov     r13, rbx
        sbb     r13, 0x0
        mov     rbx, [rsp]
        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rdi, r13
        mov     r8d, 0x0
        adc     r8, r8
        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0xffffffff
        adc     r9, r15
        mov     r10d, 0x1
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rdi
        adc     r8, 0x0
        cmovne  r14, rax
        cmovne  r15, r9
        cmovne  rcx, r10
        cmovne  rbx, r11
        cmovne  rbp, r12
        cmovne  rdi, r13
        mov     [rsp], r14
        mov     [rsp+0x8], r15
        mov     [rsp+0x10], rcx
        mov     [rsp+0x18], rbx
        mov     [rsp+0x20], rbp
        mov     [rsp+0x28], rdi
        mov     rbx, [rsi+0x30]
        mov     rax, [rsi+0x38]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x48]
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x58]
        mul     rbx
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi+0x48]
        mul     QWORD PTR [rsi+0x50]
        mov     r15, rax
        mov     rcx, rdx
        mov     rbx, [rsi+0x40]
        mov     rax, [rsi+0x30]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x38]
        mul     rbx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rbx, [rsi+0x38]
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        adc     rcx, 0x0
        mov     rbx, [rsi+0x50]
        mov     rax, [rsi+0x30]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rbx, [rsi+0x40]
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, rbp
        add     r15, rax
        adc     rcx, rdx
        sbb     rbp, rbp
        xor     ebx, ebx
        mov     rax, [rsi+0x48]
        mul     QWORD PTR [rsi+0x58]
        sub     rdx, rbp
        xor     ebp, ebp
        add     rcx, rax
        adc     rbx, rdx
        adc     ebp, ebp
        mov     rax, [rsi+0x50]
        mul     QWORD PTR [rsi+0x58]
        add     rbx, rax
        adc     rbp, rdx
        xor     r8d, r8d
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     r15, r15
        adc     rcx, rcx
        adc     rbx, rbx
        adc     rbp, rbp
        adc     r8d, r8d
        mov     rax, [rsi+0x30]
        mul     rax
        mov     [rsp+0x30], r8
        mov     r8, rax
        mov     rax, [rsi+0x38]
        mov     [rsp+0x38], rbp
        add     r9, rdx
        sbb     rbp, rbp
        mul     rax
        neg     rbp
        adc     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x40]
        mul     rax
        neg     rbp
        adc     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x48]
        mul     rax
        neg     rbp
        adc     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x50]
        mul     rax
        neg     rbp
        adc     rcx, rax
        adc     rbx, rdx
        sbb     rbp, rbp
        mov     rax, [rsi+0x58]
        mul     rax
        neg     rbp
        adc     rax, [rsp+0x38]
        adc     rdx, [rsp+0x30]
        mov     rbp, rax
        mov     rdi, rdx
        mov     [rsp+0x30], rbx
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r8, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r9, r8
        sbb     r10, rdx
        sbb     r11, rax
        sbb     r12, 0x0
        sbb     r13, 0x0
        mov     r8, rbx
        sbb     r8, 0x0
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r9, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r10, r9
        sbb     r11, rdx
        sbb     r12, rax
        sbb     r13, 0x0
        sbb     r8, 0x0
        mov     r9, rbx
        sbb     r9, 0x0
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r10, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r11, r10
        sbb     r12, rdx
        sbb     r13, rax
        sbb     r8, 0x0
        sbb     r9, 0x0
        mov     r10, rbx
        sbb     r10, 0x0
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r11, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r12, r11
        sbb     r13, rdx
        sbb     r8, rax
        sbb     r9, 0x0
        sbb     r10, 0x0
        mov     r11, rbx
        sbb     r11, 0x0
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r12, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r13, r12
        sbb     r8, rdx
        sbb     r9, rax
        sbb     r10, 0x0
        sbb     r11, 0x0
        mov     r12, rbx
        sbb     r12, 0x0
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r13, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r8, r13
        sbb     r9, rdx
        sbb     r10, rax
        sbb     r11, 0x0
        sbb     r12, 0x0
        mov     r13, rbx
        sbb     r13, 0x0
        mov     rbx, [rsp+0x30]
        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rdi, r13
        mov     r8d, 0x0
        adc     r8, r8
        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0xffffffff
        adc     r9, r15
        mov     r10d, 0x1
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rdi
        adc     r8, 0x0
        cmovne  r14, rax
        cmovne  r15, r9
        cmovne  rcx, r10
        cmovne  rbx, r11
        cmovne  rbp, r12
        cmovne  rdi, r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     [rsp+0x40], rcx
        mov     [rsp+0x48], rbx
        mov     [rsp+0x50], rbp
        mov     [rsp+0x58], rdi
        mov     rax, [rsi]
        add     rax, [rsp]
        mov     rcx, [rsi+0x8]
        adc     rcx, [rsp+0x8]
        mov     r8, [rsi+0x10]
        adc     r8, [rsp+0x10]
        mov     r9, [rsi+0x18]
        adc     r9, [rsp+0x18]
        mov     r10, [rsi+0x20]
        adc     r10, [rsp+0x20]
        mov     r11, [rsi+0x28]
        adc     r11, [rsp+0x28]
        sbb     rdx, rdx
        mov     ebx, 0x1
        and     rbx, rdx
        mov     ebp, 0xffffffff
        and     rdx, rbp
        xor     rbp, rbp
        sub     rbp, rdx
        add     rax, rbp
        mov     [rsp+0xf0], rax
        adc     rcx, rdx
        mov     [rsp+0xf8], rcx
        adc     r8, rbx
        mov     [rsp+0x100], r8
        adc     r9, 0x0
        mov     [rsp+0x108], r9
        adc     r10, 0x0
        mov     [rsp+0x110], r10
        adc     r11, 0x0
        mov     [rsp+0x118], r11
        mov     rax, [rsi]
        sub     rax, [rsp]
        mov     rdx, [rsi+0x8]
        sbb     rdx, [rsp+0x8]
        mov     r8, [rsi+0x10]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsi+0x18]
        sbb     r9, [rsp+0x18]
        mov     r10, [rsi+0x20]
        sbb     r10, [rsp+0x20]
        mov     r11, [rsi+0x28]
        sbb     r11, [rsp+0x28]
        sbb     rcx, rcx
        mov     ebx, 0xffffffff
        and     rcx, rbx
        xor     rbx, rbx
        sub     rbx, rcx
        sub     rax, rbx
        mov     [rsp+0xc0], rax
        sbb     rdx, rcx
        mov     [rsp+0xc8], rdx
        sbb     rax, rax
        and     rcx, rbx
        neg     rax
        sbb     r8, rcx
        mov     [rsp+0xd0], r8
        sbb     r9, 0x0
        mov     [rsp+0xd8], r9
        sbb     r10, 0x0
        mov     [rsp+0xe0], r10
        sbb     r11, 0x0
        mov     [rsp+0xe8], r11
        mov     rbx, [rsp+0xc0]
        mov     rax, [rsp+0xf0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xf8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x100]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x108]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0x110]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x118]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsp+0xc8]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsp+0xd0]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsp+0xd8]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsp+0xe0]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsp+0xe8]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x100]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0x60], r14
        mov     [rsp+0x68], r15
        mov     [rsp+0x70], r8
        mov     [rsp+0x78], r9
        mov     [rsp+0x80], r10
        mov     [rsp+0x88], r11
        mov     rax, [rsi+0x30]
        add     rax, [rsi+0x60]
        mov     rcx, [rsi+0x38]
        adc     rcx, [rsi+0x68]
        mov     r8, [rsi+0x40]
        adc     r8, [rsi+0x70]
        mov     r9, [rsi+0x48]
        adc     r9, [rsi+0x78]
        mov     r10, [rsi+0x50]
        adc     r10, [rsi+0x80]
        mov     r11, [rsi+0x58]
        adc     r11, [rsi+0x88]
        mov     edx, 0x0
        adc     rdx, rdx
        movabs  rbp, 0xffffffff00000001
        add     rax, rbp
        mov     ebp, 0xffffffff
        adc     rcx, rbp
        adc     r8, 0x1
        adc     r9, 0x0
        adc     r10, 0x0
        adc     r11, 0x0
        adc     rdx, 0xffffffffffffffff
        mov     ebx, 0x1
        and     rbx, rdx
        and     rdx, rbp
        xor     rbp, rbp
        sub     rbp, rdx
        sub     rax, rbp
        mov     [rsp+0xf0], rax
        sbb     rcx, rdx
        mov     [rsp+0xf8], rcx
        sbb     r8, rbx
        mov     [rsp+0x100], r8
        sbb     r9, 0x0
        mov     [rsp+0x108], r9
        sbb     r10, 0x0
        mov     [rsp+0x110], r10
        sbb     r11, 0x0
        mov     [rsp+0x118], r11
        mov     rbx, [rsp+0x60]
        mov     rax, [rsp+0x68]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x78]
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x88]
        mul     rbx
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0x80]
        mov     r15, rax
        mov     rcx, rdx
        mov     rbx, [rsp+0x70]
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rbx, [rsp+0x68]
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x80]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x88]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        adc     rcx, 0x0
        mov     rbx, [rsp+0x80]
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rbx, [rsp+0x70]
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x80]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x88]
        mul     rbx
        sub     rdx, rbp
        add     r15, rax
        adc     rcx, rdx
        sbb     rbp, rbp
        xor     ebx, ebx
        mov     rax, [rsp+0x78]
        mul     QWORD PTR [rsp+0x88]
        sub     rdx, rbp
        xor     ebp, ebp
        add     rcx, rax
        adc     rbx, rdx
        adc     ebp, ebp
        mov     rax, [rsp+0x80]
        mul     QWORD PTR [rsp+0x88]
        add     rbx, rax
        adc     rbp, rdx
        xor     r8d, r8d
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     r15, r15
        adc     rcx, rcx
        adc     rbx, rbx
        adc     rbp, rbp
        adc     r8d, r8d
        mov     rax, [rsp+0x60]
        mul     rax
        mov     [rsp+0x120], r8
        mov     r8, rax
        mov     rax, [rsp+0x68]
        mov     [rsp+0x128], rbp
        add     r9, rdx
        sbb     rbp, rbp
        mul     rax
        neg     rbp
        adc     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x70]
        mul     rax
        neg     rbp
        adc     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x78]
        mul     rax
        neg     rbp
        adc     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x80]
        mul     rax
        neg     rbp
        adc     rcx, rax
        adc     rbx, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x88]
        mul     rax
        neg     rbp
        adc     rax, [rsp+0x128]
        adc     rdx, [rsp+0x120]
        mov     rbp, rax
        mov     rdi, rdx
        mov     [rsp+0x120], rbx
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r8, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r9, r8
        sbb     r10, rdx
        sbb     r11, rax
        sbb     r12, 0x0
        sbb     r13, 0x0
        mov     r8, rbx
        sbb     r8, 0x0
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r9, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r10, r9
        sbb     r11, rdx
        sbb     r12, rax
        sbb     r13, 0x0
        sbb     r8, 0x0
        mov     r9, rbx
        sbb     r9, 0x0
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r10, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r11, r10
        sbb     r12, rdx
        sbb     r13, rax
        sbb     r8, 0x0
        sbb     r9, 0x0
        mov     r10, rbx
        sbb     r10, 0x0
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r11, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r12, r11
        sbb     r13, rdx
        sbb     r8, rax
        sbb     r9, 0x0
        sbb     r10, 0x0
        mov     r11, rbx
        sbb     r11, 0x0
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r12, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r13, r12
        sbb     r8, rdx
        sbb     r9, rax
        sbb     r10, 0x0
        sbb     r11, 0x0
        mov     r12, rbx
        sbb     r12, 0x0
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r13, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r8, r13
        sbb     r9, rdx
        sbb     r10, rax
        sbb     r11, 0x0
        sbb     r12, 0x0
        mov     r13, rbx
        sbb     r13, 0x0
        mov     rbx, [rsp+0x120]
        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rdi, r13
        mov     r8d, 0x0
        adc     r8, r8
        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0xffffffff
        adc     r9, r15
        mov     r10d, 0x1
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rdi
        adc     r8, 0x0
        cmovne  r14, rax
        cmovne  r15, r9
        cmovne  rcx, r10
        cmovne  rbx, r11
        cmovne  rbp, r12
        cmovne  rdi, r13
        mov     [rsp+0x120], r14
        mov     [rsp+0x128], r15
        mov     [rsp+0x130], rcx
        mov     [rsp+0x138], rbx
        mov     [rsp+0x140], rbp
        mov     [rsp+0x148], rdi
        mov     rbx, [rsp+0x30]
        mov     rax, [rsi]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsi+0x8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x10]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsi+0x18]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsi+0x20]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsi+0x28]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsp+0x38]
        mov     rax, [rsi]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x20]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x28]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsp+0x40]
        mov     rax, [rsi]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x20]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x28]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsp+0x48]
        mov     rax, [rsi]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsi+0x20]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsi+0x28]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsp+0x50]
        mov     rax, [rsi]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsi+0x20]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsi+0x28]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsp+0x58]
        mov     rax, [rsi]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsi+0x20]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsi+0x28]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     [rsp+0xa0], r8
        mov     [rsp+0xa8], r9
        mov     [rsp+0xb0], r10
        mov     [rsp+0xb8], r11
        mov     rbx, [rsp+0xf0]
        mov     rax, [rsp+0xf8]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x108]
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x118]
        mul     rbx
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x108]
        mul     QWORD PTR [rsp+0x110]
        mov     r15, rax
        mov     rcx, rdx
        mov     rbx, [rsp+0x100]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0xf8]
        mul     rbx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rbx, [rsp+0xf8]
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        adc     rcx, 0x0
        mov     rbx, [rsp+0x110]
        mov     rax, [rsp+0xf0]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rbx, [rsp+0x100]
        mov     rax, [rsp+0x108]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x110]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x118]
        mul     rbx
        sub     rdx, rbp
        add     r15, rax
        adc     rcx, rdx
        sbb     rbp, rbp
        xor     ebx, ebx
        mov     rax, [rsp+0x108]
        mul     QWORD PTR [rsp+0x118]
        sub     rdx, rbp
        xor     ebp, ebp
        add     rcx, rax
        adc     rbx, rdx
        adc     ebp, ebp
        mov     rax, [rsp+0x110]
        mul     QWORD PTR [rsp+0x118]
        add     rbx, rax
        adc     rbp, rdx
        xor     r8d, r8d
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     r15, r15
        adc     rcx, rcx
        adc     rbx, rbx
        adc     rbp, rbp
        adc     r8d, r8d
        mov     rax, [rsp+0xf0]
        mul     rax
        mov     [rsp+0xc0], r8
        mov     r8, rax
        mov     rax, [rsp+0xf8]
        mov     [rsp+0xc8], rbp
        add     r9, rdx
        sbb     rbp, rbp
        mul     rax
        neg     rbp
        adc     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x100]
        mul     rax
        neg     rbp
        adc     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x108]
        mul     rax
        neg     rbp
        adc     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x110]
        mul     rax
        neg     rbp
        adc     rcx, rax
        adc     rbx, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x118]
        mul     rax
        neg     rbp
        adc     rax, [rsp+0xc8]
        adc     rdx, [rsp+0xc0]
        mov     rbp, rax
        mov     rdi, rdx
        mov     [rsp+0xc0], rbx
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r8, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r9, r8
        sbb     r10, rdx
        sbb     r11, rax
        sbb     r12, 0x0
        sbb     r13, 0x0
        mov     r8, rbx
        sbb     r8, 0x0
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r9, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r10, r9
        sbb     r11, rdx
        sbb     r12, rax
        sbb     r13, 0x0
        sbb     r8, 0x0
        mov     r9, rbx
        sbb     r9, 0x0
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r10, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r11, r10
        sbb     r12, rdx
        sbb     r13, rax
        sbb     r8, 0x0
        sbb     r9, 0x0
        mov     r10, rbx
        sbb     r10, 0x0
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r11, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r12, r11
        sbb     r13, rdx
        sbb     r8, rax
        sbb     r9, 0x0
        sbb     r10, 0x0
        mov     r11, rbx
        sbb     r11, 0x0
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r12, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r13, r12
        sbb     r8, rdx
        sbb     r9, rax
        sbb     r10, 0x0
        sbb     r11, 0x0
        mov     r12, rbx
        sbb     r12, 0x0
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r13, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r8, r13
        sbb     r9, rdx
        sbb     r10, rax
        sbb     r11, 0x0
        sbb     r12, 0x0
        mov     r13, rbx
        sbb     r13, 0x0
        mov     rbx, [rsp+0xc0]
        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rdi, r13
        mov     r8d, 0x0
        adc     r8, r8
        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0xffffffff
        adc     r9, r15
        mov     r10d, 0x1
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rdi
        adc     r8, 0x0
        cmovne  r14, rax
        cmovne  r15, r9
        cmovne  rcx, r10
        cmovne  rbx, r11
        cmovne  rbp, r12
        cmovne  rdi, r13
        mov     [rsp+0xc0], r14
        mov     [rsp+0xc8], r15
        mov     [rsp+0xd0], rcx
        mov     [rsp+0xd8], rbx
        mov     [rsp+0xe0], rbp
        mov     [rsp+0xe8], rdi
        movabs  r9, 0xffffffff
        sub     r9, [rsp+0x120]
        movabs  r10, 0xffffffff00000000
        sbb     r10, [rsp+0x128]
        mov     r11, 0xfffffffffffffffe
        sbb     r11, [rsp+0x130]
        mov     r12, 0xffffffffffffffff
        sbb     r12, [rsp+0x138]
        mov     r13, 0xffffffffffffffff
        sbb     r13, [rsp+0x140]
        mov     r14, 0xffffffffffffffff
        sbb     r14, [rsp+0x148]
        mov     rcx, 0x9
        mov     rax, r9
        mul     rcx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, r10
        xor     r10d, r10d
        mul     rcx
        add     r9, rax
        adc     r10, rdx
        mov     rax, r11
        xor     r11d, r11d
        mul     rcx
        add     r10, rax
        adc     r11, rdx
        mov     rax, r12
        xor     r12d, r12d
        mul     rcx
        add     r11, rax
        adc     r12, rdx
        mov     rax, r13
        xor     r13d, r13d
        mul     rcx
        add     r12, rax
        adc     r13, rdx
        mov     rax, r14
        mov     r14d, 0x1
        mul     rcx
        add     r13, rax
        adc     r14, rdx
        mov     ecx, 0xc
        mov     rax, [rsp+0x90]
        mul     rcx
        add     r8, rax
        adc     r9, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x98]
        mul     rcx
        sub     rdx, rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0xa0]
        mul     rcx
        sub     rdx, rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0xa8]
        mul     rcx
        sub     rdx, rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0xb0]
        mul     rcx
        sub     rdx, rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0xb8]
        mul     rcx
        sub     rdx, rbx
        add     r13, rax
        adc     r14, rdx
        movabs  rax, 0xffffffff00000001
        mul     r14
        add     r8, rax
        adc     r9, rdx
        adc     r10, r14
        mov     rax, r14
        sbb     rcx, rcx
        mov     edx, 0xffffffff
        neg     rcx
        mul     rdx
        add     r9, rax
        adc     r10, rdx
        adc     r11, rcx
        adc     r12, 0x0
        adc     r13, 0x0
        sbb     rcx, rcx
        not     rcx
        mov     edx, 0xffffffff
        xor     rax, rax
        and     rdx, rcx
        sub     rax, rdx
        and     rcx, 0x1
        sub     r8, rax
        mov     [rsp+0x120], r8
        sbb     r9, rdx
        mov     [rsp+0x128], r9
        sbb     r10, rcx
        mov     [rsp+0x130], r10
        sbb     r11, 0x0
        mov     [rsp+0x138], r11
        sbb     r12, 0x0
        mov     [rsp+0x140], r12
        sbb     r13, 0x0
        mov     [rsp+0x148], r13
        mov     rax, [rsp+0xc0]
        sub     rax, [rsp]
        mov     rdx, [rsp+0xc8]
        sbb     rdx, [rsp+0x8]
        mov     r8, [rsp+0xd0]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsp+0xd8]
        sbb     r9, [rsp+0x18]
        mov     r10, [rsp+0xe0]
        sbb     r10, [rsp+0x20]
        mov     r11, [rsp+0xe8]
        sbb     r11, [rsp+0x28]
        sbb     rcx, rcx
        mov     ebx, 0xffffffff
        and     rcx, rbx
        xor     rbx, rbx
        sub     rbx, rcx
        sub     rax, rbx
        mov     [rsp+0xf0], rax
        sbb     rdx, rcx
        mov     [rsp+0xf8], rdx
        sbb     rax, rax
        and     rcx, rbx
        neg     rax
        sbb     r8, rcx
        mov     [rsp+0x100], r8
        sbb     r9, 0x0
        mov     [rsp+0x108], r9
        sbb     r10, 0x0
        mov     [rsp+0x110], r10
        sbb     r11, 0x0
        mov     [rsp+0x118], r11
        mov     rbx, [rsp+0x30]
        mov     rax, [rsp+0x38]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x48]
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x58]
        mul     rbx
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x48]
        mul     QWORD PTR [rsp+0x50]
        mov     r15, rax
        mov     rcx, rdx
        mov     rbx, [rsp+0x40]
        mov     rax, [rsp+0x30]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, rbp
        add     r11, rax
        adc     r12, rdx
        sbb     rbp, rbp
        mov     rbx, [rsp+0x38]
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, rbp
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        adc     rcx, 0x0
        mov     rbx, [rsp+0x50]
        mov     rax, [rsp+0x30]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rbx, [rsp+0x40]
        mov     rax, [rsp+0x48]
        mul     rbx
        sub     rdx, rbp
        add     r13, rax
        adc     r14, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x50]
        mul     rbx
        sub     rdx, rbp
        add     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x58]
        mul     rbx
        sub     rdx, rbp
        add     r15, rax
        adc     rcx, rdx
        sbb     rbp, rbp
        xor     ebx, ebx
        mov     rax, [rsp+0x48]
        mul     QWORD PTR [rsp+0x58]
        sub     rdx, rbp
        xor     ebp, ebp
        add     rcx, rax
        adc     rbx, rdx
        adc     ebp, ebp
        mov     rax, [rsp+0x50]
        mul     QWORD PTR [rsp+0x58]
        add     rbx, rax
        adc     rbp, rdx
        xor     r8d, r8d
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     r15, r15
        adc     rcx, rcx
        adc     rbx, rbx
        adc     rbp, rbp
        adc     r8d, r8d
        mov     rax, [rsp+0x30]
        mul     rax
        mov     [rsp+0xc0], r8
        mov     r8, rax
        mov     rax, [rsp+0x38]
        mov     [rsp+0xc8], rbp
        add     r9, rdx
        sbb     rbp, rbp
        mul     rax
        neg     rbp
        adc     r10, rax
        adc     r11, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x40]
        mul     rax
        neg     rbp
        adc     r12, rax
        adc     r13, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x48]
        mul     rax
        neg     rbp
        adc     r14, rax
        adc     r15, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x50]
        mul     rax
        neg     rbp
        adc     rcx, rax
        adc     rbx, rdx
        sbb     rbp, rbp
        mov     rax, [rsp+0x58]
        mul     rax
        neg     rbp
        adc     rax, [rsp+0xc8]
        adc     rdx, [rsp+0xc0]
        mov     rbp, rax
        mov     rdi, rdx
        mov     [rsp+0xc0], rbx
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r8, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r9, r8
        sbb     r10, rdx
        sbb     r11, rax
        sbb     r12, 0x0
        sbb     r13, 0x0
        mov     r8, rbx
        sbb     r8, 0x0
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r9, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r10, r9
        sbb     r11, rdx
        sbb     r12, rax
        sbb     r13, 0x0
        sbb     r8, 0x0
        mov     r9, rbx
        sbb     r9, 0x0
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r10, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r11, r10
        sbb     r12, rdx
        sbb     r13, rax
        sbb     r8, 0x0
        sbb     r9, 0x0
        mov     r10, rbx
        sbb     r10, 0x0
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r11, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r12, r11
        sbb     r13, rdx
        sbb     r8, rax
        sbb     r9, 0x0
        sbb     r10, 0x0
        mov     r11, rbx
        sbb     r11, 0x0
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r12, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r13, r12
        sbb     r8, rdx
        sbb     r9, rax
        sbb     r10, 0x0
        sbb     r11, 0x0
        mov     r12, rbx
        sbb     r12, 0x0
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     r13, rax
        mov     eax, 0x0
        adc     rdx, rbx
        adc     eax, eax
        sub     r8, r13
        sbb     r9, rdx
        sbb     r10, rax
        sbb     r11, 0x0
        sbb     r12, 0x0
        mov     r13, rbx
        sbb     r13, 0x0
        mov     rbx, [rsp+0xc0]
        add     r14, r8
        adc     r15, r9
        adc     rcx, r10
        adc     rbx, r11
        adc     rbp, r12
        adc     rdi, r13
        mov     r8d, 0x0
        adc     r8, r8
        xor     r11, r11
        xor     r12, r12
        xor     r13, r13
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     r9d, 0xffffffff
        adc     r9, r15
        mov     r10d, 0x1
        adc     r10, rcx
        adc     r11, rbx
        adc     r12, rbp
        adc     r13, rdi
        adc     r8, 0x0
        cmovne  r14, rax
        cmovne  r15, r9
        cmovne  rcx, r10
        cmovne  rbx, r11
        cmovne  rbp, r12
        cmovne  rdi, r13
        mov     [rsp+0xc0], r14
        mov     [rsp+0xc8], r15
        mov     [rsp+0xd0], rcx
        mov     [rsp+0xd8], rbx
        mov     [rsp+0xe0], rbp
        mov     [rsp+0xe8], rdi
        mov     rdi, [rsp+0x150]
        mov     rax, [rsp+0xf0]
        sub     rax, [rsp+0x30]
        mov     rdx, [rsp+0xf8]
        sbb     rdx, [rsp+0x38]
        mov     r8, [rsp+0x100]
        sbb     r8, [rsp+0x40]
        mov     r9, [rsp+0x108]
        sbb     r9, [rsp+0x48]
        mov     r10, [rsp+0x110]
        sbb     r10, [rsp+0x50]
        mov     r11, [rsp+0x118]
        sbb     r11, [rsp+0x58]
        sbb     rcx, rcx
        mov     ebx, 0xffffffff
        and     rcx, rbx
        xor     rbx, rbx
        sub     rbx, rcx
        sub     rax, rbx
        mov     [rdi+0x60], rax
        sbb     rdx, rcx
        mov     [rdi+0x68], rdx
        sbb     rax, rax
        and     rcx, rbx
        neg     rax
        sbb     r8, rcx
        mov     [rdi+0x70], r8
        sbb     r9, 0x0
        mov     [rdi+0x78], r9
        sbb     r10, 0x0
        mov     [rdi+0x80], r10
        sbb     r11, 0x0
        mov     [rdi+0x88], r11
        mov     rbx, [rsp+0x60]
        mov     rax, [rsp+0x120]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x128]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x130]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x138]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rax, [rsp+0x140]
        mul     rbx
        xor     r13d, r13d
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x148]
        mul     rbx
        xor     r14d, r14d
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rbx, r8
        shl     rbx, 0x20
        add     rbx, r8
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r8, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r8
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r9, rax
        sbb     r10, rdx
        sbb     r11, rbp
        sbb     r12, 0x0
        sbb     r13, 0x0
        sbb     rbx, 0x0
        add     r14, rbx
        adc     r15, 0x0
        mov     rbx, [rsp+0x68]
        mov     rax, [rsp+0x120]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x128]
        mul     rbx
        sub     rdx, r8
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x130]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x138]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x140]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x148]
        mul     rbx
        sub     rdx, r8
        add     r14, rax
        adc     r15, rdx
        sbb     r8, r8
        neg     r8
        mov     rbx, r9
        shl     rbx, 0x20
        add     rbx, r9
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r9, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r9
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r10, rax
        sbb     r11, rdx
        sbb     r12, rbp
        sbb     r13, 0x0
        sbb     r14, 0x0
        sbb     rbx, 0x0
        add     r15, rbx
        adc     r8, 0x0
        mov     rbx, [rsp+0x70]
        mov     rax, [rsp+0x120]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x128]
        mul     rbx
        sub     rdx, r9
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x130]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x138]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x140]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x148]
        mul     rbx
        sub     rdx, r9
        add     r15, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     r9
        mov     rbx, r10
        shl     rbx, 0x20
        add     rbx, r10
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r10, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r10
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r11, rax
        sbb     r12, rdx
        sbb     r13, rbp
        sbb     r14, 0x0
        sbb     r15, 0x0
        sbb     rbx, 0x0
        add     r8, rbx
        adc     r9, 0x0
        mov     rbx, [rsp+0x78]
        mov     rax, [rsp+0x120]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x128]
        mul     rbx
        sub     rdx, r10
        add     r12, rax
        adc     r13, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x130]
        mul     rbx
        sub     rdx, r10
        add     r13, rax
        adc     r14, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x138]
        mul     rbx
        sub     rdx, r10
        add     r14, rax
        adc     r15, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x140]
        mul     rbx
        sub     rdx, r10
        add     r15, rax
        adc     r8, rdx
        sbb     r10, r10
        mov     rax, [rsp+0x148]
        mul     rbx
        sub     rdx, r10
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rbx, r11
        shl     rbx, 0x20
        add     rbx, r11
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r11, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r11
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r12, rax
        sbb     r13, rdx
        sbb     r14, rbp
        sbb     r15, 0x0
        sbb     r8, 0x0
        sbb     rbx, 0x0
        add     r9, rbx
        adc     r10, 0x0
        mov     rbx, [rsp+0x80]
        mov     rax, [rsp+0x120]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x128]
        mul     rbx
        sub     rdx, r11
        add     r13, rax
        adc     r14, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x130]
        mul     rbx
        sub     rdx, r11
        add     r14, rax
        adc     r15, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x138]
        mul     rbx
        sub     rdx, r11
        add     r15, rax
        adc     r8, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x140]
        mul     rbx
        sub     rdx, r11
        add     r8, rax
        adc     r9, rdx
        sbb     r11, r11
        mov     rax, [rsp+0x148]
        mul     rbx
        sub     rdx, r11
        add     r9, rax
        adc     r10, rdx
        sbb     r11, r11
        neg     r11
        mov     rbx, r12
        shl     rbx, 0x20
        add     rbx, r12
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r12, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r12
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r13, rax
        sbb     r14, rdx
        sbb     r15, rbp
        sbb     r8, 0x0
        sbb     r9, 0x0
        sbb     rbx, 0x0
        add     r10, rbx
        adc     r11, 0x0
        mov     rbx, [rsp+0x88]
        mov     rax, [rsp+0x120]
        mul     rbx
        add     r13, rax
        adc     r14, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x128]
        mul     rbx
        sub     rdx, r12
        add     r14, rax
        adc     r15, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x130]
        mul     rbx
        sub     rdx, r12
        add     r15, rax
        adc     r8, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x138]
        mul     rbx
        sub     rdx, r12
        add     r8, rax
        adc     r9, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x140]
        mul     rbx
        sub     rdx, r12
        add     r9, rax
        adc     r10, rdx
        sbb     r12, r12
        mov     rax, [rsp+0x148]
        mul     rbx
        sub     rdx, r12
        add     r10, rax
        adc     r11, rdx
        sbb     r12, r12
        neg     r12
        mov     rbx, r13
        shl     rbx, 0x20
        add     rbx, r13
        xor     ebp, ebp
        movabs  rax, 0xffffffff00000001
        mul     rbx
        mov     r13, rdx
        movabs  rax, 0xffffffff
        mul     rbx
        add     rax, r13
        adc     rdx, rbx
        adc     ebp, ebp
        sub     r14, rax
        sbb     r15, rdx
        sbb     r8, rbp
        sbb     r9, 0x0
        sbb     r10, 0x0
        sbb     rbx, 0x0
        add     r11, rbx
        adc     r12, 0x0
        xor     edx, edx
        xor     ebp, ebp
        xor     r13d, r13d
        movabs  rax, 0xffffffff00000001
        add     rax, r14
        mov     ebx, 0xffffffff
        adc     rbx, r15
        mov     ecx, 0x1
        adc     rcx, r8
        adc     rdx, r9
        adc     rbp, r10
        adc     r13, r11
        adc     r12, 0x0
        cmovne  r14, rax
        cmovne  r15, rbx
        cmovne  r8, rcx
        cmovne  r9, rdx
        cmovne  r10, rbp
        cmovne  r11, r13
        mov     [rsp+0xf0], r14
        mov     [rsp+0xf8], r15
        mov     [rsp+0x100], r8
        mov     [rsp+0x108], r9
        mov     [rsp+0x110], r10
        mov     [rsp+0x118], r11
        mov     rcx, [rsp+0xb8]
        mov     r13, rcx
        shr     rcx, 0x3e
        mov     r12, [rsp+0xb0]
        shld    r13, r12, 0x2
        mov     r11, [rsp+0xa8]
        shld    r12, r11, 0x2
        mov     r10, [rsp+0xa0]
        shld    r11, r10, 0x2
        mov     r9, [rsp+0x98]
        shld    r10, r9, 0x2
        mov     r8, [rsp+0x90]
        shld    r9, r8, 0x2
        shl     r8, 0x2
        add     rcx, 0x1
        sub     r8, [rsp+0x120]
        sbb     r9, [rsp+0x128]
        sbb     r10, [rsp+0x130]
        sbb     r11, [rsp+0x138]
        sbb     r12, [rsp+0x140]
        sbb     r13, [rsp+0x148]
        sbb     rcx, 0x0
        movabs  rax, 0xffffffff00000001
        mul     rcx
        add     r8, rax
        adc     r9, rdx
        adc     r10, rcx
        mov     rax, rcx
        sbb     rcx, rcx
        mov     edx, 0xffffffff
        neg     rcx
        mul     rdx
        add     r9, rax
        adc     r10, rdx
        adc     r11, rcx
        adc     r12, 0x0
        adc     r13, 0x0
        sbb     rcx, rcx
        not     rcx
        mov     edx, 0xffffffff
        xor     rax, rax
        and     rdx, rcx
        sub     rax, rdx
        and     rcx, 0x1
        sub     r8, rax
        mov     [rdi], r8
        sbb     r9, rdx
        mov     [rdi+0x8], r9
        sbb     r10, rcx
        mov     [rdi+0x10], r10
        sbb     r11, 0x0
        mov     [rdi+0x18], r11
        sbb     r12, 0x0
        mov     [rdi+0x20], r12
        sbb     r13, 0x0
        mov     [rdi+0x28], r13
        movabs  r8, 0xffffffff
        sub     r8, [rsp+0xc0]
        movabs  r9, 0xffffffff00000000
        sbb     r9, [rsp+0xc8]
        mov     r10, 0xfffffffffffffffe
        sbb     r10, [rsp+0xd0]
        mov     r11, 0xffffffffffffffff
        sbb     r11, [rsp+0xd8]
        mov     r12, 0xffffffffffffffff
        sbb     r12, [rsp+0xe0]
        mov     r13, 0xffffffffffffffff
        sbb     r13, [rsp+0xe8]
        mov     r14, r13
        shr     r14, 0x3d
        shld    r13, r12, 0x3
        shld    r12, r11, 0x3
        shld    r11, r10, 0x3
        shld    r10, r9, 0x3
        shld    r9, r8, 0x3
        shl     r8, 0x3
        add     r14, 0x1
        mov     ecx, 0x3
        mov     rax, [rsp+0xf0]
        mul     rcx
        add     r8, rax
        adc     r9, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0xf8]
        mul     rcx
        sub     rdx, rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x100]
        mul     rcx
        sub     rdx, rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x108]
        mul     rcx
        sub     rdx, rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x110]
        mul     rcx
        sub     rdx, rbx
        add     r12, rax
        adc     r13, rdx
        sbb     rbx, rbx
        mov     rax, [rsp+0x118]
        mul     rcx
        sub     rdx, rbx
        add     r13, rax
        adc     r14, rdx
        movabs  rax, 0xffffffff00000001
        mul     r14
        add     r8, rax
        adc     r9, rdx
        adc     r10, r14
        mov     rax, r14
        sbb     rcx, rcx
        mov     edx, 0xffffffff
        neg     rcx
        mul     rdx
        add     r9, rax
        adc     r10, rdx
        adc     r11, rcx
        adc     r12, 0x0
        adc     r13, 0x0
        sbb     rcx, rcx
        not     rcx
        mov     edx, 0xffffffff
        xor     rax, rax
        and     rdx, rcx
        sub     rax, rdx
        and     rcx, 0x1
        sub     r8, rax
        mov     [rdi+0x30], r8
        sbb     r9, rdx
        mov     [rdi+0x38], r9
        sbb     r10, rcx
        mov     [rdi+0x40], r10
        sbb     r11, 0x0
        mov     [rdi+0x48], r11
        sbb     r12, 0x0
        mov     [rdi+0x50], r12
        sbb     r13, 0x0
        mov     [rdi+0x58], r13
        CFI_INC_RSP(344)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp384_montjscalarmul_alt_p384_montjdouble)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
