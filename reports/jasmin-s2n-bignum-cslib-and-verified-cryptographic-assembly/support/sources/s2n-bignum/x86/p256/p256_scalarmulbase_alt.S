// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Scalar multiplication for precomputed point on NIST curve P-256
// Input scalar[4], blocksize, table[]; output res[8]
//
// extern void p256_scalarmulbase_alt
//   (uint64_t res[static 8],
//    const uint64_t scalar[static 4],
//    uint64_t blocksize,
//    const uint64_t *table);
//
// Given scalar = n and point = P, assumed to be on the NIST elliptic
// curve P-256, the input argument "table" is expected to be a table of
// multiples of the point P in Montgomery-affine form, with each block
// corresponding to "blocksize" bits of the scalar as follows, where
// B = 2^{blocksize-1} (e.g. B = 8 for blocksize = 4):
//
// For each i,j with blocksize * i <= 256 and 1 <= j <= B
// the multiple 2^{blocksize * i} * j * P is stored at
// tab[8 * (B * i + (j - 1))], considered as uint64_t pointers
// or tab + 64 * (B * i + (j - 1)) as byte pointers.
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = blocksize, RCX = table
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = blocksize, R9 = table
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p256_scalarmulbase_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(p256_scalarmulbase_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p256_scalarmulbase_alt)


        .text
        .balign 32

// Size of individual field elements

#define NUMSIZE 32

// Intermediate variables on the stack. The last z2, z3 values can
// safely be overlaid on "nacc", which is no longer needed at the end.
// Uppercase syntactic variants make x86_att version simpler to generate

#define RSCALAR (0*NUMSIZE)
#define ACC (1*NUMSIZE)
#define NACC (4*NUMSIZE)
#define TABENT (7*NUMSIZE)
#define Z2 (4*NUMSIZE)
#define Z3 (5*NUMSIZE)

#define rscalar rsp+RSCALAR
#define acc rsp+ACC
#define nacc rsp+NACC
#define tabent rsp+TABENT

#define z2 rsp+Z2
#define z3 rsp+Z3

#define res [rsp+(9*NUMSIZE)]
#define blocksize [rsp+(9*NUMSIZE+8)]
#define table [rsp+(9*NUMSIZE+16)]
#define i [rsp+(9*NUMSIZE+24)]
#define bf [rsp+(9*NUMSIZE+32)]
#define cf [rsp+(9*NUMSIZE+40)]
#define j [rsp+(9*NUMSIZE+48)]

#define NSPACE 11*NUMSIZE

S2N_BN_SYMBOL(p256_scalarmulbase_alt):
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
        mov     rcx, r9
        CFI_CALL(Lp256_scalarmulbase_alt_standard)
        CFI_POP(rsi)
        CFI_POP(rdi)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(p256_scalarmulbase_alt)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp256_scalarmulbase_alt_standard)

Lp256_scalarmulbase_alt_standard:
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

// Preserve the input arguments except the scalar, since that gets absorbed
// immediately. The "table" value subsequently gets shifted up each iteration
// of the loop, while "res" and "blocksize" are static throughout.

        mov     res, rdi
        mov     blocksize, rdx
        mov     table, rcx

// Load the digits of group order n_256 = [r15;r14;r13;r12]

        mov     r12, 0xf3b9cac2fc632551
        mov     r13, 0xbce6faada7179e84
        mov     r14, 0xffffffffffffffff
        mov     r15, 0xffffffff00000000

// First, reduce the input scalar mod n_256, i.e. conditionally subtract n_256
// Store it to "rscalar" (reduced scalar)

        mov     r8, [rsi]
        sub     r8, r12
        mov     r9, [rsi+8]
        sbb     r9, r13
        mov     r10, [rsi+16]
        sbb     r10, r14
        mov     r11, [rsi+24]
        sbb     r11, r15

        cmovc   r8, [rsi]
        cmovc   r9, [rsi+8]
        cmovc   r10, [rsi+16]
        cmovc   r11, [rsi+24]

        mov     [rsp+RSCALAR], r8
        mov     [rsp+RSCALAR+8], r9
        mov     [rsp+RSCALAR+16], r10
        mov     [rsp+RSCALAR+24], r11

// Initialize the accumulator to all zeros and the "carry flag" cf to 0

        xor     eax, eax

        mov     [rsp+ACC], rax
        mov     [rsp+ACC+8], rax
        mov     [rsp+ACC+16], rax
        mov     [rsp+ACC+24], rax
        mov     [rsp+ACC+32], rax
        mov     [rsp+ACC+40], rax
        mov     [rsp+ACC+48], rax
        mov     [rsp+ACC+56], rax
        mov     [rsp+ACC+64], rax
        mov     [rsp+ACC+72], rax
        mov     [rsp+ACC+80], rax
        mov     [rsp+ACC+88], rax

        mov     cf, rax

// Main loop over {i >= 0 | blocksize * i <= 256}. Note the non-strict
// inequality, to allow top carry for any choices of blocksize.

        mov     i, rax

Lp256_scalarmulbase_alt_loop:

// The next raw bitfield is bf = bitfield(blocksize * i,blocksize) + cf,
// adding in the deferred carry cf. We then shift the whole scalar right
// by blocksize so we can keep picking bitfield(0,blocksize).

        mov     r8, [rsp+RSCALAR]
        mov     r9, [rsp+RSCALAR+8]
        mov     r10, [rsp+RSCALAR+16]
        mov     r11, [rsp+RSCALAR+24]

        mov     rcx, blocksize
        mov     eax, 1
        shl     rax, cl
        dec     rax
        and     rax, r8

        shrd    r8, r9, cl
        shrd    r9, r10, cl
        shrd    r10, r11, cl
        shr     r11, cl

        add     rax, cf
        mov     bf, rax

        mov    [rsp+RSCALAR], r8
        mov    [rsp+RSCALAR+8], r9
        mov    [rsp+RSCALAR+16], r10
        mov    [rsp+RSCALAR+24], r11

// Now if bf <= B we just select entry j, unnegated and set cf = 0.
// If bf > B we set j = 2 * B - bf and negate the j'th entry, setting cf = 1.
// In either case we ultimately add bf, in the latter case with deferred
// carry as 2 * B - (2 * B - bf) = bf.

        mov     eax, 1
        mov     rcx, blocksize
        shl     rax, cl
        mov     rbx, rax
        shr     rax, 1

        sub     rbx, bf
        cmp     rax, bf

        cmovnc  rbx, bf
        sbb     rax, rax
        mov     j, rbx
        neg     rax
        mov     cf, rax

// Load table entry j - 1 for nonzero j in constant-time style.

        mov     rcx, blocksize
        dec     rcx
        mov     esi, 1
        shl     rsi, cl
        mov     r12, j
        mov     rbp, table

Lp256_scalarmulbase_alt_tabloop:
        sub     r12, 1
        cmovz   rax, [rbp]
        cmovz   rbx, [rbp+8]
        cmovz   rcx, [rbp+16]
        cmovz   rdx, [rbp+24]
        cmovz   r8, [rbp+32]
        cmovz   r9, [rbp+40]
        cmovz   r10, [rbp+48]
        cmovz   r11, [rbp+56]

        add     rbp, 64
        dec     rsi
        jnz     Lp256_scalarmulbase_alt_tabloop

        mov     table, rbp

// Before storing back, optionally negate the y coordinate of the table entry

        xor     r14d, r14d
        lea     r12, [r14-1]
        mov     r15, 0x00000000ffffffff
        mov     r13, r15
        neg     r15

        sub     r12, r8
        sbb     r13, r9
        sbb     r14, r10
        sbb     r15, r11

        mov     [rsp+TABENT], rax
        mov     [rsp+TABENT+8], rbx
        mov     [rsp+TABENT+16], rcx
        mov     [rsp+TABENT+24], rdx

        mov     rax, cf
        test    rax, rax
        cmovnz  r8, r12
        cmovnz  r9, r13
        cmovnz  r10, r14
        cmovnz  r11, r15

        mov     [rsp+TABENT+32], r8
        mov     [rsp+TABENT+40], r9
        mov     [rsp+TABENT+48], r10
        mov     [rsp+TABENT+56], r11

// Add the adjusted table point to the accumulator

        lea     rdi, [rsp+NACC]
        lea     rsi, [rsp+ACC]
        lea     rdx, [rsp+TABENT]
        CFI_CALL(Lp256_scalarmulbase_alt_local_p256_montjmixadd)

// However, only commit that update to the accumulator if j is nonzero,
// because the mixed addition function does not handle this case directly,
// and in any case we didn't choose the table entry appropriately.

        mov     rax, j
        test    rax, rax

        mov     rax, [rsp+ACC]
        cmovnz  rax, [rsp+NACC]
        mov     [rsp+ACC],rax

        mov     rax, [rsp+ACC+8]
        cmovnz  rax, [rsp+NACC+8]
        mov     [rsp+ACC+8],rax

        mov     rax, [rsp+ACC+16]
        cmovnz  rax, [rsp+NACC+16]
        mov     [rsp+ACC+16],rax

        mov     rax, [rsp+ACC+24]
        cmovnz  rax, [rsp+NACC+24]
        mov     [rsp+ACC+24],rax

        mov     rax, [rsp+ACC+32]
        cmovnz  rax, [rsp+NACC+32]
        mov     [rsp+ACC+32],rax

        mov     rax, [rsp+ACC+40]
        cmovnz  rax, [rsp+NACC+40]
        mov     [rsp+ACC+40],rax

        mov     rax, [rsp+ACC+48]
        cmovnz  rax, [rsp+NACC+48]
        mov     [rsp+ACC+48],rax

        mov     rax, [rsp+ACC+56]
        cmovnz  rax, [rsp+NACC+56]
        mov     [rsp+ACC+56],rax

        mov     rax, [rsp+ACC+64]
        cmovnz  rax, [rsp+NACC+64]
        mov     [rsp+ACC+64],rax

        mov     rax, [rsp+ACC+72]
        cmovnz  rax, [rsp+NACC+72]
        mov     [rsp+ACC+72],rax

        mov     rax, [rsp+ACC+80]
        cmovnz  rax, [rsp+NACC+80]
        mov     [rsp+ACC+80],rax

        mov     rax, [rsp+ACC+88]
        cmovnz  rax, [rsp+NACC+88]
        mov     [rsp+ACC+88],rax

// Loop while blocksize * i <= 256

        mov     rax, i
        inc     rax
        mov     i, rax

        imul    rax, blocksize
        cmp     rax, 257
        jc      Lp256_scalarmulbase_alt_loop

// That's the end of the main loop, and we just need to translate
// back from the Jacobian representation to affine. First of all,
// let z2 = 1/z^2 and z3 = 1/z^3, both without Montgomery form

        lea     rdi, [rsp+Z2]
        lea     rsi, [rsp+ACC+64]
        CFI_CALL(Lp256_scalarmulbase_alt_local_montsqr_p256)

        lea     rdi, [rsp+Z3]
        lea     rsi, [rsp+ACC+64]
        lea     rdx, [rsp+Z2]
        CFI_CALL(Lp256_scalarmulbase_alt_local_montmul_p256)

        lea     rdi, [rsp+Z2]
        lea     rsi, [rsp+Z3]
        CFI_CALL(Lp256_scalarmulbase_alt_local_demont_p256)

        lea     rdi, [rsp+Z3]
        lea     rsi, [rsp+Z2]
        CFI_CALL(Lp256_scalarmulbase_alt_local_inv_p256)

        lea     rdi, [rsp+Z2]
        lea     rsi, [rsp+ACC+64]
        lea     rdx, [rsp+Z3]
        CFI_CALL(Lp256_scalarmulbase_alt_local_montmul_p256)

// Convert back from Jacobian (X, Y, Z) |-> (X/Z^2, Y/Z^3)

        mov     rdi, res
        lea     rsi, [rsp+ACC]
        lea     rdx, [rsp+Z2]
        mov     rbx, rdi
        CFI_CALL(Lp256_scalarmulbase_alt_local_montmul_p256)

        lea     rdi, [rbx+32]
        lea     rsi, [rsp+ACC+32]
        lea     rdx, [rsp+Z3]
        CFI_CALL(Lp256_scalarmulbase_alt_local_montmul_p256)

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
S2N_BN_SIZE_DIRECTIVE(Lp256_scalarmulbase_alt_standard)
#else
S2N_BN_SIZE_DIRECTIVE(p256_scalarmulbase_alt)
#endif

// Local copies of subroutines, complete clones at the moment

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp256_scalarmulbase_alt_local_demont_p256)

Lp256_scalarmulbase_alt_local_demont_p256:
        CFI_START
        mov     r8, [rsi]
        mov     r9, [rsi+0x8]
        mov     r10, [rsi+0x10]
        mov     r11, [rsi+0x18]
        movabs  rcx, 0x100000000
        mov     rax, r8
        mul     rcx
        add     r9, rax
        adc     r10, rdx
        sbb     rsi, rsi
        mov     rax, r9
        mul     rcx
        sub     rdx, rsi
        add     r10, rax
        adc     r11, rdx
        sbb     rsi, rsi
        neg     rcx
        neg     rsi
        inc     rcx
        mov     rax, r8
        mul     rcx
        add     r11, rax
        adc     rsi, rdx
        sbb     r8, r8
        neg     r8
        mov     rax, r9
        mul     rcx
        add     rsi, rax
        adc     r8, rdx
        neg     rcx
        inc     rcx
        mov     rax, r10
        mul     rcx
        add     r11, rax
        adc     rsi, rdx
        sbb     r9, r9
        mov     rax, r11
        mul     rcx
        sub     rdx, r9
        add     rsi, rax
        adc     r8, rdx
        sbb     r9, r9
        neg     rcx
        neg     r9
        inc     rcx
        mov     rax, r10
        mul     rcx
        add     r8, rax
        adc     r9, rdx
        sbb     r10, r10
        neg     r10
        mov     rax, r11
        mul     rcx
        add     r9, rax
        adc     r10, rdx
        mov     [rdi], rsi
        mov     [rdi+0x8], r8
        mov     [rdi+0x10], r9
        mov     [rdi+0x18], r10
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp256_scalarmulbase_alt_local_demont_p256)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp256_scalarmulbase_alt_local_inv_p256)

Lp256_scalarmulbase_alt_local_inv_p256:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(240)
        mov     [rsp+0xe0], rdi
        xor     ecx, ecx
        mov     edx, 0xffffffff
        mov     rbx, rdx
        lea     rax, [rcx-0x1]
        neg     rdx
        mov     [rsp], rax
        mov     [rsp+0x8], rbx
        mov     [rsp+0x10], rcx
        mov     [rsp+0x18], rdx
        mov     [rsp+0x20], rcx
        mov     r8, [rsi]
        mov     r9, [rsi+0x8]
        mov     r10, [rsi+0x10]
        mov     r11, [rsi+0x18]
        lea     rax, [rcx+0x1]
        add     rax, r8
        lea     rbx, [rdx-0x1]
        adc     rbx, r9
        not     rcx
        adc     rcx, r10
        not     rdx
        adc     rdx, r11
        cmovae  rax, r8
        cmovae  rbx, r9
        cmovae  rcx, r10
        cmovae  rdx, r11
        mov     [rsp+0x28], rax
        mov     [rsp+0x30], rbx
        mov     [rsp+0x38], rcx
        mov     [rsp+0x40], rdx
        xor     eax, eax
        mov     [rsp+0x48], rax
        xor     eax, eax
        mov     [rsp+0x50], rax
        mov     [rsp+0x58], rax
        mov     [rsp+0x60], rax
        mov     [rsp+0x68], rax
        movabs  rcx, 0x4000000000000
        mov     [rsp+0x78], rcx
        mov     [rsp+0x80], rax
        mov     [rsp+0x88], rax
        mov     [rsp+0x90], rax
        mov     QWORD PTR [rsp+0xb0], 0xa
        mov     QWORD PTR [rsp+0xb8], 0x1
        jmp     Lp256_scalarmulbase_alt_inv_midloop
Lp256_scalarmulbase_alt_inv_loop:
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
        mov     [rsp+0xa0], rdi
        mov     rax, r12
        and     rax, r13
        mov     rsi, r14
        and     rsi, r15
        add     rsi, rax
        mov     [rsp+0xa8], rsi
        xor     ebx, ebx
        mov     rax, [rsp]
        xor     rax, r9
        mul     r8
        add     rdi, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x28]
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
        mov     rax, [rsp+0x28]
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
        mov     rax, [rsp+0x30]
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
        mov     rax, [rsp+0x30]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rdi, rdx
        shrd    rsi, rbp, 0x3b
        mov     [rsp+0x28], rsi
        xor     esi, esi
        mov     rax, [rsp+0x10]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rsi, rdx
        mov     rax, [rsp+0x38]
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
        mov     rax, [rsp+0x38]
        xor     rax, r15
        mul     r14
        add     rdi, rax
        adc     rbx, rdx
        shrd    rbp, rdi, 0x3b
        mov     [rsp+0x30], rbp
        mov     rax, [rsp+0x18]
        xor     rax, r9
        mov     rbp, [rsp+0x20]
        xor     rbp, r9
        and     rbp, r8
        neg     rbp
        mul     r8
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+0x40]
        xor     rax, r11
        mov     rdx, [rsp+0x48]
        xor     rdx, r11
        and     rdx, r10
        sub     rbp, rdx
        mul     r10
        add     rsi, rax
        adc     rbp, rdx
        shrd    rcx, rsi, 0x3b
        mov     [rsp+0x10], rcx
        shrd    rsi, rbp, 0x3b
        sar     rbp, 0x3b
        mov     rax, [rsp+0x18]
        mov     [rsp+0x18], rsi
        mov     rsi, [rsp+0x20]
        mov     [rsp+0x20], rbp
        xor     rax, r13
        xor     rsi, r13
        and     rsi, r12
        neg     rsi
        mul     r12
        add     rbx, rax
        adc     rsi, rdx
        mov     rax, [rsp+0x40]
        xor     rax, r15
        mov     rdx, [rsp+0x48]
        xor     rdx, r15
        and     rdx, r14
        sub     rsi, rdx
        mul     r14
        add     rbx, rax
        adc     rsi, rdx
        shrd    rdi, rbx, 0x3b
        mov     [rsp+0x38], rdi
        shrd    rbx, rsi, 0x3b
        mov     [rsp+0x40], rbx
        sar     rsi, 0x3b
        mov     [rsp+0x48], rsi
        mov     rbx, [rsp+0xa0]
        mov     rbp, [rsp+0xa8]
        xor     ecx, ecx
        mov     rax, [rsp+0x50]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+0x78]
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
        mov     rax, [rsp+0x78]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+0x78], rbp
        xor     ebx, ebx
        mov     rax, [rsp+0x58]
        xor     rax, r9
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x80]
        xor     rax, r11
        mul     r10
        add     rcx, rax
        adc     rbx, rdx
        xor     ebp, ebp
        mov     rax, [rsp+0x58]
        xor     rax, r13
        mul     r12
        mov     [rsp+0x58], rcx
        add     rsi, rax
        adc     rbp, rdx
        mov     rax, [rsp+0x80]
        xor     rax, r15
        mul     r14
        add     rsi, rax
        adc     rbp, rdx
        mov     [rsp+0x80], rsi
        xor     ecx, ecx
        mov     rax, [rsp+0x60]
        xor     rax, r9
        mul     r8
        add     rbx, rax
        adc     rcx, rdx
        mov     rax, [rsp+0x88]
        xor     rax, r11
        mul     r10
        add     rbx, rax
        adc     rcx, rdx
        xor     esi, esi
        mov     rax, [rsp+0x60]
        xor     rax, r13
        mul     r12
        mov     [rsp+0x60], rbx
        add     rbp, rax
        adc     rsi, rdx
        mov     rax, [rsp+0x88]
        xor     rax, r15
        mul     r14
        add     rbp, rax
        adc     rsi, rdx
        mov     [rsp+0x88], rbp
        mov     rax, [rsp+0x68]
        xor     rax, r9
        mov     rbx, r9
        and     rbx, r8
        neg     rbx
        mul     r8
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, [rsp+0x90]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     rbx, rdx
        mul     r10
        add     rcx, rax
        adc     rdx, rbx
        mov     rax, [rsp+0x68]
        mov     [rsp+0x68], rcx
        mov     [rsp+0x70], rdx
        xor     rax, r13
        mov     rcx, r13
        and     rcx, r12
        neg     rcx
        mul     r12
        add     rsi, rax
        adc     rcx, rdx
        mov     rax, [rsp+0x90]
        xor     rax, r15
        mov     rdx, r15
        and     rdx, r14
        sub     rcx, rdx
        mul     r14
        add     rsi, rax
        adc     rdx, rcx
        mov     [rsp+0x90], rsi
        mov     [rsp+0x98], rdx
        movabs  r8, 0xe000000000000000
        add     r8, [rsp+0x50]
        mov     r9, 0xffffffffffffffff
        adc     r9, [rsp+0x58]
        mov     r10, 0x1fffffff
        adc     r10, [rsp+0x60]
        movabs  r11, 0x2000000000000000
        adc     r11, [rsp+0x68]
        movabs  r12, 0x1fffffffe0000000
        adc     r12, [rsp+0x70]
        mov     rbx, r8
        shl     rbx, 0x20
        movabs  rax, 0xffffffff00000001
        mul     r8
        shr     r8, 0x20
        add     r9, rbx
        adc     r10, r8
        adc     r11, rax
        adc     r12, rdx
        sbb     rax, rax
        mov     ebx, 0xffffffff
        and     rbx, rax
        movabs  rdx, 0xffffffff00000001
        and     rdx, rax
        sub     r9, rax
        mov     [rsp+0x50], r9
        sbb     r10, rbx
        mov     [rsp+0x58], r10
        sbb     r11, 0x0
        mov     [rsp+0x60], r11
        sbb     r12, rdx
        mov     [rsp+0x68], r12
        movabs  r8, 0xe000000000000000
        add     r8, [rsp+0x78]
        mov     r9, 0xffffffffffffffff
        adc     r9, [rsp+0x80]
        mov     r10, 0x1fffffff
        adc     r10, [rsp+0x88]
        movabs  r11, 0x2000000000000000
        adc     r11, [rsp+0x90]
        movabs  r12, 0x1fffffffe0000000
        adc     r12, [rsp+0x98]
        mov     rbx, r8
        shl     rbx, 0x20
        movabs  rax, 0xffffffff00000001
        mul     r8
        shr     r8, 0x20
        add     r9, rbx
        adc     r10, r8
        adc     r11, rax
        adc     r12, rdx
        sbb     rax, rax
        mov     ebx, 0xffffffff
        and     rbx, rax
        movabs  rdx, 0xffffffff00000001
        and     rdx, rax
        sub     r9, rax
        mov     [rsp+0x78], r9
        sbb     r10, rbx
        mov     [rsp+0x80], r10
        sbb     r11, 0x0
        mov     [rsp+0x88], r11
        sbb     r12, rdx
        mov     [rsp+0x90], r12
Lp256_scalarmulbase_alt_inv_midloop:
        mov     rsi, [rsp+0xb8]
        mov     rdx, [rsp]
        mov     rcx, [rsp+0x28]
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
        mov     [rsp+0xc0], rdx
        mov     [rsp+0xc8], rbx
        mov     [rsp+0xd0], rdi
        mov     [rsp+0xd8], rcx
        mov     r12, [rsp]
        imul    rdi, r12
        imul    r12, rdx
        mov     r13, [rsp+0x28]
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
        mov     rax, [rsp+0xc0]
        imul    rax, r8
        mov     rdx, [rsp+0xd0]
        imul    rdx, r15
        imul    r8, [rsp+0xc8]
        imul    r15, [rsp+0xd8]
        add     r15, r8
        lea     r9, [rax+rdx]
        mov     rax, [rsp+0xc0]
        imul    rax, r10
        mov     rdx, [rsp+0xd0]
        imul    rdx, r11
        imul    r10, [rsp+0xc8]
        imul    r11, [rsp+0xd8]
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
        mov     [rsp+0xb8], rsi
        dec     QWORD PTR [rsp+0xb0]
        jne     Lp256_scalarmulbase_alt_inv_loop
        mov     rax, [rsp]
        mov     rcx, [rsp+0x28]
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
        mov     rax, [rsp+0x50]
        xor     rax, r9
        mul     r8
        add     r12, rax
        adc     r13, rdx
        mov     rax, [rsp+0x78]
        xor     rax, r11
        mul     r10
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        mov     rax, [rsp+0x58]
        xor     rax, r9
        mul     r8
        add     r13, rax
        adc     r14, rdx
        mov     rax, [rsp+0x80]
        xor     rax, r11
        mul     r10
        add     r13, rax
        adc     r14, rdx
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        xor     rax, r9
        mul     r8
        add     r14, rax
        adc     r15, rdx
        mov     rax, [rsp+0x88]
        xor     rax, r11
        mul     r10
        add     r14, rax
        adc     r15, rdx
        mov     rax, [rsp+0x68]
        xor     rax, r9
        and     r9, r8
        neg     r9
        mul     r8
        add     r15, rax
        adc     r9, rdx
        mov     rax, [rsp+0x90]
        xor     rax, r11
        mov     rdx, r11
        and     rdx, r10
        sub     r9, rdx
        mul     r10
        add     r15, rax
        adc     r9, rdx
        mov     [rsp+0x50], r12
        mov     [rsp+0x58], r13
        mov     [rsp+0x60], r14
        mov     [rsp+0x68], r15
        mov     [rsp+0x70], r9
        movabs  r8, 0xe000000000000000
        add     r8, [rsp+0x50]
        mov     r9, 0xffffffffffffffff
        adc     r9, [rsp+0x58]
        mov     r10, 0x1fffffff
        adc     r10, [rsp+0x60]
        movabs  r11, 0x2000000000000000
        adc     r11, [rsp+0x68]
        movabs  r12, 0x1fffffffe0000000
        adc     r12, [rsp+0x70]
        mov     rbx, r8
        shl     rbx, 0x20
        movabs  rax, 0xffffffff00000001
        mul     r8
        shr     r8, 0x20
        add     r9, rbx
        adc     r10, r8
        adc     r11, rax
        adc     r12, rdx
        sbb     rax, rax
        mov     ebx, 0xffffffff
        and     rbx, rax
        movabs  rdx, 0xffffffff00000001
        and     rdx, rax
        sub     r9, rax
        mov     [rsp+0x50], r9
        sbb     r10, rbx
        mov     [rsp+0x58], r10
        sbb     r11, 0x0
        mov     [rsp+0x60], r11
        sbb     r12, rdx
        mov     [rsp+0x68], r12
        mov     r8, [rsp+0x50]
        mov     r9, [rsp+0x58]
        mov     r10, [rsp+0x60]
        mov     r11, [rsp+0x68]
        mov     eax, 0x1
        mov     ebx, 0xffffffff
        lea     rcx, [rax-0x2]
        lea     rdx, [rbx-0x1]
        not     rbx
        add     rax, r8
        adc     rbx, r9
        adc     rcx, r10
        adc     rdx, r11
        cmovae  rax, r8
        cmovae  rbx, r9
        cmovae  rcx, r10
        cmovae  rdx, r11
        mov     rdi, [rsp+0xe0]
        mov     [rdi], rax
        mov     [rdi+0x8], rbx
        mov     [rdi+0x10], rcx
        mov     [rdi+0x18], rdx
        CFI_INC_RSP(240)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp256_scalarmulbase_alt_local_inv_p256)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp256_scalarmulbase_alt_local_montmul_p256)

Lp256_scalarmulbase_alt_local_montmul_p256:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        mov     rcx, rdx
        mov     rbx, [rcx]
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
        mov     rbx, [rcx+0x8]
        xor     r13d, r13d
        mov     rax, [rsi]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rcx+0x10]
        xor     r15d, r15d
        mov     rax, [rsi]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rcx+0x18]
        xor     r8d, r8d
        mov     rax, [rsi]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x10]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x18]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rdi], r12
        mov     [rdi+0x8], r13
        mov     [rdi+0x10], r14
        mov     [rdi+0x18], r15
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp256_scalarmulbase_alt_local_montmul_p256)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp256_scalarmulbase_alt_local_montsqr_p256)

Lp256_scalarmulbase_alt_local_montsqr_p256:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        mov     rax, [rsi]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsi+0x8]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x18]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x10]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsi+0x18]
        mov     rax, [rsi+0x8]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsi+0x8]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x10]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x18]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rdi], r12
        mov     [rdi+0x8], r13
        mov     [rdi+0x10], r14
        mov     [rdi+0x18], r15
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp256_scalarmulbase_alt_local_montsqr_p256)

S2N_BN_FUNCTION_TYPE_DIRECTIVE(Lp256_scalarmulbase_alt_local_p256_montjmixadd)

Lp256_scalarmulbase_alt_local_p256_montjmixadd:
        CFI_START
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(192)
        mov     rbp, rdx
        mov     rax, [rsi+0x40]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsi+0x48]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsi+0x58]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsi+0x50]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsi+0x58]
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsi+0x48]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x50]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsi+0x58]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rbx, [rbp+0x20]
        mov     rax, [rsi+0x40]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsi+0x48]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x50]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsi+0x58]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rbp+0x28]
        xor     r13d, r13d
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rbp+0x30]
        xor     r15d, r15d
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rbp+0x38]
        xor     r8d, r8d
        mov     rax, [rsi+0x40]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x48]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x50]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsi+0x58]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     rbx, [rbp+0x0]
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
        mov     rbx, [rbp+0x8]
        xor     r13d, r13d
        mov     rax, [rsp]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rbp+0x10]
        xor     r15d, r15d
        mov     rax, [rsp]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rbp+0x18]
        xor     r8d, r8d
        mov     rax, [rsp]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        mov     rbx, [rsp+0x20]
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
        mov     rbx, [rsp+0x28]
        xor     r13d, r13d
        mov     rax, [rsp]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x30]
        xor     r15d, r15d
        mov     rax, [rsp]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x38]
        xor     r8d, r8d
        mov     rax, [rsp]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x10]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x18]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x20], r12
        mov     [rsp+0x28], r13
        mov     [rsp+0x30], r14
        mov     [rsp+0x38], r15
        mov     rax, [rsp+0x40]
        sub     rax, [rsi]
        mov     rcx, [rsp+0x48]
        sbb     rcx, [rsi+0x8]
        mov     r8, [rsp+0x50]
        sbb     r8, [rsi+0x10]
        mov     r9, [rsp+0x58]
        sbb     r9, [rsi+0x18]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0xa0], rax
        adc     rcx, r10
        mov     [rsp+0xa8], rcx
        adc     r8, 0x0
        mov     [rsp+0xb0], r8
        adc     r9, rdx
        mov     [rsp+0xb8], r9
        mov     rax, [rsp+0x20]
        sub     rax, [rsi+0x20]
        mov     rcx, [rsp+0x28]
        sbb     rcx, [rsi+0x28]
        mov     r8, [rsp+0x30]
        sbb     r8, [rsi+0x30]
        mov     r9, [rsp+0x38]
        sbb     r9, [rsi+0x38]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x20], rax
        adc     rcx, r10
        mov     [rsp+0x28], rcx
        adc     r8, 0x0
        mov     [rsp+0x30], r8
        adc     r9, rdx
        mov     [rsp+0x38], r9
        mov     rax, [rsp+0xa0]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0xb8]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0xb0]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsp+0xb8]
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsp+0xa8]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsp+0xb0]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsp+0xb8]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        mov     rax, [rsp+0x20]
        mov     rbx, rax
        mul     rax
        mov     r8, rax
        mov     r15, rdx
        mov     rax, [rsp+0x28]
        mul     rbx
        mov     r9, rax
        mov     r10, rdx
        mov     rax, [rsp+0x38]
        mov     r13, rax
        mul     rbx
        mov     r11, rax
        mov     r12, rdx
        mov     rax, [rsp+0x30]
        mov     rbx, rax
        mul     r13
        mov     r13, rax
        mov     r14, rdx
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rbx, [rsp+0x38]
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     ecx, ecx
        add     r9, r9
        adc     r10, r10
        adc     r11, r11
        adc     r12, r12
        adc     r13, r13
        adc     r14, r14
        adc     rcx, rcx
        mov     rax, [rsp+0x28]
        mul     rax
        add     r9, r15
        adc     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x30]
        mul     rax
        neg     r15
        adc     r12, rax
        adc     r13, rdx
        sbb     r15, r15
        mov     rax, [rsp+0x38]
        mul     rax
        neg     r15
        adc     r14, rax
        adc     rdx, rcx
        mov     r15, rdx
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, rcx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        xor     r8d, r8d
        mov     rax, r9
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        adc     r14, r8
        adc     r15, r8
        adc     r8, r8
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        xor     r9d, r9d
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        lea     rbx, [rbx-0x1]
        adc     rbx, r13
        lea     r9, [r9-0x1]
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp], r12
        mov     [rsp+0x8], r13
        mov     [rsp+0x10], r14
        mov     [rsp+0x18], r15
        mov     rbx, [rsi]
        mov     rax, [rsp+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsi+0x8]
        xor     r13d, r13d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsi+0x10]
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsi+0x18]
        xor     r8d, r8d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rbx, [rsp+0x40]
        mov     rax, [rsp+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x48]
        xor     r13d, r13d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x50]
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x58]
        xor     r8d, r8d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x40], r12
        mov     [rsp+0x48], r13
        mov     [rsp+0x50], r14
        mov     [rsp+0x58], r15
        mov     rax, [rsp]
        sub     rax, [rsp+0x80]
        mov     rcx, [rsp+0x8]
        sbb     rcx, [rsp+0x88]
        mov     r8, [rsp+0x10]
        sbb     r8, [rsp+0x90]
        mov     r9, [rsp+0x18]
        sbb     r9, [rsp+0x98]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp], rax
        adc     rcx, r10
        mov     [rsp+0x8], rcx
        adc     r8, 0x0
        mov     [rsp+0x10], r8
        adc     r9, rdx
        mov     [rsp+0x18], r9
        mov     rax, [rsp+0x40]
        sub     rax, [rsp+0x80]
        mov     rcx, [rsp+0x48]
        sbb     rcx, [rsp+0x88]
        mov     r8, [rsp+0x50]
        sbb     r8, [rsp+0x90]
        mov     r9, [rsp+0x58]
        sbb     r9, [rsp+0x98]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x60], rax
        adc     rcx, r10
        mov     [rsp+0x68], rcx
        adc     r8, 0x0
        mov     [rsp+0x70], r8
        adc     r9, rdx
        mov     [rsp+0x78], r9
        mov     rbx, [rsi+0x40]
        mov     rax, [rsp+0xa0]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0xa8]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0xb0]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0xb8]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsi+0x48]
        xor     r13d, r13d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsi+0x50]
        xor     r15d, r15d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsi+0x58]
        xor     r8d, r8d
        mov     rax, [rsp+0xa0]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xa8]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb0]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0xb8]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0xa0], r12
        mov     [rsp+0xa8], r13
        mov     [rsp+0xb0], r14
        mov     [rsp+0xb8], r15
        mov     rax, [rsp]
        sub     rax, [rsp+0x40]
        mov     rcx, [rsp+0x8]
        sbb     rcx, [rsp+0x48]
        mov     r8, [rsp+0x10]
        sbb     r8, [rsp+0x50]
        mov     r9, [rsp+0x18]
        sbb     r9, [rsp+0x58]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp], rax
        adc     rcx, r10
        mov     [rsp+0x8], rcx
        adc     r8, 0x0
        mov     [rsp+0x10], r8
        adc     r9, rdx
        mov     [rsp+0x18], r9
        mov     rax, [rsp+0x80]
        sub     rax, [rsp]
        mov     rcx, [rsp+0x88]
        sbb     rcx, [rsp+0x8]
        mov     r8, [rsp+0x90]
        sbb     r8, [rsp+0x10]
        mov     r9, [rsp+0x98]
        sbb     r9, [rsp+0x18]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x80], rax
        adc     rcx, r10
        mov     [rsp+0x88], rcx
        adc     r8, 0x0
        mov     [rsp+0x90], r8
        adc     r9, rdx
        mov     [rsp+0x98], r9
        mov     rbx, [rsi+0x20]
        mov     rax, [rsp+0x60]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x68]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x70]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x78]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsi+0x28]
        xor     r13d, r13d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsi+0x30]
        xor     r15d, r15d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsi+0x38]
        xor     r8d, r8d
        mov     rax, [rsp+0x60]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x68]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x70]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x78]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x60], r12
        mov     [rsp+0x68], r13
        mov     [rsp+0x70], r14
        mov     [rsp+0x78], r15
        mov     rbx, [rsp+0x80]
        mov     rax, [rsp+0x20]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, [rsp+0x28]
        mul     rbx
        xor     r10d, r10d
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsp+0x30]
        mul     rbx
        xor     r11d, r11d
        add     r10, rax
        adc     r11, rdx
        mov     rax, [rsp+0x38]
        mul     rbx
        xor     r12d, r12d
        add     r11, rax
        adc     r12, rdx
        mov     rbx, [rsp+0x88]
        xor     r13d, r13d
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r14
        add     r10, rax
        adc     r11, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x30]
        mul     rbx
        sub     rdx, r14
        add     r11, rax
        adc     r12, rdx
        sbb     r14, r14
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r14
        add     r12, rax
        adc     r13, rdx
        xor     r14d, r14d
        movabs  rbx, 0x100000000
        mov     rax, r8
        mul     rbx
        add     r9, rax
        adc     r10, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r10, rax
        adc     r11, rdx
        sbb     r15, r15
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r8
        mul     rbx
        sub     rdx, r15
        add     r11, rax
        adc     r12, rdx
        sbb     r15, r15
        mov     rax, r9
        mul     rbx
        sub     rdx, r15
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rbx, [rsp+0x90]
        xor     r15d, r15d
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r8
        add     r11, rax
        adc     r12, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x30]
        mul     rbx
        sub     rdx, r8
        add     r12, rax
        adc     r13, rdx
        sbb     r8, r8
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r8
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rbx, [rsp+0x98]
        xor     r8d, r8d
        mov     rax, [rsp+0x20]
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x28]
        mul     rbx
        sub     rdx, r9
        add     r12, rax
        adc     r13, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x30]
        mul     rbx
        sub     rdx, r9
        add     r13, rax
        adc     r14, rdx
        sbb     r9, r9
        mov     rax, [rsp+0x38]
        mul     rbx
        sub     rdx, r9
        add     r14, rax
        adc     r15, rdx
        adc     r8, r8
        xor     r9d, r9d
        movabs  rbx, 0x100000000
        mov     rax, r10
        mul     rbx
        add     r11, rax
        adc     r12, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r12, rax
        adc     r13, rdx
        sbb     rcx, rcx
        not     rbx
        lea     rbx, [rbx+0x2]
        mov     rax, r10
        mul     rbx
        sub     rdx, rcx
        add     r13, rax
        adc     r14, rdx
        sbb     rcx, rcx
        mov     rax, r11
        mul     rbx
        sub     rdx, rcx
        add     r14, rax
        adc     r15, rdx
        adc     r8, r9
        mov     ecx, 0x1
        add     rcx, r12
        dec     rbx
        adc     rbx, r13
        dec     r9
        mov     rax, r9
        adc     r9, r14
        mov     r11d, 0xfffffffe
        adc     r11, r15
        adc     rax, r8
        cmovb   r12, rcx
        cmovb   r13, rbx
        cmovb   r14, r9
        cmovb   r15, r11
        mov     [rsp+0x80], r12
        mov     [rsp+0x88], r13
        mov     [rsp+0x90], r14
        mov     [rsp+0x98], r15
        mov     rax, [rsp+0x80]
        sub     rax, [rsp+0x60]
        mov     rcx, [rsp+0x88]
        sbb     rcx, [rsp+0x68]
        mov     r8, [rsp+0x90]
        sbb     r8, [rsp+0x70]
        mov     r9, [rsp+0x98]
        sbb     r9, [rsp+0x78]
        mov     r10d, 0xffffffff
        sbb     r11, r11
        xor     rdx, rdx
        and     r10, r11
        sub     rdx, r10
        add     rax, r11
        mov     [rsp+0x80], rax
        adc     rcx, r10
        mov     [rsp+0x88], rcx
        adc     r8, 0x0
        mov     [rsp+0x90], r8
        adc     r9, rdx
        mov     [rsp+0x98], r9
        mov     rax, [rsi+0x40]
        mov     rdx, [rsi+0x48]
        or      rax, [rsi+0x50]
        or      rdx, [rsi+0x58]
        or      rax, rdx
        mov     r8, [rsp]
        mov     rax, [rbp+0x0]
        cmove   r8, rax
        mov     r9, [rsp+0x8]
        mov     rax, [rbp+0x8]
        cmove   r9, rax
        mov     r10, [rsp+0x10]
        mov     rax, [rbp+0x10]
        cmove   r10, rax
        mov     r11, [rsp+0x18]
        mov     rax, [rbp+0x18]
        cmove   r11, rax
        mov     r12, [rsp+0x80]
        mov     rax, [rbp+0x20]
        cmove   r12, rax
        mov     r13, [rsp+0x88]
        mov     rax, [rbp+0x28]
        cmove   r13, rax
        mov     r14, [rsp+0x90]
        mov     rax, [rbp+0x30]
        cmove   r14, rax
        mov     r15, [rsp+0x98]
        mov     rax, [rbp+0x38]
        cmove   r15, rax
        mov     [rdi], r8
        mov     [rdi+0x8], r9
        mov     [rdi+0x10], r10
        mov     [rdi+0x18], r11
        mov     [rdi+0x20], r12
        mov     [rdi+0x28], r13
        mov     [rdi+0x30], r14
        mov     [rdi+0x38], r15
        mov     r8, [rsp+0xa0]
        mov     r9, [rsp+0xa8]
        mov     r10, [rsp+0xb0]
        mov     r11, [rsp+0xb8]
        mov     eax, 0x1
        cmove   r8, rax
        movabs  rax, 0xffffffff00000000
        cmove   r9, rax
        mov     rax, 0xffffffffffffffff
        cmove   r10, rax
        mov     eax, 0xfffffffe
        cmove   r11, rax
        mov     [rdi+0x40], r8
        mov     [rdi+0x48], r9
        mov     [rdi+0x50], r10
        mov     [rdi+0x58], r11
        CFI_INC_RSP(192)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(Lp256_scalarmulbase_alt_local_p256_montjmixadd)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
