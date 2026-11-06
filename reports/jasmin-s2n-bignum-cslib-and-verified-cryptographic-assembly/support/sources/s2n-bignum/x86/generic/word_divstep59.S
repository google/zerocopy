// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Perform 59 "divstep" iterations and return signed matrix of updates
// Inputs d, f, g; output m[2][2] and function return
//
// extern int64_t word_divstep59
//  (int64_t m[2][2],int64_t d,uint64_t f,uint64_t g);
//
// Standard x86-64 ABI: RDI = m, RSI = d, RDX = f, RCX = g, returns RAX
// Microsoft x64 ABI:   RCX = m, RDX = d, R8 = f, R9 = g, returns RAX
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(word_divstep59)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(word_divstep59)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(word_divstep59)
        .text

#define mat rdi

#define d rsi
#define fuv rbx
#define grs rcx

#define f r12
#define g r13

#define m r8
#define t r9

#define zero rbp
#define zeroe ebp
#define minus2 rax
#define minus2e eax
#define plus2 rdx
#define plus2e edx

#define m00 r8
#define m01 r9
#define m10 r10
#define m11 r11

S2N_BN_SYMBOL(word_divstep59):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Save extra registers

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)

// Pack f and g into single registers with (negated) update matrices,
// initially the identity matrix. The f_lo and g_lo are initially
// the 20 lowest bits of f and g.
//
// fuv = f_lo - 2^41 * 1 - 2^62 * 0
// grs = g_lo - 2^41 * 0 - 2^62 * 1

        mov     fuv, rdx
        mov     f, rdx
        and     fuv, 0xFFFFF
        mov     rax, 0xFFFFFE0000000000
        or      fuv, rax

        mov     g, rcx
        and     grs, 0xFFFFF
        mov     rax, 0xc000000000000000
        or      grs, rax

// Now do 20 divsteps on that packed format.
//
// At the i'th iteration (starting at i = 0, ending at i = 20)
// the intermediate packed values are of the form
//
// fuv = f_lo - 2^{41-i} * m00 - 2^{62-i} * m01
// grs = g_lo - 2^{41-i} * m10 - 2^{62-i} * m11
//
// where the following matrix indicates the updates to apply
// to the original (full-sized) f and g for those iterations.
//
// [m00 m01] * [f_0] = [f_i]
// [m10 m11]   [g_0]   [g_i]

        mov     minus2, -2
        xor     zeroe, zeroe
        mov     plus2e, 2
        mov     t, fuv
        mov     m, minus2
        test    d, d
        cmovs   m, zero
        test    grs, 1
.set i, 0
.rep 20
        cmovz  m, zero
        cmovz  t, zero
.if (i != 0)
        sar     grs, 1
.endif
        xor     t, m
        xor     d, m
        bt      m, 63
        cmovc   fuv, grs
        mov     m, minus2
        add     d, plus2
        lea     grs, [grs+t]
.if (i != 19)
        cmovs   m, zero
        mov     t, fuv
        test    grs, plus2
.endif
.set i, (i+1)
.endr
        sar     grs, 1

// Extract the matrix entries, but keep them in negated form.
// Store them in the output buffer temporarily.

        mov     eax,  1048576
        lea     m00, [fuv+rax]
        lea     m10, [grs+rax]
        shl     m00, 22
        shl     m10, 22
        sar     m00, 43
        sar     m10, 43

        mov     rax, 2199024304128
        lea     m01, [fuv+rax]
        lea     m11, [grs+rax]
        sar     m01, 42
        sar     m11, 42

        mov     [mat], m00
        mov     [mat+8], m01
        mov     [mat+16], m10
        mov     [mat+24], m11

// Compute updated f and g using the negated matrix entries;
// this flips the signs of f and g but it doesn't matter.
//
//   f = (m00 * f + m01 * g) / 2^20
//   g = (m10 * f + m11 * g) / 2^20
//
// Since we only need another 40 bits, we can do all of that
// computation naively using (implicitly signed) 64-bit words.

        imul    m10, f
        imul    f, m00
        imul    m01, g
        imul    g, m11
        add     f, m01
        add     g, m10
        sar     f, 20
        sar     g, 20

// Re-pack for 20 more rounds

        mov     fuv, f
        and     fuv, 0xFFFFF
        mov     rax, 0xFFFFFE0000000000
        or      fuv, rax

        mov     grs, g
        and     grs, 0xFFFFF
        mov     rax, 0xc000000000000000
        or      grs, rax

// Second block of 20 divsteps in the same style

        mov     minus2, -2
        mov     plus2e, 2
        mov     t, fuv
        mov     m, minus2
        test    d, d
        cmovs   m, zero
        test    grs, 1
.set i, 0
.rep 20
        cmovz  m, zero
        cmovz  t, zero
.if (i != 0)
        sar     grs, 1
.endif
        xor     t, m
        xor     d, m
        bt      m, 63
        cmovc   fuv, grs
        mov     m, minus2
        add     d, plus2
        lea     grs, [grs+t]
.if (i != 19)
        cmovs   m, zero
        mov     t, fuv
        test    grs, plus2
.endif
.set i, (i+1)
.endr
        sar     grs, 1

// Extract the next matrix entries, in negated form again

        mov     eax,  1048576
        lea     m00, [fuv+rax]
        lea     m10, [grs+rax]
        shl     m00, 22
        shl     m10, 22
        sar     m00, 43
        sar     m10, 43

        mov     rax, 2199024304128
        lea     m01, [fuv+rax]
        lea     m11, [grs+rax]
        sar     m01, 42
        sar     m11, 42

// Compute updated f and g using the negated matrix entries,
// and so again flipping (thus actually restoring) the signs.
//
//   f = (n00 * f + n01 * g) / 2^20
//   g = (n10 * f + n11 * g) / 2^20

        mov     fuv, g
        mov     grs, f
        imul    f, m00
        imul    fuv, m01
        add     f, fuv
        imul    g, m11
        imul    grs, m10
        add     g, grs
        sar     f, 20
        sar     g, 20

// Re-pack for 20 more rounds

        mov     fuv, f
        and     fuv, 0xFFFFF
        mov     rax, 0xFFFFFE0000000000
        or      fuv, rax

        mov     grs, g
        and     grs, 0xFFFFF
        mov     rax, 0xc000000000000000
        or      grs, rax

// Multiply the first two matrices, and re-store in the output buffer.
//
// [m00_new  m01_new] = [m00  m01] * [m00_prev  m01_prev]
// [m10_new  m11_new]   [m10  m11]   [m10_prev  m11_prev]
//
// The resulting matrix entries are:
//
//   m00_new = m00 * m00_prev + m01 * m10_prev
//   m01_new = m00 * m01_prev + m01 * m11_prev
//   m10_new = m10 * m00_prev + m11 * m10_prev
//   m11_new = m10 * m01_prev + m11 * m11_prev
//
// At this point the sign is right since both matrices were negated.

        mov     rax, [mat]
        imul    rax, m00
        mov     rdx, [mat+16]
        imul    rdx, m01
        imul    m00, [mat+8]
        imul    m01, [mat+24]
        add     m01, m00
        lea     m00, [rax+rdx]

        mov     rax, [mat]
        imul    rax, m10
        mov     rdx, [mat+16]
        imul    rdx, m11
        imul    m10, [mat+8]
        imul    m11, [mat+24]
        add     m11, m10
        lea     m10, [rax+rdx]

        mov     [mat], m00
        mov     [mat+8], m01
        mov     [mat+16], m10
        mov     [mat+24], m11

// Third block of divsteps, same style but a total of 19 not 20

        mov     minus2, -2
        mov     plus2e, 2
        mov     t, fuv
        mov     m, minus2
        test    d, d
        cmovs   m, zero
        test    grs, 1
.set i, 0
.rep 19
        cmovz  m, zero
        cmovz  t, zero
.if (i != 0)
        sar     grs, 1
.endif
        xor     t, m
        xor     d, m
        bt      m, 63
        cmovc   fuv, grs
        mov     m, minus2
        add     d, plus2
        lea     grs, [grs+t]
.if (i != 18)
        cmovs   m, zero
        mov     t, fuv
        test    grs, plus2
.endif
.set i, (i+1)
.endr
        sar     grs, 1

// Extract the matrix entries from the final 19 divsteps

        mov     eax,  1048576
        lea     m00, [fuv+rax]
        lea     m10, [grs+rax]
        shl     m00, 21
        shl     m10, 21
        sar     m00, 43
        sar     m10, 43

        mov     rax, 2199024304128
        lea     m01, [fuv+rax]
        lea     m11, [grs+rax]
        sar     m01, 43
        sar     m11, 43

// Multiply by this new matrix
//
// [m00_new  m01_new] = [m00  m01] * [m00_prev  m01_prev]
// [m10_new  m11_new]   [m10  m11]   [m10_prev  m11_prev]
//
// The resulting matrix entries are:
//
//   m00_new = m00 * m00_prev + m01 * m10_prev
//   m01_new = m00 * m01_prev + m01 * m11_prev
//   m10_new = m10 * m00_prev + m11 * m10_prev
//   m11_new = m10 * m01_prev + m11 * m11_prev
//
// Since we didn't negate the n matrix, all products are negated
// and so we insert negations

        mov     rax, [mat]
        imul    rax, m00
        mov     rdx, [mat+16]
        imul    rdx, m01
        imul    m00, [mat+8]
        imul    m01, [mat+24]
        add     m01, m00
        lea     m00, [rax+rdx]
        neg     m01
        neg     m00

        mov     rax, [mat]
        imul    rax, m10
        mov     rdx, [mat+16]
        imul    rdx, m11
        imul    m10, [mat+8]
        imul    m11, [mat+24]
        add     m11, m10
        lea     m10, [rax+rdx]
        neg     m11
        neg     m10

// Now write back the final matrix and d for the whole 59 steps

        mov     [mat], m00
        mov     [mat+8], m01
        mov     [mat+16], m10
        mov     [mat+24], m11
        mov     rax, d

// Restore registers and return

        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(word_divstep59)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
