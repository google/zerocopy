// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Invert modulo m, z = (1/a) mod b, assuming b is an odd number > 1, coprime a
// Inputs a[k], b[k]; output z[k]; temporary buffer t[>=3*k]
//
//    extern void bignum_modinv(uint64_t k, uint64_t *z, const uint64_t *a,
//                              const uint64_t *b, uint64_t *t);
//
// k-digit (digit=64 bits) "z := a^-1 mod b" (modular inverse of a modulo b)
// using t as a temporary buffer (t at least 3*k words = 24*k bytes), and
// assuming that a and b are coprime *and* that b is an odd number > 1.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = a, RCX = b, R8 = t
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = a, R9 = b, [RSP+40] = t
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_modinv)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_modinv)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_modinv)
        .text
        .balign 32

// We get CHUNKSIZE bits per outer iteration, 64 minus a few for proxy errors

#define CHUNKSIZE 58

// These variables are so fundamental we keep them consistently in registers.
// k actually stays where it was at the beginning, while l gets set up  later

#define k rdi
#define l r13

// These are kept on the stack since there aren't enough registers

#define mat_mm     QWORD PTR [rsp]
#define mat_mn     QWORD PTR [rsp+8]
#define mat_nm     QWORD PTR [rsp+16]
#define mat_nn     QWORD PTR [rsp+24]
#define t          QWORD PTR [rsp+32]
// Modular inverse
#define v          QWORD PTR [rsp+40]
// We reconstruct n as m + 8*k as needed
#define m          QWORD PTR [rsp+48]
#define w          QWORD PTR [rsp+56]
#define z          QWORD PTR [rsp+64]
// Original b pointer, not b the temp
#define bm         QWORD PTR [rsp+72]

#define STACKVARSIZE 80

// These get set to m/n or w/z during the cross-multiplications etc.
// Otherwise they can be used as additional temporaries

#define p1 r8
#define p2 r15

// These are shorthands for common temporary registers

#define a rax
#define b rbx
#define c rcx
#define d rdx
#define i r9

// Temporaries for the top proxy selection part

#define c1        r10
#define c2        r11
#define h1        r12
#define h2        rbp
#define l1        r14
#define l2        rsi

// Re-use for the actual proxies; m_hi = h1 and n_hi = h2 are assumed

#define m_hi    r12
#define n_hi    rbp
#define m_lo    r14
#define n_lo    rsi

// Re-use for the matrix entries in the inner loop, though they
// get spilled to the corresponding memory locations mat_...

#define m_m     r10
#define m_n     r11
#define n_m     rcx
#define n_n     rdx

#define ashort eax
#define ishort r9d
#define m_mshort r10d
#define m_nshort r11d
#define n_mshort ecx
#define n_nshort edx

S2N_BN_SYMBOL(bignum_modinv):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        mov     r8, [rsp+56]
#endif

// Save all required registers and make room on stack for all the above vars

        CFI_PUSH(rbp)
        CFI_PUSH(rbx)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(STACKVARSIZE)

// If k = 0 then do nothing (this is out of scope anyway)

        test    k, k
        jz      Lbignum_modinv_end

// Set up the additional two buffers m and n beyond w in temp space
// and record all pointers m, n, w and z in stack-based variables

        mov     z, rsi
        mov     w, r8
        mov     bm, rcx
        lea     r10, [r8+8*k]
        mov     m, r10
        lea     p2, [r10+8*k]

// Initialize the main buffers with their starting values:
// m = a, n = b, w = b (to be tweaked to b - 1) and z = 0

        xor     r11, r11
        xor     i, i
Lbignum_modinv_copyloop:
        mov     a, [rdx+8*i]
        mov     b, [rcx+8*i]
        mov     [r10+8*i], a
        mov     [p2+8*i], b
        mov     [r8+8*i], b
        mov     [rsi+8*i], r11
        inc     i
        cmp     i, k
        jc      Lbignum_modinv_copyloop

// Tweak down w to b - 1 (this crude approach is safe as b needs to be odd
// for it to be in scope). We have then established the congruence invariant:
//
//   a * w == -m (mod b)
//   a * z == n (mod b)
//
// This, with the bounds w <= b and z <= b, is maintained round the outer loop

        mov     a, [r8]
        mov     b, a
        dec     b
        mov     [r8], b

// Compute v = negated modular inverse of b mod 2^64, reusing a from above
// This is used for Montgomery reduction operations each time round the loop

        mov     h2, a
        mov     h1, a
        shl     h2, 2
        sub     h1, h2
        xor     h1, 2

        mov     h2, h1
        imul    h2, a
        mov     ashort, 2
        add     a, h2
        add     h2, 1

        imul    h1, a

        imul    h2, h2
        mov     ashort, 1
        add     a, h2
        imul    h1, a

        imul    h2, h2
        mov     ashort, 1
        add     a, h2
        imul    h1, a

        imul    h2, h2
        mov     ashort, 1
        add     a, h2
        imul    h1, a

        mov     v, h1

// Set up the outer loop count of 128 * k
// The invariant is that m * n < 2^t at all times.

        mov     a, k
        shl     a, 7
        mov     t, a

// Start of the main outer loop iterated t / CHUNKSIZE times

Lbignum_modinv_outerloop:

// We need only bother with sharper l = min k (ceil(t/64)) digits
// for the computations on m and n (but we still need k for w and z).
// Either both m and n fit in l digits, or m has become zero and so
// nothing happens in the loop anyway and this makes no difference.

        mov     l, t
        add     l, 63
        shr     l, 6
        cmp     l, k
        cmovnc  l, k

// Select upper and lower proxies for both m and n to drive the inner
// loop. The lower proxies are simply the lowest digits themselves,
// m_lo = m[0] and n_lo = n[0], while the upper proxies are bitfields
// of the two inputs selected so their top bit (63) aligns with the
// most significant bit of *either* of the two inputs.

        xor     h1, h1  // Previous high and low for m
        xor     l1, l1
        xor     h2, h2  // Previous high and low for n
        xor     l2, l2
        xor     c2, c2  // Mask flag: previous word of one was nonzero
        // and in this case h1 and h2 are those words

        mov     p1, m
        lea     p2, [p1+8*k]
        xor     i, i
Lbignum_modinv_toploop:
        mov     b, [p1+8*i]
        mov     c, [p2+8*i]
        mov     c1, c2
        and     c1, h1
        and     c2, h2
        mov     a, b
        or      a, c
        neg     a
        cmovc   l1, c1
        cmovc   l2, c2
        cmovc   h1, b
        cmovc   h2, c
        sbb     c2, c2
        inc     i
        cmp     i, l
        jc      Lbignum_modinv_toploop

        mov     a, h1
        or      a, h2
        bsr     c, a
        xor     c, 63
        shld    h1, l1, cl
        shld    h2, l2, cl

// m_lo = m[0], n_lo = n[0];

        mov     rax, [p1]
        mov     m_lo, rax

        mov     rax, [p2]
        mov     n_lo, rax

// Now the inner loop, with i as loop counter from CHUNKSIZE down.
// This records a matrix of updates to apply to the initial
// values of m and n with, at stage j:
//
//     sgn * m' = (m_m * m - m_n * n) / 2^j
//    -sgn * n' = (n_m * m - n_n * n) / 2^j
//
// where "sgn" is either +1 or -1, and we lose track of which except
// that both instance above are the same. This throwing away the sign
// costs nothing (since we have to correct in general anyway because
// of the proxied comparison) and makes things a bit simpler. But it
// is simply the parity of the number of times the first condition,
// used as the swapping criterion, fires in this loop.

        mov     m_mshort, 1
        mov     m_nshort, 0
        mov     n_mshort, 0
        mov     n_nshort, 1
        mov     ishort, CHUNKSIZE

// Stash more variables over the inner loop to free up regs

        mov     mat_mn, k
        mov     mat_nm, l
        mov     mat_mm, p1
        mov     mat_nn, p2

// Conceptually in the inner loop we follow these steps:
//
// * If m_lo is odd and m_hi < n_hi, then swap the four pairs
//    (m_hi,n_hi); (m_lo,n_lo); (m_m,n_m); (m_n,n_n)
//
// * Now, if m_lo is odd (old or new, doesn't matter as initial n_lo is odd)
//    m_hi := m_hi - n_hi, m_lo := m_lo - n_lo
//    m_m  := m_m + n_m, m_n := m_n + n_n
//
// * Halve and double them
//     m_hi := m_hi / 2, m_lo := m_lo / 2
//     n_m := n_m * 2, n_n := n_n * 2
//
// The actual computation computes updates before actually swapping and
// then corrects as needed.

Lbignum_modinv_innerloop:

        xor     eax, eax
        xor     ebx, ebx
        xor     p1, p1
        xor     p2, p2
        bt      m_lo, 0

        cmovc   rax, n_hi
        cmovc   rbx, n_lo
        cmovc   p1, n_m
        cmovc   p2, n_n

        mov     l, m_lo
        sub     m_lo, rbx
        sub     rbx, l
        mov     k, m_hi
        sub     k, rax
        cmovc   n_hi, m_hi
        lea     m_hi, [k-1]
        cmovc   m_lo, rbx
        cmovc   n_lo, l
        not     m_hi
        cmovc   n_m, m_m
        cmovc   n_n, m_n
        cmovnc  m_hi, k

        shr     m_lo, 1
        add     m_m, p1
        add     m_n, p2
        shr     m_hi, 1
        add     n_m, n_m
        add     n_n, n_n

// End of the inner for-loop

        dec     i
        jnz     Lbignum_modinv_innerloop

// Unstash the temporary variables

        mov     k,mat_mn
        mov     l,mat_nm
        mov     p1,mat_mm
        mov     p2,mat_nn

// Put the matrix entries in memory since we're out of registers
// We pull them out repeatedly in the next loop

        mov     mat_mm, m_m
        mov     mat_mn, m_n
        mov     mat_nm, n_m
        mov     mat_nn, n_n

// Apply the update to w and z, using addition in this case, and also take
// the chance to shift an additional 6 = 64-CHUNKSIZE bits to be ready for a
// Montgomery multiplication. Because we know that m_m + m_n <= 2^58 and
// w, z <= b < 2^{64k}, we know that both of these fit in k+1 words.
// We do this before the m-n update to allow us to play with c1 and c2 here.
//
//    l1::w = 2^6 * (m_m * w + m_n * z)
//    l2::z = 2^6 * (n_m * w + n_n * z)
//
// with c1 and c2 recording previous words for the shifting part

        mov     p1, w
        mov     p2, z
        xor     l1, l1
        xor     l2, l2
        xor     c1, c1
        xor     c2, c2
        xor     i, i
Lbignum_modinv_congloop:

        mov     c, [p1+8*i]
        mov     a, mat_mm
        mul     c
        add     l1, a
        adc     d, 0
        mov     h1, d            // Now h1::l1 := m_m * w + l1_in

        mov     a, mat_nm
        mul     c
        add     l2, a
        adc     d, 0
        mov     h2, d            // Now h2::l2 := n_m * w + l2_in

        mov     c, [p2+8*i]
        mov     a, mat_mn
        mul     c
        add     l1, a
        adc     h1, d           // h1::l1 := m_m * w + m_n * z + l1_in
        shrd    c1, l1, CHUNKSIZE
        mov     [p1+8*i], c1
        mov     c1, l1
        mov     l1, h1

        mov     a, mat_nn
        mul     c
        add     l2, a
        adc     h2, d           // h2::l2 := n_m * w + n_n * z + l2_in
        shrd    c2, l2, CHUNKSIZE
        mov     [p2+8*i], c2
        mov     c2, l2
        mov     l2, h2

        inc     i
        cmp     i, k
        jc      Lbignum_modinv_congloop

        shld    l1, c1, 64-CHUNKSIZE
        shld    l2, c2, 64-CHUNKSIZE

// Do a Montgomery reduction of l1::w

        mov     p2, bm

        mov     b, [p1]
        mov     h1, v
        imul    h1, b
        mov     a, [p2]
        mul     h1
        add     a, b            // Will be zero but want the carry
        mov     c1, rdx
        mov     ishort, 1
        mov     c, k
        dec     c
        jz      Lbignum_modinv_wmontend

Lbignum_modinv_wmontloop:
        adc     c1, [p1+8*i]
        sbb     b, b
        mov     a, [p2+8*i]
        mul     h1
        sub     rdx, b
        add     a, c1
        mov     [p1+8*i-8], a
        mov     c1, rdx
        inc     i
        dec     c
        jnz     Lbignum_modinv_wmontloop

Lbignum_modinv_wmontend:
        adc     c1, l1
        mov     [p1+8*k-8], c1
        sbb     c1, c1
        neg     c1

        mov     c, k
        xor     i, i
Lbignum_modinv_wcmploop:
        mov     a, [p1+8*i]
        sbb     a, [p2+8*i]
        inc     i
        dec     c
        jnz     Lbignum_modinv_wcmploop
        sbb     c1, 0
        sbb     c1, c1
        not     c1

        xor     c, c
        xor     i, i
Lbignum_modinv_wcorrloop:
        mov     a, [p1+8*i]
        mov     b, [p2+8*i]
        and     b, c1
        neg     c
        sbb     a, b
        sbb     c, c
        mov     [p1+8*i], a
        inc     i
        cmp     i, k
        jc      Lbignum_modinv_wcorrloop

// Do a Montgomery reduction of l2::z

        mov     p1, z

        mov     b, [p1]
        mov     h2, v
        imul    h2, b
        mov     a, [p2]
        mul     h2
        add     a, b            // Will be zero but want the carry
        mov     c2, rdx
        mov     ishort, 1
        mov     c, k
        dec     c
        jz      Lbignum_modinv_zmontend

Lbignum_modinv_zmontloop:
        adc     c2, [p1+8*i]
        sbb     b, b
        mov     a, [p2+8*i]
        mul     h2
        sub     rdx, b
        add     a, c2
        mov     [p1+8*i-8], a
        mov     c2, rdx
        inc     i
        dec     c
        jnz     Lbignum_modinv_zmontloop

Lbignum_modinv_zmontend:
        adc     c2, l2
        mov     [p1+8*k-8], c2
        sbb     c2, c2
        neg     c2

        mov     c, k
        xor     i, i
Lbignum_modinv_zcmploop:
        mov     a, [p1+8*i]
        sbb     a, [p2+8*i]
        inc     i
        dec     c
        jnz     Lbignum_modinv_zcmploop
        sbb     c2, 0
        sbb     c2, c2
        not     c2

        xor     c, c
        xor     i, i
Lbignum_modinv_zcorrloop:
        mov     a, [p1+8*i]
        mov     b, [p2+8*i]
        and     b, c2
        neg     c
        sbb     a, b
        sbb     c, c
        mov     [p1+8*i], a
        inc     i
        cmp     i, k
        jc      Lbignum_modinv_zcorrloop

// Now actually compute the updates to m and n corresponding to the matrix,
// and correct the signs if they have gone negative. First we compute the
// (k+1)-sized updates with the following invariant (here h1 and h2 are in
// fact carry bitmasks, either 0 or -1):
//
//    h1::l1::m = m_m * m - m_n * n
//    h2::l2::n = n_m * m - n_n * n

        mov     p1, m
        lea     p2, [p1+8*k]
        xor     i, i
        xor     h1, h1
        xor     l1, l1
        xor     h2, h2
        xor     l2, l2
Lbignum_modinv_crossloop:

        mov     c, [p1+8*i]
        mov     a, mat_mm
        mul     c
        add     l1, a
        adc     d, 0
        mov     c1, d            // Now c1::l1 is +ve part 1

        mov     a, mat_nm
        mul     c
        add     l2, a
        adc     d, 0
        mov     c2, d            // Now c2::l2 is +ve part 2

        mov     c, [p2+8*i]
        mov     a, mat_mn
        mul     c
        sub     d, h1           // Now d::a is -ve part 1

        sub     l1, a
        sbb     c1, d
        sbb     h1, h1
        mov     [p1+8*i], l1
        mov     l1, c1

        mov     a, mat_nn
        mul     c
        sub     d, h2           // Now d::a is -ve part 2

        sub     l2, a
        sbb     c2, d
        sbb     h2, h2
        mov     [p2+8*i], l2
        mov     l2, c2

        inc     i
        cmp     i, l
        jc      Lbignum_modinv_crossloop

// Now fix the signs of m and n if they have gone negative

        xor     i, i
        mov     c1, h1  // carry-in coded up as well
        mov     c2, h2  // carry-in coded up as well
        xor     l1, h1  // for the Lbignum_modinv_end digit
        xor     l2, h2  // for the Lbignum_modinv_end digit
Lbignum_modinv_optnegloop:
        mov     a, [p1+8*i]
        xor     a, h1
        neg     c1
        adc     a, 0
        sbb     c1, c1
        mov     [p1+8*i], a
        mov     a, [p2+8*i]
        xor     a, h2
        neg     c2
        adc     a, 0
        sbb     c2, c2
        mov     [p2+8*i], a
        inc     i
        cmp     i, l
        jc      Lbignum_modinv_optnegloop
        sub     l1, c1
        sub     l2, c2

// Now shift them right CHUNKSIZE bits

        mov     i, l
Lbignum_modinv_shiftloop:
        mov     a, [p1+8*i-8]
        mov     c1, a
        shrd    a, l1, CHUNKSIZE
        mov     [p1+8*i-8],a
        mov     l1, c1
        mov     a, [p2+8*i-8]
        mov     c2, a
        shrd    a, l2, CHUNKSIZE
        mov     [p2+8*i-8],a
        mov     l2, c2
        dec     i
        jnz     Lbignum_modinv_shiftloop

// Finally, use the signs h1 and h2 to do optional modular negations of
// w and z respectively, flipping h2 to make signs work. We don't make
// any checks for zero values, but we certainly retain w <= b and z <= b.
// This is enough for the Montgomery step in the next iteration to give
// strict reduction w < b amd z < b, and anyway when we terminate we
// could not have z = b since it violates the coprimality assumption for
// in-scope cases.

        not     h2
        mov     c, bm
        mov     p1, w
        mov     p2, z
        mov     c1, h1
        mov     c2, h2
        xor     i, i
Lbignum_modinv_fliploop:
        mov     d, h2
        mov     a, [c+8*i]
        and     d, a
        and     a, h1
        mov     b, [p1+8*i]
        xor     b, h1
        neg     c1
        adc     a, b
        sbb     c1, c1
        mov     [p1+8*i], a
        mov     b, [p2+8*i]
        xor     b, h2
        neg     c2
        adc     d, b
        sbb     c2, c2
        mov     [p2+8*i], d
        inc     i
        cmp     i, k
        jc      Lbignum_modinv_fliploop

// End of main loop. We can stop if t' <= 0 since then m * n < 2^0, which
// since n is odd and m and n are coprime (in the in-scope cases) means
// m = 0, n = 1 and hence from the congruence invariant a * z == 1 (mod b).
// Moreover we do in fact need to maintain strictly t > 0 in the main loop,
// or the computation of the optimized digit bound l could collapse to 0.

        sub     t, CHUNKSIZE
        jnbe    Lbignum_modinv_outerloop

Lbignum_modinv_end:
        CFI_INC_RSP(STACKVARSIZE)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbx)
        CFI_POP(rbp)

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_modinv)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
