// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Test bignums for coprimality, gcd(x,y) = 1
// Inputs x[m], y[n]; output function return; temporary buffer t[>=2*max(m,n)]
//
//    extern uint64_t bignum_coprime(uint64_t m, const uint64_t *x, uint64_t n,
//                                   const uint64_t *y, uint64_t *t);
//
// Test for whether two bignums are coprime (no common factor besides 1).
// This is equivalent to testing if their gcd is 1, but a bit faster than
// doing those two computations separately.
//
// Here bignum x is m digits long, y is n digits long and the temporary
// buffer t needs to be 2 * max(m,n) digits long. The return value is
// 1 if coprime(x,y) and 0 otherwise.
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, R8 = t, returns RAX
// Microsoft x64 ABI:   RCX = m, RDX = x, R8 = n, R9 = y, [RSP+40] = t, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_coprime)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_coprime)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_coprime)
        .text
        .balign 32

// We get CHUNKSIZE bits per outer iteration, 64 minus a bit for proxy errors

#define CHUNKSIZE 58

// These variables are so fundamental we keep them consistently in registers.
// m is in fact the temporary buffer argument w so use the same register

#define m r8
#define n r15
#define k r14
#define l r13

// These are kept on the stack since there aren't enough registers

#define mat_mm     QWORD PTR [rsp]
#define mat_mn     QWORD PTR [rsp+8]
#define mat_nm     QWORD PTR [rsp+16]
#define mat_nn     QWORD PTR [rsp+24]
#define t          QWORD PTR [rsp+32]
#define evenor     QWORD PTR [rsp+40]

#define STACKVARSIZE 48

// These are shorthands for common temporary register

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
#define l1        rdi
#define l2        rsi

// Re-use for the actual proxies; m_hi = h1 and n_hi = h2 are assumed

#define m_hi    r12
#define n_hi    rbp
#define m_lo    rdi
#define n_lo    rsi

// Re-use for the matrix entries in the inner loop, though they
// get spilled to the corresponding memory locations mat_...

#define m_m     r10
#define m_n     r11
#define n_m     rcx
#define n_n     rdx

#define ishort   r9d
#define m_mshort r10d
#define m_nshort r11d
#define n_mshort ecx
#define n_nshort edx

// Because they are so unmemorable

#define arg1 rdi
#define arg2 rsi
#define arg3 rdx
#define arg4 rcx

S2N_BN_SYMBOL(bignum_coprime):
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

// Compute k = max(m,n), and if this is zero skip to the end. Note that
// in this case k is also in rax so serves as the right answer of "false"

        mov     rax, arg1
        cmp     rax, arg3
        cmovc   rax, arg3
        mov     k, rax

        test    rax, rax
        jz      Lbignum_coprime_end

// Set up inside w two size-k buffers m and n

        lea     n, [m+8*k]

// Copy the input x into the buffer m, padding with zeros as needed

        xor     i, i
        test    arg1, arg1
        jz      Lbignum_coprime_xpadloop
Lbignum_coprime_xloop:
        mov     a, [arg2+8*i]
        mov     [m+8*i], a
        inc     i
        cmp     i, arg1
        jc      Lbignum_coprime_xloop
        cmp     i, k
        jnc     Lbignum_coprime_xskip
Lbignum_coprime_xpadloop:
        mov     QWORD PTR [m+8*i], 0
        inc     i
        cmp     i, k
        jc      Lbignum_coprime_xpadloop
Lbignum_coprime_xskip:

// Copy the input y into the buffer n, padding with zeros as needed

        xor     i, i
        test    arg3, arg3
        jz      Lbignum_coprime_ypadloop
Lbignum_coprime_yloop:
        mov     a, [arg4+8*i]
        mov     [n+8*i], a
        inc     i
        cmp     i, arg3
        jc      Lbignum_coprime_yloop
        cmp     i, k
        jnc     Lbignum_coprime_yskip
Lbignum_coprime_ypadloop:
        mov     QWORD PTR [n+8*i], 0
        inc     i
        cmp     i, k
        jc      Lbignum_coprime_ypadloop
Lbignum_coprime_yskip:

// Set up the outer loop count of 64 * sum of input sizes.
// The invariant is that m * n < 2^t at all times.

        lea     a, [arg1+arg3]
        shl     a, 6
        mov     t, a

// Record for the very end the OR of the lowest words.
// If the bottom bit is zero we know both are even so the answer is false.
// But since this is constant-time code we still execute all the main part.

        mov     a, [m]
        mov     b, [n]
        or      a, b
        mov     evenor, a

// Now if n is even trigger a swap of m and n. This ensures that if
// one or other of m and n is odd then we make sure now that n is,
// as expected by our invariant later on.

        and     b, 1
        sub     b, 1

        xor     i, i
Lbignum_coprime_swaploop:
        mov     a, [m+8*i]
        mov     c, [n+8*i]
        mov     d, a
        xor     d, c
        and     d, b
        xor     a, d
        xor     c, d
        mov     [m+8*i], a
        mov     [n+8*i], c
        inc     i
        cmp     i, k
        jnz     Lbignum_coprime_swaploop

// Start of the main outer loop iterated t / CHUNKSIZE times

Lbignum_coprime_outerloop:

// We need only bother with sharper l = min k (ceil(t/64)) digits
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

        xor     i, i
Lbignum_coprime_toploop:
        mov     b, [m+8*i]
        mov     c, [n+8*i]
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
        jc      Lbignum_coprime_toploop

        mov     a, h1
        or      a, h2
        bsr     c, a
        xor     c, 63
        shld    h1, l1, cl
        shld    h2, l2, cl

// m_lo = m[0], n_lo = n[0];

        mov     rax, [m]
        mov     m_lo, rax

        mov     rax, [n]
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
        mov     mat_mm, m
        mov     mat_nn, n

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

Lbignum_coprime_innerloop:

        xor     eax, eax
        xor     ebx, ebx
        xor     m, m
        xor     n, n
        bt      m_lo, 0

        cmovc   rax, n_hi
        cmovc   rbx, n_lo
        cmovc   m, n_m
        cmovc   n, n_n

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
        add     m_m, m
        add     m_n, n
        shr     m_hi, 1
        add     n_m, n_m
        add     n_n, n_n

// End of the inner for-loop

        dec     i
        jnz     Lbignum_coprime_innerloop

// Unstash the temporary variables

        mov     k,mat_mn
        mov     l,mat_nm
        mov     m,mat_mm
        mov     n,mat_nn

// Put the matrix entries in memory since we're out of registers
// We pull them out repeatedly in the next loop

        mov     mat_mm, m_m
        mov     mat_mn, m_n
        mov     mat_nm, n_m
        mov     mat_nn, n_n

// Now actually compute the updates to m and n corresponding to that matrix,
// and correct the signs if they have gone negative. First we compute the
// (k+1)-sized updates with the following invariant (here h1 and h2 are in
// fact carry bitmasks, either 0 or -1):
//
//    h1::l1::m = m_m * m - m_n * n
//    h2::l2::n = n_m * m - n_n * n

        xor     i, i
        xor     h1, h1
        xor     l1, l1
        xor     h2, h2
        xor     l2, l2
Lbignum_coprime_crossloop:

        mov     c, [m+8*i]
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

        mov     c, [n+8*i]
        mov     a, mat_mn
        mul     c
        sub     d, h1           // Now d::a is -ve part 1

        sub     l1, a
        sbb     c1, d
        sbb     h1, h1
        mov     [m+8*i], l1
        mov     l1, c1

        mov     a, mat_nn
        mul     c
        sub     d, h2           // Now d::a is -ve part 2

        sub     l2, a
        sbb     c2, d
        sbb     h2, h2
        mov     [n+8*i], l2
        mov     l2, c2

        inc     i
        cmp     i, l
        jc      Lbignum_coprime_crossloop

// Now fix the signs of m and n if they have gone negative

        xor     i, i
        mov     c1, h1  // carry-in coded up as well
        mov     c2, h2  // carry-in coded up as well
        xor     l1, h1  // for the Lbignum_coprime_end digit
        xor     l2, h2  // for the Lbignum_coprime_end digit
Lbignum_coprime_optnegloop:
        mov     a, [m+8*i]
        xor     a, h1
        neg     c1
        adc     a, 0
        sbb     c1, c1
        mov     [m+8*i], a
        mov     a, [n+8*i]
        xor     a, h2
        neg     c2
        adc     a, 0
        sbb     c2, c2
        mov     [n+8*i], a
        inc     i
        cmp     i, l
        jc      Lbignum_coprime_optnegloop
        sub     l1, c1
        sub     l2, c2

// Now shift them right CHUNKSIZE bits

        mov     i, l
Lbignum_coprime_shiftloop:
        mov     a, [m+8*i-8]
        mov     h1, a
        shrd    a, l1, CHUNKSIZE
        mov     [m+8*i-8],a
        mov     l1, h1
        mov     a, [n+8*i-8]
        mov     h2, a
        shrd    a, l2, CHUNKSIZE
        mov     [n+8*i-8],a
        mov     l2, h2
        dec     i
        jnz     Lbignum_coprime_shiftloop

// End of main loop. We can stop if t' <= 0 since then m * n < 2^0, which
// since n is odd (in the main cases where we had one or other input odd)
// means that m = 0 and n is the final gcd. Moreover we do in fact need to
// maintain strictly t > 0 in the main loop, or the computation of the
// optimized digit bound l could collapse to 0.

        sub     t, CHUNKSIZE
        jnbe    Lbignum_coprime_outerloop

// Now compare n with 1 (OR of the XORs in a)

        mov     a, [n]
        xor     a, 1
        cmp     k, 1
        jz      Lbignum_coprime_finalcomb
        mov     ishort, 1
Lbignum_coprime_compareloop:
        or      a, [n+8*i]
        inc     i
        cmp     i, k
        jc      Lbignum_coprime_compareloop

// Now combine that with original "evenor" oddness flag
// The final condition is lsb(evenor) = 1 AND a = 0

Lbignum_coprime_finalcomb:
        neg     a
        sbb     a, a
        inc     a
        and     a, evenor

// The end

Lbignum_coprime_end:
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

S2N_BN_SIZE_DIRECTIVE(bignum_coprime)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
