// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Find bignum modulo a single word
// Input x[k], m; output function return
//
//    extern uint64_t bignum_cmod(uint64_t k, const uint64_t *x, uint64_t m);
//
// Returns x mod m, assuming m is nonzero.
//
// Standard x86-64 ABI: RDI = k, RSI = x, RDX = m, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, R8 = m, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cmod)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_cmod)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cmod)
        .text
        .balign 32

#define k rdi
#define x rsi

// This has to be rcx for variable shifts

#define e rcx

// We share the same variable for m and n, just shifting left then right.
// And h is kept in rdx which does work despite the special operands of mul.

#define m r8
#define n r8

#define w r9
#define a rax
#define r r10
#define h rdx
#define l r11

#define ashort eax
#define hshort edx

S2N_BN_SYMBOL(bignum_cmod):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Initialize l = 0 now for convenience (we eventually need to do it).
// If the bignum is zero-length, l is already the right answer of 0

        xor     l, l
        test    k, k
        jz      Lbignum_cmod_end

// Move m into its permanent home (also used for n).
// Find number of leading zeros of m and let n = 2^e m so that for an
// in-scope (nonzero) input m we have n >= 2^63, e <= 63.

        mov     m, rdx
        bsr     e, m
        xor     e, 63
        shl     m, cl

// A near-clone of word_recip so 2^64 + w = ceil(2^128 / n) - 1

        mov    r, n
        mov    w, 0x1FFFFFFFFFFFF
        shr    r, 16
        xor    w, r
        inc    r
        shr    w, 32
        mov    h, r
        imul   h, w
        neg    h
        mov    a, h
        shr    a, 49
        imul   a, a
        shr    h, 34
        add    h, a
        or     a, 0x40000000
        imul   a, h
        shr    a, 30
        imul   a, w
        shl    w, 30
        add    w, a
        shr    w, 30
        mov    h, r
        imul   h, w
        neg    h
        shr    h, 24
        imul   h, w
        shl    w, 16
        shr    h, 24
        add    w, h
        mov    h, r
        imul   h, w
        neg    h
        shr    h, 32
        imul   h, w
        shl    w, 31
        shr    h, 17
        add    w, h
        mov    a, n
        mul    w
        shrd   a, h, 60
        mov    h, w
        shr    h, 33
        not    a
        imul   a, h
        shl    w, 1
        shr    a, 33
        add    w, a
        add    w, 1
        mov    a, n
        sbb    w, 0
        mul    w
        add    h, n
        sbb    w, 0

// Take the residue r = 2^128 - (2^64 + w) * n, which by the above bound
// we know fits in 64 bits. We know 2^128 == r (mod n) and hence (mod m).

        mov     r, n
        imul    r, w
        neg     r

// Now just go down through the digits accumulating [h;l] == x (mod n)
// by 2^64 * [h;l] + d = 2^128 * h + [l;d] == r * h + [l; d]. That addition
// may overflow with a carry, say 2^128 + [h';l'] = r * h + [l; d], in
// which case we subtract 2^128 - r (which is divisible by m and keeping
// things in 128 bits we just add r). Thus the overall bound when we initially
// overflow is r * h + [l; d] - (2^128 - r) = r * (h + 1) + [l; d] - 2^128
// < 2^128 so we stay inside 2 words

        xor     hshort, hshort
Lbignum_cmod_loop:
        mov     a, h
        mul     r
        add     a, [x+8*k-8]
        adc     h, l
        mov     l, a
        sbb     a, a
        and     a, r
        add     l, a
        adc     h, 0
        dec     k
        jnz     Lbignum_cmod_loop

// Now do reciprocal multiplication to reduce the 2-word modular equivalent
// [h;l] to the single word l. If we assume the truncations are as follows
//   2^64 + w = 2^128 / n - epsilon (0 <= epsilon <= 1)
//   q = (w * h / 2^64) - delta (0 <= delta <= 1)
// the net remainder is l + (h/2^64 * epsilon + delta) * n < l + 2 * n.
// In general this needs two rounds of comparison to guarantee getting
// into a single word (though one more mul could be used instead).
// Also, the quotient estimate can overflow so we use r as extra addend
// 2^64 * n when the initial addition overflows. The overall multiple
// of n can't itself overflow, since we know it's an underestimate of
// the initial residue.

        mov     k, h    // back up h for muls
        mov     a, w
        mul     h
        add     h, k
        sbb     r, r
        and     r, n    // So q = [r;h]

        mov     a, h
        mul     n
        add     h, r
        xor     r, r
        sub     l, a
        sbb     k, h    // [k,l] = first reduction

        cmovnz  r, n
        xor     ashort, ashort
        sub     l, r
        sbb     k, a

        cmovnz  a, n
        sub     l, a

// One more reciprocal multiplication to do a modular reduction, but now in
// one word and in terms of the original m. For the quotient estimate we want
// q = ((2^64 + w) * l) / 2^{128-e} = ((2^64 + w) * l) / 2^65 / 2^{63-e}.

        mov     a, w
        mul     l
        add     h, l
        rcr     h, 1

        shr     m, cl
        xor     e, 63
        shr     h, cl

        imul    h, m
        sub     l, h

// Note that since there is no neglected "low" part of the single word,
// one round of correction suffices; in the analog of the above l = 0
// and hence the residue so far is already < 2 * m.

        mov     a, l
        sub     l, m
Lbignum_cmod_end:
        cmovnc  a, l
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_cmod)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
