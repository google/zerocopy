// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[16], y[16]; output z[32]; temporary buffer t[>=32]
//
//    extern void bignum_kmul_16_32(uint64_t z[static 32],
//                                  const uint64_t x[static 16],
//                                  const uint64_t y[static 16],
//                                  uint64_t t[static 32]);
//
// In this x86 code the final temporary space argument t is unused, but
// it is retained in the prototype above for API consistency with ARM.
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y, RCX = t
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y, R9 = t
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_kmul_16_32)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_kmul_16_32)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_kmul_16_32)
        .text

// These parameters are kept where they come in

#define z rdi
#define x rsi

// This one gets moved to free up rdx for muls

#define y rcx

// Often used for zero

#define zero rbp
#define zeroe ebp

// mulpadd i, j adds x[i] * rdx (now assumed = y[j]) into the window at i+j

.macro mulpadd arg1,arg2
        mulx    rbx, rax, [x+8*\arg1]
.if ((\arg1 + \arg2) % 8 == 0)
        adcx    r8, rax
        adox    r9, rbx
.elseif ((\arg1 + \arg2) % 8 == 1)
        adcx    r9, rax
        adox    r10, rbx
.elseif ((\arg1 + \arg2) % 8 == 2)
        adcx    r10, rax
        adox    r11, rbx
.elseif ((\arg1 + \arg2) % 8 == 3)
        adcx    r11, rax
        adox    r12, rbx
.elseif ((\arg1 + \arg2) % 8 == 4)
        adcx    r12, rax
        adox    r13, rbx
.elseif ((\arg1 + \arg2) % 8 == 5)
        adcx    r13, rax
        adox    r14, rbx
.elseif ((\arg1 + \arg2) % 8 == 6)
        adcx    r14, rax
        adox    r15, rbx
.elseif ((\arg1 + \arg2) % 8 == 7)
        adcx    r15, rax
        adox    r8, rbx
.endif

.endm

// mulpade i, j adds x[i] * rdx (now assumed = y[j]) into the window at i+j
// but re-creates the top word assuming nothing to add there

.macro mulpade arg1,arg2
.if ((\arg1 + \arg2) % 8 == 0)
        mulx    r9, rax, [x+8*\arg1]
        adcx    r8, rax
        adox    r9, zero
.elseif ((\arg1 + \arg2) % 8 == 1)
        mulx    r10, rax, [x+8*\arg1]
        adcx    r9, rax
        adox    r10, zero
.elseif ((\arg1 + \arg2) % 8 == 2)
        mulx    r11, rax, [x+8*\arg1]
        adcx    r10, rax
        adox    r11, zero
.elseif ((\arg1 + \arg2) % 8 == 3)
        mulx    r12, rax, [x+8*\arg1]
        adcx    r11, rax
        adox    r12, zero
.elseif ((\arg1 + \arg2) % 8 == 4)
        mulx    r13, rax, [x+8*\arg1]
        adcx    r12, rax
        adox    r13, zero
.elseif ((\arg1 + \arg2) % 8 == 5)
        mulx    r14, rax, [x+8*\arg1]
        adcx    r13, rax
        adox    r14, zero
.elseif ((\arg1 + \arg2) % 8 == 6)
        mulx    r15, rax, [x+8*\arg1]
        adcx    r14, rax
        adox    r15, zero
.elseif ((\arg1 + \arg2) % 8 == 7)
        mulx    r8, rax, [x+8*\arg1]
        adcx    r15, rax
        adox    r8, zero
.endif

.endm

// addrow i adds z[i] + x[0..7] * y[i] into the window

.macro addrow arg1
        mov     rdx, [y+8*\arg1]
        xor     zeroe, zeroe

.if (\arg1 % 8 == 0)
        adox    r8, [z+8*\arg1]
.elseif (\arg1 % 8 == 1)
        adox    r9, [z+8*\arg1]
.elseif (\arg1 % 8 == 2)
        adox    r10, [z+8*\arg1]
.elseif (\arg1 % 8 == 3)
        adox    r11, [z+8*\arg1]
.elseif (\arg1 % 8 == 4)
        adox    r12, [z+8*\arg1]
.elseif (\arg1 % 8 == 5)
        adox    r13, [z+8*\arg1]
.elseif (\arg1 % 8 == 6)
        adox    r14, [z+8*\arg1]
.elseif (\arg1 % 8 == 7)
        adox    r15, [z+8*\arg1]
.endif

        mulpadd 0, \arg1

.if (\arg1 % 8 == 0)
        mov     [z+8*\arg1], r8
.elseif (\arg1 % 8 == 1)
        mov     [z+8*\arg1], r9
.elseif (\arg1 % 8 == 2)
        mov     [z+8*\arg1], r10
.elseif (\arg1 % 8 == 3)
        mov     [z+8*\arg1], r11
.elseif (\arg1 % 8 == 4)
        mov     [z+8*\arg1], r12
.elseif (\arg1 % 8 == 5)
        mov     [z+8*\arg1], r13
.elseif (\arg1 % 8 == 6)
        mov     [z+8*\arg1], r14
.elseif (\arg1 % 8 == 7)
        mov     [z+8*\arg1], r15
.endif

        mulpadd 1, \arg1
        mulpadd 2, \arg1
        mulpadd 3, \arg1
        mulpadd 4, \arg1
        mulpadd 5, \arg1
        mulpadd 6, \arg1
        mulpade 7, \arg1

.if (\arg1 % 8 == 0)
        adc     r8, zero
.elseif (\arg1 % 8 == 1)
        adc     r9, zero
.elseif (\arg1 % 8 == 2)
        adc     r10, zero
.elseif (\arg1 % 8 == 3)
        adc     r11, zero
.elseif (\arg1 % 8 == 4)
        adc     r12, zero
.elseif (\arg1 % 8 == 5)
        adc     r13, zero
.elseif (\arg1 % 8 == 6)
        adc     r14, zero
.elseif (\arg1 % 8 == 7)
        adc     r15, zero
.endif

.endm

// Special zero version of addrow, setting up the window from scratch

.macro addrowz
        mov     rdx, [y]
        xor     zeroe, zeroe

        mulx    r9, rax, [x]
        adc     [z], rax

        mulx    r10, rax, [x+8]
        adc     r9, rax

        mulx    r11, rax, [x+16]
        adc     r10, rax

        mulx    r12, rax, [x+24]
        adc     r11, rax

        mulx    r13, rax, [x+32]
        adc     r12, rax

        mulx    r14, rax, [x+40]
        adc     r13, rax

        mulx    r15, rax, [x+48]
        adc     r14, rax

        mulx    r8, rax, [x+56]
        adc     r15, rax

        adc     r8, zero
.endm

// This is a variant where we add the initial z[0..7] at the outset.
// This makes the initialization process a bit less wasteful. By doing
// a block of 8 we get the same effect except that we add z[0..7]
//
// adurow i adds 2^{7*64} * z[i+7] + x[0..7] * y[i] into the window

.macro adurow arg1
        mov     rdx, [y+8*\arg1]
        xor     zeroe, zeroe

        mulpadd 0, \arg1

.if (\arg1 % 8 == 0)
        mov     [z+8*\arg1],r8
.elseif (\arg1 % 8 == 1)
        mov     [z+8*\arg1],r9
.elseif (\arg1 % 8 == 2)
        mov     [z+8*\arg1],r10
.elseif (\arg1 % 8 == 3)
        mov     [z+8*\arg1],r11
.elseif (\arg1 % 8 == 4)
        mov     [z+8*\arg1],r12
.elseif (\arg1 % 8 == 5)
        mov     [z+8*\arg1],r13
.elseif (\arg1 % 8 == 6)
        mov     [z+8*\arg1],r14
.elseif (\arg1 % 8 == 7)
        mov     [z+8*\arg1],r15
.endif

        mulpadd 1, \arg1
        mulpadd 2, \arg1
        mulpadd 3, \arg1
        mulpadd 4, \arg1
        mulpadd 5, \arg1
        mulpadd 6, \arg1
        mulpade 7, \arg1

.if (\arg1 % 8 == 0)
        adc     r8, zero
.elseif (\arg1 % 8 == 1)
        adc     r9, zero
.elseif (\arg1 % 8 == 2)
        adc     r10, zero
.elseif (\arg1 % 8 == 3)
        adc     r11, zero
.elseif (\arg1 % 8 == 4)
        adc     r12, zero
.elseif (\arg1 % 8 == 5)
        adc     r13, zero
.elseif (\arg1 % 8 == 6)
        adc     r14, zero
.elseif (\arg1 % 8 == 7)
        adc     r15, zero
.endif

.endm

// Special "adurow 0" case to do first stage

.macro adurowz
        mov     rdx, [y]
        xor     zeroe, zeroe

        mov     r8, [z]
        mov     r9, [z+8]

        mulpadd 0, 0
        mov     [z],r8

        mov     r10, [z+16]
        mulpadd 1, 0
        mov     r11, [z+24]
        mulpadd 2, 0
        mov     r12, [z+32]
        mulpadd 3, 0
        mov     r13, [z+40]
        mulpadd 4, 0
        mov     r14, [z+48]
        mulpadd 5, 0
        mov     r15, [z+56]
        mulpadd 6, 0

        mulx    r8, rax, [x+56]
        adcx    r15, rax
        adox    r8, zero
        adcx    r8, zero
.endm

// Multiply-add: z := z + x[0..7] * y

.macro addrows
        adurowz
        adurow  1
        adurow  2
        adurow  3
        adurow  4
        adurow  5
        adurow  6
        adurow  7
        addrow  8
        addrow  9
        addrow  10
        addrow  11
        addrow  12
        addrow  13
        addrow  14
        addrow  15

        mov     [z+128], r8
        mov     [z+136], r9
        mov     [z+144], r10
        mov     [z+152], r11
        mov     [z+160], r12
        mov     [z+168], r13
        mov     [z+176], r14
        mov     [z+184], r15

.endm

// mulrow i adds x[0..7] * y[i] into the window
// just like addrow but no addition of z[i]

.macro mulrow arg1
        mov     rdx, [y+8*\arg1]
        xor     zeroe, zeroe

        mulpadd 0, \arg1

.if (\arg1 % 8 == 0)
        mov     [z+8*\arg1], r8
.elseif (\arg1 % 8 == 1)
        mov     [z+8*\arg1], r9
.elseif (\arg1 % 8 == 2)
        mov     [z+8*\arg1], r10
.elseif (\arg1 % 8 == 3)
        mov     [z+8*\arg1], r11
.elseif (\arg1 % 8 == 4)
        mov     [z+8*\arg1], r12
.elseif (\arg1 % 8 == 5)
        mov     [z+8*\arg1], r13
.elseif (\arg1 % 8 == 6)
        mov     [z+8*\arg1], r14
.elseif (\arg1 % 8 == 7)
        mov     [z+8*\arg1], r15
.endif

        mulpadd 1, \arg1
        mulpadd 2, \arg1
        mulpadd 3, \arg1
        mulpadd 4, \arg1
        mulpadd 5, \arg1
        mulpadd 6, \arg1
        mulpade 7, \arg1

.if (\arg1 % 8 == 0)
        adc     r8, zero
.elseif (\arg1 % 8 == 1)
        adc     r9, zero
.elseif (\arg1 % 8 == 2)
        adc     r10, zero
.elseif (\arg1 % 8 == 3)
        adc     r11, zero
.elseif (\arg1 % 8 == 4)
        adc     r12, zero
.elseif (\arg1 % 8 == 5)
        adc     r13, zero
.elseif (\arg1 % 8 == 6)
        adc     r14, zero
.elseif (\arg1 % 8 == 7)
        adc     r15, zero
.endif


.endm

// Special zero version of mulrow, setting up the window from scratch

.macro mulrowz
        mov     rdx, [y]
        xor     zeroe, zeroe

        mulx    r9, rax, [x]
        mov     [z], rax

        mulx    r10, rax, [x+8]
        adcx     r9, rax

        mulx    r11, rax, [x+16]
        adcx    r10, rax

        mulx    r12, rax, [x+24]
        adcx    r11, rax

        mulx    r13, rax, [x+32]
        adcx    r12, rax

        mulx    r14, rax, [x+40]
        adcx    r13, rax

        mulx    r15, rax, [x+48]
        adcx    r14, rax

        mulx    r8, rax, [x+56]
        adcx    r15, rax

        adc     r8, zero
.endm

// Multiply-add: z := x[0..7] * y plus window

.macro mulrows
        mulrowz
        mulrow  1
        mulrow  2
        mulrow  3
        mulrow  4
        mulrow  5
        mulrow  6
        mulrow  7

        mulrow  8
        mulrow  9
        mulrow  10
        mulrow  11
        mulrow  12
        mulrow  13
        mulrow  14
        mulrow  15

        mov     [z+128], r8
        mov     [z+136], r9
        mov     [z+144], r10
        mov     [z+152], r11
        mov     [z+160], r12
        mov     [z+168], r13
        mov     [z+176], r14
        mov     [z+184], r15

.endm


S2N_BN_SYMBOL(bignum_kmul_16_32):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save more registers to play with

        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)

// Move y into its permanent home, freeing up rdx for its special role in muls

        mov     y, rdx

// Do the zeroth row as a pure product then the next as multiply-add

        mulrows

        add     z, 64
        add     x, 64
        addrows

// Restore registers and return

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

S2N_BN_SIZE_DIRECTIVE(bignum_kmul_16_32)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
