// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0


// ----------------------------------------------------------------------------
// Given table: uint64_t[height*width], copy table[idx*width...(idx+1)*width-1]
// into z[0..width-1].
//
//    extern void bignum_copy_row_from_table
//     (uint64_t *z, const uint64_t *table, uint64_t height, uint64_t width,
//      uint64_t idx);
//
// Standard x86-64 ABI: RDI = z, RSI = table, RDX = height, RCX = width,
//                      R8 = idx
// Microsoft x64 ABI:   RCX = z, RDX = table, R8 = height, R9 = width,
//                      [RSP+40] = idx
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_copy_row_from_table)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(bignum_copy_row_from_table)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_copy_row_from_table)
        .text
        .balign 32

#define z rdi
#define table rsi
#define height rdx
#define width rcx
#define idx r8

#define i   r9
#define j   r10

S2N_BN_SYMBOL(bignum_copy_row_from_table):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        mov     r8, [rsp+56] // offset adjusted after two pushes above
#endif

        test    height, height
        jz      Lbignum_copy_row_from_table_end
        test    width, width
        jz      Lbignum_copy_row_from_table_end
        mov     rax, z
        mov     i, width

Lbignum_copy_row_from_table_initzero:
        mov     QWORD PTR [rax], 0
        add     rax, 8
        dec     i
        jnz     Lbignum_copy_row_from_table_initzero

        mov     i, 0
        mov     rax, table

Lbignum_copy_row_from_table_outerloop:
        mov     j, 0

Lbignum_copy_row_from_table_innerloop:
        xor     r11, r11
        cmp      i, idx
        // cmov always read the memory address
        // https://stackoverflow.com/a/54050427
        cmove    r11, [rax+8*j]
        or       [z+8*j], r11

        inc     j
        cmp     j, width
        jne     Lbignum_copy_row_from_table_innerloop

Lbignum_copy_row_from_table_innerloop_done:
        lea     j, [width*8]
        add     rax, j
        inc     i
        cmp     i, height
                                jne                     Lbignum_copy_row_from_table_outerloop

Lbignum_copy_row_from_table_end:
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(bignum_copy_row_from_table)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
