	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	__RNvXCsaRjX8Jq8tjD_7cleanupNtB2_5GuardNtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4drop
	.p2align	2
__RNvXCsaRjX8Jq8tjD_7cleanupNtB2_5GuardNtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4drop:
	.cfi_startproc
	sub	sp, sp, #16
	.cfi_def_cfa_offset 16
	mov	w8, #7
	str	x8, [sp, #8]
	add	x8, sp, #8
	; InlineAsm Start
	; InlineAsm End
	add	sp, sp, #16
	.cfi_def_cfa_offset 0
	ret
	.cfi_endproc

	.globl	_rust_cleanup
	.p2align	2
_rust_cleanup:
Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception0
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_remember_state
Ltmp1:
	blr	x0
Ltmp2:
	mov	w8, #7
	str	x8, [sp, #8]
	add	x8, sp, #8
	; InlineAsm Start
	; InlineAsm End
	mov	w0, #23
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
LBB1_2:
	.cfi_restore_state
Ltmp3:
	mov	w8, #7
	str	x8, [sp, #8]
	add	x8, sp, #8
	; InlineAsm Start
	; InlineAsm End
	bl	__Unwind_Resume
Lfunc_end0:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table1:
Lexception0:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 Lcst_end0-Lcst_begin0
Lcst_begin0:
	.uleb128 Ltmp1-Lfunc_begin0
	.uleb128 Ltmp2-Ltmp1
	.uleb128 Ltmp3-Lfunc_begin0
	.byte	0
	.uleb128 Ltmp2-Lfunc_begin0
	.uleb128 Lfunc_end0-Ltmp2
	.byte	0
	.byte	0
Lcst_end0:
	.p2align	2, 0x0

.subsections_via_symbols
