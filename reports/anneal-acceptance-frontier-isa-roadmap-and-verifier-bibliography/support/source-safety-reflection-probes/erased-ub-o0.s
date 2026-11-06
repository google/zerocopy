	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RNvNtCsjIpoRzUjyHQ_4core4hint21unreachable_uncheckedCsiiRSCCMWLIh_9erased_ub:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	bl	__RNvNvNtCsjIpoRzUjyHQ_4core4hint21unreachable_unchecked18precondition_checkCsiiRSCCMWLIh_9erased_ub
	brk	#0x1
	.cfi_endproc

	.p2align	2
__RNvNvNtCsjIpoRzUjyHQ_4core4hint21unreachable_unchecked18precondition_checkCsiiRSCCMWLIh_9erased_ub:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x3, x0
	adrp	x0, l_anon.22dde56aa702025e46fe93446a044f8a.0@PAGE
	add	x0, x0, l_anon.22dde56aa702025e46fe93446a044f8a.0@PAGEOFF
	mov	w8, #399
	mov	x1, x8
	mov	w8, #0
	and	w2, w8, #0x1
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking18panic_nounwind_fmt
	.cfi_endproc

	.globl	_always_seven
	.p2align	2
_always_seven:
	.cfi_startproc
	mov	w0, #7
	ret
	.cfi_endproc

	.globl	_broken_safe_api
	.p2align	2
_broken_safe_api:
Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception0
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_remember_state
	cbz	w0, LBB3_2
	b	LBB3_1
LBB3_1:
	mov	w0, #7
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
LBB3_2:
	.cfi_restore_state
Ltmp0:
	adrp	x0, l_anon.22dde56aa702025e46fe93446a044f8a.2@PAGE
	add	x0, x0, l_anon.22dde56aa702025e46fe93446a044f8a.2@PAGEOFF
	bl	__RNvNtCsjIpoRzUjyHQ_4core4hint21unreachable_uncheckedCsiiRSCCMWLIh_9erased_ub
Ltmp1:
	b	LBB3_4
LBB3_3:
Ltmp2:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking19panic_cannot_unwind
LBB3_4:
	brk	#0x1
Lfunc_end0:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table3:
Lexception0:
	.byte	255
	.byte	155
	.uleb128 Lttbase0-Lttbaseref0
Lttbaseref0:
	.byte	1
	.uleb128 Lcst_end0-Lcst_begin0
Lcst_begin0:
	.uleb128 Ltmp0-Lfunc_begin0
	.uleb128 Ltmp1-Ltmp0
	.uleb128 Ltmp2-Lfunc_begin0
	.byte	1
Lcst_end0:
	.byte	127
	.byte	0
	.p2align	2, 0x0
Lttbase0:
	.byte	0
	.p2align	2, 0x0

	.section	__TEXT,__const
l_anon.22dde56aa702025e46fe93446a044f8a.0:
	.ascii	"unsafe precondition(s) violated: hint::unreachable_unchecked must never be reached\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety."

	.section	__TEXT,__cstring,cstring_literals
l_anon.22dde56aa702025e46fe93446a044f8a.1:
	.asciz	"erased_ub.rs"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.22dde56aa702025e46fe93446a044f8a.2:
	.quad	l_anon.22dde56aa702025e46fe93446a044f8a.1
	.asciz	"\f\000\000\000\000\000\000\000\007\000\000\000\022\000\000"

.subsections_via_symbols
