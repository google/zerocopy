	.build_version macos, 11, 0

	; PREPARED ONLY: parent ABI/CFI review and compile/metadata gate precede execution.
	; Darwin aarch64-apple-darwin, not arm64e; ordinary whole function, no asm! block.
	; C-unwind ABI: x0 = extern C-unwind fn(u64)->u64, x1 = value.
	; Result: callback(value).wrapping_add(1), or propagate its permitted Rust unwind.
	; DWARF registers: 29=x29, 30=x30/LR, 31=SP.
	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
	.globl	_anneal_unwind_bounce
_anneal_unwind_bounce:
	.cfi_startproc
	.cfi_def_cfa wsp, 0
	.cfi_same_value w29
	.cfi_same_value w30
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	.cfi_offset w29, -16
	.cfi_offset w30, -8
	mov	x29, sp
	.cfi_def_cfa_register w29
	mov	x16, x0
	mov	x0, x1
	blr	x16
	add	x0, x0, #1
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa wsp, 0
	.cfi_same_value w29
	.cfi_same_value w30
	ret
	.cfi_endproc
	.globl	_anneal_unwind_bounce_end
_anneal_unwind_bounce_end:
.subsections_via_symbols

	.private_extern	__RINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB4_7process8ExitCodeECsle4UtX85Rrh_8specimen
	.globl	__RINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB4_7process8ExitCodeECsle4UtX85Rrh_8specimen
	.p2align	2
__RINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB4_7process8ExitCodeECsle4UtX85Rrh_8specimen:
	.cfi_startproc
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	str	x0, [sp, #8]
Lloh0:
	adrp	x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.4@PAGE
Lloh1:
	add	x1, x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.4@PAGEOFF
	add	x0, sp, #8
	bl	__RNvNtCs1SSuMAdGM58_3std2rt19lang_start_internal
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.loh AdrpAdd	Lloh0, Lloh1
	.cfi_endproc

	.p2align	2
__RINvNtCs1SSuMAdGM58_3std5panic9panic_anyNtCsle4UtX85Rrh_8specimen13ExpectedPanicEBE_:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	bl	__RINvNtCs1SSuMAdGM58_3std9panicking11begin_panicNtCsle4UtX85Rrh_8specimen13ExpectedPanicEBL_
	.cfi_endproc

	.p2align	2
__RINvNtCs1SSuMAdGM58_3std9panicking11begin_panicNtCsle4UtX85Rrh_8specimen13ExpectedPanicEBL_:
	.cfi_startproc
	sub	sp, sp, #48
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, #22340
	movk	x8, #21838, lsl #16
	movk	x8, #12383, lsl #32
	movk	x8, #17716, lsl #48
	stp	x8, x0, [sp, #16]
Lloh2:
	adrp	x9, l_anon.9da64be1d17a499d89cdacccc8d87f3d.15@PAGE
Lloh3:
	add	x9, x9, l_anon.9da64be1d17a499d89cdacccc8d87f3d.15@PAGEOFF
	str	x9, [sp, #8]
	add	x0, sp, #8
	bl	__RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace26___rust_end_short_backtraceNCINvNtB6_9panicking11begin_panicNtCsle4UtX85Rrh_8specimen13ExpectedPanicE0zEB1E_
	.loh AdrpAdd	Lloh2, Lloh3
	.cfi_endproc

	.p2align	2
__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EECsle4UtX85Rrh_8specimen:
Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception0
	stp	x22, x21, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x20, x19, [sp, #16]
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	.cfi_remember_state
	mov	x19, x0
	ldr	x21, [x0, #8]
	ldr	x8, [x21]
	cbz	x8, LBB3_2
	ldr	x20, [x19]
Ltmp0:
	mov	x0, x20
	blr	x8
Ltmp1:
LBB3_2:
	ldr	x1, [x21, #8]
	cbz	x1, LBB3_4
	ldr	x2, [x21, #16]
	ldr	x0, [x19]
	.cfi_def_cfa wsp, 48
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	b	__RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc
LBB3_4:
	.cfi_restore_state
	.cfi_remember_state
	.cfi_def_cfa wsp, 48
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	ret
LBB3_5:
	.cfi_restore_state
Ltmp2:
	mov	x19, x0
	ldr	x1, [x21, #8]
	cbz	x1, LBB3_7
	ldr	x2, [x21, #16]
	mov	x0, x20
	bl	__RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc
LBB3_7:
	mov	x0, x19
	bl	__Unwind_Resume
Lfunc_end0:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table3:
Lexception0:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 Lcst_end0-Lcst_begin0
Lcst_begin0:
	.uleb128 Ltmp0-Lfunc_begin0
	.uleb128 Ltmp1-Ltmp0
	.uleb128 Ltmp2-Lfunc_begin0
	.byte	0
	.uleb128 Ltmp1-Lfunc_begin0
	.uleb128 Lfunc_end0-Ltmp1
	.byte	0
	.byte	0
Lcst_end0:
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtCs6zY7rJBZy9D_5alloc6borrow3CoweEECsle4UtX85Rrh_8specimen:
Lfunc_begin1:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception1
	stp	x20, x19, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_remember_state
	ldr	x8, [x0]
	cmn	x8, #1
	b.eq	LBB4_3
Ltmp3:
	mov	x19, x0
	bl	__RNvXsp_NtCs6zY7rJBZy9D_5alloc3vecINtB5_3VechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp4:
	mov	x0, x19
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	b	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
LBB4_3:
	.cfi_restore_state
	.cfi_remember_state
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
LBB4_4:
	.cfi_restore_state
Ltmp5:
	mov	x20, x0
Ltmp6:
	mov	x0, x19
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp7:
	mov	x0, x20
	bl	__Unwind_Resume
LBB4_6:
Ltmp8:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
Lfunc_end1:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table4:
Lexception1:
	.byte	255
	.byte	155
	.uleb128 Lttbase0-Lttbaseref0
Lttbaseref0:
	.byte	1
	.uleb128 Lcst_end1-Lcst_begin1
Lcst_begin1:
	.uleb128 Ltmp3-Lfunc_begin1
	.uleb128 Ltmp4-Ltmp3
	.uleb128 Ltmp5-Lfunc_begin1
	.byte	0
	.uleb128 Ltmp4-Lfunc_begin1
	.uleb128 Ltmp6-Ltmp4
	.byte	0
	.byte	0
	.uleb128 Ltmp6-Lfunc_begin1
	.uleb128 Ltmp7-Ltmp6
	.uleb128 Ltmp8-Lfunc_begin1
	.byte	1
	.uleb128 Ltmp7-Lfunc_begin1
	.uleb128 Lfunc_end1-Ltmp7
	.byte	0
	.byte	0
Lcst_end1:
	.byte	127
	.byte	0
	.p2align	2, 0x0
Lttbase0:
	.byte	0
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueNCNvCsle4UtX85Rrh_8specimen3run0EBF_:
Lfunc_begin2:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception2
	stp	x22, x21, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x20, x19, [sp, #16]
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	.cfi_remember_state
	mov	x19, x0
	ldr	x21, [x0, #8]
	ldr	x8, [x21]
	cbz	x8, LBB5_2
	ldr	x20, [x19]
Ltmp9:
	mov	x0, x20
	blr	x8
Ltmp10:
LBB5_2:
	ldr	x1, [x21, #8]
	cbz	x1, LBB5_4
	ldr	x2, [x21, #16]
	ldr	x0, [x19]
	.cfi_def_cfa wsp, 48
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	b	__RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc
LBB5_4:
	.cfi_restore_state
	.cfi_remember_state
	.cfi_def_cfa wsp, 48
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	ret
LBB5_5:
	.cfi_restore_state
Ltmp11:
	mov	x19, x0
	ldr	x1, [x21, #8]
	cbz	x1, LBB5_7
	ldr	x2, [x21, #16]
	mov	x0, x20
	bl	__RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc
LBB5_7:
	mov	x0, x19
	bl	__Unwind_Resume
Lfunc_end2:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table5:
Lexception2:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 Lcst_end2-Lcst_begin2
Lcst_begin2:
	.uleb128 Ltmp9-Lfunc_begin2
	.uleb128 Ltmp10-Ltmp9
	.uleb128 Ltmp11-Lfunc_begin2
	.byte	0
	.uleb128 Ltmp10-Lfunc_begin2
	.uleb128 Lfunc_end2-Ltmp10
	.byte	0
	.byte	0
Lcst_end2:
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueNtNtCs6zY7rJBZy9D_5alloc6string6StringECsle4UtX85Rrh_8specimen:
Lfunc_begin3:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception3
	stp	x20, x19, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_remember_state
	mov	x19, x0
Ltmp12:
	bl	__RNvXsp_NtCs6zY7rJBZy9D_5alloc3vecINtB5_3VechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp13:
	mov	x0, x19
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	b	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
LBB6_2:
	.cfi_restore_state
Ltmp14:
	mov	x20, x0
Ltmp15:
	mov	x0, x19
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp16:
	mov	x0, x20
	bl	__Unwind_Resume
LBB6_4:
Ltmp17:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
Lfunc_end3:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table6:
Lexception3:
	.byte	255
	.byte	155
	.uleb128 Lttbase1-Lttbaseref1
Lttbaseref1:
	.byte	1
	.uleb128 Lcst_end3-Lcst_begin3
Lcst_begin3:
	.uleb128 Ltmp12-Lfunc_begin3
	.uleb128 Ltmp13-Ltmp12
	.uleb128 Ltmp14-Lfunc_begin3
	.byte	0
	.uleb128 Ltmp13-Lfunc_begin3
	.uleb128 Ltmp15-Ltmp13
	.byte	0
	.byte	0
	.uleb128 Ltmp15-Lfunc_begin3
	.uleb128 Ltmp16-Ltmp15
	.uleb128 Ltmp17-Lfunc_begin3
	.byte	1
	.uleb128 Ltmp16-Lfunc_begin3
	.uleb128 Lfunc_end3-Ltmp16
	.byte	0
	.byte	0
Lcst_end3:
	.byte	127
	.byte	0
	.p2align	2, 0x0
Lttbase1:
	.byte	0
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace26___rust_end_short_backtraceNCINvNtB6_9panicking11begin_panicNtCsle4UtX85Rrh_8specimen13ExpectedPanicE0zEB1E_:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	bl	__RNCINvNtCs1SSuMAdGM58_3std9panicking11begin_panicNtCsle4UtX85Rrh_8specimen13ExpectedPanicE0BN_
	.cfi_endproc

	.p2align	2
__RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECsle4UtX85Rrh_8specimen:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	blr	x0
	; InlineAsm Start
	; InlineAsm End
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.p2align	2
__RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Csle4UtX85Rrh_8specimen:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	ldr	x0, [x0]
	bl	__RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECsle4UtX85Rrh_8specimen
	and	w0, w0, #0xff
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.p2align	2
__RNCINvNtCs1SSuMAdGM58_3std9panicking11begin_panicNtCsle4UtX85Rrh_8specimen13ExpectedPanicE0BN_:
	.cfi_startproc
	sub	sp, sp, #48
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	ldp	x10, x8, [x0, #8]
	mov	w9, #1
	ldr	x2, [x0]
	stp	x9, x10, [sp, #8]
	str	x8, [sp, #24]
Lloh4:
	adrp	x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.5@PAGE
Lloh5:
	add	x1, x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.5@PAGEOFF
	add	x0, sp, #8
	mov	w3, #1
	mov	w4, #0
	bl	__RNvNtCs1SSuMAdGM58_3std9panicking15panic_with_hook
	.loh AdrpAdd	Lloh4, Lloh5
	.cfi_endproc

	.p2align	2
__RNCNvCsle4UtX85Rrh_8specimen3run0B3_:
	.cfi_startproc
	sub	sp, sp, #80
	.cfi_def_cfa_offset 80
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	stp	x29, x30, [sp, #64]
	add	x29, sp, #64
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	mov	x19, x1
	mov	x20, x0
	ldp	x21, x8, [x1]
	ldr	x9, [x8, #24]
	mov	x8, sp
	mov	x0, x21
	blr	x9
	ldp	x8, x9, [sp]
	mov	x10, #22594
	movk	x10, #50467, lsl #16
	movk	x10, #60122, lsl #32
	movk	x10, #4629, lsl #48
	eor	x9, x9, x10
	mov	x10, #30253
	movk	x10, #51344, lsl #16
	movk	x10, #1343, lsl #32
	movk	x10, #21237, lsl #48
	eor	x8, x8, x10
	orr	x9, x8, x9
	cmp	x9, #0
	csel	x8, x21, xzr, eq
	cbnz	x9, LBB11_4
	ldr	x9, [x21]
	mov	x10, #22340
	movk	x10, #21838, lsl #16
	movk	x10, #12383, lsl #32
	movk	x10, #17716, lsl #48
	cmp	x9, x10
	b.ne	LBB11_4
	mov	x9, x8
	ldr	x10, [x9, #8]!
	mov	x11, #30600
	movk	x11, #21862, lsl #16
	movk	x11, #13124, lsl #32
	movk	x11, #4386, lsl #48
	cmp	x10, x11
	b.ne	LBB11_4
Lloh6:
	adrp	x10, __RNvCsle4UtX85Rrh_8specimen14EXPECTED_HOOKS@PAGE
Lloh7:
	add	x10, x10, __RNvCsle4UtX85Rrh_8specimen14EXPECTED_HOOKS@PAGEOFF
Lloh8:
	adrp	x11, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGE
Lloh9:
	ldr	x11, [x11, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGEOFF]
	mov	w12, #1
	ldaddal	x12, x10, [x10]
	stp	x8, x11, [sp]
	stp	x9, x11, [sp, #16]
Lloh10:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.9@PAGE
Lloh11:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.9@PAGEOFF
	mov	x1, sp
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio7__eprint
	b	LBB11_5
LBB11_4:
	ldp	x0, x8, [x20]
	ldr	x8, [x8, #40]
	mov	x1, x19
	blr	x8
LBB11_5:
	.cfi_def_cfa wsp, 80
	ldp	x29, x30, [sp, #64]
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	ret
	.loh AdrpAdd	Lloh10, Lloh11
	.loh AdrpLdrGot	Lloh8, Lloh9
	.loh AdrpAdd	Lloh6, Lloh7
	.cfi_endproc

	.p2align	2
__RNSNvYNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtBb_7process8ExitCodeE0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_once6vtableCsle4UtX85Rrh_8specimen:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	ldr	x0, [x0]
	bl	__RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECsle4UtX85Rrh_8specimen
	and	w0, w0, #0xff
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.p2align	2
__RNSNvYNCNvCsle4UtX85Rrh_8specimen3run0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceTRNtNtCs1SSuMAdGM58_3std5panic13PanicHookInfoEE9call_once6vtableB8_:
Lfunc_begin4:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception4
	sub	sp, sp, #96
	.cfi_def_cfa_offset 96
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	stp	x29, x30, [sp, #80]
	add	x29, sp, #80
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	.cfi_remember_state
	mov	x20, x1
	ldp	x19, x22, [x0]
	stp	x19, x22, [sp]
	ldp	x21, x8, [x1]
	ldr	x9, [x8, #24]
Ltmp18:
	add	x8, sp, #16
	mov	x0, x21
	blr	x9
Ltmp19:
	ldp	x8, x9, [sp, #16]
	mov	x10, #22594
	movk	x10, #50467, lsl #16
	movk	x10, #60122, lsl #32
	movk	x10, #4629, lsl #48
	eor	x9, x9, x10
	mov	x10, #30253
	movk	x10, #51344, lsl #16
	movk	x10, #1343, lsl #32
	movk	x10, #21237, lsl #48
	eor	x8, x8, x10
	orr	x9, x8, x9
	cmp	x9, #0
	csel	x8, x21, xzr, eq
	cbnz	x9, LBB13_5
	ldr	x9, [x21]
	mov	x10, #22340
	movk	x10, #21838, lsl #16
	movk	x10, #12383, lsl #32
	movk	x10, #17716, lsl #48
	cmp	x9, x10
	b.ne	LBB13_5
	mov	x9, x8
	ldr	x10, [x9, #8]!
	mov	x11, #30600
	movk	x11, #21862, lsl #16
	movk	x11, #13124, lsl #32
	movk	x11, #4386, lsl #48
	cmp	x10, x11
	b.ne	LBB13_5
Lloh12:
	adrp	x10, __RNvCsle4UtX85Rrh_8specimen14EXPECTED_HOOKS@PAGE
Lloh13:
	add	x10, x10, __RNvCsle4UtX85Rrh_8specimen14EXPECTED_HOOKS@PAGEOFF
Lloh14:
	adrp	x11, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGE
Lloh15:
	ldr	x11, [x11, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGEOFF]
	mov	w12, #1
	ldaddal	x12, x10, [x10]
	stp	x8, x11, [sp, #16]
	stp	x9, x11, [sp, #32]
Ltmp22:
Lloh16:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.9@PAGE
Lloh17:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.9@PAGEOFF
	add	x1, sp, #16
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio7__eprint
Ltmp23:
	b	LBB13_6
LBB13_5:
	ldr	x8, [x22, #40]
Ltmp20:
	mov	x0, x19
	mov	x1, x20
	blr	x8
Ltmp21:
LBB13_6:
	ldr	x8, [x22]
	cbz	x8, LBB13_8
Ltmp28:
	mov	x0, x19
	blr	x8
Ltmp29:
LBB13_8:
	ldr	x1, [x22, #8]
	cbz	x1, LBB13_10
	ldr	x2, [x22, #16]
	mov	x0, x19
	bl	__RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc
LBB13_10:
	.cfi_def_cfa wsp, 96
	ldp	x29, x30, [sp, #80]
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	add	sp, sp, #96
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	ret
LBB13_11:
	.cfi_restore_state
Ltmp30:
	mov	x20, x0
	ldr	x1, [x22, #8]
	cbz	x1, LBB13_14
	ldr	x2, [x22, #16]
	mov	x0, x19
	bl	__RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc
	mov	x0, x20
	bl	__Unwind_Resume
LBB13_13:
Ltmp24:
	mov	x20, x0
Ltmp25:
	mov	x0, sp
	bl	__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueNCNvCsle4UtX85Rrh_8specimen3run0EBF_
Ltmp26:
LBB13_14:
	mov	x0, x20
	bl	__Unwind_Resume
LBB13_15:
Ltmp27:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
	.loh AdrpAdd	Lloh16, Lloh17
	.loh AdrpLdrGot	Lloh14, Lloh15
	.loh AdrpAdd	Lloh12, Lloh13
Lfunc_end4:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table13:
Lexception4:
	.byte	255
	.byte	155
	.uleb128 Lttbase2-Lttbaseref2
Lttbaseref2:
	.byte	1
	.uleb128 Lcst_end4-Lcst_begin4
Lcst_begin4:
	.uleb128 Ltmp18-Lfunc_begin4
	.uleb128 Ltmp21-Ltmp18
	.uleb128 Ltmp24-Lfunc_begin4
	.byte	0
	.uleb128 Ltmp28-Lfunc_begin4
	.uleb128 Ltmp29-Ltmp28
	.uleb128 Ltmp30-Lfunc_begin4
	.byte	0
	.uleb128 Ltmp29-Lfunc_begin4
	.uleb128 Ltmp25-Ltmp29
	.byte	0
	.byte	0
	.uleb128 Ltmp25-Lfunc_begin4
	.uleb128 Ltmp26-Ltmp25
	.uleb128 Ltmp27-Lfunc_begin4
	.byte	1
	.uleb128 Ltmp26-Lfunc_begin4
	.uleb128 Lfunc_end4-Ltmp26
	.byte	0
	.byte	0
Lcst_end4:
	.byte	127
	.byte	0
	.p2align	2, 0x0
Lttbase2:
	.byte	0
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RNvCsle4UtX85Rrh_8specimen11trace_frame:
	.cfi_startproc
	mov	x8, x0
	mov	w0, #5
	cbz	x8, LBB14_6
	cbz	x1, LBB14_6
	stp	x20, x19, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	ldr	x19, [x1, #512]
	cmp	x19, #63
	b.ls	LBB14_4
	mov	w8, #1
	strb	w8, [x1, #524]
	mov	w0, #5
	b	LBB14_5
LBB14_4:
	mov	x0, x8
	mov	x20, x1
	bl	__Unwind_GetIP
	mov	x8, x0
	mov	w0, #0
	str	x8, [x20, x19, lsl #3]
	ldr	x8, [x20, #512]
	add	x8, x8, #1
	str	x8, [x20, #512]
LBB14_5:
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
LBB14_6:
	ret
	.cfi_endproc

	.p2align	2
__RNvCsle4UtX85Rrh_8specimen13capture_trace:
	.cfi_startproc
	stp	x20, x19, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_remember_state
	sub	sp, sp, #528
	strb	wzr, [sp, #524]
	mov	x0, sp
	mov	w1, #520
	bl	_bzero
	mov	w8, #-1
	str	w8, [sp, #520]
Lloh18:
	adrp	x0, __RNvCsle4UtX85Rrh_8specimen11trace_frame@PAGE
Lloh19:
	add	x0, x0, __RNvCsle4UtX85Rrh_8specimen11trace_frame@PAGEOFF
	mov	x1, sp
	bl	__Unwind_Backtrace
	str	w0, [sp, #520]
Lloh20:
	adrp	x0, __RNvNCNKNvCsle4UtX85Rrh_8specimen10LAST_TRACE0s_023___RUST_STD_INTERNAL_VAL@TLVPPAGE
Lloh21:
	ldr	x0, [x0, __RNvNCNKNvCsle4UtX85Rrh_8specimen10LAST_TRACE0s_023___RUST_STD_INTERNAL_VAL@TLVPPAGEOFF]
	ldr	x8, [x0]
	blr	x8
	ldr	x8, [x0]
	cbnz	x8, LBB15_2
	mov	x19, x0
	mov	x8, #-1
	str	x8, [x0], #8
	mov	x1, sp
	mov	w2, #528
	bl	_memcpy
	str	xzr, [x19]
	add	sp, sp, #528
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
LBB15_2:
	.cfi_restore_state
Lloh22:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.7@PAGE
Lloh23:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.7@PAGEOFF
	bl	__RNvNtCsjIpoRzUjyHQ_4core4cell22panic_already_borrowed
	.loh AdrpLdr	Lloh20, Lloh21
	.loh AdrpAdd	Lloh18, Lloh19
	.loh AdrpAdd	Lloh22, Lloh23
	.cfi_endproc

	.p2align	2
__RNvCsle4UtX85Rrh_8specimen14image_identity:
Lfunc_begin5:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception5
	sub	sp, sp, #288
	.cfi_def_cfa_offset 288
	stp	x22, x21, [sp, #240]
	stp	x20, x19, [sp, #256]
	stp	x29, x30, [sp, #272]
	add	x29, sp, #272
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	.cfi_remember_state
	mov	x20, x2
	mov	x19, x8
	stp	x0, x1, [sp, #8]
	str	x2, [sp, #24]
	movi.2d	v0, #0000000000000000
	stp	q0, q0, [sp, #32]
	add	x1, sp, #32
	mov	x0, x2
	bl	_dladdr
	cbz	w0, LBB16_2
	ldp	x21, x8, [sp, #32]
	cmp	x21, #0
	ccmp	x8, #0, #4, ne
	b.ne	LBB16_3
LBB16_2:
Lloh24:
	adrp	x8, __RNvXs1i_NtCsjIpoRzUjyHQ_4core3fmtReNtB6_7Display3fmtCs6thXTpflXIc_14rustc_demangle@GOTPAGE
Lloh25:
	ldr	x8, [x8, __RNvXs1i_NtCsjIpoRzUjyHQ_4core3fmtReNtB6_7Display3fmtCs6thXTpflXIc_14rustc_demangle@GOTPAGEOFF]
	add	x9, sp, #8
	stp	x9, x8, [sp, #128]
Lloh26:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.14@PAGE
Lloh27:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.14@PAGEOFF
	add	x1, sp, #128
	mov	x8, x19
	bl	__RNvNvNtCs6zY7rJBZy9D_5alloc3fmt6format12format_inner
	b	LBB16_22
LBB16_3:
	mov	x0, x21
	bl	_strlen
	add	x8, sp, #64
	add	x1, x0, #1
	mov	x0, x21
	bl	__RNvMsD_NtNtCs6zY7rJBZy9D_5alloc3ffi5c_strNtNtNtCsjIpoRzUjyHQ_4core3ffi5c_str4CStr15to_string_lossy
	ldr	x21, [sp, #48]
	cbz	x21, LBB16_5
	mov	x0, x21
	bl	_strlen
Ltmp31:
	add	x8, sp, #88
	add	x1, x0, #1
	mov	x0, x21
	bl	__RNvMsD_NtNtCs6zY7rJBZy9D_5alloc3ffi5c_strNtNtNtCsjIpoRzUjyHQ_4core3ffi5c_str4CStr15to_string_lossy
Ltmp32:
	b	LBB16_6
LBB16_5:
Lloh28:
	adrp	x8, l_anon.9da64be1d17a499d89cdacccc8d87f3d.12@PAGE
Lloh29:
	add	x8, x8, l_anon.9da64be1d17a499d89cdacccc8d87f3d.12@PAGEOFF
	mov	w9, #11
	stp	x8, x9, [sp, #96]
	mov	x9, #-1
	str	x9, [sp, #88]
LBB16_6:
	ldr	x8, [sp, #40]
	str	x8, [sp, #112]
	subs	x8, x20, x8
	b.hs	LBB16_8
Lloh30:
	adrp	x8, __RNvXs1i_NtCsjIpoRzUjyHQ_4core3fmtReNtB6_7Display3fmtCs6thXTpflXIc_14rustc_demangle@GOTPAGE
Lloh31:
	ldr	x8, [x8, __RNvXs1i_NtCsjIpoRzUjyHQ_4core3fmtReNtB6_7Display3fmtCs6thXTpflXIc_14rustc_demangle@GOTPAGEOFF]
	add	x9, sp, #8
	stp	x9, x8, [x29, #-48]
Ltmp33:
Lloh32:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.8@PAGE
Lloh33:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.8@PAGEOFF
	add	x8, sp, #128
	sub	x1, x29, #48
	bl	__RNvNvNtCs6zY7rJBZy9D_5alloc3fmt6format12format_inner
Ltmp34:
	b	LBB16_9
LBB16_8:
	mov	x9, #-1
	stp	x9, x8, [sp, #128]
LBB16_9:
	ldp	x9, x8, [sp, #128]
	cmn	x9, #1
	b.eq	LBB16_15
	ldr	x10, [sp, #144]
	stp	x9, x8, [x19]
	str	x10, [x19, #16]
	ldr	x8, [sp, #88]
	cmn	x8, #1
	b.eq	LBB16_13
Ltmp35:
	add	x0, sp, #88
	bl	__RNvXsp_NtCs6zY7rJBZy9D_5alloc3vecINtB5_3VechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp36:
Ltmp41:
	add	x0, sp, #88
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp42:
LBB16_13:
	ldr	x8, [sp, #64]
	cmn	x8, #1
	b.eq	LBB16_22
Ltmp43:
	add	x0, sp, #64
	bl	__RNvXsp_NtCs6zY7rJBZy9D_5alloc3vecINtB5_3VechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp44:
	b	LBB16_21
LBB16_15:
	str	x8, [sp, #120]
	add	x8, sp, #8
Lloh34:
	adrp	x9, __RNvXs1i_NtCsjIpoRzUjyHQ_4core3fmtReNtB6_7Display3fmtCs6thXTpflXIc_14rustc_demangle@GOTPAGE
Lloh35:
	ldr	x9, [x9, __RNvXs1i_NtCsjIpoRzUjyHQ_4core3fmtReNtB6_7Display3fmtCs6thXTpflXIc_14rustc_demangle@GOTPAGEOFF]
	stp	x8, x9, [sp, #128]
	add	x8, sp, #24
Lloh36:
	adrp	x9, __RNvXs6_NtNtCsjIpoRzUjyHQ_4core3fmt3numjNtB7_8LowerHex3fmt@GOTPAGE
Lloh37:
	ldr	x9, [x9, __RNvXs6_NtNtCsjIpoRzUjyHQ_4core3fmt3numjNtB7_8LowerHex3fmt@GOTPAGEOFF]
	stp	x8, x9, [sp, #144]
	add	x8, sp, #112
	stp	x8, x9, [sp, #160]
	add	x8, sp, #120
	stp	x8, x9, [sp, #176]
Lloh38:
	adrp	x8, __RNvXsb_NtCs6zY7rJBZy9D_5alloc6borrowINtB5_3CoweENtNtCsjIpoRzUjyHQ_4core3fmt7Display3fmtCsle4UtX85Rrh_8specimen@PAGE
Lloh39:
	add	x8, x8, __RNvXsb_NtCs6zY7rJBZy9D_5alloc6borrowINtB5_3CoweENtNtCsjIpoRzUjyHQ_4core3fmt7Display3fmtCsle4UtX85Rrh_8specimen@PAGEOFF
	add	x9, sp, #88
	stp	x9, x8, [sp, #192]
	add	x9, sp, #64
	stp	x9, x8, [sp, #208]
Ltmp49:
Lloh40:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.13@PAGE
Lloh41:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.13@PAGEOFF
	add	x1, sp, #128
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio6__print
Ltmp50:
	mov	x8, #-1
	str	x8, [x19]
	ldr	x8, [sp, #88]
	cmn	x8, #1
	b.eq	LBB16_19
Ltmp54:
	add	x0, sp, #88
	bl	__RNvXsp_NtCs6zY7rJBZy9D_5alloc3vecINtB5_3VechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp55:
Ltmp60:
	add	x0, sp, #88
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp61:
LBB16_19:
	ldr	x8, [sp, #64]
	cmn	x8, #1
	b.eq	LBB16_22
Ltmp66:
	add	x0, sp, #64
	bl	__RNvXsp_NtCs6zY7rJBZy9D_5alloc3vecINtB5_3VechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp67:
LBB16_21:
	add	x0, sp, #64
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
LBB16_22:
	.cfi_def_cfa wsp, 288
	ldp	x29, x30, [sp, #272]
	ldp	x20, x19, [sp, #256]
	ldp	x22, x21, [sp, #240]
	add	sp, sp, #288
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	ret
LBB16_23:
	.cfi_restore_state
Ltmp68:
	mov	x19, x0
Ltmp69:
	add	x0, sp, #64
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp70:
	b	LBB16_34
LBB16_24:
Ltmp71:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
LBB16_25:
Ltmp56:
	mov	x19, x0
Ltmp57:
	add	x0, sp, #88
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp58:
	b	LBB16_33
LBB16_26:
Ltmp59:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
LBB16_27:
Ltmp45:
	mov	x19, x0
Ltmp46:
	add	x0, sp, #64
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp47:
	b	LBB16_34
LBB16_28:
Ltmp48:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
LBB16_29:
Ltmp37:
	mov	x19, x0
Ltmp38:
	add	x0, sp, #88
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp39:
	b	LBB16_33
LBB16_30:
Ltmp40:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
LBB16_31:
Ltmp51:
	mov	x19, x0
Ltmp52:
	add	x0, sp, #88
	bl	__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtCs6zY7rJBZy9D_5alloc6borrow3CoweEECsle4UtX85Rrh_8specimen
Ltmp53:
	b	LBB16_33
LBB16_32:
Ltmp62:
	mov	x19, x0
LBB16_33:
Ltmp63:
	add	x0, sp, #64
	bl	__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtCs6zY7rJBZy9D_5alloc6borrow3CoweEECsle4UtX85Rrh_8specimen
Ltmp64:
LBB16_34:
	mov	x0, x19
	bl	__Unwind_Resume
LBB16_35:
Ltmp65:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
	.loh AdrpAdd	Lloh26, Lloh27
	.loh AdrpLdrGot	Lloh24, Lloh25
	.loh AdrpAdd	Lloh28, Lloh29
	.loh AdrpAdd	Lloh32, Lloh33
	.loh AdrpLdrGot	Lloh30, Lloh31
	.loh AdrpAdd	Lloh40, Lloh41
	.loh AdrpAdd	Lloh38, Lloh39
	.loh AdrpLdrGot	Lloh36, Lloh37
	.loh AdrpLdrGot	Lloh34, Lloh35
Lfunc_end5:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table16:
Lexception5:
	.byte	255
	.byte	155
	.uleb128 Lttbase3-Lttbaseref3
Lttbaseref3:
	.byte	1
	.uleb128 Lcst_end5-Lcst_begin5
Lcst_begin5:
	.uleb128 Lfunc_begin5-Lfunc_begin5
	.uleb128 Ltmp31-Lfunc_begin5
	.byte	0
	.byte	0
	.uleb128 Ltmp31-Lfunc_begin5
	.uleb128 Ltmp32-Ltmp31
	.uleb128 Ltmp62-Lfunc_begin5
	.byte	0
	.uleb128 Ltmp33-Lfunc_begin5
	.uleb128 Ltmp34-Ltmp33
	.uleb128 Ltmp51-Lfunc_begin5
	.byte	0
	.uleb128 Ltmp35-Lfunc_begin5
	.uleb128 Ltmp36-Ltmp35
	.uleb128 Ltmp37-Lfunc_begin5
	.byte	0
	.uleb128 Ltmp41-Lfunc_begin5
	.uleb128 Ltmp42-Ltmp41
	.uleb128 Ltmp62-Lfunc_begin5
	.byte	0
	.uleb128 Ltmp43-Lfunc_begin5
	.uleb128 Ltmp44-Ltmp43
	.uleb128 Ltmp45-Lfunc_begin5
	.byte	0
	.uleb128 Ltmp49-Lfunc_begin5
	.uleb128 Ltmp50-Ltmp49
	.uleb128 Ltmp51-Lfunc_begin5
	.byte	0
	.uleb128 Ltmp54-Lfunc_begin5
	.uleb128 Ltmp55-Ltmp54
	.uleb128 Ltmp56-Lfunc_begin5
	.byte	0
	.uleb128 Ltmp60-Lfunc_begin5
	.uleb128 Ltmp61-Ltmp60
	.uleb128 Ltmp62-Lfunc_begin5
	.byte	0
	.uleb128 Ltmp66-Lfunc_begin5
	.uleb128 Ltmp67-Ltmp66
	.uleb128 Ltmp68-Lfunc_begin5
	.byte	0
	.uleb128 Ltmp67-Lfunc_begin5
	.uleb128 Ltmp69-Ltmp67
	.byte	0
	.byte	0
	.uleb128 Ltmp69-Lfunc_begin5
	.uleb128 Ltmp70-Ltmp69
	.uleb128 Ltmp71-Lfunc_begin5
	.byte	1
	.uleb128 Ltmp57-Lfunc_begin5
	.uleb128 Ltmp58-Ltmp57
	.uleb128 Ltmp59-Lfunc_begin5
	.byte	1
	.uleb128 Ltmp46-Lfunc_begin5
	.uleb128 Ltmp47-Ltmp46
	.uleb128 Ltmp48-Lfunc_begin5
	.byte	1
	.uleb128 Ltmp38-Lfunc_begin5
	.uleb128 Ltmp39-Ltmp38
	.uleb128 Ltmp40-Lfunc_begin5
	.byte	1
	.uleb128 Ltmp52-Lfunc_begin5
	.uleb128 Ltmp64-Ltmp52
	.uleb128 Ltmp65-Lfunc_begin5
	.byte	1
	.uleb128 Ltmp64-Lfunc_begin5
	.uleb128 Lfunc_end5-Ltmp64
	.byte	0
	.byte	0
Lcst_end5:
	.byte	127
	.byte	0
	.p2align	2, 0x0
Lttbase3:
	.byte	0
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RNvCsle4UtX85Rrh_8specimen14panic_callback:
Lfunc_begin6:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception6
	stp	x20, x19, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	mov	x19, x0
Lloh42:
	adrp	x8, __RNvCsle4UtX85Rrh_8specimen5CALLS@PAGE
Lloh43:
	add	x8, x8, __RNvCsle4UtX85Rrh_8specimen5CALLS@PAGEOFF
	mov	w9, #1
	ldaddal	x9, x8, [x8]
Ltmp72:
	bl	__RNvCsle4UtX85Rrh_8specimen13capture_trace
Ltmp73:
Ltmp74:
	mov	x0, x19
	bl	__RINvNtCs1SSuMAdGM58_3std5panic9panic_anyNtCsle4UtX85Rrh_8specimen13ExpectedPanicEBE_
Ltmp75:
	brk	#0x1
LBB17_3:
Ltmp76:
Lloh44:
	adrp	x8, __RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS@PAGE
Lloh45:
	add	x8, x8, __RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS@PAGEOFF
	mov	w9, #1
	ldaddal	x9, x8, [x8]
Lloh46:
	adrp	x8, __RNvCsle4UtX85Rrh_8specimen10DROP_ORDER@PAGE
Lloh47:
	add	x8, x8, __RNvCsle4UtX85Rrh_8specimen10DROP_ORDER@PAGEOFF
	ldar	x10, [x8]
	add	x10, x10, x10, lsl #2
	orr	x9, x9, x10, lsl #1
	stlr	x9, [x8]
	bl	__Unwind_Resume
	.loh AdrpAdd	Lloh42, Lloh43
	.loh AdrpAdd	Lloh46, Lloh47
	.loh AdrpAdd	Lloh44, Lloh45
Lfunc_end6:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table17:
Lexception6:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 Lcst_end6-Lcst_begin6
Lcst_begin6:
	.uleb128 Ltmp72-Lfunc_begin6
	.uleb128 Ltmp75-Ltmp72
	.uleb128 Ltmp76-Lfunc_begin6
	.byte	0
	.uleb128 Ltmp75-Lfunc_begin6
	.uleb128 Lfunc_end6-Ltmp75
	.byte	0
	.byte	0
Lcst_end6:
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RNvCsle4UtX85Rrh_8specimen15normal_callback:
Lfunc_begin7:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception7
	stp	x20, x19, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_remember_state
	mov	x19, x0
Lloh48:
	adrp	x8, __RNvCsle4UtX85Rrh_8specimen5CALLS@PAGE
Lloh49:
	add	x8, x8, __RNvCsle4UtX85Rrh_8specimen5CALLS@PAGEOFF
	mov	w9, #1
	ldaddal	x9, x8, [x8]
Ltmp77:
	bl	__RNvCsle4UtX85Rrh_8specimen13capture_trace
Ltmp78:
	add	x0, x19, x19, lsl #1
Lloh50:
	adrp	x8, __RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS@PAGE
Lloh51:
	add	x8, x8, __RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS@PAGEOFF
	mov	w9, #1
Lloh52:
	adrp	x10, __RNvCsle4UtX85Rrh_8specimen10DROP_ORDER@PAGE
Lloh53:
	add	x10, x10, __RNvCsle4UtX85Rrh_8specimen10DROP_ORDER@PAGEOFF
	ldaddal	x9, x8, [x8]
	ldar	x8, [x10]
	add	x8, x8, x8, lsl #2
	orr	x8, x9, x8, lsl #1
	stlr	x8, [x10]
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
LBB18_2:
	.cfi_restore_state
Ltmp79:
Lloh54:
	adrp	x8, __RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS@PAGE
Lloh55:
	add	x8, x8, __RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS@PAGEOFF
	mov	w9, #1
	ldaddal	x9, x8, [x8]
Lloh56:
	adrp	x8, __RNvCsle4UtX85Rrh_8specimen10DROP_ORDER@PAGE
Lloh57:
	add	x8, x8, __RNvCsle4UtX85Rrh_8specimen10DROP_ORDER@PAGEOFF
	ldar	x10, [x8]
	add	x10, x10, x10, lsl #2
	orr	x9, x9, x10, lsl #1
	stlr	x9, [x8]
	bl	__Unwind_Resume
	.loh AdrpAdd	Lloh48, Lloh49
	.loh AdrpAdd	Lloh52, Lloh53
	.loh AdrpAdd	Lloh50, Lloh51
	.loh AdrpAdd	Lloh56, Lloh57
	.loh AdrpAdd	Lloh54, Lloh55
Lfunc_end7:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table18:
Lexception7:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 Lcst_end7-Lcst_begin7
Lcst_begin7:
	.uleb128 Ltmp77-Lfunc_begin7
	.uleb128 Ltmp78-Ltmp77
	.uleb128 Ltmp79-Lfunc_begin7
	.byte	0
	.uleb128 Ltmp78-Lfunc_begin7
	.uleb128 Lfunc_end7-Ltmp78
	.byte	0
	.byte	0
Lcst_end7:
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.private_extern	__RNvCsle4UtX85Rrh_8specimen4main
	.globl	__RNvCsle4UtX85Rrh_8specimen4main
	.p2align	2
__RNvCsle4UtX85Rrh_8specimen4main:
Lfunc_begin8:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception8
	sub	sp, sp, #160
	.cfi_def_cfa_offset 160
	stp	x24, x23, [sp, #96]
	stp	x22, x21, [sp, #112]
	stp	x20, x19, [sp, #128]
	stp	x29, x30, [sp, #144]
	add	x29, sp, #144
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	.cfi_offset w23, -56
	.cfi_offset w24, -64
	.cfi_remember_state
	bl	__RNvNtCs1SSuMAdGM58_3std9panicking9take_hook
	mov	x19, x0
	mov	x20, x1
	stp	x0, x1, [sp, #72]
	bl	__RNvCsdtSMxSA38aw_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #16
	mov	w1, #8
	bl	__RNvCsdtSMxSA38aw_7___rustc12___rust_alloc
	cbz	x0, LBB19_30
	stp	x19, x20, [x0]
Lloh58:
	adrp	x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.16@PAGE
Lloh59:
	add	x1, x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.16@PAGEOFF
	bl	__RNvNtCs1SSuMAdGM58_3std9panicking8set_hook
Lloh60:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.17@PAGE
Lloh61:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.17@PAGEOFF
Lloh62:
	adrp	x2, _anneal_unwind_bounce@GOTPAGE
Lloh63:
	ldr	x2, [x2, _anneal_unwind_bounce@GOTPAGEOFF]
	add	x8, sp, #72
	mov	w1, #15
	bl	__RNvCsle4UtX85Rrh_8specimen14image_identity
	ldr	x8, [sp, #72]
	cmn	x8, #1
	b.eq	LBB19_3
	ldur	q0, [sp, #80]
	str	q0, [sp, #16]
LBB19_3:
	cmn	x8, #1
	b.ne	LBB19_10
Lloh64:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.18@PAGE
Lloh65:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.18@PAGEOFF
Lloh66:
	adrp	x2, _anneal_rust_bounce@PAGE
Lloh67:
	add	x2, x2, _anneal_rust_bounce@PAGEOFF
	add	x8, sp, #72
	mov	w1, #11
	bl	__RNvCsle4UtX85Rrh_8specimen14image_identity
	ldr	x8, [sp, #72]
	cmn	x8, #1
	b.eq	LBB19_6
	ldur	q0, [sp, #80]
	str	q0, [sp, #16]
LBB19_6:
	cmn	x8, #1
	b.ne	LBB19_10
Lloh68:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.19@PAGE
Lloh69:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.19@PAGEOFF
Lloh70:
	adrp	x2, __Unwind_Backtrace@GOTPAGE
Lloh71:
	ldr	x2, [x2, __Unwind_Backtrace@GOTPAGEOFF]
	add	x8, sp, #72
	mov	w1, #17
	bl	__RNvCsle4UtX85Rrh_8specimen14image_identity
	ldr	x8, [sp, #72]
	cmn	x8, #1
	b.eq	LBB19_9
	ldur	q0, [sp, #80]
	str	q0, [sp, #16]
LBB19_9:
	cmn	x8, #1
	b.eq	LBB19_15
LBB19_10:
	ldr	q0, [sp, #16]
LBB19_11:
	str	q0, [sp]
	cmn	x8, #1
	b.eq	LBB19_28
LBB19_12:
	str	x8, [sp, #72]
	ldr	q0, [sp]
	stur	q0, [sp, #80]
	add	x8, sp, #72
Lloh72:
	adrp	x9, __RNvXsq_NtCs6zY7rJBZy9D_5alloc6stringNtB5_6StringNtNtCsjIpoRzUjyHQ_4core3fmt7Display3fmt@PAGE
Lloh73:
	add	x9, x9, __RNvXsq_NtCs6zY7rJBZy9D_5alloc6stringNtB5_6StringNtNtCsjIpoRzUjyHQ_4core3fmt7Display3fmt@PAGEOFF
	stp	x8, x9, [sp, #16]
Ltmp80:
Lloh74:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.21@PAGE
Lloh75:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.21@PAGEOFF
	add	x1, sp, #16
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio7__eprint
Ltmp81:
Ltmp86:
	add	x0, sp, #72
	bl	__RNvXsp_NtCs6zY7rJBZy9D_5alloc3vecINtB5_3VechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp87:
	add	x0, sp, #72
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
	mov	w0, #1
	b	LBB19_29
LBB19_15:
	mov	x19, #0
	mov	x20, #0
	mov	w8, #2
	stp	xzr, x8, [sp, #16]
	add	x8, sp, #16
	add	x21, x8, #16
	mov	w8, #1
	strh	w8, [sp, #32]
	add	x22, sp, #72
	b	LBB19_17
LBB19_16:
	cmn	x8, #1
	b.ne	LBB19_26
LBB19_17:
	cmp	x20, #2
	b.ne	LBB19_19
	mov	w23, #2
	b	LBB19_20
LBB19_19:
	add	x19, x20, #1
	ldrb	w23, [x21, x20]
	mov	x20, x19
LBB19_20:
	cmp	w23, #2
	b.eq	LBB19_27
	add	x8, sp, #72
	and	w0, w23, #0x1
	mov	w1, #0
	bl	__RNvCsle4UtX85Rrh_8specimen8run_case
	ldr	x8, [sp, #72]
	cmn	x8, #1
	b.eq	LBB19_23
	ldur	q0, [x22, #8]
	str	q0, [sp, #48]
LBB19_23:
	cmn	x8, #1
	b.ne	LBB19_26
	add	x8, sp, #72
	and	w0, w23, #0x1
	mov	w1, #1
	bl	__RNvCsle4UtX85Rrh_8specimen8run_case
	ldr	x8, [sp, #72]
	cmn	x8, #1
	b.eq	LBB19_16
	ldur	q0, [x22, #8]
	str	q0, [sp, #48]
	b	LBB19_16
LBB19_26:
	str	x19, [sp, #16]
	ldr	q0, [sp, #48]
	b	LBB19_11
LBB19_27:
	mov	x8, #-1
	cmn	x8, #1
	b.ne	LBB19_12
LBB19_28:
Lloh76:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.20@PAGE
Lloh77:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.20@PAGEOFF
	mov	w1, #45
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio6__print
	mov	w0, #0
LBB19_29:
	.cfi_def_cfa wsp, 160
	ldp	x29, x30, [sp, #144]
	ldp	x20, x19, [sp, #128]
	ldp	x22, x21, [sp, #112]
	ldp	x24, x23, [sp, #96]
	add	sp, sp, #160
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	ret
LBB19_30:
	.cfi_restore_state
Ltmp92:
	mov	w0, #8
	mov	w1, #16
	bl	__RNvNtCs6zY7rJBZy9D_5alloc5alloc18handle_alloc_error
Ltmp93:
	brk	#0x1
LBB19_32:
Ltmp88:
	mov	x19, x0
Ltmp89:
	add	x0, sp, #72
	bl	__RNvXs1_NtCs6zY7rJBZy9D_5alloc7raw_vecINtB5_6RawVechENtNtNtCsjIpoRzUjyHQ_4core3ops4drop4Drop4dropCsfhX9oYWaTAx_5gimli
Ltmp90:
	b	LBB19_37
LBB19_33:
Ltmp91:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
LBB19_34:
Ltmp82:
	mov	x19, x0
Ltmp83:
	add	x0, sp, #72
	bl	__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueNtNtCs6zY7rJBZy9D_5alloc6string6StringECsle4UtX85Rrh_8specimen
Ltmp84:
	b	LBB19_37
LBB19_35:
Ltmp85:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
LBB19_36:
Ltmp94:
	mov	x19, x0
Ltmp95:
	add	x0, sp, #72
	bl	__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueNCNvCsle4UtX85Rrh_8specimen3run0EBF_
Ltmp96:
LBB19_37:
	mov	x0, x19
	bl	__Unwind_Resume
LBB19_38:
Ltmp97:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
	.loh AdrpLdrGot	Lloh62, Lloh63
	.loh AdrpAdd	Lloh60, Lloh61
	.loh AdrpAdd	Lloh58, Lloh59
	.loh AdrpAdd	Lloh66, Lloh67
	.loh AdrpAdd	Lloh64, Lloh65
	.loh AdrpLdrGot	Lloh70, Lloh71
	.loh AdrpAdd	Lloh68, Lloh69
	.loh AdrpAdd	Lloh74, Lloh75
	.loh AdrpAdd	Lloh72, Lloh73
	.loh AdrpAdd	Lloh76, Lloh77
Lfunc_end8:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table19:
Lexception8:
	.byte	255
	.byte	155
	.uleb128 Lttbase4-Lttbaseref4
Lttbaseref4:
	.byte	1
	.uleb128 Lcst_end8-Lcst_begin8
Lcst_begin8:
	.uleb128 Lfunc_begin8-Lfunc_begin8
	.uleb128 Ltmp80-Lfunc_begin8
	.byte	0
	.byte	0
	.uleb128 Ltmp80-Lfunc_begin8
	.uleb128 Ltmp81-Ltmp80
	.uleb128 Ltmp82-Lfunc_begin8
	.byte	0
	.uleb128 Ltmp86-Lfunc_begin8
	.uleb128 Ltmp87-Ltmp86
	.uleb128 Ltmp88-Lfunc_begin8
	.byte	0
	.uleb128 Ltmp87-Lfunc_begin8
	.uleb128 Ltmp92-Ltmp87
	.byte	0
	.byte	0
	.uleb128 Ltmp92-Lfunc_begin8
	.uleb128 Ltmp93-Ltmp92
	.uleb128 Ltmp94-Lfunc_begin8
	.byte	0
	.uleb128 Ltmp89-Lfunc_begin8
	.uleb128 Ltmp90-Ltmp89
	.uleb128 Ltmp91-Lfunc_begin8
	.byte	1
	.uleb128 Ltmp83-Lfunc_begin8
	.uleb128 Ltmp84-Ltmp83
	.uleb128 Ltmp85-Lfunc_begin8
	.byte	1
	.uleb128 Ltmp95-Lfunc_begin8
	.uleb128 Ltmp96-Ltmp95
	.uleb128 Ltmp97-Lfunc_begin8
	.byte	1
	.uleb128 Ltmp96-Lfunc_begin8
	.uleb128 Lfunc_end8-Ltmp96
	.byte	0
	.byte	0
Lcst_end8:
	.byte	127
	.byte	0
	.p2align	2, 0x0
Lttbase4:
	.byte	0
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RNvCsle4UtX85Rrh_8specimen8run_case:
Lfunc_begin9:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception9
	stp	x28, x27, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x26, x25, [sp, #16]
	stp	x24, x23, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	stp	x29, x30, [sp, #80]
	add	x29, sp, #80
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	.cfi_offset w23, -56
	.cfi_offset w24, -64
	.cfi_offset w25, -72
	.cfi_offset w26, -80
	.cfi_offset w27, -88
	.cfi_offset w28, -96
	.cfi_remember_state
	sub	sp, sp, #752
	mov	x21, x1
	mov	x20, x0
	mov	x28, x8
	mov	x8, #0
	strb	w0, [sp, #6]
	add	x26, sp, #96
	strb	w1, [sp, #7]
	mov	w9, #5
	stp	xzr, x9, [sp, #96]
Lloh78:
	adrp	x11, __RNvCsle4UtX85Rrh_8specimen5CALLS@PAGE
Lloh79:
	add	x11, x11, __RNvCsle4UtX85Rrh_8specimen5CALLS@PAGEOFF
Lloh80:
	adrp	x10, __RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS@PAGE
Lloh81:
	add	x10, x10, __RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS@PAGEOFF
	add	x9, x26, #16
	stp	x11, x10, [sp, #112]
Lloh82:
	adrp	x24, __RNvCsle4UtX85Rrh_8specimen11OUTER_DROPS@PAGE
Lloh83:
	add	x24, x24, __RNvCsle4UtX85Rrh_8specimen11OUTER_DROPS@PAGEOFF
	str	x24, [sp, #128]
Lloh84:
	adrp	x25, __RNvCsle4UtX85Rrh_8specimen10DROP_ORDER@PAGE
Lloh85:
	add	x25, x25, __RNvCsle4UtX85Rrh_8specimen10DROP_ORDER@PAGEOFF
Lloh86:
	adrp	x10, __RNvCsle4UtX85Rrh_8specimen14EXPECTED_HOOKS@PAGE
Lloh87:
	add	x10, x10, __RNvCsle4UtX85Rrh_8specimen14EXPECTED_HOOKS@PAGEOFF
	stp	x25, x10, [x26, #40]
	cmp	x8, #5
	b.ne	LBB20_2
LBB20_1:
	mov	x10, #0
	cbnz	x10, LBB20_3
	b	LBB20_4
LBB20_2:
	ldr	x10, [x9, x8, lsl #3]
	add	x8, x8, #1
	cbz	x10, LBB20_4
LBB20_3:
	stlr	xzr, [x10]
	cmp	x8, #5
	b.ne	LBB20_2
	b	LBB20_1
LBB20_4:
Lloh88:
	adrp	x0, __RNvNCNKNvCsle4UtX85Rrh_8specimen10LAST_TRACE0s_023___RUST_STD_INTERNAL_VAL@TLVPPAGE
Lloh89:
	ldr	x0, [x0, __RNvNCNKNvCsle4UtX85Rrh_8specimen10LAST_TRACE0s_023___RUST_STD_INTERNAL_VAL@TLVPPAGEOFF]
	ldr	x8, [x0]
	blr	x8
	ldr	x8, [x0]
	cbnz	x8, LBB20_44
	mov	x22, x0
	mov	x8, #-1
	str	x8, [x0], #8
	mov	w1, #520
	bl	_bzero
	mov	w8, #-1
	str	w8, [x22, #528]
	strb	wzr, [x22, #532]
	str	xzr, [x22]
Lloh90:
	adrp	x8, __RNvCsle4UtX85Rrh_8specimen15normal_callback@PAGE
Lloh91:
	add	x8, x8, __RNvCsle4UtX85Rrh_8specimen15normal_callback@PAGEOFF
Lloh92:
	adrp	x9, __RNvCsle4UtX85Rrh_8specimen14panic_callback@PAGE
Lloh93:
	add	x9, x9, __RNvCsle4UtX85Rrh_8specimen14panic_callback@PAGEOFF
	cmp	w21, #0
	csel	x8, x9, x8, ne
	str	x8, [sp, #96]
	add	x8, sp, #96
	; InlineAsm Start
	; InlineAsm End
	ldr	x0, [sp, #96]
	str	x0, [sp, #8]
	ldrb	w8, [sp, #6]
	cbz	w8, LBB20_7
Ltmp100:
	mov	x1, #30600
	movk	x1, #21862, lsl #16
	movk	x1, #13124, lsl #32
	movk	x1, #4386, lsl #48
	bl	_anneal_rust_bounce
Ltmp101:
	b	LBB20_8
LBB20_7:
Ltmp98:
	mov	x1, #30600
	movk	x1, #21862, lsl #16
	movk	x1, #13124, lsl #32
	movk	x1, #4386, lsl #48
	bl	_anneal_unwind_bounce
Ltmp99:
LBB20_8:
	mov	x23, x0
	mov	w8, #0
	mov	w9, #1
	mov	x19, x24
	ldaddal	x9, x9, [x24]
	ldar	x9, [x25]
	mov	w10, #10
	mov	x11, #2
	madd	x9, x9, x10, x11
	mov	x27, x25
	stlr	x9, [x25]
	add	x1, sp, #8
LBB20_9:
	cmp	w8, #0
	csel	x25, x23, xzr, ne
	csel	x24, x1, x23, ne
	tbz	w21, #0, LBB20_21
	cbz	x25, LBB20_36
	str	w20, [sp]
	mov	x20, x28
	str	x25, [x26, #560]
	str	x24, [x26, #568]
	mov	w28, #1
	ldr	x9, [x24, #24]
Ltmp113:
	add	x8, sp, #96
	mov	x0, x23
	blr	x9
Ltmp114:
	ldp	x8, x9, [sp, #96]
	mov	x10, #22594
	movk	x10, #50467, lsl #16
	movk	x10, #60122, lsl #32
	movk	x10, #4629, lsl #48
	eor	x9, x9, x10
	mov	x10, #30253
	movk	x10, #51344, lsl #16
	movk	x10, #1343, lsl #32
	movk	x10, #21237, lsl #48
	eor	x8, x8, x10
	orr	x8, x8, x9
	cbnz	x8, LBB20_48
	ldr	x8, [x23]
	mov	x9, #22340
	movk	x9, #21838, lsl #16
	movk	x9, #12383, lsl #32
	movk	x9, #17716, lsl #48
	cmp	x8, x9
	b.ne	LBB20_48
	ldr	x8, [x23, #8]
	mov	x9, #30600
	movk	x9, #21862, lsl #16
	movk	x9, #13124, lsl #32
	movk	x9, #4386, lsl #48
	cmp	x8, x9
	b.ne	LBB20_48
	add	x8, sp, #6
Lloh94:
	adrp	x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGE
Lloh95:
	add	x9, x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGEOFF
	stp	x8, x9, [sp, #96]
Lloh96:
	adrp	x8, l_anon.9da64be1d17a499d89cdacccc8d87f3d.27@PAGE
Lloh97:
	add	x8, x8, l_anon.9da64be1d17a499d89cdacccc8d87f3d.27@PAGEOFF
Lloh98:
	adrp	x9, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGE
Lloh99:
	ldr	x9, [x9, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGEOFF]
	stp	x8, x9, [sp, #112]
Lloh100:
	adrp	x8, l_anon.9da64be1d17a499d89cdacccc8d87f3d.28@PAGE
Lloh101:
	add	x8, x8, l_anon.9da64be1d17a499d89cdacccc8d87f3d.28@PAGEOFF
	str	x8, [sp, #128]
	str	x9, [x26, #40]
Ltmp119:
Lloh102:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.29@PAGE
Lloh103:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.29@PAGEOFF
	add	x1, sp, #96
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio6__print
Ltmp120:
	ldr	x8, [x24]
	cbz	x8, LBB20_18
Ltmp125:
	mov	x0, x23
	blr	x8
Ltmp126:
LBB20_18:
	ldr	x1, [x24, #8]
	mov	x28, x20
	cbz	x1, LBB20_20
	ldr	x2, [x24, #16]
	mov	x0, x25
	bl	__RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc
LBB20_20:
	ldr	w20, [sp]
	b	LBB20_24
LBB20_21:
	cbnz	x25, LBB20_50
	str	x24, [sp, #56]
	mov	x8, #26265
	movk	x8, #51, lsl #16
	movk	x8, #39373, lsl #32
	movk	x8, #13158, lsl #48
	str	x8, [x26, #560]
	cmp	x24, x8
	b.ne	LBB20_26
	add	x8, sp, #6
Lloh104:
	adrp	x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGE
Lloh105:
	add	x9, x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGEOFF
	stp	x8, x9, [sp, #96]
	add	x8, sp, #56
Lloh106:
	adrp	x9, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGE
Lloh107:
	ldr	x9, [x9, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGEOFF]
	stp	x8, x9, [sp, #112]
Lloh108:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.22@PAGE
Lloh109:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.22@PAGEOFF
	add	x1, sp, #96
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio6__print
LBB20_24:
Lloh110:
	adrp	x8, __RNvCsle4UtX85Rrh_8specimen5CALLS@PAGE
Lloh111:
	add	x8, x8, __RNvCsle4UtX85Rrh_8specimen5CALLS@PAGEOFF
	ldar	x8, [x8]
Lloh112:
	adrp	x9, __RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS@PAGE
Lloh113:
	add	x9, x9, __RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS@PAGEOFF
	ldar	x9, [x9]
	ldar	x10, [x19]
	ldar	x11, [x27]
Lloh114:
	adrp	x12, __RNvCsle4UtX85Rrh_8specimen14EXPECTED_HOOKS@PAGE
Lloh115:
	add	x12, x12, __RNvCsle4UtX85Rrh_8specimen14EXPECTED_HOOKS@PAGEOFF
	ldar	x12, [x12]
	stp	x8, x9, [sp, #16]
	stp	x10, x11, [sp, #32]
	mov	w13, w21
	mov	w14, #1
	stp	x12, x14, [sp, #48]
	stp	x14, x14, [sp, #64]
	mov	w15, #12
	stp	x15, x13, [sp, #80]
	cmp	x8, #1
	ccmp	x9, #1, #0, eq
	ccmp	x10, #1, #0, eq
	ccmp	x11, #12, #0, eq
	ccmp	x12, x13, #0, eq
	b.eq	LBB20_27
	add	x8, sp, #6
Lloh116:
	adrp	x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGE
Lloh117:
	add	x9, x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGEOFF
	stp	x8, x9, [sp, #96]
Lloh118:
	adrp	x8, __RNvXsa_NtCsjIpoRzUjyHQ_4core5arrayAjj5_NtNtB7_3fmt5Debug3fmtCsle4UtX85Rrh_8specimen@PAGE
Lloh119:
	add	x8, x8, __RNvXsa_NtCsjIpoRzUjyHQ_4core5arrayAjj5_NtNtB7_3fmt5Debug3fmtCsle4UtX85Rrh_8specimen@PAGEOFF
	add	x9, sp, #16
	stp	x9, x8, [sp, #112]
	add	x9, sp, #56
	str	x9, [sp, #128]
	str	x8, [x26, #40]
Lloh120:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.34@PAGE
Lloh121:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.34@PAGEOFF
	add	x1, sp, #96
	b	LBB20_39
LBB20_26:
	add	x8, sp, #6
Lloh122:
	adrp	x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGE
Lloh123:
	add	x9, x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGEOFF
	stp	x8, x9, [sp, #96]
Lloh124:
	adrp	x8, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGE
Lloh125:
	ldr	x8, [x8, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGEOFF]
	add	x9, sp, #56
	stp	x9, x8, [sp, #112]
	sub	x9, x29, #176
	str	x9, [sp, #128]
	str	x8, [x26, #40]
Lloh126:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.23@PAGE
Lloh127:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.23@PAGEOFF
	add	x1, sp, #96
	b	LBB20_39
LBB20_27:
	ldr	x8, [x22]
	mov	x9, #9223372036854775807
	cmp	x8, x9
	b.hs	LBB20_45
	ldrb	w21, [x22, #532]
	str	x8, [x22]
	cmp	w21, #2
	b.eq	LBB20_46
	add	x23, x22, #533
	add	x19, sp, #96
	add	x0, sp, #96
	add	x1, x22, #8
	mov	w2, #524
	bl	_memcpy
	strb	w21, [sp, #620]
	add	x8, x19, #525
	ldrh	w9, [x23]
	strh	w9, [x8]
	ldrb	w8, [x22, #535]
	strb	w8, [sp, #623]
	tbnz	w21, #0, LBB20_37
	ldr	x1, [x26, #512]
	cbz	x1, LBB20_37
	ldr	w8, [x26, #520]
	cmp	w8, #5
	b.eq	LBB20_33
	cbnz	w8, LBB20_37
LBB20_33:
	cmp	x1, #65
	b.hs	LBB20_47
	add	x8, sp, #96
	str	x8, [x26, #528]
	str	x1, [x26, #536]
	cbz	w20, LBB20_41
LBB20_35:
	add	x8, sp, #96
	add	x8, x8, #520
	add	x9, sp, #6
	str	x9, [x26, #560]
Lloh128:
	adrp	x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGE
Lloh129:
	add	x9, x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGEOFF
	str	x9, [x26, #568]
	add	x9, sp, #7
	str	x9, [x26, #576]
Lloh130:
	adrp	x9, __RNvXsg_NtCsjIpoRzUjyHQ_4core3fmtbNtB5_7Display3fmt@GOTPAGE
Lloh131:
	ldr	x9, [x9, __RNvXsg_NtCsjIpoRzUjyHQ_4core3fmtbNtB5_7Display3fmt@GOTPAGEOFF]
	str	x9, [x26, #584]
	add	x9, sp, #16
	str	x9, [x26, #592]
Lloh132:
	adrp	x9, __RNvXsa_NtCsjIpoRzUjyHQ_4core5arrayAjj5_NtNtB7_3fmt5Debug3fmtCsle4UtX85Rrh_8specimen@PAGE
Lloh133:
	add	x9, x9, __RNvXsa_NtCsjIpoRzUjyHQ_4core5arrayAjj5_NtNtB7_3fmt5Debug3fmtCsle4UtX85Rrh_8specimen@PAGEOFF
	str	x9, [x26, #600]
	str	x8, [x26, #608]
Lloh134:
	adrp	x8, __RNvXs9_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3implNtB9_7Display3fmt@GOTPAGE
Lloh135:
	ldr	x8, [x8, __RNvXs9_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3implNtB9_7Display3fmt@GOTPAGEOFF]
	str	x8, [x26, #616]
	sub	x8, x29, #208
	str	x8, [x26, #624]
Lloh136:
	adrp	x8, __RNvXs1g_NtCsjIpoRzUjyHQ_4core3fmtRSjNtB6_5Debug3fmtCsle4UtX85Rrh_8specimen@PAGE
Lloh137:
	add	x8, x8, __RNvXs1g_NtCsjIpoRzUjyHQ_4core3fmtRSjNtB6_5Debug3fmtCsle4UtX85Rrh_8specimen@PAGEOFF
	str	x8, [x26, #632]
Lloh138:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.31@PAGE
Lloh139:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.31@PAGEOFF
	sub	x1, x29, #176
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio6__print
	mov	x8, #-1
	str	x8, [x28]
	b	LBB20_40
LBB20_36:
	add	x8, sp, #6
Lloh140:
	adrp	x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGE
Lloh141:
	add	x9, x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGEOFF
	stp	x8, x9, [sp, #96]
Lloh142:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.25@PAGE
Lloh143:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.25@PAGEOFF
	add	x1, sp, #96
	b	LBB20_39
LBB20_37:
	add	x8, x19, #524
	add	x9, x19, #520
	add	x10, x19, #512
	add	x11, sp, #6
	str	x11, [x26, #560]
Lloh144:
	adrp	x11, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGE
Lloh145:
	add	x11, x11, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGEOFF
	str	x11, [x26, #568]
	str	x9, [x26, #576]
Lloh146:
	adrp	x9, __RNvXs9_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3implNtB9_7Display3fmt@GOTPAGE
Lloh147:
	ldr	x9, [x9, __RNvXs9_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3implNtB9_7Display3fmt@GOTPAGEOFF]
	str	x9, [x26, #584]
Lloh148:
	adrp	x9, __RNvXsi_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impjNtB9_7Display3fmt@GOTPAGE
Lloh149:
	ldr	x9, [x9, __RNvXsi_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impjNtB9_7Display3fmt@GOTPAGEOFF]
	str	x10, [x26, #592]
	str	x9, [x26, #600]
	str	x8, [x26, #608]
Lloh150:
	adrp	x8, __RNvXsg_NtCsjIpoRzUjyHQ_4core3fmtbNtB5_7Display3fmt@GOTPAGE
Lloh151:
	ldr	x8, [x8, __RNvXsg_NtCsjIpoRzUjyHQ_4core3fmtbNtB5_7Display3fmt@GOTPAGEOFF]
	str	x8, [x26, #616]
Lloh152:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.33@PAGE
Lloh153:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.33@PAGEOFF
LBB20_38:
	sub	x1, x29, #176
LBB20_39:
	mov	x8, x28
	bl	__RNvNvNtCs6zY7rJBZy9D_5alloc3fmt6format12format_inner
LBB20_40:
	add	sp, sp, #752
	.cfi_def_cfa wsp, 96
	ldp	x29, x30, [sp, #80]
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldp	x24, x23, [sp, #32]
	ldp	x26, x25, [sp, #16]
	ldp	x28, x27, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	ret
LBB20_41:
	.cfi_restore_state
Lloh154:
	adrp	x8, _anneal_unwind_bounce@GOTPAGE
Lloh155:
	ldr	x8, [x8, _anneal_unwind_bounce@GOTPAGEOFF]
	str	x8, [x26, #544]
Lloh156:
	adrp	x9, _anneal_unwind_bounce_end@GOTPAGE
Lloh157:
	ldr	x9, [x9, _anneal_unwind_bounce_end@GOTPAGEOFF]
	str	x9, [x26, #552]
	subs	x9, x9, x8
	mov	w10, #32
	ccmp	x9, x10, #0, hs
	b.ne	LBB20_43
	add	x8, x8, #20
	str	x8, [x26, #560]
	add	x0, sp, #96
	sub	x2, x29, #176
	bl	__RNvMNtCsjIpoRzUjyHQ_4core5sliceSj8containsCsle4UtX85Rrh_8specimen
	cbnz	w0, LBB20_35
LBB20_43:
	sub	x8, x29, #192
	str	x8, [x26, #560]
Lloh158:
	adrp	x8, __RNvXs6_NtNtCsjIpoRzUjyHQ_4core3fmt3numjNtB7_8LowerHex3fmt@GOTPAGE
Lloh159:
	ldr	x8, [x8, __RNvXs6_NtNtCsjIpoRzUjyHQ_4core3fmt3numjNtB7_8LowerHex3fmt@GOTPAGEOFF]
	str	x8, [x26, #568]
	sub	x9, x29, #184
	str	x9, [x26, #576]
	str	x8, [x26, #584]
Lloh160:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.32@PAGE
Lloh161:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.32@PAGEOFF
	b	LBB20_38
LBB20_44:
Lloh162:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.10@PAGE
Lloh163:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.10@PAGEOFF
	bl	__RNvNtCsjIpoRzUjyHQ_4core4cell22panic_already_borrowed
LBB20_45:
Lloh164:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.11@PAGE
Lloh165:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.11@PAGEOFF
	bl	__RNvNtCsjIpoRzUjyHQ_4core4cell30panic_already_mutably_borrowed
LBB20_46:
Lloh166:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.2@PAGE
Lloh167:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.2@PAGEOFF
	bl	__RNvNtNtCs1SSuMAdGM58_3std6thread5local18panic_access_error
LBB20_47:
Lloh168:
	adrp	x3, l_anon.9da64be1d17a499d89cdacccc8d87f3d.30@PAGE
Lloh169:
	add	x3, x3, l_anon.9da64be1d17a499d89cdacccc8d87f3d.30@PAGEOFF
	mov	x0, #0
	mov	w2, #64
	bl	__RNvNtNtCsjIpoRzUjyHQ_4core5slice5index16slice_index_fail
LBB20_48:
	add	x8, sp, #6
Lloh170:
	adrp	x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGE
Lloh171:
	add	x9, x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGEOFF
	stp	x8, x9, [sp, #96]
Ltmp115:
Lloh172:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.26@PAGE
Lloh173:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.26@PAGEOFF
	add	x1, sp, #96
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio7__eprint
Ltmp116:
Ltmp117:
	mov	w28, #0
	mov	x0, x23
	mov	x1, x24
	bl	__RNvNtCs1SSuMAdGM58_3std5panic13resume_unwind
Ltmp118:
	b	LBB20_52
LBB20_50:
	str	x25, [x26, #560]
	str	x24, [x26, #568]
	add	x8, sp, #6
Lloh174:
	adrp	x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGE
Lloh175:
	add	x9, x9, __RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt@PAGEOFF
	stp	x8, x9, [sp, #96]
	mov	w20, #1
Ltmp106:
Lloh176:
	adrp	x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.24@PAGE
Lloh177:
	add	x0, x0, l_anon.9da64be1d17a499d89cdacccc8d87f3d.24@PAGEOFF
	add	x1, sp, #96
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio7__eprint
Ltmp107:
Ltmp108:
	mov	w20, #0
	mov	x0, x23
	mov	x1, x24
	bl	__RNvNtCs1SSuMAdGM58_3std5panic13resume_unwind
Ltmp109:
LBB20_52:
	brk	#0x1
LBB20_53:
Ltmp127:
	mov	x19, x0
	ldr	x1, [x24, #8]
	cbz	x1, LBB20_62
	ldr	x2, [x24, #16]
	mov	x0, x25
	bl	__RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc
	mov	x0, x19
	bl	__Unwind_Resume
LBB20_55:
Ltmp110:
	mov	x19, x0
	tbz	w20, #0, LBB20_62
Ltmp111:
	sub	x0, x29, #176
	bl	__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EECsle4UtX85Rrh_8specimen
Ltmp112:
	b	LBB20_62
LBB20_57:
Ltmp102:
	mov	w8, #1
	mov	x19, x24
	ldaddal	x8, x8, [x24]
	ldar	x8, [x25]
	mov	w9, #10
	mov	x10, #2
	madd	x8, x8, x9, x10
	mov	x27, x25
	stlr	x8, [x25]
Ltmp103:
	bl	__RNvNvNtCs1SSuMAdGM58_3std9panicking12catch_unwind7cleanup
Ltmp104:
	mov	x23, x0
	mov	w8, #1
	b	LBB20_9
LBB20_59:
Ltmp105:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking19panic_cannot_unwind
LBB20_60:
Ltmp121:
	mov	x19, x0
	tbz	w28, #0, LBB20_62
Ltmp122:
	sub	x0, x29, #176
	bl	__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EECsle4UtX85Rrh_8specimen
Ltmp123:
LBB20_62:
	mov	x0, x19
	bl	__Unwind_Resume
LBB20_63:
Ltmp124:
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup
	.loh AdrpAdd	Lloh86, Lloh87
	.loh AdrpAdd	Lloh84, Lloh85
	.loh AdrpAdd	Lloh82, Lloh83
	.loh AdrpAdd	Lloh80, Lloh81
	.loh AdrpAdd	Lloh78, Lloh79
	.loh AdrpLdr	Lloh88, Lloh89
	.loh AdrpAdd	Lloh92, Lloh93
	.loh AdrpAdd	Lloh90, Lloh91
	.loh AdrpAdd	Lloh102, Lloh103
	.loh AdrpAdd	Lloh100, Lloh101
	.loh AdrpLdrGot	Lloh98, Lloh99
	.loh AdrpAdd	Lloh96, Lloh97
	.loh AdrpAdd	Lloh94, Lloh95
	.loh AdrpAdd	Lloh108, Lloh109
	.loh AdrpLdrGot	Lloh106, Lloh107
	.loh AdrpAdd	Lloh104, Lloh105
	.loh AdrpAdd	Lloh114, Lloh115
	.loh AdrpAdd	Lloh112, Lloh113
	.loh AdrpAdd	Lloh110, Lloh111
	.loh AdrpAdd	Lloh120, Lloh121
	.loh AdrpAdd	Lloh118, Lloh119
	.loh AdrpAdd	Lloh116, Lloh117
	.loh AdrpAdd	Lloh126, Lloh127
	.loh AdrpLdrGot	Lloh124, Lloh125
	.loh AdrpAdd	Lloh122, Lloh123
	.loh AdrpAdd	Lloh138, Lloh139
	.loh AdrpAdd	Lloh136, Lloh137
	.loh AdrpLdrGot	Lloh134, Lloh135
	.loh AdrpAdd	Lloh132, Lloh133
	.loh AdrpLdrGot	Lloh130, Lloh131
	.loh AdrpAdd	Lloh128, Lloh129
	.loh AdrpAdd	Lloh142, Lloh143
	.loh AdrpAdd	Lloh140, Lloh141
	.loh AdrpAdd	Lloh152, Lloh153
	.loh AdrpLdrGot	Lloh150, Lloh151
	.loh AdrpLdrGot	Lloh148, Lloh149
	.loh AdrpLdrGot	Lloh146, Lloh147
	.loh AdrpAdd	Lloh144, Lloh145
	.loh AdrpLdrGot	Lloh156, Lloh157
	.loh AdrpLdrGot	Lloh154, Lloh155
	.loh AdrpAdd	Lloh160, Lloh161
	.loh AdrpLdrGot	Lloh158, Lloh159
	.loh AdrpAdd	Lloh162, Lloh163
	.loh AdrpAdd	Lloh164, Lloh165
	.loh AdrpAdd	Lloh166, Lloh167
	.loh AdrpAdd	Lloh168, Lloh169
	.loh AdrpAdd	Lloh172, Lloh173
	.loh AdrpAdd	Lloh170, Lloh171
	.loh AdrpAdd	Lloh176, Lloh177
	.loh AdrpAdd	Lloh174, Lloh175
Lfunc_end9:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table20:
Lexception9:
	.byte	255
	.byte	155
	.uleb128 Lttbase5-Lttbaseref5
Lttbaseref5:
	.byte	1
	.uleb128 Lcst_end9-Lcst_begin9
Lcst_begin9:
	.uleb128 Lfunc_begin9-Lfunc_begin9
	.uleb128 Ltmp100-Lfunc_begin9
	.byte	0
	.byte	0
	.uleb128 Ltmp100-Lfunc_begin9
	.uleb128 Ltmp99-Ltmp100
	.uleb128 Ltmp102-Lfunc_begin9
	.byte	5
	.uleb128 Ltmp113-Lfunc_begin9
	.uleb128 Ltmp120-Ltmp113
	.uleb128 Ltmp121-Lfunc_begin9
	.byte	0
	.uleb128 Ltmp125-Lfunc_begin9
	.uleb128 Ltmp126-Ltmp125
	.uleb128 Ltmp127-Lfunc_begin9
	.byte	0
	.uleb128 Ltmp126-Lfunc_begin9
	.uleb128 Ltmp115-Ltmp126
	.byte	0
	.byte	0
	.uleb128 Ltmp115-Lfunc_begin9
	.uleb128 Ltmp118-Ltmp115
	.uleb128 Ltmp121-Lfunc_begin9
	.byte	0
	.uleb128 Ltmp106-Lfunc_begin9
	.uleb128 Ltmp109-Ltmp106
	.uleb128 Ltmp110-Lfunc_begin9
	.byte	0
	.uleb128 Ltmp109-Lfunc_begin9
	.uleb128 Ltmp111-Ltmp109
	.byte	0
	.byte	0
	.uleb128 Ltmp111-Lfunc_begin9
	.uleb128 Ltmp112-Ltmp111
	.uleb128 Ltmp124-Lfunc_begin9
	.byte	1
	.uleb128 Ltmp103-Lfunc_begin9
	.uleb128 Ltmp104-Ltmp103
	.uleb128 Ltmp105-Lfunc_begin9
	.byte	1
	.uleb128 Ltmp122-Lfunc_begin9
	.uleb128 Ltmp123-Ltmp122
	.uleb128 Ltmp124-Lfunc_begin9
	.byte	1
	.uleb128 Ltmp123-Lfunc_begin9
	.uleb128 Lfunc_end9-Ltmp123
	.byte	0
	.byte	0
Lcst_end9:
	.byte	127
	.byte	0
	.byte	0
	.byte	0
	.byte	1
	.byte	125
	.p2align	2, 0x0
	.long	0
Lttbase5:
	.byte	0
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RNvMNtCsjIpoRzUjyHQ_4core5sliceSj8containsCsle4UtX85Rrh_8specimen:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	ldr	x8, [x2]
	ands	x9, x1, #0xffffffffffffff8
	b.eq	LBB21_4
	and	x10, x1, #0xfffffffffffffff8
	neg	x10, x10
	mov	x11, x0
LBB21_2:
	ldp	x12, x13, [x11]
	ldp	x14, x15, [x11, #16]
	ldp	x16, x17, [x11, #32]
	ldp	x2, x3, [x11, #48]
	cmp	x12, x8
	ccmp	x13, x8, #4, ne
	ccmp	x14, x8, #4, ne
	ccmp	x15, x8, #4, ne
	ccmp	x16, x8, #4, ne
	ccmp	x17, x8, #4, ne
	ccmp	x2, x8, #4, ne
	ccmp	x3, x8, #4, ne
	b.eq	LBB21_18
	add	x11, x11, #64
	adds	x10, x10, #8
	b.ne	LBB21_2
LBB21_4:
	ubfiz	x10, x1, #3, #3
	cbz	x10, LBB21_10
	add	x11, x0, x9, lsl #3
	sub	x12, x10, #8
	lsr	w9, w12, #3
	add	w9, w9, #1
	ands	x13, x9, #0x3
	b.eq	LBB21_11
	mov	x9, x11
LBB21_7:
	ldr	x14, [x9], #8
	cmp	x14, x8
	b.eq	LBB21_18
	subs	x13, x13, #1
	b.ne	LBB21_7
	cmp	x12, #24
	b.hs	LBB21_12
LBB21_10:
	mov	w0, #0
	b	LBB21_19
LBB21_11:
	mov	x9, x11
	cmp	x12, #24
	b.lo	LBB21_10
LBB21_12:
	add	x10, x11, x10
LBB21_13:
	ldr	x11, [x9]
	cmp	x11, x8
	b.eq	LBB21_18
	ldr	x11, [x9, #8]
	cmp	x11, x8
	b.eq	LBB21_18
	ldr	x11, [x9, #16]
	cmp	x11, x8
	b.eq	LBB21_18
	ldr	x11, [x9, #24]
	cmp	x11, x8
	b.eq	LBB21_18
	mov	w0, #0
	add	x9, x9, #32
	cmp	x9, x10
	b.ne	LBB21_13
	b	LBB21_19
LBB21_18:
	mov	w0, #1
LBB21_19:
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.p2align	2
__RNvXNtCsjIpoRzUjyHQ_4core3anyNtCsle4UtX85Rrh_8specimen13ExpectedPanicNtB2_3Any7type_idBt_:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
Lloh178:
	adrp	x9, l_anon.9da64be1d17a499d89cdacccc8d87f3d.0@PAGE
Lloh179:
	add	x9, x9, l_anon.9da64be1d17a499d89cdacccc8d87f3d.0@PAGEOFF
Lloh180:
	ldr	q0, [x9]
	str	q0, [x8]
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.loh AdrpAddLdr	Lloh178, Lloh179, Lloh180
	.cfi_endproc

	.p2align	2
__RNvXNvNtCs1SSuMAdGM58_3std9panicking11begin_panicINtB2_7PayloadNtCsle4UtX85Rrh_8specimen13ExpectedPanicENtNtCsjIpoRzUjyHQ_4core5panic12PanicPayload3getB11_:
	.cfi_startproc
	ldr	x8, [x0], #8
	cbz	x8, LBB23_2
Lloh181:
	adrp	x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.35@PAGE
Lloh182:
	add	x1, x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.35@PAGEOFF
	ret
LBB23_2:
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	bl	__RNvNtCs1SSuMAdGM58_3std7process5abort
	.loh AdrpAdd	Lloh181, Lloh182
	.cfi_endproc

	.p2align	2
__RNvXNvNtCs1SSuMAdGM58_3std9panicking11begin_panicINtB2_7PayloadNtCsle4UtX85Rrh_8specimen13ExpectedPanicENtNtCsjIpoRzUjyHQ_4core5panic12PanicPayload8take_boxB11_:
	.cfi_startproc
	stp	x20, x19, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_remember_state
	ldp	x8, x19, [x0]
	ldr	x20, [x0, #16]
	str	xzr, [x0]
	cmp	x8, #1
	b.ne	LBB24_3
	bl	__RNvCsdtSMxSA38aw_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #16
	mov	w1, #8
	bl	__RNvCsdtSMxSA38aw_7___rustc12___rust_alloc
	cbz	x0, LBB24_4
	stp	x19, x20, [x0]
Lloh183:
	adrp	x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.35@PAGE
Lloh184:
	add	x1, x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.35@PAGEOFF
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
LBB24_3:
	.cfi_restore_state
	bl	__RNvNtCs1SSuMAdGM58_3std7process5abort
LBB24_4:
	mov	w0, #8
	mov	w1, #16
	bl	__RNvNtCs6zY7rJBZy9D_5alloc5alloc18handle_alloc_error
	.loh AdrpAdd	Lloh183, Lloh184
	.cfi_endproc

	.p2align	2
__RNvXs1g_NtCsjIpoRzUjyHQ_4core3fmtRSjNtB6_5Debug3fmtCsle4UtX85Rrh_8specimen:
	.cfi_startproc
	sub	sp, sp, #80
	.cfi_def_cfa_offset 80
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	stp	x29, x30, [sp, #64]
	add	x29, sp, #64
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	ldp	x20, x19, [x0]
	add	x8, sp, #8
	mov	x0, x1
	bl	__RNvMsa_NtCsjIpoRzUjyHQ_4core3fmtNtB5_9Formatter10debug_list
	cbz	x19, LBB25_3
	lsl	x21, x19, #3
Lloh185:
	adrp	x19, l_anon.9da64be1d17a499d89cdacccc8d87f3d.3@PAGE
Lloh186:
	add	x19, x19, l_anon.9da64be1d17a499d89cdacccc8d87f3d.3@PAGEOFF
LBB25_2:
	str	x20, [sp, #24]
	add	x20, x20, #8
	add	x0, sp, #8
	add	x1, sp, #24
	mov	x2, x19
	bl	__RNvMs6_NtNtCsjIpoRzUjyHQ_4core3fmt8buildersNtB5_9DebugList5entry
	subs	x21, x21, #8
	b.ne	LBB25_2
LBB25_3:
	add	x0, sp, #8
	bl	__RNvMs6_NtNtCsjIpoRzUjyHQ_4core3fmt8buildersNtB5_9DebugList6finish
	.cfi_def_cfa wsp, 80
	ldp	x29, x30, [sp, #64]
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	ret
	.loh AdrpAdd	Lloh185, Lloh186
	.cfi_endproc

	.p2align	2
__RNvXs1g_NtCsjIpoRzUjyHQ_4core3fmtRjNtB6_5Debug3fmtCsle4UtX85Rrh_8specimen:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_remember_state
	ldr	x0, [x0]
	ldr	w8, [x1, #16]
	tbnz	w8, #25, LBB26_3
	tbnz	w8, #26, LBB26_4
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	b	__RNvXsi_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impjNtB9_7Display3fmt
LBB26_3:
	.cfi_restore_state
	.cfi_remember_state
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	b	__RNvXs6_NtNtCsjIpoRzUjyHQ_4core3fmt3numjNtB7_8LowerHex3fmt
LBB26_4:
	.cfi_restore_state
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	b	__RNvXs8_NtNtCsjIpoRzUjyHQ_4core3fmt3numjNtB7_8UpperHex3fmt
	.cfi_endproc

	.p2align	2
__RNvXs_NvNtCs1SSuMAdGM58_3std9panicking11begin_panicINtB4_7PayloadNtCsle4UtX85Rrh_8specimen13ExpectedPanicENtNtCsjIpoRzUjyHQ_4core3fmt7Display3fmtB13_:
	.cfi_startproc
	stp	x20, x19, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_remember_state
	ldr	x8, [x0], #8
	cbz	x8, LBB27_2
	mov	x19, x1
Lloh187:
	adrp	x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.35@PAGE
Lloh188:
	add	x1, x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.35@PAGEOFF
	bl	__RNvNtCs1SSuMAdGM58_3std9panicking14payload_as_str
	mov	x2, x0
	mov	x3, x1
	mov	x0, x19
	mov	x1, x2
	mov	x2, x3
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	b	__RNvMsa_NtCsjIpoRzUjyHQ_4core3fmtNtB5_9Formatter9write_str
LBB27_2:
	.cfi_restore_state
	bl	__RNvNtCs1SSuMAdGM58_3std7process5abort
	.loh AdrpAdd	Lloh187, Lloh188
	.cfi_endproc

	.p2align	2
__RNvXsa_Csle4UtX85Rrh_8specimenNtB5_4PathNtNtCsjIpoRzUjyHQ_4core3fmt5Debug3fmt:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x1
	ldrb	w9, [x0]
	cmp	w9, #0
	mov	w9, #8
	mov	w10, #4
	csel	x2, x10, x9, ne
Lloh189:
	adrp	x9, l_anon.9da64be1d17a499d89cdacccc8d87f3d.36@PAGE
Lloh190:
	add	x9, x9, l_anon.9da64be1d17a499d89cdacccc8d87f3d.36@PAGEOFF
Lloh191:
	adrp	x10, l_anon.9da64be1d17a499d89cdacccc8d87f3d.37@PAGE
Lloh192:
	add	x10, x10, l_anon.9da64be1d17a499d89cdacccc8d87f3d.37@PAGEOFF
	csel	x1, x10, x9, ne
	mov	x0, x8
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	b	__RNvMsa_NtCsjIpoRzUjyHQ_4core3fmtNtB5_9Formatter9write_str
	.loh AdrpAdd	Lloh191, Lloh192
	.loh AdrpAdd	Lloh189, Lloh190
	.cfi_endproc

	.p2align	2
__RNvXsa_NtCsjIpoRzUjyHQ_4core5arrayAjj5_NtNtB7_3fmt5Debug3fmtCsle4UtX85Rrh_8specimen:
	.cfi_startproc
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	stp	x20, x19, [sp, #32]
	stp	x29, x30, [sp, #48]
	add	x29, sp, #48
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	mov	x19, x0
	add	x8, sp, #8
	mov	x0, x1
	bl	__RNvMsa_NtCsjIpoRzUjyHQ_4core3fmtNtB5_9Formatter10debug_list
	str	x19, [sp, #24]
Lloh193:
	adrp	x20, l_anon.9da64be1d17a499d89cdacccc8d87f3d.3@PAGE
Lloh194:
	add	x20, x20, l_anon.9da64be1d17a499d89cdacccc8d87f3d.3@PAGEOFF
	add	x0, sp, #8
	add	x1, sp, #24
	mov	x2, x20
	bl	__RNvMs6_NtNtCsjIpoRzUjyHQ_4core3fmt8buildersNtB5_9DebugList5entry
	add	x8, x19, #8
	str	x8, [sp, #24]
	add	x0, sp, #8
	add	x1, sp, #24
	mov	x2, x20
	bl	__RNvMs6_NtNtCsjIpoRzUjyHQ_4core3fmt8buildersNtB5_9DebugList5entry
	add	x8, x19, #16
	str	x8, [sp, #24]
	add	x0, sp, #8
	add	x1, sp, #24
	mov	x2, x20
	bl	__RNvMs6_NtNtCsjIpoRzUjyHQ_4core3fmt8buildersNtB5_9DebugList5entry
	add	x8, x19, #24
	str	x8, [sp, #24]
	add	x0, sp, #8
	add	x1, sp, #24
	mov	x2, x20
	bl	__RNvMs6_NtNtCsjIpoRzUjyHQ_4core3fmt8buildersNtB5_9DebugList5entry
	add	x8, x19, #32
	str	x8, [sp, #24]
	add	x0, sp, #8
	add	x1, sp, #24
	mov	x2, x20
	bl	__RNvMs6_NtNtCsjIpoRzUjyHQ_4core3fmt8buildersNtB5_9DebugList5entry
	add	x0, sp, #8
	bl	__RNvMs6_NtNtCsjIpoRzUjyHQ_4core3fmt8buildersNtB5_9DebugList6finish
	.cfi_def_cfa wsp, 64
	ldp	x29, x30, [sp, #48]
	ldp	x20, x19, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
	.loh AdrpAdd	Lloh193, Lloh194
	.cfi_endproc

	.p2align	2
__RNvXsb_NtCs6zY7rJBZy9D_5alloc6borrowINtB5_3CoweENtNtCsjIpoRzUjyHQ_4core3fmt7Display3fmtCsle4UtX85Rrh_8specimen:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x2, x1
	ldp	x8, x1, [x0, #8]
	mov	x0, x8
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	b	__RNvXsi_NtCsjIpoRzUjyHQ_4core3fmteNtB5_7Display3fmt
	.cfi_endproc

	.p2align	2
__RNvXsq_NtCs6zY7rJBZy9D_5alloc6stringNtB5_6StringNtNtCsjIpoRzUjyHQ_4core3fmt7Display3fmt:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x2, x1
	ldp	x8, x1, [x0, #8]
	mov	x0, x8
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	b	__RNvXsi_NtCsjIpoRzUjyHQ_4core3fmteNtB5_7Display3fmt
	.cfi_endproc

	.p2align	2
__RNvYINtNvNtCs1SSuMAdGM58_3std9panicking11begin_panic7PayloadNtCsle4UtX85Rrh_8specimen13ExpectedPanicENtNtCsjIpoRzUjyHQ_4core5panic12PanicPayload6as_strBY_:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x0, #0
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.globl	_anneal_rust_bounce
	.p2align	2
_anneal_rust_bounce:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	blr	x8
	add	x0, x0, #1
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.globl	_main
	.p2align	2
_main:
	.cfi_startproc
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x3, x1
	sxtw	x2, w0
Lloh195:
	adrp	x8, __RNvCsle4UtX85Rrh_8specimen4main@PAGE
Lloh196:
	add	x8, x8, __RNvCsle4UtX85Rrh_8specimen4main@PAGEOFF
	str	x8, [sp, #8]
Lloh197:
	adrp	x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.4@PAGE
Lloh198:
	add	x1, x1, l_anon.9da64be1d17a499d89cdacccc8d87f3d.4@PAGEOFF
	add	x0, sp, #8
	mov	w4, #0
	bl	__RNvNtCs1SSuMAdGM58_3std2rt19lang_start_internal
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret
	.loh AdrpAdd	Lloh197, Lloh198
	.loh AdrpAdd	Lloh195, Lloh196
	.cfi_endproc

	.section	__TEXT,__literal16,16byte_literals
	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.0:
	.quad	5977689851910190637
	.quad	1303205892524824642

	.section	__TEXT,__cstring,cstring_literals
l_anon.9da64be1d17a499d89cdacccc8d87f3d.1:
	.asciz	"/rustc/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/std/src/thread/local.rs"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.2:
	.quad	l_anon.9da64be1d17a499d89cdacccc8d87f3d.1
	.asciz	"O\000\000\000\000\000\000\000\255\001\000\000\031\000\000"

	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.3:
	.asciz	"\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNvXs1g_NtCsjIpoRzUjyHQ_4core3fmtRjNtB6_5Debug3fmtCsle4UtX85Rrh_8specimen

	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.4:
	.asciz	"\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNSNvYNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtBb_7process8ExitCodeE0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_once6vtableCsle4UtX85Rrh_8specimen
	.quad	__RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Csle4UtX85Rrh_8specimen
	.quad	__RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Csle4UtX85Rrh_8specimen

	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.5:
	.asciz	"\000\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNvXs_NvNtCs1SSuMAdGM58_3std9panicking11begin_panicINtB4_7PayloadNtCsle4UtX85Rrh_8specimen13ExpectedPanicENtNtCsjIpoRzUjyHQ_4core3fmt7Display3fmtB13_
	.quad	__RNvXNvNtCs1SSuMAdGM58_3std9panicking11begin_panicINtB2_7PayloadNtCsle4UtX85Rrh_8specimen13ExpectedPanicENtNtCsjIpoRzUjyHQ_4core5panic12PanicPayload8take_boxB11_
	.quad	__RNvXNvNtCs1SSuMAdGM58_3std9panicking11begin_panicINtB2_7PayloadNtCsle4UtX85Rrh_8specimen13ExpectedPanicENtNtCsjIpoRzUjyHQ_4core5panic12PanicPayload3getB11_
	.quad	__RNvYINtNvNtCs1SSuMAdGM58_3std9panicking11begin_panic7PayloadNtCsle4UtX85Rrh_8specimen13ExpectedPanicENtNtCsjIpoRzUjyHQ_4core5panic12PanicPayload6as_strBY_

	.section	__TEXT,__cstring,cstring_literals
l_anon.9da64be1d17a499d89cdacccc8d87f3d.6:
	.asciz	"specimen.rs"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.7:
	.quad	l_anon.9da64be1d17a499d89cdacccc8d87f3d.6
	.asciz	"\013\000\000\000\000\000\000\000A\000\000\000\"\000\000"

	.section	__TEXT,__cstring,cstring_literals
l_anon.9da64be1d17a499d89cdacccc8d87f3d.8:
	.asciz	"\032address below image base: \300"

	.section	__TEXT,__const
l_anon.9da64be1d17a499d89cdacccc8d87f3d.9:
	.asciz	"\036EXPECTED_SUBJECT_PANIC marker=\301 \000\200`\007 value=\301 \000\200`\001\n"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.10:
	.quad	l_anon.9da64be1d17a499d89cdacccc8d87f3d.6
	.asciz	"\013\000\000\000\000\000\000\000\214\000\000\000\"\000\000"

	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.11:
	.quad	l_anon.9da64be1d17a499d89cdacccc8d87f3d.6
	.asciz	"\013\000\000\000\000\000\000\000\260\000\000\000.\000\000"

.zerofill __DATA,__bss,__RNvCsle4UtX85Rrh_8specimen10DROP_ORDER,8,3
.zerofill __DATA,__bss,__RNvCsle4UtX85Rrh_8specimen11OUTER_DROPS,8,3
.zerofill __DATA,__bss,__RNvCsle4UtX85Rrh_8specimen14CALLBACK_DROPS,8,3
.zerofill __DATA,__bss,__RNvCsle4UtX85Rrh_8specimen14EXPECTED_HOOKS,8,3
	.section	__TEXT,__const
l_anon.9da64be1d17a499d89cdacccc8d87f3d.12:
	.ascii	"<no-symbol>"

l_anon.9da64be1d17a499d89cdacccc8d87f3d.13:
	.asciz	"\fIMAGE label=\300\t address=\301 \000\200`\f image_base=\301 \000\200`\b offset=\301 \000\200`\b symbol=\300\007 image=\300\001\n"

	.section	__TEXT,__cstring,cstring_literals
l_anon.9da64be1d17a499d89cdacccc8d87f3d.14:
	.asciz	"\022dladdr failed for \300"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.15:
	.quad	l_anon.9da64be1d17a499d89cdacccc8d87f3d.6
	.asciz	"\013\000\000\000\000\000\000\000k\000\000\000\005\000\000"

	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.16:
	.quad	__RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueNCNvCsle4UtX85Rrh_8specimen3run0EBF_
	.asciz	"\020\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNSNvYNCNvCsle4UtX85Rrh_8specimen3run0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceTRNtNtCs1SSuMAdGM58_3std5panic13PanicHookInfoEE9call_once6vtableB8_
	.quad	__RNCNvCsle4UtX85Rrh_8specimen3run0B3_
	.quad	__RNCNvCsle4UtX85Rrh_8specimen3run0B3_

	.section	__TEXT,__const
l_anon.9da64be1d17a499d89cdacccc8d87f3d.17:
	.ascii	"assembly-bounce"

l_anon.9da64be1d17a499d89cdacccc8d87f3d.18:
	.ascii	"rust-bounce"

l_anon.9da64be1d17a499d89cdacccc8d87f3d.19:
	.ascii	"platform-unwinder"

l_anon.9da64be1d17a499d89cdacccc8d87f3d.20:
	.ascii	"ALL_FOUR_CASES_PASSED\n"

	.section	__TEXT,__cstring,cstring_literals
l_anon.9da64be1d17a499d89cdacccc8d87f3d.21:
	.asciz	"\036STOP_UNEXPECTED_DISAGREEMENT: \300\001\n"

.zerofill __DATA,__bss,__RNvCsle4UtX85Rrh_8specimen5CALLS,8,3
	.section	__TEXT,__const
l_anon.9da64be1d17a499d89cdacccc8d87f3d.22:
	.asciz	"\023NORMAL_RESULT path=\300\007 value=\301 \000\200`\001\n"

l_anon.9da64be1d17a499d89cdacccc8d87f3d.23:
	.asciz	"\030normal result mismatch: \300\005 got=\301 \000\200`\n expected=\301 \000\200`"

	.section	__TEXT,__cstring,cstring_literals
l_anon.9da64be1d17a499d89cdacccc8d87f3d.24:
	.asciz	"%UNEXPECTED_PANIC in normal case path=\300\013; resuming\n"

l_anon.9da64be1d17a499d89cdacccc8d87f3d.25:
	.asciz	"&expected subject panic did not occur: \300"

l_anon.9da64be1d17a499d89cdacccc8d87f3d.26:
	.asciz	"\026UNEXPECTED_PANIC path=\300 ; resuming without accepting it\n"

	.section	__TEXT,__literal8,8byte_literals
	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.27:
	.ascii	"DWNU_04E"

	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.28:
	.ascii	"\210wfUD3\"\021"

	.section	__TEXT,__const
l_anon.9da64be1d17a499d89cdacccc8d87f3d.29:
	.asciz	" EXPECTED_PAYLOAD_CONFIRMED path=\300\b marker=\301 \000\200`\007 value=\301 \000\200`\001\n"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.30:
	.quad	l_anon.9da64be1d17a499d89cdacccc8d87f3d.6
	.asciz	"\013\000\000\000\000\000\000\000\264\000\000\000\031\000\000"

	.section	__TEXT,__const
l_anon.9da64be1d17a499d89cdacccc8d87f3d.31:
	.asciz	"\017CASE_PASS path=\300\007 panic=\300\b counts=\300\016 trace_status=\300\005 ips=\301 \000\000b\001\n"

l_anon.9da64be1d17a499d89cdacccc8d87f3d.32:
	.asciz	"8assembly frame/range missing from live backtrace: start=\301 \000\200`\005 end=\301 \000\200`"

	.section	__TEXT,__cstring,cstring_literals
l_anon.9da64be1d17a499d89cdacccc8d87f3d.33:
	.asciz	"#unwind backtrace incomplete/error: \300\b status=\300\005 len=\300\013 truncated=\300"

l_anon.9da64be1d17a499d89cdacccc8d87f3d.34:
	.asciz	"\031call/drop/hook mismatch: \300\005 got=\300\n expected=\300"

	.section	__DATA,__thread_data,thread_local_regular
	.p2align	3, 0x0
__RNvNCNKNvCsle4UtX85Rrh_8specimen10LAST_TRACE0s_023___RUST_STD_INTERNAL_VAL$tlv$init:
	.asciz	"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\377\377\377\377"
	.space	3

	.section	__DATA,__thread_vars,thread_local_variables
__RNvNCNKNvCsle4UtX85Rrh_8specimen10LAST_TRACE0s_023___RUST_STD_INTERNAL_VAL:
	.quad	__tlv_bootstrap
	.quad	0
	.quad	__RNvNCNKNvCsle4UtX85Rrh_8specimen10LAST_TRACE0s_023___RUST_STD_INTERNAL_VAL$tlv$init

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.9da64be1d17a499d89cdacccc8d87f3d.35:
	.asciz	"\000\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNvXNtCsjIpoRzUjyHQ_4core3anyNtCsle4UtX85Rrh_8specimen13ExpectedPanicNtB2_3Any7type_idBt_

	.section	__TEXT,__literal8,8byte_literals
l_anon.9da64be1d17a499d89cdacccc8d87f3d.36:
	.ascii	"Assembly"

	.section	__TEXT,__literal4,4byte_literals
l_anon.9da64be1d17a499d89cdacccc8d87f3d.37:
	.ascii	"Rust"

.subsections_via_symbols
