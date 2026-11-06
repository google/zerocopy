	.build_version macos, 11, 0


	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
	.globl	_anneal_publish_relaxed
_anneal_publish_relaxed:
	mov	w8, #1
	str	w8, [x0]
	str	w8, [x1]
	ret
	.globl	_anneal_publish_release
_anneal_publish_release:
	mov	w8, #1
	str	w8, [x0]
	stlr	w8, [x1]
	ret
	.globl	_anneal_observe_relaxed
_anneal_observe_relaxed:
	ldr	w8, [x1]
	ldr	w9, [x0]
	orr	x0, x9, x8, lsl #32
	ret
	.globl	_anneal_observe_acquire
_anneal_observe_acquire:
	ldapr	w8, [x1]
	ldr	w9, [x0]
	orr	x0, x9, x8, lsl #32
	ret
	.globl	_anneal_sb_relaxed
_anneal_sb_relaxed:
	mov	w8, #1
	str	w8, [x0]
	ldr	w0, [x1]
	ret
	.globl	_anneal_sb_ra
_anneal_sb_ra:
	mov	w8, #1
	stlr	w8, [x0]
	ldapr	w0, [x1]
	ret
	.globl	_anneal_sb_sc
_anneal_sb_sc:
	mov	w8, #1
	stlr	w8, [x0]
	ldar	w0, [x1]
	ret
	.globl	_anneal_sb_fence
_anneal_sb_fence:
	mov	w8, #1
	str	w8, [x0]
	dmb	ish
	ldr	w0, [x1]
	ret


	.private_extern	__RINvNtCshrG7s5e4uVm_3std2rt10lang_startNtNtB4_7process8ExitCodeECs9nK0Xd5EwPT_19concurrent_assembly
	.globl	__RINvNtCshrG7s5e4uVm_3std2rt10lang_startNtNtB4_7process8ExitCodeECs9nK0Xd5EwPT_19concurrent_assembly
	.p2align	2
__RINvNtCshrG7s5e4uVm_3std2rt10lang_startNtNtB4_7process8ExitCodeECs9nK0Xd5EwPT_19concurrent_assembly:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	str	x0, [sp, #8]
Lloh0:
	adrp	x1, l_anon.25cbf1bc66902f282ae062428e5506ff.1@PAGE
Lloh1:
	add	x1, x1, l_anon.25cbf1bc66902f282ae062428e5506ff.1@PAGEOFF
	add	x0, sp, #8
	bl	__RNvNtCshrG7s5e4uVm_3std2rt19lang_start_internal
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret
	.loh AdrpAdd	Lloh0, Lloh1

	.p2align	2
__RINvNtCsi86csyF5gCW_4core3ptr13drop_in_placeNCINvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_uncheckedNCNvCs9nK0Xd5EwPT_19concurrent_assembly3run0uEs_0EB1J_:
	stp	x20, x19, [sp, #-32]!
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	mov	x19, x0
	ldr	x8, [x0, #32]!
	mov	x20, #-1
	ldaddl	x20, x8, [x8]
	cmp	x8, #1
	b.ne	LBB1_2
	dmb	ishld
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtCs9nK0Xd5EwPT_19concurrent_assembly6SharedE9drop_slowBI_
LBB1_2:
	mov	x0, x19
	bl	__RINvNtCsi86csyF5gCW_4core3ptr13drop_in_placeNtNtNtCshrG7s5e4uVm_3std6thread9spawnhook15ChildSpawnHooksECs9nK0Xd5EwPT_19concurrent_assembly
	ldr	x8, [x19, #56]!
	ldaddl	x20, x8, [x8]
	cmp	x8, #1
	b.ne	LBB1_4
	dmb	ishld
	mov	x0, x19
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	b	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcINtNtNtCshrG7s5e4uVm_3std6thread9lifecycle6PacketuEE9drop_slowCs9nK0Xd5EwPT_19concurrent_assembly
LBB1_4:
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	ret

	.p2align	2
__RINvNtCsi86csyF5gCW_4core3ptr13drop_in_placeNtNtNtCshrG7s5e4uVm_3std2io5error5ErrorECs9nK0Xd5EwPT_19concurrent_assembly:
	.cfi_startproc
	stp	x22, x21, [sp, #-48]!
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
	ldr	x19, [x0]
	and	x8, x19, #0x3
	sub	x9, x8, #2
	cmp	x9, #2
	ccmp	x8, #0, #4, hs
	b.ne	LBB2_2
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	ret
LBB2_2:
	ldr	x20, [x19, #-1]!
	ldr	x21, [x19, #8]
	ldr	x8, [x21]
	cbz	x8, LBB2_4
	mov	x0, x20
	blr	x8
LBB2_4:
	ldr	x1, [x21, #8]
	cbz	x1, LBB2_6
	ldr	x2, [x21, #16]
	mov	x0, x20
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB2_6:
	mov	x0, x19
	mov	w1, #24
	mov	w2, #8
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	b	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
	.cfi_endproc

	.p2align	2
__RINvNtCsi86csyF5gCW_4core3ptr13drop_in_placeNtNtNtCshrG7s5e4uVm_3std6thread9spawnhook15ChildSpawnHooksECs9nK0Xd5EwPT_19concurrent_assembly:
	stp	x24, x23, [sp, #-64]!
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	stp	x29, x30, [sp, #48]
	add	x29, sp, #48
	mov	x19, x0
	add	x0, x0, #24
	bl	__RNvXNtNtCshrG7s5e4uVm_3std6thread9spawnhookNtB2_10SpawnHooksNtNtNtCsi86csyF5gCW_4core3ops4drop4Drop4drop
	ldr	x8, [x19, #24]
	cbz	x8, LBB3_3
	mov	x9, #-1
	ldaddl	x9, x8, [x8]
	cmp	x8, #1
	b.ne	LBB3_3
	dmb	ishld
	add	x0, x19, #24
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtNtNtCshrG7s5e4uVm_3std6thread9spawnhook9SpawnHookE9drop_slowBM_
LBB3_3:
	ldp	x20, x22, [x19, #8]
	cbz	x22, LBB3_10
	add	x23, x20, #8
	b	LBB3_6
LBB3_5:
	add	x23, x23, #16
	subs	x22, x22, #1
	b.eq	LBB3_10
LBB3_6:
	ldp	x21, x24, [x23, #-8]
	ldr	x8, [x24]
	cbz	x8, LBB3_8
	mov	x0, x21
	blr	x8
LBB3_8:
	ldr	x1, [x24, #8]
	cbz	x1, LBB3_5
	ldr	x2, [x24, #16]
	mov	x0, x21
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
	b	LBB3_5
LBB3_10:
	ldr	x8, [x19]
	cbz	x8, LBB3_12
	lsl	x1, x8, #4
	mov	x0, x20
	mov	w2, #8
	ldp	x29, x30, [sp, #48]
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldp	x24, x23, [sp], #64
	b	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB3_12:
	ldp	x29, x30, [sp, #48]
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldp	x24, x23, [sp], #64
	ret

	.p2align	2
__RINvNtNtCshrG7s5e4uVm_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECs9nK0Xd5EwPT_19concurrent_assembly:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	blr	x0
	; InlineAsm Start
	; InlineAsm End
	ldp	x29, x30, [sp], #16
	ret

	.p2align	2
__RINvNtNtCshrG7s5e4uVm_3std3sys9backtrace28___rust_begin_short_backtraceNCNCNCINvNtNtB6_6thread9lifecycle15spawn_uncheckedNCNvCs9nK0Xd5EwPT_19concurrent_assembly3run0uEs_000uEB1Z_:
	sub	sp, sp, #48
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	ldp	q0, q1, [x0]
	stp	q0, q1, [sp]
	mov	x0, sp
	bl	__RNvMs_NtNtCshrG7s5e4uVm_3std6thread9spawnhookNtB4_15ChildSpawnHooks3run
	; InlineAsm Start
	; InlineAsm End
	ldp	x29, x30, [sp, #32]
	add	sp, sp, #48
	ret

	.p2align	2
__RINvNtNtCshrG7s5e4uVm_3std3sys9backtrace28___rust_begin_short_backtraceNCNvCs9nK0Xd5EwPT_19concurrent_assembly3run0uEB1b_:
	stp	x22, x21, [sp, #-48]!
	stp	x20, x19, [sp, #16]
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	mov	x19, x0
	ldp	x20, x21, [x0]
	cbz	x21, LBB6_14
	ldrb	w22, [x19, #16]
	b	LBB6_4
LBB6_2:
	bl	_anneal_sb_ra
LBB6_3:
	mov	w8, w0
	str	x8, [x20, #480]
	add	x0, x20, #432
	bl	__RNvMs0_NtNtCshrG7s5e4uVm_3std4sync7barrierNtB5_7Barrier4wait
	subs	x21, x21, #1
	b.eq	LBB6_14
LBB6_4:
	add	x0, x20, #384
	bl	__RNvMs0_NtNtCshrG7s5e4uVm_3std4sync7barrierNtB5_7Barrier4wait
	add	x0, x20, #128
	add	x1, x20, #256
	cmp	w22, #2
	b.gt	LBB6_8
	cbz	w22, LBB6_11
	cmp	w22, #1
	b.ne	LBB6_12
	bl	_anneal_publish_release
	mov	w0, #0
	b	LBB6_3
LBB6_8:
	cmp	w22, #3
	b.eq	LBB6_2
	cmp	w22, #4
	b.ne	LBB6_13
	bl	_anneal_sb_sc
	b	LBB6_3
LBB6_11:
	bl	_anneal_publish_relaxed
	mov	w0, #0
	b	LBB6_3
LBB6_12:
	bl	_anneal_sb_relaxed
	b	LBB6_3
LBB6_13:
	bl	_anneal_sb_fence
	b	LBB6_3
LBB6_14:
	mov	x8, #-1
	ldaddl	x8, x8, [x20]
	cmp	x8, #1
	b.ne	LBB6_16
	dmb	ishld
	mov	x0, x19
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtCs9nK0Xd5EwPT_19concurrent_assembly6SharedE9drop_slowBI_
LBB6_16:
	; InlineAsm Start
	; InlineAsm End
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	ret

	.p2align	2
__RINvNtNtCshrG7s5e4uVm_3std3sys9backtrace28___rust_begin_short_backtraceNCNvCs9nK0Xd5EwPT_19concurrent_assembly3runs_0uEB1b_:
	stp	x22, x21, [sp, #-48]!
	stp	x20, x19, [sp, #16]
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	mov	x19, x0
	ldp	x20, x21, [x0]
	cbz	x21, LBB7_15
	ldrb	w22, [x19, #16]
	b	LBB7_5
LBB7_2:
	bl	_anneal_sb_ra
LBB7_3:
	mov	w0, w0
LBB7_4:
	str	x0, [x20, #488]
	add	x0, x20, #432
	bl	__RNvMs0_NtNtCshrG7s5e4uVm_3std4sync7barrierNtB5_7Barrier4wait
	subs	x21, x21, #1
	b.eq	LBB7_15
LBB7_5:
	add	x0, x20, #384
	bl	__RNvMs0_NtNtCshrG7s5e4uVm_3std4sync7barrierNtB5_7Barrier4wait
	cmp	w22, #2
	b.gt	LBB7_9
	cbz	w22, LBB7_12
	cmp	w22, #1
	b.ne	LBB7_13
	add	x0, x20, #128
	add	x1, x20, #256
	bl	_anneal_observe_acquire
	b	LBB7_4
LBB7_9:
	add	x0, x20, #256
	add	x1, x20, #128
	cmp	w22, #3
	b.eq	LBB7_2
	cmp	w22, #4
	b.ne	LBB7_14
	bl	_anneal_sb_sc
	b	LBB7_3
LBB7_12:
	add	x0, x20, #128
	add	x1, x20, #256
	bl	_anneal_observe_relaxed
	b	LBB7_4
LBB7_13:
	add	x0, x20, #256
	add	x1, x20, #128
	bl	_anneal_sb_relaxed
	b	LBB7_3
LBB7_14:
	bl	_anneal_sb_fence
	b	LBB7_3
LBB7_15:
	mov	x8, #-1
	ldaddl	x8, x8, [x20]
	cmp	x8, #1
	b.ne	LBB7_17
	dmb	ishld
	mov	x0, x19
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtCs9nK0Xd5EwPT_19concurrent_assembly6SharedE9drop_slowBI_
LBB7_17:
	; InlineAsm Start
	; InlineAsm End
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	ret

	.p2align	2
__RNCINvNtCshrG7s5e4uVm_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Cs9nK0Xd5EwPT_19concurrent_assembly:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	ldr	x0, [x0]
	bl	__RINvNtNtCshrG7s5e4uVm_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECs9nK0Xd5EwPT_19concurrent_assembly
	and	w0, w0, #0xff
	ldp	x29, x30, [sp], #16
	ret

	.p2align	2
__RNSNvYNCINvNtCshrG7s5e4uVm_3std2rt10lang_startNtNtBb_7process8ExitCodeE0INtNtNtCsi86csyF5gCW_4core3ops8function6FnOnceuE9call_once6vtableCs9nK0Xd5EwPT_19concurrent_assembly:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	ldr	x0, [x0]
	bl	__RINvNtNtCshrG7s5e4uVm_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECs9nK0Xd5EwPT_19concurrent_assembly
	and	w0, w0, #0xff
	ldp	x29, x30, [sp], #16
	ret

	.p2align	2
__RNSNvYNCINvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_uncheckedNCNvCs9nK0Xd5EwPT_19concurrent_assembly3run0uEs_0INtNtNtCsi86csyF5gCW_4core3ops8function6FnOnceuE9call_once6vtableB17_:
	.cfi_startproc
	sub	sp, sp, #112
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	stp	x29, x30, [sp, #96]
	add	x29, sp, #96
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	mov	x19, x0
	mov	x20, sp
	ldp	q1, q0, [x0, #16]
	stp	q1, q0, [sp, #16]
	ldr	x8, [x0, #48]
	str	x8, [sp, #48]
	ldr	q0, [x0]
	str	q0, [sp]
	mov	x0, sp
	bl	__RINvNtNtCshrG7s5e4uVm_3std3sys9backtrace28___rust_begin_short_backtraceNCNCNCINvNtNtB6_6thread9lifecycle15spawn_uncheckedNCNvCs9nK0Xd5EwPT_19concurrent_assembly3run0uEs_000uEB1Z_
	add	x0, x20, #32
	bl	__RINvNtNtCshrG7s5e4uVm_3std3sys9backtrace28___rust_begin_short_backtraceNCNvCs9nK0Xd5EwPT_19concurrent_assembly3run0uEB1b_
	ldr	x20, [x19, #56]
	ldr	x8, [x20, #24]
	cbz	x8, LBB10_6
	ldr	x19, [x20, #32]
	cbz	x19, LBB10_6
	ldr	x21, [x20, #40]
	ldr	x8, [x21]
	cbz	x8, LBB10_4
	mov	x0, x19
	blr	x8
LBB10_4:
	ldr	x1, [x21, #8]
	cbz	x1, LBB10_6
	ldr	x2, [x21, #16]
	mov	x0, x19
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB10_6:
	mov	w8, #1
	stp	x8, xzr, [x20, #24]
	stur	x20, [x29, #-40]
	mov	x8, #-1
	ldaddl	x8, x8, [x20]
	cmp	x8, #1
	b.ne	LBB10_8
	dmb	ishld
	sub	x0, x29, #40
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcINtNtNtCshrG7s5e4uVm_3std6thread9lifecycle6PacketuEE9drop_slowCs9nK0Xd5EwPT_19concurrent_assembly
LBB10_8:
	ldp	x29, x30, [sp, #96]
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	add	sp, sp, #112
	ret
	.cfi_endproc

	.p2align	2
__RNSNvYNCINvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_uncheckedNCNvCs9nK0Xd5EwPT_19concurrent_assembly3runs_0uEs_0INtNtNtCsi86csyF5gCW_4core3ops8function6FnOnceuE9call_once6vtableB17_:
	.cfi_startproc
	sub	sp, sp, #112
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	stp	x29, x30, [sp, #96]
	add	x29, sp, #96
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	mov	x19, x0
	mov	x20, sp
	ldp	q1, q0, [x0, #16]
	stp	q1, q0, [sp, #16]
	ldr	x8, [x0, #48]
	str	x8, [sp, #48]
	ldr	q0, [x0]
	str	q0, [sp]
	mov	x0, sp
	bl	__RINvNtNtCshrG7s5e4uVm_3std3sys9backtrace28___rust_begin_short_backtraceNCNCNCINvNtNtB6_6thread9lifecycle15spawn_uncheckedNCNvCs9nK0Xd5EwPT_19concurrent_assembly3run0uEs_000uEB1Z_
	add	x0, x20, #32
	bl	__RINvNtNtCshrG7s5e4uVm_3std3sys9backtrace28___rust_begin_short_backtraceNCNvCs9nK0Xd5EwPT_19concurrent_assembly3runs_0uEB1b_
	ldr	x20, [x19, #56]
	ldr	x8, [x20, #24]
	cbz	x8, LBB11_6
	ldr	x19, [x20, #32]
	cbz	x19, LBB11_6
	ldr	x21, [x20, #40]
	ldr	x8, [x21]
	cbz	x8, LBB11_4
	mov	x0, x19
	blr	x8
LBB11_4:
	ldr	x1, [x21, #8]
	cbz	x1, LBB11_6
	ldr	x2, [x21, #16]
	mov	x0, x19
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB11_6:
	mov	w8, #1
	stp	x8, xzr, [x20, #24]
	stur	x20, [x29, #-40]
	mov	x8, #-1
	ldaddl	x8, x8, [x20]
	cmp	x8, #1
	b.ne	LBB11_8
	dmb	ishld
	sub	x0, x29, #40
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcINtNtNtCshrG7s5e4uVm_3std6thread9lifecycle6PacketuEE9drop_slowCs9nK0Xd5EwPT_19concurrent_assembly
LBB11_8:
	ldp	x29, x30, [sp, #96]
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	add	sp, sp, #112
	ret
	.cfi_endproc

	.section	__TEXT,__literal16,16byte_literals
	.p2align	4, 0x0
lCPI12_0:
	.quad	0
	.quad	6
	.section	__TEXT,__text,regular,pure_instructions
	.private_extern	__RNvCs9nK0Xd5EwPT_19concurrent_assembly4main
	.globl	__RNvCs9nK0Xd5EwPT_19concurrent_assembly4main
	.p2align	2
__RNvCs9nK0Xd5EwPT_19concurrent_assembly4main:
	.cfi_startproc
	stp	x28, x27, [sp, #-96]!
	stp	x26, x25, [sp, #16]
	stp	x24, x23, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	stp	x29, x30, [sp, #80]
	add	x29, sp, #80
	sub	sp, sp, #464
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
	mov	x16, #0
Lloh2:
	adrp	x8, lCPI12_0@PAGE
Lloh3:
	ldr	q0, [x8, lCPI12_0@PAGEOFF]
	str	q0, [sp, #32]
	add	x8, sp, #32
	add	x8, x8, #16
	str	x8, [sp, #8]
Lloh4:
	adrp	x8, l_anon.25cbf1bc66902f282ae062428e5506ff.12@PAGE
Lloh5:
	add	x8, x8, l_anon.25cbf1bc66902f282ae062428e5506ff.12@PAGEOFF
	mov	w12, #10
Lloh6:
	adrp	x9, l_anon.25cbf1bc66902f282ae062428e5506ff.13@PAGE
Lloh7:
	add	x9, x9, l_anon.25cbf1bc66902f282ae062428e5506ff.13@PAGEOFF
	stp	x8, x12, [sp, #48]
	strb	wzr, [sp, #64]
	mov	w8, #18
	mov	w20, #1
Lloh8:
	adrp	x10, l_anon.25cbf1bc66902f282ae062428e5506ff.14@PAGE
Lloh9:
	add	x10, x10, l_anon.25cbf1bc66902f282ae062428e5506ff.14@PAGEOFF
	stp	x9, x8, [sp, #72]
	strb	w20, [sp, #88]
	mov	w9, #2
Lloh10:
	adrp	x11, l_anon.25cbf1bc66902f282ae062428e5506ff.15@PAGE
Lloh11:
	add	x11, x11, l_anon.25cbf1bc66902f282ae062428e5506ff.15@PAGEOFF
	mov	w17, #3
	stp	x10, x12, [sp, #96]
Lloh12:
	adrp	x10, l_anon.25cbf1bc66902f282ae062428e5506ff.16@PAGE
Lloh13:
	add	x10, x10, l_anon.25cbf1bc66902f282ae062428e5506ff.16@PAGEOFF
	mov	w12, #9
	mov	w13, #4
	strb	w9, [sp, #112]
Lloh14:
	adrp	x9, l_anon.25cbf1bc66902f282ae062428e5506ff.17@PAGE
Lloh15:
	add	x9, x9, l_anon.25cbf1bc66902f282ae062428e5506ff.17@PAGEOFF
	mov	w14, #8
	mov	w15, #5
	stp	x11, x8, [sp, #120]
	strb	w17, [sp, #136]
	mov	x26, #-1
	stp	x10, x12, [sp, #144]
	strb	w13, [sp, #160]
	stp	x9, x14, [sp, #168]
Lloh16:
	adrp	x27, __RNvNCNvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_unchecked03MIN@GOTPAGE
Lloh17:
	ldr	x27, [x27, __RNvNCNvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_unchecked03MIN@GOTPAGEOFF]
	strb	w15, [sp, #184]
	b	LBB12_2
LBB12_1:
	stp	x20, x21, [x29, #-208]
	stp	x22, x23, [x29, #-192]
	add	x8, sp, #192
	stur	x8, [x29, #-152]
Lloh18:
	adrp	x8, __RNvXs1i_NtCsi86csyF5gCW_4core3fmtReNtB6_7Display3fmtCs9nK0Xd5EwPT_19concurrent_assembly@PAGE
Lloh19:
	add	x9, x8, __RNvXs1i_NtCsi86csyF5gCW_4core3fmtReNtB6_7Display3fmtCs9nK0Xd5EwPT_19concurrent_assembly@PAGEOFF
	sub	x8, x29, #208
	stp	x9, x8, [x29, #-144]
Lloh20:
	adrp	x8, __RNvXsa_NtCsi86csyF5gCW_4core5arrayAjj4_NtNtB7_3fmt5Debug3fmtCs9nK0Xd5EwPT_19concurrent_assembly@PAGE
Lloh21:
	add	x8, x8, __RNvXsa_NtCsi86csyF5gCW_4core5arrayAjj4_NtNtB7_3fmt5Debug3fmtCs9nK0Xd5EwPT_19concurrent_assembly@PAGEOFF
	stur	x8, [x29, #-128]
	sub	x1, x29, #152
Lloh22:
	adrp	x0, l_anon.25cbf1bc66902f282ae062428e5506ff.18@PAGE
Lloh23:
	add	x0, x0, l_anon.25cbf1bc66902f282ae062428e5506ff.18@PAGEOFF
	bl	__RNvNtNtCshrG7s5e4uVm_3std2io5stdio6__print
	ldr	x16, [sp, #16]
	cmp	x16, #6
	mov	w20, #1
	b.eq	LBB12_82
LBB12_2:
	ldr	x8, [sp, #8]
	mov	w10, #24
	madd	x8, x16, x10, x8
	add	x21, x16, #1
	str	x21, [sp, #32]
	ldrb	w22, [x8, #16]
	cmp	w22, #255
	b.eq	LBB12_82
	ldp	x8, x9, [x8]
	stp	x8, x9, [sp, #192]
	bl	__RNvCs7urVXOUFJf8_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #512
	mov	w1, #128
	bl	__RNvCs7urVXOUFJf8_7___rustc12___rust_alloc
	cbz	x0, LBB12_115
	mov	x19, x0
	dup.2d	v0, x20
	str	q0, [x0]
	str	wzr, [x0, #128]
	str	wzr, [x0, #256]
	movi.2d	v0, #0000000000000000
	stp	q0, q0, [x0, #384]
	mov	w8, #3
	stp	xzr, x8, [x0, #416]
	stp	q0, q0, [x0, #432]
	stp	xzr, x8, [x0, #464]
	stp	xzr, xzr, [x0, #480]
	str	x0, [sp, #208]
	ldadd	x20, x8, [x0]
	tbnz	x8, #63, LBB12_118
	stur	x26, [x29, #-176]
	ldr	x8, [x27]
	cbz	x8, LBB12_7
	sub	x24, x8, #1
	b	LBB12_28
LBB12_7:
	sub	x8, x29, #120
Lloh24:
	adrp	x0, l_anon.25cbf1bc66902f282ae062428e5506ff.4@PAGE
Lloh25:
	add	x0, x0, l_anon.25cbf1bc66902f282ae062428e5506ff.4@PAGEOFF
	mov	w1, #14
	bl	__RNvNtCshrG7s5e4uVm_3std3env7__var_os
	ldur	x23, [x29, #-120]
	cmn	x23, #1
	b.eq	LBB12_17
	ldp	x25, x1, [x29, #-112]
	sub	x8, x29, #240
	mov	x0, x25
	bl	__RNvNtNtCsi86csyF5gCW_4core3str8converts9from_utf8
	ldur	x8, [x29, #-240]
	cmp	x8, #1
	b.eq	LBB12_24
	ldur	x9, [x29, #-224]
	cbz	x9, LBB12_24
	ldur	x8, [x29, #-232]
	cmp	x9, #1
	b.ne	LBB12_18
	ldrb	w10, [x8]
	mov	w24, #2097152
	cmp	w10, #43
	b.eq	LBB12_25
	cmp	w10, #45
	b.eq	LBB12_25
	cmp	w10, #43
	cset	w10, eq
	cinc	x8, x8, eq
	sub	x9, x9, x10
	cmp	x9, #17
	b.hs	LBB12_19
LBB12_14:
	mov	x24, #0
	cbz	x9, LBB12_25
LBB12_15:
	ldrb	w10, [x8], #1
	sub	w10, w10, #48
	cmp	w10, #9
	b.hi	LBB12_24
	mov	w11, #10
	mul	x11, x24, x11
	add	x24, x11, w10, uxtw
	subs	x9, x9, #1
	b.ne	LBB12_15
	b	LBB12_25
LBB12_17:
	mov	w24, #2097152
	b	LBB12_27
LBB12_18:
	ldrb	w10, [x8]
	cmp	w10, #43
	cset	w10, eq
	cinc	x8, x8, eq
	sub	x9, x9, x10
	cmp	x9, #17
	b.lo	LBB12_14
LBB12_19:
	mov	x10, #0
LBB12_20:
	cbz	x9, LBB12_80
	mov	w11, #10
	umulh	x11, x10, x11
	cmp	xzr, x11
	b.ne	LBB12_24
	add	x10, x10, x10, lsl #2
	lsl	x10, x10, #1
	ldrb	w11, [x8], #1
	sub	w12, w11, #48
	adds	x10, x10, x12
	cset	w11, hs
	cmp	w12, #9
	b.hi	LBB12_24
	sub	x9, x9, #1
	mov	w24, #2097152
	tbz	w11, #0, LBB12_20
	b	LBB12_25
LBB12_24:
	mov	w24, #2097152
LBB12_25:
	cbz	x23, LBB12_27
LBB12_26:
	mov	x0, x25
	mov	x1, x23
	mov	w2, #1
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB12_27:
	add	x8, x24, #1
	str	x8, [x27]
LBB12_28:
	bl	__RNvMNtNtCshrG7s5e4uVm_3std6thread2idNtB2_8ThreadId3new
	sub	x1, x29, #176
	bl	__RNvMs_NtNtCshrG7s5e4uVm_3std6thread6threadNtB4_6Thread3new
	stur	x0, [x29, #-120]
	sub	x8, x29, #208
	sub	x0, x29, #120
	bl	__RNvNtNtCshrG7s5e4uVm_3std6thread9spawnhook15run_spawn_hooks
	bl	__RNvCs7urVXOUFJf8_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #48
	mov	w1, #8
	bl	__RNvCs7urVXOUFJf8_7___rustc12___rust_alloc
	cbz	x0, LBB12_112
	mov	x23, x0
	dup.2d	v0, x20
	str	q0, [x0]
	stp	xzr, xzr, [x0, #16]
	stur	x0, [x29, #-240]
	ldadd	x20, x8, [x0]
	tbnz	x8, #63, LBB12_118
	bl	__RNvCs7urVXOUFJf8_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #64
	mov	w1, #8
	bl	__RNvCs7urVXOUFJf8_7___rustc12___rust_alloc
	cbz	x0, LBB12_113
	mov	x25, x0
	ldp	q0, q1, [x29, #-208]
	stp	q0, q1, [x0]
	mov	w8, #10000
	stp	x19, x8, [x0, #32]
	strb	w22, [x0, #48]
	str	x23, [x0, #56]
	ldur	x8, [x29, #-120]
	ldadd	x20, x8, [x8]
	tbnz	x8, #63, LBB12_118
	ldur	x20, [x29, #-120]
	bl	__RNvCs7urVXOUFJf8_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #24
	mov	w1, #8
	bl	__RNvCs7urVXOUFJf8_7___rustc12___rust_alloc
	cbz	x0, LBB12_114
	mov	x1, x0
	stp	x20, x25, [x0]
Lloh26:
	adrp	x8, l_anon.25cbf1bc66902f282ae062428e5506ff.2@PAGE
Lloh27:
	add	x8, x8, l_anon.25cbf1bc66902f282ae062428e5506ff.2@PAGEOFF
	str	x8, [x0, #16]
	mov	x0, x24
	bl	__RNvMs0_NtNtNtCshrG7s5e4uVm_3std3sys6thread4unixNtB5_6Thread3new
	mov	x24, x1
	tbnz	w0, #0, LBB12_119
	ldur	x28, [x29, #-120]
	mov	w20, #1
	ldadd	x20, x8, [x19]
	tbnz	x8, #63, LBB12_118
	stur	x26, [x29, #-176]
	ldr	x8, [x27]
	cbz	x8, LBB12_37
	sub	x26, x8, #1
	b	LBB12_59
LBB12_37:
	sub	x8, x29, #120
Lloh28:
	adrp	x0, l_anon.25cbf1bc66902f282ae062428e5506ff.4@PAGE
Lloh29:
	add	x0, x0, l_anon.25cbf1bc66902f282ae062428e5506ff.4@PAGEOFF
	mov	w1, #14
	bl	__RNvNtCshrG7s5e4uVm_3std3env7__var_os
	ldur	x25, [x29, #-120]
	cmn	x25, #1
	b.eq	LBB12_47
	ldp	x27, x1, [x29, #-112]
	sub	x8, x29, #240
	mov	x0, x27
	bl	__RNvNtNtCsi86csyF5gCW_4core3str8converts9from_utf8
	ldur	x8, [x29, #-240]
	cmp	x8, #1
	b.eq	LBB12_54
	ldur	x9, [x29, #-224]
	cbz	x9, LBB12_54
	ldur	x8, [x29, #-232]
	cmp	x9, #1
	b.ne	LBB12_48
	ldrb	w10, [x8]
	mov	w26, #2097152
	cmp	w10, #43
	b.eq	LBB12_55
	cmp	w10, #45
	b.eq	LBB12_55
	cmp	w10, #43
	cset	w10, eq
	cinc	x8, x8, eq
	sub	x9, x9, x10
	cmp	x9, #17
	b.hs	LBB12_49
LBB12_44:
	mov	x26, #0
	cbz	x9, LBB12_55
LBB12_45:
	ldrb	w10, [x8], #1
	sub	w10, w10, #48
	cmp	w10, #9
	b.hi	LBB12_54
	mov	w11, #10
	mul	x11, x26, x11
	add	x26, x11, w10, uxtw
	subs	x9, x9, #1
	b.ne	LBB12_45
	b	LBB12_55
LBB12_47:
	mov	w26, #2097152
	b	LBB12_58
LBB12_48:
	ldrb	w10, [x8]
	cmp	w10, #43
	cset	w10, eq
	cinc	x8, x8, eq
	sub	x9, x9, x10
	cmp	x9, #17
	b.lo	LBB12_44
LBB12_49:
	mov	x10, #0
LBB12_50:
	cbz	x9, LBB12_81
	mov	w11, #10
	umulh	x11, x10, x11
	cmp	xzr, x11
	b.ne	LBB12_54
	add	x10, x10, x10, lsl #2
	lsl	x10, x10, #1
	ldrb	w11, [x8], #1
	sub	w12, w11, #48
	adds	x10, x10, x12
	cset	w11, hs
	cmp	w12, #9
	b.hi	LBB12_54
	sub	x9, x9, #1
	mov	w26, #2097152
	tbz	w11, #0, LBB12_50
	b	LBB12_55
LBB12_54:
	mov	w26, #2097152
LBB12_55:
	cbz	x25, LBB12_57
LBB12_56:
	mov	x0, x27
	mov	x1, x25
	mov	w2, #1
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB12_57:
Lloh30:
	adrp	x27, __RNvNCNvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_unchecked03MIN@GOTPAGE
Lloh31:
	ldr	x27, [x27, __RNvNCNvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_unchecked03MIN@GOTPAGEOFF]
LBB12_58:
	add	x8, x26, #1
	str	x8, [x27]
LBB12_59:
	bl	__RNvMNtNtCshrG7s5e4uVm_3std6thread2idNtB2_8ThreadId3new
	sub	x1, x29, #176
	bl	__RNvMs_NtNtCshrG7s5e4uVm_3std6thread6threadNtB4_6Thread3new
	stur	x0, [x29, #-120]
	sub	x8, x29, #152
	sub	x0, x29, #120
	bl	__RNvNtNtCshrG7s5e4uVm_3std6thread9spawnhook15run_spawn_hooks
	bl	__RNvCs7urVXOUFJf8_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #48
	mov	w1, #8
	bl	__RNvCs7urVXOUFJf8_7___rustc12___rust_alloc
	cbz	x0, LBB12_112
	mov	x25, x0
	dup.2d	v0, x20
	str	q0, [x0]
	stp	xzr, xzr, [x0, #16]
	stur	x0, [x29, #-240]
	ldadd	x20, x8, [x0]
	tbnz	x8, #63, LBB12_118
	bl	__RNvCs7urVXOUFJf8_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #64
	mov	w1, #8
	bl	__RNvCs7urVXOUFJf8_7___rustc12___rust_alloc
	cbz	x0, LBB12_113
	mov	x27, x0
	add	x8, sp, #216
	ldp	q0, q1, [x8, #176]
	stp	q0, q1, [x0]
	mov	w8, #10000
	stp	x19, x8, [x0, #32]
	strb	w22, [x0, #48]
	str	x25, [x0, #56]
	ldur	x8, [x29, #-120]
	ldadd	x20, x8, [x8]
	tbnz	x8, #63, LBB12_118
	ldur	x20, [x29, #-120]
	bl	__RNvCs7urVXOUFJf8_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #24
	mov	w1, #8
	bl	__RNvCs7urVXOUFJf8_7___rustc12___rust_alloc
	cbz	x0, LBB12_114
	mov	x1, x0
	stp	x21, x24, [sp, #16]
	stp	x20, x27, [x0]
Lloh32:
	adrp	x8, l_anon.25cbf1bc66902f282ae062428e5506ff.3@PAGE
Lloh33:
	add	x8, x8, l_anon.25cbf1bc66902f282ae062428e5506ff.3@PAGEOFF
	str	x8, [x0, #16]
	mov	x0, x26
	bl	__RNvMs0_NtNtNtCshrG7s5e4uVm_3std3sys6thread4unixNtB5_6Thread3new
	tbnz	w0, #0, LBB12_124
	ldur	x8, [x29, #-120]
	stp	x8, x25, [sp, #216]
	str	x1, [sp, #232]
	movi.2d	v0, #0000000000000000
	stp	q0, q0, [sp, #240]
	mov	x20, #-1
	mov	w24, #10000
	b	LBB12_67
LBB12_66:
	add	x10, sp, #240
	add	x9, x10, x9, lsl #4
	ldr	x10, [x9, x8, lsl #3]
	add	x10, x10, #1
	str	x10, [x9, x8, lsl #3]
	subs	x24, x24, #1
	b.eq	LBB12_71
LBB12_67:
	str	wzr, [x19, #128]
	str	wzr, [x19, #256]
	add	x0, x19, #384
	bl	__RNvMs0_NtNtCshrG7s5e4uVm_3std4sync7barrierNtB5_7Barrier4wait
	add	x0, x19, #432
	bl	__RNvMs0_NtNtCshrG7s5e4uVm_3std4sync7barrierNtB5_7Barrier4wait
	ldr	x9, [x19, #480]
	ldr	x8, [x19, #488]
	lsr	x10, x8, #32
	mov	w11, w8
	cmp	w22, #2
	csel	x8, x11, x8, lo
	csel	x9, x10, x9, lo
	stur	x9, [x29, #-176]
	stur	x8, [x29, #-120]
	orr	x10, x9, x8
	cmp	x10, #2
	b.lo	LBB12_66
	sub	x8, x29, #176
	stur	x8, [x29, #-240]
Lloh34:
	adrp	x9, __RNvXsd_NtNtNtCsi86csyF5gCW_4core3fmt3num3impyNtB9_7Display3fmt@GOTPAGE
Lloh35:
	ldr	x9, [x9, __RNvXsd_NtNtNtCsi86csyF5gCW_4core3fmt3num3impyNtB9_7Display3fmt@GOTPAGEOFF]
	sub	x8, x29, #120
	stp	x9, x8, [x29, #-232]
	stur	x9, [x29, #-216]
	add	x8, sp, #280
	sub	x1, x29, #240
Lloh36:
	adrp	x0, l_anon.25cbf1bc66902f282ae062428e5506ff.11@PAGE
Lloh37:
	add	x0, x0, l_anon.25cbf1bc66902f282ae062428e5506ff.11@PAGEOFF
	bl	__RNvNvNtCscrXPs3M05UR_5alloc3fmt6format12format_inner
	ldp	x26, x25, [sp, #280]
	ldr	x27, [sp, #296]
	sub	x8, x20, #1
	cmn	x8, #3
	b.hi	LBB12_70
	mov	x0, x21
	mov	x1, x20
	mov	w2, #1
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB12_70:
	mov	x21, x25
	mov	x20, x26
	subs	x24, x24, #1
	b.ne	LBB12_67
LBB12_71:
	stp	x28, x23, [x29, #-240]
	ldr	x8, [sp, #24]
	stur	x8, [x29, #-224]
	sub	x0, x29, #240
	bl	__RNvMs1_NtNtCshrG7s5e4uVm_3std6thread9lifecycleINtB5_9JoinInneruE4joinCs9nK0Xd5EwPT_19concurrent_assembly
	mov	x23, x0
	cbnz	x0, LBB12_83
	add	x8, sp, #216
	ldr	q0, [x8]
	stur	q0, [x29, #-240]
	ldr	x8, [sp, #232]
	stur	x8, [x29, #-224]
	sub	x0, x29, #240
	bl	__RNvMs1_NtNtCshrG7s5e4uVm_3std6thread9lifecycleINtB5_9JoinInneruE4joinCs9nK0Xd5EwPT_19concurrent_assembly
	cbnz	x0, LBB12_87
	cmn	x20, #1
	b.ne	LBB12_101
	sub	w8, w22, #4
	cmp	w8, #2
	b.hs	LBB12_76
	ldr	x8, [sp, #240]
	mov	x26, #-1
Lloh38:
	adrp	x27, __RNvNCNvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_unchecked03MIN@GOTPAGE
Lloh39:
	ldr	x27, [x27, __RNvNCNvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_unchecked03MIN@GOTPAGEOFF]
	cbz	x8, LBB12_78
	b	LBB12_107
LBB12_76:
	cmp	w22, #1
	mov	x26, #-1
Lloh40:
	adrp	x27, __RNvNCNvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_unchecked03MIN@GOTPAGE
Lloh41:
	ldr	x27, [x27, __RNvNCNvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_unchecked03MIN@GOTPAGEOFF]
	b.ne	LBB12_78
	ldr	x8, [sp, #256]
	cbnz	x8, LBB12_109
LBB12_78:
	ldp	x20, x21, [sp, #240]
	ldp	x22, x23, [sp, #256]
	ldaddl	x26, x8, [x19]
	cmp	x8, #1
	b.ne	LBB12_1
	dmb	ishld
	add	x0, sp, #208
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtCs9nK0Xd5EwPT_19concurrent_assembly6SharedE9drop_slowBI_
	b	LBB12_1
LBB12_80:
	mov	x24, x10
	cbnz	x23, LBB12_26
	b	LBB12_27
LBB12_81:
	mov	x26, x10
	cbnz	x25, LBB12_56
	b	LBB12_57
LBB12_82:
	mov	w0, #0
	b	LBB12_106
LBB12_83:
	ldr	x8, [x1]
	cbz	x8, LBB12_85
	mov	x0, x23
	mov	x22, x1
	blr	x8
	mov	x1, x22
LBB12_85:
	ldr	x8, [x1, #8]
	cbz	x8, LBB12_92
	ldr	x2, [x1, #16]
	mov	x0, x23
	b	LBB12_91
LBB12_87:
	ldr	x8, [x1]
	cbz	x8, LBB12_89
	mov	x22, x0
	mov	x24, x1
	blr	x8
	mov	x1, x24
	mov	x0, x22
LBB12_89:
	ldr	x8, [x1, #8]
	cbz	x8, LBB12_92
	ldr	x2, [x1, #16]
LBB12_91:
	mov	x1, x8
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB12_92:
	bl	__RNvCs7urVXOUFJf8_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #14
	mov	w1, #1
	bl	__RNvCs7urVXOUFJf8_7___rustc12___rust_alloc
	cbz	x0, LBB12_116
	mov	x22, x0
Lloh42:
	adrp	x8, l_anon.25cbf1bc66902f282ae062428e5506ff.10@PAGE
Lloh43:
	add	x8, x8, l_anon.25cbf1bc66902f282ae062428e5506ff.10@PAGEOFF
	ldr	x9, [x8]
	str	x9, [x0]
	ldur	x8, [x8, #6]
	stur	x8, [x0, #6]
	sub	x8, x20, #1
	cmn	x8, #2
	b.hs	LBB12_95
	mov	x0, x21
	mov	x1, x20
	mov	w2, #1
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB12_95:
	cbz	x23, LBB12_100
	add	x8, sp, #216
	add	x0, x8, #16
	bl	__RNvXs1_NtNtNtCshrG7s5e4uVm_3std3sys6thread4unixNtB5_6ThreadNtNtNtCsi86csyF5gCW_4core3ops4drop4Drop4drop
	ldr	x8, [sp, #216]
	mov	x20, #-1
	ldaddl	x20, x8, [x8]
	cmp	x8, #1
	b.ne	LBB12_98
	dmb	ishld
	add	x0, sp, #216
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtNtNtCshrG7s5e4uVm_3std6thread6thread5InnerNtNtBM_5alloc6SystemE9drop_slowBM_
LBB12_98:
	ldr	x8, [sp, #224]
	ldaddl	x20, x8, [x8]
	cmp	x8, #1
	b.ne	LBB12_100
	dmb	ishld
	add	x8, sp, #216
	add	x0, x8, #8
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcINtNtNtCshrG7s5e4uVm_3std6thread9lifecycle6PacketuEE9drop_slowCs9nK0Xd5EwPT_19concurrent_assembly
LBB12_100:
	mov	w27, #14
	mov	x21, x22
	mov	w20, #14
LBB12_101:
	mov	x8, #-1
	ldaddl	x8, x8, [x19]
	cmp	x8, #1
	b.ne	LBB12_103
LBB12_102:
	dmb	ishld
	add	x0, sp, #208
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtCs9nK0Xd5EwPT_19concurrent_assembly6SharedE9drop_slowBI_
LBB12_103:
	stp	x20, x21, [x29, #-208]
	stur	x27, [x29, #-192]
	add	x8, sp, #192
	stur	x8, [x29, #-152]
Lloh44:
	adrp	x8, __RNvXs1i_NtCsi86csyF5gCW_4core3fmtReNtB6_7Display3fmtCs9nK0Xd5EwPT_19concurrent_assembly@PAGE
Lloh45:
	add	x10, x8, __RNvXs1i_NtCsi86csyF5gCW_4core3fmtReNtB6_7Display3fmtCs9nK0Xd5EwPT_19concurrent_assembly@PAGEOFF
	sub	x8, x29, #208
Lloh46:
	adrp	x9, __RNvXsq_NtCscrXPs3M05UR_5alloc6stringNtB5_6StringNtNtCsi86csyF5gCW_4core3fmt7Display3fmt@PAGE
Lloh47:
	add	x9, x9, __RNvXsq_NtCscrXPs3M05UR_5alloc6stringNtB5_6StringNtNtCsi86csyF5gCW_4core3fmt7Display3fmt@PAGEOFF
	stp	x10, x8, [x29, #-144]
	stur	x9, [x29, #-128]
Lloh48:
	adrp	x0, l_anon.25cbf1bc66902f282ae062428e5506ff.19@PAGE
Lloh49:
	add	x0, x0, l_anon.25cbf1bc66902f282ae062428e5506ff.19@PAGEOFF
	sub	x1, x29, #152
	bl	__RNvNtNtCshrG7s5e4uVm_3std2io5stdio7__eprint
	ldur	x1, [x29, #-208]
	cbz	x1, LBB12_105
	ldur	x0, [x29, #-200]
	mov	w2, #1
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB12_105:
	mov	w0, #1
LBB12_106:
	add	sp, sp, #464
	ldp	x29, x30, [sp, #80]
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldp	x24, x23, [sp, #32]
	ldp	x26, x25, [sp, #16]
	ldp	x28, x27, [sp], #96
	ret
LBB12_107:
	bl	__RNvCs7urVXOUFJf8_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #30
	mov	w1, #1
	bl	__RNvCs7urVXOUFJf8_7___rustc12___rust_alloc
	cbz	x0, LBB12_117
	mov	x21, x0
Lloh50:
	adrp	x8, l_anon.25cbf1bc66902f282ae062428e5506ff.9@PAGE
Lloh51:
	add	x8, x8, l_anon.25cbf1bc66902f282ae062428e5506ff.9@PAGEOFF
	b	LBB12_111
LBB12_109:
	bl	__RNvCs7urVXOUFJf8_7___rustc35___rust_no_alloc_shim_is_unstable_v2
	mov	w0, #30
	mov	w1, #1
	bl	__RNvCs7urVXOUFJf8_7___rustc12___rust_alloc
	cbz	x0, LBB12_117
	mov	x21, x0
Lloh52:
	adrp	x8, l_anon.25cbf1bc66902f282ae062428e5506ff.8@PAGE
Lloh53:
	add	x8, x8, l_anon.25cbf1bc66902f282ae062428e5506ff.8@PAGEOFF
LBB12_111:
	ldr	q0, [x8]
	str	q0, [x21]
	ldur	q0, [x8, #14]
	stur	q0, [x21, #14]
	mov	w27, #30
	mov	w20, #30
	mov	x8, #-1
	ldaddl	x8, x8, [x19]
	cmp	x8, #1
	b.eq	LBB12_102
	b	LBB12_103
LBB12_112:
	mov	w0, #8
	mov	w1, #48
	bl	__RNvNtCscrXPs3M05UR_5alloc5alloc18handle_alloc_error
LBB12_113:
	mov	w0, #8
	mov	w1, #64
	bl	__RNvNtCscrXPs3M05UR_5alloc5alloc18handle_alloc_error
LBB12_114:
	mov	w0, #8
	mov	w1, #24
	bl	__RNvNtCscrXPs3M05UR_5alloc5alloc18handle_alloc_error
LBB12_115:
	mov	w0, #128
	mov	w1, #512
	bl	__RNvNtCscrXPs3M05UR_5alloc5alloc18handle_alloc_error
LBB12_116:
	mov	w0, #1
	mov	w1, #14
	bl	__RNvNtCscrXPs3M05UR_5alloc7raw_vec12handle_error
LBB12_117:
	mov	w0, #1
	mov	w1, #30
	bl	__RNvNtCscrXPs3M05UR_5alloc7raw_vec12handle_error
LBB12_118:
	brk	#0x1
LBB12_119:
	mov	x19, #-1
	ldaddl	x19, x8, [x23]
	cmp	x8, #1
	b.ne	LBB12_121
	dmb	ishld
	sub	x0, x29, #240
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcINtNtNtCshrG7s5e4uVm_3std6thread9lifecycle6PacketuEE9drop_slowCs9nK0Xd5EwPT_19concurrent_assembly
LBB12_121:
	ldur	x8, [x29, #-120]
	ldaddl	x19, x8, [x8]
	cmp	x8, #1
	b.ne	LBB12_123
	dmb	ishld
	sub	x0, x29, #120
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtNtNtCshrG7s5e4uVm_3std6thread6thread5InnerNtNtBM_5alloc6SystemE9drop_slowBM_
LBB12_123:
	stur	x24, [x29, #-240]
	b	LBB12_129
LBB12_124:
	mov	x19, x1
	mov	x20, #-1
	ldaddl	x20, x8, [x25]
	cmp	x8, #1
	b.ne	LBB12_126
	dmb	ishld
	sub	x0, x29, #240
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcINtNtNtCshrG7s5e4uVm_3std6thread9lifecycle6PacketuEE9drop_slowCs9nK0Xd5EwPT_19concurrent_assembly
LBB12_126:
	ldur	x8, [x29, #-120]
	ldaddl	x20, x8, [x8]
	cmp	x8, #1
	b.ne	LBB12_128
	dmb	ishld
	sub	x0, x29, #120
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtNtNtCshrG7s5e4uVm_3std6thread6thread5InnerNtNtBM_5alloc6SystemE9drop_slowBM_
LBB12_128:
	stur	x19, [x29, #-240]
LBB12_129:
Lloh54:
	adrp	x0, l_anon.25cbf1bc66902f282ae062428e5506ff.5@PAGE
Lloh55:
	add	x0, x0, l_anon.25cbf1bc66902f282ae062428e5506ff.5@PAGEOFF
Lloh56:
	adrp	x3, l_anon.25cbf1bc66902f282ae062428e5506ff.20@PAGE
Lloh57:
	add	x3, x3, l_anon.25cbf1bc66902f282ae062428e5506ff.20@PAGEOFF
Lloh58:
	adrp	x4, l_anon.25cbf1bc66902f282ae062428e5506ff.7@PAGE
Lloh59:
	add	x4, x4, l_anon.25cbf1bc66902f282ae062428e5506ff.7@PAGEOFF
	sub	x2, x29, #240
	mov	w1, #22
	bl	__RNvNtCsi86csyF5gCW_4core6result13unwrap_failed
	.loh AdrpLdrGot	Lloh16, Lloh17
	.loh AdrpAdd	Lloh14, Lloh15
	.loh AdrpAdd	Lloh12, Lloh13
	.loh AdrpAdd	Lloh10, Lloh11
	.loh AdrpAdd	Lloh8, Lloh9
	.loh AdrpAdd	Lloh6, Lloh7
	.loh AdrpAdd	Lloh4, Lloh5
	.loh AdrpLdr	Lloh2, Lloh3
	.loh AdrpAdd	Lloh22, Lloh23
	.loh AdrpAdd	Lloh20, Lloh21
	.loh AdrpAdd	Lloh18, Lloh19
	.loh AdrpAdd	Lloh24, Lloh25
	.loh AdrpAdd	Lloh26, Lloh27
	.loh AdrpAdd	Lloh28, Lloh29
	.loh AdrpLdrGot	Lloh30, Lloh31
	.loh AdrpAdd	Lloh32, Lloh33
	.loh AdrpAdd	Lloh36, Lloh37
	.loh AdrpLdrGot	Lloh34, Lloh35
	.loh AdrpLdrGot	Lloh38, Lloh39
	.loh AdrpLdrGot	Lloh40, Lloh41
	.loh AdrpAdd	Lloh42, Lloh43
	.loh AdrpAdd	Lloh48, Lloh49
	.loh AdrpAdd	Lloh46, Lloh47
	.loh AdrpAdd	Lloh44, Lloh45
	.loh AdrpAdd	Lloh50, Lloh51
	.loh AdrpAdd	Lloh52, Lloh53
	.loh AdrpAdd	Lloh58, Lloh59
	.loh AdrpAdd	Lloh56, Lloh57
	.loh AdrpAdd	Lloh54, Lloh55
	.cfi_endproc

	.p2align	2
__RNvMs1_NtNtCshrG7s5e4uVm_3std6thread9lifecycleINtB5_9JoinInneruE4joinCs9nK0Xd5EwPT_19concurrent_assembly:
	.cfi_startproc
	stp	x22, x21, [sp, #-48]!
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
	mov	x19, x0
	ldr	x0, [x0, #16]
	bl	__RNvMs0_NtNtNtCshrG7s5e4uVm_3std3sys6thread4unixNtB5_6Thread4join
	mov	x0, x19
	ldr	x8, [x19, #8]!
	add	x9, x8, #8
	mov	w10, #1
	mov	x11, #-1
	casa	x10, x11, [x9]
	cmp	x10, #1
	b.ne	LBB13_8
	ldapr	x9, [x8]
	stlur	x10, [x8, #8]
	cmp	x9, #1
	b.ne	LBB13_8
	ldr	x8, [x19]
	ldp	x9, x20, [x8, #24]
	ldr	x21, [x8, #40]
	str	xzr, [x8, #24]
	cmp	x9, #1
	b.ne	LBB13_9
	ldr	x8, [x0]
	mov	x22, #-1
	ldaddl	x22, x8, [x8]
	cmp	x8, #1
	b.eq	LBB13_6
	ldr	x8, [x19]
	ldaddl	x22, x8, [x8]
	cmp	x8, #1
	b.eq	LBB13_7
LBB13_5:
	mov	x0, x20
	mov	x1, x21
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	ret
LBB13_6:
	dmb	ishld
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtNtNtCshrG7s5e4uVm_3std6thread6thread5InnerNtNtBM_5alloc6SystemE9drop_slowBM_
	ldr	x8, [x19]
	ldaddl	x22, x8, [x8]
	cmp	x8, #1
	b.ne	LBB13_5
LBB13_7:
	dmb	ishld
	mov	x0, x19
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcINtNtNtCshrG7s5e4uVm_3std6thread9lifecycle6PacketuEE9drop_slowCs9nK0Xd5EwPT_19concurrent_assembly
	mov	x0, x20
	mov	x1, x21
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	ret
LBB13_8:
Lloh60:
	adrp	x0, l_anon.25cbf1bc66902f282ae062428e5506ff.21@PAGE
Lloh61:
	add	x0, x0, l_anon.25cbf1bc66902f282ae062428e5506ff.21@PAGEOFF
Lloh62:
	adrp	x2, l_anon.25cbf1bc66902f282ae062428e5506ff.23@PAGE
Lloh63:
	add	x2, x2, l_anon.25cbf1bc66902f282ae062428e5506ff.23@PAGEOFF
	mov	w1, #41
	bl	__RNvNtCsi86csyF5gCW_4core6option13expect_failed
LBB13_9:
Lloh64:
	adrp	x0, l_anon.25cbf1bc66902f282ae062428e5506ff.24@PAGE
Lloh65:
	add	x0, x0, l_anon.25cbf1bc66902f282ae062428e5506ff.24@PAGEOFF
	bl	__RNvNtCsi86csyF5gCW_4core6option13unwrap_failed
	.loh AdrpAdd	Lloh62, Lloh63
	.loh AdrpAdd	Lloh60, Lloh61
	.loh AdrpAdd	Lloh64, Lloh65
	.cfi_endproc

	.p2align	2
__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcINtNtNtCshrG7s5e4uVm_3std6thread9lifecycle6PacketuEE9drop_slowCs9nK0Xd5EwPT_19concurrent_assembly:
	.cfi_startproc
	stp	x22, x21, [sp, #-48]!
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
	ldr	x19, [x0]
	ldp	x8, x21, [x19, #24]
	cmp	x21, #0
	csel	w20, wzr, w8, eq
	cbz	x8, LBB14_6
	cbz	x21, LBB14_6
	ldr	x22, [x19, #40]
	ldr	x8, [x22]
	cbz	x8, LBB14_4
	mov	x0, x21
	blr	x8
LBB14_4:
	ldr	x1, [x22, #8]
	cbz	x1, LBB14_6
	ldr	x2, [x22, #16]
	mov	x0, x21
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB14_6:
	str	xzr, [x19, #24]
	ldr	x21, [x19, #16]
	cbz	x21, LBB14_15
	add	x0, x21, #16
	mov	x1, x20
	bl	__RNvMNtNtCshrG7s5e4uVm_3std6thread6scopedNtB2_9ScopeData29decrement_num_running_threads
	mov	x8, #-1
	ldaddl	x8, x8, [x21]
	cmp	x8, #1
	b.ne	LBB14_9
	dmb	ishld
	add	x0, x19, #16
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtNtNtCshrG7s5e4uVm_3std6thread6scoped9ScopeDataE9drop_slowCs9nK0Xd5EwPT_19concurrent_assembly
LBB14_9:
	ldr	x8, [x19, #24]
	cbz	x8, LBB14_15
	ldr	x20, [x19, #32]
	cbz	x20, LBB14_15
	ldr	x21, [x19, #40]
	ldr	x8, [x21]
	cbz	x8, LBB14_13
	mov	x0, x20
	blr	x8
LBB14_13:
	ldr	x1, [x21, #8]
	cbz	x1, LBB14_15
	ldr	x2, [x21, #16]
	mov	x0, x20
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB14_15:
	cmn	x19, #1
	b.eq	LBB14_18
	add	x8, x19, #8
	mov	x9, #-1
	ldaddl	x9, x8, [x8]
	cmp	x8, #1
	b.ne	LBB14_18
	dmb	ishld
	mov	x0, x19
	mov	w1, #48
	mov	w2, #8
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	b	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB14_18:
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	ret
	.cfi_endproc

	.p2align	2
__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtCs9nK0Xd5EwPT_19concurrent_assembly6SharedE9drop_slowBI_:
	.cfi_startproc
	stp	x20, x19, [sp, #-32]!
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	ldr	x19, [x0]
	add	x0, x19, #400
	bl	__RNvXs_NtNtNtNtCshrG7s5e4uVm_3std3sys4sync5mutex7pthreadNtB4_5MutexNtNtNtCsi86csyF5gCW_4core3ops4drop4Drop4drop
	ldr	x20, [x19, #400]
	str	xzr, [x19, #400]
	cbz	x20, LBB15_2
	mov	x0, x20
	bl	__RNvXs2_NtNtNtNtNtCshrG7s5e4uVm_3std3sys3pal4unix4sync5mutexNtB5_5MutexNtNtNtCsi86csyF5gCW_4core3ops4drop4Drop4drop
	mov	x0, x20
	mov	w1, #64
	mov	w2, #8
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB15_2:
	ldr	x20, [x19, #384]
	str	xzr, [x19, #384]
	cbz	x20, LBB15_4
	mov	x0, x20
	bl	_pthread_cond_destroy
	mov	x0, x20
	mov	w1, #48
	mov	w2, #8
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB15_4:
	add	x0, x19, #448
	bl	__RNvXs_NtNtNtNtCshrG7s5e4uVm_3std3sys4sync5mutex7pthreadNtB4_5MutexNtNtNtCsi86csyF5gCW_4core3ops4drop4Drop4drop
	ldr	x20, [x19, #448]
	str	xzr, [x19, #448]
	cbz	x20, LBB15_6
	mov	x0, x20
	bl	__RNvXs2_NtNtNtNtNtCshrG7s5e4uVm_3std3sys3pal4unix4sync5mutexNtB5_5MutexNtNtNtCsi86csyF5gCW_4core3ops4drop4Drop4drop
	mov	x0, x20
	mov	w1, #64
	mov	w2, #8
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB15_6:
	ldr	x20, [x19, #432]
	str	xzr, [x19, #432]
	cbz	x20, LBB15_8
	mov	x0, x20
	bl	_pthread_cond_destroy
	mov	x0, x20
	mov	w1, #48
	mov	w2, #8
	bl	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB15_8:
	cmn	x19, #1
	b.eq	LBB15_11
	add	x8, x19, #8
	mov	x9, #-1
	ldaddl	x9, x8, [x8]
	cmp	x8, #1
	b.ne	LBB15_11
	dmb	ishld
	mov	x0, x19
	mov	w1, #512
	mov	w2, #128
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	b	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB15_11:
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	ret
	.cfi_endproc

	.p2align	2
__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtNtNtCshrG7s5e4uVm_3std6thread6scoped9ScopeDataE9drop_slowCs9nK0Xd5EwPT_19concurrent_assembly:
	.cfi_startproc
	stp	x20, x19, [sp, #-32]!
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	ldr	x19, [x0]
	mov	x0, x19
	ldr	x8, [x0, #16]!
	mov	x9, #-1
	ldaddl	x9, x8, [x8]
	cmp	x8, #1
	b.ne	LBB16_2
	dmb	ishld
	bl	__RNvMsn_NtCscrXPs3M05UR_5alloc4syncINtB5_3ArcNtNtNtCshrG7s5e4uVm_3std6thread6thread5InnerNtNtBM_5alloc6SystemE9drop_slowBM_
LBB16_2:
	cmn	x19, #1
	b.eq	LBB16_5
	add	x8, x19, #8
	mov	x9, #-1
	ldaddl	x9, x8, [x8]
	cmp	x8, #1
	b.ne	LBB16_5
	dmb	ishld
	mov	x0, x19
	mov	w1, #40
	mov	w2, #8
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	b	__RNvCs7urVXOUFJf8_7___rustc14___rust_dealloc
LBB16_5:
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	ret
	.cfi_endproc

	.p2align	2
__RNvXs1g_NtCsi86csyF5gCW_4core3fmtRjNtB6_5Debug3fmtCs9nK0Xd5EwPT_19concurrent_assembly:
	ldr	x0, [x0]
	ldr	w8, [x1, #16]
	tbnz	w8, #25, LBB17_3
	tbnz	w8, #26, LBB17_4
	b	__RNvXsi_NtNtNtCsi86csyF5gCW_4core3fmt3num3impjNtB9_7Display3fmt
LBB17_3:
	b	__RNvXs6_NtNtCsi86csyF5gCW_4core3fmt3numjNtB7_8LowerHex3fmt
LBB17_4:
	b	__RNvXs8_NtNtCsi86csyF5gCW_4core3fmt3numjNtB7_8UpperHex3fmt

	.p2align	2
__RNvXs1i_NtCsi86csyF5gCW_4core3fmtReNtB6_7Display3fmtCs9nK0Xd5EwPT_19concurrent_assembly:
	mov	x2, x1
	ldp	x8, x1, [x0]
	mov	x0, x8
	b	__RNvXsi_NtCsi86csyF5gCW_4core3fmteNtB5_7Display3fmt

	.p2align	2
__RNvXsa_NtCsi86csyF5gCW_4core5arrayAjj4_NtNtB7_3fmt5Debug3fmtCs9nK0Xd5EwPT_19concurrent_assembly:
	.cfi_startproc
	sub	sp, sp, #64
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
	bl	__RNvMsa_NtCsi86csyF5gCW_4core3fmtNtB5_9Formatter10debug_list
	str	x19, [sp, #24]
Lloh66:
	adrp	x20, l_anon.25cbf1bc66902f282ae062428e5506ff.0@PAGE
Lloh67:
	add	x20, x20, l_anon.25cbf1bc66902f282ae062428e5506ff.0@PAGEOFF
	add	x0, sp, #8
	add	x1, sp, #24
	mov	x2, x20
	bl	__RNvMs5_NtNtCsi86csyF5gCW_4core3fmt8buildersNtB5_9DebugList5entry
	add	x8, x19, #8
	str	x8, [sp, #24]
	add	x0, sp, #8
	add	x1, sp, #24
	mov	x2, x20
	bl	__RNvMs5_NtNtCsi86csyF5gCW_4core3fmt8buildersNtB5_9DebugList5entry
	add	x8, x19, #16
	str	x8, [sp, #24]
	add	x0, sp, #8
	add	x1, sp, #24
	mov	x2, x20
	bl	__RNvMs5_NtNtCsi86csyF5gCW_4core3fmt8buildersNtB5_9DebugList5entry
	add	x8, x19, #24
	str	x8, [sp, #24]
	add	x0, sp, #8
	add	x1, sp, #24
	mov	x2, x20
	bl	__RNvMs5_NtNtCsi86csyF5gCW_4core3fmt8buildersNtB5_9DebugList5entry
	add	x0, sp, #8
	bl	__RNvMs5_NtNtCsi86csyF5gCW_4core3fmt8buildersNtB5_9DebugList6finish
	ldp	x29, x30, [sp, #48]
	ldp	x20, x19, [sp, #32]
	add	sp, sp, #64
	ret
	.loh AdrpAdd	Lloh66, Lloh67
	.cfi_endproc

	.p2align	2
__RNvXsq_NtCscrXPs3M05UR_5alloc6stringNtB5_6StringNtNtCsi86csyF5gCW_4core3fmt7Display3fmt:
	mov	x2, x1
	ldp	x8, x1, [x0, #8]
	mov	x0, x8
	b	__RNvXsi_NtCsi86csyF5gCW_4core3fmteNtB5_7Display3fmt

	.globl	_main
	.p2align	2
_main:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	mov	x3, x1
	sxtw	x2, w0
Lloh68:
	adrp	x8, __RNvCs9nK0Xd5EwPT_19concurrent_assembly4main@PAGE
Lloh69:
	add	x8, x8, __RNvCs9nK0Xd5EwPT_19concurrent_assembly4main@PAGEOFF
	str	x8, [sp, #8]
Lloh70:
	adrp	x1, l_anon.25cbf1bc66902f282ae062428e5506ff.1@PAGE
Lloh71:
	add	x1, x1, l_anon.25cbf1bc66902f282ae062428e5506ff.1@PAGEOFF
	add	x0, sp, #8
	mov	w4, #0
	bl	__RNvNtCshrG7s5e4uVm_3std2rt19lang_start_internal
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret
	.loh AdrpAdd	Lloh70, Lloh71
	.loh AdrpAdd	Lloh68, Lloh69

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.25cbf1bc66902f282ae062428e5506ff.0:
	.asciz	"\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNvXs1g_NtCsi86csyF5gCW_4core3fmtRjNtB6_5Debug3fmtCs9nK0Xd5EwPT_19concurrent_assembly

	.p2align	3, 0x0
l_anon.25cbf1bc66902f282ae062428e5506ff.1:
	.asciz	"\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNSNvYNCINvNtCshrG7s5e4uVm_3std2rt10lang_startNtNtBb_7process8ExitCodeE0INtNtNtCsi86csyF5gCW_4core3ops8function6FnOnceuE9call_once6vtableCs9nK0Xd5EwPT_19concurrent_assembly
	.quad	__RNCINvNtCshrG7s5e4uVm_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Cs9nK0Xd5EwPT_19concurrent_assembly
	.quad	__RNCINvNtCshrG7s5e4uVm_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Cs9nK0Xd5EwPT_19concurrent_assembly

	.p2align	3, 0x0
l_anon.25cbf1bc66902f282ae062428e5506ff.2:
	.quad	__RINvNtCsi86csyF5gCW_4core3ptr13drop_in_placeNCINvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_uncheckedNCNvCs9nK0Xd5EwPT_19concurrent_assembly3run0uEs_0EB1J_
	.asciz	"@\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNSNvYNCINvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_uncheckedNCNvCs9nK0Xd5EwPT_19concurrent_assembly3run0uEs_0INtNtNtCsi86csyF5gCW_4core3ops8function6FnOnceuE9call_once6vtableB17_

	.p2align	3, 0x0
l_anon.25cbf1bc66902f282ae062428e5506ff.3:
	.quad	__RINvNtCsi86csyF5gCW_4core3ptr13drop_in_placeNCINvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_uncheckedNCNvCs9nK0Xd5EwPT_19concurrent_assembly3run0uEs_0EB1J_
	.asciz	"@\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNSNvYNCINvNtNtCshrG7s5e4uVm_3std6thread9lifecycle15spawn_uncheckedNCNvCs9nK0Xd5EwPT_19concurrent_assembly3runs_0uEs_0INtNtNtCsi86csyF5gCW_4core3ops8function6FnOnceuE9call_once6vtableB17_

	.section	__TEXT,__const
l_anon.25cbf1bc66902f282ae062428e5506ff.4:
	.ascii	"RUST_MIN_STACK"

l_anon.25cbf1bc66902f282ae062428e5506ff.5:
	.ascii	"failed to spawn thread"

	.section	__TEXT,__cstring,cstring_literals
l_anon.25cbf1bc66902f282ae062428e5506ff.6:
	.asciz	"<MAY1_TOOLCHAIN>/lib/rustlib/src/rust/library/std/src/thread/functions.rs"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.25cbf1bc66902f282ae062428e5506ff.7:
	.quad	l_anon.25cbf1bc66902f282ae062428e5506ff.6
	.asciz	"\334\000\000\000\000\000\000\000\203\000\000\000\035\000\000"

	.section	__TEXT,__const
l_anon.25cbf1bc66902f282ae062428e5506ff.8:
	.ascii	"model-forbidden MP observation"

l_anon.25cbf1bc66902f282ae062428e5506ff.9:
	.ascii	"model-forbidden SB observation"

l_anon.25cbf1bc66902f282ae062428e5506ff.10:
	.ascii	"thread failure"

	.section	__TEXT,__cstring,cstring_literals
l_anon.25cbf1bc66902f282ae062428e5506ff.11:
	.asciz	"\025out-of-domain result \300\001,\300"

	.section	__TEXT,__const
l_anon.25cbf1bc66902f282ae062428e5506ff.12:
	.ascii	"MP-relaxed"

l_anon.25cbf1bc66902f282ae062428e5506ff.13:
	.ascii	"MP-release-acquire"

l_anon.25cbf1bc66902f282ae062428e5506ff.14:
	.ascii	"SB-relaxed"

l_anon.25cbf1bc66902f282ae062428e5506ff.15:
	.ascii	"SB-release-acquire"

l_anon.25cbf1bc66902f282ae062428e5506ff.16:
	.ascii	"SB-seqcst"

	.section	__TEXT,__literal8,8byte_literals
l_anon.25cbf1bc66902f282ae062428e5506ff.17:
	.ascii	"SB-fence"

	.section	__TEXT,__cstring,cstring_literals
l_anon.25cbf1bc66902f282ae062428e5506ff.18:
	.asciz	"\300!: rounds=10000 counts00_01_10_11=\300\001\n"

l_anon.25cbf1bc66902f282ae062428e5506ff.19:
	.asciz	"\300\002: \300\001\n"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.25cbf1bc66902f282ae062428e5506ff.20:
	.quad	__RINvNtCsi86csyF5gCW_4core3ptr13drop_in_placeNtNtNtCshrG7s5e4uVm_3std2io5error5ErrorECs9nK0Xd5EwPT_19concurrent_assembly
	.asciz	"\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNvXNtNtCshrG7s5e4uVm_3std2io5errorNtB2_5ErrorNtNtCsi86csyF5gCW_4core3fmt5Debug3fmt

	.section	__TEXT,__const
l_anon.25cbf1bc66902f282ae062428e5506ff.21:
	.ascii	"threads should not terminate unexpectedly"

	.section	__TEXT,__cstring,cstring_literals
l_anon.25cbf1bc66902f282ae062428e5506ff.22:
	.asciz	"<MAY1_TOOLCHAIN>/lib/rustlib/src/rust/library/std/src/thread/lifecycle.rs"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.25cbf1bc66902f282ae062428e5506ff.23:
	.quad	l_anon.25cbf1bc66902f282ae062428e5506ff.22
	.asciz	"\334\000\000\000\000\000\000\000\342\000\000\000\016\000\000"

	.p2align	3, 0x0
l_anon.25cbf1bc66902f282ae062428e5506ff.24:
	.quad	l_anon.25cbf1bc66902f282ae062428e5506ff.22
	.asciz	"\334\000\000\000\000\000\000\000\346\000\000\000\016\000\000"

.subsections_via_symbols
