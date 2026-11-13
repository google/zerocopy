	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_frame_3k
	.p2align	2
_frame_3k:
Lfunc_begin0:
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
	sub	sp, sp, #3088
	ldr	xzr, [sp]
	mov	x1, x0
	add	x19, sp, #8
	add	x0, sp, #8
	mov	w2, #3072
	bl	_memset
	stur	x19, [x29, #-24]
	sub	x8, x29, #24
	; InlineAsm Start
	; InlineAsm End
	ldrb	w0, [sp, #1032]
	add	sp, sp, #3088
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
	.cfi_endproc

	.globl	_frame_70k
	.p2align	2
_frame_70k:
Lfunc_begin1:
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
	sub	x9, sp, #17, lsl #12
LBB1_1:
	sub	sp, sp, #1, lsl #12
	ldr	xzr, [sp]
	cmp	sp, x9
	b.ne	LBB1_1
	sub	sp, sp, #2064
	ldr	xzr, [sp]
	mov	x1, x0
	add	x19, sp, #8
	add	x0, sp, #8
	mov	w2, #6144
	movk	w2, #1, lsl #16
	bl	_memset
	stur	x19, [x29, #-24]
	sub	x8, x29, #24
	; InlineAsm Start
	; InlineAsm End
	mov	w8, #65536
	ldrb	w0, [x19, x8]
	add	sp, sp, #17, lsl #12
	add	sp, sp, #2064
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
	.cfi_endproc

	.globl	_frame_8k
	.p2align	2
_frame_8k:
Lfunc_begin2:
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
	sub	sp, sp, #1, lsl #12
	ldr	xzr, [sp]
	sub	sp, sp, #1, lsl #12
	ldr	xzr, [sp], #-16
	mov	x1, x0
	add	x19, sp, #8
	add	x0, sp, #8
	mov	w2, #8192
	bl	_memset
	stur	x19, [x29, #-24]
	sub	x8, x29, #24
	; InlineAsm Start
	; InlineAsm End
	mov	w8, #4096
	ldrb	w0, [x19, x8]
	add	sp, sp, #2, lsl #12
	add	sp, sp, #16
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
	.cfi_endproc

	.globl	_overaligned_frame
	.p2align	2
_overaligned_frame:
Lfunc_begin3:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	sub	x9, sp, #112
	and	sp, x9, #0xffffffffffffffc0
	dup.16b	v0, w0
	stp	q0, q0, [sp, #32]
	stp	q0, q0, [sp]
	mov	x0, sp
	blr	x1
	ldrb	w0, [sp]
	mov	sp, x29
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.globl	_redzone_leaf
	.p2align	2
_redzone_leaf:
Lfunc_begin4:
	.cfi_startproc
	sub	sp, sp, #80
	.cfi_def_cfa_offset 80
	eor	x8, x1, x0
	eor	x9, x3, x2
	add	x10, x2, x0
	add	x11, x3, x1
	stp	x0, x1, [sp, #8]
	stp	x2, x3, [sp, #24]
	stp	x8, x9, [sp, #40]
	stp	x10, x11, [sp, #56]
	add	x8, sp, #8
	str	x8, [sp, #72]
	add	x8, sp, #72
	; InlineAsm Start
	; InlineAsm End
	ldr	x8, [sp, #8]
	ldr	x9, [sp, #64]
	add	x0, x9, x8
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	ret
	.cfi_endproc

.subsections_via_symbols
