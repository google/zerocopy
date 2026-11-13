	.file	"stack_probe.3f9c3f566e408f32-cgu.0"
	.section	.text.frame_3k,"ax",@progbits
	.globl	frame_3k
	.p2align	2
	.type	frame_3k,@function
frame_3k:
.Lfunc_begin0:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x28, x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -8
	.cfi_offset w28, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	sub	sp, sp, #3088
	ldr	xzr, [sp]
	mov	w1, w0
	add	x0, sp, #8
	mov	w2, #3072
	add	x19, sp, #8
	bl	memset
	stur	x19, [x29, #-8]
	sub	x8, x29, #8
	//APP
	//NO_APP
	ldrb	w0, [sp, #1032]
	add	sp, sp, #3088
	.cfi_def_cfa wsp, 32
	ldp	x28, x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end0:
	.size	frame_3k, .Lfunc_end0-frame_3k
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.frame_3k
	.xword	.Lfunc_begin0
	.ascii	"\260\030"
	.section	.text.frame_3k,"ax",@progbits

	.section	.text.frame_70k,"ax",@progbits
	.globl	frame_70k
	.p2align	2
	.type	frame_70k,@function
frame_70k:
.Lfunc_begin1:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x28, x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -8
	.cfi_offset w28, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	sub	x9, sp, #17, lsl #12
.LBB1_1:
	sub	sp, sp, #1, lsl #12
	ldr	xzr, [sp]
	cmp	sp, x9
	b.ne	.LBB1_1
	sub	sp, sp, #2064
	mov	w2, #6144
	ldr	xzr, [sp]
	mov	w1, w0
	add	x0, sp, #8
	movk	w2, #1, lsl #16
	add	x19, sp, #8
	bl	memset
	stur	x19, [x29, #-8]
	sub	x8, x29, #8
	//APP
	//NO_APP
	mov	w8, #65536
	ldrb	w0, [x19, x8]
	add	sp, sp, #17, lsl #12
	add	sp, sp, #2064
	.cfi_def_cfa wsp, 32
	ldp	x28, x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end1:
	.size	frame_70k, .Lfunc_end1-frame_70k
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.frame_70k
	.xword	.Lfunc_begin1
	.ascii	"\260\260\004"
	.section	.text.frame_70k,"ax",@progbits

	.section	.text.frame_8k,"ax",@progbits
	.globl	frame_8k
	.p2align	2
	.type	frame_8k,@function
frame_8k:
.Lfunc_begin2:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x28, x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -8
	.cfi_offset w28, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	sub	sp, sp, #1, lsl #12
	ldr	xzr, [sp]
	sub	sp, sp, #1, lsl #12
	ldr	xzr, [sp], #-16
	mov	w1, w0
	add	x0, sp, #8
	mov	w2, #8192
	add	x19, sp, #8
	bl	memset
	stur	x19, [x29, #-8]
	sub	x8, x29, #8
	//APP
	//NO_APP
	mov	w8, #4096
	ldrb	w0, [x19, x8]
	add	sp, sp, #2, lsl #12
	add	sp, sp, #16
	.cfi_def_cfa wsp, 32
	ldp	x28, x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end2:
	.size	frame_8k, .Lfunc_end2-frame_8k
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.frame_8k
	.xword	.Lfunc_begin2
	.ascii	"\260@"
	.section	.text.frame_8k,"ax",@progbits

	.section	.text.overaligned_frame,"ax",@progbits
	.globl	overaligned_frame
	.p2align	2
	.type	overaligned_frame,@function
overaligned_frame:
.Lfunc_begin3:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	sub	x9, sp, #112
	and	sp, x9, #0xffffffffffffffc0
	dup	v0.16b, w0
	mov	x0, sp
	stp	q0, q0, [sp]
	stp	q0, q0, [sp, #32]
	blr	x1
	ldrb	w0, [sp]
	mov	sp, x29
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end3:
	.size	overaligned_frame, .Lfunc_end3-overaligned_frame
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.overaligned_frame
	.xword	.Lfunc_begin3
	.ascii	"\200\001"
	.section	.text.overaligned_frame,"ax",@progbits

	.section	.text.redzone_leaf,"ax",@progbits
	.globl	redzone_leaf
	.p2align	2
	.type	redzone_leaf,@function
redzone_leaf:
.Lfunc_begin4:
	.cfi_startproc
	sub	sp, sp, #80
	.cfi_def_cfa_offset 80
	eor	x8, x1, x0
	eor	x9, x3, x2
	stp	x0, x1, [sp, #8]
	stp	x8, x9, [sp, #40]
	add	x8, x2, x0
	add	x9, x3, x1
	stp	x8, x9, [sp, #56]
	add	x8, sp, #8
	add	x9, sp, #72
	stp	x2, x3, [sp, #24]
	str	x8, [sp, #72]
	//APP
	//NO_APP
	ldr	x8, [sp, #8]
	ldr	x9, [sp, #64]
	add	x0, x9, x8
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	ret
.Lfunc_end4:
	.size	redzone_leaf, .Lfunc_end4-redzone_leaf
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.redzone_leaf
	.xword	.Lfunc_begin4
	.byte	80
	.section	.text.redzone_leaf,"ax",@progbits

	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
