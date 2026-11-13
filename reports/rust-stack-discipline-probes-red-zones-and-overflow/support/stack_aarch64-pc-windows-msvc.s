	.def	"@feat.00";
	.scl	3;
	.type	0;
	.endef
	.globl	"@feat.00"
"@feat.00" = 0
	.file	"stack_probe.3f9c3f566e408f32-cgu.0"
	.def	frame_3k;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,frame_3k,unique,0
	.globl	frame_3k
	.p2align	2
frame_3k:
.Lfunc_begin0:
.seh_proc frame_3k
	str	x19, [sp, #-32]!
	.seh_save_reg_x	x19, 32
	str	x28, [sp, #8]
	.seh_save_reg	x28, 8
	stp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	x29, sp, #16
	.seh_add_fp	16
	.seh_endprologue
	sub	sp, sp, #3088
	mov	w1, w0
	add	x0, sp, #8
	mov	w2, #3072
	add	x19, sp, #8
	bl	memset
	stur	x19, [x29, #-24]
	sub	x8, x29, #24
	//APP
	//NO_APP
	ldrb	w0, [sp, #1032]
	.seh_startepilogue
	add	sp, sp, #3088
	.seh_stackalloc	3088
	ldp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	ldr	x28, [sp, #8]
	.seh_save_reg	x28, 8
	ldr	x19, [sp], #32
	.seh_save_reg_x	x19, 32
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.def	frame_70k;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,frame_70k,unique,1
	.globl	frame_70k
	.p2align	2
frame_70k:
.Lfunc_begin1:
.seh_proc frame_70k
	str	x19, [sp, #-32]!
	.seh_save_reg_x	x19, 32
	str	x28, [sp, #8]
	.seh_save_reg	x28, 8
	stp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	x29, sp, #16
	.seh_add_fp	16
	.seh_endprologue
	mov	x15, #4481
	bl	__chkstk
	sub	sp, sp, x15, lsl #4
	mov	w2, #6144
	mov	w1, w0
	add	x0, sp, #8
	movk	w2, #1, lsl #16
	add	x19, sp, #8
	bl	memset
	stur	x19, [x29, #-24]
	sub	x8, x29, #24
	//APP
	//NO_APP
	mov	w8, #65536
	ldrb	w0, [x19, x8]
	.seh_startepilogue
	add	sp, sp, #17, lsl #12
	.seh_stackalloc	69632
	add	sp, sp, #2064
	.seh_stackalloc	2064
	ldp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	ldr	x28, [sp, #8]
	.seh_save_reg	x28, 8
	ldr	x19, [sp], #32
	.seh_save_reg_x	x19, 32
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.def	frame_8k;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,frame_8k,unique,2
	.globl	frame_8k
	.p2align	2
frame_8k:
.Lfunc_begin2:
.seh_proc frame_8k
	str	x19, [sp, #-32]!
	.seh_save_reg_x	x19, 32
	str	x28, [sp, #8]
	.seh_save_reg	x28, 8
	stp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	x29, sp, #16
	.seh_add_fp	16
	.seh_endprologue
	mov	x15, #513
	bl	__chkstk
	sub	sp, sp, x15, lsl #4
	mov	w1, w0
	add	x0, sp, #8
	mov	w2, #8192
	add	x19, sp, #8
	bl	memset
	stur	x19, [x29, #-24]
	sub	x8, x29, #24
	//APP
	//NO_APP
	mov	w8, #4096
	ldrb	w0, [x19, x8]
	.seh_startepilogue
	add	sp, sp, #2, lsl #12
	.seh_stackalloc	8192
	add	sp, sp, #16
	.seh_stackalloc	16
	ldp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	ldr	x28, [sp, #8]
	.seh_save_reg	x28, 8
	ldr	x19, [sp], #32
	.seh_save_reg_x	x19, 32
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.def	overaligned_frame;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,overaligned_frame,unique,3
	.globl	overaligned_frame
	.p2align	2
overaligned_frame:
.Lfunc_begin3:
.seh_proc overaligned_frame
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	mov	x29, sp
	.seh_set_fp
	.seh_endprologue
	sub	x9, sp, #112
	and	sp, x9, #0xffffffffffffffc0
	dup	v0.16b, w0
	mov	x0, sp
	stp	q0, q0, [sp]
	stp	q0, q0, [sp, #32]
	blr	x1
	ldrb	w0, [sp]
	.seh_startepilogue
	mov	sp, x29
	.seh_set_fp
	ldp	x29, x30, [sp], #16
	.seh_save_fplr_x	16
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.def	redzone_leaf;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,redzone_leaf,unique,4
	.globl	redzone_leaf
	.p2align	2
redzone_leaf:
.Lfunc_begin4:
.seh_proc redzone_leaf
	sub	sp, sp, #80
	.seh_stackalloc	80
	.seh_endprologue
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
	.seh_startepilogue
	add	sp, sp, #80
	.seh_stackalloc	80
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

