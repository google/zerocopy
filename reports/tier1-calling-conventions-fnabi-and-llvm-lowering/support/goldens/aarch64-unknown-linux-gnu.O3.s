	.file	"calling_conv_corpus.75f08b44548a9e00-cgu.0"
	.section	.text._RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,"ax",@progbits
	.globl	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.p2align	2
	.type	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,@function
_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind:
	.cfi_startproc
.LBB0_1:
	b	.LBB0_1
.Lfunc_end0:
	.size	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind, .Lfunc_end0-_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.cfi_endproc

	.section	.text.cc_c_nounwind,"ax",@progbits
	.globl	cc_c_nounwind
	.p2align	2
	.type	cc_c_nounwind,@function
cc_c_nounwind:
	.cfi_startproc
	add	w0, w0, #1
	ret
.Lfunc_end1:
	.size	cc_c_nounwind, .Lfunc_end1-cc_c_nounwind
	.cfi_endproc

	.section	.text.cc_c_unwind,"ax",@progbits
	.globl	cc_c_unwind
	.p2align	2
	.type	cc_c_unwind,@function
cc_c_unwind:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	blr	x8
	add	w0, w0, #1
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end2:
	.size	cc_c_unwind, .Lfunc_end2-cc_c_unwind
	.cfi_endproc

	.section	.text.cc_f16_f128,"ax",@progbits
	.globl	cc_f16_f128
	.p2align	2
	.type	cc_f16_f128,@function
cc_f16_f128:
	.cfi_startproc
	mov	v0.16b, v1.16b
	ret
.Lfunc_end3:
	.size	cc_f16_f128, .Lfunc_end3-cc_f16_f128
	.cfi_endproc

	.section	.text.cc_hfa2_f32,"ax",@progbits
	.globl	cc_hfa2_f32
	.p2align	2
	.type	cc_hfa2_f32,@function
cc_hfa2_f32:
	.cfi_startproc
	fmov	s2, s0
	fmov	s0, s1
	fmov	s1, s2
	ret
.Lfunc_end4:
	.size	cc_hfa2_f32, .Lfunc_end4-cc_hfa2_f32
	.cfi_endproc

	.section	.text.cc_hfa4_f32,"ax",@progbits
	.globl	cc_hfa4_f32
	.p2align	2
	.type	cc_hfa4_f32,@function
cc_hfa4_f32:
	.cfi_startproc
	fmov	s4, s1
	fmov	s5, s0
	fmov	s0, s3
	fmov	s1, s2
	fmov	s2, s4
	fmov	s3, s5
	ret
.Lfunc_end5:
	.size	cc_hfa4_f32, .Lfunc_end5-cc_hfa4_f32
	.cfi_endproc

	.section	.text.cc_hfa5_f32,"ax",@progbits
	.globl	cc_hfa5_f32
	.p2align	2
	.type	cc_hfa5_f32,@function
cc_hfa5_f32:
	.cfi_startproc
	ldur	q0, [x0, #4]
	ldr	s1, [x0]
	ext	v0.16b, v0.16b, v0.16b, #12
	str	s1, [x8, #16]
	str	q0, [x8]
	ret
.Lfunc_end6:
	.size	cc_hfa5_f32, .Lfunc_end6-cc_hfa5_f32
	.cfi_endproc

	.section	.text.cc_hva2_c,"ax",@progbits
	.globl	cc_hva2_c
	.p2align	2
	.type	cc_hva2_c,@function
cc_hva2_c:
	.cfi_startproc
	ldp	q1, q0, [x0]
	stp	q0, q1, [x8]
	ret
.Lfunc_end7:
	.size	cc_hva2_c, .Lfunc_end7-cc_hva2_c
	.cfi_endproc

	.section	.text.cc_many_args,"ax",@progbits
	.globl	cc_many_args
	.p2align	2
	.type	cc_many_args,@function
cc_many_args:
	.cfi_startproc
	fadd	d0, d0, d1
	ldr	d1, [sp, #8]
	ldr	x9, [sp]
	add	x11, x7, x0
	fcvtzu	x8, d1
	add	x9, x11, x9
	fadd	d0, d0, d2
	add	x8, x9, x8
	fadd	d0, d0, d3
	fadd	d0, d0, d4
	fadd	d0, d0, d5
	fadd	d0, d0, d6
	fadd	d0, d0, d7
	fcvtzu	x10, d0
	add	x0, x8, x10
	ret
.Lfunc_end8:
	.size	cc_many_args, .Lfunc_end8-cc_many_args
	.cfi_endproc

	.section	.text.cc_mixed_16b,"ax",@progbits
	.globl	cc_mixed_16b
	.p2align	2
	.type	cc_mixed_16b,@function
cc_mixed_16b:
	.cfi_startproc
	add	x0, x0, #1
	ret
.Lfunc_end9:
	.size	cc_mixed_16b, .Lfunc_end9-cc_mixed_16b
	.cfi_endproc

	.section	.text.cc_narrow_int,"ax",@progbits
	.globl	cc_narrow_int
	.p2align	2
	.type	cc_narrow_int,@function
cc_narrow_int:
	.cfi_startproc
	add	w8, w2, w3
	add	w9, w1, w0
	add	w0, w9, w8
	ret
.Lfunc_end10:
	.size	cc_narrow_int, .Lfunc_end10-cc_narrow_int
	.cfi_endproc

	.section	.text.cc_overaligned_16b,"ax",@progbits
	.globl	cc_overaligned_16b
	.p2align	2
	.type	cc_overaligned_16b,@function
cc_overaligned_16b:
	.cfi_startproc
	add	x8, x1, w0, uxtw
	add	x0, x8, x2
	ret
.Lfunc_end11:
	.size	cc_overaligned_16b, .Lfunc_end11-cc_overaligned_16b
	.cfi_endproc

	.section	.text.cc_rust_call,"ax",@progbits
	.globl	cc_rust_call
	.p2align	2
	.type	cc_rust_call,@function
cc_rust_call:
	.cfi_startproc
	add	x8, x0, w1, uxtw
	add	x0, x8, x2
	ret
.Lfunc_end12:
	.size	cc_rust_call, .Lfunc_end12-cc_rust_call
	.cfi_endproc

	.section	.text.cc_rust_cold_ret,"ax",@progbits
	.globl	cc_rust_cold_ret
	.p2align	2
	.type	cc_rust_cold_ret,@function
cc_rust_cold_ret:
	.cfi_startproc
	add	x0, x1, x0
	ret
.Lfunc_end13:
	.size	cc_rust_cold_ret, .Lfunc_end13-cc_rust_cold_ret
	.cfi_endproc

	.section	.text.cc_rust_cold_void,"ax",@progbits
	.globl	cc_rust_cold_void
	.p2align	2
	.type	cc_rust_cold_void,@function
cc_rust_cold_void:
	.cfi_startproc
	str	w1, [x0]
	ret
.Lfunc_end14:
	.size	cc_rust_cold_void, .Lfunc_end14-cc_rust_cold_void
	.cfi_endproc

	.section	.text.cc_rust_f32,"ax",@progbits
	.globl	cc_rust_f32
	.p2align	2
	.type	cc_rust_f32,@function
cc_rust_f32:
	.cfi_startproc
	fadd	s0, s0, s1
	ret
.Lfunc_end15:
	.size	cc_rust_f32, .Lfunc_end15-cc_rust_f32
	.cfi_endproc

	.section	.text.cc_rust_pair,"ax",@progbits
	.globl	cc_rust_pair
	.p2align	2
	.type	cc_rust_pair,@function
cc_rust_pair:
	.cfi_startproc
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	ret
.Lfunc_end16:
	.size	cc_rust_pair, .Lfunc_end16-cc_rust_pair
	.cfi_endproc

	.section	.text.cc_rust_slice,"ax",@progbits
	.globl	cc_rust_slice
	.p2align	2
	.type	cc_rust_slice,@function
cc_rust_slice:
	.cfi_startproc
	mov	x0, x1
	ret
.Lfunc_end17:
	.size	cc_rust_slice, .Lfunc_end17-cc_rust_slice
	.cfi_endproc

	.section	.text.cc_rust_triple,"ax",@progbits
	.globl	cc_rust_triple
	.p2align	2
	.type	cc_rust_triple,@function
cc_rust_triple:
	.cfi_startproc
	ldur	q0, [x0, #8]
	ldr	x9, [x0]
	ext	v0.16b, v0.16b, v0.16b, #8
	str	x9, [x8, #16]
	str	q0, [x8]
	ret
.Lfunc_end18:
	.size	cc_rust_triple, .Lfunc_end18-cc_rust_triple
	.cfi_endproc

	.section	.text.cc_struct_16b,"ax",@progbits
	.globl	cc_struct_16b
	.p2align	2
	.type	cc_struct_16b,@function
cc_struct_16b:
	.cfi_startproc
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	ret
.Lfunc_end19:
	.size	cc_struct_16b, .Lfunc_end19-cc_struct_16b
	.cfi_endproc

	.section	.text.cc_struct_8b,"ax",@progbits
	.globl	cc_struct_8b
	.p2align	2
	.type	cc_struct_8b,@function
cc_struct_8b:
	.cfi_startproc
	ror	x0, x0, #32
	ret
.Lfunc_end20:
	.size	cc_struct_8b, .Lfunc_end20-cc_struct_8b
	.cfi_endproc

	.section	.text.cc_track_caller,"ax",@progbits
	.globl	cc_track_caller
	.p2align	2
	.type	cc_track_caller,@function
cc_track_caller:
	.cfi_startproc
	mov	x0, x1
	ret
.Lfunc_end21:
	.size	cc_track_caller, .Lfunc_end21-cc_track_caller
	.cfi_endproc

	.section	.text.cc_u128,"ax",@progbits
	.globl	cc_u128
	.p2align	2
	.type	cc_u128,@function
cc_u128:
	.cfi_startproc
	adds	x0, x2, w0, uxtw
	cinc	x1, x3, hs
	ret
.Lfunc_end22:
	.size	cc_u128, .Lfunc_end22-cc_u128
	.cfi_endproc

	.section	.text.cc_variadic_caller,"ax",@progbits
	.globl	cc_variadic_caller
	.p2align	2
	.type	cc_variadic_caller,@function
cc_variadic_caller:
	.cfi_startproc
	sxtb	w4, w2
	mov	x5, x0
	mov	w0, w1
	mov	w1, #1
	mov	w2, #2
	mov	w3, #3
	br	x5
.Lfunc_end23:
	.size	cc_variadic_caller, .Lfunc_end23-cc_variadic_caller
	.cfi_endproc

	.section	.text.cc_vec128_c,"ax",@progbits
	.globl	cc_vec128_c
	.p2align	2
	.type	cc_vec128_c,@function
cc_vec128_c:
	.cfi_startproc
	ret
.Lfunc_end24:
	.size	cc_vec128_c, .Lfunc_end24-cc_vec128_c
	.cfi_endproc

	.section	.text.cc_vec128_rust,"ax",@progbits
	.globl	cc_vec128_rust
	.p2align	2
	.type	cc_vec128_rust,@function
cc_vec128_rust:
	.cfi_startproc
	ldr	q0, [x0]
	str	q0, [x8]
	ret
.Lfunc_end25:
	.size	cc_vec128_rust, .Lfunc_end25-cc_vec128_rust
	.cfi_endproc

	.globl	cc_struct_24b
	.type	cc_struct_24b,@function
cc_struct_24b = cc_rust_triple
	.globl	cc_zst_and_transparent
	.type	cc_zst_and_transparent,@function
cc_zst_and_transparent = cc_c_nounwind
	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
