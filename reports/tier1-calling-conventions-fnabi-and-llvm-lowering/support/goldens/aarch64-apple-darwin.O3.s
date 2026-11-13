	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	__RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.p2align	2
__RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind:
	.cfi_startproc
LBB0_1:
	b	LBB0_1
	.cfi_endproc

	.globl	_cc_c_nounwind
	.p2align	2
_cc_c_nounwind:
	.cfi_startproc
	add	w0, w0, #1
	ret
	.cfi_endproc

	.globl	_cc_c_unwind
	.p2align	2
_cc_c_unwind:
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
	add	w0, w0, #1
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.globl	_cc_f16_f128
	.p2align	2
_cc_f16_f128:
	.cfi_startproc
	mov.16b	v0, v1
	ret
	.cfi_endproc

	.globl	_cc_hfa2_f32
	.p2align	2
_cc_hfa2_f32:
	.cfi_startproc
	mov.16b	v2, v0
	mov.16b	v0, v1
	mov.16b	v1, v2
	ret
	.cfi_endproc

	.globl	_cc_hfa4_f32
	.p2align	2
_cc_hfa4_f32:
	.cfi_startproc
	mov.16b	v4, v1
	mov.16b	v5, v0
	mov.16b	v0, v3
	mov.16b	v1, v2
	mov.16b	v2, v4
	mov.16b	v3, v5
	ret
	.cfi_endproc

	.globl	_cc_hfa5_f32
	.p2align	2
_cc_hfa5_f32:
	.cfi_startproc
	ldr	s0, [x0]
	ldur	q1, [x0, #4]
	ext.16b	v1, v1, v1, #12
	str	q1, [x8]
	str	s0, [x8, #16]
	ret
	.cfi_endproc

	.globl	_cc_hva2_c
	.p2align	2
_cc_hva2_c:
	.cfi_startproc
	ldp	q1, q0, [x0]
	stp	q0, q1, [x8]
	ret
	.cfi_endproc

	.globl	_cc_many_args
	.p2align	2
_cc_many_args:
	.cfi_startproc
	ldr	d16, [sp, #8]
	ldr	x8, [sp]
	fcvtzu	x9, d16
	add	x10, x7, x0
	add	x8, x10, x8
	fadd	d0, d0, d1
	fadd	d0, d0, d2
	fadd	d0, d0, d3
	fadd	d0, d0, d4
	fadd	d0, d0, d5
	fadd	d0, d0, d6
	fadd	d0, d0, d7
	fcvtzu	x10, d0
	add	x8, x8, x9
	add	x0, x8, x10
	ret
	.cfi_endproc

	.globl	_cc_mixed_16b
	.p2align	2
_cc_mixed_16b:
	.cfi_startproc
	add	x0, x0, #1
	ret
	.cfi_endproc

	.globl	_cc_narrow_int
	.p2align	2
_cc_narrow_int:
	.cfi_startproc
	add	w8, w1, w0
	add	w9, w2, w3
	add	w8, w8, w9
	sxtb	w0, w8
	ret
	.cfi_endproc

	.globl	_cc_overaligned_16b
	.p2align	2
_cc_overaligned_16b:
	.cfi_startproc
	add	x8, x1, w0, uxtw
	add	x0, x8, x2
	ret
	.cfi_endproc

	.globl	_cc_rust_call
	.p2align	2
_cc_rust_call:
	.cfi_startproc
	add	x8, x0, w1, uxtw
	add	x0, x8, x2
	ret
	.cfi_endproc

	.globl	_cc_rust_cold_ret
	.p2align	2
_cc_rust_cold_ret:
	.cfi_startproc
	add	x0, x1, x0
	ret
	.cfi_endproc

	.globl	_cc_rust_cold_void
	.p2align	2
_cc_rust_cold_void:
	.cfi_startproc
	str	w1, [x0]
	ret
	.cfi_endproc

	.globl	_cc_rust_f32
	.p2align	2
_cc_rust_f32:
	.cfi_startproc
	fadd	s0, s0, s1
	ret
	.cfi_endproc

	.globl	_cc_rust_pair
	.p2align	2
_cc_rust_pair:
	.cfi_startproc
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	ret
	.cfi_endproc

	.globl	_cc_rust_slice
	.p2align	2
_cc_rust_slice:
	.cfi_startproc
	mov	x0, x1
	ret
	.cfi_endproc

	.globl	_cc_rust_triple
	.p2align	2
_cc_rust_triple:
	.cfi_startproc
	ldr	x9, [x0]
	ldur	q0, [x0, #8]
	ext.16b	v0, v0, v0, #8
	str	q0, [x8]
	str	x9, [x8, #16]
	ret
	.cfi_endproc

	.globl	_cc_struct_16b
	.p2align	2
_cc_struct_16b:
	.cfi_startproc
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	ret
	.cfi_endproc

	.globl	_cc_struct_8b
	.p2align	2
_cc_struct_8b:
	.cfi_startproc
	ror	x0, x0, #32
	ret
	.cfi_endproc

	.globl	_cc_track_caller
	.p2align	2
_cc_track_caller:
	.cfi_startproc
	mov	x0, x1
	ret
	.cfi_endproc

	.globl	_cc_u128
	.p2align	2
_cc_u128:
	.cfi_startproc
	adds	x0, x1, w0, uxtw
	cinc	x1, x2, hs
	ret
	.cfi_endproc

	.globl	_cc_variadic_caller
	.p2align	2
_cc_variadic_caller:
	.cfi_startproc
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	str	x2, [sp, #8]
	str	d0, [sp]
	mov	x0, x1
	mov	w1, #1
	mov	w2, #2
	mov	w3, #3
	blr	x8
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.globl	_cc_vec128_c
	.p2align	2
_cc_vec128_c:
	.cfi_startproc
	ret
	.cfi_endproc

	.globl	_cc_vec128_rust
	.p2align	2
_cc_vec128_rust:
	.cfi_startproc
	ldr	q0, [x0]
	str	q0, [x8]
	ret
	.cfi_endproc

	.globl	_cc_struct_24b
_cc_struct_24b = _cc_rust_triple
	.globl	_cc_zst_and_transparent
_cc_zst_and_transparent = _cc_c_nounwind
.subsections_via_symbols
