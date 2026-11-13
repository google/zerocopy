	.def	"@feat.00";
	.scl	3;
	.type	0;
	.endef
	.globl	"@feat.00"
"@feat.00" = 0
	.file	"calling_conv_corpus.75f08b44548a9e00-cgu.0"
	.def	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,unique,0
	.globl	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.p2align	2
_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind:
.LBB0_1:
	b	.LBB0_1

	.def	cc_c_nounwind;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_c_nounwind,unique,1
	.globl	cc_c_nounwind
	.p2align	2
cc_c_nounwind:
	add	w0, w0, #1
	ret

	.def	cc_c_unwind;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_c_unwind,unique,2
	.globl	cc_c_unwind
	.p2align	2
cc_c_unwind:
.seh_proc cc_c_unwind
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	mov	x29, sp
	.seh_set_fp
	.seh_endprologue
	mov	x8, x0
	mov	w0, w1
	blr	x8
	add	w0, w0, #1
	.seh_startepilogue
	ldp	x29, x30, [sp], #16
	.seh_save_fplr_x	16
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.def	cc_f16_f128;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_f16_f128,unique,3
	.globl	cc_f16_f128
	.p2align	2
cc_f16_f128:
	mov	v0.16b, v1.16b
	ret

	.def	cc_hfa2_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_hfa2_f32,unique,4
	.globl	cc_hfa2_f32
	.p2align	2
cc_hfa2_f32:
	fmov	s2, s0
	fmov	s0, s1
	fmov	s1, s2
	ret

	.def	cc_hfa4_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_hfa4_f32,unique,5
	.globl	cc_hfa4_f32
	.p2align	2
cc_hfa4_f32:
	fmov	s4, s1
	fmov	s5, s0
	fmov	s0, s3
	fmov	s1, s2
	fmov	s2, s4
	fmov	s3, s5
	ret

	.def	cc_hfa5_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_hfa5_f32,unique,6
	.globl	cc_hfa5_f32
	.p2align	2
cc_hfa5_f32:
	ldur	q0, [x0, #4]
	ldr	s1, [x0]
	ext	v0.16b, v0.16b, v0.16b, #12
	str	s1, [x8, #16]
	str	q0, [x8]
	ret

	.def	cc_hva2_c;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_hva2_c,unique,7
	.globl	cc_hva2_c
	.p2align	2
cc_hva2_c:
	ldp	q1, q0, [x0]
	stp	q0, q1, [x8]
	ret

	.def	cc_many_args;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_many_args,unique,8
	.globl	cc_many_args
	.p2align	2
cc_many_args:
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

	.def	cc_mixed_16b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_mixed_16b,unique,9
	.globl	cc_mixed_16b
	.p2align	2
cc_mixed_16b:
	add	x0, x0, #1
	ret

	.def	cc_narrow_int;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_narrow_int,unique,10
	.globl	cc_narrow_int
	.p2align	2
cc_narrow_int:
	add	w8, w2, w3
	add	w9, w1, w0
	add	w0, w9, w8
	ret

	.def	cc_overaligned_16b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_overaligned_16b,unique,11
	.globl	cc_overaligned_16b
	.p2align	2
cc_overaligned_16b:
	add	x8, x2, w0, uxtw
	add	x0, x8, x3
	ret

	.def	cc_rust_call;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_call,unique,12
	.globl	cc_rust_call
	.p2align	2
cc_rust_call:
	add	x8, x0, w1, uxtw
	add	x0, x8, x2
	ret

	.def	cc_rust_cold_ret;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_cold_ret,unique,13
	.globl	cc_rust_cold_ret
	.p2align	2
cc_rust_cold_ret:
	add	x0, x1, x0
	ret

	.def	cc_rust_cold_void;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_cold_void,unique,14
	.globl	cc_rust_cold_void
	.p2align	2
cc_rust_cold_void:
	str	w1, [x0]
	ret

	.def	cc_rust_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_f32,unique,15
	.globl	cc_rust_f32
	.p2align	2
cc_rust_f32:
	fadd	s0, s0, s1
	ret

	.def	cc_rust_pair;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_pair,unique,16
	.globl	cc_rust_pair
	.p2align	2
cc_rust_pair:
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	ret

	.def	cc_rust_slice;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_slice,unique,17
	.globl	cc_rust_slice
	.p2align	2
cc_rust_slice:
	mov	x0, x1
	ret

	.def	cc_rust_triple;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_triple,unique,18
	.globl	cc_rust_triple
	.p2align	2
cc_rust_triple:
	ldur	q0, [x0, #8]
	ldr	x9, [x0]
	ext	v0.16b, v0.16b, v0.16b, #8
	str	x9, [x8, #16]
	str	q0, [x8]
	ret

	.def	cc_struct_16b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_struct_16b,unique,19
	.globl	cc_struct_16b
	.p2align	2
cc_struct_16b:
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	ret

	.def	cc_struct_8b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_struct_8b,unique,20
	.globl	cc_struct_8b
	.p2align	2
cc_struct_8b:
	ror	x0, x0, #32
	ret

	.def	cc_track_caller;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_track_caller,unique,21
	.globl	cc_track_caller
	.p2align	2
cc_track_caller:
	mov	x0, x1
	ret

	.def	cc_u128;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_u128,unique,22
	.globl	cc_u128
	.p2align	2
cc_u128:
	adds	x0, x2, w0, uxtw
	cinc	x1, x3, hs
	ret

	.def	cc_variadic_caller;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_variadic_caller,unique,23
	.globl	cc_variadic_caller
	.p2align	2
cc_variadic_caller:
	fmov	x4, d0
	sxtb	w5, w2
	mov	x6, x0
	mov	w0, w1
	mov	w1, #1
	mov	w2, #2
	mov	w3, #3
	br	x6

	.def	cc_vec128_c;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_vec128_c,unique,24
	.globl	cc_vec128_c
	.p2align	2
cc_vec128_c:
	ret

	.def	cc_vec128_rust;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_vec128_rust,unique,25
	.globl	cc_vec128_rust
	.p2align	2
cc_vec128_rust:
	ldr	q0, [x0]
	str	q0, [x8]
	ret

	.globl	cc_struct_24b
	.def	cc_struct_24b;
	.scl	2;
	.type	32;
	.endef
cc_struct_24b = cc_rust_triple
	.globl	cc_zst_and_transparent
	.def	cc_zst_and_transparent;
	.scl	2;
	.type	32;
	.endef
cc_zst_and_transparent = cc_c_nounwind
