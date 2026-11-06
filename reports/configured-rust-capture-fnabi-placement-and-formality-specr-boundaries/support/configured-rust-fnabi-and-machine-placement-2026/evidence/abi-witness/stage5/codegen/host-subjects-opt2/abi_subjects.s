	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_abi_c_big
	.p2align	2
_abi_c_big:
	ldr	q0, [x0]
	str	q0, [x8]
	ldr	x9, [x0, #16]
	str	x9, [x8, #16]
	ret

	.globl	_abi_c_fp
	.p2align	2
_abi_c_fp:
	fcvt	d0, s0
	fadd	d0, d1, d0
	ret

	.globl	_abi_c_hfa
	.p2align	2
_abi_c_hfa:
	ret

	.globl	_abi_c_narrow
	.p2align	2
_abi_c_narrow:
	mov	w8, w0
	sxtw	x9, w1
	eor	x8, x9, x8
	mov	w9, w2
	eor	x0, x8, x9
	ret

	.globl	_abi_c_pair
	.p2align	2
_abi_c_pair:
	mov	w1, w1
	ret

	.globl	_abi_c_raw
	.p2align	2
_abi_c_raw:
	ret

	.globl	_abi_interior
	.p2align	2
_abi_interior:
	ret

	.globl	_abi_rust_narrow
	.p2align	2
_abi_rust_narrow:
	and	x8, x0, #0xff
	sxth	x9, w1
	eor	x8, x9, x8
	mov	w9, w2
	eor	x0, x8, x9
	ret

	.globl	_abi_rust_tuple
	.p2align	2
_abi_rust_tuple:
	ret

	.globl	_abi_shared
	.p2align	2
_abi_shared:
	ldr	x0, [x0]
	ret

	.globl	_abi_slice
	.p2align	2
_abi_slice:
	mov	x0, x1
	ret

	.globl	_abi_stack_driver
	.p2align	2
_abi_stack_driver:
	sub	sp, sp, #48
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	ldr	q0, [x29, #16]
	ldp	x8, x9, [x29, #32]
	stp	x8, x9, [sp, #16]
	str	q0, [sp]
	bl	_abi_opaque_twelve
	add	x0, x0, #1
	ldp	x29, x30, [sp, #32]
	add	sp, sp, #48
	ret

	.globl	_abi_track
	.p2align	2
_abi_track:
	ldr	w8, [x1, #16]
	eor	x0, x0, x8
	ret

	.globl	_abi_unique
	.p2align	2
_abi_unique:
	ldr	x8, [x0]
	add	x8, x8, #1
	str	x8, [x0]
	mov	x0, x8
	ret

	.globl	_abi_unit
	.p2align	2
_abi_unit:
	ret

	.globl	_abi_vararg_driver
	.p2align	2
_abi_vararg_driver:
	sub	sp, sp, #48
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	str	xzr, [sp, #16]
	str	d0, [sp, #8]
	str	x0, [sp]
	mov	w0, #1
	bl	_abi_opaque_vararg
	add	x0, x0, #1
	ldp	x29, x30, [sp, #32]
	add	sp, sp, #48
	ret

	.globl	_abi_system_pair
_abi_system_pair = _abi_c_pair
	.globl	_abi_rust_big
_abi_rust_big = _abi_c_big
	.globl	_abi_system_big
_abi_system_big = _abi_c_big
	.globl	_abi_system_narrow
_abi_system_narrow = _abi_c_narrow
.subsections_via_symbols
