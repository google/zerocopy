	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RNvMs4_NtNtCsi86csyF5gCW_4core5panic8locationNtB5_8Location4lineCsjplKSa1E9lu_12abi_subjects:
	ldr	w0, [x0, #16]
	ret

	.p2align	2
__RNvMs4_NtNtCsi86csyF5gCW_4core5panic8locationNtB5_8Location6callerCsjplKSa1E9lu_12abi_subjects:
	sub	sp, sp, #16
	str	x0, [sp, #8]
	ldr	x0, [sp, #8]
	add	sp, sp, #16
	ret

	.globl	_abi_c_big
	.p2align	2
_abi_c_big:
	mov	x9, x8
	ldr	q0, [x0]
	str	q0, [x9]
	ldr	x8, [x0, #16]
	str	x8, [x9, #16]
	ret

	.globl	_abi_c_fp
	.p2align	2
_abi_c_fp:
	fcvt	d0, s0
	fadd	d0, d0, d1
	ret

	.globl	_abi_c_hfa
	.p2align	2
_abi_c_hfa:
	sub	sp, sp, #48
	str	s0, [sp, #16]
	str	s1, [sp, #20]
	str	s2, [sp, #24]
	str	s3, [sp, #28]
	ldr	q0, [sp, #16]
	str	q0, [sp]
	ldr	q0, [sp]
	str	q0, [sp, #32]
	ldr	s0, [sp, #32]
	ldr	s1, [sp, #36]
	ldr	s2, [sp, #40]
	ldr	s3, [sp, #44]
	add	sp, sp, #48
	ret

	.globl	_abi_c_narrow
	.p2align	2
_abi_c_narrow:
	mov	x8, x0
	and	x8, x8, #0xff
	mov	x9, x1
	sxth	x9, w9
	eor	x8, x8, x9
	mov	x9, x2
	and	x9, x9, #0x1
	eor	x0, x8, x9
	ret

	.globl	_abi_c_pair
	.p2align	2
_abi_c_pair:
	sub	sp, sp, #48
	str	x0, [sp, #16]
	str	x1, [sp, #24]
	ldr	q0, [sp, #16]
	str	q0, [sp]
	ldr	x9, [sp]
	ldr	w8, [sp, #8]
	str	x9, [sp, #32]
	str	w8, [sp, #40]
	ldr	x0, [sp, #32]
	ldr	x1, [sp, #40]
	add	sp, sp, #48
	ret

	.globl	_abi_c_raw
	.p2align	2
_abi_c_raw:
	ret

	.globl	_abi_interior
	.p2align	2
_abi_interior:
	ret

	.globl	_abi_rust_big
	.p2align	2
_abi_rust_big:
	mov	x9, x8
	ldr	q0, [x0]
	str	q0, [x9]
	ldr	x8, [x0, #16]
	str	x8, [x9, #16]
	ret

	.globl	_abi_rust_narrow
	.p2align	2
_abi_rust_narrow:
	mov	x8, x0
	and	x8, x8, #0xff
	mov	x9, x1
	sxth	x9, w9
	eor	x8, x8, x9
	mov	x9, x2
	and	x9, x9, #0x1
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
	ldr	x12, [x29, #16]
	ldr	x11, [x29, #24]
	ldr	x10, [x29, #32]
	ldr	x8, [x29, #40]
	mov	x9, sp
	str	x12, [x9]
	str	x11, [x9, #8]
	str	x10, [x9, #16]
	str	x8, [x9, #24]
	bl	_abi_opaque_twelve
	add	x0, x0, #1
	ldp	x29, x30, [sp, #32]
	add	sp, sp, #48
	ret

	.globl	_abi_system_big
	.p2align	2
_abi_system_big:
	mov	x9, x8
	ldr	q0, [x0]
	str	q0, [x9]
	ldr	x8, [x0, #16]
	str	x8, [x9, #16]
	ret

	.globl	_abi_system_narrow
	.p2align	2
_abi_system_narrow:
	mov	x8, x0
	and	x8, x8, #0xff
	mov	x9, x1
	sxth	x9, w9
	eor	x8, x8, x9
	mov	x9, x2
	and	x9, x9, #0x1
	eor	x0, x8, x9
	ret

	.globl	_abi_system_pair
	.p2align	2
_abi_system_pair:
	sub	sp, sp, #48
	str	x0, [sp, #16]
	str	x1, [sp, #24]
	ldr	q0, [sp, #16]
	str	q0, [sp]
	ldr	x9, [sp]
	ldr	w8, [sp, #8]
	str	x9, [sp, #32]
	str	w8, [sp, #40]
	ldr	x0, [sp, #32]
	ldr	x1, [sp, #40]
	add	sp, sp, #48
	ret

	.globl	_abi_track
	.p2align	2
_abi_track:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	str	x0, [sp, #8]
	mov	x0, x1
	bl	__RNvMs4_NtNtCsi86csyF5gCW_4core5panic8locationNtB5_8Location6callerCsjplKSa1E9lu_12abi_subjects
	bl	__RNvMs4_NtNtCsi86csyF5gCW_4core5panic8locationNtB5_8Location4lineCsjplKSa1E9lu_12abi_subjects
	mov	x8, x0
	ldr	x0, [sp, #8]
	mov	w8, w8
	eor	x0, x0, x8
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret

	.globl	_abi_unique
	.p2align	2
_abi_unique:
	ldr	x8, [x0]
	add	x8, x8, #1
	str	x8, [x0]
	ldr	x0, [x0]
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
	mov	x8, sp
	mov	x9, x0
	str	x9, [x8]
	str	d0, [x8, #8]
	str	xzr, [x8, #16]
	mov	w0, #1
	bl	_abi_opaque_vararg
	add	x0, x0, #1
	ldp	x29, x30, [sp, #32]
	add	sp, sp, #48
	ret

.subsections_via_symbols
