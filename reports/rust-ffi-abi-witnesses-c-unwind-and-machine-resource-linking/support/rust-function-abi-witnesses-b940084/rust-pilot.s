	.build_version macos, 11, 0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
	.globl	_naked_add
_naked_add:
	add	x0, x0, x1
	ret
.Lfunc_end__naked_add:
	.p2align	2
	.globl	_naked_store
_naked_store:
	str	x1, [x0]
	ret
.Lfunc_end__naked_store:

	.globl	_c_pair
	.p2align	2
_c_pair:
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	ret

	.globl	_c_triple
	.p2align	2
_c_triple:
	ldr	x9, [x0]
	ldur	q0, [x0, #8]
	ext.16b	v0, v0, v0, #8
	str	q0, [x8]
	str	x9, [x8, #16]
	ret

	.globl	_inline_add
	.p2align	2
_inline_add:
	; InlineAsm Start
	add	x0, x0, x1
	; InlineAsm End
	ret

	.globl	_inline_load
	.p2align	2
_inline_load:
	; InlineAsm Start
	ldrb	w8, [x0]
	; InlineAsm End
	and	w0, w8, #0xff
	ret

	.globl	_rust_add
	.p2align	2
_rust_add:
	add	x0, x1, x0
	ret

	.globl	_rust_pair
	.p2align	2
_rust_pair:
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	ret

	.globl	_rust_slice
	.p2align	2
_rust_slice:
	mov	x0, x1
	ret

	.globl	_rust_unit
	.p2align	2
_rust_unit:
	ret

.subsections_via_symbols
