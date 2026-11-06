	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_observe_acquire
	.p2align	2
_observe_acquire:
	.cfi_startproc
	ldapr	w8, [x1]
	ldr	w9, [x0]
	orr	x0, x9, x8, lsl #32
	ret
	.cfi_endproc

	.globl	_observe_relaxed
	.p2align	2
_observe_relaxed:
	.cfi_startproc
	ldr	w8, [x1]
	ldr	w9, [x0]
	orr	x0, x9, x8, lsl #32
	ret
	.cfi_endproc

	.globl	_publish_relaxed
	.p2align	2
_publish_relaxed:
	.cfi_startproc
	mov	w8, #1
	str	w8, [x0]
	str	w8, [x1]
	ret
	.cfi_endproc

	.globl	_publish_release
	.p2align	2
_publish_release:
	.cfi_startproc
	mov	w8, #1
	str	w8, [x0]
	stlr	w8, [x1]
	ret
	.cfi_endproc

	.globl	_store_then_load_fenced
	.p2align	2
_store_then_load_fenced:
	.cfi_startproc
	mov	w8, #1
	str	w8, [x0]
	dmb	ish
	ldr	w0, [x1]
	ret
	.cfi_endproc

	.globl	_store_then_load_relaxed
	.p2align	2
_store_then_load_relaxed:
	.cfi_startproc
	mov	w8, #1
	str	w8, [x0]
	ldr	w0, [x1]
	ret
	.cfi_endproc

	.globl	_store_then_load_release_acquire
	.p2align	2
_store_then_load_release_acquire:
	.cfi_startproc
	mov	w8, #1
	stlr	w8, [x0]
	ldapr	w0, [x1]
	ret
	.cfi_endproc

	.globl	_store_then_load_seqcst
	.p2align	2
_store_then_load_seqcst:
	.cfi_startproc
	mov	w8, #1
	stlr	w8, [x0]
	ldar	w0, [x1]
	ret
	.cfi_endproc

.subsections_via_symbols
