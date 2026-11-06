	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_always_seven
	.p2align	2
_always_seven:
	.cfi_startproc
	mov	w0, #7
	ret
	.cfi_endproc

	.globl	_broken_safe_api
	.p2align	2
_broken_safe_api:
	.cfi_startproc
	mov	w0, #7
	ret
	.cfi_endproc

.subsections_via_symbols
