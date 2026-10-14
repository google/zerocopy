	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_annotation_complete
	.p2align	2
_annotation_complete:
	.cfi_startproc
	mov	w8, #7
	str	w8, [x0]
	mov	w8, #9
	; InlineAsm Start
	str	w8, [x0]
	; InlineAsm End
	ldr	w0, [x0]
	ret
	.cfi_endproc

	.globl	_annotation_wrong_nomem
	.p2align	2
_annotation_wrong_nomem:
	.cfi_startproc
	mov	w8, #7
	str	w8, [x0]
	mov	w8, #9
	; InlineAsm Start
	str	w8, [x0]
	; InlineAsm End
	mov	w0, #7
	ret
	.cfi_endproc

	.globl	_annotation_wrong_readonly
	.p2align	2
_annotation_wrong_readonly:
	.cfi_startproc
	mov	w8, #7
	str	w8, [x0]
	mov	w8, #9
	; InlineAsm Start
	str	w8, [x0]
	; InlineAsm End
	mov	w0, #7
	ret
	.cfi_endproc

.subsections_via_symbols
