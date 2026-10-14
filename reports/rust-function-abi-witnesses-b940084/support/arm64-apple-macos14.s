	.build_version macos, 14, 0	sdk_version 27, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_abi_add                        ; -- Begin function abi_add
	.p2align	2
_abi_add:                               ; @abi_add
	.cfi_startproc
; %bb.0:
	add	x0, x1, x0
	ret
	.cfi_endproc
                                        ; -- End function
	.globl	_abi_pair                       ; -- Begin function abi_pair
	.p2align	2
_abi_pair:                              ; @abi_pair
	.cfi_startproc
; %bb.0:
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	ret
	.cfi_endproc
                                        ; -- End function
	.globl	_abi_triple                     ; -- Begin function abi_triple
	.p2align	2
_abi_triple:                            ; @abi_triple
	.cfi_startproc
; %bb.0:
	ldur	q0, [x0, #8]
	ext.16b	v0, v0, v0, #8
	str	q0, [x8]
	ldr	x9, [x0]
	str	x9, [x8, #16]
	ret
	.cfi_endproc
                                        ; -- End function
.subsections_via_symbols
