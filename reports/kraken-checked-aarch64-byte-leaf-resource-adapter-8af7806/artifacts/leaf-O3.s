	.build_version macos, 11, 0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
	.globl	_read_byte_leaf
_read_byte_leaf:
	ldrb	w0, [x0]
	ret
.Lfunc_end__read_byte_leaf:

	.private_extern	__RINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB4_7process8ExitCodeECs3XPOALLYtSm_4leaf
	.globl	__RINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB4_7process8ExitCodeECs3XPOALLYtSm_4leaf
	.p2align	2
__RINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB4_7process8ExitCodeECs3XPOALLYtSm_4leaf:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	str	x0, [sp, #8]
Lloh0:
	adrp	x1, l_anon.385d3e4118c9c54dea788464219e1230.0@PAGE
Lloh1:
	add	x1, x1, l_anon.385d3e4118c9c54dea788464219e1230.0@PAGEOFF
	add	x0, sp, #8
	bl	__RNvNtCs1SSuMAdGM58_3std2rt19lang_start_internal
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret
	.loh AdrpAdd	Lloh0, Lloh1

	.p2align	2
__RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECs3XPOALLYtSm_4leaf:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	blr	x0
	; InlineAsm Start
	; InlineAsm End
	ldp	x29, x30, [sp], #16
	ret

	.p2align	2
__RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Cs3XPOALLYtSm_4leaf:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	ldr	x0, [x0]
	bl	__RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECs3XPOALLYtSm_4leaf
	and	w0, w0, #0xff
	ldp	x29, x30, [sp], #16
	ret

	.p2align	2
__RNSNvYNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtBb_7process8ExitCodeE0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_once6vtableCs3XPOALLYtSm_4leaf:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	ldr	x0, [x0]
	bl	__RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECs3XPOALLYtSm_4leaf
	and	w0, w0, #0xff
	ldp	x29, x30, [sp], #16
	ret

	.private_extern	__RNvCs3XPOALLYtSm_4leaf4main
	.globl	__RNvCs3XPOALLYtSm_4leaf4main
	.p2align	2
__RNvCs3XPOALLYtSm_4leaf4main:
	sub	sp, sp, #304
	stp	x26, x25, [sp, #224]
	stp	x24, x23, [sp, #240]
	stp	x22, x21, [sp, #256]
	stp	x20, x19, [sp, #272]
	stp	x29, x30, [sp, #288]
	add	x29, sp, #288
	mov	w20, #0
	stp	xzr, xzr, [sp]
	mov	w21, #165
	add	x22, sp, #32
	sub	x23, x29, #104
	mov	x24, #435
	movk	x24, #256, lsl #32
LBB4_1:
	mov	x25, #0
	strb	w20, [sp, #23]
	mov	x19, x20
LBB4_2:
	str	x25, [sp, #24]
	strb	w21, [sp, #96]
	movi.16b	v0, #165
	stp	q0, q0, [sp, #64]
	stp	q0, q0, [sp, #32]
	add	x8, x22, x25
	strb	w19, [x8]
	ldrb	w9, [sp, #96]
	strb	w9, [sp, #176]
	ldp	q0, q1, [sp, #32]
	stp	q0, q1, [sp, #112]
	ldp	q0, q1, [sp, #64]
	stp	q0, q1, [sp, #144]
	stur	x8, [x29, #-104]
	; InlineAsm Start
	; InlineAsm End
	ldur	x0, [x29, #-104]
	bl	_checked_read
	ldur	x8, [x29, #-104]
	ldrb	w8, [x8]
	cmp	w8, w0, uxtb
	b.ne	LBB4_8
	mov	x19, x0
	ldrb	w8, [sp, #23]
	cmp	w8, w0, uxtb
	b.ne	LBB4_8
	add	x0, sp, #32
	add	x1, sp, #112
	mov	w2, #65
	bl	_memcmp
	cbnz	w0, LBB4_8
	add	x25, x25, #1
	ldr	x8, [sp, #8]
	mul	x8, x8, x24
	add	x9, x8, w19, uxtb
	ldr	x8, [sp]
	add	x8, x8, #1
	stp	x8, x9, [sp]
	cmp	x25, #65
	b.ne	LBB4_2
	and	w8, w20, #0xff
	add	w20, w8, #1
	tbz	w20, #8, LBB4_1
	mov	x8, sp
Lloh2:
	adrp	x9, __RNvXsd_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impyNtB9_7Display3fmt@GOTPAGE
Lloh3:
	ldr	x9, [x9, __RNvXsd_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impyNtB9_7Display3fmt@GOTPAGEOFF]
	stp	x8, x9, [sp, #112]
	add	x8, sp, #8
Lloh4:
	adrp	x9, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGE
Lloh5:
	ldr	x9, [x9, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGEOFF]
	stp	x8, x9, [sp, #128]
Lloh6:
	adrp	x0, l_anon.385d3e4118c9c54dea788464219e1230.1@PAGE
Lloh7:
	add	x0, x0, l_anon.385d3e4118c9c54dea788464219e1230.1@PAGEOFF
	add	x1, sp, #112
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio6__print
	mov	w0, #0
	b	LBB4_9
LBB4_8:
	add	x8, sp, #23
Lloh8:
	adrp	x9, __RNvXNtNtNtCsjIpoRzUjyHQ_4core3fmt3num3imphNtB6_7Display3fmt@GOTPAGE
Lloh9:
	ldr	x9, [x9, __RNvXNtNtNtCsjIpoRzUjyHQ_4core3fmt3num3imphNtB6_7Display3fmt@GOTPAGEOFF]
	stp	x8, x9, [x29, #-96]
	add	x8, sp, #24
Lloh10:
	adrp	x9, __RNvXsi_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impjNtB9_7Display3fmt@GOTPAGE
Lloh11:
	ldr	x9, [x9, __RNvXsi_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impjNtB9_7Display3fmt@GOTPAGEOFF]
	stp	x8, x9, [x29, #-80]
Lloh12:
	adrp	x0, l_anon.385d3e4118c9c54dea788464219e1230.2@PAGE
Lloh13:
	add	x0, x0, l_anon.385d3e4118c9c54dea788464219e1230.2@PAGEOFF
	sub	x1, x29, #96
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio7__eprint
	mov	w0, #1
LBB4_9:
	ldp	x29, x30, [sp, #288]
	ldp	x20, x19, [sp, #272]
	ldp	x22, x21, [sp, #256]
	ldp	x24, x23, [sp, #240]
	ldp	x26, x25, [sp, #224]
	add	sp, sp, #304
	ret
	.loh AdrpAdd	Lloh6, Lloh7
	.loh AdrpLdrGot	Lloh4, Lloh5
	.loh AdrpLdrGot	Lloh2, Lloh3
	.loh AdrpAdd	Lloh12, Lloh13
	.loh AdrpLdrGot	Lloh10, Lloh11
	.loh AdrpLdrGot	Lloh8, Lloh9

	.globl	_checked_read
	.p2align	2
_checked_read:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	bl	_read_byte_leaf
	ldp	x29, x30, [sp], #16
	ret

	.globl	_main
	.p2align	2
_main:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	mov	x3, x1
	sxtw	x2, w0
Lloh14:
	adrp	x8, __RNvCs3XPOALLYtSm_4leaf4main@PAGE
Lloh15:
	add	x8, x8, __RNvCs3XPOALLYtSm_4leaf4main@PAGEOFF
	str	x8, [sp, #8]
Lloh16:
	adrp	x1, l_anon.385d3e4118c9c54dea788464219e1230.0@PAGE
Lloh17:
	add	x1, x1, l_anon.385d3e4118c9c54dea788464219e1230.0@PAGEOFF
	add	x0, sp, #8
	mov	w4, #0
	bl	__RNvNtCs1SSuMAdGM58_3std2rt19lang_start_internal
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret
	.loh AdrpAdd	Lloh16, Lloh17
	.loh AdrpAdd	Lloh14, Lloh15

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.385d3e4118c9c54dea788464219e1230.0:
	.asciz	"\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNSNvYNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtBb_7process8ExitCodeE0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_once6vtableCs3XPOALLYtSm_4leaf
	.quad	__RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Cs3XPOALLYtSm_4leaf
	.quad	__RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Cs3XPOALLYtSm_4leaf

	.section	__TEXT,__const
l_anon.385d3e4118c9c54dea788464219e1230.1:
	.asciz	"\t{\"cases\":\300\r,\"checksum\":\"\303 \000\000i\020\000\037\",\"valid_reference_only\":true}\n"

	.section	__TEXT,__cstring,cstring_literals
l_anon.385d3e4118c9c54dea788464219e1230.2:
	.asciz	"\023disagreement value=\300\b offset=\300\001\n"

.subsections_via_symbols
