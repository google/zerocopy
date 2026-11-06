	.build_version macos, 11, 0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
	.globl	_read_byte_leaf
_read_byte_leaf:
	ldrb	w0, [x0]
	ret
.Lfunc_end__read_byte_leaf:

	.p2align	2
__RINvMNtNtCsjIpoRzUjyHQ_4core3fmt2rtNtB3_8Argument11new_displayhECs3XPOALLYtSm_4leaf:
	sub	sp, sp, #16
	str	x0, [sp]
	adrp	x9, __RNvXNtNtNtCsjIpoRzUjyHQ_4core3fmt3num3imphNtB6_7Display3fmt@GOTPAGE
	ldr	x9, [x9, __RNvXNtNtNtCsjIpoRzUjyHQ_4core3fmt3num3imphNtB6_7Display3fmt@GOTPAGEOFF]
	str	x9, [sp, #8]
	ldr	q0, [sp]
	str	q0, [x8]
	add	sp, sp, #16
	ret

	.p2align	2
__RINvMNtNtCsjIpoRzUjyHQ_4core3fmt2rtNtB3_8Argument11new_displayjECs3XPOALLYtSm_4leaf:
	sub	sp, sp, #16
	str	x0, [sp]
	adrp	x9, __RNvXsi_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impjNtB9_7Display3fmt@GOTPAGE
	ldr	x9, [x9, __RNvXsi_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impjNtB9_7Display3fmt@GOTPAGEOFF]
	str	x9, [sp, #8]
	ldr	q0, [sp]
	str	q0, [x8]
	add	sp, sp, #16
	ret

	.p2align	2
__RINvMNtNtCsjIpoRzUjyHQ_4core3fmt2rtNtB3_8Argument11new_displayyECs3XPOALLYtSm_4leaf:
	sub	sp, sp, #16
	str	x0, [sp]
	adrp	x9, __RNvXsd_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impyNtB9_7Display3fmt@GOTPAGE
	ldr	x9, [x9, __RNvXsd_NtNtNtCsjIpoRzUjyHQ_4core3fmt3num3impyNtB9_7Display3fmt@GOTPAGEOFF]
	str	x9, [sp, #8]
	ldr	q0, [sp]
	str	q0, [x8]
	add	sp, sp, #16
	ret

	.p2align	2
__RINvMNtNtCsjIpoRzUjyHQ_4core3fmt2rtNtB3_8Argument13new_lower_hexyECs3XPOALLYtSm_4leaf:
	sub	sp, sp, #16
	str	x0, [sp]
	adrp	x9, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGE
	ldr	x9, [x9, __RNvXsC_NtNtCsjIpoRzUjyHQ_4core3fmt3numyNtB7_8LowerHex3fmt@GOTPAGEOFF]
	str	x9, [sp, #8]
	ldr	q0, [sp]
	str	q0, [x8]
	add	sp, sp, #16
	ret

	.p2align	2
__RINvMs2_NtCsjIpoRzUjyHQ_4core3fmtNtB6_9Arguments3newKj22_Kj2_ECs3XPOALLYtSm_4leaf:
	ret

	.p2align	2
__RINvMs2_NtCsjIpoRzUjyHQ_4core3fmtNtB6_9Arguments3newKj41_Kj2_ECs3XPOALLYtSm_4leaf:
	ret

	.private_extern	__RINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB4_7process8ExitCodeECs3XPOALLYtSm_4leaf
	.globl	__RINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB4_7process8ExitCodeECs3XPOALLYtSm_4leaf
	.p2align	2
__RINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB4_7process8ExitCodeECs3XPOALLYtSm_4leaf:
	sub	sp, sp, #48
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	mov	x8, x0
	str	x1, [sp, #8]
	mov	x0, x2
	ldr	x2, [sp, #8]
	str	x0, [sp, #16]
	mov	x4, x3
	ldr	x3, [sp, #16]
	sub	x0, x29, #8
	stur	x8, [x29, #-8]
	adrp	x1, l_anon.385d3e4118c9c54dea788464219e1230.0@PAGE
	add	x1, x1, l_anon.385d3e4118c9c54dea788464219e1230.0@PAGEOFF
	bl	__RNvNtCs1SSuMAdGM58_3std2rt19lang_start_internal
	ldp	x29, x30, [sp, #32]
	add	sp, sp, #48
	ret

	.p2align	2
__RINvNtCsjIpoRzUjyHQ_4core4hint9black_boxRhECs3XPOALLYtSm_4leaf:
	sub	sp, sp, #16
	add	x8, sp, #8
	str	x0, [sp, #8]
	; InlineAsm Start
	; InlineAsm End
	ldr	x0, [sp, #8]
	add	sp, sp, #16
	ret

	.p2align	2
__RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECs3XPOALLYtSm_4leaf:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	bl	__RNvYFENtNtCs1SSuMAdGM58_3std7process8ExitCodeINtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_onceCs3XPOALLYtSm_4leaf
	; InlineAsm Start
	; InlineAsm End
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret

	.p2align	2
__RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Cs3XPOALLYtSm_4leaf:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	ldr	x0, [x0]
	bl	__RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFENtNtB6_7process8ExitCodeB19_ECs3XPOALLYtSm_4leaf
	bl	__RNvXsX_NtCs1SSuMAdGM58_3std7processNtB5_8ExitCodeNtB5_11Termination6reportCs3XPOALLYtSm_4leaf
	and	w0, w0, #0xff
	ldp	x29, x30, [sp], #16
	ret

	.p2align	2
__RNSNvYNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtBb_7process8ExitCodeE0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_once6vtableCs3XPOALLYtSm_4leaf:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	ldr	x0, [x0]
	bl	__RNvYNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB9_7process8ExitCodeE0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_onceCs3XPOALLYtSm_4leaf
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret

	.private_extern	__RNvCs3XPOALLYtSm_4leaf4main
	.globl	__RNvCs3XPOALLYtSm_4leaf4main
	.p2align	2
__RNvCs3XPOALLYtSm_4leaf4main:
	sub	sp, sp, #432
	stp	x28, x27, [sp, #400]
	stp	x29, x30, [sp, #416]
	add	x29, sp, #416
	sub	x8, x29, #160
	str	x8, [sp, #32]
	str	xzr, [sp, #48]
	str	xzr, [sp, #56]
	mov	w0, #0
	mov	w1, #-1
	bl	__RNvMs5_NtNtCsjIpoRzUjyHQ_4core3ops5rangeINtB5_14RangeInclusivehE3newCs3XPOALLYtSm_4leaf
	ldr	x8, [sp, #32]
	lsr	w9, w0, #16
	strh	w0, [x8, #132]
	sturb	w9, [x29, #-26]
	ldrh	w9, [x8, #132]
	strh	w9, [sp, #70]
	ldurb	w9, [x29, #-26]
	strb	w9, [sp, #72]
	ldrh	w9, [sp, #70]
	strh	w9, [x8, #136]
	ldrb	w9, [sp, #72]
	sturb	w9, [x29, #-22]
	ldrh	w8, [x8, #136]
	ldurb	w9, [x29, #-22]
	orr	w0, w8, w9, lsl #16
	bl	__RNvXNtNtNtCsjIpoRzUjyHQ_4core4iter6traits7collectINtNtNtB8_3ops5range14RangeInclusivehENtB2_12IntoIterator9into_iterCs3XPOALLYtSm_4leaf
	ldr	x8, [sp, #32]
	lsr	w9, w0, #16
	strh	w0, [x8, #140]
	sturb	w9, [x29, #-18]
	ldrh	w8, [x8, #140]
	strh	w8, [sp, #66]
	ldurb	w8, [x29, #-18]
	strb	w8, [sp, #68]
	ldrh	w8, [sp, #66]
	strh	w8, [sp, #74]
	ldrb	w8, [sp, #68]
	strb	w8, [sp, #76]
	b	LBB11_1
LBB11_1:
	add	x0, sp, #74
	bl	__RNvXsd_NtNtCsjIpoRzUjyHQ_4core4iter5rangeINtNtNtB9_3ops5range14RangeInclusivehENtNtNtB7_6traits8iterator8Iterator4nextCs3XPOALLYtSm_4leaf
	and	w8, w0, #0x1
	strb	w8, [sp, #77]
	strb	w1, [sp, #78]
	ldrb	w8, [sp, #77]
	tbnz	w8, #0, LBB11_2
	b	LBB11_3
LBB11_2:
	ldrb	w8, [sp, #78]
	strb	w8, [sp, #79]
	mov	x0, #0
	mov	w8, #65
	mov	x1, x8
	bl	__RNvXNtNtNtCsjIpoRzUjyHQ_4core4iter6traits7collectINtNtNtB8_3ops5range5RangejENtB2_12IntoIterator9into_iterCs3XPOALLYtSm_4leaf
	str	x0, [sp, #80]
	str	x1, [sp, #88]
	b	LBB11_5
LBB11_3:
	sub	x8, x29, #64
	add	x0, sp, #48
	bl	__RINvMNtNtCsjIpoRzUjyHQ_4core3fmt2rtNtB3_8Argument11new_displayyECs3XPOALLYtSm_4leaf
	sub	x8, x29, #48
	add	x0, sp, #56
	bl	__RINvMNtNtCsjIpoRzUjyHQ_4core3fmt2rtNtB3_8Argument13new_lower_hexyECs3XPOALLYtSm_4leaf
	ldr	x8, [sp, #32]
	ldr	q0, [x8, #96]
	sub	x1, x29, #96
	str	q0, [x8, #64]
	ldr	q0, [x8, #112]
	str	q0, [x8, #80]
	adrp	x0, l_anon.385d3e4118c9c54dea788464219e1230.1@PAGE
	add	x0, x0, l_anon.385d3e4118c9c54dea788464219e1230.1@PAGEOFF
	bl	__RINvMs2_NtCsjIpoRzUjyHQ_4core3fmtNtB6_9Arguments3newKj41_Kj2_ECs3XPOALLYtSm_4leaf
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio6__print
	strb	wzr, [sp, #47]
	b	LBB11_4
LBB11_4:
	ldrb	w0, [sp, #47]
	ldp	x29, x30, [sp, #416]
	ldp	x28, x27, [sp, #400]
	add	sp, sp, #432
	ret
LBB11_5:
	add	x0, sp, #80
	bl	__RNvXs4_NtNtCsjIpoRzUjyHQ_4core4iter5rangeINtNtNtB9_3ops5range5RangejENtNtNtB7_6traits8iterator8Iterator4nextCs3XPOALLYtSm_4leaf
	str	x0, [sp, #96]
	str	x1, [sp, #104]
	ldr	x8, [sp, #96]
	tbnz	w8, #0, LBB11_6
	b	LBB11_1
LBB11_6:
	ldr	x8, [sp, #104]
	str	x8, [sp, #112]
	add	x0, sp, #126
	mov	w8, #65
	mov	x2, x8
	mov	w1, #-91
	bl	_memset
	ldr	x8, [sp, #112]
	subs	x8, x8, #65
	b.lo	LBB11_7
	b	LBB11_8
LBB11_7:
	ldr	x9, [sp, #112]
	add	x1, sp, #126
	ldrb	w8, [sp, #79]
	strb	w8, [x1, x9]
	add	x0, sp, #191
	mov	w8, #65
	mov	x2, x8
	bl	_memcpy
	ldr	x8, [sp, #112]
	subs	x8, x8, #65
	b.lo	LBB11_9
	b	LBB11_10
LBB11_8:
	ldr	x0, [sp, #112]
	mov	w8, #65
	mov	x1, x8
	adrp	x2, l_anon.385d3e4118c9c54dea788464219e1230.3@PAGE
	add	x2, x2, l_anon.385d3e4118c9c54dea788464219e1230.3@PAGEOFF
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking18panic_bounds_check
LBB11_9:
	ldr	x9, [sp, #112]
	add	x8, sp, #126
	add	x0, x8, x9
	bl	__RINvNtCsjIpoRzUjyHQ_4core4hint9black_boxRhECs3XPOALLYtSm_4leaf
	str	x0, [sp, #16]
	bl	_checked_read
	mov	x8, x0
	ldr	x0, [sp, #16]
	str	w8, [sp, #24]
	bl	__RNvCs3XPOALLYtSm_4leaf9rust_read
	mov	x8, x0
	ldr	w0, [sp, #24]
	str	w8, [sp, #28]
	ldrb	w8, [sp, #79]
	uxtb	w8, w8
	subs	w8, w8, w0, uxtb
	b.ne	LBB11_12
	b	LBB11_11
LBB11_10:
	ldr	x0, [sp, #112]
	mov	w8, #65
	mov	x1, x8
	adrp	x2, l_anon.385d3e4118c9c54dea788464219e1230.4@PAGE
	add	x2, x2, l_anon.385d3e4118c9c54dea788464219e1230.4@PAGEOFF
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking18panic_bounds_check
LBB11_11:
	ldr	w9, [sp, #28]
	ldr	w8, [sp, #24]
	and	w8, w8, #0xff
	subs	w8, w8, w9, uxtb
	b.ne	LBB11_12
	b	LBB11_13
LBB11_12:
	sub	x8, x29, #128
	add	x0, sp, #79
	bl	__RINvMNtNtCsjIpoRzUjyHQ_4core3fmt2rtNtB3_8Argument11new_displayhECs3XPOALLYtSm_4leaf
	sub	x8, x29, #112
	add	x0, sp, #112
	bl	__RINvMNtNtCsjIpoRzUjyHQ_4core3fmt2rtNtB3_8Argument11new_displayjECs3XPOALLYtSm_4leaf
	ldr	x8, [sp, #32]
	ldr	q0, [x8, #32]
	sub	x1, x29, #160
	str	q0, [x8]
	ldr	q0, [x8, #48]
	str	q0, [x8, #16]
	adrp	x0, l_anon.385d3e4118c9c54dea788464219e1230.6@PAGE
	add	x0, x0, l_anon.385d3e4118c9c54dea788464219e1230.6@PAGEOFF
	bl	__RINvMs2_NtCsjIpoRzUjyHQ_4core3fmtNtB6_9Arguments3newKj22_Kj2_ECs3XPOALLYtSm_4leaf
	bl	__RNvNtNtCs1SSuMAdGM58_3std2io5stdio7__eprint
	mov	w8, #1
	strb	w8, [sp, #47]
	b	LBB11_4
LBB11_13:
	add	x0, sp, #126
	add	x1, sp, #191
	bl	__RNvXNtNtCsjIpoRzUjyHQ_4core5array8equalityAhj41_NtNtB6_3cmp9PartialEq2neCs3XPOALLYtSm_4leaf
	tbnz	w0, #0, LBB11_12
	b	LBB11_14
LBB11_14:
	ldr	w9, [sp, #24]
	ldr	x8, [sp, #56]
	mov	x10, #435
	movk	x10, #256, lsl #32
	mul	x8, x8, x10
	mov	x0, x9
	mov	x9, x0
	add	x8, x8, w9, uxtb
	str	x8, [sp, #56]
	ldr	x9, [sp, #48]
	add	x8, x9, #1
	str	x8, [sp, #8]
	subs	x8, x8, x9
	b.lo	LBB11_16
	b	LBB11_15
LBB11_15:
	ldr	x8, [sp, #8]
	str	x8, [sp, #48]
	b	LBB11_5
LBB11_16:
	adrp	x0, l_anon.385d3e4118c9c54dea788464219e1230.5@PAGE
	add	x0, x0, l_anon.385d3e4118c9c54dea788464219e1230.5@PAGEOFF
	bl	__RNvNtNtCsjIpoRzUjyHQ_4core9panicking11panic_const24panic_const_add_overflow

	.p2align	2
__RNvCs3XPOALLYtSm_4leaf9rust_read:
	ldrb	w0, [x0]
	ret

	.p2align	2
__RNvMs5_NtNtCsjIpoRzUjyHQ_4core3ops5rangeINtB5_14RangeInclusivehE3newCs3XPOALLYtSm_4leaf:
	sub	sp, sp, #16
	strb	w0, [sp, #13]
	strb	w1, [sp, #14]
	strb	wzr, [sp, #12]
	ldrh	w8, [sp, #12]
	ldrb	w9, [sp, #14]
	orr	w0, w8, w9, lsl #16
	add	sp, sp, #16
	ret

	.p2align	2
__RNvNvMs9_NtCsjIpoRzUjyHQ_4core3numj13unchecked_add18precondition_checkCs3XPOALLYtSm_4leaf:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	str	x2, [sp, #8]
	add	x8, x0, x1
	subs	x8, x8, x0
	b.lo	LBB14_2
	b	LBB14_1
LBB14_1:
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret
LBB14_2:
	ldr	x3, [sp, #8]
	adrp	x0, l_anon.385d3e4118c9c54dea788464219e1230.7@PAGE
	add	x0, x0, l_anon.385d3e4118c9c54dea788464219e1230.7@PAGEOFF
	mov	w8, #373
	mov	x1, x8
	mov	w8, #0
	and	w2, w8, #0x1
	bl	__RNvNtCsjIpoRzUjyHQ_4core9panicking18panic_nounwind_fmt

	.p2align	2
__RNvXNtNtCsjIpoRzUjyHQ_4core5array8equalityAhj41_NtNtB6_3cmp9PartialEq2neCs3XPOALLYtSm_4leaf:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	bl	__RNvXs7_NtNtCsjIpoRzUjyHQ_4core5array8equalityhINtB5_11SpecArrayEqhKj41_E7spec_neCs3XPOALLYtSm_4leaf
	ldp	x29, x30, [sp], #16
	ret

	.p2align	2
__RNvXNtNtNtCsjIpoRzUjyHQ_4core4iter6traits7collectINtNtNtB8_3ops5range14RangeInclusivehENtB2_12IntoIterator9into_iterCs3XPOALLYtSm_4leaf:
	sub	sp, sp, #16
	lsr	w8, w0, #16
	strh	w0, [sp, #8]
	strb	w8, [sp, #10]
	ldrh	w8, [sp, #8]
	strh	w8, [sp, #4]
	ldrb	w8, [sp, #10]
	strb	w8, [sp, #6]
	ldrh	w8, [sp, #4]
	strh	w8, [sp, #12]
	ldrb	w8, [sp, #6]
	strb	w8, [sp, #14]
	ldrh	w8, [sp, #12]
	ldrb	w9, [sp, #14]
	orr	w0, w8, w9, lsl #16
	add	sp, sp, #16
	ret

	.p2align	2
__RNvXNtNtNtCsjIpoRzUjyHQ_4core4iter6traits7collectINtNtNtB8_3ops5range5RangejENtB2_12IntoIterator9into_iterCs3XPOALLYtSm_4leaf:
	ret

	.p2align	2
__RNvXs3_NtNtCsjIpoRzUjyHQ_4core4iter5rangeINtNtNtB9_3ops5range5RangejENtB5_17RangeIteratorImpl9spec_nextCs3XPOALLYtSm_4leaf:
	sub	sp, sp, #64
	stp	x29, x30, [sp, #48]
	add	x29, sp, #48
	str	x0, [sp, #24]
	ldr	x8, [x0]
	ldr	x9, [x0, #8]
	subs	x8, x8, x9
	b.lo	LBB18_2
	b	LBB18_1
LBB18_1:
	stur	xzr, [x29, #-16]
	b	LBB18_3
LBB18_2:
	ldr	x8, [sp, #24]
	ldr	x0, [x8]
	str	x0, [sp, #8]
	mov	w8, #1
	mov	x1, x8
	str	x1, [sp, #16]
	bl	__RNvXsL_NtNtCsjIpoRzUjyHQ_4core4iter5rangejNtB5_4Step17forward_uncheckedCs3XPOALLYtSm_4leaf
	ldr	x10, [sp, #24]
	ldr	x9, [sp, #8]
	ldr	x8, [sp, #16]
	str	x0, [x10]
	stur	x9, [x29, #-8]
	stur	x8, [x29, #-16]
	b	LBB18_3
LBB18_3:
	ldur	x0, [x29, #-16]
	ldur	x1, [x29, #-8]
	ldp	x29, x30, [sp, #48]
	add	sp, sp, #64
	ret

	.p2align	2
__RNvXs4_NtNtCsjIpoRzUjyHQ_4core4iter5rangeINtNtNtB9_3ops5range5RangejENtNtNtB7_6traits8iterator8Iterator4nextCs3XPOALLYtSm_4leaf:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	bl	__RNvXs3_NtNtCsjIpoRzUjyHQ_4core4iter5rangeINtNtNtB9_3ops5range5RangejENtB5_17RangeIteratorImpl9spec_nextCs3XPOALLYtSm_4leaf
	ldp	x29, x30, [sp], #16
	ret

	.p2align	2
__RNvXs7_NtNtCsjIpoRzUjyHQ_4core5array8equalityhINtB5_11SpecArrayEqhKj41_E7spec_neCs3XPOALLYtSm_4leaf:
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	mov	w8, #65
	mov	x2, x8
	bl	_memcmp
	subs	w8, w0, #0
	cset	w0, ne
	ldp	x29, x30, [sp], #16
	ret

	.p2align	2
__RNvXsD_NtNtCsjIpoRzUjyHQ_4core4iter5rangehNtB5_4Step19forward_overflowingCs3XPOALLYtSm_4leaf:
	sub	sp, sp, #32
	str	w0, [sp, #12]
	str	x1, [sp, #16]
	subs	x8, x1, #255
	b.hi	LBB21_2
	b	LBB21_1
LBB21_1:
	ldr	w10, [sp, #12]
	ldr	x8, [sp, #16]
	strb	w8, [sp, #31]
	strb	wzr, [sp, #30]
	ldrb	w8, [sp, #31]
	add	w9, w10, w8, uxtb
	and	w8, w9, #0xff
	subs	w8, w8, w10, uxtb
	cset	w8, lo
	strb	w9, [sp, #28]
	strb	w8, [sp, #29]
	b	LBB21_3
LBB21_2:
	ldr	w8, [sp, #12]
	ldr	x9, [sp, #16]
	add	w8, w8, w9
	strb	w8, [sp, #28]
	mov	w8, #1
	strb	w8, [sp, #29]
	b	LBB21_3
LBB21_3:
	ldrb	w0, [sp, #28]
	ldrb	w8, [sp, #29]
	and	w1, w8, #0x1
	add	sp, sp, #32
	ret

	.p2align	2
__RNvXsL_NtNtCsjIpoRzUjyHQ_4core4iter5rangejNtB5_4Step17forward_uncheckedCs3XPOALLYtSm_4leaf:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	str	x0, [sp]
	str	x1, [sp, #8]
	b	LBB22_1
LBB22_1:
	ldr	x1, [sp, #8]
	ldr	x0, [sp]
	adrp	x2, l_anon.385d3e4118c9c54dea788464219e1230.9@PAGE
	add	x2, x2, l_anon.385d3e4118c9c54dea788464219e1230.9@PAGEOFF
	bl	__RNvNvMs9_NtCsjIpoRzUjyHQ_4core3numj13unchecked_add18precondition_checkCs3XPOALLYtSm_4leaf
	b	LBB22_2
LBB22_2:
	ldr	x8, [sp]
	ldr	x9, [sp, #8]
	add	x0, x8, x9
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret

	.p2align	2
__RNvXsX_NtCs1SSuMAdGM58_3std7processNtB5_8ExitCodeNtB5_11Termination6reportCs3XPOALLYtSm_4leaf:
	ret

	.p2align	2
__RNvXsd_NtNtCsjIpoRzUjyHQ_4core4iter5rangeINtNtNtB9_3ops5range14RangeInclusivehENtNtNtB7_6traits8iterator8Iterator4nextCs3XPOALLYtSm_4leaf:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	str	x0, [sp]
	ldrb	w8, [x0]
	tbnz	w8, #0, LBB24_2
	b	LBB24_1
LBB24_1:
	ldr	x9, [sp]
	ldrb	w8, [x9, #1]
	ldrb	w9, [x9, #2]
	uxtb	w8, w8
	subs	w8, w8, w9, uxtb
	b.hi	LBB24_4
	b	LBB24_3
LBB24_2:
	b	LBB24_4
LBB24_3:
	ldr	x8, [sp]
	ldrb	w0, [x8, #1]
	mov	w8, #1
	mov	x1, x8
	bl	__RNvXsD_NtNtCsjIpoRzUjyHQ_4core4iter5rangehNtB5_4Step19forward_overflowingCs3XPOALLYtSm_4leaf
	ldr	x10, [sp]
	mov	w8, #1
	and	w9, w1, #0x1
	strb	w9, [x10]
	ldrb	w9, [x10, #1]
	strb	w0, [x10, #1]
	sturb	w9, [x29, #-1]
	sturb	w8, [x29, #-2]
	b	LBB24_5
LBB24_4:
	sturb	wzr, [x29, #-2]
	b	LBB24_5
LBB24_5:
	ldurb	w8, [x29, #-2]
	ldurb	w1, [x29, #-1]
	and	w0, w8, #0x1
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret

	.p2align	2
__RNvYFENtNtCs1SSuMAdGM58_3std7process8ExitCodeINtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_onceCs3XPOALLYtSm_4leaf:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	blr	x0
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret

	.p2align	2
__RNvYNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB9_7process8ExitCodeE0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_onceCs3XPOALLYtSm_4leaf:
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	mov	x8, x0
	mov	x0, sp
	str	x8, [sp]
	bl	__RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB6_7process8ExitCodeE0Cs3XPOALLYtSm_4leaf
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret

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
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x2, x1
	mov	x8, x0
	sxtw	x1, w8
	adrp	x0, __RNvCs3XPOALLYtSm_4leaf4main@PAGE
	add	x0, x0, __RNvCs3XPOALLYtSm_4leaf4main@PAGEOFF
	mov	w3, #0
	bl	__RINvNtCs1SSuMAdGM58_3std2rt10lang_startNtNtB4_7process8ExitCodeECs3XPOALLYtSm_4leaf
	ldp	x29, x30, [sp], #16
	ret
	.cfi_endproc

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
	.asciz	"support/leaf.rs"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.385d3e4118c9c54dea788464219e1230.3:
	.quad	l_anon.385d3e4118c9c54dea788464219e1230.2
	.asciz	"\017\000\000\000\000\000\000\000\035\000\000\000\r\000\000"

	.p2align	3, 0x0
l_anon.385d3e4118c9c54dea788464219e1230.4:
	.quad	l_anon.385d3e4118c9c54dea788464219e1230.2
	.asciz	"\017\000\000\000\000\000\000\000\037\000\000\000#\000\000"

	.p2align	3, 0x0
l_anon.385d3e4118c9c54dea788464219e1230.5:
	.quad	l_anon.385d3e4118c9c54dea788464219e1230.2
	.asciz	"\017\000\000\000\000\000\000\000'\000\000\000\r\000\000"

	.section	__TEXT,__cstring,cstring_literals
l_anon.385d3e4118c9c54dea788464219e1230.6:
	.asciz	"\023disagreement value=\300\b offset=\300\001\n"

	.section	__TEXT,__const
l_anon.385d3e4118c9c54dea788464219e1230.7:
	.ascii	"unsafe precondition(s) violated: usize::unchecked_add cannot overflow\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety."

	.section	__TEXT,__cstring,cstring_literals
l_anon.385d3e4118c9c54dea788464219e1230.8:
	.asciz	"/rustc/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/iter/range.rs"

	.section	__DATA,__const
	.p2align	3, 0x0
l_anon.385d3e4118c9c54dea788464219e1230.9:
	.quad	l_anon.385d3e4118c9c54dea788464219e1230.8
	.asciz	"N\000\000\000\000\000\000\000$\002\000\000\001\000\000"

.subsections_via_symbols
