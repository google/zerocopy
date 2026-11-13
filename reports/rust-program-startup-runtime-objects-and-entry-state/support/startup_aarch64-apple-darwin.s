	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.private_extern	__RINvNtCsdnanKjkF2cC_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.globl	__RINvNtCsdnanKjkF2cC_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.p2align	2
__RINvNtCsdnanKjkF2cC_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	str	x0, [sp, #8]
Lloh0:
	adrp	x1, l_vtable.0@PAGE
Lloh1:
	add	x1, x1, l_vtable.0@PAGEOFF
	add	x0, sp, #8
	bl	__RNvNtCsdnanKjkF2cC_3std2rt19lang_start_internal
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.loh AdrpAdd	Lloh0, Lloh1
	.cfi_endproc

	.p2align	2
__RINvNtNtCsdnanKjkF2cC_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	blr	x0
	; InlineAsm Start
	; InlineAsm End
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.p2align	2
__RNCINvNtCsdnanKjkF2cC_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	ldr	x0, [x0]
	bl	__RINvNtNtCsdnanKjkF2cC_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	mov	w0, #0
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.p2align	2
__RNSNvYNCINvNtCsdnanKjkF2cC_3std2rt10lang_startuE0INtNtNtCs3bJEMBXHbwl_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	ldr	x0, [x0]
	bl	__RINvNtNtCsdnanKjkF2cC_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	mov	w0, #0
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.private_extern	__RNvCslIq7RLtFujA_13startup_probe4main
	.globl	__RNvCslIq7RLtFujA_13startup_probe4main
	.p2align	2
__RNvCslIq7RLtFujA_13startup_probe4main:
	.cfi_startproc
Lloh2:
	adrp	x0, l_alloc_dea25bd652bc4349bac428c742353f74@PAGE
Lloh3:
	add	x0, x0, l_alloc_dea25bd652bc4349bac428c742353f74@PAGEOFF
	mov	w1, #29
	b	__RNvNtNtCsdnanKjkF2cC_3std2io5stdio6__print
	.loh AdrpAdd	Lloh2, Lloh3
	.cfi_endproc

	.globl	_main
	.p2align	2
_main:
	.cfi_startproc
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x3, x1
	sxtw	x2, w0
Lloh4:
	adrp	x8, __RNvCslIq7RLtFujA_13startup_probe4main@PAGE
Lloh5:
	add	x8, x8, __RNvCslIq7RLtFujA_13startup_probe4main@PAGEOFF
	str	x8, [sp, #8]
Lloh6:
	adrp	x1, l_vtable.0@PAGE
Lloh7:
	add	x1, x1, l_vtable.0@PAGEOFF
	add	x0, sp, #8
	mov	w4, #0
	bl	__RNvNtCsdnanKjkF2cC_3std2rt19lang_start_internal
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret
	.loh AdrpAdd	Lloh6, Lloh7
	.loh AdrpAdd	Lloh4, Lloh5
	.cfi_endproc

	.section	__DATA,__const
	.p2align	3, 0x0
l_vtable.0:
	.asciz	"\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNSNvYNCINvNtCsdnanKjkF2cC_3std2rt10lang_startuE0INtNtNtCs3bJEMBXHbwl_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe
	.quad	__RNCINvNtCsdnanKjkF2cC_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	.quad	__RNCINvNtCsdnanKjkF2cC_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe

	.section	__TEXT,__const
l_alloc_dea25bd652bc4349bac428c742353f74:
	.ascii	"hello startup\n"

.subsections_via_symbols
