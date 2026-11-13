	.file	"startup_probe.fcf1f915dc1860a0-cgu.0"
	.section	.text._RINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe,"ax",@progbits
	.hidden	_RINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.globl	_RINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.p2align	2
	.type	_RINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe,@function
_RINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	w4, w3
	mov	x3, x2
	mov	x2, x1
	str	x0, [sp, #8]
	adrp	x1, .Lvtable.0
	add	x1, x1, :lo12:.Lvtable.0
	add	x0, sp, #8
	bl	_RNvNtCs9g4b2IXPNZ3_3std2rt19lang_start_internal
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end0:
	.size	_RINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe, .Lfunc_end0-_RINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.cfi_endproc

	.section	.text._RINvNtNtCs9g4b2IXPNZ3_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe,"ax",@progbits
	.p2align	2
	.type	_RINvNtNtCs9g4b2IXPNZ3_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe,@function
_RINvNtNtCs9g4b2IXPNZ3_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	blr	x0
	//APP
	//NO_APP
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end1:
	.size	_RINvNtNtCs9g4b2IXPNZ3_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe, .Lfunc_end1-_RINvNtNtCs9g4b2IXPNZ3_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	.cfi_endproc

	.section	.text._RNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe,"ax",@progbits
	.p2align	2
	.type	_RNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe,@function
_RNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	ldr	x0, [x0]
	bl	_RINvNtNtCs9g4b2IXPNZ3_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	mov	w0, wzr
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end2:
	.size	_RNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe, .Lfunc_end2-_RNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	.cfi_endproc

	.section	.text._RNSNvYNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0INtNtNtCsaWcbhsS8OaW_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe,"ax",@progbits
	.p2align	2
	.type	_RNSNvYNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0INtNtNtCsaWcbhsS8OaW_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe,@function
_RNSNvYNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0INtNtNtCsaWcbhsS8OaW_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	ldr	x0, [x0]
	bl	_RINvNtNtCs9g4b2IXPNZ3_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	mov	w0, wzr
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end3:
	.size	_RNSNvYNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0INtNtNtCsaWcbhsS8OaW_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe, .Lfunc_end3-_RNSNvYNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0INtNtNtCsaWcbhsS8OaW_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe
	.cfi_endproc

	.section	.text._RNvCslIq7RLtFujA_13startup_probe4main,"ax",@progbits
	.hidden	_RNvCslIq7RLtFujA_13startup_probe4main
	.globl	_RNvCslIq7RLtFujA_13startup_probe4main
	.p2align	2
	.type	_RNvCslIq7RLtFujA_13startup_probe4main,@function
_RNvCslIq7RLtFujA_13startup_probe4main:
	.cfi_startproc
	adrp	x0, .Lalloc_dea25bd652bc4349bac428c742353f74
	add	x0, x0, :lo12:.Lalloc_dea25bd652bc4349bac428c742353f74
	mov	w1, #29
	b	_RNvNtNtCs9g4b2IXPNZ3_3std2io5stdio6__print
.Lfunc_end4:
	.size	_RNvCslIq7RLtFujA_13startup_probe4main, .Lfunc_end4-_RNvCslIq7RLtFujA_13startup_probe4main
	.cfi_endproc

	.section	.text.main,"ax",@progbits
	.globl	main
	.p2align	2
	.type	main,@function
main:
	.cfi_startproc
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	sxtw	x2, w0
	mov	x3, x1
	adrp	x8, _RNvCslIq7RLtFujA_13startup_probe4main
	add	x8, x8, :lo12:_RNvCslIq7RLtFujA_13startup_probe4main
	adrp	x1, .Lvtable.0
	add	x1, x1, :lo12:.Lvtable.0
	add	x0, sp, #8
	mov	w4, wzr
	str	x8, [sp, #8]
	bl	_RNvNtCs9g4b2IXPNZ3_3std2rt19lang_start_internal
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret
.Lfunc_end5:
	.size	main, .Lfunc_end5-main
	.cfi_endproc

	.type	.Lvtable.0,@object
	.section	.data.rel.ro..Lvtable.0,"aw",@progbits
	.p2align	3, 0x0
.Lvtable.0:
	.asciz	"\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.xword	_RNSNvYNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0INtNtNtCsaWcbhsS8OaW_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe
	.xword	_RNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	.xword	_RNCINvNtCs9g4b2IXPNZ3_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	.size	.Lvtable.0, 48

	.type	.Lalloc_dea25bd652bc4349bac428c742353f74,@object
	.section	.rodata..Lalloc_dea25bd652bc4349bac428c742353f74,"a",@progbits
.Lalloc_dea25bd652bc4349bac428c742353f74:
	.ascii	"hello startup\n"
	.size	.Lalloc_dea25bd652bc4349bac428c742353f74, 14

	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
