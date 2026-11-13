	.att_syntax
	.file	"startup_probe.fcf1f915dc1860a0-cgu.0"
	.section	.text._RINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe,"ax",@progbits
	.hidden	_RINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.globl	_RINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.prefalign	4, .Lfunc_end0, nop
	.type	_RINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe,@function
_RINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	pushl	%edi
	.cfi_def_cfa_offset 12
	pushl	%esi
	.cfi_def_cfa_offset 16
	subl	$16, %esp
	.cfi_def_cfa_offset 32
	.cfi_offset %esi, -16
	.cfi_offset %edi, -12
	.cfi_offset %ebx, -8
	movl	32(%esp), %edx
	movl	36(%esp), %eax
	movl	40(%esp), %ecx
	calll	.L0$pb
	.cfi_adjust_cfa_offset 4
.L0$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp0:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp0-.L0$pb), %ebx
	movl	%edx, 12(%esp)
	subl	$12, %esp
	.cfi_adjust_cfa_offset 12
	movl	56(%esp), %edx
	leal	.Lvtable.0@GOTOFF(%ebx), %esi
	leal	24(%esp), %edi
	pushl	%edx
	.cfi_adjust_cfa_offset 4
	pushl	%ecx
	.cfi_adjust_cfa_offset 4
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	pushl	%esi
	.cfi_adjust_cfa_offset 4
	pushl	%edi
	.cfi_adjust_cfa_offset 4
	calll	_RNvNtCsl0WIz0hVJ8g_3std2rt19lang_start_internal@PLT
	addl	$48, %esp
	.cfi_adjust_cfa_offset -48
	popl	%esi
	.cfi_def_cfa_offset 12
	popl	%edi
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end0:
	.size	_RINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe, .Lfunc_end0-_RINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.cfi_endproc

	.section	.text._RINvNtNtCsl0WIz0hVJ8g_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end1, nop
	.type	_RINvNtNtCsl0WIz0hVJ8g_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe,@function
_RINvNtNtCsl0WIz0hVJ8g_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	subl	$12, %esp
	.cfi_def_cfa_offset 16
	calll	*%ecx
	#APP
	#NO_APP
	addl	$12, %esp
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end1:
	.size	_RINvNtNtCsl0WIz0hVJ8g_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe, .Lfunc_end1-_RINvNtNtCsl0WIz0hVJ8g_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	.cfi_endproc

	.section	.text._RNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end2, nop
	.type	_RNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe,@function
_RNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	subl	$8, %esp
	.cfi_def_cfa_offset 16
	.cfi_offset %ebx, -8
	movl	16(%esp), %eax
	calll	.L2$pb
	.cfi_adjust_cfa_offset 4
.L2$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp1:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp1-.L2$pb), %ebx
	movl	(%eax), %ecx
	calll	_RINvNtNtCsl0WIz0hVJ8g_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	xorl	%eax, %eax
	addl	$8, %esp
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end2:
	.size	_RNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe, .Lfunc_end2-_RNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	.cfi_endproc

	.section	.text._RNSNvYNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0INtNtNtCsla01Uw4N3k7_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end3, nop
	.type	_RNSNvYNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0INtNtNtCsla01Uw4N3k7_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe,@function
_RNSNvYNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0INtNtNtCsla01Uw4N3k7_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	subl	$8, %esp
	.cfi_def_cfa_offset 16
	.cfi_offset %ebx, -8
	movl	16(%esp), %eax
	calll	.L3$pb
	.cfi_adjust_cfa_offset 4
.L3$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp2:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp2-.L3$pb), %ebx
	movl	(%eax), %ecx
	calll	_RINvNtNtCsl0WIz0hVJ8g_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	xorl	%eax, %eax
	addl	$8, %esp
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end3:
	.size	_RNSNvYNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0INtNtNtCsla01Uw4N3k7_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe, .Lfunc_end3-_RNSNvYNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0INtNtNtCsla01Uw4N3k7_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe
	.cfi_endproc

	.section	.text._RNvCslIq7RLtFujA_13startup_probe4main,"ax",@progbits
	.hidden	_RNvCslIq7RLtFujA_13startup_probe4main
	.globl	_RNvCslIq7RLtFujA_13startup_probe4main
	.prefalign	4, .Lfunc_end4, nop
	.type	_RNvCslIq7RLtFujA_13startup_probe4main,@function
_RNvCslIq7RLtFujA_13startup_probe4main:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	subl	$8, %esp
	.cfi_def_cfa_offset 16
	.cfi_offset %ebx, -8
	calll	.L4$pb
	.cfi_adjust_cfa_offset 4
.L4$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp3:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp3-.L4$pb), %ebx
	subl	$8, %esp
	.cfi_adjust_cfa_offset 8
	leal	.Lalloc_dea25bd652bc4349bac428c742353f74@GOTOFF(%ebx), %eax
	pushl	$29
	.cfi_adjust_cfa_offset 4
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	calll	_RNvNtNtCsl0WIz0hVJ8g_3std2io5stdio6__print@PLT
	addl	$24, %esp
	.cfi_adjust_cfa_offset -24
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end4:
	.size	_RNvCslIq7RLtFujA_13startup_probe4main, .Lfunc_end4-_RNvCslIq7RLtFujA_13startup_probe4main
	.cfi_endproc

	.section	.text.main,"ax",@progbits
	.globl	main
	.prefalign	4, .Lfunc_end5, nop
	.type	main,@function
main:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	pushl	%esi
	.cfi_def_cfa_offset 12
	pushl	%eax
	.cfi_def_cfa_offset 16
	.cfi_offset %esi, -12
	.cfi_offset %ebx, -8
	calll	.L5$pb
	.cfi_adjust_cfa_offset 4
.L5$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
	movl	16(%esp), %eax
	movl	20(%esp), %ecx
.Ltmp4:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp4-.L5$pb), %ebx
	leal	_RNvCslIq7RLtFujA_13startup_probe4main@GOTOFF(%ebx), %edx
	movl	%edx, (%esp)
	subl	$12, %esp
	.cfi_adjust_cfa_offset 12
	leal	.Lvtable.0@GOTOFF(%ebx), %edx
	leal	12(%esp), %esi
	pushl	$0
	.cfi_adjust_cfa_offset 4
	pushl	%ecx
	.cfi_adjust_cfa_offset 4
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	pushl	%edx
	.cfi_adjust_cfa_offset 4
	pushl	%esi
	.cfi_adjust_cfa_offset 4
	calll	_RNvNtCsl0WIz0hVJ8g_3std2rt19lang_start_internal@PLT
	addl	$36, %esp
	.cfi_adjust_cfa_offset -36
	popl	%esi
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end5:
	.size	main, .Lfunc_end5-main
	.cfi_endproc

	.type	.Lvtable.0,@object
	.section	.data.rel.ro..Lvtable.0,"aw",@progbits
	.p2align	2, 0x0
.Lvtable.0:
	.asciz	"\000\000\000\000\004\000\000\000\004\000\000"
	.long	_RNSNvYNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0INtNtNtCsla01Uw4N3k7_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe
	.long	_RNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	.long	_RNCINvNtCsl0WIz0hVJ8g_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	.size	.Lvtable.0, 24

	.type	.Lalloc_dea25bd652bc4349bac428c742353f74,@object
	.section	.rodata..Lalloc_dea25bd652bc4349bac428c742353f74,"a",@progbits
.Lalloc_dea25bd652bc4349bac428c742353f74:
	.ascii	"hello startup\n"
	.size	.Lalloc_dea25bd652bc4349bac428c742353f74, 14

	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
