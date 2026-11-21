	.file	"naked_ok.c313897bd7a97451-cgu.0"


	.section	.text.naked_add_mul,"ax",@progbits
	.p2align	2
	.globl	naked_add_mul
	.type	naked_add_mul,@function
naked_add_mul:
	leaq	(%rdi,%rsi), %rax
	imulq	%rdx, %rax
	retq
.Lfunc_end_naked_add_mul:
.Ltmp0:
	.size	naked_add_mul, .Ltmp0-naked_add_mul
	.text





	.section	.text._RINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuECsgKnYiSOl3cz_8naked_ok,"ax",@progbits
	.hidden	_RINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuECsgKnYiSOl3cz_8naked_ok
	.globl	_RINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuECsgKnYiSOl3cz_8naked_ok
	.p2align	4
	.type	_RINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuECsgKnYiSOl3cz_8naked_ok,@function
_RINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuECsgKnYiSOl3cz_8naked_ok:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	movl	%ecx, %r8d
	movq	%rdx, %rcx
	movq	%rsi, %rdx
	movq	%rdi, (%rsp)
	leaq	.Lanon.33bb3eb39124f5409ffa8ee6ee27aa0a.0(%rip), %rsi
	movq	%rsp, %rdi
	callq	*_RNvNtCsfFlbQN6m3JZ_3std2rt19lang_start_internal@GOTPCREL(%rip)
	popq	%rcx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end0:
	.size	_RINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuECsgKnYiSOl3cz_8naked_ok, .Lfunc_end0-_RINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuECsgKnYiSOl3cz_8naked_ok
	.cfi_endproc

	.section	.text._RINvNtNtCsfFlbQN6m3JZ_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECsgKnYiSOl3cz_8naked_ok,"ax",@progbits
	.p2align	4
	.type	_RINvNtNtCsfFlbQN6m3JZ_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECsgKnYiSOl3cz_8naked_ok,@function
_RINvNtNtCsfFlbQN6m3JZ_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECsgKnYiSOl3cz_8naked_ok:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	callq	*%rdi
	#APP
	#NO_APP
	popq	%rax
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end1:
	.size	_RINvNtNtCsfFlbQN6m3JZ_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECsgKnYiSOl3cz_8naked_ok, .Lfunc_end1-_RINvNtNtCsfFlbQN6m3JZ_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECsgKnYiSOl3cz_8naked_ok
	.cfi_endproc

	.section	.text._RNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0CsgKnYiSOl3cz_8naked_ok,"ax",@progbits
	.p2align	4
	.type	_RNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0CsgKnYiSOl3cz_8naked_ok,@function
_RNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0CsgKnYiSOl3cz_8naked_ok:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	movq	(%rdi), %rdi
	callq	_RINvNtNtCsfFlbQN6m3JZ_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECsgKnYiSOl3cz_8naked_ok
	xorl	%eax, %eax
	popq	%rcx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end2:
	.size	_RNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0CsgKnYiSOl3cz_8naked_ok, .Lfunc_end2-_RNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0CsgKnYiSOl3cz_8naked_ok
	.cfi_endproc

	.section	.text._RNSNvYNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0INtNtNtCs8b4M6GsfcPr_4core3ops8function6FnOnceuE9call_once6vtableCsgKnYiSOl3cz_8naked_ok,"ax",@progbits
	.p2align	4
	.type	_RNSNvYNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0INtNtNtCs8b4M6GsfcPr_4core3ops8function6FnOnceuE9call_once6vtableCsgKnYiSOl3cz_8naked_ok,@function
_RNSNvYNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0INtNtNtCs8b4M6GsfcPr_4core3ops8function6FnOnceuE9call_once6vtableCsgKnYiSOl3cz_8naked_ok:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	movq	(%rdi), %rdi
	callq	_RINvNtNtCsfFlbQN6m3JZ_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECsgKnYiSOl3cz_8naked_ok
	xorl	%eax, %eax
	popq	%rcx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end3:
	.size	_RNSNvYNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0INtNtNtCs8b4M6GsfcPr_4core3ops8function6FnOnceuE9call_once6vtableCsgKnYiSOl3cz_8naked_ok, .Lfunc_end3-_RNSNvYNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0INtNtNtCs8b4M6GsfcPr_4core3ops8function6FnOnceuE9call_once6vtableCsgKnYiSOl3cz_8naked_ok
	.cfi_endproc

	.section	.text._RNvCsgKnYiSOl3cz_8naked_ok4main,"ax",@progbits
	.hidden	_RNvCsgKnYiSOl3cz_8naked_ok4main
	.globl	_RNvCsgKnYiSOl3cz_8naked_ok4main
	.p2align	4
	.type	_RNvCsgKnYiSOl3cz_8naked_ok4main,@function
_RNvCsgKnYiSOl3cz_8naked_ok4main:
	.cfi_startproc
	subq	$24, %rsp
	.cfi_def_cfa_offset 32
	movl	$3, %edi
	movl	$4, %esi
	movl	$5, %edx
	callq	*naked_add_mul@GOTPCREL(%rip)
	movq	%rax, (%rsp)
	movq	%rsp, %rax
	movq	%rax, 8(%rsp)
	movq	_RNvXsd_NtNtNtCs8b4M6GsfcPr_4core3fmt3num3impyNtB9_7Display3fmt@GOTPCREL(%rip), %rax
	movq	%rax, 16(%rsp)
	leaq	.Lanon.33bb3eb39124f5409ffa8ee6ee27aa0a.1(%rip), %rdi
	leaq	8(%rsp), %rsi
	callq	*_RNvNtNtCsfFlbQN6m3JZ_3std2io5stdio6__print@GOTPCREL(%rip)
	addq	$24, %rsp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end4:
	.size	_RNvCsgKnYiSOl3cz_8naked_ok4main, .Lfunc_end4-_RNvCsgKnYiSOl3cz_8naked_ok4main
	.cfi_endproc

	.section	.text.main,"ax",@progbits
	.globl	main
	.p2align	4
	.type	main,@function
main:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	movq	%rsi, %rcx
	movslq	%edi, %rdx
	leaq	_RNvCsgKnYiSOl3cz_8naked_ok4main(%rip), %rax
	movq	%rax, (%rsp)
	leaq	.Lanon.33bb3eb39124f5409ffa8ee6ee27aa0a.0(%rip), %rsi
	movq	%rsp, %rdi
	xorl	%r8d, %r8d
	callq	*_RNvNtCsfFlbQN6m3JZ_3std2rt19lang_start_internal@GOTPCREL(%rip)
	popq	%rcx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end5:
	.size	main, .Lfunc_end5-main
	.cfi_endproc

	.type	.Lanon.33bb3eb39124f5409ffa8ee6ee27aa0a.0,@object
	.section	.data.rel.ro..Lanon.33bb3eb39124f5409ffa8ee6ee27aa0a.0,"aw",@progbits
	.p2align	3, 0x0
.Lanon.33bb3eb39124f5409ffa8ee6ee27aa0a.0:
	.asciz	"\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	_RNSNvYNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0INtNtNtCs8b4M6GsfcPr_4core3ops8function6FnOnceuE9call_once6vtableCsgKnYiSOl3cz_8naked_ok
	.quad	_RNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0CsgKnYiSOl3cz_8naked_ok
	.quad	_RNCINvNtCsfFlbQN6m3JZ_3std2rt10lang_startuE0CsgKnYiSOl3cz_8naked_ok
	.size	.Lanon.33bb3eb39124f5409ffa8ee6ee27aa0a.0, 48

	.type	.Lanon.33bb3eb39124f5409ffa8ee6ee27aa0a.1,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.33bb3eb39124f5409ffa8ee6ee27aa0a.1:
	.asciz	"\tNAKED_OK=\300\001\n"
	.size	.Lanon.33bb3eb39124f5409ffa8ee6ee27aa0a.1, 14

	.ident	"rustc version 1.98.0-nightly (14210df0e 2026-05-31)"
	.section	".note.GNU-stack","",@progbits
