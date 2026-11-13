	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.att_syntax
	.file	"startup_probe.fcf1f915dc1860a0-cgu.0"
	.def	_RINvNtCs9qcQDiGWtgW_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe;
	.scl	2;
	.type	32;
	.endef
	.text
	.globl	_RINvNtCs9qcQDiGWtgW_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.p2align	4
_RINvNtCs9qcQDiGWtgW_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe:
.seh_proc _RINvNtCs9qcQDiGWtgW_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, 48(%rsp)
	movb	%r9b, 32(%rsp)
	leaq	.Lvtable.0(%rip), %rdx
	leaq	48(%rsp), %rcx
	movq	%rax, %r9
	callq	_RNvNtCs9qcQDiGWtgW_3std2rt19lang_start_internal
	nop
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RINvNtNtCs9qcQDiGWtgW_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvNtNtCs9qcQDiGWtgW_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe:
.seh_proc _RINvNtNtCs9qcQDiGWtgW_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	callq	*%rcx
	nop
	#APP
	#NO_APP
	.seh_startepilogue
	addq	$40, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RNCINvNtCs9qcQDiGWtgW_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RNCINvNtCs9qcQDiGWtgW_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe:
.seh_proc _RNCINvNtCs9qcQDiGWtgW_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	movq	(%rcx), %rcx
	callq	_RINvNtNtCs9qcQDiGWtgW_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	xorl	%eax, %eax
	.seh_startepilogue
	addq	$40, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RNSNvYNCINvNtCs9qcQDiGWtgW_3std2rt10lang_startuE0INtNtNtCs2Ja4erDm0Jl_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RNSNvYNCINvNtCs9qcQDiGWtgW_3std2rt10lang_startuE0INtNtNtCs2Ja4erDm0Jl_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe:
.seh_proc _RNSNvYNCINvNtCs9qcQDiGWtgW_3std2rt10lang_startuE0INtNtNtCs2Ja4erDm0Jl_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	movq	(%rcx), %rcx
	callq	_RINvNtNtCs9qcQDiGWtgW_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	xorl	%eax, %eax
	.seh_startepilogue
	addq	$40, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RNvCslIq7RLtFujA_13startup_probe4main;
	.scl	2;
	.type	32;
	.endef
	.globl	_RNvCslIq7RLtFujA_13startup_probe4main
	.p2align	4
_RNvCslIq7RLtFujA_13startup_probe4main:
	leaq	.Lalloc_dea25bd652bc4349bac428c742353f74(%rip), %rcx
	movl	$29, %edx
	jmp	_RNvNtNtCs9qcQDiGWtgW_3std2io5stdio6__print

	.def	main;
	.scl	2;
	.type	32;
	.endef
	.globl	main
	.p2align	4
main:
.seh_proc main
	pushq	%rbp
	.seh_pushreg %rbp
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	subq	$48, %rsp
	.seh_stackalloc 48
	leaq	48(%rsp), %rbp
	.seh_setframe %rbp, 48
	.seh_endprologue
	movq	%rdx, %rsi
	movslq	%ecx, %rdi
	callq	__main
	leaq	_RNvCslIq7RLtFujA_13startup_probe4main(%rip), %rax
	movq	%rax, -8(%rbp)
	movb	$0, 32(%rsp)
	leaq	.Lvtable.0(%rip), %rdx
	leaq	-8(%rbp), %rcx
	movq	%rdi, %r8
	movq	%rsi, %r9
	callq	_RNvNtCs9qcQDiGWtgW_3std2rt19lang_start_internal
	nop
	.seh_startepilogue
	addq	$48, %rsp
	popq	%rdi
	popq	%rsi
	popq	%rbp
	.seh_endepilogue
	retq
	.seh_endproc

	.section	.rdata,"dr"
	.p2align	3, 0x0
.Lvtable.0:
	.asciz	"\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	_RNSNvYNCINvNtCs9qcQDiGWtgW_3std2rt10lang_startuE0INtNtNtCs2Ja4erDm0Jl_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe
	.quad	_RNCINvNtCs9qcQDiGWtgW_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	.quad	_RNCINvNtCs9qcQDiGWtgW_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe

.Lalloc_dea25bd652bc4349bac428c742353f74:
	.ascii	"hello startup\n"

	.section	.drectve,"yni"
	.ascii	" -exclude-symbols:_RINvNtCs9qcQDiGWtgW_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe"
	.ascii	" -exclude-symbols:_RNvCslIq7RLtFujA_13startup_probe4main"
