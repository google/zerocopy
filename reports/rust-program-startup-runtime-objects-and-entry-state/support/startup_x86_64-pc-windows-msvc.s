	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.att_syntax
	.file	"startup_probe.fcf1f915dc1860a0-cgu.0"
	.def	_RINvNtCscx1ptWZUqVR_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtCscx1ptWZUqVR_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe,unique,0
	.globl	_RINvNtCscx1ptWZUqVR_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.p2align	4
_RINvNtCscx1ptWZUqVR_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe:
.seh_proc _RINvNtCscx1ptWZUqVR_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, 48(%rsp)
	movb	%r9b, 32(%rsp)
	leaq	vtable.0(%rip), %rdx
	leaq	48(%rsp), %rcx
	movq	%rax, %r9
	callq	_RNvNtCscx1ptWZUqVR_3std2rt19lang_start_internal
	nop
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RINvNtNtCscx1ptWZUqVR_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtNtCscx1ptWZUqVR_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe,unique,1
	.p2align	4
_RINvNtNtCscx1ptWZUqVR_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe:
.seh_proc _RINvNtNtCscx1ptWZUqVR_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
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

	.def	_RNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe,unique,2
	.p2align	4
_RNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe:
.seh_proc _RNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	movq	(%rcx), %rcx
	callq	_RINvNtNtCscx1ptWZUqVR_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	xorl	%eax, %eax
	.seh_startepilogue
	addq	$40, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RNSNvYNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0INtNtNtCs7uUmbfRqPp3_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvYNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0INtNtNtCs7uUmbfRqPp3_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe,unique,3
	.p2align	4
_RNSNvYNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0INtNtNtCs7uUmbfRqPp3_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe:
.seh_proc _RNSNvYNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0INtNtNtCs7uUmbfRqPp3_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	movq	(%rcx), %rcx
	callq	_RINvNtNtCscx1ptWZUqVR_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
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
	.section	.text,"xr",one_only,_RNvCslIq7RLtFujA_13startup_probe4main,unique,4
	.globl	_RNvCslIq7RLtFujA_13startup_probe4main
	.p2align	4
_RNvCslIq7RLtFujA_13startup_probe4main:
	leaq	alloc_dea25bd652bc4349bac428c742353f74(%rip), %rcx
	movl	$29, %edx
	jmp	_RNvNtNtCscx1ptWZUqVR_3std2io5stdio6__print

	.def	main;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,main,unique,5
	.globl	main
	.p2align	4
main:
.seh_proc main
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	%rdx, %r9
	movslq	%ecx, %r8
	leaq	_RNvCslIq7RLtFujA_13startup_probe4main(%rip), %rax
	movq	%rax, 48(%rsp)
	movb	$0, 32(%rsp)
	leaq	vtable.0(%rip), %rdx
	leaq	48(%rsp), %rcx
	callq	_RNvNtCscx1ptWZUqVR_3std2rt19lang_start_internal
	nop
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.section	.rdata,"dr",one_only,vtable.0,unique,6
	.p2align	3, 0x0
vtable.0:
	.asciz	"\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	_RNSNvYNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0INtNtNtCs7uUmbfRqPp3_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe
	.quad	_RNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	.quad	_RNCINvNtCscx1ptWZUqVR_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe

	.section	.rdata,"dr",one_only,alloc_dea25bd652bc4349bac428c742353f74,unique,7
alloc_dea25bd652bc4349bac428c742353f74:
	.ascii	"hello startup\n"

