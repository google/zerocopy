	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 1
	.att_syntax
	.file	"startup_probe.fcf1f915dc1860a0-cgu.0"
	.def	__RINvNtCs13X54pRMZqp_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RINvNtCs13X54pRMZqp_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe,unique,0
	.globl	__RINvNtCs13X54pRMZqp_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe
	.p2align	4
__RINvNtCs13X54pRMZqp_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe:
	pushl	%esi
	pushl	%eax
	movl	12(%esp), %edx
	movl	16(%esp), %eax
	movl	20(%esp), %ecx
	movl	%esp, %esi
	movl	%edx, (%esp)
	movl	24(%esp), %edx
	pushl	%edx
	pushl	%ecx
	pushl	%eax
	pushl	$_vtable.0
	pushl	%esi
	calll	__RNvNtCs13X54pRMZqp_3std2rt19lang_start_internal
	addl	$24, %esp
	popl	%esi
	retl

	.def	__RINvNtNtCs13X54pRMZqp_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RINvNtNtCs13X54pRMZqp_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe,unique,1
	.p2align	4
__RINvNtNtCs13X54pRMZqp_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe:
	calll	*%ecx
	#APP
	#NO_APP
	retl

	.def	__RNCINvNtCs13X54pRMZqp_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNCINvNtCs13X54pRMZqp_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe,unique,2
	.p2align	4
__RNCINvNtCs13X54pRMZqp_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe:
	movl	4(%esp), %eax
	movl	(%eax), %ecx
	calll	__RINvNtNtCs13X54pRMZqp_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	xorl	%eax, %eax
	retl

	.def	__RNSNvYNCINvNtCs13X54pRMZqp_3std2rt10lang_startuE0INtNtNtCselTjGGDqQnQ_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNSNvYNCINvNtCs13X54pRMZqp_3std2rt10lang_startuE0INtNtNtCselTjGGDqQnQ_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe,unique,3
	.p2align	4
__RNSNvYNCINvNtCs13X54pRMZqp_3std2rt10lang_startuE0INtNtNtCselTjGGDqQnQ_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe:
	movl	4(%esp), %eax
	movl	(%eax), %ecx
	calll	__RINvNtNtCs13X54pRMZqp_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe
	xorl	%eax, %eax
	retl

	.def	__RNvCslIq7RLtFujA_13startup_probe4main;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNvCslIq7RLtFujA_13startup_probe4main,unique,4
	.globl	__RNvCslIq7RLtFujA_13startup_probe4main
	.p2align	4
__RNvCslIq7RLtFujA_13startup_probe4main:
	pushl	$29
	pushl	$_alloc_dea25bd652bc4349bac428c742353f74
	calll	__RNvNtNtCs13X54pRMZqp_3std2io5stdio6__print
	addl	$8, %esp
	retl

	.def	_main;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_main,unique,5
	.globl	_main
	.p2align	4
_main:
	pushl	%eax
	movl	8(%esp), %eax
	movl	12(%esp), %ecx
	movl	$__RNvCslIq7RLtFujA_13startup_probe4main, (%esp)
	movl	%esp, %edx
	pushl	$0
	pushl	%ecx
	pushl	%eax
	pushl	$_vtable.0
	pushl	%edx
	calll	__RNvNtCs13X54pRMZqp_3std2rt19lang_start_internal
	addl	$20, %esp
	popl	%ecx
	retl

	.section	.rdata,"dr",one_only,_vtable.0,unique,6
	.p2align	2, 0x0
_vtable.0:
	.asciz	"\000\000\000\000\004\000\000\000\004\000\000"
	.long	__RNSNvYNCINvNtCs13X54pRMZqp_3std2rt10lang_startuE0INtNtNtCselTjGGDqQnQ_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe
	.long	__RNCINvNtCs13X54pRMZqp_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe
	.long	__RNCINvNtCs13X54pRMZqp_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe

	.section	.rdata,"dr",one_only,_alloc_dea25bd652bc4349bac428c742353f74,unique,7
_alloc_dea25bd652bc4349bac428c742353f74:
	.ascii	"hello startup\n"

