	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.att_syntax
	.file	"unwind_probe.e45a91751a911c8a-cgu.0"
	.def	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop,unique,0
	.globl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	.p2align	4
_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop:
	movq	(%rcx), %rax
	movl	(%rax), %edx
	leal	(%rdx,%rdx,4), %edx
	addl	%edx, %edx
	addl	8(%rcx), %edx
	movl	%edx, (%rax)
	retq

	.def	catch_unwind_entry;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.globl	catch_unwind_entry
	.p2align	4
catch_unwind_entry:
.Lfunc_begin0:
.seh_proc catch_unwind_entry
	.seh_handler __CxxFrameHandler3, @unwind, @except
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$64, %rsp
	.seh_stackalloc 64
	leaq	64(%rsp), %rbp
	.seh_setframe %rbp, 64
	.seh_endprologue
	movq	$-2, -16(%rbp)
.Ltmp0:
	callq	nested_cleanups
	nop
.Ltmp1:
.LBB1_1:
	xorl	%eax, %eax
.LBB1_2:
	.seh_startepilogue
	addq	$64, %rsp
	popq	%rbp
	.seh_endepilogue
	retq
.LBB1_9:
$ehgcr_1_9:
	cmpq	$0, -32(%rbp)
	je	.LBB1_1
	movq	-24(%rbp), %rax
	movq	(%rax), %rax
	testq	%rax, %rax
	je	.LBB1_12
.Ltmp6:
	movq	-32(%rbp), %rcx
	callq	*%rax
	nop
.Ltmp7:
.LBB1_12:
	movq	-24(%rbp), %rax
	movq	8(%rax), %rdx
	testq	%rdx, %rdx
	je	.LBB1_14
	movq	-24(%rbp), %rax
	movq	16(%rax), %r8
	movq	-32(%rbp), %rcx
	callq	_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
.LBB1_14:
	movl	$1, %eax
	jmp	.LBB1_2
	.seh_handlerdata
	.long	$cppxdata$catch_unwind_entry@IMGREL
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.def	"?catch$3@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?catch$3@?0?catch_unwind_entry@4HA":
.seh_proc "?catch$3@?0?catch_unwind_entry@4HA"
	.seh_handler __CxxFrameHandler3, @unwind, @except
.LBB1_3:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$32, %rsp
	.seh_stackalloc 32
	leaq	64(%rdx), %rbp
	.seh_endprologue
	callq	_RNvNtCs7uUmbfRqPp3_4core9panicking19panic_cannot_unwind
	ud2
	.seh_handlerdata
	.long	$cppxdata$catch_unwind_entry@IMGREL
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.def	"?catch$4@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?catch$4@?0?catch_unwind_entry@4HA":
.seh_proc "?catch$4@?0?catch_unwind_entry@4HA"
	.seh_handler __CxxFrameHandler3, @unwind, @except
.LBB1_4:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$32, %rsp
	.seh_stackalloc 32
	leaq	64(%rdx), %rbp
	.seh_endprologue
	movq	-8(%rbp), %rcx
.Ltmp4:
	callq	_RNvNvNtCscx1ptWZUqVR_3std9panicking12catch_unwind7cleanup
	movq	%rax, -32(%rbp)
	movq	%rdx, -24(%rbp)
.Ltmp5:
	leaq	.LBB1_9(%rip), %rax
	.seh_startepilogue
	addq	$32, %rsp
	popq	%rbp
	.seh_endepilogue
	retq
	.seh_handlerdata
	.long	$cppxdata$catch_unwind_entry@IMGREL
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.def	"?catch$6@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?catch$6@?0?catch_unwind_entry@4HA":
.seh_proc "?catch$6@?0?catch_unwind_entry@4HA"
	.seh_handler __CxxFrameHandler3, @unwind, @except
.LBB1_6:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$32, %rsp
	.seh_stackalloc 32
	leaq	64(%rdx), %rbp
	.seh_endprologue
	callq	_RNvNtCs7uUmbfRqPp3_4core9panicking19panic_cannot_unwind
	ud2
	.seh_handlerdata
	.long	$cppxdata$catch_unwind_entry@IMGREL
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.def	"?catch$7@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?catch$7@?0?catch_unwind_entry@4HA":
.seh_proc "?catch$7@?0?catch_unwind_entry@4HA"
	.seh_handler __CxxFrameHandler3, @unwind, @except
.LBB1_7:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$32, %rsp
	.seh_stackalloc 32
	leaq	64(%rdx), %rbp
	.seh_endprologue
.Ltmp2:
	xorl	%ecx, %ecx
	callq	_RNvNvNtCscx1ptWZUqVR_3std9panicking12catch_unwind7cleanup
	movq	%rax, -32(%rbp)
	movq	%rdx, -24(%rbp)
.Ltmp3:
	leaq	.LBB1_9(%rip), %rax
	.seh_startepilogue
	addq	$32, %rsp
	popq	%rbp
	.seh_endepilogue
	retq
	.seh_handlerdata
	.long	$cppxdata$catch_unwind_entry@IMGREL
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.def	"?dtor$15@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$15@?0?catch_unwind_entry@4HA":
.seh_proc "?dtor$15@?0?catch_unwind_entry@4HA"
.LBB1_15:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$32, %rsp
	.seh_stackalloc 32
	leaq	64(%rdx), %rbp
	.seh_endprologue
	movq	-24(%rbp), %rax
	movq	8(%rax), %rdx
	testq	%rdx, %rdx
	je	.LBB1_17
	movq	-24(%rbp), %rax
	movq	16(%rax), %r8
	movq	-32(%rbp), %rcx
	callq	_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
	nop
.LBB1_17:
	.seh_startepilogue
	addq	$32, %rsp
	popq	%rbp
	.seh_endepilogue
	retq
.Lfunc_end0:
	.seh_handlerdata
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.section	.xdata,"dr",associative,catch_unwind_entry,unique,0
	.p2align	2, 0x0
$cppxdata$catch_unwind_entry:
	.long	429065506
	.long	7
	.long	$stateUnwindMap$catch_unwind_entry@IMGREL
	.long	3
	.long	$tryMap$catch_unwind_entry@IMGREL
	.long	12
	.long	$ip2state$catch_unwind_entry@IMGREL
	.long	48
	.long	0
	.long	1
$stateUnwindMap$catch_unwind_entry:
	.long	-1
	.long	0
	.long	-1
	.long	0
	.long	1
	.long	0
	.long	1
	.long	0
	.long	1
	.long	0
	.long	1
	.long	0
	.long	-1
	.long	"?dtor$15@?0?catch_unwind_entry@4HA"@IMGREL
$tryMap$catch_unwind_entry:
	.long	0
	.long	0
	.long	5
	.long	2
	.long	$handlerMap$0$catch_unwind_entry@IMGREL
	.long	2
	.long	2
	.long	3
	.long	1
	.long	$handlerMap$1$catch_unwind_entry@IMGREL
	.long	4
	.long	4
	.long	5
	.long	1
	.long	$handlerMap$2$catch_unwind_entry@IMGREL
$handlerMap$0$catch_unwind_entry:
	.long	8
	.long	_RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info@IMGREL
	.long	56
	.long	"?catch$4@?0?catch_unwind_entry@4HA"@IMGREL
	.long	56
	.long	64
	.long	0
	.long	0
	.long	"?catch$7@?0?catch_unwind_entry@4HA"@IMGREL
	.long	56
$handlerMap$1$catch_unwind_entry:
	.long	64
	.long	0
	.long	0
	.long	"?catch$3@?0?catch_unwind_entry@4HA"@IMGREL
	.long	56
$handlerMap$2$catch_unwind_entry:
	.long	64
	.long	0
	.long	0
	.long	"?catch$6@?0?catch_unwind_entry@4HA"@IMGREL
	.long	56
$ip2state$catch_unwind_entry:
	.long	.Lfunc_begin0@IMGREL
	.long	-1
	.long	.Ltmp0@IMGREL
	.long	0
	.long	.Ltmp6@IMGREL
	.long	6
	.long	.Ltmp7@IMGREL
	.long	-1
	.long	"?catch$3@?0?catch_unwind_entry@4HA"@IMGREL
	.long	3
	.long	"?catch$4@?0?catch_unwind_entry@4HA"@IMGREL
	.long	1
	.long	.Ltmp4@IMGREL
	.long	2
	.long	.Ltmp5@IMGREL
	.long	1
	.long	"?catch$6@?0?catch_unwind_entry@4HA"@IMGREL
	.long	5
	.long	"?catch$7@?0?catch_unwind_entry@4HA"@IMGREL
	.long	1
	.long	.Ltmp2@IMGREL
	.long	4
	.long	.Ltmp3@IMGREL
	.long	1
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1

	.def	frameless_leaf;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,frameless_leaf,unique,2
	.globl	frameless_leaf
	.p2align	4
frameless_leaf:
	leaq	42(%rcx), %rax
	retq

	.def	nested_cleanups;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,nested_cleanups,unique,3
	.globl	nested_cleanups
	.p2align	4
nested_cleanups:
.Lfunc_begin1:
.seh_proc nested_cleanups
	.seh_handler __CxxFrameHandler3, @unwind, @except
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$80, %rsp
	.seh_stackalloc 80
	leaq	80(%rsp), %rbp
	.seh_setframe %rbp, 80
	.seh_endprologue
	movq	$-2, -8(%rbp)
	movq	%rcx, -24(%rbp)
	movl	$1, -16(%rbp)
	movq	%rcx, -40(%rbp)
	movl	$2, -32(%rbp)
.Ltmp8:
	callq	*%rdx
	nop
.Ltmp9:
	leaq	-40(%rbp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	leaq	-24(%rbp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	nop
	.seh_startepilogue
	addq	$80, %rsp
	popq	%rbp
	.seh_endepilogue
	retq
	.seh_handlerdata
	.long	$cppxdata$nested_cleanups@IMGREL
	.section	.text,"xr",one_only,nested_cleanups,unique,3
	.seh_endproc
	.def	"?dtor$2@?0?nested_cleanups@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$2@?0?nested_cleanups@4HA":
.seh_proc "?dtor$2@?0?nested_cleanups@4HA"
.LBB3_2:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$32, %rsp
	.seh_stackalloc 32
	leaq	80(%rdx), %rbp
	.seh_endprologue
	leaq	-40(%rbp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	leaq	-24(%rbp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	nop
	.seh_startepilogue
	addq	$32, %rsp
	popq	%rbp
	.seh_endepilogue
	retq
.Lfunc_end1:
	.seh_handlerdata
	.section	.text,"xr",one_only,nested_cleanups,unique,3
	.seh_endproc
	.section	.xdata,"dr",associative,nested_cleanups,unique,1
	.p2align	2, 0x0
$cppxdata$nested_cleanups:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$nested_cleanups@IMGREL
	.long	0
	.long	0
	.long	3
	.long	$ip2state$nested_cleanups@IMGREL
	.long	72
	.long	0
	.long	1
$stateUnwindMap$nested_cleanups:
	.long	-1
	.long	"?dtor$2@?0?nested_cleanups@4HA"@IMGREL
$ip2state$nested_cleanups:
	.long	.Lfunc_begin1@IMGREL
	.long	-1
	.long	.Ltmp8@IMGREL
	.long	0
	.long	.Ltmp9@IMGREL
	.long	-1
	.section	.text,"xr",one_only,nested_cleanups,unique,3

	.def	nounwind_c_boundary;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,nounwind_c_boundary,unique,4
	.globl	nounwind_c_boundary
	.p2align	4
nounwind_c_boundary:
.Lfunc_begin2:
.seh_proc nounwind_c_boundary
	.seh_handler __CxxFrameHandler3, @unwind, @except
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$64, %rsp
	.seh_stackalloc 64
	leaq	64(%rsp), %rbp
	.seh_setframe %rbp, 64
	.seh_endprologue
	movq	$-2, -8(%rbp)
	movq	%rcx, -24(%rbp)
	movl	$9, -16(%rbp)
.Ltmp10:
	callq	*%rdx
	nop
.Ltmp11:
	leaq	-24(%rbp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	nop
	.seh_startepilogue
	addq	$64, %rsp
	popq	%rbp
	.seh_endepilogue
	retq
	.seh_handlerdata
	.long	$cppxdata$nounwind_c_boundary@IMGREL
	.section	.text,"xr",one_only,nounwind_c_boundary,unique,4
	.seh_endproc
	.def	"?dtor$2@?0?nounwind_c_boundary@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$2@?0?nounwind_c_boundary@4HA":
.seh_proc "?dtor$2@?0?nounwind_c_boundary@4HA"
.LBB4_2:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$32, %rsp
	.seh_stackalloc 32
	leaq	64(%rdx), %rbp
	.seh_endprologue
	leaq	-24(%rbp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	callq	_RNvNtCs7uUmbfRqPp3_4core9panicking19panic_cannot_unwind
	ud2
.Lfunc_end2:
	.seh_handlerdata
	.section	.text,"xr",one_only,nounwind_c_boundary,unique,4
	.seh_endproc
	.section	.xdata,"dr",associative,nounwind_c_boundary,unique,2
	.p2align	2, 0x0
$cppxdata$nounwind_c_boundary:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$nounwind_c_boundary@IMGREL
	.long	0
	.long	0
	.long	3
	.long	$ip2state$nounwind_c_boundary@IMGREL
	.long	56
	.long	0
	.long	1
$stateUnwindMap$nounwind_c_boundary:
	.long	-1
	.long	"?dtor$2@?0?nounwind_c_boundary@4HA"@IMGREL
$ip2state$nounwind_c_boundary:
	.long	.Lfunc_begin2@IMGREL
	.long	-1
	.long	.Ltmp10@IMGREL
	.long	0
	.long	.Ltmp11@IMGREL
	.long	-1
	.section	.text,"xr",one_only,nounwind_c_boundary,unique,4

	.def	passthrough_no_cleanup;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,passthrough_no_cleanup,unique,5
	.globl	passthrough_no_cleanup
	.p2align	4
passthrough_no_cleanup:
	rex64 jmpq	*%rcx

	.section	.data,"dw",discard,_RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info,unique,6
	.globl	_RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info
	.p2align	4, 0x0
_RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info:
	.quad	"??_7type_info@@6B@"
	.quad	0
	.asciz	"rust_panic"
	.zero	5

