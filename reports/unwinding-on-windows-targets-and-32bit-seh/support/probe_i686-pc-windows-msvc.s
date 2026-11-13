	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 1
	.att_syntax
	.file	"unwind_probe.e45a91751a911c8a-cgu.0"
	.def	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop,unique,0
	.globl	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop
	.p2align	4
__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop:
	movl	4(%esp), %eax
	movl	(%eax), %ecx
	movl	(%ecx), %edx
	leal	(%edx,%edx,4), %edx
	addl	%edx, %edx
	addl	4(%eax), %edx
	movl	%edx, (%ecx)
	retl

	.def	_catch_unwind_entry;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_catch_unwind_entry,unique,1
	.globl	_catch_unwind_entry
	.p2align	4
_catch_unwind_entry:
Lfunc_begin0:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	pushl	%edi
	pushl	%esi
	subl	$28, %esp
	movl	%esp, -28(%ebp)
	movl	$-1, -16(%ebp)
	movl	$___ehhandler$catch_unwind_entry, -20(%ebp)
	movl	12(%ebp), %ecx
	movl	8(%ebp), %eax
	leal	-24(%ebp), %edx
	movl	%fs:0, %esi
	movl	%esi, -24(%ebp)
	movl	%edx, %fs:0
	movl	$0, -16(%ebp)
	pushl	%ecx
	pushl	%eax
	calll	_nested_cleanups
	addl	$8, %esp
LBB1_1:
	xorl	%eax, %eax
LBB1_2:
	movl	-24(%ebp), %ecx
	movl	%ecx, %fs:0
	addl	$28, %esp
	popl	%esi
	popl	%edi
	popl	%ebx
	popl	%ebp
	retl
LBB1_6:
	addl	$12, %ebp
	jmp	LBB1_11
LBB1_10:
	addl	$12, %ebp
	jmp	LBB1_11
LBB1_11:
$ehgcr_1_11:
	cmpl	$0, -36(%ebp)
	je	LBB1_1
	movl	-32(%ebp), %eax
	movl	(%eax), %eax
	testl	%eax, %eax
	je	LBB1_14
	movl	$6, -16(%ebp)
	pushl	-36(%ebp)
	calll	*%eax
	addl	$4, %esp
LBB1_14:
	movl	-32(%ebp), %eax
	movl	4(%eax), %eax
	testl	%eax, %eax
	je	LBB1_16
	movl	-32(%ebp), %ecx
	pushl	8(%ecx)
	pushl	%eax
	pushl	-36(%ebp)
	calll	__RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
	addl	$12, %esp
LBB1_16:
	movl	$1, %eax
	jmp	LBB1_2
	.def	"?catch$3@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?catch$3@?0?catch_unwind_entry@4HA":
LBB1_3:
	pushl	%ebp
	subl	$12, %esp
	addl	$12, %ebp
	movl	%esp, -28(%ebp)
	calll	__RNvNtCselTjGGDqQnQ_4core9panicking19panic_cannot_unwind
	ud2
	.def	"?catch$4@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?catch$4@?0?catch_unwind_entry@4HA":
LBB1_4:
	pushl	%ebp
	subl	$12, %esp
	addl	$12, %ebp
	movl	%esp, -28(%ebp)
	movl	$2, -16(%ebp)
	movl	-40(%ebp), %eax
	pushl	%eax
	calll	__RNvNvNtCs13X54pRMZqp_3std9panicking12catch_unwind7cleanup
	addl	$4, %esp
	movl	%eax, -36(%ebp)
	movl	%edx, -32(%ebp)
	movl	$LBB1_6, %eax
	addl	$12, %esp
	popl	%ebp
	retl
	.def	"?catch$7@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?catch$7@?0?catch_unwind_entry@4HA":
LBB1_7:
	pushl	%ebp
	subl	$12, %esp
	addl	$12, %ebp
	movl	%esp, -28(%ebp)
	calll	__RNvNtCselTjGGDqQnQ_4core9panicking19panic_cannot_unwind
	ud2
	.def	"?catch$8@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?catch$8@?0?catch_unwind_entry@4HA":
LBB1_8:
	pushl	%ebp
	subl	$12, %esp
	addl	$12, %ebp
	movl	%esp, -28(%ebp)
	movl	$4, -16(%ebp)
	pushl	$0
	calll	__RNvNvNtCs13X54pRMZqp_3std9panicking12catch_unwind7cleanup
	addl	$4, %esp
	movl	%eax, -36(%ebp)
	movl	%edx, -32(%ebp)
	movl	$LBB1_10, %eax
	addl	$12, %esp
	popl	%ebp
	retl
	.def	"?dtor$17@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$17@?0?catch_unwind_entry@4HA":
LBB1_17:
	pushl	%ebp
	subl	$12, %esp
	addl	$12, %ebp
	movl	-32(%ebp), %eax
	movl	4(%eax), %eax
	testl	%eax, %eax
	je	LBB1_19
	movl	-32(%ebp), %ecx
	pushl	8(%ecx)
	pushl	%eax
	pushl	-36(%ebp)
	calll	__RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
	addl	$12, %esp
LBB1_19:
	addl	$12, %esp
	popl	%ebp
	retl
Lfunc_end0:
	.section	.xdata,"dr",associative,_catch_unwind_entry,unique,0
	.p2align	2, 0x0
L__ehtable$catch_unwind_entry:
	.long	429065506
	.long	7
	.long	$stateUnwindMap$catch_unwind_entry
	.long	3
	.long	$tryMap$catch_unwind_entry
	.long	0
	.long	0
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
	.long	"?dtor$17@?0?catch_unwind_entry@4HA"
$tryMap$catch_unwind_entry:
	.long	2
	.long	2
	.long	3
	.long	1
	.long	$handlerMap$0$catch_unwind_entry
	.long	4
	.long	4
	.long	5
	.long	1
	.long	$handlerMap$1$catch_unwind_entry
	.long	0
	.long	0
	.long	5
	.long	2
	.long	$handlerMap$2$catch_unwind_entry
$handlerMap$0$catch_unwind_entry:
	.long	64
	.long	0
	.long	0
	.long	"?catch$3@?0?catch_unwind_entry@4HA"
$handlerMap$1$catch_unwind_entry:
	.long	64
	.long	0
	.long	0
	.long	"?catch$7@?0?catch_unwind_entry@4HA"
$handlerMap$2$catch_unwind_entry:
	.long	8
	.long	__RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info
	.long	-28
	.long	"?catch$4@?0?catch_unwind_entry@4HA"
	.long	64
	.long	0
	.long	0
	.long	"?catch$8@?0?catch_unwind_entry@4HA"
	.section	.text,"xr",one_only,_catch_unwind_entry,unique,1

	.def	_frameless_leaf;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_frameless_leaf,unique,2
	.globl	_frameless_leaf
	.p2align	4
_frameless_leaf:
	movl	4(%esp), %eax
	movl	8(%esp), %edx
	addl	$42, %eax
	adcl	$0, %edx
	retl

	.def	_nested_cleanups;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_nested_cleanups,unique,3
	.globl	_nested_cleanups
	.p2align	4
_nested_cleanups:
Lfunc_begin1:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	pushl	%edi
	pushl	%esi
	subl	$32, %esp
	movl	%esp, -28(%ebp)
	movl	$-1, -16(%ebp)
	movl	$___ehhandler$nested_cleanups, -20(%ebp)
	movl	8(%ebp), %eax
	leal	-24(%ebp), %ecx
	movl	%fs:0, %edx
	movl	%edx, -24(%ebp)
	movl	%ecx, %fs:0
	movl	%eax, -36(%ebp)
	movl	%eax, -44(%ebp)
	movl	$1, -32(%ebp)
	movl	$2, -40(%ebp)
	movl	$0, -16(%ebp)
	calll	*12(%ebp)
	leal	-44(%ebp), %eax
	pushl	%eax
	calll	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop
	addl	$4, %esp
	leal	-36(%ebp), %eax
	pushl	%eax
	calll	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop
	addl	$4, %esp
	movl	-24(%ebp), %eax
	movl	%eax, %fs:0
	addl	$32, %esp
	popl	%esi
	popl	%edi
	popl	%ebx
	popl	%ebp
	retl
	.def	"?dtor$2@?0?nested_cleanups@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$2@?0?nested_cleanups@4HA":
LBB3_2:
	pushl	%ebp
	pushl	%eax
	addl	$12, %ebp
	leal	-44(%ebp), %eax
	pushl	%eax
	calll	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop
	addl	$4, %esp
	leal	-36(%ebp), %eax
	pushl	%eax
	calll	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop
	addl	$8, %esp
	popl	%ebp
	retl
Lfunc_end1:
	.section	.xdata,"dr",associative,_nested_cleanups,unique,1
	.p2align	2, 0x0
L__ehtable$nested_cleanups:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$nested_cleanups
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	1
$stateUnwindMap$nested_cleanups:
	.long	-1
	.long	"?dtor$2@?0?nested_cleanups@4HA"
	.section	.text,"xr",one_only,_nested_cleanups,unique,3

	.def	_nounwind_c_boundary;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_nounwind_c_boundary,unique,4
	.globl	_nounwind_c_boundary
	.p2align	4
_nounwind_c_boundary:
Lfunc_begin2:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	pushl	%edi
	pushl	%esi
	subl	$24, %esp
	movl	%esp, -28(%ebp)
	movl	$-1, -16(%ebp)
	movl	$___ehhandler$nounwind_c_boundary, -20(%ebp)
	movl	8(%ebp), %eax
	leal	-24(%ebp), %ecx
	movl	%fs:0, %edx
	movl	%edx, -24(%ebp)
	movl	%ecx, %fs:0
	movl	%eax, -36(%ebp)
	movl	$9, -32(%ebp)
	movl	$0, -16(%ebp)
	calll	*12(%ebp)
	leal	-36(%ebp), %eax
	pushl	%eax
	calll	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop
	addl	$4, %esp
	movl	-24(%ebp), %eax
	movl	%eax, %fs:0
	addl	$24, %esp
	popl	%esi
	popl	%edi
	popl	%ebx
	popl	%ebp
	retl
	.def	"?dtor$2@?0?nounwind_c_boundary@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$2@?0?nounwind_c_boundary@4HA":
LBB4_2:
	pushl	%ebp
	pushl	%eax
	addl	$12, %ebp
	leal	-36(%ebp), %eax
	pushl	%eax
	calll	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop
	addl	$4, %esp
	calll	__RNvNtCselTjGGDqQnQ_4core9panicking19panic_cannot_unwind
	ud2
Lfunc_end2:
	.section	.xdata,"dr",associative,_nounwind_c_boundary,unique,2
	.p2align	2, 0x0
L__ehtable$nounwind_c_boundary:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$nounwind_c_boundary
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	1
$stateUnwindMap$nounwind_c_boundary:
	.long	-1
	.long	"?dtor$2@?0?nounwind_c_boundary@4HA"
	.section	.text,"xr",one_only,_nounwind_c_boundary,unique,4

	.def	_passthrough_no_cleanup;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_passthrough_no_cleanup,unique,5
	.globl	_passthrough_no_cleanup
	.p2align	4
_passthrough_no_cleanup:
	movl	4(%esp), %eax
	jmpl	*%eax

	.def	___ehhandler$catch_unwind_entry;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,___ehhandler$catch_unwind_entry,unique,6
	.p2align	4
___ehhandler$catch_unwind_entry:
	movl	$L__ehtable$catch_unwind_entry, %eax
	jmp	___CxxFrameHandler3

	.def	___ehhandler$nested_cleanups;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,___ehhandler$nested_cleanups,unique,7
	.p2align	4
___ehhandler$nested_cleanups:
	movl	$L__ehtable$nested_cleanups, %eax
	jmp	___CxxFrameHandler3

	.def	___ehhandler$nounwind_c_boundary;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,___ehhandler$nounwind_c_boundary,unique,8
	.p2align	4
___ehhandler$nounwind_c_boundary:
	movl	$L__ehtable$nounwind_c_boundary, %eax
	jmp	___CxxFrameHandler3

	.section	.data,"dw",discard,__RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info,unique,9
	.globl	__RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info
	.p2align	4, 0x0
__RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info:
	.long	"??_7type_info@@6B@"
	.long	0
	.asciz	"rust_panic"
	.zero	1

	.safeseh	___ehhandler$catch_unwind_entry
	.safeseh	___ehhandler$nested_cleanups
	.safeseh	___ehhandler$nounwind_c_boundary
