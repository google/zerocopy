	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.att_syntax
	.file	"unwind_probe.e45a91751a911c8a-cgu.0"
	.def	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_;
	.scl	3;
	.type	32;
	.endef
	.text
	.p2align	4
_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_:
	jmp	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop

	.def	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop;
	.scl	2;
	.type	32;
	.endef
	.globl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	.p2align	4
_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop:
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
	.globl	catch_unwind_entry
	.p2align	4
catch_unwind_entry:
.Lfunc_begin0:
.seh_proc catch_unwind_entry
	.seh_handler rust_eh_personality, @unwind, @except
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	pushq	%rbx
	.seh_pushreg %rbx
	subq	$32, %rsp
	.seh_stackalloc 32
	.seh_endprologue
	xorl	%esi, %esi
.Ltmp0:
	callq	nested_cleanups
.Ltmp1:
.LBB2_8:
	movl	%esi, %eax
	.seh_startepilogue
	addq	$32, %rsp
	popq	%rbx
	popq	%rdi
	popq	%rsi
	.seh_endepilogue
	retq
.LBB2_2:
.Ltmp2:
.Ltmp3:
	movq	%rax, %rcx
	callq	_RNvNvNtCs9qcQDiGWtgW_3std9panicking12catch_unwind7cleanup
.Ltmp4:
	movq	%rax, %rdi
	testq	%rax, %rax
	je	.LBB2_8
	movq	%rdx, %rbx
	movq	(%rdx), %rax
	testq	%rax, %rax
	je	.LBB2_6
.Ltmp6:
	movq	%rdi, %rcx
	callq	*%rax
.Ltmp7:
.LBB2_6:
	movq	8(%rbx), %rdx
	movl	$1, %esi
	testq	%rdx, %rdx
	je	.LBB2_8
	movq	16(%rbx), %r8
	movq	%rdi, %rcx
	callq	_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
	jmp	.LBB2_8
.LBB2_9:
.Ltmp8:
	movq	%rax, %rsi
	movq	8(%rbx), %rdx
	testq	%rdx, %rdx
	je	.LBB2_11
	movq	16(%rbx), %r8
	movq	%rdi, %rcx
	callq	_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
.LBB2_11:
	movq	%rsi, %rcx
	callq	_Unwind_Resume
	ud2
.LBB2_1:
.Ltmp5:
	callq	_RNvNtCs2Ja4erDm0Jl_4core9panicking19panic_cannot_unwind
	ud2
.Lfunc_end0:
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table2:
.Lexception0:
	.byte	255
	.byte	0
	.uleb128 .Lttbase0-.Lttbaseref0
.Lttbaseref0:
	.byte	1
	.uleb128 .Lcst_end0-.Lcst_begin0
.Lcst_begin0:
	.uleb128 .Ltmp0-.Lfunc_begin0
	.uleb128 .Ltmp1-.Ltmp0
	.uleb128 .Ltmp2-.Lfunc_begin0
	.byte	3
	.uleb128 .Ltmp3-.Lfunc_begin0
	.uleb128 .Ltmp4-.Ltmp3
	.uleb128 .Ltmp5-.Lfunc_begin0
	.byte	1
	.uleb128 .Ltmp6-.Lfunc_begin0
	.uleb128 .Ltmp7-.Ltmp6
	.uleb128 .Ltmp8-.Lfunc_begin0
	.byte	0
	.uleb128 .Ltmp7-.Lfunc_begin0
	.uleb128 .Lfunc_end0-.Ltmp7
	.byte	0
	.byte	0
.Lcst_end0:
	.byte	127
	.byte	0
	.byte	1
	.byte	0
	.p2align	2, 0x0
	.quad	0
.Lttbase0:
	.byte	0
	.p2align	2, 0x0
	.text

	.def	frameless_leaf;
	.scl	2;
	.type	32;
	.endef
	.globl	frameless_leaf
	.p2align	4
frameless_leaf:
	leaq	42(%rcx), %rax
	retq

	.def	nested_cleanups;
	.scl	2;
	.type	32;
	.endef
	.globl	nested_cleanups
	.p2align	4
nested_cleanups:
.Lfunc_begin1:
.seh_proc nested_cleanups
	.seh_handler rust_eh_personality, @unwind, @except
	pushq	%rsi
	.seh_pushreg %rsi
	subq	$64, %rsp
	.seh_stackalloc 64
	.seh_endprologue
	movq	%rcx, 32(%rsp)
	movl	$1, 40(%rsp)
	movq	%rcx, 48(%rsp)
	movl	$2, 56(%rsp)
.Ltmp9:
	callq	*%rdx
.Ltmp10:
	leaq	48(%rsp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	leaq	32(%rsp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	nop
	.seh_startepilogue
	addq	$64, %rsp
	popq	%rsi
	.seh_endepilogue
	retq
.LBB4_2:
.Ltmp11:
	movq	%rax, %rsi
	leaq	48(%rsp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	leaq	32(%rsp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	movq	%rsi, %rcx
	callq	_Unwind_Resume
	ud2
.Lfunc_end1:
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table4:
.Lexception1:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end1-.Lcst_begin1
.Lcst_begin1:
	.uleb128 .Ltmp9-.Lfunc_begin1
	.uleb128 .Ltmp10-.Ltmp9
	.uleb128 .Ltmp11-.Lfunc_begin1
	.byte	0
	.uleb128 .Ltmp10-.Lfunc_begin1
	.uleb128 .Lfunc_end1-.Ltmp10
	.byte	0
	.byte	0
.Lcst_end1:
	.p2align	2, 0x0
	.text

	.def	nounwind_c_boundary;
	.scl	2;
	.type	32;
	.endef
	.globl	nounwind_c_boundary
	.p2align	4
nounwind_c_boundary:
.Lfunc_begin2:
.seh_proc nounwind_c_boundary
	.seh_handler rust_eh_personality, @unwind, @except
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	%rcx, 40(%rsp)
	movl	$9, 48(%rsp)
.Ltmp12:
	callq	*%rdx
.Ltmp13:
	leaq	40(%rsp), %rcx
	callq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	nop
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
.LBB5_2:
.Ltmp14:
	leaq	40(%rsp), %rcx
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_
	callq	_RNvNtCs2Ja4erDm0Jl_4core9panicking19panic_cannot_unwind
	ud2
.Lfunc_end2:
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table5:
.Lexception2:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end2-.Lcst_begin2
.Lcst_begin2:
	.uleb128 .Ltmp12-.Lfunc_begin2
	.uleb128 .Ltmp13-.Ltmp12
	.uleb128 .Ltmp14-.Lfunc_begin2
	.byte	0
.Lcst_end2:
	.p2align	2, 0x0
	.text

	.def	passthrough_no_cleanup;
	.scl	2;
	.type	32;
	.endef
	.globl	passthrough_no_cleanup
	.p2align	4
passthrough_no_cleanup:
	rex64 jmpq	*%rcx

