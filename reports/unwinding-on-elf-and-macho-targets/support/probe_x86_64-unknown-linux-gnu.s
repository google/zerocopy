	.att_syntax
	.file	"unwind_probe.e45a91751a911c8a-cgu.0"
	.section	.text._RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_,"ax",@progbits
	.prefalign	4, .Lfunc_end0, nop
	.type	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_,@function
_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_:
	.cfi_startproc
	jmpq	*_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop@GOTPCREL(%rip)
.Lfunc_end0:
	.size	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_, .Lfunc_end0-_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_
	.cfi_endproc

	.section	.text._RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop,"ax",@progbits
	.globl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop
	.prefalign	4, .Lfunc_end1, nop
	.type	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop,@function
_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop:
	.cfi_startproc
	movq	(%rdi), %rax
	movl	(%rax), %ecx
	leal	(%rcx,%rcx,4), %ecx
	addl	%ecx, %ecx
	addl	8(%rdi), %ecx
	movl	%ecx, (%rax)
	retq
.Lfunc_end1:
	.size	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop, .Lfunc_end1-_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop
	.cfi_endproc

	.section	.text.catch_unwind_entry,"ax",@progbits
	.globl	catch_unwind_entry
	.prefalign	4, .Lfunc_end2, nop
	.type	catch_unwind_entry,@function
catch_unwind_entry:
.Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception0
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	xorl	%ebx, %ebx
.Ltmp0:
	callq	*nested_cleanups@GOTPCREL(%rip)
.Ltmp1:
.LBB2_8:
	movl	%ebx, %eax
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.LBB2_2:
	.cfi_def_cfa_offset 32
.Ltmp2:
.Ltmp3:
	movq	%rax, %rdi
	callq	*_RNvNvNtCs8ZKwes1zzDd_3std9panicking12catch_unwind7cleanup@GOTPCREL(%rip)
.Ltmp4:
	movq	%rax, %r14
	testq	%rax, %rax
	je	.LBB2_8
	movq	%rdx, %r15
	movq	(%rdx), %rax
	testq	%rax, %rax
	je	.LBB2_6
.Ltmp6:
	movq	%r14, %rdi
	callq	*%rax
.Ltmp7:
.LBB2_6:
	movq	8(%r15), %rsi
	movl	$1, %ebx
	testq	%rsi, %rsi
	je	.LBB2_8
	movq	16(%r15), %rdx
	movq	%r14, %rdi
	callq	*_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc@GOTPCREL(%rip)
	jmp	.LBB2_8
.LBB2_9:
.Ltmp8:
	movq	%rax, %rbx
	movq	8(%r15), %rsi
	testq	%rsi, %rsi
	je	.LBB2_11
	movq	16(%r15), %rdx
	movq	%r14, %rdi
	callq	*_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc@GOTPCREL(%rip)
.LBB2_11:
	movq	%rbx, %rdi
	callq	_Unwind_Resume@PLT
.LBB2_1:
.Ltmp5:
	callq	*_RNvNtCskADBYZwJmSU_4core9panicking19panic_cannot_unwind@GOTPCREL(%rip)
.Lfunc_end2:
	.size	catch_unwind_entry, .Lfunc_end2-catch_unwind_entry
	.cfi_endproc
	.section	.gcc_except_table.catch_unwind_entry,"a",@progbits
	.p2align	2, 0x0
GCC_except_table2:
.Lexception0:
	.byte	255
	.byte	155
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
	.uleb128 .Lfunc_end2-.Ltmp7
	.byte	0
	.byte	0
.Lcst_end0:
	.byte	127
	.byte	0
	.byte	1
	.byte	0
	.p2align	2, 0x0
	.long	0
.Lttbase0:
	.byte	0
	.p2align	2, 0x0

	.section	.text.frameless_leaf,"ax",@progbits
	.globl	frameless_leaf
	.prefalign	4, .Lfunc_end3, nop
	.type	frameless_leaf,@function
frameless_leaf:
	.cfi_startproc
	leaq	42(%rdi), %rax
	retq
.Lfunc_end3:
	.size	frameless_leaf, .Lfunc_end3-frameless_leaf
	.cfi_endproc

	.section	.text.nested_cleanups,"ax",@progbits
	.globl	nested_cleanups
	.prefalign	4, .Lfunc_end4, nop
	.type	nested_cleanups,@function
nested_cleanups:
.Lfunc_begin1:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception1
	pushq	%r14
	.cfi_def_cfa_offset 16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	subq	$40, %rsp
	.cfi_def_cfa_offset 64
	.cfi_offset %rbx, -24
	.cfi_offset %r14, -16
	movq	%rdi, 8(%rsp)
	movl	$1, 16(%rsp)
	movq	%rdi, 24(%rsp)
	movl	$2, 32(%rsp)
.Ltmp9:
	callq	*%rsi
.Ltmp10:
	movq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop@GOTPCREL(%rip), %rbx
	leaq	24(%rsp), %rdi
	callq	*%rbx
	leaq	8(%rsp), %rdi
	callq	*%rbx
	addq	$40, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	retq
.LBB4_2:
	.cfi_def_cfa_offset 64
.Ltmp11:
	movq	%rax, %rbx
	movq	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop@GOTPCREL(%rip), %r14
	leaq	24(%rsp), %rdi
	callq	*%r14
	leaq	8(%rsp), %rdi
	callq	*%r14
	movq	%rbx, %rdi
	callq	_Unwind_Resume@PLT
.Lfunc_end4:
	.size	nested_cleanups, .Lfunc_end4-nested_cleanups
	.cfi_endproc
	.section	.gcc_except_table.nested_cleanups,"a",@progbits
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
	.uleb128 .Lfunc_end4-.Ltmp10
	.byte	0
	.byte	0
.Lcst_end1:
	.p2align	2, 0x0

	.section	.text.nounwind_c_boundary,"ax",@progbits
	.globl	nounwind_c_boundary
	.prefalign	4, .Lfunc_end5, nop
	.type	nounwind_c_boundary,@function
nounwind_c_boundary:
.Lfunc_begin2:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception2
	subq	$24, %rsp
	.cfi_def_cfa_offset 32
	movq	%rdi, 8(%rsp)
	movl	$9, 16(%rsp)
.Ltmp12:
	callq	*%rsi
.Ltmp13:
	leaq	8(%rsp), %rdi
	callq	*_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop@GOTPCREL(%rip)
	addq	$24, %rsp
	.cfi_def_cfa_offset 8
	retq
.LBB5_2:
	.cfi_def_cfa_offset 32
.Ltmp14:
	leaq	8(%rsp), %rdi
	callq	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_
	callq	*_RNvNtCskADBYZwJmSU_4core9panicking19panic_cannot_unwind@GOTPCREL(%rip)
.Lfunc_end5:
	.size	nounwind_c_boundary, .Lfunc_end5-nounwind_c_boundary
	.cfi_endproc
	.section	.gcc_except_table.nounwind_c_boundary,"a",@progbits
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

	.section	.text.passthrough_no_cleanup,"ax",@progbits
	.globl	passthrough_no_cleanup
	.prefalign	4, .Lfunc_end6, nop
	.type	passthrough_no_cleanup,@function
passthrough_no_cleanup:
	.cfi_startproc
	jmpq	*%rdi
.Lfunc_end6:
	.size	passthrough_no_cleanup, .Lfunc_end6-passthrough_no_cleanup
	.cfi_endproc

	.hidden	DW.ref.rust_eh_personality
	.weak	DW.ref.rust_eh_personality
	.section	.data.DW.ref.rust_eh_personality,"awG",@progbits,DW.ref.rust_eh_personality,comdat
	.p2align	3, 0x0
	.type	DW.ref.rust_eh_personality,@object
	.size	DW.ref.rust_eh_personality, 8
DW.ref.rust_eh_personality:
	.quad	rust_eh_personality
	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
