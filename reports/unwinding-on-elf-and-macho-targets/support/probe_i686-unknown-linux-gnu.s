	.att_syntax
	.file	"unwind_probe.e45a91751a911c8a-cgu.0"
	.section	.text._RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_,"ax",@progbits
	.prefalign	4, .Lfunc_end0, nop
	.type	_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_,@function
_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	subl	$8, %esp
	.cfi_def_cfa_offset 16
	.cfi_offset %ebx, -8
	calll	.L0$pb
	.cfi_adjust_cfa_offset 4
.L0$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
	movl	%ecx, (%esp)
.Ltmp0:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp0-.L0$pb), %ebx
	calll	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop@PLT
	addl	$8, %esp
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end0:
	.size	_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_, .Lfunc_end0-_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_
	.cfi_endproc

	.section	.text._RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop,"ax",@progbits
	.globl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop
	.prefalign	4, .Lfunc_end1, nop
	.type	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop,@function
_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop:
	.cfi_startproc
	movl	4(%esp), %eax
	movl	(%eax), %ecx
	movl	(%ecx), %edx
	leal	(%edx,%edx,4), %edx
	addl	%edx, %edx
	addl	4(%eax), %edx
	movl	%edx, (%ecx)
	retl
.Lfunc_end1:
	.size	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop, .Lfunc_end1-_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop
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
	pushl	%ebp
	.cfi_def_cfa_offset 8
	pushl	%ebx
	.cfi_def_cfa_offset 12
	pushl	%edi
	.cfi_def_cfa_offset 16
	pushl	%esi
	.cfi_def_cfa_offset 20
	subl	$12, %esp
	.cfi_def_cfa_offset 32
	.cfi_offset %esi, -20
	.cfi_offset %edi, -16
	.cfi_offset %ebx, -12
	.cfi_offset %ebp, -8
	movl	32(%esp), %eax
	movl	36(%esp), %ecx
	calll	.L2$pb
	.cfi_adjust_cfa_offset 4
.L2$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
	xorl	%esi, %esi
.Ltmp10:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp10-.L2$pb), %ebx
.Ltmp1:
	movl	%ecx, 4(%esp)
	movl	%eax, (%esp)
	calll	nested_cleanups@PLT
.Ltmp2:
.LBB2_8:
	movl	%esi, %eax
	addl	$12, %esp
	.cfi_def_cfa_offset 20
	popl	%esi
	.cfi_def_cfa_offset 16
	popl	%edi
	.cfi_def_cfa_offset 12
	popl	%ebx
	.cfi_def_cfa_offset 8
	popl	%ebp
	.cfi_def_cfa_offset 4
	retl
.LBB2_2:
	.cfi_def_cfa_offset 32
.Ltmp3:
.Ltmp4:
	movl	%eax, (%esp)
	calll	_RNvNvNtCsl0WIz0hVJ8g_3std9panicking12catch_unwind7cleanup@PLT
.Ltmp5:
	movl	%eax, %edi
	testl	%eax, %eax
	je	.LBB2_8
	movl	(%edx), %eax
	movl	%edx, %ebp
	testl	%eax, %eax
	je	.LBB2_6
.Ltmp7:
	movl	%edi, (%esp)
	calll	*%eax
.Ltmp8:
.LBB2_6:
	movl	4(%ebp), %eax
	movl	$1, %esi
	testl	%eax, %eax
	je	.LBB2_8
	movl	8(%ebp), %ecx
	movl	%eax, 4(%esp)
	movl	%edi, (%esp)
	movl	%ecx, 8(%esp)
	calll	_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc@PLT
	jmp	.LBB2_8
.LBB2_9:
.Ltmp9:
	movl	%eax, %esi
	movl	4(%ebp), %eax
	testl	%eax, %eax
	je	.LBB2_11
	movl	8(%ebp), %ecx
	movl	%eax, 4(%esp)
	movl	%edi, (%esp)
	movl	%ecx, 8(%esp)
	calll	_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc@PLT
.LBB2_11:
	movl	%esi, (%esp)
	calll	_Unwind_Resume@PLT
.LBB2_1:
.Ltmp6:
	calll	_RNvNtCsla01Uw4N3k7_4core9panicking19panic_cannot_unwind@PLT
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
	.uleb128 .Ltmp1-.Lfunc_begin0
	.uleb128 .Ltmp2-.Ltmp1
	.uleb128 .Ltmp3-.Lfunc_begin0
	.byte	3
	.uleb128 .Ltmp4-.Lfunc_begin0
	.uleb128 .Ltmp5-.Ltmp4
	.uleb128 .Ltmp6-.Lfunc_begin0
	.byte	1
	.uleb128 .Ltmp7-.Lfunc_begin0
	.uleb128 .Ltmp8-.Ltmp7
	.uleb128 .Ltmp9-.Lfunc_begin0
	.byte	0
	.uleb128 .Ltmp8-.Lfunc_begin0
	.uleb128 .Lfunc_end2-.Ltmp8
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
	movl	4(%esp), %eax
	movl	8(%esp), %edx
	addl	$42, %eax
	adcl	$0, %edx
	retl
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
	pushl	%ebx
	.cfi_def_cfa_offset 8
	pushl	%esi
	.cfi_def_cfa_offset 12
	subl	$20, %esp
	.cfi_def_cfa_offset 32
	.cfi_offset %esi, -12
	.cfi_offset %ebx, -8
	movl	32(%esp), %eax
	calll	.L4$pb
	.cfi_adjust_cfa_offset 4
.L4$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp14:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp14-.L4$pb), %ebx
	movl	%eax, 4(%esp)
	movl	%eax, 12(%esp)
	movl	$1, 8(%esp)
	movl	$2, 16(%esp)
.Ltmp11:
	calll	*36(%esp)
.Ltmp12:
	leal	12(%esp), %eax
	movl	%eax, (%esp)
	calll	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop@PLT
	leal	4(%esp), %eax
	movl	%eax, (%esp)
	calll	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop@PLT
	addl	$20, %esp
	.cfi_def_cfa_offset 12
	popl	%esi
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.LBB4_2:
	.cfi_def_cfa_offset 32
.Ltmp13:
	leal	12(%esp), %ecx
	movl	%eax, %esi
	movl	%ecx, (%esp)
	calll	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop@PLT
	leal	4(%esp), %eax
	movl	%eax, (%esp)
	calll	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop@PLT
	movl	%esi, (%esp)
	calll	_Unwind_Resume@PLT
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
	.uleb128 .Ltmp11-.Lfunc_begin1
	.uleb128 .Ltmp12-.Ltmp11
	.uleb128 .Ltmp13-.Lfunc_begin1
	.byte	0
	.uleb128 .Ltmp12-.Lfunc_begin1
	.uleb128 .Lfunc_end4-.Ltmp12
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
	pushl	%ebx
	.cfi_def_cfa_offset 8
	subl	$24, %esp
	.cfi_def_cfa_offset 32
	.cfi_offset %ebx, -8
	movl	32(%esp), %eax
	calll	.L5$pb
	.cfi_adjust_cfa_offset 4
.L5$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp18:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp18-.L5$pb), %ebx
	movl	%eax, 16(%esp)
	movl	$9, 20(%esp)
.Ltmp15:
	calll	*36(%esp)
.Ltmp16:
	leal	16(%esp), %eax
	movl	%eax, (%esp)
	calll	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop@PLT
	addl	$24, %esp
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.LBB5_2:
	.cfi_def_cfa_offset 32
.Ltmp17:
	leal	16(%esp), %ecx
	calll	_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_
	calll	_RNvNtCsla01Uw4N3k7_4core9panicking19panic_cannot_unwind@PLT
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
	.uleb128 .Ltmp15-.Lfunc_begin2
	.uleb128 .Ltmp16-.Ltmp15
	.uleb128 .Ltmp17-.Lfunc_begin2
	.byte	0
.Lcst_end2:
	.p2align	2, 0x0

	.section	.text.passthrough_no_cleanup,"ax",@progbits
	.globl	passthrough_no_cleanup
	.prefalign	4, .Lfunc_end6, nop
	.type	passthrough_no_cleanup,@function
passthrough_no_cleanup:
	.cfi_startproc
	movl	4(%esp), %eax
	jmpl	*%eax
.Lfunc_end6:
	.size	passthrough_no_cleanup, .Lfunc_end6-passthrough_no_cleanup
	.cfi_endproc

	.hidden	DW.ref.rust_eh_personality
	.weak	DW.ref.rust_eh_personality
	.section	.data.DW.ref.rust_eh_personality,"awG",@progbits,DW.ref.rust_eh_personality,comdat
	.p2align	2, 0x0
	.type	DW.ref.rust_eh_personality,@object
	.size	DW.ref.rust_eh_personality, 4
DW.ref.rust_eh_personality:
	.long	rust_eh_personality
	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
