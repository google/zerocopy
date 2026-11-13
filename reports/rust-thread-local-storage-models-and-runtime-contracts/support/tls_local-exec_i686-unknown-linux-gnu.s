	.att_syntax
	.file	"tls_probe.d6bd21401e7e8eac-cgu.0"
	.section	.text.unlikely._RINvMs0_NtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_,"ax",@progbits
	.prefalign	4, .Lfunc_end0, nop
	.type	_RINvMs0_NtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_,@function
_RINvMs0_NtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	pushl	%edi
	.cfi_def_cfa_offset 12
	pushl	%esi
	.cfi_def_cfa_offset 16
	subl	$32, %esp
	.cfi_def_cfa_offset 48
	.cfi_offset %esi, -16
	.cfi_offset %edi, -12
	.cfi_offset %ebx, -8
	movzbl	8(%ecx), %eax
	calll	.L0$pb
	.cfi_adjust_cfa_offset 4
.L0$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp0:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp0-.L0$pb), %ebx
	testl	%eax, %eax
	je	.LBB0_5
	cmpl	$1, %eax
	je	.LBB0_12
	xorl	%ecx, %ecx
	jmp	.LBB0_12
.LBB0_5:
	testl	%edx, %edx
	je	.LBB0_6
	movl	(%edx), %edi
	movl	8(%edx), %eax
	movl	4(%edx), %esi
	movl	$0, (%edx)
	cmpl	$1, %edi
	jne	.LBB0_6
	movl	%esi, (%ecx)
	movl	%eax, 4(%ecx)
	movb	$1, 8(%ecx)
	jmp	.LBB0_8
.LBB0_6:
	movl	$0, 20(%esp)
	movl	$13, 16(%esp)
	leal	16(%esp), %eax
	#APP
	#NO_APP
	movzbl	8(%ecx), %eax
	movsd	(%ecx), %xmm0
	movl	16(%esp), %edx
	movl	20(%esp), %esi
	cmpl	$1, %eax
	movsd	%xmm0, 24(%esp)
	movl	%esi, 4(%ecx)
	movl	%edx, (%ecx)
	movb	$1, 8(%ecx)
	jne	.LBB0_7
	leal	24(%esp), %eax
	movl	%ecx, %esi
	movl	%eax, (%esp)
	calll	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop@PLT
	jmp	.LBB0_11
.LBB0_7:
	testl	%eax, %eax
	jne	.LBB0_9
.LBB0_8:
	leal	_RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazy7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_@GOTOFF(%ebx), %eax
	movl	%ecx, %esi
	movl	%ecx, (%esp)
	movl	%eax, 4(%esp)
	calll	_RNvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local11destructors10linux_like8register@PLT
.LBB0_11:
	movl	%esi, %ecx
.LBB0_12:
	movl	%ecx, %eax
	addl	$32, %esp
	.cfi_def_cfa_offset 16
	popl	%esi
	.cfi_def_cfa_offset 12
	popl	%edi
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.LBB0_9:
	.cfi_def_cfa_offset 48
	leal	16(%esp), %esi
	leal	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.0@GOTOFF(%ebx), %eax
	leal	15(%esp), %edx
	movl	$87, 4(%esp)
	movl	%esi, %ecx
	movl	%eax, (%esp)
	calll	_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	movl	%esi, %ecx
	calll	_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	calll	_RNvNtCsl0WIz0hVJ8g_3std7process5abort@PLT
.Lfunc_end0:
	.size	_RINvMs0_NtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_, .Lfunc_end0-_RINvMs0_NtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	.cfi_endproc

	.section	.text._RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end1, nop
	.type	_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe,@function
_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	subl	$8, %esp
	.cfi_def_cfa_offset 16
	.cfi_offset %ebx, -8
	calll	.L1$pb
	.cfi_adjust_cfa_offset 4
.L1$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp1:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp1-.L1$pb), %ebx
	cmpb	$3, (%ecx)
	jne	.LBB1_2
	addl	$4, %ecx
	movl	%ecx, (%esp)
	calll	_RNvXsd_NtNtCsla01Uw4N3k7_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@PLT
.LBB1_2:
	addl	$8, %esp
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end1:
	.size	_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe, .Lfunc_end1-_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end2, nop
	.type	_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe,@function
_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe:
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
.Ltmp2:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp2-.L2$pb), %ebx
	cmpb	$3, (%eax)
	jne	.LBB2_2
	addl	$4, %eax
	movl	%eax, (%esp)
	calll	_RNvXsd_NtNtCsla01Uw4N3k7_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@PLT
.LBB2_2:
	addl	$8, %esp
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end2:
	.size	_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe, .Lfunc_end2-_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazy7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_,"ax",@progbits
	.prefalign	4, .Lfunc_end3, nop
	.type	_RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazy7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_,@function
_RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazy7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_:
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
.Ltmp3:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp3-.L3$pb), %ebx
	movzbl	8(%eax), %ecx
	movb	$2, 8(%eax)
	cmpb	$1, %cl
	jne	.LBB3_2
	movl	%eax, (%esp)
	calll	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop@PLT
.LBB3_2:
	addl	$8, %esp
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end3:
	.size	_RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazy7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_, .Lfunc_end3-_RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazy7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_
	.cfi_endproc

	.section	.text._RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native5eager7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_,"ax",@progbits
	.prefalign	4, .Lfunc_end4, nop
	.type	_RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native5eager7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_,@function
_RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native5eager7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	subl	$8, %esp
	.cfi_def_cfa_offset 16
	.cfi_offset %ebx, -8
	movl	16(%esp), %eax
	calll	.L4$pb
	.cfi_adjust_cfa_offset 4
.L4$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp4:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp4-.L4$pb), %ebx
	movb	$2, 8(%eax)
	movl	%eax, (%esp)
	calll	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop@PLT
	addl	$8, %esp
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end4:
	.size	_RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native5eager7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_, .Lfunc_end4-_RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native5eager7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_
	.cfi_endproc

	.section	.text._RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop,"ax",@progbits
	.globl	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop
	.prefalign	4, .Lfunc_end5, nop
	.type	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop,@function
_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop:
	.cfi_startproc
	subl	$12, %esp
	.cfi_def_cfa_offset 16
	movl	16(%esp), %eax
	movsd	(%eax), %xmm0
	movl	%esp, %eax
	movsd	%xmm0, (%esp)
	#APP
	#NO_APP
	addl	$12, %esp
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end5:
	.size	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop, .Lfunc_end5-_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsla01Uw4N3k7_4core3ops4drop4Drop4drop
	.cfi_endproc

	.section	.text._RNvXNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end6, nop
	.type	_RNvXNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,@function
_RNvXNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception0
	pushl	%ebx
	.cfi_def_cfa_offset 8
	pushl	%esi
	.cfi_def_cfa_offset 12
	subl	$36, %esp
	.cfi_def_cfa_offset 48
	.cfi_offset %esi, -12
	.cfi_offset %ebx, -8
	movl	48(%esp), %esi
	movl	56(%esp), %ecx
	movl	52(%esp), %eax
	calll	.L6$pb
	.cfi_adjust_cfa_offset 4
.L6$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp8:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp8-.L6$pb), %ebx
	movl	8(%esi), %edx
	movl	%ecx, 4(%esp)
	leal	24(%esp), %ecx
	movl	%eax, (%esp)
	calll	_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	movzbl	24(%esp), %eax
	cmpb	$-1, %al
	je	.LBB6_4
	cmpb	$3, (%esi)
	jne	.LBB6_3
	movb	%al, 23(%esp)
	leal	4(%esi), %eax
.Ltmp5:
	movl	%eax, (%esp)
	calll	_RNvXsd_NtNtCsla01Uw4N3k7_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@PLT
	movzbl	23(%esp), %eax
.Ltmp6:
.LBB6_3:
	movsd	24(%esp), %xmm0
	movsd	%xmm0, (%esi)
.LBB6_4:
	cmpb	$-1, %al
	setne	%al
	addl	$36, %esp
	.cfi_def_cfa_offset 12
	popl	%esi
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.LBB6_5:
	.cfi_def_cfa_offset 48
.Ltmp7:
	movsd	24(%esp), %xmm0
	movl	%eax, (%esp)
	movsd	%xmm0, (%esi)
	calll	_Unwind_Resume@PLT
.Lfunc_end6:
	.size	_RNvXNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe, .Lfunc_end6-_RNvXNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.gcc_except_table._RNvXNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table6:
.Lexception0:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end0-.Lcst_begin0
.Lcst_begin0:
	.uleb128 .Lfunc_begin0-.Lfunc_begin0
	.uleb128 .Ltmp5-.Lfunc_begin0
	.byte	0
	.byte	0
	.uleb128 .Ltmp5-.Lfunc_begin0
	.uleb128 .Ltmp6-.Ltmp5
	.uleb128 .Ltmp7-.Lfunc_begin0
	.byte	0
	.uleb128 .Ltmp6-.Lfunc_begin0
	.uleb128 .Lfunc_end6-.Ltmp6
	.byte	0
	.byte	0
.Lcst_end0:
	.p2align	2, 0x0

	.section	.text._RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end7, nop
	.type	_RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,@function
_RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin1:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception1
	pushl	%ebx
	.cfi_def_cfa_offset 8
	pushl	%edi
	.cfi_def_cfa_offset 12
	pushl	%esi
	.cfi_def_cfa_offset 16
	subl	$32, %esp
	.cfi_def_cfa_offset 48
	.cfi_offset %esi, -16
	.cfi_offset %edi, -12
	.cfi_offset %ebx, -8
	movl	52(%esp), %ecx
	movl	48(%esp), %esi
	calll	.L7$pb
	.cfi_adjust_cfa_offset 4
.L7$pb:
	popl	%edi
	.cfi_adjust_cfa_offset -4
	movl	$0, 16(%esp)
.Ltmp12:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp12-.L7$pb), %edi
	cmpl	$128, %ecx
	jae	.LBB7_1
	movb	%cl, 16(%esp)
	movl	$1, %eax
	jmp	.LBB7_6
.LBB7_1:
	movl	%ecx, %eax
	movl	%ecx, %edx
	andb	$63, %al
	shrl	$6, %edx
	orb	$-128, %al
	cmpl	$2048, %ecx
	jae	.LBB7_3
	orb	$-64, %dl
	movb	%dl, 16(%esp)
	movb	%al, 17(%esp)
	movl	$2, %eax
	jmp	.LBB7_6
.LBB7_3:
	andb	$63, %dl
	movl	%ecx, %ebx
	orb	$-128, %dl
	shrl	$12, %ebx
	cmpl	$65535, %ecx
	ja	.LBB7_5
	orb	$-32, %bl
	movb	%bl, 16(%esp)
	movb	%dl, 17(%esp)
	movb	%al, 18(%esp)
	movl	$3, %eax
	jmp	.LBB7_6
.LBB7_5:
	andb	$63, %bl
	shrl	$18, %ecx
	orb	$-16, %cl
	orb	$-128, %bl
	movb	%cl, 16(%esp)
	movb	%bl, 17(%esp)
	movb	%dl, 18(%esp)
	movb	%al, 19(%esp)
	movl	$4, %eax
.LBB7_6:
	movl	8(%esi), %edx
	movl	%eax, 4(%esp)
	leal	16(%esp), %eax
	leal	24(%esp), %ecx
	movl	%edi, %ebx
	movl	%eax, (%esp)
	calll	_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	movzbl	24(%esp), %eax
	cmpb	$-1, %al
	je	.LBB7_10
	cmpb	$3, (%esi)
	jne	.LBB7_9
	movb	%al, 23(%esp)
	leal	4(%esi), %eax
.Ltmp9:
	movl	%edi, %ebx
	movl	%eax, (%esp)
	calll	_RNvXsd_NtNtCsla01Uw4N3k7_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@PLT
	movzbl	23(%esp), %eax
.Ltmp10:
.LBB7_9:
	movsd	24(%esp), %xmm0
	movsd	%xmm0, (%esi)
.LBB7_10:
	cmpb	$-1, %al
	setne	%al
	addl	$32, %esp
	.cfi_def_cfa_offset 16
	popl	%esi
	.cfi_def_cfa_offset 12
	popl	%edi
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.LBB7_12:
	.cfi_def_cfa_offset 48
.Ltmp11:
	movsd	24(%esp), %xmm0
	movl	%edi, %ebx
	movl	%eax, (%esp)
	movsd	%xmm0, (%esi)
	calll	_Unwind_Resume@PLT
.Lfunc_end7:
	.size	_RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe, .Lfunc_end7-_RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.gcc_except_table._RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table7:
.Lexception1:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end1-.Lcst_begin1
.Lcst_begin1:
	.uleb128 .Lfunc_begin1-.Lfunc_begin1
	.uleb128 .Ltmp9-.Lfunc_begin1
	.byte	0
	.byte	0
	.uleb128 .Ltmp9-.Lfunc_begin1
	.uleb128 .Ltmp10-.Ltmp9
	.uleb128 .Ltmp11-.Lfunc_begin1
	.byte	0
	.uleb128 .Ltmp10-.Lfunc_begin1
	.uleb128 .Lfunc_end7-.Ltmp10
	.byte	0
	.byte	0
.Lcst_end1:
	.p2align	2, 0x0

	.section	.text._RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end8, nop
	.type	_RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,@function
_RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	subl	$8, %esp
	.cfi_def_cfa_offset 16
	.cfi_offset %ebx, -8
	calll	.L8$pb
	.cfi_adjust_cfa_offset 4
.L8$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp13:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp13-.L8$pb), %ebx
	leal	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.3@GOTOFF(%ebx), %eax
	pushl	24(%esp)
	.cfi_adjust_cfa_offset 4
	pushl	24(%esp)
	.cfi_adjust_cfa_offset 4
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	pushl	28(%esp)
	.cfi_adjust_cfa_offset 4
	calll	_RNvNtCsla01Uw4N3k7_4core3fmt5write@PLT
	addl	$24, %esp
	.cfi_adjust_cfa_offset -24
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end8:
	.size	_RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe, .Lfunc_end8-_RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end9, nop
	.type	_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,@function
_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin2:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception2
	pushl	%ebp
	.cfi_def_cfa_offset 8
	pushl	%ebx
	.cfi_def_cfa_offset 12
	pushl	%edi
	.cfi_def_cfa_offset 16
	pushl	%esi
	.cfi_def_cfa_offset 20
	subl	$28, %esp
	.cfi_def_cfa_offset 48
	.cfi_offset %esi, -20
	.cfi_offset %edi, -16
	.cfi_offset %ebx, -12
	.cfi_offset %ebp, -8
	movl	52(%esp), %esi
	calll	.L9$pb
	.cfi_adjust_cfa_offset 4
.L9$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
	movl	%edx, 24(%esp)
	movl	%ecx, 16(%esp)
.Ltmp25:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp25-.L9$pb), %ebx
	testl	%esi, %esi
	je	.LBB9_11
	movl	48(%esp), %ebp
	leal	8(%esp), %edi
	leal	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.9@GOTOFF(%ebx), %eax
	movl	%eax, 20(%esp)
	jmp	.LBB9_2
.LBB9_9:
	movl	12(%esp), %eax
	cmpb	$35, 8(%eax)
	jne	.LBB9_16
	.p2align	4
.LBB9_10:
	testl	%esi, %esi
	je	.LBB9_11
.LBB9_2:
	.cfi_escape 0x2e, 0x10
	pushl	%esi
	.cfi_adjust_cfa_offset 4
	pushl	%ebp
	.cfi_adjust_cfa_offset 4
	pushl	32(%esp)
	.cfi_adjust_cfa_offset 4
	pushl	%edi
	.cfi_adjust_cfa_offset 4
	calll	_RNvXs3_NtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unixNtB5_6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write5write@PLT
	.cfi_adjust_cfa_offset -4
	addl	$12, %esp
	.cfi_adjust_cfa_offset -12
	movzbl	8(%esp), %eax
	cmpl	$255, %eax
	je	.LBB9_14
	movl	.LJTI9_0@GOTOFF(%ebx,%eax,4), %eax
	addl	%ebx, %eax
	jmpl	*%eax
.LBB9_4:
	movl	12(%esp), %edi
.Ltmp14:
	.cfi_escape 0x2e, 0x00
	calll	_RNvNtNtNtCsla01Uw4N3k7_4core2io5error12os_functions16get_os_functions@PLT
.Ltmp15:
	movl	8(%eax), %eax
.Ltmp16:
	.cfi_escape 0x2e, 0x10
	subl	$12, %esp
	.cfi_adjust_cfa_offset 12
	pushl	%edi
	.cfi_adjust_cfa_offset 4
	calll	*%eax
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
.Ltmp17:
	testb	%al, %al
	je	.LBB9_7
	cmpb	$3, 8(%esp)
	leal	8(%esp), %edi
	jne	.LBB9_10
	jmp	.LBB9_13
	.p2align	4
.LBB9_14:
	movl	12(%esp), %eax
	testl	%eax, %eax
	je	.LBB9_15
	movl	%esi, %ecx
	subl	%eax, %ecx
	jb	.LBB9_26
	addl	%eax, %ebp
	movl	%ecx, %esi
	jmp	.LBB9_10
.LBB9_12:
	movl	12(%esp), %eax
	cmpb	$35, 16(%eax)
	jne	.LBB9_16
.LBB9_13:
	.cfi_escape 0x2e, 0x10
	subl	$12, %esp
	.cfi_adjust_cfa_offset 12
	leal	24(%esp), %eax
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	calll	_RNvXsd_NtNtCsla01Uw4N3k7_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@PLT
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
	jmp	.LBB9_10
.LBB9_8:
	cmpb	$35, 9(%esp)
	je	.LBB9_10
	jmp	.LBB9_16
.LBB9_11:
	movl	16(%esp), %eax
	movb	$-1, (%eax)
	jmp	.LBB9_17
.LBB9_15:
	movl	20(%esp), %edi
	jmp	.LBB9_16
.LBB9_7:
	leal	8(%esp), %edi
.LBB9_16:
	movl	16(%esp), %eax
	movsd	(%edi), %xmm0
	movsd	%xmm0, (%eax)
.LBB9_17:
	addl	$28, %esp
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
.LBB9_26:
	.cfi_def_cfa_offset 48
.Ltmp19:
	.cfi_escape 0x2e, 0x10
	leal	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.10@GOTOFF(%ebx), %ecx
	pushl	%ecx
	.cfi_adjust_cfa_offset 4
	pushl	%esi
	.cfi_adjust_cfa_offset 4
	pushl	%esi
	.cfi_adjust_cfa_offset 4
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	calll	_RNvNtNtCsla01Uw4N3k7_4core5slice5index16slice_index_fail@PLT
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
.Ltmp20:
	ud2
.LBB9_21:
.Ltmp18:
	jmp	.LBB9_23
.LBB9_22:
.Ltmp21:
.LBB9_23:
	cmpb	$3, 8(%esp)
	movl	%eax, %esi
	jne	.LBB9_25
.Ltmp22:
	.cfi_escape 0x2e, 0x10
	subl	$12, %esp
	.cfi_adjust_cfa_offset 12
	leal	24(%esp), %eax
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	calll	_RNvXsd_NtNtCsla01Uw4N3k7_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@PLT
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
.Ltmp23:
.LBB9_25:
	.cfi_escape 0x2e, 0x10
	subl	$12, %esp
	.cfi_adjust_cfa_offset 12
	pushl	%esi
	.cfi_adjust_cfa_offset 4
	calll	_Unwind_Resume@PLT
.LBB9_28:
	.cfi_def_cfa_offset 48
.Ltmp24:
	.cfi_escape 0x2e, 0x00
	calll	_RNvNtCsla01Uw4N3k7_4core9panicking16panic_in_cleanup@PLT
.Lfunc_end9:
	.size	_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe, .Lfunc_end9-_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.rodata._RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
.LJTI9_0:
	.long	.LBB9_4@GOTOFF
	.long	.LBB9_8@GOTOFF
	.long	.LBB9_9@GOTOFF
	.long	.LBB9_12@GOTOFF
	.section	.gcc_except_table._RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table9:
.Lexception2:
	.byte	255
	.byte	155
	.uleb128 .Lttbase0-.Lttbaseref0
.Lttbaseref0:
	.byte	1
	.uleb128 .Lcst_end2-.Lcst_begin2
.Lcst_begin2:
	.uleb128 .Lfunc_begin2-.Lfunc_begin2
	.uleb128 .Ltmp14-.Lfunc_begin2
	.byte	0
	.byte	0
	.uleb128 .Ltmp14-.Lfunc_begin2
	.uleb128 .Ltmp17-.Ltmp14
	.uleb128 .Ltmp18-.Lfunc_begin2
	.byte	0
	.uleb128 .Ltmp17-.Lfunc_begin2
	.uleb128 .Ltmp19-.Ltmp17
	.byte	0
	.byte	0
	.uleb128 .Ltmp19-.Lfunc_begin2
	.uleb128 .Ltmp20-.Ltmp19
	.uleb128 .Ltmp21-.Lfunc_begin2
	.byte	0
	.uleb128 .Ltmp22-.Lfunc_begin2
	.uleb128 .Ltmp23-.Ltmp22
	.uleb128 .Ltmp24-.Lfunc_begin2
	.byte	1
	.uleb128 .Ltmp23-.Lfunc_begin2
	.uleb128 .Lfunc_end9-.Ltmp23
	.byte	0
	.byte	0
.Lcst_end2:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase0:
	.byte	0
	.p2align	2, 0x0

	.section	.text._RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end10, nop
	.type	_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,@function
_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin3:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception3
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
	movl	%ecx, %esi
	movl	32(%esp), %eax
	movl	36(%esp), %ecx
	calll	.L10$pb
	.cfi_adjust_cfa_offset 4
.L10$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
	movl	%edx, 8(%esp)
	movb	$-1, (%esi)
.Ltmp34:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp34-.L10$pb), %ebx
	movsd	(%esi), %xmm0
	movsd	%xmm0, (%esp)
.Ltmp26:
	.cfi_escape 0x2e, 0x10
	leal	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.3@GOTOFF(%ebx), %edx
	movl	%esp, %edi
	pushl	%ecx
	.cfi_adjust_cfa_offset 4
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	pushl	%edx
	.cfi_adjust_cfa_offset 4
	pushl	%edi
	.cfi_adjust_cfa_offset 4
	calll	_RNvNtCsla01Uw4N3k7_4core3fmt5write@PLT
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
.Ltmp27:
	movzbl	(%esp), %ecx
	testb	%al, %al
	je	.LBB10_8
	cmpb	$-1, %cl
	je	.LBB10_3
	movsd	(%esp), %xmm0
	movsd	%xmm0, (%esi)
	jmp	.LBB10_12
.LBB10_8:
	cmpb	$3, %cl
	jne	.LBB10_12
	leal	4(%esp), %eax
	.cfi_escape 0x2e, 0x10
	subl	$12, %esp
	.cfi_adjust_cfa_offset 12
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	calll	_RNvXsd_NtNtCsla01Uw4N3k7_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@PLT
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
.LBB10_12:
	movl	%esi, %eax
	addl	$16, %esp
	.cfi_def_cfa_offset 16
	popl	%esi
	.cfi_def_cfa_offset 12
	popl	%edi
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.LBB10_3:
	.cfi_def_cfa_offset 32
.Ltmp28:
	.cfi_escape 0x2e, 0x10
	subl	$4, %esp
	.cfi_adjust_cfa_offset 4
	leal	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.6@GOTOFF(%ebx), %eax
	leal	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.4@GOTOFF(%ebx), %ecx
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	pushl	$173
	.cfi_adjust_cfa_offset 4
	pushl	%ecx
	.cfi_adjust_cfa_offset 4
	calll	_RNvNtCsla01Uw4N3k7_4core9panicking9panic_fmt@PLT
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
.Ltmp29:
	ud2
.LBB10_5:
.Ltmp30:
	cmpb	$3, (%esp)
	movl	%eax, %esi
	jne	.LBB10_7
	leal	4(%esp), %eax
.Ltmp31:
	.cfi_escape 0x2e, 0x10
	subl	$12, %esp
	.cfi_adjust_cfa_offset 12
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	calll	_RNvXsd_NtNtCsla01Uw4N3k7_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@PLT
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
.Ltmp32:
.LBB10_7:
	.cfi_escape 0x2e, 0x10
	subl	$12, %esp
	.cfi_adjust_cfa_offset 12
	pushl	%esi
	.cfi_adjust_cfa_offset 4
	calll	_Unwind_Resume@PLT
.LBB10_10:
	.cfi_def_cfa_offset 32
.Ltmp33:
	.cfi_escape 0x2e, 0x00
	calll	_RNvNtCsla01Uw4N3k7_4core9panicking16panic_in_cleanup@PLT
.Lfunc_end10:
	.size	_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe, .Lfunc_end10-_RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.gcc_except_table._RNvYNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrNtNtNtCsla01Uw4N3k7_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table10:
.Lexception3:
	.byte	255
	.byte	155
	.uleb128 .Lttbase1-.Lttbaseref1
.Lttbaseref1:
	.byte	1
	.uleb128 .Lcst_end3-.Lcst_begin3
.Lcst_begin3:
	.uleb128 .Ltmp26-.Lfunc_begin3
	.uleb128 .Ltmp27-.Ltmp26
	.uleb128 .Ltmp30-.Lfunc_begin3
	.byte	0
	.uleb128 .Ltmp27-.Lfunc_begin3
	.uleb128 .Ltmp28-.Ltmp27
	.byte	0
	.byte	0
	.uleb128 .Ltmp28-.Lfunc_begin3
	.uleb128 .Ltmp29-.Ltmp28
	.uleb128 .Ltmp30-.Lfunc_begin3
	.byte	0
	.uleb128 .Ltmp31-.Lfunc_begin3
	.uleb128 .Ltmp32-.Ltmp31
	.uleb128 .Ltmp33-.Lfunc_begin3
	.byte	1
	.uleb128 .Ltmp32-.Lfunc_begin3
	.uleb128 .Lfunc_end10-.Ltmp32
	.byte	0
	.byte	0
.Lcst_end3:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase1:
	.byte	0
	.p2align	2, 0x0

	.section	.text.access_all_tls,"ax",@progbits
	.globl	access_all_tls
	.prefalign	4, .Lfunc_end11, nop
	.type	access_all_tls,@function
access_all_tls:
	.cfi_startproc
	pushl	%ebp
	.cfi_def_cfa_offset 8
	pushl	%ebx
	.cfi_def_cfa_offset 12
	pushl	%edi
	.cfi_def_cfa_offset 16
	pushl	%esi
	.cfi_def_cfa_offset 20
	subl	$44, %esp
	.cfi_def_cfa_offset 64
	.cfi_offset %esi, -20
	.cfi_offset %edi, -16
	.cfi_offset %ebx, -12
	.cfi_offset %ebp, -8
	movl	%gs:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@NTPOFF, %edi
	movl	%gs:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@NTPOFF+4, %eax
	calll	.L11$pb
	.cfi_adjust_cfa_offset 4
.L11$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
	movl	%gs:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL@NTPOFF+4, %esi
	movl	%gs:_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64@NTPOFF+4, %edx
.Ltmp35:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp35-.L11$pb), %ebx
	addl	$1, %edi
	movl	%esi, 40(%esp)
	movl	%gs:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL@NTPOFF, %esi
	adcl	$0, %eax
	movl	%edi, %gs:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@NTPOFF
	movl	%eax, %gs:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@NTPOFF+4
	movl	%eax, 36(%esp)
	movl	%gs:_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64@NTPOFF, %eax
	movl	%gs:0, %ecx
	leal	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@NTPOFF(%ecx), %ebp
	movzbl	%gs:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@NTPOFF+8, %ecx
	testl	%ecx, %ecx
	jne	.LBB11_1
.LBB11_3:
	movl	(%ebp), %ecx
	cmpb	$1, %gs:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@NTPOFF+8
	movl	%esi, 24(%esp)
	movl	%ecx, 28(%esp)
	movl	4(%ebp), %ecx
	movl	%ecx, 32(%esp)
	movl	%gs:0, %ecx
	leal	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@NTPOFF(%ecx), %ecx
	jne	.LBB11_5
	movl	(%ecx), %ebp
	movl	4(%ecx), %esi
.LBB11_6:
	movl	%gs:0, %ecx
	cmpb	$1, %gs:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@NTPOFF+8
	leal	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@NTPOFF(%ecx), %ecx
	jne	.LBB11_7
.LBB11_8:
	addl	%edi, %eax
	adcl	36(%esp), %edx
	addl	24(%esp), %eax
	adcl	40(%esp), %edx
	addl	28(%esp), %eax
	adcl	32(%esp), %edx
	addl	%ebp, %eax
	adcl	%esi, %edx
	addl	(%ecx), %eax
	adcl	4(%ecx), %edx
	addl	$44, %esp
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
.LBB11_5:
	.cfi_def_cfa_offset 64
	movl	$0, 20(%esp)
	movl	$7, 16(%esp)
	leal	16(%esp), %ebp
	#APP
	#NO_APP
	movl	16(%esp), %esi
	movl	%esi, 12(%esp)
	movl	20(%esp), %esi
	movl	%esi, 8(%esp)
	movl	8(%esp), %ebp
	movl	8(%esp), %esi
	movl	%ebp, 4(%ecx)
	movl	12(%esp), %ebp
	movl	%ebp, (%ecx)
	movb	$1, 8(%ecx)
	jmp	.LBB11_6
.LBB11_7:
	movl	%edx, 12(%esp)
	xorl	%edx, %edx
	movl	%eax, 8(%esp)
	calll	_RINvMs0_NtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	movl	%eax, %ecx
	movl	12(%esp), %edx
	movl	8(%esp), %eax
	testl	%ecx, %ecx
	jne	.LBB11_8
	jmp	.LBB11_9
.LBB11_1:
	cmpl	$1, %ecx
	jne	.LBB11_9
	leal	_RINvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local6native5eager7destroyINtNtCsla01Uw4N3k7_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_@GOTOFF(%ebx), %ecx
	movl	%ebp, (%esp)
	movl	%edx, 12(%esp)
	movl	%eax, 8(%esp)
	movl	%ecx, 4(%esp)
	calll	_RNvNtNtNtNtCsl0WIz0hVJ8g_3std3sys12thread_local11destructors10linux_like8register@PLT
	movl	8(%esp), %eax
	movl	12(%esp), %edx
	movb	$0, 8(%ebp)
	jmp	.LBB11_3
.LBB11_9:
	leal	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.2@GOTOFF(%ebx), %eax
	movl	%eax, (%esp)
	calll	_RNvNtNtCsl0WIz0hVJ8g_3std6thread5local18panic_access_error@PLT
.Lfunc_end11:
	.size	access_all_tls, .Lfunc_end11-access_all_tls
	.cfi_endproc

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.0,@object
	.section	.rodata..Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.0,"a",@progbits
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.0:
	.ascii	"fatal runtime error: unreachable, aborting\n"
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.0, 43

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.1,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.1:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/std/src/thread/local.rs"
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.1, 134

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.2,@object
	.section	.data.rel.ro..Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.2,"aw",@progbits
	.p2align	2, 0x0
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.2:
	.long	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.1
	.asciz	"\205\000\000\000\255\001\000\000\031\000\000"
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.2, 16

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.3,@object
	.section	.data.rel.ro..Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.3,"aw",@progbits
	.p2align	2, 0x0
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.3:
	.long	_RINvNtCsla01Uw4N3k7_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe
	.asciz	"\f\000\000\000\004\000\000"
	.long	_RNvXNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.long	_RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.long	_RNvYINtNvNtNtCsla01Uw4N3k7_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsl0WIz0hVJ8g_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.3, 24

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.4,@object
	.section	.rodata..Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.4,"a",@progbits
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.4:
	.ascii	"a formatting trait implementation returned an error when the underlying stream did not"
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.4, 86

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.5,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.5:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/io/write.rs"
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.5, 131

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.6,@object
	.section	.data.rel.ro..Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.6,"aw",@progbits
	.p2align	2, 0x0
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.6:
	.long	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.5
	.asciz	"\202\000\000\000\233\001\000\000\021\000\000"
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.6, 16

	.type	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,@object
	.section	.tdata._RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,"awT",@progbits
	.globl	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	.p2align	2, 0x0
_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64:
	.ascii	"\210wfUD3\"\021"
	.size	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64, 8

	.type	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64,@object
	.section	.tdata._RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64,"awT",@progbits
	.globl	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	.p2align	6, 0x0
_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64:
	.asciz	"\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000"
	.size	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64, 64

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL,@object
	.section	.tdata._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL,"awT",@progbits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	2, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL:
	.ascii	"c\000\000\000\000\000\000\000\001"
	.zero	3
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL, 12

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,@object
	.section	.tbss._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,"awT",@nobits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	2, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	3
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL, 12

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,@object
	.section	.tdata._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,"awT",@progbits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	2, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.asciz	"*\000\000\000\000\000\000"
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL, 8

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,@object
	.section	.tbss._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,"awT",@nobits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	2, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	3
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL, 12

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.7,@object
	.section	.rodata..Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.7,"a",@progbits
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.7:
	.ascii	"failed to write whole buffer"
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.7, 28

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.8,@object
	.section	.data.rel.ro..Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.8,"aw",@progbits
	.p2align	2, 0x0
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.8:
	.long	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.7
	.ascii	"\034\000\000\000\027"
	.zero	3
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.8, 12

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.9,@object
	.section	.data.rel.ro..Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.9,"aw",@progbits
	.p2align	2, 0x0
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.9:
	.byte	2
	.zero	3
	.long	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.8
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.9, 8

	.type	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.10,@object
	.section	.data.rel.ro..Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.10,"aw",@progbits
	.p2align	2, 0x0
.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.10:
	.long	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.5
	.asciz	"\202\000\000\000\334\000\000\000$\000\000"
	.size	.Lanon.2b9c8d9649c33311ac3d5fb6f92fb9a8.10, 16

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
