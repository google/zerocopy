	.att_syntax
	.file	"tls_probe.d6bd21401e7e8eac-cgu.0"
	.section	.text.unlikely._RINvMs0_NtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_,"ax",@progbits
	.prefalign	4, .Lfunc_end0, nop
	.type	_RINvMs0_NtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_,@function
_RINvMs0_NtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	subq	$32, %rsp
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -16
	movzbl	8(%rdi), %eax
	testl	%eax, %eax
	je	.LBB0_5
	cmpl	$1, %eax
	je	.LBB0_12
	xorl	%edi, %edi
	jmp	.LBB0_12
.LBB0_5:
	testq	%rsi, %rsi
	je	.LBB0_6
	movl	(%rsi), %ecx
	movq	8(%rsi), %rax
	movq	$0, (%rsi)
	cmpl	$1, %ecx
	jne	.LBB0_6
	movq	%rax, (%rdi)
	movb	$1, 8(%rdi)
	jmp	.LBB0_8
.LBB0_6:
	movq	$13, 16(%rsp)
	leaq	16(%rsp), %rax
	#APP
	#NO_APP
	movq	16(%rsp), %rcx
	movzbl	8(%rdi), %eax
	movq	(%rdi), %rdx
	movq	%rdx, 24(%rsp)
	movq	%rcx, (%rdi)
	movb	$1, 8(%rdi)
	cmpl	$1, %eax
	jne	.LBB0_7
	movq	%rdi, %rbx
	leaq	24(%rsp), %rdi
	callq	*_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop@GOTPCREL(%rip)
	jmp	.LBB0_11
.LBB0_7:
	testl	%eax, %eax
	jne	.LBB0_9
.LBB0_8:
	leaq	_RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazy7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_(%rip), %rsi
	movq	%rdi, %rbx
	callq	*_RNvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local11destructors10linux_like8register@GOTPCREL(%rip)
.LBB0_11:
	movq	%rbx, %rdi
.LBB0_12:
	movq	%rdi, %rax
	addq	$32, %rsp
	.cfi_def_cfa_offset 16
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.LBB0_9:
	.cfi_def_cfa_offset 48
	leaq	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.0(%rip), %rsi
	leaq	15(%rsp), %rdi
	movl	$87, %edx
	callq	_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	movq	%rax, 16(%rsp)
	leaq	16(%rsp), %rdi
	callq	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	callq	*_RNvNtCs8ZKwes1zzDd_3std7process5abort@GOTPCREL(%rip)
.Lfunc_end0:
	.size	_RINvMs0_NtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_, .Lfunc_end0-_RINvMs0_NtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	.cfi_endproc

	.section	.text._RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end1, nop
	.type	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe,@function
_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	movq	(%rdi), %rax
	testq	%rax, %rax
	je	.LBB1_4
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB1_4
	testq	%rcx, %rcx
	je	.LBB1_4
	subq	$24, %rsp
	.cfi_def_cfa_offset 32
	decq	%rax
	leaq	16(%rsp), %rdi
	movq	%rax, 16(%rsp)
	movb	$3, 8(%rsp)
	callq	*_RNvXsd_NtNtCskADBYZwJmSU_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@GOTPCREL(%rip)
	addq	$24, %rsp
	.cfi_def_cfa_offset 8
.LBB1_4:
	retq
.Lfunc_end1:
	.size	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe, .Lfunc_end1-_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end2, nop
	.type	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe,@function
_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	movq	8(%rdi), %rax
	testq	%rax, %rax
	je	.LBB2_4
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB2_4
	testq	%rcx, %rcx
	je	.LBB2_4
	subq	$24, %rsp
	.cfi_def_cfa_offset 32
	decq	%rax
	leaq	16(%rsp), %rdi
	movq	%rax, 16(%rsp)
	movb	$3, 8(%rsp)
	callq	*_RNvXsd_NtNtCskADBYZwJmSU_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@GOTPCREL(%rip)
	addq	$24, %rsp
	.cfi_def_cfa_offset 8
.LBB2_4:
	retq
.Lfunc_end2:
	.size	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe, .Lfunc_end2-_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end3, nop
	.type	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe,@function
_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	movq	(%rdi), %rax
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB3_3
	testq	%rcx, %rcx
	je	.LBB3_3
	subq	$24, %rsp
	.cfi_def_cfa_offset 32
	decq	%rax
	leaq	16(%rsp), %rdi
	movq	%rax, 16(%rsp)
	movb	$3, 8(%rsp)
	callq	*_RNvXsd_NtNtCskADBYZwJmSU_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@GOTPCREL(%rip)
	addq	$24, %rsp
	.cfi_def_cfa_offset 8
.LBB3_3:
	retq
.Lfunc_end3:
	.size	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe, .Lfunc_end3-_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazy7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_,"ax",@progbits
	.prefalign	4, .Lfunc_end4, nop
	.type	_RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazy7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_,@function
_RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazy7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_:
	.cfi_startproc
	movzbl	8(%rdi), %eax
	movb	$2, 8(%rdi)
	cmpb	$1, %al
	jne	.LBB4_1
	jmpq	*_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop@GOTPCREL(%rip)
.LBB4_1:
	retq
.Lfunc_end4:
	.size	_RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazy7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_, .Lfunc_end4-_RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazy7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_
	.cfi_endproc

	.section	.text._RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native5eager7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_,"ax",@progbits
	.prefalign	4, .Lfunc_end5, nop
	.type	_RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native5eager7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_,@function
_RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native5eager7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_:
	.cfi_startproc
	movb	$2, 8(%rdi)
	jmpq	*_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop@GOTPCREL(%rip)
.Lfunc_end5:
	.size	_RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native5eager7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_, .Lfunc_end5-_RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native5eager7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_
	.cfi_endproc

	.section	.text._RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop,"ax",@progbits
	.globl	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop
	.prefalign	4, .Lfunc_end6, nop
	.type	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop,@function
_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop:
	.cfi_startproc
	movq	(%rdi), %rax
	movq	%rax, -8(%rsp)
	leaq	-8(%rsp), %rax
	#APP
	#NO_APP
	retq
.Lfunc_end6:
	.size	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop, .Lfunc_end6-_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCskADBYZwJmSU_4core3ops4drop4Drop4drop
	.cfi_endproc

	.section	.text._RNvXNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end7, nop
	.type	_RNvXNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,@function
_RNvXNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception0
	pushq	%r14
	.cfi_def_cfa_offset 16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	subq	$24, %rsp
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -24
	.cfi_offset %r14, -16
	movq	%rdi, %rbx
	movq	(%rdi), %rdi
	callq	_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	movq	%rax, %r14
	testq	%rax, %rax
	je	.LBB7_6
	movq	8(%rbx), %rax
	testq	%rax, %rax
	je	.LBB7_5
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB7_5
	testq	%rcx, %rcx
	je	.LBB7_5
	decq	%rax
	leaq	16(%rsp), %rdi
	movq	%rax, 16(%rsp)
	movb	$3, 8(%rsp)
.Ltmp0:
	callq	*_RNvXsd_NtNtCskADBYZwJmSU_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@GOTPCREL(%rip)
.Ltmp1:
.LBB7_5:
	movq	%r14, 8(%rbx)
.LBB7_6:
	testq	%r14, %r14
	setne	%al
	addq	$24, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	retq
.LBB7_7:
	.cfi_def_cfa_offset 48
.Ltmp2:
	movq	%r14, 8(%rbx)
	movq	%rax, %rdi
	callq	_Unwind_Resume@PLT
.Lfunc_end7:
	.size	_RNvXNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe, .Lfunc_end7-_RNvXNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.gcc_except_table._RNvXNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table7:
.Lexception0:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end0-.Lcst_begin0
.Lcst_begin0:
	.uleb128 .Lfunc_begin0-.Lfunc_begin0
	.uleb128 .Ltmp0-.Lfunc_begin0
	.byte	0
	.byte	0
	.uleb128 .Ltmp0-.Lfunc_begin0
	.uleb128 .Ltmp1-.Ltmp0
	.uleb128 .Ltmp2-.Lfunc_begin0
	.byte	0
	.uleb128 .Ltmp1-.Lfunc_begin0
	.uleb128 .Lfunc_end7-.Ltmp1
	.byte	0
	.byte	0
.Lcst_end0:
	.p2align	2, 0x0

	.section	.text._RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end8, nop
	.type	_RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,@function
_RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin1:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception1
	pushq	%r14
	.cfi_def_cfa_offset 16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	subq	$24, %rsp
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -24
	.cfi_offset %r14, -16
	movq	%rdi, %rbx
	movl	$0, 4(%rsp)
	cmpl	$128, %esi
	jae	.LBB8_1
	movb	%sil, 4(%rsp)
	movl	$1, %edx
	jmp	.LBB8_6
.LBB8_1:
	movl	%esi, %eax
	andb	$63, %al
	orb	$-128, %al
	movl	%esi, %ecx
	shrl	$6, %ecx
	cmpl	$2048, %esi
	jae	.LBB8_3
	orb	$-64, %cl
	movb	%cl, 4(%rsp)
	movb	%al, 5(%rsp)
	movl	$2, %edx
	jmp	.LBB8_6
.LBB8_3:
	andb	$63, %cl
	orb	$-128, %cl
	movl	%esi, %edx
	shrl	$12, %edx
	cmpl	$65535, %esi
	ja	.LBB8_5
	orb	$-32, %dl
	movb	%dl, 4(%rsp)
	movb	%cl, 5(%rsp)
	movb	%al, 6(%rsp)
	movl	$3, %edx
	jmp	.LBB8_6
.LBB8_5:
	andb	$63, %dl
	orb	$-128, %dl
	shrl	$18, %esi
	orb	$-16, %sil
	movb	%sil, 4(%rsp)
	movb	%dl, 5(%rsp)
	movb	%cl, 6(%rsp)
	movb	%al, 7(%rsp)
	movl	$4, %edx
.LBB8_6:
	movq	(%rbx), %rdi
	leaq	4(%rsp), %rsi
	callq	_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	movq	%rax, %r14
	testq	%rax, %rax
	je	.LBB8_12
	movq	8(%rbx), %rax
	testq	%rax, %rax
	je	.LBB8_11
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB8_11
	testq	%rcx, %rcx
	je	.LBB8_11
	decq	%rax
	leaq	16(%rsp), %rdi
	movq	%rax, 16(%rsp)
	movb	$3, 8(%rsp)
.Ltmp3:
	callq	*_RNvXsd_NtNtCskADBYZwJmSU_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@GOTPCREL(%rip)
.Ltmp4:
.LBB8_11:
	movq	%r14, 8(%rbx)
.LBB8_12:
	testq	%r14, %r14
	setne	%al
	addq	$24, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	retq
.LBB8_14:
	.cfi_def_cfa_offset 48
.Ltmp5:
	movq	%r14, 8(%rbx)
	movq	%rax, %rdi
	callq	_Unwind_Resume@PLT
.Lfunc_end8:
	.size	_RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe, .Lfunc_end8-_RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.gcc_except_table._RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table8:
.Lexception1:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end1-.Lcst_begin1
.Lcst_begin1:
	.uleb128 .Lfunc_begin1-.Lfunc_begin1
	.uleb128 .Ltmp3-.Lfunc_begin1
	.byte	0
	.byte	0
	.uleb128 .Ltmp3-.Lfunc_begin1
	.uleb128 .Ltmp4-.Ltmp3
	.uleb128 .Ltmp5-.Lfunc_begin1
	.byte	0
	.uleb128 .Ltmp4-.Lfunc_begin1
	.uleb128 .Lfunc_end8-.Ltmp4
	.byte	0
	.byte	0
.Lcst_end1:
	.p2align	2, 0x0

	.section	.text._RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end9, nop
	.type	_RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,@function
_RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	movq	%rdx, %rcx
	movq	%rsi, %rdx
	leaq	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.3(%rip), %rsi
	jmpq	*_RNvNtCskADBYZwJmSU_4core3fmt5write@GOTPCREL(%rip)
.Lfunc_end9:
	.size	_RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe, .Lfunc_end9-_RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end10, nop
	.type	_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,@function
_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin2:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception2
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$40, %rsp
	.cfi_def_cfa_offset 96
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	testq	%rdx, %rdx
	je	.LBB10_1
	movq	%rdx, %rbx
	movq	%rsi, %r14
	movq	%rdi, %r12
	movq	_RNvXs3_NtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unixNtB5_6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write5write@GOTPCREL(%rip), %r15
	leaq	.LJTI10_0(%rip), %r13
	jmp	.LBB10_4
.LBB10_11:
	movq	%rbp, %rax
	shrq	$32, %rax
	movabsq	$188978561024, %rcx
	cmpq	%rcx, %rbp
	movl	$255, %ecx
	cmovael	%ecx, %eax
	cmpb	$35, %al
	jne	.LBB10_2
	.p2align	4
.LBB10_18:
	testq	%rbx, %rbx
	je	.LBB10_1
.LBB10_4:
	movq	%r12, %rdi
	movq	%r14, %rsi
	movq	%rbx, %rdx
	callq	*%r15
	movq	%rdx, %rbp
	movq	%rax, 8(%rsp)
	movq	%rdx, 16(%rsp)
	cmpq	$1, %rax
	jne	.LBB10_9
	movl	%ebp, %eax
	andl	$3, %eax
	movslq	(%r13,%rax,4), %rax
	addq	%r13, %rax
	jmpq	*%rax
.LBB10_15:
	cmpb	$35, 16(%rbp)
	je	.LBB10_18
	jmp	.LBB10_2
	.p2align	4
.LBB10_9:
	testq	%rbp, %rbp
	je	.LBB10_10
	movq	%rbx, %rax
	subq	%rbp, %rax
	jb	.LBB10_12
	addq	%rbp, %r14
	movq	%rax, %rbx
	jmp	.LBB10_18
.LBB10_6:
.Ltmp6:
	callq	*_RNvNtNtNtCskADBYZwJmSU_4core2io5error12os_functions16get_os_functions@GOTPCREL(%rip)
.Ltmp7:
	movq	%rbp, %rdi
	shrq	$32, %rdi
.Ltmp8:
	callq	*16(%rax)
.Ltmp9:
	testb	%al, %al
	jne	.LBB10_18
	jmp	.LBB10_2
.LBB10_16:
	cmpb	$35, 31(%rbp)
	jne	.LBB10_2
	decq	%rbp
	movq	%rbp, 32(%rsp)
	movb	$3, 24(%rsp)
	leaq	32(%rsp), %rdi
	callq	*_RNvXsd_NtNtCskADBYZwJmSU_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@GOTPCREL(%rip)
	jmp	.LBB10_18
.LBB10_1:
	xorl	%ebp, %ebp
.LBB10_2:
	movq	%rbp, %rax
	addq	$40, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.LBB10_10:
	.cfi_def_cfa_offset 96
	leaq	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.8(%rip), %rbp
	jmp	.LBB10_2
.LBB10_12:
	leaq	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.9(%rip), %rcx
	movq	%rbp, %rdi
	movq	%rbx, %rsi
	movq	%rbx, %rdx
	callq	*_RNvNtNtCskADBYZwJmSU_4core5slice5index16slice_index_fail@GOTPCREL(%rip)
.LBB10_19:
.Ltmp10:
	movq	%rax, %rbx
.Ltmp11:
	leaq	16(%rsp), %rdi
	callq	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
.Ltmp12:
	movq	%rbx, %rdi
	callq	_Unwind_Resume@PLT
.LBB10_21:
.Ltmp13:
	callq	*_RNvNtCskADBYZwJmSU_4core9panicking16panic_in_cleanup@GOTPCREL(%rip)
.Lfunc_end10:
	.size	_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe, .Lfunc_end10-_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.rodata._RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
.LJTI10_0:
	.long	.LBB10_15-.LJTI10_0
	.long	.LBB10_16-.LJTI10_0
	.long	.LBB10_6-.LJTI10_0
	.long	.LBB10_11-.LJTI10_0
	.section	.gcc_except_table._RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table10:
.Lexception2:
	.byte	255
	.byte	155
	.uleb128 .Lttbase0-.Lttbaseref0
.Lttbaseref0:
	.byte	1
	.uleb128 .Lcst_end2-.Lcst_begin2
.Lcst_begin2:
	.uleb128 .Lfunc_begin2-.Lfunc_begin2
	.uleb128 .Ltmp6-.Lfunc_begin2
	.byte	0
	.byte	0
	.uleb128 .Ltmp6-.Lfunc_begin2
	.uleb128 .Ltmp9-.Ltmp6
	.uleb128 .Ltmp10-.Lfunc_begin2
	.byte	0
	.uleb128 .Ltmp9-.Lfunc_begin2
	.uleb128 .Ltmp11-.Ltmp9
	.byte	0
	.byte	0
	.uleb128 .Ltmp11-.Lfunc_begin2
	.uleb128 .Ltmp12-.Ltmp11
	.uleb128 .Ltmp13-.Lfunc_begin2
	.byte	1
	.uleb128 .Ltmp12-.Lfunc_begin2
	.uleb128 .Lfunc_end10-.Ltmp12
	.byte	0
	.byte	0
.Lcst_end2:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase0:
	.byte	0
	.p2align	2, 0x0

	.section	.text._RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.prefalign	4, .Lfunc_end11, nop
	.type	_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,@function
_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin3:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception3
	pushq	%rbx
	.cfi_def_cfa_offset 16
	subq	$32, %rsp
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -16
	movq	%rdx, %rcx
	movq	%rsi, %rdx
	movq	%rdi, (%rsp)
	movq	$0, 8(%rsp)
.Ltmp14:
	leaq	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.3(%rip), %rsi
	movq	%rsp, %rdi
	callq	*_RNvNtCskADBYZwJmSU_4core3fmt5write@GOTPCREL(%rip)
.Ltmp15:
	testb	%al, %al
	je	.LBB11_5
	movq	8(%rsp), %rax
	testq	%rax, %rax
	jne	.LBB11_10
.Ltmp16:
	leaq	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.4(%rip), %rdi
	leaq	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.6(%rip), %rdx
	movl	$173, %esi
	callq	*_RNvNtCskADBYZwJmSU_4core9panicking9panic_fmt@GOTPCREL(%rip)
.Ltmp17:
	ud2
.LBB11_5:
	movq	8(%rsp), %rax
	testq	%rax, %rax
	je	.LBB11_9
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB11_9
	testq	%rcx, %rcx
	je	.LBB11_9
	decq	%rax
	leaq	24(%rsp), %rdi
	movq	%rax, 24(%rsp)
	movb	$3, 16(%rsp)
	callq	*_RNvXsd_NtNtCskADBYZwJmSU_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop@GOTPCREL(%rip)
.LBB11_9:
	xorl	%eax, %eax
.LBB11_10:
	addq	$32, %rsp
	.cfi_def_cfa_offset 16
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.LBB11_12:
	.cfi_def_cfa_offset 48
.Ltmp18:
	movq	%rax, %rbx
.Ltmp19:
	movq	%rsp, %rdi
	callq	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe
.Ltmp20:
	movq	%rbx, %rdi
	callq	_Unwind_Resume@PLT
.LBB11_11:
.Ltmp21:
	callq	*_RNvNtCskADBYZwJmSU_4core9panicking16panic_in_cleanup@GOTPCREL(%rip)
.Lfunc_end11:
	.size	_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe, .Lfunc_end11-_RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.gcc_except_table._RNvYNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrNtNtNtCskADBYZwJmSU_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table11:
.Lexception3:
	.byte	255
	.byte	155
	.uleb128 .Lttbase1-.Lttbaseref1
.Lttbaseref1:
	.byte	1
	.uleb128 .Lcst_end3-.Lcst_begin3
.Lcst_begin3:
	.uleb128 .Ltmp14-.Lfunc_begin3
	.uleb128 .Ltmp17-.Ltmp14
	.uleb128 .Ltmp18-.Lfunc_begin3
	.byte	0
	.uleb128 .Ltmp17-.Lfunc_begin3
	.uleb128 .Ltmp19-.Ltmp17
	.byte	0
	.byte	0
	.uleb128 .Ltmp19-.Lfunc_begin3
	.uleb128 .Ltmp20-.Ltmp19
	.uleb128 .Ltmp21-.Lfunc_begin3
	.byte	1
	.uleb128 .Ltmp20-.Lfunc_begin3
	.uleb128 .Lfunc_end11-.Ltmp20
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
	.prefalign	4, .Lfunc_end12, nop
	.type	access_all_tls,@function
access_all_tls:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r13
	.cfi_def_cfa_offset 32
	pushq	%r12
	.cfi_def_cfa_offset 40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	subq	$16, %rsp
	.cfi_def_cfa_offset 64
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r13, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@GOTTPOFF(%rip), %rax
	movq	%fs:(%rax), %r14
	incq	%r14
	movq	%r14, %fs:(%rax)
	movq	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64@GOTTPOFF(%rip), %rax
	movq	%fs:(%rax), %rbx
	movq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL@GOTTPOFF(%rip), %rax
	movq	%fs:(%rax), %rax
	movq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@GOTTPOFF(%rip), %r15
	movzbl	%fs:8(%r15), %ecx
	testl	%ecx, %ecx
	jne	.LBB12_1
.LBB12_3:
	movq	%fs:(%r15), %r15
	movq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@GOTTPOFF(%rip), %rcx
	cmpb	$1, %fs:8(%rcx)
	jne	.LBB12_5
	movq	%fs:(%rcx), %r12
.LBB12_6:
	movq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@GOTTPOFF(%rip), %rcx
	cmpb	$1, %fs:8(%rcx)
	jne	.LBB12_8
	addq	%fs:0, %rcx
.LBB12_9:
	addq	%r14, %rbx
	addq	%r15, %rax
	addq	%r12, %rax
	addq	%rbx, %rax
	addq	(%rcx), %rax
	addq	$16, %rsp
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.LBB12_5:
	.cfi_def_cfa_offset 64
	movq	$7, 8(%rsp)
	leaq	8(%rsp), %rdx
	#APP
	#NO_APP
	movq	8(%rsp), %r12
	movq	%r12, %fs:(%rcx)
	movb	$1, %fs:8(%rcx)
	jmp	.LBB12_6
.LBB12_8:
	movq	%fs:0, %rdi
	addq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@GOTTPOFF(%rip), %rdi
	xorl	%esi, %esi
	movq	%rax, %r13
	callq	_RINvMs0_NtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	movq	%rax, %rcx
	movq	%r13, %rax
	testq	%rcx, %rcx
	jne	.LBB12_9
	jmp	.LBB12_10
.LBB12_1:
	cmpl	$1, %ecx
	jne	.LBB12_10
	movq	%fs:0, %rdi
	addq	%r15, %rdi
	leaq	_RINvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local6native5eager7destroyINtNtCskADBYZwJmSU_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_(%rip), %rsi
	movq	%rax, %r12
	callq	*_RNvNtNtNtNtCs8ZKwes1zzDd_3std3sys12thread_local11destructors10linux_like8register@GOTPCREL(%rip)
	movq	%r12, %rax
	movb	$0, %fs:8(%r15)
	jmp	.LBB12_3
.LBB12_10:
	leaq	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.2(%rip), %rdi
	callq	*_RNvNtNtCs8ZKwes1zzDd_3std6thread5local18panic_access_error@GOTPCREL(%rip)
.Lfunc_end12:
	.size	access_all_tls, .Lfunc_end12-access_all_tls
	.cfi_endproc

	.type	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.0,@object
	.section	.rodata..Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.0,"a",@progbits
.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.0:
	.ascii	"fatal runtime error: unreachable, aborting\n"
	.size	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.0, 43

	.type	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.1,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.1:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/std/src/thread/local.rs"
	.size	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.1, 134

	.type	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.2,@object
	.section	.data.rel.ro..Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.2,"aw",@progbits
	.p2align	3, 0x0
.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.2:
	.quad	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.1
	.asciz	"\205\000\000\000\000\000\000\000\255\001\000\000\031\000\000"
	.size	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.2, 24

	.type	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.3,@object
	.section	.data.rel.ro..Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.3,"aw",@progbits
	.p2align	3, 0x0
.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.3:
	.quad	_RINvNtCskADBYZwJmSU_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe
	.asciz	"\020\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	_RNvXNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.quad	_RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.quad	_RNvYINtNvNtNtCskADBYZwJmSU_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs8ZKwes1zzDd_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.size	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.3, 48

	.type	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.4,@object
	.section	.rodata..Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.4,"a",@progbits
.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.4:
	.ascii	"a formatting trait implementation returned an error when the underlying stream did not"
	.size	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.4, 86

	.type	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.5,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.5:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/io/write.rs"
	.size	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.5, 131

	.type	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.6,@object
	.section	.data.rel.ro..Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.6,"aw",@progbits
	.p2align	3, 0x0
.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.6:
	.quad	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.5
	.asciz	"\202\000\000\000\000\000\000\000\233\001\000\000\021\000\000"
	.size	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.6, 24

	.type	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,@object
	.section	.tdata._RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,"awT",@progbits
	.globl	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	.p2align	3, 0x0
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
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL:
	.ascii	"c\000\000\000\000\000\000\000\001"
	.zero	7
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL, 16

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,@object
	.section	.tbss._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,"awT",@nobits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	7
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL, 16

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,@object
	.section	.tdata._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,"awT",@progbits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.asciz	"*\000\000\000\000\000\000"
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL, 8

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,@object
	.section	.tbss._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,"awT",@nobits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	7
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL, 16

	.type	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.7,@object
	.section	.rodata..Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.7,"a",@progbits
.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.7:
	.ascii	"failed to write whole buffer"
	.size	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.7, 28

	.type	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.8,@object
	.section	.data.rel.ro..Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.8,"aw",@progbits
	.p2align	3, 0x0
.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.8:
	.quad	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.7
	.ascii	"\034\000\000\000\000\000\000\000\027"
	.zero	7
	.size	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.8, 24

	.type	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.9,@object
	.section	.data.rel.ro..Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.9,"aw",@progbits
	.p2align	3, 0x0
.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.9:
	.quad	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.5
	.asciz	"\202\000\000\000\000\000\000\000\334\000\000\000$\000\000"
	.size	.Lanon.1965fbeec84ec9549d7d69c3a38f3fdd.9, 24

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
