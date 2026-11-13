	.att_syntax
	.file	"stack_probe.3f9c3f566e408f32-cgu.0"
	.section	.text.frame_3k,"ax",@progbits
	.globl	frame_3k
	.prefalign	4, .Lfunc_end0, nop
	.type	frame_3k,@function
frame_3k:
.Lfunc_begin0:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	pushl	%esi
	.cfi_def_cfa_offset 12
	subl	$3076, %esp
	.cfi_def_cfa_offset 3088
	.cfi_offset %esi, -12
	.cfi_offset %ebx, -8
	calll	.L0$pb
	.cfi_adjust_cfa_offset 4
.L0$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp0:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp0-.L0$pb), %ebx
	subl	$4, %esp
	.cfi_adjust_cfa_offset 4
	movl	3092(%esp), %eax
	leal	8(%esp), %esi
	pushl	$3072
	.cfi_adjust_cfa_offset 4
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	pushl	%esi
	.cfi_adjust_cfa_offset 4
	calll	memset@PLT
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
	movl	%esi, (%esp)
	movl	%esp, %eax
	#APP
	#NO_APP
	movzbl	1028(%esp), %eax
	addl	$3076, %esp
	.cfi_def_cfa_offset 12
	popl	%esi
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end0:
	.size	frame_3k, .Lfunc_end0-frame_3k
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.frame_3k
	.long	.Lfunc_begin0
	.ascii	"\214\030"
	.section	.text.frame_3k,"ax",@progbits

	.section	.text.frame_70k,"ax",@progbits
	.globl	frame_70k
	.prefalign	4, .Lfunc_end1, nop
	.type	frame_70k,@function
frame_70k:
.Lfunc_begin1:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	pushl	%esi
	.cfi_def_cfa_offset 12
	movl	%esp, %eax
	subl	$69632, %eax
	.cfi_def_cfa_register %eax
	.cfi_adjust_cfa_offset 69632
.LBB1_1:
	subl	$4096, %esp
	movl	$0, (%esp)
	cmpl	%eax, %esp
	jne	.LBB1_1
	subl	$2052, %esp
	.cfi_def_cfa_register %esp
	.cfi_def_cfa_offset 71696
	.cfi_offset %esi, -12
	.cfi_offset %ebx, -8
	calll	.L1$pb
	.cfi_adjust_cfa_offset 4
.L1$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp1:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp1-.L1$pb), %ebx
	subl	$4, %esp
	.cfi_adjust_cfa_offset 4
	movl	71700(%esp), %eax
	leal	8(%esp), %esi
	pushl	$71680
	.cfi_adjust_cfa_offset 4
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	pushl	%esi
	.cfi_adjust_cfa_offset 4
	calll	memset@PLT
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
	movl	%esi, (%esp)
	movl	%esp, %eax
	#APP
	#NO_APP
	movzbl	65540(%esp), %eax
	addl	$71684, %esp
	.cfi_def_cfa_offset 12
	popl	%esi
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end1:
	.size	frame_70k, .Lfunc_end1-frame_70k
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.frame_70k
	.long	.Lfunc_begin1
	.ascii	"\214\260\004"
	.section	.text.frame_70k,"ax",@progbits

	.section	.text.frame_8k,"ax",@progbits
	.globl	frame_8k
	.prefalign	4, .Lfunc_end2, nop
	.type	frame_8k,@function
frame_8k:
.Lfunc_begin2:
	.cfi_startproc
	pushl	%ebx
	.cfi_def_cfa_offset 8
	pushl	%esi
	.cfi_def_cfa_offset 12
	subl	$4096, %esp
	.cfi_adjust_cfa_offset 4096
	movl	$0, (%esp)
	subl	$4096, %esp
	.cfi_adjust_cfa_offset 4096
	movl	$0, (%esp)
	pushl	%eax
	.cfi_def_cfa_offset 8208
	.cfi_offset %esi, -12
	.cfi_offset %ebx, -8
	calll	.L2$pb
	.cfi_adjust_cfa_offset 4
.L2$pb:
	popl	%ebx
	.cfi_adjust_cfa_offset -4
.Ltmp2:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp2-.L2$pb), %ebx
	subl	$4, %esp
	.cfi_adjust_cfa_offset 4
	movl	8212(%esp), %eax
	leal	8(%esp), %esi
	pushl	$8192
	.cfi_adjust_cfa_offset 4
	pushl	%eax
	.cfi_adjust_cfa_offset 4
	pushl	%esi
	.cfi_adjust_cfa_offset 4
	calll	memset@PLT
	addl	$16, %esp
	.cfi_adjust_cfa_offset -16
	movl	%esi, (%esp)
	movl	%esp, %eax
	#APP
	#NO_APP
	movzbl	4100(%esp), %eax
	addl	$8196, %esp
	.cfi_def_cfa_offset 12
	popl	%esi
	.cfi_def_cfa_offset 8
	popl	%ebx
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end2:
	.size	frame_8k, .Lfunc_end2-frame_8k
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.frame_8k
	.long	.Lfunc_begin2
	.ascii	"\214@"
	.section	.text.frame_8k,"ax",@progbits

	.section	.text.overaligned_frame,"ax",@progbits
	.globl	overaligned_frame
	.prefalign	4, .Lfunc_end3, nop
	.type	overaligned_frame,@function
overaligned_frame:
.Lfunc_begin3:
	.cfi_startproc
	pushl	%ebp
	.cfi_def_cfa_offset 8
	.cfi_offset %ebp, -8
	movl	%esp, %ebp
	.cfi_def_cfa_register %ebp
	andl	$-64, %esp
	subl	$192, %esp
	movd	8(%ebp), %xmm0
	leal	64(%esp), %eax
	movl	%eax, (%esp)
	punpcklbw	%xmm0, %xmm0
	pshuflw	$0, %xmm0, %xmm0
	pshufd	$68, %xmm0, %xmm0
	movdqa	%xmm0, 112(%esp)
	movdqa	%xmm0, 96(%esp)
	movdqa	%xmm0, 80(%esp)
	movdqa	%xmm0, 64(%esp)
	calll	*12(%ebp)
	movzbl	64(%esp), %eax
	movl	%ebp, %esp
	popl	%ebp
	.cfi_def_cfa %esp, 4
	retl
.Lfunc_end3:
	.size	overaligned_frame, .Lfunc_end3-overaligned_frame
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.overaligned_frame
	.long	.Lfunc_begin3
	.ascii	"\274\001"
	.section	.text.overaligned_frame,"ax",@progbits

	.section	.text.redzone_leaf,"ax",@progbits
	.globl	redzone_leaf
	.prefalign	4, .Lfunc_end4, nop
	.type	redzone_leaf,@function
redzone_leaf:
.Lfunc_begin4:
	.cfi_startproc
	pushl	%ebp
	.cfi_def_cfa_offset 8
	pushl	%ebx
	.cfi_def_cfa_offset 12
	pushl	%edi
	.cfi_def_cfa_offset 16
	pushl	%esi
	.cfi_def_cfa_offset 20
	subl	$76, %esp
	.cfi_def_cfa_offset 96
	.cfi_offset %esi, -20
	.cfi_offset %edi, -16
	.cfi_offset %ebx, -12
	.cfi_offset %ebp, -8
	movl	104(%esp), %eax
	movl	100(%esp), %edi
	movl	108(%esp), %ebp
	movl	112(%esp), %esi
	movl	116(%esp), %edx
	movl	124(%esp), %ebx
	movl	120(%esp), %ecx
	xorl	96(%esp), %eax
	xorl	%edi, %ebp
	xorl	%edx, %ebx
	movl	%eax, (%esp)
	movl	%edi, %eax
	movl	120(%esp), %edi
	movl	%eax, 12(%esp)
	movl	96(%esp), %eax
	xorl	%esi, %edi
	movl	%eax, 8(%esp)
	movl	108(%esp), %eax
	movl	%eax, 20(%esp)
	movl	104(%esp), %eax
	movl	%eax, 16(%esp)
	movl	%esi, 24(%esp)
	addl	96(%esp), %esi
	movl	%edx, 28(%esp)
	movl	%ecx, 32(%esp)
	adcl	100(%esp), %edx
	addl	%eax, %ecx
	movl	124(%esp), %eax
	movl	%eax, 36(%esp)
	movl	%ebp, 44(%esp)
	movl	(%esp), %ebp
	adcl	108(%esp), %eax
	movl	%ebp, 40(%esp)
	movl	%ebx, 52(%esp)
	movl	%edi, 48(%esp)
	movl	%esi, 56(%esp)
	movl	%edx, 60(%esp)
	movl	%eax, 68(%esp)
	leal	8(%esp), %eax
	movl	%ecx, 64(%esp)
	movl	%eax, 4(%esp)
	leal	4(%esp), %eax
	#APP
	#NO_APP
	movl	64(%esp), %eax
	movl	68(%esp), %edx
	addl	8(%esp), %eax
	adcl	12(%esp), %edx
	addl	$76, %esp
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
.Lfunc_end4:
	.size	redzone_leaf, .Lfunc_end4-redzone_leaf
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.redzone_leaf
	.long	.Lfunc_begin4
	.byte	92
	.section	.text.redzone_leaf,"ax",@progbits

	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
