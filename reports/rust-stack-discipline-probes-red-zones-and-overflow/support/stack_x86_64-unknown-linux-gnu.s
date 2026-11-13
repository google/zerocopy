	.att_syntax
	.file	"stack_probe.3f9c3f566e408f32-cgu.0"
	.section	.text.frame_3k,"ax",@progbits
	.globl	frame_3k
	.prefalign	4, .Lfunc_end0, nop
	.type	frame_3k,@function
frame_3k:
.Lfunc_begin0:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	subq	$3088, %rsp
	.cfi_def_cfa_offset 3104
	.cfi_offset %rbx, -16
	movl	%edi, %esi
	leaq	16(%rsp), %rbx
	movl	$3072, %edx
	movq	%rbx, %rdi
	callq	*memset@GOTPCREL(%rip)
	movq	%rbx, 8(%rsp)
	leaq	8(%rsp), %rax
	#APP
	#NO_APP
	movzbl	1040(%rsp), %eax
	addq	$3088, %rsp
	.cfi_def_cfa_offset 16
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end0:
	.size	frame_3k, .Lfunc_end0-frame_3k
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.frame_3k
	.quad	.Lfunc_begin0
	.ascii	"\230\030"
	.section	.text.frame_3k,"ax",@progbits

	.section	.text.frame_70k,"ax",@progbits
	.globl	frame_70k
	.prefalign	4, .Lfunc_end1, nop
	.type	frame_70k,@function
frame_70k:
.Lfunc_begin1:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	movq	%rsp, %r11
	subq	$69632, %r11
	.cfi_def_cfa_register %r11
	.cfi_adjust_cfa_offset 69632
.LBB1_1:
	subq	$4096, %rsp
	movq	$0, (%rsp)
	cmpq	%r11, %rsp
	jne	.LBB1_1
	subq	$2064, %rsp
	.cfi_def_cfa_register %rsp
	.cfi_def_cfa_offset 71712
	.cfi_offset %rbx, -16
	movl	%edi, %esi
	leaq	16(%rsp), %rbx
	movl	$71680, %edx
	movq	%rbx, %rdi
	callq	*memset@GOTPCREL(%rip)
	movq	%rbx, 8(%rsp)
	leaq	8(%rsp), %rax
	#APP
	#NO_APP
	movzbl	65552(%rsp), %eax
	addq	$71696, %rsp
	.cfi_def_cfa_offset 16
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end1:
	.size	frame_70k, .Lfunc_end1-frame_70k
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.frame_70k
	.quad	.Lfunc_begin1
	.ascii	"\230\260\004"
	.section	.text.frame_70k,"ax",@progbits

	.section	.text.frame_8k,"ax",@progbits
	.globl	frame_8k
	.prefalign	4, .Lfunc_end2, nop
	.type	frame_8k,@function
frame_8k:
.Lfunc_begin2:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$16, %rsp
	.cfi_def_cfa_offset 8224
	.cfi_offset %rbx, -16
	movl	%edi, %esi
	leaq	16(%rsp), %rbx
	movl	$8192, %edx
	movq	%rbx, %rdi
	callq	*memset@GOTPCREL(%rip)
	movq	%rbx, 8(%rsp)
	leaq	8(%rsp), %rax
	#APP
	#NO_APP
	movzbl	4112(%rsp), %eax
	addq	$8208, %rsp
	.cfi_def_cfa_offset 16
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end2:
	.size	frame_8k, .Lfunc_end2-frame_8k
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.frame_8k
	.quad	.Lfunc_begin2
	.ascii	"\230@"
	.section	.text.frame_8k,"ax",@progbits

	.section	.text.overaligned_frame,"ax",@progbits
	.globl	overaligned_frame
	.prefalign	4, .Lfunc_end3, nop
	.type	overaligned_frame,@function
overaligned_frame:
.Lfunc_begin3:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	andq	$-64, %rsp
	subq	$128, %rsp
	movd	%edi, %xmm0
	punpcklbw	%xmm0, %xmm0
	pshuflw	$0, %xmm0, %xmm0
	pshufd	$68, %xmm0, %xmm0
	movdqa	%xmm0, 48(%rsp)
	movdqa	%xmm0, 32(%rsp)
	movdqa	%xmm0, 16(%rsp)
	movdqa	%xmm0, (%rsp)
	movq	%rsp, %rdi
	callq	*%rsi
	movzbl	(%rsp), %eax
	movq	%rbp, %rsp
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end3:
	.size	overaligned_frame, .Lfunc_end3-overaligned_frame
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.overaligned_frame
	.quad	.Lfunc_begin3
	.byte	120
	.section	.text.overaligned_frame,"ax",@progbits

	.section	.text.redzone_leaf,"ax",@progbits
	.globl	redzone_leaf
	.prefalign	4, .Lfunc_end4, nop
	.type	redzone_leaf,@function
redzone_leaf:
.Lfunc_begin4:
	.cfi_startproc
	leaq	(%rcx,%rsi), %rax
	movq	%rdi, -64(%rsp)
	movq	%rsi, -56(%rsp)
	xorq	%rdi, %rsi
	movq	%rdx, -48(%rsp)
	movq	%rcx, -40(%rsp)
	xorq	%rdx, %rcx
	addq	%rdi, %rdx
	movq	%rsi, -32(%rsp)
	movq	%rcx, -24(%rsp)
	movq	%rdx, -16(%rsp)
	movq	%rax, -8(%rsp)
	leaq	-64(%rsp), %rax
	movq	%rax, -72(%rsp)
	leaq	-72(%rsp), %rax
	#APP
	#NO_APP
	movq	-8(%rsp), %rax
	addq	-64(%rsp), %rax
	retq
.Lfunc_end4:
	.size	redzone_leaf, .Lfunc_end4-redzone_leaf
	.cfi_endproc
	.section	.stack_sizes,"o",@progbits,.text.redzone_leaf
	.quad	.Lfunc_begin4
	.byte	0
	.section	.text.redzone_leaf,"ax",@progbits

	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
