# without_no_builtins (x86_64-unknown-linux-gnu) - set_bytes_helper + memset
	.cfi_startproc
	leaq	(%rdi,%rdx), %rax
	cmpq	%rax, %rdi
	jae	.LBB0_1
	movzbl	%sil, %esi
	jmpq	*memset@GOTPCREL(%rip)
.LBB0_1:
	retq
.Lfunc_end0:
	.size	_RNvCsfuJ9zV4K5ME_26memcpy_without_no_builtins16set_bytes_helper, .Lfunc_end0-_RNvCsfuJ9zV4K5ME_26memcpy_without_no_builtins16set_bytes_helper
	.cfi_endproc

	.section	.text._RNvCsfuJ9zV4K5ME_26memcpy_without_no_builtins19copy_forward_helper,"ax",@progbits
	.p2align	4
	.type	_RNvCsfuJ9zV4K5ME_26memcpy_without_no_builtins19copy_forward_helper,@function
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdi, %rbx
	callq	_RNvCsfuJ9zV4K5ME_26memcpy_without_no_builtins16set_bytes_helper
	movq	%rbx, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end3:
	.size	memset, .Lfunc_end3-memset
	.cfi_endproc

	.ident	"rustc version 1.98.0-nightly (14210df0e 2026-05-31)"
# without_no_builtins (x86_64-unknown-linux-gnu) - copy_forward_helper + memcpy
	.cfi_startproc
	movq	%rdi, %rax
	subq	%rsi, %rax
	cmpq	$32, %rax
	jae	.LBB1_1
	xorl	%eax, %eax
	.p2align	4
.LBB1_5:
	movzbl	(%rsi,%rax), %ecx
	movb	%cl, (%rdi,%rax)
	movzbl	1(%rsi,%rax), %ecx
	movb	%cl, 1(%rdi,%rax)
	movzbl	2(%rsi,%rax), %ecx
	movb	%cl, 2(%rdi,%rax)
	movzbl	3(%rsi,%rax), %ecx
	movb	%cl, 3(%rdi,%rax)
	addq	$4, %rax
	cmpq	$4096, %rax
	jne	.LBB1_5
	jmp	.LBB1_3
.LBB1_1:
	xorl	%eax, %eax
	.p2align	4
.LBB1_2:
	movups	(%rsi,%rax), %xmm0
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdi, %rbx
	callq	_RNvCsfuJ9zV4K5ME_26memcpy_without_no_builtins19copy_forward_helper
	movq	%rbx, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end2:
	.size	memcpy, .Lfunc_end2-memcpy
	.cfi_endproc

	.section	.text.memset,"ax",@progbits

# with_no_builtins (x86_64-unknown-linux-gnu) - set_bytes_helper + memset
	.cfi_startproc
	leaq	(%rdi,%rdx), %rax
	cmpq	%rax, %rdi
	jae	.LBB0_7
	cmpq	$4, %rdx
	jae	.LBB0_2
.LBB0_13:
	movq	%rdi, %r9
	jmp	.LBB0_14
.LBB0_2:
	movzbl	%sil, %r8d
	cmpq	$32, %rdx
	jae	.LBB0_8
	xorl	%ecx, %ecx
	jmp	.LBB0_4
.LBB0_8:
	movq	%rdx, %rcx
	andq	$-32, %rcx
	movd	%r8d, %xmm0
	punpcklbw	%xmm0, %xmm0
	pshuflw	$0, %xmm0, %xmm0
	pshufd	$68, %xmm0, %xmm0
	xorl	%r9d, %r9d
	.p2align	4
.LBB0_9:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdi, %rbx
	callq	_RNvCs4ipYLFA0IKs_23memcpy_with_no_builtins16set_bytes_helper
	movq	%rbx, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end3:
	.size	memset, .Lfunc_end3-memset
	.cfi_endproc

	.ident	"rustc version 1.98.0-nightly (14210df0e 2026-05-31)"
# with_no_builtins (x86_64-unknown-linux-gnu) - copy_forward_helper + memcpy
	.cfi_startproc
	movq	%rdi, %rax
	subq	%rsi, %rax
	cmpq	$32, %rax
	jae	.LBB1_1
	xorl	%eax, %eax
	.p2align	4
.LBB1_5:
	movzbl	(%rsi,%rax), %ecx
	movb	%cl, (%rdi,%rax)
	movzbl	1(%rsi,%rax), %ecx
	movb	%cl, 1(%rdi,%rax)
	movzbl	2(%rsi,%rax), %ecx
	movb	%cl, 2(%rdi,%rax)
	movzbl	3(%rsi,%rax), %ecx
	movb	%cl, 3(%rdi,%rax)
	addq	$4, %rax
	cmpq	$4096, %rax
	jne	.LBB1_5
	jmp	.LBB1_3
.LBB1_1:
	xorl	%eax, %eax
	.p2align	4
.LBB1_2:
	movups	(%rsi,%rax), %xmm0
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdi, %rbx
	callq	_RNvCs4ipYLFA0IKs_23memcpy_with_no_builtins19copy_forward_helper
	movq	%rbx, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end2:
	.size	memcpy, .Lfunc_end2-memcpy
	.cfi_endproc

	.section	.text.memset,"ax",@progbits

