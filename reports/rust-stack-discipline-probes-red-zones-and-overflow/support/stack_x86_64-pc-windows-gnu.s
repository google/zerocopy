	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.att_syntax
	.file	"stack_probe.3f9c3f566e408f32-cgu.0"
	.def	frame_3k;
	.scl	2;
	.type	32;
	.endef
	.text
	.globl	frame_3k
	.p2align	4
frame_3k:
.Lfunc_begin0:
.seh_proc frame_3k
	pushq	%rsi
	.seh_pushreg %rsi
	subq	$3120, %rsp
	.seh_stackalloc 3120
	.seh_endprologue
	movl	%ecx, %edx
	leaq	48(%rsp), %rsi
	movl	$3072, %r8d
	movq	%rsi, %rcx
	callq	memset
	movq	%rsi, 40(%rsp)
	leaq	40(%rsp), %rax
	#APP
	#NO_APP
	movzbl	1072(%rsp), %eax
	.seh_startepilogue
	addq	$3120, %rsp
	popq	%rsi
	.seh_endepilogue
	retq
	.seh_endproc

	.def	frame_70k;
	.scl	2;
	.type	32;
	.endef
	.globl	frame_70k
	.p2align	4
frame_70k:
.Lfunc_begin1:
.seh_proc frame_70k
	pushq	%rsi
	.seh_pushreg %rsi
	movl	$71728, %eax
	callq	___chkstk_ms
	subq	%rax, %rsp
	.seh_stackalloc 71728
	.seh_endprologue
	movl	%ecx, %edx
	leaq	48(%rsp), %rsi
	movl	$71680, %r8d
	movq	%rsi, %rcx
	callq	memset
	movq	%rsi, 40(%rsp)
	leaq	40(%rsp), %rax
	#APP
	#NO_APP
	movzbl	65584(%rsp), %eax
	.seh_startepilogue
	addq	$71728, %rsp
	popq	%rsi
	.seh_endepilogue
	retq
	.seh_endproc

	.def	frame_8k;
	.scl	2;
	.type	32;
	.endef
	.globl	frame_8k
	.p2align	4
frame_8k:
.Lfunc_begin2:
.seh_proc frame_8k
	pushq	%rsi
	.seh_pushreg %rsi
	movl	$8240, %eax
	callq	___chkstk_ms
	subq	%rax, %rsp
	.seh_stackalloc 8240
	.seh_endprologue
	movl	%ecx, %edx
	leaq	48(%rsp), %rsi
	movl	$8192, %r8d
	movq	%rsi, %rcx
	callq	memset
	movq	%rsi, 40(%rsp)
	leaq	40(%rsp), %rax
	#APP
	#NO_APP
	movzbl	4144(%rsp), %eax
	.seh_startepilogue
	addq	$8240, %rsp
	popq	%rsi
	.seh_endepilogue
	retq
	.seh_endproc

	.def	overaligned_frame;
	.scl	2;
	.type	32;
	.endef
	.globl	overaligned_frame
	.p2align	4
overaligned_frame:
.Lfunc_begin3:
.seh_proc overaligned_frame
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$176, %rsp
	.seh_stackalloc 176
	leaq	128(%rsp), %rbp
	.seh_setframe %rbp, 128
	.seh_endprologue
	andq	$-64, %rsp
	movzbl	%cl, %eax
	movd	%eax, %xmm0
	punpcklbw	%xmm0, %xmm0
	pshuflw	$0, %xmm0, %xmm0
	pshufd	$68, %xmm0, %xmm0
	movdqa	%xmm0, 112(%rsp)
	movdqa	%xmm0, 96(%rsp)
	movdqa	%xmm0, 80(%rsp)
	movdqa	%xmm0, 64(%rsp)
	leaq	64(%rsp), %rcx
	callq	*%rdx
	movzbl	64(%rsp), %eax
	.seh_startepilogue
	leaq	48(%rbp), %rsp
	popq	%rbp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	redzone_leaf;
	.scl	2;
	.type	32;
	.endef
	.globl	redzone_leaf
	.p2align	4
redzone_leaf:
.Lfunc_begin4:
.seh_proc redzone_leaf
	subq	$72, %rsp
	.seh_stackalloc 72
	.seh_endprologue
	leaq	(%r9,%rdx), %rax
	movq	%rcx, 8(%rsp)
	movq	%rdx, 16(%rsp)
	xorq	%rcx, %rdx
	movq	%r8, 24(%rsp)
	movq	%r9, 32(%rsp)
	xorq	%r8, %r9
	addq	%r8, %rcx
	movq	%rdx, 40(%rsp)
	movq	%r9, 48(%rsp)
	movq	%rcx, 56(%rsp)
	movq	%rax, 64(%rsp)
	leaq	8(%rsp), %rax
	movq	%rax, (%rsp)
	movq	%rsp, %rax
	#APP
	#NO_APP
	movq	64(%rsp), %rax
	addq	8(%rsp), %rax
	.seh_startepilogue
	addq	$72, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

