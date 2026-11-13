	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 1
	.att_syntax
	.file	"stack_probe.3f9c3f566e408f32-cgu.0"
	.def	_frame_3k;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_frame_3k,unique,0
	.globl	_frame_3k
	.p2align	4
_frame_3k:
Lfunc_begin0:
	pushl	%esi
	subl	$3076, %esp
	movl	3084(%esp), %eax
	leal	4(%esp), %esi
	pushl	$3072
	pushl	%eax
	pushl	%esi
	calll	_memset
	addl	$12, %esp
	movl	%esi, (%esp)
	movl	%esp, %eax
	#APP
	#NO_APP
	movzbl	1028(%esp), %eax
	addl	$3076, %esp
	popl	%esi
	retl

	.def	_frame_70k;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_frame_70k,unique,1
	.globl	_frame_70k
	.p2align	4
_frame_70k:
Lfunc_begin1:
	pushl	%esi
	movl	$71684, %eax
	calll	__chkstk
	movl	71692(%esp), %eax
	leal	4(%esp), %esi
	pushl	$71680
	pushl	%eax
	pushl	%esi
	calll	_memset
	addl	$12, %esp
	movl	%esi, (%esp)
	movl	%esp, %eax
	#APP
	#NO_APP
	movzbl	65540(%esp), %eax
	addl	$71684, %esp
	popl	%esi
	retl

	.def	_frame_8k;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_frame_8k,unique,2
	.globl	_frame_8k
	.p2align	4
_frame_8k:
Lfunc_begin2:
	pushl	%esi
	movl	$8196, %eax
	calll	__chkstk
	movl	8204(%esp), %eax
	leal	4(%esp), %esi
	pushl	$8192
	pushl	%eax
	pushl	%esi
	calll	_memset
	addl	$12, %esp
	movl	%esi, (%esp)
	movl	%esp, %eax
	#APP
	#NO_APP
	movzbl	4100(%esp), %eax
	addl	$8196, %esp
	popl	%esi
	retl

	.def	_overaligned_frame;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_overaligned_frame,unique,3
	.globl	_overaligned_frame
	.p2align	4
_overaligned_frame:
Lfunc_begin3:
	pushl	%ebp
	movl	%esp, %ebp
	andl	$-64, %esp
	subl	$128, %esp
	movd	8(%ebp), %xmm0
	movl	%esp, %eax
	punpcklbw	%xmm0, %xmm0
	pshuflw	$0, %xmm0, %xmm0
	pshufd	$68, %xmm0, %xmm0
	movdqa	%xmm0, 48(%esp)
	movdqa	%xmm0, 32(%esp)
	movdqa	%xmm0, 16(%esp)
	movdqa	%xmm0, (%esp)
	pushl	%eax
	calll	*12(%ebp)
	addl	$4, %esp
	movzbl	(%esp), %eax
	movl	%ebp, %esp
	popl	%ebp
	retl

	.def	_redzone_leaf;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_redzone_leaf,unique,4
	.globl	_redzone_leaf
	.p2align	4
_redzone_leaf:
Lfunc_begin4:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	pushl	%edi
	pushl	%esi
	andl	$-8, %esp
	subl	$88, %esp
	movl	8(%ebp), %edi
	movl	16(%ebp), %eax
	movl	20(%ebp), %ecx
	movl	24(%ebp), %ebx
	movl	36(%ebp), %esi
	xorl	%edi, %eax
	movl	%edi, 16(%esp)
	movl	%ecx, %edx
	movl	16(%ebp), %edi
	movl	%eax, 8(%esp)
	movl	%ecx, %eax
	movl	28(%ebp), %ecx
	xorl	12(%ebp), %eax
	xorl	%ecx, %esi
	movl	%eax, (%esp)
	movl	32(%ebp), %eax
	xorl	%ebx, %eax
	movl	%eax, 4(%esp)
	movl	12(%ebp), %eax
	movl	%eax, 20(%esp)
	movl	%edx, 28(%esp)
	movl	%edi, 24(%esp)
	movl	%ebx, 32(%esp)
	addl	8(%ebp), %ebx
	movl	%ecx, %edx
	movl	%ecx, 36(%esp)
	movl	32(%ebp), %ecx
	adcl	%eax, %edx
	movl	%ecx, 40(%esp)
	addl	%edi, %ecx
	movl	36(%ebp), %eax
	movl	(%esp), %edi
	movl	%eax, 44(%esp)
	movl	%edi, 52(%esp)
	movl	8(%esp), %edi
	adcl	20(%ebp), %eax
	movl	%edi, 48(%esp)
	movl	%esi, 60(%esp)
	movl	4(%esp), %esi
	movl	%esi, 56(%esp)
	movl	%ebx, 64(%esp)
	movl	%edx, 68(%esp)
	movl	%eax, 76(%esp)
	leal	16(%esp), %eax
	movl	%ecx, 72(%esp)
	movl	%eax, 12(%esp)
	leal	12(%esp), %eax
	#APP
	#NO_APP
	movl	72(%esp), %eax
	movl	76(%esp), %edx
	addl	16(%esp), %eax
	adcl	20(%esp), %edx
	leal	-12(%ebp), %esp
	popl	%esi
	popl	%edi
	popl	%ebx
	popl	%ebp
	retl

