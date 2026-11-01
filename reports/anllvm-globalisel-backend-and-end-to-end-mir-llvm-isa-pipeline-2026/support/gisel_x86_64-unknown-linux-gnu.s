	.file	"backend_probe.ll"
	.text
	.globl	add_u128_and_u8                 # -- Begin function add_u128_and_u8
	.p2align	4
	.type	add_u128_and_u8,@function
add_u128_and_u8:                        # @add_u128_and_u8
# %bb.0:                                # %entry
	addq	%rdi, %rdx
	adcq	%rsi, %rcx
	addb	%r8b, %r9b
	movzbl	%r9b, %eax
	addq	%rdx, %rax
	adcq	$0, %rcx
	movq	%rcx, %rdx
	retq
.Lfunc_end0:
	.size	add_u128_and_u8, .Lfunc_end0-add_u128_and_u8
                                        # -- End function
	.globl	gep_load_select                 # -- Begin function gep_load_select
	.p2align	4
	.type	gep_load_select,@function
gep_load_select:                        # @gep_load_select
# %bb.0:                                # %entry
	movq	%rcx, %rax
	cmpq	%rdx, %rsi
	setb	%cl
	testb	$1, %cl
	je	.LBB1_2
# %bb.1:                                # %in_bounds
	imulq	$8, %rsi, %rcx
	addq	%rdi, %rcx
	movq	(%rcx), %rcx
	xorl	%edx, %edx
	cmpq	%rax, %rcx
	seta	%dl
	andl	$1, %edx
	cmovneq	%rcx, %rax
.LBB1_2:                                # %exit
	retq
.Lfunc_end1:
	.size	gep_load_select, .Lfunc_end1-gep_load_select
                                        # -- End function
	.section	".note.GNU-stack","",@progbits
