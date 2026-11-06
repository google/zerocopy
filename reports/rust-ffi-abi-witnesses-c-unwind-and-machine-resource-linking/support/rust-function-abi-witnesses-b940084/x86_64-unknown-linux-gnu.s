	.file	"abi_witness.c"
	.text
	.globl	abi_add                         # -- Begin function abi_add
	.p2align	4
	.type	abi_add,@function
abi_add:                                # @abi_add
	.cfi_startproc
# %bb.0:
	leaq	(%rdi,%rsi), %rax
	retq
.Lfunc_end0:
	.size	abi_add, .Lfunc_end0-abi_add
	.cfi_endproc
                                        # -- End function
	.globl	abi_pair                        # -- Begin function abi_pair
	.p2align	4
	.type	abi_pair,@function
abi_pair:                               # @abi_pair
	.cfi_startproc
# %bb.0:
	movq	%rsi, %rax
	movq	%rdi, %rdx
	retq
.Lfunc_end1:
	.size	abi_pair, .Lfunc_end1-abi_pair
	.cfi_endproc
                                        # -- End function
	.globl	abi_triple                      # -- Begin function abi_triple
	.p2align	4
	.type	abi_triple,@function
abi_triple:                             # @abi_triple
	.cfi_startproc
# %bb.0:
	movq	%rdi, %rax
	movdqu	16(%rsp), %xmm0
	pshufd	$78, %xmm0, %xmm0               # xmm0 = xmm0[2,3,0,1]
	movdqu	%xmm0, (%rdi)
	movq	8(%rsp), %rcx
	movq	%rcx, 16(%rdi)
	retq
.Lfunc_end2:
	.size	abi_triple, .Lfunc_end2-abi_triple
	.cfi_endproc
                                        # -- End function
	.ident	"Apple clang version 21.0.0 (clang-2100.3.34.2)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
