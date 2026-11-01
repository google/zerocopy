	.file	"probe_d_lifetime_aa.ll"
	.text
	.globl	dse_lifetime_end                # -- Begin function dse_lifetime_end
	.p2align	4
	.type	dse_lifetime_end,@function
dse_lifetime_end:                       # @dse_lifetime_end
	.cfi_startproc
# %bb.0:                                # %entry
	retq
.Lfunc_end0:
	.size	dse_lifetime_end, .Lfunc_end0-dse_lifetime_end
	.cfi_endproc
                                        # -- End function
	.globl	disjoint_lifetime_stack_coloring # -- Begin function disjoint_lifetime_stack_coloring
	.p2align	4
	.type	disjoint_lifetime_stack_coloring,@function
disjoint_lifetime_stack_coloring:       # @disjoint_lifetime_stack_coloring
	.cfi_startproc
# %bb.0:                                # %entry
	pushq	%rbx
	.cfi_def_cfa_offset 16
	subq	$64, %rsp
	.cfi_def_cfa_offset 80
	.cfi_offset %rbx, -16
	movb	$0, (%rdi)
	movq	%rsp, %rdi
	callq	observe_addr@PLT
	movq	%rax, %rbx
	movq	%rsp, %rdi
	callq	observe_addr@PLT
	cmpq	%rax, %rbx
	sete	%al
	addq	$64, %rsp
	.cfi_def_cfa_offset 16
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end1:
	.size	disjoint_lifetime_stack_coloring, .Lfunc_end1-disjoint_lifetime_stack_coloring
	.cfi_endproc
                                        # -- End function
	.section	".note.GNU-stack","",@progbits
