# CE2 (-C opt-level=2): leaf_with_nostack vs leaf_without_nostack
	.cfi_startproc
	movq	%rdi, -16(%rsp)
	movq	%rsi, -8(%rsp)
	movabsq	$-2401053092612145152, %rax
	#APP

	pushq	%rax
	pushq	%rax
	popq	%rcx
	popq	%rcx

	#NO_APP
	movq	-16(%rsp), %rax
	xorq	-8(%rsp), %rax
	retq
.Lfunc_end4:
	.size	_RNvCsetPoM0sv49M_19ce2_redzone_nostack17leaf_with_nostack, .Lfunc_end4-_RNvCsetPoM0sv49M_19ce2_redzone_nostack17leaf_with_nostack
	.cfi_endproc

	.section	.text._RNvCsetPoM0sv49M_19ce2_redzone_nostack20leaf_without_nostack,"ax",@progbits
	.p2align	4
	.type	_RNvCsetPoM0sv49M_19ce2_redzone_nostack20leaf_without_nostack,@function

	.cfi_startproc
	subq	$24, %rsp
	.cfi_def_cfa_offset 32
	movq	%rdi, 8(%rsp)
	movq	%rsi, 16(%rsp)
	movabsq	$-2401053092612145152, %rax
	#APP

	pushq	%rax
	pushq	%rax
	popq	%rcx
	popq	%rcx

	#NO_APP
	movq	8(%rsp), %rax
	xorq	16(%rsp), %rax
	addq	$24, %rsp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end5:
	.size	_RNvCsetPoM0sv49M_19ce2_redzone_nostack20leaf_without_nostack, .Lfunc_end5-_RNvCsetPoM0sv49M_19ce2_redzone_nostack20leaf_without_nostack
	.cfi_endproc

	.section	.text._RNvCsetPoM0sv49M_19ce2_redzone_nostack4main,"ax",@progbits
	.hidden	_RNvCsetPoM0sv49M_19ce2_redzone_nostack4main
	.globl	_RNvCsetPoM0sv49M_19ce2_redzone_nostack4main
	.p2align	4
	.type	_RNvCsetPoM0sv49M_19ce2_redzone_nostack4main,@function
