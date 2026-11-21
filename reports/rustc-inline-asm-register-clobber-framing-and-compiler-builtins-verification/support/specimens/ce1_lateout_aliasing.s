# CE1 (-C opt-level=2): lateout(reg) vs out(reg)
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	callq	_RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing6id_eax
	#APP

	movl	$0, %eax
	addl	%eax, %eax

	#NO_APP
	popq	%rcx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end4:
	.size	_RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing22buggy_lateout_zero_add, .Lfunc_end4-_RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing22buggy_lateout_zero_add
	.cfi_endproc

	.section	.text._RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing23safe_early_out_zero_add,"ax",@progbits
	.p2align	4
	.type	_RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing23safe_early_out_zero_add,@function

	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	callq	_RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing6id_eax
	#APP

	movl	$0, %ecx
	addl	%eax, %ecx

	#NO_APP
	movl	%ecx, %eax
	popq	%rcx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end5:
	.size	_RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing23safe_early_out_zero_add, .Lfunc_end5-_RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing23safe_early_out_zero_add
	.cfi_endproc

	.section	.text._RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing4main,"ax",@progbits
	.hidden	_RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing4main
	.globl	_RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing4main
	.p2align	4
	.type	_RNvCsf4wsjs71Ta3_20ce1_lateout_aliasing4main,@function
