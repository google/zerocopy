	.file	"c_u128_sysv_probe.c"
	.text
	.p2align 4
	.globl	read_1gp_then_u128_then_u64
	.type	read_1gp_then_u128_then_u64, @function
read_1gp_then_u128_then_u64:
.LFB11:
	.cfi_startproc
	leaq	8(%rsp), %rax
	movq	%rdx, -40(%rsp)
	xorl	%edx, %edx
	movq	%rax, -72(%rsp)
	leaq	-56(%rsp), %rax
	movq	%rsi, -48(%rsp)
	movq	%rax, -64(%rsp)
	movq	%rcx, %rax
	addq	-48(%rsp), %rax
	movq	%rcx, -32(%rsp)
	adcq	-40(%rsp), %rdx
	movl	$8, -80(%rsp)
	ret
	.cfi_endproc
.LFE11:
	.size	read_1gp_then_u128_then_u64, .-read_1gp_then_u128_then_u64
	.p2align 4
	.globl	read_5gp_then_u128_then_u64
	.type	read_5gp_then_u128_then_u64, @function
read_5gp_then_u128_then_u64:
.LFB12:
	.cfi_startproc
	leaq	23(%rsp), %rdx
	leaq	-56(%rsp), %rax
	movq	%r9, %rsi
	xorl	%edi, %edi
	andq	$-16, %rdx
	movq	%r9, -16(%rsp)
	movq	%rax, -64(%rsp)
	addq	(%rdx), %rsi
	leaq	16(%rdx), %rax
	adcq	8(%rdx), %rdi
	movq	%rax, -72(%rsp)
	movq	%rsi, %rax
	movl	$40, -80(%rsp)
	movq	%rdi, %rdx
	ret
	.cfi_endproc
.LFE12:
	.size	read_5gp_then_u128_then_u64, .-read_5gp_then_u128_then_u64
	.p2align 4
	.globl	read_7gp_then_u128
	.type	read_7gp_then_u128, @function
read_7gp_then_u128:
.LFB13:
	.cfi_startproc
	leaq	8(%rsp), %rax
	movl	$48, -80(%rsp)
	movq	%rax, -72(%rsp)
	leaq	-56(%rsp), %rax
	movq	%rax, -64(%rsp)
	leaq	31(%rsp), %rax
	andq	$-16, %rax
	movq	8(%rax), %rdx
	movq	(%rax), %rax
	addq	8(%rsp), %rax
	adcq	$0, %rdx
	ret
	.cfi_endproc
.LFE13:
	.size	read_7gp_then_u128, .-read_7gp_then_u128
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC0:
	.string	"U128_ODD_GP_OK=%d U128_SPILL_R9_BACKFILL_OK=%d U128_OVERFLOW_ALIGN16_OK=%d\n"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB14:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movl	$1, %edi
	movl	$7, %ecx
	xorl	%eax, %eax
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	movl	$5, %r8d
	movabsq	$-7373874951294615808, %rsi
	movabsq	$1234605616436508552, %rdx
	movl	$9, %r9d
	subq	$8, %rsp
	.cfi_def_cfa_offset 32
	call	read_1gp_then_u128_then_u64
	movl	$4, %ecx
	movl	$2, %esi
	movq	%rax, %r10
	movq	%rdx, %rbx
	movabsq	$1234605616436508552, %rax
	movabsq	$-7373874951294615808, %rdx
	pushq	%rax
	.cfi_def_cfa_offset 40
	xorl	%eax, %eax
	pushq	%rdx
	.cfi_def_cfa_offset 48
	movl	$3, %edx
	call	read_5gp_then_u128_then_u64
	movl	$6, %r9d
	movabsq	$1234605616436508552, %rsi
	movabsq	$-7373874951294615808, %rdi
	pushq	%rsi
	.cfi_def_cfa_offset 56
	movq	%rax, %r11
	movq	%rdx, %rbp
	movl	$2, %esi
	pushq	%rdi
	.cfi_def_cfa_offset 64
	xorl	%eax, %eax
	movl	$1, %edi
	movl	$3, %edx
	subq	$8, %rsp
	.cfi_def_cfa_offset 72
	pushq	$11
	.cfi_def_cfa_offset 80
	call	read_7gp_then_u128
	addq	$48, %rsp
	.cfi_def_cfa_offset 32
	movabsq	$-7373874951294615797, %rcx
	xorq	%rcx, %rax
	movabsq	$1234605616436508552, %rcx
	xorq	%rcx, %rdx
	xorl	%ecx, %ecx
	orq	%rdx, %rax
	movabsq	$-7373874951294615799, %rax
	movabsq	$1234605616436508552, %rdx
	sete	%cl
	xorq	%rbp, %rdx
	xorq	%r11, %rax
	xorl	%edi, %edi
	orq	%rdx, %rax
	movabsq	$-7373874951294615801, %rax
	movabsq	$1234605616436508552, %rdx
	sete	%dil
	xorq	%rbx, %rdx
	xorq	%r10, %rax
	xorl	%esi, %esi
	orq	%rdx, %rax
	movl	%edi, %edx
	leaq	.LC0(%rip), %rdi
	sete	%sil
	xorl	%eax, %eax
	call	printf@PLT
	addq	$8, %rsp
	.cfi_def_cfa_offset 24
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE14:
	.size	main, .-main
	.ident	"GCC: (Debian 15.2.0-14) 15.2.0"
	.section	.note.GNU-stack,"",@progbits
