	.att_syntax
	.file	"atomic_probe.15283d9b12ef6327-cgu.0"
	.section	.text._RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,"ax",@progbits
	.globl	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.prefalign	4, .Lfunc_end0, nop
	.type	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,@function
_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind:
	.cfi_startproc
	.p2align	4
.LBB0_1:
	jmp	.LBB0_1
.Lfunc_end0:
	.size	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind, .Lfunc_end0-_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.cfi_endproc

	.section	.text.atomic_and_128_acqrel,"ax",@progbits
	.globl	atomic_and_128_acqrel
	.prefalign	4, .Lfunc_end1, nop
	.type	atomic_and_128_acqrel,@function
atomic_and_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB1_1:
	movq	%rax, %rbx
	andq	%rsi, %rbx
	movq	%rdx, %rcx
	andq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB1_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end1:
	.size	atomic_and_128_acqrel, .Lfunc_end1-atomic_and_128_acqrel
	.cfi_endproc

	.section	.text.atomic_and_128_acquire,"ax",@progbits
	.globl	atomic_and_128_acquire
	.prefalign	4, .Lfunc_end2, nop
	.type	atomic_and_128_acquire,@function
atomic_and_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB2_1:
	movq	%rax, %rbx
	andq	%rsi, %rbx
	movq	%rdx, %rcx
	andq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB2_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end2:
	.size	atomic_and_128_acquire, .Lfunc_end2-atomic_and_128_acquire
	.cfi_endproc

	.section	.text.atomic_and_128_relaxed,"ax",@progbits
	.globl	atomic_and_128_relaxed
	.prefalign	4, .Lfunc_end3, nop
	.type	atomic_and_128_relaxed,@function
atomic_and_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB3_1:
	movq	%rax, %rbx
	andq	%rsi, %rbx
	movq	%rdx, %rcx
	andq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB3_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end3:
	.size	atomic_and_128_relaxed, .Lfunc_end3-atomic_and_128_relaxed
	.cfi_endproc

	.section	.text.atomic_and_128_release,"ax",@progbits
	.globl	atomic_and_128_release
	.prefalign	4, .Lfunc_end4, nop
	.type	atomic_and_128_release,@function
atomic_and_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB4_1:
	movq	%rax, %rbx
	andq	%rsi, %rbx
	movq	%rdx, %rcx
	andq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB4_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end4:
	.size	atomic_and_128_release, .Lfunc_end4-atomic_and_128_release
	.cfi_endproc

	.section	.text.atomic_and_128_seqcst,"ax",@progbits
	.globl	atomic_and_128_seqcst
	.prefalign	4, .Lfunc_end5, nop
	.type	atomic_and_128_seqcst,@function
atomic_and_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB5_1:
	movq	%rax, %rbx
	andq	%rsi, %rbx
	movq	%rdx, %rcx
	andq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB5_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end5:
	.size	atomic_and_128_seqcst, .Lfunc_end5-atomic_and_128_seqcst
	.cfi_endproc

	.section	.text.atomic_and_16_acqrel,"ax",@progbits
	.globl	atomic_and_16_acqrel
	.prefalign	4, .Lfunc_end6, nop
	.type	atomic_and_16_acqrel,@function
atomic_and_16_acqrel:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB6_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB6_1
	retq
.Lfunc_end6:
	.size	atomic_and_16_acqrel, .Lfunc_end6-atomic_and_16_acqrel
	.cfi_endproc

	.section	.text.atomic_and_16_acquire,"ax",@progbits
	.globl	atomic_and_16_acquire
	.prefalign	4, .Lfunc_end7, nop
	.type	atomic_and_16_acquire,@function
atomic_and_16_acquire:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB7_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB7_1
	retq
.Lfunc_end7:
	.size	atomic_and_16_acquire, .Lfunc_end7-atomic_and_16_acquire
	.cfi_endproc

	.section	.text.atomic_and_16_relaxed,"ax",@progbits
	.globl	atomic_and_16_relaxed
	.prefalign	4, .Lfunc_end8, nop
	.type	atomic_and_16_relaxed,@function
atomic_and_16_relaxed:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB8_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB8_1
	retq
.Lfunc_end8:
	.size	atomic_and_16_relaxed, .Lfunc_end8-atomic_and_16_relaxed
	.cfi_endproc

	.section	.text.atomic_and_16_release,"ax",@progbits
	.globl	atomic_and_16_release
	.prefalign	4, .Lfunc_end9, nop
	.type	atomic_and_16_release,@function
atomic_and_16_release:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB9_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB9_1
	retq
.Lfunc_end9:
	.size	atomic_and_16_release, .Lfunc_end9-atomic_and_16_release
	.cfi_endproc

	.section	.text.atomic_and_16_seqcst,"ax",@progbits
	.globl	atomic_and_16_seqcst
	.prefalign	4, .Lfunc_end10, nop
	.type	atomic_and_16_seqcst,@function
atomic_and_16_seqcst:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB10_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB10_1
	retq
.Lfunc_end10:
	.size	atomic_and_16_seqcst, .Lfunc_end10-atomic_and_16_seqcst
	.cfi_endproc

	.section	.text.atomic_and_32_acqrel,"ax",@progbits
	.globl	atomic_and_32_acqrel
	.prefalign	4, .Lfunc_end11, nop
	.type	atomic_and_32_acqrel,@function
atomic_and_32_acqrel:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB11_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB11_1
	retq
.Lfunc_end11:
	.size	atomic_and_32_acqrel, .Lfunc_end11-atomic_and_32_acqrel
	.cfi_endproc

	.section	.text.atomic_and_32_acquire,"ax",@progbits
	.globl	atomic_and_32_acquire
	.prefalign	4, .Lfunc_end12, nop
	.type	atomic_and_32_acquire,@function
atomic_and_32_acquire:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB12_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB12_1
	retq
.Lfunc_end12:
	.size	atomic_and_32_acquire, .Lfunc_end12-atomic_and_32_acquire
	.cfi_endproc

	.section	.text.atomic_and_32_relaxed,"ax",@progbits
	.globl	atomic_and_32_relaxed
	.prefalign	4, .Lfunc_end13, nop
	.type	atomic_and_32_relaxed,@function
atomic_and_32_relaxed:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB13_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB13_1
	retq
.Lfunc_end13:
	.size	atomic_and_32_relaxed, .Lfunc_end13-atomic_and_32_relaxed
	.cfi_endproc

	.section	.text.atomic_and_32_release,"ax",@progbits
	.globl	atomic_and_32_release
	.prefalign	4, .Lfunc_end14, nop
	.type	atomic_and_32_release,@function
atomic_and_32_release:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB14_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB14_1
	retq
.Lfunc_end14:
	.size	atomic_and_32_release, .Lfunc_end14-atomic_and_32_release
	.cfi_endproc

	.section	.text.atomic_and_32_seqcst,"ax",@progbits
	.globl	atomic_and_32_seqcst
	.prefalign	4, .Lfunc_end15, nop
	.type	atomic_and_32_seqcst,@function
atomic_and_32_seqcst:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB15_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB15_1
	retq
.Lfunc_end15:
	.size	atomic_and_32_seqcst, .Lfunc_end15-atomic_and_32_seqcst
	.cfi_endproc

	.section	.text.atomic_and_64_acqrel,"ax",@progbits
	.globl	atomic_and_64_acqrel
	.prefalign	4, .Lfunc_end16, nop
	.type	atomic_and_64_acqrel,@function
atomic_and_64_acqrel:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB16_1:
	movq	%rax, %rcx
	andq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB16_1
	retq
.Lfunc_end16:
	.size	atomic_and_64_acqrel, .Lfunc_end16-atomic_and_64_acqrel
	.cfi_endproc

	.section	.text.atomic_and_64_acquire,"ax",@progbits
	.globl	atomic_and_64_acquire
	.prefalign	4, .Lfunc_end17, nop
	.type	atomic_and_64_acquire,@function
atomic_and_64_acquire:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB17_1:
	movq	%rax, %rcx
	andq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB17_1
	retq
.Lfunc_end17:
	.size	atomic_and_64_acquire, .Lfunc_end17-atomic_and_64_acquire
	.cfi_endproc

	.section	.text.atomic_and_64_relaxed,"ax",@progbits
	.globl	atomic_and_64_relaxed
	.prefalign	4, .Lfunc_end18, nop
	.type	atomic_and_64_relaxed,@function
atomic_and_64_relaxed:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB18_1:
	movq	%rax, %rcx
	andq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB18_1
	retq
.Lfunc_end18:
	.size	atomic_and_64_relaxed, .Lfunc_end18-atomic_and_64_relaxed
	.cfi_endproc

	.section	.text.atomic_and_64_release,"ax",@progbits
	.globl	atomic_and_64_release
	.prefalign	4, .Lfunc_end19, nop
	.type	atomic_and_64_release,@function
atomic_and_64_release:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB19_1:
	movq	%rax, %rcx
	andq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB19_1
	retq
.Lfunc_end19:
	.size	atomic_and_64_release, .Lfunc_end19-atomic_and_64_release
	.cfi_endproc

	.section	.text.atomic_and_64_seqcst,"ax",@progbits
	.globl	atomic_and_64_seqcst
	.prefalign	4, .Lfunc_end20, nop
	.type	atomic_and_64_seqcst,@function
atomic_and_64_seqcst:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB20_1:
	movq	%rax, %rcx
	andq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB20_1
	retq
.Lfunc_end20:
	.size	atomic_and_64_seqcst, .Lfunc_end20-atomic_and_64_seqcst
	.cfi_endproc

	.section	.text.atomic_and_8_acqrel,"ax",@progbits
	.globl	atomic_and_8_acqrel
	.prefalign	4, .Lfunc_end21, nop
	.type	atomic_and_8_acqrel,@function
atomic_and_8_acqrel:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB21_1:
	movl	%eax, %ecx
	andb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB21_1
	retq
.Lfunc_end21:
	.size	atomic_and_8_acqrel, .Lfunc_end21-atomic_and_8_acqrel
	.cfi_endproc

	.section	.text.atomic_and_8_acquire,"ax",@progbits
	.globl	atomic_and_8_acquire
	.prefalign	4, .Lfunc_end22, nop
	.type	atomic_and_8_acquire,@function
atomic_and_8_acquire:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB22_1:
	movl	%eax, %ecx
	andb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB22_1
	retq
.Lfunc_end22:
	.size	atomic_and_8_acquire, .Lfunc_end22-atomic_and_8_acquire
	.cfi_endproc

	.section	.text.atomic_and_8_relaxed,"ax",@progbits
	.globl	atomic_and_8_relaxed
	.prefalign	4, .Lfunc_end23, nop
	.type	atomic_and_8_relaxed,@function
atomic_and_8_relaxed:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB23_1:
	movl	%eax, %ecx
	andb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB23_1
	retq
.Lfunc_end23:
	.size	atomic_and_8_relaxed, .Lfunc_end23-atomic_and_8_relaxed
	.cfi_endproc

	.section	.text.atomic_and_8_release,"ax",@progbits
	.globl	atomic_and_8_release
	.prefalign	4, .Lfunc_end24, nop
	.type	atomic_and_8_release,@function
atomic_and_8_release:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB24_1:
	movl	%eax, %ecx
	andb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB24_1
	retq
.Lfunc_end24:
	.size	atomic_and_8_release, .Lfunc_end24-atomic_and_8_release
	.cfi_endproc

	.section	.text.atomic_and_8_seqcst,"ax",@progbits
	.globl	atomic_and_8_seqcst
	.prefalign	4, .Lfunc_end25, nop
	.type	atomic_and_8_seqcst,@function
atomic_and_8_seqcst:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB25_1:
	movl	%eax, %ecx
	andb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB25_1
	retq
.Lfunc_end25:
	.size	atomic_and_8_seqcst, .Lfunc_end25-atomic_and_8_seqcst
	.cfi_endproc

	.section	.text.atomic_compiler_fence_acqrel,"ax",@progbits
	.globl	atomic_compiler_fence_acqrel
	.prefalign	4, .Lfunc_end26, nop
	.type	atomic_compiler_fence_acqrel,@function
atomic_compiler_fence_acqrel:
	.cfi_startproc
	#MEMBARRIER
	retq
.Lfunc_end26:
	.size	atomic_compiler_fence_acqrel, .Lfunc_end26-atomic_compiler_fence_acqrel
	.cfi_endproc

	.section	.text.atomic_compiler_fence_acquire,"ax",@progbits
	.globl	atomic_compiler_fence_acquire
	.prefalign	4, .Lfunc_end27, nop
	.type	atomic_compiler_fence_acquire,@function
atomic_compiler_fence_acquire:
	.cfi_startproc
	#MEMBARRIER
	retq
.Lfunc_end27:
	.size	atomic_compiler_fence_acquire, .Lfunc_end27-atomic_compiler_fence_acquire
	.cfi_endproc

	.section	.text.atomic_compiler_fence_release,"ax",@progbits
	.globl	atomic_compiler_fence_release
	.prefalign	4, .Lfunc_end28, nop
	.type	atomic_compiler_fence_release,@function
atomic_compiler_fence_release:
	.cfi_startproc
	#MEMBARRIER
	retq
.Lfunc_end28:
	.size	atomic_compiler_fence_release, .Lfunc_end28-atomic_compiler_fence_release
	.cfi_endproc

	.section	.text.atomic_compiler_fence_seqcst,"ax",@progbits
	.globl	atomic_compiler_fence_seqcst
	.prefalign	4, .Lfunc_end29, nop
	.type	atomic_compiler_fence_seqcst,@function
atomic_compiler_fence_seqcst:
	.cfi_startproc
	#MEMBARRIER
	retq
.Lfunc_end29:
	.size	atomic_compiler_fence_seqcst, .Lfunc_end29-atomic_compiler_fence_seqcst
	.cfi_endproc

	.section	.text.atomic_fence_acqrel,"ax",@progbits
	.globl	atomic_fence_acqrel
	.prefalign	4, .Lfunc_end30, nop
	.type	atomic_fence_acqrel,@function
atomic_fence_acqrel:
	.cfi_startproc
	#MEMBARRIER
	retq
.Lfunc_end30:
	.size	atomic_fence_acqrel, .Lfunc_end30-atomic_fence_acqrel
	.cfi_endproc

	.section	.text.atomic_fence_acquire,"ax",@progbits
	.globl	atomic_fence_acquire
	.prefalign	4, .Lfunc_end31, nop
	.type	atomic_fence_acquire,@function
atomic_fence_acquire:
	.cfi_startproc
	#MEMBARRIER
	retq
.Lfunc_end31:
	.size	atomic_fence_acquire, .Lfunc_end31-atomic_fence_acquire
	.cfi_endproc

	.section	.text.atomic_fence_release,"ax",@progbits
	.globl	atomic_fence_release
	.prefalign	4, .Lfunc_end32, nop
	.type	atomic_fence_release,@function
atomic_fence_release:
	.cfi_startproc
	#MEMBARRIER
	retq
.Lfunc_end32:
	.size	atomic_fence_release, .Lfunc_end32-atomic_fence_release
	.cfi_endproc

	.section	.text.atomic_fence_seqcst,"ax",@progbits
	.globl	atomic_fence_seqcst
	.prefalign	4, .Lfunc_end33, nop
	.type	atomic_fence_seqcst,@function
atomic_fence_seqcst:
	.cfi_startproc
	lock		orl	$0, -64(%rsp)
	retq
.Lfunc_end33:
	.size	atomic_fence_seqcst, .Lfunc_end33-atomic_fence_seqcst
	.cfi_endproc

	.section	.text.atomic_load_128_acquire,"ax",@progbits
	.globl	atomic_load_128_acquire
	.prefalign	4, .Lfunc_end34, nop
	.type	atomic_load_128_acquire,@function
atomic_load_128_acquire:
	.cfi_startproc
	vmovdqa	(%rdi), %xmm0
	vmovq	%xmm0, %rax
	vpextrq	$1, %xmm0, %rdx
	retq
.Lfunc_end34:
	.size	atomic_load_128_acquire, .Lfunc_end34-atomic_load_128_acquire
	.cfi_endproc

	.section	.text.atomic_load_128_relaxed,"ax",@progbits
	.globl	atomic_load_128_relaxed
	.prefalign	4, .Lfunc_end35, nop
	.type	atomic_load_128_relaxed,@function
atomic_load_128_relaxed:
	.cfi_startproc
	vmovdqa	(%rdi), %xmm0
	vmovq	%xmm0, %rax
	vpextrq	$1, %xmm0, %rdx
	retq
.Lfunc_end35:
	.size	atomic_load_128_relaxed, .Lfunc_end35-atomic_load_128_relaxed
	.cfi_endproc

	.section	.text.atomic_load_128_seqcst,"ax",@progbits
	.globl	atomic_load_128_seqcst
	.prefalign	4, .Lfunc_end36, nop
	.type	atomic_load_128_seqcst,@function
atomic_load_128_seqcst:
	.cfi_startproc
	vmovdqa	(%rdi), %xmm0
	vmovq	%xmm0, %rax
	vpextrq	$1, %xmm0, %rdx
	retq
.Lfunc_end36:
	.size	atomic_load_128_seqcst, .Lfunc_end36-atomic_load_128_seqcst
	.cfi_endproc

	.section	.text.atomic_load_16_acquire,"ax",@progbits
	.globl	atomic_load_16_acquire
	.prefalign	4, .Lfunc_end37, nop
	.type	atomic_load_16_acquire,@function
atomic_load_16_acquire:
	.cfi_startproc
	movzwl	(%rdi), %eax
	retq
.Lfunc_end37:
	.size	atomic_load_16_acquire, .Lfunc_end37-atomic_load_16_acquire
	.cfi_endproc

	.section	.text.atomic_load_16_relaxed,"ax",@progbits
	.globl	atomic_load_16_relaxed
	.prefalign	4, .Lfunc_end38, nop
	.type	atomic_load_16_relaxed,@function
atomic_load_16_relaxed:
	.cfi_startproc
	movzwl	(%rdi), %eax
	retq
.Lfunc_end38:
	.size	atomic_load_16_relaxed, .Lfunc_end38-atomic_load_16_relaxed
	.cfi_endproc

	.section	.text.atomic_load_16_seqcst,"ax",@progbits
	.globl	atomic_load_16_seqcst
	.prefalign	4, .Lfunc_end39, nop
	.type	atomic_load_16_seqcst,@function
atomic_load_16_seqcst:
	.cfi_startproc
	movzwl	(%rdi), %eax
	retq
.Lfunc_end39:
	.size	atomic_load_16_seqcst, .Lfunc_end39-atomic_load_16_seqcst
	.cfi_endproc

	.section	.text.atomic_load_32_acquire,"ax",@progbits
	.globl	atomic_load_32_acquire
	.prefalign	4, .Lfunc_end40, nop
	.type	atomic_load_32_acquire,@function
atomic_load_32_acquire:
	.cfi_startproc
	movl	(%rdi), %eax
	retq
.Lfunc_end40:
	.size	atomic_load_32_acquire, .Lfunc_end40-atomic_load_32_acquire
	.cfi_endproc

	.section	.text.atomic_load_32_relaxed,"ax",@progbits
	.globl	atomic_load_32_relaxed
	.prefalign	4, .Lfunc_end41, nop
	.type	atomic_load_32_relaxed,@function
atomic_load_32_relaxed:
	.cfi_startproc
	movl	(%rdi), %eax
	retq
.Lfunc_end41:
	.size	atomic_load_32_relaxed, .Lfunc_end41-atomic_load_32_relaxed
	.cfi_endproc

	.section	.text.atomic_load_32_seqcst,"ax",@progbits
	.globl	atomic_load_32_seqcst
	.prefalign	4, .Lfunc_end42, nop
	.type	atomic_load_32_seqcst,@function
atomic_load_32_seqcst:
	.cfi_startproc
	movl	(%rdi), %eax
	retq
.Lfunc_end42:
	.size	atomic_load_32_seqcst, .Lfunc_end42-atomic_load_32_seqcst
	.cfi_endproc

	.section	.text.atomic_load_64_acquire,"ax",@progbits
	.globl	atomic_load_64_acquire
	.prefalign	4, .Lfunc_end43, nop
	.type	atomic_load_64_acquire,@function
atomic_load_64_acquire:
	.cfi_startproc
	movq	(%rdi), %rax
	retq
.Lfunc_end43:
	.size	atomic_load_64_acquire, .Lfunc_end43-atomic_load_64_acquire
	.cfi_endproc

	.section	.text.atomic_load_64_relaxed,"ax",@progbits
	.globl	atomic_load_64_relaxed
	.prefalign	4, .Lfunc_end44, nop
	.type	atomic_load_64_relaxed,@function
atomic_load_64_relaxed:
	.cfi_startproc
	movq	(%rdi), %rax
	retq
.Lfunc_end44:
	.size	atomic_load_64_relaxed, .Lfunc_end44-atomic_load_64_relaxed
	.cfi_endproc

	.section	.text.atomic_load_64_seqcst,"ax",@progbits
	.globl	atomic_load_64_seqcst
	.prefalign	4, .Lfunc_end45, nop
	.type	atomic_load_64_seqcst,@function
atomic_load_64_seqcst:
	.cfi_startproc
	movq	(%rdi), %rax
	retq
.Lfunc_end45:
	.size	atomic_load_64_seqcst, .Lfunc_end45-atomic_load_64_seqcst
	.cfi_endproc

	.section	.text.atomic_load_8_acquire,"ax",@progbits
	.globl	atomic_load_8_acquire
	.prefalign	4, .Lfunc_end46, nop
	.type	atomic_load_8_acquire,@function
atomic_load_8_acquire:
	.cfi_startproc
	movzbl	(%rdi), %eax
	retq
.Lfunc_end46:
	.size	atomic_load_8_acquire, .Lfunc_end46-atomic_load_8_acquire
	.cfi_endproc

	.section	.text.atomic_load_8_relaxed,"ax",@progbits
	.globl	atomic_load_8_relaxed
	.prefalign	4, .Lfunc_end47, nop
	.type	atomic_load_8_relaxed,@function
atomic_load_8_relaxed:
	.cfi_startproc
	movzbl	(%rdi), %eax
	retq
.Lfunc_end47:
	.size	atomic_load_8_relaxed, .Lfunc_end47-atomic_load_8_relaxed
	.cfi_endproc

	.section	.text.atomic_load_8_seqcst,"ax",@progbits
	.globl	atomic_load_8_seqcst
	.prefalign	4, .Lfunc_end48, nop
	.type	atomic_load_8_seqcst,@function
atomic_load_8_seqcst:
	.cfi_startproc
	movzbl	(%rdi), %eax
	retq
.Lfunc_end48:
	.size	atomic_load_8_seqcst, .Lfunc_end48-atomic_load_8_seqcst
	.cfi_endproc

	.section	.text.atomic_max_128_acqrel,"ax",@progbits
	.globl	atomic_max_128_acqrel
	.prefalign	4, .Lfunc_end49, nop
	.type	atomic_max_128_acqrel,@function
atomic_max_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB49_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovlq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovlq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB49_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end49:
	.size	atomic_max_128_acqrel, .Lfunc_end49-atomic_max_128_acqrel
	.cfi_endproc

	.section	.text.atomic_max_128_acquire,"ax",@progbits
	.globl	atomic_max_128_acquire
	.prefalign	4, .Lfunc_end50, nop
	.type	atomic_max_128_acquire,@function
atomic_max_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB50_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovlq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovlq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB50_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end50:
	.size	atomic_max_128_acquire, .Lfunc_end50-atomic_max_128_acquire
	.cfi_endproc

	.section	.text.atomic_max_128_relaxed,"ax",@progbits
	.globl	atomic_max_128_relaxed
	.prefalign	4, .Lfunc_end51, nop
	.type	atomic_max_128_relaxed,@function
atomic_max_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB51_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovlq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovlq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB51_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end51:
	.size	atomic_max_128_relaxed, .Lfunc_end51-atomic_max_128_relaxed
	.cfi_endproc

	.section	.text.atomic_max_128_release,"ax",@progbits
	.globl	atomic_max_128_release
	.prefalign	4, .Lfunc_end52, nop
	.type	atomic_max_128_release,@function
atomic_max_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB52_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovlq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovlq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB52_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end52:
	.size	atomic_max_128_release, .Lfunc_end52-atomic_max_128_release
	.cfi_endproc

	.section	.text.atomic_max_128_seqcst,"ax",@progbits
	.globl	atomic_max_128_seqcst
	.prefalign	4, .Lfunc_end53, nop
	.type	atomic_max_128_seqcst,@function
atomic_max_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB53_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovlq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovlq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB53_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end53:
	.size	atomic_max_128_seqcst, .Lfunc_end53-atomic_max_128_seqcst
	.cfi_endproc

	.section	.text.atomic_max_16_acqrel,"ax",@progbits
	.globl	atomic_max_16_acqrel
	.prefalign	4, .Lfunc_end54, nop
	.type	atomic_max_16_acqrel,@function
atomic_max_16_acqrel:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB54_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovgl	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB54_1
	retq
.Lfunc_end54:
	.size	atomic_max_16_acqrel, .Lfunc_end54-atomic_max_16_acqrel
	.cfi_endproc

	.section	.text.atomic_max_16_acquire,"ax",@progbits
	.globl	atomic_max_16_acquire
	.prefalign	4, .Lfunc_end55, nop
	.type	atomic_max_16_acquire,@function
atomic_max_16_acquire:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB55_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovgl	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB55_1
	retq
.Lfunc_end55:
	.size	atomic_max_16_acquire, .Lfunc_end55-atomic_max_16_acquire
	.cfi_endproc

	.section	.text.atomic_max_16_relaxed,"ax",@progbits
	.globl	atomic_max_16_relaxed
	.prefalign	4, .Lfunc_end56, nop
	.type	atomic_max_16_relaxed,@function
atomic_max_16_relaxed:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB56_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovgl	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB56_1
	retq
.Lfunc_end56:
	.size	atomic_max_16_relaxed, .Lfunc_end56-atomic_max_16_relaxed
	.cfi_endproc

	.section	.text.atomic_max_16_release,"ax",@progbits
	.globl	atomic_max_16_release
	.prefalign	4, .Lfunc_end57, nop
	.type	atomic_max_16_release,@function
atomic_max_16_release:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB57_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovgl	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB57_1
	retq
.Lfunc_end57:
	.size	atomic_max_16_release, .Lfunc_end57-atomic_max_16_release
	.cfi_endproc

	.section	.text.atomic_max_16_seqcst,"ax",@progbits
	.globl	atomic_max_16_seqcst
	.prefalign	4, .Lfunc_end58, nop
	.type	atomic_max_16_seqcst,@function
atomic_max_16_seqcst:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB58_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovgl	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB58_1
	retq
.Lfunc_end58:
	.size	atomic_max_16_seqcst, .Lfunc_end58-atomic_max_16_seqcst
	.cfi_endproc

	.section	.text.atomic_max_32_acqrel,"ax",@progbits
	.globl	atomic_max_32_acqrel
	.prefalign	4, .Lfunc_end59, nop
	.type	atomic_max_32_acqrel,@function
atomic_max_32_acqrel:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB59_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovgl	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB59_1
	retq
.Lfunc_end59:
	.size	atomic_max_32_acqrel, .Lfunc_end59-atomic_max_32_acqrel
	.cfi_endproc

	.section	.text.atomic_max_32_acquire,"ax",@progbits
	.globl	atomic_max_32_acquire
	.prefalign	4, .Lfunc_end60, nop
	.type	atomic_max_32_acquire,@function
atomic_max_32_acquire:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB60_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovgl	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB60_1
	retq
.Lfunc_end60:
	.size	atomic_max_32_acquire, .Lfunc_end60-atomic_max_32_acquire
	.cfi_endproc

	.section	.text.atomic_max_32_relaxed,"ax",@progbits
	.globl	atomic_max_32_relaxed
	.prefalign	4, .Lfunc_end61, nop
	.type	atomic_max_32_relaxed,@function
atomic_max_32_relaxed:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB61_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovgl	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB61_1
	retq
.Lfunc_end61:
	.size	atomic_max_32_relaxed, .Lfunc_end61-atomic_max_32_relaxed
	.cfi_endproc

	.section	.text.atomic_max_32_release,"ax",@progbits
	.globl	atomic_max_32_release
	.prefalign	4, .Lfunc_end62, nop
	.type	atomic_max_32_release,@function
atomic_max_32_release:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB62_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovgl	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB62_1
	retq
.Lfunc_end62:
	.size	atomic_max_32_release, .Lfunc_end62-atomic_max_32_release
	.cfi_endproc

	.section	.text.atomic_max_32_seqcst,"ax",@progbits
	.globl	atomic_max_32_seqcst
	.prefalign	4, .Lfunc_end63, nop
	.type	atomic_max_32_seqcst,@function
atomic_max_32_seqcst:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB63_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovgl	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB63_1
	retq
.Lfunc_end63:
	.size	atomic_max_32_seqcst, .Lfunc_end63-atomic_max_32_seqcst
	.cfi_endproc

	.section	.text.atomic_max_64_acqrel,"ax",@progbits
	.globl	atomic_max_64_acqrel
	.prefalign	4, .Lfunc_end64, nop
	.type	atomic_max_64_acqrel,@function
atomic_max_64_acqrel:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB64_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovgq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB64_1
	retq
.Lfunc_end64:
	.size	atomic_max_64_acqrel, .Lfunc_end64-atomic_max_64_acqrel
	.cfi_endproc

	.section	.text.atomic_max_64_acquire,"ax",@progbits
	.globl	atomic_max_64_acquire
	.prefalign	4, .Lfunc_end65, nop
	.type	atomic_max_64_acquire,@function
atomic_max_64_acquire:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB65_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovgq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB65_1
	retq
.Lfunc_end65:
	.size	atomic_max_64_acquire, .Lfunc_end65-atomic_max_64_acquire
	.cfi_endproc

	.section	.text.atomic_max_64_relaxed,"ax",@progbits
	.globl	atomic_max_64_relaxed
	.prefalign	4, .Lfunc_end66, nop
	.type	atomic_max_64_relaxed,@function
atomic_max_64_relaxed:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB66_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovgq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB66_1
	retq
.Lfunc_end66:
	.size	atomic_max_64_relaxed, .Lfunc_end66-atomic_max_64_relaxed
	.cfi_endproc

	.section	.text.atomic_max_64_release,"ax",@progbits
	.globl	atomic_max_64_release
	.prefalign	4, .Lfunc_end67, nop
	.type	atomic_max_64_release,@function
atomic_max_64_release:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB67_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovgq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB67_1
	retq
.Lfunc_end67:
	.size	atomic_max_64_release, .Lfunc_end67-atomic_max_64_release
	.cfi_endproc

	.section	.text.atomic_max_64_seqcst,"ax",@progbits
	.globl	atomic_max_64_seqcst
	.prefalign	4, .Lfunc_end68, nop
	.type	atomic_max_64_seqcst,@function
atomic_max_64_seqcst:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB68_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovgq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB68_1
	retq
.Lfunc_end68:
	.size	atomic_max_64_seqcst, .Lfunc_end68-atomic_max_64_seqcst
	.cfi_endproc

	.section	.text.atomic_max_8_acqrel,"ax",@progbits
	.globl	atomic_max_8_acqrel
	.prefalign	4, .Lfunc_end69, nop
	.type	atomic_max_8_acqrel,@function
atomic_max_8_acqrel:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB69_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovgl	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB69_1
	retq
.Lfunc_end69:
	.size	atomic_max_8_acqrel, .Lfunc_end69-atomic_max_8_acqrel
	.cfi_endproc

	.section	.text.atomic_max_8_acquire,"ax",@progbits
	.globl	atomic_max_8_acquire
	.prefalign	4, .Lfunc_end70, nop
	.type	atomic_max_8_acquire,@function
atomic_max_8_acquire:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB70_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovgl	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB70_1
	retq
.Lfunc_end70:
	.size	atomic_max_8_acquire, .Lfunc_end70-atomic_max_8_acquire
	.cfi_endproc

	.section	.text.atomic_max_8_relaxed,"ax",@progbits
	.globl	atomic_max_8_relaxed
	.prefalign	4, .Lfunc_end71, nop
	.type	atomic_max_8_relaxed,@function
atomic_max_8_relaxed:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB71_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovgl	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB71_1
	retq
.Lfunc_end71:
	.size	atomic_max_8_relaxed, .Lfunc_end71-atomic_max_8_relaxed
	.cfi_endproc

	.section	.text.atomic_max_8_release,"ax",@progbits
	.globl	atomic_max_8_release
	.prefalign	4, .Lfunc_end72, nop
	.type	atomic_max_8_release,@function
atomic_max_8_release:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB72_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovgl	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB72_1
	retq
.Lfunc_end72:
	.size	atomic_max_8_release, .Lfunc_end72-atomic_max_8_release
	.cfi_endproc

	.section	.text.atomic_max_8_seqcst,"ax",@progbits
	.globl	atomic_max_8_seqcst
	.prefalign	4, .Lfunc_end73, nop
	.type	atomic_max_8_seqcst,@function
atomic_max_8_seqcst:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB73_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovgl	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB73_1
	retq
.Lfunc_end73:
	.size	atomic_max_8_seqcst, .Lfunc_end73-atomic_max_8_seqcst
	.cfi_endproc

	.section	.text.atomic_min_128_acqrel,"ax",@progbits
	.globl	atomic_min_128_acqrel
	.prefalign	4, .Lfunc_end74, nop
	.type	atomic_min_128_acqrel,@function
atomic_min_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB74_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovgeq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovgeq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB74_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end74:
	.size	atomic_min_128_acqrel, .Lfunc_end74-atomic_min_128_acqrel
	.cfi_endproc

	.section	.text.atomic_min_128_acquire,"ax",@progbits
	.globl	atomic_min_128_acquire
	.prefalign	4, .Lfunc_end75, nop
	.type	atomic_min_128_acquire,@function
atomic_min_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB75_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovgeq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovgeq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB75_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end75:
	.size	atomic_min_128_acquire, .Lfunc_end75-atomic_min_128_acquire
	.cfi_endproc

	.section	.text.atomic_min_128_relaxed,"ax",@progbits
	.globl	atomic_min_128_relaxed
	.prefalign	4, .Lfunc_end76, nop
	.type	atomic_min_128_relaxed,@function
atomic_min_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB76_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovgeq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovgeq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB76_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end76:
	.size	atomic_min_128_relaxed, .Lfunc_end76-atomic_min_128_relaxed
	.cfi_endproc

	.section	.text.atomic_min_128_release,"ax",@progbits
	.globl	atomic_min_128_release
	.prefalign	4, .Lfunc_end77, nop
	.type	atomic_min_128_release,@function
atomic_min_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB77_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovgeq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovgeq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB77_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end77:
	.size	atomic_min_128_release, .Lfunc_end77-atomic_min_128_release
	.cfi_endproc

	.section	.text.atomic_min_128_seqcst,"ax",@progbits
	.globl	atomic_min_128_seqcst
	.prefalign	4, .Lfunc_end78, nop
	.type	atomic_min_128_seqcst,@function
atomic_min_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB78_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovgeq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovgeq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB78_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end78:
	.size	atomic_min_128_seqcst, .Lfunc_end78-atomic_min_128_seqcst
	.cfi_endproc

	.section	.text.atomic_min_16_acqrel,"ax",@progbits
	.globl	atomic_min_16_acqrel
	.prefalign	4, .Lfunc_end79, nop
	.type	atomic_min_16_acqrel,@function
atomic_min_16_acqrel:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB79_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovlel	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB79_1
	retq
.Lfunc_end79:
	.size	atomic_min_16_acqrel, .Lfunc_end79-atomic_min_16_acqrel
	.cfi_endproc

	.section	.text.atomic_min_16_acquire,"ax",@progbits
	.globl	atomic_min_16_acquire
	.prefalign	4, .Lfunc_end80, nop
	.type	atomic_min_16_acquire,@function
atomic_min_16_acquire:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB80_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovlel	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB80_1
	retq
.Lfunc_end80:
	.size	atomic_min_16_acquire, .Lfunc_end80-atomic_min_16_acquire
	.cfi_endproc

	.section	.text.atomic_min_16_relaxed,"ax",@progbits
	.globl	atomic_min_16_relaxed
	.prefalign	4, .Lfunc_end81, nop
	.type	atomic_min_16_relaxed,@function
atomic_min_16_relaxed:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB81_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovlel	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB81_1
	retq
.Lfunc_end81:
	.size	atomic_min_16_relaxed, .Lfunc_end81-atomic_min_16_relaxed
	.cfi_endproc

	.section	.text.atomic_min_16_release,"ax",@progbits
	.globl	atomic_min_16_release
	.prefalign	4, .Lfunc_end82, nop
	.type	atomic_min_16_release,@function
atomic_min_16_release:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB82_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovlel	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB82_1
	retq
.Lfunc_end82:
	.size	atomic_min_16_release, .Lfunc_end82-atomic_min_16_release
	.cfi_endproc

	.section	.text.atomic_min_16_seqcst,"ax",@progbits
	.globl	atomic_min_16_seqcst
	.prefalign	4, .Lfunc_end83, nop
	.type	atomic_min_16_seqcst,@function
atomic_min_16_seqcst:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB83_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovlel	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB83_1
	retq
.Lfunc_end83:
	.size	atomic_min_16_seqcst, .Lfunc_end83-atomic_min_16_seqcst
	.cfi_endproc

	.section	.text.atomic_min_32_acqrel,"ax",@progbits
	.globl	atomic_min_32_acqrel
	.prefalign	4, .Lfunc_end84, nop
	.type	atomic_min_32_acqrel,@function
atomic_min_32_acqrel:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB84_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovlel	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB84_1
	retq
.Lfunc_end84:
	.size	atomic_min_32_acqrel, .Lfunc_end84-atomic_min_32_acqrel
	.cfi_endproc

	.section	.text.atomic_min_32_acquire,"ax",@progbits
	.globl	atomic_min_32_acquire
	.prefalign	4, .Lfunc_end85, nop
	.type	atomic_min_32_acquire,@function
atomic_min_32_acquire:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB85_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovlel	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB85_1
	retq
.Lfunc_end85:
	.size	atomic_min_32_acquire, .Lfunc_end85-atomic_min_32_acquire
	.cfi_endproc

	.section	.text.atomic_min_32_relaxed,"ax",@progbits
	.globl	atomic_min_32_relaxed
	.prefalign	4, .Lfunc_end86, nop
	.type	atomic_min_32_relaxed,@function
atomic_min_32_relaxed:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB86_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovlel	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB86_1
	retq
.Lfunc_end86:
	.size	atomic_min_32_relaxed, .Lfunc_end86-atomic_min_32_relaxed
	.cfi_endproc

	.section	.text.atomic_min_32_release,"ax",@progbits
	.globl	atomic_min_32_release
	.prefalign	4, .Lfunc_end87, nop
	.type	atomic_min_32_release,@function
atomic_min_32_release:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB87_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovlel	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB87_1
	retq
.Lfunc_end87:
	.size	atomic_min_32_release, .Lfunc_end87-atomic_min_32_release
	.cfi_endproc

	.section	.text.atomic_min_32_seqcst,"ax",@progbits
	.globl	atomic_min_32_seqcst
	.prefalign	4, .Lfunc_end88, nop
	.type	atomic_min_32_seqcst,@function
atomic_min_32_seqcst:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB88_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovlel	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB88_1
	retq
.Lfunc_end88:
	.size	atomic_min_32_seqcst, .Lfunc_end88-atomic_min_32_seqcst
	.cfi_endproc

	.section	.text.atomic_min_64_acqrel,"ax",@progbits
	.globl	atomic_min_64_acqrel
	.prefalign	4, .Lfunc_end89, nop
	.type	atomic_min_64_acqrel,@function
atomic_min_64_acqrel:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB89_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovleq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB89_1
	retq
.Lfunc_end89:
	.size	atomic_min_64_acqrel, .Lfunc_end89-atomic_min_64_acqrel
	.cfi_endproc

	.section	.text.atomic_min_64_acquire,"ax",@progbits
	.globl	atomic_min_64_acquire
	.prefalign	4, .Lfunc_end90, nop
	.type	atomic_min_64_acquire,@function
atomic_min_64_acquire:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB90_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovleq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB90_1
	retq
.Lfunc_end90:
	.size	atomic_min_64_acquire, .Lfunc_end90-atomic_min_64_acquire
	.cfi_endproc

	.section	.text.atomic_min_64_relaxed,"ax",@progbits
	.globl	atomic_min_64_relaxed
	.prefalign	4, .Lfunc_end91, nop
	.type	atomic_min_64_relaxed,@function
atomic_min_64_relaxed:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB91_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovleq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB91_1
	retq
.Lfunc_end91:
	.size	atomic_min_64_relaxed, .Lfunc_end91-atomic_min_64_relaxed
	.cfi_endproc

	.section	.text.atomic_min_64_release,"ax",@progbits
	.globl	atomic_min_64_release
	.prefalign	4, .Lfunc_end92, nop
	.type	atomic_min_64_release,@function
atomic_min_64_release:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB92_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovleq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB92_1
	retq
.Lfunc_end92:
	.size	atomic_min_64_release, .Lfunc_end92-atomic_min_64_release
	.cfi_endproc

	.section	.text.atomic_min_64_seqcst,"ax",@progbits
	.globl	atomic_min_64_seqcst
	.prefalign	4, .Lfunc_end93, nop
	.type	atomic_min_64_seqcst,@function
atomic_min_64_seqcst:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB93_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovleq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB93_1
	retq
.Lfunc_end93:
	.size	atomic_min_64_seqcst, .Lfunc_end93-atomic_min_64_seqcst
	.cfi_endproc

	.section	.text.atomic_min_8_acqrel,"ax",@progbits
	.globl	atomic_min_8_acqrel
	.prefalign	4, .Lfunc_end94, nop
	.type	atomic_min_8_acqrel,@function
atomic_min_8_acqrel:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB94_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovlel	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB94_1
	retq
.Lfunc_end94:
	.size	atomic_min_8_acqrel, .Lfunc_end94-atomic_min_8_acqrel
	.cfi_endproc

	.section	.text.atomic_min_8_acquire,"ax",@progbits
	.globl	atomic_min_8_acquire
	.prefalign	4, .Lfunc_end95, nop
	.type	atomic_min_8_acquire,@function
atomic_min_8_acquire:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB95_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovlel	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB95_1
	retq
.Lfunc_end95:
	.size	atomic_min_8_acquire, .Lfunc_end95-atomic_min_8_acquire
	.cfi_endproc

	.section	.text.atomic_min_8_relaxed,"ax",@progbits
	.globl	atomic_min_8_relaxed
	.prefalign	4, .Lfunc_end96, nop
	.type	atomic_min_8_relaxed,@function
atomic_min_8_relaxed:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB96_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovlel	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB96_1
	retq
.Lfunc_end96:
	.size	atomic_min_8_relaxed, .Lfunc_end96-atomic_min_8_relaxed
	.cfi_endproc

	.section	.text.atomic_min_8_release,"ax",@progbits
	.globl	atomic_min_8_release
	.prefalign	4, .Lfunc_end97, nop
	.type	atomic_min_8_release,@function
atomic_min_8_release:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB97_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovlel	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB97_1
	retq
.Lfunc_end97:
	.size	atomic_min_8_release, .Lfunc_end97-atomic_min_8_release
	.cfi_endproc

	.section	.text.atomic_min_8_seqcst,"ax",@progbits
	.globl	atomic_min_8_seqcst
	.prefalign	4, .Lfunc_end98, nop
	.type	atomic_min_8_seqcst,@function
atomic_min_8_seqcst:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB98_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovlel	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB98_1
	retq
.Lfunc_end98:
	.size	atomic_min_8_seqcst, .Lfunc_end98-atomic_min_8_seqcst
	.cfi_endproc

	.section	.text.atomic_nand_128_acqrel,"ax",@progbits
	.globl	atomic_nand_128_acqrel
	.prefalign	4, .Lfunc_end99, nop
	.type	atomic_nand_128_acqrel,@function
atomic_nand_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB99_1:
	movq	%rdx, %rcx
	andq	%r8, %rcx
	movq	%rax, %rbx
	andq	%rsi, %rbx
	notq	%rbx
	notq	%rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB99_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end99:
	.size	atomic_nand_128_acqrel, .Lfunc_end99-atomic_nand_128_acqrel
	.cfi_endproc

	.section	.text.atomic_nand_128_acquire,"ax",@progbits
	.globl	atomic_nand_128_acquire
	.prefalign	4, .Lfunc_end100, nop
	.type	atomic_nand_128_acquire,@function
atomic_nand_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB100_1:
	movq	%rdx, %rcx
	andq	%r8, %rcx
	movq	%rax, %rbx
	andq	%rsi, %rbx
	notq	%rbx
	notq	%rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB100_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end100:
	.size	atomic_nand_128_acquire, .Lfunc_end100-atomic_nand_128_acquire
	.cfi_endproc

	.section	.text.atomic_nand_128_relaxed,"ax",@progbits
	.globl	atomic_nand_128_relaxed
	.prefalign	4, .Lfunc_end101, nop
	.type	atomic_nand_128_relaxed,@function
atomic_nand_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB101_1:
	movq	%rdx, %rcx
	andq	%r8, %rcx
	movq	%rax, %rbx
	andq	%rsi, %rbx
	notq	%rbx
	notq	%rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB101_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end101:
	.size	atomic_nand_128_relaxed, .Lfunc_end101-atomic_nand_128_relaxed
	.cfi_endproc

	.section	.text.atomic_nand_128_release,"ax",@progbits
	.globl	atomic_nand_128_release
	.prefalign	4, .Lfunc_end102, nop
	.type	atomic_nand_128_release,@function
atomic_nand_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB102_1:
	movq	%rdx, %rcx
	andq	%r8, %rcx
	movq	%rax, %rbx
	andq	%rsi, %rbx
	notq	%rbx
	notq	%rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB102_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end102:
	.size	atomic_nand_128_release, .Lfunc_end102-atomic_nand_128_release
	.cfi_endproc

	.section	.text.atomic_nand_128_seqcst,"ax",@progbits
	.globl	atomic_nand_128_seqcst
	.prefalign	4, .Lfunc_end103, nop
	.type	atomic_nand_128_seqcst,@function
atomic_nand_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB103_1:
	movq	%rdx, %rcx
	andq	%r8, %rcx
	movq	%rax, %rbx
	andq	%rsi, %rbx
	notq	%rbx
	notq	%rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB103_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end103:
	.size	atomic_nand_128_seqcst, .Lfunc_end103-atomic_nand_128_seqcst
	.cfi_endproc

	.section	.text.atomic_nand_16_acqrel,"ax",@progbits
	.globl	atomic_nand_16_acqrel
	.prefalign	4, .Lfunc_end104, nop
	.type	atomic_nand_16_acqrel,@function
atomic_nand_16_acqrel:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB104_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	notl	%ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB104_1
	retq
.Lfunc_end104:
	.size	atomic_nand_16_acqrel, .Lfunc_end104-atomic_nand_16_acqrel
	.cfi_endproc

	.section	.text.atomic_nand_16_acquire,"ax",@progbits
	.globl	atomic_nand_16_acquire
	.prefalign	4, .Lfunc_end105, nop
	.type	atomic_nand_16_acquire,@function
atomic_nand_16_acquire:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB105_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	notl	%ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB105_1
	retq
.Lfunc_end105:
	.size	atomic_nand_16_acquire, .Lfunc_end105-atomic_nand_16_acquire
	.cfi_endproc

	.section	.text.atomic_nand_16_relaxed,"ax",@progbits
	.globl	atomic_nand_16_relaxed
	.prefalign	4, .Lfunc_end106, nop
	.type	atomic_nand_16_relaxed,@function
atomic_nand_16_relaxed:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB106_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	notl	%ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB106_1
	retq
.Lfunc_end106:
	.size	atomic_nand_16_relaxed, .Lfunc_end106-atomic_nand_16_relaxed
	.cfi_endproc

	.section	.text.atomic_nand_16_release,"ax",@progbits
	.globl	atomic_nand_16_release
	.prefalign	4, .Lfunc_end107, nop
	.type	atomic_nand_16_release,@function
atomic_nand_16_release:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB107_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	notl	%ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB107_1
	retq
.Lfunc_end107:
	.size	atomic_nand_16_release, .Lfunc_end107-atomic_nand_16_release
	.cfi_endproc

	.section	.text.atomic_nand_16_seqcst,"ax",@progbits
	.globl	atomic_nand_16_seqcst
	.prefalign	4, .Lfunc_end108, nop
	.type	atomic_nand_16_seqcst,@function
atomic_nand_16_seqcst:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB108_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	notl	%ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB108_1
	retq
.Lfunc_end108:
	.size	atomic_nand_16_seqcst, .Lfunc_end108-atomic_nand_16_seqcst
	.cfi_endproc

	.section	.text.atomic_nand_32_acqrel,"ax",@progbits
	.globl	atomic_nand_32_acqrel
	.prefalign	4, .Lfunc_end109, nop
	.type	atomic_nand_32_acqrel,@function
atomic_nand_32_acqrel:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB109_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	notl	%ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB109_1
	retq
.Lfunc_end109:
	.size	atomic_nand_32_acqrel, .Lfunc_end109-atomic_nand_32_acqrel
	.cfi_endproc

	.section	.text.atomic_nand_32_acquire,"ax",@progbits
	.globl	atomic_nand_32_acquire
	.prefalign	4, .Lfunc_end110, nop
	.type	atomic_nand_32_acquire,@function
atomic_nand_32_acquire:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB110_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	notl	%ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB110_1
	retq
.Lfunc_end110:
	.size	atomic_nand_32_acquire, .Lfunc_end110-atomic_nand_32_acquire
	.cfi_endproc

	.section	.text.atomic_nand_32_relaxed,"ax",@progbits
	.globl	atomic_nand_32_relaxed
	.prefalign	4, .Lfunc_end111, nop
	.type	atomic_nand_32_relaxed,@function
atomic_nand_32_relaxed:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB111_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	notl	%ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB111_1
	retq
.Lfunc_end111:
	.size	atomic_nand_32_relaxed, .Lfunc_end111-atomic_nand_32_relaxed
	.cfi_endproc

	.section	.text.atomic_nand_32_release,"ax",@progbits
	.globl	atomic_nand_32_release
	.prefalign	4, .Lfunc_end112, nop
	.type	atomic_nand_32_release,@function
atomic_nand_32_release:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB112_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	notl	%ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB112_1
	retq
.Lfunc_end112:
	.size	atomic_nand_32_release, .Lfunc_end112-atomic_nand_32_release
	.cfi_endproc

	.section	.text.atomic_nand_32_seqcst,"ax",@progbits
	.globl	atomic_nand_32_seqcst
	.prefalign	4, .Lfunc_end113, nop
	.type	atomic_nand_32_seqcst,@function
atomic_nand_32_seqcst:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB113_1:
	movl	%eax, %ecx
	andl	%esi, %ecx
	notl	%ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB113_1
	retq
.Lfunc_end113:
	.size	atomic_nand_32_seqcst, .Lfunc_end113-atomic_nand_32_seqcst
	.cfi_endproc

	.section	.text.atomic_nand_64_acqrel,"ax",@progbits
	.globl	atomic_nand_64_acqrel
	.prefalign	4, .Lfunc_end114, nop
	.type	atomic_nand_64_acqrel,@function
atomic_nand_64_acqrel:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB114_1:
	movq	%rax, %rcx
	andq	%rsi, %rcx
	notq	%rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB114_1
	retq
.Lfunc_end114:
	.size	atomic_nand_64_acqrel, .Lfunc_end114-atomic_nand_64_acqrel
	.cfi_endproc

	.section	.text.atomic_nand_64_acquire,"ax",@progbits
	.globl	atomic_nand_64_acquire
	.prefalign	4, .Lfunc_end115, nop
	.type	atomic_nand_64_acquire,@function
atomic_nand_64_acquire:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB115_1:
	movq	%rax, %rcx
	andq	%rsi, %rcx
	notq	%rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB115_1
	retq
.Lfunc_end115:
	.size	atomic_nand_64_acquire, .Lfunc_end115-atomic_nand_64_acquire
	.cfi_endproc

	.section	.text.atomic_nand_64_relaxed,"ax",@progbits
	.globl	atomic_nand_64_relaxed
	.prefalign	4, .Lfunc_end116, nop
	.type	atomic_nand_64_relaxed,@function
atomic_nand_64_relaxed:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB116_1:
	movq	%rax, %rcx
	andq	%rsi, %rcx
	notq	%rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB116_1
	retq
.Lfunc_end116:
	.size	atomic_nand_64_relaxed, .Lfunc_end116-atomic_nand_64_relaxed
	.cfi_endproc

	.section	.text.atomic_nand_64_release,"ax",@progbits
	.globl	atomic_nand_64_release
	.prefalign	4, .Lfunc_end117, nop
	.type	atomic_nand_64_release,@function
atomic_nand_64_release:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB117_1:
	movq	%rax, %rcx
	andq	%rsi, %rcx
	notq	%rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB117_1
	retq
.Lfunc_end117:
	.size	atomic_nand_64_release, .Lfunc_end117-atomic_nand_64_release
	.cfi_endproc

	.section	.text.atomic_nand_64_seqcst,"ax",@progbits
	.globl	atomic_nand_64_seqcst
	.prefalign	4, .Lfunc_end118, nop
	.type	atomic_nand_64_seqcst,@function
atomic_nand_64_seqcst:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB118_1:
	movq	%rax, %rcx
	andq	%rsi, %rcx
	notq	%rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB118_1
	retq
.Lfunc_end118:
	.size	atomic_nand_64_seqcst, .Lfunc_end118-atomic_nand_64_seqcst
	.cfi_endproc

	.section	.text.atomic_nand_8_acqrel,"ax",@progbits
	.globl	atomic_nand_8_acqrel
	.prefalign	4, .Lfunc_end119, nop
	.type	atomic_nand_8_acqrel,@function
atomic_nand_8_acqrel:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB119_1:
	movl	%eax, %ecx
	andb	%sil, %cl
	notb	%cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB119_1
	retq
.Lfunc_end119:
	.size	atomic_nand_8_acqrel, .Lfunc_end119-atomic_nand_8_acqrel
	.cfi_endproc

	.section	.text.atomic_nand_8_acquire,"ax",@progbits
	.globl	atomic_nand_8_acquire
	.prefalign	4, .Lfunc_end120, nop
	.type	atomic_nand_8_acquire,@function
atomic_nand_8_acquire:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB120_1:
	movl	%eax, %ecx
	andb	%sil, %cl
	notb	%cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB120_1
	retq
.Lfunc_end120:
	.size	atomic_nand_8_acquire, .Lfunc_end120-atomic_nand_8_acquire
	.cfi_endproc

	.section	.text.atomic_nand_8_relaxed,"ax",@progbits
	.globl	atomic_nand_8_relaxed
	.prefalign	4, .Lfunc_end121, nop
	.type	atomic_nand_8_relaxed,@function
atomic_nand_8_relaxed:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB121_1:
	movl	%eax, %ecx
	andb	%sil, %cl
	notb	%cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB121_1
	retq
.Lfunc_end121:
	.size	atomic_nand_8_relaxed, .Lfunc_end121-atomic_nand_8_relaxed
	.cfi_endproc

	.section	.text.atomic_nand_8_release,"ax",@progbits
	.globl	atomic_nand_8_release
	.prefalign	4, .Lfunc_end122, nop
	.type	atomic_nand_8_release,@function
atomic_nand_8_release:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB122_1:
	movl	%eax, %ecx
	andb	%sil, %cl
	notb	%cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB122_1
	retq
.Lfunc_end122:
	.size	atomic_nand_8_release, .Lfunc_end122-atomic_nand_8_release
	.cfi_endproc

	.section	.text.atomic_nand_8_seqcst,"ax",@progbits
	.globl	atomic_nand_8_seqcst
	.prefalign	4, .Lfunc_end123, nop
	.type	atomic_nand_8_seqcst,@function
atomic_nand_8_seqcst:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB123_1:
	movl	%eax, %ecx
	andb	%sil, %cl
	notb	%cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB123_1
	retq
.Lfunc_end123:
	.size	atomic_nand_8_seqcst, .Lfunc_end123-atomic_nand_8_seqcst
	.cfi_endproc

	.section	.text.atomic_or_128_acqrel,"ax",@progbits
	.globl	atomic_or_128_acqrel
	.prefalign	4, .Lfunc_end124, nop
	.type	atomic_or_128_acqrel,@function
atomic_or_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB124_1:
	movq	%rax, %rbx
	orq	%rsi, %rbx
	movq	%rdx, %rcx
	orq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB124_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end124:
	.size	atomic_or_128_acqrel, .Lfunc_end124-atomic_or_128_acqrel
	.cfi_endproc

	.section	.text.atomic_or_128_acquire,"ax",@progbits
	.globl	atomic_or_128_acquire
	.prefalign	4, .Lfunc_end125, nop
	.type	atomic_or_128_acquire,@function
atomic_or_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB125_1:
	movq	%rax, %rbx
	orq	%rsi, %rbx
	movq	%rdx, %rcx
	orq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB125_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end125:
	.size	atomic_or_128_acquire, .Lfunc_end125-atomic_or_128_acquire
	.cfi_endproc

	.section	.text.atomic_or_128_relaxed,"ax",@progbits
	.globl	atomic_or_128_relaxed
	.prefalign	4, .Lfunc_end126, nop
	.type	atomic_or_128_relaxed,@function
atomic_or_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB126_1:
	movq	%rax, %rbx
	orq	%rsi, %rbx
	movq	%rdx, %rcx
	orq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB126_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end126:
	.size	atomic_or_128_relaxed, .Lfunc_end126-atomic_or_128_relaxed
	.cfi_endproc

	.section	.text.atomic_or_128_release,"ax",@progbits
	.globl	atomic_or_128_release
	.prefalign	4, .Lfunc_end127, nop
	.type	atomic_or_128_release,@function
atomic_or_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB127_1:
	movq	%rax, %rbx
	orq	%rsi, %rbx
	movq	%rdx, %rcx
	orq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB127_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end127:
	.size	atomic_or_128_release, .Lfunc_end127-atomic_or_128_release
	.cfi_endproc

	.section	.text.atomic_or_128_seqcst,"ax",@progbits
	.globl	atomic_or_128_seqcst
	.prefalign	4, .Lfunc_end128, nop
	.type	atomic_or_128_seqcst,@function
atomic_or_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB128_1:
	movq	%rax, %rbx
	orq	%rsi, %rbx
	movq	%rdx, %rcx
	orq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB128_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end128:
	.size	atomic_or_128_seqcst, .Lfunc_end128-atomic_or_128_seqcst
	.cfi_endproc

	.section	.text.atomic_or_16_acqrel,"ax",@progbits
	.globl	atomic_or_16_acqrel
	.prefalign	4, .Lfunc_end129, nop
	.type	atomic_or_16_acqrel,@function
atomic_or_16_acqrel:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB129_1:
	movl	%eax, %ecx
	orl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB129_1
	retq
.Lfunc_end129:
	.size	atomic_or_16_acqrel, .Lfunc_end129-atomic_or_16_acqrel
	.cfi_endproc

	.section	.text.atomic_or_16_acquire,"ax",@progbits
	.globl	atomic_or_16_acquire
	.prefalign	4, .Lfunc_end130, nop
	.type	atomic_or_16_acquire,@function
atomic_or_16_acquire:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB130_1:
	movl	%eax, %ecx
	orl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB130_1
	retq
.Lfunc_end130:
	.size	atomic_or_16_acquire, .Lfunc_end130-atomic_or_16_acquire
	.cfi_endproc

	.section	.text.atomic_or_16_relaxed,"ax",@progbits
	.globl	atomic_or_16_relaxed
	.prefalign	4, .Lfunc_end131, nop
	.type	atomic_or_16_relaxed,@function
atomic_or_16_relaxed:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB131_1:
	movl	%eax, %ecx
	orl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB131_1
	retq
.Lfunc_end131:
	.size	atomic_or_16_relaxed, .Lfunc_end131-atomic_or_16_relaxed
	.cfi_endproc

	.section	.text.atomic_or_16_release,"ax",@progbits
	.globl	atomic_or_16_release
	.prefalign	4, .Lfunc_end132, nop
	.type	atomic_or_16_release,@function
atomic_or_16_release:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB132_1:
	movl	%eax, %ecx
	orl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB132_1
	retq
.Lfunc_end132:
	.size	atomic_or_16_release, .Lfunc_end132-atomic_or_16_release
	.cfi_endproc

	.section	.text.atomic_or_16_seqcst,"ax",@progbits
	.globl	atomic_or_16_seqcst
	.prefalign	4, .Lfunc_end133, nop
	.type	atomic_or_16_seqcst,@function
atomic_or_16_seqcst:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB133_1:
	movl	%eax, %ecx
	orl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB133_1
	retq
.Lfunc_end133:
	.size	atomic_or_16_seqcst, .Lfunc_end133-atomic_or_16_seqcst
	.cfi_endproc

	.section	.text.atomic_or_32_acqrel,"ax",@progbits
	.globl	atomic_or_32_acqrel
	.prefalign	4, .Lfunc_end134, nop
	.type	atomic_or_32_acqrel,@function
atomic_or_32_acqrel:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB134_1:
	movl	%eax, %ecx
	orl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB134_1
	retq
.Lfunc_end134:
	.size	atomic_or_32_acqrel, .Lfunc_end134-atomic_or_32_acqrel
	.cfi_endproc

	.section	.text.atomic_or_32_acquire,"ax",@progbits
	.globl	atomic_or_32_acquire
	.prefalign	4, .Lfunc_end135, nop
	.type	atomic_or_32_acquire,@function
atomic_or_32_acquire:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB135_1:
	movl	%eax, %ecx
	orl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB135_1
	retq
.Lfunc_end135:
	.size	atomic_or_32_acquire, .Lfunc_end135-atomic_or_32_acquire
	.cfi_endproc

	.section	.text.atomic_or_32_relaxed,"ax",@progbits
	.globl	atomic_or_32_relaxed
	.prefalign	4, .Lfunc_end136, nop
	.type	atomic_or_32_relaxed,@function
atomic_or_32_relaxed:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB136_1:
	movl	%eax, %ecx
	orl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB136_1
	retq
.Lfunc_end136:
	.size	atomic_or_32_relaxed, .Lfunc_end136-atomic_or_32_relaxed
	.cfi_endproc

	.section	.text.atomic_or_32_release,"ax",@progbits
	.globl	atomic_or_32_release
	.prefalign	4, .Lfunc_end137, nop
	.type	atomic_or_32_release,@function
atomic_or_32_release:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB137_1:
	movl	%eax, %ecx
	orl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB137_1
	retq
.Lfunc_end137:
	.size	atomic_or_32_release, .Lfunc_end137-atomic_or_32_release
	.cfi_endproc

	.section	.text.atomic_or_32_seqcst,"ax",@progbits
	.globl	atomic_or_32_seqcst
	.prefalign	4, .Lfunc_end138, nop
	.type	atomic_or_32_seqcst,@function
atomic_or_32_seqcst:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB138_1:
	movl	%eax, %ecx
	orl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB138_1
	retq
.Lfunc_end138:
	.size	atomic_or_32_seqcst, .Lfunc_end138-atomic_or_32_seqcst
	.cfi_endproc

	.section	.text.atomic_or_64_acqrel,"ax",@progbits
	.globl	atomic_or_64_acqrel
	.prefalign	4, .Lfunc_end139, nop
	.type	atomic_or_64_acqrel,@function
atomic_or_64_acqrel:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB139_1:
	movq	%rax, %rcx
	orq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB139_1
	retq
.Lfunc_end139:
	.size	atomic_or_64_acqrel, .Lfunc_end139-atomic_or_64_acqrel
	.cfi_endproc

	.section	.text.atomic_or_64_acquire,"ax",@progbits
	.globl	atomic_or_64_acquire
	.prefalign	4, .Lfunc_end140, nop
	.type	atomic_or_64_acquire,@function
atomic_or_64_acquire:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB140_1:
	movq	%rax, %rcx
	orq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB140_1
	retq
.Lfunc_end140:
	.size	atomic_or_64_acquire, .Lfunc_end140-atomic_or_64_acquire
	.cfi_endproc

	.section	.text.atomic_or_64_relaxed,"ax",@progbits
	.globl	atomic_or_64_relaxed
	.prefalign	4, .Lfunc_end141, nop
	.type	atomic_or_64_relaxed,@function
atomic_or_64_relaxed:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB141_1:
	movq	%rax, %rcx
	orq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB141_1
	retq
.Lfunc_end141:
	.size	atomic_or_64_relaxed, .Lfunc_end141-atomic_or_64_relaxed
	.cfi_endproc

	.section	.text.atomic_or_64_release,"ax",@progbits
	.globl	atomic_or_64_release
	.prefalign	4, .Lfunc_end142, nop
	.type	atomic_or_64_release,@function
atomic_or_64_release:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB142_1:
	movq	%rax, %rcx
	orq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB142_1
	retq
.Lfunc_end142:
	.size	atomic_or_64_release, .Lfunc_end142-atomic_or_64_release
	.cfi_endproc

	.section	.text.atomic_or_64_seqcst,"ax",@progbits
	.globl	atomic_or_64_seqcst
	.prefalign	4, .Lfunc_end143, nop
	.type	atomic_or_64_seqcst,@function
atomic_or_64_seqcst:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB143_1:
	movq	%rax, %rcx
	orq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB143_1
	retq
.Lfunc_end143:
	.size	atomic_or_64_seqcst, .Lfunc_end143-atomic_or_64_seqcst
	.cfi_endproc

	.section	.text.atomic_or_8_acqrel,"ax",@progbits
	.globl	atomic_or_8_acqrel
	.prefalign	4, .Lfunc_end144, nop
	.type	atomic_or_8_acqrel,@function
atomic_or_8_acqrel:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB144_1:
	movl	%eax, %ecx
	orb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB144_1
	retq
.Lfunc_end144:
	.size	atomic_or_8_acqrel, .Lfunc_end144-atomic_or_8_acqrel
	.cfi_endproc

	.section	.text.atomic_or_8_acquire,"ax",@progbits
	.globl	atomic_or_8_acquire
	.prefalign	4, .Lfunc_end145, nop
	.type	atomic_or_8_acquire,@function
atomic_or_8_acquire:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB145_1:
	movl	%eax, %ecx
	orb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB145_1
	retq
.Lfunc_end145:
	.size	atomic_or_8_acquire, .Lfunc_end145-atomic_or_8_acquire
	.cfi_endproc

	.section	.text.atomic_or_8_relaxed,"ax",@progbits
	.globl	atomic_or_8_relaxed
	.prefalign	4, .Lfunc_end146, nop
	.type	atomic_or_8_relaxed,@function
atomic_or_8_relaxed:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB146_1:
	movl	%eax, %ecx
	orb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB146_1
	retq
.Lfunc_end146:
	.size	atomic_or_8_relaxed, .Lfunc_end146-atomic_or_8_relaxed
	.cfi_endproc

	.section	.text.atomic_or_8_release,"ax",@progbits
	.globl	atomic_or_8_release
	.prefalign	4, .Lfunc_end147, nop
	.type	atomic_or_8_release,@function
atomic_or_8_release:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB147_1:
	movl	%eax, %ecx
	orb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB147_1
	retq
.Lfunc_end147:
	.size	atomic_or_8_release, .Lfunc_end147-atomic_or_8_release
	.cfi_endproc

	.section	.text.atomic_or_8_seqcst,"ax",@progbits
	.globl	atomic_or_8_seqcst
	.prefalign	4, .Lfunc_end148, nop
	.type	atomic_or_8_seqcst,@function
atomic_or_8_seqcst:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB148_1:
	movl	%eax, %ecx
	orb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB148_1
	retq
.Lfunc_end148:
	.size	atomic_or_8_seqcst, .Lfunc_end148-atomic_or_8_seqcst
	.cfi_endproc

	.section	.text.atomic_store_128_relaxed,"ax",@progbits
	.globl	atomic_store_128_relaxed
	.prefalign	4, .Lfunc_end149, nop
	.type	atomic_store_128_relaxed,@function
atomic_store_128_relaxed:
	.cfi_startproc
	vmovq	%rdx, %xmm0
	vmovq	%rsi, %xmm1
	vpunpcklqdq	%xmm0, %xmm1, %xmm0
	vmovdqa	%xmm0, (%rdi)
	retq
.Lfunc_end149:
	.size	atomic_store_128_relaxed, .Lfunc_end149-atomic_store_128_relaxed
	.cfi_endproc

	.section	.text.atomic_store_128_release,"ax",@progbits
	.globl	atomic_store_128_release
	.prefalign	4, .Lfunc_end150, nop
	.type	atomic_store_128_release,@function
atomic_store_128_release:
	.cfi_startproc
	vmovq	%rdx, %xmm0
	vmovq	%rsi, %xmm1
	vpunpcklqdq	%xmm0, %xmm1, %xmm0
	vmovdqa	%xmm0, (%rdi)
	retq
.Lfunc_end150:
	.size	atomic_store_128_release, .Lfunc_end150-atomic_store_128_release
	.cfi_endproc

	.section	.text.atomic_store_128_seqcst,"ax",@progbits
	.globl	atomic_store_128_seqcst
	.prefalign	4, .Lfunc_end151, nop
	.type	atomic_store_128_seqcst,@function
atomic_store_128_seqcst:
	.cfi_startproc
	vmovq	%rdx, %xmm0
	vmovq	%rsi, %xmm1
	vpunpcklqdq	%xmm0, %xmm1, %xmm0
	vmovdqa	%xmm0, (%rdi)
	lock		orl	$0, -64(%rsp)
	retq
.Lfunc_end151:
	.size	atomic_store_128_seqcst, .Lfunc_end151-atomic_store_128_seqcst
	.cfi_endproc

	.section	.text.atomic_store_16_relaxed,"ax",@progbits
	.globl	atomic_store_16_relaxed
	.prefalign	4, .Lfunc_end152, nop
	.type	atomic_store_16_relaxed,@function
atomic_store_16_relaxed:
	.cfi_startproc
	movw	%si, (%rdi)
	retq
.Lfunc_end152:
	.size	atomic_store_16_relaxed, .Lfunc_end152-atomic_store_16_relaxed
	.cfi_endproc

	.section	.text.atomic_store_16_release,"ax",@progbits
	.globl	atomic_store_16_release
	.prefalign	4, .Lfunc_end153, nop
	.type	atomic_store_16_release,@function
atomic_store_16_release:
	.cfi_startproc
	movw	%si, (%rdi)
	retq
.Lfunc_end153:
	.size	atomic_store_16_release, .Lfunc_end153-atomic_store_16_release
	.cfi_endproc

	.section	.text.atomic_store_16_seqcst,"ax",@progbits
	.globl	atomic_store_16_seqcst
	.prefalign	4, .Lfunc_end154, nop
	.type	atomic_store_16_seqcst,@function
atomic_store_16_seqcst:
	.cfi_startproc
	xchgw	%si, (%rdi)
	retq
.Lfunc_end154:
	.size	atomic_store_16_seqcst, .Lfunc_end154-atomic_store_16_seqcst
	.cfi_endproc

	.section	.text.atomic_store_32_relaxed,"ax",@progbits
	.globl	atomic_store_32_relaxed
	.prefalign	4, .Lfunc_end155, nop
	.type	atomic_store_32_relaxed,@function
atomic_store_32_relaxed:
	.cfi_startproc
	movl	%esi, (%rdi)
	retq
.Lfunc_end155:
	.size	atomic_store_32_relaxed, .Lfunc_end155-atomic_store_32_relaxed
	.cfi_endproc

	.section	.text.atomic_store_32_release,"ax",@progbits
	.globl	atomic_store_32_release
	.prefalign	4, .Lfunc_end156, nop
	.type	atomic_store_32_release,@function
atomic_store_32_release:
	.cfi_startproc
	movl	%esi, (%rdi)
	retq
.Lfunc_end156:
	.size	atomic_store_32_release, .Lfunc_end156-atomic_store_32_release
	.cfi_endproc

	.section	.text.atomic_store_32_seqcst,"ax",@progbits
	.globl	atomic_store_32_seqcst
	.prefalign	4, .Lfunc_end157, nop
	.type	atomic_store_32_seqcst,@function
atomic_store_32_seqcst:
	.cfi_startproc
	xchgl	%esi, (%rdi)
	retq
.Lfunc_end157:
	.size	atomic_store_32_seqcst, .Lfunc_end157-atomic_store_32_seqcst
	.cfi_endproc

	.section	.text.atomic_store_64_relaxed,"ax",@progbits
	.globl	atomic_store_64_relaxed
	.prefalign	4, .Lfunc_end158, nop
	.type	atomic_store_64_relaxed,@function
atomic_store_64_relaxed:
	.cfi_startproc
	movq	%rsi, (%rdi)
	retq
.Lfunc_end158:
	.size	atomic_store_64_relaxed, .Lfunc_end158-atomic_store_64_relaxed
	.cfi_endproc

	.section	.text.atomic_store_64_release,"ax",@progbits
	.globl	atomic_store_64_release
	.prefalign	4, .Lfunc_end159, nop
	.type	atomic_store_64_release,@function
atomic_store_64_release:
	.cfi_startproc
	movq	%rsi, (%rdi)
	retq
.Lfunc_end159:
	.size	atomic_store_64_release, .Lfunc_end159-atomic_store_64_release
	.cfi_endproc

	.section	.text.atomic_store_64_seqcst,"ax",@progbits
	.globl	atomic_store_64_seqcst
	.prefalign	4, .Lfunc_end160, nop
	.type	atomic_store_64_seqcst,@function
atomic_store_64_seqcst:
	.cfi_startproc
	xchgq	%rsi, (%rdi)
	retq
.Lfunc_end160:
	.size	atomic_store_64_seqcst, .Lfunc_end160-atomic_store_64_seqcst
	.cfi_endproc

	.section	.text.atomic_store_8_relaxed,"ax",@progbits
	.globl	atomic_store_8_relaxed
	.prefalign	4, .Lfunc_end161, nop
	.type	atomic_store_8_relaxed,@function
atomic_store_8_relaxed:
	.cfi_startproc
	movb	%sil, (%rdi)
	retq
.Lfunc_end161:
	.size	atomic_store_8_relaxed, .Lfunc_end161-atomic_store_8_relaxed
	.cfi_endproc

	.section	.text.atomic_store_8_release,"ax",@progbits
	.globl	atomic_store_8_release
	.prefalign	4, .Lfunc_end162, nop
	.type	atomic_store_8_release,@function
atomic_store_8_release:
	.cfi_startproc
	movb	%sil, (%rdi)
	retq
.Lfunc_end162:
	.size	atomic_store_8_release, .Lfunc_end162-atomic_store_8_release
	.cfi_endproc

	.section	.text.atomic_store_8_seqcst,"ax",@progbits
	.globl	atomic_store_8_seqcst
	.prefalign	4, .Lfunc_end163, nop
	.type	atomic_store_8_seqcst,@function
atomic_store_8_seqcst:
	.cfi_startproc
	xchgb	%sil, (%rdi)
	retq
.Lfunc_end163:
	.size	atomic_store_8_seqcst, .Lfunc_end163-atomic_store_8_seqcst
	.cfi_endproc

	.section	.text.atomic_umax_128_acqrel,"ax",@progbits
	.globl	atomic_umax_128_acqrel
	.prefalign	4, .Lfunc_end164, nop
	.type	atomic_umax_128_acqrel,@function
atomic_umax_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB164_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovbq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovbq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB164_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end164:
	.size	atomic_umax_128_acqrel, .Lfunc_end164-atomic_umax_128_acqrel
	.cfi_endproc

	.section	.text.atomic_umax_128_acquire,"ax",@progbits
	.globl	atomic_umax_128_acquire
	.prefalign	4, .Lfunc_end165, nop
	.type	atomic_umax_128_acquire,@function
atomic_umax_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB165_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovbq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovbq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB165_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end165:
	.size	atomic_umax_128_acquire, .Lfunc_end165-atomic_umax_128_acquire
	.cfi_endproc

	.section	.text.atomic_umax_128_relaxed,"ax",@progbits
	.globl	atomic_umax_128_relaxed
	.prefalign	4, .Lfunc_end166, nop
	.type	atomic_umax_128_relaxed,@function
atomic_umax_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB166_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovbq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovbq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB166_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end166:
	.size	atomic_umax_128_relaxed, .Lfunc_end166-atomic_umax_128_relaxed
	.cfi_endproc

	.section	.text.atomic_umax_128_release,"ax",@progbits
	.globl	atomic_umax_128_release
	.prefalign	4, .Lfunc_end167, nop
	.type	atomic_umax_128_release,@function
atomic_umax_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB167_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovbq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovbq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB167_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end167:
	.size	atomic_umax_128_release, .Lfunc_end167-atomic_umax_128_release
	.cfi_endproc

	.section	.text.atomic_umax_128_seqcst,"ax",@progbits
	.globl	atomic_umax_128_seqcst
	.prefalign	4, .Lfunc_end168, nop
	.type	atomic_umax_128_seqcst,@function
atomic_umax_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB168_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovbq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovbq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB168_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end168:
	.size	atomic_umax_128_seqcst, .Lfunc_end168-atomic_umax_128_seqcst
	.cfi_endproc

	.section	.text.atomic_umax_16_acqrel,"ax",@progbits
	.globl	atomic_umax_16_acqrel
	.prefalign	4, .Lfunc_end169, nop
	.type	atomic_umax_16_acqrel,@function
atomic_umax_16_acqrel:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB169_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmoval	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB169_1
	retq
.Lfunc_end169:
	.size	atomic_umax_16_acqrel, .Lfunc_end169-atomic_umax_16_acqrel
	.cfi_endproc

	.section	.text.atomic_umax_16_acquire,"ax",@progbits
	.globl	atomic_umax_16_acquire
	.prefalign	4, .Lfunc_end170, nop
	.type	atomic_umax_16_acquire,@function
atomic_umax_16_acquire:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB170_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmoval	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB170_1
	retq
.Lfunc_end170:
	.size	atomic_umax_16_acquire, .Lfunc_end170-atomic_umax_16_acquire
	.cfi_endproc

	.section	.text.atomic_umax_16_relaxed,"ax",@progbits
	.globl	atomic_umax_16_relaxed
	.prefalign	4, .Lfunc_end171, nop
	.type	atomic_umax_16_relaxed,@function
atomic_umax_16_relaxed:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB171_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmoval	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB171_1
	retq
.Lfunc_end171:
	.size	atomic_umax_16_relaxed, .Lfunc_end171-atomic_umax_16_relaxed
	.cfi_endproc

	.section	.text.atomic_umax_16_release,"ax",@progbits
	.globl	atomic_umax_16_release
	.prefalign	4, .Lfunc_end172, nop
	.type	atomic_umax_16_release,@function
atomic_umax_16_release:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB172_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmoval	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB172_1
	retq
.Lfunc_end172:
	.size	atomic_umax_16_release, .Lfunc_end172-atomic_umax_16_release
	.cfi_endproc

	.section	.text.atomic_umax_16_seqcst,"ax",@progbits
	.globl	atomic_umax_16_seqcst
	.prefalign	4, .Lfunc_end173, nop
	.type	atomic_umax_16_seqcst,@function
atomic_umax_16_seqcst:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB173_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmoval	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB173_1
	retq
.Lfunc_end173:
	.size	atomic_umax_16_seqcst, .Lfunc_end173-atomic_umax_16_seqcst
	.cfi_endproc

	.section	.text.atomic_umax_32_acqrel,"ax",@progbits
	.globl	atomic_umax_32_acqrel
	.prefalign	4, .Lfunc_end174, nop
	.type	atomic_umax_32_acqrel,@function
atomic_umax_32_acqrel:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB174_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmoval	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB174_1
	retq
.Lfunc_end174:
	.size	atomic_umax_32_acqrel, .Lfunc_end174-atomic_umax_32_acqrel
	.cfi_endproc

	.section	.text.atomic_umax_32_acquire,"ax",@progbits
	.globl	atomic_umax_32_acquire
	.prefalign	4, .Lfunc_end175, nop
	.type	atomic_umax_32_acquire,@function
atomic_umax_32_acquire:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB175_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmoval	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB175_1
	retq
.Lfunc_end175:
	.size	atomic_umax_32_acquire, .Lfunc_end175-atomic_umax_32_acquire
	.cfi_endproc

	.section	.text.atomic_umax_32_relaxed,"ax",@progbits
	.globl	atomic_umax_32_relaxed
	.prefalign	4, .Lfunc_end176, nop
	.type	atomic_umax_32_relaxed,@function
atomic_umax_32_relaxed:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB176_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmoval	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB176_1
	retq
.Lfunc_end176:
	.size	atomic_umax_32_relaxed, .Lfunc_end176-atomic_umax_32_relaxed
	.cfi_endproc

	.section	.text.atomic_umax_32_release,"ax",@progbits
	.globl	atomic_umax_32_release
	.prefalign	4, .Lfunc_end177, nop
	.type	atomic_umax_32_release,@function
atomic_umax_32_release:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB177_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmoval	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB177_1
	retq
.Lfunc_end177:
	.size	atomic_umax_32_release, .Lfunc_end177-atomic_umax_32_release
	.cfi_endproc

	.section	.text.atomic_umax_32_seqcst,"ax",@progbits
	.globl	atomic_umax_32_seqcst
	.prefalign	4, .Lfunc_end178, nop
	.type	atomic_umax_32_seqcst,@function
atomic_umax_32_seqcst:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB178_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmoval	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB178_1
	retq
.Lfunc_end178:
	.size	atomic_umax_32_seqcst, .Lfunc_end178-atomic_umax_32_seqcst
	.cfi_endproc

	.section	.text.atomic_umax_64_acqrel,"ax",@progbits
	.globl	atomic_umax_64_acqrel
	.prefalign	4, .Lfunc_end179, nop
	.type	atomic_umax_64_acqrel,@function
atomic_umax_64_acqrel:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB179_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovaq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB179_1
	retq
.Lfunc_end179:
	.size	atomic_umax_64_acqrel, .Lfunc_end179-atomic_umax_64_acqrel
	.cfi_endproc

	.section	.text.atomic_umax_64_acquire,"ax",@progbits
	.globl	atomic_umax_64_acquire
	.prefalign	4, .Lfunc_end180, nop
	.type	atomic_umax_64_acquire,@function
atomic_umax_64_acquire:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB180_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovaq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB180_1
	retq
.Lfunc_end180:
	.size	atomic_umax_64_acquire, .Lfunc_end180-atomic_umax_64_acquire
	.cfi_endproc

	.section	.text.atomic_umax_64_relaxed,"ax",@progbits
	.globl	atomic_umax_64_relaxed
	.prefalign	4, .Lfunc_end181, nop
	.type	atomic_umax_64_relaxed,@function
atomic_umax_64_relaxed:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB181_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovaq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB181_1
	retq
.Lfunc_end181:
	.size	atomic_umax_64_relaxed, .Lfunc_end181-atomic_umax_64_relaxed
	.cfi_endproc

	.section	.text.atomic_umax_64_release,"ax",@progbits
	.globl	atomic_umax_64_release
	.prefalign	4, .Lfunc_end182, nop
	.type	atomic_umax_64_release,@function
atomic_umax_64_release:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB182_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovaq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB182_1
	retq
.Lfunc_end182:
	.size	atomic_umax_64_release, .Lfunc_end182-atomic_umax_64_release
	.cfi_endproc

	.section	.text.atomic_umax_64_seqcst,"ax",@progbits
	.globl	atomic_umax_64_seqcst
	.prefalign	4, .Lfunc_end183, nop
	.type	atomic_umax_64_seqcst,@function
atomic_umax_64_seqcst:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB183_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovaq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB183_1
	retq
.Lfunc_end183:
	.size	atomic_umax_64_seqcst, .Lfunc_end183-atomic_umax_64_seqcst
	.cfi_endproc

	.section	.text.atomic_umax_8_acqrel,"ax",@progbits
	.globl	atomic_umax_8_acqrel
	.prefalign	4, .Lfunc_end184, nop
	.type	atomic_umax_8_acqrel,@function
atomic_umax_8_acqrel:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB184_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmoval	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB184_1
	retq
.Lfunc_end184:
	.size	atomic_umax_8_acqrel, .Lfunc_end184-atomic_umax_8_acqrel
	.cfi_endproc

	.section	.text.atomic_umax_8_acquire,"ax",@progbits
	.globl	atomic_umax_8_acquire
	.prefalign	4, .Lfunc_end185, nop
	.type	atomic_umax_8_acquire,@function
atomic_umax_8_acquire:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB185_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmoval	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB185_1
	retq
.Lfunc_end185:
	.size	atomic_umax_8_acquire, .Lfunc_end185-atomic_umax_8_acquire
	.cfi_endproc

	.section	.text.atomic_umax_8_relaxed,"ax",@progbits
	.globl	atomic_umax_8_relaxed
	.prefalign	4, .Lfunc_end186, nop
	.type	atomic_umax_8_relaxed,@function
atomic_umax_8_relaxed:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB186_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmoval	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB186_1
	retq
.Lfunc_end186:
	.size	atomic_umax_8_relaxed, .Lfunc_end186-atomic_umax_8_relaxed
	.cfi_endproc

	.section	.text.atomic_umax_8_release,"ax",@progbits
	.globl	atomic_umax_8_release
	.prefalign	4, .Lfunc_end187, nop
	.type	atomic_umax_8_release,@function
atomic_umax_8_release:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB187_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmoval	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB187_1
	retq
.Lfunc_end187:
	.size	atomic_umax_8_release, .Lfunc_end187-atomic_umax_8_release
	.cfi_endproc

	.section	.text.atomic_umax_8_seqcst,"ax",@progbits
	.globl	atomic_umax_8_seqcst
	.prefalign	4, .Lfunc_end188, nop
	.type	atomic_umax_8_seqcst,@function
atomic_umax_8_seqcst:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB188_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmoval	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB188_1
	retq
.Lfunc_end188:
	.size	atomic_umax_8_seqcst, .Lfunc_end188-atomic_umax_8_seqcst
	.cfi_endproc

	.section	.text.atomic_umin_128_acqrel,"ax",@progbits
	.globl	atomic_umin_128_acqrel
	.prefalign	4, .Lfunc_end189, nop
	.type	atomic_umin_128_acqrel,@function
atomic_umin_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB189_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovaeq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovaeq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB189_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end189:
	.size	atomic_umin_128_acqrel, .Lfunc_end189-atomic_umin_128_acqrel
	.cfi_endproc

	.section	.text.atomic_umin_128_acquire,"ax",@progbits
	.globl	atomic_umin_128_acquire
	.prefalign	4, .Lfunc_end190, nop
	.type	atomic_umin_128_acquire,@function
atomic_umin_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB190_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovaeq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovaeq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB190_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end190:
	.size	atomic_umin_128_acquire, .Lfunc_end190-atomic_umin_128_acquire
	.cfi_endproc

	.section	.text.atomic_umin_128_relaxed,"ax",@progbits
	.globl	atomic_umin_128_relaxed
	.prefalign	4, .Lfunc_end191, nop
	.type	atomic_umin_128_relaxed,@function
atomic_umin_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB191_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovaeq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovaeq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB191_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end191:
	.size	atomic_umin_128_relaxed, .Lfunc_end191-atomic_umin_128_relaxed
	.cfi_endproc

	.section	.text.atomic_umin_128_release,"ax",@progbits
	.globl	atomic_umin_128_release
	.prefalign	4, .Lfunc_end192, nop
	.type	atomic_umin_128_release,@function
atomic_umin_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB192_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovaeq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovaeq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB192_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end192:
	.size	atomic_umin_128_release, .Lfunc_end192-atomic_umin_128_release
	.cfi_endproc

	.section	.text.atomic_umin_128_seqcst,"ax",@progbits
	.globl	atomic_umin_128_seqcst
	.prefalign	4, .Lfunc_end193, nop
	.type	atomic_umin_128_seqcst,@function
atomic_umin_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB193_1:
	cmpq	%rax, %rsi
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovaeq	%rdx, %rcx
	movq	%rsi, %rbx
	cmovaeq	%rax, %rbx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB193_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end193:
	.size	atomic_umin_128_seqcst, .Lfunc_end193-atomic_umin_128_seqcst
	.cfi_endproc

	.section	.text.atomic_umin_16_acqrel,"ax",@progbits
	.globl	atomic_umin_16_acqrel
	.prefalign	4, .Lfunc_end194, nop
	.type	atomic_umin_16_acqrel,@function
atomic_umin_16_acqrel:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB194_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovbel	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB194_1
	retq
.Lfunc_end194:
	.size	atomic_umin_16_acqrel, .Lfunc_end194-atomic_umin_16_acqrel
	.cfi_endproc

	.section	.text.atomic_umin_16_acquire,"ax",@progbits
	.globl	atomic_umin_16_acquire
	.prefalign	4, .Lfunc_end195, nop
	.type	atomic_umin_16_acquire,@function
atomic_umin_16_acquire:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB195_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovbel	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB195_1
	retq
.Lfunc_end195:
	.size	atomic_umin_16_acquire, .Lfunc_end195-atomic_umin_16_acquire
	.cfi_endproc

	.section	.text.atomic_umin_16_relaxed,"ax",@progbits
	.globl	atomic_umin_16_relaxed
	.prefalign	4, .Lfunc_end196, nop
	.type	atomic_umin_16_relaxed,@function
atomic_umin_16_relaxed:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB196_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovbel	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB196_1
	retq
.Lfunc_end196:
	.size	atomic_umin_16_relaxed, .Lfunc_end196-atomic_umin_16_relaxed
	.cfi_endproc

	.section	.text.atomic_umin_16_release,"ax",@progbits
	.globl	atomic_umin_16_release
	.prefalign	4, .Lfunc_end197, nop
	.type	atomic_umin_16_release,@function
atomic_umin_16_release:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB197_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovbel	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB197_1
	retq
.Lfunc_end197:
	.size	atomic_umin_16_release, .Lfunc_end197-atomic_umin_16_release
	.cfi_endproc

	.section	.text.atomic_umin_16_seqcst,"ax",@progbits
	.globl	atomic_umin_16_seqcst
	.prefalign	4, .Lfunc_end198, nop
	.type	atomic_umin_16_seqcst,@function
atomic_umin_16_seqcst:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB198_1:
	cmpw	%si, %ax
	movl	%esi, %ecx
	cmovbel	%eax, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB198_1
	retq
.Lfunc_end198:
	.size	atomic_umin_16_seqcst, .Lfunc_end198-atomic_umin_16_seqcst
	.cfi_endproc

	.section	.text.atomic_umin_32_acqrel,"ax",@progbits
	.globl	atomic_umin_32_acqrel
	.prefalign	4, .Lfunc_end199, nop
	.type	atomic_umin_32_acqrel,@function
atomic_umin_32_acqrel:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB199_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovbel	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB199_1
	retq
.Lfunc_end199:
	.size	atomic_umin_32_acqrel, .Lfunc_end199-atomic_umin_32_acqrel
	.cfi_endproc

	.section	.text.atomic_umin_32_acquire,"ax",@progbits
	.globl	atomic_umin_32_acquire
	.prefalign	4, .Lfunc_end200, nop
	.type	atomic_umin_32_acquire,@function
atomic_umin_32_acquire:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB200_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovbel	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB200_1
	retq
.Lfunc_end200:
	.size	atomic_umin_32_acquire, .Lfunc_end200-atomic_umin_32_acquire
	.cfi_endproc

	.section	.text.atomic_umin_32_relaxed,"ax",@progbits
	.globl	atomic_umin_32_relaxed
	.prefalign	4, .Lfunc_end201, nop
	.type	atomic_umin_32_relaxed,@function
atomic_umin_32_relaxed:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB201_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovbel	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB201_1
	retq
.Lfunc_end201:
	.size	atomic_umin_32_relaxed, .Lfunc_end201-atomic_umin_32_relaxed
	.cfi_endproc

	.section	.text.atomic_umin_32_release,"ax",@progbits
	.globl	atomic_umin_32_release
	.prefalign	4, .Lfunc_end202, nop
	.type	atomic_umin_32_release,@function
atomic_umin_32_release:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB202_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovbel	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB202_1
	retq
.Lfunc_end202:
	.size	atomic_umin_32_release, .Lfunc_end202-atomic_umin_32_release
	.cfi_endproc

	.section	.text.atomic_umin_32_seqcst,"ax",@progbits
	.globl	atomic_umin_32_seqcst
	.prefalign	4, .Lfunc_end203, nop
	.type	atomic_umin_32_seqcst,@function
atomic_umin_32_seqcst:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB203_1:
	cmpl	%esi, %eax
	movl	%esi, %ecx
	cmovbel	%eax, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB203_1
	retq
.Lfunc_end203:
	.size	atomic_umin_32_seqcst, .Lfunc_end203-atomic_umin_32_seqcst
	.cfi_endproc

	.section	.text.atomic_umin_64_acqrel,"ax",@progbits
	.globl	atomic_umin_64_acqrel
	.prefalign	4, .Lfunc_end204, nop
	.type	atomic_umin_64_acqrel,@function
atomic_umin_64_acqrel:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB204_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovbeq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB204_1
	retq
.Lfunc_end204:
	.size	atomic_umin_64_acqrel, .Lfunc_end204-atomic_umin_64_acqrel
	.cfi_endproc

	.section	.text.atomic_umin_64_acquire,"ax",@progbits
	.globl	atomic_umin_64_acquire
	.prefalign	4, .Lfunc_end205, nop
	.type	atomic_umin_64_acquire,@function
atomic_umin_64_acquire:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB205_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovbeq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB205_1
	retq
.Lfunc_end205:
	.size	atomic_umin_64_acquire, .Lfunc_end205-atomic_umin_64_acquire
	.cfi_endproc

	.section	.text.atomic_umin_64_relaxed,"ax",@progbits
	.globl	atomic_umin_64_relaxed
	.prefalign	4, .Lfunc_end206, nop
	.type	atomic_umin_64_relaxed,@function
atomic_umin_64_relaxed:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB206_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovbeq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB206_1
	retq
.Lfunc_end206:
	.size	atomic_umin_64_relaxed, .Lfunc_end206-atomic_umin_64_relaxed
	.cfi_endproc

	.section	.text.atomic_umin_64_release,"ax",@progbits
	.globl	atomic_umin_64_release
	.prefalign	4, .Lfunc_end207, nop
	.type	atomic_umin_64_release,@function
atomic_umin_64_release:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB207_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovbeq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB207_1
	retq
.Lfunc_end207:
	.size	atomic_umin_64_release, .Lfunc_end207-atomic_umin_64_release
	.cfi_endproc

	.section	.text.atomic_umin_64_seqcst,"ax",@progbits
	.globl	atomic_umin_64_seqcst
	.prefalign	4, .Lfunc_end208, nop
	.type	atomic_umin_64_seqcst,@function
atomic_umin_64_seqcst:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB208_1:
	cmpq	%rsi, %rax
	movq	%rsi, %rcx
	cmovbeq	%rax, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB208_1
	retq
.Lfunc_end208:
	.size	atomic_umin_64_seqcst, .Lfunc_end208-atomic_umin_64_seqcst
	.cfi_endproc

	.section	.text.atomic_umin_8_acqrel,"ax",@progbits
	.globl	atomic_umin_8_acqrel
	.prefalign	4, .Lfunc_end209, nop
	.type	atomic_umin_8_acqrel,@function
atomic_umin_8_acqrel:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB209_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovbel	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB209_1
	retq
.Lfunc_end209:
	.size	atomic_umin_8_acqrel, .Lfunc_end209-atomic_umin_8_acqrel
	.cfi_endproc

	.section	.text.atomic_umin_8_acquire,"ax",@progbits
	.globl	atomic_umin_8_acquire
	.prefalign	4, .Lfunc_end210, nop
	.type	atomic_umin_8_acquire,@function
atomic_umin_8_acquire:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB210_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovbel	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB210_1
	retq
.Lfunc_end210:
	.size	atomic_umin_8_acquire, .Lfunc_end210-atomic_umin_8_acquire
	.cfi_endproc

	.section	.text.atomic_umin_8_relaxed,"ax",@progbits
	.globl	atomic_umin_8_relaxed
	.prefalign	4, .Lfunc_end211, nop
	.type	atomic_umin_8_relaxed,@function
atomic_umin_8_relaxed:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB211_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovbel	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB211_1
	retq
.Lfunc_end211:
	.size	atomic_umin_8_relaxed, .Lfunc_end211-atomic_umin_8_relaxed
	.cfi_endproc

	.section	.text.atomic_umin_8_release,"ax",@progbits
	.globl	atomic_umin_8_release
	.prefalign	4, .Lfunc_end212, nop
	.type	atomic_umin_8_release,@function
atomic_umin_8_release:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB212_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovbel	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB212_1
	retq
.Lfunc_end212:
	.size	atomic_umin_8_release, .Lfunc_end212-atomic_umin_8_release
	.cfi_endproc

	.section	.text.atomic_umin_8_seqcst,"ax",@progbits
	.globl	atomic_umin_8_seqcst
	.prefalign	4, .Lfunc_end213, nop
	.type	atomic_umin_8_seqcst,@function
atomic_umin_8_seqcst:
	.cfi_startproc
	movzbl	(%rdi), %eax
	movzbl	%sil, %ecx
	.p2align	4
.LBB213_1:
	cmpb	%cl, %al
	movzbl	%al, %eax
	movl	%ecx, %edx
	cmovbel	%eax, %edx
	lock		cmpxchgb	%dl, (%rdi)
	jne	.LBB213_1
	retq
.Lfunc_end213:
	.size	atomic_umin_8_seqcst, .Lfunc_end213-atomic_umin_8_seqcst
	.cfi_endproc

	.section	.text.atomic_xadd_128_acqrel,"ax",@progbits
	.globl	atomic_xadd_128_acqrel
	.prefalign	4, .Lfunc_end214, nop
	.type	atomic_xadd_128_acqrel,@function
atomic_xadd_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB214_1:
	movq	%rax, %rbx
	addq	%rsi, %rbx
	movq	%rdx, %rcx
	adcq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB214_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end214:
	.size	atomic_xadd_128_acqrel, .Lfunc_end214-atomic_xadd_128_acqrel
	.cfi_endproc

	.section	.text.atomic_xadd_128_acquire,"ax",@progbits
	.globl	atomic_xadd_128_acquire
	.prefalign	4, .Lfunc_end215, nop
	.type	atomic_xadd_128_acquire,@function
atomic_xadd_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB215_1:
	movq	%rax, %rbx
	addq	%rsi, %rbx
	movq	%rdx, %rcx
	adcq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB215_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end215:
	.size	atomic_xadd_128_acquire, .Lfunc_end215-atomic_xadd_128_acquire
	.cfi_endproc

	.section	.text.atomic_xadd_128_relaxed,"ax",@progbits
	.globl	atomic_xadd_128_relaxed
	.prefalign	4, .Lfunc_end216, nop
	.type	atomic_xadd_128_relaxed,@function
atomic_xadd_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB216_1:
	movq	%rax, %rbx
	addq	%rsi, %rbx
	movq	%rdx, %rcx
	adcq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB216_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end216:
	.size	atomic_xadd_128_relaxed, .Lfunc_end216-atomic_xadd_128_relaxed
	.cfi_endproc

	.section	.text.atomic_xadd_128_release,"ax",@progbits
	.globl	atomic_xadd_128_release
	.prefalign	4, .Lfunc_end217, nop
	.type	atomic_xadd_128_release,@function
atomic_xadd_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB217_1:
	movq	%rax, %rbx
	addq	%rsi, %rbx
	movq	%rdx, %rcx
	adcq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB217_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end217:
	.size	atomic_xadd_128_release, .Lfunc_end217-atomic_xadd_128_release
	.cfi_endproc

	.section	.text.atomic_xadd_128_seqcst,"ax",@progbits
	.globl	atomic_xadd_128_seqcst
	.prefalign	4, .Lfunc_end218, nop
	.type	atomic_xadd_128_seqcst,@function
atomic_xadd_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB218_1:
	movq	%rax, %rbx
	addq	%rsi, %rbx
	movq	%rdx, %rcx
	adcq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB218_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end218:
	.size	atomic_xadd_128_seqcst, .Lfunc_end218-atomic_xadd_128_seqcst
	.cfi_endproc

	.section	.text.atomic_xadd_16_acqrel,"ax",@progbits
	.globl	atomic_xadd_16_acqrel
	.prefalign	4, .Lfunc_end219, nop
	.type	atomic_xadd_16_acqrel,@function
atomic_xadd_16_acqrel:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddw	%ax, (%rdi)
	retq
.Lfunc_end219:
	.size	atomic_xadd_16_acqrel, .Lfunc_end219-atomic_xadd_16_acqrel
	.cfi_endproc

	.section	.text.atomic_xadd_16_acquire,"ax",@progbits
	.globl	atomic_xadd_16_acquire
	.prefalign	4, .Lfunc_end220, nop
	.type	atomic_xadd_16_acquire,@function
atomic_xadd_16_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddw	%ax, (%rdi)
	retq
.Lfunc_end220:
	.size	atomic_xadd_16_acquire, .Lfunc_end220-atomic_xadd_16_acquire
	.cfi_endproc

	.section	.text.atomic_xadd_16_relaxed,"ax",@progbits
	.globl	atomic_xadd_16_relaxed
	.prefalign	4, .Lfunc_end221, nop
	.type	atomic_xadd_16_relaxed,@function
atomic_xadd_16_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddw	%ax, (%rdi)
	retq
.Lfunc_end221:
	.size	atomic_xadd_16_relaxed, .Lfunc_end221-atomic_xadd_16_relaxed
	.cfi_endproc

	.section	.text.atomic_xadd_16_release,"ax",@progbits
	.globl	atomic_xadd_16_release
	.prefalign	4, .Lfunc_end222, nop
	.type	atomic_xadd_16_release,@function
atomic_xadd_16_release:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddw	%ax, (%rdi)
	retq
.Lfunc_end222:
	.size	atomic_xadd_16_release, .Lfunc_end222-atomic_xadd_16_release
	.cfi_endproc

	.section	.text.atomic_xadd_16_seqcst,"ax",@progbits
	.globl	atomic_xadd_16_seqcst
	.prefalign	4, .Lfunc_end223, nop
	.type	atomic_xadd_16_seqcst,@function
atomic_xadd_16_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddw	%ax, (%rdi)
	retq
.Lfunc_end223:
	.size	atomic_xadd_16_seqcst, .Lfunc_end223-atomic_xadd_16_seqcst
	.cfi_endproc

	.section	.text.atomic_xadd_32_acqrel,"ax",@progbits
	.globl	atomic_xadd_32_acqrel
	.prefalign	4, .Lfunc_end224, nop
	.type	atomic_xadd_32_acqrel,@function
atomic_xadd_32_acqrel:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddl	%eax, (%rdi)
	retq
.Lfunc_end224:
	.size	atomic_xadd_32_acqrel, .Lfunc_end224-atomic_xadd_32_acqrel
	.cfi_endproc

	.section	.text.atomic_xadd_32_acquire,"ax",@progbits
	.globl	atomic_xadd_32_acquire
	.prefalign	4, .Lfunc_end225, nop
	.type	atomic_xadd_32_acquire,@function
atomic_xadd_32_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddl	%eax, (%rdi)
	retq
.Lfunc_end225:
	.size	atomic_xadd_32_acquire, .Lfunc_end225-atomic_xadd_32_acquire
	.cfi_endproc

	.section	.text.atomic_xadd_32_relaxed,"ax",@progbits
	.globl	atomic_xadd_32_relaxed
	.prefalign	4, .Lfunc_end226, nop
	.type	atomic_xadd_32_relaxed,@function
atomic_xadd_32_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddl	%eax, (%rdi)
	retq
.Lfunc_end226:
	.size	atomic_xadd_32_relaxed, .Lfunc_end226-atomic_xadd_32_relaxed
	.cfi_endproc

	.section	.text.atomic_xadd_32_release,"ax",@progbits
	.globl	atomic_xadd_32_release
	.prefalign	4, .Lfunc_end227, nop
	.type	atomic_xadd_32_release,@function
atomic_xadd_32_release:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddl	%eax, (%rdi)
	retq
.Lfunc_end227:
	.size	atomic_xadd_32_release, .Lfunc_end227-atomic_xadd_32_release
	.cfi_endproc

	.section	.text.atomic_xadd_32_seqcst,"ax",@progbits
	.globl	atomic_xadd_32_seqcst
	.prefalign	4, .Lfunc_end228, nop
	.type	atomic_xadd_32_seqcst,@function
atomic_xadd_32_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddl	%eax, (%rdi)
	retq
.Lfunc_end228:
	.size	atomic_xadd_32_seqcst, .Lfunc_end228-atomic_xadd_32_seqcst
	.cfi_endproc

	.section	.text.atomic_xadd_64_acqrel,"ax",@progbits
	.globl	atomic_xadd_64_acqrel
	.prefalign	4, .Lfunc_end229, nop
	.type	atomic_xadd_64_acqrel,@function
atomic_xadd_64_acqrel:
	.cfi_startproc
	movq	%rsi, %rax
	lock		xaddq	%rax, (%rdi)
	retq
.Lfunc_end229:
	.size	atomic_xadd_64_acqrel, .Lfunc_end229-atomic_xadd_64_acqrel
	.cfi_endproc

	.section	.text.atomic_xadd_64_acquire,"ax",@progbits
	.globl	atomic_xadd_64_acquire
	.prefalign	4, .Lfunc_end230, nop
	.type	atomic_xadd_64_acquire,@function
atomic_xadd_64_acquire:
	.cfi_startproc
	movq	%rsi, %rax
	lock		xaddq	%rax, (%rdi)
	retq
.Lfunc_end230:
	.size	atomic_xadd_64_acquire, .Lfunc_end230-atomic_xadd_64_acquire
	.cfi_endproc

	.section	.text.atomic_xadd_64_relaxed,"ax",@progbits
	.globl	atomic_xadd_64_relaxed
	.prefalign	4, .Lfunc_end231, nop
	.type	atomic_xadd_64_relaxed,@function
atomic_xadd_64_relaxed:
	.cfi_startproc
	movq	%rsi, %rax
	lock		xaddq	%rax, (%rdi)
	retq
.Lfunc_end231:
	.size	atomic_xadd_64_relaxed, .Lfunc_end231-atomic_xadd_64_relaxed
	.cfi_endproc

	.section	.text.atomic_xadd_64_release,"ax",@progbits
	.globl	atomic_xadd_64_release
	.prefalign	4, .Lfunc_end232, nop
	.type	atomic_xadd_64_release,@function
atomic_xadd_64_release:
	.cfi_startproc
	movq	%rsi, %rax
	lock		xaddq	%rax, (%rdi)
	retq
.Lfunc_end232:
	.size	atomic_xadd_64_release, .Lfunc_end232-atomic_xadd_64_release
	.cfi_endproc

	.section	.text.atomic_xadd_64_seqcst,"ax",@progbits
	.globl	atomic_xadd_64_seqcst
	.prefalign	4, .Lfunc_end233, nop
	.type	atomic_xadd_64_seqcst,@function
atomic_xadd_64_seqcst:
	.cfi_startproc
	movq	%rsi, %rax
	lock		xaddq	%rax, (%rdi)
	retq
.Lfunc_end233:
	.size	atomic_xadd_64_seqcst, .Lfunc_end233-atomic_xadd_64_seqcst
	.cfi_endproc

	.section	.text.atomic_xadd_8_acqrel,"ax",@progbits
	.globl	atomic_xadd_8_acqrel
	.prefalign	4, .Lfunc_end234, nop
	.type	atomic_xadd_8_acqrel,@function
atomic_xadd_8_acqrel:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddb	%al, (%rdi)
	retq
.Lfunc_end234:
	.size	atomic_xadd_8_acqrel, .Lfunc_end234-atomic_xadd_8_acqrel
	.cfi_endproc

	.section	.text.atomic_xadd_8_acquire,"ax",@progbits
	.globl	atomic_xadd_8_acquire
	.prefalign	4, .Lfunc_end235, nop
	.type	atomic_xadd_8_acquire,@function
atomic_xadd_8_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddb	%al, (%rdi)
	retq
.Lfunc_end235:
	.size	atomic_xadd_8_acquire, .Lfunc_end235-atomic_xadd_8_acquire
	.cfi_endproc

	.section	.text.atomic_xadd_8_relaxed,"ax",@progbits
	.globl	atomic_xadd_8_relaxed
	.prefalign	4, .Lfunc_end236, nop
	.type	atomic_xadd_8_relaxed,@function
atomic_xadd_8_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddb	%al, (%rdi)
	retq
.Lfunc_end236:
	.size	atomic_xadd_8_relaxed, .Lfunc_end236-atomic_xadd_8_relaxed
	.cfi_endproc

	.section	.text.atomic_xadd_8_release,"ax",@progbits
	.globl	atomic_xadd_8_release
	.prefalign	4, .Lfunc_end237, nop
	.type	atomic_xadd_8_release,@function
atomic_xadd_8_release:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddb	%al, (%rdi)
	retq
.Lfunc_end237:
	.size	atomic_xadd_8_release, .Lfunc_end237-atomic_xadd_8_release
	.cfi_endproc

	.section	.text.atomic_xadd_8_seqcst,"ax",@progbits
	.globl	atomic_xadd_8_seqcst
	.prefalign	4, .Lfunc_end238, nop
	.type	atomic_xadd_8_seqcst,@function
atomic_xadd_8_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	lock		xaddb	%al, (%rdi)
	retq
.Lfunc_end238:
	.size	atomic_xadd_8_seqcst, .Lfunc_end238-atomic_xadd_8_seqcst
	.cfi_endproc

	.section	.text.atomic_xchg_128_acqrel,"ax",@progbits
	.globl	atomic_xchg_128_acqrel
	.prefalign	4, .Lfunc_end239, nop
	.type	atomic_xchg_128_acqrel,@function
atomic_xchg_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rcx
	movq	%rsi, %rbx
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB239_1:
	lock		cmpxchg16b	(%rdi)
	jne	.LBB239_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end239:
	.size	atomic_xchg_128_acqrel, .Lfunc_end239-atomic_xchg_128_acqrel
	.cfi_endproc

	.section	.text.atomic_xchg_128_acquire,"ax",@progbits
	.globl	atomic_xchg_128_acquire
	.prefalign	4, .Lfunc_end240, nop
	.type	atomic_xchg_128_acquire,@function
atomic_xchg_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rcx
	movq	%rsi, %rbx
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB240_1:
	lock		cmpxchg16b	(%rdi)
	jne	.LBB240_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end240:
	.size	atomic_xchg_128_acquire, .Lfunc_end240-atomic_xchg_128_acquire
	.cfi_endproc

	.section	.text.atomic_xchg_128_relaxed,"ax",@progbits
	.globl	atomic_xchg_128_relaxed
	.prefalign	4, .Lfunc_end241, nop
	.type	atomic_xchg_128_relaxed,@function
atomic_xchg_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rcx
	movq	%rsi, %rbx
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB241_1:
	lock		cmpxchg16b	(%rdi)
	jne	.LBB241_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end241:
	.size	atomic_xchg_128_relaxed, .Lfunc_end241-atomic_xchg_128_relaxed
	.cfi_endproc

	.section	.text.atomic_xchg_128_release,"ax",@progbits
	.globl	atomic_xchg_128_release
	.prefalign	4, .Lfunc_end242, nop
	.type	atomic_xchg_128_release,@function
atomic_xchg_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rcx
	movq	%rsi, %rbx
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB242_1:
	lock		cmpxchg16b	(%rdi)
	jne	.LBB242_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end242:
	.size	atomic_xchg_128_release, .Lfunc_end242-atomic_xchg_128_release
	.cfi_endproc

	.section	.text.atomic_xchg_128_seqcst,"ax",@progbits
	.globl	atomic_xchg_128_seqcst
	.prefalign	4, .Lfunc_end243, nop
	.type	atomic_xchg_128_seqcst,@function
atomic_xchg_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rcx
	movq	%rsi, %rbx
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB243_1:
	lock		cmpxchg16b	(%rdi)
	jne	.LBB243_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end243:
	.size	atomic_xchg_128_seqcst, .Lfunc_end243-atomic_xchg_128_seqcst
	.cfi_endproc

	.section	.text.atomic_xchg_16_acqrel,"ax",@progbits
	.globl	atomic_xchg_16_acqrel
	.prefalign	4, .Lfunc_end244, nop
	.type	atomic_xchg_16_acqrel,@function
atomic_xchg_16_acqrel:
	.cfi_startproc
	movl	%esi, %eax
	xchgw	%ax, (%rdi)
	retq
.Lfunc_end244:
	.size	atomic_xchg_16_acqrel, .Lfunc_end244-atomic_xchg_16_acqrel
	.cfi_endproc

	.section	.text.atomic_xchg_16_acquire,"ax",@progbits
	.globl	atomic_xchg_16_acquire
	.prefalign	4, .Lfunc_end245, nop
	.type	atomic_xchg_16_acquire,@function
atomic_xchg_16_acquire:
	.cfi_startproc
	movl	%esi, %eax
	xchgw	%ax, (%rdi)
	retq
.Lfunc_end245:
	.size	atomic_xchg_16_acquire, .Lfunc_end245-atomic_xchg_16_acquire
	.cfi_endproc

	.section	.text.atomic_xchg_16_relaxed,"ax",@progbits
	.globl	atomic_xchg_16_relaxed
	.prefalign	4, .Lfunc_end246, nop
	.type	atomic_xchg_16_relaxed,@function
atomic_xchg_16_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	xchgw	%ax, (%rdi)
	retq
.Lfunc_end246:
	.size	atomic_xchg_16_relaxed, .Lfunc_end246-atomic_xchg_16_relaxed
	.cfi_endproc

	.section	.text.atomic_xchg_16_release,"ax",@progbits
	.globl	atomic_xchg_16_release
	.prefalign	4, .Lfunc_end247, nop
	.type	atomic_xchg_16_release,@function
atomic_xchg_16_release:
	.cfi_startproc
	movl	%esi, %eax
	xchgw	%ax, (%rdi)
	retq
.Lfunc_end247:
	.size	atomic_xchg_16_release, .Lfunc_end247-atomic_xchg_16_release
	.cfi_endproc

	.section	.text.atomic_xchg_16_seqcst,"ax",@progbits
	.globl	atomic_xchg_16_seqcst
	.prefalign	4, .Lfunc_end248, nop
	.type	atomic_xchg_16_seqcst,@function
atomic_xchg_16_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	xchgw	%ax, (%rdi)
	retq
.Lfunc_end248:
	.size	atomic_xchg_16_seqcst, .Lfunc_end248-atomic_xchg_16_seqcst
	.cfi_endproc

	.section	.text.atomic_xchg_32_acqrel,"ax",@progbits
	.globl	atomic_xchg_32_acqrel
	.prefalign	4, .Lfunc_end249, nop
	.type	atomic_xchg_32_acqrel,@function
atomic_xchg_32_acqrel:
	.cfi_startproc
	movl	%esi, %eax
	xchgl	%eax, (%rdi)
	retq
.Lfunc_end249:
	.size	atomic_xchg_32_acqrel, .Lfunc_end249-atomic_xchg_32_acqrel
	.cfi_endproc

	.section	.text.atomic_xchg_32_acquire,"ax",@progbits
	.globl	atomic_xchg_32_acquire
	.prefalign	4, .Lfunc_end250, nop
	.type	atomic_xchg_32_acquire,@function
atomic_xchg_32_acquire:
	.cfi_startproc
	movl	%esi, %eax
	xchgl	%eax, (%rdi)
	retq
.Lfunc_end250:
	.size	atomic_xchg_32_acquire, .Lfunc_end250-atomic_xchg_32_acquire
	.cfi_endproc

	.section	.text.atomic_xchg_32_relaxed,"ax",@progbits
	.globl	atomic_xchg_32_relaxed
	.prefalign	4, .Lfunc_end251, nop
	.type	atomic_xchg_32_relaxed,@function
atomic_xchg_32_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	xchgl	%eax, (%rdi)
	retq
.Lfunc_end251:
	.size	atomic_xchg_32_relaxed, .Lfunc_end251-atomic_xchg_32_relaxed
	.cfi_endproc

	.section	.text.atomic_xchg_32_release,"ax",@progbits
	.globl	atomic_xchg_32_release
	.prefalign	4, .Lfunc_end252, nop
	.type	atomic_xchg_32_release,@function
atomic_xchg_32_release:
	.cfi_startproc
	movl	%esi, %eax
	xchgl	%eax, (%rdi)
	retq
.Lfunc_end252:
	.size	atomic_xchg_32_release, .Lfunc_end252-atomic_xchg_32_release
	.cfi_endproc

	.section	.text.atomic_xchg_32_seqcst,"ax",@progbits
	.globl	atomic_xchg_32_seqcst
	.prefalign	4, .Lfunc_end253, nop
	.type	atomic_xchg_32_seqcst,@function
atomic_xchg_32_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	xchgl	%eax, (%rdi)
	retq
.Lfunc_end253:
	.size	atomic_xchg_32_seqcst, .Lfunc_end253-atomic_xchg_32_seqcst
	.cfi_endproc

	.section	.text.atomic_xchg_64_acqrel,"ax",@progbits
	.globl	atomic_xchg_64_acqrel
	.prefalign	4, .Lfunc_end254, nop
	.type	atomic_xchg_64_acqrel,@function
atomic_xchg_64_acqrel:
	.cfi_startproc
	movq	%rsi, %rax
	xchgq	%rax, (%rdi)
	retq
.Lfunc_end254:
	.size	atomic_xchg_64_acqrel, .Lfunc_end254-atomic_xchg_64_acqrel
	.cfi_endproc

	.section	.text.atomic_xchg_64_acquire,"ax",@progbits
	.globl	atomic_xchg_64_acquire
	.prefalign	4, .Lfunc_end255, nop
	.type	atomic_xchg_64_acquire,@function
atomic_xchg_64_acquire:
	.cfi_startproc
	movq	%rsi, %rax
	xchgq	%rax, (%rdi)
	retq
.Lfunc_end255:
	.size	atomic_xchg_64_acquire, .Lfunc_end255-atomic_xchg_64_acquire
	.cfi_endproc

	.section	.text.atomic_xchg_64_relaxed,"ax",@progbits
	.globl	atomic_xchg_64_relaxed
	.prefalign	4, .Lfunc_end256, nop
	.type	atomic_xchg_64_relaxed,@function
atomic_xchg_64_relaxed:
	.cfi_startproc
	movq	%rsi, %rax
	xchgq	%rax, (%rdi)
	retq
.Lfunc_end256:
	.size	atomic_xchg_64_relaxed, .Lfunc_end256-atomic_xchg_64_relaxed
	.cfi_endproc

	.section	.text.atomic_xchg_64_release,"ax",@progbits
	.globl	atomic_xchg_64_release
	.prefalign	4, .Lfunc_end257, nop
	.type	atomic_xchg_64_release,@function
atomic_xchg_64_release:
	.cfi_startproc
	movq	%rsi, %rax
	xchgq	%rax, (%rdi)
	retq
.Lfunc_end257:
	.size	atomic_xchg_64_release, .Lfunc_end257-atomic_xchg_64_release
	.cfi_endproc

	.section	.text.atomic_xchg_64_seqcst,"ax",@progbits
	.globl	atomic_xchg_64_seqcst
	.prefalign	4, .Lfunc_end258, nop
	.type	atomic_xchg_64_seqcst,@function
atomic_xchg_64_seqcst:
	.cfi_startproc
	movq	%rsi, %rax
	xchgq	%rax, (%rdi)
	retq
.Lfunc_end258:
	.size	atomic_xchg_64_seqcst, .Lfunc_end258-atomic_xchg_64_seqcst
	.cfi_endproc

	.section	.text.atomic_xchg_8_acqrel,"ax",@progbits
	.globl	atomic_xchg_8_acqrel
	.prefalign	4, .Lfunc_end259, nop
	.type	atomic_xchg_8_acqrel,@function
atomic_xchg_8_acqrel:
	.cfi_startproc
	movl	%esi, %eax
	xchgb	%al, (%rdi)
	retq
.Lfunc_end259:
	.size	atomic_xchg_8_acqrel, .Lfunc_end259-atomic_xchg_8_acqrel
	.cfi_endproc

	.section	.text.atomic_xchg_8_acquire,"ax",@progbits
	.globl	atomic_xchg_8_acquire
	.prefalign	4, .Lfunc_end260, nop
	.type	atomic_xchg_8_acquire,@function
atomic_xchg_8_acquire:
	.cfi_startproc
	movl	%esi, %eax
	xchgb	%al, (%rdi)
	retq
.Lfunc_end260:
	.size	atomic_xchg_8_acquire, .Lfunc_end260-atomic_xchg_8_acquire
	.cfi_endproc

	.section	.text.atomic_xchg_8_relaxed,"ax",@progbits
	.globl	atomic_xchg_8_relaxed
	.prefalign	4, .Lfunc_end261, nop
	.type	atomic_xchg_8_relaxed,@function
atomic_xchg_8_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	xchgb	%al, (%rdi)
	retq
.Lfunc_end261:
	.size	atomic_xchg_8_relaxed, .Lfunc_end261-atomic_xchg_8_relaxed
	.cfi_endproc

	.section	.text.atomic_xchg_8_release,"ax",@progbits
	.globl	atomic_xchg_8_release
	.prefalign	4, .Lfunc_end262, nop
	.type	atomic_xchg_8_release,@function
atomic_xchg_8_release:
	.cfi_startproc
	movl	%esi, %eax
	xchgb	%al, (%rdi)
	retq
.Lfunc_end262:
	.size	atomic_xchg_8_release, .Lfunc_end262-atomic_xchg_8_release
	.cfi_endproc

	.section	.text.atomic_xchg_8_seqcst,"ax",@progbits
	.globl	atomic_xchg_8_seqcst
	.prefalign	4, .Lfunc_end263, nop
	.type	atomic_xchg_8_seqcst,@function
atomic_xchg_8_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	xchgb	%al, (%rdi)
	retq
.Lfunc_end263:
	.size	atomic_xchg_8_seqcst, .Lfunc_end263-atomic_xchg_8_seqcst
	.cfi_endproc

	.section	.text.atomic_xor_128_acqrel,"ax",@progbits
	.globl	atomic_xor_128_acqrel
	.prefalign	4, .Lfunc_end264, nop
	.type	atomic_xor_128_acqrel,@function
atomic_xor_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB264_1:
	movq	%rax, %rbx
	xorq	%rsi, %rbx
	movq	%rdx, %rcx
	xorq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB264_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end264:
	.size	atomic_xor_128_acqrel, .Lfunc_end264-atomic_xor_128_acqrel
	.cfi_endproc

	.section	.text.atomic_xor_128_acquire,"ax",@progbits
	.globl	atomic_xor_128_acquire
	.prefalign	4, .Lfunc_end265, nop
	.type	atomic_xor_128_acquire,@function
atomic_xor_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB265_1:
	movq	%rax, %rbx
	xorq	%rsi, %rbx
	movq	%rdx, %rcx
	xorq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB265_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end265:
	.size	atomic_xor_128_acquire, .Lfunc_end265-atomic_xor_128_acquire
	.cfi_endproc

	.section	.text.atomic_xor_128_relaxed,"ax",@progbits
	.globl	atomic_xor_128_relaxed
	.prefalign	4, .Lfunc_end266, nop
	.type	atomic_xor_128_relaxed,@function
atomic_xor_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB266_1:
	movq	%rax, %rbx
	xorq	%rsi, %rbx
	movq	%rdx, %rcx
	xorq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB266_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end266:
	.size	atomic_xor_128_relaxed, .Lfunc_end266-atomic_xor_128_relaxed
	.cfi_endproc

	.section	.text.atomic_xor_128_release,"ax",@progbits
	.globl	atomic_xor_128_release
	.prefalign	4, .Lfunc_end267, nop
	.type	atomic_xor_128_release,@function
atomic_xor_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB267_1:
	movq	%rax, %rbx
	xorq	%rsi, %rbx
	movq	%rdx, %rcx
	xorq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB267_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end267:
	.size	atomic_xor_128_release, .Lfunc_end267-atomic_xor_128_release
	.cfi_endproc

	.section	.text.atomic_xor_128_seqcst,"ax",@progbits
	.globl	atomic_xor_128_seqcst
	.prefalign	4, .Lfunc_end268, nop
	.type	atomic_xor_128_seqcst,@function
atomic_xor_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB268_1:
	movq	%rax, %rbx
	xorq	%rsi, %rbx
	movq	%rdx, %rcx
	xorq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB268_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end268:
	.size	atomic_xor_128_seqcst, .Lfunc_end268-atomic_xor_128_seqcst
	.cfi_endproc

	.section	.text.atomic_xor_16_acqrel,"ax",@progbits
	.globl	atomic_xor_16_acqrel
	.prefalign	4, .Lfunc_end269, nop
	.type	atomic_xor_16_acqrel,@function
atomic_xor_16_acqrel:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB269_1:
	movl	%eax, %ecx
	xorl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB269_1
	retq
.Lfunc_end269:
	.size	atomic_xor_16_acqrel, .Lfunc_end269-atomic_xor_16_acqrel
	.cfi_endproc

	.section	.text.atomic_xor_16_acquire,"ax",@progbits
	.globl	atomic_xor_16_acquire
	.prefalign	4, .Lfunc_end270, nop
	.type	atomic_xor_16_acquire,@function
atomic_xor_16_acquire:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB270_1:
	movl	%eax, %ecx
	xorl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB270_1
	retq
.Lfunc_end270:
	.size	atomic_xor_16_acquire, .Lfunc_end270-atomic_xor_16_acquire
	.cfi_endproc

	.section	.text.atomic_xor_16_relaxed,"ax",@progbits
	.globl	atomic_xor_16_relaxed
	.prefalign	4, .Lfunc_end271, nop
	.type	atomic_xor_16_relaxed,@function
atomic_xor_16_relaxed:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB271_1:
	movl	%eax, %ecx
	xorl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB271_1
	retq
.Lfunc_end271:
	.size	atomic_xor_16_relaxed, .Lfunc_end271-atomic_xor_16_relaxed
	.cfi_endproc

	.section	.text.atomic_xor_16_release,"ax",@progbits
	.globl	atomic_xor_16_release
	.prefalign	4, .Lfunc_end272, nop
	.type	atomic_xor_16_release,@function
atomic_xor_16_release:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB272_1:
	movl	%eax, %ecx
	xorl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB272_1
	retq
.Lfunc_end272:
	.size	atomic_xor_16_release, .Lfunc_end272-atomic_xor_16_release
	.cfi_endproc

	.section	.text.atomic_xor_16_seqcst,"ax",@progbits
	.globl	atomic_xor_16_seqcst
	.prefalign	4, .Lfunc_end273, nop
	.type	atomic_xor_16_seqcst,@function
atomic_xor_16_seqcst:
	.cfi_startproc
	movzwl	(%rdi), %eax
	.p2align	4
.LBB273_1:
	movl	%eax, %ecx
	xorl	%esi, %ecx
	lock		cmpxchgw	%cx, (%rdi)
	jne	.LBB273_1
	retq
.Lfunc_end273:
	.size	atomic_xor_16_seqcst, .Lfunc_end273-atomic_xor_16_seqcst
	.cfi_endproc

	.section	.text.atomic_xor_32_acqrel,"ax",@progbits
	.globl	atomic_xor_32_acqrel
	.prefalign	4, .Lfunc_end274, nop
	.type	atomic_xor_32_acqrel,@function
atomic_xor_32_acqrel:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB274_1:
	movl	%eax, %ecx
	xorl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB274_1
	retq
.Lfunc_end274:
	.size	atomic_xor_32_acqrel, .Lfunc_end274-atomic_xor_32_acqrel
	.cfi_endproc

	.section	.text.atomic_xor_32_acquire,"ax",@progbits
	.globl	atomic_xor_32_acquire
	.prefalign	4, .Lfunc_end275, nop
	.type	atomic_xor_32_acquire,@function
atomic_xor_32_acquire:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB275_1:
	movl	%eax, %ecx
	xorl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB275_1
	retq
.Lfunc_end275:
	.size	atomic_xor_32_acquire, .Lfunc_end275-atomic_xor_32_acquire
	.cfi_endproc

	.section	.text.atomic_xor_32_relaxed,"ax",@progbits
	.globl	atomic_xor_32_relaxed
	.prefalign	4, .Lfunc_end276, nop
	.type	atomic_xor_32_relaxed,@function
atomic_xor_32_relaxed:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB276_1:
	movl	%eax, %ecx
	xorl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB276_1
	retq
.Lfunc_end276:
	.size	atomic_xor_32_relaxed, .Lfunc_end276-atomic_xor_32_relaxed
	.cfi_endproc

	.section	.text.atomic_xor_32_release,"ax",@progbits
	.globl	atomic_xor_32_release
	.prefalign	4, .Lfunc_end277, nop
	.type	atomic_xor_32_release,@function
atomic_xor_32_release:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB277_1:
	movl	%eax, %ecx
	xorl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB277_1
	retq
.Lfunc_end277:
	.size	atomic_xor_32_release, .Lfunc_end277-atomic_xor_32_release
	.cfi_endproc

	.section	.text.atomic_xor_32_seqcst,"ax",@progbits
	.globl	atomic_xor_32_seqcst
	.prefalign	4, .Lfunc_end278, nop
	.type	atomic_xor_32_seqcst,@function
atomic_xor_32_seqcst:
	.cfi_startproc
	movl	(%rdi), %eax
	.p2align	4
.LBB278_1:
	movl	%eax, %ecx
	xorl	%esi, %ecx
	lock		cmpxchgl	%ecx, (%rdi)
	jne	.LBB278_1
	retq
.Lfunc_end278:
	.size	atomic_xor_32_seqcst, .Lfunc_end278-atomic_xor_32_seqcst
	.cfi_endproc

	.section	.text.atomic_xor_64_acqrel,"ax",@progbits
	.globl	atomic_xor_64_acqrel
	.prefalign	4, .Lfunc_end279, nop
	.type	atomic_xor_64_acqrel,@function
atomic_xor_64_acqrel:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB279_1:
	movq	%rax, %rcx
	xorq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB279_1
	retq
.Lfunc_end279:
	.size	atomic_xor_64_acqrel, .Lfunc_end279-atomic_xor_64_acqrel
	.cfi_endproc

	.section	.text.atomic_xor_64_acquire,"ax",@progbits
	.globl	atomic_xor_64_acquire
	.prefalign	4, .Lfunc_end280, nop
	.type	atomic_xor_64_acquire,@function
atomic_xor_64_acquire:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB280_1:
	movq	%rax, %rcx
	xorq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB280_1
	retq
.Lfunc_end280:
	.size	atomic_xor_64_acquire, .Lfunc_end280-atomic_xor_64_acquire
	.cfi_endproc

	.section	.text.atomic_xor_64_relaxed,"ax",@progbits
	.globl	atomic_xor_64_relaxed
	.prefalign	4, .Lfunc_end281, nop
	.type	atomic_xor_64_relaxed,@function
atomic_xor_64_relaxed:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB281_1:
	movq	%rax, %rcx
	xorq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB281_1
	retq
.Lfunc_end281:
	.size	atomic_xor_64_relaxed, .Lfunc_end281-atomic_xor_64_relaxed
	.cfi_endproc

	.section	.text.atomic_xor_64_release,"ax",@progbits
	.globl	atomic_xor_64_release
	.prefalign	4, .Lfunc_end282, nop
	.type	atomic_xor_64_release,@function
atomic_xor_64_release:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB282_1:
	movq	%rax, %rcx
	xorq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB282_1
	retq
.Lfunc_end282:
	.size	atomic_xor_64_release, .Lfunc_end282-atomic_xor_64_release
	.cfi_endproc

	.section	.text.atomic_xor_64_seqcst,"ax",@progbits
	.globl	atomic_xor_64_seqcst
	.prefalign	4, .Lfunc_end283, nop
	.type	atomic_xor_64_seqcst,@function
atomic_xor_64_seqcst:
	.cfi_startproc
	movq	(%rdi), %rax
	.p2align	4
.LBB283_1:
	movq	%rax, %rcx
	xorq	%rsi, %rcx
	lock		cmpxchgq	%rcx, (%rdi)
	jne	.LBB283_1
	retq
.Lfunc_end283:
	.size	atomic_xor_64_seqcst, .Lfunc_end283-atomic_xor_64_seqcst
	.cfi_endproc

	.section	.text.atomic_xor_8_acqrel,"ax",@progbits
	.globl	atomic_xor_8_acqrel
	.prefalign	4, .Lfunc_end284, nop
	.type	atomic_xor_8_acqrel,@function
atomic_xor_8_acqrel:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB284_1:
	movl	%eax, %ecx
	xorb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB284_1
	retq
.Lfunc_end284:
	.size	atomic_xor_8_acqrel, .Lfunc_end284-atomic_xor_8_acqrel
	.cfi_endproc

	.section	.text.atomic_xor_8_acquire,"ax",@progbits
	.globl	atomic_xor_8_acquire
	.prefalign	4, .Lfunc_end285, nop
	.type	atomic_xor_8_acquire,@function
atomic_xor_8_acquire:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB285_1:
	movl	%eax, %ecx
	xorb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB285_1
	retq
.Lfunc_end285:
	.size	atomic_xor_8_acquire, .Lfunc_end285-atomic_xor_8_acquire
	.cfi_endproc

	.section	.text.atomic_xor_8_relaxed,"ax",@progbits
	.globl	atomic_xor_8_relaxed
	.prefalign	4, .Lfunc_end286, nop
	.type	atomic_xor_8_relaxed,@function
atomic_xor_8_relaxed:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB286_1:
	movl	%eax, %ecx
	xorb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB286_1
	retq
.Lfunc_end286:
	.size	atomic_xor_8_relaxed, .Lfunc_end286-atomic_xor_8_relaxed
	.cfi_endproc

	.section	.text.atomic_xor_8_release,"ax",@progbits
	.globl	atomic_xor_8_release
	.prefalign	4, .Lfunc_end287, nop
	.type	atomic_xor_8_release,@function
atomic_xor_8_release:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB287_1:
	movl	%eax, %ecx
	xorb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB287_1
	retq
.Lfunc_end287:
	.size	atomic_xor_8_release, .Lfunc_end287-atomic_xor_8_release
	.cfi_endproc

	.section	.text.atomic_xor_8_seqcst,"ax",@progbits
	.globl	atomic_xor_8_seqcst
	.prefalign	4, .Lfunc_end288, nop
	.type	atomic_xor_8_seqcst,@function
atomic_xor_8_seqcst:
	.cfi_startproc
	movzbl	(%rdi), %eax
	.p2align	4
.LBB288_1:
	movl	%eax, %ecx
	xorb	%sil, %cl
	lock		cmpxchgb	%cl, (%rdi)
	jne	.LBB288_1
	retq
.Lfunc_end288:
	.size	atomic_xor_8_seqcst, .Lfunc_end288-atomic_xor_8_seqcst
	.cfi_endproc

	.section	.text.atomic_xsub_128_acqrel,"ax",@progbits
	.globl	atomic_xsub_128_acqrel
	.prefalign	4, .Lfunc_end289, nop
	.type	atomic_xsub_128_acqrel,@function
atomic_xsub_128_acqrel:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB289_1:
	movq	%rax, %rbx
	subq	%rsi, %rbx
	movq	%rdx, %rcx
	sbbq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB289_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end289:
	.size	atomic_xsub_128_acqrel, .Lfunc_end289-atomic_xsub_128_acqrel
	.cfi_endproc

	.section	.text.atomic_xsub_128_acquire,"ax",@progbits
	.globl	atomic_xsub_128_acquire
	.prefalign	4, .Lfunc_end290, nop
	.type	atomic_xsub_128_acquire,@function
atomic_xsub_128_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB290_1:
	movq	%rax, %rbx
	subq	%rsi, %rbx
	movq	%rdx, %rcx
	sbbq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB290_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end290:
	.size	atomic_xsub_128_acquire, .Lfunc_end290-atomic_xsub_128_acquire
	.cfi_endproc

	.section	.text.atomic_xsub_128_relaxed,"ax",@progbits
	.globl	atomic_xsub_128_relaxed
	.prefalign	4, .Lfunc_end291, nop
	.type	atomic_xsub_128_relaxed,@function
atomic_xsub_128_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB291_1:
	movq	%rax, %rbx
	subq	%rsi, %rbx
	movq	%rdx, %rcx
	sbbq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB291_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end291:
	.size	atomic_xsub_128_relaxed, .Lfunc_end291-atomic_xsub_128_relaxed
	.cfi_endproc

	.section	.text.atomic_xsub_128_release,"ax",@progbits
	.globl	atomic_xsub_128_release
	.prefalign	4, .Lfunc_end292, nop
	.type	atomic_xsub_128_release,@function
atomic_xsub_128_release:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB292_1:
	movq	%rax, %rbx
	subq	%rsi, %rbx
	movq	%rdx, %rcx
	sbbq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB292_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end292:
	.size	atomic_xsub_128_release, .Lfunc_end292-atomic_xsub_128_release
	.cfi_endproc

	.section	.text.atomic_xsub_128_seqcst,"ax",@progbits
	.globl	atomic_xsub_128_seqcst
	.prefalign	4, .Lfunc_end293, nop
	.type	atomic_xsub_128_seqcst,@function
atomic_xsub_128_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %r8
	movq	(%rdi), %rax
	movq	8(%rdi), %rdx
	.p2align	4
.LBB293_1:
	movq	%rax, %rbx
	subq	%rsi, %rbx
	movq	%rdx, %rcx
	sbbq	%r8, %rcx
	lock		cmpxchg16b	(%rdi)
	jne	.LBB293_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end293:
	.size	atomic_xsub_128_seqcst, .Lfunc_end293-atomic_xsub_128_seqcst
	.cfi_endproc

	.section	.text.atomic_xsub_16_acqrel,"ax",@progbits
	.globl	atomic_xsub_16_acqrel
	.prefalign	4, .Lfunc_end294, nop
	.type	atomic_xsub_16_acqrel,@function
atomic_xsub_16_acqrel:
	.cfi_startproc
	movl	%esi, %eax
	negl	%eax
	lock		xaddw	%ax, (%rdi)
	retq
.Lfunc_end294:
	.size	atomic_xsub_16_acqrel, .Lfunc_end294-atomic_xsub_16_acqrel
	.cfi_endproc

	.section	.text.atomic_xsub_16_acquire,"ax",@progbits
	.globl	atomic_xsub_16_acquire
	.prefalign	4, .Lfunc_end295, nop
	.type	atomic_xsub_16_acquire,@function
atomic_xsub_16_acquire:
	.cfi_startproc
	movl	%esi, %eax
	negl	%eax
	lock		xaddw	%ax, (%rdi)
	retq
.Lfunc_end295:
	.size	atomic_xsub_16_acquire, .Lfunc_end295-atomic_xsub_16_acquire
	.cfi_endproc

	.section	.text.atomic_xsub_16_relaxed,"ax",@progbits
	.globl	atomic_xsub_16_relaxed
	.prefalign	4, .Lfunc_end296, nop
	.type	atomic_xsub_16_relaxed,@function
atomic_xsub_16_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	negl	%eax
	lock		xaddw	%ax, (%rdi)
	retq
.Lfunc_end296:
	.size	atomic_xsub_16_relaxed, .Lfunc_end296-atomic_xsub_16_relaxed
	.cfi_endproc

	.section	.text.atomic_xsub_16_release,"ax",@progbits
	.globl	atomic_xsub_16_release
	.prefalign	4, .Lfunc_end297, nop
	.type	atomic_xsub_16_release,@function
atomic_xsub_16_release:
	.cfi_startproc
	movl	%esi, %eax
	negl	%eax
	lock		xaddw	%ax, (%rdi)
	retq
.Lfunc_end297:
	.size	atomic_xsub_16_release, .Lfunc_end297-atomic_xsub_16_release
	.cfi_endproc

	.section	.text.atomic_xsub_16_seqcst,"ax",@progbits
	.globl	atomic_xsub_16_seqcst
	.prefalign	4, .Lfunc_end298, nop
	.type	atomic_xsub_16_seqcst,@function
atomic_xsub_16_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	negl	%eax
	lock		xaddw	%ax, (%rdi)
	retq
.Lfunc_end298:
	.size	atomic_xsub_16_seqcst, .Lfunc_end298-atomic_xsub_16_seqcst
	.cfi_endproc

	.section	.text.atomic_xsub_32_acqrel,"ax",@progbits
	.globl	atomic_xsub_32_acqrel
	.prefalign	4, .Lfunc_end299, nop
	.type	atomic_xsub_32_acqrel,@function
atomic_xsub_32_acqrel:
	.cfi_startproc
	movl	%esi, %eax
	negl	%eax
	lock		xaddl	%eax, (%rdi)
	retq
.Lfunc_end299:
	.size	atomic_xsub_32_acqrel, .Lfunc_end299-atomic_xsub_32_acqrel
	.cfi_endproc

	.section	.text.atomic_xsub_32_acquire,"ax",@progbits
	.globl	atomic_xsub_32_acquire
	.prefalign	4, .Lfunc_end300, nop
	.type	atomic_xsub_32_acquire,@function
atomic_xsub_32_acquire:
	.cfi_startproc
	movl	%esi, %eax
	negl	%eax
	lock		xaddl	%eax, (%rdi)
	retq
.Lfunc_end300:
	.size	atomic_xsub_32_acquire, .Lfunc_end300-atomic_xsub_32_acquire
	.cfi_endproc

	.section	.text.atomic_xsub_32_relaxed,"ax",@progbits
	.globl	atomic_xsub_32_relaxed
	.prefalign	4, .Lfunc_end301, nop
	.type	atomic_xsub_32_relaxed,@function
atomic_xsub_32_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	negl	%eax
	lock		xaddl	%eax, (%rdi)
	retq
.Lfunc_end301:
	.size	atomic_xsub_32_relaxed, .Lfunc_end301-atomic_xsub_32_relaxed
	.cfi_endproc

	.section	.text.atomic_xsub_32_release,"ax",@progbits
	.globl	atomic_xsub_32_release
	.prefalign	4, .Lfunc_end302, nop
	.type	atomic_xsub_32_release,@function
atomic_xsub_32_release:
	.cfi_startproc
	movl	%esi, %eax
	negl	%eax
	lock		xaddl	%eax, (%rdi)
	retq
.Lfunc_end302:
	.size	atomic_xsub_32_release, .Lfunc_end302-atomic_xsub_32_release
	.cfi_endproc

	.section	.text.atomic_xsub_32_seqcst,"ax",@progbits
	.globl	atomic_xsub_32_seqcst
	.prefalign	4, .Lfunc_end303, nop
	.type	atomic_xsub_32_seqcst,@function
atomic_xsub_32_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	negl	%eax
	lock		xaddl	%eax, (%rdi)
	retq
.Lfunc_end303:
	.size	atomic_xsub_32_seqcst, .Lfunc_end303-atomic_xsub_32_seqcst
	.cfi_endproc

	.section	.text.atomic_xsub_64_acqrel,"ax",@progbits
	.globl	atomic_xsub_64_acqrel
	.prefalign	4, .Lfunc_end304, nop
	.type	atomic_xsub_64_acqrel,@function
atomic_xsub_64_acqrel:
	.cfi_startproc
	movq	%rsi, %rax
	negq	%rax
	lock		xaddq	%rax, (%rdi)
	retq
.Lfunc_end304:
	.size	atomic_xsub_64_acqrel, .Lfunc_end304-atomic_xsub_64_acqrel
	.cfi_endproc

	.section	.text.atomic_xsub_64_acquire,"ax",@progbits
	.globl	atomic_xsub_64_acquire
	.prefalign	4, .Lfunc_end305, nop
	.type	atomic_xsub_64_acquire,@function
atomic_xsub_64_acquire:
	.cfi_startproc
	movq	%rsi, %rax
	negq	%rax
	lock		xaddq	%rax, (%rdi)
	retq
.Lfunc_end305:
	.size	atomic_xsub_64_acquire, .Lfunc_end305-atomic_xsub_64_acquire
	.cfi_endproc

	.section	.text.atomic_xsub_64_relaxed,"ax",@progbits
	.globl	atomic_xsub_64_relaxed
	.prefalign	4, .Lfunc_end306, nop
	.type	atomic_xsub_64_relaxed,@function
atomic_xsub_64_relaxed:
	.cfi_startproc
	movq	%rsi, %rax
	negq	%rax
	lock		xaddq	%rax, (%rdi)
	retq
.Lfunc_end306:
	.size	atomic_xsub_64_relaxed, .Lfunc_end306-atomic_xsub_64_relaxed
	.cfi_endproc

	.section	.text.atomic_xsub_64_release,"ax",@progbits
	.globl	atomic_xsub_64_release
	.prefalign	4, .Lfunc_end307, nop
	.type	atomic_xsub_64_release,@function
atomic_xsub_64_release:
	.cfi_startproc
	movq	%rsi, %rax
	negq	%rax
	lock		xaddq	%rax, (%rdi)
	retq
.Lfunc_end307:
	.size	atomic_xsub_64_release, .Lfunc_end307-atomic_xsub_64_release
	.cfi_endproc

	.section	.text.atomic_xsub_64_seqcst,"ax",@progbits
	.globl	atomic_xsub_64_seqcst
	.prefalign	4, .Lfunc_end308, nop
	.type	atomic_xsub_64_seqcst,@function
atomic_xsub_64_seqcst:
	.cfi_startproc
	movq	%rsi, %rax
	negq	%rax
	lock		xaddq	%rax, (%rdi)
	retq
.Lfunc_end308:
	.size	atomic_xsub_64_seqcst, .Lfunc_end308-atomic_xsub_64_seqcst
	.cfi_endproc

	.section	.text.atomic_xsub_8_acqrel,"ax",@progbits
	.globl	atomic_xsub_8_acqrel
	.prefalign	4, .Lfunc_end309, nop
	.type	atomic_xsub_8_acqrel,@function
atomic_xsub_8_acqrel:
	.cfi_startproc
	movl	%esi, %eax
	negb	%al
	lock		xaddb	%al, (%rdi)
	retq
.Lfunc_end309:
	.size	atomic_xsub_8_acqrel, .Lfunc_end309-atomic_xsub_8_acqrel
	.cfi_endproc

	.section	.text.atomic_xsub_8_acquire,"ax",@progbits
	.globl	atomic_xsub_8_acquire
	.prefalign	4, .Lfunc_end310, nop
	.type	atomic_xsub_8_acquire,@function
atomic_xsub_8_acquire:
	.cfi_startproc
	movl	%esi, %eax
	negb	%al
	lock		xaddb	%al, (%rdi)
	retq
.Lfunc_end310:
	.size	atomic_xsub_8_acquire, .Lfunc_end310-atomic_xsub_8_acquire
	.cfi_endproc

	.section	.text.atomic_xsub_8_relaxed,"ax",@progbits
	.globl	atomic_xsub_8_relaxed
	.prefalign	4, .Lfunc_end311, nop
	.type	atomic_xsub_8_relaxed,@function
atomic_xsub_8_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	negb	%al
	lock		xaddb	%al, (%rdi)
	retq
.Lfunc_end311:
	.size	atomic_xsub_8_relaxed, .Lfunc_end311-atomic_xsub_8_relaxed
	.cfi_endproc

	.section	.text.atomic_xsub_8_release,"ax",@progbits
	.globl	atomic_xsub_8_release
	.prefalign	4, .Lfunc_end312, nop
	.type	atomic_xsub_8_release,@function
atomic_xsub_8_release:
	.cfi_startproc
	movl	%esi, %eax
	negb	%al
	lock		xaddb	%al, (%rdi)
	retq
.Lfunc_end312:
	.size	atomic_xsub_8_release, .Lfunc_end312-atomic_xsub_8_release
	.cfi_endproc

	.section	.text.atomic_xsub_8_seqcst,"ax",@progbits
	.globl	atomic_xsub_8_seqcst
	.prefalign	4, .Lfunc_end313, nop
	.type	atomic_xsub_8_seqcst,@function
atomic_xsub_8_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	negb	%al
	lock		xaddb	%al, (%rdi)
	retq
.Lfunc_end313:
	.size	atomic_xsub_8_seqcst, .Lfunc_end313-atomic_xsub_8_seqcst
	.cfi_endproc

	.section	.text.cxchg_128_acqrel_acquire,"ax",@progbits
	.globl	cxchg_128_acqrel_acquire
	.prefalign	4, .Lfunc_end314, nop
	.type	cxchg_128_acqrel_acquire,@function
cxchg_128_acqrel_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end314:
	.size	cxchg_128_acqrel_acquire, .Lfunc_end314-cxchg_128_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchg_128_acquire_acquire,"ax",@progbits
	.globl	cxchg_128_acquire_acquire
	.prefalign	4, .Lfunc_end315, nop
	.type	cxchg_128_acquire_acquire,@function
cxchg_128_acquire_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end315:
	.size	cxchg_128_acquire_acquire, .Lfunc_end315-cxchg_128_acquire_acquire
	.cfi_endproc

	.section	.text.cxchg_128_relaxed_relaxed,"ax",@progbits
	.globl	cxchg_128_relaxed_relaxed
	.prefalign	4, .Lfunc_end316, nop
	.type	cxchg_128_relaxed_relaxed,@function
cxchg_128_relaxed_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end316:
	.size	cxchg_128_relaxed_relaxed, .Lfunc_end316-cxchg_128_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchg_128_release_relaxed,"ax",@progbits
	.globl	cxchg_128_release_relaxed
	.prefalign	4, .Lfunc_end317, nop
	.type	cxchg_128_release_relaxed,@function
cxchg_128_release_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end317:
	.size	cxchg_128_release_relaxed, .Lfunc_end317-cxchg_128_release_relaxed
	.cfi_endproc

	.section	.text.cxchg_128_seqcst_relaxed,"ax",@progbits
	.globl	cxchg_128_seqcst_relaxed
	.prefalign	4, .Lfunc_end318, nop
	.type	cxchg_128_seqcst_relaxed,@function
cxchg_128_seqcst_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end318:
	.size	cxchg_128_seqcst_relaxed, .Lfunc_end318-cxchg_128_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchg_128_seqcst_seqcst,"ax",@progbits
	.globl	cxchg_128_seqcst_seqcst
	.prefalign	4, .Lfunc_end319, nop
	.type	cxchg_128_seqcst_seqcst,@function
cxchg_128_seqcst_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end319:
	.size	cxchg_128_seqcst_seqcst, .Lfunc_end319-cxchg_128_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchg_16_acqrel_acquire,"ax",@progbits
	.globl	cxchg_16_acqrel_acquire
	.prefalign	4, .Lfunc_end320, nop
	.type	cxchg_16_acqrel_acquire,@function
cxchg_16_acqrel_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end320:
	.size	cxchg_16_acqrel_acquire, .Lfunc_end320-cxchg_16_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchg_16_acquire_acquire,"ax",@progbits
	.globl	cxchg_16_acquire_acquire
	.prefalign	4, .Lfunc_end321, nop
	.type	cxchg_16_acquire_acquire,@function
cxchg_16_acquire_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end321:
	.size	cxchg_16_acquire_acquire, .Lfunc_end321-cxchg_16_acquire_acquire
	.cfi_endproc

	.section	.text.cxchg_16_relaxed_relaxed,"ax",@progbits
	.globl	cxchg_16_relaxed_relaxed
	.prefalign	4, .Lfunc_end322, nop
	.type	cxchg_16_relaxed_relaxed,@function
cxchg_16_relaxed_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end322:
	.size	cxchg_16_relaxed_relaxed, .Lfunc_end322-cxchg_16_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchg_16_release_relaxed,"ax",@progbits
	.globl	cxchg_16_release_relaxed
	.prefalign	4, .Lfunc_end323, nop
	.type	cxchg_16_release_relaxed,@function
cxchg_16_release_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end323:
	.size	cxchg_16_release_relaxed, .Lfunc_end323-cxchg_16_release_relaxed
	.cfi_endproc

	.section	.text.cxchg_16_seqcst_relaxed,"ax",@progbits
	.globl	cxchg_16_seqcst_relaxed
	.prefalign	4, .Lfunc_end324, nop
	.type	cxchg_16_seqcst_relaxed,@function
cxchg_16_seqcst_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end324:
	.size	cxchg_16_seqcst_relaxed, .Lfunc_end324-cxchg_16_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchg_16_seqcst_seqcst,"ax",@progbits
	.globl	cxchg_16_seqcst_seqcst
	.prefalign	4, .Lfunc_end325, nop
	.type	cxchg_16_seqcst_seqcst,@function
cxchg_16_seqcst_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end325:
	.size	cxchg_16_seqcst_seqcst, .Lfunc_end325-cxchg_16_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchg_32_acqrel_acquire,"ax",@progbits
	.globl	cxchg_32_acqrel_acquire
	.prefalign	4, .Lfunc_end326, nop
	.type	cxchg_32_acqrel_acquire,@function
cxchg_32_acqrel_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end326:
	.size	cxchg_32_acqrel_acquire, .Lfunc_end326-cxchg_32_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchg_32_acquire_acquire,"ax",@progbits
	.globl	cxchg_32_acquire_acquire
	.prefalign	4, .Lfunc_end327, nop
	.type	cxchg_32_acquire_acquire,@function
cxchg_32_acquire_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end327:
	.size	cxchg_32_acquire_acquire, .Lfunc_end327-cxchg_32_acquire_acquire
	.cfi_endproc

	.section	.text.cxchg_32_relaxed_relaxed,"ax",@progbits
	.globl	cxchg_32_relaxed_relaxed
	.prefalign	4, .Lfunc_end328, nop
	.type	cxchg_32_relaxed_relaxed,@function
cxchg_32_relaxed_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end328:
	.size	cxchg_32_relaxed_relaxed, .Lfunc_end328-cxchg_32_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchg_32_release_relaxed,"ax",@progbits
	.globl	cxchg_32_release_relaxed
	.prefalign	4, .Lfunc_end329, nop
	.type	cxchg_32_release_relaxed,@function
cxchg_32_release_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end329:
	.size	cxchg_32_release_relaxed, .Lfunc_end329-cxchg_32_release_relaxed
	.cfi_endproc

	.section	.text.cxchg_32_seqcst_relaxed,"ax",@progbits
	.globl	cxchg_32_seqcst_relaxed
	.prefalign	4, .Lfunc_end330, nop
	.type	cxchg_32_seqcst_relaxed,@function
cxchg_32_seqcst_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end330:
	.size	cxchg_32_seqcst_relaxed, .Lfunc_end330-cxchg_32_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchg_32_seqcst_seqcst,"ax",@progbits
	.globl	cxchg_32_seqcst_seqcst
	.prefalign	4, .Lfunc_end331, nop
	.type	cxchg_32_seqcst_seqcst,@function
cxchg_32_seqcst_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end331:
	.size	cxchg_32_seqcst_seqcst, .Lfunc_end331-cxchg_32_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchg_64_acqrel_acquire,"ax",@progbits
	.globl	cxchg_64_acqrel_acquire
	.prefalign	4, .Lfunc_end332, nop
	.type	cxchg_64_acqrel_acquire,@function
cxchg_64_acqrel_acquire:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end332:
	.size	cxchg_64_acqrel_acquire, .Lfunc_end332-cxchg_64_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchg_64_acquire_acquire,"ax",@progbits
	.globl	cxchg_64_acquire_acquire
	.prefalign	4, .Lfunc_end333, nop
	.type	cxchg_64_acquire_acquire,@function
cxchg_64_acquire_acquire:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end333:
	.size	cxchg_64_acquire_acquire, .Lfunc_end333-cxchg_64_acquire_acquire
	.cfi_endproc

	.section	.text.cxchg_64_relaxed_relaxed,"ax",@progbits
	.globl	cxchg_64_relaxed_relaxed
	.prefalign	4, .Lfunc_end334, nop
	.type	cxchg_64_relaxed_relaxed,@function
cxchg_64_relaxed_relaxed:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end334:
	.size	cxchg_64_relaxed_relaxed, .Lfunc_end334-cxchg_64_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchg_64_release_relaxed,"ax",@progbits
	.globl	cxchg_64_release_relaxed
	.prefalign	4, .Lfunc_end335, nop
	.type	cxchg_64_release_relaxed,@function
cxchg_64_release_relaxed:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end335:
	.size	cxchg_64_release_relaxed, .Lfunc_end335-cxchg_64_release_relaxed
	.cfi_endproc

	.section	.text.cxchg_64_seqcst_relaxed,"ax",@progbits
	.globl	cxchg_64_seqcst_relaxed
	.prefalign	4, .Lfunc_end336, nop
	.type	cxchg_64_seqcst_relaxed,@function
cxchg_64_seqcst_relaxed:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end336:
	.size	cxchg_64_seqcst_relaxed, .Lfunc_end336-cxchg_64_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchg_64_seqcst_seqcst,"ax",@progbits
	.globl	cxchg_64_seqcst_seqcst
	.prefalign	4, .Lfunc_end337, nop
	.type	cxchg_64_seqcst_seqcst,@function
cxchg_64_seqcst_seqcst:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end337:
	.size	cxchg_64_seqcst_seqcst, .Lfunc_end337-cxchg_64_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchg_8_acqrel_acquire,"ax",@progbits
	.globl	cxchg_8_acqrel_acquire
	.prefalign	4, .Lfunc_end338, nop
	.type	cxchg_8_acqrel_acquire,@function
cxchg_8_acqrel_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end338:
	.size	cxchg_8_acqrel_acquire, .Lfunc_end338-cxchg_8_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchg_8_acquire_acquire,"ax",@progbits
	.globl	cxchg_8_acquire_acquire
	.prefalign	4, .Lfunc_end339, nop
	.type	cxchg_8_acquire_acquire,@function
cxchg_8_acquire_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end339:
	.size	cxchg_8_acquire_acquire, .Lfunc_end339-cxchg_8_acquire_acquire
	.cfi_endproc

	.section	.text.cxchg_8_relaxed_relaxed,"ax",@progbits
	.globl	cxchg_8_relaxed_relaxed
	.prefalign	4, .Lfunc_end340, nop
	.type	cxchg_8_relaxed_relaxed,@function
cxchg_8_relaxed_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end340:
	.size	cxchg_8_relaxed_relaxed, .Lfunc_end340-cxchg_8_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchg_8_release_relaxed,"ax",@progbits
	.globl	cxchg_8_release_relaxed
	.prefalign	4, .Lfunc_end341, nop
	.type	cxchg_8_release_relaxed,@function
cxchg_8_release_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end341:
	.size	cxchg_8_release_relaxed, .Lfunc_end341-cxchg_8_release_relaxed
	.cfi_endproc

	.section	.text.cxchg_8_seqcst_relaxed,"ax",@progbits
	.globl	cxchg_8_seqcst_relaxed
	.prefalign	4, .Lfunc_end342, nop
	.type	cxchg_8_seqcst_relaxed,@function
cxchg_8_seqcst_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end342:
	.size	cxchg_8_seqcst_relaxed, .Lfunc_end342-cxchg_8_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchg_8_seqcst_seqcst,"ax",@progbits
	.globl	cxchg_8_seqcst_seqcst
	.prefalign	4, .Lfunc_end343, nop
	.type	cxchg_8_seqcst_seqcst,@function
cxchg_8_seqcst_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end343:
	.size	cxchg_8_seqcst_seqcst, .Lfunc_end343-cxchg_8_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchgweak_128_acqrel_acquire,"ax",@progbits
	.globl	cxchgweak_128_acqrel_acquire
	.prefalign	4, .Lfunc_end344, nop
	.type	cxchgweak_128_acqrel_acquire,@function
cxchgweak_128_acqrel_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end344:
	.size	cxchgweak_128_acqrel_acquire, .Lfunc_end344-cxchgweak_128_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchgweak_128_acquire_acquire,"ax",@progbits
	.globl	cxchgweak_128_acquire_acquire
	.prefalign	4, .Lfunc_end345, nop
	.type	cxchgweak_128_acquire_acquire,@function
cxchgweak_128_acquire_acquire:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end345:
	.size	cxchgweak_128_acquire_acquire, .Lfunc_end345-cxchgweak_128_acquire_acquire
	.cfi_endproc

	.section	.text.cxchgweak_128_relaxed_relaxed,"ax",@progbits
	.globl	cxchgweak_128_relaxed_relaxed
	.prefalign	4, .Lfunc_end346, nop
	.type	cxchgweak_128_relaxed_relaxed,@function
cxchgweak_128_relaxed_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end346:
	.size	cxchgweak_128_relaxed_relaxed, .Lfunc_end346-cxchgweak_128_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_128_release_relaxed,"ax",@progbits
	.globl	cxchgweak_128_release_relaxed
	.prefalign	4, .Lfunc_end347, nop
	.type	cxchgweak_128_release_relaxed,@function
cxchgweak_128_release_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end347:
	.size	cxchgweak_128_release_relaxed, .Lfunc_end347-cxchgweak_128_release_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_128_seqcst_relaxed,"ax",@progbits
	.globl	cxchgweak_128_seqcst_relaxed
	.prefalign	4, .Lfunc_end348, nop
	.type	cxchgweak_128_seqcst_relaxed,@function
cxchgweak_128_seqcst_relaxed:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end348:
	.size	cxchgweak_128_seqcst_relaxed, .Lfunc_end348-cxchgweak_128_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_128_seqcst_seqcst,"ax",@progbits
	.globl	cxchgweak_128_seqcst_seqcst
	.prefalign	4, .Lfunc_end349, nop
	.type	cxchgweak_128_seqcst_seqcst,@function
cxchgweak_128_seqcst_seqcst:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdx, %rax
	movq	%rcx, %rdx
	movq	%r9, %rcx
	movq	%r8, %rbx
	lock		cmpxchg16b	(%rsi)
	movq	%rax, (%rdi)
	movq	%rdx, 8(%rdi)
	sete	16(%rdi)
	movq	%rdi, %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end349:
	.size	cxchgweak_128_seqcst_seqcst, .Lfunc_end349-cxchgweak_128_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchgweak_16_acqrel_acquire,"ax",@progbits
	.globl	cxchgweak_16_acqrel_acquire
	.prefalign	4, .Lfunc_end350, nop
	.type	cxchgweak_16_acqrel_acquire,@function
cxchgweak_16_acqrel_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end350:
	.size	cxchgweak_16_acqrel_acquire, .Lfunc_end350-cxchgweak_16_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchgweak_16_acquire_acquire,"ax",@progbits
	.globl	cxchgweak_16_acquire_acquire
	.prefalign	4, .Lfunc_end351, nop
	.type	cxchgweak_16_acquire_acquire,@function
cxchgweak_16_acquire_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end351:
	.size	cxchgweak_16_acquire_acquire, .Lfunc_end351-cxchgweak_16_acquire_acquire
	.cfi_endproc

	.section	.text.cxchgweak_16_relaxed_relaxed,"ax",@progbits
	.globl	cxchgweak_16_relaxed_relaxed
	.prefalign	4, .Lfunc_end352, nop
	.type	cxchgweak_16_relaxed_relaxed,@function
cxchgweak_16_relaxed_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end352:
	.size	cxchgweak_16_relaxed_relaxed, .Lfunc_end352-cxchgweak_16_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_16_release_relaxed,"ax",@progbits
	.globl	cxchgweak_16_release_relaxed
	.prefalign	4, .Lfunc_end353, nop
	.type	cxchgweak_16_release_relaxed,@function
cxchgweak_16_release_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end353:
	.size	cxchgweak_16_release_relaxed, .Lfunc_end353-cxchgweak_16_release_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_16_seqcst_relaxed,"ax",@progbits
	.globl	cxchgweak_16_seqcst_relaxed
	.prefalign	4, .Lfunc_end354, nop
	.type	cxchgweak_16_seqcst_relaxed,@function
cxchgweak_16_seqcst_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end354:
	.size	cxchgweak_16_seqcst_relaxed, .Lfunc_end354-cxchgweak_16_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_16_seqcst_seqcst,"ax",@progbits
	.globl	cxchgweak_16_seqcst_seqcst
	.prefalign	4, .Lfunc_end355, nop
	.type	cxchgweak_16_seqcst_seqcst,@function
cxchgweak_16_seqcst_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgw	%dx, (%rdi)
	sete	%dl
	retq
.Lfunc_end355:
	.size	cxchgweak_16_seqcst_seqcst, .Lfunc_end355-cxchgweak_16_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchgweak_32_acqrel_acquire,"ax",@progbits
	.globl	cxchgweak_32_acqrel_acquire
	.prefalign	4, .Lfunc_end356, nop
	.type	cxchgweak_32_acqrel_acquire,@function
cxchgweak_32_acqrel_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end356:
	.size	cxchgweak_32_acqrel_acquire, .Lfunc_end356-cxchgweak_32_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchgweak_32_acquire_acquire,"ax",@progbits
	.globl	cxchgweak_32_acquire_acquire
	.prefalign	4, .Lfunc_end357, nop
	.type	cxchgweak_32_acquire_acquire,@function
cxchgweak_32_acquire_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end357:
	.size	cxchgweak_32_acquire_acquire, .Lfunc_end357-cxchgweak_32_acquire_acquire
	.cfi_endproc

	.section	.text.cxchgweak_32_relaxed_relaxed,"ax",@progbits
	.globl	cxchgweak_32_relaxed_relaxed
	.prefalign	4, .Lfunc_end358, nop
	.type	cxchgweak_32_relaxed_relaxed,@function
cxchgweak_32_relaxed_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end358:
	.size	cxchgweak_32_relaxed_relaxed, .Lfunc_end358-cxchgweak_32_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_32_release_relaxed,"ax",@progbits
	.globl	cxchgweak_32_release_relaxed
	.prefalign	4, .Lfunc_end359, nop
	.type	cxchgweak_32_release_relaxed,@function
cxchgweak_32_release_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end359:
	.size	cxchgweak_32_release_relaxed, .Lfunc_end359-cxchgweak_32_release_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_32_seqcst_relaxed,"ax",@progbits
	.globl	cxchgweak_32_seqcst_relaxed
	.prefalign	4, .Lfunc_end360, nop
	.type	cxchgweak_32_seqcst_relaxed,@function
cxchgweak_32_seqcst_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end360:
	.size	cxchgweak_32_seqcst_relaxed, .Lfunc_end360-cxchgweak_32_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_32_seqcst_seqcst,"ax",@progbits
	.globl	cxchgweak_32_seqcst_seqcst
	.prefalign	4, .Lfunc_end361, nop
	.type	cxchgweak_32_seqcst_seqcst,@function
cxchgweak_32_seqcst_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgl	%edx, (%rdi)
	sete	%dl
	retq
.Lfunc_end361:
	.size	cxchgweak_32_seqcst_seqcst, .Lfunc_end361-cxchgweak_32_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchgweak_64_acqrel_acquire,"ax",@progbits
	.globl	cxchgweak_64_acqrel_acquire
	.prefalign	4, .Lfunc_end362, nop
	.type	cxchgweak_64_acqrel_acquire,@function
cxchgweak_64_acqrel_acquire:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end362:
	.size	cxchgweak_64_acqrel_acquire, .Lfunc_end362-cxchgweak_64_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchgweak_64_acquire_acquire,"ax",@progbits
	.globl	cxchgweak_64_acquire_acquire
	.prefalign	4, .Lfunc_end363, nop
	.type	cxchgweak_64_acquire_acquire,@function
cxchgweak_64_acquire_acquire:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end363:
	.size	cxchgweak_64_acquire_acquire, .Lfunc_end363-cxchgweak_64_acquire_acquire
	.cfi_endproc

	.section	.text.cxchgweak_64_relaxed_relaxed,"ax",@progbits
	.globl	cxchgweak_64_relaxed_relaxed
	.prefalign	4, .Lfunc_end364, nop
	.type	cxchgweak_64_relaxed_relaxed,@function
cxchgweak_64_relaxed_relaxed:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end364:
	.size	cxchgweak_64_relaxed_relaxed, .Lfunc_end364-cxchgweak_64_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_64_release_relaxed,"ax",@progbits
	.globl	cxchgweak_64_release_relaxed
	.prefalign	4, .Lfunc_end365, nop
	.type	cxchgweak_64_release_relaxed,@function
cxchgweak_64_release_relaxed:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end365:
	.size	cxchgweak_64_release_relaxed, .Lfunc_end365-cxchgweak_64_release_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_64_seqcst_relaxed,"ax",@progbits
	.globl	cxchgweak_64_seqcst_relaxed
	.prefalign	4, .Lfunc_end366, nop
	.type	cxchgweak_64_seqcst_relaxed,@function
cxchgweak_64_seqcst_relaxed:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end366:
	.size	cxchgweak_64_seqcst_relaxed, .Lfunc_end366-cxchgweak_64_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_64_seqcst_seqcst,"ax",@progbits
	.globl	cxchgweak_64_seqcst_seqcst
	.prefalign	4, .Lfunc_end367, nop
	.type	cxchgweak_64_seqcst_seqcst,@function
cxchgweak_64_seqcst_seqcst:
	.cfi_startproc
	movq	%rsi, %rax
	lock		cmpxchgq	%rdx, (%rdi)
	sete	%dl
	retq
.Lfunc_end367:
	.size	cxchgweak_64_seqcst_seqcst, .Lfunc_end367-cxchgweak_64_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchgweak_8_acqrel_acquire,"ax",@progbits
	.globl	cxchgweak_8_acqrel_acquire
	.prefalign	4, .Lfunc_end368, nop
	.type	cxchgweak_8_acqrel_acquire,@function
cxchgweak_8_acqrel_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end368:
	.size	cxchgweak_8_acqrel_acquire, .Lfunc_end368-cxchgweak_8_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchgweak_8_acquire_acquire,"ax",@progbits
	.globl	cxchgweak_8_acquire_acquire
	.prefalign	4, .Lfunc_end369, nop
	.type	cxchgweak_8_acquire_acquire,@function
cxchgweak_8_acquire_acquire:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end369:
	.size	cxchgweak_8_acquire_acquire, .Lfunc_end369-cxchgweak_8_acquire_acquire
	.cfi_endproc

	.section	.text.cxchgweak_8_relaxed_relaxed,"ax",@progbits
	.globl	cxchgweak_8_relaxed_relaxed
	.prefalign	4, .Lfunc_end370, nop
	.type	cxchgweak_8_relaxed_relaxed,@function
cxchgweak_8_relaxed_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end370:
	.size	cxchgweak_8_relaxed_relaxed, .Lfunc_end370-cxchgweak_8_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_8_release_relaxed,"ax",@progbits
	.globl	cxchgweak_8_release_relaxed
	.prefalign	4, .Lfunc_end371, nop
	.type	cxchgweak_8_release_relaxed,@function
cxchgweak_8_release_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end371:
	.size	cxchgweak_8_release_relaxed, .Lfunc_end371-cxchgweak_8_release_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_8_seqcst_relaxed,"ax",@progbits
	.globl	cxchgweak_8_seqcst_relaxed
	.prefalign	4, .Lfunc_end372, nop
	.type	cxchgweak_8_seqcst_relaxed,@function
cxchgweak_8_seqcst_relaxed:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end372:
	.size	cxchgweak_8_seqcst_relaxed, .Lfunc_end372-cxchgweak_8_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_8_seqcst_seqcst,"ax",@progbits
	.globl	cxchgweak_8_seqcst_seqcst
	.prefalign	4, .Lfunc_end373, nop
	.type	cxchgweak_8_seqcst_seqcst,@function
cxchgweak_8_seqcst_seqcst:
	.cfi_startproc
	movl	%esi, %eax
	lock		cmpxchgb	%dl, (%rdi)
	sete	%dl
	retq
.Lfunc_end373:
	.size	cxchgweak_8_seqcst_seqcst, .Lfunc_end373-cxchgweak_8_seqcst_seqcst
	.cfi_endproc

	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
