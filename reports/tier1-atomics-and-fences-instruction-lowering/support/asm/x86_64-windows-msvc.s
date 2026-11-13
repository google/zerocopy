	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.att_syntax
	.file	"atomic_probe.15283d9b12ef6327-cgu.0"
	.def	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,unique,0
	.globl	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.p2align	4
_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind:
	.p2align	4
.LBB0_1:
	jmp	.LBB0_1

	.def	atomic_and_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_128_acqrel,unique,1
	.globl	atomic_and_128_acqrel
	.p2align	4
atomic_and_128_acqrel:
.seh_proc atomic_and_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB1_1:
	movq	%rax, %rbx
	andq	%r9, %rbx
	movq	%rdx, %rcx
	andq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB1_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_and_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_128_acquire,unique,2
	.globl	atomic_and_128_acquire
	.p2align	4
atomic_and_128_acquire:
.seh_proc atomic_and_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB2_1:
	movq	%rax, %rbx
	andq	%r9, %rbx
	movq	%rdx, %rcx
	andq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB2_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_and_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_128_relaxed,unique,3
	.globl	atomic_and_128_relaxed
	.p2align	4
atomic_and_128_relaxed:
.seh_proc atomic_and_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB3_1:
	movq	%rax, %rbx
	andq	%r9, %rbx
	movq	%rdx, %rcx
	andq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB3_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_and_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_128_release,unique,4
	.globl	atomic_and_128_release
	.p2align	4
atomic_and_128_release:
.seh_proc atomic_and_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB4_1:
	movq	%rax, %rbx
	andq	%r9, %rbx
	movq	%rdx, %rcx
	andq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB4_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_and_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_128_seqcst,unique,5
	.globl	atomic_and_128_seqcst
	.p2align	4
atomic_and_128_seqcst:
.seh_proc atomic_and_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB5_1:
	movq	%rax, %rbx
	andq	%r9, %rbx
	movq	%rdx, %rcx
	andq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB5_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_and_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_16_acqrel,unique,6
	.globl	atomic_and_16_acqrel
	.p2align	4
atomic_and_16_acqrel:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB6_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB6_1
	retq

	.def	atomic_and_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_16_acquire,unique,7
	.globl	atomic_and_16_acquire
	.p2align	4
atomic_and_16_acquire:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB7_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB7_1
	retq

	.def	atomic_and_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_16_relaxed,unique,8
	.globl	atomic_and_16_relaxed
	.p2align	4
atomic_and_16_relaxed:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB8_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB8_1
	retq

	.def	atomic_and_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_16_release,unique,9
	.globl	atomic_and_16_release
	.p2align	4
atomic_and_16_release:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB9_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB9_1
	retq

	.def	atomic_and_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_16_seqcst,unique,10
	.globl	atomic_and_16_seqcst
	.p2align	4
atomic_and_16_seqcst:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB10_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB10_1
	retq

	.def	atomic_and_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_32_acqrel,unique,11
	.globl	atomic_and_32_acqrel
	.p2align	4
atomic_and_32_acqrel:
	movl	(%rcx), %eax
	.p2align	4
.LBB11_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB11_1
	retq

	.def	atomic_and_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_32_acquire,unique,12
	.globl	atomic_and_32_acquire
	.p2align	4
atomic_and_32_acquire:
	movl	(%rcx), %eax
	.p2align	4
.LBB12_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB12_1
	retq

	.def	atomic_and_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_32_relaxed,unique,13
	.globl	atomic_and_32_relaxed
	.p2align	4
atomic_and_32_relaxed:
	movl	(%rcx), %eax
	.p2align	4
.LBB13_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB13_1
	retq

	.def	atomic_and_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_32_release,unique,14
	.globl	atomic_and_32_release
	.p2align	4
atomic_and_32_release:
	movl	(%rcx), %eax
	.p2align	4
.LBB14_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB14_1
	retq

	.def	atomic_and_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_32_seqcst,unique,15
	.globl	atomic_and_32_seqcst
	.p2align	4
atomic_and_32_seqcst:
	movl	(%rcx), %eax
	.p2align	4
.LBB15_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB15_1
	retq

	.def	atomic_and_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_64_acqrel,unique,16
	.globl	atomic_and_64_acqrel
	.p2align	4
atomic_and_64_acqrel:
	movq	(%rcx), %rax
	.p2align	4
.LBB16_1:
	movq	%rax, %r8
	andq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB16_1
	retq

	.def	atomic_and_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_64_acquire,unique,17
	.globl	atomic_and_64_acquire
	.p2align	4
atomic_and_64_acquire:
	movq	(%rcx), %rax
	.p2align	4
.LBB17_1:
	movq	%rax, %r8
	andq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB17_1
	retq

	.def	atomic_and_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_64_relaxed,unique,18
	.globl	atomic_and_64_relaxed
	.p2align	4
atomic_and_64_relaxed:
	movq	(%rcx), %rax
	.p2align	4
.LBB18_1:
	movq	%rax, %r8
	andq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB18_1
	retq

	.def	atomic_and_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_64_release,unique,19
	.globl	atomic_and_64_release
	.p2align	4
atomic_and_64_release:
	movq	(%rcx), %rax
	.p2align	4
.LBB19_1:
	movq	%rax, %r8
	andq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB19_1
	retq

	.def	atomic_and_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_64_seqcst,unique,20
	.globl	atomic_and_64_seqcst
	.p2align	4
atomic_and_64_seqcst:
	movq	(%rcx), %rax
	.p2align	4
.LBB20_1:
	movq	%rax, %r8
	andq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB20_1
	retq

	.def	atomic_and_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_8_acqrel,unique,21
	.globl	atomic_and_8_acqrel
	.p2align	4
atomic_and_8_acqrel:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB21_1:
	movl	%eax, %r8d
	andb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB21_1
	retq

	.def	atomic_and_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_8_acquire,unique,22
	.globl	atomic_and_8_acquire
	.p2align	4
atomic_and_8_acquire:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB22_1:
	movl	%eax, %r8d
	andb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB22_1
	retq

	.def	atomic_and_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_8_relaxed,unique,23
	.globl	atomic_and_8_relaxed
	.p2align	4
atomic_and_8_relaxed:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB23_1:
	movl	%eax, %r8d
	andb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB23_1
	retq

	.def	atomic_and_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_8_release,unique,24
	.globl	atomic_and_8_release
	.p2align	4
atomic_and_8_release:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB24_1:
	movl	%eax, %r8d
	andb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB24_1
	retq

	.def	atomic_and_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_and_8_seqcst,unique,25
	.globl	atomic_and_8_seqcst
	.p2align	4
atomic_and_8_seqcst:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB25_1:
	movl	%eax, %r8d
	andb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB25_1
	retq

	.def	atomic_compiler_fence_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_compiler_fence_acqrel,unique,26
	.globl	atomic_compiler_fence_acqrel
	.p2align	4
atomic_compiler_fence_acqrel:
	#MEMBARRIER
	retq

	.def	atomic_compiler_fence_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_compiler_fence_acquire,unique,27
	.globl	atomic_compiler_fence_acquire
	.p2align	4
atomic_compiler_fence_acquire:
	#MEMBARRIER
	retq

	.def	atomic_compiler_fence_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_compiler_fence_release,unique,28
	.globl	atomic_compiler_fence_release
	.p2align	4
atomic_compiler_fence_release:
	#MEMBARRIER
	retq

	.def	atomic_compiler_fence_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_compiler_fence_seqcst,unique,29
	.globl	atomic_compiler_fence_seqcst
	.p2align	4
atomic_compiler_fence_seqcst:
	#MEMBARRIER
	retq

	.def	atomic_fence_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_fence_acqrel,unique,30
	.globl	atomic_fence_acqrel
	.p2align	4
atomic_fence_acqrel:
	#MEMBARRIER
	retq

	.def	atomic_fence_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_fence_acquire,unique,31
	.globl	atomic_fence_acquire
	.p2align	4
atomic_fence_acquire:
	#MEMBARRIER
	retq

	.def	atomic_fence_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_fence_release,unique,32
	.globl	atomic_fence_release
	.p2align	4
atomic_fence_release:
	#MEMBARRIER
	retq

	.def	atomic_fence_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_fence_seqcst,unique,33
	.globl	atomic_fence_seqcst
	.p2align	4
atomic_fence_seqcst:
	lock		orl	$0, (%rsp)
	retq

	.def	atomic_load_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_128_acquire,unique,34
	.globl	atomic_load_128_acquire
	.p2align	4
atomic_load_128_acquire:
.seh_proc atomic_load_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rcx, %r8
	xorl	%eax, %eax
	xorl	%edx, %edx
	xorl	%ecx, %ecx
	xorl	%ebx, %ebx
	lock		cmpxchg16b	(%r8)
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_load_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_128_relaxed,unique,35
	.globl	atomic_load_128_relaxed
	.p2align	4
atomic_load_128_relaxed:
.seh_proc atomic_load_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rcx, %r8
	xorl	%eax, %eax
	xorl	%edx, %edx
	xorl	%ecx, %ecx
	xorl	%ebx, %ebx
	lock		cmpxchg16b	(%r8)
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_load_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_128_seqcst,unique,36
	.globl	atomic_load_128_seqcst
	.p2align	4
atomic_load_128_seqcst:
.seh_proc atomic_load_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rcx, %r8
	xorl	%eax, %eax
	xorl	%edx, %edx
	xorl	%ecx, %ecx
	xorl	%ebx, %ebx
	lock		cmpxchg16b	(%r8)
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_load_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_16_acquire,unique,37
	.globl	atomic_load_16_acquire
	.p2align	4
atomic_load_16_acquire:
	movzwl	(%rcx), %eax
	retq

	.def	atomic_load_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_16_relaxed,unique,38
	.globl	atomic_load_16_relaxed
	.p2align	4
atomic_load_16_relaxed:
	movzwl	(%rcx), %eax
	retq

	.def	atomic_load_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_16_seqcst,unique,39
	.globl	atomic_load_16_seqcst
	.p2align	4
atomic_load_16_seqcst:
	movzwl	(%rcx), %eax
	retq

	.def	atomic_load_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_32_acquire,unique,40
	.globl	atomic_load_32_acquire
	.p2align	4
atomic_load_32_acquire:
	movl	(%rcx), %eax
	retq

	.def	atomic_load_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_32_relaxed,unique,41
	.globl	atomic_load_32_relaxed
	.p2align	4
atomic_load_32_relaxed:
	movl	(%rcx), %eax
	retq

	.def	atomic_load_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_32_seqcst,unique,42
	.globl	atomic_load_32_seqcst
	.p2align	4
atomic_load_32_seqcst:
	movl	(%rcx), %eax
	retq

	.def	atomic_load_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_64_acquire,unique,43
	.globl	atomic_load_64_acquire
	.p2align	4
atomic_load_64_acquire:
	movq	(%rcx), %rax
	retq

	.def	atomic_load_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_64_relaxed,unique,44
	.globl	atomic_load_64_relaxed
	.p2align	4
atomic_load_64_relaxed:
	movq	(%rcx), %rax
	retq

	.def	atomic_load_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_64_seqcst,unique,45
	.globl	atomic_load_64_seqcst
	.p2align	4
atomic_load_64_seqcst:
	movq	(%rcx), %rax
	retq

	.def	atomic_load_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_8_acquire,unique,46
	.globl	atomic_load_8_acquire
	.p2align	4
atomic_load_8_acquire:
	movzbl	(%rcx), %eax
	retq

	.def	atomic_load_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_8_relaxed,unique,47
	.globl	atomic_load_8_relaxed
	.p2align	4
atomic_load_8_relaxed:
	movzbl	(%rcx), %eax
	retq

	.def	atomic_load_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_load_8_seqcst,unique,48
	.globl	atomic_load_8_seqcst
	.p2align	4
atomic_load_8_seqcst:
	movzbl	(%rcx), %eax
	retq

	.def	atomic_max_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_128_acqrel,unique,49
	.globl	atomic_max_128_acqrel
	.p2align	4
atomic_max_128_acqrel:
.seh_proc atomic_max_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB49_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovlq	%rdx, %rcx
	movq	%r9, %rbx
	cmovlq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB49_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_max_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_128_acquire,unique,50
	.globl	atomic_max_128_acquire
	.p2align	4
atomic_max_128_acquire:
.seh_proc atomic_max_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB50_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovlq	%rdx, %rcx
	movq	%r9, %rbx
	cmovlq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB50_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_max_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_128_relaxed,unique,51
	.globl	atomic_max_128_relaxed
	.p2align	4
atomic_max_128_relaxed:
.seh_proc atomic_max_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB51_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovlq	%rdx, %rcx
	movq	%r9, %rbx
	cmovlq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB51_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_max_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_128_release,unique,52
	.globl	atomic_max_128_release
	.p2align	4
atomic_max_128_release:
.seh_proc atomic_max_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB52_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovlq	%rdx, %rcx
	movq	%r9, %rbx
	cmovlq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB52_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_max_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_128_seqcst,unique,53
	.globl	atomic_max_128_seqcst
	.p2align	4
atomic_max_128_seqcst:
.seh_proc atomic_max_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB53_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovlq	%rdx, %rcx
	movq	%r9, %rbx
	cmovlq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB53_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_max_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_16_acqrel,unique,54
	.globl	atomic_max_16_acqrel
	.p2align	4
atomic_max_16_acqrel:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB54_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB54_1
	retq

	.def	atomic_max_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_16_acquire,unique,55
	.globl	atomic_max_16_acquire
	.p2align	4
atomic_max_16_acquire:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB55_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB55_1
	retq

	.def	atomic_max_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_16_relaxed,unique,56
	.globl	atomic_max_16_relaxed
	.p2align	4
atomic_max_16_relaxed:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB56_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB56_1
	retq

	.def	atomic_max_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_16_release,unique,57
	.globl	atomic_max_16_release
	.p2align	4
atomic_max_16_release:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB57_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB57_1
	retq

	.def	atomic_max_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_16_seqcst,unique,58
	.globl	atomic_max_16_seqcst
	.p2align	4
atomic_max_16_seqcst:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB58_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB58_1
	retq

	.def	atomic_max_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_32_acqrel,unique,59
	.globl	atomic_max_32_acqrel
	.p2align	4
atomic_max_32_acqrel:
	movl	(%rcx), %eax
	.p2align	4
.LBB59_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB59_1
	retq

	.def	atomic_max_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_32_acquire,unique,60
	.globl	atomic_max_32_acquire
	.p2align	4
atomic_max_32_acquire:
	movl	(%rcx), %eax
	.p2align	4
.LBB60_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB60_1
	retq

	.def	atomic_max_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_32_relaxed,unique,61
	.globl	atomic_max_32_relaxed
	.p2align	4
atomic_max_32_relaxed:
	movl	(%rcx), %eax
	.p2align	4
.LBB61_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB61_1
	retq

	.def	atomic_max_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_32_release,unique,62
	.globl	atomic_max_32_release
	.p2align	4
atomic_max_32_release:
	movl	(%rcx), %eax
	.p2align	4
.LBB62_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB62_1
	retq

	.def	atomic_max_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_32_seqcst,unique,63
	.globl	atomic_max_32_seqcst
	.p2align	4
atomic_max_32_seqcst:
	movl	(%rcx), %eax
	.p2align	4
.LBB63_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB63_1
	retq

	.def	atomic_max_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_64_acqrel,unique,64
	.globl	atomic_max_64_acqrel
	.p2align	4
atomic_max_64_acqrel:
	movq	(%rcx), %rax
	.p2align	4
.LBB64_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovgq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB64_1
	retq

	.def	atomic_max_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_64_acquire,unique,65
	.globl	atomic_max_64_acquire
	.p2align	4
atomic_max_64_acquire:
	movq	(%rcx), %rax
	.p2align	4
.LBB65_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovgq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB65_1
	retq

	.def	atomic_max_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_64_relaxed,unique,66
	.globl	atomic_max_64_relaxed
	.p2align	4
atomic_max_64_relaxed:
	movq	(%rcx), %rax
	.p2align	4
.LBB66_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovgq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB66_1
	retq

	.def	atomic_max_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_64_release,unique,67
	.globl	atomic_max_64_release
	.p2align	4
atomic_max_64_release:
	movq	(%rcx), %rax
	.p2align	4
.LBB67_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovgq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB67_1
	retq

	.def	atomic_max_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_64_seqcst,unique,68
	.globl	atomic_max_64_seqcst
	.p2align	4
atomic_max_64_seqcst:
	movq	(%rcx), %rax
	.p2align	4
.LBB68_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovgq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB68_1
	retq

	.def	atomic_max_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_8_acqrel,unique,69
	.globl	atomic_max_8_acqrel
	.p2align	4
atomic_max_8_acqrel:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB69_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB69_1
	retq

	.def	atomic_max_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_8_acquire,unique,70
	.globl	atomic_max_8_acquire
	.p2align	4
atomic_max_8_acquire:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB70_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB70_1
	retq

	.def	atomic_max_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_8_relaxed,unique,71
	.globl	atomic_max_8_relaxed
	.p2align	4
atomic_max_8_relaxed:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB71_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB71_1
	retq

	.def	atomic_max_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_8_release,unique,72
	.globl	atomic_max_8_release
	.p2align	4
atomic_max_8_release:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB72_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB72_1
	retq

	.def	atomic_max_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_max_8_seqcst,unique,73
	.globl	atomic_max_8_seqcst
	.p2align	4
atomic_max_8_seqcst:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB73_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovgl	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB73_1
	retq

	.def	atomic_min_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_128_acqrel,unique,74
	.globl	atomic_min_128_acqrel
	.p2align	4
atomic_min_128_acqrel:
.seh_proc atomic_min_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB74_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovgeq	%rdx, %rcx
	movq	%r9, %rbx
	cmovgeq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB74_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_min_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_128_acquire,unique,75
	.globl	atomic_min_128_acquire
	.p2align	4
atomic_min_128_acquire:
.seh_proc atomic_min_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB75_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovgeq	%rdx, %rcx
	movq	%r9, %rbx
	cmovgeq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB75_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_min_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_128_relaxed,unique,76
	.globl	atomic_min_128_relaxed
	.p2align	4
atomic_min_128_relaxed:
.seh_proc atomic_min_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB76_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovgeq	%rdx, %rcx
	movq	%r9, %rbx
	cmovgeq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB76_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_min_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_128_release,unique,77
	.globl	atomic_min_128_release
	.p2align	4
atomic_min_128_release:
.seh_proc atomic_min_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB77_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovgeq	%rdx, %rcx
	movq	%r9, %rbx
	cmovgeq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB77_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_min_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_128_seqcst,unique,78
	.globl	atomic_min_128_seqcst
	.p2align	4
atomic_min_128_seqcst:
.seh_proc atomic_min_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB78_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovgeq	%rdx, %rcx
	movq	%r9, %rbx
	cmovgeq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB78_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_min_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_16_acqrel,unique,79
	.globl	atomic_min_16_acqrel
	.p2align	4
atomic_min_16_acqrel:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB79_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB79_1
	retq

	.def	atomic_min_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_16_acquire,unique,80
	.globl	atomic_min_16_acquire
	.p2align	4
atomic_min_16_acquire:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB80_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB80_1
	retq

	.def	atomic_min_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_16_relaxed,unique,81
	.globl	atomic_min_16_relaxed
	.p2align	4
atomic_min_16_relaxed:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB81_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB81_1
	retq

	.def	atomic_min_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_16_release,unique,82
	.globl	atomic_min_16_release
	.p2align	4
atomic_min_16_release:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB82_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB82_1
	retq

	.def	atomic_min_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_16_seqcst,unique,83
	.globl	atomic_min_16_seqcst
	.p2align	4
atomic_min_16_seqcst:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB83_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB83_1
	retq

	.def	atomic_min_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_32_acqrel,unique,84
	.globl	atomic_min_32_acqrel
	.p2align	4
atomic_min_32_acqrel:
	movl	(%rcx), %eax
	.p2align	4
.LBB84_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB84_1
	retq

	.def	atomic_min_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_32_acquire,unique,85
	.globl	atomic_min_32_acquire
	.p2align	4
atomic_min_32_acquire:
	movl	(%rcx), %eax
	.p2align	4
.LBB85_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB85_1
	retq

	.def	atomic_min_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_32_relaxed,unique,86
	.globl	atomic_min_32_relaxed
	.p2align	4
atomic_min_32_relaxed:
	movl	(%rcx), %eax
	.p2align	4
.LBB86_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB86_1
	retq

	.def	atomic_min_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_32_release,unique,87
	.globl	atomic_min_32_release
	.p2align	4
atomic_min_32_release:
	movl	(%rcx), %eax
	.p2align	4
.LBB87_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB87_1
	retq

	.def	atomic_min_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_32_seqcst,unique,88
	.globl	atomic_min_32_seqcst
	.p2align	4
atomic_min_32_seqcst:
	movl	(%rcx), %eax
	.p2align	4
.LBB88_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB88_1
	retq

	.def	atomic_min_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_64_acqrel,unique,89
	.globl	atomic_min_64_acqrel
	.p2align	4
atomic_min_64_acqrel:
	movq	(%rcx), %rax
	.p2align	4
.LBB89_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovleq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB89_1
	retq

	.def	atomic_min_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_64_acquire,unique,90
	.globl	atomic_min_64_acquire
	.p2align	4
atomic_min_64_acquire:
	movq	(%rcx), %rax
	.p2align	4
.LBB90_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovleq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB90_1
	retq

	.def	atomic_min_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_64_relaxed,unique,91
	.globl	atomic_min_64_relaxed
	.p2align	4
atomic_min_64_relaxed:
	movq	(%rcx), %rax
	.p2align	4
.LBB91_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovleq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB91_1
	retq

	.def	atomic_min_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_64_release,unique,92
	.globl	atomic_min_64_release
	.p2align	4
atomic_min_64_release:
	movq	(%rcx), %rax
	.p2align	4
.LBB92_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovleq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB92_1
	retq

	.def	atomic_min_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_64_seqcst,unique,93
	.globl	atomic_min_64_seqcst
	.p2align	4
atomic_min_64_seqcst:
	movq	(%rcx), %rax
	.p2align	4
.LBB93_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovleq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB93_1
	retq

	.def	atomic_min_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_8_acqrel,unique,94
	.globl	atomic_min_8_acqrel
	.p2align	4
atomic_min_8_acqrel:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB94_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB94_1
	retq

	.def	atomic_min_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_8_acquire,unique,95
	.globl	atomic_min_8_acquire
	.p2align	4
atomic_min_8_acquire:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB95_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB95_1
	retq

	.def	atomic_min_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_8_relaxed,unique,96
	.globl	atomic_min_8_relaxed
	.p2align	4
atomic_min_8_relaxed:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB96_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB96_1
	retq

	.def	atomic_min_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_8_release,unique,97
	.globl	atomic_min_8_release
	.p2align	4
atomic_min_8_release:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB97_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB97_1
	retq

	.def	atomic_min_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_min_8_seqcst,unique,98
	.globl	atomic_min_8_seqcst
	.p2align	4
atomic_min_8_seqcst:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB98_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovlel	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB98_1
	retq

	.def	atomic_nand_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_128_acqrel,unique,99
	.globl	atomic_nand_128_acqrel
	.p2align	4
atomic_nand_128_acqrel:
.seh_proc atomic_nand_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB99_1:
	movq	%rdx, %rcx
	andq	%r8, %rcx
	movq	%rax, %rbx
	andq	%r9, %rbx
	notq	%rbx
	notq	%rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB99_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_nand_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_128_acquire,unique,100
	.globl	atomic_nand_128_acquire
	.p2align	4
atomic_nand_128_acquire:
.seh_proc atomic_nand_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB100_1:
	movq	%rdx, %rcx
	andq	%r8, %rcx
	movq	%rax, %rbx
	andq	%r9, %rbx
	notq	%rbx
	notq	%rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB100_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_nand_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_128_relaxed,unique,101
	.globl	atomic_nand_128_relaxed
	.p2align	4
atomic_nand_128_relaxed:
.seh_proc atomic_nand_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB101_1:
	movq	%rdx, %rcx
	andq	%r8, %rcx
	movq	%rax, %rbx
	andq	%r9, %rbx
	notq	%rbx
	notq	%rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB101_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_nand_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_128_release,unique,102
	.globl	atomic_nand_128_release
	.p2align	4
atomic_nand_128_release:
.seh_proc atomic_nand_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB102_1:
	movq	%rdx, %rcx
	andq	%r8, %rcx
	movq	%rax, %rbx
	andq	%r9, %rbx
	notq	%rbx
	notq	%rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB102_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_nand_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_128_seqcst,unique,103
	.globl	atomic_nand_128_seqcst
	.p2align	4
atomic_nand_128_seqcst:
.seh_proc atomic_nand_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB103_1:
	movq	%rdx, %rcx
	andq	%r8, %rcx
	movq	%rax, %rbx
	andq	%r9, %rbx
	notq	%rbx
	notq	%rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB103_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_nand_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_16_acqrel,unique,104
	.globl	atomic_nand_16_acqrel
	.p2align	4
atomic_nand_16_acqrel:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB104_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	notl	%r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB104_1
	retq

	.def	atomic_nand_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_16_acquire,unique,105
	.globl	atomic_nand_16_acquire
	.p2align	4
atomic_nand_16_acquire:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB105_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	notl	%r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB105_1
	retq

	.def	atomic_nand_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_16_relaxed,unique,106
	.globl	atomic_nand_16_relaxed
	.p2align	4
atomic_nand_16_relaxed:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB106_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	notl	%r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB106_1
	retq

	.def	atomic_nand_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_16_release,unique,107
	.globl	atomic_nand_16_release
	.p2align	4
atomic_nand_16_release:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB107_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	notl	%r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB107_1
	retq

	.def	atomic_nand_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_16_seqcst,unique,108
	.globl	atomic_nand_16_seqcst
	.p2align	4
atomic_nand_16_seqcst:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB108_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	notl	%r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB108_1
	retq

	.def	atomic_nand_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_32_acqrel,unique,109
	.globl	atomic_nand_32_acqrel
	.p2align	4
atomic_nand_32_acqrel:
	movl	(%rcx), %eax
	.p2align	4
.LBB109_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	notl	%r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB109_1
	retq

	.def	atomic_nand_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_32_acquire,unique,110
	.globl	atomic_nand_32_acquire
	.p2align	4
atomic_nand_32_acquire:
	movl	(%rcx), %eax
	.p2align	4
.LBB110_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	notl	%r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB110_1
	retq

	.def	atomic_nand_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_32_relaxed,unique,111
	.globl	atomic_nand_32_relaxed
	.p2align	4
atomic_nand_32_relaxed:
	movl	(%rcx), %eax
	.p2align	4
.LBB111_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	notl	%r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB111_1
	retq

	.def	atomic_nand_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_32_release,unique,112
	.globl	atomic_nand_32_release
	.p2align	4
atomic_nand_32_release:
	movl	(%rcx), %eax
	.p2align	4
.LBB112_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	notl	%r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB112_1
	retq

	.def	atomic_nand_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_32_seqcst,unique,113
	.globl	atomic_nand_32_seqcst
	.p2align	4
atomic_nand_32_seqcst:
	movl	(%rcx), %eax
	.p2align	4
.LBB113_1:
	movl	%eax, %r8d
	andl	%edx, %r8d
	notl	%r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB113_1
	retq

	.def	atomic_nand_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_64_acqrel,unique,114
	.globl	atomic_nand_64_acqrel
	.p2align	4
atomic_nand_64_acqrel:
	movq	(%rcx), %rax
	.p2align	4
.LBB114_1:
	movq	%rax, %r8
	andq	%rdx, %r8
	notq	%r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB114_1
	retq

	.def	atomic_nand_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_64_acquire,unique,115
	.globl	atomic_nand_64_acquire
	.p2align	4
atomic_nand_64_acquire:
	movq	(%rcx), %rax
	.p2align	4
.LBB115_1:
	movq	%rax, %r8
	andq	%rdx, %r8
	notq	%r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB115_1
	retq

	.def	atomic_nand_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_64_relaxed,unique,116
	.globl	atomic_nand_64_relaxed
	.p2align	4
atomic_nand_64_relaxed:
	movq	(%rcx), %rax
	.p2align	4
.LBB116_1:
	movq	%rax, %r8
	andq	%rdx, %r8
	notq	%r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB116_1
	retq

	.def	atomic_nand_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_64_release,unique,117
	.globl	atomic_nand_64_release
	.p2align	4
atomic_nand_64_release:
	movq	(%rcx), %rax
	.p2align	4
.LBB117_1:
	movq	%rax, %r8
	andq	%rdx, %r8
	notq	%r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB117_1
	retq

	.def	atomic_nand_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_64_seqcst,unique,118
	.globl	atomic_nand_64_seqcst
	.p2align	4
atomic_nand_64_seqcst:
	movq	(%rcx), %rax
	.p2align	4
.LBB118_1:
	movq	%rax, %r8
	andq	%rdx, %r8
	notq	%r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB118_1
	retq

	.def	atomic_nand_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_8_acqrel,unique,119
	.globl	atomic_nand_8_acqrel
	.p2align	4
atomic_nand_8_acqrel:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB119_1:
	movl	%eax, %r8d
	andb	%dl, %r8b
	notb	%r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB119_1
	retq

	.def	atomic_nand_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_8_acquire,unique,120
	.globl	atomic_nand_8_acquire
	.p2align	4
atomic_nand_8_acquire:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB120_1:
	movl	%eax, %r8d
	andb	%dl, %r8b
	notb	%r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB120_1
	retq

	.def	atomic_nand_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_8_relaxed,unique,121
	.globl	atomic_nand_8_relaxed
	.p2align	4
atomic_nand_8_relaxed:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB121_1:
	movl	%eax, %r8d
	andb	%dl, %r8b
	notb	%r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB121_1
	retq

	.def	atomic_nand_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_8_release,unique,122
	.globl	atomic_nand_8_release
	.p2align	4
atomic_nand_8_release:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB122_1:
	movl	%eax, %r8d
	andb	%dl, %r8b
	notb	%r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB122_1
	retq

	.def	atomic_nand_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_nand_8_seqcst,unique,123
	.globl	atomic_nand_8_seqcst
	.p2align	4
atomic_nand_8_seqcst:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB123_1:
	movl	%eax, %r8d
	andb	%dl, %r8b
	notb	%r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB123_1
	retq

	.def	atomic_or_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_128_acqrel,unique,124
	.globl	atomic_or_128_acqrel
	.p2align	4
atomic_or_128_acqrel:
.seh_proc atomic_or_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB124_1:
	movq	%rax, %rbx
	orq	%r9, %rbx
	movq	%rdx, %rcx
	orq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB124_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_or_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_128_acquire,unique,125
	.globl	atomic_or_128_acquire
	.p2align	4
atomic_or_128_acquire:
.seh_proc atomic_or_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB125_1:
	movq	%rax, %rbx
	orq	%r9, %rbx
	movq	%rdx, %rcx
	orq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB125_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_or_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_128_relaxed,unique,126
	.globl	atomic_or_128_relaxed
	.p2align	4
atomic_or_128_relaxed:
.seh_proc atomic_or_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB126_1:
	movq	%rax, %rbx
	orq	%r9, %rbx
	movq	%rdx, %rcx
	orq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB126_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_or_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_128_release,unique,127
	.globl	atomic_or_128_release
	.p2align	4
atomic_or_128_release:
.seh_proc atomic_or_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB127_1:
	movq	%rax, %rbx
	orq	%r9, %rbx
	movq	%rdx, %rcx
	orq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB127_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_or_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_128_seqcst,unique,128
	.globl	atomic_or_128_seqcst
	.p2align	4
atomic_or_128_seqcst:
.seh_proc atomic_or_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB128_1:
	movq	%rax, %rbx
	orq	%r9, %rbx
	movq	%rdx, %rcx
	orq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB128_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_or_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_16_acqrel,unique,129
	.globl	atomic_or_16_acqrel
	.p2align	4
atomic_or_16_acqrel:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB129_1:
	movl	%eax, %r8d
	orl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB129_1
	retq

	.def	atomic_or_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_16_acquire,unique,130
	.globl	atomic_or_16_acquire
	.p2align	4
atomic_or_16_acquire:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB130_1:
	movl	%eax, %r8d
	orl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB130_1
	retq

	.def	atomic_or_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_16_relaxed,unique,131
	.globl	atomic_or_16_relaxed
	.p2align	4
atomic_or_16_relaxed:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB131_1:
	movl	%eax, %r8d
	orl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB131_1
	retq

	.def	atomic_or_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_16_release,unique,132
	.globl	atomic_or_16_release
	.p2align	4
atomic_or_16_release:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB132_1:
	movl	%eax, %r8d
	orl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB132_1
	retq

	.def	atomic_or_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_16_seqcst,unique,133
	.globl	atomic_or_16_seqcst
	.p2align	4
atomic_or_16_seqcst:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB133_1:
	movl	%eax, %r8d
	orl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB133_1
	retq

	.def	atomic_or_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_32_acqrel,unique,134
	.globl	atomic_or_32_acqrel
	.p2align	4
atomic_or_32_acqrel:
	movl	(%rcx), %eax
	.p2align	4
.LBB134_1:
	movl	%eax, %r8d
	orl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB134_1
	retq

	.def	atomic_or_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_32_acquire,unique,135
	.globl	atomic_or_32_acquire
	.p2align	4
atomic_or_32_acquire:
	movl	(%rcx), %eax
	.p2align	4
.LBB135_1:
	movl	%eax, %r8d
	orl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB135_1
	retq

	.def	atomic_or_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_32_relaxed,unique,136
	.globl	atomic_or_32_relaxed
	.p2align	4
atomic_or_32_relaxed:
	movl	(%rcx), %eax
	.p2align	4
.LBB136_1:
	movl	%eax, %r8d
	orl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB136_1
	retq

	.def	atomic_or_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_32_release,unique,137
	.globl	atomic_or_32_release
	.p2align	4
atomic_or_32_release:
	movl	(%rcx), %eax
	.p2align	4
.LBB137_1:
	movl	%eax, %r8d
	orl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB137_1
	retq

	.def	atomic_or_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_32_seqcst,unique,138
	.globl	atomic_or_32_seqcst
	.p2align	4
atomic_or_32_seqcst:
	movl	(%rcx), %eax
	.p2align	4
.LBB138_1:
	movl	%eax, %r8d
	orl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB138_1
	retq

	.def	atomic_or_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_64_acqrel,unique,139
	.globl	atomic_or_64_acqrel
	.p2align	4
atomic_or_64_acqrel:
	movq	(%rcx), %rax
	.p2align	4
.LBB139_1:
	movq	%rax, %r8
	orq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB139_1
	retq

	.def	atomic_or_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_64_acquire,unique,140
	.globl	atomic_or_64_acquire
	.p2align	4
atomic_or_64_acquire:
	movq	(%rcx), %rax
	.p2align	4
.LBB140_1:
	movq	%rax, %r8
	orq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB140_1
	retq

	.def	atomic_or_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_64_relaxed,unique,141
	.globl	atomic_or_64_relaxed
	.p2align	4
atomic_or_64_relaxed:
	movq	(%rcx), %rax
	.p2align	4
.LBB141_1:
	movq	%rax, %r8
	orq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB141_1
	retq

	.def	atomic_or_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_64_release,unique,142
	.globl	atomic_or_64_release
	.p2align	4
atomic_or_64_release:
	movq	(%rcx), %rax
	.p2align	4
.LBB142_1:
	movq	%rax, %r8
	orq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB142_1
	retq

	.def	atomic_or_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_64_seqcst,unique,143
	.globl	atomic_or_64_seqcst
	.p2align	4
atomic_or_64_seqcst:
	movq	(%rcx), %rax
	.p2align	4
.LBB143_1:
	movq	%rax, %r8
	orq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB143_1
	retq

	.def	atomic_or_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_8_acqrel,unique,144
	.globl	atomic_or_8_acqrel
	.p2align	4
atomic_or_8_acqrel:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB144_1:
	movl	%eax, %r8d
	orb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB144_1
	retq

	.def	atomic_or_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_8_acquire,unique,145
	.globl	atomic_or_8_acquire
	.p2align	4
atomic_or_8_acquire:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB145_1:
	movl	%eax, %r8d
	orb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB145_1
	retq

	.def	atomic_or_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_8_relaxed,unique,146
	.globl	atomic_or_8_relaxed
	.p2align	4
atomic_or_8_relaxed:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB146_1:
	movl	%eax, %r8d
	orb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB146_1
	retq

	.def	atomic_or_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_8_release,unique,147
	.globl	atomic_or_8_release
	.p2align	4
atomic_or_8_release:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB147_1:
	movl	%eax, %r8d
	orb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB147_1
	retq

	.def	atomic_or_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_or_8_seqcst,unique,148
	.globl	atomic_or_8_seqcst
	.p2align	4
atomic_or_8_seqcst:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB148_1:
	movl	%eax, %r8d
	orb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB148_1
	retq

	.def	atomic_store_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_128_relaxed,unique,149
	.globl	atomic_store_128_relaxed
	.p2align	4
atomic_store_128_relaxed:
.seh_proc atomic_store_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %rbx
	movq	%rcx, %r9
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB149_1:
	movq	%r8, %rcx
	lock		cmpxchg16b	(%r9)
	jne	.LBB149_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_store_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_128_release,unique,150
	.globl	atomic_store_128_release
	.p2align	4
atomic_store_128_release:
.seh_proc atomic_store_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %rbx
	movq	%rcx, %r9
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB150_1:
	movq	%r8, %rcx
	lock		cmpxchg16b	(%r9)
	jne	.LBB150_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_store_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_128_seqcst,unique,151
	.globl	atomic_store_128_seqcst
	.p2align	4
atomic_store_128_seqcst:
.seh_proc atomic_store_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %rbx
	movq	%rcx, %r9
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB151_1:
	movq	%r8, %rcx
	lock		cmpxchg16b	(%r9)
	jne	.LBB151_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_store_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_16_relaxed,unique,152
	.globl	atomic_store_16_relaxed
	.p2align	4
atomic_store_16_relaxed:
	movw	%dx, (%rcx)
	retq

	.def	atomic_store_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_16_release,unique,153
	.globl	atomic_store_16_release
	.p2align	4
atomic_store_16_release:
	movw	%dx, (%rcx)
	retq

	.def	atomic_store_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_16_seqcst,unique,154
	.globl	atomic_store_16_seqcst
	.p2align	4
atomic_store_16_seqcst:
	xchgw	%dx, (%rcx)
	retq

	.def	atomic_store_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_32_relaxed,unique,155
	.globl	atomic_store_32_relaxed
	.p2align	4
atomic_store_32_relaxed:
	movl	%edx, (%rcx)
	retq

	.def	atomic_store_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_32_release,unique,156
	.globl	atomic_store_32_release
	.p2align	4
atomic_store_32_release:
	movl	%edx, (%rcx)
	retq

	.def	atomic_store_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_32_seqcst,unique,157
	.globl	atomic_store_32_seqcst
	.p2align	4
atomic_store_32_seqcst:
	xchgl	%edx, (%rcx)
	retq

	.def	atomic_store_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_64_relaxed,unique,158
	.globl	atomic_store_64_relaxed
	.p2align	4
atomic_store_64_relaxed:
	movq	%rdx, (%rcx)
	retq

	.def	atomic_store_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_64_release,unique,159
	.globl	atomic_store_64_release
	.p2align	4
atomic_store_64_release:
	movq	%rdx, (%rcx)
	retq

	.def	atomic_store_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_64_seqcst,unique,160
	.globl	atomic_store_64_seqcst
	.p2align	4
atomic_store_64_seqcst:
	xchgq	%rdx, (%rcx)
	retq

	.def	atomic_store_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_8_relaxed,unique,161
	.globl	atomic_store_8_relaxed
	.p2align	4
atomic_store_8_relaxed:
	movb	%dl, (%rcx)
	retq

	.def	atomic_store_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_8_release,unique,162
	.globl	atomic_store_8_release
	.p2align	4
atomic_store_8_release:
	movb	%dl, (%rcx)
	retq

	.def	atomic_store_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_store_8_seqcst,unique,163
	.globl	atomic_store_8_seqcst
	.p2align	4
atomic_store_8_seqcst:
	xchgb	%dl, (%rcx)
	retq

	.def	atomic_umax_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_128_acqrel,unique,164
	.globl	atomic_umax_128_acqrel
	.p2align	4
atomic_umax_128_acqrel:
.seh_proc atomic_umax_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB164_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovbq	%rdx, %rcx
	movq	%r9, %rbx
	cmovbq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB164_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_umax_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_128_acquire,unique,165
	.globl	atomic_umax_128_acquire
	.p2align	4
atomic_umax_128_acquire:
.seh_proc atomic_umax_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB165_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovbq	%rdx, %rcx
	movq	%r9, %rbx
	cmovbq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB165_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_umax_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_128_relaxed,unique,166
	.globl	atomic_umax_128_relaxed
	.p2align	4
atomic_umax_128_relaxed:
.seh_proc atomic_umax_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB166_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovbq	%rdx, %rcx
	movq	%r9, %rbx
	cmovbq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB166_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_umax_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_128_release,unique,167
	.globl	atomic_umax_128_release
	.p2align	4
atomic_umax_128_release:
.seh_proc atomic_umax_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB167_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovbq	%rdx, %rcx
	movq	%r9, %rbx
	cmovbq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB167_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_umax_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_128_seqcst,unique,168
	.globl	atomic_umax_128_seqcst
	.p2align	4
atomic_umax_128_seqcst:
.seh_proc atomic_umax_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB168_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovbq	%rdx, %rcx
	movq	%r9, %rbx
	cmovbq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB168_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_umax_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_16_acqrel,unique,169
	.globl	atomic_umax_16_acqrel
	.p2align	4
atomic_umax_16_acqrel:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB169_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB169_1
	retq

	.def	atomic_umax_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_16_acquire,unique,170
	.globl	atomic_umax_16_acquire
	.p2align	4
atomic_umax_16_acquire:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB170_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB170_1
	retq

	.def	atomic_umax_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_16_relaxed,unique,171
	.globl	atomic_umax_16_relaxed
	.p2align	4
atomic_umax_16_relaxed:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB171_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB171_1
	retq

	.def	atomic_umax_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_16_release,unique,172
	.globl	atomic_umax_16_release
	.p2align	4
atomic_umax_16_release:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB172_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB172_1
	retq

	.def	atomic_umax_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_16_seqcst,unique,173
	.globl	atomic_umax_16_seqcst
	.p2align	4
atomic_umax_16_seqcst:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB173_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB173_1
	retq

	.def	atomic_umax_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_32_acqrel,unique,174
	.globl	atomic_umax_32_acqrel
	.p2align	4
atomic_umax_32_acqrel:
	movl	(%rcx), %eax
	.p2align	4
.LBB174_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB174_1
	retq

	.def	atomic_umax_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_32_acquire,unique,175
	.globl	atomic_umax_32_acquire
	.p2align	4
atomic_umax_32_acquire:
	movl	(%rcx), %eax
	.p2align	4
.LBB175_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB175_1
	retq

	.def	atomic_umax_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_32_relaxed,unique,176
	.globl	atomic_umax_32_relaxed
	.p2align	4
atomic_umax_32_relaxed:
	movl	(%rcx), %eax
	.p2align	4
.LBB176_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB176_1
	retq

	.def	atomic_umax_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_32_release,unique,177
	.globl	atomic_umax_32_release
	.p2align	4
atomic_umax_32_release:
	movl	(%rcx), %eax
	.p2align	4
.LBB177_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB177_1
	retq

	.def	atomic_umax_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_32_seqcst,unique,178
	.globl	atomic_umax_32_seqcst
	.p2align	4
atomic_umax_32_seqcst:
	movl	(%rcx), %eax
	.p2align	4
.LBB178_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB178_1
	retq

	.def	atomic_umax_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_64_acqrel,unique,179
	.globl	atomic_umax_64_acqrel
	.p2align	4
atomic_umax_64_acqrel:
	movq	(%rcx), %rax
	.p2align	4
.LBB179_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovaq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB179_1
	retq

	.def	atomic_umax_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_64_acquire,unique,180
	.globl	atomic_umax_64_acquire
	.p2align	4
atomic_umax_64_acquire:
	movq	(%rcx), %rax
	.p2align	4
.LBB180_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovaq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB180_1
	retq

	.def	atomic_umax_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_64_relaxed,unique,181
	.globl	atomic_umax_64_relaxed
	.p2align	4
atomic_umax_64_relaxed:
	movq	(%rcx), %rax
	.p2align	4
.LBB181_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovaq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB181_1
	retq

	.def	atomic_umax_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_64_release,unique,182
	.globl	atomic_umax_64_release
	.p2align	4
atomic_umax_64_release:
	movq	(%rcx), %rax
	.p2align	4
.LBB182_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovaq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB182_1
	retq

	.def	atomic_umax_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_64_seqcst,unique,183
	.globl	atomic_umax_64_seqcst
	.p2align	4
atomic_umax_64_seqcst:
	movq	(%rcx), %rax
	.p2align	4
.LBB183_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovaq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB183_1
	retq

	.def	atomic_umax_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_8_acqrel,unique,184
	.globl	atomic_umax_8_acqrel
	.p2align	4
atomic_umax_8_acqrel:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB184_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB184_1
	retq

	.def	atomic_umax_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_8_acquire,unique,185
	.globl	atomic_umax_8_acquire
	.p2align	4
atomic_umax_8_acquire:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB185_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB185_1
	retq

	.def	atomic_umax_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_8_relaxed,unique,186
	.globl	atomic_umax_8_relaxed
	.p2align	4
atomic_umax_8_relaxed:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB186_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB186_1
	retq

	.def	atomic_umax_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_8_release,unique,187
	.globl	atomic_umax_8_release
	.p2align	4
atomic_umax_8_release:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB187_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB187_1
	retq

	.def	atomic_umax_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umax_8_seqcst,unique,188
	.globl	atomic_umax_8_seqcst
	.p2align	4
atomic_umax_8_seqcst:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB188_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmoval	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB188_1
	retq

	.def	atomic_umin_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_128_acqrel,unique,189
	.globl	atomic_umin_128_acqrel
	.p2align	4
atomic_umin_128_acqrel:
.seh_proc atomic_umin_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB189_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovaeq	%rdx, %rcx
	movq	%r9, %rbx
	cmovaeq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB189_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_umin_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_128_acquire,unique,190
	.globl	atomic_umin_128_acquire
	.p2align	4
atomic_umin_128_acquire:
.seh_proc atomic_umin_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB190_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovaeq	%rdx, %rcx
	movq	%r9, %rbx
	cmovaeq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB190_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_umin_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_128_relaxed,unique,191
	.globl	atomic_umin_128_relaxed
	.p2align	4
atomic_umin_128_relaxed:
.seh_proc atomic_umin_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB191_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovaeq	%rdx, %rcx
	movq	%r9, %rbx
	cmovaeq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB191_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_umin_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_128_release,unique,192
	.globl	atomic_umin_128_release
	.p2align	4
atomic_umin_128_release:
.seh_proc atomic_umin_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB192_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovaeq	%rdx, %rcx
	movq	%r9, %rbx
	cmovaeq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB192_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_umin_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_128_seqcst,unique,193
	.globl	atomic_umin_128_seqcst
	.p2align	4
atomic_umin_128_seqcst:
.seh_proc atomic_umin_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB193_1:
	cmpq	%rax, %r9
	movq	%r8, %rcx
	sbbq	%rdx, %rcx
	movq	%r8, %rcx
	cmovaeq	%rdx, %rcx
	movq	%r9, %rbx
	cmovaeq	%rax, %rbx
	lock		cmpxchg16b	(%r10)
	jne	.LBB193_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_umin_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_16_acqrel,unique,194
	.globl	atomic_umin_16_acqrel
	.p2align	4
atomic_umin_16_acqrel:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB194_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB194_1
	retq

	.def	atomic_umin_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_16_acquire,unique,195
	.globl	atomic_umin_16_acquire
	.p2align	4
atomic_umin_16_acquire:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB195_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB195_1
	retq

	.def	atomic_umin_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_16_relaxed,unique,196
	.globl	atomic_umin_16_relaxed
	.p2align	4
atomic_umin_16_relaxed:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB196_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB196_1
	retq

	.def	atomic_umin_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_16_release,unique,197
	.globl	atomic_umin_16_release
	.p2align	4
atomic_umin_16_release:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB197_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB197_1
	retq

	.def	atomic_umin_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_16_seqcst,unique,198
	.globl	atomic_umin_16_seqcst
	.p2align	4
atomic_umin_16_seqcst:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB198_1:
	cmpw	%dx, %ax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB198_1
	retq

	.def	atomic_umin_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_32_acqrel,unique,199
	.globl	atomic_umin_32_acqrel
	.p2align	4
atomic_umin_32_acqrel:
	movl	(%rcx), %eax
	.p2align	4
.LBB199_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB199_1
	retq

	.def	atomic_umin_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_32_acquire,unique,200
	.globl	atomic_umin_32_acquire
	.p2align	4
atomic_umin_32_acquire:
	movl	(%rcx), %eax
	.p2align	4
.LBB200_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB200_1
	retq

	.def	atomic_umin_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_32_relaxed,unique,201
	.globl	atomic_umin_32_relaxed
	.p2align	4
atomic_umin_32_relaxed:
	movl	(%rcx), %eax
	.p2align	4
.LBB201_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB201_1
	retq

	.def	atomic_umin_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_32_release,unique,202
	.globl	atomic_umin_32_release
	.p2align	4
atomic_umin_32_release:
	movl	(%rcx), %eax
	.p2align	4
.LBB202_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB202_1
	retq

	.def	atomic_umin_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_32_seqcst,unique,203
	.globl	atomic_umin_32_seqcst
	.p2align	4
atomic_umin_32_seqcst:
	movl	(%rcx), %eax
	.p2align	4
.LBB203_1:
	cmpl	%edx, %eax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB203_1
	retq

	.def	atomic_umin_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_64_acqrel,unique,204
	.globl	atomic_umin_64_acqrel
	.p2align	4
atomic_umin_64_acqrel:
	movq	(%rcx), %rax
	.p2align	4
.LBB204_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovbeq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB204_1
	retq

	.def	atomic_umin_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_64_acquire,unique,205
	.globl	atomic_umin_64_acquire
	.p2align	4
atomic_umin_64_acquire:
	movq	(%rcx), %rax
	.p2align	4
.LBB205_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovbeq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB205_1
	retq

	.def	atomic_umin_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_64_relaxed,unique,206
	.globl	atomic_umin_64_relaxed
	.p2align	4
atomic_umin_64_relaxed:
	movq	(%rcx), %rax
	.p2align	4
.LBB206_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovbeq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB206_1
	retq

	.def	atomic_umin_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_64_release,unique,207
	.globl	atomic_umin_64_release
	.p2align	4
atomic_umin_64_release:
	movq	(%rcx), %rax
	.p2align	4
.LBB207_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovbeq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB207_1
	retq

	.def	atomic_umin_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_64_seqcst,unique,208
	.globl	atomic_umin_64_seqcst
	.p2align	4
atomic_umin_64_seqcst:
	movq	(%rcx), %rax
	.p2align	4
.LBB208_1:
	cmpq	%rdx, %rax
	movq	%rdx, %r8
	cmovbeq	%rax, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB208_1
	retq

	.def	atomic_umin_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_8_acqrel,unique,209
	.globl	atomic_umin_8_acqrel
	.p2align	4
atomic_umin_8_acqrel:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB209_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB209_1
	retq

	.def	atomic_umin_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_8_acquire,unique,210
	.globl	atomic_umin_8_acquire
	.p2align	4
atomic_umin_8_acquire:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB210_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB210_1
	retq

	.def	atomic_umin_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_8_relaxed,unique,211
	.globl	atomic_umin_8_relaxed
	.p2align	4
atomic_umin_8_relaxed:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB211_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB211_1
	retq

	.def	atomic_umin_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_8_release,unique,212
	.globl	atomic_umin_8_release
	.p2align	4
atomic_umin_8_release:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB212_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB212_1
	retq

	.def	atomic_umin_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_umin_8_seqcst,unique,213
	.globl	atomic_umin_8_seqcst
	.p2align	4
atomic_umin_8_seqcst:
	movzbl	(%rcx), %eax
	movzbl	%dl, %edx
	.p2align	4
.LBB213_1:
	cmpb	%dl, %al
	movzbl	%al, %eax
	movl	%edx, %r8d
	cmovbel	%eax, %r8d
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB213_1
	retq

	.def	atomic_xadd_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_128_acqrel,unique,214
	.globl	atomic_xadd_128_acqrel
	.p2align	4
atomic_xadd_128_acqrel:
.seh_proc atomic_xadd_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB214_1:
	movq	%rax, %rbx
	addq	%r9, %rbx
	movq	%rdx, %rcx
	adcq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB214_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xadd_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_128_acquire,unique,215
	.globl	atomic_xadd_128_acquire
	.p2align	4
atomic_xadd_128_acquire:
.seh_proc atomic_xadd_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB215_1:
	movq	%rax, %rbx
	addq	%r9, %rbx
	movq	%rdx, %rcx
	adcq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB215_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xadd_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_128_relaxed,unique,216
	.globl	atomic_xadd_128_relaxed
	.p2align	4
atomic_xadd_128_relaxed:
.seh_proc atomic_xadd_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB216_1:
	movq	%rax, %rbx
	addq	%r9, %rbx
	movq	%rdx, %rcx
	adcq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB216_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xadd_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_128_release,unique,217
	.globl	atomic_xadd_128_release
	.p2align	4
atomic_xadd_128_release:
.seh_proc atomic_xadd_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB217_1:
	movq	%rax, %rbx
	addq	%r9, %rbx
	movq	%rdx, %rcx
	adcq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB217_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xadd_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_128_seqcst,unique,218
	.globl	atomic_xadd_128_seqcst
	.p2align	4
atomic_xadd_128_seqcst:
.seh_proc atomic_xadd_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB218_1:
	movq	%rax, %rbx
	addq	%r9, %rbx
	movq	%rdx, %rcx
	adcq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB218_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xadd_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_16_acqrel,unique,219
	.globl	atomic_xadd_16_acqrel
	.p2align	4
atomic_xadd_16_acqrel:
	movl	%edx, %eax
	lock		xaddw	%ax, (%rcx)
	retq

	.def	atomic_xadd_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_16_acquire,unique,220
	.globl	atomic_xadd_16_acquire
	.p2align	4
atomic_xadd_16_acquire:
	movl	%edx, %eax
	lock		xaddw	%ax, (%rcx)
	retq

	.def	atomic_xadd_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_16_relaxed,unique,221
	.globl	atomic_xadd_16_relaxed
	.p2align	4
atomic_xadd_16_relaxed:
	movl	%edx, %eax
	lock		xaddw	%ax, (%rcx)
	retq

	.def	atomic_xadd_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_16_release,unique,222
	.globl	atomic_xadd_16_release
	.p2align	4
atomic_xadd_16_release:
	movl	%edx, %eax
	lock		xaddw	%ax, (%rcx)
	retq

	.def	atomic_xadd_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_16_seqcst,unique,223
	.globl	atomic_xadd_16_seqcst
	.p2align	4
atomic_xadd_16_seqcst:
	movl	%edx, %eax
	lock		xaddw	%ax, (%rcx)
	retq

	.def	atomic_xadd_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_32_acqrel,unique,224
	.globl	atomic_xadd_32_acqrel
	.p2align	4
atomic_xadd_32_acqrel:
	movl	%edx, %eax
	lock		xaddl	%eax, (%rcx)
	retq

	.def	atomic_xadd_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_32_acquire,unique,225
	.globl	atomic_xadd_32_acquire
	.p2align	4
atomic_xadd_32_acquire:
	movl	%edx, %eax
	lock		xaddl	%eax, (%rcx)
	retq

	.def	atomic_xadd_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_32_relaxed,unique,226
	.globl	atomic_xadd_32_relaxed
	.p2align	4
atomic_xadd_32_relaxed:
	movl	%edx, %eax
	lock		xaddl	%eax, (%rcx)
	retq

	.def	atomic_xadd_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_32_release,unique,227
	.globl	atomic_xadd_32_release
	.p2align	4
atomic_xadd_32_release:
	movl	%edx, %eax
	lock		xaddl	%eax, (%rcx)
	retq

	.def	atomic_xadd_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_32_seqcst,unique,228
	.globl	atomic_xadd_32_seqcst
	.p2align	4
atomic_xadd_32_seqcst:
	movl	%edx, %eax
	lock		xaddl	%eax, (%rcx)
	retq

	.def	atomic_xadd_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_64_acqrel,unique,229
	.globl	atomic_xadd_64_acqrel
	.p2align	4
atomic_xadd_64_acqrel:
	movq	%rdx, %rax
	lock		xaddq	%rax, (%rcx)
	retq

	.def	atomic_xadd_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_64_acquire,unique,230
	.globl	atomic_xadd_64_acquire
	.p2align	4
atomic_xadd_64_acquire:
	movq	%rdx, %rax
	lock		xaddq	%rax, (%rcx)
	retq

	.def	atomic_xadd_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_64_relaxed,unique,231
	.globl	atomic_xadd_64_relaxed
	.p2align	4
atomic_xadd_64_relaxed:
	movq	%rdx, %rax
	lock		xaddq	%rax, (%rcx)
	retq

	.def	atomic_xadd_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_64_release,unique,232
	.globl	atomic_xadd_64_release
	.p2align	4
atomic_xadd_64_release:
	movq	%rdx, %rax
	lock		xaddq	%rax, (%rcx)
	retq

	.def	atomic_xadd_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_64_seqcst,unique,233
	.globl	atomic_xadd_64_seqcst
	.p2align	4
atomic_xadd_64_seqcst:
	movq	%rdx, %rax
	lock		xaddq	%rax, (%rcx)
	retq

	.def	atomic_xadd_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_8_acqrel,unique,234
	.globl	atomic_xadd_8_acqrel
	.p2align	4
atomic_xadd_8_acqrel:
	movl	%edx, %eax
	lock		xaddb	%al, (%rcx)
	retq

	.def	atomic_xadd_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_8_acquire,unique,235
	.globl	atomic_xadd_8_acquire
	.p2align	4
atomic_xadd_8_acquire:
	movl	%edx, %eax
	lock		xaddb	%al, (%rcx)
	retq

	.def	atomic_xadd_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_8_relaxed,unique,236
	.globl	atomic_xadd_8_relaxed
	.p2align	4
atomic_xadd_8_relaxed:
	movl	%edx, %eax
	lock		xaddb	%al, (%rcx)
	retq

	.def	atomic_xadd_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_8_release,unique,237
	.globl	atomic_xadd_8_release
	.p2align	4
atomic_xadd_8_release:
	movl	%edx, %eax
	lock		xaddb	%al, (%rcx)
	retq

	.def	atomic_xadd_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xadd_8_seqcst,unique,238
	.globl	atomic_xadd_8_seqcst
	.p2align	4
atomic_xadd_8_seqcst:
	movl	%edx, %eax
	lock		xaddb	%al, (%rcx)
	retq

	.def	atomic_xchg_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_128_acqrel,unique,239
	.globl	atomic_xchg_128_acqrel
	.p2align	4
atomic_xchg_128_acqrel:
.seh_proc atomic_xchg_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %rbx
	movq	%rcx, %r9
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB239_1:
	movq	%r8, %rcx
	lock		cmpxchg16b	(%r9)
	jne	.LBB239_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xchg_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_128_acquire,unique,240
	.globl	atomic_xchg_128_acquire
	.p2align	4
atomic_xchg_128_acquire:
.seh_proc atomic_xchg_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %rbx
	movq	%rcx, %r9
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB240_1:
	movq	%r8, %rcx
	lock		cmpxchg16b	(%r9)
	jne	.LBB240_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xchg_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_128_relaxed,unique,241
	.globl	atomic_xchg_128_relaxed
	.p2align	4
atomic_xchg_128_relaxed:
.seh_proc atomic_xchg_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %rbx
	movq	%rcx, %r9
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB241_1:
	movq	%r8, %rcx
	lock		cmpxchg16b	(%r9)
	jne	.LBB241_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xchg_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_128_release,unique,242
	.globl	atomic_xchg_128_release
	.p2align	4
atomic_xchg_128_release:
.seh_proc atomic_xchg_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %rbx
	movq	%rcx, %r9
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB242_1:
	movq	%r8, %rcx
	lock		cmpxchg16b	(%r9)
	jne	.LBB242_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xchg_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_128_seqcst,unique,243
	.globl	atomic_xchg_128_seqcst
	.p2align	4
atomic_xchg_128_seqcst:
.seh_proc atomic_xchg_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %rbx
	movq	%rcx, %r9
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB243_1:
	movq	%r8, %rcx
	lock		cmpxchg16b	(%r9)
	jne	.LBB243_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xchg_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_16_acqrel,unique,244
	.globl	atomic_xchg_16_acqrel
	.p2align	4
atomic_xchg_16_acqrel:
	movl	%edx, %eax
	xchgw	%ax, (%rcx)
	retq

	.def	atomic_xchg_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_16_acquire,unique,245
	.globl	atomic_xchg_16_acquire
	.p2align	4
atomic_xchg_16_acquire:
	movl	%edx, %eax
	xchgw	%ax, (%rcx)
	retq

	.def	atomic_xchg_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_16_relaxed,unique,246
	.globl	atomic_xchg_16_relaxed
	.p2align	4
atomic_xchg_16_relaxed:
	movl	%edx, %eax
	xchgw	%ax, (%rcx)
	retq

	.def	atomic_xchg_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_16_release,unique,247
	.globl	atomic_xchg_16_release
	.p2align	4
atomic_xchg_16_release:
	movl	%edx, %eax
	xchgw	%ax, (%rcx)
	retq

	.def	atomic_xchg_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_16_seqcst,unique,248
	.globl	atomic_xchg_16_seqcst
	.p2align	4
atomic_xchg_16_seqcst:
	movl	%edx, %eax
	xchgw	%ax, (%rcx)
	retq

	.def	atomic_xchg_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_32_acqrel,unique,249
	.globl	atomic_xchg_32_acqrel
	.p2align	4
atomic_xchg_32_acqrel:
	movl	%edx, %eax
	xchgl	%eax, (%rcx)
	retq

	.def	atomic_xchg_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_32_acquire,unique,250
	.globl	atomic_xchg_32_acquire
	.p2align	4
atomic_xchg_32_acquire:
	movl	%edx, %eax
	xchgl	%eax, (%rcx)
	retq

	.def	atomic_xchg_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_32_relaxed,unique,251
	.globl	atomic_xchg_32_relaxed
	.p2align	4
atomic_xchg_32_relaxed:
	movl	%edx, %eax
	xchgl	%eax, (%rcx)
	retq

	.def	atomic_xchg_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_32_release,unique,252
	.globl	atomic_xchg_32_release
	.p2align	4
atomic_xchg_32_release:
	movl	%edx, %eax
	xchgl	%eax, (%rcx)
	retq

	.def	atomic_xchg_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_32_seqcst,unique,253
	.globl	atomic_xchg_32_seqcst
	.p2align	4
atomic_xchg_32_seqcst:
	movl	%edx, %eax
	xchgl	%eax, (%rcx)
	retq

	.def	atomic_xchg_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_64_acqrel,unique,254
	.globl	atomic_xchg_64_acqrel
	.p2align	4
atomic_xchg_64_acqrel:
	movq	%rdx, %rax
	xchgq	%rax, (%rcx)
	retq

	.def	atomic_xchg_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_64_acquire,unique,255
	.globl	atomic_xchg_64_acquire
	.p2align	4
atomic_xchg_64_acquire:
	movq	%rdx, %rax
	xchgq	%rax, (%rcx)
	retq

	.def	atomic_xchg_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_64_relaxed,unique,256
	.globl	atomic_xchg_64_relaxed
	.p2align	4
atomic_xchg_64_relaxed:
	movq	%rdx, %rax
	xchgq	%rax, (%rcx)
	retq

	.def	atomic_xchg_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_64_release,unique,257
	.globl	atomic_xchg_64_release
	.p2align	4
atomic_xchg_64_release:
	movq	%rdx, %rax
	xchgq	%rax, (%rcx)
	retq

	.def	atomic_xchg_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_64_seqcst,unique,258
	.globl	atomic_xchg_64_seqcst
	.p2align	4
atomic_xchg_64_seqcst:
	movq	%rdx, %rax
	xchgq	%rax, (%rcx)
	retq

	.def	atomic_xchg_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_8_acqrel,unique,259
	.globl	atomic_xchg_8_acqrel
	.p2align	4
atomic_xchg_8_acqrel:
	movl	%edx, %eax
	xchgb	%al, (%rcx)
	retq

	.def	atomic_xchg_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_8_acquire,unique,260
	.globl	atomic_xchg_8_acquire
	.p2align	4
atomic_xchg_8_acquire:
	movl	%edx, %eax
	xchgb	%al, (%rcx)
	retq

	.def	atomic_xchg_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_8_relaxed,unique,261
	.globl	atomic_xchg_8_relaxed
	.p2align	4
atomic_xchg_8_relaxed:
	movl	%edx, %eax
	xchgb	%al, (%rcx)
	retq

	.def	atomic_xchg_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_8_release,unique,262
	.globl	atomic_xchg_8_release
	.p2align	4
atomic_xchg_8_release:
	movl	%edx, %eax
	xchgb	%al, (%rcx)
	retq

	.def	atomic_xchg_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xchg_8_seqcst,unique,263
	.globl	atomic_xchg_8_seqcst
	.p2align	4
atomic_xchg_8_seqcst:
	movl	%edx, %eax
	xchgb	%al, (%rcx)
	retq

	.def	atomic_xor_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_128_acqrel,unique,264
	.globl	atomic_xor_128_acqrel
	.p2align	4
atomic_xor_128_acqrel:
.seh_proc atomic_xor_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB264_1:
	movq	%rax, %rbx
	xorq	%r9, %rbx
	movq	%rdx, %rcx
	xorq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB264_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xor_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_128_acquire,unique,265
	.globl	atomic_xor_128_acquire
	.p2align	4
atomic_xor_128_acquire:
.seh_proc atomic_xor_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB265_1:
	movq	%rax, %rbx
	xorq	%r9, %rbx
	movq	%rdx, %rcx
	xorq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB265_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xor_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_128_relaxed,unique,266
	.globl	atomic_xor_128_relaxed
	.p2align	4
atomic_xor_128_relaxed:
.seh_proc atomic_xor_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB266_1:
	movq	%rax, %rbx
	xorq	%r9, %rbx
	movq	%rdx, %rcx
	xorq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB266_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xor_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_128_release,unique,267
	.globl	atomic_xor_128_release
	.p2align	4
atomic_xor_128_release:
.seh_proc atomic_xor_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB267_1:
	movq	%rax, %rbx
	xorq	%r9, %rbx
	movq	%rdx, %rcx
	xorq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB267_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xor_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_128_seqcst,unique,268
	.globl	atomic_xor_128_seqcst
	.p2align	4
atomic_xor_128_seqcst:
.seh_proc atomic_xor_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB268_1:
	movq	%rax, %rbx
	xorq	%r9, %rbx
	movq	%rdx, %rcx
	xorq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB268_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xor_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_16_acqrel,unique,269
	.globl	atomic_xor_16_acqrel
	.p2align	4
atomic_xor_16_acqrel:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB269_1:
	movl	%eax, %r8d
	xorl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB269_1
	retq

	.def	atomic_xor_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_16_acquire,unique,270
	.globl	atomic_xor_16_acquire
	.p2align	4
atomic_xor_16_acquire:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB270_1:
	movl	%eax, %r8d
	xorl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB270_1
	retq

	.def	atomic_xor_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_16_relaxed,unique,271
	.globl	atomic_xor_16_relaxed
	.p2align	4
atomic_xor_16_relaxed:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB271_1:
	movl	%eax, %r8d
	xorl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB271_1
	retq

	.def	atomic_xor_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_16_release,unique,272
	.globl	atomic_xor_16_release
	.p2align	4
atomic_xor_16_release:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB272_1:
	movl	%eax, %r8d
	xorl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB272_1
	retq

	.def	atomic_xor_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_16_seqcst,unique,273
	.globl	atomic_xor_16_seqcst
	.p2align	4
atomic_xor_16_seqcst:
	movzwl	(%rcx), %eax
	.p2align	4
.LBB273_1:
	movl	%eax, %r8d
	xorl	%edx, %r8d
	lock		cmpxchgw	%r8w, (%rcx)
	jne	.LBB273_1
	retq

	.def	atomic_xor_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_32_acqrel,unique,274
	.globl	atomic_xor_32_acqrel
	.p2align	4
atomic_xor_32_acqrel:
	movl	(%rcx), %eax
	.p2align	4
.LBB274_1:
	movl	%eax, %r8d
	xorl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB274_1
	retq

	.def	atomic_xor_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_32_acquire,unique,275
	.globl	atomic_xor_32_acquire
	.p2align	4
atomic_xor_32_acquire:
	movl	(%rcx), %eax
	.p2align	4
.LBB275_1:
	movl	%eax, %r8d
	xorl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB275_1
	retq

	.def	atomic_xor_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_32_relaxed,unique,276
	.globl	atomic_xor_32_relaxed
	.p2align	4
atomic_xor_32_relaxed:
	movl	(%rcx), %eax
	.p2align	4
.LBB276_1:
	movl	%eax, %r8d
	xorl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB276_1
	retq

	.def	atomic_xor_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_32_release,unique,277
	.globl	atomic_xor_32_release
	.p2align	4
atomic_xor_32_release:
	movl	(%rcx), %eax
	.p2align	4
.LBB277_1:
	movl	%eax, %r8d
	xorl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB277_1
	retq

	.def	atomic_xor_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_32_seqcst,unique,278
	.globl	atomic_xor_32_seqcst
	.p2align	4
atomic_xor_32_seqcst:
	movl	(%rcx), %eax
	.p2align	4
.LBB278_1:
	movl	%eax, %r8d
	xorl	%edx, %r8d
	lock		cmpxchgl	%r8d, (%rcx)
	jne	.LBB278_1
	retq

	.def	atomic_xor_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_64_acqrel,unique,279
	.globl	atomic_xor_64_acqrel
	.p2align	4
atomic_xor_64_acqrel:
	movq	(%rcx), %rax
	.p2align	4
.LBB279_1:
	movq	%rax, %r8
	xorq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB279_1
	retq

	.def	atomic_xor_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_64_acquire,unique,280
	.globl	atomic_xor_64_acquire
	.p2align	4
atomic_xor_64_acquire:
	movq	(%rcx), %rax
	.p2align	4
.LBB280_1:
	movq	%rax, %r8
	xorq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB280_1
	retq

	.def	atomic_xor_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_64_relaxed,unique,281
	.globl	atomic_xor_64_relaxed
	.p2align	4
atomic_xor_64_relaxed:
	movq	(%rcx), %rax
	.p2align	4
.LBB281_1:
	movq	%rax, %r8
	xorq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB281_1
	retq

	.def	atomic_xor_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_64_release,unique,282
	.globl	atomic_xor_64_release
	.p2align	4
atomic_xor_64_release:
	movq	(%rcx), %rax
	.p2align	4
.LBB282_1:
	movq	%rax, %r8
	xorq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB282_1
	retq

	.def	atomic_xor_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_64_seqcst,unique,283
	.globl	atomic_xor_64_seqcst
	.p2align	4
atomic_xor_64_seqcst:
	movq	(%rcx), %rax
	.p2align	4
.LBB283_1:
	movq	%rax, %r8
	xorq	%rdx, %r8
	lock		cmpxchgq	%r8, (%rcx)
	jne	.LBB283_1
	retq

	.def	atomic_xor_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_8_acqrel,unique,284
	.globl	atomic_xor_8_acqrel
	.p2align	4
atomic_xor_8_acqrel:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB284_1:
	movl	%eax, %r8d
	xorb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB284_1
	retq

	.def	atomic_xor_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_8_acquire,unique,285
	.globl	atomic_xor_8_acquire
	.p2align	4
atomic_xor_8_acquire:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB285_1:
	movl	%eax, %r8d
	xorb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB285_1
	retq

	.def	atomic_xor_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_8_relaxed,unique,286
	.globl	atomic_xor_8_relaxed
	.p2align	4
atomic_xor_8_relaxed:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB286_1:
	movl	%eax, %r8d
	xorb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB286_1
	retq

	.def	atomic_xor_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_8_release,unique,287
	.globl	atomic_xor_8_release
	.p2align	4
atomic_xor_8_release:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB287_1:
	movl	%eax, %r8d
	xorb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB287_1
	retq

	.def	atomic_xor_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xor_8_seqcst,unique,288
	.globl	atomic_xor_8_seqcst
	.p2align	4
atomic_xor_8_seqcst:
	movzbl	(%rcx), %eax
	.p2align	4
.LBB288_1:
	movl	%eax, %r8d
	xorb	%dl, %r8b
	lock		cmpxchgb	%r8b, (%rcx)
	jne	.LBB288_1
	retq

	.def	atomic_xsub_128_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_128_acqrel,unique,289
	.globl	atomic_xsub_128_acqrel
	.p2align	4
atomic_xsub_128_acqrel:
.seh_proc atomic_xsub_128_acqrel
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB289_1:
	movq	%rax, %rbx
	subq	%r9, %rbx
	movq	%rdx, %rcx
	sbbq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB289_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xsub_128_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_128_acquire,unique,290
	.globl	atomic_xsub_128_acquire
	.p2align	4
atomic_xsub_128_acquire:
.seh_proc atomic_xsub_128_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB290_1:
	movq	%rax, %rbx
	subq	%r9, %rbx
	movq	%rdx, %rcx
	sbbq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB290_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xsub_128_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_128_relaxed,unique,291
	.globl	atomic_xsub_128_relaxed
	.p2align	4
atomic_xsub_128_relaxed:
.seh_proc atomic_xsub_128_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB291_1:
	movq	%rax, %rbx
	subq	%r9, %rbx
	movq	%rdx, %rcx
	sbbq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB291_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xsub_128_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_128_release,unique,292
	.globl	atomic_xsub_128_release
	.p2align	4
atomic_xsub_128_release:
.seh_proc atomic_xsub_128_release
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB292_1:
	movq	%rax, %rbx
	subq	%r9, %rbx
	movq	%rdx, %rcx
	sbbq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB292_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xsub_128_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_128_seqcst,unique,293
	.globl	atomic_xsub_128_seqcst
	.p2align	4
atomic_xsub_128_seqcst:
.seh_proc atomic_xsub_128_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%rdx, %r9
	movq	%rcx, %r10
	movq	(%rcx), %rax
	movq	8(%rcx), %rdx
	.p2align	4
.LBB293_1:
	movq	%rax, %rbx
	subq	%r9, %rbx
	movq	%rdx, %rcx
	sbbq	%r8, %rcx
	lock		cmpxchg16b	(%r10)
	jne	.LBB293_1
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	atomic_xsub_16_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_16_acqrel,unique,294
	.globl	atomic_xsub_16_acqrel
	.p2align	4
atomic_xsub_16_acqrel:
	movl	%edx, %eax
	negl	%eax
	lock		xaddw	%ax, (%rcx)
	retq

	.def	atomic_xsub_16_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_16_acquire,unique,295
	.globl	atomic_xsub_16_acquire
	.p2align	4
atomic_xsub_16_acquire:
	movl	%edx, %eax
	negl	%eax
	lock		xaddw	%ax, (%rcx)
	retq

	.def	atomic_xsub_16_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_16_relaxed,unique,296
	.globl	atomic_xsub_16_relaxed
	.p2align	4
atomic_xsub_16_relaxed:
	movl	%edx, %eax
	negl	%eax
	lock		xaddw	%ax, (%rcx)
	retq

	.def	atomic_xsub_16_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_16_release,unique,297
	.globl	atomic_xsub_16_release
	.p2align	4
atomic_xsub_16_release:
	movl	%edx, %eax
	negl	%eax
	lock		xaddw	%ax, (%rcx)
	retq

	.def	atomic_xsub_16_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_16_seqcst,unique,298
	.globl	atomic_xsub_16_seqcst
	.p2align	4
atomic_xsub_16_seqcst:
	movl	%edx, %eax
	negl	%eax
	lock		xaddw	%ax, (%rcx)
	retq

	.def	atomic_xsub_32_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_32_acqrel,unique,299
	.globl	atomic_xsub_32_acqrel
	.p2align	4
atomic_xsub_32_acqrel:
	movl	%edx, %eax
	negl	%eax
	lock		xaddl	%eax, (%rcx)
	retq

	.def	atomic_xsub_32_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_32_acquire,unique,300
	.globl	atomic_xsub_32_acquire
	.p2align	4
atomic_xsub_32_acquire:
	movl	%edx, %eax
	negl	%eax
	lock		xaddl	%eax, (%rcx)
	retq

	.def	atomic_xsub_32_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_32_relaxed,unique,301
	.globl	atomic_xsub_32_relaxed
	.p2align	4
atomic_xsub_32_relaxed:
	movl	%edx, %eax
	negl	%eax
	lock		xaddl	%eax, (%rcx)
	retq

	.def	atomic_xsub_32_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_32_release,unique,302
	.globl	atomic_xsub_32_release
	.p2align	4
atomic_xsub_32_release:
	movl	%edx, %eax
	negl	%eax
	lock		xaddl	%eax, (%rcx)
	retq

	.def	atomic_xsub_32_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_32_seqcst,unique,303
	.globl	atomic_xsub_32_seqcst
	.p2align	4
atomic_xsub_32_seqcst:
	movl	%edx, %eax
	negl	%eax
	lock		xaddl	%eax, (%rcx)
	retq

	.def	atomic_xsub_64_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_64_acqrel,unique,304
	.globl	atomic_xsub_64_acqrel
	.p2align	4
atomic_xsub_64_acqrel:
	movq	%rdx, %rax
	negq	%rax
	lock		xaddq	%rax, (%rcx)
	retq

	.def	atomic_xsub_64_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_64_acquire,unique,305
	.globl	atomic_xsub_64_acquire
	.p2align	4
atomic_xsub_64_acquire:
	movq	%rdx, %rax
	negq	%rax
	lock		xaddq	%rax, (%rcx)
	retq

	.def	atomic_xsub_64_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_64_relaxed,unique,306
	.globl	atomic_xsub_64_relaxed
	.p2align	4
atomic_xsub_64_relaxed:
	movq	%rdx, %rax
	negq	%rax
	lock		xaddq	%rax, (%rcx)
	retq

	.def	atomic_xsub_64_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_64_release,unique,307
	.globl	atomic_xsub_64_release
	.p2align	4
atomic_xsub_64_release:
	movq	%rdx, %rax
	negq	%rax
	lock		xaddq	%rax, (%rcx)
	retq

	.def	atomic_xsub_64_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_64_seqcst,unique,308
	.globl	atomic_xsub_64_seqcst
	.p2align	4
atomic_xsub_64_seqcst:
	movq	%rdx, %rax
	negq	%rax
	lock		xaddq	%rax, (%rcx)
	retq

	.def	atomic_xsub_8_acqrel;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_8_acqrel,unique,309
	.globl	atomic_xsub_8_acqrel
	.p2align	4
atomic_xsub_8_acqrel:
	movl	%edx, %eax
	negb	%al
	lock		xaddb	%al, (%rcx)
	retq

	.def	atomic_xsub_8_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_8_acquire,unique,310
	.globl	atomic_xsub_8_acquire
	.p2align	4
atomic_xsub_8_acquire:
	movl	%edx, %eax
	negb	%al
	lock		xaddb	%al, (%rcx)
	retq

	.def	atomic_xsub_8_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_8_relaxed,unique,311
	.globl	atomic_xsub_8_relaxed
	.p2align	4
atomic_xsub_8_relaxed:
	movl	%edx, %eax
	negb	%al
	lock		xaddb	%al, (%rcx)
	retq

	.def	atomic_xsub_8_release;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_8_release,unique,312
	.globl	atomic_xsub_8_release
	.p2align	4
atomic_xsub_8_release:
	movl	%edx, %eax
	negb	%al
	lock		xaddb	%al, (%rcx)
	retq

	.def	atomic_xsub_8_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,atomic_xsub_8_seqcst,unique,313
	.globl	atomic_xsub_8_seqcst
	.p2align	4
atomic_xsub_8_seqcst:
	movl	%edx, %eax
	negb	%al
	lock		xaddb	%al, (%rcx)
	retq

	.def	cxchg_128_acqrel_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_128_acqrel_acquire,unique,314
	.globl	cxchg_128_acqrel_acquire
	.p2align	4
cxchg_128_acqrel_acquire:
.seh_proc cxchg_128_acqrel_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchg_128_acquire_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_128_acquire_acquire,unique,315
	.globl	cxchg_128_acquire_acquire
	.p2align	4
cxchg_128_acquire_acquire:
.seh_proc cxchg_128_acquire_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchg_128_relaxed_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_128_relaxed_relaxed,unique,316
	.globl	cxchg_128_relaxed_relaxed
	.p2align	4
cxchg_128_relaxed_relaxed:
.seh_proc cxchg_128_relaxed_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchg_128_release_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_128_release_relaxed,unique,317
	.globl	cxchg_128_release_relaxed
	.p2align	4
cxchg_128_release_relaxed:
.seh_proc cxchg_128_release_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchg_128_seqcst_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_128_seqcst_relaxed,unique,318
	.globl	cxchg_128_seqcst_relaxed
	.p2align	4
cxchg_128_seqcst_relaxed:
.seh_proc cxchg_128_seqcst_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchg_128_seqcst_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_128_seqcst_seqcst,unique,319
	.globl	cxchg_128_seqcst_seqcst
	.p2align	4
cxchg_128_seqcst_seqcst:
.seh_proc cxchg_128_seqcst_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchg_16_acqrel_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_16_acqrel_acquire,unique,320
	.globl	cxchg_16_acqrel_acquire
	.p2align	4
cxchg_16_acqrel_acquire:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchg_16_acquire_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_16_acquire_acquire,unique,321
	.globl	cxchg_16_acquire_acquire
	.p2align	4
cxchg_16_acquire_acquire:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchg_16_relaxed_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_16_relaxed_relaxed,unique,322
	.globl	cxchg_16_relaxed_relaxed
	.p2align	4
cxchg_16_relaxed_relaxed:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchg_16_release_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_16_release_relaxed,unique,323
	.globl	cxchg_16_release_relaxed
	.p2align	4
cxchg_16_release_relaxed:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchg_16_seqcst_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_16_seqcst_relaxed,unique,324
	.globl	cxchg_16_seqcst_relaxed
	.p2align	4
cxchg_16_seqcst_relaxed:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchg_16_seqcst_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_16_seqcst_seqcst,unique,325
	.globl	cxchg_16_seqcst_seqcst
	.p2align	4
cxchg_16_seqcst_seqcst:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchg_32_acqrel_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_32_acqrel_acquire,unique,326
	.globl	cxchg_32_acqrel_acquire
	.p2align	4
cxchg_32_acqrel_acquire:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchg_32_acquire_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_32_acquire_acquire,unique,327
	.globl	cxchg_32_acquire_acquire
	.p2align	4
cxchg_32_acquire_acquire:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchg_32_relaxed_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_32_relaxed_relaxed,unique,328
	.globl	cxchg_32_relaxed_relaxed
	.p2align	4
cxchg_32_relaxed_relaxed:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchg_32_release_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_32_release_relaxed,unique,329
	.globl	cxchg_32_release_relaxed
	.p2align	4
cxchg_32_release_relaxed:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchg_32_seqcst_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_32_seqcst_relaxed,unique,330
	.globl	cxchg_32_seqcst_relaxed
	.p2align	4
cxchg_32_seqcst_relaxed:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchg_32_seqcst_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_32_seqcst_seqcst,unique,331
	.globl	cxchg_32_seqcst_seqcst
	.p2align	4
cxchg_32_seqcst_seqcst:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchg_64_acqrel_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_64_acqrel_acquire,unique,332
	.globl	cxchg_64_acqrel_acquire
	.p2align	4
cxchg_64_acqrel_acquire:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchg_64_acquire_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_64_acquire_acquire,unique,333
	.globl	cxchg_64_acquire_acquire
	.p2align	4
cxchg_64_acquire_acquire:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchg_64_relaxed_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_64_relaxed_relaxed,unique,334
	.globl	cxchg_64_relaxed_relaxed
	.p2align	4
cxchg_64_relaxed_relaxed:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchg_64_release_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_64_release_relaxed,unique,335
	.globl	cxchg_64_release_relaxed
	.p2align	4
cxchg_64_release_relaxed:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchg_64_seqcst_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_64_seqcst_relaxed,unique,336
	.globl	cxchg_64_seqcst_relaxed
	.p2align	4
cxchg_64_seqcst_relaxed:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchg_64_seqcst_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_64_seqcst_seqcst,unique,337
	.globl	cxchg_64_seqcst_seqcst
	.p2align	4
cxchg_64_seqcst_seqcst:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchg_8_acqrel_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_8_acqrel_acquire,unique,338
	.globl	cxchg_8_acqrel_acquire
	.p2align	4
cxchg_8_acqrel_acquire:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchg_8_acquire_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_8_acquire_acquire,unique,339
	.globl	cxchg_8_acquire_acquire
	.p2align	4
cxchg_8_acquire_acquire:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchg_8_relaxed_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_8_relaxed_relaxed,unique,340
	.globl	cxchg_8_relaxed_relaxed
	.p2align	4
cxchg_8_relaxed_relaxed:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchg_8_release_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_8_release_relaxed,unique,341
	.globl	cxchg_8_release_relaxed
	.p2align	4
cxchg_8_release_relaxed:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchg_8_seqcst_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_8_seqcst_relaxed,unique,342
	.globl	cxchg_8_seqcst_relaxed
	.p2align	4
cxchg_8_seqcst_relaxed:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchg_8_seqcst_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchg_8_seqcst_seqcst,unique,343
	.globl	cxchg_8_seqcst_seqcst
	.p2align	4
cxchg_8_seqcst_seqcst:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_128_acqrel_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_128_acqrel_acquire,unique,344
	.globl	cxchgweak_128_acqrel_acquire
	.p2align	4
cxchgweak_128_acqrel_acquire:
.seh_proc cxchgweak_128_acqrel_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchgweak_128_acquire_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_128_acquire_acquire,unique,345
	.globl	cxchgweak_128_acquire_acquire
	.p2align	4
cxchgweak_128_acquire_acquire:
.seh_proc cxchgweak_128_acquire_acquire
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchgweak_128_relaxed_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_128_relaxed_relaxed,unique,346
	.globl	cxchgweak_128_relaxed_relaxed
	.p2align	4
cxchgweak_128_relaxed_relaxed:
.seh_proc cxchgweak_128_relaxed_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchgweak_128_release_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_128_release_relaxed,unique,347
	.globl	cxchgweak_128_release_relaxed
	.p2align	4
cxchgweak_128_release_relaxed:
.seh_proc cxchgweak_128_release_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchgweak_128_seqcst_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_128_seqcst_relaxed,unique,348
	.globl	cxchgweak_128_seqcst_relaxed
	.p2align	4
cxchgweak_128_seqcst_relaxed:
.seh_proc cxchgweak_128_seqcst_relaxed
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchgweak_128_seqcst_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_128_seqcst_seqcst,unique,349
	.globl	cxchgweak_128_seqcst_seqcst
	.p2align	4
cxchgweak_128_seqcst_seqcst:
.seh_proc cxchgweak_128_seqcst_seqcst
	pushq	%rbx
	.seh_pushreg %rbx
	.seh_endprologue
	movq	%r8, %rax
	movq	%rdx, %r8
	movq	%rcx, %r10
	movq	48(%rsp), %rbx
	movq	56(%rsp), %rcx
	movq	%r9, %rdx
	lock		cmpxchg16b	(%r8)
	movq	%rax, (%r10)
	movq	%rdx, 8(%r10)
	sete	16(%r10)
	movq	%r10, %rax
	.seh_startepilogue
	popq	%rbx
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cxchgweak_16_acqrel_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_16_acqrel_acquire,unique,350
	.globl	cxchgweak_16_acqrel_acquire
	.p2align	4
cxchgweak_16_acqrel_acquire:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_16_acquire_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_16_acquire_acquire,unique,351
	.globl	cxchgweak_16_acquire_acquire
	.p2align	4
cxchgweak_16_acquire_acquire:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_16_relaxed_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_16_relaxed_relaxed,unique,352
	.globl	cxchgweak_16_relaxed_relaxed
	.p2align	4
cxchgweak_16_relaxed_relaxed:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_16_release_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_16_release_relaxed,unique,353
	.globl	cxchgweak_16_release_relaxed
	.p2align	4
cxchgweak_16_release_relaxed:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_16_seqcst_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_16_seqcst_relaxed,unique,354
	.globl	cxchgweak_16_seqcst_relaxed
	.p2align	4
cxchgweak_16_seqcst_relaxed:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_16_seqcst_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_16_seqcst_seqcst,unique,355
	.globl	cxchgweak_16_seqcst_seqcst
	.p2align	4
cxchgweak_16_seqcst_seqcst:
	movl	%edx, %eax
	lock		cmpxchgw	%r8w, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_32_acqrel_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_32_acqrel_acquire,unique,356
	.globl	cxchgweak_32_acqrel_acquire
	.p2align	4
cxchgweak_32_acqrel_acquire:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_32_acquire_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_32_acquire_acquire,unique,357
	.globl	cxchgweak_32_acquire_acquire
	.p2align	4
cxchgweak_32_acquire_acquire:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_32_relaxed_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_32_relaxed_relaxed,unique,358
	.globl	cxchgweak_32_relaxed_relaxed
	.p2align	4
cxchgweak_32_relaxed_relaxed:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_32_release_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_32_release_relaxed,unique,359
	.globl	cxchgweak_32_release_relaxed
	.p2align	4
cxchgweak_32_release_relaxed:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_32_seqcst_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_32_seqcst_relaxed,unique,360
	.globl	cxchgweak_32_seqcst_relaxed
	.p2align	4
cxchgweak_32_seqcst_relaxed:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_32_seqcst_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_32_seqcst_seqcst,unique,361
	.globl	cxchgweak_32_seqcst_seqcst
	.p2align	4
cxchgweak_32_seqcst_seqcst:
	movl	%edx, %eax
	lock		cmpxchgl	%r8d, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_64_acqrel_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_64_acqrel_acquire,unique,362
	.globl	cxchgweak_64_acqrel_acquire
	.p2align	4
cxchgweak_64_acqrel_acquire:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_64_acquire_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_64_acquire_acquire,unique,363
	.globl	cxchgweak_64_acquire_acquire
	.p2align	4
cxchgweak_64_acquire_acquire:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_64_relaxed_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_64_relaxed_relaxed,unique,364
	.globl	cxchgweak_64_relaxed_relaxed
	.p2align	4
cxchgweak_64_relaxed_relaxed:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_64_release_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_64_release_relaxed,unique,365
	.globl	cxchgweak_64_release_relaxed
	.p2align	4
cxchgweak_64_release_relaxed:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_64_seqcst_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_64_seqcst_relaxed,unique,366
	.globl	cxchgweak_64_seqcst_relaxed
	.p2align	4
cxchgweak_64_seqcst_relaxed:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_64_seqcst_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_64_seqcst_seqcst,unique,367
	.globl	cxchgweak_64_seqcst_seqcst
	.p2align	4
cxchgweak_64_seqcst_seqcst:
	movq	%rdx, %rax
	lock		cmpxchgq	%r8, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_8_acqrel_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_8_acqrel_acquire,unique,368
	.globl	cxchgweak_8_acqrel_acquire
	.p2align	4
cxchgweak_8_acqrel_acquire:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_8_acquire_acquire;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_8_acquire_acquire,unique,369
	.globl	cxchgweak_8_acquire_acquire
	.p2align	4
cxchgweak_8_acquire_acquire:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_8_relaxed_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_8_relaxed_relaxed,unique,370
	.globl	cxchgweak_8_relaxed_relaxed
	.p2align	4
cxchgweak_8_relaxed_relaxed:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_8_release_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_8_release_relaxed,unique,371
	.globl	cxchgweak_8_release_relaxed
	.p2align	4
cxchgweak_8_release_relaxed:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_8_seqcst_relaxed;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_8_seqcst_relaxed,unique,372
	.globl	cxchgweak_8_seqcst_relaxed
	.p2align	4
cxchgweak_8_seqcst_relaxed:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

	.def	cxchgweak_8_seqcst_seqcst;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cxchgweak_8_seqcst_seqcst,unique,373
	.globl	cxchgweak_8_seqcst_seqcst
	.p2align	4
cxchgweak_8_seqcst_seqcst:
	movl	%edx, %eax
	lock		cmpxchgb	%r8b, (%rcx)
	sete	%dl
	retq

