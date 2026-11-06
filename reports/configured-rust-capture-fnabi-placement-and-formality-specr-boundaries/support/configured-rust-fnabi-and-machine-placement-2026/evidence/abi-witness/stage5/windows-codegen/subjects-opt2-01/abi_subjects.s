	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.file	"abi_subjects.e2113a355ceea76a-cgu.0"
	.def	abi_c_big;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_c_big,unique,0
	.globl	abi_c_big
	.p2align	4
abi_c_big:
	movq	%rcx, %rax
	movq	16(%rdx), %rcx
	movq	%rcx, 16(%rax)
	movups	(%rdx), %xmm0
	movups	%xmm0, (%rax)
	retq

	.def	abi_c_fp;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_c_fp,unique,1
	.globl	abi_c_fp
	.p2align	4
abi_c_fp:
	cvtss2sd	%xmm0, %xmm0
	addsd	%xmm1, %xmm0
	retq

	.def	abi_c_hfa;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_c_hfa,unique,2
	.globl	abi_c_hfa
	.p2align	4
abi_c_hfa:
	movq	%rcx, %rax
	movups	(%rdx), %xmm0
	movups	%xmm0, (%rcx)
	retq

	.def	abi_c_narrow;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_c_narrow,unique,3
	.globl	abi_c_narrow
	.p2align	4
abi_c_narrow:
	movzbl	%cl, %eax
	movswq	%dx, %rcx
	xorq	%rax, %rcx
	movzbl	%r8b, %eax
	xorq	%rcx, %rax
	retq

	.def	abi_c_pair;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_c_pair,unique,4
	.globl	abi_c_pair
	.p2align	4
abi_c_pair:
	movq	%rcx, %rax
	movq	(%rdx), %rcx
	movl	8(%rdx), %edx
	movq	%rcx, (%rax)
	movl	%edx, 8(%rax)
	retq

	.def	abi_c_raw;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_c_raw,unique,5
	.globl	abi_c_raw
	.p2align	4
abi_c_raw:
	movq	%rcx, %rax
	retq

	.def	abi_interior;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_interior,unique,6
	.globl	abi_interior
	.p2align	4
abi_interior:
	movq	%rcx, %rax
	retq

	.def	abi_rust_narrow;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_rust_narrow,unique,7
	.globl	abi_rust_narrow
	.p2align	4
abi_rust_narrow:
	movzbl	%cl, %eax
	movswq	%dx, %rcx
	xorq	%rax, %rcx
	movzbl	%r8b, %eax
	xorq	%rcx, %rax
	retq

	.def	abi_rust_tuple;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_rust_tuple,unique,8
	.globl	abi_rust_tuple
	.p2align	4
abi_rust_tuple:
	movq	%rcx, %rax
	retq

	.def	abi_shared;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_shared,unique,9
	.globl	abi_shared
	.p2align	4
abi_shared:
	movq	(%rcx), %rax
	retq

	.def	abi_slice;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_slice,unique,10
	.globl	abi_slice
	.p2align	4
abi_slice:
	movq	%rdx, %rax
	retq

	.def	abi_stack_driver;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_stack_driver,unique,11
	.globl	abi_stack_driver
	.p2align	4
abi_stack_driver:
.seh_proc abi_stack_driver
	subq	$104, %rsp
	.seh_stackalloc 104
	.seh_endprologue
	movaps	144(%rsp), %xmm0
	movaps	160(%rsp), %xmm1
	movaps	176(%rsp), %xmm2
	movaps	192(%rsp), %xmm3
	movups	%xmm3, 80(%rsp)
	movups	%xmm2, 64(%rsp)
	movups	%xmm1, 48(%rsp)
	movups	%xmm0, 32(%rsp)
	callq	abi_opaque_twelve
	incq	%rax
	.seh_startepilogue
	addq	$104, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	abi_track;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_track,unique,12
	.globl	abi_track
	.p2align	4
abi_track:
	movl	16(%rdx), %eax
	xorq	%rcx, %rax
	retq

	.def	abi_unique;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_unique,unique,13
	.globl	abi_unique
	.p2align	4
abi_unique:
	movq	(%rcx), %rax
	incq	%rax
	movq	%rax, (%rcx)
	retq

	.def	abi_unit;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_unit,unique,14
	.globl	abi_unit
	.p2align	4
abi_unit:
	retq

	.def	abi_vararg_driver;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,abi_vararg_driver,unique,15
	.globl	abi_vararg_driver
	.p2align	4
abi_vararg_driver:
.seh_proc abi_vararg_driver
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	movl	%ecx, %edx
	movl	$1, %ecx
	movdqa	%xmm1, %xmm2
	movq	%xmm1, %r8
	xorl	%r9d, %r9d
	callq	abi_opaque_vararg
	incq	%rax
	.seh_startepilogue
	addq	$40, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.globl	abi_rust_big
	.def	abi_rust_big;
	.scl	2;
	.type	32;
	.endef
abi_rust_big = abi_c_big
	.globl	abi_system_big
	.def	abi_system_big;
	.scl	2;
	.type	32;
	.endef
abi_system_big = abi_c_big
	.globl	abi_system_narrow
	.def	abi_system_narrow;
	.scl	2;
	.type	32;
	.endef
abi_system_narrow = abi_c_narrow
	.globl	abi_system_pair
	.def	abi_system_pair;
	.scl	2;
	.type	32;
	.endef
abi_system_pair = abi_c_pair
	.globl	_fltused
