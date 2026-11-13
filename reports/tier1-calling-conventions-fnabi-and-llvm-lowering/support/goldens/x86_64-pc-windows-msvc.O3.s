	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.att_syntax
	.file	"calling_conv_corpus.75f08b44548a9e00-cgu.0"
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

	.def	cc_c_nounwind;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_c_nounwind,unique,1
	.globl	cc_c_nounwind
	.p2align	4
cc_c_nounwind:
	leal	1(%rcx), %eax
	retq

	.def	cc_c_unwind;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_c_unwind,unique,2
	.globl	cc_c_unwind
	.p2align	4
cc_c_unwind:
.seh_proc cc_c_unwind
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	movq	%rcx, %rax
	movl	%edx, %ecx
	callq	*%rax
	incl	%eax
	.seh_startepilogue
	addq	$40, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cc_explicit_sysv64;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_explicit_sysv64,unique,3
	.globl	cc_explicit_sysv64
	.p2align	4
cc_explicit_sysv64:
	leaq	(%rdi,%rdx), %rax
	leaq	(%rsi,%rcx), %rdx
	retq

	.def	cc_explicit_win64;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_explicit_win64,unique,4
	.globl	cc_explicit_win64
	.p2align	4
cc_explicit_win64:
	addq	(%r9), %rdx
	addq	8(%r9), %r8
	movq	%rcx, %rax
	movq	%rdx, (%rcx)
	movq	%r8, 8(%rcx)
	retq

	.def	cc_f16_f128;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_f16_f128,unique,5
	.globl	cc_f16_f128
	.p2align	4
cc_f16_f128:
	movq	%rcx, %rax
	movaps	(%r8), %xmm0
	movaps	%xmm0, (%rcx)
	retq

	.def	cc_hfa2_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_hfa2_f32,unique,6
	.globl	cc_hfa2_f32
	.p2align	4
cc_hfa2_f32:
	movq	%rcx, %rax
	rolq	$32, %rax
	retq

	.def	cc_hfa4_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_hfa4_f32,unique,7
	.globl	cc_hfa4_f32
	.p2align	4
cc_hfa4_f32:
	movq	%rcx, %rax
	movups	(%rdx), %xmm0
	shufps	$27, %xmm0, %xmm0
	movups	%xmm0, (%rcx)
	retq

	.def	cc_hfa5_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_hfa5_f32,unique,8
	.globl	cc_hfa5_f32
	.p2align	4
cc_hfa5_f32:
	movq	%rcx, %rax
	movss	(%rdx), %xmm0
	movups	4(%rdx), %xmm1
	shufps	$147, %xmm1, %xmm1
	movups	%xmm1, (%rcx)
	movss	%xmm0, 16(%rcx)
	retq

	.def	cc_hva2_c;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_hva2_c,unique,9
	.globl	cc_hva2_c
	.p2align	4
cc_hva2_c:
	movq	%rcx, %rax
	movaps	(%rdx), %xmm0
	movaps	16(%rdx), %xmm1
	movaps	%xmm1, (%rcx)
	movaps	%xmm0, 16(%rcx)
	retq

	.def	cc_many_args;
	.scl	2;
	.type	32;
	.endef
	.globl	__real@43e0000000000000
	.section	.rdata,"dr",discard,__real@43e0000000000000
	.p2align	3, 0x0
__real@43e0000000000000:
	.quad	0x43e0000000000000
	.globl	__real@43efffffffffffff
	.section	.rdata,"dr",discard,__real@43efffffffffffff
	.p2align	3, 0x0
__real@43efffffffffffff:
	.quad	0x43efffffffffffff
	.section	.text,"xr",one_only,cc_many_args,unique,10
	.globl	cc_many_args
	.p2align	4
cc_many_args:
	addq	64(%rsp), %rcx
	movsd	144(%rsp), %xmm3
	addq	72(%rsp), %rcx
	movsd	__real@43e0000000000000(%rip), %xmm0
	movapd	%xmm3, %xmm1
	subsd	%xmm0, %xmm1
	cvttsd2si	%xmm1, %rax
	cvttsd2si	%xmm3, %r8
	movq	%r8, %rdx
	sarq	$63, %rdx
	andq	%rax, %rdx
	orq	%r8, %rdx
	xorl	%r8d, %r8d
	xorpd	%xmm1, %xmm1
	ucomisd	%xmm1, %xmm3
	cmovbq	%r8, %rdx
	movsd	__real@43efffffffffffff(%rip), %xmm2
	ucomisd	%xmm2, %xmm3
	movq	$-1, %r9
	cmovaq	%r9, %rdx
	movsd	80(%rsp), %xmm3
	addq	%rcx, %rdx
	addsd	88(%rsp), %xmm3
	addsd	96(%rsp), %xmm3
	addsd	104(%rsp), %xmm3
	addsd	112(%rsp), %xmm3
	addsd	120(%rsp), %xmm3
	addsd	128(%rsp), %xmm3
	addsd	136(%rsp), %xmm3
	movapd	%xmm3, %xmm4
	subsd	%xmm0, %xmm4
	cvttsd2si	%xmm4, %rcx
	cvttsd2si	%xmm3, %r10
	movq	%r10, %rax
	sarq	$63, %rax
	andq	%rcx, %rax
	orq	%r10, %rax
	ucomisd	%xmm1, %xmm3
	cmovbq	%r8, %rax
	ucomisd	%xmm2, %xmm3
	cmovaq	%r9, %rax
	addq	%rdx, %rax
	retq

	.def	cc_mixed_16b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_mixed_16b,unique,11
	.globl	cc_mixed_16b
	.p2align	4
cc_mixed_16b:
	movq	%rcx, %rax
	movq	(%rdx), %rcx
	incq	%rcx
	movsd	8(%rdx), %xmm0
	movq	%rcx, (%rax)
	movsd	%xmm0, 8(%rax)
	retq

	.def	cc_narrow_int;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_narrow_int,unique,12
	.globl	cc_narrow_int
	.p2align	4
cc_narrow_int:
	addl	%edx, %ecx
	leal	(%r9,%r8), %eax
	addb	%cl, %al
	retq

	.def	cc_overaligned_16b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_overaligned_16b,unique,13
	.globl	cc_overaligned_16b
	.p2align	4
cc_overaligned_16b:
	movl	%ecx, %eax
	addq	(%rdx), %rax
	addq	8(%rdx), %rax
	retq

	.def	cc_rust_call;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_call,unique,14
	.globl	cc_rust_call
	.p2align	4
cc_rust_call:
	movl	%edx, %eax
	addq	%r8, %rcx
	addq	%rcx, %rax
	retq

	.def	cc_rust_cold_ret;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_cold_ret,unique,15
	.globl	cc_rust_cold_ret
	.p2align	4
cc_rust_cold_ret:
	leaq	(%rcx,%rdx), %rax
	retq

	.def	cc_rust_cold_void;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_cold_void,unique,16
	.globl	cc_rust_cold_void
	.p2align	4
cc_rust_cold_void:
	movl	%edx, (%rcx)
	retq

	.def	cc_rust_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_f32,unique,17
	.globl	cc_rust_f32
	.p2align	4
cc_rust_f32:
	addss	%xmm1, %xmm0
	retq

	.def	cc_rust_pair;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_pair,unique,18
	.globl	cc_rust_pair
	.p2align	4
cc_rust_pair:
	movq	%rdx, %rax
	movq	%rcx, %rdx
	retq

	.def	cc_rust_slice;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_slice,unique,19
	.globl	cc_rust_slice
	.p2align	4
cc_rust_slice:
	movq	%rdx, %rax
	retq

	.def	cc_rust_triple;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_rust_triple,unique,20
	.globl	cc_rust_triple
	.p2align	4
cc_rust_triple:
	movq	%rcx, %rax
	movq	(%rdx), %rcx
	movdqu	8(%rdx), %xmm0
	pshufd	$78, %xmm0, %xmm0
	movdqu	%xmm0, (%rax)
	movq	%rcx, 16(%rax)
	retq

	.def	cc_struct_16b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_struct_16b,unique,21
	.globl	cc_struct_16b
	.p2align	4
cc_struct_16b:
	movq	%rcx, %rax
	movdqu	(%rdx), %xmm0
	pshufd	$78, %xmm0, %xmm0
	movdqu	%xmm0, (%rcx)
	retq

	.def	cc_track_caller;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_track_caller,unique,22
	.globl	cc_track_caller
	.p2align	4
cc_track_caller:
	movq	%rdx, %rax
	retq

	.def	cc_u128;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_u128,unique,23
	.globl	cc_u128
	.p2align	4
cc_u128:
	movl	%ecx, %eax
	movq	8(%rdx), %rcx
	addq	(%rdx), %rax
	adcq	$0, %rcx
	movq	%rax, %xmm0
	movq	%rcx, %xmm1
	punpcklqdq	%xmm1, %xmm0
	retq

	.def	cc_variadic_caller;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_variadic_caller,unique,24
	.globl	cc_variadic_caller
	.p2align	4
cc_variadic_caller:
.seh_proc cc_variadic_caller
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	%rcx, %rax
	movsbl	%r9b, %ecx
	movl	%ecx, 40(%rsp)
	movsd	%xmm2, 32(%rsp)
	movl	%edx, %ecx
	movb	$1, %dl
	movb	$2, %r8b
	movb	$3, %r9b
	callq	*%rax
	nop
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	cc_vec128_c;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_vec128_c,unique,25
	.globl	cc_vec128_c
	.p2align	4
cc_vec128_c:
	movaps	(%rcx), %xmm0
	retq

	.def	cc_vec128_rust;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_vec128_rust,unique,26
	.globl	cc_vec128_rust
	.p2align	4
cc_vec128_rust:
	movq	%rcx, %rax
	movaps	(%rdx), %xmm0
	movaps	%xmm0, (%rcx)
	retq

	.def	cc_vectorcall@@40;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_vectorcall@@40,unique,27
	.globl	cc_vectorcall@@40
	.p2align	4
cc_vectorcall@@40:
	movq	%rcx, %rax
	movq	40(%rsp), %rcx
	movups	(%rcx), %xmm0
	movups	%xmm0, (%rax)
	retq

	.def	cc_zst_and_transparent;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_zst_and_transparent,unique,28
	.globl	cc_zst_and_transparent
	.p2align	4
cc_zst_and_transparent:
	leal	1(%rdx), %eax
	retq

	.globl	cc_struct_24b
	.def	cc_struct_24b;
	.scl	2;
	.type	32;
	.endef
cc_struct_24b = cc_rust_triple
	.globl	cc_struct_8b
	.def	cc_struct_8b;
	.scl	2;
	.type	32;
	.endef
cc_struct_8b = cc_hfa2_f32
	.globl	_fltused
