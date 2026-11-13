	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 1
	.att_syntax
	.file	"calling_conv_corpus.75f08b44548a9e00-cgu.0"
	.def	__RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,unique,0
	.globl	__RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.p2align	4
__RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind:
	.p2align	4
LBB0_1:
	jmp	LBB0_1

	.def	_cc_c_nounwind;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_c_nounwind,unique,1
	.globl	_cc_c_nounwind
	.p2align	4
_cc_c_nounwind:
	movl	4(%esp), %eax
	incl	%eax
	retl

	.def	_cc_c_unwind;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_c_unwind,unique,2
	.globl	_cc_c_unwind
	.p2align	4
_cc_c_unwind:
	pushl	8(%esp)
	calll	*8(%esp)
	addl	$4, %esp
	incl	%eax
	retl

	.def	_cc_f16_f128;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_f16_f128,unique,3
	.globl	_cc_f16_f128
	.p2align	4
_cc_f16_f128:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%edi
	pushl	%esi
	andl	$-16, %esp
	movl	8(%ebp), %eax
	movl	36(%ebp), %edi
	movl	24(%ebp), %ecx
	movl	28(%ebp), %edx
	movl	32(%ebp), %esi
	movl	%edi, 12(%eax)
	movl	%esi, 8(%eax)
	movl	%edx, 4(%eax)
	movl	%ecx, (%eax)
	leal	-8(%ebp), %esp
	popl	%esi
	popl	%edi
	popl	%ebp
	retl

	.def	_cc_hfa2_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_hfa2_f32,unique,4
	.globl	_cc_hfa2_f32
	.p2align	4
_cc_hfa2_f32:
	movl	4(%esp), %edx
	movl	8(%esp), %eax
	retl

	.def	_cc_hfa4_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_hfa4_f32,unique,5
	.globl	_cc_hfa4_f32
	.p2align	4
_cc_hfa4_f32:
	movups	8(%esp), %xmm0
	movl	4(%esp), %eax
	shufps	$27, %xmm0, %xmm0
	movups	%xmm0, (%eax)
	retl

	.def	_cc_hfa5_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_hfa5_f32,unique,6
	.globl	_cc_hfa5_f32
	.p2align	4
_cc_hfa5_f32:
	movups	12(%esp), %xmm1
	movl	4(%esp), %eax
	movss	8(%esp), %xmm0
	shufps	$147, %xmm1, %xmm1
	movups	%xmm1, (%eax)
	movss	%xmm0, 16(%eax)
	retl

	.def	_cc_hva2_c;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_hva2_c,unique,7
	.globl	_cc_hva2_c
	.p2align	4
_cc_hva2_c:
	movl	4(%esp), %eax
	movups	24(%esp), %xmm1
	movups	8(%esp), %xmm0
	movaps	%xmm1, (%eax)
	movaps	%xmm0, 16(%eax)
	retl

	.def	_cc_many_args;
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
	.section	.text,"xr",one_only,_cc_many_args,unique,8
	.globl	_cc_many_args
	.p2align	4
_cc_many_args:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	pushl	%edi
	pushl	%esi
	andl	$-8, %esp
	subl	$32, %esp
	movl	64(%ebp), %eax
	movl	68(%ebp), %edx
	movsd	__real@43e0000000000000, %xmm2
	movsd	144(%ebp), %xmm4
	xorpd	%xmm1, %xmm1
	addl	8(%ebp), %eax
	movapd	%xmm2, %xmm3
	adcl	12(%ebp), %edx
	addl	72(%ebp), %eax
	adcl	76(%ebp), %edx
	ucomisd	%xmm4, %xmm2
	jbe	LBB8_2
	xorpd	%xmm3, %xmm3
LBB8_2:
	movapd	%xmm4, %xmm5
	setbe	%bl
	movsd	80(%ebp), %xmm0
	movl	$0, %edi
	movl	$0, %esi
	subsd	%xmm3, %xmm5
	movsd	%xmm5, 8(%esp)
	fldl	8(%esp)
	fnstcw	2(%esp)
	movzwl	2(%esp), %ecx
	orl	$3072, %ecx
	movw	%cx, 6(%esp)
	xorl	%ecx, %ecx
	ucomisd	%xmm1, %xmm4
	fldcw	6(%esp)
	fistpll	8(%esp)
	fldcw	2(%esp)
	jb	LBB8_4
	movzbl	%bl, %edi
	movl	8(%esp), %esi
	shll	$31, %edi
	xorl	12(%esp), %edi
LBB8_4:
	addsd	88(%ebp), %xmm0
	movsd	__real@43efffffffffffff, %xmm3
	movl	$-1, %ebx
	addsd	96(%ebp), %xmm0
	ucomisd	%xmm3, %xmm4
	cmoval	%ebx, %esi
	cmoval	%ebx, %edi
	addl	%esi, %eax
	adcl	%edi, %edx
	addsd	104(%ebp), %xmm0
	addsd	112(%ebp), %xmm0
	addsd	120(%ebp), %xmm0
	addsd	128(%ebp), %xmm0
	addsd	136(%ebp), %xmm0
	ucomisd	%xmm2, %xmm0
	jae	LBB8_6
	xorpd	%xmm2, %xmm2
LBB8_6:
	movapd	%xmm0, %xmm4
	setae	%bl
	subsd	%xmm2, %xmm4
	movsd	%xmm4, 16(%esp)
	fldl	16(%esp)
	fnstcw	(%esp)
	movzwl	(%esp), %esi
	orl	$3072, %esi
	ucomisd	%xmm1, %xmm0
	movw	%si, 4(%esp)
	movl	$0, %esi
	fldcw	4(%esp)
	fistpll	16(%esp)
	fldcw	(%esp)
	jb	LBB8_8
	movzbl	%bl, %ecx
	movl	16(%esp), %esi
	shll	$31, %ecx
	xorl	20(%esp), %ecx
LBB8_8:
	ucomisd	%xmm3, %xmm0
	movl	$-1, %edi
	cmoval	%edi, %esi
	cmoval	%edi, %ecx
	addl	%esi, %eax
	adcl	%ecx, %edx
	leal	-12(%ebp), %esp
	popl	%esi
	popl	%edi
	popl	%ebx
	popl	%ebp
	retl

	.def	_cc_mixed_16b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_mixed_16b,unique,9
	.globl	_cc_mixed_16b
	.p2align	4
_cc_mixed_16b:
	movl	8(%esp), %ecx
	movl	12(%esp), %edx
	movl	4(%esp), %eax
	movsd	16(%esp), %xmm0
	addl	$1, %ecx
	adcl	$0, %edx
	movl	%ecx, (%eax)
	movl	%edx, 4(%eax)
	movsd	%xmm0, 8(%eax)
	retl

	.def	_cc_narrow_int;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_narrow_int,unique,10
	.globl	_cc_narrow_int
	.p2align	4
_cc_narrow_int:
	movzbl	8(%esp), %eax
	addb	4(%esp), %al
	addb	12(%esp), %al
	addb	16(%esp), %al
	retl

	.def	_cc_overaligned_16b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_overaligned_16b,unique,11
	.globl	_cc_overaligned_16b
	.p2align	4
_cc_overaligned_16b:
	movl	8(%esp), %ecx
	movl	(%ecx), %eax
	movl	4(%ecx), %edx
	addl	4(%esp), %eax
	adcl	$0, %edx
	addl	8(%ecx), %eax
	adcl	12(%ecx), %edx
	retl

	.def	_cc_rust_call;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_rust_call,unique,12
	.globl	_cc_rust_call
	.p2align	4
_cc_rust_call:
	movl	8(%esp), %eax
	xorl	%edx, %edx
	addl	4(%esp), %eax
	setb	%dl
	addl	12(%esp), %eax
	adcl	16(%esp), %edx
	retl

	.def	_cc_rust_f32;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_rust_f32,unique,13
	.globl	_cc_rust_f32
	.p2align	4
_cc_rust_f32:
	movss	4(%esp), %xmm0
	addss	8(%esp), %xmm0
	retl

	.def	_cc_rust_pair;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_rust_pair,unique,14
	.globl	_cc_rust_pair
	.p2align	4
_cc_rust_pair:
	pushl	%edi
	pushl	%esi
	movl	12(%esp), %eax
	movl	24(%esp), %esi
	movl	28(%esp), %edi
	movl	16(%esp), %ecx
	movl	20(%esp), %edx
	movl	%edi, 4(%eax)
	movl	%esi, (%eax)
	movl	%edx, 12(%eax)
	movl	%ecx, 8(%eax)
	popl	%esi
	popl	%edi
	retl

	.def	_cc_rust_slice;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_rust_slice,unique,15
	.globl	_cc_rust_slice
	.p2align	4
_cc_rust_slice:
	movl	8(%esp), %eax
	retl

	.def	_cc_rust_triple;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_rust_triple,unique,16
	.globl	_cc_rust_triple
	.p2align	4
_cc_rust_triple:
	pushl	%esi
	movl	12(%esp), %ecx
	movl	8(%esp), %eax
	movdqu	8(%ecx), %xmm0
	movl	(%ecx), %edx
	movl	4(%ecx), %esi
	pshufd	$78, %xmm0, %xmm0
	movdqu	%xmm0, (%eax)
	movl	%edx, 16(%eax)
	movl	%esi, 20(%eax)
	popl	%esi
	retl

	.def	_cc_struct_16b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_struct_16b,unique,17
	.globl	_cc_struct_16b
	.p2align	4
_cc_struct_16b:
	movdqu	8(%esp), %xmm0
	movl	4(%esp), %eax
	pshufd	$78, %xmm0, %xmm0
	movdqu	%xmm0, (%eax)
	retl

	.def	_cc_struct_24b;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_struct_24b,unique,18
	.globl	_cc_struct_24b
	.p2align	4
_cc_struct_24b:
	movdqu	16(%esp), %xmm0
	movl	4(%esp), %eax
	movl	8(%esp), %ecx
	movl	12(%esp), %edx
	pshufd	$78, %xmm0, %xmm0
	movdqu	%xmm0, (%eax)
	movl	%ecx, 16(%eax)
	movl	%edx, 20(%eax)
	retl

	.def	_cc_track_caller;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_track_caller,unique,19
	.globl	_cc_track_caller
	.p2align	4
_cc_track_caller:
	movl	8(%esp), %eax
	retl

	.def	_cc_u128;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_u128,unique,20
	.globl	_cc_u128
	.p2align	4
_cc_u128:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%edi
	pushl	%esi
	andl	$-16, %esp
	movl	24(%ebp), %esi
	movl	28(%ebp), %edi
	movl	32(%ebp), %edx
	movl	36(%ebp), %ecx
	movl	8(%ebp), %eax
	addl	12(%ebp), %esi
	adcl	$0, %edi
	adcl	$0, %edx
	adcl	$0, %ecx
	movl	%edx, 8(%eax)
	movl	%edi, 4(%eax)
	movl	%esi, (%eax)
	movl	%ecx, 12(%eax)
	leal	-8(%ebp), %esp
	popl	%esi
	popl	%edi
	popl	%ebp
	retl

	.def	_cc_variadic_caller;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_variadic_caller,unique,21
	.globl	_cc_variadic_caller
	.p2align	4
_cc_variadic_caller:
	subl	$28, %esp
	movl	36(%esp), %eax
	movsd	40(%esp), %xmm0
	movsbl	48(%esp), %ecx
	movl	$3, 12(%esp)
	movl	$2, 8(%esp)
	movl	$1, 4(%esp)
	movl	%ecx, 24(%esp)
	movsd	%xmm0, 16(%esp)
	movl	%eax, (%esp)
	calll	*32(%esp)
	addl	$28, %esp
	retl

	.def	_cc_vec128_c;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_vec128_c,unique,22
	.globl	_cc_vec128_c
	.p2align	4
_cc_vec128_c:
	retl

	.def	_cc_vec128_rust;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_vec128_rust,unique,23
	.globl	_cc_vec128_rust
	.p2align	4
_cc_vec128_rust:
	movl	8(%esp), %ecx
	movl	4(%esp), %eax
	movaps	(%ecx), %xmm0
	movaps	%xmm0, (%eax)
	retl

	.def	cc_vectorcall@@40;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,cc_vectorcall@@40,unique,24
	.globl	cc_vectorcall@@40
	.p2align	4
cc_vectorcall@@40:
	movl	4(%esp), %eax
	movsd	8(%esp), %xmm0
	movsd	16(%esp), %xmm1
	movsd	%xmm1, 8(%eax)
	movsd	%xmm0, (%eax)
	retl	$20

	.def	@cc_x86_fastcall@12;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,@cc_x86_fastcall@12,unique,25
	.globl	@cc_x86_fastcall@12
	.p2align	4
@cc_x86_fastcall@12:
	leal	(%ecx,%edx), %eax
	addl	4(%esp), %eax
	retl	$4

	.def	_cc_x86_stdcall@12;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_x86_stdcall@12,unique,26
	.globl	_cc_x86_stdcall@12
	.p2align	4
_cc_x86_stdcall@12:
	movl	8(%esp), %eax
	addl	4(%esp), %eax
	addl	12(%esp), %eax
	retl	$12

	.def	_cc_x86_thiscall;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_cc_x86_thiscall,unique,27
	.globl	_cc_x86_thiscall
	.p2align	4
_cc_x86_thiscall:
	movl	%ecx, %eax
	addl	4(%esp), %eax
	addl	8(%esp), %eax
	retl	$8

	.globl	_cc_zst_and_transparent
	.def	_cc_zst_and_transparent;
	.scl	2;
	.type	32;
	.endef
_cc_zst_and_transparent = _cc_c_nounwind
	.globl	_cc_struct_8b
	.def	_cc_struct_8b;
	.scl	2;
	.type	32;
	.endef
_cc_struct_8b = _cc_hfa2_f32
	.globl	__fltused
