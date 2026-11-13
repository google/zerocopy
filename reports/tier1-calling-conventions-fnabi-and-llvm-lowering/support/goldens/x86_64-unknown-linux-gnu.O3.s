	.att_syntax
	.file	"calling_conv_corpus.75f08b44548a9e00-cgu.0"
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

	.section	.text.cc_c_nounwind,"ax",@progbits
	.globl	cc_c_nounwind
	.prefalign	4, .Lfunc_end1, nop
	.type	cc_c_nounwind,@function
cc_c_nounwind:
	.cfi_startproc
	leal	1(%rdi), %eax
	retq
.Lfunc_end1:
	.size	cc_c_nounwind, .Lfunc_end1-cc_c_nounwind
	.cfi_endproc

	.section	.text.cc_c_unwind,"ax",@progbits
	.globl	cc_c_unwind
	.prefalign	4, .Lfunc_end2, nop
	.type	cc_c_unwind,@function
cc_c_unwind:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	movq	%rdi, %rax
	movl	%esi, %edi
	callq	*%rax
	incl	%eax
	popq	%rcx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end2:
	.size	cc_c_unwind, .Lfunc_end2-cc_c_unwind
	.cfi_endproc

	.section	.text.cc_explicit_sysv64,"ax",@progbits
	.globl	cc_explicit_sysv64
	.prefalign	4, .Lfunc_end3, nop
	.type	cc_explicit_sysv64,@function
cc_explicit_sysv64:
	.cfi_startproc
	leaq	(%rdi,%rdx), %rax
	leaq	(%rsi,%rcx), %rdx
	retq
.Lfunc_end3:
	.size	cc_explicit_sysv64, .Lfunc_end3-cc_explicit_sysv64
	.cfi_endproc

	.section	.text.cc_explicit_win64,"ax",@progbits
	.globl	cc_explicit_win64
	.prefalign	4, .Lfunc_end4, nop
	.type	cc_explicit_win64,@function
cc_explicit_win64:
	.cfi_startproc
	addq	(%r9), %rdx
	addq	8(%r9), %r8
	movq	%rcx, %rax
	movq	%rdx, (%rcx)
	movq	%r8, 8(%rcx)
	retq
.Lfunc_end4:
	.size	cc_explicit_win64, .Lfunc_end4-cc_explicit_win64
	.cfi_endproc

	.section	.text.cc_f16_f128,"ax",@progbits
	.globl	cc_f16_f128
	.prefalign	4, .Lfunc_end5, nop
	.type	cc_f16_f128,@function
cc_f16_f128:
	.cfi_startproc
	movaps	%xmm1, %xmm0
	retq
.Lfunc_end5:
	.size	cc_f16_f128, .Lfunc_end5-cc_f16_f128
	.cfi_endproc

	.section	.text.cc_hfa2_f32,"ax",@progbits
	.globl	cc_hfa2_f32
	.prefalign	4, .Lfunc_end6, nop
	.type	cc_hfa2_f32,@function
cc_hfa2_f32:
	.cfi_startproc
	movq	%xmm0, %rax
	rolq	$32, %rax
	movq	%rax, %xmm0
	retq
.Lfunc_end6:
	.size	cc_hfa2_f32, .Lfunc_end6-cc_hfa2_f32
	.cfi_endproc

	.section	.text.cc_hfa4_f32,"ax",@progbits
	.globl	cc_hfa4_f32
	.prefalign	4, .Lfunc_end7, nop
	.type	cc_hfa4_f32,@function
cc_hfa4_f32:
	.cfi_startproc
	movq	%xmm0, %rax
	movq	%xmm1, %rcx
	rolq	$32, %rcx
	rolq	$32, %rax
	movq	%rcx, %xmm0
	movq	%rax, %xmm1
	retq
.Lfunc_end7:
	.size	cc_hfa4_f32, .Lfunc_end7-cc_hfa4_f32
	.cfi_endproc

	.section	.text.cc_hfa5_f32,"ax",@progbits
	.globl	cc_hfa5_f32
	.prefalign	4, .Lfunc_end8, nop
	.type	cc_hfa5_f32,@function
cc_hfa5_f32:
	.cfi_startproc
	movq	%rdi, %rax
	movss	8(%rsp), %xmm0
	movups	12(%rsp), %xmm1
	shufps	$147, %xmm1, %xmm1
	movups	%xmm1, (%rdi)
	movss	%xmm0, 16(%rdi)
	retq
.Lfunc_end8:
	.size	cc_hfa5_f32, .Lfunc_end8-cc_hfa5_f32
	.cfi_endproc

	.section	.text.cc_hva2_c,"ax",@progbits
	.globl	cc_hva2_c
	.prefalign	4, .Lfunc_end9, nop
	.type	cc_hva2_c,@function
cc_hva2_c:
	.cfi_startproc
	movq	%rdi, %rax
	movaps	8(%rsp), %xmm0
	movaps	24(%rsp), %xmm1
	movaps	%xmm1, (%rdi)
	movaps	%xmm0, 16(%rdi)
	retq
.Lfunc_end9:
	.size	cc_hva2_c, .Lfunc_end9-cc_hva2_c
	.cfi_endproc

	.section	.rodata.cst8,"aM",@progbits,8
	.p2align	3, 0x0
.LCPI10_0:
	.quad	0x43e0000000000000
.LCPI10_1:
	.quad	0x43efffffffffffff
	.section	.text.cc_many_args,"ax",@progbits
	.globl	cc_many_args
	.prefalign	4, .Lfunc_end10, nop
	.type	cc_many_args,@function
cc_many_args:
	.cfi_startproc
	addq	16(%rsp), %rdi
	movsd	32(%rsp), %xmm11
	addq	24(%rsp), %rdi
	movsd	.LCPI10_0(%rip), %xmm8
	movapd	%xmm11, %xmm9
	subsd	%xmm8, %xmm9
	cvttsd2si	%xmm9, %rax
	cvttsd2si	%xmm11, %rdx
	movq	%rdx, %rcx
	sarq	$63, %rcx
	andq	%rax, %rcx
	orq	%rdx, %rcx
	xorl	%edx, %edx
	xorpd	%xmm9, %xmm9
	ucomisd	%xmm9, %xmm11
	cmovbq	%rdx, %rcx
	movsd	.LCPI10_1(%rip), %xmm10
	ucomisd	%xmm10, %xmm11
	movq	$-1, %rsi
	cmovaq	%rsi, %rcx
	addq	%rdi, %rcx
	addsd	%xmm1, %xmm0
	addsd	%xmm2, %xmm0
	addsd	%xmm3, %xmm0
	addsd	%xmm4, %xmm0
	addsd	%xmm5, %xmm0
	addsd	%xmm6, %xmm0
	addsd	%xmm7, %xmm0
	cvttsd2si	%xmm0, %rdi
	movq	%rdi, %r8
	sarq	$63, %r8
	movapd	%xmm0, %xmm1
	subsd	%xmm8, %xmm1
	cvttsd2si	%xmm1, %rax
	andq	%r8, %rax
	orq	%rdi, %rax
	ucomisd	%xmm9, %xmm0
	cmovbq	%rdx, %rax
	ucomisd	%xmm10, %xmm0
	cmovaq	%rsi, %rax
	addq	%rcx, %rax
	retq
.Lfunc_end10:
	.size	cc_many_args, .Lfunc_end10-cc_many_args
	.cfi_endproc

	.section	.text.cc_mixed_16b,"ax",@progbits
	.globl	cc_mixed_16b
	.prefalign	4, .Lfunc_end11, nop
	.type	cc_mixed_16b,@function
cc_mixed_16b:
	.cfi_startproc
	leaq	1(%rdi), %rax
	retq
.Lfunc_end11:
	.size	cc_mixed_16b, .Lfunc_end11-cc_mixed_16b
	.cfi_endproc

	.section	.text.cc_narrow_int,"ax",@progbits
	.globl	cc_narrow_int
	.prefalign	4, .Lfunc_end12, nop
	.type	cc_narrow_int,@function
cc_narrow_int:
	.cfi_startproc
	addl	%edi, %esi
	leal	(%rcx,%rdx), %eax
	addb	%sil, %al
	retq
.Lfunc_end12:
	.size	cc_narrow_int, .Lfunc_end12-cc_narrow_int
	.cfi_endproc

	.section	.text.cc_overaligned_16b,"ax",@progbits
	.globl	cc_overaligned_16b
	.prefalign	4, .Lfunc_end13, nop
	.type	cc_overaligned_16b,@function
cc_overaligned_16b:
	.cfi_startproc
	movl	%edi, %eax
	addq	%rsi, %rax
	addq	%rdx, %rax
	retq
.Lfunc_end13:
	.size	cc_overaligned_16b, .Lfunc_end13-cc_overaligned_16b
	.cfi_endproc

	.section	.text.cc_rust_call,"ax",@progbits
	.globl	cc_rust_call
	.prefalign	4, .Lfunc_end14, nop
	.type	cc_rust_call,@function
cc_rust_call:
	.cfi_startproc
	movl	%esi, %eax
	addq	%rdi, %rax
	addq	%rdx, %rax
	retq
.Lfunc_end14:
	.size	cc_rust_call, .Lfunc_end14-cc_rust_call
	.cfi_endproc

	.section	.text.cc_rust_cold_ret,"ax",@progbits
	.globl	cc_rust_cold_ret
	.prefalign	4, .Lfunc_end15, nop
	.type	cc_rust_cold_ret,@function
cc_rust_cold_ret:
	.cfi_startproc
	leaq	(%rdi,%rsi), %rax
	retq
.Lfunc_end15:
	.size	cc_rust_cold_ret, .Lfunc_end15-cc_rust_cold_ret
	.cfi_endproc

	.section	.text.cc_rust_cold_void,"ax",@progbits
	.globl	cc_rust_cold_void
	.prefalign	4, .Lfunc_end16, nop
	.type	cc_rust_cold_void,@function
cc_rust_cold_void:
	.cfi_startproc
	movl	%esi, (%rdi)
	retq
.Lfunc_end16:
	.size	cc_rust_cold_void, .Lfunc_end16-cc_rust_cold_void
	.cfi_endproc

	.section	.text.cc_rust_f32,"ax",@progbits
	.globl	cc_rust_f32
	.prefalign	4, .Lfunc_end17, nop
	.type	cc_rust_f32,@function
cc_rust_f32:
	.cfi_startproc
	addss	%xmm1, %xmm0
	retq
.Lfunc_end17:
	.size	cc_rust_f32, .Lfunc_end17-cc_rust_f32
	.cfi_endproc

	.section	.text.cc_rust_pair,"ax",@progbits
	.globl	cc_rust_pair
	.prefalign	4, .Lfunc_end18, nop
	.type	cc_rust_pair,@function
cc_rust_pair:
	.cfi_startproc
	movq	%rsi, %rax
	movq	%rdi, %rdx
	retq
.Lfunc_end18:
	.size	cc_rust_pair, .Lfunc_end18-cc_rust_pair
	.cfi_endproc

	.section	.text.cc_rust_slice,"ax",@progbits
	.globl	cc_rust_slice
	.prefalign	4, .Lfunc_end19, nop
	.type	cc_rust_slice,@function
cc_rust_slice:
	.cfi_startproc
	movq	%rsi, %rax
	retq
.Lfunc_end19:
	.size	cc_rust_slice, .Lfunc_end19-cc_rust_slice
	.cfi_endproc

	.section	.text.cc_rust_triple,"ax",@progbits
	.globl	cc_rust_triple
	.prefalign	4, .Lfunc_end20, nop
	.type	cc_rust_triple,@function
cc_rust_triple:
	.cfi_startproc
	movq	%rdi, %rax
	movq	(%rsi), %rcx
	movdqu	8(%rsi), %xmm0
	pshufd	$78, %xmm0, %xmm0
	movdqu	%xmm0, (%rdi)
	movq	%rcx, 16(%rdi)
	retq
.Lfunc_end20:
	.size	cc_rust_triple, .Lfunc_end20-cc_rust_triple
	.cfi_endproc

	.section	.text.cc_struct_16b,"ax",@progbits
	.globl	cc_struct_16b
	.prefalign	4, .Lfunc_end21, nop
	.type	cc_struct_16b,@function
cc_struct_16b:
	.cfi_startproc
	movq	%rsi, %rax
	movq	%rdi, %rdx
	retq
.Lfunc_end21:
	.size	cc_struct_16b, .Lfunc_end21-cc_struct_16b
	.cfi_endproc

	.section	.text.cc_struct_24b,"ax",@progbits
	.globl	cc_struct_24b
	.prefalign	4, .Lfunc_end22, nop
	.type	cc_struct_24b,@function
cc_struct_24b:
	.cfi_startproc
	movq	%rdi, %rax
	movq	8(%rsp), %rcx
	movdqu	16(%rsp), %xmm0
	pshufd	$78, %xmm0, %xmm0
	movdqu	%xmm0, (%rdi)
	movq	%rcx, 16(%rdi)
	retq
.Lfunc_end22:
	.size	cc_struct_24b, .Lfunc_end22-cc_struct_24b
	.cfi_endproc

	.section	.text.cc_struct_8b,"ax",@progbits
	.globl	cc_struct_8b
	.prefalign	4, .Lfunc_end23, nop
	.type	cc_struct_8b,@function
cc_struct_8b:
	.cfi_startproc
	movq	%rdi, %rax
	rolq	$32, %rax
	retq
.Lfunc_end23:
	.size	cc_struct_8b, .Lfunc_end23-cc_struct_8b
	.cfi_endproc

	.section	.text.cc_track_caller,"ax",@progbits
	.globl	cc_track_caller
	.prefalign	4, .Lfunc_end24, nop
	.type	cc_track_caller,@function
cc_track_caller:
	.cfi_startproc
	movq	%rsi, %rax
	retq
.Lfunc_end24:
	.size	cc_track_caller, .Lfunc_end24-cc_track_caller
	.cfi_endproc

	.section	.text.cc_u128,"ax",@progbits
	.globl	cc_u128
	.prefalign	4, .Lfunc_end25, nop
	.type	cc_u128,@function
cc_u128:
	.cfi_startproc
	movl	%edi, %eax
	addq	%rsi, %rax
	adcq	$0, %rdx
	retq
.Lfunc_end25:
	.size	cc_u128, .Lfunc_end25-cc_u128
	.cfi_endproc

	.section	.text.cc_variadic_caller,"ax",@progbits
	.globl	cc_variadic_caller
	.prefalign	4, .Lfunc_end26, nop
	.type	cc_variadic_caller,@function
cc_variadic_caller:
	.cfi_startproc
	movl	%edx, %r8d
	movq	%rdi, %r9
	movl	%esi, %edi
	movl	$1, %esi
	movl	$2, %edx
	movl	$3, %ecx
	movb	$1, %al
	jmpq	*%r9
.Lfunc_end26:
	.size	cc_variadic_caller, .Lfunc_end26-cc_variadic_caller
	.cfi_endproc

	.section	.text.cc_vec128_c,"ax",@progbits
	.globl	cc_vec128_c
	.prefalign	4, .Lfunc_end27, nop
	.type	cc_vec128_c,@function
cc_vec128_c:
	.cfi_startproc
	retq
.Lfunc_end27:
	.size	cc_vec128_c, .Lfunc_end27-cc_vec128_c
	.cfi_endproc

	.section	.text.cc_vec128_rust,"ax",@progbits
	.globl	cc_vec128_rust
	.prefalign	4, .Lfunc_end28, nop
	.type	cc_vec128_rust,@function
cc_vec128_rust:
	.cfi_startproc
	movq	%rdi, %rax
	movaps	(%rsi), %xmm0
	movaps	%xmm0, (%rdi)
	retq
.Lfunc_end28:
	.size	cc_vec128_rust, .Lfunc_end28-cc_vec128_rust
	.cfi_endproc

	.section	".text.cc_vectorcall@@40","ax",@progbits
	.globl	"cc_vectorcall@@40"
	.prefalign	4, .Lfunc_end29, nop
	.type	"cc_vectorcall@@40",@function
"cc_vectorcall@@40":
	.cfi_startproc
	movq	%rcx, %rax
	movq	8(%rsp), %rcx
	movups	(%rcx), %xmm0
	movups	%xmm0, (%rax)
	retq
.Lfunc_end29:
	.size	"cc_vectorcall@@40", .Lfunc_end29-"cc_vectorcall@@40"
	.cfi_endproc

	.globl	cc_zst_and_transparent
	.type	cc_zst_and_transparent,@function
cc_zst_and_transparent = cc_c_nounwind
	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
