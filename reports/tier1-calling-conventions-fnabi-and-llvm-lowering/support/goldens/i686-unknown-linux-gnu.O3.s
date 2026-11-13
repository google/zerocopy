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
	movl	4(%esp), %eax
	incl	%eax
	retl
.Lfunc_end1:
	.size	cc_c_nounwind, .Lfunc_end1-cc_c_nounwind
	.cfi_endproc

	.section	.text.cc_c_unwind,"ax",@progbits
	.globl	cc_c_unwind
	.prefalign	4, .Lfunc_end2, nop
	.type	cc_c_unwind,@function
cc_c_unwind:
	.cfi_startproc
	subl	$12, %esp
	.cfi_def_cfa_offset 16
	movl	20(%esp), %eax
	movl	%eax, (%esp)
	calll	*16(%esp)
	incl	%eax
	addl	$12, %esp
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end2:
	.size	cc_c_unwind, .Lfunc_end2-cc_c_unwind
	.cfi_endproc

	.section	.text.cc_f16_f128,"ax",@progbits
	.globl	cc_f16_f128
	.prefalign	4, .Lfunc_end3, nop
	.type	cc_f16_f128,@function
cc_f16_f128:
	.cfi_startproc
	subl	$12, %esp
	.cfi_def_cfa_offset 16
	movl	16(%esp), %eax
	movaps	32(%esp), %xmm0
	movaps	%xmm0, (%eax)
	addl	$12, %esp
	.cfi_def_cfa_offset 4
	retl	$4
.Lfunc_end3:
	.size	cc_f16_f128, .Lfunc_end3-cc_f16_f128
	.cfi_endproc

	.section	.text.cc_hfa2_f32,"ax",@progbits
	.globl	cc_hfa2_f32
	.prefalign	4, .Lfunc_end4, nop
	.type	cc_hfa2_f32,@function
cc_hfa2_f32:
	.cfi_startproc
	movsd	8(%esp), %xmm0
	movl	4(%esp), %eax
	shufps	$225, %xmm0, %xmm0
	movlps	%xmm0, (%eax)
	retl	$4
.Lfunc_end4:
	.size	cc_hfa2_f32, .Lfunc_end4-cc_hfa2_f32
	.cfi_endproc

	.section	.text.cc_hfa4_f32,"ax",@progbits
	.globl	cc_hfa4_f32
	.prefalign	4, .Lfunc_end5, nop
	.type	cc_hfa4_f32,@function
cc_hfa4_f32:
	.cfi_startproc
	movups	8(%esp), %xmm0
	movl	4(%esp), %eax
	shufps	$27, %xmm0, %xmm0
	movups	%xmm0, (%eax)
	retl	$4
.Lfunc_end5:
	.size	cc_hfa4_f32, .Lfunc_end5-cc_hfa4_f32
	.cfi_endproc

	.section	.text.cc_hfa5_f32,"ax",@progbits
	.globl	cc_hfa5_f32
	.prefalign	4, .Lfunc_end6, nop
	.type	cc_hfa5_f32,@function
cc_hfa5_f32:
	.cfi_startproc
	movups	12(%esp), %xmm1
	movl	4(%esp), %eax
	movss	8(%esp), %xmm0
	shufps	$147, %xmm1, %xmm1
	movups	%xmm1, (%eax)
	movss	%xmm0, 16(%eax)
	retl	$4
.Lfunc_end6:
	.size	cc_hfa5_f32, .Lfunc_end6-cc_hfa5_f32
	.cfi_endproc

	.section	.text.cc_hva2_c,"ax",@progbits
	.globl	cc_hva2_c
	.prefalign	4, .Lfunc_end7, nop
	.type	cc_hva2_c,@function
cc_hva2_c:
	.cfi_startproc
	movl	4(%esp), %eax
	movups	24(%esp), %xmm1
	movups	8(%esp), %xmm0
	movaps	%xmm1, (%eax)
	movaps	%xmm0, 16(%eax)
	retl	$4
.Lfunc_end7:
	.size	cc_hva2_c, .Lfunc_end7-cc_hva2_c
	.cfi_endproc

	.section	.rodata.cst8,"aM",@progbits,8
	.p2align	3, 0x0
.LCPI8_0:
	.quad	0x43e0000000000000
.LCPI8_1:
	.quad	0x43efffffffffffff
	.section	.text.cc_many_args,"ax",@progbits
	.globl	cc_many_args
	.prefalign	4, .Lfunc_end8, nop
	.type	cc_many_args,@function
cc_many_args:
	.cfi_startproc
	pushl	%ebp
	.cfi_def_cfa_offset 8
	pushl	%ebx
	.cfi_def_cfa_offset 12
	pushl	%edi
	.cfi_def_cfa_offset 16
	pushl	%esi
	.cfi_def_cfa_offset 20
	subl	$28, %esp
	.cfi_def_cfa_offset 48
	.cfi_offset %esi, -20
	.cfi_offset %edi, -16
	.cfi_offset %ebx, -12
	.cfi_offset %ebp, -8
	movl	104(%esp), %eax
	calll	.L8$pb
	.cfi_adjust_cfa_offset 4
.L8$pb:
	popl	%esi
	.cfi_adjust_cfa_offset -4
	movl	108(%esp), %edx
	movsd	184(%esp), %xmm4
	xorpd	%xmm1, %xmm1
.Ltmp0:
	addl	$_GLOBAL_OFFSET_TABLE_+(.Ltmp0-.L8$pb), %esi
	movsd	.LCPI8_0@GOTOFF(%esi), %xmm2
	addl	48(%esp), %eax
	movapd	%xmm2, %xmm3
	adcl	52(%esp), %edx
	addl	112(%esp), %eax
	adcl	116(%esp), %edx
	ucomisd	%xmm4, %xmm2
	jbe	.LBB8_2
	xorpd	%xmm3, %xmm3
.LBB8_2:
	movapd	%xmm4, %xmm5
	setbe	%bl
	movsd	120(%esp), %xmm0
	movl	$0, %edi
	movl	$0, %ebp
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
	jb	.LBB8_4
	movzbl	%bl, %edi
	movl	8(%esp), %ebp
	shll	$31, %edi
	xorl	12(%esp), %edi
.LBB8_4:
	addsd	128(%esp), %xmm0
	movsd	.LCPI8_1@GOTOFF(%esi), %xmm3
	movl	$-1, %esi
	addsd	136(%esp), %xmm0
	ucomisd	%xmm3, %xmm4
	cmoval	%esi, %ebp
	cmoval	%esi, %edi
	addl	%ebp, %eax
	adcl	%edi, %edx
	addsd	144(%esp), %xmm0
	addsd	152(%esp), %xmm0
	addsd	160(%esp), %xmm0
	addsd	168(%esp), %xmm0
	addsd	176(%esp), %xmm0
	ucomisd	%xmm2, %xmm0
	jae	.LBB8_6
	xorpd	%xmm2, %xmm2
.LBB8_6:
	movapd	%xmm0, %xmm4
	setae	%bl
	subsd	%xmm2, %xmm4
	movsd	%xmm4, 16(%esp)
	fldl	16(%esp)
	fnstcw	(%esp)
	movzwl	(%esp), %edi
	orl	$3072, %edi
	ucomisd	%xmm1, %xmm0
	movw	%di, 4(%esp)
	movl	$0, %edi
	fldcw	4(%esp)
	fistpll	16(%esp)
	fldcw	(%esp)
	jb	.LBB8_8
	movzbl	%bl, %ecx
	movl	16(%esp), %edi
	shll	$31, %ecx
	xorl	20(%esp), %ecx
.LBB8_8:
	ucomisd	%xmm3, %xmm0
	cmoval	%esi, %edi
	cmoval	%esi, %ecx
	addl	%edi, %eax
	adcl	%ecx, %edx
	addl	$28, %esp
	.cfi_def_cfa_offset 20
	popl	%esi
	.cfi_def_cfa_offset 16
	popl	%edi
	.cfi_def_cfa_offset 12
	popl	%ebx
	.cfi_def_cfa_offset 8
	popl	%ebp
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end8:
	.size	cc_many_args, .Lfunc_end8-cc_many_args
	.cfi_endproc

	.section	.text.cc_mixed_16b,"ax",@progbits
	.globl	cc_mixed_16b
	.prefalign	4, .Lfunc_end9, nop
	.type	cc_mixed_16b,@function
cc_mixed_16b:
	.cfi_startproc
	movl	8(%esp), %ecx
	movl	12(%esp), %edx
	movl	4(%esp), %eax
	movsd	16(%esp), %xmm0
	addl	$1, %ecx
	adcl	$0, %edx
	movl	%ecx, (%eax)
	movl	%edx, 4(%eax)
	movsd	%xmm0, 8(%eax)
	retl	$4
.Lfunc_end9:
	.size	cc_mixed_16b, .Lfunc_end9-cc_mixed_16b
	.cfi_endproc

	.section	.text.cc_narrow_int,"ax",@progbits
	.globl	cc_narrow_int
	.prefalign	4, .Lfunc_end10, nop
	.type	cc_narrow_int,@function
cc_narrow_int:
	.cfi_startproc
	movzbl	8(%esp), %eax
	addb	4(%esp), %al
	addb	12(%esp), %al
	addb	16(%esp), %al
	retl
.Lfunc_end10:
	.size	cc_narrow_int, .Lfunc_end10-cc_narrow_int
	.cfi_endproc

	.section	.text.cc_overaligned_16b,"ax",@progbits
	.globl	cc_overaligned_16b
	.prefalign	4, .Lfunc_end11, nop
	.type	cc_overaligned_16b,@function
cc_overaligned_16b:
	.cfi_startproc
	movl	8(%esp), %eax
	movl	12(%esp), %edx
	addl	4(%esp), %eax
	adcl	$0, %edx
	addl	16(%esp), %eax
	adcl	20(%esp), %edx
	retl
.Lfunc_end11:
	.size	cc_overaligned_16b, .Lfunc_end11-cc_overaligned_16b
	.cfi_endproc

	.section	.text.cc_rust_call,"ax",@progbits
	.globl	cc_rust_call
	.prefalign	4, .Lfunc_end12, nop
	.type	cc_rust_call,@function
cc_rust_call:
	.cfi_startproc
	movl	8(%esp), %eax
	xorl	%edx, %edx
	addl	4(%esp), %eax
	setb	%dl
	addl	12(%esp), %eax
	adcl	16(%esp), %edx
	retl
.Lfunc_end12:
	.size	cc_rust_call, .Lfunc_end12-cc_rust_call
	.cfi_endproc

	.section	.text.cc_rust_f32,"ax",@progbits
	.globl	cc_rust_f32
	.prefalign	4, .Lfunc_end13, nop
	.type	cc_rust_f32,@function
cc_rust_f32:
	.cfi_startproc
	movss	4(%esp), %xmm0
	addss	8(%esp), %xmm0
	retl
.Lfunc_end13:
	.size	cc_rust_f32, .Lfunc_end13-cc_rust_f32
	.cfi_endproc

	.section	.text.cc_rust_pair,"ax",@progbits
	.globl	cc_rust_pair
	.prefalign	4, .Lfunc_end14, nop
	.type	cc_rust_pair,@function
cc_rust_pair:
	.cfi_startproc
	pushl	%edi
	.cfi_def_cfa_offset 8
	pushl	%esi
	.cfi_def_cfa_offset 12
	.cfi_offset %esi, -12
	.cfi_offset %edi, -8
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
	.cfi_def_cfa_offset 8
	popl	%edi
	.cfi_def_cfa_offset 4
	retl	$4
.Lfunc_end14:
	.size	cc_rust_pair, .Lfunc_end14-cc_rust_pair
	.cfi_endproc

	.section	.text.cc_rust_slice,"ax",@progbits
	.globl	cc_rust_slice
	.prefalign	4, .Lfunc_end15, nop
	.type	cc_rust_slice,@function
cc_rust_slice:
	.cfi_startproc
	movl	8(%esp), %eax
	retl
.Lfunc_end15:
	.size	cc_rust_slice, .Lfunc_end15-cc_rust_slice
	.cfi_endproc

	.section	.text.cc_rust_triple,"ax",@progbits
	.globl	cc_rust_triple
	.prefalign	4, .Lfunc_end16, nop
	.type	cc_rust_triple,@function
cc_rust_triple:
	.cfi_startproc
	pushl	%esi
	.cfi_def_cfa_offset 8
	.cfi_offset %esi, -8
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
	.cfi_def_cfa_offset 4
	retl	$4
.Lfunc_end16:
	.size	cc_rust_triple, .Lfunc_end16-cc_rust_triple
	.cfi_endproc

	.section	.text.cc_struct_16b,"ax",@progbits
	.globl	cc_struct_16b
	.prefalign	4, .Lfunc_end17, nop
	.type	cc_struct_16b,@function
cc_struct_16b:
	.cfi_startproc
	movdqu	8(%esp), %xmm0
	movl	4(%esp), %eax
	pshufd	$78, %xmm0, %xmm0
	movdqu	%xmm0, (%eax)
	retl	$4
.Lfunc_end17:
	.size	cc_struct_16b, .Lfunc_end17-cc_struct_16b
	.cfi_endproc

	.section	.text.cc_struct_24b,"ax",@progbits
	.globl	cc_struct_24b
	.prefalign	4, .Lfunc_end18, nop
	.type	cc_struct_24b,@function
cc_struct_24b:
	.cfi_startproc
	movdqu	16(%esp), %xmm0
	movl	4(%esp), %eax
	movl	8(%esp), %ecx
	movl	12(%esp), %edx
	pshufd	$78, %xmm0, %xmm0
	movdqu	%xmm0, (%eax)
	movl	%ecx, 16(%eax)
	movl	%edx, 20(%eax)
	retl	$4
.Lfunc_end18:
	.size	cc_struct_24b, .Lfunc_end18-cc_struct_24b
	.cfi_endproc

	.section	.text.cc_struct_8b,"ax",@progbits
	.globl	cc_struct_8b
	.prefalign	4, .Lfunc_end19, nop
	.type	cc_struct_8b,@function
cc_struct_8b:
	.cfi_startproc
	movsd	8(%esp), %xmm0
	movl	4(%esp), %eax
	shufps	$225, %xmm0, %xmm0
	movlps	%xmm0, (%eax)
	retl	$4
.Lfunc_end19:
	.size	cc_struct_8b, .Lfunc_end19-cc_struct_8b
	.cfi_endproc

	.section	.text.cc_track_caller,"ax",@progbits
	.globl	cc_track_caller
	.prefalign	4, .Lfunc_end20, nop
	.type	cc_track_caller,@function
cc_track_caller:
	.cfi_startproc
	movl	8(%esp), %eax
	retl
.Lfunc_end20:
	.size	cc_track_caller, .Lfunc_end20-cc_track_caller
	.cfi_endproc

	.section	.text.cc_u128,"ax",@progbits
	.globl	cc_u128
	.prefalign	4, .Lfunc_end21, nop
	.type	cc_u128,@function
cc_u128:
	.cfi_startproc
	pushl	%edi
	.cfi_def_cfa_offset 8
	pushl	%esi
	.cfi_def_cfa_offset 12
	pushl	%eax
	.cfi_def_cfa_offset 16
	.cfi_offset %esi, -12
	.cfi_offset %edi, -8
	movl	32(%esp), %esi
	movl	36(%esp), %edi
	movl	40(%esp), %edx
	movl	44(%esp), %ecx
	movl	16(%esp), %eax
	addl	20(%esp), %esi
	adcl	$0, %edi
	adcl	$0, %edx
	adcl	$0, %ecx
	movl	%edx, 8(%eax)
	movl	%edi, 4(%eax)
	movl	%esi, (%eax)
	movl	%ecx, 12(%eax)
	addl	$4, %esp
	.cfi_def_cfa_offset 12
	popl	%esi
	.cfi_def_cfa_offset 8
	popl	%edi
	.cfi_def_cfa_offset 4
	retl	$4
.Lfunc_end21:
	.size	cc_u128, .Lfunc_end21-cc_u128
	.cfi_endproc

	.section	.text.cc_variadic_caller,"ax",@progbits
	.globl	cc_variadic_caller
	.prefalign	4, .Lfunc_end22, nop
	.type	cc_variadic_caller,@function
cc_variadic_caller:
	.cfi_startproc
	subl	$28, %esp
	.cfi_def_cfa_offset 32
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
	.cfi_def_cfa_offset 4
	retl
.Lfunc_end22:
	.size	cc_variadic_caller, .Lfunc_end22-cc_variadic_caller
	.cfi_endproc

	.section	.text.cc_vec128_c,"ax",@progbits
	.globl	cc_vec128_c
	.prefalign	4, .Lfunc_end23, nop
	.type	cc_vec128_c,@function
cc_vec128_c:
	.cfi_startproc
	retl
.Lfunc_end23:
	.size	cc_vec128_c, .Lfunc_end23-cc_vec128_c
	.cfi_endproc

	.section	.text.cc_vec128_rust,"ax",@progbits
	.globl	cc_vec128_rust
	.prefalign	4, .Lfunc_end24, nop
	.type	cc_vec128_rust,@function
cc_vec128_rust:
	.cfi_startproc
	movl	8(%esp), %ecx
	movl	4(%esp), %eax
	movaps	(%ecx), %xmm0
	movaps	%xmm0, (%eax)
	retl	$4
.Lfunc_end24:
	.size	cc_vec128_rust, .Lfunc_end24-cc_vec128_rust
	.cfi_endproc

	.section	".text.cc_vectorcall@@40","ax",@progbits
	.globl	"cc_vectorcall@@40"
	.prefalign	4, .Lfunc_end25, nop
	.type	"cc_vectorcall@@40",@function
"cc_vectorcall@@40":
	.cfi_startproc
	movl	4(%esp), %eax
	movsd	8(%esp), %xmm0
	movsd	16(%esp), %xmm1
	movsd	%xmm1, 8(%eax)
	movsd	%xmm0, (%eax)
	retl	$20
.Lfunc_end25:
	.size	"cc_vectorcall@@40", .Lfunc_end25-"cc_vectorcall@@40"
	.cfi_endproc

	.section	.text.cc_x86_fastcall,"ax",@progbits
	.globl	cc_x86_fastcall
	.prefalign	4, .Lfunc_end26, nop
	.type	cc_x86_fastcall,@function
cc_x86_fastcall:
	.cfi_startproc
	leal	(%ecx,%edx), %eax
	addl	4(%esp), %eax
	retl	$4
.Lfunc_end26:
	.size	cc_x86_fastcall, .Lfunc_end26-cc_x86_fastcall
	.cfi_endproc

	.section	.text.cc_x86_stdcall,"ax",@progbits
	.globl	cc_x86_stdcall
	.prefalign	4, .Lfunc_end27, nop
	.type	cc_x86_stdcall,@function
cc_x86_stdcall:
	.cfi_startproc
	movl	8(%esp), %eax
	addl	4(%esp), %eax
	addl	12(%esp), %eax
	retl	$12
.Lfunc_end27:
	.size	cc_x86_stdcall, .Lfunc_end27-cc_x86_stdcall
	.cfi_endproc

	.section	.text.cc_x86_thiscall,"ax",@progbits
	.globl	cc_x86_thiscall
	.prefalign	4, .Lfunc_end28, nop
	.type	cc_x86_thiscall,@function
cc_x86_thiscall:
	.cfi_startproc
	movl	%ecx, %eax
	addl	4(%esp), %eax
	addl	8(%esp), %eax
	retl	$8
.Lfunc_end28:
	.size	cc_x86_thiscall, .Lfunc_end28-cc_x86_thiscall
	.cfi_endproc

	.globl	cc_zst_and_transparent
	.type	cc_zst_and_transparent,@function
cc_zst_and_transparent = cc_c_nounwind
	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
