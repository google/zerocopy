	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.file	"abi_witness.c"
	.def	abi_add;
	.scl	2;
	.type	32;
	.endef
	.text
	.globl	abi_add                         # -- Begin function abi_add
	.p2align	4
abi_add:                                # @abi_add
# %bb.0:
	leaq	(%rcx,%rdx), %rax
	retq
                                        # -- End function
	.def	abi_pair;
	.scl	2;
	.type	32;
	.endef
	.globl	abi_pair                        # -- Begin function abi_pair
	.p2align	4
abi_pair:                               # @abi_pair
# %bb.0:
	movq	%rcx, %rax
	movdqu	(%rdx), %xmm0
	pshufd	$78, %xmm0, %xmm0               # xmm0 = xmm0[2,3,0,1]
	movdqu	%xmm0, (%rcx)
	retq
                                        # -- End function
	.def	abi_triple;
	.scl	2;
	.type	32;
	.endef
	.globl	abi_triple                      # -- Begin function abi_triple
	.p2align	4
abi_triple:                             # @abi_triple
# %bb.0:
	movq	%rcx, %rax
	movdqu	8(%rdx), %xmm0
	pshufd	$78, %xmm0, %xmm0               # xmm0 = xmm0[2,3,0,1]
	movdqu	%xmm0, (%rcx)
	movq	(%rdx), %rcx
	movq	%rcx, 16(%rax)
	retq
                                        # -- End function
	.section	.debug$S,"dr"
	.p2align	2, 0x0
	.long	4                               # Debug section magic
	.long	241
	.long	.Ltmp1-.Ltmp0                   # Subsection size
.Ltmp0:
	.short	.Ltmp3-.Ltmp2                   # Record length
.Ltmp2:
	.short	4353                            # Record kind: S_OBJNAME
	.long	0                               # Signature
	.byte	0                               # Object name
	.p2align	2, 0x0
.Ltmp3:
	.short	.Ltmp5-.Ltmp4                   # Record length
.Ltmp4:
	.short	4412                            # Record kind: S_COMPILE3
	.long	0                               # Flags and language
	.short	208                             # CPUType
	.short	21                              # Frontend version
	.short	0
	.short	0
	.short	0
	.short	65535                           # Backend version
	.short	0
	.short	0
	.short	0
	.asciz	"Apple clang version 21.0.0 (clang-2100.3.34.2)" # Null-terminated compiler version string
	.p2align	2, 0x0
.Ltmp5:
.Ltmp1:
	.p2align	2, 0x0
	.addrsig
