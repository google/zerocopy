	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.file	"specimen.c"
	.def	unwind_frame;
	.scl	2;
	.type	32;
	.endef
	.text
	.globl	unwind_frame                    # -- Begin function unwind_frame
	.p2align	4
unwind_frame:                           # @unwind_frame
.seh_proc unwind_frame
# %bb.0:
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$80, %rsp
	.seh_stackalloc 80
	leaq	80(%rsp), %rbp
	.seh_setframe %rbp, 80
	.seh_endprologue
	movq	%rcx, -32(%rbp)
	leaq	1(%rcx), %rax
	movq	%rax, -48(%rbp)
	leaq	2(%rcx), %rax
	movq	%rax, -16(%rbp)
	leaq	3(%rcx), %rax
	movq	%rax, -40(%rbp)
	callq	helper
	movq	-32(%rbp), %rcx
	addq	%rcx, %rax
	movq	-48(%rbp), %rcx
	movq	-16(%rbp), %rdx
	addq	%rcx, %rdx
	addq	%rdx, %rax
	movq	-40(%rbp), %rcx
	addq	%rcx, %rax
	.seh_startepilogue
	addq	$80, %rsp
	popq	%rbp
	.seh_endepilogue
	retq
	.seh_endproc
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
