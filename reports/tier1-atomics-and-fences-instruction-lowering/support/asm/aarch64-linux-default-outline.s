	.file	"atomic_probe.15283d9b12ef6327-cgu.0"
	.section	.text._RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,"ax",@progbits
	.globl	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.p2align	2
	.type	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,@function
_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind:
	.cfi_startproc
.LBB0_1:
	b	.LBB0_1
.Lfunc_end0:
	.size	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind, .Lfunc_end0-_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.cfi_endproc

	.section	.text.atomic_and_128_acqrel,"ax",@progbits
	.globl	atomic_and_128_acqrel
	.p2align	2
	.type	atomic_and_128_acqrel,@function
atomic_and_128_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB1_1:
	ldaxp	x0, x1, [x8]
	and	x9, x1, x3
	and	x10, x0, x2
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB1_1
	ret
.Lfunc_end1:
	.size	atomic_and_128_acqrel, .Lfunc_end1-atomic_and_128_acqrel
	.cfi_endproc

	.section	.text.atomic_and_128_acquire,"ax",@progbits
	.globl	atomic_and_128_acquire
	.p2align	2
	.type	atomic_and_128_acquire,@function
atomic_and_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB2_1:
	ldaxp	x0, x1, [x8]
	and	x9, x1, x3
	and	x10, x0, x2
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB2_1
	ret
.Lfunc_end2:
	.size	atomic_and_128_acquire, .Lfunc_end2-atomic_and_128_acquire
	.cfi_endproc

	.section	.text.atomic_and_128_relaxed,"ax",@progbits
	.globl	atomic_and_128_relaxed
	.p2align	2
	.type	atomic_and_128_relaxed,@function
atomic_and_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB3_1:
	ldxp	x0, x1, [x8]
	and	x9, x1, x3
	and	x10, x0, x2
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB3_1
	ret
.Lfunc_end3:
	.size	atomic_and_128_relaxed, .Lfunc_end3-atomic_and_128_relaxed
	.cfi_endproc

	.section	.text.atomic_and_128_release,"ax",@progbits
	.globl	atomic_and_128_release
	.p2align	2
	.type	atomic_and_128_release,@function
atomic_and_128_release:
	.cfi_startproc
	mov	x8, x0
.LBB4_1:
	ldxp	x0, x1, [x8]
	and	x9, x1, x3
	and	x10, x0, x2
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB4_1
	ret
.Lfunc_end4:
	.size	atomic_and_128_release, .Lfunc_end4-atomic_and_128_release
	.cfi_endproc

	.section	.text.atomic_and_128_seqcst,"ax",@progbits
	.globl	atomic_and_128_seqcst
	.p2align	2
	.type	atomic_and_128_seqcst,@function
atomic_and_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB5_1:
	ldaxp	x0, x1, [x8]
	and	x9, x1, x3
	and	x10, x0, x2
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB5_1
	ret
.Lfunc_end5:
	.size	atomic_and_128_seqcst, .Lfunc_end5-atomic_and_128_seqcst
	.cfi_endproc

	.section	.text.atomic_and_16_acqrel,"ax",@progbits
	.globl	atomic_and_16_acqrel
	.p2align	2
	.type	atomic_and_16_acqrel,@function
atomic_and_16_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end6:
	.size	atomic_and_16_acqrel, .Lfunc_end6-atomic_and_16_acqrel
	.cfi_endproc

	.section	.text.atomic_and_16_acquire,"ax",@progbits
	.globl	atomic_and_16_acquire
	.p2align	2
	.type	atomic_and_16_acquire,@function
atomic_and_16_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr2_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end7:
	.size	atomic_and_16_acquire, .Lfunc_end7-atomic_and_16_acquire
	.cfi_endproc

	.section	.text.atomic_and_16_relaxed,"ax",@progbits
	.globl	atomic_and_16_relaxed
	.p2align	2
	.type	atomic_and_16_relaxed,@function
atomic_and_16_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr2_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end8:
	.size	atomic_and_16_relaxed, .Lfunc_end8-atomic_and_16_relaxed
	.cfi_endproc

	.section	.text.atomic_and_16_release,"ax",@progbits
	.globl	atomic_and_16_release
	.p2align	2
	.type	atomic_and_16_release,@function
atomic_and_16_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr2_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end9:
	.size	atomic_and_16_release, .Lfunc_end9-atomic_and_16_release
	.cfi_endproc

	.section	.text.atomic_and_16_seqcst,"ax",@progbits
	.globl	atomic_and_16_seqcst
	.p2align	2
	.type	atomic_and_16_seqcst,@function
atomic_and_16_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end10:
	.size	atomic_and_16_seqcst, .Lfunc_end10-atomic_and_16_seqcst
	.cfi_endproc

	.section	.text.atomic_and_32_acqrel,"ax",@progbits
	.globl	atomic_and_32_acqrel
	.p2align	2
	.type	atomic_and_32_acqrel,@function
atomic_and_32_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end11:
	.size	atomic_and_32_acqrel, .Lfunc_end11-atomic_and_32_acqrel
	.cfi_endproc

	.section	.text.atomic_and_32_acquire,"ax",@progbits
	.globl	atomic_and_32_acquire
	.p2align	2
	.type	atomic_and_32_acquire,@function
atomic_and_32_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr4_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end12:
	.size	atomic_and_32_acquire, .Lfunc_end12-atomic_and_32_acquire
	.cfi_endproc

	.section	.text.atomic_and_32_relaxed,"ax",@progbits
	.globl	atomic_and_32_relaxed
	.p2align	2
	.type	atomic_and_32_relaxed,@function
atomic_and_32_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr4_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end13:
	.size	atomic_and_32_relaxed, .Lfunc_end13-atomic_and_32_relaxed
	.cfi_endproc

	.section	.text.atomic_and_32_release,"ax",@progbits
	.globl	atomic_and_32_release
	.p2align	2
	.type	atomic_and_32_release,@function
atomic_and_32_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr4_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end14:
	.size	atomic_and_32_release, .Lfunc_end14-atomic_and_32_release
	.cfi_endproc

	.section	.text.atomic_and_32_seqcst,"ax",@progbits
	.globl	atomic_and_32_seqcst
	.p2align	2
	.type	atomic_and_32_seqcst,@function
atomic_and_32_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end15:
	.size	atomic_and_32_seqcst, .Lfunc_end15-atomic_and_32_seqcst
	.cfi_endproc

	.section	.text.atomic_and_64_acqrel,"ax",@progbits
	.globl	atomic_and_64_acqrel
	.p2align	2
	.type	atomic_and_64_acqrel,@function
atomic_and_64_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	x0, x1
	mov	x1, x8
	bl	__aarch64_ldclr8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end16:
	.size	atomic_and_64_acqrel, .Lfunc_end16-atomic_and_64_acqrel
	.cfi_endproc

	.section	.text.atomic_and_64_acquire,"ax",@progbits
	.globl	atomic_and_64_acquire
	.p2align	2
	.type	atomic_and_64_acquire,@function
atomic_and_64_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	x0, x1
	mov	x1, x8
	bl	__aarch64_ldclr8_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end17:
	.size	atomic_and_64_acquire, .Lfunc_end17-atomic_and_64_acquire
	.cfi_endproc

	.section	.text.atomic_and_64_relaxed,"ax",@progbits
	.globl	atomic_and_64_relaxed
	.p2align	2
	.type	atomic_and_64_relaxed,@function
atomic_and_64_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	x0, x1
	mov	x1, x8
	bl	__aarch64_ldclr8_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end18:
	.size	atomic_and_64_relaxed, .Lfunc_end18-atomic_and_64_relaxed
	.cfi_endproc

	.section	.text.atomic_and_64_release,"ax",@progbits
	.globl	atomic_and_64_release
	.p2align	2
	.type	atomic_and_64_release,@function
atomic_and_64_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	x0, x1
	mov	x1, x8
	bl	__aarch64_ldclr8_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end19:
	.size	atomic_and_64_release, .Lfunc_end19-atomic_and_64_release
	.cfi_endproc

	.section	.text.atomic_and_64_seqcst,"ax",@progbits
	.globl	atomic_and_64_seqcst
	.p2align	2
	.type	atomic_and_64_seqcst,@function
atomic_and_64_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	x0, x1
	mov	x1, x8
	bl	__aarch64_ldclr8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end20:
	.size	atomic_and_64_seqcst, .Lfunc_end20-atomic_and_64_seqcst
	.cfi_endproc

	.section	.text.atomic_and_8_acqrel,"ax",@progbits
	.globl	atomic_and_8_acqrel
	.p2align	2
	.type	atomic_and_8_acqrel,@function
atomic_and_8_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end21:
	.size	atomic_and_8_acqrel, .Lfunc_end21-atomic_and_8_acqrel
	.cfi_endproc

	.section	.text.atomic_and_8_acquire,"ax",@progbits
	.globl	atomic_and_8_acquire
	.p2align	2
	.type	atomic_and_8_acquire,@function
atomic_and_8_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr1_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end22:
	.size	atomic_and_8_acquire, .Lfunc_end22-atomic_and_8_acquire
	.cfi_endproc

	.section	.text.atomic_and_8_relaxed,"ax",@progbits
	.globl	atomic_and_8_relaxed
	.p2align	2
	.type	atomic_and_8_relaxed,@function
atomic_and_8_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr1_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end23:
	.size	atomic_and_8_relaxed, .Lfunc_end23-atomic_and_8_relaxed
	.cfi_endproc

	.section	.text.atomic_and_8_release,"ax",@progbits
	.globl	atomic_and_8_release
	.p2align	2
	.type	atomic_and_8_release,@function
atomic_and_8_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr1_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end24:
	.size	atomic_and_8_release, .Lfunc_end24-atomic_and_8_release
	.cfi_endproc

	.section	.text.atomic_and_8_seqcst,"ax",@progbits
	.globl	atomic_and_8_seqcst
	.p2align	2
	.type	atomic_and_8_seqcst,@function
atomic_and_8_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mvn	w0, w1
	mov	x1, x8
	bl	__aarch64_ldclr1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end25:
	.size	atomic_and_8_seqcst, .Lfunc_end25-atomic_and_8_seqcst
	.cfi_endproc

	.section	.text.atomic_compiler_fence_acqrel,"ax",@progbits
	.globl	atomic_compiler_fence_acqrel
	.p2align	2
	.type	atomic_compiler_fence_acqrel,@function
atomic_compiler_fence_acqrel:
	.cfi_startproc
	//MEMBARRIER
	ret
.Lfunc_end26:
	.size	atomic_compiler_fence_acqrel, .Lfunc_end26-atomic_compiler_fence_acqrel
	.cfi_endproc

	.section	.text.atomic_compiler_fence_acquire,"ax",@progbits
	.globl	atomic_compiler_fence_acquire
	.p2align	2
	.type	atomic_compiler_fence_acquire,@function
atomic_compiler_fence_acquire:
	.cfi_startproc
	//MEMBARRIER
	ret
.Lfunc_end27:
	.size	atomic_compiler_fence_acquire, .Lfunc_end27-atomic_compiler_fence_acquire
	.cfi_endproc

	.section	.text.atomic_compiler_fence_release,"ax",@progbits
	.globl	atomic_compiler_fence_release
	.p2align	2
	.type	atomic_compiler_fence_release,@function
atomic_compiler_fence_release:
	.cfi_startproc
	//MEMBARRIER
	ret
.Lfunc_end28:
	.size	atomic_compiler_fence_release, .Lfunc_end28-atomic_compiler_fence_release
	.cfi_endproc

	.section	.text.atomic_compiler_fence_seqcst,"ax",@progbits
	.globl	atomic_compiler_fence_seqcst
	.p2align	2
	.type	atomic_compiler_fence_seqcst,@function
atomic_compiler_fence_seqcst:
	.cfi_startproc
	//MEMBARRIER
	ret
.Lfunc_end29:
	.size	atomic_compiler_fence_seqcst, .Lfunc_end29-atomic_compiler_fence_seqcst
	.cfi_endproc

	.section	.text.atomic_fence_acqrel,"ax",@progbits
	.globl	atomic_fence_acqrel
	.p2align	2
	.type	atomic_fence_acqrel,@function
atomic_fence_acqrel:
	.cfi_startproc
	dmb	ish
	ret
.Lfunc_end30:
	.size	atomic_fence_acqrel, .Lfunc_end30-atomic_fence_acqrel
	.cfi_endproc

	.section	.text.atomic_fence_acquire,"ax",@progbits
	.globl	atomic_fence_acquire
	.p2align	2
	.type	atomic_fence_acquire,@function
atomic_fence_acquire:
	.cfi_startproc
	dmb	ishld
	ret
.Lfunc_end31:
	.size	atomic_fence_acquire, .Lfunc_end31-atomic_fence_acquire
	.cfi_endproc

	.section	.text.atomic_fence_release,"ax",@progbits
	.globl	atomic_fence_release
	.p2align	2
	.type	atomic_fence_release,@function
atomic_fence_release:
	.cfi_startproc
	dmb	ish
	ret
.Lfunc_end32:
	.size	atomic_fence_release, .Lfunc_end32-atomic_fence_release
	.cfi_endproc

	.section	.text.atomic_fence_seqcst,"ax",@progbits
	.globl	atomic_fence_seqcst
	.p2align	2
	.type	atomic_fence_seqcst,@function
atomic_fence_seqcst:
	.cfi_startproc
	dmb	ish
	ret
.Lfunc_end33:
	.size	atomic_fence_seqcst, .Lfunc_end33-atomic_fence_seqcst
	.cfi_endproc

	.section	.text.atomic_load_128_acquire,"ax",@progbits
	.globl	atomic_load_128_acquire
	.p2align	2
	.type	atomic_load_128_acquire,@function
atomic_load_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB34_1:
	ldaxp	x0, x1, [x8]
	stxp	w9, x0, x1, [x8]
	cbnz	w9, .LBB34_1
	ret
.Lfunc_end34:
	.size	atomic_load_128_acquire, .Lfunc_end34-atomic_load_128_acquire
	.cfi_endproc

	.section	.text.atomic_load_128_relaxed,"ax",@progbits
	.globl	atomic_load_128_relaxed
	.p2align	2
	.type	atomic_load_128_relaxed,@function
atomic_load_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB35_1:
	ldxp	x0, x1, [x8]
	stxp	w9, x0, x1, [x8]
	cbnz	w9, .LBB35_1
	ret
.Lfunc_end35:
	.size	atomic_load_128_relaxed, .Lfunc_end35-atomic_load_128_relaxed
	.cfi_endproc

	.section	.text.atomic_load_128_seqcst,"ax",@progbits
	.globl	atomic_load_128_seqcst
	.p2align	2
	.type	atomic_load_128_seqcst,@function
atomic_load_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB36_1:
	ldaxp	x0, x1, [x8]
	stlxp	w9, x0, x1, [x8]
	cbnz	w9, .LBB36_1
	ret
.Lfunc_end36:
	.size	atomic_load_128_seqcst, .Lfunc_end36-atomic_load_128_seqcst
	.cfi_endproc

	.section	.text.atomic_load_16_acquire,"ax",@progbits
	.globl	atomic_load_16_acquire
	.p2align	2
	.type	atomic_load_16_acquire,@function
atomic_load_16_acquire:
	.cfi_startproc
	ldarh	w0, [x0]
	ret
.Lfunc_end37:
	.size	atomic_load_16_acquire, .Lfunc_end37-atomic_load_16_acquire
	.cfi_endproc

	.section	.text.atomic_load_16_relaxed,"ax",@progbits
	.globl	atomic_load_16_relaxed
	.p2align	2
	.type	atomic_load_16_relaxed,@function
atomic_load_16_relaxed:
	.cfi_startproc
	ldrh	w0, [x0]
	ret
.Lfunc_end38:
	.size	atomic_load_16_relaxed, .Lfunc_end38-atomic_load_16_relaxed
	.cfi_endproc

	.section	.text.atomic_load_16_seqcst,"ax",@progbits
	.globl	atomic_load_16_seqcst
	.p2align	2
	.type	atomic_load_16_seqcst,@function
atomic_load_16_seqcst:
	.cfi_startproc
	ldarh	w0, [x0]
	ret
.Lfunc_end39:
	.size	atomic_load_16_seqcst, .Lfunc_end39-atomic_load_16_seqcst
	.cfi_endproc

	.section	.text.atomic_load_32_acquire,"ax",@progbits
	.globl	atomic_load_32_acquire
	.p2align	2
	.type	atomic_load_32_acquire,@function
atomic_load_32_acquire:
	.cfi_startproc
	ldar	w0, [x0]
	ret
.Lfunc_end40:
	.size	atomic_load_32_acquire, .Lfunc_end40-atomic_load_32_acquire
	.cfi_endproc

	.section	.text.atomic_load_32_relaxed,"ax",@progbits
	.globl	atomic_load_32_relaxed
	.p2align	2
	.type	atomic_load_32_relaxed,@function
atomic_load_32_relaxed:
	.cfi_startproc
	ldr	w0, [x0]
	ret
.Lfunc_end41:
	.size	atomic_load_32_relaxed, .Lfunc_end41-atomic_load_32_relaxed
	.cfi_endproc

	.section	.text.atomic_load_32_seqcst,"ax",@progbits
	.globl	atomic_load_32_seqcst
	.p2align	2
	.type	atomic_load_32_seqcst,@function
atomic_load_32_seqcst:
	.cfi_startproc
	ldar	w0, [x0]
	ret
.Lfunc_end42:
	.size	atomic_load_32_seqcst, .Lfunc_end42-atomic_load_32_seqcst
	.cfi_endproc

	.section	.text.atomic_load_64_acquire,"ax",@progbits
	.globl	atomic_load_64_acquire
	.p2align	2
	.type	atomic_load_64_acquire,@function
atomic_load_64_acquire:
	.cfi_startproc
	ldar	x0, [x0]
	ret
.Lfunc_end43:
	.size	atomic_load_64_acquire, .Lfunc_end43-atomic_load_64_acquire
	.cfi_endproc

	.section	.text.atomic_load_64_relaxed,"ax",@progbits
	.globl	atomic_load_64_relaxed
	.p2align	2
	.type	atomic_load_64_relaxed,@function
atomic_load_64_relaxed:
	.cfi_startproc
	ldr	x0, [x0]
	ret
.Lfunc_end44:
	.size	atomic_load_64_relaxed, .Lfunc_end44-atomic_load_64_relaxed
	.cfi_endproc

	.section	.text.atomic_load_64_seqcst,"ax",@progbits
	.globl	atomic_load_64_seqcst
	.p2align	2
	.type	atomic_load_64_seqcst,@function
atomic_load_64_seqcst:
	.cfi_startproc
	ldar	x0, [x0]
	ret
.Lfunc_end45:
	.size	atomic_load_64_seqcst, .Lfunc_end45-atomic_load_64_seqcst
	.cfi_endproc

	.section	.text.atomic_load_8_acquire,"ax",@progbits
	.globl	atomic_load_8_acquire
	.p2align	2
	.type	atomic_load_8_acquire,@function
atomic_load_8_acquire:
	.cfi_startproc
	ldarb	w0, [x0]
	ret
.Lfunc_end46:
	.size	atomic_load_8_acquire, .Lfunc_end46-atomic_load_8_acquire
	.cfi_endproc

	.section	.text.atomic_load_8_relaxed,"ax",@progbits
	.globl	atomic_load_8_relaxed
	.p2align	2
	.type	atomic_load_8_relaxed,@function
atomic_load_8_relaxed:
	.cfi_startproc
	ldrb	w0, [x0]
	ret
.Lfunc_end47:
	.size	atomic_load_8_relaxed, .Lfunc_end47-atomic_load_8_relaxed
	.cfi_endproc

	.section	.text.atomic_load_8_seqcst,"ax",@progbits
	.globl	atomic_load_8_seqcst
	.p2align	2
	.type	atomic_load_8_seqcst,@function
atomic_load_8_seqcst:
	.cfi_startproc
	ldarb	w0, [x0]
	ret
.Lfunc_end48:
	.size	atomic_load_8_seqcst, .Lfunc_end48-atomic_load_8_seqcst
	.cfi_endproc

	.section	.text.atomic_max_128_acqrel,"ax",@progbits
	.globl	atomic_max_128_acqrel
	.p2align	2
	.type	atomic_max_128_acqrel,@function
atomic_max_128_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB49_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, lt
	csel	x10, x0, x2, lt
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB49_1
	ret
.Lfunc_end49:
	.size	atomic_max_128_acqrel, .Lfunc_end49-atomic_max_128_acqrel
	.cfi_endproc

	.section	.text.atomic_max_128_acquire,"ax",@progbits
	.globl	atomic_max_128_acquire
	.p2align	2
	.type	atomic_max_128_acquire,@function
atomic_max_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB50_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, lt
	csel	x10, x0, x2, lt
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB50_1
	ret
.Lfunc_end50:
	.size	atomic_max_128_acquire, .Lfunc_end50-atomic_max_128_acquire
	.cfi_endproc

	.section	.text.atomic_max_128_relaxed,"ax",@progbits
	.globl	atomic_max_128_relaxed
	.p2align	2
	.type	atomic_max_128_relaxed,@function
atomic_max_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB51_1:
	ldxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, lt
	csel	x10, x0, x2, lt
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB51_1
	ret
.Lfunc_end51:
	.size	atomic_max_128_relaxed, .Lfunc_end51-atomic_max_128_relaxed
	.cfi_endproc

	.section	.text.atomic_max_128_release,"ax",@progbits
	.globl	atomic_max_128_release
	.p2align	2
	.type	atomic_max_128_release,@function
atomic_max_128_release:
	.cfi_startproc
	mov	x8, x0
.LBB52_1:
	ldxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, lt
	csel	x10, x0, x2, lt
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB52_1
	ret
.Lfunc_end52:
	.size	atomic_max_128_release, .Lfunc_end52-atomic_max_128_release
	.cfi_endproc

	.section	.text.atomic_max_128_seqcst,"ax",@progbits
	.globl	atomic_max_128_seqcst
	.p2align	2
	.type	atomic_max_128_seqcst,@function
atomic_max_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB53_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, lt
	csel	x10, x0, x2, lt
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB53_1
	ret
.Lfunc_end53:
	.size	atomic_max_128_seqcst, .Lfunc_end53-atomic_max_128_seqcst
	.cfi_endproc

	.section	.text.atomic_max_16_acqrel,"ax",@progbits
	.globl	atomic_max_16_acqrel
	.p2align	2
	.type	atomic_max_16_acqrel,@function
atomic_max_16_acqrel:
	.cfi_startproc
.LBB54_1:
	ldaxrh	w9, [x0]
	sxth	w8, w9
	cmp	w8, w1, sxth
	csel	w9, w9, w1, gt
	stlxrh	w10, w9, [x0]
	cbnz	w10, .LBB54_1
	mov	w0, w8
	ret
.Lfunc_end54:
	.size	atomic_max_16_acqrel, .Lfunc_end54-atomic_max_16_acqrel
	.cfi_endproc

	.section	.text.atomic_max_16_acquire,"ax",@progbits
	.globl	atomic_max_16_acquire
	.p2align	2
	.type	atomic_max_16_acquire,@function
atomic_max_16_acquire:
	.cfi_startproc
.LBB55_1:
	ldaxrh	w9, [x0]
	sxth	w8, w9
	cmp	w8, w1, sxth
	csel	w9, w9, w1, gt
	stxrh	w10, w9, [x0]
	cbnz	w10, .LBB55_1
	mov	w0, w8
	ret
.Lfunc_end55:
	.size	atomic_max_16_acquire, .Lfunc_end55-atomic_max_16_acquire
	.cfi_endproc

	.section	.text.atomic_max_16_relaxed,"ax",@progbits
	.globl	atomic_max_16_relaxed
	.p2align	2
	.type	atomic_max_16_relaxed,@function
atomic_max_16_relaxed:
	.cfi_startproc
.LBB56_1:
	ldxrh	w9, [x0]
	sxth	w8, w9
	cmp	w8, w1, sxth
	csel	w9, w9, w1, gt
	stxrh	w10, w9, [x0]
	cbnz	w10, .LBB56_1
	mov	w0, w8
	ret
.Lfunc_end56:
	.size	atomic_max_16_relaxed, .Lfunc_end56-atomic_max_16_relaxed
	.cfi_endproc

	.section	.text.atomic_max_16_release,"ax",@progbits
	.globl	atomic_max_16_release
	.p2align	2
	.type	atomic_max_16_release,@function
atomic_max_16_release:
	.cfi_startproc
.LBB57_1:
	ldxrh	w9, [x0]
	sxth	w8, w9
	cmp	w8, w1, sxth
	csel	w9, w9, w1, gt
	stlxrh	w10, w9, [x0]
	cbnz	w10, .LBB57_1
	mov	w0, w8
	ret
.Lfunc_end57:
	.size	atomic_max_16_release, .Lfunc_end57-atomic_max_16_release
	.cfi_endproc

	.section	.text.atomic_max_16_seqcst,"ax",@progbits
	.globl	atomic_max_16_seqcst
	.p2align	2
	.type	atomic_max_16_seqcst,@function
atomic_max_16_seqcst:
	.cfi_startproc
.LBB58_1:
	ldaxrh	w9, [x0]
	sxth	w8, w9
	cmp	w8, w1, sxth
	csel	w9, w9, w1, gt
	stlxrh	w10, w9, [x0]
	cbnz	w10, .LBB58_1
	mov	w0, w8
	ret
.Lfunc_end58:
	.size	atomic_max_16_seqcst, .Lfunc_end58-atomic_max_16_seqcst
	.cfi_endproc

	.section	.text.atomic_max_32_acqrel,"ax",@progbits
	.globl	atomic_max_32_acqrel
	.p2align	2
	.type	atomic_max_32_acqrel,@function
atomic_max_32_acqrel:
	.cfi_startproc
.LBB59_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, gt
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB59_1
	mov	w0, w8
	ret
.Lfunc_end59:
	.size	atomic_max_32_acqrel, .Lfunc_end59-atomic_max_32_acqrel
	.cfi_endproc

	.section	.text.atomic_max_32_acquire,"ax",@progbits
	.globl	atomic_max_32_acquire
	.p2align	2
	.type	atomic_max_32_acquire,@function
atomic_max_32_acquire:
	.cfi_startproc
.LBB60_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, gt
	stxr	w10, w9, [x0]
	cbnz	w10, .LBB60_1
	mov	w0, w8
	ret
.Lfunc_end60:
	.size	atomic_max_32_acquire, .Lfunc_end60-atomic_max_32_acquire
	.cfi_endproc

	.section	.text.atomic_max_32_relaxed,"ax",@progbits
	.globl	atomic_max_32_relaxed
	.p2align	2
	.type	atomic_max_32_relaxed,@function
atomic_max_32_relaxed:
	.cfi_startproc
.LBB61_1:
	ldxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, gt
	stxr	w10, w9, [x0]
	cbnz	w10, .LBB61_1
	mov	w0, w8
	ret
.Lfunc_end61:
	.size	atomic_max_32_relaxed, .Lfunc_end61-atomic_max_32_relaxed
	.cfi_endproc

	.section	.text.atomic_max_32_release,"ax",@progbits
	.globl	atomic_max_32_release
	.p2align	2
	.type	atomic_max_32_release,@function
atomic_max_32_release:
	.cfi_startproc
.LBB62_1:
	ldxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, gt
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB62_1
	mov	w0, w8
	ret
.Lfunc_end62:
	.size	atomic_max_32_release, .Lfunc_end62-atomic_max_32_release
	.cfi_endproc

	.section	.text.atomic_max_32_seqcst,"ax",@progbits
	.globl	atomic_max_32_seqcst
	.p2align	2
	.type	atomic_max_32_seqcst,@function
atomic_max_32_seqcst:
	.cfi_startproc
.LBB63_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, gt
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB63_1
	mov	w0, w8
	ret
.Lfunc_end63:
	.size	atomic_max_32_seqcst, .Lfunc_end63-atomic_max_32_seqcst
	.cfi_endproc

	.section	.text.atomic_max_64_acqrel,"ax",@progbits
	.globl	atomic_max_64_acqrel
	.p2align	2
	.type	atomic_max_64_acqrel,@function
atomic_max_64_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB64_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, gt
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB64_1
	ret
.Lfunc_end64:
	.size	atomic_max_64_acqrel, .Lfunc_end64-atomic_max_64_acqrel
	.cfi_endproc

	.section	.text.atomic_max_64_acquire,"ax",@progbits
	.globl	atomic_max_64_acquire
	.p2align	2
	.type	atomic_max_64_acquire,@function
atomic_max_64_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB65_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, gt
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB65_1
	ret
.Lfunc_end65:
	.size	atomic_max_64_acquire, .Lfunc_end65-atomic_max_64_acquire
	.cfi_endproc

	.section	.text.atomic_max_64_relaxed,"ax",@progbits
	.globl	atomic_max_64_relaxed
	.p2align	2
	.type	atomic_max_64_relaxed,@function
atomic_max_64_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB66_1:
	ldxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, gt
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB66_1
	ret
.Lfunc_end66:
	.size	atomic_max_64_relaxed, .Lfunc_end66-atomic_max_64_relaxed
	.cfi_endproc

	.section	.text.atomic_max_64_release,"ax",@progbits
	.globl	atomic_max_64_release
	.p2align	2
	.type	atomic_max_64_release,@function
atomic_max_64_release:
	.cfi_startproc
	mov	x8, x0
.LBB67_1:
	ldxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, gt
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB67_1
	ret
.Lfunc_end67:
	.size	atomic_max_64_release, .Lfunc_end67-atomic_max_64_release
	.cfi_endproc

	.section	.text.atomic_max_64_seqcst,"ax",@progbits
	.globl	atomic_max_64_seqcst
	.p2align	2
	.type	atomic_max_64_seqcst,@function
atomic_max_64_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB68_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, gt
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB68_1
	ret
.Lfunc_end68:
	.size	atomic_max_64_seqcst, .Lfunc_end68-atomic_max_64_seqcst
	.cfi_endproc

	.section	.text.atomic_max_8_acqrel,"ax",@progbits
	.globl	atomic_max_8_acqrel
	.p2align	2
	.type	atomic_max_8_acqrel,@function
atomic_max_8_acqrel:
	.cfi_startproc
.LBB69_1:
	ldaxrb	w9, [x0]
	sxtb	w8, w9
	cmp	w8, w1, sxtb
	csel	w9, w9, w1, gt
	stlxrb	w10, w9, [x0]
	cbnz	w10, .LBB69_1
	mov	w0, w8
	ret
.Lfunc_end69:
	.size	atomic_max_8_acqrel, .Lfunc_end69-atomic_max_8_acqrel
	.cfi_endproc

	.section	.text.atomic_max_8_acquire,"ax",@progbits
	.globl	atomic_max_8_acquire
	.p2align	2
	.type	atomic_max_8_acquire,@function
atomic_max_8_acquire:
	.cfi_startproc
.LBB70_1:
	ldaxrb	w9, [x0]
	sxtb	w8, w9
	cmp	w8, w1, sxtb
	csel	w9, w9, w1, gt
	stxrb	w10, w9, [x0]
	cbnz	w10, .LBB70_1
	mov	w0, w8
	ret
.Lfunc_end70:
	.size	atomic_max_8_acquire, .Lfunc_end70-atomic_max_8_acquire
	.cfi_endproc

	.section	.text.atomic_max_8_relaxed,"ax",@progbits
	.globl	atomic_max_8_relaxed
	.p2align	2
	.type	atomic_max_8_relaxed,@function
atomic_max_8_relaxed:
	.cfi_startproc
.LBB71_1:
	ldxrb	w9, [x0]
	sxtb	w8, w9
	cmp	w8, w1, sxtb
	csel	w9, w9, w1, gt
	stxrb	w10, w9, [x0]
	cbnz	w10, .LBB71_1
	mov	w0, w8
	ret
.Lfunc_end71:
	.size	atomic_max_8_relaxed, .Lfunc_end71-atomic_max_8_relaxed
	.cfi_endproc

	.section	.text.atomic_max_8_release,"ax",@progbits
	.globl	atomic_max_8_release
	.p2align	2
	.type	atomic_max_8_release,@function
atomic_max_8_release:
	.cfi_startproc
.LBB72_1:
	ldxrb	w9, [x0]
	sxtb	w8, w9
	cmp	w8, w1, sxtb
	csel	w9, w9, w1, gt
	stlxrb	w10, w9, [x0]
	cbnz	w10, .LBB72_1
	mov	w0, w8
	ret
.Lfunc_end72:
	.size	atomic_max_8_release, .Lfunc_end72-atomic_max_8_release
	.cfi_endproc

	.section	.text.atomic_max_8_seqcst,"ax",@progbits
	.globl	atomic_max_8_seqcst
	.p2align	2
	.type	atomic_max_8_seqcst,@function
atomic_max_8_seqcst:
	.cfi_startproc
.LBB73_1:
	ldaxrb	w9, [x0]
	sxtb	w8, w9
	cmp	w8, w1, sxtb
	csel	w9, w9, w1, gt
	stlxrb	w10, w9, [x0]
	cbnz	w10, .LBB73_1
	mov	w0, w8
	ret
.Lfunc_end73:
	.size	atomic_max_8_seqcst, .Lfunc_end73-atomic_max_8_seqcst
	.cfi_endproc

	.section	.text.atomic_min_128_acqrel,"ax",@progbits
	.globl	atomic_min_128_acqrel
	.p2align	2
	.type	atomic_min_128_acqrel,@function
atomic_min_128_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB74_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, ge
	csel	x10, x0, x2, ge
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB74_1
	ret
.Lfunc_end74:
	.size	atomic_min_128_acqrel, .Lfunc_end74-atomic_min_128_acqrel
	.cfi_endproc

	.section	.text.atomic_min_128_acquire,"ax",@progbits
	.globl	atomic_min_128_acquire
	.p2align	2
	.type	atomic_min_128_acquire,@function
atomic_min_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB75_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, ge
	csel	x10, x0, x2, ge
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB75_1
	ret
.Lfunc_end75:
	.size	atomic_min_128_acquire, .Lfunc_end75-atomic_min_128_acquire
	.cfi_endproc

	.section	.text.atomic_min_128_relaxed,"ax",@progbits
	.globl	atomic_min_128_relaxed
	.p2align	2
	.type	atomic_min_128_relaxed,@function
atomic_min_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB76_1:
	ldxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, ge
	csel	x10, x0, x2, ge
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB76_1
	ret
.Lfunc_end76:
	.size	atomic_min_128_relaxed, .Lfunc_end76-atomic_min_128_relaxed
	.cfi_endproc

	.section	.text.atomic_min_128_release,"ax",@progbits
	.globl	atomic_min_128_release
	.p2align	2
	.type	atomic_min_128_release,@function
atomic_min_128_release:
	.cfi_startproc
	mov	x8, x0
.LBB77_1:
	ldxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, ge
	csel	x10, x0, x2, ge
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB77_1
	ret
.Lfunc_end77:
	.size	atomic_min_128_release, .Lfunc_end77-atomic_min_128_release
	.cfi_endproc

	.section	.text.atomic_min_128_seqcst,"ax",@progbits
	.globl	atomic_min_128_seqcst
	.p2align	2
	.type	atomic_min_128_seqcst,@function
atomic_min_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB78_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, ge
	csel	x10, x0, x2, ge
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB78_1
	ret
.Lfunc_end78:
	.size	atomic_min_128_seqcst, .Lfunc_end78-atomic_min_128_seqcst
	.cfi_endproc

	.section	.text.atomic_min_16_acqrel,"ax",@progbits
	.globl	atomic_min_16_acqrel
	.p2align	2
	.type	atomic_min_16_acqrel,@function
atomic_min_16_acqrel:
	.cfi_startproc
.LBB79_1:
	ldaxrh	w9, [x0]
	sxth	w8, w9
	cmp	w8, w1, sxth
	csel	w9, w9, w1, le
	stlxrh	w10, w9, [x0]
	cbnz	w10, .LBB79_1
	mov	w0, w8
	ret
.Lfunc_end79:
	.size	atomic_min_16_acqrel, .Lfunc_end79-atomic_min_16_acqrel
	.cfi_endproc

	.section	.text.atomic_min_16_acquire,"ax",@progbits
	.globl	atomic_min_16_acquire
	.p2align	2
	.type	atomic_min_16_acquire,@function
atomic_min_16_acquire:
	.cfi_startproc
.LBB80_1:
	ldaxrh	w9, [x0]
	sxth	w8, w9
	cmp	w8, w1, sxth
	csel	w9, w9, w1, le
	stxrh	w10, w9, [x0]
	cbnz	w10, .LBB80_1
	mov	w0, w8
	ret
.Lfunc_end80:
	.size	atomic_min_16_acquire, .Lfunc_end80-atomic_min_16_acquire
	.cfi_endproc

	.section	.text.atomic_min_16_relaxed,"ax",@progbits
	.globl	atomic_min_16_relaxed
	.p2align	2
	.type	atomic_min_16_relaxed,@function
atomic_min_16_relaxed:
	.cfi_startproc
.LBB81_1:
	ldxrh	w9, [x0]
	sxth	w8, w9
	cmp	w8, w1, sxth
	csel	w9, w9, w1, le
	stxrh	w10, w9, [x0]
	cbnz	w10, .LBB81_1
	mov	w0, w8
	ret
.Lfunc_end81:
	.size	atomic_min_16_relaxed, .Lfunc_end81-atomic_min_16_relaxed
	.cfi_endproc

	.section	.text.atomic_min_16_release,"ax",@progbits
	.globl	atomic_min_16_release
	.p2align	2
	.type	atomic_min_16_release,@function
atomic_min_16_release:
	.cfi_startproc
.LBB82_1:
	ldxrh	w9, [x0]
	sxth	w8, w9
	cmp	w8, w1, sxth
	csel	w9, w9, w1, le
	stlxrh	w10, w9, [x0]
	cbnz	w10, .LBB82_1
	mov	w0, w8
	ret
.Lfunc_end82:
	.size	atomic_min_16_release, .Lfunc_end82-atomic_min_16_release
	.cfi_endproc

	.section	.text.atomic_min_16_seqcst,"ax",@progbits
	.globl	atomic_min_16_seqcst
	.p2align	2
	.type	atomic_min_16_seqcst,@function
atomic_min_16_seqcst:
	.cfi_startproc
.LBB83_1:
	ldaxrh	w9, [x0]
	sxth	w8, w9
	cmp	w8, w1, sxth
	csel	w9, w9, w1, le
	stlxrh	w10, w9, [x0]
	cbnz	w10, .LBB83_1
	mov	w0, w8
	ret
.Lfunc_end83:
	.size	atomic_min_16_seqcst, .Lfunc_end83-atomic_min_16_seqcst
	.cfi_endproc

	.section	.text.atomic_min_32_acqrel,"ax",@progbits
	.globl	atomic_min_32_acqrel
	.p2align	2
	.type	atomic_min_32_acqrel,@function
atomic_min_32_acqrel:
	.cfi_startproc
.LBB84_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, le
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB84_1
	mov	w0, w8
	ret
.Lfunc_end84:
	.size	atomic_min_32_acqrel, .Lfunc_end84-atomic_min_32_acqrel
	.cfi_endproc

	.section	.text.atomic_min_32_acquire,"ax",@progbits
	.globl	atomic_min_32_acquire
	.p2align	2
	.type	atomic_min_32_acquire,@function
atomic_min_32_acquire:
	.cfi_startproc
.LBB85_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, le
	stxr	w10, w9, [x0]
	cbnz	w10, .LBB85_1
	mov	w0, w8
	ret
.Lfunc_end85:
	.size	atomic_min_32_acquire, .Lfunc_end85-atomic_min_32_acquire
	.cfi_endproc

	.section	.text.atomic_min_32_relaxed,"ax",@progbits
	.globl	atomic_min_32_relaxed
	.p2align	2
	.type	atomic_min_32_relaxed,@function
atomic_min_32_relaxed:
	.cfi_startproc
.LBB86_1:
	ldxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, le
	stxr	w10, w9, [x0]
	cbnz	w10, .LBB86_1
	mov	w0, w8
	ret
.Lfunc_end86:
	.size	atomic_min_32_relaxed, .Lfunc_end86-atomic_min_32_relaxed
	.cfi_endproc

	.section	.text.atomic_min_32_release,"ax",@progbits
	.globl	atomic_min_32_release
	.p2align	2
	.type	atomic_min_32_release,@function
atomic_min_32_release:
	.cfi_startproc
.LBB87_1:
	ldxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, le
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB87_1
	mov	w0, w8
	ret
.Lfunc_end87:
	.size	atomic_min_32_release, .Lfunc_end87-atomic_min_32_release
	.cfi_endproc

	.section	.text.atomic_min_32_seqcst,"ax",@progbits
	.globl	atomic_min_32_seqcst
	.p2align	2
	.type	atomic_min_32_seqcst,@function
atomic_min_32_seqcst:
	.cfi_startproc
.LBB88_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, le
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB88_1
	mov	w0, w8
	ret
.Lfunc_end88:
	.size	atomic_min_32_seqcst, .Lfunc_end88-atomic_min_32_seqcst
	.cfi_endproc

	.section	.text.atomic_min_64_acqrel,"ax",@progbits
	.globl	atomic_min_64_acqrel
	.p2align	2
	.type	atomic_min_64_acqrel,@function
atomic_min_64_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB89_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, le
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB89_1
	ret
.Lfunc_end89:
	.size	atomic_min_64_acqrel, .Lfunc_end89-atomic_min_64_acqrel
	.cfi_endproc

	.section	.text.atomic_min_64_acquire,"ax",@progbits
	.globl	atomic_min_64_acquire
	.p2align	2
	.type	atomic_min_64_acquire,@function
atomic_min_64_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB90_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, le
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB90_1
	ret
.Lfunc_end90:
	.size	atomic_min_64_acquire, .Lfunc_end90-atomic_min_64_acquire
	.cfi_endproc

	.section	.text.atomic_min_64_relaxed,"ax",@progbits
	.globl	atomic_min_64_relaxed
	.p2align	2
	.type	atomic_min_64_relaxed,@function
atomic_min_64_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB91_1:
	ldxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, le
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB91_1
	ret
.Lfunc_end91:
	.size	atomic_min_64_relaxed, .Lfunc_end91-atomic_min_64_relaxed
	.cfi_endproc

	.section	.text.atomic_min_64_release,"ax",@progbits
	.globl	atomic_min_64_release
	.p2align	2
	.type	atomic_min_64_release,@function
atomic_min_64_release:
	.cfi_startproc
	mov	x8, x0
.LBB92_1:
	ldxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, le
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB92_1
	ret
.Lfunc_end92:
	.size	atomic_min_64_release, .Lfunc_end92-atomic_min_64_release
	.cfi_endproc

	.section	.text.atomic_min_64_seqcst,"ax",@progbits
	.globl	atomic_min_64_seqcst
	.p2align	2
	.type	atomic_min_64_seqcst,@function
atomic_min_64_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB93_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, le
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB93_1
	ret
.Lfunc_end93:
	.size	atomic_min_64_seqcst, .Lfunc_end93-atomic_min_64_seqcst
	.cfi_endproc

	.section	.text.atomic_min_8_acqrel,"ax",@progbits
	.globl	atomic_min_8_acqrel
	.p2align	2
	.type	atomic_min_8_acqrel,@function
atomic_min_8_acqrel:
	.cfi_startproc
.LBB94_1:
	ldaxrb	w9, [x0]
	sxtb	w8, w9
	cmp	w8, w1, sxtb
	csel	w9, w9, w1, le
	stlxrb	w10, w9, [x0]
	cbnz	w10, .LBB94_1
	mov	w0, w8
	ret
.Lfunc_end94:
	.size	atomic_min_8_acqrel, .Lfunc_end94-atomic_min_8_acqrel
	.cfi_endproc

	.section	.text.atomic_min_8_acquire,"ax",@progbits
	.globl	atomic_min_8_acquire
	.p2align	2
	.type	atomic_min_8_acquire,@function
atomic_min_8_acquire:
	.cfi_startproc
.LBB95_1:
	ldaxrb	w9, [x0]
	sxtb	w8, w9
	cmp	w8, w1, sxtb
	csel	w9, w9, w1, le
	stxrb	w10, w9, [x0]
	cbnz	w10, .LBB95_1
	mov	w0, w8
	ret
.Lfunc_end95:
	.size	atomic_min_8_acquire, .Lfunc_end95-atomic_min_8_acquire
	.cfi_endproc

	.section	.text.atomic_min_8_relaxed,"ax",@progbits
	.globl	atomic_min_8_relaxed
	.p2align	2
	.type	atomic_min_8_relaxed,@function
atomic_min_8_relaxed:
	.cfi_startproc
.LBB96_1:
	ldxrb	w9, [x0]
	sxtb	w8, w9
	cmp	w8, w1, sxtb
	csel	w9, w9, w1, le
	stxrb	w10, w9, [x0]
	cbnz	w10, .LBB96_1
	mov	w0, w8
	ret
.Lfunc_end96:
	.size	atomic_min_8_relaxed, .Lfunc_end96-atomic_min_8_relaxed
	.cfi_endproc

	.section	.text.atomic_min_8_release,"ax",@progbits
	.globl	atomic_min_8_release
	.p2align	2
	.type	atomic_min_8_release,@function
atomic_min_8_release:
	.cfi_startproc
.LBB97_1:
	ldxrb	w9, [x0]
	sxtb	w8, w9
	cmp	w8, w1, sxtb
	csel	w9, w9, w1, le
	stlxrb	w10, w9, [x0]
	cbnz	w10, .LBB97_1
	mov	w0, w8
	ret
.Lfunc_end97:
	.size	atomic_min_8_release, .Lfunc_end97-atomic_min_8_release
	.cfi_endproc

	.section	.text.atomic_min_8_seqcst,"ax",@progbits
	.globl	atomic_min_8_seqcst
	.p2align	2
	.type	atomic_min_8_seqcst,@function
atomic_min_8_seqcst:
	.cfi_startproc
.LBB98_1:
	ldaxrb	w9, [x0]
	sxtb	w8, w9
	cmp	w8, w1, sxtb
	csel	w9, w9, w1, le
	stlxrb	w10, w9, [x0]
	cbnz	w10, .LBB98_1
	mov	w0, w8
	ret
.Lfunc_end98:
	.size	atomic_min_8_seqcst, .Lfunc_end98-atomic_min_8_seqcst
	.cfi_endproc

	.section	.text.atomic_nand_128_acqrel,"ax",@progbits
	.globl	atomic_nand_128_acqrel
	.p2align	2
	.type	atomic_nand_128_acqrel,@function
atomic_nand_128_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB99_1:
	ldaxp	x0, x1, [x8]
	and	x9, x0, x2
	and	x10, x1, x3
	mvn	x10, x10
	mvn	x9, x9
	stlxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB99_1
	ret
.Lfunc_end99:
	.size	atomic_nand_128_acqrel, .Lfunc_end99-atomic_nand_128_acqrel
	.cfi_endproc

	.section	.text.atomic_nand_128_acquire,"ax",@progbits
	.globl	atomic_nand_128_acquire
	.p2align	2
	.type	atomic_nand_128_acquire,@function
atomic_nand_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB100_1:
	ldaxp	x0, x1, [x8]
	and	x9, x0, x2
	and	x10, x1, x3
	mvn	x10, x10
	mvn	x9, x9
	stxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB100_1
	ret
.Lfunc_end100:
	.size	atomic_nand_128_acquire, .Lfunc_end100-atomic_nand_128_acquire
	.cfi_endproc

	.section	.text.atomic_nand_128_relaxed,"ax",@progbits
	.globl	atomic_nand_128_relaxed
	.p2align	2
	.type	atomic_nand_128_relaxed,@function
atomic_nand_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB101_1:
	ldxp	x0, x1, [x8]
	and	x9, x0, x2
	and	x10, x1, x3
	mvn	x10, x10
	mvn	x9, x9
	stxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB101_1
	ret
.Lfunc_end101:
	.size	atomic_nand_128_relaxed, .Lfunc_end101-atomic_nand_128_relaxed
	.cfi_endproc

	.section	.text.atomic_nand_128_release,"ax",@progbits
	.globl	atomic_nand_128_release
	.p2align	2
	.type	atomic_nand_128_release,@function
atomic_nand_128_release:
	.cfi_startproc
	mov	x8, x0
.LBB102_1:
	ldxp	x0, x1, [x8]
	and	x9, x0, x2
	and	x10, x1, x3
	mvn	x10, x10
	mvn	x9, x9
	stlxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB102_1
	ret
.Lfunc_end102:
	.size	atomic_nand_128_release, .Lfunc_end102-atomic_nand_128_release
	.cfi_endproc

	.section	.text.atomic_nand_128_seqcst,"ax",@progbits
	.globl	atomic_nand_128_seqcst
	.p2align	2
	.type	atomic_nand_128_seqcst,@function
atomic_nand_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB103_1:
	ldaxp	x0, x1, [x8]
	and	x9, x0, x2
	and	x10, x1, x3
	mvn	x10, x10
	mvn	x9, x9
	stlxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB103_1
	ret
.Lfunc_end103:
	.size	atomic_nand_128_seqcst, .Lfunc_end103-atomic_nand_128_seqcst
	.cfi_endproc

	.section	.text.atomic_nand_16_acqrel,"ax",@progbits
	.globl	atomic_nand_16_acqrel
	.p2align	2
	.type	atomic_nand_16_acqrel,@function
atomic_nand_16_acqrel:
	.cfi_startproc
.LBB104_1:
	ldaxrh	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stlxrh	w10, w9, [x0]
	cbnz	w10, .LBB104_1
	mov	w0, w8
	ret
.Lfunc_end104:
	.size	atomic_nand_16_acqrel, .Lfunc_end104-atomic_nand_16_acqrel
	.cfi_endproc

	.section	.text.atomic_nand_16_acquire,"ax",@progbits
	.globl	atomic_nand_16_acquire
	.p2align	2
	.type	atomic_nand_16_acquire,@function
atomic_nand_16_acquire:
	.cfi_startproc
.LBB105_1:
	ldaxrh	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stxrh	w10, w9, [x0]
	cbnz	w10, .LBB105_1
	mov	w0, w8
	ret
.Lfunc_end105:
	.size	atomic_nand_16_acquire, .Lfunc_end105-atomic_nand_16_acquire
	.cfi_endproc

	.section	.text.atomic_nand_16_relaxed,"ax",@progbits
	.globl	atomic_nand_16_relaxed
	.p2align	2
	.type	atomic_nand_16_relaxed,@function
atomic_nand_16_relaxed:
	.cfi_startproc
.LBB106_1:
	ldxrh	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stxrh	w10, w9, [x0]
	cbnz	w10, .LBB106_1
	mov	w0, w8
	ret
.Lfunc_end106:
	.size	atomic_nand_16_relaxed, .Lfunc_end106-atomic_nand_16_relaxed
	.cfi_endproc

	.section	.text.atomic_nand_16_release,"ax",@progbits
	.globl	atomic_nand_16_release
	.p2align	2
	.type	atomic_nand_16_release,@function
atomic_nand_16_release:
	.cfi_startproc
.LBB107_1:
	ldxrh	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stlxrh	w10, w9, [x0]
	cbnz	w10, .LBB107_1
	mov	w0, w8
	ret
.Lfunc_end107:
	.size	atomic_nand_16_release, .Lfunc_end107-atomic_nand_16_release
	.cfi_endproc

	.section	.text.atomic_nand_16_seqcst,"ax",@progbits
	.globl	atomic_nand_16_seqcst
	.p2align	2
	.type	atomic_nand_16_seqcst,@function
atomic_nand_16_seqcst:
	.cfi_startproc
.LBB108_1:
	ldaxrh	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stlxrh	w10, w9, [x0]
	cbnz	w10, .LBB108_1
	mov	w0, w8
	ret
.Lfunc_end108:
	.size	atomic_nand_16_seqcst, .Lfunc_end108-atomic_nand_16_seqcst
	.cfi_endproc

	.section	.text.atomic_nand_32_acqrel,"ax",@progbits
	.globl	atomic_nand_32_acqrel
	.p2align	2
	.type	atomic_nand_32_acqrel,@function
atomic_nand_32_acqrel:
	.cfi_startproc
.LBB109_1:
	ldaxr	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB109_1
	mov	w0, w8
	ret
.Lfunc_end109:
	.size	atomic_nand_32_acqrel, .Lfunc_end109-atomic_nand_32_acqrel
	.cfi_endproc

	.section	.text.atomic_nand_32_acquire,"ax",@progbits
	.globl	atomic_nand_32_acquire
	.p2align	2
	.type	atomic_nand_32_acquire,@function
atomic_nand_32_acquire:
	.cfi_startproc
.LBB110_1:
	ldaxr	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stxr	w10, w9, [x0]
	cbnz	w10, .LBB110_1
	mov	w0, w8
	ret
.Lfunc_end110:
	.size	atomic_nand_32_acquire, .Lfunc_end110-atomic_nand_32_acquire
	.cfi_endproc

	.section	.text.atomic_nand_32_relaxed,"ax",@progbits
	.globl	atomic_nand_32_relaxed
	.p2align	2
	.type	atomic_nand_32_relaxed,@function
atomic_nand_32_relaxed:
	.cfi_startproc
.LBB111_1:
	ldxr	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stxr	w10, w9, [x0]
	cbnz	w10, .LBB111_1
	mov	w0, w8
	ret
.Lfunc_end111:
	.size	atomic_nand_32_relaxed, .Lfunc_end111-atomic_nand_32_relaxed
	.cfi_endproc

	.section	.text.atomic_nand_32_release,"ax",@progbits
	.globl	atomic_nand_32_release
	.p2align	2
	.type	atomic_nand_32_release,@function
atomic_nand_32_release:
	.cfi_startproc
.LBB112_1:
	ldxr	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB112_1
	mov	w0, w8
	ret
.Lfunc_end112:
	.size	atomic_nand_32_release, .Lfunc_end112-atomic_nand_32_release
	.cfi_endproc

	.section	.text.atomic_nand_32_seqcst,"ax",@progbits
	.globl	atomic_nand_32_seqcst
	.p2align	2
	.type	atomic_nand_32_seqcst,@function
atomic_nand_32_seqcst:
	.cfi_startproc
.LBB113_1:
	ldaxr	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB113_1
	mov	w0, w8
	ret
.Lfunc_end113:
	.size	atomic_nand_32_seqcst, .Lfunc_end113-atomic_nand_32_seqcst
	.cfi_endproc

	.section	.text.atomic_nand_64_acqrel,"ax",@progbits
	.globl	atomic_nand_64_acqrel
	.p2align	2
	.type	atomic_nand_64_acqrel,@function
atomic_nand_64_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB114_1:
	ldaxr	x0, [x8]
	and	x9, x0, x1
	mvn	x9, x9
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB114_1
	ret
.Lfunc_end114:
	.size	atomic_nand_64_acqrel, .Lfunc_end114-atomic_nand_64_acqrel
	.cfi_endproc

	.section	.text.atomic_nand_64_acquire,"ax",@progbits
	.globl	atomic_nand_64_acquire
	.p2align	2
	.type	atomic_nand_64_acquire,@function
atomic_nand_64_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB115_1:
	ldaxr	x0, [x8]
	and	x9, x0, x1
	mvn	x9, x9
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB115_1
	ret
.Lfunc_end115:
	.size	atomic_nand_64_acquire, .Lfunc_end115-atomic_nand_64_acquire
	.cfi_endproc

	.section	.text.atomic_nand_64_relaxed,"ax",@progbits
	.globl	atomic_nand_64_relaxed
	.p2align	2
	.type	atomic_nand_64_relaxed,@function
atomic_nand_64_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB116_1:
	ldxr	x0, [x8]
	and	x9, x0, x1
	mvn	x9, x9
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB116_1
	ret
.Lfunc_end116:
	.size	atomic_nand_64_relaxed, .Lfunc_end116-atomic_nand_64_relaxed
	.cfi_endproc

	.section	.text.atomic_nand_64_release,"ax",@progbits
	.globl	atomic_nand_64_release
	.p2align	2
	.type	atomic_nand_64_release,@function
atomic_nand_64_release:
	.cfi_startproc
	mov	x8, x0
.LBB117_1:
	ldxr	x0, [x8]
	and	x9, x0, x1
	mvn	x9, x9
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB117_1
	ret
.Lfunc_end117:
	.size	atomic_nand_64_release, .Lfunc_end117-atomic_nand_64_release
	.cfi_endproc

	.section	.text.atomic_nand_64_seqcst,"ax",@progbits
	.globl	atomic_nand_64_seqcst
	.p2align	2
	.type	atomic_nand_64_seqcst,@function
atomic_nand_64_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB118_1:
	ldaxr	x0, [x8]
	and	x9, x0, x1
	mvn	x9, x9
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB118_1
	ret
.Lfunc_end118:
	.size	atomic_nand_64_seqcst, .Lfunc_end118-atomic_nand_64_seqcst
	.cfi_endproc

	.section	.text.atomic_nand_8_acqrel,"ax",@progbits
	.globl	atomic_nand_8_acqrel
	.p2align	2
	.type	atomic_nand_8_acqrel,@function
atomic_nand_8_acqrel:
	.cfi_startproc
.LBB119_1:
	ldaxrb	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stlxrb	w10, w9, [x0]
	cbnz	w10, .LBB119_1
	mov	w0, w8
	ret
.Lfunc_end119:
	.size	atomic_nand_8_acqrel, .Lfunc_end119-atomic_nand_8_acqrel
	.cfi_endproc

	.section	.text.atomic_nand_8_acquire,"ax",@progbits
	.globl	atomic_nand_8_acquire
	.p2align	2
	.type	atomic_nand_8_acquire,@function
atomic_nand_8_acquire:
	.cfi_startproc
.LBB120_1:
	ldaxrb	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stxrb	w10, w9, [x0]
	cbnz	w10, .LBB120_1
	mov	w0, w8
	ret
.Lfunc_end120:
	.size	atomic_nand_8_acquire, .Lfunc_end120-atomic_nand_8_acquire
	.cfi_endproc

	.section	.text.atomic_nand_8_relaxed,"ax",@progbits
	.globl	atomic_nand_8_relaxed
	.p2align	2
	.type	atomic_nand_8_relaxed,@function
atomic_nand_8_relaxed:
	.cfi_startproc
.LBB121_1:
	ldxrb	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stxrb	w10, w9, [x0]
	cbnz	w10, .LBB121_1
	mov	w0, w8
	ret
.Lfunc_end121:
	.size	atomic_nand_8_relaxed, .Lfunc_end121-atomic_nand_8_relaxed
	.cfi_endproc

	.section	.text.atomic_nand_8_release,"ax",@progbits
	.globl	atomic_nand_8_release
	.p2align	2
	.type	atomic_nand_8_release,@function
atomic_nand_8_release:
	.cfi_startproc
.LBB122_1:
	ldxrb	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stlxrb	w10, w9, [x0]
	cbnz	w10, .LBB122_1
	mov	w0, w8
	ret
.Lfunc_end122:
	.size	atomic_nand_8_release, .Lfunc_end122-atomic_nand_8_release
	.cfi_endproc

	.section	.text.atomic_nand_8_seqcst,"ax",@progbits
	.globl	atomic_nand_8_seqcst
	.p2align	2
	.type	atomic_nand_8_seqcst,@function
atomic_nand_8_seqcst:
	.cfi_startproc
.LBB123_1:
	ldaxrb	w8, [x0]
	and	w9, w8, w1
	mvn	w9, w9
	stlxrb	w10, w9, [x0]
	cbnz	w10, .LBB123_1
	mov	w0, w8
	ret
.Lfunc_end123:
	.size	atomic_nand_8_seqcst, .Lfunc_end123-atomic_nand_8_seqcst
	.cfi_endproc

	.section	.text.atomic_or_128_acqrel,"ax",@progbits
	.globl	atomic_or_128_acqrel
	.p2align	2
	.type	atomic_or_128_acqrel,@function
atomic_or_128_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB124_1:
	ldaxp	x0, x1, [x8]
	orr	x9, x1, x3
	orr	x10, x0, x2
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB124_1
	ret
.Lfunc_end124:
	.size	atomic_or_128_acqrel, .Lfunc_end124-atomic_or_128_acqrel
	.cfi_endproc

	.section	.text.atomic_or_128_acquire,"ax",@progbits
	.globl	atomic_or_128_acquire
	.p2align	2
	.type	atomic_or_128_acquire,@function
atomic_or_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB125_1:
	ldaxp	x0, x1, [x8]
	orr	x9, x1, x3
	orr	x10, x0, x2
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB125_1
	ret
.Lfunc_end125:
	.size	atomic_or_128_acquire, .Lfunc_end125-atomic_or_128_acquire
	.cfi_endproc

	.section	.text.atomic_or_128_relaxed,"ax",@progbits
	.globl	atomic_or_128_relaxed
	.p2align	2
	.type	atomic_or_128_relaxed,@function
atomic_or_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB126_1:
	ldxp	x0, x1, [x8]
	orr	x9, x1, x3
	orr	x10, x0, x2
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB126_1
	ret
.Lfunc_end126:
	.size	atomic_or_128_relaxed, .Lfunc_end126-atomic_or_128_relaxed
	.cfi_endproc

	.section	.text.atomic_or_128_release,"ax",@progbits
	.globl	atomic_or_128_release
	.p2align	2
	.type	atomic_or_128_release,@function
atomic_or_128_release:
	.cfi_startproc
	mov	x8, x0
.LBB127_1:
	ldxp	x0, x1, [x8]
	orr	x9, x1, x3
	orr	x10, x0, x2
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB127_1
	ret
.Lfunc_end127:
	.size	atomic_or_128_release, .Lfunc_end127-atomic_or_128_release
	.cfi_endproc

	.section	.text.atomic_or_128_seqcst,"ax",@progbits
	.globl	atomic_or_128_seqcst
	.p2align	2
	.type	atomic_or_128_seqcst,@function
atomic_or_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB128_1:
	ldaxp	x0, x1, [x8]
	orr	x9, x1, x3
	orr	x10, x0, x2
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB128_1
	ret
.Lfunc_end128:
	.size	atomic_or_128_seqcst, .Lfunc_end128-atomic_or_128_seqcst
	.cfi_endproc

	.section	.text.atomic_or_16_acqrel,"ax",@progbits
	.globl	atomic_or_16_acqrel
	.p2align	2
	.type	atomic_or_16_acqrel,@function
atomic_or_16_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end129:
	.size	atomic_or_16_acqrel, .Lfunc_end129-atomic_or_16_acqrel
	.cfi_endproc

	.section	.text.atomic_or_16_acquire,"ax",@progbits
	.globl	atomic_or_16_acquire
	.p2align	2
	.type	atomic_or_16_acquire,@function
atomic_or_16_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset2_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end130:
	.size	atomic_or_16_acquire, .Lfunc_end130-atomic_or_16_acquire
	.cfi_endproc

	.section	.text.atomic_or_16_relaxed,"ax",@progbits
	.globl	atomic_or_16_relaxed
	.p2align	2
	.type	atomic_or_16_relaxed,@function
atomic_or_16_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset2_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end131:
	.size	atomic_or_16_relaxed, .Lfunc_end131-atomic_or_16_relaxed
	.cfi_endproc

	.section	.text.atomic_or_16_release,"ax",@progbits
	.globl	atomic_or_16_release
	.p2align	2
	.type	atomic_or_16_release,@function
atomic_or_16_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset2_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end132:
	.size	atomic_or_16_release, .Lfunc_end132-atomic_or_16_release
	.cfi_endproc

	.section	.text.atomic_or_16_seqcst,"ax",@progbits
	.globl	atomic_or_16_seqcst
	.p2align	2
	.type	atomic_or_16_seqcst,@function
atomic_or_16_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end133:
	.size	atomic_or_16_seqcst, .Lfunc_end133-atomic_or_16_seqcst
	.cfi_endproc

	.section	.text.atomic_or_32_acqrel,"ax",@progbits
	.globl	atomic_or_32_acqrel
	.p2align	2
	.type	atomic_or_32_acqrel,@function
atomic_or_32_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end134:
	.size	atomic_or_32_acqrel, .Lfunc_end134-atomic_or_32_acqrel
	.cfi_endproc

	.section	.text.atomic_or_32_acquire,"ax",@progbits
	.globl	atomic_or_32_acquire
	.p2align	2
	.type	atomic_or_32_acquire,@function
atomic_or_32_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset4_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end135:
	.size	atomic_or_32_acquire, .Lfunc_end135-atomic_or_32_acquire
	.cfi_endproc

	.section	.text.atomic_or_32_relaxed,"ax",@progbits
	.globl	atomic_or_32_relaxed
	.p2align	2
	.type	atomic_or_32_relaxed,@function
atomic_or_32_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset4_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end136:
	.size	atomic_or_32_relaxed, .Lfunc_end136-atomic_or_32_relaxed
	.cfi_endproc

	.section	.text.atomic_or_32_release,"ax",@progbits
	.globl	atomic_or_32_release
	.p2align	2
	.type	atomic_or_32_release,@function
atomic_or_32_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset4_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end137:
	.size	atomic_or_32_release, .Lfunc_end137-atomic_or_32_release
	.cfi_endproc

	.section	.text.atomic_or_32_seqcst,"ax",@progbits
	.globl	atomic_or_32_seqcst
	.p2align	2
	.type	atomic_or_32_seqcst,@function
atomic_or_32_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end138:
	.size	atomic_or_32_seqcst, .Lfunc_end138-atomic_or_32_seqcst
	.cfi_endproc

	.section	.text.atomic_or_64_acqrel,"ax",@progbits
	.globl	atomic_or_64_acqrel
	.p2align	2
	.type	atomic_or_64_acqrel,@function
atomic_or_64_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldset8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end139:
	.size	atomic_or_64_acqrel, .Lfunc_end139-atomic_or_64_acqrel
	.cfi_endproc

	.section	.text.atomic_or_64_acquire,"ax",@progbits
	.globl	atomic_or_64_acquire
	.p2align	2
	.type	atomic_or_64_acquire,@function
atomic_or_64_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldset8_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end140:
	.size	atomic_or_64_acquire, .Lfunc_end140-atomic_or_64_acquire
	.cfi_endproc

	.section	.text.atomic_or_64_relaxed,"ax",@progbits
	.globl	atomic_or_64_relaxed
	.p2align	2
	.type	atomic_or_64_relaxed,@function
atomic_or_64_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldset8_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end141:
	.size	atomic_or_64_relaxed, .Lfunc_end141-atomic_or_64_relaxed
	.cfi_endproc

	.section	.text.atomic_or_64_release,"ax",@progbits
	.globl	atomic_or_64_release
	.p2align	2
	.type	atomic_or_64_release,@function
atomic_or_64_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldset8_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end142:
	.size	atomic_or_64_release, .Lfunc_end142-atomic_or_64_release
	.cfi_endproc

	.section	.text.atomic_or_64_seqcst,"ax",@progbits
	.globl	atomic_or_64_seqcst
	.p2align	2
	.type	atomic_or_64_seqcst,@function
atomic_or_64_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldset8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end143:
	.size	atomic_or_64_seqcst, .Lfunc_end143-atomic_or_64_seqcst
	.cfi_endproc

	.section	.text.atomic_or_8_acqrel,"ax",@progbits
	.globl	atomic_or_8_acqrel
	.p2align	2
	.type	atomic_or_8_acqrel,@function
atomic_or_8_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end144:
	.size	atomic_or_8_acqrel, .Lfunc_end144-atomic_or_8_acqrel
	.cfi_endproc

	.section	.text.atomic_or_8_acquire,"ax",@progbits
	.globl	atomic_or_8_acquire
	.p2align	2
	.type	atomic_or_8_acquire,@function
atomic_or_8_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset1_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end145:
	.size	atomic_or_8_acquire, .Lfunc_end145-atomic_or_8_acquire
	.cfi_endproc

	.section	.text.atomic_or_8_relaxed,"ax",@progbits
	.globl	atomic_or_8_relaxed
	.p2align	2
	.type	atomic_or_8_relaxed,@function
atomic_or_8_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset1_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end146:
	.size	atomic_or_8_relaxed, .Lfunc_end146-atomic_or_8_relaxed
	.cfi_endproc

	.section	.text.atomic_or_8_release,"ax",@progbits
	.globl	atomic_or_8_release
	.p2align	2
	.type	atomic_or_8_release,@function
atomic_or_8_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset1_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end147:
	.size	atomic_or_8_release, .Lfunc_end147-atomic_or_8_release
	.cfi_endproc

	.section	.text.atomic_or_8_seqcst,"ax",@progbits
	.globl	atomic_or_8_seqcst
	.p2align	2
	.type	atomic_or_8_seqcst,@function
atomic_or_8_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldset1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end148:
	.size	atomic_or_8_seqcst, .Lfunc_end148-atomic_or_8_seqcst
	.cfi_endproc

	.section	.text.atomic_store_128_relaxed,"ax",@progbits
	.globl	atomic_store_128_relaxed
	.p2align	2
	.type	atomic_store_128_relaxed,@function
atomic_store_128_relaxed:
	.cfi_startproc
.LBB149_1:
	ldxp	xzr, x8, [x0]
	stxp	w8, x2, x3, [x0]
	cbnz	w8, .LBB149_1
	ret
.Lfunc_end149:
	.size	atomic_store_128_relaxed, .Lfunc_end149-atomic_store_128_relaxed
	.cfi_endproc

	.section	.text.atomic_store_128_release,"ax",@progbits
	.globl	atomic_store_128_release
	.p2align	2
	.type	atomic_store_128_release,@function
atomic_store_128_release:
	.cfi_startproc
.LBB150_1:
	ldxp	xzr, x8, [x0]
	stlxp	w8, x2, x3, [x0]
	cbnz	w8, .LBB150_1
	ret
.Lfunc_end150:
	.size	atomic_store_128_release, .Lfunc_end150-atomic_store_128_release
	.cfi_endproc

	.section	.text.atomic_store_128_seqcst,"ax",@progbits
	.globl	atomic_store_128_seqcst
	.p2align	2
	.type	atomic_store_128_seqcst,@function
atomic_store_128_seqcst:
	.cfi_startproc
.LBB151_1:
	ldaxp	xzr, x8, [x0]
	stlxp	w8, x2, x3, [x0]
	cbnz	w8, .LBB151_1
	ret
.Lfunc_end151:
	.size	atomic_store_128_seqcst, .Lfunc_end151-atomic_store_128_seqcst
	.cfi_endproc

	.section	.text.atomic_store_16_relaxed,"ax",@progbits
	.globl	atomic_store_16_relaxed
	.p2align	2
	.type	atomic_store_16_relaxed,@function
atomic_store_16_relaxed:
	.cfi_startproc
	strh	w1, [x0]
	ret
.Lfunc_end152:
	.size	atomic_store_16_relaxed, .Lfunc_end152-atomic_store_16_relaxed
	.cfi_endproc

	.section	.text.atomic_store_16_release,"ax",@progbits
	.globl	atomic_store_16_release
	.p2align	2
	.type	atomic_store_16_release,@function
atomic_store_16_release:
	.cfi_startproc
	stlrh	w1, [x0]
	ret
.Lfunc_end153:
	.size	atomic_store_16_release, .Lfunc_end153-atomic_store_16_release
	.cfi_endproc

	.section	.text.atomic_store_16_seqcst,"ax",@progbits
	.globl	atomic_store_16_seqcst
	.p2align	2
	.type	atomic_store_16_seqcst,@function
atomic_store_16_seqcst:
	.cfi_startproc
	stlrh	w1, [x0]
	ret
.Lfunc_end154:
	.size	atomic_store_16_seqcst, .Lfunc_end154-atomic_store_16_seqcst
	.cfi_endproc

	.section	.text.atomic_store_32_relaxed,"ax",@progbits
	.globl	atomic_store_32_relaxed
	.p2align	2
	.type	atomic_store_32_relaxed,@function
atomic_store_32_relaxed:
	.cfi_startproc
	str	w1, [x0]
	ret
.Lfunc_end155:
	.size	atomic_store_32_relaxed, .Lfunc_end155-atomic_store_32_relaxed
	.cfi_endproc

	.section	.text.atomic_store_32_release,"ax",@progbits
	.globl	atomic_store_32_release
	.p2align	2
	.type	atomic_store_32_release,@function
atomic_store_32_release:
	.cfi_startproc
	stlr	w1, [x0]
	ret
.Lfunc_end156:
	.size	atomic_store_32_release, .Lfunc_end156-atomic_store_32_release
	.cfi_endproc

	.section	.text.atomic_store_32_seqcst,"ax",@progbits
	.globl	atomic_store_32_seqcst
	.p2align	2
	.type	atomic_store_32_seqcst,@function
atomic_store_32_seqcst:
	.cfi_startproc
	stlr	w1, [x0]
	ret
.Lfunc_end157:
	.size	atomic_store_32_seqcst, .Lfunc_end157-atomic_store_32_seqcst
	.cfi_endproc

	.section	.text.atomic_store_64_relaxed,"ax",@progbits
	.globl	atomic_store_64_relaxed
	.p2align	2
	.type	atomic_store_64_relaxed,@function
atomic_store_64_relaxed:
	.cfi_startproc
	str	x1, [x0]
	ret
.Lfunc_end158:
	.size	atomic_store_64_relaxed, .Lfunc_end158-atomic_store_64_relaxed
	.cfi_endproc

	.section	.text.atomic_store_64_release,"ax",@progbits
	.globl	atomic_store_64_release
	.p2align	2
	.type	atomic_store_64_release,@function
atomic_store_64_release:
	.cfi_startproc
	stlr	x1, [x0]
	ret
.Lfunc_end159:
	.size	atomic_store_64_release, .Lfunc_end159-atomic_store_64_release
	.cfi_endproc

	.section	.text.atomic_store_64_seqcst,"ax",@progbits
	.globl	atomic_store_64_seqcst
	.p2align	2
	.type	atomic_store_64_seqcst,@function
atomic_store_64_seqcst:
	.cfi_startproc
	stlr	x1, [x0]
	ret
.Lfunc_end160:
	.size	atomic_store_64_seqcst, .Lfunc_end160-atomic_store_64_seqcst
	.cfi_endproc

	.section	.text.atomic_store_8_relaxed,"ax",@progbits
	.globl	atomic_store_8_relaxed
	.p2align	2
	.type	atomic_store_8_relaxed,@function
atomic_store_8_relaxed:
	.cfi_startproc
	strb	w1, [x0]
	ret
.Lfunc_end161:
	.size	atomic_store_8_relaxed, .Lfunc_end161-atomic_store_8_relaxed
	.cfi_endproc

	.section	.text.atomic_store_8_release,"ax",@progbits
	.globl	atomic_store_8_release
	.p2align	2
	.type	atomic_store_8_release,@function
atomic_store_8_release:
	.cfi_startproc
	stlrb	w1, [x0]
	ret
.Lfunc_end162:
	.size	atomic_store_8_release, .Lfunc_end162-atomic_store_8_release
	.cfi_endproc

	.section	.text.atomic_store_8_seqcst,"ax",@progbits
	.globl	atomic_store_8_seqcst
	.p2align	2
	.type	atomic_store_8_seqcst,@function
atomic_store_8_seqcst:
	.cfi_startproc
	stlrb	w1, [x0]
	ret
.Lfunc_end163:
	.size	atomic_store_8_seqcst, .Lfunc_end163-atomic_store_8_seqcst
	.cfi_endproc

	.section	.text.atomic_umax_128_acqrel,"ax",@progbits
	.globl	atomic_umax_128_acqrel
	.p2align	2
	.type	atomic_umax_128_acqrel,@function
atomic_umax_128_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB164_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, lo
	csel	x10, x0, x2, lo
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB164_1
	ret
.Lfunc_end164:
	.size	atomic_umax_128_acqrel, .Lfunc_end164-atomic_umax_128_acqrel
	.cfi_endproc

	.section	.text.atomic_umax_128_acquire,"ax",@progbits
	.globl	atomic_umax_128_acquire
	.p2align	2
	.type	atomic_umax_128_acquire,@function
atomic_umax_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB165_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, lo
	csel	x10, x0, x2, lo
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB165_1
	ret
.Lfunc_end165:
	.size	atomic_umax_128_acquire, .Lfunc_end165-atomic_umax_128_acquire
	.cfi_endproc

	.section	.text.atomic_umax_128_relaxed,"ax",@progbits
	.globl	atomic_umax_128_relaxed
	.p2align	2
	.type	atomic_umax_128_relaxed,@function
atomic_umax_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB166_1:
	ldxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, lo
	csel	x10, x0, x2, lo
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB166_1
	ret
.Lfunc_end166:
	.size	atomic_umax_128_relaxed, .Lfunc_end166-atomic_umax_128_relaxed
	.cfi_endproc

	.section	.text.atomic_umax_128_release,"ax",@progbits
	.globl	atomic_umax_128_release
	.p2align	2
	.type	atomic_umax_128_release,@function
atomic_umax_128_release:
	.cfi_startproc
	mov	x8, x0
.LBB167_1:
	ldxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, lo
	csel	x10, x0, x2, lo
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB167_1
	ret
.Lfunc_end167:
	.size	atomic_umax_128_release, .Lfunc_end167-atomic_umax_128_release
	.cfi_endproc

	.section	.text.atomic_umax_128_seqcst,"ax",@progbits
	.globl	atomic_umax_128_seqcst
	.p2align	2
	.type	atomic_umax_128_seqcst,@function
atomic_umax_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB168_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, lo
	csel	x10, x0, x2, lo
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB168_1
	ret
.Lfunc_end168:
	.size	atomic_umax_128_seqcst, .Lfunc_end168-atomic_umax_128_seqcst
	.cfi_endproc

	.section	.text.atomic_umax_16_acqrel,"ax",@progbits
	.globl	atomic_umax_16_acqrel
	.p2align	2
	.type	atomic_umax_16_acqrel,@function
atomic_umax_16_acqrel:
	.cfi_startproc
	and	w9, w1, #0xffff
.LBB169_1:
	ldaxrh	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, hi
	stlxrh	w11, w10, [x0]
	cbnz	w11, .LBB169_1
	mov	w0, w8
	ret
.Lfunc_end169:
	.size	atomic_umax_16_acqrel, .Lfunc_end169-atomic_umax_16_acqrel
	.cfi_endproc

	.section	.text.atomic_umax_16_acquire,"ax",@progbits
	.globl	atomic_umax_16_acquire
	.p2align	2
	.type	atomic_umax_16_acquire,@function
atomic_umax_16_acquire:
	.cfi_startproc
	and	w9, w1, #0xffff
.LBB170_1:
	ldaxrh	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, hi
	stxrh	w11, w10, [x0]
	cbnz	w11, .LBB170_1
	mov	w0, w8
	ret
.Lfunc_end170:
	.size	atomic_umax_16_acquire, .Lfunc_end170-atomic_umax_16_acquire
	.cfi_endproc

	.section	.text.atomic_umax_16_relaxed,"ax",@progbits
	.globl	atomic_umax_16_relaxed
	.p2align	2
	.type	atomic_umax_16_relaxed,@function
atomic_umax_16_relaxed:
	.cfi_startproc
	and	w9, w1, #0xffff
.LBB171_1:
	ldxrh	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, hi
	stxrh	w11, w10, [x0]
	cbnz	w11, .LBB171_1
	mov	w0, w8
	ret
.Lfunc_end171:
	.size	atomic_umax_16_relaxed, .Lfunc_end171-atomic_umax_16_relaxed
	.cfi_endproc

	.section	.text.atomic_umax_16_release,"ax",@progbits
	.globl	atomic_umax_16_release
	.p2align	2
	.type	atomic_umax_16_release,@function
atomic_umax_16_release:
	.cfi_startproc
	and	w9, w1, #0xffff
.LBB172_1:
	ldxrh	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, hi
	stlxrh	w11, w10, [x0]
	cbnz	w11, .LBB172_1
	mov	w0, w8
	ret
.Lfunc_end172:
	.size	atomic_umax_16_release, .Lfunc_end172-atomic_umax_16_release
	.cfi_endproc

	.section	.text.atomic_umax_16_seqcst,"ax",@progbits
	.globl	atomic_umax_16_seqcst
	.p2align	2
	.type	atomic_umax_16_seqcst,@function
atomic_umax_16_seqcst:
	.cfi_startproc
	and	w9, w1, #0xffff
.LBB173_1:
	ldaxrh	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, hi
	stlxrh	w11, w10, [x0]
	cbnz	w11, .LBB173_1
	mov	w0, w8
	ret
.Lfunc_end173:
	.size	atomic_umax_16_seqcst, .Lfunc_end173-atomic_umax_16_seqcst
	.cfi_endproc

	.section	.text.atomic_umax_32_acqrel,"ax",@progbits
	.globl	atomic_umax_32_acqrel
	.p2align	2
	.type	atomic_umax_32_acqrel,@function
atomic_umax_32_acqrel:
	.cfi_startproc
.LBB174_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, hi
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB174_1
	mov	w0, w8
	ret
.Lfunc_end174:
	.size	atomic_umax_32_acqrel, .Lfunc_end174-atomic_umax_32_acqrel
	.cfi_endproc

	.section	.text.atomic_umax_32_acquire,"ax",@progbits
	.globl	atomic_umax_32_acquire
	.p2align	2
	.type	atomic_umax_32_acquire,@function
atomic_umax_32_acquire:
	.cfi_startproc
.LBB175_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, hi
	stxr	w10, w9, [x0]
	cbnz	w10, .LBB175_1
	mov	w0, w8
	ret
.Lfunc_end175:
	.size	atomic_umax_32_acquire, .Lfunc_end175-atomic_umax_32_acquire
	.cfi_endproc

	.section	.text.atomic_umax_32_relaxed,"ax",@progbits
	.globl	atomic_umax_32_relaxed
	.p2align	2
	.type	atomic_umax_32_relaxed,@function
atomic_umax_32_relaxed:
	.cfi_startproc
.LBB176_1:
	ldxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, hi
	stxr	w10, w9, [x0]
	cbnz	w10, .LBB176_1
	mov	w0, w8
	ret
.Lfunc_end176:
	.size	atomic_umax_32_relaxed, .Lfunc_end176-atomic_umax_32_relaxed
	.cfi_endproc

	.section	.text.atomic_umax_32_release,"ax",@progbits
	.globl	atomic_umax_32_release
	.p2align	2
	.type	atomic_umax_32_release,@function
atomic_umax_32_release:
	.cfi_startproc
.LBB177_1:
	ldxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, hi
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB177_1
	mov	w0, w8
	ret
.Lfunc_end177:
	.size	atomic_umax_32_release, .Lfunc_end177-atomic_umax_32_release
	.cfi_endproc

	.section	.text.atomic_umax_32_seqcst,"ax",@progbits
	.globl	atomic_umax_32_seqcst
	.p2align	2
	.type	atomic_umax_32_seqcst,@function
atomic_umax_32_seqcst:
	.cfi_startproc
.LBB178_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, hi
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB178_1
	mov	w0, w8
	ret
.Lfunc_end178:
	.size	atomic_umax_32_seqcst, .Lfunc_end178-atomic_umax_32_seqcst
	.cfi_endproc

	.section	.text.atomic_umax_64_acqrel,"ax",@progbits
	.globl	atomic_umax_64_acqrel
	.p2align	2
	.type	atomic_umax_64_acqrel,@function
atomic_umax_64_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB179_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, hi
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB179_1
	ret
.Lfunc_end179:
	.size	atomic_umax_64_acqrel, .Lfunc_end179-atomic_umax_64_acqrel
	.cfi_endproc

	.section	.text.atomic_umax_64_acquire,"ax",@progbits
	.globl	atomic_umax_64_acquire
	.p2align	2
	.type	atomic_umax_64_acquire,@function
atomic_umax_64_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB180_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, hi
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB180_1
	ret
.Lfunc_end180:
	.size	atomic_umax_64_acquire, .Lfunc_end180-atomic_umax_64_acquire
	.cfi_endproc

	.section	.text.atomic_umax_64_relaxed,"ax",@progbits
	.globl	atomic_umax_64_relaxed
	.p2align	2
	.type	atomic_umax_64_relaxed,@function
atomic_umax_64_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB181_1:
	ldxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, hi
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB181_1
	ret
.Lfunc_end181:
	.size	atomic_umax_64_relaxed, .Lfunc_end181-atomic_umax_64_relaxed
	.cfi_endproc

	.section	.text.atomic_umax_64_release,"ax",@progbits
	.globl	atomic_umax_64_release
	.p2align	2
	.type	atomic_umax_64_release,@function
atomic_umax_64_release:
	.cfi_startproc
	mov	x8, x0
.LBB182_1:
	ldxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, hi
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB182_1
	ret
.Lfunc_end182:
	.size	atomic_umax_64_release, .Lfunc_end182-atomic_umax_64_release
	.cfi_endproc

	.section	.text.atomic_umax_64_seqcst,"ax",@progbits
	.globl	atomic_umax_64_seqcst
	.p2align	2
	.type	atomic_umax_64_seqcst,@function
atomic_umax_64_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB183_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, hi
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB183_1
	ret
.Lfunc_end183:
	.size	atomic_umax_64_seqcst, .Lfunc_end183-atomic_umax_64_seqcst
	.cfi_endproc

	.section	.text.atomic_umax_8_acqrel,"ax",@progbits
	.globl	atomic_umax_8_acqrel
	.p2align	2
	.type	atomic_umax_8_acqrel,@function
atomic_umax_8_acqrel:
	.cfi_startproc
	and	w9, w1, #0xff
.LBB184_1:
	ldaxrb	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, hi
	stlxrb	w11, w10, [x0]
	cbnz	w11, .LBB184_1
	mov	w0, w8
	ret
.Lfunc_end184:
	.size	atomic_umax_8_acqrel, .Lfunc_end184-atomic_umax_8_acqrel
	.cfi_endproc

	.section	.text.atomic_umax_8_acquire,"ax",@progbits
	.globl	atomic_umax_8_acquire
	.p2align	2
	.type	atomic_umax_8_acquire,@function
atomic_umax_8_acquire:
	.cfi_startproc
	and	w9, w1, #0xff
.LBB185_1:
	ldaxrb	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, hi
	stxrb	w11, w10, [x0]
	cbnz	w11, .LBB185_1
	mov	w0, w8
	ret
.Lfunc_end185:
	.size	atomic_umax_8_acquire, .Lfunc_end185-atomic_umax_8_acquire
	.cfi_endproc

	.section	.text.atomic_umax_8_relaxed,"ax",@progbits
	.globl	atomic_umax_8_relaxed
	.p2align	2
	.type	atomic_umax_8_relaxed,@function
atomic_umax_8_relaxed:
	.cfi_startproc
	and	w9, w1, #0xff
.LBB186_1:
	ldxrb	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, hi
	stxrb	w11, w10, [x0]
	cbnz	w11, .LBB186_1
	mov	w0, w8
	ret
.Lfunc_end186:
	.size	atomic_umax_8_relaxed, .Lfunc_end186-atomic_umax_8_relaxed
	.cfi_endproc

	.section	.text.atomic_umax_8_release,"ax",@progbits
	.globl	atomic_umax_8_release
	.p2align	2
	.type	atomic_umax_8_release,@function
atomic_umax_8_release:
	.cfi_startproc
	and	w9, w1, #0xff
.LBB187_1:
	ldxrb	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, hi
	stlxrb	w11, w10, [x0]
	cbnz	w11, .LBB187_1
	mov	w0, w8
	ret
.Lfunc_end187:
	.size	atomic_umax_8_release, .Lfunc_end187-atomic_umax_8_release
	.cfi_endproc

	.section	.text.atomic_umax_8_seqcst,"ax",@progbits
	.globl	atomic_umax_8_seqcst
	.p2align	2
	.type	atomic_umax_8_seqcst,@function
atomic_umax_8_seqcst:
	.cfi_startproc
	and	w9, w1, #0xff
.LBB188_1:
	ldaxrb	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, hi
	stlxrb	w11, w10, [x0]
	cbnz	w11, .LBB188_1
	mov	w0, w8
	ret
.Lfunc_end188:
	.size	atomic_umax_8_seqcst, .Lfunc_end188-atomic_umax_8_seqcst
	.cfi_endproc

	.section	.text.atomic_umin_128_acqrel,"ax",@progbits
	.globl	atomic_umin_128_acqrel
	.p2align	2
	.type	atomic_umin_128_acqrel,@function
atomic_umin_128_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB189_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, hs
	csel	x10, x0, x2, hs
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB189_1
	ret
.Lfunc_end189:
	.size	atomic_umin_128_acqrel, .Lfunc_end189-atomic_umin_128_acqrel
	.cfi_endproc

	.section	.text.atomic_umin_128_acquire,"ax",@progbits
	.globl	atomic_umin_128_acquire
	.p2align	2
	.type	atomic_umin_128_acquire,@function
atomic_umin_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB190_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, hs
	csel	x10, x0, x2, hs
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB190_1
	ret
.Lfunc_end190:
	.size	atomic_umin_128_acquire, .Lfunc_end190-atomic_umin_128_acquire
	.cfi_endproc

	.section	.text.atomic_umin_128_relaxed,"ax",@progbits
	.globl	atomic_umin_128_relaxed
	.p2align	2
	.type	atomic_umin_128_relaxed,@function
atomic_umin_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB191_1:
	ldxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, hs
	csel	x10, x0, x2, hs
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB191_1
	ret
.Lfunc_end191:
	.size	atomic_umin_128_relaxed, .Lfunc_end191-atomic_umin_128_relaxed
	.cfi_endproc

	.section	.text.atomic_umin_128_release,"ax",@progbits
	.globl	atomic_umin_128_release
	.p2align	2
	.type	atomic_umin_128_release,@function
atomic_umin_128_release:
	.cfi_startproc
	mov	x8, x0
.LBB192_1:
	ldxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, hs
	csel	x10, x0, x2, hs
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB192_1
	ret
.Lfunc_end192:
	.size	atomic_umin_128_release, .Lfunc_end192-atomic_umin_128_release
	.cfi_endproc

	.section	.text.atomic_umin_128_seqcst,"ax",@progbits
	.globl	atomic_umin_128_seqcst
	.p2align	2
	.type	atomic_umin_128_seqcst,@function
atomic_umin_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB193_1:
	ldaxp	x0, x1, [x8]
	cmp	x2, x0
	sbcs	xzr, x3, x1
	csel	x9, x1, x3, hs
	csel	x10, x0, x2, hs
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB193_1
	ret
.Lfunc_end193:
	.size	atomic_umin_128_seqcst, .Lfunc_end193-atomic_umin_128_seqcst
	.cfi_endproc

	.section	.text.atomic_umin_16_acqrel,"ax",@progbits
	.globl	atomic_umin_16_acqrel
	.p2align	2
	.type	atomic_umin_16_acqrel,@function
atomic_umin_16_acqrel:
	.cfi_startproc
	and	w9, w1, #0xffff
.LBB194_1:
	ldaxrh	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, ls
	stlxrh	w11, w10, [x0]
	cbnz	w11, .LBB194_1
	mov	w0, w8
	ret
.Lfunc_end194:
	.size	atomic_umin_16_acqrel, .Lfunc_end194-atomic_umin_16_acqrel
	.cfi_endproc

	.section	.text.atomic_umin_16_acquire,"ax",@progbits
	.globl	atomic_umin_16_acquire
	.p2align	2
	.type	atomic_umin_16_acquire,@function
atomic_umin_16_acquire:
	.cfi_startproc
	and	w9, w1, #0xffff
.LBB195_1:
	ldaxrh	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, ls
	stxrh	w11, w10, [x0]
	cbnz	w11, .LBB195_1
	mov	w0, w8
	ret
.Lfunc_end195:
	.size	atomic_umin_16_acquire, .Lfunc_end195-atomic_umin_16_acquire
	.cfi_endproc

	.section	.text.atomic_umin_16_relaxed,"ax",@progbits
	.globl	atomic_umin_16_relaxed
	.p2align	2
	.type	atomic_umin_16_relaxed,@function
atomic_umin_16_relaxed:
	.cfi_startproc
	and	w9, w1, #0xffff
.LBB196_1:
	ldxrh	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, ls
	stxrh	w11, w10, [x0]
	cbnz	w11, .LBB196_1
	mov	w0, w8
	ret
.Lfunc_end196:
	.size	atomic_umin_16_relaxed, .Lfunc_end196-atomic_umin_16_relaxed
	.cfi_endproc

	.section	.text.atomic_umin_16_release,"ax",@progbits
	.globl	atomic_umin_16_release
	.p2align	2
	.type	atomic_umin_16_release,@function
atomic_umin_16_release:
	.cfi_startproc
	and	w9, w1, #0xffff
.LBB197_1:
	ldxrh	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, ls
	stlxrh	w11, w10, [x0]
	cbnz	w11, .LBB197_1
	mov	w0, w8
	ret
.Lfunc_end197:
	.size	atomic_umin_16_release, .Lfunc_end197-atomic_umin_16_release
	.cfi_endproc

	.section	.text.atomic_umin_16_seqcst,"ax",@progbits
	.globl	atomic_umin_16_seqcst
	.p2align	2
	.type	atomic_umin_16_seqcst,@function
atomic_umin_16_seqcst:
	.cfi_startproc
	and	w9, w1, #0xffff
.LBB198_1:
	ldaxrh	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, ls
	stlxrh	w11, w10, [x0]
	cbnz	w11, .LBB198_1
	mov	w0, w8
	ret
.Lfunc_end198:
	.size	atomic_umin_16_seqcst, .Lfunc_end198-atomic_umin_16_seqcst
	.cfi_endproc

	.section	.text.atomic_umin_32_acqrel,"ax",@progbits
	.globl	atomic_umin_32_acqrel
	.p2align	2
	.type	atomic_umin_32_acqrel,@function
atomic_umin_32_acqrel:
	.cfi_startproc
.LBB199_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, ls
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB199_1
	mov	w0, w8
	ret
.Lfunc_end199:
	.size	atomic_umin_32_acqrel, .Lfunc_end199-atomic_umin_32_acqrel
	.cfi_endproc

	.section	.text.atomic_umin_32_acquire,"ax",@progbits
	.globl	atomic_umin_32_acquire
	.p2align	2
	.type	atomic_umin_32_acquire,@function
atomic_umin_32_acquire:
	.cfi_startproc
.LBB200_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, ls
	stxr	w10, w9, [x0]
	cbnz	w10, .LBB200_1
	mov	w0, w8
	ret
.Lfunc_end200:
	.size	atomic_umin_32_acquire, .Lfunc_end200-atomic_umin_32_acquire
	.cfi_endproc

	.section	.text.atomic_umin_32_relaxed,"ax",@progbits
	.globl	atomic_umin_32_relaxed
	.p2align	2
	.type	atomic_umin_32_relaxed,@function
atomic_umin_32_relaxed:
	.cfi_startproc
.LBB201_1:
	ldxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, ls
	stxr	w10, w9, [x0]
	cbnz	w10, .LBB201_1
	mov	w0, w8
	ret
.Lfunc_end201:
	.size	atomic_umin_32_relaxed, .Lfunc_end201-atomic_umin_32_relaxed
	.cfi_endproc

	.section	.text.atomic_umin_32_release,"ax",@progbits
	.globl	atomic_umin_32_release
	.p2align	2
	.type	atomic_umin_32_release,@function
atomic_umin_32_release:
	.cfi_startproc
.LBB202_1:
	ldxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, ls
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB202_1
	mov	w0, w8
	ret
.Lfunc_end202:
	.size	atomic_umin_32_release, .Lfunc_end202-atomic_umin_32_release
	.cfi_endproc

	.section	.text.atomic_umin_32_seqcst,"ax",@progbits
	.globl	atomic_umin_32_seqcst
	.p2align	2
	.type	atomic_umin_32_seqcst,@function
atomic_umin_32_seqcst:
	.cfi_startproc
.LBB203_1:
	ldaxr	w8, [x0]
	cmp	w8, w1
	csel	w9, w8, w1, ls
	stlxr	w10, w9, [x0]
	cbnz	w10, .LBB203_1
	mov	w0, w8
	ret
.Lfunc_end203:
	.size	atomic_umin_32_seqcst, .Lfunc_end203-atomic_umin_32_seqcst
	.cfi_endproc

	.section	.text.atomic_umin_64_acqrel,"ax",@progbits
	.globl	atomic_umin_64_acqrel
	.p2align	2
	.type	atomic_umin_64_acqrel,@function
atomic_umin_64_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB204_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, ls
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB204_1
	ret
.Lfunc_end204:
	.size	atomic_umin_64_acqrel, .Lfunc_end204-atomic_umin_64_acqrel
	.cfi_endproc

	.section	.text.atomic_umin_64_acquire,"ax",@progbits
	.globl	atomic_umin_64_acquire
	.p2align	2
	.type	atomic_umin_64_acquire,@function
atomic_umin_64_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB205_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, ls
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB205_1
	ret
.Lfunc_end205:
	.size	atomic_umin_64_acquire, .Lfunc_end205-atomic_umin_64_acquire
	.cfi_endproc

	.section	.text.atomic_umin_64_relaxed,"ax",@progbits
	.globl	atomic_umin_64_relaxed
	.p2align	2
	.type	atomic_umin_64_relaxed,@function
atomic_umin_64_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB206_1:
	ldxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, ls
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB206_1
	ret
.Lfunc_end206:
	.size	atomic_umin_64_relaxed, .Lfunc_end206-atomic_umin_64_relaxed
	.cfi_endproc

	.section	.text.atomic_umin_64_release,"ax",@progbits
	.globl	atomic_umin_64_release
	.p2align	2
	.type	atomic_umin_64_release,@function
atomic_umin_64_release:
	.cfi_startproc
	mov	x8, x0
.LBB207_1:
	ldxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, ls
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB207_1
	ret
.Lfunc_end207:
	.size	atomic_umin_64_release, .Lfunc_end207-atomic_umin_64_release
	.cfi_endproc

	.section	.text.atomic_umin_64_seqcst,"ax",@progbits
	.globl	atomic_umin_64_seqcst
	.p2align	2
	.type	atomic_umin_64_seqcst,@function
atomic_umin_64_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB208_1:
	ldaxr	x0, [x8]
	cmp	x0, x1
	csel	x9, x0, x1, ls
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB208_1
	ret
.Lfunc_end208:
	.size	atomic_umin_64_seqcst, .Lfunc_end208-atomic_umin_64_seqcst
	.cfi_endproc

	.section	.text.atomic_umin_8_acqrel,"ax",@progbits
	.globl	atomic_umin_8_acqrel
	.p2align	2
	.type	atomic_umin_8_acqrel,@function
atomic_umin_8_acqrel:
	.cfi_startproc
	and	w9, w1, #0xff
.LBB209_1:
	ldaxrb	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, ls
	stlxrb	w11, w10, [x0]
	cbnz	w11, .LBB209_1
	mov	w0, w8
	ret
.Lfunc_end209:
	.size	atomic_umin_8_acqrel, .Lfunc_end209-atomic_umin_8_acqrel
	.cfi_endproc

	.section	.text.atomic_umin_8_acquire,"ax",@progbits
	.globl	atomic_umin_8_acquire
	.p2align	2
	.type	atomic_umin_8_acquire,@function
atomic_umin_8_acquire:
	.cfi_startproc
	and	w9, w1, #0xff
.LBB210_1:
	ldaxrb	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, ls
	stxrb	w11, w10, [x0]
	cbnz	w11, .LBB210_1
	mov	w0, w8
	ret
.Lfunc_end210:
	.size	atomic_umin_8_acquire, .Lfunc_end210-atomic_umin_8_acquire
	.cfi_endproc

	.section	.text.atomic_umin_8_relaxed,"ax",@progbits
	.globl	atomic_umin_8_relaxed
	.p2align	2
	.type	atomic_umin_8_relaxed,@function
atomic_umin_8_relaxed:
	.cfi_startproc
	and	w9, w1, #0xff
.LBB211_1:
	ldxrb	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, ls
	stxrb	w11, w10, [x0]
	cbnz	w11, .LBB211_1
	mov	w0, w8
	ret
.Lfunc_end211:
	.size	atomic_umin_8_relaxed, .Lfunc_end211-atomic_umin_8_relaxed
	.cfi_endproc

	.section	.text.atomic_umin_8_release,"ax",@progbits
	.globl	atomic_umin_8_release
	.p2align	2
	.type	atomic_umin_8_release,@function
atomic_umin_8_release:
	.cfi_startproc
	and	w9, w1, #0xff
.LBB212_1:
	ldxrb	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, ls
	stlxrb	w11, w10, [x0]
	cbnz	w11, .LBB212_1
	mov	w0, w8
	ret
.Lfunc_end212:
	.size	atomic_umin_8_release, .Lfunc_end212-atomic_umin_8_release
	.cfi_endproc

	.section	.text.atomic_umin_8_seqcst,"ax",@progbits
	.globl	atomic_umin_8_seqcst
	.p2align	2
	.type	atomic_umin_8_seqcst,@function
atomic_umin_8_seqcst:
	.cfi_startproc
	and	w9, w1, #0xff
.LBB213_1:
	ldaxrb	w8, [x0]
	cmp	w8, w9
	csel	w10, w8, w9, ls
	stlxrb	w11, w10, [x0]
	cbnz	w11, .LBB213_1
	mov	w0, w8
	ret
.Lfunc_end213:
	.size	atomic_umin_8_seqcst, .Lfunc_end213-atomic_umin_8_seqcst
	.cfi_endproc

	.section	.text.atomic_xadd_128_acqrel,"ax",@progbits
	.globl	atomic_xadd_128_acqrel
	.p2align	2
	.type	atomic_xadd_128_acqrel,@function
atomic_xadd_128_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB214_1:
	ldaxp	x0, x1, [x8]
	adds	x9, x0, x2
	adc	x10, x1, x3
	stlxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB214_1
	ret
.Lfunc_end214:
	.size	atomic_xadd_128_acqrel, .Lfunc_end214-atomic_xadd_128_acqrel
	.cfi_endproc

	.section	.text.atomic_xadd_128_acquire,"ax",@progbits
	.globl	atomic_xadd_128_acquire
	.p2align	2
	.type	atomic_xadd_128_acquire,@function
atomic_xadd_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB215_1:
	ldaxp	x0, x1, [x8]
	adds	x9, x0, x2
	adc	x10, x1, x3
	stxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB215_1
	ret
.Lfunc_end215:
	.size	atomic_xadd_128_acquire, .Lfunc_end215-atomic_xadd_128_acquire
	.cfi_endproc

	.section	.text.atomic_xadd_128_relaxed,"ax",@progbits
	.globl	atomic_xadd_128_relaxed
	.p2align	2
	.type	atomic_xadd_128_relaxed,@function
atomic_xadd_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB216_1:
	ldxp	x0, x1, [x8]
	adds	x9, x0, x2
	adc	x10, x1, x3
	stxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB216_1
	ret
.Lfunc_end216:
	.size	atomic_xadd_128_relaxed, .Lfunc_end216-atomic_xadd_128_relaxed
	.cfi_endproc

	.section	.text.atomic_xadd_128_release,"ax",@progbits
	.globl	atomic_xadd_128_release
	.p2align	2
	.type	atomic_xadd_128_release,@function
atomic_xadd_128_release:
	.cfi_startproc
	mov	x8, x0
.LBB217_1:
	ldxp	x0, x1, [x8]
	adds	x9, x0, x2
	adc	x10, x1, x3
	stlxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB217_1
	ret
.Lfunc_end217:
	.size	atomic_xadd_128_release, .Lfunc_end217-atomic_xadd_128_release
	.cfi_endproc

	.section	.text.atomic_xadd_128_seqcst,"ax",@progbits
	.globl	atomic_xadd_128_seqcst
	.p2align	2
	.type	atomic_xadd_128_seqcst,@function
atomic_xadd_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB218_1:
	ldaxp	x0, x1, [x8]
	adds	x9, x0, x2
	adc	x10, x1, x3
	stlxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB218_1
	ret
.Lfunc_end218:
	.size	atomic_xadd_128_seqcst, .Lfunc_end218-atomic_xadd_128_seqcst
	.cfi_endproc

	.section	.text.atomic_xadd_16_acqrel,"ax",@progbits
	.globl	atomic_xadd_16_acqrel
	.p2align	2
	.type	atomic_xadd_16_acqrel,@function
atomic_xadd_16_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end219:
	.size	atomic_xadd_16_acqrel, .Lfunc_end219-atomic_xadd_16_acqrel
	.cfi_endproc

	.section	.text.atomic_xadd_16_acquire,"ax",@progbits
	.globl	atomic_xadd_16_acquire
	.p2align	2
	.type	atomic_xadd_16_acquire,@function
atomic_xadd_16_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd2_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end220:
	.size	atomic_xadd_16_acquire, .Lfunc_end220-atomic_xadd_16_acquire
	.cfi_endproc

	.section	.text.atomic_xadd_16_relaxed,"ax",@progbits
	.globl	atomic_xadd_16_relaxed
	.p2align	2
	.type	atomic_xadd_16_relaxed,@function
atomic_xadd_16_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd2_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end221:
	.size	atomic_xadd_16_relaxed, .Lfunc_end221-atomic_xadd_16_relaxed
	.cfi_endproc

	.section	.text.atomic_xadd_16_release,"ax",@progbits
	.globl	atomic_xadd_16_release
	.p2align	2
	.type	atomic_xadd_16_release,@function
atomic_xadd_16_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd2_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end222:
	.size	atomic_xadd_16_release, .Lfunc_end222-atomic_xadd_16_release
	.cfi_endproc

	.section	.text.atomic_xadd_16_seqcst,"ax",@progbits
	.globl	atomic_xadd_16_seqcst
	.p2align	2
	.type	atomic_xadd_16_seqcst,@function
atomic_xadd_16_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end223:
	.size	atomic_xadd_16_seqcst, .Lfunc_end223-atomic_xadd_16_seqcst
	.cfi_endproc

	.section	.text.atomic_xadd_32_acqrel,"ax",@progbits
	.globl	atomic_xadd_32_acqrel
	.p2align	2
	.type	atomic_xadd_32_acqrel,@function
atomic_xadd_32_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end224:
	.size	atomic_xadd_32_acqrel, .Lfunc_end224-atomic_xadd_32_acqrel
	.cfi_endproc

	.section	.text.atomic_xadd_32_acquire,"ax",@progbits
	.globl	atomic_xadd_32_acquire
	.p2align	2
	.type	atomic_xadd_32_acquire,@function
atomic_xadd_32_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd4_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end225:
	.size	atomic_xadd_32_acquire, .Lfunc_end225-atomic_xadd_32_acquire
	.cfi_endproc

	.section	.text.atomic_xadd_32_relaxed,"ax",@progbits
	.globl	atomic_xadd_32_relaxed
	.p2align	2
	.type	atomic_xadd_32_relaxed,@function
atomic_xadd_32_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd4_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end226:
	.size	atomic_xadd_32_relaxed, .Lfunc_end226-atomic_xadd_32_relaxed
	.cfi_endproc

	.section	.text.atomic_xadd_32_release,"ax",@progbits
	.globl	atomic_xadd_32_release
	.p2align	2
	.type	atomic_xadd_32_release,@function
atomic_xadd_32_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd4_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end227:
	.size	atomic_xadd_32_release, .Lfunc_end227-atomic_xadd_32_release
	.cfi_endproc

	.section	.text.atomic_xadd_32_seqcst,"ax",@progbits
	.globl	atomic_xadd_32_seqcst
	.p2align	2
	.type	atomic_xadd_32_seqcst,@function
atomic_xadd_32_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end228:
	.size	atomic_xadd_32_seqcst, .Lfunc_end228-atomic_xadd_32_seqcst
	.cfi_endproc

	.section	.text.atomic_xadd_64_acqrel,"ax",@progbits
	.globl	atomic_xadd_64_acqrel
	.p2align	2
	.type	atomic_xadd_64_acqrel,@function
atomic_xadd_64_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldadd8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end229:
	.size	atomic_xadd_64_acqrel, .Lfunc_end229-atomic_xadd_64_acqrel
	.cfi_endproc

	.section	.text.atomic_xadd_64_acquire,"ax",@progbits
	.globl	atomic_xadd_64_acquire
	.p2align	2
	.type	atomic_xadd_64_acquire,@function
atomic_xadd_64_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldadd8_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end230:
	.size	atomic_xadd_64_acquire, .Lfunc_end230-atomic_xadd_64_acquire
	.cfi_endproc

	.section	.text.atomic_xadd_64_relaxed,"ax",@progbits
	.globl	atomic_xadd_64_relaxed
	.p2align	2
	.type	atomic_xadd_64_relaxed,@function
atomic_xadd_64_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldadd8_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end231:
	.size	atomic_xadd_64_relaxed, .Lfunc_end231-atomic_xadd_64_relaxed
	.cfi_endproc

	.section	.text.atomic_xadd_64_release,"ax",@progbits
	.globl	atomic_xadd_64_release
	.p2align	2
	.type	atomic_xadd_64_release,@function
atomic_xadd_64_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldadd8_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end232:
	.size	atomic_xadd_64_release, .Lfunc_end232-atomic_xadd_64_release
	.cfi_endproc

	.section	.text.atomic_xadd_64_seqcst,"ax",@progbits
	.globl	atomic_xadd_64_seqcst
	.p2align	2
	.type	atomic_xadd_64_seqcst,@function
atomic_xadd_64_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldadd8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end233:
	.size	atomic_xadd_64_seqcst, .Lfunc_end233-atomic_xadd_64_seqcst
	.cfi_endproc

	.section	.text.atomic_xadd_8_acqrel,"ax",@progbits
	.globl	atomic_xadd_8_acqrel
	.p2align	2
	.type	atomic_xadd_8_acqrel,@function
atomic_xadd_8_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end234:
	.size	atomic_xadd_8_acqrel, .Lfunc_end234-atomic_xadd_8_acqrel
	.cfi_endproc

	.section	.text.atomic_xadd_8_acquire,"ax",@progbits
	.globl	atomic_xadd_8_acquire
	.p2align	2
	.type	atomic_xadd_8_acquire,@function
atomic_xadd_8_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd1_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end235:
	.size	atomic_xadd_8_acquire, .Lfunc_end235-atomic_xadd_8_acquire
	.cfi_endproc

	.section	.text.atomic_xadd_8_relaxed,"ax",@progbits
	.globl	atomic_xadd_8_relaxed
	.p2align	2
	.type	atomic_xadd_8_relaxed,@function
atomic_xadd_8_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd1_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end236:
	.size	atomic_xadd_8_relaxed, .Lfunc_end236-atomic_xadd_8_relaxed
	.cfi_endproc

	.section	.text.atomic_xadd_8_release,"ax",@progbits
	.globl	atomic_xadd_8_release
	.p2align	2
	.type	atomic_xadd_8_release,@function
atomic_xadd_8_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd1_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end237:
	.size	atomic_xadd_8_release, .Lfunc_end237-atomic_xadd_8_release
	.cfi_endproc

	.section	.text.atomic_xadd_8_seqcst,"ax",@progbits
	.globl	atomic_xadd_8_seqcst
	.p2align	2
	.type	atomic_xadd_8_seqcst,@function
atomic_xadd_8_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end238:
	.size	atomic_xadd_8_seqcst, .Lfunc_end238-atomic_xadd_8_seqcst
	.cfi_endproc

	.section	.text.atomic_xchg_128_acqrel,"ax",@progbits
	.globl	atomic_xchg_128_acqrel
	.p2align	2
	.type	atomic_xchg_128_acqrel,@function
atomic_xchg_128_acqrel:
	.cfi_startproc
.LBB239_1:
	ldaxp	x8, x1, [x0]
	stlxp	w9, x2, x3, [x0]
	cbnz	w9, .LBB239_1
	mov	x0, x8
	ret
.Lfunc_end239:
	.size	atomic_xchg_128_acqrel, .Lfunc_end239-atomic_xchg_128_acqrel
	.cfi_endproc

	.section	.text.atomic_xchg_128_acquire,"ax",@progbits
	.globl	atomic_xchg_128_acquire
	.p2align	2
	.type	atomic_xchg_128_acquire,@function
atomic_xchg_128_acquire:
	.cfi_startproc
.LBB240_1:
	ldaxp	x8, x1, [x0]
	stxp	w9, x2, x3, [x0]
	cbnz	w9, .LBB240_1
	mov	x0, x8
	ret
.Lfunc_end240:
	.size	atomic_xchg_128_acquire, .Lfunc_end240-atomic_xchg_128_acquire
	.cfi_endproc

	.section	.text.atomic_xchg_128_relaxed,"ax",@progbits
	.globl	atomic_xchg_128_relaxed
	.p2align	2
	.type	atomic_xchg_128_relaxed,@function
atomic_xchg_128_relaxed:
	.cfi_startproc
.LBB241_1:
	ldxp	x8, x1, [x0]
	stxp	w9, x2, x3, [x0]
	cbnz	w9, .LBB241_1
	mov	x0, x8
	ret
.Lfunc_end241:
	.size	atomic_xchg_128_relaxed, .Lfunc_end241-atomic_xchg_128_relaxed
	.cfi_endproc

	.section	.text.atomic_xchg_128_release,"ax",@progbits
	.globl	atomic_xchg_128_release
	.p2align	2
	.type	atomic_xchg_128_release,@function
atomic_xchg_128_release:
	.cfi_startproc
.LBB242_1:
	ldxp	x8, x1, [x0]
	stlxp	w9, x2, x3, [x0]
	cbnz	w9, .LBB242_1
	mov	x0, x8
	ret
.Lfunc_end242:
	.size	atomic_xchg_128_release, .Lfunc_end242-atomic_xchg_128_release
	.cfi_endproc

	.section	.text.atomic_xchg_128_seqcst,"ax",@progbits
	.globl	atomic_xchg_128_seqcst
	.p2align	2
	.type	atomic_xchg_128_seqcst,@function
atomic_xchg_128_seqcst:
	.cfi_startproc
.LBB243_1:
	ldaxp	x8, x1, [x0]
	stlxp	w9, x2, x3, [x0]
	cbnz	w9, .LBB243_1
	mov	x0, x8
	ret
.Lfunc_end243:
	.size	atomic_xchg_128_seqcst, .Lfunc_end243-atomic_xchg_128_seqcst
	.cfi_endproc

	.section	.text.atomic_xchg_16_acqrel,"ax",@progbits
	.globl	atomic_xchg_16_acqrel
	.p2align	2
	.type	atomic_xchg_16_acqrel,@function
atomic_xchg_16_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end244:
	.size	atomic_xchg_16_acqrel, .Lfunc_end244-atomic_xchg_16_acqrel
	.cfi_endproc

	.section	.text.atomic_xchg_16_acquire,"ax",@progbits
	.globl	atomic_xchg_16_acquire
	.p2align	2
	.type	atomic_xchg_16_acquire,@function
atomic_xchg_16_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp2_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end245:
	.size	atomic_xchg_16_acquire, .Lfunc_end245-atomic_xchg_16_acquire
	.cfi_endproc

	.section	.text.atomic_xchg_16_relaxed,"ax",@progbits
	.globl	atomic_xchg_16_relaxed
	.p2align	2
	.type	atomic_xchg_16_relaxed,@function
atomic_xchg_16_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp2_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end246:
	.size	atomic_xchg_16_relaxed, .Lfunc_end246-atomic_xchg_16_relaxed
	.cfi_endproc

	.section	.text.atomic_xchg_16_release,"ax",@progbits
	.globl	atomic_xchg_16_release
	.p2align	2
	.type	atomic_xchg_16_release,@function
atomic_xchg_16_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp2_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end247:
	.size	atomic_xchg_16_release, .Lfunc_end247-atomic_xchg_16_release
	.cfi_endproc

	.section	.text.atomic_xchg_16_seqcst,"ax",@progbits
	.globl	atomic_xchg_16_seqcst
	.p2align	2
	.type	atomic_xchg_16_seqcst,@function
atomic_xchg_16_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end248:
	.size	atomic_xchg_16_seqcst, .Lfunc_end248-atomic_xchg_16_seqcst
	.cfi_endproc

	.section	.text.atomic_xchg_32_acqrel,"ax",@progbits
	.globl	atomic_xchg_32_acqrel
	.p2align	2
	.type	atomic_xchg_32_acqrel,@function
atomic_xchg_32_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end249:
	.size	atomic_xchg_32_acqrel, .Lfunc_end249-atomic_xchg_32_acqrel
	.cfi_endproc

	.section	.text.atomic_xchg_32_acquire,"ax",@progbits
	.globl	atomic_xchg_32_acquire
	.p2align	2
	.type	atomic_xchg_32_acquire,@function
atomic_xchg_32_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp4_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end250:
	.size	atomic_xchg_32_acquire, .Lfunc_end250-atomic_xchg_32_acquire
	.cfi_endproc

	.section	.text.atomic_xchg_32_relaxed,"ax",@progbits
	.globl	atomic_xchg_32_relaxed
	.p2align	2
	.type	atomic_xchg_32_relaxed,@function
atomic_xchg_32_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp4_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end251:
	.size	atomic_xchg_32_relaxed, .Lfunc_end251-atomic_xchg_32_relaxed
	.cfi_endproc

	.section	.text.atomic_xchg_32_release,"ax",@progbits
	.globl	atomic_xchg_32_release
	.p2align	2
	.type	atomic_xchg_32_release,@function
atomic_xchg_32_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp4_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end252:
	.size	atomic_xchg_32_release, .Lfunc_end252-atomic_xchg_32_release
	.cfi_endproc

	.section	.text.atomic_xchg_32_seqcst,"ax",@progbits
	.globl	atomic_xchg_32_seqcst
	.p2align	2
	.type	atomic_xchg_32_seqcst,@function
atomic_xchg_32_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end253:
	.size	atomic_xchg_32_seqcst, .Lfunc_end253-atomic_xchg_32_seqcst
	.cfi_endproc

	.section	.text.atomic_xchg_64_acqrel,"ax",@progbits
	.globl	atomic_xchg_64_acqrel
	.p2align	2
	.type	atomic_xchg_64_acqrel,@function
atomic_xchg_64_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_swp8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end254:
	.size	atomic_xchg_64_acqrel, .Lfunc_end254-atomic_xchg_64_acqrel
	.cfi_endproc

	.section	.text.atomic_xchg_64_acquire,"ax",@progbits
	.globl	atomic_xchg_64_acquire
	.p2align	2
	.type	atomic_xchg_64_acquire,@function
atomic_xchg_64_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_swp8_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end255:
	.size	atomic_xchg_64_acquire, .Lfunc_end255-atomic_xchg_64_acquire
	.cfi_endproc

	.section	.text.atomic_xchg_64_relaxed,"ax",@progbits
	.globl	atomic_xchg_64_relaxed
	.p2align	2
	.type	atomic_xchg_64_relaxed,@function
atomic_xchg_64_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_swp8_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end256:
	.size	atomic_xchg_64_relaxed, .Lfunc_end256-atomic_xchg_64_relaxed
	.cfi_endproc

	.section	.text.atomic_xchg_64_release,"ax",@progbits
	.globl	atomic_xchg_64_release
	.p2align	2
	.type	atomic_xchg_64_release,@function
atomic_xchg_64_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_swp8_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end257:
	.size	atomic_xchg_64_release, .Lfunc_end257-atomic_xchg_64_release
	.cfi_endproc

	.section	.text.atomic_xchg_64_seqcst,"ax",@progbits
	.globl	atomic_xchg_64_seqcst
	.p2align	2
	.type	atomic_xchg_64_seqcst,@function
atomic_xchg_64_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_swp8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end258:
	.size	atomic_xchg_64_seqcst, .Lfunc_end258-atomic_xchg_64_seqcst
	.cfi_endproc

	.section	.text.atomic_xchg_8_acqrel,"ax",@progbits
	.globl	atomic_xchg_8_acqrel
	.p2align	2
	.type	atomic_xchg_8_acqrel,@function
atomic_xchg_8_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end259:
	.size	atomic_xchg_8_acqrel, .Lfunc_end259-atomic_xchg_8_acqrel
	.cfi_endproc

	.section	.text.atomic_xchg_8_acquire,"ax",@progbits
	.globl	atomic_xchg_8_acquire
	.p2align	2
	.type	atomic_xchg_8_acquire,@function
atomic_xchg_8_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp1_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end260:
	.size	atomic_xchg_8_acquire, .Lfunc_end260-atomic_xchg_8_acquire
	.cfi_endproc

	.section	.text.atomic_xchg_8_relaxed,"ax",@progbits
	.globl	atomic_xchg_8_relaxed
	.p2align	2
	.type	atomic_xchg_8_relaxed,@function
atomic_xchg_8_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp1_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end261:
	.size	atomic_xchg_8_relaxed, .Lfunc_end261-atomic_xchg_8_relaxed
	.cfi_endproc

	.section	.text.atomic_xchg_8_release,"ax",@progbits
	.globl	atomic_xchg_8_release
	.p2align	2
	.type	atomic_xchg_8_release,@function
atomic_xchg_8_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp1_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end262:
	.size	atomic_xchg_8_release, .Lfunc_end262-atomic_xchg_8_release
	.cfi_endproc

	.section	.text.atomic_xchg_8_seqcst,"ax",@progbits
	.globl	atomic_xchg_8_seqcst
	.p2align	2
	.type	atomic_xchg_8_seqcst,@function
atomic_xchg_8_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_swp1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end263:
	.size	atomic_xchg_8_seqcst, .Lfunc_end263-atomic_xchg_8_seqcst
	.cfi_endproc

	.section	.text.atomic_xor_128_acqrel,"ax",@progbits
	.globl	atomic_xor_128_acqrel
	.p2align	2
	.type	atomic_xor_128_acqrel,@function
atomic_xor_128_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB264_1:
	ldaxp	x0, x1, [x8]
	eor	x9, x1, x3
	eor	x10, x0, x2
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB264_1
	ret
.Lfunc_end264:
	.size	atomic_xor_128_acqrel, .Lfunc_end264-atomic_xor_128_acqrel
	.cfi_endproc

	.section	.text.atomic_xor_128_acquire,"ax",@progbits
	.globl	atomic_xor_128_acquire
	.p2align	2
	.type	atomic_xor_128_acquire,@function
atomic_xor_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB265_1:
	ldaxp	x0, x1, [x8]
	eor	x9, x1, x3
	eor	x10, x0, x2
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB265_1
	ret
.Lfunc_end265:
	.size	atomic_xor_128_acquire, .Lfunc_end265-atomic_xor_128_acquire
	.cfi_endproc

	.section	.text.atomic_xor_128_relaxed,"ax",@progbits
	.globl	atomic_xor_128_relaxed
	.p2align	2
	.type	atomic_xor_128_relaxed,@function
atomic_xor_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB266_1:
	ldxp	x0, x1, [x8]
	eor	x9, x1, x3
	eor	x10, x0, x2
	stxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB266_1
	ret
.Lfunc_end266:
	.size	atomic_xor_128_relaxed, .Lfunc_end266-atomic_xor_128_relaxed
	.cfi_endproc

	.section	.text.atomic_xor_128_release,"ax",@progbits
	.globl	atomic_xor_128_release
	.p2align	2
	.type	atomic_xor_128_release,@function
atomic_xor_128_release:
	.cfi_startproc
	mov	x8, x0
.LBB267_1:
	ldxp	x0, x1, [x8]
	eor	x9, x1, x3
	eor	x10, x0, x2
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB267_1
	ret
.Lfunc_end267:
	.size	atomic_xor_128_release, .Lfunc_end267-atomic_xor_128_release
	.cfi_endproc

	.section	.text.atomic_xor_128_seqcst,"ax",@progbits
	.globl	atomic_xor_128_seqcst
	.p2align	2
	.type	atomic_xor_128_seqcst,@function
atomic_xor_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB268_1:
	ldaxp	x0, x1, [x8]
	eor	x9, x1, x3
	eor	x10, x0, x2
	stlxp	w11, x10, x9, [x8]
	cbnz	w11, .LBB268_1
	ret
.Lfunc_end268:
	.size	atomic_xor_128_seqcst, .Lfunc_end268-atomic_xor_128_seqcst
	.cfi_endproc

	.section	.text.atomic_xor_16_acqrel,"ax",@progbits
	.globl	atomic_xor_16_acqrel
	.p2align	2
	.type	atomic_xor_16_acqrel,@function
atomic_xor_16_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end269:
	.size	atomic_xor_16_acqrel, .Lfunc_end269-atomic_xor_16_acqrel
	.cfi_endproc

	.section	.text.atomic_xor_16_acquire,"ax",@progbits
	.globl	atomic_xor_16_acquire
	.p2align	2
	.type	atomic_xor_16_acquire,@function
atomic_xor_16_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor2_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end270:
	.size	atomic_xor_16_acquire, .Lfunc_end270-atomic_xor_16_acquire
	.cfi_endproc

	.section	.text.atomic_xor_16_relaxed,"ax",@progbits
	.globl	atomic_xor_16_relaxed
	.p2align	2
	.type	atomic_xor_16_relaxed,@function
atomic_xor_16_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor2_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end271:
	.size	atomic_xor_16_relaxed, .Lfunc_end271-atomic_xor_16_relaxed
	.cfi_endproc

	.section	.text.atomic_xor_16_release,"ax",@progbits
	.globl	atomic_xor_16_release
	.p2align	2
	.type	atomic_xor_16_release,@function
atomic_xor_16_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor2_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end272:
	.size	atomic_xor_16_release, .Lfunc_end272-atomic_xor_16_release
	.cfi_endproc

	.section	.text.atomic_xor_16_seqcst,"ax",@progbits
	.globl	atomic_xor_16_seqcst
	.p2align	2
	.type	atomic_xor_16_seqcst,@function
atomic_xor_16_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end273:
	.size	atomic_xor_16_seqcst, .Lfunc_end273-atomic_xor_16_seqcst
	.cfi_endproc

	.section	.text.atomic_xor_32_acqrel,"ax",@progbits
	.globl	atomic_xor_32_acqrel
	.p2align	2
	.type	atomic_xor_32_acqrel,@function
atomic_xor_32_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end274:
	.size	atomic_xor_32_acqrel, .Lfunc_end274-atomic_xor_32_acqrel
	.cfi_endproc

	.section	.text.atomic_xor_32_acquire,"ax",@progbits
	.globl	atomic_xor_32_acquire
	.p2align	2
	.type	atomic_xor_32_acquire,@function
atomic_xor_32_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor4_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end275:
	.size	atomic_xor_32_acquire, .Lfunc_end275-atomic_xor_32_acquire
	.cfi_endproc

	.section	.text.atomic_xor_32_relaxed,"ax",@progbits
	.globl	atomic_xor_32_relaxed
	.p2align	2
	.type	atomic_xor_32_relaxed,@function
atomic_xor_32_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor4_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end276:
	.size	atomic_xor_32_relaxed, .Lfunc_end276-atomic_xor_32_relaxed
	.cfi_endproc

	.section	.text.atomic_xor_32_release,"ax",@progbits
	.globl	atomic_xor_32_release
	.p2align	2
	.type	atomic_xor_32_release,@function
atomic_xor_32_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor4_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end277:
	.size	atomic_xor_32_release, .Lfunc_end277-atomic_xor_32_release
	.cfi_endproc

	.section	.text.atomic_xor_32_seqcst,"ax",@progbits
	.globl	atomic_xor_32_seqcst
	.p2align	2
	.type	atomic_xor_32_seqcst,@function
atomic_xor_32_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end278:
	.size	atomic_xor_32_seqcst, .Lfunc_end278-atomic_xor_32_seqcst
	.cfi_endproc

	.section	.text.atomic_xor_64_acqrel,"ax",@progbits
	.globl	atomic_xor_64_acqrel
	.p2align	2
	.type	atomic_xor_64_acqrel,@function
atomic_xor_64_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldeor8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end279:
	.size	atomic_xor_64_acqrel, .Lfunc_end279-atomic_xor_64_acqrel
	.cfi_endproc

	.section	.text.atomic_xor_64_acquire,"ax",@progbits
	.globl	atomic_xor_64_acquire
	.p2align	2
	.type	atomic_xor_64_acquire,@function
atomic_xor_64_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldeor8_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end280:
	.size	atomic_xor_64_acquire, .Lfunc_end280-atomic_xor_64_acquire
	.cfi_endproc

	.section	.text.atomic_xor_64_relaxed,"ax",@progbits
	.globl	atomic_xor_64_relaxed
	.p2align	2
	.type	atomic_xor_64_relaxed,@function
atomic_xor_64_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldeor8_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end281:
	.size	atomic_xor_64_relaxed, .Lfunc_end281-atomic_xor_64_relaxed
	.cfi_endproc

	.section	.text.atomic_xor_64_release,"ax",@progbits
	.globl	atomic_xor_64_release
	.p2align	2
	.type	atomic_xor_64_release,@function
atomic_xor_64_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldeor8_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end282:
	.size	atomic_xor_64_release, .Lfunc_end282-atomic_xor_64_release
	.cfi_endproc

	.section	.text.atomic_xor_64_seqcst,"ax",@progbits
	.globl	atomic_xor_64_seqcst
	.p2align	2
	.type	atomic_xor_64_seqcst,@function
atomic_xor_64_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	bl	__aarch64_ldeor8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end283:
	.size	atomic_xor_64_seqcst, .Lfunc_end283-atomic_xor_64_seqcst
	.cfi_endproc

	.section	.text.atomic_xor_8_acqrel,"ax",@progbits
	.globl	atomic_xor_8_acqrel
	.p2align	2
	.type	atomic_xor_8_acqrel,@function
atomic_xor_8_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end284:
	.size	atomic_xor_8_acqrel, .Lfunc_end284-atomic_xor_8_acqrel
	.cfi_endproc

	.section	.text.atomic_xor_8_acquire,"ax",@progbits
	.globl	atomic_xor_8_acquire
	.p2align	2
	.type	atomic_xor_8_acquire,@function
atomic_xor_8_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor1_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end285:
	.size	atomic_xor_8_acquire, .Lfunc_end285-atomic_xor_8_acquire
	.cfi_endproc

	.section	.text.atomic_xor_8_relaxed,"ax",@progbits
	.globl	atomic_xor_8_relaxed
	.p2align	2
	.type	atomic_xor_8_relaxed,@function
atomic_xor_8_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor1_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end286:
	.size	atomic_xor_8_relaxed, .Lfunc_end286-atomic_xor_8_relaxed
	.cfi_endproc

	.section	.text.atomic_xor_8_release,"ax",@progbits
	.globl	atomic_xor_8_release
	.p2align	2
	.type	atomic_xor_8_release,@function
atomic_xor_8_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor1_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end287:
	.size	atomic_xor_8_release, .Lfunc_end287-atomic_xor_8_release
	.cfi_endproc

	.section	.text.atomic_xor_8_seqcst,"ax",@progbits
	.globl	atomic_xor_8_seqcst
	.p2align	2
	.type	atomic_xor_8_seqcst,@function
atomic_xor_8_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	mov	w0, w1
	mov	x1, x8
	bl	__aarch64_ldeor1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end288:
	.size	atomic_xor_8_seqcst, .Lfunc_end288-atomic_xor_8_seqcst
	.cfi_endproc

	.section	.text.atomic_xsub_128_acqrel,"ax",@progbits
	.globl	atomic_xsub_128_acqrel
	.p2align	2
	.type	atomic_xsub_128_acqrel,@function
atomic_xsub_128_acqrel:
	.cfi_startproc
	mov	x8, x0
.LBB289_1:
	ldaxp	x0, x1, [x8]
	subs	x9, x0, x2
	sbc	x10, x1, x3
	stlxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB289_1
	ret
.Lfunc_end289:
	.size	atomic_xsub_128_acqrel, .Lfunc_end289-atomic_xsub_128_acqrel
	.cfi_endproc

	.section	.text.atomic_xsub_128_acquire,"ax",@progbits
	.globl	atomic_xsub_128_acquire
	.p2align	2
	.type	atomic_xsub_128_acquire,@function
atomic_xsub_128_acquire:
	.cfi_startproc
	mov	x8, x0
.LBB290_1:
	ldaxp	x0, x1, [x8]
	subs	x9, x0, x2
	sbc	x10, x1, x3
	stxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB290_1
	ret
.Lfunc_end290:
	.size	atomic_xsub_128_acquire, .Lfunc_end290-atomic_xsub_128_acquire
	.cfi_endproc

	.section	.text.atomic_xsub_128_relaxed,"ax",@progbits
	.globl	atomic_xsub_128_relaxed
	.p2align	2
	.type	atomic_xsub_128_relaxed,@function
atomic_xsub_128_relaxed:
	.cfi_startproc
	mov	x8, x0
.LBB291_1:
	ldxp	x0, x1, [x8]
	subs	x9, x0, x2
	sbc	x10, x1, x3
	stxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB291_1
	ret
.Lfunc_end291:
	.size	atomic_xsub_128_relaxed, .Lfunc_end291-atomic_xsub_128_relaxed
	.cfi_endproc

	.section	.text.atomic_xsub_128_release,"ax",@progbits
	.globl	atomic_xsub_128_release
	.p2align	2
	.type	atomic_xsub_128_release,@function
atomic_xsub_128_release:
	.cfi_startproc
	mov	x8, x0
.LBB292_1:
	ldxp	x0, x1, [x8]
	subs	x9, x0, x2
	sbc	x10, x1, x3
	stlxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB292_1
	ret
.Lfunc_end292:
	.size	atomic_xsub_128_release, .Lfunc_end292-atomic_xsub_128_release
	.cfi_endproc

	.section	.text.atomic_xsub_128_seqcst,"ax",@progbits
	.globl	atomic_xsub_128_seqcst
	.p2align	2
	.type	atomic_xsub_128_seqcst,@function
atomic_xsub_128_seqcst:
	.cfi_startproc
	mov	x8, x0
.LBB293_1:
	ldaxp	x0, x1, [x8]
	subs	x9, x0, x2
	sbc	x10, x1, x3
	stlxp	w11, x9, x10, [x8]
	cbnz	w11, .LBB293_1
	ret
.Lfunc_end293:
	.size	atomic_xsub_128_seqcst, .Lfunc_end293-atomic_xsub_128_seqcst
	.cfi_endproc

	.section	.text.atomic_xsub_16_acqrel,"ax",@progbits
	.globl	atomic_xsub_16_acqrel
	.p2align	2
	.type	atomic_xsub_16_acqrel,@function
atomic_xsub_16_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end294:
	.size	atomic_xsub_16_acqrel, .Lfunc_end294-atomic_xsub_16_acqrel
	.cfi_endproc

	.section	.text.atomic_xsub_16_acquire,"ax",@progbits
	.globl	atomic_xsub_16_acquire
	.p2align	2
	.type	atomic_xsub_16_acquire,@function
atomic_xsub_16_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd2_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end295:
	.size	atomic_xsub_16_acquire, .Lfunc_end295-atomic_xsub_16_acquire
	.cfi_endproc

	.section	.text.atomic_xsub_16_relaxed,"ax",@progbits
	.globl	atomic_xsub_16_relaxed
	.p2align	2
	.type	atomic_xsub_16_relaxed,@function
atomic_xsub_16_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd2_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end296:
	.size	atomic_xsub_16_relaxed, .Lfunc_end296-atomic_xsub_16_relaxed
	.cfi_endproc

	.section	.text.atomic_xsub_16_release,"ax",@progbits
	.globl	atomic_xsub_16_release
	.p2align	2
	.type	atomic_xsub_16_release,@function
atomic_xsub_16_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd2_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end297:
	.size	atomic_xsub_16_release, .Lfunc_end297-atomic_xsub_16_release
	.cfi_endproc

	.section	.text.atomic_xsub_16_seqcst,"ax",@progbits
	.globl	atomic_xsub_16_seqcst
	.p2align	2
	.type	atomic_xsub_16_seqcst,@function
atomic_xsub_16_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd2_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end298:
	.size	atomic_xsub_16_seqcst, .Lfunc_end298-atomic_xsub_16_seqcst
	.cfi_endproc

	.section	.text.atomic_xsub_32_acqrel,"ax",@progbits
	.globl	atomic_xsub_32_acqrel
	.p2align	2
	.type	atomic_xsub_32_acqrel,@function
atomic_xsub_32_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end299:
	.size	atomic_xsub_32_acqrel, .Lfunc_end299-atomic_xsub_32_acqrel
	.cfi_endproc

	.section	.text.atomic_xsub_32_acquire,"ax",@progbits
	.globl	atomic_xsub_32_acquire
	.p2align	2
	.type	atomic_xsub_32_acquire,@function
atomic_xsub_32_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd4_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end300:
	.size	atomic_xsub_32_acquire, .Lfunc_end300-atomic_xsub_32_acquire
	.cfi_endproc

	.section	.text.atomic_xsub_32_relaxed,"ax",@progbits
	.globl	atomic_xsub_32_relaxed
	.p2align	2
	.type	atomic_xsub_32_relaxed,@function
atomic_xsub_32_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd4_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end301:
	.size	atomic_xsub_32_relaxed, .Lfunc_end301-atomic_xsub_32_relaxed
	.cfi_endproc

	.section	.text.atomic_xsub_32_release,"ax",@progbits
	.globl	atomic_xsub_32_release
	.p2align	2
	.type	atomic_xsub_32_release,@function
atomic_xsub_32_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd4_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end302:
	.size	atomic_xsub_32_release, .Lfunc_end302-atomic_xsub_32_release
	.cfi_endproc

	.section	.text.atomic_xsub_32_seqcst,"ax",@progbits
	.globl	atomic_xsub_32_seqcst
	.p2align	2
	.type	atomic_xsub_32_seqcst,@function
atomic_xsub_32_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd4_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end303:
	.size	atomic_xsub_32_seqcst, .Lfunc_end303-atomic_xsub_32_seqcst
	.cfi_endproc

	.section	.text.atomic_xsub_64_acqrel,"ax",@progbits
	.globl	atomic_xsub_64_acqrel
	.p2align	2
	.type	atomic_xsub_64_acqrel,@function
atomic_xsub_64_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	x0, x1
	mov	x1, x8
	bl	__aarch64_ldadd8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end304:
	.size	atomic_xsub_64_acqrel, .Lfunc_end304-atomic_xsub_64_acqrel
	.cfi_endproc

	.section	.text.atomic_xsub_64_acquire,"ax",@progbits
	.globl	atomic_xsub_64_acquire
	.p2align	2
	.type	atomic_xsub_64_acquire,@function
atomic_xsub_64_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	x0, x1
	mov	x1, x8
	bl	__aarch64_ldadd8_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end305:
	.size	atomic_xsub_64_acquire, .Lfunc_end305-atomic_xsub_64_acquire
	.cfi_endproc

	.section	.text.atomic_xsub_64_relaxed,"ax",@progbits
	.globl	atomic_xsub_64_relaxed
	.p2align	2
	.type	atomic_xsub_64_relaxed,@function
atomic_xsub_64_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	x0, x1
	mov	x1, x8
	bl	__aarch64_ldadd8_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end306:
	.size	atomic_xsub_64_relaxed, .Lfunc_end306-atomic_xsub_64_relaxed
	.cfi_endproc

	.section	.text.atomic_xsub_64_release,"ax",@progbits
	.globl	atomic_xsub_64_release
	.p2align	2
	.type	atomic_xsub_64_release,@function
atomic_xsub_64_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	x0, x1
	mov	x1, x8
	bl	__aarch64_ldadd8_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end307:
	.size	atomic_xsub_64_release, .Lfunc_end307-atomic_xsub_64_release
	.cfi_endproc

	.section	.text.atomic_xsub_64_seqcst,"ax",@progbits
	.globl	atomic_xsub_64_seqcst
	.p2align	2
	.type	atomic_xsub_64_seqcst,@function
atomic_xsub_64_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	x0, x1
	mov	x1, x8
	bl	__aarch64_ldadd8_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end308:
	.size	atomic_xsub_64_seqcst, .Lfunc_end308-atomic_xsub_64_seqcst
	.cfi_endproc

	.section	.text.atomic_xsub_8_acqrel,"ax",@progbits
	.globl	atomic_xsub_8_acqrel
	.p2align	2
	.type	atomic_xsub_8_acqrel,@function
atomic_xsub_8_acqrel:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end309:
	.size	atomic_xsub_8_acqrel, .Lfunc_end309-atomic_xsub_8_acqrel
	.cfi_endproc

	.section	.text.atomic_xsub_8_acquire,"ax",@progbits
	.globl	atomic_xsub_8_acquire
	.p2align	2
	.type	atomic_xsub_8_acquire,@function
atomic_xsub_8_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd1_acq
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end310:
	.size	atomic_xsub_8_acquire, .Lfunc_end310-atomic_xsub_8_acquire
	.cfi_endproc

	.section	.text.atomic_xsub_8_relaxed,"ax",@progbits
	.globl	atomic_xsub_8_relaxed
	.p2align	2
	.type	atomic_xsub_8_relaxed,@function
atomic_xsub_8_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd1_relax
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end311:
	.size	atomic_xsub_8_relaxed, .Lfunc_end311-atomic_xsub_8_relaxed
	.cfi_endproc

	.section	.text.atomic_xsub_8_release,"ax",@progbits
	.globl	atomic_xsub_8_release
	.p2align	2
	.type	atomic_xsub_8_release,@function
atomic_xsub_8_release:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd1_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end312:
	.size	atomic_xsub_8_release, .Lfunc_end312-atomic_xsub_8_release
	.cfi_endproc

	.section	.text.atomic_xsub_8_seqcst,"ax",@progbits
	.globl	atomic_xsub_8_seqcst
	.p2align	2
	.type	atomic_xsub_8_seqcst,@function
atomic_xsub_8_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x8, x0
	neg	w0, w1
	mov	x1, x8
	bl	__aarch64_ldadd1_acq_rel
	.cfi_def_cfa wsp, 16
	ldp	x29, x30, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end313:
	.size	atomic_xsub_8_seqcst, .Lfunc_end313-atomic_xsub_8_seqcst
	.cfi_endproc

	.section	.text.cxchg_128_acqrel_acquire,"ax",@progbits
	.globl	cxchg_128_acqrel_acquire
	.p2align	2
	.type	cxchg_128_acqrel_acquire,@function
cxchg_128_acqrel_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_acq_rel
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end314:
	.size	cxchg_128_acqrel_acquire, .Lfunc_end314-cxchg_128_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchg_128_acquire_acquire,"ax",@progbits
	.globl	cxchg_128_acquire_acquire
	.p2align	2
	.type	cxchg_128_acquire_acquire,@function
cxchg_128_acquire_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_acq
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end315:
	.size	cxchg_128_acquire_acquire, .Lfunc_end315-cxchg_128_acquire_acquire
	.cfi_endproc

	.section	.text.cxchg_128_relaxed_relaxed,"ax",@progbits
	.globl	cxchg_128_relaxed_relaxed
	.p2align	2
	.type	cxchg_128_relaxed_relaxed,@function
cxchg_128_relaxed_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_relax
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end316:
	.size	cxchg_128_relaxed_relaxed, .Lfunc_end316-cxchg_128_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchg_128_release_relaxed,"ax",@progbits
	.globl	cxchg_128_release_relaxed
	.p2align	2
	.type	cxchg_128_release_relaxed,@function
cxchg_128_release_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_rel
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end317:
	.size	cxchg_128_release_relaxed, .Lfunc_end317-cxchg_128_release_relaxed
	.cfi_endproc

	.section	.text.cxchg_128_seqcst_relaxed,"ax",@progbits
	.globl	cxchg_128_seqcst_relaxed
	.p2align	2
	.type	cxchg_128_seqcst_relaxed,@function
cxchg_128_seqcst_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_acq_rel
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end318:
	.size	cxchg_128_seqcst_relaxed, .Lfunc_end318-cxchg_128_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchg_128_seqcst_seqcst,"ax",@progbits
	.globl	cxchg_128_seqcst_seqcst
	.p2align	2
	.type	cxchg_128_seqcst_seqcst,@function
cxchg_128_seqcst_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_acq_rel
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end319:
	.size	cxchg_128_seqcst_seqcst, .Lfunc_end319-cxchg_128_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchg_16_acqrel_acquire,"ax",@progbits
	.globl	cxchg_16_acqrel_acquire
	.p2align	2
	.type	cxchg_16_acqrel_acquire,@function
cxchg_16_acqrel_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_acq_rel
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end320:
	.size	cxchg_16_acqrel_acquire, .Lfunc_end320-cxchg_16_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchg_16_acquire_acquire,"ax",@progbits
	.globl	cxchg_16_acquire_acquire
	.p2align	2
	.type	cxchg_16_acquire_acquire,@function
cxchg_16_acquire_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_acq
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end321:
	.size	cxchg_16_acquire_acquire, .Lfunc_end321-cxchg_16_acquire_acquire
	.cfi_endproc

	.section	.text.cxchg_16_relaxed_relaxed,"ax",@progbits
	.globl	cxchg_16_relaxed_relaxed
	.p2align	2
	.type	cxchg_16_relaxed_relaxed,@function
cxchg_16_relaxed_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_relax
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end322:
	.size	cxchg_16_relaxed_relaxed, .Lfunc_end322-cxchg_16_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchg_16_release_relaxed,"ax",@progbits
	.globl	cxchg_16_release_relaxed
	.p2align	2
	.type	cxchg_16_release_relaxed,@function
cxchg_16_release_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_rel
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end323:
	.size	cxchg_16_release_relaxed, .Lfunc_end323-cxchg_16_release_relaxed
	.cfi_endproc

	.section	.text.cxchg_16_seqcst_relaxed,"ax",@progbits
	.globl	cxchg_16_seqcst_relaxed
	.p2align	2
	.type	cxchg_16_seqcst_relaxed,@function
cxchg_16_seqcst_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_acq_rel
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end324:
	.size	cxchg_16_seqcst_relaxed, .Lfunc_end324-cxchg_16_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchg_16_seqcst_seqcst,"ax",@progbits
	.globl	cxchg_16_seqcst_seqcst
	.p2align	2
	.type	cxchg_16_seqcst_seqcst,@function
cxchg_16_seqcst_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_acq_rel
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end325:
	.size	cxchg_16_seqcst_seqcst, .Lfunc_end325-cxchg_16_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchg_32_acqrel_acquire,"ax",@progbits
	.globl	cxchg_32_acqrel_acquire
	.p2align	2
	.type	cxchg_32_acqrel_acquire,@function
cxchg_32_acqrel_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_acq_rel
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end326:
	.size	cxchg_32_acqrel_acquire, .Lfunc_end326-cxchg_32_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchg_32_acquire_acquire,"ax",@progbits
	.globl	cxchg_32_acquire_acquire
	.p2align	2
	.type	cxchg_32_acquire_acquire,@function
cxchg_32_acquire_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_acq
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end327:
	.size	cxchg_32_acquire_acquire, .Lfunc_end327-cxchg_32_acquire_acquire
	.cfi_endproc

	.section	.text.cxchg_32_relaxed_relaxed,"ax",@progbits
	.globl	cxchg_32_relaxed_relaxed
	.p2align	2
	.type	cxchg_32_relaxed_relaxed,@function
cxchg_32_relaxed_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_relax
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end328:
	.size	cxchg_32_relaxed_relaxed, .Lfunc_end328-cxchg_32_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchg_32_release_relaxed,"ax",@progbits
	.globl	cxchg_32_release_relaxed
	.p2align	2
	.type	cxchg_32_release_relaxed,@function
cxchg_32_release_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_rel
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end329:
	.size	cxchg_32_release_relaxed, .Lfunc_end329-cxchg_32_release_relaxed
	.cfi_endproc

	.section	.text.cxchg_32_seqcst_relaxed,"ax",@progbits
	.globl	cxchg_32_seqcst_relaxed
	.p2align	2
	.type	cxchg_32_seqcst_relaxed,@function
cxchg_32_seqcst_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_acq_rel
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end330:
	.size	cxchg_32_seqcst_relaxed, .Lfunc_end330-cxchg_32_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchg_32_seqcst_seqcst,"ax",@progbits
	.globl	cxchg_32_seqcst_seqcst
	.p2align	2
	.type	cxchg_32_seqcst_seqcst,@function
cxchg_32_seqcst_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_acq_rel
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end331:
	.size	cxchg_32_seqcst_seqcst, .Lfunc_end331-cxchg_32_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchg_64_acqrel_acquire,"ax",@progbits
	.globl	cxchg_64_acqrel_acquire
	.p2align	2
	.type	cxchg_64_acqrel_acquire,@function
cxchg_64_acqrel_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_acq_rel
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end332:
	.size	cxchg_64_acqrel_acquire, .Lfunc_end332-cxchg_64_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchg_64_acquire_acquire,"ax",@progbits
	.globl	cxchg_64_acquire_acquire
	.p2align	2
	.type	cxchg_64_acquire_acquire,@function
cxchg_64_acquire_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_acq
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end333:
	.size	cxchg_64_acquire_acquire, .Lfunc_end333-cxchg_64_acquire_acquire
	.cfi_endproc

	.section	.text.cxchg_64_relaxed_relaxed,"ax",@progbits
	.globl	cxchg_64_relaxed_relaxed
	.p2align	2
	.type	cxchg_64_relaxed_relaxed,@function
cxchg_64_relaxed_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_relax
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end334:
	.size	cxchg_64_relaxed_relaxed, .Lfunc_end334-cxchg_64_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchg_64_release_relaxed,"ax",@progbits
	.globl	cxchg_64_release_relaxed
	.p2align	2
	.type	cxchg_64_release_relaxed,@function
cxchg_64_release_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_rel
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end335:
	.size	cxchg_64_release_relaxed, .Lfunc_end335-cxchg_64_release_relaxed
	.cfi_endproc

	.section	.text.cxchg_64_seqcst_relaxed,"ax",@progbits
	.globl	cxchg_64_seqcst_relaxed
	.p2align	2
	.type	cxchg_64_seqcst_relaxed,@function
cxchg_64_seqcst_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_acq_rel
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end336:
	.size	cxchg_64_seqcst_relaxed, .Lfunc_end336-cxchg_64_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchg_64_seqcst_seqcst,"ax",@progbits
	.globl	cxchg_64_seqcst_seqcst
	.p2align	2
	.type	cxchg_64_seqcst_seqcst,@function
cxchg_64_seqcst_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_acq_rel
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end337:
	.size	cxchg_64_seqcst_seqcst, .Lfunc_end337-cxchg_64_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchg_8_acqrel_acquire,"ax",@progbits
	.globl	cxchg_8_acqrel_acquire
	.p2align	2
	.type	cxchg_8_acqrel_acquire,@function
cxchg_8_acqrel_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_acq_rel
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end338:
	.size	cxchg_8_acqrel_acquire, .Lfunc_end338-cxchg_8_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchg_8_acquire_acquire,"ax",@progbits
	.globl	cxchg_8_acquire_acquire
	.p2align	2
	.type	cxchg_8_acquire_acquire,@function
cxchg_8_acquire_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_acq
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end339:
	.size	cxchg_8_acquire_acquire, .Lfunc_end339-cxchg_8_acquire_acquire
	.cfi_endproc

	.section	.text.cxchg_8_relaxed_relaxed,"ax",@progbits
	.globl	cxchg_8_relaxed_relaxed
	.p2align	2
	.type	cxchg_8_relaxed_relaxed,@function
cxchg_8_relaxed_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_relax
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end340:
	.size	cxchg_8_relaxed_relaxed, .Lfunc_end340-cxchg_8_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchg_8_release_relaxed,"ax",@progbits
	.globl	cxchg_8_release_relaxed
	.p2align	2
	.type	cxchg_8_release_relaxed,@function
cxchg_8_release_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_rel
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end341:
	.size	cxchg_8_release_relaxed, .Lfunc_end341-cxchg_8_release_relaxed
	.cfi_endproc

	.section	.text.cxchg_8_seqcst_relaxed,"ax",@progbits
	.globl	cxchg_8_seqcst_relaxed
	.p2align	2
	.type	cxchg_8_seqcst_relaxed,@function
cxchg_8_seqcst_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_acq_rel
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end342:
	.size	cxchg_8_seqcst_relaxed, .Lfunc_end342-cxchg_8_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchg_8_seqcst_seqcst,"ax",@progbits
	.globl	cxchg_8_seqcst_seqcst
	.p2align	2
	.type	cxchg_8_seqcst_seqcst,@function
cxchg_8_seqcst_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_acq_rel
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end343:
	.size	cxchg_8_seqcst_seqcst, .Lfunc_end343-cxchg_8_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchgweak_128_acqrel_acquire,"ax",@progbits
	.globl	cxchgweak_128_acqrel_acquire
	.p2align	2
	.type	cxchgweak_128_acqrel_acquire,@function
cxchgweak_128_acqrel_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_acq_rel
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end344:
	.size	cxchgweak_128_acqrel_acquire, .Lfunc_end344-cxchgweak_128_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchgweak_128_acquire_acquire,"ax",@progbits
	.globl	cxchgweak_128_acquire_acquire
	.p2align	2
	.type	cxchgweak_128_acquire_acquire,@function
cxchgweak_128_acquire_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_acq
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end345:
	.size	cxchgweak_128_acquire_acquire, .Lfunc_end345-cxchgweak_128_acquire_acquire
	.cfi_endproc

	.section	.text.cxchgweak_128_relaxed_relaxed,"ax",@progbits
	.globl	cxchgweak_128_relaxed_relaxed
	.p2align	2
	.type	cxchgweak_128_relaxed_relaxed,@function
cxchgweak_128_relaxed_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_relax
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end346:
	.size	cxchgweak_128_relaxed_relaxed, .Lfunc_end346-cxchgweak_128_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_128_release_relaxed,"ax",@progbits
	.globl	cxchgweak_128_release_relaxed
	.p2align	2
	.type	cxchgweak_128_release_relaxed,@function
cxchgweak_128_release_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_rel
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end347:
	.size	cxchgweak_128_release_relaxed, .Lfunc_end347-cxchgweak_128_release_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_128_seqcst_relaxed,"ax",@progbits
	.globl	cxchgweak_128_seqcst_relaxed
	.p2align	2
	.type	cxchgweak_128_seqcst_relaxed,@function
cxchgweak_128_seqcst_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_acq_rel
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end348:
	.size	cxchgweak_128_seqcst_relaxed, .Lfunc_end348-cxchgweak_128_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_128_seqcst_seqcst,"ax",@progbits
	.globl	cxchgweak_128_seqcst_seqcst
	.p2align	2
	.type	cxchgweak_128_seqcst_seqcst,@function
cxchgweak_128_seqcst_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	str	x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	mov	x29, sp
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x9, x0
	mov	x19, x3
	mov	x20, x2
	mov	x0, x2
	mov	x1, x3
	mov	x2, x4
	mov	x3, x5
	mov	x4, x9
	mov	x21, x8
	bl	__aarch64_cas16_acq_rel
	cmp	x0, x20
	stp	x0, x1, [x21]
	ccmp	x1, x19, #0, eq
	cset	w8, eq
	strb	w8, [x21, #16]
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldr	x21, [sp, #16]
	ldp	x29, x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end349:
	.size	cxchgweak_128_seqcst_seqcst, .Lfunc_end349-cxchgweak_128_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchgweak_16_acqrel_acquire,"ax",@progbits
	.globl	cxchgweak_16_acqrel_acquire
	.p2align	2
	.type	cxchgweak_16_acqrel_acquire,@function
cxchgweak_16_acqrel_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_acq_rel
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end350:
	.size	cxchgweak_16_acqrel_acquire, .Lfunc_end350-cxchgweak_16_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchgweak_16_acquire_acquire,"ax",@progbits
	.globl	cxchgweak_16_acquire_acquire
	.p2align	2
	.type	cxchgweak_16_acquire_acquire,@function
cxchgweak_16_acquire_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_acq
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end351:
	.size	cxchgweak_16_acquire_acquire, .Lfunc_end351-cxchgweak_16_acquire_acquire
	.cfi_endproc

	.section	.text.cxchgweak_16_relaxed_relaxed,"ax",@progbits
	.globl	cxchgweak_16_relaxed_relaxed
	.p2align	2
	.type	cxchgweak_16_relaxed_relaxed,@function
cxchgweak_16_relaxed_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_relax
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end352:
	.size	cxchgweak_16_relaxed_relaxed, .Lfunc_end352-cxchgweak_16_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_16_release_relaxed,"ax",@progbits
	.globl	cxchgweak_16_release_relaxed
	.p2align	2
	.type	cxchgweak_16_release_relaxed,@function
cxchgweak_16_release_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_rel
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end353:
	.size	cxchgweak_16_release_relaxed, .Lfunc_end353-cxchgweak_16_release_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_16_seqcst_relaxed,"ax",@progbits
	.globl	cxchgweak_16_seqcst_relaxed
	.p2align	2
	.type	cxchgweak_16_seqcst_relaxed,@function
cxchgweak_16_seqcst_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_acq_rel
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end354:
	.size	cxchgweak_16_seqcst_relaxed, .Lfunc_end354-cxchgweak_16_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_16_seqcst_seqcst,"ax",@progbits
	.globl	cxchgweak_16_seqcst_seqcst
	.p2align	2
	.type	cxchgweak_16_seqcst_seqcst,@function
cxchgweak_16_seqcst_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas2_acq_rel
	cmp	w0, w19, uxth
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end355:
	.size	cxchgweak_16_seqcst_seqcst, .Lfunc_end355-cxchgweak_16_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchgweak_32_acqrel_acquire,"ax",@progbits
	.globl	cxchgweak_32_acqrel_acquire
	.p2align	2
	.type	cxchgweak_32_acqrel_acquire,@function
cxchgweak_32_acqrel_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_acq_rel
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end356:
	.size	cxchgweak_32_acqrel_acquire, .Lfunc_end356-cxchgweak_32_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchgweak_32_acquire_acquire,"ax",@progbits
	.globl	cxchgweak_32_acquire_acquire
	.p2align	2
	.type	cxchgweak_32_acquire_acquire,@function
cxchgweak_32_acquire_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_acq
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end357:
	.size	cxchgweak_32_acquire_acquire, .Lfunc_end357-cxchgweak_32_acquire_acquire
	.cfi_endproc

	.section	.text.cxchgweak_32_relaxed_relaxed,"ax",@progbits
	.globl	cxchgweak_32_relaxed_relaxed
	.p2align	2
	.type	cxchgweak_32_relaxed_relaxed,@function
cxchgweak_32_relaxed_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_relax
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end358:
	.size	cxchgweak_32_relaxed_relaxed, .Lfunc_end358-cxchgweak_32_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_32_release_relaxed,"ax",@progbits
	.globl	cxchgweak_32_release_relaxed
	.p2align	2
	.type	cxchgweak_32_release_relaxed,@function
cxchgweak_32_release_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_rel
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end359:
	.size	cxchgweak_32_release_relaxed, .Lfunc_end359-cxchgweak_32_release_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_32_seqcst_relaxed,"ax",@progbits
	.globl	cxchgweak_32_seqcst_relaxed
	.p2align	2
	.type	cxchgweak_32_seqcst_relaxed,@function
cxchgweak_32_seqcst_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_acq_rel
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end360:
	.size	cxchgweak_32_seqcst_relaxed, .Lfunc_end360-cxchgweak_32_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_32_seqcst_seqcst,"ax",@progbits
	.globl	cxchgweak_32_seqcst_seqcst
	.p2align	2
	.type	cxchgweak_32_seqcst_seqcst,@function
cxchgweak_32_seqcst_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas4_acq_rel
	cmp	w0, w19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end361:
	.size	cxchgweak_32_seqcst_seqcst, .Lfunc_end361-cxchgweak_32_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchgweak_64_acqrel_acquire,"ax",@progbits
	.globl	cxchgweak_64_acqrel_acquire
	.p2align	2
	.type	cxchgweak_64_acqrel_acquire,@function
cxchgweak_64_acqrel_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_acq_rel
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end362:
	.size	cxchgweak_64_acqrel_acquire, .Lfunc_end362-cxchgweak_64_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchgweak_64_acquire_acquire,"ax",@progbits
	.globl	cxchgweak_64_acquire_acquire
	.p2align	2
	.type	cxchgweak_64_acquire_acquire,@function
cxchgweak_64_acquire_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_acq
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end363:
	.size	cxchgweak_64_acquire_acquire, .Lfunc_end363-cxchgweak_64_acquire_acquire
	.cfi_endproc

	.section	.text.cxchgweak_64_relaxed_relaxed,"ax",@progbits
	.globl	cxchgweak_64_relaxed_relaxed
	.p2align	2
	.type	cxchgweak_64_relaxed_relaxed,@function
cxchgweak_64_relaxed_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_relax
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end364:
	.size	cxchgweak_64_relaxed_relaxed, .Lfunc_end364-cxchgweak_64_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_64_release_relaxed,"ax",@progbits
	.globl	cxchgweak_64_release_relaxed
	.p2align	2
	.type	cxchgweak_64_release_relaxed,@function
cxchgweak_64_release_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_rel
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end365:
	.size	cxchgweak_64_release_relaxed, .Lfunc_end365-cxchgweak_64_release_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_64_seqcst_relaxed,"ax",@progbits
	.globl	cxchgweak_64_seqcst_relaxed
	.p2align	2
	.type	cxchgweak_64_seqcst_relaxed,@function
cxchgweak_64_seqcst_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_acq_rel
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end366:
	.size	cxchgweak_64_seqcst_relaxed, .Lfunc_end366-cxchgweak_64_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_64_seqcst_seqcst,"ax",@progbits
	.globl	cxchgweak_64_seqcst_seqcst
	.p2align	2
	.type	cxchgweak_64_seqcst_seqcst,@function
cxchgweak_64_seqcst_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	x19, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x8
	bl	__aarch64_cas8_acq_rel
	cmp	x0, x19
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end367:
	.size	cxchgweak_64_seqcst_seqcst, .Lfunc_end367-cxchgweak_64_seqcst_seqcst
	.cfi_endproc

	.section	.text.cxchgweak_8_acqrel_acquire,"ax",@progbits
	.globl	cxchgweak_8_acqrel_acquire
	.p2align	2
	.type	cxchgweak_8_acqrel_acquire,@function
cxchgweak_8_acqrel_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_acq_rel
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end368:
	.size	cxchgweak_8_acqrel_acquire, .Lfunc_end368-cxchgweak_8_acqrel_acquire
	.cfi_endproc

	.section	.text.cxchgweak_8_acquire_acquire,"ax",@progbits
	.globl	cxchgweak_8_acquire_acquire
	.p2align	2
	.type	cxchgweak_8_acquire_acquire,@function
cxchgweak_8_acquire_acquire:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_acq
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end369:
	.size	cxchgweak_8_acquire_acquire, .Lfunc_end369-cxchgweak_8_acquire_acquire
	.cfi_endproc

	.section	.text.cxchgweak_8_relaxed_relaxed,"ax",@progbits
	.globl	cxchgweak_8_relaxed_relaxed
	.p2align	2
	.type	cxchgweak_8_relaxed_relaxed,@function
cxchgweak_8_relaxed_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_relax
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end370:
	.size	cxchgweak_8_relaxed_relaxed, .Lfunc_end370-cxchgweak_8_relaxed_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_8_release_relaxed,"ax",@progbits
	.globl	cxchgweak_8_release_relaxed
	.p2align	2
	.type	cxchgweak_8_release_relaxed,@function
cxchgweak_8_release_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_rel
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end371:
	.size	cxchgweak_8_release_relaxed, .Lfunc_end371-cxchgweak_8_release_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_8_seqcst_relaxed,"ax",@progbits
	.globl	cxchgweak_8_seqcst_relaxed
	.p2align	2
	.type	cxchgweak_8_seqcst_relaxed,@function
cxchgweak_8_seqcst_relaxed:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_acq_rel
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end372:
	.size	cxchgweak_8_seqcst_relaxed, .Lfunc_end372-cxchgweak_8_seqcst_relaxed
	.cfi_endproc

	.section	.text.cxchgweak_8_seqcst_seqcst,"ax",@progbits
	.globl	cxchgweak_8_seqcst_seqcst
	.p2align	2
	.type	cxchgweak_8_seqcst_seqcst,@function
cxchgweak_8_seqcst_seqcst:
	.cfi_startproc
	stp	x29, x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	str	x19, [sp, #16]
	mov	x29, sp
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	mov	x8, x0
	mov	w19, w1
	mov	w0, w1
	mov	w1, w2
	mov	x2, x8
	bl	__aarch64_cas1_acq_rel
	cmp	w0, w19, uxtb
	cset	w1, eq
	.cfi_def_cfa wsp, 32
	ldr	x19, [sp, #16]
	ldp	x29, x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end373:
	.size	cxchgweak_8_seqcst_seqcst, .Lfunc_end373-cxchgweak_8_seqcst_seqcst
	.cfi_endproc

	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
