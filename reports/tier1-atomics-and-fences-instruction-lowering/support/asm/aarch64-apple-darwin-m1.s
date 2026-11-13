	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	__RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.p2align	2
__RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind:
LBB0_1:
	b	LBB0_1

	.globl	_atomic_and_128_acqrel
	.p2align	2
_atomic_and_128_acqrel:
	ldp	x4, x5, [x0]
LBB1_1:
	mov	x7, x5
	mov	x6, x4
	and	x8, x4, x1
	and	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB1_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_and_128_acquire
	.p2align	2
_atomic_and_128_acquire:
	ldp	x4, x5, [x0]
LBB2_1:
	mov	x7, x5
	mov	x6, x4
	and	x8, x4, x1
	and	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspa	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB2_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_and_128_relaxed
	.p2align	2
_atomic_and_128_relaxed:
	ldp	x4, x5, [x0]
LBB3_1:
	mov	x7, x5
	mov	x6, x4
	and	x8, x4, x1
	and	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	casp	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB3_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_and_128_release
	.p2align	2
_atomic_and_128_release:
	ldp	x4, x5, [x0]
LBB4_1:
	mov	x7, x5
	mov	x6, x4
	and	x8, x4, x1
	and	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspl	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB4_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_and_128_seqcst
	.p2align	2
_atomic_and_128_seqcst:
	ldp	x4, x5, [x0]
LBB5_1:
	mov	x7, x5
	mov	x6, x4
	and	x8, x4, x1
	and	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB5_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_and_16_acqrel
	.p2align	2
_atomic_and_16_acqrel:
	mvn	w8, w1
	ldclralh	w8, w0, [x0]
	ret

	.globl	_atomic_and_16_acquire
	.p2align	2
_atomic_and_16_acquire:
	mvn	w8, w1
	ldclrah	w8, w0, [x0]
	ret

	.globl	_atomic_and_16_relaxed
	.p2align	2
_atomic_and_16_relaxed:
	mvn	w8, w1
	ldclrh	w8, w0, [x0]
	ret

	.globl	_atomic_and_16_release
	.p2align	2
_atomic_and_16_release:
	mvn	w8, w1
	ldclrlh	w8, w0, [x0]
	ret

	.globl	_atomic_and_16_seqcst
	.p2align	2
_atomic_and_16_seqcst:
	mvn	w8, w1
	ldclralh	w8, w0, [x0]
	ret

	.globl	_atomic_and_32_acqrel
	.p2align	2
_atomic_and_32_acqrel:
	mvn	w8, w1
	ldclral	w8, w0, [x0]
	ret

	.globl	_atomic_and_32_acquire
	.p2align	2
_atomic_and_32_acquire:
	mvn	w8, w1
	ldclra	w8, w0, [x0]
	ret

	.globl	_atomic_and_32_relaxed
	.p2align	2
_atomic_and_32_relaxed:
	mvn	w8, w1
	ldclr	w8, w0, [x0]
	ret

	.globl	_atomic_and_32_release
	.p2align	2
_atomic_and_32_release:
	mvn	w8, w1
	ldclrl	w8, w0, [x0]
	ret

	.globl	_atomic_and_32_seqcst
	.p2align	2
_atomic_and_32_seqcst:
	mvn	w8, w1
	ldclral	w8, w0, [x0]
	ret

	.globl	_atomic_and_64_acqrel
	.p2align	2
_atomic_and_64_acqrel:
	mvn	x8, x1
	ldclral	x8, x0, [x0]
	ret

	.globl	_atomic_and_64_acquire
	.p2align	2
_atomic_and_64_acquire:
	mvn	x8, x1
	ldclra	x8, x0, [x0]
	ret

	.globl	_atomic_and_64_relaxed
	.p2align	2
_atomic_and_64_relaxed:
	mvn	x8, x1
	ldclr	x8, x0, [x0]
	ret

	.globl	_atomic_and_64_release
	.p2align	2
_atomic_and_64_release:
	mvn	x8, x1
	ldclrl	x8, x0, [x0]
	ret

	.globl	_atomic_and_64_seqcst
	.p2align	2
_atomic_and_64_seqcst:
	mvn	x8, x1
	ldclral	x8, x0, [x0]
	ret

	.globl	_atomic_and_8_acqrel
	.p2align	2
_atomic_and_8_acqrel:
	mvn	w8, w1
	ldclralb	w8, w0, [x0]
	ret

	.globl	_atomic_and_8_acquire
	.p2align	2
_atomic_and_8_acquire:
	mvn	w8, w1
	ldclrab	w8, w0, [x0]
	ret

	.globl	_atomic_and_8_relaxed
	.p2align	2
_atomic_and_8_relaxed:
	mvn	w8, w1
	ldclrb	w8, w0, [x0]
	ret

	.globl	_atomic_and_8_release
	.p2align	2
_atomic_and_8_release:
	mvn	w8, w1
	ldclrlb	w8, w0, [x0]
	ret

	.globl	_atomic_and_8_seqcst
	.p2align	2
_atomic_and_8_seqcst:
	mvn	w8, w1
	ldclralb	w8, w0, [x0]
	ret

	.globl	_atomic_compiler_fence_acqrel
	.p2align	2
_atomic_compiler_fence_acqrel:
	;MEMBARRIER
	ret

	.globl	_atomic_compiler_fence_acquire
	.p2align	2
_atomic_compiler_fence_acquire:
	;MEMBARRIER
	ret

	.globl	_atomic_compiler_fence_release
	.p2align	2
_atomic_compiler_fence_release:
	;MEMBARRIER
	ret

	.globl	_atomic_compiler_fence_seqcst
	.p2align	2
_atomic_compiler_fence_seqcst:
	;MEMBARRIER
	ret

	.globl	_atomic_fence_acqrel
	.p2align	2
_atomic_fence_acqrel:
	dmb	ish
	ret

	.globl	_atomic_fence_acquire
	.p2align	2
_atomic_fence_acquire:
	dmb	ishld
	ret

	.globl	_atomic_fence_release
	.p2align	2
_atomic_fence_release:
	dmb	ish
	ret

	.globl	_atomic_fence_seqcst
	.p2align	2
_atomic_fence_seqcst:
	dmb	ish
	ret

	.globl	_atomic_load_128_acquire
	.p2align	2
_atomic_load_128_acquire:
	ldp	x0, x1, [x0]
	dmb	ishld
	ret

	.globl	_atomic_load_128_relaxed
	.p2align	2
_atomic_load_128_relaxed:
	ldp	x0, x1, [x0]
	ret

	.globl	_atomic_load_128_seqcst
	.p2align	2
_atomic_load_128_seqcst:
	ldar	xzr, [x0]
	ldp	x0, x1, [x0]
	dmb	ish
	ret

	.globl	_atomic_load_16_acquire
	.p2align	2
_atomic_load_16_acquire:
	ldaprh	w0, [x0]
	ret

	.globl	_atomic_load_16_relaxed
	.p2align	2
_atomic_load_16_relaxed:
	ldrh	w0, [x0]
	ret

	.globl	_atomic_load_16_seqcst
	.p2align	2
_atomic_load_16_seqcst:
	ldarh	w0, [x0]
	ret

	.globl	_atomic_load_32_acquire
	.p2align	2
_atomic_load_32_acquire:
	ldapr	w0, [x0]
	ret

	.globl	_atomic_load_32_relaxed
	.p2align	2
_atomic_load_32_relaxed:
	ldr	w0, [x0]
	ret

	.globl	_atomic_load_32_seqcst
	.p2align	2
_atomic_load_32_seqcst:
	ldar	w0, [x0]
	ret

	.globl	_atomic_load_64_acquire
	.p2align	2
_atomic_load_64_acquire:
	ldapr	x0, [x0]
	ret

	.globl	_atomic_load_64_relaxed
	.p2align	2
_atomic_load_64_relaxed:
	ldr	x0, [x0]
	ret

	.globl	_atomic_load_64_seqcst
	.p2align	2
_atomic_load_64_seqcst:
	ldar	x0, [x0]
	ret

	.globl	_atomic_load_8_acquire
	.p2align	2
_atomic_load_8_acquire:
	ldaprb	w0, [x0]
	ret

	.globl	_atomic_load_8_relaxed
	.p2align	2
_atomic_load_8_relaxed:
	ldrb	w0, [x0]
	ret

	.globl	_atomic_load_8_seqcst
	.p2align	2
_atomic_load_8_seqcst:
	ldarb	w0, [x0]
	ret

	.globl	_atomic_max_128_acqrel
	.p2align	2
_atomic_max_128_acqrel:
	ldp	x4, x5, [x0]
LBB49_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, lt
	csel	x8, x4, x1, lt
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB49_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_max_128_acquire
	.p2align	2
_atomic_max_128_acquire:
	ldp	x4, x5, [x0]
LBB50_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, lt
	csel	x8, x4, x1, lt
	mov	x4, x6
	mov	x5, x7
	caspa	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB50_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_max_128_relaxed
	.p2align	2
_atomic_max_128_relaxed:
	ldp	x4, x5, [x0]
LBB51_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, lt
	csel	x8, x4, x1, lt
	mov	x4, x6
	mov	x5, x7
	casp	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB51_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_max_128_release
	.p2align	2
_atomic_max_128_release:
	ldp	x4, x5, [x0]
LBB52_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, lt
	csel	x8, x4, x1, lt
	mov	x4, x6
	mov	x5, x7
	caspl	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB52_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_max_128_seqcst
	.p2align	2
_atomic_max_128_seqcst:
	ldp	x4, x5, [x0]
LBB53_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, lt
	csel	x8, x4, x1, lt
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB53_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_max_16_acqrel
	.p2align	2
_atomic_max_16_acqrel:
	ldsmaxalh	w1, w0, [x0]
	ret

	.globl	_atomic_max_16_acquire
	.p2align	2
_atomic_max_16_acquire:
	ldsmaxah	w1, w0, [x0]
	ret

	.globl	_atomic_max_16_relaxed
	.p2align	2
_atomic_max_16_relaxed:
	ldsmaxh	w1, w0, [x0]
	ret

	.globl	_atomic_max_16_release
	.p2align	2
_atomic_max_16_release:
	ldsmaxlh	w1, w0, [x0]
	ret

	.globl	_atomic_max_16_seqcst
	.p2align	2
_atomic_max_16_seqcst:
	ldsmaxalh	w1, w0, [x0]
	ret

	.globl	_atomic_max_32_acqrel
	.p2align	2
_atomic_max_32_acqrel:
	ldsmaxal	w1, w0, [x0]
	ret

	.globl	_atomic_max_32_acquire
	.p2align	2
_atomic_max_32_acquire:
	ldsmaxa	w1, w0, [x0]
	ret

	.globl	_atomic_max_32_relaxed
	.p2align	2
_atomic_max_32_relaxed:
	ldsmax	w1, w0, [x0]
	ret

	.globl	_atomic_max_32_release
	.p2align	2
_atomic_max_32_release:
	ldsmaxl	w1, w0, [x0]
	ret

	.globl	_atomic_max_32_seqcst
	.p2align	2
_atomic_max_32_seqcst:
	ldsmaxal	w1, w0, [x0]
	ret

	.globl	_atomic_max_64_acqrel
	.p2align	2
_atomic_max_64_acqrel:
	ldsmaxal	x1, x0, [x0]
	ret

	.globl	_atomic_max_64_acquire
	.p2align	2
_atomic_max_64_acquire:
	ldsmaxa	x1, x0, [x0]
	ret

	.globl	_atomic_max_64_relaxed
	.p2align	2
_atomic_max_64_relaxed:
	ldsmax	x1, x0, [x0]
	ret

	.globl	_atomic_max_64_release
	.p2align	2
_atomic_max_64_release:
	ldsmaxl	x1, x0, [x0]
	ret

	.globl	_atomic_max_64_seqcst
	.p2align	2
_atomic_max_64_seqcst:
	ldsmaxal	x1, x0, [x0]
	ret

	.globl	_atomic_max_8_acqrel
	.p2align	2
_atomic_max_8_acqrel:
	ldsmaxalb	w1, w0, [x0]
	ret

	.globl	_atomic_max_8_acquire
	.p2align	2
_atomic_max_8_acquire:
	ldsmaxab	w1, w0, [x0]
	ret

	.globl	_atomic_max_8_relaxed
	.p2align	2
_atomic_max_8_relaxed:
	ldsmaxb	w1, w0, [x0]
	ret

	.globl	_atomic_max_8_release
	.p2align	2
_atomic_max_8_release:
	ldsmaxlb	w1, w0, [x0]
	ret

	.globl	_atomic_max_8_seqcst
	.p2align	2
_atomic_max_8_seqcst:
	ldsmaxalb	w1, w0, [x0]
	ret

	.globl	_atomic_min_128_acqrel
	.p2align	2
_atomic_min_128_acqrel:
	ldp	x4, x5, [x0]
LBB74_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, ge
	csel	x8, x4, x1, ge
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB74_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_min_128_acquire
	.p2align	2
_atomic_min_128_acquire:
	ldp	x4, x5, [x0]
LBB75_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, ge
	csel	x8, x4, x1, ge
	mov	x4, x6
	mov	x5, x7
	caspa	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB75_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_min_128_relaxed
	.p2align	2
_atomic_min_128_relaxed:
	ldp	x4, x5, [x0]
LBB76_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, ge
	csel	x8, x4, x1, ge
	mov	x4, x6
	mov	x5, x7
	casp	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB76_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_min_128_release
	.p2align	2
_atomic_min_128_release:
	ldp	x4, x5, [x0]
LBB77_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, ge
	csel	x8, x4, x1, ge
	mov	x4, x6
	mov	x5, x7
	caspl	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB77_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_min_128_seqcst
	.p2align	2
_atomic_min_128_seqcst:
	ldp	x4, x5, [x0]
LBB78_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, ge
	csel	x8, x4, x1, ge
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB78_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_min_16_acqrel
	.p2align	2
_atomic_min_16_acqrel:
	ldsminalh	w1, w0, [x0]
	ret

	.globl	_atomic_min_16_acquire
	.p2align	2
_atomic_min_16_acquire:
	ldsminah	w1, w0, [x0]
	ret

	.globl	_atomic_min_16_relaxed
	.p2align	2
_atomic_min_16_relaxed:
	ldsminh	w1, w0, [x0]
	ret

	.globl	_atomic_min_16_release
	.p2align	2
_atomic_min_16_release:
	ldsminlh	w1, w0, [x0]
	ret

	.globl	_atomic_min_16_seqcst
	.p2align	2
_atomic_min_16_seqcst:
	ldsminalh	w1, w0, [x0]
	ret

	.globl	_atomic_min_32_acqrel
	.p2align	2
_atomic_min_32_acqrel:
	ldsminal	w1, w0, [x0]
	ret

	.globl	_atomic_min_32_acquire
	.p2align	2
_atomic_min_32_acquire:
	ldsmina	w1, w0, [x0]
	ret

	.globl	_atomic_min_32_relaxed
	.p2align	2
_atomic_min_32_relaxed:
	ldsmin	w1, w0, [x0]
	ret

	.globl	_atomic_min_32_release
	.p2align	2
_atomic_min_32_release:
	ldsminl	w1, w0, [x0]
	ret

	.globl	_atomic_min_32_seqcst
	.p2align	2
_atomic_min_32_seqcst:
	ldsminal	w1, w0, [x0]
	ret

	.globl	_atomic_min_64_acqrel
	.p2align	2
_atomic_min_64_acqrel:
	ldsminal	x1, x0, [x0]
	ret

	.globl	_atomic_min_64_acquire
	.p2align	2
_atomic_min_64_acquire:
	ldsmina	x1, x0, [x0]
	ret

	.globl	_atomic_min_64_relaxed
	.p2align	2
_atomic_min_64_relaxed:
	ldsmin	x1, x0, [x0]
	ret

	.globl	_atomic_min_64_release
	.p2align	2
_atomic_min_64_release:
	ldsminl	x1, x0, [x0]
	ret

	.globl	_atomic_min_64_seqcst
	.p2align	2
_atomic_min_64_seqcst:
	ldsminal	x1, x0, [x0]
	ret

	.globl	_atomic_min_8_acqrel
	.p2align	2
_atomic_min_8_acqrel:
	ldsminalb	w1, w0, [x0]
	ret

	.globl	_atomic_min_8_acquire
	.p2align	2
_atomic_min_8_acquire:
	ldsminab	w1, w0, [x0]
	ret

	.globl	_atomic_min_8_relaxed
	.p2align	2
_atomic_min_8_relaxed:
	ldsminb	w1, w0, [x0]
	ret

	.globl	_atomic_min_8_release
	.p2align	2
_atomic_min_8_release:
	ldsminlb	w1, w0, [x0]
	ret

	.globl	_atomic_min_8_seqcst
	.p2align	2
_atomic_min_8_seqcst:
	ldsminalb	w1, w0, [x0]
	ret

	.globl	_atomic_nand_128_acqrel
	.p2align	2
_atomic_nand_128_acqrel:
	ldp	x4, x5, [x0]
LBB99_1:
	mov	x7, x5
	mov	x6, x4
	and	x8, x7, x2
	and	x9, x4, x1
	mvn	x10, x9
	mvn	x11, x8
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x10, x11, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB99_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_nand_128_acquire
	.p2align	2
_atomic_nand_128_acquire:
	ldp	x4, x5, [x0]
LBB100_1:
	mov	x7, x5
	mov	x6, x4
	and	x8, x7, x2
	and	x9, x4, x1
	mvn	x10, x9
	mvn	x11, x8
	mov	x4, x6
	mov	x5, x7
	caspa	x4, x5, x10, x11, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB100_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_nand_128_relaxed
	.p2align	2
_atomic_nand_128_relaxed:
	ldp	x4, x5, [x0]
LBB101_1:
	mov	x7, x5
	mov	x6, x4
	and	x8, x7, x2
	and	x9, x4, x1
	mvn	x10, x9
	mvn	x11, x8
	mov	x4, x6
	mov	x5, x7
	casp	x4, x5, x10, x11, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB101_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_nand_128_release
	.p2align	2
_atomic_nand_128_release:
	ldp	x4, x5, [x0]
LBB102_1:
	mov	x7, x5
	mov	x6, x4
	and	x8, x7, x2
	and	x9, x4, x1
	mvn	x10, x9
	mvn	x11, x8
	mov	x4, x6
	mov	x5, x7
	caspl	x4, x5, x10, x11, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB102_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_nand_128_seqcst
	.p2align	2
_atomic_nand_128_seqcst:
	ldp	x4, x5, [x0]
LBB103_1:
	mov	x7, x5
	mov	x6, x4
	and	x8, x7, x2
	and	x9, x4, x1
	mvn	x10, x9
	mvn	x11, x8
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x10, x11, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB103_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_nand_16_acqrel
	.p2align	2
_atomic_nand_16_acqrel:
	ldrh	w8, [x0]
	mov	x9, x8
LBB104_1:
	and	w10, w8, w1
	mvn	w10, w10
	casalh	w9, w10, [x0]
	cmp	w9, w8, uxth
	mov	x8, x9
	b.ne	LBB104_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_16_acquire
	.p2align	2
_atomic_nand_16_acquire:
	ldrh	w8, [x0]
	mov	x9, x8
LBB105_1:
	and	w10, w8, w1
	mvn	w10, w10
	casah	w9, w10, [x0]
	cmp	w9, w8, uxth
	mov	x8, x9
	b.ne	LBB105_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_16_relaxed
	.p2align	2
_atomic_nand_16_relaxed:
	ldrh	w8, [x0]
	mov	x9, x8
LBB106_1:
	and	w10, w8, w1
	mvn	w10, w10
	cash	w9, w10, [x0]
	cmp	w9, w8, uxth
	mov	x8, x9
	b.ne	LBB106_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_16_release
	.p2align	2
_atomic_nand_16_release:
	ldrh	w8, [x0]
	mov	x9, x8
LBB107_1:
	and	w10, w8, w1
	mvn	w10, w10
	caslh	w9, w10, [x0]
	cmp	w9, w8, uxth
	mov	x8, x9
	b.ne	LBB107_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_16_seqcst
	.p2align	2
_atomic_nand_16_seqcst:
	ldrh	w8, [x0]
	mov	x9, x8
LBB108_1:
	and	w10, w8, w1
	mvn	w10, w10
	casalh	w9, w10, [x0]
	cmp	w9, w8, uxth
	mov	x8, x9
	b.ne	LBB108_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_32_acqrel
	.p2align	2
_atomic_nand_32_acqrel:
	ldr	w8, [x0]
	mov	x9, x8
LBB109_1:
	and	w10, w8, w1
	mvn	w10, w10
	casal	w9, w10, [x0]
	cmp	w9, w8
	mov	x8, x9
	b.ne	LBB109_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_32_acquire
	.p2align	2
_atomic_nand_32_acquire:
	ldr	w8, [x0]
	mov	x9, x8
LBB110_1:
	and	w10, w8, w1
	mvn	w10, w10
	casa	w9, w10, [x0]
	cmp	w9, w8
	mov	x8, x9
	b.ne	LBB110_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_32_relaxed
	.p2align	2
_atomic_nand_32_relaxed:
	ldr	w8, [x0]
	mov	x9, x8
LBB111_1:
	and	w10, w8, w1
	mvn	w10, w10
	cas	w9, w10, [x0]
	cmp	w9, w8
	mov	x8, x9
	b.ne	LBB111_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_32_release
	.p2align	2
_atomic_nand_32_release:
	ldr	w8, [x0]
	mov	x9, x8
LBB112_1:
	and	w10, w8, w1
	mvn	w10, w10
	casl	w9, w10, [x0]
	cmp	w9, w8
	mov	x8, x9
	b.ne	LBB112_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_32_seqcst
	.p2align	2
_atomic_nand_32_seqcst:
	ldr	w8, [x0]
	mov	x9, x8
LBB113_1:
	and	w10, w8, w1
	mvn	w10, w10
	casal	w9, w10, [x0]
	cmp	w9, w8
	mov	x8, x9
	b.ne	LBB113_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_64_acqrel
	.p2align	2
_atomic_nand_64_acqrel:
	ldr	x8, [x0]
	mov	x9, x8
LBB114_1:
	and	x10, x8, x1
	mvn	x10, x10
	casal	x9, x10, [x0]
	cmp	x9, x8
	mov	x8, x9
	b.ne	LBB114_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_64_acquire
	.p2align	2
_atomic_nand_64_acquire:
	ldr	x8, [x0]
	mov	x9, x8
LBB115_1:
	and	x10, x8, x1
	mvn	x10, x10
	casa	x9, x10, [x0]
	cmp	x9, x8
	mov	x8, x9
	b.ne	LBB115_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_64_relaxed
	.p2align	2
_atomic_nand_64_relaxed:
	ldr	x8, [x0]
	mov	x9, x8
LBB116_1:
	and	x10, x8, x1
	mvn	x10, x10
	cas	x9, x10, [x0]
	cmp	x9, x8
	mov	x8, x9
	b.ne	LBB116_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_64_release
	.p2align	2
_atomic_nand_64_release:
	ldr	x8, [x0]
	mov	x9, x8
LBB117_1:
	and	x10, x8, x1
	mvn	x10, x10
	casl	x9, x10, [x0]
	cmp	x9, x8
	mov	x8, x9
	b.ne	LBB117_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_64_seqcst
	.p2align	2
_atomic_nand_64_seqcst:
	ldr	x8, [x0]
	mov	x9, x8
LBB118_1:
	and	x10, x8, x1
	mvn	x10, x10
	casal	x9, x10, [x0]
	cmp	x9, x8
	mov	x8, x9
	b.ne	LBB118_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_8_acqrel
	.p2align	2
_atomic_nand_8_acqrel:
	ldrb	w8, [x0]
	mov	x9, x8
LBB119_1:
	and	w10, w8, w1
	mvn	w10, w10
	casalb	w9, w10, [x0]
	cmp	w9, w8, uxtb
	mov	x8, x9
	b.ne	LBB119_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_8_acquire
	.p2align	2
_atomic_nand_8_acquire:
	ldrb	w8, [x0]
	mov	x9, x8
LBB120_1:
	and	w10, w8, w1
	mvn	w10, w10
	casab	w9, w10, [x0]
	cmp	w9, w8, uxtb
	mov	x8, x9
	b.ne	LBB120_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_8_relaxed
	.p2align	2
_atomic_nand_8_relaxed:
	ldrb	w8, [x0]
	mov	x9, x8
LBB121_1:
	and	w10, w8, w1
	mvn	w10, w10
	casb	w9, w10, [x0]
	cmp	w9, w8, uxtb
	mov	x8, x9
	b.ne	LBB121_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_8_release
	.p2align	2
_atomic_nand_8_release:
	ldrb	w8, [x0]
	mov	x9, x8
LBB122_1:
	and	w10, w8, w1
	mvn	w10, w10
	caslb	w9, w10, [x0]
	cmp	w9, w8, uxtb
	mov	x8, x9
	b.ne	LBB122_1
	mov	x0, x8
	ret

	.globl	_atomic_nand_8_seqcst
	.p2align	2
_atomic_nand_8_seqcst:
	ldrb	w8, [x0]
	mov	x9, x8
LBB123_1:
	and	w10, w8, w1
	mvn	w10, w10
	casalb	w9, w10, [x0]
	cmp	w9, w8, uxtb
	mov	x8, x9
	b.ne	LBB123_1
	mov	x0, x8
	ret

	.globl	_atomic_or_128_acqrel
	.p2align	2
_atomic_or_128_acqrel:
	ldp	x4, x5, [x0]
LBB124_1:
	mov	x7, x5
	mov	x6, x4
	orr	x8, x4, x1
	orr	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB124_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_or_128_acquire
	.p2align	2
_atomic_or_128_acquire:
	ldp	x4, x5, [x0]
LBB125_1:
	mov	x7, x5
	mov	x6, x4
	orr	x8, x4, x1
	orr	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspa	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB125_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_or_128_relaxed
	.p2align	2
_atomic_or_128_relaxed:
	ldp	x4, x5, [x0]
LBB126_1:
	mov	x7, x5
	mov	x6, x4
	orr	x8, x4, x1
	orr	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	casp	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB126_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_or_128_release
	.p2align	2
_atomic_or_128_release:
	ldp	x4, x5, [x0]
LBB127_1:
	mov	x7, x5
	mov	x6, x4
	orr	x8, x4, x1
	orr	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspl	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB127_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_or_128_seqcst
	.p2align	2
_atomic_or_128_seqcst:
	ldp	x4, x5, [x0]
LBB128_1:
	mov	x7, x5
	mov	x6, x4
	orr	x8, x4, x1
	orr	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB128_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_or_16_acqrel
	.p2align	2
_atomic_or_16_acqrel:
	ldsetalh	w1, w0, [x0]
	ret

	.globl	_atomic_or_16_acquire
	.p2align	2
_atomic_or_16_acquire:
	ldsetah	w1, w0, [x0]
	ret

	.globl	_atomic_or_16_relaxed
	.p2align	2
_atomic_or_16_relaxed:
	ldseth	w1, w0, [x0]
	ret

	.globl	_atomic_or_16_release
	.p2align	2
_atomic_or_16_release:
	ldsetlh	w1, w0, [x0]
	ret

	.globl	_atomic_or_16_seqcst
	.p2align	2
_atomic_or_16_seqcst:
	ldsetalh	w1, w0, [x0]
	ret

	.globl	_atomic_or_32_acqrel
	.p2align	2
_atomic_or_32_acqrel:
	ldsetal	w1, w0, [x0]
	ret

	.globl	_atomic_or_32_acquire
	.p2align	2
_atomic_or_32_acquire:
	ldseta	w1, w0, [x0]
	ret

	.globl	_atomic_or_32_relaxed
	.p2align	2
_atomic_or_32_relaxed:
	ldset	w1, w0, [x0]
	ret

	.globl	_atomic_or_32_release
	.p2align	2
_atomic_or_32_release:
	ldsetl	w1, w0, [x0]
	ret

	.globl	_atomic_or_32_seqcst
	.p2align	2
_atomic_or_32_seqcst:
	ldsetal	w1, w0, [x0]
	ret

	.globl	_atomic_or_64_acqrel
	.p2align	2
_atomic_or_64_acqrel:
	ldsetal	x1, x0, [x0]
	ret

	.globl	_atomic_or_64_acquire
	.p2align	2
_atomic_or_64_acquire:
	ldseta	x1, x0, [x0]
	ret

	.globl	_atomic_or_64_relaxed
	.p2align	2
_atomic_or_64_relaxed:
	ldset	x1, x0, [x0]
	ret

	.globl	_atomic_or_64_release
	.p2align	2
_atomic_or_64_release:
	ldsetl	x1, x0, [x0]
	ret

	.globl	_atomic_or_64_seqcst
	.p2align	2
_atomic_or_64_seqcst:
	ldsetal	x1, x0, [x0]
	ret

	.globl	_atomic_or_8_acqrel
	.p2align	2
_atomic_or_8_acqrel:
	ldsetalb	w1, w0, [x0]
	ret

	.globl	_atomic_or_8_acquire
	.p2align	2
_atomic_or_8_acquire:
	ldsetab	w1, w0, [x0]
	ret

	.globl	_atomic_or_8_relaxed
	.p2align	2
_atomic_or_8_relaxed:
	ldsetb	w1, w0, [x0]
	ret

	.globl	_atomic_or_8_release
	.p2align	2
_atomic_or_8_release:
	ldsetlb	w1, w0, [x0]
	ret

	.globl	_atomic_or_8_seqcst
	.p2align	2
_atomic_or_8_seqcst:
	ldsetalb	w1, w0, [x0]
	ret

	.globl	_atomic_store_128_relaxed
	.p2align	2
_atomic_store_128_relaxed:
	stp	x1, x2, [x0]
	ret

	.globl	_atomic_store_128_release
	.p2align	2
_atomic_store_128_release:
	dmb	ish
	stp	x1, x2, [x0]
	ret

	.globl	_atomic_store_128_seqcst
	.p2align	2
_atomic_store_128_seqcst:
	dmb	ish
	stp	x1, x2, [x0]
	dmb	ish
	ret

	.globl	_atomic_store_16_relaxed
	.p2align	2
_atomic_store_16_relaxed:
	strh	w1, [x0]
	ret

	.globl	_atomic_store_16_release
	.p2align	2
_atomic_store_16_release:
	stlrh	w1, [x0]
	ret

	.globl	_atomic_store_16_seqcst
	.p2align	2
_atomic_store_16_seqcst:
	stlrh	w1, [x0]
	ret

	.globl	_atomic_store_32_relaxed
	.p2align	2
_atomic_store_32_relaxed:
	str	w1, [x0]
	ret

	.globl	_atomic_store_32_release
	.p2align	2
_atomic_store_32_release:
	stlr	w1, [x0]
	ret

	.globl	_atomic_store_32_seqcst
	.p2align	2
_atomic_store_32_seqcst:
	stlr	w1, [x0]
	ret

	.globl	_atomic_store_64_relaxed
	.p2align	2
_atomic_store_64_relaxed:
	str	x1, [x0]
	ret

	.globl	_atomic_store_64_release
	.p2align	2
_atomic_store_64_release:
	stlr	x1, [x0]
	ret

	.globl	_atomic_store_64_seqcst
	.p2align	2
_atomic_store_64_seqcst:
	stlr	x1, [x0]
	ret

	.globl	_atomic_store_8_relaxed
	.p2align	2
_atomic_store_8_relaxed:
	strb	w1, [x0]
	ret

	.globl	_atomic_store_8_release
	.p2align	2
_atomic_store_8_release:
	stlrb	w1, [x0]
	ret

	.globl	_atomic_store_8_seqcst
	.p2align	2
_atomic_store_8_seqcst:
	stlrb	w1, [x0]
	ret

	.globl	_atomic_umax_128_acqrel
	.p2align	2
_atomic_umax_128_acqrel:
	ldp	x4, x5, [x0]
LBB164_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, lo
	csel	x8, x4, x1, lo
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB164_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_umax_128_acquire
	.p2align	2
_atomic_umax_128_acquire:
	ldp	x4, x5, [x0]
LBB165_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, lo
	csel	x8, x4, x1, lo
	mov	x4, x6
	mov	x5, x7
	caspa	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB165_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_umax_128_relaxed
	.p2align	2
_atomic_umax_128_relaxed:
	ldp	x4, x5, [x0]
LBB166_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, lo
	csel	x8, x4, x1, lo
	mov	x4, x6
	mov	x5, x7
	casp	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB166_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_umax_128_release
	.p2align	2
_atomic_umax_128_release:
	ldp	x4, x5, [x0]
LBB167_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, lo
	csel	x8, x4, x1, lo
	mov	x4, x6
	mov	x5, x7
	caspl	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB167_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_umax_128_seqcst
	.p2align	2
_atomic_umax_128_seqcst:
	ldp	x4, x5, [x0]
LBB168_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, lo
	csel	x8, x4, x1, lo
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB168_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_umax_16_acqrel
	.p2align	2
_atomic_umax_16_acqrel:
	ldumaxalh	w1, w0, [x0]
	ret

	.globl	_atomic_umax_16_acquire
	.p2align	2
_atomic_umax_16_acquire:
	ldumaxah	w1, w0, [x0]
	ret

	.globl	_atomic_umax_16_relaxed
	.p2align	2
_atomic_umax_16_relaxed:
	ldumaxh	w1, w0, [x0]
	ret

	.globl	_atomic_umax_16_release
	.p2align	2
_atomic_umax_16_release:
	ldumaxlh	w1, w0, [x0]
	ret

	.globl	_atomic_umax_16_seqcst
	.p2align	2
_atomic_umax_16_seqcst:
	ldumaxalh	w1, w0, [x0]
	ret

	.globl	_atomic_umax_32_acqrel
	.p2align	2
_atomic_umax_32_acqrel:
	ldumaxal	w1, w0, [x0]
	ret

	.globl	_atomic_umax_32_acquire
	.p2align	2
_atomic_umax_32_acquire:
	ldumaxa	w1, w0, [x0]
	ret

	.globl	_atomic_umax_32_relaxed
	.p2align	2
_atomic_umax_32_relaxed:
	ldumax	w1, w0, [x0]
	ret

	.globl	_atomic_umax_32_release
	.p2align	2
_atomic_umax_32_release:
	ldumaxl	w1, w0, [x0]
	ret

	.globl	_atomic_umax_32_seqcst
	.p2align	2
_atomic_umax_32_seqcst:
	ldumaxal	w1, w0, [x0]
	ret

	.globl	_atomic_umax_64_acqrel
	.p2align	2
_atomic_umax_64_acqrel:
	ldumaxal	x1, x0, [x0]
	ret

	.globl	_atomic_umax_64_acquire
	.p2align	2
_atomic_umax_64_acquire:
	ldumaxa	x1, x0, [x0]
	ret

	.globl	_atomic_umax_64_relaxed
	.p2align	2
_atomic_umax_64_relaxed:
	ldumax	x1, x0, [x0]
	ret

	.globl	_atomic_umax_64_release
	.p2align	2
_atomic_umax_64_release:
	ldumaxl	x1, x0, [x0]
	ret

	.globl	_atomic_umax_64_seqcst
	.p2align	2
_atomic_umax_64_seqcst:
	ldumaxal	x1, x0, [x0]
	ret

	.globl	_atomic_umax_8_acqrel
	.p2align	2
_atomic_umax_8_acqrel:
	ldumaxalb	w1, w0, [x0]
	ret

	.globl	_atomic_umax_8_acquire
	.p2align	2
_atomic_umax_8_acquire:
	ldumaxab	w1, w0, [x0]
	ret

	.globl	_atomic_umax_8_relaxed
	.p2align	2
_atomic_umax_8_relaxed:
	ldumaxb	w1, w0, [x0]
	ret

	.globl	_atomic_umax_8_release
	.p2align	2
_atomic_umax_8_release:
	ldumaxlb	w1, w0, [x0]
	ret

	.globl	_atomic_umax_8_seqcst
	.p2align	2
_atomic_umax_8_seqcst:
	ldumaxalb	w1, w0, [x0]
	ret

	.globl	_atomic_umin_128_acqrel
	.p2align	2
_atomic_umin_128_acqrel:
	ldp	x4, x5, [x0]
LBB189_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, hs
	csel	x8, x4, x1, hs
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB189_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_umin_128_acquire
	.p2align	2
_atomic_umin_128_acquire:
	ldp	x4, x5, [x0]
LBB190_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, hs
	csel	x8, x4, x1, hs
	mov	x4, x6
	mov	x5, x7
	caspa	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB190_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_umin_128_relaxed
	.p2align	2
_atomic_umin_128_relaxed:
	ldp	x4, x5, [x0]
LBB191_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, hs
	csel	x8, x4, x1, hs
	mov	x4, x6
	mov	x5, x7
	casp	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB191_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_umin_128_release
	.p2align	2
_atomic_umin_128_release:
	ldp	x4, x5, [x0]
LBB192_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, hs
	csel	x8, x4, x1, hs
	mov	x4, x6
	mov	x5, x7
	caspl	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB192_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_umin_128_seqcst
	.p2align	2
_atomic_umin_128_seqcst:
	ldp	x4, x5, [x0]
LBB193_1:
	mov	x7, x5
	mov	x6, x4
	cmp	x1, x4
	sbcs	xzr, x2, x7
	csel	x9, x7, x2, hs
	csel	x8, x4, x1, hs
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB193_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_umin_16_acqrel
	.p2align	2
_atomic_umin_16_acqrel:
	lduminalh	w1, w0, [x0]
	ret

	.globl	_atomic_umin_16_acquire
	.p2align	2
_atomic_umin_16_acquire:
	lduminah	w1, w0, [x0]
	ret

	.globl	_atomic_umin_16_relaxed
	.p2align	2
_atomic_umin_16_relaxed:
	lduminh	w1, w0, [x0]
	ret

	.globl	_atomic_umin_16_release
	.p2align	2
_atomic_umin_16_release:
	lduminlh	w1, w0, [x0]
	ret

	.globl	_atomic_umin_16_seqcst
	.p2align	2
_atomic_umin_16_seqcst:
	lduminalh	w1, w0, [x0]
	ret

	.globl	_atomic_umin_32_acqrel
	.p2align	2
_atomic_umin_32_acqrel:
	lduminal	w1, w0, [x0]
	ret

	.globl	_atomic_umin_32_acquire
	.p2align	2
_atomic_umin_32_acquire:
	ldumina	w1, w0, [x0]
	ret

	.globl	_atomic_umin_32_relaxed
	.p2align	2
_atomic_umin_32_relaxed:
	ldumin	w1, w0, [x0]
	ret

	.globl	_atomic_umin_32_release
	.p2align	2
_atomic_umin_32_release:
	lduminl	w1, w0, [x0]
	ret

	.globl	_atomic_umin_32_seqcst
	.p2align	2
_atomic_umin_32_seqcst:
	lduminal	w1, w0, [x0]
	ret

	.globl	_atomic_umin_64_acqrel
	.p2align	2
_atomic_umin_64_acqrel:
	lduminal	x1, x0, [x0]
	ret

	.globl	_atomic_umin_64_acquire
	.p2align	2
_atomic_umin_64_acquire:
	ldumina	x1, x0, [x0]
	ret

	.globl	_atomic_umin_64_relaxed
	.p2align	2
_atomic_umin_64_relaxed:
	ldumin	x1, x0, [x0]
	ret

	.globl	_atomic_umin_64_release
	.p2align	2
_atomic_umin_64_release:
	lduminl	x1, x0, [x0]
	ret

	.globl	_atomic_umin_64_seqcst
	.p2align	2
_atomic_umin_64_seqcst:
	lduminal	x1, x0, [x0]
	ret

	.globl	_atomic_umin_8_acqrel
	.p2align	2
_atomic_umin_8_acqrel:
	lduminalb	w1, w0, [x0]
	ret

	.globl	_atomic_umin_8_acquire
	.p2align	2
_atomic_umin_8_acquire:
	lduminab	w1, w0, [x0]
	ret

	.globl	_atomic_umin_8_relaxed
	.p2align	2
_atomic_umin_8_relaxed:
	lduminb	w1, w0, [x0]
	ret

	.globl	_atomic_umin_8_release
	.p2align	2
_atomic_umin_8_release:
	lduminlb	w1, w0, [x0]
	ret

	.globl	_atomic_umin_8_seqcst
	.p2align	2
_atomic_umin_8_seqcst:
	lduminalb	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_128_acqrel
	.p2align	2
_atomic_xadd_128_acqrel:
	ldp	x4, x5, [x0]
LBB214_1:
	mov	x7, x5
	mov	x6, x4
	adds	x8, x4, x1
	adc	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB214_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xadd_128_acquire
	.p2align	2
_atomic_xadd_128_acquire:
	ldp	x4, x5, [x0]
LBB215_1:
	mov	x7, x5
	mov	x6, x4
	adds	x8, x4, x1
	adc	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspa	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB215_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xadd_128_relaxed
	.p2align	2
_atomic_xadd_128_relaxed:
	ldp	x4, x5, [x0]
LBB216_1:
	mov	x7, x5
	mov	x6, x4
	adds	x8, x4, x1
	adc	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	casp	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB216_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xadd_128_release
	.p2align	2
_atomic_xadd_128_release:
	ldp	x4, x5, [x0]
LBB217_1:
	mov	x7, x5
	mov	x6, x4
	adds	x8, x4, x1
	adc	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspl	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB217_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xadd_128_seqcst
	.p2align	2
_atomic_xadd_128_seqcst:
	ldp	x4, x5, [x0]
LBB218_1:
	mov	x7, x5
	mov	x6, x4
	adds	x8, x4, x1
	adc	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB218_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xadd_16_acqrel
	.p2align	2
_atomic_xadd_16_acqrel:
	ldaddalh	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_16_acquire
	.p2align	2
_atomic_xadd_16_acquire:
	ldaddah	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_16_relaxed
	.p2align	2
_atomic_xadd_16_relaxed:
	ldaddh	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_16_release
	.p2align	2
_atomic_xadd_16_release:
	ldaddlh	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_16_seqcst
	.p2align	2
_atomic_xadd_16_seqcst:
	ldaddalh	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_32_acqrel
	.p2align	2
_atomic_xadd_32_acqrel:
	ldaddal	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_32_acquire
	.p2align	2
_atomic_xadd_32_acquire:
	ldadda	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_32_relaxed
	.p2align	2
_atomic_xadd_32_relaxed:
	ldadd	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_32_release
	.p2align	2
_atomic_xadd_32_release:
	ldaddl	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_32_seqcst
	.p2align	2
_atomic_xadd_32_seqcst:
	ldaddal	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_64_acqrel
	.p2align	2
_atomic_xadd_64_acqrel:
	ldaddal	x1, x0, [x0]
	ret

	.globl	_atomic_xadd_64_acquire
	.p2align	2
_atomic_xadd_64_acquire:
	ldadda	x1, x0, [x0]
	ret

	.globl	_atomic_xadd_64_relaxed
	.p2align	2
_atomic_xadd_64_relaxed:
	ldadd	x1, x0, [x0]
	ret

	.globl	_atomic_xadd_64_release
	.p2align	2
_atomic_xadd_64_release:
	ldaddl	x1, x0, [x0]
	ret

	.globl	_atomic_xadd_64_seqcst
	.p2align	2
_atomic_xadd_64_seqcst:
	ldaddal	x1, x0, [x0]
	ret

	.globl	_atomic_xadd_8_acqrel
	.p2align	2
_atomic_xadd_8_acqrel:
	ldaddalb	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_8_acquire
	.p2align	2
_atomic_xadd_8_acquire:
	ldaddab	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_8_relaxed
	.p2align	2
_atomic_xadd_8_relaxed:
	ldaddb	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_8_release
	.p2align	2
_atomic_xadd_8_release:
	ldaddlb	w1, w0, [x0]
	ret

	.globl	_atomic_xadd_8_seqcst
	.p2align	2
_atomic_xadd_8_seqcst:
	ldaddalb	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_128_acqrel
	.p2align	2
_atomic_xchg_128_acqrel:
	mov	x5, x2
	ldp	x2, x3, [x0]
	mov	x4, x1
LBB239_1:
	mov	x7, x3
	mov	x6, x2
	mov	x2, x6
	mov	x3, x7
	caspal	x2, x3, x4, x5, [x0]
	cmp	x3, x7
	ccmp	x2, x6, #0, eq
	b.ne	LBB239_1
	mov	x0, x2
	mov	x1, x3
	ret

	.globl	_atomic_xchg_128_acquire
	.p2align	2
_atomic_xchg_128_acquire:
	mov	x5, x2
	ldp	x2, x3, [x0]
	mov	x4, x1
LBB240_1:
	mov	x7, x3
	mov	x6, x2
	mov	x2, x6
	mov	x3, x7
	caspa	x2, x3, x4, x5, [x0]
	cmp	x3, x7
	ccmp	x2, x6, #0, eq
	b.ne	LBB240_1
	mov	x0, x2
	mov	x1, x3
	ret

	.globl	_atomic_xchg_128_relaxed
	.p2align	2
_atomic_xchg_128_relaxed:
	mov	x5, x2
	ldp	x2, x3, [x0]
	mov	x4, x1
LBB241_1:
	mov	x7, x3
	mov	x6, x2
	mov	x2, x6
	mov	x3, x7
	casp	x2, x3, x4, x5, [x0]
	cmp	x3, x7
	ccmp	x2, x6, #0, eq
	b.ne	LBB241_1
	mov	x0, x2
	mov	x1, x3
	ret

	.globl	_atomic_xchg_128_release
	.p2align	2
_atomic_xchg_128_release:
	mov	x5, x2
	ldp	x2, x3, [x0]
	mov	x4, x1
LBB242_1:
	mov	x7, x3
	mov	x6, x2
	mov	x2, x6
	mov	x3, x7
	caspl	x2, x3, x4, x5, [x0]
	cmp	x3, x7
	ccmp	x2, x6, #0, eq
	b.ne	LBB242_1
	mov	x0, x2
	mov	x1, x3
	ret

	.globl	_atomic_xchg_128_seqcst
	.p2align	2
_atomic_xchg_128_seqcst:
	mov	x5, x2
	ldp	x2, x3, [x0]
	mov	x4, x1
LBB243_1:
	mov	x7, x3
	mov	x6, x2
	mov	x2, x6
	mov	x3, x7
	caspal	x2, x3, x4, x5, [x0]
	cmp	x3, x7
	ccmp	x2, x6, #0, eq
	b.ne	LBB243_1
	mov	x0, x2
	mov	x1, x3
	ret

	.globl	_atomic_xchg_16_acqrel
	.p2align	2
_atomic_xchg_16_acqrel:
	swpalh	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_16_acquire
	.p2align	2
_atomic_xchg_16_acquire:
	swpah	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_16_relaxed
	.p2align	2
_atomic_xchg_16_relaxed:
	swph	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_16_release
	.p2align	2
_atomic_xchg_16_release:
	swplh	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_16_seqcst
	.p2align	2
_atomic_xchg_16_seqcst:
	swpalh	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_32_acqrel
	.p2align	2
_atomic_xchg_32_acqrel:
	swpal	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_32_acquire
	.p2align	2
_atomic_xchg_32_acquire:
	swpa	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_32_relaxed
	.p2align	2
_atomic_xchg_32_relaxed:
	swp	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_32_release
	.p2align	2
_atomic_xchg_32_release:
	swpl	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_32_seqcst
	.p2align	2
_atomic_xchg_32_seqcst:
	swpal	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_64_acqrel
	.p2align	2
_atomic_xchg_64_acqrel:
	swpal	x1, x0, [x0]
	ret

	.globl	_atomic_xchg_64_acquire
	.p2align	2
_atomic_xchg_64_acquire:
	swpa	x1, x0, [x0]
	ret

	.globl	_atomic_xchg_64_relaxed
	.p2align	2
_atomic_xchg_64_relaxed:
	swp	x1, x0, [x0]
	ret

	.globl	_atomic_xchg_64_release
	.p2align	2
_atomic_xchg_64_release:
	swpl	x1, x0, [x0]
	ret

	.globl	_atomic_xchg_64_seqcst
	.p2align	2
_atomic_xchg_64_seqcst:
	swpal	x1, x0, [x0]
	ret

	.globl	_atomic_xchg_8_acqrel
	.p2align	2
_atomic_xchg_8_acqrel:
	swpalb	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_8_acquire
	.p2align	2
_atomic_xchg_8_acquire:
	swpab	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_8_relaxed
	.p2align	2
_atomic_xchg_8_relaxed:
	swpb	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_8_release
	.p2align	2
_atomic_xchg_8_release:
	swplb	w1, w0, [x0]
	ret

	.globl	_atomic_xchg_8_seqcst
	.p2align	2
_atomic_xchg_8_seqcst:
	swpalb	w1, w0, [x0]
	ret

	.globl	_atomic_xor_128_acqrel
	.p2align	2
_atomic_xor_128_acqrel:
	ldp	x4, x5, [x0]
LBB264_1:
	mov	x7, x5
	mov	x6, x4
	eor	x8, x4, x1
	eor	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB264_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xor_128_acquire
	.p2align	2
_atomic_xor_128_acquire:
	ldp	x4, x5, [x0]
LBB265_1:
	mov	x7, x5
	mov	x6, x4
	eor	x8, x4, x1
	eor	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspa	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB265_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xor_128_relaxed
	.p2align	2
_atomic_xor_128_relaxed:
	ldp	x4, x5, [x0]
LBB266_1:
	mov	x7, x5
	mov	x6, x4
	eor	x8, x4, x1
	eor	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	casp	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB266_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xor_128_release
	.p2align	2
_atomic_xor_128_release:
	ldp	x4, x5, [x0]
LBB267_1:
	mov	x7, x5
	mov	x6, x4
	eor	x8, x4, x1
	eor	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspl	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB267_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xor_128_seqcst
	.p2align	2
_atomic_xor_128_seqcst:
	ldp	x4, x5, [x0]
LBB268_1:
	mov	x7, x5
	mov	x6, x4
	eor	x8, x4, x1
	eor	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB268_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xor_16_acqrel
	.p2align	2
_atomic_xor_16_acqrel:
	ldeoralh	w1, w0, [x0]
	ret

	.globl	_atomic_xor_16_acquire
	.p2align	2
_atomic_xor_16_acquire:
	ldeorah	w1, w0, [x0]
	ret

	.globl	_atomic_xor_16_relaxed
	.p2align	2
_atomic_xor_16_relaxed:
	ldeorh	w1, w0, [x0]
	ret

	.globl	_atomic_xor_16_release
	.p2align	2
_atomic_xor_16_release:
	ldeorlh	w1, w0, [x0]
	ret

	.globl	_atomic_xor_16_seqcst
	.p2align	2
_atomic_xor_16_seqcst:
	ldeoralh	w1, w0, [x0]
	ret

	.globl	_atomic_xor_32_acqrel
	.p2align	2
_atomic_xor_32_acqrel:
	ldeoral	w1, w0, [x0]
	ret

	.globl	_atomic_xor_32_acquire
	.p2align	2
_atomic_xor_32_acquire:
	ldeora	w1, w0, [x0]
	ret

	.globl	_atomic_xor_32_relaxed
	.p2align	2
_atomic_xor_32_relaxed:
	ldeor	w1, w0, [x0]
	ret

	.globl	_atomic_xor_32_release
	.p2align	2
_atomic_xor_32_release:
	ldeorl	w1, w0, [x0]
	ret

	.globl	_atomic_xor_32_seqcst
	.p2align	2
_atomic_xor_32_seqcst:
	ldeoral	w1, w0, [x0]
	ret

	.globl	_atomic_xor_64_acqrel
	.p2align	2
_atomic_xor_64_acqrel:
	ldeoral	x1, x0, [x0]
	ret

	.globl	_atomic_xor_64_acquire
	.p2align	2
_atomic_xor_64_acquire:
	ldeora	x1, x0, [x0]
	ret

	.globl	_atomic_xor_64_relaxed
	.p2align	2
_atomic_xor_64_relaxed:
	ldeor	x1, x0, [x0]
	ret

	.globl	_atomic_xor_64_release
	.p2align	2
_atomic_xor_64_release:
	ldeorl	x1, x0, [x0]
	ret

	.globl	_atomic_xor_64_seqcst
	.p2align	2
_atomic_xor_64_seqcst:
	ldeoral	x1, x0, [x0]
	ret

	.globl	_atomic_xor_8_acqrel
	.p2align	2
_atomic_xor_8_acqrel:
	ldeoralb	w1, w0, [x0]
	ret

	.globl	_atomic_xor_8_acquire
	.p2align	2
_atomic_xor_8_acquire:
	ldeorab	w1, w0, [x0]
	ret

	.globl	_atomic_xor_8_relaxed
	.p2align	2
_atomic_xor_8_relaxed:
	ldeorb	w1, w0, [x0]
	ret

	.globl	_atomic_xor_8_release
	.p2align	2
_atomic_xor_8_release:
	ldeorlb	w1, w0, [x0]
	ret

	.globl	_atomic_xor_8_seqcst
	.p2align	2
_atomic_xor_8_seqcst:
	ldeoralb	w1, w0, [x0]
	ret

	.globl	_atomic_xsub_128_acqrel
	.p2align	2
_atomic_xsub_128_acqrel:
	ldp	x4, x5, [x0]
LBB289_1:
	mov	x7, x5
	mov	x6, x4
	subs	x8, x4, x1
	sbc	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB289_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xsub_128_acquire
	.p2align	2
_atomic_xsub_128_acquire:
	ldp	x4, x5, [x0]
LBB290_1:
	mov	x7, x5
	mov	x6, x4
	subs	x8, x4, x1
	sbc	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspa	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB290_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xsub_128_relaxed
	.p2align	2
_atomic_xsub_128_relaxed:
	ldp	x4, x5, [x0]
LBB291_1:
	mov	x7, x5
	mov	x6, x4
	subs	x8, x4, x1
	sbc	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	casp	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB291_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xsub_128_release
	.p2align	2
_atomic_xsub_128_release:
	ldp	x4, x5, [x0]
LBB292_1:
	mov	x7, x5
	mov	x6, x4
	subs	x8, x4, x1
	sbc	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspl	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB292_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xsub_128_seqcst
	.p2align	2
_atomic_xsub_128_seqcst:
	ldp	x4, x5, [x0]
LBB293_1:
	mov	x7, x5
	mov	x6, x4
	subs	x8, x4, x1
	sbc	x9, x7, x2
	mov	x4, x6
	mov	x5, x7
	caspal	x4, x5, x8, x9, [x0]
	cmp	x5, x7
	ccmp	x4, x6, #0, eq
	b.ne	LBB293_1
	mov	x0, x4
	mov	x1, x5
	ret

	.globl	_atomic_xsub_16_acqrel
	.p2align	2
_atomic_xsub_16_acqrel:
	neg	w8, w1
	ldaddalh	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_16_acquire
	.p2align	2
_atomic_xsub_16_acquire:
	neg	w8, w1
	ldaddah	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_16_relaxed
	.p2align	2
_atomic_xsub_16_relaxed:
	neg	w8, w1
	ldaddh	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_16_release
	.p2align	2
_atomic_xsub_16_release:
	neg	w8, w1
	ldaddlh	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_16_seqcst
	.p2align	2
_atomic_xsub_16_seqcst:
	neg	w8, w1
	ldaddalh	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_32_acqrel
	.p2align	2
_atomic_xsub_32_acqrel:
	neg	w8, w1
	ldaddal	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_32_acquire
	.p2align	2
_atomic_xsub_32_acquire:
	neg	w8, w1
	ldadda	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_32_relaxed
	.p2align	2
_atomic_xsub_32_relaxed:
	neg	w8, w1
	ldadd	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_32_release
	.p2align	2
_atomic_xsub_32_release:
	neg	w8, w1
	ldaddl	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_32_seqcst
	.p2align	2
_atomic_xsub_32_seqcst:
	neg	w8, w1
	ldaddal	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_64_acqrel
	.p2align	2
_atomic_xsub_64_acqrel:
	neg	x8, x1
	ldaddal	x8, x0, [x0]
	ret

	.globl	_atomic_xsub_64_acquire
	.p2align	2
_atomic_xsub_64_acquire:
	neg	x8, x1
	ldadda	x8, x0, [x0]
	ret

	.globl	_atomic_xsub_64_relaxed
	.p2align	2
_atomic_xsub_64_relaxed:
	neg	x8, x1
	ldadd	x8, x0, [x0]
	ret

	.globl	_atomic_xsub_64_release
	.p2align	2
_atomic_xsub_64_release:
	neg	x8, x1
	ldaddl	x8, x0, [x0]
	ret

	.globl	_atomic_xsub_64_seqcst
	.p2align	2
_atomic_xsub_64_seqcst:
	neg	x8, x1
	ldaddal	x8, x0, [x0]
	ret

	.globl	_atomic_xsub_8_acqrel
	.p2align	2
_atomic_xsub_8_acqrel:
	neg	w8, w1
	ldaddalb	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_8_acquire
	.p2align	2
_atomic_xsub_8_acquire:
	neg	w8, w1
	ldaddab	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_8_relaxed
	.p2align	2
_atomic_xsub_8_relaxed:
	neg	w8, w1
	ldaddb	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_8_release
	.p2align	2
_atomic_xsub_8_release:
	neg	w8, w1
	ldaddlb	w8, w0, [x0]
	ret

	.globl	_atomic_xsub_8_seqcst
	.p2align	2
_atomic_xsub_8_seqcst:
	neg	w8, w1
	ldaddalb	w8, w0, [x0]
	ret

	.globl	_cxchg_128_acqrel_acquire
	.p2align	2
_cxchg_128_acqrel_acquire:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	caspal	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchg_128_acquire_acquire
	.p2align	2
_cxchg_128_acquire_acquire:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	caspa	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchg_128_relaxed_relaxed
	.p2align	2
_cxchg_128_relaxed_relaxed:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	casp	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchg_128_release_relaxed
	.p2align	2
_cxchg_128_release_relaxed:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	caspl	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchg_128_seqcst_relaxed
	.p2align	2
_cxchg_128_seqcst_relaxed:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	caspal	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchg_128_seqcst_seqcst
	.p2align	2
_cxchg_128_seqcst_seqcst:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	caspal	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchg_16_acqrel_acquire
	.p2align	2
_cxchg_16_acqrel_acquire:
	mov	x8, x1
	casalh	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_16_acquire_acquire
	.p2align	2
_cxchg_16_acquire_acquire:
	mov	x8, x1
	casah	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_16_relaxed_relaxed
	.p2align	2
_cxchg_16_relaxed_relaxed:
	mov	x8, x1
	cash	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_16_release_relaxed
	.p2align	2
_cxchg_16_release_relaxed:
	mov	x8, x1
	caslh	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_16_seqcst_relaxed
	.p2align	2
_cxchg_16_seqcst_relaxed:
	mov	x8, x1
	casalh	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_16_seqcst_seqcst
	.p2align	2
_cxchg_16_seqcst_seqcst:
	mov	x8, x1
	casalh	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_32_acqrel_acquire
	.p2align	2
_cxchg_32_acqrel_acquire:
	mov	x8, x1
	casal	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_32_acquire_acquire
	.p2align	2
_cxchg_32_acquire_acquire:
	mov	x8, x1
	casa	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_32_relaxed_relaxed
	.p2align	2
_cxchg_32_relaxed_relaxed:
	mov	x8, x1
	cas	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_32_release_relaxed
	.p2align	2
_cxchg_32_release_relaxed:
	mov	x8, x1
	casl	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_32_seqcst_relaxed
	.p2align	2
_cxchg_32_seqcst_relaxed:
	mov	x8, x1
	casal	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_32_seqcst_seqcst
	.p2align	2
_cxchg_32_seqcst_seqcst:
	mov	x8, x1
	casal	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_64_acqrel_acquire
	.p2align	2
_cxchg_64_acqrel_acquire:
	mov	x8, x1
	casal	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_64_acquire_acquire
	.p2align	2
_cxchg_64_acquire_acquire:
	mov	x8, x1
	casa	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_64_relaxed_relaxed
	.p2align	2
_cxchg_64_relaxed_relaxed:
	mov	x8, x1
	cas	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_64_release_relaxed
	.p2align	2
_cxchg_64_release_relaxed:
	mov	x8, x1
	casl	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_64_seqcst_relaxed
	.p2align	2
_cxchg_64_seqcst_relaxed:
	mov	x8, x1
	casal	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_64_seqcst_seqcst
	.p2align	2
_cxchg_64_seqcst_seqcst:
	mov	x8, x1
	casal	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_8_acqrel_acquire
	.p2align	2
_cxchg_8_acqrel_acquire:
	mov	x8, x1
	casalb	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_8_acquire_acquire
	.p2align	2
_cxchg_8_acquire_acquire:
	mov	x8, x1
	casab	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_8_relaxed_relaxed
	.p2align	2
_cxchg_8_relaxed_relaxed:
	mov	x8, x1
	casb	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_8_release_relaxed
	.p2align	2
_cxchg_8_release_relaxed:
	mov	x8, x1
	caslb	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_8_seqcst_relaxed
	.p2align	2
_cxchg_8_seqcst_relaxed:
	mov	x8, x1
	casalb	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchg_8_seqcst_seqcst
	.p2align	2
_cxchg_8_seqcst_seqcst:
	mov	x8, x1
	casalb	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_128_acqrel_acquire
	.p2align	2
_cxchgweak_128_acqrel_acquire:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	caspal	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchgweak_128_acquire_acquire
	.p2align	2
_cxchgweak_128_acquire_acquire:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	caspa	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchgweak_128_relaxed_relaxed
	.p2align	2
_cxchgweak_128_relaxed_relaxed:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	casp	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchgweak_128_release_relaxed
	.p2align	2
_cxchgweak_128_release_relaxed:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	caspl	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchgweak_128_seqcst_relaxed
	.p2align	2
_cxchgweak_128_seqcst_relaxed:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	caspal	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchgweak_128_seqcst_seqcst
	.p2align	2
_cxchgweak_128_seqcst_seqcst:
	mov	x5, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x6, x2
	mov	x7, x3
	caspal	x6, x7, x4, x5, [x0]
	cmp	x6, x1
	ccmp	x7, x3, #0, eq
	cset	w9, eq
	stp	x6, x7, [x8]
	strb	w9, [x8, #16]
	ret

	.globl	_cxchgweak_16_acqrel_acquire
	.p2align	2
_cxchgweak_16_acqrel_acquire:
	mov	x8, x1
	casalh	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_16_acquire_acquire
	.p2align	2
_cxchgweak_16_acquire_acquire:
	mov	x8, x1
	casah	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_16_relaxed_relaxed
	.p2align	2
_cxchgweak_16_relaxed_relaxed:
	mov	x8, x1
	cash	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_16_release_relaxed
	.p2align	2
_cxchgweak_16_release_relaxed:
	mov	x8, x1
	caslh	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_16_seqcst_relaxed
	.p2align	2
_cxchgweak_16_seqcst_relaxed:
	mov	x8, x1
	casalh	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_16_seqcst_seqcst
	.p2align	2
_cxchgweak_16_seqcst_seqcst:
	mov	x8, x1
	casalh	w8, w2, [x0]
	cmp	w8, w1, uxth
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_32_acqrel_acquire
	.p2align	2
_cxchgweak_32_acqrel_acquire:
	mov	x8, x1
	casal	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_32_acquire_acquire
	.p2align	2
_cxchgweak_32_acquire_acquire:
	mov	x8, x1
	casa	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_32_relaxed_relaxed
	.p2align	2
_cxchgweak_32_relaxed_relaxed:
	mov	x8, x1
	cas	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_32_release_relaxed
	.p2align	2
_cxchgweak_32_release_relaxed:
	mov	x8, x1
	casl	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_32_seqcst_relaxed
	.p2align	2
_cxchgweak_32_seqcst_relaxed:
	mov	x8, x1
	casal	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_32_seqcst_seqcst
	.p2align	2
_cxchgweak_32_seqcst_seqcst:
	mov	x8, x1
	casal	w8, w2, [x0]
	cmp	w8, w1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_64_acqrel_acquire
	.p2align	2
_cxchgweak_64_acqrel_acquire:
	mov	x8, x1
	casal	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_64_acquire_acquire
	.p2align	2
_cxchgweak_64_acquire_acquire:
	mov	x8, x1
	casa	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_64_relaxed_relaxed
	.p2align	2
_cxchgweak_64_relaxed_relaxed:
	mov	x8, x1
	cas	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_64_release_relaxed
	.p2align	2
_cxchgweak_64_release_relaxed:
	mov	x8, x1
	casl	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_64_seqcst_relaxed
	.p2align	2
_cxchgweak_64_seqcst_relaxed:
	mov	x8, x1
	casal	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_64_seqcst_seqcst
	.p2align	2
_cxchgweak_64_seqcst_seqcst:
	mov	x8, x1
	casal	x8, x2, [x0]
	cmp	x8, x1
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_8_acqrel_acquire
	.p2align	2
_cxchgweak_8_acqrel_acquire:
	mov	x8, x1
	casalb	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_8_acquire_acquire
	.p2align	2
_cxchgweak_8_acquire_acquire:
	mov	x8, x1
	casab	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_8_relaxed_relaxed
	.p2align	2
_cxchgweak_8_relaxed_relaxed:
	mov	x8, x1
	casb	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_8_release_relaxed
	.p2align	2
_cxchgweak_8_release_relaxed:
	mov	x8, x1
	caslb	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_8_seqcst_relaxed
	.p2align	2
_cxchgweak_8_seqcst_relaxed:
	mov	x8, x1
	casalb	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

	.globl	_cxchgweak_8_seqcst_seqcst
	.p2align	2
_cxchgweak_8_seqcst_seqcst:
	mov	x8, x1
	casalb	w8, w2, [x0]
	cmp	w8, w1, uxtb
	cset	w1, eq
	mov	x0, x8
	ret

.subsections_via_symbols
