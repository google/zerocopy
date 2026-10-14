	.globl	_anneal_publish_relaxed
_anneal_publish_relaxed:
	mov	w8, #1
	str	w8, [x0]
	str	w8, [x1]
	ret
	.globl	_anneal_publish_release
_anneal_publish_release:
	mov	w8, #1
	str	w8, [x0]
	stlr	w8, [x1]
	ret
	.globl	_anneal_observe_relaxed
_anneal_observe_relaxed:
	ldr	w8, [x1]
	ldr	w9, [x0]
	orr	x0, x9, x8, lsl #32
	ret
	.globl	_anneal_observe_acquire
_anneal_observe_acquire:
	ldapr	w8, [x1]
	ldr	w9, [x0]
	orr	x0, x9, x8, lsl #32
	ret
	.globl	_anneal_sb_relaxed
_anneal_sb_relaxed:
	mov	w8, #1
	str	w8, [x0]
	ldr	w0, [x1]
	ret
	.globl	_anneal_sb_ra
_anneal_sb_ra:
	mov	w8, #1
	stlr	w8, [x0]
	ldapr	w0, [x1]
	ret
	.globl	_anneal_sb_sc
_anneal_sb_sc:
	mov	w8, #1
	stlr	w8, [x0]
	ldar	w0, [x1]
	ret
	.globl	_anneal_sb_fence
_anneal_sb_fence:
	mov	w8, #1
	str	w8, [x0]
	dmb	ish
	ldr	w0, [x1]
	ret