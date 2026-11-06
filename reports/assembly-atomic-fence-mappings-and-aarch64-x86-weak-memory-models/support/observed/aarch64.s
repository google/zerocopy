	.file	"atomics.c"
	.text
	.globl	load_relaxed                    // -- Begin function load_relaxed
	.p2align	2
	.type	load_relaxed,@function
load_relaxed:                           // @load_relaxed
// %bb.0:
	ldr	x0, [x0]
	ret
.Lfunc_end0:
	.size	load_relaxed, .Lfunc_end0-load_relaxed
                                        // -- End function
	.globl	load_acquire                    // -- Begin function load_acquire
	.p2align	2
	.type	load_acquire,@function
load_acquire:                           // @load_acquire
// %bb.0:
	ldar	x0, [x0]
	ret
.Lfunc_end1:
	.size	load_acquire, .Lfunc_end1-load_acquire
                                        // -- End function
	.globl	load_seq_cst                    // -- Begin function load_seq_cst
	.p2align	2
	.type	load_seq_cst,@function
load_seq_cst:                           // @load_seq_cst
// %bb.0:
	ldar	x0, [x0]
	ret
.Lfunc_end2:
	.size	load_seq_cst, .Lfunc_end2-load_seq_cst
                                        // -- End function
	.globl	store_relaxed                   // -- Begin function store_relaxed
	.p2align	2
	.type	store_relaxed,@function
store_relaxed:                          // @store_relaxed
// %bb.0:
	str	x1, [x0]
	ret
.Lfunc_end3:
	.size	store_relaxed, .Lfunc_end3-store_relaxed
                                        // -- End function
	.globl	store_release                   // -- Begin function store_release
	.p2align	2
	.type	store_release,@function
store_release:                          // @store_release
// %bb.0:
	stlr	x1, [x0]
	ret
.Lfunc_end4:
	.size	store_release, .Lfunc_end4-store_release
                                        // -- End function
	.globl	store_seq_cst                   // -- Begin function store_seq_cst
	.p2align	2
	.type	store_seq_cst,@function
store_seq_cst:                          // @store_seq_cst
// %bb.0:
	stlr	x1, [x0]
	ret
.Lfunc_end5:
	.size	store_seq_cst, .Lfunc_end5-store_seq_cst
                                        // -- End function
	.globl	add_relaxed                     // -- Begin function add_relaxed
	.p2align	2
	.type	add_relaxed,@function
add_relaxed:                            // @add_relaxed
// %bb.0:
	mov	x8, x0
.LBB6_1:                                // =>This Inner Loop Header: Depth=1
	ldxr	x0, [x8]
	add	x9, x0, x1
	stxr	w10, x9, [x8]
	cbnz	w10, .LBB6_1
// %bb.2:
	ret
.Lfunc_end6:
	.size	add_relaxed, .Lfunc_end6-add_relaxed
                                        // -- End function
	.globl	add_acq_rel                     // -- Begin function add_acq_rel
	.p2align	2
	.type	add_acq_rel,@function
add_acq_rel:                            // @add_acq_rel
// %bb.0:
	mov	x8, x0
.LBB7_1:                                // =>This Inner Loop Header: Depth=1
	ldaxr	x0, [x8]
	add	x9, x0, x1
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB7_1
// %bb.2:
	ret
.Lfunc_end7:
	.size	add_acq_rel, .Lfunc_end7-add_acq_rel
                                        // -- End function
	.globl	add_seq_cst                     // -- Begin function add_seq_cst
	.p2align	2
	.type	add_seq_cst,@function
add_seq_cst:                            // @add_seq_cst
// %bb.0:
	mov	x8, x0
.LBB8_1:                                // =>This Inner Loop Header: Depth=1
	ldaxr	x0, [x8]
	add	x9, x0, x1
	stlxr	w10, x9, [x8]
	cbnz	w10, .LBB8_1
// %bb.2:
	ret
.Lfunc_end8:
	.size	add_seq_cst, .Lfunc_end8-add_seq_cst
                                        // -- End function
	.globl	cas_acq_rel                     // -- Begin function cas_acq_rel
	.p2align	2
	.type	cas_acq_rel,@function
cas_acq_rel:                            // @cas_acq_rel
// %bb.0:
	ldr	x9, [x1]
.LBB9_1:                                // =>This Inner Loop Header: Depth=1
	ldaxr	x8, [x0]
	cmp	x8, x9
	b.ne	.LBB9_4
// %bb.2:                               //   in Loop: Header=BB9_1 Depth=1
	stlxr	w10, x2, [x0]
	cbnz	w10, .LBB9_1
// %bb.3:
	mov	w0, #1                          // =0x1
	tbz	w0, #0, .LBB9_5
	b	.LBB9_6
.LBB9_4:
	mov	w0, wzr
	clrex
	tbnz	w0, #0, .LBB9_6
.LBB9_5:
	str	x8, [x1]
.LBB9_6:
	ret
.Lfunc_end9:
	.size	cas_acq_rel, .Lfunc_end9-cas_acq_rel
                                        // -- End function
	.globl	fence_acquire                   // -- Begin function fence_acquire
	.p2align	2
	.type	fence_acquire,@function
fence_acquire:                          // @fence_acquire
// %bb.0:
	dmb	ishld
	ret
.Lfunc_end10:
	.size	fence_acquire, .Lfunc_end10-fence_acquire
                                        // -- End function
	.globl	fence_release                   // -- Begin function fence_release
	.p2align	2
	.type	fence_release,@function
fence_release:                          // @fence_release
// %bb.0:
	dmb	ish
	ret
.Lfunc_end11:
	.size	fence_release, .Lfunc_end11-fence_release
                                        // -- End function
	.globl	fence_acq_rel                   // -- Begin function fence_acq_rel
	.p2align	2
	.type	fence_acq_rel,@function
fence_acq_rel:                          // @fence_acq_rel
// %bb.0:
	dmb	ish
	ret
.Lfunc_end12:
	.size	fence_acq_rel, .Lfunc_end12-fence_acq_rel
                                        // -- End function
	.globl	fence_seq_cst                   // -- Begin function fence_seq_cst
	.p2align	2
	.type	fence_seq_cst,@function
fence_seq_cst:                          // @fence_seq_cst
// %bb.0:
	dmb	ish
	ret
.Lfunc_end13:
	.size	fence_seq_cst, .Lfunc_end13-fence_seq_cst
                                        // -- End function
	.globl	signal_seq_cst                  // -- Begin function signal_seq_cst
	.p2align	2
	.type	signal_seq_cst,@function
signal_seq_cst:                         // @signal_seq_cst
// %bb.0:
	//MEMBARRIER
	ret
.Lfunc_end14:
	.size	signal_seq_cst, .Lfunc_end14-signal_seq_cst
                                        // -- End function
	.globl	compiler_barrier                // -- Begin function compiler_barrier
	.p2align	2
	.type	compiler_barrier,@function
compiler_barrier:                       // @compiler_barrier
// %bb.0:
	//APP
	//NO_APP
	ret
.Lfunc_end15:
	.size	compiler_barrier, .Lfunc_end15-compiler_barrier
                                        // -- End function
	.globl	explicit_hw_fence               // -- Begin function explicit_hw_fence
	.p2align	2
	.type	explicit_hw_fence,@function
explicit_hw_fence:                      // @explicit_hw_fence
// %bb.0:
	//APP
	dmb	ish
	//NO_APP
	ret
.Lfunc_end16:
	.size	explicit_hw_fence, .Lfunc_end16-explicit_hw_fence
                                        // -- End function
	.ident	"Apple clang version 21.0.0 (clang-2100.3.34.2)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
