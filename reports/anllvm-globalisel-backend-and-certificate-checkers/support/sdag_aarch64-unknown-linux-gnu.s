	.file	"backend_probe.ll"
	.text
	.globl	add_u128_and_u8                 // -- Begin function add_u128_and_u8
	.p2align	2
	.type	add_u128_and_u8,@function
add_u128_and_u8:                        // @add_u128_and_u8
// %bb.0:                               // %entry
	adds	x8, x0, x2
	add	w9, w4, w5
	adc	x10, x1, x3
	adds	x0, x8, w9, uxtb
	cinc	x1, x10, hs
	ret
.Lfunc_end0:
	.size	add_u128_and_u8, .Lfunc_end0-add_u128_and_u8
                                        // -- End function
	.globl	gep_load_select                 // -- Begin function gep_load_select
	.p2align	2
	.type	gep_load_select,@function
gep_load_select:                        // @gep_load_select
// %bb.0:                               // %entry
	cmp	x1, x2
	b.hs	.LBB1_2
// %bb.1:                               // %in_bounds
	ldr	x8, [x0, x1, lsl #3]
	cmp	x8, x3
	csel	x3, x8, x3, hi
.LBB1_2:                                // %exit
	mov	x0, x3
	ret
.Lfunc_end1:
	.size	gep_load_select, .Lfunc_end1-gep_load_select
                                        // -- End function
	.section	".note.GNU-stack","",@progbits
