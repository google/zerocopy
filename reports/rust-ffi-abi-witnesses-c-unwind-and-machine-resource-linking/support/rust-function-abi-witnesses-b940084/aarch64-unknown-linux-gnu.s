	.file	"abi_witness.c"
	.text
	.globl	abi_add                         // -- Begin function abi_add
	.p2align	2
	.type	abi_add,@function
abi_add:                                // @abi_add
	.cfi_startproc
// %bb.0:
	add	x0, x1, x0
	ret
.Lfunc_end0:
	.size	abi_add, .Lfunc_end0-abi_add
	.cfi_endproc
                                        // -- End function
	.globl	abi_pair                        // -- Begin function abi_pair
	.p2align	2
	.type	abi_pair,@function
abi_pair:                               // @abi_pair
	.cfi_startproc
// %bb.0:
	mov	x8, x0
	mov	x0, x1
	mov	x1, x8
	ret
.Lfunc_end1:
	.size	abi_pair, .Lfunc_end1-abi_pair
	.cfi_endproc
                                        // -- End function
	.globl	abi_triple                      // -- Begin function abi_triple
	.p2align	2
	.type	abi_triple,@function
abi_triple:                             // @abi_triple
	.cfi_startproc
// %bb.0:
	ldur	q0, [x0, #8]
	ldr	x9, [x0]
	ext	v0.16b, v0.16b, v0.16b, #8
	str	x9, [x8, #16]
	str	q0, [x8]
	ret
.Lfunc_end2:
	.size	abi_triple, .Lfunc_end2-abi_triple
	.cfi_endproc
                                        // -- End function
	.ident	"Apple clang version 21.0.0 (clang-2100.3.34.2)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
