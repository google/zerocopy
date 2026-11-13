	.file	"unwind_probe.e45a91751a911c8a-cgu.0"
	.section	.text._RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_,@function
_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_:
	.cfi_startproc
	b	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
.Lfunc_end0:
	.size	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_, .Lfunc_end0-_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_
	.cfi_endproc

	.section	.text._RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop,"ax",@progbits
	.globl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
	.p2align	2
	.type	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop,@function
_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop:
	.cfi_startproc
	ldr	x8, [x0]
	mov	w10, #10
	ldr	w11, [x0, #8]
	ldr	w9, [x8]
	madd	w9, w9, w10, w11
	str	w9, [x8]
	ret
.Lfunc_end1:
	.size	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop, .Lfunc_end1-_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
	.cfi_endproc

	.section	.text.catch_unwind_entry,"ax",@progbits
	.globl	catch_unwind_entry
	.p2align	2
	.type	catch_unwind_entry,@function
catch_unwind_entry:
.Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 156, DW.ref.rust_eh_personality
	.cfi_lsda 28, .Lexception0
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
	.cfi_remember_state
.Ltmp0:
	bl	nested_cleanups
.Ltmp1:
.LBB2_1:
	mov	w0, wzr
.LBB2_2:
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
.LBB2_3:
	.cfi_restore_state
.Ltmp2:
.Ltmp3:
	bl	_RNvNvNtCs9g4b2IXPNZ3_3std9panicking12catch_unwind7cleanup
.Ltmp4:
	mov	x19, x0
	cbz	x0, .LBB2_1
	ldr	x8, [x1]
	mov	x20, x1
	cbz	x8, .LBB2_7
.Ltmp6:
	mov	x0, x19
	blr	x8
.Ltmp7:
.LBB2_7:
	ldr	x1, [x20, #8]
	cbz	x1, .LBB2_9
	ldr	x2, [x20, #16]
	mov	x0, x19
	bl	_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
.LBB2_9:
	mov	w0, #1
	b	.LBB2_2
.LBB2_10:
.Ltmp8:
	ldr	x1, [x20, #8]
	mov	x21, x0
	cbz	x1, .LBB2_12
	ldr	x2, [x20, #16]
	mov	x0, x19
	bl	_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
.LBB2_12:
	mov	x0, x21
	bl	_Unwind_Resume
.LBB2_13:
.Ltmp5:
	bl	_RNvNtCsaWcbhsS8OaW_4core9panicking19panic_cannot_unwind
.Lfunc_end2:
	.size	catch_unwind_entry, .Lfunc_end2-catch_unwind_entry
	.cfi_endproc
	.section	.gcc_except_table.catch_unwind_entry,"a",@progbits
	.p2align	2, 0x0
GCC_except_table2:
.Lexception0:
	.byte	255
	.byte	156
	.uleb128 .Lttbase0-.Lttbaseref0
.Lttbaseref0:
	.byte	1
	.uleb128 .Lcst_end0-.Lcst_begin0
.Lcst_begin0:
	.uleb128 .Ltmp0-.Lfunc_begin0
	.uleb128 .Ltmp1-.Ltmp0
	.uleb128 .Ltmp2-.Lfunc_begin0
	.byte	3
	.uleb128 .Ltmp3-.Lfunc_begin0
	.uleb128 .Ltmp4-.Ltmp3
	.uleb128 .Ltmp5-.Lfunc_begin0
	.byte	1
	.uleb128 .Ltmp6-.Lfunc_begin0
	.uleb128 .Ltmp7-.Ltmp6
	.uleb128 .Ltmp8-.Lfunc_begin0
	.byte	0
	.uleb128 .Ltmp7-.Lfunc_begin0
	.uleb128 .Lfunc_end2-.Ltmp7
	.byte	0
	.byte	0
.Lcst_end0:
	.byte	127
	.byte	0
	.byte	1
	.byte	0
	.p2align	2, 0x0
	.xword	0
.Lttbase0:
	.byte	0
	.p2align	2, 0x0

	.section	.text.frameless_leaf,"ax",@progbits
	.globl	frameless_leaf
	.p2align	2
	.type	frameless_leaf,@function
frameless_leaf:
	.cfi_startproc
	add	x0, x0, #42
	ret
.Lfunc_end3:
	.size	frameless_leaf, .Lfunc_end3-frameless_leaf
	.cfi_endproc

	.section	.text.nested_cleanups,"ax",@progbits
	.globl	nested_cleanups
	.p2align	2
	.type	nested_cleanups,@function
nested_cleanups:
.Lfunc_begin1:
	.cfi_startproc
	.cfi_personality 156, DW.ref.rust_eh_personality
	.cfi_lsda 28, .Lexception1
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	stp	x29, x30, [sp, #32]
	str	x19, [sp, #48]
	add	x29, sp, #32
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	.cfi_remember_state
	mov	w8, #1
	str	x0, [sp]
	str	w8, [sp, #8]
	mov	w8, #2
	str	x0, [sp, #16]
	str	w8, [sp, #24]
.Ltmp9:
	blr	x1
.Ltmp10:
	add	x0, sp, #16
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
	mov	x0, sp
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
	.cfi_def_cfa wsp, 64
	ldp	x29, x30, [sp, #32]
	ldr	x19, [sp, #48]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB4_2:
	.cfi_restore_state
.Ltmp11:
	mov	x19, x0
	add	x0, sp, #16
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
	mov	x0, sp
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
	mov	x0, x19
	bl	_Unwind_Resume
.Lfunc_end4:
	.size	nested_cleanups, .Lfunc_end4-nested_cleanups
	.cfi_endproc
	.section	.gcc_except_table.nested_cleanups,"a",@progbits
	.p2align	2, 0x0
GCC_except_table4:
.Lexception1:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end1-.Lcst_begin1
.Lcst_begin1:
	.uleb128 .Ltmp9-.Lfunc_begin1
	.uleb128 .Ltmp10-.Ltmp9
	.uleb128 .Ltmp11-.Lfunc_begin1
	.byte	0
	.uleb128 .Ltmp10-.Lfunc_begin1
	.uleb128 .Lfunc_end4-.Ltmp10
	.byte	0
	.byte	0
.Lcst_end1:
	.p2align	2, 0x0

	.section	.text.nounwind_c_boundary,"ax",@progbits
	.globl	nounwind_c_boundary
	.p2align	2
	.type	nounwind_c_boundary,@function
nounwind_c_boundary:
.Lfunc_begin2:
	.cfi_startproc
	.cfi_personality 156, DW.ref.rust_eh_personality
	.cfi_lsda 28, .Lexception2
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_remember_state
	mov	w8, #9
	str	x0, [sp]
	str	w8, [sp, #8]
.Ltmp12:
	blr	x1
.Ltmp13:
	mov	x0, sp
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB5_2:
	.cfi_restore_state
.Ltmp14:
	mov	x0, sp
	bl	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_
	bl	_RNvNtCsaWcbhsS8OaW_4core9panicking19panic_cannot_unwind
.Lfunc_end5:
	.size	nounwind_c_boundary, .Lfunc_end5-nounwind_c_boundary
	.cfi_endproc
	.section	.gcc_except_table.nounwind_c_boundary,"a",@progbits
	.p2align	2, 0x0
GCC_except_table5:
.Lexception2:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end2-.Lcst_begin2
.Lcst_begin2:
	.uleb128 .Ltmp12-.Lfunc_begin2
	.uleb128 .Ltmp13-.Ltmp12
	.uleb128 .Ltmp14-.Lfunc_begin2
	.byte	0
.Lcst_end2:
	.p2align	2, 0x0

	.section	.text.passthrough_no_cleanup,"ax",@progbits
	.globl	passthrough_no_cleanup
	.p2align	2
	.type	passthrough_no_cleanup,@function
passthrough_no_cleanup:
	.cfi_startproc
	br	x0
.Lfunc_end6:
	.size	passthrough_no_cleanup, .Lfunc_end6-passthrough_no_cleanup
	.cfi_endproc

	.hidden	DW.ref.rust_eh_personality
	.weak	DW.ref.rust_eh_personality
	.section	.data.DW.ref.rust_eh_personality,"awG",@progbits,DW.ref.rust_eh_personality,comdat
	.p2align	3, 0x0
	.type	DW.ref.rust_eh_personality,@object
	.size	DW.ref.rust_eh_personality, 8
DW.ref.rust_eh_personality:
	.xword	rust_eh_personality
	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
