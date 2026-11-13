	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RINvNtCs3bJEMBXHbwl_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_:
	.cfi_startproc
	b	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
	.cfi_endproc

	.globl	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
	.p2align	2
__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop:
	.cfi_startproc
	ldr	x8, [x0]
	ldr	w9, [x8]
	mov	w10, #10
	ldr	w11, [x0, #8]
	madd	w9, w9, w10, w11
	str	w9, [x8]
	ret
	.cfi_endproc

	.globl	_catch_unwind_entry
	.p2align	2
_catch_unwind_entry:
Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception0
	stp	x22, x21, [sp, #-48]!
	stp	x20, x19, [sp, #16]
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
Ltmp0:
	bl	_nested_cleanups
Ltmp1:
LBB2_1:
	mov	w0, #0
LBB2_2:
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	ldp	x22, x21, [sp], #48
	ret
LBB2_3:
Ltmp2:
Ltmp3:
	bl	__RNvNvNtCsdnanKjkF2cC_3std9panicking12catch_unwind7cleanup
Ltmp4:
	mov	x19, x0
	cbz	x0, LBB2_1
	mov	x20, x1
	ldr	x8, [x1]
	cbz	x8, LBB2_7
Ltmp6:
	mov	x0, x19
	blr	x8
Ltmp7:
LBB2_7:
	ldr	x1, [x20, #8]
	cbz	x1, LBB2_9
	ldr	x2, [x20, #16]
	mov	x0, x19
	bl	__RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
LBB2_9:
	mov	w0, #1
	b	LBB2_2
LBB2_10:
Ltmp8:
	mov	x21, x0
	ldr	x1, [x20, #8]
	cbz	x1, LBB2_12
	ldr	x2, [x20, #16]
	mov	x0, x19
	bl	__RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
LBB2_12:
	mov	x0, x21
	bl	__Unwind_Resume
LBB2_13:
Ltmp5:
	bl	__RNvNtCs3bJEMBXHbwl_4core9panicking19panic_cannot_unwind
Lfunc_end0:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table2:
Lexception0:
	.byte	255
	.byte	155
	.uleb128 Lttbase0-Lttbaseref0
Lttbaseref0:
	.byte	1
	.uleb128 Lcst_end0-Lcst_begin0
Lcst_begin0:
	.uleb128 Ltmp0-Lfunc_begin0
	.uleb128 Ltmp1-Ltmp0
	.uleb128 Ltmp2-Lfunc_begin0
	.byte	3
	.uleb128 Ltmp3-Lfunc_begin0
	.uleb128 Ltmp4-Ltmp3
	.uleb128 Ltmp5-Lfunc_begin0
	.byte	1
	.uleb128 Ltmp6-Lfunc_begin0
	.uleb128 Ltmp7-Ltmp6
	.uleb128 Ltmp8-Lfunc_begin0
	.byte	0
	.uleb128 Ltmp7-Lfunc_begin0
	.uleb128 Lfunc_end0-Ltmp7
	.byte	0
	.byte	0
Lcst_end0:
	.byte	127
	.byte	0
	.byte	1
	.byte	0
	.p2align	2, 0x0
	.long	0
Lttbase0:
	.byte	0
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.globl	_frameless_leaf
	.p2align	2
_frameless_leaf:
	.cfi_startproc
	add	x0, x0, #42
	ret
	.cfi_endproc

	.globl	_nested_cleanups
	.p2align	2
_nested_cleanups:
Lfunc_begin1:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception1
	sub	sp, sp, #64
	stp	x20, x19, [sp, #32]
	stp	x29, x30, [sp, #48]
	add	x29, sp, #48
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	str	x0, [sp]
	mov	w8, #1
	str	w8, [sp, #8]
	str	x0, [sp, #16]
	mov	w8, #2
	str	w8, [sp, #24]
Ltmp9:
	blr	x1
Ltmp10:
	add	x0, sp, #16
	bl	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
	mov	x0, sp
	bl	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
	ldp	x29, x30, [sp, #48]
	ldp	x20, x19, [sp, #32]
	add	sp, sp, #64
	ret
LBB4_2:
Ltmp11:
	mov	x19, x0
	add	x0, sp, #16
	bl	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
	mov	x0, sp
	bl	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
	mov	x0, x19
	bl	__Unwind_Resume
Lfunc_end1:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table4:
Lexception1:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 Lcst_end1-Lcst_begin1
Lcst_begin1:
	.uleb128 Ltmp9-Lfunc_begin1
	.uleb128 Ltmp10-Ltmp9
	.uleb128 Ltmp11-Lfunc_begin1
	.byte	0
	.uleb128 Ltmp10-Lfunc_begin1
	.uleb128 Lfunc_end1-Ltmp10
	.byte	0
	.byte	0
Lcst_end1:
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.globl	_nounwind_c_boundary
	.p2align	2
_nounwind_c_boundary:
Lfunc_begin2:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception2
	sub	sp, sp, #32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	str	x0, [sp]
	mov	w8, #9
	str	w8, [sp, #8]
Ltmp12:
	blr	x1
Ltmp13:
	mov	x0, sp
	bl	__RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	ret
LBB5_2:
Ltmp14:
	mov	x0, sp
	bl	__RINvNtCs3bJEMBXHbwl_4core3ptr9drop_glueNtCsjBwlT6cN9ry_12unwind_probe11DropTrackerEBD_
	bl	__RNvNtCs3bJEMBXHbwl_4core9panicking19panic_cannot_unwind
Lfunc_end2:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table5:
Lexception2:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 Lcst_end2-Lcst_begin2
Lcst_begin2:
	.uleb128 Ltmp12-Lfunc_begin2
	.uleb128 Ltmp13-Ltmp12
	.uleb128 Ltmp14-Lfunc_begin2
	.byte	0
Lcst_end2:
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.globl	_passthrough_no_cleanup
	.p2align	2
_passthrough_no_cleanup:
	.cfi_startproc
	br	x0
	.cfi_endproc

	.globl	_passthrough_with_frame
	.p2align	2
_passthrough_with_frame:
	.cfi_startproc
	stp	x20, x19, [sp, #-32]!
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	mov	x19, x0
	blr	x1
	add	x0, x0, x19
	ldp	x29, x30, [sp, #16]
	ldp	x20, x19, [sp], #32
	ret
	.cfi_endproc

	.globl	_simple_nonleaf_call
	.p2align	2
_simple_nonleaf_call:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	blr	x0
	add	x0, x0, #1
	ldp	x29, x30, [sp], #16
	ret
	.cfi_endproc

.subsections_via_symbols
