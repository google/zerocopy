	.def	"@feat.00";
	.scl	3;
	.type	0;
	.endef
	.globl	"@feat.00"
"@feat.00" = 0
	.file	"unwind_probe.e45a91751a911c8a-cgu.0"
	.def	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop,unique,0
	.globl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
	.p2align	2
_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop:
	ldr	x8, [x0]
	mov	w10, #10
	ldr	w11, [x0, #8]
	ldr	w9, [x8]
	madd	w9, w9, w10, w11
	str	w9, [x8]
	ret

	.def	catch_unwind_entry;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.globl	catch_unwind_entry
	.p2align	2
catch_unwind_entry:
.Lfunc_begin0:
.seh_proc catch_unwind_entry
	.seh_handler __CxxFrameHandler3, @unwind, @except
	sub	sp, sp, #48
	.seh_stackalloc	48
	stp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	x29, sp, #16
	.seh_add_fp	16
	.seh_endprologue
	mov	x2, #-2
	stur	x2, [x29, #16]
.Ltmp0:
	bl	nested_cleanups
.Ltmp1:
.LBB1_1:
	mov	w0, wzr
.LBB1_2:
	.seh_startepilogue
	ldp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	sp, sp, #48
	.seh_stackalloc	48
	.seh_endepilogue
	ret
.LBB1_3:
$ehgcr_1_3:
	ldur	x8, [x29, #-8]
	cbz	x8, .LBB1_1
	ldur	x8, [x29, #-16]
	ldr	x8, [x8]
	cbz	x8, .LBB1_6
.Ltmp6:
	ldur	x0, [x29, #-8]
	blr	x8
.Ltmp7:
.LBB1_6:
	ldur	x8, [x29, #-16]
	ldr	x1, [x8, #8]
	cbz	x1, .LBB1_8
	ldp	x8, x0, [x29, #-16]
	ldr	x2, [x8, #16]
	bl	_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
.LBB1_8:
	mov	w0, #1
	b	.LBB1_2
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$catch_unwind_entry@IMGREL
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.def	"?catch$9@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?catch$9@?0?catch_unwind_entry@4HA":
.seh_proc "?catch$9@?0?catch_unwind_entry@4HA"
	.seh_handler __CxxFrameHandler3, @unwind, @except
.LBB1_9:
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	.seh_endprologue
	bl	_RNvNtCsaF4MlZlPuCq_4core9panicking19panic_cannot_unwind
	brk	#0x1
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$catch_unwind_entry@IMGREL
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.def	"?catch$10@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?catch$10@?0?catch_unwind_entry@4HA":
.seh_proc "?catch$10@?0?catch_unwind_entry@4HA"
	.seh_handler __CxxFrameHandler3, @unwind, @except
.LBB1_10:
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	.seh_endprologue
	ldr	x0, [x29, #24]
.Ltmp4:
	bl	_RNvNvNtCs7wTP75QBMFn_3std9panicking12catch_unwind7cleanup
	stp	x1, x0, [x29, #-16]
.Ltmp5:
	adrp	x0, .LBB1_3
	add	x0, x0, .LBB1_3
	.seh_startepilogue
	ldp	x29, x30, [sp], #16
	.seh_save_fplr_x	16
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$catch_unwind_entry@IMGREL
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.def	"?catch$12@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?catch$12@?0?catch_unwind_entry@4HA":
.seh_proc "?catch$12@?0?catch_unwind_entry@4HA"
	.seh_handler __CxxFrameHandler3, @unwind, @except
.LBB1_12:
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	.seh_endprologue
	bl	_RNvNtCsaF4MlZlPuCq_4core9panicking19panic_cannot_unwind
	brk	#0x1
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$catch_unwind_entry@IMGREL
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.def	"?catch$13@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?catch$13@?0?catch_unwind_entry@4HA":
.seh_proc "?catch$13@?0?catch_unwind_entry@4HA"
	.seh_handler __CxxFrameHandler3, @unwind, @except
.LBB1_13:
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	.seh_endprologue
.Ltmp2:
	mov	x0, xzr
	bl	_RNvNvNtCs7wTP75QBMFn_3std9panicking12catch_unwind7cleanup
	stp	x1, x0, [x29, #-16]
.Ltmp3:
	adrp	x0, .LBB1_3
	add	x0, x0, .LBB1_3
	.seh_startepilogue
	ldp	x29, x30, [sp], #16
	.seh_save_fplr_x	16
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$catch_unwind_entry@IMGREL
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.def	"?dtor$15@?0?catch_unwind_entry@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?dtor$15@?0?catch_unwind_entry@4HA":
.seh_proc "?dtor$15@?0?catch_unwind_entry@4HA"
.LBB1_15:
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	.seh_endprologue
	ldur	x8, [x29, #-16]
	ldr	x1, [x8, #8]
	cbz	x1, .LBB1_17
	ldp	x8, x0, [x29, #-16]
	ldr	x2, [x8, #16]
	bl	_RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc
.LBB1_17:
	.seh_startepilogue
	ldp	x29, x30, [sp], #16
	.seh_save_fplr_x	16
	.seh_endepilogue
	ret
.Lfunc_end0:
	.seh_endfunclet
	.seh_handlerdata
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1
	.seh_endproc
	.section	.xdata,"dr",associative,catch_unwind_entry,unique,0
	.p2align	2, 0x0
$cppxdata$catch_unwind_entry:
	.word	429065506
	.word	7
	.word	$stateUnwindMap$catch_unwind_entry@IMGREL
	.word	3
	.word	$tryMap$catch_unwind_entry@IMGREL
	.word	12
	.word	$ip2state$catch_unwind_entry@IMGREL
	.word	-16
	.word	0
	.word	1
$stateUnwindMap$catch_unwind_entry:
	.word	-1
	.word	0
	.word	-1
	.word	0
	.word	1
	.word	0
	.word	1
	.word	0
	.word	1
	.word	0
	.word	1
	.word	0
	.word	-1
	.word	"?dtor$15@?0?catch_unwind_entry@4HA"@IMGREL
$tryMap$catch_unwind_entry:
	.word	0
	.word	0
	.word	5
	.word	2
	.word	$handlerMap$0$catch_unwind_entry@IMGREL
	.word	2
	.word	2
	.word	3
	.word	1
	.word	$handlerMap$1$catch_unwind_entry@IMGREL
	.word	4
	.word	4
	.word	5
	.word	1
	.word	$handlerMap$2$catch_unwind_entry@IMGREL
$handlerMap$0$catch_unwind_entry:
	.word	8
	.word	_RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info@IMGREL
	.word	-8
	.word	"?catch$10@?0?catch_unwind_entry@4HA"@IMGREL
	.word	0
	.word	64
	.word	0
	.word	0
	.word	"?catch$13@?0?catch_unwind_entry@4HA"@IMGREL
	.word	0
$handlerMap$1$catch_unwind_entry:
	.word	64
	.word	0
	.word	0
	.word	"?catch$9@?0?catch_unwind_entry@4HA"@IMGREL
	.word	0
$handlerMap$2$catch_unwind_entry:
	.word	64
	.word	0
	.word	0
	.word	"?catch$12@?0?catch_unwind_entry@4HA"@IMGREL
	.word	0
$ip2state$catch_unwind_entry:
	.word	.Lfunc_begin0@IMGREL
	.word	-1
	.word	.Ltmp0@IMGREL
	.word	0
	.word	.Ltmp6@IMGREL
	.word	6
	.word	.Ltmp7@IMGREL
	.word	-1
	.word	"?catch$9@?0?catch_unwind_entry@4HA"@IMGREL
	.word	3
	.word	"?catch$10@?0?catch_unwind_entry@4HA"@IMGREL
	.word	1
	.word	.Ltmp4@IMGREL
	.word	2
	.word	.Ltmp5@IMGREL
	.word	1
	.word	"?catch$12@?0?catch_unwind_entry@4HA"@IMGREL
	.word	5
	.word	"?catch$13@?0?catch_unwind_entry@4HA"@IMGREL
	.word	1
	.word	.Ltmp2@IMGREL
	.word	4
	.word	.Ltmp3@IMGREL
	.word	1
	.section	.text,"xr",one_only,catch_unwind_entry,unique,1

	.def	frameless_leaf;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,frameless_leaf,unique,2
	.globl	frameless_leaf
	.p2align	2
frameless_leaf:
	add	x0, x0, #42
	ret

	.def	nested_cleanups;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,nested_cleanups,unique,3
	.globl	nested_cleanups
	.p2align	2
nested_cleanups:
.Lfunc_begin1:
.seh_proc nested_cleanups
	.seh_handler __CxxFrameHandler3, @unwind, @except
	sub	sp, sp, #64
	.seh_stackalloc	64
	stp	x29, x30, [sp, #32]
	.seh_save_fplr	32
	add	x29, sp, #32
	.seh_add_fp	32
	.seh_endprologue
	mov	x2, #-2
	mov	w8, #1
	stur	x2, [x29, #16]
	stur	w8, [x29, #-24]
	mov	w8, #2
	stur	x0, [x29, #-32]
	stur	x0, [x29, #-16]
	stur	w8, [x29, #-8]
.Ltmp8:
	blr	x1
.Ltmp9:
	sub	x0, x29, #16
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
	sub	x0, x29, #32
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
	.seh_startepilogue
	ldp	x29, x30, [sp, #32]
	.seh_save_fplr	32
	add	sp, sp, #64
	.seh_stackalloc	64
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$nested_cleanups@IMGREL
	.section	.text,"xr",one_only,nested_cleanups,unique,3
	.seh_endproc
	.def	"?dtor$2@?0?nested_cleanups@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?dtor$2@?0?nested_cleanups@4HA":
.seh_proc "?dtor$2@?0?nested_cleanups@4HA"
.LBB3_2:
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	.seh_endprologue
	sub	x0, x29, #16
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
	sub	x0, x29, #32
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
	.seh_startepilogue
	ldp	x29, x30, [sp], #16
	.seh_save_fplr_x	16
	.seh_endepilogue
	ret
.Lfunc_end1:
	.seh_endfunclet
	.seh_handlerdata
	.section	.text,"xr",one_only,nested_cleanups,unique,3
	.seh_endproc
	.section	.xdata,"dr",associative,nested_cleanups,unique,1
	.p2align	2, 0x0
$cppxdata$nested_cleanups:
	.word	429065506
	.word	1
	.word	$stateUnwindMap$nested_cleanups@IMGREL
	.word	0
	.word	0
	.word	3
	.word	$ip2state$nested_cleanups@IMGREL
	.word	-16
	.word	0
	.word	1
$stateUnwindMap$nested_cleanups:
	.word	-1
	.word	"?dtor$2@?0?nested_cleanups@4HA"@IMGREL
$ip2state$nested_cleanups:
	.word	.Lfunc_begin1@IMGREL
	.word	-1
	.word	.Ltmp8@IMGREL
	.word	0
	.word	.Ltmp9@IMGREL
	.word	-1
	.section	.text,"xr",one_only,nested_cleanups,unique,3

	.def	nounwind_c_boundary;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,nounwind_c_boundary,unique,4
	.globl	nounwind_c_boundary
	.p2align	2
nounwind_c_boundary:
.Lfunc_begin2:
.seh_proc nounwind_c_boundary
	.seh_handler __CxxFrameHandler3, @unwind, @except
	sub	sp, sp, #48
	.seh_stackalloc	48
	stp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	x29, sp, #16
	.seh_add_fp	16
	.seh_endprologue
	mov	x2, #-2
	mov	w8, #9
	stur	x2, [x29, #16]
	stur	x0, [x29, #-16]
	stur	w8, [x29, #-8]
.Ltmp10:
	blr	x1
.Ltmp11:
	sub	x0, x29, #16
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
	.seh_startepilogue
	ldp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	sp, sp, #48
	.seh_stackalloc	48
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$nounwind_c_boundary@IMGREL
	.section	.text,"xr",one_only,nounwind_c_boundary,unique,4
	.seh_endproc
	.def	"?dtor$2@?0?nounwind_c_boundary@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?dtor$2@?0?nounwind_c_boundary@4HA":
.seh_proc "?dtor$2@?0?nounwind_c_boundary@4HA"
.LBB4_2:
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	.seh_endprologue
	sub	x0, x29, #16
	bl	_RNvXCsjBwlT6cN9ry_12unwind_probeNtB2_11DropTrackerNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
	bl	_RNvNtCsaF4MlZlPuCq_4core9panicking19panic_cannot_unwind
	brk	#0x1
.Lfunc_end2:
	.seh_endfunclet
	.seh_handlerdata
	.section	.text,"xr",one_only,nounwind_c_boundary,unique,4
	.seh_endproc
	.section	.xdata,"dr",associative,nounwind_c_boundary,unique,2
	.p2align	2, 0x0
$cppxdata$nounwind_c_boundary:
	.word	429065506
	.word	1
	.word	$stateUnwindMap$nounwind_c_boundary@IMGREL
	.word	0
	.word	0
	.word	3
	.word	$ip2state$nounwind_c_boundary@IMGREL
	.word	-16
	.word	0
	.word	1
$stateUnwindMap$nounwind_c_boundary:
	.word	-1
	.word	"?dtor$2@?0?nounwind_c_boundary@4HA"@IMGREL
$ip2state$nounwind_c_boundary:
	.word	.Lfunc_begin2@IMGREL
	.word	-1
	.word	.Ltmp10@IMGREL
	.word	0
	.word	.Ltmp11@IMGREL
	.word	-1
	.section	.text,"xr",one_only,nounwind_c_boundary,unique,4

	.def	passthrough_no_cleanup;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,passthrough_no_cleanup,unique,5
	.globl	passthrough_no_cleanup
	.p2align	2
passthrough_no_cleanup:
	br	x0

	.def	passthrough_with_frame;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,passthrough_with_frame,unique,6
	.globl	passthrough_with_frame
	.p2align	2
passthrough_with_frame:
.seh_proc passthrough_with_frame
	str	x19, [sp, #-32]!
	.seh_save_reg_x	x19, 32
	stp	x29, x30, [sp, #8]
	.seh_save_fplr	8
	add	x29, sp, #8
	.seh_add_fp	8
	.seh_endprologue
	mov	x19, x0
	blr	x1
	add	x0, x0, x19
	.seh_startepilogue
	ldp	x29, x30, [sp, #8]
	.seh_save_fplr	8
	ldr	x19, [sp], #32
	.seh_save_reg_x	x19, 32
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.def	simple_nonleaf_call;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,simple_nonleaf_call,unique,7
	.globl	simple_nonleaf_call
	.p2align	2
simple_nonleaf_call:
.seh_proc simple_nonleaf_call
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	mov	x29, sp
	.seh_set_fp
	.seh_endprologue
	blr	x0
	add	x0, x0, #1
	.seh_startepilogue
	ldp	x29, x30, [sp], #16
	.seh_save_fplr_x	16
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.section	.data,"dw",discard,_RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info,unique,8
	.globl	_RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info
	.p2align	4, 0x0
_RNvCs5fGHjzWXRav_7___rustc22___rust_panic_type_info:
	.xword	"??_7type_info@@6B@"
	.xword	0
	.asciz	"rust_panic"
	.zero	5

