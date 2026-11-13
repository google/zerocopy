	.file	"tls_probe.d6bd21401e7e8eac-cgu.0"
	.section	.text.unlikely._RINvMs0_NtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_,"ax",@progbits
	.p2align	2
	.type	_RINvMs0_NtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_,@function
_RINvMs0_NtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_:
	.cfi_startproc
	sub	sp, sp, #48
	.cfi_def_cfa_offset 48
	stp	x29, x30, [sp, #16]
	str	x19, [sp, #32]
	add	x29, sp, #16
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	.cfi_remember_state
	ldrb	w8, [x0, #8]
	cbz	w8, .LBB0_3
	cmp	w8, #1
	b.eq	.LBB0_11
	mov	x0, xzr
	b	.LBB0_11
.LBB0_3:
	cbz	x1, .LBB0_6
	ldp	x9, x8, [x1]
	str	xzr, [x1]
	cbz	x9, .LBB0_6
	str	x8, [x0]
	mov	w8, #1
	strb	w8, [x0, #8]
	b	.LBB0_9
.LBB0_6:
	mov	w8, #13
	add	x9, sp, #8
	str	x8, [sp, #8]
	//APP
	//NO_APP
	ldr	x9, [x0]
	ldrb	w8, [x0, #8]
	ldr	x10, [sp, #8]
	str	x9, [sp]
	mov	w9, #1
	cmp	w8, #1
	str	x10, [x0]
	strb	w9, [x0, #8]
	b.ne	.LBB0_8
	mov	x19, x0
	mov	x0, sp
	bl	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
	b	.LBB0_10
.LBB0_8:
	cbnz	w8, .LBB0_12
.LBB0_9:
	adrp	x1, _RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazy7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_
	add	x1, x1, :lo12:_RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazy7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_
	mov	x19, x0
	bl	_RNvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local11destructors10linux_like8register
.LBB0_10:
	mov	x0, x19
.LBB0_11:
	.cfi_def_cfa wsp, 48
	ldp	x29, x30, [sp, #16]
	ldr	x19, [sp, #32]
	add	sp, sp, #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB0_12:
	.cfi_restore_state
	adrp	x1, .Lalloc_70165e1942fbf2cb7aee6a08556ee215
	add	x1, x1, :lo12:.Lalloc_70165e1942fbf2cb7aee6a08556ee215
	add	x0, x29, #31
	mov	w2, #87
	bl	_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	str	x0, [sp, #8]
	add	x0, sp, #8
	bl	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	bl	_RNvNtCs9g4b2IXPNZ3_3std7process5abort
.Lfunc_end0:
	.size	_RINvMs0_NtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_, .Lfunc_end0-_RINvMs0_NtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	.cfi_endproc

	.section	.text._RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe,@function
_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	ldr	x8, [x0]
	cbz	x8, .LBB1_4
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	b.lo	.LBB1_4
	cbz	x9, .LBB1_4
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	sub	x8, x8, #1
	mov	w9, #3
	str	x8, [sp, #8]
	mov	x8, sp
	add	x0, x8, #8
	strb	w9, [sp]
	bl	_RNvXsd_NtNtCsaWcbhsS8OaW_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
.LBB1_4:
	ret
.Lfunc_end1:
	.size	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe, .Lfunc_end1-_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe,@function
_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	ldr	x8, [x0, #8]
	cbz	x8, .LBB2_4
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	b.lo	.LBB2_4
	cbz	x9, .LBB2_4
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	sub	x8, x8, #1
	mov	w9, #3
	str	x8, [sp, #8]
	mov	x8, sp
	add	x0, x8, #8
	strb	w9, [sp]
	bl	_RNvXsd_NtNtCsaWcbhsS8OaW_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
.LBB2_4:
	ret
.Lfunc_end2:
	.size	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe, .Lfunc_end2-_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe,@function
_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	ldr	x8, [x0]
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	ccmp	x9, #0, #4, hs
	b.ne	.LBB3_2
	ret
.LBB3_2:
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	sub	x8, x8, #1
	mov	w9, #3
	str	x8, [sp, #8]
	mov	x8, sp
	add	x0, x8, #8
	strb	w9, [sp]
	bl	_RNvXsd_NtNtCsaWcbhsS8OaW_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end3:
	.size	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe, .Lfunc_end3-_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazy7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_,"ax",@progbits
	.p2align	2
	.type	_RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazy7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_,@function
_RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazy7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_:
	.cfi_startproc
	ldrb	w9, [x0, #8]
	mov	w8, #2
	strb	w8, [x0, #8]
	cmp	w9, #1
	b.ne	.LBB4_2
	b	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
.LBB4_2:
	ret
.Lfunc_end4:
	.size	_RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazy7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_, .Lfunc_end4-_RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazy7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_
	.cfi_endproc

	.section	.text._RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native5eager7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_,"ax",@progbits
	.p2align	2
	.type	_RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native5eager7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_,@function
_RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native5eager7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_:
	.cfi_startproc
	mov	w8, #2
	strb	w8, [x0, #8]
	b	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
.Lfunc_end5:
	.size	_RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native5eager7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_, .Lfunc_end5-_RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native5eager7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_
	.cfi_endproc

	.section	.text._RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop,"ax",@progbits
	.globl	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
	.p2align	2
	.type	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop,@function
_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop:
	.cfi_startproc
	sub	sp, sp, #16
	.cfi_def_cfa_offset 16
	ldr	x9, [x0]
	add	x8, sp, #8
	str	x9, [sp, #8]
	//APP
	//NO_APP
	add	sp, sp, #16
	.cfi_def_cfa_offset 0
	ret
.Lfunc_end6:
	.size	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop, .Lfunc_end6-_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaWcbhsS8OaW_4core3ops4drop4Drop4drop
	.cfi_endproc

	.section	.text._RNvXNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.p2align	2
	.type	_RNvXNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,@function
_RNvXNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 156, DW.ref.rust_eh_personality
	.cfi_lsda 28, .Lexception0
	sub	sp, sp, #48
	.cfi_def_cfa_offset 48
	stp	x29, x30, [sp, #16]
	stp	x20, x19, [sp, #32]
	add	x29, sp, #16
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	.cfi_remember_state
	mov	x19, x0
	ldr	x0, [x0]
	bl	_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	mov	x20, x0
	cbz	x0, .LBB7_6
	ldr	x8, [x19, #8]
	cbz	x8, .LBB7_5
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	b.lo	.LBB7_5
	cbz	x9, .LBB7_5
	sub	x8, x8, #1
	mov	w9, #3
	str	x8, [sp, #8]
	mov	x8, sp
	strb	w9, [sp]
.Ltmp1:
	add	x0, x8, #8
	bl	_RNvXsd_NtNtCsaWcbhsS8OaW_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.Ltmp2:
.LBB7_5:
	str	x20, [x19, #8]
.LBB7_6:
	cmp	x20, #0
	cset	w0, ne
	.cfi_def_cfa wsp, 48
	ldp	x20, x19, [sp, #32]
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB7_7:
	.cfi_restore_state
.Ltmp3:
	str	x20, [x19, #8]
	bl	_Unwind_Resume
.Lfunc_end7:
	.size	_RNvXNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe, .Lfunc_end7-_RNvXNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.gcc_except_table._RNvXNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table7:
.Lexception0:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end0-.Lcst_begin0
.Lcst_begin0:
	.uleb128 .Lfunc_begin0-.Lfunc_begin0
	.uleb128 .Ltmp1-.Lfunc_begin0
	.byte	0
	.byte	0
	.uleb128 .Ltmp1-.Lfunc_begin0
	.uleb128 .Ltmp2-.Ltmp1
	.uleb128 .Ltmp3-.Lfunc_begin0
	.byte	0
	.uleb128 .Ltmp2-.Lfunc_begin0
	.uleb128 .Lfunc_end7-.Ltmp2
	.byte	0
	.byte	0
.Lcst_end0:
	.p2align	2, 0x0

	.section	.text._RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.p2align	2
	.type	_RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,@function
_RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin1:
	.cfi_startproc
	.cfi_personality 156, DW.ref.rust_eh_personality
	.cfi_lsda 28, .Lexception1
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	stp	x29, x30, [sp, #32]
	stp	x20, x19, [sp, #48]
	add	x29, sp, #32
	.cfi_def_cfa w29, 32
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w30, -24
	.cfi_offset w29, -32
	.cfi_remember_state
	mov	x19, x0
	cmp	w1, #128
	str	wzr, [sp, #12]
	b.hs	.LBB8_2
	strb	w1, [sp, #12]
	mov	w2, #1
	b	.LBB8_7
.LBB8_2:
	mov	w8, #-128
	cmp	w1, #2048
	mov	w9, #-128
	bfxil	w8, w1, #0, #6
	b.hs	.LBB8_4
	lsr	w9, w1, #6
	strb	w8, [sp, #13]
	mov	w2, #2
	orr	w9, w9, #0xc0
	strb	w9, [sp, #12]
	b	.LBB8_7
.LBB8_4:
	mov	w10, #-128
	lsr	w11, w1, #16
	bfxil	w10, w1, #6, #6
	cbnz	w11, .LBB8_6
	lsr	w9, w1, #12
	strb	w10, [sp, #13]
	mov	w2, #3
	strb	w8, [sp, #14]
	orr	w9, w9, #0xe0
	strb	w9, [sp, #12]
	b	.LBB8_7
.LBB8_6:
	lsr	w11, w1, #18
	bfxil	w9, w1, #12, #6
	strb	w10, [sp, #14]
	mov	w2, #4
	strb	w8, [sp, #15]
	orr	w10, w11, #0xfffffff0
	strb	w9, [sp, #13]
	strb	w10, [sp, #12]
.LBB8_7:
	ldr	x0, [x19]
	add	x1, sp, #12
	bl	_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	mov	x20, x0
	cbz	x0, .LBB8_13
	ldr	x8, [x19, #8]
	cbz	x8, .LBB8_12
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	b.lo	.LBB8_12
	cbz	x9, .LBB8_12
	sub	x8, x8, #1
	mov	w9, #3
	str	x8, [sp, #24]
	add	x8, sp, #16
	strb	w9, [sp, #16]
.Ltmp4:
	add	x0, x8, #8
	bl	_RNvXsd_NtNtCsaWcbhsS8OaW_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.Ltmp5:
.LBB8_12:
	str	x20, [x19, #8]
.LBB8_13:
	cmp	x20, #0
	cset	w0, ne
	.cfi_def_cfa wsp, 64
	ldp	x20, x19, [sp, #48]
	ldp	x29, x30, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB8_14:
	.cfi_restore_state
.Ltmp6:
	str	x20, [x19, #8]
	bl	_Unwind_Resume
.Lfunc_end8:
	.size	_RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe, .Lfunc_end8-_RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.gcc_except_table._RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table8:
.Lexception1:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end1-.Lcst_begin1
.Lcst_begin1:
	.uleb128 .Lfunc_begin1-.Lfunc_begin1
	.uleb128 .Ltmp4-.Lfunc_begin1
	.byte	0
	.byte	0
	.uleb128 .Ltmp4-.Lfunc_begin1
	.uleb128 .Ltmp5-.Ltmp4
	.uleb128 .Ltmp6-.Lfunc_begin1
	.byte	0
	.uleb128 .Ltmp5-.Lfunc_begin1
	.uleb128 .Lfunc_end8-.Ltmp5
	.byte	0
	.byte	0
.Lcst_end1:
	.p2align	2, 0x0

	.section	.text._RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.p2align	2
	.type	_RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,@function
_RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	mov	x3, x2
	mov	x2, x1
	adrp	x1, .Lvtable.0
	add	x1, x1, :lo12:.Lvtable.0
	b	_RNvNtCsaWcbhsS8OaW_4core3fmt5write
.Lfunc_end9:
	.size	_RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe, .Lfunc_end9-_RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc

	.section	.text._RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.p2align	2
	.type	_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,@function
_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin2:
	.cfi_startproc
	.cfi_personality 156, DW.ref.rust_eh_personality
	.cfi_lsda 28, .Lexception2
	sub	sp, sp, #128
	.cfi_def_cfa_offset 128
	stp	x29, x30, [sp, #32]
	str	x27, [sp, #48]
	stp	x26, x25, [sp, #64]
	stp	x24, x23, [sp, #80]
	stp	x22, x21, [sp, #96]
	stp	x20, x19, [sp, #112]
	add	x29, sp, #32
	.cfi_def_cfa w29, 96
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	.cfi_remember_state
	cbz	x2, .LBB10_18
	mov	x19, x2
	mov	x20, x1
	mov	x21, x0
	mov	x23, sp
	add	x24, sp, #16
	mov	w26, #3
	mov	w27, #255
	adrp	x25, .Lalloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2
	add	x25, x25, :lo12:.Lalloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2
	b	.LBB10_5
.LBB10_2:
	ldrb	w8, [x22, #16]
.LBB10_3:
	cmp	w8, #35
	b.ne	.LBB10_19
.LBB10_4:
	cbz	x19, .LBB10_18
.LBB10_5:
	mov	x0, x21
	mov	x1, x20
	mov	x2, x19
	bl	_RNvXs3_NtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unixNtB5_6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write5write
	mov	x22, x1
	cmp	x0, #1
	stp	x0, x1, [sp]
	b.ne	.LBB10_10
	and	x8, x22, #0x3
	cmp	x8, #1
	b.gt	.LBB10_13
	cbz	x8, .LBB10_2
	ldrb	w8, [x22, #31]
	cmp	w8, #35
	b.ne	.LBB10_19
	sub	x8, x22, #1
	add	x0, x24, #8
	strb	w26, [sp, #16]
	str	x8, [sp, #24]
	bl	_RNvXsd_NtNtCsaWcbhsS8OaW_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	cbnz	x19, .LBB10_5
	b	.LBB10_18
.LBB10_10:
	cbz	x22, .LBB10_20
	subs	x8, x19, x22
	b.lo	.LBB10_21
	add	x20, x20, x22
	mov	x19, x8
	cbnz	x8, .LBB10_5
	b	.LBB10_18
.LBB10_13:
	cmp	x8, #2
	b.ne	.LBB10_17
.Ltmp7:
	bl	_RNvNtNtNtCsaWcbhsS8OaW_4core2io5error12os_functions16get_os_functions
.Ltmp8:
	ldr	x9, [x0, #16]
	lsr	x8, x22, #32
.Ltmp9:
	mov	w0, w8
	blr	x9
.Ltmp10:
	tbnz	w0, #0, .LBB10_4
	b	.LBB10_19
.LBB10_17:
	lsr	x8, x22, #34
	ubfx	x9, x22, #32, #8
	cmp	x8, #11
	csel	w8, w9, w27, lo
	b	.LBB10_3
.LBB10_18:
	mov	x22, xzr
.LBB10_19:
	mov	x0, x22
	.cfi_def_cfa wsp, 128
	ldp	x20, x19, [sp, #112]
	ldr	x27, [sp, #48]
	ldp	x22, x21, [sp, #96]
	ldp	x24, x23, [sp, #80]
	ldp	x26, x25, [sp, #64]
	ldp	x29, x30, [sp, #32]
	add	sp, sp, #128
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB10_20:
	.cfi_restore_state
	mov	x22, x25
	b	.LBB10_19
.LBB10_21:
	adrp	x3, .Lalloc_22d3a9dec0cad4fe8d6eb3a7bed31903
	add	x3, x3, :lo12:.Lalloc_22d3a9dec0cad4fe8d6eb3a7bed31903
	mov	x0, x22
	mov	x1, x19
	mov	x2, x19
	bl	_RNvNtNtCsaWcbhsS8OaW_4core5slice5index16slice_index_fail
.LBB10_22:
.Ltmp11:
	mov	x19, x0
.Ltmp12:
	add	x0, x23, #8
	bl	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
.Ltmp13:
	mov	x0, x19
	bl	_Unwind_Resume
.LBB10_24:
.Ltmp14:
	bl	_RNvNtCsaWcbhsS8OaW_4core9panicking16panic_in_cleanup
.Lfunc_end10:
	.size	_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe, .Lfunc_end10-_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.gcc_except_table._RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table10:
.Lexception2:
	.byte	255
	.byte	156
	.uleb128 .Lttbase0-.Lttbaseref0
.Lttbaseref0:
	.byte	1
	.uleb128 .Lcst_end2-.Lcst_begin2
.Lcst_begin2:
	.uleb128 .Lfunc_begin2-.Lfunc_begin2
	.uleb128 .Ltmp7-.Lfunc_begin2
	.byte	0
	.byte	0
	.uleb128 .Ltmp7-.Lfunc_begin2
	.uleb128 .Ltmp10-.Ltmp7
	.uleb128 .Ltmp11-.Lfunc_begin2
	.byte	0
	.uleb128 .Ltmp10-.Lfunc_begin2
	.uleb128 .Ltmp12-.Ltmp10
	.byte	0
	.byte	0
	.uleb128 .Ltmp12-.Lfunc_begin2
	.uleb128 .Ltmp13-.Ltmp12
	.uleb128 .Ltmp14-.Lfunc_begin2
	.byte	1
	.uleb128 .Ltmp13-.Lfunc_begin2
	.uleb128 .Lfunc_end10-.Ltmp13
	.byte	0
	.byte	0
.Lcst_end2:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase0:
	.byte	0
	.p2align	2, 0x0

	.section	.text._RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,"ax",@progbits
	.p2align	2
	.type	_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,@function
_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin3:
	.cfi_startproc
	.cfi_personality 156, DW.ref.rust_eh_personality
	.cfi_lsda 28, .Lexception3
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
	mov	x3, x2
	mov	x2, x1
	stp	x0, xzr, [sp]
.Ltmp15:
	adrp	x1, .Lvtable.0
	add	x1, x1, :lo12:.Lvtable.0
	mov	x0, sp
	bl	_RNvNtCsaWcbhsS8OaW_4core3fmt5write
.Ltmp16:
	cbz	w0, .LBB11_5
	ldr	x0, [sp, #8]
	cbnz	x0, .LBB11_10
.Ltmp17:
	adrp	x0, .Lalloc_a439077caaee6bab9af745f1531d72a4
	add	x0, x0, :lo12:.Lalloc_a439077caaee6bab9af745f1531d72a4
	adrp	x2, .Lalloc_66f584c540a2b1d04ce5ea73db115bd6
	add	x2, x2, :lo12:.Lalloc_66f584c540a2b1d04ce5ea73db115bd6
	mov	w1, #173
	bl	_RNvNtCsaWcbhsS8OaW_4core9panicking9panic_fmt
.Ltmp18:
	brk	#0x1
.LBB11_5:
	ldr	x8, [sp, #8]
	cbz	x8, .LBB11_9
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	b.lo	.LBB11_9
	cbz	x9, .LBB11_9
	sub	x8, x8, #1
	mov	w9, #3
	str	x8, [sp, #24]
	add	x8, sp, #16
	add	x0, x8, #8
	strb	w9, [sp, #16]
	bl	_RNvXsd_NtNtCsaWcbhsS8OaW_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.LBB11_9:
	mov	x0, xzr
.LBB11_10:
	.cfi_def_cfa wsp, 64
	ldp	x29, x30, [sp, #32]
	ldr	x19, [sp, #48]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB11_11:
	.cfi_restore_state
.Ltmp19:
	mov	x19, x0
.Ltmp20:
	mov	x0, sp
	bl	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe
.Ltmp21:
	mov	x0, x19
	bl	_Unwind_Resume
.LBB11_13:
.Ltmp22:
	bl	_RNvNtCsaWcbhsS8OaW_4core9panicking16panic_in_cleanup
.Lfunc_end11:
	.size	_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe, .Lfunc_end11-_RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.cfi_endproc
	.section	.gcc_except_table._RNvYNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrNtNtNtCsaWcbhsS8OaW_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,"a",@progbits
	.p2align	2, 0x0
GCC_except_table11:
.Lexception3:
	.byte	255
	.byte	156
	.uleb128 .Lttbase1-.Lttbaseref1
.Lttbaseref1:
	.byte	1
	.uleb128 .Lcst_end3-.Lcst_begin3
.Lcst_begin3:
	.uleb128 .Ltmp15-.Lfunc_begin3
	.uleb128 .Ltmp18-.Ltmp15
	.uleb128 .Ltmp19-.Lfunc_begin3
	.byte	0
	.uleb128 .Ltmp18-.Lfunc_begin3
	.uleb128 .Ltmp20-.Ltmp18
	.byte	0
	.byte	0
	.uleb128 .Ltmp20-.Lfunc_begin3
	.uleb128 .Ltmp21-.Ltmp20
	.uleb128 .Ltmp22-.Lfunc_begin3
	.byte	1
	.uleb128 .Ltmp21-.Lfunc_begin3
	.uleb128 .Lfunc_end11-.Ltmp21
	.byte	0
	.byte	0
.Lcst_end3:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase1:
	.byte	0
	.p2align	2, 0x0

	.section	.text.access_all_tls,"ax",@progbits
	.globl	access_all_tls
	.p2align	2
	.type	access_all_tls,@function
access_all_tls:
	.cfi_startproc
	sub	sp, sp, #80
	.cfi_def_cfa_offset 80
	stp	x29, x30, [sp, #16]
	stp	x24, x23, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	add	x29, sp, #16
	.cfi_def_cfa w29, 64
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w30, -56
	.cfi_offset w29, -64
	.cfi_remember_state
	adrp	x0, :tlsdesc:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	ldr	x1, [x0, :tlsdesc_lo12:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64]
	add	x0, x0, :tlsdesc_lo12:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	.tlsdesccall _RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	blr	x1
	mrs	x23, TPIDR_EL0
	ldr	x8, [x23, x0]
	add	x20, x8, #1
	str	x20, [x23, x0]
	adrp	x0, :tlsdesc:_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	ldr	x1, [x0, :tlsdesc_lo12:_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64]
	add	x0, x0, :tlsdesc_lo12:_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	.tlsdesccall _RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	blr	x1
	ldr	x21, [x23, x0]
	adrp	x0, :tlsdesc:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	ldr	x1, [x0, :tlsdesc_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL]
	add	x0, x0, :tlsdesc_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.tlsdesccall _RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	blr	x1
	ldr	x22, [x23, x0]
	adrp	x0, :tlsdesc:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	ldr	x1, [x0, :tlsdesc_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL]
	add	x0, x0, :tlsdesc_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	.tlsdesccall _RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	blr	x1
	add	x19, x23, x0
	ldrb	w8, [x19, #8]
	cbnz	w8, .LBB12_7
.LBB12_1:
	ldr	x19, [x19]
	adrp	x0, :tlsdesc:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	ldr	x1, [x0, :tlsdesc_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL]
	add	x0, x0, :tlsdesc_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.tlsdesccall _RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	blr	x1
	add	x8, x23, x0
	ldrb	w9, [x8, #8]
	cbz	w9, .LBB12_5
	ldr	x24, [x8]
.LBB12_3:
	adrp	x0, :tlsdesc:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	ldr	x1, [x0, :tlsdesc_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL]
	add	x0, x0, :tlsdesc_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	.tlsdesccall _RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	blr	x1
	add	x0, x23, x0
	ldrb	w8, [x0, #8]
	cmp	w8, #1
	b.ne	.LBB12_6
.LBB12_4:
	ldr	x8, [x0]
	add	x9, x21, x20
	add	x10, x22, x19
	add	x9, x9, x10
	add	x8, x24, x8
	add	x0, x9, x8
	.cfi_def_cfa wsp, 80
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldp	x24, x23, [sp, #32]
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB12_5:
	.cfi_restore_state
	mov	w9, #7
	add	x10, sp, #8
	str	x9, [sp, #8]
	mov	w9, #1
	//APP
	//NO_APP
	strb	w9, [x8, #8]
	ldr	x24, [sp, #8]
	str	x24, [x8]
	b	.LBB12_3
.LBB12_6:
	mov	x1, xzr
	bl	_RINvMs0_NtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	cbnz	x0, .LBB12_4
	b	.LBB12_9
.LBB12_7:
	cmp	w8, #1
	b.ne	.LBB12_9
	adrp	x1, _RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native5eager7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_
	add	x1, x1, :lo12:_RINvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local6native5eager7destroyINtNtCsaWcbhsS8OaW_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_
	mov	x0, x19
	bl	_RNvNtNtNtNtCs9g4b2IXPNZ3_3std3sys12thread_local11destructors10linux_like8register
	strb	wzr, [x19, #8]
	b	.LBB12_1
.LBB12_9:
	adrp	x0, .Lalloc_cf04a7d848f454bae906dcea67110b94
	add	x0, x0, :lo12:.Lalloc_cf04a7d848f454bae906dcea67110b94
	bl	_RNvNtNtCs9g4b2IXPNZ3_3std6thread5local18panic_access_error
.Lfunc_end12:
	.size	access_all_tls, .Lfunc_end12-access_all_tls
	.cfi_endproc

	.type	.Lalloc_70165e1942fbf2cb7aee6a08556ee215,@object
	.section	.rodata..Lalloc_70165e1942fbf2cb7aee6a08556ee215,"a",@progbits
.Lalloc_70165e1942fbf2cb7aee6a08556ee215:
	.ascii	"fatal runtime error: unreachable, aborting\n"
	.size	.Lalloc_70165e1942fbf2cb7aee6a08556ee215, 43

	.type	.Lalloc_cccd7a83c897ff0b212dd50c8ec2f4d1,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lalloc_cccd7a83c897ff0b212dd50c8ec2f4d1:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/std/src/thread/local.rs"
	.size	.Lalloc_cccd7a83c897ff0b212dd50c8ec2f4d1, 134

	.type	.Lalloc_cf04a7d848f454bae906dcea67110b94,@object
	.section	.data.rel.ro..Lalloc_cf04a7d848f454bae906dcea67110b94,"aw",@progbits
	.p2align	3, 0x0
.Lalloc_cf04a7d848f454bae906dcea67110b94:
	.xword	.Lalloc_cccd7a83c897ff0b212dd50c8ec2f4d1
	.asciz	"\205\000\000\000\000\000\000\000\255\001\000\000\031\000\000"
	.size	.Lalloc_cf04a7d848f454bae906dcea67110b94, 24

	.type	.Lvtable.0,@object
	.section	.data.rel.ro..Lvtable.0,"aw",@progbits
	.p2align	3, 0x0
.Lvtable.0:
	.xword	_RINvNtCsaWcbhsS8OaW_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe
	.asciz	"\020\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.xword	_RNvXNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.xword	_RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.xword	_RNvYINtNvNtNtCsaWcbhsS8OaW_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9g4b2IXPNZ3_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.size	.Lvtable.0, 48

	.type	.Lalloc_a439077caaee6bab9af745f1531d72a4,@object
	.section	.rodata..Lalloc_a439077caaee6bab9af745f1531d72a4,"a",@progbits
.Lalloc_a439077caaee6bab9af745f1531d72a4:
	.ascii	"a formatting trait implementation returned an error when the underlying stream did not"
	.size	.Lalloc_a439077caaee6bab9af745f1531d72a4, 86

	.type	.Lalloc_cb6f00447019d73f4f2c3d453e522c22,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lalloc_cb6f00447019d73f4f2c3d453e522c22:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/io/write.rs"
	.size	.Lalloc_cb6f00447019d73f4f2c3d453e522c22, 131

	.type	.Lalloc_66f584c540a2b1d04ce5ea73db115bd6,@object
	.section	.data.rel.ro..Lalloc_66f584c540a2b1d04ce5ea73db115bd6,"aw",@progbits
	.p2align	3, 0x0
.Lalloc_66f584c540a2b1d04ce5ea73db115bd6:
	.xword	.Lalloc_cb6f00447019d73f4f2c3d453e522c22
	.asciz	"\202\000\000\000\000\000\000\000\233\001\000\000\021\000\000"
	.size	.Lalloc_66f584c540a2b1d04ce5ea73db115bd6, 24

	.type	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,@object
	.section	.tdata._RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,"awT",@progbits
	.globl	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	.p2align	3, 0x0
_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64:
	.ascii	"\210wfUD3\"\021"
	.size	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64, 8

	.type	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64,@object
	.section	.tdata._RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64,"awT",@progbits
	.globl	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	.p2align	6, 0x0
_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64:
	.asciz	"\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000"
	.size	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64, 64

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL,@object
	.section	.tdata._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL,"awT",@progbits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL:
	.ascii	"c\000\000\000\000\000\000\000\001"
	.zero	7
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL, 16

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,@object
	.section	.tbss._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,"awT",@nobits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	7
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL, 16

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,@object
	.section	.tdata._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,"awT",@progbits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.asciz	"*\000\000\000\000\000\000"
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL, 8

	.type	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,@object
	.section	.tbss._RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,"awT",@nobits
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	7
	.size	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL, 16

	.type	.Lalloc_8d68fcbc011419193bd208f22e2789d1,@object
	.section	.rodata..Lalloc_8d68fcbc011419193bd208f22e2789d1,"a",@progbits
.Lalloc_8d68fcbc011419193bd208f22e2789d1:
	.ascii	"failed to write whole buffer"
	.size	.Lalloc_8d68fcbc011419193bd208f22e2789d1, 28

	.type	.Lalloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2,@object
	.section	.data.rel.ro..Lalloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2,"aw",@progbits
	.p2align	3, 0x0
.Lalloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2:
	.xword	.Lalloc_8d68fcbc011419193bd208f22e2789d1
	.ascii	"\034\000\000\000\000\000\000\000\027"
	.zero	7
	.size	.Lalloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2, 24

	.type	.Lalloc_22d3a9dec0cad4fe8d6eb3a7bed31903,@object
	.section	.data.rel.ro..Lalloc_22d3a9dec0cad4fe8d6eb3a7bed31903,"aw",@progbits
	.p2align	3, 0x0
.Lalloc_22d3a9dec0cad4fe8d6eb3a7bed31903:
	.xword	.Lalloc_cb6f00447019d73f4f2c3d453e522c22
	.asciz	"\202\000\000\000\000\000\000\000\334\000\000\000$\000\000"
	.size	.Lalloc_22d3a9dec0cad4fe8d6eb3a7bed31903, 24

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
