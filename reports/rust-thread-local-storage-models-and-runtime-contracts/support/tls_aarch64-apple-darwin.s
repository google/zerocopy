	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RINvMs0_NtNtNtNtCsdnanKjkF2cC_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCs3bJEMBXHbwl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_:
	.cfi_startproc
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	stp	x20, x19, [sp, #32]
	stp	x29, x30, [sp, #48]
	add	x29, sp, #48
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_remember_state
	ldrb	w8, [x0, #8]
	cbz	w8, LBB0_2
	cmp	w8, #1
	csel	x0, x0, xzr, eq
	b	LBB0_10
LBB0_2:
	cbz	x1, LBB0_5
	ldp	x9, x8, [x1]
	str	xzr, [x1]
	cbz	x9, LBB0_5
	str	x8, [x0]
	mov	w8, #1
	strb	w8, [x0, #8]
	b	LBB0_8
LBB0_5:
	mov	w8, #13
	str	x8, [sp, #16]
	add	x8, sp, #16
	; InlineAsm Start
	; InlineAsm End
	ldr	x9, [sp, #16]
	ldrb	w8, [x0, #8]
	ldr	x10, [x0]
	str	x10, [sp, #8]
	str	x9, [x0]
	mov	w9, #1
	strb	w9, [x0, #8]
	cmp	w8, #1
	b.ne	LBB0_7
	mov	x19, x0
	add	x0, sp, #8
	bl	__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
	b	LBB0_9
LBB0_7:
	cbnz	w8, LBB0_11
LBB0_8:
Lloh0:
	adrp	x1, __RINvNtNtNtNtCsdnanKjkF2cC_3std3sys12thread_local6native4lazy7destroyINtNtCs3bJEMBXHbwl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_@PAGE
Lloh1:
	add	x1, x1, __RINvNtNtNtNtCsdnanKjkF2cC_3std3sys12thread_local6native4lazy7destroyINtNtCs3bJEMBXHbwl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_@PAGEOFF
	mov	x19, x0
	bl	__RNvNtNtNtNtCsdnanKjkF2cC_3std3sys12thread_local11destructors4list8register
LBB0_9:
	mov	x0, x19
LBB0_10:
	.cfi_def_cfa wsp, 64
	ldp	x29, x30, [sp, #48]
	ldp	x20, x19, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
LBB0_11:
	.cfi_restore_state
Lloh2:
	adrp	x1, l_alloc_70165e1942fbf2cb7aee6a08556ee215@PAGE
Lloh3:
	add	x1, x1, l_alloc_70165e1942fbf2cb7aee6a08556ee215@PAGEOFF
	sub	x0, x29, #17
	mov	w2, #87
	bl	__RNvYNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrNtNtNtCs3bJEMBXHbwl_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	str	x0, [sp, #16]
	add	x0, sp, #16
	bl	__RINvNtCs3bJEMBXHbwl_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	bl	__RNvNtCsdnanKjkF2cC_3std7process5abort
	.loh AdrpAdd	Lloh0, Lloh1
	.loh AdrpAdd	Lloh2, Lloh3
	.cfi_endproc

	.p2align	2
__RINvNtCs3bJEMBXHbwl_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	ldr	x8, [x0]
	cbz	x8, LBB1_2
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	ccmp	x9, #0, #4, hs
	b.ne	LBB1_3
LBB1_2:
	ret
LBB1_3:
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	sub	x8, x8, #1
	mov	x9, sp
	str	x8, [sp, #8]
	mov	w8, #3
	strb	w8, [sp]
	add	x0, x9, #8
	bl	__RNvXsd_NtNtCs3bJEMBXHbwl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.p2align	2
__RINvNtCs3bJEMBXHbwl_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	ldr	x8, [x0, #8]
	cbz	x8, LBB2_2
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	ccmp	x9, #0, #4, hs
	b.ne	LBB2_3
LBB2_2:
	ret
LBB2_3:
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	sub	x8, x8, #1
	mov	x9, sp
	str	x8, [sp, #8]
	mov	w8, #3
	strb	w8, [sp]
	add	x0, x9, #8
	bl	__RNvXsd_NtNtCs3bJEMBXHbwl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.p2align	2
__RINvNtCs3bJEMBXHbwl_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	ldr	x8, [x0]
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	ccmp	x9, #0, #4, hs
	b.ne	LBB3_2
	ret
LBB3_2:
	sub	sp, sp, #32
	.cfi_def_cfa_offset 32
	stp	x29, x30, [sp, #16]
	add	x29, sp, #16
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	sub	x8, x8, #1
	mov	x9, sp
	str	x8, [sp, #8]
	mov	w8, #3
	strb	w8, [sp]
	add	x0, x9, #8
	bl	__RNvXsd_NtNtCs3bJEMBXHbwl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	.cfi_def_cfa wsp, 32
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #32
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	ret
	.cfi_endproc

	.p2align	2
__RINvNtNtNtNtCsdnanKjkF2cC_3std3sys12thread_local6native4lazy7destroyINtNtCs3bJEMBXHbwl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_:
	.cfi_startproc
	ldrb	w8, [x0, #8]
	mov	w9, #2
	strb	w9, [x0, #8]
	cmp	w8, #1
	b.ne	LBB4_2
	b	__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
LBB4_2:
	ret
	.cfi_endproc

	.p2align	2
__RINvNtNtNtNtCsdnanKjkF2cC_3std3sys12thread_local6native5eager7destroyINtNtCs3bJEMBXHbwl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_:
	.cfi_startproc
	mov	w8, #2
	strb	w8, [x0, #8]
	b	__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
	.cfi_endproc

	.globl	__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop
	.p2align	2
__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs3bJEMBXHbwl_4core3ops4drop4Drop4drop:
	.cfi_startproc
	sub	sp, sp, #16
	.cfi_def_cfa_offset 16
	ldr	x8, [x0]
	str	x8, [sp, #8]
	add	x8, sp, #8
	; InlineAsm Start
	; InlineAsm End
	add	sp, sp, #16
	.cfi_def_cfa_offset 0
	ret
	.cfi_endproc

	.p2align	2
__RNvXNvNtNtCs3bJEMBXHbwl_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception0
	sub	sp, sp, #48
	.cfi_def_cfa_offset 48
	stp	x20, x19, [sp, #16]
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_remember_state
	mov	x19, x0
	ldr	x0, [x0]
	bl	__RNvYNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrNtNtNtCs3bJEMBXHbwl_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	mov	x20, x0
	cbz	x0, LBB7_5
	ldr	x8, [x19, #8]
	cbz	x8, LBB7_4
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	ccmp	x9, #0, #4, hs
	b.eq	LBB7_4
	sub	x8, x8, #1
	mov	x9, sp
	str	x8, [sp, #8]
	mov	w8, #3
	strb	w8, [sp]
Ltmp1:
	add	x0, x9, #8
	bl	__RNvXsd_NtNtCs3bJEMBXHbwl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
Ltmp2:
LBB7_4:
	str	x20, [x19, #8]
LBB7_5:
	cmp	x20, #0
	cset	w0, ne
	.cfi_def_cfa wsp, 48
	ldp	x29, x30, [sp, #32]
	ldp	x20, x19, [sp, #16]
	add	sp, sp, #48
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
LBB7_6:
	.cfi_restore_state
Ltmp3:
	str	x20, [x19, #8]
	bl	__Unwind_Resume
Lfunc_end0:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table7:
Lexception0:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 Lcst_end0-Lcst_begin0
Lcst_begin0:
	.uleb128 Lfunc_begin0-Lfunc_begin0
	.uleb128 Ltmp1-Lfunc_begin0
	.byte	0
	.byte	0
	.uleb128 Ltmp1-Lfunc_begin0
	.uleb128 Ltmp2-Ltmp1
	.uleb128 Ltmp3-Lfunc_begin0
	.byte	0
	.uleb128 Ltmp2-Lfunc_begin0
	.uleb128 Lfunc_end0-Ltmp2
	.byte	0
	.byte	0
Lcst_end0:
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RNvYINtNvNtNtCs3bJEMBXHbwl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
Lfunc_begin1:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception1
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	stp	x20, x19, [sp, #32]
	stp	x29, x30, [sp, #48]
	add	x29, sp, #48
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_remember_state
	mov	x19, x0
	str	wzr, [sp, #12]
	cmp	w1, #128
	b.hs	LBB8_2
	strb	w1, [sp, #12]
	mov	w2, #1
	b	LBB8_7
LBB8_2:
	mov	w9, #-128
	mov	w8, #-128
	bfxil	w8, w1, #0, #6
	cmp	w1, #2048
	b.hs	LBB8_4
	lsr	w9, w1, #6
	orr	w9, w9, #0xc0
	strb	w9, [sp, #12]
	strb	w8, [sp, #13]
	mov	w2, #2
	b	LBB8_7
LBB8_4:
	mov	w10, #-128
	bfxil	w10, w1, #6, #6
	lsr	w11, w1, #16
	cbnz	w11, LBB8_6
	lsr	w9, w1, #12
	orr	w9, w9, #0xe0
	strb	w9, [sp, #12]
	strb	w10, [sp, #13]
	strb	w8, [sp, #14]
	mov	w2, #3
	b	LBB8_7
LBB8_6:
	lsr	w11, w1, #18
	orr	w11, w11, #0xfffffff0
	strb	w11, [sp, #12]
	bfxil	w9, w1, #12, #6
	strb	w9, [sp, #13]
	strb	w10, [sp, #14]
	strb	w8, [sp, #15]
	mov	w2, #4
LBB8_7:
	ldr	x0, [x19]
	add	x1, sp, #12
	bl	__RNvYNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrNtNtNtCs3bJEMBXHbwl_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	mov	x20, x0
	cbz	x0, LBB8_12
	ldr	x8, [x19, #8]
	cbz	x8, LBB8_11
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	ccmp	x9, #0, #4, hs
	b.eq	LBB8_11
	sub	x8, x8, #1
	add	x9, sp, #16
	str	x8, [sp, #24]
	mov	w8, #3
	strb	w8, [sp, #16]
Ltmp4:
	add	x0, x9, #8
	bl	__RNvXsd_NtNtCs3bJEMBXHbwl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
Ltmp5:
LBB8_11:
	str	x20, [x19, #8]
LBB8_12:
	cmp	x20, #0
	cset	w0, ne
	.cfi_def_cfa wsp, 64
	ldp	x29, x30, [sp, #48]
	ldp	x20, x19, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
LBB8_13:
	.cfi_restore_state
Ltmp6:
	str	x20, [x19, #8]
	bl	__Unwind_Resume
Lfunc_end1:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table8:
Lexception1:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 Lcst_end1-Lcst_begin1
Lcst_begin1:
	.uleb128 Lfunc_begin1-Lfunc_begin1
	.uleb128 Ltmp4-Lfunc_begin1
	.byte	0
	.byte	0
	.uleb128 Ltmp4-Lfunc_begin1
	.uleb128 Ltmp5-Ltmp4
	.uleb128 Ltmp6-Lfunc_begin1
	.byte	0
	.uleb128 Ltmp5-Lfunc_begin1
	.uleb128 Lfunc_end1-Ltmp5
	.byte	0
	.byte	0
Lcst_end1:
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RNvYINtNvNtNtCs3bJEMBXHbwl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.cfi_startproc
	mov	x3, x2
	mov	x2, x1
Lloh4:
	adrp	x1, l_vtable.0@PAGE
Lloh5:
	add	x1, x1, l_vtable.0@PAGEOFF
	b	__RNvNtCs3bJEMBXHbwl_4core3fmt5write
	.loh AdrpAdd	Lloh4, Lloh5
	.cfi_endproc

	.p2align	2
__RNvYNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrNtNtNtCs3bJEMBXHbwl_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
Lfunc_begin2:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception2
	sub	sp, sp, #128
	.cfi_def_cfa_offset 128
	stp	x28, x27, [sp, #32]
	stp	x26, x25, [sp, #48]
	stp	x24, x23, [sp, #64]
	stp	x22, x21, [sp, #80]
	stp	x20, x19, [sp, #96]
	stp	x29, x30, [sp, #112]
	add	x29, sp, #112
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	.cfi_offset w23, -56
	.cfi_offset w24, -64
	.cfi_offset w25, -72
	.cfi_offset w26, -80
	.cfi_offset w27, -88
	.cfi_offset w28, -96
	.cfi_remember_state
	cbz	x2, LBB10_18
	mov	x19, x2
	mov	x20, x1
	mov	x21, x0
	mov	x23, sp
	add	x24, sp, #16
	mov	w26, #3
	mov	w27, #255
Lloh6:
	adrp	x25, l_alloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2@PAGE
Lloh7:
	add	x25, x25, l_alloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2@PAGEOFF
	b	LBB10_5
LBB10_2:
	ldrb	w8, [x22, #16]
LBB10_3:
	cmp	w8, #35
	b.ne	LBB10_19
LBB10_4:
	cbz	x19, LBB10_18
LBB10_5:
	mov	x0, x21
	mov	x1, x20
	mov	x2, x19
	bl	__RNvXs3_NtNtNtCsdnanKjkF2cC_3std3sys5stdio4unixNtB5_6StderrNtNtNtCs3bJEMBXHbwl_4core2io5write5Write5write
	mov	x22, x1
	stp	x0, x1, [sp]
	cmp	x0, #1
	b.ne	LBB10_10
	and	x8, x22, #0x3
	cmp	x8, #1
	b.gt	LBB10_13
	cbz	x8, LBB10_2
	ldrb	w8, [x22, #31]
	cmp	w8, #35
	b.ne	LBB10_19
	sub	x8, x22, #1
	str	x8, [sp, #24]
	strb	w26, [sp, #16]
	add	x0, x24, #8
	bl	__RNvXsd_NtNtCs3bJEMBXHbwl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	cbnz	x19, LBB10_5
	b	LBB10_18
LBB10_10:
	cbz	x22, LBB10_20
	subs	x8, x19, x22
	b.lo	LBB10_21
	add	x20, x20, x22
	mov	x19, x8
	cbnz	x8, LBB10_5
	b	LBB10_18
LBB10_13:
	cmp	x8, #2
	b.ne	LBB10_17
Ltmp7:
	bl	__RNvNtNtNtCs3bJEMBXHbwl_4core2io5error12os_functions16get_os_functions
Ltmp8:
	lsr	x8, x22, #32
	ldr	x9, [x0, #16]
Ltmp9:
	mov	x0, x8
	blr	x9
Ltmp10:
	tbnz	w0, #0, LBB10_4
	b	LBB10_19
LBB10_17:
	ubfx	x8, x22, #32, #8
	lsr	x9, x22, #34
	cmp	x9, #11
	csel	w8, w8, w27, lo
	b	LBB10_3
LBB10_18:
	mov	x22, #0
LBB10_19:
	mov	x0, x22
	.cfi_def_cfa wsp, 128
	ldp	x29, x30, [sp, #112]
	ldp	x20, x19, [sp, #96]
	ldp	x22, x21, [sp, #80]
	ldp	x24, x23, [sp, #64]
	ldp	x26, x25, [sp, #48]
	ldp	x28, x27, [sp, #32]
	add	sp, sp, #128
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	ret
LBB10_20:
	.cfi_restore_state
	mov	x22, x25
	b	LBB10_19
LBB10_21:
Lloh8:
	adrp	x3, l_alloc_22d3a9dec0cad4fe8d6eb3a7bed31903@PAGE
Lloh9:
	add	x3, x3, l_alloc_22d3a9dec0cad4fe8d6eb3a7bed31903@PAGEOFF
	mov	x0, x22
	mov	x1, x19
	mov	x2, x19
	bl	__RNvNtNtCs3bJEMBXHbwl_4core5slice5index16slice_index_fail
LBB10_22:
Ltmp11:
	mov	x19, x0
Ltmp12:
	add	x0, x23, #8
	bl	__RINvNtCs3bJEMBXHbwl_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
Ltmp13:
	mov	x0, x19
	bl	__Unwind_Resume
LBB10_24:
Ltmp14:
	bl	__RNvNtCs3bJEMBXHbwl_4core9panicking16panic_in_cleanup
	.loh AdrpAdd	Lloh6, Lloh7
	.loh AdrpAdd	Lloh8, Lloh9
Lfunc_end2:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table10:
Lexception2:
	.byte	255
	.byte	155
	.uleb128 Lttbase0-Lttbaseref0
Lttbaseref0:
	.byte	1
	.uleb128 Lcst_end2-Lcst_begin2
Lcst_begin2:
	.uleb128 Lfunc_begin2-Lfunc_begin2
	.uleb128 Ltmp7-Lfunc_begin2
	.byte	0
	.byte	0
	.uleb128 Ltmp7-Lfunc_begin2
	.uleb128 Ltmp10-Ltmp7
	.uleb128 Ltmp11-Lfunc_begin2
	.byte	0
	.uleb128 Ltmp10-Lfunc_begin2
	.uleb128 Ltmp12-Ltmp10
	.byte	0
	.byte	0
	.uleb128 Ltmp12-Lfunc_begin2
	.uleb128 Ltmp13-Ltmp12
	.uleb128 Ltmp14-Lfunc_begin2
	.byte	1
	.uleb128 Ltmp13-Lfunc_begin2
	.uleb128 Lfunc_end2-Ltmp13
	.byte	0
	.byte	0
Lcst_end2:
	.byte	127
	.byte	0
	.p2align	2, 0x0
Lttbase0:
	.byte	0
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.p2align	2
__RNvYNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrNtNtNtCs3bJEMBXHbwl_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
Lfunc_begin3:
	.cfi_startproc
	.cfi_personality 155, _rust_eh_personality
	.cfi_lsda 16, Lexception3
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	stp	x20, x19, [sp, #32]
	stp	x29, x30, [sp, #48]
	add	x29, sp, #48
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_remember_state
	mov	x3, x2
	mov	x2, x1
	stp	x0, xzr, [sp]
Ltmp15:
Lloh10:
	adrp	x1, l_vtable.0@PAGE
Lloh11:
	add	x1, x1, l_vtable.0@PAGEOFF
	mov	x0, sp
	bl	__RNvNtCs3bJEMBXHbwl_4core3fmt5write
Ltmp16:
	cbz	w0, LBB11_5
	ldr	x0, [sp, #8]
	cbnz	x0, LBB11_9
Ltmp17:
Lloh12:
	adrp	x0, l_alloc_a439077caaee6bab9af745f1531d72a4@PAGE
Lloh13:
	add	x0, x0, l_alloc_a439077caaee6bab9af745f1531d72a4@PAGEOFF
Lloh14:
	adrp	x2, l_alloc_66f584c540a2b1d04ce5ea73db115bd6@PAGE
Lloh15:
	add	x2, x2, l_alloc_66f584c540a2b1d04ce5ea73db115bd6@PAGEOFF
	mov	w1, #173
	bl	__RNvNtCs3bJEMBXHbwl_4core9panicking9panic_fmt
Ltmp18:
	brk	#0x1
LBB11_5:
	ldr	x8, [sp, #8]
	cbz	x8, LBB11_8
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	ccmp	x9, #0, #4, hs
	b.eq	LBB11_8
	sub	x8, x8, #1
	add	x9, sp, #16
	str	x8, [sp, #24]
	mov	w8, #3
	strb	w8, [sp, #16]
	add	x0, x9, #8
	bl	__RNvXsd_NtNtCs3bJEMBXHbwl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
LBB11_8:
	mov	x0, #0
LBB11_9:
	.cfi_def_cfa wsp, 64
	ldp	x29, x30, [sp, #48]
	ldp	x20, x19, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	ret
LBB11_10:
	.cfi_restore_state
Ltmp19:
	mov	x19, x0
Ltmp20:
	mov	x0, sp
	bl	__RINvNtCs3bJEMBXHbwl_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe
Ltmp21:
	mov	x0, x19
	bl	__Unwind_Resume
LBB11_12:
Ltmp22:
	bl	__RNvNtCs3bJEMBXHbwl_4core9panicking16panic_in_cleanup
	.loh AdrpAdd	Lloh10, Lloh11
	.loh AdrpAdd	Lloh14, Lloh15
	.loh AdrpAdd	Lloh12, Lloh13
Lfunc_end3:
	.cfi_endproc
	.section	__TEXT,__gcc_except_tab
	.p2align	2, 0x0
GCC_except_table11:
Lexception3:
	.byte	255
	.byte	155
	.uleb128 Lttbase1-Lttbaseref1
Lttbaseref1:
	.byte	1
	.uleb128 Lcst_end3-Lcst_begin3
Lcst_begin3:
	.uleb128 Ltmp15-Lfunc_begin3
	.uleb128 Ltmp18-Ltmp15
	.uleb128 Ltmp19-Lfunc_begin3
	.byte	0
	.uleb128 Ltmp18-Lfunc_begin3
	.uleb128 Ltmp20-Ltmp18
	.byte	0
	.byte	0
	.uleb128 Ltmp20-Lfunc_begin3
	.uleb128 Ltmp21-Ltmp20
	.uleb128 Ltmp22-Lfunc_begin3
	.byte	1
	.uleb128 Ltmp21-Lfunc_begin3
	.uleb128 Lfunc_end3-Ltmp21
	.byte	0
	.byte	0
Lcst_end3:
	.byte	127
	.byte	0
	.p2align	2, 0x0
Lttbase1:
	.byte	0
	.p2align	2, 0x0

	.section	__TEXT,__text,regular,pure_instructions
	.globl	_access_all_tls
	.p2align	2
_access_all_tls:
	.cfi_startproc
	sub	sp, sp, #80
	.cfi_def_cfa_offset 80
	stp	x24, x23, [sp, #16]
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	stp	x29, x30, [sp, #64]
	add	x29, sp, #64
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	.cfi_offset w19, -24
	.cfi_offset w20, -32
	.cfi_offset w21, -40
	.cfi_offset w22, -48
	.cfi_offset w23, -56
	.cfi_offset w24, -64
	.cfi_remember_state
Lloh16:
	adrp	x0, __RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@TLVPPAGE
Lloh17:
	ldr	x0, [x0, __RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@TLVPPAGEOFF]
	ldr	x8, [x0]
	blr	x8
	ldr	x8, [x0]
	add	x20, x8, #1
	str	x20, [x0]
Lloh18:
	adrp	x0, __RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64@TLVPPAGE
Lloh19:
	ldr	x0, [x0, __RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64@TLVPPAGEOFF]
	ldr	x8, [x0]
	blr	x8
	ldr	x21, [x0]
Lloh20:
	adrp	x0, __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL@TLVPPAGE
Lloh21:
	ldr	x0, [x0, __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL@TLVPPAGEOFF]
	ldr	x8, [x0]
	blr	x8
	ldr	x22, [x0]
Lloh22:
	adrp	x0, __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@TLVPPAGE
Lloh23:
	ldr	x0, [x0, __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@TLVPPAGEOFF]
	ldr	x8, [x0]
	blr	x8
	ldrb	w8, [x0, #8]
	cbnz	w8, LBB12_7
LBB12_1:
	ldr	x19, [x0]
Lloh24:
	adrp	x0, __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@TLVPPAGE
Lloh25:
	ldr	x0, [x0, __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@TLVPPAGEOFF]
	ldr	x8, [x0]
	blr	x8
	ldrb	w8, [x0, #8]
	cbz	w8, LBB12_5
	ldr	x23, [x0]
LBB12_3:
Lloh26:
	adrp	x0, __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@TLVPPAGE
Lloh27:
	ldr	x0, [x0, __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@TLVPPAGEOFF]
	ldr	x8, [x0]
	blr	x8
	ldrb	w8, [x0, #8]
	cmp	w8, #1
	b.ne	LBB12_6
LBB12_4:
	add	x8, x22, x19
	add	x8, x8, x23
	add	x9, x21, x20
	add	x8, x9, x8
	ldr	x9, [x0]
	add	x0, x8, x9
	.cfi_def_cfa wsp, 80
	ldp	x29, x30, [sp, #64]
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x24, x23, [sp, #16]
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	.cfi_restore w29
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	ret
LBB12_5:
	.cfi_restore_state
	mov	w8, #7
	str	x8, [sp, #8]
	add	x8, sp, #8
	; InlineAsm Start
	; InlineAsm End
	ldr	x23, [sp, #8]
	str	x23, [x0]
	mov	w8, #1
	strb	w8, [x0, #8]
	b	LBB12_3
LBB12_6:
	mov	x1, #0
	bl	__RINvMs0_NtNtNtNtCsdnanKjkF2cC_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCs3bJEMBXHbwl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	cbnz	x0, LBB12_4
	b	LBB12_9
LBB12_7:
	cmp	w8, #1
	b.ne	LBB12_9
Lloh28:
	adrp	x1, __RINvNtNtNtNtCsdnanKjkF2cC_3std3sys12thread_local6native5eager7destroyINtNtCs3bJEMBXHbwl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_@PAGE
Lloh29:
	add	x1, x1, __RINvNtNtNtNtCsdnanKjkF2cC_3std3sys12thread_local6native5eager7destroyINtNtCs3bJEMBXHbwl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_@PAGEOFF
	mov	x19, x0
	bl	__RNvNtNtNtNtCsdnanKjkF2cC_3std3sys12thread_local11destructors4list8register
	mov	x0, x19
	strb	wzr, [x19, #8]
	b	LBB12_1
LBB12_9:
Lloh30:
	adrp	x0, l_alloc_cf04a7d848f454bae906dcea67110b94@PAGE
Lloh31:
	add	x0, x0, l_alloc_cf04a7d848f454bae906dcea67110b94@PAGEOFF
	bl	__RNvNtNtCsdnanKjkF2cC_3std6thread5local18panic_access_error
	.loh AdrpLdr	Lloh22, Lloh23
	.loh AdrpLdr	Lloh20, Lloh21
	.loh AdrpLdr	Lloh18, Lloh19
	.loh AdrpLdr	Lloh16, Lloh17
	.loh AdrpLdr	Lloh24, Lloh25
	.loh AdrpLdr	Lloh26, Lloh27
	.loh AdrpAdd	Lloh28, Lloh29
	.loh AdrpAdd	Lloh30, Lloh31
	.cfi_endproc

	.section	__TEXT,__const
l_alloc_70165e1942fbf2cb7aee6a08556ee215:
	.ascii	"fatal runtime error: unreachable, aborting\n"

	.section	__TEXT,__cstring,cstring_literals
l_alloc_cccd7a83c897ff0b212dd50c8ec2f4d1:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/std/src/thread/local.rs"

	.section	__DATA,__const
	.p2align	3, 0x0
l_alloc_cf04a7d848f454bae906dcea67110b94:
	.quad	l_alloc_cccd7a83c897ff0b212dd50c8ec2f4d1
	.asciz	"\205\000\000\000\000\000\000\000\255\001\000\000\031\000\000"

	.p2align	3, 0x0
l_vtable.0:
	.quad	__RINvNtCs3bJEMBXHbwl_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrEECsir34p5gJ1Pk_9tls_probe
	.asciz	"\020\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	__RNvXNvNtNtCs3bJEMBXHbwl_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.quad	__RNvYINtNvNtNtCs3bJEMBXHbwl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.quad	__RNvYINtNvNtNtCs3bJEMBXHbwl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCsdnanKjkF2cC_3std3sys5stdio4unix6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe

	.section	__TEXT,__const
l_alloc_a439077caaee6bab9af745f1531d72a4:
	.ascii	"a formatting trait implementation returned an error when the underlying stream did not"

	.section	__TEXT,__cstring,cstring_literals
l_alloc_cb6f00447019d73f4f2c3d453e522c22:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/io/write.rs"

	.section	__DATA,__const
	.p2align	3, 0x0
l_alloc_66f584c540a2b1d04ce5ea73db115bd6:
	.quad	l_alloc_cb6f00447019d73f4f2c3d453e522c22
	.asciz	"\202\000\000\000\000\000\000\000\233\001\000\000\021\000\000"

	.section	__DATA,__thread_data,thread_local_regular
	.p2align	3, 0x0
__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64$tlv$init:
	.ascii	"\210wfUD3\"\021"

	.section	__DATA,__thread_vars,thread_local_variables
	.globl	__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64:
	.quad	__tlv_bootstrap
	.quad	0
	.quad	__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64$tlv$init

	.section	__DATA,__thread_data,thread_local_regular
	.p2align	6, 0x0
__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64$tlv$init:
	.asciz	"\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000"

	.section	__DATA,__thread_vars,thread_local_variables
	.globl	__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64:
	.quad	__tlv_bootstrap
	.quad	0
	.quad	__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64$tlv$init

	.section	__DATA,__thread_data,thread_local_regular
	.p2align	3, 0x0
__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL$tlv$init:
	.ascii	"c\000\000\000\000\000\000\000\001"
	.space	7

	.section	__DATA,__thread_vars,thread_local_variables
	.globl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL:
	.quad	__tlv_bootstrap
	.quad	0
	.quad	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL$tlv$init

.tbss __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL$tlv$init, 16, 3

	.globl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.quad	__tlv_bootstrap
	.quad	0
	.quad	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL$tlv$init

	.section	__DATA,__thread_data,thread_local_regular
	.p2align	3, 0x0
__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL$tlv$init:
	.asciz	"*\000\000\000\000\000\000"

	.section	__DATA,__thread_vars,thread_local_variables
	.globl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.quad	__tlv_bootstrap
	.quad	0
	.quad	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL$tlv$init

.tbss __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL$tlv$init, 16, 3

	.globl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL:
	.quad	__tlv_bootstrap
	.quad	0
	.quad	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL$tlv$init

	.section	__TEXT,__const
l_alloc_8d68fcbc011419193bd208f22e2789d1:
	.ascii	"failed to write whole buffer"

	.section	__DATA,__const
	.p2align	3, 0x0
l_alloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2:
	.quad	l_alloc_8d68fcbc011419193bd208f22e2789d1
	.ascii	"\034\000\000\000\000\000\000\000\027"
	.space	7

	.p2align	3, 0x0
l_alloc_22d3a9dec0cad4fe8d6eb3a7bed31903:
	.quad	l_alloc_cb6f00447019d73f4f2c3d453e522c22
	.asciz	"\202\000\000\000\000\000\000\000\334\000\000\000$\000\000"

.subsections_via_symbols
