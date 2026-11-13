	.def	"@feat.00";
	.scl	3;
	.type	0;
	.endef
	.globl	"@feat.00"
"@feat.00" = 0
	.file	"tls_probe.d6bd21401e7e8eac-cgu.0"
	.def	_RINvMs0_NtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_;
	.scl	3;
	.type	32;
	.endef
	.section	.text$unlikely,"xr",one_only,_RINvMs0_NtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_,unique,0
	.p2align	2
_RINvMs0_NtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_:
.seh_proc _RINvMs0_NtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	sub	sp, sp, #48
	.seh_stackalloc	48
	str	x19, [sp, #16]
	.seh_save_reg	x19, 16
	stp	x29, x30, [sp, #24]
	.seh_save_fplr	24
	add	x29, sp, #24
	.seh_add_fp	24
	.seh_endprologue
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
	add	x9, x29, #16
	str	x8, [x29, #16]
	//APP
	//NO_APP
	ldr	x9, [x0]
	ldrb	w8, [x0, #8]
	ldr	x10, [x29, #16]
	str	x9, [sp]
	mov	w9, #1
	cmp	w8, #1
	str	x10, [x0]
	strb	w9, [x0, #8]
	b.ne	.LBB0_8
	mov	x19, x0
	mov	x0, sp
	bl	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
	b	.LBB0_10
.LBB0_8:
	cbnz	w8, .LBB0_12
.LBB0_9:
	adrp	x1, _RINvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native4lazy7destroyINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_
	add	x1, x1, :lo12:_RINvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native4lazy7destroyINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_
	mov	x19, x0
	bl	_RNvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local11destructors4list8register
.LBB0_10:
	mov	x0, x19
.LBB0_11:
	.seh_startepilogue
	ldp	x29, x30, [sp, #24]
	.seh_save_fplr	24
	ldr	x19, [sp, #16]
	.seh_save_reg	x19, 16
	add	sp, sp, #48
	.seh_stackalloc	48
	.seh_endepilogue
	ret
.LBB0_12:
	adrp	x1, alloc_70165e1942fbf2cb7aee6a08556ee215
	add	x1, x1, :lo12:alloc_70165e1942fbf2cb7aee6a08556ee215
	add	x0, sp, #8
	mov	w2, #87
	str	wzr, [sp, #8]
	strb	wzr, [sp, #12]
	bl	_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	str	x0, [x29, #16]
	add	x0, x29, #16
	bl	_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	mov	w0, #7
	//APP
	brk	#0xf003
	//NO_APP
	brk	#0x1
	.seh_endfunclet
	.seh_endproc

	.def	_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe,unique,1
	.p2align	2
_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe:
.seh_proc _RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	sub	sp, sp, #32
	.seh_stackalloc	32
	stp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	x29, sp, #16
	.seh_add_fp	16
	.seh_endprologue
	ldr	x8, [x0]
	cbz	x8, .LBB1_4
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	b.lo	.LBB1_4
	cbz	x9, .LBB1_4
	sub	x8, x8, #1
	mov	w9, #3
	str	x8, [sp, #8]
	mov	x8, sp
	add	x0, x8, #8
	strb	w9, [sp]
	bl	_RNvXsd_NtNtCsaF4MlZlPuCq_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.LBB1_4:
	.seh_startepilogue
	ldp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	sp, sp, #32
	.seh_stackalloc	32
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.def	_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe,unique,2
	.p2align	2
_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe:
.seh_proc _RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe
	sub	sp, sp, #32
	.seh_stackalloc	32
	stp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	x29, sp, #16
	.seh_add_fp	16
	.seh_endprologue
	ldr	x8, [x0, #8]
	cbz	x8, .LBB2_4
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	b.lo	.LBB2_4
	cbz	x9, .LBB2_4
	sub	x8, x8, #1
	mov	w9, #3
	str	x8, [sp, #8]
	mov	x8, sp
	add	x0, x8, #8
	strb	w9, [sp]
	bl	_RNvXsd_NtNtCsaF4MlZlPuCq_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.LBB2_4:
	.seh_startepilogue
	ldp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	sp, sp, #32
	.seh_stackalloc	32
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.def	_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe,unique,3
	.p2align	2
_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe:
.seh_proc _RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
	sub	sp, sp, #32
	.seh_stackalloc	32
	stp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	x29, sp, #16
	.seh_add_fp	16
	.seh_endprologue
	ldr	x8, [x0]
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	ccmp	x9, #0, #4, hs
	b.eq	.LBB3_2
	sub	x8, x8, #1
	mov	w9, #3
	str	x8, [sp, #8]
	mov	x8, sp
	add	x0, x8, #8
	strb	w9, [sp]
	bl	_RNvXsd_NtNtCsaF4MlZlPuCq_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.LBB3_2:
	.seh_startepilogue
	ldp	x29, x30, [sp, #16]
	.seh_save_fplr	16
	add	sp, sp, #32
	.seh_stackalloc	32
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.def	_RINvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native4lazy7destroyINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native4lazy7destroyINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_,unique,4
	.p2align	2
_RINvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native4lazy7destroyINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_:
	ldrb	w9, [x0, #8]
	mov	w8, #2
	strb	w8, [x0, #8]
	cmp	w9, #1
	b.ne	.LBB4_2
	b	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
.LBB4_2:
	ret

	.def	_RINvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native5eager7destroyINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native5eager7destroyINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_,unique,5
	.p2align	2
_RINvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native5eager7destroyINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_:
	mov	w8, #2
	strb	w8, [x0, #8]
	b	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop

	.def	_RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls,unique,6
	.globl	_RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls
	.p2align	2
_RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls:
	adrp	x8, _tls_index
	ldr	x9, [x18, #88]
	ldr	w8, [x8, :lo12:_tls_index]
	ldr	x8, [x9, x8, lsl #3]
	add	x8, x8, :secrel_hi12:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	add	x0, x8, :secrel_lo12:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	ret

	.def	_RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls,unique,7
	.globl	_RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls
	.p2align	2
_RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls:
	adrp	x8, _tls_index
	ldr	x9, [x18, #88]
	ldr	w8, [x8, :lo12:_tls_index]
	ldr	x8, [x9, x8, lsl #3]
	add	x8, x8, :secrel_hi12:_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	add	x0, x8, :secrel_lo12:_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	ret

	.def	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls,unique,8
	.globl	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls
	.p2align	2
_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls:
	adrp	x8, _tls_index
	ldr	x9, [x18, #88]
	ldr	w8, [x8, :lo12:_tls_index]
	ldr	x8, [x9, x8, lsl #3]
	add	x8, x8, :secrel_hi12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	add	x0, x8, :secrel_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	ret

	.def	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls,unique,9
	.globl	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls
	.p2align	2
_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls:
	adrp	x8, _tls_index
	ldr	x9, [x18, #88]
	ldr	w8, [x8, :lo12:_tls_index]
	ldr	x8, [x9, x8, lsl #3]
	add	x8, x8, :secrel_hi12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	add	x0, x8, :secrel_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	ret

	.def	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls,unique,10
	.globl	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls
	.p2align	2
_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls:
	adrp	x8, _tls_index
	ldr	x9, [x18, #88]
	ldr	w8, [x8, :lo12:_tls_index]
	ldr	x8, [x9, x8, lsl #3]
	add	x8, x8, :secrel_hi12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	add	x0, x8, :secrel_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	ret

	.def	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls,unique,11
	.globl	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls
	.p2align	2
_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls:
	adrp	x8, _tls_index
	ldr	x9, [x18, #88]
	ldr	w8, [x8, :lo12:_tls_index]
	ldr	x8, [x9, x8, lsl #3]
	add	x8, x8, :secrel_hi12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	add	x0, x8, :secrel_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	ret

	.def	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop,unique,12
	.globl	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
	.p2align	2
_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop:
.seh_proc _RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCsaF4MlZlPuCq_4core3ops4drop4Drop4drop
	sub	sp, sp, #16
	.seh_stackalloc	16
	.seh_endprologue
	ldr	x9, [x0]
	add	x8, sp, #8
	str	x9, [sp, #8]
	//APP
	//NO_APP
	.seh_startepilogue
	add	sp, sp, #16
	.seh_stackalloc	16
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_endproc

	.def	_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,13
	.p2align	2
_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin0:
.seh_proc _RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.seh_handler __CxxFrameHandler3, @unwind, @except
	sub	sp, sp, #64
	.seh_stackalloc	64
	str	x19, [sp, #16]
	.seh_save_reg	x19, 16
	stp	x29, x30, [sp, #24]
	.seh_save_fplr	24
	add	x29, sp, #24
	.seh_add_fp	24
	.seh_endprologue
	mov	x3, #-2
	mov	x19, x0
	stur	x3, [x29, #24]
	ldr	x0, [x0]
	bl	_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	cbz	x0, .LBB13_7
	ldr	x8, [x19, #8]
	cbz	x8, .LBB13_6
	and	x9, x8, #0x3
	str	x0, [x29, #16]
	sub	x10, x9, #2
	str	x19, [x29, #32]
	cmp	x10, #2
	b.lo	.LBB13_5
	cbz	x9, .LBB13_5
	sub	x8, x8, #1
	mov	w9, #3
	stur	x8, [x29, #-16]
	sub	x8, x29, #24
	sturb	w9, [x29, #-24]
.Ltmp0:
	add	x0, x8, #8
	bl	_RNvXsd_NtNtCsaF4MlZlPuCq_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.Ltmp1:
.LBB13_5:
	ldr	x19, [x29, #32]
	ldr	x0, [x29, #16]
.LBB13_6:
	str	x0, [x19, #8]
.LBB13_7:
	cmp	x0, #0
	cset	w0, ne
	.seh_startepilogue
	ldp	x29, x30, [sp, #24]
	.seh_save_fplr	24
	ldr	x19, [sp, #16]
	.seh_save_reg	x19, 16
	add	sp, sp, #64
	.seh_stackalloc	64
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@IMGREL
	.section	.text,"xr",one_only,_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,13
	.seh_endproc
	.def	"?dtor$8@?0?_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?dtor$8@?0?_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA":
.seh_proc "?dtor$8@?0?_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA"
.LBB13_8:
	str	x19, [sp, #-32]!
	.seh_save_reg_x	x19, 32
	stp	x29, x30, [sp, #8]
	.seh_save_fplr	8
	.seh_endprologue
	ldr	x8, [x29, #32]
	ldr	x9, [x29, #16]
	str	x9, [x8, #8]
	.seh_startepilogue
	ldp	x29, x30, [sp, #8]
	.seh_save_fplr	8
	ldr	x19, [sp], #32
	.seh_save_reg_x	x19, 32
	.seh_endepilogue
	ret
.Lfunc_end0:
	.seh_endfunclet
	.seh_handlerdata
	.section	.text,"xr",one_only,_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,13
	.seh_endproc
	.section	.xdata,"dr",associative,_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,0
	.p2align	2, 0x0
$cppxdata$_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
	.word	429065506
	.word	1
	.word	$stateUnwindMap$_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@IMGREL
	.word	0
	.word	0
	.word	3
	.word	$ip2state$_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@IMGREL
	.word	-16
	.word	0
	.word	1
$stateUnwindMap$_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
	.word	-1
	.word	"?dtor$8@?0?_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA"@IMGREL
$ip2state$_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
	.word	.Lfunc_begin0@IMGREL
	.word	-1
	.word	.Ltmp0@IMGREL
	.word	0
	.word	.Ltmp1@IMGREL
	.word	-1
	.section	.text,"xr",one_only,_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,13

	.def	_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,14
	.p2align	2
_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin1:
.seh_proc _RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.seh_handler __CxxFrameHandler3, @unwind, @except
	sub	sp, sp, #80
	.seh_stackalloc	80
	str	x19, [sp, #32]
	.seh_save_reg	x19, 32
	stp	x29, x30, [sp, #40]
	.seh_save_fplr	40
	add	x29, sp, #40
	.seh_add_fp	40
	.seh_endprologue
	mov	x2, #-2
	mov	x19, x0
	cmp	w1, #128
	stur	x2, [x29, #24]
	str	wzr, [x29, #36]
	b.hs	.LBB14_2
	strb	w1, [x29, #36]
	mov	w2, #1
	b	.LBB14_7
.LBB14_2:
	mov	w8, #-128
	cmp	w1, #2048
	mov	w9, #-128
	bfxil	w8, w1, #0, #6
	b.hs	.LBB14_4
	lsr	w9, w1, #6
	strb	w8, [x29, #37]
	mov	w2, #2
	orr	w9, w9, #0xc0
	strb	w9, [x29, #36]
	b	.LBB14_7
.LBB14_4:
	mov	w10, #-128
	lsr	w11, w1, #16
	bfxil	w10, w1, #6, #6
	cbnz	w11, .LBB14_6
	lsr	w9, w1, #12
	strb	w10, [x29, #37]
	mov	w2, #3
	strb	w8, [x29, #38]
	orr	w9, w9, #0xe0
	strb	w9, [x29, #36]
	b	.LBB14_7
.LBB14_6:
	lsr	w11, w1, #18
	bfxil	w9, w1, #12, #6
	strb	w10, [x29, #38]
	mov	w2, #4
	strb	w8, [x29, #39]
	orr	w10, w11, #0xfffffff0
	strb	w9, [x29, #37]
	strb	w10, [x29, #36]
.LBB14_7:
	ldr	x0, [x19]
	add	x1, x29, #36
	bl	_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	cbz	x0, .LBB14_14
	ldr	x8, [x19, #8]
	cbz	x8, .LBB14_13
	and	x9, x8, #0x3
	stur	x0, [x29, #-32]
	sub	x10, x9, #2
	str	x19, [x29, #16]
	cmp	x10, #2
	b.lo	.LBB14_12
	cbz	x9, .LBB14_12
	sub	x8, x8, #1
	mov	w9, #3
	stur	x8, [x29, #-16]
	sub	x8, x29, #24
	sturb	w9, [x29, #-24]
.Ltmp2:
	add	x0, x8, #8
	bl	_RNvXsd_NtNtCsaF4MlZlPuCq_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.Ltmp3:
.LBB14_12:
	ldr	x19, [x29, #16]
	ldur	x0, [x29, #-32]
.LBB14_13:
	str	x0, [x19, #8]
.LBB14_14:
	cmp	x0, #0
	cset	w0, ne
	.seh_startepilogue
	ldp	x29, x30, [sp, #40]
	.seh_save_fplr	40
	ldr	x19, [sp, #32]
	.seh_save_reg	x19, 32
	add	sp, sp, #80
	.seh_stackalloc	80
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@IMGREL
	.section	.text,"xr",one_only,_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,14
	.seh_endproc
	.def	"?dtor$15@?0?_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?dtor$15@?0?_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA":
.seh_proc "?dtor$15@?0?_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA"
.LBB14_15:
	str	x19, [sp, #-32]!
	.seh_save_reg_x	x19, 32
	stp	x29, x30, [sp, #8]
	.seh_save_fplr	8
	.seh_endprologue
	ldr	x8, [x29, #16]
	ldur	x9, [x29, #-32]
	str	x9, [x8, #8]
	.seh_startepilogue
	ldp	x29, x30, [sp, #8]
	.seh_save_fplr	8
	ldr	x19, [sp], #32
	.seh_save_reg_x	x19, 32
	.seh_endepilogue
	ret
.Lfunc_end1:
	.seh_endfunclet
	.seh_handlerdata
	.section	.text,"xr",one_only,_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,14
	.seh_endproc
	.section	.xdata,"dr",associative,_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,1
	.p2align	2, 0x0
$cppxdata$_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
	.word	429065506
	.word	1
	.word	$stateUnwindMap$_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@IMGREL
	.word	0
	.word	0
	.word	3
	.word	$ip2state$_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@IMGREL
	.word	-16
	.word	0
	.word	1
$stateUnwindMap$_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
	.word	-1
	.word	"?dtor$15@?0?_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA"@IMGREL
$ip2state$_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
	.word	.Lfunc_begin1@IMGREL
	.word	-1
	.word	.Ltmp2@IMGREL
	.word	0
	.word	.Ltmp3@IMGREL
	.word	-1
	.section	.text,"xr",one_only,_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,14

	.def	_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,15
	.p2align	2
_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	mov	x3, x2
	mov	x2, x1
	adrp	x1, vtable.0
	add	x1, x1, :lo12:vtable.0
	b	_RNvNtCsaF4MlZlPuCq_4core3fmt5write

	.def	_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,16
	.p2align	2
_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin2:
.seh_proc _RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	.seh_handler __CxxFrameHandler3, @unwind, @except
	sub	sp, sp, #144
	.seh_stackalloc	144
	stp	x19, x20, [sp, #48]
	.seh_save_regp	x19, 48
	stp	x21, x22, [sp, #64]
	.seh_save_regp	x21, 64
	stp	x23, x24, [sp, #80]
	.seh_save_regp	x23, 80
	stp	x25, x26, [sp, #96]
	.seh_save_regp	x25, 96
	stp	x29, x30, [sp, #112]
	.seh_save_fplr	112
	add	x29, sp, #112
	.seh_add_fp	112
	.seh_endprologue
	mov	x3, #-2
	mov	x19, x2
	mov	x20, x1
	mov	x21, x0
	sub	x23, x29, #80
	mov	w25, #3
	mov	w26, #255
	adrp	x24, alloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2
	add	x24, x24, :lo12:alloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2
	stur	x3, [x29, #16]
	b	.LBB16_3
.LBB16_1:
	ldrb	w8, [x22, #16]
.LBB16_2:
	cmp	w8, #35
	b.ne	.LBB16_19
.LBB16_3:
	cbz	x19, .LBB16_17
	mov	x0, x21
	mov	x1, x20
	mov	x2, x19
	bl	_RNvXs5_NtNtNtCs7wTP75QBMFn_3std3sys5stdio7windowsNtB5_6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write5write
	mov	x22, x1
	cmp	x0, #1
	stp	x0, x1, [x29, #-96]
	b.ne	.LBB16_9
	and	x8, x22, #0x3
	cmp	x8, #1
	b.gt	.LBB16_12
	cbz	x8, .LBB16_1
	ldrb	w8, [x22, #31]
	cmp	w8, #35
	b.ne	.LBB16_19
	sub	x8, x22, #1
	add	x0, x23, #8
	sturb	w25, [x29, #-80]
	stur	x8, [x29, #-72]
	bl	_RNvXsd_NtNtCsaF4MlZlPuCq_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	b	.LBB16_3
.LBB16_9:
	cbz	x22, .LBB16_18
	subs	x8, x19, x22
	b.lo	.LBB16_20
	add	x20, x20, x22
	mov	x19, x8
	b	.LBB16_3
.LBB16_12:
	cmp	x8, #2
	b.ne	.LBB16_16
.Ltmp6:
	stur	x0, [x29, #-104]
	bl	_RNvNtNtNtCsaF4MlZlPuCq_4core2io5error12os_functions16get_os_functions
.Ltmp7:
	ldr	x9, [x0, #16]
	lsr	x8, x22, #32
.Ltmp8:
	mov	w0, w8
	blr	x9
.Ltmp9:
	tbnz	w0, #0, .LBB16_3
	b	.LBB16_19
.LBB16_16:
	lsr	x8, x22, #34
	ubfx	x9, x22, #32, #8
	cmp	x8, #11
	csel	w8, w9, w26, lo
	b	.LBB16_2
.LBB16_17:
	mov	x22, xzr
	b	.LBB16_19
.LBB16_18:
	mov	x22, x24
.LBB16_19:
	mov	x0, x22
	.seh_startepilogue
	ldp	x29, x30, [sp, #112]
	.seh_save_fplr	112
	ldp	x25, x26, [sp, #96]
	.seh_save_regp	x25, 96
	ldp	x23, x24, [sp, #80]
	.seh_save_regp	x23, 80
	ldp	x21, x22, [sp, #64]
	.seh_save_regp	x21, 64
	ldp	x19, x20, [sp, #48]
	.seh_save_regp	x19, 48
	add	sp, sp, #144
	.seh_stackalloc	144
	.seh_endepilogue
	ret
.LBB16_20:
.Ltmp4:
	stur	x0, [x29, #-104]
	adrp	x3, alloc_ba1bfa9f01512a2cbee7a129faa5ce35
	add	x3, x3, :lo12:alloc_ba1bfa9f01512a2cbee7a129faa5ce35
	mov	x0, x22
	mov	x1, x19
	mov	x2, x19
	bl	_RNvNtNtCsaF4MlZlPuCq_4core5slice5index16slice_index_fail
.Ltmp5:
	brk	#0x1
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@IMGREL
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,16
	.seh_endproc
	.def	"?dtor$22@?0?_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?dtor$22@?0?_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA":
.seh_proc "?dtor$22@?0?_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA"
.LBB16_22:
	stp	x19, x20, [sp, #-80]!
	.seh_save_regp_x	x19, 80
	stp	x21, x22, [sp, #16]
	.seh_save_regp	x21, 16
	stp	x23, x24, [sp, #32]
	.seh_save_regp	x23, 32
	stp	x25, x26, [sp, #48]
	.seh_save_regp	x25, 48
	stp	x29, x30, [sp, #64]
	.seh_save_fplr	64
	.seh_endprologue
	ldur	x8, [x29, #-104]
	tbnz	w8, #0, .LBB16_24
.LBB16_23:
	.seh_startepilogue
	ldp	x29, x30, [sp, #64]
	.seh_save_fplr	64
	ldp	x25, x26, [sp, #48]
	.seh_save_regp	x25, 48
	ldp	x23, x24, [sp, #32]
	.seh_save_regp	x23, 32
	ldp	x21, x22, [sp, #16]
	.seh_save_regp	x21, 16
	ldp	x19, x20, [sp], #80
	.seh_save_regp_x	x19, 80
	.seh_endepilogue
	ret
.LBB16_24:
	sub	x8, x29, #96
	add	x0, x8, #8
	bl	_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
	b	.LBB16_23
.Lfunc_end2:
	.seh_endfunclet
	.seh_handlerdata
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,16
	.seh_endproc
	.section	.xdata,"dr",associative,_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,2
	.p2align	2, 0x0
$cppxdata$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
	.word	429065506
	.word	1
	.word	$stateUnwindMap$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@IMGREL
	.word	0
	.word	0
	.word	3
	.word	$ip2state$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@IMGREL
	.word	-16
	.word	0
	.word	1
$stateUnwindMap$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
	.word	-1
	.word	"?dtor$22@?0?_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA"@IMGREL
$ip2state$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
	.word	.Lfunc_begin2@IMGREL
	.word	-1
	.word	.Ltmp6@IMGREL
	.word	0
	.word	.Ltmp5@IMGREL
	.word	-1
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,16

	.def	_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,17
	.p2align	2
_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin3:
.seh_proc _RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.seh_handler __CxxFrameHandler3, @unwind, @except
	sub	sp, sp, #64
	.seh_stackalloc	64
	stp	x29, x30, [sp, #32]
	.seh_save_fplr	32
	add	x29, sp, #32
	.seh_add_fp	32
	.seh_endprologue
	mov	x3, #-2
	stur	x3, [x29, #16]
	mov	x3, x2
	mov	x2, x1
	stp	x0, xzr, [x29, #-32]
.Ltmp10:
	adrp	x1, vtable.0
	add	x1, x1, :lo12:vtable.0
	sub	x0, x29, #32
	bl	_RNvNtCsaF4MlZlPuCq_4core3fmt5write
.Ltmp11:
	cbz	w0, .LBB17_5
	ldur	x0, [x29, #-24]
	cbnz	x0, .LBB17_10
.Ltmp12:
	adrp	x0, alloc_a439077caaee6bab9af745f1531d72a4
	add	x0, x0, :lo12:alloc_a439077caaee6bab9af745f1531d72a4
	adrp	x2, alloc_1a670b50d276900533e9b5ea016aeb83
	add	x2, x2, :lo12:alloc_1a670b50d276900533e9b5ea016aeb83
	mov	w1, #173
	bl	_RNvNtCsaF4MlZlPuCq_4core9panicking9panic_fmt
.Ltmp13:
	brk	#0x1
.LBB17_5:
	ldur	x8, [x29, #-24]
	cbz	x8, .LBB17_9
	and	x9, x8, #0x3
	sub	x10, x9, #2
	cmp	x10, #2
	b.lo	.LBB17_9
	cbz	x9, .LBB17_9
	sub	x8, x8, #1
	mov	w9, #3
	stur	x8, [x29, #-8]
	sub	x8, x29, #16
	add	x0, x8, #8
	sturb	w9, [x29, #-16]
	bl	_RNvXsd_NtNtCsaF4MlZlPuCq_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.LBB17_9:
	mov	x0, xzr
.LBB17_10:
	.seh_startepilogue
	ldp	x29, x30, [sp, #32]
	.seh_save_fplr	32
	add	sp, sp, #64
	.seh_stackalloc	64
	.seh_endepilogue
	ret
	.seh_endfunclet
	.seh_handlerdata
	.word	$cppxdata$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@IMGREL
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,17
	.seh_endproc
	.def	"?dtor$11@?0?_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	2
"?dtor$11@?0?_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA":
.seh_proc "?dtor$11@?0?_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA"
.LBB17_11:
	stp	x29, x30, [sp, #-16]!
	.seh_save_fplr_x	16
	.seh_endprologue
	sub	x0, x29, #32
	bl	_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe
	.seh_startepilogue
	ldp	x29, x30, [sp], #16
	.seh_save_fplr_x	16
	.seh_endepilogue
	ret
.Lfunc_end3:
	.seh_endfunclet
	.seh_handlerdata
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,17
	.seh_endproc
	.section	.xdata,"dr",associative,_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,3
	.p2align	2, 0x0
$cppxdata$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.word	429065506
	.word	1
	.word	$stateUnwindMap$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@IMGREL
	.word	0
	.word	0
	.word	3
	.word	$ip2state$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@IMGREL
	.word	-16
	.word	0
	.word	1
$stateUnwindMap$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.word	-1
	.word	"?dtor$11@?0?_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA"@IMGREL
$ip2state$_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.word	.Lfunc_begin3@IMGREL
	.word	-1
	.word	.Ltmp10@IMGREL
	.word	0
	.word	.Ltmp13@IMGREL
	.word	-1
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrNtNtNtCsaF4MlZlPuCq_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,17

	.def	access_all_tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,access_all_tls,unique,18
	.globl	access_all_tls
	.p2align	2
access_all_tls:
.seh_proc access_all_tls
	sub	sp, sp, #80
	.seh_stackalloc	80
	stp	x19, x20, [sp, #16]
	.seh_save_regp	x19, 16
	stp	x21, x22, [sp, #32]
	.seh_save_regp	x21, 32
	stp	x23, x24, [sp, #48]
	.seh_save_regp	x23, 48
	stp	x29, x30, [sp, #64]
	.seh_save_fplr	64
	add	x29, sp, #64
	.seh_add_fp	64
	.seh_endprologue
	adrp	x23, _tls_index
	ldr	x9, [x18, #88]
	ldr	w8, [x23, :lo12:_tls_index]
	ldr	x8, [x9, x8, lsl #3]
	add	x9, x8, :secrel_hi12:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	add	x12, x8, :secrel_hi12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	add	x11, x8, :secrel_hi12:_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	ldr	x10, [x9, :secrel_lo12:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64]
	add	x13, x8, :secrel_hi12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	add	x19, x12, :secrel_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	ldrb	w8, [x19, #8]
	ldr	x21, [x11, :secrel_lo12:_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64]
	ldr	x22, [x13, :secrel_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL]
	add	x20, x10, #1
	str	x20, [x9, :secrel_lo12:_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64]
	cbnz	w8, .LBB18_7
.LBB18_1:
	ldr	w8, [x23, :lo12:_tls_index]
	ldr	x9, [x18, #88]
	ldr	x19, [x19]
	ldr	x8, [x9, x8, lsl #3]
	add	x8, x8, :secrel_hi12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	add	x8, x8, :secrel_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	ldrb	w9, [x8, #8]
	cbz	w9, .LBB18_5
	ldr	x24, [x8]
.LBB18_3:
	ldr	w8, [x23, :lo12:_tls_index]
	ldr	x9, [x18, #88]
	ldr	x8, [x9, x8, lsl #3]
	add	x8, x8, :secrel_hi12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	add	x0, x8, :secrel_lo12:_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	ldrb	w8, [x0, #8]
	cmp	w8, #1
	b.ne	.LBB18_6
.LBB18_4:
	add	x8, x22, x19
	add	x9, x21, x20
	ldr	x10, [x0]
	add	x8, x8, x24
	add	x8, x9, x8
	add	x0, x8, x10
	.seh_startepilogue
	ldp	x29, x30, [sp, #64]
	.seh_save_fplr	64
	ldp	x23, x24, [sp, #48]
	.seh_save_regp	x23, 48
	ldp	x21, x22, [sp, #32]
	.seh_save_regp	x21, 32
	ldp	x19, x20, [sp, #16]
	.seh_save_regp	x19, 16
	add	sp, sp, #80
	.seh_stackalloc	80
	.seh_endepilogue
	ret
.LBB18_5:
	mov	w9, #7
	add	x10, sp, #8
	str	x9, [sp, #8]
	mov	w9, #1
	//APP
	//NO_APP
	strb	w9, [x8, #8]
	ldr	x24, [sp, #8]
	str	x24, [x8]
	b	.LBB18_3
.LBB18_6:
	mov	x1, xzr
	bl	_RINvMs0_NtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	cbnz	x0, .LBB18_4
	b	.LBB18_9
.LBB18_7:
	cmp	w8, #1
	b.ne	.LBB18_9
	adrp	x1, _RINvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native5eager7destroyINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_
	add	x1, x1, :lo12:_RINvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local6native5eager7destroyINtNtCsaF4MlZlPuCq_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_
	mov	x0, x19
	bl	_RNvNtNtNtNtCs7wTP75QBMFn_3std3sys12thread_local11destructors4list8register
	strb	wzr, [x19, #8]
	b	.LBB18_1
.LBB18_9:
	adrp	x0, alloc_d967d5ae25e575721be85468d37a1295
	add	x0, x0, :lo12:alloc_d967d5ae25e575721be85468d37a1295
	bl	_RNvNtNtCs7wTP75QBMFn_3std6thread5local18panic_access_error
	brk	#0x1
	.seh_endfunclet
	.seh_endproc

	.section	.rdata,"dr",one_only,alloc_70165e1942fbf2cb7aee6a08556ee215,unique,19
alloc_70165e1942fbf2cb7aee6a08556ee215:
	.ascii	"fatal runtime error: unreachable, aborting\n"

	.section	.rdata,"dr",one_only,alloc_5b02399d15196f4565c9574d7e606137,unique,20
alloc_5b02399d15196f4565c9574d7e606137:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library\\std\\src\\thread\\local.rs"

	.section	.rdata,"dr",one_only,alloc_d967d5ae25e575721be85468d37a1295,unique,21
	.p2align	3, 0x0
alloc_d967d5ae25e575721be85468d37a1295:
	.xword	alloc_5b02399d15196f4565c9574d7e606137
	.asciz	"\205\000\000\000\000\000\000\000\255\001\000\000\031\000\000"

	.section	.rdata,"dr",one_only,vtable.0,unique,22
	.p2align	3, 0x0
vtable.0:
	.xword	_RINvNtCsaF4MlZlPuCq_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe
	.asciz	"\020\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.xword	_RNvXNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.xword	_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.xword	_RNvYINtNvNtNtCsaF4MlZlPuCq_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs7wTP75QBMFn_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe

	.section	.rdata,"dr",one_only,alloc_a439077caaee6bab9af745f1531d72a4,unique,23
alloc_a439077caaee6bab9af745f1531d72a4:
	.ascii	"a formatting trait implementation returned an error when the underlying stream did not"

	.section	.rdata,"dr",one_only,alloc_686723c4fc0450ab61097742d7654dd3,unique,24
alloc_686723c4fc0450ab61097742d7654dd3:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library\\core\\src\\io\\write.rs"

	.section	.rdata,"dr",one_only,alloc_1a670b50d276900533e9b5ea016aeb83,unique,25
	.p2align	3, 0x0
alloc_1a670b50d276900533e9b5ea016aeb83:
	.xword	alloc_686723c4fc0450ab61097742d7654dd3
	.asciz	"\202\000\000\000\000\000\000\000\233\001\000\000\021\000\000"

	.section	.tls$,"dw",one_only,_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,unique,26
	.globl	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	.p2align	3, 0x0
_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64:
	.ascii	"\210wfUD3\"\021"

	.section	.tls$,"dw",one_only,_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64,unique,27
	.globl	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	.p2align	6, 0x0
_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64:
	.asciz	"\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000"

	.section	.tls$,"dw",one_only,_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL,unique,28
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL:
	.ascii	"c\000\000\000\000\000\000\000\001"
	.zero	7

	.section	.tls$,"dw",one_only,_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,29
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	7

	.section	.tls$,"dw",one_only,_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,30
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.asciz	"*\000\000\000\000\000\000"

	.section	.tls$,"dw",one_only,_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,unique,31
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	7

	.section	.rdata,"dr",one_only,alloc_8d68fcbc011419193bd208f22e2789d1,unique,32
alloc_8d68fcbc011419193bd208f22e2789d1:
	.ascii	"failed to write whole buffer"

	.section	.rdata,"dr",one_only,alloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2,unique,33
	.p2align	3, 0x0
alloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2:
	.xword	alloc_8d68fcbc011419193bd208f22e2789d1
	.ascii	"\034\000\000\000\000\000\000\000\027"
	.zero	7

	.section	.rdata,"dr",one_only,alloc_ba1bfa9f01512a2cbee7a129faa5ce35,unique,34
	.p2align	3, 0x0
alloc_ba1bfa9f01512a2cbee7a129faa5ce35:
	.xword	alloc_686723c4fc0450ab61097742d7654dd3
	.asciz	"\202\000\000\000\000\000\000\000\334\000\000\000$\000\000"

	.section	.data,"dw",one_only,__imp__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,unique,35
	.globl	__imp__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	.p2align	3, 0x0
__imp__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64:
	.xword	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64

	.section	.data,"dw",one_only,__imp__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64,unique,36
	.globl	__imp__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	.p2align	3, 0x0
__imp__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64:
	.xword	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64

	.section	.data,"dw",one_only,__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL,unique,37
	.globl	__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL:
	.xword	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL

	.section	.data,"dw",one_only,__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,38
	.globl	__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.xword	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL

	.section	.data,"dw",one_only,__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,39
	.globl	__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.xword	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL

	.section	.data,"dw",one_only,__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,unique,40
	.globl	__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL:
	.xword	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL

