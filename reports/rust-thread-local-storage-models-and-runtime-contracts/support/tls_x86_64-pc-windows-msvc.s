	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.att_syntax
	.file	"tls_probe.d6bd21401e7e8eac-cgu.0"
	.def	_RINvMs0_NtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_;
	.scl	3;
	.type	32;
	.endef
	.section	.text$unlikely,"xr",one_only,_RINvMs0_NtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_,unique,0
	.p2align	4
_RINvMs0_NtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_:
.seh_proc _RINvMs0_NtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	pushq	%rsi
	.seh_pushreg %rsi
	subq	$64, %rsp
	.seh_stackalloc 64
	.seh_endprologue
	movq	%rcx, %rax
	movzbl	8(%rcx), %ecx
	testl	%ecx, %ecx
	je	.LBB0_5
	cmpl	$1, %ecx
	je	.LBB0_12
	xorl	%eax, %eax
	jmp	.LBB0_12
.LBB0_5:
	testq	%rdx, %rdx
	je	.LBB0_6
	movl	(%rdx), %r8d
	movq	8(%rdx), %rcx
	movq	$0, (%rdx)
	cmpl	$1, %r8d
	jne	.LBB0_6
	movq	%rcx, (%rax)
	movb	$1, 8(%rax)
	jmp	.LBB0_8
.LBB0_6:
	movq	$13, 40(%rsp)
	leaq	40(%rsp), %rcx
	#APP
	#NO_APP
	movq	40(%rsp), %rdx
	movzbl	8(%rax), %ecx
	movq	(%rax), %r8
	movq	%r8, 56(%rsp)
	movq	%rdx, (%rax)
	movb	$1, 8(%rax)
	cmpl	$1, %ecx
	jne	.LBB0_7
	movq	%rax, %rsi
	leaq	56(%rsp), %rcx
	callq	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	jmp	.LBB0_11
.LBB0_7:
	testl	%ecx, %ecx
	jne	.LBB0_9
.LBB0_8:
	leaq	_RINvNtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native4lazy7destroyINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_(%rip), %rdx
	movq	%rax, %rsi
	movq	%rax, %rcx
	callq	_RNvNtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local11destructors4list8register
.LBB0_11:
	movq	%rsi, %rax
.LBB0_12:
	.seh_startepilogue
	addq	$64, %rsp
	popq	%rsi
	.seh_endepilogue
	retq
.LBB0_9:
	movl	$0, 48(%rsp)
	movb	$0, 52(%rsp)
	leaq	alloc_70165e1942fbf2cb7aee6a08556ee215(%rip), %rdx
	leaq	48(%rsp), %rcx
	movl	$87, %r8d
	callq	_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	movq	%rax, 40(%rsp)
	leaq	40(%rsp), %rcx
	callq	_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	movl	$7, %ecx
	#APP

	int	$41

	#NO_APP
	ud2
	.seh_endproc

	.def	_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe,unique,1
	.p2align	4
_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe:
.seh_proc _RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	(%rcx), %rax
	testq	%rax, %rax
	je	.LBB1_4
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB1_4
	testq	%rcx, %rcx
	je	.LBB1_4
	decq	%rax
	leaq	48(%rsp), %rcx
	movq	%rax, 48(%rsp)
	movb	$3, 40(%rsp)
	callq	_RNvXsd_NtNtCs7uUmbfRqPp3_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	nop
.LBB1_4:
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe,unique,2
	.p2align	4
_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe:
.seh_proc _RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	8(%rcx), %rax
	testq	%rax, %rax
	je	.LBB2_4
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB2_4
	testq	%rcx, %rcx
	je	.LBB2_4
	decq	%rax
	leaq	48(%rsp), %rcx
	movq	%rax, 48(%rsp)
	movb	$3, 40(%rsp)
	callq	_RNvXsd_NtNtCs7uUmbfRqPp3_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	nop
.LBB2_4:
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe,unique,3
	.p2align	4
_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe:
.seh_proc _RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	(%rcx), %rax
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB3_3
	testq	%rcx, %rcx
	je	.LBB3_3
	decq	%rax
	leaq	48(%rsp), %rcx
	movq	%rax, 48(%rsp)
	movb	$3, 40(%rsp)
	callq	_RNvXsd_NtNtCs7uUmbfRqPp3_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	nop
.LBB3_3:
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RINvNtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native4lazy7destroyINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native4lazy7destroyINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_,unique,4
	.p2align	4
_RINvNtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native4lazy7destroyINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_:
	movzbl	8(%rcx), %eax
	movb	$2, 8(%rcx)
	cmpb	$1, %al
	je	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	retq

	.def	_RINvNtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native5eager7destroyINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RINvNtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native5eager7destroyINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_,unique,5
	.p2align	4
_RINvNtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native5eager7destroyINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_:
	movb	$2, 8(%rcx)
	jmp	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop

	.def	_RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls,unique,6
	.globl	_RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls
	.p2align	4
_RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls:
	movl	_tls_index(%rip), %eax
	movq	%gs:88, %rcx
	movq	(%rcx,%rax,8), %rax
	leaq	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@SECREL32(%rax), %rax
	retq

	.def	_RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls,unique,7
	.globl	_RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls
	.p2align	4
_RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls:
	movl	_tls_index(%rip), %eax
	movq	%gs:88, %rcx
	movq	(%rcx,%rax,8), %rax
	leaq	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64@SECREL32(%rax), %rax
	retq

	.def	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls,unique,8
	.globl	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls
	.p2align	4
_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls:
	movl	_tls_index(%rip), %eax
	movq	%gs:88, %rcx
	movq	(%rcx,%rax,8), %rax
	leaq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32(%rax), %rax
	retq

	.def	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls,unique,9
	.globl	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls
	.p2align	4
_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls:
	movl	_tls_index(%rip), %eax
	movq	%gs:88, %rcx
	movq	(%rcx,%rax,8), %rax
	leaq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32(%rax), %rax
	retq

	.def	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls,unique,10
	.globl	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls
	.p2align	4
_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls:
	movl	_tls_index(%rip), %eax
	movq	%gs:88, %rcx
	movq	(%rcx,%rax,8), %rax
	leaq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32(%rax), %rax
	retq

	.def	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls,unique,11
	.globl	_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls
	.p2align	4
_RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls:
	movl	_tls_index(%rip), %eax
	movq	%gs:88, %rcx
	movq	(%rcx,%rax,8), %rax
	leaq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32(%rax), %rax
	retq

	.def	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop,unique,12
	.globl	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	.p2align	4
_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop:
.seh_proc _RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs7uUmbfRqPp3_4core3ops4drop4Drop4drop
	pushq	%rax
	.seh_stackalloc 8
	.seh_endprologue
	movq	(%rcx), %rax
	movq	%rax, (%rsp)
	movq	%rsp, %rax
	#APP
	#NO_APP
	.seh_startepilogue
	popq	%rax
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,13
	.p2align	4
_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin0:
.seh_proc _RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.seh_handler __CxxFrameHandler3, @unwind, @except
	pushq	%rbp
	.seh_pushreg %rbp
	pushq	%rsi
	.seh_pushreg %rsi
	subq	$72, %rsp
	.seh_stackalloc 72
	leaq	64(%rsp), %rbp
	.seh_setframe %rbp, 64
	.seh_endprologue
	movq	$-2, (%rbp)
	movq	%rcx, %rsi
	movq	(%rcx), %rcx
	callq	_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	testq	%rax, %rax
	je	.LBB13_7
	movq	8(%rsi), %r8
	testq	%r8, %r8
	je	.LBB13_6
	movq	%rax, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movl	%r8d, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB13_5
	testq	%rcx, %rcx
	je	.LBB13_5
	decq	%r8
	leaq	-24(%rbp), %rcx
	movq	%r8, -24(%rbp)
	movb	$3, -32(%rbp)
.Ltmp0:
	callq	_RNvXsd_NtNtCs7uUmbfRqPp3_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	nop
.Ltmp1:
.LBB13_5:
	movq	-16(%rbp), %rsi
	movq	-8(%rbp), %rax
.LBB13_6:
	movq	%rax, 8(%rsi)
.LBB13_7:
	testq	%rax, %rax
	setne	%al
	.seh_startepilogue
	addq	$72, %rsp
	popq	%rsi
	popq	%rbp
	.seh_endepilogue
	retq
	.seh_handlerdata
	.long	$cppxdata$_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@IMGREL
	.section	.text,"xr",one_only,_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,13
	.seh_endproc
	.def	"?dtor$8@?0?_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$8@?0?_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA":
.seh_proc "?dtor$8@?0?_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA"
.LBB13_8:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	pushq	%rsi
	.seh_pushreg %rsi
	subq	$40, %rsp
	.seh_stackalloc 40
	leaq	64(%rdx), %rbp
	.seh_endprologue
	movq	-16(%rbp), %rax
	movq	-8(%rbp), %rcx
	movq	%rcx, 8(%rax)
	.seh_startepilogue
	addq	$40, %rsp
	popq	%rsi
	popq	%rbp
	.seh_endepilogue
	retq
.Lfunc_end0:
	.seh_handlerdata
	.section	.text,"xr",one_only,_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,13
	.seh_endproc
	.section	.xdata,"dr",associative,_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,0
	.p2align	2, 0x0
$cppxdata$_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@IMGREL
	.long	0
	.long	0
	.long	3
	.long	$ip2state$_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@IMGREL
	.long	64
	.long	0
	.long	1
$stateUnwindMap$_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
	.long	-1
	.long	"?dtor$8@?0?_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA"@IMGREL
$ip2state$_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
	.long	.Lfunc_begin0@IMGREL
	.long	-1
	.long	.Ltmp0@IMGREL
	.long	0
	.long	.Ltmp1@IMGREL
	.long	-1
	.section	.text,"xr",one_only,_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,13

	.def	_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,14
	.p2align	4
_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin1:
.seh_proc _RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.seh_handler __CxxFrameHandler3, @unwind, @except
	pushq	%rbp
	.seh_pushreg %rbp
	pushq	%rsi
	.seh_pushreg %rsi
	subq	$88, %rsp
	.seh_stackalloc 88
	leaq	80(%rsp), %rbp
	.seh_setframe %rbp, 80
	.seh_endprologue
	movq	$-2, (%rbp)
	movq	%rcx, %rsi
	movl	$0, -4(%rbp)
	cmpl	$128, %edx
	jae	.LBB14_1
	movb	%dl, -4(%rbp)
	movl	$1, %r8d
	jmp	.LBB14_6
.LBB14_1:
	movl	%edx, %eax
	andb	$63, %al
	orb	$-128, %al
	movl	%edx, %ecx
	shrl	$6, %ecx
	cmpl	$2048, %edx
	jae	.LBB14_3
	orb	$-64, %cl
	movb	%cl, -4(%rbp)
	movb	%al, -3(%rbp)
	movl	$2, %r8d
	jmp	.LBB14_6
.LBB14_3:
	andb	$63, %cl
	orb	$-128, %cl
	movl	%edx, %r8d
	shrl	$12, %r8d
	cmpl	$65535, %edx
	ja	.LBB14_5
	orb	$-32, %r8b
	movb	%r8b, -4(%rbp)
	movb	%cl, -3(%rbp)
	movb	%al, -2(%rbp)
	movl	$3, %r8d
	jmp	.LBB14_6
.LBB14_5:
	andb	$63, %r8b
	orb	$-128, %r8b
	shrl	$18, %edx
	orb	$-16, %dl
	movb	%dl, -4(%rbp)
	movb	%r8b, -3(%rbp)
	movb	%cl, -2(%rbp)
	movb	%al, -1(%rbp)
	movl	$4, %r8d
.LBB14_6:
	movq	(%rsi), %rcx
	leaq	-4(%rbp), %rdx
	callq	_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	testq	%rax, %rax
	je	.LBB14_13
	movq	8(%rsi), %r8
	testq	%r8, %r8
	je	.LBB14_12
	movq	%rax, -16(%rbp)
	movq	%rsi, -24(%rbp)
	movl	%r8d, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB14_11
	testq	%rcx, %rcx
	je	.LBB14_11
	decq	%r8
	leaq	-32(%rbp), %rcx
	movq	%r8, -32(%rbp)
	movb	$3, -40(%rbp)
.Ltmp2:
	callq	_RNvXsd_NtNtCs7uUmbfRqPp3_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	nop
.Ltmp3:
.LBB14_11:
	movq	-24(%rbp), %rsi
	movq	-16(%rbp), %rax
.LBB14_12:
	movq	%rax, 8(%rsi)
.LBB14_13:
	testq	%rax, %rax
	setne	%al
	.seh_startepilogue
	addq	$88, %rsp
	popq	%rsi
	popq	%rbp
	.seh_endepilogue
	retq
	.seh_handlerdata
	.long	$cppxdata$_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@IMGREL
	.section	.text,"xr",one_only,_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,14
	.seh_endproc
	.def	"?dtor$15@?0?_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$15@?0?_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA":
.seh_proc "?dtor$15@?0?_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA"
.LBB14_15:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	pushq	%rsi
	.seh_pushreg %rsi
	subq	$40, %rsp
	.seh_stackalloc 40
	leaq	80(%rdx), %rbp
	.seh_endprologue
	movq	-24(%rbp), %rax
	movq	-16(%rbp), %rcx
	movq	%rcx, 8(%rax)
	.seh_startepilogue
	addq	$40, %rsp
	popq	%rsi
	popq	%rbp
	.seh_endepilogue
	retq
.Lfunc_end1:
	.seh_handlerdata
	.section	.text,"xr",one_only,_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,14
	.seh_endproc
	.section	.xdata,"dr",associative,_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,1
	.p2align	2, 0x0
$cppxdata$_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@IMGREL
	.long	0
	.long	0
	.long	3
	.long	$ip2state$_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@IMGREL
	.long	80
	.long	0
	.long	1
$stateUnwindMap$_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
	.long	-1
	.long	"?dtor$15@?0?_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA"@IMGREL
$ip2state$_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
	.long	.Lfunc_begin1@IMGREL
	.long	-1
	.long	.Ltmp2@IMGREL
	.long	0
	.long	.Ltmp3@IMGREL
	.long	-1
	.section	.text,"xr",one_only,_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,14

	.def	_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,15
	.p2align	4
_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	movq	%r8, %r9
	movq	%rdx, %r8
	leaq	vtable.0(%rip), %rdx
	jmp	_RNvNtCs7uUmbfRqPp3_4core3fmt5write

	.def	_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,16
	.p2align	4
_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin2:
.seh_proc _RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	.seh_handler __CxxFrameHandler3, @unwind, @except
	pushq	%rbp
	.seh_pushreg %rbp
	pushq	%r15
	.seh_pushreg %r15
	pushq	%r14
	.seh_pushreg %r14
	pushq	%r13
	.seh_pushreg %r13
	pushq	%r12
	.seh_pushreg %r12
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	pushq	%rbx
	.seh_pushreg %rbx
	subq	$88, %rsp
	.seh_stackalloc 88
	leaq	80(%rsp), %rbp
	.seh_setframe %rbp, 80
	.seh_endprologue
	movq	$-2, (%rbp)
	movq	%r8, %rsi
	movq	%rdx, %rdi
	movq	%rcx, %rbx
	leaq	-32(%rbp), %r14
	leaq	.LJTI16_0(%rip), %r12
	movl	$255, %r13d
	jmp	.LBB16_1
.LBB16_11:
	movq	%r15, %rax
	shrq	$32, %rax
	movq	%r15, %rcx
	shrq	$34, %rcx
	cmpl	$11, %ecx
	cmovael	%r13d, %eax
	cmpb	$35, %al
	jne	.LBB16_3
	.p2align	4
.LBB16_1:
	testq	%rsi, %rsi
	je	.LBB16_2
	movq	%rbx, %rcx
	movq	%rdi, %rdx
	movq	%rsi, %r8
	callq	_RNvXs5_NtNtNtCscx1ptWZUqVR_3std3sys5stdio7windowsNtB5_6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write5write
	movq	%rdx, %r15
	movq	%rax, -24(%rbp)
	movq	%rdx, -16(%rbp)
	cmpq	$1, %rax
	movq	%rax, -8(%rbp)
	jne	.LBB16_9
	movl	%r15d, %eax
	andl	$3, %eax
	movslq	(%r12,%rax,4), %rax
	addq	%r12, %rax
	jmpq	*%rax
.LBB16_16:
	cmpb	$35, 16(%r15)
	je	.LBB16_1
	jmp	.LBB16_3
	.p2align	4
.LBB16_9:
	testq	%r15, %r15
	je	.LBB16_10
	movq	%rsi, %rax
	subq	%r15, %rax
	jb	.LBB16_14
	addq	%r15, %rdi
	movq	%rax, %rsi
	jmp	.LBB16_1
.LBB16_6:
.Ltmp6:
	callq	_RNvNtNtNtCs7uUmbfRqPp3_4core2io5error12os_functions16get_os_functions
	nop
.Ltmp7:
	movq	%r15, %rcx
	shrq	$32, %rcx
.Ltmp8:
	callq	*16(%rax)
	nop
.Ltmp9:
	testb	%al, %al
	jne	.LBB16_1
	jmp	.LBB16_3
.LBB16_17:
	cmpb	$35, 31(%r15)
	jne	.LBB16_3
	decq	%r15
	movq	%r15, -32(%rbp)
	movb	$3, -40(%rbp)
	movq	%r14, %rcx
	callq	_RNvXsd_NtNtCs7uUmbfRqPp3_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	jmp	.LBB16_1
.LBB16_2:
	xorl	%r15d, %r15d
	jmp	.LBB16_3
.LBB16_10:
	leaq	alloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2(%rip), %r15
.LBB16_3:
	movq	%r15, %rax
	.seh_startepilogue
	addq	$88, %rsp
	popq	%rbx
	popq	%rdi
	popq	%rsi
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.seh_endepilogue
	retq
.LBB16_14:
.Ltmp4:
	leaq	alloc_ba1bfa9f01512a2cbee7a129faa5ce35(%rip), %r9
	movq	%r15, %rcx
	movq	%rsi, %rdx
	movq	%rsi, %r8
	callq	_RNvNtNtCs7uUmbfRqPp3_4core5slice5index16slice_index_fail
	nop
.Ltmp5:
	ud2
	.seh_handlerdata
	.long	$cppxdata$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@IMGREL
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,16
	.seh_endproc
	.def	"?dtor$19@?0?_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$19@?0?_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA":
.seh_proc "?dtor$19@?0?_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA"
.LBB16_19:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	pushq	%r15
	.seh_pushreg %r15
	pushq	%r14
	.seh_pushreg %r14
	pushq	%r13
	.seh_pushreg %r13
	pushq	%r12
	.seh_pushreg %r12
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	pushq	%rbx
	.seh_pushreg %rbx
	subq	$40, %rsp
	.seh_stackalloc 40
	leaq	80(%rdx), %rbp
	.seh_endprologue
	testb	$1, -8(%rbp)
	jne	.LBB16_20
.LBB16_21:
	.seh_startepilogue
	addq	$40, %rsp
	popq	%rbx
	popq	%rdi
	popq	%rsi
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	.seh_endepilogue
	retq
.LBB16_20:
	leaq	-16(%rbp), %rcx
	callq	_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
	jmp	.LBB16_21
.Lfunc_end2:
	.section	.rdata,"dr",associative,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,17
	.p2align	2, 0x0
.LJTI16_0:
	.long	.LBB16_16-.LJTI16_0
	.long	.LBB16_17-.LJTI16_0
	.long	.LBB16_6-.LJTI16_0
	.long	.LBB16_11-.LJTI16_0
	.seh_handlerdata
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,16
	.seh_endproc
	.section	.xdata,"dr",associative,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,2
	.p2align	2, 0x0
$cppxdata$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@IMGREL
	.long	0
	.long	0
	.long	5
	.long	$ip2state$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@IMGREL
	.long	80
	.long	0
	.long	1
$stateUnwindMap$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
	.long	-1
	.long	"?dtor$19@?0?_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA"@IMGREL
$ip2state$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
	.long	.Lfunc_begin2@IMGREL
	.long	-1
	.long	.Ltmp6@IMGREL
	.long	0
	.long	.Ltmp9@IMGREL
	.long	-1
	.long	.Ltmp4@IMGREL
	.long	0
	.long	.Ltmp5@IMGREL
	.long	-1
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,16

	.def	_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,18
	.p2align	4
_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin3:
.seh_proc _RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.seh_handler __CxxFrameHandler3, @unwind, @except
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$80, %rsp
	.seh_stackalloc 80
	leaq	80(%rsp), %rbp
	.seh_setframe %rbp, 80
	.seh_endprologue
	movq	$-2, -8(%rbp)
	movq	%r8, %r9
	movq	%rdx, %r8
	movq	%rcx, -24(%rbp)
	movq	$0, -16(%rbp)
.Ltmp10:
	leaq	vtable.0(%rip), %rdx
	leaq	-24(%rbp), %rcx
	callq	_RNvNtCs7uUmbfRqPp3_4core3fmt5write
	nop
.Ltmp11:
	testb	%al, %al
	je	.LBB17_5
	movq	-16(%rbp), %rax
	testq	%rax, %rax
	jne	.LBB17_10
.Ltmp12:
	leaq	alloc_a439077caaee6bab9af745f1531d72a4(%rip), %rcx
	leaq	alloc_1a670b50d276900533e9b5ea016aeb83(%rip), %r8
	movl	$173, %edx
	callq	_RNvNtCs7uUmbfRqPp3_4core9panicking9panic_fmt
	nop
.Ltmp13:
	ud2
.LBB17_5:
	movq	-16(%rbp), %rax
	testq	%rax, %rax
	je	.LBB17_9
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB17_9
	testq	%rcx, %rcx
	je	.LBB17_9
	decq	%rax
	leaq	-32(%rbp), %rcx
	movq	%rax, -32(%rbp)
	movb	$3, -40(%rbp)
	callq	_RNvXsd_NtNtCs7uUmbfRqPp3_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.LBB17_9:
	xorl	%eax, %eax
.LBB17_10:
	.seh_startepilogue
	addq	$80, %rsp
	popq	%rbp
	.seh_endepilogue
	retq
	.seh_handlerdata
	.long	$cppxdata$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@IMGREL
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,18
	.seh_endproc
	.def	"?dtor$11@?0?_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$11@?0?_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA":
.seh_proc "?dtor$11@?0?_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA"
.LBB17_11:
	movq	%rdx, 16(%rsp)
	pushq	%rbp
	.seh_pushreg %rbp
	subq	$32, %rsp
	.seh_stackalloc 32
	leaq	80(%rdx), %rbp
	.seh_endprologue
	leaq	-24(%rbp), %rcx
	callq	_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe
	nop
	.seh_startepilogue
	addq	$32, %rsp
	popq	%rbp
	.seh_endepilogue
	retq
.Lfunc_end3:
	.seh_handlerdata
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,18
	.seh_endproc
	.section	.xdata,"dr",associative,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,3
	.p2align	2, 0x0
$cppxdata$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@IMGREL
	.long	0
	.long	0
	.long	3
	.long	$ip2state$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@IMGREL
	.long	72
	.long	0
	.long	1
$stateUnwindMap$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.long	-1
	.long	"?dtor$11@?0?_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA"@IMGREL
$ip2state$_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.long	.Lfunc_begin3@IMGREL
	.long	-1
	.long	.Ltmp10@IMGREL
	.long	0
	.long	.Ltmp13@IMGREL
	.long	-1
	.section	.text,"xr",one_only,_RNvYNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrNtNtNtCs7uUmbfRqPp3_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,18

	.def	access_all_tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,access_all_tls,unique,19
	.globl	access_all_tls
	.p2align	4
access_all_tls:
.seh_proc access_all_tls
	pushq	%r15
	.seh_pushreg %r15
	pushq	%r14
	.seh_pushreg %r14
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	pushq	%rbx
	.seh_pushreg %rbx
	subq	$48, %rsp
	.seh_stackalloc 48
	.seh_endprologue
	movl	_tls_index(%rip), %eax
	movq	%gs:88, %rcx
	movq	(%rcx,%rax,8), %rcx
	movq	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@SECREL32(%rcx), %rdi
	incq	%rdi
	movq	%rdi, _RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@SECREL32(%rcx)
	movq	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64@SECREL32(%rcx), %rbx
	movq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32(%rcx), %rax
	leaq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32(%rcx), %rsi
	movzbl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32+8(%rcx), %ecx
	testl	%ecx, %ecx
	jne	.LBB18_1
.LBB18_3:
	movq	(%rsi), %rsi
	movl	_tls_index(%rip), %ecx
	movq	%gs:88, %rdx
	movq	(%rdx,%rcx,8), %rdx
	leaq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32(%rdx), %rcx
	cmpb	$1, _RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32+8(%rdx)
	jne	.LBB18_5
	movq	(%rcx), %r14
.LBB18_6:
	movl	_tls_index(%rip), %ecx
	movq	%gs:88, %rdx
	movq	(%rdx,%rcx,8), %rdx
	leaq	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32(%rdx), %rcx
	cmpb	$1, _RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32+8(%rdx)
	jne	.LBB18_7
.LBB18_9:
	addq	%rdi, %rbx
	addq	%rsi, %rax
	addq	%rbx, %rax
	addq	%r14, %rax
	addq	(%rcx), %rax
	.seh_startepilogue
	addq	$48, %rsp
	popq	%rbx
	popq	%rdi
	popq	%rsi
	popq	%r14
	popq	%r15
	.seh_endepilogue
	retq
.LBB18_5:
	movq	$7, 40(%rsp)
	leaq	40(%rsp), %rdx
	#APP
	#NO_APP
	movq	40(%rsp), %r14
	movq	%r14, (%rcx)
	movb	$1, 8(%rcx)
	jmp	.LBB18_6
.LBB18_7:
	xorl	%edx, %edx
	movq	%rax, %r15
	callq	_RINvMs0_NtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	movq	%rax, %rcx
	movq	%r15, %rax
	testq	%rcx, %rcx
	jne	.LBB18_9
	jmp	.LBB18_8
.LBB18_1:
	cmpl	$1, %ecx
	jne	.LBB18_8
	leaq	_RINvNtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local6native5eager7destroyINtNtCs7uUmbfRqPp3_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_(%rip), %rdx
	movq	%rsi, %rcx
	movq	%rax, %r14
	callq	_RNvNtNtNtNtCscx1ptWZUqVR_3std3sys12thread_local11destructors4list8register
	movq	%r14, %rax
	movb	$0, 8(%rsi)
	jmp	.LBB18_3
.LBB18_8:
	leaq	alloc_d967d5ae25e575721be85468d37a1295(%rip), %rcx
	callq	_RNvNtNtCscx1ptWZUqVR_3std6thread5local18panic_access_error
	ud2
	.seh_endproc

	.section	.rdata,"dr",one_only,alloc_70165e1942fbf2cb7aee6a08556ee215,unique,20
alloc_70165e1942fbf2cb7aee6a08556ee215:
	.ascii	"fatal runtime error: unreachable, aborting\n"

	.section	.rdata,"dr",one_only,alloc_5b02399d15196f4565c9574d7e606137,unique,21
alloc_5b02399d15196f4565c9574d7e606137:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library\\std\\src\\thread\\local.rs"

	.section	.rdata,"dr",one_only,alloc_d967d5ae25e575721be85468d37a1295,unique,22
	.p2align	3, 0x0
alloc_d967d5ae25e575721be85468d37a1295:
	.quad	alloc_5b02399d15196f4565c9574d7e606137
	.asciz	"\205\000\000\000\000\000\000\000\255\001\000\000\031\000\000"

	.section	.rdata,"dr",one_only,vtable.0,unique,23
	.p2align	3, 0x0
vtable.0:
	.quad	_RINvNtCs7uUmbfRqPp3_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe
	.asciz	"\020\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	_RNvXNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.quad	_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.quad	_RNvYINtNvNtNtCs7uUmbfRqPp3_4core2io5write17default_write_fmt7AdapterNtNtNtNtCscx1ptWZUqVR_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe

	.section	.rdata,"dr",one_only,alloc_a439077caaee6bab9af745f1531d72a4,unique,24
alloc_a439077caaee6bab9af745f1531d72a4:
	.ascii	"a formatting trait implementation returned an error when the underlying stream did not"

	.section	.rdata,"dr",one_only,alloc_686723c4fc0450ab61097742d7654dd3,unique,25
alloc_686723c4fc0450ab61097742d7654dd3:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library\\core\\src\\io\\write.rs"

	.section	.rdata,"dr",one_only,alloc_1a670b50d276900533e9b5ea016aeb83,unique,26
	.p2align	3, 0x0
alloc_1a670b50d276900533e9b5ea016aeb83:
	.quad	alloc_686723c4fc0450ab61097742d7654dd3
	.asciz	"\202\000\000\000\000\000\000\000\233\001\000\000\021\000\000"

	.section	.tls$,"dw",one_only,_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,unique,27
	.globl	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	.p2align	3, 0x0
_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64:
	.ascii	"\210wfUD3\"\021"

	.section	.tls$,"dw",one_only,_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64,unique,28
	.globl	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	.p2align	6, 0x0
_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64:
	.asciz	"\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000"

	.section	.tls$,"dw",one_only,_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL,unique,29
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL:
	.ascii	"c\000\000\000\000\000\000\000\001"
	.zero	7

	.section	.tls$,"dw",one_only,_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,30
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	7

	.section	.tls$,"dw",one_only,_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,31
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.asciz	"*\000\000\000\000\000\000"

	.section	.tls$,"dw",one_only,_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,unique,32
	.globl	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	7

	.section	.rdata,"dr",one_only,alloc_8d68fcbc011419193bd208f22e2789d1,unique,33
alloc_8d68fcbc011419193bd208f22e2789d1:
	.ascii	"failed to write whole buffer"

	.section	.rdata,"dr",one_only,alloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2,unique,34
	.p2align	3, 0x0
alloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2:
	.quad	alloc_8d68fcbc011419193bd208f22e2789d1
	.ascii	"\034\000\000\000\000\000\000\000\027"
	.zero	7

	.section	.rdata,"dr",one_only,alloc_ba1bfa9f01512a2cbee7a129faa5ce35,unique,35
	.p2align	3, 0x0
alloc_ba1bfa9f01512a2cbee7a129faa5ce35:
	.quad	alloc_686723c4fc0450ab61097742d7654dd3
	.asciz	"\202\000\000\000\000\000\000\000\334\000\000\000$\000\000"

	.section	.data,"dw",one_only,__imp__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,unique,36
	.globl	__imp__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	.p2align	3, 0x0
__imp__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64:
	.quad	_RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64

	.section	.data,"dw",one_only,__imp__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64,unique,37
	.globl	__imp__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	.p2align	3, 0x0
__imp__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64:
	.quad	_RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64

	.section	.data,"dw",one_only,__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL,unique,38
	.globl	__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL:
	.quad	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL

	.section	.data,"dw",one_only,__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,39
	.globl	__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.quad	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL

	.section	.data,"dw",one_only,__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,40
	.globl	__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.quad	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL

	.section	.data,"dw",one_only,__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,unique,41
	.globl	__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL:
	.quad	_RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL

