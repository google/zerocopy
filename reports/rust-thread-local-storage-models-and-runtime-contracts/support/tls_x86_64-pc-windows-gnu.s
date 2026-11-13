	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 0
	.att_syntax
	.file	"tls_probe.d6bd21401e7e8eac-cgu.0"
	.def	_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_E14try_initializeNvNvB1D_10CONST_DROP27___rust_std_internal_init_fnEB1D_;
	.scl	3;
	.type	32;
	.endef
	.text
	.p2align	4
_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_E14try_initializeNvNvB1D_10CONST_DROP27___rust_std_internal_init_fnEB1D_:
.Lfunc_begin0:
.seh_proc _RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_E14try_initializeNvNvB1D_10CONST_DROP27___rust_std_internal_init_fnEB1D_
	.seh_handler rust_eh_personality, @unwind, @except
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	pushq	%rbx
	.seh_pushreg %rbx
	subq	$64, %rsp
	.seh_stackalloc 64
	.seh_endprologue
	cmpq	$1, %rdx
	je	.LBB0_1
	movl	%ecx, %edi
	testq	%r8, %r8
	je	.LBB0_5
	movq	8(%r8), %rbx
	cmpb	$0, (%r8)
	movq	$0, (%r8)
	jne	.LBB0_6
.LBB0_5:
	movl	$99, %ebx
.LBB0_6:
	movq	%rbx, 48(%rsp)
	movl	%edi, 56(%rsp)
.Ltmp0:
	movl	$8, %ecx
	movl	$16, %edx
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows5alloc
.Ltmp1:
	movq	%rax, %rsi
	testq	%rax, %rax
	je	.LBB0_8
	movq	%rbx, (%rsi)
	movl	%edi, 8(%rsi)
	movl	%edi, %ecx
	callq	TlsGetValue
	movq	%rax, %rbx
	movl	%edi, %ecx
	movq	%rsi, %rdx
	callq	TlsSetValue
	cmpl	$1, %eax
	jne	.LBB0_15
	testq	%rbx, %rbx
	je	.LBB0_2
	movq	%rbx, %rcx
	callq	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows16get_process_heap
	movq	%rax, %rcx
	xorl	%edx, %edx
	movq	%rbx, %r8
	callq	HeapFree
	jmp	.LBB0_2
.LBB0_1:
	xorl	%esi, %esi
.LBB0_2:
	movq	%rsi, %rax
	.seh_startepilogue
	addq	$64, %rsp
	popq	%rbx
	popq	%rdi
	popq	%rsi
	.seh_endepilogue
	retq
.LBB0_15:
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windows4fail
	ud2
.LBB0_8:
	movl	$0, 32(%rsp)
	movb	$0, 36(%rsp)
.Ltmp2:
	leaq	.Lalloc_0407a3e59c8988b5606db2776e0ad4d5(%rip), %rdx
	leaq	32(%rsp), %rcx
	movl	$50, %r8d
	callq	_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
.Ltmp3:
	movq	%rax, 40(%rsp)
.Ltmp4:
	leaq	40(%rsp), %rcx
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
.Ltmp5:
	movl	$7, %ecx
	#APP

	int	$41

	#NO_APP
	ud2
.LBB0_11:
.Ltmp6:
	movq	%rax, %rsi
	leaq	48(%rsp), %rcx
	callq	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	movq	%rsi, %rcx
	callq	_Unwind_Resume
	ud2
.Lfunc_end0:
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table0:
.Lexception0:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end0-.Lcst_begin0
.Lcst_begin0:
	.uleb128 .Ltmp0-.Lfunc_begin0
	.uleb128 .Ltmp1-.Ltmp0
	.uleb128 .Ltmp6-.Lfunc_begin0
	.byte	0
	.uleb128 .Ltmp1-.Lfunc_begin0
	.uleb128 .Ltmp2-.Ltmp1
	.byte	0
	.byte	0
	.uleb128 .Ltmp2-.Lfunc_begin0
	.uleb128 .Ltmp5-.Ltmp2
	.uleb128 .Ltmp6-.Lfunc_begin0
	.byte	0
	.uleb128 .Ltmp5-.Lfunc_begin0
	.uleb128 .Lfunc_end0-.Ltmp5
	.byte	0
	.byte	0
.Lcst_end0:
	.p2align	2, 0x0
	.text

	.def	_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_E14try_initializeNvNvB1D_9LAZY_DROP27___rust_std_internal_init_fnEB1D_;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_E14try_initializeNvNvB1D_9LAZY_DROP27___rust_std_internal_init_fnEB1D_:
.Lfunc_begin1:
.seh_proc _RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_E14try_initializeNvNvB1D_9LAZY_DROP27___rust_std_internal_init_fnEB1D_
	.seh_handler rust_eh_personality, @unwind, @except
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	pushq	%rbx
	.seh_pushreg %rbx
	subq	$64, %rsp
	.seh_stackalloc 64
	.seh_endprologue
	cmpq	$1, %rdx
	je	.LBB1_1
	movl	%ecx, %edi
	testq	%r8, %r8
	je	.LBB1_5
	movq	8(%r8), %rbx
	cmpb	$0, (%r8)
	movq	$0, (%r8)
	jne	.LBB1_6
.LBB1_5:
	movq	$13, 40(%rsp)
	leaq	40(%rsp), %rax
	#APP
	#NO_APP
	movq	40(%rsp), %rbx
.LBB1_6:
	movq	%rbx, 40(%rsp)
	movl	%edi, 48(%rsp)
.Ltmp7:
	movl	$8, %ecx
	movl	$16, %edx
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows5alloc
.Ltmp8:
	movq	%rax, %rsi
	testq	%rax, %rax
	je	.LBB1_8
	movq	%rbx, (%rsi)
	movl	%edi, 8(%rsi)
	movl	%edi, %ecx
	callq	TlsGetValue
	movq	%rax, %rbx
	movl	%edi, %ecx
	movq	%rsi, %rdx
	callq	TlsSetValue
	cmpl	$1, %eax
	jne	.LBB1_15
	testq	%rbx, %rbx
	je	.LBB1_2
	movq	%rbx, %rcx
	callq	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows16get_process_heap
	movq	%rax, %rcx
	xorl	%edx, %edx
	movq	%rbx, %r8
	callq	HeapFree
	jmp	.LBB1_2
.LBB1_1:
	xorl	%esi, %esi
.LBB1_2:
	movq	%rsi, %rax
	.seh_startepilogue
	addq	$64, %rsp
	popq	%rbx
	popq	%rdi
	popq	%rsi
	.seh_endepilogue
	retq
.LBB1_15:
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windows4fail
	ud2
.LBB1_8:
	movl	$0, 32(%rsp)
	movb	$0, 36(%rsp)
.Ltmp9:
	leaq	.Lalloc_0407a3e59c8988b5606db2776e0ad4d5(%rip), %rdx
	leaq	32(%rsp), %rcx
	movl	$50, %r8d
	callq	_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
.Ltmp10:
	movq	%rax, 56(%rsp)
.Ltmp11:
	leaq	56(%rsp), %rcx
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
.Ltmp12:
	movl	$7, %ecx
	#APP

	int	$41

	#NO_APP
	ud2
.LBB1_11:
.Ltmp13:
	movq	%rax, %rsi
	leaq	40(%rsp), %rcx
	callq	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	movq	%rsi, %rcx
	callq	_Unwind_Resume
	ud2
.Lfunc_end1:
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table1:
.Lexception1:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end1-.Lcst_begin1
.Lcst_begin1:
	.uleb128 .Ltmp7-.Lfunc_begin1
	.uleb128 .Ltmp8-.Ltmp7
	.uleb128 .Ltmp13-.Lfunc_begin1
	.byte	0
	.uleb128 .Ltmp8-.Lfunc_begin1
	.uleb128 .Ltmp9-.Ltmp8
	.byte	0
	.byte	0
	.uleb128 .Ltmp9-.Lfunc_begin1
	.uleb128 .Ltmp12-.Ltmp9
	.uleb128 .Ltmp13-.Lfunc_begin1
	.byte	0
	.uleb128 .Ltmp12-.Lfunc_begin1
	.uleb128 .Lfunc_end1-.Ltmp12
	.byte	0
	.byte	0
.Lcst_end1:
	.p2align	2, 0x0
	.text

	.def	_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_E14try_initializeNvNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP27___rust_std_internal_init_fnEB22_;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_E14try_initializeNvNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP27___rust_std_internal_init_fnEB22_:
.seh_proc _RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_E14try_initializeNvNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP27___rust_std_internal_init_fnEB22_
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	pushq	%rbx
	.seh_pushreg %rbx
	subq	$48, %rsp
	.seh_stackalloc 48
	.seh_endprologue
	cmpq	$1, %rdx
	je	.LBB2_1
	movl	%ecx, %edi
	testq	%r8, %r8
	je	.LBB2_5
	movq	8(%r8), %rbx
	cmpb	$0, (%r8)
	movq	$0, (%r8)
	jne	.LBB2_6
.LBB2_5:
	movq	$7, 32(%rsp)
	leaq	32(%rsp), %rax
	#APP
	#NO_APP
	movq	32(%rsp), %rbx
.LBB2_6:
	movl	$8, %ecx
	movl	$16, %edx
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows5alloc
	testq	%rax, %rax
	je	.LBB2_10
	movq	%rax, %rsi
	movq	%rbx, (%rax)
	movl	%edi, 8(%rax)
	movl	%edi, %ecx
	callq	TlsGetValue
	movq	%rax, %rbx
	movl	%edi, %ecx
	movq	%rsi, %rdx
	callq	TlsSetValue
	cmpl	$1, %eax
	jne	.LBB2_11
	testq	%rbx, %rbx
	je	.LBB2_2
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows16get_process_heap
	movq	%rax, %rcx
	xorl	%edx, %edx
	movq	%rbx, %r8
	callq	HeapFree
	jmp	.LBB2_2
.LBB2_1:
	xorl	%esi, %esi
.LBB2_2:
	movq	%rsi, %rax
	.seh_startepilogue
	addq	$48, %rsp
	popq	%rbx
	popq	%rdi
	popq	%rsi
	.seh_endepilogue
	retq
.LBB2_11:
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windows4fail
	ud2
.LBB2_10:
	movl	$0, 40(%rsp)
	movb	$0, 44(%rsp)
	leaq	.Lalloc_0407a3e59c8988b5606db2776e0ad4d5(%rip), %rdx
	leaq	40(%rsp), %rcx
	movl	$101, %r8d
	callq	_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	movq	%rax, 32(%rsp)
	leaq	32(%rsp), %rcx
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	movl	$7, %ecx
	#APP

	int	$41

	#NO_APP
	ud2
	.seh_endproc

	.def	_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_E14try_initializeNvNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP27___rust_std_internal_init_fnEB22_;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_E14try_initializeNvNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP27___rust_std_internal_init_fnEB22_:
.seh_proc _RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_E14try_initializeNvNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP27___rust_std_internal_init_fnEB22_
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	pushq	%rbx
	.seh_pushreg %rbx
	subq	$48, %rsp
	.seh_stackalloc 48
	.seh_endprologue
	cmpq	$1, %rdx
	je	.LBB3_1
	movl	%ecx, %edi
	testq	%r8, %r8
	je	.LBB3_5
	movq	8(%r8), %rbx
	cmpb	$0, (%r8)
	movq	$0, (%r8)
	jne	.LBB3_6
.LBB3_5:
	movl	$42, %ebx
.LBB3_6:
	movl	$8, %ecx
	movl	$16, %edx
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows5alloc
	testq	%rax, %rax
	je	.LBB3_10
	movq	%rax, %rsi
	movq	%rbx, (%rax)
	movl	%edi, 8(%rax)
	movl	%edi, %ecx
	callq	TlsGetValue
	movq	%rax, %rbx
	movl	%edi, %ecx
	movq	%rsi, %rdx
	callq	TlsSetValue
	cmpl	$1, %eax
	jne	.LBB3_11
	testq	%rbx, %rbx
	je	.LBB3_2
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows16get_process_heap
	movq	%rax, %rcx
	xorl	%edx, %edx
	movq	%rbx, %r8
	callq	HeapFree
	jmp	.LBB3_2
.LBB3_1:
	xorl	%esi, %esi
.LBB3_2:
	movq	%rsi, %rax
	.seh_startepilogue
	addq	$48, %rsp
	popq	%rbx
	popq	%rdi
	popq	%rsi
	.seh_endepilogue
	retq
.LBB3_11:
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windows4fail
	ud2
.LBB3_10:
	movl	$0, 32(%rsp)
	movb	$0, 36(%rsp)
	leaq	.Lalloc_0407a3e59c8988b5606db2776e0ad4d5(%rip), %rdx
	leaq	32(%rsp), %rcx
	movl	$101, %r8d
	callq	_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	movq	%rax, 40(%rsp)
	leaq	40(%rsp), %rcx
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	movl	$7, %ecx
	#APP

	int	$41

	#NO_APP
	ud2
	.seh_endproc

	.def	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe:
.seh_proc _RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	(%rcx), %rax
	testq	%rax, %rax
	je	.LBB4_4
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB4_4
	testq	%rcx, %rcx
	je	.LBB4_4
	decq	%rax
	leaq	48(%rsp), %rcx
	movq	%rax, 48(%rsp)
	movb	$3, 40(%rsp)
	callq	_RNvXsd_NtNtCs2Ja4erDm0Jl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	nop
.LBB4_4:
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os16AlignedSystemBoxINtNtB4_4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_EEB1Z_;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os16AlignedSystemBoxINtNtB4_4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_EEB1Z_:
.seh_proc _RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os16AlignedSystemBoxINtNtB4_4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_EEB1Z_
	pushq	%rsi
	.seh_pushreg %rsi
	subq	$32, %rsp
	.seh_stackalloc 32
	.seh_endprologue
	movq	(%rcx), %rsi
	movq	%rsi, %rcx
	callq	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows16get_process_heap
	movq	%rax, %rcx
	xorl	%edx, %edx
	movq	%rsi, %r8
	.seh_startepilogue
	addq	$32, %rsp
	popq	%rsi
	.seh_endepilogue
	jmp	HeapFree
	.seh_endproc

	.def	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe:
.seh_proc _RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	8(%rcx), %rax
	testq	%rax, %rax
	je	.LBB6_4
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB6_4
	testq	%rcx, %rcx
	je	.LBB6_4
	decq	%rax
	leaq	48(%rsp), %rcx
	movq	%rax, 48(%rsp)
	movb	$3, 40(%rsp)
	callq	_RNvXsd_NtNtCs2Ja4erDm0Jl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	nop
.LBB6_4:
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe:
.seh_proc _RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	(%rcx), %rax
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB7_3
	testq	%rcx, %rcx
	je	.LBB7_3
	decq	%rax
	leaq	48(%rsp), %rcx
	movq	%rax, 48(%rsp)
	movb	$3, 40(%rsp)
	callq	_RNvXsd_NtNtCs2Ja4erDm0Jl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	nop
.LBB7_3:
	.seh_startepilogue
	addq	$56, %rsp
	.seh_endepilogue
	retq
	.seh_endproc

	.def	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtNvNtNtCs9qcQDiGWtgW_3std3sys12thread_local20abort_on_dtor_unwind15DtorUnwindGuardECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtNvNtNtCs9qcQDiGWtgW_3std3sys12thread_local20abort_on_dtor_unwind15DtorUnwindGuardECsir34p5gJ1Pk_9tls_probe:
.seh_proc _RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtNvNtNtCs9qcQDiGWtgW_3std3sys12thread_local20abort_on_dtor_unwind15DtorUnwindGuardECsir34p5gJ1Pk_9tls_probe
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movl	$0, 40(%rsp)
	movb	$0, 44(%rsp)
	leaq	.Lalloc_f669120e3e486c1bafaf3a5c53b19058(%rip), %rdx
	leaq	40(%rsp), %rcx
	movl	$123, %r8d
	callq	_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	movq	%rax, 48(%rsp)
	leaq	48(%rsp), %rcx
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	movl	$7, %ecx
	#APP

	int	$41

	#NO_APP
	ud2
	.seh_endproc

	.def	_RINvNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os13destroy_valueINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_EB1A_;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os13destroy_valueINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_EB1A_:
.Lfunc_begin2:
.seh_proc _RINvNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os13destroy_valueINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_EB1A_
	.seh_handler rust_eh_personality, @unwind, @except
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	movq	%rcx, %rdi
	movq	%rcx, 32(%rsp)
	movl	8(%rcx), %esi
	movl	$1, %edx
	movl	%esi, %ecx
	callq	TlsSetValue
	cmpl	$1, %eax
	jne	.LBB9_7
	movq	%rdi, %rcx
	callq	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
.Ltmp20:
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows16get_process_heap
.Ltmp21:
	movq	%rax, %rcx
	xorl	%edx, %edx
	movq	%rdi, %r8
	callq	HeapFree
	movl	%esi, %ecx
	xorl	%edx, %edx
	callq	TlsSetValue
	cmpl	$1, %eax
	jne	.LBB9_5
.Ltmp24:
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local5guard7windows6enable
	nop
.Ltmp25:
	.seh_startepilogue
	addq	$40, %rsp
	popq	%rdi
	popq	%rsi
	.seh_endepilogue
	retq
.LBB9_7:
.Ltmp14:
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windows4fail
.Ltmp15:
	jmp	.LBB9_6
.LBB9_5:
.Ltmp22:
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windows4fail
.Ltmp23:
	jmp	.LBB9_6
.LBB9_8:
.Ltmp16:
.Ltmp17:
	leaq	32(%rsp), %rcx
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os16AlignedSystemBoxINtNtB4_4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_EEB1Z_
.Ltmp18:
	jmp	.LBB9_11
.LBB9_9:
.Ltmp19:
	callq	_RNvNtCs2Ja4erDm0Jl_4core9panicking16panic_in_cleanup
	ud2
.LBB9_10:
.Ltmp26:
.LBB9_11:
.Ltmp27:
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtNvNtNtCs9qcQDiGWtgW_3std3sys12thread_local20abort_on_dtor_unwind15DtorUnwindGuardECsir34p5gJ1Pk_9tls_probe
.Ltmp28:
.LBB9_6:
	ud2
.LBB9_12:
.Ltmp29:
	callq	_RNvNtCs2Ja4erDm0Jl_4core9panicking16panic_in_cleanup
	ud2
.Lfunc_end2:
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table9:
.Lexception2:
	.byte	255
	.byte	0
	.uleb128 .Lttbase0-.Lttbaseref0
.Lttbaseref0:
	.byte	1
	.uleb128 .Lcst_end2-.Lcst_begin2
.Lcst_begin2:
	.uleb128 .Ltmp20-.Lfunc_begin2
	.uleb128 .Ltmp25-.Ltmp20
	.uleb128 .Ltmp26-.Lfunc_begin2
	.byte	1
	.uleb128 .Ltmp14-.Lfunc_begin2
	.uleb128 .Ltmp15-.Ltmp14
	.uleb128 .Ltmp16-.Lfunc_begin2
	.byte	1
	.uleb128 .Ltmp22-.Lfunc_begin2
	.uleb128 .Ltmp23-.Ltmp22
	.uleb128 .Ltmp26-.Lfunc_begin2
	.byte	1
	.uleb128 .Ltmp17-.Lfunc_begin2
	.uleb128 .Ltmp18-.Ltmp17
	.uleb128 .Ltmp19-.Lfunc_begin2
	.byte	1
	.uleb128 .Ltmp27-.Lfunc_begin2
	.uleb128 .Ltmp28-.Ltmp27
	.uleb128 .Ltmp29-.Lfunc_begin2
	.byte	1
.Lcst_end2:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase0:
	.byte	0
	.p2align	2, 0x0
	.text

	.def	_RINvNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os13destroy_valueINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_ECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RINvNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os13destroy_valueINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_ECsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin3:
.seh_proc _RINvNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os13destroy_valueINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_ECsir34p5gJ1Pk_9tls_probe
	.seh_handler rust_eh_personality, @unwind, @except
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	movq	%rcx, %rsi
	movl	8(%rcx), %edi
	movl	$1, %edx
	movl	%edi, %ecx
	callq	TlsSetValue
	cmpl	$1, %eax
	jne	.LBB10_7
.Ltmp36:
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows16get_process_heap
.Ltmp37:
	movq	%rax, %rcx
	xorl	%edx, %edx
	movq	%rsi, %r8
	callq	HeapFree
	movl	%edi, %ecx
	xorl	%edx, %edx
	callq	TlsSetValue
	cmpl	$1, %eax
	jne	.LBB10_5
.Ltmp40:
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local5guard7windows6enable
	nop
.Ltmp41:
	.seh_startepilogue
	addq	$40, %rsp
	popq	%rdi
	popq	%rsi
	.seh_endepilogue
	retq
.LBB10_7:
.Ltmp30:
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windows4fail
.Ltmp31:
	jmp	.LBB10_6
.LBB10_5:
.Ltmp38:
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windows4fail
.Ltmp39:
	jmp	.LBB10_6
.LBB10_8:
.Ltmp32:
.Ltmp33:
	callq	_RNvNtNtNtCs9qcQDiGWtgW_3std3sys5alloc7windows16get_process_heap
.Ltmp34:
	movq	%rax, %rcx
	xorl	%edx, %edx
	movq	%rsi, %r8
	callq	HeapFree
	jmp	.LBB10_12
.LBB10_10:
.Ltmp35:
	callq	_RNvNtCs2Ja4erDm0Jl_4core9panicking16panic_in_cleanup
	ud2
.LBB10_11:
.Ltmp42:
.LBB10_12:
.Ltmp43:
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtNvNtNtCs9qcQDiGWtgW_3std3sys12thread_local20abort_on_dtor_unwind15DtorUnwindGuardECsir34p5gJ1Pk_9tls_probe
.Ltmp44:
.LBB10_6:
	ud2
.LBB10_13:
.Ltmp45:
	callq	_RNvNtCs2Ja4erDm0Jl_4core9panicking16panic_in_cleanup
	ud2
.Lfunc_end3:
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table10:
.Lexception3:
	.byte	255
	.byte	0
	.uleb128 .Lttbase1-.Lttbaseref1
.Lttbaseref1:
	.byte	1
	.uleb128 .Lcst_end3-.Lcst_begin3
.Lcst_begin3:
	.uleb128 .Ltmp36-.Lfunc_begin3
	.uleb128 .Ltmp41-.Ltmp36
	.uleb128 .Ltmp42-.Lfunc_begin3
	.byte	1
	.uleb128 .Ltmp30-.Lfunc_begin3
	.uleb128 .Ltmp31-.Ltmp30
	.uleb128 .Ltmp32-.Lfunc_begin3
	.byte	1
	.uleb128 .Ltmp38-.Lfunc_begin3
	.uleb128 .Ltmp39-.Ltmp38
	.uleb128 .Ltmp42-.Lfunc_begin3
	.byte	1
	.uleb128 .Ltmp33-.Lfunc_begin3
	.uleb128 .Ltmp34-.Ltmp33
	.uleb128 .Ltmp35-.Lfunc_begin3
	.byte	1
	.uleb128 .Ltmp43-.Lfunc_begin3
	.uleb128 .Ltmp44-.Ltmp43
	.uleb128 .Ltmp45-.Lfunc_begin3
	.byte	1
.Lcst_end3:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase1:
	.byte	0
	.p2align	2, 0x0
	.text

	.def	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop;
	.scl	2;
	.type	32;
	.endef
	.globl	_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
	.p2align	4
_RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop:
.seh_proc _RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCs2Ja4erDm0Jl_4core3ops4drop4Drop4drop
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

	.def	_RNvXNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RNvXNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin4:
.seh_proc _RNvXNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.seh_handler rust_eh_personality, @unwind, @except
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	%rcx, %rsi
	movq	(%rcx), %rcx
	callq	_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	movq	%rax, %rdi
	testq	%rax, %rax
	je	.LBB12_6
	movq	8(%rsi), %rax
	testq	%rax, %rax
	je	.LBB12_5
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB12_5
	testq	%rcx, %rcx
	je	.LBB12_5
	decq	%rax
	leaq	48(%rsp), %rcx
	movq	%rax, 48(%rsp)
	movb	$3, 40(%rsp)
.Ltmp46:
	callq	_RNvXsd_NtNtCs2Ja4erDm0Jl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.Ltmp47:
.LBB12_5:
	movq	%rdi, 8(%rsi)
.LBB12_6:
	testq	%rdi, %rdi
	setne	%al
	.seh_startepilogue
	addq	$56, %rsp
	popq	%rdi
	popq	%rsi
	.seh_endepilogue
	retq
.LBB12_7:
.Ltmp48:
	movq	%rdi, 8(%rsi)
	movq	%rax, %rcx
	callq	_Unwind_Resume
	ud2
.Lfunc_end4:
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table12:
.Lexception4:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end4-.Lcst_begin4
.Lcst_begin4:
	.uleb128 .Lfunc_begin4-.Lfunc_begin4
	.uleb128 .Ltmp46-.Lfunc_begin4
	.byte	0
	.byte	0
	.uleb128 .Ltmp46-.Lfunc_begin4
	.uleb128 .Ltmp47-.Ltmp46
	.uleb128 .Ltmp48-.Lfunc_begin4
	.byte	0
	.uleb128 .Ltmp47-.Lfunc_begin4
	.uleb128 .Lfunc_end4-.Ltmp47
	.byte	0
	.byte	0
.Lcst_end4:
	.p2align	2, 0x0
	.text

	.def	_RNvYINtNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RNvYINtNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin5:
.seh_proc _RNvYINtNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.seh_handler rust_eh_personality, @unwind, @except
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	subq	$56, %rsp
	.seh_stackalloc 56
	.seh_endprologue
	movq	%rcx, %rsi
	movl	$0, 36(%rsp)
	cmpl	$128, %edx
	jae	.LBB13_1
	movb	%dl, 36(%rsp)
	movl	$1, %r8d
	jmp	.LBB13_6
.LBB13_1:
	movl	%edx, %eax
	andb	$63, %al
	orb	$-128, %al
	movl	%edx, %ecx
	shrl	$6, %ecx
	cmpl	$2048, %edx
	jae	.LBB13_3
	orb	$-64, %cl
	movb	%cl, 36(%rsp)
	movb	%al, 37(%rsp)
	movl	$2, %r8d
	jmp	.LBB13_6
.LBB13_3:
	andb	$63, %cl
	orb	$-128, %cl
	movl	%edx, %r8d
	shrl	$12, %r8d
	cmpl	$65535, %edx
	ja	.LBB13_5
	orb	$-32, %r8b
	movb	%r8b, 36(%rsp)
	movb	%cl, 37(%rsp)
	movb	%al, 38(%rsp)
	movl	$3, %r8d
	jmp	.LBB13_6
.LBB13_5:
	andb	$63, %r8b
	orb	$-128, %r8b
	shrl	$18, %edx
	orb	$-16, %dl
	movb	%dl, 36(%rsp)
	movb	%r8b, 37(%rsp)
	movb	%cl, 38(%rsp)
	movb	%al, 39(%rsp)
	movl	$4, %r8d
.LBB13_6:
	movq	(%rsi), %rcx
	leaq	36(%rsp), %rdx
	callq	_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	movq	%rax, %rdi
	testq	%rax, %rax
	je	.LBB13_12
	movq	8(%rsi), %rax
	testq	%rax, %rax
	je	.LBB13_11
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB13_11
	testq	%rcx, %rcx
	je	.LBB13_11
	decq	%rax
	leaq	48(%rsp), %rcx
	movq	%rax, 48(%rsp)
	movb	$3, 40(%rsp)
.Ltmp49:
	callq	_RNvXsd_NtNtCs2Ja4erDm0Jl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.Ltmp50:
.LBB13_11:
	movq	%rdi, 8(%rsi)
.LBB13_12:
	testq	%rdi, %rdi
	setne	%al
	.seh_startepilogue
	addq	$56, %rsp
	popq	%rdi
	popq	%rsi
	.seh_endepilogue
	retq
.LBB13_14:
.Ltmp51:
	movq	%rdi, 8(%rsi)
	movq	%rax, %rcx
	callq	_Unwind_Resume
	ud2
.Lfunc_end5:
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table13:
.Lexception5:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end5-.Lcst_begin5
.Lcst_begin5:
	.uleb128 .Lfunc_begin5-.Lfunc_begin5
	.uleb128 .Ltmp49-.Lfunc_begin5
	.byte	0
	.byte	0
	.uleb128 .Ltmp49-.Lfunc_begin5
	.uleb128 .Ltmp50-.Ltmp49
	.uleb128 .Ltmp51-.Lfunc_begin5
	.byte	0
	.uleb128 .Ltmp50-.Lfunc_begin5
	.uleb128 .Lfunc_end5-.Ltmp50
	.byte	0
	.byte	0
.Lcst_end5:
	.p2align	2, 0x0
	.text

	.def	_RNvYINtNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RNvYINtNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	movq	%r8, %r9
	movq	%rdx, %r8
	leaq	.Lvtable.0(%rip), %rdx
	jmp	_RNvNtCs2Ja4erDm0Jl_4core3fmt5write

	.def	_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin6:
.seh_proc _RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	.seh_handler rust_eh_personality, @unwind, @except
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
	pushq	%rbp
	.seh_pushreg %rbp
	pushq	%rbx
	.seh_pushreg %rbx
	subq	$72, %rsp
	.seh_stackalloc 72
	.seh_endprologue
	testq	%r8, %r8
	je	.LBB15_1
	movq	%r8, %rsi
	movq	%rdx, %rdi
	movq	%rcx, %r14
	movabsq	$188978561024, %r13
	leaq	64(%rsp), %r15
	leaq	.LJTI15_0(%rip), %rbp
	movl	$255, %ebx
	jmp	.LBB15_4
.LBB15_11:
	movq	%r12, %rax
	shrq	$32, %rax
	cmpq	%r13, %r12
	cmovael	%ebx, %eax
	cmpb	$35, %al
	jne	.LBB15_2
	.p2align	4
.LBB15_18:
	testq	%rsi, %rsi
	je	.LBB15_1
.LBB15_4:
	movq	%r14, %rcx
	movq	%rdi, %rdx
	movq	%rsi, %r8
	callq	_RNvXs5_NtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windowsNtB5_6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write5write
	movq	%rdx, %r12
	movq	%rax, 40(%rsp)
	movq	%rdx, 48(%rsp)
	cmpq	$1, %rax
	jne	.LBB15_9
	movl	%r12d, %eax
	andl	$3, %eax
	movslq	(%rbp,%rax,4), %rax
	addq	%rbp, %rax
	jmpq	*%rax
.LBB15_15:
	cmpb	$35, 16(%r12)
	je	.LBB15_18
	jmp	.LBB15_2
	.p2align	4
.LBB15_9:
	testq	%r12, %r12
	je	.LBB15_10
	movq	%rsi, %rax
	subq	%r12, %rax
	jb	.LBB15_12
	addq	%r12, %rdi
	movq	%rax, %rsi
	jmp	.LBB15_18
.LBB15_6:
.Ltmp52:
	callq	_RNvNtNtNtCs2Ja4erDm0Jl_4core2io5error12os_functions16get_os_functions
.Ltmp53:
	movq	%r12, %rcx
	shrq	$32, %rcx
.Ltmp54:
	callq	*16(%rax)
.Ltmp55:
	testb	%al, %al
	jne	.LBB15_18
	jmp	.LBB15_2
.LBB15_16:
	cmpb	$35, 31(%r12)
	jne	.LBB15_2
	decq	%r12
	movq	%r12, 64(%rsp)
	movb	$3, 56(%rsp)
	movq	%r15, %rcx
	callq	_RNvXsd_NtNtCs2Ja4erDm0Jl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	jmp	.LBB15_18
.LBB15_1:
	xorl	%r12d, %r12d
.LBB15_2:
	movq	%r12, %rax
	.seh_startepilogue
	addq	$72, %rsp
	popq	%rbx
	popq	%rbp
	popq	%rdi
	popq	%rsi
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	.seh_endepilogue
	retq
.LBB15_10:
	leaq	.Lalloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2(%rip), %r12
	jmp	.LBB15_2
.LBB15_12:
	leaq	.Lalloc_ba1bfa9f01512a2cbee7a129faa5ce35(%rip), %r9
	movq	%r12, %rcx
	movq	%rsi, %rdx
	movq	%rsi, %r8
	callq	_RNvNtNtCs2Ja4erDm0Jl_4core5slice5index16slice_index_fail
	ud2
.LBB15_19:
.Ltmp56:
	movq	%rax, %rsi
.Ltmp57:
	leaq	48(%rsp), %rcx
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueNtNtNtB4_2io5error5ErrorECsir34p5gJ1Pk_9tls_probe
.Ltmp58:
	movq	%rsi, %rcx
	callq	_Unwind_Resume
	ud2
.LBB15_21:
.Ltmp59:
	callq	_RNvNtCs2Ja4erDm0Jl_4core9panicking16panic_in_cleanup
	ud2
.Lfunc_end6:
	.section	.rdata,"dr"
	.p2align	2, 0x0
.LJTI15_0:
	.long	.LBB15_15-.LJTI15_0
	.long	.LBB15_16-.LJTI15_0
	.long	.LBB15_6-.LJTI15_0
	.long	.LBB15_11-.LJTI15_0
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table15:
.Lexception6:
	.byte	255
	.byte	0
	.uleb128 .Lttbase2-.Lttbaseref2
.Lttbaseref2:
	.byte	1
	.uleb128 .Lcst_end6-.Lcst_begin6
.Lcst_begin6:
	.uleb128 .Lfunc_begin6-.Lfunc_begin6
	.uleb128 .Ltmp52-.Lfunc_begin6
	.byte	0
	.byte	0
	.uleb128 .Ltmp52-.Lfunc_begin6
	.uleb128 .Ltmp55-.Ltmp52
	.uleb128 .Ltmp56-.Lfunc_begin6
	.byte	0
	.uleb128 .Ltmp55-.Lfunc_begin6
	.uleb128 .Ltmp57-.Ltmp55
	.byte	0
	.byte	0
	.uleb128 .Ltmp57-.Lfunc_begin6
	.uleb128 .Ltmp58-.Ltmp57
	.uleb128 .Ltmp59-.Lfunc_begin6
	.byte	1
	.uleb128 .Ltmp58-.Lfunc_begin6
	.uleb128 .Lfunc_end6-.Ltmp58
	.byte	0
	.byte	0
.Lcst_end6:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase2:
	.byte	0
	.p2align	2, 0x0
	.text

	.def	_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.p2align	4
_RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
.Lfunc_begin7:
.seh_proc _RNvYNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrNtNtNtCs2Ja4erDm0Jl_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.seh_handler rust_eh_personality, @unwind, @except
	pushq	%rsi
	.seh_pushreg %rsi
	subq	$64, %rsp
	.seh_stackalloc 64
	.seh_endprologue
	movq	%r8, %r9
	movq	%rdx, %r8
	movq	%rcx, 32(%rsp)
	movq	$0, 40(%rsp)
.Ltmp60:
	leaq	.Lvtable.0(%rip), %rdx
	leaq	32(%rsp), %rcx
	callq	_RNvNtCs2Ja4erDm0Jl_4core3fmt5write
.Ltmp61:
	testb	%al, %al
	je	.LBB16_5
	movq	40(%rsp), %rax
	testq	%rax, %rax
	jne	.LBB16_10
.Ltmp62:
	leaq	.Lalloc_a439077caaee6bab9af745f1531d72a4(%rip), %rcx
	leaq	.Lalloc_1a670b50d276900533e9b5ea016aeb83(%rip), %r8
	movl	$173, %edx
	callq	_RNvNtCs2Ja4erDm0Jl_4core9panicking9panic_fmt
.Ltmp63:
	ud2
.LBB16_5:
	movq	40(%rsp), %rax
	testq	%rax, %rax
	je	.LBB16_9
	movl	%eax, %ecx
	andl	$3, %ecx
	leal	-2(%rcx), %edx
	cmpl	$2, %edx
	jb	.LBB16_9
	testq	%rcx, %rcx
	je	.LBB16_9
	decq	%rax
	leaq	56(%rsp), %rcx
	movq	%rax, 56(%rsp)
	movb	$3, 48(%rsp)
	callq	_RNvXsd_NtNtCs2Ja4erDm0Jl_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
.LBB16_9:
	xorl	%eax, %eax
.LBB16_10:
	.seh_startepilogue
	addq	$64, %rsp
	popq	%rsi
	.seh_endepilogue
	retq
.LBB16_12:
.Ltmp64:
	movq	%rax, %rsi
.Ltmp65:
	leaq	32(%rsp), %rcx
	callq	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe
.Ltmp66:
	movq	%rsi, %rcx
	callq	_Unwind_Resume
	ud2
.LBB16_11:
.Ltmp67:
	callq	_RNvNtCs2Ja4erDm0Jl_4core9panicking16panic_in_cleanup
	ud2
.Lfunc_end7:
	.seh_handlerdata
	.text
	.seh_endproc
	.section	.xdata,"dr"
	.p2align	2, 0x0
GCC_except_table16:
.Lexception7:
	.byte	255
	.byte	0
	.uleb128 .Lttbase3-.Lttbaseref3
.Lttbaseref3:
	.byte	1
	.uleb128 .Lcst_end7-.Lcst_begin7
.Lcst_begin7:
	.uleb128 .Ltmp60-.Lfunc_begin7
	.uleb128 .Ltmp63-.Ltmp60
	.uleb128 .Ltmp64-.Lfunc_begin7
	.byte	0
	.uleb128 .Ltmp63-.Lfunc_begin7
	.uleb128 .Ltmp65-.Ltmp63
	.byte	0
	.byte	0
	.uleb128 .Ltmp65-.Lfunc_begin7
	.uleb128 .Ltmp66-.Ltmp65
	.uleb128 .Ltmp67-.Lfunc_begin7
	.byte	1
	.uleb128 .Ltmp66-.Lfunc_begin7
	.uleb128 .Lfunc_end7-.Ltmp66
	.byte	0
	.byte	0
.Lcst_end7:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase3:
	.byte	0
	.p2align	2, 0x0
	.text

	.def	access_all_tls;
	.scl	2;
	.type	32;
	.endef
	.globl	access_all_tls
	.p2align	4
access_all_tls:
.seh_proc access_all_tls
	pushq	%r14
	.seh_pushreg %r14
	pushq	%rsi
	.seh_pushreg %rsi
	pushq	%rdi
	.seh_pushreg %rdi
	pushq	%rbx
	.seh_pushreg %rbx
	subq	$40, %rsp
	.seh_stackalloc 40
	.seh_endprologue
	cmpq	$0, _RNvNCNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP023___RUST_STD_INTERNAL_VAL(%rip)
	je	.LBB17_1
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local5guard7windows6enable
.LBB17_1:
	movl	_RNvNCNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP023___RUST_STD_INTERNAL_VAL+24(%rip), %esi
	testl	%esi, %esi
	je	.LBB17_3
	decl	%esi
.LBB17_4:
	movl	%esi, %ecx
	callq	TlsGetValue
	cmpq	$1, %rax
	jbe	.LBB17_5
	testq	%rax, %rax
	je	.LBB17_30
.LBB17_7:
	movq	(%rax), %rbx
	cmpq	$0, _RNvNCNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP023___RUST_STD_INTERNAL_VAL(%rip)
	je	.LBB17_8
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local5guard7windows6enable
.LBB17_8:
	movl	_RNvNCNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP023___RUST_STD_INTERNAL_VAL+24(%rip), %esi
	testl	%esi, %esi
	je	.LBB17_10
	decl	%esi
.LBB17_11:
	movl	%esi, %ecx
	callq	TlsGetValue
	cmpq	$1, %rax
	jbe	.LBB17_12
	testq	%rax, %rax
	je	.LBB17_30
.LBB17_14:
	movq	(%rax), %rsi
	cmpq	$0, _RNvNCNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP023___RUST_STD_INTERNAL_VAL(%rip)
	je	.LBB17_15
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local5guard7windows6enable
.LBB17_15:
	movl	_RNvNCNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP023___RUST_STD_INTERNAL_VAL+24(%rip), %edi
	testl	%edi, %edi
	je	.LBB17_17
	decl	%edi
.LBB17_18:
	movl	%edi, %ecx
	callq	TlsGetValue
	cmpq	$1, %rax
	jbe	.LBB17_19
	testq	%rax, %rax
	je	.LBB17_30
.LBB17_21:
	movq	(%rax), %r14
	cmpq	$0, _RNvNCNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP023___RUST_STD_INTERNAL_VAL(%rip)
	je	.LBB17_22
	callq	_RNvNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local5guard7windows6enable
.LBB17_22:
	movl	_RNvNCNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP023___RUST_STD_INTERNAL_VAL+24(%rip), %edi
	testl	%edi, %edi
	je	.LBB17_24
	decl	%edi
.LBB17_25:
	movl	%edi, %ecx
	callq	TlsGetValue
	cmpq	$1, %rax
	jbe	.LBB17_26
	testq	%rax, %rax
	je	.LBB17_30
.LBB17_28:
	addq	%rbx, %rsi
	addq	%r14, %rsi
	addq	(%rax), %rsi
	movq	%rsi, %rax
	.seh_startepilogue
	addq	$40, %rsp
	popq	%rbx
	popq	%rdi
	popq	%rsi
	popq	%r14
	.seh_endepilogue
	retq
.LBB17_3:
	leaq	_RNvNCNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP023___RUST_STD_INTERNAL_VAL(%rip), %rcx
	callq	_RNvMNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windowsNtB2_7LazyKey4init
	movl	%eax, %esi
	jmp	.LBB17_4
.LBB17_5:
	movl	%esi, %ecx
	movq	%rax, %rdx
	xorl	%r8d, %r8d
	callq	_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_E14try_initializeNvNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP27___rust_std_internal_init_fnEB22_
	testq	%rax, %rax
	jne	.LBB17_7
	jmp	.LBB17_30
.LBB17_10:
	leaq	_RNvNCNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP023___RUST_STD_INTERNAL_VAL(%rip), %rcx
	callq	_RNvMNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windowsNtB2_7LazyKey4init
	movl	%eax, %esi
	jmp	.LBB17_11
.LBB17_12:
	movl	%esi, %ecx
	movq	%rax, %rdx
	xorl	%r8d, %r8d
	callq	_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_E14try_initializeNvNvB1D_10CONST_DROP27___rust_std_internal_init_fnEB1D_
	testq	%rax, %rax
	jne	.LBB17_14
	jmp	.LBB17_30
.LBB17_17:
	leaq	_RNvNCNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP023___RUST_STD_INTERNAL_VAL(%rip), %rcx
	callq	_RNvMNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windowsNtB2_7LazyKey4init
	movl	%eax, %edi
	jmp	.LBB17_18
.LBB17_19:
	movl	%edi, %ecx
	movq	%rax, %rdx
	xorl	%r8d, %r8d
	callq	_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_E14try_initializeNvNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP27___rust_std_internal_init_fnEB22_
	testq	%rax, %rax
	jne	.LBB17_21
	jmp	.LBB17_30
.LBB17_24:
	leaq	_RNvNCNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP023___RUST_STD_INTERNAL_VAL(%rip), %rcx
	callq	_RNvMNtNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local3key7windowsNtB2_7LazyKey4init
	movl	%eax, %edi
	jmp	.LBB17_25
.LBB17_26:
	movl	%edi, %ecx
	movq	%rax, %rdx
	xorl	%r8d, %r8d
	callq	_RINvMs2_NtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2osINtB6_7StorageINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_E14try_initializeNvNvB1D_9LAZY_DROP27___rust_std_internal_init_fnEB1D_
	testq	%rax, %rax
	jne	.LBB17_28
.LBB17_30:
	leaq	.Lalloc_d967d5ae25e575721be85468d37a1295(%rip), %rcx
	callq	_RNvNtNtCs9qcQDiGWtgW_3std6thread5local18panic_access_error
	ud2
	.seh_endproc

	.section	.rdata,"dr"
.Lalloc_5b02399d15196f4565c9574d7e606137:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library\\std\\src\\thread\\local.rs"

	.p2align	3, 0x0
.Lalloc_d967d5ae25e575721be85468d37a1295:
	.quad	.Lalloc_5b02399d15196f4565c9574d7e606137
	.asciz	"\205\000\000\000\000\000\000\000\255\001\000\000\031\000\000"

	.p2align	3, 0x0
.Lvtable.0:
	.quad	_RINvNtCs2Ja4erDm0Jl_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe
	.asciz	"\020\000\000\000\000\000\000\000\b\000\000\000\000\000\000"
	.quad	_RNvXNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.quad	_RNvYINtNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.quad	_RNvYINtNvNtNtCs2Ja4erDm0Jl_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs9qcQDiGWtgW_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe

.Lalloc_a439077caaee6bab9af745f1531d72a4:
	.ascii	"a formatting trait implementation returned an error when the underlying stream did not"

.Lalloc_686723c4fc0450ab61097742d7654dd3:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library\\core\\src\\io\\write.rs"

	.p2align	3, 0x0
.Lalloc_1a670b50d276900533e9b5ea016aeb83:
	.quad	.Lalloc_686723c4fc0450ab61097742d7654dd3
	.asciz	"\202\000\000\000\000\000\000\000\233\001\000\000\021\000\000"

.Lalloc_0407a3e59c8988b5606db2776e0ad4d5:
	.ascii	"fatal runtime error: Allocation failure, aborting\n"

	.data
	.globl	_RNvNCNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP023___RUST_STD_INTERNAL_VAL:
	.quad	_RINvNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os13destroy_valueINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_EB1A_
	.zero	20
	.zero	4

	.globl	_RNvNCNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP023___RUST_STD_INTERNAL_VAL:
	.quad	_RINvNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os13destroy_valueINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_ECsir34p5gJ1Pk_9tls_probe
	.zero	20
	.zero	4

	.globl	_RNvNCNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP023___RUST_STD_INTERNAL_VAL:
	.quad	_RINvNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os13destroy_valueINtNtCs2Ja4erDm0Jl_4core4cell4CellyEKj8_ECsir34p5gJ1Pk_9tls_probe
	.zero	20
	.zero	4

	.globl	_RNvNCNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
_RNvNCNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP023___RUST_STD_INTERNAL_VAL:
	.quad	_RINvNtNtNtCs9qcQDiGWtgW_3std3sys12thread_local2os13destroy_valueINtNtCs2Ja4erDm0Jl_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEKj8_EB1A_
	.zero	20
	.zero	4

	.section	.rdata,"dr"
.Lalloc_f669120e3e486c1bafaf3a5c53b19058:
	.ascii	"fatal runtime error: thread local panicked on drop, aborting\n"

.Lalloc_8d68fcbc011419193bd208f22e2789d1:
	.ascii	"failed to write whole buffer"

	.p2align	3, 0x0
.Lalloc_0c6bd0c1dc63d8d7fb1eb0c800f5dec2:
	.quad	.Lalloc_8d68fcbc011419193bd208f22e2789d1
	.ascii	"\034\000\000\000\000\000\000\000\027"
	.zero	7

	.p2align	3, 0x0
.Lalloc_ba1bfa9f01512a2cbee7a129faa5ce35:
	.quad	.Lalloc_686723c4fc0450ab61097742d7654dd3
	.asciz	"\202\000\000\000\000\000\000\000\334\000\000\000$\000\000"

	.data
	.globl	__imp__RNvNCNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP023___RUST_STD_INTERNAL_VAL:
	.quad	_RNvNCNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP023___RUST_STD_INTERNAL_VAL

	.globl	__imp__RNvNCNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP023___RUST_STD_INTERNAL_VAL:
	.quad	_RNvNCNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP023___RUST_STD_INTERNAL_VAL

	.globl	__imp__RNvNCNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP023___RUST_STD_INTERNAL_VAL:
	.quad	_RNvNCNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP023___RUST_STD_INTERNAL_VAL

	.globl	__imp__RNvNCNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__imp__RNvNCNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP023___RUST_STD_INTERNAL_VAL:
	.quad	_RNvNCNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP023___RUST_STD_INTERNAL_VAL

