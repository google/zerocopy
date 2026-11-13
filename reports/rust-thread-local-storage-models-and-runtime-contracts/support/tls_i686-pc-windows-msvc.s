	.def	@feat.00;
	.scl	3;
	.type	0;
	.endef
	.globl	@feat.00
@feat.00 = 1
	.att_syntax
	.file	"tls_probe.d6bd21401e7e8eac-cgu.0"
	.def	__RINvMs0_NtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_;
	.scl	3;
	.type	32;
	.endef
	.section	.text$unlikely,"xr",one_only,__RINvMs0_NtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_,unique,0
	.p2align	4
__RINvMs0_NtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%esi
	andl	$-8, %esp
	subl	$32, %esp
	movl	%ecx, %eax
	movzbl	8(%ecx), %ecx
	testl	%ecx, %ecx
	je	LBB0_5
	cmpl	$1, %ecx
	je	LBB0_12
	xorl	%eax, %eax
	jmp	LBB0_12
LBB0_5:
	testl	%edx, %edx
	je	LBB0_6
	movl	8(%edx), %ecx
	movl	12(%edx), %esi
	testb	$1, (%edx)
	movl	$0, 4(%edx)
	movl	$0, (%edx)
	je	LBB0_6
	movl	%ecx, (%eax)
	movl	%esi, 4(%eax)
	movb	$1, 8(%eax)
	jmp	LBB0_8
LBB0_6:
	movl	$0, 4(%esp)
	movl	$13, (%esp)
	movl	%esp, %ecx
	#APP
	#NO_APP
	movzbl	8(%eax), %ecx
	movsd	(%eax), %xmm0
	movl	(%esp), %edx
	movl	4(%esp), %esi
	cmpl	$1, %ecx
	movsd	%xmm0, 16(%esp)
	movl	%esi, 4(%eax)
	movl	%edx, (%eax)
	movb	$1, 8(%eax)
	jne	LBB0_7
	movl	%eax, %esi
	leal	16(%esp), %eax
	pushl	%eax
	calll	__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop
	addl	$4, %esp
	jmp	LBB0_11
LBB0_7:
	testl	%ecx, %ecx
	jne	LBB0_9
LBB0_8:
	pushl	$__RINvNtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native4lazy7destroyINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_
	movl	%eax, %esi
	pushl	%eax
	calll	__RNvNtNtNtNtCs13X54pRMZqp_3std3sys12thread_local11destructors4list8register
	addl	$8, %esp
LBB0_11:
	movl	%esi, %eax
LBB0_12:
	leal	-4(%ebp), %esp
	popl	%esi
	popl	%ebp
	retl
LBB0_9:
	movl	%esp, %esi
	movl	$0, 8(%esp)
	movb	$0, 12(%esp)
	leal	8(%esp), %edx
	movl	%esi, %ecx
	pushl	$87
	pushl	$_alloc_70165e1942fbf2cb7aee6a08556ee215
	calll	__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	addl	$8, %esp
	movl	%esi, %ecx
	calll	__RINvNtCselTjGGDqQnQ_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe
	movl	$7, %ecx
	#APP

	int	$41

	#NO_APP
	ud2

	.def	__RINvNtCselTjGGDqQnQ_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RINvNtCselTjGGDqQnQ_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe,unique,1
	.p2align	4
__RINvNtCselTjGGDqQnQ_4core3ptr9drop_glueINtNtB4_6result6ResultuNtNtNtB4_2io5error5ErrorEECsir34p5gJ1Pk_9tls_probe:
	cmpb	$3, (%ecx)
	jne	LBB1_1
	addl	$4, %ecx
	pushl	%ecx
	calll	__RNvXsd_NtNtCselTjGGDqQnQ_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	addl	$4, %esp
	retl
LBB1_1:
	retl

	.def	__RINvNtCselTjGGDqQnQ_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RINvNtCselTjGGDqQnQ_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe,unique,2
	.p2align	4
__RINvNtCselTjGGDqQnQ_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe:
	movl	4(%esp), %eax
	cmpb	$3, (%eax)
	jne	LBB2_2
	addl	$4, %eax
	pushl	%eax
	calll	__RNvXsd_NtNtCselTjGGDqQnQ_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	addl	$4, %esp
LBB2_2:
	retl

	.def	__RINvNtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native4lazy7destroyINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RINvNtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native4lazy7destroyINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_,unique,3
	.p2align	4
__RINvNtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native4lazy7destroyINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1E_:
	movl	4(%esp), %eax
	movzbl	8(%eax), %ecx
	movb	$2, 8(%eax)
	cmpb	$1, %cl
	je	__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop
	retl

	.def	__RINvNtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native5eager7destroyINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RINvNtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native5eager7destroyINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_,unique,4
	.p2align	4
__RINvNtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native5eager7destroyINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_:
	movl	4(%esp), %eax
	movb	$2, 8(%eax)
	jmp	__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop

	.def	__RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls,unique,5
	.globl	__RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls
	.p2align	4
__RNSNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U643tls:
	movl	__tls_index, %eax
	movl	%fs:__tls_array, %ecx
	movl	(%ecx,%eax,4), %eax
	leal	__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@SECREL32(%eax), %eax
	retl

	.def	__RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls,unique,6
	.globl	__RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls
	.p2align	4
__RNSNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN643tls:
	movl	__tls_index, %eax
	movl	%fs:__tls_array, %ecx
	movl	(%ecx,%eax,4), %eax
	leal	__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64@SECREL32(%eax), %eax
	retl

	.def	__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls,unique,7
	.globl	__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls
	.p2align	4
__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL3tls:
	movl	__tls_index, %eax
	movl	%fs:__tls_array, %ecx
	movl	(%ecx,%eax,4), %eax
	leal	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32(%eax), %eax
	retl

	.def	__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls,unique,8
	.globl	__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls
	.p2align	4
__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls:
	movl	__tls_index, %eax
	movl	%fs:__tls_array, %ecx
	movl	(%ecx,%eax,4), %eax
	leal	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32(%eax), %eax
	retl

	.def	__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls,unique,9
	.globl	__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls
	.p2align	4
__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL3tls:
	movl	__tls_index, %eax
	movl	%fs:__tls_array, %ecx
	movl	(%ecx,%eax,4), %eax
	leal	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32(%eax), %eax
	retl

	.def	__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls,unique,10
	.globl	__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls
	.p2align	4
__RNSNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL3tls:
	movl	__tls_index, %eax
	movl	%fs:__tls_array, %ecx
	movl	(%ecx,%eax,4), %eax
	leal	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32(%eax), %eax
	retl

	.def	__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop,unique,11
	.globl	__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop
	.p2align	4
__RNvXCsir34p5gJ1Pk_9tls_probeNtB2_7HasDropNtNtNtCselTjGGDqQnQ_4core3ops4drop4Drop4drop:
	pushl	%ebp
	movl	%esp, %ebp
	andl	$-8, %esp
	subl	$8, %esp
	movl	8(%ebp), %eax
	movsd	(%eax), %xmm0
	movl	%esp, %eax
	movsd	%xmm0, (%esp)
	#APP
	#NO_APP
	movl	%ebp, %esp
	popl	%ebp
	retl

	.def	__RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,12
	.p2align	4
__RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
Lfunc_begin0:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	pushl	%edi
	pushl	%esi
	subl	$28, %esp
	movl	%esp, -28(%ebp)
	movl	$-1, -16(%ebp)
	movl	$___ehhandler$_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe, -20(%ebp)
	movl	8(%ebp), %edi
	leal	-24(%ebp), %ecx
	movl	16(%ebp), %esi
	movl	12(%ebp), %eax
	movl	%fs:0, %edx
	movl	%edx, -24(%ebp)
	movl	%ecx, %fs:0
	leal	-40(%ebp), %ecx
	movl	8(%edi), %edx
	pushl	%esi
	pushl	%eax
	calll	__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	addl	$8, %esp
	movzbl	-40(%ebp), %ecx
	cmpb	$-1, %cl
	je	LBB12_4
	cmpb	$3, (%edi)
	jne	LBB12_3
	movl	8(%ebp), %eax
	movl	$0, -16(%ebp)
	addl	$4, %eax
	pushl	%eax
	movb	%cl, -29(%ebp)
	calll	__RNvXsd_NtNtCselTjGGDqQnQ_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	movzbl	-29(%ebp), %ecx
	addl	$4, %esp
LBB12_3:
	movsd	-40(%ebp), %xmm0
	movl	8(%ebp), %eax
	movsd	%xmm0, (%eax)
LBB12_4:
	movl	-24(%ebp), %edx
	cmpb	$-1, %cl
	setne	%al
	movl	%edx, %fs:0
	addl	$28, %esp
	popl	%esi
	popl	%edi
	popl	%ebx
	popl	%ebp
	retl
	.def	"?dtor$5@?0?_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$5@?0?_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA":
LBB12_5:
	pushl	%ebp
	subl	$8, %esp
	addl	$12, %ebp
	movsd	-40(%ebp), %xmm0
	movl	8(%ebp), %eax
	movsd	%xmm0, (%eax)
	addl	$8, %esp
	popl	%ebp
	retl
Lfunc_end0:
	.section	.xdata,"dr",associative,__RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,0
	.p2align	2, 0x0
L__ehtable$_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	1
$stateUnwindMap$_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
	.long	-1
	.long	"?dtor$5@?0?_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe@4HA"
	.section	.text,"xr",one_only,__RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,12

	.def	__RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,13
	.p2align	4
__RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
Lfunc_begin1:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	pushl	%edi
	pushl	%esi
	subl	$32, %esp
	movl	12(%ebp), %eax
	movl	%esp, -28(%ebp)
	movl	$-1, -16(%ebp)
	movl	$___ehhandler$_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe, -20(%ebp)
	movl	8(%ebp), %edi
	leal	-24(%ebp), %ecx
	movl	%fs:0, %edx
	cmpl	$128, %eax
	movl	%edx, -24(%ebp)
	movl	%ecx, %fs:0
	movl	$0, -32(%ebp)
	jae	LBB13_1
	movb	%al, -32(%ebp)
	movl	$1, %eax
	jmp	LBB13_6
LBB13_1:
	movl	%eax, %ecx
	movl	%eax, %edx
	andb	$63, %cl
	shrl	$6, %edx
	orb	$-128, %cl
	cmpl	$2048, %eax
	jae	LBB13_3
	orb	$-64, %dl
	movl	$2, %eax
	movb	%dl, -32(%ebp)
	movb	%cl, -31(%ebp)
	jmp	LBB13_6
LBB13_3:
	andb	$63, %dl
	movl	%eax, %ebx
	orb	$-128, %dl
	shrl	$12, %ebx
	cmpl	$65535, %eax
	ja	LBB13_5
	orb	$-32, %bl
	movl	$3, %eax
	movb	%bl, -32(%ebp)
	movb	%dl, -31(%ebp)
	movb	%cl, -30(%ebp)
	jmp	LBB13_6
LBB13_5:
	shrl	$18, %eax
	andb	$63, %bl
	orb	$-16, %al
	orb	$-128, %bl
	movb	%al, -32(%ebp)
	movl	$4, %eax
	movb	%bl, -31(%ebp)
	movb	%dl, -30(%ebp)
	movb	%cl, -29(%ebp)
LBB13_6:
	movl	8(%edi), %edx
	leal	-32(%ebp), %esi
	leal	-44(%ebp), %ecx
	pushl	%eax
	pushl	%esi
	calll	__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	addl	$8, %esp
	movzbl	-44(%ebp), %eax
	cmpb	$-1, %al
	je	LBB13_10
	cmpb	$3, (%edi)
	jne	LBB13_9
	movb	%al, -33(%ebp)
	movl	8(%ebp), %eax
	movl	$0, -16(%ebp)
	addl	$4, %eax
	pushl	%eax
	calll	__RNvXsd_NtNtCselTjGGDqQnQ_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	movzbl	-33(%ebp), %eax
	addl	$4, %esp
LBB13_9:
	movsd	-44(%ebp), %xmm0
	movl	8(%ebp), %ecx
	movsd	%xmm0, (%ecx)
LBB13_10:
	movl	-24(%ebp), %ecx
	cmpb	$-1, %al
	setne	%al
	movl	%ecx, %fs:0
	addl	$32, %esp
	popl	%esi
	popl	%edi
	popl	%ebx
	popl	%ebp
	retl
	.def	"?dtor$12@?0?_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$12@?0?_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA":
LBB13_12:
	pushl	%ebp
	subl	$8, %esp
	addl	$12, %ebp
	movsd	-44(%ebp), %xmm0
	movl	8(%ebp), %eax
	movsd	%xmm0, (%eax)
	addl	$8, %esp
	popl	%ebp
	retl
Lfunc_end1:
	.section	.xdata,"dr",associative,__RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,1
	.p2align	2, 0x0
L__ehtable$_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	1
$stateUnwindMap$_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
	.long	-1
	.long	"?dtor$12@?0?_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe@4HA"
	.section	.text,"xr",one_only,__RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,13

	.def	__RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,14
	.p2align	4
__RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	pushl	12(%esp)
	pushl	12(%esp)
	pushl	$_vtable.0
	pushl	16(%esp)
	calll	__RNvNtCselTjGGDqQnQ_4core3fmt5write
	addl	$16, %esp
	retl

	.def	__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,15
	.p2align	4
__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
Lfunc_begin2:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	pushl	%edi
	pushl	%esi
	subl	$48, %esp
	calll	L15$pb
L15$pb:
	popl	%eax
	movl	%esp, -28(%ebp)
	movl	$-1, -16(%ebp)
	movl	$___ehhandler$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe, -20(%ebp)
	movl	8(%ebp), %ebx
	movl	%ecx, %esi
	movl	12(%ebp), %ecx
	movl	%edx, %edi
	movl	%edx, -52(%ebp)
	movl	%eax, -60(%ebp)
	movl	%fs:0, %eax
	movl	%esi, -44(%ebp)
	movl	%ebx, -48(%ebp)
	leal	-40(%ebp), %ebx
	movl	%eax, -24(%ebp)
	leal	-24(%ebp), %eax
	movl	%eax, %fs:0
	jmp	LBB15_1
LBB15_10:
	movl	-36(%ebp), %eax
	cmpb	$35, 8(%eax)
LBB15_9:
	movl	-32(%ebp), %ecx
	jne	LBB15_16
LBB15_1:
	testl	%ecx, %ecx
	je	LBB15_22
	movl	$-1, -16(%ebp)
	movl	%ecx, -32(%ebp)
	pushl	%ecx
	pushl	-48(%ebp)
	pushl	%edi
	pushl	%ebx
	calll	__RNvXs5_NtNtNtCs13X54pRMZqp_3std3sys5stdio7windowsNtB5_6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write5write
	addl	$16, %esp
	movzbl	-40(%ebp), %eax
	cmpl	$255, %eax
	je	LBB15_14
	movl	LJTI15_0(,%eax,4), %eax
	addl	-60(%ebp), %eax
	jmpl	*%eax
LBB15_4:
	movl	-36(%ebp), %eax
	movl	$0, -16(%ebp)
	movl	%eax, -56(%ebp)
	calll	__RNvNtNtNtCselTjGGDqQnQ_4core2io5error12os_functions16get_os_functions
	pushl	-56(%ebp)
	calll	*8(%eax)
	addl	$4, %esp
	testb	%al, %al
	leal	-40(%ebp), %ebx
	je	LBB15_7
	cmpb	$3, -40(%ebp)
	movl	-44(%ebp), %esi
	movl	-52(%ebp), %edi
	je	LBB15_12
	jmp	LBB15_13
	.p2align	4
LBB15_14:
	movl	-36(%ebp), %eax
	testl	%eax, %eax
	je	LBB15_15
	movl	-32(%ebp), %edx
	movl	%edx, %ecx
	subl	%eax, %ecx
	jb	LBB15_20
	addl	%eax, -48(%ebp)
	jmp	LBB15_1
LBB15_11:
	movl	-36(%ebp), %eax
	cmpb	$35, 16(%eax)
	jne	LBB15_16
LBB15_12:
	leal	-36(%ebp), %eax
	movl	$-1, -16(%ebp)
	pushl	%eax
	calll	__RNvXsd_NtNtCselTjGGDqQnQ_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	addl	$4, %esp
LBB15_13:
	movl	-32(%ebp), %ecx
	jmp	LBB15_1
LBB15_8:
	cmpb	$35, -39(%ebp)
	jmp	LBB15_9
LBB15_22:
	movb	$-1, (%esi)
	jmp	LBB15_23
LBB15_15:
	movl	$_anon.d11343ae16036a0b0a60efd45b2c56cb.0, %ebx
	jmp	LBB15_16
LBB15_7:
	movl	-44(%ebp), %esi
LBB15_16:
	movsd	(%ebx), %xmm0
	movsd	%xmm0, (%esi)
LBB15_23:
	movl	-24(%ebp), %eax
	movl	%eax, %fs:0
	movl	%esi, %eax
	addl	$48, %esp
	popl	%esi
	popl	%edi
	popl	%ebx
	popl	%ebp
	retl
LBB15_20:
	movl	$0, -16(%ebp)
	pushl	$_alloc_6a27cde1cb1aea013a9d1048bbdc89ec
	pushl	%edx
	pushl	%edx
	pushl	%eax
	calll	__RNvNtNtCselTjGGDqQnQ_4core5slice5index16slice_index_fail
	addl	$16, %esp
	ud2
	.def	"?dtor$24@?0?_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$24@?0?_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA":
LBB15_24:
	pushl	%ebp
	subl	$16, %esp
	addl	$12, %ebp
	cmpb	$3, -40(%ebp)
	jne	LBB15_26
	leal	-36(%ebp), %eax
	pushl	%eax
	calll	__RNvXsd_NtNtCselTjGGDqQnQ_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	addl	$4, %esp
LBB15_26:
	addl	$16, %esp
	popl	%ebp
	retl
Lfunc_end2:
	.p2align	2
LJTI15_0:
	.long	LBB15_4-L15$pb
	.long	LBB15_8-L15$pb
	.long	LBB15_10-L15$pb
	.long	LBB15_11-L15$pb
	.section	.xdata,"dr",associative,__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,2
	.p2align	2, 0x0
L__ehtable$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	1
$stateUnwindMap$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
	.long	-1
	.long	"?dtor$24@?0?_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe@4HA"
	.section	.text,"xr",one_only,__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,15

	.def	__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,16
	.p2align	4
__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
Lfunc_begin3:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	pushl	%edi
	pushl	%esi
	subl	$32, %esp
	movl	%esp, -28(%ebp)
	movl	$-1, -16(%ebp)
	movl	$___ehhandler$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe, -20(%ebp)
	movl	%ecx, -32(%ebp)
	movl	12(%ebp), %esi
	movl	%fs:0, %eax
	movl	%eax, -24(%ebp)
	leal	-24(%ebp), %eax
	movl	%eax, %fs:0
	movb	$-1, (%ecx)
	movl	8(%ebp), %eax
	movl	%edx, -36(%ebp)
	movl	$0, -16(%ebp)
	movl	4(%ecx), %edx
	movl	(%ecx), %ecx
	movl	%edx, -40(%ebp)
	movl	%ecx, -44(%ebp)
	leal	-44(%ebp), %edx
	pushl	%esi
	pushl	%eax
	pushl	$_vtable.0
	pushl	%edx
	calll	__RNvNtCselTjGGDqQnQ_4core3fmt5write
	addl	$16, %esp
	movzbl	-44(%ebp), %ecx
	testb	%al, %al
	je	LBB16_8
	movl	-32(%ebp), %esi
	cmpb	$-1, %cl
	je	LBB16_3
	movsd	-44(%ebp), %xmm0
	movsd	%xmm0, (%esi)
	jmp	LBB16_11
LBB16_8:
	movl	-32(%ebp), %esi
	cmpb	$3, %cl
	jne	LBB16_11
	leal	-40(%ebp), %eax
	movl	$-1, -16(%ebp)
	pushl	%eax
	calll	__RNvXsd_NtNtCselTjGGDqQnQ_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	addl	$4, %esp
LBB16_11:
	movl	-24(%ebp), %eax
	movl	%eax, %fs:0
	movl	%esi, %eax
	addl	$32, %esp
	popl	%esi
	popl	%edi
	popl	%ebx
	popl	%ebp
	retl
LBB16_3:
	pushl	$_alloc_b669088d5dd24290bcda13acda724848
	pushl	$173
	pushl	$_alloc_a439077caaee6bab9af745f1531d72a4
	calll	__RNvNtCselTjGGDqQnQ_4core9panicking9panic_fmt
	addl	$12, %esp
	ud2
	.def	"?dtor$5@?0?_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA";
	.scl	3;
	.type	32;
	.endef
	.p2align	4
"?dtor$5@?0?_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA":
LBB16_5:
	pushl	%ebp
	subl	$16, %esp
	addl	$12, %ebp
	cmpb	$3, -44(%ebp)
	jne	LBB16_7
	leal	-40(%ebp), %eax
	pushl	%eax
	calll	__RNvXsd_NtNtCselTjGGDqQnQ_4core2io5errorNtB5_11CustomOwnerNtNtNtB9_3ops4drop4Drop4drop
	addl	$4, %esp
LBB16_7:
	addl	$16, %esp
	popl	%ebp
	retl
Lfunc_end3:
	.section	.xdata,"dr",associative,__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,3
	.p2align	2, 0x0
L__ehtable$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.long	429065506
	.long	1
	.long	$stateUnwindMap$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
	.long	0
	.long	0
	.long	0
	.long	0
	.long	0
	.long	1
$stateUnwindMap$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	.long	-1
	.long	"?dtor$5@?0?_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe@4HA"
	.section	.text,"xr",one_only,__RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,16

	.def	_access_all_tls;
	.scl	2;
	.type	32;
	.endef
	.section	.text,"xr",one_only,_access_all_tls,unique,17
	.globl	_access_all_tls
	.p2align	4
_access_all_tls:
	pushl	%ebp
	movl	%esp, %ebp
	pushl	%ebx
	pushl	%edi
	pushl	%esi
	andl	$-8, %esp
	subl	$48, %esp
	movl	__tls_index, %eax
	movl	%fs:__tls_array, %ecx
	movl	(%ecx,%eax,4), %ecx
	movl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32+4(%ecx), %ebx
	movl	__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@SECREL32(%ecx), %edi
	movl	__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@SECREL32+4(%ecx), %esi
	movl	__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64@SECREL32+4(%ecx), %edx
	movl	__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64@SECREL32(%ecx), %eax
	movl	%ebx, 40(%esp)
	movl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32(%ecx), %ebx
	addl	$1, %edi
	adcl	$0, %esi
	movl	%edi, __RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@SECREL32(%ecx)
	movl	%esi, __RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64@SECREL32+4(%ecx)
	movl	%ebx, 36(%esp)
	leal	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32(%ecx), %ebx
	movzbl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32+8(%ecx), %ecx
	testl	%ecx, %ecx
	jne	LBB17_1
LBB17_3:
	movl	(%ebx), %ecx
	movl	%ecx, 28(%esp)
	movl	4(%ebx), %ecx
	movl	%fs:__tls_array, %ebx
	movl	%ecx, 32(%esp)
	movl	__tls_index, %ecx
	movl	(%ebx,%ecx,4), %ebx
	cmpb	$1, __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32+8(%ebx)
	leal	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL@SECREL32(%ebx), %ecx
	jne	LBB17_5
	movl	(%ecx), %ebx
	movl	4(%ecx), %ecx
	movl	%ebx, 8(%esp)
	movl	%ecx, 12(%esp)
LBB17_6:
	movl	__tls_index, %ecx
	movl	%fs:__tls_array, %ebx
	movl	(%ebx,%ecx,4), %ebx
	cmpb	$1, __RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32+8(%ebx)
	leal	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL@SECREL32(%ebx), %ecx
	jne	LBB17_7
LBB17_9:
	addl	%edi, %eax
	adcl	%esi, %edx
	addl	36(%esp), %eax
	adcl	40(%esp), %edx
	addl	28(%esp), %eax
	adcl	32(%esp), %edx
	addl	8(%esp), %eax
	adcl	12(%esp), %edx
	addl	(%ecx), %eax
	adcl	4(%ecx), %edx
	leal	-12(%ebp), %esp
	popl	%esi
	popl	%edi
	popl	%ebx
	popl	%ebp
	retl
LBB17_5:
	movl	$0, 20(%esp)
	movl	$7, 16(%esp)
	leal	16(%esp), %ebx
	#APP
	#NO_APP
	movl	16(%esp), %ebx
	movl	%ebx, 8(%esp)
	movl	20(%esp), %ebx
	movl	%ebx, 12(%esp)
	movl	%ebx, 4(%ecx)
	movl	8(%esp), %ebx
	movl	%ebx, (%ecx)
	movb	$1, 8(%ecx)
	jmp	LBB17_6
LBB17_7:
	movl	%edx, (%esp)
	xorl	%edx, %edx
	movl	%eax, 4(%esp)
	calll	__RINvMs0_NtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native4lazyINtB6_7StorageINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEuE16get_or_init_slowNvNvB1O_9LAZY_DROP27___rust_std_internal_init_fnEB1O_
	movl	%eax, %ecx
	movl	(%esp), %edx
	movl	4(%esp), %eax
	testl	%ecx, %ecx
	jne	LBB17_9
	jmp	LBB17_8
LBB17_1:
	cmpl	$1, %ecx
	jne	LBB17_8
	pushl	$__RINvNtNtNtNtCs13X54pRMZqp_3std3sys12thread_local6native5eager7destroyINtNtCselTjGGDqQnQ_4core4cell4CellNtCsir34p5gJ1Pk_9tls_probe7HasDropEEB1F_
	pushl	%ebx
	movl	%edx, 8(%esp)
	movl	%eax, 12(%esp)
	calll	__RNvNtNtNtNtCs13X54pRMZqp_3std3sys12thread_local11destructors4list8register
	movl	12(%esp), %eax
	movl	8(%esp), %edx
	addl	$8, %esp
	movb	$0, 8(%ebx)
	jmp	LBB17_3
LBB17_8:
	pushl	$_alloc_be9c1efca84b69faa59cec9167786ea9
	calll	__RNvNtNtCs13X54pRMZqp_3std6thread5local18panic_access_error
	addl	$4, %esp
	ud2

	.def	___ehhandler$_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,___ehhandler$_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe,unique,18
	.p2align	4
___ehhandler$_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe:
	movl	$L__ehtable$_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe, %eax
	jmp	___CxxFrameHandler3

	.def	___ehhandler$_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,___ehhandler$_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe,unique,19
	.p2align	4
___ehhandler$_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe:
	movl	$L__ehtable$_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe, %eax
	jmp	___CxxFrameHandler3

	.def	___ehhandler$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,___ehhandler$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe,unique,20
	.p2align	4
___ehhandler$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe:
	movl	$L__ehtable$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe, %eax
	jmp	___CxxFrameHandler3

	.def	___ehhandler$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe;
	.scl	3;
	.type	32;
	.endef
	.section	.text,"xr",one_only,___ehhandler$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe,unique,21
	.p2align	4
___ehhandler$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe:
	movl	$L__ehtable$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe, %eax
	jmp	___CxxFrameHandler3

	.section	.rdata,"dr",one_only,_alloc_70165e1942fbf2cb7aee6a08556ee215,unique,22
_alloc_70165e1942fbf2cb7aee6a08556ee215:
	.ascii	"fatal runtime error: unreachable, aborting\n"

	.section	.rdata,"dr",one_only,_alloc_5b02399d15196f4565c9574d7e606137,unique,23
_alloc_5b02399d15196f4565c9574d7e606137:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library\\std\\src\\thread\\local.rs"

	.section	.rdata,"dr",one_only,_alloc_be9c1efca84b69faa59cec9167786ea9,unique,24
	.p2align	2, 0x0
_alloc_be9c1efca84b69faa59cec9167786ea9:
	.long	_alloc_5b02399d15196f4565c9574d7e606137
	.asciz	"\205\000\000\000\255\001\000\000\031\000\000"

	.section	.rdata,"dr",one_only,_vtable.0,unique,25
	.p2align	2, 0x0
_vtable.0:
	.long	__RINvNtCselTjGGDqQnQ_4core3ptr9drop_glueINtNvNtNtB4_2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrEECsir34p5gJ1Pk_9tls_probe
	.asciz	"\f\000\000\000\004\000\000"
	.long	__RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.long	__RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.long	__RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write9write_fmtCsir34p5gJ1Pk_9tls_probe

	.section	.rdata,"dr",one_only,_alloc_a439077caaee6bab9af745f1531d72a4,unique,26
_alloc_a439077caaee6bab9af745f1531d72a4:
	.ascii	"a formatting trait implementation returned an error when the underlying stream did not"

	.section	.rdata,"dr",one_only,_alloc_686723c4fc0450ab61097742d7654dd3,unique,27
_alloc_686723c4fc0450ab61097742d7654dd3:
	.asciz	"/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library\\core\\src\\io\\write.rs"

	.section	.rdata,"dr",one_only,_alloc_b669088d5dd24290bcda13acda724848,unique,28
	.p2align	2, 0x0
_alloc_b669088d5dd24290bcda13acda724848:
	.long	_alloc_686723c4fc0450ab61097742d7654dd3
	.asciz	"\202\000\000\000\233\001\000\000\021\000\000"

	.section	.tls$,"dw",one_only,__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,unique,29
	.globl	__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	.p2align	3, 0x0
__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64:
	.ascii	"\210wfUD3\"\021"

	.section	.tls$,"dw",one_only,__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64,unique,30
	.globl	__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	.p2align	6, 0x0
__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64:
	.asciz	"\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000"

	.section	.tls$,"dw",one_only,__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL,unique,31
	.globl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL:
	.ascii	"c\000\000\000\000\000\000\000\001"
	.zero	7

	.section	.tls$,"dw",one_only,__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,32
	.globl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	7

	.section	.tls$,"dw",one_only,__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,33
	.globl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.asciz	"*\000\000\000\000\000\000"

	.section	.tls$,"dw",one_only,__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,unique,34
	.globl	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	3, 0x0
__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL:
	.zero	8
	.zero	1
	.zero	7

	.section	.rdata,"dr",one_only,_alloc_8d68fcbc011419193bd208f22e2789d1,unique,35
_alloc_8d68fcbc011419193bd208f22e2789d1:
	.ascii	"failed to write whole buffer"

	.section	.rdata,"dr",one_only,_alloc_a581db5dec7871ed68c0f24b18f2c603,unique,36
	.p2align	2, 0x0
_alloc_a581db5dec7871ed68c0f24b18f2c603:
	.long	_alloc_8d68fcbc011419193bd208f22e2789d1
	.ascii	"\034\000\000\000\027"
	.zero	3

	.section	.rdata,"dr",one_only,_anon.d11343ae16036a0b0a60efd45b2c56cb.0,unique,37
	.p2align	2, 0x0
_anon.d11343ae16036a0b0a60efd45b2c56cb.0:
	.byte	2
	.zero	3
	.long	_alloc_a581db5dec7871ed68c0f24b18f2c603

	.section	.rdata,"dr",one_only,_alloc_6a27cde1cb1aea013a9d1048bbdc89ec,unique,38
	.p2align	2, 0x0
_alloc_6a27cde1cb1aea013a9d1048bbdc89ec:
	.long	_alloc_686723c4fc0450ab61097742d7654dd3
	.asciz	"\202\000\000\000\334\000\000\000$\000\000"

	.section	.data,"dw",one_only,__imp___RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64,unique,39
	.globl	__imp___RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64
	.p2align	2, 0x0
__imp___RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64:
	.long	__RNvCsir34p5gJ1Pk_9tls_probe11RAW_TLS_U64

	.section	.data,"dw",one_only,__imp___RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64,unique,40
	.globl	__imp___RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64
	.p2align	2, 0x0
__imp___RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64:
	.long	__RNvCsir34p5gJ1Pk_9tls_probe15RAW_TLS_ALIGN64

	.section	.data,"dw",one_only,__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL,unique,41
	.globl	__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	2, 0x0
__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL:
	.long	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe10CONST_DROP0023___RUST_STD_INTERNAL_VAL

	.section	.data,"dw",one_only,__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,42
	.globl	__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	2, 0x0
__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.long	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe11LAZY_NODROP0s_023___RUST_STD_INTERNAL_VAL

	.section	.data,"dw",one_only,__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL,unique,43
	.globl	__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL
	.p2align	2, 0x0
__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL:
	.long	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe12CONST_NODROP0s_023___RUST_STD_INTERNAL_VAL

	.section	.data,"dw",one_only,__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL,unique,44
	.globl	__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL
	.p2align	2, 0x0
__imp___RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL:
	.long	__RNvNCNKNvCsir34p5gJ1Pk_9tls_probe9LAZY_DROP0023___RUST_STD_INTERNAL_VAL

	.safeseh	___ehhandler$_RNvXNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmtINtB2_7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtB8_3fmt5Write9write_strCsir34p5gJ1Pk_9tls_probe
	.safeseh	___ehhandler$_RNvYINtNvNtNtCselTjGGDqQnQ_4core2io5write17default_write_fmt7AdapterNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrENtNtBb_3fmt5Write10write_charCsir34p5gJ1Pk_9tls_probe
	.safeseh	___ehhandler$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_allCsir34p5gJ1Pk_9tls_probe
	.safeseh	___ehhandler$_RNvYNtNtNtNtCs13X54pRMZqp_3std3sys5stdio7windows6StderrNtNtNtCselTjGGDqQnQ_4core2io5write5Write9write_fmtCsir34p5gJ1Pk_9tls_probe
