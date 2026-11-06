	.build_version macos, 11, 0
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_abi_c_vector
	.p2align	2
_abi_c_vector:
	ret

	.globl	_abi_rust_vector
	.p2align	2
_abi_rust_vector:
	ldr	q0, [x0]
	str	q0, [x8]
	ret

	.globl	_abi_system_vector
	.p2align	2
_abi_system_vector:
	ret

.subsections_via_symbols
