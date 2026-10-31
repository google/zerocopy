.intel_syntax noprefix
.text

.globl anneal_double_u64
.type anneal_double_u64, @function
anneal_double_u64:
    push rbp
    mov rbp, rsp
    sub rsp, 16
    mov QWORD PTR [rbp - 8], rdi
    mov rax, QWORD PTR [rbp - 8]
    mov rcx, QWORD PTR [rbp - 8]
    add rax, rcx
    mov QWORD PTR [rbp - 16], rax
    mov rax, QWORD PTR [rbp - 16]
    add rsp, 16
    pop rbp
    ret

.section .note.GNU-stack,"",@progbits
