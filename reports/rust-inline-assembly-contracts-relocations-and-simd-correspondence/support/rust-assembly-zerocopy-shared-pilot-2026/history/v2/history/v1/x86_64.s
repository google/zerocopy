// E46 proposed positive source: Linux x86-64 SysV, baseline SSE2.
// Rust global_asm uses Intel syntax; do not add AT&T options.
.text
.p2align 4
.global pilot_mul
.type pilot_mul,@function
pilot_mul:
    mov rcx, rdx
    mov rax, rdi
    mul rsi
    mov [rcx], rax
    mov [rcx + 8], rdx
    ret
.size pilot_mul, .-pilot_mul

.global pilot_add128
.type pilot_add128,@function
pilot_add128:
    mov rcx, [rdi]
    mov r8, [rdi + 8]
    add rcx, [rsi]
    adc r8, [rsi + 8]
    setc al
    movzx eax, al
    mov [rdx], rcx
    mov [rdx + 8], r8
    ret
.size pilot_add128, .-pilot_add128

.global pilot_bswap
.type pilot_bswap,@function
pilot_bswap:
    mov rax, rdi
    bswap rax
    ret
.size pilot_bswap, .-pilot_bswap

.global pilot_load
.type pilot_load,@function
pilot_load:
    mov rax, [rdi]
    ret
.size pilot_load, .-pilot_load

.global pilot_store
.type pilot_store,@function
pilot_store:
    mov [rdi], rsi
    ret
.size pilot_store, .-pilot_store

.global pilot_copy16
.type pilot_copy16,@function
pilot_copy16:
    mov rax, [rsi]
    mov rcx, [rsi + 8]
    mov [rdi], rax
    mov [rdi + 8], rcx
    ret
.size pilot_copy16, .-pilot_copy16

.global pilot_ptr
.type pilot_ptr,@function
pilot_ptr:
    lea rax, [rdi + rsi]
    ret
.size pilot_ptr, .-pilot_ptr

.global pilot_call_helper
.type pilot_call_helper,@function
pilot_call_helper:
    .cfi_startproc
    sub rsp, 8
    .cfi_def_cfa_offset 16
    call pilot_helper
    add rax, 1
    add rsp, 8
    .cfi_def_cfa_offset 8
    ret
    .cfi_endproc
.size pilot_call_helper, .-pilot_call_helper

.global pilot_simd_copy16
.type pilot_simd_copy16,@function
pilot_simd_copy16:
    movdqa xmm0, [rsi]
    movdqa [rdi], xmm0
    ret
.size pilot_simd_copy16, .-pilot_simd_copy16

.global pilot_simd_add16
.type pilot_simd_add16,@function
pilot_simd_add16:
    movdqa xmm0, [rsi]
    movdqa xmm1, [rdx]
    paddb xmm0, xmm1
    movdqa [rdi], xmm0
    ret
.size pilot_simd_add16, .-pilot_simd_add16
.section .note.GNU-stack,"",@progbits
