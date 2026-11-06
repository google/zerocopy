; ModuleID = 'extended_pilot.9ff03a49851a832a-cgu.0'
source_filename = "extended_pilot.9ff03a49851a832a-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

module asm ".intel_syntax"
module asm "// E46 proposed positive source: Linux x86-64 SysV, baseline SSE2."
module asm "// Rust global_asm uses Intel syntax; do not add AT&T options."
module asm ".pushsection .text"
module asm ".p2align 4"
module asm ".global pilot_mul"
module asm ".type pilot_mul,@function"
module asm "pilot_mul:"
module asm "    mov rcx, rdx"
module asm "    mov rax, rdi"
module asm "    mul rsi"
module asm "    mov [rcx], rax"
module asm "    mov [rcx + 8], rdx"
module asm "    ret"
module asm ".size pilot_mul, .-pilot_mul"
module asm ""
module asm ".global pilot_add128"
module asm ".type pilot_add128,@function"
module asm "pilot_add128:"
module asm "    mov rcx, [rdi]"
module asm "    mov r8, [rdi + 8]"
module asm "    add rcx, [rsi]"
module asm "    adc r8, [rsi + 8]"
module asm "    setc al"
module asm "    movzx eax, al"
module asm "    mov [rdx], rcx"
module asm "    mov [rdx + 8], r8"
module asm "    ret"
module asm ".size pilot_add128, .-pilot_add128"
module asm ""
module asm ".global pilot_bswap"
module asm ".type pilot_bswap,@function"
module asm "pilot_bswap:"
module asm "    mov rax, rdi"
module asm "    bswap rax"
module asm "    ret"
module asm ".size pilot_bswap, .-pilot_bswap"
module asm ""
module asm ".global pilot_load"
module asm ".type pilot_load,@function"
module asm "pilot_load:"
module asm "    mov rax, [rdi]"
module asm "    ret"
module asm ".size pilot_load, .-pilot_load"
module asm ""
module asm ".global pilot_store"
module asm ".type pilot_store,@function"
module asm "pilot_store:"
module asm "    mov [rdi], rsi"
module asm "    ret"
module asm ".size pilot_store, .-pilot_store"
module asm ""
module asm ".global pilot_copy16"
module asm ".type pilot_copy16,@function"
module asm "pilot_copy16:"
module asm "    mov rax, [rsi]"
module asm "    mov rcx, [rsi + 8]"
module asm "    mov [rdi], rax"
module asm "    mov [rdi + 8], rcx"
module asm "    ret"
module asm ".size pilot_copy16, .-pilot_copy16"
module asm ""
module asm ".global pilot_ptr"
module asm ".type pilot_ptr,@function"
module asm "pilot_ptr:"
module asm "    lea rax, [rdi + rsi]"
module asm "    ret"
module asm ".size pilot_ptr, .-pilot_ptr"
module asm ""
module asm ".global pilot_call_helper"
module asm ".type pilot_call_helper,@function"
module asm "pilot_call_helper:"
module asm "    .cfi_startproc"
module asm "    sub rsp, 8"
module asm "    .cfi_def_cfa_offset 16"
module asm "    call pilot_helper"
module asm "    add rax, 1"
module asm "    add rsp, 8"
module asm "    .cfi_def_cfa_offset 8"
module asm "    ret"
module asm "    .cfi_endproc"
module asm ".size pilot_call_helper, .-pilot_call_helper"
module asm ""
module asm ".global pilot_simd_copy16"
module asm ".type pilot_simd_copy16,@function"
module asm "pilot_simd_copy16:"
module asm "    movdqa xmm0, [rsi]"
module asm "    movdqa [rdi], xmm0"
module asm "    ret"
module asm ".size pilot_simd_copy16, .-pilot_simd_copy16"
module asm ""
module asm ".global pilot_simd_add16"
module asm ".type pilot_simd_add16,@function"
module asm "pilot_simd_add16:"
module asm "    movdqa xmm0, [rsi]"
module asm "    movdqa xmm1, [rdx]"
module asm "    paddb xmm0, xmm1"
module asm "    movdqa [rdi], xmm0"
module asm "    ret"
module asm ".size pilot_simd_add16, .-pilot_simd_add16"
module asm ".popsection"
module asm ".pushsection .note.GNU-stack,\22\22,@progbits"
module asm ".popsection"
module asm ""
module asm ".att_syntax"

%"core::mem::maybe_uninit::MaybeUninit<[u64; 3]>" = type { [3 x i64] }
%"core::mem::maybe_uninit::MaybeUninit<[u64; 2]>" = type { [2 x i64] }
%"core::mem::maybe_uninit::MaybeUninit<(usize, usize, [u8; 16])>" = type { [4 x i64] }
%"core::mem::maybe_uninit::MaybeUninit<[u8; 16]>" = type { [16 x i8] }
%"core::mem::maybe_uninit::MaybeUninit<[u64; 7]>" = type { [7 x i64] }
%"core::mem::maybe_uninit::MaybeUninit<[u64; 4]>" = type { [4 x i64] }
%"core::mem::maybe_uninit::MaybeUninit<[u64; 5]>" = type { [5 x i64] }
%"core::fmt::rt::Argument<'_>" = type { %"core::fmt::rt::ArgumentType<'_>" }
%"core::fmt::rt::ArgumentType<'_>" = type { ptr, [1 x i64] }

@alloc_5a8fdd84b3281310cbf6b74bb6bf0065 = private unnamed_addr constant [218 x i8] c"unsafe precondition(s) violated: slice::get_unchecked_mut requires that the index is within the slice\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@anon.c68ad90a3a9dfb7a47f86997a7ce991b.0 = private unnamed_addr constant <{ [8 x i8], [8 x i8] }> <{ [8 x i8] zeroinitializer, [8 x i8] undef }>, align 8
@alloc_18d73aa062d524e9620b9e3b55bd9eb1 = private unnamed_addr constant [218 x i8] c"unsafe precondition(s) violated: slice::get_unchecked_mut requires that the range is within the slice\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_8079f9779031096a28f1c21fcf966932 = private unnamed_addr constant [90 x i8] c"/rustc/29483883eed69d5fb4db01964cdf2af4d86e9cb2/library/core/src/array/iter/iter_inner.rs\00", align 1
@alloc_4e72358380a5b7b26dfc8b890055d168 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_8079f9779031096a28f1c21fcf966932, [16 x i8] c"Z\00\00\00\00\00\00\00\12\00\00\00\17\00\00\00" }>, align 8
@vtable.0 = private unnamed_addr constant <{ [24 x i8], ptr, ptr, ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h9e7f46232d862455E", ptr @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17hb764b9c7e0decc7bE", ptr @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17hb764b9c7e0decc7bE" }>, align 8
@alloc_77e54a365f15d7fd19e674745691b3d5 = private unnamed_addr constant [79 x i8] c"/rustc/29483883eed69d5fb4db01964cdf2af4d86e9cb2/library/core/src/iter/range.rs\00", align 1
@alloc_51d47b6744cc9a652983e1beeae10eec = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_77e54a365f15d7fd19e674745691b3d5, [16 x i8] c"O\00\00\00\00\00\00\00\AB\01\00\00\01\00\00\00" }>, align 8
@alloc_3e1ebac14318b612ab4efabc52799932 = private unnamed_addr constant [186 x i8] c"unsafe precondition(s) violated: usize::unchecked_add cannot overflow\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_846c8306b730cf00804b037ffdb61170 = private unnamed_addr constant [186 x i8] c"unsafe precondition(s) violated: usize::unchecked_sub cannot overflow\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_5e88976d06bf274de8521db71c58c0ff = private unnamed_addr constant [76 x i8] c"/rustc/29483883eed69d5fb4db01964cdf2af4d86e9cb2/library/core/src/ptr/mod.rs\00", align 1
@alloc_9b0170f47317373e331799536b583a9f = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_5e88976d06bf274de8521db71c58c0ff, [16 x i8] c"L\00\00\00\00\00\00\00\0A\02\00\00\05\00\00\00" }>, align 8
@alloc_fad0cd83b7d1858a846a172eb260e593 = private unnamed_addr constant [42 x i8] c"is_aligned_to: align is not a power-of-two", align 1
@alloc_e92e94d0ff530782b571cfd99ec66aef = private unnamed_addr constant <{ ptr, [8 x i8] }> <{ ptr @alloc_fad0cd83b7d1858a846a172eb260e593, [8 x i8] c"*\00\00\00\00\00\00\00" }>, align 8
@alloc_37ae6c70dbc8911fffd4aae92801f83d = private unnamed_addr constant [82 x i8] c"/rustc/29483883eed69d5fb4db01964cdf2af4d86e9cb2/library/core/src/ptr/const_ptr.rs\00", align 1
@alloc_84fd0ee1b6b57a4ef5ffe86edcc9d22c = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_37ae6c70dbc8911fffd4aae92801f83d, [16 x i8] c"R\00\00\00\00\00\00\00\92\05\00\00\0D\00\00\00" }>, align 8
@alloc_bd3468a7b96187f70c1ce98a3e7a63bf = private unnamed_addr constant [283 x i8] c"unsafe precondition(s) violated: ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null and the specified memory ranges do not overlap\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_560a59ed819b9d9a5841f6e731c4c8e5 = private unnamed_addr constant [210 x i8] c"unsafe precondition(s) violated: NonNull::new_unchecked requires that the pointer is non-null\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_688a628223f8000b5508b05159671adf = private unnamed_addr constant [81 x i8] c"/rustc/29483883eed69d5fb4db01964cdf2af4d86e9cb2/library/core/src/ptr/non_null.rs\00", align 1
@alloc_b7e0708131946905642ff5dd82ebdcf1 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_688a628223f8000b5508b05159671adf, [16 x i8] c"Q\00\00\00\00\00\00\00l\05\00\00\12\00\00\00" }>, align 8
@alloc_75fb06c2453febd814e73f5f2e72ae38 = private unnamed_addr constant [199 x i8] c"unsafe precondition(s) violated: hint::unreachable_unchecked must never be reached\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_9cd20c3e415f4d39f0ceb012cb758628 = private unnamed_addr constant [40 x i8] c"there is no such thing as a release load", align 1
@alloc_b55f69a00b865c3d8c5f6dad0122f5bd = private unnamed_addr constant <{ ptr, [8 x i8] }> <{ ptr @alloc_9cd20c3e415f4d39f0ceb012cb758628, [8 x i8] c"(\00\00\00\00\00\00\00" }>, align 8
@alloc_519ab44b195e83be7f8a6112fc2d5ea2 = private unnamed_addr constant [80 x i8] c"/rustc/29483883eed69d5fb4db01964cdf2af4d86e9cb2/library/core/src/sync/atomic.rs\00", align 1
@alloc_9e3a721e4192284d14075f86dfc4f099 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_519ab44b195e83be7f8a6112fc2d5ea2, [16 x i8] c"P\00\00\00\00\00\00\00n\0F\00\00\18\00\00\00" }>, align 8
@alloc_96ab912d0054b46da785b206a96c9a45 = private unnamed_addr constant [49 x i8] c"there is no such thing as an acquire-release load", align 1
@alloc_0175cc81e1f5c8f5b757d44420d81e68 = private unnamed_addr constant <{ ptr, [8 x i8] }> <{ ptr @alloc_96ab912d0054b46da785b206a96c9a45, [8 x i8] c"1\00\00\00\00\00\00\00" }>, align 8
@alloc_6abb0457cb178205e8fd1b354df1db12 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_519ab44b195e83be7f8a6112fc2d5ea2, [16 x i8] c"P\00\00\00\00\00\00\00o\0F\00\00\17\00\00\00" }>, align 8
@alloc_bf39103a6db665396aab4632362d9353 = private unnamed_addr constant [42 x i8] c"there is no such thing as an acquire store", align 1
@alloc_d30e09dd75f4c40be0845475870856e6 = private unnamed_addr constant <{ ptr, [8 x i8] }> <{ ptr @alloc_bf39103a6db665396aab4632362d9353, [8 x i8] c"*\00\00\00\00\00\00\00" }>, align 8
@alloc_cbff13f8de7390bd0c1ed709ab3bc81d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_519ab44b195e83be7f8a6112fc2d5ea2, [16 x i8] c"P\00\00\00\00\00\00\00_\0F\00\00\18\00\00\00" }>, align 8
@alloc_00c0bce0fa6327f8ec8e69d6d765d508 = private unnamed_addr constant [50 x i8] c"there is no such thing as an acquire-release store", align 1
@alloc_9b1e61e0572571d4b583b134cc9efd32 = private unnamed_addr constant <{ ptr, [8 x i8] }> <{ ptr @alloc_00c0bce0fa6327f8ec8e69d6d765d508, [8 x i8] c"2\00\00\00\00\00\00\00" }>, align 8
@alloc_cf705c09b2a84d97072e92cdb5f56b17 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_519ab44b195e83be7f8a6112fc2d5ea2, [16 x i8] c"P\00\00\00\00\00\00\00`\0F\00\00\17\00\00\00" }>, align 8
@alloc_75cb10705f254685ab4a8a1f76a6bb3a = private unnamed_addr constant [78 x i8] c"/rustc/29483883eed69d5fb4db01964cdf2af4d86e9cb2/library/core/src/array/mod.rs\00", align 1
@alloc_c1eb65d8576c1851388b4960911d9ce4 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_75cb10705f254685ab4a8a1f76a6bb3a, [16 x i8] c"N\00\00\00\00\00\00\00\9A\03\00\00\1C\00\00\00" }>, align 8
@alloc_a950e1fcf72a54c3b4c4a808b1a03ffa = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_75cb10705f254685ab4a8a1f76a6bb3a, [16 x i8] c"N\00\00\00\00\00\00\00\9B\03\00\001\00\00\00" }>, align 8
@alloc_502d4ba5749b0feb67ea3f01a2b6a87b = private unnamed_addr constant [84 x i8] c"/rustc/29483883eed69d5fb4db01964cdf2af4d86e9cb2/library/core/src/ops/index_range.rs\00", align 1
@alloc_ff966b345d1e2cc01dc78ffc82fcc559 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_502d4ba5749b0feb67ea3f01a2b6a87b, [16 x i8] c"T\00\00\00\00\00\00\00>\00\00\00%\00\00\00" }>, align 8
@alloc_6d0f5de3526dcf1c1bed664a017ff4d3 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_8079f9779031096a28f1c21fcf966932, [16 x i8] c"Z\00\00\00\00\00\00\00\AE\00\00\00 \00\00\00" }>, align 8
@alloc_7eef3defff2f487d21aa8c214a5bbdb3 = private unnamed_addr constant [78 x i8] c"/rustc/29483883eed69d5fb4db01964cdf2af4d86e9cb2/library/core/src/ub_checks.rs\00", align 1
@alloc_97f23febd0de9d435a256e040eb42813 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_7eef3defff2f487d21aa8c214a5bbdb3, [16 x i8] c"N\00\00\00\00\00\00\00\88\00\00\006\00\00\00" }>, align 8
@alloc_a28e8c8fd5088943a8b5d44af697ff83 = private unnamed_addr constant [279 x i8] c"unsafe precondition(s) violated: slice::from_raw_parts requires the pointer to be aligned and non-null, and the total size of the slice not to exceed `isize::MAX`\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@vtable.1 = private unnamed_addr constant <{ [24 x i8], ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\10\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN80_$LT$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17hb1c293a2a609b964E" }>, align 8
@vtable.2 = private unnamed_addr constant <{ [24 x i8], ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN80_$LT$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17h4210c2b99a10fdafE" }>, align 8
@vtable.3 = private unnamed_addr constant <{ [24 x i8], ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\18\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN83_$LT$zerocopy..error..ConvertError$LT$A$C$S$C$V$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17h29c73536d87efdf9E" }>, align 8
@vtable.4 = private unnamed_addr constant <{ [24 x i8], ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\10\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN80_$LT$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17hb04a3bd15d4021cbE" }>, align 8
@vtable.5 = private unnamed_addr constant <{ [24 x i8], ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN80_$LT$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17h51fe6da6896044deE" }>, align 8
@vtable.6 = private unnamed_addr constant <{ [24 x i8], ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\10\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN80_$LT$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17h29c52287891abf53E" }>, align 8
@alloc_763310d78c99c2c1ad3f8a9821e942f3 = private unnamed_addr constant [61 x i8] c"is_nonoverlapping: `size_of::<T>() * count` overflows a usize", align 1
@alloc_83523ad8990d3aa2660a73fc704f9834 = private unnamed_addr constant [80 x i8] c"/rustc/29483883eed69d5fb4db01964cdf2af4d86e9cb2/library/core/src/slice/index.rs\00", align 1
@alloc_f5da46e47ed57d40a34a62ec70202128 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_83523ad8990d3aa2660a73fc704f9834, [16 x i8] c"P\00\00\00\00\00\00\00\04\02\00\00 \00\00\00" }>, align 8
@alloc_97d92cbf2a68a6ac45a1b13da79836e4 = private unnamed_addr constant [214 x i8] c"unsafe precondition(s) violated: slice::get_unchecked requires that the index is within the slice\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_c1dcee2c0147c5bf2be6e4d2507481cb = private unnamed_addr constant [9 x i8] c"SizeError", align 1
@alloc_a5fc064c3c780589d8ff39e05dfc61c2 = private unnamed_addr constant [9 x i8] c"Alignment", align 1
@vtable.7 = private unnamed_addr constant <{ [24 x i8], ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\10\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @"_ZN85_$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17h6f0dc63dc8f3dc96E" }>, align 8
@alloc_728f72eadbe4863ffd4951bbce90c6df = private unnamed_addr constant [4 x i8] c"Size", align 1
@alloc_c78721185e288f48cd1139f3ec1d2a9a = private unnamed_addr constant [8 x i8] c"Validity", align 1
@vtable.8 = private unnamed_addr constant <{ [24 x i8], ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00", ptr @"_ZN62_$LT$core..convert..Infallible$u20$as$u20$core..fmt..Debug$GT$3fmt17h64c104fba08fb8a5E" }>, align 8
@alloc_1705c20888af7763fe2181ce42f9e54e = private unnamed_addr constant [14 x i8] c"AlignmentError", align 1
@anon.c68ad90a3a9dfb7a47f86997a7ce991b.1 = private unnamed_addr constant <{ [24 x i8], [16 x i8], [1 x i8], [7 x i8] }> <{ [24 x i8] c"\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\10\00\00\00\00\00\00\00", [16 x i8] undef, [1 x i8] zeroinitializer, [7 x i8] undef }>, align 8
@anon.c68ad90a3a9dfb7a47f86997a7ce991b.2 = private unnamed_addr constant [32 x i8] c"\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00", align 8
@alloc_5ce921956b05d8539aba8c5faeee375a = private unnamed_addr constant [34 x i8] c"/e46/upstream/zerocopy/src/ref.rs\00", align 1
@alloc_5c158c4449c997c190308fffed5cd440 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_5ce921956b05d8539aba8c5faeee375a, [16 x i8] c"\22\00\00\00\00\00\00\00\99\04\00\00\12\00\00\00" }>, align 8
@alloc_f3cc2310f7efe1762c6731b6a8e4875b = private unnamed_addr constant [40 x i8] c"assertion failed: src.len() <= dst.len()", align 1
@alloc_257eb941809ff4ffb9c35582b06dad28 = private unnamed_addr constant [39 x i8] c"/e46/upstream/zerocopy/src/util/mod.rs\00", align 1
@alloc_03c388b1e702c5d2e3d9dbcfde85d5b3 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_257eb941809ff4ffb9c35582b06dad28, [16 x i8] c"'\00\00\00\00\00\00\00\1C\01\00\00\05\00\00\00" }>, align 8
@alloc_56a4be23acc1b1c3018ea783f63ae09a = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_257eb941809ff4ffb9c35582b06dad28, [16 x i8] c"'\00\00\00\00\00\00\00\83\00\00\00\15\00\00\00" }>, align 8
@alloc_289f879f0c7d96128297d6dd5a3ad59d = private unnamed_addr constant [41 x i8] c"assertion failed: align.is_power_of_two()", align 1
@alloc_c6f1a83cf202f671c45a40b695eb8f70 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_257eb941809ff4ffb9c35582b06dad28, [16 x i8] c"'\00\00\00\00\00\00\00\F9\00\00\00\05\00\00\00" }>, align 8
@alloc_e7b7d000cf090c3222f3db2028bfac60 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_257eb941809ff4ffb9c35582b06dad28, [16 x i8] c"'\00\00\00\00\00\00\00\FD\00\00\00\11\00\00\00" }>, align 8
@alloc_070512b75885343f240d4e39148a647a = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_257eb941809ff4ffb9c35582b06dad28, [16 x i8] c"'\00\00\00\00\00\00\00Y\02\00\00\11\00\00\00" }>, align 8
@alloc_4515a21d4dc9b36f89435de9319bc84f = private unnamed_addr constant [37 x i8] c"/e46/upstream/zerocopy/src/layout.rs\00", align 1
@alloc_c7fb12713fc7ee73392f756a24cec321 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00\1E\03\00\00\11\00\00\00" }>, align 8
@alloc_a500d906b91607583596fa15e63c2ada = private unnamed_addr constant [40 x i8] c"internal error: entered unreachable code", align 1
@alloc_46a03d2f1091ab2605bc31f4a926f118 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00!\03\00\00\11\00\00\00" }>, align 8
@alloc_21ddd4c26dc1532b2647d440f1b43a1d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00w\00\00\00\15\00\00\00" }>, align 8
@alloc_8db9b9cdc5fa06515b130316754951f4 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00y\00\00\00\15\00\00\00" }>, align 8
@alloc_62c4135799e1c4b88c454bf0806d12af = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00|\00\00\00\15\00\00\00" }>, align 8
@alloc_2a1e08f3dea28730048a53142e6e2d0d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00A\01\00\00\1F\00\00\00" }>, align 8
@alloc_1159bf97533187ac0a3ca94bbadf71c7 = private unnamed_addr constant [55 x i8] c"attempted to cast to slice type with zero-sized element", align 1
@alloc_6e5ff68ef613cd819c351642e46138cf = private unnamed_addr constant <{ ptr, [8 x i8] }> <{ ptr @alloc_1159bf97533187ac0a3ca94bbadf71c7, [8 x i8] c"7\00\00\00\00\00\00\00" }>, align 8
@alloc_c0a3c00142921a8f95892928b7888f5e = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00\9A\06\00\00\15\00\00\00" }>, align 8
@alloc_21b86ecece681adf9584733efbf846a5 = private unnamed_addr constant [33 x i8] c"`addr` + `bytes_len` > usize::MAX", align 1
@alloc_a8b9d51f4716b1abea4342af19a187da = private unnamed_addr constant <{ ptr, [8 x i8] }> <{ ptr @alloc_21b86ecece681adf9584733efbf846a5, [8 x i8] c"!\00\00\00\00\00\00\00" }>, align 8
@alloc_541d4452affef989fd65692928d2720e = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00\9E\06\00\00\09\00\00\00" }>, align 8
@alloc_5682d82eaed587cd5c5b8bab05d565ca = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00\BB\06\00\00\10\00\00\00" }>, align 8
@alloc_9b1bb719df70d519086fef1cda697ad0 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00\E6\06\00\00$\00\00\00" }>, align 8
@alloc_d570cd8297926e8621ddfb6b2b8e2ad9 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00\EB\06\00\00\15\00\00\00" }>, align 8
@alloc_4cab74535d2ec5c8285921dd4499d52e = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00\F2\06\00\007\00\00\00" }>, align 8
@alloc_69f87fd79a0e8bc360cd9fab3ffbc279 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00\F2\06\00\00\22\00\00\00" }>, align 8
@alloc_a6bf1f98997d43151aae6dc674dd1f22 = private unnamed_addr constant [112 x i8] c"assertion failed: {\0A    #[allow(clippy :: arithmetic_side_effects)]\0A    let e = self_bytes <= bytes_len;\0A    e\0A}", align 1
@alloc_ba9ffb706a6ca16eea68370d5abffdfd = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00\F7\06\00\00\09\00\00\00" }>, align 8
@alloc_c9ffeeb1c1cfce728d4707955a20fda1 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4515a21d4dc9b36f89435de9319bc84f, [16 x i8] c"%\00\00\00\00\00\00\00\01\07\00\00!\00\00\00" }>, align 8
@alloc_a62461c94be6605d87e7ee7452ee7ab3 = private unnamed_addr constant [42 x i8] c"/e46/upstream/zerocopy/src/pointer/ptr.rs\00", align 1
@alloc_43af08c406911e254d158ce900b82413 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_a62461c94be6605d87e7ee7452ee7ab3, [16 x i8] c"*\00\00\00\00\00\00\00{\04\00\00&\00\00\00" }>, align 8
@alloc_01e5371d744a42d42be22970a5f671a1 = private unnamed_addr constant [44 x i8] c"/e46/upstream/zerocopy/src/pointer/inner.rs\00", align 1
@alloc_eb9b175a6329995b4605c01e089f69ea = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_01e5371d744a42d42be22970a5f671a1, [16 x i8] c",\00\00\00\00\00\00\00_\01\00\00$\00\00\00" }>, align 8
@alloc_2b3b8bf8575d7b890532fae13f928a4a = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_01e5371d744a42d42be22970a5f671a1, [16 x i8] c",\00\00\00\00\00\00\00d\01\00\00\1E\00\00\00" }>, align 8
@alloc_7df927a12c94620fa0c9f4ff08fe1b25 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_01e5371d744a42d42be22970a5f671a1, [16 x i8] c",\00\00\00\00\00\00\00\C9\00\00\00+\00\00\00" }>, align 8
@alloc_c534ab00c8a6da77c9ac3e7f01a7c346 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_01e5371d744a42d42be22970a5f671a1, [16 x i8] c",\00\00\00\00\00\00\00\93\01\00\00\22\00\00\00" }>, align 8
@alloc_009fcd67ec40494897136844fb2e9cf2 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_01e5371d744a42d42be22970a5f671a1, [16 x i8] c",\00\00\00\00\00\00\00\98\01\00\00&\00\00\00" }>, align 8
@alloc_7655f6ef89bcdccd0e255f36da05e01b = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_01e5371d744a42d42be22970a5f671a1, [16 x i8] c",\00\00\00\00\00\00\00\9F\01\00\00\1C\00\00\00" }>, align 8
@alloc_40dff3eabad1c181051df07dd4c6a834 = private unnamed_addr constant [34 x i8] c"/e46/upstream/zerocopy/src/lib.rs\00", align 1
@alloc_a4fa2aa40384d33bcd146a1f883fbfac = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_40dff3eabad1c181051df07dd4c6a834, [16 x i8] c"\22\00\00\00\00\00\00\00L\15\00\00\1A\00\00\00" }>, align 8
@alloc_47681e2ae4251711b9fba137fe3c184f = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_40dff3eabad1c181051df07dd4c6a834, [16 x i8] c"\22\00\00\00\00\00\00\00\88\17\00\00\12\00\00\00" }>, align 8
@_ZN14extended_pilot12HELPER_CALLS17hceaaa1dfa217d7abE = internal global [8 x i8] zeroinitializer, align 8
@alloc_9d2f10b99692de8b0347ccb8b850521d = private unnamed_addr constant [9 x i8] c"pilot.rs\00", align 1
@alloc_9582a9046867ff233d22477abdba1e19 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00N\00\00\00\0D\00\00\00" }>, align 8
@alloc_3593e8f28b974255b321f2f902d146b2 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00Z\00\00\00\0D\00\00\00" }>, align 8
@alloc_237662a0f6470bc7d494d03469948f8d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00d\00\00\00=\00\00\00" }>, align 8
@alloc_f2c8a29a7418eb1a2322d9e36eba085f = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00m\00\00\00\1D\00\00\00" }>, align 8
@alloc_45b90ed248e7cd080a07bdc6e70dd3a1 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00m\00\00\00/\00\00\00" }>, align 8
@alloc_21df5683520d569a1eb51be289b6cea3 = private unnamed_addr constant [16 x i8] c"\A5\A5\A5\A5\A5\A5\A5\A5\A5\A5\A5\A5\A5\A5\A5\A5", align 1
@alloc_2262ac44f76923e65696c0dac3b1908c = private unnamed_addr constant [16 x i8] c"ZZZZZZZZZZZZZZZZ", align 1
@alloc_8201ddbf69297838cdcfbcf366c93eb4 = private unnamed_addr constant [13 x i8] c"exact8 source", align 1
@alloc_174ca6095dd798f3bae55190774d0abd = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\D2\00\00\00.\00\00\00" }>, align 8
@alloc_561d3d4073b7782336f3422149c0c11e = private unnamed_addr constant [18 x i8] c"exact8 destination", align 1
@alloc_e663c9224e057f8bb5f411b30ae6c7c8 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\D8\00\00\00\1A\00\00\00" }>, align 8
@alloc_5dee763f4f60d547e9365f94454ebd3a = private unnamed_addr constant [14 x i8] c"exact16 source", align 1
@alloc_6abd98a2cd140a8e8b20b1b8921e0cf0 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\DC\00\00\004\00\00\00" }>, align 8
@alloc_c4acb29d339694a0db93fd511b0aa138 = private unnamed_addr constant [19 x i8] c"exact16 destination", align 1
@alloc_5b1f55ab60e406fbd3eb1e254aed020b = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\DD\00\00\00\18\00\00\00" }>, align 8
@alloc_808ad300ebb34afb9eceb74f85f1e6d3 = private unnamed_addr constant [18 x i8] c"E46_MISMATCH case=", align 1
@alloc_2a9ce5f334b088ccf931185f4c3818c5 = private unnamed_addr constant [7 x i8] c" check=", align 1
@alloc_49a1e817e911805af64bbc7efb390101 = private unnamed_addr constant [1 x i8] c"\0A", align 1
@alloc_81515a03d1756c347036b25cb9acf81a = private unnamed_addr constant <{ ptr, [8 x i8], ptr, [8 x i8], ptr, [8 x i8] }> <{ ptr @alloc_808ad300ebb34afb9eceb74f85f1e6d3, [8 x i8] c"\12\00\00\00\00\00\00\00", ptr @alloc_2a9ce5f334b088ccf931185f4c3818c5, [8 x i8] c"\07\00\00\00\00\00\00\00", ptr @alloc_49a1e817e911805af64bbc7efb390101, [8 x i8] c"\01\00\00\00\00\00\00\00" }>, align 8
@alloc_87b55dc4e757b81e4ee925b5b00b364d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\E5\00\00\00\05\00\00\00" }>, align 8
@alloc_e74c78967c49fe173e1453708be77ccf = private unnamed_addr constant [12 x i8] c"guard-layout", align 1
@anon.c68ad90a3a9dfb7a47f86997a7ce991b.3 = private unnamed_addr constant [9248 x i8] c"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00UUUUUUUUUUUUUUUU\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FE\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FE\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FE\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FC\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\DE\9BW\13\CF\8AF\02\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE d\A8\EC0u\B9\FD\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AATUUUUUUU\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00UUUUUUUU\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FE\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\FE\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\FF\FF\7F\7F\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\7F\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\FF\FF\FF\FE\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\FF\FF\FF\FF\FF\FF\7F\7F\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\7F\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\02\FE\FF\FF\FF\FF\FF\FF\FE\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\FF\FF\FF\FF\FF\FF\FF\FE\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\11!\22\22\22\22\22\22\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\F0\DD\DD\DD\DD\DD\DD\DD\FD\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AAV\FF\FF\FF\FF\FF\FF\FF\A9\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00UUUUUUUU\AB\FF\FF\FF\FF\FF\FF\FFT\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00UUUUUUUU\00UUUUUUUU\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\02\00\00\00\00\00\00\00\FE\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\00\00\00\00\00\00\00\01\FF\FF\7F\7F\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\FF\FF\FF?\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\FF\FF\FF?\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\80\FE\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\80\FF\FF\FF\7F\FF\FF\FF?\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\FF\FF\FF?\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\FF\FF\FF\FF\FE\FF\FF\7F\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\80\FF\FF\FF\FF\FE\FF\FF\7F\00\00\00\00\FF\FF\FF\7F\00\00\00\00\EF\CD\AB\89gE#\01\112T\F6\8F\A1\B2\C3\B3\A2\91\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\102Tv\98\BA\DC\FE\F0\CD\AB\89o^M<K]n\7F\00\00\00\00\FF\FF\FF\7F\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AAVUUU\AA\AA\AA\AATUUU\00\00\00\00\FF\FF\FF\7F\00\00\00\00UUUUUUUU\AB\AA\AA*UUUU\AA\AA\AA*\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\80\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\80\FF\FF\FF?\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00@\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\80\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\80\FF\FF\FF\FF\FF\FF\FF?\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00@\00\00\00\00\00\00\00\80\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\80\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\80\F7\E6\D5\C4\B3\A2\91\00\00\00\00\00\00\00\00\80\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\08\19*;L]n\7F\00\00\00\00\00\00\00\80\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\80\00\00\00\00UUUUUUUU\00\00\00\80\AA\AA\AA\AA\AA\AA\AA*\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\02\00\00\00\00\00\00\00\FE\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\00\00\00\00\00\00\00\01\FF\FF\FF\FE\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\80\FE\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\FE\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\FF\FF\FF\7F\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\FE\FF\FF\FF\FE\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\FF\FF\FF\FF\FE\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\00\00\00\00\EF\CD\AB\89gE#\01\112Tv\87\88\88\88gE#\01\00\00\00\00\FF\FF\FF\FF\00\00\00\00\102Tv\98\BA\DC\FE\F0\CD\AB\89wwww\97\BA\DC\FE\00\00\00\00\FF\FF\FF\FF\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AAVUUU\FF\FF\FF\FF\A9\AA\AA\AA\00\00\00\00\FF\FF\FF\FF\00\00\00\00UUUUUUUU\AB\AA\AA\AA\FF\FF\FF\FFTUUU\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\01\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\01\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\01\00\00\00UUUUUUUU\00\00\00\00UUUUUUUU\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\02\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\00\00\00\00\00\00\00\01\FF\FF\FF\FF\FF\FF\7F\7F\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\7F\00\00\00\00\01\00\00\80\FF\FF\FF\7F\FF\FF\FF?\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\80\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF?\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\00\00\00\00\01\00\00\00\FF\FF\FF\7F\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF?\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF?\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\80\FE\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\7F\EF\CD\AB\89gE#\01\112Tv\98\BA\DC~\F7\E6\D5\C4\B3\A2\91\00\FF\FF\FF\FF\FF\FF\FF\7F\102Tv\98\BA\DC\FE\F0\CD\AB\89gE#\01\07\19*;L]n\7F\FF\FF\FF\FF\FF\FF\FF\7F\AA\AA\AA\AA\AA\AA\AA\AAVUUUUUUUTUUUUUUU\FF\FF\FF\FF\FF\FF\FF\7FUUUUUUUU\AB\AA\AA\AA\AA\AA\AA*\AA\AA\AA\AA\AA\AA\AA*\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF?\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00@\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF?\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00@\00\00\00\00\00\00\00\80\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\80\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\80\F7\E6\D5\C4\B3\A2\91\00\00\00\00\00\00\00\00\80\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\08\19*;L]n\7F\00\00\00\00\00\00\00\80\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\80UUUUUUUU\00\00\00\00\00\00\00\80\AA\AA\AA\AA\AA\AA\AA*\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\FC\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\02\FE\FF\FF\FF\FF\FF\FF\FE\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\02\00\00\00\FF\FF\FF\FF\FE\FF\FF\7F\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\02\00\00\00\FE\FF\FF\FF\FE\FF\FF\FF\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\02\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\04\00\00\00\00\00\00\00\FC\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\FD\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\22d\A8\EC0u\B9\FD\EE\CD\AB\89gE#\01\FE\FF\FF\FF\FF\FF\FF\FF\102Tv\98\BA\DC\FE\E0\9BW\13\CF\8AF\02\0E2Tv\98\BA\DC\FE\FE\FF\FF\FF\FF\FF\FF\FF\AA\AA\AA\AA\AA\AA\AA\AA\AC\AA\AA\AA\AA\AA\AA\AA\A8\AA\AA\AA\AA\AA\AA\AA\FE\FF\FF\FF\FF\FF\FF\FFUUUUUUUUVUUUUUUUTUUUUUUU\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\01\FF\FF\FF\FF\FF\FF\FF\FE\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\01\00\00\80\FF\FF\FF\FF\FE\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\FF\FF\FF\FF\FE\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\80\FE\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\FD\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\112Tv\98\BA\DC\FE\EE\CD\AB\89gE#\01\FF\FF\FF\FF\FF\FF\FF\FF\102Tv\98\BA\DC\FE\F0\CD\AB\89gE#\01\0F2Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\FF\AA\AA\AA\AA\AA\AA\AA\AAVUUUUUUU\A9\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\FF\FF\FF\FFUUUUUUUU\AB\AA\AA\AA\AA\AA\AA\AATUUUUUUU\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\02\00\00\00\00\00\00\00\DE\9BW\13\CF\8AF\02\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\00\00\00\00\00\00\00\11!\22\22\22\22\22\22\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\7F\00\00\00\00\112T\F6\8F\A1\B2\C3\B3\A2\91\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\80\00\00\00\00\00\00\00\80\F7\E6\D5\C4\B3\A2\91\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\FF\00\00\00\00\112Tv\87\88\88\88gE#\01\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\FF\FF\FF\FF\7F\112Tv\98\BA\DC~\F7\E6\D5\C4\B3\A2\91\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\F7\E6\D5\C4\B3\A2\91\00\EF\CD\AB\89gE#\01\FE\FF\FF\FF\FF\FF\FF\FF\22d\A8\EC0u\B9\FD\EE\CD\AB\89gE#\01\EF\CD\AB\89gE#\01\FF\FF\FF\FF\FF\FF\FF\FF\112Tv\98\BA\DC\FE\EE\CD\AB\89gE#\01\EF\CD\AB\89gE#\01\EF\CD\AB\89gE#\01!\A5\F2\90\08\E2\A5\DC\AC\F63\DCfK\01\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\F0\8Ca\E5\8F\D86\22B\D7w\AD\00\FA!\01\EF\CD\AB\89gE#\01\AA\AA\AA\AA\AA\AA\AA\AA\B6v\8D\F9\BA\D1=\FFI\89r\06E.\C2\00\EF\CD\AB\89gE#\01UUUUUUUU[\BB\C6|\DD\E8\9E\FF\A4D9\83\22\17a\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\02\00\00\00\00\00\00\00 d\A8\EC0u\B9\FD\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\00\00\00\00\00\00\00\F0\DD\DD\DD\DD\DD\DD\DD\FD\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\7F\00\00\00\00\F0\CD\AB\89o^M<K]n\7F\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\80\00\00\00\00\00\00\00\00\08\19*;L]n\7F\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\FF\00\00\00\00\F0\CD\AB\89wwww\97\BA\DC\FE\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\7F\F0\CD\AB\89gE#\01\07\19*;L]n\7F\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\08\19*;L]n\7F\102Tv\98\BA\DC\FE\FE\FF\FF\FF\FF\FF\FF\FF\E0\9BW\13\CF\8AF\02\0E2Tv\98\BA\DC\FE\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\FF\F0\CD\AB\89gE#\01\0F2Tv\98\BA\DC\FE\102Tv\98\BA\DC\FE\EF\CD\AB\89gE#\01\F0\8Ca\E5\8F\D86\22B\D7w\AD\00\FA!\01\102Tv\98\BA\DC\FE\102Tv\98\BA\DC\FE\00AJ\A4\D7l\EC\DE\CCZ\DC\C8\97\C0\BA\FD\102Tv\98\BA\DC\FE\AA\AA\AA\AA\AA\AA\AA\AA\A0\DE\C7[\9A\83\17V_!8\A4e|\E8\A9\102Tv\98\BA\DC\FEUUUUUUUUP\EF\E3-\CD\C1\0B\AB\AF\10\1C\D22>\F4T\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\02\00\00\00\00\00\00\00TUUUUUUU\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\00\00\00\00\00\00\00V\FF\FF\FF\FF\FF\FF\FF\A9\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\7F\00\00\00\00VUUU\AA\AA\AA\AATUUU\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\80\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\00\00\00\00VUUU\FF\FF\FF\FF\A9\AA\AA\AA\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\FF\FF\FF\7FVUUUUUUUTUUUUUUU\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00UUUUUUUU\AA\AA\AA\AA\AA\AA\AA\AA\FE\FF\FF\FF\FF\FF\FF\FF\AC\AA\AA\AA\AA\AA\AA\AA\A8\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\FF\FF\FF\FFVUUUUUUU\A9\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\EF\CD\AB\89gE#\01\B6v\8D\F9\BA\D1=\FFI\89r\06E.\C2\00\AA\AA\AA\AA\AA\AA\AA\AA\102Tv\98\BA\DC\FE\A0\DE\C7[\9A\83\17V_!8\A4e|\E8\A9\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\E48\8E\E38\8E\E38\C6q\1C\C7q\1C\C7q\AA\AA\AA\AA\AA\AA\AA\AAUUUUUUUUr\1C\C7q\1C\C7q\1C\E38\8E\E38\8E\E38UUUUUUUU\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\02\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00UUUUUUUU\FF\00\00\00\00\00\00\00\AB\FF\FF\FF\FF\FF\FF\FFT\00\00\00\00\00\00\00UUUUUUUU\00\01\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00UUUUUUUU\FF\FF\FF\7F\00\00\00\00\AB\AA\AA*UUUU\AA\AA\AA*\00\00\00\00UUUUUUUU\00\00\00\80\00\00\00\00\00\00\00\80\AA\AA\AA\AA\AA\AA\AA*\00\00\00\00UUUUUUUU\FF\FF\FF\FF\00\00\00\00\AB\AA\AA\AA\FF\FF\FF\FFTUUU\00\00\00\00UUUUUUUU\00\00\00\00\01\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00UUUUUUUU\FF\FF\FF\FF\FF\FF\FF\7F\AB\AA\AA\AA\AA\AA\AA*\AA\AA\AA\AA\AA\AA\AA*UUUUUUUU\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\AA\AA\AA\AA\AA\AA\AA*UUUUUUUU\FE\FF\FF\FF\FF\FF\FF\FFVUUUUUUUTUUUUUUUUUUUUUUU\FF\FF\FF\FF\FF\FF\FF\FF\AB\AA\AA\AA\AA\AA\AA\AATUUUUUUUUUUUUUUU\EF\CD\AB\89gE#\01[\BB\C6|\DD\E8\9E\FF\A4D9\83\22\17a\00UUUUUUUU\102Tv\98\BA\DC\FEP\EF\E3-\CD\C1\0B\AB\AF\10\1C\D22>\F4TUUUUUUUU\AA\AA\AA\AA\AA\AA\AA\AAr\1C\C7q\1C\C7q\1C\E38\8E\E38\8E\E38UUUUUUUUUUUUUUUU9\8E\E38\8E\E38\8Eq\1C\C7q\1C\C7q\1C", align 8
@anon.c68ad90a3a9dfb7a47f86997a7ce991b.4 = private unnamed_addr constant [8064 x i8] c"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\F0\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FD\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\EE\CD\AB\89gE#\01\112Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\EF\CD\AB\89gE#\01\112Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FD\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\EE\CD\AB\89gE#\01\122Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\EF\CD\AB\89gE#\01\0F2Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FD\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\EE\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FD\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FD\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FD\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FC\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FD\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\ED\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\F0\CD\AB\89gE#\01\0F2Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\EF\CD\AB\89gE#\01\102Tv\98\BA\DC~\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FD\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\EE\CD\AB\89gE#\01\102Tv\98\BA\DC~\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\F0\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\EE\CD\AB\89gE#\01\112Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\112Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\EE\CD\AB\89gE#\01\122Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\0F2Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\EE\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\ED\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\F0\CD\AB\89gE#\01\0F2Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\EF\CD\AB\89gE#\01\102Tv\98\BA\DC~\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\EE\CD\AB\89gE#\01\102Tv\98\BA\DC~\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\DE\9BW\13\CF\8AF\02 d\A8\EC0u\B9\FD\01\00\00\00\00\00\00\00", align 8
@anon.c68ad90a3a9dfb7a47f86997a7ce991b.5 = private unnamed_addr constant [23120 x i8] c"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\F0\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\112Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AB\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00VUUUUUUU\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\F0\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\F1\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\112Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\122Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AB\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AC\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00VUUUUUUU\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00WUUUUUUU\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\03\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\03\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\03\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\03\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\F1\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\F2\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\122Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\132Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AC\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AD\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00WUUUUUUU\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00XUUUUUUU\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FE\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FE\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FE\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FD\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EE\CE\AB\89gE#\01\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EF\CE\AB\89gE#\01\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\0F3Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\103Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\A9\AB\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AA\AB\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00TVUUUUUU\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00UVUUUUUU\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\03\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\01\01\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\01\01\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\01\01\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CE\AB\89gE#\01\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\F0\CE\AB\89gE#\01\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\103Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\113Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AB\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AB\AB\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00UVUUUUUU\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00VVUUUUUU\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FE\FF\FF\7F\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FD\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EE\CD\AB\09hE#\01\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EF\CD\AB\09hE#\01\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\0F2T\F6\98\BA\DC\FE\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\102T\F6\98\BA\DC\FE\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\A9\AA\AA*\AB\AA\AA\AA\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AA\AA\AA*\AB\AA\AA\AA\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00TUU\D5UUUU\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00UUU\D5UUUU\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\03\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\01\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\01\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\01\00\00\80\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\09hE#\01\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\F0\CD\AB\09hE#\01\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102T\F6\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\112T\F6\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA*\AB\AA\AA\AA\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AB\AA\AA*\AB\AA\AA\AA\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00UUU\D5UUUU\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00VUU\D5UUUU\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FE\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FD\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EE\CD\AB\89hE#\01\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EF\CD\AB\89hE#\01\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\0F2Tv\99\BA\DC\FE\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\102Tv\99\BA\DC\FE\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\A9\AA\AA\AA\AB\AA\AA\AA\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AB\AA\AA\AA\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00TUUUVUUU\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00UUUUVUUU\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\03\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\01\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\01\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89hE#\01\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\F0\CD\AB\89hE#\01\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\99\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\112Tv\99\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AB\AA\AA\AA\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AB\AA\AA\AA\AB\AA\AA\AA\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00UUUUVUUU\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00VUUUVUUU\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\7F\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FD\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EE\CD\AB\89gE#\81\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\81\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\0F2Tv\98\BA\DC~\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\102Tv\98\BA\DC~\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\A9\AA\AA\AA\AA\AA\AA*\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA*\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7FUUUUUUUU\00\00\00\00\00\00\00\00TUUUUUU\D5\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7FUUUUUUUU\01\00\00\00\00\00\00\00UUUUUUU\D5\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\03\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\01\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\80\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\01\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\81\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\F0\CD\AB\89gE#\81\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC~\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\112Tv\98\BA\DC~\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA*\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AB\AA\AA\AA\AA\AA\AA*\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80UUUUUUUU\00\00\00\00\00\00\00\00UUUUUUU\D5\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80UUUUUUUU\01\00\00\00\00\00\00\00VUUUUUU\D5\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FD\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FD\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FD\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FD\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FC\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FD\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FD\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\ED\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EE\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\0E2Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\0F2Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\A8\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\A9\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FFUUUUUUUU\00\00\00\00\00\00\00\00SUUUUUUU\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FFUUUUUUUU\01\00\00\00\00\00\00\00TUUUUUUU\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FE\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\FE\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FD\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EE\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\0F2Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\A9\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFUUUUUUUU\00\00\00\00\00\00\00\00TUUUUUUU\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFUUUUUUUU\01\00\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\F0\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\F0\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\F1\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\F1\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\F2\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\EE\CE\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\EF\CE\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\EF\CE\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\F0\CE\AB\89gE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\EE\CD\AB\09hE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\EF\CD\AB\09hE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\EF\CD\AB\09hE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\F0\CD\AB\09hE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\EE\CD\AB\89hE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\EF\CD\AB\89hE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\EF\CD\AB\89hE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\F0\CD\AB\89hE#\01\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\EE\CD\AB\89gE#\81\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\81\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\81\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\F0\CD\AB\89gE#\81\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\ED\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\EE\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\EE\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\DE\9BW\13\CF\8AF\02\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\DF\9BW\13\CF\8AF\02\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\99xV4\12\F0\CD\AB\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\9AxV4\12\F0\CD\AB\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01UUUUUUUU\00\00\00\00\00\00\00\00D#\01\DF\BC\9AxV\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01UUUUUUUU\01\00\00\00\00\00\00\00E#\01\DF\BC\9AxV\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\112Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\112Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\122Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\122Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\132Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\0F3Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\103Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\103Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\113Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\0F2T\F6\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\102T\F6\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\102T\F6\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\112T\F6\98\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\0F2Tv\99\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\102Tv\99\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\102Tv\99\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\112Tv\99\BA\DC\FE\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\0F2Tv\98\BA\DC~\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\102Tv\98\BA\DC~\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\102Tv\98\BA\DC~\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\112Tv\98\BA\DC~\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\0E2Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\0F2Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\0F2Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00 d\A8\EC0u\B9\FD\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00!d\A8\EC0u\B9\FD\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\BA\DC\FE Ce\87\A9\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FE\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\BB\DC\FE Ce\87\A9\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FEUUUUUUUU\00\00\00\00\00\00\00\00e\87\A9\CB\ED\0F2T\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FEUUUUUUUU\01\00\00\00\00\00\00\00f\87\A9\CB\ED\0F2T\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\AB\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\AB\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\AC\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\AC\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\AD\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\A9\AB\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\AA\AB\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\AA\AB\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\AB\AB\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\A9\AA\AA*\AB\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\AA\AA\AA*\AB\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\AA\AA\AA*\AB\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\AB\AA\AA*\AB\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\A9\AA\AA\AA\AB\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AB\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AB\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\AB\AA\AA\AA\AB\AA\AA\AA\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\A9\AA\AA\AA\AA\AA\AA*\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA*\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA*\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\AB\AA\AA\AA\AA\AA\AA*\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\A8\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\A9\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\A9\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00\99xV4\12\F0\CD\AB\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\9AxV4\12\F0\CD\AB\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\BA\DC\FE Ce\87\A9\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00\BB\DC\FE Ce\87\A9\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00TUUUUUUU\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AAUUUUUUUU\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AAUUUUUUUU\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00VUUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00VUUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00WUUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00WUUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00XUUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00TVUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00UVUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00UVUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00VVUUUUUU\00\00\00\00\00\00\00\00UUUUUUUU\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00TUU\D5UUUU\00\00\00\00\00\00\00\00UUUUUUUU\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00UUU\D5UUUU\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00UUU\D5UUUU\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00VUU\D5UUUU\00\00\00\00\00\00\00\00UUUUUUUU\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00TUUUVUUU\00\00\00\00\00\00\00\00UUUUUUUU\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00UUUUVUUU\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00UUUUVUUU\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00VUUUVUUU\00\00\00\00\00\00\00\00UUUUUUUU\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00TUUUUUU\D5\00\00\00\00\00\00\00\00UUUUUUUU\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00UUUUUUU\D5\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00UUUUUUU\D5\00\00\00\00\00\00\00\00UUUUUUUU\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00VUUUUUU\D5\00\00\00\00\00\00\00\00UUUUUUUU\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00SUUUUUUU\01\00\00\00\00\00\00\00UUUUUUUU\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00TUUUUUUU\01\00\00\00\00\00\00\00UUUUUUUU\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00TUUUUUUU\01\00\00\00\00\00\00\00UUUUUUUU\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00UUUUUUUU\01\00\00\00\00\00\00\00UUUUUUUU\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00D#\01\DF\BC\9AxV\00\00\00\00\00\00\00\00UUUUUUUU\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00E#\01\DF\BC\9AxV\00\00\00\00\00\00\00\00UUUUUUUU\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00e\87\A9\CB\ED\0F2T\01\00\00\00\00\00\00\00UUUUUUUU\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00f\87\A9\CB\ED\0F2T\01\00\00\00\00\00\00\00UUUUUUUU\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00UUUUUUUU\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00UUUUUUUUUUUUUUUU\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00UUUUUUUUUUUUUUUU\01\00\00\00\00\00\00\00\AB\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00", align 8
@anon.c68ad90a3a9dfb7a47f86997a7ce991b.6 = private unnamed_addr constant [272 x i8] c"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\02\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\01\00\00\00\00\00\00\00\00\00\00\00\00\01\00\FF\FF\FF\7F\00\00\00\00\00\00\00\00\7F\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\00\80\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\7F\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\80\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\01#Eg\89\AB\CD\EF\102Tv\98\BA\DC\FE\FE\DC\BA\98vT2\10\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AAUUUUUUUUUUUUUUUU", align 8
@anon.c68ad90a3a9dfb7a47f86997a7ce991b.7 = private unnamed_addr constant [136 x i8] c"\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00\00\00\00\80\00\00\00\00\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\80\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FE\AA\AA\AA\AA\AA\AA\AA\AAUUUUUUUU", align 8
@alloc_df49633132bd0738f71b84ee1e58fda5 = private unnamed_addr constant [192 x i8] c"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F\0F\0E\0D\0C\0B\0A\09\08\07\06\05\04\03\02\01\00\80\80\80\80\80\80\80\80\80\80\80\80\80\80\80\80\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AAUUUUUUUUUUUUUUUU\00\FF\00\FF\00\FF\00\FF\00\FF\00\FF\00\FF\00\FF\01\02\04\08\10 @\80\01\02\04\08\10 @\80\13\\\A5\EE7\80\C9\12[\A4\ED6\7F\C8\11Zwire-header-0016", align 1
@anon.c68ad90a3a9dfb7a47f86997a7ce991b.8 = private unnamed_addr constant [4608 x i8] c"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F\00\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\0F\0E\0D\0C\0B\0A\09\08\07\06\05\04\03\02\01\00\00\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\80\80\80\80\80\80\80\80\80\80\80\80\80\80\80\80\00\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\00\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00UUUUUUUUUUUUUUUU\00\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\00\FF\00\FF\00\FF\00\FF\00\FF\00\FF\00\FF\00\FF\00\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\01\02\04\08\10 @\80\01\02\04\08\10 @\80\00\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\13\\\A5\EE7\80\C9\12[\A4\ED6\7F\C8\11Z\00\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00wire-header-0016\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\FF\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\01\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\0E\0D\0C\0B\0A\09\08\07\06\05\04\03\02\01\00\FF\01\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\01\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00~~~~~~~~~~~~~~~~\01\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\01\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00TTTTTTTTTTTTTTTT\01\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\FF\FE\FF\FE\FF\FE\FF\FE\FF\FE\FF\FE\FF\FE\FF\FE\01\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\00\01\03\07\0F\1F?\7F\00\01\03\07\0F\1F?\7F\01\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\12[\A4\ED6\7F\C8\11Z\A3\EC5~\C7\10Y\01\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00vhqd,gd`cdq,//05\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\02\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\02\04\06\08\0A\0C\0E\10\12\14\16\18\1A\1C\1E\02\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\02\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\80\81\82\83\84\85\86\87\88\89\8A\8B\8C\8D\8E\8F\02\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\7F\80\81\82\83\84\85\86\87\88\89\8A\8B\8C\8D\8E\02\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\AA\AB\AC\AD\AE\AF\B0\B1\B2\B3\B4\B5\B6\B7\B8\B9\02\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00UVWXYZ[\\]^_`abcd\02\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\00\00\02\02\04\04\06\06\08\08\0A\0A\0C\0C\0E\0E\02\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\01\03\06\0B\14%F\87\09\0B\0E\13\1C-N\8F\02\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\13]\A7\F1;\85\CF\19c\AD\F7A\8B\D5\1Fi\02\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00wjth1mkhln|8<=?E\03\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\0F\0E\0D\0C\0B\0A\09\08\07\06\05\04\03\02\01\00\03\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\0E\0D\0C\0B\0A\09\08\07\06\05\04\03\02\01\00\FF\03\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\0F\03\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\1E\1C\1A\18\16\14\12\10\0E\0C\0A\08\06\04\02\00\03\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\8F\8E\8D\8C\8B\8A\89\88\87\86\85\84\83\82\81\80\03\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\8E\8D\8C\8B\8A\89\88\87\86\85\84\83\82\81\80\7F\03\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\B9\B8\B7\B6\B5\B4\B3\B2\B1\B0\AF\AE\AD\AC\AB\AA\03\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00dcba`_^]\\[ZYXWVU\03\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\0F\0D\0D\0B\0B\09\09\07\07\05\05\03\03\01\01\FF\03\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\10\10\11\14\1B*I\88\08\08\09\0C\13\22A\80\03\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\22j\B2\FAB\8A\D2\1Ab\AA\F2:\82\CA\12Z\03\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\86w\7Fq8rnikkw13226\04\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\80\80\80\80\80\80\80\80\80\80\80\80\80\80\80\04\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\04\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\80\81\82\83\84\85\86\87\88\89\8A\8B\8C\8D\8E\8F\04\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\8F\8E\8D\8C\8B\8A\89\88\87\86\85\84\83\82\81\80\04\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\04\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00****************\04\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\04\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\80\7F\80\7F\80\7F\80\7F\80\7F\80\7F\80\7F\80\7F\04\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\81\82\84\88\90\A0\C0\00\81\82\84\88\90\A0\C0\00\04\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\93\DC%n\B7\00I\92\DB$m\B6\FFH\91\DA\04\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\F7\E9\F2\E5\AD\E8\E5\E1\E4\E5\F2\AD\B0\B0\B1\B6\05\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\7F\05\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00~~~~~~~~~~~~~~~~\05\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\7F\80\81\82\83\84\85\86\87\88\89\8A\8B\8C\8D\8E\05\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\8E\8D\8C\8B\8A\89\88\87\86\85\84\83\82\81\80\7F\05\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\05\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\FE\05\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00))))))))))))))))\05\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\05\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\7F~\7F~\7F~\7F~\7F~\7F~\7F~\7F~\05\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\80\81\83\87\8F\9F\BF\FF\80\81\83\87\8F\9F\BF\FF\05\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\92\DB$m\B6\FFH\91\DA#l\B5\FEG\90\D9\05\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\F6\E8\F1\E4\AC\E7\E4\E0\E3\E4\F1\AC\AF\AF\B0\B5\06\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\06\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\A9\06\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\AA\AB\AC\AD\AE\AF\B0\B1\B2\B3\B4\B5\B6\B7\B8\B9\06\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\B9\B8\B7\B6\B5\B4\B3\B2\B1\B0\AF\AE\AD\AC\AB\AA\06\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00****************\06\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00))))))))))))))))\06\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00TTTTTTTTTTTTTTTT\06\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\06\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\AA\A9\AA\A9\AA\A9\AA\A9\AA\A9\AA\A9\AA\A9\AA\A9\06\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\AB\AC\AE\B2\BA\CA\EA*\AB\AC\AE\B2\BA\CA\EA*\06\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\BD\06O\98\E1*s\BC\05N\97\E0)r\BB\04\06\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00!\13\1C\0F\D7\12\0F\0B\0E\0F\1C\D7\DA\DA\DB\E0\07\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00UUUUUUUUUUUUUUUU\07\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00TTTTTTTTTTTTTTTT\07\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00UVWXYZ[\\]^_`abcd\07\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00dcba`_^]\\[ZYXWVU\07\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\D5\07\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\D4\07\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\07\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\07\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00UTUTUTUTUTUTUTUT\07\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00VWY]eu\95\D5VWY]eu\95\D5\07\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00h\B1\FAC\8C\D5\1Eg\B0\F9B\8B\D4\1Df\AF\07\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\CC\BE\C7\BA\82\BD\BA\B6\B9\BA\C7\82\85\85\86\8B\08\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\00\FF\00\FF\00\FF\00\FF\00\FF\00\FF\00\FF\08\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\FF\FE\FF\FE\FF\FE\FF\FE\FF\FE\FF\FE\FF\FE\FF\FE\08\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\00\00\02\02\04\04\06\06\08\08\0A\0A\0C\0C\0E\0E\08\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\0F\0D\0D\0B\0B\09\09\07\07\05\05\03\03\01\01\FF\08\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\80\7F\80\7F\80\7F\80\7F\80\7F\80\7F\80\7F\80\7F\08\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\7F~\7F~\7F~\7F~\7F~\7F~\7F~\7F~\08\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\AA\A9\AA\A9\AA\A9\AA\A9\AA\A9\AA\A9\AA\A9\AA\A9\08\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00UTUTUTUTUTUTUTUT\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\00\FE\00\FE\00\FE\00\FE\00\FE\00\FE\00\FE\00\FE\08\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\01\01\04\07\10\1F@\7F\01\01\04\07\10\1F@\7F\08\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\13[\A5\ED7\7F\C9\11[\A3\ED5\7F\C7\11Y\08\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00whrd-ge`ddr,0/15\09\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\02\04\08\10 @\80\01\02\04\08\10 @\80\09\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\01\03\07\0F\1F?\7F\00\01\03\07\0F\1F?\7F\09\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\03\06\0B\14%F\87\09\0B\0E\13\1C-N\8F\09\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\10\10\11\14\1B*I\88\08\08\09\0C\13\22A\80\09\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\81\82\84\88\90\A0\C0\00\81\82\84\88\90\A0\C0\00\09\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\80\81\83\87\8F\9F\BF\FF\80\81\83\87\8F\9F\BF\FF\09\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\AB\AC\AE\B2\BA\CA\EA*\AB\AC\AE\B2\BA\CA\EA*\09\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00VWY]eu\95\D5VWY]eu\95\D5\09\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\01\01\04\07\10\1F@\7F\01\01\04\07\10\1F@\7F\09\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\02\04\08\10 @\80\00\02\04\08\10 @\80\00\09\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\14^\A9\F6G\A0\09\92\\\A6\F1>\8F\E8Q\DA\09\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00xkvm=\88\A5\E1egv5@Pq\B6\0A\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\13\\\A5\EE7\80\C9\12[\A4\ED6\7F\C8\11Z\0A\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\12[\A4\ED6\7F\C8\11Z\A3\EC5~\C7\10Y\0A\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\13]\A7\F1;\85\CF\19c\AD\F7A\8B\D5\1Fi\0A\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\22j\B2\FAB\8A\D2\1Ab\AA\F2:\82\CA\12Z\0A\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\93\DC%n\B7\00I\92\DB$m\B6\FFH\91\DA\0A\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\92\DB$m\B6\FFH\91\DA#l\B5\FEG\90\D9\0A\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00\BD\06O\98\E1*s\BC\05N\97\E0)r\BB\04\0A\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00h\B1\FAC\8C\D5\1Eg\B0\F9B\8B\D4\1Df\AF\0A\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\13[\A5\ED7\7F\C9\11[\A3\ED5\7F\C7\11Y\0A\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00\14^\A9\F6G\A0\09\92\\\A6\F1>\8F\E8Q\DA\0A\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00&\B8J\DCn\00\92$\B6H\DAl\FE\90\22\B4\0A\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\8A\C5\17Sd\E8.s\BF\09_c\AF\F8B\90\0B\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00wire-header-0016\0B\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00vhqd,gd`cdq,//05\0B\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00wjth1mkhln|8<=?E\0B\00\00\00\00\00\00\00\03\00\00\00\00\00\00\00\86w\7Fq8rnikkw13226\0B\00\00\00\00\00\00\00\04\00\00\00\00\00\00\00\F7\E9\F2\E5\AD\E8\E5\E1\E4\E5\F2\AD\B0\B0\B1\B6\0B\00\00\00\00\00\00\00\05\00\00\00\00\00\00\00\F6\E8\F1\E4\AC\E7\E4\E0\E3\E4\F1\AC\AF\AF\B0\B5\0B\00\00\00\00\00\00\00\06\00\00\00\00\00\00\00!\13\1C\0F\D7\12\0F\0B\0E\0F\1C\D7\DA\DA\DB\E0\0B\00\00\00\00\00\00\00\07\00\00\00\00\00\00\00\CC\BE\C7\BA\82\BD\BA\B6\B9\BA\C7\82\85\85\86\8B\0B\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00whrd-ge`ddr,0/15\0B\00\00\00\00\00\00\00\09\00\00\00\00\00\00\00xkvm=\88\A5\E1egv5@Pq\B6\0B\00\00\00\00\00\00\00\0A\00\00\00\00\00\00\00\8A\C5\17Sd\E8.s\BF\09_c\AF\F8B\90\0B\00\00\00\00\00\00\00\0B\00\00\00\00\00\00\00\EE\D2\E4\CAZ\D0\CA\C2\C8\CA\E4Z``bl", align 8
@anon.c68ad90a3a9dfb7a47f86997a7ce991b.9 = private unnamed_addr constant [6936 x i8] c"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\88\CA\EB\85\B1y7\9E\00\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\0F\95\D7\0Bc\F3n<\00\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00z\BC\DEe\D47B\99\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\87\CA\EB\85\B1y7\00\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00z5\14\FA\91k\BE$\00\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\80C\E5\F5\C2\00\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00z5\14z\D5P\B4\E7\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\87\CA\EB\85\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7Fz5\14zN\86\C8\E1\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\F3j(\F4\9C\0C\91\C3\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFz5\14zN\86\C8a\00\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\0A/}_-Hg\13\00\00\00\00\00\00\00\00\102Tv\98\BA\DC\FEq\06\97\1A!>aN\00\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\A7#\B8\A6\89Y0A\00\00\00\00\00\00\00\00UUUUUUUU\D4\11\\\D3\C4,\98 \01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01 \00\00\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\88\EA\EB\85\B1y7\9E\01\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\0F\B5\D7\0Bc\F3n<\01\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00z\9C\DEe\D47B\99\01\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\A7\CA\EB\85\B1y7\01\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00z\15\14\FA\91k\BE$\01\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01 \00\80C\E5\F5\C2\01\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00z\15\14z\D5P\B4\E7\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01 \00\00\87\CA\EB\85\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7Fz\15\14zN\86\C8\E1\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01 \00\00\00\00\00\80\01\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\F3J(\F4\9C\0C\91\C3\01\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFz\15\14zN\86\C8a\01\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\0A\0F}_-Hg\13\01\00\00\00\00\00\00\00\102Tv\98\BA\DC\FEq&\97\1A!>aN\01\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\A7\03\B8\A6\89Y0A\01\00\00\00\00\00\00\00UUUUUUUU\D41\\\D3\C4,\98 \02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01@\00\00\00\00\00\00\02\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\88\8A\EB\85\B1y7\9E\02\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\0F\D5\D7\0Bc\F3n<\02\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00z\FC\DEe\D47B\99\02\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\C7\CA\EB\85\B1y7\02\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00zu\14\FA\91k\BE$\02\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01@\00\80C\E5\F5\C2\02\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00zu\14z\D5P\B4\E7\02\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01@\00\00\87\CA\EB\85\02\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7Fzu\14zN\86\C8\E1\02\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01@\00\00\00\00\00\80\02\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\F3*(\F4\9C\0C\91\C3\02\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFzu\14zN\86\C8a\02\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\0Ao}_-Hg\13\02\00\00\00\00\00\00\00\102Tv\98\BA\DC\FEqF\97\1A!>aN\02\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\A7c\B8\A6\89Y0A\02\00\00\00\00\00\00\00UUUUUUUU\D4Q\\\D3\C4,\98 \FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\E0\1F\00\00\00\00\00\FF\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00\88*\F4\85\B1y7\9E\FF\00\00\00\00\00\00\00\02\00\00\00\00\00\00\00\0Fu\C8\0Bc\F3n<\FF\00\00\00\00\00\00\00\FF\00\00\00\00\00\00\00z\\\C1e\D47B\99\FF\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01g\D5\EB\85\B1y7\FF\00\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00z\D5\0B\FA\91k\BE$\FF\00\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\E0\1F\80C\E5\F5\C2\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00z\D5\0Bz\D5P\B4\E7\FF\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\E0\1F\00\87\CA\EB\85\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7Fz\D5\0BzN\86\C8\E1\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\E0\1F\00\00\00\00\80\FF\00\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\F3\8A7\F4\9C\0C\91\C3\FF\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFz\D5\0BzN\86\C8a\FF\00\00\00\00\00\00\00\EF\CD\AB\89gE#\01\0A\CFb_-Hg\13\FF\00\00\00\00\00\00\00\102Tv\98\BA\DC\FEq\E6\88\1A!>aN\FF\00\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\A7\C3\A7\A6\89Y0A\FF\00\00\00\00\00\00\00UUUUUUUU\D4\F1C\D3\C4,\98 \00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00 \00\00\00\00\00\00\01\00\00\00\00\00\00\01\00\00\00\00\00\00\00\88\CA\CB\85\B1y7\9E\00\01\00\00\00\00\00\00\02\00\00\00\00\00\00\00\0F\95\F7\0Bc\F3n<\00\01\00\00\00\00\00\00\FF\00\00\00\00\00\00\00z\BC\FEe\D47B\99\00\01\00\00\00\00\00\00\00\01\00\00\00\00\00\00\01\87\EA\EB\85\B1y7\00\01\00\00\00\00\00\00\FF\FF\FF\7F\00\00\00\00z54\FA\91k\BE$\00\01\00\00\00\00\00\00\00\00\00\80\00\00\00\00\01\00 \80C\E5\F5\C2\00\01\00\00\00\00\00\00\FF\FF\FF\FF\00\00\00\00z54z\D5P\B4\E7\00\01\00\00\00\00\00\00\00\00\00\00\01\00\00\00\01\00 \00\87\CA\EB\85\00\01\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7Fz54zN\86\C8\E1\00\01\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00 \00\00\00\00\80\00\01\00\00\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\F3j\08\F4\9C\0C\91\C3\00\01\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFz54zN\86\C8a\00\01\00\00\00\00\00\00\EF\CD\AB\89gE#\01\0A/]_-Hg\13\00\01\00\00\00\00\00\00\102Tv\98\BA\DC\FEq\06\B7\1A!>aN\00\01\00\00\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\A7#\98\A6\89Y0A\00\01\00\00\00\00\00\00UUUUUUUU\D4\11|\D3\C4,\98 \FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\00\01\E0\FF\FF\FF\0F\00\00\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\00\00\00\88*\14zNv7\9E\FF\FF\FF\7F\00\00\00\00\02\00\00\00\00\00\00\00\0Fu(\F4\9C\FCn<\FF\FF\FF\7F\00\00\00\00\FF\00\00\00\00\00\00\00z\\!\9A+8B\99\FF\FF\FF\7F\00\00\00\00\00\01\00\00\00\00\00\00\01g5\14z\BEy7\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\7F\00\00\00\00z\D5\EB\05nd\BE$\FF\FF\FF\7F\00\00\00\00\00\00\00\80\00\00\00\00\01\E0\FF\7F\BC\EA\F5\C2\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\00\00\00\00z\D5\EB\85*_\B4\E7\FF\FF\FF\7F\00\00\00\00\00\00\00\00\01\00\00\00\01\E0\FF\FFx\C5\EB\85\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7Fz\D5\EB\85\B1\89\C8\E1\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\00\00\80\01\E0\FF\FF\FF\0F\00\80\FF\FF\FF\7F\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\F3\8A\D7\0Bc\03\91\C3\FF\FF\FF\7F\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFz\D5\EB\85\B1\89\C8a\FF\FF\FF\7F\00\00\00\00\EF\CD\AB\89gE#\01\0A\CF\82\A0\D2Gg\13\FF\FF\FF\7F\00\00\00\00\102Tv\98\BA\DC\FEq\E6h\E5\DE1aN\FF\FF\FF\7F\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\A7\C3GYvV0A\FF\FF\FF\7F\00\00\00\00UUUUUUUU\D4\F1\A3,;#\98 \00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\10\00\00\00\00\00\80\00\00\00\00\01\00\00\00\00\00\00\00\88\CA\EB\85\B1i7\9E\00\00\00\80\00\00\00\00\02\00\00\00\00\00\00\00\0F\95\D7\0Bc\E3n<\00\00\00\80\00\00\00\00\FF\00\00\00\00\00\00\00z\BC\DEe\D4'B\99\00\00\00\80\00\00\00\00\00\01\00\00\00\00\00\00\01\87\CA\EB\85\A1y7\00\00\00\80\00\00\00\00\FF\FF\FF\7F\00\00\00\00z5\14\FA\91{\BE$\00\00\00\80\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\80C\F5\F5\C2\00\00\00\80\00\00\00\00\FF\FF\FF\FF\00\00\00\00z5\14z\D5@\B4\E7\00\00\00\80\00\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\87\DA\EB\85\00\00\00\80\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7Fz5\14zN\96\C8\E1\00\00\00\80\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\10\00\80\00\00\00\80\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\F3j(\F4\9C\1C\91\C3\00\00\00\80\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFz5\14zN\96\C8a\00\00\00\80\00\00\00\00\EF\CD\AB\89gE#\01\0A/}_-Xg\13\00\00\00\80\00\00\00\00\102Tv\98\BA\DC\FEq\06\97\1A!.aN\00\00\00\80\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\A7#\B8\A6\89I0A\00\00\00\80\00\00\00\00UUUUUUUU\D4\11\\\D3\C4<\98 \FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\01\E0\FF\FF\FF\1F\00\00\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00\88*\14zNf7\9E\FF\FF\FF\FF\00\00\00\00\02\00\00\00\00\00\00\00\0Fu(\F4\9C\ECn<\FF\FF\FF\FF\00\00\00\00\FF\00\00\00\00\00\00\00z\\!\9A+(B\99\FF\FF\FF\FF\00\00\00\00\00\01\00\00\00\00\00\00\01g5\14z\AEy7\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\7F\00\00\00\00z\D5\EB\05nt\BE$\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\01\E0\FF\7F\BC\FA\F5\C2\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\00\00\00\00z\D5\EB\85*O\B4\E7\FF\FF\FF\FF\00\00\00\00\00\00\00\00\01\00\00\00\01\E0\FF\FFx\D5\EB\85\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\7Fz\D5\EB\85\B1\99\C8\E1\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\80\01\E0\FF\FF\FF\1F\00\80\FF\FF\FF\FF\00\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\F3\8A\D7\0Bc\13\91\C3\FF\FF\FF\FF\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFz\D5\EB\85\B1\99\C8a\FF\FF\FF\FF\00\00\00\00\EF\CD\AB\89gE#\01\0A\CF\82\A0\D2Wg\13\FF\FF\FF\FF\00\00\00\00\102Tv\98\BA\DC\FEq\E6h\E5\DE!aN\FF\FF\FF\FF\00\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\A7\C3GYvF0A\FF\FF\FF\FF\00\00\00\00UUUUUUUU\D4\F1\A3,;3\98 \00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00 \00\00\00\00\00\00\01\00\00\00\01\00\00\00\00\00\00\00\88\CA\EB\85\B1Y7\9E\00\00\00\00\01\00\00\00\02\00\00\00\00\00\00\00\0F\95\D7\0Bc\D3n<\00\00\00\00\01\00\00\00\FF\00\00\00\00\00\00\00z\BC\DEe\D4\17B\99\00\00\00\00\01\00\00\00\00\01\00\00\00\00\00\00\01\87\CA\EB\85\91y7\00\00\00\00\01\00\00\00\FF\FF\FF\7F\00\00\00\00z5\14\FA\91K\BE$\00\00\00\00\01\00\00\00\00\00\00\80\00\00\00\00\01\00\00\80C\C5\F5\C2\00\00\00\00\01\00\00\00\FF\FF\FF\FF\00\00\00\00z5\14z\D5p\B4\E7\00\00\00\00\01\00\00\00\00\00\00\00\01\00\00\00\01\00\00\00\87\EA\EB\85\00\00\00\00\01\00\00\00\FF\FF\FF\FF\FF\FF\FF\7Fz5\14zN\A6\C8\E1\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00 \00\80\00\00\00\00\01\00\00\00\FE\FF\FF\FF\FF\FF\FF\FF\F3j(\F4\9C,\91\C3\00\00\00\00\01\00\00\00\FF\FF\FF\FF\FF\FF\FF\FFz5\14zN\A6\C8a\00\00\00\00\01\00\00\00\EF\CD\AB\89gE#\01\0A/}_-hg\13\00\00\00\00\01\00\00\00\102Tv\98\BA\DC\FEq\06\97\1A!\1EaN\00\00\00\00\01\00\00\00\AA\AA\AA\AA\AA\AA\AA\AA\A7#\B8\A6\89y0A\00\00\00\00\01\00\00\00UUUUUUUU\D4\11\\\D3\C4\0C\98 \FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\00\00\F0\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\01\00\00\00\00\00\00\00y%\14zN\86\C8a\FF\FF\FF\FF\FF\FF\FF\7F\02\00\00\00\00\00\00\00\F2z(\F4\9C\0C\91\C3\FF\FF\FF\FF\FF\FF\FF\7F\FF\00\00\00\00\00\00\00\87S!\9A+\C8\BDf\FF\FF\FF\FF\FF\FF\FF\7F\00\01\00\00\00\00\00\00\00i5\14zN\86\C8\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\7F\00\00\00\00\87\DA\EB\05n\94A\DB\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\80\00\00\00\00\00\F0\FF\7F\BC\1A\0A=\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\00\00\00\00\87\DA\EB\85*\AFK\18\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\01\00\00\00\00\F0\FF\FFx5\14z\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\7F\87\DA\EB\85\B1y7\1E\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\00\00\00\80\00\F0\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\0E\85\D7\0Bc\F3n<\FF\FF\FF\FF\FF\FF\FF\7F\FF\FF\FF\FF\FF\FF\FF\FF\87\DA\EB\85\B1y7\9E\FF\FF\FF\FF\FF\FF\FF\7F\EF\CD\AB\89gE#\01\F7\C0\82\A0\D2\B7\98\EC\FF\FF\FF\FF\FF\FF\FF\7F\102Tv\98\BA\DC\FE\90\E9h\E5\DE\C1\9E\B1\FF\FF\FF\FF\FF\FF\FF\7F\AA\AA\AA\AA\AA\AA\AA\AAZ\CCGYv\A6\CF\BE\FF\FF\FF\FF\FF\FF\FF\7FUUUUUUUU-\FE\A3,;\D3g\DF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\00\01\10\00\00\00\00\00\00\00\00\00\00\00\00\00\80\01\00\00\00\00\00\00\00\88\DA\EB\85\B1y7\9E\00\00\00\00\00\00\00\80\02\00\00\00\00\00\00\00\0F\85\D7\0Bc\F3n<\00\00\00\00\00\00\00\80\FF\00\00\00\00\00\00\00z\AC\DEe\D47B\99\00\00\00\00\00\00\00\80\00\01\00\00\00\00\00\00\01\97\CA\EB\85\B1y7\00\00\00\00\00\00\00\80\FF\FF\FF\7F\00\00\00\00z%\14\FA\91k\BE$\00\00\00\00\00\00\00\80\00\00\00\80\00\00\00\00\01\10\00\80C\E5\F5\C2\00\00\00\00\00\00\00\80\FF\FF\FF\FF\00\00\00\00z%\14z\D5P\B4\E7\00\00\00\00\00\00\00\80\00\00\00\00\01\00\00\00\01\10\00\00\87\CA\EB\85\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\7Fz%\14zN\86\C8\E1\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\01\10\00\00\00\00\00\80\00\00\00\00\00\00\00\80\FE\FF\FF\FF\FF\FF\FF\FF\F3z(\F4\9C\0C\91\C3\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FFz%\14zN\86\C8a\00\00\00\00\00\00\00\80\EF\CD\AB\89gE#\01\0A?}_-Hg\13\00\00\00\00\00\00\00\80\102Tv\98\BA\DC\FEq\16\97\1A!>aN\00\00\00\00\00\00\00\80\AA\AA\AA\AA\AA\AA\AA\AA\A73\B8\A6\89Y0A\00\00\00\00\00\00\00\80UUUUUUUU\D4\01\\\D3\C4,\98 \FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\E0\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00y\15\14zN\86\C8a\FE\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\F2J(\F4\9C\0C\91\C3\FE\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\87c!\9A+\C8\BDf\FE\FF\FF\FF\FF\FF\FF\FF\00\01\00\00\00\00\00\00\00Y5\14zN\86\C8\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\87\EA\EB\05n\94A\DB\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\E0\FF\7F\BC\1A\0A=\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\87\EA\EB\85*\AFK\18\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\E0\FF\FFx5\14z\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\87\EA\EB\85\B1y7\1E\FE\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\E0\FF\FF\FF\FF\FF\7F\FE\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\0E\B5\D7\0Bc\F3n<\FE\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\87\EA\EB\85\B1y7\9E\FE\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\F7\F0\82\A0\D2\B7\98\EC\FE\FF\FF\FF\FF\FF\FF\FF\102Tv\98\BA\DC\FE\90\D9h\E5\DE\C1\9E\B1\FE\FF\FF\FF\FF\FF\FF\FF\AA\AA\AA\AA\AA\AA\AA\AAZ\FCGYv\A6\CF\BE\FE\FF\FF\FF\FF\FF\FF\FFUUUUUUUU-\CE\A3,;\D3g\DF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\FF\FF\FF\FF\FF\FF\FF\FF\01\00\00\00\00\00\00\00y5\14zN\86\C8a\FF\FF\FF\FF\FF\FF\FF\FF\02\00\00\00\00\00\00\00\F2j(\F4\9C\0C\91\C3\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\87C!\9A+\C8\BDf\FF\FF\FF\FF\FF\FF\FF\FF\00\01\00\00\00\00\00\00\00y5\14zN\86\C8\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\00\00\00\00\87\CA\EB\05n\94A\DB\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\80\00\00\00\00\00\00\00\80\BC\1A\0A=\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\87\CA\EB\85*\AFK\18\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\01\00\00\00\00\00\00\00y5\14z\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\7F\87\CA\EB\85\B1y7\1E\FF\FF\FF\FF\FF\FF\FF\FF\00\00\00\00\00\00\00\80\00\00\00\00\00\00\00\80\FF\FF\FF\FF\FF\FF\FF\FF\FE\FF\FF\FF\FF\FF\FF\FF\0E\95\D7\0Bc\F3n<\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\FF\87\CA\EB\85\B1y7\9E\FF\FF\FF\FF\FF\FF\FF\FF\EF\CD\AB\89gE#\01\F7\D0\82\A0\D2\B7\98\EC\FF\FF\FF\FF\FF\FF\FF\FF\102Tv\98\BA\DC\FE\90\F9h\E5\DE\C1\9E\B1\FF\FF\FF\FF\FF\FF\FF\FF\AA\AA\AA\AA\AA\AA\AA\AAZ\DCGYv\A6\CF\BE\FF\FF\FF\FF\FF\FF\FF\FFUUUUUUUU-\EE\A3,;\D3g\DF\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\00%\E0\BDy5\F1\ACh\EF\CD\AB\89gE#\01\01\00\00\00\00\00\00\00\A4*V\FC\84\88\9B\F6\EF\CD\AB\89gE#\01\02\00\00\00\00\00\00\00+ujrV\02\C2T\EF\CD\AB\89gE#\01\FF\00\00\00\00\00\00\00^\\c\1C\E1\C6\EE\F1\EF\CD\AB\89gE#\01\00\01\00\00\00\00\00\00%gw\92\B0@\D5_\EF\CD\AB\89gE#\01\FF\FF\FF\7F\00\00\00\00^\D5\A9\83\A4\9A\12L\EF\CD\AB\89gE#\01\00\00\00\80\00\00\00\00%\E0\BD\F9v\14Y\AA\EF\CD\AB\89gE#\01\FF\FF\FF\FF\00\00\00\00^\D5\A9\03\E0\A1\18\8F\EF\CD\AB\89gE#\01\00\00\00\00\01\00\00\00%\E0\BDy\B2;G\ED\EF\CD\AB\89gE#\01\FF\FF\FF\FF\FF\FF\FF\7F^\D5\A9\03{wd\89\EF\CD\AB\89gE#\01\00\00\00\00\00\00\00\80%\E0\BDy5\F1\AC\E8\EF\CD\AB\89gE#\01\FE\FF\FF\FF\FF\FF\FF\FF\D7\8A\95\8D\A9\FD=\AB\EF\CD\AB\89gE#\01\FF\FF\FF\FF\FF\FF\FF\FF^\D5\A9\03{wd\09\EF\CD\AB\89gE#\01\EF\CD\AB\89gE#\01.\CF\C0&\18\B9\CB{\EF\CD\AB\89gE#\01\102Tv\98\BA\DC\FEU\E6*c\14\CF\CD&\EF\CD\AB\89gE#\01\AA\AA\AA\AA\AA\AA\AA\AA\83\C3\05\DF\BC\A8\9C)\EF\CD\AB\89gE#\01UUUUUUUU\F8\F1\E1\AA\F1\DD4H\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\00\DC\1FB\86\CA\0ES\97\102Tv\98\BA\DC\FE\01\00\00\00\00\00\00\00]\D5\A9\03{wd\09\102Tv\98\BA\DC\FE\02\00\00\00\00\00\00\00\D6\8A\95\8D\A9\FD=\AB\102Tv\98\BA\DC\FE\FF\00\00\00\00\00\00\00\A3\A3\9C\E3\1E9\11\0E\102Tv\98\BA\DC\FE\00\01\00\00\00\00\00\00\DC\98\88mO\BF*\A0\102Tv\98\BA\DC\FE\FF\FF\FF\7F\00\00\00\00\A3*V|[e\ED\B3\102Tv\98\BA\DC\FE\00\00\00\80\00\00\00\00\DC\1FB\06\89\EB\A6U\102Tv\98\BA\DC\FE\FF\FF\FF\FF\00\00\00\00\A3*V\FC\1F^\E7p\102Tv\98\BA\DC\FE\00\00\00\00\01\00\00\00\DC\1FB\86M\C4\B8\12\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\7F\A3*V\FC\84\88\9Bv\102Tv\98\BA\DC\FE\00\00\00\00\00\00\00\80\DC\1FB\86\CA\0ES\17\102Tv\98\BA\DC\FE\FE\FF\FF\FF\FF\FF\FF\FF*ujrV\02\C2T\102Tv\98\BA\DC\FE\FF\FF\FF\FF\FF\FF\FF\FF\A3*V\FC\84\88\9B\F6\102Tv\98\BA\DC\FE\EF\CD\AB\89gE#\01\D30?\D9\E7F4\84\102Tv\98\BA\DC\FE\102Tv\98\BA\DC\FE\AC\19\D5\9C\EB02\D9\102Tv\98\BA\DC\FE\AA\AA\AA\AA\AA\AA\AA\AA~<\FA CWc\D6\102Tv\98\BA\DC\FEUUUUUUUU\09\0E\1EU\0E\22\CB\B7\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\00VUUUUUUU\AA\AA\AA\AA\AA\AA\AA\AA\01\00\00\00\00\00\00\00\D3\9F\BE\D0\E4,b\CB\AA\AA\AA\AA\AA\AA\AA\AA\02\00\00\00\00\00\00\00\\\C0\82^6\A6;i\AA\AA\AA\AA\AA\AA\AA\AA\FF\00\00\00\00\00\00\00-\E9\8B0\81b\17\CC\AA\AA\AA\AA\AA\AA\AA\AA\00\01\00\00\00\00\00\00V\D2\9F\BE\D0\E4,b\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\7F\00\00\00\00-`A\AF\C4>\EBq\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\80\00\00\00\00VUU\D5\16\B0\A0\97\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\00\00\00\00-`A/\80\05\E1\B2\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\01\00\00\00VUUU\D2\9F\BE\D0\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\FF\FF\FF\7F-`A/\1B\D3\9D\B4\AA\AA\AA\AA\AA\AA\AA\AA\00\00\00\00\00\00\00\80VUUUUUU\D5\AA\AA\AA\AA\AA\AA\AA\AA\FE\FF\FF\FF\FF\FF\FF\FF\A8?}\A1\C9Y\C4\96\AA\AA\AA\AA\AA\AA\AA\AA\FF\FF\FF\FF\FF\FF\FF\FF-`A/\1B\D3\9D4\AA\AA\AA\AA\AA\AA\AA\AA\EF\CD\AB\89gE#\01]z(\0Ax\1D2F\AA\AA\AA\AA\AA\AA\AA\AA\102Tv\98\BA\DC\FE&S\C2Otk4\1B\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\AA\F4v\ED\F3\DC\0Ce\14\AA\AA\AA\AA\AA\AA\AA\AAUUUUUUUU\87D\09\86\91y\CDuUUUUUUUU\00\00\00\00\00\00\00\00\AB\AA\AA\AA\AA\AA\AA\AAUUUUUUUU\01\00\00\00\00\00\00\00.`A/\1B\D3\9D4UUUUUUUU\02\00\00\00\00\00\00\00\A5?}\A1\C9Y\C4\96UUUUUUUU\FF\00\00\00\00\00\00\00\D4\16t\CF~\9D\E83UUUUUUUU\00\01\00\00\00\00\00\00\AB-`A/\1B\D3\9DUUUUUUUU\FF\FF\FF\7F\00\00\00\00\D4\9F\BEP;\C1\14\8EUUUUUUUU\00\00\00\80\00\00\00\00\AB\AA\AA*\E9O_hUUUUUUUU\FF\FF\FF\FF\00\00\00\00\D4\9F\BE\D0\7F\FA\1EMUUUUUUUU\00\00\00\00\01\00\00\00\AB\AA\AA\AA-`A/UUUUUUUU\FF\FF\FF\FF\FF\FF\FF\7F\D4\9F\BE\D0\E4,bKUUUUUUUU\00\00\00\00\00\00\00\80\AB\AA\AA\AA\AA\AA\AA*UUUUUUUU\FE\FF\FF\FF\FF\FF\FF\FFY\C0\82^6\A6;iUUUUUUUU\FF\FF\FF\FF\FF\FF\FF\FF\D4\9F\BE\D0\E4,b\CBUUUUUUUU\EF\CD\AB\89gE#\01\A4\85\D7\F5\87\E2\CD\B9UUUUUUUU\102Tv\98\BA\DC\FE\DB\AC=\B0\8B\94\CB\E4UUUUUUUU\AA\AA\AA\AA\AA\AA\AA\AA\0D\89\12\0C#\F3\9A\EBUUUUUUUUUUUUUUUUz\BB\F6yn\862\8A", align 8
@alloc_4a29a4faa0904cd7ff982831f2813e90 = private unnamed_addr constant [6 x i8] c"x86_64", align 1
@alloc_c152a840973ba04895d1feffaffa964c = private unnamed_addr constant <{ ptr, [8 x i8] }> <{ ptr @alloc_4a29a4faa0904cd7ff982831f2813e90, [8 x i8] c"\06\00\00\00\00\00\00\00" }>, align 8
@alloc_44315d594dbcf3e603348f4c43d7c5fc = private unnamed_addr constant [12 x i8] c"E46_OK arch=", align 1
@alloc_095c2f6aafea7c7f99f9f5e984bff0ed = private unnamed_addr constant [8 x i8] c" checks=", align 1
@alloc_d3ac12b0dd8a8f05e09b09405411ead2 = private unnamed_addr constant [37 x i8] c" native_or_emulated=external_receipt\0A", align 1
@alloc_919c696c65d381e392ab9e07a65fcc86 = private unnamed_addr constant <{ ptr, [8 x i8], ptr, [8 x i8], ptr, [8 x i8] }> <{ ptr @alloc_44315d594dbcf3e603348f4c43d7c5fc, [8 x i8] c"\0C\00\00\00\00\00\00\00", ptr @alloc_095c2f6aafea7c7f99f9f5e984bff0ed, [8 x i8] c"\08\00\00\00\00\00\00\00", ptr @alloc_d3ac12b0dd8a8f05e09b09405411ead2, [8 x i8] c"%\00\00\00\00\00\00\00" }>, align 8
@alloc_a027c4cfdd2d4ac1ea07f38a958983b3 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00o\01\00\008\00\00\00" }>, align 8
@alloc_9fc22b8281c31507a4d7153995e6364a = private unnamed_addr constant [23 x i8] c"zerocopy-size-rejection", align 1
@alloc_3d2b22f6797fb9c8509022e3de60e2be = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00s\01\00\00,\00\00\00" }>, align 8
@alloc_b0b71860c7ea2a29b7e0e8c26098b5d4 = private unnamed_addr constant [29 x i8] c"zerocopy-write-size-rejection", align 1
@alloc_740169030ee0401ee356367948a12a38 = private unnamed_addr constant [9 x i8] c"\A6\A6\A6\A6\A6\A6\A6\A6\A6", align 1
@alloc_03d5a65b6a5ce4615b00d06a59905895 = private unnamed_addr constant [29 x i8] c"zerocopy-rejected-write-frame", align 1
@alloc_39fbebfa06d3949ee7666a8f08c17138 = private unnamed_addr constant [19 x i8] c"c-abi-helper-return", align 1
@alloc_ba5c6512d8d7f8a9c3e50e6eeb52fba9 = private unnamed_addr constant [17 x i8] c"c-abi-helper-once", align 1
@alloc_7fb6948253e08425011968cd1ab90324 = private unnamed_addr constant [17 x i8] c"c-abi-rust-bounce", align 1
@alloc_065d390ec367a092c01bac2a3e88eda3 = private unnamed_addr constant [22 x i8] c"c-abi-rust-helper-once", align 1
@alloc_fe7b60ca705568a437d85786e99ed873 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00O\01\00\00\1E\00\00\00" }>, align 8
@alloc_13818b644a22fbe6e3bb8eec05faecad = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00O\01\00\00C\00\00\00" }>, align 8
@alloc_b68c7081e6f02e9733108cba6bc83cee = private unnamed_addr constant [18 x i8] c"simd-add-alignment", align 1
@alloc_aff5e137726c4d2349c18b19090c6249 = private unnamed_addr constant [14 x i8] c"simd-add-lanes", align 1
@alloc_1e94e04a48e4b99390186fc97f15465b = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\\\01\00\00\19\00\00\00" }>, align 8
@alloc_03c51604ed10e62df9e875a4492ddac3 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\\\01\00\004\00\00\00" }>, align 8
@alloc_99f669e0aea23b6e9811243e2889d625 = private unnamed_addr constant [14 x i8] c"simd-add-frame", align 1
@alloc_0fcaa72dade1d254e789d4d18a2b43e7 = private unnamed_addr constant [14 x i8] c"copy-alignment", align 1
@alloc_e2884dc8bff5c33bae7b2ab5a2e22eea = private unnamed_addr constant [27 x i8] c"copy16-four-implementations", align 1
@alloc_2dce8867486f99811029456ce360cb96 = private unnamed_addr constant [12 x i8] c"copy16-frame", align 1
@alloc_6b7d3b6c55e21a409becc8ff4e5b6cfa = private unnamed_addr constant [13 x i8] c"exact16 bytes", align 1
@alloc_9607a92e94d9641e754f5eba05a75b50 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00B\01\00\00=\00\00\00" }>, align 8
@alloc_ccd7e5b641e08e3803aeabc6c7bbadbb = private unnamed_addr constant [21 x i8] c"zerocopy-view-pointer", align 1
@alloc_26a5af88e29a37ea28c610c1e1ea11fc = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00I\01\00\00:\00\00\00" }>, align 8
@alloc_85fda77841ed425dbdbff2ea33376135 = private unnamed_addr constant [29 x i8] c"pointer-return-no-dereference", align 1
@alloc_95f14cffea45f57db655c3f37835aa19 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\18\01\00\005\00\00\00" }>, align 8
@alloc_fe50387898c12f1be5ea6769040fd13b = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\1A\01\00\006\00\00\00" }>, align 8
@alloc_b110a08ed55610b06df9c62d38498d39 = private unnamed_addr constant [21 x i8] c"load-and-source-frame", align 1
@alloc_85aff4030bef76eb17649fc423a5fa40 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00 \01\00\00/\00\00\00" }>, align 8
@alloc_a3022215cbc4d93d75ff36ef0e45ea7d = private unnamed_addr constant [16 x i8] c"store-and-guards", align 1
@alloc_64b8082190e4360c7d33da45da484988 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00$\01\00\000\00\00\00" }>, align 8
@alloc_dbb2f02de7ffe024ec16cb240f78d280 = private unnamed_addr constant [23 x i8] c"inline-store-and-guards", align 1
@alloc_d402f7413af788172cdb7d05f581a90e = private unnamed_addr constant [19 x i8] c"store-rust-baseline", align 1
@alloc_82ec933a04e9adbc1c67d6f1c0ac3ada = private unnamed_addr constant [12 x i8] c"inline-label", align 1
@alloc_0d1d49781481982934645de3da0719d5 = private unnamed_addr constant [8 x i8] c"swap-asm", align 1
@alloc_2113db9752c8b12eb5687084ee02e22c = private unnamed_addr constant [9 x i8] c"swap-rust", align 1
@alloc_abf8626ad38cc02965dbd49aa14f61de = private unnamed_addr constant [13 x i8] c"zerocopy-wire", align 1
@alloc_4d00ccfdfe200e5040c2e2fbfdf1aaf8 = private unnamed_addr constant [21 x i8] c"zerocopy-rev-relation", align 1
@alloc_b1c687d5d6b680777219ce5cf351ec52 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\10\01\00\00:\00\00\00" }>, align 8
@alloc_27bbe9f55c42f8bb464508153e0483ae = private unnamed_addr constant [20 x i8] c"zerocopy-native-read", align 1
@alloc_149d364d8349edfe71770e753c396aa0 = private unnamed_addr constant [12 x i8] c"carry-domain", align 1
@alloc_b3cea492701bfda0e383697982d6e842 = private unnamed_addr constant [12 x i8] c"carry-inline", align 1
@alloc_2c6e6fe2dd10fb5e3112086a381bbd92 = private unnamed_addr constant [10 x i8] c"carry-rust", align 1
@alloc_faf886e179a440fdc6958e9c8e12af3c = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\FC\00\00\00K\00\00\00" }>, align 8
@alloc_02eca21413ccc32994161c12acef02d6 = private unnamed_addr constant [10 x i8] c"add128-asm", align 1
@alloc_c168e215480fb2698effa558f0e4841f = private unnamed_addr constant [11 x i8] c"add128-rust", align 1
@alloc_093aaf3820506a5cd0516e6789bd6927 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9d2f10b99692de8b0347ccb8b850521d, [16 x i8] c"\09\00\00\00\00\00\00\00\F2\00\00\003\00\00\00" }>, align 8
@alloc_46d4440e7a9abba00851fd9bc6521d38 = private unnamed_addr constant [7 x i8] c"mul-asm", align 1
@alloc_ad3f71f8fadccdea3aae76bb9fc6967b = private unnamed_addr constant [8 x i8] c"mul-rust", align 1

; <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h542bab8160d7c35cE"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_2 = getelementptr inbounds i8, ptr %self, i64 16
  %_3.0 = load i64, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.1 = load i64, ptr %0, align 8
; call <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h8d54de00bebc942dE"(ptr align 8 %_2, i64 %_3.0, i64 %_3.1) #14
  ret void
}

; <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h6c63ea1b9b49205bE"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_2 = getelementptr inbounds i8, ptr %self, i64 16
  %_3.0 = load i64, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.1 = load i64, ptr %0, align 8
; call <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17hc308302d770e9c8aE"(ptr align 8 %_2, i64 %_3.0, i64 %_3.1) #14
  ret void
}

; <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h90272728e9df5b47E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_2 = getelementptr inbounds i8, ptr %self, i64 16
  %_3.0 = load i64, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.1 = load i64, ptr %0, align 8
; call <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17hf4eef12aedd13e1aE"(ptr align 8 %_2, i64 %_3.0, i64 %_3.1) #14
  ret void
}

; <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h9b74a513d3379f92E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_2 = getelementptr inbounds i8, ptr %self, i64 16
  %_3.0 = load i64, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.1 = load i64, ptr %0, align 8
; call <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h7664700c9fa0dcc0E"(ptr align 8 %_2, i64 %_3.0, i64 %_3.1) #14
  ret void
}

; <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17haeaad4b1dc475b33E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_2 = getelementptr inbounds i8, ptr %self, i64 16
  %_3.0 = load i64, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.1 = load i64, ptr %0, align 8
; call <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17hae77f88aacdc268eE"(ptr align 8 %_2, i64 %_3.0, i64 %_3.1) #14
  ret void
}

; <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hb49a93b454613d63E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_2 = getelementptr inbounds i8, ptr %self, i64 16
  %_3.0 = load i64, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.1 = load i64, ptr %0, align 8
; call <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17hb3b048e0cd0e9593E"(ptr align 8 %_2, i64 %_3.0, i64 %_3.1) #14
  ret void
}

; <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hd2ee46e11933b0d5E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_2 = getelementptr inbounds i8, ptr %self, i64 16
  %_3.0 = load i64, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.1 = load i64, ptr %0, align 8
; call <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h010cc81022f5caf6E"(ptr align 8 %_2, i64 %_3.0, i64 %_3.1) #14
  ret void
}

; <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17he756edc91af43ec6E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_2 = getelementptr inbounds i8, ptr %self, i64 16
  %_3.0 = load i64, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.1 = load i64, ptr %0, align 8
; call <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h38a5836e0756315aE"(ptr align 1 %_2, i64 %_3.0, i64 %_3.1) #14
  ret void
}

; <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hfa6b483d5e01d474E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_2 = getelementptr inbounds i8, ptr %self, i64 16
  %_3.0 = load i64, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.1 = load i64, ptr %0, align 8
; call <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h805eec8f069511c7E"(ptr align 8 %_2, i64 %_3.0, i64 %_3.1) #14
  ret void
}

; <core::ops::index_range::IndexRange as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN104_$LT$core..ops..index_range..IndexRange$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hb539e16e3844cd2fE"(i64 %end, i64 %len, ptr align 8 %0) unnamed_addr #0 {
start:
  %_7 = alloca [16 x i8], align 8
  %_5 = alloca [48 x i8], align 8
  %_3 = icmp ule i64 %end, %len
  br i1 %_3, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %1 = getelementptr inbounds nuw { ptr, i64 }, ptr %_7, i64 0
  store ptr @alloc_5a8fdd84b3281310cbf6b74bb6bf0065, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %1, i64 8
  store i64 218, ptr %2, align 8
  store ptr %_7, ptr %_5, align 8
  %3 = getelementptr inbounds i8, ptr %_5, i64 8
  store i64 1, ptr %3, align 8
  %4 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %5 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %6 = getelementptr inbounds i8, ptr %_5, i64 32
  store ptr %4, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  store i64 %5, ptr %7, align 8
  %8 = getelementptr inbounds i8, ptr %_5, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %8, align 8
  %9 = getelementptr inbounds i8, ptr %8, i64 8
  store i64 0, ptr %9, align 8
; call core::panicking::panic_nounwind_fmt
  call void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8 %_5, i1 zeroext false, ptr align 8 %0) #15
  unreachable

bb1:                                              ; preds = %start
  ret void
}

; <core::ops::range::Range<usize> as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN106_$LT$core..ops..range..Range$LT$usize$GT$$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17h3777bb088f02bcd7E"(i64 %start1, i64 %end, i64 %len, ptr align 8 %0) unnamed_addr #0 {
start:
  %_9 = alloca [16 x i8], align 8
  %_7 = alloca [48 x i8], align 8
  %_4 = icmp uge i64 %end, %start1
  br i1 %_4, label %bb1, label %bb3

bb3:                                              ; preds = %bb1, %start
  %1 = getelementptr inbounds nuw { ptr, i64 }, ptr %_9, i64 0
  store ptr @alloc_18d73aa062d524e9620b9e3b55bd9eb1, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %1, i64 8
  store i64 218, ptr %2, align 8
  store ptr %_9, ptr %_7, align 8
  %3 = getelementptr inbounds i8, ptr %_7, i64 8
  store i64 1, ptr %3, align 8
  %4 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %5 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %6 = getelementptr inbounds i8, ptr %_7, i64 32
  store ptr %4, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  store i64 %5, ptr %7, align 8
  %8 = getelementptr inbounds i8, ptr %_7, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %8, align 8
  %9 = getelementptr inbounds i8, ptr %8, i64 8
  store i64 0, ptr %9, align 8
; call core::panicking::panic_nounwind_fmt
  call void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8 %_7, i1 zeroext false, ptr align 8 %0) #15
  unreachable

bb1:                                              ; preds = %start
  %_5 = icmp ule i64 %end, %len
  br i1 %_5, label %bb2, label %bb3

bb2:                                              ; preds = %bb1
  ret void
}

; <core::ops::range::Range<usize> as core::slice::index::SliceIndex<[T]>>::index_mut
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN106_$LT$core..ops..range..Range$LT$usize$GT$$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$9index_mut17h2e04aa241db781deE"(i64 %self.0, i64 %self.1, ptr align 1 %slice.0, i64 %slice.1, ptr align 8 %0) unnamed_addr #0 {
start:
  %_5 = alloca [16 x i8], align 8
  %_13 = icmp ult i64 %self.1, %self.0
  br i1 %_13, label %bb3, label %bb4

bb4:                                              ; preds = %start
  %_14 = sub nuw i64 %self.1, %self.0
  %1 = getelementptr inbounds i8, ptr %_5, i64 8
  store i64 %_14, ptr %1, align 8
  store i64 1, ptr %_5, align 8
  %2 = getelementptr inbounds i8, ptr %_5, i64 8
  %new_len = load i64, ptr %2, align 8
  %_8 = icmp ugt i64 %self.1, %slice.1
  br i1 %_8, label %bb1, label %bb2

bb3:                                              ; preds = %start
; call core::slice::index::slice_index_order_fail
  call void @_ZN4core5slice5index22slice_index_order_fail17h7a48bcbdaef81cf2E(i64 %self.0, i64 %self.1, ptr align 8 %0) #15
  unreachable

bb2:                                              ; preds = %bb4
  %_16 = getelementptr inbounds nuw i8, ptr %slice.0, i64 %self.0
  %3 = insertvalue { ptr, i64 } poison, ptr %_16, 0
  %4 = insertvalue { ptr, i64 } %3, i64 %new_len, 1
  ret { ptr, i64 } %4

bb1:                                              ; preds = %bb4
; call core::slice::index::slice_end_index_len_fail
  call void @_ZN4core5slice5index24slice_end_index_len_fail17heb50b9bbe4663132E(i64 %self.1, i64 %slice.1, ptr align 8 %0) #15
  unreachable
}

; <core::ops::range::RangeInclusive<T> as core::iter::range::RangeInclusiveIteratorImpl>::spec_next
; Function Attrs: inlinehint nounwind nonlazybind
define internal { i64, i64 } @"_ZN107_$LT$core..ops..range..RangeInclusive$LT$T$GT$$u20$as$u20$core..iter..range..RangeInclusiveIteratorImpl$GT$9spec_next17h0f00df2fb6d0e402E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_6 = alloca [8 x i8], align 8
  %_0 = alloca [16 x i8], align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 16
  %1 = load i8, ptr %0, align 8
  %_10 = trunc nuw i8 %1 to i1
  br i1 %_10, label %bb9, label %bb10

bb10:                                             ; preds = %start
  %_13 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.i = load i64, ptr %self, align 8
  %_4.i = load i64, ptr %_13, align 8
  %_0.i = icmp ule i64 %_3.i, %_4.i
  %_2 = xor i1 %_0.i, true
  br i1 %_2, label %bb1, label %bb2

bb9:                                              ; preds = %start
  br label %bb1

bb2:                                              ; preds = %bb10
  %_5 = getelementptr inbounds i8, ptr %self, i64 8
  %_3.i1 = load i64, ptr %self, align 8
  %_4.i2 = load i64, ptr %_5, align 8
  %_0.i3 = icmp ult i64 %_3.i1, %_4.i2
  br i1 %_0.i3, label %bb4, label %bb6

bb1:                                              ; preds = %bb9, %bb10
  store i64 0, ptr %_0, align 8
  br label %bb8

bb6:                                              ; preds = %bb2
  %2 = getelementptr inbounds i8, ptr %self, i64 16
  store i8 1, ptr %2, align 8
  %3 = load i64, ptr %self, align 8
  store i64 %3, ptr %_6, align 8
  br label %bb7

bb4:                                              ; preds = %bb2
  %_8 = load i64, ptr %self, align 8
; call <usize as core::iter::range::Step>::forward_unchecked
  %n = call i64 @"_ZN49_$LT$usize$u20$as$u20$core..iter..range..Step$GT$17forward_unchecked17h3a1ae6f4fc8e5645E"(i64 %_8, i64 1) #14
  %4 = load i64, ptr %self, align 8
  store i64 %4, ptr %_6, align 8
  store i64 %n, ptr %self, align 8
  br label %bb7

bb7:                                              ; preds = %bb4, %bb6
  %5 = load i64, ptr %_6, align 8
  %6 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %5, ptr %6, align 8
  store i64 1, ptr %_0, align 8
  br label %bb8

bb8:                                              ; preds = %bb1, %bb7
  %7 = load i64, ptr %_0, align 8
  %8 = getelementptr inbounds i8, ptr %_0, i64 8
  %9 = load i64, ptr %8, align 8
  %10 = insertvalue { i64, i64 } poison, i64 %7, 0
  %11 = insertvalue { i64, i64 } %10, i64 %9, 1
  ret { i64, i64 } %11
}

; <core::ops::range::RangeTo<usize> as core::slice::index::SliceIndex<[T]>>::index_mut
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN108_$LT$core..ops..range..RangeTo$LT$usize$GT$$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$9index_mut17hedaa82a3c29d03f1E"(i64 %self, ptr align 1 %slice.0, i64 %slice.1, ptr align 8 %0) unnamed_addr #0 {
start:
; call <core::ops::range::Range<usize> as core::slice::index::SliceIndex<[T]>>::index_mut
  %1 = call { ptr, i64 } @"_ZN106_$LT$core..ops..range..Range$LT$usize$GT$$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$9index_mut17h2e04aa241db781deE"(i64 0, i64 %self, ptr align 1 %slice.0, i64 %slice.1, ptr align 8 %0) #14
  %_0.0 = extractvalue { ptr, i64 } %1, 0
  %_0.1 = extractvalue { ptr, i64 } %1, 1
  %2 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %3 = insertvalue { ptr, i64 } %2, i64 %_0.1, 1
  ret { ptr, i64 } %3
}

; <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h0285df207ead1926E"(ptr align 8 %self.0, i64 %self.1, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
  %index = alloca [16 x i8], align 8
  store i64 %alive.0, ptr %index, align 8
  %0 = getelementptr inbounds i8, ptr %index, i64 8
  store i64 %alive.1, ptr %0, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <core::ops::index_range::IndexRange as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN104_$LT$core..ops..index_range..IndexRange$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hb539e16e3844cd2fE"(i64 %alive.1, i64 %self.1, ptr align 8 @alloc_4e72358380a5b7b26dfc8b890055d168) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %len = sub nuw i64 %alive.1, %alive.0
  %_18 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u64; 3]>", ptr %self.0, i64 %alive.0
  %1 = icmp eq i64 %len, 0
  br i1 %1, label %bb4, label %bb5

bb4:                                              ; preds = %bb5, %bb3
  ret void

bb5:                                              ; preds = %bb3
  br label %bb4
}

; <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h119789d7e9ee4d2dE"(ptr align 8 %self.0, i64 %self.1, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
  %index = alloca [16 x i8], align 8
  store i64 %alive.0, ptr %index, align 8
  %0 = getelementptr inbounds i8, ptr %index, i64 8
  store i64 %alive.1, ptr %0, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <core::ops::index_range::IndexRange as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN104_$LT$core..ops..index_range..IndexRange$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hb539e16e3844cd2fE"(i64 %alive.1, i64 %self.1, ptr align 8 @alloc_4e72358380a5b7b26dfc8b890055d168) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %len = sub nuw i64 %alive.1, %alive.0
  %_18 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u64; 2]>", ptr %self.0, i64 %alive.0
  %1 = icmp eq i64 %len, 0
  br i1 %1, label %bb4, label %bb5

bb4:                                              ; preds = %bb5, %bb3
  ret void

bb5:                                              ; preds = %bb3
  br label %bb4
}

; <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h2496d61e13506cd9E"(ptr align 8 %self.0, i64 %self.1, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
  %index = alloca [16 x i8], align 8
  store i64 %alive.0, ptr %index, align 8
  %0 = getelementptr inbounds i8, ptr %index, i64 8
  store i64 %alive.1, ptr %0, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <core::ops::index_range::IndexRange as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN104_$LT$core..ops..index_range..IndexRange$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hb539e16e3844cd2fE"(i64 %alive.1, i64 %self.1, ptr align 8 @alloc_4e72358380a5b7b26dfc8b890055d168) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %len = sub nuw i64 %alive.1, %alive.0
  %_18 = getelementptr inbounds nuw i64, ptr %self.0, i64 %alive.0
  %1 = icmp eq i64 %len, 0
  br i1 %1, label %bb4, label %bb5

bb4:                                              ; preds = %bb5, %bb3
  ret void

bb5:                                              ; preds = %bb3
  br label %bb4
}

; <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h55e18572dead6aa0E"(ptr align 8 %self.0, i64 %self.1, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
  %index = alloca [16 x i8], align 8
  store i64 %alive.0, ptr %index, align 8
  %0 = getelementptr inbounds i8, ptr %index, i64 8
  store i64 %alive.1, ptr %0, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <core::ops::index_range::IndexRange as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN104_$LT$core..ops..index_range..IndexRange$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hb539e16e3844cd2fE"(i64 %alive.1, i64 %self.1, ptr align 8 @alloc_4e72358380a5b7b26dfc8b890055d168) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %len = sub nuw i64 %alive.1, %alive.0
  %_18 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<(usize, usize, [u8; 16])>", ptr %self.0, i64 %alive.0
  %1 = icmp eq i64 %len, 0
  br i1 %1, label %bb4, label %bb5

bb4:                                              ; preds = %bb5, %bb3
  ret void

bb5:                                              ; preds = %bb3
  br label %bb4
}

; <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h58a020cb748aa500E"(ptr align 8 %self.0, i64 %self.1, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
  %index = alloca [16 x i8], align 8
  store i64 %alive.0, ptr %index, align 8
  %0 = getelementptr inbounds i8, ptr %index, i64 8
  store i64 %alive.1, ptr %0, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <core::ops::index_range::IndexRange as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN104_$LT$core..ops..index_range..IndexRange$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hb539e16e3844cd2fE"(i64 %alive.1, i64 %self.1, ptr align 8 @alloc_4e72358380a5b7b26dfc8b890055d168) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %len = sub nuw i64 %alive.1, %alive.0
  %_18 = getelementptr inbounds nuw i64, ptr %self.0, i64 %alive.0
  %1 = icmp eq i64 %len, 0
  br i1 %1, label %bb4, label %bb5

bb4:                                              ; preds = %bb5, %bb3
  ret void

bb5:                                              ; preds = %bb3
  br label %bb4
}

; <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h60bae541dc2ce170E"(ptr align 1 %self.0, i64 %self.1, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
  %index = alloca [16 x i8], align 8
  store i64 %alive.0, ptr %index, align 8
  %0 = getelementptr inbounds i8, ptr %index, i64 8
  store i64 %alive.1, ptr %0, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <core::ops::index_range::IndexRange as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN104_$LT$core..ops..index_range..IndexRange$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hb539e16e3844cd2fE"(i64 %alive.1, i64 %self.1, ptr align 8 @alloc_4e72358380a5b7b26dfc8b890055d168) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %len = sub nuw i64 %alive.1, %alive.0
  %_18 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u8; 16]>", ptr %self.0, i64 %alive.0
  %1 = icmp eq i64 %len, 0
  br i1 %1, label %bb4, label %bb5

bb4:                                              ; preds = %bb5, %bb3
  ret void

bb5:                                              ; preds = %bb3
  br label %bb4
}

; <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h6455bf479532d280E"(ptr align 8 %self.0, i64 %self.1, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
  %index = alloca [16 x i8], align 8
  store i64 %alive.0, ptr %index, align 8
  %0 = getelementptr inbounds i8, ptr %index, i64 8
  store i64 %alive.1, ptr %0, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <core::ops::index_range::IndexRange as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN104_$LT$core..ops..index_range..IndexRange$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hb539e16e3844cd2fE"(i64 %alive.1, i64 %self.1, ptr align 8 @alloc_4e72358380a5b7b26dfc8b890055d168) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %len = sub nuw i64 %alive.1, %alive.0
  %_18 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u64; 7]>", ptr %self.0, i64 %alive.0
  %1 = icmp eq i64 %len, 0
  br i1 %1, label %bb4, label %bb5

bb4:                                              ; preds = %bb5, %bb3
  ret void

bb5:                                              ; preds = %bb3
  br label %bb4
}

; <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h91c265e010bca897E"(ptr align 8 %self.0, i64 %self.1, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
  %index = alloca [16 x i8], align 8
  store i64 %alive.0, ptr %index, align 8
  %0 = getelementptr inbounds i8, ptr %index, i64 8
  store i64 %alive.1, ptr %0, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <core::ops::index_range::IndexRange as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN104_$LT$core..ops..index_range..IndexRange$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hb539e16e3844cd2fE"(i64 %alive.1, i64 %self.1, ptr align 8 @alloc_4e72358380a5b7b26dfc8b890055d168) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %len = sub nuw i64 %alive.1, %alive.0
  %_18 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u64; 4]>", ptr %self.0, i64 %alive.0
  %1 = icmp eq i64 %len, 0
  br i1 %1, label %bb4, label %bb5

bb4:                                              ; preds = %bb5, %bb3
  ret void

bb5:                                              ; preds = %bb3
  br label %bb4
}

; <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17hc780129c5ce5c268E"(ptr align 8 %self.0, i64 %self.1, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
  %index = alloca [16 x i8], align 8
  store i64 %alive.0, ptr %index, align 8
  %0 = getelementptr inbounds i8, ptr %index, i64 8
  store i64 %alive.1, ptr %0, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <core::ops::index_range::IndexRange as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN104_$LT$core..ops..index_range..IndexRange$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hb539e16e3844cd2fE"(i64 %alive.1, i64 %self.1, ptr align 8 @alloc_4e72358380a5b7b26dfc8b890055d168) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %len = sub nuw i64 %alive.1, %alive.0
  %_18 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u64; 5]>", ptr %self.0, i64 %alive.0
  %1 = icmp eq i64 %len, 0
  br i1 %1, label %bb4, label %bb5

bb4:                                              ; preds = %bb5, %bb3
  ret void

bb5:                                              ; preds = %bb3
  br label %bb4
}

; <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h010cc81022f5caf6E"(ptr align 8 %self, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
; call <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h2496d61e13506cd9E"(ptr align 8 %self, i64 2, i64 %alive.0, i64 %alive.1) #14
  ret void
}

; <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h38a5836e0756315aE"(ptr align 1 %self, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
; call <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h60bae541dc2ce170E"(ptr align 1 %self, i64 12, i64 %alive.0, i64 %alive.1) #14
  ret void
}

; <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h7664700c9fa0dcc0E"(ptr align 8 %self, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
; call <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h91c265e010bca897E"(ptr align 8 %self, i64 289, i64 %alive.0, i64 %alive.1) #14
  ret void
}

; <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h805eec8f069511c7E"(ptr align 8 %self, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
; call <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h55e18572dead6aa0E"(ptr align 8 %self, i64 144, i64 %alive.0, i64 %alive.1) #14
  ret void
}

; <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h8d54de00bebc942dE"(ptr align 8 %self, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
; call <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17hc780129c5ce5c268E"(ptr align 8 %self, i64 578, i64 %alive.0, i64 %alive.1) #14
  ret void
}

; <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17hae77f88aacdc268eE"(ptr align 8 %self, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
; call <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h0285df207ead1926E"(ptr align 8 %self, i64 289, i64 %alive.0, i64 %alive.1) #14
  ret void
}

; <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17hb3b048e0cd0e9593E"(ptr align 8 %self, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
; call <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h6455bf479532d280E"(ptr align 8 %self, i64 144, i64 %alive.0, i64 %alive.1) #14
  ret void
}

; <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17hc308302d770e9c8aE"(ptr align 8 %self, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
; call <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h58a020cb748aa500E"(ptr align 8 %self, i64 17, i64 %alive.0, i64 %alive.1) #14
  ret void
}

; <[core::mem::maybe_uninit::MaybeUninit<T>; N] as core::array::iter::iter_inner::PartialDrop>::partial_drop
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN129_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u3b$$u20$N$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17hf4eef12aedd13e1aE"(ptr align 8 %self, i64 %alive.0, i64 %alive.1) unnamed_addr #1 {
start:
; call <[core::mem::maybe_uninit::MaybeUninit<T>] as core::array::iter::iter_inner::PartialDrop>::partial_drop
  call void @"_ZN118_$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$u20$as$u20$core..array..iter..iter_inner..PartialDrop$GT$12partial_drop17h119789d7e9ee4d2dE"(ptr align 8 %self, i64 17, i64 %alive.0, i64 %alive.1) #14
  ret void
}

; <core::result::Result<T,F> as core::ops::try_trait::FromResidual<core::result::Result<core::convert::Infallible,E>>>::from_residual
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN153_$LT$core..result..Result$LT$T$C$F$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..result..Result$LT$core..convert..Infallible$C$E$GT$$GT$$GT$13from_residual17haa588d2d34a518fdE"(ptr sret([16 x i8]) align 8 %_0, i1 zeroext %0, ptr align 8 %1) unnamed_addr #0 {
start:
  %residual = alloca [1 x i8], align 1
  %2 = zext i1 %0 to i8
  store i8 %2, ptr %residual, align 1
  %3 = load i8, ptr %residual, align 1
  %e = trunc nuw i8 %3 to i1
  %4 = getelementptr inbounds i8, ptr %_0, i64 1
  %5 = zext i1 %e to i8
  store i8 %5, ptr %4, align 1
  store i8 1, ptr %_0, align 8
  ret void
}

; <core::result::Result<T,F> as core::ops::try_trait::FromResidual<core::result::Result<core::convert::Infallible,E>>>::from_residual
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN153_$LT$core..result..Result$LT$T$C$F$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..result..Result$LT$core..convert..Infallible$C$E$GT$$GT$$GT$13from_residual17habf6625c1fc10ec1E"(ptr sret([32 x i8]) align 8 %_0, ptr align 8 %residual, ptr align 8 %0) unnamed_addr #0 {
start:
  %_3 = alloca [24 x i8], align 8
  %e = alloca [24 x i8], align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %e, ptr align 8 %residual, i64 24, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_3, ptr align 8 %e, i64 24, i1 false)
  %1 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 8 %_3, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  ret void
}

; <core::ops::try_trait::NeverShortCircuit<T> as core::ops::try_trait::FromResidual<core::ops::try_trait::NeverShortCircuitResidual>>::from_residual
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN158_$LT$core..ops..try_trait..NeverShortCircuit$LT$T$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..ops..try_trait..NeverShortCircuitResidual$GT$$GT$13from_residual17hf80d254b2d03953cE"(ptr sret([16 x i8]) align 1 %_0) unnamed_addr #0 {
start:
  unreachable
}

; <zerocopy::error::ConvertError<zerocopy::error::AlignmentError<Src,Dst>,zerocopy::error::SizeError<Src,Dst>,core::convert::Infallible> as zerocopy::pointer::ptr::_casts::TryWithError<NewSrc>>::map
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN238_$LT$zerocopy..error..ConvertError$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$C$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$C$core..convert..Infallible$GT$$u20$as$u20$zerocopy..pointer..ptr.._casts..TryWithError$LT$NewSrc$GT$$GT$3map17h2a80ab23a5914275E"(ptr sret([24 x i8]) align 8 %_0, i1 zeroext %self, ptr align 8 %f) unnamed_addr #0 {
start:
; call zerocopy::error::ConvertError<zerocopy::error::AlignmentError<Src,Dst>,zerocopy::error::SizeError<Src,Dst>,core::convert::Infallible>::map_src
  call void @"_ZN8zerocopy5error142ConvertError$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$C$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$C$core..convert..Infallible$GT$7map_src17h8a55bf6585f616aeE"(ptr sret([24 x i8]) align 8 %_0, i1 zeroext %self, ptr align 8 %f) #14
  ret void
}

; std::rt::lang_start
; Function Attrs: nounwind nonlazybind
define hidden i64 @_ZN3std2rt10lang_start17hceb1b6aa47208e68E(ptr %main, i64 %argc, ptr %argv, i8 %sigpipe) unnamed_addr #1 {
start:
  %_7 = alloca [8 x i8], align 8
  store ptr %main, ptr %_7, align 8
; call std::rt::lang_start_internal
  %_0 = call i64 @_ZN3std2rt19lang_start_internal17h31bbb7f936fd6b5dE(ptr align 1 %_7, ptr align 8 @vtable.0, i64 %argc, ptr %argv, i8 %sigpipe) #14
  ret i64 %_0
}

; std::rt::lang_start::{{closure}}
; Function Attrs: inlinehint nounwind nonlazybind
define internal i32 @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17hb764b9c7e0decc7bE"(ptr align 8 %_1) unnamed_addr #0 {
start:
  %_4 = load ptr, ptr %_1, align 8
; call std::sys::backtrace::__rust_begin_short_backtrace
  call void @_ZN3std3sys9backtrace28__rust_begin_short_backtrace17hbd42e3f545df04a7E(ptr %_4) #14
; call <() as std::process::Termination>::report
  %self = call i8 @"_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h2631335329a91021E"() #14
  %_0 = zext i8 %self to i32
  ret i32 %_0
}

; std::sys::backtrace::__rust_begin_short_backtrace
; Function Attrs: noinline nounwind nonlazybind
define internal void @_ZN3std3sys9backtrace28__rust_begin_short_backtrace17hbd42e3f545df04a7E(ptr %f) unnamed_addr #2 {
start:
; call core::ops::function::FnOnce::call_once
  call void @_ZN4core3ops8function6FnOnce9call_once17hfcaa7286a06b0d4dE(ptr %f) #14
  call void asm sideeffect "", "~{memory}"(), !srcloc !4
  ret void
}

; <&T as core::ops::deref::Deref>::deref
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN49_$LT$$RF$T$u20$as$u20$core..ops..deref..Deref$GT$5deref17hf2c26a9a04406c1fE"(ptr align 8 %self) unnamed_addr #1 {
start:
  %_0.0 = load ptr, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_0.1 = load i64, ptr %0, align 8
  %1 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %2 = insertvalue { ptr, i64 } %1, i64 %_0.1, 1
  ret { ptr, i64 } %2
}

; <usize as core::iter::range::Step>::forward_unchecked
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN49_$LT$usize$u20$as$u20$core..iter..range..Step$GT$17forward_unchecked17h3a1ae6f4fc8e5645E"(i64 %start1, i64 %n) unnamed_addr #0 {
start:
  br label %bb1

bb1:                                              ; preds = %start
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %start1, i64 %n, ptr align 8 @alloc_51d47b6744cc9a652983e1beeae10eec) #14
  br label %bb2

bb2:                                              ; preds = %bb1
  %_0 = add nuw i64 %start1, %n
  ret i64 %_0
}

; core::intrinsics::cold_path
; Function Attrs: cold nounwind nonlazybind
define internal void @_ZN4core10intrinsics9cold_path17hb88f405144600927E() unnamed_addr #3 {
start:
  ret void
}

; core::cmp::impls::<impl core::cmp::PartialEq for u64>::eq
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core3cmp5impls54_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$u64$GT$2eq17hfd8942048f5d5838E"(ptr align 8 %self, ptr align 8 %other) unnamed_addr #0 {
start:
  %_3 = load i64, ptr %self, align 8
  %_4 = load i64, ptr %other, align 8
  %_0 = icmp eq i64 %_3, %_4
  ret i1 %_0
}

; core::fmt::rt::<impl core::fmt::Arguments>::new_v1
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core3fmt2rt38_$LT$impl$u20$core..fmt..Arguments$GT$6new_v117haf3e53cd4fb6e77eE"(ptr sret([48 x i8]) align 8 %_0, ptr align 8 %pieces, ptr align 8 %args) unnamed_addr #0 {
start:
  store ptr %pieces, ptr %_0, align 8
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 3, ptr %0, align 8
  %1 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %2 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %3 = getelementptr inbounds i8, ptr %_0, i64 32
  store ptr %1, ptr %3, align 8
  %4 = getelementptr inbounds i8, ptr %3, i64 8
  store i64 %2, ptr %4, align 8
  %5 = getelementptr inbounds i8, ptr %_0, i64 16
  store ptr %args, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %5, i64 8
  store i64 2, ptr %6, align 8
  ret void
}

; core::fmt::rt::<impl core::fmt::Arguments>::new_const
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core3fmt2rt38_$LT$impl$u20$core..fmt..Arguments$GT$9new_const17hc17ead96ff728c9aE"(ptr sret([48 x i8]) align 8 %_0, ptr align 8 %pieces) unnamed_addr #0 {
start:
  store ptr %pieces, ptr %_0, align 8
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 1, ptr %0, align 8
  %1 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %2 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %3 = getelementptr inbounds i8, ptr %_0, i64 32
  store ptr %1, ptr %3, align 8
  %4 = getelementptr inbounds i8, ptr %3, i64 8
  store i64 %2, ptr %4, align 8
  %5 = getelementptr inbounds i8, ptr %_0, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %5, i64 8
  store i64 0, ptr %6, align 8
  ret void
}

; core::fmt::rt::Argument::new_display
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core3fmt2rt8Argument11new_display17h17ee8a6fae403bc4E(ptr sret([16 x i8]) align 8 %_0, ptr align 8 %x) unnamed_addr #0 {
start:
  %_2 = alloca [16 x i8], align 8
  store ptr %x, ptr %_2, align 8
  %0 = getelementptr inbounds i8, ptr %_2, i64 8
  store ptr @"_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17hd277b88914e88d67E", ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_2, i64 16, i1 false)
  ret void
}

; core::fmt::rt::Argument::new_display
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core3fmt2rt8Argument11new_display17he5979accc9ea05abE(ptr sret([16 x i8]) align 8 %_0, ptr align 8 %x) unnamed_addr #0 {
start:
  %_2 = alloca [16 x i8], align 8
  store ptr %x, ptr %_2, align 8
  %0 = getelementptr inbounds i8, ptr %_2, i64 8
  store ptr @"_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17h7601fb479c860baeE", ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_2, i64 16, i1 false)
  ret void
}

; core::fmt::rt::Argument::new_display
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core3fmt2rt8Argument11new_display17hfb13677ee243d15eE(ptr sret([16 x i8]) align 8 %_0, ptr align 8 %x) unnamed_addr #0 {
start:
  %_2 = alloca [16 x i8], align 8
  store ptr %x, ptr %_2, align 8
  %0 = getelementptr inbounds i8, ptr %_2, i64 8
  store ptr @"_ZN52_$LT$$RF$mut$u20$T$u20$as$u20$core..fmt..Display$GT$3fmt17h39130a453e30f3adE", ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_2, i64 16, i1 false)
  ret void
}

; core::mem::size_of_val
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @_ZN4core3mem11size_of_val17h461cba1b7fec62f5E(ptr align 1 %val) unnamed_addr #0 {
start:
  %0 = alloca [8 x i8], align 8
  store i64 16, ptr %0, align 8
  %_0 = load i64, ptr %0, align 8
  ret i64 %_0
}

; core::mem::size_of_val
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @_ZN4core3mem11size_of_val17hbf8b027503e661beE(ptr align 1 %val) unnamed_addr #0 {
start:
  %0 = alloca [8 x i8], align 8
  store i64 8, ptr %0, align 8
  %_0 = load i64, ptr %0, align 8
  ret i64 %_0
}

; core::mem::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core3mem4drop17h1eaf4b0d526cfd48E() unnamed_addr #0 {
start:
  ret void
}

; core::num::<impl u64>::to_be_bytes
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$11to_be_bytes17h763c5b251a6c665cE"(i64 %self) unnamed_addr #0 {
start:
  %0 = alloca [8 x i8], align 8
  %_0 = alloca [8 x i8], align 1
  %1 = call i64 @llvm.bswap.i64(i64 %self)
  store i64 %1, ptr %0, align 8
  %self1 = load i64, ptr %0, align 8
  store i64 %self1, ptr %_0, align 1
  %2 = load i64, ptr %_0, align 1
  ret i64 %2
}

; core::num::<impl u64>::to_le_bytes
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$11to_le_bytes17h9b6ef962f188f4afE"(i64 %self) unnamed_addr #0 {
start:
  %_0 = alloca [8 x i8], align 1
  store i64 %self, ptr %_0, align 1
  %0 = load i64, ptr %_0, align 1
  ret i64 %0
}

; core::num::<impl u64>::from_be_bytes
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$13from_be_bytes17h310cb9b2da71e482E"(i64 %0) unnamed_addr #0 {
start:
  %1 = alloca [8 x i8], align 8
  %2 = alloca [8 x i8], align 8
  %bytes = alloca [8 x i8], align 1
  store i64 %0, ptr %2, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %bytes, ptr align 8 %2, i64 8, i1 false)
  %x = load i64, ptr %bytes, align 1
  %3 = call i64 @llvm.bswap.i64(i64 %x)
  store i64 %3, ptr %1, align 8
  %_0 = load i64, ptr %1, align 8
  ret i64 %_0
}

; core::num::<impl u64>::from_le_bytes
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$13from_le_bytes17h109ece7e3f19119cE"(i64 %0) unnamed_addr #0 {
start:
  %1 = alloca [8 x i8], align 8
  %bytes = alloca [8 x i8], align 1
  store i64 %0, ptr %1, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %bytes, ptr align 8 %1, i64 8, i1 false)
  %_0 = load i64, ptr %bytes, align 1
  ret i64 %_0
}

; core::num::<impl u64>::from_ne_bytes
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$13from_ne_bytes17hc580473d72475e6fE"(i64 %0) unnamed_addr #0 {
start:
  %1 = alloca [8 x i8], align 8
  %bytes = alloca [8 x i8], align 1
  store i64 %0, ptr %1, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %bytes, ptr align 8 %1, i64 8, i1 false)
  %_0 = load i64, ptr %bytes, align 1
  ret i64 %_0
}

; core::num::<impl usize>::checked_add
; Function Attrs: inlinehint nounwind nonlazybind
define internal { i64, i64 } @"_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_add17h07a6aef785bb2367E"(i64 %self, i64 %rhs) unnamed_addr #0 {
start:
  %_0 = alloca [16 x i8], align 8
  %0 = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %self, i64 %rhs)
  %_4.0 = extractvalue { i64, i1 } %0, 0
  %_4.1 = extractvalue { i64, i1 } %0, 1
  br i1 %_4.1, label %bb2, label %bb4

bb4:                                              ; preds = %start
  %_5 = add nuw i64 %self, %rhs
  %1 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %_5, ptr %1, align 8
  store i64 1, ptr %_0, align 8
  br label %bb1

bb2:                                              ; preds = %start
  %2 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %3 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %2, ptr %_0, align 8
  %4 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %3, ptr %4, align 8
  br label %bb1

bb1:                                              ; preds = %bb2, %bb4
  %5 = load i64, ptr %_0, align 8
  %6 = getelementptr inbounds i8, ptr %_0, i64 8
  %7 = load i64, ptr %6, align 8
  %8 = insertvalue { i64, i64 } poison, i64 %5, 0
  %9 = insertvalue { i64, i64 } %8, i64 %7, 1
  ret { i64, i64 } %9
}

; core::num::<impl usize>::checked_mul
; Function Attrs: inlinehint nounwind nonlazybind
define internal { i64, i64 } @"_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_mul17h15ddeb83d8fdb7cfE"(i64 %self, i64 %rhs) unnamed_addr #0 {
start:
  %_0 = alloca [16 x i8], align 8
  %0 = call { i64, i1 } @llvm.umul.with.overflow.i64(i64 %self, i64 %rhs)
  %_5.0 = extractvalue { i64, i1 } %0, 0
  %_5.1 = extractvalue { i64, i1 } %0, 1
  br i1 %_5.1, label %bb2, label %bb4

bb4:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %_5.0, ptr %1, align 8
  store i64 1, ptr %_0, align 8
  br label %bb1

bb2:                                              ; preds = %start
  %2 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %3 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %2, ptr %_0, align 8
  %4 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %3, ptr %4, align 8
  br label %bb1

bb1:                                              ; preds = %bb2, %bb4
  %5 = load i64, ptr %_0, align 8
  %6 = getelementptr inbounds i8, ptr %_0, i64 8
  %7 = load i64, ptr %6, align 8
  %8 = insertvalue { i64, i64 } poison, i64 %5, 0
  %9 = insertvalue { i64, i64 } %8, i64 %7, 1
  ret { i64, i64 } %9
}

; core::num::<impl usize>::checked_sub
; Function Attrs: inlinehint nounwind nonlazybind
define internal { i64, i64 } @"_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_sub17hdabf32b0dd7c6f9bE"(i64 %self, i64 %rhs) unnamed_addr #0 {
start:
  %_0 = alloca [16 x i8], align 8
  %_3 = icmp ult i64 %self, %rhs
  br i1 %_3, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %_4 = sub nuw i64 %self, %rhs
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %_4, ptr %0, align 8
  store i64 1, ptr %_0, align 8
  br label %bb3

bb1:                                              ; preds = %start
  %1 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %2 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %1, ptr %_0, align 8
  %3 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %2, ptr %3, align 8
  br label %bb3

bb3:                                              ; preds = %bb1, %bb2
  %4 = load i64, ptr %_0, align 8
  %5 = getelementptr inbounds i8, ptr %_0, i64 8
  %6 = load i64, ptr %5, align 8
  %7 = insertvalue { i64, i64 } poison, i64 %4, 0
  %8 = insertvalue { i64, i64 } %7, i64 %6, 1
  ret { i64, i64 } %8
}

; core::num::<impl usize>::unchecked_add::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %lhs, i64 %rhs, ptr align 8 %0) unnamed_addr #0 {
start:
  %_6 = alloca [16 x i8], align 8
  %_4 = alloca [48 x i8], align 8
  %1 = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %lhs, i64 %rhs)
  %_8.0 = extractvalue { i64, i1 } %1, 0
  %_8.1 = extractvalue { i64, i1 } %1, 1
  br i1 %_8.1, label %bb1, label %bb2

bb2:                                              ; preds = %start
  ret void

bb1:                                              ; preds = %start
  %2 = getelementptr inbounds nuw { ptr, i64 }, ptr %_6, i64 0
  store ptr @alloc_3e1ebac14318b612ab4efabc52799932, ptr %2, align 8
  %3 = getelementptr inbounds i8, ptr %2, i64 8
  store i64 186, ptr %3, align 8
  store ptr %_6, ptr %_4, align 8
  %4 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 1, ptr %4, align 8
  %5 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %6 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 32
  store ptr %5, ptr %7, align 8
  %8 = getelementptr inbounds i8, ptr %7, i64 8
  store i64 %6, ptr %8, align 8
  %9 = getelementptr inbounds i8, ptr %_4, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %9, align 8
  %10 = getelementptr inbounds i8, ptr %9, i64 8
  store i64 0, ptr %10, align 8
; call core::panicking::panic_nounwind_fmt
  call void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8 %_4, i1 zeroext false, ptr align 8 %0) #15
  unreachable
}

; core::num::<impl usize>::unchecked_sub::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_sub18precondition_check17h8b0b7e8c552b56ffE"(i64 %lhs, i64 %rhs, ptr align 8 %0) unnamed_addr #0 {
start:
  %_6 = alloca [16 x i8], align 8
  %_4 = alloca [48 x i8], align 8
  %_8.0 = sub i64 %lhs, %rhs
  %_8.1 = icmp ult i64 %lhs, %rhs
  br i1 %_8.1, label %bb1, label %bb2

bb2:                                              ; preds = %start
  ret void

bb1:                                              ; preds = %start
  %1 = getelementptr inbounds nuw { ptr, i64 }, ptr %_6, i64 0
  store ptr @alloc_846c8306b730cf00804b037ffdb61170, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %1, i64 8
  store i64 186, ptr %2, align 8
  store ptr %_6, ptr %_4, align 8
  %3 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 1, ptr %3, align 8
  %4 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %5 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %6 = getelementptr inbounds i8, ptr %_4, i64 32
  store ptr %4, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  store i64 %5, ptr %7, align 8
  %8 = getelementptr inbounds i8, ptr %_4, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %8, align 8
  %9 = getelementptr inbounds i8, ptr %8, i64 8
  store i64 0, ptr %9, align 8
; call core::panicking::panic_nounwind_fmt
  call void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8 %_4, i1 zeroext false, ptr align 8 %0) #15
  unreachable
}

; core::num::nonzero::NonZero<T>::get
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %self) unnamed_addr #0 {
start:
  ret i64 %self
}

; core::num::nonzero::NonZero<T>::new
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3new17h61bb2493f7c27af8E"(i64 %n) unnamed_addr #0 {
start:
  ret i64 %n
}

; core::ops::range::RangeInclusive<Idx>::new
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core3ops5range25RangeInclusive$LT$Idx$GT$3new17h65d5050921f6672bE"(ptr sret([24 x i8]) align 8 %_0, i64 %start1, i64 %end) unnamed_addr #0 {
start:
  store i64 %start1, ptr %_0, align 8
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %end, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_0, i64 16
  store i8 0, ptr %1, align 8
  ret void
}

; core::ops::function::FnOnce::call_once{{vtable.shim}}
; Function Attrs: inlinehint nounwind nonlazybind
define internal i32 @"_ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h9e7f46232d862455E"(ptr %_1) unnamed_addr #0 {
start:
  %_2 = alloca [0 x i8], align 1
  %0 = load ptr, ptr %_1, align 8
; call core::ops::function::FnOnce::call_once
  %_0 = call i32 @_ZN4core3ops8function6FnOnce9call_once17h20d88fcd66df5114E(ptr %0) #14
  ret i32 %_0
}

; core::ops::function::FnOnce::call_once
; Function Attrs: inlinehint nounwind nonlazybind
define internal i32 @_ZN4core3ops8function6FnOnce9call_once17h20d88fcd66df5114E(ptr %0) unnamed_addr #0 {
start:
  %_2 = alloca [0 x i8], align 1
  %_1 = alloca [8 x i8], align 8
  store ptr %0, ptr %_1, align 8
; call std::rt::lang_start::{{closure}}
  %_0 = call i32 @"_ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17hb764b9c7e0decc7bE"(ptr align 8 %_1) #14
  ret i32 %_0
}

; core::ops::function::FnOnce::call_once
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core3ops8function6FnOnce9call_once17hfcaa7286a06b0d4dE(ptr %_1) unnamed_addr #0 {
start:
  %_2 = alloca [0 x i8], align 1
  call void %_1() #14
  ret void
}

; core::ops::try_trait::NeverShortCircuit<T>::wrap_mut_1::{{closure}}
; Function Attrs: inlinehint nounwind nonlazybind
define internal i8 @"_ZN4core3ops9try_trait26NeverShortCircuit$LT$T$GT$10wrap_mut_128_$u7b$$u7b$closure$u7d$$u7d$17h8b7ad2441085dc6bE"(ptr align 8 %_1, i64 %a) unnamed_addr #0 {
start:
; call extended_pilot::rust_add16::{{closure}}
  %_3 = call i8 @"_ZN14extended_pilot10rust_add1628_$u7b$$u7b$closure$u7d$$u7d$17hbdd83e617637f6caE"(ptr align 8 %_1, i64 %a) #14
  ret i8 %_3
}

; core::ptr::drop_in_place<core::array::iter::IntoIter<(usize,usize,[u8; 16]),144_usize>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr116drop_in_place$LT$core..array..iter..IntoIter$LT$$LP$usize$C$usize$C$$u5b$u8$u3b$$u20$16$u5d$$RP$$C$144_usize$GT$$GT$17h4bd794b93b0579dcE"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
  call void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hdd4f2b0ba15ecce2E"(ptr align 8 %_1) #14
; call core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<(usize,usize,[u8; 16])>; 144]>>
  call void @"_ZN4core3ptr190drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$LP$usize$C$usize$C$$u5b$u8$u3b$$u20$16$u5d$$RP$$GT$$u3b$$u20$144$u5d$$GT$$GT$17h4dd45b3c49b2e56dE"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<u64>; 17]>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr144drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$u64$GT$$u3b$$u20$17$u5d$$GT$$GT$17hf0ed550dc9c1cf9fE"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
  call void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h6c63ea1b9b49205bE"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<usize>; 2]>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr145drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$usize$GT$$u3b$$u20$2$u5d$$GT$$GT$17h7a45940782d49efeE"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
  call void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hd2ee46e11933b0d5E"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u64; 2]>; 17]>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr165drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u64$u3b$$u20$2$u5d$$GT$$u3b$$u20$17$u5d$$GT$$GT$17h7dd8d148cc2d069cE"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
  call void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h90272728e9df5b47E"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u8; 16]>; 12]>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr165drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u8$u3b$$u20$16$u5d$$GT$$u3b$$u20$12$u5d$$GT$$GT$17hf6845c2af571177aE"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
  call void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17he756edc91af43ec6E"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u64; 3]>; 289]>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr166drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u64$u3b$$u20$3$u5d$$GT$$u3b$$u20$289$u5d$$GT$$GT$17h45150eec91d4152cE"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
  call void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17haeaad4b1dc475b33E"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u64; 4]>; 289]>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr166drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u64$u3b$$u20$4$u5d$$GT$$u3b$$u20$289$u5d$$GT$$GT$17h0a20244e4094def7E"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
  call void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h9b74a513d3379f92E"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u64; 5]>; 578]>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr166drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u64$u3b$$u20$5$u5d$$GT$$u3b$$u20$578$u5d$$GT$$GT$17he2c69a425d9aa0f5E"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
  call void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h542bab8160d7c35cE"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u64; 7]>; 144]>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr166drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u64$u3b$$u20$7$u5d$$GT$$u3b$$u20$144$u5d$$GT$$GT$17h6fae487eb47bcb81E"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
  call void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hb49a93b454613d63E"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<(usize,usize,[u8; 16])>; 144]>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr190drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$LP$usize$C$usize$C$$u5b$u8$u3b$$u20$16$u5d$$RP$$GT$$u3b$$u20$144$u5d$$GT$$GT$17h4dd45b3c49b2e56dE"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::iter_inner::PolymorphicIter<DATA> as core::ops::drop::Drop>::drop
  call void @"_ZN100_$LT$core..array..iter..iter_inner..PolymorphicIter$LT$DATA$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hfa6b483d5e01d474E"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::copy_nonoverlapping::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core3ptr19copy_nonoverlapping18precondition_check17h1af93ef5bb8d2ab6E(ptr %src, ptr %dst, i64 %size, i64 %align, i64 %count, ptr align 8 %0) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %1 = alloca [4 x i8], align 4
  %_29 = alloca [48 x i8], align 8
  %_24 = alloca [4 x i8], align 4
  %_23 = alloca [8 x i8], align 8
  %_22 = alloca [8 x i8], align 8
  %_21 = alloca [8 x i8], align 8
  %_20 = alloca [48 x i8], align 8
  %_17 = alloca [16 x i8], align 8
  %_15 = alloca [48 x i8], align 8
  %is_zst = alloca [1 x i8], align 1
  %align1 = alloca [8 x i8], align 8
  %zero_size = alloca [1 x i8], align 1
  %2 = icmp eq i64 %count, 0
  br i1 %2, label %bb1, label %bb2

bb1:                                              ; preds = %start
  store i8 1, ptr %zero_size, align 1
  store i64 %align, ptr %align1, align 8
  %3 = load i8, ptr %zero_size, align 1
  %4 = trunc nuw i8 %3 to i1
  %5 = zext i1 %4 to i8
  store i8 %5, ptr %is_zst, align 1
  %6 = call i64 @llvm.ctpop.i64(i64 %align)
  %7 = trunc i64 %6 to i32
  store i32 %7, ptr %_24, align 4
  %8 = load i32, ptr %_24, align 4
  %9 = icmp eq i32 %8, 1
  br i1 %9, label %bb26, label %bb15

bb2:                                              ; preds = %start
  %10 = icmp eq i64 %size, 0
  %11 = zext i1 %10 to i8
  store i8 %11, ptr %zero_size, align 1
  store i64 %align, ptr %align1, align 8
  %12 = load i8, ptr %zero_size, align 1
  %13 = trunc nuw i8 %12 to i1
  %14 = zext i1 %13 to i8
  store i8 %14, ptr %is_zst, align 1
  %15 = call i64 @llvm.ctpop.i64(i64 %align)
  %16 = trunc i64 %15 to i32
  store i32 %16, ptr %_24, align 4
  %17 = load i32, ptr %_24, align 4
  %18 = icmp eq i32 %17, 1
  br i1 %18, label %bb14, label %bb15

bb26:                                             ; preds = %bb1
  %19 = ptrtoint ptr %src to i64
  store i64 %19, ptr %_22, align 8
  %20 = sub i64 %align, 1
  store i64 %20, ptr %_23, align 8
  %21 = load i64, ptr %_22, align 8
  %22 = load i64, ptr %_23, align 8
  %23 = and i64 %21, %22
  store i64 %23, ptr %_21, align 8
  %24 = load i64, ptr %_21, align 8
  %25 = icmp eq i64 %24, 0
  br i1 %25, label %bb27, label %bb11

bb15:                                             ; preds = %bb2, %bb1
  store ptr @alloc_e92e94d0ff530782b571cfd99ec66aef, ptr %_20, align 8
  %26 = getelementptr inbounds i8, ptr %_20, i64 8
  store i64 1, ptr %26, align 8
  %27 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %28 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %29 = getelementptr inbounds i8, ptr %_20, i64 32
  store ptr %27, ptr %29, align 8
  %30 = getelementptr inbounds i8, ptr %29, i64 8
  store i64 %28, ptr %30, align 8
  %31 = getelementptr inbounds i8, ptr %_20, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %31, align 8
  %32 = getelementptr inbounds i8, ptr %31, i64 8
  store i64 0, ptr %32, align 8
; call core::panicking::panic_fmt
  call void @_ZN4core9panicking9panic_fmt17hc49fc28484033487E(ptr align 8 %_20, ptr align 8 @alloc_84fd0ee1b6b57a4ef5ffe86edcc9d22c) #15
  unreachable

bb27:                                             ; preds = %bb26
  br label %bb12

bb11:                                             ; preds = %bb14, %bb26
  br label %bb6

bb12:                                             ; preds = %bb10, %bb27
  br label %bb3

bb14:                                             ; preds = %bb2
  %33 = ptrtoint ptr %src to i64
  store i64 %33, ptr %_22, align 8
  %34 = sub i64 %align, 1
  store i64 %34, ptr %_23, align 8
  %35 = load i64, ptr %_22, align 8
  %36 = load i64, ptr %_23, align 8
  %37 = and i64 %35, %36
  store i64 %37, ptr %_21, align 8
  %38 = load i64, ptr %_21, align 8
  %39 = icmp eq i64 %38, 0
  br i1 %39, label %bb10, label %bb11

bb10:                                             ; preds = %bb14
  %40 = load i8, ptr %is_zst, align 1
  %41 = trunc nuw i8 %40 to i1
  br i1 %41, label %bb12, label %bb13

bb13:                                             ; preds = %bb10
  %42 = load i64, ptr %_22, align 8
  %_18 = icmp eq i64 %42, 0
  %_8 = xor i1 %_18, true
  br i1 %_8, label %bb3, label %bb6

bb6:                                              ; preds = %bb11, %bb13
  br label %bb7

bb3:                                              ; preds = %bb12, %bb13
  %43 = load i8, ptr %zero_size, align 1
  %is_zst2 = trunc nuw i8 %43 to i1
  %44 = call i64 @llvm.ctpop.i64(i64 %align)
  %45 = trunc i64 %44 to i32
  store i32 %45, ptr %1, align 4
  %_32 = load i32, ptr %1, align 4
  %46 = icmp eq i32 %_32, 1
  br i1 %46, label %bb21, label %bb22

bb21:                                             ; preds = %bb3
  %_31 = ptrtoint ptr %dst to i64
  %47 = load i64, ptr %_23, align 8
  %_30 = and i64 %_31, %47
  %48 = icmp eq i64 %_30, 0
  br i1 %48, label %bb17, label %bb18

bb22:                                             ; preds = %bb3
  store ptr @alloc_e92e94d0ff530782b571cfd99ec66aef, ptr %_29, align 8
  %49 = getelementptr inbounds i8, ptr %_29, i64 8
  store i64 1, ptr %49, align 8
  %50 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %51 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %52 = getelementptr inbounds i8, ptr %_29, i64 32
  store ptr %50, ptr %52, align 8
  %53 = getelementptr inbounds i8, ptr %52, i64 8
  store i64 %51, ptr %53, align 8
  %54 = getelementptr inbounds i8, ptr %_29, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %54, align 8
  %55 = getelementptr inbounds i8, ptr %54, i64 8
  store i64 0, ptr %55, align 8
; call core::panicking::panic_fmt
  call void @_ZN4core9panicking9panic_fmt17hc49fc28484033487E(ptr align 8 %_29, ptr align 8 @alloc_84fd0ee1b6b57a4ef5ffe86edcc9d22c) #15
  unreachable

bb17:                                             ; preds = %bb21
  br i1 %is_zst2, label %bb19, label %bb20

bb18:                                             ; preds = %bb21
  br label %bb5

bb20:                                             ; preds = %bb17
  %_27 = icmp eq i64 %_31, 0
  %_11 = xor i1 %_27, true
  br i1 %_11, label %bb4, label %bb5

bb19:                                             ; preds = %bb17
  br label %bb4

bb5:                                              ; preds = %bb18, %bb20
  br label %bb7

bb4:                                              ; preds = %bb19, %bb20
; call core::ub_checks::maybe_is_nonoverlapping::runtime
  %_6 = call zeroext i1 @_ZN4core9ub_checks23maybe_is_nonoverlapping7runtime17h87d6f7c633fc7293E(ptr %src, ptr %dst, i64 %size, i64 %count) #14
  br i1 %_6, label %bb9, label %bb8

bb8:                                              ; preds = %bb7, %bb4
  %56 = getelementptr inbounds nuw { ptr, i64 }, ptr %_17, i64 0
  store ptr @alloc_bd3468a7b96187f70c1ce98a3e7a63bf, ptr %56, align 8
  %57 = getelementptr inbounds i8, ptr %56, i64 8
  store i64 283, ptr %57, align 8
  store ptr %_17, ptr %_15, align 8
  %58 = getelementptr inbounds i8, ptr %_15, i64 8
  store i64 1, ptr %58, align 8
  %59 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %60 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %61 = getelementptr inbounds i8, ptr %_15, i64 32
  store ptr %59, ptr %61, align 8
  %62 = getelementptr inbounds i8, ptr %61, i64 8
  store i64 %60, ptr %62, align 8
  %63 = getelementptr inbounds i8, ptr %_15, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %63, align 8
  %64 = getelementptr inbounds i8, ptr %63, i64 8
  store i64 0, ptr %64, align 8
; call core::panicking::panic_nounwind_fmt
  call void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8 %_15, i1 zeroext false, ptr align 8 %0) #15
  unreachable

bb9:                                              ; preds = %bb4
  ret void

bb7:                                              ; preds = %bb6, %bb5
  br label %bb8
}

; core::ptr::slice_from_raw_parts_mut
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @_ZN4core3ptr24slice_from_raw_parts_mut17h9fe5a088220a3d11E(ptr %data, i64 %len) unnamed_addr #0 {
start:
  %0 = insertvalue { ptr, i64 } poison, ptr %data, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %len, 1
  ret { ptr, i64 } %1
}

; core::ptr::drop_in_place<core::array::Guard<u8>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr49drop_in_place$LT$core..array..Guard$LT$u8$GT$$GT$17h673dc5c8847d92d8E"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::Guard<T> as core::ops::drop::Drop>::drop
  call void @"_ZN69_$LT$core..array..Guard$LT$T$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h398677062c4df853E"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::read
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core3ptr4read17h11a61a189bbb4cc5E(ptr sret([16 x i8]) align 1 %_0, ptr %src, ptr align 8 %0) unnamed_addr #0 {
start:
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0, ptr align 1 %src, i64 16, i1 false)
  ret void
}

; core::ptr::read
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @_ZN4core3ptr4read17ha6e646c6d3854f9eE(ptr %src, ptr align 8 %0) unnamed_addr #0 {
start:
  %_0 = alloca [8 x i8], align 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0, ptr align 1 %src, i64 8, i1 false)
  %1 = load i64, ptr %_0, align 1
  ret i64 %1
}

; core::ptr::read
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @_ZN4core3ptr4read17hab62c60c64480059E(ptr %src, ptr align 8 %0) unnamed_addr #0 {
start:
  %_0 = alloca [8 x i8], align 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0, ptr align 1 %src, i64 8, i1 false)
  %1 = load i64, ptr %_0, align 1
  ret i64 %1
}

; core::ptr::drop_in_place<core::array::iter::IntoIter<u64,17_usize>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr70drop_in_place$LT$core..array..iter..IntoIter$LT$u64$C$17_usize$GT$$GT$17ha7750d7bc5ccc23fE"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
  call void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h7a3db9b058eca382E"(ptr align 8 %_1) #14
; call core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<u64>; 17]>>
  call void @"_ZN4core3ptr144drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$u64$GT$$u3b$$u20$17$u5d$$GT$$GT$17hf0ed550dc9c1cf9fE"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::IntoIter<usize,2_usize>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr71drop_in_place$LT$core..array..iter..IntoIter$LT$usize$C$2_usize$GT$$GT$17hcae5af927efba4b4E"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
  call void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hd6a24cdc59b53e3aE"(ptr align 8 %_1) #14
; call core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<usize>; 2]>>
  call void @"_ZN4core3ptr145drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$usize$GT$$u3b$$u20$2$u5d$$GT$$GT$17h7a45940782d49efeE"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::non_null::NonNull<T>::new_unchecked
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h1c6dc69b456e977bE"(ptr %ptr, ptr align 8 %0) unnamed_addr #0 {
start:
  br label %bb1

bb1:                                              ; preds = %start
; call core::ptr::non_null::NonNull<T>::new_unchecked::precondition_check
  call void @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked18precondition_check17h5f73ce62f9f6c4ebE"(ptr %ptr, ptr align 8 %0) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  ret ptr %ptr
}

; core::ptr::non_null::NonNull<T>::new_unchecked
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h25de8935aa4ad477E"(ptr %ptr, ptr align 8 %0) unnamed_addr #0 {
start:
  br label %bb1

bb1:                                              ; preds = %start
; call core::ptr::non_null::NonNull<T>::new_unchecked::precondition_check
  call void @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked18precondition_check17h5f73ce62f9f6c4ebE"(ptr %ptr, ptr align 8 %0) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  ret ptr %ptr
}

; core::ptr::non_null::NonNull<T>::new_unchecked
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17hf6de2e43cf1c61b0E"(ptr %ptr.0, i64 %ptr.1, ptr align 8 %0) unnamed_addr #0 {
start:
  br label %bb1

bb1:                                              ; preds = %start
; call core::ptr::non_null::NonNull<T>::new_unchecked::precondition_check
  call void @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked18precondition_check17h5f73ce62f9f6c4ebE"(ptr %ptr.0, ptr align 8 %0) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %1 = insertvalue { ptr, i64 } poison, ptr %ptr.0, 0
  %2 = insertvalue { ptr, i64 } %1, i64 %ptr.1, 1
  ret { ptr, i64 } %2
}

; core::ptr::non_null::NonNull<T>::new_unchecked::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked18precondition_check17h5f73ce62f9f6c4ebE"(ptr %ptr, ptr align 8 %0) unnamed_addr #0 {
start:
  %_5 = alloca [16 x i8], align 8
  %_3 = alloca [48 x i8], align 8
  %_6 = ptrtoint ptr %ptr to i64
  %1 = icmp eq i64 %_6, 0
  br i1 %1, label %bb1, label %bb2

bb1:                                              ; preds = %start
  %2 = getelementptr inbounds nuw { ptr, i64 }, ptr %_5, i64 0
  store ptr @alloc_560a59ed819b9d9a5841f6e731c4c8e5, ptr %2, align 8
  %3 = getelementptr inbounds i8, ptr %2, i64 8
  store i64 210, ptr %3, align 8
  store ptr %_5, ptr %_3, align 8
  %4 = getelementptr inbounds i8, ptr %_3, i64 8
  store i64 1, ptr %4, align 8
  %5 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %6 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %7 = getelementptr inbounds i8, ptr %_3, i64 32
  store ptr %5, ptr %7, align 8
  %8 = getelementptr inbounds i8, ptr %7, i64 8
  store i64 %6, ptr %8, align 8
  %9 = getelementptr inbounds i8, ptr %_3, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %9, align 8
  %10 = getelementptr inbounds i8, ptr %9, i64 8
  store i64 0, ptr %10, align 8
; call core::panicking::panic_nounwind_fmt
  call void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8 %_3, i1 zeroext false, ptr align 8 %0) #15
  unreachable

bb2:                                              ; preds = %start
  ret void
}

; core::ptr::non_null::NonNull<T>::cast
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17h110a24a51af34c8dE"(ptr %self.0, i64 %self.1) unnamed_addr #0 {
start:
  ret ptr %self.0
}

; core::ptr::non_null::NonNull<T>::cast
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17h718584af148cdac1E"(ptr %self) unnamed_addr #0 {
start:
  ret ptr %self
}

; core::ptr::non_null::NonNull<T>::cast
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17hf7dee4d24dee0e26E"(ptr %self) unnamed_addr #0 {
start:
  ret ptr %self
}

; core::ptr::non_null::NonNull<[T]>::slice_from_raw_parts
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN4core3ptr8non_null26NonNull$LT$$u5b$T$u5d$$GT$20slice_from_raw_parts17h04e6fc05340fc983E"(ptr %data, i64 %len) unnamed_addr #0 {
start:
  br label %bb1

bb1:                                              ; preds = %start
; call core::ptr::non_null::NonNull<T>::new_unchecked::precondition_check
  call void @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked18precondition_check17h5f73ce62f9f6c4ebE"(ptr %data, ptr align 8 @alloc_b7e0708131946905642ff5dd82ebdcf1) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %0 = insertvalue { ptr, i64 } poison, ptr %data, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %len, 1
  ret { ptr, i64 } %1
}

; core::ptr::drop_in_place<core::array::iter::IntoIter<[u64; 2],17_usize>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr91drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u64$u3b$$u20$2$u5d$$C$17_usize$GT$$GT$17hdc3c237a1461c403E"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
  call void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h8a926ea295a2290eE"(ptr align 8 %_1) #14
; call core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u64; 2]>; 17]>>
  call void @"_ZN4core3ptr165drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u64$u3b$$u20$2$u5d$$GT$$u3b$$u20$17$u5d$$GT$$GT$17h7dd8d148cc2d069cE"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::IntoIter<[u8; 16],12_usize>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr91drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u8$u3b$$u20$16$u5d$$C$12_usize$GT$$GT$17hb357102e7eaa006aE"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
  call void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h4f781dc08e8b28a7E"(ptr align 8 %_1) #14
; call core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u8; 16]>; 12]>>
  call void @"_ZN4core3ptr165drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u8$u3b$$u20$16$u5d$$GT$$u3b$$u20$12$u5d$$GT$$GT$17hf6845c2af571177aE"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::IntoIter<[u64; 3],289_usize>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr92drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u64$u3b$$u20$3$u5d$$C$289_usize$GT$$GT$17h6320d5ec2bb54e95E"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
  call void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hae31289f73b9331cE"(ptr align 8 %_1) #14
; call core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u64; 3]>; 289]>>
  call void @"_ZN4core3ptr166drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u64$u3b$$u20$3$u5d$$GT$$u3b$$u20$289$u5d$$GT$$GT$17h45150eec91d4152cE"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::IntoIter<[u64; 4],289_usize>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr92drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u64$u3b$$u20$4$u5d$$C$289_usize$GT$$GT$17ha871b6e048fae9c7E"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
  call void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hb2ca57aab1b19302E"(ptr align 8 %_1) #14
; call core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u64; 4]>; 289]>>
  call void @"_ZN4core3ptr166drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u64$u3b$$u20$4$u5d$$GT$$u3b$$u20$289$u5d$$GT$$GT$17h0a20244e4094def7E"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::IntoIter<[u64; 5],578_usize>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr92drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u64$u3b$$u20$5$u5d$$C$578_usize$GT$$GT$17h398570afd82295f4E"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
  call void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hd374a0c0eb06d4aaE"(ptr align 8 %_1) #14
; call core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u64; 5]>; 578]>>
  call void @"_ZN4core3ptr166drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u64$u3b$$u20$5$u5d$$GT$$u3b$$u20$578$u5d$$GT$$GT$17he2c69a425d9aa0f5E"(ptr align 8 %_1) #14
  ret void
}

; core::ptr::drop_in_place<core::array::iter::IntoIter<[u64; 7],144_usize>>
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN4core3ptr92drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u64$u3b$$u20$7$u5d$$C$144_usize$GT$$GT$17hbc817a1e405b13e9E"(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
  call void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17haf29285ee22537e9E"(ptr align 8 %_1) #14
; call core::ptr::drop_in_place<core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<[u64; 7]>; 144]>>
  call void @"_ZN4core3ptr166drop_in_place$LT$core..array..iter..iter_inner..PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$$u5b$u64$u3b$$u20$7$u5d$$GT$$u3b$$u20$144$u5d$$GT$$GT$17h6fae487eb47bcb81E"(ptr align 8 %_1) #14
  ret void
}

; core::hint::unreachable_unchecked
; Function Attrs: inlinehint noreturn nounwind nonlazybind
define internal void @_ZN4core4hint21unreachable_unchecked17h21c3b9f74b946857E(ptr align 8 %0) unnamed_addr #4 {
start:
; call core::hint::unreachable_unchecked::precondition_check
  call void @_ZN4core4hint21unreachable_unchecked18precondition_check17h01a686d8fb705dceE(ptr align 8 %0) #14
  unreachable
}

; core::hint::unreachable_unchecked::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core4hint21unreachable_unchecked18precondition_check17h01a686d8fb705dceE(ptr align 8 %0) unnamed_addr #0 {
start:
  %_4 = alloca [16 x i8], align 8
  %_2 = alloca [48 x i8], align 8
  %1 = getelementptr inbounds nuw { ptr, i64 }, ptr %_4, i64 0
  store ptr @alloc_75fb06c2453febd814e73f5f2e72ae38, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %1, i64 8
  store i64 199, ptr %2, align 8
  store ptr %_4, ptr %_2, align 8
  %3 = getelementptr inbounds i8, ptr %_2, i64 8
  store i64 1, ptr %3, align 8
  %4 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %5 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %6 = getelementptr inbounds i8, ptr %_2, i64 32
  store ptr %4, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  store i64 %5, ptr %7, align 8
  %8 = getelementptr inbounds i8, ptr %_2, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %8, align 8
  %9 = getelementptr inbounds i8, ptr %8, i64 8
  store i64 0, ptr %9, align 8
; call core::panicking::panic_nounwind_fmt
  call void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8 %_2, i1 zeroext false, ptr align 8 %0) #15
  unreachable
}

; core::iter::range::<impl core::iter::traits::iterator::Iterator for core::ops::range::RangeInclusive<A>>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal { i64, i64 } @"_ZN4core4iter5range110_$LT$impl$u20$core..iter..traits..iterator..Iterator$u20$for$u20$core..ops..range..RangeInclusive$LT$A$GT$$GT$4next17hd68c10f4d31d14e8E"(ptr align 8 %self) unnamed_addr #0 {
start:
; call <core::ops::range::RangeInclusive<T> as core::iter::range::RangeInclusiveIteratorImpl>::spec_next
  %0 = call { i64, i64 } @"_ZN107_$LT$core..ops..range..RangeInclusive$LT$T$GT$$u20$as$u20$core..iter..range..RangeInclusiveIteratorImpl$GT$9spec_next17h0f00df2fb6d0e402E"(ptr align 8 %self) #14
  %_0.0 = extractvalue { i64, i64 } %0, 0
  %_0.1 = extractvalue { i64, i64 } %0, 1
  %1 = insertvalue { i64, i64 } poison, i64 %_0.0, 0
  %2 = insertvalue { i64, i64 } %1, i64 %_0.1, 1
  ret { i64, i64 } %2
}

; core::sync::atomic::AtomicUsize::load
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @_ZN4core4sync6atomic11AtomicUsize4load17hc1325ac4b52c1b05E(ptr align 8 %self, i8 %order) unnamed_addr #0 {
start:
; call core::sync::atomic::atomic_load
  %_0 = call i64 @_ZN4core4sync6atomic11atomic_load17h9b6ba90efb39c93dE(ptr %self, i8 %order) #14
  ret i64 %_0
}

; core::sync::atomic::AtomicUsize::store
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core4sync6atomic11AtomicUsize5store17hd81bb965d8847172E(ptr align 8 %self, i64 %val, i8 %order) unnamed_addr #0 {
start:
; call core::sync::atomic::atomic_store
  call void @_ZN4core4sync6atomic12atomic_store17he318f64a8aea65fbE(ptr %self, i64 %val, i8 %order) #14
  ret void
}

; core::sync::atomic::AtomicUsize::fetch_add
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @_ZN4core4sync6atomic11AtomicUsize9fetch_add17h31c6c38a32e51c38E(ptr align 8 %self, i64 %val, i8 %order) unnamed_addr #0 {
start:
  %_0 = alloca [8 x i8], align 8
  %_7 = zext i8 %order to i64
  switch i64 %_7, label %bb2 [
    i64 0, label %bb7
    i64 1, label %bb5
    i64 2, label %bb6
    i64 3, label %bb4
    i64 4, label %bb3
  ]

bb2:                                              ; preds = %start
  unreachable

bb7:                                              ; preds = %start
  %0 = atomicrmw add ptr %self, i64 %val monotonic, align 8
  store i64 %0, ptr %_0, align 8
  br label %bb1

bb5:                                              ; preds = %start
  %1 = atomicrmw add ptr %self, i64 %val release, align 8
  store i64 %1, ptr %_0, align 8
  br label %bb1

bb6:                                              ; preds = %start
  %2 = atomicrmw add ptr %self, i64 %val acquire, align 8
  store i64 %2, ptr %_0, align 8
  br label %bb1

bb4:                                              ; preds = %start
  %3 = atomicrmw add ptr %self, i64 %val acq_rel, align 8
  store i64 %3, ptr %_0, align 8
  br label %bb1

bb3:                                              ; preds = %start
  %4 = atomicrmw add ptr %self, i64 %val seq_cst, align 8
  store i64 %4, ptr %_0, align 8
  br label %bb1

bb1:                                              ; preds = %bb3, %bb4, %bb6, %bb5, %bb7
  %5 = load i64, ptr %_0, align 8
  ret i64 %5
}

; core::sync::atomic::atomic_load
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @_ZN4core4sync6atomic11atomic_load17h9b6ba90efb39c93dE(ptr %dst, i8 %order) unnamed_addr #0 {
start:
  %_7 = alloca [48 x i8], align 8
  %_5 = alloca [48 x i8], align 8
  %_0 = alloca [8 x i8], align 8
  %_3 = zext i8 %order to i64
  switch i64 %_3, label %bb1 [
    i64 0, label %bb6
    i64 1, label %bb3
    i64 2, label %bb5
    i64 3, label %bb2
    i64 4, label %bb4
  ]

bb1:                                              ; preds = %start
  unreachable

bb6:                                              ; preds = %start
  %0 = load atomic i64, ptr %dst monotonic, align 8
  store i64 %0, ptr %_0, align 8
  br label %bb7

bb3:                                              ; preds = %start
  store ptr @alloc_b55f69a00b865c3d8c5f6dad0122f5bd, ptr %_5, align 8
  %1 = getelementptr inbounds i8, ptr %_5, i64 8
  store i64 1, ptr %1, align 8
  %2 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %3 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %4 = getelementptr inbounds i8, ptr %_5, i64 32
  store ptr %2, ptr %4, align 8
  %5 = getelementptr inbounds i8, ptr %4, i64 8
  store i64 %3, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %_5, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  store i64 0, ptr %7, align 8
; call core::panicking::panic_fmt
  call void @_ZN4core9panicking9panic_fmt17hc49fc28484033487E(ptr align 8 %_5, ptr align 8 @alloc_9e3a721e4192284d14075f86dfc4f099) #15
  unreachable

bb5:                                              ; preds = %start
  %8 = load atomic i64, ptr %dst acquire, align 8
  store i64 %8, ptr %_0, align 8
  br label %bb7

bb2:                                              ; preds = %start
  store ptr @alloc_0175cc81e1f5c8f5b757d44420d81e68, ptr %_7, align 8
  %9 = getelementptr inbounds i8, ptr %_7, i64 8
  store i64 1, ptr %9, align 8
  %10 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %11 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %12 = getelementptr inbounds i8, ptr %_7, i64 32
  store ptr %10, ptr %12, align 8
  %13 = getelementptr inbounds i8, ptr %12, i64 8
  store i64 %11, ptr %13, align 8
  %14 = getelementptr inbounds i8, ptr %_7, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %14, align 8
  %15 = getelementptr inbounds i8, ptr %14, i64 8
  store i64 0, ptr %15, align 8
; call core::panicking::panic_fmt
  call void @_ZN4core9panicking9panic_fmt17hc49fc28484033487E(ptr align 8 %_7, ptr align 8 @alloc_6abb0457cb178205e8fd1b354df1db12) #15
  unreachable

bb4:                                              ; preds = %start
  %16 = load atomic i64, ptr %dst seq_cst, align 8
  store i64 %16, ptr %_0, align 8
  br label %bb7

bb7:                                              ; preds = %bb4, %bb5, %bb6
  %17 = load i64, ptr %_0, align 8
  ret i64 %17
}

; core::sync::atomic::atomic_store
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core4sync6atomic12atomic_store17he318f64a8aea65fbE(ptr %dst, i64 %val, i8 %order) unnamed_addr #0 {
start:
  %_8 = alloca [48 x i8], align 8
  %_6 = alloca [48 x i8], align 8
  %_4 = zext i8 %order to i64
  switch i64 %_4, label %bb1 [
    i64 0, label %bb6
    i64 1, label %bb5
    i64 2, label %bb3
    i64 3, label %bb2
    i64 4, label %bb4
  ]

bb1:                                              ; preds = %start
  unreachable

bb6:                                              ; preds = %start
  store atomic i64 %val, ptr %dst monotonic, align 8
  br label %bb7

bb5:                                              ; preds = %start
  store atomic i64 %val, ptr %dst release, align 8
  br label %bb7

bb3:                                              ; preds = %start
  store ptr @alloc_d30e09dd75f4c40be0845475870856e6, ptr %_6, align 8
  %0 = getelementptr inbounds i8, ptr %_6, i64 8
  store i64 1, ptr %0, align 8
  %1 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %2 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %3 = getelementptr inbounds i8, ptr %_6, i64 32
  store ptr %1, ptr %3, align 8
  %4 = getelementptr inbounds i8, ptr %3, i64 8
  store i64 %2, ptr %4, align 8
  %5 = getelementptr inbounds i8, ptr %_6, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %5, i64 8
  store i64 0, ptr %6, align 8
; call core::panicking::panic_fmt
  call void @_ZN4core9panicking9panic_fmt17hc49fc28484033487E(ptr align 8 %_6, ptr align 8 @alloc_cbff13f8de7390bd0c1ed709ab3bc81d) #15
  unreachable

bb2:                                              ; preds = %start
  store ptr @alloc_9b1e61e0572571d4b583b134cc9efd32, ptr %_8, align 8
  %7 = getelementptr inbounds i8, ptr %_8, i64 8
  store i64 1, ptr %7, align 8
  %8 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %9 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %10 = getelementptr inbounds i8, ptr %_8, i64 32
  store ptr %8, ptr %10, align 8
  %11 = getelementptr inbounds i8, ptr %10, i64 8
  store i64 %9, ptr %11, align 8
  %12 = getelementptr inbounds i8, ptr %_8, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %12, align 8
  %13 = getelementptr inbounds i8, ptr %12, i64 8
  store i64 0, ptr %13, align 8
; call core::panicking::panic_fmt
  call void @_ZN4core9panicking9panic_fmt17hc49fc28484033487E(ptr align 8 %_8, ptr align 8 @alloc_cf705c09b2a84d97072e92cdb5f56b17) #15
  unreachable

bb4:                                              ; preds = %start
  store atomic i64 %val, ptr %dst seq_cst, align 8
  br label %bb7

bb7:                                              ; preds = %bb4, %bb5, %bb6
  ret void
}

; core::array::try_from_fn
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core5array11try_from_fn17hd7f029f869ba4659E(ptr sret([16 x i8]) align 1 %_0, ptr align 1 %cb.0, ptr align 1 %cb.1) unnamed_addr #0 {
start:
  %array1 = alloca [16 x i8], align 1
  %_8 = alloca [16 x i8], align 1
  %array = alloca [16 x i8], align 1
  call void @llvm.memset.p0.i64(ptr align 1 %array, i8 undef, i64 16, i1 false)
; call core::array::try_from_fn_erased
  call void @_ZN4core5array18try_from_fn_erased17h142d1525fc11388fE(ptr align 1 %array, i64 16, ptr align 1 %cb.0, ptr align 1 %cb.1) #14
  br label %bb3

bb3:                                              ; preds = %start
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %array1, ptr align 1 %array, i64 16, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_8, ptr align 1 %array1, i64 16, i1 false)
; call <core::ops::try_trait::NeverShortCircuit<T> as core::ops::try_trait::Try>::from_output
  call void @"_ZN94_$LT$core..ops..try_trait..NeverShortCircuit$LT$T$GT$$u20$as$u20$core..ops..try_trait..Try$GT$11from_output17h4c8a75f1d068ec78E"(ptr sret([16 x i8]) align 1 %_0, ptr align 1 %_8) #14
  br label %bb6

bb6:                                              ; preds = %bb4, %bb3
  ret void

bb4:                                              ; No predecessors!
; call <core::ops::try_trait::NeverShortCircuit<T> as core::ops::try_trait::FromResidual<core::ops::try_trait::NeverShortCircuitResidual>>::from_residual
  call void @"_ZN158_$LT$core..ops..try_trait..NeverShortCircuit$LT$T$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..ops..try_trait..NeverShortCircuitResidual$GT$$GT$13from_residual17hf80d254b2d03953cE"(ptr sret([16 x i8]) align 1 %_0) #14
  br label %bb6

bb2:                                              ; No predecessors!
  unreachable
}

; core::array::Guard<T>::push_unchecked
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array14Guard$LT$T$GT$14push_unchecked17hc5360192e547b1b5E"(ptr align 8 %self, i8 %item) unnamed_addr #0 {
start:
  %_13 = alloca [1 x i8], align 1
  %self1 = alloca [8 x i8], align 8
  %self.0 = load ptr, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %self.1 = load i64, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %self, i64 16
  %index = load i64, ptr %1, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hc49bed520081e145E"(i64 %index, i64 %self.1, ptr align 8 @alloc_c1eb65d8576c1851388b4960911d9ce4) #14
  %self2 = getelementptr inbounds nuw i8, ptr %self.0, i64 %index
  store i8 %item, ptr %_13, align 1
  %2 = load i8, ptr %_13, align 1
  store i8 %2, ptr %self2, align 1
  %3 = getelementptr inbounds i8, ptr %self, i64 16
  %4 = load i64, ptr %3, align 8
  store i64 %4, ptr %self1, align 8
  br label %bb5

bb5:                                              ; preds = %bb1
  %5 = load i64, ptr %self1, align 8
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %5, i64 1, ptr align 8 @alloc_a950e1fcf72a54c3b4c4a808b1a03ffa) #14
  br label %bb6

bb6:                                              ; preds = %bb5
  %6 = load i64, ptr %self1, align 8
  %_5 = add nuw i64 %6, 1
  %7 = getelementptr inbounds i8, ptr %self, i64 16
  store i64 %_5, ptr %7, align 8
  ret void

bb3:                                              ; No predecessors!
  unreachable

bb4:                                              ; No predecessors!
  unreachable
}

; core::array::try_from_fn_erased
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core5array18try_from_fn_erased17h142d1525fc11388fE(ptr align 1 %buffer.0, i64 %buffer.1, ptr align 1 %0, ptr align 1 %1) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %2 = alloca [16 x i8], align 8
  %_21 = alloca [0 x i8], align 1
  %self = alloca [1 x i8], align 1
  %_7 = alloca [1 x i8], align 1
  %guard = alloca [24 x i8], align 8
  %_0 = alloca [0 x i8], align 1
  %generator = alloca [16 x i8], align 8
  store ptr %0, ptr %generator, align 8
  %3 = getelementptr inbounds i8, ptr %generator, i64 8
  store ptr %1, ptr %3, align 8
  store ptr %buffer.0, ptr %guard, align 8
  %4 = getelementptr inbounds i8, ptr %guard, i64 8
  store i64 %buffer.1, ptr %4, align 8
  %5 = getelementptr inbounds i8, ptr %guard, i64 16
  store i64 0, ptr %5, align 8
  br label %bb1

bb1:                                              ; preds = %bb6, %start
  %6 = getelementptr inbounds i8, ptr %guard, i64 16
  %_5 = load i64, ptr %6, align 8
  %_17.0 = load ptr, ptr %guard, align 8
  %7 = getelementptr inbounds i8, ptr %guard, i64 8
  %_17.1 = load i64, ptr %7, align 8
  %_4 = icmp ult i64 %_5, %_17.1
  br i1 %_4, label %bb2, label %bb7

bb7:                                              ; preds = %bb1
  %t.0 = load ptr, ptr %guard, align 8
  %8 = getelementptr inbounds i8, ptr %guard, i64 8
  %t.1 = load i64, ptr %8, align 8
  %9 = getelementptr inbounds i8, ptr %guard, i64 16
  %t = load i64, ptr %9, align 8
  br label %bb9

bb2:                                              ; preds = %bb1
  %10 = getelementptr inbounds i8, ptr %guard, i64 16
  %_12 = load i64, ptr %10, align 8
; call core::ops::try_trait::NeverShortCircuit<T>::wrap_mut_1::{{closure}}
  %_9 = call i8 @"_ZN4core3ops9try_trait26NeverShortCircuit$LT$T$GT$10wrap_mut_128_$u7b$$u7b$closure$u7d$$u7d$17h8b7ad2441085dc6bE"(ptr align 8 %generator, i64 %_12) #14
  br label %bb3

bb9:                                              ; preds = %bb8, %bb7
  ret void

bb3:                                              ; preds = %bb2
; call <core::ops::try_trait::NeverShortCircuit<T> as core::ops::try_trait::Try>::branch
  %11 = call i8 @"_ZN94_$LT$core..ops..try_trait..NeverShortCircuit$LT$T$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17hab34c1accb7c7c09E"(i8 %_9) #14
  store i8 %11, ptr %self, align 1
  br label %bb4

bb4:                                              ; preds = %bb3
  %12 = load i8, ptr %self, align 1
  br label %bb14

bb14:                                             ; preds = %bb4
  %c = load i8, ptr %self, align 1
  store i8 %c, ptr %_7, align 1
  %item = load i8, ptr %_7, align 1
; call core::array::Guard<T>::push_unchecked
  call void @"_ZN4core5array14Guard$LT$T$GT$14push_unchecked17hc5360192e547b1b5E"(ptr align 8 %guard, i8 %item) #14
  br label %bb6

bb6:                                              ; preds = %bb14
  br label %bb1

bb13:                                             ; No predecessors!
  call void @llvm.trap()
  call void @llvm.trap()
  call void @llvm.trap()
; call core::ptr::drop_in_place<core::array::Guard<u8>>
  call void @"_ZN4core3ptr49drop_in_place$LT$core..array..Guard$LT$u8$GT$$GT$17h673dc5c8847d92d8E"(ptr align 8 %guard) #14
  br label %bb8

bb8:                                              ; preds = %bb13
  br label %bb9

bb5:                                              ; No predecessors!
  unreachable

bb12:                                             ; No predecessors!
; call core::ptr::drop_in_place<core::array::Guard<u8>>
  call void @"_ZN4core3ptr49drop_in_place$LT$core..array..Guard$LT$u8$GT$$GT$17h673dc5c8847d92d8E"(ptr align 8 %guard) #16
  br label %bb10

bb10:                                             ; preds = %bb12
  %13 = load ptr, ptr %2, align 8
  %14 = getelementptr inbounds i8, ptr %2, i64 8
  %15 = load i32, ptr %14, align 8
  %16 = insertvalue { ptr, i32 } poison, ptr %13, 0
  %17 = insertvalue { ptr, i32 } %16, i32 %15, 1
  resume { ptr, i32 } %17
}

; core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17h3c562e2db464758cE"(ptr sret([48 x i8]) align 8 %_0, ptr align 8 %self.0, i64 %self.1) unnamed_addr #0 {
start:
  %f = alloca [16 x i8], align 8
  %_15 = alloca [40 x i8], align 8
  %_4 = alloca [16 x i8], align 8
  %self1 = alloca [8 x i8], align 8
  %self = alloca [16 x i8], align 8
  store ptr %self.0, ptr %self1, align 8
  %0 = load ptr, ptr %self1, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  %_9 = load i64, ptr %1, align 8
  %2 = load ptr, ptr %self1, align 8
  %_10 = load i64, ptr %2, align 8
  %_6 = sub nuw i64 %_9, %_10
  %_5 = icmp ugt i64 %_6, 0
  br i1 %_5, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %3 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %4 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %3, ptr %self, align 8
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %4, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %6, ptr %_4, align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %7, align 8
  %8 = load ptr, ptr %_4, align 8
  %9 = getelementptr inbounds i8, ptr %_4, i64 8
  %10 = load i64, ptr %9, align 8
  store ptr %8, ptr %f, align 8
  %11 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %10, ptr %11, align 8
  store i64 0, ptr %_0, align 8
  br label %bb5

bb1:                                              ; preds = %start
  %12 = load ptr, ptr %self1, align 8
  %value = load i64, ptr %12, align 8
  br label %bb3

bb5:                                              ; preds = %bb8, %bb2
  ret void

bb3:                                              ; preds = %bb1
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %value, i64 1, ptr align 8 @alloc_ff966b345d1e2cc01dc78ffc82fcc559) #14
  br label %bb4

bb4:                                              ; preds = %bb3
  %_11 = add nuw i64 %value, 1
  %13 = load ptr, ptr %self1, align 8
  store i64 %_11, ptr %13, align 8
  %14 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %value, ptr %14, align 8
  store i64 1, ptr %self, align 8
  %15 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %15, ptr %_4, align 8
  %16 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %16, align 8
  %17 = load ptr, ptr %_4, align 8
  %18 = getelementptr inbounds i8, ptr %_4, i64 8
  %19 = load i64, ptr %18, align 8
  store ptr %17, ptr %f, align 8
  %20 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %19, ptr %20, align 8
  %21 = getelementptr inbounds i8, ptr %self, i64 8
  %x = load i64, ptr %21, align 8
  %_25.0 = load ptr, ptr %_4, align 8
  %22 = getelementptr inbounds i8, ptr %_4, i64 8
  %_25.1 = load i64, ptr %22, align 8
  %self.02 = load ptr, ptr %_4, align 8
  %23 = getelementptr inbounds i8, ptr %_4, i64 8
  %self.13 = load i64, ptr %23, align 8
  br label %bb6

bb6:                                              ; preds = %bb4
  %24 = load ptr, ptr %_4, align 8
  %25 = getelementptr inbounds i8, ptr %_4, i64 8
  %_19 = load i64, ptr %25, align 8
; call <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check
  call void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$13get_unchecked18precondition_check17hff5b7d722b1e5766E"(i64 %x, i64 %_19, ptr align 8 @alloc_6d0f5de3526dcf1c1bed664a017ff4d3) #14
  br label %bb8

bb8:                                              ; preds = %bb6
  %26 = load ptr, ptr %_4, align 8
  %27 = getelementptr inbounds i8, ptr %_4, i64 8
  %_21 = load i64, ptr %27, align 8
  %_20 = icmp ult i64 %x, %_21
  %28 = load ptr, ptr %_4, align 8
  %29 = getelementptr inbounds i8, ptr %_4, i64 8
  %30 = load i64, ptr %29, align 8
  %self4 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u64; 5]>", ptr %28, i64 %x
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_15, ptr align 8 %self4, i64 40, i1 false)
  %31 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %31, ptr align 8 %_15, i64 40, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb5
}

; core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal { i64, i64 } @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17h5491f5036cfbf5ffE"(ptr align 8 %self.0, i64 %self.1) unnamed_addr #0 {
start:
  %f = alloca [16 x i8], align 8
  %_4 = alloca [16 x i8], align 8
  %self1 = alloca [8 x i8], align 8
  %self = alloca [16 x i8], align 8
  %_0 = alloca [16 x i8], align 8
  store ptr %self.0, ptr %self1, align 8
  %0 = load ptr, ptr %self1, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  %_9 = load i64, ptr %1, align 8
  %2 = load ptr, ptr %self1, align 8
  %_10 = load i64, ptr %2, align 8
  %_6 = sub nuw i64 %_9, %_10
  %_5 = icmp ugt i64 %_6, 0
  br i1 %_5, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %3 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %4 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %3, ptr %self, align 8
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %4, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %6, ptr %_4, align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %7, align 8
  %8 = load ptr, ptr %_4, align 8
  %9 = getelementptr inbounds i8, ptr %_4, i64 8
  %10 = load i64, ptr %9, align 8
  store ptr %8, ptr %f, align 8
  %11 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %10, ptr %11, align 8
  store i64 0, ptr %_0, align 8
  br label %bb5

bb1:                                              ; preds = %start
  %12 = load ptr, ptr %self1, align 8
  %value = load i64, ptr %12, align 8
  br label %bb3

bb5:                                              ; preds = %bb8, %bb2
  %13 = load i64, ptr %_0, align 8
  %14 = getelementptr inbounds i8, ptr %_0, i64 8
  %15 = load i64, ptr %14, align 8
  %16 = insertvalue { i64, i64 } poison, i64 %13, 0
  %17 = insertvalue { i64, i64 } %16, i64 %15, 1
  ret { i64, i64 } %17

bb3:                                              ; preds = %bb1
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %value, i64 1, ptr align 8 @alloc_ff966b345d1e2cc01dc78ffc82fcc559) #14
  br label %bb4

bb4:                                              ; preds = %bb3
  %_11 = add nuw i64 %value, 1
  %18 = load ptr, ptr %self1, align 8
  store i64 %_11, ptr %18, align 8
  %19 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %value, ptr %19, align 8
  store i64 1, ptr %self, align 8
  %20 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %20, ptr %_4, align 8
  %21 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %21, align 8
  %22 = load ptr, ptr %_4, align 8
  %23 = getelementptr inbounds i8, ptr %_4, i64 8
  %24 = load i64, ptr %23, align 8
  store ptr %22, ptr %f, align 8
  %25 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %24, ptr %25, align 8
  %26 = getelementptr inbounds i8, ptr %self, i64 8
  %x = load i64, ptr %26, align 8
  %_25.0 = load ptr, ptr %_4, align 8
  %27 = getelementptr inbounds i8, ptr %_4, i64 8
  %_25.1 = load i64, ptr %27, align 8
  %self.02 = load ptr, ptr %_4, align 8
  %28 = getelementptr inbounds i8, ptr %_4, i64 8
  %self.13 = load i64, ptr %28, align 8
  br label %bb6

bb6:                                              ; preds = %bb4
  %29 = load ptr, ptr %_4, align 8
  %30 = getelementptr inbounds i8, ptr %_4, i64 8
  %_19 = load i64, ptr %30, align 8
; call <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check
  call void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$13get_unchecked18precondition_check17hff5b7d722b1e5766E"(i64 %x, i64 %_19, ptr align 8 @alloc_6d0f5de3526dcf1c1bed664a017ff4d3) #14
  br label %bb8

bb8:                                              ; preds = %bb6
  %31 = load ptr, ptr %_4, align 8
  %32 = getelementptr inbounds i8, ptr %_4, i64 8
  %_21 = load i64, ptr %32, align 8
  %_20 = icmp ult i64 %x, %_21
  %33 = load ptr, ptr %_4, align 8
  %34 = getelementptr inbounds i8, ptr %_4, i64 8
  %35 = load i64, ptr %34, align 8
  %self4 = getelementptr inbounds nuw i64, ptr %33, i64 %x
  %_15 = load i64, ptr %self4, align 8
  %36 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %_15, ptr %36, align 8
  store i64 1, ptr %_0, align 8
  br label %bb5
}

; core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17h7f12c327d7b3c1e7E"(ptr sret([32 x i8]) align 8 %_0, ptr align 8 %self.0, i64 %self.1) unnamed_addr #0 {
start:
  %f = alloca [16 x i8], align 8
  %_15 = alloca [24 x i8], align 8
  %_4 = alloca [16 x i8], align 8
  %self1 = alloca [8 x i8], align 8
  %self = alloca [16 x i8], align 8
  store ptr %self.0, ptr %self1, align 8
  %0 = load ptr, ptr %self1, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  %_9 = load i64, ptr %1, align 8
  %2 = load ptr, ptr %self1, align 8
  %_10 = load i64, ptr %2, align 8
  %_6 = sub nuw i64 %_9, %_10
  %_5 = icmp ugt i64 %_6, 0
  br i1 %_5, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %3 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %4 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %3, ptr %self, align 8
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %4, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %6, ptr %_4, align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %7, align 8
  %8 = load ptr, ptr %_4, align 8
  %9 = getelementptr inbounds i8, ptr %_4, i64 8
  %10 = load i64, ptr %9, align 8
  store ptr %8, ptr %f, align 8
  %11 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %10, ptr %11, align 8
  store i64 0, ptr %_0, align 8
  br label %bb5

bb1:                                              ; preds = %start
  %12 = load ptr, ptr %self1, align 8
  %value = load i64, ptr %12, align 8
  br label %bb3

bb5:                                              ; preds = %bb8, %bb2
  ret void

bb3:                                              ; preds = %bb1
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %value, i64 1, ptr align 8 @alloc_ff966b345d1e2cc01dc78ffc82fcc559) #14
  br label %bb4

bb4:                                              ; preds = %bb3
  %_11 = add nuw i64 %value, 1
  %13 = load ptr, ptr %self1, align 8
  store i64 %_11, ptr %13, align 8
  %14 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %value, ptr %14, align 8
  store i64 1, ptr %self, align 8
  %15 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %15, ptr %_4, align 8
  %16 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %16, align 8
  %17 = load ptr, ptr %_4, align 8
  %18 = getelementptr inbounds i8, ptr %_4, i64 8
  %19 = load i64, ptr %18, align 8
  store ptr %17, ptr %f, align 8
  %20 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %19, ptr %20, align 8
  %21 = getelementptr inbounds i8, ptr %self, i64 8
  %x = load i64, ptr %21, align 8
  %_25.0 = load ptr, ptr %_4, align 8
  %22 = getelementptr inbounds i8, ptr %_4, i64 8
  %_25.1 = load i64, ptr %22, align 8
  %self.02 = load ptr, ptr %_4, align 8
  %23 = getelementptr inbounds i8, ptr %_4, i64 8
  %self.13 = load i64, ptr %23, align 8
  br label %bb6

bb6:                                              ; preds = %bb4
  %24 = load ptr, ptr %_4, align 8
  %25 = getelementptr inbounds i8, ptr %_4, i64 8
  %_19 = load i64, ptr %25, align 8
; call <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check
  call void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$13get_unchecked18precondition_check17hff5b7d722b1e5766E"(i64 %x, i64 %_19, ptr align 8 @alloc_6d0f5de3526dcf1c1bed664a017ff4d3) #14
  br label %bb8

bb8:                                              ; preds = %bb6
  %26 = load ptr, ptr %_4, align 8
  %27 = getelementptr inbounds i8, ptr %_4, i64 8
  %_21 = load i64, ptr %27, align 8
  %_20 = icmp ult i64 %x, %_21
  %28 = load ptr, ptr %_4, align 8
  %29 = getelementptr inbounds i8, ptr %_4, i64 8
  %30 = load i64, ptr %29, align 8
  %self4 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u64; 3]>", ptr %28, i64 %x
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_15, ptr align 8 %self4, i64 24, i1 false)
  %31 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %31, ptr align 8 %_15, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb5
}

; core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17h83e271421541d69cE"(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %self.0, i64 %self.1) unnamed_addr #0 {
start:
  %f = alloca [16 x i8], align 8
  %_15 = alloca [16 x i8], align 8
  %_4 = alloca [16 x i8], align 8
  %self1 = alloca [8 x i8], align 8
  %self = alloca [16 x i8], align 8
  store ptr %self.0, ptr %self1, align 8
  %0 = load ptr, ptr %self1, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  %_9 = load i64, ptr %1, align 8
  %2 = load ptr, ptr %self1, align 8
  %_10 = load i64, ptr %2, align 8
  %_6 = sub nuw i64 %_9, %_10
  %_5 = icmp ugt i64 %_6, 0
  br i1 %_5, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %3 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %4 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %3, ptr %self, align 8
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %4, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %6, ptr %_4, align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %7, align 8
  %8 = load ptr, ptr %_4, align 8
  %9 = getelementptr inbounds i8, ptr %_4, i64 8
  %10 = load i64, ptr %9, align 8
  store ptr %8, ptr %f, align 8
  %11 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %10, ptr %11, align 8
  store i64 0, ptr %_0, align 8
  br label %bb5

bb1:                                              ; preds = %start
  %12 = load ptr, ptr %self1, align 8
  %value = load i64, ptr %12, align 8
  br label %bb3

bb5:                                              ; preds = %bb8, %bb2
  ret void

bb3:                                              ; preds = %bb1
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %value, i64 1, ptr align 8 @alloc_ff966b345d1e2cc01dc78ffc82fcc559) #14
  br label %bb4

bb4:                                              ; preds = %bb3
  %_11 = add nuw i64 %value, 1
  %13 = load ptr, ptr %self1, align 8
  store i64 %_11, ptr %13, align 8
  %14 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %value, ptr %14, align 8
  store i64 1, ptr %self, align 8
  %15 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %15, ptr %_4, align 8
  %16 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %16, align 8
  %17 = load ptr, ptr %_4, align 8
  %18 = getelementptr inbounds i8, ptr %_4, i64 8
  %19 = load i64, ptr %18, align 8
  store ptr %17, ptr %f, align 8
  %20 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %19, ptr %20, align 8
  %21 = getelementptr inbounds i8, ptr %self, i64 8
  %x = load i64, ptr %21, align 8
  %_25.0 = load ptr, ptr %_4, align 8
  %22 = getelementptr inbounds i8, ptr %_4, i64 8
  %_25.1 = load i64, ptr %22, align 8
  %self.02 = load ptr, ptr %_4, align 8
  %23 = getelementptr inbounds i8, ptr %_4, i64 8
  %self.13 = load i64, ptr %23, align 8
  br label %bb6

bb6:                                              ; preds = %bb4
  %24 = load ptr, ptr %_4, align 8
  %25 = getelementptr inbounds i8, ptr %_4, i64 8
  %_19 = load i64, ptr %25, align 8
; call <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check
  call void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$13get_unchecked18precondition_check17hff5b7d722b1e5766E"(i64 %x, i64 %_19, ptr align 8 @alloc_6d0f5de3526dcf1c1bed664a017ff4d3) #14
  br label %bb8

bb8:                                              ; preds = %bb6
  %26 = load ptr, ptr %_4, align 8
  %27 = getelementptr inbounds i8, ptr %_4, i64 8
  %_21 = load i64, ptr %27, align 8
  %_20 = icmp ult i64 %x, %_21
  %28 = load ptr, ptr %_4, align 8
  %29 = getelementptr inbounds i8, ptr %_4, i64 8
  %30 = load i64, ptr %29, align 8
  %self4 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u64; 2]>", ptr %28, i64 %x
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_15, ptr align 8 %self4, i64 16, i1 false)
  %31 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %31, ptr align 8 %_15, i64 16, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb5
}

; core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17h8ceb2f03430a553cE"(ptr sret([40 x i8]) align 8 %_0, ptr align 8 %self.0, i64 %self.1) unnamed_addr #0 {
start:
  %f = alloca [16 x i8], align 8
  %_15 = alloca [32 x i8], align 8
  %_4 = alloca [16 x i8], align 8
  %self1 = alloca [8 x i8], align 8
  %self = alloca [16 x i8], align 8
  store ptr %self.0, ptr %self1, align 8
  %0 = load ptr, ptr %self1, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  %_9 = load i64, ptr %1, align 8
  %2 = load ptr, ptr %self1, align 8
  %_10 = load i64, ptr %2, align 8
  %_6 = sub nuw i64 %_9, %_10
  %_5 = icmp ugt i64 %_6, 0
  br i1 %_5, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %3 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %4 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %3, ptr %self, align 8
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %4, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %6, ptr %_4, align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %7, align 8
  %8 = load ptr, ptr %_4, align 8
  %9 = getelementptr inbounds i8, ptr %_4, i64 8
  %10 = load i64, ptr %9, align 8
  store ptr %8, ptr %f, align 8
  %11 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %10, ptr %11, align 8
  store i64 0, ptr %_0, align 8
  br label %bb5

bb1:                                              ; preds = %start
  %12 = load ptr, ptr %self1, align 8
  %value = load i64, ptr %12, align 8
  br label %bb3

bb5:                                              ; preds = %bb8, %bb2
  ret void

bb3:                                              ; preds = %bb1
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %value, i64 1, ptr align 8 @alloc_ff966b345d1e2cc01dc78ffc82fcc559) #14
  br label %bb4

bb4:                                              ; preds = %bb3
  %_11 = add nuw i64 %value, 1
  %13 = load ptr, ptr %self1, align 8
  store i64 %_11, ptr %13, align 8
  %14 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %value, ptr %14, align 8
  store i64 1, ptr %self, align 8
  %15 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %15, ptr %_4, align 8
  %16 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %16, align 8
  %17 = load ptr, ptr %_4, align 8
  %18 = getelementptr inbounds i8, ptr %_4, i64 8
  %19 = load i64, ptr %18, align 8
  store ptr %17, ptr %f, align 8
  %20 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %19, ptr %20, align 8
  %21 = getelementptr inbounds i8, ptr %self, i64 8
  %x = load i64, ptr %21, align 8
  %_25.0 = load ptr, ptr %_4, align 8
  %22 = getelementptr inbounds i8, ptr %_4, i64 8
  %_25.1 = load i64, ptr %22, align 8
  %self.02 = load ptr, ptr %_4, align 8
  %23 = getelementptr inbounds i8, ptr %_4, i64 8
  %self.13 = load i64, ptr %23, align 8
  br label %bb6

bb6:                                              ; preds = %bb4
  %24 = load ptr, ptr %_4, align 8
  %25 = getelementptr inbounds i8, ptr %_4, i64 8
  %_19 = load i64, ptr %25, align 8
; call <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check
  call void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$13get_unchecked18precondition_check17hff5b7d722b1e5766E"(i64 %x, i64 %_19, ptr align 8 @alloc_6d0f5de3526dcf1c1bed664a017ff4d3) #14
  br label %bb8

bb8:                                              ; preds = %bb6
  %26 = load ptr, ptr %_4, align 8
  %27 = getelementptr inbounds i8, ptr %_4, i64 8
  %_21 = load i64, ptr %27, align 8
  %_20 = icmp ult i64 %x, %_21
  %28 = load ptr, ptr %_4, align 8
  %29 = getelementptr inbounds i8, ptr %_4, i64 8
  %30 = load i64, ptr %29, align 8
  %self4 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u64; 4]>", ptr %28, i64 %x
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_15, ptr align 8 %self4, i64 32, i1 false)
  %31 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %31, ptr align 8 %_15, i64 32, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb5
}

; core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17ha7b2489d5115c341E"(ptr sret([64 x i8]) align 8 %_0, ptr align 8 %self.0, i64 %self.1) unnamed_addr #0 {
start:
  %f = alloca [16 x i8], align 8
  %_15 = alloca [56 x i8], align 8
  %_4 = alloca [16 x i8], align 8
  %self1 = alloca [8 x i8], align 8
  %self = alloca [16 x i8], align 8
  store ptr %self.0, ptr %self1, align 8
  %0 = load ptr, ptr %self1, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  %_9 = load i64, ptr %1, align 8
  %2 = load ptr, ptr %self1, align 8
  %_10 = load i64, ptr %2, align 8
  %_6 = sub nuw i64 %_9, %_10
  %_5 = icmp ugt i64 %_6, 0
  br i1 %_5, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %3 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %4 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %3, ptr %self, align 8
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %4, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %6, ptr %_4, align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %7, align 8
  %8 = load ptr, ptr %_4, align 8
  %9 = getelementptr inbounds i8, ptr %_4, i64 8
  %10 = load i64, ptr %9, align 8
  store ptr %8, ptr %f, align 8
  %11 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %10, ptr %11, align 8
  store i64 0, ptr %_0, align 8
  br label %bb5

bb1:                                              ; preds = %start
  %12 = load ptr, ptr %self1, align 8
  %value = load i64, ptr %12, align 8
  br label %bb3

bb5:                                              ; preds = %bb8, %bb2
  ret void

bb3:                                              ; preds = %bb1
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %value, i64 1, ptr align 8 @alloc_ff966b345d1e2cc01dc78ffc82fcc559) #14
  br label %bb4

bb4:                                              ; preds = %bb3
  %_11 = add nuw i64 %value, 1
  %13 = load ptr, ptr %self1, align 8
  store i64 %_11, ptr %13, align 8
  %14 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %value, ptr %14, align 8
  store i64 1, ptr %self, align 8
  %15 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %15, ptr %_4, align 8
  %16 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %16, align 8
  %17 = load ptr, ptr %_4, align 8
  %18 = getelementptr inbounds i8, ptr %_4, i64 8
  %19 = load i64, ptr %18, align 8
  store ptr %17, ptr %f, align 8
  %20 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %19, ptr %20, align 8
  %21 = getelementptr inbounds i8, ptr %self, i64 8
  %x = load i64, ptr %21, align 8
  %_25.0 = load ptr, ptr %_4, align 8
  %22 = getelementptr inbounds i8, ptr %_4, i64 8
  %_25.1 = load i64, ptr %22, align 8
  %self.02 = load ptr, ptr %_4, align 8
  %23 = getelementptr inbounds i8, ptr %_4, i64 8
  %self.13 = load i64, ptr %23, align 8
  br label %bb6

bb6:                                              ; preds = %bb4
  %24 = load ptr, ptr %_4, align 8
  %25 = getelementptr inbounds i8, ptr %_4, i64 8
  %_19 = load i64, ptr %25, align 8
; call <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check
  call void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$13get_unchecked18precondition_check17hff5b7d722b1e5766E"(i64 %x, i64 %_19, ptr align 8 @alloc_6d0f5de3526dcf1c1bed664a017ff4d3) #14
  br label %bb8

bb8:                                              ; preds = %bb6
  %26 = load ptr, ptr %_4, align 8
  %27 = getelementptr inbounds i8, ptr %_4, i64 8
  %_21 = load i64, ptr %27, align 8
  %_20 = icmp ult i64 %x, %_21
  %28 = load ptr, ptr %_4, align 8
  %29 = getelementptr inbounds i8, ptr %_4, i64 8
  %30 = load i64, ptr %29, align 8
  %self4 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u64; 7]>", ptr %28, i64 %x
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_15, ptr align 8 %self4, i64 56, i1 false)
  %31 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %31, ptr align 8 %_15, i64 56, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb5
}

; core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17hc04c71adeb3c0847E"(ptr sret([17 x i8]) align 1 %_0, ptr align 8 %self.0, i64 %self.1) unnamed_addr #0 {
start:
  %f = alloca [16 x i8], align 8
  %_15 = alloca [16 x i8], align 1
  %_4 = alloca [16 x i8], align 8
  %self1 = alloca [8 x i8], align 8
  %self = alloca [16 x i8], align 8
  store ptr %self.0, ptr %self1, align 8
  %0 = load ptr, ptr %self1, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  %_9 = load i64, ptr %1, align 8
  %2 = load ptr, ptr %self1, align 8
  %_10 = load i64, ptr %2, align 8
  %_6 = sub nuw i64 %_9, %_10
  %_5 = icmp ugt i64 %_6, 0
  br i1 %_5, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %3 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %4 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %3, ptr %self, align 8
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %4, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %6, ptr %_4, align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %7, align 8
  %8 = load ptr, ptr %_4, align 8
  %9 = getelementptr inbounds i8, ptr %_4, i64 8
  %10 = load i64, ptr %9, align 8
  store ptr %8, ptr %f, align 8
  %11 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %10, ptr %11, align 8
  store i8 0, ptr %_0, align 1
  br label %bb5

bb1:                                              ; preds = %start
  %12 = load ptr, ptr %self1, align 8
  %value = load i64, ptr %12, align 8
  br label %bb3

bb5:                                              ; preds = %bb8, %bb2
  ret void

bb3:                                              ; preds = %bb1
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %value, i64 1, ptr align 8 @alloc_ff966b345d1e2cc01dc78ffc82fcc559) #14
  br label %bb4

bb4:                                              ; preds = %bb3
  %_11 = add nuw i64 %value, 1
  %13 = load ptr, ptr %self1, align 8
  store i64 %_11, ptr %13, align 8
  %14 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %value, ptr %14, align 8
  store i64 1, ptr %self, align 8
  %15 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %15, ptr %_4, align 8
  %16 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %16, align 8
  %17 = load ptr, ptr %_4, align 8
  %18 = getelementptr inbounds i8, ptr %_4, i64 8
  %19 = load i64, ptr %18, align 8
  store ptr %17, ptr %f, align 8
  %20 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %19, ptr %20, align 8
  %21 = getelementptr inbounds i8, ptr %self, i64 8
  %x = load i64, ptr %21, align 8
  %_25.0 = load ptr, ptr %_4, align 8
  %22 = getelementptr inbounds i8, ptr %_4, i64 8
  %_25.1 = load i64, ptr %22, align 8
  %self.02 = load ptr, ptr %_4, align 8
  %23 = getelementptr inbounds i8, ptr %_4, i64 8
  %self.13 = load i64, ptr %23, align 8
  br label %bb6

bb6:                                              ; preds = %bb4
  %24 = load ptr, ptr %_4, align 8
  %25 = getelementptr inbounds i8, ptr %_4, i64 8
  %_19 = load i64, ptr %25, align 8
; call <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check
  call void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$13get_unchecked18precondition_check17hff5b7d722b1e5766E"(i64 %x, i64 %_19, ptr align 8 @alloc_6d0f5de3526dcf1c1bed664a017ff4d3) #14
  br label %bb8

bb8:                                              ; preds = %bb6
  %26 = load ptr, ptr %_4, align 8
  %27 = getelementptr inbounds i8, ptr %_4, i64 8
  %_21 = load i64, ptr %27, align 8
  %_20 = icmp ult i64 %x, %_21
  %28 = load ptr, ptr %_4, align 8
  %29 = getelementptr inbounds i8, ptr %_4, i64 8
  %30 = load i64, ptr %29, align 8
  %self4 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<[u8; 16]>", ptr %28, i64 %x
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_15, ptr align 1 %self4, i64 16, i1 false)
  %31 = getelementptr inbounds i8, ptr %_0, i64 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %31, ptr align 1 %_15, i64 16, i1 false)
  store i8 1, ptr %_0, align 1
  br label %bb5
}

; core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal { i64, i64 } @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17hf903c3629b32bc4fE"(ptr align 8 %self.0, i64 %self.1) unnamed_addr #0 {
start:
  %f = alloca [16 x i8], align 8
  %_4 = alloca [16 x i8], align 8
  %self1 = alloca [8 x i8], align 8
  %self = alloca [16 x i8], align 8
  %_0 = alloca [16 x i8], align 8
  store ptr %self.0, ptr %self1, align 8
  %0 = load ptr, ptr %self1, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  %_9 = load i64, ptr %1, align 8
  %2 = load ptr, ptr %self1, align 8
  %_10 = load i64, ptr %2, align 8
  %_6 = sub nuw i64 %_9, %_10
  %_5 = icmp ugt i64 %_6, 0
  br i1 %_5, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %3 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %4 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %3, ptr %self, align 8
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %4, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %6, ptr %_4, align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %7, align 8
  %8 = load ptr, ptr %_4, align 8
  %9 = getelementptr inbounds i8, ptr %_4, i64 8
  %10 = load i64, ptr %9, align 8
  store ptr %8, ptr %f, align 8
  %11 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %10, ptr %11, align 8
  store i64 0, ptr %_0, align 8
  br label %bb5

bb1:                                              ; preds = %start
  %12 = load ptr, ptr %self1, align 8
  %value = load i64, ptr %12, align 8
  br label %bb3

bb5:                                              ; preds = %bb8, %bb2
  %13 = load i64, ptr %_0, align 8
  %14 = getelementptr inbounds i8, ptr %_0, i64 8
  %15 = load i64, ptr %14, align 8
  %16 = insertvalue { i64, i64 } poison, i64 %13, 0
  %17 = insertvalue { i64, i64 } %16, i64 %15, 1
  ret { i64, i64 } %17

bb3:                                              ; preds = %bb1
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %value, i64 1, ptr align 8 @alloc_ff966b345d1e2cc01dc78ffc82fcc559) #14
  br label %bb4

bb4:                                              ; preds = %bb3
  %_11 = add nuw i64 %value, 1
  %18 = load ptr, ptr %self1, align 8
  store i64 %_11, ptr %18, align 8
  %19 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %value, ptr %19, align 8
  store i64 1, ptr %self, align 8
  %20 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %20, ptr %_4, align 8
  %21 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %21, align 8
  %22 = load ptr, ptr %_4, align 8
  %23 = getelementptr inbounds i8, ptr %_4, i64 8
  %24 = load i64, ptr %23, align 8
  store ptr %22, ptr %f, align 8
  %25 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %24, ptr %25, align 8
  %26 = getelementptr inbounds i8, ptr %self, i64 8
  %x = load i64, ptr %26, align 8
  %_25.0 = load ptr, ptr %_4, align 8
  %27 = getelementptr inbounds i8, ptr %_4, i64 8
  %_25.1 = load i64, ptr %27, align 8
  %self.02 = load ptr, ptr %_4, align 8
  %28 = getelementptr inbounds i8, ptr %_4, i64 8
  %self.13 = load i64, ptr %28, align 8
  br label %bb6

bb6:                                              ; preds = %bb4
  %29 = load ptr, ptr %_4, align 8
  %30 = getelementptr inbounds i8, ptr %_4, i64 8
  %_19 = load i64, ptr %30, align 8
; call <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check
  call void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$13get_unchecked18precondition_check17hff5b7d722b1e5766E"(i64 %x, i64 %_19, ptr align 8 @alloc_6d0f5de3526dcf1c1bed664a017ff4d3) #14
  br label %bb8

bb8:                                              ; preds = %bb6
  %31 = load ptr, ptr %_4, align 8
  %32 = getelementptr inbounds i8, ptr %_4, i64 8
  %_21 = load i64, ptr %32, align 8
  %_20 = icmp ult i64 %x, %_21
  %33 = load ptr, ptr %_4, align 8
  %34 = getelementptr inbounds i8, ptr %_4, i64 8
  %35 = load i64, ptr %34, align 8
  %self4 = getelementptr inbounds nuw i64, ptr %33, i64 %x
  %_15 = load i64, ptr %self4, align 8
  %36 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %_15, ptr %36, align 8
  store i64 1, ptr %_0, align 8
  br label %bb5
}

; core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17hfc3802082c92961dE"(ptr sret([40 x i8]) align 8 %_0, ptr align 8 %self.0, i64 %self.1) unnamed_addr #0 {
start:
  %f = alloca [16 x i8], align 8
  %_15 = alloca [32 x i8], align 8
  %_4 = alloca [16 x i8], align 8
  %self1 = alloca [8 x i8], align 8
  %self = alloca [16 x i8], align 8
  store ptr %self.0, ptr %self1, align 8
  %0 = load ptr, ptr %self1, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  %_9 = load i64, ptr %1, align 8
  %2 = load ptr, ptr %self1, align 8
  %_10 = load i64, ptr %2, align 8
  %_6 = sub nuw i64 %_9, %_10
  %_5 = icmp ugt i64 %_6, 0
  br i1 %_5, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %3 = load i64, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %4 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  store i64 %3, ptr %self, align 8
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %4, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %6, ptr %_4, align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %7, align 8
  %8 = load ptr, ptr %_4, align 8
  %9 = getelementptr inbounds i8, ptr %_4, i64 8
  %10 = load i64, ptr %9, align 8
  store ptr %8, ptr %f, align 8
  %11 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %10, ptr %11, align 8
  store i64 0, ptr %_0, align 8
  br label %bb5

bb1:                                              ; preds = %start
  %12 = load ptr, ptr %self1, align 8
  %value = load i64, ptr %12, align 8
  br label %bb3

bb5:                                              ; preds = %bb8, %bb2
  ret void

bb3:                                              ; preds = %bb1
; call core::num::<impl usize>::unchecked_add::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_add18precondition_check17ha53a8e05c29b6ce3E"(i64 %value, i64 1, ptr align 8 @alloc_ff966b345d1e2cc01dc78ffc82fcc559) #14
  br label %bb4

bb4:                                              ; preds = %bb3
  %_11 = add nuw i64 %value, 1
  %13 = load ptr, ptr %self1, align 8
  store i64 %_11, ptr %13, align 8
  %14 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %value, ptr %14, align 8
  store i64 1, ptr %self, align 8
  %15 = getelementptr inbounds i8, ptr %self.0, i64 16
  store ptr %15, ptr %_4, align 8
  %16 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %self.1, ptr %16, align 8
  %17 = load ptr, ptr %_4, align 8
  %18 = getelementptr inbounds i8, ptr %_4, i64 8
  %19 = load i64, ptr %18, align 8
  store ptr %17, ptr %f, align 8
  %20 = getelementptr inbounds i8, ptr %f, i64 8
  store i64 %19, ptr %20, align 8
  %21 = getelementptr inbounds i8, ptr %self, i64 8
  %x = load i64, ptr %21, align 8
  %_25.0 = load ptr, ptr %_4, align 8
  %22 = getelementptr inbounds i8, ptr %_4, i64 8
  %_25.1 = load i64, ptr %22, align 8
  %self.02 = load ptr, ptr %_4, align 8
  %23 = getelementptr inbounds i8, ptr %_4, i64 8
  %self.13 = load i64, ptr %23, align 8
  br label %bb6

bb6:                                              ; preds = %bb4
  %24 = load ptr, ptr %_4, align 8
  %25 = getelementptr inbounds i8, ptr %_4, i64 8
  %_19 = load i64, ptr %25, align 8
; call <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check
  call void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$13get_unchecked18precondition_check17hff5b7d722b1e5766E"(i64 %x, i64 %_19, ptr align 8 @alloc_6d0f5de3526dcf1c1bed664a017ff4d3) #14
  br label %bb8

bb8:                                              ; preds = %bb6
  %26 = load ptr, ptr %_4, align 8
  %27 = getelementptr inbounds i8, ptr %_4, i64 8
  %_21 = load i64, ptr %27, align 8
  %_20 = icmp ult i64 %x, %_21
  %28 = load ptr, ptr %_4, align 8
  %29 = getelementptr inbounds i8, ptr %_4, i64 8
  %30 = load i64, ptr %29, align 8
  %self4 = getelementptr inbounds nuw %"core::mem::maybe_uninit::MaybeUninit<(usize, usize, [u8; 16])>", ptr %28, i64 %x
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_15, ptr align 8 %self4, i64 32, i1 false)
  %31 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %31, ptr align 8 %_15, i64 32, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb5
}

; core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17h0dac118a2232d692E"(ptr sret([8080 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = alloca [8080 x i8], align 8
  %_2 = alloca [8064 x i8], align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_2, ptr align 8 %self, i64 8064, i1 false)
  store i64 0, ptr %_3, align 8
  %0 = getelementptr inbounds i8, ptr %_3, i64 8
  store i64 144, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_3, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 8 %_2, i64 8064, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_3, i64 8080, i1 false)
  ret void
}

; core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17h0ff281db88122b47E"(ptr sret([208 x i8]) align 8 %_0, ptr align 1 %self) unnamed_addr #0 {
start:
  %_3 = alloca [208 x i8], align 8
  %_2 = alloca [192 x i8], align 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_2, ptr align 1 %self, i64 192, i1 false)
  store i64 0, ptr %_3, align 8
  %0 = getelementptr inbounds i8, ptr %_3, i64 8
  store i64 12, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_3, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 1 %_2, i64 192, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_3, i64 208, i1 false)
  ret void
}

; core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17h44e26c08a95e2df0E"(ptr sret([6952 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = alloca [6952 x i8], align 8
  %_2 = alloca [6936 x i8], align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_2, ptr align 8 %self, i64 6936, i1 false)
  store i64 0, ptr %_3, align 8
  %0 = getelementptr inbounds i8, ptr %_3, i64 8
  store i64 289, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_3, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 8 %_2, i64 6936, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_3, i64 6952, i1 false)
  ret void
}

; core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17h743bdf75d6c2515cE"(ptr sret([9264 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = alloca [9264 x i8], align 8
  %_2 = alloca [9248 x i8], align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_2, ptr align 8 %self, i64 9248, i1 false)
  store i64 0, ptr %_3, align 8
  %0 = getelementptr inbounds i8, ptr %_3, i64 8
  store i64 289, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_3, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 8 %_2, i64 9248, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_3, i64 9264, i1 false)
  ret void
}

; core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17h89910c6c1c61791aE"(ptr sret([152 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = alloca [152 x i8], align 8
  %_2 = alloca [136 x i8], align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_2, ptr align 8 %self, i64 136, i1 false)
  store i64 0, ptr %_3, align 8
  %0 = getelementptr inbounds i8, ptr %_3, i64 8
  store i64 17, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_3, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 8 %_2, i64 136, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_3, i64 152, i1 false)
  ret void
}

; core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17ha5f4d59370b62cd9E"(ptr sret([23136 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = alloca [23136 x i8], align 8
  %_2 = alloca [23120 x i8], align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_2, ptr align 8 %self, i64 23120, i1 false)
  store i64 0, ptr %_3, align 8
  %0 = getelementptr inbounds i8, ptr %_3, i64 8
  store i64 578, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_3, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 8 %_2, i64 23120, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_3, i64 23136, i1 false)
  ret void
}

; core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17ha80ce2e88a3efc4cE"(ptr sret([4624 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = alloca [4624 x i8], align 8
  %_2 = alloca [4608 x i8], align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_2, ptr align 8 %self, i64 4608, i1 false)
  store i64 0, ptr %_3, align 8
  %0 = getelementptr inbounds i8, ptr %_3, i64 8
  store i64 144, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_3, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 8 %_2, i64 4608, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_3, i64 4624, i1 false)
  ret void
}

; core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17hae2a0c71c360f183E"(ptr sret([288 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = alloca [288 x i8], align 8
  %_2 = alloca [272 x i8], align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_2, ptr align 8 %self, i64 272, i1 false)
  store i64 0, ptr %_3, align 8
  %0 = getelementptr inbounds i8, ptr %_3, i64 8
  store i64 17, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_3, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 8 %_2, i64 272, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_3, i64 288, i1 false)
  ret void
}

; core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17hf73a437d98e3e86dE"(ptr sret([32 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = alloca [32 x i8], align 8
  %_2 = alloca [16 x i8], align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_2, ptr align 8 %self, i64 16, i1 false)
  store i64 0, ptr %_3, align 8
  %0 = getelementptr inbounds i8, ptr %_3, i64 8
  store i64 2, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_3, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 8 %_2, i64 16, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_3, i64 32, i1 false)
  ret void
}

; core::array::from_fn
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core5array7from_fn17h3afbe38aa9ab8eecE(ptr sret([16 x i8]) align 1 %_0, ptr align 1 %f.0, ptr align 1 %f.1) unnamed_addr #0 {
start:
  %_2 = alloca [16 x i8], align 1
; call core::array::try_from_fn
  call void @_ZN4core5array11try_from_fn17hd7f029f869ba4659E(ptr sret([16 x i8]) align 1 %_2, ptr align 1 %f.0, ptr align 1 %f.1) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0, ptr align 1 %_2, i64 16, i1 false)
  ret void
}

; core::array::<impl core::ops::index::Index<I> for [T; N]>::index
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN4core5array85_$LT$impl$u20$core..ops..index..Index$LT$I$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$5index17h389ca3ce22185a5dE"(ptr align 1 %self, i64 %index, ptr align 8 %0) unnamed_addr #0 {
start:
  %_5.i.i.i = alloca [16 x i8], align 8
  %1 = getelementptr inbounds i8, ptr %_5.i.i.i, i64 8
  store i64 %index, ptr %1, align 8
  store i64 1, ptr %_5.i.i.i, align 8
  %2 = getelementptr inbounds i8, ptr %_5.i.i.i, i64 8
  %new_len.i.i.i = load i64, ptr %2, align 8
  %_8.i.i.i = icmp ugt i64 %index, 9
  br i1 %_8.i.i.i, label %bb1.i.i.i, label %"_ZN4core5slice5index74_$LT$impl$u20$core..ops..index..Index$LT$I$GT$$u20$for$u20$$u5b$T$u5d$$GT$5index17h80f2ae4863889bbfE.exit"

bb1.i.i.i:                                        ; preds = %start
; call core::slice::index::slice_end_index_len_fail
  call void @_ZN4core5slice5index24slice_end_index_len_fail17heb50b9bbe4663132E(i64 %index, i64 9, ptr align 8 %0) #15
  unreachable

"_ZN4core5slice5index74_$LT$impl$u20$core..ops..index..Index$LT$I$GT$$u20$for$u20$$u5b$T$u5d$$GT$5index17h80f2ae4863889bbfE.exit": ; preds = %start
  %3 = insertvalue { ptr, i64 } poison, ptr %self, 0
  %4 = insertvalue { ptr, i64 } %3, i64 %new_len.i.i.i, 1
  %5 = insertvalue { ptr, i64 } poison, ptr %self, 0
  %6 = insertvalue { ptr, i64 } %5, i64 %new_len.i.i.i, 1
  %7 = insertvalue { ptr, i64 } poison, ptr %self, 0
  %8 = insertvalue { ptr, i64 } %7, i64 %new_len.i.i.i, 1
  %_0.0 = extractvalue { ptr, i64 } %8, 0
  %_0.1 = extractvalue { ptr, i64 } %8, 1
  %9 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %10 = insertvalue { ptr, i64 } %9, i64 %_0.1, 1
  ret { ptr, i64 } %10
}

; core::array::<impl core::ops::index::IndexMut<I> for [T; N]>::index_mut
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN4core5array88_$LT$impl$u20$core..ops..index..IndexMut$LT$I$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9index_mut17hf70689d488f7481bE"(ptr align 1 %self, i64 %index, ptr align 8 %0) unnamed_addr #0 {
start:
; call <core::ops::range::RangeTo<usize> as core::slice::index::SliceIndex<[T]>>::index_mut
  %1 = call { ptr, i64 } @"_ZN108_$LT$core..ops..range..RangeTo$LT$usize$GT$$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$9index_mut17hedaa82a3c29d03f1E"(i64 %index, ptr align 1 %self, i64 9, ptr align 8 %0) #14
  %_0.0.i = extractvalue { ptr, i64 } %1, 0
  %_0.1.i = extractvalue { ptr, i64 } %1, 1
  %_0.0 = extractvalue { ptr, i64 } %1, 0
  %_0.1 = extractvalue { ptr, i64 } %1, 1
  %2 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %3 = insertvalue { ptr, i64 } %2, i64 %_0.1, 1
  ret { ptr, i64 } %3
}

; core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h271358e2f5dffc76E"(ptr align 1 %self, ptr align 1 %other) unnamed_addr #0 {
start:
; call <T as core::array::equality::SpecArrayEq<U,_>>::spec_eq
  %_0 = call zeroext i1 @"_ZN69_$LT$T$u20$as$u20$core..array..equality..SpecArrayEq$LT$U$C$_$GT$$GT$7spec_eq17h07d7bbf30a09b131E"(ptr align 1 %self, ptr align 1 %other) #14
  ret i1 %_0
}

; core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h2aa518081be58070E"(ptr align 1 %self, ptr align 1 %other) unnamed_addr #0 {
start:
; call <T as core::array::equality::SpecArrayEq<U,_>>::spec_eq
  %_0 = call zeroext i1 @"_ZN69_$LT$T$u20$as$u20$core..array..equality..SpecArrayEq$LT$U$C$_$GT$$GT$7spec_eq17h41cb6230264a39f1E"(ptr align 1 %self, ptr align 1 %other) #14
  ret i1 %_0
}

; core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h6d8e9898dd9d4c85E"(ptr align 8 %self, ptr align 8 %other) unnamed_addr #0 {
start:
; call <T as core::array::equality::SpecArrayEq<U,_>>::spec_eq
  %_0 = call zeroext i1 @"_ZN69_$LT$T$u20$as$u20$core..array..equality..SpecArrayEq$LT$U$C$_$GT$$GT$7spec_eq17hab59d30fde77205cE"(ptr align 8 %self, ptr align 8 %other) #14
  ret i1 %_0
}

; core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %self, ptr align 1 %other) unnamed_addr #0 {
start:
; call <T as core::array::equality::SpecArrayEq<U,_>>::spec_eq
  %_0 = call zeroext i1 @"_ZN69_$LT$T$u20$as$u20$core..array..equality..SpecArrayEq$LT$U$C$_$GT$$GT$7spec_eq17hdab43b81fb2049a6E"(ptr align 1 %self, ptr align 1 %other) #14
  ret i1 %_0
}

; core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h859fe206253d1728E"(ptr align 8 %self, ptr align 8 %other) unnamed_addr #0 {
start:
; call <T as core::array::equality::SpecArrayEq<U,_>>::spec_eq
  %_0 = call zeroext i1 @"_ZN69_$LT$T$u20$as$u20$core..array..equality..SpecArrayEq$LT$U$C$_$GT$$GT$7spec_eq17h8ba13dad16149b3fE"(ptr align 8 %self, ptr align 8 %other) #14
  ret i1 %_0
}

; core::slice::<impl [T]>::copy_from_slice
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$15copy_from_slice17h9dd8a1e05b1baa82E"(ptr align 1 %self.0, i64 %self.1, ptr align 1 %src.0, i64 %src.1, ptr align 8 %0) unnamed_addr #0 {
start:
  %_3 = icmp ne i64 %self.1, %src.1
  br i1 %_3, label %bb1, label %bb2

bb2:                                              ; preds = %start
  br label %bb3

bb1:                                              ; preds = %start
; call core::slice::<impl [T]>::copy_from_slice::len_mismatch_fail
  call void @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$15copy_from_slice17len_mismatch_fail17h4edba79c204d9f9bE"(i64 %self.1, i64 %src.1, ptr align 8 %0) #15
  unreachable

bb3:                                              ; preds = %bb2
; call core::ptr::copy_nonoverlapping::precondition_check
  call void @_ZN4core3ptr19copy_nonoverlapping18precondition_check17h1af93ef5bb8d2ab6E(ptr %src.0, ptr %self.0, i64 1, i64 1, i64 %self.1, ptr align 8 @alloc_9b0170f47317373e331799536b583a9f) #14
  br label %bb5

bb5:                                              ; preds = %bb3
  %1 = mul i64 %self.1, 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %self.0, ptr align 1 %src.0, i64 %1, i1 false)
  ret void
}

; core::slice::raw::from_raw_parts
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @_ZN4core5slice3raw14from_raw_parts17h01ee7e45a67da397E(ptr %data, i64 %len, ptr align 8 %0) unnamed_addr #0 {
start:
  br label %bb1

bb1:                                              ; preds = %start
; call core::slice::raw::from_raw_parts::precondition_check
  call void @_ZN4core5slice3raw14from_raw_parts18precondition_check17h20499ad3da49ff88E(ptr %data, i64 1, i64 1, i64 %len, ptr align 8 %0) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %1 = insertvalue { ptr, i64 } poison, ptr %data, 0
  %2 = insertvalue { ptr, i64 } %1, i64 %len, 1
  ret { ptr, i64 } %2
}

; core::slice::raw::from_raw_parts::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN4core5slice3raw14from_raw_parts18precondition_check17h20499ad3da49ff88E(ptr %data, i64 %size, i64 %align, i64 %len, ptr align 8 %0) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %1 = alloca [4 x i8], align 4
  %max_len = alloca [8 x i8], align 8
  %_14 = alloca [48 x i8], align 8
  %_11 = alloca [16 x i8], align 8
  %_9 = alloca [48 x i8], align 8
  %2 = call i64 @llvm.ctpop.i64(i64 %align)
  %3 = trunc i64 %2 to i32
  store i32 %3, ptr %1, align 4
  %_18 = load i32, ptr %1, align 4
  %4 = icmp eq i32 %_18, 1
  br i1 %4, label %bb8, label %bb9

bb8:                                              ; preds = %start
  %_16 = ptrtoint ptr %data to i64
  %_17 = sub i64 %align, 1
  %_15 = and i64 %_16, %_17
  %5 = icmp eq i64 %_15, 0
  br i1 %5, label %bb6, label %bb7

bb9:                                              ; preds = %start
  store ptr @alloc_e92e94d0ff530782b571cfd99ec66aef, ptr %_14, align 8
  %6 = getelementptr inbounds i8, ptr %_14, i64 8
  store i64 1, ptr %6, align 8
  %7 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %8 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %9 = getelementptr inbounds i8, ptr %_14, i64 32
  store ptr %7, ptr %9, align 8
  %10 = getelementptr inbounds i8, ptr %9, i64 8
  store i64 %8, ptr %10, align 8
  %11 = getelementptr inbounds i8, ptr %_14, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %11, align 8
  %12 = getelementptr inbounds i8, ptr %11, i64 8
  store i64 0, ptr %12, align 8
; call core::panicking::panic_fmt
  call void @_ZN4core9panicking9panic_fmt17hc49fc28484033487E(ptr align 8 %_14, ptr align 8 @alloc_84fd0ee1b6b57a4ef5ffe86edcc9d22c) #15
  unreachable

bb6:                                              ; preds = %bb8
  %_12 = icmp eq i64 %_16, 0
  %_5 = xor i1 %_12, true
  br i1 %_5, label %bb1, label %bb4

bb7:                                              ; preds = %bb8
  br label %bb4

bb4:                                              ; preds = %bb7, %bb6
  br label %bb5

bb1:                                              ; preds = %bb6
  %_22 = icmp eq i64 %size, 0
  %13 = icmp eq i64 %size, 0
  br i1 %13, label %bb11, label %bb12

bb11:                                             ; preds = %bb1
  store i64 -1, ptr %max_len, align 8
  br label %bb14

bb12:                                             ; preds = %bb1
  br i1 %_22, label %panic, label %bb13

bb14:                                             ; preds = %bb13, %bb11
  %_23 = load i64, ptr %max_len, align 8
  %_7 = icmp ule i64 %len, %_23
  br i1 %_7, label %bb2, label %bb3

bb13:                                             ; preds = %bb12
  %14 = udiv i64 9223372036854775807, %size
  store i64 %14, ptr %max_len, align 8
  br label %bb14

panic:                                            ; preds = %bb12
; call core::panicking::panic_const::panic_const_div_by_zero
  call void @_ZN4core9panicking11panic_const23panic_const_div_by_zero17hd1b66acfd73a6e98E(ptr align 8 @alloc_97f23febd0de9d435a256e040eb42813) #15
  unreachable

bb3:                                              ; preds = %bb14
  br label %bb5

bb2:                                              ; preds = %bb14
  ret void

bb5:                                              ; preds = %bb4, %bb3
  %15 = getelementptr inbounds nuw { ptr, i64 }, ptr %_11, i64 0
  store ptr @alloc_a28e8c8fd5088943a8b5d44af697ff83, ptr %15, align 8
  %16 = getelementptr inbounds i8, ptr %15, i64 8
  store i64 279, ptr %16, align 8
  store ptr %_11, ptr %_9, align 8
  %17 = getelementptr inbounds i8, ptr %_9, i64 8
  store i64 1, ptr %17, align 8
  %18 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %19 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %20 = getelementptr inbounds i8, ptr %_9, i64 32
  store ptr %18, ptr %20, align 8
  %21 = getelementptr inbounds i8, ptr %20, i64 8
  store i64 %19, ptr %21, align 8
  %22 = getelementptr inbounds i8, ptr %_9, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %22, align 8
  %23 = getelementptr inbounds i8, ptr %22, i64 8
  store i64 0, ptr %23, align 8
; call core::panicking::panic_nounwind_fmt
  call void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8 %_9, i1 zeroext false, ptr align 8 %0) #15
  unreachable
}

; core::tuple::<impl core::cmp::PartialEq for (U,T)>::eq
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core5tuple64_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$$LP$U$C$T$RP$$GT$2eq17h3c9f146d4a7f7867E"(ptr align 8 %self, ptr align 8 %other) unnamed_addr #0 {
start:
  %_0 = alloca [1 x i8], align 1
; call core::cmp::impls::<impl core::cmp::PartialEq for u64>::eq
  %_3 = call zeroext i1 @"_ZN4core3cmp5impls54_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$u64$GT$2eq17hfd8942048f5d5838E"(ptr align 8 %self, ptr align 8 %other) #14
  br i1 %_3, label %bb2, label %bb3

bb3:                                              ; preds = %start
  store i8 0, ptr %_0, align 1
  br label %bb5

bb2:                                              ; preds = %start
  %_6 = getelementptr inbounds i8, ptr %self, i64 8
  %_7 = getelementptr inbounds i8, ptr %other, i64 8
; call core::cmp::impls::<impl core::cmp::PartialEq for u64>::eq
  %0 = call zeroext i1 @"_ZN4core3cmp5impls54_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$u64$GT$2eq17hfd8942048f5d5838E"(ptr align 8 %_6, ptr align 8 %_7) #14
  %1 = zext i1 %0 to i8
  store i8 %1, ptr %_0, align 1
  br label %bb5

bb5:                                              ; preds = %bb2, %bb3
  %2 = load i8, ptr %_0, align 1
  %3 = trunc nuw i8 %2 to i1
  ret i1 %3
}

; core::tuple::<impl core::cmp::PartialEq for (V,U,T)>::eq
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core5tuple68_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$$LP$V$C$U$C$T$RP$$GT$2eq17h1504af208955cb31E"(ptr align 8 %self, ptr align 8 %other) unnamed_addr #0 {
start:
  %_0 = alloca [1 x i8], align 1
; call core::cmp::impls::<impl core::cmp::PartialEq for u64>::eq
  %_3 = call zeroext i1 @"_ZN4core3cmp5impls54_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$u64$GT$2eq17hfd8942048f5d5838E"(ptr align 8 %self, ptr align 8 %other) #14
  br i1 %_3, label %bb2, label %bb6

bb6:                                              ; preds = %start
  br label %bb7

bb2:                                              ; preds = %start
  %_7 = getelementptr inbounds i8, ptr %self, i64 8
  %_8 = getelementptr inbounds i8, ptr %other, i64 8
; call core::cmp::impls::<impl core::cmp::PartialEq for u64>::eq
  %_6 = call zeroext i1 @"_ZN4core3cmp5impls54_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$u64$GT$2eq17hfd8942048f5d5838E"(ptr align 8 %_7, ptr align 8 %_8) #14
  br i1 %_6, label %bb4, label %bb5

bb7:                                              ; preds = %bb5, %bb6
  store i8 0, ptr %_0, align 1
  br label %bb9

bb5:                                              ; preds = %bb2
  br label %bb7

bb4:                                              ; preds = %bb2
  %_9 = getelementptr inbounds i8, ptr %self, i64 16
  %_10 = getelementptr inbounds i8, ptr %other, i64 16
; call core::cmp::impls::<impl core::cmp::PartialEq for u64>::eq
  %0 = call zeroext i1 @"_ZN4core3cmp5impls54_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$u64$GT$2eq17hfd8942048f5d5838E"(ptr align 8 %_9, ptr align 8 %_10) #14
  %1 = zext i1 %0 to i8
  store i8 %1, ptr %_0, align 1
  br label %bb9

bb9:                                              ; preds = %bb4, %bb7
  %2 = load i8, ptr %_0, align 1
  %3 = trunc nuw i8 %2 to i1
  ret i1 %3
}

; core::option::Option<T>::is_some
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core6option15Option$LT$T$GT$7is_some17hc4289163496f99cdE"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_2 = load i64, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %1 = load i64, ptr %0, align 8
  %_0 = icmp eq i64 %_2, 1
  ret i1 %_0
}

; core::option::Option<T>::unwrap_or
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core6option15Option$LT$T$GT$9unwrap_or17h9f918ae027ea2a49E"(i1 zeroext %self) unnamed_addr #0 {
start:
  %_3 = zext i1 %self to i64
  %0 = trunc nuw i64 %_3 to i1
  br i1 %0, label %bb3, label %bb2

bb3:                                              ; preds = %start
  br label %bb4

bb2:                                              ; preds = %start
  br label %bb4

bb4:                                              ; preds = %bb3, %bb2
  ret void

bb1:                                              ; No predecessors!
  unreachable
}

; core::result::Result<T,E>::expect
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h1a3f49af4364d9deE"(ptr align 8 %self, ptr align 1 %msg.0, i64 %msg.1, ptr align 8 %0) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %1 = alloca [16 x i8], align 8
  %e = alloca [16 x i8], align 8
  %2 = load ptr, ptr %self, align 8
  %3 = ptrtoint ptr %2 to i64
  %4 = icmp eq i64 %3, 0
  %_3 = select i1 %4, i64 0, i64 1
  %5 = trunc nuw i64 %_3 to i1
  br i1 %5, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %6 = load ptr, ptr %self, align 8
  %7 = getelementptr inbounds i8, ptr %self, i64 8
  %8 = load i64, ptr %7, align 8
  store ptr %6, ptr %e, align 8
  %9 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %8, ptr %9, align 8
; call core::result::unwrap_failed
  call void @_ZN4core6result13unwrap_failed17h9e4c136384b1cfa3E(ptr align 1 %msg.0, i64 %msg.1, ptr align 1 %e, ptr align 8 @vtable.1, ptr align 8 %0) #15
  unreachable

bb3:                                              ; preds = %start
  %10 = getelementptr inbounds i8, ptr %self, i64 8
  %t = load i64, ptr %10, align 8
  ret i64 %t

bb4:                                              ; No predecessors!
  %11 = load ptr, ptr %1, align 8
  %12 = getelementptr inbounds i8, ptr %1, i64 8
  %13 = load i32, ptr %12, align 8
  %14 = insertvalue { ptr, i32 } poison, ptr %11, 0
  %15 = insertvalue { ptr, i32 } %14, i32 %13, 1
  resume { ptr, i32 } %15

bb1:                                              ; No predecessors!
  unreachable
}

; core::result::Result<T,E>::expect
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h250be7b870b5ab1fE"(ptr align 1 %0, ptr align 1 %msg.0, i64 %msg.1, ptr align 8 %1) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %2 = alloca [16 x i8], align 8
  %e = alloca [8 x i8], align 8
  %self = alloca [8 x i8], align 8
  store ptr %0, ptr %self, align 8
  %3 = load ptr, ptr %self, align 8
  %4 = ptrtoint ptr %3 to i64
  %5 = icmp eq i64 %4, 0
  %_3 = select i1 %5, i64 0, i64 1
  %6 = trunc nuw i64 %_3 to i1
  br i1 %6, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %7 = load ptr, ptr %self, align 8
  store ptr %7, ptr %e, align 8
; call core::result::unwrap_failed
  call void @_ZN4core6result13unwrap_failed17h9e4c136384b1cfa3E(ptr align 1 %msg.0, i64 %msg.1, ptr align 1 %e, ptr align 8 @vtable.2, ptr align 8 %1) #15
  unreachable

bb3:                                              ; preds = %start
  ret void

bb4:                                              ; No predecessors!
  %8 = load ptr, ptr %2, align 8
  %9 = getelementptr inbounds i8, ptr %2, i64 8
  %10 = load i32, ptr %9, align 8
  %11 = insertvalue { ptr, i32 } poison, ptr %8, 0
  %12 = insertvalue { ptr, i32 } %11, i32 %10, 1
  resume { ptr, i32 } %12

bb1:                                              ; No predecessors!
  unreachable
}

; core::result::Result<T,E>::expect
; Function Attrs: inlinehint nounwind nonlazybind
define internal align 1 ptr @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h47abfc140087601bE"(ptr align 8 %self, ptr align 1 %msg.0, i64 %msg.1, ptr align 8 %0) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %1 = alloca [16 x i8], align 8
  %e = alloca [24 x i8], align 8
  %2 = load i64, ptr %self, align 8
  %3 = icmp eq i64 %2, 2
  %_3 = select i1 %3, i64 0, i64 1
  %4 = trunc nuw i64 %_3 to i1
  br i1 %4, label %bb2, label %bb3

bb2:                                              ; preds = %start
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %e, ptr align 8 %self, i64 24, i1 false)
; call core::result::unwrap_failed
  call void @_ZN4core6result13unwrap_failed17h9e4c136384b1cfa3E(ptr align 1 %msg.0, i64 %msg.1, ptr align 1 %e, ptr align 8 @vtable.3, ptr align 8 %0) #15
  unreachable

bb3:                                              ; preds = %start
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  %t = load ptr, ptr %5, align 8
  ret ptr %t

bb4:                                              ; No predecessors!
  %6 = load ptr, ptr %1, align 8
  %7 = getelementptr inbounds i8, ptr %1, i64 8
  %8 = load i32, ptr %7, align 8
  %9 = insertvalue { ptr, i32 } poison, ptr %6, 0
  %10 = insertvalue { ptr, i32 } %9, i32 %8, 1
  resume { ptr, i32 } %10

bb1:                                              ; No predecessors!
  unreachable
}

; core::result::Result<T,E>::expect
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h570553249822f492E"(ptr align 8 %self, ptr align 1 %msg.0, i64 %msg.1, ptr align 8 %0) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %1 = alloca [16 x i8], align 8
  %e = alloca [16 x i8], align 8
  %t = alloca [8 x i8], align 1
  %2 = load ptr, ptr %self, align 8
  %3 = ptrtoint ptr %2 to i64
  %4 = icmp eq i64 %3, 0
  %_3 = select i1 %4, i64 0, i64 1
  %5 = trunc nuw i64 %_3 to i1
  br i1 %5, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %6 = load ptr, ptr %self, align 8
  %7 = getelementptr inbounds i8, ptr %self, i64 8
  %8 = load i64, ptr %7, align 8
  store ptr %6, ptr %e, align 8
  %9 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %8, ptr %9, align 8
; call core::result::unwrap_failed
  call void @_ZN4core6result13unwrap_failed17h9e4c136384b1cfa3E(ptr align 1 %msg.0, i64 %msg.1, ptr align 1 %e, ptr align 8 @vtable.4, ptr align 8 %0) #15
  unreachable

bb3:                                              ; preds = %start
  %10 = getelementptr inbounds i8, ptr %self, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %t, ptr align 8 %10, i64 8, i1 false)
  %11 = load i64, ptr %t, align 1
  ret i64 %11

bb4:                                              ; No predecessors!
  %12 = load ptr, ptr %1, align 8
  %13 = getelementptr inbounds i8, ptr %1, i64 8
  %14 = load i32, ptr %13, align 8
  %15 = insertvalue { ptr, i32 } poison, ptr %12, 0
  %16 = insertvalue { ptr, i32 } %15, i32 %14, 1
  resume { ptr, i32 } %16

bb1:                                              ; No predecessors!
  unreachable
}

; core::result::Result<T,E>::expect
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h58a6929434be20e0E"(ptr align 1 %0, ptr align 1 %msg.0, i64 %msg.1, ptr align 8 %1) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %2 = alloca [16 x i8], align 8
  %e = alloca [8 x i8], align 8
  %self = alloca [8 x i8], align 8
  store ptr %0, ptr %self, align 8
  %3 = load ptr, ptr %self, align 8
  %4 = ptrtoint ptr %3 to i64
  %5 = icmp eq i64 %4, 0
  %_3 = select i1 %5, i64 0, i64 1
  %6 = trunc nuw i64 %_3 to i1
  br i1 %6, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %7 = load ptr, ptr %self, align 8
  store ptr %7, ptr %e, align 8
; call core::result::unwrap_failed
  call void @_ZN4core6result13unwrap_failed17h9e4c136384b1cfa3E(ptr align 1 %msg.0, i64 %msg.1, ptr align 1 %e, ptr align 8 @vtable.5, ptr align 8 %1) #15
  unreachable

bb3:                                              ; preds = %start
  ret void

bb4:                                              ; No predecessors!
  %8 = load ptr, ptr %2, align 8
  %9 = getelementptr inbounds i8, ptr %2, i64 8
  %10 = load i32, ptr %9, align 8
  %11 = insertvalue { ptr, i32 } poison, ptr %8, 0
  %12 = insertvalue { ptr, i32 } %11, i32 %10, 1
  resume { ptr, i32 } %12

bb1:                                              ; No predecessors!
  unreachable
}

; core::result::Result<T,E>::expect
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h8081aa36d77a1c7eE"(ptr sret([16 x i8]) align 1 %t, ptr align 8 %self, ptr align 1 %msg.0, i64 %msg.1, ptr align 8 %0) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %1 = alloca [16 x i8], align 8
  %e = alloca [16 x i8], align 8
  %2 = load i8, ptr %self, align 8
  %3 = trunc nuw i8 %2 to i1
  %_3 = zext i1 %3 to i64
  %4 = trunc nuw i64 %_3 to i1
  br i1 %4, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %5 = getelementptr inbounds i8, ptr %self, i64 8
  %6 = load ptr, ptr %5, align 8
  %7 = getelementptr inbounds i8, ptr %5, i64 8
  %8 = load i64, ptr %7, align 8
  store ptr %6, ptr %e, align 8
  %9 = getelementptr inbounds i8, ptr %e, i64 8
  store i64 %8, ptr %9, align 8
; call core::result::unwrap_failed
  call void @_ZN4core6result13unwrap_failed17h9e4c136384b1cfa3E(ptr align 1 %msg.0, i64 %msg.1, ptr align 1 %e, ptr align 8 @vtable.6, ptr align 8 %0) #15
  unreachable

bb3:                                              ; preds = %start
  %10 = getelementptr inbounds i8, ptr %self, i64 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %t, ptr align 1 %10, i64 16, i1 false)
  ret void

bb4:                                              ; No predecessors!
  %11 = load ptr, ptr %1, align 8
  %12 = getelementptr inbounds i8, ptr %1, i64 8
  %13 = load i32, ptr %12, align 8
  %14 = insertvalue { ptr, i32 } poison, ptr %11, 0
  %15 = insertvalue { ptr, i32 } %14, i32 %13, 1
  resume { ptr, i32 } %15

bb1:                                              ; No predecessors!
  unreachable
}

; core::result::Result<T,E>::is_err
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core6result19Result$LT$T$C$E$GT$6is_err17h3645aee6148a1928E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %0 = load ptr, ptr %self, align 8
  %1 = ptrtoint ptr %0 to i64
  %2 = icmp eq i64 %1, 0
  %_3 = select i1 %2, i64 0, i64 1
  %_2 = icmp eq i64 %_3, 0
  %_0 = xor i1 %_2, true
  ret i1 %_0
}

; core::result::Result<T,E>::is_err
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN4core6result19Result$LT$T$C$E$GT$6is_err17h7384aa11ff037724E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %0 = load ptr, ptr %self, align 8
  %1 = ptrtoint ptr %0 to i64
  %2 = icmp eq i64 %1, 0
  %_3 = select i1 %2, i64 0, i64 1
  %_2 = icmp eq i64 %_3, 0
  %_0 = xor i1 %_2, true
  ret i1 %_0
}

; core::result::Result<T,E>::map_err
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core6result19Result$LT$T$C$E$GT$7map_err17h1bd886c68be95901E"(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %self, ptr %op.0, i64 %op.1) unnamed_addr #0 {
start:
  %_1.i = alloca [16 x i8], align 8
  %_6 = alloca [24 x i8], align 8
  %0 = load i8, ptr %self, align 8
  %1 = trunc nuw i8 %0 to i1
  %_3 = zext i1 %1 to i64
  %2 = trunc nuw i64 %_3 to i1
  br i1 %2, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %3 = getelementptr inbounds i8, ptr %self, i64 1
  %4 = load i8, ptr %3, align 1
  %e = trunc nuw i8 %4 to i1
  store ptr %op.0, ptr %_1.i, align 8
  %5 = getelementptr inbounds i8, ptr %_1.i, i64 8
  store i64 %op.1, ptr %5, align 8
; call <zerocopy::error::ConvertError<zerocopy::error::AlignmentError<Src,Dst>,zerocopy::error::SizeError<Src,Dst>,core::convert::Infallible> as zerocopy::pointer::ptr::_casts::TryWithError<NewSrc>>::map
  call void @"_ZN238_$LT$zerocopy..error..ConvertError$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$C$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$C$core..convert..Infallible$GT$$u20$as$u20$zerocopy..pointer..ptr.._casts..TryWithError$LT$NewSrc$GT$$GT$3map17h2a80ab23a5914275E"(ptr sret([24 x i8]) align 8 %_6, i1 zeroext %e, ptr align 8 %_1.i) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_6, i64 24, i1 false)
  br label %bb5

bb3:                                              ; preds = %start
  %6 = getelementptr inbounds i8, ptr %self, i64 8
  %t = load ptr, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %t, ptr %7, align 8
  store i64 2, ptr %_0, align 8
  br label %bb5

bb5:                                              ; preds = %bb2, %bb3
  ret void

bb1:                                              ; No predecessors!
  unreachable
}

; core::result::Result<T,E>::map_err
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN4core6result19Result$LT$T$C$E$GT$7map_err17hffd1455effdf2821E"(ptr sret([32 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_8 = alloca [24 x i8], align 8
  %_6 = alloca [24 x i8], align 8
  %e = alloca [24 x i8], align 8
  %t = alloca [24 x i8], align 8
  %_3 = load i64, ptr %self, align 8
  %0 = trunc nuw i64 %_3 to i1
  br i1 %0, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %self, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %e, ptr align 8 %1, i64 24, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_8, ptr align 8 %e, i64 24, i1 false)
; call zerocopy::error::ConvertError<zerocopy::error::AlignmentError<Src,Dst>,zerocopy::error::SizeError<Src,Dst>,core::convert::Infallible>::map_src
  call void @"_ZN8zerocopy5error142ConvertError$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$C$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$C$core..convert..Infallible$GT$7map_src17h3bcf6f9550f87e96E"(ptr sret([24 x i8]) align 8 %_6, ptr align 8 %_8) #14
  %2 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %2, ptr align 8 %_6, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb5

bb3:                                              ; preds = %start
  %3 = getelementptr inbounds i8, ptr %self, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %t, ptr align 8 %3, i64 24, i1 false)
  %4 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %4, ptr align 8 %t, i64 24, i1 false)
  store i64 0, ptr %_0, align 8
  br label %bb5

bb5:                                              ; preds = %bb2, %bb3
  ret void

bb1:                                              ; No predecessors!
  unreachable
}

; core::ub_checks::maybe_is_nonoverlapping::runtime
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @_ZN4core9ub_checks23maybe_is_nonoverlapping7runtime17h87d6f7c633fc7293E(ptr %src, ptr %dst, i64 %size, i64 %count) unnamed_addr #0 {
start:
  %diff = alloca [8 x i8], align 8
  %_9 = alloca [16 x i8], align 8
  %src_usize = ptrtoint ptr %src to i64
  %dst_usize = ptrtoint ptr %dst to i64
  %0 = call { i64, i1 } @llvm.umul.with.overflow.i64(i64 %size, i64 %count)
  %_14.0 = extractvalue { i64, i1 } %0, 0
  %_14.1 = extractvalue { i64, i1 } %0, 1
  br i1 %_14.1, label %bb1, label %bb3

bb3:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %_9, i64 8
  store i64 %_14.0, ptr %1, align 8
  store i64 1, ptr %_9, align 8
  %2 = getelementptr inbounds i8, ptr %_9, i64 8
  %size1 = load i64, ptr %2, align 8
  %_22 = icmp ult i64 %src_usize, %dst_usize
  br i1 %_22, label %bb4, label %bb5

bb1:                                              ; preds = %start
; call core::panicking::panic_nounwind
  call void @_ZN4core9panicking14panic_nounwind17h681d69c581350003E(ptr align 1 @alloc_763310d78c99c2c1ad3f8a9821e942f3, i64 61) #15
  unreachable

bb5:                                              ; preds = %bb3
  %3 = sub i64 %src_usize, %dst_usize
  store i64 %3, ptr %diff, align 8
  br label %bb6

bb4:                                              ; preds = %bb3
  %4 = sub i64 %dst_usize, %src_usize
  store i64 %4, ptr %diff, align 8
  br label %bb6

bb6:                                              ; preds = %bb4, %bb5
  %_11 = load i64, ptr %diff, align 8
  %_0 = icmp uge i64 %_11, %size1
  ret i1 %_0
}

; <usize as zerocopy::PointerMetadata>::to_elem_count
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN51_$LT$usize$u20$as$u20$zerocopy..PointerMetadata$GT$13to_elem_count17h9137fabb3c28584aE"(i64 %self) unnamed_addr #0 {
start:
  ret i64 %self
}

; <&mut T as core::fmt::Display>::fmt
; Function Attrs: nounwind nonlazybind
define internal zeroext i1 @"_ZN52_$LT$$RF$mut$u20$T$u20$as$u20$core..fmt..Display$GT$3fmt17h39130a453e30f3adE"(ptr align 8 %self, ptr align 8 %f) unnamed_addr #1 {
start:
  %_4 = load ptr, ptr %self, align 8
; call core::fmt::num::imp::<impl core::fmt::Display for u64>::fmt
  %_0 = call zeroext i1 @"_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17h7601fb479c860baeE"(ptr align 8 %_4, ptr align 8 %f) #14
  ret i1 %_0
}

; <() as std::process::Termination>::report
; Function Attrs: inlinehint nounwind nonlazybind
define internal i8 @"_ZN54_$LT$$LP$$RP$$u20$as$u20$std..process..Termination$GT$6report17h2631335329a91021E"() unnamed_addr #0 {
start:
  ret i8 0
}

; <() as zerocopy::PointerMetadata>::to_elem_count
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN54_$LT$$LP$$RP$$u20$as$u20$zerocopy..PointerMetadata$GT$13to_elem_count17h01919dbaceb5bfd3E"() unnamed_addr #0 {
start:
  ret i64 0
}

; <() as zerocopy::PointerMetadata>::from_elem_count
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN54_$LT$$LP$$RP$$u20$as$u20$zerocopy..PointerMetadata$GT$15from_elem_count17h94cd1d1a56a5f00dE"(i64 %_elems) unnamed_addr #0 {
start:
  ret void
}

; <() as zerocopy::PointerMetadata>::size_for_metadata
; Function Attrs: inlinehint nounwind nonlazybind
define internal { i64, i64 } @"_ZN54_$LT$$LP$$RP$$u20$as$u20$zerocopy..PointerMetadata$GT$17size_for_metadata17hfbf01e521c20d141E"(ptr align 8 %layout) unnamed_addr #0 {
start:
  %_0 = alloca [16 x i8], align 8
  %0 = getelementptr inbounds i8, ptr %layout, i64 8
  %1 = load i64, ptr %0, align 8
  %2 = icmp eq i64 %1, 0
  %_3 = select i1 %2, i64 0, i64 1
  %3 = trunc nuw i64 %_3 to i1
  br i1 %3, label %bb2, label %bb3

bb2:                                              ; preds = %start
  store i64 0, ptr %_0, align 8
  br label %bb4

bb3:                                              ; preds = %start
  %4 = getelementptr inbounds i8, ptr %layout, i64 8
  %5 = getelementptr inbounds i8, ptr %4, i64 8
  %size = load i64, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %size, ptr %6, align 8
  store i64 1, ptr %_0, align 8
  br label %bb4

bb4:                                              ; preds = %bb2, %bb3
  %7 = load i64, ptr %_0, align 8
  %8 = getelementptr inbounds i8, ptr %_0, i64 8
  %9 = load i64, ptr %8, align 8
  %10 = insertvalue { i64, i64 } poison, i64 %7, 0
  %11 = insertvalue { i64, i64 } %10, i64 %9, 1
  ret { i64, i64 } %11

bb1:                                              ; No predecessors!
  unreachable
}

; <core::convert::Infallible as core::fmt::Debug>::fmt
; Function Attrs: nounwind nonlazybind
define internal zeroext i1 @"_ZN62_$LT$core..convert..Infallible$u20$as$u20$core..fmt..Debug$GT$3fmt17h64c104fba08fb8a5E"(ptr align 1 %self, ptr align 8 %_2) unnamed_addr #1 {
start:
  unreachable
}

; <I as core::iter::traits::collect::IntoIterator>::into_iter
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN63_$LT$I$u20$as$u20$core..iter..traits..collect..IntoIterator$GT$9into_iter17hb981ff5553f36980E"(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %self, i64 24, i1 false)
  ret void
}

; <T as core::array::equality::SpecArrayEq<U,_>>::spec_eq
; Function Attrs: nounwind nonlazybind
define internal zeroext i1 @"_ZN69_$LT$T$u20$as$u20$core..array..equality..SpecArrayEq$LT$U$C$_$GT$$GT$7spec_eq17h07d7bbf30a09b131E"(ptr align 1 %a, ptr align 1 %b) unnamed_addr #1 {
start:
  %0 = alloca [1 x i8], align 1
  %1 = load i64, ptr %a, align 1
  %2 = load i64, ptr %b, align 1
  %3 = icmp eq i64 %1, %2
  %4 = zext i1 %3 to i8
  store i8 %4, ptr %0, align 1
  %5 = load i8, ptr %0, align 1
  %_0 = trunc nuw i8 %5 to i1
  ret i1 %_0
}

; <T as core::array::equality::SpecArrayEq<U,_>>::spec_eq
; Function Attrs: nounwind nonlazybind
define internal zeroext i1 @"_ZN69_$LT$T$u20$as$u20$core..array..equality..SpecArrayEq$LT$U$C$_$GT$$GT$7spec_eq17h41cb6230264a39f1E"(ptr align 1 %a, ptr align 1 %b) unnamed_addr #1 {
start:
  %0 = alloca [1 x i8], align 1
  %1 = load i72, ptr %a, align 1
  %2 = load i72, ptr %b, align 1
  %3 = icmp eq i72 %1, %2
  %4 = zext i1 %3 to i8
  store i8 %4, ptr %0, align 1
  %5 = load i8, ptr %0, align 1
  %_0 = trunc nuw i8 %5 to i1
  ret i1 %_0
}

; <T as core::array::equality::SpecArrayEq<U,_>>::spec_eq
; Function Attrs: nounwind nonlazybind
define internal zeroext i1 @"_ZN69_$LT$T$u20$as$u20$core..array..equality..SpecArrayEq$LT$U$C$_$GT$$GT$7spec_eq17h8ba13dad16149b3fE"(ptr align 8 %a, ptr align 8 %b) unnamed_addr #1 {
start:
  %0 = alloca [1 x i8], align 1
  %1 = call i32 @memcmp(ptr %a, ptr %b, i64 24)
  %2 = icmp eq i32 %1, 0
  %3 = zext i1 %2 to i8
  store i8 %3, ptr %0, align 1
  %4 = load i8, ptr %0, align 1
  %_0 = trunc nuw i8 %4 to i1
  ret i1 %_0
}

; <T as core::array::equality::SpecArrayEq<U,_>>::spec_eq
; Function Attrs: nounwind nonlazybind
define internal zeroext i1 @"_ZN69_$LT$T$u20$as$u20$core..array..equality..SpecArrayEq$LT$U$C$_$GT$$GT$7spec_eq17hab59d30fde77205cE"(ptr align 8 %a, ptr align 8 %b) unnamed_addr #1 {
start:
  %0 = alloca [1 x i8], align 1
  %1 = call i32 @memcmp(ptr %a, ptr %b, i64 32)
  %2 = icmp eq i32 %1, 0
  %3 = zext i1 %2 to i8
  store i8 %3, ptr %0, align 1
  %4 = load i8, ptr %0, align 1
  %_0 = trunc nuw i8 %4 to i1
  ret i1 %_0
}

; <T as core::array::equality::SpecArrayEq<U,_>>::spec_eq
; Function Attrs: nounwind nonlazybind
define internal zeroext i1 @"_ZN69_$LT$T$u20$as$u20$core..array..equality..SpecArrayEq$LT$U$C$_$GT$$GT$7spec_eq17hdab43b81fb2049a6E"(ptr align 1 %a, ptr align 1 %b) unnamed_addr #1 {
start:
  %0 = alloca [1 x i8], align 1
  %1 = load i128, ptr %a, align 1
  %2 = load i128, ptr %b, align 1
  %3 = icmp eq i128 %1, %2
  %4 = zext i1 %3 to i8
  store i8 %4, ptr %0, align 1
  %5 = load i8, ptr %0, align 1
  %_0 = trunc nuw i8 %5 to i1
  ret i1 %_0
}

; <core::array::Guard<T> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN69_$LT$core..array..Guard$LT$T$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h398677062c4df853E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %self.0 = load ptr, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %self.1 = load i64, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %self, i64 16
  %index = load i64, ptr %1, align 8
  br label %bb1

bb1:                                              ; preds = %start
; call <core::ops::range::Range<usize> as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
  call void @"_ZN106_$LT$core..ops..range..Range$LT$usize$GT$$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17h3777bb088f02bcd7E"(i64 0, i64 %index, i64 %self.1, ptr align 8 @alloc_f5da46e47ed57d40a34a62ec70202128) #14
  br label %bb3

bb3:                                              ; preds = %bb1
  %2 = icmp eq i64 %index, 0
  br i1 %2, label %bb4, label %bb5

bb4:                                              ; preds = %bb5, %bb3
  ret void

bb5:                                              ; preds = %bb3
  br label %bb4
}

; <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$13get_unchecked18precondition_check17hff5b7d722b1e5766E"(i64 %this, i64 %len, ptr align 8 %0) unnamed_addr #0 {
start:
  %_7 = alloca [16 x i8], align 8
  %_5 = alloca [48 x i8], align 8
  %_3 = icmp ult i64 %this, %len
  br i1 %_3, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %1 = getelementptr inbounds nuw { ptr, i64 }, ptr %_7, i64 0
  store ptr @alloc_97d92cbf2a68a6ac45a1b13da79836e4, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %1, i64 8
  store i64 214, ptr %2, align 8
  store ptr %_7, ptr %_5, align 8
  %3 = getelementptr inbounds i8, ptr %_5, i64 8
  store i64 1, ptr %3, align 8
  %4 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %5 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %6 = getelementptr inbounds i8, ptr %_5, i64 32
  store ptr %4, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  store i64 %5, ptr %7, align 8
  %8 = getelementptr inbounds i8, ptr %_5, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %8, align 8
  %9 = getelementptr inbounds i8, ptr %8, i64 8
  store i64 0, ptr %9, align 8
; call core::panicking::panic_nounwind_fmt
  call void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8 %_5, i1 zeroext false, ptr align 8 %0) #15
  unreachable

bb1:                                              ; preds = %start
  ret void
}

; <usize as core::slice::index::SliceIndex<[T]>>::get_unchecked_mut::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN75_$LT$usize$u20$as$u20$core..slice..index..SliceIndex$LT$$u5b$T$u5d$$GT$$GT$17get_unchecked_mut18precondition_check17hc49bed520081e145E"(i64 %this, i64 %len, ptr align 8 %0) unnamed_addr #0 {
start:
  %_7 = alloca [16 x i8], align 8
  %_5 = alloca [48 x i8], align 8
  %_3 = icmp ult i64 %this, %len
  br i1 %_3, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %1 = getelementptr inbounds nuw { ptr, i64 }, ptr %_7, i64 0
  store ptr @alloc_5a8fdd84b3281310cbf6b74bb6bf0065, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %1, i64 8
  store i64 218, ptr %2, align 8
  store ptr %_7, ptr %_5, align 8
  %3 = getelementptr inbounds i8, ptr %_5, i64 8
  store i64 1, ptr %3, align 8
  %4 = load ptr, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, align 8
  %5 = load i64, ptr getelementptr inbounds (i8, ptr @anon.c68ad90a3a9dfb7a47f86997a7ce991b.0, i64 8), align 8
  %6 = getelementptr inbounds i8, ptr %_5, i64 32
  store ptr %4, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  store i64 %5, ptr %7, align 8
  %8 = getelementptr inbounds i8, ptr %_5, i64 16
  store ptr inttoptr (i64 8 to ptr), ptr %8, align 8
  %9 = getelementptr inbounds i8, ptr %8, i64 8
  store i64 0, ptr %9, align 8
; call core::panicking::panic_nounwind_fmt
  call void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8 %_5, i1 zeroext false, ptr align 8 %0) #15
  unreachable

bb1:                                              ; preds = %start
  ret void
}

; <core::result::Result<T,E> as core::ops::try_trait::Try>::branch
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN79_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17h2d7e48b51d222444E"(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_5 = alloca [1 x i8], align 1
  %0 = load i8, ptr %self, align 8
  %1 = trunc nuw i8 %0 to i1
  %_2 = zext i1 %1 to i64
  %2 = trunc nuw i64 %_2 to i1
  br i1 %2, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %3 = getelementptr inbounds i8, ptr %self, i64 1
  %4 = load i8, ptr %3, align 1
  %e = trunc nuw i8 %4 to i1
  %5 = zext i1 %e to i8
  store i8 %5, ptr %_5, align 1
  %6 = load i8, ptr %_5, align 1
  %7 = trunc nuw i8 %6 to i1
  %8 = getelementptr inbounds i8, ptr %_0, i64 1
  %9 = zext i1 %7 to i8
  store i8 %9, ptr %8, align 1
  store i8 1, ptr %_0, align 8
  br label %bb4

bb3:                                              ; preds = %start
  %10 = getelementptr inbounds i8, ptr %self, i64 8
  %v.0 = load i64, ptr %10, align 8
  %11 = getelementptr inbounds i8, ptr %10, i64 8
  %v.1 = load i64, ptr %11, align 8
  %12 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %v.0, ptr %12, align 8
  %13 = getelementptr inbounds i8, ptr %12, i64 8
  store i64 %v.1, ptr %13, align 8
  store i8 0, ptr %_0, align 8
  br label %bb4

bb4:                                              ; preds = %bb2, %bb3
  ret void

bb1:                                              ; No predecessors!
  unreachable
}

; <core::result::Result<T,E> as core::ops::try_trait::Try>::branch
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN79_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17h2fcadaea52e1380bE"(ptr sret([32 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_5 = alloca [24 x i8], align 8
  %e = alloca [24 x i8], align 8
  %v = alloca [24 x i8], align 8
  %_2 = load i64, ptr %self, align 8
  %0 = trunc nuw i64 %_2 to i1
  br i1 %0, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %self, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %e, ptr align 8 %1, i64 24, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_5, ptr align 8 %e, i64 24, i1 false)
  %2 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %2, ptr align 8 %_5, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb4

bb3:                                              ; preds = %start
  %3 = getelementptr inbounds i8, ptr %self, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %v, ptr align 8 %3, i64 24, i1 false)
  %4 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %4, ptr align 8 %v, i64 24, i1 false)
  store i64 0, ptr %_0, align 8
  br label %bb4

bb4:                                              ; preds = %bb2, %bb3
  ret void

bb1:                                              ; No predecessors!
  unreachable
}

; <zerocopy::error::SizeError<Src,Dst> as core::fmt::Debug>::fmt
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN80_$LT$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17h29c52287891abf53E"(ptr align 8 %self, ptr align 8 %f) unnamed_addr #0 {
start:
  %_4 = alloca [16 x i8], align 8
; call core::fmt::Formatter::debug_struct
  call void @_ZN4core3fmt9Formatter12debug_struct17ha54210e59fde88afE(ptr sret([16 x i8]) align 8 %_4, ptr align 8 %f, ptr align 1 @alloc_c1dcee2c0147c5bf2be6e4d2507481cb, i64 9) #14
; call core::fmt::builders::DebugStruct::finish
  %_0 = call zeroext i1 @_ZN4core3fmt8builders11DebugStruct6finish17hd58177b4b9fef635E(ptr align 8 %_4) #14
  ret i1 %_0
}

; <zerocopy::error::SizeError<Src,Dst> as core::fmt::Debug>::fmt
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN80_$LT$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17h4210c2b99a10fdafE"(ptr align 8 %self, ptr align 8 %f) unnamed_addr #0 {
start:
  %_4 = alloca [16 x i8], align 8
; call core::fmt::Formatter::debug_struct
  call void @_ZN4core3fmt9Formatter12debug_struct17ha54210e59fde88afE(ptr sret([16 x i8]) align 8 %_4, ptr align 8 %f, ptr align 1 @alloc_c1dcee2c0147c5bf2be6e4d2507481cb, i64 9) #14
; call core::fmt::builders::DebugStruct::finish
  %_0 = call zeroext i1 @_ZN4core3fmt8builders11DebugStruct6finish17hd58177b4b9fef635E(ptr align 8 %_4) #14
  ret i1 %_0
}

; <zerocopy::error::SizeError<Src,Dst> as core::fmt::Debug>::fmt
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN80_$LT$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17h51fe6da6896044deE"(ptr align 8 %self, ptr align 8 %f) unnamed_addr #0 {
start:
  %_4 = alloca [16 x i8], align 8
; call core::fmt::Formatter::debug_struct
  call void @_ZN4core3fmt9Formatter12debug_struct17ha54210e59fde88afE(ptr sret([16 x i8]) align 8 %_4, ptr align 8 %f, ptr align 1 @alloc_c1dcee2c0147c5bf2be6e4d2507481cb, i64 9) #14
; call core::fmt::builders::DebugStruct::finish
  %_0 = call zeroext i1 @_ZN4core3fmt8builders11DebugStruct6finish17hd58177b4b9fef635E(ptr align 8 %_4) #14
  ret i1 %_0
}

; <zerocopy::error::SizeError<Src,Dst> as core::fmt::Debug>::fmt
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN80_$LT$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17hb04a3bd15d4021cbE"(ptr align 8 %self, ptr align 8 %f) unnamed_addr #0 {
start:
  %_4 = alloca [16 x i8], align 8
; call core::fmt::Formatter::debug_struct
  call void @_ZN4core3fmt9Formatter12debug_struct17ha54210e59fde88afE(ptr sret([16 x i8]) align 8 %_4, ptr align 8 %f, ptr align 1 @alloc_c1dcee2c0147c5bf2be6e4d2507481cb, i64 9) #14
; call core::fmt::builders::DebugStruct::finish
  %_0 = call zeroext i1 @_ZN4core3fmt8builders11DebugStruct6finish17hd58177b4b9fef635E(ptr align 8 %_4) #14
  ret i1 %_0
}

; <zerocopy::error::SizeError<Src,Dst> as core::fmt::Debug>::fmt
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN80_$LT$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17hb1c293a2a609b964E"(ptr align 8 %self, ptr align 8 %f) unnamed_addr #0 {
start:
  %_4 = alloca [16 x i8], align 8
; call core::fmt::Formatter::debug_struct
  call void @_ZN4core3fmt9Formatter12debug_struct17ha54210e59fde88afE(ptr sret([16 x i8]) align 8 %_4, ptr align 8 %f, ptr align 1 @alloc_c1dcee2c0147c5bf2be6e4d2507481cb, i64 9) #14
; call core::fmt::builders::DebugStruct::finish
  %_0 = call zeroext i1 @_ZN4core3fmt8builders11DebugStruct6finish17hd58177b4b9fef635E(ptr align 8 %_4) #14
  ret i1 %_0
}

; <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h4f781dc08e8b28a7E"(ptr align 8 %self) unnamed_addr #0 {
start:
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h7a3db9b058eca382E"(ptr align 8 %self) unnamed_addr #0 {
start:
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h8a926ea295a2290eE"(ptr align 8 %self) unnamed_addr #0 {
start:
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hae31289f73b9331cE"(ptr align 8 %self) unnamed_addr #0 {
start:
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17haf29285ee22537e9E"(ptr align 8 %self) unnamed_addr #0 {
start:
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hb2ca57aab1b19302E"(ptr align 8 %self) unnamed_addr #0 {
start:
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hd374a0c0eb06d4aaE"(ptr align 8 %self) unnamed_addr #0 {
start:
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hd6a24cdc59b53e3aE"(ptr align 8 %self) unnamed_addr #0 {
start:
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN82_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17hdd4f2b0ba15ecce2E"(ptr align 8 %self) unnamed_addr #0 {
start:
  ret void
}

; <zerocopy::error::ConvertError<A,S,V> as core::fmt::Debug>::fmt
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN83_$LT$zerocopy..error..ConvertError$LT$A$C$S$C$V$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17h29c73536d87efdf9E"(ptr align 8 %self, ptr align 8 %f) unnamed_addr #0 {
start:
  %_19 = alloca [24 x i8], align 8
  %_13 = alloca [24 x i8], align 8
  %_7 = alloca [24 x i8], align 8
  %_0 = alloca [1 x i8], align 1
  %_3 = load i64, ptr %self, align 8
  switch i64 %_3, label %bb1 [
    i64 0, label %bb4
    i64 1, label %bb3
    i64 2, label %bb2
  ]

bb1:                                              ; preds = %start
  unreachable

bb4:                                              ; preds = %start
  %e = getelementptr inbounds i8, ptr %self, i64 8
; call core::fmt::Formatter::debug_tuple
  call void @_ZN4core3fmt9Formatter11debug_tuple17h5788c8e9cef8e881E(ptr sret([24 x i8]) align 8 %_7, ptr align 8 %f, ptr align 1 @alloc_a5fc064c3c780589d8ff39e05dfc61c2, i64 9) #14
; call core::fmt::builders::DebugTuple::field
  %_5 = call align 8 ptr @_ZN4core3fmt8builders10DebugTuple5field17haade97ea9c4f7f62E(ptr align 8 %_7, ptr align 1 %e, ptr align 8 @vtable.7) #14
; call core::fmt::builders::DebugTuple::finish
  %0 = call zeroext i1 @_ZN4core3fmt8builders10DebugTuple6finish17hc28ea1e2485caf89E(ptr align 8 %_5) #14
  %1 = zext i1 %0 to i8
  store i8 %1, ptr %_0, align 1
  br label %bb11

bb3:                                              ; preds = %start
  %e1 = getelementptr inbounds i8, ptr %self, i64 8
; call core::fmt::Formatter::debug_tuple
  call void @_ZN4core3fmt9Formatter11debug_tuple17h5788c8e9cef8e881E(ptr sret([24 x i8]) align 8 %_13, ptr align 8 %f, ptr align 1 @alloc_728f72eadbe4863ffd4951bbce90c6df, i64 4) #14
; call core::fmt::builders::DebugTuple::field
  %_11 = call align 8 ptr @_ZN4core3fmt8builders10DebugTuple5field17haade97ea9c4f7f62E(ptr align 8 %_13, ptr align 1 %e1, ptr align 8 @vtable.6) #14
; call core::fmt::builders::DebugTuple::finish
  %2 = call zeroext i1 @_ZN4core3fmt8builders10DebugTuple6finish17hc28ea1e2485caf89E(ptr align 8 %_11) #14
  %3 = zext i1 %2 to i8
  store i8 %3, ptr %_0, align 1
  br label %bb11

bb2:                                              ; preds = %start
  %e2 = getelementptr inbounds i8, ptr %self, i64 8
; call core::fmt::Formatter::debug_tuple
  call void @_ZN4core3fmt9Formatter11debug_tuple17h5788c8e9cef8e881E(ptr sret([24 x i8]) align 8 %_19, ptr align 8 %f, ptr align 1 @alloc_c78721185e288f48cd1139f3ec1d2a9a, i64 8) #14
; call core::fmt::builders::DebugTuple::field
  %_17 = call align 8 ptr @_ZN4core3fmt8builders10DebugTuple5field17haade97ea9c4f7f62E(ptr align 8 %_19, ptr align 1 %e2, ptr align 8 @vtable.8) #14
; call core::fmt::builders::DebugTuple::finish
  %4 = call zeroext i1 @_ZN4core3fmt8builders10DebugTuple6finish17hc28ea1e2485caf89E(ptr align 8 %_17) #14
  %5 = zext i1 %4 to i8
  store i8 %5, ptr %_0, align 1
  br label %bb11

bb11:                                             ; preds = %bb2, %bb3, %bb4
  %6 = load i8, ptr %_0, align 1
  %7 = trunc nuw i8 %6 to i1
  ret i1 %7
}

; <zerocopy::error::AlignmentError<Src,Dst> as core::fmt::Debug>::fmt
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN85_$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$u20$as$u20$core..fmt..Debug$GT$3fmt17h6f0dc63dc8f3dc96E"(ptr align 8 %self, ptr align 8 %f) unnamed_addr #0 {
start:
  %_4 = alloca [16 x i8], align 8
; call core::fmt::Formatter::debug_struct
  call void @_ZN4core3fmt9Formatter12debug_struct17ha54210e59fde88afE(ptr sret([16 x i8]) align 8 %_4, ptr align 8 %f, ptr align 1 @alloc_1705c20888af7763fe2181ce42f9e54e, i64 14) #14
; call core::fmt::builders::DebugStruct::finish
  %_0 = call zeroext i1 @_ZN4core3fmt8builders11DebugStruct6finish17hd58177b4b9fef635E(ptr align 8 %_4) #14
  ret i1 %_0
}

; <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h10b7f08ebd2ff639E"() unnamed_addr #1 {
start:
  ret void
}

; <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h2bb6f689937470e7E"() unnamed_addr #1 {
start:
  ret void
}

; <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h2c77c6482e67ff5aE"() unnamed_addr #1 {
start:
  ret void
}

; <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h5ddb3b45459da16eE"() unnamed_addr #1 {
start:
  ret void
}

; <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() unnamed_addr #1 {
start:
  ret void
}

; <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd13491eea66327dcE"() unnamed_addr #1 {
start:
  ret void
}

; <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd988217da53bf241E"() unnamed_addr #1 {
start:
  ret void
}

; zerocopy::ref::def::Ref<B,T>::as_byte_slice
; Function Attrs: nounwind nonlazybind
define internal align 8 ptr @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$13as_byte_slice17h154bf20a9c4c2b16E"(ptr align 8 %self) unnamed_addr #1 {
start:
  ret ptr %self
}

; zerocopy::ref::def::Ref<B,T>::as_byte_slice
; Function Attrs: nounwind nonlazybind
define internal align 8 ptr @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$13as_byte_slice17h1eeaafc9ae281e7fE"(ptr align 8 %self) unnamed_addr #1 {
start:
  ret ptr %self
}

; zerocopy::ref::def::Ref<B,T>::as_byte_slice
; Function Attrs: nounwind nonlazybind
define internal align 8 ptr @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$13as_byte_slice17hda2f189217b62747E"(ptr align 8 %self) unnamed_addr #1 {
start:
  ret ptr %self
}

; zerocopy::ref::def::Ref<B,T>::new_sized_unchecked
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$19new_sized_unchecked17h0de91f1acbe5f191E"(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %bytes.0, i64 %bytes.1) unnamed_addr #1 {
start:
  store ptr %bytes.0, ptr %_0, align 8
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %bytes.1, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_0, i64 16
  store i64 0, ptr %1, align 8
  ret void
}

; zerocopy::ref::def::Ref<B,T>::new_sized_unchecked
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$19new_sized_unchecked17h3b856e7cd58482b1E"(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %bytes.0, i64 %bytes.1) unnamed_addr #1 {
start:
  store ptr %bytes.0, ptr %_0, align 8
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %bytes.1, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_0, i64 16
  store i64 0, ptr %1, align 8
  ret void
}

; zerocopy::ref::def::Ref<B,T>::new_sized_unchecked
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$19new_sized_unchecked17h861730f3255ca9b8E"(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %bytes.0, i64 %bytes.1) unnamed_addr #1 {
start:
  store ptr %bytes.0, ptr %_0, align 8
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %bytes.1, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %_0, i64 16
  store i64 0, ptr %1, align 8
  ret void
}

; zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::sized_from
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$10sized_from17h62c54e1ff9599918E"(ptr sret([32 x i8]) align 8 %_0, ptr align 1 %0, i64 %1) unnamed_addr #1 {
start:
  %_0.i = alloca [1 x i8], align 1
  %_17 = alloca [24 x i8], align 8
  %_14 = alloca [24 x i8], align 8
  %_7 = alloca [24 x i8], align 8
  %bytes = alloca [16 x i8], align 8
  store ptr %0, ptr %bytes, align 8
  %2 = getelementptr inbounds i8, ptr %bytes, i64 8
  store i64 %1, ptr %2, align 8
; call <&T as core::ops::deref::Deref>::deref
  %3 = call { ptr, i64 } @"_ZN49_$LT$$RF$T$u20$as$u20$core..ops..deref..Deref$GT$5deref17hf2c26a9a04406c1fE"(ptr align 8 %bytes) #14
  %_4.0 = extractvalue { ptr, i64 } %3, 0
  %_4.1 = extractvalue { ptr, i64 } %3, 1
  %_2 = icmp ne i64 %_4.1, 8
  br i1 %_2, label %bb3, label %bb6

bb6:                                              ; preds = %start
; call <&T as core::ops::deref::Deref>::deref
  %4 = call { ptr, i64 } @"_ZN49_$LT$$RF$T$u20$as$u20$core..ops..deref..Deref$GT$5deref17hf2c26a9a04406c1fE"(ptr align 8 %bytes) #14
  %_11.0 = extractvalue { ptr, i64 } %4, 0
  %_11.1 = extractvalue { ptr, i64 } %4, 1
  %_0.i1.i = ptrtoint ptr %_11.0 to i64
  store i8 0, ptr %_0.i, align 1
  %5 = load i8, ptr %_0.i, align 1
  %6 = trunc nuw i8 %5 to i1
  %_13 = zext i1 %6 to i64
  %7 = trunc nuw i64 %_13 to i1
  br i1 %7, label %bb9, label %bb12

bb3:                                              ; preds = %start
  %_9.0 = load ptr, ptr %bytes, align 8
  %8 = getelementptr inbounds i8, ptr %bytes, i64 8
  %_9.1 = load i64, ptr %8, align 8
; call zerocopy::error::SizeError<Src,Dst>::new
  %9 = call { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17h46c0ab41b59d907bE"(ptr align 1 %_9.0, i64 %_9.1) #14
  %_8.0 = extractvalue { ptr, i64 } %9, 0
  %_8.1 = extractvalue { ptr, i64 } %9, 1
; call zerocopy::error::SizeError<Src,Dst>::into
  call void @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$4into17h7922f2f716402c56E"(ptr sret([24 x i8]) align 8 %_7, ptr align 1 %_8.0, i64 %_8.1) #14
  %10 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %10, ptr align 8 %_7, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb14

bb9:                                              ; preds = %bb6
  %_16.0 = load ptr, ptr %bytes, align 8
  %11 = getelementptr inbounds i8, ptr %bytes, i64 8
  %_16.1 = load i64, ptr %11, align 8
; call zerocopy::error::AlignmentError<Src,Dst>::with_src
  %12 = call { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$8with_src17h9c9e30cbe7f87ce1E"(ptr align 1 %_16.0, i64 %_16.1) #14
  %_15.0 = extractvalue { ptr, i64 } %12, 0
  %_15.1 = extractvalue { ptr, i64 } %12, 1
; call zerocopy::error::AlignmentError<Src,Dst>::into
  call void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$4into17h306e1a2eddecd6b0E"(ptr sret([24 x i8]) align 8 %_14, ptr align 1 %_15.0, i64 %_15.1) #14
  %13 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %13, ptr align 8 %_14, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb14

bb12:                                             ; preds = %bb6
  %_18.0 = load ptr, ptr %bytes, align 8
  %14 = getelementptr inbounds i8, ptr %bytes, i64 8
  %_18.1 = load i64, ptr %14, align 8
; call zerocopy::ref::def::Ref<B,T>::new_sized_unchecked
  call void @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$19new_sized_unchecked17h861730f3255ca9b8E"(ptr sret([24 x i8]) align 8 %_17, ptr align 1 %_18.0, i64 %_18.1) #14
  %15 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %15, ptr align 8 %_17, i64 24, i1 false)
  store i64 0, ptr %_0, align 8
  br label %bb14

bb14:                                             ; preds = %bb3, %bb12, %bb9
  ret void

bb15:                                             ; No predecessors!
  unreachable
}

; zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::sized_from
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$10sized_from17h6914f5febbbbc0deE"(ptr sret([32 x i8]) align 8 %_0, ptr align 1 %0, i64 %1) unnamed_addr #1 {
start:
  %_0.i = alloca [1 x i8], align 1
  %_17 = alloca [24 x i8], align 8
  %_14 = alloca [24 x i8], align 8
  %_7 = alloca [24 x i8], align 8
  %bytes = alloca [16 x i8], align 8
  store ptr %0, ptr %bytes, align 8
  %2 = getelementptr inbounds i8, ptr %bytes, i64 8
  store i64 %1, ptr %2, align 8
; call <&T as core::ops::deref::Deref>::deref
  %3 = call { ptr, i64 } @"_ZN49_$LT$$RF$T$u20$as$u20$core..ops..deref..Deref$GT$5deref17hf2c26a9a04406c1fE"(ptr align 8 %bytes) #14
  %_4.0 = extractvalue { ptr, i64 } %3, 0
  %_4.1 = extractvalue { ptr, i64 } %3, 1
  %_2 = icmp ne i64 %_4.1, 16
  br i1 %_2, label %bb3, label %bb6

bb6:                                              ; preds = %start
; call <&T as core::ops::deref::Deref>::deref
  %4 = call { ptr, i64 } @"_ZN49_$LT$$RF$T$u20$as$u20$core..ops..deref..Deref$GT$5deref17hf2c26a9a04406c1fE"(ptr align 8 %bytes) #14
  %_11.0 = extractvalue { ptr, i64 } %4, 0
  %_11.1 = extractvalue { ptr, i64 } %4, 1
  %_0.i1.i = ptrtoint ptr %_11.0 to i64
  store i8 0, ptr %_0.i, align 1
  %5 = load i8, ptr %_0.i, align 1
  %6 = trunc nuw i8 %5 to i1
  %_13 = zext i1 %6 to i64
  %7 = trunc nuw i64 %_13 to i1
  br i1 %7, label %bb9, label %bb12

bb3:                                              ; preds = %start
  %_9.0 = load ptr, ptr %bytes, align 8
  %8 = getelementptr inbounds i8, ptr %bytes, i64 8
  %_9.1 = load i64, ptr %8, align 8
; call zerocopy::error::SizeError<Src,Dst>::new
  %9 = call { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17h844846c0e1a3bda9E"(ptr align 1 %_9.0, i64 %_9.1) #14
  %_8.0 = extractvalue { ptr, i64 } %9, 0
  %_8.1 = extractvalue { ptr, i64 } %9, 1
; call zerocopy::error::SizeError<Src,Dst>::into
  call void @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$4into17heed897796300af4cE"(ptr sret([24 x i8]) align 8 %_7, ptr align 1 %_8.0, i64 %_8.1) #14
  %10 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %10, ptr align 8 %_7, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb14

bb9:                                              ; preds = %bb6
  %_16.0 = load ptr, ptr %bytes, align 8
  %11 = getelementptr inbounds i8, ptr %bytes, i64 8
  %_16.1 = load i64, ptr %11, align 8
; call zerocopy::error::AlignmentError<Src,Dst>::with_src
  %12 = call { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$8with_src17h050c9819055759edE"(ptr align 1 %_16.0, i64 %_16.1) #14
  %_15.0 = extractvalue { ptr, i64 } %12, 0
  %_15.1 = extractvalue { ptr, i64 } %12, 1
; call zerocopy::error::AlignmentError<Src,Dst>::into
  call void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$4into17h42b33bd17edf970bE"(ptr sret([24 x i8]) align 8 %_14, ptr align 1 %_15.0, i64 %_15.1) #14
  %13 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %13, ptr align 8 %_14, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb14

bb12:                                             ; preds = %bb6
  %_18.0 = load ptr, ptr %bytes, align 8
  %14 = getelementptr inbounds i8, ptr %bytes, i64 8
  %_18.1 = load i64, ptr %14, align 8
; call zerocopy::ref::def::Ref<B,T>::new_sized_unchecked
  call void @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$19new_sized_unchecked17h3b856e7cd58482b1E"(ptr sret([24 x i8]) align 8 %_17, ptr align 1 %_18.0, i64 %_18.1) #14
  %15 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %15, ptr align 8 %_17, i64 24, i1 false)
  store i64 0, ptr %_0, align 8
  br label %bb14

bb14:                                             ; preds = %bb3, %bb12, %bb9
  ret void

bb15:                                             ; No predecessors!
  unreachable
}

; zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::sized_from
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$10sized_from17h84a0543841e5444cE"(ptr sret([32 x i8]) align 8 %_0, ptr align 1 %0, i64 %1) unnamed_addr #1 {
start:
  %_0.i = alloca [1 x i8], align 1
  %_17 = alloca [24 x i8], align 8
  %_14 = alloca [24 x i8], align 8
  %_7 = alloca [24 x i8], align 8
  %bytes = alloca [16 x i8], align 8
  store ptr %0, ptr %bytes, align 8
  %2 = getelementptr inbounds i8, ptr %bytes, i64 8
  store i64 %1, ptr %2, align 8
; call <&T as core::ops::deref::Deref>::deref
  %3 = call { ptr, i64 } @"_ZN49_$LT$$RF$T$u20$as$u20$core..ops..deref..Deref$GT$5deref17hf2c26a9a04406c1fE"(ptr align 8 %bytes) #14
  %_4.0 = extractvalue { ptr, i64 } %3, 0
  %_4.1 = extractvalue { ptr, i64 } %3, 1
  %_2 = icmp ne i64 %_4.1, 8
  br i1 %_2, label %bb3, label %bb6

bb6:                                              ; preds = %start
; call <&T as core::ops::deref::Deref>::deref
  %4 = call { ptr, i64 } @"_ZN49_$LT$$RF$T$u20$as$u20$core..ops..deref..Deref$GT$5deref17hf2c26a9a04406c1fE"(ptr align 8 %bytes) #14
  %_11.0 = extractvalue { ptr, i64 } %4, 0
  %_11.1 = extractvalue { ptr, i64 } %4, 1
  %_0.i1.i = ptrtoint ptr %_11.0 to i64
  store i8 0, ptr %_0.i, align 1
  %5 = load i8, ptr %_0.i, align 1
  %6 = trunc nuw i8 %5 to i1
  %_13 = zext i1 %6 to i64
  %7 = trunc nuw i64 %_13 to i1
  br i1 %7, label %bb9, label %bb12

bb3:                                              ; preds = %start
  %_9.0 = load ptr, ptr %bytes, align 8
  %8 = getelementptr inbounds i8, ptr %bytes, i64 8
  %_9.1 = load i64, ptr %8, align 8
; call zerocopy::error::SizeError<Src,Dst>::new
  %9 = call { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17ha3510e5bc3493db0E"(ptr align 1 %_9.0, i64 %_9.1) #14
  %_8.0 = extractvalue { ptr, i64 } %9, 0
  %_8.1 = extractvalue { ptr, i64 } %9, 1
; call zerocopy::error::SizeError<Src,Dst>::into
  call void @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$4into17h65b4ace548f19de7E"(ptr sret([24 x i8]) align 8 %_7, ptr align 1 %_8.0, i64 %_8.1) #14
  %10 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %10, ptr align 8 %_7, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb14

bb9:                                              ; preds = %bb6
  %_16.0 = load ptr, ptr %bytes, align 8
  %11 = getelementptr inbounds i8, ptr %bytes, i64 8
  %_16.1 = load i64, ptr %11, align 8
; call zerocopy::error::AlignmentError<Src,Dst>::with_src
  %12 = call { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$8with_src17h634a45c428572e75E"(ptr align 1 %_16.0, i64 %_16.1) #14
  %_15.0 = extractvalue { ptr, i64 } %12, 0
  %_15.1 = extractvalue { ptr, i64 } %12, 1
; call zerocopy::error::AlignmentError<Src,Dst>::into
  call void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$4into17h16a071609168b15cE"(ptr sret([24 x i8]) align 8 %_14, ptr align 1 %_15.0, i64 %_15.1) #14
  %13 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %13, ptr align 8 %_14, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb14

bb12:                                             ; preds = %bb6
  %_18.0 = load ptr, ptr %bytes, align 8
  %14 = getelementptr inbounds i8, ptr %bytes, i64 8
  %_18.1 = load i64, ptr %14, align 8
; call zerocopy::ref::def::Ref<B,T>::new_sized_unchecked
  call void @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$19new_sized_unchecked17h0de91f1acbe5f191E"(ptr sret([24 x i8]) align 8 %_17, ptr align 1 %_18.0, i64 %_18.1) #14
  %15 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %15, ptr align 8 %_17, i64 24, i1 false)
  store i64 0, ptr %_0, align 8
  br label %bb14

bb14:                                             ; preds = %bb3, %bb12, %bb9
  ret void

bb15:                                             ; No predecessors!
  unreachable
}

; zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::read
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$4read17h23881d3f68faaf40E"(ptr sret([16 x i8]) align 1 %_0, ptr align 8 %r) unnamed_addr #0 {
start:
; call zerocopy::ref::def::Ref<B,T>::as_byte_slice
  %b = call align 8 ptr @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$13as_byte_slice17h1eeaafc9ae281e7fE"(ptr align 8 %r) #14
; call <&T as core::ops::deref::Deref>::deref
  %0 = call { ptr, i64 } @"_ZN49_$LT$$RF$T$u20$as$u20$core..ops..deref..Deref$GT$5deref17hf2c26a9a04406c1fE"(ptr align 8 %b) #14
  %_5.0 = extractvalue { ptr, i64 } %0, 0
  %_5.1 = extractvalue { ptr, i64 } %0, 1
; call core::ptr::read
  call void @_ZN4core3ptr4read17h11a61a189bbb4cc5E(ptr sret([16 x i8]) align 1 %_0, ptr %_5.0, ptr align 8 @alloc_5c158c4449c997c190308fffed5cd440) #14
  ret void
}

; zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::read
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$4read17h8ba7c23d7e825d21E"(ptr align 8 %r) unnamed_addr #0 {
start:
  %0 = alloca [8 x i8], align 8
  %_0 = alloca [8 x i8], align 1
; call zerocopy::ref::def::Ref<B,T>::as_byte_slice
  %b = call align 8 ptr @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$13as_byte_slice17h154bf20a9c4c2b16E"(ptr align 8 %r) #14
; call <&T as core::ops::deref::Deref>::deref
  %1 = call { ptr, i64 } @"_ZN49_$LT$$RF$T$u20$as$u20$core..ops..deref..Deref$GT$5deref17hf2c26a9a04406c1fE"(ptr align 8 %b) #14
  %_5.0 = extractvalue { ptr, i64 } %1, 0
  %_5.1 = extractvalue { ptr, i64 } %1, 1
; call core::ptr::read
  %2 = call i64 @_ZN4core3ptr4read17ha6e646c6d3854f9eE(ptr %_5.0, ptr align 8 @alloc_5c158c4449c997c190308fffed5cd440) #14
  store i64 %2, ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0, ptr align 8 %0, i64 8, i1 false)
  %3 = load i64, ptr %_0, align 1
  ret i64 %3
}

; zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::read
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$4read17ha3073fb02ddf5463E"(ptr align 8 %r) unnamed_addr #0 {
start:
  %0 = alloca [8 x i8], align 8
  %_0 = alloca [8 x i8], align 1
; call zerocopy::ref::def::Ref<B,T>::as_byte_slice
  %b = call align 8 ptr @"_ZN8zerocopy3ref3def16Ref$LT$B$C$T$GT$13as_byte_slice17hda2f189217b62747E"(ptr align 8 %r) #14
; call <&T as core::ops::deref::Deref>::deref
  %1 = call { ptr, i64 } @"_ZN49_$LT$$RF$T$u20$as$u20$core..ops..deref..Deref$GT$5deref17hf2c26a9a04406c1fE"(ptr align 8 %b) #14
  %_5.0 = extractvalue { ptr, i64 } %1, 0
  %_5.1 = extractvalue { ptr, i64 } %1, 1
; call core::ptr::read
  %2 = call i64 @_ZN4core3ptr4read17hab62c60c64480059E(ptr %_5.0, ptr align 8 @alloc_5c158c4449c997c190308fffed5cd440) #14
  store i64 %2, ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0, ptr align 8 %0, i64 8, i1 false)
  %3 = load i64, ptr %_0, align 1
  ret i64 %3
}

; zerocopy::util::len_of::MetadataOf<T>::new_unchecked
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$13new_unchecked17h0ae4cc51ed972104E"() unnamed_addr #1 {
start:
  ret void
}

; zerocopy::util::len_of::MetadataOf<T>::new_unchecked
; Function Attrs: nounwind nonlazybind
define internal i64 @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$13new_unchecked17hbf283257ae23f131E"(i64 %meta) unnamed_addr #1 {
start:
  ret i64 %meta
}

; zerocopy::util::len_of::MetadataOf<T>::get
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$3get17h0182bf0d597d886dE"(ptr align 1 %self) unnamed_addr #1 {
start:
  ret void
}

; zerocopy::util::len_of::MetadataOf<T>::get
; Function Attrs: nounwind nonlazybind
define internal i64 @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$3get17h5aa6cb6cfb0917d9E"(ptr align 8 %self) unnamed_addr #1 {
start:
  %_0 = load i64, ptr %self, align 8
  ret i64 %_0
}

; zerocopy::error::ConvertError<zerocopy::error::AlignmentError<Src,Dst>,zerocopy::error::SizeError<Src,Dst>,core::convert::Infallible>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN8zerocopy5error142ConvertError$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$C$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$C$core..convert..Infallible$GT$7map_src17h3bcf6f9550f87e96E"(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = load i64, ptr %self, align 8
  %0 = trunc nuw i64 %_3 to i1
  br i1 %0, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %self, i64 8
  %e.01 = load ptr, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %1, i64 8
  %e.12 = load i64, ptr %2, align 8
; call zerocopy::error::SizeError<Src,Dst>::map_src
  %3 = call { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$7map_src17h91554b315c08677aE"(ptr %e.01, i64 %e.12) #14
  %_7.0 = extractvalue { ptr, i64 } %3, 0
  %_7.1 = extractvalue { ptr, i64 } %3, 1
  %4 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %_7.0, ptr %4, align 8
  %5 = getelementptr inbounds i8, ptr %4, i64 8
  store i64 %_7.1, ptr %5, align 8
  store i64 1, ptr %_0, align 8
  br label %bb6

bb3:                                              ; preds = %start
  %6 = getelementptr inbounds i8, ptr %self, i64 8
  %e.0 = load ptr, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  %e.1 = load i64, ptr %7, align 8
; call zerocopy::error::AlignmentError<Src,Dst>::map_src
  %8 = call { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$7map_src17h533da408a212c2eeE"(ptr %e.0, i64 %e.1) #14
  %_5.0 = extractvalue { ptr, i64 } %8, 0
  %_5.1 = extractvalue { ptr, i64 } %8, 1
  %9 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %_5.0, ptr %9, align 8
  %10 = getelementptr inbounds i8, ptr %9, i64 8
  store i64 %_5.1, ptr %10, align 8
  store i64 0, ptr %_0, align 8
  br label %bb6

bb6:                                              ; preds = %bb2, %bb3
  ret void

bb1:                                              ; No predecessors!
  unreachable
}

; zerocopy::error::ConvertError<zerocopy::error::AlignmentError<Src,Dst>,zerocopy::error::SizeError<Src,Dst>,core::convert::Infallible>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN8zerocopy5error142ConvertError$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$C$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$C$core..convert..Infallible$GT$7map_src17h8a55bf6585f616aeE"(ptr sret([24 x i8]) align 8 %_0, i1 zeroext %self, ptr align 8 %f) unnamed_addr #0 {
start:
  %_3 = zext i1 %self to i64
  %0 = trunc nuw i64 %_3 to i1
  br i1 %0, label %bb2, label %bb3

bb2:                                              ; preds = %start
; call zerocopy::error::SizeError<Src,Dst>::map_src
  %1 = call { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$7map_src17h756d3f1aeb49a29aE"(ptr align 8 %f) #14
  %_7.0 = extractvalue { ptr, i64 } %1, 0
  %_7.1 = extractvalue { ptr, i64 } %1, 1
  %2 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %_7.0, ptr %2, align 8
  %3 = getelementptr inbounds i8, ptr %2, i64 8
  store i64 %_7.1, ptr %3, align 8
  store i64 1, ptr %_0, align 8
  br label %bb6

bb3:                                              ; preds = %start
; call zerocopy::error::AlignmentError<Src,Dst>::map_src
  %4 = call { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$7map_src17h5fb8eec72bc12cc7E"(ptr align 8 %f) #14
  %_5.0 = extractvalue { ptr, i64 } %4, 0
  %_5.1 = extractvalue { ptr, i64 } %4, 1
  %5 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %_5.0, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %5, i64 8
  store i64 %_5.1, ptr %6, align 8
  store i64 0, ptr %_0, align 8
  br label %bb6

bb6:                                              ; preds = %bb2, %bb3
  ret void

bb1:                                              ; No predecessors!
  unreachable
}

; zerocopy::error::ConvertError<zerocopy::error::AlignmentError<Src,Dst>,zerocopy::error::SizeError<Src,Dst>,core::convert::Infallible>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN8zerocopy5error142ConvertError$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$C$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$C$core..convert..Infallible$GT$7map_src17h9f9510464e1be662E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_0 = alloca [1 x i8], align 1
  %_3 = load i64, ptr %self, align 8
  %0 = trunc nuw i64 %_3 to i1
  br i1 %0, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %self, i64 8
  %e.01 = load ptr, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %1, i64 8
  %e.12 = load i64, ptr %2, align 8
; call zerocopy::error::SizeError<Src,Dst>::map_src
  call void @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$7map_src17h77a4b16362fc8f14E"(ptr %e.01, i64 %e.12) #14
  store i8 1, ptr %_0, align 1
  br label %bb6

bb3:                                              ; preds = %start
  %3 = getelementptr inbounds i8, ptr %self, i64 8
  %e.0 = load ptr, ptr %3, align 8
  %4 = getelementptr inbounds i8, ptr %3, i64 8
  %e.1 = load i64, ptr %4, align 8
; call zerocopy::error::AlignmentError<Src,Dst>::map_src
  call void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$7map_src17h41d52c6c53d961dbE"(ptr %e.0, i64 %e.1) #14
  store i8 0, ptr %_0, align 1
  br label %bb6

bb6:                                              ; preds = %bb2, %bb3
  %5 = load i8, ptr %_0, align 1
  %6 = trunc nuw i8 %5 to i1
  ret i1 %6

bb1:                                              ; No predecessors!
  unreachable
}

; zerocopy::error::ConvertError<zerocopy::error::AlignmentError<Src,Dst>,zerocopy::error::SizeError<Src,Dst>,core::convert::Infallible>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN8zerocopy5error142ConvertError$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$C$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$C$core..convert..Infallible$GT$7map_src17hd0f9105e56625d1bE"(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = load i64, ptr %self, align 8
  %0 = trunc nuw i64 %_3 to i1
  br i1 %0, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %self, i64 8
  %e.01 = load ptr, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %1, i64 8
  %e.12 = load i64, ptr %2, align 8
; call zerocopy::error::SizeError<Src,Dst>::map_src
  %3 = call { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$7map_src17hf823c08b31dea1dfE"(ptr %e.01, i64 %e.12) #14
  %_7.0 = extractvalue { ptr, i64 } %3, 0
  %_7.1 = extractvalue { ptr, i64 } %3, 1
  %4 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %_7.0, ptr %4, align 8
  %5 = getelementptr inbounds i8, ptr %4, i64 8
  store i64 %_7.1, ptr %5, align 8
  store i64 1, ptr %_0, align 8
  br label %bb6

bb3:                                              ; preds = %start
  %6 = getelementptr inbounds i8, ptr %self, i64 8
  %e.0 = load ptr, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  %e.1 = load i64, ptr %7, align 8
; call zerocopy::error::AlignmentError<Src,Dst>::map_src
  %8 = call { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$7map_src17h204812e01e060d52E"(ptr %e.0, i64 %e.1) #14
  %_5.0 = extractvalue { ptr, i64 } %8, 0
  %_5.1 = extractvalue { ptr, i64 } %8, 1
  %9 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %_5.0, ptr %9, align 8
  %10 = getelementptr inbounds i8, ptr %9, i64 8
  store i64 %_5.1, ptr %10, align 8
  store i64 0, ptr %_0, align 8
  br label %bb6

bb6:                                              ; preds = %bb2, %bb3
  ret void

bb1:                                              ; No predecessors!
  unreachable
}

; zerocopy::error::SizeError<Src,Dst>::new
; Function Attrs: nounwind nonlazybind
define internal align 1 ptr @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17h17cc28c5c583c726E"(ptr align 1 %src) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h5ddb3b45459da16eE"() #14
  ret ptr %src
}

; zerocopy::error::SizeError<Src,Dst>::new
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17h46c0ab41b59d907bE"(ptr align 1 %src.0, i64 %src.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h2c77c6482e67ff5aE"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %src.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %src.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::error::SizeError<Src,Dst>::new
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17h4ec66291b0b58be6E"() unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  ret void
}

; zerocopy::error::SizeError<Src,Dst>::new
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17h844846c0e1a3bda9E"(ptr align 1 %src.0, i64 %src.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd13491eea66327dcE"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %src.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %src.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::error::SizeError<Src,Dst>::new
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17ha3510e5bc3493db0E"(ptr align 1 %src.0, i64 %src.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h2bb6f689937470e7E"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %src.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %src.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::error::SizeError<Src,Dst>::new
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17hdb2b84825caa4500E"(ptr %src.0, i64 %src.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %src.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %src.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::error::SizeError<Src,Dst>::new
; Function Attrs: nounwind nonlazybind
define internal align 1 ptr @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17hef446897463d0a96E"(ptr align 1 %src) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h5ddb3b45459da16eE"() #14
  ret ptr %src
}

; zerocopy::error::SizeError<Src,Dst>::into
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$4into17h65b4ace548f19de7E"(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %self.0, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  store i64 %self.1, ptr %1, align 8
  store i64 1, ptr %_0, align 8
  ret void
}

; zerocopy::error::SizeError<Src,Dst>::into
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$4into17h7922f2f716402c56E"(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %self.0, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  store i64 %self.1, ptr %1, align 8
  store i64 1, ptr %_0, align 8
  ret void
}

; zerocopy::error::SizeError<Src,Dst>::into
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$4into17heed897796300af4cE"(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %self.0, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  store i64 %self.1, ptr %1, align 8
  store i64 1, ptr %_0, align 8
  ret void
}

; zerocopy::error::SizeError<Src,Dst>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$7map_src17h756d3f1aeb49a29aE"(ptr align 8 %f) unnamed_addr #0 {
start:
  %_1.i = alloca [8 x i8], align 8
  store ptr %f, ptr %_1.i, align 8
; call core::mem::drop
  call void @_ZN4core3mem4drop17h1eaf4b0d526cfd48E() #14
  %_5.i = load ptr, ptr %_1.i, align 8
  %_4.0.i = load ptr, ptr %_5.i, align 8
  %0 = getelementptr inbounds i8, ptr %_5.i, i64 8
  %_4.1.i = load i64, ptr %0, align 8
; call zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
  %1 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17h7999d45e09566338E"(ptr %_4.0.i, i64 %_4.1.i) #14
  %_0.0.i = extractvalue { ptr, i64 } %1, 0
  %_0.1.i = extractvalue { ptr, i64 } %1, 1
  %_3.0 = extractvalue { ptr, i64 } %1, 0
  %_3.1 = extractvalue { ptr, i64 } %1, 1
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  %2 = insertvalue { ptr, i64 } poison, ptr %_3.0, 0
  %3 = insertvalue { ptr, i64 } %2, i64 %_3.1, 1
  ret { ptr, i64 } %3
}

; zerocopy::error::SizeError<Src,Dst>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$7map_src17h77a4b16362fc8f14E"(ptr %self.0, i64 %self.1) unnamed_addr #0 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  ret void
}

; zerocopy::error::SizeError<Src,Dst>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$7map_src17h91554b315c08677aE"(ptr %self.0, i64 %self.1) unnamed_addr #0 {
start:
; call zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
  %0 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17h7999d45e09566338E"(ptr %self.0, i64 %self.1) #14
  %_0.0.i = extractvalue { ptr, i64 } %0, 0
  %_0.1.i = extractvalue { ptr, i64 } %0, 1
  %_3.0 = extractvalue { ptr, i64 } %0, 0
  %_3.1 = extractvalue { ptr, i64 } %0, 1
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  %1 = insertvalue { ptr, i64 } poison, ptr %_3.0, 0
  %2 = insertvalue { ptr, i64 } %1, i64 %_3.1, 1
  ret { ptr, i64 } %2
}

; zerocopy::error::SizeError<Src,Dst>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$7map_src17hf823c08b31dea1dfE"(ptr %self.0, i64 %self.1) unnamed_addr #0 {
start:
; call zerocopy::FromBytes::ref_from_bytes::{{closure}}
  %0 = call { ptr, i64 } @"_ZN8zerocopy9FromBytes14ref_from_bytes28_$u7b$$u7b$closure$u7d$$u7d$17hbaaefa6ef958b60bE"(ptr %self.0, i64 %self.1) #14
  %_3.0 = extractvalue { ptr, i64 } %0, 0
  %_3.1 = extractvalue { ptr, i64 } %0, 1
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  %1 = insertvalue { ptr, i64 } poison, ptr %_3.0, 0
  %2 = insertvalue { ptr, i64 } %1, i64 %_3.1, 1
  ret { ptr, i64 } %2
}

; zerocopy::error::SizeError<Src,Dst>::with_dst
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$8with_dst17h919ef6595d35425dE"(ptr align 1 %self.0, i64 %self.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd988217da53bf241E"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %self.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %self.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::error::SizeError<Src,Dst>::with_dst
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$8with_dst17ha92b9efa146cad10E"(ptr align 1 %self.0, i64 %self.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %self.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %self.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::error::SizeError<Src,Dst>::with_dst
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$8with_dst17hedf4e3d124b30148E"(ptr align 1 %self.0, i64 %self.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h10b7f08ebd2ff639E"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %self.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %self.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::error::AlignmentError<Src,Dst>::new_unchecked
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$13new_unchecked17h874cb1acc4959203E"() unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd13491eea66327dcE"() #14
  ret void
}

; zerocopy::error::AlignmentError<Src,Dst>::new_unchecked
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$13new_unchecked17h878b9f09874c69c2E"() unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h2c77c6482e67ff5aE"() #14
  ret void
}

; zerocopy::error::AlignmentError<Src,Dst>::new_unchecked
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$13new_unchecked17hd391c7402348796aE"() unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h2bb6f689937470e7E"() #14
  ret void
}

; zerocopy::error::AlignmentError<Src,Dst>::new_unchecked
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$13new_unchecked17hdec382a38f918049E"(ptr %src.0, i64 %src.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %src.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %src.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::error::AlignmentError<Src,Dst>::into
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$4into17h16a071609168b15cE"(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %self.0, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  store i64 %self.1, ptr %1, align 8
  store i64 0, ptr %_0, align 8
  ret void
}

; zerocopy::error::AlignmentError<Src,Dst>::into
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$4into17h306e1a2eddecd6b0E"(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %self.0, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  store i64 %self.1, ptr %1, align 8
  store i64 0, ptr %_0, align 8
  ret void
}

; zerocopy::error::AlignmentError<Src,Dst>::into
; Function Attrs: nounwind nonlazybind
define internal void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$4into17h42b33bd17edf970bE"(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %self.0, i64 %self.1) unnamed_addr #1 {
start:
  %0 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %self.0, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 8
  store i64 %self.1, ptr %1, align 8
  store i64 0, ptr %_0, align 8
  ret void
}

; zerocopy::error::AlignmentError<Src,Dst>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$7map_src17h204812e01e060d52E"(ptr %self.0, i64 %self.1) unnamed_addr #0 {
start:
; call zerocopy::FromBytes::ref_from_bytes::{{closure}}
  %0 = call { ptr, i64 } @"_ZN8zerocopy9FromBytes14ref_from_bytes28_$u7b$$u7b$closure$u7d$$u7d$17hbaaefa6ef958b60bE"(ptr %self.0, i64 %self.1) #14
  %_3.0 = extractvalue { ptr, i64 } %0, 0
  %_3.1 = extractvalue { ptr, i64 } %0, 1
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  %1 = insertvalue { ptr, i64 } poison, ptr %_3.0, 0
  %2 = insertvalue { ptr, i64 } %1, i64 %_3.1, 1
  ret { ptr, i64 } %2
}

; zerocopy::error::AlignmentError<Src,Dst>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$7map_src17h41d52c6c53d961dbE"(ptr %self.0, i64 %self.1) unnamed_addr #0 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  ret void
}

; zerocopy::error::AlignmentError<Src,Dst>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$7map_src17h533da408a212c2eeE"(ptr %self.0, i64 %self.1) unnamed_addr #0 {
start:
; call zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
  %0 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17h7999d45e09566338E"(ptr %self.0, i64 %self.1) #14
  %_0.0.i = extractvalue { ptr, i64 } %0, 0
  %_0.1.i = extractvalue { ptr, i64 } %0, 1
  %_3.0 = extractvalue { ptr, i64 } %0, 0
  %_3.1 = extractvalue { ptr, i64 } %0, 1
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  %1 = insertvalue { ptr, i64 } poison, ptr %_3.0, 0
  %2 = insertvalue { ptr, i64 } %1, i64 %_3.1, 1
  ret { ptr, i64 } %2
}

; zerocopy::error::AlignmentError<Src,Dst>::map_src
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$7map_src17h5fb8eec72bc12cc7E"(ptr align 8 %f) unnamed_addr #0 {
start:
  %_1.i = alloca [8 x i8], align 8
  store ptr %f, ptr %_1.i, align 8
; call core::mem::drop
  call void @_ZN4core3mem4drop17h1eaf4b0d526cfd48E() #14
  %_5.i = load ptr, ptr %_1.i, align 8
  %_4.0.i = load ptr, ptr %_5.i, align 8
  %0 = getelementptr inbounds i8, ptr %_5.i, i64 8
  %_4.1.i = load i64, ptr %0, align 8
; call zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
  %1 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17h7999d45e09566338E"(ptr %_4.0.i, i64 %_4.1.i) #14
  %_0.0.i = extractvalue { ptr, i64 } %1, 0
  %_0.1.i = extractvalue { ptr, i64 } %1, 1
  %_3.0 = extractvalue { ptr, i64 } %1, 0
  %_3.1 = extractvalue { ptr, i64 } %1, 1
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd0521df090875ab2E"() #14
  %2 = insertvalue { ptr, i64 } poison, ptr %_3.0, 0
  %3 = insertvalue { ptr, i64 } %2, i64 %_3.1, 1
  ret { ptr, i64 } %3
}

; zerocopy::error::AlignmentError<Src,Dst>::with_src
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$8with_src17h050c9819055759edE"(ptr align 1 %new_src.0, i64 %new_src.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17hd13491eea66327dcE"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %new_src.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %new_src.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::error::AlignmentError<Src,Dst>::with_src
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$8with_src17h634a45c428572e75E"(ptr align 1 %new_src.0, i64 %new_src.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h2bb6f689937470e7E"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %new_src.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %new_src.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::error::AlignmentError<Src,Dst>::with_src
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$8with_src17h9c9e30cbe7f87ce1E"(ptr align 1 %new_src.0, i64 %new_src.1) unnamed_addr #1 {
start:
; call <zerocopy::util::SendSyncPhantomData<T> as core::default::Default>::default
  call void @"_ZN87_$LT$zerocopy..util..SendSyncPhantomData$LT$T$GT$$u20$as$u20$core..default..Default$GT$7default17h2c77c6482e67ff5aE"() #14
  %0 = insertvalue { ptr, i64 } poison, ptr %new_src.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %new_src.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::layout::SizeInfo::try_to_nonzero_elem_size
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN8zerocopy6layout8SizeInfo24try_to_nonzero_elem_size17hccd2473991364d9bE(ptr sret([40 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
  %_12 = alloca [32 x i8], align 8
  %_9 = alloca [8 x i8], align 8
  %_2 = alloca [32 x i8], align 8
  %0 = load i64, ptr %self, align 8
  %1 = icmp eq i64 %0, 0
  %_3 = select i1 %1, i64 0, i64 1
  %2 = trunc nuw i64 %_3 to i1
  br i1 %2, label %bb2, label %bb3

bb2:                                              ; preds = %start
  %3 = getelementptr inbounds i8, ptr %self, i64 8
  %offset = load i64, ptr %3, align 8
  %4 = getelementptr inbounds i8, ptr %self, i64 16
  %elem_size = load i64, ptr %4, align 8
  %5 = getelementptr inbounds i8, ptr %self, i64 24
  %size_base = load i64, ptr %5, align 8
  %size_rounding_align_and_phase = load i64, ptr %self, align 8
; call core::num::nonzero::NonZero<T>::new
  %6 = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3new17h61bb2493f7c27af8E"(i64 %elem_size) #14
  store i64 %6, ptr %_9, align 8
  %7 = load i64, ptr %_9, align 8
  %8 = icmp eq i64 %7, 0
  %_10 = select i1 %8, i64 0, i64 1
  %9 = trunc nuw i64 %_10 to i1
  br i1 %9, label %bb5, label %bb6

bb3:                                              ; preds = %start
  %10 = getelementptr inbounds i8, ptr %self, i64 8
  %size = load i64, ptr %10, align 8
  %11 = getelementptr inbounds i8, ptr %_2, i64 8
  store i64 %size, ptr %11, align 8
  store i64 0, ptr %_2, align 8
  br label %bb7

bb7:                                              ; preds = %bb5, %bb3
  %12 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %12, ptr align 8 %_2, i64 32, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb8

bb5:                                              ; preds = %bb2
  %elem_size1 = load i64, ptr %_9, align 8
  %13 = getelementptr inbounds i8, ptr %_12, i64 16
  store i64 %offset, ptr %13, align 8
  store i64 %elem_size1, ptr %_12, align 8
  %14 = getelementptr inbounds i8, ptr %_12, i64 24
  store i64 %size_base, ptr %14, align 8
  %15 = getelementptr inbounds i8, ptr %_12, i64 8
  store i64 %size_rounding_align_and_phase, ptr %15, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_2, ptr align 8 %_12, i64 32, i1 false)
  br label %bb7

bb6:                                              ; preds = %bb2
  store i64 0, ptr %_0, align 8
  br label %bb8

bb8:                                              ; preds = %bb6, %bb7
  ret void

bb1:                                              ; No predecessors!
  unreachable
}

; zerocopy::pointer::ptr::_conversions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::transmute_with
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr12_conversions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$14transmute_with17hecdd44ce24bf69e2E"(ptr %self) unnamed_addr #0 {
start:
; call zerocopy::pointer::ptr::_conversions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::project_transmute_unchecked
  %_0 = call ptr @"_ZN8zerocopy7pointer3ptr12_conversions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$27project_transmute_unchecked17hcfce6057122a17dcE"(ptr %self) #14
  ret ptr %_0
}

; zerocopy::pointer::ptr::_conversions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::recall_validity
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr12_conversions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$15recall_validity17h126b8dae3c9c939eE"(ptr %self) unnamed_addr #0 {
start:
; call zerocopy::pointer::ptr::_conversions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::transmute_with
  %ptr = call ptr @"_ZN8zerocopy7pointer3ptr12_conversions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$14transmute_with17hecdd44ce24bf69e2E"(ptr %self) #14
; call zerocopy::pointer::ptr::_transitions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::assume_alignment
  %_0 = call ptr @"_ZN8zerocopy7pointer3ptr12_transitions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$16assume_alignment17hf3cd29bb6f9c0ea7E"(ptr %ptr) #14
  ret ptr %_0
}

; zerocopy::pointer::ptr::_conversions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::project_transmute_unchecked
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr12_conversions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$27project_transmute_unchecked17hcfce6057122a17dcE"(ptr %0) unnamed_addr #0 {
start:
  %src.i = alloca [8 x i8], align 8
  %self = alloca [8 x i8], align 8
  store ptr %0, ptr %self, align 8
; call zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
  %_3 = call ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17hc99a8fd1daa208b5E"(ptr align 8 %self) #14
  store ptr %_3, ptr %src.i, align 8
  %_2.i.i = load ptr, ptr %src.i, align 8
; call core::ptr::non_null::NonNull<T>::new_unchecked
  %projected_non_null.i = call ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h1c6dc69b456e977bE"(ptr %_2.i.i, ptr align 8 @alloc_7df927a12c94620fa0c9f4ff08fe1b25) #14
; call zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
  %_0 = call ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17hc12b1b0b6dcfdd76E"(ptr %projected_non_null.i) #14
  ret ptr %_0
}

; zerocopy::pointer::ptr::_conversions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::as_ref
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy7pointer3ptr12_conversions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$6as_ref17h6aa45dbbf1297d7cE"(ptr %0, i64 %1) unnamed_addr #0 {
start:
  %_4 = alloca [16 x i8], align 8
  %raw = alloca [16 x i8], align 8
  %self = alloca [16 x i8], align 8
  store ptr %0, ptr %self, align 8
  %2 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %1, ptr %2, align 8
; call zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
  %3 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17h801ca11e9df76339E"(ptr align 8 %self) #14
  %4 = extractvalue { ptr, i64 } %3, 0
  %5 = extractvalue { ptr, i64 } %3, 1
  store ptr %4, ptr %_4, align 8
  %6 = getelementptr inbounds i8, ptr %_4, i64 8
  store i64 %5, ptr %6, align 8
  %_0.0.i = load ptr, ptr %_4, align 8
  %7 = getelementptr inbounds i8, ptr %_4, i64 8
  %_0.1.i = load i64, ptr %7, align 8
  %8 = insertvalue { ptr, i64 } poison, ptr %_0.0.i, 0
  %9 = insertvalue { ptr, i64 } %8, i64 %_0.1.i, 1
  %10 = extractvalue { ptr, i64 } %9, 0
  %11 = extractvalue { ptr, i64 } %9, 1
  store ptr %10, ptr %raw, align 8
  %12 = getelementptr inbounds i8, ptr %raw, i64 8
  store i64 %11, ptr %12, align 8
  %_3.0.i = load ptr, ptr %raw, align 8
  %13 = getelementptr inbounds i8, ptr %raw, i64 8
  %_3.1.i = load i64, ptr %13, align 8
  %14 = insertvalue { ptr, i64 } poison, ptr %_3.0.i, 0
  %15 = insertvalue { ptr, i64 } %14, i64 %_3.1.i, 1
  %_0.0 = extractvalue { ptr, i64 } %15, 0
  %_0.1 = extractvalue { ptr, i64 } %15, 1
  %16 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %17 = insertvalue { ptr, i64 } %16, i64 %_0.1, 1
  ret { ptr, i64 } %17
}

; zerocopy::pointer::ptr::_conversions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::as_ref
; Function Attrs: inlinehint nounwind nonlazybind
define internal align 1 ptr @"_ZN8zerocopy7pointer3ptr12_conversions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$6as_ref17ha7b0957f87e2139dE"(ptr %0) unnamed_addr #0 {
start:
  %_4 = alloca [8 x i8], align 8
  %raw = alloca [8 x i8], align 8
  %self = alloca [8 x i8], align 8
  store ptr %0, ptr %self, align 8
; call zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
  %1 = call ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17h2b9c1ccbc92ac579E"(ptr align 8 %self) #14
  store ptr %1, ptr %_4, align 8
  %_0.i = load ptr, ptr %_4, align 8
  store ptr %_0.i, ptr %raw, align 8
  %_3.i = load ptr, ptr %raw, align 8
  ret ptr %_3.i
}

; zerocopy::pointer::ptr::_transitions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::assume_alignment
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr12_transitions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$16assume_alignment17hf3cd29bb6f9c0ea7E"(ptr %self) unnamed_addr #0 {
start:
; call zerocopy::pointer::ptr::_transitions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::assume_invariants
  %_0 = call ptr @"_ZN8zerocopy7pointer3ptr12_transitions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$17assume_invariants17hc3588a06e6850170E"(ptr %self) #14
  ret ptr %_0
}

; zerocopy::pointer::ptr::_transitions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::assume_invariants
; Function Attrs: nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr12_transitions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$17assume_invariants17hc3588a06e6850170E"(ptr %0) unnamed_addr #1 {
start:
  %self = alloca [8 x i8], align 8
  store ptr %0, ptr %self, align 8
; call zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
  %_2 = call ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17hba58c1318d6f5821E"(ptr align 8 %self) #14
; call zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
  %_0 = call ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17h56fbfb88c6a41e88E"(ptr %_2) #14
  ret ptr %_0
}

; zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
; Function Attrs: nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17h56fbfb88c6a41e88E"(ptr %ptr) unnamed_addr #1 {
start:
  ret ptr %ptr
}

; zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
; Function Attrs: nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17h7999d45e09566338E"(ptr %ptr.0, i64 %ptr.1) unnamed_addr #1 {
start:
  %0 = insertvalue { ptr, i64 } poison, ptr %ptr.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %ptr.1, 1
  ret { ptr, i64 } %1
}

; zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
; Function Attrs: nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17hc12b1b0b6dcfdd76E"(ptr %ptr) unnamed_addr #1 {
start:
  ret ptr %ptr
}

; zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
; Function Attrs: nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17he81ccfeaff6c6b60E"(ptr %ptr) unnamed_addr #1 {
start:
  ret ptr %ptr
}

; zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17h2b9c1ccbc92ac579E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_0 = load ptr, ptr %self, align 8
  ret ptr %_0
}

; zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17h801ca11e9df76339E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_0.0 = load ptr, ptr %self, align 8
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_0.1 = load i64, ptr %0, align 8
  %1 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %2 = insertvalue { ptr, i64 } %1, i64 %_0.1, 1
  ret { ptr, i64 } %2
}

; zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17hba58c1318d6f5821E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_0 = load ptr, ptr %self, align 8
  ret ptr %_0
}

; zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
; Function Attrs: inlinehint nounwind nonlazybind
define internal ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17hc99a8fd1daa208b5E"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_0 = load ptr, ptr %self, align 8
  ret ptr %_0
}

; zerocopy::pointer::ptr::_project::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::len
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN8zerocopy7pointer3ptr8_project63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$3len17hf62f1d4fceb2850dE"(ptr align 8 %self) unnamed_addr #0 {
start:
  %_3 = alloca [8 x i8], align 8
; call zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
  %0 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17h801ca11e9df76339E"(ptr align 8 %self) #14
  %_4.0 = extractvalue { ptr, i64 } %0, 0
  %_4.1 = extractvalue { ptr, i64 } %0, 1
; call zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::meta
  %1 = call i64 @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$4meta17h687c92233b93586eE"(ptr %_4.0, i64 %_4.1) #14
  store i64 %1, ptr %_3, align 8
; call zerocopy::util::len_of::MetadataOf<T>::get
  %_0 = call i64 @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$3get17h5aa6cb6cfb0917d9E"(ptr align 8 %_3) #14
  ret i64 %_0
}

; zerocopy::pointer::ptr::_project::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::is_empty
; Function Attrs: inlinehint nounwind nonlazybind
define internal zeroext i1 @"_ZN8zerocopy7pointer3ptr8_project63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$8is_empty17hd0e663a8b7fd10fbE"(ptr align 8 %self) unnamed_addr #0 {
start:
; call zerocopy::pointer::ptr::_project::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::len
  %_2 = call i64 @"_ZN8zerocopy7pointer3ptr8_project63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$3len17hf62f1d4fceb2850dE"(ptr align 8 %self) #14
  %_0 = icmp eq i64 %_2, 0
  ret i1 %_0
}

; zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::trailing_slice
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$14trailing_slice17h8c00b148dec6e90eE"(ptr %0, i64 %1) unnamed_addr #0 {
start:
  %_13 = alloca [8 x i8], align 8
  %_3 = alloca [32 x i8], align 8
  %self = alloca [16 x i8], align 8
  store ptr %0, ptr %self, align 8
  %2 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %1, ptr %2, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_3, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.2, i64 32, i1 false)
  %3 = getelementptr inbounds i8, ptr %_3, i64 8
  %offset = load i64, ptr %3, align 8
  %_0.0.i3 = load ptr, ptr %self, align 8
  %4 = getelementptr inbounds i8, ptr %self, i64 8
  %_0.1.i4 = load i64, ptr %4, align 8
  %5 = insertvalue { ptr, i64 } poison, ptr %_0.0.i3, 0
  %6 = insertvalue { ptr, i64 } %5, i64 %_0.1.i4, 1
  %_6.0 = extractvalue { ptr, i64 } %6, 0
  %_6.1 = extractvalue { ptr, i64 } %6, 1
; call core::ptr::non_null::NonNull<T>::cast
  %_5 = call ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17h110a24a51af34c8dE"(ptr %_6.0, i64 %_6.1) #14
  %_0.i = getelementptr inbounds nuw i8, ptr %_5, i64 %offset
; call core::ptr::non_null::NonNull<T>::new_unchecked
  %bytes2 = call ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h25de8935aa4ad477E"(ptr %_0.i, ptr align 8 @alloc_2b3b8bf8575d7b890532fae13f928a4a) #14
  %_14.0 = load ptr, ptr %self, align 8
  %7 = getelementptr inbounds i8, ptr %self, i64 8
  %_14.1 = load i64, ptr %7, align 8
; call zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::meta
  %8 = call i64 @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$4meta17h687c92233b93586eE"(ptr %_14.0, i64 %_14.1) #14
  store i64 %8, ptr %_13, align 8
; call zerocopy::util::len_of::MetadataOf<T>::get
  %_11 = call i64 @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$3get17h5aa6cb6cfb0917d9E"(ptr align 8 %_13) #14
; call core::ptr::non_null::NonNull<T>::cast
  %_3.i = call ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17hf7dee4d24dee0e26E"(ptr %bytes2) #14
; call core::ptr::non_null::NonNull<[T]>::slice_from_raw_parts
  %9 = call { ptr, i64 } @"_ZN4core3ptr8non_null26NonNull$LT$$u5b$T$u5d$$GT$20slice_from_raw_parts17h04e6fc05340fc983E"(ptr %_3.i, i64 %_11) #14
  %_0.0.i = extractvalue { ptr, i64 } %9, 0
  %_0.1.i = extractvalue { ptr, i64 } %9, 1
  %ptr.0 = extractvalue { ptr, i64 } %9, 0
  %ptr.1 = extractvalue { ptr, i64 } %9, 1
  %_0.0 = extractvalue { ptr, i64 } %9, 0
  %_0.1 = extractvalue { ptr, i64 } %9, 1
  %10 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %11 = insertvalue { ptr, i64 } %10, i64 %_0.1, 1
  ret { ptr, i64 } %11
}

; zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::split_at_unchecked
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$18split_at_unchecked17heee872bc71fa1092E"(ptr sret([32 x i8]) align 8 %_0, ptr %self.0, i64 %self.1, i64 %0) unnamed_addr #0 {
start:
  %_11 = alloca [8 x i8], align 8
  %l_len = alloca [8 x i8], align 8
  store i64 %0, ptr %l_len, align 8
; call zerocopy::util::len_of::MetadataOf<T>::get
  %l_len1 = call i64 @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$3get17h5aa6cb6cfb0917d9E"(ptr align 8 %l_len) #14
; call zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::with_meta
  %1 = call { ptr, i64 } @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$9with_meta17h5b269fe0784e6078E"(ptr %self.0, i64 %self.1, i64 %l_len1) #14
  %left.0 = extractvalue { ptr, i64 } %1, 0
  %left.1 = extractvalue { ptr, i64 } %1, 1
; call zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::trailing_slice
  %2 = call { ptr, i64 } @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$14trailing_slice17h8c00b148dec6e90eE"(ptr %self.0, i64 %self.1) #14
  %right.0 = extractvalue { ptr, i64 } %2, 0
  %right.1 = extractvalue { ptr, i64 } %2, 1
; call zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::meta
  %3 = call i64 @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$4meta17h687c92233b93586eE"(ptr %self.0, i64 %self.1) #14
  store i64 %3, ptr %_11, align 8
; call zerocopy::util::len_of::MetadataOf<T>::get
  %_9 = call i64 @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$3get17h5aa6cb6cfb0917d9E"(ptr align 8 %_11) #14
; call zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<[T]>>::slice_unchecked
  %4 = call { ptr, i64 } @"_ZN8zerocopy7pointer5inner77_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$$u5b$T$u5d$$GT$$GT$15slice_unchecked17ha6ee66c00bcb37b6E"(ptr %right.0, i64 %right.1, i64 %l_len1, i64 %_9) #14
  %right.02 = extractvalue { ptr, i64 } %4, 0
  %right.13 = extractvalue { ptr, i64 } %4, 1
  store ptr %left.0, ptr %_0, align 8
  %5 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %left.1, ptr %5, align 8
  %6 = getelementptr inbounds i8, ptr %_0, i64 16
  store ptr %right.02, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  store i64 %right.13, ptr %7, align 8
  ret void
}

; zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::meta
; Function Attrs: inlinehint nounwind nonlazybind
define internal i64 @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$4meta17h687c92233b93586eE"(ptr %0, i64 %1) unnamed_addr #0 {
start:
  %self = alloca [16 x i8], align 8
  store ptr %0, ptr %self, align 8
  %2 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %1, ptr %2, align 8
  %_2.0.i = load ptr, ptr %self, align 8
  %3 = getelementptr inbounds i8, ptr %self, i64 8
  %_2.1.i = load i64, ptr %3, align 8
  %4 = insertvalue { ptr, i64 } poison, ptr %_2.0.i, 0
  %5 = insertvalue { ptr, i64 } %4, i64 %_2.1.i, 1
  %6 = insertvalue { ptr, i64 } poison, ptr %_2.0.i, 0
  %7 = insertvalue { ptr, i64 } %6, i64 %_2.1.i, 1
  %_3.0 = extractvalue { ptr, i64 } %7, 0
  %_3.1 = extractvalue { ptr, i64 } %7, 1
; call zerocopy::util::len_of::MetadataOf<T>::new_unchecked
  %_0 = call i64 @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$13new_unchecked17hbf283257ae23f131E"(i64 %_3.1) #14
  ret i64 %_0
}

; zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::from_ref
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$8from_ref17hc7bd5b06f49ddec7E"(ptr align 1 %ptr.0, i64 %ptr.1) unnamed_addr #0 {
start:
; call <core::ptr::non_null::NonNull<T> as core::convert::From<&T>>::from
  %0 = call { ptr, i64 } @"_ZN90_$LT$core..ptr..non_null..NonNull$LT$T$GT$$u20$as$u20$core..convert..From$LT$$RF$T$GT$$GT$4from17hd39d9ba562bec714E"(ptr align 1 %ptr.0, i64 %ptr.1) #14
  %ptr.01 = extractvalue { ptr, i64 } %0, 0
  %ptr.12 = extractvalue { ptr, i64 } %0, 1
  %_0.0 = extractvalue { ptr, i64 } %0, 0
  %_0.1 = extractvalue { ptr, i64 } %0, 1
  %1 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %2 = insertvalue { ptr, i64 } %1, i64 %_0.1, 1
  ret { ptr, i64 } %2
}

; zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::with_meta
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$9with_meta17h5b269fe0784e6078E"(ptr %0, i64 %1, i64 %meta) unnamed_addr #0 {
start:
  %self = alloca [16 x i8], align 8
  store ptr %0, ptr %self, align 8
  %2 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %1, ptr %2, align 8
  %_0.0.i1 = load ptr, ptr %self, align 8
  %3 = getelementptr inbounds i8, ptr %self, i64 8
  %_0.1.i2 = load i64, ptr %3, align 8
  %4 = insertvalue { ptr, i64 } poison, ptr %_0.0.i1, 0
  %5 = insertvalue { ptr, i64 } %4, i64 %_0.1.i2, 1
  %_5.0 = extractvalue { ptr, i64 } %5, 0
  %_5.1 = extractvalue { ptr, i64 } %5, 1
; call core::ptr::non_null::NonNull<T>::cast
  %_4 = call ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17h110a24a51af34c8dE"(ptr %_5.0, i64 %_5.1) #14
; call core::ptr::non_null::NonNull<T>::cast
  %_3.i = call ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17hf7dee4d24dee0e26E"(ptr %_4) #14
; call core::ptr::non_null::NonNull<[T]>::slice_from_raw_parts
  %6 = call { ptr, i64 } @"_ZN4core3ptr8non_null26NonNull$LT$$u5b$T$u5d$$GT$20slice_from_raw_parts17h04e6fc05340fc983E"(ptr %_3.i, i64 %meta) #14
  %_0.0.i = extractvalue { ptr, i64 } %6, 0
  %_0.1.i = extractvalue { ptr, i64 } %6, 1
  %raw.0 = extractvalue { ptr, i64 } %6, 0
  %raw.1 = extractvalue { ptr, i64 } %6, 1
  %_0.0 = extractvalue { ptr, i64 } %6, 0
  %_0.1 = extractvalue { ptr, i64 } %6, 1
  %7 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %8 = insertvalue { ptr, i64 } %7, i64 %_0.1, 1
  ret { ptr, i64 } %8
}

; zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<[T]>>::slice_unchecked
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy7pointer5inner77_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$$u5b$T$u5d$$GT$$GT$15slice_unchecked17ha6ee66c00bcb37b6E"(ptr %0, i64 %1, i64 %range.0, i64 %range.1) unnamed_addr #0 {
start:
  %self = alloca [16 x i8], align 8
  store ptr %0, ptr %self, align 8
  %2 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %1, ptr %2, align 8
  %_0.0.i = load ptr, ptr %self, align 8
  %3 = getelementptr inbounds i8, ptr %self, i64 8
  %_0.1.i = load i64, ptr %3, align 8
  %4 = insertvalue { ptr, i64 } poison, ptr %_0.0.i, 0
  %5 = insertvalue { ptr, i64 } %4, i64 %_0.1.i, 1
  %_5.0 = extractvalue { ptr, i64 } %5, 0
  %_5.1 = extractvalue { ptr, i64 } %5, 1
; call core::ptr::non_null::NonNull<T>::cast
  %_4 = call ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17h110a24a51af34c8dE"(ptr %_5.0, i64 %_5.1) #14
  %_0.i4 = getelementptr inbounds nuw i8, ptr %_4, i64 %range.0
; call core::num::<impl usize>::unchecked_sub::precondition_check
  call void @"_ZN4core3num23_$LT$impl$u20$usize$GT$13unchecked_sub18precondition_check17h8b0b7e8c552b56ffE"(i64 %range.1, i64 %range.0, ptr align 8 @alloc_009fcd67ec40494897136844fb2e9cf2) #14
  %_0.i = sub nuw i64 %range.1, %range.0
; call core::ptr::slice_from_raw_parts_mut
  %6 = call { ptr, i64 } @_ZN4core3ptr24slice_from_raw_parts_mut17h9fe5a088220a3d11E(ptr %_0.i4, i64 %_0.i) #14
  %ptr.0 = extractvalue { ptr, i64 } %6, 0
  %ptr.1 = extractvalue { ptr, i64 } %6, 1
; call core::ptr::non_null::NonNull<T>::new_unchecked
  %7 = call { ptr, i64 } @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17hf6de2e43cf1c61b0E"(ptr %ptr.0, i64 %ptr.1, ptr align 8 @alloc_7655f6ef89bcdccd0e255f36da05e01b) #14
  %ptr.02 = extractvalue { ptr, i64 } %7, 0
  %ptr.13 = extractvalue { ptr, i64 } %7, 1
  %_0.0 = extractvalue { ptr, i64 } %7, 0
  %_0.1 = extractvalue { ptr, i64 } %7, 1
  %8 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %9 = insertvalue { ptr, i64 } %8, i64 %_0.1, 1
  ret { ptr, i64 } %9
}

; zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<[u8]>>::try_cast_into
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN8zerocopy7pointer5inner78_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$$u5b$u8$u5d$$GT$$GT$13try_cast_into17h3f9659ced87cb72fE"(ptr sret([32 x i8]) align 8 %_0, ptr %0, i64 %1, i1 zeroext %cast_type, i1 zeroext %meta) unnamed_addr #0 {
start:
  %2 = alloca [4 x i8], align 4
  %_12.i.i20.i = alloca [8 x i8], align 8
  %3 = alloca [4 x i8], align 4
  %_13.i.i = alloca [16 x i8], align 8
  %_8.i21.i = alloca [16 x i8], align 8
  %rounded_phase.i.i = alloca [8 x i8], align 8
  %_0.i22.i = alloca [16 x i8], align 8
  %4 = alloca [4 x i8], align 4
  %_12.i.i.i = alloca [8 x i8], align 8
  %_6.i.i = alloca [16 x i8], align 8
  %5 = alloca [4 x i8], align 4
  %6 = alloca [4 x i8], align 4
  %split_at.i2 = alloca [8 x i8], align 8
  %_40.i = alloca [1 x i8], align 1
  %_36.i = alloca [16 x i8], align 8
  %trailing.i = alloca [32 x i8], align 8
  %_34.i = alloca [1 x i8], align 1
  %_30.i = alloca [16 x i8], align 8
  %_27.i = alloca [1 x i8], align 1
  %offset.i = alloca [8 x i8], align 8
  %_16.i3 = alloca [48 x i8], align 8
  %_14.i4 = alloca [16 x i8], align 8
  %_10.i5 = alloca [48 x i8], align 8
  %size_info.i = alloca [32 x i8], align 8
  %_5.i = alloca [40 x i8], align 8
  %7 = alloca [48 x i8], align 8
  %_20.i = alloca [24 x i8], align 8
  %_19.i = alloca [24 x i8], align 8
  %_16.i = alloca [32 x i8], align 8
  %_15.i = alloca [48 x i8], align 8
  %_13.i = alloca [1 x i8], align 1
  %_10.i = alloca [16 x i8], align 8
  %_9.i = alloca [1 x i8], align 1
  %layout.i = alloca [48 x i8], align 8
  %bytes_len.i = alloca [8 x i8], align 8
  %_37 = alloca [24 x i8], align 8
  %_29 = alloca [32 x i8], align 8
  %target = alloca [16 x i8], align 8
  %_25 = alloca [32 x i8], align 8
  %_20 = alloca [24 x i8], align 8
  %_19 = alloca [24 x i8], align 8
  %elems = alloca [0 x i8], align 1
  %maybe_metadata = alloca [16 x i8], align 8
  %self = alloca [16 x i8], align 8
  store ptr %0, ptr %self, align 8
  %8 = getelementptr inbounds i8, ptr %self, i64 8
  store i64 %1, ptr %8, align 8
  %_2.0.i = load ptr, ptr %self, align 8
  %9 = getelementptr inbounds i8, ptr %self, i64 8
  %_2.1.i = load i64, ptr %9, align 8
  %10 = insertvalue { ptr, i64 } poison, ptr %_2.0.i, 0
  %11 = insertvalue { ptr, i64 } %10, i64 %_2.1.i, 1
  %12 = insertvalue { ptr, i64 } poison, ptr %_2.0.i, 0
  %13 = insertvalue { ptr, i64 } %12, i64 %_2.1.i, 1
  %_6.0 = extractvalue { ptr, i64 } %13, 0
  %_6.1 = extractvalue { ptr, i64 } %13, 1
  %_0.i1 = ptrtoint ptr %_6.0 to i64
  %_9.0 = load ptr, ptr %self, align 8
  %14 = getelementptr inbounds i8, ptr %self, i64 8
  %_9.1 = load i64, ptr %14, align 8
; call zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::meta
  %_8 = call i64 @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$4meta17h687c92233b93586eE"(ptr %_9.0, i64 %_9.1) #14
  store i64 %_8, ptr %bytes_len.i, align 8
  %_6.i = zext i1 %meta to i64
  br i1 %meta, label %bb2.i, label %bb3.i

bb2.i:                                            ; preds = %start
; call <() as zerocopy::PointerMetadata>::to_elem_count
  %_2.i.i = call i64 @"_ZN54_$LT$$LP$$RP$$u20$as$u20$zerocopy..PointerMetadata$GT$13to_elem_count17h01919dbaceb5bfd3E"() #14
; call <usize as zerocopy::PointerMetadata>::to_elem_count
  %_3.i.i = call i64 @"_ZN51_$LT$usize$u20$as$u20$zerocopy..PointerMetadata$GT$13to_elem_count17h9137fabb3c28584aE"(i64 0) #14
  %_0.i.i = icmp ule i64 %_2.i.i, %_3.i.i
  br i1 %_0.i.i, label %bb5.i, label %bb6.i

bb3.i:                                            ; preds = %start
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %layout.i, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.1, i64 48, i1 false)
  br label %bb10.i

bb10.i:                                           ; preds = %bb9.i, %bb3.i
; call zerocopy::util::len_of::MetadataOf<T>::get
  %_22.i = call i64 @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$3get17h5aa6cb6cfb0917d9E"(ptr align 8 %bytes_len.i) #14
  %_6.i6 = getelementptr inbounds i8, ptr %layout.i, i64 8
; call zerocopy::layout::SizeInfo::try_to_nonzero_elem_size
  call void @_ZN8zerocopy6layout8SizeInfo24try_to_nonzero_elem_size17hccd2473991364d9bE(ptr sret([40 x i8]) align 8 %_5.i, ptr align 8 %_6.i6) #14
  %_7.i = load i64, ptr %_5.i, align 8
  %15 = trunc nuw i64 %_7.i to i1
  br i1 %15, label %bb4.i, label %bb3.i7

bb4.i:                                            ; preds = %bb10.i
  %16 = getelementptr inbounds i8, ptr %_5.i, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %size_info.i, ptr align 8 %16, i64 32, i1 false)
; call core::num::<impl usize>::checked_add
  %17 = call { i64, i64 } @"_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_add17h07a6aef785bb2367E"(i64 %_0.i1, i64 %_22.i) #14
  %18 = extractvalue { i64, i64 } %17, 0
  %19 = extractvalue { i64, i64 } %17, 1
  store i64 %18, ptr %_14.i4, align 8
  %20 = getelementptr inbounds i8, ptr %_14.i4, i64 8
  store i64 %19, ptr %20, align 8
; call core::option::Option<T>::is_some
  %e.i = call zeroext i1 @"_ZN4core6option15Option$LT$T$GT$7is_some17hc4289163496f99cdE"(ptr align 8 %_14.i4) #14
  br i1 %e.i, label %bb10.i9, label %bb8.i8

bb3.i7:                                           ; preds = %bb10.i
; call core::fmt::rt::<impl core::fmt::Arguments>::new_const
  call void @"_ZN4core3fmt2rt38_$LT$impl$u20$core..fmt..Arguments$GT$9new_const17hc17ead96ff728c9aE"(ptr sret([48 x i8]) align 8 %_10.i5, ptr align 8 @alloc_6e5ff68ef613cd819c351642e46138cf) #14
; call core::panicking::panic_fmt
  call void @_ZN4core9panicking9panic_fmt17hc49fc28484033487E(ptr align 8 %_10.i5, ptr align 8 @alloc_c0a3c00142921a8f95892928b7888f5e) #15
  unreachable

bb8.i8:                                           ; preds = %bb4.i
; call core::fmt::rt::<impl core::fmt::Arguments>::new_const
  call void @"_ZN4core3fmt2rt38_$LT$impl$u20$core..fmt..Arguments$GT$9new_const17hc17ead96ff728c9aE"(ptr sret([48 x i8]) align 8 %_16.i3, ptr align 8 @alloc_a8b9d51f4716b1abea4342af19a187da) #14
; call core::panicking::panic_fmt
  call void @_ZN4core9panicking9panic_fmt17hc49fc28484033487E(ptr align 8 %_16.i3, ptr align 8 @alloc_541d4452affef989fd65692928d2720e) #15
  unreachable

bb10.i9:                                          ; preds = %bb4.i
  %_19.i10 = zext i1 %cast_type to i64
  br i1 %cast_type, label %bb11.i, label %bb12.i

bb11.i:                                           ; preds = %bb10.i9
  store i64 %_22.i, ptr %offset.i, align 8
  br label %bb13.i

bb12.i:                                           ; preds = %bb10.i9
  store i64 0, ptr %offset.i, align 8
  br label %bb13.i

bb13.i:                                           ; preds = %bb12.i, %bb11.i
  %_22.i11 = load i64, ptr %offset.i, align 8
  %21 = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %_0.i1, i64 %_22.i11)
  %_23.0.i = extractvalue { i64, i1 } %21, 0
  %_23.1.i = extractvalue { i64, i1 } %21, 1
  br i1 %_23.1.i, label %panic.i, label %bb14.i12

bb14.i12:                                         ; preds = %bb13.i
  %_25.i = load i64, ptr %layout.i, align 8
; call core::num::nonzero::NonZero<T>::get
  %_24.i13 = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %_25.i) #14
  %_26.i = icmp eq i64 %_24.i13, 0
  br i1 %_26.i, label %panic1.i, label %bb16.i

panic.i:                                          ; preds = %bb13.i
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_add_overflow17h371a9588e01a5f2aE(ptr align 8 @alloc_5682d82eaed587cd5c5b8bab05d565ca) #15
  unreachable

bb16.i:                                           ; preds = %bb14.i12
  %_20.i14 = urem i64 %_23.0.i, %_24.i13
  %22 = icmp eq i64 %_20.i14, 0
  br i1 %22, label %bb18.i, label %bb17.i

panic1.i:                                         ; preds = %bb14.i12
; call core::panicking::panic_const::panic_const_rem_by_zero
  call void @_ZN4core9panicking11panic_const23panic_const_rem_by_zero17hb2eecb9bde6b0e42E(ptr align 8 @alloc_5682d82eaed587cd5c5b8bab05d565ca) #15
  unreachable

bb18.i:                                           ; preds = %bb16.i
  %23 = load i64, ptr %size_info.i, align 8
  %24 = icmp eq i64 %23, 0
  %_31.i = select i1 %24, i64 0, i64 1
  %25 = trunc nuw i64 %_31.i to i1
  br i1 %25, label %bb19.i, label %bb20.i

bb17.i:                                           ; preds = %bb16.i
  store i8 0, ptr %_27.i, align 1
  %26 = load i8, ptr %_27.i, align 1
  %27 = trunc nuw i8 %26 to i1
  %28 = getelementptr inbounds i8, ptr %_20.i, i64 1
  %29 = zext i1 %27 to i8
  store i8 %29, ptr %28, align 1
  store i8 1, ptr %_20.i, align 8
  br label %_ZN8zerocopy6layout9DstLayout34validate_cast_and_convert_metadata17hb1550c31ca7ee394E.exit

bb19.i:                                           ; preds = %bb18.i
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %trailing.i, ptr align 8 %size_info.i, i64 32, i1 false)
  %30 = getelementptr inbounds i8, ptr %trailing.i, i64 8
  %_6.i23.i = load i64, ptr %30, align 8
; call core::num::nonzero::NonZero<T>::get
  %_7.i.i24.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %_6.i23.i) #14
  %31 = call i64 @llvm.ctlz.i64(i64 %_7.i.i24.i, i1 false)
  %32 = trunc i64 %31 to i32
  store i32 %32, ptr %2, align 4
  %_0.i.i1.i.i = load i32, ptr %2, align 4
  %_5.i.i25.i = zext i32 %_0.i.i1.i.i to i64
  %_9.0.i.i26.i = sub i64 63, %_5.i.i25.i
  %_9.1.i.i27.i = icmp ult i64 63, %_5.i.i25.i
  br i1 %_9.1.i.i27.i, label %panic.i3.i.i, label %bb4.i2.i.i

bb4.i2.i.i:                                       ; preds = %bb19.i
  %_11.i.i28.i = icmp ult i64 %_9.0.i.i26.i, 64
  br i1 %_11.i.i28.i, label %bb5.i.i30.i, label %panic1.i.i29.i

panic.i3.i.i:                                     ; preds = %bb19.i
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h9d34257ac1862bebE(ptr align 8 @alloc_21ddd4c26dc1532b2647d440f1b43a1d) #15
  unreachable

bb5.i.i30.i:                                      ; preds = %bb4.i2.i.i
  %33 = and i64 %_9.0.i.i26.i, 63
  %align.i.i31.i = shl i64 1, %33
; call core::num::nonzero::NonZero<T>::new
  %34 = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3new17h61bb2493f7c27af8E"(i64 %align.i.i31.i) #14
  store i64 %34, ptr %_12.i.i20.i, align 8
  %35 = load i64, ptr %_12.i.i20.i, align 8
  %36 = icmp eq i64 %35, 0
  %_13.i.i32.i = select i1 %36, i64 0, i64 1
  %37 = trunc nuw i64 %_13.i.i32.i to i1
  br i1 %37, label %_ZN8zerocopy6layout21RoundingAlignAndPhase10components17he0fb8a99d944a89dE.exit.i.i, label %bb8.i.i33.i

panic1.i.i29.i:                                   ; preds = %bb4.i2.i.i
; call core::panicking::panic_const::panic_const_shl_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_shl_overflow17hbfdb61d170f9fa81E(ptr align 8 @alloc_8db9b9cdc5fa06515b130316754951f4) #15
  unreachable

bb8.i.i33.i:                                      ; preds = %bb5.i.i30.i
; call core::panicking::panic
  call void @_ZN4core9panicking5panic17h239804395728b21fE(ptr align 1 @alloc_a500d906b91607583596fa15e63c2ada, i64 40, ptr align 8 @alloc_62c4135799e1c4b88c454bf0806d12af) #15
  unreachable

_ZN8zerocopy6layout21RoundingAlignAndPhase10components17he0fb8a99d944a89dE.exit.i.i: ; preds = %bb5.i.i30.i
  %align2.i.i34.i = load i64, ptr %_12.i.i20.i, align 8
; call core::num::nonzero::NonZero<T>::get
  %_17.i.i35.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %_6.i23.i) #14
; call core::num::nonzero::NonZero<T>::get
  %_19.i.i36.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %align2.i.i34.i) #14
  %phase.i.i37.i = xor i64 %_17.i.i35.i, %_19.i.i36.i
  %38 = insertvalue { i64, i64 } poison, i64 %align2.i.i34.i, 0
  %39 = insertvalue { i64, i64 } %38, i64 %phase.i.i37.i, 1
  %40 = icmp eq i64 %phase.i.i37.i, 0
  br i1 %40, label %bb2.i45.i, label %bb3.i38.i

bb2.i45.i:                                        ; preds = %_ZN8zerocopy6layout21RoundingAlignAndPhase10components17he0fb8a99d944a89dE.exit.i.i
  store i64 0, ptr %rounded_phase.i.i, align 8
  br label %bb4.i39.i

bb3.i38.i:                                        ; preds = %_ZN8zerocopy6layout21RoundingAlignAndPhase10components17he0fb8a99d944a89dE.exit.i.i
; call core::num::nonzero::NonZero<T>::get
  %41 = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %align2.i.i34.i) #14
  store i64 %41, ptr %rounded_phase.i.i, align 8
  br label %bb4.i39.i

bb4.i39.i:                                        ; preds = %bb3.i38.i, %bb2.i45.i
  %42 = getelementptr inbounds i8, ptr %trailing.i, i64 24
  %_9.i.i = load i64, ptr %42, align 8
  %_10.i.i = load i64, ptr %rounded_phase.i.i, align 8
; call core::num::<impl usize>::checked_add
  %43 = call { i64, i64 } @"_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_add17h07a6aef785bb2367E"(i64 %_9.i.i, i64 %_10.i.i) #14
  %44 = extractvalue { i64, i64 } %43, 0
  %45 = extractvalue { i64, i64 } %43, 1
  store i64 %44, ptr %_8.i21.i, align 8
  %46 = getelementptr inbounds i8, ptr %_8.i21.i, i64 8
  store i64 %45, ptr %46, align 8
  %_11.i.i = load i64, ptr %_8.i21.i, align 8
  %47 = getelementptr inbounds i8, ptr %_8.i21.i, i64 8
  %48 = load i64, ptr %47, align 8
  %49 = trunc nuw i64 %_11.i.i to i1
  br i1 %49, label %bb8.i.i, label %bb7.i.i

bb8.i.i:                                          ; preds = %bb4.i39.i
  %50 = getelementptr inbounds i8, ptr %_8.i21.i, i64 8
  %minimum_size.i.i = load i64, ptr %50, align 8
; call core::num::<impl usize>::checked_sub
  %51 = call { i64, i64 } @"_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_sub17hdabf32b0dd7c6f9bE"(i64 %_22.i, i64 %minimum_size.i.i) #14
  %52 = extractvalue { i64, i64 } %51, 0
  %53 = extractvalue { i64, i64 } %51, 1
  store i64 %52, ptr %_13.i.i, align 8
  %54 = getelementptr inbounds i8, ptr %_13.i.i, i64 8
  store i64 %53, ptr %54, align 8
  %_14.i.i = load i64, ptr %_13.i.i, align 8
  %55 = getelementptr inbounds i8, ptr %_13.i.i, i64 8
  %56 = load i64, ptr %55, align 8
  %57 = trunc nuw i64 %_14.i.i to i1
  br i1 %57, label %bb11.i.i, label %bb10.i.i

bb7.i.i:                                          ; preds = %bb4.i39.i
  store i64 0, ptr %_0.i22.i, align 8
  br label %"_ZN8zerocopy6layout28TrailingSliceLayout$LT$E$GT$18max_trailing_bytes17hf55180bbf3e35a37E.exit.i"

bb11.i.i:                                         ; preds = %bb8.i.i
  %58 = getelementptr inbounds i8, ptr %_13.i.i, i64 8
  %extra_bytes.i.i = load i64, ptr %58, align 8
; call core::num::nonzero::NonZero<T>::get
  %align1.i.i.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %align2.i.i34.i) #14
  %59 = call i64 @llvm.ctpop.i64(i64 %align1.i.i.i)
  %60 = trunc i64 %59 to i32
  store i32 %60, ptr %3, align 4
  %_2.i.i.i.i = load i32, ptr %3, align 4
  %_0.i.i.i40.i = icmp eq i32 %_2.i.i.i.i, 1
  br i1 %_0.i.i.i40.i, label %bb4.i.i41.i, label %bb3.i.i.i

bb3.i.i.i:                                        ; preds = %bb11.i.i
; call core::panicking::panic
  call void @_ZN4core9panicking5panic17h239804395728b21fE(ptr align 1 @alloc_289f879f0c7d96128297d6dd5a3ad59d, i64 41, ptr align 8 @alloc_c6f1a83cf202f671c45a40b695eb8f70) #15
  unreachable

bb4.i.i41.i:                                      ; preds = %bb11.i.i
  %_8.0.i.i.i = sub i64 %align1.i.i.i, 1
  %_8.1.i.i.i = icmp ult i64 %align1.i.i.i, 1
  br i1 %_8.1.i.i.i, label %panic.i.i44.i, label %_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit.i.i

panic.i.i44.i:                                    ; preds = %bb4.i.i41.i
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h9d34257ac1862bebE(ptr align 8 @alloc_e7b7d000cf090c3222f3db2028bfac60) #15
  unreachable

_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit.i.i: ; preds = %bb4.i.i41.i
  %mask.i.i.i = xor i64 %_8.0.i.i.i, -1
  %_0.i.i42.i = and i64 %extra_bytes.i.i, %mask.i.i.i
  %_18.i.i = load i64, ptr %rounded_phase.i.i, align 8
  %_19.0.i.i = sub i64 %_18.i.i, %phase.i.i37.i
  %_19.1.i.i = icmp ult i64 %_18.i.i, %phase.i.i37.i
  br i1 %_19.1.i.i, label %panic.i43.i, label %bb13.i.i

bb10.i.i:                                         ; preds = %bb8.i.i
  store i64 0, ptr %_0.i22.i, align 8
  br label %"_ZN8zerocopy6layout28TrailingSliceLayout$LT$E$GT$18max_trailing_bytes17hf55180bbf3e35a37E.exit.i"

bb13.i.i:                                         ; preds = %_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit.i.i
  %trailing_bytes.i.i = or i64 %_0.i.i42.i, %_19.0.i.i
  %61 = getelementptr inbounds i8, ptr %_0.i22.i, i64 8
  store i64 %trailing_bytes.i.i, ptr %61, align 8
  store i64 1, ptr %_0.i22.i, align 8
  br label %"_ZN8zerocopy6layout28TrailingSliceLayout$LT$E$GT$18max_trailing_bytes17hf55180bbf3e35a37E.exit.i"

panic.i43.i:                                      ; preds = %_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit.i.i
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h9d34257ac1862bebE(ptr align 8 @alloc_2a1e08f3dea28730048a53142e6e2d0d) #15
  unreachable

"_ZN8zerocopy6layout28TrailingSliceLayout$LT$E$GT$18max_trailing_bytes17hf55180bbf3e35a37E.exit.i": ; preds = %bb13.i.i, %bb10.i.i, %bb7.i.i
  %62 = load i64, ptr %_0.i22.i, align 8
  %63 = getelementptr inbounds i8, ptr %_0.i22.i, i64 8
  %64 = load i64, ptr %63, align 8
  %65 = insertvalue { i64, i64 } poison, i64 %62, 0
  %66 = insertvalue { i64, i64 } %65, i64 %64, 1
  store i64 %62, ptr %_36.i, align 8
  %67 = getelementptr inbounds i8, ptr %_36.i, i64 8
  store i64 %64, ptr %67, align 8
  %_38.i = load i64, ptr %_36.i, align 8
  %68 = getelementptr inbounds i8, ptr %_36.i, i64 8
  %69 = load i64, ptr %68, align 8
  %70 = trunc nuw i64 %_38.i to i1
  br i1 %70, label %bb25.i, label %bb24.i

bb20.i:                                           ; preds = %bb18.i
  %71 = getelementptr inbounds i8, ptr %size_info.i, i64 8
  %size.i15 = load i64, ptr %71, align 8
  %_33.i = icmp ugt i64 %size.i15, %_22.i
  br i1 %_33.i, label %bb21.i, label %bb22.i

bb22.i:                                           ; preds = %bb20.i
  store i64 0, ptr %_30.i, align 8
  %72 = getelementptr inbounds i8, ptr %_30.i, i64 8
  store i64 %size.i15, ptr %72, align 8
  br label %bb35.i

bb21.i:                                           ; preds = %bb20.i
  store i8 1, ptr %_34.i, align 1
  %73 = load i8, ptr %_34.i, align 1
  %74 = trunc nuw i8 %73 to i1
  %75 = getelementptr inbounds i8, ptr %_20.i, i64 1
  %76 = zext i1 %74 to i8
  store i8 %76, ptr %75, align 1
  store i8 1, ptr %_20.i, align 8
  br label %_ZN8zerocopy6layout9DstLayout34validate_cast_and_convert_metadata17hb1550c31ca7ee394E.exit

bb35.i:                                           ; preds = %bb34.i, %bb22.i
  %elems.i = load i64, ptr %_30.i, align 8
  %77 = getelementptr inbounds i8, ptr %_30.i, i64 8
  %self_bytes.i = load i64, ptr %77, align 8
  %e6.i = icmp ule i64 %self_bytes.i, %_22.i
  br i1 %e6.i, label %bb37.i, label %bb36.i

bb25.i:                                           ; preds = %"_ZN8zerocopy6layout28TrailingSliceLayout$LT$E$GT$18max_trailing_bytes17hf55180bbf3e35a37E.exit.i"
  %78 = getelementptr inbounds i8, ptr %_36.i, i64 8
  %max_slice_bytes.i = load i64, ptr %78, align 8
  %_43.i = load i64, ptr %trailing.i, align 8
; call core::num::nonzero::NonZero<T>::get
  %_4.i.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %_43.i) #14
  %_5.i.i = icmp eq i64 %_4.i.i, 0
  br i1 %_5.i.i, label %panic.i19.i, label %bb2.i.i

bb2.i.i:                                          ; preds = %bb25.i
  %elems.i.i = udiv i64 %max_slice_bytes.i, %_4.i.i
; call core::num::nonzero::NonZero<T>::get
  %_7.i.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %_43.i) #14
; call core::num::<impl usize>::checked_mul
  %79 = call { i64, i64 } @"_ZN4core3num23_$LT$impl$u20$usize$GT$11checked_mul17h15ddeb83d8fdb7cfE"(i64 %elems.i.i, i64 %_7.i.i) #14
  %80 = extractvalue { i64, i64 } %79, 0
  %81 = extractvalue { i64, i64 } %79, 1
  store i64 %80, ptr %_6.i.i, align 8
  %82 = getelementptr inbounds i8, ptr %_6.i.i, i64 8
  store i64 %81, ptr %82, align 8
  %_8.i.i = load i64, ptr %_6.i.i, align 8
  %83 = getelementptr inbounds i8, ptr %_6.i.i, i64 8
  %84 = load i64, ptr %83, align 8
  %85 = trunc nuw i64 %_8.i.i to i1
  br i1 %85, label %_ZN8zerocopy6layout19max_elems_for_bytes17hc4adf6a4738e6baeE.exit.i, label %bb6.i.i

panic.i19.i:                                      ; preds = %bb25.i
; call core::panicking::panic_const::panic_const_div_by_zero
  call void @_ZN4core9panicking11panic_const23panic_const_div_by_zero17hd1b66acfd73a6e98E(ptr align 8 @alloc_c7fb12713fc7ee73392f756a24cec321) #15
  unreachable

bb6.i.i:                                          ; preds = %bb2.i.i
; call core::panicking::panic
  call void @_ZN4core9panicking5panic17h239804395728b21fE(ptr align 1 @alloc_a500d906b91607583596fa15e63c2ada, i64 40, ptr align 8 @alloc_46a03d2f1091ab2605bc31f4a926f118) #15
  unreachable

_ZN8zerocopy6layout19max_elems_for_bytes17hc4adf6a4738e6baeE.exit.i: ; preds = %bb2.i.i
  %86 = getelementptr inbounds i8, ptr %_6.i.i, i64 8
  %used.i.i = load i64, ptr %86, align 8
  %87 = insertvalue { i64, i64 } poison, i64 %elems.i.i, 0
  %88 = insertvalue { i64, i64 } %87, i64 %used.i.i, 1
  %89 = getelementptr inbounds i8, ptr %trailing.i, i64 8
  %_45.i = load i64, ptr %89, align 8
; call core::num::nonzero::NonZero<T>::get
  %_7.i.i.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %_45.i) #14
  %90 = call i64 @llvm.ctlz.i64(i64 %_7.i.i.i, i1 false)
  %91 = trunc i64 %90 to i32
  store i32 %91, ptr %4, align 4
  %_0.i.i.i.i = load i32, ptr %4, align 4
  %_5.i.i.i = zext i32 %_0.i.i.i.i to i64
  %_9.0.i.i.i = sub i64 63, %_5.i.i.i
  %_9.1.i.i.i = icmp ult i64 63, %_5.i.i.i
  br i1 %_9.1.i.i.i, label %panic.i.i.i, label %bb4.i.i.i

bb4.i.i.i:                                        ; preds = %_ZN8zerocopy6layout19max_elems_for_bytes17hc4adf6a4738e6baeE.exit.i
  %_11.i.i.i = icmp ult i64 %_9.0.i.i.i, 64
  br i1 %_11.i.i.i, label %bb5.i.i.i, label %panic1.i.i.i

panic.i.i.i:                                      ; preds = %_ZN8zerocopy6layout19max_elems_for_bytes17hc4adf6a4738e6baeE.exit.i
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h9d34257ac1862bebE(ptr align 8 @alloc_21ddd4c26dc1532b2647d440f1b43a1d) #15
  unreachable

bb5.i.i.i:                                        ; preds = %bb4.i.i.i
  %92 = and i64 %_9.0.i.i.i, 63
  %align.i.i.i = shl i64 1, %92
; call core::num::nonzero::NonZero<T>::new
  %93 = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3new17h61bb2493f7c27af8E"(i64 %align.i.i.i) #14
  store i64 %93, ptr %_12.i.i.i, align 8
  %94 = load i64, ptr %_12.i.i.i, align 8
  %95 = icmp eq i64 %94, 0
  %_13.i.i.i = select i1 %95, i64 0, i64 1
  %96 = trunc nuw i64 %_13.i.i.i to i1
  br i1 %96, label %_ZN8zerocopy6layout21RoundingAlignAndPhase5align17h1795371afa4bdae6E.exit.i, label %bb8.i.i.i

panic1.i.i.i:                                     ; preds = %bb4.i.i.i
; call core::panicking::panic_const::panic_const_shl_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_shl_overflow17hbfdb61d170f9fa81E(ptr align 8 @alloc_8db9b9cdc5fa06515b130316754951f4) #15
  unreachable

bb8.i.i.i:                                        ; preds = %bb5.i.i.i
; call core::panicking::panic
  call void @_ZN4core9panicking5panic17h239804395728b21fE(ptr align 1 @alloc_a500d906b91607583596fa15e63c2ada, i64 40, ptr align 8 @alloc_62c4135799e1c4b88c454bf0806d12af) #15
  unreachable

_ZN8zerocopy6layout21RoundingAlignAndPhase5align17h1795371afa4bdae6E.exit.i: ; preds = %bb5.i.i.i
  %align2.i.i.i = load i64, ptr %_12.i.i.i, align 8
; call core::num::nonzero::NonZero<T>::get
  %_17.i.i.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %_45.i) #14
; call core::num::nonzero::NonZero<T>::get
  %_19.i.i.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %align2.i.i.i) #14
  %phase.i.i.i = xor i64 %_17.i.i.i, %_19.i.i.i
  %97 = insertvalue { i64, i64 } poison, i64 %align2.i.i.i, 0
  %98 = insertvalue { i64, i64 } %97, i64 %phase.i.i.i, 1
  %_48.i = load i64, ptr %trailing.i, align 8
; call core::num::nonzero::NonZero<T>::get
  %_47.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %_48.i) #14
  %_49.i = icmp eq i64 %_47.i, 0
  br i1 %_49.i, label %panic2.i, label %bb29.i

bb24.i:                                           ; preds = %"_ZN8zerocopy6layout28TrailingSliceLayout$LT$E$GT$18max_trailing_bytes17hf55180bbf3e35a37E.exit.i"
  store i8 1, ptr %_40.i, align 1
  %99 = load i8, ptr %_40.i, align 1
  %100 = trunc nuw i8 %99 to i1
  %101 = getelementptr inbounds i8, ptr %_20.i, i64 1
  %102 = zext i1 %100 to i8
  store i8 %102, ptr %101, align 1
  store i8 1, ptr %_20.i, align 8
  br label %_ZN8zerocopy6layout9DstLayout34validate_cast_and_convert_metadata17hb1550c31ca7ee394E.exit

bb29.i:                                           ; preds = %_ZN8zerocopy6layout21RoundingAlignAndPhase5align17h1795371afa4bdae6E.exit.i
  %unused_bytes.i = urem i64 %max_slice_bytes.i, %_47.i
; call core::num::nonzero::NonZero<T>::get
  %align1.i8.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %align2.i.i.i) #14
  %103 = call i64 @llvm.ctpop.i64(i64 %align1.i8.i)
  %104 = trunc i64 %103 to i32
  store i32 %104, ptr %5, align 4
  %_2.i.i9.i = load i32, ptr %5, align 4
  %_0.i.i10.i = icmp eq i32 %_2.i.i9.i, 1
  br i1 %_0.i.i10.i, label %bb4.i12.i, label %bb3.i11.i

bb3.i11.i:                                        ; preds = %bb29.i
; call core::panicking::panic
  call void @_ZN4core9panicking5panic17h239804395728b21fE(ptr align 1 @alloc_289f879f0c7d96128297d6dd5a3ad59d, i64 41, ptr align 8 @alloc_c6f1a83cf202f671c45a40b695eb8f70) #15
  unreachable

bb4.i12.i:                                        ; preds = %bb29.i
  %_8.0.i13.i = sub i64 %align1.i8.i, 1
  %_8.1.i14.i = icmp ult i64 %align1.i8.i, 1
  br i1 %_8.1.i14.i, label %panic.i17.i, label %_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit18.i

panic.i17.i:                                      ; preds = %bb4.i12.i
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h9d34257ac1862bebE(ptr align 8 @alloc_e7b7d000cf090c3222f3db2028bfac60) #15
  unreachable

_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit18.i: ; preds = %bb4.i12.i
  %mask.i15.i = xor i64 %_8.0.i13.i, -1
  %_0.i16.i = and i64 %unused_bytes.i, %mask.i15.i
  %105 = getelementptr inbounds i8, ptr %trailing.i, i64 24
  %_53.i = load i64, ptr %105, align 8
  %_54.0.i = sub i64 %_22.i, %_53.i
  %_54.1.i = icmp ult i64 %_22.i, %_53.i
  br i1 %_54.1.i, label %panic3.i, label %bb31.i

panic2.i:                                         ; preds = %_ZN8zerocopy6layout21RoundingAlignAndPhase5align17h1795371afa4bdae6E.exit.i
; call core::panicking::panic_const::panic_const_rem_by_zero
  call void @_ZN4core9panicking11panic_const23panic_const_rem_by_zero17hb2eecb9bde6b0e42E(ptr align 8 @alloc_9b1bb719df70d519086fef1cda697ad0) #15
  unreachable

bb31.i:                                           ; preds = %_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit18.i
; call core::num::nonzero::NonZero<T>::get
  %align1.i.i = call i64 @"_ZN4core3num7nonzero16NonZero$LT$T$GT$3get17hed7ab60c7ab0e952E"(i64 %align2.i.i.i) #14
  %106 = call i64 @llvm.ctpop.i64(i64 %align1.i.i)
  %107 = trunc i64 %106 to i32
  store i32 %107, ptr %6, align 4
  %_2.i.i.i = load i32, ptr %6, align 4
  %_0.i.i.i = icmp eq i32 %_2.i.i.i, 1
  br i1 %_0.i.i.i, label %bb4.i.i, label %bb3.i.i

bb3.i.i:                                          ; preds = %bb31.i
; call core::panicking::panic
  call void @_ZN4core9panicking5panic17h239804395728b21fE(ptr align 1 @alloc_289f879f0c7d96128297d6dd5a3ad59d, i64 41, ptr align 8 @alloc_c6f1a83cf202f671c45a40b695eb8f70) #15
  unreachable

bb4.i.i:                                          ; preds = %bb31.i
  %_8.0.i.i = sub i64 %align1.i.i, 1
  %_8.1.i.i = icmp ult i64 %align1.i.i, 1
  br i1 %_8.1.i.i, label %panic.i.i, label %_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit.i

panic.i.i:                                        ; preds = %bb4.i.i
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h9d34257ac1862bebE(ptr align 8 @alloc_e7b7d000cf090c3222f3db2028bfac60) #15
  unreachable

_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit.i: ; preds = %bb4.i.i
  %mask.i.i = xor i64 %_8.0.i.i, -1
  %_0.i.i16 = and i64 %_54.0.i, %mask.i.i
  %108 = getelementptr inbounds i8, ptr %trailing.i, i64 24
  %_56.i = load i64, ptr %108, align 8
  %_58.0.i = sub i64 %_0.i.i16, %_0.i16.i
  %_58.1.i = icmp ult i64 %_0.i.i16, %_0.i16.i
  br i1 %_58.1.i, label %panic4.i, label %bb33.i

panic3.i:                                         ; preds = %_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit18.i
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h9d34257ac1862bebE(ptr align 8 @alloc_d570cd8297926e8621ddfb6b2b8e2ad9) #15
  unreachable

bb33.i:                                           ; preds = %_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit.i
  %109 = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %_56.i, i64 %_58.0.i)
  %_59.0.i = extractvalue { i64, i1 } %109, 0
  %_59.1.i = extractvalue { i64, i1 } %109, 1
  br i1 %_59.1.i, label %panic5.i, label %bb34.i

panic4.i:                                         ; preds = %_ZN8zerocopy4util40round_down_to_next_multiple_of_alignment17h4767bbb0fa1edfe9E.exit.i
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h9d34257ac1862bebE(ptr align 8 @alloc_4cab74535d2ec5c8285921dd4499d52e) #15
  unreachable

bb34.i:                                           ; preds = %bb33.i
  store i64 %elems.i.i, ptr %_30.i, align 8
  %110 = getelementptr inbounds i8, ptr %_30.i, i64 8
  store i64 %_59.0.i, ptr %110, align 8
  br label %bb35.i

panic5.i:                                         ; preds = %bb33.i
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_add_overflow17h371a9588e01a5f2aE(ptr align 8 @alloc_69f87fd79a0e8bc360cd9fab3ffbc279) #15
  unreachable

bb36.i:                                           ; preds = %bb35.i
; call core::panicking::panic
  call void @_ZN4core9panicking5panic17h239804395728b21fE(ptr align 1 @alloc_a6bf1f98997d43151aae6dc674dd1f22, i64 112, ptr align 8 @alloc_ba9ffb706a6ca16eea68370d5abffdfd) #15
  unreachable

bb37.i:                                           ; preds = %bb35.i
  %_63.i = zext i1 %cast_type to i64
  br i1 %cast_type, label %bb38.i, label %bb39.i

bb38.i:                                           ; preds = %bb37.i
  %_64.0.i = sub i64 %_22.i, %self_bytes.i
  %_64.1.i = icmp ult i64 %_22.i, %self_bytes.i
  br i1 %_64.1.i, label %panic7.i, label %bb40.i

bb39.i:                                           ; preds = %bb37.i
  store i64 %self_bytes.i, ptr %split_at.i2, align 8
  br label %bb41.i

bb41.i:                                           ; preds = %bb40.i, %bb39.i
  %_66.i = load i64, ptr %split_at.i2, align 8
  %111 = getelementptr inbounds i8, ptr %_20.i, i64 8
  store i64 %elems.i, ptr %111, align 8
  %112 = getelementptr inbounds i8, ptr %111, i64 8
  store i64 %_66.i, ptr %112, align 8
  store i8 0, ptr %_20.i, align 8
  br label %_ZN8zerocopy6layout9DstLayout34validate_cast_and_convert_metadata17hb1550c31ca7ee394E.exit

bb40.i:                                           ; preds = %bb38.i
  store i64 %_64.0.i, ptr %split_at.i2, align 8
  br label %bb41.i

panic7.i:                                         ; preds = %bb38.i
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h9d34257ac1862bebE(ptr align 8 @alloc_c9ffeeb1c1cfce728d4707955a20fda1) #15
  unreachable

_ZN8zerocopy6layout9DstLayout34validate_cast_and_convert_metadata17hb1550c31ca7ee394E.exit: ; preds = %bb17.i, %bb21.i, %bb24.i, %bb41.i
; call <core::result::Result<T,E> as core::ops::try_trait::Try>::branch
  call void @"_ZN79_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17h2d7e48b51d222444E"(ptr sret([24 x i8]) align 8 %_19.i, ptr align 8 %_20.i) #14
  %113 = load i8, ptr %_19.i, align 8
  %114 = trunc nuw i8 %113 to i1
  %_24.i = zext i1 %114 to i64
  br i1 %114, label %bb15.i, label %bb14.i

bb6.i:                                            ; preds = %bb2.i
  store i8 1, ptr %_9.i, align 1
  %115 = load i8, ptr %_9.i, align 1
  %116 = trunc nuw i8 %115 to i1
  %117 = getelementptr inbounds i8, ptr %maybe_metadata, i64 1
  %118 = zext i1 %116 to i8
  store i8 %118, ptr %117, align 1
  store i8 1, ptr %maybe_metadata, align 8
  br label %"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$34validate_cast_and_convert_metadata17h7b6a805136b7faacE.exit"

bb5.i:                                            ; preds = %bb2.i
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %7, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.1, i64 48, i1 false)
; call <() as zerocopy::PointerMetadata>::size_for_metadata
  %119 = call { i64, i64 } @"_ZN54_$LT$$LP$$RP$$u20$as$u20$zerocopy..PointerMetadata$GT$17size_for_metadata17hfbf01e521c20d141E"(ptr align 8 %7) #14
  %_0.0.i.i = extractvalue { i64, i64 } %119, 0
  %_0.1.i.i = extractvalue { i64, i64 } %119, 1
  %120 = extractvalue { i64, i64 } %119, 0
  %121 = extractvalue { i64, i64 } %119, 1
  store i64 %120, ptr %_10.i, align 8
  %122 = getelementptr inbounds i8, ptr %_10.i, i64 8
  store i64 %121, ptr %122, align 8
  %_11.i = load i64, ptr %_10.i, align 8
  %123 = getelementptr inbounds i8, ptr %_10.i, i64 8
  %124 = load i64, ptr %123, align 8
  %125 = trunc nuw i64 %_11.i to i1
  br i1 %125, label %bb9.i, label %bb8.i

bb9.i:                                            ; preds = %bb5.i
  %126 = getelementptr inbounds i8, ptr %_10.i, i64 8
  %size.i = load i64, ptr %126, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_15.i, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.1, i64 48, i1 false)
  %_14.i = load i64, ptr %_15.i, align 8
  %127 = getelementptr inbounds i8, ptr %_16.i, i64 8
  store i64 %size.i, ptr %127, align 8
  store i64 0, ptr %_16.i, align 8
  store i64 %_14.i, ptr %layout.i, align 8
  %128 = getelementptr inbounds i8, ptr %layout.i, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %128, ptr align 8 %_16.i, i64 32, i1 false)
  %129 = getelementptr inbounds i8, ptr %layout.i, i64 40
  store i8 0, ptr %129, align 8
  br label %bb10.i

bb8.i:                                            ; preds = %bb5.i
  store i8 1, ptr %_13.i, align 1
  %130 = load i8, ptr %_13.i, align 1
  %131 = trunc nuw i8 %130 to i1
  %132 = getelementptr inbounds i8, ptr %maybe_metadata, i64 1
  %133 = zext i1 %131 to i8
  store i8 %133, ptr %132, align 1
  store i8 1, ptr %maybe_metadata, align 8
  br label %"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$34validate_cast_and_convert_metadata17h7b6a805136b7faacE.exit"

bb15.i:                                           ; preds = %_ZN8zerocopy6layout9DstLayout34validate_cast_and_convert_metadata17hb1550c31ca7ee394E.exit
  %134 = getelementptr inbounds i8, ptr %_19.i, i64 1
  %135 = load i8, ptr %134, align 1
  %residual.i = trunc nuw i8 %135 to i1
; call <core::result::Result<T,F> as core::ops::try_trait::FromResidual<core::result::Result<core::convert::Infallible,E>>>::from_residual
  call void @"_ZN153_$LT$core..result..Result$LT$T$C$F$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..result..Result$LT$core..convert..Infallible$C$E$GT$$GT$$GT$13from_residual17haa588d2d34a518fdE"(ptr sret([16 x i8]) align 8 %maybe_metadata, i1 zeroext %residual.i, ptr align 8 @alloc_070512b75885343f240d4e39148a647a) #14
  br label %"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$34validate_cast_and_convert_metadata17h7b6a805136b7faacE.exit"

bb14.i:                                           ; preds = %_ZN8zerocopy6layout9DstLayout34validate_cast_and_convert_metadata17hb1550c31ca7ee394E.exit
  %136 = getelementptr inbounds i8, ptr %_19.i, i64 8
  %val.0.i = load i64, ptr %136, align 8
  %137 = getelementptr inbounds i8, ptr %136, i64 8
  %val.1.i = load i64, ptr %137, align 8
; call <() as zerocopy::PointerMetadata>::from_elem_count
  call void @"_ZN54_$LT$$LP$$RP$$u20$as$u20$zerocopy..PointerMetadata$GT$15from_elem_count17h94cd1d1a56a5f00dE"(i64 %val.0.i) #14
; call core::option::Option<T>::unwrap_or
  call void @"_ZN4core6option15Option$LT$T$GT$9unwrap_or17h9f918ae027ea2a49E"(i1 zeroext %meta) #14
; call zerocopy::util::len_of::MetadataOf<T>::new_unchecked
  call void @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$13new_unchecked17h0ae4cc51ed972104E"() #14
; call zerocopy::util::len_of::MetadataOf<T>::new_unchecked
  %split_at.i = call i64 @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$13new_unchecked17hbf283257ae23f131E"(i64 %val.1.i) #14
  %138 = getelementptr inbounds i8, ptr %maybe_metadata, i64 8
  store i64 %split_at.i, ptr %138, align 8
  store i8 0, ptr %maybe_metadata, align 8
  br label %"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$34validate_cast_and_convert_metadata17h7b6a805136b7faacE.exit"

"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$34validate_cast_and_convert_metadata17h7b6a805136b7faacE.exit": ; preds = %bb6.i, %bb8.i, %bb15.i, %bb14.i
  %139 = load i8, ptr %maybe_metadata, align 8
  %140 = trunc nuw i8 %139 to i1
  %_14 = zext i1 %140 to i64
  %141 = trunc nuw i64 %_14 to i1
  br i1 %141, label %bb6, label %bb9

bb6:                                              ; preds = %"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$34validate_cast_and_convert_metadata17h7b6a805136b7faacE.exit"
  %142 = getelementptr inbounds i8, ptr %maybe_metadata, i64 1
  %143 = load i8, ptr %142, align 1
  %144 = trunc nuw i8 %143 to i1
  %_13 = zext i1 %144 to i64
  %145 = trunc nuw i64 %_13 to i1
  br i1 %145, label %bb7, label %bb8

bb9:                                              ; preds = %"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$34validate_cast_and_convert_metadata17h7b6a805136b7faacE.exit"
  %146 = getelementptr inbounds i8, ptr %maybe_metadata, i64 8
  %split_at = load i64, ptr %146, align 8
  %_26.0 = load ptr, ptr %self, align 8
  %147 = getelementptr inbounds i8, ptr %self, i64 8
  %_26.1 = load i64, ptr %147, align 8
; call zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::split_at_unchecked
  call void @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$18split_at_unchecked17heee872bc71fa1092E"(ptr sret([32 x i8]) align 8 %_25, ptr %_26.0, i64 %_26.1, i64 %split_at) #14
  %l_slice.0 = load ptr, ptr %_25, align 8
  %148 = getelementptr inbounds i8, ptr %_25, i64 8
  %l_slice.1 = load i64, ptr %148, align 8
  %149 = getelementptr inbounds i8, ptr %_25, i64 16
  %r_slice.0 = load ptr, ptr %149, align 8
  %150 = getelementptr inbounds i8, ptr %149, i64 8
  %r_slice.1 = load i64, ptr %150, align 8
  %_30 = zext i1 %cast_type to i64
  %151 = trunc nuw i64 %_30 to i1
  br i1 %151, label %bb13, label %bb14

bb13:                                             ; preds = %bb9
  store ptr %r_slice.0, ptr %_29, align 8
  %152 = getelementptr inbounds i8, ptr %_29, i64 8
  store i64 %r_slice.1, ptr %152, align 8
  %153 = getelementptr inbounds i8, ptr %_29, i64 16
  store ptr %l_slice.0, ptr %153, align 8
  %154 = getelementptr inbounds i8, ptr %153, i64 8
  store i64 %l_slice.1, ptr %154, align 8
  br label %bb15

bb14:                                             ; preds = %bb9
  store ptr %l_slice.0, ptr %_29, align 8
  %155 = getelementptr inbounds i8, ptr %_29, i64 8
  store i64 %l_slice.1, ptr %155, align 8
  %156 = getelementptr inbounds i8, ptr %_29, i64 16
  store ptr %r_slice.0, ptr %156, align 8
  %157 = getelementptr inbounds i8, ptr %156, i64 8
  store i64 %r_slice.1, ptr %157, align 8
  br label %bb15

bb15:                                             ; preds = %bb13, %bb14
  %158 = load ptr, ptr %_29, align 8
  %159 = getelementptr inbounds i8, ptr %_29, i64 8
  %160 = load i64, ptr %159, align 8
  store ptr %158, ptr %target, align 8
  %161 = getelementptr inbounds i8, ptr %target, i64 8
  store i64 %160, ptr %161, align 8
  %162 = getelementptr inbounds i8, ptr %_29, i64 16
  %remainder.0 = load ptr, ptr %162, align 8
  %163 = getelementptr inbounds i8, ptr %162, i64 8
  %remainder.1 = load i64, ptr %163, align 8
  %_0.0.i = load ptr, ptr %target, align 8
  %164 = getelementptr inbounds i8, ptr %target, i64 8
  %_0.1.i = load i64, ptr %164, align 8
  %165 = insertvalue { ptr, i64 } poison, ptr %_0.0.i, 0
  %166 = insertvalue { ptr, i64 } %165, i64 %_0.1.i, 1
  %_32.0 = extractvalue { ptr, i64 } %166, 0
  %_32.1 = extractvalue { ptr, i64 } %166, 1
; call core::ptr::non_null::NonNull<T>::cast
  %base = call ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17h110a24a51af34c8dE"(ptr %_32.0, i64 %_32.1) #14
; call zerocopy::util::len_of::MetadataOf<T>::get
  call void @"_ZN8zerocopy4util6len_of19MetadataOf$LT$T$GT$3get17h0182bf0d597d886dE"(ptr align 1 %elems) #14
; call core::ptr::non_null::NonNull<T>::cast
  %_0.i = call ptr @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17h718584af148cdac1E"(ptr %base) #14
  store ptr %_0.i, ptr %_37, align 8
  %167 = getelementptr inbounds i8, ptr %_37, i64 8
  store ptr %remainder.0, ptr %167, align 8
  %168 = getelementptr inbounds i8, ptr %167, i64 8
  store i64 %remainder.1, ptr %168, align 8
  %169 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %169, ptr align 8 %_37, i64 24, i1 false)
  store i64 0, ptr %_0, align 8
  br label %bb21

bb21:                                             ; preds = %bb7, %bb8, %bb15
  ret void

bb7:                                              ; preds = %bb6
  %_22.0 = load ptr, ptr %self, align 8
  %170 = getelementptr inbounds i8, ptr %self, i64 8
  %_22.1 = load i64, ptr %170, align 8
; call zerocopy::error::SizeError<Src,Dst>::new
  %171 = call { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17hdb2b84825caa4500E"(ptr %_22.0, i64 %_22.1) #14
  %_21.0 = extractvalue { ptr, i64 } %171, 0
  %_21.1 = extractvalue { ptr, i64 } %171, 1
  %172 = getelementptr inbounds i8, ptr %_20, i64 8
  store ptr %_21.0, ptr %172, align 8
  %173 = getelementptr inbounds i8, ptr %172, i64 8
  store i64 %_21.1, ptr %173, align 8
  store i64 1, ptr %_20, align 8
  %174 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %174, ptr align 8 %_20, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb21

bb8:                                              ; preds = %bb6
  %_18.0 = load ptr, ptr %self, align 8
  %175 = getelementptr inbounds i8, ptr %self, i64 8
  %_18.1 = load i64, ptr %175, align 8
; call zerocopy::error::AlignmentError<Src,Dst>::new_unchecked
  %176 = call { ptr, i64 } @"_ZN8zerocopy5error31AlignmentError$LT$Src$C$Dst$GT$13new_unchecked17hdec382a38f918049E"(ptr %_18.0, i64 %_18.1) #14
  %err.0 = extractvalue { ptr, i64 } %176, 0
  %err.1 = extractvalue { ptr, i64 } %176, 1
  %177 = getelementptr inbounds i8, ptr %_19, i64 8
  store ptr %err.0, ptr %177, align 8
  %178 = getelementptr inbounds i8, ptr %177, i64 8
  store i64 %err.1, ptr %178, align 8
  store i64 0, ptr %_19, align 8
  %179 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %179, ptr align 8 %_19, i64 24, i1 false)
  store i64 1, ptr %_0, align 8
  br label %bb21

bb5:                                              ; No predecessors!
  unreachable
}

; zerocopy::FromBytes::ref_from_bytes
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN8zerocopy9FromBytes14ref_from_bytes17h3fe09cf7564e14e4E(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %source.0, i64 %source.1) unnamed_addr #0 {
start:
  %_16.i.i = alloca [24 x i8], align 8
  %val.i.i = alloca [24 x i8], align 8
  %residual.i.i = alloca [24 x i8], align 8
  %_8.i.i = alloca [32 x i8], align 8
  %_7.i.i = alloca [32 x i8], align 8
  %_6.i.i = alloca [32 x i8], align 8
  %self.i.i1 = alloca [16 x i8], align 8
  %err.i = alloca [24 x i8], align 8
  %_11.i = alloca [1 x i8], align 1
  %remainder.i = alloca [16 x i8], align 8
  %_4.i = alloca [1 x i8], align 1
  %_3.i = alloca [32 x i8], align 8
  %_1.i = alloca [8 x i8], align 8
  %_5.i.i = alloca [16 x i8], align 8
  %self.i.i = alloca [16 x i8], align 8
  %meta.i = alloca [1 x i8], align 1
  %_11 = alloca [24 x i8], align 8
  %err = alloca [24 x i8], align 8
  %_5 = alloca [1 x i8], align 1
  %_3 = alloca [24 x i8], align 8
  br label %bb2

bb2:                                              ; preds = %start
; call zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<T>>::from_ref
  %0 = call { ptr, i64 } @"_ZN8zerocopy7pointer5inner67_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$T$GT$$GT$8from_ref17hc7bd5b06f49ddec7E"(ptr align 1 %source.0, i64 %source.1) #14
  %inner.0.i = extractvalue { ptr, i64 } %0, 0
  %inner.1.i = extractvalue { ptr, i64 } %0, 1
; call zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
  %1 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17h7999d45e09566338E"(ptr %inner.0.i, i64 %inner.1.i) #14
  %_0.0.i = extractvalue { ptr, i64 } %1, 0
  %_0.1.i = extractvalue { ptr, i64 } %1, 1
  %_4.0 = extractvalue { ptr, i64 } %1, 0
  %_4.1 = extractvalue { ptr, i64 } %1, 1
  store i8 0, ptr %_5, align 1
  %2 = load i8, ptr %_5, align 1
  %3 = trunc nuw i8 %2 to i1
  %4 = zext i1 %3 to i8
  store i8 %4, ptr %meta.i, align 1
  store ptr %_4.0, ptr %self.i.i, align 8
  %5 = getelementptr inbounds i8, ptr %self.i.i, i64 8
  store i64 %_4.1, ptr %5, align 8
; call zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
  %6 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17h801ca11e9df76339E"(ptr align 8 %self.i.i) #14
  %old_inner.0.i.i = extractvalue { ptr, i64 } %6, 0
  %old_inner.1.i.i = extractvalue { ptr, i64 } %6, 1
  %_7.0.i.i = load ptr, ptr %self.i.i, align 8
  %7 = getelementptr inbounds i8, ptr %self.i.i, i64 8
  %_7.1.i.i = load i64, ptr %7, align 8
  store ptr %meta.i, ptr %_1.i, align 8
  store i8 0, ptr %_4.i, align 1
  %_15.i = load ptr, ptr %_1.i, align 8
  %8 = load i8, ptr %_15.i, align 1
  %_5.i = trunc nuw i8 %8 to i1
  %9 = load i8, ptr %_4.i, align 1
  %10 = trunc nuw i8 %9 to i1
  store ptr %_7.0.i.i, ptr %self.i.i1, align 8
  %11 = getelementptr inbounds i8, ptr %self.i.i1, i64 8
  store i64 %_7.1.i.i, ptr %11, align 8
; call zerocopy::pointer::ptr::def::Ptr<T,I>::as_inner
  %12 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$8as_inner17h801ca11e9df76339E"(ptr align 8 %self.i.i1) #14
  %_9.0.i.i = extractvalue { ptr, i64 } %12, 0
  %_9.1.i.i = extractvalue { ptr, i64 } %12, 1
; call zerocopy::pointer::inner::<impl zerocopy::pointer::inner::_def::PtrInner<[u8]>>::try_cast_into
  call void @"_ZN8zerocopy7pointer5inner78_$LT$impl$u20$zerocopy..pointer..inner.._def..PtrInner$LT$$u5b$u8$u5d$$GT$$GT$13try_cast_into17h3f9659ced87cb72fE"(ptr sret([32 x i8]) align 8 %_8.i.i, ptr %_9.0.i.i, i64 %_9.1.i.i, i1 zeroext %10, i1 zeroext %_5.i) #14
; call core::result::Result<T,E>::map_err
  call void @"_ZN4core6result19Result$LT$T$C$E$GT$7map_err17hffd1455effdf2821E"(ptr sret([32 x i8]) align 8 %_7.i.i, ptr align 8 %_8.i.i) #14
; call <core::result::Result<T,E> as core::ops::try_trait::Try>::branch
  call void @"_ZN79_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17h2fcadaea52e1380bE"(ptr sret([32 x i8]) align 8 %_6.i.i, ptr align 8 %_7.i.i) #14
  %_11.i.i = load i64, ptr %_6.i.i, align 8
  %13 = trunc nuw i64 %_11.i.i to i1
  br i1 %13, label %bb7.i.i, label %bb6.i.i

bb7.i.i:                                          ; preds = %bb2
  %14 = getelementptr inbounds i8, ptr %_6.i.i, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %residual.i.i, ptr align 8 %14, i64 24, i1 false)
; call <core::result::Result<T,F> as core::ops::try_trait::FromResidual<core::result::Result<core::convert::Infallible,E>>>::from_residual
  call void @"_ZN153_$LT$core..result..Result$LT$T$C$F$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..result..Result$LT$core..convert..Infallible$C$E$GT$$GT$$GT$13from_residual17habf6625c1fc10ec1E"(ptr sret([32 x i8]) align 8 %_3.i, ptr align 8 %residual.i.i, ptr align 8 @alloc_43af08c406911e254d158ce900b82413) #14
  br label %"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$13try_cast_into17h25178ec849c75b08E.exit.i"

bb6.i.i:                                          ; preds = %bb2
  %15 = getelementptr inbounds i8, ptr %_6.i.i, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %val.i.i, ptr align 8 %15, i64 24, i1 false)
  %inner.i.i = load ptr, ptr %val.i.i, align 8
  %16 = getelementptr inbounds i8, ptr %val.i.i, i64 8
  %remainder.0.i.i = load ptr, ptr %16, align 8
  %17 = getelementptr inbounds i8, ptr %16, i64 8
  %remainder.1.i.i = load i64, ptr %17, align 8
; call zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
  %res.i.i = call ptr @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17he81ccfeaff6c6b60E"(ptr %inner.i.i) #14
; call zerocopy::pointer::ptr::def::Ptr<T,I>::from_inner
  %18 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr3def16Ptr$LT$T$C$I$GT$10from_inner17h7999d45e09566338E"(ptr %remainder.0.i.i, i64 %remainder.1.i.i) #14
  %remainder.01.i.i = extractvalue { ptr, i64 } %18, 0
  %remainder.12.i.i = extractvalue { ptr, i64 } %18, 1
  store ptr %res.i.i, ptr %_16.i.i, align 8
  %19 = getelementptr inbounds i8, ptr %_16.i.i, i64 8
  store ptr %remainder.01.i.i, ptr %19, align 8
  %20 = getelementptr inbounds i8, ptr %19, i64 8
  store i64 %remainder.12.i.i, ptr %20, align 8
  %21 = getelementptr inbounds i8, ptr %_3.i, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %21, ptr align 8 %_16.i.i, i64 24, i1 false)
  store i64 0, ptr %_3.i, align 8
  br label %"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$13try_cast_into17h25178ec849c75b08E.exit.i"

"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$13try_cast_into17h25178ec849c75b08E.exit.i": ; preds = %bb6.i.i, %bb7.i.i
  %_6.i = load i64, ptr %_3.i, align 8
  %22 = trunc nuw i64 %_6.i to i1
  br i1 %22, label %bb3.i, label %bb4.i

bb3.i:                                            ; preds = %"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$13try_cast_into17h25178ec849c75b08E.exit.i"
  %23 = getelementptr inbounds i8, ptr %_3.i, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %err.i, ptr align 8 %23, i64 24, i1 false)
; call zerocopy::error::ConvertError<zerocopy::error::AlignmentError<Src,Dst>,zerocopy::error::SizeError<Src,Dst>,core::convert::Infallible>::map_src
  %_14.i = call zeroext i1 @"_ZN8zerocopy5error142ConvertError$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$C$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$C$core..convert..Infallible$GT$7map_src17h9f9510464e1be662E"(ptr align 8 %err.i) #14
  %24 = getelementptr inbounds i8, ptr %_5.i.i, i64 1
  %25 = zext i1 %_14.i to i8
  store i8 %25, ptr %24, align 1
  store i8 1, ptr %_5.i.i, align 8
  br label %"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$25try_cast_into_no_leftover28_$u7b$$u7b$closure$u7d$$u7d$17h854b2ea29ee7cd7eE.exit"

bb4.i:                                            ; preds = %"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$13try_cast_into17h25178ec849c75b08E.exit.i"
  %26 = getelementptr inbounds i8, ptr %_3.i, i64 8
  %slf.i = load ptr, ptr %26, align 8
  %27 = getelementptr inbounds i8, ptr %_3.i, i64 8
  %28 = getelementptr inbounds i8, ptr %27, i64 8
  %29 = load ptr, ptr %28, align 8
  %30 = getelementptr inbounds i8, ptr %28, i64 8
  %31 = load i64, ptr %30, align 8
  store ptr %29, ptr %remainder.i, align 8
  %32 = getelementptr inbounds i8, ptr %remainder.i, i64 8
  store i64 %31, ptr %32, align 8
; call zerocopy::pointer::ptr::_project::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::is_empty
  %_9.i = call zeroext i1 @"_ZN8zerocopy7pointer3ptr8_project63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$8is_empty17hd0e663a8b7fd10fbE"(ptr align 8 %remainder.i) #14
  br i1 %_9.i, label %bb6.i, label %bb7.i

bb7.i:                                            ; preds = %bb4.i
; call zerocopy::error::SizeError<Src,Dst>::new
  call void @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17h4ec66291b0b58be6E"() #14
  store i8 1, ptr %_11.i, align 1
  %33 = load i8, ptr %_11.i, align 1
  %34 = trunc nuw i8 %33 to i1
  %35 = getelementptr inbounds i8, ptr %_5.i.i, i64 1
  %36 = zext i1 %34 to i8
  store i8 %36, ptr %35, align 1
  store i8 1, ptr %_5.i.i, align 8
  br label %"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$25try_cast_into_no_leftover28_$u7b$$u7b$closure$u7d$$u7d$17h854b2ea29ee7cd7eE.exit"

bb6.i:                                            ; preds = %bb4.i
  %37 = getelementptr inbounds i8, ptr %_5.i.i, i64 8
  store ptr %slf.i, ptr %37, align 8
  store i8 0, ptr %_5.i.i, align 8
  br label %"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$25try_cast_into_no_leftover28_$u7b$$u7b$closure$u7d$$u7d$17h854b2ea29ee7cd7eE.exit"

"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$25try_cast_into_no_leftover28_$u7b$$u7b$closure$u7d$$u7d$17h854b2ea29ee7cd7eE.exit": ; preds = %bb3.i, %bb7.i, %bb6.i
; call core::result::Result<T,E>::map_err
  call void @"_ZN4core6result19Result$LT$T$C$E$GT$7map_err17h1bd886c68be95901E"(ptr sret([24 x i8]) align 8 %_3, ptr align 8 %_5.i.i, ptr %old_inner.0.i.i, i64 %old_inner.1.i.i) #14
  %38 = load i64, ptr %_3, align 8
  %39 = icmp eq i64 %38, 2
  %_6 = select i1 %39, i64 0, i64 1
  %40 = trunc nuw i64 %_6 to i1
  br i1 %40, label %bb6, label %bb7

bb6:                                              ; preds = %"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$25try_cast_into_no_leftover28_$u7b$$u7b$closure$u7d$$u7d$17h854b2ea29ee7cd7eE.exit"
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %err, ptr align 8 %_3, i64 24, i1 false)
; call zerocopy::error::ConvertError<zerocopy::error::AlignmentError<Src,Dst>,zerocopy::error::SizeError<Src,Dst>,core::convert::Infallible>::map_src
  call void @"_ZN8zerocopy5error142ConvertError$LT$zerocopy..error..AlignmentError$LT$Src$C$Dst$GT$$C$zerocopy..error..SizeError$LT$Src$C$Dst$GT$$C$core..convert..Infallible$GT$7map_src17hd0f9105e56625d1bE"(ptr sret([24 x i8]) align 8 %_11, ptr align 8 %err) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_11, i64 24, i1 false)
  br label %bb11

bb7:                                              ; preds = %"_ZN8zerocopy7pointer3ptr6_casts74_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$$u5b$u8$u5d$$C$I$GT$$GT$25try_cast_into_no_leftover28_$u7b$$u7b$closure$u7d$$u7d$17h854b2ea29ee7cd7eE.exit"
  %41 = getelementptr inbounds i8, ptr %_3, i64 8
  %ptr = load ptr, ptr %41, align 8
; call zerocopy::pointer::ptr::_conversions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::recall_validity
  %_9 = call ptr @"_ZN8zerocopy7pointer3ptr12_conversions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$15recall_validity17h126b8dae3c9c939eE"(ptr %ptr) #14
; call zerocopy::pointer::ptr::_conversions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::as_ref
  %_8 = call align 1 ptr @"_ZN8zerocopy7pointer3ptr12_conversions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$6as_ref17ha7b0957f87e2139dE"(ptr %_9) #14
  %42 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %_8, ptr %42, align 8
  store i64 2, ptr %_0, align 8
  br label %bb11

bb11:                                             ; preds = %bb6, %bb7
  ret void

bb5:                                              ; No predecessors!
  unreachable

bb1:                                              ; No predecessors!
  unreachable
}

; zerocopy::FromBytes::ref_from_bytes::{{closure}}
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN8zerocopy9FromBytes14ref_from_bytes28_$u7b$$u7b$closure$u7d$$u7d$17hbaaefa6ef958b60bE"(ptr %src.0, i64 %src.1) unnamed_addr #0 {
start:
; call zerocopy::pointer::ptr::_conversions::<impl zerocopy::pointer::ptr::def::Ptr<T,I>>::as_ref
  %0 = call { ptr, i64 } @"_ZN8zerocopy7pointer3ptr12_conversions63_$LT$impl$u20$zerocopy..pointer..ptr..def..Ptr$LT$T$C$I$GT$$GT$6as_ref17h6aa45dbbf1297d7cE"(ptr %src.0, i64 %src.1) #14
  %_0.0 = extractvalue { ptr, i64 } %0, 0
  %_0.1 = extractvalue { ptr, i64 } %0, 1
  %1 = insertvalue { ptr, i64 } poison, ptr %_0.0, 0
  %2 = insertvalue { ptr, i64 } %1, i64 %_0.1, 1
  ret { ptr, i64 } %2
}

; zerocopy::FromBytes::read_from_bytes
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN8zerocopy9FromBytes15read_from_bytes17h7dfc2b7241a232c8E(ptr sret([16 x i8]) align 8 %_0, ptr align 1 %source.0, i64 %source.1) unnamed_addr #0 {
start:
  %_0.i1.i.i = alloca [8 x i8], align 1
  %0 = alloca [8 x i8], align 8
  %value.i.i.i = alloca [8 x i8], align 1
  %_0.i.i.i = alloca [8 x i8], align 1
  %1 = alloca [8 x i8], align 8
  %slot.i.i.i = alloca [8 x i8], align 1
  %2 = alloca [8 x i8], align 8
  %3 = alloca [8 x i8], align 8
  %4 = alloca [8 x i8], align 8
  %5 = alloca [8 x i8], align 8
  %_5.i.i = alloca [8 x i8], align 1
  %_4.i.i = alloca [8 x i8], align 1
  %_3.i.i = alloca [8 x i8], align 1
  %_0.i.i = alloca [8 x i8], align 1
  %6 = alloca [8 x i8], align 8
  %src.i.i = alloca [8 x i8], align 1
  %7 = alloca [8 x i8], align 8
  %8 = alloca [8 x i8], align 8
  %_0.i = alloca [8 x i8], align 1
  %9 = alloca [8 x i8], align 8
  %self.i = alloca [8 x i8], align 1
  %10 = alloca [8 x i8], align 8
  %11 = alloca [8 x i8], align 8
  %12 = alloca [8 x i8], align 8
  %_7 = alloca [8 x i8], align 1
  %_6 = alloca [8 x i8], align 1
  %r = alloca [24 x i8], align 8
  %_2 = alloca [32 x i8], align 8
; call zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::sized_from
  call void @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$10sized_from17h84a0543841e5444cE"(ptr sret([32 x i8]) align 8 %_2, ptr align 1 %source.0, i64 %source.1) #14
  %_4 = load i64, ptr %_2, align 8
  %13 = trunc nuw i64 %_4 to i1
  br i1 %13, label %bb3, label %bb6

bb3:                                              ; preds = %start
  %14 = getelementptr inbounds i8, ptr %_2, i64 8
  %_3 = load i64, ptr %14, align 8
  %15 = trunc nuw i64 %_3 to i1
  br i1 %15, label %bb5, label %bb4

bb6:                                              ; preds = %start
  %16 = getelementptr inbounds i8, ptr %_2, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %r, ptr align 8 %16, i64 24, i1 false)
; call zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::read
  %17 = call i64 @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$4read17ha3073fb02ddf5463E"(ptr align 8 %r) #14
  store i64 %17, ptr %12, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_7, ptr align 8 %12, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %11, ptr align 1 %_7, i64 8, i1 false)
  %18 = load i64, ptr %11, align 8
  store i64 %18, ptr %9, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %self.i, ptr align 8 %9, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %8, ptr align 1 %self.i, i64 8, i1 false)
  %19 = load i64, ptr %8, align 8
  store i64 %19, ptr %6, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %src.i.i, ptr align 8 %6, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %5, ptr align 1 %src.i.i, i64 8, i1 false)
  %20 = load i64, ptr %5, align 8
  store i64 %20, ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %value.i.i.i, ptr align 8 %0, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0.i1.i.i, ptr align 1 %value.i.i.i, i64 8, i1 false)
  %21 = load i64, ptr %_0.i1.i.i, align 1
  store i64 %21, ptr %4, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_5.i.i, ptr align 8 %4, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_4.i.i, ptr align 1 %_5.i.i, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_3.i.i, ptr align 1 %_4.i.i, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %3, ptr align 1 %_3.i.i, i64 8, i1 false)
  %22 = load i64, ptr %3, align 8
  store i64 %22, ptr %1, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %slot.i.i.i, ptr align 8 %1, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0.i.i.i, ptr align 1 %slot.i.i.i, i64 8, i1 false)
  %23 = load i64, ptr %_0.i.i.i, align 1
  store i64 %23, ptr %2, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0.i.i, ptr align 8 %2, i64 8, i1 false)
  %24 = load i64, ptr %_0.i.i, align 1
  store i64 %24, ptr %7, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0.i, ptr align 8 %7, i64 8, i1 false)
  %25 = load i64, ptr %_0.i, align 1
  store i64 %25, ptr %10, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_6, ptr align 8 %10, i64 8, i1 false)
  %26 = getelementptr inbounds i8, ptr %_0, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %26, ptr align 1 %_6, i64 8, i1 false)
  store ptr null, ptr %_0, align 8
  br label %bb10

bb10:                                             ; preds = %bb5, %bb6
  ret void

bb5:                                              ; preds = %bb3
  %27 = getelementptr inbounds i8, ptr %_2, i64 8
  %28 = getelementptr inbounds i8, ptr %27, i64 8
  %e.0 = load ptr, ptr %28, align 8
  %29 = getelementptr inbounds i8, ptr %28, i64 8
  %e.1 = load i64, ptr %29, align 8
; call zerocopy::error::SizeError<Src,Dst>::with_dst
  %30 = call { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$8with_dst17h919ef6595d35425dE"(ptr align 1 %e.0, i64 %e.1) #14
  %_10.0 = extractvalue { ptr, i64 } %30, 0
  %_10.1 = extractvalue { ptr, i64 } %30, 1
  store ptr %_10.0, ptr %_0, align 8
  %31 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %_10.1, ptr %31, align 8
  br label %bb10

bb4:                                              ; preds = %bb3
; call core::hint::unreachable_unchecked
  call void @_ZN4core4hint21unreachable_unchecked17h21c3b9f74b946857E(ptr align 8 @alloc_a4fa2aa40384d33bcd146a1f883fbfac) #15
  unreachable

bb2:                                              ; No predecessors!
  unreachable
}

; zerocopy::FromBytes::read_from_bytes
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN8zerocopy9FromBytes15read_from_bytes17hb75740783c564722E(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %source.0, i64 %source.1) unnamed_addr #0 {
start:
  %_5.i.i = alloca [16 x i8], align 1
  %_4.i.i = alloca [16 x i8], align 1
  %_3.i.i = alloca [16 x i8], align 1
  %_7 = alloca [16 x i8], align 1
  %_6 = alloca [16 x i8], align 1
  %r = alloca [24 x i8], align 8
  %_2 = alloca [32 x i8], align 8
; call zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::sized_from
  call void @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$10sized_from17h6914f5febbbbc0deE"(ptr sret([32 x i8]) align 8 %_2, ptr align 1 %source.0, i64 %source.1) #14
  %_4 = load i64, ptr %_2, align 8
  %0 = trunc nuw i64 %_4 to i1
  br i1 %0, label %bb3, label %bb6

bb3:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %_2, i64 8
  %_3 = load i64, ptr %1, align 8
  %2 = trunc nuw i64 %_3 to i1
  br i1 %2, label %bb5, label %bb4

bb6:                                              ; preds = %start
  %3 = getelementptr inbounds i8, ptr %_2, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %r, ptr align 8 %3, i64 24, i1 false)
; call zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::read
  call void @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$4read17h23881d3f68faaf40E"(ptr sret([16 x i8]) align 1 %_7, ptr align 8 %r) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_5.i.i, ptr align 1 %_7, i64 16, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_4.i.i, ptr align 1 %_5.i.i, i64 16, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_3.i.i, ptr align 1 %_4.i.i, i64 16, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_6, ptr align 1 %_3.i.i, i64 16, i1 false)
  %4 = getelementptr inbounds i8, ptr %_0, i64 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %4, ptr align 1 %_6, i64 16, i1 false)
  store i8 0, ptr %_0, align 8
  br label %bb10

bb10:                                             ; preds = %bb5, %bb6
  ret void

bb5:                                              ; preds = %bb3
  %5 = getelementptr inbounds i8, ptr %_2, i64 8
  %6 = getelementptr inbounds i8, ptr %5, i64 8
  %e.0 = load ptr, ptr %6, align 8
  %7 = getelementptr inbounds i8, ptr %6, i64 8
  %e.1 = load i64, ptr %7, align 8
; call zerocopy::error::SizeError<Src,Dst>::with_dst
  %8 = call { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$8with_dst17ha92b9efa146cad10E"(ptr align 1 %e.0, i64 %e.1) #14
  %_10.0 = extractvalue { ptr, i64 } %8, 0
  %_10.1 = extractvalue { ptr, i64 } %8, 1
  %9 = getelementptr inbounds i8, ptr %_0, i64 8
  store ptr %_10.0, ptr %9, align 8
  %10 = getelementptr inbounds i8, ptr %9, i64 8
  store i64 %_10.1, ptr %10, align 8
  store i8 1, ptr %_0, align 8
  br label %bb10

bb4:                                              ; preds = %bb3
; call core::hint::unreachable_unchecked
  call void @_ZN4core4hint21unreachable_unchecked17h21c3b9f74b946857E(ptr align 8 @alloc_a4fa2aa40384d33bcd146a1f883fbfac) #15
  unreachable

bb2:                                              ; No predecessors!
  unreachable
}

; zerocopy::FromBytes::read_from_bytes
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @_ZN8zerocopy9FromBytes15read_from_bytes17hc141de9c938fd231E(ptr sret([16 x i8]) align 8 %_0, ptr align 1 %source.0, i64 %source.1) unnamed_addr #0 {
start:
  %_0.i.i.i = alloca [8 x i8], align 1
  %0 = alloca [8 x i8], align 8
  %value.i.i.i = alloca [8 x i8], align 1
  %1 = alloca [8 x i8], align 8
  %2 = alloca [8 x i8], align 8
  %_5.i.i = alloca [8 x i8], align 1
  %_4.i.i = alloca [8 x i8], align 8
  %3 = alloca [8 x i8], align 8
  %src.i.i = alloca [8 x i8], align 1
  %4 = alloca [8 x i8], align 8
  %5 = alloca [8 x i8], align 8
  %self.i = alloca [8 x i8], align 1
  %6 = alloca [8 x i8], align 8
  %7 = alloca [8 x i8], align 8
  %_7 = alloca [8 x i8], align 1
  %r = alloca [24 x i8], align 8
  %_2 = alloca [32 x i8], align 8
; call zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::sized_from
  call void @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$10sized_from17h62c54e1ff9599918E"(ptr sret([32 x i8]) align 8 %_2, ptr align 1 %source.0, i64 %source.1) #14
  %_4 = load i64, ptr %_2, align 8
  %8 = trunc nuw i64 %_4 to i1
  br i1 %8, label %bb3, label %bb6

bb3:                                              ; preds = %start
  %9 = getelementptr inbounds i8, ptr %_2, i64 8
  %_3 = load i64, ptr %9, align 8
  %10 = trunc nuw i64 %_3 to i1
  br i1 %10, label %bb5, label %bb4

bb6:                                              ; preds = %start
  %11 = getelementptr inbounds i8, ptr %_2, i64 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %r, ptr align 8 %11, i64 24, i1 false)
; call zerocopy::ref::<impl zerocopy::ref::def::Ref<B,T>>::read
  %12 = call i64 @"_ZN8zerocopy3ref54_$LT$impl$u20$zerocopy..ref..def..Ref$LT$B$C$T$GT$$GT$4read17h8ba7c23d7e825d21E"(ptr align 8 %r) #14
  store i64 %12, ptr %7, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_7, ptr align 8 %7, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %6, ptr align 1 %_7, i64 8, i1 false)
  %13 = load i64, ptr %6, align 8
  store i64 %13, ptr %5, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %self.i, ptr align 8 %5, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %4, ptr align 1 %self.i, i64 8, i1 false)
  %14 = load i64, ptr %4, align 8
  store i64 %14, ptr %3, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %src.i.i, ptr align 8 %3, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %2, ptr align 1 %src.i.i, i64 8, i1 false)
  %15 = load i64, ptr %2, align 8
  store i64 %15, ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %value.i.i.i, ptr align 8 %0, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0.i.i.i, ptr align 1 %value.i.i.i, i64 8, i1 false)
  %16 = load i64, ptr %_0.i.i.i, align 1
  store i64 %16, ptr %1, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_5.i.i, ptr align 8 %1, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_4.i.i, ptr align 1 %_5.i.i, i64 8, i1 false)
  %_3.i.i = load i64, ptr %_4.i.i, align 8
  %17 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %_3.i.i, ptr %17, align 8
  store ptr null, ptr %_0, align 8
  br label %bb10

bb10:                                             ; preds = %bb5, %bb6
  ret void

bb5:                                              ; preds = %bb3
  %18 = getelementptr inbounds i8, ptr %_2, i64 8
  %19 = getelementptr inbounds i8, ptr %18, i64 8
  %e.0 = load ptr, ptr %19, align 8
  %20 = getelementptr inbounds i8, ptr %19, i64 8
  %e.1 = load i64, ptr %20, align 8
; call zerocopy::error::SizeError<Src,Dst>::with_dst
  %21 = call { ptr, i64 } @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$8with_dst17hedf4e3d124b30148E"(ptr align 1 %e.0, i64 %e.1) #14
  %_10.0 = extractvalue { ptr, i64 } %21, 0
  %_10.1 = extractvalue { ptr, i64 } %21, 1
  store ptr %_10.0, ptr %_0, align 8
  %22 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %_10.1, ptr %22, align 8
  br label %bb10

bb4:                                              ; preds = %bb3
; call core::hint::unreachable_unchecked
  call void @_ZN4core4hint21unreachable_unchecked17h21c3b9f74b946857E(ptr align 8 @alloc_a4fa2aa40384d33bcd146a1f883fbfac) #15
  unreachable

bb2:                                              ; No predecessors!
  unreachable
}

; zerocopy::IntoBytes::write_to
; Function Attrs: inlinehint nounwind nonlazybind
define internal align 1 ptr @_ZN8zerocopy9IntoBytes8write_to17h333dd8283fe0b02eE(ptr align 1 %self, ptr align 1 %dst.0, i64 %dst.1) unnamed_addr #0 {
start:
  %_0 = alloca [8 x i8], align 8
; call core::mem::size_of_val
  %len.i = call i64 @_ZN4core3mem11size_of_val17hbf8b027503e661beE(ptr align 1 %self) #14
; call core::slice::raw::from_raw_parts
  %0 = call { ptr, i64 } @_ZN4core5slice3raw14from_raw_parts17h01ee7e45a67da397E(ptr align 1 %self, i64 %len.i, ptr align 8 @alloc_47681e2ae4251711b9fba137fe3c184f) #14
  %_0.0.i = extractvalue { ptr, i64 } %0, 0
  %_0.1.i = extractvalue { ptr, i64 } %0, 1
  %src.0 = extractvalue { ptr, i64 } %0, 0
  %src.1 = extractvalue { ptr, i64 } %0, 1
  %_4 = icmp eq i64 %dst.1, %src.1
  br i1 %_4, label %bb2, label %bb4

bb4:                                              ; preds = %start
; call zerocopy::error::SizeError<Src,Dst>::new
  %_9 = call align 1 ptr @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17hef446897463d0a96E"(ptr align 1 %self) #14
  store ptr %_9, ptr %_0, align 8
  br label %bb6

bb2:                                              ; preds = %start
  %_3.i = icmp ule i64 %src.1, %dst.1
  br i1 %_3.i, label %_ZN8zerocopy4util14copy_unchecked17h78e036eb51373068E.exit, label %bb1.i

bb1.i:                                            ; preds = %bb2
; call core::panicking::panic
  call void @_ZN4core9panicking5panic17h239804395728b21fE(ptr align 1 @alloc_f3cc2310f7efe1762c6731b6a8e4875b, i64 40, ptr align 8 @alloc_03c388b1e702c5d2e3d9dbcfde85d5b3) #15
  unreachable

_ZN8zerocopy4util14copy_unchecked17h78e036eb51373068E.exit: ; preds = %bb2
; call core::ptr::copy_nonoverlapping::precondition_check
  call void @_ZN4core3ptr19copy_nonoverlapping18precondition_check17h1af93ef5bb8d2ab6E(ptr align 1 %src.0, ptr align 1 %dst.0, i64 1, i64 1, i64 %src.1, ptr align 8 @alloc_9b0170f47317373e331799536b583a9f) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst.0, ptr align 1 %src.0, i64 %src.1, i1 false)
  store ptr null, ptr %_0, align 8
  br label %bb6

bb6:                                              ; preds = %_ZN8zerocopy4util14copy_unchecked17h78e036eb51373068E.exit, %bb4
  %1 = load ptr, ptr %_0, align 8
  ret ptr %1
}

; zerocopy::IntoBytes::write_to
; Function Attrs: inlinehint nounwind nonlazybind
define internal align 1 ptr @_ZN8zerocopy9IntoBytes8write_to17h50ba8809e39be976E(ptr align 1 %self, ptr align 1 %dst.0, i64 %dst.1) unnamed_addr #0 {
start:
  %_0 = alloca [8 x i8], align 8
; call core::mem::size_of_val
  %len.i = call i64 @_ZN4core3mem11size_of_val17h461cba1b7fec62f5E(ptr align 1 %self) #14
; call core::slice::raw::from_raw_parts
  %0 = call { ptr, i64 } @_ZN4core5slice3raw14from_raw_parts17h01ee7e45a67da397E(ptr align 1 %self, i64 %len.i, ptr align 8 @alloc_47681e2ae4251711b9fba137fe3c184f) #14
  %_0.0.i = extractvalue { ptr, i64 } %0, 0
  %_0.1.i = extractvalue { ptr, i64 } %0, 1
  %src.0 = extractvalue { ptr, i64 } %0, 0
  %src.1 = extractvalue { ptr, i64 } %0, 1
  %_4 = icmp eq i64 %dst.1, %src.1
  br i1 %_4, label %bb2, label %bb4

bb4:                                              ; preds = %start
; call zerocopy::error::SizeError<Src,Dst>::new
  %_9 = call align 1 ptr @"_ZN8zerocopy5error26SizeError$LT$Src$C$Dst$GT$3new17h17cc28c5c583c726E"(ptr align 1 %self) #14
  store ptr %_9, ptr %_0, align 8
  br label %bb6

bb2:                                              ; preds = %start
  %_3.i = icmp ule i64 %src.1, %dst.1
  br i1 %_3.i, label %_ZN8zerocopy4util14copy_unchecked17h78e036eb51373068E.exit, label %bb1.i

bb1.i:                                            ; preds = %bb2
; call core::panicking::panic
  call void @_ZN4core9panicking5panic17h239804395728b21fE(ptr align 1 @alloc_f3cc2310f7efe1762c6731b6a8e4875b, i64 40, ptr align 8 @alloc_03c388b1e702c5d2e3d9dbcfde85d5b3) #15
  unreachable

_ZN8zerocopy4util14copy_unchecked17h78e036eb51373068E.exit: ; preds = %bb2
; call core::ptr::copy_nonoverlapping::precondition_check
  call void @_ZN4core3ptr19copy_nonoverlapping18precondition_check17h1af93ef5bb8d2ab6E(ptr align 1 %src.0, ptr align 1 %dst.0, i64 1, i64 1, i64 %src.1, ptr align 8 @alloc_9b0170f47317373e331799536b583a9f) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst.0, ptr align 1 %src.0, i64 %src.1, i1 false)
  store ptr null, ptr %_0, align 8
  br label %bb6

bb6:                                              ; preds = %_ZN8zerocopy4util14copy_unchecked17h78e036eb51373068E.exit, %bb4
  %1 = load ptr, ptr %_0, align 8
  ret ptr %1
}

; <core::ptr::non_null::NonNull<T> as core::convert::From<&T>>::from
; Function Attrs: inlinehint nounwind nonlazybind
define internal { ptr, i64 } @"_ZN90_$LT$core..ptr..non_null..NonNull$LT$T$GT$$u20$as$u20$core..convert..From$LT$$RF$T$GT$$GT$4from17hd39d9ba562bec714E"(ptr align 1 %r.0, i64 %r.1) unnamed_addr #0 {
start:
  %0 = insertvalue { ptr, i64 } poison, ptr %r.0, 0
  %1 = insertvalue { ptr, i64 } %0, i64 %r.1, 1
  ret { ptr, i64 } %1
}

; <core::ops::try_trait::NeverShortCircuit<T> as core::ops::try_trait::Try>::from_output
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN94_$LT$core..ops..try_trait..NeverShortCircuit$LT$T$GT$$u20$as$u20$core..ops..try_trait..Try$GT$11from_output17h4c8a75f1d068ec78E"(ptr sret([16 x i8]) align 1 %_0, ptr align 1 %x) unnamed_addr #0 {
start:
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0, ptr align 1 %x, i64 16, i1 false)
  ret void
}

; <core::ops::try_trait::NeverShortCircuit<T> as core::ops::try_trait::Try>::branch
; Function Attrs: inlinehint nounwind nonlazybind
define internal i8 @"_ZN94_$LT$core..ops..try_trait..NeverShortCircuit$LT$T$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17hab34c1accb7c7c09E"(i8 %self) unnamed_addr #0 {
start:
  %_0 = alloca [1 x i8], align 1
  store i8 %self, ptr %_0, align 1
  %0 = load i8, ptr %_0, align 1
  ret i8 %0
}

; <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h114ac4c20ee5a3a0E"(ptr sret([32 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
; call core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
  call void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17h7f12c327d7b3c1e7E"(ptr sret([32 x i8]) align 8 %_0, ptr align 8 %self, i64 289) #14
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h4cf0f7b71d3c67a4E"(ptr sret([64 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
; call core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
  call void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17ha7b2489d5115c341E"(ptr sret([64 x i8]) align 8 %_0, ptr align 8 %self, i64 144) #14
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h73063a66b0101d33E"(ptr sret([17 x i8]) align 1 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
; call core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
  call void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17hc04c71adeb3c0847E"(ptr sret([17 x i8]) align 1 %_0, ptr align 8 %self, i64 12) #14
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h765e1cfb9add1435E"(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
; call core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
  call void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17h83e271421541d69cE"(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %self, i64 17) #14
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal { i64, i64 } @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h97f1caf174d894b1E"(ptr align 8 %self) unnamed_addr #0 {
start:
; call core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
  %0 = call { i64, i64 } @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17hf903c3629b32bc4fE"(ptr align 8 %self, i64 2) #14
  %_0.0 = extractvalue { i64, i64 } %0, 0
  %_0.1 = extractvalue { i64, i64 } %0, 1
  %1 = insertvalue { i64, i64 } poison, i64 %_0.0, 0
  %2 = insertvalue { i64, i64 } %1, i64 %_0.1, 1
  ret { i64, i64 } %2
}

; <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal { i64, i64 } @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17ha251e644709270caE"(ptr align 8 %self) unnamed_addr #0 {
start:
; call core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
  %0 = call { i64, i64 } @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17h5491f5036cfbf5ffE"(ptr align 8 %self, i64 17) #14
  %_0.0 = extractvalue { i64, i64 } %0, 0
  %_0.1 = extractvalue { i64, i64 } %0, 1
  %1 = insertvalue { i64, i64 } poison, i64 %_0.0, 0
  %2 = insertvalue { i64, i64 } %1, i64 %_0.1, 1
  ret { i64, i64 } %2
}

; <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17ha4f8e32da9056a90E"(ptr sret([40 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
; call core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
  call void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17hfc3802082c92961dE"(ptr sret([40 x i8]) align 8 %_0, ptr align 8 %self, i64 144) #14
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17ha81cec4ae52ac598E"(ptr sret([40 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
; call core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
  call void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17h8ceb2f03430a553cE"(ptr sret([40 x i8]) align 8 %_0, ptr align 8 %self, i64 289) #14
  ret void
}

; <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
; Function Attrs: inlinehint nounwind nonlazybind
define internal void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hb3a617123b21ed31E"(ptr sret([48 x i8]) align 8 %_0, ptr align 8 %self) unnamed_addr #0 {
start:
; call core::array::iter::iter_inner::PolymorphicIter<[core::mem::maybe_uninit::MaybeUninit<T>]>::next
  call void @"_ZN4core5array4iter10iter_inner78PolymorphicIter$LT$$u5b$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$u5d$$GT$4next17h3c562e2db464758cE"(ptr sret([48 x i8]) align 8 %_0, ptr align 8 %self, i64 578) #14
  ret void
}

; extended_pilot::helper_math
; Function Attrs: nounwind nonlazybind
define internal i64 @_ZN14extended_pilot11helper_math17h8abbf2b36f1bb902E(i64 %a, i64 %b) unnamed_addr #1 {
start:
  %0 = alloca [8 x i8], align 8
  %1 = call i64 @llvm.fshl.i64(i64 %a, i64 %a, i64 13)
  store i64 %1, ptr %0, align 8
  %_0.i = load i64, ptr %0, align 8
  %_0.i1 = mul i64 %b, -7046029288634856825
  %_0 = xor i64 %_0.i, %_0.i1
  ret i64 %_0
}

; Function Attrs: noinline nounwind nonlazybind
define dso_local i64 @pilot_helper(i64 %a, i64 %b) unnamed_addr #2 {
start:
  %_5 = alloca [1 x i8], align 1
  store i8 0, ptr %_5, align 1
  %0 = load i8, ptr %_5, align 1
; call core::sync::atomic::AtomicUsize::fetch_add
  %_3 = call i64 @_ZN4core4sync6atomic11AtomicUsize9fetch_add17h31c6c38a32e51c38E(ptr align 8 @_ZN14extended_pilot12HELPER_CALLS17hceaaa1dfa217d7abE, i64 1, i8 %0) #14
; call extended_pilot::helper_math
  %_0 = call i64 @_ZN14extended_pilot11helper_math17h8abbf2b36f1bb902E(i64 %a, i64 %b) #14
  ret i64 %_0
}

; extended_pilot::rust_mul
; Function Attrs: noinline nounwind nonlazybind
define internal { i64, i64 } @_ZN14extended_pilot8rust_mul17h23452971b31aa446E(i64 %a, i64 %b) unnamed_addr #2 {
start:
  %_0.i1 = zext i64 %a to i128
  %_0.i = zext i64 %b to i128
  %0 = call { i128, i1 } @llvm.umul.with.overflow.i128(i128 %_0.i1, i128 %_0.i)
  %_6.0 = extractvalue { i128, i1 } %0, 0
  %_6.1 = extractvalue { i128, i1 } %0, 1
  br i1 %_6.1, label %panic, label %bb3

bb3:                                              ; preds = %start
  %_7 = trunc i128 %_6.0 to i64
  %_9 = lshr i128 %_6.0, 64
  %_8 = trunc i128 %_9 to i64
  %1 = insertvalue { i64, i64 } poison, i64 %_7, 0
  %2 = insertvalue { i64, i64 } %1, i64 %_8, 1
  ret { i64, i64 } %2

panic:                                            ; preds = %start
; call core::panicking::panic_const::panic_const_mul_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_mul_overflow17hd5526b32f0b9d968E(ptr align 8 @alloc_9582a9046867ff233d22477abdba1e19) #15
  unreachable
}

; extended_pilot::rust_add128
; Function Attrs: noinline nounwind nonlazybind
define internal void @_ZN14extended_pilot11rust_add12817h7f46eaca12712c06E(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %a, ptr align 8 %b) unnamed_addr #2 {
start:
  %0 = alloca [32 x i8], align 16
  %1 = getelementptr inbounds nuw i64, ptr %a, i64 0
  %_5 = load i64, ptr %1, align 8
  %_0.i4 = zext i64 %_5 to i128
  %2 = getelementptr inbounds nuw i64, ptr %a, i64 1
  %_10 = load i64, ptr %2, align 8
  %_0.i3 = zext i64 %_10 to i128
  %_8 = shl i128 %_0.i3, 64
  %x = or i128 %_0.i4, %_8
  %3 = getelementptr inbounds nuw i64, ptr %b, i64 0
  %_17 = load i64, ptr %3, align 8
  %_0.i2 = zext i64 %_17 to i128
  %4 = getelementptr inbounds nuw i64, ptr %b, i64 1
  %_22 = load i64, ptr %4, align 8
  %_0.i1 = zext i64 %_22 to i128
  %_20 = shl i128 %_0.i1, 64
  %y = or i128 %_0.i2, %_20
  %5 = call { i128, i1 } @llvm.uadd.with.overflow.i128(i128 %x, i128 %y)
  %_5.0.i = extractvalue { i128, i1 } %5, 0
  %_5.1.i = extractvalue { i128, i1 } %5, 1
  store i128 %_5.0.i, ptr %0, align 16
  %6 = getelementptr inbounds i8, ptr %0, i64 16
  %7 = zext i1 %_5.1.i to i8
  store i8 %7, ptr %6, align 16
  %_29.0 = load i128, ptr %0, align 16
  %8 = getelementptr inbounds i8, ptr %0, i64 16
  %9 = load i8, ptr %8, align 16
  %_29.1 = trunc nuw i8 %9 to i1
  %_30 = trunc i128 %_29.0 to i64
  %_32 = lshr i128 %_29.0, 64
  %_31 = trunc i128 %_32 to i64
  %_0.i = zext i1 %_29.1 to i64
  store i64 %_30, ptr %_0, align 8
  %10 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %_31, ptr %10, align 8
  %11 = getelementptr inbounds i8, ptr %_0, i64 16
  store i64 %_0.i, ptr %11, align 8
  ret void
}

; extended_pilot::rust_carry
; Function Attrs: noinline nounwind nonlazybind
define internal { i64, i64 } @_ZN14extended_pilot10rust_carry17hcd557fb1e0beef8aE(i64 %a, i64 %b, i64 %cin) unnamed_addr #2 {
start:
  %_0.i3 = zext i64 %a to i128
  %_0.i2 = zext i64 %b to i128
  %0 = call { i128, i1 } @llvm.uadd.with.overflow.i128(i128 %_0.i3, i128 %_0.i2)
  %_8.0 = extractvalue { i128, i1 } %0, 0
  %_8.1 = extractvalue { i128, i1 } %0, 1
  br i1 %_8.1, label %panic, label %bb3

bb3:                                              ; preds = %start
  %_0.i = zext i64 %cin to i128
  %1 = call { i128, i1 } @llvm.uadd.with.overflow.i128(i128 %_8.0, i128 %_0.i)
  %_10.0 = extractvalue { i128, i1 } %1, 0
  %_10.1 = extractvalue { i128, i1 } %1, 1
  br i1 %_10.1, label %panic1, label %bb5

panic:                                            ; preds = %start
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_add_overflow17h371a9588e01a5f2aE(ptr align 8 @alloc_3593e8f28b974255b321f2f902d146b2) #15
  unreachable

bb5:                                              ; preds = %bb3
  %_11 = trunc i128 %_10.0 to i64
  %_13 = lshr i128 %_10.0, 64
  %_12 = trunc i128 %_13 to i64
  %2 = insertvalue { i64, i64 } poison, i64 %_11, 0
  %3 = insertvalue { i64, i64 } %2, i64 %_12, 1
  ret { i64, i64 } %3

panic1:                                           ; preds = %bb3
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_add_overflow17h371a9588e01a5f2aE(ptr align 8 @alloc_3593e8f28b974255b321f2f902d146b2) #15
  unreachable
}

; extended_pilot::rust_swap
; Function Attrs: noinline nounwind nonlazybind
define internal i64 @_ZN14extended_pilot9rust_swap17hb3a8b149d95298c4E(i64 %x) unnamed_addr #2 {
start:
  %0 = alloca [8 x i8], align 8
  %1 = call i64 @llvm.bswap.i64(i64 %x)
  store i64 %1, ptr %0, align 8
  %_0.i = load i64, ptr %0, align 8
  ret i64 %_0.i
}

; extended_pilot::rust_load
; Function Attrs: noinline nounwind nonlazybind
define internal i64 @_ZN14extended_pilot9rust_load17h119de87a71289100E(ptr align 8 %p) unnamed_addr #2 {
start:
  %_0 = load i64, ptr %p, align 8
  ret i64 %_0
}

; extended_pilot::rust_store
; Function Attrs: noinline nounwind nonlazybind
define internal void @_ZN14extended_pilot10rust_store17h8f7ecb3f0dbf5221E(ptr align 8 %p, i64 %x) unnamed_addr #2 {
start:
  store i64 %x, ptr %p, align 8
  ret void
}

; extended_pilot::rust_copy16
; Function Attrs: noinline nounwind nonlazybind
define internal void @_ZN14extended_pilot11rust_copy1617hf553a6eb2e70da00E(ptr align 1 %source, ptr align 1 %dst) unnamed_addr #2 {
start:
; call core::slice::<impl [T]>::copy_from_slice
  call void @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$15copy_from_slice17h9dd8a1e05b1baa82E"(ptr align 1 %dst, i64 16, ptr align 1 %source, i64 16, ptr align 8 @alloc_237662a0f6470bc7d494d03469948f8d) #14
  ret void
}

; extended_pilot::rust_ptr
; Function Attrs: noinline nounwind nonlazybind
define internal ptr @_ZN14extended_pilot8rust_ptr17h749ef15fb3237769E(ptr align 1 %source, i64 %offset) unnamed_addr #2 {
start:
  %0 = alloca [8 x i8], align 8
  %1 = getelementptr i8, ptr %source, i64 %offset
  store ptr %1, ptr %0, align 8
  %_0.i = load ptr, ptr %0, align 8
  ret ptr %_0.i
}

; extended_pilot::rust_label
; Function Attrs: noinline nounwind nonlazybind
define internal i64 @_ZN14extended_pilot10rust_label17hb5450f348c5f2ff7E(i64 %value) unnamed_addr #2 {
start:
  %_0 = alloca [8 x i8], align 8
  %0 = icmp eq i64 %value, 0
  br i1 %0, label %bb1, label %bb2

bb1:                                              ; preds = %start
  store i64 17, ptr %_0, align 8
  br label %bb3

bb2:                                              ; preds = %start
  store i64 41, ptr %_0, align 8
  br label %bb3

bb3:                                              ; preds = %bb2, %bb1
  %1 = load i64, ptr %_0, align 8
  ret i64 %1
}

; extended_pilot::rust_add16
; Function Attrs: noinline nounwind nonlazybind
define internal void @_ZN14extended_pilot10rust_add1617h0a68c57815c18a3eE(ptr sret([16 x i8]) align 1 %_0, ptr align 1 %a, ptr align 1 %b) unnamed_addr #2 {
start:
; call core::array::from_fn
  call void @_ZN4core5array7from_fn17h3afbe38aa9ab8eecE(ptr sret([16 x i8]) align 1 %_0, ptr align 1 %a, ptr align 1 %b) #14
  ret void
}

; extended_pilot::rust_add16::{{closure}}
; Function Attrs: inlinehint nounwind nonlazybind
define internal i8 @"_ZN14extended_pilot10rust_add1628_$u7b$$u7b$closure$u7d$$u7d$17hbdd83e617637f6caE"(ptr align 8 %_1, i64 %i) unnamed_addr #0 {
start:
  %_4 = icmp ult i64 %i, 16
  br i1 %_4, label %bb1, label %panic

bb1:                                              ; preds = %start
  %_7 = load ptr, ptr %_1, align 8
  %0 = getelementptr inbounds nuw i8, ptr %_7, i64 %i
  %_3 = load i8, ptr %0, align 1
  %_6 = icmp ult i64 %i, 16
  br i1 %_6, label %bb2, label %panic1

panic:                                            ; preds = %start
; call core::panicking::panic_bounds_check
  call void @_ZN4core9panicking18panic_bounds_check17hfa2ac8420ad021dcE(i64 %i, i64 16, ptr align 8 @alloc_f2c8a29a7418eb1a2322d9e36eba085f) #15
  unreachable

bb2:                                              ; preds = %bb1
  %1 = getelementptr inbounds i8, ptr %_1, i64 8
  %_8 = load ptr, ptr %1, align 8
  %2 = getelementptr inbounds nuw i8, ptr %_8, i64 %i
  %_5 = load i8, ptr %2, align 1
  %_0.i = add i8 %_3, %_5
  ret i8 %_0.i

panic1:                                           ; preds = %bb1
; call core::panicking::panic_bounds_check
  call void @_ZN4core9panicking18panic_bounds_check17hfa2ac8420ad021dcE(i64 %i, i64 16, ptr align 8 @alloc_45b90ed248e7cd080a07bdc6e70dd3a1) #15
  unreachable
}

; extended_pilot::rust_call_helper
; Function Attrs: noinline nounwind nonlazybind
define internal i64 @_ZN14extended_pilot16rust_call_helper17h4802fef1bbd0e865E(i64 %a, i64 %b) unnamed_addr #2 {
start:
  %_3 = call i64 @pilot_helper(i64 %a, i64 %b) #14
  %_0.i = add i64 %_3, 1
  ret i64 %_0.i
}

; extended_pilot::inline_carry
; Function Attrs: noinline nounwind nonlazybind
define internal { i64, i64 } @_ZN14extended_pilot12inline_carry17h27e24da72dcbbd2aE(i64 %0, i64 %b, i64 %cin) unnamed_addr #2 {
start:
  %carry = alloca [1 x i8], align 1
  %a = alloca [8 x i8], align 8
  store i64 %0, ptr %a, align 8
  %1 = load i64, ptr %a, align 8
  %2 = call { i64, i8 } asm sideeffect inteldialect "bt ${4:q}, 0\0Aadc ${0:q}, ${3:q}\0Asetc ${1}", "=&r,=q,0,r,r,~{dirflag},~{fpsr},~{flags}"(i64 %1, i64 %b, i64 %cin) #17, !srcloc !5
  %3 = extractvalue { i64, i8 } %2, 0
  store i64 %3, ptr %a, align 8
  %4 = extractvalue { i64, i8 } %2, 1
  store i8 %4, ptr %carry, align 1
  %_5 = load i64, ptr %a, align 8
  %_7 = load i8, ptr %carry, align 1
  %_0.i = zext i8 %_7 to i64
  %5 = insertvalue { i64, i64 } poison, i64 %_5, 0
  %6 = insertvalue { i64, i64 } %5, i64 %_0.i, 1
  ret { i64, i64 } %6
}

; extended_pilot::inline_label
; Function Attrs: noinline nounwind nonlazybind
define internal i64 @_ZN14extended_pilot12inline_label17hce24d0f42a259affE(i64 %value) unnamed_addr #2 {
start:
  %answer = alloca [8 x i8], align 8
  store i64 41, ptr %answer, align 8
  callbr void asm sideeffect alignstack inteldialect "test ${0:q}, ${0:q}\0Ajz ${1:l}", "r,!i,~{dirflag},~{fpsr},~{flags},~{memory}"(i64 %value)
          to label %bb1 [label %bb2], !srcloc !6

bb2:                                              ; preds = %start
  store i64 17, ptr %answer, align 8
  br label %bb1

bb1:                                              ; preds = %bb2, %start
  %_0 = load i64, ptr %answer, align 8
  ret i64 %_0
}

; extended_pilot::inline_load
; Function Attrs: noinline nounwind nonlazybind
define internal i64 @_ZN14extended_pilot11inline_load17h9d5ac2614c7daabdE(ptr %p) unnamed_addr #2 {
start:
  %out = alloca [8 x i8], align 8
  %0 = call i64 asm sideeffect inteldialect "mov ${0:q}, [${1:q}]", "=r,r,~{memory}"(ptr %p), !srcloc !7
  store i64 %0, ptr %out, align 8
  %_0 = load i64, ptr %out, align 8
  ret i64 %_0
}

; extended_pilot::inline_store
; Function Attrs: noinline nounwind nonlazybind
define internal void @_ZN14extended_pilot12inline_store17h07e83f398e5e13c5E(ptr %p, i64 %value) unnamed_addr #2 {
start:
  call void asm sideeffect inteldialect "mov [${1:q}], ${0:q}", "r,r,~{memory}"(i64 %value, ptr %p), !srcloc !8
  ret void
}

; extended_pilot::Guard16::new
; Function Attrs: nounwind nonlazybind
define internal void @_ZN14extended_pilot7Guard163new17h424d6b061fee17aaE(ptr sret([48 x i8]) align 16 %_0, ptr align 1 %data) unnamed_addr #1 {
start:
  %_3 = alloca [16 x i8], align 1
  %_2 = alloca [16 x i8], align 1
  call void @llvm.memset.p0.i64(ptr align 1 %_2, i8 -91, i64 16, i1 false)
  call void @llvm.memset.p0.i64(ptr align 1 %_3, i8 90, i64 16, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 16 %_0, ptr align 1 %_2, i64 16, i1 false)
  %0 = getelementptr inbounds i8, ptr %_0, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 16 %0, ptr align 1 %data, i64 16, i1 false)
  %1 = getelementptr inbounds i8, ptr %_0, i64 32
  call void @llvm.memcpy.p0.p0.i64(ptr align 16 %1, ptr align 1 %_3, i64 16, i1 false)
  ret void
}

; extended_pilot::Guard16::intact
; Function Attrs: nounwind nonlazybind
define internal zeroext i1 @_ZN14extended_pilot7Guard166intact17h0cc5d2cddb0349aaE(ptr align 16 %self) unnamed_addr #1 {
start:
  %_0 = alloca [1 x i8], align 1
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_2 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %self, ptr align 1 @alloc_21df5683520d569a1eb51be289b6cea3) #14
  br i1 %_2, label %bb2, label %bb3

bb3:                                              ; preds = %start
  store i8 0, ptr %_0, align 1
  br label %bb4

bb2:                                              ; preds = %start
  %_5 = getelementptr inbounds i8, ptr %self, i64 32
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %0 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %_5, ptr align 1 @alloc_2262ac44f76923e65696c0dac3b1908c) #14
  %1 = zext i1 %0 to i8
  store i8 %1, ptr %_0, align 1
  br label %bb4

bb4:                                              ; preds = %bb2, %bb3
  %2 = load i8, ptr %_0, align 1
  %3 = trunc nuw i8 %2 to i1
  ret i1 %3
}

; extended_pilot::zc_decode
; Function Attrs: noinline nounwind nonlazybind
define internal i64 @_ZN14extended_pilot9zc_decode17hf5ef34b6dafe7c79E(ptr align 1 %bytes) unnamed_addr #2 {
start:
  %0 = alloca [8 x i8], align 8
  %_4.i = alloca [8 x i8], align 1
  %_0.i = alloca [8 x i8], align 8
  %1 = alloca [8 x i8], align 8
  %self.i = alloca [8 x i8], align 1
  %2 = alloca [8 x i8], align 8
  %3 = alloca [8 x i8], align 8
  %_3 = alloca [16 x i8], align 8
  %_2 = alloca [8 x i8], align 1
; call zerocopy::FromBytes::read_from_bytes
  call void @_ZN8zerocopy9FromBytes15read_from_bytes17h7dfc2b7241a232c8E(ptr sret([16 x i8]) align 8 %_3, ptr align 1 %bytes, i64 8) #14
; call core::result::Result<T,E>::expect
  %4 = call i64 @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h570553249822f492E"(ptr align 8 %_3, ptr align 1 @alloc_8201ddbf69297838cdcfbcf366c93eb4, i64 13, ptr align 8 @alloc_174ca6095dd798f3bae55190774d0abd) #14
  store i64 %4, ptr %3, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_2, ptr align 8 %3, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %2, ptr align 1 %_2, i64 8, i1 false)
  %5 = load i64, ptr %2, align 8
  store i64 %5, ptr %1, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %self.i, ptr align 8 %1, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_4.i, ptr align 1 %self.i, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %0, ptr align 1 %_4.i, i64 8, i1 false)
  %6 = load i64, ptr %0, align 8
; call core::num::<impl u64>::from_be_bytes
  %7 = call i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$13from_be_bytes17h310cb9b2da71e482E"(i64 %6) #14
  store i64 %7, ptr %_0.i, align 8
  %8 = load i64, ptr %_0.i, align 8
  ret i64 %8
}

; extended_pilot::zc_encode
; Function Attrs: noinline nounwind nonlazybind
define internal void @_ZN14extended_pilot9zc_encode17hd42c115e91ba9f69E(i64 %value, ptr align 1 %bytes) unnamed_addr #2 {
start:
  %0 = alloca [8 x i8], align 8
  %_5.i.i = alloca [8 x i8], align 1
  %bytes.i.i = alloca [8 x i8], align 1
  %_0.i.i = alloca [8 x i8], align 1
  %1 = alloca [8 x i8], align 8
  %_3.i = alloca [8 x i8], align 1
  %2 = alloca [8 x i8], align 8
  %_5.i = alloca [8 x i8], align 1
  %bytes.i = alloca [8 x i8], align 1
  %_0.i = alloca [8 x i8], align 1
  %3 = alloca [8 x i8], align 8
  %wire = alloca [8 x i8], align 1
; call core::num::<impl u64>::to_be_bytes
  %4 = call i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$11to_be_bytes17h763c5b251a6c665cE"(i64 0) #14
  store i64 %4, ptr %2, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %bytes.i, ptr align 8 %2, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_5.i, ptr align 1 %bytes.i, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0.i, ptr align 1 %_5.i, i64 8, i1 false)
  %5 = load i64, ptr %_0.i, align 1
  store i64 %5, ptr %3, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %wire, ptr align 8 %3, i64 8, i1 false)
; call core::num::<impl u64>::to_be_bytes
  %6 = call i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$11to_be_bytes17h763c5b251a6c665cE"(i64 %value) #14
  store i64 %6, ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %bytes.i.i, ptr align 8 %0, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_5.i.i, ptr align 1 %bytes.i.i, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0.i.i, ptr align 1 %_5.i.i, i64 8, i1 false)
  %7 = load i64, ptr %_0.i.i, align 1
  store i64 %7, ptr %1, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_3.i, ptr align 8 %1, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %wire, ptr align 1 %_3.i, i64 8, i1 false)
; call zerocopy::IntoBytes::write_to
  %_7 = call align 1 ptr @_ZN8zerocopy9IntoBytes8write_to17h333dd8283fe0b02eE(ptr align 1 %wire, ptr align 1 %bytes, i64 8) #14
; call core::result::Result<T,E>::expect
  call void @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h58a6929434be20e0E"(ptr align 1 %_7, ptr align 1 @alloc_561d3d4073b7782336f3422149c0c11e, i64 18, ptr align 8 @alloc_e663c9224e057f8bb5f411b30ae6c7c8) #14
  ret void
}

; extended_pilot::zc_copy16
; Function Attrs: noinline nounwind nonlazybind
define internal void @_ZN14extended_pilot9zc_copy1617h333cef0da883ee38E(ptr align 1 %source, ptr align 1 %dst) unnamed_addr #2 {
start:
  %_4 = alloca [24 x i8], align 8
  %copy = alloca [16 x i8], align 1
; call zerocopy::FromBytes::read_from_bytes
  call void @_ZN8zerocopy9FromBytes15read_from_bytes17hb75740783c564722E(ptr sret([24 x i8]) align 8 %_4, ptr align 1 %source, i64 16) #14
; call core::result::Result<T,E>::expect
  call void @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h8081aa36d77a1c7eE"(ptr sret([16 x i8]) align 1 %copy, ptr align 8 %_4, ptr align 1 @alloc_5dee763f4f60d547e9365f94454ebd3a, i64 14, ptr align 8 @alloc_6abd98a2cd140a8e8b20b1b8921e0cf0) #14
; call zerocopy::IntoBytes::write_to
  %_8 = call align 1 ptr @_ZN8zerocopy9IntoBytes8write_to17h50ba8809e39be976E(ptr align 1 %copy, ptr align 1 %dst, i64 16) #14
; call core::result::Result<T,E>::expect
  call void @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h250be7b870b5ab1fE"(ptr align 1 %_8, ptr align 1 @alloc_c4acb29d339694a0db93fd511b0aa138, i64 19, ptr align 8 @alloc_5b1f55ab60e406fbd3eb1e254aed020b) #14
  ret void
}

; extended_pilot::check
; Function Attrs: nounwind nonlazybind
define internal void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %ok, ptr align 1 %0, i64 %1, ptr align 8 %2) unnamed_addr #1 {
start:
  %_11 = alloca [16 x i8], align 8
  %_10 = alloca [16 x i8], align 8
  %args1 = alloca [32 x i8], align 8
  %args = alloca [16 x i8], align 8
  %_5 = alloca [48 x i8], align 8
  %count = alloca [8 x i8], align 8
  %what = alloca [16 x i8], align 8
  store ptr %0, ptr %what, align 8
  %3 = getelementptr inbounds i8, ptr %what, i64 8
  store i64 %1, ptr %3, align 8
  store ptr %2, ptr %count, align 8
  br i1 %ok, label %bb6, label %bb1

bb1:                                              ; preds = %start
  store ptr %what, ptr %args, align 8
  %4 = getelementptr inbounds i8, ptr %args, i64 8
  store ptr %count, ptr %4, align 8
  %_16 = load ptr, ptr %args, align 8
; call core::fmt::rt::Argument::new_display
  call void @_ZN4core3fmt2rt8Argument11new_display17h17ee8a6fae403bc4E(ptr sret([16 x i8]) align 8 %_10, ptr align 8 %_16) #14
  %5 = getelementptr inbounds i8, ptr %args, i64 8
  %_17 = load ptr, ptr %5, align 8
; call core::fmt::rt::Argument::new_display
  call void @_ZN4core3fmt2rt8Argument11new_display17hfb13677ee243d15eE(ptr sret([16 x i8]) align 8 %_11, ptr align 8 %_17) #14
  %6 = getelementptr inbounds nuw %"core::fmt::rt::Argument<'_>", ptr %args1, i64 0
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %6, ptr align 8 %_10, i64 16, i1 false)
  %7 = getelementptr inbounds nuw %"core::fmt::rt::Argument<'_>", ptr %args1, i64 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %7, ptr align 8 %_11, i64 16, i1 false)
; call core::fmt::rt::<impl core::fmt::Arguments>::new_v1
  call void @"_ZN4core3fmt2rt38_$LT$impl$u20$core..fmt..Arguments$GT$6new_v117haf3e53cd4fb6e77eE"(ptr sret([48 x i8]) align 8 %_5, ptr align 8 @alloc_81515a03d1756c347036b25cb9acf81a, ptr align 8 %args1) #14
; call std::io::stdio::_eprint
  call void @_ZN3std2io5stdio7_eprint17h58458461bd19d139E(ptr align 8 %_5) #14
; call std::process::exit
  call void @_ZN3std7process4exit17h00460fefcf032948E(i32 2) #15
  unreachable

bb6:                                              ; preds = %start
  %8 = load ptr, ptr %count, align 8
  %9 = load i64, ptr %8, align 8
  %10 = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %9, i64 1)
  %_15.0 = extractvalue { i64, i1 } %10, 0
  %_15.1 = extractvalue { i64, i1 } %10, 1
  br i1 %_15.1, label %panic, label %bb7

bb7:                                              ; preds = %bb6
  %11 = load ptr, ptr %count, align 8
  store i64 %_15.0, ptr %11, align 8
  ret void

panic:                                            ; preds = %bb6
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_add_overflow17h371a9588e01a5f2aE(ptr align 8 @alloc_87b55dc4e757b81e4ee925b5b00b364d) #15
  unreachable
}

; extended_pilot::main
; Function Attrs: nounwind nonlazybind
define internal void @_ZN14extended_pilot4main17hca72231bfee5693fE() unnamed_addr #1 {
start:
  %0 = alloca [8 x i8], align 8
  %_5.i = alloca [8 x i8], align 1
  %bytes.i = alloca [8 x i8], align 1
  %_0.i48 = alloca [8 x i8], align 1
  %1 = alloca [8 x i8], align 8
  %2 = alloca [8 x i8], align 8
  %3 = alloca [8 x i8], align 8
  %4 = alloca [6936 x i8], align 8
  %5 = alloca [4608 x i8], align 8
  %6 = alloca [192 x i8], align 1
  %7 = alloca [136 x i8], align 8
  %8 = alloca [272 x i8], align 8
  %9 = alloca [23120 x i8], align 8
  %10 = alloca [8064 x i8], align 8
  %11 = alloca [9248 x i8], align 8
  %_593 = alloca [16 x i8], align 8
  %_592 = alloca [16 x i8], align 8
  %args20 = alloca [32 x i8], align 8
  %args = alloca [16 x i8], align 8
  %_587 = alloca [48 x i8], align 8
  %result = alloca [8 x i8], align 8
  %wire = alloca [8 x i8], align 1
  %dst19 = alloca [9 x i8], align 1
  %_562 = alloca [16 x i8], align 8
  %source18 = alloca [9 x i8], align 1
  %_554 = alloca [16 x i8], align 8
  %iter17 = alloca [32 x i8], align 8
  %_552 = alloca [16 x i8], align 8
  %_551 = alloca [32 x i8], align 8
  %_548 = alloca [1 x i8], align 1
  %_538 = alloca [1 x i8], align 1
  %_533 = alloca [1 x i8], align 1
  %_523 = alloca [1 x i8], align 1
  %_520 = alloca [1 x i8], align 1
  %_512 = alloca [32 x i8], align 8
  %iter16 = alloca [6952 x i8], align 8
  %_510 = alloca [6952 x i8], align 8
  %_494 = alloca [1 x i8], align 1
  %_485 = alloca [1 x i8], align 1
  %baseline15 = alloca [16 x i8], align 1
  %_452 = alloca [1 x i8], align 1
  %b_ptr14 = alloca [8 x i8], align 8
  %_444 = alloca [16 x i8], align 1
  %out13 = alloca [48 x i8], align 16
  %_441 = alloca [192 x i8], align 1
  %_440 = alloca [16 x i8], align 1
  %b12 = alloca [48 x i8], align 16
  %_437 = alloca [192 x i8], align 1
  %_436 = alloca [16 x i8], align 1
  %a11 = alloca [48 x i8], align 16
  %expected = alloca [16 x i8], align 1
  %_429 = alloca [40 x i8], align 8
  %iter10 = alloca [4624 x i8], align 8
  %_427 = alloca [4624 x i8], align 8
  %_421 = alloca [1 x i8], align 1
  %_408 = alloca [16 x i8], align 8
  %iter9 = alloca [24 x i8], align 8
  %_406 = alloca [24 x i8], align 8
  %_405 = alloca [24 x i8], align 8
  %_392 = alloca [24 x i8], align 8
  %_376 = alloca [1 x i8], align 1
  %_361 = alloca [1 x i8], align 1
  %_319 = alloca [1 x i8], align 1
  %_317 = alloca [16 x i8], align 1
  %baseline8 = alloca [48 x i8], align 16
  %_315 = alloca [16 x i8], align 1
  %zc = alloca [48 x i8], align 16
  %_313 = alloca [16 x i8], align 1
  %simd = alloca [48 x i8], align 16
  %_311 = alloca [16 x i8], align 1
  %scalar = alloca [48 x i8], align 16
  %_309 = alloca [16 x i8], align 1
  %source7 = alloca [48 x i8], align 16
  %bytes = alloca [16 x i8], align 1
  %_304 = alloca [17 x i8], align 1
  %iter6 = alloca [208 x i8], align 8
  %_302 = alloca [208 x i8], align 8
  %_299 = alloca [8 x i8], align 8
  %_294 = alloca [1 x i8], align 1
  %baseline = alloca [24 x i8], align 8
  %_267 = alloca [24 x i8], align 8
  %_247 = alloca [24 x i8], align 8
  %_229 = alloca [24 x i8], align 8
  %_219 = alloca [1 x i8], align 1
  %dst = alloca [24 x i8], align 8
  %source = alloca [24 x i8], align 8
  %_190 = alloca [16 x i8], align 8
  %iter5 = alloca [152 x i8], align 8
  %_188 = alloca [152 x i8], align 8
  %_180 = alloca [16 x i8], align 8
  %_174 = alloca [8 x i8], align 1
  %_168 = alloca [8 x i8], align 1
  %_164 = alloca [1 x i8], align 1
  %encoded = alloca [8 x i8], align 1
  %_145 = alloca [24 x i8], align 8
  %iter4 = alloca [288 x i8], align 8
  %_143 = alloca [288 x i8], align 8
  %_140 = alloca [16 x i8], align 8
  %_138 = alloca [16 x i8], align 8
  %_132 = alloca [16 x i8], align 8
  %_130 = alloca [16 x i8], align 8
  %_115 = alloca [48 x i8], align 8
  %iter3 = alloca [23136 x i8], align 8
  %_113 = alloca [23136 x i8], align 8
  %_110 = alloca [24 x i8], align 8
  %_106 = alloca [24 x i8], align 8
  %_94 = alloca [32 x i8], align 8
  %_90 = alloca [1 x i8], align 1
  %b_ptr = alloca [8 x i8], align 8
  %out2 = alloca [32 x i8], align 8
  %b = alloca [16 x i8], align 8
  %a = alloca [16 x i8], align 8
  %_54 = alloca [64 x i8], align 8
  %iter1 = alloca [8080 x i8], align 8
  %_52 = alloca [8080 x i8], align 8
  %_49 = alloca [16 x i8], align 8
  %_47 = alloca [16 x i8], align 8
  %_35 = alloca [32 x i8], align 8
  %out = alloca [32 x i8], align 8
  %_12 = alloca [40 x i8], align 8
  %iter = alloca [9264 x i8], align 8
  %_10 = alloca [9264 x i8], align 8
  %sentinels = alloca [16 x i8], align 8
  %_3 = alloca [1 x i8], align 1
  %checks = alloca [8 x i8], align 8
  store i64 0, ptr %checks, align 8
  %12 = icmp eq i64 48, 48
  br i1 %12, label %bb2, label %bb5

bb2:                                              ; preds = %start
  %13 = icmp eq i64 16, 16
  br i1 %13, label %bb4, label %bb5

bb5:                                              ; preds = %bb2, %start
  store i8 0, ptr %_3, align 1
  br label %bb6

bb4:                                              ; preds = %bb2
  store i8 1, ptr %_3, align 1
  br label %bb6

bb6:                                              ; preds = %bb5, %bb4
  %14 = load i8, ptr %_3, align 1
  %15 = trunc nuw i8 %14 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %15, ptr align 1 @alloc_e74c78967c49fe173e1453708be77ccf, i64 12, ptr align 8 %checks) #14
  %16 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  store i64 1234605616436508552, ptr %16, align 8
  %17 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  store i64 -8613303245920329199, ptr %17, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %11, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.3, i64 9248, i1 false)
; call core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
  call void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17h743bdf75d6c2515cE"(ptr sret([9264 x i8]) align 8 %_10, ptr align 8 %11) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %iter, ptr align 8 %_10, i64 9264, i1 false)
  br label %bb9

bb9:                                              ; preds = %bb12, %bb6
; call <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
  call void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17ha81cec4ae52ac598E"(ptr sret([40 x i8]) align 8 %_12, ptr align 8 %iter) #14
  %_14 = load i64, ptr %_12, align 8
  %18 = trunc nuw i64 %_14 to i1
  br i1 %18, label %bb12, label %bb13

bb12:                                             ; preds = %bb9
  %19 = getelementptr inbounds i8, ptr %_12, i64 8
  %20 = getelementptr inbounds nuw i64, ptr %19, i64 0
  %a37 = load i64, ptr %20, align 8
  %21 = getelementptr inbounds i8, ptr %_12, i64 8
  %22 = getelementptr inbounds nuw i64, ptr %21, i64 1
  %b38 = load i64, ptr %22, align 8
  %23 = getelementptr inbounds i8, ptr %_12, i64 8
  %24 = getelementptr inbounds nuw i64, ptr %23, i64 2
  %low39 = load i64, ptr %24, align 8
  %25 = getelementptr inbounds i8, ptr %_12, i64 8
  %26 = getelementptr inbounds nuw i64, ptr %25, i64 3
  %high40 = load i64, ptr %26, align 8
  %27 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  %_20 = load i64, ptr %27, align 8
  %28 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  %_23 = load i64, ptr %28, align 8
  %29 = getelementptr inbounds nuw i64, ptr %out, i64 0
  store i64 %_20, ptr %29, align 8
  %30 = getelementptr inbounds nuw i64, ptr %out, i64 1
  store i64 0, ptr %30, align 8
  %31 = getelementptr inbounds nuw i64, ptr %out, i64 2
  store i64 0, ptr %31, align 8
  %32 = getelementptr inbounds nuw i64, ptr %out, i64 3
  store i64 %_23, ptr %32, align 8
  %_0.i41 = getelementptr inbounds nuw i64, ptr %out, i64 1
  call void @pilot_mul(i64 %a37, i64 %b38, ptr %_0.i41) #14
  %33 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  %_36 = load i64, ptr %33, align 8
  %34 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  %_39 = load i64, ptr %34, align 8
  %35 = getelementptr inbounds nuw i64, ptr %_35, i64 0
  store i64 %_36, ptr %35, align 8
  %36 = getelementptr inbounds nuw i64, ptr %_35, i64 1
  store i64 %low39, ptr %36, align 8
  %37 = getelementptr inbounds nuw i64, ptr %_35, i64 2
  store i64 %high40, ptr %37, align 8
  %38 = getelementptr inbounds nuw i64, ptr %_35, i64 3
  store i64 %_39, ptr %38, align 8
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_32 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h6d8e9898dd9d4c85E"(ptr align 8 %out, ptr align 8 %_35) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_32, ptr align 1 @alloc_46d4440e7a9abba00851fd9bc6521d38, i64 7, ptr align 8 %checks) #14
; call extended_pilot::rust_mul
  %39 = call { i64, i64 } @_ZN14extended_pilot8rust_mul17h23452971b31aa446E(i64 %a37, i64 %b38) #14
  %40 = extractvalue { i64, i64 } %39, 0
  %41 = extractvalue { i64, i64 } %39, 1
  store i64 %40, ptr %_47, align 8
  %42 = getelementptr inbounds i8, ptr %_47, i64 8
  store i64 %41, ptr %42, align 8
  store i64 %low39, ptr %_49, align 8
  %43 = getelementptr inbounds i8, ptr %_49, i64 8
  store i64 %high40, ptr %43, align 8
; call core::tuple::<impl core::cmp::PartialEq for (U,T)>::eq
  %_45 = call zeroext i1 @"_ZN4core5tuple64_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$$LP$U$C$T$RP$$GT$2eq17h3c9f146d4a7f7867E"(ptr align 8 %_47, ptr align 8 %_49) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_45, ptr align 1 @alloc_ad3f71f8fadccdea3aae76bb9fc6967b, i64 8, ptr align 8 %checks) #14
  br label %bb9

bb13:                                             ; preds = %bb9
; call core::ptr::drop_in_place<core::array::iter::IntoIter<[u64; 4],289_usize>>
  call void @"_ZN4core3ptr92drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u64$u3b$$u20$4$u5d$$C$289_usize$GT$$GT$17ha871b6e048fae9c7E"(ptr align 8 %iter) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %10, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.4, i64 8064, i1 false)
; call core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
  call void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17h0dac118a2232d692E"(ptr sret([8080 x i8]) align 8 %_52, ptr align 8 %10) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %iter1, ptr align 8 %_52, i64 8080, i1 false)
  br label %bb27

bb27:                                             ; preds = %bb46, %bb13
; call <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
  call void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h4cf0f7b71d3c67a4E"(ptr sret([64 x i8]) align 8 %_54, ptr align 8 %iter1) #14
  %_56 = load i64, ptr %_54, align 8
  %44 = trunc nuw i64 %_56 to i1
  br i1 %44, label %bb29, label %bb30

bb29:                                             ; preds = %bb27
  %45 = getelementptr inbounds i8, ptr %_54, i64 8
  %46 = getelementptr inbounds nuw i64, ptr %45, i64 0
  %al = load i64, ptr %46, align 8
  %47 = getelementptr inbounds i8, ptr %_54, i64 8
  %48 = getelementptr inbounds nuw i64, ptr %47, i64 1
  %ah = load i64, ptr %48, align 8
  %49 = getelementptr inbounds i8, ptr %_54, i64 8
  %50 = getelementptr inbounds nuw i64, ptr %49, i64 2
  %bl = load i64, ptr %50, align 8
  %51 = getelementptr inbounds i8, ptr %_54, i64 8
  %52 = getelementptr inbounds nuw i64, ptr %51, i64 3
  %bh = load i64, ptr %52, align 8
  %53 = getelementptr inbounds i8, ptr %_54, i64 8
  %54 = getelementptr inbounds nuw i64, ptr %53, i64 4
  %low35 = load i64, ptr %54, align 8
  %55 = getelementptr inbounds i8, ptr %_54, i64 8
  %56 = getelementptr inbounds nuw i64, ptr %55, i64 5
  %high = load i64, ptr %56, align 8
  %57 = getelementptr inbounds i8, ptr %_54, i64 8
  %58 = getelementptr inbounds nuw i64, ptr %57, i64 6
  %carry36 = load i64, ptr %58, align 8
  %59 = getelementptr inbounds nuw i64, ptr %a, i64 0
  store i64 %al, ptr %59, align 8
  %60 = getelementptr inbounds nuw i64, ptr %a, i64 1
  store i64 %ah, ptr %60, align 8
  %61 = getelementptr inbounds nuw i64, ptr %b, i64 0
  store i64 %bl, ptr %61, align 8
  %62 = getelementptr inbounds nuw i64, ptr %b, i64 1
  store i64 %bh, ptr %62, align 8
  %63 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  %_67 = load i64, ptr %63, align 8
  %64 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  %_70 = load i64, ptr %64, align 8
  %65 = getelementptr inbounds nuw i64, ptr %out2, i64 0
  store i64 %_67, ptr %65, align 8
  %66 = getelementptr inbounds nuw i64, ptr %out2, i64 1
  store i64 0, ptr %66, align 8
  %67 = getelementptr inbounds nuw i64, ptr %out2, i64 2
  store i64 0, ptr %67, align 8
  %68 = getelementptr inbounds nuw i64, ptr %out2, i64 3
  store i64 %_70, ptr %68, align 8
  %_74 = icmp eq i64 %al, %bl
  br i1 %_74, label %bb33, label %bb35

bb30:                                             ; preds = %bb27
; call core::ptr::drop_in_place<core::array::iter::IntoIter<[u64; 7],144_usize>>
  call void @"_ZN4core3ptr92drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u64$u3b$$u20$7$u5d$$C$144_usize$GT$$GT$17hbc817a1e405b13e9E"(ptr align 8 %iter1) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %9, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.5, i64 23120, i1 false)
; call core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
  call void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17ha5f4d59370b62cd9E"(ptr sret([23136 x i8]) align 8 %_113, ptr align 8 %9) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %iter3, ptr align 8 %_113, i64 23136, i1 false)
  br label %bb52

bb52:                                             ; preds = %bb54, %bb30
; call <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
  call void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17hb3a617123b21ed31E"(ptr sret([48 x i8]) align 8 %_115, ptr align 8 %iter3) #14
  %_117 = load i64, ptr %_115, align 8
  %69 = trunc nuw i64 %_117 to i1
  br i1 %69, label %bb54, label %bb55

bb54:                                             ; preds = %bb52
  %70 = getelementptr inbounds i8, ptr %_115, i64 8
  %71 = getelementptr inbounds nuw i64, ptr %70, i64 0
  %a33 = load i64, ptr %71, align 8
  %72 = getelementptr inbounds i8, ptr %_115, i64 8
  %73 = getelementptr inbounds nuw i64, ptr %72, i64 1
  %b34 = load i64, ptr %73, align 8
  %74 = getelementptr inbounds i8, ptr %_115, i64 8
  %75 = getelementptr inbounds nuw i64, ptr %74, i64 2
  %cin = load i64, ptr %75, align 8
  %76 = getelementptr inbounds i8, ptr %_115, i64 8
  %77 = getelementptr inbounds nuw i64, ptr %76, i64 3
  %low = load i64, ptr %77, align 8
  %78 = getelementptr inbounds i8, ptr %_115, i64 8
  %79 = getelementptr inbounds nuw i64, ptr %78, i64 4
  %carry = load i64, ptr %79, align 8
  %_124 = icmp ule i64 %cin, 1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_124, ptr align 1 @alloc_149d364d8349edfe71770e753c396aa0, i64 12, ptr align 8 %checks) #14
; call extended_pilot::inline_carry
  %80 = call { i64, i64 } @_ZN14extended_pilot12inline_carry17h27e24da72dcbbd2aE(i64 %a33, i64 %b34, i64 %cin) #14
  %81 = extractvalue { i64, i64 } %80, 0
  %82 = extractvalue { i64, i64 } %80, 1
  store i64 %81, ptr %_130, align 8
  %83 = getelementptr inbounds i8, ptr %_130, i64 8
  store i64 %82, ptr %83, align 8
  store i64 %low, ptr %_132, align 8
  %84 = getelementptr inbounds i8, ptr %_132, i64 8
  store i64 %carry, ptr %84, align 8
; call core::tuple::<impl core::cmp::PartialEq for (U,T)>::eq
  %_128 = call zeroext i1 @"_ZN4core5tuple64_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$$LP$U$C$T$RP$$GT$2eq17h3c9f146d4a7f7867E"(ptr align 8 %_130, ptr align 8 %_132) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_128, ptr align 1 @alloc_b3cea492701bfda0e383697982d6e842, i64 12, ptr align 8 %checks) #14
; call extended_pilot::rust_carry
  %85 = call { i64, i64 } @_ZN14extended_pilot10rust_carry17hcd557fb1e0beef8aE(i64 %a33, i64 %b34, i64 %cin) #14
  %86 = extractvalue { i64, i64 } %85, 0
  %87 = extractvalue { i64, i64 } %85, 1
  store i64 %86, ptr %_138, align 8
  %88 = getelementptr inbounds i8, ptr %_138, i64 8
  store i64 %87, ptr %88, align 8
  store i64 %low, ptr %_140, align 8
  %89 = getelementptr inbounds i8, ptr %_140, i64 8
  store i64 %carry, ptr %89, align 8
; call core::tuple::<impl core::cmp::PartialEq for (U,T)>::eq
  %_136 = call zeroext i1 @"_ZN4core5tuple64_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$$LP$U$C$T$RP$$GT$2eq17h3c9f146d4a7f7867E"(ptr align 8 %_138, ptr align 8 %_140) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_136, ptr align 1 @alloc_2c6e6fe2dd10fb5e3112086a381bbd92, i64 10, ptr align 8 %checks) #14
  br label %bb52

bb55:                                             ; preds = %bb52
; call core::ptr::drop_in_place<core::array::iter::IntoIter<[u64; 5],578_usize>>
  call void @"_ZN4core3ptr92drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u64$u3b$$u20$5$u5d$$C$578_usize$GT$$GT$17h398570afd82295f4E"(ptr align 8 %iter3) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %8, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.6, i64 272, i1 false)
; call core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
  call void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17hae2a0c71c360f183E"(ptr sret([288 x i8]) align 8 %_143, ptr align 8 %8) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %iter4, ptr align 8 %_143, i64 288, i1 false)
  br label %bb64

bb64:                                             ; preds = %bb78, %bb55
; call <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
  call void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h765e1cfb9add1435E"(ptr sret([24 x i8]) align 8 %_145, ptr align 8 %iter4) #14
  %_147 = load i64, ptr %_145, align 8
  %90 = trunc nuw i64 %_147 to i1
  br i1 %90, label %bb66, label %bb67

bb66:                                             ; preds = %bb64
  %91 = getelementptr inbounds i8, ptr %_145, i64 8
  %92 = getelementptr inbounds nuw i64, ptr %91, i64 0
  %x31 = load i64, ptr %92, align 8
  %93 = getelementptr inbounds i8, ptr %_145, i64 8
  %94 = getelementptr inbounds nuw i64, ptr %93, i64 1
  %expected32 = load i64, ptr %94, align 8
  %_152 = call i64 @pilot_bswap(i64 %x31) #14
  %_151 = icmp eq i64 %_152, %expected32
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_151, ptr align 1 @alloc_0d1d49781481982934645de3da0719d5, i64 8, ptr align 8 %checks) #14
; call extended_pilot::rust_swap
  %_157 = call i64 @_ZN14extended_pilot9rust_swap17hb3a8b149d95298c4E(i64 %x31) #14
  %_156 = icmp eq i64 %_157, %expected32
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_156, ptr align 1 @alloc_2113db9752c8b12eb5687084ee02e22c, i64 9, ptr align 8 %checks) #14
  call void @llvm.memset.p0.i64(ptr align 1 %encoded, i8 0, i64 8, i1 false)
; call extended_pilot::zc_encode
  call void @_ZN14extended_pilot9zc_encode17hd42c115e91ba9f69E(i64 %x31, ptr align 1 %encoded) #14
; call core::num::<impl u64>::to_be_bytes
  %95 = call i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$11to_be_bytes17h763c5b251a6c665cE"(i64 %x31) #14
  store i64 %95, ptr %2, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_168, ptr align 8 %2, i64 8, i1 false)
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_165 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h271358e2f5dffc76E"(ptr align 1 %encoded, ptr align 1 %_168) #14
  br i1 %_165, label %bb75, label %bb76

bb67:                                             ; preds = %bb64
; call core::ptr::drop_in_place<core::array::iter::IntoIter<[u64; 2],17_usize>>
  call void @"_ZN4core3ptr91drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u64$u3b$$u20$2$u5d$$C$17_usize$GT$$GT$17hdc3c237a1461c403E"(ptr align 8 %iter4) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %7, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.7, i64 136, i1 false)
; call core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
  call void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17h89910c6c1c61791aE"(ptr sret([152 x i8]) align 8 %_188, ptr align 8 %7) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %iter5, ptr align 8 %_188, i64 152, i1 false)
  br label %bb86

bb86:                                             ; preds = %bb139, %bb67
; call <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
  %96 = call { i64, i64 } @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17ha251e644709270caE"(ptr align 8 %iter5) #14
  %97 = extractvalue { i64, i64 } %96, 0
  %98 = extractvalue { i64, i64 } %96, 1
  store i64 %97, ptr %_190, align 8
  %99 = getelementptr inbounds i8, ptr %_190, i64 8
  store i64 %98, ptr %99, align 8
  %_192 = load i64, ptr %_190, align 8
  %100 = getelementptr inbounds i8, ptr %_190, i64 8
  %101 = load i64, ptr %100, align 8
  %102 = trunc nuw i64 %_192 to i1
  br i1 %102, label %bb88, label %bb89

bb88:                                             ; preds = %bb86
  %103 = getelementptr inbounds i8, ptr %_190, i64 8
  %x = load i64, ptr %103, align 8
  %104 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  %_195 = load i64, ptr %104, align 8
  %105 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  %_198 = load i64, ptr %105, align 8
  %106 = getelementptr inbounds nuw i64, ptr %source, i64 0
  store i64 %_195, ptr %106, align 8
  %107 = getelementptr inbounds nuw i64, ptr %source, i64 1
  store i64 %x, ptr %107, align 8
  %108 = getelementptr inbounds nuw i64, ptr %source, i64 2
  store i64 %_198, ptr %108, align 8
  %109 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  %_202 = load i64, ptr %109, align 8
  %110 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  %_205 = load i64, ptr %110, align 8
  %111 = getelementptr inbounds nuw i64, ptr %dst, i64 0
  store i64 %_202, ptr %111, align 8
  %112 = getelementptr inbounds nuw i64, ptr %dst, i64 1
  store i64 0, ptr %112, align 8
  %113 = getelementptr inbounds nuw i64, ptr %dst, i64 2
  store i64 %_205, ptr %113, align 8
  %_0.i46 = getelementptr inbounds nuw i64, ptr %source, i64 1
  %a29 = call i64 @pilot_load(ptr %_0.i46) #14
  %_0.i45 = getelementptr inbounds nuw i64, ptr %source, i64 1
; call extended_pilot::inline_load
  %b30 = call i64 @_ZN14extended_pilot11inline_load17h9d5ac2614c7daabdE(ptr %_0.i45) #14
  %_220 = icmp eq i64 %a29, %x
  br i1 %_220, label %bb100, label %bb105

bb89:                                             ; preds = %bb86
; call core::ptr::drop_in_place<core::array::iter::IntoIter<u64,17_usize>>
  call void @"_ZN4core3ptr70drop_in_place$LT$core..array..iter..IntoIter$LT$u64$C$17_usize$GT$$GT$17ha7750d7bc5ccc23fE"(ptr align 8 %iter5) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %6, ptr align 1 @alloc_df49633132bd0738f71b84ee1e58fda5, i64 192, i1 false)
; call core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
  call void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17h0ff281db88122b47E"(ptr sret([208 x i8]) align 8 %_302, ptr align 1 %6) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %iter6, ptr align 8 %_302, i64 208, i1 false)
  br label %bb142

bb142:                                            ; preds = %bb199, %bb89
; call <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
  call void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h73063a66b0101d33E"(ptr sret([17 x i8]) align 1 %_304, ptr align 8 %iter6) #14
  %114 = load i8, ptr %_304, align 1
  %115 = trunc nuw i8 %114 to i1
  %_306 = zext i1 %115 to i64
  %116 = trunc nuw i64 %_306 to i1
  br i1 %116, label %bb144, label %bb145

bb144:                                            ; preds = %bb142
  %117 = getelementptr inbounds i8, ptr %_304, i64 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %bytes, ptr align 1 %117, i64 16, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_309, ptr align 1 %bytes, i64 16, i1 false)
; call extended_pilot::Guard16::new
  call void @_ZN14extended_pilot7Guard163new17h424d6b061fee17aaE(ptr sret([48 x i8]) align 16 %source7, ptr align 1 %_309) #14
  call void @llvm.memset.p0.i64(ptr align 1 %_311, i8 -52, i64 16, i1 false)
; call extended_pilot::Guard16::new
  call void @_ZN14extended_pilot7Guard163new17h424d6b061fee17aaE(ptr sret([48 x i8]) align 16 %scalar, ptr align 1 %_311) #14
  call void @llvm.memset.p0.i64(ptr align 1 %_313, i8 -52, i64 16, i1 false)
; call extended_pilot::Guard16::new
  call void @_ZN14extended_pilot7Guard163new17h424d6b061fee17aaE(ptr sret([48 x i8]) align 16 %simd, ptr align 1 %_313) #14
  call void @llvm.memset.p0.i64(ptr align 1 %_315, i8 -52, i64 16, i1 false)
; call extended_pilot::Guard16::new
  call void @_ZN14extended_pilot7Guard163new17h424d6b061fee17aaE(ptr sret([48 x i8]) align 16 %zc, ptr align 1 %_315) #14
  call void @llvm.memset.p0.i64(ptr align 1 %_317, i8 -52, i64 16, i1 false)
; call extended_pilot::Guard16::new
  call void @_ZN14extended_pilot7Guard163new17h424d6b061fee17aaE(ptr sret([48 x i8]) align 16 %baseline8, ptr align 1 %_317) #14
  %_324 = getelementptr inbounds i8, ptr %source7, i64 16
  %_321 = ptrtoint ptr %_324 to i64
  %_320 = urem i64 %_321, 16
  %118 = icmp eq i64 %_320, 0
  br i1 %118, label %bb153, label %bb157

bb145:                                            ; preds = %bb142
; call core::ptr::drop_in_place<core::array::iter::IntoIter<[u8; 16],12_usize>>
  call void @"_ZN4core3ptr91drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u8$u3b$$u20$16$u5d$$C$12_usize$GT$$GT$17hb357102e7eaa006aE"(ptr align 8 %iter6) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %5, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.8, i64 4608, i1 false)
; call core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
  call void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17ha80ce2e88a3efc4cE"(ptr sret([4624 x i8]) align 8 %_427, ptr align 8 %5) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %iter10, ptr align 8 %_427, i64 4624, i1 false)
  br label %bb212

bb212:                                            ; preds = %bb255, %bb145
; call <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
  call void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17ha4f8e32da9056a90E"(ptr sret([40 x i8]) align 8 %_429, ptr align 8 %iter10) #14
  %_431 = load i64, ptr %_429, align 8
  %119 = trunc nuw i64 %_431 to i1
  br i1 %119, label %bb214, label %bb215

bb214:                                            ; preds = %bb212
  %120 = getelementptr inbounds i8, ptr %_429, i64 8
  %ai = load i64, ptr %120, align 8
  %121 = getelementptr inbounds i8, ptr %_429, i64 8
  %122 = getelementptr inbounds i8, ptr %121, i64 8
  %bi = load i64, ptr %122, align 8
  %123 = getelementptr inbounds i8, ptr %_429, i64 8
  %124 = getelementptr inbounds i8, ptr %123, i64 16
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %expected, ptr align 8 %124, i64 16, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_437, ptr align 1 @alloc_df49633132bd0738f71b84ee1e58fda5, i64 192, i1 false)
  %_438 = icmp ult i64 %ai, 12
  br i1 %_438, label %bb216, label %panic

bb215:                                            ; preds = %bb212
; call core::ptr::drop_in_place<core::array::iter::IntoIter<(usize,usize,[u8; 16]),144_usize>>
  call void @"_ZN4core3ptr116drop_in_place$LT$core..array..iter..IntoIter$LT$$LP$usize$C$usize$C$$u5b$u8$u3b$$u20$16$u5d$$RP$$C$144_usize$GT$$GT$17h4bd794b93b0579dcE"(ptr align 8 %iter10) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %4, ptr align 8 @anon.c68ad90a3a9dfb7a47f86997a7ce991b.9, i64 6936, i1 false)
; call core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
  call void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17h44e26c08a95e2df0E"(ptr sret([6952 x i8]) align 8 %_510, ptr align 8 %4) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %iter16, ptr align 8 %_510, i64 6952, i1 false)
  br label %bb258

bb258:                                            ; preds = %bb268, %bb215
; call <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
  call void @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h114ac4c20ee5a3a0E"(ptr sret([32 x i8]) align 8 %_512, ptr align 8 %iter16) #14
  %_514 = load i64, ptr %_512, align 8
  %125 = trunc nuw i64 %_514 to i1
  br i1 %125, label %bb260, label %bb261

bb260:                                            ; preds = %bb258
  %126 = getelementptr inbounds i8, ptr %_512, i64 8
  %127 = getelementptr inbounds nuw i64, ptr %126, i64 0
  %a21 = load i64, ptr %127, align 8
  %128 = getelementptr inbounds i8, ptr %_512, i64 8
  %129 = getelementptr inbounds nuw i64, ptr %128, i64 1
  %b22 = load i64, ptr %129, align 8
  %130 = getelementptr inbounds i8, ptr %_512, i64 8
  %131 = getelementptr inbounds nuw i64, ptr %130, i64 2
  %expected23 = load i64, ptr %131, align 8
  store i8 0, ptr %_520, align 1
  %132 = load i8, ptr %_520, align 1
; call core::sync::atomic::AtomicUsize::store
  call void @_ZN4core4sync6atomic11AtomicUsize5store17hd81bb965d8847172E(ptr align 8 @_ZN14extended_pilot12HELPER_CALLS17hceaaa1dfa217d7abE, i64 0, i8 %132) #14
  %got = call i64 @pilot_call_helper(i64 %a21, i64 %b22) #14
  %_524 = icmp eq i64 %got, %expected23
  br i1 %_524, label %bb264, label %bb265

bb261:                                            ; preds = %bb258
; call core::ptr::drop_in_place<core::array::iter::IntoIter<[u64; 3],289_usize>>
  call void @"_ZN4core3ptr92drop_in_place$LT$core..array..iter..IntoIter$LT$$u5b$u64$u3b$$u20$3$u5d$$C$289_usize$GT$$GT$17h6320d5ec2bb54e95E"(ptr align 8 %iter16) #14
  %133 = getelementptr inbounds nuw i64, ptr %_552, i64 0
  store i64 7, ptr %133, align 8
  %134 = getelementptr inbounds nuw i64, ptr %_552, i64 1
  store i64 9, ptr %134, align 8
; call core::array::iter::<impl core::iter::traits::collect::IntoIterator for [T; N]>::into_iter
  call void @"_ZN4core5array4iter94_$LT$impl$u20$core..iter..traits..collect..IntoIterator$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9into_iter17hf73a437d98e3e86dE"(ptr sret([32 x i8]) align 8 %_551, ptr align 8 %_552) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %iter17, ptr align 8 %_551, i64 32, i1 false)
  br label %bb278

bb278:                                            ; preds = %bb280, %bb261
; call <core::array::iter::IntoIter<T,_> as core::iter::traits::iterator::Iterator>::next
  %135 = call { i64, i64 } @"_ZN99_$LT$core..array..iter..IntoIter$LT$T$C$_$GT$$u20$as$u20$core..iter..traits..iterator..Iterator$GT$4next17h97f1caf174d894b1E"(ptr align 8 %iter17) #14
  %136 = extractvalue { i64, i64 } %135, 0
  %137 = extractvalue { i64, i64 } %135, 1
  store i64 %136, ptr %_554, align 8
  %138 = getelementptr inbounds i8, ptr %_554, i64 8
  store i64 %137, ptr %138, align 8
  %_556 = load i64, ptr %_554, align 8
  %139 = getelementptr inbounds i8, ptr %_554, i64 8
  %140 = load i64, ptr %139, align 8
  %141 = trunc nuw i64 %_556 to i1
  br i1 %141, label %bb280, label %bb281

bb280:                                            ; preds = %bb278
  %142 = getelementptr inbounds i8, ptr %_554, i64 8
  %len = load i64, ptr %142, align 8
  call void @llvm.memset.p0.i64(ptr align 1 %source18, i8 60, i64 9, i1 false)
; call core::array::<impl core::ops::index::Index<I> for [T; N]>::index
  %143 = call { ptr, i64 } @"_ZN4core5array85_$LT$impl$u20$core..ops..index..Index$LT$I$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$5index17h389ca3ce22185a5dE"(ptr align 1 %source18, i64 %len, ptr align 8 @alloc_a027c4cfdd2d4ac1ea07f38a958983b3) #14
  %_563.0 = extractvalue { ptr, i64 } %143, 0
  %_563.1 = extractvalue { ptr, i64 } %143, 1
; call zerocopy::FromBytes::read_from_bytes
  call void @_ZN8zerocopy9FromBytes15read_from_bytes17h7dfc2b7241a232c8E(ptr sret([16 x i8]) align 8 %_562, ptr align 1 %_563.0, i64 %_563.1) #14
; call core::result::Result<T,E>::is_err
  %_560 = call zeroext i1 @"_ZN4core6result19Result$LT$T$C$E$GT$6is_err17h3645aee6148a1928E"(ptr align 8 %_562) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_560, ptr align 1 @alloc_9fc22b8281c31507a4d7153995e6364a, i64 23, ptr align 8 %checks) #14
  call void @llvm.memset.p0.i64(ptr align 1 %dst19, i8 -90, i64 9, i1 false)
; call core::num::<impl u64>::to_be_bytes
  %144 = call i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$11to_be_bytes17h763c5b251a6c665cE"(i64 4660) #14
  store i64 %144, ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %bytes.i, ptr align 8 %0, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_5.i, ptr align 1 %bytes.i, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_0.i48, ptr align 1 %_5.i, i64 8, i1 false)
  %145 = load i64, ptr %_0.i48, align 1
  store i64 %145, ptr %3, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %wire, ptr align 8 %3, i64 8, i1 false)
; call core::array::<impl core::ops::index::IndexMut<I> for [T; N]>::index_mut
  %146 = call { ptr, i64 } @"_ZN4core5array88_$LT$impl$u20$core..ops..index..IndexMut$LT$I$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$9index_mut17hf70689d488f7481bE"(ptr align 1 %dst19, i64 %len, ptr align 8 @alloc_3d2b22f6797fb9c8509022e3de60e2be) #14
  %_572.0 = extractvalue { ptr, i64 } %146, 0
  %_572.1 = extractvalue { ptr, i64 } %146, 1
; call zerocopy::IntoBytes::write_to
  %147 = call align 1 ptr @_ZN8zerocopy9IntoBytes8write_to17h333dd8283fe0b02eE(ptr align 1 %wire, ptr align 1 %_572.0, i64 %_572.1) #14
  store ptr %147, ptr %result, align 8
; call core::result::Result<T,E>::is_err
  %_576 = call zeroext i1 @"_ZN4core6result19Result$LT$T$C$E$GT$6is_err17h7384aa11ff037724E"(ptr align 8 %result) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_576, ptr align 1 @alloc_b0b71860c7ea2a29b7e0e8c26098b5d4, i64 29, ptr align 8 %checks) #14
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_581 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h2aa518081be58070E"(ptr align 1 %dst19, ptr align 1 @alloc_740169030ee0401ee356367948a12a38) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_581, ptr align 1 @alloc_03d5a65b6a5ce4615b00d06a59905895, i64 29, ptr align 8 %checks) #14
  br label %bb278

bb281:                                            ; preds = %bb278
; call core::ptr::drop_in_place<core::array::iter::IntoIter<usize,2_usize>>
  call void @"_ZN4core3ptr71drop_in_place$LT$core..array..iter..IntoIter$LT$usize$C$2_usize$GT$$GT$17hcae5af927efba4b4E"(ptr align 8 %iter17) #14
  store ptr @alloc_c152a840973ba04895d1feffaffa964c, ptr %args, align 8
  %148 = getelementptr inbounds i8, ptr %args, i64 8
  store ptr %checks, ptr %148, align 8
  %_598 = load ptr, ptr %args, align 8
; call core::fmt::rt::Argument::new_display
  call void @_ZN4core3fmt2rt8Argument11new_display17h17ee8a6fae403bc4E(ptr sret([16 x i8]) align 8 %_592, ptr align 8 %_598) #14
  %149 = getelementptr inbounds i8, ptr %args, i64 8
  %_599 = load ptr, ptr %149, align 8
; call core::fmt::rt::Argument::new_display
  call void @_ZN4core3fmt2rt8Argument11new_display17he5979accc9ea05abE(ptr sret([16 x i8]) align 8 %_593, ptr align 8 %_599) #14
  %150 = getelementptr inbounds nuw %"core::fmt::rt::Argument<'_>", ptr %args20, i64 0
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %150, ptr align 8 %_592, i64 16, i1 false)
  %151 = getelementptr inbounds nuw %"core::fmt::rt::Argument<'_>", ptr %args20, i64 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %151, ptr align 8 %_593, i64 16, i1 false)
; call core::fmt::rt::<impl core::fmt::Arguments>::new_v1
  call void @"_ZN4core3fmt2rt38_$LT$impl$u20$core..fmt..Arguments$GT$6new_v117haf3e53cd4fb6e77eE"(ptr sret([48 x i8]) align 8 %_587, ptr align 8 @alloc_919c696c65d381e392ab9e07a65fcc86, ptr align 8 %args20) #14
; call std::io::stdio::_print
  call void @_ZN3std2io5stdio6_print17h86bf21ce6e231958E(ptr align 8 %_587) #14
  ret void

bb265:                                            ; preds = %bb260
  store i8 0, ptr %_523, align 1
  br label %bb268

bb264:                                            ; preds = %bb260
; call extended_pilot::helper_math
  %_526 = call i64 @_ZN14extended_pilot11helper_math17h8abbf2b36f1bb902E(i64 %a21, i64 %b22) #14
  %_0.i = add i64 %_526, 1
  %152 = icmp eq i64 %_0.i, %expected23
  %153 = zext i1 %152 to i8
  store i8 %153, ptr %_523, align 1
  br label %bb268

bb268:                                            ; preds = %bb264, %bb265
  %154 = load i8, ptr %_523, align 1
  %155 = trunc nuw i8 %154 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %155, ptr align 1 @alloc_39fbebfa06d3949ee7666a8f08c17138, i64 19, ptr align 8 %checks) #14
  store i8 0, ptr %_533, align 1
  %156 = load i8, ptr %_533, align 1
; call core::sync::atomic::AtomicUsize::load
  %_531 = call i64 @_ZN4core4sync6atomic11AtomicUsize4load17hc1325ac4b52c1b05E(ptr align 8 @_ZN14extended_pilot12HELPER_CALLS17hceaaa1dfa217d7abE, i8 %156) #14
  %_530 = icmp eq i64 %_531, 1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_530, ptr align 1 @alloc_ba5c6512d8d7f8a9c3e50e6eeb52fba9, i64 17, ptr align 8 %checks) #14
  store i8 0, ptr %_538, align 1
  %157 = load i8, ptr %_538, align 1
; call core::sync::atomic::AtomicUsize::store
  call void @_ZN4core4sync6atomic11AtomicUsize5store17hd81bb965d8847172E(ptr align 8 @_ZN14extended_pilot12HELPER_CALLS17hceaaa1dfa217d7abE, i64 0, i8 %157) #14
; call extended_pilot::rust_call_helper
  %_541 = call i64 @_ZN14extended_pilot16rust_call_helper17h4802fef1bbd0e865E(i64 %a21, i64 %b22) #14
  %_540 = icmp eq i64 %_541, %expected23
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_540, ptr align 1 @alloc_7fb6948253e08425011968cd1ab90324, i64 17, ptr align 8 %checks) #14
  store i8 0, ptr %_548, align 1
  %158 = load i8, ptr %_548, align 1
; call core::sync::atomic::AtomicUsize::load
  %_546 = call i64 @_ZN4core4sync6atomic11AtomicUsize4load17hc1325ac4b52c1b05E(ptr align 8 @_ZN14extended_pilot12HELPER_CALLS17hceaaa1dfa217d7abE, i8 %158) #14
  %_545 = icmp eq i64 %_546, 1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_545, ptr align 1 @alloc_065d390ec367a092c01bac2a3e88eda3, i64 22, ptr align 8 %checks) #14
  br label %bb258

bb216:                                            ; preds = %bb214
  %159 = getelementptr inbounds nuw [16 x i8], ptr %_437, i64 %ai
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_436, ptr align 1 %159, i64 16, i1 false)
; call extended_pilot::Guard16::new
  call void @_ZN14extended_pilot7Guard163new17h424d6b061fee17aaE(ptr sret([48 x i8]) align 16 %a11, ptr align 1 %_436) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_441, ptr align 1 @alloc_df49633132bd0738f71b84ee1e58fda5, i64 192, i1 false)
  %_442 = icmp ult i64 %bi, 12
  br i1 %_442, label %bb218, label %panic24

panic:                                            ; preds = %bb214
; call core::panicking::panic_bounds_check
  call void @_ZN4core9panicking18panic_bounds_check17hfa2ac8420ad021dcE(i64 %ai, i64 12, ptr align 8 @alloc_fe7b60ca705568a437d85786e99ed873) #15
  unreachable

bb218:                                            ; preds = %bb216
  %160 = getelementptr inbounds nuw [16 x i8], ptr %_441, i64 %bi
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_440, ptr align 1 %160, i64 16, i1 false)
; call extended_pilot::Guard16::new
  call void @_ZN14extended_pilot7Guard163new17h424d6b061fee17aaE(ptr sret([48 x i8]) align 16 %b12, ptr align 1 %_440) #14
  call void @llvm.memset.p0.i64(ptr align 1 %_444, i8 -52, i64 16, i1 false)
; call extended_pilot::Guard16::new
  call void @_ZN14extended_pilot7Guard163new17h424d6b061fee17aaE(ptr sret([48 x i8]) align 16 %out13, ptr align 1 %_444) #14
  %_446 = icmp eq i64 %ai, %bi
  br i1 %_446, label %bb221, label %bb222

panic24:                                          ; preds = %bb216
; call core::panicking::panic_bounds_check
  call void @_ZN4core9panicking18panic_bounds_check17hfa2ac8420ad021dcE(i64 %bi, i64 12, ptr align 8 @alloc_13818b644a22fbe6e3bb8eec05faecad) #15
  unreachable

bb222:                                            ; preds = %bb218
  %_450 = getelementptr inbounds i8, ptr %b12, i64 16
  store ptr %_450, ptr %b_ptr14, align 8
  br label %bb223

bb221:                                            ; preds = %bb218
  %_448 = getelementptr inbounds i8, ptr %a11, i64 16
  store ptr %_448, ptr %b_ptr14, align 8
  br label %bb223

bb223:                                            ; preds = %bb221, %bb222
  %_457 = getelementptr inbounds i8, ptr %a11, i64 16
  %_454 = ptrtoint ptr %_457 to i64
  %_453 = urem i64 %_454, 16
  %161 = icmp eq i64 %_453, 0
  br i1 %161, label %bb226, label %bb230

bb226:                                            ; preds = %bb223
  %_463 = getelementptr inbounds i8, ptr %b12, i64 16
  %_460 = ptrtoint ptr %_463 to i64
  %_459 = urem i64 %_460, 16
  %162 = icmp eq i64 %_459, 0
  br i1 %162, label %bb229, label %bb230

bb230:                                            ; preds = %bb226, %bb223
  store i8 0, ptr %_452, align 1
  br label %bb233

bb229:                                            ; preds = %bb226
  %_469 = getelementptr inbounds i8, ptr %out13, i64 16
  %_466 = ptrtoint ptr %_469 to i64
  %_465 = urem i64 %_466, 16
  %163 = icmp eq i64 %_465, 0
  %164 = zext i1 %163 to i8
  store i8 %164, ptr %_452, align 1
  br label %bb233

bb233:                                            ; preds = %bb230, %bb229
  %165 = load i8, ptr %_452, align 1
  %166 = trunc nuw i8 %165 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %166, ptr align 1 @alloc_b68c7081e6f02e9733108cba6bc83cee, i64 18, ptr align 8 %checks) #14
  %_476 = getelementptr inbounds i8, ptr %out13, i64 16
  %_479 = getelementptr inbounds i8, ptr %a11, i64 16
  %_480 = load ptr, ptr %b_ptr14, align 8
  call void @pilot_simd_add16(ptr %_476, ptr %_479, ptr %_480) #14
  %_482 = getelementptr inbounds i8, ptr %a11, i64 16
  %_483 = getelementptr inbounds i8, ptr %b12, i64 16
; call extended_pilot::rust_add16
  call void @_ZN14extended_pilot10rust_add1617h0a68c57815c18a3eE(ptr sret([16 x i8]) align 1 %baseline15, ptr align 1 %_482, ptr align 1 %_483) #14
  %_487 = getelementptr inbounds i8, ptr %out13, i64 16
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_486 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %_487, ptr align 1 %expected) #14
  br i1 %_486, label %bb240, label %bb241

bb241:                                            ; preds = %bb233
  store i8 0, ptr %_485, align 1
  br label %bb242

bb240:                                            ; preds = %bb233
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %167 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %baseline15, ptr align 1 %expected) #14
  %168 = zext i1 %167 to i8
  store i8 %168, ptr %_485, align 1
  br label %bb242

bb242:                                            ; preds = %bb240, %bb241
  %169 = load i8, ptr %_485, align 1
  %170 = trunc nuw i8 %169 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %170, ptr align 1 @alloc_aff5e137726c4d2349c18b19090c6249, i64 14, ptr align 8 %checks) #14
; call extended_pilot::Guard16::intact
  %_495 = call zeroext i1 @_ZN14extended_pilot7Guard166intact17h0cc5d2cddb0349aaE(ptr align 16 %out13) #14
  br i1 %_495, label %bb245, label %bb253

bb253:                                            ; preds = %bb250, %bb247, %bb245, %bb242
  store i8 0, ptr %_494, align 1
  br label %bb255

bb245:                                            ; preds = %bb242
; call extended_pilot::Guard16::intact
  %_497 = call zeroext i1 @_ZN14extended_pilot7Guard166intact17h0cc5d2cddb0349aaE(ptr align 16 %a11) #14
  br i1 %_497, label %bb247, label %bb253

bb247:                                            ; preds = %bb245
; call extended_pilot::Guard16::intact
  %_499 = call zeroext i1 @_ZN14extended_pilot7Guard166intact17h0cc5d2cddb0349aaE(ptr align 16 %b12) #14
  br i1 %_499, label %bb249, label %bb253

bb249:                                            ; preds = %bb247
  %_502 = getelementptr inbounds i8, ptr %a11, i64 16
  %_504 = icmp ult i64 %ai, 12
  br i1 %_504, label %bb250, label %panic25

bb250:                                            ; preds = %bb249
  %_503 = getelementptr inbounds nuw [16 x i8], ptr @alloc_df49633132bd0738f71b84ee1e58fda5, i64 %ai
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_501 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %_502, ptr align 1 %_503) #14
  br i1 %_501, label %bb252, label %bb253

panic25:                                          ; preds = %bb249
; call core::panicking::panic_bounds_check
  call void @_ZN4core9panicking18panic_bounds_check17hfa2ac8420ad021dcE(i64 %ai, i64 12, ptr align 8 @alloc_1e94e04a48e4b99390186fc97f15465b) #15
  unreachable

bb252:                                            ; preds = %bb250
  %_505 = getelementptr inbounds i8, ptr %b12, i64 16
  %_507 = icmp ult i64 %bi, 12
  br i1 %_507, label %bb254, label %panic26

bb255:                                            ; preds = %bb254, %bb253
  %171 = load i8, ptr %_494, align 1
  %172 = trunc nuw i8 %171 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %172, ptr align 1 @alloc_99f669e0aea23b6e9811243e2889d625, i64 14, ptr align 8 %checks) #14
  br label %bb212

bb254:                                            ; preds = %bb252
  %_506 = getelementptr inbounds nuw [16 x i8], ptr @alloc_df49633132bd0738f71b84ee1e58fda5, i64 %bi
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %173 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %_505, ptr align 1 %_506) #14
  %174 = zext i1 %173 to i8
  store i8 %174, ptr %_494, align 1
  br label %bb255

panic26:                                          ; preds = %bb252
; call core::panicking::panic_bounds_check
  call void @_ZN4core9panicking18panic_bounds_check17hfa2ac8420ad021dcE(i64 %bi, i64 12, ptr align 8 @alloc_03c51604ed10e62df9e875a4492ddac3) #15
  unreachable

bb153:                                            ; preds = %bb144
  %_330 = getelementptr inbounds i8, ptr %scalar, i64 16
  %_327 = ptrtoint ptr %_330 to i64
  %_326 = urem i64 %_327, 16
  %175 = icmp eq i64 %_326, 0
  br i1 %175, label %bb156, label %bb157

bb157:                                            ; preds = %bb153, %bb144
  store i8 0, ptr %_319, align 1
  br label %bb160

bb156:                                            ; preds = %bb153
  %_336 = getelementptr inbounds i8, ptr %simd, i64 16
  %_333 = ptrtoint ptr %_336 to i64
  %_332 = urem i64 %_333, 16
  %176 = icmp eq i64 %_332, 0
  %177 = zext i1 %176 to i8
  store i8 %177, ptr %_319, align 1
  br label %bb160

bb160:                                            ; preds = %bb157, %bb156
  %178 = load i8, ptr %_319, align 1
  %179 = trunc nuw i8 %178 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %179, ptr align 1 @alloc_0fcaa72dade1d254e789d4d18a2b43e7, i64 14, ptr align 8 %checks) #14
  %_343 = getelementptr inbounds i8, ptr %scalar, i64 16
  %_346 = getelementptr inbounds i8, ptr %source7, i64 16
  call void @pilot_copy16(ptr %_343, ptr %_346) #14
  %_350 = getelementptr inbounds i8, ptr %simd, i64 16
  %_353 = getelementptr inbounds i8, ptr %source7, i64 16
  call void @pilot_simd_copy16(ptr %_350, ptr %_353) #14
  %_355 = getelementptr inbounds i8, ptr %source7, i64 16
  %_356 = getelementptr inbounds i8, ptr %zc, i64 16
; call extended_pilot::zc_copy16
  call void @_ZN14extended_pilot9zc_copy1617h333cef0da883ee38E(ptr align 1 %_355, ptr align 1 %_356) #14
  %_358 = getelementptr inbounds i8, ptr %source7, i64 16
  %_359 = getelementptr inbounds i8, ptr %baseline8, i64 16
; call extended_pilot::rust_copy16
  call void @_ZN14extended_pilot11rust_copy1617hf553a6eb2e70da00E(ptr align 1 %_358, ptr align 1 %_359) #14
  %_363 = getelementptr inbounds i8, ptr %scalar, i64 16
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_362 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %_363, ptr align 1 %bytes) #14
  br i1 %_362, label %bb171, label %bb176

bb176:                                            ; preds = %bb173, %bb171, %bb160
  store i8 0, ptr %_361, align 1
  br label %bb177

bb171:                                            ; preds = %bb160
  %_366 = getelementptr inbounds i8, ptr %simd, i64 16
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_365 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %_366, ptr align 1 %bytes) #14
  br i1 %_365, label %bb173, label %bb176

bb173:                                            ; preds = %bb171
  %_369 = getelementptr inbounds i8, ptr %zc, i64 16
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_368 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %_369, ptr align 1 %bytes) #14
  br i1 %_368, label %bb175, label %bb176

bb175:                                            ; preds = %bb173
  %_371 = getelementptr inbounds i8, ptr %baseline8, i64 16
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %180 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %_371, ptr align 1 %bytes) #14
  %181 = zext i1 %180 to i8
  store i8 %181, ptr %_361, align 1
  br label %bb177

bb177:                                            ; preds = %bb175, %bb176
  %182 = load i8, ptr %_361, align 1
  %183 = trunc nuw i8 %182 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %183, ptr align 1 @alloc_e2884dc8bff5c33bae7b2ab5a2e22eea, i64 27, ptr align 8 %checks) #14
; call extended_pilot::Guard16::intact
  %_377 = call zeroext i1 @_ZN14extended_pilot7Guard166intact17h0cc5d2cddb0349aaE(ptr align 16 %scalar) #14
  br i1 %_377, label %bb180, label %bb189

bb189:                                            ; preds = %bb186, %bb184, %bb182, %bb180, %bb177
  store i8 0, ptr %_376, align 1
  br label %bb190

bb180:                                            ; preds = %bb177
; call extended_pilot::Guard16::intact
  %_379 = call zeroext i1 @_ZN14extended_pilot7Guard166intact17h0cc5d2cddb0349aaE(ptr align 16 %simd) #14
  br i1 %_379, label %bb182, label %bb189

bb182:                                            ; preds = %bb180
; call extended_pilot::Guard16::intact
  %_381 = call zeroext i1 @_ZN14extended_pilot7Guard166intact17h0cc5d2cddb0349aaE(ptr align 16 %zc) #14
  br i1 %_381, label %bb184, label %bb189

bb184:                                            ; preds = %bb182
; call extended_pilot::Guard16::intact
  %_383 = call zeroext i1 @_ZN14extended_pilot7Guard166intact17h0cc5d2cddb0349aaE(ptr align 16 %baseline8) #14
  br i1 %_383, label %bb186, label %bb189

bb186:                                            ; preds = %bb184
; call extended_pilot::Guard16::intact
  %_385 = call zeroext i1 @_ZN14extended_pilot7Guard166intact17h0cc5d2cddb0349aaE(ptr align 16 %source7) #14
  br i1 %_385, label %bb188, label %bb189

bb188:                                            ; preds = %bb186
  %_387 = getelementptr inbounds i8, ptr %source7, i64 16
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %184 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h7d5d7f18f6572938E"(ptr align 1 %_387, ptr align 1 %bytes) #14
  %185 = zext i1 %184 to i8
  store i8 %185, ptr %_376, align 1
  br label %bb190

bb190:                                            ; preds = %bb188, %bb189
  %186 = load i8, ptr %_376, align 1
  %187 = trunc nuw i8 %186 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %187, ptr align 1 @alloc_2dce8867486f99811029456ce360cb96, i64 12, ptr align 8 %checks) #14
  %_394 = getelementptr inbounds i8, ptr %source7, i64 16
; call zerocopy::FromBytes::ref_from_bytes
  call void @_ZN8zerocopy9FromBytes14ref_from_bytes17h3fe09cf7564e14e4E(ptr sret([24 x i8]) align 8 %_392, ptr align 1 %_394, i64 16) #14
; call core::result::Result<T,E>::expect
  %view = call align 1 ptr @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h47abfc140087601bE"(ptr align 8 %_392, ptr align 1 @alloc_6b7d3b6c55e21a409becc8ff4e5b6cfa, i64 13, ptr align 8 @alloc_9607a92e94d9641e754f5eba05a75b50) #14
  %_402 = getelementptr inbounds i8, ptr %source7, i64 16
  %_397 = icmp eq ptr %view, %_402
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_397, ptr align 1 @alloc_ccd7e5b641e08e3803aeabc6c7bbadbb, i64 21, ptr align 8 %checks) #14
; call core::ops::range::RangeInclusive<Idx>::new
  call void @"_ZN4core3ops5range25RangeInclusive$LT$Idx$GT$3new17h65d5050921f6672bE"(ptr sret([24 x i8]) align 8 %_406, i64 0, i64 16) #14
; call <I as core::iter::traits::collect::IntoIterator>::into_iter
  call void @"_ZN63_$LT$I$u20$as$u20$core..iter..traits..collect..IntoIterator$GT$9into_iter17hb981ff5553f36980E"(ptr sret([24 x i8]) align 8 %_405, ptr align 8 %_406) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %iter9, ptr align 8 %_405, i64 24, i1 false)
  br label %bb199

bb199:                                            ; preds = %bb209, %bb190
; call core::iter::range::<impl core::iter::traits::iterator::Iterator for core::ops::range::RangeInclusive<A>>::next
  %188 = call { i64, i64 } @"_ZN4core4iter5range110_$LT$impl$u20$core..iter..traits..iterator..Iterator$u20$for$u20$core..ops..range..RangeInclusive$LT$A$GT$$GT$4next17hd68c10f4d31d14e8E"(ptr align 8 %iter9) #14
  %189 = extractvalue { i64, i64 } %188, 0
  %190 = extractvalue { i64, i64 } %188, 1
  store i64 %189, ptr %_408, align 8
  %191 = getelementptr inbounds i8, ptr %_408, i64 8
  store i64 %190, ptr %191, align 8
  %_410 = load i64, ptr %_408, align 8
  %192 = getelementptr inbounds i8, ptr %_408, i64 8
  %193 = load i64, ptr %192, align 8
  %194 = trunc nuw i64 %_410 to i1
  br i1 %194, label %bb201, label %bb142

bb201:                                            ; preds = %bb199
  %195 = getelementptr inbounds i8, ptr %_408, i64 8
  %offset = load i64, ptr %195, align 8
  %_415 = getelementptr inbounds i8, ptr %source7, i64 16
  %got27 = call ptr @pilot_ptr(ptr %_415, i64 %offset) #14
  %_419 = getelementptr inbounds i8, ptr %source7, i64 16
  %_0.i47 = getelementptr inbounds nuw i8, ptr %_419, i64 %offset
  %_422 = icmp eq ptr %got27, %_0.i47
  br i1 %_422, label %bb206, label %bb207

bb207:                                            ; preds = %bb201
  store i8 0, ptr %_421, align 1
  br label %bb209

bb206:                                            ; preds = %bb201
  %_424 = getelementptr inbounds i8, ptr %source7, i64 16
; call extended_pilot::rust_ptr
  %_423 = call ptr @_ZN14extended_pilot8rust_ptr17h749ef15fb3237769E(ptr align 1 %_424, i64 %offset) #14
  %196 = icmp eq ptr %_423, %_0.i47
  %197 = zext i1 %196 to i8
  store i8 %197, ptr %_421, align 1
  br label %bb209

bb209:                                            ; preds = %bb206, %bb207
  %198 = load i8, ptr %_421, align 1
  %199 = trunc nuw i8 %198 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %199, ptr align 1 @alloc_85fda77841ed425dbdbff2ea33376135, i64 29, ptr align 8 %checks) #14
  br label %bb199

bb105:                                            ; preds = %bb101, %bb100, %bb88
  store i8 0, ptr %_219, align 1
  br label %bb108

bb100:                                            ; preds = %bb88
  %_221 = icmp eq i64 %b30, %x
  br i1 %_221, label %bb101, label %bb105

bb101:                                            ; preds = %bb100
  %_224 = getelementptr inbounds nuw i64, ptr %source, i64 1
; call extended_pilot::rust_load
  %_223 = call i64 @_ZN14extended_pilot9rust_load17h119de87a71289100E(ptr align 8 %_224) #14
  %_222 = icmp eq i64 %_223, %x
  br i1 %_222, label %bb104, label %bb105

bb104:                                            ; preds = %bb101
  %200 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  %_230 = load i64, ptr %200, align 8
  %201 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  %_233 = load i64, ptr %201, align 8
  %202 = getelementptr inbounds nuw i64, ptr %_229, i64 0
  store i64 %_230, ptr %202, align 8
  %203 = getelementptr inbounds nuw i64, ptr %_229, i64 1
  store i64 %x, ptr %203, align 8
  %204 = getelementptr inbounds nuw i64, ptr %_229, i64 2
  store i64 %_233, ptr %204, align 8
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %205 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h859fe206253d1728E"(ptr align 8 %source, ptr align 8 %_229) #14
  %206 = zext i1 %205 to i8
  store i8 %206, ptr %_219, align 1
  br label %bb108

bb108:                                            ; preds = %bb104, %bb105
  %207 = load i8, ptr %_219, align 1
  %208 = trunc nuw i8 %207 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %208, ptr align 1 @alloc_b110a08ed55610b06df9c62d38498d39, i64 21, ptr align 8 %checks) #14
  %_0.i44 = getelementptr inbounds nuw i64, ptr %dst, i64 1
  call void @pilot_store(ptr %_0.i44, i64 %x) #14
  %209 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  %_248 = load i64, ptr %209, align 8
  %210 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  %_251 = load i64, ptr %210, align 8
  %211 = getelementptr inbounds nuw i64, ptr %_247, i64 0
  store i64 %_248, ptr %211, align 8
  %212 = getelementptr inbounds nuw i64, ptr %_247, i64 1
  store i64 %x, ptr %212, align 8
  %213 = getelementptr inbounds nuw i64, ptr %_247, i64 2
  store i64 %_251, ptr %213, align 8
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_244 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h859fe206253d1728E"(ptr align 8 %dst, ptr align 8 %_247) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_244, ptr align 1 @alloc_a3022215cbc4d93d75ff36ef0e45ea7d, i64 16, ptr align 8 %checks) #14
  %214 = getelementptr inbounds nuw i64, ptr %dst, i64 1
  store i64 0, ptr %214, align 8
  %_0.i43 = getelementptr inbounds nuw i64, ptr %dst, i64 1
; call extended_pilot::inline_store
  call void @_ZN14extended_pilot12inline_store17h07e83f398e5e13c5E(ptr %_0.i43, i64 %x) #14
  %215 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  %_268 = load i64, ptr %215, align 8
  %216 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  %_271 = load i64, ptr %216, align 8
  %217 = getelementptr inbounds nuw i64, ptr %_267, i64 0
  store i64 %_268, ptr %217, align 8
  %218 = getelementptr inbounds nuw i64, ptr %_267, i64 1
  store i64 %x, ptr %218, align 8
  %219 = getelementptr inbounds nuw i64, ptr %_267, i64 2
  store i64 %_271, ptr %219, align 8
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_264 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h859fe206253d1728E"(ptr align 8 %dst, ptr align 8 %_267) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_264, ptr align 1 @alloc_dbb2f02de7ffe024ec16cb240f78d280, i64 23, ptr align 8 %checks) #14
  %220 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  %_277 = load i64, ptr %220, align 8
  %221 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  %_280 = load i64, ptr %221, align 8
  %222 = getelementptr inbounds nuw i64, ptr %baseline, i64 0
  store i64 %_277, ptr %222, align 8
  %223 = getelementptr inbounds nuw i64, ptr %baseline, i64 1
  store i64 0, ptr %223, align 8
  %224 = getelementptr inbounds nuw i64, ptr %baseline, i64 2
  store i64 %_280, ptr %224, align 8
  %_284 = getelementptr inbounds nuw i64, ptr %baseline, i64 1
; call extended_pilot::rust_store
  call void @_ZN14extended_pilot10rust_store17h8f7ecb3f0dbf5221E(ptr align 8 %_284, i64 %x) #14
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_288 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h859fe206253d1728E"(ptr align 8 %dst, ptr align 8 %baseline) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_288, ptr align 1 @alloc_d402f7413af788172cdb7d05f581a90e, i64 19, ptr align 8 %checks) #14
; call extended_pilot::inline_label
  %_296 = call i64 @_ZN14extended_pilot12inline_label17hce24d0f42a259affE(i64 %x) #14
; call extended_pilot::rust_label
  %_297 = call i64 @_ZN14extended_pilot10rust_label17hb5450f348c5f2ff7E(i64 %x) #14
  %_295 = icmp eq i64 %_296, %_297
  br i1 %_295, label %bb133, label %bb134

bb134:                                            ; preds = %bb108
  store i8 0, ptr %_294, align 1
  br label %bb139

bb133:                                            ; preds = %bb108
; call extended_pilot::rust_label
  %_298 = call i64 @_ZN14extended_pilot10rust_label17hb5450f348c5f2ff7E(i64 %x) #14
  %225 = icmp eq i64 %x, 0
  br i1 %225, label %bb136, label %bb137

bb139:                                            ; preds = %bb138, %bb134
  %226 = load i8, ptr %_294, align 1
  %227 = trunc nuw i8 %226 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %227, ptr align 1 @alloc_82ec933a04e9adbc1c67d6f1c0ac3ada, i64 12, ptr align 8 %checks) #14
  br label %bb86

bb136:                                            ; preds = %bb133
  store i64 17, ptr %_299, align 8
  br label %bb138

bb137:                                            ; preds = %bb133
  store i64 41, ptr %_299, align 8
  br label %bb138

bb138:                                            ; preds = %bb137, %bb136
  %228 = load i64, ptr %_299, align 8
  %229 = icmp eq i64 %_298, %228
  %230 = zext i1 %229 to i8
  store i8 %230, ptr %_294, align 1
  br label %bb139

bb76:                                             ; preds = %bb66
  store i8 0, ptr %_164, align 1
  br label %bb78

bb75:                                             ; preds = %bb66
; call extended_pilot::zc_decode
  %_169 = call i64 @_ZN14extended_pilot9zc_decode17hf5ef34b6dafe7c79E(ptr align 1 %encoded) #14
  %231 = icmp eq i64 %_169, %x31
  %232 = zext i1 %231 to i8
  store i8 %232, ptr %_164, align 1
  br label %bb78

bb78:                                             ; preds = %bb75, %bb76
  %233 = load i8, ptr %_164, align 1
  %234 = trunc nuw i8 %233 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %234, ptr align 1 @alloc_abf8626ad38cc02965dbd49aa14f61de, i64 13, ptr align 8 %checks) #14
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_174, ptr align 1 %encoded, i64 8, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 1 %_174, i64 8, i1 false)
  %235 = load i64, ptr %1, align 8
; call core::num::<impl u64>::from_ne_bytes
  %host_word = call i64 @"_ZN4core3num21_$LT$impl$u20$u64$GT$13from_ne_bytes17hc580473d72475e6fE"(i64 %235) #14
  %_176 = icmp eq i64 %host_word, %expected32
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_176, ptr align 1 @alloc_4d00ccfdfe200e5040c2e2fbfdf1aaf8, i64 21, ptr align 8 %checks) #14
; call zerocopy::FromBytes::read_from_bytes
  call void @_ZN8zerocopy9FromBytes15read_from_bytes17hc141de9c938fd231E(ptr sret([16 x i8]) align 8 %_180, ptr align 1 %encoded, i64 8) #14
; call core::result::Result<T,E>::expect
  %native_read = call i64 @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17h1a3f49af4364d9deE"(ptr align 8 %_180, ptr align 1 @alloc_8201ddbf69297838cdcfbcf366c93eb4, i64 13, ptr align 8 @alloc_b1c687d5d6b680777219ce5cf351ec52) #14
  %_185 = icmp eq i64 %native_read, %expected32
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_185, ptr align 1 @alloc_27bbe9f55c42f8bb464508153e0483ae, i64 20, ptr align 8 %checks) #14
  br label %bb64

bb35:                                             ; preds = %bb33, %bb29
  store ptr %b, ptr %b_ptr, align 8
  br label %bb36

bb33:                                             ; preds = %bb29
  %_75 = icmp eq i64 %ah, %bh
  br i1 %_75, label %bb34, label %bb35

bb34:                                             ; preds = %bb33
  store ptr %a, ptr %b_ptr, align 8
  br label %bb36

bb36:                                             ; preds = %bb34, %bb35
  %_84 = load ptr, ptr %b_ptr, align 8
  %_0.i42 = getelementptr inbounds nuw i64, ptr %out2, i64 1
  %c = call i64 @pilot_add128(ptr %a, ptr %_84, ptr %_0.i42) #14
  %236 = getelementptr inbounds nuw i64, ptr %sentinels, i64 0
  %_95 = load i64, ptr %236, align 8
  %237 = getelementptr inbounds nuw i64, ptr %sentinels, i64 1
  %_98 = load i64, ptr %237, align 8
  %238 = getelementptr inbounds nuw i64, ptr %_94, i64 0
  store i64 %_95, ptr %238, align 8
  %239 = getelementptr inbounds nuw i64, ptr %_94, i64 1
  store i64 %low35, ptr %239, align 8
  %240 = getelementptr inbounds nuw i64, ptr %_94, i64 2
  store i64 %high, ptr %240, align 8
  %241 = getelementptr inbounds nuw i64, ptr %_94, i64 3
  store i64 %_98, ptr %241, align 8
; call core::array::equality::<impl core::cmp::PartialEq<[U; N]> for [T; N]>::eq
  %_91 = call zeroext i1 @"_ZN4core5array8equality103_$LT$impl$u20$core..cmp..PartialEq$LT$$u5b$U$u3b$$u20$N$u5d$$GT$$u20$for$u20$$u5b$T$u3b$$u20$N$u5d$$GT$2eq17h6d8e9898dd9d4c85E"(ptr align 8 %out2, ptr align 8 %_94) #14
  br i1 %_91, label %bb44, label %bb45

bb45:                                             ; preds = %bb36
  store i8 0, ptr %_90, align 1
  br label %bb46

bb44:                                             ; preds = %bb36
  %242 = icmp eq i64 %c, %carry36
  %243 = zext i1 %242 to i8
  store i8 %243, ptr %_90, align 1
  br label %bb46

bb46:                                             ; preds = %bb44, %bb45
  %244 = load i8, ptr %_90, align 1
  %245 = trunc nuw i8 %244 to i1
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %245, ptr align 1 @alloc_02eca21413ccc32994161c12acef02d6, i64 10, ptr align 8 %checks) #14
; call extended_pilot::rust_add128
  call void @_ZN14extended_pilot11rust_add12817h7f46eaca12712c06E(ptr sret([24 x i8]) align 8 %_106, ptr align 8 %a, ptr align 8 %b) #14
  store i64 %low35, ptr %_110, align 8
  %246 = getelementptr inbounds i8, ptr %_110, i64 8
  store i64 %high, ptr %246, align 8
  %247 = getelementptr inbounds i8, ptr %_110, i64 16
  store i64 %carry36, ptr %247, align 8
; call core::tuple::<impl core::cmp::PartialEq for (V,U,T)>::eq
  %_104 = call zeroext i1 @"_ZN4core5tuple68_$LT$impl$u20$core..cmp..PartialEq$u20$for$u20$$LP$V$C$U$C$T$RP$$GT$2eq17h1504af208955cb31E"(ptr align 8 %_106, ptr align 8 %_110) #14
; call extended_pilot::check
  call void @_ZN14extended_pilot5check17hc7f166296c072d40E(i1 zeroext %_104, ptr align 1 @alloc_c168e215480fb2698effa558f0e4841f, i64 11, ptr align 8 %checks) #14
  br label %bb27

bb11:                                             ; No predecessors!
  unreachable
}

; core::panicking::panic_nounwind_fmt
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core9panicking18panic_nounwind_fmt17hdcc420bb84b07b49E(ptr align 8, i1 zeroext, ptr align 8) unnamed_addr #5

; core::slice::index::slice_end_index_len_fail
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core5slice5index24slice_end_index_len_fail17heb50b9bbe4663132E(i64, i64, ptr align 8) unnamed_addr #5

; core::slice::index::slice_index_order_fail
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core5slice5index22slice_index_order_fail17h7a48bcbdaef81cf2E(i64, i64, ptr align 8) unnamed_addr #5

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg) #6

; std::rt::lang_start_internal
; Function Attrs: nounwind nonlazybind
declare i64 @_ZN3std2rt19lang_start_internal17h31bbb7f936fd6b5dE(ptr align 1, ptr align 8, i64, ptr, i8) unnamed_addr #1

; <&T as core::fmt::Display>::fmt
; Function Attrs: nounwind nonlazybind
declare zeroext i1 @"_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17hd277b88914e88d67E"(ptr align 8, ptr align 8) unnamed_addr #1

; core::fmt::num::imp::<impl core::fmt::Display for u64>::fmt
; Function Attrs: nounwind nonlazybind
declare zeroext i1 @"_ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u64$GT$3fmt17h7601fb479c860baeE"(ptr align 8, ptr align 8) unnamed_addr #1

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.bswap.i64(i64) #7

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.fshl.i64(i64, i64, i64) #7

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i128, i1 } @llvm.uadd.with.overflow.i128(i128, i128) #7

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i64, i1 } @llvm.uadd.with.overflow.i64(i64, i64) #7

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i64, i1 } @llvm.umul.with.overflow.i64(i64, i64) #7

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.ctlz.i64(i64, i1 immarg) #7

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.ctpop.i64(i64) #7

; Function Attrs: nounwind nonlazybind
declare i32 @rust_eh_personality(i32, i32, i64, ptr, ptr) unnamed_addr #1

; core::panicking::panic_fmt
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core9panicking9panic_fmt17hc49fc28484033487E(ptr align 8, ptr align 8) unnamed_addr #5

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg) #8

; Function Attrs: cold noreturn nounwind memory(inaccessiblemem: write)
declare void @llvm.trap() #9

; core::slice::<impl [T]>::copy_from_slice::len_mismatch_fail
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @"_ZN4core5slice29_$LT$impl$u20$$u5b$T$u5d$$GT$15copy_from_slice17len_mismatch_fail17h4edba79c204d9f9bE"(i64, i64, ptr align 8) unnamed_addr #5

; core::panicking::panic_const::panic_const_div_by_zero
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core9panicking11panic_const23panic_const_div_by_zero17hd1b66acfd73a6e98E(ptr align 8) unnamed_addr #5

; core::result::unwrap_failed
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core6result13unwrap_failed17h9e4c136384b1cfa3E(ptr align 1, i64, ptr align 1, ptr align 8, ptr align 8) unnamed_addr #5

; core::panicking::panic_nounwind
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core9panicking14panic_nounwind17h681d69c581350003E(ptr align 1, i64) unnamed_addr #5

; Function Attrs: nonlazybind
declare i32 @memcmp(ptr, ptr, i64) #10

; core::fmt::Formatter::debug_struct
; Function Attrs: nounwind nonlazybind
declare void @_ZN4core3fmt9Formatter12debug_struct17ha54210e59fde88afE(ptr sret([16 x i8]) align 8, ptr align 8, ptr align 1, i64) unnamed_addr #1

; core::fmt::builders::DebugStruct::finish
; Function Attrs: nounwind nonlazybind
declare zeroext i1 @_ZN4core3fmt8builders11DebugStruct6finish17hd58177b4b9fef635E(ptr align 8) unnamed_addr #1

; core::fmt::Formatter::debug_tuple
; Function Attrs: nounwind nonlazybind
declare void @_ZN4core3fmt9Formatter11debug_tuple17h5788c8e9cef8e881E(ptr sret([24 x i8]) align 8, ptr align 8, ptr align 1, i64) unnamed_addr #1

; core::fmt::builders::DebugTuple::field
; Function Attrs: nounwind nonlazybind
declare align 8 ptr @_ZN4core3fmt8builders10DebugTuple5field17haade97ea9c4f7f62E(ptr align 8, ptr align 1, ptr align 8) unnamed_addr #1

; core::fmt::builders::DebugTuple::finish
; Function Attrs: nounwind nonlazybind
declare zeroext i1 @_ZN4core3fmt8builders10DebugTuple6finish17hc28ea1e2485caf89E(ptr align 8) unnamed_addr #1

; core::panicking::panic
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core9panicking5panic17h239804395728b21fE(ptr align 1, i64, ptr align 8) unnamed_addr #5

; core::panicking::panic_const::panic_const_rem_by_zero
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core9panicking11panic_const23panic_const_rem_by_zero17hb2eecb9bde6b0e42E(ptr align 8) unnamed_addr #5

; core::panicking::panic_const::panic_const_sub_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core9panicking11panic_const24panic_const_sub_overflow17h9d34257ac1862bebE(ptr align 8) unnamed_addr #5

; core::panicking::panic_const::panic_const_shl_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core9panicking11panic_const24panic_const_shl_overflow17hbfdb61d170f9fa81E(ptr align 8) unnamed_addr #5

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core9panicking11panic_const24panic_const_add_overflow17h371a9588e01a5f2aE(ptr align 8) unnamed_addr #5

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i128, i1 } @llvm.umul.with.overflow.i128(i128, i128) #7

; core::panicking::panic_const::panic_const_mul_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind
declare void @_ZN4core9panicking11panic_const24panic_const_mul_overflow17hd5526b32f0b9d968E(ptr align 8) unnamed_addr #5

; core::panicking::panic_bounds_check
; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize
declare void @_ZN4core9panicking18panic_bounds_check17hfa2ac8420ad021dcE(i64, i64, ptr align 8) unnamed_addr #11

; std::io::stdio::_eprint
; Function Attrs: nounwind nonlazybind
declare void @_ZN3std2io5stdio7_eprint17h58458461bd19d139E(ptr align 8) unnamed_addr #1

; std::process::exit
; Function Attrs: noreturn nounwind nonlazybind
declare void @_ZN3std7process4exit17h00460fefcf032948E(i32) unnamed_addr #12

; std::io::stdio::_print
; Function Attrs: nounwind nonlazybind
declare void @_ZN3std2io5stdio6_print17h86bf21ce6e231958E(ptr align 8) unnamed_addr #1

; Function Attrs: nounwind nonlazybind
declare i64 @pilot_call_helper(i64, i64) unnamed_addr #1

; Function Attrs: nounwind nonlazybind
declare void @pilot_simd_add16(ptr, ptr, ptr) unnamed_addr #1

; Function Attrs: nounwind nonlazybind
declare void @pilot_copy16(ptr, ptr) unnamed_addr #1

; Function Attrs: nounwind nonlazybind
declare void @pilot_simd_copy16(ptr, ptr) unnamed_addr #1

; Function Attrs: nounwind nonlazybind
declare ptr @pilot_ptr(ptr, i64) unnamed_addr #1

; Function Attrs: nounwind nonlazybind
declare i64 @pilot_load(ptr) unnamed_addr #1

; Function Attrs: nounwind nonlazybind
declare void @pilot_store(ptr, i64) unnamed_addr #1

; Function Attrs: nounwind nonlazybind
declare i64 @pilot_bswap(i64) unnamed_addr #1

; Function Attrs: nounwind nonlazybind
declare i64 @pilot_add128(ptr, ptr, ptr) unnamed_addr #1

; Function Attrs: nounwind nonlazybind
declare void @pilot_mul(i64, i64, ptr) unnamed_addr #1

; Function Attrs: nonlazybind
define i32 @main(i32 %0, ptr %1) unnamed_addr #13 {
top:
  %2 = sext i32 %0 to i64
; call std::rt::lang_start
  %3 = call i64 @_ZN3std2rt10lang_start17hceb1b6aa47208e68E(ptr @_ZN14extended_pilot4main17hca72231bfee5693fE, i64 %2, ptr %1, i8 0)
  %4 = trunc i64 %3 to i32
  ret i32 %4
}

attributes #0 = { inlinehint nounwind nonlazybind "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nounwind nonlazybind "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { noinline nounwind nonlazybind "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { cold nounwind nonlazybind "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { inlinehint noreturn nounwind nonlazybind "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #5 = { cold noinline noreturn nounwind nonlazybind "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #6 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #7 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #8 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #9 = { cold noreturn nounwind memory(inaccessiblemem: write) }
attributes #10 = { nonlazybind }
attributes #11 = { cold minsize noinline noreturn nounwind nonlazybind optsize "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #12 = { noreturn nounwind nonlazybind "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #13 = { nonlazybind "target-cpu"="x86-64" }
attributes #14 = { nounwind }
attributes #15 = { noreturn nounwind }
attributes #16 = { cold nounwind }
attributes #17 = { memory(inaccessiblemem: readwrite) }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 7, !"PIE Level", i32 2}
!2 = !{i32 2, !"RtLibUseGOT", i32 1}
!3 = !{!"rustc version 1.89.0 (29483883e 2025-08-04)"}
!4 = !{i64 22191958584645461}
!5 = !{i64 0, i64 26182120642501, i64 26250840119252, i64 26319559596004}
!6 = !{i64 0, i64 30210799967077, i64 30266634541950}
!7 = !{i64 33882997006017}
!8 = !{i64 37357625549288}
