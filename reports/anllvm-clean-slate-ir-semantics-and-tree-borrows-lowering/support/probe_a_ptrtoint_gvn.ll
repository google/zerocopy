; Probe A: ptrtoint + icmp eq + GVN + InstCombine + BasicAA on one-past-the-end pointers
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Variant A1: Pointer comparison `icmp eq ptr %p_end, %q` with GVN + BasicAA
; `%p` and `%q` are distinct objects (`noalias`). `%p_end` is one-past-the-end of `%p`.
; When `%p_end` and `%q` happen to share the same runtime integer address,
; GVN substitutes `%p_end` for `%q` in the `true` branch, causing BasicAA to report
; `NoAlias` between `%p` (via `%p_end`) and `%q`, so GVN forwards `0` instead of `42`!
define i32 @ptr_eq_gvn_miscompile(ptr noalias %p, ptr noalias %q) {
entry:
  store i32 0, ptr %q, align 4
  %p_end = getelementptr inbounds i8, ptr %p, i64 8
  %cmp = icmp eq ptr %p_end, %q
  br i1 %cmp, label %if.true, label %if.false

if.true:
  store i32 42, ptr %q, align 4
  %v = load i32, ptr %q, align 4
  ret i32 %v

if.false:
  ret i32 -1
}

; Variant A2: Integer comparison `ptrtoint` + `icmp eq i64` + `inttoptr`
; Step 1 (GVN): replaces `%iq` with `%ip` in `inttoptr i64 %iq to ptr`.
; Step 2 (InstCombine): folds `inttoptr (ptrtoint %p_end)` -> `%p_end`.
; Step 3 (GVN + BasicAA): sees `store i32 42, ptr %p_end` and `load i32, ptr %q` as NoAlias,
; forwarding `0` across the store to `%q`!
define i32 @ptrtoint_inttoptr_gvn_instcombine(ptr noalias %p, ptr noalias %q) {
entry:
  store i32 0, ptr %q, align 4
  %p_end = getelementptr inbounds i8, ptr %p, i64 8
  %ip = ptrtoint ptr %p_end to i64
  %iq = ptrtoint ptr %q to i64
  %cmp = icmp eq i64 %ip, %iq
  br i1 %cmp, label %if.true, label %if.false

if.true:
  %q_cast = inttoptr i64 %iq to ptr
  store i32 42, ptr %q_cast, align 4
  %v = load i32, ptr %q, align 4
  ret i32 %v

if.false:
  ret i32 -1
}
