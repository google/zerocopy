; Probe D: DSE / GVN / StackColoring with llvm.lifetime.start.p0 and llvm.lifetime.end.p0
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare void @llvm.lifetime.start.p0(i64 immarg, ptr nocapture)
declare void @llvm.lifetime.end.p0(i64 immarg, ptr nocapture)
declare i64 @observe_addr(ptr)

; Variant D1: Dead Store Elimination across `llvm.lifetime.end.p0`
define void @dse_lifetime_end(i32 %x) {
entry:
  %a = alloca i32, align 4
  call void @llvm.lifetime.start.p0(i64 4, ptr %a)
  store i32 %x, ptr %a, align 4
  call void @llvm.lifetime.end.p0(i64 4, ptr %a)
  ret void
}

; Variant D2: StackColoring merges `%a` and `%b` into the SAME stack slot `[rsp]`
; when their `lifetime.start`/`lifetime.end` regions are disjoint, while `InstCombine`
; folds `icmp eq ptr %a, %b` to `false`!
define i1 @disjoint_lifetime_stack_coloring(ptr %out_eq) {
entry:
  %a = alloca [64 x i8], align 16
  %b = alloca [64 x i8], align 16
  %cmp_ir = icmp eq ptr %a, %b
  store i1 %cmp_ir, ptr %out_eq, align 1

  call void @llvm.lifetime.start.p0(i64 64, ptr %a)
  %addr_a = call i64 @observe_addr(ptr %a)
  call void @llvm.lifetime.end.p0(i64 64, ptr %a)

  call void @llvm.lifetime.start.p0(i64 64, ptr %b)
  %addr_b = call i64 @observe_addr(ptr %b)
  call void @llvm.lifetime.end.p0(i64 64, ptr %b)

  %cmp_obs = icmp eq i64 %addr_a, %addr_b
  ret i1 %cmp_obs
}
