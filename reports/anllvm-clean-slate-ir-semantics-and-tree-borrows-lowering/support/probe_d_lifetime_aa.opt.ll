; ModuleID = '.
source_filename = "."
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(i64 immarg, ptr captures(none)) #0

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(i64 immarg, ptr captures(none)) #0

declare i64 @observe_addr(ptr)

define void @dse_lifetime_end(i32 %x) {
entry:
  ret void
}

define i1 @disjoint_lifetime_stack_coloring(ptr %out_eq) {
entry:
  %a = alloca [64 x i8], align 16
  %b = alloca [64 x i8], align 16
  store i1 false, ptr %out_eq, align 1
  call void @llvm.lifetime.start.p0(i64 64, ptr nonnull %a)
  %addr_a = call i64 @observe_addr(ptr nonnull %a)
  call void @llvm.lifetime.end.p0(i64 64, ptr nonnull %a)
  call void @llvm.lifetime.start.p0(i64 64, ptr nonnull %b)
  %addr_b = call i64 @observe_addr(ptr nonnull %b)
  call void @llvm.lifetime.end.p0(i64 64, ptr nonnull %b)
  %cmp_obs = icmp eq i64 %addr_a, %addr_b
  ret i1 %cmp_obs
}

attributes #0 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
