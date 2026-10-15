; ModuleID = 'abi_subjects.e2113a355ceea76a-cgu.0'
source_filename = "abi_subjects.e2113a355ceea76a-cgu.0"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "arm64-apple-macosx11.0.0"

; <core::panic::location::Location>::line
; Function Attrs: inlinehint nounwind
define internal i32 @_RNvMs4_NtNtCsi86csyF5gCW_4core5panic8locationNtB5_8Location4lineCsjplKSa1E9lu_12abi_subjects(ptr align 8 %self) unnamed_addr #0 {
start:
  %0 = getelementptr inbounds i8, ptr %self, i64 16
  %_0 = load i32, ptr %0, align 8
  ret i32 %_0
}

; <core::panic::location::Location>::caller
; Function Attrs: inlinehint nounwind
define internal align 8 ptr @_RNvMs4_NtNtCsi86csyF5gCW_4core5panic8locationNtB5_8Location6callerCsjplKSa1E9lu_12abi_subjects(ptr align 8 %0) unnamed_addr #0 {
start:
  %1 = alloca [8 x i8], align 8
  store ptr %0, ptr %1, align 8
  %_0 = load ptr, ptr %1, align 8
  ret ptr %_0
}

; Function Attrs: noinline nounwind
define void @abi_c_big(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %x) unnamed_addr #1 {
start:
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %x, i64 24, i1 false)
  ret void
}

; Function Attrs: noinline nounwind
define double @abi_c_fp(float %x, double %y) unnamed_addr #1 {
start:
  %_3 = fpext float %x to double
  %_0 = fadd double %_3, %y
  ret double %_0
}

; Function Attrs: noinline nounwind
define [4 x float] @abi_c_hfa([4 x float] %0) unnamed_addr #1 {
start:
  %_0 = alloca [16 x i8], align 4
  %1 = alloca [16 x i8], align 4
  %x = alloca [16 x i8], align 4
  store [4 x float] %0, ptr %1, align 4
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %x, ptr align 4 %1, i64 16, i1 false)
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %_0, ptr align 4 %x, i64 16, i1 false)
  %2 = load [4 x float], ptr %_0, align 4
  ret [4 x float] %2
}

; Function Attrs: noinline nounwind
define i64 @abi_c_narrow(i8 zeroext %x, i16 signext %y, i1 zeroext %flag) unnamed_addr #1 {
start:
  %_5 = zext i8 %x to i64
  %_7 = sext i16 %y to i64
  %_4 = xor i64 %_5, %_7
  %_8 = zext i1 %flag to i64
  %_0 = xor i64 %_4, %_8
  ret i64 %_0
}

; Function Attrs: noinline nounwind
define [2 x i64] @abi_c_pair([2 x i64] %0) unnamed_addr #1 {
start:
  %_0 = alloca [16 x i8], align 8
  %1 = alloca [16 x i8], align 8
  %x = alloca [16 x i8], align 8
  store [2 x i64] %0, ptr %1, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %x, ptr align 8 %1, i64 16, i1 false)
  %2 = load i64, ptr %x, align 8
  %3 = getelementptr inbounds i8, ptr %x, i64 8
  %4 = load i32, ptr %3, align 8
  store i64 %2, ptr %_0, align 8
  %5 = getelementptr inbounds i8, ptr %_0, i64 8
  store i32 %4, ptr %5, align 8
  %6 = load [2 x i64], ptr %_0, align 8
  ret [2 x i64] %6
}

; Function Attrs: noinline nounwind
define ptr @abi_c_raw(ptr %x) unnamed_addr #1 {
start:
  ret ptr %x
}

; Function Attrs: noinline nounwind
define ptr @abi_interior(ptr align 8 %x) unnamed_addr #1 {
start:
  ret ptr %x
}

; Function Attrs: noinline nounwind
define void @abi_rust_big(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %x) unnamed_addr #1 {
start:
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %x, i64 24, i1 false)
  ret void
}

; Function Attrs: noinline nounwind
define i64 @abi_rust_narrow(i8 %x, i16 %y, i1 zeroext %flag) unnamed_addr #1 {
start:
  %_5 = zext i8 %x to i64
  %_7 = sext i16 %y to i64
  %_4 = xor i64 %_5, %_7
  %_8 = zext i1 %flag to i64
  %_0 = xor i64 %_4, %_8
  ret i64 %_0
}

; Function Attrs: noinline nounwind
define { i64, i32 } @abi_rust_tuple(i64 %x.0, i32 %x.1) unnamed_addr #1 {
start:
  %0 = insertvalue { i64, i32 } poison, i64 %x.0, 0
  %1 = insertvalue { i64, i32 } %0, i32 %x.1, 1
  ret { i64, i32 } %1
}

; Function Attrs: noinline nounwind
define i64 @abi_shared(ptr align 8 %x) unnamed_addr #1 {
start:
  %_0 = load i64, ptr %x, align 8
  ret i64 %_0
}

; Function Attrs: noinline nounwind
define i64 @abi_slice(ptr %x.0, i64 %x.1) unnamed_addr #1 {
start:
  ret i64 %x.1
}

; Function Attrs: noinline nounwind
define i64 @abi_stack_driver(i64 %a, i64 %b, i64 %c, i64 %d, i64 %e, i64 %f, i64 %g, i64 %h, i64 %i, i64 %j, i64 %k, i64 %l) unnamed_addr #1 {
start:
  %_13 = call i64 @abi_opaque_twelve(i64 %a, i64 %b, i64 %c, i64 %d, i64 %e, i64 %f, i64 %g, i64 %h, i64 %i, i64 %j, i64 %k, i64 %l) #4
  %_0.i = add i64 %_13, 1
  ret i64 %_0.i
}

; Function Attrs: noinline nounwind
define void @abi_system_big(ptr sret([24 x i8]) align 8 %_0, ptr align 8 %x) unnamed_addr #1 {
start:
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %x, i64 24, i1 false)
  ret void
}

; Function Attrs: noinline nounwind
define i64 @abi_system_narrow(i8 zeroext %x, i16 signext %y, i1 zeroext %flag) unnamed_addr #1 {
start:
  %_5 = zext i8 %x to i64
  %_7 = sext i16 %y to i64
  %_4 = xor i64 %_5, %_7
  %_8 = zext i1 %flag to i64
  %_0 = xor i64 %_4, %_8
  ret i64 %_0
}

; Function Attrs: noinline nounwind
define [2 x i64] @abi_system_pair([2 x i64] %0) unnamed_addr #1 {
start:
  %_0 = alloca [16 x i8], align 8
  %1 = alloca [16 x i8], align 8
  %x = alloca [16 x i8], align 8
  store [2 x i64] %0, ptr %1, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %x, ptr align 8 %1, i64 16, i1 false)
  %2 = load i64, ptr %x, align 8
  %3 = getelementptr inbounds i8, ptr %x, i64 8
  %4 = load i32, ptr %3, align 8
  store i64 %2, ptr %_0, align 8
  %5 = getelementptr inbounds i8, ptr %_0, i64 8
  store i32 %4, ptr %5, align 8
  %6 = load [2 x i64], ptr %_0, align 8
  ret [2 x i64] %6
}

; Function Attrs: noinline nounwind
define i64 @abi_track(i64 %x, ptr align 8 %0) unnamed_addr #1 {
start:
; call <core::panic::location::Location>::caller
  %_4 = call align 8 ptr @_RNvMs4_NtNtCsi86csyF5gCW_4core5panic8locationNtB5_8Location6callerCsjplKSa1E9lu_12abi_subjects(ptr align 8 %0) #5
; call <core::panic::location::Location>::line
  %_3 = call i32 @_RNvMs4_NtNtCsi86csyF5gCW_4core5panic8locationNtB5_8Location4lineCsjplKSa1E9lu_12abi_subjects(ptr align 8 %_4) #5
  %_2 = zext i32 %_3 to i64
  %_0 = xor i64 %x, %_2
  ret i64 %_0
}

; Function Attrs: noinline nounwind
define i64 @abi_unique(ptr align 8 %x) unnamed_addr #1 {
start:
  %_3 = load i64, ptr %x, align 8
  %_0.i = add i64 %_3, 1
  store i64 %_0.i, ptr %x, align 8
  %_0 = load i64, ptr %x, align 8
  ret i64 %_0
}

; Function Attrs: noinline nounwind
define void @abi_unit() unnamed_addr #1 {
start:
  ret void
}

; Function Attrs: noinline nounwind
define i64 @abi_vararg_driver(i32 %x, double %y) unnamed_addr #1 {
start:
  %_3 = call i64 (i32, ...) @abi_opaque_vararg(i32 1, i32 %x, double %y, ptr null) #4
  %_0.i = add i64 %_3, 1
  ret i64 %_0.i
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #2

; Function Attrs: nounwind
declare i64 @abi_opaque_twelve(i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) unnamed_addr #3

; Function Attrs: nounwind
declare i64 @abi_opaque_vararg(i32, ...) unnamed_addr #3

attributes #0 = { inlinehint nounwind "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #1 = { noinline nounwind "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #2 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #3 = { nounwind "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #4 = { nounwind }
attributes #5 = { inlinehint nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{!"rustc version 1.97.0-nightly (f53b654a8 2026-04-30)"}
