; ModuleID = 'startup_probe.fcf1f915dc1860a0-cgu.0'
source_filename = "startup_probe.fcf1f915dc1860a0-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@vtable.0 = private unnamed_addr constant <{ [24 x i8], ptr, ptr, ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @_RNSNvYNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0INtNtNtCskADBYZwJmSU_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe, ptr @_RNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe, ptr @_RNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe }>, align 8, !guid !0
@alloc_dea25bd652bc4349bac428c742353f74 = private unnamed_addr constant [14 x i8] c"hello startup\0A", align 1, !guid !1

; std::rt::lang_start::<()>
; Function Attrs: nonlazybind uwtable
define hidden noundef i64 @_RINvNtCs8ZKwes1zzDd_3std2rt10lang_startuECslIq7RLtFujA_13startup_probe(ptr noundef nonnull %main, i64 noundef %argc, ptr noundef %argv, i8 noundef %sigpipe) unnamed_addr #0 !guid !7 {
start:
  %_7 = alloca [8 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %_7)
  store ptr %main, ptr %_7, align 8
; call std::rt::lang_start_internal
  %_0 = call noundef i64 @_RNvNtCs8ZKwes1zzDd_3std2rt19lang_start_internal(ptr noundef nonnull %_7, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(48) @vtable.0, i64 noundef %argc, ptr noundef %argv, i8 noundef %sigpipe)
  call void @llvm.lifetime.end.p0(ptr nonnull %_7)
  ret i64 %_0
}

; std::sys::backtrace::__rust_begin_short_backtrace::<fn(), ()>
; Function Attrs: noinline nonlazybind uwtable
define internal fastcc void @_RINvNtNtCs8ZKwes1zzDd_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe(ptr nofree noundef nonnull readonly captures(none) %f) unnamed_addr #1 !guid !8 {
start:
  tail call void %f(), !inline_history !9
  tail call void asm sideeffect "", "~{memory}"() #6, !srcloc !10
  ret void
}

; std::rt::lang_start::<()>::{closure#0}
; Function Attrs: inlinehint nonlazybind uwtable
define internal noundef i32 @_RNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe(ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(8) %_1) unnamed_addr #2 !guid !11 {
start:
  %_4 = load ptr, ptr %_1, align 8, !nonnull !12, !noundef !12
; call std::sys::backtrace::__rust_begin_short_backtrace::<fn(), ()>
  tail call fastcc void @_RINvNtNtCs8ZKwes1zzDd_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe(ptr noundef nonnull %_4) #7
  ret i32 0
}

; <std::rt::lang_start<()>::{closure#0} as core::ops::function::FnOnce<()>>::call_once::{shim:vtable#0}
; Function Attrs: inlinehint nonlazybind uwtable
define internal noundef i32 @_RNSNvYNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0INtNtNtCskADBYZwJmSU_4core3ops8function6FnOnceuE9call_once6vtableCslIq7RLtFujA_13startup_probe(ptr nofree noundef readonly captures(none) %_1) unnamed_addr #2 personality ptr @rust_eh_personality !guid !13 {
start:
  %0 = load ptr, ptr %_1, align 8, !nonnull !12, !noundef !12
; call std::sys::backtrace::__rust_begin_short_backtrace::<fn(), ()>
  tail call fastcc void @_RINvNtNtCs8ZKwes1zzDd_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECslIq7RLtFujA_13startup_probe(ptr noundef nonnull readonly %0) #7, !noalias !14
  ret i32 0
}

; startup_probe::main
; Function Attrs: nonlazybind uwtable
define hidden void @_RNvCslIq7RLtFujA_13startup_probe4main() unnamed_addr #0 !guid !17 {
start:
; call std::io::stdio::_print
  tail call void @_RNvNtNtCs8ZKwes1zzDd_3std2io5stdio6__print(ptr noundef nonnull @alloc_dea25bd652bc4349bac428c742353f74, ptr noundef nonnull inttoptr (i64 29 to ptr))
  ret void
}

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #3

; std::rt::lang_start_internal
; Function Attrs: nonlazybind uwtable
declare noundef i64 @_RNvNtCs8ZKwes1zzDd_3std2rt19lang_start_internal(ptr noundef nonnull, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(48), i64 noundef, ptr noundef, i8 noundef) unnamed_addr #0

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #3

; std::io::stdio::_print
; Function Attrs: nonlazybind uwtable
declare void @_RNvNtNtCs8ZKwes1zzDd_3std2io5stdio6__print(ptr noundef nonnull, ptr noundef nonnull) unnamed_addr #0

; Function Attrs: nounwind nonlazybind uwtable
declare noundef range(i32 0, 10) i32 @rust_eh_personality(i32 noundef, i32 noundef, i64 noundef, ptr noundef, ptr noundef) unnamed_addr #4

; Function Attrs: nonlazybind
define noundef i32 @main(i32 %0, ptr %1) unnamed_addr #5 !guid !18 {
top:
  %_7.i = alloca [8 x i8], align 8
  %2 = sext i32 %0 to i64
  call void @llvm.lifetime.start.p0(ptr nonnull %_7.i)
  store ptr @_RNvCslIq7RLtFujA_13startup_probe4main, ptr %_7.i, align 8
; call std::rt::lang_start_internal
  %_0.i = call noundef i64 @_RNvNtCs8ZKwes1zzDd_3std2rt19lang_start_internal(ptr noundef nonnull %_7.i, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(48) @vtable.0, i64 noundef %2, ptr noundef %1, i8 noundef 0)
  call void @llvm.lifetime.end.p0(ptr nonnull %_7.i)
  %3 = trunc i64 %_0.i to i32
  ret i32 %3
}

attributes #0 = { nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { noinline nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { inlinehint nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #4 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #5 = { nonlazybind "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #6 = { nounwind }
attributes #7 = { noinline }

!llvm.module.flags = !{!2, !3, !4, !5}
!llvm.ident = !{!6}

!0 = !{i64 -6152417765979872687}
!1 = !{i64 6874774668876096691}
!2 = !{i32 8, !"PIC Level", i32 2}
!3 = !{i32 7, !"PIE Level", i32 2}
!4 = !{i32 2, !"RtLibUseGOT", i32 1}
!5 = !{i32 7, !"uwtable", i32 2}
!6 = !{!"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"}
!7 = !{i64 6187716739543115054}
!8 = !{i64 -7626041775494668844}
!9 = distinct !{null}
!10 = !{i64 5611838629998541}
!11 = !{i64 3371453792084001043}
!12 = !{}
!13 = !{i64 8870575970445900029}
!14 = !{!15}
!15 = distinct !{!15, !16, !"_RNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe: %_1"}
!16 = distinct !{!16, !"_RNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0CslIq7RLtFujA_13startup_probe"}
!17 = !{i64 5071101643614678191}
!18 = !{i64 -2624081020897602054}
