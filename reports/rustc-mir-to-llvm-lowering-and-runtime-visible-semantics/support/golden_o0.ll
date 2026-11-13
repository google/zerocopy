; ModuleID = 'golden_probe.12188cc1735cf2df-cgu.0'
source_filename = "golden_probe.12188cc1735cf2df-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@vtable.0 = private unnamed_addr constant <{ [24 x i8], ptr, ptr, ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @_RNSNvYNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0INtNtNtCskADBYZwJmSU_4core3ops8function6FnOnceuE9call_once6vtableCs1yk5BBwLqjP_12golden_probe, ptr @_RNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0Cs1yk5BBwLqjP_12golden_probe, ptr @_RNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0Cs1yk5BBwLqjP_12golden_probe }>, align 8, !guid !0
@alloc_e3a8563b75a1d71abe5cf72cb3563dbb = private unnamed_addr constant [16 x i8] c"golden_probe.rs\00", align 1, !guid !1
@alloc_1d8cbb8a5b8b3e42ca6a4db941805118 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_e3a8563b75a1d71abe5cf72cb3563dbb, [16 x i8] c"\0F\00\00\00\00\00\00\00\1C\00\00\00'\00\00\00" }>, align 8, !guid !2
@alloc_65344a484785545c114698177a455030 = private unnamed_addr constant [15 x i8] c"x out of bounds", align 1, !guid !3
@alloc_84abce7e49f60c62633cd38fe990d3ec = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_e3a8563b75a1d71abe5cf72cb3563dbb, [16 x i8] c"\0F\00\00\00\00\00\00\002\00\00\00\0D\00\00\00" }>, align 8, !guid !4

; std::rt::lang_start::<()>
; Function Attrs: nonlazybind uwtable
define hidden i64 @_RINvNtCs8ZKwes1zzDd_3std2rt10lang_startuECs1yk5BBwLqjP_12golden_probe(ptr %main, i64 %argc, ptr %argv, i8 %sigpipe) unnamed_addr #0 !guid !10 {
start:
  %_7 = alloca [8 x i8], align 8
  store ptr %main, ptr %_7, align 8
; call std::rt::lang_start_internal
  %_0 = call i64 @_RNvNtCs8ZKwes1zzDd_3std2rt19lang_start_internal(ptr %_7, ptr align 8 @vtable.0, i64 %argc, ptr %argv, i8 %sigpipe)
  ret i64 %_0
}

; std::sys::backtrace::__rust_begin_short_backtrace::<fn(), ()>
; Function Attrs: noinline nonlazybind uwtable
define internal void @_RINvNtNtCs8ZKwes1zzDd_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECs1yk5BBwLqjP_12golden_probe(ptr %f) unnamed_addr #1 !guid !11 {
start:
  %_2 = alloca [0 x i8], align 1
; call <fn() as core::ops::function::FnOnce<()>>::call_once
  call void @_RNvYFEuINtNtNtCskADBYZwJmSU_4core3ops8function6FnOnceuE9call_onceCs1yk5BBwLqjP_12golden_probe(ptr %f) #9
  call void asm sideeffect "", "~{memory}"(), !srcloc !12
  ret void
}

; std::rt::lang_start::<()>::{closure#0}
; Function Attrs: inlinehint nonlazybind uwtable
define internal i32 @_RNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0Cs1yk5BBwLqjP_12golden_probe(ptr align 8 %_1) unnamed_addr #2 !guid !13 {
start:
  %_4 = load ptr, ptr %_1, align 8
; call std::sys::backtrace::__rust_begin_short_backtrace::<fn(), ()>
  call void @_RINvNtNtCs8ZKwes1zzDd_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECs1yk5BBwLqjP_12golden_probe(ptr %_4) #10
; call <() as std::process::Termination>::report
  %self = call i8 @_RNvXsU_NtCs8ZKwes1zzDd_3std7processuNtB5_11Termination6reportCs1yk5BBwLqjP_12golden_probe() #9
  %_0 = zext i8 %self to i32
  ret i32 %_0
}

; <std::rt::lang_start<()>::{closure#0} as core::ops::function::FnOnce<()>>::call_once::{shim:vtable#0}
; Function Attrs: inlinehint nonlazybind uwtable
define internal i32 @_RNSNvYNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0INtNtNtCskADBYZwJmSU_4core3ops8function6FnOnceuE9call_once6vtableCs1yk5BBwLqjP_12golden_probe(ptr %_1) unnamed_addr #2 !guid !14 {
start:
  %_2 = alloca [0 x i8], align 1
  %0 = load ptr, ptr %_1, align 8
; call <std::rt::lang_start<()>::{closure#0} as core::ops::function::FnOnce<()>>::call_once
  %_0 = call i32 @_RNvYNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0INtNtNtCskADBYZwJmSU_4core3ops8function6FnOnceuE9call_onceCs1yk5BBwLqjP_12golden_probe(ptr %0) #9
  ret i32 %_0
}

; golden_probe::match_and_project
; Function Attrs: nonlazybind uwtable
define internal i32 @_RNvCs1yk5BBwLqjP_12golden_probe17match_and_project(ptr align 4 %c, ptr align 8 %p, ptr align 4 %slice.0, i64 %slice.1) unnamed_addr #0 !guid !15 {
start:
  %elem = alloca [4 x i8], align 4
  %base = alloca [4 x i8], align 4
  %0 = load i32, ptr %c, align 4
  %_5 = zext i32 %0 to i64
  switch i64 %_5, label %bb1 [
    i64 0, label %bb4
    i64 1, label %bb3
    i64 2, label %bb2
  ]

bb1:                                              ; preds = %start
  unreachable

bb4:                                              ; preds = %start
  store i32 0, ptr %base, align 4
  br label %bb6

bb3:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %c, i64 4
  %v = load i32, ptr %1, align 4
  store i32 %v, ptr %base, align 4
  br label %bb6

bb2:                                              ; preds = %start
  %2 = getelementptr inbounds i8, ptr %c, i64 4
  %x = load i32, ptr %2, align 4
  %3 = getelementptr inbounds i8, ptr %c, i64 8
  %y = load i32, ptr %3, align 4
  %_0.i2 = add i32 %x, %y
  store i32 %_0.i2, ptr %base, align 4
  br label %bb6

bb6:                                              ; preds = %bb2, %bb3, %bb4
; call <[u32]>::is_empty
  %_12 = call zeroext i1 @_RNvMNtCskADBYZwJmSU_4core5sliceSm8is_emptyCs1yk5BBwLqjP_12golden_probe(ptr align 4 %slice.0, i64 %slice.1) #9
  br i1 %_12, label %bb8, label %bb9

bb9:                                              ; preds = %bb6
  %_16 = icmp ult i64 0, %slice.1
  br i1 %_16, label %bb10, label %panic

bb8:                                              ; preds = %bb6
  store i32 0, ptr %elem, align 4
  br label %bb11

bb10:                                             ; preds = %bb9
  %4 = getelementptr inbounds nuw i32, ptr %slice.0, i64 0
  %5 = load i32, ptr %4, align 4
  store i32 %5, ptr %elem, align 4
  br label %bb11

panic:                                            ; preds = %bb9
; call core::panicking::panic_bounds_check
  call void @_RNvNtCskADBYZwJmSU_4core9panicking18panic_bounds_check(i64 0, i64 %slice.1, ptr align 8 @alloc_1d8cbb8a5b8b3e42ca6a4db941805118) #11
  unreachable

bb11:                                             ; preds = %bb8, %bb10
  %_18 = load i32, ptr %base, align 4
  %_19 = load i32, ptr %p, align 8
  %_0.i1 = add i32 %_18, %_19
  %_20 = load i32, ptr %elem, align 4
  %_0.i = add i32 %_0.i1, %_20
  ret i32 %_0.i
}

; golden_probe::intrinsics_and_abort
; Function Attrs: nonlazybind uwtable
define internal void @_RNvCs1yk5BBwLqjP_12golden_probe20intrinsics_and_abort(i1 zeroext %flag, ptr %src, ptr %dst) unnamed_addr #0 !guid !16 {
start:
; call <*const u32>::is_null
  %_7 = call zeroext i1 @_RNvMNtNtCskADBYZwJmSU_4core3ptr9const_ptrPm7is_nullCs1yk5BBwLqjP_12golden_probe(ptr %src) #9
  %_6 = xor i1 %_7, true
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %dst, ptr align 4 %src, i64 4, i1 false)
  br i1 %flag, label %bb3, label %bb2

bb2:                                              ; preds = %start
  call void @llvm.trap()
  unreachable

bb3:                                              ; preds = %start
  ret void
}

; golden_probe::checked_add_and_assert
; Function Attrs: nonlazybind uwtable
define internal i32 @_RNvCs1yk5BBwLqjP_12golden_probe22checked_add_and_assert(i32 %x, i32 %y, ptr align 8 %0) unnamed_addr #0 !guid !17 {
start:
  %_4 = icmp ult i32 %x, 10000
  br i1 %_4, label %bb1, label %bb2

bb2:                                              ; preds = %start
; call <core::fmt::Arguments>::from_str
  %1 = call { ptr, ptr } @_RNvMs4_NtCskADBYZwJmSU_4core3fmtNtB5_9Arguments8from_strCs1yk5BBwLqjP_12golden_probe(ptr @alloc_65344a484785545c114698177a455030, i64 15) #9
  %_8.0 = extractvalue { ptr, ptr } %1, 0
  %_8.1 = extractvalue { ptr, ptr } %1, 1
; call core::panicking::panic_fmt
  call void @_RNvNtCskADBYZwJmSU_4core9panicking9panic_fmt(ptr %_8.0, ptr %_8.1, ptr align 8 %0) #11
  unreachable

bb1:                                              ; preds = %start
  %_11.0 = add i32 %x, %y
  %_11.1 = icmp ult i32 %_11.0, %x
  br i1 %_11.1, label %panic, label %bb4

bb4:                                              ; preds = %bb1
  ret i32 %_11.0

panic:                                            ; preds = %bb1
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCskADBYZwJmSU_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 %0) #11
  unreachable
}

; golden_probe::main
; Function Attrs: nonlazybind uwtable
define hidden void @_RNvCs1yk5BBwLqjP_12golden_probe4main() unnamed_addr #0 !guid !18 {
start:
  %out = alloca [4 x i8], align 4
  %_6 = alloca [12 x i8], align 4
  %arr = alloca [8 x i8], align 4
  %p = alloca [16 x i8], align 8
  store i128 166020696663385964547, ptr %p, align 8
  %0 = getelementptr inbounds nuw i32, ptr %arr, i64 0
  store i32 4, ptr %0, align 4
  %1 = getelementptr inbounds nuw i32, ptr %arr, i64 1
  store i32 5, ptr %1, align 4
; call golden_probe::checked_add_and_assert
  %_4 = call i32 @_RNvCs1yk5BBwLqjP_12golden_probe22checked_add_and_assert(i32 10, i32 20, ptr align 8 @alloc_84abce7e49f60c62633cd38fe990d3ec)
  %2 = getelementptr inbounds i8, ptr %_6, i64 4
  store i32 7, ptr %2, align 4
  store i32 1, ptr %_6, align 4
; call golden_probe::match_and_project
  %_5 = call i32 @_RNvCs1yk5BBwLqjP_12golden_probe17match_and_project(ptr align 4 %_6, ptr align 8 %p, ptr align 4 %arr, i64 2)
  %_12.0 = add i32 %_4, %_5
  %_12.1 = icmp ult i32 %_12.0, %_4
  br i1 %_12.1, label %panic, label %bb3

bb3:                                              ; preds = %start
  store i32 0, ptr %out, align 4
  %_15 = icmp ugt i32 %_12.0, 0
; call golden_probe::intrinsics_and_abort
  call void @_RNvCs1yk5BBwLqjP_12golden_probe20intrinsics_and_abort(i1 zeroext %_15, ptr %arr, ptr %out)
  ret void

panic:                                            ; preds = %start
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCskADBYZwJmSU_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_84abce7e49f60c62633cd38fe990d3ec) #11
  unreachable
}

; <[u32]>::is_empty
; Function Attrs: inlinehint nonlazybind uwtable
define internal zeroext i1 @_RNvMNtCskADBYZwJmSU_4core5sliceSm8is_emptyCs1yk5BBwLqjP_12golden_probe(ptr align 4 %self.0, i64 %self.1) unnamed_addr #2 !guid !19 {
start:
  %_0 = icmp eq i64 %self.1, 0
  ret i1 %_0
}

; <*const u32>::is_null
; Function Attrs: inlinehint nonlazybind uwtable
define internal zeroext i1 @_RNvMNtNtCskADBYZwJmSU_4core3ptr9const_ptrPm7is_nullCs1yk5BBwLqjP_12golden_probe(ptr %self) unnamed_addr #2 !guid !20 {
start:
  %_3 = ptrtoint ptr %self to i64
  %_0 = icmp eq i64 %_3, 0
  ret i1 %_0
}

; <core::fmt::Arguments>::from_str
; Function Attrs: inlinehint nonlazybind uwtable
define internal { ptr, ptr } @_RNvMs4_NtCskADBYZwJmSU_4core3fmtNtB5_9Arguments8from_strCs1yk5BBwLqjP_12golden_probe(ptr %s.0, i64 %s.1) unnamed_addr #2 !guid !21 {
start:
  %_6 = shl i64 %s.1, 1
  %_5 = or i64 %_6, 1
  %_4 = inttoptr i64 %_5 to ptr
  %0 = insertvalue { ptr, ptr } poison, ptr %s.0, 0
  %1 = insertvalue { ptr, ptr } %0, ptr %_4, 1
  ret { ptr, ptr } %1
}

; <() as std::process::Termination>::report
; Function Attrs: inlinehint nonlazybind uwtable
define internal i8 @_RNvXsU_NtCs8ZKwes1zzDd_3std7processuNtB5_11Termination6reportCs1yk5BBwLqjP_12golden_probe() unnamed_addr #2 !guid !22 {
start:
  ret i8 0
}

; <fn() as core::ops::function::FnOnce<()>>::call_once
; Function Attrs: inlinehint nonlazybind uwtable
define internal void @_RNvYFEuINtNtNtCskADBYZwJmSU_4core3ops8function6FnOnceuE9call_onceCs1yk5BBwLqjP_12golden_probe(ptr %_1) unnamed_addr #2 !guid !23 {
start:
  %_2 = alloca [0 x i8], align 1
  call void %_1()
  ret void
}

; <std::rt::lang_start<()>::{closure#0} as core::ops::function::FnOnce<()>>::call_once
; Function Attrs: inlinehint nonlazybind uwtable
define internal i32 @_RNvYNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0INtNtNtCskADBYZwJmSU_4core3ops8function6FnOnceuE9call_onceCs1yk5BBwLqjP_12golden_probe(ptr %0) unnamed_addr #2 personality ptr @rust_eh_personality !guid !24 {
start:
  %_2 = alloca [0 x i8], align 1
  %_1 = alloca [8 x i8], align 8
  store ptr %0, ptr %_1, align 8
; call std::rt::lang_start::<()>::{closure#0}
  %_0 = call i32 @_RNCINvNtCs8ZKwes1zzDd_3std2rt10lang_startuE0Cs1yk5BBwLqjP_12golden_probe(ptr align 8 %_1) #9
  br label %bb1

bb1:                                              ; preds = %start
  ret i32 %_0

bb3:                                              ; No predecessors!
  unreachable

bb4:                                              ; No predecessors!
  unreachable
}

; std::rt::lang_start_internal
; Function Attrs: nonlazybind uwtable
declare i64 @_RNvNtCs8ZKwes1zzDd_3std2rt19lang_start_internal(ptr, ptr align 8, i64, ptr, i8) unnamed_addr #0

; core::panicking::panic_bounds_check
; Function Attrs: cold minsize noinline noreturn nonlazybind optsize uwtable
declare void @_RNvNtCskADBYZwJmSU_4core9panicking18panic_bounds_check(i64, i64, ptr align 8) unnamed_addr #3

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #4

; Function Attrs: cold noreturn nounwind memory(inaccessiblemem: write)
declare void @llvm.trap() #5

; core::panicking::panic_fmt
; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @_RNvNtCskADBYZwJmSU_4core9panicking9panic_fmt(ptr, ptr, ptr align 8) unnamed_addr #6

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @_RNvNtNtCskADBYZwJmSU_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8) unnamed_addr #6

; Function Attrs: nounwind nonlazybind uwtable
declare i32 @rust_eh_personality(i32, i32, i64, ptr, ptr) unnamed_addr #7

; Function Attrs: nonlazybind
define i32 @main(i32 %0, ptr %1) unnamed_addr #8 !guid !25 {
top:
  %2 = sext i32 %0 to i64
; call std::rt::lang_start::<()>
  %3 = call i64 @_RINvNtCs8ZKwes1zzDd_3std2rt10lang_startuECs1yk5BBwLqjP_12golden_probe(ptr @_RNvCs1yk5BBwLqjP_12golden_probe4main, i64 %2, ptr %1, i8 0)
  %4 = trunc i64 %3 to i32
  ret i32 %4
}

attributes #0 = { nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { noinline nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { inlinehint nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { cold minsize noinline noreturn nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { cold noreturn nounwind memory(inaccessiblemem: write) }
attributes #6 = { cold noinline noreturn nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #7 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #8 = { nonlazybind "target-cpu"="x86-64" }
attributes #9 = { inlinehint }
attributes #10 = { noinline }
attributes #11 = { noinline noreturn }

!llvm.module.flags = !{!5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = !{i64 1538591720630931076}
!1 = !{i64 -7439888551137281444}
!2 = !{i64 6301982152630530319}
!3 = !{i64 4956474343508070580}
!4 = !{i64 8013115721943523123}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 2, !"RtLibUseGOT", i32 1}
!8 = !{i32 7, !"uwtable", i32 2}
!9 = !{!"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"}
!10 = !{i64 -786874741756462341}
!11 = !{i64 6163128561527194387}
!12 = !{i64 13347014602353383}
!13 = !{i64 6777388979413742723}
!14 = !{i64 4832502800090044325}
!15 = !{i64 2570354906863965338}
!16 = !{i64 -8693188619919993011}
!17 = !{i64 7404670357162747429}
!18 = !{i64 -578921095667901185}
!19 = !{i64 -8455240095390839595}
!20 = !{i64 6530385196728261408}
!21 = !{i64 -8061739290264863520}
!22 = !{i64 1524001450718518803}
!23 = !{i64 -5722581931631226450}
!24 = !{i64 -1420165833465973279}
!25 = !{i64 -2624081020897602054}
