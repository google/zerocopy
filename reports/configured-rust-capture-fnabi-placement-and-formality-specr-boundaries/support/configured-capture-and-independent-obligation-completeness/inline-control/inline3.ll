; ModuleID = 'inline.29be407425b66a3-cgu.0'
source_filename = "inline.29be407425b66a3-cgu.0"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "arm64-apple-macosx11.0.0"

@vtable.0 = private unnamed_addr constant <{ [24 x i8], ptr, ptr, ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00", ptr @_RNSNvYNCINvNtCs1SSuMAdGM58_3std2rt10lang_startuE0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_once6vtableCsdT136XbhqV_6inline, ptr @_RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startuE0CsdT136XbhqV_6inline, ptr @_RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startuE0CsdT136XbhqV_6inline }>, align 8, !guid !0
@vtable.1 = private unnamed_addr constant <{ [24 x i8], ptr, ptr, ptr }> <{ [24 x i8] c"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01\00\00\00\00\00\00\00", ptr @_RNSNvYNCNvCsdT136XbhqV_6inline4main0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceTRNtNtCs1SSuMAdGM58_3std5panic13PanicHookInfoEE9call_once6vtableB8_, ptr @_RNCNvCsdT136XbhqV_6inline4main0B3_, ptr @_RNCNvCsdT136XbhqV_6inline4main0B3_ }>, align 8, !guid !1
@alloc_43fa7d350c43388be7b948b5f9d284a1 = private unnamed_addr constant [73 x i8] c"inputs=256;callee_failure_preserved=1;successful_result=7;all_match=true\0A", align 1, !guid !2
@alloc_c249215ed965e65873a409de62ba0710 = private unnamed_addr constant [46 x i8] c"work/research/parent/inline-control/inline.rs\00", align 1, !guid !3
@alloc_914b2c69d7eca30497b9feaf15ac92f1 = private unnamed_addr constant [1 x i8] zeroinitializer, align 1, !guid !4
@alloc_6db4f1a17b367c3a1db3117e52086a5a = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_c249215ed965e65873a409de62ba0710, [16 x i8] c"-\00\00\00\00\00\00\00\03\00\00\00\8C\00\00\00" }>, align 8, !guid !5
@alloc_09550ab97c37fcb91c47d068ab3fdf81 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_c249215ed965e65873a409de62ba0710, [16 x i8] c"-\00\00\00\00\00\00\00\03\00\00\00\B7\00\00\00" }>, align 8, !guid !6
@alloc_26b08ca1aba9231e7107a958b8f064b4 = private unnamed_addr constant [26 x i8] c"intentional callee failure", align 1, !guid !7
@alloc_e04a3fb0cf0949bf22815cf6203f64b9 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_c249215ed965e65873a409de62ba0710, [16 x i8] c"-\00\00\00\00\00\00\00\01\00\00\001\00\00\00" }>, align 8, !guid !8

; std::rt::lang_start::<()>
; Function Attrs: uwtable
define hidden noundef i64 @_RINvNtCs1SSuMAdGM58_3std2rt10lang_startuECsdT136XbhqV_6inline(ptr noundef nonnull %main, i64 noundef %argc, ptr noundef %argv, i8 noundef %sigpipe) unnamed_addr #0 !guid !14 {
start:
  %_7 = alloca [8 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %_7)
  store ptr %main, ptr %_7, align 8
; call std::rt::lang_start_internal
  %_0 = call noundef i64 @_RNvNtCs1SSuMAdGM58_3std2rt19lang_start_internal(ptr noundef nonnull %_7, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(48) @vtable.0, i64 noundef %argc, ptr noundef %argv, i8 noundef %sigpipe)
  call void @llvm.lifetime.end.p0(ptr nonnull %_7)
  ret i64 %_0
}

; std::sys::backtrace::__rust_begin_short_backtrace::<fn(), ()>
; Function Attrs: noinline uwtable
define internal fastcc void @_RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECsdT136XbhqV_6inline(ptr nofree noundef nonnull readonly captures(none) %f) unnamed_addr #1 !guid !15 {
start:
  tail call void %f(), !inline_history !16
  tail call void asm sideeffect "", "~{memory}"() #13, !srcloc !17
  ret void
}

; std::rt::lang_start::<()>::{closure#0}
; Function Attrs: inlinehint uwtable
define internal noundef i32 @_RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startuE0CsdT136XbhqV_6inline(ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(8) %_1) unnamed_addr #2 !guid !18 {
start:
  %_4 = load ptr, ptr %_1, align 8, !nonnull !19, !noundef !19
; call std::sys::backtrace::__rust_begin_short_backtrace::<fn(), ()>
  tail call fastcc void @_RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECsdT136XbhqV_6inline(ptr noundef nonnull %_4) #14
  ret i32 0
}

; inline::main::{closure#0}
; Function Attrs: inlinehint mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define internal void @_RNCNvCsdT136XbhqV_6inline4main0B3_(ptr noalias nofree nonnull readonly captures(none) %_1, ptr noalias nofree readonly align 8 captures(none) %_2) unnamed_addr #3 !guid !20 {
start:
  ret void
}

; <std::rt::lang_start<()>::{closure#0} as core::ops::function::FnOnce<()>>::call_once::{shim:vtable#0}
; Function Attrs: inlinehint uwtable
define internal noundef i32 @_RNSNvYNCINvNtCs1SSuMAdGM58_3std2rt10lang_startuE0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceuE9call_once6vtableCsdT136XbhqV_6inline(ptr nofree noundef readonly captures(none) %_1) unnamed_addr #2 personality ptr @rust_eh_personality !guid !21 {
start:
  %0 = load ptr, ptr %_1, align 8, !nonnull !19, !noundef !19
; call std::sys::backtrace::__rust_begin_short_backtrace::<fn(), ()>
  tail call fastcc void @_RINvNtNtCs1SSuMAdGM58_3std3sys9backtrace28___rust_begin_short_backtraceFEuuECsdT136XbhqV_6inline(ptr noundef nonnull readonly %0) #14, !noalias !22
  ret i32 0
}

; <inline::main::{closure#0} as core::ops::function::FnOnce<(&std::panic::PanicHookInfo,)>>::call_once::{shim:vtable#0}
; Function Attrs: inlinehint mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define internal void @_RNSNvYNCNvCsdT136XbhqV_6inline4main0INtNtNtCsjIpoRzUjyHQ_4core3ops8function6FnOnceTRNtNtCs1SSuMAdGM58_3std5panic13PanicHookInfoEE9call_once6vtableB8_(ptr nofree readnone captures(none) %_1, ptr noalias nofree readonly align 8 captures(none) %0) unnamed_addr #3 personality ptr @rust_eh_personality !guid !25 {
start:
  ret void
}

; inline::main
; Function Attrs: uwtable
define hidden void @_RNvCsdT136XbhqV_6inline4main() unnamed_addr #0 personality ptr @rust_eh_personality !guid !26 {
start:
  %x = alloca [1 x i8], align 1
; call std::panicking::set_hook
  tail call void @_RNvNtCs1SSuMAdGM58_3std9panicking8set_hook(ptr noundef nonnull inttoptr (i64 1 to ptr), ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(48) @vtable.1)
  call void @llvm.lifetime.start.p0(ptr nonnull %x)
  store i8 0, ptr %x, align 1
; invoke inline::caller
  invoke fastcc void @_RNvCsdT136XbhqV_6inline6caller(i8 noundef 0) #14
          to label %bb10 unwind label %catch.i.peel

catch.i.peel:                                     ; preds = %start
  %0 = landingpad { ptr, i32 }
          catch ptr null
  %1 = extractvalue { ptr, i32 } %0, 0
; invoke std::panicking::catch_unwind::cleanup
  %2 = invoke { ptr, ptr } @_RNvNvNtCs1SSuMAdGM58_3std9panicking12catch_unwind7cleanup(ptr noundef %1)
          to label %bb26.peel unwind label %terminate.i.i.loopexit.split-lp

bb26.peel:                                        ; preds = %catch.i.peel
  %obj.0.i.i.peel = extractvalue { ptr, ptr } %2, 0
  %obj.1.i.i.peel = extractvalue { ptr, ptr } %2, 1
  call void @llvm.assume(i1 true) [ "nonnull"(ptr %obj.0.i.i.peel) ]
  call void @llvm.assume(i1 true) [ "nonnull"(ptr %obj.1.i.i.peel) ]
  %3 = load ptr, ptr %obj.1.i.i.peel, align 8, !invariant.load !19
  %.not.i.i7.peel = icmp eq ptr %3, null
  br i1 %.not.i.i7.peel, label %bb3.i.i14.peel, label %is_not_null.i.i8.peel

is_not_null.i.i8.peel:                            ; preds = %bb26.peel
  invoke void %3(ptr noundef nonnull %obj.0.i.i.peel)
          to label %bb3.i.i14.peel unwind label %cleanup.i.i9.loopexit.split-lp

bb3.i.i14.peel:                                   ; preds = %is_not_null.i.i8.peel, %bb26.peel
  %4 = getelementptr inbounds nuw i8, ptr %obj.1.i.i.peel, i64 8
  %size.i.i.i15.peel = load i64, ptr %4, align 8, !range !27, !invariant.load !19
  %5 = icmp eq i64 %size.i.i.i15.peel, 0
  br i1 %5, label %_RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtB4_6result6ResulthINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EEECsdT136XbhqV_6inline.exit18.peel, label %bb1.i.i.i16.peel

bb1.i.i.i16.peel:                                 ; preds = %bb3.i.i14.peel
  %6 = getelementptr inbounds nuw i8, ptr %obj.1.i.i.peel, i64 16
  %align.i.i.i17.peel = load i64, ptr %6, align 8, !range !28, !invariant.load !19
; call __rustc::__rust_dealloc
  tail call void @_RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc(ptr noundef nonnull %obj.0.i.i.peel, i64 noundef range(i64 1, -9223372036854775808) %size.i.i.i15.peel, i64 noundef range(i64 1, 536870913) %align.i.i.i17.peel) #13
  br label %_RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtB4_6result6ResulthINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EEECsdT136XbhqV_6inline.exit18.peel

_RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtB4_6result6ResulthINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EEECsdT136XbhqV_6inline.exit18.peel: ; preds = %bb1.i.i.i16.peel, %bb3.i.i14.peel
  call void @llvm.lifetime.end.p0(ptr nonnull %x)
  br label %bb6

bb6:                                              ; preds = %_RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtB4_6result6ResulthINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EEECsdT136XbhqV_6inline.exit18.peel, %_RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtB4_6result6ResulthINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EEECsdT136XbhqV_6inline.exit18
  %iter.sroa.5.066 = phi i8 [ 1, %_RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtB4_6result6ResulthINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EEECsdT136XbhqV_6inline.exit18.peel ], [ %8, %_RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtB4_6result6ResulthINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EEECsdT136XbhqV_6inline.exit18 ]
  %7 = icmp eq i8 %iter.sroa.5.066, -1
  %8 = add nuw i8 %iter.sroa.5.066, 1
  call void @llvm.lifetime.start.p0(ptr nonnull %x)
  store i8 %iter.sroa.5.066, ptr %x, align 1
; invoke inline::caller
  invoke fastcc void @_RNvCsdT136XbhqV_6inline6caller(i8 noundef %iter.sroa.5.066) #14
          to label %_RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtB4_6result6ResulthINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EEECsdT136XbhqV_6inline.exit18 unwind label %catch.i

catch.i:                                          ; preds = %bb6
  %9 = landingpad { ptr, i32 }
          catch ptr null
  %10 = extractvalue { ptr, i32 } %9, 0
; invoke std::panicking::catch_unwind::cleanup
  %11 = invoke { ptr, ptr } @_RNvNvNtCs1SSuMAdGM58_3std9panicking12catch_unwind7cleanup(ptr noundef %10)
          to label %bb15.loopexit unwind label %terminate.i.i.loopexit.split-lp

terminate.i.i.loopexit.split-lp:                  ; preds = %catch.i, %catch.i.peel
  %lpad.loopexit.split-lp = landingpad { ptr, i32 }
          filter [0 x ptr] zeroinitializer
; call core::panicking::panic_cannot_unwind
  tail call void @_RNvNtCsjIpoRzUjyHQ_4core9panicking19panic_cannot_unwind() #15
  unreachable

bb18:                                             ; preds = %_RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtB4_6result6ResulthINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EEECsdT136XbhqV_6inline.exit18
; call std::io::stdio::_print
  tail call void @_RNvNtNtCs1SSuMAdGM58_3std2io5stdio6__print(ptr noundef nonnull @alloc_43fa7d350c43388be7b948b5f9d284a1, ptr noundef nonnull inttoptr (i64 147 to ptr))
  ret void

bb10:                                             ; preds = %start
; call core::panicking::assert_failed::<u8, u8>
  call void @_RINvNtCsjIpoRzUjyHQ_4core9panicking13assert_failedhhECs1SSuMAdGM58_3std(i8 noundef 1, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) dereferenceable(1) %x, ptr noalias nofree noundef readonly captures(address, read_provenance) dereferenceable(1) @alloc_914b2c69d7eca30497b9feaf15ac92f1, ptr noundef null, ptr undef, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_6db4f1a17b367c3a1db3117e52086a5a) #16
  unreachable

bb2.i5:                                           ; preds = %bb15.loopexit
  %lpad.thr_comm.split-lp = landingpad { ptr, i32 }
          cleanup
  %12 = load ptr, ptr %obj.1.i.i, align 8, !invariant.load !19
  %.not.i.i = icmp eq ptr %12, null
  br i1 %.not.i.i, label %bb3.i.i, label %is_not_null.i.i

is_not_null.i.i:                                  ; preds = %bb2.i5
  invoke void %12(ptr noundef nonnull %obj.0.i.i)
          to label %bb3.i.i unwind label %cleanup.i.i

bb3.i.i:                                          ; preds = %is_not_null.i.i, %bb2.i5
  %13 = getelementptr inbounds nuw i8, ptr %obj.1.i.i, i64 8
  %size.i.i.i = load i64, ptr %13, align 8, !range !27, !invariant.load !19
  %14 = icmp eq i64 %size.i.i.i, 0
  br i1 %14, label %common.resume, label %bb1.i.i.i

bb1.i.i.i:                                        ; preds = %bb3.i.i
  %15 = getelementptr inbounds nuw i8, ptr %obj.1.i.i, i64 16
  %align.i.i.i = load i64, ptr %15, align 8, !range !28, !invariant.load !19
; call __rustc::__rust_dealloc
  call void @_RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc(ptr noundef nonnull %obj.0.i.i, i64 noundef range(i64 1, -9223372036854775808) %size.i.i.i, i64 noundef range(i64 1, 536870913) %align.i.i.i) #13
  br label %common.resume

cleanup.i.i:                                      ; preds = %is_not_null.i.i
  %16 = landingpad { ptr, i32 }
          filter [0 x ptr] zeroinitializer
  %17 = getelementptr inbounds nuw i8, ptr %obj.1.i.i, i64 8
  %size.i4.i.i = load i64, ptr %17, align 8, !range !27, !invariant.load !19
  %18 = icmp eq i64 %size.i4.i.i, 0
  br i1 %18, label %terminate.body, label %bb1.i5.i.i

bb1.i5.i.i:                                       ; preds = %cleanup.i.i
  %19 = getelementptr inbounds nuw i8, ptr %obj.1.i.i, i64 16
  %align.i6.i.i = load i64, ptr %19, align 8, !range !28, !invariant.load !19
; call __rustc::__rust_dealloc
  call void @_RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc(ptr noundef nonnull %obj.0.i.i, i64 noundef range(i64 1, -9223372036854775808) %size.i4.i.i, i64 noundef range(i64 1, 536870913) %align.i6.i.i) #13
  br label %terminate.body

unreachable:                                      ; preds = %bb15.loopexit
  unreachable

cleanup.i.i9.loopexit.split-lp:                   ; preds = %is_not_null.i.i8.peel
  %lpad.loopexit.split-lp78 = landingpad { ptr, i32 }
          cleanup
  %20 = getelementptr inbounds nuw i8, ptr %obj.1.i.i.peel, i64 8
  %size.i4.i.i10 = load i64, ptr %20, align 8, !range !27, !invariant.load !19
  %21 = icmp eq i64 %size.i4.i.i10, 0
  br i1 %21, label %common.resume, label %bb1.i5.i.i11

bb1.i5.i.i11:                                     ; preds = %cleanup.i.i9.loopexit.split-lp
  %22 = getelementptr inbounds nuw i8, ptr %obj.1.i.i.peel, i64 16
  %align.i6.i.i12 = load i64, ptr %22, align 8, !range !28, !invariant.load !19
; call __rustc::__rust_dealloc
  tail call void @_RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc(ptr noundef nonnull %obj.0.i.i.peel, i64 noundef range(i64 1, -9223372036854775808) %size.i4.i.i10, i64 noundef range(i64 1, 536870913) %align.i6.i.i12) #13
  br label %common.resume

common.resume:                                    ; preds = %bb3.i.i, %bb1.i.i.i, %cleanup.i.i9.loopexit.split-lp, %bb1.i5.i.i11
  %common.resume.op = phi { ptr, i32 } [ %lpad.loopexit.split-lp78, %cleanup.i.i9.loopexit.split-lp ], [ %lpad.loopexit.split-lp78, %bb1.i5.i.i11 ], [ %lpad.thr_comm.split-lp, %bb3.i.i ], [ %lpad.thr_comm.split-lp, %bb1.i.i.i ]
  resume { ptr, i32 } %common.resume.op

_RINvNtCsjIpoRzUjyHQ_4core3ptr9drop_glueINtNtB4_6result6ResulthINtNtCs6zY7rJBZy9D_5alloc5boxed3BoxDNtNtB4_3any3AnyNtNtB4_6marker4SendEL_EEECsdT136XbhqV_6inline.exit18: ; preds = %bb6
  call void @llvm.lifetime.end.p0(ptr nonnull %x)
  br i1 %7, label %bb18, label %bb6, !llvm.loop !29

bb15.loopexit:                                    ; preds = %catch.i
  %obj.1.i.i = extractvalue { ptr, ptr } %11, 1
  %obj.0.i.i = extractvalue { ptr, ptr } %11, 0
; invoke core::panicking::assert_failed::<u8, u8>
  invoke void @_RINvNtCsjIpoRzUjyHQ_4core9panicking13assert_failedhhECs1SSuMAdGM58_3std(i8 noundef 0, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) dereferenceable(1) %x, ptr noalias nofree noundef readonly captures(address, read_provenance) dereferenceable(1) @alloc_914b2c69d7eca30497b9feaf15ac92f1, ptr noundef null, ptr undef, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_09550ab97c37fcb91c47d068ab3fdf81) #16
          to label %unreachable unwind label %bb2.i5

terminate.body:                                   ; preds = %cleanup.i.i, %bb1.i5.i.i
; call core::panicking::panic_in_cleanup
  call void @_RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup() #15
  unreachable
}

; inline::caller
; Function Attrs: noinline uwtable
define internal fastcc void @_RNvCsdT136XbhqV_6inline6caller(i8 noundef %x) unnamed_addr #1 !guid !31 {
start:
  %0 = icmp eq i8 %x, 0
  br i1 %0, label %bb1, label %bb2, !prof !32

bb1:                                              ; preds = %start
; call core::panicking::panic_fmt
  tail call void @_RNvNtCsjIpoRzUjyHQ_4core9panicking9panic_fmt(ptr noundef nonnull @alloc_26b08ca1aba9231e7107a958b8f064b4, ptr noundef nonnull inttoptr (i64 53 to ptr), ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_e04a3fb0cf0949bf22815cf6203f64b9) #17
  unreachable

bb2:                                              ; preds = %start
  ret void
}

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #4

; std::rt::lang_start_internal
; Function Attrs: uwtable
declare noundef i64 @_RNvNtCs1SSuMAdGM58_3std2rt19lang_start_internal(ptr noundef nonnull, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(48), i64 noundef, ptr noundef, i8 noundef) unnamed_addr #0

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #4

; Function Attrs: nounwind uwtable
declare noundef range(i32 0, 10) i32 @rust_eh_personality(i32 noundef, i32 noundef, i64 noundef, ptr noundef, ptr noundef) unnamed_addr #5

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: write)
declare void @llvm.assume(i1 noundef) #6

; core::panicking::panic_in_cleanup
; Function Attrs: cold minsize noinline noreturn nounwind optsize uwtable
declare void @_RNvNtCsjIpoRzUjyHQ_4core9panicking16panic_in_cleanup() unnamed_addr #7

; std::panicking::catch_unwind::cleanup
; Function Attrs: cold minsize optsize uwtable
declare { ptr, ptr } @_RNvNvNtCs1SSuMAdGM58_3std9panicking12catch_unwind7cleanup(ptr noundef) unnamed_addr #8

; core::panicking::panic_cannot_unwind
; Function Attrs: cold minsize noinline noreturn nounwind optsize uwtable
declare void @_RNvNtCsjIpoRzUjyHQ_4core9panicking19panic_cannot_unwind() unnamed_addr #7

; std::panicking::set_hook
; Function Attrs: uwtable
declare void @_RNvNtCs1SSuMAdGM58_3std9panicking8set_hook(ptr noundef nonnull, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(48)) unnamed_addr #0

; std::io::stdio::_print
; Function Attrs: uwtable
declare void @_RNvNtNtCs1SSuMAdGM58_3std2io5stdio6__print(ptr noundef nonnull, ptr noundef nonnull) unnamed_addr #0

; core::panicking::assert_failed::<u8, u8>
; Function Attrs: cold minsize noinline noreturn optsize uwtable
declare void @_RINvNtCsjIpoRzUjyHQ_4core9panicking13assert_failedhhECs1SSuMAdGM58_3std(i8 noundef range(i8 0, 3), ptr noalias nofree noundef readonly captures(address, read_provenance) dereferenceable(1), ptr noalias nofree noundef readonly captures(address, read_provenance) dereferenceable(1), ptr noundef, ptr, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24)) unnamed_addr #9

; core::panicking::panic_fmt
; Function Attrs: cold noinline noreturn uwtable
declare void @_RNvNtCsjIpoRzUjyHQ_4core9panicking9panic_fmt(ptr noundef nonnull, ptr noundef nonnull, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24)) unnamed_addr #10

; __rustc::__rust_dealloc
; Function Attrs: nounwind allockind("free") uwtable
declare void @_RNvCsdtSMxSA38aw_7___rustc14___rust_dealloc(ptr allocptr noundef nonnull captures(address), i64 noundef, i64 noundef range(i64 1, -9223372036854775807)) unnamed_addr #11

define noundef i32 @main(i32 %0, ptr %1) unnamed_addr #12 !guid !33 {
top:
  %_7.i = alloca [8 x i8], align 8
  %2 = sext i32 %0 to i64
  call void @llvm.lifetime.start.p0(ptr nonnull %_7.i)
  store ptr @_RNvCsdT136XbhqV_6inline4main, ptr %_7.i, align 8
; call std::rt::lang_start_internal
  %_0.i = call noundef i64 @_RNvNtCs1SSuMAdGM58_3std2rt19lang_start_internal(ptr noundef nonnull %_7.i, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(48) @vtable.0, i64 noundef %2, ptr noundef %1, i8 noundef 0)
  call void @llvm.lifetime.end.p0(ptr nonnull %_7.i)
  %3 = trunc i64 %_0.i to i32
  ret i32 %3
}

attributes #0 = { uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #1 = { noinline uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #2 = { inlinehint uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #3 = { inlinehint mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #4 = { mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { nounwind uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #6 = { mustprogress nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: write) }
attributes #7 = { cold minsize noinline noreturn nounwind optsize uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #8 = { cold minsize optsize uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #9 = { cold minsize noinline noreturn optsize uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #10 = { cold noinline noreturn uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #11 = { nounwind allockind("free") uwtable "alloc-family"="__rust_alloc" "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #12 = { "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #13 = { nounwind }
attributes #14 = { noinline }
attributes #15 = { cold noreturn nounwind }
attributes #16 = { noreturn }
attributes #17 = { noinline noreturn }

!llvm.module.flags = !{!9, !10, !11, !12}
!llvm.ident = !{!13}

!0 = !{i64 6196142460575908940}
!1 = !{i64 -8701154560090103003}
!2 = !{i64 1897939990155485659}
!3 = !{i64 -5596976623501523573}
!4 = !{i64 -5020314055150098766}
!5 = !{i64 -2549367410985306993}
!6 = !{i64 -8640368351438629818}
!7 = !{i64 -1097685740632018531}
!8 = !{i64 5888091376758735650}
!9 = !{i32 8, !"PIC Level", i32 2}
!10 = !{i32 7, !"PIE Level", i32 2}
!11 = !{i32 7, !"uwtable", i32 2}
!12 = !{i32 7, !"frame-pointer", i32 1}
!13 = !{!"rustc version 1.99.0 (b940084d7 2026-09-28)"}
!14 = !{i64 -1137523807514948001}
!15 = !{i64 4919174864718266953}
!16 = distinct !{null}
!17 = !{i64 16275984730411721}
!18 = !{i64 -1751057908153127017}
!19 = !{}
!20 = !{i64 -451110163226107756}
!21 = !{i64 5451314842247561764}
!22 = !{!23}
!23 = distinct !{!23, !24, !"_RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startuE0CsdT136XbhqV_6inline: %_1"}
!24 = distinct !{!24, !"_RNCINvNtCs1SSuMAdGM58_3std2rt10lang_startuE0CsdT136XbhqV_6inline"}
!25 = !{i64 -5607625123046151422}
!26 = !{i64 -315290698475095539}
!27 = !{i64 0, i64 -9223372036854775808}
!28 = !{i64 1, i64 536870913}
!29 = distinct !{!29, !30}
!30 = !{!"llvm.loop.peeled.count", i32 1}
!31 = !{i64 6652646680625618698}
!32 = !{!"branch_weights", !"expected", i32 1, i32 2000}
!33 = !{i64 -2624081020897602054}
