; ModuleID = 'erased_ub.d533b3e062397667-cgu.0'
source_filename = "erased_ub.d533b3e062397667-cgu.0"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "arm64-apple-macosx11.0.0"

@alloc_75fb06c2453febd814e73f5f2e72ae38 = private unnamed_addr constant [199 x i8] c"unsafe precondition(s) violated: hint::unreachable_unchecked must never be reached\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1, !guid !0
@alloc_2ae9090710e2aad7fd5b25ca26e66089 = private unnamed_addr constant [13 x i8] c"erased_ub.rs\00", align 1, !guid !1
@alloc_803660bb05b5efd0f0b4896d6709e15b = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_2ae9090710e2aad7fd5b25ca26e66089, [16 x i8] c"\0C\00\00\00\00\00\00\00\07\00\00\00\12\00\00\00" }>, align 8, !guid !2

; core::hint::unreachable_unchecked
; Function Attrs: inlinehint noreturn uwtable
define internal void @_RNvNtCsjIpoRzUjyHQ_4core4hint21unreachable_uncheckedCsiiRSCCMWLIh_9erased_ub(ptr align 8 %0) unnamed_addr #0 !guid !7 {
start:
; call core::hint::unreachable_unchecked::precondition_check
  call void @_RNvNvNtCsjIpoRzUjyHQ_4core4hint21unreachable_unchecked18precondition_checkCsiiRSCCMWLIh_9erased_ub(ptr align 8 %0) #5
  unreachable
}

; core::hint::unreachable_unchecked::precondition_check
; Function Attrs: inlinehint nounwind uwtable
define internal void @_RNvNvNtCsjIpoRzUjyHQ_4core4hint21unreachable_unchecked18precondition_checkCsiiRSCCMWLIh_9erased_ub(ptr align 8 %0) unnamed_addr #1 !guid !8 {
start:
; call core::panicking::panic_nounwind_fmt
  call void @_RNvNtCsjIpoRzUjyHQ_4core9panicking18panic_nounwind_fmt(ptr @alloc_75fb06c2453febd814e73f5f2e72ae38, ptr inttoptr (i64 399 to ptr), i1 zeroext false, ptr align 8 %0) #6
  unreachable
}

; Function Attrs: nounwind uwtable
define zeroext i8 @always_seven(i8 zeroext %_input) unnamed_addr #2 !guid !9 {
start:
  ret i8 7
}

; Function Attrs: nounwind uwtable
define zeroext i8 @broken_safe_api(i8 zeroext %input) unnamed_addr #2 personality ptr @rust_eh_personality !guid !10 {
start:
  %_2 = icmp eq i8 %input, 0
  br i1 %_2, label %bb1, label %bb2

bb2:                                              ; preds = %start
  ret i8 7

bb1:                                              ; preds = %start
; invoke core::hint::unreachable_unchecked
  invoke void @_RNvNtCsjIpoRzUjyHQ_4core4hint21unreachable_uncheckedCsiiRSCCMWLIh_9erased_ub(ptr align 8 @alloc_803660bb05b5efd0f0b4896d6709e15b) #7
          to label %unreachable unwind label %terminate

terminate:                                        ; preds = %bb1
  %0 = landingpad { ptr, i32 }
          filter [0 x ptr] zeroinitializer
; call core::panicking::panic_cannot_unwind
  call void @_RNvNtCsjIpoRzUjyHQ_4core9panicking19panic_cannot_unwind() #8
  unreachable

unreachable:                                      ; preds = %bb1
  unreachable
}

; core::panicking::panic_nounwind_fmt
; Function Attrs: cold noinline noreturn nounwind uwtable
declare void @_RNvNtCsjIpoRzUjyHQ_4core9panicking18panic_nounwind_fmt(ptr, ptr, i1 zeroext, ptr align 8) unnamed_addr #3

; Function Attrs: nounwind uwtable
declare i32 @rust_eh_personality(i32, i32, i64, ptr, ptr) unnamed_addr #2

; core::panicking::panic_cannot_unwind
; Function Attrs: cold minsize noinline noreturn nounwind optsize uwtable
declare void @_RNvNtCsjIpoRzUjyHQ_4core9panicking19panic_cannot_unwind() unnamed_addr #4

attributes #0 = { inlinehint noreturn uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #1 = { inlinehint nounwind uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #2 = { nounwind uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #3 = { cold noinline noreturn nounwind uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #4 = { cold minsize noinline noreturn nounwind optsize uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #5 = { inlinehint nounwind }
attributes #6 = { noinline noreturn nounwind }
attributes #7 = { noreturn }
attributes #8 = { cold noreturn nounwind }

!llvm.module.flags = !{!3, !4, !5}
!llvm.ident = !{!6}

!0 = !{i64 3169784256839974184}
!1 = !{i64 1728183965043641729}
!2 = !{i64 3601292760157944154}
!3 = !{i32 8, !"PIC Level", i32 2}
!4 = !{i32 7, !"uwtable", i32 2}
!5 = !{i32 7, !"frame-pointer", i32 1}
!6 = !{!"rustc version 1.99.0 (b940084d7 2026-09-28)"}
!7 = !{i64 -1270291667148158981}
!8 = !{i64 -983807437931380615}
!9 = !{i64 -1242483637123021054}
!10 = !{i64 -6732109238648086000}
