; ModuleID = 'fixture.352611ba05082b26-cgu.0'
source_filename = "fixture.352611ba05082b26-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define noundef range(i64 0, 2001) i64 @add_bounded(i64 noundef %x, i64 noundef %y) unnamed_addr #0 !guid !4 {
start:
  %_3 = icmp ult i64 %x, 1001
  %_4 = icmp ult i64 %y, 1001
  %or.cond = and i1 %_3, %_4
  %0 = add nuw nsw i64 %y, %x
  %_0.sroa.0.0 = select i1 %or.cond, i64 %0, i64 0
  ret i64 %_0.sroa.0.0
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define noundef i64 @alloc_passthrough(i64 noundef returned %x) unnamed_addr #0 !guid !5 {
start:
  ret i64 %x
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"}
!4 = !{i64 6419884775981512784}
!5 = !{i64 8732288253445790394}
