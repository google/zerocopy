; ModuleID = 'c_uninit.c'
source_filename = "c_uninit.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@switch.table.bf_switch_then_set = private unnamed_addr constant [3 x i32] [i32 10, i32 18, i32 66], align 4

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local noundef range(i32 0, 2) i32 @bf_read_back(i32 noundef %0) local_unnamed_addr #0 {
  %2 = and i32 %0, 1
  ret i32 %2
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local noundef range(i32 0, 2) i32 @bf_return_whole(i32 noundef %0) local_unnamed_addr #0 {
  %2 = and i32 %0, 1
  ret i32 %2
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local range(i32 0, 256) i32 @bf_loop_then_set(i32 noundef %0, i32 noundef %1) local_unnamed_addr #0 {
  %3 = icmp sgt i32 %1, 0
  %4 = shl nuw i32 %1, 1
  %5 = add i32 %4, 254
  %6 = and i32 %5, 254
  %7 = select i1 %3, i32 %6, i32 0
  %8 = and i32 %0, 1
  %9 = or disjoint i32 %7, %8
  ret i32 %9
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local range(i32 0, 68) i32 @bf_switch_then_set(i32 noundef %0, i32 noundef %1) local_unnamed_addr #0 {
  %3 = add i32 %1, -1
  %4 = icmp ult i32 %3, 3
  br i1 %4, label %5, label %9

5:                                                ; preds = %2
  %6 = zext nneg i32 %3 to i64
  %7 = getelementptr inbounds nuw i32, ptr @switch.table.bf_switch_then_set, i64 %6
  %8 = load i32, ptr %7, align 4
  br label %9

9:                                                ; preds = %5, %2
  %10 = phi i32 [ 0, %2 ], [ %8, %5 ]
  %11 = and i32 %0, 1
  %12 = or disjoint i32 %10, %11
  ret i32 %12
}

; Function Attrs: nounwind uwtable
define dso_local range(i32 0, 256) i32 @bf_loop_ext(i32 noundef %0) local_unnamed_addr #1 {
  %2 = tail call i32 @cond() #3
  %3 = icmp eq i32 %2, 0
  br i1 %3, label %10, label %4

4:                                                ; preds = %1, %4
  %5 = tail call signext i8 @next() #3
  %6 = tail call i32 @cond() #3
  %7 = icmp eq i32 %6, 0
  br i1 %7, label %8, label %4, !llvm.loop !9

8:                                                ; preds = %4
  %9 = shl i8 %5, 1
  br label %10

10:                                               ; preds = %8, %1
  %11 = phi i8 [ 0, %1 ], [ %9, %8 ]
  %12 = trunc i32 %0 to i8
  %13 = and i8 %12, 1
  %14 = or disjoint i8 %11, %13
  %15 = zext i8 %14 to i32
  ret i32 %15
}

declare i32 @cond() local_unnamed_addr #2

declare signext i8 @next() local_unnamed_addr #2

; Function Attrs: nounwind uwtable
define dso_local i16 @plain_loop(i8 noundef signext %0) local_unnamed_addr #1 {
  %2 = tail call i32 @cond() #3
  %3 = icmp eq i32 %2, 0
  br i1 %3, label %11, label %4

4:                                                ; preds = %1, %4
  %5 = tail call signext i8 @next() #3
  %6 = tail call i32 @cond() #3
  %7 = icmp eq i32 %6, 0
  br i1 %7, label %8, label %4, !llvm.loop !12

8:                                                ; preds = %4
  %9 = zext i8 %5 to i16
  %10 = shl nuw i16 %9, 8
  br label %11

11:                                               ; preds = %8, %1
  %12 = phi i16 [ 0, %1 ], [ %10, %8 ]
  %13 = zext i8 %0 to i16
  %14 = or disjoint i16 %12, %13
  ret i16 %14
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local range(i32 0, 256) i32 @pun(i8 noundef signext %0) local_unnamed_addr #0 {
  %2 = zext i8 %0 to i32
  ret i32 %2
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local range(i64 0, 256) i64 @partial_coerced(i8 noundef signext %0) local_unnamed_addr #0 {
  %2 = zext i8 %0 to i64
  ret i64 %2
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local range(i64 0, 4294967296) i64 @arr_part(i32 noundef %0) local_unnamed_addr #0 {
  %2 = zext i32 %0 to i64
  ret i64 %2
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local range(i64 0, -4294967295) i64 @fi(i32 noundef %0) local_unnamed_addr #0 {
  %2 = zext i32 %0 to i64
  %3 = shl nuw i64 %2, 32
  ret i64 %3
}

; Function Attrs: nounwind uwtable
define dso_local i32 @two_copies(i8 noundef signext %0, i8 noundef signext %1) local_unnamed_addr #1 {
  %3 = tail call i32 @cond() #3
  %4 = icmp eq i32 %3, 0
  br i1 %4, label %11, label %5

5:                                                ; preds = %2, %5
  %6 = tail call signext i8 @next() #3
  %7 = tail call i32 @cond() #3
  %8 = icmp eq i32 %7, 0
  br i1 %8, label %9, label %5, !llvm.loop !13

9:                                                ; preds = %5
  %10 = zext i8 %6 to i32
  br label %11

11:                                               ; preds = %9, %2
  %12 = phi i32 [ 0, %2 ], [ %10, %9 ]
  %13 = shl nuw i32 %12, 24
  %14 = zext i8 %1 to i32
  %15 = shl nuw nsw i32 %14, 16
  %16 = or disjoint i32 %13, %15
  %17 = shl nuw nsw i32 %12, 8
  %18 = or disjoint i32 %16, %17
  %19 = zext i8 %0 to i32
  %20 = or disjoint i32 %18, %19
  ret i32 %20
}

; Function Attrs: nounwind uwtable
define dso_local range(i64 137438953472, 201863463168) i64 @two_masks(i32 noundef %0) local_unnamed_addr #1 {
  %2 = tail call i32 @cond() #3
  %3 = icmp eq i32 %2, 0
  br i1 %3, label %11, label %4

4:                                                ; preds = %1, %4
  %5 = tail call signext i8 @next() #3
  %6 = tail call i32 @cond() #3
  %7 = icmp eq i32 %6, 0
  br i1 %7, label %8, label %4, !llvm.loop !14

8:                                                ; preds = %4
  %9 = shl i8 %5, 1
  %10 = and i8 %9, 14
  br label %11

11:                                               ; preds = %8, %1
  %12 = phi i8 [ undef, %1 ], [ %10, %8 ]
  %13 = trunc i32 %0 to i8
  %14 = and i8 %13, 1
  %15 = and i8 %12, -2
  %16 = or disjoint i8 %15, %14
  %17 = and i8 %12, 15
  %18 = or disjoint i8 %17, 32
  %19 = zext nneg i8 %18 to i64
  %20 = shl nuw nsw i64 %19, 32
  %21 = zext i8 %16 to i64
  %22 = or disjoint i64 %20, %21
  ret i64 %22
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local { i64, i64 } @partial_pair(i64 noundef %0) local_unnamed_addr #0 {
  %2 = insertvalue { i64, i64 } poison, i64 %0, 0
  %3 = insertvalue { i64, i64 } %2, i64 undef, 1
  ret { i64, i64 } %3
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local { double, double } @dd(double noundef %0) local_unnamed_addr #0 {
  %2 = insertvalue { double, double } poison, double %0, 0
  %3 = insertvalue { double, double } %2, double undef, 1
  ret { double, double } %3
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local { i64, i32 } @li(i32 noundef %0) local_unnamed_addr #0 {
  %2 = insertvalue { i64, i32 } { i64 undef, i32 poison }, i32 %0, 1
  ret { i64, i32 } %2
}

; Function Attrs: nounwind uwtable
define dso_local { i64, i64 } @pair_loop(i64 noundef %0) local_unnamed_addr #1 {
  %2 = tail call i32 @cond() #3
  %3 = icmp eq i32 %2, 0
  br i1 %3, label %10, label %4

4:                                                ; preds = %1, %4
  %5 = tail call signext i8 @next() #3
  %6 = tail call i32 @cond() #3
  %7 = icmp eq i32 %6, 0
  br i1 %7, label %8, label %4, !llvm.loop !15

8:                                                ; preds = %4
  %9 = sext i8 %5 to i64
  br label %10

10:                                               ; preds = %8, %1
  %11 = phi i64 [ %9, %8 ], [ undef, %1 ]
  %12 = insertvalue { i64, i64 } poison, i64 %0, 0
  %13 = insertvalue { i64, i64 } %12, i64 %11, 1
  ret { i64, i64 } %13
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}
!llvm.errno.tbaa = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{!"clang version 22.1.4 (https://github.com/llvm/llvm-project 35990504507d79e0b9deb809c8ee5e1b34ceef20)"}
!5 = !{!6, !6, i64 0}
!6 = !{!"int", !7, i64 0}
!7 = !{!"omnipotent char", !8, i64 0}
!8 = !{!"Simple C/C++ TBAA"}
!9 = distinct !{!9, !10, !11}
!10 = !{!"llvm.loop.mustprogress"}
!11 = !{!"llvm.loop.unroll.disable"}
!12 = distinct !{!12, !10, !11}
!13 = distinct !{!13, !10, !11}
!14 = distinct !{!14, !10, !11}
!15 = distinct !{!15, !10, !11}
