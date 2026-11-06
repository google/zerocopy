; ModuleID = '.
source_filename = "."
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare void @side_effect_a()

declare void @side_effect_b()

declare i1 @step_guard(i32)

define void @unswitch_unconditional_no_freeze(i32 %n, i1 %cond) {
entry:
  %cmp0 = icmp sgt i32 %n, 0
  br i1 %cmp0, label %loop.header.preheader, label %exit

loop.header.preheader:                            ; preds = %entry
  br i1 %cond, label %loop.header.preheader.split.us, label %loop.header.preheader.split

loop.header.preheader.split.us:                   ; preds = %loop.header.preheader
  br label %loop.header.us

loop.header.us:                                   ; preds = %loop.latch.us, %loop.header.preheader.split.us
  %iv.us = phi i32 [ %iv.next.us, %loop.latch.us ], [ 0, %loop.header.preheader.split.us ]
  br label %then.us

then.us:                                          ; preds = %loop.header.us
  call void @side_effect_a()
  br label %loop.latch.us

loop.latch.us:                                    ; preds = %then.us
  %iv.next.us = add nuw nsw i32 %iv.us, 1
  %exitcond.us = icmp eq i32 %iv.next.us, %n
  br i1 %exitcond.us, label %exit.loopexit.split.us, label %loop.header.us

exit.loopexit.split.us:                           ; preds = %loop.latch.us
  br label %exit.loopexit

loop.header.preheader.split:                      ; preds = %loop.header.preheader
  br label %loop.header

loop.header:                                      ; preds = %loop.header.preheader.split, %loop.latch
  %iv = phi i32 [ %iv.next, %loop.latch ], [ 0, %loop.header.preheader.split ]
  br label %else

else:                                             ; preds = %loop.header
  call void @side_effect_b()
  br label %loop.latch

loop.latch:                                       ; preds = %else
  %iv.next = add nuw nsw i32 %iv, 1
  %exitcond = icmp eq i32 %iv.next, %n
  br i1 %exitcond, label %exit.loopexit.split, label %loop.header

exit.loopexit.split:                              ; preds = %loop.latch
  br label %exit.loopexit

exit.loopexit:                                    ; preds = %exit.loopexit.split.us, %exit.loopexit.split
  br label %exit

exit:                                             ; preds = %exit.loopexit, %entry
  ret void
}

define void @unswitch_guarded_inserts_freeze(i32 %n, i1 %cond) {
entry:
  %cmp0 = icmp sgt i32 %n, 0
  br i1 %cmp0, label %loop.header.preheader, label %exit

loop.header.preheader:                            ; preds = %entry
  %cond.fr = freeze i1 %cond
  br i1 %cond.fr, label %loop.header.preheader.split.us, label %loop.header.preheader.split

loop.header.preheader.split.us:                   ; preds = %loop.header.preheader
  br label %loop.header.us

loop.header.us:                                   ; preds = %loop.latch.us, %loop.header.preheader.split.us
  %iv.us = phi i32 [ %iv.next.us, %loop.latch.us ], [ 0, %loop.header.preheader.split.us ]
  %g.us = call i1 @step_guard(i32 %iv.us)
  br i1 %g.us, label %guarded.us, label %loop.latch.us

guarded.us:                                       ; preds = %loop.header.us
  br label %then.us

then.us:                                          ; preds = %guarded.us
  call void @side_effect_a()
  br label %loop.latch.us

loop.latch.us:                                    ; preds = %then.us, %loop.header.us
  %iv.next.us = add nuw nsw i32 %iv.us, 1
  %exitcond.us = icmp eq i32 %iv.next.us, %n
  br i1 %exitcond.us, label %exit.loopexit.split.us, label %loop.header.us

exit.loopexit.split.us:                           ; preds = %loop.latch.us
  br label %exit.loopexit

loop.header.preheader.split:                      ; preds = %loop.header.preheader
  br label %loop.header

loop.header:                                      ; preds = %loop.header.preheader.split, %loop.latch
  %iv = phi i32 [ %iv.next, %loop.latch ], [ 0, %loop.header.preheader.split ]
  %g = call i1 @step_guard(i32 %iv)
  br i1 %g, label %guarded, label %loop.latch

guarded:                                          ; preds = %loop.header
  br label %else

else:                                             ; preds = %guarded
  call void @side_effect_b()
  br label %loop.latch

loop.latch:                                       ; preds = %else, %loop.header
  %iv.next = add nuw nsw i32 %iv, 1
  %exitcond = icmp eq i32 %iv.next, %n
  br i1 %exitcond, label %exit.loopexit.split, label %loop.header

exit.loopexit.split:                              ; preds = %loop.latch
  br label %exit.loopexit

exit.loopexit:                                    ; preds = %exit.loopexit.split.us, %exit.loopexit.split
  br label %exit

exit:                                             ; preds = %exit.loopexit, %entry
  ret void
}
