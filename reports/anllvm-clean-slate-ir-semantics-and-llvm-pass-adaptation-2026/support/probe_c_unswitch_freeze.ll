; Probe C: SimpleLoopUnswitchPass inserting `freeze` when hoisting a potentially-poison condition
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare void @side_effect_a()
declare void @side_effect_b()
declare i1 @step_guard(i32)

; Variant C1: Condition `%cond` is unconditionally branched on in `loop.header`,
; so `mustExecuteUBIfPoisonOnPathTo` proves no `freeze` is needed.
define void @unswitch_unconditional_no_freeze(i32 %n, i1 %cond) {
entry:
  %cmp0 = icmp sgt i32 %n, 0
  br i1 %cmp0, label %loop.header, label %exit

loop.header:
  %iv = phi i32 [ 0, %entry ], [ %iv.next, %loop.latch ]
  br i1 %cond, label %then, label %else

then:
  call void @side_effect_a()
  br label %loop.latch

else:
  call void @side_effect_b()
  br label %loop.latch

loop.latch:
  %iv.next = add nuw nsw i32 %iv, 1
  %exitcond = icmp eq i32 %iv.next, %n
  br i1 %exitcond, label %exit, label %loop.header

exit:
  ret void
}

; Variant C2: Condition `%cond` is guarded by `@step_guard(%iv)` inside the loop,
; so `%cond` might never be branched on in the original program. Hoisting `br i1 %cond`
; to the preheader requires `SimpleLoopUnswitchPass` to insert `%cond.fr = freeze i1 %cond`!
define void @unswitch_guarded_inserts_freeze(i32 %n, i1 %cond) {
entry:
  %cmp0 = icmp sgt i32 %n, 0
  br i1 %cmp0, label %loop.header, label %exit

loop.header:
  %iv = phi i32 [ 0, %entry ], [ %iv.next, %loop.latch ]
  %g = call i1 @step_guard(i32 %iv)
  br i1 %g, label %guarded, label %loop.latch

guarded:
  br i1 %cond, label %then, label %else

then:
  call void @side_effect_a()
  br label %loop.latch

else:
  call void @side_effect_b()
  br label %loop.latch

loop.latch:
  %iv.next = add nuw nsw i32 %iv, 1
  %exitcond = icmp eq i32 %iv.next, %n
  br i1 %exitcond, label %exit, label %loop.header

exit:
  ret void
}
