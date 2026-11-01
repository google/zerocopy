; ModuleID = '.
source_filename = "."
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @rust_may_diverge_loop(i1 %c) {
entry:
  br label %loop

loop:                                             ; preds = %loop, %entry
  br i1 %c, label %exit, label %loop

exit:                                             ; preds = %loop
  ret i32 7
}

; Function Attrs: mustprogress
define i32 @cpp_mustprogress_loop(i1 %c) #0 {
entry:
  ret i32 7
}

; Function Attrs: mustprogress willreturn
define void @unconditional_infinite_loop_willreturn() #1 {
entry:
  unreachable
}

attributes #0 = { mustprogress }
attributes #1 = { mustprogress willreturn }
