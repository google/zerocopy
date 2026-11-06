; Probe E: mustprogress / willreturn vs. Rust-style infinite loops in ADCE and LoopDeletion
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Variant E1: Rust default (NO `mustprogress`, NO `willreturn`)
; A side-effect-free loop that may diverge (`loop {}` if `%c == false`) MUST be preserved!
define i32 @rust_may_diverge_loop(i1 %c) {
entry:
  br label %loop

loop:
  br i1 %c, label %exit, label %loop

exit:
  ret i32 7
}

; Variant E2: C++-style `mustprogress` attribute on the function
; LoopDeletion deletes the side-effect-free potentially-infinite loop!
define i32 @cpp_mustprogress_loop(i1 %c) mustprogress {
entry:
  br label %loop

loop:
  br i1 %c, label %exit, label %loop

exit:
  ret i32 7
}

; Variant E3: `willreturn` attribute on a function with an unconditional infinite loop
define void @unconditional_infinite_loop_willreturn() mustprogress willreturn {
entry:
  br label %loop

loop:
  br label %loop
}
