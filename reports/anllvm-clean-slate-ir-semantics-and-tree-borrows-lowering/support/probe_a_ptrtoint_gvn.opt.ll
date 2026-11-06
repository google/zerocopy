; ModuleID = '.
source_filename = "."
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @ptr_eq_gvn_miscompile(ptr noalias %p, ptr noalias %q) {
entry:
  store i32 0, ptr %q, align 4
  %p_end = getelementptr inbounds nuw i8, ptr %p, i64 8
  %cmp = icmp eq ptr %p_end, %q
  br i1 %cmp, label %if.true, label %if.false

if.true:                                          ; preds = %entry
  store i32 42, ptr %q, align 4
  ret i32 42

if.false:                                         ; preds = %entry
  ret i32 -1
}

define i32 @ptrtoint_inttoptr_gvn_instcombine(ptr noalias %p, ptr noalias %q) {
entry:
  store i32 0, ptr %q, align 4
  %p_end = getelementptr inbounds nuw i8, ptr %p, i64 8
  %cmp = icmp eq ptr %p_end, %q
  br i1 %cmp, label %if.true, label %if.false

if.true:                                          ; preds = %entry
  store i32 42, ptr %p_end, align 4
  ret i32 0

if.false:                                         ; preds = %entry
  ret i32 -1
}
