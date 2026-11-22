target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define { i64, i1 } @mlir_trunc_ret_i1(i64 %a, i64 %flags) {
  %v = add i64 %a, 10
  %bit = trunc i64 %flags to i1
  %r0 = insertvalue { i64, i1 } poison, i64 %v, 0
  %r1 = insertvalue { i64, i1 } %r0, i1 %bit, 1
  ret { i64, i1 } %r1
}

define { i64, i8 } @mlir_ext_ret_i8(i64 %a, i64 %flags) {
  %v = add i64 %a, 10
  %bit = trunc i64 %flags to i1
  %ext = zext i1 %bit to i8
  %r0 = insertvalue { i64, i8 } poison, i64 %v, 0
  %r1 = insertvalue { i64, i8 } %r0, i8 %ext, 1
  ret { i64, i8 } %r1
}
