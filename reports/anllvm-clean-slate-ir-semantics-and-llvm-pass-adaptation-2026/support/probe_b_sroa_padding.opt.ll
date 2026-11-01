; ModuleID = '.
source_filename = "."
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i64 @rust_pass_mode_cast_sroa(i8 %a, i32 %b) {
entry:
  %slot.sroa.21.0.insert.ext = zext i32 %b to i64
  %slot.sroa.21.0.insert.shift = shl nuw i64 %slot.sroa.21.0.insert.ext, 32
  %slot.sroa.0.0.insert.ext = zext i8 %a to i64
  %slot.sroa.0.0.insert.insert = or disjoint i64 %slot.sroa.21.0.insert.shift, %slot.sroa.0.0.insert.ext
  ret i64 %slot.sroa.0.0.insert.insert
}

define i32 @extract_field_from_wide_load(i8 %a, i32 %b) {
entry:
  ret i32 %b
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #0

define i32 @memcpy_padded_struct(i8 %a, i32 %b) {
entry:
  ret i32 %b
}

attributes #0 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
