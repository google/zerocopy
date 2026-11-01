; Probe B: SROA & MemCpyOpt on structs with uninitialized padding (Rust PassMode::Cast pattern)
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%PaddedStruct = type { i8, [3 x i8], i32 }

; Variant B1: Rust `PassMode::Cast` ABI pattern (`rustc_codegen_ssa::mir::block::load_cast`).
; A `{ u8, u32 }` struct with 3 bytes of padding is stored field-by-field into an alloca,
; then loaded as a single `i64` for register return.
define i64 @rust_pass_mode_cast_sroa(i8 %a, i32 %b) {
entry:
  %slot = alloca %PaddedStruct, align 8
  store i8 %a, ptr %slot, align 8
  %f1 = getelementptr inbounds i8, ptr %slot, i64 4
  store i32 %b, ptr %f1, align 4
  %wide = load i64, ptr %slot, align 8
  ret i64 %wide
}

; Variant B2: Extracting a field from a widened i64 load across uninitialized padding
define i32 @extract_field_from_wide_load(i8 %a, i32 %b) {
entry:
  %slot = alloca %PaddedStruct, align 8
  store i8 %a, ptr %slot, align 8
  %f1 = getelementptr inbounds i8, ptr %slot, i64 4
  store i32 %b, ptr %f1, align 4
  %wide = load i64, ptr %slot, align 8
  %shifted = lshr i64 %wide, 32
  %extracted = trunc i64 %shifted to i32
  ret i32 %extracted
}

; Variant B3: MemCpy across padded struct followed by field read
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg)

define i32 @memcpy_padded_struct(i8 %a, i32 %b) {
entry:
  %src = alloca %PaddedStruct, align 8
  %dst = alloca %PaddedStruct, align 8
  store i8 %a, ptr %src, align 8
  %src_f1 = getelementptr inbounds i8, ptr %src, i64 4
  store i32 %b, ptr %src_f1, align 4
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %dst, ptr align 8 %src, i64 8, i1 false)
  %dst_f1 = getelementptr inbounds i8, ptr %dst, i64 4
  %res = load i32, ptr %dst_f1, align 4
  ret i32 %res
}
