; ModuleID = 'abi_subjects.e2113a355ceea76a-cgu.0'
source_filename = "abi_subjects.e2113a355ceea76a-cgu.0"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc"

@abi_rust_big = unnamed_addr alias void (ptr, ptr), ptr @abi_c_big
@abi_system_big = unnamed_addr alias void (ptr, ptr), ptr @abi_c_big
@abi_system_narrow = unnamed_addr alias i64 (i8, i16, i1), ptr @abi_c_narrow
@abi_system_pair = unnamed_addr alias void (ptr, ptr), ptr @abi_c_pair

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: readwrite) uwtable
define void @abi_c_big(ptr dead_on_unwind noalias noundef writable writeonly sret([24 x i8]) align 8 captures(none) dereferenceable(24) initializes((0, 24)) %_0, ptr dead_on_return noalias noundef readonly align 8 captures(none) dereferenceable(24) %x) unnamed_addr #0 {
start:
  tail call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(24) %_0, ptr noundef nonnull align 8 dereferenceable(24) %x, i64 24, i1 false)
  ret void
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable
define noundef double @abi_c_fp(float noundef %x, double noundef %y) unnamed_addr #1 {
start:
  %_3 = fpext float %x to double
  %_0 = fadd double %y, %_3
  ret double %_0
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: readwrite) uwtable
define void @abi_c_hfa(ptr dead_on_unwind noalias noundef writable writeonly sret([16 x i8]) align 4 captures(none) dereferenceable(16) initializes((0, 16)) %_0, ptr dead_on_return noalias noundef readonly align 4 captures(none) dereferenceable(16) %x) unnamed_addr #0 {
start:
  tail call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 4 dereferenceable(16) %_0, ptr noundef nonnull align 4 dereferenceable(16) %x, i64 16, i1 false)
  ret void
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable
define noundef i64 @abi_c_narrow(i8 noundef zeroext %x, i16 noundef signext %y, i1 noundef zeroext %flag) unnamed_addr #1 {
start:
  %_5 = zext i8 %x to i64
  %_7 = sext i16 %y to i64
  %_4 = xor i64 %_7, %_5
  %_8 = zext i1 %flag to i64
  %_0 = xor i64 %_4, %_8
  ret i64 %_0
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: readwrite) uwtable
define void @abi_c_pair(ptr dead_on_unwind noalias noundef writable writeonly sret([16 x i8]) align 8 captures(none) dereferenceable(16) initializes((0, 12)) %_0, ptr dead_on_return noalias noundef readonly align 8 captures(none) dereferenceable(16) %x) unnamed_addr #0 {
start:
  %0 = load i64, ptr %x, align 8, !noundef !2
  %1 = getelementptr inbounds nuw i8, ptr %x, i64 8
  %2 = load i32, ptr %1, align 8, !noundef !2
  store i64 %0, ptr %_0, align 8
  %3 = getelementptr inbounds nuw i8, ptr %_0, i64 8
  store i32 %2, ptr %3, align 8
  ret void
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable
define noundef ptr @abi_c_raw(ptr noundef readnone returned captures(ret: address, provenance) %x) unnamed_addr #1 {
start:
  ret ptr %x
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable
define noundef nonnull ptr @abi_interior(ptr noundef nonnull readnone returned align 8 captures(ret: address, provenance) %x) unnamed_addr #1 {
start:
  ret ptr %x
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable
define noundef i64 @abi_rust_narrow(i8 noundef %x, i16 noundef %y, i1 noundef zeroext %flag) unnamed_addr #1 {
start:
  %_5 = zext i8 %x to i64
  %_7 = sext i16 %y to i64
  %_4 = xor i64 %_7, %_5
  %_8 = zext i1 %flag to i64
  %_0 = xor i64 %_4, %_8
  ret i64 %_0
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable
define { i64, i32 } @abi_rust_tuple(i64 noundef %x.0, i32 noundef %x.1) unnamed_addr #1 {
start:
  %0 = insertvalue { i64, i32 } poison, i64 %x.0, 0
  %1 = insertvalue { i64, i32 } %0, i32 %x.1, 1
  ret { i64, i32 } %1
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: read) uwtable
define noundef i64 @abi_shared(ptr noalias noundef readonly align 8 captures(none) dereferenceable(8) %x) unnamed_addr #2 {
start:
  %_0 = load i64, ptr %x, align 8, !noundef !2
  ret i64 %_0
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable
define noundef range(i64 0, -9223372036854775808) i64 @abi_slice(ptr noalias noundef nonnull readonly captures(none) %x.0, i64 noundef returned range(i64 0, -9223372036854775808) %x.1) unnamed_addr #1 {
start:
  ret i64 %x.1
}

; Function Attrs: noinline nounwind uwtable
define noundef i64 @abi_stack_driver(i64 noundef %a, i64 noundef %b, i64 noundef %c, i64 noundef %d, i64 noundef %e, i64 noundef %f, i64 noundef %g, i64 noundef %h, i64 noundef %i, i64 noundef %j, i64 noundef %k, i64 noundef %l) unnamed_addr #3 {
start:
  %_13 = tail call noundef i64 @abi_opaque_twelve(i64 noundef %a, i64 noundef %b, i64 noundef %c, i64 noundef %d, i64 noundef %e, i64 noundef %f, i64 noundef %g, i64 noundef %h, i64 noundef %i, i64 noundef %j, i64 noundef %k, i64 noundef %l) #6
  %_0 = add i64 %_13, 1
  ret i64 %_0
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: read) uwtable
define noundef i64 @abi_track(i64 noundef %x, ptr noalias noundef readonly align 8 captures(none) dereferenceable(24) %0) unnamed_addr #2 {
start:
  %1 = getelementptr inbounds nuw i8, ptr %0, i64 16
  %_3 = load i32, ptr %1, align 8, !noundef !2
  %_2 = zext i32 %_3 to i64
  %_0 = xor i64 %x, %_2
  ret i64 %_0
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: readwrite) uwtable
define noundef i64 @abi_unique(ptr noalias noundef align 8 captures(none) dereferenceable(8) %x) unnamed_addr #0 {
start:
  %_3 = load i64, ptr %x, align 8, !noundef !2
  %_2 = add i64 %_3, 1
  store i64 %_2, ptr %x, align 8
  ret i64 %_2
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable
define void @abi_unit() unnamed_addr #1 {
start:
  ret void
}

; Function Attrs: noinline nounwind uwtable
define noundef i64 @abi_vararg_driver(i32 noundef %x, double noundef %y) unnamed_addr #3 {
start:
  %_3 = tail call noundef i64 (i32, ...) @abi_opaque_vararg(i32 noundef 1, i32 noundef %x, double noundef %y, ptr noundef null) #6
  %_0 = add i64 %_3, 1
  ret i64 %_0
}

; Function Attrs: mustprogress nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #4

; Function Attrs: nounwind uwtable
declare noundef i64 @abi_opaque_twelve(i64 noundef, i64 noundef, i64 noundef, i64 noundef, i64 noundef, i64 noundef, i64 noundef, i64 noundef, i64 noundef, i64 noundef, i64 noundef, i64 noundef) unnamed_addr #5

; Function Attrs: nounwind uwtable
declare noundef i64 @abi_opaque_vararg(i32 noundef, ...) unnamed_addr #5

attributes #0 = { mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: readwrite) uwtable "target-cpu"="x86-64" "target-features"="+cx16,+sse,+sse2,+sse3,+sahf" }
attributes #1 = { mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) uwtable "target-cpu"="x86-64" "target-features"="+cx16,+sse,+sse2,+sse3,+sahf" }
attributes #2 = { mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: read) uwtable "target-cpu"="x86-64" "target-features"="+cx16,+sse,+sse2,+sse3,+sahf" }
attributes #3 = { noinline nounwind uwtable "target-cpu"="x86-64" "target-features"="+cx16,+sse,+sse2,+sse3,+sahf" }
attributes #4 = { mustprogress nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { nounwind uwtable "target-cpu"="x86-64" "target-features"="+cx16,+sse,+sse2,+sse3,+sahf" }
attributes #6 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{!"rustc version 1.97.0-nightly (f53b654a8 2026-04-30)"}
!2 = !{}
