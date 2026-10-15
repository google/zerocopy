; ModuleID = 'abi_vectors.bc15791f4c5649f0-cgu.0'
source_filename = "abi_vectors.bc15791f4c5649f0-cgu.0"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "arm64-apple-macosx11.0.0"

@abi_system_vector = unnamed_addr alias <4 x i32> (<4 x i32>), ptr @abi_c_vector

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none)
define <4 x i32> @abi_c_vector(<4 x i32> returned %x) unnamed_addr #0 {
start:
  ret <4 x i32> %x
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: readwrite)
define void @abi_rust_vector(ptr dead_on_unwind noalias noundef writable writeonly sret([16 x i8]) align 16 captures(none) dereferenceable(16) initializes((0, 16)) %_0, ptr dead_on_return noalias noundef readonly align 16 captures(none) dereferenceable(16) %x) unnamed_addr #1 {
start:
  %0 = load <4 x i32>, ptr %x, align 16
  store <4 x i32> %0, ptr %_0, align 16
  ret void
}

attributes #0 = { mustprogress nofree noinline norecurse nosync nounwind willreturn memory(none) "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #1 = { mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: readwrite) "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{!"rustc version 1.97.0-nightly (f53b654a8 2026-04-30)"}
