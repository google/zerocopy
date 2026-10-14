; ModuleID = 'pilot.e3b020646cbbfdd0-cgu.0'
source_filename = "pilot.e3b020646cbbfdd0-cgu.0"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "arm64-apple-macosx11.0.0"

module asm(target_cpu: "apple-m1")
    ".section __TEXT,__text,regular,pure_instructions"
    ".balign 4"
    ".globl _naked_add"
    "_naked_add:"
    "add x0, x0, x1"
    "ret"
    ".Lfunc_end__naked_add:"
    ".section __TEXT,__text,regular,pure_instructions"
    ".balign 4"
    ".globl _naked_store"
    "_naked_store:"
    "str x1, [x0]"
    "ret"
    ".Lfunc_end__naked_store:"

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none)
define [2 x i64] @c_pair([2 x i64] %0) unnamed_addr #0 !guid !3 {
start:
  %.fca.0.extract = extractvalue [2 x i64] %0, 0
  %.fca.1.extract = extractvalue [2 x i64] %0, 1
  %.fca.0.insert = insertvalue [2 x i64] poison, i64 %.fca.1.extract, 0
  %.fca.1.insert = insertvalue [2 x i64] %.fca.0.insert, i64 %.fca.0.extract, 1
  ret [2 x i64] %.fca.1.insert
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(argmem: readwrite)
define void @c_triple(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([24 x i8]) align 8 captures(none) dereferenceable(24) initializes((0, 24)) %_0, ptr noalias nofree noundef readonly align 8 captures(none) dead_on_return dereferenceable(24) %a) unnamed_addr #1 !guid !4 {
start:
  %0 = getelementptr inbounds nuw i8, ptr %a, i64 8
  %_4 = load i64, ptr %a, align 8, !noundef !5
  %1 = load <2 x i64>, ptr %0, align 8
  %2 = shufflevector <2 x i64> %1, <2 x i64> poison, <2 x i32> <i32 1, i32 0>
  store <2 x i64> %2, ptr %_0, align 8
  %3 = getelementptr inbounds nuw i8, ptr %_0, i64 16
  store i64 %_4, ptr %3, align 8
  ret void
}

; Function Attrs: mustprogress nofree nosync nounwind willreturn memory(none)
define noundef i64 @inline_add(i64 noundef %a, i64 noundef %b) unnamed_addr #2 !guid !6 {
start:
  %0 = tail call i64 asm "add ${0}, ${1}, ${2}", "=r,r,r,~{cc}"(i64 %a, i64 %b) #4, !srcloc !7
  ret i64 %0
}

; Function Attrs: nounwind memory(read, inaccessiblemem: readwrite)
define noundef zeroext i8 @inline_load(ptr noundef %p) unnamed_addr #3 !guid !8 {
start:
  %0 = tail call i32 asm sideeffect "ldrb ${0:w}, [${1}]", "=r,r,~{cc},~{memory}"(ptr %p) #5, !srcloc !9
  %_0 = trunc i32 %0 to i8
  ret i8 %_0
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none)
define noundef i64 @rust_add(i64 noundef %a, i64 noundef %b) unnamed_addr #0 !guid !10 {
start:
  %_0 = add i64 %b, %a
  ret i64 %_0
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none)
define { i64, i64 } @rust_pair(i64 noundef %a.0, i64 noundef %a.1) unnamed_addr #0 !guid !11 {
start:
  %0 = insertvalue { i64, i64 } poison, i64 %a.1, 0
  %1 = insertvalue { i64, i64 } %0, i64 %a.0, 1
  ret { i64, i64 } %1
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none)
define noundef range(i64 0, -9223372036854775808) i64 @rust_slice(ptr noalias nofree noundef nonnull readonly captures(none) %a.0, i64 noundef returned range(i64 0, -9223372036854775808) %a.1) unnamed_addr #0 !guid !12 {
start:
  ret i64 %a.1
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none)
define void @rust_unit() unnamed_addr #0 !guid !13 {
start:
  ret void
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind willreturn memory(none) "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #1 = { mustprogress nofree norecurse nosync nounwind willreturn memory(argmem: readwrite) "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #2 = { mustprogress nofree nosync nounwind willreturn memory(none) "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #3 = { nounwind memory(read, inaccessiblemem: readwrite) "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #4 = { nounwind willreturn memory(none) }
attributes #5 = { nounwind memory(read, inaccessiblemem: readwrite) }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 7, !"frame-pointer", i32 1}
!2 = !{!"rustc version 1.99.0 (b940084d7 2026-09-28)"}
!3 = !{i64 5286678134838979282}
!4 = !{i64 2611214780525556032}
!5 = !{}
!6 = !{i64 2649754275034584549}
!7 = !{i64 1202590843141}
!8 = !{i64 5799125265474596827}
!9 = !{i64 2890512990862}
!10 = !{i64 -7185409316468286058}
!11 = !{i64 -1938512751433902825}
!12 = !{i64 -6639879649526911278}
!13 = !{i64 4105278056781235846}
