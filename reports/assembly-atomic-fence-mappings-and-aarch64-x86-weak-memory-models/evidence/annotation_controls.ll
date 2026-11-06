; ModuleID = 'annotation_controls.33ad15d571ef0aad-cgu.0'
source_filename = "annotation_controls.33ad15d571ef0aad-cgu.0"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "arm64-apple-macosx11.0.0"

; Function Attrs: nounwind uwtable
define noundef i32 @annotation_complete(ptr noalias noundef align 4 dereferenceable(4) initializes((0, 4)) %cell) unnamed_addr #0 {
start:
  store i32 7, ptr %cell, align 4
  tail call void asm sideeffect "str ${1:w}, [${0}]", "r,r,~{memory}"(ptr nonnull %cell, i32 9) #3, !srcloc !2
  %_0 = load i32, ptr %cell, align 4, !noundef !3
  ret i32 %_0
}

; Function Attrs: nounwind memory(argmem: write, inaccessiblemem: readwrite) uwtable
define noundef i32 @annotation_wrong_nomem(ptr noalias noundef align 4 dereferenceable(4) initializes((0, 4)) %cell) unnamed_addr #1 {
start:
  store i32 7, ptr %cell, align 4
  tail call void asm sideeffect "str ${1:w}, [${0}]", "r,r"(ptr nonnull %cell, i32 9) #4, !srcloc !4
  ret i32 7
}

; Function Attrs: nounwind memory(read, argmem: readwrite, inaccessiblemem: readwrite) uwtable
define noundef i32 @annotation_wrong_readonly(ptr noalias noundef align 4 dereferenceable(4) initializes((0, 4)) %cell) unnamed_addr #2 {
start:
  store i32 7, ptr %cell, align 4
  tail call void asm sideeffect "str ${1:w}, [${0}]", "r,r,~{memory}"(ptr nonnull %cell, i32 9) #5, !srcloc !5
  ret i32 7
}

attributes #0 = { nounwind uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #1 = { nounwind memory(argmem: write, inaccessiblemem: readwrite) uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #2 = { nounwind memory(read, argmem: readwrite, inaccessiblemem: readwrite) uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #3 = { nounwind }
attributes #4 = { nounwind memory(inaccessiblemem: readwrite) }
attributes #5 = { nounwind memory(read, inaccessiblemem: readwrite) }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{!"rustc version 1.97.0-nightly (f53b654a8 2026-04-30)"}
!2 = !{i64 1099511628006}
!3 = !{}
!4 = !{i64 2525440770610}
!5 = !{i64 4007204488075}
