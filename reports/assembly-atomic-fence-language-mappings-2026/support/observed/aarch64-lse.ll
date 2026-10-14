; ModuleID = '<task-workspace>/work/research/phase2-minirust-foundations/assembly-atomic-fence-language-mappings-2026/support/atomics.c'
source_filename = "<task-workspace>/work/research/phase2-minirust-foundations/assembly-atomic-fence-language-mappings-2026/support/atomics.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "aarch64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite)
define dso_local i64 @load_relaxed(ptr noundef readonly captures(none) %0) local_unnamed_addr #0 {
  %2 = load atomic i64, ptr %0 monotonic, align 8
  ret i64 %2
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite)
define dso_local i64 @load_acquire(ptr noundef readonly captures(none) %0) local_unnamed_addr #0 {
  %2 = load atomic i64, ptr %0 acquire, align 8
  ret i64 %2
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite)
define dso_local i64 @load_seq_cst(ptr noundef readonly captures(none) %0) local_unnamed_addr #0 {
  %2 = load atomic i64, ptr %0 seq_cst, align 8
  ret i64 %2
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite)
define dso_local void @store_relaxed(ptr noundef writeonly captures(none) %0, i64 noundef %1) local_unnamed_addr #0 {
  store atomic i64 %1, ptr %0 monotonic, align 8
  ret void
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite)
define dso_local void @store_release(ptr noundef writeonly captures(none) %0, i64 noundef %1) local_unnamed_addr #0 {
  store atomic i64 %1, ptr %0 release, align 8
  ret void
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite)
define dso_local void @store_seq_cst(ptr noundef writeonly captures(none) %0, i64 noundef %1) local_unnamed_addr #0 {
  store atomic i64 %1, ptr %0 seq_cst, align 8
  ret void
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite)
define dso_local i64 @add_relaxed(ptr noundef captures(none) %0, i64 noundef %1) local_unnamed_addr #0 {
  %3 = atomicrmw add ptr %0, i64 %1 monotonic, align 8
  ret i64 %3
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite)
define dso_local i64 @add_acq_rel(ptr noundef captures(none) %0, i64 noundef %1) local_unnamed_addr #0 {
  %3 = atomicrmw add ptr %0, i64 %1 acq_rel, align 8
  ret i64 %3
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite)
define dso_local i64 @add_seq_cst(ptr noundef captures(none) %0, i64 noundef %1) local_unnamed_addr #0 {
  %3 = atomicrmw add ptr %0, i64 %1 seq_cst, align 8
  ret i64 %3
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite)
define dso_local noundef i1 @cas_acq_rel(ptr noundef captures(none) %0, ptr noundef captures(none) %1, i64 noundef %2) local_unnamed_addr #0 {
  %4 = load i64, ptr %1, align 8
  %5 = cmpxchg ptr %0, i64 %4, i64 %2 acq_rel acquire, align 8
  %6 = extractvalue { i64, i1 } %5, 1
  br i1 %6, label %9, label %7

7:                                                ; preds = %3
  %8 = extractvalue { i64, i1 } %5, 0
  store i64 %8, ptr %1, align 8
  br label %9

9:                                                ; preds = %7, %3
  ret i1 %6
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn
define dso_local void @fence_acquire() local_unnamed_addr #1 {
  fence acquire
  ret void
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn
define dso_local void @fence_release() local_unnamed_addr #1 {
  fence release
  ret void
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn
define dso_local void @fence_acq_rel() local_unnamed_addr #1 {
  fence acq_rel
  ret void
}

; Function Attrs: mustprogress nofree norecurse nounwind willreturn
define dso_local void @fence_seq_cst() local_unnamed_addr #1 {
  fence seq_cst
  ret void
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn
define dso_local void @signal_seq_cst() local_unnamed_addr #2 {
  fence syncscope("singlethread") seq_cst
  ret void
}

; Function Attrs: nounwind
define dso_local void @compiler_barrier() local_unnamed_addr #3 {
  tail call void asm sideeffect "", "~{memory}"() #4, !srcloc !5
  ret void
}

; Function Attrs: nounwind
define dso_local void @explicit_hw_fence() local_unnamed_addr #3 {
  tail call void asm sideeffect "dmb ish", "~{memory}"() #4, !srcloc !6
  ret void
}

attributes #0 = { mustprogress nofree norecurse nounwind willreturn memory(argmem: readwrite) "frame-pointer"="non-leaf" "no-builtins" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+crc,+fp-armv8,+lse,+neon,+rdm,+v8.1a,+v8a,-fmv,-outline-atomics" }
attributes #1 = { mustprogress nofree norecurse nounwind willreturn "frame-pointer"="non-leaf" "no-builtins" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+crc,+fp-armv8,+lse,+neon,+rdm,+v8.1a,+v8a,-fmv,-outline-atomics" }
attributes #2 = { mustprogress nofree norecurse nosync nounwind willreturn "frame-pointer"="non-leaf" "no-builtins" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+crc,+fp-armv8,+lse,+neon,+rdm,+v8.1a,+v8a,-fmv,-outline-atomics" }
attributes #3 = { nounwind "frame-pointer"="non-leaf" "no-builtins" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+crc,+fp-armv8,+lse,+neon,+rdm,+v8.1a,+v8a,-fmv,-outline-atomics" }
attributes #4 = { nounwind }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"frame-pointer", i32 1}
!4 = !{!"Apple clang version 21.0.0 (clang-2100.3.34.2)"}
!5 = !{i64 1289}
!6 = !{i64 1390}
