; ModuleID = 'empirical_probe.7a40d4b2119fcb1a-cgu.0'
source_filename = "empirical_probe.7a40d4b2119fcb1a-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_a58c3db7b11286242761139ba19a1a81 = private unnamed_addr constant [129 x i8] c".", align 1, !guid !0
@alloc_5039019bfe2ea52d0c777491f62bc6e8 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_a58c3db7b11286242761139ba19a1a81, [16 x i8] c"\80\00\00\00\00\00\00\00\98\00\00\00\05\00\00\00" }>, align 8, !guid !1

; <u8>::wrapping_add
; Function Attrs: alwaysinline nonlazybind uwtable
define internal noundef i8 @_RNvMs4_NtCsdse6LlLb5Hq_4core3numh12wrapping_add(i8 noundef %self, i8 noundef %rhs) unnamed_addr #0 !guid !6 {
start:
  %_0 = add i8 %self, %rhs
  ret i8 %_0
}

; <u32>::wrapping_add
; Function Attrs: alwaysinline nonlazybind uwtable
define internal noundef i32 @_RNvMs6_NtCsdse6LlLb5Hq_4core3numm12wrapping_add(i32 noundef %self, i32 noundef %rhs) unnamed_addr #0 !guid !7 {
start:
  %_0 = add i32 %self, %rhs
  ret i32 %_0
}

; <u64>::wrapping_add
; Function Attrs: alwaysinline nonlazybind uwtable
define internal noundef i64 @_RNvMs7_NtCsdse6LlLb5Hq_4core3numy12wrapping_add(i64 noundef %self, i64 noundef %rhs) unnamed_addr #0 !guid !8 {
start:
  %_0 = add i64 %self, %rhs
  ret i64 %_0
}

; <u64>::wrapping_sub
; Function Attrs: alwaysinline nonlazybind uwtable
define internal noundef i64 @_RNvMs7_NtCsdse6LlLb5Hq_4core3numy12wrapping_sub(i64 noundef %self, i64 noundef %rhs) unnamed_addr #0 !guid !9 {
start:
  %_0 = sub i64 %self, %rhs
  ret i64 %_0
}

; <core::num::nonzero::NonZero<u64>>::get
; Function Attrs: inlinehint nonlazybind uwtable
define internal noundef i64 @_RNvMsi_NtNtCsdse6LlLb5Hq_4core3num7nonzeroINtB5_7NonZeroyE3getCsauKzrKesPwc_15empirical_probe(i64 noundef range(i64 1, 0) %self) unnamed_addr #1 !guid !10 {
start:
  %0 = sub i64 %self, 1
  %1 = icmp ule i64 %0, -2
  call void @llvm.assume(i1 %1)
  ret i64 %self
}

; Function Attrs: nonlazybind uwtable
define noundef i64 @probe_checked_arith_and_assert(i64 noundef %x, i64 noundef %y, i64 noundef %z) unnamed_addr #2 !guid !11 {
start:
  %_5.0 = add i64 %x, %y
  %_5.1 = icmp ult i64 %_5.0, %x
  br i1 %_5.1, label %panic, label %bb1

bb1:                                              ; preds = %start
  %0 = call { i64, i1 } @llvm.umul.with.overflow.i64(i64 %z, i64 %_5.0)
  %_6.0 = extractvalue { i64, i1 } %0, 0
  %_6.1 = extractvalue { i64, i1 } %0, 1
  br i1 %_6.1, label %panic1, label %bb2

panic:                                            ; preds = %start
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCsdse6LlLb5Hq_4core9panicking11panic_const24panic_const_add_overflow(ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_5039019bfe2ea52d0c777491f62bc6e8) #10
  unreachable

bb2:                                              ; preds = %bb1
  ret i64 %_6.0

panic1:                                           ; preds = %bb1
; call core::panicking::panic_const::panic_const_mul_overflow
  call void @_RNvNtNtCsdse6LlLb5Hq_4core9panicking11panic_const24panic_const_mul_overflow(ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_5039019bfe2ea52d0c777491f62bc6e8) #10
  unreachable
}

; Function Attrs: nonlazybind uwtable
define noundef i8 @probe_multi_niche_decode(i8 noundef range(i8 7, 13) %0) unnamed_addr #2 !guid !12 {
start:
  %_0 = alloca [1 x i8], align 1
  %val = alloca [1 x i8], align 1
  store i8 %0, ptr %val, align 1
  %1 = load i8, ptr %val, align 1, !range !13, !noundef !14
  %2 = sub i8 %1, 7
  %3 = zext i8 %2 to i64
  %4 = icmp ule i8 %1, 9
  %_2 = select i1 %4, i64 %3, i64 3
  switch i64 %_2, label %bb1 [
    i64 0, label %bb5
    i64 1, label %bb4
    i64 2, label %bb3
    i64 3, label %bb2
  ]

bb1:                                              ; preds = %start
  unreachable

bb5:                                              ; preds = %start
  store i8 1, ptr %_0, align 1
  br label %bb6

bb4:                                              ; preds = %start
  store i8 2, ptr %_0, align 1
  br label %bb6

bb3:                                              ; preds = %start
  store i8 3, ptr %_0, align 1
  br label %bb6

bb2:                                              ; preds = %start
  %p = load i8, ptr %val, align 1, !range !15, !noundef !14
  store i8 %p, ptr %_0, align 1
  br label %bb6

bb6:                                              ; preds = %bb2, %bb3, %bb4, %bb5
  %5 = load i8, ptr %_0, align 1, !noundef !14
  ret i8 %5
}

; Function Attrs: nonlazybind uwtable
define noundef range(i8 7, 13) i8 @probe_multi_niche_encode(i8 noundef %which, i8 noundef range(i8 10, 13) %p) unnamed_addr #2 !guid !16 {
start:
  %_0 = alloca [1 x i8], align 1
  switch i8 %which, label %bb1 [
    i8 0, label %bb4
    i8 1, label %bb3
    i8 2, label %bb2
  ]

bb1:                                              ; preds = %start
  store i8 %p, ptr %_0, align 1
  br label %bb5

bb4:                                              ; preds = %start
  store i8 7, ptr %_0, align 1
  br label %bb5

bb3:                                              ; preds = %start
  store i8 8, ptr %_0, align 1
  br label %bb5

bb2:                                              ; preds = %start
  store i8 9, ptr %_0, align 1
  br label %bb5

bb5:                                              ; preds = %bb1, %bb2, %bb3, %bb4
  %0 = load i8, ptr %_0, align 1, !range !13, !noundef !14
  ret i8 %0
}

; Function Attrs: nonlazybind uwtable
define noundef i64 @probe_option_nonzero_pair(i64 noundef %0, i64 %1) unnamed_addr #2 !guid !17 {
start:
  %_0 = alloca [8 x i8], align 8
  %opt = alloca [16 x i8], align 8
  store i64 %0, ptr %opt, align 8
  %2 = getelementptr inbounds i8, ptr %opt, i64 8
  store i64 %1, ptr %2, align 8
  %3 = load i64, ptr %opt, align 8, !noundef !14
  %4 = getelementptr inbounds i8, ptr %opt, i64 8
  %5 = load i64, ptr %4, align 8
  %6 = icmp eq i64 %3, 0
  %_2 = select i1 %6, i64 0, i64 1
  %7 = trunc nuw i64 %_2 to i1
  br i1 %7, label %bb3, label %bb2

bb3:                                              ; preds = %start
  %nz = load i64, ptr %opt, align 8, !range !18, !noundef !14
  %8 = getelementptr inbounds i8, ptr %opt, i64 8
  %extra = load i64, ptr %8, align 8, !noundef !14
; call <core::num::nonzero::NonZero<u64>>::get
  %_5 = call noundef i64 @_RNvMsi_NtNtCsdse6LlLb5Hq_4core3num7nonzeroINtB5_7NonZeroyE3getCsauKzrKesPwc_15empirical_probe(i64 noundef %nz)
; call <u64>::wrapping_add
  %9 = call noundef i64 @_RNvMs7_NtCsdse6LlLb5Hq_4core3numy12wrapping_add(i64 noundef %_5, i64 noundef %extra)
  store i64 %9, ptr %_0, align 8
  br label %bb6

bb2:                                              ; preds = %start
  store i64 0, ptr %_0, align 8
  br label %bb6

bb6:                                              ; preds = %bb3, %bb2
  %10 = load i64, ptr %_0, align 8, !noundef !14
  ret i64 %10

bb1:                                              ; No predecessors!
  unreachable
}

; Function Attrs: nonlazybind uwtable
define noundef i64 @probe_option_nonzero_scalar(i64 noundef %0) unnamed_addr #2 !guid !19 {
start:
  %_0 = alloca [8 x i8], align 8
  %opt = alloca [8 x i8], align 8
  store i64 %0, ptr %opt, align 8
  %1 = load i64, ptr %opt, align 8, !noundef !14
  %2 = icmp eq i64 %1, 0
  %_2 = select i1 %2, i64 0, i64 1
  %3 = trunc nuw i64 %_2 to i1
  br i1 %3, label %bb3, label %bb2

bb3:                                              ; preds = %start
  %v = load i64, ptr %opt, align 8, !range !18, !noundef !14
; call <core::num::nonzero::NonZero<u64>>::get
  %4 = call noundef i64 @_RNvMsi_NtNtCsdse6LlLb5Hq_4core3num7nonzeroINtB5_7NonZeroyE3getCsauKzrKesPwc_15empirical_probe(i64 noundef %v)
  store i64 %4, ptr %_0, align 8
  br label %bb5

bb2:                                              ; preds = %start
  store i64 0, ptr %_0, align 8
  br label %bb5

bb5:                                              ; preds = %bb3, %bb2
  %5 = load i64, ptr %_0, align 8, !noundef !14
  ret i64 %5

bb1:                                              ; No predecessors!
  unreachable
}

; Function Attrs: nounwind nonlazybind uwtable
define i64 @probe_pass_mode_cast_caller(i8 noundef zeroext %a, i32 noundef %b) unnamed_addr #3 !guid !20 {
start:
  %0 = alloca [8 x i8], align 8
  %1 = alloca [8 x i8], align 8
  %2 = alloca [8 x i8], align 4
  %_0 = alloca [8 x i8], align 4
  store i8 %a, ptr %2, align 4
  %3 = getelementptr inbounds i8, ptr %2, i64 4
  store i32 %b, ptr %3, align 4
  call void @llvm.lifetime.start.p0(ptr %1)
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 4 %2, i64 8, i1 false)
  %4 = load i64, ptr %1, align 8
  call void @llvm.lifetime.end.p0(ptr %1)
  %5 = call i64 @probe_pass_mode_cast_modify(i64 %4) #11
  call void @llvm.lifetime.start.p0(ptr %0)
  store i64 %5, ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %_0, ptr align 8 %0, i64 8, i1 false)
  call void @llvm.lifetime.end.p0(ptr %0)
  %6 = load i64, ptr %_0, align 4
  ret i64 %6
}

; Function Attrs: nounwind nonlazybind uwtable
define i64 @probe_pass_mode_cast_construct(i8 noundef zeroext %a, i32 noundef %b) unnamed_addr #3 !guid !21 {
start:
  %_0 = alloca [8 x i8], align 4
  store i8 %a, ptr %_0, align 4
  %0 = getelementptr inbounds i8, ptr %_0, i64 4
  store i32 %b, ptr %0, align 4
  %1 = load i64, ptr %_0, align 4
  ret i64 %1
}

; Function Attrs: nounwind nonlazybind uwtable
define i64 @probe_pass_mode_cast_modify(i64 %0) unnamed_addr #3 personality ptr @_RNvCseTBOuNxBJBZ_7___rustc19rust_eh_personality !guid !22 {
start:
  %_0 = alloca [8 x i8], align 4
  %1 = alloca [8 x i8], align 8
  %p = alloca [8 x i8], align 4
  call void @llvm.lifetime.start.p0(ptr %1)
  store i64 %0, ptr %1, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %p, ptr align 8 %1, i64 8, i1 false)
  call void @llvm.lifetime.end.p0(ptr %1)
  %_3 = load i8, ptr %p, align 4, !noundef !14
; invoke <u8>::wrapping_add
  %_2 = invoke noundef i8 @_RNvMs4_NtCsdse6LlLb5Hq_4core3numh12wrapping_add(i8 noundef %_3, i8 noundef 1)
          to label %bb1 unwind label %terminate

terminate:                                        ; preds = %bb1, %start
  %2 = landingpad { ptr, i32 }
          filter [0 x ptr] zeroinitializer
; call core::panicking::panic_cannot_unwind
  call void @_RNvNtCsdse6LlLb5Hq_4core9panicking19panic_cannot_unwind() #12
  unreachable

bb1:                                              ; preds = %start
  store i8 %_2, ptr %p, align 4
  %3 = getelementptr inbounds i8, ptr %p, i64 4
  %_5 = load i32, ptr %3, align 4, !noundef !14
; invoke <u32>::wrapping_add
  %_4 = invoke noundef i32 @_RNvMs6_NtCsdse6LlLb5Hq_4core3numm12wrapping_add(i32 noundef %_5, i32 noundef 2)
          to label %bb2 unwind label %terminate

bb2:                                              ; preds = %bb1
  %4 = getelementptr inbounds i8, ptr %p, i64 4
  store i32 %_4, ptr %4, align 4
  %5 = load i8, ptr %p, align 4, !noundef !14
  %6 = getelementptr inbounds i8, ptr %p, i64 4
  %7 = load i32, ptr %6, align 4, !noundef !14
  store i8 %5, ptr %_0, align 4
  %8 = getelementptr inbounds i8, ptr %_0, i64 4
  store i32 %7, ptr %8, align 4
  %9 = load i64, ptr %_0, align 4
  ret i64 %9
}

; Function Attrs: nonlazybind uwtable
define noundef i64 @probe_scalar_pair_slice(ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %slice.0, i64 noundef range(i64 0, -9223372036854775808) %slice.1) unnamed_addr #2 !guid !23 {
start:
  ret i64 %slice.1
}

; Function Attrs: nonlazybind uwtable
define { i64, i64 } @probe_scalar_pair_tuple(i64 noundef %pair.0, i64 noundef %pair.1) unnamed_addr #2 !guid !24 {
start:
; call <u64>::wrapping_add
  %_2 = call noundef i64 @_RNvMs7_NtCsdse6LlLb5Hq_4core3numy12wrapping_add(i64 noundef %pair.1, i64 noundef 1)
  %0 = insertvalue { i64, i64 } poison, i64 %_2, 0
  %1 = insertvalue { i64, i64 } %0, i64 %pair.0, 1
  ret { i64, i64 } %1
}

; Function Attrs: nonlazybind uwtable
define noundef i64 @probe_ssa_vs_alloca(i1 noundef zeroext %cond, i64 noundef %x, i64 noundef %y) unnamed_addr #2 !guid !25 {
start:
  %pinned = alloca [8 x i8], align 8
  %acc = alloca [8 x i8], align 8
; call <u64>::wrapping_add
  %ssa_tmp = call noundef i64 @_RNvMs7_NtCsdse6LlLb5Hq_4core3numy12wrapping_add(i64 noundef %x, i64 noundef 1)
  store i64 %ssa_tmp, ptr %acc, align 8
  br i1 %cond, label %bb2, label %bb4

bb4:                                              ; preds = %start
  %0 = load i64, ptr %acc, align 8, !noundef !14
; call <u64>::wrapping_sub
  %_7 = call noundef i64 @_RNvMs7_NtCsdse6LlLb5Hq_4core3numy12wrapping_sub(i64 noundef %0, i64 noundef %y)
  store i64 %_7, ptr %acc, align 8
  br label %bb6

bb2:                                              ; preds = %start
  %1 = load i64, ptr %acc, align 8, !noundef !14
; call <u64>::wrapping_add
  %_6 = call noundef i64 @_RNvMs7_NtCsdse6LlLb5Hq_4core3numy12wrapping_add(i64 noundef %1, i64 noundef %y)
  store i64 %_6, ptr %acc, align 8
  br label %bb6

bb6:                                              ; preds = %bb2, %bb4
  call void @llvm.lifetime.start.p0(ptr %pinned)
  store i64 %ssa_tmp, ptr %pinned, align 8
  %loaded = load i64, ptr %pinned, align 8, !noundef !14
  %2 = load i64, ptr %acc, align 8, !noundef !14
; call <u64>::wrapping_add
  %_0 = call noundef i64 @_RNvMs7_NtCsdse6LlLb5Hq_4core3numy12wrapping_add(i64 noundef %2, i64 noundef %loaded)
  call void @llvm.lifetime.end.p0(ptr %pinned)
  ret i64 %_0
}

; Function Attrs: nonlazybind uwtable
define noundef i64 @probe_transmute_padded_to_u64(i8 noundef %p.0, i32 noundef %p.1) unnamed_addr #2 !guid !26 {
start:
  %0 = alloca [8 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr %0)
  store i8 %p.0, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 4
  store i32 %p.1, ptr %1, align 4
  %_0 = load i64, ptr %0, align 8, !noundef !14
  call void @llvm.lifetime.end.p0(ptr %0)
  ret i64 %_0
}

; Function Attrs: nonlazybind uwtable
define noundef i64 @probe_transmute_pair_to_u64(i32 noundef %pair.0, i32 noundef %pair.1) unnamed_addr #2 !guid !27 {
start:
  %0 = alloca [8 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr %0)
  store i32 %pair.0, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 4
  store i32 %pair.1, ptr %1, align 4
  %_0 = load i64, ptr %0, align 8, !noundef !14
  call void @llvm.lifetime.end.p0(ptr %0)
  ret i64 %_0
}

; Function Attrs: nonlazybind uwtable
define { i32, i32 } @probe_transmute_u64_to_pair(i64 noundef %bits) unnamed_addr #2 !guid !28 {
start:
  %0 = alloca [8 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr %0)
  store i64 %bits, ptr %0, align 8
  %_0.0 = load i32, ptr %0, align 8, !noundef !14
  %1 = getelementptr inbounds i8, ptr %0, i64 4
  %_0.1 = load i32, ptr %1, align 4, !noundef !14
  call void @llvm.lifetime.end.p0(ptr %0)
  %2 = insertvalue { i32, i32 } poison, i32 %_0.0, 0
  %3 = insertvalue { i32, i32 } %2, i32 %_0.1, 1
  ret { i32, i32 } %3
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: write)
declare void @llvm.assume(i1 noundef) #4

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @_RNvNtNtCsdse6LlLb5Hq_4core9panicking11panic_const24panic_const_add_overflow(ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24)) unnamed_addr #5

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare { i64, i1 } @llvm.umul.with.overflow.i64(i64, i64) #6

; core::panicking::panic_const::panic_const_mul_overflow
; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @_RNvNtNtCsdse6LlLb5Hq_4core9panicking11panic_const24panic_const_mul_overflow(ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24)) unnamed_addr #5

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #7

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #7

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #7

; __rustc::rust_eh_personality
; Function Attrs: nonlazybind
declare i32 @_RNvCseTBOuNxBJBZ_7___rustc19rust_eh_personality(...) unnamed_addr #8

; core::panicking::panic_cannot_unwind
; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize uwtable
declare void @_RNvNtCsdse6LlLb5Hq_4core9panicking19panic_cannot_unwind() unnamed_addr #9

attributes #0 = { alwaysinline nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { inlinehint nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: write) }
attributes #5 = { cold noinline noreturn nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #6 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #7 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #8 = { nonlazybind "target-cpu"="x86-64" }
attributes #9 = { cold minsize noinline noreturn nounwind nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #10 = { noreturn }
attributes #11 = { nounwind }
attributes #12 = { cold noreturn nounwind }

!llvm.module.flags = !{!2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i64 -2804670625332872641}
!1 = !{i64 -3458169953284201831}
!2 = !{i32 8, !"PIC Level", i32 2}
!3 = !{i32 2, !"RtLibUseGOT", i32 1}
!4 = !{i32 7, !"uwtable", i32 2}
!5 = !{!"rustc version 1.101.0-nightly (19833af72 2026-10-20)"}
!6 = !{i64 748183398112412565}
!7 = !{i64 -4937048998391661937}
!8 = !{i64 6544553068242030546}
!9 = !{i64 -175555448060685932}
!10 = !{i64 -5396442737790373988}
!11 = !{i64 -3677371460121889096}
!12 = !{i64 3210987519311567330}
!13 = !{i8 7, i8 13}
!14 = !{}
!15 = !{i8 10, i8 13}
!16 = !{i64 -5990659863568369796}
!17 = !{i64 -8194647078898378202}
!18 = !{i64 1, i64 0}
!19 = !{i64 -1322442240486915806}
!20 = !{i64 3423518642781525320}
!21 = !{i64 6931109928988637295}
!22 = !{i64 -6303934027020426049}
!23 = !{i64 4744087910439151659}
!24 = !{i64 -1377383003982573574}
!25 = !{i64 643916505221030202}
!26 = !{i64 -3008199192154590144}
!27 = !{i64 -2957856993050690530}
!28 = !{i64 4743840703113269511}
