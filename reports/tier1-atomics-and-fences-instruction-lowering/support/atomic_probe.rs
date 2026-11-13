#![no_std]
#![allow(internal_features)]
#![feature(core_intrinsics)]
use core::intrinsics::*;
use core::sync::atomic::{Ordering, fence, compiler_fence};

#[no_mangle] pub unsafe fn atomic_load_8_relaxed(p: *const u8) -> u8 { atomic_load::<u8, { AtomicOrdering::Relaxed }>(p) }
#[no_mangle] pub unsafe fn atomic_load_8_acquire(p: *const u8) -> u8 { atomic_load::<u8, { AtomicOrdering::Acquire }>(p) }
#[no_mangle] pub unsafe fn atomic_load_8_seqcst(p: *const u8) -> u8 { atomic_load::<u8, { AtomicOrdering::SeqCst }>(p) }
#[no_mangle] pub unsafe fn atomic_load_16_relaxed(p: *const u16) -> u16 { atomic_load::<u16, { AtomicOrdering::Relaxed }>(p) }
#[no_mangle] pub unsafe fn atomic_load_16_acquire(p: *const u16) -> u16 { atomic_load::<u16, { AtomicOrdering::Acquire }>(p) }
#[no_mangle] pub unsafe fn atomic_load_16_seqcst(p: *const u16) -> u16 { atomic_load::<u16, { AtomicOrdering::SeqCst }>(p) }
#[no_mangle] pub unsafe fn atomic_load_32_relaxed(p: *const u32) -> u32 { atomic_load::<u32, { AtomicOrdering::Relaxed }>(p) }
#[no_mangle] pub unsafe fn atomic_load_32_acquire(p: *const u32) -> u32 { atomic_load::<u32, { AtomicOrdering::Acquire }>(p) }
#[no_mangle] pub unsafe fn atomic_load_32_seqcst(p: *const u32) -> u32 { atomic_load::<u32, { AtomicOrdering::SeqCst }>(p) }
#[no_mangle] pub unsafe fn atomic_load_64_relaxed(p: *const u64) -> u64 { atomic_load::<u64, { AtomicOrdering::Relaxed }>(p) }
#[no_mangle] pub unsafe fn atomic_load_64_acquire(p: *const u64) -> u64 { atomic_load::<u64, { AtomicOrdering::Acquire }>(p) }
#[no_mangle] pub unsafe fn atomic_load_64_seqcst(p: *const u64) -> u64 { atomic_load::<u64, { AtomicOrdering::SeqCst }>(p) }
#[no_mangle] pub unsafe fn atomic_store_8_relaxed(p: *mut u8, v: u8) { atomic_store::<u8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_8_release(p: *mut u8, v: u8) { atomic_store::<u8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_8_seqcst(p: *mut u8, v: u8) { atomic_store::<u8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_16_relaxed(p: *mut u16, v: u16) { atomic_store::<u16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_16_release(p: *mut u16, v: u16) { atomic_store::<u16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_16_seqcst(p: *mut u16, v: u16) { atomic_store::<u16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_32_relaxed(p: *mut u32, v: u32) { atomic_store::<u32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_32_release(p: *mut u32, v: u32) { atomic_store::<u32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_32_seqcst(p: *mut u32, v: u32) { atomic_store::<u32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_64_relaxed(p: *mut u64, v: u64) { atomic_store::<u64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_64_release(p: *mut u64, v: u64) { atomic_store::<u64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_store_64_seqcst(p: *mut u64, v: u64) { atomic_store::<u64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_8_relaxed(p: *mut u8, v: u8) -> u8 { atomic_xchg::<u8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_8_acquire(p: *mut u8, v: u8) -> u8 { atomic_xchg::<u8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_8_release(p: *mut u8, v: u8) -> u8 { atomic_xchg::<u8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_8_acqrel(p: *mut u8, v: u8) -> u8 { atomic_xchg::<u8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_8_seqcst(p: *mut u8, v: u8) -> u8 { atomic_xchg::<u8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_16_relaxed(p: *mut u16, v: u16) -> u16 { atomic_xchg::<u16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_16_acquire(p: *mut u16, v: u16) -> u16 { atomic_xchg::<u16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_16_release(p: *mut u16, v: u16) -> u16 { atomic_xchg::<u16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_16_acqrel(p: *mut u16, v: u16) -> u16 { atomic_xchg::<u16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_16_seqcst(p: *mut u16, v: u16) -> u16 { atomic_xchg::<u16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_32_relaxed(p: *mut u32, v: u32) -> u32 { atomic_xchg::<u32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_32_acquire(p: *mut u32, v: u32) -> u32 { atomic_xchg::<u32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_32_release(p: *mut u32, v: u32) -> u32 { atomic_xchg::<u32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_32_acqrel(p: *mut u32, v: u32) -> u32 { atomic_xchg::<u32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_32_seqcst(p: *mut u32, v: u32) -> u32 { atomic_xchg::<u32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_64_relaxed(p: *mut u64, v: u64) -> u64 { atomic_xchg::<u64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_64_acquire(p: *mut u64, v: u64) -> u64 { atomic_xchg::<u64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_64_release(p: *mut u64, v: u64) -> u64 { atomic_xchg::<u64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_64_acqrel(p: *mut u64, v: u64) -> u64 { atomic_xchg::<u64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xchg_64_seqcst(p: *mut u64, v: u64) -> u64 { atomic_xchg::<u64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_8_relaxed(p: *mut u8, v: u8) -> u8 { atomic_xadd::<u8, u8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_8_acquire(p: *mut u8, v: u8) -> u8 { atomic_xadd::<u8, u8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_8_release(p: *mut u8, v: u8) -> u8 { atomic_xadd::<u8, u8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_8_acqrel(p: *mut u8, v: u8) -> u8 { atomic_xadd::<u8, u8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_8_seqcst(p: *mut u8, v: u8) -> u8 { atomic_xadd::<u8, u8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_16_relaxed(p: *mut u16, v: u16) -> u16 { atomic_xadd::<u16, u16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_16_acquire(p: *mut u16, v: u16) -> u16 { atomic_xadd::<u16, u16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_16_release(p: *mut u16, v: u16) -> u16 { atomic_xadd::<u16, u16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_16_acqrel(p: *mut u16, v: u16) -> u16 { atomic_xadd::<u16, u16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_16_seqcst(p: *mut u16, v: u16) -> u16 { atomic_xadd::<u16, u16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_32_relaxed(p: *mut u32, v: u32) -> u32 { atomic_xadd::<u32, u32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_32_acquire(p: *mut u32, v: u32) -> u32 { atomic_xadd::<u32, u32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_32_release(p: *mut u32, v: u32) -> u32 { atomic_xadd::<u32, u32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_32_acqrel(p: *mut u32, v: u32) -> u32 { atomic_xadd::<u32, u32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_32_seqcst(p: *mut u32, v: u32) -> u32 { atomic_xadd::<u32, u32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_64_relaxed(p: *mut u64, v: u64) -> u64 { atomic_xadd::<u64, u64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_64_acquire(p: *mut u64, v: u64) -> u64 { atomic_xadd::<u64, u64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_64_release(p: *mut u64, v: u64) -> u64 { atomic_xadd::<u64, u64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_64_acqrel(p: *mut u64, v: u64) -> u64 { atomic_xadd::<u64, u64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xadd_64_seqcst(p: *mut u64, v: u64) -> u64 { atomic_xadd::<u64, u64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_8_relaxed(p: *mut u8, v: u8) -> u8 { atomic_xsub::<u8, u8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_8_acquire(p: *mut u8, v: u8) -> u8 { atomic_xsub::<u8, u8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_8_release(p: *mut u8, v: u8) -> u8 { atomic_xsub::<u8, u8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_8_acqrel(p: *mut u8, v: u8) -> u8 { atomic_xsub::<u8, u8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_8_seqcst(p: *mut u8, v: u8) -> u8 { atomic_xsub::<u8, u8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_16_relaxed(p: *mut u16, v: u16) -> u16 { atomic_xsub::<u16, u16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_16_acquire(p: *mut u16, v: u16) -> u16 { atomic_xsub::<u16, u16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_16_release(p: *mut u16, v: u16) -> u16 { atomic_xsub::<u16, u16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_16_acqrel(p: *mut u16, v: u16) -> u16 { atomic_xsub::<u16, u16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_16_seqcst(p: *mut u16, v: u16) -> u16 { atomic_xsub::<u16, u16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_32_relaxed(p: *mut u32, v: u32) -> u32 { atomic_xsub::<u32, u32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_32_acquire(p: *mut u32, v: u32) -> u32 { atomic_xsub::<u32, u32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_32_release(p: *mut u32, v: u32) -> u32 { atomic_xsub::<u32, u32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_32_acqrel(p: *mut u32, v: u32) -> u32 { atomic_xsub::<u32, u32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_32_seqcst(p: *mut u32, v: u32) -> u32 { atomic_xsub::<u32, u32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_64_relaxed(p: *mut u64, v: u64) -> u64 { atomic_xsub::<u64, u64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_64_acquire(p: *mut u64, v: u64) -> u64 { atomic_xsub::<u64, u64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_64_release(p: *mut u64, v: u64) -> u64 { atomic_xsub::<u64, u64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_64_acqrel(p: *mut u64, v: u64) -> u64 { atomic_xsub::<u64, u64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xsub_64_seqcst(p: *mut u64, v: u64) -> u64 { atomic_xsub::<u64, u64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_8_relaxed(p: *mut u8, v: u8) -> u8 { atomic_and::<u8, u8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_8_acquire(p: *mut u8, v: u8) -> u8 { atomic_and::<u8, u8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_8_release(p: *mut u8, v: u8) -> u8 { atomic_and::<u8, u8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_8_acqrel(p: *mut u8, v: u8) -> u8 { atomic_and::<u8, u8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_8_seqcst(p: *mut u8, v: u8) -> u8 { atomic_and::<u8, u8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_16_relaxed(p: *mut u16, v: u16) -> u16 { atomic_and::<u16, u16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_16_acquire(p: *mut u16, v: u16) -> u16 { atomic_and::<u16, u16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_16_release(p: *mut u16, v: u16) -> u16 { atomic_and::<u16, u16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_16_acqrel(p: *mut u16, v: u16) -> u16 { atomic_and::<u16, u16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_16_seqcst(p: *mut u16, v: u16) -> u16 { atomic_and::<u16, u16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_32_relaxed(p: *mut u32, v: u32) -> u32 { atomic_and::<u32, u32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_32_acquire(p: *mut u32, v: u32) -> u32 { atomic_and::<u32, u32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_32_release(p: *mut u32, v: u32) -> u32 { atomic_and::<u32, u32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_32_acqrel(p: *mut u32, v: u32) -> u32 { atomic_and::<u32, u32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_32_seqcst(p: *mut u32, v: u32) -> u32 { atomic_and::<u32, u32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_64_relaxed(p: *mut u64, v: u64) -> u64 { atomic_and::<u64, u64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_64_acquire(p: *mut u64, v: u64) -> u64 { atomic_and::<u64, u64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_64_release(p: *mut u64, v: u64) -> u64 { atomic_and::<u64, u64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_64_acqrel(p: *mut u64, v: u64) -> u64 { atomic_and::<u64, u64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_and_64_seqcst(p: *mut u64, v: u64) -> u64 { atomic_and::<u64, u64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_8_relaxed(p: *mut u8, v: u8) -> u8 { atomic_nand::<u8, u8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_8_acquire(p: *mut u8, v: u8) -> u8 { atomic_nand::<u8, u8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_8_release(p: *mut u8, v: u8) -> u8 { atomic_nand::<u8, u8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_8_acqrel(p: *mut u8, v: u8) -> u8 { atomic_nand::<u8, u8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_8_seqcst(p: *mut u8, v: u8) -> u8 { atomic_nand::<u8, u8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_16_relaxed(p: *mut u16, v: u16) -> u16 { atomic_nand::<u16, u16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_16_acquire(p: *mut u16, v: u16) -> u16 { atomic_nand::<u16, u16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_16_release(p: *mut u16, v: u16) -> u16 { atomic_nand::<u16, u16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_16_acqrel(p: *mut u16, v: u16) -> u16 { atomic_nand::<u16, u16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_16_seqcst(p: *mut u16, v: u16) -> u16 { atomic_nand::<u16, u16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_32_relaxed(p: *mut u32, v: u32) -> u32 { atomic_nand::<u32, u32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_32_acquire(p: *mut u32, v: u32) -> u32 { atomic_nand::<u32, u32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_32_release(p: *mut u32, v: u32) -> u32 { atomic_nand::<u32, u32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_32_acqrel(p: *mut u32, v: u32) -> u32 { atomic_nand::<u32, u32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_32_seqcst(p: *mut u32, v: u32) -> u32 { atomic_nand::<u32, u32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_64_relaxed(p: *mut u64, v: u64) -> u64 { atomic_nand::<u64, u64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_64_acquire(p: *mut u64, v: u64) -> u64 { atomic_nand::<u64, u64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_64_release(p: *mut u64, v: u64) -> u64 { atomic_nand::<u64, u64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_64_acqrel(p: *mut u64, v: u64) -> u64 { atomic_nand::<u64, u64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_nand_64_seqcst(p: *mut u64, v: u64) -> u64 { atomic_nand::<u64, u64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_8_relaxed(p: *mut u8, v: u8) -> u8 { atomic_or::<u8, u8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_8_acquire(p: *mut u8, v: u8) -> u8 { atomic_or::<u8, u8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_8_release(p: *mut u8, v: u8) -> u8 { atomic_or::<u8, u8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_8_acqrel(p: *mut u8, v: u8) -> u8 { atomic_or::<u8, u8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_8_seqcst(p: *mut u8, v: u8) -> u8 { atomic_or::<u8, u8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_16_relaxed(p: *mut u16, v: u16) -> u16 { atomic_or::<u16, u16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_16_acquire(p: *mut u16, v: u16) -> u16 { atomic_or::<u16, u16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_16_release(p: *mut u16, v: u16) -> u16 { atomic_or::<u16, u16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_16_acqrel(p: *mut u16, v: u16) -> u16 { atomic_or::<u16, u16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_16_seqcst(p: *mut u16, v: u16) -> u16 { atomic_or::<u16, u16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_32_relaxed(p: *mut u32, v: u32) -> u32 { atomic_or::<u32, u32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_32_acquire(p: *mut u32, v: u32) -> u32 { atomic_or::<u32, u32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_32_release(p: *mut u32, v: u32) -> u32 { atomic_or::<u32, u32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_32_acqrel(p: *mut u32, v: u32) -> u32 { atomic_or::<u32, u32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_32_seqcst(p: *mut u32, v: u32) -> u32 { atomic_or::<u32, u32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_64_relaxed(p: *mut u64, v: u64) -> u64 { atomic_or::<u64, u64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_64_acquire(p: *mut u64, v: u64) -> u64 { atomic_or::<u64, u64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_64_release(p: *mut u64, v: u64) -> u64 { atomic_or::<u64, u64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_64_acqrel(p: *mut u64, v: u64) -> u64 { atomic_or::<u64, u64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_or_64_seqcst(p: *mut u64, v: u64) -> u64 { atomic_or::<u64, u64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_8_relaxed(p: *mut u8, v: u8) -> u8 { atomic_xor::<u8, u8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_8_acquire(p: *mut u8, v: u8) -> u8 { atomic_xor::<u8, u8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_8_release(p: *mut u8, v: u8) -> u8 { atomic_xor::<u8, u8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_8_acqrel(p: *mut u8, v: u8) -> u8 { atomic_xor::<u8, u8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_8_seqcst(p: *mut u8, v: u8) -> u8 { atomic_xor::<u8, u8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_16_relaxed(p: *mut u16, v: u16) -> u16 { atomic_xor::<u16, u16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_16_acquire(p: *mut u16, v: u16) -> u16 { atomic_xor::<u16, u16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_16_release(p: *mut u16, v: u16) -> u16 { atomic_xor::<u16, u16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_16_acqrel(p: *mut u16, v: u16) -> u16 { atomic_xor::<u16, u16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_16_seqcst(p: *mut u16, v: u16) -> u16 { atomic_xor::<u16, u16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_32_relaxed(p: *mut u32, v: u32) -> u32 { atomic_xor::<u32, u32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_32_acquire(p: *mut u32, v: u32) -> u32 { atomic_xor::<u32, u32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_32_release(p: *mut u32, v: u32) -> u32 { atomic_xor::<u32, u32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_32_acqrel(p: *mut u32, v: u32) -> u32 { atomic_xor::<u32, u32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_32_seqcst(p: *mut u32, v: u32) -> u32 { atomic_xor::<u32, u32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_64_relaxed(p: *mut u64, v: u64) -> u64 { atomic_xor::<u64, u64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_64_acquire(p: *mut u64, v: u64) -> u64 { atomic_xor::<u64, u64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_64_release(p: *mut u64, v: u64) -> u64 { atomic_xor::<u64, u64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_64_acqrel(p: *mut u64, v: u64) -> u64 { atomic_xor::<u64, u64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_xor_64_seqcst(p: *mut u64, v: u64) -> u64 { atomic_xor::<u64, u64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_8_relaxed(p: *mut u8, v: u8) -> u8 { atomic_umax::<u8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_8_acquire(p: *mut u8, v: u8) -> u8 { atomic_umax::<u8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_8_release(p: *mut u8, v: u8) -> u8 { atomic_umax::<u8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_8_acqrel(p: *mut u8, v: u8) -> u8 { atomic_umax::<u8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_8_seqcst(p: *mut u8, v: u8) -> u8 { atomic_umax::<u8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_16_relaxed(p: *mut u16, v: u16) -> u16 { atomic_umax::<u16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_16_acquire(p: *mut u16, v: u16) -> u16 { atomic_umax::<u16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_16_release(p: *mut u16, v: u16) -> u16 { atomic_umax::<u16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_16_acqrel(p: *mut u16, v: u16) -> u16 { atomic_umax::<u16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_16_seqcst(p: *mut u16, v: u16) -> u16 { atomic_umax::<u16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_32_relaxed(p: *mut u32, v: u32) -> u32 { atomic_umax::<u32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_32_acquire(p: *mut u32, v: u32) -> u32 { atomic_umax::<u32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_32_release(p: *mut u32, v: u32) -> u32 { atomic_umax::<u32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_32_acqrel(p: *mut u32, v: u32) -> u32 { atomic_umax::<u32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_32_seqcst(p: *mut u32, v: u32) -> u32 { atomic_umax::<u32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_64_relaxed(p: *mut u64, v: u64) -> u64 { atomic_umax::<u64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_64_acquire(p: *mut u64, v: u64) -> u64 { atomic_umax::<u64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_64_release(p: *mut u64, v: u64) -> u64 { atomic_umax::<u64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_64_acqrel(p: *mut u64, v: u64) -> u64 { atomic_umax::<u64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umax_64_seqcst(p: *mut u64, v: u64) -> u64 { atomic_umax::<u64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_8_relaxed(p: *mut u8, v: u8) -> u8 { atomic_umin::<u8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_8_acquire(p: *mut u8, v: u8) -> u8 { atomic_umin::<u8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_8_release(p: *mut u8, v: u8) -> u8 { atomic_umin::<u8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_8_acqrel(p: *mut u8, v: u8) -> u8 { atomic_umin::<u8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_8_seqcst(p: *mut u8, v: u8) -> u8 { atomic_umin::<u8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_16_relaxed(p: *mut u16, v: u16) -> u16 { atomic_umin::<u16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_16_acquire(p: *mut u16, v: u16) -> u16 { atomic_umin::<u16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_16_release(p: *mut u16, v: u16) -> u16 { atomic_umin::<u16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_16_acqrel(p: *mut u16, v: u16) -> u16 { atomic_umin::<u16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_16_seqcst(p: *mut u16, v: u16) -> u16 { atomic_umin::<u16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_32_relaxed(p: *mut u32, v: u32) -> u32 { atomic_umin::<u32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_32_acquire(p: *mut u32, v: u32) -> u32 { atomic_umin::<u32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_32_release(p: *mut u32, v: u32) -> u32 { atomic_umin::<u32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_32_acqrel(p: *mut u32, v: u32) -> u32 { atomic_umin::<u32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_32_seqcst(p: *mut u32, v: u32) -> u32 { atomic_umin::<u32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_64_relaxed(p: *mut u64, v: u64) -> u64 { atomic_umin::<u64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_64_acquire(p: *mut u64, v: u64) -> u64 { atomic_umin::<u64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_64_release(p: *mut u64, v: u64) -> u64 { atomic_umin::<u64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_64_acqrel(p: *mut u64, v: u64) -> u64 { atomic_umin::<u64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_umin_64_seqcst(p: *mut u64, v: u64) -> u64 { atomic_umin::<u64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_8_relaxed(p: *mut i8, v: i8) -> i8 { atomic_max::<i8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_8_acquire(p: *mut i8, v: i8) -> i8 { atomic_max::<i8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_8_release(p: *mut i8, v: i8) -> i8 { atomic_max::<i8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_8_acqrel(p: *mut i8, v: i8) -> i8 { atomic_max::<i8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_8_seqcst(p: *mut i8, v: i8) -> i8 { atomic_max::<i8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_16_relaxed(p: *mut i16, v: i16) -> i16 { atomic_max::<i16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_16_acquire(p: *mut i16, v: i16) -> i16 { atomic_max::<i16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_16_release(p: *mut i16, v: i16) -> i16 { atomic_max::<i16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_16_acqrel(p: *mut i16, v: i16) -> i16 { atomic_max::<i16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_16_seqcst(p: *mut i16, v: i16) -> i16 { atomic_max::<i16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_32_relaxed(p: *mut i32, v: i32) -> i32 { atomic_max::<i32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_32_acquire(p: *mut i32, v: i32) -> i32 { atomic_max::<i32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_32_release(p: *mut i32, v: i32) -> i32 { atomic_max::<i32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_32_acqrel(p: *mut i32, v: i32) -> i32 { atomic_max::<i32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_32_seqcst(p: *mut i32, v: i32) -> i32 { atomic_max::<i32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_64_relaxed(p: *mut i64, v: i64) -> i64 { atomic_max::<i64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_64_acquire(p: *mut i64, v: i64) -> i64 { atomic_max::<i64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_64_release(p: *mut i64, v: i64) -> i64 { atomic_max::<i64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_64_acqrel(p: *mut i64, v: i64) -> i64 { atomic_max::<i64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_max_64_seqcst(p: *mut i64, v: i64) -> i64 { atomic_max::<i64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_8_relaxed(p: *mut i8, v: i8) -> i8 { atomic_min::<i8, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_8_acquire(p: *mut i8, v: i8) -> i8 { atomic_min::<i8, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_8_release(p: *mut i8, v: i8) -> i8 { atomic_min::<i8, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_8_acqrel(p: *mut i8, v: i8) -> i8 { atomic_min::<i8, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_8_seqcst(p: *mut i8, v: i8) -> i8 { atomic_min::<i8, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_16_relaxed(p: *mut i16, v: i16) -> i16 { atomic_min::<i16, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_16_acquire(p: *mut i16, v: i16) -> i16 { atomic_min::<i16, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_16_release(p: *mut i16, v: i16) -> i16 { atomic_min::<i16, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_16_acqrel(p: *mut i16, v: i16) -> i16 { atomic_min::<i16, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_16_seqcst(p: *mut i16, v: i16) -> i16 { atomic_min::<i16, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_32_relaxed(p: *mut i32, v: i32) -> i32 { atomic_min::<i32, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_32_acquire(p: *mut i32, v: i32) -> i32 { atomic_min::<i32, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_32_release(p: *mut i32, v: i32) -> i32 { atomic_min::<i32, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_32_acqrel(p: *mut i32, v: i32) -> i32 { atomic_min::<i32, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_32_seqcst(p: *mut i32, v: i32) -> i32 { atomic_min::<i32, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_64_relaxed(p: *mut i64, v: i64) -> i64 { atomic_min::<i64, { AtomicOrdering::Relaxed }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_64_acquire(p: *mut i64, v: i64) -> i64 { atomic_min::<i64, { AtomicOrdering::Acquire }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_64_release(p: *mut i64, v: i64) -> i64 { atomic_min::<i64, { AtomicOrdering::Release }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_64_acqrel(p: *mut i64, v: i64) -> i64 { atomic_min::<i64, { AtomicOrdering::AcqRel }>(p, v) }
#[no_mangle] pub unsafe fn atomic_min_64_seqcst(p: *mut i64, v: i64) -> i64 { atomic_min::<i64, { AtomicOrdering::SeqCst }>(p, v) }
#[no_mangle] pub unsafe fn cxchg_8_relaxed_relaxed(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchg::<u8, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_8_acquire_acquire(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchg::<u8, { AtomicOrdering::Acquire }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_8_release_relaxed(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchg::<u8, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_8_acqrel_acquire(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchg::<u8, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_8_seqcst_seqcst(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchg::<u8, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_8_seqcst_relaxed(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchg::<u8, { AtomicOrdering::SeqCst }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_16_relaxed_relaxed(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchg::<u16, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_16_acquire_acquire(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchg::<u16, { AtomicOrdering::Acquire }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_16_release_relaxed(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchg::<u16, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_16_acqrel_acquire(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchg::<u16, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_16_seqcst_seqcst(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchg::<u16, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_16_seqcst_relaxed(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchg::<u16, { AtomicOrdering::SeqCst }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_32_relaxed_relaxed(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchg::<u32, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_32_acquire_acquire(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchg::<u32, { AtomicOrdering::Acquire }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_32_release_relaxed(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchg::<u32, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_32_acqrel_acquire(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchg::<u32, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_32_seqcst_seqcst(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchg::<u32, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_32_seqcst_relaxed(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchg::<u32, { AtomicOrdering::SeqCst }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_64_relaxed_relaxed(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchg::<u64, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_64_acquire_acquire(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchg::<u64, { AtomicOrdering::Acquire }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_64_release_relaxed(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchg::<u64, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_64_acqrel_acquire(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchg::<u64, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_64_seqcst_seqcst(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchg::<u64, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchg_64_seqcst_relaxed(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchg::<u64, { AtomicOrdering::SeqCst }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_8_relaxed_relaxed(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchgweak::<u8, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_8_acquire_acquire(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchgweak::<u8, { AtomicOrdering::Acquire }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_8_release_relaxed(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchgweak::<u8, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_8_acqrel_acquire(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchgweak::<u8, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_8_seqcst_seqcst(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchgweak::<u8, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_8_seqcst_relaxed(p: *mut u8, old: u8, new: u8) -> (u8, bool) { atomic_cxchgweak::<u8, { AtomicOrdering::SeqCst }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_16_relaxed_relaxed(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchgweak::<u16, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_16_acquire_acquire(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchgweak::<u16, { AtomicOrdering::Acquire }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_16_release_relaxed(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchgweak::<u16, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_16_acqrel_acquire(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchgweak::<u16, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_16_seqcst_seqcst(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchgweak::<u16, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_16_seqcst_relaxed(p: *mut u16, old: u16, new: u16) -> (u16, bool) { atomic_cxchgweak::<u16, { AtomicOrdering::SeqCst }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_32_relaxed_relaxed(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchgweak::<u32, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_32_acquire_acquire(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchgweak::<u32, { AtomicOrdering::Acquire }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_32_release_relaxed(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchgweak::<u32, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_32_acqrel_acquire(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchgweak::<u32, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_32_seqcst_seqcst(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchgweak::<u32, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_32_seqcst_relaxed(p: *mut u32, old: u32, new: u32) -> (u32, bool) { atomic_cxchgweak::<u32, { AtomicOrdering::SeqCst }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_64_relaxed_relaxed(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchgweak::<u64, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_64_acquire_acquire(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchgweak::<u64, { AtomicOrdering::Acquire }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_64_release_relaxed(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchgweak::<u64, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_64_acqrel_acquire(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchgweak::<u64, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_64_seqcst_seqcst(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchgweak::<u64, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, old, new) }
#[no_mangle] pub unsafe fn cxchgweak_64_seqcst_relaxed(p: *mut u64, old: u64, new: u64) -> (u64, bool) { atomic_cxchgweak::<u64, { AtomicOrdering::SeqCst }, { AtomicOrdering::Relaxed }>(p, old, new) }
#[cfg(u128_atomics)] pub mod u128_ops {
    use core::intrinsics::*;
    #[no_mangle] pub unsafe fn atomic_load_128_relaxed(p: *const u128) -> u128 { atomic_load::<u128, { AtomicOrdering::Relaxed }>(p) }
    #[no_mangle] pub unsafe fn atomic_load_128_acquire(p: *const u128) -> u128 { atomic_load::<u128, { AtomicOrdering::Acquire }>(p) }
    #[no_mangle] pub unsafe fn atomic_load_128_seqcst(p: *const u128) -> u128 { atomic_load::<u128, { AtomicOrdering::SeqCst }>(p) }
    #[no_mangle] pub unsafe fn atomic_store_128_relaxed(p: *mut u128, v: u128) { atomic_store::<u128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_store_128_release(p: *mut u128, v: u128) { atomic_store::<u128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_store_128_seqcst(p: *mut u128, v: u128) { atomic_store::<u128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xchg_128_relaxed(p: *mut u128, v: u128) -> u128 { atomic_xchg::<u128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xchg_128_acquire(p: *mut u128, v: u128) -> u128 { atomic_xchg::<u128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xchg_128_release(p: *mut u128, v: u128) -> u128 { atomic_xchg::<u128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xchg_128_acqrel(p: *mut u128, v: u128) -> u128 { atomic_xchg::<u128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xchg_128_seqcst(p: *mut u128, v: u128) -> u128 { atomic_xchg::<u128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xadd_128_relaxed(p: *mut u128, v: u128) -> u128 { atomic_xadd::<u128, u128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xadd_128_acquire(p: *mut u128, v: u128) -> u128 { atomic_xadd::<u128, u128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xadd_128_release(p: *mut u128, v: u128) -> u128 { atomic_xadd::<u128, u128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xadd_128_acqrel(p: *mut u128, v: u128) -> u128 { atomic_xadd::<u128, u128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xadd_128_seqcst(p: *mut u128, v: u128) -> u128 { atomic_xadd::<u128, u128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xsub_128_relaxed(p: *mut u128, v: u128) -> u128 { atomic_xsub::<u128, u128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xsub_128_acquire(p: *mut u128, v: u128) -> u128 { atomic_xsub::<u128, u128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xsub_128_release(p: *mut u128, v: u128) -> u128 { atomic_xsub::<u128, u128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xsub_128_acqrel(p: *mut u128, v: u128) -> u128 { atomic_xsub::<u128, u128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xsub_128_seqcst(p: *mut u128, v: u128) -> u128 { atomic_xsub::<u128, u128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_and_128_relaxed(p: *mut u128, v: u128) -> u128 { atomic_and::<u128, u128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_and_128_acquire(p: *mut u128, v: u128) -> u128 { atomic_and::<u128, u128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_and_128_release(p: *mut u128, v: u128) -> u128 { atomic_and::<u128, u128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_and_128_acqrel(p: *mut u128, v: u128) -> u128 { atomic_and::<u128, u128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_and_128_seqcst(p: *mut u128, v: u128) -> u128 { atomic_and::<u128, u128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_nand_128_relaxed(p: *mut u128, v: u128) -> u128 { atomic_nand::<u128, u128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_nand_128_acquire(p: *mut u128, v: u128) -> u128 { atomic_nand::<u128, u128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_nand_128_release(p: *mut u128, v: u128) -> u128 { atomic_nand::<u128, u128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_nand_128_acqrel(p: *mut u128, v: u128) -> u128 { atomic_nand::<u128, u128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_nand_128_seqcst(p: *mut u128, v: u128) -> u128 { atomic_nand::<u128, u128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_or_128_relaxed(p: *mut u128, v: u128) -> u128 { atomic_or::<u128, u128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_or_128_acquire(p: *mut u128, v: u128) -> u128 { atomic_or::<u128, u128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_or_128_release(p: *mut u128, v: u128) -> u128 { atomic_or::<u128, u128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_or_128_acqrel(p: *mut u128, v: u128) -> u128 { atomic_or::<u128, u128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_or_128_seqcst(p: *mut u128, v: u128) -> u128 { atomic_or::<u128, u128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xor_128_relaxed(p: *mut u128, v: u128) -> u128 { atomic_xor::<u128, u128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xor_128_acquire(p: *mut u128, v: u128) -> u128 { atomic_xor::<u128, u128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xor_128_release(p: *mut u128, v: u128) -> u128 { atomic_xor::<u128, u128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xor_128_acqrel(p: *mut u128, v: u128) -> u128 { atomic_xor::<u128, u128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_xor_128_seqcst(p: *mut u128, v: u128) -> u128 { atomic_xor::<u128, u128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_umax_128_relaxed(p: *mut u128, v: u128) -> u128 { atomic_umax::<u128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_umax_128_acquire(p: *mut u128, v: u128) -> u128 { atomic_umax::<u128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_umax_128_release(p: *mut u128, v: u128) -> u128 { atomic_umax::<u128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_umax_128_acqrel(p: *mut u128, v: u128) -> u128 { atomic_umax::<u128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_umax_128_seqcst(p: *mut u128, v: u128) -> u128 { atomic_umax::<u128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_umin_128_relaxed(p: *mut u128, v: u128) -> u128 { atomic_umin::<u128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_umin_128_acquire(p: *mut u128, v: u128) -> u128 { atomic_umin::<u128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_umin_128_release(p: *mut u128, v: u128) -> u128 { atomic_umin::<u128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_umin_128_acqrel(p: *mut u128, v: u128) -> u128 { atomic_umin::<u128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_umin_128_seqcst(p: *mut u128, v: u128) -> u128 { atomic_umin::<u128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_max_128_relaxed(p: *mut i128, v: i128) -> i128 { atomic_max::<i128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_max_128_acquire(p: *mut i128, v: i128) -> i128 { atomic_max::<i128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_max_128_release(p: *mut i128, v: i128) -> i128 { atomic_max::<i128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_max_128_acqrel(p: *mut i128, v: i128) -> i128 { atomic_max::<i128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_max_128_seqcst(p: *mut i128, v: i128) -> i128 { atomic_max::<i128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_min_128_relaxed(p: *mut i128, v: i128) -> i128 { atomic_min::<i128, { AtomicOrdering::Relaxed }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_min_128_acquire(p: *mut i128, v: i128) -> i128 { atomic_min::<i128, { AtomicOrdering::Acquire }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_min_128_release(p: *mut i128, v: i128) -> i128 { atomic_min::<i128, { AtomicOrdering::Release }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_min_128_acqrel(p: *mut i128, v: i128) -> i128 { atomic_min::<i128, { AtomicOrdering::AcqRel }>(p, v) }
    #[no_mangle] pub unsafe fn atomic_min_128_seqcst(p: *mut i128, v: i128) -> i128 { atomic_min::<i128, { AtomicOrdering::SeqCst }>(p, v) }
    #[no_mangle] pub unsafe fn cxchg_128_relaxed_relaxed(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchg::<u128, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchg_128_acquire_acquire(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchg::<u128, { AtomicOrdering::Acquire }, { AtomicOrdering::Acquire }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchg_128_release_relaxed(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchg::<u128, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchg_128_acqrel_acquire(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchg::<u128, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchg_128_seqcst_seqcst(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchg::<u128, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchg_128_seqcst_relaxed(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchg::<u128, { AtomicOrdering::SeqCst }, { AtomicOrdering::Relaxed }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchgweak_128_relaxed_relaxed(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchgweak::<u128, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchgweak_128_acquire_acquire(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchgweak::<u128, { AtomicOrdering::Acquire }, { AtomicOrdering::Acquire }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchgweak_128_release_relaxed(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchgweak::<u128, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchgweak_128_acqrel_acquire(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchgweak::<u128, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchgweak_128_seqcst_seqcst(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchgweak::<u128, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, old, new) }
    #[no_mangle] pub unsafe fn cxchgweak_128_seqcst_relaxed(p: *mut u128, old: u128, new: u128) -> (u128, bool) { atomic_cxchgweak::<u128, { AtomicOrdering::SeqCst }, { AtomicOrdering::Relaxed }>(p, old, new) }
}
#[no_mangle] pub fn atomic_fence_acquire() { fence(Ordering::Acquire); }
#[no_mangle] pub fn atomic_fence_release() { fence(Ordering::Release); }
#[no_mangle] pub fn atomic_fence_acqrel() { fence(Ordering::AcqRel); }
#[no_mangle] pub fn atomic_fence_seqcst() { fence(Ordering::SeqCst); }
#[no_mangle] pub fn atomic_compiler_fence_acquire() { compiler_fence(Ordering::Acquire); }
#[no_mangle] pub fn atomic_compiler_fence_release() { compiler_fence(Ordering::Release); }
#[no_mangle] pub fn atomic_compiler_fence_acqrel() { compiler_fence(Ordering::AcqRel); }
#[no_mangle] pub fn atomic_compiler_fence_seqcst() { compiler_fence(Ordering::SeqCst); }
#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
