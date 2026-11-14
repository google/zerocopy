// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Prototype Version-Isolated `.anneal-mir` v1 Schema (`CoreMIR`) and Multi-Release
//! Desugaring Adapter (`rustc 1.98.1`, `1.99.1`, `1.100.0`, and nightlies).
//!
//! This standalone Rust module demonstrates how frontend MIR and ABI churn across
//! five `rustc` releases is canonicalized into an invariant `CoreMirBody` together
//! with an `AdapterNormCert` witnessing that every Tier A erasure and Tier B
//! syntactic desugaring preserves `Runtime(PostCleanup)` operational semantics.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustcFrontendVersion {
    Nightly20260531,
    V1_98_1,
    V1_99_1,
    V1_100_0,
    Nightly20261112,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendProjectionElem {
    Deref,
    Field(u32, u32),
    Index(u32),
    ConstantIndex { offset: u64, min_length: u64, from_end: bool },
    Subslice { from: u64, to: u64, from_end: bool },
    Downcast(u32),
    OpaqueCast(u32),
    UnwrapUnsafeBinder(u32),
    /// Added in `rustc 1.100.0` (`rust-lang/rust#159103`). Purely static borrowck/lint projection.
    PhantomDeref,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendCastKind {
    PointerExposeProvenance,
    PointerWithExposedProvenance,
    PointerCoercion,
    IntToInt,
    FloatToInt,
    FloatToFloat,
    IntToFloat,
    PtrToPtr,
    FnPtrToPtr,
    Transmute,
    Subtype,
    /// Added in `rustc 1.99.1`. Semantically a pointer/transmute copy of `Box<T>` inner pointer.
    BoxDerefTransmute,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendAssertKind {
    BoundsCheck { len: u32, index: u32 },
    Overflow,
    OverflowNeg,
    DivisionByZero,
    RemainderByZero,
    ResumedAfterReturn,
    ResumedAfterPanic,
    MisalignedPointerDereference { required: u64, found: u32 },
    /// Added in `rustc 1.99.1` for `-Zub-checks` null-reference checks.
    NullReferenceConstructed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendInlineAsmConst {
    /// Pre-1.99.1 (`1.98.1`, `nightly-2026-05-31`): pre-rendered string constant.
    LegacyString(String),
    /// `1.99.1+`: typed scalar constant (`value: Scalar, ty: Ty<'tcx>`).
    TypedScalar { bits: u128, size_bytes: u8 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendStmt {
    Assign { dst_local: u32, proj: Vec<FrontendProjectionElem>, rvalue: FrontendRvalue },
    SetDiscriminant { dst_local: u32, variant_idx: u32 },
    StorageLive(u32),
    StorageDead(u32),
    /// Tier A purely static/lint statements across `1.98.1..1.100.0`.
    FakeRead,
    AscribeUserType,
    Coverage,
    ConstEvalCounter,
    PlaceMention,
    BackwardIncompatibleDropHint,
    Nop,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendRvalue {
    UseLocal(u32),
    Cast { kind: FrontendCastKind, src_local: u32, src_size: u32, dst_size: u32 },
    BinaryOp { op: u8, lhs: u32, rhs: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendTerminator {
    Return,
    Goto(u32),
    Assert { cond_local: u32, expected: bool, target_bb: u32, kind: FrontendAssertKind },
    InlineAsm { template: String, const_operands: Vec<FrontendInlineAsmConst>, target_bb: u32 },
}

// ============================================================================
// Version-Isolated `.anneal-mir` v1 Core Schema (`CoreMIR`)
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreProjectionElem {
    Deref,
    Field(u32, u32),
    Index(u32),
    ConstantIndex { offset: u64, min_length: u64, from_end: bool },
    Subslice { from: u64, to: u64, from_end: bool },
    Downcast(u32),
    OpaqueCast(u32),
    UnwrapUnsafeBinder(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreCastKind {
    PointerExposeProvenance,
    PointerWithExposedProvenance,
    PointerCoercion,
    IntToInt,
    FloatToInt,
    FloatToFloat,
    IntToFloat,
    PtrToPtr,
    FnPtrToPtr,
    Transmute,
    Subtype,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CorePanicTrapSymbol {
    BoundsCheck { len: u32, index: u32 },
    ArithmeticOverflow,
    DivisionByZero,
    RemainderByZero,
    CoroutineMisuse,
    MisalignedPointer { required: u64, found: u32 },
    NullReferenceTrap,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreAsmConst {
    pub canonical_decimal: String,
    pub bits: Option<(u128, u8)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreStmt {
    Assign { dst_local: u32, proj: Vec<CoreProjectionElem>, rvalue: CoreRvalue },
    SetDiscriminant { dst_local: u32, variant_idx: u32 },
    StorageLive(u32),
    StorageDead(u32),
    Nop,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreRvalue {
    UseLocal(u32),
    Cast { kind: CoreCastKind, src_local: u32, src_size: u32, dst_size: u32 },
    BinaryOp { op: u8, lhs: u32, rhs: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreTerminator {
    Return,
    Goto(u32),
    Assert { cond_local: u32, expected: bool, target_bb: u32, trap: CorePanicTrapSymbol },
    InlineAsm { template: String, const_operands: Vec<CoreAsmConst>, target_bb: u32 },
}

/// Certificate step emitted by the adapter for audit/proof bridge (`Layer 1`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdapterRewriteStep {
    StripPhantomDeref { stmt_idx: usize },
    EraseTierAMarker { stmt_idx: usize, marker_name: &'static str },
    DesugarBoxDerefTransmute { stmt_idx: usize, byte_size: u32 },
    DesugarNullReferenceAssert { bb_idx: usize },
    CanonicalizeInlineAsmConst { bb_idx: usize, op_idx: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdaptedFunctionArtifact {
    pub schema_version: u32,
    pub source_version: RustcFrontendVersion,
    pub stmts: Vec<CoreStmt>,
    pub terminator: CoreTerminator,
    pub cert_steps: Vec<AdapterRewriteStep>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdapterError {
    SizeMismatchInBoxDerefTransmute { src_size: u32, dst_size: u32 },
}

pub fn adapt_function_to_core_mir(
    version: RustcFrontendVersion,
    stmts: &[FrontendStmt],
    term: &FrontendTerminator,
) -> Result<AdaptedFunctionArtifact, AdapterError> {
    let mut core_stmts = Vec::with_capacity(stmts.len());
    let mut cert_steps = Vec::new();

    for (idx, stmt) in stmts.iter().enumerate() {
        match stmt {
            FrontendStmt::Assign { dst_local, proj, rvalue } => {
                let mut core_proj = Vec::with_capacity(proj.len());
                for p in proj {
                    match p {
                        FrontendProjectionElem::Deref => core_proj.push(CoreProjectionElem::Deref),
                        FrontendProjectionElem::Field(f, t) => {
                            core_proj.push(CoreProjectionElem::Field(*f, *t))
                        }
                        FrontendProjectionElem::Index(l) => {
                            core_proj.push(CoreProjectionElem::Index(*l))
                        }
                        FrontendProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                            core_proj.push(CoreProjectionElem::ConstantIndex {
                                offset: *offset,
                                min_length: *min_length,
                                from_end: *from_end,
                            })
                        }
                        FrontendProjectionElem::Subslice { from, to, from_end } => {
                            core_proj.push(CoreProjectionElem::Subslice {
                                from: *from,
                                to: *to,
                                from_end: *from_end,
                            })
                        }
                        FrontendProjectionElem::Downcast(v) => {
                            core_proj.push(CoreProjectionElem::Downcast(*v))
                        }
                        FrontendProjectionElem::OpaqueCast(t) => {
                            core_proj.push(CoreProjectionElem::OpaqueCast(*t))
                        }
                        FrontendProjectionElem::UnwrapUnsafeBinder(t) => {
                            core_proj.push(CoreProjectionElem::UnwrapUnsafeBinder(*t))
                        }
                        FrontendProjectionElem::PhantomDeref => {
                            cert_steps.push(AdapterRewriteStep::StripPhantomDeref { stmt_idx: idx });
                        }
                    }
                }
                let core_rv = match rvalue {
                    FrontendRvalue::UseLocal(l) => CoreRvalue::UseLocal(*l),
                    FrontendRvalue::BinaryOp { op, lhs, rhs } => {
                        CoreRvalue::BinaryOp { op: *op, lhs: *lhs, rhs: *rhs }
                    }
                    FrontendRvalue::Cast { kind, src_local, src_size, dst_size } => {
                        let core_kind = match kind {
                            FrontendCastKind::PointerExposeProvenance => {
                                CoreCastKind::PointerExposeProvenance
                            }
                            FrontendCastKind::PointerWithExposedProvenance => {
                                CoreCastKind::PointerWithExposedProvenance
                            }
                            FrontendCastKind::PointerCoercion => CoreCastKind::PointerCoercion,
                            FrontendCastKind::IntToInt => CoreCastKind::IntToInt,
                            FrontendCastKind::FloatToInt => CoreCastKind::FloatToInt,
                            FrontendCastKind::FloatToFloat => CoreCastKind::FloatToFloat,
                            FrontendCastKind::IntToFloat => CoreCastKind::IntToFloat,
                            FrontendCastKind::PtrToPtr => CoreCastKind::PtrToPtr,
                            FrontendCastKind::FnPtrToPtr => CoreCastKind::FnPtrToPtr,
                            FrontendCastKind::Transmute => CoreCastKind::Transmute,
                            FrontendCastKind::Subtype => CoreCastKind::Subtype,
                            FrontendCastKind::BoxDerefTransmute => {
                                if src_size != dst_size {
                                    return Err(AdapterError::SizeMismatchInBoxDerefTransmute {
                                        src_size: *src_size,
                                        dst_size: *dst_size,
                                    });
                                }
                                cert_steps.push(AdapterRewriteStep::DesugarBoxDerefTransmute {
                                    stmt_idx: idx,
                                    byte_size: *src_size,
                                });
                                CoreCastKind::Transmute
                            }
                        };
                        CoreRvalue::Cast {
                            kind: core_kind,
                            src_local: *src_local,
                            src_size: *src_size,
                            dst_size: *dst_size,
                        }
                    }
                };
                core_stmts.push(CoreStmt::Assign {
                    dst_local: *dst_local,
                    proj: core_proj,
                    rvalue: core_rv,
                });
            }
            FrontendStmt::SetDiscriminant { dst_local, variant_idx } => {
                core_stmts.push(CoreStmt::SetDiscriminant {
                    dst_local: *dst_local,
                    variant_idx: *variant_idx,
                });
            }
            FrontendStmt::StorageLive(l) => core_stmts.push(CoreStmt::StorageLive(*l)),
            FrontendStmt::StorageDead(l) => core_stmts.push(CoreStmt::StorageDead(*l)),
            FrontendStmt::FakeRead => {
                cert_steps.push(AdapterRewriteStep::EraseTierAMarker {
                    stmt_idx: idx,
                    marker_name: "FakeRead",
                });
                core_stmts.push(CoreStmt::Nop);
            }
            FrontendStmt::AscribeUserType => {
                cert_steps.push(AdapterRewriteStep::EraseTierAMarker {
                    stmt_idx: idx,
                    marker_name: "AscribeUserType",
                });
                core_stmts.push(CoreStmt::Nop);
            }
            FrontendStmt::Coverage => {
                cert_steps.push(AdapterRewriteStep::EraseTierAMarker {
                    stmt_idx: idx,
                    marker_name: "Coverage",
                });
                core_stmts.push(CoreStmt::Nop);
            }
            FrontendStmt::ConstEvalCounter => {
                cert_steps.push(AdapterRewriteStep::EraseTierAMarker {
                    stmt_idx: idx,
                    marker_name: "ConstEvalCounter",
                });
                core_stmts.push(CoreStmt::Nop);
            }
            FrontendStmt::PlaceMention => {
                cert_steps.push(AdapterRewriteStep::EraseTierAMarker {
                    stmt_idx: idx,
                    marker_name: "PlaceMention",
                });
                core_stmts.push(CoreStmt::Nop);
            }
            FrontendStmt::BackwardIncompatibleDropHint => {
                cert_steps.push(AdapterRewriteStep::EraseTierAMarker {
                    stmt_idx: idx,
                    marker_name: "BackwardIncompatibleDropHint",
                });
                core_stmts.push(CoreStmt::Nop);
            }
            FrontendStmt::Nop => core_stmts.push(CoreStmt::Nop),
        }
    }

    let core_term = match term {
        FrontendTerminator::Return => CoreTerminator::Return,
        FrontendTerminator::Goto(bb) => CoreTerminator::Goto(*bb),
        FrontendTerminator::Assert { cond_local, expected, target_bb, kind } => {
            let trap = match kind {
                FrontendAssertKind::BoundsCheck { len, index } => {
                    CorePanicTrapSymbol::BoundsCheck { len: *len, index: *index }
                }
                FrontendAssertKind::Overflow | FrontendAssertKind::OverflowNeg => {
                    CorePanicTrapSymbol::ArithmeticOverflow
                }
                FrontendAssertKind::DivisionByZero => CorePanicTrapSymbol::DivisionByZero,
                FrontendAssertKind::RemainderByZero => CorePanicTrapSymbol::RemainderByZero,
                FrontendAssertKind::ResumedAfterReturn | FrontendAssertKind::ResumedAfterPanic => {
                    CorePanicTrapSymbol::CoroutineMisuse
                }
                FrontendAssertKind::MisalignedPointerDereference { required, found } => {
                    CorePanicTrapSymbol::MisalignedPointer { required: *required, found: *found }
                }
                FrontendAssertKind::NullReferenceConstructed => {
                    cert_steps.push(AdapterRewriteStep::DesugarNullReferenceAssert { bb_idx: 0 });
                    CorePanicTrapSymbol::NullReferenceTrap
                }
            };
            CoreTerminator::Assert {
                cond_local: *cond_local,
                expected: *expected,
                target_bb: *target_bb,
                trap,
            }
        }
        FrontendTerminator::InlineAsm { template, const_operands, target_bb } => {
            let mut ops = Vec::with_capacity(const_operands.len());
            for (op_idx, op) in const_operands.iter().enumerate() {
                match op {
                    FrontendInlineAsmConst::LegacyString(s) => {
                        ops.push(CoreAsmConst { canonical_decimal: s.clone(), bits: None });
                    }
                    FrontendInlineAsmConst::TypedScalar { bits, size_bytes } => {
                        cert_steps.push(AdapterRewriteStep::CanonicalizeInlineAsmConst {
                            bb_idx: 0,
                            op_idx,
                        });
                        ops.push(CoreAsmConst {
                            canonical_decimal: bits.to_string(),
                            bits: Some((*bits, *size_bytes)),
                        });
                    }
                }
            }
            CoreTerminator::InlineAsm {
                template: template.clone(),
                const_operands: ops,
                target_bb: *target_bb,
            }
        }
    };

    Ok(AdaptedFunctionArtifact {
        schema_version: 1,
        source_version: version,
        stmts: core_stmts,
        terminator: core_term,
        cert_steps,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cross_version_canonicalization_1981_1991_1100() {
        let stmts_1100 = vec![
            FrontendStmt::BackwardIncompatibleDropHint,
            FrontendStmt::Assign {
                dst_local: 1,
                proj: vec![FrontendProjectionElem::PhantomDeref, FrontendProjectionElem::Deref],
                rvalue: FrontendRvalue::Cast {
                    kind: FrontendCastKind::BoxDerefTransmute,
                    src_local: 2,
                    src_size: 8,
                    dst_size: 8,
                },
            },
        ];
        let term_1100 = FrontendTerminator::Assert {
            cond_local: 3,
            expected: true,
            target_bb: 1,
            kind: FrontendAssertKind::NullReferenceConstructed,
        };
        let adapted =
            adapt_function_to_core_mir(RustcFrontendVersion::V1_100_0, &stmts_1100, &term_1100)
                .expect("valid adaptation");
        assert_eq!(adapted.schema_version, 1);
        assert_eq!(adapted.cert_steps.len(), 4);
        assert_eq!(
            adapted.stmts[1],
            CoreStmt::Assign {
                dst_local: 1,
                proj: vec![CoreProjectionElem::Deref],
                rvalue: CoreRvalue::Cast {
                    kind: CoreCastKind::Transmute,
                    src_local: 2,
                    src_size: 8,
                    dst_size: 8,
                },
            }
        );
    }
}
