// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Declarative Lean Pass 2 correspondence harness and request builders.
//!
//! Replaces repeated inline synthetic Miri stub modules, 37-claim/proof blocks,
//! and verbose [`InspectorRequest::CorrespondenceAudit`] literals across
//! `anneal-audit-tests`.

#![allow(dead_code)]

use std::{collections::BTreeMap, path::PathBuf};

use anneal_audit::{CandidateFeature, Checker, Failure, InspectorRequest, Json, TrustTier};

use super::{TempFixture, compile_forged_module};

/// Minimal synthetic `Miri.FakeStubs` module covering all 39 required live
/// `ExecutionMachine` Miri primitives plus `AllowedStep`, `MachineHooks`,
/// `FnArg`, `Call`, and `Allocation` scalar stubs.
pub const MIRI_FAKE_STUBS_SRC: &str = "\
prelude
import Init.Core
namespace Miri.Interpreter.ExecutionMachine
def step : Nat := 0
def AllowedStep : Nat := 0
def withValidation : Nat := 0
def stepHooks : Nat := 0
def rvalueHooks : Nat := 0
def operandHooks : Nat := 0
def projectionHooks : Nat := 0
def discriminantHooks : Nat := 0
def scalarHooks : Nat := 0
end Miri.Interpreter.ExecutionMachine
namespace Miri.Interpreter.Step
def step : Nat := 0
def evalStatement : Nat := 0
end Miri.Interpreter.Step
namespace Miri.Interpreter.ControlFlow
def goToBlock : Nat := 0
def evalTerminator : Nat := 0
def returnFromCurrentFrame : Nat := 0
end Miri.Interpreter.ControlFlow
namespace Miri.Interpreter.ExecutionControl
def hooks : Nat := 0
end Miri.Interpreter.ExecutionControl
namespace Miri.Interpreter.MachineHooks
def storageLiveDyn : Nat := 0
def storageDead : Nat := 0
def takeLastPendingMoveDeinit : Nat := 0
def recordPendingMoveDeinit : Nat := 0
end Miri.Interpreter.MachineHooks
namespace Miri.Interpreter.OperandMachine
def evalOperand : Nat := 0
def evalPlaceToOp : Nat := 0
end Miri.Interpreter.OperandMachine
namespace Miri.Interpreter.PlaceMachine
def readImmediate : Nat := 0
def writeMemory : Nat := 0
end Miri.Interpreter.PlaceMachine
namespace Miri.Interpreter.ValidityVisitor
def validatePlace : Nat := 0
end Miri.Interpreter.ValidityVisitor
namespace Miri.Interpreter.ValidityMemory
def bind : Nat := 0
end Miri.Interpreter.ValidityMemory
namespace Miri.Interpreter.FnArg
def copyFnArg : Nat := 0
end Miri.Interpreter.FnArg
namespace Miri.Interpreter.Call
def deinitInPlaceArg : Nat := 0
end Miri.Interpreter.Call
namespace Miri.Interpreter.ScalarOps
def binary : Nat := 0
def unary : Nat := 0
end Miri.Interpreter.ScalarOps
namespace Miri.Interpreter.IntegerOps
def binary : Nat := 0
def binaryBool : Nat := 0
def unary : Nat := 0
def binaryChar : Nat := 0
end Miri.Interpreter.IntegerOps
namespace Miri.Interpreter.Cast
def cast : Nat := 0
end Miri.Interpreter.Cast
namespace Miri.Interpreter.IntegerCast
def cast : Nat := 0
end Miri.Interpreter.IntegerCast
namespace Miri.Memory.ScalarInt
def truncateFromUInt : Nat := 0
def tryFromUInt : Nat := 0
def tryToBool : Nat := 0
def toChar : Nat := 0
def ofChar : Nat := 0
end Miri.Memory.ScalarInt
namespace Miri.Interpreter
def evalOperand : Nat := 0
def evalRvalueIntoPlace : Nat := 0
end Miri.Interpreter
namespace Miri.Interpreter.TerminatorMachine
def beforeTerminatorWithChoice : Nat := 0
end Miri.Interpreter.TerminatorMachine
namespace Miri.Interpreter.Discriminant
def readDiscriminant : Nat := 0
def discriminantForVariant : Nat := 0
end Miri.Interpreter.Discriminant
namespace Miri.Memory.Allocation
def writeScalar : Nat := 0
def getBytesUnchecked : Nat := 0
def readScalar : Nat := 0
def writeUninit : Nat := 0
end Miri.Memory.Allocation
";

pub const TRUSTED_MIR_SEMANTICS_SRC: &str = "\
prelude
import Init.Core
namespace Trusted.MirSemantics
def WellFormed : Prop := True
def Behavior : Prop := True
def Diverges : Prop := True
def ReachesResult : Prop := True
def ValidPrefixAtChoices : Prop := True
def BehaviorAtChoices : Prop := True
def DivergesAtChoices : Prop := True
def ReachesResultAtChoices : Prop := True
def initState : Nat := 0
def Step : Prop := True
def Reaches : Prop := True
def progAddUncheckedU32 : Nat := 0
def progAddU32 : Nat := 0
def progEnumExplicitReprU8 : Nat := 0
def progEnumSignedTagIsize : Nat := 0
def progZstSingleEnumImplicitRet : Nat := 0
def progZstSingleEnumMoveAndDiscr : Nat := 0
def progEnumInvalidTagConstUb : Nat := 0
def progEnumUninitDiscrUb : Nat := 0
def evalShiftOp : Nat := 0
def evalArithOp : Nat := 0
def jumpToBlock : Nat := 0
def enumAdmitted : Nat := 0
def tagBitsToDiscrBits : Nat := 0
def isZstEnumTy : Nat := 0
def findDiscrVariant? : Nat := 0
def evalStep : Nat := 0
def encodeVal : Nat := 0
def decodeVal : Nat := 0
def profileTargetEndian : Nat := 0
def mkBinOpProg : Nat := 0
def mkCmpDiscriminantProg : Nat := 0
def progCharSwitch : Nat := 0
def mkIntToIntCastProg : Nat := 0
def overflowPairTy : Nat := 0
def unlistedAnnealHelper : Nat := 0
end Trusted.MirSemantics
";

pub const TRUSTED_MIR_SEMANTICS_SUB_HELPER_SRC: &str = "\
prelude
import Init.Core
namespace Trusted.MirSemantics
def subEvalHelper : Nat := 0
end Trusted.MirSemantics
";

pub const TRUSTED_MIR_MODEL_SRC: &str = "\
prelude
import Init.Core
namespace Trusted.MirSemantics
def sharedModelData : Nat := 0
end Trusted.MirSemantics
namespace Trusted.MirAst
def BinOp.cmp : Nat := 0
def BinOp.addWithOverflow : Nat := 0
def BinOp.subWithOverflow : Nat := 0
def MirTy.char : Nat := 0
end Trusted.MirAst
";

pub const TRUSTED_MIR_HELPER_SRC: &str = "\
prelude
import Init.Core
namespace Trusted.MirHelper
def siblingHelper : Nat := 0
end Trusted.MirHelper
";

/// All 39 required live `ExecutionMachine` Miri primitives checked on
/// `[evalRefStep, initRefState]`.
pub const REQUIRED_MIRI_PRIMITIVES: [&str; 39] = [
    "Miri.Interpreter.ExecutionMachine.step",
    "Miri.Interpreter.ExecutionMachine.withValidation",
    "Miri.Interpreter.ExecutionMachine.stepHooks",
    "Miri.Interpreter.ExecutionMachine.rvalueHooks",
    "Miri.Interpreter.ExecutionMachine.operandHooks",
    "Miri.Interpreter.ExecutionMachine.projectionHooks",
    "Miri.Interpreter.ExecutionMachine.discriminantHooks",
    "Miri.Interpreter.ExecutionMachine.scalarHooks",
    "Miri.Interpreter.Step.step",
    "Miri.Interpreter.Step.evalStatement",
    "Miri.Interpreter.ControlFlow.goToBlock",
    "Miri.Interpreter.ControlFlow.evalTerminator",
    "Miri.Interpreter.ControlFlow.returnFromCurrentFrame",
    "Miri.Interpreter.ExecutionControl.hooks",
    "Miri.Interpreter.MachineHooks.storageLiveDyn",
    "Miri.Interpreter.MachineHooks.storageDead",
    "Miri.Interpreter.OperandMachine.evalOperand",
    "Miri.Interpreter.OperandMachine.evalPlaceToOp",
    "Miri.Interpreter.PlaceMachine.readImmediate",
    "Miri.Interpreter.PlaceMachine.writeMemory",
    "Miri.Interpreter.ValidityVisitor.validatePlace",
    "Miri.Interpreter.ValidityMemory.bind",
    "Miri.Interpreter.evalRvalueIntoPlace",
    "Miri.Interpreter.TerminatorMachine.beforeTerminatorWithChoice",
    "Miri.Interpreter.ScalarOps.binary",
    "Miri.Interpreter.ScalarOps.unary",
    "Miri.Interpreter.IntegerOps.binary",
    "Miri.Interpreter.IntegerOps.binaryBool",
    "Miri.Interpreter.IntegerOps.unary",
    "Miri.Interpreter.IntegerOps.binaryChar",
    "Miri.Interpreter.Cast.cast",
    "Miri.Interpreter.IntegerCast.cast",
    "Miri.Interpreter.Discriminant.readDiscriminant",
    "Miri.Interpreter.Discriminant.discriminantForVariant",
    "Miri.Memory.ScalarInt.truncateFromUInt",
    "Miri.Memory.ScalarInt.tryFromUInt",
    "Miri.Memory.ScalarInt.tryToBool",
    "Miri.Memory.ScalarInt.toChar",
    "Miri.Memory.ScalarInt.ofChar",
];

pub const CORR_DEPS: [&str; 5] = [
    "Miri.FakeStubs",
    "Trusted.MirModel",
    "Trusted.MirHelper",
    "Trusted.MirSemantics",
    "Trusted.MirSemantics.SubHelper",
];

/// Assert that `outcome` failed with policy exit code `1`, `expected_phase`,
/// and a message containing `expected_substr`.
pub fn assert_policy_rejection(
    outcome: Result<Json, Failure>,
    expected_phase: &str,
    expected_substr: &str,
) {
    let err = outcome.unwrap_err();
    assert_eq!(err.code, 1, "expected policy code 1, got {err}");
    assert_eq!(err.phase, expected_phase, "unexpected phase for {err}");
    assert!(
        err.message.contains(expected_substr),
        "expected substring {expected_substr:?}, got: {err}"
    );
}

/// Canonical `BytesCodecMatchesMiriClaim` body for substring replacement tests.
pub const VALID_BYTES_CODEC_DEF: &str = "def BytesCodecMatchesMiriClaim : Prop :=\n\
               Trusted.MirSemantics.encodeVal = Trusted.MirSemantics.decodeVal ∧\n\
               Trusted.MirSemantics.profileTargetEndian = Miri.Memory.Allocation.writeScalar ∧\n\
               Miri.Memory.Allocation.getBytesUnchecked = Miri.Memory.Allocation.readScalar ∧\n\
               Miri.Memory.Allocation.writeUninit = Miri.Memory.Allocation.writeUninit\n";

/// Canonical `CanaryD11EnumDiscriminantAndConstOkClaim` body.
pub const VALID_D11_DEF: &str = "def CanaryD11EnumDiscriminantAndConstOkClaim : Prop :=\n\
               Trusted.MirSemantics.progEnumExplicitReprU8 = Trusted.MirSemantics.progEnumSignedTagIsize ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n";

/// Canonical `CanaryD12ZstEnumMoveAndDiscrOkClaim` body.
pub const VALID_D12_DEF: &str = "def CanaryD12ZstEnumMoveAndDiscrOkClaim : Prop :=\n\
               Trusted.MirSemantics.progZstSingleEnumImplicitRet = Trusted.MirSemantics.progZstSingleEnumMoveAndDiscr ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n";

/// Canonical `CanaryD13EnumInvalidTagAndUninitUbClaim` body.
pub const VALID_D13_DEF: &str = "def CanaryD13EnumInvalidTagAndUninitUbClaim : Prop :=\n\
               Trusted.MirSemantics.progEnumInvalidTagConstUb = Trusted.MirSemantics.progEnumUninitDiscrUb ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.ReachesResult ∧\n\
               Trusted.MirSemantics.WellFormed ∧ RefReachesOutcome\n";

/// Declarative spec for `Trusted.Correspondence`.
#[derive(Clone, Debug)]
pub struct ClaimsSpec {
    pub init_ref_state: String,
    pub eval_ref_step: String,
    pub ref_allowed_step: String,
    pub corr_choices: Option<String>,
    pub fault_choices: Option<String>,
    pub wiring: Option<String>,
    pub d6: Option<String>,
    pub ref_step_allowed: Option<String>,
    pub replacements: Vec<(String, String)>,
}

impl ClaimsSpec {
    pub fn valid() -> Self {
        Self {
            init_ref_state: "0".to_string(),
            eval_ref_step: "0".to_string(),
            ref_allowed_step: "Miri.Interpreter.ExecutionMachine.AllowedStep".to_string(),
            corr_choices: None,
            fault_choices: None,
            wiring: None,
            d6: None,
            ref_step_allowed: None,
            replacements: Vec::new(),
        }
    }

    pub fn with_init_ref_state(mut self, body: impl Into<String>) -> Self {
        self.init_ref_state = body.into();
        self
    }

    pub fn with_eval_ref_step(mut self, body: impl Into<String>) -> Self {
        self.eval_ref_step = body.into();
        self
    }

    pub fn with_ref_allowed_step(mut self, body: impl Into<String>) -> Self {
        self.ref_allowed_step = body.into();
        self
    }

    pub fn with_replace(mut self, from: impl Into<String>, to: impl Into<String>) -> Self {
        self.replacements.push((from.into(), to.into()));
        self
    }

    pub fn render(&self) -> String {
        let corr_choices_def = self.corr_choices.as_deref().unwrap_or(
            "Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧\n\
             RefValidPrefixAtChoices ∧ Trusted.MirSemantics.ValidPrefixAtChoices ∧\n\
             RefBehaviorAtChoices ∧ Trusted.MirSemantics.BehaviorAtChoices ∧\n\
             RefDivergesAtChoices ∧ Trusted.MirSemantics.DivergesAtChoices ∧\n\
             encodeProg = encodeProg",
        );
        let fault_choices_def = self.fault_choices.as_deref().unwrap_or(
            "Trusted.MirSemantics.ReachesResultAtChoices ∧ RefReachesOutcomeAtChoices ∧\n\
             faultToRefOutcome = encodeProg",
        );
        let wiring_def = self.wiring.as_deref().unwrap_or(
            "Miri.Interpreter.ExecutionMachine.step = Miri.Interpreter.ExecutionMachine.stepHooks ∧\n\
             Miri.Interpreter.Step.step = Miri.Interpreter.ExecutionMachine.withValidation ∧\n\
             Miri.Interpreter.ExecutionMachine.operandHooks = Miri.Interpreter.OperandMachine.evalOperand ∧\n\
             Miri.Interpreter.OperandMachine.evalPlaceToOp = Miri.Interpreter.evalOperand ∧\n\
             Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit = Miri.Interpreter.MachineHooks.recordPendingMoveDeinit ∧\n\
             Miri.Interpreter.FnArg.copyFnArg = Miri.Interpreter.Call.deinitInPlaceArg",
        );
        let d6_def = self.d6.as_deref().unwrap_or(
            "progUseAfterMoveD6 = encodeProg ∧ Trusted.MirSemantics.ReachesResult ∧\n\
             Trusted.MirSemantics.WellFormed ∧ RefReachesOutcome",
        );
        let ref_step_allowed_def = self
            .ref_step_allowed
            .as_deref()
            .unwrap_or("RefStep ∧ RefAllowedStep = refReadReturnVal");
        let mut out = format!(
            "prelude\nimport Init.Core\nimport Miri.FakeStubs\nimport Trusted.MirModel\n\
             import Trusted.MirHelper\nimport Trusted.MirSemantics\nimport Trusted.MirSemantics.SubHelper\n\
             namespace Trusted.Correspondence\n\
             def RefWellFormed : Prop := True\n\
             def RefBehavior : Prop := True\n\
             def RefDiverges : Prop := True\n\
             def RefValidPrefixAtChoices : Prop := True\n\
             def RefBehaviorAtChoices : Prop := True\n\
             def RefDivergesAtChoices : Prop := True\n\
             def RefReachesOutcomeAtChoices : Prop := True\n\
             def decodeProg : Nat := 0\n\
             def encodeProg : Nat := 0\n\
             def typesAreCanonical : Nat := 0\n\
             def encodeStmt : Nat := 0\n\
             def encodeRvalue : Nat := 0\n\
             def encodeOperand : Nat := 0\n\
             def encodePlace : Nat := 0\n\
             def SimulationInv : Prop := True\n\
             def stepResultToRefOutcome : Nat := 0\n\
             def mapStepRes : Nat := 0\n\
             def RefStep : Prop := True\n\
             def RefReaches : Prop := True\n\
             def RefReachesOutcome : Prop := True\n\
             def faultToRefOutcome : Nat := 0\n\
             def refReadReturnVal : Nat := 0\n\
             def progUseAfterMoveD6 : Nat := 0\n\
             def progBinOpCopyThenMoveD7a : Nat := 0\n\
             def progBinOpMoveThenCopyD7b : Nat := 0\n\
             def progBinOpMoveThenMoveD7c : Nat := 0\n\
             def progSelfMoveD8 : Nat := 0\n\
             def progMoveUnitZstD9 : Nat := 0\n\
             def transitiveSubHelper : Nat := Trusted.MirSemantics.subEvalHelper\n\
             def initRefState : Nat := {init_ref_state}\n\
             def evalRefStep : Nat := {eval_ref_step}\n\
             def RefAllowedStep : Nat := {ref_allowed_step}\n\
             def CorrespondenceClaim : Prop :=\n\
               Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefBehavior ∧\n\
               Trusted.MirSemantics.Diverges ∧ RefDiverges ∧ encodeProg = encodeProg\n\
             def FaultEquivalenceClaim : Prop :=\n\
               Trusted.MirSemantics.ReachesResult ∧ RefReachesOutcome ∧\n\
               faultToRefOutcome = encodeProg\n\
             def CorrespondenceAtChoicesClaim : Prop := {corr_choices_def}\n\
             def FaultEquivalenceAtChoicesClaim : Prop := {fault_choices_def}\n\
             def MiriMoveDeinitWiringClaim : Prop := {wiring_def}\n\
             def DecodeProgEncodeProgClaim : Prop := decodeProg = encodeProg\n\
             def EncodeProgTypesCanonicalClaim : Prop := typesAreCanonical = encodeProg\n\
             def EncodeStmtNoDormantNoopsClaim : Prop := encodeStmt = encodeStmt\n\
             def EncodeRvalueBinaryOpIffClaim : Prop := encodeRvalue = encodeOperand\n\
             def EncodeRvalueUnaryOpIffClaim : Prop := encodeRvalue = encodeOperand\n\
             def EncodeStmtAssignIffClaim : Prop :=\n\
               encodeStmt = encodePlace ∧ encodePlace = encodeRvalue\n\
             def StateUniqueOfSimulationInvClaim : Prop := SimulationInv\n\
             def RefStateUniqueOfSimulationInvClaim : Prop := SimulationInv\n\
             def InitRefStateSimClaim : Prop :=\n\
               decodeProg = Trusted.MirSemantics.initState ∧\n\
               initRefState = decodeProg ∧ SimulationInv\n\
             def EvalRefStepEqClaim : Prop :=\n\
               decodeProg = stepResultToRefOutcome ∧ mapStepRes = Trusted.MirSemantics.evalStep ∧\n\
               evalRefStep = evalRefStep\n\
             def SimOfRefStepClaim : Prop :=\n\
               decodeProg = decodeProg ∧ SimulationInv ∧ RefStep ∧ Trusted.MirSemantics.Step\n\
             def SimOfRefReachesClaim : Prop :=\n\
               decodeProg = decodeProg ∧ SimulationInv ∧ RefReaches ∧ Trusted.MirSemantics.Reaches\n\
             def RefWellFormedOfWellFormedClaim : Prop :=\n\
               Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧ encodeProg = encodeProg\n\
             def RefBehaviorOfBehaviorClaim : Prop :=\n\
               Trusted.MirSemantics.Behavior ∧ RefBehavior ∧ encodeProg = encodeProg\n\
             def BehaviorOfRefBehaviorClaim : Prop :=\n\
               RefBehavior ∧ Trusted.MirSemantics.Behavior ∧ encodeProg = encodeProg\n\
             def BehaviorIffRefBehaviorClaim : Prop :=\n\
               Trusted.MirSemantics.Behavior ∧ RefBehavior ∧ encodeProg = encodeProg\n\
             def DivergesIffRefDivergesClaim : Prop :=\n\
               Trusted.MirSemantics.Diverges ∧ RefDiverges ∧ encodeProg = encodeProg\n\
             def CanaryD6UseAfterMoveUbClaim : Prop := {d6_def}\n\
             def CanaryD7aBinopCopyThenMoveOkClaim : Prop :=\n\
               progBinOpCopyThenMoveD7a = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def CanaryD7bBinopMoveThenCopyUbClaim : Prop :=\n\
               progBinOpMoveThenCopyD7b = encodeProg ∧ Trusted.MirSemantics.ReachesResult ∧\n\
               Trusted.MirSemantics.WellFormed ∧ RefReachesOutcome\n\
             def CanaryD7cBinopMoveThenMoveUbClaim : Prop :=\n\
               progBinOpMoveThenMoveD7c = encodeProg ∧ Trusted.MirSemantics.ReachesResult ∧\n\
               Trusted.MirSemantics.WellFormed ∧ RefReachesOutcome\n\
             def CanaryD8SelfMoveOkClaim : Prop :=\n\
               progSelfMoveD8 = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def CanaryD9MoveUnitZstOkClaim : Prop :=\n\
               progMoveUnitZstD9 = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def CanaryD10AddUncheckedOverflowUbClaim : Prop :=\n\
               Trusted.MirSemantics.progAddUncheckedU32 = Trusted.MirSemantics.progAddU32 ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.ReachesResult ∧\n\
               Trusted.MirSemantics.WellFormed ∧ RefReachesOutcome ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefBehavior\n\
             {VALID_D11_DEF}\
             {VALID_D12_DEF}\
             {VALID_D13_DEF}\
             def CanaryD14CharCmpAndSwitchOkClaim : Prop :=\n\
               Trusted.MirSemantics.mkBinOpProg = Trusted.MirSemantics.mkCmpDiscriminantProg ∧\n\
               Trusted.MirAst.BinOp.cmp = Trusted.MirAst.MirTy.char ∧\n\
               Trusted.MirSemantics.progCharSwitch = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def CanaryD15IntToIntCastClaim : Prop :=\n\
               Trusted.MirSemantics.mkIntToIntCastProg = Trusted.MirAst.MirTy.char ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ Trusted.MirSemantics.ReachesResult ∧\n\
               RefWellFormed ∧ RefBehavior ∧ RefReachesOutcome\n\
             def CanaryD16WithOverflowOkClaim : Prop :=\n\
               Trusted.MirSemantics.mkBinOpProg = Trusted.MirSemantics.overflowPairTy ∧\n\
               Trusted.MirAst.BinOp.addWithOverflow = Trusted.MirAst.BinOp.subWithOverflow ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def RefStepSoundForAllowedStepClaim : Prop := {ref_step_allowed_def}\n\
             {VALID_BYTES_CODEC_DEF}\
             end Trusted.Correspondence\n",
            init_ref_state = self.init_ref_state,
            eval_ref_step = self.eval_ref_step,
            ref_allowed_step = self.ref_allowed_step,
        );
        for (from, to) in &self.replacements {
            assert_eq!(
                out.matches(from.as_str()).count(),
                1,
                "synthetic claim drifted: missing or ambiguous {from:?}"
            );
            out = out.replace(from, to);
        }
        out
    }
}

/// Declarative spec for `Anneal.MirCorrespondenceProof`.
#[derive(Clone, Debug)]
pub struct ProofsSpec {
    pub corr_choices: String,
    pub fault_choices: String,
    pub wiring: String,
    pub d6: String,
    pub ref_step_allowed: String,
    pub bytes_codec: String,
}

impl ProofsSpec {
    pub fn valid() -> Self {
        Self {
            corr_choices: "⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, Eq.refl _⟩".to_string(),
            fault_choices: "⟨True.intro, True.intro, Eq.refl _⟩".to_string(),
            wiring: "⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩".to_string(),
            d6: "⟨Eq.refl _, True.intro, True.intro, True.intro⟩".to_string(),
            ref_step_allowed: "⟨True.intro, Eq.refl _⟩".to_string(),
            bytes_codec: "⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩".to_string(),
        }
    }

    pub fn render(&self) -> String {
        format!(
            "prelude\nimport Trusted.Correspondence\n\
             namespace Anneal.MirCorrespondenceProof\n\
             open Trusted.Correspondence\n\
             theorem correspondence_claim_holds : CorrespondenceClaim :=\n\
               ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, Eq.refl _⟩\n\
             theorem fault_equivalence_claim_holds : FaultEquivalenceClaim :=\n\
               ⟨True.intro, True.intro, Eq.refl _⟩\n\
             theorem correspondence_at_choices_claim_holds : CorrespondenceAtChoicesClaim :=\n\
               {corr_choices}\n\
             theorem fault_equivalence_at_choices_claim_holds : FaultEquivalenceAtChoicesClaim :=\n\
               {fault_choices}\n\
             theorem miri_move_deinit_wiring_claim_holds : MiriMoveDeinitWiringClaim :=\n\
               {wiring}\n\
             theorem decodeProg_encodeProg : DecodeProgEncodeProgClaim := Eq.refl _\n\
             theorem encodeProg_types_canonical : EncodeProgTypesCanonicalClaim := Eq.refl _\n\
             theorem encodeStmt_no_dormant_noops : EncodeStmtNoDormantNoopsClaim := Eq.refl _\n\
             theorem encodeRvalue_binaryOp_iff : EncodeRvalueBinaryOpIffClaim := Eq.refl _\n\
             theorem encodeRvalue_unaryOp_iff : EncodeRvalueUnaryOpIffClaim := Eq.refl _\n\
             theorem encodeStmt_assign_iff : EncodeStmtAssignIffClaim := ⟨Eq.refl _, Eq.refl _⟩\n\
             theorem state_unique_of_simulationInv : StateUniqueOfSimulationInvClaim := True.intro\n\
             theorem refState_unique_of_simulationInv : RefStateUniqueOfSimulationInvClaim := True.intro\n\
             theorem initRefState_sim : InitRefStateSimClaim := ⟨Eq.refl _, Eq.refl _, True.intro⟩\n\
             theorem evalRefStep_eq : EvalRefStepEqClaim := ⟨Eq.refl _, Eq.refl _, Eq.refl _⟩\n\
             theorem sim_of_refStep : SimOfRefStepClaim := ⟨Eq.refl _, True.intro, True.intro, True.intro⟩\n\
             theorem sim_of_refReaches : SimOfRefReachesClaim := ⟨Eq.refl _, True.intro, True.intro, True.intro⟩\n\
             theorem refWellFormed_of_wellFormed : RefWellFormedOfWellFormedClaim := ⟨True.intro, True.intro, Eq.refl _⟩\n\
             theorem refBehavior_of_behavior : RefBehaviorOfBehaviorClaim := ⟨True.intro, True.intro, Eq.refl _⟩\n\
             theorem behavior_of_refBehavior : BehaviorOfRefBehaviorClaim := ⟨True.intro, True.intro, Eq.refl _⟩\n\
             theorem behavior_iff_refBehavior : BehaviorIffRefBehaviorClaim := ⟨True.intro, True.intro, Eq.refl _⟩\n\
             theorem diverges_iff_refDiverges : DivergesIffRefDivergesClaim := ⟨True.intro, True.intro, Eq.refl _⟩\n\
             theorem canary_D6_use_after_move_ub : CanaryD6UseAfterMoveUbClaim := {d6}\n\
             theorem canary_D7a_binop_copy_then_move_ok : CanaryD7aBinopCopyThenMoveOkClaim :=\n\
               ⟨Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D7b_binop_move_then_copy_ub : CanaryD7bBinopMoveThenCopyUbClaim :=\n\
               ⟨Eq.refl _, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D7c_binop_move_then_move_ub : CanaryD7cBinopMoveThenMoveUbClaim :=\n\
               ⟨Eq.refl _, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D8_self_move_ok : CanaryD8SelfMoveOkClaim :=\n\
               ⟨Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D9_move_unit_zst_ok : CanaryD9MoveUnitZstOkClaim :=\n\
               ⟨Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D10_add_unchecked_overflow_ub : CanaryD10AddUncheckedOverflowUbClaim :=\n\
               ⟨Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D11_enum_discriminant_and_const_ok : CanaryD11EnumDiscriminantAndConstOkClaim :=\n\
               ⟨Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D12_zst_enum_move_and_discr_ok : CanaryD12ZstEnumMoveAndDiscrOkClaim :=\n\
               ⟨Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D13_enum_invalid_tag_and_uninit_ub : CanaryD13EnumInvalidTagAndUninitUbClaim :=\n\
               ⟨Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D14_char_cmp_and_switch_ok : CanaryD14CharCmpAndSwitchOkClaim :=\n\
               ⟨Eq.refl _, Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D15_int_to_int_cast : CanaryD15IntToIntCastClaim :=\n\
               ⟨Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro, True.intro, True.intro⟩\n\
             theorem canary_D16_with_overflow_ok : CanaryD16WithOverflowOkClaim :=\n\
               ⟨Eq.refl _, Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
             theorem refStep_sound_for_allowedStep_holds : RefStepSoundForAllowedStepClaim :=\n\
               {ref_step_allowed}\n\
             theorem bytes_codec_matches_miri : BytesCodecMatchesMiriClaim :=\n\
               {bytes_codec}\n\
             end Anneal.MirCorrespondenceProof\n",
            corr_choices = self.corr_choices,
            fault_choices = self.fault_choices,
            wiring = self.wiring,
            d6 = self.d6,
            ref_step_allowed = self.ref_step_allowed,
            bytes_codec = self.bytes_codec,
        )
    }
}

/// Concise builder for [`InspectorRequest::CorrespondenceAudit`] inputs,
/// defaulting `candidate:mir_semantics` tiers cleanly without boilerplate.
#[derive(Clone, Debug)]
pub struct CorrAuditRequestBuilder {
    pub search_path: Vec<PathBuf>,
    pub trusted: Vec<String>,
    pub corr_trusted: Vec<String>,
    pub theory: Vec<String>,
    pub corr_theory: Vec<String>,
    pub vendor_miri: Vec<String>,
    pub module_tiers: BTreeMap<String, TrustTier>,
}

impl CorrAuditRequestBuilder {
    pub fn empty(search_path: Vec<PathBuf>) -> Self {
        Self {
            search_path,
            trusted: Vec::new(),
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::new(),
        }
    }

    pub fn mir_semantics_tier() -> TrustTier {
        TrustTier::Candidate(CandidateFeature::MirSemantics)
    }

    pub fn with_trusted_vetted(mut self, module: &str) -> Self {
        self.trusted.push(module.to_string());
        self.module_tiers.insert(module.to_string(), TrustTier::Vetted);
        self
    }

    pub fn with_trusted_candidate(mut self, module: &str) -> Self {
        self.trusted.push(module.to_string());
        self.module_tiers.insert(module.to_string(), Self::mir_semantics_tier());
        self
    }

    pub fn with_corr_trusted_candidate(mut self, module: &str) -> Self {
        self.corr_trusted.push(module.to_string());
        self.module_tiers.insert(module.to_string(), Self::mir_semantics_tier());
        self
    }

    pub fn with_corr_theory(mut self, module: &str) -> Self {
        self.corr_theory.push(module.to_string());
        self
    }

    pub fn with_vendor_miri(mut self, module: &str) -> Self {
        self.vendor_miri.push(module.to_string());
        self
    }

    pub fn build(self) -> InspectorRequest {
        InspectorRequest::CorrespondenceAudit {
            search_path: self.search_path,
            trusted: self.trusted,
            corr_trusted: self.corr_trusted,
            theory: self.theory,
            corr_theory: self.corr_theory,
            vendor_miri: self.vendor_miri,
            module_tiers: self.module_tiers,
        }
    }
}

/// Stateful Pass 2 synthetic correspondence harness pre-seeded with
/// `Miri.FakeStubs`, `Trusted.MirSemantics`, `Trusted.MirSemantics.SubHelper`,
/// `Trusted.MirModel`, and `Trusted.MirHelper`.
pub struct CorrespondenceHarness {
    pub _fix: TempFixture,
    pub checker: Checker,
    pub trusted_lib: PathBuf,
    pub corr_src: PathBuf,
    pub corr_lib: PathBuf,
    pub vendor_src: PathBuf,
    pub vendor_lib: PathBuf,
    pub search_paths: Vec<PathBuf>,
}

impl CorrespondenceHarness {
    pub fn new() -> Self {
        let fix = TempFixture::new(None);
        let mut checker = Checker::new(&fix.root, None).unwrap();
        checker.set_require_mir_wp(false);
        checker.run().unwrap();
        let trusted_lib = checker.stage().join("lib");
        let corr_src = checker.stage().join("src/fake-corr");
        let corr_lib = checker.stage().join("fake-corr-lib");
        let vendor_src = checker.stage().join("src/fake-vendor");
        let vendor_lib = checker.stage().join("fake-vendor-lib");
        let search_paths = vec![trusted_lib.clone(), vendor_lib.clone(), corr_lib.clone()];

        compile_forged_module(
            &mut checker,
            &vendor_src,
            &vendor_lib,
            &[],
            "Miri.FakeStubs",
            MIRI_FAKE_STUBS_SRC,
        );
        compile_forged_module(
            &mut checker,
            &corr_src,
            &trusted_lib,
            &[],
            "Trusted.MirSemantics",
            TRUSTED_MIR_SEMANTICS_SRC,
        );
        compile_forged_module(
            &mut checker,
            &corr_src,
            &trusted_lib,
            &[],
            "Trusted.MirSemantics.SubHelper",
            TRUSTED_MIR_SEMANTICS_SUB_HELPER_SRC,
        );
        compile_forged_module(
            &mut checker,
            &corr_src,
            &trusted_lib,
            &[],
            "Trusted.MirModel",
            TRUSTED_MIR_MODEL_SRC,
        );
        compile_forged_module(
            &mut checker,
            &corr_src,
            &trusted_lib,
            &[],
            "Trusted.MirHelper",
            TRUSTED_MIR_HELPER_SRC,
        );

        Self {
            _fix: fix,
            checker,
            trusted_lib,
            corr_src,
            corr_lib,
            vendor_src,
            vendor_lib,
            search_paths,
        }
    }

    pub fn base_request(&self) -> CorrAuditRequestBuilder {
        CorrAuditRequestBuilder::empty(self.search_paths.clone())
            .with_trusted_vetted("Trusted")
            .with_trusted_candidate("Trusted.MirModel")
            .with_trusted_candidate("Trusted.MirHelper")
            .with_trusted_candidate("Trusted.MirSemantics")
            .with_trusted_candidate("Trusted.MirSemantics.SubHelper")
            .with_corr_trusted_candidate("Trusted.Correspondence")
            .with_corr_theory("Anneal.MirCorrespondenceProof")
            .with_vendor_miri("Miri.FakeStubs")
    }

    pub fn compile_trusted(&mut self, imports: &[&str], module: &str, body: &str) {
        let corr_src = self.corr_src.clone();
        let trusted_lib = self.trusted_lib.clone();
        compile_forged_module(&mut self.checker, &corr_src, &trusted_lib, imports, module, body);
    }

    pub fn compile_corr_proof(&mut self, imports: &[&str], module: &str, body: &str) {
        let corr_src = self.corr_src.clone();
        let corr_lib = self.corr_lib.clone();
        compile_forged_module(&mut self.checker, &corr_src, &corr_lib, imports, module, body);
    }

    pub fn publish(&mut self, claims: &ClaimsSpec, proofs: &ProofsSpec) {
        self.compile_trusted(&CORR_DEPS, "Trusted.Correspondence", &claims.render());
        self.compile_corr_proof(
            &["Trusted.Correspondence"],
            "Anneal.MirCorrespondenceProof",
            &proofs.render(),
        );
    }

    pub fn run_audit(&mut self, req: InspectorRequest) -> Result<Json, Failure> {
        self.checker.inspect(req)
    }

    pub fn assert_default_rejected(&mut self, expected_substr: &str) {
        let req = self.base_request().build();
        assert_policy_rejection(self.run_audit(req), "correspondence-audit", expected_substr);
    }
}
