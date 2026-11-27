// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Synthetic Lean module sources and fixed module lists for the
//! correspondence harness.

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
def queryEmpty : Nat := 0
def scalarNatVal : Nat := 0
def TerminalOut.aborted : Nat := 0
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
def PanicStrategy.abort : Nat := 0
def PanicStrategy.unwind : Nat := 0
def AssertKind.divByZero : Nat := 0
def AssertKind.boundsCheck : Nat := 0
def AssertKind.misalignedPtrDeref : Nat := 0
def UnwindAction.continue_ : Nat := 0
def UnwindAction.cleanup : Nat := 0
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
