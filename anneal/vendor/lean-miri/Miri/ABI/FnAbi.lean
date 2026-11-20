import Miri.ABI.CallConv

/-! Complete canonical calling-convention and FnAbi records from pinned
rustc_abi/canon_abi.rs and rustc_target/callconv/mod.rs:660–679. Target ABI
classification is supplied by the compiler, not recomputed by this module. -/
namespace Miri.ABI
inductive ArmCall where
  | Aapcs | CCmseNonSecureCall | CCmseNonSecureEntry
  deriving DecidableEq, Repr
inductive InterruptKind where
  | Avr | AvrNonBlocking | Msp430 | RiscvMachine | RiscvSupervisor | X86
  deriving DecidableEq, Repr
inductive X86Call where
  | Fastcall | Stdcall | SysV64 | Thiscall | Vectorcall | Win64
  deriving DecidableEq, Repr
inductive CanonAbi where
  | C | Rust | RustCold | RustPreserveNone | RustTail | Custom | Swift
  | Arm (call : ArmCall)
  | GpuKernel
  | Interrupt (kind : InterruptKind)
  | X86 (call : X86Call)
  deriving DecidableEq, Repr
namespace CanonAbi

def isRusticAbi : CanonAbi → Bool
  | .Rust | .RustCold | .RustPreserveNone | .RustTail => true
  | .C | .Custom | .Swift | .Arm _ | .GpuKernel | .Interrupt _ | .X86 _ => false
end CanonAbi
structure FnAbi (Ty : Type) where
  args : Array (ArgAbi Ty)
  ret : ArgAbi Ty
  cVariadic : Bool
  fixedCount : UInt32
  conv : CanonAbi
  canUnwind : Bool
  deriving DecidableEq, Repr
end Miri.ABI
