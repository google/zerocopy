/-! Exact pinned `rustc_abi/src/extern_abi.rs::ExternAbi` identity. In particular,
System/C/Cdecl and unwind distinctions survive target-specific ABI lowering.
This is independent of FnAbi's canonical calling convention. -/
namespace Miri.ABI
inductive ExternAbi where
  | C (unwind : Bool)
  | System (unwind : Bool)
  | Rust
  | RustCall
  | RustCold
  | RustInvalid
  | RustPreserveNone
  | RustTail
  | LlvmIntrinsic
  | Custom
  | EfiApi
  | Swift
  | Aapcs (unwind : Bool)
  | CmseNonSecureCall
  | CmseNonSecureEntry
  | GpuKernel
  | PtxKernel
  | AvrInterrupt
  | AvrNonBlockingInterrupt
  | Msp430Interrupt
  | RiscvInterruptM
  | RiscvInterruptS
  | X86Interrupt
  | Cdecl (unwind : Bool)
  | Stdcall (unwind : Bool)
  | Fastcall (unwind : Bool)
  | Thiscall (unwind : Bool)
  | Vectorcall (unwind : Bool)
  | SysV64 (unwind : Bool)
  | Win64 (unwind : Bool)
  deriving DecidableEq, BEq, Repr

namespace ExternAbi
def cNoUnwind : ExternAbi := .C false
def systemNoUnwind : ExternAbi := .System false
def rust : ExternAbi := .Rust
end ExternAbi
end Miri.ABI
