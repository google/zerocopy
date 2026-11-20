import Lean
import Miri.ABI.ExternAbi

/-! Validates the exact structured compiler ExternAbi variant fields. Diagnostic
spelling and target canonical convention do not participate in source identity. -/
namespace Miri.Input.CompilerExternAbi
open Lean

def decode (source : Json) : Except String ABI.ExternAbi := do
  unless (← (← source.getObjVal? "status").getStr?) == "supported" do
    throw "compiler ExternAbi is unsupported"
  let unwind ← source.getObjVal? "unwind"
  let kind ← (← source.getObjVal? "kind").getStr?
  match kind with
  | "c" => return .C (← unwind.getBool?)
  | "system" => return .System (← unwind.getBool?)
  | "rust" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .Rust
  | "rust_call" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RustCall
  | "rust_cold" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RustCold
  | "rust_invalid" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RustInvalid
  | "rust_preserve_none" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RustPreserveNone
  | "rust_tail" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RustTail
  | "llvm_intrinsic" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .LlvmIntrinsic
  | "custom" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .Custom
  | "efi_api" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .EfiApi
  | "swift" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .Swift
  | "aapcs" => return .Aapcs (← unwind.getBool?)
  | "cmse_nonsecure_call" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .CmseNonSecureCall
  | "cmse_nonsecure_entry" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .CmseNonSecureEntry
  | "gpu_kernel" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .GpuKernel
  | "ptx_kernel" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .PtxKernel
  | "avr_interrupt" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .AvrInterrupt
  | "avr_non_blocking_interrupt" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .AvrNonBlockingInterrupt
  | "msp430_interrupt" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .Msp430Interrupt
  | "riscv_interrupt_machine" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RiscvInterruptM
  | "riscv_interrupt_supervisor" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .RiscvInterruptS
  | "x86_interrupt" => do
    unless unwind == Json.null do throw "non-unwind ExternAbi variant contains an unwind field"
    pure .X86Interrupt
  | "cdecl" => return .Cdecl (← unwind.getBool?)
  | "stdcall" => return .Stdcall (← unwind.getBool?)
  | "fastcall" => return .Fastcall (← unwind.getBool?)
  | "thiscall" => return .Thiscall (← unwind.getBool?)
  | "vectorcall" => return .Vectorcall (← unwind.getBool?)
  | "sysv64" => return .SysV64 (← unwind.getBool?)
  | "win64" => return .Win64 (← unwind.getBool?)
  | _ => throw "unknown compiler ExternAbi variant"
end Miri.Input.CompilerExternAbi
