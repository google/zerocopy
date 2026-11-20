import Miri.Input.EvalMiriSourceConstruction
import Miri.Input.EvalMiriHostEffectsConstruction
import Miri.TreeBorrows.DiagnosticsRender

/-! Source Tree Borrows implementations of the two Miri diagnostic shims.
Names mutate the allocation's real BorrowTree; printing renders the current
allocation-local ranges and permissions and writes through the caller's actual
stderr writer. -/
namespace Miri.Input.EvalMiriTreeDiagnostics
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalConfigurationCore.SourceOther Raw Listener TcpStream Error
abbrev Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler :=
  EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler
abbrev User Os R P H D O Aff B Host := EvalCoreMachine.User Os R P H D O Aff B Host
abbrev Control Os R P H D O Aff B Host :=
  ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D O Aff B Host)
abbrev State Os R P H D O Aff B Host := EvalCoreMachine.State Os R P H D O Aff B Host
abbrev M Os R P H D O Aff B Host A :=
  MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) A

private def lossyUtf8 (bytes : ByteArray) : String := Id.run do
  let mut result := ""
  let mut index := 0
  while hIndex : index < bytes.size do
    let first := bytes[index]'hIndex |>.toNat
    let count :=
      if first ≤ 0x7f then 1
      else if first ≥ 0xc2 && first ≤ 0xdf then 2
      else if first ≥ 0xe0 && first ≤ 0xef then 3
      else if first ≥ 0xf0 && first ≤ 0xf4 then 4
      else 0
    if count == 0 then
      result := result ++ "�"
      index := index + 1
    else
      let mut invalidAt : Option Nat := none
      let mut offset := 1
      while offset < count && invalidAt.isNone do
        if hByte : index + offset < bytes.size then
          let byte := bytes[index + offset]'hByte |>.toNat
          let valid :=
            if offset > 1 then byte ≥ 0x80 && byte ≤ 0xbf
            else if first == 0xe0 then byte ≥ 0xa0 && byte ≤ 0xbf
            else if first == 0xed then byte ≥ 0x80 && byte ≤ 0x9f
            else if first == 0xf0 then byte ≥ 0x90 && byte ≤ 0xbf
            else if first == 0xf4 then byte ≥ 0x80 && byte ≤ 0x8f
            else byte ≥ 0x80 && byte ≤ 0xbf
          if !valid then invalidAt := some offset
          else offset := offset + 1
        else
          offset := count
      if let some validPrefixLength := invalidAt then
        result := result ++ "�"
        index := index + validPrefixLength
      else if index + count > bytes.size then
        result := result ++ "�"
        index := bytes.size
      else
        let slice := bytes.extract index (index + count)
        match String.fromUTF8? slice with
        | some decoded =>
          result := result ++ decoded
          index := index + count
        | none =>
          result := result ++ "�"
          index := index + 1
  return result

private def emitLine
    (writeStderr : ByteArray → M Os R P H D (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) Unit)
    (line : String) : M Os R P H D (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) Unit :=
  writeStderr (line ++ "\n").toUTF8

/-- Source `give_pointer_debug_name` for Tree Borrows. Wildcard and missing
provenance pointers emit the upstream stderr diagnostic and remain successful;
concrete pointers mutate the actual live allocation's persistent tree. -/
def namePointer [DecidableEq MiriMemoryKind]
    (machine : MiriShimMachine.Hooks MiriMemoryKind
      (Control Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C MachineHooks.FrameExtra (Other Raw Listener TcpStream Error))
    (writeStderr : ByteArray → M Os R P H D (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) Unit)
    (pointer : Pointer (Option Provenance)) (parentDistance : UInt8) (nameBytes : ByteArray) :
    M Os R P H D (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) Unit := do
  let name := lossyUtf8 nameBytes
  unless (← get).machine.borrowTracker.isSome do
    throw (.invalidProgram "miri_pointer_name called without an active Tree Borrows tracker")
  match pointer.provenance with
  | none => emitLine writeStderr s!"Can't give the name {name} to pointer without provenance"
  | some .wildcard => emitLine writeStderr s!"Can't give the name {name} to wildcard pointer"
  | some (.concrete allocId tag) => do
    -- `get_alloc_extra` lazily materializes compiler-global allocations in
    -- the source machine. Run that canonical path before inspecting memory.
    machine.pointer.ensureTreeExtra allocId
    let state ← get
    let some entry := state.machine.memory.live.find? (fun item => item.1 == allocId)
      | throw (.invalidProgram "miri_pointer_name allocation has no live Tree Borrows extra")
    let tree := entry.2.allocation.extra
    let tree ← match tree.givePointerDebugName tag parentDistance.toNat name with
      | .ok tree => pure tree
      | .error error => throw (.invalidProgram s!"Tree Borrows pointer name: {reprStr error}")
    let memory ← match state.machine.memory.setLiveAllocation allocId
        (entry.2.allocation.setExtra tree) with
      | .ok memory => pure memory
      | .error error => throw (.invalidProgram s!"Tree Borrows pointer name update: {reprStr error}")
    modify fun current => {current with machine := {current.machine with memory}}

/-- Source `print_borrow_state` for the interpreter's real Tree Borrows
allocation extra and protector map. The raw host writer is supplied by the
source residual constructor, which applies `write_all` and ignores host I/O
errors just like upstream's `eprintln!` path. -/
def printBorrowState [DecidableEq MiriMemoryKind]
    (machine : MiriShimMachine.Hooks MiriMemoryKind
      (Control Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
      C MachineHooks.FrameExtra (Other Raw Listener TcpStream Error))
    (writeStderr : ByteArray → M Os R P H D (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) Unit)
    (image : AllocationImage.Imported) (sourceId : UInt64) (showUnnamed : Bool) :
    M Os R P H D (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) Unit := do
  let state ← get
  if sourceId == 0 then
    emitLine writeStderr "0 is not the ID of a live data allocation"
    return
  let allocId ← EvalMiriHostEffectsConstruction.sourceAllocIdFromImage image sourceId
  let some allocId := allocId
    | emitLine writeStderr s!"{sourceId} is not the ID of a live data allocation"
      return
  let info ← match state.machine.memory.getAllocInfo allocId with
    | .ok info => pure info
    | .error _ => do
      emitLine writeStderr s!"{sourceId} is not the ID of a live data allocation"
      return
  if info.kind != .liveData then
    emitLine writeStderr s!"{sourceId} is not the ID of a live data allocation"
    return
  match state.machine.borrowTracker with
  | none => emitLine writeStderr "attempted to print borrow state, but no borrow state is being tracked"
  | some _ => do
    -- Like rustc's `get_alloc_extra`, this can insert the lazy tree extra for
    -- an imported compiler global. Read the fresh machine state afterwards.
    machine.pointer.ensureTreeExtra allocId
    let state ← get
    let some tracker := state.machine.borrowTracker
      | throw (.invalidProgram "Tree Borrows tracker disappeared during diagnostic materialization")
    let some entry := state.machine.memory.live.find? (fun item => item.1 == allocId)
      | throw (.invalidProgram "miri_print_borrow_state allocation is not live")
    let tree := entry.2.allocation.extra
    let lines ← match TreeBorrows.DiagnosticsRender.render tree tracker.global.protectedTags showUnnamed with
      | .ok lines => pure lines
      | .error reason => throw (.invalidProgram s!"Tree Borrows diagnostic rendering: {reason}")
    for line in lines do emitLine writeStderr line

end Miri.Input.EvalMiriTreeDiagnostics
