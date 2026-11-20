import Miri.Interpreter.ForeignItems
import Miri.Memory.Pointer

/-! Pinned env.rs and Unix/Windows env storage. Os is a lossless target OS
string, never a host String approximation. All memory operations are effectful
leaves and must preserve provenance, allocation kinds, and race checks. -/
namespace Miri.Interpreter.EnvVars
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure Unix (P : Type) where
  variables : Array (ByteArray × Pointer P)
  environ : Pointer P
inductive State (P Os : Type) where
  | uninit
  | unix (vars : Unix P)
  | windows (variables : Array (Os × Os))
inductive Kind where | machine | externStatic | runtime | winLocal deriving DecidableEq, Repr
structure Hooks (P Os S : Type) where
  family : ForeignItems.Family
  get : M S (State P Os)
  put : State P Os → M S Unit
  encodeUnix : Os → M S ByteArray
  decodeUnix : ByteArray → M S Os
  emptyOs : Os
  concatOs : Os → Os → Os
  asciiOs : String → Os
  isEmpty : Os → Bool
  containsEquals : Os → Bool
  nullPointer : Pointer P
  isNull : Pointer P → M S Bool
  readCString : Pointer P → M S ByteArray
  allocCString : ByteArray → Kind → M S (Pointer P)
  allocPointerCell : Kind → M S (Pointer P)
  allocPointerArray : Nat → Kind → M S (Pointer P)
  projectPointerElement : Pointer P → Nat → Nat → M S (Pointer P)
  readPointer : Pointer P → M S (Pointer P)
  writePointer : Pointer P → Pointer P → M S Unit
  offset : Pointer P → UInt64 → M S (Pointer P)
  deallocate : Pointer P → Kind → M S Unit
  invalidArgument : M S Int32
  readWideString : Pointer P → M S Os
  writeWideString : Os → Pointer P → UInt32 → M S (Bool × UInt64)
  allocWideString : Os → Kind → M S (Pointer P)
  envVarNotFound : M S Unit
private def unix (h : Hooks P Os S) : M S (Unix P) := do
  match ← h.get with
  | .unix vars => pure vars
  | _ => throw (.invalidProgram "Unix environment is uninitialized or target is not Unix")
private def windows (h : Hooks P Os S) : M S (Array (Os × Os)) := do
  match ← h.get with
  | .windows vars => pure vars
  | _ => throw (.invalidProgram "Windows environment is uninitialized or target is not Windows")

def allocEnvironmentBlock (h : Hooks P Os S) (values : Array (Pointer P)) : M S (Pointer P) := do
  let values := values.push h.nullPointer
  let block ← h.allocPointerArray values.size .machine
  for index in [:values.size] do
    let some pointer := values[index]? | throw (.invalidProgram "environment array index")
    h.writePointer pointer (← h.projectPointerElement block values.size index)
  return block

def allocVariable (h : Hooks P Os S) (name value : ByteArray) : M S (Pointer P) :=
  h.allocCString (name ++ ByteArray.mk #[61] ++ value) .machine

def initUnix (h : Hooks P Os S) (variables : Array (ByteArray × ByteArray)) : M S Unit := do
  let mut entries := #[]
  for (name,value) in variables do
    let pointer ← allocVariable h name value
    entries := entries.push (name,pointer)
  let environ ← h.allocPointerCell .externStatic
  let block ← allocEnvironmentBlock h (entries.map (·.2))
  h.writePointer block environ
  h.put (.unix ⟨entries,environ⟩)

/-- The environ cell read is required even when the lookup misses: it participates
in data-race detection. The returned pointer aliases the actual name=value allocation. -/
def getPointer (h : Hooks P Os S) (name : ByteArray) : M S (Option (Pointer P)) := do
  let vars ← unix h
  let _ ← h.readPointer vars.environ
  let some (_,pointer) := vars.variables.find? (·.1 == name) | return none
  if name.size + 1 >= 2^64 then throw (.invalidProgram "environment name length overflow")
  return some (← h.offset pointer (UInt64.ofNat (name.size + 1)))

def getEnv [DecidableEq Os] (h : Hooks P Os S) (name : Os) : M S (Option Os) := do
  match ← h.get with
  | .uninit => return none
  | .windows variables => return (variables.find? (·.1 == name)).map (·.2)
  | .unix _ =>
    let some pointer ← getPointer h (← h.encodeUnix name) | return none
    return some (← h.decodeUnix (← h.readCString pointer))

def getenv (h : Hooks P Os S) (name : Pointer P) : M S (Pointer P) := do
  if h.family != .unix then throw (.invalidProgram "getenv requires Unix")
  return (← getPointer h (← h.readCString name)).getD h.nullPointer

def updateEnviron (h : Hooks P Os S) : M S Unit := do
  let vars ← unix h
  let old ← h.readPointer vars.environ
  h.deallocate old .machine
  let vars ← unix h
  let block ← allocEnvironmentBlock h (vars.variables.map (·.2))
  h.writePointer block vars.environ
private def validName (name : ByteArray) : Bool :=
  !name.isEmpty && !name.data.contains 61

def setenv (h : Hooks P Os S) (namePointer valuePointer : Pointer P) : M S Int32 := do
  if h.family != .unix then throw (.invalidProgram "setenv requires Unix")
  if ← h.isNull namePointer then return ← h.invalidArgument
  let name ← h.readCString namePointer
  if !validName name then return ← h.invalidArgument
  let value ← h.readCString valuePointer
  let pointer ← allocVariable h name value
  let vars ← unix h
  let old := vars.variables.find? (·.1 == name)
  h.put (.unix { vars with variables := (vars.variables.filter (·.1 != name)).push (name,pointer) })
  if let some (_,old) := old then h.deallocate old .machine
  updateEnviron h
  return 0

def unsetenv (h : Hooks P Os S) (namePointer : Pointer P) : M S Int32 := do
  if h.family != .unix then throw (.invalidProgram "unsetenv requires Unix")
  if ← h.isNull namePointer then return ← h.invalidArgument
  let name ← h.readCString namePointer
  if !validName name then return ← h.invalidArgument
  let vars ← unix h
  let old := vars.variables.find? (·.1 == name)
  h.put (.unix { vars with variables := vars.variables.filter (·.1 != name) })
  if let some (_,old) := old then h.deallocate old .machine
  updateEnviron h
  return 0

/-- Config environment is supplied evidence. No process environment is read
implicitly, and explicit overrides win after forwarding. -/
def init [DecidableEq Os] (h : Hooks P Os S) (communicate : Bool)
    (forwarded : Array Os) (environment overrides : Array (Os × Os)) : M S Unit := do
  let mut variables := #[]
  for (name,value) in environment do
    if communicate || forwarded.contains name then
      variables := (variables.filter (·.1 != name)).push (name,value)
  for (name,value) in overrides do
    variables := (variables.filter (·.1 != name)).push (name,value)
  match h.family with
  | .unix =>
    let encoded ← variables.mapM fun (name,value) => do
      return (← h.encodeUnix name,← h.encodeUnix value)
    initUnix h encoded
  | .windows => h.put (.windows variables)
  | .other => h.put .uninit

private def checkWindows (h : Hooks P Os S) : M S Unit := do
  if h.family != .windows then throw (.invalidProgram "Windows environment API requires Windows")

def windowsBufferSize (result : Bool × UInt64) : Except StepError UInt32 := do
  let (success,len) := result
  if success && len == 0 then throw (.invalidProgram "successful wide string missing trailing null")
  let value := if success then len - 1 else len
  if value.toNat >= 2^32 then throw (.invalidProgram "wide string result exceeds DWORD")
  return UInt32.ofNat value.toNat

def getEnvironmentVariableW [DecidableEq Os] (h : Hooks P Os S)
    (name buffer : Pointer P) (size : UInt32) : M S UInt32 := do
  checkWindows h
  let name ← h.readWideString name
  let variables ← windows h
  if let some (_,value) := variables.find? (·.1 == name) then
    let result ← h.writeWideString value buffer size
    match windowsBufferSize result with
    | .ok size => return size
    | .error error => throw error
  else
    h.envVarNotFound
    return 0

def getEnvironmentStringsW (h : Hooks P Os S) : M S (Pointer P) := do
  checkWindows h
  let variables ← windows h
  let mut contents := h.emptyOs
  for (name,value) in variables do
    contents := h.concatOs contents (h.concatOs name
      (h.concatOs (h.asciiOs "=") (h.concatOs value (h.asciiOs "\x00"))))
  h.allocWideString contents .runtime

def freeEnvironmentStringsW (h : Hooks P Os S) (pointer : Pointer P) : M S Int32 := do
  checkWindows h
  h.deallocate pointer .runtime
  return 1

def setEnvironmentVariableW [DecidableEq Os] (h : Hooks P Os S)
    (namePointer valuePointer : Pointer P) : M S Bool := do
  checkWindows h
  if ← h.isNull namePointer then throw (.undefinedBehavior "pointer to environment variable name is NULL")
  let name ← h.readWideString namePointer
  if h.isEmpty name then throw (.unsupported "environment variable name is an empty string")
  if h.containsEquals name then throw (.unsupported "environment variable name contains '='")
  if ← h.isNull valuePointer then
    let variables ← windows h
    h.put (.windows (variables.filter (·.1 != name)))
  else
    let value ← h.readWideString valuePointer
    let variables ← windows h
    h.put (.windows ((variables.filter (·.1 != name)).push (name,value)))
  return true

structure ProcessHooks (S : Type) where
  communicate : Bool
  family : ForeignItems.Family
  os : String
  hostPid : M S UInt32
  activeThread : M S UInt32
  /-- Authoritative thread manager check includes termination and ID validity. -/
  threadIdTryFrom : UInt32 → M S (Option UInt32)

def getPid (h : ProcessHooks S) : M S UInt32 :=
  if h.communicate then h.hostPid else pure 1000

def getTid (h : ProcessHooks S) (thread : UInt32) : M S UInt32 := do
  match ForeignItems.getTid h.family (← getPid h) thread with
  | .ok tid => return tid
  | .error error => throw error

def currentTid (h : ProcessHooks S) : M S UInt32 := do getTid h (← h.activeThread)

def threadIdFromLinuxTid (h : ProcessHooks S) (tid : UInt32) : M S (Option UInt32) := do
  if h.os != "linux" && h.os != "android" then
    throw (.invalidProgram "Linux TID conversion requires Linux or Android")
  let pid ← getPid h
  if tid < pid then return none
  h.threadIdTryFrom (tid - pid)
/-- All environment-owned pointer roots, including the stable environ cell.
Windows/Uninit store no provenance. GC must visit these without dereferencing. -/
def provenanceRoots : State P Os → Array (Pointer P)
  | .uninit | .windows _ => #[]
  | .unix vars => #[vars.environ] ++ vars.variables.map (·.2)
end Miri.Interpreter.EnvVars
