import Miri.Interpreter.MemoryShims

/-! Pinned shims/os_str.rs. Host OsStr encodings remain explicit operational
leaves; they are not replaced with Lean UTF-8 strings. Allocation size follows
the source encoded-byte length even for UTF-16 output. Path conversion itself
is implemented on exact code units, preserving invalid non-Unicode paths.
-/
namespace Miri.Interpreter.OsStrings
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Direction where | hostToTarget | targetToHost deriving DecidableEq, Repr

/-- Generic code units implement the same source routine for u8 and u16. -/
def windowsToUnix [BEq A] (ascii : UInt8 → A) (path : List A) : List A := Id.run do
  let sep := ascii 47
  let path := path.map (fun c => if c == ascii 92 then sep else c)
  match path with
  | a::b::c::d::rest =>
    if a == sep && b == sep && c == ascii 63 && d == sep then return d::rest
    if b == ascii 58 && c == sep then return sep::path
    return path
  | _::b::c::[] =>
    if b == ascii 58 && c == sep then return sep::path
    return path
  | _ => return path

def unixToWindows [BEq A] (ascii : UInt8 → A) (path : List A) : List A := Id.run do
  let sep := ascii 92
  let path := path.map (fun c => if c == ascii 47 then sep else c)
  match path with
  | a::b::c::d::rest =>
    if a == sep && c == ascii 58 && d == sep then return b::c::d::rest
    if a == sep && b != sep then return sep::sep::ascii 63::path
    return path
  | a::b::_ =>
    if a == sep && b != sep then return sep::sep::ascii 63::path
    return path
  | [a] =>
    if a == sep then return sep::sep::ascii 63::path
    return path
  | [] => return []

structure Hooks (P S Os Kind : Type) where
  hostWindows : Bool
  hostUnix : Bool
  targetWindows : Bool
  /-- OsStr::from_bytes / OsString::from_vec on the actual Unix host. -/
  fromUnixBytes : ByteArray → Os
  /-- std::str::from_utf8 then OsStr::new, retaining invalid-UTF8 unsupported. -/
  fromUtf8 : ByteArray → Except StepError Os
  /-- Windows from_wide is lossless; other hosts use strict String::from_utf16. -/
  fromWide : Array UInt16 → Except StepError Os
  /-- Windows encode_wide; other hosts require valid UTF8 then encode_utf16. -/
  toWide : Os → Except StepError (Array UInt16)
  encodedBytes : Os → ByteArray
  encodedLength : Os → Nat
  readCString : Pointer (Option P) → M S ByteArray
  readWideString : Pointer (Option P) → M S (Array UInt16)
  writeCString : ByteArray → Pointer (Option P) → UInt64 → M S (Bool × UInt64)
  writeWideString : Array UInt16 → Pointer (Option P) → UInt64 → M S (Bool × UInt64)
  /-- Actual Ty::new_array(u8/u16,count) and layout_of, including runtime type
  interning; a matching byte layout cannot substitute a fabricated type ID. -/
  arrayLayout : Bool → UInt64 → M S LocalLayout
  allocate : LocalLayout → Kind → M S (Pointer (Option P))

private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error

private def sourceUnwrap (operation : String) (action : M S A) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => .error (.invalidProgram s!"{operation} source unwrap: {reprStr error}") state

def bytesToOsStr (h : Hooks P S Os Kind) (bytes : ByteArray) : Except StepError Os :=
  if h.hostUnix then .ok (h.fromUnixBytes bytes) else h.fromUtf8 bytes

/-- Unix `OsString::into_string`: consume the exact encoded bytes and return
the string only when they form valid UTF-8. This is distinct from lossy display
conversion and is the operation used by Miri's `localtime_r` for guest `TZ`. -/
def unixIntoString (bytes : ByteArray) : Option String := String.fromUTF8? bytes

def unixIntoStringOf {Os : Type} (encodedBytes : Os → ByteArray) (value : Os) :
    Option String := unixIntoString (encodedBytes value)

def readOsString (h : Hooks P S Os Kind) (pointer : Pointer (Option P)) : M S Os := do
  lift (bytesToOsStr h (← h.readCString pointer))

def readOsWideString (h : Hooks P S Os Kind) (pointer : Pointer (Option P)) : M S Os := do
  lift (h.fromWide (← h.readWideString pointer))

def writeOsString (h : Hooks P S Os Kind) (value : Os) (pointer : Pointer (Option P))
    (capacity : UInt64) : M S (Bool × UInt64) :=
  h.writeCString (h.encodedBytes value) pointer capacity

/-- Return the original failed/full length result even after successfully
writing the truncated prefix, exactly as the source helper does. -/
def writeOsWideString (h : Hooks P S Os Kind) (value : Os) (pointer : Pointer (Option P))
    (capacity : UInt64) (truncate : Bool := false) : M S (Bool × UInt64) := do
  let units ← lift (h.toWide value)
  let (written,needed) ← h.writeWideString units pointer capacity
  if truncate && !written && capacity > 0 then
    let length := capacity.toNat - 1
    if length > units.size then throw (.invalidProgram "wide truncation slice out of bounds")
    let (written,length) ← h.writeWideString (units.extract 0 length) pointer capacity
    unless written && length == capacity do
      throw (.invalidProgram "wide truncated write source assertion")
  return (written,needed)

/-- Source uses encoded OsStr length for both arrays, before conversion to
UTF-16. Its unwrap/assert failure occurs after the actual allocation effects. -/
def allocOsString (h : Hooks P S Os Kind) (value : Os) (kind : Kind) (wide : Bool := false) :
    M S (Pointer (Option P)) := do
  let count := h.encodedLength value + 1
  if count >= 2^64 then throw (.invalidProgram "OsStr allocation length conversion/strict_add overflow")
  let count := UInt64.ofNat count
  let layout ← sourceUnwrap "OsStr array layout" (h.arrayLayout wide count)
  let pointer ← h.allocate layout kind
  let (written,_) ← sourceUnwrap "OsStr write" (if wide then writeOsWideString h value pointer count
    else writeOsString h value pointer count)
  unless written do throw (.invalidProgram "allocated OsStr buffer write failed")
  return pointer

def convertPath (h : Hooks P S Os Kind) (value : Os) (direction : Direction) : Except StepError Os := do
  if h.hostWindows then
    if h.targetWindows then return value
    let path ← h.toWide value
    let ascii := fun byte : UInt8 => UInt16.ofNat byte.toNat
    let path := match direction with
      | .hostToTarget => windowsToUnix ascii path.toList
      | .targetToHost => unixToWindows ascii path.toList
    h.fromWide path.toArray
  else
    if !h.targetWindows then return value
    let path := (h.encodedBytes value).data.toList
    let path := match direction with
      | .hostToTarget => unixToWindows id path
      | .targetToHost => windowsToUnix id path
    return h.fromUnixBytes (ByteArray.mk path.toArray)

def readPath (h : Hooks P S Os Kind) (pointer : Pointer (Option P)) (wide : Bool := false) : M S Os := do
  let value ← if wide then readOsWideString h pointer else readOsString h pointer
  lift (convertPath h value .targetToHost)

def writePath (h : Hooks P S Os Kind) (path : Os) (pointer : Pointer (Option P))
    (capacity : UInt64) (wide truncate : Bool := false) : M S (Bool × UInt64) := do
  let value ← lift (convertPath h path .hostToTarget)
  if wide then writeOsWideString h value pointer capacity truncate
  else writeOsString h value pointer capacity

def allocPath (h : Hooks P S Os Kind) (path : Os) (kind : Kind) (wide : Bool := false) :
    M S (Pointer (Option P)) := do
  let value ← lift (convertPath h path .hostToTarget)
  allocOsString h value kind wide

end Miri.Interpreter.OsStrings
