import Miri.Interpreter.WindowsFiles
import Miri.Interpreter.OsStrings

/-! Pinned windows/foreign_items.rs::win_get_full_path_name and its shim arm.
Unix-host normalization deliberately retains the upstream approximation. -/
namespace Miri.Interpreter.WindowsPaths
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Normalized where | direct (bytes : ByteArray) | absolute (bytes : ByteArray)
private def upper (byte : UInt8) : UInt8 := if byte >= 97 && byte <= 122 then byte-32 else byte
private def asciiEq (bytes : ByteArray) (text : String) : Bool := bytes.data.map upper == text.toUTF8.data
private def magicNames : Array String := #["CON","PRN","AUX","NUL","COM1","COM2","COM3","COM4","COM5","COM6","COM7","COM8","COM9","LPT1","LPT2","LPT3","LPT4","LPT5","LPT6","LPT7","LPT8","LPT9"]
private def components (bytes : ByteArray) : Array ByteArray := Id.run do
  let mut result := #[]
  let mut current := ByteArray.empty
  for byte in bytes.data do
    if byte == 47 then result := result.push current; current := ByteArray.empty
    else current := current.push byte
  return result.push current
private def driveRoot (result : Array ByteArray) : Bool :=
  match result.toList with
  | [a,b] => a.isEmpty && b.size == 2 && b.data[1]? == some 58
  | _ => false
private def uncRoot (result : Array ByteArray) : Bool :=
  result.size == 4 && (result[0]?.map ByteArray.isEmpty == some true) &&
    (result[1]?.map ByteArray.isEmpty == some true)

def normalizeUnix (bytes : ByteArray) : Normalized := Id.run do
  if bytes.data[0]? == some 47 && bytes.data[1]? == some 47 &&
      (bytes.data[2]? == some 46 || bytes.data[2]? == some 63) && bytes.data[3]? == some 47 then
    return .direct bytes
  let unc := bytes.data[0]? == some 47 && bytes.data[1]? == some 47
  if (String.fromUTF8? bytes).isSome && magicNames.any (asciiEq bytes) then
    return .direct ("//./".toUTF8 ++ bytes)
  let mut result : Array ByteArray := #[]
  for component in components bytes do
    if !unc && asciiEq component "NUL" then return .direct ("//./".toUTF8 ++ component)
    if component == "..".toUTF8 then
      if !driveRoot result && !uncRoot result then result := result.pop
    else
      let component := if !unc && component.size >= 2 && component.data[component.size-1]? == some 46 &&
          component.data[component.size-2]? != some 46 then component.extract 0 (component.size-1) else component
      result := result.push component
  if driveRoot result then result := result.push ByteArray.empty
  let joined := result.foldl (fun (pair : Bool × ByteArray) bytes =>
    (true,if pair.1 then pair.2.push 47 ++ bytes else bytes)) (false,ByteArray.empty)
  return .absolute joined.2
structure Hooks (S F H D Path HM Time E Kind : Type) where
  files : WindowsFiles.Hooks S F H D Path HM Time E
  strings : OsStrings.Hooks Provenance S Path Kind
  absolute : Path → M S (Except (IoError.HostError E) Path)
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error

def fullPath (h : Hooks S F H D P HM T E K) (path : P) : M S (Except (IoError.HostError E) P) := do
  if h.strings.hostWindows then return ← h.absolute path
  if !h.strings.hostUnix then throw (.unsupported "GetFullPathNameW requires Unix or Windows host")
  match normalizeUnix (h.strings.encodedBytes path) with
  | .direct bytes => return .ok (← lift (OsStrings.bytesToOsStr h.strings bytes))
  | .absolute bytes => h.absolute (← lift (OsStrings.bytesToOsStr h.strings bytes))

def getFullPath (h : Hooks S F H D P HM T E K) (name size buffer filepart : OpTy Provenance) : M S UInt32 := do
  h.files.noIsolation "`GetFullPathNameW`"
  let name ← h.files.handles.readPointer name
  let size ← h.files.handles.readU32 size
  let buffer ← h.files.handles.readPointer buffer
  let filepart ← h.files.handles.readPointer filepart
  if !(← h.files.handles.isNull filepart) then throw (.unsupported "GetFullPathNameW: non-null lpFilePart unsupported")
  let path ← h.files.readWidePath name
  match ← fullPath h path with
  | .error error => IoError.setLastError h.files.errors (.host error); return 0
  | .ok path =>
    let (success,length) ← OsStrings.writePath h.strings path buffer size.toUInt64 true
    if success && length == 0 then throw (.invalidProgram "Windows path length strict_sub underflow")
    let value := if success then length.toNat-1 else length.toNat
    if value >= 2^32 then throw (.invalidProgram "Windows path length exceeds u32")
    return UInt32.ofNat value
end Miri.Interpreter.WindowsPaths
