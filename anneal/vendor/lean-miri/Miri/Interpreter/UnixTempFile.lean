import Miri.Interpreter.UnixFsPaths

/-! Entire mkstemp source algorithm. Random choice uses actual machine RNG;
exclusive host creation and open flags are explicit typed effects. -/
namespace Miri.Interpreter.UnixTempFile
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive HostOptions where
  /-- read+write+create_new, mode0600 and host O_EXCL. -/
  | unix
  /-- read+write+create_new, share_mode(0). -/
  | windows
structure Hooks (S F D Path HM Time E Kind H : Type) where
  paths : UnixFsPaths.Hooks S F D Path HM Time E Kind
  /-- Actual uniform IndexedRandom.choose index from canonical machine RNG. -/
  choose : Nat → M S Nat
  openExclusive : Path → HostOptions → M S (Except (IoError.HostError E) H)
  insertFile : H → Bool → Bool → M S Int32
  /-- Explicit runner bound, independent of compiler TMP_MAX. -/
  attemptBudget : Nat
private def fail (h : Hooks S F D P HM T E K H) (name : String) : M S Int32 :=
  IoError.setErrnoAndReturnNeg1I32 h.paths.metadata.errors (.libc name)
private def substitutions : ByteArray := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".toUTF8
private def attempts (h : Hooks S F D P HM T E K H) (pointer : Pointer (Option Provenance))
    (template : ByteArray) (options : HostOptions) (fuel count : Nat) : M S Int32 := do
  match count,fuel with
  | 0,_ => fail h "EEXIST"
  | _+1,0 => throw (.resourceExhaustion "mkstemp attempt budget")
  | remaining+1,fuel+1 =>
    let mut suffix := ByteArray.empty
    for _ in [:6] do
      let index ← h.choose 62
      let some byte := substitutions.data[index]? | throw (.invalidProgram "machine random index outside substitutions")
      suffix := suffix.push byte
    let template := template.extract 0 (template.size-6) ++ suffix
    h.paths.writeBytes pointer template
    let path ← match OsStrings.bytesToOsStr h.paths.strings template with
      | .ok path => pure path
      | .error error => throw error
    match ← h.openExclusive path options with
    | .ok file => h.insertFile file true true
    | .error error =>
      if error.kind == .AlreadyExists then attempts h pointer template options fuel remaining
      else IoError.setErrnoAndReturnNeg1I32 h.paths.metadata.errors (.host error)

def mkstemp (h : Hooks S F D P HM T E K H) (template : OpTy Provenance) : M S Int32 := do
  if h.paths.metadata.errors.family != .unix then throw (.invalidProgram "mkstemp requires Unix target")
  let maximum ← h.paths.metadata.libcU32 "TMP_MAX"
  let pointer ← h.paths.metadata.readPointer template
  let bytes ← h.paths.strings.readCString pointer
  if ← h.paths.metadata.isolationReject "`mkstemp`" then return ← fail h "EACCES"
  if bytes.extract (bytes.size-6) bytes.size != "XXXXXX".toUTF8 then return ← fail h "EINVAL"
  let options ← if h.paths.metadata.hostUnix then pure HostOptions.unix
    else if h.paths.metadata.hostWindows then pure .windows
    else throw (.unsupported "mkstemp unsupported on host OS")
  attempts h pointer bytes options h.attemptBudget maximum.toNat
end Miri.Interpreter.UnixTempFile
