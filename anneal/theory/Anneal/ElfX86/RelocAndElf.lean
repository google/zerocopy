-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Anneal.ElfX86.PrefixDecode

public section
namespace Anneal.ElfX86

/-!
# Computable ELF64 Relocation & Read-Only `.rodata` Binding
(`Anneal.ElfX86.RelocAndElf`)

Pure Pass-1 (`0` `._unsafe_rec`, `0` `partial`, at most `[propext]` axioms on
theorems)
ELF64 little-endian `ET_REL` `EM_X86_64` parser and relocation/hygiene
validator:

- **Complete ELF64 header identity validation (`parseElf64Header?`):** enforces
  `\x7fELF`, `ELFCLASS64`, `ELFDATA2LSB`, `EI_VERSION = 1`, `EI_OSABI ∈ {0,3}`,
  `EI_ABIVERSION = 0`, zero `EI_PAD[9..15]`, `ET_REL`, `EM_X86_64`,
  `e_version = 1`, exact `e_ehsize = 64`, exact `e_shentsize = 64`,
  `0 < e_shnum`, `e_shstrndx < e_shnum`, and in-bounds section header table.
- **Whole-object raw-byte parser (`parseElf64Object?`):** derives the complete
  section table from `e_shoff`/`e_shnum`/`e_shstrndx` (requiring an all-zero
  `SHT_NULL` entry at index `0` and resolving every section name from raw
  `.shstrtab`), the unique `SHT_SYMTAB` (resolving symbol names from its linked
  `SHT_STRTAB`), and every `SHT_RELA` section across the object (rejecting
  every section type outside `sectionTypeIsKnown`, including `SHT_CREL`,
  `SHT_DYNSYM`, `SHT_REL`, and `SHT_RELR`, and duplicate `SHT_SYMTAB`).
- **Raw-object-bound public gates:** `objectHasNoForbiddenElfFeatures`,
  `resolvePc32RodataReloc`, `extractFuncPcRelRelocs?`, `funcTextBytes?`, and
  `decodeFuncFromElf?` consume ONLY raw object bytes `bs : List UInt8` via
  `parseElf64Object? bs` (validating that `textSecIdx` is a non-COMDAT,
  uncompressed executable `PROGBITS` code section with
  `funcOff + funcSize ≤ shSize`, and running `resolvePc32RodataReloc` on every
  decoded `.ripRel` operand), preventing any omitted `.init_array`,
  `STT_GNU_IFUNC`, `R_X86_64_IRELATIVE`, or caller `(bytes, relocs)` decoupling
  bypass.
- **Read-only `.rodata` & `SHF_MERGE` safety:** enforces `R_X86_64_PC32`,
  `r_sym ≠ 0` (`STN_UNDEF`), `0 < st_shndx < 0xFF00` (rejecting `SHN_UNDEF`,
  `SHN_ABS`, `SHN_COMMON`, `SHN_XINDEX`), `STB_LOCAL`, `SHF_WRITE = 0`,
  `SHF_ALLOC = 1`, `SHF_EXECINSTR = 0`, `SHF_GROUP = 0`, `SHF_COMPRESSED = 0`,
  `SHF_TLS = 0`, `SHF_STRINGS = 0`, `0 ≤ effOff`,
  `effOff + accessBytes ≤ shSize`, rejects `STT_SECTION` anchors into
  `SHF_MERGE` sections, and enforces single-entry `SHF_MERGE` bounds anchored
  to `sym.stValue`.
-/

/-! ## 1. Pure Computable Little-Endian Byte & String-Table Parsers -/

/-- Drop `8 * q` bytes in `q` `@Nat.rec` steps. -/
@[expose] def fastDropBytes8 (q : Nat) (bs : List UInt8) : List UInt8 :=
  @Nat.rec (fun _ => List UInt8 → List UInt8)
    (fun xs => xs)
    (fun _ ih xs =>
      match xs with
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => ih rest
      | _ => [])
    q bs

/-- Drop 8 bytes per step (`@Nat.rec` on `n / 8`, then `n % 8`) so kernel
reduction stays shallow on multi-hundred-byte ELF64 images. -/
@[expose] def fastDropBytes (n : Nat) (bs : List UInt8) : List UInt8 :=
  listDrop (Nat.mod n 8) (fastDropBytes8 (Nat.div n 8) bs)

/-- True iff `bs` has at least `n` bytes (runs in `O(n / 8)` steps without
walking past byte `n`). -/
@[expose] def bytesLenAtLeast (n : Nat) (bs : List UInt8) : Bool :=
  if Nat.beq n 0 then true
  else
    match fastDropBytes (n - 1) bs with
    | _ :: _ => true
    | [] => false

/-- Bounds-checked byte slice `[off, off + len)`. Returns `none` if out of
bounds. -/
@[expose] def sliceBytes? (bs : List UInt8) (off len : Nat) :
    Option (List UInt8) :=
  if bytesLenAtLeast (off + len) bs then
    some (listTake len (fastDropBytes off bs))
  else none

/-- Read a single byte at offset `off` using 8-byte chunked drop. -/
@[expose] def readU8At? (bs : List UInt8) (off : Nat) : Option UInt8 :=
  match fastDropBytes off bs with
  | b :: _ => some b
  | [] => none

/-- Read a 16-bit little-endian unsigned integer at byte offset `off`. -/
@[expose] def readU16Le? (bs : List UInt8) (off : Nat) : Option Nat :=
  match fastDropBytes off bs with
  | b0 :: b1 :: _ => some (le16Nat b0 b1)
  | _ => none

/-- Read a 32-bit little-endian unsigned integer at byte offset `off`. -/
@[expose] def readU32Le? (bs : List UInt8) (off : Nat) : Option Nat :=
  match fastDropBytes off bs with
  | b0 :: b1 :: b2 :: b3 :: _ => some (le32Nat b0 b1 b2 b3)
  | _ => none

/-- Read a 64-bit little-endian unsigned integer at byte offset `off`. -/
@[expose] def readU64Le? (bs : List UInt8) (off : Nat) : Option Nat :=
  match fastDropBytes off bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
    some (le64Nat b0 b1 b2 b3 b4 b5 b6 b7)
  | _ => none

/-- Read a 64-bit little-endian signed integer (`Elf64_Sxword`) at `off`. -/
@[expose] def readI64Le? (bs : List UInt8) (off : Nat) : Option Int :=
  match readU64Le? bs off with
  | none => none
  | some u => some (sext64 u)

/-- Bounded `@Nat.rec` NUL-terminated byte reader (fails closed if NUL is not
encountered before EOF or fuel exhaustion). -/
@[expose] def readNullTermCharsAux (fuel : Nat) (bs : List UInt8) :
    Option (List Char) :=
  @Nat.rec (fun _ => List UInt8 → Option (List Char))
    (fun _ => none)
    (fun _ ih rem =>
      match rem with
      | [] => none
      | b :: rest =>
        if Nat.beq b.toNat 0 then some []
        else
          match ih rest with
          | none => none
          | some cs => some (Char.ofNat b.toNat :: cs))
    fuel bs

/-- Parse a NUL-terminated ASCII string from string-table bytes `strtab` at
offset `off`. Returns `none` on out-of-bounds or missing NUL terminator. -/
@[expose] def readNullTermString? (strtab : List UInt8) (off : Nat) :
    Option String :=
  match fastDropBytes off strtab with
  | [] => none
  | tail =>
    match readNullTermCharsAux (tail.length + 1) tail with
    | none => none
    | some cs => some (String.ofList cs)

/-- Bounded `@Nat.rec` byte-list prefix test (`0` `._unsafe_rec`). -/
@[expose] def bytesStartsWithAux (fuel : Nat) (s pfx : List UInt8) : Bool :=
  @Nat.rec (fun _ => List UInt8 → List UInt8 → Bool)
    (fun _ ps =>
      match ps with
      | [] => true
      | _ :: _ => false)
    (fun _ ih xs ps =>
      match ps with
      | [] => true
      | p :: pr =>
        match xs with
        | [] => false
        | x :: xr => Nat.beq x.toNat p.toNat && ih xr pr)
    fuel s pfx

/-- Pure Pass-1 string prefix test (`0` `._unsafe_rec`). -/
@[expose] def stringStartsWith (s pfx : String) : Bool :=
  let sb := s.toByteArray.data.toList
  let pb := pfx.toByteArray.data.toList
  bytesStartsWithAux pb.length sb pb

/-! ## 2. ELF64 Constants, Structures, & Raw-Object Parser -/

@[expose] def elfClass64 : Nat := 2
@[expose] def elfData2Lsb : Nat := 1
@[expose] def evCurrent : Nat := 1
@[expose] def elfOsAbiSysv : Nat := 0
@[expose] def elfOsAbiGnu : Nat := 3
@[expose] def etRel : Nat := 1
@[expose] def emX86_64 : Nat := 62
@[expose] def elf64Ehsize : Nat := 64
@[expose] def elf64Shentsize : Nat := 64
@[expose] def elf64SymentSize : Nat := 24
@[expose] def elf64RelaEntSize : Nat := 24
@[expose] def shnUndef : Nat := 0
@[expose] def shnLoreserve : Nat := 0xFF00
@[expose] def stnUndef : Nat := 0

@[expose] def rX86_64_64 : Nat := 1
@[expose] def rX86_64_PC32 : Nat := 2
@[expose] def rX86_64_PLT32 : Nat := 4
@[expose] def rX86_64_32S : Nat := 11
@[expose] def rX86_64_TLSGD : Nat := 19
@[expose] def rX86_64_TLSLD : Nat := 20
@[expose] def rX86_64_GOTTPOFF : Nat := 22
@[expose] def rX86_64_IRelative : Nat := 37
@[expose] def rX86_64_GOTPCRELX : Nat := 41
@[expose] def rX86_64_REX_GOTPCRELX : Nat := 42

@[expose] def shfWrite : Nat := 1
@[expose] def shfAlloc : Nat := 2
@[expose] def shfExecInstr : Nat := 4
@[expose] def shfMerge : Nat := 16
@[expose] def shfStrings : Nat := 32
@[expose] def shfGroup : Nat := 512
@[expose] def shfTls : Nat := 1024
@[expose] def shfCompressed : Nat := 2048
@[expose] def shfExclude : Nat := 0x80000000

@[expose] def shtNull : Nat := 0
@[expose] def shtProgbits : Nat := 1
@[expose] def shtSymtab : Nat := 2
@[expose] def shtStrtab : Nat := 3
@[expose] def shtRela : Nat := 4
@[expose] def shtDynamic : Nat := 6
@[expose] def shtNobits : Nat := 8
@[expose] def shtRel : Nat := 9
@[expose] def shtDynsym : Nat := 11
@[expose] def shtInitArray : Nat := 14
@[expose] def shtFiniArray : Nat := 15
@[expose] def shtPreinitArray : Nat := 16
@[expose] def shtSymtabShndx : Nat := 18
@[expose] def shtRelr : Nat := 19
@[expose] def shtNote : Nat := 7
@[expose] def shtGroup : Nat := 17
@[expose] def shtLlvmAddrsig : Nat := 0x6FFF4C03
@[expose] def shtX8664Unwind : Nat := 0x70000001
@[expose] def shtCrel : Nat := 0x40000014

@[expose] def stbLocal : Nat := 0
@[expose] def stbGlobal : Nat := 1
@[expose] def stbWeak : Nat := 2

@[expose] def sttSection : Nat := 3
@[expose] def sttGnuIfunc : Nat := 10

/-- Parsed ELF64 little-endian `ET_REL` `EM_X86_64` file header. -/
structure Elf64Header where
  eType : Nat
  eMachine : Nat
  eVersion : Nat
  eEhsize : Nat
  eShoff : Nat
  eShentsize : Nat
  eShnum : Nat
  eShstrndx : Nat

/-- Parsed ELF64 section header. -/
structure Elf64SectionHdr where
  name : String
  shType : Nat
  shFlags : Nat
  shOffset : Nat
  shSize : Nat
  shLink : Nat
  shInfo : Nat
  shEntsize : Nat

/-- Parsed ELF64 symbol table entry. -/
structure Elf64Sym where
  name : String
  stType : Nat
  stBind : Nat
  stShndx : Nat
  stValue : Nat
  stSize : Nat

/-- Parsed ELF64 explicit-addend relocation (`Elf64_Rela`). -/
structure Elf64Rela where
  rOffset : Nat
  rSymIdx : Nat
  rType : Nat
  rAddend : Int

/-- Complete parsed ELF64 `ET_REL` object inventory derived directly from raw
object bytes `rawBytes` via `parseElf64Object?`. -/
structure ParsedElf64Object where
  rawBytes : List UInt8
  header : Elf64Header
  sections : List Elf64SectionHdr
  syms : List Elf64Sym
  relaSections : List (Nat × Elf64SectionHdr × List Elf64Rela)
  allRelas : List Elf64Rela

/-- Validated `.rodata` target produced by `resolvePc32RodataReloc`. -/
structure ResolvedRodataRef where
  secIdx : Nat
  byteOff : Nat
  accessBytes : Nat

@[expose] def ResolvedRodataRef.beq (a b : ResolvedRodataRef) : Bool :=
  Nat.beq a.secIdx b.secIdx && Nat.beq a.byteOff b.byteOff &&
  Nat.beq a.accessBytes b.accessBytes

/-- Sequential byte-stream readers returning `(value, rest)` so ELF64 table
parsers walk `bs` once without repeated `fastDropBytes` from offset `0`. -/
@[expose] def readU8Step? (bs : List UInt8) : Option (UInt8 × List UInt8) :=
  match bs with
  | b :: rest => some (b, rest)
  | [] => none

@[expose] def readU16Step? (bs : List UInt8) : Option (Nat × List UInt8) :=
  match bs with
  | b0 :: b1 :: rest => some (le16Nat b0 b1, rest)
  | _ => none

@[expose] def readU32Step? (bs : List UInt8) : Option (Nat × List UInt8) :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest => some (le32Nat b0 b1 b2 b3, rest)
  | _ => none

@[expose] def readU64Step? (bs : List UInt8) : Option (Nat × List UInt8) :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    some (le64Nat b0 b1 b2 b3 b4 b5 b6 b7, rest)
  | _ => none

@[expose] def skip4Step? (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | _ :: _ :: _ :: _ :: rest => some rest
  | _ => none

@[expose] def skip8Step? (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => some rest
  | _ => none

@[expose] def isZero4Step? (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest =>
    if Nat.beq b0.toNat 0 && Nat.beq b1.toNat 0 &&
       Nat.beq b2.toNat 0 && Nat.beq b3.toNat 0 then
      some rest
    else none
  | _ => none

@[expose] def isZero8Step? (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    if Nat.beq b0.toNat 0 && Nat.beq b1.toNat 0 &&
       Nat.beq b2.toNat 0 && Nat.beq b3.toNat 0 &&
       Nat.beq b4.toNat 0 && Nat.beq b5.toNat 0 &&
       Nat.beq b6.toNat 0 && Nat.beq b7.toNat 0 then
      some rest
    else none
  | _ => none

/-- True iff `bs` begins with 64 all-zero bytes (exact `SHT_NULL` entry). -/
@[expose] def bytesPrefixAllZero64 (bs : List UInt8) : Bool :=
  match isZero8Step? bs with
  | none => false
  | some r1 => match isZero8Step? r1 with
    | none => false
    | some r2 => match isZero8Step? r2 with
      | none => false
      | some r3 => match isZero8Step? r3 with
        | none => false
        | some r4 => match isZero8Step? r4 with
          | none => false
          | some r5 => match isZero8Step? r5 with
            | none => false
            | some r6 => match isZero8Step? r6 with
              | none => false
              | some r7 => (isZero8Step? r7).isSome

/-- Parse and validate the complete ELF64 LE `ET_REL` `EM_X86_64` header
identity in a single sequential pass: `\x7fELF`, `ELFCLASS64`, `ELFDATA2LSB`,
`EI_VERSION = 1`, `EI_OSABI ∈ {0, 3}`, `EI_ABIVERSION = 0`, zero
`EI_PAD[9..15]`, `ET_REL`, `EM_X86_64`, `e_version = 1`, zero `e_entry` /
`e_phoff` / `e_flags` / `e_phentsize` / `e_phnum`, exact `e_ehsize = 64`,
exact `e_shentsize = 64`, `0 < e_shnum < 0xFF00`, `e_shstrndx < e_shnum`, and
in-bounds section header table. -/
@[expose] def parseElf64Header? (bs : List UInt8) : Option Elf64Header :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest8 =>
    let idLoOk :=
      Nat.beq b0.toNat 0x7F && Nat.beq b1.toNat 0x45 &&
      Nat.beq b2.toNat 0x4C && Nat.beq b3.toNat 0x46 &&
      Nat.beq b4.toNat elfClass64 && Nat.beq b5.toNat elfData2Lsb &&
      Nat.beq b6.toNat evCurrent &&
      (Nat.beq b7.toNat elfOsAbiSysv || Nat.beq b7.toNat elfOsAbiGnu)
    if !idLoOk then none
    else
      match isZero8Step? rest8 with
      | none => none
      | some r16 =>
        match readU16Step? r16 with
        | none => none
        | some (eTy, r18) =>
          match readU16Step? r18 with
          | none => none
          | some (eMach, r20) =>
            match readU32Step? r20 with
            | none => none
            | some (eVer, r24) =>
              match isZero8Step? r24 with
              | none => none
              | some r32 =>
                match isZero8Step? r32 with
                | none => none
                | some r40 =>
                  match readU64Step? r40 with
                  | none => none
                  | some (shoff, r48) =>
                    match isZero4Step? r48 with
                    | none => none
                    | some r52 =>
                      match readU16Step? r52 with
                      | none => none
                      | some (ehsz, r54) =>
                        match isZero4Step? r54 with
                        | none => none
                        | some r58 =>
                          match readU16Step? r58 with
                          | none => none
                          | some (shent, r60) =>
                            match readU16Step? r60 with
                            | none => none
                            | some (shnum, r62) =>
                              match readU16Step? r62 with
                              | none => none
                              | some (shstr, _) =>
                                if Nat.beq eTy etRel &&
                                   Nat.beq eMach emX86_64 &&
                                   Nat.beq eVer evCurrent &&
                                   Nat.beq ehsz elf64Ehsize &&
                                   Nat.beq shent elf64Shentsize &&
                                   Nat.blt 0 shnum &&
                                   Nat.blt shnum shnLoreserve &&
                                   Nat.blt shstr shnum &&
                                   bytesLenAtLeast
                                     (shoff + shnum * elf64Shentsize) bs then
                                  some {
                                    eType := eTy
                                    eMachine := eMach
                                    eVersion := eVer
                                    eEhsize := ehsz
                                    eShoff := shoff
                                    eShentsize := shent
                                    eShnum := shnum
                                    eShstrndx := shstr
                                  }
                                else none
  | _ => none

/-- Parse a 64-byte `Elf64_Shdr` sequentially from the head of `tail` with
caller-supplied section name, returning `(sh, restAfter64)`. -/
@[expose] def parseElf64SectionHdrHeadWithName? (name : String)
    (tail : List UInt8) : Option (Elf64SectionHdr × List UInt8) :=
  match skip4Step? tail with
  | none => none
  | some r4 =>
    match readU32Step? r4 with
    | none => none
    | some (sTy, r8) =>
      match readU64Step? r8 with
      | none => none
      | some (sFlg, r16) =>
        match skip8Step? r16 with
        | none => none
        | some r24 =>
          match readU64Step? r24 with
          | none => none
          | some (sOff, r32) =>
            match readU64Step? r32 with
            | none => none
            | some (sSz, r40) =>
              match readU32Step? r40 with
              | none => none
              | some (sLnk, r44) =>
                match readU32Step? r44 with
                | none => none
                | some (sInf, r48) =>
                  match skip8Step? r48 with
                  | none => none
                  | some r56 =>
                    match readU64Step? r56 with
                    | none => none
                    | some (sEnt, r64) =>
                      some ({
                        name := name
                        shType := sTy
                        shFlags := sFlg
                        shOffset := sOff
                        shSize := sSz
                        shLink := sLnk
                        shInfo := sInf
                        shEntsize := sEnt
                      }, r64)

/-- Parse a 64-byte `Elf64_Shdr` sequentially from `tail`, resolving `sh_name`
directly from raw `.shstrtab` bytes, returning `(sh, restAfter64)`. -/
@[expose] def parseElf64SectionHdrHead? (shstrtab tail : List UInt8) :
    Option (Elf64SectionHdr × List UInt8) :=
  match readU32Step? tail with
  | none => none
  | some (nameOff, r4) =>
    match readNullTermString? shstrtab nameOff with
    | none => none
    | some name =>
      match readU32Step? r4 with
      | none => none
      | some (sTy, r8) =>
        match readU64Step? r8 with
        | none => none
        | some (sFlg, r16) =>
          match skip8Step? r16 with
          | none => none
          | some r24 =>
            match readU64Step? r24 with
            | none => none
            | some (sOff, r32) =>
              match readU64Step? r32 with
              | none => none
              | some (sSz, r40) =>
                match readU32Step? r40 with
                | none => none
                | some (sLnk, r44) =>
                  match readU32Step? r44 with
                  | none => none
                  | some (sInf, r48) =>
                    match skip8Step? r48 with
                    | none => none
                    | some r56 =>
                      match readU64Step? r56 with
                      | none => none
                      | some (sEnt, r64) =>
                        some ({
                          name := name
                          shType := sTy
                          shFlags := sFlg
                          shOffset := sOff
                          shSize := sSz
                          shLink := sLnk
                          shInfo := sInf
                          shEntsize := sEnt
                        }, r64)

/-- Parse a 64-byte `Elf64_Shdr` at byte offset `off` with caller-supplied
section name. -/
@[expose] def parseElf64SectionHdr? (name : String) (bs : List UInt8)
    (off : Nat) : Option Elf64SectionHdr :=
  match parseElf64SectionHdrHeadWithName? name (fastDropBytes off bs) with
  | some (sh, _) => some sh
  | none => none

/-- Parse a 64-byte `Elf64_Shdr` at byte offset `off`, resolving `sh_name`
directly from raw `.shstrtab` bytes instead of trusting caller strings. -/
@[expose] def parseElf64SectionHdrFromTable? (bs shstrtab : List UInt8)
    (off : Nat) : Option Elf64SectionHdr :=
  match parseElf64SectionHdrHead? shstrtab (fastDropBytes off bs) with
  | some (sh, _) => some sh
  | none => none

/-- Parse a 24-byte `Elf64_Sym` sequentially from `tail`, resolving `st_name`
directly from raw `.strtab` bytes, returning `(sym, restAfter24)`. -/
@[expose] def parseElf64SymHead? (strtab tail : List UInt8) :
    Option (Elf64Sym × List UInt8) :=
  match readU32Step? tail with
  | none => none
  | some (nameOff, r4) =>
    match readU8Step? r4 with
    | none => none
    | some (infoB, r5) =>
      match readU8Step? r5 with
      | none => none
      | some (_, r6) =>
        match readU16Step? r6 with
        | none => none
        | some (shndx, r8) =>
          match readU64Step? r8 with
          | none => none
          | some (val, r16) =>
            match readU64Step? r16 with
            | none => none
            | some (sz, r24) =>
              match readNullTermString? strtab nameOff with
              | none => none
              | some name =>
                some ({
                  name := name
                  stType := Nat.mod infoB.toNat 16
                  stBind := Nat.div infoB.toNat 16
                  stShndx := shndx
                  stValue := val
                  stSize := sz
                }, r24)

/-- Parse a 24-byte `Elf64_Sym` at byte offset `off`, resolving `st_name`
directly from raw `.strtab` bytes. -/
@[expose] def parseElf64SymFromTable? (bs strtab : List UInt8)
    (off : Nat) : Option Elf64Sym :=
  match parseElf64SymHead? strtab (fastDropBytes off bs) with
  | some (sym, _) => some sym
  | none => none

/-- Parse a 24-byte `Elf64_Rela` sequentially from `tail`, returning
`(rela, restAfter24)`. -/
@[expose] def parseElf64RelaHead? (tail : List UInt8) :
    Option (Elf64Rela × List UInt8) :=
  match readU64Step? tail with
  | none => none
  | some (rOff, r8) =>
    match readU64Step? r8 with
    | none => none
    | some (rInfo, r16) =>
      match readU64Step? r16 with
      | none => none
      | some (rAddRaw, r24) =>
        some ({
          rOffset := rOff
          rSymIdx := Nat.div rInfo 4294967296
          rType := Nat.mod rInfo 4294967296
          rAddend := sext64 rAddRaw
        }, r24)

/-- Parse a 24-byte `Elf64_Rela` at byte offset `off`. -/
@[expose] def parseElf64Rela? (bs : List UInt8) (off : Nat) :
    Option Elf64Rela :=
  match parseElf64RelaHead? (fastDropBytes off bs) with
  | some (rl, _) => some rl
  | none => none

/-- Bounded `@Nat.rec` single-pass parser reading `rem` consecutive 64-byte
`Elf64_Shdr` entries starting at `cur` (zero repeated `fastDropBytes`). -/
@[expose] def parseAllSectionHdrsAux (bs shstrtab : List UInt8)
    (rem : Nat) (cur : List UInt8) : Option (List Elf64SectionHdr) :=
  @Nat.rec (fun _ => List UInt8 → Option (List Elf64SectionHdr))
    (fun _ => some [])
    (fun _ ih tail =>
      match parseElf64SectionHdrHead? shstrtab tail with
      | none => none
      | some (sh, rest) =>
        if !Nat.beq sh.shType shtNobits &&
           !bytesLenAtLeast (sh.shOffset + sh.shSize) bs then none
        else
          match ih rest with
          | none => none
          | some tl => some (sh :: tl))
    rem cur

/-- Bounded `@Nat.rec` single-pass parser reading `rem` consecutive 24-byte
`Elf64_Sym` entries from `cur`. -/
@[expose] def parseAllSymsAux (strtab : List UInt8)
    (rem : Nat) (cur : List UInt8) : Option (List Elf64Sym) :=
  @Nat.rec (fun _ => List UInt8 → Option (List Elf64Sym))
    (fun _ => some [])
    (fun _ ih tail =>
      match parseElf64SymHead? strtab tail with
      | none => none
      | some (sym, rest) =>
        match ih rest with
        | none => none
        | some tl => some (sym :: tl))
    rem cur

/-- Bounded `@Nat.rec` single-pass parser reading `rem` consecutive 24-byte
`Elf64_Rela` entries from `cur`. -/
@[expose] def parseAllRelasAux (rem : Nat) (cur : List UInt8) :
    Option (List Elf64Rela) :=
  @Nat.rec (fun _ => List UInt8 → Option (List Elf64Rela))
    (fun _ => some [])
    (fun _ ih tail =>
      match parseElf64RelaHead? tail with
      | none => none
      | some (rl, rest) =>
        match ih rest with
        | none => none
        | some tl => some (rl :: tl))
    rem cur

/-- True iff `SHF_WRITE` (bit 0) is set on `sec`. -/
@[expose] def sectionIsWritable (sec : Elf64SectionHdr) : Bool :=
  Nat.beq (Nat.mod sec.shFlags 2) 1

/-- True iff `SHF_ALLOC` (bit 1) is set on `sec`. -/
@[expose] def sectionIsAlloc (sec : Elf64SectionHdr) : Bool :=
  Nat.beq (Nat.mod (Nat.div sec.shFlags 2) 2) 1

/-- True iff `SHF_EXECINSTR` (bit 2) is set on `sec`. -/
@[expose] def sectionIsExec (sec : Elf64SectionHdr) : Bool :=
  Nat.beq (Nat.mod (Nat.div sec.shFlags 4) 2) 1

/-- True iff `SHF_MERGE` (`0x10`) is set on `sec`. -/
@[expose] def sectionHasMerge (sec : Elf64SectionHdr) : Bool :=
  Nat.beq (Nat.mod (Nat.div sec.shFlags 16) 2) 1

/-- True iff `SHF_STRINGS` (`0x20`) is set on `sec`. -/
@[expose] def sectionHasStrings (sec : Elf64SectionHdr) : Bool :=
  Nat.beq (Nat.mod (Nat.div sec.shFlags 32) 2) 1

/-- True iff `SHF_GROUP` (`0x200`, COMDAT group) is set on `sec`. -/
@[expose] def sectionHasGroup (sec : Elf64SectionHdr) : Bool :=
  Nat.beq (Nat.mod (Nat.div sec.shFlags 512) 2) 1

/-- True iff `SHF_TLS` (`0x400`, thread-local storage) is set on `sec`. -/
@[expose] def sectionHasTls (sec : Elf64SectionHdr) : Bool :=
  Nat.beq (Nat.mod (Nat.div sec.shFlags 1024) 2) 1

/-- True iff `SHF_COMPRESSED` (`0x800`) is set on `sec`. -/
@[expose] def sectionHasCompressed (sec : Elf64SectionHdr) : Bool :=
  Nat.beq (Nat.mod (Nat.div sec.shFlags 2048) 2) 1

/-- True iff `SHF_EXCLUDE` (`0x80000000`) is set on `sec`. -/
@[expose] def sectionHasExclude (sec : Elf64SectionHdr) : Bool :=
  Nat.beq (Nat.mod (Nat.div sec.shFlags shfExclude) 2) 1

/-- True iff `shndx` names a regular defined section (`0 < shndx < 0xFF00`),
excluding `SHN_UNDEF` (`0`) and reserved indices (`SHN_ABS`, `SHN_COMMON`,
`SHN_XINDEX`, etc. at `≥ 0xFF00`). -/
@[expose] def shndxIsDefinedRegular (shndx : Nat) : Bool :=
  Nat.blt shnUndef shndx && Nat.blt shndx shnLoreserve

/-- Metadata table sections consumed by `parseElf64Object?` (`.shstrtab`,
`SHT_SYMTAB`, linked `SHT_STRTAB`) must be uncompressed (`!SHF_COMPRESSED`),
non-COMDAT (`!SHF_GROUP`), non-writable, non-executable, non-TLS, and
non-excluded (`!SHF_EXCLUDE`). -/
@[expose] def sectionMetaFlagsOk (sec : Elf64SectionHdr) : Bool :=
  !sectionHasCompressed sec &&
  !sectionHasGroup sec &&
  !sectionIsWritable sec &&
  !sectionIsExec sec &&
  !sectionHasTls sec &&
  !sectionHasExclude sec

/-- Every `SHT_RELA` section parsed by `parseAllRelaSections?` must be
uncompressed (`!SHF_COMPRESSED`) and free of writable, executable, TLS, or
exclude flags (allowing `SHF_INFO_LINK`, and permitting `SHF_GROUP` on
unrelated COMDAT functions while rejecting `SHF_GROUP` on the target
`textSecIdx` RELA section). -/
@[expose] def relaSectionFlagsOk (sec : Elf64SectionHdr) : Bool :=
  !sectionHasCompressed sec &&
  !sectionIsWritable sec &&
  !sectionIsExec sec &&
  !sectionHasTls sec &&
  !sectionHasExclude sec

/-- Find the unique `SHT_SYMTAB` section in `secs` together with its 0-based
section index (`some none` if absent, `some (some (idx, s))` if unique, `none`
if duplicate `SHT_SYMTAB` exists). -/
@[expose] def findUniqueSymtabWithIdx? (secs : List Elf64SectionHdr) :
    Option (Option (Nat × Elf64SectionHdr)) :=
  match List.foldr
    (fun sec acc =>
      match acc with
      | none => none
      | some (idx, found) =>
        if Nat.beq sec.shType shtSymtab then
          match found with
          | none => some (idx - 1, some (idx, sec))
          | some _ => none
        else some (idx - 1, found))
    (some (secs.length - 1, none)) secs with
  | none => none
  | some (_, found) => some found

/-- Find the unique `SHT_SYMTAB` section in `secs` (`some none` if absent,
`some (some s)` if unique, `none` if duplicate `SHT_SYMTAB` exists). -/
@[expose] def findUniqueSymtab? (secs : List Elf64SectionHdr) :
    Option (Option Elf64SectionHdr) :=
  match findUniqueSymtabWithIdx? secs with
  | none => none
  | some none => some none
  | some (some (_, sec)) => some (some sec)

/-- Parse all symbols from the unique `SHT_SYMTAB` (if present), rejecting
compressed or malformed metadata flags on both `SHT_SYMTAB` and its linked
`SHT_STRTAB` section. -/
@[expose] def parseObjectSymtab? (bs : List UInt8)
    (secs : List Elf64SectionHdr) : Option (List Elf64Sym) :=
  match findUniqueSymtab? secs with
  | none => none
  | some none => some []
  | some (some symSec) =>
    if !sectionMetaFlagsOk symSec ||
       !Nat.beq symSec.shEntsize elf64SymentSize ||
       !Nat.beq (Nat.mod symSec.shSize elf64SymentSize) 0 ||
       !bytesLenAtLeast (symSec.shOffset + symSec.shSize) bs then none
    else
      match listGet? secs symSec.shLink with
      | none => none
      | some strSec =>
        if !Nat.beq strSec.shType shtStrtab ||
           !sectionMetaFlagsOk strSec then none
        else
          match sliceBytes? bs strSec.shOffset strSec.shSize with
          | none => none
          | some strtab =>
            let count := Nat.div symSec.shSize elf64SymentSize
            parseAllSymsAux strtab count (fastDropBytes symSec.shOffset bs)

/-- Parse EVERY `SHT_RELA` section in `secs`, preserving each section's 0-based
index. Fails closed if any `SHT_RELA` section is compressed/malformed, has an
out-of-range or reserved `shInfo`, or does not link (`shLink`) to the unique
`SHT_SYMTAB` section. -/
@[expose] def parseAllRelaSections? (bs : List UInt8)
    (secs : List Elf64SectionHdr) :
    Option (List (Nat × Elf64SectionHdr × List Elf64Rela)) :=
  match findUniqueSymtabWithIdx? secs with
  | none => none
  | some symOpt =>
    match List.foldr
      (fun sec acc =>
        match acc with
        | none => none
        | some (idx, out) =>
          if Nat.beq sec.shType shtRela then
            let linkOk := match symOpt with
              | some (stIdx, _) => Nat.beq sec.shLink stIdx
              | none => false
            if relaSectionFlagsOk sec &&
               linkOk &&
               shndxIsDefinedRegular sec.shInfo &&
               Nat.blt sec.shInfo secs.length &&
               Nat.beq sec.shEntsize elf64RelaEntSize &&
               Nat.beq (Nat.mod sec.shSize elf64RelaEntSize) 0 &&
               bytesLenAtLeast (sec.shOffset + sec.shSize) bs then
              let cnt := Nat.div sec.shSize elf64RelaEntSize
              match parseAllRelasAux cnt (fastDropBytes sec.shOffset bs) with
              | none => none
              | some rs => some (idx - 1, (idx, sec, rs) :: out)
            else none
          else some (idx - 1, out))
      (some (secs.length - 1, [])) secs with
    | none => none
    | some (_, out) => some out

/-- Concatenate every relocation across all parsed `SHT_RELA` sections. -/
@[expose] def collectAllRelas
    (relaSecs : List (Nat × Elf64SectionHdr × List Elf64Rela)) :
    List Elf64Rela :=
  List.foldr (fun entry acc => entry.2.2 ++ acc) [] relaSecs

/-- True iff `sec` is an all-zero `SHT_NULL` section header. -/
@[expose] def sectionHdrIsNull (sec : Elf64SectionHdr) : Bool :=
  (sec.name == "") &&
  Nat.beq sec.shType shtNull &&
  Nat.beq sec.shFlags 0 &&
  Nat.beq sec.shOffset 0 &&
  Nat.beq sec.shSize 0 &&
  Nat.beq sec.shLink 0 &&
  Nat.beq sec.shInfo 0 &&
  Nat.beq sec.shEntsize 0

/-- True iff `sec.shType` is on the explicit list of section types this parser
admits: `SHT_NULL`, `SHT_PROGBITS`, `SHT_SYMTAB`, `SHT_STRTAB`, `SHT_RELA`,
`SHT_NOBITS`, the initializer-array types (`SHT_INIT_ARRAY`, `SHT_FINI_ARRAY`,
`SHT_PREINIT_ARRAY`, which `sectionIsForbidden` then rejects), and the benign
non-relocation types that ordinary rustc/LLVM objects carry: `SHT_NOTE`,
`SHT_GROUP` (group-member code is still rejected through `SHF_GROUP`),
`SHT_LLVM_ADDRSIG`, and `SHT_X86_64_UNWIND` (`.eh_frame`, whose `SHT_RELA`
sections remain subject to the usual hygiene checks). Every other type,
including compact relocation tables (`SHT_CREL`, `0x40000014`), `SHT_REL`,
`SHT_RELR`, `SHT_DYNSYM`, `SHT_DYNAMIC`, `SHT_SYMTAB_SHNDX`, and every
unlisted OS-, processor-, or vendor-specific type, is unknown. -/
@[expose] def sectionTypeIsKnown (sec : Elf64SectionHdr) : Bool :=
  Nat.beq sec.shType shtNull ||
  Nat.beq sec.shType shtProgbits ||
  Nat.beq sec.shType shtSymtab ||
  Nat.beq sec.shType shtStrtab ||
  Nat.beq sec.shType shtRela ||
  Nat.beq sec.shType shtNobits ||
  Nat.beq sec.shType shtInitArray ||
  Nat.beq sec.shType shtFiniArray ||
  Nat.beq sec.shType shtPreinitArray ||
  Nat.beq sec.shType shtNote ||
  Nat.beq sec.shType shtGroup ||
  Nat.beq sec.shType shtLlvmAddrsig ||
  Nat.beq sec.shType shtX8664Unwind

/-- True iff `sec` has a section type outside `sectionTypeIsKnown`. Such
sections are rejected fail-closed, so no symbol or relocation table of an
unmodeled encoding (for example `SHT_CREL`, `SHT_REL`, `SHT_RELR`, or
`SHT_DYNSYM`) can carry hidden link-time effects past `parseElf64Object?`. -/
@[expose] def sectionIsUnparsedTableType (sec : Elf64SectionHdr) : Bool :=
  !sectionTypeIsKnown sec

/-- Parse a complete ELF64 `ET_REL` `EM_X86_64` object directly from raw bytes
`bs`: validates the full ELF64 header, rejects compressed or malformed
`.shstrtab`/`SHT_SYMTAB`/`SHT_STRTAB`/`SHT_RELA` sections, derives all `e_shnum`
sections in a single sequential pass over the section-header table with
`.shstrtab`-resolved names, requires `sections[0]` to be an all-zero 64-byte
`SHT_NULL` entry, rejects unparsed table types and duplicate `SHT_SYMTAB`,
parses the complete symbol table, and parses every `SHT_RELA` section into both
`relaSections` and `allRelas`. -/
@[expose] def parseElf64Object? (bs : List UInt8) :
    Option ParsedElf64Object :=
  match parseElf64Header? bs with
  | none => none
  | some hdr =>
    let shTable := fastDropBytes hdr.eShoff bs
    if !bytesPrefixAllZero64 shTable then none
    else
      match parseElf64SectionHdrHeadWithName? ".shstrtab"
          (fastDropBytes (hdr.eShstrndx * elf64Shentsize) shTable) with
      | none => none
      | some (shstrHdr, _) =>
        if !Nat.beq shstrHdr.shType shtStrtab ||
           !sectionMetaFlagsOk shstrHdr then none
        else
          match sliceBytes? bs shstrHdr.shOffset shstrHdr.shSize with
          | none => none
          | some shstrtab =>
            match parseAllSectionHdrsAux bs shstrtab hdr.eShnum shTable with
            | none => none
            | some secs =>
              match secs with
              | [] => none
              | s0 :: _ =>
                if !sectionHdrIsNull s0 ||
                   listAny sectionIsUnparsedTableType secs then none
                else
                  match parseObjectSymtab? bs secs with
                  | none => none
                  | some syms =>
                    match parseAllRelaSections? bs secs with
                    | none => none
                    | some relaSecs =>
                      some {
                        rawBytes := bs
                        header := hdr
                        sections := secs
                        syms := syms
                        relaSections := relaSecs
                        allRelas := collectAllRelas relaSecs
                      }

/-- Find the unique `SHT_RELA` section targeting `targetSecIdx`
(`shInfo == targetSecIdx`): returns `some none` if absent,
`some (some (rSec, relas))` if unique, and `none` (fail closed) if two or more
`SHT_RELA` sections target `targetSecIdx` (preventing a second RELA section
from hiding an `R_X86_64_32S` or other relocation from the 1-to-1 check). -/
@[expose] def findUniqueRelaForTarget?
    (relaSecs : List (Nat × Elf64SectionHdr × List Elf64Rela))
    (targetSecIdx : Nat) :
    Option (Option (Elf64SectionHdr × List Elf64Rela)) :=
  List.foldr
    (fun entry acc =>
      match acc with
      | none => none
      | some found =>
        if Nat.beq entry.2.1.shInfo targetSecIdx then
          match found with
          | none => some (some entry.2)
          | some _ => none
        else some found)
    (some none) relaSecs

/-- True iff any parsed `SHT_RELA` section in `relaSecs` targets `secIdx`
(`shInfo == secIdx`), meaning link-time relocations may overwrite bytes in
`secIdx`. -/
@[expose] def hasRelaTargetingSection
    (relaSecs : List (Nat × Elf64SectionHdr × List Elf64Rela))
    (secIdx : Nat) : Bool :=
  listAny (fun entry => Nat.beq entry.2.1.shInfo secIdx) relaSecs

/-! ## 3. Read-Only `.rodata`, `SHF_MERGE`, & Raw-Object-Bound Validators -/

/-- True iff `sec` is an allocated, non-writable, non-executable, non-COMDAT,
uncompressed, non-TLS, non-string, non-excluded `PROGBITS` read-only data
section. -/
@[expose] def sectionIsReadOnlyRodata (sec : Elf64SectionHdr) : Bool :=
  Nat.beq sec.shType shtProgbits &&
  !sectionIsWritable sec &&
  sectionIsAlloc sec &&
  !sectionIsExec sec &&
  !sectionHasGroup sec &&
  !sectionHasCompressed sec &&
  !sectionHasTls sec &&
  !sectionHasStrings sec &&
  !sectionHasExclude sec

/-- True iff `sec` is an allocated, executable, non-writable, non-COMDAT,
uncompressed, non-TLS, non-merge, non-string, non-excluded `PROGBITS` code
section (`SHT_PROGBITS`, `SHF_ALLOC | SHF_EXECINSTR`). -/
@[expose] def sectionIsExecText (sec : Elf64SectionHdr) : Bool :=
  Nat.beq sec.shType shtProgbits &&
  sectionIsAlloc sec &&
  sectionIsExec sec &&
  !sectionIsWritable sec &&
  !sectionHasGroup sec &&
  !sectionHasCompressed sec &&
  !sectionHasTls sec &&
  !sectionHasMerge sec &&
  !sectionHasStrings sec &&
  !sectionHasExclude sec

/-- True iff `sec` is a forbidden initializer/finalizer section
(`.init_array*`, `.fini_array*`, `.preinit_array*`, `.ctors*`, `.dtors*`,
`.init`, `.init.*`, `.fini`, `.fini.*`) or a `W+X` section. -/
@[expose] def sectionIsForbidden (sec : Elf64SectionHdr) : Bool :=
  Nat.beq sec.shType shtInitArray ||
  Nat.beq sec.shType shtFiniArray ||
  Nat.beq sec.shType shtPreinitArray ||
  stringStartsWith sec.name ".init_array" ||
  stringStartsWith sec.name ".fini_array" ||
  stringStartsWith sec.name ".preinit_array" ||
  stringStartsWith sec.name ".ctors" ||
  stringStartsWith sec.name ".dtors" ||
  (sec.name == ".init") ||
  stringStartsWith sec.name ".init." ||
  (sec.name == ".fini") ||
  stringStartsWith sec.name ".fini." ||
  (sectionIsWritable sec && sectionIsExec sec)

/-- True iff `sym` is a GNU indirect function (`STT_GNU_IFUNC = 10`). -/
@[expose] def symIsIfunc (sym : Elf64Sym) : Bool :=
  Nat.beq sym.stType sttGnuIfunc

/-- True iff `sym` is a section symbol (`STT_SECTION = 3`). -/
@[expose] def symIsSection (sym : Elf64Sym) : Bool :=
  Nat.beq sym.stType sttSection

/-- True iff `sym` has local binding (`STB_LOCAL = 0`, preventing global or
weak symbol interposition at link time). -/
@[expose] def symIsLocalBinding (sym : Elf64Sym) : Bool :=
  Nat.beq sym.stBind stbLocal

/-- True iff `r` is an `R_X86_64_IRELATIVE` (`type = 37`) relocation. -/
@[expose] def relaIsIRelative (r : Elf64Rela) : Bool :=
  Nat.beq r.rType rX86_64_IRelative

/-- Convert a non-negative `Int` to `Option Nat` (negative values return
`none`). -/
@[expose] def intToNat? (x : Int) : Option Nat :=
  match x with
  | Int.ofNat n => some n
  | Int.negSucc _ => none

/-- When `SHF_MERGE` is set on `sec`, reject `STT_SECTION` symbols as
relocation anchors (linkers rewrite `STT_SECTION` addends against section
starts, whereas per-entry symbols like `.LCPI*` anchor the deduplicated entry)
and verify that `[byteOff, byteOff + accessBytes)` lies strictly inside the
same `shEntsize`-byte mergeable entry as `sym.stValue`. -/
@[expose] def mergeEntryBoundsOk (sec : Elf64SectionHdr) (sym : Elf64Sym)
    (byteOff accessBytes : Nat) : Bool :=
  if !sectionHasMerge sec then true
  else
    !symIsSection sym &&
    Nat.blt 0 sec.shEntsize &&
    Nat.blt 0 accessBytes &&
    Nat.ble accessBytes sec.shEntsize &&
    Nat.beq (Nat.div sym.stValue sec.shEntsize)
      (Nat.div byteOff sec.shEntsize) &&
    Nat.beq (Nat.div byteOff sec.shEntsize)
      (Nat.div (byteOff + accessBytes - 1) sec.shEntsize)

/-- Explicit non-relaxable executable-section relocation allowlist
(`R_X86_64_PC32` only, matching 100% of relocations in deployed AVX2 `.rcgu.o`
kernels): rejects all relaxable (`REX_GOTPCRELX`/`GOTPCRELX`/`GOTTPOFF`), TLS
(`TLSGD`/`TLSLD`), `R_X86_64_32S`, and unmodeled relocation types. -/
@[expose] def relaTypeAllowedInExecSec (r : Elf64Rela) : Bool :=
  Nat.beq r.rType rX86_64_PC32

/-- Exact `(beforeBytes, afterBytes)` linker write footprint for admitted
executable-section relocation types: `some (0, 4)` for `R_X86_64_PC32`, and
`none` (fail closed) for every other relocation type so no backward or
`>8`-byte linker-relaxation rewrite can escape overlap checks. -/
@[expose] def execRelaWriteFootprint? (r : Elf64Rela) : Option (Nat × Nat) :=
  if relaTypeAllowedInExecSec r then some (0, 4) else none

/-- Exact `(beforeBytes, afterBytes)` linker write footprint
`[rOffset - beforeBytes, rOffset + afterBytes)` for the non-relaxable
relocation types admitted in sibling executable sections, or `none` (fail
closed) for every other type:
- `R_X86_64_PC32`, `R_X86_64_PLT32`: `[o, o + 4)`;
- `R_X86_64_64`: `[o, o + 8)`.

Relaxable and TLS types (`GOTPCRELX`, `REX_GOTPCRELX`, `GOTTPOFF`, `TLSGD`,
`TLSLD`, and any unlisted type) are excluded because their linker rewrite
footprint depends on the surrounding section bytes and on which linker runs
(e.g. lld/mold rewrite TLSGD's MOVABS form over `[o - 3, o + 19)`), so no
fixed per-type footprint bounds it. -/
@[expose] def execRelaSiblingFootprint? (r : Elf64Rela) :
    Option (Nat × Nat) :=
  if Nat.beq r.rType rX86_64_PC32 || Nat.beq r.rType rX86_64_PLT32 then
    some (0, 4)
  else if Nat.beq r.rType rX86_64_64 then some (0, 8)
  else none

/-- Section-bounds check for a relocation targeting an executable section of
byte size `secSize`: `R_X86_64_PC32` requires `rOffset + 4 ≤ secSize`, and
every other type requires its exact `execRelaSiblingFootprint?` write
footprint `[rOffset - before, rOffset + after)` to lie within `[0, secSize)`.
Relaxable, TLS, and unlisted relocation types are rejected (no fallback
envelope). -/
@[expose] def execRelaFootprintInOwnSec (secSize : Nat)
    (r : Elf64Rela) : Bool :=
  if relaTypeAllowedInExecSec r then
    Nat.ble (r.rOffset + 4) secSize
  else
    match execRelaSiblingFootprint? r with
    | none => false
    | some (before, after) =>
      Nat.ble before r.rOffset && Nat.ble (r.rOffset + after) secSize

/-- True iff every `SHT_RELA` section in `obj` targets a valid section header
`obj.sections[shInfo]` and, whenever that target section is executable
(`sectionIsExec`), every relocation satisfies `execRelaFootprintInOwnSec`
against that section's own `shSize` (preventing any sibling relocation or
linker relaxation from writing past its section into a certified section). -/
@[expose] def allExecRelaFootprintsInBounds (obj : ParsedElf64Object) : Bool :=
  listAll
    (fun entry =>
      match listGet? obj.sections entry.2.1.shInfo with
      | none => false
      | some targetSec =>
        if sectionIsExec targetSec then
          listAll (execRelaFootprintInOwnSec targetSec.shSize) entry.2.2
        else true)
    obj.relaSections

/-- True iff every `SHT_RELA` section in `obj` targets a valid section header
`obj.sections[shInfo]` such that:
- if `shInfo == textSecIdx`, every relocation belongs to
  `relaTypeAllowedInExecSec` (`R_X86_64_PC32`) and satisfies
  `rOffset + 4 ≤ targetSec.shSize`;
- if `shInfo ≠ textSecIdx` and `sectionIsExec targetSec`, every relocation
  satisfies `execRelaFootprintInOwnSec targetSec.shSize` (so every
  relocation in a sibling executable section is a non-relaxable type whose
  exact write footprint stays within its own section). -/
@[expose] def allExecRelaTypesAllowed (obj : ParsedElf64Object)
    (textSecIdx : Nat) : Bool :=
  listAll
    (fun entry =>
      match listGet? obj.sections entry.2.1.shInfo with
      | none => false
      | some targetSec =>
        if Nat.beq entry.2.1.shInfo textSecIdx then
          listAll
            (fun r =>
              relaTypeAllowedInExecSec r &&
              Nat.ble (r.rOffset + 4) targetSec.shSize)
            entry.2.2
        else if sectionIsExec targetSec then
          listAll (execRelaFootprintInOwnSec targetSec.shSize) entry.2.2
        else true)
    obj.relaSections

/-- True iff relocation `r` has an admitted exact write footprint
`some (before, after)` lying strictly outside `[funcOff, funcOff + funcSize)`.
Any non-allowlisted relocation type returns `false` (never skipped as
disjoint). -/
@[expose] def relaDisjointFromFunc (funcOff funcSize : Nat)
    (r : Elf64Rela) : Bool :=
  match execRelaWriteFootprint? r with
  | none => false
  | some (before, after) =>
    Nat.ble (r.rOffset + after) funcOff ||
    Nat.ble (funcOff + funcSize + before) r.rOffset

/-- True iff some sibling relocation at index `j ≠ relaIdx` in `relas` is
outside `execRelaWriteFootprint?` or overlaps the 4-byte `PC32` field
`[targetOff, targetOff + 4)` (accounting for both backward and forward write
footprints). -/
@[expose] def otherRelaOverlapsPc32 (relas : List Elf64Rela)
    (relaIdx targetOff : Nat) : Bool :=
  (List.foldr
    (fun (r : Elf64Rela) (acc : Nat × Bool) =>
      let idx := acc.1
      let ov :=
        !Nat.beq idx relaIdx &&
        match execRelaWriteFootprint? r with
        | none => true
        | some (before, after) =>
          !(Nat.ble (r.rOffset + after) targetOff ||
            Nat.ble (targetOff + 4 + before) r.rOffset)
      (idx - 1, ov || acc.2))
    (relas.length - 1, false) relas).2

/-- Object-wide ELF hygiene gate bound directly to raw object bytes `bs`:
parses the complete ELF64 object via `parseElf64Object? bs` and checks zero
forbidden initializer/`W+X` sections across all `e_shnum` sections, zero
`STT_GNU_IFUNC` symbols across the entire `SHT_SYMTAB`, zero
`R_X86_64_IRELATIVE` relocations across every `SHT_RELA` section, and that
every executable-section relocation footprint stays within its own section's
`shSize` (`allExecRelaFootprintsInBounds`). -/
@[expose] def objectHasNoForbiddenElfFeatures (bs : List UInt8) : Bool :=
  match parseElf64Object? bs with
  | none => false
  | some obj =>
    !listAny sectionIsForbidden obj.sections &&
    !listAny symIsIfunc obj.syms &&
    !listAny relaIsIRelative obj.allRelas &&
    allExecRelaFootprintsInBounds obj

/-- Resolve an `R_X86_64_PC32` relocation at index `relaIdx` in the unique
non-COMDAT `SHT_RELA` section targeting `textSecIdx` (`shInfo == textSecIdx`),
bound directly to raw object bytes `bs`:
1. `parseElf64Object? bs = some obj` and `objectHasNoForbiddenElfFeatures bs`;
2. `obj.sections[textSecIdx]` exists and satisfies `sectionIsExecText`;
3. Exactly one `SHT_RELA` section targets `textSecIdx` (failing closed on
   duplicates or `SHF_GROUP`), with `shType = shtRela`, `shInfo = textSecIdx`,
   relocation `r` at `relaIdx` has `rType = PC32`, `rSymIdx ≠ 0`, and no other
   relocation in `relas` overlaps `[r.rOffset, r.rOffset + 4)`;
4. Target symbol exists in `obj.syms`, has `STB_LOCAL`, is not `IFUNC`, and
   has `0 < stShndx < 0xFF00` (excluding `SHN_UNDEF` and reserved indices);
5. Target section exists in `obj.sections`, satisfies
   `sectionIsReadOnlyRodata`, and NO `SHT_RELA` section in `obj.relaSections`
   targets `sym.stShndx` (certified read-only bytes are never relocation
   targets);
6. Effective constant offset `effOff` is non-negative,
   `effOff + accessBytes ≤ sec.shSize`, and
   `mergeEntryBoundsOk sec sym effOff accessBytes = true`. -/
@[expose] def resolvePc32RodataReloc (bs : List UInt8)
    (textSecIdx relaIdx insnEnd accessBytes : Nat) :
    Option ResolvedRodataRef :=
  match parseElf64Object? bs with
  | none => none
  | some obj =>
    if listAny sectionIsForbidden obj.sections ||
       listAny symIsIfunc obj.syms ||
       listAny relaIsIRelative obj.allRelas ||
       !allExecRelaTypesAllowed obj textSecIdx then none
    else
      match listGet? obj.sections textSecIdx with
      | none => none
      | some textSec =>
        if !sectionIsExecText textSec then none
        else
          match findUniqueRelaForTarget? obj.relaSections textSecIdx with
          | some (some (relaSec, relas)) =>
            if !Nat.beq relaSec.shType shtRela ||
               !Nat.beq relaSec.shInfo textSecIdx ||
               sectionHasGroup relaSec then none
            else
              match listGet? relas relaIdx with
              | none => none
              | some r =>
                if !Nat.beq r.rType rX86_64_PC32 ||
                   Nat.beq r.rSymIdx stnUndef ||
                   otherRelaOverlapsPc32 relas relaIdx r.rOffset then none
                else
                  match listGet? obj.syms r.rSymIdx with
                  | none => none
                  | some sym =>
                    if symIsIfunc sym || !symIsLocalBinding sym ||
                       !shndxIsDefinedRegular sym.stShndx then none
                    else
                      match listGet? obj.sections sym.stShndx with
                      | none => none
                      | some sec =>
                        if !sectionIsReadOnlyRodata sec ||
                           hasRelaTargetingSection obj.relaSections
                             sym.stShndx then none
                        else
                          let effInt : Int :=
                            Int.ofNat sym.stValue + r.rAddend +
                              (Int.ofNat insnEnd - Int.ofNat r.rOffset)
                          match intToNat? effInt with
                          | none => none
                          | some effOff =>
                            if Nat.ble (effOff + accessBytes) sec.shSize &&
                               mergeEntryBoundsOk sec sym effOff accessBytes
                            then
                              some {
                                secIdx := sym.stShndx
                                byteOff := effOff
                                accessBytes := accessBytes
                              }
                            else none
          | _ => none

/-- Extract and validate all `PcRelReloc`s for function
`[funcOff, funcOff + funcSize)` in validated executable `PROGBITS` section
`textSecIdx` (`funcOff + funcSize ≤ textSec.shSize`), deriving the unique
non-COMDAT `SHT_RELA` section targeting `textSecIdx` directly from
`parseElf64Object? bs` and rejecting any resolved `.rodata` target section
that is itself targeted by an `SHT_RELA` section. -/
@[expose] def extractFuncPcRelRelocs? (bs : List UInt8)
    (textSecIdx funcOff funcSize : Nat) : Option (List PcRelReloc) :=
  match parseElf64Object? bs with
  | none => none
  | some obj =>
    if listAny sectionIsForbidden obj.sections ||
       listAny symIsIfunc obj.syms ||
       listAny relaIsIRelative obj.allRelas ||
       !allExecRelaTypesAllowed obj textSecIdx then none
    else
      match listGet? obj.sections textSecIdx with
      | none => none
      | some textSec =>
        if !sectionIsExecText textSec ||
           !Nat.ble (funcOff + funcSize) textSec.shSize then none
        else
          match findUniqueRelaForTarget? obj.relaSections textSecIdx with
          | none => none
          | some none => some []
          | some (some (relaSec, relas)) =>
            if !Nat.beq relaSec.shType shtRela ||
               !Nat.beq relaSec.shInfo textSecIdx ||
               sectionHasGroup relaSec then none
            else
              List.foldr
                (fun r acc =>
                  match acc with
                  | none => none
                  | some out =>
                    if relaDisjointFromFunc funcOff funcSize r then some out
                    else if !Nat.beq r.rType rX86_64_PC32 ||
                            Nat.beq r.rSymIdx stnUndef then none
                    else if !Nat.ble funcOff r.rOffset ||
                            !Nat.ble (r.rOffset + 4) (funcOff + funcSize) then
                      none
                    else
                      match listGet? obj.syms r.rSymIdx with
                      | none => none
                      | some sym =>
                        if symIsIfunc sym || !symIsLocalBinding sym ||
                           !shndxIsDefinedRegular sym.stShndx then none
                        else
                          match listGet? obj.sections sym.stShndx with
                          | none => none
                          | some sec =>
                            if !sectionIsReadOnlyRodata sec ||
                               (sectionHasMerge sec && symIsSection sym) ||
                               hasRelaTargetingSection obj.relaSections
                                 sym.stShndx then
                              none
                            else
                              let pr : PcRelReloc := {
                                offset := r.rOffset - funcOff
                                secIdx := sym.stShndx
                                target := Int.ofNat sym.stValue + r.rAddend
                              }
                              some (pr :: out))
                (some []) relas

/-- Slice raw machine-code bytes of function `[funcOff, funcOff + funcSize)`
directly from validated executable `PROGBITS` section `textSecIdx` of raw ELF64
object `bs` (failing closed on malformed ELF, forbidden features, missing or
non-executable `textSecIdx`, or `funcOff + funcSize > textSec.shSize`). -/
@[expose] def funcTextBytes? (bs : List UInt8)
    (textSecIdx funcOff funcSize : Nat) : Option (List UInt8) :=
  match parseElf64Object? bs with
  | none => none
  | some obj =>
    if listAny sectionIsForbidden obj.sections ||
       listAny symIsIfunc obj.syms ||
       listAny relaIsIRelative obj.allRelas ||
       !allExecRelaTypesAllowed obj textSecIdx then none
    else
      match listGet? obj.sections textSecIdx with
      | none => none
      | some textSec =>
        if !sectionIsExecText textSec ||
           !Nat.ble (funcOff + funcSize) textSec.shSize then none
        else sliceBytes? bs (textSec.shOffset + funcOff) funcSize

/-- Find the 0-based index of a relocation in `relas` with
`r.rOffset == targetOff`. -/
@[expose] def findRelaIdxByOffset? (relas : List Elf64Rela)
    (targetOff : Nat) : Option Nat :=
  (List.foldr
    (fun (r : Elf64Rela) (acc : Nat × Option Nat) =>
      let idx := acc.1
      if Nat.beq r.rOffset targetOff then (idx - 1, some idx)
      else (idx - 1, acc.2))
    (relas.length - 1, none) relas).2

/-- Validate a single decoded trace entry's `.ripRel` operand (if any) by
reusing `resolvePc32RodataReloc` on raw bytes `bs`, rejecting active `FS:`/`GS:`
segment overrides (`seg.isSome`), `0x67` EIP-relative (`addr32 = true`),
un-relocated `.ripRel`, negative offsets, out-of-bounds `.rodata` accesses, and
cross-entry `SHF_MERGE` escapes. -/
@[expose] def traceEntryRipRelocOk (bs : List UInt8)
    (relas : List Elf64Rela) (textSecIdx funcOff : Nat)
    (entry : Nat × Nat × DecodedInsn) : Bool :=
  let off := entry.1
  let len := entry.2.1
  let ins := entry.2.2
  match insnMemOperandWithSize? ins with
  | some (.ripRel seg a32 secOpt relocOffOpt effOff, accBytes) =>
    if seg.isSome || a32 then false
    else
      match relocOffOpt with
      | none => false
      | some relocOff =>
        match findRelaIdxByOffset? relas (funcOff + relocOff) with
        | none => false
        | some rIdx =>
          match listGet? relas rIdx with
          | none => false
          | some r =>
            if !Nat.beq r.rOffset (funcOff + relocOff) then false
            else
              match resolvePc32RodataReloc bs textSecIdx rIdx
                  (funcOff + off + len) accBytes with
              | none => false
              | some ref =>
                optBeq Nat.beq secOpt (some ref.secIdx) &&
                intBeq effOff (Int.ofNat ref.byteOff)
  | _ => true

/-- Extract the relocation list from `findUniqueRelaForTarget?`'s result. -/
@[expose] def optRelaEntries
    (optRela : Option (Elf64SectionHdr × List Elf64Rela)) : List Elf64Rela :=
  match optRela with
  | none => []
  | some (_, rs) => rs

/-- Composed raw-ELF function decode entry point: fails closed unless
`cfg.requireRelocForRip = true` (rejecting base-less SIB `[disp32]` and
non-zero `disp32` placeholders on relocatable `ET_REL` objects), slices
`textBytes` from validated executable `PROGBITS` section `textSecIdx` via
`funcTextBytes?`, extracts `relocs` via `extractFuncPcRelRelocs?`, enforces
1-to-1 relocation coverage via `localDecodeCoverageOk`, decodes via
`decodeStream`, and validates every decoded `.ripRel` operand via
`resolvePc32RodataReloc` (`0 ≤ effOff`, `effOff + accessBytes ≤ sec.shSize`,
`mergeEntryBoundsOk`, and zero `SHT_RELA` sections targeting `.rodata`) without
trusting any caller-supplied `(bytes, relocs)` pair. -/
@[expose] def decodeFuncFromElf? (cfg : DecodeConfig) (bs : List UInt8)
    (textSecIdx funcOff funcSize : Nat) :
    Option (List (Nat × Nat × DecodedInsn)) :=
  if !cfg.requireRelocForRip then none
  else
    match funcTextBytes? bs textSecIdx funcOff funcSize with
    | none => none
    | some textBytes =>
      match extractFuncPcRelRelocs? bs textSecIdx funcOff funcSize with
      | none => none
      | some relocs =>
        if !localDecodeCoverageOk cfg relocs textBytes then none
        else
          match decodeStream cfg relocs textBytes with
          | none => none
          | some tr =>
            match parseElf64Object? bs with
            | none => none
            | some obj =>
              match findUniqueRelaForTarget? obj.relaSections textSecIdx with
              | none => none
              | some optRela =>
                if listAll (traceEntryRipRelocOk bs (optRelaEntries optRela)
                    textSecIdx funcOff) tr
                then some tr
                else none

/-! ## 4. Soundness, Raw-Object Binding, & Rejection Theorems
(at most `[propext]` Axioms) -/

private theorem relocIteTrue {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

private theorem relocIteFalse {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

private theorem relocBandLeft {a b : Bool} (h : (a && b) = true) :
    a = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => rfl

private theorem relocBandRight {a b : Bool} (h : (a && b) = true) :
    b = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => exact h

private theorem relocBorFalse {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | true => exact Bool.noConfusion h
  | false => exact ⟨rfl, h⟩

private theorem relocBoolFalseOfNotTrue {b : Bool} (h : (!b) = true) :
    b = false := by
  cases b with
  | false => rfl
  | true => exact Bool.noConfusion h

private theorem relocBoolTrueOfNotFalse {b : Bool} (h : (!b) = false) :
    b = true := by
  cases b with
  | true => rfl
  | false => exact Bool.noConfusion h

private theorem relocNatEqOfBeq (a b : Nat) (h : Nat.beq a b = true) :
    a = b :=
  Nat.eq_of_beq_eq_true h

private theorem relocNatBeqFalseOfNe {a b : Nat} (hne : a ≠ b) :
    Nat.beq a b = false := by
  cases h : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (hne (relocNatEqOfBeq a b h))

private theorem relocNatNeOfBeqFalse {a b : Nat} (h : Nat.beq a b = false) :
    a ≠ b := by
  intro hEq
  subst hEq
  have hT : Nat.beq a a = true := Nat.beq_refl a
  rw [hT] at h
  exact Bool.noConfusion h

private theorem relocIntEqOfBeq (a b : Int) (h : intBeq a b = true) :
    a = b := by
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y =>
      dsimp only [intBeq] at h
      rw [relocNatEqOfBeq x y h]
    | negSucc _ => exact Bool.noConfusion h
  | negSucc x =>
    cases b with
    | ofNat _ => exact Bool.noConfusion h
    | negSucc y =>
      dsimp only [intBeq] at h
      rw [relocNatEqOfBeq x y h]

private theorem relocOptNatEqOfBeq (a b : Option Nat)
    (h : optBeq Nat.beq a b = true) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some _ => exact Bool.noConfusion h
  | some x =>
    cases b with
    | none => exact Bool.noConfusion h
    | some y =>
      dsimp only [optBeq] at h
      rw [relocNatEqOfBeq x y h]

private theorem relocListAllMem {α : Type} (p : α → Bool) :
    ∀ (xs : List α), listAll p xs = true → ∀ x, x ∈ xs → p x = true := by
  intro xs hAll x hMem
  induction xs with
  | nil => nomatch hMem
  | cons y ys ih =>
    dsimp only [listAll, List.foldr] at hAll
    cases hMem with
    | head _ => exact relocBandLeft hAll
    | tail _ htl => exact ih (relocBandRight hAll) htl

private theorem relocListAnyOfMem {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (x : α), x ∈ xs → p x = true → listAny p xs = true := by
  intro xs x hmem hp
  induction xs with
  | nil => nomatch hmem
  | cons y ys ih =>
    cases hmem with
    | head _ =>
      change (p x || listAny p ys) = true
      rw [hp]
      rfl
    | tail _ htl =>
      change (p y || listAny p ys) = true
      rw [ih htl]
      cases p y <;> rfl

private theorem relocListAnyFalseOfMem {α : Type} (p : α → Bool)
    (xs : List α) (hAll : listAny p xs = false) (x : α) (hMem : x ∈ xs) :
    p x = false := by
  cases hp : p x with
  | false => rfl
  | true =>
    have hT := relocListAnyOfMem p xs x hMem hp
    rw [hT] at hAll
    exact Bool.noConfusion hAll

private theorem relocListGetMem {α : Type} :
    ∀ (xs : List α) (i : Nat) (x : α), listGet? xs i = some x → x ∈ xs := by
  intro xs
  induction xs with
  | nil =>
    intro i x h
    cases i <;> nomatch h
  | cons y ys ih =>
    intro i x h
    cases i with
    | zero =>
      dsimp only [listGet?] at h
      injection h with hEq
      subst hEq
      exact List.Mem.head ys
    | succ k =>
      dsimp only [listGet?] at h
      exact List.Mem.tail y (ih k x h)

private theorem relocListMemAppendLeft {α : Type} (xs ys : List α) {x : α}
    (h : x ∈ xs) : x ∈ xs ++ ys := by
  induction xs with
  | nil => nomatch h
  | cons a as ih =>
    cases h with
    | head _ => exact List.Mem.head (as ++ ys)
    | tail _ htl => exact List.Mem.tail a (ih htl)

private theorem relocListMemAppendRight {α : Type} (xs ys : List α) {x : α}
    (h : x ∈ ys) : x ∈ xs ++ ys := by
  induction xs with
  | nil => exact h
  | cons a as ih => exact List.Mem.tail a ih

private theorem parseAllSectionHdrsAux_length (bs shstrtab : List UInt8) :
    ∀ (rem : Nat) (cur : List UInt8) (secs : List Elf64SectionHdr),
      parseAllSectionHdrsAux bs shstrtab rem cur = some secs →
      secs.length = rem := by
  intro rem
  induction rem with
  | zero =>
    intro cur secs h
    dsimp only [parseAllSectionHdrsAux] at h
    injection h with hEq
    subst hEq
    rfl
  | succ k ih =>
    intro cur secs h
    dsimp only [parseAllSectionHdrsAux] at h
    revert h
    cases hSh : parseElf64SectionHdrHead? shstrtab cur with
    | none => intro h; nomatch h
    | some p =>
      intro h
      cases p with
      | mk sh rest =>
        dsimp only at h
        cases hB : (!Nat.beq sh.shType shtNobits &&
            !bytesLenAtLeast (sh.shOffset + sh.shSize) bs) with
        | true => rw [relocIteTrue hB] at h; nomatch h
        | false =>
          rw [relocIteFalse hB] at h
          cases hPrev : parseAllSectionHdrsAux bs shstrtab k rest with
          | none =>
            dsimp only [parseAllSectionHdrsAux] at hPrev
            rw [hPrev] at h
            nomatch h
          | some tl =>
            dsimp only [parseAllSectionHdrsAux] at hPrev
            rw [hPrev] at h
            dsimp only at h
            injection h with hEq
            subst hEq
            dsimp only [List.length]
            rw [ih rest tl hPrev]

private theorem collectAllRelas_mem
    (relaSecs : List (Nat × Elf64SectionHdr × List Elf64Rela))
    (entry : Nat × Elf64SectionHdr × List Elf64Rela)
    (hEntry : entry ∈ relaSecs) (r : Elf64Rela) (hR : r ∈ entry.2.2) :
    r ∈ collectAllRelas relaSecs := by
  induction relaSecs with
  | nil => nomatch hEntry
  | cons hd tl ih =>
    dsimp only [collectAllRelas, List.foldr]
    cases hEntry with
    | head _ => exact relocListMemAppendLeft entry.2.2 (collectAllRelas tl) hR
    | tail _ htl =>
      exact relocListMemAppendRight hd.2.2 (collectAllRelas tl) (ih htl)

private theorem relocListFindMem {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (x : α), listFind? p xs = some x → x ∈ xs := by
  intro xs
  induction xs with
  | nil =>
    intro x h
    dsimp only [listFind?, List.foldr] at h
    nomatch h
  | cons y ys ih =>
    intro x h
    dsimp only [listFind?, List.foldr] at h
    cases hp : p y with
    | true =>
      rw [relocIteTrue hp] at h
      injection h with hEq
      subst hEq
      exact List.Mem.head ys
    | false =>
      rw [relocIteFalse hp] at h
      exact List.Mem.tail y (ih x h)

/-- Raw-object binding theorem (`[propext]` only): whenever
`parseElf64Object? bs = some obj`, the resulting inventory is bound verbatim
to `bs`, `obj.sections` has exact length `obj.header.eShnum`, `sections[0]` is
an all-zero `SHT_NULL` entry, no unparsed symbol/relocation table sections
(`SHT_DYNSYM`/`SHT_REL`/`SHT_RELR`) exist anywhere in `obj.sections`, and every
relocation from every `SHT_RELA` section belongs to `obj.allRelas`. -/
theorem parseElf64Object?_binds_raw (bs : List UInt8)
    (obj : ParsedElf64Object) (h : parseElf64Object? bs = some obj) :
    obj.rawBytes = bs ∧
    parseElf64Header? bs = some obj.header ∧
    obj.sections.length = obj.header.eShnum ∧
    (∀ sec, sec ∈ obj.sections → sectionIsUnparsedTableType sec = false) ∧
    (∀ entry, entry ∈ obj.relaSections →
      ∀ r, r ∈ entry.2.2 → r ∈ obj.allRelas) ∧
    (∃ s0 rest, obj.sections = s0 :: rest ∧ sectionHdrIsNull s0 = true) := by
  dsimp only [parseElf64Object?] at h
  revert h
  cases hHdr : parseElf64Header? bs with
  | none => intro h; nomatch h
  | some hdr =>
    intro h; dsimp only at h
    revert h
    cases hZero0 : bytesPrefixAllZero64 (fastDropBytes hdr.eShoff bs) with
    | false => intro h; nomatch h
    | true =>
      intro h; rw [relocIteFalse (rfl : (!true) = false)] at h
      revert h
      cases hShstrHdr : parseElf64SectionHdrHeadWithName? ".shstrtab"
          (fastDropBytes (hdr.eShstrndx * elf64Shentsize)
            (fastDropBytes hdr.eShoff bs)) with
      | none => intro h; nomatch h
      | some shstrP =>
        intro h
        cases shstrP with
        | mk shstrHdr _ =>
          dsimp only at h
          cases hStrBad : (!Nat.beq shstrHdr.shType shtStrtab ||
              !sectionMetaFlagsOk shstrHdr) with
          | true => rw [relocIteTrue hStrBad] at h; nomatch h
          | false =>
            rw [relocIteFalse hStrBad] at h
            revert h
            cases hSlice :
                sliceBytes? bs shstrHdr.shOffset shstrHdr.shSize with
            | none => intro h; nomatch h
            | some shstrtab =>
              intro h; dsimp only at h
              revert h
              cases hSecs : parseAllSectionHdrsAux bs shstrtab hdr.eShnum
                  (fastDropBytes hdr.eShoff bs) with
              | none => intro h; nomatch h
              | some secs =>
                intro h; dsimp only at h
                cases secs with
                | nil => nomatch h
                | cons s0 rest =>
                  dsimp only at h
                  cases hBad0 : (!sectionHdrIsNull s0 ||
                      listAny sectionIsUnparsedTableType (s0 :: rest)) with
                  | true => rw [relocIteTrue hBad0] at h; nomatch h
                  | false =>
                    rw [relocIteFalse hBad0] at h
                    have hBad0P := relocBorFalse hBad0
                    have hS0Null : sectionHdrIsNull s0 = true :=
                      relocBoolTrueOfNotFalse hBad0P.1
                    have hUnp :
                        listAny sectionIsUnparsedTableType (s0 :: rest) =
                          false := hBad0P.2
                    revert h
                    cases hSyms : parseObjectSymtab? bs (s0 :: rest) with
                    | none => intro h; nomatch h
                    | some syms =>
                      intro h; dsimp only at h
                      revert h
                      cases hRelas : parseAllRelaSections? bs (s0 :: rest) with
                      | none => intro h; nomatch h
                      | some relaSecs =>
                        intro h; dsimp only at h
                        injection h with hObj
                        subst hObj
                        refine ⟨rfl, rfl,
                          parseAllSectionHdrsAux_length bs shstrtab hdr.eShnum
                            (fastDropBytes hdr.eShoff bs) (s0 :: rest) hSecs,
                          fun sec hMem =>
                            relocListAnyFalseOfMem sectionIsUnparsedTableType
                              (s0 :: rest) hUnp sec hMem,
                          fun entry hE r hR =>
                            collectAllRelas_mem relaSecs entry hE r hR,
                          ⟨s0, rest, rfl, hS0Null⟩⟩

/-- Object-hygiene binding theorem (`[propext]` only, via `parseElf64Object?`):
`objectHasNoForbiddenElfFeatures bs = true` proves that `bs` parses cleanly via
`parseElf64Object? bs = some obj` and that EVERY section in `obj.sections`,
EVERY symbol in `obj.syms`, EVERY relocation in `obj.allRelas`, and EVERY
executable-section relocation footprint (`allExecRelaFootprintsInBounds`) is
clean. -/
theorem objectHasNoForbiddenElfFeatures_bound (bs : List UInt8)
    (h : objectHasNoForbiddenElfFeatures bs = true) :
    ∃ obj,
      parseElf64Object? bs = some obj ∧
      obj.rawBytes = bs ∧
      obj.sections.length = obj.header.eShnum ∧
      (∀ s, s ∈ obj.sections → sectionIsForbidden s = false) ∧
      (∀ sym, sym ∈ obj.syms → symIsIfunc sym = false) ∧
      (∀ r, r ∈ obj.allRelas → relaIsIRelative r = false) ∧
      allExecRelaFootprintsInBounds obj = true := by
  dsimp only [objectHasNoForbiddenElfFeatures] at h
  revert h
  cases hP : parseElf64Object? bs with
  | none => intro h; nomatch h
  | some obj =>
    intro h; dsimp only at h
    have hB := parseElf64Object?_binds_raw bs obj hP
    have hL3 := relocBandLeft h
    have hFootOk := relocBandRight h
    have hL2 := relocBandLeft hL3
    have hNoIR := relocBoolFalseOfNotTrue (relocBandRight hL3)
    have hNoForb := relocBoolFalseOfNotTrue (relocBandLeft hL2)
    have hNoIf := relocBoolFalseOfNotTrue (relocBandRight hL2)
    exact ⟨obj, rfl, hB.1, hB.2.2.1,
      fun s hs => relocListAnyFalseOfMem sectionIsForbidden obj.sections
        hNoForb s hs,
      fun sym hs => relocListAnyFalseOfMem symIsIfunc obj.syms hNoIf sym hs,
      fun r hr => relocListAnyFalseOfMem relaIsIRelative obj.allRelas
        hNoIR r hr,
      hFootOk⟩

private theorem relocListAllImp {α : Type} (p q : α → Bool)
    (hImp : ∀ x, p x = true → q x = true) :
    ∀ (xs : List α), listAll p xs = true → listAll q xs = true := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons a tl ih =>
    intro h
    dsimp only [listAll, List.foldr] at h
    dsimp only [listAll, List.foldr]
    have hTl : listAll q tl = true := ih (relocBandRight h)
    dsimp only [listAll] at hTl
    rw [hImp a (relocBandLeft h), hTl]
    rfl

private theorem relocNatBeqRefl : ∀ (n : Nat), Nat.beq n n = true := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => exact ih

/-- Target-section allowlist implies object-wide executable-section relocation
footprint bounds (`[]` axioms). -/
theorem allExecRelaFootprintsInBounds_of_allowed (obj : ParsedElf64Object)
    (textSecIdx : Nat) (h : allExecRelaTypesAllowed obj textSecIdx = true) :
    allExecRelaFootprintsInBounds obj = true := by
  dsimp only [allExecRelaTypesAllowed] at h
  dsimp only [allExecRelaFootprintsInBounds]
  refine relocListAllImp
    (fun (entry : Nat × Elf64SectionHdr × List Elf64Rela) =>
      match listGet? obj.sections entry.2.1.shInfo with
      | none => false
      | some targetSec =>
        if Nat.beq entry.2.1.shInfo textSecIdx then
          listAll
            (fun r =>
              relaTypeAllowedInExecSec r &&
              Nat.ble (r.rOffset + 4) targetSec.shSize)
            entry.2.2
        else if sectionIsExec targetSec then
          listAll (execRelaFootprintInOwnSec targetSec.shSize) entry.2.2
        else true)
    (fun (entry : Nat × Elf64SectionHdr × List Elf64Rela) =>
      match listGet? obj.sections entry.2.1.shInfo with
      | none => false
      | some targetSec =>
        if sectionIsExec targetSec then
          listAll (execRelaFootprintInOwnSec targetSec.shSize) entry.2.2
        else true)
    ?_ obj.relaSections h
  intro entry hE
  revert hE
  cases hSec : listGet? obj.sections entry.2.1.shInfo with
  | none => intro hE; exact Bool.noConfusion hE
  | some targetSec =>
    intro hE
    dsimp only at hE
    dsimp only
    cases hEq : Nat.beq entry.2.1.shInfo textSecIdx with
    | false => rw [relocIteFalse hEq] at hE; exact hE
    | true =>
      rw [relocIteTrue hEq] at hE
      cases hEx : sectionIsExec targetSec with
      | false => rw [relocIteFalse (rfl : false = false)]
      | true =>
        rw [relocIteTrue (rfl : true = true)]
        refine relocListAllImp
          (fun r =>
            relaTypeAllowedInExecSec r &&
            Nat.ble (r.rOffset + 4) targetSec.shSize)
          (execRelaFootprintInOwnSec targetSec.shSize)
          ?_ entry.2.2 hE
        intro r hR
        dsimp only [execRelaFootprintInOwnSec]
        rw [relocIteTrue (relocBandLeft hR)]
        exact relocBandRight hR

/-- Scoped executable-section relocation allowlist and footprint bound
(`[]` axioms): `allExecRelaTypesAllowed obj textSecIdx = true` proves that
every `SHT_RELA` section in `obj` targets a valid section header
`obj.sections[shInfo] = some targetSec` such that:
- if `shInfo = textSecIdx`, every relocation is `R_X86_64_PC32` with
  `rOffset + 4 ≤ targetSec.shSize`;
- if `sectionIsExec targetSec = true`, every relocation satisfies
  `execRelaFootprintInOwnSec targetSec.shSize r = true`. -/
theorem allExecRelaTypesAllowed_bound (obj : ParsedElf64Object)
    (textSecIdx : Nat) (h : allExecRelaTypesAllowed obj textSecIdx = true) :
    ∀ entry, entry ∈ obj.relaSections →
      ∃ targetSec,
        listGet? obj.sections entry.2.1.shInfo = some targetSec ∧
        (entry.2.1.shInfo = textSecIdx →
          ∀ r, r ∈ entry.2.2 →
            relaTypeAllowedInExecSec r = true ∧
            r.rOffset + 4 ≤ targetSec.shSize) ∧
        (sectionIsExec targetSec = true →
          ∀ r, r ∈ entry.2.2 →
            execRelaFootprintInOwnSec targetSec.shSize r = true) := by
  intro entry hE
  have hFoot := allExecRelaFootprintsInBounds_of_allowed obj textSecIdx h
  dsimp only [allExecRelaTypesAllowed] at h
  dsimp only [allExecRelaFootprintsInBounds] at hFoot
  have hAll := relocListAllMem
    (fun (e : Nat × Elf64SectionHdr × List Elf64Rela) =>
      match listGet? obj.sections e.2.1.shInfo with
      | none => false
      | some targetSec =>
        if Nat.beq e.2.1.shInfo textSecIdx then
          listAll
            (fun r =>
              relaTypeAllowedInExecSec r &&
              Nat.ble (r.rOffset + 4) targetSec.shSize)
            e.2.2
        else if sectionIsExec targetSec then
          listAll (execRelaFootprintInOwnSec targetSec.shSize) e.2.2
        else true)
    obj.relaSections h entry hE
  have hFAll := relocListAllMem
    (fun (e : Nat × Elf64SectionHdr × List Elf64Rela) =>
      match listGet? obj.sections e.2.1.shInfo with
      | none => false
      | some targetSec =>
        if sectionIsExec targetSec then
          listAll (execRelaFootprintInOwnSec targetSec.shSize) e.2.2
        else true)
    obj.relaSections hFoot entry hE
  cases hSec : listGet? obj.sections entry.2.1.shInfo with
  | none => rw [hSec] at hAll; exact Bool.noConfusion hAll
  | some targetSec =>
    rw [hSec] at hAll hFAll; dsimp only at hAll hFAll
    refine ⟨targetSec, rfl, ?_, ?_⟩
    · intro hInfo r hR
      have hBeq : Nat.beq entry.2.1.shInfo textSecIdx = true := by
        rw [hInfo]; exact relocNatBeqRefl textSecIdx
      rw [relocIteTrue hBeq] at hAll
      have hOk := relocListAllMem
        (fun r =>
          relaTypeAllowedInExecSec r &&
          Nat.ble (r.rOffset + 4) targetSec.shSize)
        entry.2.2 hAll r hR
      exact ⟨relocBandLeft hOk, Nat.le_of_ble_eq_true (relocBandRight hOk)⟩
    · intro hEx r hR
      rw [relocIteTrue hEx] at hFAll
      exact relocListAllMem
        (execRelaFootprintInOwnSec targetSec.shSize) entry.2.2 hFAll r hR

/-- Uniqueness theorem for `findUniqueRelaForTarget?` (`[propext]` only):
whenever `findUniqueRelaForTarget? relaSecs targetSecIdx = some found`, every
parsed
`SHT_RELA` section targeting `targetSecIdx` in `relaSecs` equals `found`
(so no second `SHT_RELA` section targeting `targetSecIdx` can exist). -/
theorem findUniqueRelaForTarget?_unique
    (relaSecs : List (Nat × Elf64SectionHdr × List Elf64Rela))
    (targetSecIdx : Nat)
    (found : Option (Elf64SectionHdr × List Elf64Rela))
    (h : findUniqueRelaForTarget? relaSecs targetSecIdx = some found) :
    ∀ entry, entry ∈ relaSecs → entry.2.1.shInfo = targetSecIdx →
      found = some entry.2 := by
  revert found
  induction relaSecs with
  | nil =>
    intro _ _ _ hMem _
    nomatch hMem
  | cons hd tl ih =>
    intro found h entry hMem hInfo
    dsimp only [findUniqueRelaForTarget?, List.foldr] at h
    cases hTl : findUniqueRelaForTarget? tl targetSecIdx with
    | none =>
      dsimp only [findUniqueRelaForTarget?] at hTl
      rw [hTl] at h
      nomatch h
    | some tlFound =>
      dsimp only [findUniqueRelaForTarget?] at hTl
      rw [hTl] at h; dsimp only at h
      cases hHit : Nat.beq hd.2.1.shInfo targetSecIdx with
      | true =>
        rw [relocIteTrue hHit] at h
        cases tlFound with
        | some _ => nomatch h
        | none =>
          injection h with hEq
          subst hEq
          cases hMem with
          | head _ => rfl
          | tail _ hInTl =>
            have hContra := ih none hTl entry hInTl hInfo
            nomatch hContra
      | false =>
        rw [relocIteFalse hHit] at h
        injection h with hEq
        subst hEq
        cases hMem with
        | head _ =>
          rw [hInfo] at hHit
          have hRefl : Nat.beq targetSecIdx targetSecIdx = true :=
            Nat.beq_refl targetSecIdx
          rw [hRefl] at hHit
          exact Bool.noConfusion hHit
        | tail _ hInTl => exact ih tlFound hTl entry hInTl hInfo

private theorem hasRelaTargetingSection_false_imp
    (relaSecs : List (Nat × Elf64SectionHdr × List Elf64Rela))
    (secIdx : Nat) (h : hasRelaTargetingSection relaSecs secIdx = false) :
    ∀ entry, entry ∈ relaSecs → entry.2.1.shInfo ≠ secIdx := by
  intro entry hMem
  have hF := relocListAnyFalseOfMem
    (fun (e : Nat × Elf64SectionHdr × List Elf64Rela) =>
      Nat.beq e.2.1.shInfo secIdx)
    relaSecs h entry hMem
  exact relocNatNeOfBeqFalse hF

/-- Soundness of `resolvePc32RodataReloc` (`[propext]` only): any resolved
reference is bound to `parseElf64Object? bs = some obj`, a validated executable
`PROGBITS` code section at `textSecIdx` (`sectionIsExecText`), and the unique
non-COMDAT `SHT_RELA` section targeting `textSecIdx` (`shType = shtRela`,
`shInfo = textSecIdx`), guaranteeing whole-object hygiene, `R_X86_64_PC32`,
`r_sym ≠ 0`, no overlapping sibling relocation in `relas`, a local non-`IFUNC`
symbol with `0 < st_shndx < 0xFF00`, a read-only non-COMDAT uncompressed
non-TLS non-string non-excluded target section with ZERO `SHT_RELA` sections
targeting `sym.stShndx`, a non-negative in-bounds constant offset,
`SHF_MERGE` single-entry bounds (non-`STT_SECTION`), and the target-section
relocation allowlist (`allExecRelaTypesAllowed obj textSecIdx = true`). -/
theorem resolvePc32RodataReloc_sound (bs : List UInt8)
    (textSecIdx relaIdx insnEnd accessBytes : Nat) (ref : ResolvedRodataRef)
    (h : resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      some ref) :
    objectHasNoForbiddenElfFeatures bs = true ∧
    ∃ obj textSec relaSec relas r sym sec,
      parseElf64Object? bs = some obj ∧
      listGet? obj.sections textSecIdx = some textSec ∧
      sectionIsExecText textSec = true ∧
      findUniqueRelaForTarget? obj.relaSections textSecIdx =
        some (some (relaSec, relas)) ∧
      relaSec.shType = shtRela ∧
      relaSec.shInfo = textSecIdx ∧
      listGet? relas relaIdx = some r ∧
      r.rType = rX86_64_PC32 ∧
      r.rSymIdx ≠ stnUndef ∧
      listGet? obj.syms r.rSymIdx = some sym ∧
      shndxIsDefinedRegular sym.stShndx = true ∧
      listGet? obj.sections sym.stShndx = some sec ∧
      sym.stBind = stbLocal ∧
      sectionIsWritable sec = false ∧
      sectionHasGroup sec = false ∧
      sectionIsReadOnlyRodata sec = true ∧
      ref.secIdx = sym.stShndx ∧
      intToNat? (Int.ofNat sym.stValue + r.rAddend +
        (Int.ofNat insnEnd - Int.ofNat r.rOffset)) = some ref.byteOff ∧
      ref.byteOff + accessBytes ≤ sec.shSize ∧
      mergeEntryBoundsOk sec sym ref.byteOff accessBytes = true ∧
      sectionHasGroup relaSec = false ∧
      hasRelaTargetingSection obj.relaSections sym.stShndx = false ∧
      (∀ entry, entry ∈ obj.relaSections → entry.2.1.shInfo ≠ sym.stShndx) ∧
      allExecRelaTypesAllowed obj textSecIdx = true := by
  dsimp only [resolvePc32RodataReloc] at h
  revert h
  cases hP : parseElf64Object? bs with
  | none => intro h; nomatch h
  | some obj =>
    intro h; dsimp only at h
    cases hBad : (listAny sectionIsForbidden obj.sections ||
        listAny symIsIfunc obj.syms ||
        listAny relaIsIRelative obj.allRelas ||
        !allExecRelaTypesAllowed obj textSecIdx) with
    | true => rw [relocIteTrue hBad] at h; nomatch h
    | false =>
      rw [relocIteFalse hBad] at h
      have hBad3 := (relocBorFalse hBad).1
      have hExecOk : allExecRelaTypesAllowed obj textSecIdx = true :=
        relocBoolTrueOfNotFalse (relocBorFalse hBad).2
      have hBadL := (relocBorFalse hBad3).1
      have hNoIR := (relocBorFalse hBad3).2
      have hNoForb := (relocBorFalse hBadL).1
      have hNoIf := (relocBorFalse hBadL).2
      revert h
      cases hText : listGet? obj.sections textSecIdx with
      | none => intro h; nomatch h
      | some textSec =>
        intro h; dsimp only at h
        revert h
        cases hExec : sectionIsExecText textSec with
        | false => intro h; nomatch h
        | true =>
          intro h; rw [relocIteFalse (rfl : (!true) = false)] at h
          revert h
          cases hRs : findUniqueRelaForTarget? obj.relaSections textSecIdx with
          | none => intro h; nomatch h
          | some optP =>
            intro h
            cases optP with
            | none => nomatch h
            | some p =>
              cases p with
              | mk relaSec relas =>
                dsimp only at h
                cases hHdr : (!Nat.beq relaSec.shType shtRela ||
                              !Nat.beq relaSec.shInfo textSecIdx ||
                              sectionHasGroup relaSec) with
                | true => rw [relocIteTrue hHdr] at h; nomatch h
                | false =>
                  rw [relocIteFalse hHdr] at h
                  have hHdrL := (relocBorFalse hHdr).1
                  have hRelaNoGrp := (relocBorFalse hHdr).2
                  have hHdrOk := relocBorFalse hHdrL
                  have hTySec := relocNatEqOfBeq relaSec.shType shtRela
                    (relocBoolTrueOfNotFalse hHdrOk.1)
                  have hInfSec := relocNatEqOfBeq relaSec.shInfo textSecIdx
                    (relocBoolTrueOfNotFalse hHdrOk.2)
                  revert h
                  cases hR : listGet? relas relaIdx with
                  | none => intro h; nomatch h
                  | some r =>
                    intro h; dsimp only at h
                    cases hRTyBad : (!Nat.beq r.rType rX86_64_PC32 ||
                        Nat.beq r.rSymIdx stnUndef ||
                        otherRelaOverlapsPc32 relas relaIdx r.rOffset) with
                    | true => rw [relocIteTrue hRTyBad] at h; nomatch h
                    | false =>
                      rw [relocIteFalse hRTyBad] at h
                      have hRTyOk := relocBorFalse (relocBorFalse hRTyBad).1
                      have hTyEq : r.rType = rX86_64_PC32 :=
                        relocNatEqOfBeq r.rType rX86_64_PC32
                          (relocBoolTrueOfNotFalse hRTyOk.1)
                      have hSymNe : r.rSymIdx ≠ stnUndef :=
                        relocNatNeOfBeqFalse hRTyOk.2
                      revert h
                      cases hSym : listGet? obj.syms r.rSymIdx with
                      | none => intro h; nomatch h
                      | some sym =>
                        intro h; dsimp only at h
                        cases hSymBad : (symIsIfunc sym ||
                            !symIsLocalBinding sym ||
                            !shndxIsDefinedRegular sym.stShndx) with
                        | true => rw [relocIteTrue hSymBad] at h; nomatch h
                        | false =>
                          rw [relocIteFalse hSymBad] at h
                          have hSymBadL := (relocBorFalse hSymBad).1
                          have hShndxOk :
                              shndxIsDefinedRegular sym.stShndx = true :=
                            relocBoolTrueOfNotFalse (relocBorFalse hSymBad).2
                          have hLocalB : symIsLocalBinding sym = true :=
                            relocBoolTrueOfNotFalse (relocBorFalse hSymBadL).2
                          have hBindEq : sym.stBind = stbLocal :=
                            relocNatEqOfBeq sym.stBind stbLocal hLocalB
                          revert h
                          cases hSec : listGet? obj.sections sym.stShndx with
                          | none => intro h; nomatch h
                          | some sec =>
                            intro h; dsimp only at h
                            cases hRoBad : (!sectionIsReadOnlyRodata sec ||
                                hasRelaTargetingSection obj.relaSections
                                  sym.stShndx) with
                            | true => rw [relocIteTrue hRoBad] at h; nomatch h
                            | false =>
                              rw [relocIteFalse hRoBad] at h
                              have hRoP := relocBorFalse hRoBad
                              have hRo : sectionIsReadOnlyRodata sec = true :=
                                relocBoolTrueOfNotFalse hRoP.1
                              have hNoRoRela :
                                  hasRelaTargetingSection obj.relaSections
                                    sym.stShndx = false := hRoP.2
                              revert h
                              cases hInt :
                                  intToNat? (Int.ofNat sym.stValue + r.rAddend +
                                    (Int.ofNat insnEnd -
                                      Int.ofNat r.rOffset)) with
                              | none => intro h; nomatch h
                              | some effOff =>
                                intro h; dsimp only at h
                                cases hBnd :
                                    (Nat.ble (effOff + accessBytes)
                                        sec.shSize &&
                                      mergeEntryBoundsOk sec sym effOff
                                        accessBytes) with
                                | false =>
                                  rw [relocIteFalse hBnd] at h; nomatch h
                                | true =>
                                  rw [relocIteTrue hBnd] at h
                                  injection h with hRef
                                  subst hRef
                                  have hRo8 := relocBandLeft hRo
                                  have hRo7 := relocBandLeft hRo8
                                  have hRo6 := relocBandLeft hRo7
                                  have hRo5 := relocBandLeft hRo6
                                  have hRoGrp :=
                                    relocBoolFalseOfNotTrue
                                      (relocBandRight hRo5)
                                  have hRo4 := relocBandLeft hRo5
                                  have hRo3 := relocBandLeft hRo4
                                  have hRo2 := relocBandLeft hRo3
                                  have hWFalse :=
                                    relocBoolFalseOfNotTrue
                                      (relocBandRight hRo2)
                                  have hHyg :
                                      objectHasNoForbiddenElfFeatures bs =
                                        true := by
                                    dsimp only [objectHasNoForbiddenElfFeatures]
                                    rw [hP]; dsimp only
                                    rw [hNoForb, hNoIf, hNoIR,
                                      allExecRelaFootprintsInBounds_of_allowed
                                        obj textSecIdx hExecOk]; rfl
                                  exact ⟨hHyg,
                                    ⟨obj, textSec, relaSec, relas, r, sym, sec,
                                     rfl, hText, hExec, hRs, hTySec, hInfSec,
                                     hR, hTyEq, hSymNe, hSym, hShndxOk, hSec,
                                     hBindEq, hWFalse, hRoGrp, hRo, rfl, hInt,
                                     Nat.le_of_ble_eq_true (relocBandLeft hBnd),
                                     relocBandRight hBnd, hRelaNoGrp, hNoRoRela,
                                     hasRelaTargetingSection_false_imp
                                       obj.relaSections sym.stShndx hNoRoRela,
                                     hExecOk⟩⟩

/-- The facts `resolvePc32RodataReloc_sound` gives about the relocation, symbol,
and section a successful resolution used, restated for the caller's own `obj`,
`relas`, `r`, `sym`, and `sec`. The negative rejection theorems below share
this single destructuring of the soundness theorem's long existential. -/
private theorem resolvePc32RodataReloc_sound_at {bs : List UInt8}
    {obj : ParsedElf64Object} {relaSec : Elf64SectionHdr}
    {relas : List Elf64Rela} {r : Elf64Rela}
    {textSecIdx relaIdx insnEnd accessBytes : Nat} {ref : ResolvedRodataRef}
    (hRes : resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      some ref)
    (hP : parseElf64Object? bs = some obj)
    (hRs : findUniqueRelaForTarget? obj.relaSections textSecIdx =
      some (some (relaSec, relas)))
    (hR : listGet? relas relaIdx = some r) :
    r.rType = rX86_64_PC32 ∧
    ∀ sym, listGet? obj.syms r.rSymIdx = some sym →
      sym.stBind = stbLocal ∧
      (∀ entry, entry ∈ obj.relaSections → entry.2.1.shInfo ≠ sym.stShndx) ∧
      ∀ sec, listGet? obj.sections sym.stShndx = some sec →
        sectionIsWritable sec = false ∧ sectionHasGroup sec = false ∧
        intToNat? (Int.ofNat sym.stValue + r.rAddend +
          (Int.ofNat insnEnd - Int.ofNat r.rOffset)) = some ref.byteOff ∧
        ref.byteOff + accessBytes ≤ sec.shSize ∧
        mergeEntryBoundsOk sec sym ref.byteOff accessBytes = true := by
  have hS := resolvePc32RodataReloc_sound bs textSecIdx relaIdx insnEnd
    accessBytes ref hRes
  have ⟨obj', _, _, relas', r', sym', sec', hP', _, _, hRs', _, _, hR', hTy',
        _, hSym', _, hSec', hBind', hW', hGrp', _, _, hOff', hLe', hMb', _, _,
        hNoTarget', _⟩ := hS.2
  rw [hP] at hP'
  have hObjEq : obj = obj' := Option.some.inj hP'
  subst hObjEq
  rw [hRs] at hRs'
  have hPairEq := Option.some.inj (Option.some.inj hRs')
  injection hPairEq with _ hRelasEq
  subst hRelasEq
  rw [hR] at hR'
  have hREq : r = r' := Option.some.inj hR'
  subst hREq
  refine ⟨hTy', fun sym hSym => ?_⟩
  rw [hSym] at hSym'
  have hSymEq : sym = sym' := Option.some.inj hSym'
  subst hSymEq
  refine ⟨hBind', hNoTarget', fun sec hSec => ?_⟩
  rw [hSec] at hSec'
  have hSecEq : sec = sec' := Option.some.inj hSec'
  subst hSecEq
  exact ⟨hW', hGrp', hOff', hLe', hMb'⟩

/-- Negative rejection: any writable target section (`SHF_WRITE = 1`) is
rejected fail-closed. -/
theorem resolvePc32RodataReloc_rejects_writable (bs : List UInt8)
    (obj : ParsedElf64Object) (relaSec : Elf64SectionHdr)
    (relas : List Elf64Rela) (r : Elf64Rela)
    (textSecIdx relaIdx insnEnd accessBytes : Nat)
    (sym : Elf64Sym) (sec : Elf64SectionHdr)
    (hP : parseElf64Object? bs = some obj)
    (hRs : findUniqueRelaForTarget? obj.relaSections textSecIdx =
      some (some (relaSec, relas)))
    (hR : listGet? relas relaIdx = some r)
    (hSym : listGet? obj.syms r.rSymIdx = some sym)
    (hSec : listGet? obj.sections sym.stShndx = some sec)
    (hW : sectionIsWritable sec = true) :
    resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      none := by
  cases hRes :
      resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes with
  | none => rfl
  | some ref =>
    have hA := resolvePc32RodataReloc_sound_at hRes hP hRs hR
    have hWFalse := ((hA.2 sym hSym).2.2 sec hSec).1
    rw [hW] at hWFalse
    exact Bool.noConfusion hWFalse

/-- Negative rejection: any non-`STB_LOCAL` symbol (`STB_GLOBAL`/`STB_WEAK`)
is rejected fail-closed. -/
theorem resolvePc32RodataReloc_rejects_nonlocal (bs : List UInt8)
    (obj : ParsedElf64Object) (relaSec : Elf64SectionHdr)
    (relas : List Elf64Rela) (r : Elf64Rela)
    (textSecIdx relaIdx insnEnd accessBytes : Nat) (sym : Elf64Sym)
    (hP : parseElf64Object? bs = some obj)
    (hRs : findUniqueRelaForTarget? obj.relaSections textSecIdx =
      some (some (relaSec, relas)))
    (hR : listGet? relas relaIdx = some r)
    (hSym : listGet? obj.syms r.rSymIdx = some sym)
    (hNe : sym.stBind ≠ stbLocal) :
    resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      none := by
  cases hRes :
      resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes with
  | none => rfl
  | some ref =>
    have hA := resolvePc32RodataReloc_sound_at hRes hP hRs hR
    exact False.elim (hNe (hA.2 sym hSym).1)

/-- Negative rejection: any `SHF_GROUP` (COMDAT) target section is rejected
fail-closed. -/
theorem resolvePc32RodataReloc_rejects_group (bs : List UInt8)
    (obj : ParsedElf64Object) (relaSec : Elf64SectionHdr)
    (relas : List Elf64Rela) (r : Elf64Rela)
    (textSecIdx relaIdx insnEnd accessBytes : Nat)
    (sym : Elf64Sym) (sec : Elf64SectionHdr)
    (hP : parseElf64Object? bs = some obj)
    (hRs : findUniqueRelaForTarget? obj.relaSections textSecIdx =
      some (some (relaSec, relas)))
    (hR : listGet? relas relaIdx = some r)
    (hSym : listGet? obj.syms r.rSymIdx = some sym)
    (hSec : listGet? obj.sections sym.stShndx = some sec)
    (hGrp : sectionHasGroup sec = true) :
    resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      none := by
  cases hRes :
      resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes with
  | none => rfl
  | some ref =>
    have hA := resolvePc32RodataReloc_sound_at hRes hP hRs hR
    have hGrpFalse := ((hA.2 sym hSym).2.2 sec hSec).2.1
    rw [hGrp] at hGrpFalse
    exact Bool.noConfusion hGrpFalse

/-- Negative rejection: any non-`R_X86_64_PC32` relocation (including
`R_X86_64_IRELATIVE` and `R_X86_64_32S`) is rejected fail-closed. -/
theorem resolvePc32RodataReloc_rejects_non_pc32 (bs : List UInt8)
    (obj : ParsedElf64Object) (relaSec : Elf64SectionHdr)
    (relas : List Elf64Rela) (r : Elf64Rela)
    (textSecIdx relaIdx insnEnd accessBytes : Nat)
    (hP : parseElf64Object? bs = some obj)
    (hRs : findUniqueRelaForTarget? obj.relaSections textSecIdx =
      some (some (relaSec, relas)))
    (hR : listGet? relas relaIdx = some r)
    (hne : r.rType ≠ rX86_64_PC32) :
    resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      none := by
  cases hRes :
      resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes with
  | none => rfl
  | some ref =>
    have hA := resolvePc32RodataReloc_sound_at hRes hP hRs hR
    exact False.elim (hne hA.1)

/-- Negative rejection: any `SHT_RELA` section targeting the resolved `.rodata`
section (`shInfo = sym.stShndx`) is rejected fail-closed. -/
theorem resolvePc32RodataReloc_rejects_rela_targeting_rodata (bs : List UInt8)
    (obj : ParsedElf64Object) (relaSec : Elf64SectionHdr)
    (relas : List Elf64Rela) (r : Elf64Rela)
    (textSecIdx relaIdx insnEnd accessBytes : Nat) (sym : Elf64Sym)
    (roRela : Nat × Elf64SectionHdr × List Elf64Rela)
    (hP : parseElf64Object? bs = some obj)
    (hRs : findUniqueRelaForTarget? obj.relaSections textSecIdx =
      some (some (relaSec, relas)))
    (hR : listGet? relas relaIdx = some r)
    (hSym : listGet? obj.syms r.rSymIdx = some sym)
    (hRoRelaMem : roRela ∈ obj.relaSections)
    (hRoRelaInfo : roRela.2.1.shInfo = sym.stShndx) :
    resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      none := by
  cases hRes :
      resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes with
  | none => rfl
  | some ref =>
    have hA := resolvePc32RodataReloc_sound_at hRes hP hRs hR
    exact False.elim ((hA.2 sym hSym).2.1 roRela hRoRelaMem hRoRelaInfo)

/-- Negative rejection: any `STT_GNU_IFUNC` symbol anywhere in `obj.syms`
rejects all relocations fail-closed. -/
theorem resolvePc32RodataReloc_rejects_ifunc (bs : List UInt8)
    (obj : ParsedElf64Object) (sym : Elf64Sym)
    (textSecIdx relaIdx insnEnd accessBytes : Nat)
    (hP : parseElf64Object? bs = some obj)
    (hMem : sym ∈ obj.syms) (hIf : sym.stType = sttGnuIfunc) :
    resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      none := by
  have hSymIf : symIsIfunc sym = true := by
    dsimp only [symIsIfunc]
    rw [hIf]
    rfl
  have hAny : listAny symIsIfunc obj.syms = true :=
    relocListAnyOfMem symIsIfunc obj.syms sym hMem hSymIf
  have hBad : (listAny sectionIsForbidden obj.sections ||
      listAny symIsIfunc obj.syms ||
      listAny relaIsIRelative obj.allRelas ||
      !allExecRelaTypesAllowed obj textSecIdx) = true := by
    rw [hAny]
    cases listAny sectionIsForbidden obj.sections <;> rfl
  dsimp only [resolvePc32RodataReloc]
  rw [hP]; dsimp only
  rw [relocIteTrue hBad]

/-- Negative rejection: any `.init_array` (`SHT_INIT_ARRAY`) section anywhere
in the parsed ELF64 object rejects all relocations fail-closed. -/
theorem resolvePc32RodataReloc_rejects_init_array (bs : List UInt8)
    (obj : ParsedElf64Object) (sec : Elf64SectionHdr)
    (textSecIdx relaIdx insnEnd accessBytes : Nat)
    (hP : parseElf64Object? bs = some obj)
    (hMem : sec ∈ obj.sections) (hInit : sec.shType = shtInitArray) :
    resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      none := by
  have hForb : sectionIsForbidden sec = true := by
    dsimp only [sectionIsForbidden]
    rw [hInit]
    rfl
  have hAny : listAny sectionIsForbidden obj.sections = true :=
    relocListAnyOfMem sectionIsForbidden obj.sections sec hMem hForb
  have hBad : (listAny sectionIsForbidden obj.sections ||
      listAny symIsIfunc obj.syms ||
      listAny relaIsIRelative obj.allRelas ||
      !allExecRelaTypesAllowed obj textSecIdx) = true := by
    rw [hAny]; rfl
  dsimp only [resolvePc32RodataReloc]
  rw [hP]; dsimp only
  rw [relocIteTrue hBad]

/-- Negative rejection: any out-of-bounds effective offset
(`effOff + accessBytes > sec.shSize`) is rejected fail-closed. -/
theorem resolvePc32RodataReloc_rejects_oob (bs : List UInt8)
    (obj : ParsedElf64Object) (relaSec : Elf64SectionHdr)
    (relas : List Elf64Rela) (r : Elf64Rela)
    (textSecIdx relaIdx insnEnd accessBytes : Nat)
    (sym : Elf64Sym) (sec : Elf64SectionHdr) (effOff : Nat)
    (hP : parseElf64Object? bs = some obj)
    (hRs : findUniqueRelaForTarget? obj.relaSections textSecIdx =
      some (some (relaSec, relas)))
    (hR : listGet? relas relaIdx = some r)
    (hSym : listGet? obj.syms r.rSymIdx = some sym)
    (hSec : listGet? obj.sections sym.stShndx = some sec)
    (hOff : intToNat? (Int.ofNat sym.stValue + r.rAddend +
      (Int.ofNat insnEnd - Int.ofNat r.rOffset)) = some effOff)
    (hOob : sec.shSize < effOff + accessBytes) :
    resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      none := by
  cases hRes :
      resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes with
  | none => rfl
  | some ref =>
    have hA := resolvePc32RodataReloc_sound_at hRes hP hRs hR
    have hFacts := (hA.2 sym hSym).2.2 sec hSec
    have hOff' := hFacts.2.2.1
    have hLe' := hFacts.2.2.2.1
    rw [hOff] at hOff'
    have hEffEq : effOff = ref.byteOff := Option.some.inj hOff'
    subst hEffEq
    exact False.elim (Nat.not_le_of_gt hOob hLe')

/-- Negative rejection: any `STT_SECTION` symbol targeting an `SHF_MERGE`
section is rejected fail-closed. -/
theorem resolvePc32RodataReloc_rejects_merge_section_sym (bs : List UInt8)
    (obj : ParsedElf64Object) (relaSec : Elf64SectionHdr)
    (relas : List Elf64Rela) (r : Elf64Rela)
    (textSecIdx relaIdx insnEnd accessBytes : Nat)
    (sym : Elf64Sym) (sec : Elf64SectionHdr)
    (hP : parseElf64Object? bs = some obj)
    (hRs : findUniqueRelaForTarget? obj.relaSections textSecIdx =
      some (some (relaSec, relas)))
    (hR : listGet? relas relaIdx = some r)
    (hSym : listGet? obj.syms r.rSymIdx = some sym)
    (hSec : listGet? obj.sections sym.stShndx = some sec)
    (hMerge : sectionHasMerge sec = true)
    (hSecSym : sym.stType = sttSection) :
    resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes =
      none := by
  cases hRes :
      resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd accessBytes with
  | none => rfl
  | some ref =>
    have hA := resolvePc32RodataReloc_sound_at hRes hP hRs hR
    have hMb := ((hA.2 sym hSym).2.2 sec hSec).2.2.2.2
    have hFalse :
        mergeEntryBoundsOk sec sym ref.byteOff accessBytes = false := by
      dsimp only [mergeEntryBoundsOk, symIsSection]
      rw [hMerge, hSecSym]
      rfl
    rw [hFalse] at hMb
    exact Bool.noConfusion hMb

/-- Bridge soundness theorem linking raw-object `extractFuncPcRelRelocs?` to
`resolvePc32RodataReloc`: if `extractFuncPcRelRelocs?` succeeds on `bs` for
`textSecIdx`, then `parseElf64Object? bs = some obj` passes whole-object
hygiene, `allExecRelaTypesAllowed obj textSecIdx = true`,
`obj.sections[textSecIdx]` is a validated executable `PROGBITS` code section
with `funcOff + funcSize ≤ textSec.shSize`, at most one non-COMDAT
`SHT_RELA` section targets `textSecIdx`, and EVERY overlapping relocation `r`
in EVERY parsed `SHT_RELA` section targeting `textSecIdx` is a strictly
contained `R_X86_64_PC32` (`r_sym ≠ 0`, `0 < st_shndx < 0xFF00`) whose target
`.rodata` section has ZERO `SHT_RELA` sections targeting it, resolving via
`resolvePc32RodataReloc` whenever no sibling relocation overlaps its 4-byte
slot and `(insnEnd, accessBytes)` lies inside the target section (and single
`SHF_MERGE` entry). -/
theorem extractFuncPcRelRelocs?_resolves_overlapping (bs : List UInt8)
    (textSecIdx funcOff funcSize : Nat)
    (out : List PcRelReloc)
    (hExt : extractFuncPcRelRelocs? bs textSecIdx funcOff funcSize =
      some out) :
    objectHasNoForbiddenElfFeatures bs = true ∧
    ∃ obj textSec,
      parseElf64Object? bs = some obj ∧
      allExecRelaTypesAllowed obj textSecIdx = true ∧
      listGet? obj.sections textSecIdx = some textSec ∧
      sectionIsExecText textSec = true ∧
      funcOff + funcSize ≤ textSec.shSize ∧
      ∀ entry, entry ∈ obj.relaSections → entry.2.1.shInfo = textSecIdx →
        entry.2.1.shType = shtRela ∧
        sectionHasGroup entry.2.1 = false ∧
        ∀ relaIdx r, listGet? entry.2.2 relaIdx = some r →
          relaDisjointFromFunc funcOff funcSize r = false →
          r.rType = rX86_64_PC32 ∧
          r.rSymIdx ≠ stnUndef ∧
          funcOff ≤ r.rOffset ∧
          r.rOffset + 4 ≤ funcOff + funcSize ∧
          ∃ sym sec,
            listGet? obj.syms r.rSymIdx = some sym ∧
            shndxIsDefinedRegular sym.stShndx = true ∧
            listGet? obj.sections sym.stShndx = some sec ∧
            hasRelaTargetingSection obj.relaSections sym.stShndx = false ∧
            (∀ roE, roE ∈ obj.relaSections → roE.2.1.shInfo ≠ sym.stShndx) ∧
            ∀ insnEnd accessBytes effOff,
              otherRelaOverlapsPc32 entry.2.2 relaIdx r.rOffset = false →
              intToNat? (Int.ofNat sym.stValue + r.rAddend +
                (Int.ofNat insnEnd - Int.ofNat r.rOffset)) = some effOff →
              effOff + accessBytes ≤ sec.shSize →
              mergeEntryBoundsOk sec sym effOff accessBytes = true →
              resolvePc32RodataReloc bs textSecIdx relaIdx insnEnd
                accessBytes =
                some { secIdx := sym.stShndx, byteOff := effOff,
                       accessBytes := accessBytes } := by
  dsimp only [extractFuncPcRelRelocs?] at hExt
  revert hExt
  cases hP : parseElf64Object? bs with
  | none => intro hExt; nomatch hExt
  | some obj =>
    intro hExt; dsimp only at hExt
    cases hBad : (listAny sectionIsForbidden obj.sections ||
        listAny symIsIfunc obj.syms ||
        listAny relaIsIRelative obj.allRelas ||
        !allExecRelaTypesAllowed obj textSecIdx) with
    | true => rw [relocIteTrue hBad] at hExt; nomatch hExt
    | false =>
      rw [relocIteFalse hBad] at hExt
      have hBad3 := (relocBorFalse hBad).1
      have hExecOk : allExecRelaTypesAllowed obj textSecIdx = true :=
        relocBoolTrueOfNotFalse (relocBorFalse hBad).2
      have hBadL := (relocBorFalse hBad3).1
      have hNoIR := (relocBorFalse hBad3).2
      have hNoForb := (relocBorFalse hBadL).1
      have hNoIf := (relocBorFalse hBadL).2
      have hHyg : objectHasNoForbiddenElfFeatures bs = true := by
        dsimp only [objectHasNoForbiddenElfFeatures]
        rw [hP]; dsimp only
        rw [hNoForb, hNoIf, hNoIR,
          allExecRelaFootprintsInBounds_of_allowed obj textSecIdx hExecOk]; rfl
      revert hExt
      cases hText : listGet? obj.sections textSecIdx with
      | none => intro hExt; nomatch hExt
      | some textSec =>
        intro hExt; dsimp only at hExt
        cases hTextBad : (!sectionIsExecText textSec ||
            !Nat.ble (funcOff + funcSize) textSec.shSize) with
        | true => rw [relocIteTrue hTextBad] at hExt; nomatch hExt
        | false =>
          rw [relocIteFalse hTextBad] at hExt
          have hTextOk := relocBorFalse hTextBad
          have hExec : sectionIsExecText textSec = true :=
            relocBoolTrueOfNotFalse hTextOk.1
          have hFuncLe : funcOff + funcSize ≤ textSec.shSize :=
            Nat.le_of_ble_eq_true (relocBoolTrueOfNotFalse hTextOk.2)
          revert hExt
          cases hRs : findUniqueRelaForTarget? obj.relaSections textSecIdx with
          | none => intro hExt; nomatch hExt
          | some optP =>
            intro hExt
            cases optP with
            | none =>
              refine ⟨hHyg, ⟨obj, textSec, rfl, hExecOk, hText, hExec, hFuncLe,
                ?_⟩⟩
              intro entry hE hInfo
              have hUniq := findUniqueRelaForTarget?_unique obj.relaSections
                textSecIdx none hRs entry hE hInfo
              nomatch hUniq
            | some p =>
              cases p with
              | mk relaSec relas =>
                dsimp only at hExt
                cases hHdr : (!Nat.beq relaSec.shType shtRela ||
                              !Nat.beq relaSec.shInfo textSecIdx ||
                              sectionHasGroup relaSec) with
                | true => rw [relocIteTrue hHdr] at hExt; nomatch hExt
                | false =>
                  rw [relocIteFalse hHdr] at hExt
                  have hHdrL := (relocBorFalse hHdr).1
                  have hRelaNoGrp := (relocBorFalse hHdr).2
                  have hHdrOk := relocBorFalse hHdrL
                  have hTySec := relocNatEqOfBeq relaSec.shType shtRela
                    (relocBoolTrueOfNotFalse hHdrOk.1)
                  have hFold : ∀ (rs : List Elf64Rela) (res : List PcRelReloc),
                      List.foldr
                        (fun r acc =>
                          match acc with
                          | none => none
                          | some out =>
                            if relaDisjointFromFunc funcOff funcSize r then
                              some out
                            else if !Nat.beq r.rType rX86_64_PC32 ||
                                    Nat.beq r.rSymIdx stnUndef then none
                            else if !Nat.ble funcOff r.rOffset ||
                                    !Nat.ble (r.rOffset + 4)
                                      (funcOff + funcSize) then
                              none
                            else
                              match listGet? obj.syms r.rSymIdx with
                              | none => none
                              | some sym =>
                                if symIsIfunc sym || !symIsLocalBinding sym ||
                                   !shndxIsDefinedRegular sym.stShndx then
                                  none
                                else
                                  match listGet? obj.sections sym.stShndx with
                                  | none => none
                                  | some sec =>
                                    if !sectionIsReadOnlyRodata sec ||
                                       (sectionHasMerge sec &&
                                         symIsSection sym) ||
                                       hasRelaTargetingSection obj.relaSections
                                         sym.stShndx then
                                      none
                                    else
                                      let pr : PcRelReloc := {
                                        offset := r.rOffset - funcOff
                                        secIdx := sym.stShndx
                                        target :=
                                          Int.ofNat sym.stValue + r.rAddend
                                      }
                                      some (pr :: out))
                        (some []) rs = some res →
                      ∀ r, r ∈ rs →
                        relaDisjointFromFunc funcOff funcSize r = false →
                        r.rType = rX86_64_PC32 ∧
                        r.rSymIdx ≠ stnUndef ∧
                        funcOff ≤ r.rOffset ∧
                        r.rOffset + 4 ≤ funcOff + funcSize ∧
                        ∃ sym sec,
                          listGet? obj.syms r.rSymIdx = some sym ∧
                          listGet? obj.sections sym.stShndx = some sec ∧
                          (symIsIfunc sym || !symIsLocalBinding sym ||
                            !shndxIsDefinedRegular sym.stShndx) = false ∧
                          sectionIsReadOnlyRodata sec = true ∧
                          hasRelaTargetingSection obj.relaSections sym.stShndx =
                            false := by
                    intro rs
                    induction rs with
                    | nil =>
                      intro _ _ _ hMem
                      nomatch hMem
                    | cons hd tl ih =>
                      intro res hF r hMem hNotDisj
                      dsimp only [List.foldr] at hF
                      revert hF
                      cases hTl : List.foldr
                          (fun r acc =>
                            match acc with
                            | none => none
                            | some out =>
                              if relaDisjointFromFunc funcOff funcSize r then
                                some out
                              else if !Nat.beq r.rType rX86_64_PC32 ||
                                      Nat.beq r.rSymIdx stnUndef then none
                              else if !Nat.ble funcOff r.rOffset ||
                                      !Nat.ble (r.rOffset + 4)
                                        (funcOff + funcSize) then
                                none
                              else
                                match listGet? obj.syms r.rSymIdx with
                                | none => none
                                | some sym =>
                                  if symIsIfunc sym ||
                                     !symIsLocalBinding sym ||
                                     !shndxIsDefinedRegular sym.stShndx then
                                    none
                                  else
                                    match listGet? obj.sections sym.stShndx with
                                    | none => none
                                    | some sec =>
                                      if !sectionIsReadOnlyRodata sec ||
                                         (sectionHasMerge sec &&
                                           symIsSection sym) ||
                                         hasRelaTargetingSection
                                           obj.relaSections sym.stShndx then
                                        none
                                      else
                                        let pr : PcRelReloc := {
                                          offset := r.rOffset - funcOff
                                          secIdx := sym.stShndx
                                          target :=
                                            Int.ofNat sym.stValue + r.rAddend
                                        }
                                        some (pr :: out))
                          (some []) tl with
                      | none => intro hF; nomatch hF
                      | some tlOut =>
                        intro hF; dsimp only at hF
                        cases hMem with
                        | tail _ hInTl => exact ih tlOut hTl r hInTl hNotDisj
                        | head _ =>
                          rw [relocIteFalse hNotDisj] at hF
                          cases hPcBad : (!Nat.beq hd.rType rX86_64_PC32 ||
                              Nat.beq hd.rSymIdx stnUndef) with
                          | true => rw [relocIteTrue hPcBad] at hF; nomatch hF
                          | false =>
                            rw [relocIteFalse hPcBad] at hF
                            have hPcOk := relocBorFalse hPcBad
                            revert hF
                            cases hStrad : (!Nat.ble funcOff hd.rOffset ||
                                !Nat.ble (hd.rOffset + 4)
                                  (funcOff + funcSize)) with
                            | true => intro hF; nomatch hF
                            | false =>
                              intro hF; rw [relocIteFalse rfl] at hF
                              have hStrOk := relocBorFalse hStrad
                              revert hF
                              cases hSym : listGet? obj.syms hd.rSymIdx with
                              | none => intro hF; nomatch hF
                              | some sym =>
                                intro hF; dsimp only at hF
                                cases hSB :
                                    (symIsIfunc sym ||
                                      !symIsLocalBinding sym ||
                                      !shndxIsDefinedRegular sym.stShndx) with
                                | true =>
                                  rw [relocIteTrue hSB] at hF; nomatch hF
                                | false =>
                                  rw [relocIteFalse hSB] at hF
                                  revert hF
                                  cases hSec :
                                      listGet? obj.sections sym.stShndx with
                                  | none => intro hF; nomatch hF
                                  | some sec =>
                                    intro hF; dsimp only at hF
                                    revert hF
                                    cases hSecBad :
                                        (!sectionIsReadOnlyRodata sec ||
                                         (sectionHasMerge sec &&
                                           symIsSection sym) ||
                                         hasRelaTargetingSection
                                           obj.relaSections sym.stShndx) with
                                    | true => intro hF; nomatch hF
                                    | false =>
                                      intro hF
                                      have hSecBadP := relocBorFalse hSecBad
                                      have hSecBadL :=
                                        relocBorFalse hSecBadP.1
                                      have hRo :
                                          sectionIsReadOnlyRodata sec = true :=
                                        relocBoolTrueOfNotFalse hSecBadL.1
                                      exact ⟨relocNatEqOfBeq hd.rType
                                        rX86_64_PC32
                                        (relocBoolTrueOfNotFalse hPcOk.1),
                                        relocNatNeOfBeqFalse hPcOk.2,
                                        Nat.le_of_ble_eq_true
                                          (relocBoolTrueOfNotFalse hStrOk.1),
                                        Nat.le_of_ble_eq_true
                                          (relocBoolTrueOfNotFalse hStrOk.2),
                                        ⟨sym, sec, rfl, hSec, hSB, hRo,
                                         hSecBadP.2⟩⟩
                  refine ⟨hHyg, ⟨obj, textSec, rfl, hExecOk, hText, hExec,
                    hFuncLe, ?_⟩⟩
                  intro entry hE hInfo
                  have hUniq := findUniqueRelaForTarget?_unique obj.relaSections
                    textSecIdx (some (relaSec, relas)) hRs entry hE hInfo
                  have hPairEq : (relaSec, relas) = entry.2 :=
                    Option.some.inj hUniq
                  cases entry with
                  | mk eIdx ePair =>
                    cases ePair with
                    | mk eSec eRelas =>
                      dsimp only at hPairEq
                      injection hPairEq with hSecEq hRelasEq
                      subst hSecEq
                      subst hRelasEq
                      refine ⟨hTySec, hRelaNoGrp, ?_⟩
                      intro relaIdx r hGetR hNotDisj
                      have hMem := relocListGetMem relas relaIdx r hGetR
                      have hQ := hFold relas out hExt r hMem hNotDisj
                      have ⟨hTyQ, hSymNeQ, hOffLo, hOffHi, sym, sec, hSymQ,
                            hSecQ, hSBQ, hRoQ, hNoRoRelaQ⟩ := hQ
                      have hShndxQ : shndxIsDefinedRegular sym.stShndx = true :=
                        relocBoolTrueOfNotFalse (relocBorFalse hSBQ).2
                      refine ⟨hTyQ, hSymNeQ, hOffLo, hOffHi,
                        ⟨sym, sec, hSymQ, hShndxQ, hSecQ, hNoRoRelaQ,
                         hasRelaTargetingSection_false_imp obj.relaSections
                           sym.stShndx hNoRoRelaQ, ?_⟩⟩
                      intro insnEnd accessBytes effOff hNoOv hOff hLe hMerge
                      dsimp only [resolvePc32RodataReloc]
                      rw [hP]; dsimp only
                      rw [relocIteFalse hBad, hText]; dsimp only
                      rw [hExec, relocIteFalse (rfl : (!true) = false), hRs]
                      dsimp only
                      rw [relocIteFalse hHdr, hGetR]
                      dsimp only
                      have hTyBeq : Nat.beq r.rType rX86_64_PC32 = true := by
                        rw [hTyQ]; rfl
                      have hSymZero : Nat.beq r.rSymIdx stnUndef = false :=
                        relocNatBeqFalseOfNe hSymNeQ
                      have hRTyF : (!Nat.beq r.rType rX86_64_PC32 ||
                          Nat.beq r.rSymIdx stnUndef ||
                          otherRelaOverlapsPc32 relas relaIdx r.rOffset) =
                          false := by
                        rw [hTyBeq, hSymZero, hNoOv]; rfl
                      rw [relocIteFalse hRTyF, hSymQ]
                      dsimp only
                      rw [relocIteFalse hSBQ, hSecQ]
                      dsimp only
                      have hRoBadF : (!sectionIsReadOnlyRodata sec ||
                          hasRelaTargetingSection obj.relaSections
                            sym.stShndx) = false := by
                        rw [hRoQ, hNoRoRelaQ]; rfl
                      rw [relocIteFalse hRoBadF, hOff]
                      dsimp only
                      have hBle :
                          Nat.ble (effOff + accessBytes) sec.shSize = true :=
                        Nat.ble_eq_true_of_le hLe
                      have hCond :
                          (Nat.ble (effOff + accessBytes) sec.shSize &&
                            mergeEntryBoundsOk sec sym effOff accessBytes)
                            = true := by
                        rw [hBle, hMerge]; rfl
                      rw [relocIteTrue hCond]

private theorem listDrop_nil {α : Type} (n : Nat) :
    ([] : List α).drop n = [] := by
  cases n <;> rfl

private theorem listDrop_eq_drop {α : Type} :
    ∀ (n : Nat) (xs : List α), listDrop n xs = xs.drop n := by
  intro n
  induction n with
  | zero => intro xs; cases xs <;> rfl
  | succ k ih =>
    intro xs
    cases xs with
    | nil => rfl
    | cons _ tl => exact ih tl

private theorem listTake_eq_take {α : Type} :
    ∀ (n : Nat) (xs : List α), listTake n xs = xs.take n := by
  intro n
  induction n with
  | zero => intro xs; cases xs <;> rfl
  | succ k ih =>
    intro xs
    cases xs with
    | nil => rfl
    | cons x tl => exact congrArg (List.cons x) (ih tl)

private theorem listDrop_add {α : Type} :
    ∀ (a b : Nat) (xs : List α), (xs.drop a).drop b = xs.drop (a + b) := by
  intro a
  induction a with
  | zero =>
    intro b xs
    rw [Nat.zero_add]
    rfl
  | succ k ih =>
    intro b xs
    rw [Nat.succ_add]
    cases xs with
    | nil => exact listDrop_nil b
    | cons _ tl => exact ih b tl

private theorem drop8_eq_drop :
    ∀ (q : Nat) (xs : List UInt8),
      fastDropBytes8 q xs = xs.drop (8 * q) := by
  intro q
  induction q with
  | zero => intro xs; rfl
  | succ k ih =>
    intro xs
    dsimp only [fastDropBytes8]
    have hMul : 8 * (k + 1) = 8 + 8 * k := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [hMul, ← listDrop_add]
    cases xs with
    | nil => exact (listDrop_nil (8 * k)).symm
    | cons _ r1 => cases r1 with
      | nil => exact (listDrop_nil (8 * k)).symm
      | cons _ r2 => cases r2 with
        | nil => exact (listDrop_nil (8 * k)).symm
        | cons _ r3 => cases r3 with
          | nil => exact (listDrop_nil (8 * k)).symm
          | cons _ r4 => cases r4 with
            | nil => exact (listDrop_nil (8 * k)).symm
            | cons _ r5 => cases r5 with
              | nil => exact (listDrop_nil (8 * k)).symm
              | cons _ r6 => cases r6 with
                | nil => exact (listDrop_nil (8 * k)).symm
                | cons _ r7 => cases r7 with
                  | nil => exact (listDrop_nil (8 * k)).symm
                  | cons _ rest => exact ih rest

private theorem fastDropBytes_eq_drop (n : Nat) (bs : List UInt8) :
    fastDropBytes n bs = bs.drop n := by
  dsimp only [fastDropBytes]
  have hDm : 8 * Nat.div n 8 + Nat.mod n 8 = n := Nat.div_add_mod n 8
  rw [listDrop_eq_drop, drop8_eq_drop, listDrop_add, hDm]

private theorem drop_cons_le {α : Type} :
    ∀ (k : Nat) (xs : List α) (b : α) (tl : List α),
      xs.drop k = b :: tl → k + 1 ≤ xs.length := by
  intro k
  induction k with
  | zero =>
    intro xs b tl h
    cases xs with
    | nil => nomatch h
    | cons _ rest => exact Nat.succ_le_succ (Nat.zero_le rest.length)
  | succ k' ih =>
    intro xs b tl h
    cases xs with
    | nil => nomatch h
    | cons _ rest => exact Nat.succ_le_succ (ih rest b tl h)

private theorem bytesLenAtLeast_le (n : Nat) (bs : List UInt8)
    (h : bytesLenAtLeast n bs = true) : n ≤ bs.length := by
  cases n with
  | zero => exact Nat.zero_le bs.length
  | succ k =>
    dsimp only [bytesLenAtLeast] at h
    have hZ : Nat.beq (k + 1) 0 = false := rfl
    rw [relocIteFalse hZ] at h
    have hSub : k + 1 - 1 = k := rfl
    rw [hSub, fastDropBytes_eq_drop] at h
    revert h
    cases hD : bs.drop k with
    | nil => intro h; exact Bool.noConfusion h
    | cons b tl => intro h; exact drop_cons_le k bs b tl hD

private theorem drop_length_ge {α : Type} :
    ∀ (off len : Nat) (xs : List α),
      off + len ≤ xs.length → len ≤ (xs.drop off).length := by
  intro off
  induction off with
  | zero =>
    intro len xs h
    rw [Nat.zero_add] at h
    exact h
  | succ k ih =>
    intro len xs h
    cases xs with
    | nil =>
      rw [Nat.succ_add] at h
      exact False.elim (Nat.not_succ_le_zero (k + len) h)
    | cons _ tl =>
      rw [Nat.succ_add] at h
      exact ih len tl (Nat.le_of_succ_le_succ h)

private theorem take_length_of_le {α : Type} :
    ∀ (len : Nat) (xs : List α),
      len ≤ xs.length → (xs.take len).length = len := by
  intro len
  induction len with
  | zero => intro xs _; cases xs <;> rfl
  | succ k ih =>
    intro xs h
    cases xs with
    | nil => exact False.elim (Nat.not_succ_le_zero k h)
    | cons _ tl => exact congrArg Nat.succ (ih tl (Nat.le_of_succ_le_succ h))

/-- Exact specification of `sliceBytes?` (`[propext]` only, via `Nat.div`/
`Nat.mod` in `fastDropBytes`): whenever `sliceBytes? bs off len = some out`,
`[off, off + len)` lies within `bs`, `out = (bs.drop off).take len`, and
`out.length = len`. -/
theorem sliceBytes?_spec (bs : List UInt8) (off len : Nat)
    (out : List UInt8) (h : sliceBytes? bs off len = some out) :
    off + len ≤ bs.length ∧
    out = (bs.drop off).take len ∧
    out.length = len := by
  dsimp only [sliceBytes?] at h
  cases hLen : bytesLenAtLeast (off + len) bs with
  | false => rw [relocIteFalse hLen] at h; nomatch h
  | true =>
    rw [relocIteTrue hLen] at h
    injection h with hEq
    subst hEq
    have hLe : off + len ≤ bs.length := bytesLenAtLeast_le (off + len) bs hLen
    rw [listTake_eq_take, fastDropBytes_eq_drop]
    exact ⟨hLe, rfl, take_length_of_le len (bs.drop off)
      (drop_length_ge off len bs hLe)⟩

/-- Specification of `funcTextBytes?` (`[propext]` only, via `Nat.div`/
`Nat.mod`/`UInt8` in `parseElf64Object?` and `fastDropBytes`): whenever
`funcTextBytes? bs textSecIdx funcOff funcSize = some textBytes`, `bs` passes
whole-object hygiene, `parseElf64Object? bs = some obj`, all relocations in any
`SHT_RELA` targeting `textSecIdx` belong to the non-relaxable allowlist,
`obj.sections[textSecIdx]` is a validated executable `PROGBITS` code section
(`sectionIsExecText textSec = true`) with `funcOff + funcSize ≤ textSec.shSize`
and `textSec.shOffset + funcOff + funcSize ≤ bs.length`, and `textBytes` equals
the exact raw slice `(bs.drop (textSec.shOffset + funcOff)).take funcSize` of
length `funcSize`. -/
theorem funcTextBytes?_spec (bs : List UInt8)
    (textSecIdx funcOff funcSize : Nat) (textBytes : List UInt8)
    (h : funcTextBytes? bs textSecIdx funcOff funcSize = some textBytes) :
    objectHasNoForbiddenElfFeatures bs = true ∧
    ∃ obj textSec,
      parseElf64Object? bs = some obj ∧
      allExecRelaTypesAllowed obj textSecIdx = true ∧
      listGet? obj.sections textSecIdx = some textSec ∧
      sectionIsExecText textSec = true ∧
      funcOff + funcSize ≤ textSec.shSize ∧
      textSec.shOffset + funcOff + funcSize ≤ bs.length ∧
      textBytes = (bs.drop (textSec.shOffset + funcOff)).take funcSize ∧
      textBytes.length = funcSize := by
  dsimp only [funcTextBytes?] at h
  revert h
  cases hP : parseElf64Object? bs with
  | none => intro h; nomatch h
  | some obj =>
    intro h; dsimp only at h
    cases hBad : (listAny sectionIsForbidden obj.sections ||
        listAny symIsIfunc obj.syms ||
        listAny relaIsIRelative obj.allRelas ||
        !allExecRelaTypesAllowed obj textSecIdx) with
    | true => rw [relocIteTrue hBad] at h; nomatch h
    | false =>
      rw [relocIteFalse hBad] at h
      have hBad3 := (relocBorFalse hBad).1
      have hExecOk : allExecRelaTypesAllowed obj textSecIdx = true :=
        relocBoolTrueOfNotFalse (relocBorFalse hBad).2
      have hBadL := (relocBorFalse hBad3).1
      have hNoIR := (relocBorFalse hBad3).2
      have hNoForb := (relocBorFalse hBadL).1
      have hNoIf := (relocBorFalse hBadL).2
      have hHyg : objectHasNoForbiddenElfFeatures bs = true := by
        dsimp only [objectHasNoForbiddenElfFeatures]
        rw [hP]; dsimp only
        rw [hNoForb, hNoIf, hNoIR,
          allExecRelaFootprintsInBounds_of_allowed obj textSecIdx hExecOk]; rfl
      revert h
      cases hText : listGet? obj.sections textSecIdx with
      | none => intro h; nomatch h
      | some textSec =>
        intro h; dsimp only at h
        cases hTextBad : (!sectionIsExecText textSec ||
            !Nat.ble (funcOff + funcSize) textSec.shSize) with
        | true => rw [relocIteTrue hTextBad] at h; nomatch h
        | false =>
          rw [relocIteFalse hTextBad] at h
          have hTextOk := relocBorFalse hTextBad
          have hExec : sectionIsExecText textSec = true :=
            relocBoolTrueOfNotFalse hTextOk.1
          have hFuncLe : funcOff + funcSize ≤ textSec.shSize :=
            Nat.le_of_ble_eq_true (relocBoolTrueOfNotFalse hTextOk.2)
          have hSl := sliceBytes?_spec bs (textSec.shOffset + funcOff)
            funcSize textBytes h
          exact ⟨hHyg, ⟨obj, textSec, rfl, hExecOk, hText, hExec, hFuncLe,
            hSl.1, hSl.2.1, hSl.2.2⟩⟩

/-- Soundness of composed raw-ELF `decodeFuncFromElf?` (`[propext]` only):
any decoded trace enforces `cfg.requireRelocForRip = true`, comes from raw
ELF64 object `bs` passing whole-object hygiene and the target-section
relocation allowlist (`allExecRelaTypesAllowed obj textSecIdx = true`, so every
relocation against `textSecIdx` is `R_X86_64_PC32`), with `textBytes`
sliced directly from validated executable `PROGBITS` section `textSecIdx`
(`funcOff + funcSize ≤ shSize`), relocations extracted via
`extractFuncPcRelRelocs?`, exact 1-to-1 `localDecodeCoverageOk`, AND EVERY
decoded `.ripRel` operand in `tr` validated via `resolvePc32RodataReloc`
(`seg = none`, `addr32 = false`, non-negative `effOff = Int.ofNat ref.byteOff`,
`ref.byteOff + accBytes ≤ sec.shSize`, `mergeEntryBoundsOk`, and zero
`SHT_RELA` sections targeting `.rodata`). -/
theorem decodeFuncFromElf?_sound (cfg : DecodeConfig) (bs : List UInt8)
    (textSecIdx funcOff funcSize : Nat)
    (tr : List (Nat × Nat × DecodedInsn))
    (h : decodeFuncFromElf? cfg bs textSecIdx funcOff funcSize = some tr) :
    cfg.requireRelocForRip = true ∧
    objectHasNoForbiddenElfFeatures bs = true ∧
    ∃ textBytes relocs,
      funcTextBytes? bs textSecIdx funcOff funcSize = some textBytes ∧
      extractFuncPcRelRelocs? bs textSecIdx funcOff funcSize = some relocs ∧
      (∃ obj, parseElf64Object? bs = some obj ∧
        allExecRelaTypesAllowed obj textSecIdx = true) ∧
      localDecodeCoverageOk cfg relocs textBytes = true ∧
      decodeStream cfg relocs textBytes = some tr ∧
      ∀ off len ins, (off, len, ins) ∈ tr →
        ∀ seg a32 secOpt relocOffOpt effOff accBytes,
          insnMemOperandWithSize? ins =
            some (.ripRel seg a32 secOpt relocOffOpt effOff, accBytes) →
          seg = none ∧
          a32 = false ∧
          ∃ relocOff rIdx ref obj textSec relaSec relas r sym sec,
            relocOffOpt = some relocOff ∧
            resolvePc32RodataReloc bs textSecIdx rIdx (funcOff + off + len)
              accBytes = some ref ∧
            parseElf64Object? bs = some obj ∧
            listGet? obj.sections textSecIdx = some textSec ∧
            sectionIsExecText textSec = true ∧
            findUniqueRelaForTarget? obj.relaSections textSecIdx =
              some (some (relaSec, relas)) ∧
            listGet? relas rIdx = some r ∧
            r.rOffset = funcOff + relocOff ∧
            listGet? obj.syms r.rSymIdx = some sym ∧
            listGet? obj.sections sym.stShndx = some sec ∧
            sectionIsReadOnlyRodata sec = true ∧
            secOpt = some ref.secIdx ∧
            ref.secIdx = sym.stShndx ∧
            effOff = Int.ofNat ref.byteOff ∧
            ref.byteOff + accBytes ≤ sec.shSize ∧
            mergeEntryBoundsOk sec sym ref.byteOff accBytes = true ∧
            hasRelaTargetingSection obj.relaSections sym.stShndx = false ∧
            (∀ roE, roE ∈ obj.relaSections →
              roE.2.1.shInfo ≠ sym.stShndx) := by
  dsimp only [decodeFuncFromElf?] at h
  revert h
  cases hReq : cfg.requireRelocForRip with
  | false => intro h; nomatch h
  | true =>
    intro h; rw [relocIteFalse (rfl : (!true) = false)] at h
    revert h
    cases hBytes : funcTextBytes? bs textSecIdx funcOff funcSize with
    | none => intro h; nomatch h
    | some textBytes =>
      intro h; dsimp only at h
      revert h
      cases hRel : extractFuncPcRelRelocs? bs textSecIdx funcOff funcSize with
      | none => intro h; nomatch h
      | some relocs =>
        intro h; dsimp only at h
        revert h
        cases hCov : localDecodeCoverageOk cfg relocs textBytes with
        | false => intro h; nomatch h
        | true =>
          intro h; rw [relocIteFalse (rfl : (!true) = false)] at h
          revert h
          cases hDec : decodeStream cfg relocs textBytes with
          | none => intro h; nomatch h
          | some tr' =>
            intro h; dsimp only at h
            revert h
            cases hObj : parseElf64Object? bs with
            | none => intro h; nomatch h
            | some obj =>
              intro h; dsimp only at h
              revert h
              cases hRs :
                  findUniqueRelaForTarget? obj.relaSections textSecIdx with
              | none => intro h; nomatch h
              | some optRela =>
                intro h; dsimp only at h
                cases hAll : listAll (traceEntryRipRelocOk bs
                    (optRelaEntries optRela) textSecIdx funcOff) tr' with
                | false => rw [relocIteFalse hAll] at h; nomatch h
                | true =>
                  rw [relocIteTrue hAll] at h
                  injection h with hTrEq
                  subst hTrEq
                  have hHyg := (extractFuncPcRelRelocs?_resolves_overlapping bs
                    textSecIdx funcOff funcSize relocs hRel).1
                  have ⟨objE, _, hPE, hAlE, _⟩ :=
                    (extractFuncPcRelRelocs?_resolves_overlapping bs
                      textSecIdx funcOff funcSize relocs hRel).2
                  have hObjE : objE = obj :=
                    Option.some.inj (Eq.trans (Eq.symm hPE) hObj)
                  rw [hObjE] at hAlE
                  refine ⟨rfl, hHyg,
                    ⟨textBytes, relocs, rfl, rfl, ⟨obj, rfl, hAlE⟩, hCov, hDec,
                      ?_⟩⟩
                  intro off len ins hMem seg a32 secOpt relocOffOpt effOff
                    accBytes hOp
                  have hOk := relocListAllMem
                    (traceEntryRipRelocOk bs (optRelaEntries optRela)
                      textSecIdx funcOff)
                    tr' hAll (off, len, ins) hMem
                  dsimp only [traceEntryRipRelocOk] at hOk
                  rw [hOp] at hOk; dsimp only at hOk
                  cases seg with
                  | some s =>
                    have hSg : ((some s).isSome || a32) = true := rfl
                    rw [relocIteTrue hSg] at hOk
                    exact Bool.noConfusion hOk
                  | none =>
                    cases a32 with
                    | true =>
                      have hA32 :
                          ((none : Option SegReg).isSome || true) = true := rfl
                      rw [relocIteTrue hA32] at hOk
                      exact Bool.noConfusion hOk
                    | false =>
                      have hOk0 :
                          ((none : Option SegReg).isSome || false) = false :=
                        rfl
                      rw [relocIteFalse hOk0] at hOk
                      cases relocOffOpt with
                      | none => dsimp only at hOk; exact Bool.noConfusion hOk
                      | some relocOff =>
                        dsimp only at hOk
                        revert hOk
                        cases hIdx : findRelaIdxByOffset?
                            (optRelaEntries optRela) (funcOff + relocOff) with
                        | none => intro hOk; exact Bool.noConfusion hOk
                        | some rIdx =>
                          intro hOk; dsimp only at hOk
                          revert hOk
                          cases hGetR :
                              listGet? (optRelaEntries optRela) rIdx with
                          | none =>
                            intro hOk; exact Bool.noConfusion hOk
                          | some r =>
                            intro hOk; dsimp only at hOk
                            cases hOffEq :
                                Nat.beq r.rOffset (funcOff + relocOff) with
                            | false =>
                              rw [hOffEq] at hOk; exact Bool.noConfusion hOk
                            | true =>
                              rw [hOffEq,
                                  relocIteFalse (rfl : (!true) = false)] at hOk
                              revert hOk
                              cases hRes : resolvePc32RodataReloc bs textSecIdx
                                  rIdx (funcOff + off + len) accBytes with
                              | none =>
                                intro hOk; exact Bool.noConfusion hOk
                              | some ref =>
                                intro hOk; dsimp only at hOk
                                have hSecOptEq : secOpt = some ref.secIdx :=
                                  relocOptNatEqOfBeq secOpt (some ref.secIdx)
                                    (relocBandLeft hOk)
                                have hEffEq : effOff = Int.ofNat ref.byteOff :=
                                  relocIntEqOfBeq effOff (Int.ofNat ref.byteOff)
                                    (relocBandRight hOk)
                                have hS := resolvePc32RodataReloc_sound bs
                                  textSecIdx rIdx (funcOff + off + len) accBytes
                                  ref hRes
                                have ⟨obj', textSec', relaSec', relas', r',
                                      sym', sec', hP', hText', hExec', hRs', _,
                                      _, hR', _, _, hSym', _, hSec', _, _, _,
                                      hRo', hRefSec', _, hLe', hMb', _,
                                      hNoRoRela', hNoRoImp', _⟩ := hS.2
                                rw [hObj] at hP'
                                have hObjEq : obj = obj' := Option.some.inj hP'
                                subst hObjEq
                                rw [hRs] at hRs'
                                have hOptEq :
                                    optRela = some (relaSec', relas') :=
                                  Option.some.inj hRs'
                                subst hOptEq
                                dsimp only [optRelaEntries] at hGetR
                                rw [hGetR] at hR'
                                have hREq : r = r' := Option.some.inj hR'
                                subst hREq
                                exact ⟨rfl, rfl, ⟨relocOff, rIdx, ref, obj,
                                  textSec', relaSec', relas', r, sym', sec',
                                  rfl, hRes, rfl, hText', hExec', hRs, hGetR,
                                  relocNatEqOfBeq r.rOffset (funcOff + relocOff)
                                    hOffEq,
                                  hSym', hSec', hRo', hSecOptEq, hRefSec',
                                  hEffEq, hLe', hMb', hNoRoRela', hNoRoImp'⟩⟩

end Anneal.ElfX86
end
