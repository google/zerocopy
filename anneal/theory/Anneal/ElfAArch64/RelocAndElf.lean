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
public import Anneal.ElfAArch64.Decode

public section
namespace Anneal.ElfAArch64

/-!
# Computable ELF64 `EM_AARCH64` Object Parser & Relocation Gate
(`Anneal.ElfAArch64.RelocAndElf`)

Pure Pass-1 (`0` `._unsafe_rec`, `0` `partial`, `0` `noncomputable`, axioms
`⊆ {propext}`) ELF64 little-endian `ET_REL` `EM_AARCH64` (183) object parser,
section/relocation hygiene checker, and read-only `.rodata` resolver:

- **Complete ELF64 header identity validation (`parseElf64Header?`):**
  enforces `\x7fELF`, `ELFCLASS64`, `ELFDATA2LSB`, `EI_VERSION = 1`,
  `EI_OSABI ∈ {0, 3}`, `EI_ABIVERSION = 0`, zero `EI_PAD[9..15]`,
  `ET_REL = 1`, `EM_AARCH64 = 183`, `e_version = 1`, `e_flags = 0`, exact
  `e_ehsize = 64`, exact `e_shentsize = 64`, `0 < e_shnum`,
  `e_shstrndx < e_shnum`, and in-bounds section header table.
- **Whole-object raw-byte parser (`parseElf64Object?`):** derives all
  `e_shnum` section headers with `.shstrtab` names, the unique `SHT_SYMTAB`
  with linked `SHT_STRTAB` names, and all `SHT_RELA` sections (rejecting
  `SHT_DYNSYM`, `SHT_REL`, `SHT_RELR`, `SHF_COMPRESSED` on
  `.shstrtab`/`.symtab`/`.strtab`/`SHT_RELA`, duplicate `SHT_SYMTAB`, or
  duplicate `SHT_RELA` targeting the same section).
- **Raw-object-bound gates (`objectHasNoForbiddenElfFeatures`,
  `resolveAArch64RodataReloc`, `extractFuncRodataRelocs?`,
  `funcTextBytes?`, `decodeFuncFromElf?`):** consume raw object bytes
  `bs : List UInt8` directly via `parseElf64Object? bs`, enforcing all-zero
  `STN_UNDEF` `sym[0]` and non-zero `r_sym`, rejecting `SHT_GROUP`,
  `.init_array*`, `.fini_array*`, `.preinit_array*`, `.ctors*`, `.dtors*`,
  `.init*`, `.fini*`, `W+X` sections, `STT_GNU_IFUNC`, `STT_TLS` and other
  non-allowlisted symbol types, `R_AARCH64_IRELATIVE` (1032), non-`STB_LOCAL`,
  non-allowlisted `.text`/`.rodata` flags (`SHF_WRITE`, `SHF_GROUP`,
  `SHF_TLS`, `SHF_COMPRESSED`, `SHF_EXCLUDE`, `SHF_STRINGS`), `.rodata`
  targeted by `SHT_RELA`, duplicate or overlapping sibling relocations,
  misaligned `effOff` or `sh_addralign` on scaled `LDST64`/`LDST128`
  relocations, `STT_SECTION` anchors into `SHF_MERGE`, and partial or
  cross-entry `SHF_MERGE` escapes, while enforcing 4-byte instruction
  alignment on `funcOff` and `funcSize` and `cfg.requireRelocForPcRel = true`
  on `ET_REL` objects. -/

/-! ## 1. Chunked Little-Endian Byte & String-Table Readers -/

/-- Drop 8 bytes per step (`@Nat.rec` on `n / 8`, then `n % 8`) to keep
kernel reduction shallow on real ELF64 object images. -/
@[expose] def fastDropBytes (n : Nat) (bs : List UInt8) : List UInt8 :=
  let drop8 : List UInt8 → List UInt8 :=
    @Nat.rec (fun _ => List UInt8 → List UInt8)
      (fun xs => xs)
      (fun _ ih xs =>
        match xs with
        | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => ih rest
        | _ => [])
      (Nat.div n 8)
  listDrop (Nat.mod n 8) (drop8 bs)

/-- True iff `bs` has at least `n` bytes. -/
@[expose] def bytesLenAtLeast (n : Nat) (bs : List UInt8) : Bool :=
  if Nat.beq n 0 then true
  else
    match fastDropBytes (n - 1) bs with
    | _ :: _ => true
    | [] => false

/-- Take 8 bytes per step (`@Nat.rec` on `n / 8`, then `n % 8`) to keep
kernel & elaborator reduction shallow on real ELF64 object images. -/
@[expose] def fastTakeBytes (n : Nat) (bs : List UInt8) : List UInt8 :=
  let take8 : List UInt8 → List UInt8 :=
    @Nat.rec (fun _ => List UInt8 → List UInt8)
      (fun xs => listTake (Nat.mod n 8) xs)
      (fun _ ih xs =>
        match xs with
        | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
          b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: ih rest
        | other => other)
      (Nat.div n 8)
  take8 bs

/-- Bounds-checked byte slice `[off, off + len)`. -/
@[expose] def sliceBytes? (bs : List UInt8) (off len : Nat) :
    Option (List UInt8) :=
  if bytesLenAtLeast (off + len) bs then
    some (fastTakeBytes len (fastDropBytes off bs))
  else none

/-- Read a single byte at offset `off`. -/
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

/-- Bounded `@Nat.rec` NUL-terminated byte reader. -/
@[expose] def readNullTermBytesAux (fuel : Nat) (bs : List UInt8) :
    Option (List UInt8) :=
  @Nat.rec (fun _ => List UInt8 → Option (List UInt8))
    (fun _ => none)
    (fun _ ih rem =>
      match rem with
      | [] => none
      | b :: rest =>
        if Nat.beq b.toNat 0 then some []
        else
          match ih rest with
          | none => none
          | some cs => some (b :: cs))
    fuel bs

/-- Parse a NUL-terminated byte string from `strtab` at offset `off`. -/
@[expose] def readNullTermBytes? (strtab : List UInt8) (off : Nat) :
    Option (List UInt8) :=
  match fastDropBytes off strtab with
  | [] => none
  | tail => readNullTermBytesAux (tail.length + 1) tail

/-- Bounded `@Nat.rec` byte-list prefix test (`0` `._unsafe_rec`). -/
@[expose] def bytesStartsWith (s pfx : List UInt8) : Bool :=
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
    (pfx.length + 1) s pfx

/-! ## 2. ELF64 & AAELF64 Constants and Structures -/

@[expose] def ELFCLASS64 : Nat := 2
@[expose] def ELFDATA2LSB : Nat := 1
@[expose] def EV_CURRENT : Nat := 1
@[expose] def ELFOSABI_NONE : Nat := 0
@[expose] def ELFOSABI_GNU : Nat := 3
@[expose] def ET_REL : Nat := 1
@[expose] def EM_AARCH64 : Nat := 183
@[expose] def ELF64_EHDR_SIZE : Nat := 64
@[expose] def ELF64_SHDR_SIZE : Nat := 64
@[expose] def ELF64_SYM_SIZE : Nat := 24
@[expose] def ELF64_RELA_SIZE : Nat := 24

@[expose] def SHT_NULL : Nat := 0
@[expose] def SHT_PROGBITS : Nat := 1
@[expose] def SHT_SYMTAB : Nat := 2
@[expose] def SHT_STRTAB : Nat := 3
@[expose] def SHT_RELA : Nat := 4
@[expose] def SHT_NOBITS : Nat := 8
@[expose] def SHT_REL : Nat := 9
@[expose] def SHT_DYNSYM : Nat := 11
@[expose] def SHT_INIT_ARRAY : Nat := 14
@[expose] def SHT_FINI_ARRAY : Nat := 15
@[expose] def SHT_PREINIT_ARRAY : Nat := 16
@[expose] def SHT_GROUP : Nat := 17
@[expose] def SHT_RELR : Nat := 19

@[expose] def SHF_WRITE : Nat := 1
@[expose] def SHF_ALLOC : Nat := 2
@[expose] def SHF_EXECINSTR : Nat := 4
@[expose] def SHF_MERGE : Nat := 16
@[expose] def SHF_STRINGS : Nat := 32
@[expose] def SHF_GROUP : Nat := 512
@[expose] def SHF_TLS : Nat := 1024
@[expose] def SHF_COMPRESSED : Nat := 2048
@[expose] def SHF_EXCLUDE : Nat := 2147483648

@[expose] def STB_LOCAL : Nat := 0
@[expose] def STT_NOTYPE : Nat := 0
@[expose] def STT_OBJECT : Nat := 1
@[expose] def STT_SECTION : Nat := 3
@[expose] def STT_TLS : Nat := 6
@[expose] def STT_GNU_IFUNC : Nat := 10

@[expose] def R_AARCH64_ADR_PREL_LO21 : Nat := 274
@[expose] def R_AARCH64_ADR_PREL_PG_HI21 : Nat := 275
@[expose] def R_AARCH64_ADD_ABS_LO12_NC : Nat := 277
@[expose] def R_AARCH64_LDST64_ABS_LO12_NC : Nat := 286
@[expose] def R_AARCH64_LDST128_ABS_LO12_NC : Nat := 299
@[expose] def R_AARCH64_IRELATIVE : Nat := 1032

/-- Test whether `n` is a positive power of two (bounded to 64-bit alignments
via `@Nat.rec`, `0` `._unsafe_rec`). -/
@[expose] def isPow2Nat (n : Nat) : Bool :=
  @Nat.rec (fun _ => Nat → Bool)
    (fun _ => false)
    (fun _ ih k =>
      if Nat.beq k 1 then true
      else if Nat.beq k 0 || !Nat.beq (Nat.mod k 2) 0 then false
      else ih (Nat.div k 2))
    65 n

/-- Test whether a single power-of-two flag bit `bit` is set in `flags`. -/
@[expose] def hasFlagBit (flags bit : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.div flags bit) 2) 1

/-- Parsed ELF64 file header (`ET_REL`, `EM_AARCH64`). -/
structure Elf64Header where
  eType     : Nat
  eMachine  : Nat
  eVersion  : Nat
  eShoff    : Nat
  eFlags    : Nat
  eEhsize   : Nat
  eShentsz  : Nat
  eShnum    : Nat
  eShstrndx : Nat

/-- Parsed ELF64 section header with resolved name bytes from `.shstrtab`. -/
structure Elf64Section where
  idx       : Nat
  shName    : Nat
  name      : List UInt8
  shType    : Nat
  shFlags   : Nat
  shAddr    : Nat
  shOffset  : Nat
  shSize    : Nat
  shLink    : Nat
  shInfo    : Nat
  shAddral  : Nat
  shEntsize : Nat

/-- Parsed ELF64 symbol table entry. -/
structure Elf64Symbol where
  idx     : Nat
  stName  : Nat
  name    : List UInt8
  stInfo  : Nat
  stOther : Nat
  stShndx : Nat
  stValue : Nat
  stSize  : Nat

/-- Parsed ELF64 `Elf64_Rela` entry. -/
structure Elf64Rela where
  rOffset : Nat
  rSym    : Nat
  rType   : Nat
  rAddend : Int

/-- A parsed `SHT_RELA` section bundled with its target section index. -/
structure Elf64RelaSection where
  secIdx    : Nat
  targetSec : Nat
  symtabSec : Nat
  entries   : List Elf64Rela

/-- Complete parsed ELF64 relocatable `EM_AARCH64` object. -/
structure Elf64Object where
  header       : Elf64Header
  sections     : List Elf64Section
  symtabIdx    : Option Nat
  symbols      : List Elf64Symbol
  relaSections : List Elf64RelaSection

/-! ## 3. ELF64 Header, Section, Symbol, and RELA Parsers -/

/-- Validate and parse the 64-byte ELF64 header for little-endian `ET_REL`
`EM_AARCH64` objects. Rejects malformed `e_ident`, non-zero `EI_PAD`, non-zero
reserved `e_flags`, wrong `e_ehsize`/`e_shentsize`, `e_shnum == 0`,
out-of-range `e_shstrndx`, or truncated section header table. -/
@[expose] def parseElf64Header? (bs : List UInt8) : Option Elf64Header :=
  if !bytesLenAtLeast ELF64_EHDR_SIZE bs then none
  else
    match bs with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 ::
      p9 :: p10 :: p11 :: p12 :: p13 :: p14 :: p15 :: _ =>
      let magicOk :=
        Nat.beq b0.toNat 0x7F && Nat.beq b1.toNat 0x45 &&
        Nat.beq b2.toNat 0x4C && Nat.beq b3.toNat 0x46
      let classOk := Nat.beq b4.toNat ELFCLASS64
      let dataOk  := Nat.beq b5.toNat ELFDATA2LSB
      let verOk   := Nat.beq b6.toNat EV_CURRENT
      let osabiOk := Nat.beq b7.toNat ELFOSABI_NONE ||
                     Nat.beq b7.toNat ELFOSABI_GNU
      let abivOk  := Nat.beq b8.toNat 0
      let padOk   :=
        Nat.beq p9.toNat 0 && Nat.beq p10.toNat 0 &&
        Nat.beq p11.toNat 0 && Nat.beq p12.toNat 0 &&
        Nat.beq p13.toNat 0 && Nat.beq p14.toNat 0 &&
        Nat.beq p15.toNat 0
      if !(magicOk && classOk && dataOk && verOk &&
           osabiOk && abivOk && padOk) then none
      else
        match readU16Le? bs 16, readU16Le? bs 18, readU32Le? bs 20,
              readU64Le? bs 40, readU32Le? bs 48, readU16Le? bs 52,
              readU16Le? bs 58, readU16Le? bs 60, readU16Le? bs 62 with
        | some eType, some eMach, some eVer, some eShoff, some eFlags,
          some eEhsz, some eShent, some eShnum, some eShstr =>
          if Nat.beq eType ET_REL &&
             Nat.beq eMach EM_AARCH64 &&
             Nat.beq eVer EV_CURRENT &&
             Nat.beq eFlags 0 &&
             Nat.beq eEhsz ELF64_EHDR_SIZE &&
             Nat.beq eShent ELF64_SHDR_SIZE &&
             Nat.blt 0 eShnum &&
             Nat.blt eShnum 0xFF00 &&
             Nat.blt eShstr eShnum &&
             bytesLenAtLeast (eShoff + ELF64_SHDR_SIZE * eShnum) bs then
            some { eType := eType, eMachine := eMach, eVersion := eVer,
                   eShoff := eShoff, eFlags := eFlags, eEhsize := eEhsz,
                   eShentsz := eShent, eShnum := eShnum, eShstrndx := eShstr }
          else none
        | _, _, _, _, _, _, _, _, _ => none
    | _ => none

/-- Raw section header fields before `.shstrtab` name resolution. -/
structure RawShdr where
  idx       : Nat
  shName    : Nat
  shType    : Nat
  shFlags   : Nat
  shAddr    : Nat
  shOffset  : Nat
  shSize    : Nat
  shLink    : Nat
  shInfo    : Nat
  shAddral  : Nat
  shEntsize : Nat

/-- Parse one 64-byte `Elf64_Shdr` at file offset `off`. -/
@[expose] def parseRawShdr? (bs : List UInt8) (idx off : Nat) :
    Option RawShdr :=
  match readU32Le? bs off, readU32Le? bs (off + 4),
        readU64Le? bs (off + 8), readU64Le? bs (off + 16),
        readU64Le? bs (off + 24), readU64Le? bs (off + 32),
        readU32Le? bs (off + 40), readU32Le? bs (off + 44),
        readU64Le? bs (off + 48), readU64Le? bs (off + 56) with
  | some nm, some tp, some fl, some ad, some so,
    some sz, some lk, some inf, some al, some es =>
    -- Every non-NULL, non-NOBITS section payload must lie in bounds of `bs`.
    if !Nat.beq tp SHT_NULL && !Nat.beq tp SHT_NOBITS &&
       !bytesLenAtLeast (so + sz) bs then none
    else
      some { idx := idx, shName := nm, shType := tp, shFlags := fl,
             shAddr := ad, shOffset := so, shSize := sz, shLink := lk,
             shInfo := inf, shAddral := al, shEntsize := es }
  | _, _, _, _, _, _, _, _, _, _ => none

/-- Parse `count` consecutive section headers starting at `off`. -/
@[expose] def parseRawShdrsAux (bs : List UInt8) (shoff count : Nat) :
    Option (List RawShdr) :=
  @Nat.rec (fun _ => Nat → Option (List RawShdr))
    (fun _ => some [])
    (fun _ ih idx =>
      match parseRawShdr? bs idx (shoff + ELF64_SHDR_SIZE * idx) with
      | none => none
      | some sh =>
        match ih (idx + 1) with
        | none => none
        | some rest => some (sh :: rest))
    count 0

/-- Resolve section names against `.shstrtab`. -/
@[expose] def resolveSections (shstrBytes : List UInt8)
    (raws : List RawShdr) : Option (List Elf64Section) :=
  List.foldr
    (fun r acc? =>
      match acc? with
      | none => none
      | some acc =>
        let nm? :=
          if Nat.beq r.shType SHT_NULL && Nat.beq r.shName 0 then some []
          else readNullTermBytes? shstrBytes r.shName
        match nm? with
        | none => none
        | some nm =>
          some ({ idx := r.idx, shName := r.shName, name := nm,
                  shType := r.shType, shFlags := r.shFlags,
                  shAddr := r.shAddr, shOffset := r.shOffset,
                  shSize := r.shSize, shLink := r.shLink,
                  shInfo := r.shInfo, shAddral := r.shAddral,
                  shEntsize := r.shEntsize } :: acc))
    (some []) raws

/-- Parse one 24-byte `Elf64_Sym` at file offset `off`. -/
@[expose] def parseSym? (bs strtab : List UInt8) (idx off : Nat) :
    Option Elf64Symbol :=
  match readU32Le? bs off, readU8At? bs (off + 4), readU8At? bs (off + 5),
        readU16Le? bs (off + 6), readU64Le? bs (off + 8),
        readU64Le? bs (off + 16) with
  | some nmOff, some info, some other, some shndx, some val, some sz =>
    let nm? :=
      if Nat.beq nmOff 0 then some []
      else readNullTermBytes? strtab nmOff
    match nm? with
    | none => none
    | some nm =>
      some { idx := idx, stName := nmOff, name := nm,
             stInfo := info.toNat, stOther := other.toNat,
             stShndx := shndx, stValue := val, stSize := sz }
  | _, _, _, _, _, _ => none

/-- Parse `count` symbol table entries starting at `baseOff`. -/
@[expose] def parseSymsAux (bs strtab : List UInt8) (baseOff count : Nat) :
    Option (List Elf64Symbol) :=
  @Nat.rec (fun _ => Nat → Option (List Elf64Symbol))
    (fun _ => some [])
    (fun _ ih idx =>
      match parseSym? bs strtab idx (baseOff + ELF64_SYM_SIZE * idx) with
      | none => none
      | some s =>
        match ih (idx + 1) with
        | none => none
        | some rest => some (s :: rest))
    count 0

/-- Parse one 24-byte `Elf64_Rela` entry at file offset `off`. -/
@[expose] def parseRela? (bs : List UInt8) (off : Nat) : Option Elf64Rela :=
  match readU64Le? bs off, readU64Le? bs (off + 8),
        readI64Le? bs (off + 16) with
  | some rOff, some rInfo, some rAdd =>
    let rType := Nat.mod rInfo 4294967296
    let rSym := Nat.div rInfo 4294967296
    some { rOffset := rOff, rSym := rSym, rType := rType, rAddend := rAdd }
  | _, _, _ => none

/-- Parse `count` `Elf64_Rela` entries starting at `baseOff`. -/
@[expose] def parseRelasAux (bs : List UInt8) (baseOff count : Nat) :
    Option (List Elf64Rela) :=
  @Nat.rec (fun _ => Nat → Option (List Elf64Rela))
    (fun _ => some [])
    (fun _ ih idx =>
      match parseRela? bs (baseOff + ELF64_RELA_SIZE * idx) with
      | none => none
      | some r =>
        match ih (idx + 1) with
        | none => none
        | some rest => some (r :: rest))
    count 0

/-- Parse all `SHT_RELA` sections, rejecting malformed entry sizes or
duplicate `SHT_RELA` sections targeting the same `shInfo` section. -/
@[expose] def parseAllRelaSections? (bs : List UInt8)
    (secs : List Elf64Section) (symtabIdx? : Option Nat) :
    Option (List Elf64RelaSection) :=
  let relaSecs := secs.filter (fun s => Nat.beq s.shType SHT_RELA)
  let targets := relaSecs.map (fun s => s.shInfo)
  if !natListAllDistinct targets then none
  else
    List.foldr
      (fun s acc? =>
        match acc? with
        | none => none
        | some acc =>
          if hasFlagBit s.shFlags SHF_COMPRESSED ||
             !Nat.beq s.shEntsize ELF64_RELA_SIZE ||
             !Nat.beq (Nat.mod s.shSize ELF64_RELA_SIZE) 0 ||
             !Nat.blt s.shInfo secs.length then none
          else
            let linkOk :=
              match symtabIdx? with
              | none => false
              | some stIdx => Nat.beq s.shLink stIdx
            if !linkOk then none
            else
              let cnt := Nat.div s.shSize ELF64_RELA_SIZE
              match parseRelasAux bs s.shOffset cnt with
              | none => none
              | some entries =>
                some ({ secIdx := s.idx, targetSec := s.shInfo,
                        symtabSec := s.shLink, entries := entries } :: acc))
      (some []) relaSecs

/-- Whole-object raw-byte ELF64 `ET_REL` `EM_AARCH64` parser. Rejects
`SHT_DYNSYM`, `SHT_REL`, `SHT_RELR`, `SHF_COMPRESSED` on `.shstrtab`/
`.symtab`/`.strtab`/`SHT_RELA`, duplicate `SHT_SYMTAB`, duplicate `SHT_RELA`
for the same target section, and any out-of-bounds table. -/
@[expose] def parseElf64Object? (bs : List UInt8) : Option Elf64Object :=
  match parseElf64Header? bs with
  | none => none
  | some hdr =>
    match parseRawShdrsAux bs hdr.eShoff hdr.eShnum with
    | none => none
    | some raws =>
      let sh0Null :=
        match raws with
        | sh0 :: _ => Nat.beq sh0.shType SHT_NULL
        | [] => false
      if !sh0Null then none
      else
      match listGet? raws hdr.eShstrndx with
      | none => none
      | some shstr =>
        if !Nat.beq shstr.shType SHT_STRTAB ||
           hasFlagBit shstr.shFlags SHF_COMPRESSED then none
        else
          match sliceBytes? bs shstr.shOffset shstr.shSize with
          | none => none
          | some shstrBytes =>
            match resolveSections shstrBytes raws with
            | none => none
            | some secs =>
              -- Reject dynamic symbol tables, non-RELA relocs, and compressed
              -- metadata tables (`SHT_SYMTAB`, `SHT_STRTAB`, `SHT_RELA`)
              let badTable := listAny (fun s =>
                Nat.beq s.shType SHT_DYNSYM ||
                Nat.beq s.shType SHT_REL ||
                Nat.beq s.shType SHT_RELR ||
                ((Nat.beq s.shType SHT_SYMTAB ||
                  Nat.beq s.shType SHT_STRTAB ||
                  Nat.beq s.shType SHT_RELA) &&
                 hasFlagBit s.shFlags SHF_COMPRESSED)) secs
              if badTable then none
              else
                let symtabs :=
                  secs.filter (fun s => Nat.beq s.shType SHT_SYMTAB)
                match symtabs with
                | [] =>
                  match parseAllRelaSections? bs secs none with
                  | none => none
                  | some relas =>
                    some { header := hdr, sections := secs,
                           symtabIdx := none, symbols := [],
                           relaSections := relas }
                | [st] =>
                  if hasFlagBit st.shFlags SHF_COMPRESSED ||
                     !Nat.beq st.shEntsize ELF64_SYM_SIZE ||
                     !Nat.beq (Nat.mod st.shSize ELF64_SYM_SIZE) 0 then none
                  else
                    match listGet? secs st.shLink with
                    | none => none
                    | some strSec =>
                      if !Nat.beq strSec.shType SHT_STRTAB ||
                         hasFlagBit strSec.shFlags SHF_COMPRESSED then none
                      else
                        match sliceBytes? bs strSec.shOffset strSec.shSize with
                        | none => none
                        | some strBytes =>
                          let symCnt := Nat.div st.shSize ELF64_SYM_SIZE
                          match parseSymsAux bs strBytes st.shOffset symCnt with
                          | none => none
                          | some syms =>
                            let sym0Undef :=
                              match syms with
                              | s0 :: _ =>
                                Nat.beq s0.stName 0 &&
                                Nat.beq s0.stInfo 0 &&
                                Nat.beq s0.stOther 0 &&
                                Nat.beq s0.stShndx 0 &&
                                Nat.beq s0.stValue 0 &&
                                Nat.beq s0.stSize 0
                              | [] => false
                            if !sym0Undef then none
                            else
                              match parseAllRelaSections? bs secs
                                  (some st.idx) with
                              | none => none
                              | some relas =>
                                some { header := hdr, sections := secs,
                                       symtabIdx := some st.idx,
                                       symbols := syms,
                                       relaSections := relas }
                | _ => none

/-! ## 4. Whole-Object Hygiene & Read-Only `.rodata` Resolution -/

/-- ASCII byte prefixes for forbidden init/fini/ctor/dtor section names. -/
@[expose] def pfxInitArray : List UInt8 :=
  [0x2E, 0x69, 0x6E, 0x69, 0x74, 0x5F, 0x61, 0x72, 0x72, 0x61, 0x79]
@[expose] def pfxFiniArray : List UInt8 :=
  [0x2E, 0x66, 0x69, 0x6E, 0x69, 0x5F, 0x61, 0x72, 0x72, 0x61, 0x79]
@[expose] def pfxPreinitArray : List UInt8 :=
  [0x2E, 0x70, 0x72, 0x65, 0x69, 0x6E, 0x69, 0x74, 0x5F, 0x61, 0x72, 0x72,
   0x61, 0x79]
@[expose] def pfxCtors : List UInt8 := [0x2E, 0x63, 0x74, 0x6F, 0x72, 0x73]
@[expose] def pfxDtors : List UInt8 := [0x2E, 0x64, 0x74, 0x6F, 0x72, 0x73]
@[expose] def pfxInit  : List UInt8 := [0x2E, 0x69, 0x6E, 0x69, 0x74]
@[expose] def pfxFini  : List UInt8 := [0x2E, 0x66, 0x69, 0x6E, 0x69]

/-- True iff a section name is a forbidden constructor/destructor/init hook. -/
@[expose] def isForbiddenSectionName (nm : List UInt8) : Bool :=
  bytesStartsWith nm pfxInitArray ||
  bytesStartsWith nm pfxFiniArray ||
  bytesStartsWith nm pfxPreinitArray ||
  bytesStartsWith nm pfxCtors ||
  bytesStartsWith nm pfxDtors ||
  bytesStartsWith nm pfxInit ||
  bytesStartsWith nm pfxFini

/-- True iff a section violates object-level ELF hygiene (init/fini arrays,
`SHT_GROUP`, `SHF_GROUP`, `W+X`, or forbidden names). -/
@[expose] def isForbiddenSection (s : Elf64Section) : Bool :=
  Nat.beq s.shType SHT_INIT_ARRAY ||
  Nat.beq s.shType SHT_FINI_ARRAY ||
  Nat.beq s.shType SHT_PREINIT_ARRAY ||
  Nat.beq s.shType SHT_GROUP ||
  hasFlagBit s.shFlags SHF_GROUP ||
  (hasFlagBit s.shFlags SHF_WRITE && hasFlagBit s.shFlags SHF_EXECINSTR) ||
  isForbiddenSectionName s.name

/-- True iff a symbol is a `STT_GNU_IFUNC` resolver. -/
@[expose] def isIfuncSymbol (s : Elf64Symbol) : Bool :=
  Nat.beq (Nat.mod s.stInfo 16) STT_GNU_IFUNC

/-- True iff a parsed `Elf64Object` has zero forbidden sections, zero
`STT_GNU_IFUNC` symbols, and zero `R_AARCH64_IRELATIVE` relocations. -/
@[expose] def parsedObjectHygieneOk (obj : Elf64Object) : Bool :=
  let noBadSec := !listAny isForbiddenSection obj.sections
  let noIfunc := !listAny isIfuncSymbol obj.symbols
  let noIrel := !listAny (fun rs =>
    listAny (fun r => Nat.beq r.rType R_AARCH64_IRELATIVE) rs.entries)
    obj.relaSections
  noBadSec && noIfunc && noIrel

/-- Raw-byte-bound object hygiene gate: parses `bs` as an ELF64 `EM_AARCH64`
object and verifies zero forbidden sections, `IFUNC`, or `IRELATIVE`. -/
@[expose] def objectHasNoForbiddenElfFeatures (bs : List UInt8) : Bool :=
  match parseElf64Object? bs with
  | none => false
  | some obj => parsedObjectHygieneOk obj

/-- Map an AAELF64 relocation type code to an admitted `.rodata`
`AArch64RelocKind` (rejecting all other relocation types fail-closed). -/
@[expose] def rodataRelocKindOfNat? (rType : Nat) : Option AArch64RelocKind :=
  if Nat.beq rType R_AARCH64_ADR_PREL_LO21 then some .adrPrelLo21
  else if Nat.beq rType R_AARCH64_ADR_PREL_PG_HI21 then some .adrPrelPgHi21
  else if Nat.beq rType R_AARCH64_ADD_ABS_LO12_NC then some .addAbsLo12Nc
  else if Nat.beq rType R_AARCH64_LDST64_ABS_LO12_NC then some .ldst64AbsLo12Nc
  else if Nat.beq rType R_AARCH64_LDST128_ABS_LO12_NC then
    some .ldst128AbsLo12Nc
  else none

/-- Required access width in bytes for an admitted `.rodata` relocation kind.
-/
@[expose] def rodataAccessBytes (k : AArch64RelocKind) : Nat :=
  match k with
  | .ldst128AbsLo12Nc => 16
  | .ldst64AbsLo12Nc  => 8
  | _                 => 1

/-- True iff `sec` is a plain executable `SHT_PROGBITS` code section with exact
flags `SHF_ALLOC | SHF_EXECINSTR` (rejecting `SHF_WRITE`, `SHF_GROUP`,
`SHF_TLS`, `SHF_COMPRESSED`, `SHF_EXCLUDE`, and unknown flags). -/
@[expose] def isValidExecTextSection (sec : Elf64Section) : Bool :=
  Nat.beq sec.shType SHT_PROGBITS &&
  Nat.beq sec.shFlags (SHF_ALLOC + SHF_EXECINSTR)

/-- True iff `sec` is a read-only `SHT_PROGBITS` `.rodata` section with exact
flags `SHF_ALLOC` or `SHF_ALLOC | SHF_MERGE` (rejecting `SHF_WRITE`,
`SHF_EXECINSTR`, `SHF_GROUP`, `SHF_STRINGS`, `SHF_TLS`, `SHF_COMPRESSED`,
`SHF_EXCLUDE`, and unknown flags). -/
@[expose] def isValidRodataSection (sec : Elf64Section) : Bool :=
  Nat.beq sec.shType SHT_PROGBITS &&
  (Nat.beq sec.shFlags SHF_ALLOC ||
   Nat.beq sec.shFlags (SHF_ALLOC + SHF_MERGE))

/-- Validate a single `Elf64Rela` entry targeting read-only `.rodata` inside
`obj`: enforces admitted AAELF64 `.rodata` reloc type, non-zero `r_sym`,
`STB_LOCAL` binding with type in `{STT_NOTYPE, STT_OBJECT, STT_SECTION}`,
strict read-only `SHT_PROGBITS` target section (no `SHT_RELA` targeting it,
no `SHF_WRITE`/`SHF_TLS`/`SHF_COMPRESSED`/`SHF_EXCLUDE`/`SHF_GROUP`), AAELF64
scaled alignment on both `effOff` and power-of-two `sh_addralign`, in-bounds
`effOff + accessBytes <= shSize`, and `SHF_MERGE` exact single-entry
containment (`shSize % shEntsize == 0`, entry inside `shSize`, no
`STT_SECTION` anchor). -/
@[expose] def resolveParsedRodataReloc? (obj : Elf64Object)
    (funcOff : Nat) (rela : Elf64Rela) : Option AArch64Reloc :=
  if Nat.beq rela.rSym 0 then none
  else
    match rodataRelocKindOfNat? rela.rType with
    | none => none
    | some kind =>
      match listGet? obj.symbols rela.rSym with
      | none => none
      | some sym =>
        let bind := Nat.div sym.stInfo 16
        let stType := Nat.mod sym.stInfo 16
        let stTypeOk :=
          Nat.beq stType STT_NOTYPE ||
          Nat.beq stType STT_OBJECT ||
          Nat.beq stType STT_SECTION
        if !Nat.beq bind STB_LOCAL || !stTypeOk ||
           Nat.beq sym.stShndx 0 || !Nat.blt sym.stShndx 0xFF00 then none
        else
          match listGet? obj.sections sym.stShndx with
          | none => none
          | some sec =>
            let roOk :=
              isValidRodataSection sec &&
              !listAny (fun rs => Nat.beq rs.targetSec sec.idx) obj.relaSections
            if !roOk then none
            else
              let effInt := Int.add (Int.ofNat sym.stValue) rela.rAddend
              match effInt with
              | Int.negSucc _ => none
              | Int.ofNat effOff =>
                let accBytes := rodataAccessBytes kind
                let alignOk :=
                  if !Nat.blt 1 accBytes then true
                  else
                    Nat.beq (Nat.mod effOff accBytes) 0 &&
                    Nat.blt 0 sec.shAddral &&
                    isPow2Nat sec.shAddral &&
                    Nat.beq (Nat.mod sec.shAddral accBytes) 0
                if !alignOk || !Nat.ble (effOff + accBytes) sec.shSize then none
                else
                  let mergeOk :=
                    if !hasFlagBit sec.shFlags SHF_MERGE then true
                    else if Nat.beq stType STT_SECTION then false
                    else
                      let esz := sec.shEntsize
                      Nat.blt 0 esz &&
                      Nat.beq (Nat.mod sec.shSize esz) 0 &&
                      Nat.beq (Nat.mod sym.stValue esz) 0 &&
                      Nat.ble (sym.stValue + esz) sec.shSize &&
                      Nat.ble sym.stValue effOff &&
                      Nat.ble (effOff + accBytes) (sym.stValue + esz) &&
                      (!Nat.blt 1 accBytes || Nat.beq (Nat.mod esz accBytes) 0)
                  if !mergeOk then none
                  else if Nat.blt rela.rOffset funcOff then none
                  else
                    let relOff := rela.rOffset - funcOff
                    if !Nat.beq (Nat.mod relOff 4) 0 then none
                    else
                      some { offset := relOff, kind := kind,
                             secIdx := sec.idx, target := Int.ofNat effOff }

/-- Exact `Int` boolean equality (`0` `._unsafe_rec`). -/
@[expose] def intBeq (a b : Int) : Bool :=
  match a, b with
  | Int.ofNat x, Int.ofNat y => Nat.beq x y
  | Int.negSucc x, Int.negSucc y => Nat.beq x y
  | _, _ => false

/-- Exact `Elf64Rela` boolean equality (`0` `._unsafe_rec`). -/
@[expose] def elf64RelaBeq (a b : Elf64Rela) : Bool :=
  Nat.beq a.rOffset b.rOffset &&
  Nat.beq a.rSym b.rSym &&
  Nat.beq a.rType b.rType &&
  intBeq a.rAddend b.rAddend

/-- Conservative static patch width in bytes for an AAELF64 relocation type.
Known 4-byte A64 instruction relocations (branches, calls, `ADRP`/`LO12`,
`MOVW`, `ABS32`/`PREL32`, GOT page/lo12) return `4`; `R_AARCH64_NONE` returns
`0`; 2-byte `ABS16`/`PREL16` return `2`; `ABS64`/`PREL64` and all unknown
types conservatively return `8` (fail-closed) so an 8-byte literal-pool patch
cannot silently overwrite bytes at `funcOff` or an adjacent relocation slot. -/
@[expose] def relaPatchWidthBytes (rType : Nat) : Nat :=
  if Nat.beq rType 0 then 0
  else if Nat.beq rType 259 || Nat.beq rType 262 then 2 -- ABS16 / PREL16
  else if
    Nat.beq rType 258 || Nat.beq rType 261 || -- ABS32 / PREL32
    (Nat.ble 263 rType && Nat.ble rType 280) || -- MOVW/LD/ADR/ADD/LDST8/BR
    (Nat.ble 282 rType && Nat.ble rType 293) || -- JUMP/CALL/LDST16-64/MOVW
    Nat.beq rType 299 || -- LDST128_ABS_LO12_NC
    Nat.beq rType 311 || Nat.beq rType 312 -- ADR_GOT_PAGE / LD64_GOT_LO12_NC
  then 4
  else 8

/-- Raw-byte-bound single `.rodata` relocation validator: parses `bs`,
verifies object-wide hygiene, verifies `textSecIdx` is an executable
`SHT_PROGBITS` section whose parsed `SHT_RELA` section links to the object's
`SHT_SYMTAB`, contains `rela` strictly once, and has no sibling entry whose
patch window `[e.rOffset, e.rOffset + relaPatchWidthBytes e.rType)` overlaps
`[rela.rOffset, rela.rOffset + 4)` (or shares `rela.rOffset`), and validates
`rela`'s `.rodata` target. Rejects fabricated, duplicate, overlapping, or
cross-section relocations fail-closed. -/
@[expose] def resolveAArch64RodataReloc (bs : List UInt8)
    (textSecIdx funcOff : Nat) (rela : Elf64Rela) : Option AArch64Reloc :=
  match parseElf64Object? bs with
  | none => none
  | some obj =>
    if !parsedObjectHygieneOk obj then none
    else
      match listGet? obj.sections textSecIdx, obj.symtabIdx,
            listFind? (fun rs => Nat.beq rs.targetSec textSecIdx)
              obj.relaSections with
      | some sec, some stIdx, some rs =>
        let exactCnt := listCountP (elf64RelaBeq rela) rs.entries
        let overlapCnt :=
          listCountP
            (fun e =>
              let eEnd := e.rOffset + relaPatchWidthBytes e.rType
              Nat.beq e.rOffset rela.rOffset ||
              (Nat.blt e.rOffset (rela.rOffset + 4) &&
               Nat.blt rela.rOffset eEnd))
            rs.entries
        if !isValidExecTextSection sec ||
           !Nat.beq (Nat.mod funcOff 4) 0 ||
           !Nat.ble (rela.rOffset + 4) sec.shSize ||
           !Nat.beq rs.symtabSec stIdx ||
           !Nat.beq exactCnt 1 ||
           !Nat.beq overlapCnt 1 then none
        else resolveParsedRodataReloc? obj funcOff rela
      | _, _, _ => none

/-- Extract and validate all `.rodata` relocations overlapping the function
byte range `[funcOff, funcOff + funcSize)` of `textSecIdx`. Uses per-type
conservative patch widths (`relaPatchWidthBytes`: `4` for known 4-byte A64
instruction relocations, `8` for `ABS64`/`PREL64` and any unknown type) so
preceding tail-call/4-byte relocations at `funcOff - 4` do not cause false
rejections while preceding 8-byte literal-pool relocations overlapping
`funcOff` are rejected fail-closed. -/
@[expose] def extractParsedFuncRelocs? (obj : Elf64Object)
    (textSecIdx funcOff funcSize : Nat) : Option (List AArch64Reloc) :=
  match listFind? (fun rs => Nat.beq rs.targetSec textSecIdx)
      obj.relaSections with
  | none => some []
  | some rs =>
    List.foldr
      (fun r acc? =>
        match acc? with
        | none => none
        | some acc =>
          let funcEnd := funcOff + funcSize
          let rEnd := r.rOffset + relaPatchWidthBytes r.rType
          if Nat.ble funcEnd r.rOffset || Nat.ble rEnd funcOff then
            some acc
          else if Nat.blt r.rOffset funcOff ||
                  Nat.blt funcEnd (r.rOffset + 4) then
            none
          else
            match resolveParsedRodataReloc? obj funcOff r with
            | none => none
            | some resolved => some (resolved :: acc))
      (some []) rs.entries

/-- Wildcard-free GPR write set for intra-block `ADRP` tracking. -/
@[expose] def adrpKillGprs (i : DecodedInsn) : List Gpr :=
  let wrZr (rz : RegOrZr) : List Gpr :=
    match rz with | .gpr r => [r] | .zr => []
  let wrSp (rs : RegOrSp) (isZr : Bool) : List Gpr :=
    if isZr then [] else match rs with | .gpr r => [r] | .sp => []
  match i with
  | .addSubImm _ _ _ rd rdIsZr _ _ _ => wrSp rd rdIsZr
  | .logicImm _ _ rd rdIsZr _ _ _ _ => wrSp rd rdIsZr
  | .moveWide _ _ rd _ _ => wrZr rd
  | .bitfield _ _ rd _ _ _ => wrZr rd
  | .pcRelAddr _ rd _ _ => wrZr rd
  | .addSubShift _ _ _ _ _ rd _ _ => wrZr rd
  | .addSubExt _ _ _ _ _ rd rdIsZr _ _ => wrSp rd rdIsZr
  | .logicShift _ _ _ _ rd _ _ => wrZr rd
  | .condSel _ _ _ rd _ _ => wrZr rd
  | .maddSub _ _ rd _ _ _ => wrZr rd
  | .gpLoadStore isLoad _ _ _ rt rn mode _ =>
    let wb := match mode with
      | .unsignedOff _ => []
      | .postIndex _ | .preIndex _ => wrSp rn false
    (if isLoad then wrZr rt else []) ++ wb
  | .gpLoadStorePair isLoad _ rt rt2 rn mode =>
    let wb := match mode with
      | .signedOff _ => []
      | .postIndex _ | .preIndex _ => wrSp rn false
    (if isLoad then wrZr rt ++ wrZr rt2 else []) ++ wb
  | .simdLoadStore _ _ _ rn mode _ =>
    match mode with
    | .unsignedOff _ => []
    | .postIndex _ | .preIndex _ => wrSp rn false
  | .simdLoadStorePair _ _ _ _ rn mode =>
    match mode with
    | .signedOff _ => []
    | .postIndex _ | .preIndex _ => wrSp rn false
  | .simdLdSt1 _ _ _ _ _ rn post =>
    match post with | .none => [] | .imm _ | .reg _ => wrSp rn false
  | .branch isLink _ => if isLink then [.x30] else []
  | .branchCond _ _ | .cbz _ _ _ _ | .tbz _ _ _ _
  | .ret _ | .branchReg _ _ | .nop | .bti _ | .trapOrSys
  | .simdShiftImm _ _ _ _ _ _ | .simdThreeSame _ _ _ _ _ _
  | .simdCmeqZero _ _ _ _ | .simdPerm _ _ _ _ _ _ => []

/-- True iff `i` terminates or transfers control such that subsequent
instructions cannot inherit an `ADRP` page base across it. -/
@[expose] def adrpClearsAll (i : DecodedInsn) : Bool :=
  match i with
  | .branch _ _ | .ret _ | .branchReg _ _ | .trapOrSys => true
  | _ => false

/-- Collect byte offsets targeted by intra-function direct branches (`B`, `BL`,
`B.cond`, `CBZ`/`CBNZ`, `TBZ`/`TBNZ`) in `tr`. -/
@[expose] def streamBranchTargetOffsets (tr : List (Nat × DecodedInsn)) :
    List Nat :=
  let addOff (cur : Nat) (off : Int) (acc : List Nat) : List Nat :=
    match Int.add (Int.ofNat cur) off with
    | Int.ofNat tgt => tgt :: acc
    | Int.negSucc _ => acc
  List.foldr
    (fun e acc =>
      match e.2 with
      | .branch _ off | .branchCond _ off | .cbz _ _ _ off
      | .tbz _ _ _ off => addOff e.1 off acc
      | _ => acc)
    [] tr

/-- True iff `k` is one of the admitted `*_ABS_LO12_NC` relocation kinds. -/
@[expose] def isLo12RelocKind (k : AArch64RelocKind) : Bool :=
  match k with
  | .adrPrelLo21 | .adrPrelPgHi21 => false
  | .addAbsLo12Nc | .ldst64AbsLo12Nc | .ldst128AbsLo12Nc => true

/-- Require every `*_ABS_LO12_NC` relocation (`ADD`, `LDR` 64/128-bit) to use a
base register `rn = .gpr r` defined in the same basic block (no intervening
direct branch target including `BL`, control transfer, or write to `r`) by an
`ADRP` (`R_AARCH64_ADR_PREL_PG_HI21`) with the exact same `(secIdx, target)`.
Rejects any function containing both a `*_ABS_LO12_NC` relocation and an
indirect branch (`BR`/`BLR`, non-`x30` `RET`, or any instruction that writes
`x30` and could redirect `RET x30`) since an indirect target could bypass
`ADRP`; unmodified `RET x30` returns to the caller. -/
@[expose] def adrpLo12PairingOk (tr : List (Nat × DecodedInsn)) : Bool :=
  let hasIndirectBranch :=
    listAny
      (fun e =>
        match e.2 with
        | .branchReg _ _ => true
        | .ret rn => !rn.beq (.gpr .x30)
        | _ => listAny (fun g => g.beq .x30) (adrpKillGprs e.2))
      tr
  let hasAnyLo12 :=
    listAny
      (fun e =>
        match e.2 with
        | .addSubImm _ _ _ _ _ _ _ (some _)
        | .gpLoadStore _ _ _ _ _ _ _ (some _)
        | .simdLoadStore _ _ _ _ _ (some _) => true
        | _ => false)
      tr
  if hasIndirectBranch && hasAnyLo12 then false
  else
    let targets := streamBranchTargetOffsets tr
    let lookup (env : List (Gpr × Nat × Int)) (r : Gpr) :
        Option (Nat × Int) :=
      match listFind? (fun e => e.1.beq r) env with
      | none => none
      | some e => some e.2
    let killList (env : List (Gpr × Nat × Int)) (ks : List Gpr) :
        List (Gpr × Nat × Int) :=
      env.filter (fun e => !listAny (fun k => k.beq e.1) ks)
    let checkLo12 (env : List (Gpr × Nat × Int)) (rn : RegOrSp)
        (rel : AArch64Reloc) : Bool :=
      if !isLo12RelocKind rel.kind then false
      else
        match rn with
        | .sp => false
        | .gpr r =>
          match lookup env r with
          | none => false
          | some (sIdx, tgt) =>
            Nat.beq sIdx rel.secIdx && intBeq tgt rel.target
    let res :=
      List.foldl
        (fun st e =>
          if !st.1 then (false, [])
          else
            let env0 :=
              if natListContains targets e.1 then [] else st.2
            let lo12Ok :=
              match e.2 with
              | .addSubImm _ _ _ _ _ rn _ (some r) => checkLo12 env0 rn r
              | .gpLoadStore isLoad _ _ _ _ rn _ (some r) =>
                isLoad && checkLo12 env0 rn r
              | .simdLoadStore isLoad _ _ rn _ (some r) =>
                isLoad && checkLo12 env0 rn r
              | _ => true
            if !lo12Ok then (false, [])
            else if adrpClearsAll e.2 then (true, [])
            else
              let env1 := killList env0 (adrpKillGprs e.2)
              let env2 :=
                match e.2 with
                | .pcRelAddr true (.gpr rd) _ (some r) =>
                  match r.kind with
                  | .adrPrelPgHi21 => (rd, (r.secIdx, r.target)) :: env1
                  | _ => env1
                | _ => env1
              (true, env2))
        (true, []) tr
    res.1

/-- Raw-byte-bound extraction of validated function `.rodata` relocations.
Validates that `textSecIdx` is an executable `SHT_PROGBITS` section and that
`[funcOff, funcOff + funcSize)` is non-empty, 4-byte-aligned, and in bounds
before extracting relocations. -/
@[expose] def extractFuncRodataRelocs? (bs : List UInt8)
    (textSecIdx funcOff funcSize : Nat) : Option (List AArch64Reloc) :=
  match parseElf64Object? bs with
  | none => none
  | some obj =>
    if !parsedObjectHygieneOk obj then none
    else
      match listGet? obj.sections textSecIdx with
      | none => none
      | some sec =>
        if !isValidExecTextSection sec ||
           !Nat.blt 0 funcSize ||
           !Nat.beq (Nat.mod funcOff 4) 0 ||
           !Nat.beq (Nat.mod funcSize 4) 0 ||
           !Nat.ble (funcOff + funcSize) sec.shSize then none
        else extractParsedFuncRelocs? obj textSecIdx funcOff funcSize

/-- Extract the raw 4-byte-aligned executable function byte slice from `bs` at
`(textSecIdx, funcOff, funcSize)`. Verifies `textSecIdx` is a valid executable
`SHT_PROGBITS` section (`SHF_ALLOC | SHF_EXECINSTR` only) and
`funcOff + funcSize <= shSize`. -/
@[expose] def funcTextBytes? (bs : List UInt8)
    (textSecIdx funcOff funcSize : Nat) : Option (List UInt8) :=
  match parseElf64Object? bs with
  | none => none
  | some obj =>
    if !parsedObjectHygieneOk obj then none
    else
      match listGet? obj.sections textSecIdx with
      | none => none
      | some sec =>
        if !isValidExecTextSection sec ||
           !Nat.blt 0 funcSize ||
           !Nat.beq (Nat.mod funcOff 4) 0 ||
           !Nat.beq (Nat.mod funcSize 4) 0 ||
           !Nat.ble (funcOff + funcSize) sec.shSize then none
        else
          sliceBytes? bs (sec.shOffset + funcOff) funcSize

/-- End-to-end raw-byte ELF64 `EM_AARCH64` function decoder: requires
`cfg.requireRelocForPcRel = true` (since `parseElf64Header?` admits only
`ET_REL` objects whose link-time placement and 4 KiB page alignment are
undetermined), parses `bs`, verifies object-wide hygiene, extracts executable
4-byte-aligned function bytes and validated `.rodata` relocations (using
per-type conservative patch widths via `relaPatchWidthBytes`), enforces 1-to-1
relocation coverage and intra-block `ADRP`->`LO12` pairing
(`adrpLo12PairingOk`), and returns the decoded instruction stream. -/
@[expose] def decodeFuncFromElf? (cfg : DecodeConfig) (bs : List UInt8)
    (textSecIdx funcOff funcSize : Nat) :
    Option (List (Nat × DecodedInsn)) :=
  if !cfg.requireRelocForPcRel then none
  else
    match parseElf64Object? bs with
    | none => none
    | some obj =>
      if !parsedObjectHygieneOk obj then none
      else
        match listGet? obj.sections textSecIdx with
        | none => none
        | some sec =>
          if !isValidExecTextSection sec ||
             !Nat.blt 0 funcSize ||
             !Nat.beq (Nat.mod funcOff 4) 0 ||
             !Nat.beq (Nat.mod funcSize 4) 0 ||
             !Nat.ble (funcOff + funcSize) sec.shSize then none
          else
            match sliceBytes? bs (sec.shOffset + funcOff) funcSize,
                  extractParsedFuncRelocs? obj textSecIdx funcOff funcSize with
            | some textBs, some relocs =>
              if !localDecodeCoverageOk cfg relocs textBs then none
              else
                match decodeStream cfg relocs textBs with
                | none => none
                | some tr =>
                  if !adrpLo12PairingOk tr then none
                  else some tr
            | _, _ => none

/-! ## 5. ELF Gate Soundness Lemmas (`⊆ {propext}` axioms) -/

/-- Helper: `if false = true then a else b` reduces definitionally to `b`. -/
theorem ite_false_eq_true {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

/-- Any function decoded by `decodeFuncFromElf?` comes from an ELF64 object
passing `objectHasNoForbiddenElfFeatures`. -/
theorem decodeFuncFromElf_implies_hygiene (cfg : DecodeConfig)
    (bs : List UInt8) (textSecIdx funcOff funcSize : Nat)
    (tr : List (Nat × DecodedInsn))
    (h : decodeFuncFromElf? cfg bs textSecIdx funcOff funcSize = some tr) :
    objectHasNoForbiddenElfFeatures bs = true := by
  unfold decodeFuncFromElf? at h
  unfold objectHasNoForbiddenElfFeatures
  revert h
  cases hReq : cfg.requireRelocForPcRel with
  | false =>
    intro h
    simp only [Bool.not_false, ite_true] at h
    cases h
  | true =>
    intro h
    simp only [Bool.not_true, ite_false_eq_true] at h
    revert h
    cases hp : parseElf64Object? bs with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some obj =>
      intro h
      dsimp only at h
      revert h
      cases hh : parsedObjectHygieneOk obj with
      | false =>
        intro h
        simp only [Bool.not_false, ite_true] at h
        cases h
      | true =>
        intro h; dsimp only
        exact hh

/-- Any function decoded by `decodeFuncFromElf?` has 4-byte-aligned length and
instruction offsets. -/
theorem decodeFuncFromElf_aligned (cfg : DecodeConfig) (bs : List UInt8)
    (textSecIdx funcOff funcSize : Nat) (tr : List (Nat × DecodedInsn))
    (h : decodeFuncFromElf? cfg bs textSecIdx funcOff funcSize = some tr) :
    ∀ e, List.Mem e tr → Nat.mod e.1 4 = 0 := by
  unfold decodeFuncFromElf? at h
  revert h
  cases hReq : cfg.requireRelocForPcRel with
  | false =>
    intro h
    simp only [Bool.not_false, ite_true] at h
    cases h
  | true =>
    intro h
    simp only [Bool.not_true, ite_false_eq_true] at h
    revert h
    cases hp : parseElf64Object? bs with
    | none => intro h; dsimp only at h; cases h
    | some obj =>
      intro h
      dsimp only at h
      revert h
      cases hh : parsedObjectHygieneOk obj with
      | false =>
        intro h
        simp only [Bool.not_false, ite_true] at h
        cases h
      | true =>
        intro h
        simp only [Bool.not_true, ite_false_eq_true] at h
        revert h
        cases hs : listGet? obj.sections textSecIdx with
        | none => intro h; dsimp only at h; cases h
        | some sec =>
          intro h
          dsimp only at h
          revert h
          cases hchk : (!isValidExecTextSection sec ||
              !Nat.blt 0 funcSize ||
              !Nat.beq (Nat.mod funcOff 4) 0 ||
              !Nat.beq (Nat.mod funcSize 4) 0 ||
              !Nat.ble (funcOff + funcSize) sec.shSize) with
          | true =>
            intro h
            simp only [ite_true] at h
            cases h
          | false =>
            intro h
            simp only [ite_false_eq_true] at h
            revert h
            cases hts : sliceBytes? bs (sec.shOffset + funcOff) funcSize with
            | none => intro h; dsimp only at h; cases h
            | some textBs =>
              intro h
              revert h
              cases hrl : extractParsedFuncRelocs? obj textSecIdx funcOff
                  funcSize with
              | none => intro h; dsimp only at h; cases h
              | some relocs =>
                intro h
                dsimp only at h
                revert h
                cases hcov : localDecodeCoverageOk cfg relocs textBs with
                | false =>
                  intro h
                  simp only [Bool.not_false, ite_true] at h
                  cases h
                | true =>
                  intro h
                  simp only [Bool.not_true, ite_false_eq_true] at h
                  revert h
                  cases hds : decodeStream cfg relocs textBs with
                  | none => intro h; dsimp only at h; cases h
                  | some tr0 =>
                    intro h
                    dsimp only at h
                    revert h
                    cases hp2 : adrpLo12PairingOk tr0 with
                    | false =>
                      intro h
                      simp only [Bool.not_false, ite_true] at h
                      cases h
                    | true =>
                      intro h
                      simp only [Bool.not_true, ite_false_eq_true] at h
                      have hEq : tr0 = tr := Option.some.inj h
                      subst hEq
                      exact (decodeStream_aligned cfg relocs textBs tr0 hds).2

end Anneal.ElfAArch64
