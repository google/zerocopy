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
public import Anneal.ElfX86.RelocAndElf
public import Anneal.ElfX86.DeadFlagAndSfi

public section
namespace Anneal.ElfX86

/-!
ELF64 Post-Link `ET_EXEC`/`ET_DYN` Program Header, Zero-Syscall, and DOITM
Constant-Time Opcode Gates for `EM_X86_64` (Pass-1 Pure, `0` TCB).

Provides raw-byte ELF64 program-header parsing (`parseElf64ProgramHdrs?`)
supporting `ET_EXEC` (`2`) and static `ET_DYN` (`3`) images with strict `W^X`
enforcement (`!(PF_W && PF_X)`), pairwise disjoint `PT_LOAD` file and virtual
address ranges, power-of-two page-aligned `p_align >= 4096` with
`p_offset % p_align = p_vaddr % p_align`, mandatory single `PT_GNU_STACK` with
flags in `{PF_R, PF_R | PF_W}` (preventing pre-5.8 Linux `READ_IMPLIES_EXEC`
executable-mapping defaults), fail-closed rejection of `PT_INTERP`,
`PT_DYNAMIC`, `PT_SHLIB`, `PT_TLS`, `PT_NULL`, and unmodeled segments,
CFG-confined decoded zero-`syscall`/`sysenter`/`int` gating (banning indirect
`jmp`/`call`, banning `push`/`pop` and `rsp`/`rbp` operands via
`insnTampersReturnStack`, confining every `jmpRel`/`callRel` target VA and
every `callRel` fallthrough `nextRIP` to decoded instruction boundaries inside
executable segments, requiring every executable segment to end in `.ret` or
`.jmpRel`, and aligning `e_entry` to a decoded boundary), and conservative
`DOITM` opcode checking.

Assumptions & current scope: `.ret` relies on caller entry return-slot validity
and non-aliasing between non-stack memory stores (e.g. `[rdi]`/`[rip+disp]`)
and the active call stack, plus non-writable static RX mappings; real static
binaries with `int3` padding, `push`/`pop` prologues, or `PT_NULL` headers
currently fail closed (positive image coverage is synthetic).
-/

/-! ## 1. ELF64 Program-Header Constants & Data Structures -/

@[expose] def etExec : Nat := 2
@[expose] def etDyn : Nat := 3
@[expose] def pnXnum : Nat := 0xFFFF
@[expose] def elf64PhdrSize : Nat := 56
@[expose] def pageSize4k : Nat := 4096
@[expose] def u64AddressLimit : Nat := 18446744073709551616

@[expose] def ptNull : Nat := 0
@[expose] def ptLoad : Nat := 1
@[expose] def ptDynamic : Nat := 2
@[expose] def ptInterp : Nat := 3
@[expose] def ptNote : Nat := 4
@[expose] def ptShlib : Nat := 5
@[expose] def ptPhdr : Nat := 6
@[expose] def ptTls : Nat := 7
@[expose] def ptGnuEhFrame : Nat := 0x6474e550
@[expose] def ptGnuStack : Nat := 0x6474e551
@[expose] def ptGnuRelro : Nat := 0x6474e552
@[expose] def ptGnuProperty : Nat := 0x6474e553

@[expose] def pfX : Nat := 1
@[expose] def pfW : Nat := 2
@[expose] def pfR : Nat := 4

/-- Parsed ELF64 little-endian `ET_EXEC`/`ET_DYN` `EM_X86_64` header. -/
structure Elf64ImageHeader where
  eType : Nat
  eMachine : Nat
  eVersion : Nat
  eEntry : Nat
  ePhoff : Nat
  eShoff : Nat
  eFlags : Nat
  eEhsize : Nat
  ePhentsize : Nat
  ePhnum : Nat
  eShentsize : Nat
  eShnum : Nat
  eShstrndx : Nat

/-- Parsed 56-byte `Elf64_Phdr` entry with zero-based table index. -/
structure Elf64ProgramHdr where
  idx : Nat
  pType : Nat
  pFlags : Nat
  pOffset : Nat
  pVaddr : Nat
  pPaddr : Nat
  pFilesz : Nat
  pMemsz : Nat
  pAlign : Nat

/-- Validated ELF64 program-header view paired with extracted executable
`PT_LOAD` byte payloads (`(seg, payloadBytes)`). -/
structure Elf64ProgramImage where
  header : Elf64ImageHeader
  phdrs : List Elf64ProgramHdr
  loadSegments : List Elf64ProgramHdr
  execSegments : List Elf64ProgramHdr
  execPayloads : List (Elf64ProgramHdr × List UInt8)

/-! ## 2. Total Boolean Helpers (`0` `._unsafe_rec`) -/

/-- Structural list filter via `List.foldr`. -/
@[expose] def listFilter {α : Type} (p : α → Bool) (xs : List α) :
    List α :=
  List.foldr (fun x acc => if p x then x :: acc else acc) [] xs

/-- Take 8 bytes per step via `@Nat.rec` to keep kernel reduction shallow. -/
@[expose] def fastTakeBytes8 (n : Nat) (bs : List UInt8) : List UInt8 :=
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

/-- Shallow bounds-checked byte slice `[off, off + len)` (`8`-byte steps). -/
@[expose] def fastSliceBytes? (bs : List UInt8) (off len : Nat) :
    Option (List UInt8) :=
  if bytesLenAtLeast (off + len) bs then
    some (fastTakeBytes8 len (fastDropBytes off bs))
  else none

/-- Test whether `n` is a positive power of two up to `2^64` via `@Nat.rec`. -/
@[expose] def isPow2Nat64 (n : Nat) : Bool :=
  @Nat.rec (fun _ => Nat → Bool)
    (fun _ => false)
    (fun _ ih k =>
      if Nat.beq k 1 then true
      else if Nat.beq k 0 || !Nat.beq (Nat.mod k 2) 0 then false
      else ih (Nat.div k 2))
    65 n

@[expose] def phdrHasExec (pFlags : Nat) : Bool :=
  Nat.beq (Nat.mod pFlags 2) 1

@[expose] def phdrHasWrite (pFlags : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.div pFlags 2) 2) 1

@[expose] def phdrHasRead (pFlags : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.div pFlags 4) 2) 1

/-- True iff `pFlags` uses only `{PF_X, PF_W, PF_R}` (`< 8`). -/
@[expose] def phdrFlagsValid (pFlags : Nat) : Bool :=
  Nat.blt pFlags 8

/-- Strict `W^X`: valid bits only and never both `PF_W` and `PF_X`. -/
@[expose] def phdrWxOk (pFlags : Nat) : Bool :=
  phdrFlagsValid pFlags && !(phdrHasWrite pFlags && phdrHasExec pFlags)

/-! ## 3. ELF64 Image Header & Program Header Table Parser -/

/-- Validate the 16-byte ELF64 little-endian `e_ident` prefix including
zero-checked `EI_ABIVERSION` and `EI_PAD[9..15]`. -/
@[expose] def elf64ImageIdentOk (bs : List UInt8) : Bool :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 ::
    p9 :: p10 :: p11 :: p12 :: p13 :: p14 :: p15 :: _ =>
    Nat.beq b0.toNat 0x7F && Nat.beq b1.toNat 0x45 &&
    Nat.beq b2.toNat 0x4C && Nat.beq b3.toNat 0x46 &&
    Nat.beq b4.toNat elfClass64 && Nat.beq b5.toNat elfData2Lsb &&
    Nat.beq b6.toNat evCurrent &&
    (Nat.beq b7.toNat elfOsAbiSysv || Nat.beq b7.toNat elfOsAbiGnu) &&
    Nat.beq b8.toNat 0 && Nat.beq p9.toNat 0 && Nat.beq p10.toNat 0 &&
    Nat.beq p11.toNat 0 && Nat.beq p12.toNat 0 && Nat.beq p13.toNat 0 &&
    Nat.beq p14.toNat 0 && Nat.beq p15.toNat 0
  | _ => false

/-- Validate fixed scalar header invariants for `ET_EXEC`/`ET_DYN` `EM_X86_64`
images against total image length via `bytesLenAtLeast`. -/
@[expose] def imageHeaderFieldsOk (bs : List UInt8)
    (eTy eMach eVer eFlags ehsz phent phnum phoff : Nat) : Bool :=
  (Nat.beq eTy etExec || Nat.beq eTy etDyn) &&
  Nat.beq eMach emX86_64 &&
  Nat.beq eVer evCurrent &&
  Nat.beq eFlags 0 &&
  Nat.beq ehsz elf64Ehsize &&
  Nat.beq phent elf64PhdrSize &&
  Nat.blt 0 phnum &&
  Nat.blt phnum pnXnum &&
  Nat.ble elf64Ehsize phoff &&
  bytesLenAtLeast (phoff + phnum * elf64PhdrSize) bs

/-- Validate and parse the 64-byte ELF64 header for little-endian `ET_EXEC` or
static `ET_DYN` `EM_X86_64` binaries. Accepts both stripped (`e_shoff = 0`)
and unstripped images; rejects malformed `e_ident`, non-zero `EI_PAD`,
non-zero `e_flags`, bad `e_ehsize`/`e_phentsize`, `e_phnum == 0` or `>= pnXnum`,
overlapping `e_phoff < 64`, or truncated program header table. -/
@[expose] def parseElf64ImageHeader? (bs : List UInt8) :
    Option Elf64ImageHeader :=
  if !(bytesLenAtLeast elf64Ehsize bs && elf64ImageIdentOk bs) then none
  else
    match readU16Le? bs 16, readU16Le? bs 18, readU32Le? bs 20,
          readU64Le? bs 24, readU64Le? bs 32, readU64Le? bs 40,
          readU32Le? bs 48, readU16Le? bs 52, readU16Le? bs 54,
          readU16Le? bs 56, readU16Le? bs 58, readU16Le? bs 60,
          readU16Le? bs 62 with
    | some eTy, some eMach, some eVer, some entry, some phoff, some shoff,
      some eFlags, some ehsz, some phent, some phnum, some shent, some shnum,
      some shstr =>
      if imageHeaderFieldsOk bs eTy eMach eVer eFlags ehsz phent phnum phoff
      then
        some {
          eType := eTy
          eMachine := eMach
          eVersion := eVer
          eEntry := entry
          ePhoff := phoff
          eShoff := shoff
          eFlags := eFlags
          eEhsize := ehsz
          ePhentsize := phent
          ePhnum := phnum
          eShentsize := shent
          eShnum := shnum
          eShstrndx := shstr
        }
      else none
    | _, _, _, _, _, _, _, _, _, _, _, _, _ => none

/-- Sequential 56-byte `Elf64_Phdr` reader returning `(ph, restTail)`. -/
@[expose] def parseElf64PhdrStep? (idx : Nat) (tail : List UInt8) :
    Option (Elf64ProgramHdr × List UInt8) :=
  match readU32Step? tail with
  | none => none
  | some (pTy, r4) =>
    match readU32Step? r4 with
    | none => none
    | some (pFlg, r8) =>
      match readU64Step? r8 with
      | none => none
      | some (pOff, r16) =>
        match readU64Step? r16 with
        | none => none
        | some (pVa, r24) =>
          match readU64Step? r24 with
          | none => none
          | some (pPa, r32) =>
            match readU64Step? r32 with
            | none => none
            | some (pFsz, r40) =>
              match readU64Step? r40 with
              | none => none
              | some (pMsz, r48) =>
                match readU64Step? r48 with
                | none => none
                | some (pAln, rest) =>
                  some ({
                    idx := idx
                    pType := pTy
                    pFlags := pFlg
                    pOffset := pOff
                    pVaddr := pVa
                    pPaddr := pPa
                    pFilesz := pFsz
                    pMemsz := pMsz
                    pAlign := pAln
                  }, rest)

/-- Total `@Nat.rec` parser for `n` sequential 56-byte `Elf64_Phdr` entries,
requiring exact table exhaustion. -/
@[expose] def parseElf64PhdrsAux (n idx : Nat) (bs : List UInt8) :
    Option (List Elf64ProgramHdr) :=
  @Nat.rec (fun _ => Nat → List UInt8 → Option (List Elf64ProgramHdr))
    (fun _ rem =>
      match rem with
      | [] => some []
      | _ :: _ => none)
    (fun _ ih curIdx rem =>
      match parseElf64PhdrStep? curIdx rem with
      | none => none
      | some (ph, rest) =>
        match ih (curIdx + 1) rest with
        | none => none
        | some tl => some (ph :: tl))
    n idx bs

/-- `PT_LOAD` invariant checker: `W^X`, positive non-overflowing `p_memsz`,
`p_filesz <= p_memsz`, in-bounds file slice, executable segment non-empty,
`p_align >= 4096` power of two, and modulo congruence. -/
@[expose] def ptLoadValid (bs : List UInt8) (ph : Elf64ProgramHdr) : Bool :=
  Nat.beq ph.pType ptLoad &&
  phdrWxOk ph.pFlags &&
  Nat.blt 0 ph.pMemsz &&
  Nat.ble ph.pFilesz ph.pMemsz &&
  Nat.ble (ph.pVaddr + ph.pMemsz) u64AddressLimit &&
  bytesLenAtLeast (ph.pOffset + ph.pFilesz) bs &&
  Nat.ble pageSize4k ph.pAlign &&
  isPow2Nat64 ph.pAlign &&
  Nat.beq (Nat.mod ph.pOffset ph.pAlign) (Nat.mod ph.pVaddr ph.pAlign) &&
  (!phdrHasExec ph.pFlags || Nat.blt 0 ph.pFilesz)

/-- True iff `pFlags` is strictly `PF_R` or `PF_R | PF_W` (`{R, RW}`). -/
@[expose] def gnuStackFlagsOk (pFlags : Nat) : Bool :=
  Nat.beq pFlags pfR || Nat.beq pFlags (pfR + pfW)

/-- Allowlisted static program-header predicate. Rejects `PT_INTERP`,
`PT_DYNAMIC`, `PT_SHLIB`, `PT_TLS`, `PT_GNU_STACK` outside `{PF_R, PF_R|PF_W}`,
`W^X` violations, and unknown segment types fail-closed. -/
@[expose] def phdrEntryValid (bs : List UInt8) (ph : Elf64ProgramHdr) : Bool :=
  if Nat.beq ph.pType ptLoad then
    ptLoadValid bs ph
  else if Nat.beq ph.pType ptPhdr || Nat.beq ph.pType ptNote then
    phdrWxOk ph.pFlags &&
    !phdrHasExec ph.pFlags &&
    !phdrHasWrite ph.pFlags &&
    bytesLenAtLeast (ph.pOffset + ph.pFilesz) bs
  else if Nat.beq ph.pType ptGnuStack then
    gnuStackFlagsOk ph.pFlags &&
    bytesLenAtLeast (ph.pOffset + ph.pFilesz) bs
  else if Nat.beq ph.pType ptGnuEhFrame ||
          Nat.beq ph.pType ptGnuRelro ||
          Nat.beq ph.pType ptGnuProperty then
    phdrWxOk ph.pFlags &&
    !phdrHasExec ph.pFlags &&
    bytesLenAtLeast (ph.pOffset + ph.pFilesz) bs
  else
    false

/-- Round `addr` down to a `pageSz` boundary (`(addr / pageSz) * pageSz`). -/
@[expose] def roundDownPage (addr pageSz : Nat) : Nat :=
  Nat.div addr pageSz * pageSz

/-- Round `addr` up to a `pageSz` boundary. -/
@[expose] def roundUpPage (addr pageSz : Nat) : Nat :=
  Nat.div (addr + pageSz - 1) pageSz * pageSz

/-- Two `PT_LOAD` segments are disjoint on rounded `4 KiB` virtual pages
(`roundUpPage (va + memsz) 4096 <= roundDownPage va 4096`) and (when both
carry file bytes) in file offsets, preventing `MAP_FIXED` page replacement or
`.bss` zeroing from clobbering or exposing unscanned file bytes on shared pages.

File offsets are compared unrounded, so two segments may share a backing file
page at distinct virtual pages (the usual linker layout). Each `MAP_PRIVATE`
file mapping is copy-on-write, so writes through the writable mapping never
reach the executable one. Unscanned bytes on an executable segment's pages
(such as the ELF header) are mapped executable either way; CFG confinement,
not this predicate, keeps control flow off them. -/
@[expose] def ptLoadPairDisjoint (a b : Elf64ProgramHdr) : Bool :=
  let aEnd := roundUpPage (a.pVaddr + a.pMemsz) pageSize4k
  let aStart := roundDownPage a.pVaddr pageSize4k
  let bEnd := roundUpPage (b.pVaddr + b.pMemsz) pageSize4k
  let bStart := roundDownPage b.pVaddr pageSize4k
  let vaDisjoint := Nat.ble aEnd bStart || Nat.ble bEnd aStart
  let offDisjoint :=
    if Nat.beq a.pFilesz 0 || Nat.beq b.pFilesz 0 then true
    else
      Nat.ble (a.pOffset + a.pFilesz) b.pOffset ||
      Nat.ble (b.pOffset + b.pFilesz) a.pOffset
  vaDisjoint && offDisjoint

/-- Pairwise disjointness across all `PT_LOAD` segments via `List.foldr`. -/
@[expose] def ptLoadPairwiseDisjoint (segs : List Elf64ProgramHdr) : Bool :=
  (List.foldr (fun s st =>
    (s :: st.1, listAll (ptLoadPairDisjoint s) st.1 && st.2))
    ([], true) segs).2

/-- True iff `eEntry` falls inside `[pVaddr, pVaddr + pFilesz)` of an
executable `PT_LOAD` segment. -/
@[expose] def entryInExecLoad (eEntry : Nat)
    (execSegs : List Elf64ProgramHdr) : Bool :=
  listAny
    (fun s => Nat.ble s.pVaddr eEntry && Nat.blt eEntry (s.pVaddr + s.pFilesz))
    execSegs

/-- Extract `(seg, fileBytes)` pairs for exec `PT_LOAD`s (`List.foldr`). -/
@[expose] def extractExecPayloads? (bs : List UInt8)
    (segs : List Elf64ProgramHdr) :
    Option (List (Elf64ProgramHdr × List UInt8)) :=
  List.foldr (fun s acc =>
    match acc with
    | none => none
    | some tl =>
      match fastSliceBytes? bs s.pOffset s.pFilesz with
      | none => none
      | some bytes => some ((s, bytes) :: tl))
    (some []) segs

/-- Parse and validate an ELF64 `ET_EXEC` or static `ET_DYN` `EM_X86_64`
program header table, enforcing `W^X`, pairwise disjoint `PT_LOAD` segments,
exactly one `PT_GNU_STACK` with flags in `{PF_R, PF_R | PF_W}`, zero
`PT_INTERP`/`PT_DYNAMIC`, at least one executable `PT_LOAD`, and entry
containment within an executable `PT_LOAD`. -/
@[expose] def parseElf64ProgramHdrs? (bs : List UInt8) :
    Option Elf64ProgramImage :=
  match parseElf64ImageHeader? bs with
  | none => none
  | some hdr =>
    match fastSliceBytes? bs hdr.ePhoff (hdr.ePhnum * elf64PhdrSize) with
    | none => none
    | some phTable =>
      match parseElf64PhdrsAux hdr.ePhnum 0 phTable with
      | none => none
      | some phdrs =>
        if !listAll (phdrEntryValid bs) phdrs then none
        else
          let gnuStacks :=
            listFilter (fun p => Nat.beq p.pType ptGnuStack) phdrs
          if !Nat.beq gnuStacks.length 1 then none
          else
            let loadSegs := listFilter (fun p => Nat.beq p.pType ptLoad) phdrs
            match loadSegs with
            | [] => none
            | _ :: _ =>
              if !ptLoadPairwiseDisjoint loadSegs then none
              else
                let execSegs :=
                  listFilter (fun p => phdrHasExec p.pFlags) loadSegs
                match execSegs with
                | [] => none
                | _ :: _ =>
                  if !entryInExecLoad hdr.eEntry execSegs then none
                  else
                    match extractExecPayloads? bs execSegs with
                    | none => none
                    | some payloads =>
                      some {
                        header := hdr
                        phdrs := phdrs
                        loadSegments := loadSegs
                        execSegments := execSegs
                        execPayloads := payloads
                      }

/-! ## 4. Zero-Syscall & Constant-Time (`DOITM`) Opcode Gates -/

/-- Default decoder configuration for post-link `ET_EXEC`/`ET_DYN` image
scanning (`requireRelocForRip := false`, plus `bmi1`/`popcnt`/`lzcnt` enabled
so `F3` bit-counting instructions decode explicitly and can be rejected by
`insnIsDoitmConstantTime` rather than failing arbitrarily or aliasing `BSR`). -/
@[expose] def doitmImageDecodeCfg : DecodeConfig :=
  { requireRelocForRip := false
    bmi1 := true
    popcnt := true
    lzcnt := true }

/-- True iff `ins` is a system-call / software-interrupt entry instruction
(`syscall`, `sysenter`, or `int <vec>`). -/
@[expose] def insnIsSyscall (ins : DecodedInsn) : Bool :=
  match ins with
  | .syscall | .sysenter | .intImm _ => true
  | _ => false

/-- True iff `ins` is a system-call or software-trap opcode (`syscall`,
`sysenter`, `int <vec>`, `int3`, or `ud2`). -/
@[expose] def insnIsSyscallOrTrap (ins : DecodedInsn) : Bool :=
  match ins with
  | .syscall | .sysenter | .intImm _ | .int3 | .ud2 => true
  | _ => false

/-- Wildcard-free constant-time (`DOITM`) opcode classification. Rejects
variable-latency integer division (`div`/`idiv`), bit-scan/population-count
(`bsf`/`tzcnt`/`popcnt`/`lzcnt`), and syscalls/traps (`syscall`/`sysenter`/
`int`/`int3`/`ud2`); any unmodeled opcode (`VGATHER*`/`VSCATTER*`/`VPERMB`/
x87/FP) fails closed at `decodeStream`. -/
@[expose] def insnIsDoitmConstantTime (ins : DecodedInsn) : Bool :=
  match ins with
  | .vbin _ _ _ _ _ => true
  | .vshift _ _ _ _ _ => true
  | .vload _ _ _ _ => true
  | .vmovhps _ _ _ => true
  | .vstore _ _ _ _ => true
  | .vpmovzxwd _ _ _ => true
  | .vperm2i128 _ _ _ _ => true
  | .vinserti128 _ _ _ _ => true
  | .vextracti128 _ _ _ => true
  | .vpermq _ _ _ => true
  | .vpshufd _ _ _ _ => true
  | .vpblendd _ _ _ _ _ => true
  | .vzeroupper => true
  | .lea _ _ _ => true
  | .movsxd _ _ => true
  | .movRegRm _ _ _ => true
  | .movRmReg _ _ _ => true
  | .movImm _ _ _ => true
  | .aluRmReg _ _ _ _ _ => true
  | .aluRegRm _ _ _ _ => true
  | .aluRmImm _ _ _ _ _ => true
  | .shiftRmImm _ _ _ _ => true
  | .imulRegRm _ _ _ => true
  | .xchgAx _ _ => true
  | .pushReg _ _ => true
  | .popReg _ _ => true
  | .endbr64 => true
  | .nop => true
  | .ret => true
  | .jmpRel _ => true
  | .callRel _ => true
  | .jmpInd _ => true
  | .callInd _ => true
  | .div _ _ _ _ => false
  | .bsf _ _ _ => false
  | .tzcnt _ _ _ => false
  | .popcnt _ _ _ => false
  | .lzcnt _ _ _ => false
  | .syscall => false
  | .sysenter => false
  | .intImm _ => false
  | .int3 => false
  | .ud2 => false

/-- Decoded-stream zero-syscall gate (fails closed on decode errors). -/
@[expose] def checkStreamZeroSyscall
    (cfg : DecodeConfig := doitmImageDecodeCfg)
    (bs : List UInt8) : Bool :=
  match decodeStream cfg [] bs with
  | none => false
  | some trace => listAll (fun e => !insnIsSyscall e.2.2) trace

/-- Decoded-stream strict zero-syscall-or-trap gate (`syscall`/`sysenter`/
`int`/`int3`/`ud2`, fails closed on decode errors). -/
@[expose] def checkStreamZeroSyscallOrTrap
    (cfg : DecodeConfig := doitmImageDecodeCfg)
    (bs : List UInt8) : Bool :=
  match decodeStream cfg [] bs with
  | none => false
  | some trace => listAll (fun e => !insnIsSyscallOrTrap e.2.2) trace

/-- Decoded-stream constant-time (`DOITM`) opcode gate. -/
@[expose] def checkStreamDoitmConstantTime
    (cfg : DecodeConfig := doitmImageDecodeCfg)
    (bs : List UInt8) : Bool :=
  match decodeStream cfg [] bs with
  | none => false
  | some trace => listAll (fun e => insnIsDoitmConstantTime e.2.2) trace

/-- True iff `ins` unconditionally transfers control away (`.ret` or direct
`.jmpRel`), preventing sequential fallthrough past the end of an executable
payload into RX page slop. `.ret` relies on the ABI return-stack invariant. -/
@[expose] def insnIsUncondTerm (ins : DecodedInsn) : Bool :=
  match ins with
  | .ret | .jmpRel _ => true
  | _ => false

/-- True iff `ins` is an indirect branch or call (`.jmpInd` / `.callInd`),
which post-link image CFG confinement rejects fail-closed. -/
@[expose] def insnIsIndirectControl (ins : DecodedInsn) : Bool :=
  match ins with
  | .jmpInd _ | .callInd _ => true
  | _ => false

/-- True iff `ins` is a direct PC-relative branch or call. -/
@[expose] def insnIsDirectBranch (ins : DecodedInsn) : Bool :=
  match ins with
  | .jmpRel _ | .callRel _ => true
  | _ => false

/-- True iff `ins` is a direct PC-relative call (`.callRel`). -/
@[expose] def insnIsDirectCall (ins : DecodedInsn) : Bool :=
  match ins with
  | .callRel _ => true
  | _ => false

/-- True iff `ins` pushes, pops, or accesses `rsp`/`rbp` other than a direct
`.callRel`, preventing intra-image return-stack forgery for `.ret`. -/
@[expose] def insnTampersReturnStack (ins : DecodedInsn) : Bool :=
  match ins with
  | .callRel _ => false
  | _ => insnTouchesStackOrFrame ins

/-- Compute non-wrapping 64-bit target virtual address for a direct
`jmpRel`/`callRel` at `(segVa + off)` of byte length `len` (`nextRIP + disp`),
returning `none` on underflow/overflow or non-branch instructions. -/
@[expose] def directBranchTargetVa? (segVa off len : Nat)
    (ins : DecodedInsn) : Option Nat :=
  match ins with
  | .jmpRel disp | .callRel disp =>
    match Int.add (Int.ofNat (segVa + off + len)) disp with
    | Int.ofNat n => if Nat.blt n u64AddressLimit then some n else none
    | Int.negSucc _ => none
  | _ => none

/-- Decode all executable `PT_LOAD` payloads via structural `List.foldr`. -/
@[expose] def decodeAllExecPayloads? (cfg : DecodeConfig)
    (ps : List (Elf64ProgramHdr × List UInt8)) :
    Option (List (Elf64ProgramHdr × List (Nat × Nat × DecodedInsn))) :=
  List.foldr
    (fun pair acc =>
      match acc with
      | none => none
      | some rest =>
        match decodeStream cfg [] pair.2 with
        | none => none
        | some tr => some ((pair.1, tr) :: rest))
    (some []) ps

/-- Collect all decoded instruction start virtual addresses `(seg.pVaddr + e.1)`
across every executable segment trace. -/
@[expose] def collectAllStartVas
    (traces : List (Elf64ProgramHdr × List (Nat × Nat × DecodedInsn))) :
    List Nat :=
  List.foldr
    (fun pair acc =>
      List.foldr (fun e a => (pair.1.pVaddr + e.1) :: a) acc pair.2)
    [] traces

/-- True iff decoded trace `tr` is non-empty and ends in an unconditional
transfer (`insnIsUncondTerm`), preventing fallthrough past the payload end. -/
@[expose] def traceTerminatedOk
    (tr : List (Nat × Nat × DecodedInsn)) : Bool :=
  match List.foldl (fun _ x => some x) none tr with
  | none => false
  | some last => insnIsUncondTerm last.2.2

/-- Per-instruction verification check combining zero-syscall, `DOITM`
constant-time opcodes, indirect-control rejection, return-stack tamper
rejection (`insnTampersReturnStack`), `.callRel` fallthrough boundary
verification, and intra-image decoded branch-target boundary confinement
against `validVas`. -/
@[expose] def entryZeroSyscallDoitmCfOk (validVas : List Nat) (segVa : Nat)
    (e : Nat × Nat × DecodedInsn) : Bool :=
  let ins := e.2.2
  !insnIsSyscall ins &&
  insnIsDoitmConstantTime ins &&
  !insnIsIndirectControl ins &&
  !insnTampersReturnStack ins &&
  (!insnIsDirectCall ins ||
    natListContains validVas (segVa + e.1 + e.2.1)) &&
  (!insnIsDirectBranch ins ||
    match directBranchTargetVa? segVa e.1 e.2.1 ins with
    | some tgt => natListContains validVas tgt
    | none => false)

/-- Whole-image `ET_EXEC`/`ET_DYN` verification gate: parses program headers
(`W^X`, disjoint `PT_LOAD`, zero `PT_INTERP`/`PT_DYNAMIC`/exec-stack), decodes
every executable `PT_LOAD` payload, confines intra-image control flow (banning
indirect branches/calls, validating all direct branch targets against decoded
instruction VAs, and requiring unconditional termination on every exec payload),
aligns `e_entry` to a decoded boundary, and enforces zero syscalls plus `DOITM`
constant-time opcodes. -/
@[expose] def checkElf64ImageZeroSyscallAndDoitm
    (cfg : DecodeConfig := doitmImageDecodeCfg) (bs : List UInt8) :
    Option Elf64ProgramImage :=
  match parseElf64ProgramHdrs? bs with
  | none => none
  | some img =>
    match decodeAllExecPayloads? cfg img.execPayloads with
    | none => none
    | some traces =>
      let validVas := collectAllStartVas traces
      if natListContains validVas img.header.eEntry &&
         listAll (fun p =>
           traceTerminatedOk p.2 &&
           listAll (entryZeroSyscallDoitmCfOk validVas p.1.pVaddr) p.2)
           traces then
        some img
      else none

/-! ## 5. Soundness & Rejection Theorems (`[]` / `['propext']` Axioms) -/

private theorem bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => rfl

private theorem bandRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => exact h

private theorem borEq {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

private theorem boolNotTrue {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact Bool.noConfusion h

private theorem iteBoolTrue {α : Type} {c : Bool} {t e : α} (h : c = true) :
    (if c then t else e) = t := by
  subst h; rfl

private theorem iteBoolFalse {α : Type} {c : Bool} {t e : α} (h : c = false) :
    (if c then t else e) = e := by
  subst h; rfl

private theorem listAll_mem {α : Type} (p : α → Bool) :
    ∀ (xs : List α), listAll p xs = true → ∀ x, List.Mem x xs → p x = true
  | [], _, x, hm => by cases hm
  | y :: ys, h, x, hm => by
    change (p y && listAll p ys) = true at h
    cases hm with
    | head => exact bandLeft h
    | tail _ htl => exact listAll_mem p ys (bandRight h) x htl

private theorem listAny_mem {α : Type} (p : α → Bool) :
    ∀ (xs : List α), listAny p xs = true → ∃ x, List.Mem x xs ∧ p x = true
  | [], h => by exact Bool.noConfusion h
  | y :: ys, h => by
    change (p y || listAny p ys) = true at h
    cases hy : p y with
    | true => exact ⟨y, List.Mem.head _, hy⟩
    | false =>
      rw [hy] at h
      have hRest := listAny_mem p ys h
      cases hRest with
      | intro z hz => exact ⟨z, List.Mem.tail _ hz.1, hz.2⟩

private theorem listFilter_mem {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (x : α),
      List.Mem x (listFilter p xs) → List.Mem x xs ∧ p x = true
  | [], x, hm => by cases hm
  | y :: ys, x, hm => by
    change List.Mem x
      (if p y then y :: listFilter p ys else listFilter p ys) at hm
    cases hy : p y with
    | true =>
      rw [iteBoolTrue hy] at hm
      cases hm with
      | head => exact ⟨List.Mem.head _, hy⟩
      | tail _ htl =>
        have hR := listFilter_mem p ys x htl
        exact ⟨List.Mem.tail _ hR.1, hR.2⟩
    | false =>
      rw [iteBoolFalse hy] at hm
      have hR := listFilter_mem p ys x hm
      exact ⟨List.Mem.tail _ hR.1, hR.2⟩

private theorem parseElf64PhdrsAux_len :
    ∀ (n idx : Nat) (bs : List UInt8) (phdrs : List Elf64ProgramHdr),
      parseElf64PhdrsAux n idx bs = some phdrs → phdrs.length = n := by
  intro n
  induction n with
  | zero =>
    intro idx bs phdrs h
    cases bs with
    | nil =>
      change some [] = some phdrs at h
      have heq := Option.some.inj h
      subst heq; rfl
    | cons _ _ =>
      change none = some phdrs at h
      cases h
  | succ k ih =>
    intro idx bs phdrs h
    change
      (match parseElf64PhdrStep? idx bs with
       | none => none
       | some (ph, rest) =>
         match parseElf64PhdrsAux k (idx + 1) rest with
         | none => none
         | some tl => some (ph :: tl)) = some phdrs at h
    cases hStep : parseElf64PhdrStep? idx bs with
    | none => rw [hStep] at h; cases h
    | some p =>
      rw [hStep] at h
      dsimp only at h
      cases p with
      | mk ph rest =>
        cases hRec : parseElf64PhdrsAux k (idx + 1) rest with
        | none => rw [hRec] at h; cases h
        | some tl =>
          rw [hRec] at h
          dsimp only at h
          have heq := Option.some.inj h
          subst heq
          exact congrArg Nat.succ (ih (idx + 1) rest tl hRec)

private theorem extractExecPayloads?_mem (bs : List UInt8) :
    ∀ (segs : List Elf64ProgramHdr)
      (payloads : List (Elf64ProgramHdr × List UInt8)),
      extractExecPayloads? bs segs = some payloads →
      (∀ p, List.Mem p payloads →
        List.Mem p.1 segs ∧
        fastSliceBytes? bs p.1.pOffset p.1.pFilesz = some p.2) ∧
      payloads.length = segs.length := by
  intro segs
  induction segs with
  | nil =>
    intro payloads h
    have heq := Option.some.inj h
    subst heq
    refine ⟨?_, rfl⟩
    intro _ hm
    cases hm
  | cons s rest ih =>
    intro payloads h
    change
      (match extractExecPayloads? bs rest with
       | none => none
       | some tl =>
         match fastSliceBytes? bs s.pOffset s.pFilesz with
         | none => none
         | some bytes => some ((s, bytes) :: tl)) = some payloads at h
    cases hRec : extractExecPayloads? bs rest with
    | none => rw [hRec] at h; cases h
    | some tl =>
      rw [hRec] at h
      dsimp only at h
      cases hSl : fastSliceBytes? bs s.pOffset s.pFilesz with
      | none => rw [hSl] at h; cases h
      | some bytes =>
        rw [hSl] at h
        have heq := Option.some.inj h
        subst heq
        have hI := ih tl hRec
        refine ⟨?_, congrArg Nat.succ hI.2⟩
        intro p hm
        cases hm with
        | head => exact ⟨List.Mem.head _, hSl⟩
        | tail _ htl =>
          have hP := hI.1 p htl
          exact ⟨List.Mem.tail _ hP.1, hP.2⟩

/-- Explicit `Prop` specification of page-rounded `ptLoadPairDisjoint`. -/
@[expose] def PtLoadDisjointProp (a b : Elf64ProgramHdr) : Prop :=
  (roundUpPage (a.pVaddr + a.pMemsz) pageSize4k ≤
      roundDownPage b.pVaddr pageSize4k ∨
    roundUpPage (b.pVaddr + b.pMemsz) pageSize4k ≤
      roundDownPage a.pVaddr pageSize4k) ∧
  (a.pFilesz = 0 ∨ b.pFilesz = 0 ∨
    a.pOffset + a.pFilesz ≤ b.pOffset ∨ b.pOffset + b.pFilesz ≤ a.pOffset)

private theorem ptLoadPairDisjoint_sound (a b : Elf64ProgramHdr)
    (h : ptLoadPairDisjoint a b = true) : PtLoadDisjointProp a b := by
  dsimp only [ptLoadPairDisjoint] at h
  have hVa := bandLeft h
  have hOff := bandRight h
  refine ⟨?_, ?_⟩
  · cases borEq hVa with
    | inl h1 => exact Or.inl (Nat.le_of_ble_eq_true h1)
    | inr h2 => exact Or.inr (Nat.le_of_ble_eq_true h2)
  · cases hZero : (Nat.beq a.pFilesz 0 || Nat.beq b.pFilesz 0) with
    | true =>
      cases borEq hZero with
      | inl ha => exact Or.inl (Nat.eq_of_beq_eq_true ha)
      | inr hb => exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true hb))
    | false =>
      rw [iteBoolFalse hZero] at hOff
      cases borEq hOff with
      | inl h1 => exact Or.inr (Or.inr (Or.inl (Nat.le_of_ble_eq_true h1)))
      | inr h2 => exact Or.inr (Or.inr (Or.inr (Nat.le_of_ble_eq_true h2)))

private theorem listGet?_mem {α : Type} :
    ∀ (xs : List α) (b : α) (j : Nat),
      listGet? xs j = some b → List.Mem b xs
  | [], _, j, hb => by cases j <;> cases hb
  | r :: rs, b, 0, hb => by
    have hr : r = b := Option.some.inj hb
    subst hr; exact List.Mem.head _
  | _ :: rs, b, j + 1, hb => List.Mem.tail _ (listGet?_mem rs b j hb)

private theorem ptLoadPairwiseDisjoint_fst :
    ∀ (segs : List Elf64ProgramHdr),
      (List.foldr (fun s st =>
        (s :: st.1, listAll (ptLoadPairDisjoint s) st.1 && st.2))
        ([], true) segs).1 = segs
  | [] => rfl
  | s :: rest => congrArg (List.cons s) (ptLoadPairwiseDisjoint_fst rest)

private theorem ptLoadPairwiseDisjoint_at_pairs :
    ∀ (segs : List Elf64ProgramHdr),
      ptLoadPairwiseDisjoint segs = true →
      ∀ (i j : Nat) (a b : Elf64ProgramHdr),
        i < j →
        listGet? segs i = some a →
        listGet? segs j = some b →
        PtLoadDisjointProp a b := by
  intro segs
  induction segs with
  | nil =>
    intro _ i _ a _ _ ha _
    cases i <;> cases ha
  | cons s rest ih =>
    intro h i j a b hij ha hb
    dsimp only [ptLoadPairwiseDisjoint] at h
    change (listAll (ptLoadPairDisjoint s)
      (List.foldr (fun s st =>
        (s :: st.1, listAll (ptLoadPairDisjoint s) st.1 && st.2))
        ([], true) rest).1 && ptLoadPairwiseDisjoint rest) = true at h
    rw [ptLoadPairwiseDisjoint_fst rest] at h
    have hAll := listAll_mem (ptLoadPairDisjoint s) rest (bandLeft h)
    have hRest := bandRight h
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd hij (Nat.lt_irrefl 0)
      | succ j' =>
        have haEq : s = a := Option.some.inj ha
        subst haEq
        exact ptLoadPairDisjoint_sound s b
          (hAll b (listGet?_mem rest b j' hb))
    | succ i' =>
      cases j with
      | zero => exact absurd hij (Nat.not_lt_zero _)
      | succ j' =>
        exact ih hRest i' j' a b (Nat.lt_of_succ_lt_succ hij) ha hb

/-- Complete structural `Prop` witness guaranteed whenever
`parseElf64ProgramHdrs? bs = some img`. -/
@[expose] def Elf64ProgramImageValid (bs : List UInt8)
    (img : Elf64ProgramImage) : Prop :=
  (img.header.eType = etExec ∨ img.header.eType = etDyn) ∧
  img.header.eMachine = emX86_64 ∧
  img.header.eVersion = evCurrent ∧
  img.header.eFlags = 0 ∧
  img.header.eEhsize = elf64Ehsize ∧
  img.header.ePhentsize = elf64PhdrSize ∧
  0 < img.header.ePhnum ∧
  img.header.ePhnum < pnXnum ∧
  elf64Ehsize ≤ img.header.ePhoff ∧
  img.phdrs.length = img.header.ePhnum ∧
  (∀ ph, List.Mem ph img.phdrs →
    phdrEntryValid bs ph = true ∧
    ph.pType ≠ ptInterp ∧
    ph.pType ≠ ptDynamic ∧
    ph.pType ≠ ptShlib ∧
    ph.pType ≠ ptTls ∧
    ¬ (phdrHasWrite ph.pFlags = true ∧ phdrHasExec ph.pFlags = true) ∧
    (ph.pType = ptGnuStack →
      (ph.pFlags = pfR ∨ ph.pFlags = pfR + pfW) ∧
      phdrHasExec ph.pFlags = false)) ∧
  (listFilter (fun p => Nat.beq p.pType ptGnuStack) img.phdrs).length = 1 ∧
  img.loadSegments ≠ [] ∧
  (∀ s, List.Mem s img.loadSegments →
    List.Mem s img.phdrs ∧ s.pType = ptLoad ∧ ptLoadValid bs s = true) ∧
  (∀ i j a b, i < j →
    listGet? img.loadSegments i = some a →
    listGet? img.loadSegments j = some b →
    PtLoadDisjointProp a b) ∧
  img.execSegments ≠ [] ∧
  (∀ s, List.Mem s img.execSegments →
    List.Mem s img.loadSegments ∧ phdrHasExec s.pFlags = true ∧
    0 < s.pFilesz) ∧
  (∃ s, List.Mem s img.execSegments ∧
    s.pVaddr ≤ img.header.eEntry ∧
    img.header.eEntry < s.pVaddr + s.pFilesz) ∧
  (∀ p, List.Mem p img.execPayloads →
    List.Mem p.1 img.execSegments ∧
    fastSliceBytes? bs p.1.pOffset p.1.pFilesz = some p.2) ∧
  img.execPayloads.length = img.execSegments.length

private theorem phdrEntryValid_implies_safety (bs : List UInt8)
    (ph : Elf64ProgramHdr) (h : phdrEntryValid bs ph = true) :
    ph.pType ≠ ptInterp ∧
    ph.pType ≠ ptDynamic ∧
    ph.pType ≠ ptShlib ∧
    ph.pType ≠ ptTls ∧
    ¬ (phdrHasWrite ph.pFlags = true ∧ phdrHasExec ph.pFlags = true) ∧
    (ph.pType = ptGnuStack →
      (ph.pFlags = pfR ∨ ph.pFlags = pfR + pfW) ∧
      phdrHasExec ph.pFlags = false) := by
  dsimp only [phdrEntryValid] at h
  cases hLoad : Nat.beq ph.pType ptLoad with
  | true =>
    rw [iteBoolTrue hLoad] at h
    have hTy := Nat.eq_of_beq_eq_true hLoad
    dsimp only [ptLoadValid] at h
    have hWx := bandRight (bandLeft (bandLeft (bandLeft (bandLeft
      (bandLeft (bandLeft (bandLeft (bandLeft h))))))))
    dsimp only [phdrWxOk] at hWx
    have hNotWX := boolNotTrue (bandRight hWx)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro heq; rw [hTy] at heq; cases heq
    · intro heq; rw [hTy] at heq; cases heq
    · intro heq; rw [hTy] at heq; cases heq
    · intro heq; rw [hTy] at heq; cases heq
    · intro hPair
      have hT : (phdrHasWrite ph.pFlags && phdrHasExec ph.pFlags) = true := by
        rw [hPair.1, hPair.2]; rfl
      rw [hT] at hNotWX; cases hNotWX
    · intro heq; rw [hTy] at heq; cases heq
  | false =>
    rw [iteBoolFalse hLoad] at h
    cases hMeta : (Nat.beq ph.pType ptPhdr || Nat.beq ph.pType ptNote) with
    | true =>
      rw [iteBoolTrue hMeta] at h
      have hWx := bandLeft (bandLeft (bandLeft h))
      dsimp only [phdrWxOk] at hWx
      have hNotWX := boolNotTrue (bandRight hWx)
      cases borEq hMeta with
      | inl hPhdr =>
        have hTy := Nat.eq_of_beq_eq_true hPhdr
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hTy]; exact fun e => by cases e
        · rw [hTy]; exact fun e => by cases e
        · rw [hTy]; exact fun e => by cases e
        · rw [hTy]; exact fun e => by cases e
        · intro hPair
          have hT : (phdrHasWrite ph.pFlags && phdrHasExec ph.pFlags) =
              true := by
            rw [hPair.1, hPair.2]; rfl
          rw [hT] at hNotWX; cases hNotWX
        · rw [hTy]; exact fun e => by cases e
      | inr hNote =>
        have hTy := Nat.eq_of_beq_eq_true hNote
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hTy]; exact fun e => by cases e
        · rw [hTy]; exact fun e => by cases e
        · rw [hTy]; exact fun e => by cases e
        · rw [hTy]; exact fun e => by cases e
        · intro hPair
          have hT : (phdrHasWrite ph.pFlags && phdrHasExec ph.pFlags) =
              true := by
            rw [hPair.1, hPair.2]; rfl
          rw [hT] at hNotWX; cases hNotWX
        · rw [hTy]; exact fun e => by cases e
    | false =>
      rw [iteBoolFalse hMeta] at h
      cases hStack : Nat.beq ph.pType ptGnuStack with
      | true =>
        rw [iteBoolTrue hStack] at h
        have hTy := Nat.eq_of_beq_eq_true hStack
        have hFlg := bandLeft h
        dsimp only [gnuStackFlagsOk] at hFlg
        cases borEq hFlg with
        | inl hR =>
          have hF := Nat.eq_of_beq_eq_true hR
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hTy]; exact fun e => by cases e
          · rw [hTy]; exact fun e => by cases e
          · rw [hTy]; exact fun e => by cases e
          · rw [hTy]; exact fun e => by cases e
          · intro hPair
            have hX := hPair.2; rw [hF] at hX; exact Bool.noConfusion hX
          · intro _; exact ⟨Or.inl hF, by rw [hF]; rfl⟩
        | inr hRW =>
          have hF := Nat.eq_of_beq_eq_true hRW
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hTy]; exact fun e => by cases e
          · rw [hTy]; exact fun e => by cases e
          · rw [hTy]; exact fun e => by cases e
          · rw [hTy]; exact fun e => by cases e
          · intro hPair
            have hX := hPair.2; rw [hF] at hX; exact Bool.noConfusion hX
          · intro _; exact ⟨Or.inr hF, by rw [hF]; rfl⟩
      | false =>
        rw [iteBoolFalse hStack] at h
        cases hGnu : (Nat.beq ph.pType ptGnuEhFrame ||
                      Nat.beq ph.pType ptGnuRelro ||
                      Nat.beq ph.pType ptGnuProperty) with
        | false =>
          rw [iteBoolFalse hGnu] at h; cases h
        | true =>
          rw [iteBoolTrue hGnu] at h
          have hWx := bandLeft (bandLeft h)
          dsimp only [phdrWxOk] at hWx
          have hNotWX := boolNotTrue (bandRight hWx)
          have hTyNe : ∀ t, ph.pType = t →
              (Nat.beq t ptGnuEhFrame ||
               Nat.beq t ptGnuRelro || Nat.beq t ptGnuProperty) = true := by
            intro t heq; subst heq; exact hGnu
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro heq; exact Bool.noConfusion (hTyNe ptInterp heq)
          · intro heq; exact Bool.noConfusion (hTyNe ptDynamic heq)
          · intro heq; exact Bool.noConfusion (hTyNe ptShlib heq)
          · intro heq; exact Bool.noConfusion (hTyNe ptTls heq)
          · intro hPair
            have hT : (phdrHasWrite ph.pFlags && phdrHasExec ph.pFlags) =
                true := by
              rw [hPair.1, hPair.2]; rfl
            rw [hT] at hNotWX; cases hNotWX
          · intro heq; rw [heq] at hStack; exact Bool.noConfusion hStack

private theorem imageHeaderFieldsOk_sound
    {bs : List UInt8}
    {eTy eMach eVer eFlags ehsz phent phnum phoff : Nat}
    (h : imageHeaderFieldsOk bs eTy eMach eVer eFlags ehsz phent phnum phoff =
      true) :
    (eTy = etExec ∨ eTy = etDyn) ∧
    eMach = emX86_64 ∧
    eVer = evCurrent ∧
    eFlags = 0 ∧
    ehsz = elf64Ehsize ∧
    phent = elf64PhdrSize ∧
    0 < phnum ∧
    phnum < pnXnum ∧
    elf64Ehsize ≤ phoff := by
  dsimp only [imageHeaderFieldsOk] at h
  have c9 := bandLeft h
  have c8 := bandLeft c9
  have c7 := bandLeft c8
  have c6 := bandLeft c7
  have c5 := bandLeft c6
  have c4 := bandLeft c5
  have c3 := bandLeft c4
  have c2 := bandLeft c3
  have c1 := bandLeft c2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases borEq c1 with
    | inl he => exact Or.inl (Nat.eq_of_beq_eq_true he)
    | inr hd => exact Or.inr (Nat.eq_of_beq_eq_true hd)
  · exact Nat.eq_of_beq_eq_true (bandRight c2)
  · exact Nat.eq_of_beq_eq_true (bandRight c3)
  · exact Nat.eq_of_beq_eq_true (bandRight c4)
  · exact Nat.eq_of_beq_eq_true (bandRight c5)
  · exact Nat.eq_of_beq_eq_true (bandRight c6)
  · exact Nat.le_of_ble_eq_true (bandRight c7)
  · exact Nat.le_of_ble_eq_true (bandRight c8)
  · exact Nat.le_of_ble_eq_true (bandRight c9)

private theorem parseElf64ImageHeader?_sound (bs : List UInt8)
    (hdr : Elf64ImageHeader) (h : parseElf64ImageHeader? bs = some hdr) :
    (hdr.eType = etExec ∨ hdr.eType = etDyn) ∧
    hdr.eMachine = emX86_64 ∧
    hdr.eVersion = evCurrent ∧
    hdr.eFlags = 0 ∧
    hdr.eEhsize = elf64Ehsize ∧
    hdr.ePhentsize = elf64PhdrSize ∧
    0 < hdr.ePhnum ∧
    hdr.ePhnum < pnXnum ∧
    elf64Ehsize ≤ hdr.ePhoff := by
  dsimp only [parseElf64ImageHeader?] at h
  cases hPre : (bytesLenAtLeast elf64Ehsize bs && elf64ImageIdentOk bs) with
  | false =>
    have hNeg : (!(bytesLenAtLeast elf64Ehsize bs && elf64ImageIdentOk bs)) =
        true := by
      rw [hPre]; rfl
    rw [iteBoolTrue hNeg] at h
    cases h
  | true =>
    have hNeg : (!(bytesLenAtLeast elf64Ehsize bs && elf64ImageIdentOk bs)) =
        false := by
      rw [hPre]; rfl
    rw [iteBoolFalse hNeg] at h
    cases hTy : readU16Le? bs 16 with
      | none => rw [hTy] at h; cases h
      | some eTy =>
        rw [hTy] at h
        cases hMc : readU16Le? bs 18 with
        | none => rw [hMc] at h; cases h
        | some eMach =>
          rw [hMc] at h
          cases hVr : readU32Le? bs 20 with
          | none => rw [hVr] at h; cases h
          | some eVer =>
            rw [hVr] at h
            cases hEn : readU64Le? bs 24 with
            | none => rw [hEn] at h; cases h
            | some entry =>
              rw [hEn] at h
              cases hPh : readU64Le? bs 32 with
              | none => rw [hPh] at h; cases h
              | some phoff =>
                rw [hPh] at h
                cases hSh : readU64Le? bs 40 with
                | none => rw [hSh] at h; cases h
                | some shoff =>
                  rw [hSh] at h
                  cases hFl : readU32Le? bs 48 with
                  | none => rw [hFl] at h; cases h
                  | some eFlags =>
                    rw [hFl] at h
                    cases hEh : readU16Le? bs 52 with
                    | none => rw [hEh] at h; cases h
                    | some ehsz =>
                      rw [hEh] at h
                      cases hPe : readU16Le? bs 54 with
                      | none => rw [hPe] at h; cases h
                      | some phent =>
                        rw [hPe] at h
                        cases hPn : readU16Le? bs 56 with
                        | none => rw [hPn] at h; cases h
                        | some phnum =>
                          rw [hPn] at h
                          cases hSe : readU16Le? bs 58 with
                          | none => rw [hSe] at h; cases h
                          | some shent =>
                            rw [hSe] at h
                            cases hSn : readU16Le? bs 60 with
                            | none => rw [hSn] at h; cases h
                            | some shnum =>
                              rw [hSn] at h
                              cases hSs : readU16Le? bs 62 with
                              | none => rw [hSs] at h; cases h
                              | some shstr =>
                                rw [hSs] at h
                                dsimp only at h
                                cases hOk :
                                  imageHeaderFieldsOk bs eTy eMach eVer eFlags
                                    ehsz phent phnum phoff with
                                | false => rw [iteBoolFalse hOk] at h; cases h
                                | true =>
                                  rw [iteBoolTrue hOk] at h
                                  have heq := Option.some.inj h
                                  subst heq
                                  exact imageHeaderFieldsOk_sound hOk

/-- Soundness theorem for `parseElf64ProgramHdrs?` (`['propext']` max). -/
theorem parseElf64ProgramHdrs?_sound (bs : List UInt8)
    (img : Elf64ProgramImage) (h : parseElf64ProgramHdrs? bs = some img) :
    Elf64ProgramImageValid bs img := by
  unfold parseElf64ProgramHdrs? at h
  cases hHdr : parseElf64ImageHeader? bs with
  | none => rw [hHdr] at h; cases h
  | some hdr =>
    rw [hHdr] at h
    dsimp only at h
    cases hSl : fastSliceBytes? bs hdr.ePhoff (hdr.ePhnum * elf64PhdrSize) with
    | none => rw [hSl] at h; cases h
    | some phTable =>
      rw [hSl] at h
      dsimp only at h
      cases hPh : parseElf64PhdrsAux hdr.ePhnum 0 phTable with
      | none => rw [hPh] at h; cases h
      | some phdrs =>
        rw [hPh] at h
        dsimp only at h
        cases hValid : listAll (phdrEntryValid bs) phdrs with
        | false =>
          have hNV : (!listAll (phdrEntryValid bs) phdrs) = true := by
            rw [hValid]; rfl
          rw [iteBoolTrue hNV] at h; cases h
        | true =>
          have hNV : (!listAll (phdrEntryValid bs) phdrs) = false := by
            rw [hValid]; rfl
          rw [iteBoolFalse hNV] at h
          cases hGnuCnt :
            Nat.beq (listFilter (fun p => Nat.beq p.pType ptGnuStack)
              phdrs).length 1 with
          | false =>
            have hNG :
                (!Nat.beq (listFilter (fun p => Nat.beq p.pType ptGnuStack)
                  phdrs).length 1) = true := by
              rw [hGnuCnt]; rfl
            rw [iteBoolTrue hNG] at h; cases h
          | true =>
            have hNG :
                (!Nat.beq (listFilter (fun p => Nat.beq p.pType ptGnuStack)
                  phdrs).length 1) = false := by
              rw [hGnuCnt]; rfl
            rw [iteBoolFalse hNG] at h
            cases hLoads :
                listFilter (fun p => Nat.beq p.pType ptLoad) phdrs with
            | nil => rw [hLoads] at h; cases h
            | cons l0 ls =>
              rw [hLoads] at h
              dsimp only at h
              cases hDisj : ptLoadPairwiseDisjoint (l0 :: ls) with
              | false =>
                have hND : (!ptLoadPairwiseDisjoint (l0 :: ls)) = true := by
                  rw [hDisj]; rfl
                rw [iteBoolTrue hND] at h; cases h
              | true =>
                have hND : (!ptLoadPairwiseDisjoint (l0 :: ls)) = false := by
                  rw [hDisj]; rfl
                rw [iteBoolFalse hND] at h
                cases hExecs :
                  listFilter (fun p => phdrHasExec p.pFlags) (l0 :: ls) with
                | nil => rw [hExecs] at h; cases h
                | cons e0 es =>
                  rw [hExecs] at h
                  dsimp only at h
                  cases hEnt : entryInExecLoad hdr.eEntry (e0 :: es) with
                  | false =>
                    have hNE : (!entryInExecLoad hdr.eEntry (e0 :: es)) =
                        true := by
                      rw [hEnt]; rfl
                    rw [iteBoolTrue hNE] at h; cases h
                  | true =>
                    have hNE : (!entryInExecLoad hdr.eEntry (e0 :: es)) =
                        false := by
                      rw [hEnt]; rfl
                    rw [iteBoolFalse hNE] at h
                    cases hPay : extractExecPayloads? bs (e0 :: es) with
                    | none => rw [hPay] at h; cases h
                    | some payloads =>
                      rw [hPay] at h
                      dsimp only at h
                      have heq := Option.some.inj h
                      subst heq
                      have hHdrS := parseElf64ImageHeader?_sound bs hdr hHdr
                      have hPhLen := parseElf64PhdrsAux_len hdr.ePhnum 0 phTable
                        phdrs hPh
                      have hPhMem := listAll_mem (phdrEntryValid bs) phdrs
                        hValid
                      have hPaySpec := extractExecPayloads?_mem bs (e0 :: es)
                        payloads hPay
                      dsimp only [entryInExecLoad] at hEnt
                      have hEntryAny := listAny_mem
                        (fun s => Nat.ble s.pVaddr hdr.eEntry &&
                                  Nat.blt hdr.eEntry (s.pVaddr + s.pFilesz))
                        (e0 :: es) hEnt
                      refine ⟨hHdrS.1, hHdrS.2.1, hHdrS.2.2.1, hHdrS.2.2.2.1,
                        hHdrS.2.2.2.2.1, hHdrS.2.2.2.2.2.1,
                        hHdrS.2.2.2.2.2.2.1, hHdrS.2.2.2.2.2.2.2.1,
                        hHdrS.2.2.2.2.2.2.2.2, hPhLen, ?_,
                        Nat.eq_of_beq_eq_true hGnuCnt, ?_, ?_, ?_, ?_, ?_,
                        ?_, hPaySpec.1, hPaySpec.2⟩
                      · intro ph hmem
                        have hv := hPhMem ph hmem
                        exact ⟨hv, phdrEntryValid_implies_safety bs ph hv⟩
                      · intro hc; cases hc
                      · intro s hs
                        have hLF := listFilter_mem
                          (fun p => Nat.beq p.pType ptLoad)
                          phdrs s (by rw [hLoads]; exact hs)
                        have hsPh := hPhMem s hLF.1
                        have hTy := Nat.eq_of_beq_eq_true hLF.2
                        dsimp only [phdrEntryValid] at hsPh
                        rw [iteBoolTrue hLF.2] at hsPh
                        exact ⟨hLF.1, hTy, hsPh⟩
                      · exact ptLoadPairwiseDisjoint_at_pairs (l0 :: ls) hDisj
                      · intro hc; cases hc
                      · intro s hs
                        have hEF := listFilter_mem
                          (fun p => phdrHasExec p.pFlags)
                          (l0 :: ls) s (by rw [hExecs]; exact hs)
                        have hLF := listFilter_mem
                          (fun p => Nat.beq p.pType ptLoad)
                          phdrs s (by rw [hLoads]; exact hEF.1)
                        have hsPh := hPhMem s hLF.1
                        dsimp only [phdrEntryValid] at hsPh
                        rw [iteBoolTrue hLF.2] at hsPh
                        dsimp only [ptLoadValid] at hsPh
                        have hFzPos := bandRight hsPh
                        rw [hEF.2] at hFzPos
                        change Nat.blt 0 s.pFilesz = true at hFzPos
                        refine ⟨hEF.1, hEF.2, Nat.le_of_ble_eq_true hFzPos⟩
                      · cases hEntryAny with
                        | intro s hsPair =>
                          exact ⟨s, hsPair.1,
                            Nat.le_of_ble_eq_true (bandLeft hsPair.2),
                            Nat.le_of_ble_eq_true (bandRight hsPair.2)⟩

private theorem decodeAllExecPayloads?_of_mem (cfg : DecodeConfig) :
    ∀ (ps : List (Elf64ProgramHdr × List UInt8))
      (trs : List (Elf64ProgramHdr × List (Nat × Nat × DecodedInsn))),
      decodeAllExecPayloads? cfg ps = some trs →
      ∀ pair, List.Mem pair ps →
        ∃ tr, List.Mem (pair.1, tr) trs ∧
          decodeStream cfg [] pair.2 = some tr
  | [], _, _, _, hmem => by cases hmem
  | (seg, bs) :: rest, trs, h, pair, hmem => by
    change
      (match decodeAllExecPayloads? cfg rest with
      | none => none
      | some rest0 =>
        match decodeStream cfg [] bs with
        | none => none
        | some tr => some ((seg, tr) :: rest0)) = some trs at h
    cases hRest : decodeAllExecPayloads? cfg rest with
    | none => rw [hRest] at h; cases h
    | some trRest =>
      rw [hRest] at h
      dsimp only at h
      cases hDec : decodeStream cfg [] bs with
      | none => rw [hDec] at h; cases h
      | some tr =>
        rw [hDec] at h
        dsimp only at h
        have heq := Option.some.inj h
        subst heq
        cases hmem with
        | head => exact ⟨tr, List.Mem.head _, hDec⟩
        | tail _ htl =>
          have hSub :=
            decodeAllExecPayloads?_of_mem cfg rest trRest hRest pair htl
          cases hSub with
          | intro tr0 htr0 => exact ⟨tr0, List.Mem.tail _ htr0.1, htr0.2⟩

/-- Soundness theorem for `checkElf64ImageZeroSyscallAndDoitm`: returns an
image only when `parseElf64ProgramHdrs?` succeeds (with `4 KiB` page-disjoint
`PT_LOAD`s and a single `{PF_R, PF_R | PF_W}` `PT_GNU_STACK`), every executable
`PT_LOAD` payload decodes via `decodeStream` with unconditional termination,
zero syscalls, `DOITM` constant-time opcodes, zero indirect control flow, zero
return-stack tampering (`insnTampersReturnStack = false`), every `.callRel`
fallthrough `nextRIP` and every direct branch target matching a decoded
intra-image instruction VA, and `e_entry` aligned to a decoded boundary. -/
theorem checkElf64ImageZeroSyscallAndDoitm_sound (cfg : DecodeConfig)
    (bs : List UInt8) (img : Elf64ProgramImage)
    (h : checkElf64ImageZeroSyscallAndDoitm cfg bs = some img) :
    Elf64ProgramImageValid bs img ∧
    ∃ traces,
      decodeAllExecPayloads? cfg img.execPayloads = some traces ∧
      natListContains (collectAllStartVas traces) img.header.eEntry = true ∧
      (∀ pair, List.Mem pair img.execPayloads →
        ∃ tr, List.Mem (pair.1, tr) traces ∧
          decodeStream cfg [] pair.2 = some tr) ∧
      (∀ p, List.Mem p traces →
        traceTerminatedOk p.2 = true ∧
        ∀ e, List.Mem e p.2 →
          insnIsSyscall e.2.2 = false ∧
          insnIsDoitmConstantTime e.2.2 = true ∧
          insnIsIndirectControl e.2.2 = false ∧
          insnTampersReturnStack e.2.2 = false ∧
          (insnIsDirectCall e.2.2 = true →
            natListContains (collectAllStartVas traces)
              (p.1.pVaddr + e.1 + e.2.1) = true) ∧
          (insnIsDirectBranch e.2.2 = true →
            ∃ tgt,
              directBranchTargetVa? p.1.pVaddr e.1 e.2.1 e.2.2 = some tgt ∧
              natListContains (collectAllStartVas traces) tgt = true)) := by
  unfold checkElf64ImageZeroSyscallAndDoitm at h
  cases hImg : parseElf64ProgramHdrs? bs with
  | none => rw [hImg] at h; cases h
  | some img0 =>
    rw [hImg] at h
    dsimp only at h
    cases hAllDec : decodeAllExecPayloads? cfg img0.execPayloads with
    | none => rw [hAllDec] at h; cases h
    | some traces =>
      rw [hAllDec] at h
      dsimp only at h
      cases hChk :
        (natListContains (collectAllStartVas traces) img0.header.eEntry &&
         listAll (fun p =>
           traceTerminatedOk p.2 &&
           listAll (entryZeroSyscallDoitmCfOk
             (collectAllStartVas traces) p.1.pVaddr) p.2) traces) with
      | false => rw [iteBoolFalse hChk] at h; cases h
      | true =>
        rw [iteBoolTrue hChk] at h
        have heq := Option.some.inj h
        subst heq
        have hEntry := bandLeft hChk
        have hTraces := listAll_mem _ traces (bandRight hChk)
        refine ⟨parseElf64ProgramHdrs?_sound bs img0 hImg,
          traces, hAllDec, hEntry,
          decodeAllExecPayloads?_of_mem cfg img0.execPayloads traces hAllDec,
          ?_⟩
        intro p hpMem
        have hPair := hTraces p hpMem
        refine ⟨bandLeft hPair, ?_⟩
        have hIns := listAll_mem _ p.2 (bandRight hPair)
        intro e heMem
        have hE := hIns e heMem
        dsimp only [entryZeroSyscallDoitmCfOk] at hE
        have h5 := bandLeft hE
        have h4 := bandLeft h5
        have h3 := bandLeft h4
        have h2 := bandLeft h3
        refine ⟨boolNotTrue (bandLeft h2), bandRight h2,
          boolNotTrue (bandRight h3), boolNotTrue (bandRight h4), ?_, ?_⟩
        · intro hCall
          have hCallClause := bandRight h5
          rw [hCall] at hCallClause
          simp only [Bool.not_true, Bool.false_or] at hCallClause
          exact hCallClause
        · intro hBr
          have hBrClause := bandRight hE
          rw [hBr] at hBrClause
          simp only [Bool.not_true, Bool.false_or] at hBrClause
          cases hTgt : directBranchTargetVa? p.1.pVaddr e.1 e.2.1 e.2.2 with
          | none => rw [hTgt] at hBrClause; exact Bool.noConfusion hBrClause
          | some tgt =>
            rw [hTgt] at hBrClause
            exact ⟨tgt, rfl, hBrClause⟩

/-- Concrete non-vacuous theorem: `.syscall`, `.sysenter`, `.intImm`, `.div`,
`.bsf`, `.tzcnt`, `.popcnt`, and `.lzcnt` are each rejected by
`insnIsDoitmConstantTime`. -/
theorem doitmConstantTime_rejects_syscalls_and_varlat :
    insnIsDoitmConstantTime .syscall = false ∧
    insnIsDoitmConstantTime .sysenter = false ∧
    insnIsDoitmConstantTime (.intImm 0x80) = false ∧
    insnIsDoitmConstantTime (.div false false .s64 (.reg .rcx)) = false ∧
    insnIsDoitmConstantTime (.div true false .s64 (.reg .rbx)) = false ∧
    insnIsDoitmConstantTime (.bsf .s64 .rax (.reg .rcx)) = false ∧
    insnIsDoitmConstantTime (.tzcnt .s64 .rax (.reg .rcx)) = false ∧
    insnIsDoitmConstantTime (.popcnt .s64 .rax (.reg .rcx)) = false ∧
    insnIsDoitmConstantTime (.lzcnt .s64 .rax (.reg .rcx)) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.ElfX86
end
