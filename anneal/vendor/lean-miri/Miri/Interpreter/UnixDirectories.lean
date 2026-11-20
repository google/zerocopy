import Miri.Interpreter.UnixFsPaths

/-! DirTable/DirStream and opendir/readdir/dirfd/closedir from pinned unix/fs.rs.
Opaque DIR IDs are target usize scalars, not allocated or dereferenceable pointers. -/
namespace Miri.Interpreter.UnixDirectories
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure Stream (ReadDir : Type) where
  host : ReadDir
  fd : Int32
  identity : Files.FdId
  specials : Array String := #["..","."]
  entry : Option (Pointer (Option Provenance) × String) := none
structure Table (ReadDir : Type) where
  nextId : UInt64 := 1
  streams : Array (UInt64 × Stream ReadDir) := #[]
structure Hooks (S F D Path HM Time E Kind ReadDir Entry : Type) where
  paths : UnixFsPaths.Hooks S F D Path HM Time E Kind
  get : M S (Table ReadDir)
  put : Table ReadDir → M S Unit
  readDir : Path → M S (Except (IoError.HostError E) ReadDir)
  openDirectory : Path → M S (Except (IoError.HostError E) D)
  dropReadDir : ReadDir → M S Unit
  /-- Owns/transfers the actual directory handle into FileOwnership + FD table. -/
  insertDirectory : D → M S (Int32 × Files.FdId)
  id : F → Files.FdId
  nextEntry : ReadDir → M S (Option (Except (IoError.HostError E) Entry))
  entryName : Entry → Path
  entryType : Entry → M S (Except (IoError.HostError E) UnixFsMetadata.FileType)
  entryInode : Entry → UInt64
  readUsize : OpTy Provenance → M S UInt64
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
  /-- Compiler dirent layout, last-field offset and ABI alignment; no inferred shape. -/
  direntLayout : String → M S LocalLayout
  allocateRuntime : Size → Align → M S (Pointer (Option Provenance))
  asPlace : Pointer (Option Provenance) → LocalLayout → MPlaceTy Provenance
  wrappingOffset : Pointer (Option Provenance) → Size → M S (Pointer (Option Provenance))
  optionalField : MPlaceTy Provenance → String → M S (Option (MPlaceTy Provenance))
  writeNull : MPlaceTy Provenance → M S Unit
  deallocateRuntime : Pointer (Option Provenance) → M S Unit
  closeFd : Int32 → M S Int32
  libcU8 : String → M S UInt8
private def stream (table : Table R) (id : UInt64) : Except StepError (Stream R) := do
  let some (_,value) := table.streams.find? (·.1 == id)
    | throw (.undefinedBehavior "DIR pointer did not come from opendir")
  return value
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def putStream (h : Hooks S F D P HM T E K R Ent) (id : UInt64) (value : Stream R) : M S Unit := do
  let state ← h.get
  let _ ← lift (stream state id)
  h.put { state with streams := state.streams.map fun (old,entry) => (old,if old == id then value else entry) }
private def backing (h : Hooks S F D P HM T E K R Ent) (value : Stream R) : M S Unit := do
  let some fd ← h.paths.metadata.lookupFd value.fd
    | throw (.undefinedBehavior "backing FD for DIR stream tampered with")
  Files.withDrop (do
    if h.id fd != value.identity then throw (.undefinedBehavior "backing FD for DIR stream tampered with")
  ) (h.paths.metadata.dropFd fd)

private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state =>
    match cleanup state with | .ok _ state => .error error state | .error next state => .error next state

def openDir (h : Hooks S F D P HM T E K R Ent) (name : OpTy Provenance) : M S UInt64 := do
  let name ← h.paths.metadata.readPath (← h.paths.metadata.readPointer name)
  if ← h.paths.metadata.isolationReject "`opendir`" then
    IoError.setLastError h.paths.metadata.errors (.libc "EACCES")
    return 0
  match ← h.readDir name with
  | .error error => IoError.setLastError h.paths.metadata.errors (.host error); return 0
  | .ok readDir =>
    -- Host ReadDir is dropped on all failing setup branches; successful transfer owns it.
    onError (do
      let .ok directory ← h.openDirectory name
        | throw (.unsupported "cannot opendir: failed to create directory handle")
      let (number,identity) ← h.insertDirectory directory
      let table ← h.get
      if table.nextId == 18446744073709551615 then throw (.invalidProgram "DIR id increment overflow")
      if table.streams.any (·.1 == table.nextId) then throw (.invalidProgram "DIR stream id collision")
      h.put { table with nextId := table.nextId + 1, streams := table.streams.push (table.nextId,⟨readDir,number,identity,#["..","."],none⟩) }
      return table.nextId
    ) (h.dropReadDir readDir)

private def typeName (unix : Bool) : UnixFsMetadata.FileType → String
  | .directory => "DT_DIR" | .regular => "DT_REG" | .symlink => "DT_LNK"
  | .block => if unix then "DT_BLK" else "DT_UNKNOWN"
  | .character => if unix then "DT_CHR" else "DT_UNKNOWN"
  | .fifo => if unix then "DT_FIFO" else "DT_UNKNOWN"
  | .socket => if unix then "DT_SOCK" else "DT_UNKNOWN"
  | .other => "DT_UNKNOWN"
private def entryFields (h : Hooks S F D P HM T E K R Ent) (entry : Sum Ent String) : M S (ByteArray × UInt64 × Int) := do
  match entry with
  | .inr special => return (special.toUTF8,0,(← h.libcU8 "DT_DIR").toNat)
  | .inl entry =>
    let name := h.paths.strings.encodedBytes (h.entryName entry)
    let result ← h.entryType entry
    let kind := match result with
      | .ok kind => typeName h.paths.metadata.hostUnix kind
      | .error _ => "DT_UNKNOWN"
    let dtype ← h.libcU8 kind
    return (name,if h.paths.metadata.hostUnix then h.entryInode entry else 0,dtype.toNat)

private def nextHost (h : Hooks S F D P HM T E K R Ent) (id : UInt64) :
    M S (Option (Except (IoError.HostError E) (Sum Ent String))) := do
  let value ← lift (stream (← h.get) id)
  if let some special := value.specials.back? then
    putStream h id { value with specials := value.specials.pop }
    return some (.ok (.inr special))
  return (← h.nextEntry value.host).map (fun result => result.map .inl)

private def allocateEntry (h : Hooks S F D P HM T E K R Ent) (kind : String)
    (entry : Sum Ent String) : M S (Pointer (Option Provenance)) := do
  let (name,inode,dtype) ← entryFields h entry
  let layout ← h.direntLayout kind
  let fields := layout.layout.fields
  if fields.count == 0 then throw (.invalidProgram "dirent last field strict_sub underflow")
  let offset ← match fields.offset (fields.count-1) with
    | .ok size => pure size.bytes
    | .error error => throw (.invalidProgram s!"dirent field offset: {reprStr error}")
  let name := name.push 0
  if name.size >= 2^64 || offset.toNat + name.size >= 2^64 then
    throw (.invalidProgram "dirent name size strict_add overflow")
  let size := UInt64.ofNat (offset.toNat + name.size)
  let pointer ← h.allocateRuntime (Size.ofBytes size) layout.layout.align.abi
  let place := h.asPlace pointer layout
  h.paths.writeBytes (← h.wrappingOffset pointer (Size.ofBytes offset)) name
  h.paths.metadata.writeFields #[(if h.paths.metadata.os == "freebsd" then "d_fileno" else "d_ino",inode.toNat),
    ("d_reclen",size.toNat)] place
  if let some field ← h.optionalField place "d_off" then h.writeNull field
  if let some field ← h.optionalField place "d_seekoff" then h.writeNull field
  if let some field ← h.optionalField place "d_namlen" then h.paths.metadata.writeInt (name.size-1) field
  if let some field ← h.optionalField place "d_type" then h.paths.metadata.writeInt dtype field
  return pointer

def readDir (h : Hooks S F D P HM T E K R Ent) (dir : OpTy Provenance)
    (dest : MPlaceTy Provenance) (kind : String) : M S Unit := do
  if !(#["linux","android","solaris","illumos","freebsd","macos"].contains h.paths.metadata.os) then
    throw (.unsupported "readdir unsupported on target OS")
  let id ← h.readUsize dir
  if ← h.paths.metadata.isolationReject "`readdir`" then
    IoError.setLastError h.paths.metadata.errors (.libc "EBADF")
    h.writeNull dest
    return
  backing h (← lift (stream (← h.get) id))
  let entry ← match ← nextHost h id with
    | none => pure none
    | some (.error error) => IoError.setLastError h.paths.metadata.errors (.host error) *> pure none
    | some (.ok entry) => (allocateEntry h kind entry).map some
  let old ← lift (stream (← h.get) id)
  putStream h id { old with entry := entry.map (fun pointer => (pointer,kind)) }
  if let some (pointer,oldKind) := old.entry then
    if oldKind != kind then throw (.undefinedBehavior "mixing different readdir variants on same DIR")
    h.deallocateRuntime pointer
  h.writePointer (entry.getD Pointer.null) dest

def dirFd (h : Hooks S F D P HM T E K R Ent) (dir : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let id ← h.readUsize dir
  let value ← lift (stream (← h.get) id)
  backing h value
  h.paths.metadata.writeInt value.fd.toInt dest

def closeDir (h : Hooks S F D P HM T E K R Ent) (dir : OpTy Provenance) : M S Int32 := do
  let id ← h.readUsize dir
  if ← h.paths.metadata.isolationReject "`closedir`" then
    return ← IoError.setErrnoAndReturnNeg1I32 h.paths.metadata.errors (.libc "EBADF")
  let table ← h.get
  let value ← lift (stream table id)
  h.put { table with streams := table.streams.filter (·.1 != id) }
  Files.withDrop (do
    backing h value
    let _ ← h.closeFd value.fd
    if let some (pointer,_) := value.entry then h.deallocateRuntime pointer
    return 0
  ) (h.dropReadDir value.host)
end Miri.Interpreter.UnixDirectories
