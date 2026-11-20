import Miri.Interpreter.ForeignItems
import Miri.Memory.Scalar

/-! Source-extracted ordered error tables and policy from pinned shims/io_error.rs.
Host/target errno numbers remain compiler/host queries, never platform guesses. -/
namespace Miri.Interpreter.IoError
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive ErrorKind where
  | ArgumentListTooLong | AddrInUse | AddrNotAvailable | ResourceBusy | ConnectionAborted | ConnectionRefused | ConnectionReset | Deadlock | QuotaExceeded | AlreadyExists | FileTooLarge | HostUnreachable | Interrupted | InvalidInput | IsADirectory | FilesystemLoop | NotFound | OutOfMemory | StorageFull | TooManyLinks | InvalidFilename | NetworkDown | NetworkUnreachable | NotConnected | NotADirectory | DirectoryNotEmpty | BrokenPipe | ReadOnlyFilesystem | NotSeekable | StaleNetworkFileHandle | TimedOut | ExecutableFileBusy | CrossesDevices | InProgress | InputOutputError | PermissionDenied | WouldBlock | Unsupported | TooManyOpenFiles | Other
  deriving DecidableEq, Repr
structure HostError (Host : Type) where
  kind : ErrorKind
  raw : Option Int32
  payload : Host
inductive Error (Host : Type) where
  | libc (name : String)
  | windows (name : String)
  | host (error : HostError Host)
  | raw (value : Scalar Provenance)
def unixTable : Array (String × ErrorKind) := #[
  ("E2BIG",.ArgumentListTooLong),
  ("EADDRINUSE",.AddrInUse),
  ("EADDRNOTAVAIL",.AddrNotAvailable),
  ("EBUSY",.ResourceBusy),
  ("ECONNABORTED",.ConnectionAborted),
  ("ECONNREFUSED",.ConnectionRefused),
  ("ECONNRESET",.ConnectionReset),
  ("EDEADLK",.Deadlock),
  ("EDQUOT",.QuotaExceeded),
  ("EEXIST",.AlreadyExists),
  ("EFBIG",.FileTooLarge),
  ("EHOSTUNREACH",.HostUnreachable),
  ("EINTR",.Interrupted),
  ("EINVAL",.InvalidInput),
  ("EISDIR",.IsADirectory),
  ("ELOOP",.FilesystemLoop),
  ("ENOENT",.NotFound),
  ("ENOMEM",.OutOfMemory),
  ("ENOSPC",.StorageFull),
  ("EMLINK",.TooManyLinks),
  ("ENAMETOOLONG",.InvalidFilename),
  ("ENETDOWN",.NetworkDown),
  ("ENETUNREACH",.NetworkUnreachable),
  ("ENOTCONN",.NotConnected),
  ("ENOTDIR",.NotADirectory),
  ("ENOTEMPTY",.DirectoryNotEmpty),
  ("EPIPE",.BrokenPipe),
  ("EROFS",.ReadOnlyFilesystem),
  ("ESPIPE",.NotSeekable),
  ("ESTALE",.StaleNetworkFileHandle),
  ("ETIMEDOUT",.TimedOut),
  ("ETXTBSY",.ExecutableFileBusy),
  ("EXDEV",.CrossesDevices),
  ("EINPROGRESS",.InProgress),
  ("EIO",.InputOutputError),
  ("EPERM",.PermissionDenied),
  ("EACCES",.PermissionDenied),
  ("EWOULDBLOCK",.WouldBlock),
  ("EAGAIN",.WouldBlock),
  ("ENOSYS",.Unsupported),
  ("EOPNOTSUPP",.Unsupported),
  ("ENOTSUP",.Unsupported),
  ("EMFILE",.TooManyOpenFiles),
  ("ENFILE",.TooManyOpenFiles)]
def windowsTable : Array (String × ErrorKind) := #[
  ("WSAEADDRINUSE",.AddrInUse),
  ("WSAEADDRNOTAVAIL",.AddrNotAvailable),
  ("ERROR_FILE_EXISTS",.AlreadyExists),
  ("ERROR_ALREADY_EXISTS",.AlreadyExists),
  ("ERROR_NO_DATA",.BrokenPipe),
  ("WSAECONNABORTED",.ConnectionAborted),
  ("WSAECONNREFUSED",.ConnectionRefused),
  ("WSAECONNRESET",.ConnectionReset),
  ("ERROR_NOT_SAME_DEVICE",.CrossesDevices),
  ("ERROR_POSSIBLE_DEADLOCK",.Deadlock),
  ("ERROR_DIR_NOT_EMPTY",.DirectoryNotEmpty),
  ("ERROR_CANT_RESOLVE_FILENAME",.FilesystemLoop),
  ("ERROR_DISK_QUOTA_EXCEEDED",.QuotaExceeded),
  ("WSAEDQUOT",.QuotaExceeded),
  ("ERROR_FILE_TOO_LARGE",.FileTooLarge),
  ("ERROR_HOST_UNREACHABLE",.HostUnreachable),
  ("WSAEHOSTUNREACH",.HostUnreachable),
  ("ERROR_INVALID_NAME",.InvalidFilename),
  ("ERROR_BAD_PATHNAME",.InvalidFilename),
  ("ERROR_FILENAME_EXCED_RANGE",.InvalidFilename),
  ("ERROR_INVALID_PARAMETER",.InvalidInput),
  ("WSAEINVAL",.InvalidInput),
  ("ERROR_DIRECTORY_NOT_SUPPORTED",.IsADirectory),
  ("WSAENETDOWN",.NetworkDown),
  ("ERROR_NETWORK_UNREACHABLE",.NetworkUnreachable),
  ("WSAENETUNREACH",.NetworkUnreachable),
  ("ERROR_DIRECTORY",.NotADirectory),
  ("WSAENOTCONN",.NotConnected),
  ("ERROR_FILE_NOT_FOUND",.NotFound),
  ("ERROR_PATH_NOT_FOUND",.NotFound),
  ("ERROR_INVALID_DRIVE",.NotFound),
  ("ERROR_BAD_NETPATH",.NotFound),
  ("ERROR_BAD_NET_NAME",.NotFound),
  ("ERROR_SEEK_ON_DEVICE",.NotSeekable),
  ("ERROR_NOT_ENOUGH_MEMORY",.OutOfMemory),
  ("ERROR_OUTOFMEMORY",.OutOfMemory),
  ("ERROR_ACCESS_DENIED",.PermissionDenied),
  ("WSAEACCES",.PermissionDenied),
  ("ERROR_WRITE_PROTECT",.ReadOnlyFilesystem),
  ("ERROR_BUSY",.ResourceBusy),
  ("ERROR_DISK_FULL",.StorageFull),
  ("ERROR_HANDLE_DISK_FULL",.StorageFull),
  ("WAIT_TIMEOUT",.TimedOut),
  ("WSAETIMEDOUT",.TimedOut),
  ("ERROR_DRIVER_CANCEL_TIMEOUT",.TimedOut),
  ("ERROR_OPERATION_ABORTED",.TimedOut),
  ("ERROR_SERVICE_REQUEST_TIMEOUT",.TimedOut),
  ("ERROR_COUNTER_TIMEOUT",.TimedOut),
  ("ERROR_TIMEOUT",.TimedOut),
  ("ERROR_RESOURCE_CALL_TIMED_OUT",.TimedOut),
  ("ERROR_CTX_MODEM_RESPONSE_TIMEOUT",.TimedOut),
  ("ERROR_CTX_CLIENT_QUERY_TIMEOUT",.TimedOut),
  ("FRS_ERR_SYSVOL_POPULATE_TIMEOUT",.TimedOut),
  ("ERROR_DS_TIMELIMIT_EXCEEDED",.TimedOut),
  ("DNS_ERROR_RECORD_TIMED_OUT",.TimedOut),
  ("ERROR_IPSEC_IKE_TIMED_OUT",.TimedOut),
  ("ERROR_RUNLEVEL_SWITCH_TIMEOUT",.TimedOut),
  ("ERROR_RUNLEVEL_SWITCH_AGENT_TIMEOUT",.TimedOut),
  ("ERROR_TOO_MANY_LINKS",.TooManyLinks),
  ("ERROR_CALL_NOT_IMPLEMENTED",.Unsupported),
  ("WSAEWOULDBLOCK",.WouldBlock),
  ("ERROR_TOO_MANY_OPEN_FILES",.TooManyOpenFiles),
  ("ERROR_IO_DEVICE",.InputOutputError)]
def unixErrnoNames : Array String := #["E2BIG","EACCES","EADDRINUSE","EADDRNOTAVAIL","EAFNOSUPPORT","EAGAIN","EALREADY","EBADF","EBADMSG","EBUSY","ECANCELED","ECHILD","ECONNABORTED","ECONNREFUSED","ECONNRESET","EDEADLK","EDESTADDRREQ","EDOM","EDQUOT","EEXIST","EFAULT","EFBIG","EHOSTUNREACH","EIDRM","EILSEQ","EINPROGRESS","EINTR","EINVAL","EIO","EISCONN","EISDIR","ELOOP","EMFILE","EMLINK","EMSGSIZE","EMULTIHOP","ENAMETOOLONG","ENETDOWN","ENETRESET","ENETUNREACH","ENFILE","ENOBUFS","ENODEV","ENOENT","ENOEXEC","ENOLCK","ENOLINK","ENOMEM","ENOMSG","ENOPROTOOPT","ENOSPC","ENOSYS","ENOTCONN","ENOTDIR","ENOTEMPTY","ENOTRECOVERABLE","ENOTSOCK","ENOTSUP","ENOTTY","ENXIO","EOPNOTSUPP","EOVERFLOW","EOWNERDEAD","EPERM","EPIPE","EPROTO","EPROTONOSUPPORT","EPROTOTYPE","ERANGE","EROFS","ESOCKTNOSUPPORT","ESPIPE","ESRCH","ESTALE","ETIMEDOUT","ETXTBSY","EWOULDBLOCK","EXDEV"]
structure Hooks (S Host : Type) where
  family : ForeignItems.Family
  os : String
  hostUnix : Bool
  hostErrno : String → M S Int32
  libc : String → M S (Scalar Provenance)
  windows : String → M S (Scalar Provenance)
  scalarI32 : Scalar Provenance → M S Int32
  scalarU32 : Scalar Provenance → M S UInt32
  hostFromRaw : Int32 → M S (HostError Host)
  hostFromKind : ErrorKind → M S (HostError Host)
  getLastErrorPlace : M S (Option (MPlaceTy Provenance))
  setLastErrorPlace : MPlaceTy Provenance → M S Unit
  allocateU32Machine : M S (MPlaceTy Provenance)
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  readScalar : MPlaceTy Provenance → M S (Scalar Provenance)
  writeInt : Int → MPlaceTy Provenance → M S Unit

def hostErrorToErrnum (h : Hooks S H) (error : HostError H) : M S (Scalar Provenance) := do
  if h.family == .unix then
    if h.hostUnix then
      if let some raw := error.raw then
        for name in unixErrnoNames do
          if raw == (← h.hostErrno name) then return ← h.libc name
    for (name,kind) in unixTable do
      if error.kind == kind then return ← h.libc name
    throw (.unsupported "unsupported host io error")
  if h.family == .windows then
    for (name,kind) in windowsTable do
      if error.kind == kind then return ← h.windows name
    throw (.unsupported "unsupported host io error")
  throw (.unsupported s!"io::Error to errnum unsupported for OS {h.os}")

def toErrnum (h : Hooks S H) : Error H → M S (Scalar Provenance)
  | .host error => hostErrorToErrnum h error
  | .libc name => h.libc name
  | .windows name => h.windows name
  | .raw value => pure value

def lastErrorPlace (h : Hooks S H) : M S (MPlaceTy Provenance) := do
  if let some place ← h.getLastErrorPlace then return place
  let place ← h.allocateU32Machine
  let zero ← match Scalar.fromInt 0 (Size.ofBytes 4) with
    | .ok value => pure value
    | .error _ => throw (.invalidProgram "u32 zero scalar construction failed")
  h.writeScalar zero place
  h.setLastErrorPlace place
  return place

def setLastError (h : Hooks S H) (error : Error H) : M S Unit := do
  let value ← toErrnum h error
  h.writeScalar value (← lastErrorPlace h)

def setErrnoAndReturnNeg1 (h : Hooks S H) (error : Error H) (dest : MPlaceTy Provenance) : M S Unit := do
  setLastError h error
  h.writeInt (-1) dest

def setErrnoAndReturnNeg1I32 (h : Hooks S H) (error : Error H) : M S Int32 := do
  setLastError h error
  return -1

def setErrnoAndReturnNeg1I64 (h : Hooks S H) (error : Error H) : M S Int64 := do
  setLastError h error
  return -1

def getLastError (h : Hooks S H) : M S (Scalar Provenance) := do h.readScalar (← lastErrorPlace h)

def tryErrnumToHost (h : Hooks S H) (value : Scalar Provenance) : M S (Option (HostError H)) := do
  if h.family == .unix then
    let value ← h.scalarI32 value
    if h.hostUnix then
      for name in unixErrnoNames do
        if value == (← h.scalarI32 (← h.libc name)) then
          return some (← h.hostFromRaw (← h.hostErrno name))
    for (name,kind) in unixTable do
      if value == (← h.scalarI32 (← h.libc name)) then return some (← h.hostFromKind kind)
    return none
  if h.family == .windows then
    let value ← h.scalarU32 value
    for (name,kind) in windowsTable do
      if value == (← h.scalarU32 (← h.windows name)) then return some (← h.hostFromKind kind)
    return none
  throw (.unsupported s!"errnum to io::Error unsupported for OS {h.os}")

def intoNtstatus : Error H → Int32
  | .host error => Int32.ofInt (Int.ofNat (match error.kind with
      | .ReadOnlyFilesystem => 0xC00000A2
      | .InvalidInput => 0xC0000098
      | .QuotaExceeded => 0xC000007F
      | .PermissionDenied => 0xC0000022
      | _ => 0xC0000185))
  | _ => Int32.ofInt 0xC0000185

def tryUnwrap (h : Hooks S H) (result : Except (HostError H) A) (negativeOne : A) : M S A := do
  match result with
  | .ok value => return value
  | .error error => setLastError h (.host error); return negativeOne
end Miri.Interpreter.IoError
