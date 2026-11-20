import Miri.Interpreter.SocketAddress
import Miri.Interpreter.Clock

/-! All socket.rs generic/IP/TCP option helpers. Host options are typed effects;
absence of a SockRef produces Unsupported, never an accepted option. -/
namespace Miri.Interpreter.SocketOptions
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive HostOption where | reuse | linger | keepalive | ttl | nodelay deriving DecidableEq, Repr
inductive Value where | boolean (value : Bool) | linger (value : Option Clock.Duration) | ttl (value : UInt32)
structure Hooks (S F E I : Type) where
  address : SocketAddress.Hooks S E I
  os : String
  i32Layout : M S LocalLayout
  u32Layout : M S LocalLayout
  readI32 : MPlaceTy Provenance → M S Int32
  readTimeval : MPlaceTy Provenance → M S (Option Clock.Duration)
  setTimeout : F → Bool → Option Clock.Duration → M S Unit
  getTimeout : F → Bool → M S (Option Clock.Duration)
  takeError : F → M S (Option (IoError.HostError E))
  setHost : F → HostOption → Value → M S (Option (Except (IoError.HostError E) Unit))
  getHost : F → HostOption → M S (Option (Except (IoError.HostError E) Value))
private def unsupported : M S A := throw (.unsupported "unsupported socket option or socket has no host SockRef")
private def setHost (h : Hooks S F E I) (socket : F) (option : HostOption) (value : Value) : M S (Files.Result E Unit) := do
  let some result ← h.setHost socket option value | unsupported
  return result.mapError .host
private def getHost (h : Hooks S F E I) (socket : F) (option : HostOption) : M S (Files.Result E Value) := do
  let some result ← h.getHost socket option | unsupported
  return result.mapError .host
private def intPlace (h : Hooks S F E I) (pointer : Pointer (Option Provenance)) : M S (MPlaceTy Provenance) := do
  return h.address.ptrToPlace pointer (← h.i32Layout)
private def boolAt (h : Hooks S F E I) (pointer : Pointer (Option Provenance)) : M S Bool := do
  return (← h.readI32 (← intPlace h pointer)) != 0
private def outputInt (h : Hooks S F E I) (value : Int) (unsigned : Bool := false) : M S (Files.Result E (MPlaceTy Provenance)) := do
  let place ← h.address.allocate (← if unsigned then h.u32Layout else h.i32Layout) .stack
  h.address.writeInt value place
  return .ok place
private def lingerName (os : String) : String := if os == "macos" then "SO_LINGER_SEC" else "SO_LINGER"

def setGeneric (h : Hooks S F E I) (socket : F) (option : Int32) (pointer : Pointer (Option Provenance)) (length : UInt64) : M S (Files.Result E Unit) := do
  let receive ← h.address.libcI32 "SO_RCVTIMEO"
  let send ← h.address.libcI32 "SO_SNDTIMEO"
  let reuse ← h.address.libcI32 "SO_REUSEADDR"
  let linger ← h.address.libcI32 (lingerName h.os)
  let keepalive ← h.address.libcI32 "SO_KEEPALIVE"
  if #["macos","freebsd","netbsd"].contains h.os then
    if option == (← h.address.libcI32 "SO_NOSIGPIPE") then
      if length != 4 then return .error (.libc "EINVAL")
      let _ ← h.readI32 (← intPlace h pointer)
      return .ok ()
  if option == receive || option == send then
    let place := h.address.ptrToPlace pointer (← h.address.layout "timeval")
    let some timeout ← h.readTimeval place | return .error (.libc "EINVAL")
    h.setTimeout socket (option == send) (if timeout.asNanos == 0 then none else some timeout)
    return .ok ()
  if option == reuse then
    if length != 4 then return .error (.libc "EINVAL")
    return ← setHost h socket .reuse (.boolean (← boolAt h pointer))
  else if option == linger then
    let layout ← h.address.layout "linger"
    if length != layout.layout.size.bytes then return .error (.libc "EINVAL")
    let place := h.address.ptrToPlace pointer layout
    let enabled ← h.readI32 (← h.address.field place "l_onoff")
    let seconds ← h.readI32 (← h.address.field place "l_linger")
    -- Rust then_some eagerly converts the duration even with enabled=false.
    if seconds < 0 then throw (.invalidProgram "linger duration cannot convert u64")
    let duration : Clock.Duration := ⟨seconds.toUInt32.toUInt64,0,by decide⟩
    return ← setHost h socket .linger (.linger (if enabled != 0 then some duration else none))
  else if option == keepalive then
    if length != 4 then return .error (.libc "EINVAL")
    return ← setHost h socket .keepalive (.boolean (← boolAt h pointer))
  unsupported

def setIp (h : Hooks S F E I) (socket : F) (option : Int32) (pointer : Pointer (Option Provenance)) (length : UInt64) : M S (Files.Result E Unit) := do
  if option != (← h.address.libcI32 "IP_TTL") then unsupported
  else
    if length != 4 then return .error (.libc "EINVAL")
    let place := h.address.ptrToPlace pointer (← h.u32Layout)
    setHost h socket .ttl (.ttl (← h.address.readU32 place))
def setTcp (h : Hooks S F E I) (socket : F) (option : Int32) (pointer : Pointer (Option Provenance)) (length : UInt64) : M S (Files.Result E Unit) := do
  if option != (← h.address.libcI32 "TCP_NODELAY") then unsupported
  else
    if length != 4 then return .error (.libc "EINVAL")
    setHost h socket .nodelay (.boolean (← boolAt h pointer))

def getGeneric (h : Hooks S F E I) (socket : F) (option : Int32) : M S (Files.Result E (MPlaceTy Provenance)) := do
  let error ← h.address.libcI32 "SO_ERROR"
  let receive ← h.address.libcI32 "SO_RCVTIMEO"
  let send ← h.address.libcI32 "SO_SNDTIMEO"
  let reuse ← h.address.libcI32 "SO_REUSEADDR"
  let linger ← h.address.libcI32 (lingerName h.os)
  let keepalive ← h.address.libcI32 "SO_KEEPALIVE"
  if option == error then
    let value ← match ← h.takeError socket with
      | none => pure (0 : Int32)
      | some error => h.address.errors.scalarI32 (← IoError.toErrnum h.address.errors (.host error))
    return ← outputInt h value.toInt
  else if option == receive || option == send then
    let timeout ← h.getTimeout socket (option == send)
    let place ← h.address.allocate (← h.address.layout "timeval") .stack
    h.address.writeInt (timeout.map (·.seconds.toNat) |>.getD 0) (← h.address.field place "tv_sec")
    h.address.writeInt (Int.ofNat (timeout.map (fun d => d.nanos.toNat / 1000) |>.getD 0)) (← h.address.field place "tv_usec")
    return .ok place
  let selected ← if option == reuse then pure HostOption.reuse else if option == linger then pure .linger
    else if option == keepalive then pure .keepalive else unsupported
  let result ← getHost h socket selected
  match result with
  | .error error => return .error error
  | .ok (.boolean value) =>
    if selected == .linger then throw (.invalidProgram "host linger getter returned bool")
    outputInt h (if value then 1 else 0)
  | .ok (.linger value) =>
    if selected != .linger then throw (.invalidProgram "host boolean getter returned linger")
    let place ← h.address.allocate (← h.address.layout "linger") .stack
    h.address.writeInt (if value.isSome then 1 else 0) (← h.address.field place "l_onoff")
    let field ← h.address.field place "l_linger"
    let seconds := value.map (·.seconds) |>.getD 0
    if seconds > 2147483647 then throw (.invalidProgram "host linger seconds exceeds i32")
    h.address.writeInt seconds.toNat field
    return .ok place
  | .ok _ => throw (.invalidProgram "host generic socket getter returned TTL")
private def getSimple (h : Hooks S F E I) (socket : F) (option : HostOption) : M S (Files.Result E (MPlaceTy Provenance)) := do
  match ← getHost h socket option with
  | .error error => return .error error
  | .ok (.ttl value) =>
    if option != .ttl then throw (.invalidProgram "host socket getter type mismatch")
    outputInt h value.toNat true
  | .ok (.boolean value) =>
    if option != .nodelay then throw (.invalidProgram "host socket getter type mismatch")
    outputInt h (if value then 1 else 0)
  | .ok _ => throw (.invalidProgram "host socket getter type mismatch")
def getIp (h : Hooks S F E I) (socket : F) (option : Int32) : M S (Files.Result E (MPlaceTy Provenance)) := do
  if option != (← h.address.libcI32 "IP_TTL") then unsupported else getSimple h socket .ttl
def getTcp (h : Hooks S F E I) (socket : F) (option : Int32) : M S (Files.Result E (MPlaceTy Provenance)) := do
  if option != (← h.address.libcI32 "TCP_NODELAY") then unsupported else getSimple h socket .nodelay
end Miri.Interpreter.SocketOptions
