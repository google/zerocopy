import Miri.Interpreter.Files

/-! Pinned unix/socket_address.rs. Network bytes are independent of target
endianness; native flowinfo/scope fields use typed scalar operations. -/
namespace Miri.Interpreter.SocketAddress
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Address where
  | v4 (bits : UInt32) (port : UInt16)
  | v6 (bits : BitVec 128) (port : UInt16) (flow scope : UInt32)
  deriving DecidableEq, Repr
inductive Kind where | stack | socketAddress | machine deriving DecidableEq, Repr
structure Hooks (S E Iterator : Type) where
  errors : IoError.Hooks S E
  gnu : Bool
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  isLiteralNull : Pointer (Option Provenance) → Bool
  readCString : Pointer (Option Provenance) → M S ByteArray
  readScalar : MPlaceTy Provenance → M S (Scalar Provenance)
  readSigned : MPlaceTy Provenance → Size → M S Int
  readU32 : MPlaceTy Provenance → M S UInt32
  readSocklen : OpTy Provenance → M S UInt64
  layout : String → M S LocalLayout
  u128Layout : M S LocalLayout
  pointerLayout : M S LocalLayout
  derefAs : OpTy Provenance → LocalLayout → M S (MPlaceTy Provenance)
  ptrToPlace : Pointer (Option Provenance) → LocalLayout → MPlaceTy Provenance
  transmute : MPlaceTy Provenance → LocalLayout → M S (MPlaceTy Provenance)
  offsetZero : MPlaceTy Provenance → LocalLayout → M S (MPlaceTy Provenance)
  field : MPlaceTy Provenance → String → M S (MPlaceTy Provenance)
  readBytes : Pointer (Option Provenance) → Size → M S ByteArray
  writeBytes : Pointer (Option Provenance) → ByteArray → M S Unit
  writeZeros : Pointer (Option Provenance) → Size → M S Unit
  pointer : MPlaceTy Provenance → Pointer (Option Provenance)
  allocate : LocalLayout → Kind → M S (MPlaceTy Provenance)
  deallocate : Pointer (Option Provenance) → Kind → M S Unit
  memCopy : Pointer (Option Provenance) → Pointer (Option Provenance) → Size → Bool → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
  readPlacePointer : MPlaceTy Provenance → M S (Pointer (Option Provenance))
  libc : String → M S (Scalar Provenance)
  libcI32 : String → M S Int32
  scalarSigned : Scalar Provenance → Size → M S Int
  /-- Actual host ToSocketAddrs iterator, including each next operation. -/
  resolve : String → UInt16 → M S (Except (IoError.HostError E) Iterator)
  nextAddress : Iterator → M S (Option (Address × Iterator))
  dropIterator : Iterator → M S Unit
  resolutionDiagnostic : IoError.HostError E → M S Unit
  listBudget : Nat
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def bytes (h : Hooks S E I) (place : MPlaceTy Provenance) (size : Nat) : M S Nat := do
  let data ← h.readBytes (h.pointer place) (Size.ofBytes (UInt64.ofNat size))
  if data.size != size then throw (.invalidProgram "socket address byte reader length mismatch")
  return data.data.foldl (fun total byte => total*256+byte.toNat) 0
private def networkBytes (value count : Nat) : ByteArray :=
  ⟨(List.range count).toArray.map fun i => UInt8.ofNat (value / 256^(count-1-i) % 256)⟩

def read (h : Hooks S E I) (address length : OpTy Provenance) (name : String) : M S (Except (IoError.Error E) Address) := do
  let length ← h.readSocklen length
  let generic ← h.layout "sockaddr"
  if length < generic.layout.size.bytes then return .error (.libc "EINVAL")
  let address ← h.derefAs address generic
  let familyField ← h.field address "sa_family"
  let familyLayout ← h.layout "sa_family_t"
  let family ← h.readSigned familyField familyLayout.layout.size
  if family == (← h.libcI32 "AF_INET").toInt then
    let layout ← h.layout "sockaddr_in"
    if length != layout.layout.size.bytes then return .error (.libc "EINVAL")
    let address ← h.transmute address layout
    let port ← bytes h (← h.field address "sin_port") 2
    let bits ← bytes h (← h.field (← h.field address "sin_addr") "s_addr") 4
    return .ok (.v4 (UInt32.ofNat bits) (UInt16.ofNat port))
  else if family == (← h.libcI32 "AF_INET6").toInt then
    let layout ← h.layout "sockaddr_in6"
    if length != layout.layout.size.bytes then return .error (.libc "EINVAL")
    let address ← h.offsetZero address layout
    let port ← bytes h (← h.field address "sin6_port") 2
    let field ← h.transmute (← h.field (← h.field address "sin6_addr") "s6_addr") (← h.u128Layout)
    let bits ← bytes h field 16
    let flow ← h.readU32 (← h.field address "sin6_flowinfo")
    let scope ← h.readU32 (← h.field address "sin6_scope_id")
    return .ok (.v6 (BitVec.ofNat 128 bits) (UInt16.ofNat port) flow scope)
  else throw (.unsupported s!"{name}: address family unsupported; only AF_INET/AF_INET6")

private def family (h : Hooks S E I) (place : MPlaceTy Provenance) (name : String) : M S Unit := do
  let scalar ← h.libc name
  let signed ← h.scalarSigned scalar scalar.size
  match Scalar.fromInt signed place.layout.layout.size with
  | .ok scalar => h.writeScalar scalar place
  | .error _ => throw (.invalidProgram "socket family cannot convert to destination size")

def write (h : Hooks S E I) (address : Address) (output length : Pointer (Option Provenance)) (name : String) : M S Unit := do
  if h.isLiteralNull output || h.isLiteralNull length then throw (.undefinedBehavior s!"{name}: socket address or length pointer is null")
  let socklen ← h.layout "socklen_t"
  let lengthPlace := h.ptrToPlace length socklen
  let bufferLength ← h.readSigned lengthPlace socklen.layout.size
  if bufferLength < 0 || bufferLength > 18446744073709551615 then throw (.invalidProgram "socklen does not fit u64")
  let buffer ← match address with
    | .v4 bits port => do
      let buffer ← h.allocate (← h.layout "sockaddr_in") .stack
      h.writeZeros (h.pointer buffer) buffer.layout.layout.size
      family h (← h.field buffer "sin_family") "AF_INET"
      h.writeBytes (h.pointer (← h.field buffer "sin_port")) (networkBytes port.toNat 2)
      h.writeBytes (h.pointer (← h.field (← h.field buffer "sin_addr") "s_addr")) (networkBytes bits.toNat 4)
      pure buffer
    | .v6 bits port flow scope => do
      let buffer ← h.allocate (← h.layout "sockaddr_in6") .stack
      h.writeZeros (h.pointer buffer) buffer.layout.layout.size
      family h (← h.field buffer "sin6_family") "AF_INET6"
      h.writeBytes (h.pointer (← h.field buffer "sin6_port")) (networkBytes port.toNat 2)
      h.writeInt flow.toNat (← h.field buffer "sin6_flowinfo")
      h.writeInt scope.toNat (← h.field buffer "sin6_scope_id")
      h.writeBytes (h.pointer (← h.field (← h.field buffer "sin6_addr") "s6_addr")) (networkBytes bits.toNat 16)
      pure buffer
  h.memCopy (h.pointer buffer) output (Size.ofBytes (min buffer.layout.layout.size.bytes (UInt64.ofNat bufferLength.toNat))) true
  h.deallocate (h.pointer buffer) .stack
  h.writeInt buffer.layout.layout.size.bytes.toNat lengthPlace

private def allocateInfos (h : Hooks S E I) (iterator : I) (budget : Nat) : M S (Pointer (Option Provenance)) := do
  match budget with
  | 0 => throw (.resourceExhaustion "getaddrinfo allocation list budget")
  | budget+1 =>
    let some (address,iterator) ← h.nextAddress iterator | return Pointer.null
    let info ← h.allocate (← h.layout "addrinfo") .socketAddress
    let flagsField ← h.field info "ai_flags"
    let flags ← if h.gnu then do
        let mapped ← h.libcI32 "AI_V4MAPPED"
        let config ← h.libcI32 "AI_ADDRCONFIG"
        pure (mapped ||| config)
      else pure 0
    h.writeInt flags.toInt flagsField
    let field ← h.field info "ai_family"
    h.writeScalar (← h.libc (match address with | .v4 .. => "AF_INET" | .v6 .. => "AF_INET6")) field
    let field ← h.field info "ai_socktype"
    h.writeScalar (← h.libc "SOCK_STREAM") field
    h.writeInt 0 (← h.field info "ai_protocol")
    let storage ← h.layout "sockaddr_storage"
    let length ← h.field info "ai_addrlen"
    let field ← h.field info "ai_addr"
    h.writeInt storage.layout.size.bytes.toNat length
    let buffer ← h.allocate storage .machine
    h.writeZeros (h.pointer buffer) buffer.layout.layout.size
    write h address (h.pointer buffer) (h.pointer length) "getaddrinfo"
    h.writePointer (h.pointer buffer) field
    h.writePointer Pointer.null (← h.field info "ai_canonname")
    let field ← h.field info "ai_next"
    h.writePointer (← allocateInfos h iterator budget) field
    return h.pointer info

private def freeInfos (h : Hooks S E I) (pointer : Pointer (Option Provenance)) (budget : Nat) : M S Unit := do
  if h.isLiteralNull pointer then return
  match budget with
  | 0 => throw (.resourceExhaustion "freeaddrinfo traversal budget")
  | budget+1 =>
    let info := h.ptrToPlace pointer (← h.layout "addrinfo")
    h.deallocate (← h.readPlacePointer (← h.field info "ai_addr")) .machine
    let next ← h.readPlacePointer (← h.field info "ai_next")
    freeInfos h next budget
    h.deallocate pointer .socketAddress
private def servicePort (bytes : ByteArray) : Option UInt16 := do
  let _ ← String.fromUTF8? bytes
  let bytes := if bytes.data[0]? == some 43 then bytes.extract 1 bytes.size else bytes
  if bytes.isEmpty then none else do
    let value ← bytes.data.foldlM (fun total byte =>
      if byte < 48 || byte > 57 then none
      else
        let value := total*10+(byte.toNat-48)
        if value > 65535 then none else some value) 0
    return UInt16.ofNat value

def getaddrinfo (h : Hooks S E I) (node service hints result : OpTy Provenance) : M S (Scalar Provenance) := do
  let node ← h.readPointer node
  let service ← h.readPointer service
  let hints ← h.readPointer hints
  let result ← h.derefAs result (← h.pointerLayout)
  if h.isLiteralNull node then throw (.unsupported "getaddrinfo without node unsupported")
  let port ← if h.isLiteralNull service then pure (0 : UInt16) else do
    let some port := servicePort (← h.readCString service) | throw (.unsupported "getaddrinfo non-numeric service unsupported")
    pure port
  let some node := String.fromUTF8? (← h.readCString node) | throw (.unsupported "getaddrinfo node is not UTF-8")
  if h.isLiteralNull hints then throw (.unsupported "getaddrinfo requires socket type hint")
  let hints := h.ptrToPlace hints (← h.layout "addrinfo")
  let zero ← lift ((Scalar.fromInt 0 (Size.ofBytes 4)).mapError fun _ => .invalidProgram "i32 zero construction")
  if (← h.readScalar (← h.field hints "ai_family")) != zero then throw (.unsupported "getaddrinfo family hints unsupported")
  let kind ← h.readScalar (← h.field hints "ai_socktype")
  if kind != (← h.libc "SOCK_STREAM") then throw (.unsupported "getaddrinfo requires SOCK_STREAM")
  if (← h.readScalar (← h.field hints "ai_protocol")) != zero then throw (.unsupported "getaddrinfo protocol hints unsupported")
  if (← h.readScalar (← h.field hints "ai_flags")) != zero then throw (.unsupported "getaddrinfo flag hints unsupported")
  match ← h.resolve node port with
  | .error error =>
    h.resolutionDiagnostic error
    IoError.setLastError h.errors (.libc "EPROTO")
    h.libc "EAI_SYSTEM"
  | .ok iterator =>
    let pointer ← Files.withDrop (allocateInfos h iterator h.listBudget) (h.dropIterator iterator)
    h.writePointer pointer result
    return zero

def freeaddrinfo (h : Hooks S E I) (operand : OpTy Provenance) : M S Unit := do
  freeInfos h (← h.readPointer operand) h.listBudget
end Miri.Interpreter.SocketAddress
