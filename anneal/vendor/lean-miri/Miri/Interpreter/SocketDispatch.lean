import Miri.Interpreter.SocketMachine
import Miri.Interpreter.ForeignItems

/-! Entire socket/address/pipe arm group in pinned unix/foreign_items.rs.
Caller ABI construction uses compiler socklen_t, size_t, ssize_t records. -/
namespace Miri.Interpreter.SocketDispatch
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Operation where
  | socketpair | pipe | pipe2 | create | bind | listen | accept | accept4 | connect
  | send | recv | setOption | getOption | localName | peerName | shutdown | getaddrinfo | freeaddrinfo
  deriving DecidableEq, Repr
inductive ArgType where | i32 | pointer | socklenT | sizeT | ssizeT | unit deriving DecidableEq, Repr
structure Signature where
  args : Array ArgType
  ret : ArgType

def parse : String → Option Operation
  | "socketpair" => some .socketpair | "pipe" => some .pipe | "pipe2" => some .pipe2
  | "socket" => some .create | "bind" => some .bind | "listen" => some .listen
  | "accept" => some .accept | "accept4" => some .accept4 | "connect" => some .connect
  | "send" => some .send | "recv" => some .recv | "setsockopt" => some .setOption
  | "getsockopt" => some .getOption | "getsockname" => some .localName | "getpeername" => some .peerName
  | "shutdown" => some .shutdown | "getaddrinfo" => some .getaddrinfo | "freeaddrinfo" => some .freeaddrinfo
  | _ => none

def parseTarget (os name : String) : Option (Operation × Bool) :=
  if let some operation := parse name then some (operation,false)
  else if os == "solaris" || os == "illumos" then
    match name with
    | "__xnet_socketpair" => some (.socketpair,true)
    | "__xnet_socket" | "__xnet7_socket" => some (.create,false)
    | "__xnet_bind" => some (.bind,false)
    | "__xnet_connect" => some (.connect,false)
    | "__xnet_getaddrinfo" => some (.getaddrinfo,false)
    | "__xnet_getsockopt" => some (.getOption,false)
    | _ => none
  else none

def signature : Operation → Signature
  | .socketpair => ⟨#[.i32,.i32,.i32,.pointer],.i32⟩
  | .pipe => ⟨#[.pointer],.i32⟩ | .pipe2 => ⟨#[.pointer,.i32],.i32⟩
  | .create => ⟨#[.i32,.i32,.i32],.i32⟩
  | .bind | .connect => ⟨#[.i32,.pointer,.socklenT],.i32⟩
  | .listen | .shutdown => ⟨#[.i32,.i32],.i32⟩
  | .accept | .localName | .peerName => ⟨#[.i32,.pointer,.pointer],.i32⟩
  | .accept4 => ⟨#[.i32,.pointer,.pointer,.i32],.i32⟩
  | .send | .recv => ⟨#[.i32,.pointer,.sizeT,.i32],.ssizeT⟩
  | .setOption => ⟨#[.i32,.i32,.i32,.pointer,.socklenT],.i32⟩
  | .getOption => ⟨#[.i32,.i32,.i32,.pointer,.pointer],.i32⟩
  | .getaddrinfo => ⟨#[.pointer,.pointer,.pointer,.pointer],.i32⟩
  | .freeaddrinfo => ⟨#[.pointer],.unit⟩
structure Hooks (S F E I : Type) where
  socket : Socket.Hooks S F E I
  virtual : VirtualSocket.Hooks S F E
  /-- Exact rustc signature query for this source symbol. Names are retained
  because target libc typedefs such as `socklen_t` cannot be reconstructed
  from their width or from the operation's coarse argument category. -/
  expectedAbi : String → M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  pollAndUnblockZero : M S Unit
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "checked socket operand missing")
private def checked (h : Hooks S F E I) (operation : Operation) (legacy : Bool) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  let signature := signature operation
  if legacy then
    h.checkSymbolClash name
    if caller.conv != .C then throw (.undefinedBehavior "socket calling convention mismatch")
    if caller.cVariadic then throw (.undefinedBehavior "socket variadic signature mismatch")
    if args.size != signature.args.size then throw (.undefinedBehavior "socket argument count mismatch")
    return args
  let callee ← h.expectedAbi name
  if callee.conv != .C || callee.cVariadic || callee.fixedCount.toNat != signature.args.size || callee.args.size != signature.args.size then
    throw (.invalidProgram "compiler socket signature mismatch")
  if caller.conv != callee.conv then throw (.undefinedBehavior "socket calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "socket variadic signature mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "socket argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "socket return ABI mismatch")
  for (actual,expected) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat actual expected) then throw (.undefinedBehavior "socket argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != signature.args.size then throw (.invalidProgram "socket operands disagree with ABI")
  args.mapIdxM fun index op => do
    let some expected := callee.args[index]? | throw (.invalidProgram "compiler socket ABI operand missing")
    h.transmute op expected.layout

def dispatch (h : Hooks S F E I) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  let some (operation,legacy) := parseTarget h.socket.os name | return .NotSupported
  if operation == .pipe2 && !(#["linux","android","freebsd","solaris","illumos"].contains h.socket.os) then
    throw (.unsupported "pipe2 unsupported on target OS")
  let args ← checked h operation legacy name abi args
  let first ← arg args 0
  let int := fun (value : Int32) => h.socket.writeInt value.toInt dest
  match operation with
  | .socketpair => int (← VirtualSocket.socketpair h.virtual first (← arg args 1) (← arg args 2) (← arg args 3))
  | .pipe => int (← VirtualSocket.pipe2 h.virtual first none)
  | .pipe2 => int (← VirtualSocket.pipe2 h.virtual first (some (← arg args 1)))
  | .create => int (← Socket.create h.socket first (← arg args 1) (← arg args 2))
  | .bind => int (← Socket.bind h.socket first (← arg args 1) (← arg args 2))
  | .listen => int (← Socket.listen h.socket first (← arg args 1))
  | .accept | .accept4 =>
    let flags ← if operation == .accept4 then (arg args 3).map some else pure none
    Socket.accept4 h.socket first (← arg args 1) (← arg args 2) flags dest
  | .connect => Socket.connect h.socket first (← arg args 1) (← arg args 2) dest
  | .send | .recv => Socket.sendRecv h.socket (operation == .send) first (← arg args 1) (← arg args 2) (← arg args 3) dest
  | .setOption => int (← Socket.setOption h.socket first (← arg args 1) (← arg args 2) (← arg args 3) (← arg args 4))
  | .getOption => int (← Socket.getOption h.socket first (← arg args 1) (← arg args 2) (← arg args 3) (← arg args 4))
  | .localName => int (← Socket.localName h.socket first (← arg args 1) (← arg args 2))
  | .peerName => Socket.peerName h.socket first (← arg args 1) (← arg args 2) dest
  | .shutdown => int (← Socket.shutdown h.socket first (← arg args 1))
  | .getaddrinfo => h.writeScalar (← SocketAddress.getaddrinfo h.socket.address first (← arg args 1) (← arg args 2) (← arg args 3)) dest
  | .freeaddrinfo => SocketAddress.freeaddrinfo h.socket.address first
  return .NeedsReturn

/-- Called by the existing Linux syscall dispatcher only after its sequential
check_varargs for [i32,*sockaddr,*socklen_t,i32]; extra varargs stay ignored. -/
def syscallAccept4 (h : Hooks S F E I) (socket address length flags : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit :=
  Socket.accept4 h.socket socket address length (some flags) dest

def bindUnix (h : Hooks S F E I)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B Inst) :
    ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B Inst := {
  base with unix := fun name abi args dest => do
    if base.family != .unix || base.os != h.socket.os then throw (.invalidProgram "socket dispatcher target mismatch")
    if h.socket.communicate then h.pollAndUnblockZero
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.unix name abi args dest }
end Miri.Interpreter.SocketDispatch
