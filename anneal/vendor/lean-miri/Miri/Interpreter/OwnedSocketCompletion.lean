import Miri.Interpreter.ScalarOps
import Miri.Interpreter.IoCompletion
import Miri.Interpreter.SocketAddress

/-! Exact socket.rs finish environments and result-specific source bodies.
File-description IO and socket send/recv use distinct source result encodings. -/
namespace Miri.Interpreter.OwnedSocketCompletion
open Miri.ABI Miri.Memory
abbrev Dest := IoCompletionData.Dest
inductive Bytes where
  | file (capture : IoCompletionData.Capture)
  | socket (dest : Dest)
structure Accept where
  address : Pointer (Option Provenance)
  length : Pointer (Option Provenance)
  dest : Dest
structure Connect where
  dest : Dest
structure Peer where
  address : Pointer (Option Provenance)
  length : Pointer (Option Provenance)
  dest : Dest
inductive Data : Type → Type where
  | bytes (value : Bytes) : Data Nat
  | accept (value : Accept) : Data (Int32 × SocketAddress.Address)
  | connect (value : Connect) : Data Unit
  | peer (value : Peer) : Data SocketAddress.Address
structure Finish (S E A : Type) where
  body : Files.Result E A → EStateM StepError S Unit
  capture : Option (Data A) := none
instance : Coe (Files.Result E A → EStateM StepError S Unit) (Finish S E A) := ⟨fun body => ⟨body,none⟩⟩
instance : CoeFun (Finish S E A) (fun _ => Files.Result E A → EStateM StepError S Unit) := ⟨Finish.body⟩
def Finish.source (capture : Data A) (body : Files.Result E A → EStateM StepError S Unit) : Finish S E A := ⟨body,some capture⟩

structure Hooks (S E Iter : Type) where
  file : IoCompletion.Hooks S E
  address : SocketAddress.Hooks S E Iter
  pointerSize : Size

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw error

def bytes (h : Hooks S E I) (capture : Bytes) (result : Files.Result E Nat) : EStateM StepError S Unit := do
  match capture with
  | .file capture => IoCompletion.invoke h.file capture result
  | .socket dest =>
    match result with
    | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error dest
    | .ok count =>
      if count >= 2^64 then throw (.invalidProgram "socket count usize-to-target-usize conversion panic")
      let scalar ← lift (Scalar.fromUInt (BitVec.ofNat 128 count) h.pointerSize |>.mapError ScalarOps.scalarError)
      h.address.writeScalar scalar dest

def accept (h : Hooks S E I) (capture : Accept)
    (result : Files.Result E (Int32 × SocketAddress.Address)) : EStateM StepError S Unit := do
  match result with
  | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error capture.dest
  | .ok (number,address) =>
    unless h.address.isLiteralNull capture.address do
      SocketAddress.write h.address address capture.address capture.length "accept4"
    h.address.writeInt number.toInt capture.dest

def connect (h : Hooks S E I) (capture : Connect) (result : Files.Result E Unit) : EStateM StepError S Unit := do
  match result with
  | .ok () => h.address.writeInt 0 capture.dest
  | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error capture.dest

def peer (h : Hooks S E I) (capture : Peer) (result : Files.Result E SocketAddress.Address) : EStateM StepError S Unit := do
  match result with
  | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error capture.dest
  | .ok address =>
    SocketAddress.write h.address address capture.address capture.length "getpeername"
    h.address.writeInt 0 capture.dest
end Miri.Interpreter.OwnedSocketCompletion
