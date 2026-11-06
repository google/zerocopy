import Sail.Attr
import Sail.Common

import Std.Data.ExtDHashMap
import Std.Data.ExtHashMap

namespace Sail.ConcurrencyInterfaceV1

structure ChoiceSource where
  (α : Type)
  (nextState : Sail.Primitive → α → α)
  (choose : ∀ p : Sail.Primitive, α → p.reflect)

def trivialChoiceSource : ChoiceSource where
  α := Unit
  nextState _ _ := ()
  choose p _ :=
    match p with
    | .bool => false
    | .bit => 0
    | .int => 0
    | .nat => 0
    | .string => ""
    | .fin _ => 0
    | .bitvector _ => 0

class Arch where
  va_size : Nat
  pa : Type
  arch_ak : Type
  translation : Type
  trans_start : Type
  trans_end : Type
  abort : Type
  barrier : Type
  cache_op : Type
  tlb_op : Type
  fault : Type
  sys_reg_id : Type

inductive Access_variety where
  | AV_plain
  | AV_exclusive
  | AV_atomic_rmw
  deriving Inhabited, DecidableEq, Repr

export Access_variety (AV_plain AV_exclusive AV_atomic_rmw)

inductive Access_strength where
  | AS_normal
  | AS_rel_or_acq
  | AS_acq_rcpc
  deriving Inhabited, DecidableEq, Repr

export Access_strength(AS_normal AS_rel_or_acq AS_acq_rcpc)

structure Explicit_access_kind where
  variety : Access_variety
  strength : Access_strength
deriving Repr

inductive Access_kind (arch : Type) where
  | AK_explicit (_ : Explicit_access_kind)
  | AK_ifetch (_ : Unit)
  | AK_ttw (_ : Unit)
  | AK_arch (_ : arch)
  deriving Inhabited, Repr

export Access_kind(AK_explicit AK_ifetch AK_ttw AK_arch)


structure Mem_read_request
  (n : Nat) (vasize : Nat) (pa : Type) (ts : Type) (arch_ak : Type) where
  access_kind : Access_kind arch_ak
  va : (Option (BitVec vasize))
  pa : pa
  translation : ts
  size : Int
  tag : Bool
  deriving Inhabited, Repr

structure Mem_write_request
  (n : Nat) (vasize : Nat) (pa : Type) (ts : Type) (arch_ak : Type) where
  access_kind : Access_kind arch_ak
  va : (Option (BitVec vasize))
  pa : pa
  translation : ts
  size : Int
  value : (Option (BitVec (8 * n)))
  tag : (Option Bool)
  deriving Inhabited, Repr

end Sail.ConcurrencyInterfaceV1

namespace Sail.ConcurrencyInterfaceV1

open Sail (Result)

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

structure SequentialState (RegisterType : Register → Type) (c : ChoiceSource) where
  regs : Std.ExtDHashMap Register RegisterType
  choiceState : c.α
  mem : Std.ExtHashMap Nat (BitVec 8)
  tags : Unit
  cycleCount : Nat -- Part of the concurrency interface. See `{get_}cycle_count`
  sailOutput : Array String -- TODO: be able to use the IO monad to run

abbrev PreSailM (RegisterType : Register → Type) (c : ChoiceSource) (ue: Type) :=
  EStateM (Sail.Error ue) (SequentialState RegisterType c)

variable (RegisterType) in
abbrev PreSailME c ue α := ExceptT (Sail.Error ue ⊕ α) (PreSailM RegisterType c ue)

inductive RegisterRef (RegisterType : Register → Type) : Type → Type where
  | Reg (r : Register) : RegisterRef _ (RegisterType r)
export RegisterRef (Reg)

namespace PreSail

@[simp_sail]
def sailTryCatch (e : PreSailM RegisterType c ue α) (h : ue → PreSailM RegisterType c ue α) :
    PreSailM RegisterType c ue α :=
  EStateM.tryCatch e fun e =>
    match e with
    | .User u => h u
    | _ => EStateM.throw e

@[simp_sail]
def sailThrow (e : ue) : PreSailM RegisterType c ue α := EStateM.throw (.User e)

def choose (p : Sail.Primitive) : PreSailM RegisterType c ue p.reflect :=
  modifyGet
    (fun σ => (c.choose _ σ.choiceState, { σ with choiceState := c.nextState p σ.choiceState }))

def undefined_unit (_ : Unit) : PreSailM RegisterType c ue Unit := pure ()

def undefined_bit (_ : Unit) : PreSailM RegisterType c ue (BitVec 1) :=
  choose .bit

def undefined_bool (_ : Unit) : PreSailM RegisterType c ue Bool :=
  choose .bool

def undefined_int (_ : Unit) : PreSailM RegisterType c ue Int :=
  choose .int

def undefined_range (low high : Int) : PreSailM RegisterType c ue Int := do
  pure (low + (← choose .int) % (high - low))

def undefined_nat (_ : Unit) : PreSailM RegisterType c ue Nat :=
  choose .nat

def undefined_string (_ : Unit) : PreSailM RegisterType c ue String :=
  choose .string

def undefined_bitvector (n : Nat) : PreSailM RegisterType c ue (BitVec n) :=
  choose <| .bitvector n

def undefined_vector (n : Nat) (a : α) : PreSailM RegisterType c ue (Vector α n) :=
  pure <| .replicate n a

def internal_pick {α : Type} : List α → PreSailM RegisterType c ue α
  | [] => .error .Unreachable
  | (a :: as) => do
    let idx ← choose <| .fin (as.length)
    pure <| (a :: as).get idx

@[simp_sail]
def writeReg (r : Register) (v : RegisterType r) : PreSailM RegisterType c ue PUnit :=
  modify fun s => { s with regs := s.regs.insert r v }

@[simp_sail]
def readReg (r : Register) : PreSailM RegisterType c ue (RegisterType r) := do
  let .some s := (← get).regs.get? r
    | throw .Unreachable
  pure s

@[simp_sail]
def readRegRef (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType c ue α :=
  match reg_ref with | .Reg r => readReg r

@[simp_sail]
def writeRegRef (reg_ref : @RegisterRef Register RegisterType α) (a : α) :
  PreSailM RegisterType c ue Unit :=
  match reg_ref with | .Reg r => writeReg r a

@[simp_sail]
def reg_deref (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType c ue α :=
  readRegRef reg_ref

@[simp_sail]
def sail_assert (p : Bool) (s : String) : PreSailM RegisterType c ue Unit :=
  if p then pure () else throw (.Assertion s)

--- Older versions of Sail used assert, which clashes with newer versions of Lean
@[simp_sail]
def assert (p : Bool) (s : String) : PreSailM RegisterType c ue Unit := sail_assert p s

@[simp_sail]
def writeByte (addr : Nat) (value : BitVec 8) : PreSailM RegisterType c ue PUnit := do
  modify fun s => { s with mem := s.mem.insert addr value }

@[simp_sail]
def writeBytes (addr : Nat) (value : BitVec (8 * n)) : PreSailM RegisterType c ue Bool := do
  let list := List.ofFn (λ i : Fin n => (addr + i.val, value.extractLsb' (8 * i.val) 8))
  List.forM list (λ (a, v) => writeByte a v)
  pure true

@[simp_sail]
def writeByteVec (addr : Nat) (value : Vector (BitVec 8) n) : PreSailM RegisterType c ue Bool := do
  let list := List.ofFn (λ i : Fin n => (addr + i.val, value[i]))
  List.forM list (λ (a, v) => writeByte a v)
  pure true

@[simp_sail]
def write_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) (value : BitVec (8 * data_size)) :
    PreSailM RegisterType c ue Unit := do
  let _ ← writeBytes addr.toNat value
  pure ()

@[simp_sail]
def readByte (addr : Nat) : PreSailM RegisterType c ue (BitVec 8) := do
  let .some s := (← get).mem.get? addr
    | throw (.OutOfMemoryRange addr)
  pure s

@[simp_sail]
def readBytes (size : Nat) (addr : Nat) : PreSailM RegisterType c ue ((BitVec (8 * size)) × Option Bool) :=
  match size with
  | 0 => pure (default, none)
  | 1 => do
    let b ← readByte addr
    have h : 8 * 1 = 8 := rfl
    return (h ▸ b, none)
  | n + 1 => do
    let b ← readByte addr
    let (bytes, bool) ← readBytes n (addr+1)
    have h : 8 * n + 8 = 8 * (n + 1) := by omega
    return (h ▸ bytes.append b, bool)

@[simp_sail]
def readBytesVec (size : Nat) (addr : Nat) :
    PreSailM RegisterType c ue ((Vector (BitVec 8) size) × Vector Bool nt) :=
  match size with
  | 0 => pure (default, default)
  | 1 => do
    let b ← readByte addr
    return (#v[b], default)
  | n + 1 => do
    let b ← readByte (addr + n)
    let (bytes, bool) ← readBytesVec n addr
    return (bytes.push b, bool)

@[simp_sail]
def sail_mem_write [Arch] (req : Mem_write_request n vasize (BitVec pa_size) ts arch) : PreSailM RegisterType c ue (Result (Option Bool) Arch.abort) := do
  let addr := req.pa.toNat
  let b ← match req.value with
    | some v => writeBytes addr v
    | none => pure true
  pure (.Ok (some b))

@[simp_sail]
def sail_mem_read [Arch] (req : Mem_read_request n vasize (BitVec pa_size) ts arch) : PreSailM RegisterType c ue (Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) := do
  let addr := req.pa.toNat
  let value ← readBytes n addr
  pure (.Ok value)

@[simp_sail]
def sail_barrier (_ : α) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_cache_op [Arch] (_ : Arch.cache_op) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_tlbi [Arch] (_ : Arch.tlb_op) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_translation_start [Arch] (_ : Arch.trans_start) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_translation_end [Arch] (_ : Arch.trans_end) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_take_exception [Arch] (_ : Arch.fault) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_return_exception [Arch] (_ : Arch.pa) : PreSailM RegisterType c ue Unit := pure ()

@[simp_sail]
def read_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) : PreSailM RegisterType c ue (BitVec (8 * data_size)) := do
  let ⟨bytes, _⟩ ← readBytes data_size addr.toNat
  pure bytes

@[simp_sail]
def cycle_count (_ : Unit) : PreSailM RegisterType c ue Unit :=
  modify fun s => { s with cycleCount := s.cycleCount + 1 }

@[simp_sail]
def get_cycle_count (_ : Unit) : PreSailM RegisterType c ue Nat := do
  pure (← get).cycleCount

def print_effect (str : String) : PreSailM RegisterType c ue Unit :=
  modify fun s ↦ { s with sailOutput := s.sailOutput.push str }

def print_int_effect (str : String) (n : Int) : PreSailM RegisterType c ue Unit :=
  print_effect s!"{str}{n}\n"

def print_bits_effect {w : Nat} (str : String) (x : BitVec w) : PreSailM RegisterType c ue Unit :=
  print_effect s!"{str}{Sail.BitVec.toFormatted x}\n"

def print_endline_effect (str : String) : PreSailM RegisterType c ue Unit :=
  print_effect s!"{str}\n"

@[simp_sail]
def sailTryCatchE (e : ExceptT β (PreSailM RegisterType c ue) α) (h : ue → ExceptT β (PreSailM RegisterType c ue) α) : ExceptT β (PreSailM RegisterType c ue) α :=
  EStateM.tryCatch e fun e =>
    match e with
    | .User u => h u
    | _ => EStateM.throw e

section SailME

variable {Register : Type} {RT : Register → Type} [DecidableEq Register] [Hashable Register]

instance: MonadExceptOf (Sail.Error ue) (PreSailME RT c ue α) where
  throw e := MonadExcept.throw (.inl e)
  tryCatch x h := MonadExcept.tryCatch x (fun e => match e with | .inl e => h e | .inr _ => MonadExcept.throw e)

def PreSailME.run (m : PreSailME RT c ue α α) : PreSailM RT c ue α := do
  match (← ExceptT.run m) with
    | .error (.inr e) => pure e
    | .error (.inl e) => throw e
    | .ok e => pure e

def _root_.ExceptT.map_error [Monad m] (e : ExceptT ε m α) (f : ε → ε') : ExceptT ε' m α :=
  ExceptT.mk <| do
    match ← e.run with
    | .ok x => pure $ .ok x
    | .error e => pure $ .error (f e)

instance [∀ x, CoeT α x α'] :
    CoeT (PreSailME RT c ue α β) e (PreSailME RT c ue α' β) where
  coe := e.map_error (fun x => match x with | .inl e => .inl e | .inr e => .inr e)

def PreSailME.throw (e : α) : PreSailME RT c ue α β :=
    MonadExceptOf.throw (Sum.inr (α := Sail.Error ue) e)

instance : Inhabited (SequentialState RT trivialChoiceSource) where
  default := ⟨default, (), default, default, default, default⟩

end SailME

end Sail.ConcurrencyInterfaceV1.PreSail
