import Sail.Common

open Sail (Result)

namespace Sail.ArchSem

/-- Architecture parameters known to ArchSem. -/
class Arch where
  /-- Number of bits used to index an address. -/
  addr_size : Nat
  /--
  ARMs memory model has "Memory types and attributes" such as
  "Normal Memory" or "Device Memory".
  -/
  addr_space : Type
  /-- Is this architecture CHERI-enabled. -/
  CHERI : Bool
  /--
  The base 2 logarithm of the number of bytes a CHERI tag bit projects.
  This field is only meaningful if CHERI is set true.
  -/
  cap_size_log : Nat
  /-- Architecture register types. -/
  register : Type
  [register_deq : DecidableEq register]
  [register_hashable : Hashable register]
  register_type : register → Type
  /-- Memory access classes to be used in MemRequest structure. -/
  mem_acc : Type
  mem_acc_is_explicit : mem_acc → Bool
  mem_acc_is_ifetch : mem_acc → Bool
  mem_acc_is_ttw : mem_acc → Bool
  mem_acc_is_relaxed : mem_acc → Bool
  mem_acc_is_rel_acq_rcpc : mem_acc → Bool
  mem_acc_is_rel_acq_rcsc : mem_acc → Bool
  mem_acc_is_rel_acq (acc : mem_acc) : Bool :=
    mem_acc_is_rel_acq_rcpc acc || mem_acc_is_rel_acq_rcsc acc
  mem_acc_is_standalone : mem_acc → Bool
  mem_acc_is_exclusive : mem_acc → Bool
  mem_acc_is_atomic_rmw : mem_acc → Bool
  /-- Type associated with translation start ISA effect. -/
  trans_start : Type
  /-- Type associated with translation end ISA effect. -/
  trans_end : Type
  /-- The type thrown on physical memory access abort. -/
  abort : Type
  /-- Barrier types. -/
  barrier : Type
  /-- Cache operations for data and instruction caches. -/
  cache_op : Type
  /- Translation lookaside buffer instructions. -/
  tlbi : Type
  /-- Type thrown on fault or exception. -/
  exn : Type
  /--
  ARM system registers can be accessed implicitly or explicitly which changes
  their timing properties? This type enumerates the access types.
  -/
  sys_reg_id : Type

instance [Arch] : DecidableEq Arch.register := Arch.register_deq
instance [Arch] : Hashable Arch.register := Arch.register_hashable
variable [Arch]

/-- ArchSem's external memory request type used in ISA effects. -/
structure MemRequest where
  accessKind : Arch.mem_acc
  address : BitVec Arch.addr_size
  addressSpace : Arch.addr_space
  size : Nat
  numTag : Nat

/--
This reflects Sail's Mem_request structure, having size and numTags at both
type and term level. It is used by the sail-generated lean code.

To prevent from exposing this redundancy to ArchSem users, the `Mem_request`
type is converted to `MemRequest` before reaching the effect interface.
-/
structure Mem_request (_size : Nat) (_numTags : Nat)
    (addr_size : Nat) (addr_space : Type) (mem_acc : Type) where
  access_kind : mem_acc
  address : BitVec addr_size
  address_space : addr_space
  size : Nat
  num_tag : Nat

/-- Convert the sail-internal memory request type to the ArchSem-external type. -/
def Mem_request.toArchSem
    {size numTag: Nat}
    (memReq : Mem_request size numTag Arch.addr_size Arch.addr_space Arch.mem_acc)
    : ArchSem.MemRequest :=
  { accessKind := memReq.access_kind
  , address := memReq.address
  , addressSpace := memReq.address_space
  , size := size
  , numTag := numTag }

/-- An effect is type which can be used to instantiate a free monad. -/
class Effect.{u, v} (Eff : Type v) where
  ret : Eff → Type u

/-- Free monad effects are compositional. -/
instance [Effect A] [Effect B] : Effect (A ⊕ B) where
  ret eff := match eff with
    | .inl a => Effect.ret a
    | .inr b => Effect.ret b

instance [Effect A] : Effect (Except ε A) where
  ret eff := match eff with
    | .error _ => Empty
    | .ok eff => Effect.ret eff

/--
The finite choice effect used to introducing finite non-determinisim.
-/
def FinChoice := Nat
def FinChoice.ret : FinChoice → Type := fun n => Fin n

instance : Effect FinChoice where
  ret choice := Fin choice

/--
Free Monad, based on the _freer monad_ of Kiselyov and Ishii.

Unlike the standard implementation of the freer monad such as in CSLib,
we use a separate function for effect return types which
lets the free monad live in the same universe as its effect
return types.
-/
inductive FreeM.{u, v, w} (Eff : Type v) [Effect.{u, v} Eff] (α : Type w)
    : Type (max u (max v w)) where
  | pure (a : α) : FreeM Eff α
  | impure (call : Eff) (cont : Effect.ret call → FreeM Eff α) : FreeM Eff α

def FreeM.bind [Effect Eff] (x : FreeM Eff α) (f : α → FreeM Eff β) : FreeM Eff β :=
  match x with
    | FreeM.pure x => f x
    | FreeM.impure op cont => FreeM.impure op (fun r => FreeM.bind (cont r) f)

instance [Effect Eff] : Monad (FreeM Eff) where
  pure x := FreeM.pure x
  bind := FreeM.bind

def FreeM.liftM {m : Type → Type} [Monad m] [Effect Eff]
    (interp : (eff : Eff) → m (Effect.ret eff)) : FreeM Eff α → m α
  | .pure a => return a
  | .impure eff cont => do
    let res ← interp eff
    FreeM.liftM interp (cont res)

/--
The ArchSem interface ISA Effect type.
Represents primitive operations an architecture instruction can perform.
ISA instructions are a free monad of InstructionEffects.
-/
inductive InstructionEffect where
  | regRead (reg : Arch.register) (accessType : Option Arch.sys_reg_id)
  | regWrite (reg : Arch.register) (accessType : Option Arch.sys_reg_id) (value: Arch.register_type reg)
  | memRead (memReq : MemRequest)
  | memWrite (memReq : MemRequest) (value : BitVec (8 * memReq.size)) (tags : BitVec (memReq.numTag))
  | memWriteAnnounce (memReq : MemRequest)
  | barrier (barrier : Arch.barrier)
  | cacheOp (op : Arch.cache_op)
  | tlbOp (op : Arch.tlbi)
  | clockCycle
  | getCycleCount
  | translationStart (translationStart : Arch.trans_start)
  | translationEnd (translationEnd : Arch.trans_end)
  | archException (exception : Arch.exn)
  | returnException
  | printMessage (msg : String)

def InstructionEffect.ret : InstructionEffect → Type
  | .regRead reg _ => Arch.register_type reg
  | .regWrite _ _ _ => Unit
  | .memRead memReq => Except Arch.abort (BitVec (8 * memReq.size) × BitVec (memReq.numTag))
  | .memWrite _ _ _ => Except Arch.abort Unit
  | .memWriteAnnounce _ => Unit
  | .barrier _ => Unit
  | .cacheOp _ => Unit
  | .tlbOp _ => Unit
  | .clockCycle => Unit
  | .getCycleCount => Nat
  | .translationStart _ => Unit
  | .translationEnd _ => Unit
  | .archException _ => Unit
  | .returnException => Unit
  | .printMessage _ => Unit

instance : Effect InstructionEffect where
  ret := InstructionEffect.ret

/--
The lean-backend fills in the userError type to define `SailM`, the ISA
instruction monad.
-/
abbrev PreSailM (userError : Type) :=
  FreeM ((Except (Sail.Error userError) InstructionEffect) ⊕ FinChoice)

abbrev PreSailME ue exception :=
  FreeM (Except exception ((Except (Sail.Error ue) InstructionEffect) ⊕ FinChoice))

instance: MonadExcept ue (PreSailME ue α) where
  throw e := .impure (.ok (.inl (.error (.User e)))) Empty.elim
  tryCatch eff h :=
    let rec tryCatch eff h :=
      match eff with
        | .pure v => .pure v
        | .impure (.ok (.inl (.error (.User err)))) _cont => h err
        | .impure eff cont => .impure eff (fun v => tryCatch (cont v) h)
    tryCatch eff h


inductive RegisterRef : Type → Type where
  | Reg (r : Arch.register) : RegisterRef (Arch.register_type r)
export RegisterRef (Reg)

namespace PreSail

variable [Arch]

@[simp_sail]
def sailTryCatch (e : PreSailM ue α) (h : ue → PreSailM ue α) : PreSailM ue α :=
  match e with
  | .pure v => .pure v
  | .impure (.inl (.error (.User e))) _cont => h e
  | .impure eff cont => .impure eff (fun v => sailTryCatch (cont v) h)

@[simp_sail]
def sailThrow (e : ue) : PreSailM ue α := .impure (.inl (.error (.User e))) Empty.elim

instance: MonadExceptOf (Sail.Error userError) (PreSailM userError) where
  throw e := FreeM.impure (.inl (.error e)) Empty.elim
  tryCatch eff h :=
    let rec tryCatch eff h := match eff with
    | .pure v => .pure v
    | .impure (.inl (.error e)) _cont => h e
    | .impure eff cont => .impure eff (fun v => tryCatch (cont v) h)
  tryCatch eff h

def unwrapValue : (x : PreSailM ue α) → match x with | FreeM.pure _ => α | FreeM.impure _ _ => Unit
  | .pure a => a
  | .impure _ _ => ()

def choose_fin (n : Nat) : PreSailM ue (Fin n) :=
  FreeM.impure (.inr n) FreeM.pure

def undefined_unit (_ : Unit) : PreSailM ue Unit := pure ()

def undefined_bit (_ : Unit) : PreSailM ue (BitVec 1) := do
  return BitVec.ofFin (← choose_fin 2)

def undefined_bool (_ : Unit) : PreSailM ue Bool := do
  return ((← choose_fin 2) == 0)

def undefined_range (low high : Int) : PreSailM ue Int := do
  return (low + (← choose_fin (high - low).toNat))

def undefined_bitvector (n : Nat) : PreSailM ue (BitVec n) := do
  return @BitVec.ofFin n (← choose_fin _)

def undefined_int (_ : Unit) : PreSailM ue Int := do
  .impure (.inl (.error (.InfiniteNondeterminisim))) (fun x => by simp [Effect.ret] at x; grind)

def undefined_nat (_ : Unit) : PreSailM ue Nat := do
  .impure (.inl (.error (.InfiniteNondeterminisim))) (fun x => by simp [Effect.ret] at x; grind)

def undefined_string (_ : Unit) : PreSailM ue String := do
  .impure (.inl (.error (.InfiniteNondeterminisim))) (fun x => by simp [Effect.ret] at x; grind)

def undefined_vector (n : Nat) (a : α) : PreSailM ue (Vector α n) :=
  pure <| .replicate n a

def internal_pick {α : Type} (l : List α) : PreSailM ue α := do
  if l.isEmpty then
    .impure (.inr (0 : Nat)) (fun (n : Fin 0) => nomatch n)
  else
    return l.get (← choose_fin l.length)

@[simp_sail]
def writeReg (r : Arch.register) (v : Arch.register_type r) : PreSailM ue PUnit :=
  FreeM.impure (.inl (.ok (InstructionEffect.regWrite r Option.none v))) FreeM.pure

@[simp_sail]
def readReg (r : Arch.register) : PreSailM ue (Arch.register_type r) :=
  FreeM.impure (.inl (.ok (InstructionEffect.regRead r Option.none))) FreeM.pure

@[simp_sail]
def readRegRef (reg_ref : RegisterRef α) : PreSailM ue α :=
  let .Reg r := reg_ref
  readReg r

@[simp_sail]
def writeRegRef (reg_ref : RegisterRef α) (v : α) : PreSailM ue Unit :=
  let .Reg r := reg_ref
  writeReg r v

@[simp_sail]
def reg_deref (reg_ref : RegisterRef α) : PreSailM ue α :=
  readRegRef reg_ref

@[simp_sail]
def sail_assert (p : Bool) (s : String) : PreSailM ue Unit :=
  if p then .pure () else .impure (.inl (.error (.Assertion s))) Empty.elim

--- Older versions of Sail used assert, which clashes with newer versions of Lean
@[simp_sail]
def assert (p : Bool) (s : String) : PreSailM ue Unit := sail_assert p s

@[simp_sail]
def sail_mem_read (mem_req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) :
    PreSailM ue (Result ((Vector (BitVec 8) n) × (Vector Bool nt)) Arch.abort) :=
  let req := mem_req.toArchSem
  let bitVecsToSail
      : Except Arch.abort (BitVec (8 * n) × BitVec nt) →
        Except Arch.abort ((Vector (BitVec 8) n) × (Vector Bool nt))
    := Except.map (fun (value,tags) =>
      let valueBytes := bitvec_to_vecbytes value
      let tagsVector := bitvec_to_vecbool tags
      (valueBytes, tagsVector))
   let exceptToResult {ε α : Type} : Except ε α → Result α ε
     | .ok a => .Ok a
     | .error e => .Err e
  .impure (.inl (.ok (InstructionEffect.memRead req)))
    (.pure ∘ exceptToResult ∘ bitVecsToSail)


@[simp_sail]
def sail_mem_write (mem_req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc)
    (valueBytes : Vector (BitVec 8) n) (tagsVector : Vector Bool nt)
    : PreSailM ue (Result (Option Bool) Arch.abort) :=
  let req := mem_req.toArchSem
  let value : BitVec (8*n) := vecbytes_to_bitvec valueBytes
  let tags : BitVec nt := vecbool_to_bitvec tagsVector
  let resultToSail : Except Arch.abort Unit → Result (Option Bool) Arch.abort
    | .ok () => .Ok (.none)
    | .error abort => .Err abort
  .impure (.inl (.ok (InstructionEffect.memWrite req value tags)))
    (.pure ∘ resultToSail)


@[simp_sail]
def sail_sys_reg_read (_id : Arch.sys_reg_id) (r : RegisterRef α) : PreSailM ue α :=
  readRegRef r

@[simp_sail]
def sail_sys_reg_write (_id : Arch.sys_reg_id) (r : RegisterRef α) (v : α) : PreSailM ue Unit :=
  writeRegRef r v

def sail_mem_address_announce (ann : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc)
    : PreSailM ue Unit :=
  .impure (.inl (.ok (.memWriteAnnounce ann.toArchSem))) .pure

@[simp_sail]
def sail_translation_start (t : Arch.trans_start) : PreSailM ue Unit :=
  .impure (.inl (.ok (.translationStart t))) .pure

@[simp_sail]
def sail_translation_end (t : Arch.trans_end) : PreSailM ue Unit :=
  .impure (.inl (.ok (.translationEnd t))) .pure

@[simp_sail]
def sail_barrier (b : Arch.barrier) : PreSailM ue Unit :=
  .impure (.inl (.ok (.barrier b))) .pure

@[simp_sail]
def sail_take_exception (e : Arch.exn) : PreSailM ue Unit :=
  .impure (.inl (.ok (.archException e))) .pure

@[simp_sail]
def sail_return_exception (_ : Unit) : PreSailM ue Unit :=
  .impure (.inl (.ok (.returnException))) .pure

@[simp_sail]
def sail_cache_op (op : Arch.cache_op) : PreSailM ue Unit :=
  .impure (.inl (.ok (.cacheOp op))) .pure

@[simp_sail]
def sail_tlbi (op : Arch.tlbi) : PreSailM ue Unit :=
  .impure (.inl (.ok (.tlbOp op))) .pure

@[simp_sail]
def cycle_count (_ : Unit) : PreSailM ue Unit :=
  .impure (.inl (.ok (.clockCycle))) .pure

@[simp_sail]
def get_cycle_count (_ : Unit) : PreSailM ue Nat := do
  .impure (.inl (.ok (.getCycleCount))) .pure

def print_effect (str : String) : PreSailM ue Unit :=
  .impure (.inl (.ok (.printMessage str))) .pure

def print_int_effect (str : String) (n : Int) : PreSailM ue Unit :=
  print_effect s!"{str}{n}\n"

def print_bits_effect {w : Nat} (str : String) (x : BitVec w) : PreSailM ue Unit :=
  print_effect s!"{str}{Sail.BitVec.toFormatted x}\n"

def print_endline_effect (str : String) : PreSailM ue Unit :=
  print_effect s!"{str}\n"

def sailTryCatchE (eff : PreSailME ue e α) (h : ue → PreSailME ue e α)
    : PreSailME ue e α :=
  tryCatch eff h

def PreSailME.run : PreSailME ue α α → PreSailM ue α
 | .pure v => .pure v
 | .impure (.error ret) _cont => .pure ret
 | .impure (.ok eff) cont =>
   .impure eff (fun v => PreSailME.run (cont v))

def PreSailME.throw (e : α) : PreSailME ue α β :=
  .impure (.error e) Empty.elim

instance : MonadLift (PreSailM ue) (PreSailME ue ε) where
  monadLift m :=
    let rec lift m :=
      match m with
      | .pure v => .pure v
      | .impure eff cont => .impure (.ok eff) (fun v => lift (cont v))
    lift m

end Sail.ArchSem.PreSail
