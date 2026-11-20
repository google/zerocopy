import Std

/-!
Finite semantic port of Miri's `tree_borrows/unimap.rs`. `UniKeyMap` keeps
the source's reusable u32 index pool; `UniValMap` keeps optional values in an
array indexed by the same value. Large collections are represented by Lean
arrays, but all observable insertion/removal behavior is explicit.
-/

namespace Miri.TreeBorrows

structure UniIndex where
  idx : UInt32
  deriving DecidableEq, Repr, Inhabited

namespace UniIndex

def toNat (index : UniIndex) : Nat := index.idx.toNat

def ofNat? (value : Nat) : Option UniIndex :=
  if value ≤ 4294967295 then some ⟨UInt32.ofNat value⟩ else none

end UniIndex

inductive UniKeyMapError where
  | IndexSpaceExhausted (active : Nat)
  deriving DecidableEq, Repr

/-- Source `UniKeyMap<K>` from key to reusable index. -/
structure UniKeyMap (α : Type) where
  mapping : Array (α × UniIndex) := #[]
  deassigned : Array UniIndex := #[]
  deriving DecidableEq, Repr, Inhabited

inductive UniKeyMapInsertResult (α : Type) where
  | Inserted (map : UniKeyMap α) (index : UniIndex)
  | DuplicateKeyAfterReplacement (map : UniKeyMap α) (index : UniIndex)
  | Error (map : UniKeyMap α) (error : UniKeyMapError)
  deriving Repr

namespace UniKeyMap

def get [BEq α] (map : UniKeyMap α) (key : α) : Option UniIndex :=
  (map.mapping.find? fun entry => entry.1 == key).map Prod.snd

def containsKey [BEq α] (map : UniKeyMap α) (key : α) : Bool :=
  (map.get key).isSome

/-- Source insertion pops a reusable index first, otherwise converts the
current active map length to u32. A duplicate key preserves Rust HashMap's
replacement mutation before returning the source panic as an explicit result.
-/
def insert [BEq α] (map : UniKeyMap α) (key : α) : UniKeyMapInsertResult α := Id.run do
  let (available, index) ←
    match map.deassigned.back? with
    | some index =>
        let deassigned := map.deassigned.pop
        pure ({ map with deassigned }, index)
    | none =>
        match UniIndex.ofNat? map.mapping.size with
        | some index => pure (map, index)
        | none => return .Error map (.IndexSpaceExhausted map.mapping.size)
  let alreadyPresent := map.get key |>.isSome
  let mapping := (available.mapping.filter fun entry => entry.1 != key).push (key, index)
  let updated := { available with mapping }
  if alreadyPresent then
    return .DuplicateKeyAfterReplacement updated index
  return .Inserted updated index

def getOrInsert [BEq α] (map : UniKeyMap α) (key : α) :
    UniKeyMapInsertResult α :=
  match map.get key with
  | some index => .Inserted map index
  | none => map.insert key

def remove [BEq α] (map : UniKeyMap α) (key : α) : UniKeyMap α :=
  match map.get key with
  | none => map
  | some index =>
      { mapping := map.mapping.filter fun entry => entry.1 != key,
        deassigned := map.deassigned.push index }

def size (map : UniKeyMap α) : Nat := map.mapping.size

end UniKeyMap

/-- Source `UniValMap<V>` as a vector of optional values. -/
structure UniValMap (α : Type) where
  data : Array (Option α) := #[]
  deriving DecidableEq, Repr, Inhabited

namespace UniValMap

def extendTo (data : Array (Option α)) (length : Nat) : Array (Option α) :=
  data ++ Array.replicate (length - data.size) none

def containsIdx (map : UniValMap α) (index : UniIndex) : Bool :=
  match map.data[index.toNat]? with
  | some value => value.isSome
  | none => false

/-- Source insert permanently overwrites any old value at the index. -/
def insert (map : UniValMap α) (index : UniIndex) (value : α) : UniValMap α := Id.run do
  let length := index.toNat + 1
  let data := extendTo map.data length
  if h : index.toNat < data.size then
    return { data := data.set index.toNat (some value) h }
  else
    return { data }

def get (map : UniValMap α) (index : UniIndex) : Option α :=
  match map.data[index.toNat]? with
  | some value => value
  | none => none

def remove (map : UniValMap α) (index : UniIndex) : UniValMap α :=
  if h : index.toNat < map.data.size then
    { map with data := map.data.set index.toNat none h }
  else map

/-- Canonical representation for source `UniValMap::equivalent` equality.
Rust treats trailing `None` slots as absent when comparing maps; trimming them
before Lean's structural range-map comparison preserves that behavior. -/
def trimTrailingNone (map : UniValMap α) : UniValMap α := Id.run do
  let mut data := map.data
  while match data.back? with
    | some none => true
    | _ => false do
    data := data.pop
  return { data }

def isEmpty (map : UniValMap α) : Bool :=
  map.data.all Option.isNone

def entries (map : UniValMap α) : Array (UniIndex × α) := Id.run do
  let mut result := #[]
  for position in [:map.data.size] do
    match UniIndex.ofNat? position, map.data[position]? with
    | some index, some (some value) => result := result.push (index, value)
    | _, _ => pure ()
  return result

def orInsert (map : UniValMap α) (index : UniIndex) (default : α) : UniValMap α × α :=
  match map.get index with
  | some value => (map, value)
  | none => (map.insert index default, default)

def size (map : UniValMap α) : Nat := map.data.size

end UniValMap

end Miri.TreeBorrows
