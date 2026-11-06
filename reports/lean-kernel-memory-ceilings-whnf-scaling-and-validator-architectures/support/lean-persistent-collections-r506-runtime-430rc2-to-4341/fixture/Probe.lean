import Lean.Data.PersistentArray
import Lean.Data.PersistentHashMap

open Lean

def buildArray (n : Nat) : PersistentArray Nat := Id.run do
  let mut a : PersistentArray Nat := .empty
  for i in [:n] do
    a := a.push i
  return a

def retainedArray (n : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let old := buildArray n
  let mut latest := old
  for i in [:n] do
    latest := latest.set i (n + i)
  return (old.get! 0, old.get! (n - 1), latest.get! 0, latest.get! (n - 1))

def discardedArray (n : Nat) : Nat × Nat := Id.run do
  let mut latest := buildArray n
  for i in [:n] do
    latest := latest.set i (n + i)
  return (latest.get! 0, latest.get! (n - 1))

def buildMap (n : Nat) : PersistentHashMap Nat Nat := Id.run do
  let mut m : PersistentHashMap Nat Nat := .empty
  for i in [:n] do
    m := m.insert i i
  return m

def retainedMap (n : Nat) : Option Nat × Option Nat × Option Nat × Option Nat := Id.run do
  let old := buildMap n
  let mut latest := old
  for i in [:n] do
    latest := latest.insert i (n + i)
  return (old.find? 0, old.find? (n - 1), latest.find? 0, latest.find? (n - 1))

def discardedMap (n : Nat) : Option Nat × Option Nat := Id.run do
  let mut latest := buildMap n
  for i in [:n] do
    latest := latest.insert i (n + i)
  return (latest.find? 0, latest.find? (n - 1))

def main (args : List String) : IO Unit := do
  let mode := args.headD ""
  let n := (args[1]?.getD "64").toNat!
  if n == 0 then throw <| IO.userError "n must be positive"
  match mode with
  | "array-retained" => IO.println s!"array-retained {repr (retainedArray n)}"
  | "array-discarded" => IO.println s!"array-discarded {repr (discardedArray n)}"
  | "map-retained" => IO.println s!"map-retained {repr (retainedMap n)}"
  | "map-discarded" => IO.println s!"map-discarded {repr (discardedMap n)}"
  | _ => throw <| IO.userError "unknown mode"
