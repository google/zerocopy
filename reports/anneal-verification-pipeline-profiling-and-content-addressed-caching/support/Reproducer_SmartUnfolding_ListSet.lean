-- Standalone Reproducer: Exponential O(2^m) Meta.whnf Blowup on Nested List.set under smartUnfolding
-- Subject: leanprover/lean4 v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52)

def L0 (v : Nat) : List Nat := [0, 1, 1, v] ++ List.replicate 61 0

-- 1. Unreduced List.set spine: each step wraps two nested List.set calls around xs.
def stepGetSet (i : Nat) (xs : List Nat) : Option (List Nat) :=
  match xs[3]?, xs[i]? with
  | some v, some u => some ((xs.set 3 0).set i (v + u))
  | _, _ => none

def runGetSet : Nat → List Nat → Option (List Nat)
  | 0, xs => some xs
  | k + 1, xs =>
      match stepGetSet (4 + (k % 20)) xs with
      | some xs' => runGetSet k xs'
      | none => none

-- 2. Spine-forcing setNatSpine: pattern-matching on `some xs'` forces WHNF to
-- materialize the List.cons spine at every step (0 nested List.set thunks).
def setNatSpine : List Nat → Nat → Nat → Option (List Nat)
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
      match setNatSpine xs n v with
      | some xs' => some (x :: xs')
      | none => none
  | [], _, _ => some []

def stepGetSetSpine (i : Nat) (xs : List Nat) : Option (List Nat) :=
  match xs[3]?, xs[i]? with
  | some v, some u =>
      match setNatSpine xs 3 0 with
      | some xs1 => setNatSpine xs1 i (v + u)
      | none => none
  | _, _ => none

def runGetSetSpine : Nat → List Nat → Option (List Nat)
  | 0, xs => some xs
  | k + 1, xs =>
      match stepGetSetSpine (4 + (k % 20)) xs with
      | some xs' => runGetSetSpine k xs'
      | none => none

-- Experiment A: Default smartUnfolding=true on nested List.set:
-- k=1: L0 unfolded 4 times; k=2: 20 times; k=3: 84 times; k=4: 340 times; k=5: 1,364 times (329 ms); k=8: >17,100 ms!
set_option diagnostics true in
theorem test_default_k5 (v : Nat) : (runGetSet 5 (L0 v)).isSome = true := by rfl

-- Experiment B: smartUnfolding=false on nested List.set:
-- k=5: L0 unfolded 10 times (15.4 ms); k=8: 16 times (36.1 ms); k=12: 24 times (66.5 ms).
set_option smartUnfolding false in
theorem test_no_smart_unfolding_k12 (v : Nat) : (runGetSet 12 (L0 v)).isSome = true := by rfl

-- Experiment C: Default smartUnfolding=true with spine-forcing setNatSpine:
-- k=12: ~30 ms; k=50: ~65 ms; linear O(k) scaling in both Meta.whnf and Kernel.whnf!
theorem test_spine_forced_k12 (v : Nat) : (runGetSetSpine 12 (L0 v)).isSome = true := by rfl
