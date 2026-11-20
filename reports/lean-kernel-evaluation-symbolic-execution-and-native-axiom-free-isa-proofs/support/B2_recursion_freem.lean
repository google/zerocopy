/- Probe B2: kernel reduction of recursion encodings (Lean v4.34.1).
   (1) structural fuel, (2) well-founded recursion (termination_by), (3) `partial`,
   (4) a Sail-V2-style free monad (`FreeM`) interpreted into EStateM. -/

def sumFuel : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => sumFuel n (acc + n + 1)

def sumWF (i n acc : Nat) : Nat :=
  if h : i < n then sumWF (i + 1) n (acc + i + 1) else acc
termination_by n - i

partial def sumPartial (i n acc : Nat) : Nat :=
  if i < n then sumPartial (i + 1) n (acc + i + 1) else acc

-- (1) structural: kernel ok
theorem b2_fuel : sumFuel 1000 0 = 500500 := by decide +kernel
#print axioms b2_fuel

-- (2a) WF: elaborator `decide` (WF defs are @[irreducible] for the elaborator)
theorem b2_wf_dec : sumWF 0 10 0 = 55 := by decide
-- (2b) WF: kernel-only `decide +kernel` (the kernel ignores reducibility attributes)
theorem b2_wf_dk10 : sumWF 0 10 0 = 55 := by decide +kernel
#print axioms b2_wf_dk10
theorem b2_wf_dk200 : sumWF 0 200 0 = 20100 := by decide +kernel
#print axioms b2_wf_dk200

theorem b2_wf_dk2000 : sumWF 0 2000 0 = 2001000 := by decide +kernel
#print axioms b2_wf_dk2000

-- (2c) WF with a NON-Nat (lexicographic) measure: compiled via `WellFounded.fix` + `Lean.opaqueId`
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
theorem b2_wf_lex : ack 1 1 = 3 := by decide +kernel

-- (3) partial: opaque to the kernel
theorem b2_partial : sumPartial 0 10 0 = 55 := by decide +kernel

/-! (4) Sail-V2-style free monad, as in rems-project/lean-sail `Sail/ArchSem.lean`
    (`FreeM`, `PreSailM := FreeM (Except Error Effect ⊕ FinChoice)`), with a function-based
    register file interpreter. -/
inductive Eff | rd (r : Nat) | wr (r : Nat) (v : BitVec 64)
def Eff.ret : Eff → Type | .rd _ => BitVec 64 | .wr _ _ => Unit
inductive FreeM (α : Type) where
  | pure (a : α)
  | impure (e : Eff) (k : e.ret → FreeM α)
def FreeM.bind : FreeM α → (α → FreeM β) → FreeM β
  | .pure a, f => f a
  | .impure e k, f => .impure e (fun r => (k r).bind f)
instance : Monad FreeM where pure := .pure; bind := FreeM.bind
def rdR (r : Nat) : FreeM (BitVec 64) := .impure (.rd r) .pure
def wrR (r : Nat) (v : BitVec 64) : FreeM Unit := .impure (.wr r v) .pure
/-- "execute ADD rd rs1 rs2" in Sail style -/
def execAdd (rd rs1 rs2 : Nat) : FreeM Unit := do
  let a ← rdR rs1; let b ← rdR rs2; wrR rd (a + b)
abbrev Regs := Nat → BitVec 64
def interp : FreeM α → EStateM String Regs α
  | .pure a => pure a
  | .impure (.rd r) k => do let s ← get; interp (k (s r))
  | .impure (.wr r v) k => do modify (fun s j => if j = r then v else s j); interp (k ())
def prog : Nat → FreeM Unit
  | 0 => pure ()
  | n + 1 => do execAdd 1 1 2; prog n
def resultFree (n : Nat) : Nat :=
  match (interp (prog n)).run (fun j => if j = 2 then 3 else 0) with
  | .ok _ s => (s 1).toNat | .error _ _ => 0

-- effect tree of one instruction, by rfl (as in the prior Sail RV64D `execute_add_effects`)
theorem b2_free_tree : execAdd 3 1 2 =
    .impure (.rd 1) (fun (a : BitVec 64) => .impure (.rd 2) (fun (b : BitVec 64) => .impure (.wr 3 (a + b)) .pure)) := rfl
theorem b2_free_100 : resultFree 100 = 300 := by decide +kernel
#print axioms b2_free_100
theorem b2_free_1000 : resultFree 1000 = 3000 := by decide +kernel
#print axioms b2_free_1000
