/-
Stored sentences are stable under signature extension; displayed text is not.
A toy elaborator from surface strings to stored sentences, parameterized by an
environment of default numeral types, coercions and operator instances.
-/
import Toy.Extension.Axiomatic

namespace Toy.Extension

/-! ### Term level -/

/-- **Main result (reference point; same statement as `sat_map`).** For any
signature morphism `ι`, any structure `S'` of the larger language and any
stored formula `φ` of the smaller one, `φ` read along `ι` has, under every
assignment, the same truth value in `S'` as `φ` has in the reduct of `S'`
(the old symbols read through `ι`). -/
theorem stored_formula_stable_under_expansion {L L' : Sig} (ι : SigHom L L') {α : Type}
    (S' : Str L' α) {n : Nat} (φ : Formula L n) (v : Fin n → α) :
    Sat S' v (φ.map ι) ↔ Sat (S'.reduct ι) v φ :=
  sat_map ι S' v φ

/-- Negative example (`Str.reduct`): reinterpreting the old symbol `P` (here
along the identity morphism) changes the truth value of the stored sentence
`∃ x, P x`; stability is relative to the reduct, not to an arbitrary old
structure. -/
theorem stored_formula_stable_ce_reinterpreted :
    (pStr (fun _ : Unit => False)).reduct (SigHom.id LP) ≠ pStr (fun _ : Unit => True) ∧
    ¬ (Sat (pStr (fun _ : Unit => False)) noVars (existsP.map (SigHom.id LP)) ↔
       Sat (pStr (fun _ : Unit => True)) noVars existsP) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (fun S : Str LP Unit => S.rel PRel.P (fun _ => ())) h
    simp only at this
    exact (this ▸ trivial : (pStr (fun _ : Unit => False)).rel PRel.P (fun _ => ()))
  · obtain ⟨_, hx⟩ := h.2 ⟨(), trivial⟩
    exact hx

/-- Instance for `stored_formula_stable_under_expansion`: expanding by a new
constant keeps the old symbols, so the reduct is the original structure. -/
theorem stored_formula_stable_nonvacuity :
    ((pStr (fun _ : Unit => True)).withFn (fun _ : Fin 0 → Unit => ())).reduct (SigHom.inclFn LP 0)
      = pStr (fun _ : Unit => True) := rfl

/-! ### A toy elaborator -/

/-- Surface numeric types. -/
inductive Ty | nat | int
  deriving DecidableEq

/-- Surface binary operators. -/
inductive Op | add | sub | div
  deriving DecidableEq

/-- Stored function symbols: numerals, addition, truncated (natural-number)
subtraction, integer subtraction, truncating and Euclidean division, and the
two casts. -/
inductive AFn | lit (k : Nat) | add | subN | subZ | divT | divE | castNZ | castZN
  deriving DecidableEq

/-- The stored relation symbol `<`. -/
inductive ARel | lt
  deriving DecidableEq

/-- Arities of `AFn`. -/
def AFn.arity : AFn → Nat
  | .lit _ => 0
  | .castNZ => 1
  | .castZN => 1
  | _ => 2

/-- The stored-statement signature. -/
abbrev ASig : Sig := ⟨AFn, ARel, AFn.arity, fun _ => 2⟩

/-- The intended structure on `Int`; natural-number values are the
nonnegative integers. -/
def intStr : Str ASig Int where
  fn := fun f => match f with
    | .lit k => fun _ => (k : Int)
    | .add => fun a => a ⟨0, by decide⟩ + a ⟨1, by decide⟩
    | .subN => fun a => if a ⟨1, by decide⟩ ≤ a ⟨0, by decide⟩ then a ⟨0, by decide⟩ - a ⟨1, by decide⟩ else 0
    | .subZ => fun a => a ⟨0, by decide⟩ - a ⟨1, by decide⟩
    | .divT => fun a => Int.tdiv (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | .divE => fun a => Int.ediv (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | .castNZ => fun a => a ⟨0, by decide⟩
    | .castZN => fun a => if 0 ≤ a ⟨0, by decide⟩ then a ⟨0, by decide⟩ else 0
  rel := fun r => match r with
    | .lt => fun a => a ⟨0, by decide⟩ < a ⟨1, by decide⟩

/-- Elaboration environment. Each list is in priority order (first match wins);
extending an environment prepends entries, as a later declaration with higher
priority would. -/
structure Env where
  defaults : List Ty
  coercions : List (Ty × Ty)
  instances : List (Op × Ty × AFn)

/-- Surface numeric expressions. -/
inductive Stx
  | num : Nat → Stx
  | numAt : Nat → Ty → Stx
  | bin : Op → Stx → Stx → Stx

/-- Displayed statements: `a < b`. -/
inductive Disp
  | lt : Stx → Stx → Disp

/-- Type ascriptions occurring in an expression. -/
def Stx.annots : Stx → List Ty
  | .num _ => []
  | .numAt _ t => [t]
  | .bin _ a b => a.annots ++ b.annots

/-- Join two types using the first applicable coercion. -/
def Env.joinTy (e : Env) (t u : Ty) : Option Ty :=
  if t = u then some t else
  match e.coercions.find? (fun c => (c.1 == t && c.2 == u) || (c.1 == u && c.2 == t)) with
  | some c => some c.2
  | none => none

/-- Join a list of types. -/
def Env.joinAll (e : Env) : Ty → List Ty → Option Ty
  | acc, [] => some acc
  | acc, u :: us => match e.joinTy acc u with
    | some t => e.joinAll t us
    | none => none

/-- The type at which a whole arithmetic tree is elaborated: the join of its
ascriptions, or the default numeral type if there are none. -/
def Env.treeTy (e : Env) : List Ty → Option Ty
  | [] => e.defaults.head?
  | t :: ts => e.joinAll t ts

/-- The stored cast symbol for a coercion. -/
def castSym : Ty → Ty → Option AFn
  | .nat, .int => some .castNZ
  | .int, .nat => some .castZN
  | _, _ => none

/-- Numeral term. -/
def lit {n : Nat} (k : Nat) : Term ASig n := .app (AFn.lit k) (fun i => i.elim0)

/-- Unary application. -/
def app1 {n : Nat} (f : AFn) (x : Term ASig n) : Term ASig n := .app f (fun _ => x)

/-- Binary application. -/
def app2 {n : Nat} (f : AFn) (x y : Term ASig n) : Term ASig n :=
  .app f (fun j => if j.val = 0 then x else y)

/-- Insert a coercion at a leaf, if needed and available. -/
def Env.coe (e : Env) (t τ : Ty) (x : Term ASig 0) : Option (Term ASig 0) :=
  if t = τ then some x
  else if (t, τ) ∈ e.coercions then (castSym t τ).map (fun f => app1 f x) else none

/-- Resolve an operator at a type through the first matching instance. -/
def Env.lookupInst (e : Env) (op : Op) (τ : Ty) : Option AFn :=
  (e.instances.find? (fun i => i.1 == op && i.2.1 == τ)).map (fun i => i.2.2)

/-- Elaborate an expression at a fixed type, coercing leaves. -/
def Env.elabAt (e : Env) (τ : Ty) : Stx → Option (Term ASig 0)
  | .num k => some (lit k)
  | .numAt k t => e.coe t τ (lit k)
  | .bin op a b =>
    match e.lookupInst op τ, e.elabAt τ a, e.elabAt τ b with
    | some f, some x, some y => some (app2 f x y)
    | _, _, _ => none

/-- Elaborate a displayed statement to a stored sentence. -/
def Env.elab (e : Env) : Disp → Option (Sentence ASig)
  | .lt a b =>
    match e.treeTy (a.annots ++ b.annots) with
    | none => none
    | some τ =>
      match e.elabAt τ a, e.elabAt τ b with
      | some x, some y => some (.rel ARel.lt (fun j => if j.val = 0 then x else y))
      | _, _ => none

/-- `e'` extends `e`: each list gains entries in front (higher priority);
nothing is removed. -/
def Env.Extends (e' e : Env) : Prop :=
  ∃ ds cs is, e' = ⟨ds ++ e.defaults, cs ++ e.coercions, is ++ e.instances⟩

/-- Elaboration is invariant on `D`: every displayed string in `D` elaborates to
the same stored sentence before and after, or fails in both. This relation is
symmetric in `e` and `e'`. -/
def ElabInvariantOn (e e' : Env) (D : List Disp) : Prop :=
  ∀ s ∈ D, e.elab s = e'.elab s

/-- Directional preservation: every displayed string in `D` that elaborates
under `e` elaborates to the same stored sentence under `e'`. Strings that fail
under `e` are unconstrained. -/
def ElabPreservesAccepted (e e' : Env) (D : List Disp) : Prop :=
  ∀ s ∈ D, ∀ φ, e.elab s = some φ → e'.elab s = some φ

/-- Re-elaborate every displayed string and compare the results. -/
def elabInvariantCheck (e e' : Env) (D : List Disp) : Bool :=
  D.all (fun s => decide (e.elab s = e'.elab s))

/-- Re-elaborate every displayed string accepted under `e` and compare. -/
def elabPreservesCheck (e e' : Env) (D : List Disp) : Bool :=
  D.all fun s => match e.elab s with
    | none => true
    | some φ => decide (e'.elab s = some φ)

/-- `ElabInvariantOn` is symmetric in the two environments. -/
theorem elabInvariantOn_symm (e e' : Env) (D : List Disp) :
    ElabInvariantOn e e' D ↔ ElabInvariantOn e' e D :=
  ⟨fun h s hs => (h s hs).symm, fun h s hs => (h s hs).symm⟩

/-- Invariance implies directional preservation. -/
theorem elabInvariantOn_preservesAccepted (e e' : Env) (D : List Disp)
    (h : ElabInvariantOn e e' D) : ElabPreservesAccepted e e' D :=
  fun s hs _ hφ => (h s hs) ▸ hφ

/-! ### Environments and displayed strings used in the countermodels -/

/-- Base environment: default numerals are natural numbers; the only
coercion is `int → nat`; `/` on both types is truncating division. -/
def baseEnv : Env where
  defaults := [.nat]
  coercions := [(.int, .nat)]
  instances := [(.add, .nat, .add), (.add, .int, .add), (.sub, .nat, .subN),
    (.sub, .int, .subZ), (.div, .nat, .divT), (.div, .int, .divT)]

/-- Changed default numeral type: integers. -/
def envDefaultInt : Env := { baseEnv with defaults := .int :: baseEnv.defaults }

/-- New, higher-priority coercion `nat → int`. -/
def envCoeNatInt : Env := { baseEnv with coercions := (.nat, .int) :: baseEnv.coercions }

/-- New, higher-priority instance: `/` on integers is Euclidean division. -/
def envDivE : Env := { baseEnv with instances := (.div, .int, .divE) :: baseEnv.instances }

/-- `0 - 1 < 0` (unannotated numerals). -/
def sDefault : Disp := .lt (.bin .sub (.num 0) (.num 1)) (.num 0)

/-- `(0 : nat) - (1 : nat) < (0 : int)`. -/
def sCoe : Disp := .lt (.bin .sub (.numAt 0 .nat) (.numAt 1 .nat)) (.numAt 0 .int)

/-- `((0 : int) - (7 : int)) / (2 : int) + (3 : int) < (0 : int)`. -/
def sDiv : Disp :=
  .lt (.bin .add (.bin .div (.bin .sub (.numAt 0 .int) (.numAt 7 .int)) (.numAt 2 .int)) (.numAt 3 .int))
    (.numAt 0 .int)

/-- `(1 : nat) - (0 : nat) < (2 : int)`. -/
def sHarmless : Disp := .lt (.bin .sub (.numAt 1 .nat) (.numAt 0 .nat)) (.numAt 2 .int)

/-! ### Examples of the definitions -/

/-- Positive example (`Env.Extends`): each modified environment extends the base. -/
theorem envs_extend_base :
    envDefaultInt.Extends baseEnv ∧ envCoeNatInt.Extends baseEnv ∧ envDivE.Extends baseEnv :=
  ⟨⟨[.int], [], [], rfl⟩, ⟨[], [(.nat, .int)], [], rfl⟩, ⟨[], [], [(.div, .int, .divE)], rfl⟩⟩

/-- Negative example (`Env.Extends`): removing the only coercion is not an extension. -/
theorem drop_coercion_not_extends : ¬ ({ baseEnv with coercions := [] } : Env).Extends baseEnv := by
  rintro ⟨ds, cs, is, h⟩
  have := congrArg (fun e : Env => e.coercions.length) h
  simp [baseEnv] at this

/-- Positive example (`ElabInvariantOn`, `elabInvariantCheck`): changing the
default numeral type does not affect fully annotated strings. -/
theorem default_change_invariant_on_annotated :
    elabInvariantCheck baseEnv envDefaultInt [sCoe, sDiv] = true := by decide

/-- Negative example (`ElabInvariantOn`, `elabInvariantCheck`): it does affect
`0 - 1 < 0`. -/
theorem default_change_not_invariant_on_unannotated :
    elabInvariantCheck baseEnv envDefaultInt [sDefault] = false := by decide

/-- Positive and negative example (`ElabPreservesAccepted`, `elabPreservesCheck`):
the default-type change preserves the accepted annotated strings and does not
preserve `0 - 1 < 0`. -/
theorem default_change_preserves_examples :
    elabPreservesCheck baseEnv envDefaultInt [sCoe, sDiv] = true ∧
    elabPreservesCheck baseEnv envDefaultInt [sDefault] = false := by decide

/-! ### Text-level countermodels -/

/-- **Main result (counterexample; default numeral type).** Changing the default numeral type
from `nat` to `int` changes the stored reading of the old string `0 - 1 < 0`
from a false sentence (truncated subtraction) to a true one. -/
theorem default_numeral_change_flips_truth :
    envDefaultInt.Extends baseEnv ∧
    ∃ φ φ', baseEnv.elab sDefault = some φ ∧ envDefaultInt.elab sDefault = some φ' ∧
      ¬ intStr.Models φ ∧ intStr.Models φ' := by
  refine ⟨envs_extend_base.1, _, _, rfl, rfl, ?_, ?_⟩
  · show ¬ ((0 : Int) < 0); decide
  · show ((-1 : Int) < 0); decide

/-- **Main result (counterexample; coercion).** Adding a higher-priority coercion `nat → int`
changes the stored reading of the old string `(0 : nat) - (1 : nat) < (0 : int)`
from a false sentence (computed in `nat`) to a true one (computed in `int`). -/
theorem new_coercion_flips_truth :
    envCoeNatInt.Extends baseEnv ∧
    ∃ φ φ', baseEnv.elab sCoe = some φ ∧ envCoeNatInt.elab sCoe = some φ' ∧
      ¬ intStr.Models φ ∧ intStr.Models φ' := by
  refine ⟨envs_extend_base.2.1, _, _, rfl, rfl, ?_, ?_⟩
  · show ¬ ((0 : Int) < 0); decide
  · show ((-1 : Int) < 0); decide

/-- **Main result (counterexample; instance).** Adding a higher-priority
instance making `/` on `int` Euclidean changes the stored reading of the old
string `((0 : int) - (7 : int)) / (2 : int) + (3 : int) < (0 : int)` from a
false sentence (`-7 / 2 = -3`, truncating) to a true one (`-7 / 2 = -4`,
Euclidean). -/
theorem new_instance_flips_truth :
    envDivE.Extends baseEnv ∧
    ∃ φ φ', baseEnv.elab sDiv = some φ ∧ envDivE.elab sDiv = some φ' ∧
      ¬ intStr.Models φ ∧ intStr.Models φ' := by
  refine ⟨envs_extend_base.2.2, _, _, rfl, rfl, ?_, ?_⟩
  · show ¬ ((0 : Int) < 0); decide
  · show ((-1 : Int) < 0); decide

/-- A changed elaboration need not change the truth value: with the new
coercion, `(1 : nat) - (0 : nat) < (2 : int)` elaborates to a different stored
sentence with the same truth value. So failing `ElabInvariantOn` does not by
itself show that the truth of a displayed string changed. -/
theorem elab_change_without_truth_change :
    ∃ φ φ', baseEnv.elab sHarmless = some φ ∧ envCoeNatInt.elab sHarmless = some φ' ∧
      φ ≠ φ' ∧ intStr.Models φ ∧ intStr.Models φ' := by
  refine ⟨_, _, rfl, rfl, by decide, ?_, ?_⟩
  · show ((1 : Int) < 2); decide
  · show ((1 : Int) < 2); decide

/-! ### A coercion-adding extension that preserves every accepted string -/

/-- A base environment without coercions. -/
def envNoCoe : Env where
  defaults := [.nat]
  coercions := []
  instances := baseEnv.instances

/-- Its extension by the coercion `nat → int`. -/
def envAddNatInt : Env := { envNoCoe with coercions := [(.nat, .int)] }

theorem joinAll_envNoCoe {τ : Ty} :
    ∀ {acc : Ty} {ts : List Ty}, envNoCoe.joinAll acc ts = some τ →
      acc = τ ∧ ∀ u ∈ ts, u = τ
  | acc, [], h => by
    injection h with h'; subst h'; exact ⟨rfl, fun _ hm => nomatch hm⟩
  | acc, u :: us, h => by
    unfold Env.joinAll Env.joinTy at h
    by_cases heq : acc = u
    · subst heq
      simp only [↓reduceIte] at h
      obtain ⟨rfl, hus⟩ := joinAll_envNoCoe h
      exact ⟨rfl, fun x hx => by cases hx with | head => rfl | tail _ hx => exact hus x hx⟩
    · simp [heq, envNoCoe] at h

theorem joinAll_same (e : Env) (t : Ty) :
    ∀ ts : List Ty, (∀ u ∈ ts, u = t) → e.joinAll t ts = some t
  | [], _ => rfl
  | u :: us, h => by
    have hu : u = t := h u (.head _)
    subst hu
    simp only [Env.joinAll, Env.joinTy, ↓reduceIte]
    exact joinAll_same e u us (fun x hx => h x (.tail _ hx))

theorem elabAt_envNoCoe_to_envAddNatInt (τ : Ty) :
    ∀ (a : Stx) (t : Term ASig 0), envNoCoe.elabAt τ a = some t → envAddNatInt.elabAt τ a = some t
  | .num _, _, h => h
  | .numAt k u, t, h => by
    unfold Env.elabAt Env.coe at h ⊢
    by_cases heq : u = τ
    · simp [heq] at h ⊢; exact h
    · simp [heq, envNoCoe] at h
  | .bin op a b, t, h => by
    dsimp [Env.elabAt] at h ⊢
    cases hi : envNoCoe.lookupInst op τ with
    | none => simp [hi] at h
    | some f =>
      cases ha : envNoCoe.elabAt τ a with
      | none => simp [hi, ha] at h
      | some x =>
        cases hb : envNoCoe.elabAt τ b with
        | none => simp [hi, ha, hb] at h
        | some y =>
          simp only [hi, ha, hb] at h
          have hi' : envAddNatInt.lookupInst op τ = some f := hi
          have ha' := elabAt_envNoCoe_to_envAddNatInt τ a x ha
          have hb' := elabAt_envNoCoe_to_envAddNatInt τ b y hb
          simp [hi', ha', hb', h]

theorem treeTy_envNoCoe_to_envAddNatInt :
    ∀ (l : List Ty) (τ : Ty), envNoCoe.treeTy l = some τ → envAddNatInt.treeTy l = some τ
  | [], _, h => h
  | t :: ts, _, h => by
    obtain ⟨rfl, hts⟩ := joinAll_envNoCoe h
    exact joinAll_same envAddNatInt t ts hts

/-- Adding the coercion `nat → int` to `envNoCoe` is an extension that preserves
every displayed string accepted before, across the whole surface language;
yet it is not elaboration-invariant on `[sCoe]`, because `sCoe` is rejected
before and accepted after. -/
theorem additive_coercion_preserves_but_not_invariant :
    envAddNatInt.Extends envNoCoe ∧
    (∀ (s : Disp) (φ : Sentence ASig), envNoCoe.elab s = some φ → envAddNatInt.elab s = some φ) ∧
    envNoCoe.elab sCoe = none ∧ (envAddNatInt.elab sCoe).isSome = true ∧
    ¬ ElabInvariantOn envNoCoe envAddNatInt [sCoe] ∧
    ElabPreservesAccepted envNoCoe envAddNatInt [sCoe] := by
  have hpres : ∀ (s : Disp) (φ : Sentence ASig), envNoCoe.elab s = some φ →
      envAddNatInt.elab s = some φ := by
    rintro ⟨a, b⟩ φ h
    change (match envNoCoe.treeTy (a.annots ++ b.annots) with
      | none => none
      | some τ => match envNoCoe.elabAt τ a, envNoCoe.elabAt τ b with
        | some x, some y => some (Formula.rel ARel.lt fun j => if j.val = 0 then x else y)
        | _, _ => none) = some φ at h
    change (match envAddNatInt.treeTy (a.annots ++ b.annots) with
      | none => none
      | some τ => match envAddNatInt.elabAt τ a, envAddNatInt.elabAt τ b with
        | some x, some y => some (Formula.rel ARel.lt fun j => if j.val = 0 then x else y)
        | _, _ => none) = some φ
    cases hty : envNoCoe.treeTy (a.annots ++ b.annots) with
    | none => rw [hty] at h; cases h
    | some τ =>
      rw [hty] at h
      rw [treeTy_envNoCoe_to_envAddNatInt _ τ hty]
      dsimp only at h ⊢
      cases ha : envNoCoe.elabAt τ a with
      | none => rw [ha] at h; cases h
      | some x =>
        cases hb : envNoCoe.elabAt τ b with
        | none => rw [ha, hb] at h; cases h
        | some y =>
          rw [ha, hb] at h
          rw [elabAt_envNoCoe_to_envAddNatInt τ a x ha, elabAt_envNoCoe_to_envAddNatInt τ b y hb]
          exact h
  refine ⟨⟨[], [(.nat, .int)], [], rfl⟩, hpres, by decide, by decide, fun h => ?_,
    fun s _ φ hφ => hpres s φ hφ⟩
  have h' := h sCoe (.head _)
  exact absurd h' (by decide)

/-! ### Deciding preservation and invariance by re-elaboration -/

/-- **Main result (reference point; definitional).** For every pair of
environments and every finite list of displayed strings: re-elaborating the
strings accepted under `e` and comparing decides directional preservation, and
re-elaborating all strings and comparing decides invariance. -/
theorem elabPreservesCheck_iff_elabPreservesAccepted (e e' : Env) (D : List Disp) :
    elabPreservesCheck e e' D = true ↔ ElabPreservesAccepted e e' D := by
  simp only [elabPreservesCheck, ElabPreservesAccepted, List.all_eq_true]
  refine forall_congr' fun s => imp_congr_right fun _ => ?_
  cases e.elab s <;> simp

/-- Companion of `elabPreservesCheck_iff_elabPreservesAccepted` for invariance. -/
theorem elabInvariantCheck_iff_elabInvariantOn (e e' : Env) (D : List Disp) :
    elabInvariantCheck e e' D = true ↔ ElabInvariantOn e e' D := by
  simp [elabInvariantCheck, ElabInvariantOn]

end Toy.Extension
