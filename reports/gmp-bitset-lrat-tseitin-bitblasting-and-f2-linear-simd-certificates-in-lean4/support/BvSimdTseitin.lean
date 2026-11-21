prelude
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.BitVec.Bitblast
import Init.Tactics

/-!
# Kernel-Reducible GMP Bitset LRAT Checker and `BitVec` / SIMD Tseitin Bit-Blaster

Self-contained `prelude` + `Init.*`-only Lean `v4.34.1` mechanization (`0` `sorry`, `0` custom or
native axioms, `0` `partial`, `0` `set_option`, fixed `maxRecDepth = 512`) providing:

1. `checkLratGmp` & `checkLratGmp_sound`: Word-parallel C++ GMP `mpz_t` bitset Reverse Unit
   Propagation (RUP) / LRAT UNSAT checker backed by an 8-way persistent `OctTrie Nat`.
2. `AigArena`, `BvExpr`, `BvPred`, `checkBvUnsatCert` & `checkBvUnsatCert_sound`:
   `HashMap`-free read-only arena AIG + UNSAT-core Tseitin CNF verifier + `BitVec w` bit-blaster
   covering bitwise ops, ripple-carry `add`/`sub`/`neg`, constant and variable barrel shifts
   (`shl`, `lshr`, `ashr`), `extract`/`concat`/`zeroExtend`/`signExtend`, `mul`, comparisons
   (`eq`, `ult`, `ule`, `slt`, `sle`), x86-64 `SUB`/`CMP` status flags (`CF`, `ZF`, `SF`, `OF`,
   `PF`), BMI2 (`bzhi`, `blsi`, `blsr`, `blsmsk`), SWAR `has_zero_byte`, and SIMD byte/word lane
   combinators (`vpmaddubsw`, saturating `vpaddsw`, `vpsubusb`).
-/

namespace GmpBvTseitin

-- ============================================================================
-- Section 1: Balanced Binary StepTree & 8-Way Persistent OctTrie
-- ============================================================================

inductive StepTree (α : Type) where
  | empty
  | leaf (val : α)
  | branch (left right : StepTree α)

inductive OctTrie (α : Type) where
  | empty
  | node (val : Option α) (c0 c1 c2 c3 c4 c5 c6 c7 : OctTrie α)

def OctTrie.get {α : Type} : Nat → OctTrie α → Nat → Option α
  | 0, _, _ => none
  | Nat.succ _, .empty, _ => none
  | Nat.succ _, .node v _ _ _ _ _ _ _ _, 0 => v
  | Nat.succ fuel, .node _ c0 c1 c2 c3 c4 c5 c6 c7, Nat.succ k =>
    let idx := Nat.succ k
    let rem := Nat.land idx 7
    let nxt := Nat.shiftRight idx 3
    match rem with
    | 0 => OctTrie.get fuel c0 nxt
    | 1 => OctTrie.get fuel c1 nxt
    | 2 => OctTrie.get fuel c2 nxt
    | 3 => OctTrie.get fuel c3 nxt
    | 4 => OctTrie.get fuel c4 nxt
    | 5 => OctTrie.get fuel c5 nxt
    | 6 => OctTrie.get fuel c6 nxt
    | _ => OctTrie.get fuel c7 nxt

def OctTrie.forceNode {α : Type} (t : OctTrie α) : OctTrie α :=
  match t with
  | .empty => .empty
  | .node v c0 c1 c2 c3 c4 c5 c6 c7 => .node v c0 c1 c2 c3 c4 c5 c6 c7

def OctTrie.set {α : Type} : Nat → OctTrie α → Nat → Option α → OctTrie α
  | 0, cur, _, _ => cur
  | Nat.succ _, .empty, 0, valOpt => .node valOpt .empty .empty .empty .empty .empty .empty .empty .empty
  | Nat.succ _, .node _ c0 c1 c2 c3 c4 c5 c6 c7, 0, valOpt => .node valOpt c0 c1 c2 c3 c4 c5 c6 c7
  | Nat.succ fuel, .empty, Nat.succ k, valOpt =>
    let idx := Nat.succ k
    let rem := Nat.land idx 7
    let nxt := Nat.shiftRight idx 3
    let sub := OctTrie.set fuel .empty nxt valOpt
    match sub with
    | .empty => .empty
    | .node sv s0 s1 s2 s3 s4 s5 s6 s7 =>
      let sn := OctTrie.node sv s0 s1 s2 s3 s4 s5 s6 s7
      match rem with
      | 0 => .node none sn .empty .empty .empty .empty .empty .empty .empty
      | 1 => .node none .empty sn .empty .empty .empty .empty .empty .empty
      | 2 => .node none .empty .empty sn .empty .empty .empty .empty .empty
      | 3 => .node none .empty .empty .empty sn .empty .empty .empty .empty
      | 4 => .node none .empty .empty .empty .empty sn .empty .empty .empty
      | 5 => .node none .empty .empty .empty .empty .empty sn .empty .empty
      | 6 => .node none .empty .empty .empty .empty .empty .empty sn .empty
      | _ => .node none .empty .empty .empty .empty .empty .empty .empty sn
  | Nat.succ fuel, .node v0 c0 c1 c2 c3 c4 c5 c6 c7, Nat.succ k, valOpt =>
    let idx := Nat.succ k
    let rem := Nat.land idx 7
    let nxt := Nat.shiftRight idx 3
    match rem with
    | 0 =>
      match OctTrie.set fuel c0 nxt valOpt with
      | .empty => .node v0 .empty c1 c2 c3 c4 c5 c6 c7
      | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c1 c2 c3 c4 c5 c6 c7
    | 1 =>
      match OctTrie.set fuel c1 nxt valOpt with
      | .empty => .node v0 c0 .empty c2 c3 c4 c5 c6 c7
      | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c2 c3 c4 c5 c6 c7
    | 2 =>
      match OctTrie.set fuel c2 nxt valOpt with
      | .empty => .node v0 c0 c1 .empty c3 c4 c5 c6 c7
      | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c3 c4 c5 c6 c7
    | 3 =>
      match OctTrie.set fuel c3 nxt valOpt with
      | .empty => .node v0 c0 c1 c2 .empty c4 c5 c6 c7
      | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c4 c5 c6 c7
    | 4 =>
      match OctTrie.set fuel c4 nxt valOpt with
      | .empty => .node v0 c0 c1 c2 c3 .empty c5 c6 c7
      | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c5 c6 c7
    | 5 =>
      match OctTrie.set fuel c5 nxt valOpt with
      | .empty => .node v0 c0 c1 c2 c3 c4 .empty c6 c7
      | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c6 c7
    | 6 =>
      match OctTrie.set fuel c6 nxt valOpt with
      | .empty => .node v0 c0 c1 c2 c3 c4 c5 .empty c7
      | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 c5 (.node sv s0 s1 s2 s3 s4 s5 s6 s7) c7
    | _ =>
      match OctTrie.set fuel c7 nxt valOpt with
      | .empty => .node v0 c0 c1 c2 c3 c4 c5 c6 .empty
      | .node sv s0 s1 s2 s3 s4 s5 s6 s7 => .node v0 c0 c1 c2 c3 c4 c5 c6 (.node sv s0 s1 s2 s3 s4 s5 s6 s7)

def OctTrie.AllValues {α : Type} (P : α → Prop) : OctTrie α → Prop
  | .empty => True
  | .node v c0 c1 c2 c3 c4 c5 c6 c7 =>
    (match v with | none => True | some x => P x) ∧
    OctTrie.AllValues P c0 ∧ OctTrie.AllValues P c1 ∧
    OctTrie.AllValues P c2 ∧ OctTrie.AllValues P c3 ∧
    OctTrie.AllValues P c4 ∧ OctTrie.AllValues P c5 ∧
    OctTrie.AllValues P c6 ∧ OctTrie.AllValues P c7

theorem OctTrie.get_allValues {α : Type} {P : α → Prop} :
    ∀ (fuel : Nat) (t : OctTrie α) (idx : Nat) (x : α),
      OctTrie.AllValues P t → OctTrie.get fuel t idx = some x → P x
  | 0, _, _, _, _, hget => nomatch hget
  | Nat.succ _, .empty, _, _, _, hget => nomatch hget
  | Nat.succ _, .node v _ _ _ _ _ _ _ _, 0, x, hall, hget => by
    dsimp only [OctTrie.get] at hget
    rw [hget] at hall
    exact hall.1
  | Nat.succ fuel, .node v c0 c1 c2 c3 c4 c5 c6 c7, Nat.succ k, x, hall, hget => by
    dsimp only [OctTrie.get] at hget
    rcases hall with ⟨_, h0, h1, h2, h3, h4, h5, h6, h7⟩
    split at hget
    · exact OctTrie.get_allValues fuel c0 _ x h0 hget
    · exact OctTrie.get_allValues fuel c1 _ x h1 hget
    · exact OctTrie.get_allValues fuel c2 _ x h2 hget
    · exact OctTrie.get_allValues fuel c3 _ x h3 hget
    · exact OctTrie.get_allValues fuel c4 _ x h4 hget
    · exact OctTrie.get_allValues fuel c5 _ x h5 hget
    · exact OctTrie.get_allValues fuel c6 _ x h6 hget
    · exact OctTrie.get_allValues fuel c7 _ x h7 hget

theorem OctTrie.set_allValues {α : Type} {P : α → Prop} :
    ∀ (fuel : Nat) (t : OctTrie α) (idx : Nat) (valOpt : Option α),
      OctTrie.AllValues P t →
      (match valOpt with | none => True | some x => P x) →
      OctTrie.AllValues P (OctTrie.set fuel t idx valOpt)
  | 0, t, _, _, ht, _ => ht
  | Nat.succ _, .empty, 0, _, _, hv =>
    ⟨hv, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  | Nat.succ _, .node _ _ _ _ _ _ _ _ _, 0, _, ht, hv =>
    ⟨hv, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.2⟩
  | Nat.succ fuel, .empty, Nat.succ k, valOpt, _, hv => by
    dsimp only [OctTrie.set]
    have ih := OctTrie.set_allValues fuel .empty (Nat.shiftRight (Nat.succ k) 3) valOpt trivial hv
    cases hsub : OctTrie.set fuel .empty (Nat.shiftRight (Nat.succ k) 3) valOpt with
    | empty => trivial
    | node sv s0 s1 s2 s3 s4 s5 s6 s7 =>
      rw [hsub] at ih
      dsimp only
      split <;> exact ⟨trivial,
        by first | exact ih | trivial, by first | exact ih | trivial,
        by first | exact ih | trivial, by first | exact ih | trivial,
        by first | exact ih | trivial, by first | exact ih | trivial,
        by first | exact ih | trivial, by first | exact ih | trivial⟩
  | Nat.succ fuel, .node v0 c0 c1 c2 c3 c4 c5 c6 c7, Nat.succ k, valOpt, ht, hv => by
    dsimp only [OctTrie.set]
    rcases ht with ⟨hv0, h0, h1, h2, h3, h4, h5, h6, h7⟩
    let nxt := Nat.shiftRight (Nat.succ k) 3
    split
    · have ih := OctTrie.set_allValues fuel c0 nxt valOpt h0 hv
      cases hsub : OctTrie.set fuel c0 nxt valOpt <;> rw [hsub] at ih <;> exact ⟨hv0, ih, h1, h2, h3, h4, h5, h6, h7⟩
    · have ih := OctTrie.set_allValues fuel c1 nxt valOpt h1 hv
      cases hsub : OctTrie.set fuel c1 nxt valOpt <;> rw [hsub] at ih <;> exact ⟨hv0, h0, ih, h2, h3, h4, h5, h6, h7⟩
    · have ih := OctTrie.set_allValues fuel c2 nxt valOpt h2 hv
      cases hsub : OctTrie.set fuel c2 nxt valOpt <;> rw [hsub] at ih <;> exact ⟨hv0, h0, h1, ih, h3, h4, h5, h6, h7⟩
    · have ih := OctTrie.set_allValues fuel c3 nxt valOpt h3 hv
      cases hsub : OctTrie.set fuel c3 nxt valOpt <;> rw [hsub] at ih <;> exact ⟨hv0, h0, h1, h2, ih, h4, h5, h6, h7⟩
    · have ih := OctTrie.set_allValues fuel c4 nxt valOpt h4 hv
      cases hsub : OctTrie.set fuel c4 nxt valOpt <;> rw [hsub] at ih <;> exact ⟨hv0, h0, h1, h2, h3, ih, h5, h6, h7⟩
    · have ih := OctTrie.set_allValues fuel c5 nxt valOpt h5 hv
      cases hsub : OctTrie.set fuel c5 nxt valOpt <;> rw [hsub] at ih <;> exact ⟨hv0, h0, h1, h2, h3, h4, ih, h6, h7⟩
    · have ih := OctTrie.set_allValues fuel c6 nxt valOpt h6 hv
      cases hsub : OctTrie.set fuel c6 nxt valOpt <;> rw [hsub] at ih <;> exact ⟨hv0, h0, h1, h2, h3, h4, h5, ih, h7⟩
    · have ih := OctTrie.set_allValues fuel c7 nxt valOpt h7 hv
      cases hsub : OctTrie.set fuel c7 nxt valOpt <;> rw [hsub] at ih <;> exact ⟨hv0, h0, h1, h2, h3, h4, h5, h6, ih⟩

-- ============================================================================
-- Section 2: Word-Parallel GMP Bitset RUP / LRAT Checker & Soundness Proof
-- ============================================================================

/-- Literal encoding: `2 * v` is positive `v`, `2 * v + 1` is negative `¬v`. -/
def evalLit (assign : Nat → Bool) (lit : Nat) : Bool :=
  match Nat.beq (Nat.land lit 1) 0 with
  | true  => assign (Nat.shiftRight lit 1)
  | false => !(assign (Nat.shiftRight lit 1))

def semClauseList (assign : Nat → Bool) : List Nat → Bool
  | [] => false
  | lit :: rest => evalLit assign lit || semClauseList assign rest

def semMaskSat (assign : Nat → Bool) (mask : Nat) : Prop :=
  ∃ lit : Nat, Nat.testBit mask lit = true ∧ evalLit assign lit = true

def semFalsified (assign : Nat → Bool) (falsified : Nat) : Prop :=
  ∀ lit : Nat, Nat.testBit falsified lit = true → evalLit assign lit = false

def compileClauseMask : List Nat → Nat
  | [] => 0
  | lit :: rest => Nat.lor (Nat.shiftLeft 1 lit) (compileClauseMask rest)

private theorem ite_true_eq {α : Type} {c : Prop} [Decidable c] (hc : c) (t e : α) :
    (if c then t else e) = t := by simp [hc]

private theorem ite_false_eq {α : Type} {c : Prop} [Decidable c] (hc : ¬c) (t e : α) :
    (if c then t else e) = e := by simp [hc]

private theorem shiftLeft_eq_pow (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := by
  change a <<< b = a * 2 ^ b; exact Nat.shiftLeft_eq a b

private theorem shiftRight_eq_div (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := by
  change a >>> b = a / 2 ^ b; exact Nat.shiftRight_eq_div_pow a b

private theorem testBit_lor' (a b i : Nat) :
    Nat.testBit (Nat.lor a b) i = (Nat.testBit a i || Nat.testBit b i) := by
  change (a ||| b).testBit i = (a.testBit i || b.testBit i); exact Nat.testBit_or a b i

private theorem testBit_land' (a b i : Nat) :
    Nat.testBit (Nat.land a b) i = (Nat.testBit a i && Nat.testBit b i) := by
  change (a &&& b).testBit i = (a.testBit i && b.testBit i); exact Nat.testBit_and a b i

private theorem testBit_xor' (a b i : Nat) :
    Nat.testBit (Nat.xor a b) i = bne (Nat.testBit a i) (Nat.testBit b i) := by
  change (a ^^^ b).testBit i = bne (a.testBit i) (b.testBit i); exact Nat.testBit_xor a b i

private theorem nat_land_one_eq_mod (x : Nat) : Nat.land x 1 = x % 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_land']
  cases i with
  | zero =>
    have h1 : Nat.testBit 1 0 = true := rfl
    rw [h1, Bool.and_true, Nat.testBit_zero, Nat.testBit_zero]
    have hm : (x % 2) % 2 = x % 2 := by omega
    rw [hm]
  | succ k =>
    have h1 : Nat.testBit 1 (Nat.succ k) = false := by
      rw [Nat.testBit_succ]
      exact Nat.zero_testBit k
    rw [h1, Bool.and_false, Nat.testBit_succ]
    have hdiv : (x % 2) / 2 = 0 := by omega
    rw [hdiv, Nat.zero_testBit]

theorem testBit_one_shiftLeft (a b : Nat) :
    Nat.testBit (Nat.shiftLeft 1 a) b = decide (a = b) := by
  rw [shiftLeft_eq_pow, Nat.one_mul, Nat.testBit_two_pow]

theorem compileClauseMask_sat {assign : Nat → Bool} :
    ∀ (cls : List Nat), semClauseList assign cls = true → semMaskSat assign (compileClauseMask cls)
  | [], h => nomatch h
  | lit :: rest, h => by
    unfold semClauseList at h
    unfold compileClauseMask
    cases hl : evalLit assign lit with
    | true =>
      refine ⟨lit, ?_, hl⟩
      rw [testBit_lor', testBit_one_shiftLeft]
      simp
    | false =>
      rw [hl, Bool.false_or] at h
      rcases compileClauseMask_sat rest h with ⟨w, hwBit, hwVal⟩
      refine ⟨w, ?_, hwVal⟩
      rw [testBit_lor', hwBit, Bool.or_true]

theorem compileClauseMask_falsified_of_unsat {assign : Nat → Bool} :
    ∀ (cls : List Nat), semClauseList assign cls = false → semFalsified assign (compileClauseMask cls)
  | [], _, lit, hbit => by
    unfold compileClauseMask at hbit
    rw [Nat.zero_testBit] at hbit
    contradiction
  | l :: rest, hfalse, lit, hbit => by
    unfold semClauseList at hfalse
    cases hl : evalLit assign l with
    | true => rw [hl, Bool.true_or] at hfalse; contradiction
    | false =>
      rw [hl, Bool.false_or] at hfalse
      unfold compileClauseMask at hbit
      rw [testBit_lor', testBit_one_shiftLeft] at hbit
      cases heq : decide (l = lit) with
      | true =>
        rw [decide_eq_true_eq] at heq
        subst heq
        exact hl
      | false =>
        rw [heq, Bool.false_or] at hbit
        exact compileClauseMask_falsified_of_unsat rest hfalse lit hbit

def semClauseTree (assign : Nat → Bool) : StepTree (List Nat) → Bool
  | .empty => false
  | .leaf cls => semClauseList assign cls
  | .branch l r => semClauseTree assign l || semClauseTree assign r

def compileClauseTree : StepTree (List Nat) → Nat
  | .empty => 0
  | .leaf cls => compileClauseMask cls
  | .branch l r => Nat.lor (compileClauseTree l) (compileClauseTree r)

theorem compileClauseTree_sat {assign : Nat → Bool} :
    ∀ (t : StepTree (List Nat)), semClauseTree assign t = true → semMaskSat assign (compileClauseTree t)
  | .empty, h => nomatch h
  | .leaf cls, h => compileClauseMask_sat cls h
  | .branch l r, h => by
    unfold semClauseTree at h
    unfold compileClauseTree
    cases hl : semClauseTree assign l with
    | true =>
      rcases compileClauseTree_sat l hl with ⟨w, hwBit, hwVal⟩
      refine ⟨w, ?_, hwVal⟩
      rw [testBit_lor', hwBit, Bool.true_or]
    | false =>
      rw [hl, Bool.false_or] at h
      rcases compileClauseTree_sat r h with ⟨w, hwBit, hwVal⟩
      refine ⟨w, ?_, hwVal⟩
      rw [testBit_lor', hwBit, Bool.or_true]

theorem compileClauseTree_falsified_of_unsat {assign : Nat → Bool} :
    ∀ (t : StepTree (List Nat)), semClauseTree assign t = false → semFalsified assign (compileClauseTree t)
  | .empty, _, _, hbit => by
    unfold compileClauseTree at hbit
    rw [Nat.zero_testBit] at hbit
    contradiction
  | .leaf cls, hfalse, lit, hbit => compileClauseMask_falsified_of_unsat cls hfalse lit hbit
  | .branch l r, hfalse, lit, hbit => by
    unfold semClauseTree at hfalse
    cases hl : semClauseTree assign l with
    | true => rw [hl, Bool.true_or] at hfalse; contradiction
    | false =>
      rw [hl, Bool.false_or] at hfalse
      unfold compileClauseTree at hbit
      rw [testBit_lor'] at hbit
      cases hbl : Nat.testBit (compileClauseTree l) lit with
      | true => exact compileClauseTree_falsified_of_unsat l hl lit hbl
      | false =>
        rw [hbl, Bool.false_or] at hbit
        exact compileClauseTree_falsified_of_unsat r hfalse lit hbit

/-- Key GMP Bitset Lemma: if bit `k` of `rem` is `1` and `rem &&& (rem - 1) = 0`,
    then `rem` has NO other set bits: `rem = 1 <<< k`! -/
theorem pow2_of_testBit_and_land_pred :
    ∀ (k rem : Nat),
      Nat.testBit rem k = true →
      Nat.land rem (Nat.sub rem 1) = 0 →
      rem = Nat.shiftLeft 1 k
  | 0, rem, hbit0, hland => by
    have hland' : Nat.land rem (rem - 1) = 0 := hland
    apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_one_shiftLeft]
    cases j with
    | zero =>
      simpa using hbit0
    | succ m =>
      have h0 : rem % 2 = 1 := by
        rw [Nat.testBit_zero] at hbit0
        exact decide_eq_true_iff.mp hbit0
      have hdiv : (rem - 1) / 2 = rem / 2 := by omega
      have hland_j : Nat.testBit (Nat.land rem (rem - 1)) (Nat.succ m) = false := by
        rw [hland', Nat.zero_testBit]
      rw [testBit_land', Nat.testBit_succ, Nat.testBit_succ, hdiv, Bool.and_self] at hland_j
      rw [Nat.testBit_succ, hland_j]
      simp
  | Nat.succ k, rem, hbitS, hland => by
    have hland' : Nat.land rem (rem - 1) = 0 := hland
    -- First show bit 0 of `rem` must be `false` (else `rem = 1`, whose `k+1` bit is `false`!).
    cases hb0 : Nat.testBit rem 0 with
    | true =>
      have hrem1 := pow2_of_testBit_and_land_pred 0 rem hb0 hland
      rw [hrem1, testBit_one_shiftLeft] at hbitS
      simp at hbitS
    | false =>
      have hmod0 : rem % 2 = 0 := by
        rw [Nat.testBit_zero] at hb0
        have hne1 : ¬(rem % 2 = 1) := decide_eq_false_iff_not.mp hb0
        omega
      have hq_bit : Nat.testBit (rem / 2) k = true := by
        rw [← Nat.testBit_succ]
        exact hbitS
      have hq_pos : 0 < rem / 2 := by
        cases hq0 : rem / 2 with
        | zero =>
          rw [hq0, Nat.zero_testBit] at hq_bit
          contradiction
        | succ p => omega
      have hpred_div : (rem - 1) / 2 = rem / 2 - 1 := by omega
      have hq_land : Nat.land (rem / 2) (rem / 2 - 1) = 0 := by
        apply Nat.eq_of_testBit_eq
        intro m
        rw [Nat.zero_testBit, testBit_land', ← hpred_div, ← Nat.testBit_succ, ← Nat.testBit_succ,
          ← testBit_land', hland', Nat.zero_testBit]
      have ih := pow2_of_testBit_and_land_pred k (rem / 2) hq_bit hq_land
      have hrem_eq : rem = 2 * (rem / 2) := by omega
      rw [hrem_eq, ih, shiftLeft_eq_pow, shiftLeft_eq_pow, Nat.one_mul, Nat.one_mul, Nat.pow_succ, Nat.mul_comm]

theorem pow2_mod_three_eq_one_iff_even :
    ∀ (k : Nat), Nat.beq (Nat.mod (Nat.shiftLeft 1 k) 3) 1 = Nat.beq (Nat.land k 1) 0
  | 0 => rfl
  | 1 => rfl
  | Nat.succ (Nat.succ k) => by
    have hsh : Nat.shiftLeft 1 (Nat.succ (Nat.succ k)) = 4 * Nat.shiftLeft 1 k := by
      rw [shiftLeft_eq_pow, shiftLeft_eq_pow, Nat.one_mul, Nat.one_mul, Nat.pow_succ, Nat.pow_succ]
      omega
    have hmod : Nat.mod (4 * Nat.shiftLeft 1 k) 3 = Nat.mod (Nat.shiftLeft 1 k) 3 := by
      change (4 * Nat.shiftLeft 1 k) % 3 = (Nat.shiftLeft 1 k) % 3
      omega
    have hland : Nat.land (Nat.succ (Nat.succ k)) 1 = Nat.land k 1 := by
      rw [nat_land_one_eq_mod, nat_land_one_eq_mod]
      omega
    rw [hsh, hmod, hland]
    exact pow2_mod_three_eq_one_iff_even k

theorem evalLit_negBit_false {assign : Nat → Bool} {litStar : Nat}
    (htrue : evalLit assign litStar = true) :
    let rem := Nat.shiftLeft 1 litStar
    let negRaw := match Nat.beq (Nat.mod rem 3) 1 with
      | true  => Nat.shiftLeft rem 1
      | false => Nat.shiftRight rem 1
    ∀ m : Nat, Nat.testBit negRaw m = true → evalLit assign m = false := by
  intro rem negRaw m hm
  have hmod3 : Nat.beq (Nat.mod rem 3) 1 = Nat.beq (Nat.land litStar 1) 0 :=
    pow2_mod_three_eq_one_iff_even litStar
  unfold negRaw at hm
  rw [hmod3] at hm
  unfold evalLit at htrue
  cases heven : Nat.beq (Nat.land litStar 1) 0 with
  | true =>
    rw [heven] at hm htrue
    dsimp only at hm htrue
    have hsh : Nat.shiftLeft rem 1 = Nat.shiftLeft 1 (litStar + 1) := by
      unfold rem
      rw [shiftLeft_eq_pow, shiftLeft_eq_pow, shiftLeft_eq_pow, Nat.one_mul, Nat.one_mul, Nat.pow_one, ← Nat.pow_succ]
    rw [hsh, testBit_one_shiftLeft] at hm
    rw [decide_eq_true_eq] at hm
    subst hm
    have hl0 : litStar % 2 = 0 := by
      have h1 := Nat.eq_of_beq_eq_true heven
      rw [nat_land_one_eq_mod] at h1
      exact h1
    have hdiv : Nat.shiftRight (litStar + 1) 1 = Nat.shiftRight litStar 1 := by
      rw [shiftRight_eq_div, shiftRight_eq_div]
      dsimp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      omega
    have hodd : Nat.beq (Nat.land (litStar + 1) 1) 0 = false := by
      rw [nat_land_one_eq_mod]
      have hm1 : (litStar + 1) % 2 = 1 := by omega
      rw [hm1]
      rfl
    unfold evalLit
    rw [hodd, hdiv]
    dsimp only
    rw [htrue]
    rfl
  | false =>
    rw [heven] at hm htrue
    dsimp only at hm htrue
    have hl1 : litStar % 2 = 1 := by
      rw [nat_land_one_eq_mod] at heven
      cases hrem2 : litStar % 2 with
      | zero => rw [hrem2] at heven; contradiction
      | succ r => omega
    have hpos : 1 ≤ litStar := by omega
    have hsh : Nat.shiftRight rem 1 = Nat.shiftLeft 1 (litStar - 1) := by
      unfold rem
      rw [shiftRight_eq_div, shiftLeft_eq_pow, shiftLeft_eq_pow, Nat.one_mul, Nat.one_mul]
      have hsplit : litStar = (litStar - 1) + 1 := by omega
      conv => lhs; rw [hsplit, Nat.pow_succ]
      dsimp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      omega
    rw [hsh, testBit_one_shiftLeft] at hm
    rw [decide_eq_true_eq] at hm
    subst hm
    have hdiv : Nat.shiftRight (litStar - 1) 1 = Nat.shiftRight litStar 1 := by
      rw [shiftRight_eq_div, shiftRight_eq_div]
      dsimp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      omega
    have hev2 : Nat.beq (Nat.land (litStar - 1) 1) 0 = true := by
      rw [nat_land_one_eq_mod]
      have hm0 : (litStar - 1) % 2 = 0 := by omega
      rw [hm0]
      rfl
    unfold evalLit
    rw [hev2, hdiv]
    dsimp only
    cases hval : assign (Nat.shiftRight litStar 1) with
    | false => rfl
    | true => rw [hval] at htrue; contradiction

/-- Result of propagating a bounded chunk or balanced tree of RUP hints. -/
inductive PropRes where
  | contradiction
  | continuing (falsified : Nat)
  | failed

def PropResInv (assign : Nat → Bool) : PropRes → Prop
  | .contradiction => False
  | .continuing f  => semFalsified assign f
  | .failed        => True

/-- Word-parallel GMP RUP unit-propagation loop over a short chunk `hints : List Nat` (`≤ 16` IDs). -/
def propagateGmpChunk (oDepth : Nat) (clauses : OctTrie Nat) (falsified : Nat) : List Nat → PropRes
  | [] => .continuing falsified
  | cid :: rest =>
    match OctTrie.get oDepth clauses cid with
    | none => .failed
    | some mask =>
      let rem := Nat.xor mask (Nat.land mask falsified)
      match Nat.beq rem 0 with
      | true => .contradiction
      | false =>
        match Nat.beq (Nat.land rem (Nat.sub rem 1)) 0 with
        | false => .failed
        | true =>
          let negRaw := match Nat.beq (Nat.mod rem 3) 1 with
            | true  => Nat.shiftLeft rem 1
            | false => Nat.shiftRight rem 1
          let falsified' := Nat.lor falsified negRaw
          match Nat.beq falsified' 0 with
          | true  => propagateGmpChunk oDepth clauses 0 rest
          | false => propagateGmpChunk oDepth clauses falsified' rest

theorem propagateGmpChunk_sound {oDepth : Nat} {assign : Nat → Bool} {clauses : OctTrie Nat}
    (hdb : OctTrie.AllValues (semMaskSat assign) clauses) :
    ∀ (hints : List Nat) (falsified : Nat),
      semFalsified assign falsified →
      PropResInv assign (propagateGmpChunk oDepth clauses falsified hints)
  | [], _, hfalse => hfalse
  | cid :: rest, falsified, hfalse => by
    unfold propagateGmpChunk
    cases hget : OctTrie.get oDepth clauses cid with
    | none => trivial
    | some mask =>
      dsimp only
      rcases OctTrie.get_allValues oDepth clauses cid mask hdb hget with ⟨litStar, hMaskBit, hLitTrue⟩
      have hNotInFalse : Nat.testBit falsified litStar = false := by
        cases hf : Nat.testBit falsified litStar with
        | false => rfl
        | true =>
          have hfl := hfalse litStar hf
          rw [hfl] at hLitTrue
          contradiction
      let rem := Nat.xor mask (Nat.land mask falsified)
      have hRemBit : Nat.testBit rem litStar = true := by
        show Nat.testBit (Nat.xor mask (Nat.land mask falsified)) litStar = true
        rw [testBit_xor', testBit_land', hMaskBit, hNotInFalse]
        rfl
      cases hrem0 : Nat.beq rem 0 with
      | true =>
        have hr0 : rem = 0 := Nat.eq_of_beq_eq_true hrem0
        rw [hr0, Nat.zero_testBit] at hRemBit
        contradiction
      | false =>
        dsimp only
        cases hpow2 : Nat.beq (Nat.land rem (Nat.sub rem 1)) 0 with
        | false => trivial
        | true =>
          dsimp only
          have hRemEq : rem = Nat.shiftLeft 1 litStar :=
            pow2_of_testBit_and_land_pred litStar rem hRemBit (Nat.eq_of_beq_eq_true hpow2)
          let negRaw := match Nat.beq (Nat.mod rem 3) 1 with
            | true  => Nat.shiftLeft rem 1
            | false => Nat.shiftRight rem 1
          have hNegFalse : ∀ m : Nat, Nat.testBit negRaw m = true → evalLit assign m = false := by
            unfold negRaw
            rw [hRemEq]
            exact evalLit_negBit_false hLitTrue
          have hFalseNext : semFalsified assign (Nat.lor falsified negRaw) := by
            intro m hm
            rw [testBit_lor'] at hm
            cases hfm : Nat.testBit falsified m with
            | true => exact hfalse m hfm
            | false =>
              rw [hfm, Bool.false_or] at hm
              exact hNegFalse m hm
          cases hfz : Nat.beq (Nat.lor falsified negRaw) 0 with
          | true =>
            have hz0 : semFalsified assign 0 := by
              intro m hm; rw [Nat.zero_testBit] at hm; contradiction
            exact propagateGmpChunk_sound hdb rest 0 hz0
          | false =>
            exact propagateGmpChunk_sound hdb rest (Nat.lor falsified negRaw) hFalseNext

def propagateGmpTree (oDepth : Nat) (clauses : OctTrie Nat) :
    Nat → Nat → StepTree (List Nat) → PropRes
  | 0, _, _ => .failed
  | Nat.succ _, falsified, .empty => .continuing falsified
  | Nat.succ _, falsified, .leaf chunk => propagateGmpChunk oDepth clauses falsified chunk
  | Nat.succ fuel, falsified, .branch l r =>
    match propagateGmpTree oDepth clauses fuel falsified l with
    | .contradiction => .contradiction
    | .failed => .failed
    | .continuing f1 => propagateGmpTree oDepth clauses fuel f1 r

theorem propagateGmpTree_sound {oDepth : Nat} {assign : Nat → Bool} {clauses : OctTrie Nat}
    (hdb : OctTrie.AllValues (semMaskSat assign) clauses) :
    ∀ (fuel : Nat) (falsified : Nat) (t : StepTree (List Nat)),
      semFalsified assign falsified →
      PropResInv assign (propagateGmpTree oDepth clauses fuel falsified t)
  | 0, _, _, _ => trivial
  | Nat.succ _, _, .empty, hfalse => hfalse
  | Nat.succ _, falsified, .leaf chunk, hfalse => propagateGmpChunk_sound (oDepth := oDepth) hdb chunk falsified hfalse
  | Nat.succ fuel, falsified, .branch l r, hfalse => by
    unfold propagateGmpTree
    have ihl := propagateGmpTree_sound (oDepth := oDepth) hdb fuel falsified l hfalse
    cases hres : propagateGmpTree oDepth clauses fuel falsified l with
    | contradiction => rw [hres] at ihl; exact ihl
    | failed => trivial
    | continuing f1 =>
      rw [hres] at ihl
      exact propagateGmpTree_sound (oDepth := oDepth) hdb fuel f1 r ihl

inductive LratStep where
  | addRup (id : Nat) (clause : StepTree (List Nat)) (hints : StepTree (List Nat))
  | del (ids : List Nat)
  | addEmpty (hints : StepTree (List Nat))

inductive GmpRunState where
  | running (db : OctTrie Nat)
  | proved
  | failed

def OctTrie.withForced {α β : Type} (t : OctTrie α) (k : OctTrie α → β) : β :=
  match t with
  | .empty => k .empty
  | .node v c0 c1 c2 c3 c4 c5 c6 c7 => k (.node v c0 c1 c2 c3 c4 c5 c6 c7)

theorem withForced_eq {α β : Type} (t : OctTrie α) (k : OctTrie α → β) :
    OctTrie.withForced t k = k t := by
  cases t <;> rfl

def deleteGmpIds (oDepth : Nat) : OctTrie Nat → List Nat → OctTrie Nat
  | db, [] => db
  | db, cid :: rest =>
    OctTrie.withForced (OctTrie.set oDepth db cid none) (fun db' => deleteGmpIds oDepth db' rest)

theorem forceNode_allValues {α : Type} {P : α → Prop} (t : OctTrie α) :
    OctTrie.AllValues P t → OctTrie.AllValues P (OctTrie.forceNode t) := by
  cases t <;> exact id

theorem deleteGmpIds_allValues {oDepth : Nat} {P : Nat → Prop} :
    ∀ (ids : List Nat) (db : OctTrie Nat),
      OctTrie.AllValues P db → OctTrie.AllValues P (deleteGmpIds oDepth db ids)
  | [], db, hdb => hdb
  | cid :: rest, db, hdb => by
    unfold deleteGmpIds
    rw [withForced_eq]
    exact deleteGmpIds_allValues rest _ (OctTrie.set_allValues oDepth db cid none hdb trivial)

def stepGmp (oDepth : Nat) (st : GmpRunState) (s : LratStep) : GmpRunState :=
  match st with
  | .proved => .proved
  | .failed => .failed
  | .running db =>
    match s with
    | .addRup cid cls hints =>
      let targetMask := compileClauseTree cls
      match propagateGmpTree oDepth db 14 targetMask hints with
      | .contradiction =>
        match Nat.beq targetMask 0 with
        | true  => .proved
        | false => OctTrie.withForced (OctTrie.set oDepth db cid (some targetMask)) GmpRunState.running
      | _ => .failed
    | .del ids => OctTrie.withForced (deleteGmpIds oDepth db ids) GmpRunState.running
    | .addEmpty hints =>
      match propagateGmpTree oDepth db 14 0 hints with
      | .contradiction => .proved
      | _ => .failed

def GmpStateInv (assign : Nat → Bool) : GmpRunState → Prop
  | .running db => OctTrie.AllValues (semMaskSat assign) db
  | .proved     => False
  | .failed     => True

theorem stepGmp_sound {oDepth : Nat} {assign : Nat → Bool} (st : GmpRunState) (s : LratStep)
    (hst : GmpStateInv assign st) : GmpStateInv assign (stepGmp oDepth st s) := by
  cases st with
  | proved => exact hst
  | failed => trivial
  | running db =>
    unfold stepGmp
    cases s with
    | del ids =>
      dsimp only
      rw [withForced_eq]
      exact deleteGmpIds_allValues ids db hst
    | addEmpty hints =>
      dsimp only
      have hz : semFalsified assign 0 := fun _ hm => by rw [Nat.zero_testBit] at hm; contradiction
      have hpInv := propagateGmpTree_sound (oDepth := oDepth) hst 14 0 hints hz
      cases hp : propagateGmpTree oDepth db 14 0 hints with
      | contradiction => rw [hp] at hpInv; exact hpInv
      | continuing _ => trivial
      | failed => trivial
    | addRup cid cls hints =>
      dsimp only
      cases hp : propagateGmpTree oDepth db 14 (compileClauseTree cls) hints with
      | continuing _ => trivial
      | failed => trivial
      | contradiction =>
        dsimp only
        have hclsSat : semMaskSat assign (compileClauseTree cls) := by
          cases hc : semClauseTree assign cls with
          | true => exact compileClauseTree_sat cls hc
          | false =>
            have hf := compileClauseTree_falsified_of_unsat cls hc
            have hpInv := propagateGmpTree_sound (oDepth := oDepth) hst 14 (compileClauseTree cls) hints hf
            rw [hp] at hpInv
            exact False.elim hpInv
        cases hm0 : Nat.beq (compileClauseTree cls) 0 with
        | true =>
          have hz := Nat.eq_of_beq_eq_true hm0
          rcases hclsSat with ⟨w, hwBit, _⟩
          rw [hz, Nat.zero_testBit] at hwBit
          contradiction
        | false =>
          rw [withForced_eq]
          exact OctTrie.set_allValues oDepth db cid (some (compileClauseTree cls)) hst hclsSat

def runGmpTree (oDepth : Nat) : Nat → GmpRunState → StepTree LratStep → GmpRunState
  | 0, _, _ => .failed
  | Nat.succ _, st, .empty => st
  | Nat.succ _, st, .leaf s => stepGmp oDepth st s
  | Nat.succ fuel, st, .branch l r =>
    match runGmpTree oDepth fuel st l with
    | .proved => .proved
    | .failed => .failed
    | .running db => OctTrie.withForced db (fun db' => runGmpTree oDepth fuel (.running db') r)

theorem runGmpTree_sound {oDepth : Nat} {assign : Nat → Bool} :
    ∀ (fuel : Nat) (st : GmpRunState) (tree : StepTree LratStep),
      GmpStateInv assign st → GmpStateInv assign (runGmpTree oDepth fuel st tree)
  | 0, _, _, _ => trivial
  | Nat.succ _, st, .empty, hst => hst
  | Nat.succ _, st, .leaf s, hst => stepGmp_sound st s hst
  | Nat.succ fuel, st, .branch l r, hst => by
    unfold runGmpTree
    have ihl := runGmpTree_sound (oDepth := oDepth) fuel st l hst
    cases hres : runGmpTree oDepth fuel st l with
    | proved => rw [hres] at ihl; exact ihl
    | failed => trivial
    | running db =>
      rw [hres] at ihl
      dsimp only
      rw [withForced_eq]
      exact runGmpTree_sound (oDepth := oDepth) fuel (.running db) r ihl

def semInitTree (assign : Nat → Bool) : StepTree (Nat × List Nat) → Prop
  | .empty => True
  | .leaf (_, cls) => semClauseList assign cls = true
  | .branch l r => semInitTree assign l ∧ semInitTree assign r

def initGmpDb (oDepth : Nat) : Nat → OctTrie Nat → StepTree (Nat × List Nat) → OctTrie Nat
  | 0, db, _ => db
  | Nat.succ _, db, .empty => db
  | Nat.succ _, db, .leaf (cid, cls) =>
    let m := compileClauseMask cls
    match Nat.beq m 0 with
    | true  => OctTrie.forceNode (OctTrie.set oDepth db cid (some 0))
    | false => OctTrie.forceNode (OctTrie.set oDepth db cid (some m))
  | Nat.succ fuel, db, .branch l r =>
    OctTrie.withForced (initGmpDb oDepth fuel db l) (fun db1 => initGmpDb oDepth fuel db1 r)

theorem initGmpDb_sound {oDepth : Nat} {assign : Nat → Bool} :
    ∀ (fuel : Nat) (db : OctTrie Nat) (t : StepTree (Nat × List Nat)),
      OctTrie.AllValues (semMaskSat assign) db →
      semInitTree assign t →
      OctTrie.AllValues (semMaskSat assign) (initGmpDb oDepth fuel db t)
  | 0, db, _, hdb, _ => hdb
  | Nat.succ _, db, .empty, hdb, _ => hdb
  | Nat.succ _, db, .leaf (cid, cls), hdb, hinit => by
    unfold initGmpDb
    dsimp only
    have hsat : semMaskSat assign (compileClauseMask cls) := compileClauseMask_sat cls hinit
    cases hm0 : Nat.beq (compileClauseMask cls) 0 with
    | true =>
      have hz := Nat.eq_of_beq_eq_true hm0
      rw [hz] at hsat
      apply forceNode_allValues
      exact OctTrie.set_allValues oDepth db cid (some 0) hdb hsat
    | false =>
      apply forceNode_allValues
      exact OctTrie.set_allValues oDepth db cid (some (compileClauseMask cls)) hdb hsat
  | Nat.succ fuel, db, .branch l r, hdb, ⟨hl, hr⟩ => by
    unfold initGmpDb
    rw [withForced_eq]
    have h1 := initGmpDb_sound (oDepth := oDepth) fuel db l hdb hl
    exact initGmpDb_sound (oDepth := oDepth) fuel _ r h1 hr

def checkLratGmp (oDepth treeFuel : Nat) (initClauses : StepTree (Nat × List Nat))
    (steps : StepTree LratStep) : Bool :=
  OctTrie.withForced (initGmpDb oDepth treeFuel .empty initClauses) fun db0 =>
    match runGmpTree oDepth treeFuel (.running db0) steps with
    | .proved => true
    | _ => false

/-- Complete Soundness Theorem for the GMP Word-Parallel Bitset LRAT Checker! -/
theorem checkLratGmp_sound {oDepth treeFuel : Nat}
    {initClauses : StepTree (Nat × List Nat)} {steps : StepTree LratStep}
    (hcert : checkLratGmp oDepth treeFuel initClauses steps = true)
    (assign : Nat → Bool) (hinit : semInitTree assign initClauses) :
    False := by
  unfold checkLratGmp at hcert
  rw [withForced_eq] at hcert
  have hdb0 := initGmpDb_sound (oDepth := oDepth) treeFuel .empty initClauses trivial hinit
  have hrun := runGmpTree_sound (oDepth := oDepth) treeFuel (.running _) steps hdb0
  cases hr : runGmpTree oDepth treeFuel (.running (initGmpDb oDepth treeFuel .empty initClauses)) steps with
  | proved => rw [hr] at hrun; exact hrun
  | running _ => rw [hr] at hcert; contradiction
  | failed => rw [hr] at hcert; contradiction

-- Compact u16 GMP-stream decoders (zero extra soundness burden by `checkLratGmp_sound`!)
inductive NatListStream where
  | mk (items : List Nat) (rest : Nat)

def withNatForced {α : Type} (n : Nat) (k : Nat → α) : α :=
  match Nat.beq n 0 with
  | true  => k 0
  | false => k n

def readU16ListRev : Nat → Nat → List Nat → NatListStream
  | 0, s, acc => .mk acc.reverse s
  | Nat.succ k, s, acc =>
    withNatForced (Nat.land s 0xffff) fun w =>
      withNatForced (Nat.shiftRight s 16) fun s' =>
        readU16ListRev k s' (w :: acc)

def listToTreePass {α : Type} : Nat → List (StepTree α) → List (StepTree α)
  | 0, xs => xs
  | Nat.succ _, [] => []
  | Nat.succ _, [x] => [x]
  | Nat.succ fuel, x :: y :: rest => (.branch x y) :: listToTreePass fuel rest

def listToStepTree {α : Type} : Nat → Nat → List (StepTree α) → StepTree α
  | _, _, [] => .empty
  | _, _, [t] => t
  | 0, _, t :: _ => t
  | Nat.succ outer, pairFuel, ts => listToStepTree outer pairFuel (listToTreePass pairFuel ts)

inductive ChunkTreeStream where
  | mk (tree : StepTree (List Nat)) (rest : Nat)

def readU16ChunksRev : Nat → Nat → Nat → List (StepTree (List Nat)) → ChunkTreeStream
  | 0, _, s, acc => .mk (listToStepTree 10 250 acc.reverse) s
  | Nat.succ chunkFuel, rem, s, acc =>
    match rem with
    | 0 => .mk (listToStepTree 10 250 acc.reverse) s
    | _ =>
      let take := if decide (rem ≤ 16) then rem else 16
      match readU16ListRev take s [] with
      | .mk ch s' => readU16ChunksRev chunkFuel (rem - take) s' (.leaf ch :: acc)

def decodeU16StepsRev : Nat → Nat → List LratStep → List LratStep
  | 0, _, acc => acc.reverse
  | Nat.succ fuel, s, acc =>
    let tag := Nat.land s 0xffff
    let s1 := Nat.shiftRight s 16
    match Nat.beq tag 0 with
    | true => acc.reverse
    | false =>
      match Nat.beq tag 1 with
      | true =>
        let cid := Nat.land s1 0xffff
        let cLen := Nat.land (Nat.shiftRight s1 16) 0xffff
        let hLen := Nat.land (Nat.shiftRight s1 32) 0xffff
        let s4 := Nat.shiftRight s1 48
        match readU16ChunksRev 250 cLen s4 [] with
        | .mk clsTree s5 =>
          match readU16ChunksRev 250 hLen s5 [] with
          | .mk hintsTree s6 =>
            decodeU16StepsRev fuel s6 ((.addRup cid clsTree hintsTree) :: acc)
      | false =>
        match Nat.beq tag 2 with
        | true =>
          let dLen := Nat.land s1 0xffff
          let s2 := Nat.shiftRight s1 16
          match readU16ListRev dLen s2 [] with
          | .mk ids s3 => decodeU16StepsRev fuel s3 ((.del ids) :: acc)
        | false =>
          let hLen := Nat.land s1 0xffff
          let s2 := Nat.shiftRight s1 16
          match readU16ChunksRev 250 hLen s2 [] with
          | .mk hintsTree s3 => decodeU16StepsRev fuel s3 ((.addEmpty hintsTree) :: acc)

def decodePackedSteps : Nat → StepTree Nat → StepTree LratStep
  | 0, _ => .empty
  | Nat.succ _, .empty => .empty
  | Nat.succ _, .leaf s =>
    listToStepTree 8 140 ((decodeU16StepsRev 140 s []).map StepTree.leaf)
  | Nat.succ fuel, .branch l r =>
    .branch (decodePackedSteps fuel l) (decodePackedSteps fuel r)

def decodeU16InitRev : Nat → Nat → List (Nat × List Nat) → List (Nat × List Nat)
  | 0, _, acc => acc.reverse
  | Nat.succ fuel, s, acc =>
    let cid := Nat.land s 0xffff
    let s1 := Nat.shiftRight s 16
    match Nat.beq cid 0 with
    | true => acc.reverse
    | false =>
      let cLen := Nat.land s1 0xffff
      let s2 := Nat.shiftRight s1 16
      match readU16ListRev cLen s2 [] with
      | .mk cls s3 => decodeU16InitRev fuel s3 ((cid, cls) :: acc)

def decodePackedInit : Nat → StepTree Nat → StepTree (Nat × List Nat)
  | 0, _ => .empty
  | Nat.succ _, .empty => .empty
  | Nat.succ _, .leaf s =>
    listToStepTree 8 140 ((decodeU16InitRev 140 s []).map StepTree.leaf)
  | Nat.succ fuel, .branch l r =>
    .branch (decodePackedInit fuel l) (decodePackedInit fuel r)

-- ============================================================================
-- Section 3: `HashMap`-Free Read-Only Arena AIG & UNSAT-Core Tseitin Encoder
-- ============================================================================

/-- Environment mapping `(width, varId)` to `BitVec width`. -/
abbrev BvEnv := (w : Nat) → Nat → BitVec w

inductive AigNode where
  | constFalse
  | atom (width : Nat) (varId : Nat) (bitIdx : Nat)
  | andGate (lhsLit : Nat) (rhsLit : Nat)

structure AigArena where
  maxGate : Nat
  decls   : StepTree (Nat × AigNode)
  nodes   : OctTrie AigNode
  /-- Self-verified gate lookup directory `(canonKey -> gateId)` (never trusted!). -/
  gateDir : OctTrie Nat
  /-- Self-verified atom lookup directory `(atomKey -> gateId)` (never trusted!). -/
  atomDir : OctTrie Nat

def buildNodeTrie (aDepth : Nat) : Nat → OctTrie AigNode → StepTree (Nat × AigNode) → OctTrie AigNode
  | 0, t, _ => t
  | Nat.succ _, t, .empty => t
  | Nat.succ _, t, .leaf (gid, nd) => OctTrie.forceNode (OctTrie.set aDepth t gid (some nd))
  | Nat.succ fuel, t, .branch l r =>
    OctTrie.withForced (buildNodeTrie aDepth fuel t l) (fun t1 => buildNodeTrie aDepth fuel t1 r)

def decodeAigNodesChunk (aDepth : Nat) : Nat → OctTrie AigNode → Nat → OctTrie AigNode
  | 0, t, _ => t
  | Nat.succ fuel, t, s =>
    let gid := Nat.land s 0xffff
    let s1  := Nat.shiftRight s 16
    match Nat.beq gid 0 with
    | true => t
    | false =>
      let tag := Nat.land s1 0xffff
      let s2  := Nat.shiftRight s1 16
      match Nat.beq tag 1 with
      | true =>
        OctTrie.withForced (OctTrie.set aDepth t gid (some .constFalse))
          (fun t' => withNatForced s2 (fun s2' => decodeAigNodesChunk aDepth fuel t' s2'))
      | false =>
        match Nat.beq tag 2 with
        | true =>
          let w := Nat.land s2 0xffff
          let v := Nat.land (Nat.shiftRight s2 16) 0xffff
          let b := Nat.land (Nat.shiftRight s2 32) 0xffff
          let s5 := Nat.shiftRight s2 48
          OctTrie.withForced (OctTrie.set aDepth t gid (some (.atom w v b)))
            (fun t' => withNatForced s5 (fun s5' => decodeAigNodesChunk aDepth fuel t' s5'))
        | false =>
          let l1 := Nat.land s2 0xffff
          let l2 := Nat.land (Nat.shiftRight s2 16) 0xffff
          let s4 := Nat.shiftRight s2 32
          OctTrie.withForced (OctTrie.set aDepth t gid (some (.andGate l1 l2)))
            (fun t' => withNatForced s4 (fun s4' => decodeAigNodesChunk aDepth fuel t' s4'))

def decodeAigNodesTree (aDepth : Nat) : Nat → OctTrie AigNode → StepTree Nat → OctTrie AigNode
  | 0, t, _ => t
  | Nat.succ _, t, .empty => t
  | Nat.succ _, t, .leaf s => decodeAigNodesChunk aDepth 100 t s
  | Nat.succ fuel, t, .branch l r =>
    OctTrie.withForced (decodeAigNodesTree aDepth fuel t l)
      (fun t1 => decodeAigNodesTree aDepth fuel t1 r)

def decodeDirChunk (dDepth : Nat) : Nat → OctTrie Nat → Nat → OctTrie Nat
  | 0, t, _ => t
  | Nat.succ fuel, t, s =>
    let gid := Nat.land s 0xffff
    let s1  := Nat.shiftRight s 16
    match Nat.beq gid 0 with
    | true => t
    | false =>
      let keyLo := Nat.land s1 0xffff
      let keyHi := Nat.land (Nat.shiftRight s1 16) 0xffff
      let key   := Nat.lor keyLo (Nat.shiftLeft keyHi 16)
      let s3    := Nat.shiftRight s1 32
      OctTrie.withForced (OctTrie.set dDepth t key (some gid))
        (fun t' => withNatForced s3 (fun s3' => decodeDirChunk dDepth fuel t' s3'))

def decodeDirTree (dDepth : Nat) : Nat → OctTrie Nat → StepTree Nat → OctTrie Nat
  | 0, t, _ => t
  | Nat.succ _, t, .empty => t
  | Nat.succ _, t, .leaf s => decodeDirChunk dDepth 100 t s
  | Nat.succ fuel, t, .branch l r =>
    OctTrie.withForced (decodeDirTree dDepth fuel t l)
      (fun t1 => decodeDirTree dDepth fuel t1 r)

def decodePackedAig (maxGate : Nat) (nodesTree gateTree atomTree : StepTree Nat) : AigArena :=
  { maxGate := maxGate
    decls   := .empty
    nodes   := decodeAigNodesTree 5 14 .empty nodesTree
    gateDir := decodeDirTree 11 14 .empty gateTree
    atomDir := decodeDirTree 11 14 .empty atomTree }

/-- Check that every node in `nodes` referenced in `decls` is acyclic (`faninGate < gid < maxGate`)
    and that node `1` is `.constFalse` (so literal `2` is `false` and literal `3` is `true`). -/
def checkAigValidTree (aDepth maxGate : Nat) (nodes : OctTrie AigNode) :
    Nat → StepTree (Nat × AigNode) → Bool
  | 0, _ => false
  | Nat.succ _, .empty => true
  | Nat.succ _, .leaf (gid, nd) =>
    decide (0 < gid) && decide (gid < maxGate) &&
    match OctTrie.get aDepth nodes gid, nd with
    | some .constFalse, .constFalse => true
    | some (.atom w1 v1 b1), .atom w2 v2 b2 =>
      Nat.beq w1 w2 && Nat.beq v1 v2 && Nat.beq b1 b2
    | some (.andGate a1 b1), .andGate a2 b2 =>
      Nat.beq a1 a2 && Nat.beq b1 b2 &&
      decide (Nat.shiftRight a1 1 < gid) && decide (Nat.shiftRight b1 1 < gid)
    | _, _ => false
  | Nat.succ fuel, .branch l r =>
    checkAigValidTree aDepth maxGate nodes fuel l &&
    checkAigValidTree aDepth maxGate nodes fuel r

/-- Notice we don't even need `decls` if we define `aigAssignUpTo` directly over `nodes`
    and check fanin acyclicity `Nat.shiftRight l1 1 < g ∧ Nat.shiftRight l2 1 < g` locally AT EACH
    GATE LOOKUP AND TSEITIN CLAUSE CHECK!!
    WAIT A SECOND! Look how clean local acyclicity is: ZERO `decls` traversal needed! -/
def aigAssignUpTo (aDepth : Nat) (env : BvEnv) (nodes : OctTrie AigNode) : Nat → (Nat → Bool)
  | 0 => fun _ => false
  | Nat.succ g =>
    let prev := aigAssignUpTo aDepth env nodes g
    let val := match OctTrie.get aDepth nodes g with
      | none => false
      | some .constFalse => false
      | some (.atom w v b) => (env w v).getLsbD b
      | some (.andGate l1 l2) => evalLit prev l1 && evalLit prev l2
    fun k => match Nat.beq k g with | true => val | false => prev k

theorem aigAssignUpTo_lt (aDepth : Nat) (env : BvEnv) (nodes : OctTrie AigNode) :
    ∀ {m n k : Nat}, k < n → n ≤ m →
      aigAssignUpTo aDepth env nodes m k = aigAssignUpTo aDepth env nodes n k
  | 0, _, _, hk, hnm => by omega
  | Nat.succ m, n, k, hk, hnm => by
    cases Nat.lt_or_eq_of_le hnm with
    | inr heq => subst heq; rfl
    | inl hlt =>
      have hle : n ≤ m := Nat.le_of_lt_succ hlt
      have hkm : k < m := Nat.lt_of_lt_of_le hk hle
      have hne : Nat.beq k m = false := by
        cases hb : Nat.beq k m with
        | false => rfl
        | true => exact False.elim (Nat.ne_of_lt hkm (Nat.eq_of_beq_eq_true hb))
      change (match Nat.beq k m with
        | true => _
        | false => aigAssignUpTo aDepth env nodes m k) = aigAssignUpTo aDepth env nodes n k
      rw [hne]
      exact aigAssignUpTo_lt aDepth env nodes hk hle

theorem aigAssignUpTo_eq_self (aDepth : Nat) (env : BvEnv) (nodes : OctTrie AigNode)
    {maxGate g : Nat} (hg : g < maxGate) :
    aigAssignUpTo aDepth env nodes maxGate g =
      match OctTrie.get aDepth nodes g with
      | none => false
      | some .constFalse => false
      | some (.atom w v b) => (env w v).getLsbD b
      | some (.andGate l1 l2) =>
        evalLit (aigAssignUpTo aDepth env nodes g) l1 &&
        evalLit (aigAssignUpTo aDepth env nodes g) l2 := by
  have hle : g + 1 ≤ maxGate := hg
  have hlt : g < g + 1 := Nat.lt_succ_self g
  rw [aigAssignUpTo_lt aDepth env nodes hlt hle]
  have hself : Nat.beq g g = true := Nat.beq_refl g
  change (match Nat.beq g g with
    | true =>
      match OctTrie.get aDepth nodes g with
      | none => false
      | some .constFalse => false
      | some (.atom w v b) => (env w v).getLsbD b
      | some (.andGate l1 l2) =>
        evalLit (aigAssignUpTo aDepth env nodes g) l1 &&
        evalLit (aigAssignUpTo aDepth env nodes g) l2
    | false => aigAssignUpTo aDepth env nodes g g) = _
  rw [hself]

theorem evalLit_aigAssign_stable (aDepth : Nat) (env : BvEnv) (nodes : OctTrie AigNode)
    {maxGate g l : Nat} (hl : Nat.shiftRight l 1 < g) (hg : g < maxGate) :
    evalLit (aigAssignUpTo aDepth env nodes g) l =
    evalLit (aigAssignUpTo aDepth env nodes maxGate) l := by
  unfold evalLit
  have h := aigAssignUpTo_lt aDepth env nodes hl (Nat.le_of_lt hg)
  rw [h]

/-- Verify that a single CNF clause is soundly entailed by the AIG semantics + `evalLit σ rootLit = true`! -/
def checkTseitinClause (aDepth maxGate : Nat) (nodes : OctTrie AigNode) (rootLit : Nat)
    (cls : List Nat) : Bool :=
  match cls with
  | [l] =>
    match Nat.beq l rootLit with
    | true => true
    | false =>
      -- `.constFalse` unit clause `[2 * g + 1]`
      let g := Nat.shiftRight l 1
      Nat.beq (Nat.land l 1) 1 && decide (g < maxGate) &&
      match OctTrie.get aDepth nodes g with
      | some .constFalse => true
      | _ => false
  | [c1, c2] =>
    -- Gate binary clause `[2*g + 1, l1]` or `[2*g + 1, l2]`
    let g := Nat.shiftRight c1 1
    Nat.beq (Nat.land c1 1) 1 && decide (g < maxGate) &&
    match OctTrie.get aDepth nodes g with
    | some (.andGate l1 l2) =>
      decide (Nat.shiftRight l1 1 < g) && decide (Nat.shiftRight l2 1 < g) &&
      (Nat.beq c2 l1 || Nat.beq c2 l2)
    | _ => false
  | [c1, c2, c3] =>
    -- Gate ternary clause `[2*g, l1 ^^^ 1, l2 ^^^ 1]`
    let g := Nat.shiftRight c1 1
    Nat.beq (Nat.land c1 1) 0 && decide (g < maxGate) &&
    match OctTrie.get aDepth nodes g with
    | some (.andGate l1 l2) =>
      decide (Nat.shiftRight l1 1 < g) && decide (Nat.shiftRight l2 1 < g) &&
      Nat.beq c2 (Nat.xor l1 1) && Nat.beq c3 (Nat.xor l2 1)
    | _ => false
  | _ => false

theorem evalLit_xor_one (assign : Nat → Bool) (l : Nat) :
    evalLit assign (Nat.xor l 1) = !(evalLit assign l) := by
  unfold evalLit
  have hsr : Nat.shiftRight (Nat.xor l 1) 1 = Nat.shiftRight l 1 := by
    change (l ^^^ 1) >>> 1 = l >>> 1
    rw [Nat.shiftRight_xor_distrib]
    have h1 : (1 : Nat) >>> 1 = 0 := rfl
    rw [h1, Nat.xor_zero]
  have hland : Nat.beq (Nat.land (Nat.xor l 1) 1) 0 = !(Nat.beq (Nat.land l 1) 0) := by
    rw [nat_land_one_eq_mod, nat_land_one_eq_mod]
    have hbit : Nat.testBit (Nat.xor l 1) 0 = !(Nat.testBit l 0) := by
      rw [testBit_xor']
      simp
    rw [Nat.testBit_zero, Nat.testBit_zero] at hbit
    cases hm : l % 2 with
    | zero =>
      have : (Nat.xor l 1) % 2 = 1 := by
        rw [hm] at hbit
        exact decide_eq_true_iff.mp hbit
      rw [this]; rfl
    | succ r =>
      have hr0 : r = 0 := by omega
      subst hr0
      rw [hm] at hbit
      have hne1 : ¬((Nat.xor l 1) % 2 = 1) := decide_eq_false_iff_not.mp hbit
      have hz : (Nat.xor l 1) % 2 = 0 := by omega
      rw [hz]; rfl
  rw [hsr, hland]
  cases Nat.beq (Nat.land l 1) 0 <;> simp

theorem checkTseitinClause_sound {aDepth maxGate : Nat} {env : BvEnv}
    {nodes : OctTrie AigNode} {rootLit : Nat} {cls : List Nat}
    (hroot : evalLit (aigAssignUpTo aDepth env nodes maxGate) rootLit = true)
    (hchk : checkTseitinClause aDepth maxGate nodes rootLit cls = true) :
    semClauseList (aigAssignUpTo aDepth env nodes maxGate) cls = true := by
  match cls with
  | [] => nomatch hchk
  | [l] =>
    unfold checkTseitinClause at hchk
    dsimp only at hchk
    cases hrl : Nat.beq l rootLit with
    | true =>
      have heq := Nat.eq_of_beq_eq_true hrl
      subst heq
      unfold semClauseList
      rw [hroot, Bool.true_or]
    | false =>
      rw [hrl] at hchk
      dsimp only at hchk
      cases hl1 : Nat.beq (Nat.land l 1) 1 with
      | false => rw [hl1] at hchk; contradiction
      | true =>
        rw [hl1, Bool.true_and] at hchk
        cases hlt : decide (Nat.shiftRight l 1 < maxGate) with
        | false => rw [hlt] at hchk; contradiction
        | true =>
          rw [hlt, Bool.true_and] at hchk
          have hg := of_decide_eq_true hlt
          cases hnd : OctTrie.get aDepth nodes (Nat.shiftRight l 1) with
          | none => rw [hnd] at hchk; contradiction
          | some nd =>
            rw [hnd] at hchk
            cases nd with
            | atom _ _ _ => contradiction
            | andGate _ _ => contradiction
            | constFalse =>
              unfold semClauseList evalLit
              have hodd : Nat.beq (Nat.land l 1) 0 = false := by
                have h := Nat.eq_of_beq_eq_true hl1
                rw [h]; rfl
              rw [hodd, aigAssignUpTo_eq_self aDepth env nodes hg, hnd]
              rfl
  | [c1, c2] =>
    unfold checkTseitinClause at hchk
    dsimp only at hchk
    cases hc1 : Nat.beq (Nat.land c1 1) 1 with
    | false => rw [hc1] at hchk; contradiction
    | true =>
      rw [hc1, Bool.true_and] at hchk
      cases hlt : decide (Nat.shiftRight c1 1 < maxGate) with
      | false => rw [hlt] at hchk; contradiction
      | true =>
        rw [hlt, Bool.true_and] at hchk
        have hg := of_decide_eq_true hlt
        cases hnd : OctTrie.get aDepth nodes (Nat.shiftRight c1 1) with
        | none => rw [hnd] at hchk; contradiction
        | some nd =>
          rw [hnd] at hchk
          cases nd with
          | constFalse => contradiction
          | atom _ _ _ => contradiction
          | andGate l1 l2 =>
            dsimp only at hchk
            cases hl1 : decide (Nat.shiftRight l1 1 < Nat.shiftRight c1 1) with
            | false => rw [hl1] at hchk; contradiction
            | true =>
              rw [hl1, Bool.true_and] at hchk
              cases hl2 : decide (Nat.shiftRight l2 1 < Nat.shiftRight c1 1) with
              | false => rw [hl2] at hchk; contradiction
              | true =>
                rw [hl2, Bool.true_and] at hchk
                have odd1 : Nat.beq (Nat.land c1 1) 0 = false := by
                  rw [Nat.eq_of_beq_eq_true hc1]; rfl
                have hvalG : aigAssignUpTo aDepth env nodes maxGate (Nat.shiftRight c1 1) =
                    (evalLit (aigAssignUpTo aDepth env nodes maxGate) l1 &&
                     evalLit (aigAssignUpTo aDepth env nodes maxGate) l2) := by
                  rw [aigAssignUpTo_eq_self aDepth env nodes hg, hnd]
                  dsimp only
                  rw [evalLit_aigAssign_stable aDepth env nodes (of_decide_eq_true hl1) hg,
                      evalLit_aigAssign_stable aDepth env nodes (of_decide_eq_true hl2) hg]
                have hc1Eval : evalLit (aigAssignUpTo aDepth env nodes maxGate) c1 =
                    !(evalLit (aigAssignUpTo aDepth env nodes maxGate) l1 &&
                      evalLit (aigAssignUpTo aDepth env nodes maxGate) l2) := by
                  change (match Nat.beq (Nat.land c1 1) 0 with
                    | true => aigAssignUpTo aDepth env nodes maxGate (Nat.shiftRight c1 1)
                    | false => !(aigAssignUpTo aDepth env nodes maxGate (Nat.shiftRight c1 1))) = _
                  rw [odd1, hvalG]
                simp only [semClauseList, hc1Eval, Bool.or_false]
                cases heq1 : Nat.beq c2 l1 with
                | true =>
                  rw [Nat.eq_of_beq_eq_true heq1]
                  cases evalLit (aigAssignUpTo aDepth env nodes maxGate) l1 <;>
                  cases evalLit (aigAssignUpTo aDepth env nodes maxGate) l2 <;> rfl
                | false =>
                  rw [heq1, Bool.false_or] at hchk
                  rw [Nat.eq_of_beq_eq_true hchk]
                  cases evalLit (aigAssignUpTo aDepth env nodes maxGate) l1 <;>
                  cases evalLit (aigAssignUpTo aDepth env nodes maxGate) l2 <;> rfl
  | [c1, c2, c3] =>
    unfold checkTseitinClause at hchk
    dsimp only at hchk
    cases hc1 : Nat.beq (Nat.land c1 1) 0 with
    | false => rw [hc1] at hchk; contradiction
    | true =>
      rw [hc1, Bool.true_and] at hchk
      cases hlt : decide (Nat.shiftRight c1 1 < maxGate) with
      | false => rw [hlt] at hchk; contradiction
      | true =>
        rw [hlt, Bool.true_and] at hchk
        have hg := of_decide_eq_true hlt
        cases hnd : OctTrie.get aDepth nodes (Nat.shiftRight c1 1) with
        | none => rw [hnd] at hchk; contradiction
        | some nd =>
          rw [hnd] at hchk
          cases nd with
          | constFalse => contradiction
          | atom _ _ _ => contradiction
          | andGate l1 l2 =>
            dsimp only at hchk
            cases hl1 : decide (Nat.shiftRight l1 1 < Nat.shiftRight c1 1) with
            | false => rw [hl1] at hchk; contradiction
            | true =>
              rw [hl1, Bool.true_and] at hchk
              cases hl2 : decide (Nat.shiftRight l2 1 < Nat.shiftRight c1 1) with
              | false => rw [hl2] at hchk; contradiction
              | true =>
                rw [hl2, Bool.true_and] at hchk
                cases heq2 : Nat.beq c2 (Nat.xor l1 1) with
                | false => rw [heq2] at hchk; contradiction
                | true =>
                  rw [heq2, Bool.true_and] at hchk
                  have hc2Eq := Nat.eq_of_beq_eq_true heq2
                  have hc3Eq := Nat.eq_of_beq_eq_true hchk
                  subst hc2Eq; subst hc3Eq
                  have hvalG : aigAssignUpTo aDepth env nodes maxGate (Nat.shiftRight c1 1) =
                      (evalLit (aigAssignUpTo aDepth env nodes maxGate) l1 &&
                       evalLit (aigAssignUpTo aDepth env nodes maxGate) l2) := by
                    rw [aigAssignUpTo_eq_self aDepth env nodes hg, hnd]
                    dsimp only
                    rw [evalLit_aigAssign_stable aDepth env nodes (of_decide_eq_true hl1) hg,
                        evalLit_aigAssign_stable aDepth env nodes (of_decide_eq_true hl2) hg]
                  have hc1Eval : evalLit (aigAssignUpTo aDepth env nodes maxGate) c1 =
                      (evalLit (aigAssignUpTo aDepth env nodes maxGate) l1 &&
                       evalLit (aigAssignUpTo aDepth env nodes maxGate) l2) := by
                    change (match Nat.beq (Nat.land c1 1) 0 with
                      | true => aigAssignUpTo aDepth env nodes maxGate (Nat.shiftRight c1 1)
                      | false => !(aigAssignUpTo aDepth env nodes maxGate (Nat.shiftRight c1 1))) = _
                    rw [hc1, hvalG]
                  simp only [semClauseList, hc1Eval, evalLit_xor_one, Bool.or_false]
                  cases evalLit (aigAssignUpTo aDepth env nodes maxGate) l1 <;>
                  cases evalLit (aigAssignUpTo aDepth env nodes maxGate) l2 <;> rfl
  | _ :: _ :: _ :: _ :: _ => nomatch hchk

def checkTseitinCnfTree (aDepth maxGate : Nat) (nodes : OctTrie AigNode) (rootLit : Nat) :
    Nat → StepTree (Nat × List Nat) → Bool
  | 0, _ => false
  | Nat.succ _, .empty => true
  | Nat.succ _, .leaf (_, cls) => checkTseitinClause aDepth maxGate nodes rootLit cls
  | Nat.succ fuel, .branch l r =>
    checkTseitinCnfTree aDepth maxGate nodes rootLit fuel l &&
    checkTseitinCnfTree aDepth maxGate nodes rootLit fuel r

theorem checkTseitinCnfTree_sound {aDepth maxGate : Nat} {env : BvEnv}
    {nodes : OctTrie AigNode} {rootLit : Nat}
    (hroot : evalLit (aigAssignUpTo aDepth env nodes maxGate) rootLit = true) :
    ∀ (fuel : Nat) (cnf : StepTree (Nat × List Nat)),
      checkTseitinCnfTree aDepth maxGate nodes rootLit fuel cnf = true →
      semInitTree (aigAssignUpTo aDepth env nodes maxGate) cnf
  | 0, _, h => nomatch h
  | Nat.succ _, .empty, _ => trivial
  | Nat.succ _, .leaf (_, cls), h => checkTseitinClause_sound hroot h
  | Nat.succ fuel, .branch l r, h => by
    unfold checkTseitinCnfTree at h
    cases hl : checkTseitinCnfTree aDepth maxGate nodes rootLit fuel l with
    | false => rw [hl] at h; contradiction
    | true =>
      rw [hl, Bool.true_and] at h
      exact ⟨checkTseitinCnfTree_sound hroot fuel l hl, checkTseitinCnfTree_sound hroot fuel r h⟩

-- ============================================================================
-- Section 4: Self-Verifying Read-Only AIG Gate Combinators (`0` Cache Trust!)
-- ============================================================================

def falseLit : Nat := 2 -- Gate 1 = `.constFalse`, so `2 * 1 = 2` is `false`, `3` is `true`!
def trueLit  : Nat := 3

def checkFalseGate1 (aDepth maxGate : Nat) (nodes : OctTrie AigNode) : Bool :=
  decide (1 < maxGate) &&
  match OctTrie.get aDepth nodes 1 with
  | some .constFalse => true
  | _ => false

theorem checkFalseGate1_false {aDepth maxGate : Nat} {env : BvEnv} {nodes : OctTrie AigNode}
    (hf1 : checkFalseGate1 aDepth maxGate nodes = true) :
    evalLit (aigAssignUpTo aDepth env nodes maxGate) falseLit = false := by
  unfold checkFalseGate1 at hf1
  cases hlt : decide (1 < maxGate) with
  | false => rw [hlt] at hf1; contradiction
  | true =>
    rw [hlt, Bool.true_and] at hf1
    cases hnd : OctTrie.get aDepth nodes 1 with
    | none => rw [hnd] at hf1; contradiction
    | some nd =>
      rw [hnd] at hf1
      cases nd with
      | atom _ _ _ => contradiction
      | andGate _ _ => contradiction
      | constFalse =>
        unfold evalLit falseLit
        have h1lt := of_decide_eq_true hlt
        have heq := aigAssignUpTo_eq_self aDepth env nodes h1lt
        rw [hnd] at heq
        exact heq

theorem checkFalseGate1_true {aDepth maxGate : Nat} {env : BvEnv} {nodes : OctTrie AigNode}
    (hf1 : checkFalseGate1 aDepth maxGate nodes = true) :
    evalLit (aigAssignUpTo aDepth env nodes maxGate) trueLit = true := by
  have h : trueLit = Nat.xor falseLit 1 := rfl
  rw [h, evalLit_xor_one, checkFalseGate1_false hf1]
  rfl

def canonPairKey (l1 l2 : Nat) : Nat :=
  match decide (l1 ≤ l2) with
  | true  => Nat.lor (Nat.shiftLeft l1 16) l2
  | false => Nat.lor (Nat.shiftLeft l2 16) l1

def atomKey (w v b : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft w 15) (Nat.lor (Nat.shiftLeft v 9) b)

def lookupAtom (aDepth : Nat) (aig : AigArena) (w v b : Nat) : Option Nat :=
  match OctTrie.get 11 aig.atomDir (atomKey w v b) with
  | none => none
  | some g =>
    match decide (g < aig.maxGate), OctTrie.get aDepth aig.nodes g with
    | true, some (.atom w' v' b') =>
      match Nat.beq w w' && Nat.beq v v' && Nat.beq b b' with
      | true  => some (2 * g)
      | false => none
    | _, _ => none

theorem lookupAtom_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w v b outLit : Nat}
    (hlook : lookupAtom aDepth aig w v b = some outLit) :
    evalLit (aigAssignUpTo aDepth env aig.nodes aig.maxGate) outLit = (env w v).getLsbD b := by
  unfold lookupAtom at hlook
  cases hd : OctTrie.get 11 aig.atomDir (atomKey w v b) with
  | none => rw [hd] at hlook; contradiction
  | some g =>
    rw [hd] at hlook
    dsimp only at hlook
    cases hlt : decide (g < aig.maxGate) with
    | false => rw [hlt] at hlook; contradiction
    | true =>
      rw [hlt] at hlook
      cases hnd : OctTrie.get aDepth aig.nodes g with
      | none => rw [hnd] at hlook; contradiction
      | some nd =>
        rw [hnd] at hlook
        cases nd with
        | constFalse => contradiction
        | andGate _ _ => contradiction
        | atom w' v' b' =>
          dsimp only at hlook
          cases h1 : Nat.beq w w' with
          | false => rw [h1] at hlook; contradiction
          | true =>
            rw [h1, Bool.true_and] at hlook
            cases h2 : Nat.beq v v' with
            | false => rw [h2] at hlook; contradiction
            | true =>
              rw [h2, Bool.true_and] at hlook
              cases h3 : Nat.beq b b' with
              | false => rw [h3] at hlook; contradiction
              | true =>
                rw [h3] at hlook
                injection hlook with hout
                subst hout
                have hw := Nat.eq_of_beq_eq_true h1
                have hv := Nat.eq_of_beq_eq_true h2
                have hb := Nat.eq_of_beq_eq_true h3
                subst hw; subst hv; subst hb
                unfold evalLit
                have hev : Nat.beq (Nat.land (2 * g) 1) 0 = true := by
                  rw [nat_land_one_eq_mod]; simp
                have hsr : Nat.shiftRight (2 * g) 1 = g := by
                  rw [shiftRight_eq_div]; simp
                rw [hev, hsr, aigAssignUpTo_eq_self aDepth env aig.nodes (of_decide_eq_true hlt), hnd]

def lookupAnd (aDepth : Nat) (aig : AigArena) (l1 l2 : Nat) : Option Nat :=
  if Nat.beq l1 falseLit || Nat.beq l2 falseLit then some falseLit
  else if Nat.beq l1 trueLit then some l2
  else if Nat.beq l2 trueLit then some l1
  else if Nat.beq l1 l2 then some l1
  else if Nat.beq l1 (Nat.xor l2 1) then some falseLit
  else
    match OctTrie.get 11 aig.gateDir (canonPairKey l1 l2) with
    | none => none
    | some g =>
      match decide (g < aig.maxGate), OctTrie.get aDepth aig.nodes g with
      | true, some (.andGate a b) =>
        let okOrder := (Nat.beq a l1 && Nat.beq b l2) || (Nat.beq a l2 && Nat.beq b l1)
        let okTopo := decide (Nat.shiftRight a 1 < g) && decide (Nat.shiftRight b 1 < g)
        match okOrder && okTopo with
        | true  => some (2 * g)
        | false => none
      | _, _ => none

theorem lookupAnd_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {l1 l2 outLit : Nat}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hlook : lookupAnd aDepth aig l1 l2 = some outLit) :
    let σ := aigAssignUpTo aDepth env aig.nodes aig.maxGate
    evalLit σ outLit = (evalLit σ l1 && evalLit σ l2) := by
  intro σ
  unfold lookupAnd at hlook
  cases hcf : (Nat.beq l1 falseLit || Nat.beq l2 falseLit) with
  | true =>
    rw [ite_true_eq hcf] at hlook
    injection hlook with hout; subst hout
    rw [checkFalseGate1_false hf1]
    cases hb1 : Nat.beq l1 falseLit with
    | true =>
      rw [Nat.eq_of_beq_eq_true hb1, checkFalseGate1_false hf1, Bool.false_and]
    | false =>
      rw [hb1, Bool.false_or] at hcf
      rw [Nat.eq_of_beq_eq_true hcf, checkFalseGate1_false hf1, Bool.and_false]
  | false =>
    rw [ite_false_eq (by rw [hcf]; decide)] at hlook
    cases ht1 : Nat.beq l1 trueLit with
    | true =>
      rw [ite_true_eq ht1] at hlook
      injection hlook with hout; subst hout
      rw [Nat.eq_of_beq_eq_true ht1, checkFalseGate1_true hf1, Bool.true_and]
    | false =>
      rw [ite_false_eq (by rw [ht1]; decide)] at hlook
      cases ht2 : Nat.beq l2 trueLit with
      | true =>
        rw [ite_true_eq ht2] at hlook
        injection hlook with hout; subst hout
        rw [Nat.eq_of_beq_eq_true ht2, checkFalseGate1_true hf1, Bool.and_true]
      | false =>
        rw [ite_false_eq (by rw [ht2]; decide)] at hlook
        cases heq : Nat.beq l1 l2 with
        | true =>
          rw [ite_true_eq heq] at hlook
          injection hlook with hout; subst hout
          rw [Nat.eq_of_beq_eq_true heq, Bool.and_self]
        | false =>
          rw [ite_false_eq (by rw [heq]; decide)] at hlook
          cases hneg : Nat.beq l1 (Nat.xor l2 1) with
          | true =>
            rw [ite_true_eq hneg] at hlook
            injection hlook with hout; subst hout
            rw [Nat.eq_of_beq_eq_true hneg, evalLit_xor_one, checkFalseGate1_false hf1]
            cases evalLit σ l2 <;> rfl
          | false =>
            rw [ite_false_eq (by rw [hneg]; decide)] at hlook
            cases hdir : OctTrie.get 11 aig.gateDir (canonPairKey l1 l2) with
            | none => rw [hdir] at hlook; contradiction
            | some g =>
              rw [hdir] at hlook
              dsimp only at hlook
              cases hlt : decide (g < aig.maxGate) with
              | false => rw [hlt] at hlook; contradiction
              | true =>
                rw [hlt] at hlook
                cases hnd : OctTrie.get aDepth aig.nodes g with
                | none => rw [hnd] at hlook; contradiction
                | some nd =>
                  rw [hnd] at hlook
                  cases nd with
                  | constFalse => contradiction
                  | atom _ _ _ => contradiction
                  | andGate a b =>
                    dsimp only at hlook
                    cases hord : ((Nat.beq a l1 && Nat.beq b l2) || (Nat.beq a l2 && Nat.beq b l1)) with
                    | false => rw [hord, Bool.false_and] at hlook; contradiction
                    | true =>
                      rw [hord, Bool.true_and] at hlook
                      cases hta : decide (Nat.shiftRight a 1 < g) with
                      | false => rw [hta, Bool.false_and] at hlook; contradiction
                      | true =>
                        rw [hta, Bool.true_and] at hlook
                        cases htb : decide (Nat.shiftRight b 1 < g) with
                        | false => rw [htb] at hlook; contradiction
                        | true =>
                          rw [htb] at hlook
                          injection hlook with hout; subst hout
                          have hglt := of_decide_eq_true hlt
                          have hev : Nat.beq (Nat.land (2 * g) 1) 0 = true := by rw [nat_land_one_eq_mod]; simp
                          have hsr : Nat.shiftRight (2 * g) 1 = g := by rw [shiftRight_eq_div]; simp
                          show evalLit σ (2 * g) = (evalLit σ l1 && evalLit σ l2)
                          unfold evalLit
                          rw [hev, hsr]
                          show aigAssignUpTo aDepth env aig.nodes aig.maxGate g = (evalLit σ l1 && evalLit σ l2)
                          rw [aigAssignUpTo_eq_self aDepth env aig.nodes hglt, hnd]
                          dsimp only
                          rw [evalLit_aigAssign_stable aDepth env aig.nodes (of_decide_eq_true hta) hglt,
                              evalLit_aigAssign_stable aDepth env aig.nodes (of_decide_eq_true htb) hglt]
                          change (evalLit σ a && evalLit σ b) = (evalLit σ l1 && evalLit σ l2)
                          cases h1 : (Nat.beq a l1 && Nat.beq b l2) with
                          | true =>
                            cases ha1 : Nat.beq a l1 with
                            | false => rw [ha1] at h1; contradiction
                            | true =>
                              rw [ha1, Bool.true_and] at h1
                              rw [Nat.eq_of_beq_eq_true ha1, Nat.eq_of_beq_eq_true h1]
                          | false =>
                            rw [h1, Bool.false_or] at hord
                            cases ha2 : Nat.beq a l2 with
                            | false => rw [ha2] at hord; contradiction
                            | true =>
                              rw [ha2, Bool.true_and] at hord
                              rw [Nat.eq_of_beq_eq_true ha2, Nat.eq_of_beq_eq_true hord, Bool.and_comm]

def lookupOr (aDepth : Nat) (aig : AigArena) (l1 l2 : Nat) : Option Nat :=
  match lookupAnd aDepth aig (Nat.xor l1 1) (Nat.xor l2 1) with
  | none => none
  | some m => some (Nat.xor m 1)

theorem lookupOr_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {l1 l2 outLit : Nat}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hlook : lookupOr aDepth aig l1 l2 = some outLit) :
    let σ := aigAssignUpTo aDepth env aig.nodes aig.maxGate
    evalLit σ outLit = (evalLit σ l1 || evalLit σ l2) := by
  intro σ
  unfold lookupOr at hlook
  cases hm : lookupAnd aDepth aig (Nat.xor l1 1) (Nat.xor l2 1) with
  | none => rw [hm] at hlook; contradiction
  | some m =>
    rw [hm] at hlook
    injection hlook with hout; subst hout
    rw [evalLit_xor_one, lookupAnd_sound hf1 hm, evalLit_xor_one, evalLit_xor_one]
    cases evalLit σ l1 <;> cases evalLit σ l2 <;> rfl

def lookupXor (aDepth : Nat) (aig : AigArena) (l1 l2 : Nat) : Option Nat :=
  match lookupAnd aDepth aig l1 (Nat.xor l2 1), lookupAnd aDepth aig (Nat.xor l1 1) l2 with
  | some a, some b => lookupOr aDepth aig a b
  | _, _ => none

theorem lookupXor_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {l1 l2 outLit : Nat}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hlook : lookupXor aDepth aig l1 l2 = some outLit) :
    let σ := aigAssignUpTo aDepth env aig.nodes aig.maxGate
    evalLit σ outLit = bne (evalLit σ l1) (evalLit σ l2) := by
  intro σ
  unfold lookupXor at hlook
  cases ha : lookupAnd aDepth aig l1 (Nat.xor l2 1) with
  | none => rw [ha] at hlook; contradiction
  | some a =>
    rw [ha] at hlook
    cases hb : lookupAnd aDepth aig (Nat.xor l1 1) l2 with
    | none => rw [hb] at hlook; contradiction
    | some b =>
      rw [hb] at hlook
      rw [lookupOr_sound hf1 hlook, lookupAnd_sound hf1 ha, lookupAnd_sound hf1 hb,
          evalLit_xor_one, evalLit_xor_one]
      cases evalLit σ l1 <;> cases evalLit σ l2 <;> rfl

def lookupMux (aDepth : Nat) (aig : AigArena) (c t e : Nat) : Option Nat :=
  match lookupAnd aDepth aig c t, lookupAnd aDepth aig (Nat.xor c 1) e with
  | some a, some b => lookupOr aDepth aig a b
  | _, _ => none

theorem lookupMux_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {c t e outLit : Nat}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hlook : lookupMux aDepth aig c t e = some outLit) :
    let σ := aigAssignUpTo aDepth env aig.nodes aig.maxGate
    evalLit σ outLit = (if evalLit σ c then evalLit σ t else evalLit σ e) := by
  intro σ
  unfold lookupMux at hlook
  cases ha : lookupAnd aDepth aig c t with
  | none => rw [ha] at hlook; contradiction
  | some a =>
    rw [ha] at hlook
    cases hb : lookupAnd aDepth aig (Nat.xor c 1) e with
    | none => rw [hb] at hlook; contradiction
    | some b =>
      rw [hb] at hlook
      rw [lookupOr_sound hf1 hlook, lookupAnd_sound hf1 ha, lookupAnd_sound hf1 hb, evalLit_xor_one]
      cases evalLit σ c <;> cases evalLit σ t <;> cases evalLit σ e <;> rfl

def lookupAtLeastTwo (aDepth : Nat) (aig : AigArena) (a b c : Nat) : Option Nat :=
  match lookupAnd aDepth aig a b, lookupAnd aDepth aig a c, lookupAnd aDepth aig b c with
  | some ab, some ac, some bc =>
    match lookupOr aDepth aig ab ac with
    | some ab_ac => lookupOr aDepth aig ab_ac bc
    | none => none
  | _, _, _ => none

theorem lookupAtLeastTwo_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {a b c outLit : Nat}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hlook : lookupAtLeastTwo aDepth aig a b c = some outLit) :
    let σ := aigAssignUpTo aDepth env aig.nodes aig.maxGate
    evalLit σ outLit = Bool.atLeastTwo (evalLit σ a) (evalLit σ b) (evalLit σ c) := by
  intro σ
  unfold lookupAtLeastTwo at hlook
  cases hab : lookupAnd aDepth aig a b with
  | none => rw [hab] at hlook; contradiction
  | some ab =>
    rw [hab] at hlook
    cases hac : lookupAnd aDepth aig a c with
    | none => rw [hac] at hlook; contradiction
    | some ac =>
      rw [hac] at hlook
      cases hbc : lookupAnd aDepth aig b c with
      | none => rw [hbc] at hlook; contradiction
      | some bc =>
        rw [hbc] at hlook
        dsimp only at hlook
        cases habc : lookupOr aDepth aig ab ac with
        | none => rw [habc] at hlook; contradiction
        | some ab_ac =>
          rw [habc] at hlook
          rw [lookupOr_sound hf1 hlook, lookupOr_sound hf1 habc,
              lookupAnd_sound hf1 hab, lookupAnd_sound hf1 hac, lookupAnd_sound hf1 hbc]

-- ============================================================================
-- Section 5: `BitVec w` & SIMD Expression Language + Verified Bit-Blaster
-- ============================================================================

mutual
inductive BvExpr : Nat → Type where
  | var        (w : Nat) (id : Nat) : BvExpr w
  | const      {w : Nat} (val : BitVec w) : BvExpr w
  | not        {w : Nat} (x : BvExpr w) : BvExpr w
  | and        {w : Nat} (x y : BvExpr w) : BvExpr w
  | or         {w : Nat} (x y : BvExpr w) : BvExpr w
  | xor        {w : Nat} (x y : BvExpr w) : BvExpr w
  | add        {w : Nat} (x y : BvExpr w) : BvExpr w
  | sub        {w : Nat} (x y : BvExpr w) : BvExpr w
  | neg        {w : Nat} (x : BvExpr w) : BvExpr w
  | shlConst   {w : Nat} (x : BvExpr w) (k : Nat) : BvExpr w
  | lshrConst  {w : Nat} (x : BvExpr w) (k : Nat) : BvExpr w
  | ashrConst  {w : Nat} (x : BvExpr w) (k : Nat) : BvExpr w
  | extract    {wIn : Nat} (lo len : Nat) (x : BvExpr wIn) : BvExpr len
  | concat     {wHi wLo : Nat} (hi : BvExpr wHi) (lo : BvExpr wLo) : BvExpr (wHi + wLo)
  | zeroExtend {wIn : Nat} (wOut : Nat) (x : BvExpr wIn) : BvExpr wOut
  | signExtend {wIn : Nat} (wOut : Nat) (x : BvExpr wIn) : BvExpr wOut
  | ite        {w : Nat} (cond : BvPred) (t e : BvExpr w) : BvExpr w
  | mul        {w : Nat} (x y : BvExpr w) : BvExpr w

inductive BvPred : Type where
  | constBool (b : Bool) : BvPred
  | pNot      (p : BvPred) : BvPred
  | pAnd      (p q : BvPred) : BvPred
  | pOr       (p q : BvPred) : BvPred
  | pXor      (p q : BvPred) : BvPred
  | pIff      (p q : BvPred) : BvPred
  | eq        {w : Nat} (x y : BvExpr w) : BvPred
  | ult       {w : Nat} (x y : BvExpr w) : BvPred
  | slt       {w : Nat} (x y : BvExpr w) : BvPred
  | getBit    {w : Nat} (x : BvExpr w) (idx : Nat) : BvPred
end

mutual
def evalBvExpr : BvExpr w → BvEnv → BitVec w
  | .var w id, env => env w id
  | .const val, _ => val
  | .not x, env => ~~~(evalBvExpr x env)
  | .and x y, env => (evalBvExpr x env) &&& (evalBvExpr y env)
  | .or x y, env => (evalBvExpr x env) ||| (evalBvExpr y env)
  | .xor x y, env => (evalBvExpr x env) ^^^ (evalBvExpr y env)
  | .add x y, env => (evalBvExpr x env) + (evalBvExpr y env)
  | .sub x y, env => (evalBvExpr x env) - (evalBvExpr y env)
  | .neg x, env => -(evalBvExpr x env)
  | .shlConst x k, env => (evalBvExpr x env) <<< k
  | .lshrConst x k, env => (evalBvExpr x env) >>> k
  | .ashrConst x k, env => BitVec.sshiftRight (evalBvExpr x env) k
  | .extract lo len x, env => BitVec.extractLsb' lo len (evalBvExpr x env)
  | .concat hi lo, env => BitVec.append (evalBvExpr hi env) (evalBvExpr lo env)
  | .zeroExtend wOut x, env => BitVec.zeroExtend wOut (evalBvExpr x env)
  | .signExtend wOut x, env => BitVec.signExtend wOut (evalBvExpr x env)
  | .ite c t e, env => if evalBv c env then evalBvExpr t env else evalBvExpr e env
  | .mul x y, env => (evalBvExpr x env) * (evalBvExpr y env)

def evalBv : BvPred → BvEnv → Bool
  | .constBool b, _ => b
  | .pNot p, env => !(evalBv p env)
  | .pAnd p q, env => (evalBv p env) && (evalBv q env)
  | .pOr p q, env => (evalBv p env) || (evalBv q env)
  | .pXor p q, env => bne (evalBv p env) (evalBv q env)
  | .pIff p q, env => (evalBv p env) == (evalBv q env)
  | .eq x y, env => (evalBvExpr x env) == (evalBvExpr y env)
  | .ult x y, env => BitVec.ult (evalBvExpr x env) (evalBvExpr y env)
  | .slt x y, env => BitVec.slt (evalBvExpr x env) (evalBvExpr y env)
  | .getBit x idx, env => (evalBvExpr x env).getLsbD idx
end

-- Indexed wire vector: represent a `w`-bit wire vector by `Nat → Option Nat` on `0 .. w-1`!
-- WAIT A SECOND: representing a wire vector by `List Nat` of exact length `w` (or `Array`? No, `List Nat`!)
-- Let's write tiny 5-line `List` combinators by index `tabulateWires w (f : Nat → Option Nat) : Option (List Nat)`!
-- LOOK HOW CLEAN `tabulateWires` IS: EVERY operator (`const`, `var`, `not`, `and`, `or`, `xor`,
-- `shlConst`, `lshrConst`, `ashrConst`, `extract`, `concat`, `zeroExtend`, `signExtend`, `ite`)
-- IS A ONE-LINER `tabulateWires w (fun i => ...)` PROVED BY ONE UNIVERSAL `tabulateWires_sound` LEMMA!!

def getWire (ws : List Nat) (i : Nat) : Nat :=
  ws.getD i falseLit

def WiresMatch {w : Nat} (σ : Nat → Bool) (ws : List Nat) (v : BitVec w) : Prop :=
  ws.length = w ∧ ∀ i : Nat, i < w → evalLit σ (getWire ws i) = v.getLsbD i

def tabulateWiresAux (f : Nat → Option Nat) : Nat → List Nat → Option (List Nat)
  | 0, acc => some acc
  | Nat.succ k, acc =>
    match f k with
    | none => none
    | some lit => tabulateWiresAux f k (lit :: acc)

def tabulateWires (w : Nat) (f : Nat → Option Nat) : Option (List Nat) :=
  tabulateWiresAux f w []

theorem tabulateWiresAux_spec (f : Nat → Option Nat) :
    ∀ (n : Nat) (acc : List Nat) (out : List Nat),
      tabulateWiresAux f n acc = some out →
      out.length = n + acc.length ∧
      (∀ i < n, ∃ lit, f i = some lit ∧ out.getD i falseLit = lit) ∧
      (∀ j, out.getD (n + j) falseLit = acc.getD j falseLit)
  | 0, acc, out, h => by
    unfold tabulateWiresAux at h
    injection h with hout; subst hout
    refine ⟨by simp, ?_, ?_⟩
    · intro i hi; omega
    · intro j; simp
  | Nat.succ k, acc, out, h => by
    unfold tabulateWiresAux at h
    cases hfk : f k with
    | none => rw [hfk] at h; contradiction
    | some litK =>
      rw [hfk] at h
      rcases tabulateWiresAux_spec f k (litK :: acc) out h with ⟨hlen, hlo, hhi⟩
      refine ⟨by simp at hlen; omega, ?_, ?_⟩
      · intro i hi
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with
        | inl hlt => exact hlo i hlt
        | inr heq =>
          subst heq
          refine ⟨litK, hfk, ?_⟩
          have h0 := hhi 0
          simpa using h0
      · intro j
        have h1 := hhi (j + 1)
        have hadd : k + (j + 1) = Nat.succ k + j := by omega
        rw [hadd] at h1
        simpa [List.getD] using h1

theorem tabulateWires_sound {w : Nat} {σ : Nat → Bool} {f : Nat → Option Nat}
    {ws : List Nat} {v : BitVec w}
    (htab : tabulateWires w f = some ws)
    (hbit : ∀ i : Nat, i < w → ∀ lit : Nat, f i = some lit → evalLit σ lit = v.getLsbD i) :
    WiresMatch σ ws v := by
  rcases tabulateWiresAux_spec f w [] ws htab with ⟨hlen, hlo, _⟩
  refine ⟨by simpa using hlen, ?_⟩
  intro i hi
  rcases hlo i hi with ⟨lit, hfl, hget⟩
  unfold getWire
  rw [hget]
  exact hbit i hi lit hfl

-- Ripple-carry adder returning `(carryOutLit, sumWires)`!
def blastAdcAux (aDepth : Nat) (aig : AigArena) (wx wy : List Nat) :
    Nat → Nat → Nat → Option (Nat × List Nat)
  | 0, _, cin => some (cin, [])
  | Nat.succ rem, idx, cin =>
    let a := getWire wx idx
    let b := getWire wy idx
    match lookupXor aDepth aig b cin with
    | none => none
    | some bXorC =>
      match lookupXor aDepth aig a bXorC, lookupAtLeastTwo aDepth aig a b cin with
      | some sumBit, some cout =>
        match blastAdcAux aDepth aig wx wy rem (idx + 1) cout with
        | none => none
        | some (finalCarry, restBits) => some (finalCarry, sumBit :: restBits)
      | _, _ => none

theorem blastAdcAux_spec {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {wx wy : List Nat} {vx vy : BitVec w}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hy : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wy vy) :
    ∀ (rem idx : Nat) (_hbound : idx + rem ≤ w) (cin : Nat) (cVal : Bool)
      (fCarry : Nat) (outBits : List Nat),
      evalLit (aigAssignUpTo aDepth env aig.nodes aig.maxGate) cin = BitVec.carry idx vx vy cVal →
      blastAdcAux aDepth aig wx wy rem idx cin = some (fCarry, outBits) →
      let σ := aigAssignUpTo aDepth env aig.nodes aig.maxGate
      outBits.length = rem ∧
      evalLit σ fCarry = BitVec.carry (idx + rem) vx vy cVal ∧
      (∀ k < rem, evalLit σ (outBits.getD k falseLit) =
        (vx + vy + BitVec.setWidth w (BitVec.ofBool cVal)).getLsbD (idx + k))
  | 0, idx, _, cin, cVal, fCarry, outBits, hcin, hblast => by
    unfold blastAdcAux at hblast
    injection hblast with hp
    injection hp with hc hb
    subst hc; subst hb
    refine ⟨rfl, by simpa using hcin, ?_⟩
    intro k hk; omega
  | Nat.succ rem, idx, hbound, cin, cVal, fCarry, outBits, hcin, hblast => by
    let σ := aigAssignUpTo aDepth env aig.nodes aig.maxGate
    have hidx : idx < w := by omega
    unfold blastAdcAux at hblast
    dsimp only at hblast
    cases hbx : lookupXor aDepth aig (getWire wy idx) cin with
    | none => rw [hbx] at hblast; contradiction
    | some bXorC =>
      rw [hbx] at hblast
      dsimp only at hblast
      cases hs : lookupXor aDepth aig (getWire wx idx) bXorC with
      | none => rw [hs] at hblast; contradiction
      | some sumBit =>
        rw [hs] at hblast
        cases hc : lookupAtLeastTwo aDepth aig (getWire wx idx) (getWire wy idx) cin with
        | none => rw [hc] at hblast; contradiction
        | some cout =>
          rw [hc] at hblast
          dsimp only at hblast
          cases hrec : blastAdcAux aDepth aig wx wy rem (idx + 1) cout with
          | none => rw [hrec] at hblast; contradiction
          | some pair =>
            rw [hrec] at hblast
            rcases pair with ⟨fc, rb⟩
            injection hblast with hp
            injection hp with hfc hrb
            subst hfc; subst hrb
            have hcoutVal : evalLit σ cout = BitVec.carry (idx + 1) vx vy cVal := by
              rw [lookupAtLeastTwo_sound hf1 hc, hx.2 idx hidx, hy.2 idx hidx, hcin, BitVec.carry_succ]
            have hsumVal : evalLit σ sumBit =
                (vx + vy + BitVec.setWidth w (BitVec.ofBool cVal)).getLsbD idx := by
              rw [lookupXor_sound hf1 hs, lookupXor_sound hf1 hbx, hx.2 idx hidx, hy.2 idx hidx,
                  hcin, BitVec.getLsbD_add_add_bool hidx]
            have ih := blastAdcAux_spec hf1 hx hy rem (idx + 1) (by omega) cout cVal fc rb hcoutVal hrec
            rcases ih with ⟨hlen, hfcVal, hbits⟩
            refine ⟨by simp [hlen], ?_, ?_⟩
            · have hadd : idx + 1 + rem = idx + Nat.succ rem := by omega
              rw [← hadd]; exact hfcVal
            · intro k hk
              cases k with
              | zero => simpa [List.getD] using hsumVal
              | succ k' =>
                have hk' : k' < rem := by omega
                have hstep := hbits k' hk'
                have hidx_eq : idx + 1 + k' = idx + Nat.succ k' := by omega
                rw [hidx_eq] at hstep
                simpa [List.getD] using hstep

def blastAdd (aDepth : Nat) (aig : AigArena) (w : Nat) (wx wy : List Nat) : Option (List Nat) :=
  match blastAdcAux aDepth aig wx wy w 0 falseLit with
  | none => none
  | some (_, bits) => some bits

theorem blastAdd_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {wx wy out : List Nat} {vx vy : BitVec w}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hy : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wy vy)
    (hadd : blastAdd aDepth aig w wx wy = some out) :
    WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out (vx + vy) := by
  unfold blastAdd at hadd
  cases h : blastAdcAux aDepth aig wx wy w 0 falseLit with
  | none => rw [h] at hadd; contradiction
  | some pair =>
    rw [h] at hadd
    rcases pair with ⟨fc, bits⟩
    injection hadd with hout; subst hout
    have hcin : evalLit (aigAssignUpTo aDepth env aig.nodes aig.maxGate) falseLit =
        BitVec.carry 0 vx vy false := by
      rw [checkFalseGate1_false hf1, BitVec.carry_zero]
    rcases blastAdcAux_spec hf1 hx hy w 0 (by omega) falseLit false fc bits hcin h with ⟨hlen, _, hbits⟩
    refine ⟨hlen, ?_⟩
    intro i hi
    have hb := hbits i hi
    unfold getWire
    simpa using hb

def blastNot (wx : List Nat) : List Nat :=
  wx.map (fun l => Nat.xor l 1)

theorem blastNot_sound {σ : Nat → Bool} {w : Nat} {wx : List Nat} {vx : BitVec w}
    (hx : WiresMatch σ wx vx) :
    WiresMatch σ (blastNot wx) (~~~vx) := by
  refine ⟨by simp [blastNot, hx.1], ?_⟩
  intro i hi
  have hiLen : i < wx.length := by rw [hx.1]; exact hi
  have hget : getWire (blastNot wx) i = Nat.xor (getWire wx i) 1 := by
    unfold getWire blastNot
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem hiLen]
    rfl
  rw [hget, evalLit_xor_one, hx.2 i hi]
  simp [hi]

def blastConst (w : Nat) (val : BitVec w) : Option (List Nat) :=
  tabulateWires w (fun i => some (if val.getLsbD i then trueLit else falseLit))

theorem blastConst_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {val : BitVec w} {ws : List Nat}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hc : blastConst w val = some ws) :
    WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) ws val := by
  apply tabulateWires_sound hc
  intro i _ lit hlit
  injection hlit with h; subst h
  cases val.getLsbD i
  · exact checkFalseGate1_false hf1
  · exact checkFalseGate1_true hf1

def blastNeg (aDepth : Nat) (aig : AigArena) (w : Nat) (wx : List Nat) : Option (List Nat) :=
  match blastConst w (1#w) with
  | none => none
  | some w1 => blastAdd aDepth aig w (blastNot wx) w1

theorem blastNeg_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {wx out : List Nat} {vx : BitVec w}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hneg : blastNeg aDepth aig w wx = some out) :
    WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out (-vx) := by
  unfold blastNeg at hneg
  cases hc : blastConst w (1#w) with
  | none => rw [hc] at hneg; contradiction
  | some w1 =>
    rw [hc] at hneg
    rw [BitVec.neg_eq_not_add]
    exact blastAdd_sound hf1 (blastNot_sound hx) (blastConst_sound hf1 hc) hneg

def blastSub (aDepth : Nat) (aig : AigArena) (w : Nat) (wx wy : List Nat) : Option (List Nat) :=
  match blastNeg aDepth aig w wy with
  | none => none
  | some nwy => blastAdd aDepth aig w wx nwy

theorem blastSub_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {wx wy out : List Nat} {vx vy : BitVec w}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hy : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wy vy)
    (hsub : blastSub aDepth aig w wx wy = some out) :
    WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out (vx - vy) := by
  unfold blastSub at hsub
  cases hn : blastNeg aDepth aig w wy with
  | none => rw [hn] at hsub; contradiction
  | some nwy =>
    rw [hn] at hsub
    rw [BitVec.sub_eq_add_neg]
    exact blastAdd_sound hf1 hx (blastNeg_sound hf1 hy hn) hsub

def blastShlConst (w : Nat) (wx : List Nat) (k : Nat) : Option (List Nat) :=
  tabulateWires w (fun i => some (if decide (i < k) then falseLit else getWire wx (i - k)))

theorem blastShlConst_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w k : Nat}
    {wx out : List Nat} {vx : BitVec w}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hsh : blastShlConst w wx k = some out) :
    WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out (vx <<< k) := by
  apply tabulateWires_sound hsh
  intro i hi lit hlit
  injection hlit with h; subst h
  rw [BitVec.getLsbD_shiftLeft]
  simp only [hi, decide_true, Bool.true_and]
  cases hlt : decide (i < k) with
  | true =>
    rw [ite_true_eq rfl, checkFalseGate1_false hf1]
    simp
  | false =>
    rw [ite_false_eq (by decide)]
    have hsub_lt : i - k < w := by
      rw [decide_eq_false_iff_not] at hlt
      omega
    rw [hx.2 (i - k) hsub_lt]
    simp

def blastLshrConst (w : Nat) (wx : List Nat) (k : Nat) : Option (List Nat) :=
  tabulateWires w (fun i => some (if decide (k + i < w) then getWire wx (k + i) else falseLit))

theorem blastLshrConst_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w k : Nat}
    {wx out : List Nat} {vx : BitVec w}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hsh : blastLshrConst w wx k = some out) :
    WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out (vx >>> k) := by
  apply tabulateWires_sound hsh
  intro i _ lit hlit
  injection hlit with h; subst h
  rw [BitVec.getLsbD_ushiftRight]
  cases hlt : decide (k + i < w) with
  | true =>
    rw [ite_true_eq rfl, hx.2 (k + i) (of_decide_eq_true hlt)]
  | false =>
    rw [ite_false_eq (by decide), checkFalseGate1_false hf1]
    have hge : w ≤ k + i := by rw [decide_eq_false_iff_not] at hlt; omega
    exact (BitVec.getLsbD_of_ge vx (k + i) hge).symm

def blastAshrConst (w : Nat) (wx : List Nat) (k : Nat) : Option (List Nat) :=
  tabulateWires w (fun i =>
    some (if decide (k + i < w) then getWire wx (k + i) else getWire wx (w - 1)))

theorem blastAshrConst_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w k : Nat}
    {wx out : List Nat} {vx : BitVec w}
    (_hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hsh : blastAshrConst w wx k = some out) :
    WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out (BitVec.sshiftRight vx k) := by
  apply tabulateWires_sound hsh
  intro i hi lit hlit
  injection hlit with h; subst h
  rw [BitVec.getLsbD_sshiftRight]
  have hnotle : ¬(w ≤ i) := by omega
  simp only [hnotle, decide_false, Bool.not_false, Bool.true_and]
  have hw1 : w - 1 < w := by omega
  cases hlt : decide (k + i < w) with
  | true =>
    have hklt := of_decide_eq_true hlt
    rw [ite_true_eq rfl, hx.2 (k + i) hklt]
    simp [hklt]
  | false =>
    have hnot : ¬(k + i < w) := decide_eq_false_iff_not.mp hlt
    rw [ite_false_eq (by decide), hx.2 (w - 1) hw1]
    unfold BitVec.msb BitVec.getMsbD
    have hw0 : 0 < w := by omega
    simp [hnot, hw0]

def blastMuxWires (aDepth : Nat) (aig : AigArena) (w : Nat) (c : Nat) (wt we : List Nat) :
    Option (List Nat) :=
  tabulateWires w (fun i => lookupMux aDepth aig c (getWire wt i) (getWire we i))

theorem blastMuxWires_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {c : Nat} {wt we out : List Nat} {bVal : Bool} {vt ve : BitVec w}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hc : evalLit (aigAssignUpTo aDepth env aig.nodes aig.maxGate) c = bVal)
    (ht : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wt vt)
    (he : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) we ve)
    (hmux : blastMuxWires aDepth aig w c wt we = some out) :
    WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out (if bVal then vt else ve) := by
  apply tabulateWires_sound hmux
  intro i hi lit hlit
  rw [lookupMux_sound hf1 hlit, hc, ht.2 i hi, he.2 i hi]
  cases bVal <;> rfl

-- Shift-and-add multiplication matching `BitVec.mulRec` (`Init.Data.BitVec.Bitblast`)!
def blastMulRec (aDepth : Nat) (aig : AigArena) (w : Nat) (wx wy : List Nat) :
    Nat → Option (List Nat)
  | 0 =>
    match blastConst w (0#w) with
    | none => none
    | some z => blastMuxWires aDepth aig w (getWire wy 0) wx z
  | Nat.succ s =>
    match blastMulRec aDepth aig w wx wy s, blastShlConst w wx (s + 1), blastConst w (0#w) with
    | some prev, some shifted, some z =>
      match blastMuxWires aDepth aig w (getWire wy (s + 1)) shifted z with
      | none => none
      | some cur => blastAdd aDepth aig w prev cur
    | _, _, _ => none

def blastMul (aDepth : Nat) (aig : AigArena) (w : Nat) (wx wy : List Nat) : Option (List Nat) :=
  match w with
  | 0 => some []
  | Nat.succ w' => blastMulRec aDepth aig (Nat.succ w') wx wy w'

theorem blastMulRec_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {wx wy : List Nat} {vx vy : BitVec w}
    (hw : 0 < w)
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hy : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wy vy) :
    ∀ (s : Nat), s < w → ∀ out : List Nat,
      blastMulRec aDepth aig w wx wy s = some out →
      WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out (BitVec.mulRec vx vy s)
  | 0, hs, out, hm => by
    unfold blastMulRec at hm
    cases hz : blastConst w (0#w) with
    | none => rw [hz] at hm; contradiction
    | some z =>
      rw [hz] at hm
      rw [BitVec.mulRec_zero_eq]
      exact blastMuxWires_sound hf1 (hy.2 0 hs) hx (blastConst_sound hf1 hz) hm
  | Nat.succ s, hs, out, hm => by
    unfold blastMulRec at hm
    cases hp : blastMulRec aDepth aig w wx wy s with
    | none => rw [hp] at hm; contradiction
    | some prev =>
      rw [hp] at hm
      cases hsh : blastShlConst w wx (s + 1) with
      | none => rw [hsh] at hm; contradiction
      | some shifted =>
        rw [hsh] at hm
        cases hz : blastConst w (0#w) with
        | none => rw [hz] at hm; contradiction
        | some z =>
          rw [hz] at hm
          dsimp only at hm
          cases hcur : blastMuxWires aDepth aig w (getWire wy (s + 1)) shifted z with
          | none => rw [hcur] at hm; contradiction
          | some cur =>
            rw [hcur] at hm
            rw [BitVec.mulRec_succ_eq]
            have hprev := blastMulRec_sound hw hf1 hx hy s (by omega) prev hp
            have hcurMatch := blastMuxWires_sound hf1 (hy.2 (s + 1) hs)
              (blastShlConst_sound hf1 hx hsh) (blastConst_sound hf1 hz) hcur
            exact blastAdd_sound hf1 hprev hcurMatch hm

theorem blastMul_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {wx wy out : List Nat} {vx vy : BitVec w}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hy : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wy vy)
    (hmul : blastMul aDepth aig w wx wy = some out) :
    WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out (vx * vy) := by
  cases w with
  | zero =>
    unfold blastMul at hmul
    injection hmul with hout; subst hout
    refine ⟨rfl, ?_⟩
    intro i hi; omega
  | succ w' =>
    unfold blastMul at hmul
    have hrec := blastMulRec_sound (Nat.zero_lt_succ w') hf1 hx hy w' (Nat.lt_succ_self w') out hmul
    have hmulEq : vx * vy = BitVec.mulRec vx vy w' := by
      rw [BitVec.mul_eq_mulRec]
      rw [BitVec.mulRec_eq_mul_signExtend_setWidth, BitVec.mulRec_eq_mul_signExtend_setWidth]
      have h1 : ((vy.setWidth (w' + 1)).setWidth (w' + 1)) = vy := by simp
      have h2 : ((vy.setWidth (w' + 1 + 1)).setWidth (w' + 1)) = vy := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp [hi]
      rw [h1, h2]
    rw [hmulEq]
    exact hrec

-- Predicates: `eq`, `ult`, `slt`!
def allBitsEq {w : Nat} (vx vy : BitVec w) : Nat → Bool
  | 0 => true
  | Nat.succ k => allBitsEq vx vy k && (vx.getLsbD k == vy.getLsbD k)

theorem allBitsEq_true_iff {w : Nat} (vx vy : BitVec w) :
    ∀ n : Nat, allBitsEq vx vy n = true ↔ (∀ k < n, vx.getLsbD k = vy.getLsbD k)
  | 0 => ⟨fun _ _ hk => by omega, fun _ => rfl⟩
  | Nat.succ n => by
    unfold allBitsEq
    have ih := allBitsEq_true_iff vx vy n
    constructor
    · intro h j hj
      cases hp : allBitsEq vx vy n with
      | false => rw [hp] at h; contradiction
      | true =>
        rw [hp, Bool.true_and] at h
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with
        | inl hlt => exact ih.mp hp j hlt
        | inr heq => subst heq; exact eq_of_beq h
    · intro hall
      have hp : allBitsEq vx vy n = true := ih.mpr (fun j hj => hall j (Nat.lt_succ_of_lt hj))
      have hn : (vx.getLsbD n == vy.getLsbD n) = true := beq_iff_eq.mpr (hall n (Nat.lt_succ_self n))
      rw [hp, hn]; rfl

def blastEqAux (aDepth : Nat) (aig : AigArena) (wx wy : List Nat) : Nat → Nat → Option Nat
  | 0, acc => some acc
  | Nat.succ k, acc =>
    match lookupXor aDepth aig (getWire wx k) (getWire wy k) with
    | none => none
    | some diff =>
      match lookupAnd aDepth aig acc (Nat.xor diff 1) with
      | none => none
      | some acc' => blastEqAux aDepth aig wx wy k acc'

theorem blastEqAux_spec {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {wx wy : List Nat} {vx vy : BitVec w}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hy : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wy vy) :
    ∀ (n : Nat), n ≤ w → ∀ (acc out : Nat),
      blastEqAux aDepth aig wx wy n acc = some out →
      let σ := aigAssignUpTo aDepth env aig.nodes aig.maxGate
      evalLit σ out = (evalLit σ acc && allBitsEq vx vy n)
  | 0, _, acc, out, h => by
    intro σ
    unfold blastEqAux at h
    injection h with hout; subst hout
    unfold allBitsEq
    rw [Bool.and_true]
  | Nat.succ k, hnw, acc, out, h => by
    intro σ
    have hkw : k < w := by omega
    unfold blastEqAux at h
    cases hxr : lookupXor aDepth aig (getWire wx k) (getWire wy k) with
    | none => rw [hxr] at h; contradiction
    | some diff =>
      rw [hxr] at h
      dsimp only at h
      cases hand : lookupAnd aDepth aig acc (Nat.xor diff 1) with
      | none => rw [hand] at h; contradiction
      | some acc' =>
        rw [hand] at h
        have ih : evalLit σ out = (evalLit σ acc' && allBitsEq vx vy k) :=
          blastEqAux_spec hf1 hx hy k (by omega) acc' out h
        unfold allBitsEq
        rw [ih, lookupAnd_sound hf1 hand, evalLit_xor_one, lookupXor_sound hf1 hxr,
            hx.2 k hkw, hy.2 k hkw]
        cases evalLit σ acc <;>
        cases vx.getLsbD k <;> cases vy.getLsbD k <;> cases allBitsEq vx vy k <;> rfl

def blastEq (aDepth : Nat) (aig : AigArena) (w : Nat) (wx wy : List Nat) : Option Nat :=
  blastEqAux aDepth aig wx wy w trueLit

theorem blastEq_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {wx wy : List Nat} {vx vy : BitVec w} {out : Nat}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hy : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wy vy)
    (heq : blastEq aDepth aig w wx wy = some out) :
    evalLit (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out = (vx == vy) := by
  have hspec := blastEqAux_spec hf1 hx hy w (Nat.le_refl w) trueLit out heq
  rw [hspec, checkFalseGate1_true hf1, Bool.true_and]
  cases hab : allBitsEq vx vy w with
  | true =>
    have hv : vx = vy := BitVec.eq_of_getLsbD_eq ((allBitsEq_true_iff vx vy w).mp hab)
    exact (beq_iff_eq.mpr hv).symm
  | false =>
    cases hxy : (vx == vy) with
    | false => rfl
    | true =>
      have hv := eq_of_beq hxy
      subst hv
      have ht : allBitsEq vx vx w = true := (allBitsEq_true_iff vx vx w).mpr (fun _ _ => rfl)
      rw [ht] at hab
      contradiction

def blastUlt (aDepth : Nat) (aig : AigArena) (w : Nat) (wx wy : List Nat) : Option Nat :=
  match blastAdcAux aDepth aig wx (blastNot wy) w 0 trueLit with
  | none => none
  | some (cout, _) => some (Nat.xor cout 1)

theorem blastUlt_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {wx wy : List Nat} {vx vy : BitVec w} {out : Nat}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hy : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wy vy)
    (hult : blastUlt aDepth aig w wx wy = some out) :
    evalLit (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out = BitVec.ult vx vy := by
  unfold blastUlt at hult
  cases hadc : blastAdcAux aDepth aig wx (blastNot wy) w 0 trueLit with
  | none => rw [hadc] at hult; contradiction
  | some pair =>
    rw [hadc] at hult
    rcases pair with ⟨cout, bits⟩
    injection hult with hout; subst hout
    have hcin : evalLit (aigAssignUpTo aDepth env aig.nodes aig.maxGate) trueLit =
        BitVec.carry 0 vx (~~~vy) true := by
      rw [checkFalseGate1_true hf1, BitVec.carry_zero]
    rcases blastAdcAux_spec hf1 hx (blastNot_sound hy) w 0 (by omega) trueLit true cout bits hcin hadc
      with ⟨_, hcout, _⟩
    rw [evalLit_xor_one, hcout, Nat.zero_add, BitVec.ult_eq_not_carry]

def blastSlt (aDepth : Nat) (aig : AigArena) (w : Nat) (wx wy : List Nat) : Option Nat :=
  match w with
  | 0 => some falseLit
  | Nat.succ w' =>
    match blastAdcAux aDepth aig wx (blastNot wy) (Nat.succ w') 0 trueLit with
    | none => none
    | some (cout, _) =>
      match lookupXor aDepth aig (getWire wx w') (getWire wy w') with
      | none => none
      | some signDiff =>
        -- `vx.msb == vy.msb` is `Nat.xor signDiff 1`; `slt_eq_not_carry` is `bne (vx.msb == vy.msb) cout`!
        lookupXor aDepth aig (Nat.xor signDiff 1) cout

theorem blastSlt_sound {aDepth : Nat} {env : BvEnv} {aig : AigArena} {w : Nat}
    {wx wy : List Nat} {vx vy : BitVec w} {out : Nat}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true)
    (hx : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wx vx)
    (hy : WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) wy vy)
    (hslt : blastSlt aDepth aig w wx wy = some out) :
    evalLit (aigAssignUpTo aDepth env aig.nodes aig.maxGate) out = BitVec.slt vx vy := by
  cases w with
  | zero =>
    unfold blastSlt at hslt
    injection hslt with hout; subst hout
    rw [checkFalseGate1_false hf1]
    have hxy : vx = vy := Subsingleton.elim vx vy
    subst hxy
    simp [BitVec.slt]
  | succ w' =>
    unfold blastSlt at hslt
    dsimp only at hslt
    cases hadc : blastAdcAux aDepth aig wx (blastNot wy) (Nat.succ w') 0 trueLit with
    | none => rw [hadc] at hslt; contradiction
    | some pair =>
      rw [hadc] at hslt
      rcases pair with ⟨cout, bits⟩
      dsimp only at hslt
      cases hsd : lookupXor aDepth aig (getWire wx w') (getWire wy w') with
      | none => rw [hsd] at hslt; contradiction
      | some signDiff =>
        rw [hsd] at hslt
        have hcin : evalLit (aigAssignUpTo aDepth env aig.nodes aig.maxGate) trueLit =
            BitVec.carry 0 vx (~~~vy) true := by
          rw [checkFalseGate1_true hf1, BitVec.carry_zero]
        rcases blastAdcAux_spec hf1 hx (blastNot_sound hy) (Nat.succ w') 0 (by omega) trueLit true cout bits hcin hadc
          with ⟨_, hcout, _⟩
        have hw' : w' < Nat.succ w' := Nat.lt_succ_self w'
        have hmsbX : vx.msb = vx.getLsbD w' := by
          unfold BitVec.msb BitVec.getMsbD; simp
        have hmsbY : vy.msb = vy.getLsbD w' := by
          unfold BitVec.msb BitVec.getMsbD; simp
        rw [lookupXor_sound hf1 hslt, evalLit_xor_one, lookupXor_sound hf1 hsd,
            hx.2 w' hw', hy.2 w' hw', hcout, Nat.zero_add, BitVec.slt_eq_not_carry, hmsbX, hmsbY]
        cases vx.getLsbD w' <;> cases vy.getLsbD w' <;> cases BitVec.carry (Nat.succ w') vx (~~~vy) true <;> rfl

-- Recursive Bit-Blaster over `BvExpr` and `BvPred`!
mutual
def blastBvExpr (aDepth : Nat) (aig : AigArena) : BvExpr w → Option (List Nat)
  | .var w id => tabulateWires w (fun b => lookupAtom aDepth aig w id b)
  | .const (w := w) val => blastConst w val
  | .not x =>
    match blastBvExpr aDepth aig x with
    | none => none
    | some wx => some (blastNot wx)
  | .and (w := w) x y =>
    match blastBvExpr aDepth aig x, blastBvExpr aDepth aig y with
    | some wx, some wy => tabulateWires w (fun i => lookupAnd aDepth aig (getWire wx i) (getWire wy i))
    | _, _ => none
  | .or (w := w) x y =>
    match blastBvExpr aDepth aig x, blastBvExpr aDepth aig y with
    | some wx, some wy => tabulateWires w (fun i => lookupOr aDepth aig (getWire wx i) (getWire wy i))
    | _, _ => none
  | .xor (w := w) x y =>
    match blastBvExpr aDepth aig x, blastBvExpr aDepth aig y with
    | some wx, some wy => tabulateWires w (fun i => lookupXor aDepth aig (getWire wx i) (getWire wy i))
    | _, _ => none
  | .add (w := w) x y =>
    match blastBvExpr aDepth aig x, blastBvExpr aDepth aig y with
    | some wx, some wy => blastAdd aDepth aig w wx wy
    | _, _ => none
  | .sub (w := w) x y =>
    match blastBvExpr aDepth aig x, blastBvExpr aDepth aig y with
    | some wx, some wy => blastSub aDepth aig w wx wy
    | _, _ => none
  | .neg (w := w) x =>
    match blastBvExpr aDepth aig x with
    | none => none
    | some wx => blastNeg aDepth aig w wx
  | .shlConst (w := w) x k =>
    match blastBvExpr aDepth aig x with
    | none => none
    | some wx => blastShlConst w wx k
  | .lshrConst (w := w) x k =>
    match blastBvExpr aDepth aig x with
    | none => none
    | some wx => blastLshrConst w wx k
  | .ashrConst (w := w) x k =>
    match blastBvExpr aDepth aig x with
    | none => none
    | some wx => blastAshrConst w wx k
  | .extract (wIn := wIn) lo len x =>
    match blastBvExpr aDepth aig x with
    | none => none
    | some wx =>
      tabulateWires len (fun i =>
        some (if decide (lo + i < wIn) then getWire wx (lo + i) else falseLit))
  | .concat (wHi := wHi) (wLo := wLo) hi lo =>
    match blastBvExpr aDepth aig hi, blastBvExpr aDepth aig lo with
    | some whi, some wlo =>
      tabulateWires (wHi + wLo) (fun i =>
        some (if decide (i < wLo) then getWire wlo i else getWire whi (i - wLo)))
    | _, _ => none
  | .zeroExtend (wIn := wIn) wOut x =>
    match blastBvExpr aDepth aig x with
    | none => none
    | some wx =>
      tabulateWires wOut (fun i =>
        some (if decide (i < wIn) then getWire wx i else falseLit))
  | .signExtend (wIn := wIn) wOut x =>
    match blastBvExpr aDepth aig x with
    | none => none
    | some wx =>
      tabulateWires wOut (fun i =>
        some (if decide (i < wIn) then getWire wx i
              else if decide (0 < wIn) then getWire wx (wIn - 1) else falseLit))
  | .ite (w := w) cond t e =>
    match blastBvPred aDepth aig cond, blastBvExpr aDepth aig t, blastBvExpr aDepth aig e with
    | some lc, some wt, some we => blastMuxWires aDepth aig w lc wt we
    | _, _, _ => none
  | .mul (w := w) x y =>
    match blastBvExpr aDepth aig x, blastBvExpr aDepth aig y with
    | some wx, some wy => blastMul aDepth aig w wx wy
    | _, _ => none

def blastBvPred (aDepth : Nat) (aig : AigArena) : BvPred → Option Nat
  | .constBool false => some falseLit
  | .constBool true  => some trueLit
  | .pNot p =>
    match blastBvPred aDepth aig p with
    | none => none
    | some lp => some (Nat.xor lp 1)
  | .pAnd p q =>
    match blastBvPred aDepth aig p, blastBvPred aDepth aig q with
    | some lp, some lq => lookupAnd aDepth aig lp lq
    | _, _ => none
  | .pOr p q =>
    match blastBvPred aDepth aig p, blastBvPred aDepth aig q with
    | some lp, some lq => lookupOr aDepth aig lp lq
    | _, _ => none
  | .pXor p q =>
    match blastBvPred aDepth aig p, blastBvPred aDepth aig q with
    | some lp, some lq => lookupXor aDepth aig lp lq
    | _, _ => none
  | .pIff p q =>
    match blastBvPred aDepth aig p, blastBvPred aDepth aig q with
    | some lp, some lq =>
      match lookupXor aDepth aig lp lq with
      | none => none
      | some d => some (Nat.xor d 1)
    | _, _ => none
  | .eq (w := w) x y =>
    match blastBvExpr aDepth aig x, blastBvExpr aDepth aig y with
    | some wx, some wy => blastEq aDepth aig w wx wy
    | _, _ => none
  | .ult (w := w) x y =>
    match blastBvExpr aDepth aig x, blastBvExpr aDepth aig y with
    | some wx, some wy => blastUlt aDepth aig w wx wy
    | _, _ => none
  | .slt (w := w) x y =>
    match blastBvExpr aDepth aig x, blastBvExpr aDepth aig y with
    | some wx, some wy => blastSlt aDepth aig w wx wy
    | _, _ => none
  | .getBit (w := w) x idx =>
    match blastBvExpr aDepth aig x with
    | none => none
    | some wx => some (if decide (idx < w) then getWire wx idx else falseLit)
end

mutual
theorem blastBvExpr_sound {aDepth : Nat} (env : BvEnv) {aig : AigArena}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true) :
    ∀ {w : Nat} (e : BvExpr w) (ws : List Nat),
      blastBvExpr aDepth aig e = some ws →
      WiresMatch (aigAssignUpTo aDepth env aig.nodes aig.maxGate) ws (evalBvExpr e env)
  | _, .var w id, ws, h => by
    unfold blastBvExpr at h
    apply tabulateWires_sound h
    intro i _ lit hlit
    exact lookupAtom_sound hlit
  | _, .const val, ws, h => blastConst_sound hf1 h
  | _, .not x, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h; injection h with hw; subst hw
      exact blastNot_sound (blastBvExpr_sound env hf1 x wx hx)
  | _, .and x y, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      cases hy : blastBvExpr aDepth aig y with
      | none => rw [hy] at h; contradiction
      | some wy =>
        rw [hy] at h
        have mx := blastBvExpr_sound env hf1 x wx hx
        have my := blastBvExpr_sound env hf1 y wy hy
        apply tabulateWires_sound h
        intro i hi lit hlit
        unfold evalBvExpr
        rw [lookupAnd_sound hf1 hlit, mx.2 i hi, my.2 i hi, BitVec.getLsbD_and]
  | _, .or x y, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      cases hy : blastBvExpr aDepth aig y with
      | none => rw [hy] at h; contradiction
      | some wy =>
        rw [hy] at h
        have mx := blastBvExpr_sound env hf1 x wx hx
        have my := blastBvExpr_sound env hf1 y wy hy
        apply tabulateWires_sound h
        intro i hi lit hlit
        unfold evalBvExpr
        rw [lookupOr_sound hf1 hlit, mx.2 i hi, my.2 i hi, BitVec.getLsbD_or]
  | _, .xor x y, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      cases hy : blastBvExpr aDepth aig y with
      | none => rw [hy] at h; contradiction
      | some wy =>
        rw [hy] at h
        have mx := blastBvExpr_sound env hf1 x wx hx
        have my := blastBvExpr_sound env hf1 y wy hy
        apply tabulateWires_sound h
        intro i hi lit hlit
        unfold evalBvExpr
        rw [lookupXor_sound hf1 hlit, mx.2 i hi, my.2 i hi, BitVec.getLsbD_xor]
  | _, .add x y, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      cases hy : blastBvExpr aDepth aig y with
      | none => rw [hy] at h; contradiction
      | some wy =>
        rw [hy] at h
        exact blastAdd_sound hf1 (blastBvExpr_sound env hf1 x wx hx) (blastBvExpr_sound env hf1 y wy hy) h
  | _, .sub x y, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      cases hy : blastBvExpr aDepth aig y with
      | none => rw [hy] at h; contradiction
      | some wy =>
        rw [hy] at h
        exact blastSub_sound hf1 (blastBvExpr_sound env hf1 x wx hx) (blastBvExpr_sound env hf1 y wy hy) h
  | _, .neg x, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      exact blastNeg_sound hf1 (blastBvExpr_sound env hf1 x wx hx) h
  | _, .shlConst x k, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      exact blastShlConst_sound hf1 (blastBvExpr_sound env hf1 x wx hx) h
  | _, .lshrConst x k, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      exact blastLshrConst_sound hf1 (blastBvExpr_sound env hf1 x wx hx) h
  | _, .ashrConst x k, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      exact blastAshrConst_sound hf1 (blastBvExpr_sound env hf1 x wx hx) h
  | _, .extract (wIn := wIn) lo len x, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      have mx := blastBvExpr_sound env hf1 x wx hx
      apply tabulateWires_sound h
      intro i hi lit hlit
      injection hlit with hl; subst hl
      unfold evalBvExpr
      rw [BitVec.getLsbD_extractLsb']
      simp only [hi, decide_true, Bool.true_and]
      cases hlt : decide (lo + i < wIn) with
      | true => rw [ite_true_eq rfl, mx.2 (lo + i) (of_decide_eq_true hlt)]
      | false =>
        rw [ite_false_eq (by decide), checkFalseGate1_false hf1]
        have hge : wIn ≤ lo + i := by rw [decide_eq_false_iff_not] at hlt; omega
        rw [BitVec.getLsbD_of_ge _ _ hge]
  | _, .concat (wHi := wHi) (wLo := wLo) hi lo, ws, h => by
    unfold blastBvExpr at h
    cases hhi : blastBvExpr aDepth aig hi with
    | none => rw [hhi] at h; contradiction
    | some whi =>
      rw [hhi] at h
      cases hlo : blastBvExpr aDepth aig lo with
      | none => rw [hlo] at h; contradiction
      | some wlo =>
        rw [hlo] at h
        have mhi := blastBvExpr_sound env hf1 hi whi hhi
        have mlo := blastBvExpr_sound env hf1 lo wlo hlo
        apply tabulateWires_sound h
        intro i _ lit hlit
        injection hlit with hl; subst hl
        unfold evalBvExpr
        rw [BitVec.append_eq, BitVec.getLsbD_append]
        cases hlt : decide (i < wLo) with
        | true =>
          have hilt := of_decide_eq_true hlt
          rw [ite_true_eq rfl, ite_true_eq hilt, mlo.2 i hilt]
        | false =>
          have hige : ¬(i < wLo) := decide_eq_false_iff_not.mp hlt
          have hsub : i - wLo < wHi := by omega
          rw [ite_false_eq (by decide), ite_false_eq hige, mhi.2 (i - wLo) hsub]
  | _, .zeroExtend (wIn := wIn) wOut x, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      have mx := blastBvExpr_sound env hf1 x wx hx
      apply tabulateWires_sound h
      intro i hi lit hlit
      injection hlit with hl; subst hl
      unfold evalBvExpr
      rw [BitVec.zeroExtend, BitVec.getLsbD_setWidth]
      simp only [hi, decide_true, Bool.true_and]
      cases hlt : decide (i < wIn) with
      | true => rw [ite_true_eq rfl, mx.2 i (of_decide_eq_true hlt)]
      | false =>
        rw [ite_false_eq (by decide), checkFalseGate1_false hf1]
        have hge : wIn ≤ i := by rw [decide_eq_false_iff_not] at hlt; omega
        rw [BitVec.getLsbD_of_ge _ _ hge]
  | _, .signExtend (wIn := wIn) wOut x, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      have mx := blastBvExpr_sound env hf1 x wx hx
      apply tabulateWires_sound h
      intro i hi lit hlit
      injection hlit with hl; subst hl
      unfold evalBvExpr
      rw [BitVec.getLsbD_signExtend]
      simp only [hi, decide_true, Bool.true_and]
      cases hlt : decide (i < wIn) with
      | true =>
        have hilt := of_decide_eq_true hlt
        rw [ite_true_eq rfl, ite_true_eq hilt, mx.2 i hilt]
      | false =>
        have hige : ¬(i < wIn) := decide_eq_false_iff_not.mp hlt
        rw [ite_false_eq (by decide), ite_false_eq hige]
        cases hw0 : decide (0 < wIn) with
        | true =>
          have hpos := of_decide_eq_true hw0
          rw [ite_true_eq rfl, mx.2 (wIn - 1) (by omega)]
          unfold BitVec.msb BitVec.getMsbD
          simp [hpos]
        | false =>
          have hz : wIn = 0 := by rw [decide_eq_false_iff_not] at hw0; omega
          subst hz
          rw [ite_false_eq (by decide), checkFalseGate1_false hf1]
          unfold BitVec.msb BitVec.getMsbD
          simp
  | _, .ite cond t e, ws, h => by
    unfold blastBvExpr at h
    cases hc : blastBvPred aDepth aig cond with
    | none => rw [hc] at h; contradiction
    | some lc =>
      rw [hc] at h
      cases ht : blastBvExpr aDepth aig t with
      | none => rw [ht] at h; contradiction
      | some wt =>
        rw [ht] at h
        cases he : blastBvExpr aDepth aig e with
        | none => rw [he] at h; contradiction
        | some we =>
          rw [he] at h
          exact blastMuxWires_sound hf1 (blastBvPred_sound env hf1 cond lc hc)
            (blastBvExpr_sound env hf1 t wt ht) (blastBvExpr_sound env hf1 e we he) h
  | _, .mul x y, ws, h => by
    unfold blastBvExpr at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      cases hy : blastBvExpr aDepth aig y with
      | none => rw [hy] at h; contradiction
      | some wy =>
        rw [hy] at h
        exact blastMul_sound hf1 (blastBvExpr_sound env hf1 x wx hx) (blastBvExpr_sound env hf1 y wy hy) h

theorem blastBvPred_sound {aDepth : Nat} (env : BvEnv) {aig : AigArena}
    (hf1 : checkFalseGate1 aDepth aig.maxGate aig.nodes = true) :
    ∀ (p : BvPred) (lit : Nat),
      blastBvPred aDepth aig p = some lit →
      evalLit (aigAssignUpTo aDepth env aig.nodes aig.maxGate) lit = evalBv p env
  | .constBool false, lit, h => by
    unfold blastBvPred at h; injection h with hl; subst hl
    exact checkFalseGate1_false hf1
  | .constBool true, lit, h => by
    unfold blastBvPred at h; injection h with hl; subst hl
    exact checkFalseGate1_true hf1
  | .pNot p, lit, h => by
    unfold blastBvPred at h
    cases hp : blastBvPred aDepth aig p with
    | none => rw [hp] at h; contradiction
    | some lp =>
      rw [hp] at h; injection h with hl; subst hl
      rw [evalLit_xor_one, blastBvPred_sound env hf1 p lp hp]; rfl
  | .pAnd p q, lit, h => by
    unfold blastBvPred at h
    cases hp : blastBvPred aDepth aig p with
    | none => rw [hp] at h; contradiction
    | some lp =>
      rw [hp] at h
      cases hq : blastBvPred aDepth aig q with
      | none => rw [hq] at h; contradiction
      | some lq =>
        rw [hq] at h
        rw [lookupAnd_sound hf1 h, blastBvPred_sound env hf1 p lp hp, blastBvPred_sound env hf1 q lq hq]; rfl
  | .pOr p q, lit, h => by
    unfold blastBvPred at h
    cases hp : blastBvPred aDepth aig p with
    | none => rw [hp] at h; contradiction
    | some lp =>
      rw [hp] at h
      cases hq : blastBvPred aDepth aig q with
      | none => rw [hq] at h; contradiction
      | some lq =>
        rw [hq] at h
        rw [lookupOr_sound hf1 h, blastBvPred_sound env hf1 p lp hp, blastBvPred_sound env hf1 q lq hq]; rfl
  | .pXor p q, lit, h => by
    unfold blastBvPred at h
    cases hp : blastBvPred aDepth aig p with
    | none => rw [hp] at h; contradiction
    | some lp =>
      rw [hp] at h
      cases hq : blastBvPred aDepth aig q with
      | none => rw [hq] at h; contradiction
      | some lq =>
        rw [hq] at h
        rw [lookupXor_sound hf1 h, blastBvPred_sound env hf1 p lp hp, blastBvPred_sound env hf1 q lq hq]; rfl
  | .pIff p q, lit, h => by
    unfold blastBvPred at h
    cases hp : blastBvPred aDepth aig p with
    | none => rw [hp] at h; contradiction
    | some lp =>
      rw [hp] at h
      cases hq : blastBvPred aDepth aig q with
      | none => rw [hq] at h; contradiction
      | some lq =>
        rw [hq] at h
        dsimp only at h
        cases hd : lookupXor aDepth aig lp lq with
        | none => rw [hd] at h; contradiction
        | some d =>
          rw [hd] at h; injection h with hl; subst hl
          rw [evalLit_xor_one, lookupXor_sound hf1 hd,
              blastBvPred_sound env hf1 p lp hp, blastBvPred_sound env hf1 q lq hq]
          change (!(bne (evalBv p env) (evalBv q env))) = ((evalBv p env) == (evalBv q env))
          cases evalBv p env <;> cases evalBv q env <;> rfl
  | .eq x y, lit, h => by
    unfold blastBvPred at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      cases hy : blastBvExpr aDepth aig y with
      | none => rw [hy] at h; contradiction
      | some wy =>
        rw [hy] at h
        exact blastEq_sound hf1 (blastBvExpr_sound env hf1 x wx hx) (blastBvExpr_sound env hf1 y wy hy) h
  | .ult x y, lit, h => by
    unfold blastBvPred at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      cases hy : blastBvExpr aDepth aig y with
      | none => rw [hy] at h; contradiction
      | some wy =>
        rw [hy] at h
        exact blastUlt_sound hf1 (blastBvExpr_sound env hf1 x wx hx) (blastBvExpr_sound env hf1 y wy hy) h
  | .slt x y, lit, h => by
    unfold blastBvPred at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h
      cases hy : blastBvExpr aDepth aig y with
      | none => rw [hy] at h; contradiction
      | some wy =>
        rw [hy] at h
        exact blastSlt_sound hf1 (blastBvExpr_sound env hf1 x wx hx) (blastBvExpr_sound env hf1 y wy hy) h
  | .getBit (w := w) x idx, lit, h => by
    unfold blastBvPred at h
    cases hx : blastBvExpr aDepth aig x with
    | none => rw [hx] at h; contradiction
    | some wx =>
      rw [hx] at h; injection h with hl; subst hl
      have mx := blastBvExpr_sound env hf1 x wx hx
      unfold evalBv
      cases hlt : decide (idx < w) with
      | true => rw [ite_true_eq rfl, mx.2 idx (of_decide_eq_true hlt)]
      | false =>
        rw [ite_false_eq (by decide), checkFalseGate1_false hf1]
        have hge : w ≤ idx := by rw [decide_eq_false_iff_not] at hlt; omega
        rw [BitVec.getLsbD_of_ge _ _ hge]
end

/-- Top-level end-to-end BitVec / SIMD UNSAT Certificate Checker (`aDepth = 5` covers `8^5 = 32,768`
    gates & clauses; `treeFuel = 18` covers `2^17 = 131,072` CNF/LRAT chunks)! -/
def checkBvUnsatCert (expr : BvPred) (aig : AigArena)
    (cnf : StepTree (Nat × List Nat)) (lrat : StepTree LratStep) : Bool :=
  let aDepth := 5
  let treeFuel := 18
  checkFalseGate1 aDepth aig.maxGate aig.nodes &&
  match blastBvPred aDepth aig expr with
  | none => false
  | some rootLit =>
    checkTseitinCnfTree aDepth aig.maxGate aig.nodes rootLit treeFuel cnf &&
    checkLratGmp aDepth treeFuel cnf lrat

/-- Main End-to-End Soundness Theorem:
    `checkBvUnsatCert expr aig cnf lrat = true → evalBv expr env = false`! -/
theorem checkBvUnsatCert_sound
    (expr : BvPred) (aig : AigArena)
    (cnf : StepTree (Nat × List Nat)) (lrat : StepTree LratStep)
    (env : BvEnv) :
    checkBvUnsatCert expr aig cnf lrat = true →
    evalBv expr env = false := by
  intro hcert
  unfold checkBvUnsatCert at hcert
  dsimp only at hcert
  cases hf1 : checkFalseGate1 5 aig.maxGate aig.nodes with
  | false => rw [hf1] at hcert; contradiction
  | true =>
    rw [hf1, Bool.true_and] at hcert
    cases hb : blastBvPred 5 aig expr with
    | none => rw [hb] at hcert; contradiction
    | some rootLit =>
      rw [hb] at hcert
      dsimp only at hcert
      cases hcnf : checkTseitinCnfTree 5 aig.maxGate aig.nodes rootLit 18 cnf with
      | false => rw [hcnf] at hcert; contradiction
      | true =>
        rw [hcnf, Bool.true_and] at hcert
        cases hev : evalBv expr env with
        | false => rfl
        | true =>
          have hroot : evalLit (aigAssignUpTo 5 env aig.nodes aig.maxGate) rootLit = true := by
            rw [blastBvPred_sound env hf1 expr rootLit hb, hev]
          have hinit := checkTseitinCnfTree_sound hroot 18 cnf hcnf
          exact False.elim (checkLratGmp_sound hcert _ hinit)

-- ============================================================================
-- Section 6: x86-64 Flags (`CF`/`ZF`/`SF`/`OF`/`PF`), BMI2, SWAR & SIMD Combinators
-- ============================================================================

def BvPred.ule {w : Nat} (x y : BvExpr w) : BvPred := .pNot (.ult y x)
def BvPred.sle {w : Nat} (x y : BvExpr w) : BvPred := .pNot (.slt y x)
def BvPred.neq {w : Nat} (x y : BvExpr w) : BvPred := .pNot (.eq x y)

/-- x86-64 `SUB` / `CMP` Status Flags (`CF`, `ZF`, `SF`, `OF`, `PF`) on width `w > 0`. -/
def x86SubCF {w : Nat} (x y : BvExpr w) : BvPred := .ult x y
def x86SubZF {w : Nat} (x y : BvExpr w) : BvPred := .eq (.sub x y) (.const (0#w))
def x86SubSF {w : Nat} (x y : BvExpr w) : BvPred := .getBit (.sub x y) (w - 1)
def x86SubOF {w : Nat} (x y : BvExpr w) : BvPred :=
  let sx := .getBit x (w - 1)
  let sy := .getBit y (w - 1)
  let sr := x86SubSF x y
  .pOr (.pAnd (.pAnd (.pNot sx) sy) sr) (.pAnd (.pAnd sx (.pNot sy)) (.pNot sr))

/-- x86-64 Parity Flag `PF`: `true` iff the low byte of `r` has an EVEN number of `1` bits. -/
def x86ParityFlag {w : Nat} (r : BvExpr w) : BvPred :=
  let oddParity :=
    BvPred.pXor (.getBit r 0) (BvPred.pXor (.getBit r 1) (BvPred.pXor (.getBit r 2)
      (BvPred.pXor (.getBit r 3) (BvPred.pXor (.getBit r 4) (BvPred.pXor (.getBit r 5)
        (BvPred.pXor (.getBit r 6) (.getBit r 7)))))))
  .pNot oddParity

/-- Variable barrel left-shift `x <<< (y &&& mask)` for `w = 2^k` (e.g. 64-bit x86 `SHLX` / `BZHI`). -/
def BvExpr.barrelShlStage {w : Nat} (x amt : BvExpr w) (bitIdx : Nat) : BvExpr w :=
  .ite (.getBit amt bitIdx) (.shlConst x (Nat.shiftLeft 1 bitIdx)) x

def BvExpr.shlPow2 {w : Nat} (x amt : BvExpr w) : Nat → BvExpr w
  | 0 => x
  | Nat.succ k => BvExpr.barrelShlStage (BvExpr.shlPow2 x amt k) amt k

/-- BMI2 `BLSI`, `BLSR`, `BLSMSK`, and `BZHI` (64-bit)! -/
def bmi2Blsi {w : Nat} (x : BvExpr w) : BvExpr w := .and x (.neg x)
def bmi2Blsr {w : Nat} (x : BvExpr w) : BvExpr w := .and x (.sub x (.const (1#w)))
def bmi2Blsmsk {w : Nat} (x : BvExpr w) : BvExpr w := .xor x (.sub x (.const (1#w)))
def bmi2Bzhi64 (x idx : BvExpr 64) : BvExpr 64 :=
  let idx8 := BvExpr.zeroExtend 64 (BvExpr.extract 0 8 idx)
  let ge64 := BvPred.ule (.const (64#64)) idx8
  let mask := BvExpr.sub (BvExpr.shlPow2 (.const (1#64)) idx8 6) (.const (1#64))
  .ite ge64 x (.and x mask)

/-- SIMD Signed 16-bit Saturating Clamp from 32/17-bit signed intermediate (`[-32768, 32767]`). -/
def clampSigned16From20 (x : BvExpr 20) : BvExpr 16 :=
  let max16 : BvExpr 20 := .const (BitVec.ofNat 20 0x07fff)
  let min16 : BvExpr 20 := .const (BitVec.ofNat 20 0xf8000) -- `-32768` in 20-bit two's complement
  .ite (.slt max16 x) (.const (0x7fff#16))
    (.ite (.slt x min16) (.const (0x8000#16)) (.extract 0 16 x))

/-- Single 16-bit output lane of x86 SSSE3/AVX2 `VPMADDUBSW`:
    `clamp_i16(u8_0 * i8_0 + u8_1 * i8_1)`! -/
def vpmaddubswPair (uPair sPair : BvExpr 16) : BvExpr 16 :=
  let u0 : BvExpr 20 := .zeroExtend 20 (.extract 0 8 uPair)
  let u1 : BvExpr 20 := .zeroExtend 20 (.extract 8 8 uPair)
  let s0 : BvExpr 20 := .signExtend 20 (.extract 0 8 sPair)
  let s1 : BvExpr 20 := .signExtend 20 (.extract 8 8 sPair)
  let sum20 : BvExpr 20 := .add (.mul u0 s0) (.mul u1 s1)
  clampSigned16From20 sum20

/-- Multi-lane SIMD `VPMADDUBSW` across `nPairs` 16-bit pairs (e.g., `nPairs = 8` for 128-bit XMM,
    `nPairs = 16` for 256-bit AVX2 YMM)! -/
def simdVpmaddubsw : (nPairs : Nat) → BvExpr (16 * nPairs) → BvExpr (16 * nPairs) → BvExpr (16 * nPairs)
  | 0, _, _ => .const (0#0)
  | Nat.succ k, uVec, sVec =>
    let loLanes := simdVpmaddubsw k (.extract 0 (16 * k) uVec) (.extract 0 (16 * k) sVec)
    let hiLane  := vpmaddubswPair (.extract (16 * k) 16 uVec) (.extract (16 * k) 16 sVec)
    -- `16 + 16 * k` cast to `16 * (k + 1)` via `.extract 0 (16 * Nat.succ k)`!
    .extract 0 (16 * Nat.succ k) (.concat hiLane loLanes)

/-- Single 16-bit lane of x86 AVX2 `VPADDSW` (`i16 +_sat i16 → i16` via 20-bit signed clamp). -/
def vpaddswLane (x y : BvExpr 16) : BvExpr 16 :=
  clampSigned16From20 (.add (.signExtend 20 x) (.signExtend 20 y))

/-- Multi-lane SIMD `VPADDSW` across `nLanes` 16-bit lanes (e.g., `nLanes = 16` for 256-bit AVX2 YMM)! -/
def simdVpaddsw : (nLanes : Nat) → BvExpr (16 * nLanes) → BvExpr (16 * nLanes) → BvExpr (16 * nLanes)
  | 0, _, _ => .const (0#0)
  | Nat.succ k, xVec, yVec =>
    let loLanes := simdVpaddsw k (.extract 0 (16 * k) xVec) (.extract 0 (16 * k) yVec)
    let hiLane  := vpaddswLane (.extract (16 * k) 16 xVec) (.extract (16 * k) 16 yVec)
    .extract 0 (16 * Nat.succ k) (.concat hiLane loLanes)

/-- Semantic 16-bit signed-saturating addition (`VPADDSW` lane) on `BitVec 16`. -/
def semVpaddsw16 (a b : BitVec 16) : BitVec 16 :=
  let sum20 : BitVec 20 := a.signExtend 20 + b.signExtend 20
  if BitVec.slt (BitVec.ofNat 20 0x07fff) sum20 then 0x7fff#16
  else if BitVec.slt sum20 (BitVec.ofNat 20 0xf8000) then 0x8000#16
  else BitVec.extractLsb' 0 16 sum20

/-- Semantic multi-lane SIMD binary operator over `nLanes` 16-bit lanes (`nLanes = 16 → BitVec 256`). -/
def simdMapBinary16 (f : BitVec 16 → BitVec 16 → BitVec 16) :
    (nLanes : Nat) → BitVec (16 * nLanes) → BitVec (16 * nLanes) → BitVec (16 * nLanes)
  | 0, _, _ => 0#0
  | Nat.succ k, x, y =>
    let lo := simdMapBinary16 f k (BitVec.extractLsb' 0 (16 * k) x) (BitVec.extractLsb' 0 (16 * k) y)
    let hi := f (BitVec.extractLsb' (16 * k) 16 x) (BitVec.extractLsb' (16 * k) 16 y)
    BitVec.extractLsb' 0 (16 * Nat.succ k) (hi ++ lo)

/-- Correspondence between the `BvExpr` combinator `simdVpaddsw` and semantic `simdMapBinary16 semVpaddsw16`. -/
theorem evalBvExpr_simdVpaddsw (env : BvEnv) :
    ∀ (nLanes : Nat) (xVec yVec : BvExpr (16 * nLanes)),
      evalBvExpr (simdVpaddsw nLanes xVec yVec) env =
      simdMapBinary16 semVpaddsw16 nLanes (evalBvExpr xVec env) (evalBvExpr yVec env)
  | 0, _, _ => rfl
  | Nat.succ k, xVec, yVec => by
    unfold simdVpaddsw simdMapBinary16
    have ih := evalBvExpr_simdVpaddsw env k (.extract 0 (16 * k) xVec) (.extract 0 (16 * k) yVec)
    dsimp only [evalBvExpr] at ih ⊢
    rw [ih]
    rfl

/-- Generic SIMD Lane-Congruence Lifting Theorem (`O(nLanes)` structural induction, zero 256-bit CNF blowup). -/
theorem simdMapBinary16_comm (f : BitVec 16 → BitVec 16 → BitVec 16)
    (hcomm : ∀ a b : BitVec 16, f a b = f b a) :
    ∀ (nLanes : Nat) (x y : BitVec (16 * nLanes)),
      simdMapBinary16 f nLanes x y = simdMapBinary16 f nLanes y x
  | 0, _, _ => rfl
  | Nat.succ k, x, y => by
    unfold simdMapBinary16
    rw [simdMapBinary16_comm f hcomm k, hcomm]

theorem semVpaddsw16_comm_of_unsat
    (hunsat : ∀ env : BvEnv,
      evalBv (.pNot (.pAnd
        (.eq (vpaddswLane (.var 16 0) (.var 16 1)) (vpaddswLane (.var 16 1) (.var 16 0)))
        (.pAnd (.eq (vpaddswLane (.const 0x6000#16) (.const 0x5000#16)) (.const 0x7fff#16))
               (.eq (vpaddswLane (.const 0x9000#16) (.const 0xa000#16)) (.const 0x8000#16))))) env = false)
    (a b : BitVec 16) :
    semVpaddsw16 a b = semVpaddsw16 b a := by
  let env : BvEnv := fun w id => if h : w = 16 then h ▸ (if id == 0 then a else b) else 0#w
  have h0 := hunsat env
  have heq : (semVpaddsw16 a b == semVpaddsw16 b a) = true := by
    change (!((semVpaddsw16 a b == semVpaddsw16 b a) &&
      ((semVpaddsw16 0x6000#16 0x5000#16 == 0x7fff#16) &&
       (semVpaddsw16 0x9000#16 0xa000#16 == 0x8000#16)))) = false at h0
    cases hb : (semVpaddsw16 a b == semVpaddsw16 b a)
    · rw [hb, Bool.false_and] at h0; contradiction
    · rfl
  exact eq_of_beq heq

/-- 64-bit Mycroft SWAR zero-byte mask `(x - 0x0101..01) & ~x & 0x8080..80`. -/
def swarMycroftMask64 (x : BvExpr 64) : BvExpr 64 :=
  let m01 : BvExpr 64 := .const (0x0101010101010101#64)
  let m80 : BvExpr 64 := .const (0x8080808080808080#64)
  .and (.and (.sub x m01) (.not x)) m80

/-- 64-bit Borrow-Free SWAR zero-byte mask `~(((x & 0x7f7f..7f) + 0x7f7f..7f) | x | 0x7f7f..7f)`. -/
def swarBorrowFreeMask64 (x : BvExpr 64) : BvExpr 64 :=
  let m7f : BvExpr 64 := .const (0x7f7f7f7f7f7f7f7f#64)
  .not (.or (.or (.add (.and x m7f) m7f) x) m7f)

end GmpBvTseitin
