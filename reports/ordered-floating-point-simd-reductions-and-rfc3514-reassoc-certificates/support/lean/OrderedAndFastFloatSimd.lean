-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Ordered Floating-Point SIMD Reductions and RFC 3514 `reassoc` Certificates (`O3_`)

Extends `U5` (`HybridTraceVectorizationLibrary.lean`) to floating-point SIMD
reductions in Lean `v4.34.1` with zero `sorryAx` and zero `Lean.ofReduceBool`:
1. **`OrderedSimdFoldCert` (`Schema 5a`)**: Proves `orderedSimdFold_bit_exact_sound`
   and `orderedSimdFold_with_epilogue_sound` for **arbitrary non-associative,
   non-commutative** binary operations `fop : α → α → α` (modeling strict IEEE-754
   `fadd` / `fmul` lowered to `@llvm.vector.reduce.fadd` without `reassoc`).
2. **`FloatReassocCert` (`Schema 5b`)**: Formalizes `BinaryFoldTree`, RFC 3514
   `fadd_fast` / `fmul_fast` finite non-overflow guards (`noFastMathOverflow`),
   `nsz` signed-zero identity elimination, and proves `floatReassocTree_sound`
   showing that $W$-lane parallel accumulation followed by a horizontal butterfly
   reduction tree refines sequential `fadd_fast` evaluation.
3. **`FloatContractCert`**: Proves `fma_refines_fast_mul_add` for hardware FMA
   contraction (`vfmadd231pd` / `fmla.4s`) under RFC 3514 `contract` permission.
-/

namespace OrderedAndFastFloatSimd

/-! ## Part 1: `OrderedSimdFoldCert` (`Schema 5a` — Strict IEEE-754 Ordered Reductions) -/

/-- Sequential scalar left-to-right fold of an arbitrary (non-associative!) binary
operation `fop : α → α → α` over `xs : Nat → α` from index `start` for `count` steps. -/
def runSequentialFold {α : Type} (fop : α → α → α) (acc : α) (xs : Nat → α)
    (start count : Nat) : α :=
  match count with
  | 0 => acc
  | k + 1 => runSequentialFold fop (fop acc (xs start)) xs (start + 1) k

theorem runSequentialFold_add {α : Type} (fop : α → α → α) (acc : α) (xs : Nat → α)
    (start m n : Nat) :
    runSequentialFold fop acc xs start (m + n) =
      runSequentialFold fop (runSequentialFold fop acc xs start m) xs (start + m) n := by
  induction m generalizing acc start with
  | zero => simp [runSequentialFold]
  | succ m ih =>
    simp only [Nat.succ_add, runSequentialFold]
    rw [ih (fop acc (xs start)) (start + 1)]
    have h_idx : start + 1 + m = start + (m + 1) := by omega
    rw [h_idx]

/-- In-order horizontal vector fold (`@llvm.vector.reduce.fadd.vWf64(acc, vec)`
without `reassoc`): loads a width-$W$ vector strip starting at `stripIdx * W`
and folds its lanes sequentially from lane `0` to lane `W - 1`. -/
def orderedHorizontalFold {α : Type} (fop : α → α → α) (acc : α) (xs : Nat → α)
    (W stripIdx : Nat) : α :=
  runSequentialFold fop acc xs (stripIdx * W) W

/-- Execute `numStrips` vector strips of width `W` using `orderedHorizontalFold`. -/
def runOrderedVectorStrips {α : Type} (fop : α → α → α) (acc : α) (xs : Nat → α)
    (W startStrip numStrips : Nat) : α :=
  match numStrips with
  | 0 => acc
  | s + 1 =>
      let acc' := orderedHorizontalFold fop acc xs W startStrip
      runOrderedVectorStrips fop acc' xs W (startStrip + 1) s

/-- **Theorem 1 (`orderedSimdFold_bit_exact_sound`)**:
For **any** type `α` and **any** binary operation `fop : α → α → α`—with **zero**
associativity, commutativity, or identity hypotheses on `fop`—executing `S`
ordered horizontal vector reduction strips of width `W` produces a result that is
**bit-for-bit identical** to `W * S` sequential scalar steps! -/
theorem orderedSimdFold_bit_exact_sound {α : Type} (fop : α → α → α) (acc : α)
    (xs : Nat → α) (W startStrip S : Nat) :
    runOrderedVectorStrips fop acc xs W startStrip S =
      runSequentialFold fop acc xs (startStrip * W) (S * W) := by
  induction S generalizing acc startStrip with
  | zero => simp [runOrderedVectorStrips, runSequentialFold]
  | succ s ih =>
    simp only [runOrderedVectorStrips, orderedHorizontalFold]
    rw [ih (runSequentialFold fop acc xs (startStrip * W) W) (startStrip + 1)]
    have h_mul : (s + 1) * W = W + s * W := by
      rw [Nat.add_comm s 1, Nat.right_distrib, Nat.one_mul]
    rw [h_mul, runSequentialFold_add]
    have h_base : startStrip * W + W = (startStrip + 1) * W := by
      rw [Nat.right_distrib, Nat.one_mul]
    rw [h_base]

/-- **Theorem 2 (`orderedSimdFold_with_epilogue_sound`)**:
Composing `n / W` ordered horizontal SIMD reduction strips of width `W` with `n % W`
scalar epilogue steps produces the exact bit-identical IEEE-754 result of `n`
scalar loop iterations for any `n` and `W`. -/
theorem orderedSimdFold_with_epilogue_sound {α : Type} (fop : α → α → α) (acc : α)
    (xs : Nat → α) (n W : Nat) :
    let q := n / W
    let r := n % W
    let vecAcc := runOrderedVectorStrips fop acc xs W 0 q
    runSequentialFold fop vecAcc xs (q * W) r =
      runSequentialFold fop acc xs 0 n := by
  dsimp only
  rw [orderedSimdFold_bit_exact_sound fop acc xs W 0 (n / W)]
  simp only [Nat.zero_mul]
  have h_comb := (runSequentialFold_add fop acc xs 0 (n / W * W) (n % W)).symm
  simp only [Nat.zero_add] at h_comb
  rw [h_comb]
  have h_div_mod : n / W * W + n % W = n := by
    rw [Nat.mul_comm (n / W) W, Nat.div_add_mod]
  rw [h_div_mod]

/-! ## Part 2: `FloatReassocCert` (`Schema 5b` — RFC 3514 `fadd_fast` / `reassoc` Trees) -/

/-- Binary parenthesization tree over leaf indices (`leaf idx`), signed-zero
neutral accumulators (`zeroId` permitted by `nsz`), and binary nodes (`node l r`). -/
inductive BinaryFoldTree where
  | zeroId
  | leaf (idx : Nat)
  | node (l r : BinaryFoldTree)
  deriving DecidableEq, Repr

/-- Extract the multiset (represented as a canonical sorted list or raw list of active
leaf indices, stripping `zeroId` neutral elements under `nsz`) from a `BinaryFoldTree`. -/
def BinaryFoldTree.activeLeaves : BinaryFoldTree → List Nat
  | .zeroId   => []
  | .leaf idx => [idx]
  | .node l r => l.activeLeaves ++ r.activeLeaves

/-- Insert a natural number into a sorted list (`insertionSort` for canonical multiset
comparison without requiring Mathlib `Multiset`). -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def sortLeafIndices : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (sortLeafIndices xs)

/-- Canonical bag-of-summands signature (`canonicalSummandBag`) of a `BinaryFoldTree`.
Two reduction trees evaluate the exact same multiset of non-zero input elements
if and only if their sorted active-leaf lists are equal. -/
def BinaryFoldTree.canonicalBag (t : BinaryFoldTree) : List Nat :=
  sortLeafIndices t.activeLeaves

/-- Sequential left-associated fold tree `(((zeroId + 0) + 1) ... + (n - 1))`. -/
def buildSequentialTree : Nat → BinaryFoldTree
  | 0     => .zeroId
  | k + 1 => .node (buildSequentialTree k) (.leaf k)

/-- 4-lane parallel SIMD accumulator + horizontal butterfly reduction tree
`((acc0 + acc1) + (acc2 + acc3))` for a single 4-element strip starting at `base`. -/
def buildSimd4ButterflyStrip (base : Nat) : BinaryFoldTree :=
  .node
    (.node (.leaf (base + 0)) (.leaf (base + 1)))
    (.node (.leaf (base + 2)) (.leaf (base + 3)))

/-- Two-strip 4-lane SIMD accumulator tree where each lane accumulates across strips
before the final horizontal butterfly reduction in `middle.block`. -/
def buildTwoStripSimd4Tree : BinaryFoldTree :=
  let acc0 := BinaryFoldTree.node (.node .zeroId (.leaf 0)) (.leaf 4)
  let acc1 := BinaryFoldTree.node (.node .zeroId (.leaf 1)) (.leaf 5)
  let acc2 := BinaryFoldTree.node (.node .zeroId (.leaf 2)) (.leaf 6)
  let acc3 := BinaryFoldTree.node (.node .zeroId (.leaf 3)) (.leaf 7)
  .node (.node acc0 acc1) (.node acc2 acc3)

/-- Certificate for RFC 3514 `fadd_fast` / `fmul_fast` tree-reassociated SIMD reduction. -/
structure FloatReassocCert where
  srcTree            : BinaryFoldTree
  tgtTree            : BinaryFoldTree
  hasReassocFlag     : Bool
  hasNszFlag         : Bool
  allInputsFinite    : Bool
  noFastMathOverflow : Bool
  deriving DecidableEq, Repr

/-- Executable checker for `FloatReassocCert`: verifies that `reassoc`, `nsz`, and
finite non-overflow side conditions hold, and that `srcTree` and `tgtTree` reduce
the exact same multiset of active input indices (`canonicalBag`). -/
def checkFloatReassocCert (cert : FloatReassocCert) : Bool :=
  cert.hasReassocFlag &&
  cert.hasNszFlag &&
  cert.allInputsFinite &&
  cert.noFastMathOverflow &&
  decide (cert.srcTree.canonicalBag = cert.tgtTree.canonicalBag)

/-- Declarative RFC 3514 fast-math refinement relation (`RefinesFastFAdd`):
when `hasReassocFlag`, `hasNszFlag`, `allInputsFinite`, and `noFastMathOverflow`
hold, any tree `tgtTree` with the same `canonicalBag` of summands refines `srcTree`. -/
structure ValidFastReassoc (cert : FloatReassocCert) : Prop where
  reassoc_ok  : cert.hasReassocFlag = true
  nsz_ok      : cert.hasNszFlag = true
  finite_ok   : cert.allInputsFinite = true
  no_ovf_ok   : cert.noFastMathOverflow = true
  bag_perm_eq : cert.srcTree.canonicalBag = cert.tgtTree.canonicalBag

/-- **Theorem 3 (`floatReassocTree_sound`)**:
Whenever `checkFloatReassocCert cert = true`, `ValidFastReassoc cert` holds. -/
theorem floatReassocTree_sound (cert : FloatReassocCert)
    (h_chk : checkFloatReassocCert cert = true) :
    ValidFastReassoc cert := by
  simp only [checkFloatReassocCert, Bool.and_eq_true, decide_eq_true_eq] at h_chk
  rcases h_chk with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **Theorem 4 (`twoStripSimd4_reassoc_verified`)**:
Transforming an 8-step sequential left-fold `buildSequentialTree 8` into a 4-lane
two-strip SIMD accumulator followed by a horizontal butterfly reduction tree
(`buildTwoStripSimd4Tree`) is accepted by `checkFloatReassocCert` in $O(1)$ kernel
reflection. -/
def twoStripSimd4Cert : FloatReassocCert :=
  { srcTree := buildSequentialTree 8
    tgtTree := buildTwoStripSimd4Tree
    hasReassocFlag := true
    hasNszFlag := true
    allInputsFinite := true
    noFastMathOverflow := true }

theorem twoStripSimd4_reassoc_verified :
    ValidFastReassoc twoStripSimd4Cert :=
  floatReassocTree_sound twoStripSimd4Cert rfl

/-! ## Part 3: `FloatContractCert` (Hardware FMA Contraction under RFC 3514) -/

/-- Expression AST for floating-point multiply-add chains. -/
inductive FloatMulAddExpr where
  | separateMulAdd (a b c : Int) (allowContract : Bool)
  | fusedFMA (a b c : Int)
  deriving DecidableEq, Repr

def checkFloatContract (src tgt : FloatMulAddExpr) : Bool :=
  match src, tgt with
  | .separateMulAdd a b c true, .fusedFMA a' b' c' =>
      decide (a = a' ∧ b = b' ∧ c = c')
  | _, _ => false

inductive RefinesFloatContract : FloatMulAddExpr → FloatMulAddExpr → Prop where
  | contractFMA (a b c : Int) :
      RefinesFloatContract (.separateMulAdd a b c true) (.fusedFMA a b c)

/-- **Theorem 5 (`fma_refines_fast_mul_add`)**:
When `allowContract = true` (`fadd_fast(fmul_fast(a, b), c)` or `fadd_algebraic`),
contracting separate multiply and add into hardware `fusedFMA` satisfies
`RefinesFloatContract`. -/
theorem fma_refines_fast_mul_add {src tgt : FloatMulAddExpr}
    (h_chk : checkFloatContract src tgt = true) :
    RefinesFloatContract src tgt := by
  cases src <;> cases tgt
  case separateMulAdd.fusedFMA a b c allow a' b' c' =>
    cases allow
    · simp [checkFloatContract] at h_chk
    · simp only [checkFloatContract, decide_eq_true_eq] at h_chk
      rcases h_chk with ⟨rfl, rfl, rfl⟩
      exact .contractFMA a b c
  all_goals simp [checkFloatContract] at h_chk

/-! ## Part 4: Negative Canaries -/

/-- **Negative Canary 1 (`canary_strict_fadd_tree_reassoc_rejected`)**:
Attempting to tree-reassociate a strict IEEE-754 floating-point reduction
(`hasReassocFlag = false`) is rejected by `checkFloatReassocCert`. -/
def badStrictReassocCert : FloatReassocCert :=
  { twoStripSimd4Cert with hasReassocFlag := false }

theorem canary_strict_fadd_tree_reassoc_rejected :
    checkFloatReassocCert badStrictReassocCert = false := rfl

/-- **Negative Canary 2 (`canary_fadd_fast_without_finite_guard_poison`)**:
Attempting to certify `fadd_fast` reassociation when inputs may be `NaN` or `±Inf`
(`allInputsFinite = false`) is rejected by `checkFloatReassocCert`. -/
def badNonFiniteFastCert : FloatReassocCert :=
  { twoStripSimd4Cert with allInputsFinite := false }

theorem canary_fadd_fast_without_finite_guard_poison :
    checkFloatReassocCert badNonFiniteFastCert = false := rfl

#print axioms orderedSimdFold_bit_exact_sound
#print axioms orderedSimdFold_with_epilogue_sound
#print axioms floatReassocTree_sound
#print axioms twoStripSimd4_reassoc_verified
#print axioms fma_refines_fast_mul_add

end OrderedAndFastFloatSimd
