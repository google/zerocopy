# Farkas certificates in Lean: checker soundness and completeness over scaled rational points, integer incompleteness and Chvátal–Gomory cuts, and range conditions for transferring bit-vector comparisons to the integers

## Summary

This package is a self-contained, Mathlib-free Lean 4 development (namespace `Toy.Farkas`, library `ToyFarkas`, Lean `v4.34.1`) of a Boolean checker `checkFarkas` for Farkas/Motzkin infeasibility certificates over finite systems of integer linear constraints `a · x ≤ b` and `a · x < b`, of its integer-tightened and cutting-plane variants, and of the range conditions under which comparisons between affine expressions over fixed-width bit-vectors may be decided over the integers. All 22 results below are kernel-checked: no declaration uses `sorry`, and every declaration of the library depends only on the axioms `propext`, `Classical.choice`, `Quot.sound`. Statements about rational points are made over scaled pairs `(d, p)` with `d > 0` standing for `p / d`; reading them as statements about rational numbers, or about real checkers, solvers and machine integers, is a separate modeling claim (see Applicability and the `Basis: derived (modeling bridge)` lines under Findings).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Results (the plain-language claim of each card, which states its key hypotheses). **The non-claims of every result are listed first under Boundaries; read them before relying on a result.**

- **R1a** (theorem; `checkFarkas_sound_scaled`, `checkFarkas_sound_int`, `checkFarkas_sound_scaled_posSupport`, `checkFarkas_sound_int_posSupport`): If the Boolean checker checkFarkas accepts a certificate cert for a finite list S of integer linear constraints (each a . x <= b or a . x < b), then no scaled point (d, p) with d > 0 satisfies S (checkFarkas_sound_scaled), and in particular no integer point satisfies S (checkFarkas_sound_int, the case d = 1); more precisely, already the premises that cert weights positively (posSupport cert S) have no such point (the _posSupport forms).
- **R1c** (theorem; `farkas_sound_scaled_of_nonneg_of_lhsVanishes_of_rhsContradicts`): If the multipliers are non-negative, the combined left-hand side Sum lambda_k a_k is the zero form in the dense semantics, and the combined conclusion 0 <= Sum lambda_k b_k (or 0 < ... when some positively weighted premise is strict) is false, then no scaled point (d, p) with d > 0 satisfies S.
- **R2a** (theorem; `SparseVec.eval_eq_denseDotOn_coeff_of_nodup_of_keys_mem`, `SparseVec.eval_eq_denseDot_coeff_of_keys_lt`): For a sparse linear form v (an association list that may repeat indices) and any duplicate-free index list ks containing every index of v, evaluating v at x equals the dense dot product Sum_{i in ks} coeff v i * x i, where coeff v i sums all coefficients recorded for i; the corollary takes ks = [0, ..., n-1] when every index of v is < n.
- **R2b** (theorem; `combineLhs_coeff`, `combineLhs_eval`): The unnormalized sparse combination combineLhs S cert (concatenated scaled premises) has, at each index i, dense coefficient Sum_k lambda_k * coeff(a_k, i), and its value at x is Sum_k lambda_k * (a_k . x), with multiplier k paired with constraint k.
- **R2d** (characterization; `SparseVec.isZero_iff_coeff_eq_zero`): The decidable zero test isZero v (every mentioned index has total coefficient 0) holds exactly when the dense coefficient function of v is identically zero.
- **R3a** (counterexample; `ce_farkas_negative_multiplier`): With multipliers (1, -1) the satisfiable system {x0 <= 1, x0 <= 2} combines to 0 <= -1: the left-hand side vanishes and the conclusion contradicts, with d = 1 > 0, yet x0 = 0 is a solution; only the non-negativity check fails.
- **R3b** (counterexample; `ce_farkas_strictness_ignored`, `ce_farkas_strict_flag_from_zero_weight`): Two strictness-bookkeeping errors make a Farkas checker unsound: (1) treating every combined conclusion as strict accepts 0 <= 0 as contradictory and 'certifies' the satisfiable {x0 <= 1, -x0 <= -1} with (1, 1), which rhsContradicts and checkFarkas both reject; (2) declaring the combination strict whenever some premise is strict, even one with multiplier 0, 'certifies' the satisfiable {x0 <= 1, -x0 <= -1, x1 < 5} with (1, 1, 0), which rhsContradicts rejects, and hence so does checkFarkas (its definition requires rhsContradicts = true; this last step follows by unfolding checkFarkas and is not a separate conjunct of ce_farkas_strict_flag_from_zero_weight).
- **R3d** (theorem; `checkFarkasTightened_sound_int`): If checkFarkas accepts a certificate for the integer-tightened system (each strict a . x < b replaced by a . x <= b - 1), then the original system has no integer solution x : Nat -> Int.
- **R3e** (counterexample; `ce_tightening_unsound_over_rat`): The tightened checker accepts (1, 1) for {x0 < 1, -x0 < 0}, which the scaled point (d, p) = (2, 1) with d > 0 satisfies (read through the rational modeling bridge: x0 = 1/2); the untightened checker rejects the same certificate. So integer tightening is not sound over scaled points; over integer points it is sound (R3d).
- **R3f** (counterexample; `ce_zero_test_index_blind`, `ce_zero_test_first_match`, `ce_zero_test_first_match_dupfree_inputs`): Zero tests that ignore the dense semantics make the checker unsound: (1) an index-blind test (all coefficients sum to 0) accepts x0 - x1 and 'certifies' the satisfiable {x0 - x1 <= -1} with (1); (2) a first-match test (read only the first entry per index) accepts [(0,0),(0,1)] and 'certifies' the satisfiable {0*x0 + 1*x0 <= -1} with (1); (3) the first-match failure arises even when every input constraint is duplicate-free: for {x0 <= 0, x0 <= -1} with (0, 1) the combination is [(0,0),(0,1)] and x0 = -1 is a solution. checkFarkas rejects all three.
- **R4a** (theorem; `farkas_complete_scaled`): Every finite list S of integer linear constraints (each a . x <= b or a . x < b) that has no scaled solution (d, p) with d > 0 has a certificate accepted by checkFarkas.
- **R4b** (impossibility; `ce_farkas_incomplete_int`): The system sysHalf = {2x0 <= 1, -2x0 <= -1} has no integer solution x : Nat -> Int, yet checkFarkas rejects every certificate cert : List Int for it.
- **R5a** (theorem; `cgCut_sound_int_of_nonneg_of_div_pos_of_divisible`, `cgDerive_sound_int`): For a system S and a Chvátal–Gomory step (multipliers lambda paired with the constraints by List.zipWith, divisor g): every strict premise a . x < b is first tightened to a . x <= b - 1; if lambda >= 0, g > 0, and g divides every dense coefficient of Sum lambda_k a_k, then every integer solution of S satisfies the cut (Sum lambda_k a_k / g) . x <= floor((Sum lambda_k b'_k) / g), where b'_k = b_k for <= and b_k - 1 for <. The checked step cgDerive returns this cut exactly when the three conditions hold, so every cut it returns is satisfied by every integer solution (cgDerive_sound_int).
- **R5c** (theorem; `checkCutCert_sound_int`): If the cut-plus-Farkas checker accepts (every Chvátal–Gomory step is valid when applied in order to the original system extended by earlier cuts, each step tightening strict premises to <= b - 1 before combining, and checkFarkas, which does not tighten, accepts the final multipliers for the extended system), then S has no integer solution x : Nat -> Int.
- **R6a** (theorem; `bv_ule_ult_iff_int_of_inUnsignedRange`): For affine expressions e1, e2 with Int coefficients over w-bit variables x, if the integer values of e1 and e2 at the unsigned reading (x i).toNat both lie in [0, 2^w), then e1 <=u e2 (resp. <u) over BitVec w with wrapping evaluation holds iff e1 <= e2 (resp. <) holds over Int.
- **R6b** (theorem; `bv_sle_slt_iff_int_of_inSignedRange`): For affine expressions e1, e2 over w-bit variables x, if the integer values of e1 and e2 at the signed reading (x i).toInt both lie in the w-bit two's-complement range (-2^w <= 2z < 2^w), then e1 <=s e2 (resp. <s) over BitVec w with wrapping evaluation holds iff e1 <= e2 (resp. <) over Int.
- **R6c** (theorem; `bv_ule_ult_iff_int_of_noWrapU`, `bv_sle_slt_iff_int_of_noWrapS`): If every intermediate value of the left-to-right evaluation of e1 and of e2 (each coefficient literal, each product c_i * x_i, each partial sum, the constant, and the final value) lies in [0, 2^w) at the unsigned reading, then e1 <=u e2 (resp. <u) over BitVec w holds iff e1 <= e2 (resp. <) over Int; likewise for the signed reading, the two's-complement range, and <=s / <s. These are corollaries of R6a/R6b; the no-wrap hypotheses are stronger than needed (R6i).
- **R6e** (theorem; `checkFarkas_refutes_bvU_posSupport_of_lhs_lt_of_rhs_nonneg`): Let A be a list of bit-vector atoms e1 <= e2 or e1 < e2 between affine expressions, translated to integer constraints in normal form (e1 - e2 <= 0, resp. < 0). If checkFarkas accepts cert for the translations, then at every w-bit point x at which every atom with a positive multiplier has left-hand integer value (unsigned reading) < 2^w and right-hand integer value >= 0, those positively weighted atoms do not all hold in the unsigned bit-vector reading (so neither does A). The two-sided corollary checkFarkas_refutes_bvU_of_inUnsignedRange assumes [0, 2^w) on both sides of every atom.
- **R6f** (theorem; `checkFarkas_refutes_bvS_posSupport_of_lhs_lt_of_rhs_ge`): As R6e for the signed reading: if checkFarkas accepts cert for the integer translations of A, then at every w-bit point x at which every positively weighted atom has 2 * lhs < 2^w and -2^w <= 2 * rhs (integer values at the signed reading), those atoms do not all hold in the signed bit-vector reading. The two-sided corollary checkFarkas_refutes_bvS_of_inSignedRange assumes the signed range on both sides of every atom.
- **R6g** (counterexample; `ce_bv_reading_mismatch`): At w = 8 and x0 = 255#8: under the signed reading both sides of x0 <= 0 are in signed range and -1 <= 0 holds, but the unsigned comparison 255 <=u 0 fails; conversely, under the unsigned reading both sides are in unsigned range and 255 <= 0 fails, but the signed comparison -1 <=s 0 holds. The integer reading must match the comparison's signedness.
- **R6h** (counterexample; `ce_bv_rearrangement_unsound`): Moving terms across a bit-vector comparison is unsound even when the original sides are in range: at w = 8 and (x0, x1) = (0, 1), x0 <=u x1 holds but x0 - x1 <=u 0 fails (x0 - x1 wraps to 255), although the integer -1 <= 0 holds; at (x0, x1) = (-100, 100) in the signed reading, x0 <=s x1 holds but x0 - x1 <=s 0 fails (x0 - x1 = -200 wraps to 56).
- **R6i** (counterexample; `ce_noWrap_not_needed_for_wrapping_eval`): Intermediate no-wrap is not necessary for wrapping evaluation: for e = x0 + x0 - x0 (written x0 + x0 + (-1) * x0) at w = 8, in the signed reading at x0 = 100 the left-to-right partial sum 200 leaves the signed range while every other intermediate value (literals, products, other partial sums, constant, final value 100) is in range, so NoWrapS fails, yet the wrapping value of e equals its integer value 100; in the unsigned reading at x0 = 200 the partial sum 400 (and the literal -1 and the product -200) leave the unsigned range, so NoWrapU fails, yet the wrapping value equals the integer value 200. Hence comparisons of e with any in-range right-hand side transfer (R6a/R6b).

## Applicability

### Model fidelity

This is a **toy model**. Every definition is a small Lean function written for this package; none is extracted from, or proved equivalent to, a production checker, solver, proof format, or compiler.

What the definitions are meant to capture:

- `checkFarkas` is the arithmetic core of checking an infeasibility certificate for linear arithmetic: a non-negative integer combination of the input constraints whose left-hand side cancels and whose right-hand side is contradictory, with the combination strict when a positively weighted premise is strict. Checks of this kind appear in proof checkers for SMT proofs (the Alethe rule `la_generic`, checked for example by Carcara), in tactics that obtain a certificate from an untrusted oracle and then check it (Mathlib `linarith`; Rocq's `lia` through ZMicromega), and in verified simplex developments (Isabelle AFP). Linear forms are sparse association lists that may repeat an index, as arises when scaled premises are concatenated without normalization; multipliers are paired with constraints by position (`List.zipWith`).
- `checkFarkasTightened`, `cgCut`, `cgDerive` and `checkCutCert` capture integer reasoning steps: tightening a strict integer constraint `a · x < b` to `a · x ≤ b - 1`, and Chvátal–Gomory cuts (divide a non-negative combination by a positive integer and round the right-hand side down), as in GCD tightening inside Lean's `omega` and the `CutProof` certificates of Rocq ZMicromega.
- `AffExpr.evalBv`, `uval`/`sval`, `InUnsignedRange`/`InSignedRange`, `NoWrapU`/`NoWrapS` and `BvAtom` capture the step in which a verifier or an SMT solver decides comparisons between affine expressions over `w`-bit machine integers (`BitVec w`, wrapping `+` and `*`, unsigned or two's-complement reading) by reasoning over unbounded integers, and the range facts that step needs.

Known gaps between the model and real systems:

- Only `≤` and `<` constraints. Equalities must be written as two inequalities; disequalities (which need case splits) are not modeled.
- Coefficients and right-hand sides are integers. Rational inputs must first be scaled by a positive integer; that step is not modeled.
- Rational points appear only as scaled pairs `(d, p)` with `d > 0`; no rational number type is used (see the modeling bridge below).
- Certificates are positional lists of integers. Parsing a proof format, normal forms of linear expressions beyond the dense zero test, and the size of certificates are not modeled.
- The completeness theorem (R4a) is existential: no verified certificate-producing procedure and no complexity bound are given.
- The bit-vector part covers one fixed width `w`, wrapping `+` and `*` with integer literals, and the comparisons `ule`/`ult`/`sle`/`slt`. Division, remainder, shifts, zero- or sign-extension, truncation, checked or trapping arithmetic, and poison-producing flags (LLVM `nuw`/`nsw`) are out of scope.

### Rational reading of the scaled statements

Basis: derived (modeling bridge). A finite system `S` mentions finitely many variables, so the restriction of any rational point to those variables can be written `p / d` with a common denominator `d > 0`, and variables that `S` does not mention do not affect satisfaction. Hence, for finite `S`, "no scaled point `(d, p)` with `d > 0` satisfies `S`" is equivalent to "`S` has no rational solution". This is argued in prose (module documentation of `ToyFarkas.Constraint`), not proved in Lean. It relies on finiteness: for an arbitrary point `q : Nat → ℚ` such as `q i = 1 / (i + 1)` no common denominator exists. Every Lean theorem about rational points takes `0 < d` as an explicit hypothesis, because `SatScaled S 0 p` is degenerate (`ex_satScaled_denominator_zero_degenerate`).

### Reading the results as statements about real checkers and machine integers

Basis: derived (modeling bridge). A real checker whose arithmetic core implements the conditions of `checkFarkas` (non-negative multipliers, a dense zero test of the combined left-hand side, strictness taken only from positively weighted premises, and a contradictory right-hand side) inherits the soundness argument of R1a for that core, provided its parsing, normalization and arithmetic are faithful; R3a, R3b and R3f show in the model which deviations break soundness. Likewise, Lean's `BitVec w` with `BitVec.ofInt`, `+`, `*`, `toNat` and `toInt` is the standard model of `w`-bit wrapping arithmetic with unsigned and two's-complement readings, so R6a–R6i describe machine-integer comparisons under wrapping semantics. Nothing in this package inspects or verifies the code of a real checker, solver, or compiler.

### How the subjects relate

The Lean 4 toolchain `v4.34.1` (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`) checks every proof, and its core library supplies `BitVec` and the lemmas used by the bit-vector results. The papers listed as subjects (Farkas 1902; Motzkin 1936; Gomory 1958; Chvátal 1973) are the sources of the classical results restated here in this package's own vocabulary; their own statements are not formalized.

### Relation to the machine-integer package of this corpus

The corpus package `machine-integer-arithmetic-refinement-and-overflow-obligations` develops wrapping, checked and overflow-checked evaluation of general ring expressions over Lean's `BitVec n` (for example, that the unsigned value of wrapping evaluation is the integer value reduced modulo `2^n`, and that checked evaluation succeeds exactly when every subexpression is in range). The bit-vector results here (R6a–R6i) are narrower and aimed at certificate checking: affine expressions, `≤`/`<` comparisons, and the range facts that let an integer Farkas certificate refute a system of bit-vector comparisons. The two packages share no Lean code: this package defines its own `AffExpr`, `AffExpr.evalBv`, `uval`, `sval`, `InUnsignedRange`, `InSignedRange`, `NoWrapU` and `NoWrapS`. The relationship is stated in prose only; no theorem of this package depends on, or is proved equivalent to, a theorem of that package.

### Toolchain

Lean `leanprover/lean4:v4.34.1`, core library only: no Mathlib, no other dependency, no `[[require]]` in `lean/lakefile.toml`. Concrete facts are proved by `decide` (kernel evaluation); `native_decide` is not used.

## Findings

### Conventions

- *Depth* describes the mathematical content of a card's statement from the package definitions, not the length of its Lean proof; a card restating a corollary of another card has the depth of that card.
- A card may list several Lean theorems: the first is the primary statement and the rest are corollaries or related forms covered by the same hypothesis ledger.
- Every theorem is labeled `Basis: execution (Lean kernel check)`. Any claim connecting a Lean statement to rational numbers or to real systems is a separate `Basis: derived (modeling bridge)` line with its reasoning.
- Counterexamples are in canonical form: all other hypotheses hold and the conclusion fails.
- Each card's non-claims are listed under Boundaries; each card's statement and definition-closure hashes are listed under Evidence.
- Lean statements are printed by Lean's `#check` (namespace `Toy.Farkas` opened). Definitions they use are quoted in full under Core definitions. Where the default `#check` output would not elaborate back to the theorem's statement, it is printed with `set_option pp.numericTypes true` (every numeral shows its type; used where a numeral's type is not fixed by its context, e.g. `(0 : Int) < (1 : Int)`, which the default output prints as `0 < 1` and which would then elaborate over `Nat`) or with `set_option pp.structureInstanceTypes true` (every structure instance shows its type, as in `{ terms := …, const := 0 : AffExpr }`).

### Core definitions

Definitions are shown as in the source (doc comments omitted). Each definition has proved positive and negative examples; they are listed by exact Lean name after each group of definitions, and their statements (the concrete inputs and outcomes they check) are quoted under "Statements of the definition examples" after the result cards.

#### Sparse linear forms (`ToyFarkas/Sparse.lean`)

```lean
abbrev SparseVec := List (Nat × Int)

def SparseVec.coeff (v : SparseVec) (i : Nat) : Int :=
  (v.map (fun p => if p.1 = i then p.2 else 0)).sum

def SparseVec.eval (v : SparseVec) (x : Nat → Int) : Int :=
  (v.map (fun p => p.2 * x p.1)).sum

def SparseVec.smul (l : Int) (v : SparseVec) : SparseVec :=
  v.map (fun p => (p.1, l * p.2))

def SparseVec.isZero (v : SparseVec) : Bool :=
  v.all (fun p => v.coeff p.1 == 0)

def SparseVec.bound (v : SparseVec) : Nat := v.foldr (fun p m => max (p.1 + 1) m) 0

def denseDotOn (ks : List Nat) (a x : Nat → Int) : Int :=
  (ks.map (fun i => a i * x i)).sum

def denseDot (n : Nat) (a x : Nat → Int) : Int :=
  denseDotOn (List.range n) a x
```

*Meant to capture.* A sparse integer linear form as an untrusted solver or a checker would hold it: an association list that may repeat indices (as arises when scaled premises are concatenated). `coeff` is the dense semantics (duplicates add; absent indices are `0`); `eval` is evaluation at an integer point; `isZero` is the decidable dense zero test; `bound` is one past the largest index; `denseDotOn`/`denseDot` are dense dot products over an index list / range.

*Examples (proved).* `ex_coeff_duplicates_add`, `ex_coeff_not_first_match`; `ex_eval_pos`, `ex_eval_neg`; `ex_smul_pos`, `ex_smul_neg`; `ex_isZero_pos` (cancelling duplicates, non-empty list), `ex_isZero_neg`; `ex_bound_pos`, `ex_bound_neg`; `ex_denseDotOn_pos`, `ex_denseDotOn_neg`; `ex_denseDot_pos`, `ex_denseDot_neg`.

#### Constraints and their integer / scaled-rational semantics (`ToyFarkas/Constraint.lean`)

```lean
inductive Rel where
  | le
  | lt
  deriving DecidableEq, Repr

def Rel.Sat : Rel → Int → Int → Prop
  | .le, a, b => a ≤ b
  | .lt, a, b => a < b

structure Constraint where
  lhs : SparseVec
  rel : Rel
  rhs : Int
  deriving DecidableEq, Repr

def Constraint.isStrict (c : Constraint) : Bool :=
  match c.rel with
  | .le => false
  | .lt => true

def Constraint.HoldsInt (c : Constraint) (x : Nat → Int) : Prop :=
  c.rel.Sat (SparseVec.eval c.lhs x) c.rhs

def Constraint.HoldsScaled (c : Constraint) (d : Int) (p : Nat → Int) : Prop :=
  c.rel.Sat (SparseVec.eval c.lhs p) (c.rhs * d)

def SatInt (S : List Constraint) (x : Nat → Int) : Prop :=
  ∀ c ∈ S, c.HoldsInt x

def SatScaled (S : List Constraint) (d : Int) (p : Nat → Int) : Prop :=
  ∀ c ∈ S, c.HoldsScaled d p

def pt1 (v : Int) : Nat → Int := fun i => if i = 0 then v else 0

def pt2 (a b : Int) : Nat → Int := fun i => if i = 0 then a else if i = 1 then b else 0
```

*Meant to capture.* A finite conjunction of linear constraints `a · x ≤ b` / `a · x < b` with integer data. `HoldsInt` is satisfaction at an integer point. `HoldsScaled c d p` is `lhs · p ⋈ rhs * d`; for `d > 0` it is satisfaction at the rational point `p / d`, and every theorem about such points takes `0 < d` as an explicit hypothesis. **Modeling bridge (prose, not a Lean theorem):** a finite system mentions finitely many variables, so the restriction of any rational point to them has a positive common denominator; for an arbitrary point `q : Nat → ℚ` (e.g. `q i = 1/(i+1)`) no common denominator exists, so the bridge relies on finiteness of `S`. `satInt_iff_satScaled_one` (proved) identifies integer satisfaction with `d = 1`. `pt1 v` / `pt2 a b` are the points `x₀ = v` / `(x₀, x₁) = (a, b)` with all other variables `0`.

*Examples (proved).* `ex_holdsInt_pos`, `ex_holdsInt_neg`, `ex_holdsInt_strict_neg`; `ex_holdsScaled_pos` (`x₀ = 1/2`), `ex_holdsScaled_neg`; `ex_satScaled_pos`, `ex_satScaled_neg` (`x₀ = 3/2` violates `x₀ = 1/2`); `ex_satInt_pos`, `ex_satInt_neg` (no small integer solution of `{2x₀ ≤ 1, -2x₀ ≤ -1}`); `ex_satScaled_denominator_zero_degenerate` (`d = 0` is not a rational semantics: `{0 ≤ -1}` holds at `d = 0`); `ex_isStrict_pos`, `ex_isStrict_neg`.

#### The Farkas checker and the positive support (`ToyFarkas/Checker.lean`)

```lean
def multipliersNonneg (cert : List Int) : Bool :=
  cert.all (fun l => decide (0 ≤ l))

def combineLhs (S : List Constraint) (cert : List Int) : SparseVec :=
  (List.zipWith (fun l c => SparseVec.smul l c.lhs) cert S).flatten

def combineRhs (S : List Constraint) (cert : List Int) : Int :=
  (List.zipWith (fun l c => l * c.rhs) cert S).sum

def combineStrict (S : List Constraint) (cert : List Int) : Bool :=
  (List.zipWith (fun l c => decide (0 < l) && c.isStrict) cert S).any id

def lhsVanishes (S : List Constraint) (cert : List Int) : Bool :=
  (combineLhs S cert).isZero

def rhsContradicts (S : List Constraint) (cert : List Int) : Bool :=
  if combineStrict S cert then decide (combineRhs S cert ≤ 0) else decide (combineRhs S cert < 0)

def checkFarkas (S : List Constraint) (cert : List Int) : Bool :=
  multipliersNonneg cert && lhsVanishes S cert && rhsContradicts S cert

def posSupport {α : Type} (cert : List Int) (S : List α) : List α :=
  ((cert.zip S).filter (fun q => decide (0 < q.1))).map Prod.snd

def sysLeGe : List Constraint := [⟨[(0, 1)], .le, 1⟩, ⟨[(0, -1)], .le, -2⟩]

def sysEq : List Constraint := [⟨[(0, 1)], .le, 1⟩, ⟨[(0, -1)], .le, -1⟩]

def sysStrict : List Constraint := [⟨[(0, 1)], .lt, 1⟩, ⟨[(0, -1)], .le, -1⟩]
```

*Meant to capture.* A Farkas / Motzkin certificate checker: multiplier `k` is paired with constraint `k` (`List.zipWith`: a short certificate gives the remaining constraints multiplier `0`; surplus multipliers are ignored by the combination but still checked for sign); the combined left-hand side must be the zero form; the derived variable-free conclusion `0 ≤ R` (or `0 < R` if some positively weighted premise is strict) must be false, i.e. `R < 0` (or `R ≤ 0`). `posSupport cert S` is the sublist of premises with a positive multiplier (same pairing).

*Examples (proved).* `ex_multipliersNonneg_pos`, `ex_multipliersNonneg_neg`, `ex_combineLhs_pos`, `ex_combineLhs_neg` (the combination is not normalized), `ex_combineRhs_pos`, `ex_combineRhs_neg`, `ex_combineStrict_pos`, `ex_combineStrict_neg` (a zero-weighted strict premise does not count), `ex_lhsVanishes_pos`, `ex_lhsVanishes_neg`, `ex_rhsContradicts_pos`, `ex_rhsContradicts_neg` (`0 ≤ 0` is not contradictory), `ex_checkFarkas_pos`, `ex_checkFarkas_strict_pos`, `ex_checkFarkas_neg` (all 25 small certificates rejected for the satisfiable `sysEq`), `ex_checkFarkas_short_certificate`, `ex_checkFarkas_surplus_multipliers`; `nv_checkFarkas_sound_posSupport` (a zero-weighted premise is not in the support).

#### Buggy variants and integer tightening (`ToyFarkas/Counterexamples.lean`)

```lean
def sysTwoUpper : List Constraint := [⟨[(0, 1)], .le, 1⟩, ⟨[(0, 1)], .le, 2⟩]

def rhsContradictsIgnoringStrictness (S : List Constraint) (cert : List Int) : Bool :=
  decide (combineRhs S cert ≤ 0)

def combineStrictAnyPremise (S : List Constraint) (_cert : List Int) : Bool :=
  S.any Constraint.isStrict

def rhsContradictsAnyPremise (S : List Constraint) (cert : List Int) : Bool :=
  if combineStrictAnyPremise S cert then decide (combineRhs S cert ≤ 0)
  else decide (combineRhs S cert < 0)

def sysEqPlusStrict : List Constraint :=
  [⟨[(0, 1)], .le, 1⟩, ⟨[(0, -1)], .le, -1⟩, ⟨[(1, 1)], .lt, 5⟩]

def Constraint.tighten (c : Constraint) : Constraint :=
  match c.rel with
  | .le => c
  | .lt => ⟨c.lhs, .le, c.rhs - 1⟩

def checkFarkasTightened (S : List Constraint) (cert : List Int) : Bool :=
  checkFarkas (S.map Constraint.tighten) cert

def sysOpenUnit : List Constraint := [⟨[(0, 1)], .lt, 1⟩, ⟨[(0, -1)], .lt, 0⟩]

def isZeroIndexBlind (v : SparseVec) : Bool := (v.map Prod.snd).sum == 0

def coeffFirstMatch (v : SparseVec) (i : Nat) : Int :=
  match v.find? (fun p => p.1 == i) with
  | some p => p.2
  | none => 0

def isZeroFirstMatch (v : SparseVec) : Bool := v.all (fun p => coeffFirstMatch v p.1 == 0)
```

*Meant to capture.* Plausible implementation mistakes (strictness ignored; strictness read from any premise; index-blind or first-match zero tests) and the integer-only strengthening of strict constraints (`tighten`, sound over `Int` only).

*Examples (proved).* `ex_rhsContradictsIgnoringStrictness_pos`, `ex_rhsContradictsIgnoringStrictness_neg`, `ex_combineStrictAnyPremise_pos`, `ex_combineStrictAnyPremise_neg`, `ex_rhsContradictsAnyPremise_pos`, `ex_rhsContradictsAnyPremise_neg`, `ex_tighten_pos`, `ex_tighten_neg`, `ex_isZeroIndexBlind_pos`, `ex_isZeroIndexBlind_neg`, `ex_coeffFirstMatch_pos`, `ex_coeffFirstMatch_neg`, `ex_isZeroFirstMatch_pos`, `ex_isZeroFirstMatch_neg`.

#### The half-integral system (`ToyFarkas/Completeness.lean`)

```lean
def sysHalf : List Constraint := [⟨[(0, 2)], .le, 1⟩, ⟨[(0, -2)], .le, -1⟩]
```

*Meant to capture.* `{2x₀ ≤ 1, -2x₀ ≤ -1}`, i.e. `x₀ = 1/2`: rationally feasible, integer infeasible.

*Examples (proved).* `ex_satScaled_pos`, `ex_satInt_neg` (same system, in `Constraint.lean`).

#### Chvátal–Gomory cuts and cut-plus-Farkas certificates (`ToyFarkas/Cuts.lean`)

```lean
structure CGStep where
  mult : List Int
  div : Int
  deriving DecidableEq, Repr

def cgLhs (S : List Constraint) (k : CGStep) : SparseVec := combineLhs S k.mult

def cgRhs (S : List Constraint) (k : CGStep) : Int := combineRhs (S.map Constraint.tighten) k.mult

def cgDivisible (S : List Constraint) (k : CGStep) : Bool :=
  (List.range (cgLhs S k).bound).all (fun i => SparseVec.coeff (cgLhs S k) i % k.div == 0)

def cgCut (S : List Constraint) (k : CGStep) : Constraint :=
  ⟨(List.range (cgLhs S k).bound).map (fun i => (i, SparseVec.coeff (cgLhs S k) i / k.div)),
   .le, cgRhs S k / k.div⟩

def cgValid (S : List Constraint) (k : CGStep) : Bool :=
  multipliersNonneg k.mult && decide (0 < k.div) && cgDivisible S k

def cgDerive (S : List Constraint) (k : CGStep) : Option Constraint :=
  if cgValid S k then some (cgCut S k) else none

def applyCuts : List Constraint → List CGStep → Option (List Constraint)
  | S, [] => some S
  | S, k :: ks =>
    match cgDerive S k with
    | some c => applyCuts (S ++ [c]) ks
    | none => none

structure CutCert where
  cuts : List CGStep
  farkas : List Int
  deriving DecidableEq, Repr

def checkCutCert (S : List Constraint) (cc : CutCert) : Bool :=
  match applyCuts S cc.cuts with
  | some S' => checkFarkas S' cc.farkas
  | none => false

def sysTwoXLeThree : List Constraint := [⟨[(0, 2)], .le, 3⟩]

def halfCutCert : CutCert := ⟨[⟨[1, 0], 2⟩, ⟨[0, 1], 2⟩], [0, 0, 1, 1]⟩
```

*Meant to capture.* A Chvátal–Gomory step with rational multipliers `λ / g` written as integer multipliers (paired with the constraints by `List.zipWith`) and a common divisor `g`: strict premises are first read as `≤ b - 1` (integers); the combined left-hand side must have every dense coefficient divisible by `g`; the cut divides it by `g` and rounds the right-hand side down (Lean's `Int` `/` is floor division for positive divisors, cf. `ex_cgCut_floor_negative`). The cut's left-hand side is written densely over `0 … bound-1` (a reference definition, not an efficient one). A cut-plus-Farkas certificate applies steps in order, each seeing the original system plus earlier cuts, and then runs `checkFarkas` (which does not tighten).

*Examples (proved).* `ex_cgLhs_pos`, `ex_cgLhs_neg`, `ex_cgCut_pos`, `ex_cgCut_neg`, `ex_cgCut_floor_negative`, `ex_cgRhs_strict_pos`, `ex_cgRhs_neg`, `ex_cgDivisible_pos`, `ex_cgDivisible_neg`, `ex_cgDivisible_duplicates_pos`, `ex_cgValid_pos`, `ex_cgValid_neg`, `ex_cgDerive_pos`, `ex_cgDerive_neg`, `ex_applyCuts_pos`, `ex_applyCuts_neg`, `ex_checkCutCert_pos`, `ex_checkCutCert_neg`, `ex_checkCutCert_no_cuts_no_tightening`.

#### Bit-vector evaluation, readings, ranges, intermediate values (`ToyFarkas/BitVecTransfer.lean`)

```lean
structure AffExpr where
  terms : SparseVec
  const : Int
  deriving DecidableEq, Repr

def AffExpr.evalInt (e : AffExpr) (ρ : Nat → Int) : Int :=
  SparseVec.eval e.terms ρ + e.const

def SparseVec.evalBv (w : Nat) (v : SparseVec) (x : Nat → BitVec w) : BitVec w :=
  v.foldl (fun s p => s + BitVec.ofInt w p.2 * x p.1) 0#w

def AffExpr.evalBv (w : Nat) (e : AffExpr) (x : Nat → BitVec w) : BitVec w :=
  SparseVec.evalBv w e.terms x + BitVec.ofInt w e.const

def uval {w : Nat} (x : Nat → BitVec w) : Nat → Int := fun i => ((x i).toNat : Int)

def sval {w : Nat} (x : Nat → BitVec w) : Nat → Int := fun i => (x i).toInt

def InUnsignedRange (w : Nat) (z : Int) : Prop := 0 ≤ z ∧ z < (2 : Int) ^ w

def InSignedRange (w : Nat) (z : Int) : Prop := -((2 : Int) ^ w) ≤ 2 * z ∧ 2 * z < (2 : Int) ^ w

def SparseVec.intermediatesFrom (v : SparseVec) (ρ : Nat → Int) (acc : Int) : List Int :=
  match v with
  | [] => []
  | p :: v => p.2 :: (p.2 * ρ p.1) :: (acc + p.2 * ρ p.1) ::
      SparseVec.intermediatesFrom v ρ (acc + p.2 * ρ p.1)

def SparseVec.intermediates (v : SparseVec) (ρ : Nat → Int) : List Int :=
  SparseVec.intermediatesFrom v ρ 0

def AffExpr.intermediates (e : AffExpr) (ρ : Nat → Int) : List Int :=
  SparseVec.intermediates e.terms ρ ++ [e.const, e.evalInt ρ]

def NoWrapU (w : Nat) (e : AffExpr) (ρ : Nat → Int) : Prop :=
  ∀ z ∈ e.intermediates ρ, InUnsignedRange w z

def NoWrapS (w : Nat) (e : AffExpr) (ρ : Nat → Int) : Prop :=
  ∀ z ∈ e.intermediates ρ, InSignedRange w z

def bvPt2 {w : Nat} (a b : BitVec w) : Nat → BitVec w :=
  fun i => if i = 0 then a else if i = 1 then b else 0#w

def eDouble : AffExpr := ⟨[(0, 1), (0, 1)], 0⟩

def eConst (k : Int) : AffExpr := ⟨[], k⟩

def eX0 : AffExpr := ⟨[(0, 1)], 0⟩

def eX1 : AffExpr := ⟨[(1, 1)], 0⟩
```

*Meant to capture.* Affine expressions over `w`-bit machine integers with wrapping `+`, `*` and literals embedded by `BitVec.ofInt`; terms are summed left to right and the constant is added last. Their integer value under the unsigned (`toNat`) or signed (`toInt`) reading; the exact representable intervals (`InSignedRange` is written with `2z` so that at `w = 0` only `0` is representable). "Interval transfer" in this package means transfer under these representable intervals `[0, 2^w)` and `[-2^(w-1), 2^(w-1))`; no abstract interval domain is defined. `intermediates` lists, in evaluation order, each coefficient literal, each product, each left-to-right partial sum, the constant, and the final value; `NoWrapU`/`NoWrapS` require all of them in range. Known divergences from machine-level no-wrap conditions: there is no subtraction node (`x₀ - x₁` is `x₀ + (-1)·x₁`, so a negative coefficient fails `NoWrapU`; `ex_noWrapU_rejects_machine_subtraction`), and the intermediates are those of this particular evaluation order.

*Examples (proved).* `ex_evalInt_pos`, `ex_evalInt_neg`, `ex_evalBv_pos`, `ex_evalBv_neg` (wrapping `200 + 200 = 144`), `ex_sparse_evalBv_pos`, `ex_sparse_evalBv_neg`, `ex_uval_pos`, `ex_uval_neg`, `ex_sval_pos`, `ex_sval_neg`, `ex_inUnsignedRange_pos`, `ex_inUnsignedRange_neg`, `ex_inSignedRange_pos`, `ex_inSignedRange_neg`, `ex_inSignedRange_zero_width`, `ex_intermediates_pos`, `ex_intermediates_neg`, `ex_noWrapU_pos`, `ex_noWrapU_neg`, `ex_noWrapS_pos`, `ex_noWrapS_neg`, `ex_noWrap_checks_coefficient_literals`, `ex_noWrapU_rejects_machine_subtraction`.

#### Bit-vector atoms and concrete systems (`ToyFarkas/BitVecSystems.lean`)

```lean
structure BvAtom where
  lhs : AffExpr
  rel : Rel
  rhs : AffExpr
  deriving DecidableEq, Repr

def BvAtom.HoldsU (w : Nat) (a : BvAtom) (x : Nat → BitVec w) : Prop :=
  match a.rel with
  | .le => (a.lhs.evalBv w x).ule (a.rhs.evalBv w x) = true
  | .lt => (a.lhs.evalBv w x).ult (a.rhs.evalBv w x) = true

def BvAtom.HoldsS (w : Nat) (a : BvAtom) (x : Nat → BitVec w) : Prop :=
  match a.rel with
  | .le => (a.lhs.evalBv w x).sle (a.rhs.evalBv w x) = true
  | .lt => (a.lhs.evalBv w x).slt (a.rhs.evalBv w x) = true

def BvAtom.toConstraint (a : BvAtom) : Constraint :=
  ⟨a.lhs.terms ++ SparseVec.smul (-1) a.rhs.terms, a.rel, a.rhs.const - a.lhs.const⟩

def atomEx : BvAtom := ⟨⟨[(0, 1)], 1⟩, .le, ⟨[(1, 1)], 0⟩⟩

def atomsLtLe : List BvAtom := [⟨⟨[(0, 1)], 0⟩, .lt, ⟨[(1, 1)], 0⟩⟩, ⟨⟨[(1, 1)], 0⟩, .le, ⟨[(0, 1)], 0⟩⟩]

def atomsLhsUnderflowU : List BvAtom :=
  [⟨⟨[(0, 1)], -1⟩, .le, ⟨[], 0⟩⟩, ⟨⟨[], 2⟩, .le, ⟨[(0, 1)], 0⟩⟩]

def atomsZeroWeight : List BvAtom :=
  atomsLtLe ++ [⟨⟨[(0, 3)], 0⟩, .le, ⟨[(1, 1)], -10⟩⟩]

def eAddAddSub : AffExpr := ⟨[(0, 1), (0, 1), (0, -1)], 0⟩

def atomsLhsWrapU : List BvAtom :=
  [⟨⟨[(0, 3)], 0⟩, .le, ⟨[], 100⟩⟩, ⟨⟨[], 200⟩, .le, ⟨[(0, 1)], 0⟩⟩]

def atomsRhsWrapU : List BvAtom :=
  [⟨⟨[], 200⟩, .le, ⟨[(0, 1)], -1⟩⟩, ⟨⟨[(0, 1)], 0⟩, .le, ⟨[], 0⟩⟩]

def atomsLhsWrapS : List BvAtom :=
  [⟨⟨[(0, 3)], 0⟩, .le, ⟨[], 100⟩⟩, ⟨⟨[], 90⟩, .le, ⟨[(0, 1)], 0⟩⟩]

def atomsRhsWrapS : List BvAtom :=
  [⟨⟨[], 100⟩, .le, ⟨[(0, 1)], -200⟩⟩, ⟨⟨[(0, 1)], 0⟩, .le, ⟨[], 50⟩⟩]

def atomsLe : List BvAtom := [⟨⟨[(0, 1)], 0⟩, .le, ⟨[(1, 1)], 0⟩⟩]

def atomsLtZero : List BvAtom := [⟨⟨[(0, 1)], 0⟩, .lt, ⟨[], 0⟩⟩]

def atomsHalfU : List BvAtom := [⟨⟨[(0, 2)], 0⟩, .le, ⟨[], 1⟩⟩, ⟨⟨[], 1⟩, .le, ⟨[(0, 2)], 0⟩⟩]
```

*Meant to capture.* Comparison atoms `e₁ ⋈ e₂` between affine expressions, read unsigned (`ule`/`ult`) or signed (`sle`/`slt`), and their integer translation into `Constraint` normal form (moving terms across is valid over `Int` only). The translation adds no variable domain bounds.

*Examples (proved).* `ex_bvAtom_holdsU_pos`, `ex_bvAtom_holdsU_neg`, `ex_bvAtom_holdsU_wrap`, `ex_bvAtom_holdsS_pos`, `ex_bvAtom_holdsS_neg`, `ex_bvAtom_toConstraint_pos`, `ex_bvAtom_toConstraint_neg`.

*Helper lemmas (proved).* `SparseVec.evalBv_eq_ofInt` / `AffExpr.evalBv_eq_ofInt`: if `BitVec.ofInt w (ρ i) = x i` for all `i`, wrapping evaluation equals `BitVec.ofInt w` of the integer value (because `BitVec.ofInt w` commutes with `+` and `*`). `BvAtom.toConstraint_holdsInt_iff`, `BvAtom.holdsU_iff_holdsInt_of_inUnsignedRange`, `BvAtom.holdsS_iff_holdsInt_of_inSignedRange`, `BvAtom.holdsInt_of_holdsU_of_lhs_lt_of_rhs_nonneg`, `BvAtom.holdsInt_of_holdsS_of_lhs_lt_of_rhs_ge` connect atoms to the Farkas checker. Their statements are listed under "Other kernel-checked theorems mentioned in this report".

### How Farkas completeness (R4a) is proved

`farkas_complete_scaled` is proved in module `ToyFarkas.Motzkin` (`Toy.Farkas.Motzkin.complete`). The auxiliary definitions of that module (namespace `Toy.Farkas.Motzkin`) are used only inside proofs; they occur in no card statement and in no statement or closure hash. Because the proof-internal statements listed under "Other kernel-checked theorems mentioned in this report" use them, they are quoted here as in the source (inside namespace `Toy.Farkas.Motzkin`, so `HC` here is `Motzkin.HC` in those statements; doc comments omitted):

```lean
structure HC where
  a : SparseVec
  s : Bool

def HC.Holds (h : HC) (y : Nat → Int) : Prop :=
  SparseVec.eval h.a y ≤ 0 ∧ (h.s = true → SparseVec.eval h.a y < 0)

def HSat (H : List HC) (y : Nat → Int) : Prop := ∀ h ∈ H, h.Holds y

inductive Deriv (H : List HC) : HC → Prop
  | mem {h : HC} : h ∈ H → Deriv H h
  | add {h g : HC} : Deriv H h → Deriv H g → Deriv H ⟨h.a ++ g.a, h.s || g.s⟩
  | smul {h : HC} {c : Int} : 0 < c → Deriv H h → Deriv H ⟨SparseVec.smul c h.a, h.s⟩

def comb (n : Nat) (p q : HC) : HC :=
  ⟨SparseVec.smul (-SparseVec.coeff q.a n) p.a ++ SparseVec.smul (SparseVec.coeff p.a n) q.a,
    p.s || q.s⟩

def elim (n : Nat) (H : List HC) : List HC :=
  H.filter (fun h => decide (SparseVec.coeff h.a n = 0)) ++
  (H.filter (fun h => decide (0 < SparseVec.coeff h.a n))).flatMap (fun p =>
    (H.filter (fun h => decide (SparseVec.coeff h.a n < 0))).map (fun q => comb n p q))

def rest (n : Nat) (y : Nat → Int) (h : HC) : Int :=
  SparseVec.eval h.a y - SparseVec.coeff h.a n * y n

def lincomb (μ : List Int) (H : List HC) (i : Nat) : Int :=
  (List.zipWith (fun l h => l * SparseVec.coeff h.a i) μ H).sum

def strictPos (μ : List Int) (H : List HC) : Bool :=
  (List.zipWith (fun l h => decide (0 < l) && h.s) μ H).any id

structure IsMult (H : List HC) (g : HC) (μ : List Int) : Prop where
  len : μ.length = H.length
  nonneg : ∀ l ∈ μ, 0 ≤ l
  coeff : ∀ i, SparseVec.coeff g.a i = lincomb μ H i
  strict : g.s = true → strictPos μ H = true

def shift (v : SparseVec) : SparseVec := v.map (fun e => (e.1 + 1, e.2))

def homC (c : Constraint) : HC := ⟨(0, -c.rhs) :: shift c.lhs, c.isStrict⟩

def hden : HC := ⟨[(0, -1)], true⟩

def homSys (S : List Constraint) : List HC := hden :: S.map homC

def homBound (S : List Constraint) : Nat := (S.map (fun c => c.lhs.bound)).sum + 1
```

`HC` is a homogeneous constraint `a · y ≤ 0` (`s = false`) or `a · y < 0` (`s = true`) over integer points `y : Nat → Int`; `HC.Holds` is its satisfaction, and `HSat H y` says that every member of `H` holds at `y`. `Deriv H g` says that `g` is derivable from `H` by members, sums (strict if either summand is strict) and positive integer multiples. `comb n p q` combines `p` (positive coefficient at variable `n`) and `q` (negative coefficient at `n`) so that variable `n` cancels, and `elim n H` is one Fourier–Motzkin step eliminating variable `n`. `rest n y h` is the value of `h.a` at `y` with the contribution of variable `n` removed, so that `h.a.eval y = rest n y h + h.a.coeff n * y n`. `IsMult H g μ` says that the list `μ` of non-negative integers, one per member of `H` (paired by position), produces `g`: every dense coefficient of `g.a` equals `lincomb μ H i = Σₖ μₖ · Hₖ.a.coeff i`, and if `g` is strict then some strict member of `H` has a positive multiplier (`strictPos μ H = true`). `shift` moves every variable index up by one (index `0` is reserved for the denominator); `homC`, `hden` and `homSys` are the homogenization of step 1 below; and `homBound S`, one more than the sum of the `bound`s of the left-hand sides of `S`, bounds the variable indices: by `homSys_support`, no member of `homSys S` has a non-zero coefficient at an index `≥ homBound S`.

The proof has four steps.

1. **Homogenization.** A homogeneous constraint is `a · y ≤ 0` or `a · y < 0` over integer points `y : Nat → Int`. Each constraint `c` becomes `homC c`, namely `-c.rhs · y₀ + Σᵢ cᵢ · y_{i+1} ⋈ 0` with the strictness of `c`, and the strict constraint `hden`, namely `-y₀ < 0`, is added: `homSys S = hden :: S.map homC`. By `homSys_sat`, every integer solution `y` of `homSys S` gives `0 < y 0` and `SatScaled S (y 0) (fun i => y (i + 1))`. So the hypothesis of R4a makes `homSys S` unsatisfiable over integer points.
2. **Fourier–Motzkin elimination with integer pivots.** `elim n H` keeps the constraints whose coefficient at variable `n` is `0`, and adds, for every constraint `p` with coefficient `pₙ > 0` and every `q` with `qₙ < 0`, the combination `(-qₙ) · p + pₙ · q`, which is strict if `p` or `q` is strict and has coefficient `0` at `n`. By `elim_extend`, an integer solution of `elim n H` yields an integer solution of `H`: scale the solution by a positive integer and set coordinate `n` between the tightest upper bound (from the `p`'s) and the tightest lower bound (from the `q`'s), at their midpoint when both kinds exist. The extension step is `extend_of_bounds`: if `y'` satisfies the members of `H` whose coefficient at `n` is `0`, and `M > 0` and `t` satisfy `M * rest n y' h + h.a.coeff n * t ≤ 0` (`< 0` when `h` is strict) for every member `h` with a non-zero coefficient at `n`, then the point `fun i => if i = n then t else M * y' i` satisfies `H`. Scaling by a positive integer preserves homogeneous constraints, so no rational number is needed.
3. **Induction on the number of variables** (`fm_main`). If every constraint of `H` mentions only variables `< n` and `H` has no integer solution, then some strict constraint whose left-hand side is the zero form is derivable from `H` by sums and positive integer multiples (`Deriv`). With no variables left, every left-hand side is the zero form, and unsatisfiability at the point `0` forces a strict member `0 < 0`. The proof of `complete` applies `fm_main` to `H = homSys S` and `n = homBound S`; the support hypothesis is `homSys_support`.
4. **Reading back a certificate** (`isMult_of_deriv`, `complete`). A derivation is a vector of non-negative integer multipliers `(μ_d, μ₀, μ₁, …)` over `homSys S`. The coefficients at the variables `i + 1` give `lhsVanishes S [μ₀, μ₁, …] = true`; the coefficient at `y₀` gives `combineRhs S [μ₀, μ₁, …] = -μ_d`; and strictness gives either `μ_d > 0` (so the right-hand side is `< 0`) or a positively weighted strict premise (so `combineStrict` holds and `≤ 0` suffices). Hence `checkFarkas S [μ₀, μ₁, …] = true`.

Basis: execution (Lean kernel check). The statements of the lemmas named above are listed under "Other kernel-checked theorems mentioned in this report"; they carry no recorded hash because they are proof internals, not card statements.

### Result cards

#### R1a — `checkFarkas_sound_scaled` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Soundness of Farkas certificates is classical (Farkas 1902 for non-strict systems, Motzkin 1936 for mixed strict/non-strict systems) and mechanized (Isabelle AFP; Rocq micromega checker soundness); restated for this checker and representation. The positive-support form is an immediate strengthening recorded because a verifier only needs facts about the premises a certificate uses.
- **Plain claim:** If the Boolean checker checkFarkas accepts a certificate cert for a finite list S of integer linear constraints (each a . x <= b or a . x < b), then no scaled point (d, p) with d > 0 satisfies S (checkFarkas_sound_scaled), and in particular no integer point satisfies S (checkFarkas_sound_int, the case d = 1); more precisely, already the premises that cert weights positively (posSupport cert S) have no such point (the _posSupport forms).
- **Lean statement** (`Toy.Farkas.checkFarkas_sound_scaled`; corollaries and related forms: `checkFarkas_sound_int`, `checkFarkas_sound_scaled_posSupport`, `checkFarkas_sound_int_posSupport`):

```lean
theorem checkFarkas_sound_scaled (S : List Constraint) (cert : List Int) (h : checkFarkas S cert = true) (d : Int)
  (hd : 0 < d) (p : Nat → Int) : ¬SatScaled S d p

theorem checkFarkas_sound_int (S : List Constraint) (cert : List Int) (h : checkFarkas S cert = true)
  (x : Nat → Int) : ¬SatInt S x

theorem checkFarkas_sound_scaled_posSupport (S : List Constraint) (cert : List Int) (h : checkFarkas S cert = true)
  (d : Int) (hd : 0 < d) (p : Nat → Int) : ¬SatScaled (posSupport cert S) d p

theorem checkFarkas_sound_int_posSupport (S : List Constraint) (cert : List Int) (h : checkFarkas S cert = true)
  (x : Nat → Int) : ¬SatInt (posSupport cert S) x
```

- **Key definitions** (quoted in full under Core definitions): `Constraint`, `checkFarkas`, `SatScaled`, `SatInt`, `posSupport`.
- **Hypothesis ledger:**
  - `h : checkFarkas S cert = true` — the certificate is accepted; **tight** (counterexample `ce_checkFarkas_rejected_satisfiable`).
  - `hd : 0 < d (scaled forms only)` — the scaled pair (d, p) denotes the rational point p / d only for a positive denominator; **tight** (counterexample `ce_farkas_denominator_zero`).
- **Non-vacuity witness:** checkFarkas accepts (1, 1) for {x0 <= 1, -x0 <= -2} and for the strictness-dependent {x0 < 1, -x0 <= -1}, and d = 1 > 0; with an extra premise x1 <= -7 weighted 0, the positive support is {x0 <= 1, -x0 <= -2}. Lean: `nv_checkFarkas_sound_scaled`, `nv_checkFarkas_sound`, `nv_checkFarkas_sound_posSupport`.
- **Prior art:**
  - Julius Farkas, 'Theorie der einfachen Ungleichungen', Journal für die reine und angewandte Mathematik 124 (1902), pp. 1-27, DOI 10.1515/crll.1902.124.1 (non-strict linear inequalities).
  - Theodore S. Motzkin, 'Beiträge zur Theorie der linearen Ungleichungen', doctoral dissertation, University of Basel; printed by Azriel, Jerusalem, 1936 (the transposition theorem for systems mixing strict and non-strict inequalities; bibliographic record checked via secondary sources, the German text was not read).
  - Alexander Schrijver, Theory of Linear and Integer Programming, John Wiley & Sons, 1986 (paperback reprint 1998, ISBN 978-0-471-98232-6; chapter list checked on the publisher's page): Chapter 7 'Fundamental concepts and results on polyhedra, linear inequalities, and linear programming' (Farkas' lemma and its variants), Chapter 12 'Primal-dual, elimination, and relaxation methods' (includes elimination), Chapter 23 'Cutting planes'. Specific theorem numbers were not checked against the book.
  - Ralph Bottesch, Max W. Haslbeck, René Thiemann, 'Farkas' Lemma and Motzkin's Transposition Theorem', Archive of Formal Proofs, January 17, 2019, https://isa-afp.org/entries/Farkas.html (Isabelle/HOL, via a verified simplex algorithm: a set of linear constraints is unsatisfiable iff some linear combination of them evaluates to a trivially unsatisfiable inequality; covers mixed strict/non-strict systems).
  - Ralph Bottesch, Alban Reynaud, René Thiemann, 'Linear Inequalities', Archive of Formal Proofs, June 21, 2019, https://isa-afp.org/entries/Linear_Inequalities.html (Isabelle/HOL: fundamental theorem of linear inequalities, Farkas' lemma, Carathéodory's theorem, Farkas-Minkowsky-Weyl theorem, decomposition theorem of polyhedra, Meyer's integer-hull result).
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Analysis/Convex/Cone/Dual.lean: Farkas' lemma in geometric form for proper cones in locally convex real topological vector spaces (ProperCone.hyperplane_separation, ProperCone.hyperplane_separation_point); real-valued, not a certificate checker.
  - Xavier Allamigeon, Ricardo D. Katz, 'A Formalization of Convex Polyhedra Based on the Simplex Method', Journal of Automated Reasoning 63 (2019), pp. 323-345, DOI 10.1007/s10817-018-9477-1 (Coq formalization of convex polyhedra via the simplex method; metadata checked via Crossref, full text not read).
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Frontend.lean module docstring: an untrusted oracle (simplex by default, Fourier–Motzkin optional) searches for natural-number coefficients k_i with sum k_i t_i = 0 and k_i > 0 for at least one strict hypothesis; the certificate is checked by building a proof term (not by reflection); over Int, linarith 'will fail to prove False on some unsatisfiable problems'.
  - Haniel Barbosa, Mathias Fleury, Pascal Fontaine, Hans-Jörg Schurr, 'The Alethe Proof Format: An Evolving Specification and Reference', online specification https://verit.gitlabpages.uliege.be/alethe/specification.pdf (typeset March 31, 2026; accessed 2026-11-20), rule la_generic: one rational coefficient per literal, inequalities multiplied by the coefficient's absolute value; step 4 strengthens each individual (negated, normalized) input literal when all its variables are integer-sorted (a strict bound > d becomes >= d + 1, a non-integer bound is rounded), before the multiplication; the specification remarks that after strengthening the conjunction is unsatisfiable 'even if integer variables are assumed to be real variables'; the sum must be a trivial contradiction. The specification has no Chvátal–Gomory cutting-plane rule.
  - Bruno Andreotti, Hanna Lachnitt, Haniel Barbosa, 'Carcara: An Efficient Proof Checker and Elaborator for SMT Proofs in the Alethe Format', TACAS 2023, LNCS 13993, Springer, 2023, pp. 367-386, DOI 10.1007/978-3-031-30823-9_19 (an independent checker for Alethe proofs; metadata checked via Crossref, full text not read).
  - Rocq Stdlib, rocq-prover/stdlib commit f50ccefc570f6b815874df96bb3b872611cfaf0e, theories/micromega/ZMicromega.v: certificate type ZArithProof with constructors DoneProof, RatProof, CutProof, SplitProof, deprecated_EnumProof, ExProof; genCuttingPlane divides a constraint by the gcd of its coefficients and rounds the constant, first rewriting a strict e > 0 as e - 1 >= 0; ZChecker_sound proves the checker sound in Coq/Rocq.
  - Frédéric Besson, 'Fast Reflexive Arithmetic Tactics the Linear Case and Beyond', in Types for Proofs and Programs (TYPES 2006), LNCS 4502, Springer, 2007, pp. 48-62, DOI 10.1007/978-3-540-74464-1_4 (abstract: certificates of infeasibility for quantifier-free linear and non-linear integer arithmetic are produced by off-the-shelf algorithms and validated in Coq by reflexive checkers; full text not read).
- **Design question:** What exactly does accepting a Farkas certificate guarantee, and which checker side conditions (non-negative multipliers, a dense zero test, strictness bookkeeping, positive denominators) carry that guarantee?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Basis:** derived (modeling bridge): a finite system S mentions finitely many variables, so the restriction of a rational point to them can be written p / d with d > 0; hence for finite S 'no scaled point (d, p) with d > 0 satisfies S' corresponds to 'S has no rational solution'. This is argued in prose (module documentation of ToyFarkas.Constraint), not proved in Lean; no rational number type is used.
- **Non-claims:** listed under Boundaries, Non-claims, R1a.

#### R1c — `farkas_sound_scaled_of_nonneg_of_lhsVanishes_of_rhsContradicts` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Known result (Farkas 1902; Motzkin 1936 for strictness) restated for this checker and representation, with each checker condition separated.
- **Plain claim:** If the multipliers are non-negative, the combined left-hand side Sum lambda_k a_k is the zero form in the dense semantics, and the combined conclusion 0 <= Sum lambda_k b_k (or 0 < ... when some positively weighted premise is strict) is false, then no scaled point (d, p) with d > 0 satisfies S.
- **Lean statement** (`Toy.Farkas.farkas_sound_scaled_of_nonneg_of_lhsVanishes_of_rhsContradicts`):

```lean
theorem farkas_sound_scaled_of_nonneg_of_lhsVanishes_of_rhsContradicts (S : List Constraint) (cert : List Int)
  (hnn : multipliersNonneg cert = true) (hlhs : lhsVanishes S cert = true) (hrhs : rhsContradicts S cert = true)
  (d : Int) (hd : 0 < d) (p : Nat → Int) : ¬SatScaled S d p
```

- **Key definitions** (quoted in full under Core definitions): `Constraint`, `multipliersNonneg`, `lhsVanishes`, `rhsContradicts`, `SatScaled`.
- **Hypothesis ledger:**
  - `hnn : multipliersNonneg cert = true` — scaling an inequality by a negative multiplier reverses it; **tight** (counterexample `ce_farkas_negative_multiplier`).
  - `hlhs : lhsVanishes S cert = true` — the combination must be variable-free to be trivially false; **tight** (counterexample `ce_farkas_lhs_not_vanishing`).
  - `hrhs : rhsContradicts S cert = true` — the variable-free conclusion must actually be false (0 <= 0 is not); **tight** (counterexample `ce_farkas_rhs_not_contradicting`).
  - `hd : 0 < d` — positive denominator; **tight** (counterexample `ce_farkas_denominator_zero`).
- **Non-vacuity witness:** All three checker conditions hold for {x0 <= 1, -x0 <= -2} with (1, 1), and d = 1 > 0. Lean: `nv_farkas_sound_structured`.
- **Prior art:**
  - Julius Farkas, 'Theorie der einfachen Ungleichungen', Journal für die reine und angewandte Mathematik 124 (1902), pp. 1-27, DOI 10.1515/crll.1902.124.1 (non-strict linear inequalities).
  - Theodore S. Motzkin, 'Beiträge zur Theorie der linearen Ungleichungen', doctoral dissertation, University of Basel; printed by Azriel, Jerusalem, 1936 (the transposition theorem for systems mixing strict and non-strict inequalities; bibliographic record checked via secondary sources, the German text was not read).
  - Alexander Schrijver, Theory of Linear and Integer Programming, John Wiley & Sons, 1986 (paperback reprint 1998, ISBN 978-0-471-98232-6; chapter list checked on the publisher's page): Chapter 7 'Fundamental concepts and results on polyhedra, linear inequalities, and linear programming' (Farkas' lemma and its variants), Chapter 12 'Primal-dual, elimination, and relaxation methods' (includes elimination), Chapter 23 'Cutting planes'. Specific theorem numbers were not checked against the book.
  - Ralph Bottesch, Max W. Haslbeck, René Thiemann, 'Farkas' Lemma and Motzkin's Transposition Theorem', Archive of Formal Proofs, January 17, 2019, https://isa-afp.org/entries/Farkas.html (Isabelle/HOL, via a verified simplex algorithm: a set of linear constraints is unsatisfiable iff some linear combination of them evaluates to a trivially unsatisfiable inequality; covers mixed strict/non-strict systems).
  - Ralph Bottesch, Alban Reynaud, René Thiemann, 'Linear Inequalities', Archive of Formal Proofs, June 21, 2019, https://isa-afp.org/entries/Linear_Inequalities.html (Isabelle/HOL: fundamental theorem of linear inequalities, Farkas' lemma, Carathéodory's theorem, Farkas-Minkowsky-Weyl theorem, decomposition theorem of polyhedra, Meyer's integer-hull result).
  - Haniel Barbosa, Mathias Fleury, Pascal Fontaine, Hans-Jörg Schurr, 'The Alethe Proof Format: An Evolving Specification and Reference', online specification https://verit.gitlabpages.uliege.be/alethe/specification.pdf (typeset March 31, 2026; accessed 2026-11-20), rule la_generic: one rational coefficient per literal, inequalities multiplied by the coefficient's absolute value; step 4 strengthens each individual (negated, normalized) input literal when all its variables are integer-sorted (a strict bound > d becomes >= d + 1, a non-integer bound is rounded), before the multiplication; the specification remarks that after strengthening the conjunction is unsatisfiable 'even if integer variables are assumed to be real variables'; the sum must be a trivial contradiction. The specification has no Chvátal–Gomory cutting-plane rule.
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Frontend.lean module docstring: an untrusted oracle (simplex by default, Fourier–Motzkin optional) searches for natural-number coefficients k_i with sum k_i t_i = 0 and k_i > 0 for at least one strict hypothesis; the certificate is checked by building a proof term (not by reflection); over Int, linarith 'will fail to prove False on some unsatisfiable problems'.
- **Design question:** What exactly does accepting a Farkas certificate guarantee, and which checker side conditions (non-negative multipliers, a dense zero test, strictness bookkeeping, positive denominators) carry that guarantee?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Basis:** derived (modeling bridge): a finite system S mentions finitely many variables, so the restriction of a rational point to them can be written p / d with d > 0; hence for finite S 'no scaled point (d, p) with d > 0 satisfies S' corresponds to 'S has no rational solution'. This is argued in prose (module documentation of ToyFarkas.Constraint), not proved in Lean; no rational number type is used.
- **Non-claims:** listed under Boundaries, Non-claims, R1c.

#### R2a — `SparseVec.eval_eq_denseDotOn_coeff_of_nodup_of_keys_mem` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Elementary identity for association-list linear forms; sparse linear-form representations with evaluation are standard in verified and proof-producing arithmetic code (Mathlib Linexp, Lean omega Coeffs, Isabelle AFP Simplex and Linear_Diophantine_Preprocessor). No search for a mechanized statement of exactly this form was made; the tier does not depend on one.
- **Plain claim:** For a sparse linear form v (an association list that may repeat indices) and any duplicate-free index list ks containing every index of v, evaluating v at x equals the dense dot product Sum_{i in ks} coeff v i * x i, where coeff v i sums all coefficients recorded for i; the corollary takes ks = [0, ..., n-1] when every index of v is < n.
- **Lean statement** (`Toy.Farkas.SparseVec.eval_eq_denseDotOn_coeff_of_nodup_of_keys_mem`; corollaries and related forms: `SparseVec.eval_eq_denseDot_coeff_of_keys_lt`):

```lean
theorem SparseVec.eval_eq_denseDotOn_coeff_of_nodup_of_keys_mem (v : SparseVec) (ks : List Nat) (hnd : ks.Nodup)
  (hmem : ∀ (p : Nat × Int), p ∈ v → p.fst ∈ ks) (x : Nat → Int) : v.eval x = denseDotOn ks v.coeff x

theorem SparseVec.eval_eq_denseDot_coeff_of_keys_lt (v : SparseVec) (n : Nat)
  (h : ∀ (p : Nat × Int), p ∈ v → p.fst < n) (x : Nat → Int) : v.eval x = denseDot n v.coeff x
```

- **Key definitions** (quoted in full under Core definitions): `SparseVec`, `SparseVec.eval`, `denseDotOn`, `SparseVec.coeff`, `denseDot`.
- **Hypothesis ledger:**
  - `hnd : ks.Nodup (general form only)` — an index listed twice would be counted twice; **tight** (counterexample `ce_eval_eq_denseDotOn_duplicate_index_list`).
  - `hmem : every index of v occurs in ks (general form only)` — an index missing from ks would be dropped; **tight** (counterexample `ce_eval_eq_denseDotOn_missing_index`).
  - `h : every index of v is < n (range corollary only)` — an index >= n would be dropped; **tight** (counterexample `ce_eval_eq_denseDot_index_out_of_range`).
- **Non-vacuity witness:** v = [(0,2),(1,-3),(0,1)], ks = [1,0], x i = i + 4; range form with indices < 3. Lean: `nv_eval_eq_denseDotOn`, `nv_eval_eq_denseDot`.
- **Prior art:**
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Datatypes.lean: `abbrev Linexp : Type := List (Nat × Int)`, a sparse linear form as an association list; its docstring states that some functions assume each index occurs at most once and that the list is sorted in decreasing index order, an invariant 'not enforced by the type' but preserved by the operations (Linexp.get stops at the first smaller key).
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Omega/Constraint.lean and src/Init/Omega/Coeffs.lean: `Lean.Omega.Constraint.div` divides a two-sided bound constraint by a natural number k, rounding the upper bound down and the lower bound up; `Lean.Omega.Constraint.div_sat` proves the divided constraint holds at t / k when k ≠ 0 divides t, and `div_sat'` uses the gcd of the coefficients (integer GCD tightening inside omega's proof-producing procedure); Coeffs.lean notes that omega uses a dense coefficient list and that a sparse `AssocList Nat Int` representation is an alternative.
  - Filip Marić, Mirko Spasić, René Thiemann, 'An Incremental Simplex Algorithm with Unsatisfiable Core Generation', Archive of Formal Proofs, August 24, 2018, https://isa-afp.org/entries/Simplex.html (Isabelle/HOL incremental simplex with unsatisfiable cores; its session includes theories Abstract_Linear_Poly and Linear_Poly_Maps, a representation of linear polynomials; contents of those theories not examined beyond their names).
  - René Thiemann (with contributions from Manuel Eberl), 'A Preprocessor for Linear Diophantine Equalities and Inequalities', Archive of Formal Proofs, June 13, 2024, https://isa-afp.org/entries/Linear_Diophantine_Preprocessor.html (abstract: Pugh's technique of tightening linear inequalities, detection of implicit equalities, and elimination of equations; the result either detects unsatisfiability over Z or returns equisatisfiable inequalities; session theories include Linear_Polynomial, Linear_Polynomial_Impl, Diophantine_Tightening).
- **Design question:** Can a certificate checker work on unnormalized sparse combinations, and which zero test is sound for them?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R2a.

#### R2b — `combineLhs_coeff` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Linearity of the dense semantics, restated for this representation.
- **Plain claim:** The unnormalized sparse combination combineLhs S cert (concatenated scaled premises) has, at each index i, dense coefficient Sum_k lambda_k * coeff(a_k, i), and its value at x is Sum_k lambda_k * (a_k . x), with multiplier k paired with constraint k.
- **Lean statement** (`Toy.Farkas.combineLhs_coeff`; corollaries and related forms: `combineLhs_eval`):

```lean
theorem combineLhs_coeff (S : List Constraint) (cert : List Int) (i : Nat) :
  (combineLhs S cert).coeff i = (List.zipWith (fun l c => l * c.lhs.coeff i) cert S).sum

theorem combineLhs_eval (S : List Constraint) (cert : List Int) (x : Nat → Int) :
  (combineLhs S cert).eval x = (List.zipWith (fun l c => l * c.lhs.eval x) cert S).sum
```

- **Key definitions** (quoted in full under Core definitions): `Constraint`, `SparseVec.coeff`, `combineLhs`, `Constraint.lhs`, `SparseVec.eval`.
- **Hypothesis ledger:** no propositional side-condition hypotheses; both statements are universally quantified over `S : List Constraint`, `cert : List Int`, and `i : Nat` (`combineLhs_coeff`) or `x : Nat → Int` (`combineLhs_eval`).
- **Non-vacuity witness:** Combining {x0 <= 1, -x0 <= -2} with (2, 3) gives coefficient 2*1 + 3*(-1) at index 0 and the expected value at x0 = 5. Lean: `nv_combineLhs_coeff`, `nv_combineLhs_eval`.
- **Prior art:**
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Datatypes.lean: `abbrev Linexp : Type := List (Nat × Int)`, a sparse linear form as an association list; its docstring states that some functions assume each index occurs at most once and that the list is sorted in decreasing index order, an invariant 'not enforced by the type' but preserved by the operations (Linexp.get stops at the first smaller key).
  - Filip Marić, Mirko Spasić, René Thiemann, 'An Incremental Simplex Algorithm with Unsatisfiable Core Generation', Archive of Formal Proofs, August 24, 2018, https://isa-afp.org/entries/Simplex.html (Isabelle/HOL incremental simplex with unsatisfiable cores; its session includes theories Abstract_Linear_Poly and Linear_Poly_Maps, a representation of linear polynomials; contents of those theories not examined beyond their names).
- **Design question:** Can a certificate checker work on unnormalized sparse combinations, and which zero test is sound for them?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R2b.

#### R2d — `SparseVec.isZero_iff_coeff_eq_zero` (characterization)

- **Tier:** T0. **Kind:** characterization. **Depth:** shallow.
- **Tier justification:** Elementary property of the dense semantics, restated for this representation.
- **Plain claim:** The decidable zero test isZero v (every mentioned index has total coefficient 0) holds exactly when the dense coefficient function of v is identically zero.
- **Lean statement** (`Toy.Farkas.SparseVec.isZero_iff_coeff_eq_zero`):

```lean
theorem SparseVec.isZero_iff_coeff_eq_zero (v : SparseVec) : v.isZero = true ↔ ∀ (i : Nat), v.coeff i = 0
```

- **Key definitions** (quoted in full under Core definitions): `SparseVec`, `SparseVec.isZero`, `SparseVec.coeff`.
- **Hypothesis ledger:** no propositional side-condition hypotheses; the statement is universally quantified over `v : SparseVec`.
- **Non-vacuity witness:** [(3,2),(3,-2)] is non-empty yet isZero, and its coefficient at 3 is 0. Lean: `nv_isZero_iff`.
- **Prior art:**
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Datatypes.lean: `abbrev Linexp : Type := List (Nat × Int)`, a sparse linear form as an association list; its docstring states that some functions assume each index occurs at most once and that the list is sorted in decreasing index order, an invariant 'not enforced by the type' but preserved by the operations (Linexp.get stops at the first smaller key).
  - Filip Marić, Mirko Spasić, René Thiemann, 'An Incremental Simplex Algorithm with Unsatisfiable Core Generation', Archive of Formal Proofs, August 24, 2018, https://isa-afp.org/entries/Simplex.html (Isabelle/HOL incremental simplex with unsatisfiable cores; its session includes theories Abstract_Linear_Poly and Linear_Poly_Maps, a representation of linear polynomials; contents of those theories not examined beyond their names).
- **Design question:** Can a certificate checker work on unnormalized sparse combinations, and which zero test is sound for them?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R2d.

#### R3a — `ce_farkas_negative_multiplier` (counterexample)

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Tier justification:** Textbook necessity of the sign condition, as a concrete instance.
- **Plain claim:** With multipliers (1, -1) the satisfiable system {x0 <= 1, x0 <= 2} combines to 0 <= -1: the left-hand side vanishes and the conclusion contradicts, with d = 1 > 0, yet x0 = 0 is a solution; only the non-negativity check fails.
- **Lean statement** (`Toy.Farkas.ce_farkas_negative_multiplier`):

```lean
theorem ce_farkas_negative_multiplier :
  multipliersNonneg [(1 : Int), (-1 : Int)] = false ∧
    lhsVanishes sysTwoUpper [(1 : Int), (-1 : Int)] = true ∧
      rhsContradicts sysTwoUpper [(1 : Int), (-1 : Int)] = true ∧
        (0 : Int) < (1 : Int) ∧ SatScaled sysTwoUpper (1 : Int) (pt1 (0 : Int)) ∧ SatInt sysTwoUpper (pt1 (0 : Int))
```

- **Key definitions** (quoted in full under Core definitions): `multipliersNonneg`, `lhsVanishes`, `sysTwoUpper`, `rhsContradicts`, `SatScaled`, `pt1`, `SatInt`.
- **Hypothesis ledger:** no hypotheses (the statement is a closed, concrete proposition).
- **Non-vacuity witness:** not applicable; the card is a concrete counterexample whose statement asserts every fact it relies on.
- **Prior art:**
  - Julius Farkas, 'Theorie der einfachen Ungleichungen', Journal für die reine und angewandte Mathematik 124 (1902), pp. 1-27, DOI 10.1515/crll.1902.124.1 (non-strict linear inequalities).
  - Haniel Barbosa, Mathias Fleury, Pascal Fontaine, Hans-Jörg Schurr, 'The Alethe Proof Format: An Evolving Specification and Reference', online specification https://verit.gitlabpages.uliege.be/alethe/specification.pdf (typeset March 31, 2026; accessed 2026-11-20), rule la_generic: one rational coefficient per literal, inequalities multiplied by the coefficient's absolute value; step 4 strengthens each individual (negated, normalized) input literal when all its variables are integer-sorted (a strict bound > d becomes >= d + 1, a non-integer bound is rounded), before the multiplication; the specification remarks that after strengthening the conjunction is unsatisfiable 'even if integer variables are assumed to be real variables'; the sum must be a trivial contradiction. The specification has no Chvátal–Gomory cutting-plane rule.
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Frontend.lean module docstring: an untrusted oracle (simplex by default, Fourier–Motzkin optional) searches for natural-number coefficients k_i with sum k_i t_i = 0 and k_i > 0 for at least one strict hypothesis; the certificate is checked by building a proof term (not by reflection); over Int, linarith 'will fail to prove False on some unsatisfiable problems'.
- **Design question:** What exactly does accepting a Farkas certificate guarantee, and which checker side conditions (non-negative multipliers, a dense zero test, strictness bookkeeping, positive denominators) carry that guarantee?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R3a.

#### R3b — `ce_farkas_strictness_ignored` (counterexample)

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Tier justification:** The positive-multiplier-on-a-strict-premise condition is part of Motzkin's transposition theorem and of linarith's certificate condition; concrete instances of violating it.
- **Plain claim:** Two strictness-bookkeeping errors make a Farkas checker unsound: (1) treating every combined conclusion as strict accepts 0 <= 0 as contradictory and 'certifies' the satisfiable {x0 <= 1, -x0 <= -1} with (1, 1), which rhsContradicts and checkFarkas both reject; (2) declaring the combination strict whenever some premise is strict, even one with multiplier 0, 'certifies' the satisfiable {x0 <= 1, -x0 <= -1, x1 < 5} with (1, 1, 0), which rhsContradicts rejects, and hence so does checkFarkas (its definition requires rhsContradicts = true; this last step follows by unfolding checkFarkas and is not a separate conjunct of ce_farkas_strict_flag_from_zero_weight).
- **Lean statement** (`Toy.Farkas.ce_farkas_strictness_ignored`; corollaries and related forms: `ce_farkas_strict_flag_from_zero_weight`):

```lean
theorem ce_farkas_strictness_ignored :
  multipliersNonneg [(1 : Int), (1 : Int)] = true ∧
    lhsVanishes sysEq [(1 : Int), (1 : Int)] = true ∧
      rhsContradictsIgnoringStrictness sysEq [(1 : Int), (1 : Int)] = true ∧
        rhsContradicts sysEq [(1 : Int), (1 : Int)] = false ∧
          checkFarkas sysEq [(1 : Int), (1 : Int)] = false ∧
            (0 : Int) < (1 : Int) ∧ SatInt sysEq (pt1 (1 : Int)) ∧ SatScaled sysEq (1 : Int) (pt1 (1 : Int))

theorem ce_farkas_strict_flag_from_zero_weight :
  multipliersNonneg [1, 1, 0] = true ∧
    lhsVanishes sysEqPlusStrict [1, 1, 0] = true ∧
      rhsContradictsAnyPremise sysEqPlusStrict [1, 1, 0] = true ∧
        rhsContradicts sysEqPlusStrict [1, 1, 0] = false ∧ SatInt sysEqPlusStrict (pt2 1 0)
```

- **Key definitions** (quoted in full under Core definitions): `multipliersNonneg`, `lhsVanishes`, `sysEq`, `rhsContradictsIgnoringStrictness`, `rhsContradicts`, `checkFarkas`, `SatInt`, `pt1`, `SatScaled`, `sysEqPlusStrict`, `rhsContradictsAnyPremise`, `pt2`.
- **Hypothesis ledger:** no hypotheses (the statement is a closed, concrete proposition).
- **Non-vacuity witness:** not applicable; the card is a concrete counterexample whose statement asserts every fact it relies on.
- **Prior art:**
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Frontend.lean module docstring: an untrusted oracle (simplex by default, Fourier–Motzkin optional) searches for natural-number coefficients k_i with sum k_i t_i = 0 and k_i > 0 for at least one strict hypothesis; the certificate is checked by building a proof term (not by reflection); over Int, linarith 'will fail to prove False on some unsatisfiable problems'.
  - Ralph Bottesch, Max W. Haslbeck, René Thiemann, 'Farkas' Lemma and Motzkin's Transposition Theorem', Archive of Formal Proofs, January 17, 2019, https://isa-afp.org/entries/Farkas.html (Isabelle/HOL, via a verified simplex algorithm: a set of linear constraints is unsatisfiable iff some linear combination of them evaluates to a trivially unsatisfiable inequality; covers mixed strict/non-strict systems).
  - Theodore S. Motzkin, 'Beiträge zur Theorie der linearen Ungleichungen', doctoral dissertation, University of Basel; printed by Azriel, Jerusalem, 1936 (the transposition theorem for systems mixing strict and non-strict inequalities; bibliographic record checked via secondary sources, the German text was not read).
  - Bruno Dutertre and Leonardo de Moura, 'A Fast Linear-Arithmetic Solver for DPLL(T)', CAV 2006, LNCS 4144, pp. 81-94, DOI 10.1007/11817963_11 (simplex-based solver for DPLL(T); strict inequalities are handled with bounds over rationals extended by a symbolic infinitesimal delta, e.g. x < b as x <= b - delta, rather than by a strictness flag on Farkas combinations; metadata via Crossref, the delta mechanism confirmed from secondary descriptions, full text not read).
- **Design question:** What exactly does accepting a Farkas certificate guarantee, and which checker side conditions (non-negative multipliers, a dense zero test, strictness bookkeeping, positive denominators) carry that guarantee?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R3b.

#### R3d — `checkFarkasTightened_sound_int` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Integer strengthening of strict bounds is standard (Alethe la_generic for integer-sorted variables; Rocq micromega's genCuttingPlane, mechanized; Pugh-style tightening in AFP Linear_Diophantine_Preprocessor).
- **Plain claim:** If checkFarkas accepts a certificate for the integer-tightened system (each strict a . x < b replaced by a . x <= b - 1), then the original system has no integer solution x : Nat -> Int.
- **Lean statement** (`Toy.Farkas.checkFarkasTightened_sound_int`):

```lean
theorem checkFarkasTightened_sound_int (S : List Constraint) (cert : List Int)
  (h : checkFarkasTightened S cert = true) (x : Nat → Int) : ¬SatInt S x
```

- **Key definitions** (quoted in full under Core definitions): `Constraint`, `checkFarkasTightened`, `SatInt`.
- **Hypothesis ledger:**
  - `h : checkFarkasTightened S cert = true` — the certificate is accepted for the tightened system; **tight** (counterexample `ce_checkFarkasTightened_rejects_satisfiable`).
  - `x : Nat -> Int (integral variables, by type)` — replacing a . x < b by a . x <= b - 1 is valid only at integer points; **tight** (counterexample `ce_tightening_unsound_over_rat`).
- **Non-vacuity witness:** {x0 < 1, -x0 < 0} (0 < x0 < 1) is accepted with (1, 1) after tightening. Lean: `nv_checkFarkasTightened`.
- **Prior art:**
  - Haniel Barbosa, Mathias Fleury, Pascal Fontaine, Hans-Jörg Schurr, 'The Alethe Proof Format: An Evolving Specification and Reference', online specification https://verit.gitlabpages.uliege.be/alethe/specification.pdf (typeset March 31, 2026; accessed 2026-11-20), rule la_generic: one rational coefficient per literal, inequalities multiplied by the coefficient's absolute value; step 4 strengthens each individual (negated, normalized) input literal when all its variables are integer-sorted (a strict bound > d becomes >= d + 1, a non-integer bound is rounded), before the multiplication; the specification remarks that after strengthening the conjunction is unsatisfiable 'even if integer variables are assumed to be real variables'; the sum must be a trivial contradiction. The specification has no Chvátal–Gomory cutting-plane rule.
  - Rocq Stdlib, rocq-prover/stdlib commit f50ccefc570f6b815874df96bb3b872611cfaf0e, theories/micromega/ZMicromega.v: certificate type ZArithProof with constructors DoneProof, RatProof, CutProof, SplitProof, deprecated_EnumProof, ExProof; genCuttingPlane divides a constraint by the gcd of its coefficients and rounds the constant, first rewriting a strict e > 0 as e - 1 >= 0; ZChecker_sound proves the checker sound in Coq/Rocq.
  - René Thiemann (with contributions from Manuel Eberl), 'A Preprocessor for Linear Diophantine Equalities and Inequalities', Archive of Formal Proofs, June 13, 2024, https://isa-afp.org/entries/Linear_Diophantine_Preprocessor.html (abstract: Pugh's technique of tightening linear inequalities, detection of implicit equalities, and elimination of equations; the result either detects unsatisfiability over Z or returns equisatisfiable inequalities; session theories include Linear_Polynomial, Linear_Polynomial_Impl, Diophantine_Tightening).
- **Design question:** What exactly does accepting a Farkas certificate guarantee, and which checker side conditions (non-negative multipliers, a dense zero test, strictness bookkeeping, positive denominators) carry that guarantee?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R3d.

#### R3e — `ce_tightening_unsound_over_rat` (counterexample)

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Tier justification:** Textbook fact (strict-to-non-strict strengthening needs integrality), as a concrete instance.
- **Plain claim:** The tightened checker accepts (1, 1) for {x0 < 1, -x0 < 0}, which the scaled point (d, p) = (2, 1) with d > 0 satisfies (read through the rational modeling bridge: x0 = 1/2); the untightened checker rejects the same certificate. So integer tightening is not sound over scaled points; over integer points it is sound (R3d).
- **Lean statement** (`Toy.Farkas.ce_tightening_unsound_over_rat`):

```lean
theorem ce_tightening_unsound_over_rat :
  checkFarkasTightened sysOpenUnit [(1 : Int), (1 : Int)] = true ∧
    checkFarkas sysOpenUnit [(1 : Int), (1 : Int)] = false ∧
      (0 : Int) < (2 : Int) ∧ SatScaled sysOpenUnit (2 : Int) (pt1 (1 : Int))
```

- **Key definitions** (quoted in full under Core definitions): `checkFarkasTightened`, `sysOpenUnit`, `checkFarkas`, `SatScaled`, `pt1`.
- **Hypothesis ledger:** no hypotheses (the statement is a closed, concrete proposition).
- **Non-vacuity witness:** not applicable; the card is a concrete counterexample whose statement asserts every fact it relies on.
- **Prior art:**
  - Haniel Barbosa, Mathias Fleury, Pascal Fontaine, Hans-Jörg Schurr, 'The Alethe Proof Format: An Evolving Specification and Reference', online specification https://verit.gitlabpages.uliege.be/alethe/specification.pdf (typeset March 31, 2026; accessed 2026-11-20), rule la_generic: one rational coefficient per literal, inequalities multiplied by the coefficient's absolute value; step 4 strengthens each individual (negated, normalized) input literal when all its variables are integer-sorted (a strict bound > d becomes >= d + 1, a non-integer bound is rounded), before the multiplication; the specification remarks that after strengthening the conjunction is unsatisfiable 'even if integer variables are assumed to be real variables'; the sum must be a trivial contradiction. The specification has no Chvátal–Gomory cutting-plane rule.
- **Design question:** What exactly does accepting a Farkas certificate guarantee, and which checker side conditions (non-negative multipliers, a dense zero test, strictness bookkeeping, positive denominators) carry that guarantee?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Basis:** derived (modeling bridge): the scaled point (d, p) = (2, 1) with d > 0 (pt1 1 is the point with x0 = 1 and all other coordinates 0) stands for the rational point p / d, i.e. x0 = 1/2, so the system that the tightened checker accepts is rationally feasible. The correspondence between scaled points and rational points of a finite system is argued in prose (module documentation of ToyFarkas.Constraint), not proved in Lean; no rational number type is used.
- **Non-claims:** listed under Boundaries, Non-claims, R3e.

#### R3f — `ce_zero_test_index_blind` (counterexample)

- **Tier:** T1. **Kind:** counterexample. **Depth:** definitional.
- **Tier justification:** Implementation folklore (sparse lookups assume a normalized, duplicate-free form; Mathlib's Linexp documents this invariant as not enforced by the type), made precise as concrete instances; no mechanized statement of these pitfalls was located (search limited to the sources listed).
- **Plain claim:** Zero tests that ignore the dense semantics make the checker unsound: (1) an index-blind test (all coefficients sum to 0) accepts x0 - x1 and 'certifies' the satisfiable {x0 - x1 <= -1} with (1); (2) a first-match test (read only the first entry per index) accepts [(0,0),(0,1)] and 'certifies' the satisfiable {0*x0 + 1*x0 <= -1} with (1); (3) the first-match failure arises even when every input constraint is duplicate-free: for {x0 <= 0, x0 <= -1} with (0, 1) the combination is [(0,0),(0,1)] and x0 = -1 is a solution. checkFarkas rejects all three.
- **Lean statement** (`Toy.Farkas.ce_zero_test_index_blind`; corollaries and related forms: `ce_zero_test_first_match`, `ce_zero_test_first_match_dupfree_inputs`):

```lean
theorem ce_zero_test_index_blind :
  multipliersNonneg [1] = true ∧
    checkFarkas [{ lhs := [(0, 1), (1, -1)], rel := Rel.le, rhs := -1 }] [1] = false ∧
      isZeroIndexBlind (combineLhs [{ lhs := [(0, 1), (1, -1)], rel := Rel.le, rhs := -1 }] [1]) = true ∧
        lhsVanishes [{ lhs := [(0, 1), (1, -1)], rel := Rel.le, rhs := -1 }] [1] = false ∧
          rhsContradicts [{ lhs := [(0, 1), (1, -1)], rel := Rel.le, rhs := -1 }] [1] = true ∧
            SatInt [{ lhs := [(0, 1), (1, -1)], rel := Rel.le, rhs := -1 }] (pt2 0 1)

theorem ce_zero_test_first_match :
  multipliersNonneg [1] = true ∧
    checkFarkas [{ lhs := [(0, 0), (0, 1)], rel := Rel.le, rhs := -1 }] [1] = false ∧
      isZeroFirstMatch (combineLhs [{ lhs := [(0, 0), (0, 1)], rel := Rel.le, rhs := -1 }] [1]) = true ∧
        lhsVanishes [{ lhs := [(0, 0), (0, 1)], rel := Rel.le, rhs := -1 }] [1] = false ∧
          rhsContradicts [{ lhs := [(0, 0), (0, 1)], rel := Rel.le, rhs := -1 }] [1] = true ∧
            SatInt [{ lhs := [(0, 0), (0, 1)], rel := Rel.le, rhs := -1 }] (pt1 (-1))

theorem ce_zero_test_first_match_dupfree_inputs :
  combineLhs [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }, { lhs := [(0, 1)], rel := Rel.le, rhs := -1 }] [0, 1] =
      [(0, 0), (0, 1)] ∧
    multipliersNonneg [0, 1] = true ∧
      checkFarkas [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }, { lhs := [(0, 1)], rel := Rel.le, rhs := -1 }] [0, 1] =
          false ∧
        isZeroFirstMatch
              (combineLhs [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }, { lhs := [(0, 1)], rel := Rel.le, rhs := -1 }]
                [0, 1]) =
            true ∧
          rhsContradicts [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }, { lhs := [(0, 1)], rel := Rel.le, rhs := -1 }]
                [0, 1] =
              true ∧
            SatInt [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }, { lhs := [(0, 1)], rel := Rel.le, rhs := -1 }]
              (pt1 (-1))
```

- **Key definitions** (quoted in full under Core definitions): `multipliersNonneg`, `checkFarkas`, `Constraint`, `isZeroIndexBlind`, `combineLhs`, `lhsVanishes`, `rhsContradicts`, `SatInt`, `pt2`, `isZeroFirstMatch`, `pt1`, `SparseVec`.
- **Hypothesis ledger:** no hypotheses (the statement is a closed, concrete proposition).
- **Non-vacuity witness:** not applicable; the card is a concrete counterexample whose statement asserts every fact it relies on.
- **Prior art:**
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Datatypes.lean: `abbrev Linexp : Type := List (Nat × Int)`, a sparse linear form as an association list; its docstring states that some functions assume each index occurs at most once and that the list is sorted in decreasing index order, an invariant 'not enforced by the type' but preserved by the operations (Linexp.get stops at the first smaller key).
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Omega/Constraint.lean and src/Init/Omega/Coeffs.lean: `Lean.Omega.Constraint.div` divides a two-sided bound constraint by a natural number k, rounding the upper bound down and the lower bound up; `Lean.Omega.Constraint.div_sat` proves the divided constraint holds at t / k when k ≠ 0 divides t, and `div_sat'` uses the gcd of the coefficients (integer GCD tightening inside omega's proof-producing procedure); Coeffs.lean notes that omega uses a dense coefficient list and that a sparse `AssocList Nat Int` representation is an alternative.
- **Design question:** Can a certificate checker work on unnormalized sparse combinations, and which zero test is sound for them?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R3f.

#### R4a — `farkas_complete_scaled` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** substantive.
- **Tier justification:** Motzkin's transposition theorem with rational multipliers cleared to integers; mechanized in Isabelle (AFP Farkas). Proved here by integer-scaled Fourier-Motzkin elimination on the homogenized system (module ToyFarkas.Motzkin).
- **Plain claim:** Every finite list S of integer linear constraints (each a . x <= b or a . x < b) that has no scaled solution (d, p) with d > 0 has a certificate accepted by checkFarkas.
- **Lean statement** (`Toy.Farkas.farkas_complete_scaled`):

```lean
theorem farkas_complete_scaled (S : List Constraint) (h : ∀ (d : Int) (p : Nat → Int), 0 < d → ¬SatScaled S d p) :
  ∃ cert, checkFarkas S cert = true
```

- **Key definitions** (quoted in full under Core definitions): `Constraint`, `SatScaled`, `checkFarkas`.
- **Hypothesis ledger:**
  - `h : no scaled point (d, p) with d > 0 satisfies S` — completeness is only for systems without scaled (rational) solutions; **tight** (counterexample `ce_farkas_complete_feasible_system`).
- **Non-vacuity witness:** {x0 <= 1, -x0 <= -2} and {x0 < 1, -x0 <= -1} satisfy the hypothesis (proved from R1a) and have accepted certificates. Lean: `nv_farkas_complete_scaled`.
- **Prior art:**
  - Julius Farkas, 'Theorie der einfachen Ungleichungen', Journal für die reine und angewandte Mathematik 124 (1902), pp. 1-27, DOI 10.1515/crll.1902.124.1 (non-strict linear inequalities).
  - Theodore S. Motzkin, 'Beiträge zur Theorie der linearen Ungleichungen', doctoral dissertation, University of Basel; printed by Azriel, Jerusalem, 1936 (the transposition theorem for systems mixing strict and non-strict inequalities; bibliographic record checked via secondary sources, the German text was not read).
  - Alexander Schrijver, Theory of Linear and Integer Programming, John Wiley & Sons, 1986 (paperback reprint 1998, ISBN 978-0-471-98232-6; chapter list checked on the publisher's page): Chapter 7 'Fundamental concepts and results on polyhedra, linear inequalities, and linear programming' (Farkas' lemma and its variants), Chapter 12 'Primal-dual, elimination, and relaxation methods' (includes elimination), Chapter 23 'Cutting planes'. Specific theorem numbers were not checked against the book.
  - Ralph Bottesch, Max W. Haslbeck, René Thiemann, 'Farkas' Lemma and Motzkin's Transposition Theorem', Archive of Formal Proofs, January 17, 2019, https://isa-afp.org/entries/Farkas.html (Isabelle/HOL, via a verified simplex algorithm: a set of linear constraints is unsatisfiable iff some linear combination of them evaluates to a trivially unsatisfiable inequality; covers mixed strict/non-strict systems).
  - Ralph Bottesch, Alban Reynaud, René Thiemann, 'Linear Inequalities', Archive of Formal Proofs, June 21, 2019, https://isa-afp.org/entries/Linear_Inequalities.html (Isabelle/HOL: fundamental theorem of linear inequalities, Farkas' lemma, Carathéodory's theorem, Farkas-Minkowsky-Weyl theorem, decomposition theorem of polyhedra, Meyer's integer-hull result).
  - René Thiemann, 'Duality of Linear Programming', Archive of Formal Proofs, February 3, 2022, https://isa-afp.org/entries/LP_Duality.html (weak and strong LP duality, based on the formalization of Farkas' lemma in 'Linear Inequalities').
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Analysis/Convex/Cone/Dual.lean: Farkas' lemma in geometric form for proper cones in locally convex real topological vector spaces (ProperCone.hyperplane_separation, ProperCone.hyperplane_separation_point); real-valued, not a certificate checker.
  - Xavier Allamigeon, Ricardo D. Katz, 'A Formalization of Convex Polyhedra Based on the Simplex Method', Journal of Automated Reasoning 63 (2019), pp. 323-345, DOI 10.1007/s10817-018-9477-1 (Coq formalization of convex polyhedra via the simplex method; metadata checked via Crossref, full text not read).
- **Design question:** Is a Farkas checker complete for rational infeasibility, and why is it incomplete for integer infeasibility?
- **Proof:** see "How Farkas completeness (R4a) is proved" above.
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Basis:** derived (modeling bridge): a finite system S mentions finitely many variables, so the restriction of a rational point to them can be written p / d with d > 0; hence for finite S 'no scaled point (d, p) with d > 0 satisfies S' corresponds to 'S has no rational solution'. This is argued in prose (module documentation of ToyFarkas.Constraint), not proved in Lean; no rational number type is used. Read through this bridge, R4a is completeness of checkFarkas for rationally infeasible finite systems.
- **Non-claims:** listed under Boundaries, Non-claims, R4a.

#### R4b — `ce_farkas_incomplete_int` (impossibility)

- **Tier:** T0. **Kind:** impossibility. **Depth:** shallow.
- **Tier justification:** The textbook integrality gap of the LP relaxation (linarith documents failure on some unsatisfiable problems over Int), as a concrete instance.
- **Plain claim:** The system sysHalf = {2x0 <= 1, -2x0 <= -1} has no integer solution x : Nat -> Int, yet checkFarkas rejects every certificate cert : List Int for it.
- **Lean statement** (`Toy.Farkas.ce_farkas_incomplete_int`):

```lean
theorem ce_farkas_incomplete_int :
  (∀ (x : Nat → Int), ¬SatInt sysHalf x) ∧ ∀ (cert : List Int), checkFarkas sysHalf cert = false
```

- **Key definitions** (quoted in full under Core definitions): `SatInt`, `sysHalf`, `checkFarkas`.
- **Hypothesis ledger:** no side-condition hypotheses; the statement is a closed impossibility statement about the concrete system `sysHalf`, universally quantified over all integer points `x : Nat → Int` and all certificates `cert : List Int`.
- **Non-vacuity witness:** The statement is about one concrete system (sysHalf) and quantifies over all integer points and all certificates; it has no side-condition hypotheses.
- **Positive control** (a nearby setting where the conclusion fails): `nv_checkCutCert_sound_int`, `sysHalf_refuted_by_case_split`.
- **Prior art:**
  - Alexander Schrijver, Theory of Linear and Integer Programming, John Wiley & Sons, 1986 (paperback reprint 1998, ISBN 978-0-471-98232-6; chapter list checked on the publisher's page): Chapter 7 'Fundamental concepts and results on polyhedra, linear inequalities, and linear programming' (Farkas' lemma and its variants), Chapter 12 'Primal-dual, elimination, and relaxation methods' (includes elimination), Chapter 23 'Cutting planes'. Specific theorem numbers were not checked against the book.
  - Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Frontend.lean module docstring: an untrusted oracle (simplex by default, Fourier–Motzkin optional) searches for natural-number coefficients k_i with sum k_i t_i = 0 and k_i > 0 for at least one strict hypothesis; the certificate is checked by building a proof term (not by reflection); over Int, linarith 'will fail to prove False on some unsatisfiable problems'.
  - Ralph E. Gomory, 'Outline of an algorithm for integer solutions to linear programs', Bulletin of the American Mathematical Society 64(5) (1958), pp. 275-278, DOI 10.1090/S0002-9904-1958-10224-4.
  - William Pugh, 'A practical algorithm for exact array dependence analysis', Communications of the ACM 35(8) (1992), pp. 102-114, DOI 10.1145/135226.135233 (the Omega test: integer tightening and exact projection with dark shadows and splintering; metadata via Crossref, full text not read).
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Omega/Constraint.lean and src/Init/Omega/Coeffs.lean: `Lean.Omega.Constraint.div` divides a two-sided bound constraint by a natural number k, rounding the upper bound down and the lower bound up; `Lean.Omega.Constraint.div_sat` proves the divided constraint holds at t / k when k ≠ 0 divides t, and `div_sat'` uses the gcd of the coefficients (integer GCD tightening inside omega's proof-producing procedure); Coeffs.lean notes that omega uses a dense coefficient list and that a sparse `AssocList Nat Int` representation is an alternative.
  - Rocq Stdlib, rocq-prover/stdlib commit f50ccefc570f6b815874df96bb3b872611cfaf0e, theories/micromega/ZMicromega.v: certificate type ZArithProof with constructors DoneProof, RatProof, CutProof, SplitProof, deprecated_EnumProof, ExProof; genCuttingPlane divides a constraint by the gcd of its coefficients and rounds the constant, first rewriting a strict e > 0 as e - 1 >= 0; ZChecker_sound proves the checker sound in Coq/Rocq.
  - Alan J. Hoffman, Joseph B. Kruskal, 'Integral boundary points of convex polyhedra', in Linear Inequalities and Related Systems (H. W. Kuhn, A. W. Tucker, eds.), Annals of Mathematics Studies 38, Princeton University Press, 1956, pp. 223-246 (total unimodularity and integral polyhedra; bibliographic record via secondary sources, full text not read).
- **Design question:** Is a Farkas checker complete for rational infeasibility, and why is it incomplete for integer infeasibility?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Basis:** derived (modeling bridge): the reason no certificate is accepted is that sysHalf is satisfied by the scaled point (d, p) = (2, 1) with d > 0 (SatScaled sysHalf 2 (pt1 1) is kernel-checked as a conjunct of ce_cgCut_unsound_over_rat and of ce_checkCutCert_unsound_over_rat, not of ce_farkas_incomplete_int), so R1a rules out every accepted certificate. Read through the rational modeling bridge, that point is x0 = 1/2: sysHalf is rationally feasible but has no integer solution. ce_farkas_incomplete_int itself asserts only integer infeasibility and the rejection of every certificate. The correspondence between scaled points and rational points of a finite system is argued in prose (module documentation of ToyFarkas.Constraint), not proved in Lean; no rational number type is used.
- **Non-claims:** listed under Boundaries, Non-claims, R4b.

#### R5a — `cgCut_sound_int_of_nonneg_of_div_pos_of_divisible` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Chvátal–Gomory rounding is classical; Rocq micromega mechanizes soundness of its cutting-plane checker and Lean's omega mechanizes GCD tightening (div_sat).
- **Plain claim:** For a system S and a Chvátal–Gomory step (multipliers lambda paired with the constraints by List.zipWith, divisor g): every strict premise a . x < b is first tightened to a . x <= b - 1; if lambda >= 0, g > 0, and g divides every dense coefficient of Sum lambda_k a_k, then every integer solution of S satisfies the cut (Sum lambda_k a_k / g) . x <= floor((Sum lambda_k b'_k) / g), where b'_k = b_k for <= and b_k - 1 for <. The checked step cgDerive returns this cut exactly when the three conditions hold, so every cut it returns is satisfied by every integer solution (cgDerive_sound_int).
- **Lean statement** (`Toy.Farkas.cgCut_sound_int_of_nonneg_of_div_pos_of_divisible`; corollaries and related forms: `cgDerive_sound_int`):

```lean
theorem cgCut_sound_int_of_nonneg_of_div_pos_of_divisible (S : List Constraint) (k : CGStep)
  (hnn : multipliersNonneg k.mult = true) (hg : 0 < k.div) (hdiv : cgDivisible S k = true) (x : Nat → Int)
  (hx : SatInt S x) : (cgCut S k).HoldsInt x

theorem cgDerive_sound_int (S : List Constraint) (k : CGStep) (c : Constraint) (h : cgDerive S k = some c)
  (x : Nat → Int) (hx : SatInt S x) : c.HoldsInt x
```

- **Key definitions** (quoted in full under Core definitions): `Constraint`, `CGStep`, `multipliersNonneg`, `CGStep.mult`, `CGStep.div`, `cgDivisible`, `SatInt`, `Constraint.HoldsInt`, `cgCut`, `cgDerive`.
- **Hypothesis ledger:**
  - `hnn : multipliersNonneg k.mult = true (cgCut_sound_int_of_nonneg_of_div_pos_of_divisible only)` — negative multipliers reverse inequalities; **tight** (counterexample `ce_cgCut_negative_multiplier`).
  - `hg : 0 < k.div (cgCut_sound_int_of_nonneg_of_div_pos_of_divisible only)` — dividing by a negative number reverses the inequality; **tight** (counterexample `ce_cgCut_negative_divisor`).
  - `hdiv : cgDivisible S k = true (cgCut_sound_int_of_nonneg_of_div_pos_of_divisible only)` — rounding is only valid when the divided left-hand side has integer coefficients; **tight** (counterexample `ce_cgCut_not_divisible`).
  - `hx : SatInt S x` — the point must satisfy the premises; **tight** (counterexample `ce_cgCut_point_not_solution`).
  - `x : Nat -> Int (integral variables, by type)` — rounding the right-hand side down, and tightening strict premises, are only valid at integer points (even with divisor 1); **tight** (counterexample `ce_cgCut_unsound_over_rat`, `ce_cgCut_div_one_unsound_over_rat`).
  - `h : cgDerive S k = some c (cgDerive_sound_int only)` — c must be produced by a validated step; **tight** (counterexample `ce_cgDerive_rejected`).
- **Non-vacuity witness:** {2x0 <= 3} with step ((1), 2): the step is valid, cgDerive returns x0 <= 1, and it holds at the integer solution x0 = 1. Lean: `nv_cgCut_sound_int`.
- **Prior art:**
  - Vašek Chvátal, 'Edmonds polytopes and a hierarchy of combinatorial problems', Discrete Mathematics 4(4) (1973), pp. 305-337, DOI 10.1016/0012-365X(73)90167-2 (cutting-plane hierarchy; finitely many rounds of cuts reach the integer hull for bounded rational polytopes).
  - Ralph E. Gomory, 'Outline of an algorithm for integer solutions to linear programs', Bulletin of the American Mathematical Society 64(5) (1958), pp. 275-278, DOI 10.1090/S0002-9904-1958-10224-4.
  - Alexander Schrijver, Theory of Linear and Integer Programming, John Wiley & Sons, 1986 (paperback reprint 1998, ISBN 978-0-471-98232-6; chapter list checked on the publisher's page): Chapter 7 'Fundamental concepts and results on polyhedra, linear inequalities, and linear programming' (Farkas' lemma and its variants), Chapter 12 'Primal-dual, elimination, and relaxation methods' (includes elimination), Chapter 23 'Cutting planes'. Specific theorem numbers were not checked against the book.
  - Rocq Stdlib, rocq-prover/stdlib commit f50ccefc570f6b815874df96bb3b872611cfaf0e, theories/micromega/ZMicromega.v: certificate type ZArithProof with constructors DoneProof, RatProof, CutProof, SplitProof, deprecated_EnumProof, ExProof; genCuttingPlane divides a constraint by the gcd of its coefficients and rounds the constant, first rewriting a strict e > 0 as e - 1 >= 0; ZChecker_sound proves the checker sound in Coq/Rocq.
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Omega/Constraint.lean and src/Init/Omega/Coeffs.lean: `Lean.Omega.Constraint.div` divides a two-sided bound constraint by a natural number k, rounding the upper bound down and the lower bound up; `Lean.Omega.Constraint.div_sat` proves the divided constraint holds at t / k when k ≠ 0 divides t, and `div_sat'` uses the gcd of the coefficients (integer GCD tightening inside omega's proof-producing procedure); Coeffs.lean notes that omega uses a dense coefficient list and that a sparse `AssocList Nat Int` representation is an alternative.
  - William Pugh, 'A practical algorithm for exact array dependence analysis', Communications of the ACM 35(8) (1992), pp. 102-114, DOI 10.1145/135226.135233 (the Omega test: integer tightening and exact projection with dark shadows and splintering; metadata via Crossref, full text not read).
  - René Thiemann (with contributions from Manuel Eberl), 'A Preprocessor for Linear Diophantine Equalities and Inequalities', Archive of Formal Proofs, June 13, 2024, https://isa-afp.org/entries/Linear_Diophantine_Preprocessor.html (abstract: Pugh's technique of tightening linear inequalities, detection of implicit equalities, and elimination of equations; the result either detects unsatisfiability over Z or returns equisatisfiable inequalities; session theories include Linear_Polynomial, Linear_Polynomial_Impl, Diophantine_Tightening).
- **Design question:** What does a Chvátal–Gomory cut checker guarantee, under which side conditions (non-negative multipliers, positive divisor, integral combined coefficients, integral variables), and what does a cut-plus-Farkas certificate prove?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R5a.

#### R5c — `checkCutCert_sound_int` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Known result restated for this checker and representation (Rocq micromega mechanizes a checker with cutting-plane steps).
- **Plain claim:** If the cut-plus-Farkas checker accepts (every Chvátal–Gomory step is valid when applied in order to the original system extended by earlier cuts, each step tightening strict premises to <= b - 1 before combining, and checkFarkas, which does not tighten, accepts the final multipliers for the extended system), then S has no integer solution x : Nat -> Int.
- **Lean statement** (`Toy.Farkas.checkCutCert_sound_int`):

```lean
theorem checkCutCert_sound_int (S : List Constraint) (cc : CutCert) (h : checkCutCert S cc = true) (x : Nat → Int) :
  ¬SatInt S x
```

- **Key definitions** (quoted in full under Core definitions): `Constraint`, `CutCert`, `checkCutCert`, `SatInt`.
- **Hypothesis ledger:**
  - `h : checkCutCert S cc = true` — the certificate is accepted; **tight** (counterexample `ce_checkCutCert_rejects_satisfiable`).
  - `x : Nat -> Int (integral variables, by type)` — cuts are only valid at integer points; **tight** (counterexample `ce_checkCutCert_unsound_over_rat`).
- **Non-vacuity witness:** {2x0 <= 1, -2x0 <= -1} is refuted by deriving x0 <= 0 and -x0 <= -1 and combining with (0, 0, 1, 1); plain Farkas certificates cannot refute it (R4b). Lean: `nv_checkCutCert_sound_int`.
- **Prior art:**
  - Vašek Chvátal, 'Edmonds polytopes and a hierarchy of combinatorial problems', Discrete Mathematics 4(4) (1973), pp. 305-337, DOI 10.1016/0012-365X(73)90167-2 (cutting-plane hierarchy; finitely many rounds of cuts reach the integer hull for bounded rational polytopes).
  - Alexander Schrijver, 'On cutting planes', in Combinatorics 79, Part II, Annals of Discrete Mathematics, Vol. 9, North-Holland, 1980, pp. 291-296, DOI 10.1016/S0167-5060(08)70085-2 (extends the finiteness of the cutting-plane hierarchy to arbitrary, possibly unbounded, rational polyhedra; metadata via Crossref, volume number via secondary records, full text not read).
  - Ralph E. Gomory, 'Outline of an algorithm for integer solutions to linear programs', Bulletin of the American Mathematical Society 64(5) (1958), pp. 275-278, DOI 10.1090/S0002-9904-1958-10224-4.
  - Rocq Stdlib, rocq-prover/stdlib commit f50ccefc570f6b815874df96bb3b872611cfaf0e, theories/micromega/ZMicromega.v: certificate type ZArithProof with constructors DoneProof, RatProof, CutProof, SplitProof, deprecated_EnumProof, ExProof; genCuttingPlane divides a constraint by the gcd of its coefficients and rounds the constant, first rewriting a strict e > 0 as e - 1 >= 0; ZChecker_sound proves the checker sound in Coq/Rocq.
  - Frédéric Besson, 'Fast Reflexive Arithmetic Tactics the Linear Case and Beyond', in Types for Proofs and Programs (TYPES 2006), LNCS 4502, Springer, 2007, pp. 48-62, DOI 10.1007/978-3-540-74464-1_4 (abstract: certificates of infeasibility for quantifier-free linear and non-linear integer arithmetic are produced by off-the-shelf algorithms and validated in Coq by reflexive checkers; full text not read).
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Omega/Constraint.lean and src/Init/Omega/Coeffs.lean: `Lean.Omega.Constraint.div` divides a two-sided bound constraint by a natural number k, rounding the upper bound down and the lower bound up; `Lean.Omega.Constraint.div_sat` proves the divided constraint holds at t / k when k ≠ 0 divides t, and `div_sat'` uses the gcd of the coefficients (integer GCD tightening inside omega's proof-producing procedure); Coeffs.lean notes that omega uses a dense coefficient list and that a sparse `AssocList Nat Int` representation is an alternative.
  - René Thiemann (with contributions from Manuel Eberl), 'A Preprocessor for Linear Diophantine Equalities and Inequalities', Archive of Formal Proofs, June 13, 2024, https://isa-afp.org/entries/Linear_Diophantine_Preprocessor.html (abstract: Pugh's technique of tightening linear inequalities, detection of implicit equalities, and elimination of equations; the result either detects unsatisfiability over Z or returns equisatisfiable inequalities; session theories include Linear_Polynomial, Linear_Polynomial_Impl, Diophantine_Tightening).
- **Design question:** What does a Chvátal–Gomory cut checker guarantee, under which side conditions (non-negative multipliers, positive divisor, integral combined coefficients, integral variables), and what does a cut-plus-Farkas certificate prove?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R5c.

#### R6a — `bv_ule_ult_iff_int_of_inUnsignedRange` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** The underlying facts (ofInt is a ring homomorphism; toNat (ofInt z) = z on [0, 2^w)) are mechanized in Lean core and in CompCert's Integers.v and Isabelle's Word_Lib; restated here for affine expressions and comparisons with final-value hypotheses.
- **Plain claim:** For affine expressions e1, e2 with Int coefficients over w-bit variables x, if the integer values of e1 and e2 at the unsigned reading (x i).toNat both lie in [0, 2^w), then e1 <=u e2 (resp. <u) over BitVec w with wrapping evaluation holds iff e1 <= e2 (resp. <) holds over Int.
- **Lean statement** (`Toy.Farkas.bv_ule_ult_iff_int_of_inUnsignedRange`):

```lean
theorem bv_ule_ult_iff_int_of_inUnsignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
  (h₁ : InUnsignedRange w (e₁.evalInt (uval x))) (h₂ : InUnsignedRange w (e₂.evalInt (uval x))) :
  ((AffExpr.evalBv w e₁ x).ule (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (uval x) ≤ e₂.evalInt (uval x)) ∧
    ((AffExpr.evalBv w e₁ x).ult (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (uval x) < e₂.evalInt (uval x))
```

- **Key definitions** (quoted in full under Core definitions): `AffExpr`, `InUnsignedRange`, `AffExpr.evalInt`, `uval`, `AffExpr.evalBv`.
- **Hypothesis ledger:**
  - `h1 : InUnsignedRange w (e1.evalInt (uval x))` — the left value must not wrap; **tight** (counterexample `ce_bv_ule_lhs_out_of_range`).
  - `h2 : InUnsignedRange w (e2.evalInt (uval x))` — the right value must not wrap; **tight** (counterexample `ce_bv_ule_rhs_out_of_range`).
- **Non-vacuity witness:** w = 8, x0 = 70: x0 + x0 = 140 and 150 are in range and 140 <=u 150. Lean: `nv_bv_ule_ult_transfer`.
- **Prior art:**
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Data/BitVec/Lemmas.lean: BitVec.ofInt_add, BitVec.ofInt_mul (BitVec.ofInt w is additive and multiplicative), BitVec.toNat_ofInt ((ofInt n i).toNat = (i % 2^n).toNat), BitVec.toInt_ofInt ((ofInt n i).toInt = i.bmod (2^n)), BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide, BitVec.slt_eq_decide.
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Tactics.lean: the `omega` docstring ('not yet a full decision procedure (no "dark" or "grey" shadows)'); `bv_omega` ('omega with an additional preprocessor that turns statements about BitVec into statements about Nat', via simp lemmas tagged bitvec_to_nat); `bv_decide` (obtains a proof from an external SAT solver and verifies it inside Lean; LRAT proofs per the `bv_check` docstring).
  - CompCert, AbsInt/CompCert commit 99627f88db37a7c98e03775741e5048b981d2032, lib/Integers.v: unsigned_repr (0 <= z <= max_unsigned -> unsigned (repr z) = z), signed_repr (min_signed <= z <= max_signed -> signed (repr z) = z), add_unsigned, add_signed (wrapping addition as repr of the integer sum), and the comparisons ltu / lt (Coq mechanization of machine-integer-to-integer transfer).
  - Joel Beeren, Matthew Fernandez, Xin Gao, Gerwin Klein, Rafal Kolanski, Japheth Lim, Corey Lewis, Daniel Matichuk, Thomas Sewell, 'Finite Machine Word Library', Archive of Formal Proofs, June 9, 2016, https://isa-afp.org/entries/Word_Lib.html (Isabelle/HOL library of fixed-width machine words, including signed words and an extensive library of properties of generic fixed-width words).
  - Yoni Zohar, Ahmed Irfan, Makai Mann, Aina Niemetz, Andres Nötzli, Mathias Preiner, Andrew Reynolds, Clark Barrett, Cesare Tinelli, 'Bit-Precise Reasoning via Int-Blasting', VMCAI 2022, LNCS 13182, Springer, 2022, pp. 496-518, DOI 10.1007/978-3-030-94583-1_24 (translating bit-vector constraints into integer arithmetic in an SMT solver; metadata via Crossref, full text not read).
  - Axel Simon, Andy King, 'Taming the Wrapping of Integer Arithmetic', SAS 2007, LNCS 4634, Springer, 2007, pp. 121-136 (pages per Crossref), DOI 10.1007/978-3-540-74061-2_8 (polyhedral analysis of programs over wrapping fixed-width integers; metadata via Crossref, full text not read).
  - Jorge A. Navas, Peter Schachte, Harald Søndergaard, Peter J. Stuckey, 'Signedness-Agnostic Program Analysis: Precise Integer Bounds for Low-Level Code', APLAS 2012, LNCS 7705, Springer, 2012, pp. 115-130, DOI 10.1007/978-3-642-35182-2_9 (integer bounds analysis for low-level code where signedness is not known; metadata via Crossref, full text not read).
- **Design question:** When may constraints over machine integers (BitVec w, unsigned or signed) be reasoned about over unbounded integers, and which range facts must a verifier establish first?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R6a.

#### R6b — `bv_sle_slt_iff_int_of_inSignedRange` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Signed counterpart of R6a; the underlying facts (toInt (ofInt z) = z.bmod 2^w) are mechanized in Lean core and CompCert (signed_repr).
- **Plain claim:** For affine expressions e1, e2 over w-bit variables x, if the integer values of e1 and e2 at the signed reading (x i).toInt both lie in the w-bit two's-complement range (-2^w <= 2z < 2^w), then e1 <=s e2 (resp. <s) over BitVec w with wrapping evaluation holds iff e1 <= e2 (resp. <) over Int.
- **Lean statement** (`Toy.Farkas.bv_sle_slt_iff_int_of_inSignedRange`):

```lean
theorem bv_sle_slt_iff_int_of_inSignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
  (h₁ : InSignedRange w (e₁.evalInt (sval x))) (h₂ : InSignedRange w (e₂.evalInt (sval x))) :
  ((AffExpr.evalBv w e₁ x).sle (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (sval x) ≤ e₂.evalInt (sval x)) ∧
    ((AffExpr.evalBv w e₁ x).slt (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (sval x) < e₂.evalInt (sval x))
```

- **Key definitions** (quoted in full under Core definitions): `AffExpr`, `InSignedRange`, `AffExpr.evalInt`, `sval`, `AffExpr.evalBv`.
- **Hypothesis ledger:**
  - `h1 : InSignedRange w (e1.evalInt (sval x))` — the left value must not wrap; **tight** (counterexample `ce_bv_sle_lhs_out_of_range`).
  - `h2 : InSignedRange w (e2.evalInt (sval x))` — the right value must not wrap; **tight** (counterexample `ce_bv_sle_rhs_out_of_range`).
- **Non-vacuity witness:** w = 8, x0 = -50: x0 + x0 = -100 and 0 are in signed range and -100 <=s 0. Lean: `nv_bv_sle_slt_transfer`.
- **Prior art:**
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Data/BitVec/Lemmas.lean: BitVec.ofInt_add, BitVec.ofInt_mul (BitVec.ofInt w is additive and multiplicative), BitVec.toNat_ofInt ((ofInt n i).toNat = (i % 2^n).toNat), BitVec.toInt_ofInt ((ofInt n i).toInt = i.bmod (2^n)), BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide, BitVec.slt_eq_decide.
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Tactics.lean: the `omega` docstring ('not yet a full decision procedure (no "dark" or "grey" shadows)'); `bv_omega` ('omega with an additional preprocessor that turns statements about BitVec into statements about Nat', via simp lemmas tagged bitvec_to_nat); `bv_decide` (obtains a proof from an external SAT solver and verifies it inside Lean; LRAT proofs per the `bv_check` docstring).
  - CompCert, AbsInt/CompCert commit 99627f88db37a7c98e03775741e5048b981d2032, lib/Integers.v: unsigned_repr (0 <= z <= max_unsigned -> unsigned (repr z) = z), signed_repr (min_signed <= z <= max_signed -> signed (repr z) = z), add_unsigned, add_signed (wrapping addition as repr of the integer sum), and the comparisons ltu / lt (Coq mechanization of machine-integer-to-integer transfer).
  - Joel Beeren, Matthew Fernandez, Xin Gao, Gerwin Klein, Rafal Kolanski, Japheth Lim, Corey Lewis, Daniel Matichuk, Thomas Sewell, 'Finite Machine Word Library', Archive of Formal Proofs, June 9, 2016, https://isa-afp.org/entries/Word_Lib.html (Isabelle/HOL library of fixed-width machine words, including signed words and an extensive library of properties of generic fixed-width words).
  - Yoni Zohar, Ahmed Irfan, Makai Mann, Aina Niemetz, Andres Nötzli, Mathias Preiner, Andrew Reynolds, Clark Barrett, Cesare Tinelli, 'Bit-Precise Reasoning via Int-Blasting', VMCAI 2022, LNCS 13182, Springer, 2022, pp. 496-518, DOI 10.1007/978-3-030-94583-1_24 (translating bit-vector constraints into integer arithmetic in an SMT solver; metadata via Crossref, full text not read).
  - Axel Simon, Andy King, 'Taming the Wrapping of Integer Arithmetic', SAS 2007, LNCS 4634, Springer, 2007, pp. 121-136 (pages per Crossref), DOI 10.1007/978-3-540-74061-2_8 (polyhedral analysis of programs over wrapping fixed-width integers; metadata via Crossref, full text not read).
  - Jorge A. Navas, Peter Schachte, Harald Søndergaard, Peter J. Stuckey, 'Signedness-Agnostic Program Analysis: Precise Integer Bounds for Low-Level Code', APLAS 2012, LNCS 7705, Springer, 2012, pp. 115-130, DOI 10.1007/978-3-642-35182-2_9 (integer bounds analysis for low-level code where signedness is not known; metadata via Crossref, full text not read).
- **Design question:** When may constraints over machine integers (BitVec w, unsigned or signed) be reasoned about over unbounded integers, and which range facts must a verifier establish first?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R6b.

#### R6c — `bv_ule_ult_iff_int_of_noWrapU` (theorem)

- **Tier:** T0. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Corollary of R6a/R6b with a stronger, intermediate-value hypothesis, restated for this representation.
- **Plain claim:** If every intermediate value of the left-to-right evaluation of e1 and of e2 (each coefficient literal, each product c_i * x_i, each partial sum, the constant, and the final value) lies in [0, 2^w) at the unsigned reading, then e1 <=u e2 (resp. <u) over BitVec w holds iff e1 <= e2 (resp. <) over Int; likewise for the signed reading, the two's-complement range, and <=s / <s. These are corollaries of R6a/R6b; the no-wrap hypotheses are stronger than needed (R6i).
- **Lean statement** (`Toy.Farkas.bv_ule_ult_iff_int_of_noWrapU`; corollaries and related forms: `bv_sle_slt_iff_int_of_noWrapS`):

```lean
theorem bv_ule_ult_iff_int_of_noWrapU (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w) (h₁ : NoWrapU w e₁ (uval x))
  (h₂ : NoWrapU w e₂ (uval x)) :
  ((AffExpr.evalBv w e₁ x).ule (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (uval x) ≤ e₂.evalInt (uval x)) ∧
    ((AffExpr.evalBv w e₁ x).ult (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (uval x) < e₂.evalInt (uval x))

theorem bv_sle_slt_iff_int_of_noWrapS (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w) (h₁ : NoWrapS w e₁ (sval x))
  (h₂ : NoWrapS w e₂ (sval x)) :
  ((AffExpr.evalBv w e₁ x).sle (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (sval x) ≤ e₂.evalInt (sval x)) ∧
    ((AffExpr.evalBv w e₁ x).slt (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (sval x) < e₂.evalInt (sval x))
```

- **Key definitions** (quoted in full under Core definitions): `AffExpr`, `NoWrapU`, `uval`, `AffExpr.evalBv`, `AffExpr.evalInt`, `NoWrapS`, `sval`.
- **Hypothesis ledger:**
  - `h1 : NoWrapU w e1 (uval x) (unsigned form only)` — no intermediate wrap in e1 (unsigned); **tight** (counterexample `ce_bv_ule_noWrapU_lhs`).
  - `h2 : NoWrapU w e2 (uval x) (unsigned form only)` — no intermediate wrap in e2 (unsigned); **tight** (counterexample `ce_bv_ule_noWrapU_rhs`).
  - `h1 : NoWrapS w e1 (sval x) (signed form only)` — no intermediate wrap in e1 (signed); **tight** (counterexample `ce_bv_sle_noWrapS_lhs`).
  - `h2 : NoWrapS w e2 (sval x) (signed form only)` — no intermediate wrap in e2 (signed); **tight** (counterexample `ce_bv_sle_noWrapS_rhs`).
- **Non-vacuity witness:** w = 8: x0 + x0 at x0 = 70 and the constant 150 (unsigned), x0 + x0 at x0 = -50 and the constant 0 (signed), have no wrapping intermediates. Lean: `nv_bv_ule_ult_noWrapU`, `nv_bv_sle_slt_noWrapS`.
- **Prior art:**
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Data/BitVec/Lemmas.lean: BitVec.ofInt_add, BitVec.ofInt_mul (BitVec.ofInt w is additive and multiplicative), BitVec.toNat_ofInt ((ofInt n i).toNat = (i % 2^n).toNat), BitVec.toInt_ofInt ((ofInt n i).toInt = i.bmod (2^n)), BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide, BitVec.slt_eq_decide.
  - LLVM Language Reference Manual, https://llvm.org/docs/LangRef.html (accessed 2026-11-20), poison-value examples: `sub nuw i32 0, 1` 'Results in a poison value' (with the nuw flag an unsigned wrap of one operation poisons the result, unlike the wrapping semantics modeled here).
- **Design question:** When may constraints over machine integers (BitVec w, unsigned or signed) be reasoned about over unbounded integers, and which range facts must a verifier establish first?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R6c.

#### R6e — `checkFarkas_refutes_bvU_posSupport_of_lhs_lt_of_rhs_nonneg` (theorem)

- **Tier:** T1. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Folklore behind translating bit-vector constraints to integers before linear reasoning (e.g. Lean's bv_omega, which adds domain bounds and calls omega; int-blasting in SMT), made precise for Farkas certificates with one-sided, support-restricted range facts; no mechanized statement of this form was located among the sources listed.
- **Plain claim:** Let A be a list of bit-vector atoms e1 <= e2 or e1 < e2 between affine expressions, translated to integer constraints in normal form (e1 - e2 <= 0, resp. < 0). If checkFarkas accepts cert for the translations, then at every w-bit point x at which every atom with a positive multiplier has left-hand integer value (unsigned reading) < 2^w and right-hand integer value >= 0, those positively weighted atoms do not all hold in the unsigned bit-vector reading (so neither does A). The two-sided corollary checkFarkas_refutes_bvU_of_inUnsignedRange assumes [0, 2^w) on both sides of every atom.
- **Lean statement** (`Toy.Farkas.checkFarkas_refutes_bvU_posSupport_of_lhs_lt_of_rhs_nonneg`):

```lean
theorem checkFarkas_refutes_bvU_posSupport_of_lhs_lt_of_rhs_nonneg (A : List BvAtom) (cert : List Int)
  (h : checkFarkas (List.map BvAtom.toConstraint A) cert = true) (w : Nat) (x : Nat → BitVec w)
  (hl : ∀ (a : BvAtom), a ∈ posSupport cert A → a.lhs.evalInt (uval x) < 2 ^ w)
  (hr : ∀ (a : BvAtom), a ∈ posSupport cert A → 0 ≤ a.rhs.evalInt (uval x)) :
  ¬∀ (a : BvAtom), a ∈ posSupport cert A → BvAtom.HoldsU w a x
```

- **Key definitions** (quoted in full under Core definitions): `BvAtom`, `checkFarkas`, `Constraint`, `BvAtom.toConstraint`, `posSupport`, `AffExpr.evalInt`, `BvAtom.lhs`, `uval`, `BvAtom.rhs`, `BvAtom.HoldsU`.
- **Hypothesis ledger:**
  - `h : checkFarkas (A.map BvAtom.toConstraint) cert = true` — the certificate is accepted; **tight** (counterexample `ce_checkFarkas_refutes_bv_rejected`).
  - `hl : every positively weighted atom has lhs.evalInt (uval x) < 2^w` — a left side that wraps past 2^w can make a false integer inequality hold in BitVec; **tight** (counterexample `ce_checkFarkas_bvU_lhs_out_of_range`).
  - `hr : every positively weighted atom has 0 <= rhs.evalInt (uval x)` — a negative right side wraps to a large unsigned value; **tight** (counterexample `ce_checkFarkas_bvU_rhs_out_of_range`).
- **Non-vacuity witness:** {x0 <u x1, x1 <=u x0} with certificate (1, 1); both atoms are positively weighted and at x = (5, 9) every one-sided range fact holds. Lean: `nv_checkFarkas_refutes_bvU`, `nv_checkFarkas_refutes_bv_two_sided`.
- **Prior art:**
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Data/BitVec/Lemmas.lean: BitVec.ofInt_add, BitVec.ofInt_mul (BitVec.ofInt w is additive and multiplicative), BitVec.toNat_ofInt ((ofInt n i).toNat = (i % 2^n).toNat), BitVec.toInt_ofInt ((ofInt n i).toInt = i.bmod (2^n)), BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide, BitVec.slt_eq_decide.
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Tactics.lean: the `omega` docstring ('not yet a full decision procedure (no "dark" or "grey" shadows)'); `bv_omega` ('omega with an additional preprocessor that turns statements about BitVec into statements about Nat', via simp lemmas tagged bitvec_to_nat); `bv_decide` (obtains a proof from an external SAT solver and verifies it inside Lean; LRAT proofs per the `bv_check` docstring).
  - Julius Farkas, 'Theorie der einfachen Ungleichungen', Journal für die reine und angewandte Mathematik 124 (1902), pp. 1-27, DOI 10.1515/crll.1902.124.1 (non-strict linear inequalities).
  - Yoni Zohar, Ahmed Irfan, Makai Mann, Aina Niemetz, Andres Nötzli, Mathias Preiner, Andrew Reynolds, Clark Barrett, Cesare Tinelli, 'Bit-Precise Reasoning via Int-Blasting', VMCAI 2022, LNCS 13182, Springer, 2022, pp. 496-518, DOI 10.1007/978-3-030-94583-1_24 (translating bit-vector constraints into integer arithmetic in an SMT solver; metadata via Crossref, full text not read).
  - Axel Simon, Andy King, 'Taming the Wrapping of Integer Arithmetic', SAS 2007, LNCS 4634, Springer, 2007, pp. 121-136 (pages per Crossref), DOI 10.1007/978-3-540-74061-2_8 (polyhedral analysis of programs over wrapping fixed-width integers; metadata via Crossref, full text not read).
  - CompCert, AbsInt/CompCert commit 99627f88db37a7c98e03775741e5048b981d2032, lib/Integers.v: unsigned_repr (0 <= z <= max_unsigned -> unsigned (repr z) = z), signed_repr (min_signed <= z <= max_signed -> signed (repr z) = z), add_unsigned, add_signed (wrapping addition as repr of the integer sum), and the comparisons ltu / lt (Coq mechanization of machine-integer-to-integer transfer).
- **Design question:** When may constraints over machine integers (BitVec w, unsigned or signed) be reasoned about over unbounded integers, and which range facts must a verifier establish first?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R6e.

#### R6f — `checkFarkas_refutes_bvS_posSupport_of_lhs_lt_of_rhs_ge` (theorem)

- **Tier:** T1. **Kind:** theorem. **Depth:** shallow.
- **Tier justification:** Signed counterpart of R6e; folklore made precise, no mechanized statement of this form located among the sources listed.
- **Plain claim:** As R6e for the signed reading: if checkFarkas accepts cert for the integer translations of A, then at every w-bit point x at which every positively weighted atom has 2 * lhs < 2^w and -2^w <= 2 * rhs (integer values at the signed reading), those atoms do not all hold in the signed bit-vector reading. The two-sided corollary checkFarkas_refutes_bvS_of_inSignedRange assumes the signed range on both sides of every atom.
- **Lean statement** (`Toy.Farkas.checkFarkas_refutes_bvS_posSupport_of_lhs_lt_of_rhs_ge`):

```lean
theorem checkFarkas_refutes_bvS_posSupport_of_lhs_lt_of_rhs_ge (A : List BvAtom) (cert : List Int)
  (h : checkFarkas (List.map BvAtom.toConstraint A) cert = true) (w : Nat) (x : Nat → BitVec w)
  (hl : ∀ (a : BvAtom), a ∈ posSupport cert A → 2 * a.lhs.evalInt (sval x) < 2 ^ w)
  (hr : ∀ (a : BvAtom), a ∈ posSupport cert A → -2 ^ w ≤ 2 * a.rhs.evalInt (sval x)) :
  ¬∀ (a : BvAtom), a ∈ posSupport cert A → BvAtom.HoldsS w a x
```

- **Key definitions** (quoted in full under Core definitions): `BvAtom`, `checkFarkas`, `Constraint`, `BvAtom.toConstraint`, `posSupport`, `AffExpr.evalInt`, `BvAtom.lhs`, `sval`, `BvAtom.rhs`, `BvAtom.HoldsS`.
- **Hypothesis ledger:**
  - `h : checkFarkas (A.map BvAtom.toConstraint) cert = true` — the certificate is accepted; **tight** (counterexample `ce_checkFarkas_refutes_bv_rejected`).
  - `hl : every positively weighted atom has 2 * lhs.evalInt (sval x) < 2^w` — a left side above the signed range wraps to a negative value; **tight** (counterexample `ce_checkFarkas_bvS_lhs_out_of_range`).
  - `hr : every positively weighted atom has -2^w <= 2 * rhs.evalInt (sval x)` — a right side below the signed range wraps to a positive value; **tight** (counterexample `ce_checkFarkas_bvS_rhs_out_of_range`).
- **Non-vacuity witness:** {x0 <s x1, x1 <=s x0} with certificate (1, 1); at x = (-3, 9) every one-sided signed range fact holds. Lean: `nv_checkFarkas_refutes_bvS`, `nv_checkFarkas_refutes_bv_two_sided`.
- **Prior art:**
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Data/BitVec/Lemmas.lean: BitVec.ofInt_add, BitVec.ofInt_mul (BitVec.ofInt w is additive and multiplicative), BitVec.toNat_ofInt ((ofInt n i).toNat = (i % 2^n).toNat), BitVec.toInt_ofInt ((ofInt n i).toInt = i.bmod (2^n)), BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide, BitVec.slt_eq_decide.
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Tactics.lean: the `omega` docstring ('not yet a full decision procedure (no "dark" or "grey" shadows)'); `bv_omega` ('omega with an additional preprocessor that turns statements about BitVec into statements about Nat', via simp lemmas tagged bitvec_to_nat); `bv_decide` (obtains a proof from an external SAT solver and verifies it inside Lean; LRAT proofs per the `bv_check` docstring).
  - Julius Farkas, 'Theorie der einfachen Ungleichungen', Journal für die reine und angewandte Mathematik 124 (1902), pp. 1-27, DOI 10.1515/crll.1902.124.1 (non-strict linear inequalities).
  - Yoni Zohar, Ahmed Irfan, Makai Mann, Aina Niemetz, Andres Nötzli, Mathias Preiner, Andrew Reynolds, Clark Barrett, Cesare Tinelli, 'Bit-Precise Reasoning via Int-Blasting', VMCAI 2022, LNCS 13182, Springer, 2022, pp. 496-518, DOI 10.1007/978-3-030-94583-1_24 (translating bit-vector constraints into integer arithmetic in an SMT solver; metadata via Crossref, full text not read).
  - Axel Simon, Andy King, 'Taming the Wrapping of Integer Arithmetic', SAS 2007, LNCS 4634, Springer, 2007, pp. 121-136 (pages per Crossref), DOI 10.1007/978-3-540-74061-2_8 (polyhedral analysis of programs over wrapping fixed-width integers; metadata via Crossref, full text not read).
  - CompCert, AbsInt/CompCert commit 99627f88db37a7c98e03775741e5048b981d2032, lib/Integers.v: unsigned_repr (0 <= z <= max_unsigned -> unsigned (repr z) = z), signed_repr (min_signed <= z <= max_signed -> signed (repr z) = z), add_unsigned, add_signed (wrapping addition as repr of the integer sum), and the comparisons ltu / lt (Coq mechanization of machine-integer-to-integer transfer).
- **Design question:** When may constraints over machine integers (BitVec w, unsigned or signed) be reasoned about over unbounded integers, and which range facts must a verifier establish first?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R6f.

#### R6g — `ce_bv_reading_mismatch` (counterexample)

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Tier justification:** Well-known signedness pitfall, as a concrete instance.
- **Plain claim:** At w = 8 and x0 = 255#8: under the signed reading both sides of x0 <= 0 are in signed range and -1 <= 0 holds, but the unsigned comparison 255 <=u 0 fails; conversely, under the unsigned reading both sides are in unsigned range and 255 <= 0 fails, but the signed comparison -1 <=s 0 holds. The integer reading must match the comparison's signedness.
- **Lean statement** (`Toy.Farkas.ce_bv_reading_mismatch`):

```lean
theorem ce_bv_reading_mismatch :
  (InSignedRange 8 (eX0.evalInt (sval (bvPt2 255#8 0#8))) ∧
      InSignedRange 8 ((eConst 0).evalInt (sval (bvPt2 255#8 0#8))) ∧
        eX0.evalInt (sval (bvPt2 255#8 0#8)) ≤ (eConst 0).evalInt (sval (bvPt2 255#8 0#8)) ∧
          (AffExpr.evalBv 8 eX0 (bvPt2 255#8 0#8)).ule (AffExpr.evalBv 8 (eConst 0) (bvPt2 255#8 0#8)) = false) ∧
    InUnsignedRange 8 (eX0.evalInt (uval (bvPt2 255#8 0#8))) ∧
      InUnsignedRange 8 ((eConst 0).evalInt (uval (bvPt2 255#8 0#8))) ∧
        ¬eX0.evalInt (uval (bvPt2 255#8 0#8)) ≤ (eConst 0).evalInt (uval (bvPt2 255#8 0#8)) ∧
          (AffExpr.evalBv 8 eX0 (bvPt2 255#8 0#8)).sle (AffExpr.evalBv 8 (eConst 0) (bvPt2 255#8 0#8)) = true
```

- **Key definitions** (quoted in full under Core definitions): `InSignedRange`, `AffExpr.evalInt`, `eX0`, `sval`, `bvPt2`, `eConst`, `AffExpr.evalBv`, `InUnsignedRange`, `uval`.
- **Hypothesis ledger:** no hypotheses (the statement is a closed, concrete proposition).
- **Non-vacuity witness:** not applicable; the card is a concrete counterexample whose statement asserts every fact it relies on.
- **Prior art:**
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Data/BitVec/Lemmas.lean: BitVec.ofInt_add, BitVec.ofInt_mul (BitVec.ofInt w is additive and multiplicative), BitVec.toNat_ofInt ((ofInt n i).toNat = (i % 2^n).toNat), BitVec.toInt_ofInt ((ofInt n i).toInt = i.bmod (2^n)), BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide, BitVec.slt_eq_decide.
  - Jorge A. Navas, Peter Schachte, Harald Søndergaard, Peter J. Stuckey, 'Signedness-Agnostic Program Analysis: Precise Integer Bounds for Low-Level Code', APLAS 2012, LNCS 7705, Springer, 2012, pp. 115-130, DOI 10.1007/978-3-642-35182-2_9 (integer bounds analysis for low-level code where signedness is not known; metadata via Crossref, full text not read).
- **Design question:** When may constraints over machine integers (BitVec w, unsigned or signed) be reasoned about over unbounded integers, and which range facts must a verifier establish first?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R6g.

#### R6h — `ce_bv_rearrangement_unsound` (counterexample)

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Tier justification:** Well-known consequence of wrapping, as concrete instances.
- **Plain claim:** Moving terms across a bit-vector comparison is unsound even when the original sides are in range: at w = 8 and (x0, x1) = (0, 1), x0 <=u x1 holds but x0 - x1 <=u 0 fails (x0 - x1 wraps to 255), although the integer -1 <= 0 holds; at (x0, x1) = (-100, 100) in the signed reading, x0 <=s x1 holds but x0 - x1 <=s 0 fails (x0 - x1 = -200 wraps to 56).
- **Lean statement** (`Toy.Farkas.ce_bv_rearrangement_unsound`):

```lean
theorem ce_bv_rearrangement_unsound :
  (InUnsignedRange 8 (eX0.evalInt (uval (bvPt2 0#8 1#8))) ∧
      InUnsignedRange 8 (eX1.evalInt (uval (bvPt2 0#8 1#8))) ∧
        (AffExpr.evalBv 8 eX0 (bvPt2 0#8 1#8)).ule (AffExpr.evalBv 8 eX1 (bvPt2 0#8 1#8)) = true ∧
          (AffExpr.evalBv 8 { terms := [(0, 1), (1, -1)], const := 0 : AffExpr } (bvPt2 0#8 1#8)).ule
                (AffExpr.evalBv 8 (eConst 0) (bvPt2 0#8 1#8)) =
              false ∧
            { terms := [(0, 1), (1, -1)], const := 0 : AffExpr }.evalInt (uval (bvPt2 0#8 1#8)) ≤
              (eConst 0).evalInt (uval (bvPt2 0#8 1#8))) ∧
    sval (bvPt2 156#8 100#8) 0 = -100 ∧
      InSignedRange 8 (eX0.evalInt (sval (bvPt2 156#8 100#8))) ∧
        InSignedRange 8 (eX1.evalInt (sval (bvPt2 156#8 100#8))) ∧
          (AffExpr.evalBv 8 eX0 (bvPt2 156#8 100#8)).sle (AffExpr.evalBv 8 eX1 (bvPt2 156#8 100#8)) = true ∧
            (AffExpr.evalBv 8 { terms := [(0, 1), (1, -1)], const := 0 : AffExpr } (bvPt2 156#8 100#8)).sle
                  (AffExpr.evalBv 8 (eConst 0) (bvPt2 156#8 100#8)) =
                false ∧
              { terms := [(0, 1), (1, -1)], const := 0 : AffExpr }.evalInt (sval (bvPt2 156#8 100#8)) ≤
                (eConst 0).evalInt (sval (bvPt2 156#8 100#8))
```

- **Key definitions** (quoted in full under Core definitions): `InUnsignedRange`, `AffExpr.evalInt`, `eX0`, `uval`, `bvPt2`, `eX1`, `AffExpr.evalBv`, `eConst`, `sval`, `InSignedRange`.
- **Hypothesis ledger:** no hypotheses (the statement is a closed, concrete proposition).
- **Non-vacuity witness:** not applicable; the card is a concrete counterexample whose statement asserts every fact it relies on.
- **Prior art:**
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Data/BitVec/Lemmas.lean: BitVec.ofInt_add, BitVec.ofInt_mul (BitVec.ofInt w is additive and multiplicative), BitVec.toNat_ofInt ((ofInt n i).toNat = (i % 2^n).toNat), BitVec.toInt_ofInt ((ofInt n i).toInt = i.bmod (2^n)), BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide, BitVec.slt_eq_decide.
  - Axel Simon, Andy King, 'Taming the Wrapping of Integer Arithmetic', SAS 2007, LNCS 4634, Springer, 2007, pp. 121-136 (pages per Crossref), DOI 10.1007/978-3-540-74061-2_8 (polyhedral analysis of programs over wrapping fixed-width integers; metadata via Crossref, full text not read).
- **Design question:** When may constraints over machine integers (BitVec w, unsigned or signed) be reasoned about over unbounded integers, and which range facts must a verifier establish first?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R6h.

#### R6i — `ce_noWrap_not_needed_for_wrapping_eval` (counterexample)

- **Tier:** T0. **Kind:** counterexample. **Depth:** definitional.
- **Tier justification:** Immediate from ofInt being a ring homomorphism (mechanized in Lean core); concrete instances.
- **Plain claim:** Intermediate no-wrap is not necessary for wrapping evaluation: for e = x0 + x0 - x0 (written x0 + x0 + (-1) * x0) at w = 8, in the signed reading at x0 = 100 the left-to-right partial sum 200 leaves the signed range while every other intermediate value (literals, products, other partial sums, constant, final value 100) is in range, so NoWrapS fails, yet the wrapping value of e equals its integer value 100; in the unsigned reading at x0 = 200 the partial sum 400 (and the literal -1 and the product -200) leave the unsigned range, so NoWrapU fails, yet the wrapping value equals the integer value 200. Hence comparisons of e with any in-range right-hand side transfer (R6a/R6b).
- **Lean statement** (`Toy.Farkas.ce_noWrap_not_needed_for_wrapping_eval`):

```lean
theorem ce_noWrap_not_needed_for_wrapping_eval :
  (200 ∈ eAddAddSub.intermediates (sval (bvPt2 100#8 0#8)) ∧
      (∀ (z : Int), z ∈ eAddAddSub.intermediates (sval (bvPt2 100#8 0#8)) → z ≠ 200 → InSignedRange 8 z) ∧
        ¬NoWrapS 8 eAddAddSub (sval (bvPt2 100#8 0#8)) ∧
          InSignedRange 8 (eAddAddSub.evalInt (sval (bvPt2 100#8 0#8))) ∧
            (AffExpr.evalBv 8 eAddAddSub (bvPt2 100#8 0#8)).toInt = eAddAddSub.evalInt (sval (bvPt2 100#8 0#8))) ∧
    400 ∈ eAddAddSub.intermediates (uval (bvPt2 200#8 0#8)) ∧
      ¬NoWrapU 8 eAddAddSub (uval (bvPt2 200#8 0#8)) ∧
        InUnsignedRange 8 (eAddAddSub.evalInt (uval (bvPt2 200#8 0#8))) ∧
          ↑(AffExpr.evalBv 8 eAddAddSub (bvPt2 200#8 0#8)).toNat = eAddAddSub.evalInt (uval (bvPt2 200#8 0#8))
```

- **Key definitions** (quoted in full under Core definitions): `AffExpr.intermediates`, `eAddAddSub`, `sval`, `bvPt2`, `InSignedRange`, `NoWrapS`, `AffExpr.evalInt`, `AffExpr.evalBv`, `uval`, `NoWrapU`, `InUnsignedRange`.
- **Hypothesis ledger:** no hypotheses (the statement is a closed, concrete proposition).
- **Non-vacuity witness:** not applicable; the card is a concrete counterexample whose statement asserts every fact it relies on.
- **Prior art:**
  - Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Data/BitVec/Lemmas.lean: BitVec.ofInt_add, BitVec.ofInt_mul (BitVec.ofInt w is additive and multiplicative), BitVec.toNat_ofInt ((ofInt n i).toNat = (i % 2^n).toNat), BitVec.toInt_ofInt ((ofInt n i).toInt = i.bmod (2^n)), BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide, BitVec.slt_eq_decide.
  - LLVM Language Reference Manual, https://llvm.org/docs/LangRef.html (accessed 2026-11-20), poison-value examples: `sub nuw i32 0, 1` 'Results in a poison value' (with the nuw flag an unsigned wrap of one operation poisons the result, unlike the wrapping semantics modeled here).
  - Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, John Regehr, 'Alive2: bounded translation validation for LLVM', PLDI 2021, ACM, pp. 65-79, DOI 10.1145/3453483.3454030 (translation validation for LLVM IR, including its poison semantics; metadata via Crossref, full text not read).
- **Design question:** When may constraints over machine integers (BitVec w, unsigned or signed) be reasoned about over unbounded integers, and which range facts must a verifier establish first?
- **Basis:** execution (Lean kernel check) of the theorems above and of every Lean name in this card.
- **Non-claims:** listed under Boundaries, Non-claims, R6i.

### Statements of the other card-referenced theorems

Ledger counterexamples, non-vacuity witnesses and positive controls referenced by the cards (all kernel-checked; statement and closure hashes under Evidence).

```lean
theorem ce_bv_sle_lhs_out_of_range :
  ¬InSignedRange 8 (eDouble.evalInt (sval (bvPt2 100#8 0#8))) ∧
    InSignedRange 8 ((eConst 0).evalInt (sval (bvPt2 100#8 0#8))) ∧
      (AffExpr.evalBv 8 eDouble (bvPt2 100#8 0#8)).sle (AffExpr.evalBv 8 (eConst 0) (bvPt2 100#8 0#8)) = true ∧
        ¬eDouble.evalInt (sval (bvPt2 100#8 0#8)) ≤ (eConst 0).evalInt (sval (bvPt2 100#8 0#8))

theorem ce_bv_sle_noWrapS_lhs :
  ¬NoWrapS 8 eDouble (sval (bvPt2 100#8 0#8)) ∧
    NoWrapS 8 (eConst 0) (sval (bvPt2 100#8 0#8)) ∧
      ¬(((AffExpr.evalBv 8 eDouble (bvPt2 100#8 0#8)).sle (AffExpr.evalBv 8 (eConst 0) (bvPt2 100#8 0#8)) = true ↔
            eDouble.evalInt (sval (bvPt2 100#8 0#8)) ≤ (eConst 0).evalInt (sval (bvPt2 100#8 0#8))) ∧
          ((AffExpr.evalBv 8 eDouble (bvPt2 100#8 0#8)).slt (AffExpr.evalBv 8 (eConst 0) (bvPt2 100#8 0#8)) = true ↔
            eDouble.evalInt (sval (bvPt2 100#8 0#8)) < (eConst 0).evalInt (sval (bvPt2 100#8 0#8))))

theorem ce_bv_sle_noWrapS_rhs :
  NoWrapS 8 eX0 (sval (bvPt2 100#8 0#8)) ∧
    ¬NoWrapS 8 (eConst 200) (sval (bvPt2 100#8 0#8)) ∧
      ¬(((AffExpr.evalBv 8 eX0 (bvPt2 100#8 0#8)).sle (AffExpr.evalBv 8 (eConst 200) (bvPt2 100#8 0#8)) = true ↔
            eX0.evalInt (sval (bvPt2 100#8 0#8)) ≤ (eConst 200).evalInt (sval (bvPt2 100#8 0#8))) ∧
          ((AffExpr.evalBv 8 eX0 (bvPt2 100#8 0#8)).slt (AffExpr.evalBv 8 (eConst 200) (bvPt2 100#8 0#8)) = true ↔
            eX0.evalInt (sval (bvPt2 100#8 0#8)) < (eConst 200).evalInt (sval (bvPt2 100#8 0#8))))

theorem ce_bv_sle_rhs_out_of_range :
  InSignedRange 8 (eX0.evalInt (sval (bvPt2 100#8 0#8))) ∧
    ¬InSignedRange 8 ((eConst 200).evalInt (sval (bvPt2 100#8 0#8))) ∧
      (AffExpr.evalBv 8 eX0 (bvPt2 100#8 0#8)).sle (AffExpr.evalBv 8 (eConst 200) (bvPt2 100#8 0#8)) = false ∧
        eX0.evalInt (sval (bvPt2 100#8 0#8)) ≤ (eConst 200).evalInt (sval (bvPt2 100#8 0#8))

theorem ce_bv_ule_lhs_out_of_range :
  ¬InUnsignedRange 8 (eDouble.evalInt (uval (bvPt2 200#8 0#8))) ∧
    InUnsignedRange 8 ((eConst 150).evalInt (uval (bvPt2 200#8 0#8))) ∧
      (AffExpr.evalBv 8 eDouble (bvPt2 200#8 0#8)).ule (AffExpr.evalBv 8 (eConst 150) (bvPt2 200#8 0#8)) = true ∧
        ¬eDouble.evalInt (uval (bvPt2 200#8 0#8)) ≤ (eConst 150).evalInt (uval (bvPt2 200#8 0#8))

theorem ce_bv_ule_noWrapU_lhs :
  ¬NoWrapU 8 eDouble (uval (bvPt2 200#8 0#8)) ∧
    NoWrapU 8 (eConst 150) (uval (bvPt2 200#8 0#8)) ∧
      ¬(((AffExpr.evalBv 8 eDouble (bvPt2 200#8 0#8)).ule (AffExpr.evalBv 8 (eConst 150) (bvPt2 200#8 0#8)) = true ↔
            eDouble.evalInt (uval (bvPt2 200#8 0#8)) ≤ (eConst 150).evalInt (uval (bvPt2 200#8 0#8))) ∧
          ((AffExpr.evalBv 8 eDouble (bvPt2 200#8 0#8)).ult (AffExpr.evalBv 8 (eConst 150) (bvPt2 200#8 0#8)) = true ↔
            eDouble.evalInt (uval (bvPt2 200#8 0#8)) < (eConst 150).evalInt (uval (bvPt2 200#8 0#8))))

theorem ce_bv_ule_noWrapU_rhs :
  NoWrapU 8 eX0 (uval (bvPt2 200#8 0#8)) ∧
    ¬NoWrapU 8 (eConst 300) (uval (bvPt2 200#8 0#8)) ∧
      ¬(((AffExpr.evalBv 8 eX0 (bvPt2 200#8 0#8)).ule (AffExpr.evalBv 8 (eConst 300) (bvPt2 200#8 0#8)) = true ↔
            eX0.evalInt (uval (bvPt2 200#8 0#8)) ≤ (eConst 300).evalInt (uval (bvPt2 200#8 0#8))) ∧
          ((AffExpr.evalBv 8 eX0 (bvPt2 200#8 0#8)).ult (AffExpr.evalBv 8 (eConst 300) (bvPt2 200#8 0#8)) = true ↔
            eX0.evalInt (uval (bvPt2 200#8 0#8)) < (eConst 300).evalInt (uval (bvPt2 200#8 0#8))))

theorem ce_bv_ule_rhs_out_of_range :
  InUnsignedRange 8 (eX0.evalInt (uval (bvPt2 200#8 0#8))) ∧
    ¬InUnsignedRange 8 ((eConst 300).evalInt (uval (bvPt2 200#8 0#8))) ∧
      (AffExpr.evalBv 8 eX0 (bvPt2 200#8 0#8)).ule (AffExpr.evalBv 8 (eConst 300) (bvPt2 200#8 0#8)) = false ∧
        eX0.evalInt (uval (bvPt2 200#8 0#8)) ≤ (eConst 300).evalInt (uval (bvPt2 200#8 0#8))

theorem ce_cgCut_div_one_unsound_over_rat :
  cgValid sysOpenUnit { mult := [(1 : Int), (1 : Int)], div := (1 : Int) } = true ∧
    cgCut sysOpenUnit { mult := [(1 : Int), (1 : Int)], div := (1 : Int) } =
        { lhs := [((0 : Nat), (0 : Int))], rel := Rel.le, rhs := (-1 : Int) } ∧
      (0 : Int) < (2 : Int) ∧
        SatScaled sysOpenUnit (2 : Int) (pt1 (1 : Int)) ∧
          ¬(cgCut sysOpenUnit { mult := [(1 : Int), (1 : Int)], div := (1 : Int) }).HoldsScaled (2 : Int)
              (pt1 (1 : Int))

theorem ce_cgCut_negative_divisor :
  multipliersNonneg [1] = true ∧
    ¬0 < -1 ∧
      cgDivisible [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }] { mult := [1], div := -1 } = true ∧
        SatInt [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }] (pt1 (-1)) ∧
          ¬(cgCut [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }] { mult := [1], div := -1 }).HoldsInt (pt1 (-1))

theorem ce_cgCut_negative_multiplier :
  multipliersNonneg [(-1 : Int)] = false ∧
    (0 : Int) < (1 : Int) ∧
      cgDivisible [{ lhs := [((0 : Nat), (1 : Int))], rel := Rel.le, rhs := (0 : Int) }]
            { mult := [(-1 : Int)], div := (1 : Int) } =
          true ∧
        SatInt [{ lhs := [((0 : Nat), (1 : Int))], rel := Rel.le, rhs := (0 : Int) }] (pt1 (-1 : Int)) ∧
          ¬(cgCut [{ lhs := [((0 : Nat), (1 : Int))], rel := Rel.le, rhs := (0 : Int) }]
                  { mult := [(-1 : Int)], div := (1 : Int) }).HoldsInt
              (pt1 (-1 : Int))

theorem ce_cgCut_not_divisible :
  multipliersNonneg [(1 : Int)] = true ∧
    (0 : Int) < (2 : Int) ∧
      cgDivisible [{ lhs := [((0 : Nat), (1 : Int)), ((1 : Nat), (-1 : Int))], rel := Rel.le, rhs := (0 : Int) }]
            { mult := [(1 : Int)], div := (2 : Int) } =
          false ∧
        SatInt [{ lhs := [((0 : Nat), (1 : Int)), ((1 : Nat), (-1 : Int))], rel := Rel.le, rhs := (0 : Int) }]
            (pt2 (-1 : Int) (-1 : Int)) ∧
          ¬(cgCut [{ lhs := [((0 : Nat), (1 : Int)), ((1 : Nat), (-1 : Int))], rel := Rel.le, rhs := (0 : Int) }]
                  { mult := [(1 : Int)], div := (2 : Int) }).HoldsInt
              (pt2 (-1 : Int) (-1 : Int))

theorem ce_cgCut_point_not_solution :
  multipliersNonneg [(1 : Int)] = true ∧
    (0 : Int) < (2 : Int) ∧
      cgDivisible sysTwoXLeThree { mult := [(1 : Int)], div := (2 : Int) } = true ∧
        ¬SatInt sysTwoXLeThree (pt1 (5 : Int)) ∧
          ¬(cgCut sysTwoXLeThree { mult := [(1 : Int)], div := (2 : Int) }).HoldsInt (pt1 (5 : Int))

theorem ce_cgCut_unsound_over_rat :
  multipliersNonneg [(1 : Int), (0 : Int)] = true ∧
    (0 : Int) < (2 : Int) ∧
      cgDivisible sysHalf { mult := [(1 : Int), (0 : Int)], div := (2 : Int) } = true ∧
        (0 : Int) < (2 : Int) ∧
          SatScaled sysHalf (2 : Int) (pt1 (1 : Int)) ∧
            ¬(cgCut sysHalf { mult := [(1 : Int), (0 : Int)], div := (2 : Int) }).HoldsScaled (2 : Int) (pt1 (1 : Int))

theorem ce_cgDerive_rejected :
  cgDerive [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }] { mult := [-1], div := 1 } = none ∧
    SatInt [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }] (pt1 (-1)) ∧
      ¬(cgCut [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }] { mult := [-1], div := 1 }).HoldsInt (pt1 (-1))

theorem ce_checkCutCert_rejects_satisfiable :
  checkCutCert sysTwoXLeThree { cuts := [{ mult := [1], div := 2 }], farkas := [1] } = false ∧
    SatInt sysTwoXLeThree (pt1 1)

theorem ce_checkCutCert_unsound_over_rat :
  checkCutCert sysHalf halfCutCert = true ∧ (0 : Int) < (2 : Int) ∧ SatScaled sysHalf (2 : Int) (pt1 (1 : Int))

theorem ce_checkFarkasTightened_rejects_satisfiable :
  checkFarkasTightened sysEq [1, 1] = false ∧ SatInt sysEq (pt1 1)

theorem ce_checkFarkas_bvS_lhs_out_of_range :
  checkFarkas (List.map BvAtom.toConstraint atomsLhsWrapS) [1, 3] = true ∧
    posSupport [1, 3] atomsLhsWrapS = atomsLhsWrapS ∧
      (¬∀ (a : BvAtom), a ∈ posSupport [1, 3] atomsLhsWrapS → 2 * a.lhs.evalInt (sval (bvPt2 100#8 0#8)) < 2 ^ 8) ∧
        (∀ (a : BvAtom), a ∈ posSupport [1, 3] atomsLhsWrapS → -2 ^ 8 ≤ 2 * a.rhs.evalInt (sval (bvPt2 100#8 0#8))) ∧
          ∀ (a : BvAtom), a ∈ posSupport [1, 3] atomsLhsWrapS → BvAtom.HoldsS 8 a (bvPt2 100#8 0#8)

theorem ce_checkFarkas_bvS_rhs_out_of_range :
  checkFarkas (List.map BvAtom.toConstraint atomsRhsWrapS) [1, 1] = true ∧
    posSupport [1, 1] atomsRhsWrapS = atomsRhsWrapS ∧
      (∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsRhsWrapS → 2 * a.lhs.evalInt (sval (bvPt2 50#8 0#8)) < 2 ^ 8) ∧
        (¬∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsRhsWrapS → -2 ^ 8 ≤ 2 * a.rhs.evalInt (sval (bvPt2 50#8 0#8))) ∧
          ∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsRhsWrapS → BvAtom.HoldsS 8 a (bvPt2 50#8 0#8)

theorem ce_checkFarkas_bvU_lhs_out_of_range :
  checkFarkas (List.map BvAtom.toConstraint atomsLhsWrapU) [1, 3] = true ∧
    posSupport [1, 3] atomsLhsWrapU = atomsLhsWrapU ∧
      (¬∀ (a : BvAtom), a ∈ posSupport [1, 3] atomsLhsWrapU → a.lhs.evalInt (uval (bvPt2 200#8 0#8)) < 2 ^ 8) ∧
        (∀ (a : BvAtom), a ∈ posSupport [1, 3] atomsLhsWrapU → 0 ≤ a.rhs.evalInt (uval (bvPt2 200#8 0#8))) ∧
          ∀ (a : BvAtom), a ∈ posSupport [1, 3] atomsLhsWrapU → BvAtom.HoldsU 8 a (bvPt2 200#8 0#8)

theorem ce_checkFarkas_bvU_rhs_out_of_range :
  checkFarkas (List.map BvAtom.toConstraint atomsRhsWrapU) [1, 1] = true ∧
    posSupport [1, 1] atomsRhsWrapU = atomsRhsWrapU ∧
      (∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsRhsWrapU → a.lhs.evalInt (uval (bvPt2 0#8 0#8)) < 2 ^ 8) ∧
        (¬∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsRhsWrapU → 0 ≤ a.rhs.evalInt (uval (bvPt2 0#8 0#8))) ∧
          ∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsRhsWrapU → BvAtom.HoldsU 8 a (bvPt2 0#8 0#8)

theorem ce_checkFarkas_refutes_bv_rejected :
  checkFarkas (List.map BvAtom.toConstraint atomsLe) [1] = false ∧
    posSupport [1] atomsLe = atomsLe ∧
      (∀ (a : BvAtom), a ∈ atomsLe → InUnsignedRange 8 (a.lhs.evalInt (uval (bvPt2 0#8 0#8)))) ∧
        (∀ (a : BvAtom), a ∈ atomsLe → InUnsignedRange 8 (a.rhs.evalInt (uval (bvPt2 0#8 0#8)))) ∧
          (∀ (a : BvAtom), a ∈ atomsLe → InSignedRange 8 (a.lhs.evalInt (sval (bvPt2 0#8 0#8)))) ∧
            (∀ (a : BvAtom), a ∈ atomsLe → InSignedRange 8 (a.rhs.evalInt (sval (bvPt2 0#8 0#8)))) ∧
              (∀ (a : BvAtom), a ∈ atomsLe → BvAtom.HoldsU 8 a (bvPt2 0#8 0#8)) ∧
                ∀ (a : BvAtom), a ∈ atomsLe → BvAtom.HoldsS 8 a (bvPt2 0#8 0#8)

theorem ce_checkFarkas_rejected_satisfiable :
  checkFarkas sysEq [(1 : Int), (1 : Int)] = false ∧
    (0 : Int) < (1 : Int) ∧
      SatScaled sysEq (1 : Int) (pt1 (1 : Int)) ∧
        SatInt sysEq (pt1 (1 : Int)) ∧ posSupport [(1 : Int), (1 : Int)] sysEq = sysEq

theorem ce_eval_eq_denseDotOn_duplicate_index_list :
  ¬[0, 0].Nodup ∧
    (∀ (p : Nat × Int), p ∈ [(0, 1)] → p.fst ∈ [0, 0]) ∧
      (SparseVec.eval [(0, 1)] fun x => 1) ≠ denseDotOn [0, 0] (SparseVec.coeff [(0, 1)]) fun x => 1

theorem ce_eval_eq_denseDotOn_missing_index :
  [0].Nodup ∧
    (¬∀ (p : Nat × Int), p ∈ [(1, 1)] → p.fst ∈ [0]) ∧
      (SparseVec.eval [(1, 1)] fun x => 1) ≠ denseDotOn [0] (SparseVec.coeff [(1, 1)]) fun x => 1

theorem ce_eval_eq_denseDot_index_out_of_range :
  (¬∀ (p : Nat × Int), p ∈ [(1, 1)] → p.fst < 1) ∧
    (SparseVec.eval [(1, 1)] fun x => 1) ≠ denseDot 1 (SparseVec.coeff [(1, 1)]) fun x => 1

theorem ce_farkas_complete_feasible_system :
  (0 : Int) < (1 : Int) ∧ SatScaled sysEq (1 : Int) (pt1 (1 : Int)) ∧ ¬∃ cert, checkFarkas sysEq cert = true

theorem ce_farkas_denominator_zero :
  checkFarkas [{ lhs := [], rel := Rel.le, rhs := (-1 : Int) }] [(1 : Int)] = true ∧
    multipliersNonneg [(1 : Int)] = true ∧
      lhsVanishes [{ lhs := [], rel := Rel.le, rhs := (-1 : Int) }] [(1 : Int)] = true ∧
        rhsContradicts [{ lhs := [], rel := Rel.le, rhs := (-1 : Int) }] [(1 : Int)] = true ∧
          ¬(0 : Int) < (0 : Int) ∧
            SatScaled [{ lhs := [], rel := Rel.le, rhs := (-1 : Int) }] (0 : Int) fun x => (0 : Int)

theorem ce_farkas_lhs_not_vanishing :
  multipliersNonneg [(1 : Int)] = true ∧
    lhsVanishes [{ lhs := [((0 : Nat), (1 : Int))], rel := Rel.le, rhs := (-1 : Int) }] [(1 : Int)] = false ∧
      rhsContradicts [{ lhs := [((0 : Nat), (1 : Int))], rel := Rel.le, rhs := (-1 : Int) }] [(1 : Int)] = true ∧
        (0 : Int) < (1 : Int) ∧
          SatScaled [{ lhs := [((0 : Nat), (1 : Int))], rel := Rel.le, rhs := (-1 : Int) }] (1 : Int) (pt1 (-1 : Int))

theorem ce_farkas_rhs_not_contradicting :
  multipliersNonneg [(1 : Int), (1 : Int)] = true ∧
    lhsVanishes sysEq [(1 : Int), (1 : Int)] = true ∧
      rhsContradicts sysEq [(1 : Int), (1 : Int)] = false ∧
        (0 : Int) < (1 : Int) ∧ SatScaled sysEq (1 : Int) (pt1 (1 : Int))

theorem nv_bv_sle_slt_noWrapS :
  NoWrapS 8 eDouble (sval (bvPt2 206#8 0#8)) ∧ NoWrapS 8 (eConst 0) (sval (bvPt2 206#8 0#8))

theorem nv_bv_sle_slt_transfer :
  InSignedRange 8 (eDouble.evalInt (sval (bvPt2 206#8 0#8))) ∧
    InSignedRange 8 ((eConst 0).evalInt (sval (bvPt2 206#8 0#8))) ∧
      sval (bvPt2 206#8 0#8) 0 = -50 ∧
        (AffExpr.evalBv 8 eDouble (bvPt2 206#8 0#8)).sle (AffExpr.evalBv 8 (eConst 0) (bvPt2 206#8 0#8)) = true

theorem nv_bv_ule_ult_noWrapU :
  NoWrapU 8 eDouble (uval (bvPt2 70#8 0#8)) ∧ NoWrapU 8 (eConst 150) (uval (bvPt2 70#8 0#8))

theorem nv_bv_ule_ult_transfer :
  InUnsignedRange 8 (eDouble.evalInt (uval (bvPt2 70#8 0#8))) ∧
    InUnsignedRange 8 ((eConst 150).evalInt (uval (bvPt2 70#8 0#8))) ∧
      (AffExpr.evalBv 8 eDouble (bvPt2 70#8 0#8)).ule (AffExpr.evalBv 8 (eConst 150) (bvPt2 70#8 0#8)) = true

theorem nv_cgCut_sound_int :
  multipliersNonneg [(1 : Int)] = true ∧
    (0 : Int) < (2 : Int) ∧
      cgDivisible sysTwoXLeThree { mult := [(1 : Int)], div := (2 : Int) } = true ∧
        SatInt sysTwoXLeThree (pt1 (1 : Int)) ∧
          cgDerive sysTwoXLeThree { mult := [(1 : Int)], div := (2 : Int) } =
              some { lhs := [((0 : Nat), (1 : Int))], rel := Rel.le, rhs := (1 : Int) } ∧
            (cgCut sysTwoXLeThree { mult := [(1 : Int)], div := (2 : Int) }).HoldsInt (pt1 (1 : Int))

theorem nv_checkCutCert_sound_int : checkCutCert sysHalf halfCutCert = true

theorem nv_checkFarkasTightened : checkFarkasTightened sysOpenUnit [1, 1] = true

theorem nv_checkFarkas_refutes_bvS :
  checkFarkas (List.map BvAtom.toConstraint atomsLtLe) [1, 1] = true ∧
    posSupport [1, 1] atomsLtLe = atomsLtLe ∧
      (∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsLtLe → 2 * a.lhs.evalInt (sval (bvPt2 253#8 9#8)) < 2 ^ 8) ∧
        ∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsLtLe → -2 ^ 8 ≤ 2 * a.rhs.evalInt (sval (bvPt2 253#8 9#8))

theorem nv_checkFarkas_refutes_bvU :
  checkFarkas (List.map BvAtom.toConstraint atomsLtLe) [1, 1] = true ∧
    posSupport [1, 1] atomsLtLe = atomsLtLe ∧
      (∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsLtLe → a.lhs.evalInt (uval (bvPt2 5#8 9#8)) < 2 ^ 8) ∧
        ∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsLtLe → 0 ≤ a.rhs.evalInt (uval (bvPt2 5#8 9#8))

theorem nv_checkFarkas_refutes_bv_two_sided :
  checkFarkas (List.map BvAtom.toConstraint atomsLtLe) [1, 1] = true ∧
    (∀ (a : BvAtom), a ∈ atomsLtLe → InUnsignedRange 8 (a.lhs.evalInt (uval (bvPt2 5#8 9#8)))) ∧
      (∀ (a : BvAtom), a ∈ atomsLtLe → InUnsignedRange 8 (a.rhs.evalInt (uval (bvPt2 5#8 9#8)))) ∧
        (∀ (a : BvAtom), a ∈ atomsLtLe → InSignedRange 8 (a.lhs.evalInt (sval (bvPt2 253#8 9#8)))) ∧
          ∀ (a : BvAtom), a ∈ atomsLtLe → InSignedRange 8 (a.rhs.evalInt (sval (bvPt2 253#8 9#8)))

theorem nv_checkFarkas_sound : checkFarkas sysLeGe [1, 1] = true ∧ checkFarkas sysStrict [1, 1] = true

theorem nv_checkFarkas_sound_posSupport :
  checkFarkas (sysLeGe ++ [{ lhs := [((1 : Nat), (1 : Int))], rel := Rel.le, rhs := (-7 : Int) }])
        [(1 : Int), (1 : Int), (0 : Int)] =
      true ∧
    posSupport [(1 : Int), (1 : Int), (0 : Int)]
          (sysLeGe ++ [{ lhs := [((1 : Nat), (1 : Int))], rel := Rel.le, rhs := (-7 : Int) }]) =
        sysLeGe ∧
      (0 : Int) < (1 : Int)

theorem nv_checkFarkas_sound_scaled :
  checkFarkas sysLeGe [(1 : Int), (1 : Int)] = true ∧
    checkFarkas sysStrict [(1 : Int), (1 : Int)] = true ∧ (0 : Int) < (1 : Int)

theorem nv_combineLhs_coeff : (combineLhs sysLeGe [2, 3]).coeff 0 = 2 * 1 + 3 * -1

theorem nv_combineLhs_eval :
  (combineLhs sysLeGe [2, 3]).eval (pt1 5) = 2 * SparseVec.eval [(0, 1)] (pt1 5) + 3 * SparseVec.eval [(0, -1)] (pt1 5)

theorem nv_eval_eq_denseDot :
  (∀ (p : Nat × Int), p ∈ [(0, 2), (2, -3), (0, 1)] → p.fst < 3) ∧
    (SparseVec.eval [(0, 2), (2, -3), (0, 1)] fun i => ↑i + 4) =
      denseDot 3 (SparseVec.coeff [(0, 2), (2, -3), (0, 1)]) fun i => ↑i + 4

theorem nv_eval_eq_denseDotOn :
  [1, 0].Nodup ∧
    (∀ (p : Nat × Int), p ∈ [(0, 2), (1, -3), (0, 1)] → p.fst ∈ [1, 0]) ∧
      (SparseVec.eval [(0, 2), (1, -3), (0, 1)] fun i => ↑i + 4) =
        denseDotOn [1, 0] (SparseVec.coeff [(0, 2), (1, -3), (0, 1)]) fun i => ↑i + 4

theorem nv_farkas_complete_scaled :
  (∀ (d : Int) (p : Nat → Int), 0 < d → ¬SatScaled sysLeGe d p) ∧
    (∀ (d : Int) (p : Nat → Int), 0 < d → ¬SatScaled sysStrict d p) ∧
      checkFarkas sysLeGe [1, 1] = true ∧ checkFarkas sysStrict [1, 1] = true

theorem nv_farkas_sound_structured :
  multipliersNonneg [(1 : Int), (1 : Int)] = true ∧
    lhsVanishes sysLeGe [(1 : Int), (1 : Int)] = true ∧
      rhsContradicts sysLeGe [(1 : Int), (1 : Int)] = true ∧ (0 : Int) < (1 : Int)

theorem nv_isZero_iff : SparseVec.isZero [(3, 2), (3, -2)] = true ∧ SparseVec.coeff [(3, 2), (3, -2)] 3 = 0

theorem sysHalf_refuted_by_case_split :
  (∀ (v : Int), v ≤ 0 ∨ -v ≤ -1) ∧
    checkFarkas (sysHalf ++ [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }]) [0, 1, 2] = true ∧
      checkFarkas (sysHalf ++ [{ lhs := [(0, -1)], rel := Rel.le, rhs := -1 }]) [1, 0, 2] = true
```

### Other kernel-checked theorems mentioned in this report

Corollaries, helper lemmas, bounded checks and proof internals named in card prose or above. They are kernel-checked with standard axioms only (recorded in `audit/axioms.json`) but carry no recorded statement hash, because no card lists them in a Lean-name field. Statements of the definition examples cited under Core definitions are in the next subsection, "Statements of the definition examples".

```lean
theorem AffExpr.evalBv_eq_ofInt (w : Nat) (e : AffExpr) (x : Nat → BitVec w) (ρ : Nat → Int)
  (hρ : ∀ (i : Nat), BitVec.ofInt w (ρ i) = x i) : AffExpr.evalBv w e x = BitVec.ofInt w (e.evalInt ρ)

theorem BvAtom.holdsInt_of_holdsS_of_lhs_lt_of_rhs_ge (w : Nat) (a : BvAtom) (x : Nat → BitVec w)
  (h₁ : 2 * a.lhs.evalInt (sval x) < 2 ^ w) (h₂ : -2 ^ w ≤ 2 * a.rhs.evalInt (sval x)) (h : BvAtom.HoldsS w a x) :
  a.toConstraint.HoldsInt (sval x)

theorem BvAtom.holdsInt_of_holdsU_of_lhs_lt_of_rhs_nonneg (w : Nat) (a : BvAtom) (x : Nat → BitVec w)
  (h₁ : a.lhs.evalInt (uval x) < 2 ^ w) (h₂ : 0 ≤ a.rhs.evalInt (uval x)) (h : BvAtom.HoldsU w a x) :
  a.toConstraint.HoldsInt (uval x)

theorem BvAtom.holdsS_iff_holdsInt_of_inSignedRange (w : Nat) (a : BvAtom) (x : Nat → BitVec w)
  (h₁ : InSignedRange w (a.lhs.evalInt (sval x))) (h₂ : InSignedRange w (a.rhs.evalInt (sval x))) :
  BvAtom.HoldsS w a x ↔ a.toConstraint.HoldsInt (sval x)

theorem BvAtom.holdsU_iff_holdsInt_of_inUnsignedRange (w : Nat) (a : BvAtom) (x : Nat → BitVec w)
  (h₁ : InUnsignedRange w (a.lhs.evalInt (uval x))) (h₂ : InUnsignedRange w (a.rhs.evalInt (uval x))) :
  BvAtom.HoldsU w a x ↔ a.toConstraint.HoldsInt (uval x)

theorem BvAtom.toConstraint_holdsInt_iff (a : BvAtom) (ρ : Nat → Int) :
  a.toConstraint.HoldsInt ρ ↔ a.rel.Sat (a.lhs.evalInt ρ) (a.rhs.evalInt ρ)

theorem Constraint.holdsInt_tighten_iff (c : Constraint) (x : Nat → Int) : c.tighten.HoldsInt x ↔ c.HoldsInt x

theorem SparseVec.evalBv_eq_ofInt (w : Nat) (v : SparseVec) (x : Nat → BitVec w) (ρ : Nat → Int)
  (hρ : ∀ (i : Nat), BitVec.ofInt w (ρ i) = x i) : SparseVec.evalBv w v x = BitVec.ofInt w (v.eval ρ)

theorem SparseVec.eval_eq_zero_of_isZero (v : SparseVec) (h : v.isZero = true) (x : Nat → Int) : v.eval x = 0

theorem applyCuts_satInt (ks : List CGStep) (S S' : List Constraint) (h : applyCuts S ks = some S') (x : Nat → Int)
  (hx : SatInt S x) : SatInt S' x

theorem bv_sle_iff_int_le_of_inSignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
  (h₁ : InSignedRange w (e₁.evalInt (sval x))) (h₂ : InSignedRange w (e₂.evalInt (sval x))) :
  (AffExpr.evalBv w e₁ x).sle (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (sval x) ≤ e₂.evalInt (sval x)

theorem bv_sle_slt_imp_int_of_lhs_lt_of_rhs_ge (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
  (h₁ : 2 * e₁.evalInt (sval x) < 2 ^ w) (h₂ : -2 ^ w ≤ 2 * e₂.evalInt (sval x)) :
  ((AffExpr.evalBv w e₁ x).sle (AffExpr.evalBv w e₂ x) = true → e₁.evalInt (sval x) ≤ e₂.evalInt (sval x)) ∧
    ((AffExpr.evalBv w e₁ x).slt (AffExpr.evalBv w e₂ x) = true → e₁.evalInt (sval x) < e₂.evalInt (sval x))

theorem bv_slt_iff_int_lt_of_inSignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
  (h₁ : InSignedRange w (e₁.evalInt (sval x))) (h₂ : InSignedRange w (e₂.evalInt (sval x))) :
  (AffExpr.evalBv w e₁ x).slt (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (sval x) < e₂.evalInt (sval x)

theorem bv_ule_iff_int_le_of_inUnsignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
  (h₁ : InUnsignedRange w (e₁.evalInt (uval x))) (h₂ : InUnsignedRange w (e₂.evalInt (uval x))) :
  (AffExpr.evalBv w e₁ x).ule (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (uval x) ≤ e₂.evalInt (uval x)

theorem bv_ule_ult_imp_int_of_lhs_lt_of_rhs_nonneg (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
  (h₁ : e₁.evalInt (uval x) < 2 ^ w) (h₂ : 0 ≤ e₂.evalInt (uval x)) :
  ((AffExpr.evalBv w e₁ x).ule (AffExpr.evalBv w e₂ x) = true → e₁.evalInt (uval x) ≤ e₂.evalInt (uval x)) ∧
    ((AffExpr.evalBv w e₁ x).ult (AffExpr.evalBv w e₂ x) = true → e₁.evalInt (uval x) < e₂.evalInt (uval x))

theorem bv_ult_iff_int_lt_of_inUnsignedRange (w : Nat) (e₁ e₂ : AffExpr) (x : Nat → BitVec w)
  (h₁ : InUnsignedRange w (e₁.evalInt (uval x))) (h₂ : InUnsignedRange w (e₂.evalInt (uval x))) :
  (AffExpr.evalBv w e₁ x).ult (AffExpr.evalBv w e₂ x) = true ↔ e₁.evalInt (uval x) < e₂.evalInt (uval x)

theorem ce_bvS_range_on_difference_insufficient :
  InSignedRange 8 ((eConst 150).evalInt (sval (bvPt2 0#8 0#8)) - (eConst 100).evalInt (sval (bvPt2 0#8 0#8))) ∧
    ¬InSignedRange 8 ((eConst 150).evalInt (sval (bvPt2 0#8 0#8))) ∧
      (AffExpr.evalBv 8 (eConst 150) (bvPt2 0#8 0#8)).sle (AffExpr.evalBv 8 (eConst 100) (bvPt2 0#8 0#8)) = true ∧
        ¬(eConst 150).evalInt (sval (bvPt2 0#8 0#8)) ≤ (eConst 100).evalInt (sval (bvPt2 0#8 0#8))

theorem ce_bv_domain_bounds_not_emitted :
  (∀ (v : BitVec 8), ¬∀ (a : BvAtom), a ∈ atomsLtZero → BvAtom.HoldsU 8 a (bvPt2 v 0#8)) ∧
    SatInt (List.map BvAtom.toConstraint atomsLtZero) (pt1 (-1)) ∧
      ∀ (cert : List Int), checkFarkas (List.map BvAtom.toConstraint atomsLtZero) cert = false

theorem ce_bv_tightening_unsound :
  (∀ (v : BitVec 8),
      ¬BvAtom.HoldsU 8 { lhs := { terms := [(0, 1)], const := 0 }, rel := Rel.lt, rhs := { terms := [], const := 0 } }
          (bvPt2 v 0#8)) ∧
    ∀ (v : BitVec 8),
      BvAtom.HoldsU 8 { lhs := { terms := [(0, 1)], const := 0 }, rel := Rel.le, rhs := { terms := [], const := -1 } }
        (bvPt2 v 0#8)

theorem ce_checkFarkasTightened_incomplete_int :
  List.map Constraint.tighten sysHalf = sysHalf ∧
    (∀ (x : Nat → Int), ¬SatInt sysHalf x) ∧ ∀ (cert : List Int), checkFarkasTightened sysHalf cert = false

theorem ce_checkFarkas_bv_incomplete :
  (∀ (v : BitVec (8 : Nat)),
      ¬∀ (a : BvAtom), a ∈ atomsHalfU → BvAtom.HoldsU (8 : Nat) a (bvPt2 v (BitVec.ofNat (8 : Nat) (0 : Nat)))) ∧
    (0 : Int) < (2 : Int) ∧
      SatScaled (List.map BvAtom.toConstraint atomsHalfU) (2 : Int) (pt1 (1 : Int)) ∧
        ∀ (cert : List Int), checkFarkas (List.map BvAtom.toConstraint atomsHalfU) cert = false

theorem cgLhs_eval_le_cgRhs (S : List Constraint) (k : CGStep) (hnn : multipliersNonneg k.mult = true)
  (x : Nat → Int) (hx : SatInt S x) : (cgLhs S k).eval x ≤ cgRhs S k

theorem checkFarkas_refutes_bvS_of_inSignedRange (A : List BvAtom) (cert : List Int)
  (h : checkFarkas (List.map BvAtom.toConstraint A) cert = true) (w : Nat) (x : Nat → BitVec w)
  (hl : ∀ (a : BvAtom), a ∈ A → InSignedRange w (a.lhs.evalInt (sval x)))
  (hr : ∀ (a : BvAtom), a ∈ A → InSignedRange w (a.rhs.evalInt (sval x))) : ¬∀ (a : BvAtom), a ∈ A → BvAtom.HoldsS w a x

theorem checkFarkas_refutes_bvU_of_inUnsignedRange (A : List BvAtom) (cert : List Int)
  (h : checkFarkas (List.map BvAtom.toConstraint A) cert = true) (w : Nat) (x : Nat → BitVec w)
  (hl : ∀ (a : BvAtom), a ∈ A → InUnsignedRange w (a.lhs.evalInt (uval x)))
  (hr : ∀ (a : BvAtom), a ∈ A → InUnsignedRange w (a.rhs.evalInt (uval x))) :
  ¬∀ (a : BvAtom), a ∈ A → BvAtom.HoldsU w a x

theorem check_bv_sle_transfer_w0 :
  have x := fun x => 0#0;
  ∀ (k₁ k₂ : Fin 5),
    have e₁ := { terms := [(0, 3)], const := ↑↑k₁ - 2 };
    have e₂ := { terms := [], const := ↑↑k₂ - 2 };
    InSignedRange 0 (e₁.evalInt (sval x)) →
      InSignedRange 0 (e₂.evalInt (sval x)) →
        ((AffExpr.evalBv 0 e₁ x).sle (AffExpr.evalBv 0 e₂ x) = true ↔ e₁.evalInt (sval x) ≤ e₂.evalInt (sval x))

theorem check_bv_sle_transfer_w3 (a b : Fin 8) :
  have x := bvPt2 (BitVec.ofNat 3 ↑a) (BitVec.ofNat 3 ↑b);
  have e₁ := { terms := [(0, 2), (1, -1)], const := 1 };
  have e₂ := { terms := [(1, 1)], const := 0 };
  InSignedRange 3 (e₁.evalInt (sval x)) →
    InSignedRange 3 (e₂.evalInt (sval x)) →
      ((AffExpr.evalBv 3 e₁ x).sle (AffExpr.evalBv 3 e₂ x) = true ↔ e₁.evalInt (sval x) ≤ e₂.evalInt (sval x))

theorem check_bv_ule_transfer_w3 (a b : Fin 8) :
  have x := bvPt2 (BitVec.ofNat 3 ↑a) (BitVec.ofNat 3 ↑b);
  have e₁ := { terms := [(0, 2), (1, -1)], const := 1 };
  have e₂ := { terms := [(1, 1)], const := 0 };
  InUnsignedRange 3 (e₁.evalInt (uval x)) →
    InUnsignedRange 3 (e₂.evalInt (uval x)) →
      ((AffExpr.evalBv 3 e₁ x).ule (AffExpr.evalBv 3 e₂ x) = true ↔ e₁.evalInt (uval x) ≤ e₂.evalInt (uval x))

theorem check_noWrapU_of_final_in_range_w3 (c1 c2 k v : Fin 8) :
  have e := { terms := [(0, ↑↑c1), (0, ↑↑c2)], const := ↑↑k };
  InUnsignedRange 3 (e.evalInt (uval (bvPt2 (BitVec.ofNat 3 ↑v) 0#3))) →
    NoWrapU 3 e (uval (bvPt2 (BitVec.ofNat 3 ↑v) 0#3))

theorem combine_holdsScaled (S : List Constraint) (cert : List Int) (d : Int) (p : Nat → Int)
  (hnn : ∀ (l : Int), l ∈ cert → 0 ≤ l) (hS : SatScaled S d p) :
  (combineLhs S cert).eval p ≤ combineRhs S cert * d ∧
    (combineStrict S cert = true → (combineLhs S cert).eval p < combineRhs S cert * d)

theorem combine_holdsScaled_of_posSupport (S : List Constraint) (cert : List Int) (d : Int) (p : Nat → Int)
  (hnn : ∀ (l : Int), l ∈ cert → 0 ≤ l) (hS : SatScaled (posSupport cert S) d p) :
  (combineLhs S cert).eval p ≤ combineRhs S cert * d ∧
    (combineStrict S cert = true → (combineLhs S cert).eval p < combineRhs S cert * d)

theorem ex_isZero_not_bitvector_vanishing :
  SparseVec.isZero [(0, 256)] = false ∧ ∀ (v : BitVec 8), SparseVec.evalBv 8 [(0, 256)] (bvPt2 v 0#8) = 0#8

theorem ex_one_sided_posSupport_weaker_than_two_sided :
  (checkFarkas (List.map BvAtom.toConstraint atomsLhsUnderflowU) [1, 1] = true ∧
      (¬∀ (a : BvAtom), a ∈ atomsLhsUnderflowU → InUnsignedRange 8 (a.lhs.evalInt (uval (bvPt2 0#8 0#8)))) ∧
        (∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsLhsUnderflowU → a.lhs.evalInt (uval (bvPt2 0#8 0#8)) < 2 ^ 8) ∧
          ∀ (a : BvAtom), a ∈ posSupport [1, 1] atomsLhsUnderflowU → 0 ≤ a.rhs.evalInt (uval (bvPt2 0#8 0#8))) ∧
    checkFarkas (List.map BvAtom.toConstraint atomsZeroWeight) [1, 1, 0] = true ∧
      posSupport [1, 1, 0] atomsZeroWeight = atomsLtLe ∧
        ¬∀ (a : BvAtom), a ∈ atomsZeroWeight → InUnsignedRange 8 (a.lhs.evalInt (uval (bvPt2 200#8 200#8)))

theorem inSignedRange_evalInt_of_noWrapS (w : Nat) (e : AffExpr) (ρ : Nat → Int) (h : NoWrapS w e ρ) :
  InSignedRange w (e.evalInt ρ)

theorem inUnsignedRange_evalInt_of_noWrapU (w : Nat) (e : AffExpr) (ρ : Nat → Int) (h : NoWrapU w e ρ) :
  InUnsignedRange w (e.evalInt ρ)

theorem satInt_iff_satScaled_one (S : List Constraint) (x : Nat → Int) : SatInt S x ↔ SatScaled S 1 x

theorem Motzkin.complete (S : List Constraint) (h : ∀ (d : Int) (p : Nat → Int), 0 < d → ¬SatScaled S d p) :
  ∃ cert, checkFarkas S cert = true

theorem Motzkin.fm_main (n : Nat) (H : List Motzkin.HC) :
  (∀ (h : Motzkin.HC), h ∈ H → ∀ (i : Nat), n ≤ i → h.a.coeff i = 0) →
    (∀ (y : Nat → Int), ¬Motzkin.HSat H y) → ∃ g, Motzkin.Deriv H g ∧ g.s = true ∧ ∀ (i : Nat), g.a.coeff i = 0

theorem Motzkin.elim_extend (n : Nat) (H : List Motzkin.HC) (y' : Nat → Int)
  (hy : Motzkin.HSat (Motzkin.elim n H) y') : ∃ y, Motzkin.HSat H y

theorem Motzkin.extend_of_bounds (n : Nat) (H : List Motzkin.HC) (y' : Nat → Int)
  (hZ : ∀ (h : Motzkin.HC), h ∈ H → h.a.coeff n = 0 → h.Holds y') (M t : Int) (hM : 0 < M)
  (hP :
    ∀ (p : Motzkin.HC),
      p ∈ H →
        0 < p.a.coeff n →
          M * Motzkin.rest n y' p + p.a.coeff n * t ≤ 0 ∧ (p.s = true → M * Motzkin.rest n y' p + p.a.coeff n * t < 0))
  (hN :
    ∀ (q : Motzkin.HC),
      q ∈ H →
        q.a.coeff n < 0 →
          M * Motzkin.rest n y' q + q.a.coeff n * t ≤ 0 ∧
            (q.s = true → M * Motzkin.rest n y' q + q.a.coeff n * t < 0)) :
  Motzkin.HSat H fun i => if i = n then t else M * y' i

theorem Motzkin.isMult_of_deriv {H : List Motzkin.HC} {g : Motzkin.HC} (hd : Motzkin.Deriv H g) :
  ∃ μ, Motzkin.IsMult H g μ

theorem Motzkin.homSys_sat (S : List Constraint) (y : Nat → Int) (h : Motzkin.HSat (Motzkin.homSys S) y) :
  0 < y 0 ∧ SatScaled S (y 0) fun i => y (i + 1)

theorem Motzkin.homSys_support (S : List Constraint) (h : Motzkin.HC) :
  h ∈ Motzkin.homSys S → ∀ (i : Nat), Motzkin.homBound S ≤ i → h.a.coeff i = 0

theorem Motzkin.deriv_of_mem_elim (n : Nat) (H : List Motzkin.HC) (g : Motzkin.HC) :
  g ∈ Motzkin.elim n H → Motzkin.Deriv H g

theorem Motzkin.elim_support (n : Nat) (H : List Motzkin.HC)
  (hH : ∀ (h : Motzkin.HC), h ∈ H → ∀ (i : Nat), n + 1 ≤ i → h.a.coeff i = 0) (g : Motzkin.HC) :
  g ∈ Motzkin.elim n H → ∀ (i : Nat), n ≤ i → g.a.coeff i = 0

theorem Motzkin.Deriv.trans {H H' : List Motzkin.HC} (hH : ∀ (g : Motzkin.HC), g ∈ H' → Motzkin.Deriv H g)
  {x : Motzkin.HC} (hx : Motzkin.Deriv H' x) : Motzkin.Deriv H x
```

### Statements of the definition examples

The positive and negative examples cited under Core definitions, grouped by source module in the order in which they are cited there. They use only the definitions quoted under Core definitions, are kernel-checked with standard axioms only (recorded in `audit/axioms.json`), and carry no recorded statement hash. Statements are printed by Lean's `#check` (namespace `Toy.Farkas` opened; printing options as described under Conventions); in them `↑` is a coercion to `Int` (from `Nat`; `↑↑v` for `v : Fin n` goes through `Nat`), and a statement with a binder such as `(v : Fin 7)` is a bounded check over all values of that finite type.

#### `ToyFarkas/Sparse.lean`

```lean
theorem ex_coeff_duplicates_add : SparseVec.coeff [(0, 1), (1, 5), (0, 2)] 0 = 3

theorem ex_coeff_not_first_match : SparseVec.coeff [(0, 1), (1, 5), (0, 2)] 0 ≠ 1

theorem ex_eval_pos : (SparseVec.eval [(0, 2), (1, -3)] fun i => if i = 0 then 5 else 1) = 7

theorem ex_eval_neg : (SparseVec.eval [(0, 2), (1, -3)] fun i => if i = 0 then 5 else 1) ≠ 10

theorem ex_smul_pos : SparseVec.smul 3 [(0, 2), (1, -1)] = [(0, 6), (1, -3)]

theorem ex_smul_neg : SparseVec.smul 3 [(1, 2)] ≠ [(3, 6)]

theorem ex_isZero_pos : SparseVec.isZero [(0, 1), (1, 4), (0, -1), (1, -4)] = true

theorem ex_isZero_neg : SparseVec.isZero [(0, 1), (1, 4), (0, -1)] = false

theorem ex_bound_pos : SparseVec.bound [(3, 1), (7, 0), (2, 5)] = 8

theorem ex_bound_neg : SparseVec.bound [(3, 1), (7, 0), (2, 5)] ≠ 3

theorem ex_denseDotOn_pos : (denseDotOn [0, 2] (fun i => ↑i + 1) fun x => 2) = 8

theorem ex_denseDotOn_neg : (denseDotOn [0, 2] (fun i => ↑i + 1) fun x => 2) ≠ 12

theorem ex_denseDot_pos : (denseDot 3 (fun i => ↑i) fun x => 1) = 3

theorem ex_denseDot_neg : (denseDot 3 (fun i => ↑i) fun x => 1) ≠ 6
```

#### `ToyFarkas/Constraint.lean`

```lean
theorem ex_holdsInt_pos : { lhs := [(0, 2), (1, -1)], rel := Rel.le, rhs := 3 : Constraint }.HoldsInt (pt2 2 1)

theorem ex_holdsInt_neg : ¬{ lhs := [(0, 2), (1, -1)], rel := Rel.le, rhs := 3 : Constraint }.HoldsInt (pt2 3 1)

theorem ex_holdsInt_strict_neg : ¬{ lhs := [(0, 1)], rel := Rel.lt, rhs := 2 : Constraint }.HoldsInt (pt1 2)

theorem ex_holdsScaled_pos : { lhs := [(0, 2)], rel := Rel.le, rhs := 1 : Constraint }.HoldsScaled 2 (pt1 1)

theorem ex_holdsScaled_neg : ¬{ lhs := [(0, 2)], rel := Rel.le, rhs := 1 : Constraint }.HoldsScaled 2 (pt1 3)

theorem ex_satScaled_pos :
  SatScaled [{ lhs := [(0, 2)], rel := Rel.le, rhs := 1 }, { lhs := [(0, -2)], rel := Rel.le, rhs := -1 }] 2 (pt1 1)

theorem ex_satScaled_neg :
  ¬SatScaled [{ lhs := [(0, 2)], rel := Rel.le, rhs := 1 }, { lhs := [(0, -2)], rel := Rel.le, rhs := -1 }] 2 (pt1 3)

theorem ex_satInt_pos :
  SatInt [{ lhs := [(0, 1)], rel := Rel.le, rhs := 1 }, { lhs := [(0, -1)], rel := Rel.le, rhs := 0 }] (pt1 1)

theorem ex_satInt_neg (v : Fin 7) :
  ¬SatInt [{ lhs := [(0, 2)], rel := Rel.le, rhs := 1 }, { lhs := [(0, -2)], rel := Rel.le, rhs := -1 }] (pt1 (↑↑v - 3))

theorem ex_satScaled_denominator_zero_degenerate : SatScaled [{ lhs := [], rel := Rel.le, rhs := -1 }] 0 fun x => 0

theorem ex_isStrict_pos : { lhs := [(0, 1)], rel := Rel.lt, rhs := 1 : Constraint }.isStrict = true

theorem ex_isStrict_neg : { lhs := [(0, 1)], rel := Rel.le, rhs := 1 : Constraint }.isStrict = false
```

#### `ToyFarkas/Checker.lean`

```lean
theorem ex_multipliersNonneg_pos : multipliersNonneg [0, 3, 1] = true

theorem ex_multipliersNonneg_neg : multipliersNonneg [0, -3, 1] = false

theorem ex_combineLhs_pos : combineLhs sysLeGe [1, 1] = [(0, 1), (0, -1)]

theorem ex_combineLhs_neg : combineLhs sysLeGe [1, 1] ≠ []

theorem ex_combineRhs_pos : combineRhs sysLeGe [1, 1] = -1

theorem ex_combineRhs_neg : combineRhs sysLeGe [2, 1] ≠ -1

theorem ex_combineStrict_pos : combineStrict sysStrict [1, 1] = true

theorem ex_combineStrict_neg : combineStrict sysStrict [0, 1] = false

theorem ex_lhsVanishes_pos : lhsVanishes sysLeGe [1, 1] = true

theorem ex_lhsVanishes_neg : lhsVanishes sysLeGe [1, 2] = false

theorem ex_rhsContradicts_pos : rhsContradicts sysLeGe [1, 1] = true

theorem ex_rhsContradicts_neg : rhsContradicts sysEq [1, 1] = false

theorem ex_checkFarkas_pos : checkFarkas sysLeGe [1, 1] = true

theorem ex_checkFarkas_strict_pos : checkFarkas sysStrict [1, 1] = true

theorem ex_checkFarkas_neg (a b : Fin 5) : checkFarkas sysEq [↑↑a - 2, ↑↑b - 2] = false

theorem ex_checkFarkas_short_certificate :
  checkFarkas (sysLeGe ++ [{ lhs := [(1, 1)], rel := Rel.le, rhs := 5 }]) [1, 1] = true

theorem ex_checkFarkas_surplus_multipliers :
  checkFarkas sysLeGe [1, 1, 7] = true ∧ checkFarkas sysLeGe [1, 1, -7] = false
```

#### `ToyFarkas/Counterexamples.lean`

```lean
theorem ex_rhsContradictsIgnoringStrictness_pos : rhsContradictsIgnoringStrictness sysEq [1, 1] = true

theorem ex_rhsContradictsIgnoringStrictness_neg : rhsContradictsIgnoringStrictness sysTwoUpper [1, 0] = false

theorem ex_combineStrictAnyPremise_pos : combineStrictAnyPremise sysEqPlusStrict [1, 1, 0] = true

theorem ex_combineStrictAnyPremise_neg : combineStrictAnyPremise sysEq [1, 1] = false

theorem ex_rhsContradictsAnyPremise_pos : rhsContradictsAnyPremise sysEqPlusStrict [1, 1, 0] = true

theorem ex_rhsContradictsAnyPremise_neg : rhsContradictsAnyPremise sysEq [1, 1] = false

theorem ex_tighten_pos :
  { lhs := [(0, 1)], rel := Rel.lt, rhs := 1 : Constraint }.tighten =
    { lhs := [(0, 1)], rel := Rel.le, rhs := 0 : Constraint }

theorem ex_tighten_neg :
  { lhs := [(0, 1)], rel := Rel.le, rhs := 1 : Constraint }.tighten ≠
    { lhs := [(0, 1)], rel := Rel.le, rhs := 0 : Constraint }

theorem ex_isZeroIndexBlind_pos : isZeroIndexBlind [(0, 1), (0, -1)] = true

theorem ex_isZeroIndexBlind_neg : isZeroIndexBlind [(0, 1), (1, 1)] = false

theorem ex_coeffFirstMatch_pos : coeffFirstMatch [(0, 0), (0, 1)] 0 = 0

theorem ex_coeffFirstMatch_neg : coeffFirstMatch [(0, 0), (0, 1)] 0 ≠ SparseVec.coeff [(0, 0), (0, 1)] 0

theorem ex_isZeroFirstMatch_pos : isZeroFirstMatch [(0, 0), (1, 0)] = true

theorem ex_isZeroFirstMatch_neg : isZeroFirstMatch [(0, 0), (1, 2)] = false
```

#### `ToyFarkas/Cuts.lean`

```lean
theorem ex_cgCut_floor_negative :
  cgCut sysHalf { mult := [0, 1], div := 2 } = { lhs := [(0, -1)], rel := Rel.le, rhs := -1 }

theorem ex_cgLhs_pos :
  cgLhs [{ lhs := [(0, 1), (1, 1)], rel := Rel.le, rhs := 1 }, { lhs := [(0, 1), (1, -1)], rel := Rel.le, rhs := 0 }]
      { mult := [1, 1], div := 2 } =
    [(0, 1), (1, 1), (0, 1), (1, -1)]

theorem ex_cgLhs_neg :
  cgLhs [{ lhs := [(0, 1), (1, 1)], rel := Rel.le, rhs := 1 }, { lhs := [(0, 1), (1, -1)], rel := Rel.le, rhs := 0 }]
      { mult := [1, 1], div := 2 } ≠
    [(0, 1)]

theorem ex_cgCut_pos : cgCut sysTwoXLeThree { mult := [1], div := 2 } = { lhs := [(0, 1)], rel := Rel.le, rhs := 1 }

theorem ex_cgCut_neg : cgCut sysTwoXLeThree { mult := [1], div := 2 } ≠ { lhs := [(0, 1)], rel := Rel.le, rhs := 2 }

theorem ex_cgRhs_strict_pos : cgRhs [{ lhs := [(0, 2)], rel := Rel.lt, rhs := 3 }] { mult := [1], div := 2 } = 2

theorem ex_cgRhs_neg : cgRhs [{ lhs := [(0, 2)], rel := Rel.lt, rhs := 3 }] { mult := [1], div := 2 } ≠ 3

theorem ex_cgDivisible_pos : cgDivisible sysTwoXLeThree { mult := [1], div := 2 } = true

theorem ex_cgDivisible_neg : cgDivisible sysTwoXLeThree { mult := [1], div := 3 } = false

theorem ex_cgDivisible_duplicates_pos :
  cgDivisible
      [{ lhs := [(0, 1), (1, 1)], rel := Rel.le, rhs := 1 }, { lhs := [(0, 1), (1, -1)], rel := Rel.le, rhs := 0 }]
      { mult := [1, 1], div := 2 } =
    true

theorem ex_cgValid_pos : cgValid sysTwoXLeThree { mult := [1], div := 2 } = true

theorem ex_cgValid_neg : cgValid sysTwoXLeThree { mult := [1], div := 0 } = false

theorem ex_cgDerive_pos :
  cgDerive sysTwoXLeThree { mult := [1], div := 2 } = some { lhs := [(0, 1)], rel := Rel.le, rhs := 1 }

theorem ex_cgDerive_neg : cgDerive sysTwoXLeThree { mult := [-1], div := 2 } = none

theorem ex_applyCuts_pos :
  applyCuts sysHalf halfCutCert.cuts =
    some (sysHalf ++ [{ lhs := [(0, 1)], rel := Rel.le, rhs := 0 }, { lhs := [(0, -1)], rel := Rel.le, rhs := -1 }])

theorem ex_applyCuts_neg : applyCuts sysHalf [{ mult := [1, 0], div := 3 }] = none

theorem ex_checkCutCert_pos : checkCutCert sysHalf halfCutCert = true

theorem ex_checkCutCert_neg : checkCutCert sysHalf { cuts := [], farkas := [1, 1] } = false

theorem ex_checkCutCert_no_cuts_no_tightening :
  checkCutCert sysOpenUnit { cuts := [], farkas := [1, 1] } = false ∧
    checkCutCert sysOpenUnit { cuts := [{ mult := [1, 1], div := 1 }], farkas := [0, 0, 1] } = true
```

#### `ToyFarkas/BitVecTransfer.lean`

```lean
theorem ex_noWrapU_rejects_machine_subtraction :
  (10#8 - 3#8).toNat = 7 ∧
    { terms := [(0, 1), (1, -1)], const := 0 : AffExpr }.evalInt (uval (bvPt2 10#8 3#8)) = 7 ∧
      ¬NoWrapU 8 { terms := [(0, 1), (1, -1)], const := 0 : AffExpr } (uval (bvPt2 10#8 3#8))

theorem ex_evalInt_pos : eDouble.evalInt (uval (bvPt2 200#8 0#8)) = 400

theorem ex_evalInt_neg : eDouble.evalInt (uval (bvPt2 200#8 0#8)) ≠ 144

theorem ex_evalBv_pos : AffExpr.evalBv 8 eDouble (bvPt2 200#8 0#8) = 144#8

theorem ex_evalBv_neg : (AffExpr.evalBv 8 eDouble (bvPt2 200#8 0#8)).toNat ≠ 400

theorem ex_sparse_evalBv_pos : SparseVec.evalBv 8 [(0, -1)] (bvPt2 1#8 0#8) = 255#8

theorem ex_sparse_evalBv_neg : SparseVec.evalBv 8 [(0, -1)] (bvPt2 1#8 0#8) ≠ 0#8

theorem ex_uval_pos : uval (bvPt2 255#8 0#8) 0 = 255

theorem ex_uval_neg : uval (bvPt2 255#8 0#8) 0 ≠ -1

theorem ex_sval_pos : sval (bvPt2 255#8 0#8) 0 = -1

theorem ex_sval_neg : sval (bvPt2 255#8 0#8) 0 ≠ 255

theorem ex_inUnsignedRange_pos : InUnsignedRange 8 255

theorem ex_inUnsignedRange_neg : ¬InUnsignedRange 8 256 ∧ ¬InUnsignedRange 8 (-1)

theorem ex_inSignedRange_pos : InSignedRange 8 (-128) ∧ InSignedRange 8 127

theorem ex_inSignedRange_neg : ¬InSignedRange 8 128 ∧ ¬InSignedRange 8 (-129)

theorem ex_inSignedRange_zero_width : InSignedRange 0 0 ∧ ¬InSignedRange 0 (-1)

theorem ex_intermediates_pos : eDouble.intermediates (uval (bvPt2 200#8 0#8)) = [1, 200, 200, 1, 200, 400, 0, 400]

theorem ex_intermediates_neg : eDouble.intermediates (uval (bvPt2 200#8 0#8)) ≠ [400]

theorem ex_noWrapU_pos : NoWrapU 8 eDouble (uval (bvPt2 100#8 0#8))

theorem ex_noWrapU_neg : ¬NoWrapU 8 eDouble (uval (bvPt2 200#8 0#8))

theorem ex_noWrapS_pos : NoWrapS 8 eDouble (sval (bvPt2 50#8 0#8))

theorem ex_noWrapS_neg : ¬NoWrapS 8 eDouble (sval (bvPt2 100#8 0#8))

theorem ex_noWrap_checks_coefficient_literals :
  ¬NoWrapU 8 { terms := [(0, 1000)], const := 0 } (uval (bvPt2 0#8 0#8)) ∧
    ¬NoWrapS 8 { terms := [(0, 1000)], const := 0 } (sval (bvPt2 0#8 0#8))
```

#### `ToyFarkas/BitVecSystems.lean`

```lean
theorem ex_bvAtom_holdsU_pos : BvAtom.HoldsU 8 atomEx (bvPt2 3#8 4#8)

theorem ex_bvAtom_holdsU_neg : ¬BvAtom.HoldsU 8 atomEx (bvPt2 4#8 4#8)

theorem ex_bvAtom_holdsU_wrap : BvAtom.HoldsU 8 atomEx (bvPt2 255#8 0#8)

theorem ex_bvAtom_holdsS_pos : BvAtom.HoldsS 8 atomEx (bvPt2 255#8 0#8)

theorem ex_bvAtom_holdsS_neg : ¬BvAtom.HoldsS 8 atomEx (bvPt2 5#8 3#8)

theorem ex_bvAtom_toConstraint_pos : atomEx.toConstraint = { lhs := [(0, 1), (1, -1)], rel := Rel.le, rhs := -1 }

theorem ex_bvAtom_toConstraint_neg : atomEx.toConstraint ≠ { lhs := [(0, 1), (1, -1)], rel := Rel.le, rhs := 1 }
```

## Boundaries

### Non-claims

What each result does *not* show. These qualify the plain claims in Summary and Findings.

#### R1a — `checkFarkas_sound_scaled`

- Does not show completeness: that every system without a scaled solution has an accepted certificate is the separate result R4a.
- Does not reject length-mismatched certificates: multiplier k is paired with constraint k by List.zipWith, so constraints without a multiplier get multiplier 0 and surplus multipliers are ignored by the combination (though still checked to be non-negative).
- The rational reading is by scaling: a point is a pair (d, p) with d > 0 standing for p / d. No rational number type is used; the correspondence with rational points (finite systems only) is the separate modeling-bridge claim, not a Lean theorem.
- Does not concern rational-coefficient input: constraints have Int coefficients and right-hand sides; a rational constraint must first be scaled by a positive integer, and that scaling step is not modeled.
- Does not model equality (=) or disequality (!=) constraints: Rel contains only <= and <. An equality a . x = b must be encoded as two inequalities a . x <= b and -a . x <= -b; disequalities require disjunctive reasoning.
- Does not say anything about bit-vector (machine-integer) semantics; see R6e/R6f for the range facts needed.

#### R1c — `farkas_sound_scaled_of_nonneg_of_lhsVanishes_of_rhsContradicts`

- Does not show these are the only sound checker designs; it shows each of the four conditions cannot be dropped from this one.
- Strictness is taken only from premises with a positive multiplier; variants that read strictness from any premise or ignore it are unsound (R3b).
- The rational reading is by scaling: a point is a pair (d, p) with d > 0 standing for p / d. No rational number type is used; the correspondence with rational points (finite systems only) is the separate modeling-bridge claim, not a Lean theorem.
- Does not reject length-mismatched certificates: multiplier k is paired with constraint k by List.zipWith, so constraints without a multiplier get multiplier 0 and surplus multipliers are ignored by the combination (though still checked to be non-negative).
- Does not concern rational-coefficient input: constraints have Int coefficients and right-hand sides; a rational constraint must first be scaled by a positive integer, and that scaling step is not modeled.
- Does not model equality (=) or disequality (!=) constraints: Rel contains only <= and <. An equality a . x = b must be encoded as two inequalities a . x <= b and -a . x <= -b; disequalities require disjunctive reasoning.
- Does not apply to wrapping bit-vector semantics without separate range facts; see R6e/R6f.

#### R2a — `SparseVec.eval_eq_denseDotOn_coeff_of_nodup_of_keys_mem`

- Does not concern normalization: no canonical sorted or duplicate-free sparse form is defined or claimed.
- Says nothing about efficiency of either representation.

#### R2b — `combineLhs_coeff`

- Pairing is List.zipWith: unpaired constraints or multipliers are dropped from the sum.
- Says nothing about the size or normal form of the combined list.

#### R2d — `SparseVec.isZero_iff_coeff_eq_zero`

- Index-blind (sum of all coefficients) and first-match zero tests are not equivalent and are unsound inside a checker (R3f).
- Characterizes vanishing of the integer coefficient function (equivalently, vanishing of eval at all Int points), not vanishing over finite rings or BitVec w: over BitVec 8, the nonzero form 256 * x0 evaluates to 0#8 everywhere while isZero returns false (ex_isZero_not_bitvector_vanishing).
- Says nothing about efficiency (the test is quadratic in the list length).

#### R3a — `ce_farkas_negative_multiplier`

- Does not show that negative multipliers are useless in other certificate formats: formats with equality constraints allow arbitrary-sign multipliers on equalities; this checker has no equality constraints.
- Alethe's la_generic uses the absolute value of each coefficient for inequalities, a different way to enforce the sign condition; not modeled.

#### R3b — `ce_farkas_strictness_ignored`

- Treating strict premises as non-strict is the opposite mismatch; it is sound but incomplete and is not a counterexample to soundness.
- Does not cover other strictness encodings, such as the infinitesimal-delta bounds used by simplex-based solvers (Dutertre and de Moura 2006).

#### R3d — `checkFarkasTightened_sound_int`

- Not sound over the rationals: the same certificate is accepted for a rationally satisfiable system (R3e).
- Does not make Farkas certificates complete over Int: on systems with no strict constraints such as {2x0 <= 1, -2x0 <= -1}, checkFarkasTightened is identical to checkFarkas and still rejects every certificate (ce_checkFarkasTightened_incomplete_int, R4b).
- Not sound for mixed-integer (MILP / LIRA) systems: the integer step requires every variable with a nonzero coefficient to be integral (the model has only integer variables x : Nat -> Int); continuous variables must be eliminated or handled by mixed-integer cuts.
- Not sound for wrapping bit-vector constraints: over BitVec w, x <u 0 is unsatisfiable while x <=u (0 - 1) = 2^w - 1 is identically true (ce_bv_tightening_unsound; similarly at the signed minimum -2^(w-1)).
- Does not reject length-mismatched certificates: multiplier k is paired with constraint k by List.zipWith, so constraints without a multiplier get multiplier 0 and surplus multipliers are ignored by the combination (though still checked to be non-negative).
- Does not concern rational-coefficient input: constraints have Int coefficients and right-hand sides; a rational constraint must first be scaled by a positive integer, and that scaling step is not modeled.

#### R3e — `ce_tightening_unsound_over_rat`

- Does not show that integer tightening is unsound over Int (it is sound, R3d).
- Integral variables alone are not sufficient for tightening: integer coefficients and an integer right-hand side are also required (e.g., over integral x0, (1/2)x0 < 1 holds at x0 = 1 while (1/2)x0 <= 0 fails); in this model coefficients are Int by construction, so a rational constraint must be scaled to integer coefficients before tightening.

#### R3f — `ce_zero_test_index_blind`

- Does not claim any deployed checker uses these tests; it shows why the dense semantics (R2d) is the right zero test.
- Only relevant when the combined form combineLhs S cert can contain duplicate indices. Duplicate-free input constraints do not make first-match lookup safe, because combineLhs concatenates scaled premises and multiplying by 0 inserts (i, 0) entries ahead of nonzero entries for the same index; first-match lookup is sound only if the combined linear form itself is merged into a duplicate-free normal form.

#### R4a — `farkas_complete_scaled`

- Not true over the integers: R4b.
- Applies only to finite constraint lists S : List Constraint; Farkas' lemma and Motzkin's transposition theorem can fail for infinite systems of linear inequalities.
- Is an existential statement: although the proof follows Fourier-Motzkin elimination, the theorem exports no executable or verified certificate generator, does not assert cert.length = S.length, and does not bound the number of nonzero multipliers, the bit-size of the multipliers, or the cost of finding them.
- Does not model equality (=) or disequality (!=) constraints: Rel contains only <= and <. An equality a . x = b must be encoded as two inequalities a . x <= b and -a . x <= -b; disequalities require disjunctive reasoning.
- The rational reading is by scaling: a point is a pair (d, p) with d > 0 standing for p / d. No rational number type is used; the correspondence with rational points (finite systems only) is the separate modeling-bridge claim, not a Lean theorem.

#### R4b — `ce_farkas_incomplete_int`

- Does not show that integer infeasibility is uncheckable: the cut-plus-Farkas checker refutes the same system (positive control nv_checkCutCert_sound_int).
- Is a single instance, not a characterization of which integer-infeasible systems lack Farkas certificates.
- Escape hatch (cutting planes and GCD tightening): adding Chvátal–Gomory cuts (checkCutCert) or GCD divisibility/tightening rules (as in Lean's omega, Init/Omega/Constraint.lean) defeats this impossibility: dividing 2x0 <= 1 by 2 and rounding gives x0 <= 0.
- Escape hatch (case splitting): allowing integer case splits (x <= k or x >= k + 1, as in branch-and-bound or Rocq ZMicromega's SplitProof) defeats it without cutting planes: both branches of sysHalf under the split x0 <= 0 or x0 >= 1 have accepted Farkas certificates (sysHalf_refuted_by_case_split).
- Escape hatch (totally unimodular fragments; the integrality step is not formalized here): the impossibility uses a non-unimodular coefficient (2). For a totally unimodular constraint matrix with integer right-hand sides and only non-strict constraints, including difference constraints x_i - x_j <= c, x_i <= c, -x_i <= c, a rationally feasible system has an integer solution (Hoffman–Kruskal 1956), so, combined with R4a, plain Farkas certificates are complete for integer infeasibility on that fragment. With strict constraints this needs integer tightening first: {x0 < 1, -x0 < 0} is totally unimodular, integer infeasible, rationally feasible, and refuted only by the tightened checker (R3d, R3e).
- Escape hatch (rational or real domain): over scaled points (d > 0), {2x0 <= 1, -2x0 <= -1} is feasible at x0 = 1/2, so the integer-infeasibility premise of the impossibility is what fails; for rationally infeasible systems Farkas certificates exist by R4a.
- Non-escape: integer tightening of strict inequalities (R3d, checkFarkasTightened) does not escape this impossibility, because {2x0 <= 1, -2x0 <= -1} contains no strict constraints (ce_checkFarkasTightened_incomplete_int).

#### R5a — `cgCut_sound_int_of_nonneg_of_div_pos_of_divisible`

- Does not claim the cut is non-redundant or that any sequence of cuts reaches the integer hull (Chvátal 1973 / Schrijver 1980 finiteness results are not formalized).
- Divisor 0 is excluded by hg although it would be harmless (Lean's x / 0 = 0 yields 0 <= 0).
- Unsound over the rationals even when div = 1 (no division or rounding) whenever S contains strict constraints, because cgRhs tightens every strict premise before combining (ce_cgCut_div_one_unsound_over_rat).
- Not sound for mixed-integer (MILP / LIRA) systems: the integer step requires every variable with a nonzero coefficient to be integral (the model has only integer variables x : Nat -> Int); continuous variables must be eliminated or handled by mixed-integer cuts.
- Not sound for wrapping bit-vector constraints: over BitVec w, x <u 0 is unsatisfiable while x <=u (0 - 1) = 2^w - 1 is identically true (ce_bv_tightening_unsound; similarly at the signed minimum -2^(w-1)).
- Uses List.zipWith pairing: short multiplier lists give remaining constraints multiplier 0 and surplus multipliers are ignored by the combination (though still checked non-negative).
- Does not say the step is the strongest available cut (no gcd normalization of the derived cut is performed or claimed).
- Does not concern rational-coefficient input: constraints have Int coefficients and right-hand sides; a rational constraint must first be scaled by a positive integer, and that scaling step is not modeled.

#### R5c — `checkCutCert_sound_int`

- Does not claim completeness of cut-plus-Farkas certificates for integer infeasibility (known for bounded rational polytopes by Chvátal 1973 and for arbitrary rational polyhedra by Schrijver 1980; not formalized here).
- Does not prove rational infeasibility: the certificate halfCutCert is accepted for {2x0 <= 1, -2x0 <= -1}, which x0 = 1/2 satisfies (ce_checkCutCert_unsound_over_rat).
- Does not bound the number of cuts (Chvátal rank) or the total certificate size required to refute an integer-infeasible system; moreover, when cc.cuts = [], checkCutCert is plain checkFarkas and does not tighten strict premises, unlike a single CG step with divisor 1 (ex_checkCutCert_no_cuts_no_tightening).
- Not sound for mixed-integer (MILP / LIRA) systems: the integer step requires every variable with a nonzero coefficient to be integral (the model has only integer variables x : Nat -> Int); continuous variables must be eliminated or handled by mixed-integer cuts.
- Not sound for wrapping bit-vector constraints: over BitVec w, x <u 0 is unsatisfiable while x <=u (0 - 1) = 2^w - 1 is identically true (ce_bv_tightening_unsound; similarly at the signed minimum -2^(w-1)).
- Uses List.zipWith pairing in every step and in the final Farkas combination.
- Does not concern rational-coefficient input: constraints have Int coefficients and right-hand sides; a rational constraint must first be scaled by a positive integer, and that scaling step is not modeled.

#### R6a — `bv_ule_ult_iff_int_of_inUnsignedRange`

- Only the final values of e1 and e2 must be in range; intermediate values may wrap (R6i). This is specific to wrapping semantics.
- For the forward direction alone (bit-vector comparison implies integer comparison) the one-sided bounds e1 < 2^w and 0 <= e2 suffice (bv_ule_ult_imp_int_of_lhs_lt_of_rhs_nonneg); the biconditional needs all four bounds.
- The reading must match the comparison: unsigned comparison with signed-reading ranges fails, and signed comparison with unsigned-reading ranges fails (R6g).
- Does not license moving terms across the comparison (R6h).
- Covers only <= and < (ule/ult), not equality (=) or disequality (!=). Bit-vector equality implies integer equality only when both sides are in range (whereas integer equality always implies wrapping bit-vector equality).
- Applies to a single fixed bit-width w; mixed-width expressions (zero-extension, sign-extension, truncation) are not modeled.
- Concerns only wrapping (modular) evaluation of +, *, and literals; division, remainder, shifts, and checked or trapping arithmetic (where intermediate overflow matters) are out of scope.
- Does not show how to establish the range facts; they are hypotheses to be discharged by other means (e.g. interval reasoning).

#### R6b — `bv_sle_slt_iff_int_of_inSignedRange`

- At w = 0 the signed range is {0} (the 2z formulation avoids the natural-number pitfall 2^(0-1) = 1); the statement is also checked at w = 0 on 25 constant pairs in check_bv_sle_transfer_w0.
- Only final values must be in range; intermediate wrap is harmless for wrapping semantics (R6i).
- For the forward direction alone the one-sided bounds 2 e1 < 2^w and -2^w <= 2 e2 suffice (bv_sle_slt_imp_int_of_lhs_lt_of_rhs_ge).
- The reading must match the comparison: signed comparison with unsigned-reading ranges is likewise wrong (R6g).
- Covers only <= and < (sle/slt), not equality (=) or disequality (!=).
- Applies to a single fixed bit-width w; mixed-width expressions (zero-extension, sign-extension, truncation) are not modeled.
- Concerns only wrapping (modular) evaluation of +, *, and literals; division, remainder, shifts, and checked or trapping arithmetic (where intermediate overflow matters) are out of scope.
- Does not license moving terms across a signed comparison: at w = 8 and (x0, x1) = (-100, 100) both sides of x0 <=s x1 are in signed range and the comparison holds, but x0 - x1 <=s 0 fails because x0 - x1 = -200 wraps to 56 (R6h, ce_bv_rearrangement_unsound); a rearranged comparison needs range facts for its own sides.
- Does not show how to establish the range facts InSignedRange w (e1.evalInt (sval x)) and InSignedRange w (e2.evalInt (sval x)); they are hypotheses that must be discharged independently (e.g. by interval reasoning), and a range fact about the difference e1 - e2 alone does not suffice (ce_bvS_range_on_difference_insufficient).

#### R6c — `bv_ule_ult_iff_int_of_noWrapU`

- The hypotheses cannot be dropped but can be weakened to final-value range facts (R6a/R6b); ce_noWrap_not_needed_for_wrapping_eval exhibits intermediate wrap with the wrapping value intact.
- NoWrapU/NoWrapS are toy no-wrap conditions for the evaluation order of SparseVec.evalBv (terms summed left to right, constant added last); a different evaluation order has different intermediates.
- AffExpr has no subtraction: x0 - x1 is x0 + (-1) * x1, so under the unsigned reading any term with a negative coefficient fails NoWrapU even when the machine subtraction would not underflow (ex_noWrapU_rejects_machine_subtraction). NoWrapU is therefore not the LLVM nuw condition.
- Coefficient literals are checked: a literal outside the range (e.g. 1000 at w = 8) violates NoWrapU/NoWrapS even when its variable is 0 (ex_noWrap_checks_coefficient_literals).
- Concerns only wrapping (modular) evaluation of +, *, and literals; division, remainder, shifts, and checked or trapping arithmetic (where intermediate overflow matters) are out of scope.

#### R6e — `checkFarkas_refutes_bvU_posSupport_of_lhs_lt_of_rhs_nonneg`

- Is pointwise: it refutes the bit-vector system only at points where the range facts hold, not globally.
- Lower bounds on left sides, upper bounds on right sides, and any bounds on atoms with multiplier 0 are not needed (ex_one_sided_posSupport_weaker_than_two_sided); the two-sided version is a corollary.
- The translation moves terms across the comparison, which is valid over Int only; the range facts are on the two original sides, not on e1 - e2.
- BvAtom.toConstraint does not emit intrinsic bit-vector domain bounds (0 <= x_i < 2^w). A bit-vector-unsatisfiable system such as {x0 <u 0} translates to {x0 < 0}, which is satisfiable over Int and cannot be refuted unless variable domain bounds are explicitly included in A (ce_bv_domain_bounds_not_emitted).
- Does not show how to establish the range facts hl and hr; they must be discharged independently, without circularly relying on wrapping bit-vector atoms in A (for example, x0 + 1 <u 10 holds at x0 = 255#8 even though x0 + 1 wraps).
- Does not give completeness over BitVec w even when all range facts hold: {2x0 <=u 1, 1 <=u 2x0} fails at every 8-bit point, yet checkFarkas rejects every certificate for its translation (ce_checkFarkas_bv_incomplete, cf. R4b).
- Requires all atoms in A to share a single width w and the unsigned reading; mixed-width and mixed-signedness systems are not modeled.
- Invokes only plain checkFarkas, not checkCutCert or checkFarkasTightened; in particular, tightening a strict bit-vector comparison before translation (a <u b to a <=u b - 1) is unsound at b = 0 (ce_bv_tightening_unsound).
- Concerns only wrapping (modular) evaluation of +, *, and literals; division, remainder, shifts, and checked or trapping arithmetic (where intermediate overflow matters) are out of scope.

#### R6f — `checkFarkas_refutes_bvS_posSupport_of_lhs_lt_of_rhs_ge`

- Is pointwise, as R6e.
- The translation moves terms across the comparison, which is valid over Int only; the range facts must hold on the two original sides a.lhs and a.rhs, not on a.lhs - a.rhs: for the atom 150 <= 100 at w = 8 the difference 50 is in signed range, 150 wraps to -106, and 150 <=s 100 holds (ce_bvS_range_on_difference_insufficient).
- BvAtom.toConstraint does not emit intrinsic signed domain bounds (-2^w <= 2*x_i < 2^w, i.e., -2^(w-1) <= x_i < 2^(w-1) for w >= 1 and x_i = 0 for w = 0); they must be included in A explicitly (cf. ce_bv_domain_bounds_not_emitted for the unsigned case).
- Does not show how to establish the range facts; they must be discharged without circularly relying on wrapping atoms in A.
- Does not give completeness over BitVec w even when all range facts hold (cf. ce_checkFarkas_bv_incomplete, R4b).
- Requires a single width w and the signed reading for all atoms; mixed-width and mixed-signedness systems are not modeled.
- Invokes only plain checkFarkas; tightening a strict signed comparison before translation is unsound at the signed minimum -2^(w-1).
- Concerns only wrapping (modular) evaluation of +, *, and literals; division, remainder, shifts, and checked or trapping arithmetic (where intermediate overflow matters) are out of scope.

#### R6g — `ce_bv_reading_mismatch`

- Does not show any mixed-signedness transfer is impossible; only that pairing a comparison with the other signedness's reading is wrong.

#### R6h — `ce_bv_rearrangement_unsound`

- Does not show rearrangement is always wrong: it is valid when the rearranged sides are themselves in range (then R6a or R6b applies to them).

#### R6i — `ce_noWrap_not_needed_for_wrapping_eval`

- Does not apply to checked or trapping arithmetic, or to poison-on-overflow flags such as LLVM nuw/nsw, where an intermediate overflow changes the result.
- In the unsigned reading, if every coefficient literal lies in [0, 2^w) and the constant is non-negative, products and partial sums are non-negative and bounded by the final value, so an in-range final value implies NoWrapU; unsigned intermediate wrap with an in-range final value therefore needs a negative literal (here -1). Stated for orientation, not proved as a general theorem (bounded check check_noWrapU_of_final_in_range_w3: w = 3, two terms, all such literals, constants, and points).

### Attractive stronger conclusions that are not established

- R1a and R4a together give: for a finite `S`, `checkFarkas` accepts some certificate exactly when no scaled point `(d, p)` with `d > 0` satisfies `S` (derived by combining the two theorems; not stated as one Lean theorem). This says nothing about integer feasibility: R4b exhibits an integer-infeasible system for which every certificate is rejected.
- No completeness theorem is proved for the integer-tightened checker (R3d) or for the cut-plus-Farkas checker (R5c). That finitely many rounds of Chvátal–Gomory cuts reach the integer hull (Chvátal 1973 for bounded polytopes; Schrijver 1980 for rational polyhedra) is cited, not formalized.
- R4a bounds neither the size of a certificate nor the cost of finding one; Fourier–Motzkin elimination is only the proof method.
- No result shows that a particular SMT proof checker, tactic, solver, or compiler implements these definitions; that reading is the derived modeling bridge under Applicability.
- The bit-vector results give no decision procedure for bit-vector arithmetic and do not show how range facts are obtained; they state what must be established before integer reasoning may be used.

### Escape hatches for the impossibility result (R4b)

R4b (`ce_farkas_incomplete_int`) shows that plain Farkas certificates cannot refute the integer-infeasible system `{2x₀ ≤ 1, -2x₀ ≤ -1}`. Each of the following defeats it (details in the R4b non-claims above):

- **Cutting planes or GCD tightening:** dividing `2x₀ ≤ 1` by `2` and rounding gives `x₀ ≤ 0`; the cut-plus-Farkas checker accepts a certificate (positive control `nv_checkCutCert_sound_int`).
- **Integer case splits:** under `x₀ ≤ 0 ∨ x₀ ≥ 1` both branches have accepted Farkas certificates (positive control `sysHalf_refuted_by_case_split`).
- **Totally unimodular fragments** (the integrality step, Hoffman–Kruskal 1956, is not formalized): with only non-strict constraints and integer right-hand sides, a rationally feasible system has an integer solution, so with R4a plain certificates suffice; strict constraints first need integer tightening (R3d, R3e).
- **Rational or real domain:** over scaled points the system is feasible (`x₀ = 1/2`), so the premise of the impossibility fails.
- **Not an escape:** integer tightening of strict inequalities alone (R3d) does not help, because the system has no strict constraint (`ce_checkFarkasTightened_incomplete_int`).

### Tightness status

Every hypothesis of every card is `tight`, with a kernel-checked counterexample named in its ledger. No hypothesis is labeled `harmless` or `unknown`.

### Disproved or dropped statements

None. No statement of this package was found false, and none was dropped or weakened.

## Evidence

### Kernel-check record

Observed on 2026-11-20 with Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`, resolved through the GitHub API):

- `lake build` of `lean/` succeeds; no declaration uses `sorry`.
- No Lean source contains `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `extern`, or `unsafe`.
- All 619 declarations of the `ToyFarkas` modules were audited with `Lean.collectAxioms`; each depends only on a subset of `propext`, `Classical.choice`, `Quot.sound`. The per-declaration lists are in `audit/axioms.json`.
- The statement hash is the SHA-256 of Lean's `repr` of the theorem's type. The closure hash is the SHA-256 of the sorted, newline-joined lines `name : type := value` for every package constant reachable from the statement (types and values of definitions, structures and inductive types; theorem bodies excluded). Both are recorded in `audit/statements.json` and are recomputed by the commands under Revalidation.

| Theorem | Referenced by | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `checkFarkas_sound_scaled` | R1a result | Classical.choice, Quot.sound, propext | `1a507ae10913942459136278d78e0163cc274aec1d790006ceb029644b77e52e` | `7916ce0aeaff1e5a308e410357af6ae0bf3f1373c27bebf7485bbecd0b47370c` (28) |
| `checkFarkas_sound_int` | R1a result | Classical.choice, Quot.sound, propext | `bfabaea03b700e4fbdbac00583014d2ac00f006e8a87d3337f0e23e1500f588d` | `117424f32bd8d7c2eff962928f84c05e0278b4bc9bf2c2c1759362fe838ebf95` (28) |
| `checkFarkas_sound_scaled_posSupport` | R1a result | Classical.choice, Quot.sound, propext | `0580d8f07f26890e0571db182ce71814cff6429390d048978db9d3888d06959f` | `8c37c15eba03c3da877b42134cdd7eaccc701fc15cf3911fe2c6bd932fed9633` (29) |
| `checkFarkas_sound_int_posSupport` | R1a result | Classical.choice, Quot.sound, propext | `48759b648f7ba34e965d1aa36e92035e1e224793a09048ca142883c99f9ac62a` | `7a101f5745c877e19d419cd8601b902c62aa1d468b3ba0ec02fefbb895809b70` (29) |
| `farkas_sound_scaled_of_nonneg_of_lhsVanishes_of_rhsContradicts` | R1c result | Classical.choice, Quot.sound, propext | `03f76c9863efaf75db20890956faa98e43334f37b48e449bc879550eb1bab36a` | `2fb0f84e0a0bd79ae6389ad1daf50d6c2d3b4584e0ae8dd4d5f7187597ebe3f3` (27) |
| `SparseVec.eval_eq_denseDotOn_coeff_of_nodup_of_keys_mem` | R2a result | Quot.sound, propext | `93ff225114bb0e69a3c6f80f47aa10578f01ed3d330618f4f836f95334b607ce` | `7c23f9e4c58109875ba93c91bb772bbcef1d5b928170142c9300ac4d571ad753` (4) |
| `SparseVec.eval_eq_denseDot_coeff_of_keys_lt` | R2a result | Classical.choice, Quot.sound, propext | `65a650da94da9bcc9ddb11eee894bb713c6e85ca0fb15088a6b51e83f3d9a71d` | `fa470dbe7a73e6a39fb3f5f64d43d081eb4a2577de7d52d1f46a986613879e57` (5) |
| `combineLhs_coeff` | R2b result | propext | `9df3d79ba484849a430d1276f6ef8daa2dbabf9e1370d68569886bfd4e80fe18` | `a3b85b414e16c6714af423a220e8332b9b4ac4499d604c0bea261c9bc6394f1d` (10) |
| `combineLhs_eval` | R2b result | propext | `0470a3afa5d4742012308b50eac20ebf4e3778b3d3cc6e0cea1a04c2218cc0ba` | `186797443a83c890d2f260c3c5cacd9770b1e6fc82531e5766b9b7737af0233a` (10) |
| `SparseVec.isZero_iff_coeff_eq_zero` | R2d result | Classical.choice, Quot.sound, propext | `59d78355f7cc7638ab6e7b979cef0f63fb36f51e510b9c24bc78c493e0eb768c` | `dd811bde3b01ec713cb35f7f48274457069ac30415ddd98b227302aec0441b94` (3) |
| `ce_farkas_negative_multiplier` | R1c counterexample; R3a result | (none) | `d08f67b06f95eae31a2b3ca7ed1dae6fd503cd67e67d123c09cecef2f56d48ad` | `e4d034a7193ae7a237977e1096d3dde3b997f618ca2dc42496f442fb5ef78eb9` (31) |
| `ce_farkas_strictness_ignored` | R3b result | (none) | `4b9d7c2f09442699fc5d1526f1de6f889ba641c2d39de56477380913e9d3061c` | `e133c60efaa11117c1ad575d9686f31c0115a1d549661b3b1ccfe6c031628dbd` (33) |
| `ce_farkas_strict_flag_from_zero_weight` | R3b result | (none) | `9e8ed671e92ef4a0dac5001ab3c456fff894f1dba9b0a5fbec48d4f7025ec55f` | `0c1129ddebd8affdec20e4d5a3b36dba30a4c1197003de07f9140760e6456b41` (31) |
| `checkFarkasTightened_sound_int` | R3d result | Classical.choice, Quot.sound, propext | `3db4cea93f82a44a653f515af3af7731ad04f7c00f3384fa47ed9cb7c40719a0` | `48583f327eb7a722a6a78fb1f321cae01afc95caa29a12ede8b4828fad597ab9` (31) |
| `ce_tightening_unsound_over_rat` | R3d counterexample; R3e result | (none) | `833b10c1bf817967ab4eeda3de47329aece2d3f112ff3c8694714cd84411df7c` | `a2c3a03e9133e6f23a294a0af4130b5f79d677c8594b82b9bad3474ea815fe55` (33) |
| `ce_zero_test_index_blind` | R3f result | (none) | `4ff91517f5360f01897dc1ced92619c27581aa590ce17723e80180f0946084fc` | `4d97f71214a81f4f58739e25b0a10978a187a92bf2e1e4c99dddc3aa0a3b374c` (30) |
| `ce_zero_test_first_match` | R3f result | (none) | `3fb1b5194bd734362199aee8bd6b9c96c0ff3716bf4a4ee656297ce13549ba83` | `da0b5e5a124f7af42bd91e361fe05b3eed182758dd6ef576a59e0f261f7a7b63` (32) |
| `ce_zero_test_first_match_dupfree_inputs` | R3f result | (none) | `9681aa6e79ec9dcd80b54ec1637e2c738d1eafcd722dfe2aff43380c2b386ea8` | `da0b5e5a124f7af42bd91e361fe05b3eed182758dd6ef576a59e0f261f7a7b63` (32) |
| `farkas_complete_scaled` | R4a result | Classical.choice, Quot.sound, propext | `d15445716dfcae1616478b8d5d3da933e9faece0f221cc48a2a56f0c32cadcbf` | `7916ce0aeaff1e5a308e410357af6ae0bf3f1373c27bebf7485bbecd0b47370c` (28) |
| `ce_farkas_incomplete_int` | R4b result | Classical.choice, Quot.sound, propext | `ef69fb6307737ce663a146ab91e98d99e3637eeabcd1200a24b3e3b436d2dcc0` | `c590a2ca38f6169e6b265f5870fef2c9f5f0d90b2d0bc6a721692995d9550cee` (29) |
| `cgCut_sound_int_of_nonneg_of_div_pos_of_divisible` | R5a result | Classical.choice, Quot.sound, propext | `0299622d2c54935222e534b5830630fbcb0062f1964b749979acb4e581daedd0` | `5ba6f3b4f3a81e0209719a4ec3dbe92a618952d571114ef754e79318d1906dbf` (32) |
| `cgDerive_sound_int` | R5a result | Classical.choice, Quot.sound, propext | `855565fd6c8ad7344b3e360c393227cab4f87c2fe1ad616017297a05aca7dbe2` | `b96652eb16db341ca5397250f55d1c75b286bcff7044482f1934473e181b95e9` (34) |
| `checkCutCert_sound_int` | R5c result | Classical.choice, Quot.sound, propext | `cf23144cc90bb314523a9103872e8672d3066be0f2057655130a2b3312e521c9` | `8bf3584558922dededc424413fe4504a5bb21a36057910839b05d160ac28e74a` (51) |
| `bv_ule_ult_iff_int_of_inUnsignedRange` | R6a result | Classical.choice, Quot.sound, propext | `1c95c71e4c2acf52334be4605406d61e5d2848948d4f4f805c06d1dc9bf2dae2` | `f4cb53da3e399888f29ec674fd5f6b7fcfb09f948c57fb79f3a77aaa9d2b2305` (11) |
| `bv_sle_slt_iff_int_of_inSignedRange` | R6b result | Classical.choice, Quot.sound, propext | `d6b52b517326d074a999ef92afd821d49a42d8dafe6bc74028953a1162448a53` | `ac6a680140adc3fe68df63571e7062778a4d04efaababda034e2448efe81fe65` (11) |
| `bv_ule_ult_iff_int_of_noWrapU` | R6c result | Classical.choice, Quot.sound, propext | `2ff99cb81d9db01beb7f0e13fdb86a040131553a36cbf7e51e0ad76835d7afe0` | `9e1fd057cc5bd2876e77780e2743c6563b9e1daf83aeae13849fc6c0e738a677` (17) |
| `bv_sle_slt_iff_int_of_noWrapS` | R6c result | Classical.choice, Quot.sound, propext | `a65060adfc2c4998c92bfe4ab68f0f2ec5b10825ca86bd9343c46f684d394cc5` | `4348d05e1a67196cad38608dc3af7055dbe0d308367969a0d1f7cd36331e1d67` (17) |
| `checkFarkas_refutes_bvU_posSupport_of_lhs_lt_of_rhs_nonneg` | R6e result | Classical.choice, Quot.sound, propext | `808f395ad3ca73b3c36b185eb87e3be2812765c70d82f2d8a4fadc225bd773e5` | `1428c2b9e5acedc9cc5474f275a30d4d78234dc75ee5646e3ce09e792f35e4ab` (41) |
| `checkFarkas_refutes_bvS_posSupport_of_lhs_lt_of_rhs_ge` | R6f result | Classical.choice, Quot.sound, propext | `446faadfc4c8216fe30e58b6ba1e98d11f5dd1d584ca230252133b355ba07417` | `f8763fb0d6181aa99a40388200b4c7d72c7ea27633808f2b15cf131d1acd6eee` (41) |
| `ce_bv_reading_mismatch` | R6g result | propext | `49b3af4dc8a17164400e1f8eb73825d6a4d46818237f937eabc275013cb469e9` | `a813edce405478ce986715e1c356d4b737387543c755c15e2dc48f6e4781b13a` (16) |
| `ce_bv_rearrangement_unsound` | R6h result | propext | `6b33f2c958de00e31cd48c750e30632c7c6121bbfae6df9398c30aa6b03f1988` | `0f9893bf7d3c1e017e2b1be87e9421a27995fb945c15c9ce5fa45988dc4a591c` (17) |
| `ce_noWrap_not_needed_for_wrapping_eval` | R6i result | Quot.sound, propext | `9f6079f80e980c4bc3cb7dea6b2a49b63be45795988e24b32eb5b482927718de` | `58084a751c4bcbe77ed4d458d205d45081e5117c7e6d2bace0487f8fd6f42b40` (22) |
| `ce_bv_sle_lhs_out_of_range` | R6b counterexample | propext | `6c67280af7b6f5b713575a5aa0bd2430455bf878f7d17bd65aa9a94add58f6e7` | `2262beab592e7f0f6b2dba5a796cf72c2236e6506e40eda3f3e96f9941b0e9a7` (14) |
| `ce_bv_sle_noWrapS_lhs` | R6c counterexample | propext | `dc00c4152205c0a63fad81b843adabf7a7700f5f1d2790a514ca91f2e0258693` | `023ee9447f6fa8a38193c80da9f7d6bad2226f35168e8024486685ae7aeb3d45` (20) |
| `ce_bv_sle_noWrapS_rhs` | R6c counterexample | propext | `7c3d1f673767608f13e44dd97db2245f602228b28a99012156d390be07bfbfae` | `fe0e77779348ded9bb807f0973e0d861ba67e8b7501dbbc77248f86a2ae93515` (20) |
| `ce_bv_sle_rhs_out_of_range` | R6b counterexample | propext | `d8f78dfce227c87c722f47482f95dfb4e2cd7ef51464714b98ae9ab1fd911de8` | `82d16d52209d27a820634d7152404d7aea6bd27bce3b995b6f04197ae1a7fbd6` (14) |
| `ce_bv_ule_lhs_out_of_range` | R6a counterexample | propext | `c674731f6becf49235cd05ee002aacac34c09270b935caac1232088b4304f9b3` | `52d1ae6dcdd0cd9ff05b275e4f417cc2aae5cdc8394bf91efd26f79520dc6f27` (14) |
| `ce_bv_ule_noWrapU_lhs` | R6c counterexample | propext | `1bdf5d2eb528d595cf44f89a89a7f2bf89ee6da27d99651f996cb42547d04675` | `57450e65c5be6864a38a82695088d53f88c0eb6a42fac6d0164fc548729e5ae1` (20) |
| `ce_bv_ule_noWrapU_rhs` | R6c counterexample | propext | `e556860f588a5dc73888515bfeb3f48f74e58f2bec8159b35ba36857e6c60972` | `69e47f3215347518726e62b938931b5af734dfc946c161535740863048166ecf` (20) |
| `ce_bv_ule_rhs_out_of_range` | R6a counterexample | propext | `c143508962cb6fbbf19d939c085c454c7dd73cb54beba0406f008cac79562960` | `5e43d9789fb55b73900b93b5590eb4ae5f30e43be1f2998f66c23ef1f60ea05a` (14) |
| `ce_cgCut_div_one_unsound_over_rat` | R5a counterexample | (none) | `296666d962068a02c27f5795cd07dc903a77ca24d3a649f49929ed5fd22406a2` | `afa900767bb6dc99fbdc05860098013041648338b6388f887ba8ce305b238d5a` (35) |
| `ce_cgCut_negative_divisor` | R5a counterexample | (none) | `2ccf8000617f0be4b313de1a61d2a6efe26bfb5c64fd8b207145542adad39029` | `ba3dc02226f7f7b570cb29c8563f1111d8f80bf7ee0d042255fc67263737c6ee` (33) |
| `ce_cgCut_negative_multiplier` | R5a counterexample | (none) | `a0d64a4abc955420f83d8164baa352531b9efe3b4e8f4c0c5dbf4a952c31b83f` | `ba3dc02226f7f7b570cb29c8563f1111d8f80bf7ee0d042255fc67263737c6ee` (33) |
| `ce_cgCut_not_divisible` | R5a counterexample | (none) | `c8feab05e562e81c1a6364d762281d1de715e00a581b59c915b0ab6ec9c33f98` | `fada5ca9e67dcf9ea5a11d59736a4841e63ef7f305d36eaa1d57dfaccdeaeca4` (33) |
| `ce_cgCut_point_not_solution` | R5a counterexample | (none) | `65ef5702537f98cd380524b0a65dd1ae9b29238a2ee0ded9a1588373b573e154` | `3a29ef1bed99e6f9dc6456d1c0b4d9fd1ef60666a0ece9b0e6316ab1504fe4f2` (34) |
| `ce_cgCut_unsound_over_rat` | R5a counterexample | (none) | `7df21f0894cc6b30cd766d10feb214b1bbca05323fcabe6a1617c33b90109a93` | `1e95c6e07bee16904e79409484fff4e56536c05dc6207d9c88e74176314f5faa` (34) |
| `ce_cgDerive_rejected` | R5a counterexample | (none) | `efe2ed13894d1dc5ba9ea88c956a25797372e7e1e25a3ed0b155f6fe213985d5` | `9acf914dbcdabae9f2be380e8077e4d40c7fdb054073f571f7078a6f8bacb7ce` (35) |
| `ce_checkCutCert_rejects_satisfiable` | R5c counterexample | (none) | `3ed84d5cd1cd2671211ed49506754c167dd979821ba551261cf6aedf815070df` | `9611b13b6bd34267877f07fdcd1db8dbf38e6fa5f455eb4eccf4b00d6b08dc19` (53) |
| `ce_checkCutCert_unsound_over_rat` | R5c counterexample | (none) | `662cf5569385a69924ddc11666b90d9787e75b18c95de5ec4d47e07f6ea1257a` | `5c86ba0e97436c8d6b62a1cd805d42d628175aa6efeb90213d56d3da902e82b0` (54) |
| `ce_checkFarkasTightened_rejects_satisfiable` | R3d counterexample | (none) | `02b2094034dc6e7b1c2ea43eac2db29cf193c39343ea1526277ce73d0d554d40` | `5cd710f70f7eac8695ad6eddb490d99b69a25c7af6f4ce62df2d46ab4512a52b` (33) |
| `ce_checkFarkas_bvS_lhs_out_of_range` | R6f counterexample | propext | `b78bffb886e8425af787e3ab3dfe976d170fa0475411d7aed56e8e206d036617` | `ecb705784fdc9903bcdc72c52c0a3cd4221a6604e562fdf2133be1d8781c9148` (43) |
| `ce_checkFarkas_bvS_rhs_out_of_range` | R6f counterexample | propext | `93e857fc2644337b2e46993095603f5ceb5c0c2fbe384c2dbb5f0ad952e66491` | `a8f9816bd1b6d5fd53c8207ff5d1a53251ebc596fdf7b8ccdb80fe59a50b302f` (43) |
| `ce_checkFarkas_bvU_lhs_out_of_range` | R6e counterexample | propext | `c2a3892b04fc22dc2ea5d4d14eaa9dcb8d679a13959d4f683ad8c3098ba7e3e8` | `c629856c78dbb2bfb1b17e22d26700078cd8347272ee965b1d92e2fb30a71e5d` (43) |
| `ce_checkFarkas_bvU_rhs_out_of_range` | R6e counterexample | propext | `b6a2a95db7c10899ce0f9a0a1c847122b9338276962345f23794bafd532cbf58` | `8506bfc0db56057016c5ba687bf3a1ec199bb8ab9e18e3f3d9c7ee4df2b2a4ec` (43) |
| `ce_checkFarkas_refutes_bv_rejected` | R6e counterexample; R6f counterexample | propext | `cecfaca1b5d296c8f34304fdac5a4ff7efa83586edb772366a672da46c28a228` | `2ee27d3a7c63c4f5188ba2cea7dbbc78b560e11cc6a8720fce3b9715f53578de` (47) |
| `ce_checkFarkas_rejected_satisfiable` | R1a counterexample | (none) | `6d00692e391f1bff4a5079fe6766c2eade88e863223fbcf6334311a3d794bdcd` | `6bf2b1728fb31485d8ca5c41a0eaef1a798144ec270eaf501f6a4405789f98d1` (33) |
| `ce_eval_eq_denseDotOn_duplicate_index_list` | R2a counterexample | Quot.sound, propext | `8bb6e5da8486396e91ec618485790cb9d8851a5839892d49fb6844e41359ee55` | `7c23f9e4c58109875ba93c91bb772bbcef1d5b928170142c9300ac4d571ad753` (4) |
| `ce_eval_eq_denseDotOn_missing_index` | R2a counterexample | Quot.sound, propext | `5ec7a40517e8218b767a7b85ed00c1fa90374fd93e50b76a5f2c4a5bc47a1269` | `7c23f9e4c58109875ba93c91bb772bbcef1d5b928170142c9300ac4d571ad753` (4) |
| `ce_eval_eq_denseDot_index_out_of_range` | R2a counterexample | (none) | `748ef048d38746ad89889d947f94c2bf7abe2b6437e826904d000092fd6e229a` | `fa470dbe7a73e6a39fb3f5f64d43d081eb4a2577de7d52d1f46a986613879e57` (5) |
| `ce_farkas_complete_feasible_system` | R4a counterexample | Classical.choice, Quot.sound, propext | `500eb04892c4f35b46f86ee0abda28e378e1b5a689805234f7c91153cece79a1` | `9ce8aa2fa763900d256fd17c0ace2065397744af8fa3350b838a563a2afd88c7` (30) |
| `ce_farkas_denominator_zero` | R1a counterexample; R1c counterexample | (none) | `61264b37ae932ac3f336de8c8e7af11ed0491a42644a7842143b7ed309250c05` | `7916ce0aeaff1e5a308e410357af6ae0bf3f1373c27bebf7485bbecd0b47370c` (28) |
| `ce_farkas_lhs_not_vanishing` | R1c counterexample | (none) | `4ef1e8f3e92ed91376bde863c02f052a6e7ccb7ab2110b668657fe32f43f035d` | `fd469e29c645633594502632a515ec2347c1f3ee9823180a7ab0dc007a1a4041` (28) |
| `ce_farkas_rhs_not_contradicting` | R1c counterexample | (none) | `067415216523f66f6b4c3ca0e628f296ab269a1ff9e0f888c5ff22fc0d3ae175` | `ad78071d72770b172cfacd4f44f9d8ddfce897f987287213ba8839631634bd30` (29) |
| `nv_bv_sle_slt_noWrapS` | R6c non-vacuity | (none) | `b21a626e5444f0a19a392db1d706d9743dc487f16860b62b772beaf98368f9b0` | `1d6d8078dd86badac404c7ee2d7d8cb05f451218c5c6c7bb6c825440bb38445c` (18) |
| `nv_bv_sle_slt_transfer` | R6b non-vacuity | propext | `d649f6bd71015119dcaa3ba43dc110b4a635a07604a94a7edf27695aaefc10f8` | `2262beab592e7f0f6b2dba5a796cf72c2236e6506e40eda3f3e96f9941b0e9a7` (14) |
| `nv_bv_ule_ult_noWrapU` | R6c non-vacuity | (none) | `d729ec3ddca3ff5a5f486e0064771aab36e26c6428239c678816be2076203116` | `960d3ebd5e8c6df680ce5e20f18983780b2bdcdd43dbfc85480d226107958375` (18) |
| `nv_bv_ule_ult_transfer` | R6a non-vacuity | propext | `491f8ba748bbebca711e8e35e9dae603b34c5c58b86fc6dc6251c0f50b470b4a` | `52d1ae6dcdd0cd9ff05b275e4f417cc2aae5cdc8394bf91efd26f79520dc6f27` (14) |
| `nv_cgCut_sound_int` | R5a non-vacuity | (none) | `ca2ff4a982268e3b99961163c06cc6c96949b0273f88f7b954697384f1cfadca` | `4d4d2e1ec9d35dcd4c83e03d3ff57d336e6740d23f3dbbbc7548c38e23c98f8e` (36) |
| `nv_checkCutCert_sound_int` | R4b positive control; R5c non-vacuity | (none) | `c7f541c72ed0e0d50c41d0dd8c2fbd4f8509ba608baf80aa814fe4321cb65608` | `31cdbe75b3df3cff030c278e9ccd0c990e5a0bf037cdc2cbcaf9c7a2e1affaf6` (48) |
| `nv_checkFarkasTightened` | R3d non-vacuity | (none) | `9c1040daa1d80cd4e47c5601cb33d7141165c690963cb897ba6ae127ab884155` | `0b6d27b923eca0cf497abf0835f8a1fbc665bdd6cd62701b7fe29ea3bba9b431` (27) |
| `nv_checkFarkas_refutes_bvS` | R6f non-vacuity | (none) | `27337f1e1df98e7cc71faafd310403b45121ba61895fb9795dab070134f1c44b` | `f39fb608741c458730264d6a44bfc372ece97c7bfd78faba3279721af9e1530d` (39) |
| `nv_checkFarkas_refutes_bvU` | R6e non-vacuity | (none) | `99ef88fcdb3e7490740862b4edeb36e1a91a7b5b6ca54e13141b8718925ffba5` | `469b1257089a0276f049105de3ec42cea0a73c63de4fed4fe71f60f883c8bf3d` (39) |
| `nv_checkFarkas_refutes_bv_two_sided` | R6e non-vacuity; R6f non-vacuity | (none) | `3b9992e2e9612f6fd0ea02287f65268be8859d37be1fcc98f253938eabc644de` | `676e773f028f871c008dfc12fb20aa619b7b7c896b5c30a36a442080c2a8d0c9` (41) |
| `nv_checkFarkas_sound` | R1a non-vacuity | (none) | `175ee19b9abd92a785889f4bef447608365106887760f4deae84d8065397b9b8` | `2e3de4fe1cd591b482c582efb84231a074987396c0a6720c50378bd3bd9f0597` (25) |
| `nv_checkFarkas_sound_posSupport` | R1a non-vacuity | (none) | `a4ecda5a9700b6f3eda93449561f80ee0305ae507374787e6ec4c483b54dbdb6` | `6a384d406b1a2df517195da9408eccddb1c76f93512a34fd28ca3052ec9a92a9` (25) |
| `nv_checkFarkas_sound_scaled` | R1a non-vacuity | (none) | `bf0da2faab654f1c06a64ac4c8ee1846384efe917c4eea8e2c275343545654c0` | `2e3de4fe1cd591b482c582efb84231a074987396c0a6720c50378bd3bd9f0597` (25) |
| `nv_combineLhs_coeff` | R2b non-vacuity | (none) | `49e1dccecd84d4fdca372cd17c17925943947e85f3c7b158a4255126c586a6ee` | `e35612c114f3a97a487b2eaaa4692f4c58af53ac330fa4a4b9f3016ee81f41d5` (11) |
| `nv_combineLhs_eval` | R2b non-vacuity | (none) | `45114c2d3077546be13ad20ac05eb7ac3b0f1d29323c3e6c558fa16ba674e164` | `160cae289b341c3a15c4987248e779cb32414034157d59b5e8f0f938ff623f57` (12) |
| `nv_eval_eq_denseDot` | R2a non-vacuity | (none) | `9c3a4714a77b71a134e6edac6e1e98cdd165b447670951d78c4552221a64390e` | `fa470dbe7a73e6a39fb3f5f64d43d081eb4a2577de7d52d1f46a986613879e57` (5) |
| `nv_eval_eq_denseDotOn` | R2a non-vacuity | Quot.sound, propext | `60dc6338366cdc2ae3fde06ccf0b04e26f0b42cea262424ace4314e1c8fe2abb` | `7c23f9e4c58109875ba93c91bb772bbcef1d5b928170142c9300ac4d571ad753` (4) |
| `nv_farkas_complete_scaled` | R4a non-vacuity | Classical.choice, Quot.sound, propext | `1f047efbe2f99dc8911f3bf9c5d82c3da44b1eec5f815758d8204ea2a5b15815` | `d42fd1ac36bb5cd488849e3b7f9804d7e161ae2d398f0b8f45f7399b1fba575d` (30) |
| `nv_farkas_sound_structured` | R1c non-vacuity | (none) | `52a393e939f790ba6c3a801b47b63a163e98ebeaebaa4047a3415b4dbaa81d34` | `e67ca3861f02e19f636253e91a35e37d8b2544d9f57eacc75f9d499e79995bc1` (23) |
| `nv_isZero_iff` | R2d non-vacuity | (none) | `0a5826528ad8a040233fe4c2b9eb1e0ac73a03ec06e7e180e31f113e22b2820b` | `dd811bde3b01ec713cb35f7f48274457069ac30415ddd98b227302aec0441b94` (3) |
| `sysHalf_refuted_by_case_split` | R4b positive control | Quot.sound, propext | `76799bffce2bc0265a25044a0df4c9780d1e3e47ecba3506822f0067aa89d6b9` | `b39213a37db4e16d8d1154e06e12adada872ef415b035ee3d81dcf61b613b40e` (24) |

### Primary sources and prior art

Every citation used by a card, as recorded in `results.json` (each entry states what was checked: the source itself, its metadata, or its table of contents). Lean core, Mathlib, Rocq and CompCert sources are cited at the exact commit given in the entry.

- Alan J. Hoffman, Joseph B. Kruskal, 'Integral boundary points of convex polyhedra', in Linear Inequalities and Related Systems (H. W. Kuhn, A. W. Tucker, eds.), Annals of Mathematics Studies 38, Princeton University Press, 1956, pp. 223-246 (total unimodularity and integral polyhedra; bibliographic record via secondary sources, full text not read).
- Alexander Schrijver, 'On cutting planes', in Combinatorics 79, Part II, Annals of Discrete Mathematics, Vol. 9, North-Holland, 1980, pp. 291-296, DOI 10.1016/S0167-5060(08)70085-2 (extends the finiteness of the cutting-plane hierarchy to arbitrary, possibly unbounded, rational polyhedra; metadata via Crossref, volume number via secondary records, full text not read).
- Alexander Schrijver, Theory of Linear and Integer Programming, John Wiley & Sons, 1986 (paperback reprint 1998, ISBN 978-0-471-98232-6; chapter list checked on the publisher's page): Chapter 7 'Fundamental concepts and results on polyhedra, linear inequalities, and linear programming' (Farkas' lemma and its variants), Chapter 12 'Primal-dual, elimination, and relaxation methods' (includes elimination), Chapter 23 'Cutting planes'. Specific theorem numbers were not checked against the book.
- Axel Simon, Andy King, 'Taming the Wrapping of Integer Arithmetic', SAS 2007, LNCS 4634, Springer, 2007, pp. 121-136 (pages per Crossref), DOI 10.1007/978-3-540-74061-2_8 (polyhedral analysis of programs over wrapping fixed-width integers; metadata via Crossref, full text not read).
- Bruno Andreotti, Hanna Lachnitt, Haniel Barbosa, 'Carcara: An Efficient Proof Checker and Elaborator for SMT Proofs in the Alethe Format', TACAS 2023, LNCS 13993, Springer, 2023, pp. 367-386, DOI 10.1007/978-3-031-30823-9_19 (an independent checker for Alethe proofs; metadata checked via Crossref, full text not read).
- Bruno Dutertre and Leonardo de Moura, 'A Fast Linear-Arithmetic Solver for DPLL(T)', CAV 2006, LNCS 4144, pp. 81-94, DOI 10.1007/11817963_11 (simplex-based solver for DPLL(T); strict inequalities are handled with bounds over rationals extended by a symbolic infinitesimal delta, e.g. x < b as x <= b - delta, rather than by a strictness flag on Farkas combinations; metadata via Crossref, the delta mechanism confirmed from secondary descriptions, full text not read).
- CompCert, AbsInt/CompCert commit 99627f88db37a7c98e03775741e5048b981d2032, lib/Integers.v: unsigned_repr (0 <= z <= max_unsigned -> unsigned (repr z) = z), signed_repr (min_signed <= z <= max_signed -> signed (repr z) = z), add_unsigned, add_signed (wrapping addition as repr of the integer sum), and the comparisons ltu / lt (Coq mechanization of machine-integer-to-integer transfer).
- Filip Marić, Mirko Spasić, René Thiemann, 'An Incremental Simplex Algorithm with Unsatisfiable Core Generation', Archive of Formal Proofs, August 24, 2018, https://isa-afp.org/entries/Simplex.html (Isabelle/HOL incremental simplex with unsatisfiable cores; its session includes theories Abstract_Linear_Poly and Linear_Poly_Maps, a representation of linear polynomials; contents of those theories not examined beyond their names).
- Frédéric Besson, 'Fast Reflexive Arithmetic Tactics the Linear Case and Beyond', in Types for Proofs and Programs (TYPES 2006), LNCS 4502, Springer, 2007, pp. 48-62, DOI 10.1007/978-3-540-74464-1_4 (abstract: certificates of infeasibility for quantifier-free linear and non-linear integer arithmetic are produced by off-the-shelf algorithms and validated in Coq by reflexive checkers; full text not read).
- Haniel Barbosa, Mathias Fleury, Pascal Fontaine, Hans-Jörg Schurr, 'The Alethe Proof Format: An Evolving Specification and Reference', online specification https://verit.gitlabpages.uliege.be/alethe/specification.pdf (typeset March 31, 2026; accessed 2026-11-20), rule la_generic: one rational coefficient per literal, inequalities multiplied by the coefficient's absolute value; step 4 strengthens each individual (negated, normalized) input literal when all its variables are integer-sorted (a strict bound > d becomes >= d + 1, a non-integer bound is rounded), before the multiplication; the specification remarks that after strengthening the conjunction is unsatisfiable 'even if integer variables are assumed to be real variables'; the sum must be a trivial contradiction. The specification has no Chvátal–Gomory cutting-plane rule.
- Joel Beeren, Matthew Fernandez, Xin Gao, Gerwin Klein, Rafal Kolanski, Japheth Lim, Corey Lewis, Daniel Matichuk, Thomas Sewell, 'Finite Machine Word Library', Archive of Formal Proofs, June 9, 2016, https://isa-afp.org/entries/Word_Lib.html (Isabelle/HOL library of fixed-width machine words, including signed words and an extensive library of properties of generic fixed-width words).
- Jorge A. Navas, Peter Schachte, Harald Søndergaard, Peter J. Stuckey, 'Signedness-Agnostic Program Analysis: Precise Integer Bounds for Low-Level Code', APLAS 2012, LNCS 7705, Springer, 2012, pp. 115-130, DOI 10.1007/978-3-642-35182-2_9 (integer bounds analysis for low-level code where signedness is not known; metadata via Crossref, full text not read).
- Julius Farkas, 'Theorie der einfachen Ungleichungen', Journal für die reine und angewandte Mathematik 124 (1902), pp. 1-27, DOI 10.1515/crll.1902.124.1 (non-strict linear inequalities).
- Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Data/BitVec/Lemmas.lean: BitVec.ofInt_add, BitVec.ofInt_mul (BitVec.ofInt w is additive and multiplicative), BitVec.toNat_ofInt ((ofInt n i).toNat = (i % 2^n).toNat), BitVec.toInt_ofInt ((ofInt n i).toInt = i.bmod (2^n)), BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.sle_eq_decide, BitVec.slt_eq_decide.
- Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Omega/Constraint.lean and src/Init/Omega/Coeffs.lean: `Lean.Omega.Constraint.div` divides a two-sided bound constraint by a natural number k, rounding the upper bound down and the lower bound up; `Lean.Omega.Constraint.div_sat` proves the divided constraint holds at t / k when k ≠ 0 divides t, and `div_sat'` uses the gcd of the coefficients (integer GCD tightening inside omega's proof-producing procedure); Coeffs.lean notes that omega uses a dense coefficient list and that a sparse `AssocList Nat Int` representation is an alternative.
- Lean 4 core, leanprover/lean4 tag v4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Init/Tactics.lean: the `omega` docstring ('not yet a full decision procedure (no "dark" or "grey" shadows)'); `bv_omega` ('omega with an additional preprocessor that turns statements about BitVec into statements about Nat', via simp lemmas tagged bitvec_to_nat); `bv_decide` (obtains a proof from an external SAT solver and verifies it inside Lean; LRAT proofs per the `bv_check` docstring).
- LLVM Language Reference Manual, https://llvm.org/docs/LangRef.html (accessed 2026-11-20), poison-value examples: `sub nuw i32 0, 1` 'Results in a poison value' (with the nuw flag an unsigned wrap of one operation poisons the result, unlike the wrapping semantics modeled here).
- Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Analysis/Convex/Cone/Dual.lean: Farkas' lemma in geometric form for proper cones in locally convex real topological vector spaces (ProperCone.hyperplane_separation, ProperCone.hyperplane_separation_point); real-valued, not a certificate checker.
- Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Datatypes.lean: `abbrev Linexp : Type := List (Nat × Int)`, a sparse linear form as an association list; its docstring states that some functions assume each index occurs at most once and that the list is sorted in decreasing index order, an invariant 'not enforced by the type' but preserved by the operations (Linexp.get stops at the first smaller key).
- Mathlib, leanprover-community/mathlib4 commit b679ac024dccdf39b1be683d5890c072b58ae8d0, Mathlib/Tactic/Linarith/Frontend.lean module docstring: an untrusted oracle (simplex by default, Fourier–Motzkin optional) searches for natural-number coefficients k_i with sum k_i t_i = 0 and k_i > 0 for at least one strict hypothesis; the certificate is checked by building a proof term (not by reflection); over Int, linarith 'will fail to prove False on some unsatisfiable problems'.
- Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, John Regehr, 'Alive2: bounded translation validation for LLVM', PLDI 2021, ACM, pp. 65-79, DOI 10.1145/3453483.3454030 (translation validation for LLVM IR, including its poison semantics; metadata via Crossref, full text not read).
- Ralph Bottesch, Alban Reynaud, René Thiemann, 'Linear Inequalities', Archive of Formal Proofs, June 21, 2019, https://isa-afp.org/entries/Linear_Inequalities.html (Isabelle/HOL: fundamental theorem of linear inequalities, Farkas' lemma, Carathéodory's theorem, Farkas-Minkowsky-Weyl theorem, decomposition theorem of polyhedra, Meyer's integer-hull result).
- Ralph Bottesch, Max W. Haslbeck, René Thiemann, 'Farkas' Lemma and Motzkin's Transposition Theorem', Archive of Formal Proofs, January 17, 2019, https://isa-afp.org/entries/Farkas.html (Isabelle/HOL, via a verified simplex algorithm: a set of linear constraints is unsatisfiable iff some linear combination of them evaluates to a trivially unsatisfiable inequality; covers mixed strict/non-strict systems).
- Ralph E. Gomory, 'Outline of an algorithm for integer solutions to linear programs', Bulletin of the American Mathematical Society 64(5) (1958), pp. 275-278, DOI 10.1090/S0002-9904-1958-10224-4.
- René Thiemann (with contributions from Manuel Eberl), 'A Preprocessor for Linear Diophantine Equalities and Inequalities', Archive of Formal Proofs, June 13, 2024, https://isa-afp.org/entries/Linear_Diophantine_Preprocessor.html (abstract: Pugh's technique of tightening linear inequalities, detection of implicit equalities, and elimination of equations; the result either detects unsatisfiability over Z or returns equisatisfiable inequalities; session theories include Linear_Polynomial, Linear_Polynomial_Impl, Diophantine_Tightening).
- René Thiemann, 'Duality of Linear Programming', Archive of Formal Proofs, February 3, 2022, https://isa-afp.org/entries/LP_Duality.html (weak and strong LP duality, based on the formalization of Farkas' lemma in 'Linear Inequalities').
- Rocq Stdlib, rocq-prover/stdlib commit f50ccefc570f6b815874df96bb3b872611cfaf0e, theories/micromega/ZMicromega.v: certificate type ZArithProof with constructors DoneProof, RatProof, CutProof, SplitProof, deprecated_EnumProof, ExProof; genCuttingPlane divides a constraint by the gcd of its coefficients and rounds the constant, first rewriting a strict e > 0 as e - 1 >= 0; ZChecker_sound proves the checker sound in Coq/Rocq.
- Theodore S. Motzkin, 'Beiträge zur Theorie der linearen Ungleichungen', doctoral dissertation, University of Basel; printed by Azriel, Jerusalem, 1936 (the transposition theorem for systems mixing strict and non-strict inequalities; bibliographic record checked via secondary sources, the German text was not read).
- Vašek Chvátal, 'Edmonds polytopes and a hierarchy of combinatorial problems', Discrete Mathematics 4(4) (1973), pp. 305-337, DOI 10.1016/0012-365X(73)90167-2 (cutting-plane hierarchy; finitely many rounds of cuts reach the integer hull for bounded rational polytopes).
- William Pugh, 'A practical algorithm for exact array dependence analysis', Communications of the ACM 35(8) (1992), pp. 102-114, DOI 10.1145/135226.135233 (the Omega test: integer tightening and exact projection with dark shadows and splintering; metadata via Crossref, full text not read).
- Xavier Allamigeon, Ricardo D. Katz, 'A Formalization of Convex Polyhedra Based on the Simplex Method', Journal of Automated Reasoning 63 (2019), pp. 323-345, DOI 10.1007/s10817-018-9477-1 (Coq formalization of convex polyhedra via the simplex method; metadata checked via Crossref, full text not read).
- Yoni Zohar, Ahmed Irfan, Makai Mann, Aina Niemetz, Andres Nötzli, Mathias Preiner, Andrew Reynolds, Clark Barrett, Cesare Tinelli, 'Bit-Precise Reasoning via Int-Blasting', VMCAI 2022, LNCS 13182, Springer, 2022, pp. 496-518, DOI 10.1007/978-3-030-94583-1_24 (translating bit-vector constraints into integer arithmetic in an SMT solver; metadata via Crossref, full text not read).

The subjects in `REPORT.json` are identified by DOI where Crossref resolves one (Farkas 1902, Gomory 1958, Chvátal 1973; checked 2026-11-20). Motzkin's 1936 dissertation has no DOI that could be found; it is identified by its Open Library catalog record `https://openlibrary.org/works/OL39347129W` (title, author, Jerusalem, Buchdr. Azriel, 1936; checked 2026-11-20).

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

The script copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, scans the Lean sources for `sorry`, `admit`, `native_decide` and `axiom` declarations, computes the axioms of every library declaration with `Lean.collectAxioms` (only `propext`, `Classical.choice`, `Quot.sound` are accepted), and recomputes, for every name referenced by `results.json` and every name in `audit/statements.json`, the SHA-256 of the statement (Lean `repr` of the theorem's type) and of its definition closure (one line `name : type := value` for every package constant reachable from the statement, sorted and joined with newlines; theorem bodies are excluded). It prints `REVALIDATED` and exits with status 0 only if every check passes.

The same audit without the script, using only `elan`, `lake` and `python3` (`lean/RevalidationAudit.lean` is outside the `ToyFarkas` library target and lists every card-referenced name):

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/farkas_audit.txt
cd ..
python3 - <<'EOF'
import hashlib, json, re
audit = json.loads(re.search(r'REVALIDATION_AUDIT_JSON (\{.*\})', open('/tmp/farkas_audit.txt').read()).group(1))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [d['name'] for d in audit['decls'] if set(d['axioms']) - allowed]
rec = json.load(open('audit/statements.json'))['statements']
drift = []
for s in audit['stmts']:
    got = {'statement_sha256': hashlib.sha256(s['type_repr'].encode()).hexdigest(),
           'closure_sha256': hashlib.sha256('\n'.join(s['closure']).encode()).hexdigest(),
           'closure_size': len(s['closure'])}
    if s.get('missing') or rec.get(s['name']) != got:
        drift.append(s['name'])
print('axiom violations:', bad)
print('hash mismatches:', drift)
print('names checked:', len(audit['stmts']), 'of', len(rec), 'recorded')
EOF
```

Both lists must be empty and all 84 recorded names must be checked. A passing run re-establishes the kernel checks and that the statements and the definitions they depend on are unchanged; it does not re-establish the modeling bridges under Applicability, which must be re-argued for any real checker, solver, or machine-integer semantics.

To revalidate against a newer Lean release, change `lean/lean-toolchain` and rerun the commands above. A hash mismatch then indicates a change in how Lean elaborates or prints a statement or definition, which must be inspected by hand (compare the printed statements under Findings) before the cards are relied on for that release.
