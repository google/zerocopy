# Junk values, guarded arithmetic, and the human reading of total operations: a Lean 4 toy model

## Summary

This package formalizes, in Lean 4 with the core library only, a toy arithmetic language over `Nat` and `Int` with two readings. In the **total reading** every partial operation (natural subtraction below zero, division, remainder, `Int.toNat` of a negative integer) has its exact value on a fixed domain and takes a *junk value* from a record `J : Junk` outside it; Lean's own operators are the record `leanJ`. In the **human reading** the same operations are undefined outside their domains, terms evaluate into `Option Int`, and formulas take three truth values (`some true`, `some false`, `none` for undefined) under strong Kleene or sequential connectives and under one of two readings of natural subtraction (`partialNat`: undefined below zero; `intValued`: evaluated in the integers). The package proves when the two readings agree, a decidable guard discipline on which they provably coincide, and a catalogue of concrete Lean-core traps.

**Notation used throughout.** Every arithmetic expression printed in this report outside a verbatim Lean quote shows its types. A leading binder list names the variables and their type: `(a b : Nat), a - b + b = a` is the formula `a - b + b = a` over natural-number variables `a` and `b`, with Lean's truncated subtraction; `(x : Int) / 0 = 0` uses integer division, and `(2 : Nat) - 3 < 0` differs from `(2 : Int) - 3 < 0`. Each named toy formula (`fSubAddCancel`, `fDivZero`, ...) has a kernel-checked Lean reading with explicit types (`ToyJunk/Readings.lean`, quoted under Findings, *Named formulas and their Lean readings*). Plain claims and non-claims are quoted from `results.json`, which writes connectives in ASCII (`<=`, `->`, `!=`, `|` for divisibility, `AND`, `OR`, `NOT`). *Lean value* means the total value under `leanJ`; *human value* means the value of `hEval`; *human-valid* means defined and true at every environment; *junk-independent* means the total value does not depend on the junk record.

**Results** (one sentence each, with the key hypotheses; the cards under Findings carry the exact statements):

- **R0** (`lean_reading_is_junk_record_leanJ`, theorem): For every environment and toy term, the total value under the junk record `leanJ` equals the value computed with Lean's core operators (`Nat` subtraction, division and remainder, `Int.ediv` and `Int.emod` as `Int` `/` and `%`, `Int.toNat`, the cast `Nat → Int`), and for every toy formula φ and environment ρ, `evalJ leanJ φ ρ = true` iff the Lean proposition `leanEvalF φ ρ` holds.
- **R1** (`agreement_where_defined_partialNat`, theorem): Under the `partialNat` reading, for either connective semantics, every junk record, toy formula φ, environment ρ and Boolean b: if the human value of φ at ρ is defined and equal to b, then the total value of φ at ρ equals b; so under `partialNat` no toy formula is human-false and Lean-true, or human-true and Lean-false, at any environment.
- **R2** (`definedEverywhere_implies_junkIndependent`, theorem): Under `partialNat`, for either connective semantics, a toy formula whose human value is defined at every environment is junk-independent.
- **R3** (`junkIndependent_does_not_imply_defined`, counterexample): Junk independence implies neither definedness nor human validity: for each connective semantics, `(a b : Nat), (a - b) * 0 = 0` is junk-independent but undefined under `partialNat` at `a = 0, b = 1`; for each connective semantics and reading, `(x : Int) / 0 = x / 0` and `(x : Int) / 0 = 0 ∨ ¬ (x / 0 = 0)` are Lean-valid, junk-independent and human-undefined at every environment.
- **R4** (`agreement_does_not_imply_junkIndependent_or_definedness`, counterexample): For each connective semantics, `(a b : Nat), a - b ≤ a` agrees with the `partialNat` human reading wherever that reading is defined, for every junk record, and is Lean-valid, yet it is junk-dependent and not defined at every environment.
- **R5** (`validity_transfer_partialNat`, theorem): Under `partialNat`, for either connective semantics and every toy formula φ: if φ is human-valid then φ is Lean-valid; and if the human value of φ is defined at every environment, then φ is Lean-valid iff it is human-valid.
- **R6** (`guarded_fragment_conservativity`, theorem): For every toy formula accepted by the decidable syntactic guard checker `guarded`, every connective semantics, reading of natural subtraction, junk record and environment, the human value is defined and equals the total value; in particular every accepted formula is defined everywhere and junk-independent.
- **R7** (`guarded_validity_transfer`, theorem): For every connective semantics, reading and toy formula accepted by `guarded`, the formula is Lean-valid iff it is human-valid; for instance `(a b : Nat), b ≤ a → a - b + b = a` is accepted, Lean-valid and human-valid.
- **R8** (`guard_checker_incomplete`, counterexample): The checker `guarded` rejects formulas that are well behaved: `(a b : Nat), (a - b) * 0 = 0`, which is junk-independent; for each connective semantics, `(a b : Nat), (0 : Nat) ≤ 0 ∨ a - b = 0`, which is human-valid under `partialNat`; for each connective semantics and reading, `(a b : Nat), ¬ (b ≤ a) ∨ a - b + b = a` and `(a b : Nat), b = 0 ∨ a % b < b`, which are human-valid; and, under strong Kleene connectives and either reading, `(a b : Nat), a - b + b = a ∧ b ≤ a`, which is defined at every environment.
- **R9** (`trap_truncated_subtraction`, counterexample): For each connective semantics, `(0 : Nat) - 1 + 1 = 0` is Lean-false, undefined under `partialNat` and true under `intValued`, and `(0 : Nat) - 1 ≤ 0` is Lean-true, false under the junk record `oneJ` and undefined under `partialNat`.
- **R10** (`trap_division_by_zero`, counterexample): For each connective semantics and reading, `(5 : Int) / 0 = 0` and `(5 : Nat) % 0 = 5` are Lean-true, false under `oneJ` and human-undefined; in Lean core `(5 : Int) / 0 = 0`, `(5 : Nat) / 0 = 0`, `(5 : Nat) % 0 = 5` and `(5 : Int) % 0 = 5`.
- **R11** (`trap_floor_division_read_as_exact`, counterexample): For each connective semantics and reading, `(7 : Nat) / 2 * 2 = 7` is Lean-false (`(7 : Nat) / 2 * 2 = 6`) and human-undefined, because the human reading reads `/` as exact division.
- **R12** (`trap_integer_rounding`, counterexample): Lean's default `Int` `/` and `%` are `Int.ediv` and `Int.emod`; at `(-7, 2)` the Euclidean, truncating and flooring quotients are `-4, -3, -4` and the remainders `1, -1, 1`, at `(7, -2)` the quotients are `-3, -3, -4` and the remainders `1, 1, -1`; in the toy, for each connective semantics and reading, `(-7 : Int) / 2 = -4` and `(-7 : Int) % 2 = 1` hold for `leanJ` and `floorJ` and fail for `truncJ`, `(7 : Int) / (-2) = -3` and `(7 : Int) % (-2) = 1` hold for `leanJ` and `truncJ` and fail for `floorJ`, and all four are human-undefined.
- **R13** (`rounding_conventions_agree_on_domains`, theorem): For all `n d : Int`: if `d ∣ n` then `Int.tdiv n d = n / d` and `Int.fdiv n d = n / d`; if `0 ≤ n` and `0 ≤ d` then `Int.tmod n d = n % d` and `Int.fmod n d = n % d`; in particular the three conventions agree on the domains `DivDom` and `ModDom`.
- **R14** (`trap_fin_wraparound`, counterexample): In Lean core, `(3 : Fin 5) + 4 = 2`, `((2 : Fin 5) - 3).val = 4`, `(7 : Fin 5).val = 2` and `(4 : Fin 3).val = 1`, so `(1 : Fin 3).val + (4 : Fin 3).val < 3` holds while `((1 : Fin 3) + 4).val ≠ (1 + 4 : Nat)`.
- **R15** (`trap_cast_placement_and_toNat`, counterexample): For each connective semantics, `(((0 : Nat) - 1 : Nat) : Int) = ((0 : Nat) : Int) - ((1 : Nat) : Int)` is Lean-false, undefined under `partialNat` and true under `intValued`; at every environment the Lean value of `(a b : Nat), ((a - b : Nat) : Int) = (a : Int) - (b : Int)` is `decide (b ≤ a)`; in Lean core that cast equation holds iff `b ≤ a`; and for each connective semantics and reading, `(-3 : Int).toNat = 0` is Lean-true, false under `oneJ` and human-undefined.
- **R16** (`trap_numeral_typing`, counterexample): For each connective semantics and reading, `(2 : Nat) - 3 < 0` is Lean-false and `(2 : Int) - 3 < 0` is Lean-true; the human value of the `Int` formula is true, and that of the `Nat` formula is undefined under `partialNat` and true under `intValued`; in Lean core the unannotated `2 - 3` elaborates at `Nat`, so the unannotated `¬ (2 - 3 < 0)` and `2 - 3 = 0`, which elaborate as `¬ ((2 : Nat) - 3 < 0)` and `(2 : Nat) - 3 = 0`, are provable.
- **R17** (`guarded_fragment_not_closed_under_lean_equivalences`, impossibility): The set of formulas accepted by `guarded` is closed neither under commuting a conjunction nor under contraposition: with `a b : Nat`, `b ≤ a ∧ a - b + b = a` and `b ≤ a → a - b + b = a` are accepted while `a - b + b = a ∧ b ≤ a` and `¬ (a - b + b = a) → ¬ (b ≤ a)` are rejected, although each pair has the same total value under every junk record at every environment.
- **R18** (`kleene_definedness_closed_under_comm_and_contraposition`, theorem): Under strong Kleene connectives, for either reading, all toy formulas φ and ψ and every environment, `φ ∧ ψ` and `ψ ∧ φ` have the same human value, as do `φ → ψ` and `¬ ψ → ¬ φ`; hence definedness at every environment is preserved by both rewrites.
- **R19** (`sequential_connectives_break_closure`, counterexample): With sequential connectives, definedness at every environment is preserved neither by commuting a conjunction nor by contraposition: under `partialNat` for `(a b : Nat), b ≤ a ∧ a - b + b = a` and `(a b : Nat), b ≤ a → a - b + b = a`, and under either reading for `(x : Int), 0 ≤ x ∧ x.toNat = x.toNat` and `(x : Int), 0 ≤ x → x.toNat = x.toNat`.
- **R20** (`restate_signed_difference_with_casts`, theorem): For every connective semantics, with the `intValued` reading fixed: for every junk record and environment the human value of the `Nat` term `a - b` is defined and equals the total value of `(a : Int) - (b : Int)`; `(a b : Nat), (a : Int) - (b : Int) + (b : Int) = (a : Int)` is accepted by `guarded` and Lean-valid; and the human value of `(a b : Nat), a - b + b = a` is defined and equals the total value of that cast formula.
- **R21** (`restate_exact_division_with_nonzero_divisor_guard`, theorem): For every connective semantics and reading, `(a b : Nat), b ∣ a → a / b * b = a` is Lean-valid and rejected by `guarded`, and its human value is undefined if `a = 0` and `b = 0` and true otherwise; adding the premise `¬ (b = 0)` gives a formula that is accepted, Lean-valid and human-valid; and `(a b : Nat), ¬ (a = 0) → b ∣ a → a / b * b = a` is rejected yet Lean-valid and human-valid.
- **R22** (`named_integer_division_characterization`, characterization): For all `a b : Int`, with `/` and `%` Lean's default Euclidean operators: `Int.tdiv a b = a / b` iff `0 ≤ a ∨ b ∣ a ∨ b = 0`; `Int.fdiv a b = a / b` iff `0 ≤ b ∨ b ∣ a`; `Int.tmod a b = a % b` iff `0 ≤ a ∨ b ∣ a ∨ b = 0`; `Int.fmod a b = a % b` iff `0 ≤ b ∨ b ∣ a`.
- **R23** (`restate_fin_addition_with_bound`, theorem): For every `n : Nat` and all `a b : Fin n`, if `a.val + b.val < n` then `(a + b).val = a.val + b.val` (addition of natural numbers on the right).
- **R24** (`bounded_quantifier_guard_rule`, theorem): For every fact list Γ, natural variable `x`, bound term `t` that does not mention `x`, and body φ: `ballNat x t φ` (that is, `∀ x : Nat, x ≤ t → φ` for the natural variable `x`) is accepted relative to Γ iff `t` is accepted by Γ and φ is accepted by the facts of Γ that do not mention `x` together with `x ≤ t`; for instance `∀ a b : Nat, b ≤ a → a - b + b = a` is accepted, Lean-valid and human-valid for every connective semantics and reading.
- **R25** (`flips_under_intValued`, counterexample): Under the `intValued` reading, for each connective semantics, `∀ a : Nat, 0 ≤ a - 1` is human-false and Lean-true, and `∀ a b : Nat, a - b + b = a` is human-true and Lean-false.
- **R26** (`undefined_to_lean_truth_under_partialNat`, counterexample): Under `partialNat`, for each connective semantics, `∀ a : Nat, a - (a + 1) = 0` is human-undefined, Lean-true and false under `oneJ`, and `∃ a : Nat, ¬ (a - (a + 1) = 0)` is human-undefined, Lean-false and true under `oneJ`; for each connective semantics and reading, `(1 : Nat) / 2 = 0` and `∀ n : Nat, 2 < n → 1 / n = 0` are human-undefined and Lean-true.

What each result does **not** show is listed under Boundaries, *Non-claims*, result by result; the most important limits are that the human reading treats `/` as exact division (an inexact quotient such as `(7 : Nat) / 2` is undefined, not `3`), that the language is a toy with no translation from Lean source statements, and that agreement fails under the `intValued` reading of natural subtraction. Where a result's Lean value rests on a truncating operation (truncated `Nat` subtraction, floor division, division by zero returning `0`, `Int.toNat` sending negatives to `0`), the trap is relative to the reader's convention: readers bring integer, wrapping or panicking semantics, not the absence of a convention, and Lean's truncated subtraction differs from each of them below zero (Applicability, gap 8; the per-result non-claims).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity.** This is a toy model. The language `Term : Srt → Type` is intrinsically typed over two sorts, `Nat` and `Int`, with literals, variables, `+`, `-`, `*`, `/`, `%`, an explicit cast `Nat → Int` and `Int.toNat`; formulas have the atoms `=`, `≤`, `<` and divisibility, the connectives `¬`, `∧`, `∨`, `→`, and quantifiers over `Nat` and over `Int`. The language models the *elaborated* form of a statement: every cast is an explicit node and every literal carries its sort.

What the definitions are meant to capture:

- **Lean's reading.** The total semantics at the junk record `leanJ` is exactly Lean core's arithmetic on `Nat` and `Int` (`evalT_leanJ`, `evalJ_leanJ_iff`): truncated `Nat` subtraction, `Nat` division and remainder with `(n : Nat) / 0 = 0` and `(n : Nat) % 0 = n`, `Int` division and remainder by `Int.ediv` and `Int.emod`, and `Int.toNat` sending negatives to `0`. Other junk records (`truncJ`, `floorJ`, `oneJ`) are test devices that vary the out-of-domain values.
- **The human reading.** An exact reading of the same symbols: subtraction, division and remainder are partial and evaluated in the integers, and a formula is three-valued.

Known gaps and modeling choices (each one bounds every result below):

1. **Division is read as exact division.** The human domain of `/` is `DivDom n d := d ≠ 0 ∧ d ∣ n` (on `Int` values), so an inexact quotient with a nonzero divisor, such as `(7 : Nat) / 2`, is human-undefined and its total value comes from the junk record (`inexact_division_is_junk`). The human domain of `%` is `ModDom n d := 0 ≤ n ∧ 0 < d`, which contains inexact cases such as `(7 : Nat) % 2`; `/` and `%` are therefore treated asymmetrically. Floor or Euclidean division read as intended is not modeled.
2. **Two readings of natural subtraction** are modeled (`partialNat`, `intValued`); the agreement results assume `partialNat`, and that hypothesis is tight, witnessed under `intValued` by `ce_agreement_intValued` and `ce_intValued_humanValid_not_leanValid`.
3. **Two connective semantics** are modeled: Kleene's strong three-valued connectives (`Conn.kleene`) and McCarthy-style left-to-right sequential connectives (`Conn.seq`). Quantifiers are the strong Kleene quantifiers under both.
4. **Junk values are functions of the operand values** (a record `J : Junk` of functions), not arbitrary choices per occurrence of a term.
5. **Surface syntax is outside the model.** Coercion insertion, numeral defaulting and overloaded notation are not modeled; the Lean-core facts about them (cast placement, numeral typing) are checked directly in Lean core, not through the toy.
6. **`Fin n`** is outside the toy language; the `Fin` results are Lean-core facts.
7. **No translation** from Lean source statements into the toy language is given, so no result certifies a statement written in a Lean source file.
8. **Readers bring conventions.** A reader of `a - b` on `Nat`, of `/` and `%`, or of `Int.toNat` brings a convention from mathematics or programming, not the absence of one: integer-valued subtraction, wrapping (modular) machine arithmetic, or an operation that panics, traps or is undefined outside its domain. Lean's truncated subtraction (`(0 : Nat) - 1 = 0`) differs from each of these below zero, and its division and remainder by zero (`(n : Nat) / 0 = 0`, `(n : Nat) % 0 = n`) differ from trapping and from undefinedness. The toy models the integer convention (`intValued`) and represents a panicking, trapping or undefined outcome by the undefined human value (`partialNat`, `none`); wrapping arithmetic on `Nat` and `Int` is not modeled, and `Fin n` (arithmetic modulo `n`, R14, R23) is examined through Lean-core facts outside the toy. No relation between these readings and the semantics of any programming language is proved; the comparisons in the non-claims are modeling-bridge prose.

These are statements about the toy model and about the listed Lean core operators. Model–system relation: embedding (proved by `evalT_leanJ` and `evalJ_leanJ_iff`; R0) of the toy's total reading at `leanJ` into Lean core's operators; the Lean-core conjuncts of R9 to R16, R22 and R23 are statements about Lean core's operators themselves. Between the toy and statements written in Lean source files, Mathlib, other proof assistants or programming languages the relation is none proved, so these results neither establish nor refute the corresponding claims about those systems.

**Versions.** Lean `leanprover/lean4` release `v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library only; no Mathlib and no other dependency. The Lake project in `lean/` declares one library, `ToyJunk` (modules `Basic`, `Lemmas`, `Instances`, `Agreement`, `Guarded`, `Traps`, `Quantifiers`, `Examples`, `Readings`). The Lean-core facts (for instance `(5 : Nat) / 0 = 0` and the rounding of `Int.tdiv`) were checked against `v4.34.1`; other Lean versions were not examined.

**Subjects.** The Lean toolchain is the system whose core operators `leanJ` and the Lean-core trap theorems describe, and in which every theorem is kernel-checked. The papers listed as subjects are prior art for the concepts (guards, underspecification, well-definedness operators, three-valued connectives, rounding conventions); none of them is formalized here, and the cards state which part of each source a result relates to. Leijen (2001) has no immutable identifier (no DOI, arXiv identifier or report number); `REPORT.json` records its landing-page URL, its PDF URL and the date printed on the note, as explained under Evidence, *Sources*, [P13].

## Findings

Each result card below gives: kind, tier and depth; the plain claim (quoted from `results.json`); every Lean statement of the result as a verbatim quote of the source with its `file:line` range (proofs elided as `:= …`); in some cards a checked rendering with definitions unfolded; the named formulas the statements use, with their Lean readings; the hypothesis ledger; the non-vacuity witness (or an explicit *vacuous* mark); a positive control for the impossibility result; prior art; the design question; and the evidence basis.

In a hypothesis ledger, **tight** means: there is a counterexample, satisfying all the other hypotheses of the theorem, in which the conclusion fails; the ledger names that counterexample theorem and records the class its witness lies in. Every counterexample theorem is quoted in the card.

Vocabulary of the statements (all quoted under *Definitions*): `hEval c r φ ρ : Option Bool` is the human value of `φ` at `ρ` under connective semantics `c` (`.kleene` or `.seq`) and subtraction reading `r` (`.partialNat` or `.intValued`); `evalJ J φ ρ : Bool` is the total value under junk record `J`; `LeanValid φ` is `∀ ρ, evalJ leanJ φ ρ = true`; `HumanValid c r φ` is `∀ ρ, hEval c r φ ρ = some true`; `DefinedEverywhere c r φ` is `∀ ρ, hEval c r φ ρ ≠ none`; `JunkIndependent φ` is `∀ J J' ρ, evalJ J φ ρ = evalJ J' φ ρ`; `AgreesWhereDefined c r J φ` is `∀ ρ b, hEval c r φ ρ = some b → evalJ J φ ρ = b`; `guarded φ : Bool` is the guard checker. `Env.zero` sends every variable to `0`; `envAB a b` sends the natural variables `vA`, `vB` to `a`, `b`; `envX x` sends the integer variable `vX` to `x`.

Basis convention: a kernel-checked theorem is labeled `Basis: execution (Lean kernel check)`. A claim connecting a formal statement to a real system is a separate `Basis: derived (modeling bridge)` line with its reasoning; "proved" never means "true of the real system" by itself.

### Definitions: syntax

The sorts, terms, formulas, bounded quantifier and environments. `Srt.toInt` embeds a carrier value into `Int`; atoms are evaluated on these `Int` images in the total semantics.

```lean
-- lean/ToyJunk/Basic.lean:28-31
inductive Srt
  | nat
  | int
  deriving DecidableEq, Repr
-- lean/ToyJunk/Basic.lean:34-36
abbrev Srt.denote : Srt → Type
  | .nat => Nat
  | .int => Int
-- lean/ToyJunk/Basic.lean:40-42
def Srt.toInt : (s : Srt) → s.denote → Int
  | .nat, v => ((v : Nat) : Int)
  | .int, v => v
-- lean/ToyJunk/Basic.lean:46-58
inductive Term : Srt → Type
  | natVar (i : Nat) : Term .nat
  | intVar (i : Nat) : Term .int
  | natLit (n : Nat) : Term .nat
  | intLit (z : Int) : Term .int
  | add {s : Srt} (t u : Term s) : Term s
  | sub {s : Srt} (t u : Term s) : Term s
  | mul {s : Srt} (t u : Term s) : Term s
  | div {s : Srt} (t u : Term s) : Term s
  | mod {s : Srt} (t u : Term s) : Term s
  | cast (t : Term .nat) : Term .int
  | toNat (t : Term .int) : Term .nat
  deriving DecidableEq, Repr
-- lean/ToyJunk/Basic.lean:61-63
def zeroOf : (s : Srt) → Term s
  | .nat => .natLit 0
  | .int => .intLit 0
-- lean/ToyJunk/Basic.lean:67-80
inductive Formula
  | eq {s : Srt} (t u : Term s)
  | le {s : Srt} (t u : Term s)
  | lt {s : Srt} (t u : Term s)
  | dvd {s : Srt} (d n : Term s)
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)
  | imp (φ ψ : Formula)
  | allNat (x : Nat) (φ : Formula)
  | allInt (x : Nat) (φ : Formula)
  | exNat (x : Nat) (φ : Formula)
  | exInt (x : Nat) (φ : Formula)
  deriving DecidableEq, Repr
-- lean/ToyJunk/Basic.lean:87-88
def ballNat (x : Nat) (t : Term .nat) (φ : Formula) : Formula :=
  .allNat x (.imp (.le (.natVar x) t) φ)
-- lean/ToyJunk/Basic.lean:92-94
structure Env where
  nat : Nat → Nat
  int : Nat → Int
-- lean/ToyJunk/Basic.lean:97-98
def Env.setNat (ρ : Env) (x v : Nat) : Env :=
  ⟨fun i => if i = x then v else ρ.nat i, ρ.int⟩
-- lean/ToyJunk/Basic.lean:101-102
def Env.setInt (ρ : Env) (x : Nat) (v : Int) : Env :=
  ⟨ρ.nat, fun i => if i = x then v else ρ.int i⟩
-- lean/ToyJunk/Basic.lean:105
def Env.zero : Env := ⟨fun _ => 0, fun _ => 0⟩
```

### Definitions: domains and junk records

The domains on which both semantics compute exact values, and the junk records that supply total values outside them. `DivDom` and `ModDom` take `Int` arguments; at sort `Nat` the operands are cast to `Int` first. `leanJ` is Lean's own choice (its fields are Lean's `Nat` and `Int` operators); `truncJ` and `floorJ` replace `Int` `/` and `%` by the truncating and flooring conventions; `oneJ` returns `1` everywhere.

```lean
-- lean/ToyJunk/Basic.lean:118
def DivDom (n d : Int) : Prop := d ≠ 0 ∧ d ∣ n
-- lean/ToyJunk/Basic.lean:127
def ModDom (n d : Int) : Prop := 0 ≤ n ∧ 0 < d
-- lean/ToyJunk/Basic.lean:139-145
structure Junk where
  natSub : Nat → Nat → Nat
  natDiv : Nat → Nat → Nat
  natMod : Nat → Nat → Nat
  intDiv : Int → Int → Int
  intMod : Int → Int → Int
  toNat : Int → Nat
-- lean/ToyJunk/Basic.lean:150-156
def leanJ : Junk where
  natSub a b := a - b
  natDiv a b := a / b
  natMod a b := a % b
  intDiv a b := a / b
  intMod a b := a % b
  toNat z := z.toNat
-- lean/ToyJunk/Basic.lean:160
def truncJ : Junk := { leanJ with intDiv := Int.tdiv, intMod := Int.tmod }
-- lean/ToyJunk/Basic.lean:163
def floorJ : Junk := { leanJ with intDiv := Int.fdiv, intMod := Int.fmod }
-- lean/ToyJunk/Basic.lean:166-172
def oneJ : Junk where
  natSub _ _ := 1
  natDiv _ _ := 1
  natMod _ _ := 1
  intDiv _ _ := 1
  intMod _ _ := 1
  toNat _ := 1
```

### Definitions: total semantics

Total, junk-parameterized evaluation. Each partial operation computes its exact value on its domain (`b ≤ a` for `Nat` subtraction, `DivDom` for `/`, `ModDom` for `%`, `0 ≤ z` for `Int.toNat`) and consults the junk record otherwise. `evalJ` decides quantifiers classically.

```lean
-- lean/ToyJunk/Basic.lean:175-177
def opAdd : (s : Srt) → s.denote → s.denote → s.denote
  | .nat, a, b => (a + b : Nat)
  | .int, a, b => (a + b : Int)
-- lean/ToyJunk/Basic.lean:180-182
def opMul : (s : Srt) → s.denote → s.denote → s.denote
  | .nat, a, b => (a * b : Nat)
  | .int, a, b => (a * b : Int)
-- lean/ToyJunk/Basic.lean:185-187
def jSub (J : Junk) : (s : Srt) → s.denote → s.denote → s.denote
  | .nat, a, b => if (b : Nat) ≤ a then (a - b : Nat) else J.natSub a b
  | .int, a, b => (a - b : Int)
-- lean/ToyJunk/Basic.lean:190-192
def jDiv (J : Junk) : (s : Srt) → s.denote → s.denote → s.denote
  | .nat, a, b => if DivDom ((a : Nat) : Int) ((b : Nat) : Int) then (a / b : Nat) else J.natDiv a b
  | .int, a, b => if DivDom a b then (a / b : Int) else J.intDiv a b
-- lean/ToyJunk/Basic.lean:195-197
def jMod (J : Junk) : (s : Srt) → s.denote → s.denote → s.denote
  | .nat, a, b => if ModDom ((a : Nat) : Int) ((b : Nat) : Int) then (a % b : Nat) else J.natMod a b
  | .int, a, b => if ModDom a b then (a % b : Int) else J.intMod a b
-- lean/ToyJunk/Basic.lean:200
def jToNat (J : Junk) (z : Int) : Nat := if 0 ≤ z then z.toNat else J.toNat z
-- lean/ToyJunk/Basic.lean:203-214
def evalT (J : Junk) (ρ : Env) : {s : Srt} → Term s → s.denote
  | _, .natVar i => ρ.nat i
  | _, .intVar i => ρ.int i
  | _, .natLit n => n
  | _, .intLit z => z
  | s, .add t u => opAdd s (evalT J ρ t) (evalT J ρ u)
  | s, .sub t u => jSub J s (evalT J ρ t) (evalT J ρ u)
  | s, .mul t u => opMul s (evalT J ρ t) (evalT J ρ u)
  | s, .div t u => jDiv J s (evalT J ρ t) (evalT J ρ u)
  | s, .mod t u => jMod J s (evalT J ρ t) (evalT J ρ u)
  | _, .cast t => ((evalT J ρ t : Nat) : Int)
  | _, .toNat t => jToNat J (evalT J ρ t)
-- lean/ToyJunk/Basic.lean:220-232
noncomputable def evalJ (J : Junk) : Formula → Env → Bool
  | @Formula.eq s t u, ρ => decide (s.toInt (evalT J ρ t) = s.toInt (evalT J ρ u))
  | @Formula.le s t u, ρ => decide (s.toInt (evalT J ρ t) ≤ s.toInt (evalT J ρ u))
  | @Formula.lt s t u, ρ => decide (s.toInt (evalT J ρ t) < s.toInt (evalT J ρ u))
  | @Formula.dvd s d n, ρ => decide (s.toInt (evalT J ρ d) ∣ s.toInt (evalT J ρ n))
  | .not φ, ρ => !evalJ J φ ρ
  | .and φ ψ, ρ => evalJ J φ ρ && evalJ J ψ ρ
  | .or φ ψ, ρ => evalJ J φ ρ || evalJ J ψ ρ
  | .imp φ ψ, ρ => !evalJ J φ ρ || evalJ J ψ ρ
  | .allNat x φ, ρ => decide (∀ v : Nat, evalJ J φ (ρ.setNat x v) = true)
  | .allInt x φ, ρ => decide (∀ v : Int, evalJ J φ (ρ.setInt x v) = true)
  | .exNat x φ, ρ => decide (∃ v : Nat, evalJ J φ (ρ.setNat x v) = true)
  | .exInt x φ, ρ => decide (∃ v : Int, evalJ J φ (ρ.setInt x v) = true)
```

### Definitions: Lean's reading

The same language read directly with Lean's operators and relations at the native sort; `evalJ_leanJ_iff` (result R0) shows it coincides with `evalJ leanJ`.

```lean
-- lean/ToyJunk/Basic.lean:238-254
def leanEvalT (ρ : Env) : {s : Srt} → Term s → s.denote
  | _, .natVar i => ρ.nat i
  | _, .intVar i => ρ.int i
  | _, .natLit n => n
  | _, .intLit z => z
  | .nat, .add t u => (leanEvalT ρ t : Nat) + leanEvalT ρ u
  | .int, .add t u => (leanEvalT ρ t : Int) + leanEvalT ρ u
  | .nat, .sub t u => (leanEvalT ρ t : Nat) - leanEvalT ρ u
  | .int, .sub t u => (leanEvalT ρ t : Int) - leanEvalT ρ u
  | .nat, .mul t u => (leanEvalT ρ t : Nat) * leanEvalT ρ u
  | .int, .mul t u => (leanEvalT ρ t : Int) * leanEvalT ρ u
  | .nat, .div t u => (leanEvalT ρ t : Nat) / leanEvalT ρ u
  | .int, .div t u => (leanEvalT ρ t : Int) / leanEvalT ρ u
  | .nat, .mod t u => (leanEvalT ρ t : Nat) % leanEvalT ρ u
  | .int, .mod t u => (leanEvalT ρ t : Int) % leanEvalT ρ u
  | _, .cast t => ((leanEvalT ρ t : Nat) : Int)
  | _, .toNat t => (leanEvalT ρ t : Int).toNat
-- lean/ToyJunk/Basic.lean:257-259
def Srt.leP : (s : Srt) → s.denote → s.denote → Prop
  | .nat, a, b => (a : Nat) ≤ b
  | .int, a, b => (a : Int) ≤ b
-- lean/ToyJunk/Basic.lean:262-264
def Srt.ltP : (s : Srt) → s.denote → s.denote → Prop
  | .nat, a, b => (a : Nat) < b
  | .int, a, b => (a : Int) < b
-- lean/ToyJunk/Basic.lean:267-269
def Srt.dvdP : (s : Srt) → s.denote → s.denote → Prop
  | .nat, a, b => (a : Nat) ∣ b
  | .int, a, b => (a : Int) ∣ b
-- lean/ToyJunk/Basic.lean:273-285
def leanEvalF : Formula → Env → Prop
  | .eq t u, ρ => leanEvalT ρ t = leanEvalT ρ u
  | @Formula.le s t u, ρ => s.leP (leanEvalT ρ t) (leanEvalT ρ u)
  | @Formula.lt s t u, ρ => s.ltP (leanEvalT ρ t) (leanEvalT ρ u)
  | @Formula.dvd s d n, ρ => s.dvdP (leanEvalT ρ d) (leanEvalT ρ n)
  | .not φ, ρ => ¬ leanEvalF φ ρ
  | .and φ ψ, ρ => leanEvalF φ ρ ∧ leanEvalF ψ ρ
  | .or φ ψ, ρ => leanEvalF φ ρ ∨ leanEvalF ψ ρ
  | .imp φ ψ, ρ => leanEvalF φ ρ → leanEvalF ψ ρ
  | .allNat x φ, ρ => ∀ v : Nat, leanEvalF φ (ρ.setNat x v)
  | .allInt x φ, ρ => ∀ v : Int, leanEvalF φ (ρ.setInt x v)
  | .exNat x φ, ρ => ∃ v : Nat, leanEvalF φ (ρ.setNat x v)
  | .exInt x φ, ρ => ∃ v : Int, leanEvalF φ (ρ.setInt x v)
```

### Definitions: human semantics

Exact, partial evaluation into `Option Int`, three-valued connectives and quantifiers. `hSub` at sort `nat` is undefined below zero under `partialNat` and integer-valued under `intValued`; `hDiv`, `hMod` and `hToNat` are undefined off `DivDom`, `ModDom` and `0 ≤ a`.

```lean
-- lean/ToyJunk/Basic.lean:291-294
inductive SubReading
  | partialNat
  | intValued
  deriving DecidableEq, Repr
-- lean/ToyJunk/Basic.lean:300-303
inductive Conn
  | kleene
  | seq
  deriving DecidableEq, Repr
-- lean/ToyJunk/Basic.lean:306-309
def obind2 (x y : Option Int) (f : Int → Int → Option Int) : Option Int :=
  match x, y with
  | some a, some b => f a b
  | _, _ => none
-- lean/ToyJunk/Basic.lean:312-317
def hSub (r : SubReading) : Srt → Int → Int → Option Int
  | .nat, a, b =>
    match r with
    | .partialNat => if b ≤ a then some (a - b) else none
    | .intValued => some (a - b)
  | .int, a, b => some (a - b)
-- lean/ToyJunk/Basic.lean:320
def hDiv (a b : Int) : Option Int := if DivDom a b then some (a / b) else none
-- lean/ToyJunk/Basic.lean:323
def hMod (a b : Int) : Option Int := if ModDom a b then some (a % b) else none
-- lean/ToyJunk/Basic.lean:326
def hToNat (a : Int) : Option Int := if 0 ≤ a then some a else none
-- lean/ToyJunk/Basic.lean:330-341
def hEvalT (r : SubReading) (ρ : Env) : {s : Srt} → Term s → Option Int
  | _, .natVar i => some (ρ.nat i : Int)
  | _, .intVar i => some (ρ.int i)
  | _, .natLit n => some (n : Int)
  | _, .intLit z => some z
  | _, .add t u => obind2 (hEvalT r ρ t) (hEvalT r ρ u) fun a b => some (a + b)
  | s, .sub t u => obind2 (hEvalT r ρ t) (hEvalT r ρ u) (hSub r s)
  | _, .mul t u => obind2 (hEvalT r ρ t) (hEvalT r ρ u) fun a b => some (a * b)
  | _, .div t u => obind2 (hEvalT r ρ t) (hEvalT r ρ u) hDiv
  | _, .mod t u => obind2 (hEvalT r ρ t) (hEvalT r ρ u) hMod
  | _, .cast t => hEvalT r ρ t
  | _, .toNat t => (hEvalT r ρ t).bind hToNat
-- lean/ToyJunk/Basic.lean:344-346
def hAtom (rel : Int → Int → Bool) : Option Int → Option Int → Option Bool
  | some a, some b => some (rel a b)
  | _, _ => none
-- lean/ToyJunk/Basic.lean:349
def tvNot (x : Option Bool) : Option Bool := x.map (!·)
-- lean/ToyJunk/Basic.lean:354-361
def tvAnd : Conn → Option Bool → Option Bool → Option Bool
  | .kleene, some false, _ => some false
  | .kleene, _, some false => some false
  | .kleene, some true, some true => some true
  | .kleene, _, _ => none
  | .seq, some false, _ => some false
  | .seq, some true, y => y
  | .seq, none, _ => none
-- lean/ToyJunk/Basic.lean:364-371
def tvOr : Conn → Option Bool → Option Bool → Option Bool
  | .kleene, some true, _ => some true
  | .kleene, _, some true => some true
  | .kleene, some false, some false => some false
  | .kleene, _, _ => none
  | .seq, some true, _ => some true
  | .seq, some false, y => y
  | .seq, none, _ => none
-- lean/ToyJunk/Basic.lean:375
def tvImp (c : Conn) (x y : Option Bool) : Option Bool := tvOr c (tvNot x) y
-- lean/ToyJunk/Basic.lean:381-384
noncomputable def tvAll {α : Type} (f : α → Option Bool) : Option Bool :=
  if ∀ v, f v = some true then some true
  else if ∃ v, f v = some false then some false
  else none
-- lean/ToyJunk/Basic.lean:389-392
noncomputable def tvEx {α : Type} (f : α → Option Bool) : Option Bool :=
  if ∃ v, f v = some true then some true
  else if ∀ v, f v = some false then some false
  else none
-- lean/ToyJunk/Basic.lean:396-408
noncomputable def hEval (c : Conn) (r : SubReading) : Formula → Env → Option Bool
  | .eq t u, ρ => hAtom (fun a b => decide (a = b)) (hEvalT r ρ t) (hEvalT r ρ u)
  | .le t u, ρ => hAtom (fun a b => decide (a ≤ b)) (hEvalT r ρ t) (hEvalT r ρ u)
  | .lt t u, ρ => hAtom (fun a b => decide (a < b)) (hEvalT r ρ t) (hEvalT r ρ u)
  | .dvd d n, ρ => hAtom (fun a b => decide (a ∣ b)) (hEvalT r ρ d) (hEvalT r ρ n)
  | .not φ, ρ => tvNot (hEval c r φ ρ)
  | .and φ ψ, ρ => tvAnd c (hEval c r φ ρ) (hEval c r ψ ρ)
  | .or φ ψ, ρ => tvOr c (hEval c r φ ρ) (hEval c r ψ ρ)
  | .imp φ ψ, ρ => tvImp c (hEval c r φ ρ) (hEval c r ψ ρ)
  | .allNat x φ, ρ => tvAll fun v : Nat => hEval c r φ (ρ.setNat x v)
  | .allInt x φ, ρ => tvAll fun v : Int => hEval c r φ (ρ.setInt x v)
  | .exNat x φ, ρ => tvEx fun v : Nat => hEval c r φ (ρ.setNat x v)
  | .exInt x φ, ρ => tvEx fun v : Int => hEval c r φ (ρ.setInt x v)
```

### Definitions: properties of formulas

The properties the results relate.

```lean
-- lean/ToyJunk/Basic.lean:416-417
def JunkIndependent (φ : Formula) : Prop :=
  ∀ (J J' : Junk) (ρ : Env), evalJ J φ ρ = evalJ J' φ ρ
-- lean/ToyJunk/Basic.lean:420-421
def DefinedEverywhere (c : Conn) (r : SubReading) (φ : Formula) : Prop :=
  ∀ ρ : Env, hEval c r φ ρ ≠ none
-- lean/ToyJunk/Basic.lean:424-425
def AgreesWhereDefined (c : Conn) (r : SubReading) (J : Junk) (φ : Formula) : Prop :=
  ∀ (ρ : Env) (b : Bool), hEval c r φ ρ = some b → evalJ J φ ρ = b
-- lean/ToyJunk/Basic.lean:428
def LeanValid (φ : Formula) : Prop := ∀ ρ : Env, evalJ leanJ φ ρ = true
-- lean/ToyJunk/Basic.lean:431-432
def HumanValid (c : Conn) (r : SubReading) (φ : Formula) : Prop :=
  ∀ ρ : Env, hEval c r φ ρ = some true
```

### Definitions: the guard checker

The syntactic checker. `Formula.facts` collects the atomic facts a formula contributes when it is known true; facts accumulate left to right through the left conjunct of `∧` and the premise of `→`; `∨` and `¬` contribute none; a quantifier discards the facts that mention its bound variable. Each partial operation needs its guard among the facts, matched syntactically.

```lean
-- lean/ToyJunk/Basic.lean:438-445
def Formula.facts : Formula → List Formula
  | .and φ ψ => φ.facts ++ ψ.facts
  | .eq t u => [.eq t u]
  | .le t u => [.le t u]
  | .lt t u => [.lt t u]
  | .dvd d n => [.dvd d n]
  | .not (.eq t u) => [.not (.eq t u)]
  | _ => []
-- lean/ToyJunk/Basic.lean:452-467
def Term.guardedIn (Γ : List Formula) : {s : Srt} → Term s → Bool
  | _, .natVar _ => true
  | _, .intVar _ => true
  | _, .natLit _ => true
  | _, .intLit _ => true
  | _, .add t u => t.guardedIn Γ && u.guardedIn Γ
  | _, .mul t u => t.guardedIn Γ && u.guardedIn Γ
  | .nat, .sub t u => t.guardedIn Γ && u.guardedIn Γ && Γ.contains (.le u t)
  | .int, .sub t u => t.guardedIn Γ && u.guardedIn Γ
  | s, .div t u => t.guardedIn Γ && u.guardedIn Γ &&
      Γ.contains (.not (.eq u (zeroOf s))) && Γ.contains (.dvd u t)
  | .nat, .mod t u => t.guardedIn Γ && u.guardedIn Γ && Γ.contains (.not (.eq u (.natLit 0)))
  | .int, .mod t u => t.guardedIn Γ && u.guardedIn Γ &&
      Γ.contains (.lt (.intLit 0) u) && Γ.contains (.le (.intLit 0) t)
  | _, .cast t => t.guardedIn Γ
  | _, .toNat t => t.guardedIn Γ && Γ.contains (.le (.intLit 0) t)
-- lean/ToyJunk/Basic.lean:470-478
def Term.mentionsNat (x : Nat) : {s : Srt} → Term s → Bool
  | _, .natVar i => i == x
  | _, .intVar _ => false
  | _, .natLit _ => false
  | _, .intLit _ => false
  | _, .add t u | _, .sub t u | _, .mul t u | _, .div t u | _, .mod t u =>
      t.mentionsNat x || u.mentionsNat x
  | _, .cast t => t.mentionsNat x
  | _, .toNat t => t.mentionsNat x
-- lean/ToyJunk/Basic.lean:481-489
def Term.mentionsInt (x : Nat) : {s : Srt} → Term s → Bool
  | _, .natVar _ => false
  | _, .intVar i => i == x
  | _, .natLit _ => false
  | _, .intLit _ => false
  | _, .add t u | _, .sub t u | _, .mul t u | _, .div t u | _, .mod t u =>
      t.mentionsInt x || u.mentionsInt x
  | _, .cast t => t.mentionsInt x
  | _, .toNat t => t.mentionsInt x
-- lean/ToyJunk/Basic.lean:493-497
def Formula.mentionsNat (x : Nat) : Formula → Bool
  | .eq t u | .le t u | .lt t u | .dvd t u => t.mentionsNat x || u.mentionsNat x
  | .not φ => φ.mentionsNat x
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.mentionsNat x || ψ.mentionsNat x
  | .allNat _ φ | .allInt _ φ | .exNat _ φ | .exInt _ φ => φ.mentionsNat x
-- lean/ToyJunk/Basic.lean:500-504
def Formula.mentionsInt (x : Nat) : Formula → Bool
  | .eq t u | .le t u | .lt t u | .dvd t u => t.mentionsInt x || u.mentionsInt x
  | .not φ => φ.mentionsInt x
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.mentionsInt x || ψ.mentionsInt x
  | .allNat _ φ | .allInt _ φ | .exNat _ φ | .exInt _ φ => φ.mentionsInt x
-- lean/ToyJunk/Basic.lean:509-516
def Formula.guardedIn : List Formula → Formula → Bool
  | Γ, .eq t u | Γ, .le t u | Γ, .lt t u | Γ, .dvd t u => t.guardedIn Γ && u.guardedIn Γ
  | Γ, .not φ => φ.guardedIn Γ
  | Γ, .and φ ψ => φ.guardedIn Γ && ψ.guardedIn (Γ ++ φ.facts)
  | Γ, .or φ ψ => φ.guardedIn Γ && ψ.guardedIn Γ
  | Γ, .imp φ ψ => φ.guardedIn Γ && ψ.guardedIn (Γ ++ φ.facts)
  | Γ, .allNat x φ | Γ, .exNat x φ => φ.guardedIn (Γ.filter fun f => !f.mentionsNat x)
  | Γ, .allInt x φ | Γ, .exInt x φ => φ.guardedIn (Γ.filter fun f => !f.mentionsInt x)
-- lean/ToyJunk/Basic.lean:519
def guarded (φ : Formula) : Bool := φ.guardedIn []
```

### Connective tables

The connectives of `Conn.kleene` are Kleene's strong three-valued connectives and those of `Conn.seq` are McCarthy's sequential connectives; the quantifiers `tvAll` and `tvEx` are the strong Kleene quantifiers. The three theorems below state this; `tvRank` takes values in `Nat`, so `2 - tvRank x` is natural-number subtraction on the values `0`, `1`, `2`.

```lean
-- lean/ToyJunk/Lemmas.lean:130-133
def tvRank : Option Bool → Nat
  | some false => 0
  | none => 1
  | some true => 2
-- lean/ToyJunk/Lemmas.lean:141-145
theorem kleene_tables (x y : Option Bool) :
    tvRank (tvAnd .kleene x y) = min (tvRank x) (tvRank y) ∧
      tvRank (tvOr .kleene x y) = max (tvRank x) (tvRank y) ∧
      tvRank (tvNot x) = 2 - tvRank x ∧
      tvImp .kleene x y = tvOr .kleene (tvNot x) y := …
-- lean/ToyJunk/Lemmas.lean:151-154
theorem seq_tables (x y : Option Bool) :
    tvAnd .seq x y = x.bind (fun b => if b then y else some false) ∧
      tvOr .seq x y = x.bind (fun b => if b then some true else y) ∧
      tvImp .seq x y = x.bind (fun b => if b then y else some true) := …
-- lean/ToyJunk/Lemmas.lean:160-164
theorem kleene_quantifier_tables {α : Type} (f : α → Option Bool) :
    (tvAll f = some true ↔ ∀ v, f v = some true) ∧
      (tvAll f = some false ↔ ∃ v, f v = some false) ∧
      (tvEx f = some true ↔ ∃ v, f v = some true) ∧
      (tvEx f = some false ↔ ∀ v, f v = some false) := …
```

### Definition examples

Each core definition has intended positive and negative instances, proved in `ToyJunk/Examples.lean` (quoted verbatim). They test that the definitions admit what they should and reject what they should: for instance `DivDom_neg` shows that an inexact quotient lies outside `DivDom`, and `guarded_neg` shows rejected formulas.

```lean
-- lean/ToyJunk/Examples.lean:15
theorem DivDom_pos : DivDom 6 3 ∧ DivDom (-4) 2 ∧ DivDom 0 5 := …
-- lean/ToyJunk/Examples.lean:19
theorem DivDom_neg : ¬ DivDom 5 0 ∧ ¬ DivDom 0 0 ∧ ¬ DivDom 7 2 := …
-- lean/ToyJunk/Examples.lean:22
theorem ModDom_pos : ModDom 7 2 ∧ ModDom 0 3 := …
-- lean/ToyJunk/Examples.lean:26-28
theorem ModDom_neg :
    ¬ ModDom 5 0 ∧ ¬ ModDom (-7) 2 ∧ ¬ ModDom 7 (-2) ∧ ¬ ModDom (-4) 2 ∧
      (Int.tmod (-4) 2 = (-4) % 2 ∧ Int.fmod (-4) 2 = (-4) % 2) := …
-- lean/ToyJunk/Examples.lean:33-37
theorem evalT_pos (J : Junk) :
    evalT J Env.zero (.sub (.natLit 5) (.natLit 3)) = (2 : Nat) ∧
      evalT J Env.zero (.div (.natLit 6) (.natLit 3)) = (2 : Nat) ∧
      evalT J Env.zero (.div (.intLit (-6)) (.intLit 3)) = (-2 : Int) ∧
      evalT J Env.zero (.mod (.natLit 7) (.natLit 2)) = (1 : Nat) := …
-- lean/ToyJunk/Examples.lean:41-45
theorem evalT_neg :
    evalT leanJ Env.zero (.sub (.natLit 0) (.natLit 1)) = (0 : Nat) ∧
      evalT oneJ Env.zero (.sub (.natLit 0) (.natLit 1)) = (1 : Nat) ∧
      evalT leanJ Env.zero (.div (.intLit 5) (.intLit 0)) = (0 : Int) ∧
      evalT oneJ Env.zero (.div (.intLit 5) (.intLit 0)) = (1 : Int) := …
-- lean/ToyJunk/Examples.lean:49-52
theorem leanJ_pos :
    evalT leanJ Env.zero (.div (.intLit (-7)) (.intLit 2)) = Int.ediv (-7) 2 ∧
      evalT leanJ Env.zero (.div (.intLit (-7)) (.intLit 2)) =
        leanEvalT Env.zero (.div (.intLit (-7)) (.intLit 2)) := …
-- lean/ToyJunk/Examples.lean:56-58
theorem leanJ_neg :
    evalT truncJ Env.zero (.div (.intLit (-7)) (.intLit 2)) ≠
      leanEvalT Env.zero (.div (.intLit (-7)) (.intLit 2)) := …
-- lean/ToyJunk/Examples.lean:64-68
theorem hEvalT_pos (r : SubReading) :
    hEvalT .partialNat Env.zero (.sub (.natLit 5) (.natLit 3)) = some 2 ∧
      hEvalT r Env.zero (.div (.natLit 6) (.natLit 3)) = some 2 ∧
      hEvalT r Env.zero (.div (.intLit (-6)) (.intLit 3)) = some (-2) ∧
      hEvalT .intValued Env.zero (.sub (.natLit 3) (.natLit 5)) = some (-2) := …
-- lean/ToyJunk/Examples.lean:74-80
theorem hEvalT_neg (r : SubReading) :
    hEvalT .partialNat Env.zero (.sub (.natLit 3) (.natLit 5)) = none ∧
      hEvalT r Env.zero (.div (.natLit 5) (.natLit 0)) = none ∧
      hEvalT r Env.zero (.div (.natLit 7) (.natLit 2)) = none ∧
      hEvalT r Env.zero (.mod (.intLit (-7)) (.intLit 2)) = none ∧
      hEvalT r Env.zero (.toNat (.intLit (-3))) = none ∧
      hEvalT .partialNat Env.zero (.mul (.sub (.natLit 0) (.natLit 1)) (.natLit 0)) = none := …
-- lean/ToyJunk/Examples.lean:85-87
theorem tv_pos :
    tvAnd .kleene none (some false) = some false ∧ tvOr .kleene none (some true) = some true ∧
      tvAnd .seq (some false) none = some false ∧ tvOr .seq (some true) none = some true := …
-- lean/ToyJunk/Examples.lean:90-92
theorem tv_neg :
    tvAnd .seq none (some false) = none ∧ tvOr .seq none (some true) = none ∧
      tvAnd .kleene none (some true) = none := …
-- lean/ToyJunk/Examples.lean:97-99
theorem tvImp_pos :
    tvImp .kleene (some false) none = some true ∧ tvImp .seq (some false) none = some true ∧
      tvImp .kleene none (some true) = some true := …
-- lean/ToyJunk/Examples.lean:104-106
theorem tvImp_neg :
    tvImp .seq none (some true) = none ∧ tvImp .kleene none (some false) = none ∧
      tvImp .kleene (some true) (some false) = some false := …
-- lean/ToyJunk/Examples.lean:111
theorem tvAll_pos : tvAll (fun n : Nat => if n = 0 then some false else none) = some false := …
-- lean/ToyJunk/Examples.lean:117
theorem tvAll_neg : tvAll (fun n : Nat => if n = 0 then some true else none) = none := …
-- lean/ToyJunk/Examples.lean:127
theorem tvEx_pos : tvEx (fun n : Nat => if n = 0 then some true else none) = some true := …
-- lean/ToyJunk/Examples.lean:132
theorem tvEx_neg : tvEx (fun n : Nat => if n = 0 then some false else none) = none := …
-- lean/ToyJunk/Examples.lean:145
theorem leanEvalF_pos : leanEvalF fZeroSubOne Env.zero ∧ leanEvalF fDivZero Env.zero := …
-- lean/ToyJunk/Examples.lean:149
theorem leanEvalF_neg : ¬ leanEvalF fNumeralNat Env.zero ∧ ¬ leanEvalF fSubAddCancel (envAB 0 1) := …
-- lean/ToyJunk/Examples.lean:155
theorem JunkIndependent_pos : JunkIndependent fMulZero ∧ JunkIndependent fSubAddCancelGuarded := …
-- lean/ToyJunk/Examples.lean:158
theorem JunkIndependent_neg : ¬ JunkIndependent fZeroSubOne ∧ ¬ JunkIndependent fSubLeSelf := …
-- lean/ToyJunk/Examples.lean:161-162
theorem DefinedEverywhere_pos (c : Conn) (r : SubReading) :
    DefinedEverywhere c r fSubAddCancelGuarded := …
-- lean/ToyJunk/Examples.lean:165
theorem DefinedEverywhere_neg (c : Conn) : ¬ DefinedEverywhere c .partialNat fSubAddCancel := …
-- lean/ToyJunk/Examples.lean:175
theorem AgreesWhereDefined_pos (c : Conn) : AgreesWhereDefined c .intValued leanJ fSubLeSelf := …
-- lean/ToyJunk/Examples.lean:188-189
theorem AgreesWhereDefined_partialNat_trivial (c : Conn) (J : Junk) :
    AgreesWhereDefined c .partialNat J fDivZero := …
-- lean/ToyJunk/Examples.lean:192
theorem AgreesWhereDefined_neg (c : Conn) : ¬ AgreesWhereDefined c .intValued leanJ fNumeralNat := …
-- lean/ToyJunk/Examples.lean:198
theorem LeanValid_pos : LeanValid fDivZero := …
-- lean/ToyJunk/Examples.lean:200
theorem LeanValid_neg : ¬ LeanValid fSubAddCancel := …
-- lean/ToyJunk/Examples.lean:202
theorem HumanValid_pos (c : Conn) (r : SubReading) : HumanValid c r fSubAddCancelGuarded := …
-- lean/ToyJunk/Examples.lean:205
theorem HumanValid_neg (c : Conn) (r : SubReading) : ¬ HumanValid c r fDivZero := …
-- lean/ToyJunk/Examples.lean:230-234
theorem guarded_pos :
    guarded fSubAddCancelGuarded = true ∧ guarded fDvdDivGuarded = true ∧
      guarded fBoundedCancel = true ∧ guarded fGuardedNatMod = true ∧
      guarded fGuardedIntMod = true ∧ guarded fGuardedIntDiv = true ∧
      guarded fGuardedToNat = true := …
-- lean/ToyJunk/Examples.lean:240-244
theorem guarded_branches_pos (c : Conn) (r : SubReading) :
    (LeanValid fGuardedNatMod ∧ HumanValid c r fGuardedNatMod) ∧
      (LeanValid fGuardedIntMod ∧ HumanValid c r fGuardedIntMod) ∧
      (LeanValid fGuardedIntDiv ∧ HumanValid c r fGuardedIntDiv) ∧
      (LeanValid fGuardedToNat ∧ HumanValid c r fGuardedToNat) := …
-- lean/ToyJunk/Examples.lean:276-277
theorem guarded_neg :
    guarded fSubAddCancel = false ∧ guarded fDivZero = false ∧ guarded fStaleGuard = false := …
-- lean/ToyJunk/Examples.lean:281-283
theorem facts_pos :
    (Formula.and (.le vB vA) (.not (.eq vB (.natLit 0)))).facts =
      [.le vB vA, .not (.eq vB (.natLit 0))] := …
-- lean/ToyJunk/Examples.lean:287-290
theorem facts_neg :
    (Formula.or (.le vB vA) (.le vA vB)).facts = [] ∧
      (Formula.imp (.le vB vA) (.le vA vB)).facts = [] ∧
      (Formula.not (.le vB vA)).facts = [] := …
-- lean/ToyJunk/Examples.lean:294-295
theorem ballNat_unfold (x : Nat) (t : Term .nat) (φ : Formula) :
    ballNat x t φ = .allNat x (.imp (.le (.natVar x) t) φ) := …
```

### Named formulas and their Lean readings

The variables `vA`, `vB` (natural variables 0 and 1) and `vX`, `vY` (integer variables 0 and 1), the environments `envAB` and `envX`, and every named formula used by the results, quoted verbatim:

```lean
-- lean/ToyJunk/Instances.lean:10
abbrev vA : Term .nat := .natVar 0
-- lean/ToyJunk/Instances.lean:12
abbrev vB : Term .nat := .natVar 1
-- lean/ToyJunk/Instances.lean:14
abbrev vX : Term .int := .intVar 0
-- lean/ToyJunk/Instances.lean:18
def envAB (x y : Nat) : Env := ⟨fun i => if i = 0 then x else if i = 1 then y else 0, fun _ => 0⟩
-- lean/ToyJunk/Instances.lean:21
def fMulZero : Formula := .eq (.mul (.sub vA vB) (.natLit 0)) (.natLit 0)
-- lean/ToyJunk/Instances.lean:24
def fSubLeSelf : Formula := .le (.sub vA vB) vA
-- lean/ToyJunk/Instances.lean:27
def fSubAddCancel : Formula := .eq (.add (.sub vA vB) vB) vA
-- lean/ToyJunk/Instances.lean:30
def fSubAddCancelGuarded : Formula := .imp (.le vB vA) fSubAddCancel
-- lean/ToyJunk/Instances.lean:33
def fZeroSubOne : Formula := .eq (.sub (.natLit 0) (.natLit 1)) (.natLit 0)
-- lean/ToyJunk/Instances.lean:36
def fFiveSubThree : Formula := .eq (.sub (.natLit 5) (.natLit 3)) (.natLit 2)
-- lean/ToyJunk/Instances.lean:39
def fDivZero : Formula := .eq (.div vX (.intLit 0)) (.intLit 0)
-- lean/ToyJunk/Instances.lean:42
def fNumeralNat : Formula := .lt (.sub (.natLit 2) (.natLit 3)) (.natLit 0)
-- lean/ToyJunk/Instances.lean:45
def fNumeralInt : Formula := .lt (.sub (.intLit 2) (.intLit 3)) (.intLit 0)
-- lean/ToyJunk/Instances.lean:48
def fDivZeroRefl : Formula := .eq (.div vX (.intLit 0)) (.div vX (.intLit 0))
-- lean/ToyJunk/Instances.lean:51
def fDivZeroEM : Formula := .or fDivZero (.not fDivZero)
-- lean/ToyJunk/Guarded.lean:329
def fTrivOr : Formula := .or (.le (.natLit 0) (.natLit 0)) (.eq (.sub vA vB) (.natLit 0))
-- lean/ToyJunk/Guarded.lean:343
def fOrNegGuardSubCancel : Formula := .or (.not (.le vB vA)) fSubAddCancel
-- lean/ToyJunk/Guarded.lean:346
def fModDisjGuard : Formula := .or (.eq vB (.natLit 0)) (.lt (.mod vA vB) vB)
-- lean/ToyJunk/Guarded.lean:383-384
def fContradictoryGuard : Formula :=
  .imp (.and (.le vB vA) (.lt vA vB)) (.eq (.sub vA vB) (.natLit 1))
-- lean/ToyJunk/Guarded.lean:387
def fExImpGuard : Formula := .exNat 1 (.imp (.le vB vA) (.eq (.sub vA vB) (.natLit 1)))
-- lean/ToyJunk/Guarded.lean:390
def fExAndGuard : Formula := .exNat 1 (.and (.le vB vA) (.eq (.sub vA vB) (.natLit 1)))
-- lean/ToyJunk/Guarded.lean:427
def fSevenDivTwo : Formula := .eq (.div (.natLit 7) (.natLit 2)) (.natLit 3)
-- lean/ToyJunk/Guarded.lean:430
def fSevenModTwo : Formula := .eq (.mod (.natLit 7) (.natLit 2)) (.natLit 1)
-- lean/ToyJunk/Guarded.lean:433-434
def fNatDivModId : Formula :=
  .imp (.not (.eq vB (.natLit 0))) (.eq (.add (.mul (.div vA vB) vB) (.mod vA vB)) vA)
-- lean/ToyJunk/Guarded.lean:475
def fGuardFirst : Formula := .and (.le vB vA) fSubAddCancel
-- lean/ToyJunk/Guarded.lean:478
def fGuardSecond : Formula := .and fSubAddCancel (.le vB vA)
-- lean/ToyJunk/Guarded.lean:481
def fContrapositive : Formula := .imp (.not fSubAddCancel) (.not (.le vB vA))
-- lean/ToyJunk/Guarded.lean:597
def envX (z : Int) : Env := ⟨fun _ => 0, fun i => if i = 0 then z else 0⟩
-- lean/ToyJunk/Guarded.lean:600
def fToNatGuardFirst : Formula := .and (.le (.intLit 0) vX) (.eq (.toNat vX) (.toNat vX))
-- lean/ToyJunk/Guarded.lean:602
def fToNatGuardSecond : Formula := .and (.eq (.toNat vX) (.toNat vX)) (.le (.intLit 0) vX)
-- lean/ToyJunk/Guarded.lean:604
def fToNatImp : Formula := .imp (.le (.intLit 0) vX) (.eq (.toNat vX) (.toNat vX))
-- lean/ToyJunk/Guarded.lean:606-607
def fToNatContrapose : Formula :=
  .imp (.not (.eq (.toNat vX) (.toNat vX))) (.not (.le (.intLit 0) vX))
-- lean/ToyJunk/Traps.lean:20-21
def fTruncSubCancel01 : Formula :=
  .eq (.add (.sub (.natLit 0) (.natLit 1)) (.natLit 1)) (.natLit 0)
-- lean/ToyJunk/Traps.lean:33
def fTruncSubLe01 : Formula := .le (.sub (.natLit 0) (.natLit 1)) (.natLit 0)
-- lean/ToyJunk/Traps.lean:43
def fFiveDivZero : Formula := .eq (.div (.intLit 5) (.intLit 0)) (.intLit 0)
-- lean/ToyJunk/Traps.lean:46
def fFiveModZero : Formula := .eq (.mod (.natLit 5) (.natLit 0)) (.natLit 5)
-- lean/ToyJunk/Traps.lean:59
def fFloorDiv : Formula := .eq (.mul (.div (.natLit 7) (.natLit 2)) (.natLit 2)) (.natLit 7)
-- lean/ToyJunk/Traps.lean:69
def fNegSevenDivTwo : Formula := .eq (.div (.intLit (-7)) (.intLit 2)) (.intLit (-4))
-- lean/ToyJunk/Traps.lean:71
def fSevenDivNegTwo : Formula := .eq (.div (.intLit 7) (.intLit (-2))) (.intLit (-3))
-- lean/ToyJunk/Traps.lean:73
def fNegSevenModTwo : Formula := .eq (.mod (.intLit (-7)) (.intLit 2)) (.intLit 1)
-- lean/ToyJunk/Traps.lean:75
def fSevenModNegTwo : Formula := .eq (.mod (.intLit 7) (.intLit (-2))) (.intLit 1)
-- lean/ToyJunk/Traps.lean:168-169
def fCastPlacement01 : Formula :=
  .eq (.cast (.sub (.natLit 0) (.natLit 1))) (.sub (.cast (.natLit 0)) (.cast (.natLit 1)))
-- lean/ToyJunk/Traps.lean:172
def fCastPlacement : Formula := .eq (.cast (.sub vA vB)) (.sub (.cast vA) (.cast vB))
-- lean/ToyJunk/Traps.lean:200
def fToNatNeg : Formula := .eq (.toNat (.intLit (-3))) (.natLit 0)
-- lean/ToyJunk/Traps.lean:240-241
def fSubAddCancelCast : Formula :=
  .eq (.add (.sub (.cast vA) (.cast vB)) (.cast vB)) (.cast vA)
-- lean/ToyJunk/Traps.lean:287
def fDvdDiv : Formula := .imp (.dvd vB vA) (.eq (.mul (.div vA vB) vB) vA)
-- lean/ToyJunk/Traps.lean:290
def fDvdDivGuarded : Formula := .imp (.not (.eq vB (.natLit 0))) fDvdDiv
-- lean/ToyJunk/Traps.lean:345
def fDvdDivDividendGuard : Formula := .imp (.not (.eq vA (.natLit 0))) fDvdDiv
-- lean/ToyJunk/Quantifiers.lean:71
def fBoundedCancel : Formula := .allNat 0 (ballNat 1 vA fSubAddCancel)
-- lean/ToyJunk/Quantifiers.lean:74
def fUnboundedCancel : Formula := .allNat 0 (.allNat 1 fSubAddCancel)
-- lean/ToyJunk/Quantifiers.lean:77
def fAllZeroLeSubOne : Formula := .allNat 0 (.le (.natLit 0) (.sub vA (.natLit 1)))
-- lean/ToyJunk/Quantifiers.lean:80
def fAllSubSucc : Formula := .allNat 0 (.eq (.sub vA (.add vA (.natLit 1))) (.natLit 0))
-- lean/ToyJunk/Quantifiers.lean:83-84
def fExSubSuccNe : Formula :=
  .exNat 0 (.not (.eq (.sub vA (.add vA (.natLit 1))) (.natLit 0)))
-- lean/ToyJunk/Quantifiers.lean:394
def fOneDivTwo : Formula := .eq (.div (.natLit 1) (.natLit 2)) (.natLit 0)
-- lean/ToyJunk/Quantifiers.lean:397-398
def fAllOneDivZero : Formula :=
  .allNat 0 (.imp (.lt (.natLit 2) vA) (.eq (.div (.natLit 1) vA) (.natLit 0)))
-- lean/ToyJunk/Examples.lean:211
abbrev vY : Term .int := .intVar 1
-- lean/ToyJunk/Examples.lean:214
def fGuardedNatMod : Formula := .imp (.not (.eq vB (.natLit 0))) (.lt (.mod vA vB) vB)
-- lean/ToyJunk/Examples.lean:217-218
def fGuardedIntMod : Formula :=
  .imp (.and (.lt (.intLit 0) vY) (.le (.intLit 0) vX)) (.lt (.mod vX vY) vY)
-- lean/ToyJunk/Examples.lean:221-222
def fGuardedIntDiv : Formula :=
  .imp (.and (.not (.eq vY (.intLit 0))) (.dvd vY vX)) (.eq (.mul (.div vX vY) vY) vX)
-- lean/ToyJunk/Examples.lean:225
def fGuardedToNat : Formula := .imp (.le (.intLit 0) vX) (.eq (.cast (.toNat vX)) vX)
-- lean/ToyJunk/Examples.lean:272
def fStaleGuard : Formula := .and (.le vB vA) (.allNat 1 fSubAddCancel)
```

The Lean reading of each named formula, stated with explicit types and proved (each proof is a definitional unfolding of `leanEvalF` through `evalJ_leanJ_iff`). These theorems are the authority for every typed rendering of a named formula in this report. For example, `leanReading_fNumeralNat` shows that `fNumeralNat` means `(2 : Nat) - 3 < 0` in Lean's reading, and `leanReading_fDivZero` that `fDivZero` at `envX x` means `x / 0 = (0 : Int)`.

```lean
-- lean/ToyJunk/Readings.lean:19-20
theorem leanReading_fMulZero (a b : Nat) :
    evalJ leanJ fMulZero (envAB a b) = true ↔ (a - b) * 0 = (0 : Nat) := …
-- lean/ToyJunk/Readings.lean:23-24
theorem leanReading_fSubLeSelf (a b : Nat) :
    evalJ leanJ fSubLeSelf (envAB a b) = true ↔ a - b ≤ a := …
-- lean/ToyJunk/Readings.lean:27-28
theorem leanReading_fSubAddCancel (a b : Nat) :
    evalJ leanJ fSubAddCancel (envAB a b) = true ↔ a - b + b = a := …
-- lean/ToyJunk/Readings.lean:31-32
theorem leanReading_fSubAddCancelGuarded (a b : Nat) :
    evalJ leanJ fSubAddCancelGuarded (envAB a b) = true ↔ (b ≤ a → a - b + b = a) := …
-- lean/ToyJunk/Readings.lean:35-36
theorem leanReading_fCastPlacement (a b : Nat) :
    evalJ leanJ fCastPlacement (envAB a b) = true ↔ ((a - b : Nat) : Int) = (a : Int) - (b : Int) := …
-- lean/ToyJunk/Readings.lean:39-41
theorem leanReading_fSubAddCancelCast (a b : Nat) :
    evalJ leanJ fSubAddCancelCast (envAB a b) = true ↔
      (a : Int) - (b : Int) + (b : Int) = (a : Int) := …
-- lean/ToyJunk/Readings.lean:44-45
theorem leanReading_fDvdDiv (a b : Nat) :
    evalJ leanJ fDvdDiv (envAB a b) = true ↔ (b ∣ a → a / b * b = a) := …
-- lean/ToyJunk/Readings.lean:48-49
theorem leanReading_fDvdDivGuarded (a b : Nat) :
    evalJ leanJ fDvdDivGuarded (envAB a b) = true ↔ (¬ b = 0 → b ∣ a → a / b * b = a) := …
-- lean/ToyJunk/Readings.lean:52-53
theorem leanReading_fDvdDivDividendGuard (a b : Nat) :
    evalJ leanJ fDvdDivDividendGuard (envAB a b) = true ↔ (¬ a = 0 → b ∣ a → a / b * b = a) := …
-- lean/ToyJunk/Readings.lean:56-57
theorem leanReading_fTrivOr (a b : Nat) :
    evalJ leanJ fTrivOr (envAB a b) = true ↔ ((0 : Nat) ≤ 0 ∨ a - b = 0) := …
-- lean/ToyJunk/Readings.lean:60-61
theorem leanReading_fOrNegGuardSubCancel (a b : Nat) :
    evalJ leanJ fOrNegGuardSubCancel (envAB a b) = true ↔ (¬ b ≤ a ∨ a - b + b = a) := …
-- lean/ToyJunk/Readings.lean:64-65
theorem leanReading_fModDisjGuard (a b : Nat) :
    evalJ leanJ fModDisjGuard (envAB a b) = true ↔ (b = 0 ∨ a % b < b) := …
-- lean/ToyJunk/Readings.lean:68-69
theorem leanReading_fContradictoryGuard (a b : Nat) :
    evalJ leanJ fContradictoryGuard (envAB a b) = true ↔ (b ≤ a ∧ a < b → a - b = 1) := …
-- lean/ToyJunk/Readings.lean:72-73
theorem leanReading_fExImpGuard (a b : Nat) :
    evalJ leanJ fExImpGuard (envAB a b) = true ↔ ∃ v : Nat, v ≤ a → a - v = 1 := …
-- lean/ToyJunk/Readings.lean:76-77
theorem leanReading_fExAndGuard (a b : Nat) :
    evalJ leanJ fExAndGuard (envAB a b) = true ↔ ∃ v : Nat, v ≤ a ∧ a - v = 1 := …
-- lean/ToyJunk/Readings.lean:80-81
theorem leanReading_fNatDivModId (a b : Nat) :
    evalJ leanJ fNatDivModId (envAB a b) = true ↔ (¬ b = 0 → a / b * b + a % b = a) := …
-- lean/ToyJunk/Readings.lean:84-85
theorem leanReading_fGuardFirst (a b : Nat) :
    evalJ leanJ fGuardFirst (envAB a b) = true ↔ (b ≤ a ∧ a - b + b = a) := …
-- lean/ToyJunk/Readings.lean:88-89
theorem leanReading_fGuardSecond (a b : Nat) :
    evalJ leanJ fGuardSecond (envAB a b) = true ↔ (a - b + b = a ∧ b ≤ a) := …
-- lean/ToyJunk/Readings.lean:92-93
theorem leanReading_fContrapositive (a b : Nat) :
    evalJ leanJ fContrapositive (envAB a b) = true ↔ (¬ a - b + b = a → ¬ b ≤ a) := …
-- lean/ToyJunk/Readings.lean:96-97
theorem leanReading_fGuardedNatMod (a b : Nat) :
    evalJ leanJ fGuardedNatMod (envAB a b) = true ↔ (¬ b = 0 → a % b < b) := …
-- lean/ToyJunk/Readings.lean:100-101
theorem leanReading_fStaleGuard (a b : Nat) :
    evalJ leanJ fStaleGuard (envAB a b) = true ↔ (b ≤ a ∧ ∀ v : Nat, a - v + v = a) := …
-- lean/ToyJunk/Readings.lean:106-107
theorem leanReading_fDivZero (x : Int) :
    evalJ leanJ fDivZero (envX x) = true ↔ x / 0 = (0 : Int) := …
-- lean/ToyJunk/Readings.lean:110-111
theorem leanReading_fDivZeroRefl (x : Int) :
    evalJ leanJ fDivZeroRefl (envX x) = true ↔ x / (0 : Int) = x / (0 : Int) := …
-- lean/ToyJunk/Readings.lean:114-115
theorem leanReading_fDivZeroEM (x : Int) :
    evalJ leanJ fDivZeroEM (envX x) = true ↔ (x / 0 = (0 : Int) ∨ ¬ x / 0 = (0 : Int)) := …
-- lean/ToyJunk/Readings.lean:118-119
theorem leanReading_fToNatGuardFirst (x : Int) :
    evalJ leanJ fToNatGuardFirst (envX x) = true ↔ (0 ≤ x ∧ x.toNat = x.toNat) := …
-- lean/ToyJunk/Readings.lean:122-123
theorem leanReading_fToNatGuardSecond (x : Int) :
    evalJ leanJ fToNatGuardSecond (envX x) = true ↔ (x.toNat = x.toNat ∧ 0 ≤ x) := …
-- lean/ToyJunk/Readings.lean:126-127
theorem leanReading_fToNatImp (x : Int) :
    evalJ leanJ fToNatImp (envX x) = true ↔ (0 ≤ x → x.toNat = x.toNat) := …
-- lean/ToyJunk/Readings.lean:130-131
theorem leanReading_fToNatContrapose (x : Int) :
    evalJ leanJ fToNatContrapose (envX x) = true ↔ (¬ x.toNat = x.toNat → ¬ 0 ≤ x) := …
-- lean/ToyJunk/Readings.lean:134-135
theorem leanReading_fGuardedToNat (x : Int) :
    evalJ leanJ fGuardedToNat (envX x) = true ↔ (0 ≤ x → ((x.toNat : Nat) : Int) = x) := …
-- lean/ToyJunk/Readings.lean:138-140
theorem leanReading_fGuardedIntMod (ρ : Env) :
    evalJ leanJ fGuardedIntMod ρ = true ↔
      (0 < ρ.int 1 ∧ 0 ≤ ρ.int 0 → ρ.int 0 % ρ.int 1 < ρ.int 1) := …
-- lean/ToyJunk/Readings.lean:143-145
theorem leanReading_fGuardedIntDiv (ρ : Env) :
    evalJ leanJ fGuardedIntDiv ρ = true ↔
      (¬ ρ.int 1 = 0 ∧ ρ.int 1 ∣ ρ.int 0 → ρ.int 0 / ρ.int 1 * ρ.int 1 = ρ.int 0) := …
-- lean/ToyJunk/Readings.lean:150-151
theorem leanReading_fZeroSubOne (ρ : Env) :
    evalJ leanJ fZeroSubOne ρ = true ↔ (0 : Nat) - 1 = 0 := …
-- lean/ToyJunk/Readings.lean:154-155
theorem leanReading_fFiveSubThree (ρ : Env) :
    evalJ leanJ fFiveSubThree ρ = true ↔ (5 : Nat) - 3 = 2 := …
-- lean/ToyJunk/Readings.lean:158-159
theorem leanReading_fNumeralNat (ρ : Env) :
    evalJ leanJ fNumeralNat ρ = true ↔ (2 : Nat) - 3 < 0 := …
-- lean/ToyJunk/Readings.lean:162-163
theorem leanReading_fNumeralInt (ρ : Env) :
    evalJ leanJ fNumeralInt ρ = true ↔ (2 : Int) - 3 < 0 := …
-- lean/ToyJunk/Readings.lean:166-167
theorem leanReading_fTruncSubCancel01 (ρ : Env) :
    evalJ leanJ fTruncSubCancel01 ρ = true ↔ (0 : Nat) - 1 + 1 = 0 := …
-- lean/ToyJunk/Readings.lean:170-171
theorem leanReading_fTruncSubLe01 (ρ : Env) :
    evalJ leanJ fTruncSubLe01 ρ = true ↔ (0 : Nat) - 1 ≤ 0 := …
-- lean/ToyJunk/Readings.lean:174-175
theorem leanReading_fFiveDivZero (ρ : Env) :
    evalJ leanJ fFiveDivZero ρ = true ↔ (5 : Int) / 0 = 0 := …
-- lean/ToyJunk/Readings.lean:178-179
theorem leanReading_fFiveModZero (ρ : Env) :
    evalJ leanJ fFiveModZero ρ = true ↔ (5 : Nat) % 0 = 5 := …
-- lean/ToyJunk/Readings.lean:182-183
theorem leanReading_fFloorDiv (ρ : Env) :
    evalJ leanJ fFloorDiv ρ = true ↔ (7 : Nat) / 2 * 2 = 7 := …
-- lean/ToyJunk/Readings.lean:186-187
theorem leanReading_fNegSevenDivTwo (ρ : Env) :
    evalJ leanJ fNegSevenDivTwo ρ = true ↔ (-7 : Int) / 2 = -4 := …
-- lean/ToyJunk/Readings.lean:190-191
theorem leanReading_fSevenDivNegTwo (ρ : Env) :
    evalJ leanJ fSevenDivNegTwo ρ = true ↔ (7 : Int) / (-2) = -3 := …
-- lean/ToyJunk/Readings.lean:194-195
theorem leanReading_fNegSevenModTwo (ρ : Env) :
    evalJ leanJ fNegSevenModTwo ρ = true ↔ (-7 : Int) % 2 = 1 := …
-- lean/ToyJunk/Readings.lean:198-199
theorem leanReading_fSevenModNegTwo (ρ : Env) :
    evalJ leanJ fSevenModNegTwo ρ = true ↔ (7 : Int) % (-2) = 1 := …
-- lean/ToyJunk/Readings.lean:202-204
theorem leanReading_fCastPlacement01 (ρ : Env) :
    evalJ leanJ fCastPlacement01 ρ = true ↔
      (((0 : Nat) - 1 : Nat) : Int) = ((0 : Nat) : Int) - ((1 : Nat) : Int) := …
-- lean/ToyJunk/Readings.lean:207-208
theorem leanReading_fToNatNeg (ρ : Env) :
    evalJ leanJ fToNatNeg ρ = true ↔ (-3 : Int).toNat = 0 := …
-- lean/ToyJunk/Readings.lean:211-212
theorem leanReading_fSevenDivTwo (ρ : Env) :
    evalJ leanJ fSevenDivTwo ρ = true ↔ (7 : Nat) / 2 = 3 := …
-- lean/ToyJunk/Readings.lean:215-216
theorem leanReading_fSevenModTwo (ρ : Env) :
    evalJ leanJ fSevenModTwo ρ = true ↔ (7 : Nat) % 2 = 1 := …
-- lean/ToyJunk/Readings.lean:219-220
theorem leanReading_fOneDivTwo (ρ : Env) :
    evalJ leanJ fOneDivTwo ρ = true ↔ (1 : Nat) / 2 = 0 := …
-- lean/ToyJunk/Readings.lean:225-226
theorem leanReading_fBoundedCancel (ρ : Env) :
    evalJ leanJ fBoundedCancel ρ = true ↔ ∀ a b : Nat, b ≤ a → a - b + b = a := …
-- lean/ToyJunk/Readings.lean:229-230
theorem leanReading_fUnboundedCancel (ρ : Env) :
    evalJ leanJ fUnboundedCancel ρ = true ↔ ∀ a b : Nat, a - b + b = a := …
-- lean/ToyJunk/Readings.lean:233-234
theorem leanReading_fAllZeroLeSubOne (ρ : Env) :
    evalJ leanJ fAllZeroLeSubOne ρ = true ↔ ∀ a : Nat, 0 ≤ a - 1 := …
-- lean/ToyJunk/Readings.lean:237-238
theorem leanReading_fAllSubSucc (ρ : Env) :
    evalJ leanJ fAllSubSucc ρ = true ↔ ∀ a : Nat, a - (a + 1) = 0 := …
-- lean/ToyJunk/Readings.lean:241-242
theorem leanReading_fExSubSuccNe (ρ : Env) :
    evalJ leanJ fExSubSuccNe ρ = true ↔ ∃ a : Nat, ¬ a - (a + 1) = 0 := …
-- lean/ToyJunk/Readings.lean:245-246
theorem leanReading_fAllOneDivZero (ρ : Env) :
    evalJ leanJ fAllOneDivZero ρ = true ↔ ∀ n : Nat, 2 < n → 1 / n = 0 := …
```

### Supporting theorems cited in non-claims

These proved theorems back the non-claims and remarks of several results (Boundaries). Each is listed in `results.json` under `lean_names` of the citing results and carries a statement hash in Evidence.

```lean
-- lean/ToyJunk/Guarded.lean:442-450
theorem inexact_division_is_junk (c : Conn) (r : SubReading) :
    (evalT leanJ Env.zero (.div (.natLit 7) (.natLit 2)) = (3 : Nat) ∧
        evalT truncJ Env.zero (.div (.natLit 7) (.natLit 2)) = (3 : Nat) ∧
        evalT floorJ Env.zero (.div (.natLit 7) (.natLit 2)) = (3 : Nat) ∧
        evalT oneJ Env.zero (.div (.natLit 7) (.natLit 2)) = (1 : Nat)) ∧
      ¬ JunkIndependent fSevenDivTwo ∧ hEval c r fSevenDivTwo Env.zero = none ∧
      JunkIndependent fSevenModTwo ∧ hEval c r fSevenModTwo Env.zero = some true ∧
      LeanValid fNatDivModId ∧ guarded fNatDivModId = false ∧
      ¬ JunkIndependent fNatDivModId ∧ ¬ DefinedEverywhere c r fNatDivModId := …
-- lean/ToyJunk/Agreement.lean:191-192
theorem agreesWhereDefined_partialNat (c : Conn) (J : Junk) (φ : Formula) :
    AgreesWhereDefined c .partialNat J φ := …
-- lean/ToyJunk/Guarded.lean:397-401
theorem guarded_accepts_vacuous_guards (c : Conn) (r : SubReading) :
    (guarded fContradictoryGuard = true ∧ LeanValid fContradictoryGuard ∧
        HumanValid c r fContradictoryGuard) ∧
      (guarded fExImpGuard = true ∧ LeanValid fExImpGuard ∧ HumanValid c r fExImpGuard) ∧
      ¬ LeanValid fExAndGuard := …
-- lean/ToyJunk/Quantifiers.lean:255-259
theorem guarded_rejects_strict_bound :
    (guarded (.allNat 0 (.allNat 1 (.imp (.lt vB vA) fSubAddCancel))) = false ∧
        LeanValid (.allNat 0 (.allNat 1 (.imp (.lt vB vA) fSubAddCancel)))) ∧
      (guarded (.allNat 0 (.allNat 1 (.imp (.lt vB (.add vA (.natLit 1))) fSubAddCancel))) = false ∧
        LeanValid (.allNat 0 (.allNat 1 (.imp (.lt vB (.add vA (.natLit 1))) fSubAddCancel)))) := …
-- lean/ToyJunk/Guarded.lean:578-580
theorem seq_defined_intValued :
    DefinedEverywhere .seq .intValued fGuardSecond ∧
      DefinedEverywhere .seq .intValued fContrapositive := …
-- lean/ToyJunk/Traps.lean:280-283
theorem ce_shallow_cast_nested_sub :
    hEvalT .intValued Env.zero (.sub (.sub (.natLit 0) (.natLit 1)) (.natLit 0)) = some (-1) ∧
      evalT leanJ Env.zero (.sub (.cast (.sub (.natLit 0) (.natLit 1))) (.cast (.natLit 0))) =
        (0 : Int) := …
```

(`kleene_tables`, `seq_tables` and `kleene_quantifier_tables` are quoted under *Connective tables*; `AgreesWhereDefined_pos`, `AgreesWhereDefined_neg` under *Definition examples*; `agreesWhereDefined_partialNat` in R4.)

### Results

The 27 result cards follow, numbered R0 to R26 in the order of `results.json`.

### R0. lean_reading_is_junk_record_leanJ

**Kind:** theorem · **Tier:** T1 · **Depth:** shallow

**Plain claim.** For every environment rho and every toy term t, the junk-parameterized total value of t at the junk record leanJ equals the value computed directly with Lean's core operators (truncated Nat subtraction, Nat floor division and remainder, the default Int / and % which are Int.ediv and Int.emod, Int.toNat, and the cast Nat -> Int); and for every toy formula phi and environment rho, evalJ leanJ phi rho = true iff the Lean proposition leanEvalF phi rho, built from Lean's operators and relations at the native sort, holds.

**Tier rationale.** Folklore ('Lean's arithmetic is exact arithmetic plus one choice of junk values') made precise for this toy language; no mechanized statement of it was found.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Lemmas.lean:236
theorem evalJ_leanJ_iff : ∀ (φ : Formula) (ρ : Env), evalJ leanJ φ ρ = true ↔ leanEvalF φ ρ := …
-- lean/ToyJunk/Lemmas.lean:197
theorem evalT_leanJ (ρ : Env) : ∀ {s : Srt} (t : Term s), evalT leanJ ρ t = leanEvalT ρ t := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No hypotheses: both statements are universal over all terms, formulas and environments (vacuous).

**Supporting theorems:** `inexact_division_is_junk` (quoted under *Supporting theorems*), and the 55 `leanReading_*` theorems (instances of `evalJ_leanJ_iff`, quoted under *Named formulas*).

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [L1] Lean core v4.34.1 `src/Init/Prelude.lean` (`Nat.sub`, `Nat.div`, `Nat.modCore`)
- [L2] Lean core v4.34.1 `src/Init/Data/Int/DivMod/Basic.lean` (`Int.ediv`, `Int.emod`, `Int.div`, `Int.mod`)
- [L3] Lean core v4.34.1 `src/Init/Data/Int/Basic.lean` (`Int.toNat`)
- [P1] Lean Prover Community (web page)

**Design question.** Is the folklore statement 'Lean's arithmetic is exact arithmetic plus one particular choice of junk values' exactly true of Lean's core operators?

Basis: execution (Lean kernel check) — `evalJ_leanJ_iff`, `evalT_leanJ`.

Basis: derived (modeling bridge) — A Lean statement over `Nat` and `Int` built from these operators and relations denotes the same proposition as `leanEvalF` of the corresponding toy formula, because `leanEvalT` and `leanEvalF` are written with the same core operators. The toy does not model how a source statement elaborates (coercions, numeral defaulting), so the correspondence has to be checked statement by statement.

Non-claims: Boundaries, *Non-claims*, R0.

### R1. agreement_where_defined_partialNat

**Kind:** theorem · **Tier:** T1 · **Depth:** shallow

**Plain claim.** Under the human reading in which natural subtraction below zero is undefined (partialNat), for either connective semantics (strong Kleene or sequential), every junk record J, every toy formula phi, every environment rho and every b: if the three-valued human value of phi at rho is defined and equal to b, then the total value of phi at rho under J equals b. Equivalently, under partialNat and for either connective semantics, there is no toy formula (quantified or not), environment and junk record at which the human value is false and the total value true, or the human value is true and the total value false.

**Tier rationale.** The idea that a two-valued completion agrees with a three-valued value wherever the latter is defined is known informally (Gries and Schneider 1995; Darvas, Mehta and Rudich 2008); the nearest mechanization found (Schmalz 2012) concerns Event-B's logic in Isabelle/HOL, a different formalism and statement.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Agreement.lean:125-127
theorem evalJ_eq_of_hEval_eq_some_partialNat (c : Conn) (J : Junk) :
    ∀ (φ : Formula) (ρ : Env) (b : Bool),
      hEval c .partialNat φ ρ = some b → evalJ J φ ρ = b := …
-- lean/ToyJunk/Agreement.lean:360-362
theorem no_flip_partialNat (c : Conn) (J : Junk) (φ : Formula) (ρ : Env) :
    ¬ (hEval c .partialNat φ ρ = some false ∧ evalJ J φ ρ = true) ∧
      ¬ (hEval c .partialNat φ ρ = some true ∧ evalJ J φ ρ = false) := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fNumeralNat`: `(2 : Nat) - 3 < 0` (closed; `leanReading_fNumeralNat`)
- `fAllZeroLeSubOne`: `∀ a : Nat, 0 ≤ a - 1` (closed; `leanReading_fAllZeroLeSubOne`)
- `fDivZero`: `x / 0 = (0 : Int)` (with `x : Int`; `leanReading_fDivZero`)
- `fFiveSubThree`: `(5 : Nat) - 3 = 2` (closed; `leanReading_fFiveSubThree`)

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| reading = partialNat (both theorems) | Natural subtraction below zero must be undefined in the human reading; if it is evaluated in Z, a defined human value can differ from the total value. | tight | `ce_agreement_intValued`, `ce_intValued_forall_humanFalse_leanTrue` | closed formulas under the intValued reading: the quantifier-free (2 : Nat) - 3 < 0 (fNumeralNat; human true, Lean false) and the universal statement for all a : Nat, 0 <= a - 1 (fAllZeroLeSubOne; human false, Lean true) |
| h : hEval c partialNat phi rho = some b (evalJ_eq_of_hEval_eq_some_partialNat) | Agreement is claimed where the human value is defined, and not elsewhere. | tight | `ce_agreement_undefined` | an atom with one Int variable, (x : Int) / 0 = 0 (fDivZero), at the zero environment, with b = false and J = leanJ |

Counterexample statements:

```lean
-- lean/ToyJunk/Agreement.lean:244-246
theorem ce_agreement_intValued (c : Conn) :
    hEval c .intValued fNumeralNat Env.zero = some true ∧
      evalJ leanJ fNumeralNat Env.zero = false := …
-- lean/ToyJunk/Quantifiers.lean:336-338
theorem ce_intValued_forall_humanFalse_leanTrue (c : Conn) :
    hEval c .intValued fAllZeroLeSubOne Env.zero = some false ∧
      evalJ leanJ fAllZeroLeSubOne Env.zero = true := …
-- lean/ToyJunk/Agreement.lean:252-253
theorem ce_agreement_undefined (c : Conn) :
    hEval c .partialNat fDivZero Env.zero = none ∧ evalJ leanJ fDivZero Env.zero ≠ false := …
```

**Non-vacuity.** (5 : Nat) - 3 = 2 (fFiveSubThree) has the defined human value true under partialNat with either connectives; (5 : Nat) - 3 = 3 has the defined human value false.

```lean
-- lean/ToyJunk/Agreement.lean:223-224
theorem nv_evalJ_eq_of_hEval_eq_some_partialNat (c : Conn) :
    hEval c .partialNat fFiveSubThree Env.zero = some true := …
-- lean/ToyJunk/Quantifiers.lean:329-330
theorem nv_hEval_eq_some_false_partialNat (c : Conn) :
    hEval c .partialNat (.eq (.sub (.natLit 5) (.natLit 3)) (.natLit 3)) Env.zero = some false := …
```

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `kleene_tables`, `seq_tables`, `kleene_quantifier_tables`.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P2] David Gries and Fred B. Schneider (1995)
- [P3] S. C. Kleene (1952)
- [P4] John McCarthy (1963)
- [P5] Adam Darvas, Farhad Mehta and Arsenii Rudich (2008)
- [P6] Matthias Schmalz (2012)

**Design question.** Can a reader trust a statement's Lean truth value at every point where the statement's exact human reading is meaningful?

Basis: execution (Lean kernel check) — `evalJ_eq_of_hEval_eq_some_partialNat`, `no_flip_partialNat`.

Basis: derived (modeling bridge) — For a statement that lies in the toy language, a reader whose exact meaning is `hEval c .partialNat` (in particular, who reads `/` as exact division and natural subtraction below zero as undefined) can trust Lean's truth value wherever that meaning is defined. A reader who evaluates natural subtraction in the integers is in the `intValued` case, where the counterexamples of this card apply.

Non-claims: Boundaries, *Non-claims*, R1.

### R2. definedEverywhere_implies_junkIndependent

**Kind:** theorem · **Tier:** T1 · **Depth:** shallow

**Plain claim.** Under the partialNat reading, for either connective semantics and every toy formula phi: if the human value of phi is defined at every environment, then phi is junk-independent (at every environment its total value is the same for every two junk records).

**Tier rationale.** Same status as agreement_where_defined_partialNat, of which it is a corollary.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Agreement.lean:196-197
theorem junkIndependent_of_definedEverywhere_partialNat (c : Conn) (φ : Formula)
    (h : DefinedEverywhere c .partialNat φ) : JunkIndependent φ := …
```

Unfolded (`junkIndependent_of_definedEverywhere_partialNat`), with `DefinedEverywhere` and `JunkIndependent` expanded:
```lean
∀ (c : Conn) (φ : Formula), (∀ ρ : Env, hEval c .partialNat φ ρ ≠ none) →
  ∀ (J J' : Junk) (ρ : Env), evalJ J φ ρ = evalJ J' φ ρ
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fZeroSubOne`: `(0 : Nat) - 1 = 0` (closed; `leanReading_fZeroSubOne`)
- `fFiveSubThree`: `(5 : Nat) - 3 = 2` (closed; `leanReading_fFiveSubThree`)

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| DefinedEverywhere c partialNat phi | Definedness at every environment is what forces every junk record to agree. | tight | `ce_zeroSubOne_junkDependent` | a closed atom, (0 : Nat) - 1 = 0 (fZeroSubOne), undefined everywhere under partialNat and junk-dependent |
| reading = partialNat | Under intValued a defined human value need not constrain the junk values. | tight | `ce_zeroSubOne_junkDependent` | the same closed atom, defined everywhere under intValued and junk-dependent |

Counterexample statements:

```lean
-- lean/ToyJunk/Agreement.lean:296-298
theorem ce_zeroSubOne_junkDependent (c : Conn) :
    ¬ JunkIndependent fZeroSubOne ∧ (∀ ρ, hEval c .partialNat fZeroSubOne ρ = none) ∧
      DefinedEverywhere c .intValued fZeroSubOne := …
```

**Non-vacuity.** (5 : Nat) - 3 = 2 (fFiveSubThree) is defined at every environment under partialNat.

```lean
-- lean/ToyJunk/Agreement.lean:229-230
theorem nv_definedEverywhere_partialNat (c : Conn) :
    DefinedEverywhere c .partialNat fFiveSubThree := …
```

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `inexact_division_is_junk`.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P2] David Gries and Fred B. Schneider (1995) — for this result: Its underspecified terms may take different values at different occurrences, whereas a junk record of this package assigns values as a function of the operands.

**Design question.** Which properties of a formula (definedness of its exact human reading at every environment, junk independence, agreement where defined) guarantee that its truth value in Lean's reading matches its exact human reading?

Basis: execution (Lean kernel check) — `junkIndependent_of_definedEverywhere_partialNat`.

Non-claims: Boundaries, *Non-claims*, R2.

### R3. junkIndependent_does_not_imply_defined

**Kind:** counterexample · **Tier:** T1 · **Depth:** shallow

**Plain claim.** For each connective semantics c: (a b : Nat), (a - b) * 0 = 0 (fMulZero) is junk-independent, but its partialNat human value is undefined at a = 0, b = 1 (undefinedness propagates strictly through * 0), so it is not defined everywhere. For each connective semantics c and reading r: (x : Int) / 0 = x / 0 (fDivZeroRefl) and (x : Int) / 0 = 0 OR NOT (x / 0 = 0) (fDivZeroEM) contain no multiplication, are Lean-valid and junk-independent, and are human-undefined at every environment. So junk independence implies neither definedness nor human validity.

**Tier rationale.** Instances of a known gap between totalized and three-valued readings (Gries and Schneider 1995, Section 2, on excluded middle) worked out for this toy language.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Agreement.lean:259-261
theorem ce_junkIndependent_not_definedEverywhere (c : Conn) :
    JunkIndependent fMulZero ∧ hEval c .partialNat fMulZero (envAB 0 1) = none ∧
      ¬ DefinedEverywhere c .partialNat fMulZero := …
-- lean/ToyJunk/Agreement.lean:324-328
theorem ce_junkIndependent_leanValid_undefined (c : Conn) (r : SubReading) :
    (LeanValid fDivZeroRefl ∧ JunkIndependent fDivZeroRefl ∧
        ∀ ρ, hEval c r fDivZeroRefl ρ = none) ∧
      (LeanValid fDivZeroEM ∧ JunkIndependent fDivZeroEM ∧
        ∀ ρ, hEval c r fDivZeroEM ρ = none) := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fMulZero`: `(a - b) * 0 = (0 : Nat)` (with `a b : Nat`; `leanReading_fMulZero`)
- `fDivZeroRefl`: `x / (0 : Int) = x / (0 : Int)` (with `x : Int`; `leanReading_fDivZeroRefl`)
- `fDivZeroEM`: `x / 0 = (0 : Int) ∨ ¬ x / 0 = (0 : Int)` (with `x : Int`; `leanReading_fDivZeroEM`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). ce_junkIndependent_not_definedEverywhere quantifies over c : Conn, and ce_junkIndependent_leanValid_undefined over c : Conn and r : SubReading; both types are inhabited (Conn by kleene and seq, SubReading by partialNat and intValued). The quantifier over environments rho inside the second statement is part of its conclusion, not a hypothesis.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P2] David Gries and Fred B. Schneider (1995)

**Design question.** Which properties of a formula (definedness of its exact human reading at every environment, junk independence, agreement where defined) guarantee that its truth value in Lean's reading matches its exact human reading?

Basis: execution (Lean kernel check) — `ce_junkIndependent_not_definedEverywhere`, `ce_junkIndependent_leanValid_undefined`.

Non-claims: Boundaries, *Non-claims*, R3.

### R4. agreement_does_not_imply_junkIndependent_or_definedness

**Kind:** counterexample · **Tier:** T1 · **Depth:** shallow

**Plain claim.** For each connective semantics c: (a b : Nat), a - b <= a (fSubLeSelf) agrees with the partialNat human reading wherever that is defined, for every junk record (AgreesWhereDefined c partialNat J, which holds for every formula by agreesWhereDefined_partialNat); it is Lean-valid; it is junk-dependent (with every junk value equal to 1, the record oneJ, it is false at a = 0, b = 1); and its human value is undefined at a = 0, b = 1, so it is not defined everywhere. Hence agreement-where-defined implies neither junk independence nor definedness everywhere.

**Tier rationale.** A concrete instance in this toy language; no prior statement of it was found.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Agreement.lean:273-278
theorem ce_agrees_not_junkIndependent (c : Conn) :
    (∀ J : Junk, AgreesWhereDefined c .partialNat J fSubLeSelf) ∧
      LeanValid fSubLeSelf ∧ evalJ oneJ fSubLeSelf (envAB 0 1) = false ∧
      ¬ JunkIndependent fSubLeSelf ∧
      hEval c .partialNat fSubLeSelf (envAB 0 1) = none ∧
      ¬ DefinedEverywhere c .partialNat fSubLeSelf := …
```

Unfolded (`ce_agrees_not_junkIndependent`), with `AgreesWhereDefined`, `LeanValid`, `JunkIndependent` and `DefinedEverywhere` expanded:
```lean
∀ (c : Conn),
  (∀ (J : Junk) (ρ : Env) (b : Bool), hEval c .partialNat fSubLeSelf ρ = some b → evalJ J fSubLeSelf ρ = b) ∧
    (∀ ρ : Env, evalJ leanJ fSubLeSelf ρ = true) ∧ evalJ oneJ fSubLeSelf (envAB 0 1) = false ∧
    ¬ (∀ (J J' : Junk) (ρ : Env), evalJ J fSubLeSelf ρ = evalJ J' fSubLeSelf ρ) ∧
    hEval c .partialNat fSubLeSelf (envAB 0 1) = none ∧
    ¬ (∀ ρ : Env, hEval c .partialNat fSubLeSelf ρ ≠ none)
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fSubLeSelf`: `a - b ≤ a` (with `a b : Nat`; `leanReading_fSubLeSelf`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). The sole parameter of ce_agrees_not_junkIndependent is c : Conn (inhabited by kleene and seq); the reading is fixed to partialNat, and the quantifier over junk records J inside the statement is part of its conclusion. The supporting theorem agreesWhereDefined_partialNat (quoted under Supporting theorems) is universal over c, J and phi and has no hypotheses.

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `agreesWhereDefined_partialNat`, `AgreesWhereDefined_pos`, `AgreesWhereDefined_neg`.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [L1] Lean core v4.34.1 `src/Init/Prelude.lean` (`Nat.sub`, `Nat.div`, `Nat.modCore`)

**Design question.** Which properties of a formula (definedness of its exact human reading at every environment, junk independence, agreement where defined) guarantee that its truth value in Lean's reading matches its exact human reading?

Basis: execution (Lean kernel check) — `ce_agrees_not_junkIndependent`.

Non-claims: Boundaries, *Non-claims*, R4.

### R5. validity_transfer_partialNat

**Kind:** theorem · **Tier:** T1 · **Depth:** shallow

**Plain claim.** Under the partialNat reading, for either connective semantics and every toy formula phi: if phi is human-valid (defined and true at every environment) then phi is valid in Lean's reading (true at every environment for leanJ); and if the human value of phi is defined at every environment, then phi is valid in Lean's reading iff it is human-valid.

**Tier rationale.** Same status as agreement_where_defined_partialNat, of which both parts are corollaries.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Agreement.lean:204-205
theorem leanValid_of_humanValid_partialNat (c : Conn) (φ : Formula)
    (h : HumanValid c .partialNat φ) : LeanValid φ := …
-- lean/ToyJunk/Agreement.lean:209-210
theorem leanValid_iff_humanValid_of_definedEverywhere_partialNat (c : Conn) (φ : Formula)
    (h : DefinedEverywhere c .partialNat φ) : LeanValid φ ↔ HumanValid c .partialNat φ := …
```

Unfolded (`leanValid_of_humanValid_partialNat`), with `HumanValid` and `LeanValid` expanded:
```lean
∀ (c : Conn) (φ : Formula), (∀ ρ : Env, hEval c .partialNat φ ρ = some true) →
  ∀ ρ : Env, evalJ leanJ φ ρ = true
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fSubAddCancel`: `a - b + b = a` (with `a b : Nat`; `leanReading_fSubAddCancel`)
- `fDivZero`: `x / 0 = (0 : Int)` (with `x : Int`; `leanReading_fDivZero`)
- `fFiveSubThree`: `(5 : Nat) - 3 = 2` (closed; `leanReading_fFiveSubThree`)

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| HumanValid c partialNat phi (leanValid_of_humanValid_partialNat) | The first transfer starts from human validity. | tight | `ce_not_humanValid_not_leanValid` | an open quantifier-free formula with two Nat variables, (a b : Nat), a - b + b = a (fSubAddCancel), neither human-valid under partialNat nor Lean-valid |
| DefinedEverywhere c partialNat phi (leanValid_iff_humanValid_of_definedEverywhere_partialNat) | Without definedness, Lean validity can hold where the human reading is undefined. | tight | `ce_leanValid_not_humanValid` | an open atom with one Int variable, (x : Int) / 0 = 0 (fDivZero), Lean-valid and never human-defined |
| reading = partialNat (both theorems) | Under intValued, a formula can be defined everywhere and human-valid without being Lean-valid. | tight | `ce_intValued_humanValid_not_leanValid`, `ce_intValued_definedEverywhere_humanValid_not_leanValid` | (a b : Nat), a - b + b = a (fSubAddCancel) under intValued: defined everywhere and human-valid, not Lean-valid |

Counterexample statements:

```lean
-- lean/ToyJunk/Agreement.lean:345-346
theorem ce_not_humanValid_not_leanValid (c : Conn) :
    ¬ HumanValid c .partialNat fSubAddCancel ∧ ¬ LeanValid fSubAddCancel := …
-- lean/ToyJunk/Agreement.lean:311-312
theorem ce_leanValid_not_humanValid (c : Conn) (r : SubReading) :
    LeanValid fDivZero ∧ (∀ ρ, hEval c r fDivZero ρ = none) ∧ ¬ HumanValid c r fDivZero := …
-- lean/ToyJunk/Agreement.lean:369-370
theorem ce_intValued_humanValid_not_leanValid (c : Conn) :
    HumanValid c .intValued fSubAddCancel ∧ ¬ LeanValid fSubAddCancel := …
-- lean/ToyJunk/Agreement.lean:383-385
theorem ce_intValued_definedEverywhere_humanValid_not_leanValid (c : Conn) :
    DefinedEverywhere c .intValued fSubAddCancel ∧ HumanValid c .intValued fSubAddCancel ∧
      ¬ LeanValid fSubAddCancel := …
```

**Non-vacuity.** (5 : Nat) - 3 = 2 (fFiveSubThree) is human-valid and defined at every environment under partialNat.

```lean
-- lean/ToyJunk/Agreement.lean:235
theorem nv_humanValid_partialNat (c : Conn) : HumanValid c .partialNat fFiveSubThree := …
-- lean/ToyJunk/Agreement.lean:229-230
theorem nv_definedEverywhere_partialNat (c : Conn) :
    DefinedEverywhere c .partialNat fFiveSubThree := …
```

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P2] David Gries and Fred B. Schneider (1995)
- [P5] Adam Darvas, Farhad Mehta and Arsenii Rudich (2008)

**Design question.** Which properties of a formula (definedness of its exact human reading at every environment, junk independence, agreement where defined) guarantee that its truth value in Lean's reading matches its exact human reading?

Basis: execution (Lean kernel check) — `leanValid_of_humanValid_partialNat`, `leanValid_iff_humanValid_of_definedEverywhere_partialNat`.

Non-claims: Boundaries, *Non-claims*, R5.

### R6. guarded_fragment_conservativity

**Kind:** theorem · **Tier:** T0 · **Depth:** substantive

**Plain claim.** For every toy formula phi accepted by the decidable guard checker guarded (each Nat subtraction a - b needs the fact b <= a; each division n / d, at Nat or at Int, needs the facts not (d = 0) and d | n; each Nat remainder n % d needs not (d = 0); each Int remainder n % d needs 0 < d and 0 <= n; each Int.toNat t (t : Int) needs 0 <= t; facts are matched syntactically and accumulate left to right through the earlier conjuncts of AND and the premise of IMPLIES, and facts mentioning a variable are discarded under a quantifier that binds it), for every connective semantics c, every reading r of natural subtraction, every junk record J and every environment rho, the human value of phi at rho is defined and equals the total value of phi at rho under J. In particular every formula accepted by guarded is defined everywhere (for every c and r) and junk-independent.

**Tier rationale.** Restates, for this toy language and the checker guarded, the known principle that proving left-to-right well-definedness conditions licenses two-valued reasoning about a three-valued specification language (Darvas, Mehta and Rudich 2008).

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Guarded.lean:264-265
theorem hEval_eq_some_evalJ_of_guarded (c : Conn) (r : SubReading) (J : Junk) (φ : Formula)
    (ρ : Env) (hg : guarded φ = true) : hEval c r φ ρ = some (evalJ J φ ρ) := …
-- lean/ToyJunk/Guarded.lean:269-270
theorem definedEverywhere_of_guarded (c : Conn) (r : SubReading) (φ : Formula)
    (hg : guarded φ = true) : DefinedEverywhere c r φ := …
-- lean/ToyJunk/Guarded.lean:276-277
theorem junkIndependent_of_guarded (φ : Formula) (hg : guarded φ = true) :
    JunkIndependent φ := …
```

Unfolded (`definedEverywhere_of_guarded`), with `DefinedEverywhere` expanded:
```lean
∀ (c : Conn) (r : SubReading) (φ : Formula), guarded φ = true → ∀ ρ : Env, hEval c r φ ρ ≠ none
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fDivZero`: `x / 0 = (0 : Int)` (with `x : Int`; `leanReading_fDivZero`)
- `fZeroSubOne`: `(0 : Nat) - 1 = 0` (closed; `leanReading_fZeroSubOne`)
- `fSubAddCancelGuarded`: `b ≤ a → a - b + b = a` (with `a b : Nat`; `leanReading_fSubAddCancelGuarded`)
- `fDvdDivGuarded`: `¬ b = 0 → b ∣ a → a / b * b = a` (with `a b : Nat`; `leanReading_fDvdDivGuarded`)
- `fBoundedCancel`: `∀ a b : Nat, b ≤ a → a - b + b = a` (closed; `leanReading_fBoundedCancel`)
- `fGuardedNatMod`: `¬ b = 0 → a % b < b` (with `a b : Nat`; `leanReading_fGuardedNatMod`)
- `fGuardedIntMod`: `0 < ρ.int 1 ∧ 0 ≤ ρ.int 0 → ρ.int 0 % ρ.int 1 < ρ.int 1` (where `ρ.int 0` (for `vX`) and `ρ.int 1` (for `vY`) are integers; `leanReading_fGuardedIntMod`)
- `fGuardedIntDiv`: `¬ ρ.int 1 = 0 ∧ ρ.int 1 ∣ ρ.int 0 → ρ.int 0 / ρ.int 1 * ρ.int 1 = ρ.int 0` (where `ρ.int 0` (for `vX`) and `ρ.int 1` (for `vY`) are integers; `leanReading_fGuardedIntDiv`)
- `fGuardedToNat`: `0 ≤ x → ((x.toNat : Nat) : Int) = x` (with `x : Int`; `leanReading_fGuardedToNat`)

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| guarded phi = true (hEval_eq_some_evalJ_of_guarded, definedEverywhere_of_guarded) | The guards are what make every partial operation defined. | tight | `ce_unguarded_divZero` | an open atom with one Int variable, (x : Int) / 0 = 0 (fDivZero), rejected and undefined at every environment |
| guarded phi = true (junkIndependent_of_guarded) | Unguarded formulas can depend on junk values. | tight | `ce_unguarded_junkDependent` | a closed atom, (0 : Nat) - 1 = 0 (fZeroSubOne), rejected and junk-dependent |

Counterexample statements:

```lean
-- lean/ToyJunk/Guarded.lean:303-304
theorem ce_unguarded_divZero (c : Conn) (r : SubReading) :
    guarded fDivZero = false ∧ ∀ ρ, hEval c r fDivZero ρ = none := …
-- lean/ToyJunk/Guarded.lean:318-319
theorem ce_unguarded_junkDependent :
    guarded fZeroSubOne = false ∧ ¬ JunkIndependent fZeroSubOne := …
```

**Non-vacuity.** (a b : Nat), b <= a -> a - b + b = a (fSubAddCancelGuarded) is accepted by the checker; each partial-operation rule has an accepted instance (guarded_pos).

```lean
-- lean/ToyJunk/Guarded.lean:299
theorem nv_guarded_subAddCancel : guarded fSubAddCancelGuarded = true := …
-- lean/ToyJunk/Examples.lean:230-234
theorem guarded_pos :
    guarded fSubAddCancelGuarded = true ∧ guarded fDvdDivGuarded = true ∧
      guarded fBoundedCancel = true ∧ guarded fGuardedNatMod = true ∧
      guarded fGuardedIntMod = true ∧ guarded fGuardedIntDiv = true ∧
      guarded fGuardedToNat = true := …
```

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `inexact_division_is_junk`, `guarded_accepts_vacuous_guards`, `guarded_rejects_strict_bound`.

**Depth:** substantive.

**Prior art** (full records under Evidence, *Sources*):

- [P5] Adam Darvas, Farhad Mehta and Arsenii Rudich (2008)
- [P6] Matthias Schmalz (2012)
- [P7] John Rushby, Sam Owre and Natarajan Shankar (1998)
- [P8] Matt Kaufmann and J Strother Moore (1997)
- [P2] David Gries and Fred B. Schneider (1995)
- [P9] Kevin Buzzard (2020)

**Design question.** Is there a decidable syntactic discipline (guards for every partial operation, explicit casts) on which the exact human reading and the total reading provably coincide?

Basis: execution (Lean kernel check) — `hEval_eq_some_evalJ_of_guarded`, `definedEverywhere_of_guarded`, `junkIndependent_of_guarded`.

Basis: derived (modeling bridge) — Writing a statement so that every partial operation is preceded by its guard as a hypothesis (`b ≤ a` before the `Nat` subtraction `a - b`, `¬ (d = 0)` and `d ∣ n` before a division `n / d` at `Nat` or `Int`, and so on) makes Lean's truth value coincide with the exact reading, for statements expressible in the toy language. This matches the idiom of stating side conditions as hypotheses described by Buzzard (2020); the toy gives no procedure for translating Lean source statements, so the bridge is an argument, not a check.

Non-claims: Boundaries, *Non-claims*, R6.

### R7. guarded_validity_transfer

**Kind:** theorem · **Tier:** T0 · **Depth:** shallow

**Plain claim.** For every connective semantics c, every reading r of natural subtraction and every toy formula phi accepted by guarded, phi is valid in Lean's reading iff it is human-valid. For instance, for every c and r, (a b : Nat), b <= a -> a - b + b = a (fSubAddCancelGuarded) is accepted by guarded, Lean-valid and human-valid.

**Tier rationale.** A corollary of guarded_fragment_conservativity; same status.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Guarded.lean:286-287
theorem leanValid_iff_humanValid_of_guarded (c : Conn) (r : SubReading) (φ : Formula)
    (hg : guarded φ = true) : LeanValid φ ↔ HumanValid c r φ := …
-- lean/ToyJunk/Traps.lean:228-230
theorem restate_subAddCancel_guarded (c : Conn) (r : SubReading) :
    guarded fSubAddCancelGuarded = true ∧ LeanValid fSubAddCancelGuarded ∧
      HumanValid c r fSubAddCancelGuarded := …
```

Unfolded (`leanValid_iff_humanValid_of_guarded`), with `LeanValid` and `HumanValid` expanded:
```lean
∀ (c : Conn) (r : SubReading) (φ : Formula), guarded φ = true →
  ((∀ ρ : Env, evalJ leanJ φ ρ = true) ↔ ∀ ρ : Env, hEval c r φ ρ = some true)
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fSubAddCancelGuarded`: `b ≤ a → a - b + b = a` (with `a b : Nat`; `leanReading_fSubAddCancelGuarded`)
- `fDivZero`: `x / 0 = (0 : Int)` (with `x : Int`; `leanReading_fDivZero`)

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| guarded phi = true (leanValid_iff_humanValid_of_guarded) | Unguarded formulas can be Lean-valid with no defined human value. | tight | `ce_unguarded_leanValid_not_humanValid` | an open atom with one Int variable, (x : Int) / 0 = 0 (fDivZero), rejected, Lean-valid, not human-valid |

Counterexample statements:

```lean
-- lean/ToyJunk/Guarded.lean:311-312
theorem ce_unguarded_leanValid_not_humanValid (c : Conn) (r : SubReading) :
    guarded fDivZero = false ∧ LeanValid fDivZero ∧ ¬ HumanValid c r fDivZero := …
```

**Non-vacuity.** (a b : Nat), b <= a -> a - b + b = a (fSubAddCancelGuarded) is accepted.

```lean
-- lean/ToyJunk/Guarded.lean:299
theorem nv_guarded_subAddCancel : guarded fSubAddCancelGuarded = true := …
```

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `guarded_accepts_vacuous_guards`.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P5] Adam Darvas, Farhad Mehta and Arsenii Rudich (2008)
- [P2] David Gries and Fred B. Schneider (1995)
- [P9] Kevin Buzzard (2020)

**Design question.** Is there a decidable syntactic discipline (guards for every partial operation, explicit casts) on which the exact human reading and the total reading provably coincide?

Basis: execution (Lean kernel check) — `leanValid_iff_humanValid_of_guarded`, `restate_subAddCancel_guarded`.

Non-claims: Boundaries, *Non-claims*, R7.

### R8. guard_checker_incomplete

**Kind:** counterexample · **Tier:** T1 · **Depth:** shallow

**Plain claim.** The guard checker guarded rejects formulas that are well behaved: (a b : Nat), (a - b) * 0 = 0 (fMulZero), which is junk-independent; for each connective semantics, (a b : Nat), (0 : Nat) <= 0 OR a - b = 0 (fTrivOr), which is human-valid under partialNat (its left disjunct is true and both semantics return true for a disjunction whose left side is true), while the checker's rule for OR checks both disjuncts against the same facts; for each connective semantics and reading, (a b : Nat), NOT (b <= a) OR a - b + b = a (fOrNegGuardSubCancel) and (a b : Nat), b = 0 OR a % b < b (fModDisjGuard), which are human-valid, because the checker adds no facts across OR; and, under strong Kleene connectives and either reading, (a b : Nat), a - b + b = a AND b <= a (fGuardSecond), which is defined at every environment.

**Tier rationale.** Instances for this checker; the asymmetry of left-to-right well-definedness operators is known (Darvas, Mehta and Rudich 2008), the particular instances are not taken from a source.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Guarded.lean:324-325
theorem guarded_incomplete_junkIndependent :
    guarded fMulZero = false ∧ JunkIndependent fMulZero := …
-- lean/ToyJunk/Guarded.lean:336-337
theorem guarded_incomplete_defined (c : Conn) :
    guarded fTrivOr = false ∧ HumanValid c .partialNat fTrivOr := …
-- lean/ToyJunk/Guarded.lean:352-354
theorem guarded_incomplete_disjunctive_guards (c : Conn) (r : SubReading) :
    (guarded fOrNegGuardSubCancel = false ∧ HumanValid c r fOrNegGuardSubCancel) ∧
      (guarded fModDisjGuard = false ∧ HumanValid c r fModDisjGuard) := …
-- lean/ToyJunk/Guarded.lean:539-540
theorem definedEverywhere_kleene_guardSecond (r : SubReading) :
    guarded fGuardSecond = false ∧ DefinedEverywhere .kleene r fGuardSecond := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fMulZero`: `(a - b) * 0 = (0 : Nat)` (with `a b : Nat`; `leanReading_fMulZero`)
- `fTrivOr`: `(0 : Nat) ≤ 0 ∨ a - b = 0` (with `a b : Nat`; `leanReading_fTrivOr`)
- `fOrNegGuardSubCancel`: `¬ b ≤ a ∨ a - b + b = a` (with `a b : Nat`; `leanReading_fOrNegGuardSubCancel`)
- `fModDisjGuard`: `b = 0 ∨ a % b < b` (with `a b : Nat`; `leanReading_fModDisjGuard`)
- `fGuardSecond`: `a - b + b = a ∧ b ≤ a` (with `a b : Nat`; `leanReading_fGuardSecond`)
- `fGuardFirst`: `b ≤ a ∧ a - b + b = a` (with `a b : Nat`; `leanReading_fGuardFirst`)
- `fSubAddCancelGuarded`: `b ≤ a → a - b + b = a` (with `a b : Nat`; `leanReading_fSubAddCancelGuarded`)
- `fContrapositive`: `¬ a - b + b = a → ¬ b ≤ a` (with `a b : Nat`; `leanReading_fContrapositive`)

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| connectives = strong Kleene (definedEverywhere_kleene_guardSecond) | With sequential connectives the guard-second conjunction is undefined at a < b. | tight | `ce_seq_not_closed` | sequential connectives, partialNat, the formula (a b : Nat), a - b + b = a AND b <= a (fGuardSecond) at a = 0, b = 1 |

Counterexample statements:

```lean
-- lean/ToyJunk/Guarded.lean:564-567
theorem ce_seq_not_closed :
    DefinedEverywhere .seq .partialNat fGuardFirst ∧ ¬ DefinedEverywhere .seq .partialNat fGuardSecond ∧
      DefinedEverywhere .seq .partialNat fSubAddCancelGuarded ∧
      ¬ DefinedEverywhere .seq .partialNat fContrapositive := …
```

**Non-vacuity.** No propositional hypotheses. guarded_incomplete_junkIndependent has no parameters; guarded_incomplete_defined quantifies over c : Conn; guarded_incomplete_disjunctive_guards over c : Conn and r : SubReading; definedEverywhere_kleene_guardSecond over r : SubReading, with the connective semantics fixed to kleene. The ledger entry connectives = strong Kleene is that fixed instantiation rather than a premise, and definedEverywhere_kleene_guardSecond is itself an instance satisfying it (with either reading). Conn and SubReading are inhabited.

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `seq_tables`.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P5] Adam Darvas, Farhad Mehta and Arsenii Rudich (2008)
- [P4] John McCarthy (1963)

**Design question.** Is there a decidable syntactic discipline (guards for every partial operation, explicit casts) on which the exact human reading and the total reading provably coincide?

Basis: execution (Lean kernel check) — `guarded_incomplete_junkIndependent`, `guarded_incomplete_defined`, `guarded_incomplete_disjunctive_guards`, `definedEverywhere_kleene_guardSecond`.

Non-claims: Boundaries, *Non-claims*, R8.

### R9. trap_truncated_subtraction

**Kind:** counterexample · **Tier:** T0 · **Depth:** definitional

**Plain claim.** Truncated subtraction, for each connective semantics: (0 : Nat) - 1 + 1 = 0 (fTruncSubCancel01) is false in Lean, undefined in the partialNat reading and true in the intValued reading; (0 : Nat) - 1 <= 0 (fTruncSubLe01) is true in Lean, false for the junk record oneJ and undefined under partialNat, so its Lean truth rests on the junk value 0.

**Tier rationale.** Ground evaluations of Lean core operators whose behavior is documented in the cited docstrings.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:25-29
theorem trap_truncSub_addCancel (c : Conn) :
    evalJ leanJ fTruncSubCancel01 Env.zero = false ∧
      hEval c .partialNat fTruncSubCancel01 Env.zero = none ∧
      hEval c .intValued fTruncSubCancel01 Env.zero = some true ∧
      ((0 : Nat) - 1 + 1 ≠ 0) := …
-- lean/ToyJunk/Traps.lean:37-39
theorem trap_truncSub_le_self (c : Conn) :
    evalJ leanJ fTruncSubLe01 Env.zero = true ∧ evalJ oneJ fTruncSubLe01 Env.zero = false ∧
      hEval c .partialNat fTruncSubLe01 Env.zero = none := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fTruncSubCancel01`: `(0 : Nat) - 1 + 1 = 0` (closed; `leanReading_fTruncSubCancel01`)
- `fTruncSubLe01`: `(0 : Nat) - 1 ≤ 0` (closed; `leanReading_fTruncSubLe01`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). The sole parameter of trap_truncSub_addCancel and of trap_truncSub_le_self is c : Conn (inhabited by kleene and seq); the readings partialNat and intValued appear as fixed constants, the formulas are closed and evaluated at Env.zero, and (0 : Nat) - 1 + 1 != 0 is a closed Lean-core proposition.

**Depth:** definitional.

**Prior art** (full records under Evidence, *Sources*):

- [L1] Lean core v4.34.1 `src/Init/Prelude.lean` (`Nat.sub`, `Nat.div`, `Nat.modCore`)
- [P1] Lean Prover Community (web page)
- [P9] Kevin Buzzard (2020)

**Design question.** Which constructs make a statement's Lean reading diverge from its exact human reading, construct by construct?

Basis: execution (Lean kernel check) — `trap_truncSub_addCancel`, `trap_truncSub_le_self`.

Basis: derived (modeling bridge) — The Lean-core facts are kernel-checked. That a reader who reads `-` on `Nat` as exact subtraction would misjudge these statements is the modeling bridge: it follows from the reading `hEval` formalizes, not from an observation of readers.

Non-claims: Boundaries, *Non-claims*, R9.

### R10. trap_division_by_zero

**Kind:** counterexample · **Tier:** T0 · **Depth:** definitional

**Plain claim.** Division and remainder by zero, for each connective semantics and reading: (5 : Int) / 0 = 0 (fFiveDivZero) and (5 : Nat) % 0 = 5 (fFiveModZero) are true in Lean, false for oneJ, and human-undefined; in Lean core (5 : Int) / 0 = 0, (5 : Nat) / 0 = 0, (5 : Nat) % 0 = 5 and (5 : Int) % 0 = 5.

**Tier rationale.** Ground evaluations of Lean core operators whose behavior is documented in the cited docstrings.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:50-55
theorem trap_div_mod_zero (c : Conn) (r : SubReading) :
    evalJ leanJ fFiveDivZero Env.zero = true ∧ evalJ oneJ fFiveDivZero Env.zero = false ∧
      hEval c r fFiveDivZero Env.zero = none ∧
      evalJ leanJ fFiveModZero Env.zero = true ∧ evalJ oneJ fFiveModZero Env.zero = false ∧
      hEval c r fFiveModZero Env.zero = none ∧
      ((5 : Int) / 0 = 0 ∧ (5 : Nat) / 0 = 0 ∧ (5 : Nat) % 0 = 5 ∧ (5 : Int) % 0 = 5) := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fFiveDivZero`: `(5 : Int) / 0 = 0` (closed; `leanReading_fFiveDivZero`)
- `fFiveModZero`: `(5 : Nat) % 0 = 5` (closed; `leanReading_fFiveModZero`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). trap_div_mod_zero quantifies over c : Conn and r : SubReading, both inhabited; the formulas are closed and evaluated at Env.zero, and the Lean-core conjunct is a closed proposition.

**Depth:** definitional.

**Prior art** (full records under Evidence, *Sources*):

- [L1] Lean core v4.34.1 `src/Init/Prelude.lean` (`Nat.sub`, `Nat.div`, `Nat.modCore`)
- [L2] Lean core v4.34.1 `src/Init/Data/Int/DivMod/Basic.lean` (`Int.ediv`, `Int.emod`, `Int.div`, `Int.mod`)
- [P1] Lean Prover Community (web page)
- [P9] Kevin Buzzard (2020)
- [P10] Lawrence C. Paulson (2021)
- [P11] Jan A. Bergstra and John V. Tucker (2007)

**Design question.** Which constructs make a statement's Lean reading diverge from its exact human reading, construct by construct?

Basis: execution (Lean kernel check) — `trap_div_mod_zero`.

Basis: derived (modeling bridge) — The Lean-core facts are kernel-checked. The divergence from an exact reader follows from the human reading formalized here (division by zero undefined).

Non-claims: Boundaries, *Non-claims*, R10.

### R11. trap_floor_division_read_as_exact

**Kind:** counterexample · **Tier:** T0 · **Depth:** definitional

**Plain claim.** Floor division read as exact division, for each connective semantics and reading: (7 : Nat) / 2 * 2 = 7 (fFloorDiv) is false in Lean ((7 : Nat) / 2 * 2 = 6) and human-undefined, because the human reading reads / as exact division and leaves inexact quotients undefined.

**Tier rationale.** A ground evaluation of a Lean core operator whose behavior is documented in the cited docstring.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:63-65
theorem trap_floorDiv_exact (c : Conn) (r : SubReading) :
    evalJ leanJ fFloorDiv Env.zero = false ∧ hEval c r fFloorDiv Env.zero = none ∧
      ((7 : Nat) / 2 * 2 = 6) := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fFloorDiv`: `(7 : Nat) / 2 * 2 = 7` (closed; `leanReading_fFloorDiv`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). trap_floorDiv_exact quantifies over c : Conn and r : SubReading, both inhabited; the formula is closed and evaluated at Env.zero, and (7 : Nat) / 2 * 2 = 6 is a closed Lean-core proposition.

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `inexact_division_is_junk`.

**Depth:** definitional.

**Prior art** (full records under Evidence, *Sources*):

- [L1] Lean core v4.34.1 `src/Init/Prelude.lean` (`Nat.sub`, `Nat.div`, `Nat.modCore`)
- [P1] Lean Prover Community (web page)

**Design question.** Which constructs make a statement's Lean reading diverge from its exact human reading, construct by construct?

Basis: execution (Lean kernel check) — `trap_floorDiv_exact`.

Non-claims: Boundaries, *Non-claims*, R11.

### R12. trap_integer_rounding

**Kind:** counterexample · **Tier:** T0 · **Depth:** definitional

**Plain claim.** Integer rounding: Lean's default Int / and % are Int.ediv and Int.emod (definitionally). At (-7, 2) the Euclidean, truncating and flooring quotients are -4, -3, -4 and the remainders 1, -1, 1; at (7, -2) the quotients are -3, -3, -4 and the remainders 1, 1, -1. In the toy, for each connective semantics and reading, (-7 : Int) / 2 = -4 (fNegSevenDivTwo) and (-7 : Int) % 2 = 1 (fNegSevenModTwo) hold for leanJ and floorJ and fail for truncJ; (7 : Int) / (-2) = -3 (fSevenDivNegTwo) and (7 : Int) % (-2) = 1 (fSevenModNegTwo) hold for leanJ and truncJ and fail for floorJ; all four are human-undefined.

**Tier rationale.** Ground evaluations of Lean core operators whose conventions are documented in the cited module comment.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:92-100
theorem trap_int_rounding (c : Conn) (r : SubReading) :
    (evalJ leanJ fNegSevenDivTwo Env.zero = true ∧ evalJ truncJ fNegSevenDivTwo Env.zero = false ∧
      evalJ floorJ fNegSevenDivTwo Env.zero = true ∧ hEval c r fNegSevenDivTwo Env.zero = none) ∧
    (evalJ leanJ fSevenDivNegTwo Env.zero = true ∧ evalJ truncJ fSevenDivNegTwo Env.zero = true ∧
      evalJ floorJ fSevenDivNegTwo Env.zero = false ∧ hEval c r fSevenDivNegTwo Env.zero = none) ∧
    (evalJ leanJ fNegSevenModTwo Env.zero = true ∧ evalJ truncJ fNegSevenModTwo Env.zero = false ∧
      evalJ floorJ fNegSevenModTwo Env.zero = true ∧ hEval c r fNegSevenModTwo Env.zero = none) ∧
    (evalJ leanJ fSevenModNegTwo Env.zero = true ∧ evalJ truncJ fSevenModNegTwo Env.zero = true ∧
      evalJ floorJ fSevenModNegTwo Env.zero = false ∧ hEval c r fSevenModNegTwo Env.zero = none) := …
-- lean/ToyJunk/Traps.lean:81-86
theorem trap_int_rounding_values :
    ((-7 : Int) / 2 = -4 ∧ Int.tdiv (-7) 2 = -3 ∧ Int.fdiv (-7) 2 = -4) ∧
      ((7 : Int) / (-2) = -3 ∧ Int.tdiv 7 (-2) = -3 ∧ Int.fdiv 7 (-2) = -4) ∧
      ((-7 : Int) % 2 = 1 ∧ Int.tmod (-7) 2 = -1 ∧ Int.fmod (-7) 2 = 1) ∧
      ((7 : Int) % (-2) = 1 ∧ Int.tmod 7 (-2) = 1 ∧ Int.fmod 7 (-2) = -1) ∧
      (∀ a b : Int, a / b = Int.ediv a b ∧ a % b = Int.emod a b) := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fNegSevenDivTwo`: `(-7 : Int) / 2 = -4` (closed; `leanReading_fNegSevenDivTwo`)
- `fSevenDivNegTwo`: `(7 : Int) / (-2) = -3` (closed; `leanReading_fSevenDivNegTwo`)
- `fNegSevenModTwo`: `(-7 : Int) % 2 = 1` (closed; `leanReading_fNegSevenModTwo`)
- `fSevenModNegTwo`: `(7 : Int) % (-2) = 1` (closed; `leanReading_fSevenModNegTwo`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). trap_int_rounding quantifies over c : Conn and r : SubReading, both inhabited, with closed formulas evaluated at Env.zero; trap_int_rounding_values has no parameters, and its last conjunct, for all a b : Int, a / b = Int.ediv a b AND a % b = Int.emod a b, is a universal conclusion without premises (Int is inhabited).

**Depth:** definitional.

**Prior art** (full records under Evidence, *Sources*):

- [L2] Lean core v4.34.1 `src/Init/Data/Int/DivMod/Basic.lean` (`Int.ediv`, `Int.emod`, `Int.div`, `Int.mod`)
- [P12] Raymond T. Boute (1992)
- [P13] Daan Leijen (2001)

**Design question.** Which constructs make a statement's Lean reading diverge from its exact human reading, construct by construct?

Basis: execution (Lean kernel check) — `trap_int_rounding`, `trap_int_rounding_values`.

Non-claims: Boundaries, *Non-claims*, R12.

### R13. rounding_conventions_agree_on_domains

**Kind:** theorem · **Tier:** T0 · **Depth:** shallow

**Plain claim.** For all integers n and d, with / and % Lean's default (Euclidean) operators: if d | n then Int.tdiv n d = n / d and Int.fdiv n d = n / d (no d != 0 hypothesis is used); if 0 <= n and 0 <= d then Int.tmod n d = n % d and Int.fmod n d = n % d. In particular the quotients agree on DivDom (d != 0 and d | n) and the remainders on ModDom (0 <= n and 0 < d).

**Tier rationale.** Re-derivation from Lean core lemmas (Int.tdiv_eq_ediv_of_dvd, Int.fdiv_eq_ediv_of_dvd, Int.tmod_eq_emod_of_nonneg, Int.fmod_eq_emod_of_nonneg).

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:106-107
theorem quotient_conventions_agree_of_dvd (n d : Int) (h : d ∣ n) :
    Int.tdiv n d = n / d ∧ Int.fdiv n d = n / d := …
-- lean/ToyJunk/Traps.lean:113-114
theorem remainder_conventions_agree_of_nonneg (n d : Int) (hn : 0 ≤ n) (hd : 0 ≤ d) :
    Int.tmod n d = n % d ∧ Int.fmod n d = n % d := …
-- lean/ToyJunk/Traps.lean:121-123
theorem rounding_conventions_agree_on_domains (n d : Int) :
    (DivDom n d → Int.tdiv n d = n / d ∧ Int.fdiv n d = n / d) ∧
      (ModDom n d → Int.tmod n d = n % d ∧ Int.fmod n d = n % d) := …
```

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| h : d \| n (quotient_conventions_agree_of_dvd) | Without divisibility the quotient conventions can differ. | tight | `ce_quotient_conventions_not_dvd` | one integer pair, n = -7, d = 2 |
| hn : 0 <= n (remainder_conventions_agree_of_nonneg) | With a negative dividend the truncating remainder can differ. | tight | `ce_remainder_conventions_neg_dividend` | one integer pair with 0 <= d, n = -7, d = 2 |
| hd : 0 <= d (remainder_conventions_agree_of_nonneg) | With a negative divisor the flooring remainder can differ. | tight | `ce_remainder_conventions_neg_divisor` | one integer pair with 0 <= n, n = 7, d = -2 |

Counterexample statements:

```lean
-- lean/ToyJunk/Traps.lean:135-136
theorem ce_quotient_conventions_not_dvd :
    ¬ (2 : Int) ∣ -7 ∧ ¬ (Int.tdiv (-7) 2 = (-7) / 2 ∧ Int.fdiv (-7) 2 = (-7) / 2) := …
-- lean/ToyJunk/Traps.lean:141-143
theorem ce_remainder_conventions_neg_dividend :
    (0 : Int) ≤ 2 ∧ ¬ (0 : Int) ≤ -7 ∧
      ¬ (Int.tmod (-7) 2 = (-7) % 2 ∧ Int.fmod (-7) 2 = (-7) % 2) := …
-- lean/ToyJunk/Traps.lean:148-150
theorem ce_remainder_conventions_neg_divisor :
    (0 : Int) ≤ 7 ∧ ¬ (0 : Int) ≤ -2 ∧
      ¬ (Int.tmod 7 (-2) = 7 % (-2) ∧ Int.fmod 7 (-2) = 7 % (-2)) := …
```

**Non-vacuity.** (3 : Int) | 6 and (2 : Int) | -4; (0 : Int) <= 7 and (0 : Int) <= 2; DivDom 6 3 and ModDom 7 2 (on Int) hold.

```lean
-- lean/ToyJunk/Traps.lean:128
theorem nv_quotient_conventions_agree_of_dvd : (3 : Int) ∣ 6 ∧ (2 : Int) ∣ -4 := …
-- lean/ToyJunk/Traps.lean:131
theorem nv_remainder_conventions_agree_of_nonneg : (0 : Int) ≤ 7 ∧ (0 : Int) ≤ 2 := …
-- lean/ToyJunk/Examples.lean:15
theorem DivDom_pos : DivDom 6 3 ∧ DivDom (-4) 2 ∧ DivDom 0 5 := …
-- lean/ToyJunk/Examples.lean:22
theorem ModDom_pos : ModDom 7 2 ∧ ModDom 0 3 := …
```

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [L4] Lean core v4.34.1 `src/Init/Data/Int/DivMod/Lemmas.lean` (`Int.tdiv_eq_ediv`, `Int.fdiv_eq_ediv`, `Int.tdiv_eq_ediv_of_dvd`, `Int.fdiv_eq_ediv_of_dvd`, `Int.fmod_eq_emod_of_nonneg`, `Int.fmod_eq_emod`)
- [L2] Lean core v4.34.1 `src/Init/Data/Int/DivMod/Basic.lean` (`Int.ediv`, `Int.emod`, `Int.div`, `Int.mod`)
- [P13] Daan Leijen (2001)

**Design question.** Do the domains on which the total semantics is fixed silently commit to a rounding convention?

Basis: execution (Lean kernel check) — `quotient_conventions_agree_of_dvd`, `remainder_conventions_agree_of_nonneg`, `rounding_conventions_agree_on_domains`.

Non-claims: Boundaries, *Non-claims*, R13.

### R14. trap_fin_wraparound

**Kind:** counterexample · **Tier:** T0 · **Depth:** definitional

**Plain claim.** Fin wrap-around (Lean core): (3 : Fin 5) + 4 = 2; (3 : Fin 5).val + (4 : Fin 5).val is not ((3 : Fin 5) + 4).val; ((2 : Fin 5) - 3).val = 4; and (7 : Fin 5).val = 2. In Fin 3 the numeral 4 denotes the element with value 1, (4 : Fin 3).val = 1, so (1 : Fin 3).val + (4 : Fin 3).val < 3 holds while ((1 : Fin 3) + 4).val is not the natural number 1 + 4.

**Tier rationale.** Ground evaluations of Lean core Fin operations documented in the cited docstrings.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:155-157
theorem trap_fin_wrap :
    ((3 : Fin 5) + 4 = 2) ∧ ((3 : Fin 5).val + (4 : Fin 5).val ≠ ((3 : Fin 5) + 4).val) ∧
      ((2 : Fin 5) - 3).val = 4 ∧ (7 : Fin 5).val = 2 := …
-- lean/ToyJunk/Traps.lean:163-164
theorem trap_fin_numeral_wraps_before_bound :
    (4 : Fin 3).val = 1 ∧ (1 : Fin 3).val + (4 : Fin 3).val < 3 ∧ ((1 : Fin 3) + 4).val ≠ 1 + 4 := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No hypotheses and no parameters (vacuous): trap_fin_wrap and trap_fin_numeral_wraps_before_bound are closed Lean-core propositions about Fin 5 and Fin 3. The degenerate modulus n = 0 does not arise (Fin 0 has no elements).

**Depth:** definitional.

**Prior art** (full records under Evidence, *Sources*):

- [L5] Lean core v4.34.1 `src/Init/Data/Fin/Basic.lean` (`Fin.add`, `Fin.sub`, `Fin.ofNat`, `Fin.instOfNat`)
- [P1] Lean Prover Community (web page)

**Design question.** Which constructs make a statement's Lean reading diverge from its exact human reading, construct by construct?

Basis: execution (Lean kernel check) — `trap_fin_wrap`, `trap_fin_numeral_wraps_before_bound`.

Basis: derived (modeling bridge) — The Lean-core facts are kernel-checked. They are traps for a reader who reads `+` on `Fin n` as exact natural-number addition; for a reader who reads it modulo `n` they are the intended meaning.

Non-claims: Boundaries, *Non-claims*, R14.

### R15. trap_cast_placement_and_toNat

**Kind:** counterexample · **Tier:** T0 · **Depth:** shallow

**Plain claim.** Cast placement, for each connective semantics: the Int formula with the Nat subtraction inside the cast, (((0 : Nat) - 1 : Nat) : Int) = ((0 : Nat) : Int) - ((1 : Nat) : Int) (fCastPlacement01), is false in Lean, undefined under partialNat and true under intValued; in the toy, at every environment the Lean value of (a b : Nat), ((a - b : Nat) : Int) = (a : Int) - (b : Int) (fCastPlacement) is decide (b <= a); and in Lean core, for all a b : Nat, ((a - b : Nat) : Int) = (a : Int) - (b : Int) iff b <= a. For each connective semantics and reading, (-3 : Int).toNat = 0 (fToNatNeg) is true in Lean, false for oneJ and human-undefined.

**Tier rationale.** Ground evaluations and a restatement of Lean core's Int.ofNat_sub.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:181-185
theorem trap_cast_placement (c : Conn) :
    evalJ leanJ fCastPlacement01 Env.zero = false ∧
      hEval c .partialNat fCastPlacement01 Env.zero = none ∧
      hEval c .intValued fCastPlacement01 Env.zero = some true ∧
      ∀ ρ, evalJ leanJ fCastPlacement ρ = decide (ρ.nat 1 ≤ ρ.nat 0) := …
-- lean/ToyJunk/Traps.lean:175
theorem natCast_sub_eq_iff_le (a b : Nat) : ((a - b : Nat) : Int) = (a : Int) - (b : Int) ↔ b ≤ a := …
-- lean/ToyJunk/Traps.lean:204-206
theorem trap_toNat_neg (c : Conn) (r : SubReading) :
    evalJ leanJ fToNatNeg Env.zero = true ∧ evalJ oneJ fToNatNeg Env.zero = false ∧
      hEval c r fToNatNeg Env.zero = none ∧ Int.toNat (-3) = 0 := …
```

Explicit rendering (`trap_toNat_neg`) with the argument type of `Int.toNat` written out:
```lean
∀ (c : Conn) (r : SubReading),
  evalJ leanJ fToNatNeg Env.zero = true ∧ evalJ oneJ fToNatNeg Env.zero = false ∧
    hEval c r fToNatNeg Env.zero = none ∧ (-3 : Int).toNat = 0
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fCastPlacement01`: `(((0 : Nat) - 1 : Nat) : Int) = ((0 : Nat) : Int) - ((1 : Nat) : Int)` (closed; `leanReading_fCastPlacement01`)
- `fCastPlacement`: `((a - b : Nat) : Int) = (a : Int) - (b : Int)` (with `a b : Nat`; `leanReading_fCastPlacement`)
- `fToNatNeg`: `(-3 : Int).toNat = 0` (closed; `leanReading_fToNatNeg`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). trap_cast_placement quantifies over c : Conn and trap_toNat_neg over c : Conn and r : SubReading, all inhabited; the quantifier over environments rho inside trap_cast_placement is part of its conclusion. natCast_sub_eq_iff_le (a b : Nat) is a biconditional without premises, and both of its sides take both truth values: at a = 1, b = 0 the cast equation holds (0 <= 1), and at a = 0, b = 1 it fails (NOT (1 <= 0)).

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [L6] Lean core v4.34.1 `src/Init/Data/Int/Lemmas.lean` (`Int.ofNat_sub`)
- [L1] Lean core v4.34.1 `src/Init/Prelude.lean` (`Nat.sub`, `Nat.div`, `Nat.modCore`)
- [L3] Lean core v4.34.1 `src/Init/Data/Int/Basic.lean` (`Int.toNat`)

**Design question.** Which constructs make a statement's Lean reading diverge from its exact human reading, construct by construct?

Basis: execution (Lean kernel check) — `trap_cast_placement`, `natCast_sub_eq_iff_le`, `trap_toNat_neg`.

Non-claims: Boundaries, *Non-claims*, R15.

### R16. trap_numeral_typing

**Kind:** counterexample · **Tier:** T0 · **Depth:** definitional

**Plain claim.** Numeral typing, for each connective semantics and reading: (2 : Nat) - 3 < 0 (fNumeralNat) is false in Lean and (2 : Int) - 3 < 0 (fNumeralInt) is true in Lean; in the human readings the Int version is true and the Nat version is undefined under partialNat and true under intValued. In Lean core the unannotated propositions NOT (2 - 3 < 0) and 2 - 3 = 0, whose numerals elaborate at Nat by default, are provable (both are false at Int, where (2 : Int) - 3 < 0 holds), and HEq (2 - 3) ((2 : Nat) - 3) holds for the unannotated term 2 - 3, so that term has type Nat (heterogeneous equality implies equal types, by Lean core's type_eq_of_heq).

**Tier rationale.** Ground evaluations plus a check of Lean core's default numeral instance.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:215-220
theorem trap_numeral_typing (c : Conn) (r : SubReading) :
    evalJ leanJ fNumeralNat Env.zero = false ∧ evalJ leanJ fNumeralInt Env.zero = true ∧
      hEval c .partialNat fNumeralNat Env.zero = none ∧
      hEval c .intValued fNumeralNat Env.zero = some true ∧
      hEval c r fNumeralInt Env.zero = some true ∧
      ¬ (2 - 3 < 0) ∧ ((2 : Int) - 3 < 0) ∧ HEq (2 - 3) ((2 : Nat) - 3) ∧ (2 - 3 = 0) := …
```

In the quoted statement the conjuncts `¬ (2 - 3 < 0)`, `HEq (2 - 3) ((2 : Nat) - 3)` and `2 - 3 = 0` are deliberately unannotated: they record what Lean does with numerals whose type is not otherwise determined. The explicit rendering below shows the elaborated types.

Explicit rendering (`trap_numeral_typing`) with the numeral types that Lean's default instance assigns written out; it is the same term, so `HEq` relates a term to itself:
```lean
∀ (c : Conn) (r : SubReading),
  evalJ leanJ fNumeralNat Env.zero = false ∧ evalJ leanJ fNumeralInt Env.zero = true ∧
    hEval c .partialNat fNumeralNat Env.zero = none ∧
    hEval c .intValued fNumeralNat Env.zero = some true ∧
    hEval c r fNumeralInt Env.zero = some true ∧
    ¬ ((2 : Nat) - 3 < 0) ∧ ((2 : Int) - 3 < 0) ∧ HEq ((2 : Nat) - 3) ((2 : Nat) - 3) ∧ ((2 : Nat) - 3 = 0)
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fNumeralNat`: `(2 : Nat) - 3 < 0` (closed; `leanReading_fNumeralNat`)
- `fNumeralInt`: `(2 : Int) - 3 < 0` (closed; `leanReading_fNumeralInt`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). trap_numeral_typing quantifies over c : Conn and r : SubReading, both inhabited; its formulas are closed and evaluated at Env.zero, and its Lean-core conjuncts are closed propositions.

**Depth:** definitional.

**Prior art** (full records under Evidence, *Sources*):

- [L7] Lean core v4.34.1 `src/Init/Prelude.lean` (`instOfNatNat`)
- [L1] Lean core v4.34.1 `src/Init/Prelude.lean` (`Nat.sub`, `Nat.div`, `Nat.modCore`)
- [P1] Lean Prover Community (web page)

**Design question.** Which constructs make a statement's Lean reading diverge from its exact human reading, construct by construct?

Basis: execution (Lean kernel check) — `trap_numeral_typing`.

Non-claims: Boundaries, *Non-claims*, R16.

### R17. guarded_fragment_not_closed_under_lean_equivalences

**Kind:** impossibility · **Tier:** T0 · **Depth:** shallow

**Plain claim.** The set of formulas accepted by the syntactic checker guarded is not closed under rewrites that are equivalences in Lean's reading: with a b : Nat, b <= a AND a - b + b = a (fGuardFirst) is accepted while a - b + b = a AND b <= a (fGuardSecond) is rejected, and b <= a -> a - b + b = a (fSubAddCancelGuarded) is accepted while its contrapositive NOT (a - b + b = a) -> NOT (b <= a) (fContrapositive) is rejected, although each pair has the same total value under every junk record at every environment.

**Tier rationale.** The left-to-right well-definedness operator L is known to be stricter than the symmetric operator D (Darvas, Mehta and Rudich 2008); these are concrete instances for the checker guarded.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Guarded.lean:486-488
theorem ce_guarded_not_closed_under_and_comm :
    guarded fGuardFirst = true ∧ guarded fGuardSecond = false ∧
      ∀ (J : Junk) (ρ : Env), evalJ J fGuardFirst ρ = evalJ J fGuardSecond ρ := …
-- lean/ToyJunk/Guarded.lean:496-498
theorem ce_guarded_not_closed_under_contrapose :
    guarded fSubAddCancelGuarded = true ∧ guarded fContrapositive = false ∧
      ∀ (J : Junk) (ρ : Env), evalJ J fSubAddCancelGuarded ρ = evalJ J fContrapositive ρ := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fGuardFirst`: `b ≤ a ∧ a - b + b = a` (with `a b : Nat`; `leanReading_fGuardFirst`)
- `fGuardSecond`: `a - b + b = a ∧ b ≤ a` (with `a b : Nat`; `leanReading_fGuardSecond`)
- `fSubAddCancelGuarded`: `b ≤ a → a - b + b = a` (with `a b : Nat`; `leanReading_fSubAddCancelGuarded`)
- `fContrapositive`: `¬ a - b + b = a → ¬ b ≤ a` (with `a b : Nat`; `leanReading_fContrapositive`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** Concrete formulas; no hypotheses (vacuous).

**Positive control** (a nearby setting where the conclusion fails: under strong Kleene connectives the *semantic* class of everywhere-defined formulas is closed under both rewrites):

```lean
-- lean/ToyJunk/Guarded.lean:525-528
theorem definedEverywhere_kleene_closed (r : SubReading) (φ ψ : Formula) :
    (DefinedEverywhere .kleene r (.and φ ψ) ↔ DefinedEverywhere .kleene r (.and ψ φ)) ∧
      (DefinedEverywhere .kleene r (.imp φ ψ) ↔
        DefinedEverywhere .kleene r (.imp (.not ψ) (.not φ))) := …
```

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `seq_tables`.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P5] Adam Darvas, Farhad Mehta and Arsenii Rudich (2008)
- [P4] John McCarthy (1963)

**Design question.** Does the position of a guard matter, and is the set of formulas accepted by the guard checker stable under rewrites that are equivalences in Lean?

Basis: execution (Lean kernel check) — `ce_guarded_not_closed_under_and_comm`, `ce_guarded_not_closed_under_contrapose`.

Non-claims: Boundaries, *Non-claims*, R17.

### R18. kleene_definedness_closed_under_comm_and_contraposition

**Kind:** theorem · **Tier:** T0 · **Depth:** shallow

**Plain claim.** Under strong Kleene connectives, for either reading of natural subtraction, all toy formulas phi and psi and every environment, the human values of phi AND psi and psi AND phi coincide, as do those of phi -> psi and NOT psi -> NOT phi; hence phi AND psi is defined everywhere iff psi AND phi is, and phi -> psi is defined everywhere iff NOT psi -> NOT phi is.

**Tier rationale.** Restates the symmetry of Kleene's strong conjunction (minimum) and the equivalence of an implication and its contrapositive under the strong tables.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Guarded.lean:525-528
theorem definedEverywhere_kleene_closed (r : SubReading) (φ ψ : Formula) :
    (DefinedEverywhere .kleene r (.and φ ψ) ↔ DefinedEverywhere .kleene r (.and ψ φ)) ∧
      (DefinedEverywhere .kleene r (.imp φ ψ) ↔
        DefinedEverywhere .kleene r (.imp (.not ψ) (.not φ))) := …
-- lean/ToyJunk/Guarded.lean:514-515
theorem hEval_kleene_and_comm (r : SubReading) (φ ψ : Formula) (ρ : Env) :
    hEval .kleene r (.and φ ψ) ρ = hEval .kleene r (.and ψ φ) ρ := …
-- lean/ToyJunk/Guarded.lean:519-520
theorem hEval_kleene_contrapose (r : SubReading) (φ ψ : Formula) (ρ : Env) :
    hEval .kleene r (.imp (.not ψ) (.not φ)) ρ = hEval .kleene r (.imp φ ψ) ρ := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fGuardFirst`: `b ≤ a ∧ a - b + b = a` (with `a b : Nat`; `leanReading_fGuardFirst`)
- `fGuardSecond`: `a - b + b = a ∧ b ≤ a` (with `a b : Nat`; `leanReading_fGuardSecond`)
- `fSubAddCancelGuarded`: `b ≤ a → a - b + b = a` (with `a b : Nat`; `leanReading_fSubAddCancelGuarded`)
- `fContrapositive`: `¬ a - b + b = a → ¬ b ≤ a` (with `a b : Nat`; `leanReading_fContrapositive`)

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| connectives = strong Kleene | Sequential connectives are not commutative on undefined values. | tight | `ce_seq_not_closed` | sequential connectives, partialNat, the formulas (a b : Nat), a - b + b = a AND b <= a (fGuardSecond) and (a b : Nat), NOT (a - b + b = a) -> NOT (b <= a) (fContrapositive) |

Counterexample statements:

```lean
-- lean/ToyJunk/Guarded.lean:564-567
theorem ce_seq_not_closed :
    DefinedEverywhere .seq .partialNat fGuardFirst ∧ ¬ DefinedEverywhere .seq .partialNat fGuardSecond ∧
      DefinedEverywhere .seq .partialNat fSubAddCancelGuarded ∧
      ¬ DefinedEverywhere .seq .partialNat fContrapositive := …
```

**Non-vacuity.** No hypotheses on phi and psi; for instance (a b : Nat), a - b + b = a AND b <= a (fGuardSecond) is defined everywhere under strong Kleene.

```lean
-- lean/ToyJunk/Guarded.lean:539-540
theorem definedEverywhere_kleene_guardSecond (r : SubReading) :
    guarded fGuardSecond = false ∧ DefinedEverywhere .kleene r fGuardSecond := …
```

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `kleene_tables`, `kleene_quantifier_tables`.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P3] S. C. Kleene (1952)
- [P5] Adam Darvas, Farhad Mehta and Arsenii Rudich (2008)
- [P6] Matthias Schmalz (2012)

**Design question.** Does the position of a guard matter, and is the set of formulas accepted by the guard checker stable under rewrites that are equivalences in Lean?

Basis: execution (Lean kernel check) — `definedEverywhere_kleene_closed`, `hEval_kleene_and_comm`, `hEval_kleene_contrapose`.

Non-claims: Boundaries, *Non-claims*, R18.

### R19. sequential_connectives_break_closure

**Kind:** counterexample · **Tier:** T0 · **Depth:** shallow

**Plain claim.** With sequential (McCarthy-style) connectives and the partialNat reading, at a = 0, b = 1 (a b : Nat) the formula b <= a AND a - b + b = a (fGuardFirst) is defined (false) while a - b + b = a AND b <= a (fGuardSecond) is undefined, and b <= a -> a - b + b = a (fSubAddCancelGuarded) is defined (true) while its contrapositive (fContrapositive) is undefined; the first and third are defined everywhere and the second and fourth are not. With sequential connectives and either reading, (x : Int), 0 <= x AND x.toNat = x.toNat (fToNatGuardFirst) and (x : Int), 0 <= x -> x.toNat = x.toNat (fToNatImp) are defined everywhere while their commuted and contraposed forms (fToNatGuardSecond, fToNatContrapose) are undefined at x = -1. So with sequential connectives the class of everywhere-defined formulas is closed under neither commutation of AND nor contraposition.

**Tier rationale.** Instances of McCarthy's remark that sequential conjunction is not commutative on undefined values.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Guarded.lean:549-551
theorem ce_seq_and_comm_changes_definedness :
    hEval .seq .partialNat fGuardFirst (envAB 0 1) = some false ∧
      hEval .seq .partialNat fGuardSecond (envAB 0 1) = none := …
-- lean/ToyJunk/Guarded.lean:556-558
theorem ce_seq_contrapose_changes_definedness :
    hEval .seq .partialNat fSubAddCancelGuarded (envAB 0 1) = some true ∧
      hEval .seq .partialNat fContrapositive (envAB 0 1) = none := …
-- lean/ToyJunk/Guarded.lean:564-567
theorem ce_seq_not_closed :
    DefinedEverywhere .seq .partialNat fGuardFirst ∧ ¬ DefinedEverywhere .seq .partialNat fGuardSecond ∧
      DefinedEverywhere .seq .partialNat fSubAddCancelGuarded ∧
      ¬ DefinedEverywhere .seq .partialNat fContrapositive := …
-- lean/ToyJunk/Guarded.lean:613-615
theorem ce_seq_not_closed_toNat (r : SubReading) :
    DefinedEverywhere .seq r fToNatGuardFirst ∧ ¬ DefinedEverywhere .seq r fToNatGuardSecond ∧
      DefinedEverywhere .seq r fToNatImp ∧ ¬ DefinedEverywhere .seq r fToNatContrapose := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fGuardFirst`: `b ≤ a ∧ a - b + b = a` (with `a b : Nat`; `leanReading_fGuardFirst`)
- `fGuardSecond`: `a - b + b = a ∧ b ≤ a` (with `a b : Nat`; `leanReading_fGuardSecond`)
- `fSubAddCancelGuarded`: `b ≤ a → a - b + b = a` (with `a b : Nat`; `leanReading_fSubAddCancelGuarded`)
- `fContrapositive`: `¬ a - b + b = a → ¬ b ≤ a` (with `a b : Nat`; `leanReading_fContrapositive`)
- `fToNatGuardFirst`: `0 ≤ x ∧ x.toNat = x.toNat` (with `x : Int`; `leanReading_fToNatGuardFirst`)
- `fToNatGuardSecond`: `x.toNat = x.toNat ∧ 0 ≤ x` (with `x : Int`; `leanReading_fToNatGuardSecond`)
- `fToNatImp`: `0 ≤ x → x.toNat = x.toNat` (with `x : Int`; `leanReading_fToNatImp`)
- `fToNatContrapose`: `¬ x.toNat = x.toNat → ¬ 0 ≤ x` (with `x : Int`; `leanReading_fToNatContrapose`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). ce_seq_and_comm_changes_definedness, ce_seq_contrapose_changes_definedness and ce_seq_not_closed have no parameters (connective semantics seq and reading partialNat fixed); ce_seq_not_closed_toNat quantifies over r : SubReading (inhabited by partialNat and intValued), with the connective semantics fixed to seq.

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `seq_defined_intValued`, `seq_tables`.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P4] John McCarthy (1963)
- [P5] Adam Darvas, Farhad Mehta and Arsenii Rudich (2008)

**Design question.** Does the position of a guard matter, and is the set of formulas accepted by the guard checker stable under rewrites that are equivalences in Lean?

Basis: execution (Lean kernel check) — `ce_seq_and_comm_changes_definedness`, `ce_seq_contrapose_changes_definedness`, `ce_seq_not_closed`, `ce_seq_not_closed_toNat`.

Non-claims: Boundaries, *Non-claims*, R19.

### R20. restate_signed_difference_with_casts

**Kind:** theorem · **Tier:** T1 · **Depth:** shallow

**Plain claim.** For every connective semantics c, with the intValued reading fixed: for every junk record J and environment rho, the intValued human value of the Nat term a - b (a b : Nat, the Nat variables) is defined and equals the total value of the Int term (a : Int) - (b : Int); (a : Int) - (b : Int) + (b : Int) = (a : Int) (fSubAddCancelCast) is accepted by guarded and Lean-valid; and at every environment and for every junk record, the intValued human value of the trap (a b : Nat), a - b + b = a (fSubAddCancel) is defined and equals the total value of (a : Int) - (b : Int) + (b : Int) = (a : Int).

**Tier rationale.** A worked restatement for this toy language; the general practice of moving Nat subtraction to Int under casts is known (Lean core Int.ofNat_sub).

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:247-250
theorem restate_signedDiff_cast (c : Conn) :
    (∀ (J : Junk) (ρ : Env), hEvalT .intValued ρ (.sub vA vB) = some (evalT J ρ (.sub (.cast vA) (.cast vB)))) ∧
      guarded fSubAddCancelCast = true ∧ LeanValid fSubAddCancelCast ∧
      ∀ (J : Junk) (ρ : Env), hEval c .intValued fSubAddCancel ρ = some (evalJ J fSubAddCancelCast ρ) := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fSubAddCancelCast`: `(a : Int) - (b : Int) + (b : Int) = (a : Int)` (with `a b : Nat`; `leanReading_fSubAddCancelCast`)
- `fSubAddCancel`: `a - b + b = a` (with `a b : Nat`; `leanReading_fSubAddCancel`)

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| reading = intValued (fixed in the first and last conjuncts) | Under partialNat, the Nat subtraction a - b is undefined when a < b. | tight | `ce_restate_signedDiff_partialNat` | the partialNat reading at a = 0, b = 1, with J = leanJ |

Counterexample statements:

```lean
-- lean/ToyJunk/Traps.lean:264-268
theorem ce_restate_signedDiff_partialNat (c : Conn) :
    ¬ (∀ (J : Junk) (ρ : Env),
        hEvalT .partialNat ρ (.sub vA vB) = some (evalT J ρ (.sub (.cast vA) (.cast vB)))) ∧
      ¬ (∀ (J : Junk) (ρ : Env),
        hEval c .partialNat fSubAddCancel ρ = some (evalJ J fSubAddCancelCast ρ)) := …
```

**Non-vacuity.** No hypotheses beyond the universally quantified c, J and rho; the statement fixes the reading intValued (vacuous).

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `ce_shallow_cast_nested_sub`.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [L6] Lean core v4.34.1 `src/Init/Data/Int/Lemmas.lean` (`Int.ofNat_sub`)

**Design question.** How should a statement be written so that its Lean reading and its exact human reading coincide?

Basis: execution (Lean kernel check) — `restate_signedDiff_cast`.

Non-claims: Boundaries, *Non-claims*, R20.

### R21. restate_exact_division_with_nonzero_divisor_guard

**Kind:** theorem · **Tier:** T1 · **Depth:** shallow

**Plain claim.** For every connective semantics c and reading r: (a b : Nat), b | a -> a / b * b = a (fDvdDiv) is Lean-valid and rejected by guarded; at every environment its human value is undefined if a = 0 and b = 0, and true otherwise; adding the premise not (b = 0) gives a formula (fDvdDivGuarded) that is accepted by guarded, Lean-valid and human-valid. The divisor guard is what the checker's division rule asks for, not what human validity needs: (a b : Nat), not (a = 0) -> b | a -> a / b * b = a (fDvdDivDividendGuard) is rejected by guarded, yet Lean-valid and human-valid, and human-true at a = 5, b = 0.

**Tier rationale.** A worked example of a guard antecedent (Gries and Schneider 1995, Section 4) in this toy language, with the exact undefinedness set computed.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:325-328
theorem restate_dvd_div (c : Conn) (r : SubReading) :
    LeanValid fDvdDiv ∧ guarded fDvdDiv = false ∧
      (∀ ρ, hEval c r fDvdDiv ρ = if ρ.nat 0 = 0 ∧ ρ.nat 1 = 0 then none else some true) ∧
      guarded fDvdDivGuarded = true ∧ LeanValid fDvdDivGuarded ∧ HumanValid c r fDvdDivGuarded := …
-- lean/ToyJunk/Traps.lean:294-295
theorem hEval_dvdDiv (c : Conn) (r : SubReading) (ρ : Env) :
    hEval c r fDvdDiv ρ = if ρ.nat 0 = 0 ∧ ρ.nat 1 = 0 then none else some true := …
-- lean/ToyJunk/Traps.lean:350-353
theorem humanValid_dvdDiv_dividend_guard (c : Conn) (r : SubReading) :
    guarded fDvdDivDividendGuard = false ∧ LeanValid fDvdDivDividendGuard ∧
      HumanValid c r fDvdDivDividendGuard ∧
      hEval c r fDvdDivDividendGuard (envAB 5 0) = some true := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fDvdDiv`: `b ∣ a → a / b * b = a` (with `a b : Nat`; `leanReading_fDvdDiv`)
- `fDvdDivGuarded`: `¬ b = 0 → b ∣ a → a / b * b = a` (with `a b : Nat`; `leanReading_fDvdDivGuarded`)
- `fDvdDivDividendGuard`: `¬ a = 0 → b ∣ a → a / b * b = a` (with `a b : Nat`; `leanReading_fDvdDivDividendGuard`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No hypotheses beyond the universally quantified c and r (vacuous).

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [L8] Lean core v4.34.1 `src/Init/Data/Nat/Dvd.lean` (`Nat.div_mul_cancel`)
- [P2] David Gries and Fred B. Schneider (1995)

**Design question.** How should a statement be written so that its Lean reading and its exact human reading coincide?

Basis: execution (Lean kernel check) — `restate_dvd_div`, `hEval_dvdDiv`, `humanValid_dvdDiv_dividend_guard`.

Non-claims: Boundaries, *Non-claims*, R21.

### R22. named_integer_division_characterization

**Kind:** characterization · **Tier:** T0 · **Depth:** shallow

**Plain claim.** For all integers a and b, with / and % Lean's default Euclidean operators: Int.tdiv a b = a / b iff 0 <= a or b | a or b = 0; Int.fdiv a b = a / b iff 0 <= b or b | a; Int.tmod a b = a % b iff 0 <= a or b | a or b = 0; Int.fmod a b = a % b iff 0 <= b or b | a.

**Tier rationale.** Re-derivation from Lean core lemmas Int.tdiv_eq_ediv, Int.fdiv_eq_ediv, Int.tmod_eq_emod and Int.fmod_eq_emod.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:380-384
theorem restate_named_int_division (a b : Int) :
    (Int.tdiv a b = a / b ↔ (0 ≤ a ∨ b ∣ a ∨ b = 0)) ∧
      (Int.fdiv a b = a / b ↔ (0 ≤ b ∨ b ∣ a)) ∧
      (Int.tmod a b = a % b ↔ (0 ≤ a ∨ b ∣ a ∨ b = 0)) ∧
      (Int.fmod a b = a % b ↔ (0 ≤ b ∨ b ∣ a)) := …
```

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No hypotheses (vacuous); at a = -7, b = 2 both sides of the tdiv clause are false (trap_int_rounding_values).

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [L4] Lean core v4.34.1 `src/Init/Data/Int/DivMod/Lemmas.lean` (`Int.tdiv_eq_ediv`, `Int.fdiv_eq_ediv`, `Int.tdiv_eq_ediv_of_dvd`, `Int.fdiv_eq_ediv_of_dvd`, `Int.fmod_eq_emod_of_nonneg`, `Int.fmod_eq_emod`)
- [L2] Lean core v4.34.1 `src/Init/Data/Int/DivMod/Basic.lean` (`Int.ediv`, `Int.emod`, `Int.div`, `Int.mod`)
- [P13] Daan Leijen (2001)
- [P12] Raymond T. Boute (1992)

**Design question.** How should a statement be written so that its Lean reading and its exact human reading coincide?

Basis: execution (Lean kernel check) — `restate_named_int_division`.

Non-claims: Boundaries, *Non-claims*, R22.

### R23. restate_fin_addition_with_bound

**Kind:** theorem · **Tier:** T0 · **Depth:** shallow

**Plain claim.** For every n and all a, b : Fin n, if a.val + b.val < n then (a + b).val = a.val + b.val.

**Tier rationale.** Re-derivation from Lean core's Fin.val_add.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Traps.lean:435-436
theorem restate_fin_add_of_lt {n : Nat} (a b : Fin n) (h : a.val + b.val < n) :
    (a + b).val = a.val + b.val := …
```

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| h : a.val + b.val < n | Without the bound, Fin addition wraps. | tight | `ce_restate_fin_add_bound` | n = 5, a = 3, b = 4 |

Counterexample statements:

```lean
-- lean/ToyJunk/Traps.lean:444-446
theorem ce_restate_fin_add_bound :
    ¬ ((3 : Fin 5).val + (4 : Fin 5).val < 5) ∧
      ((3 : Fin 5) + 4).val ≠ (3 : Fin 5).val + (4 : Fin 5).val := …
```

**Non-vacuity.** (1 : Fin 5) and (2 : Fin 5) satisfy the bound: (1 : Fin 5).val + (2 : Fin 5).val < 5.

```lean
-- lean/ToyJunk/Traps.lean:440
theorem nv_restate_fin_add_of_lt : (1 : Fin 5).val + (2 : Fin 5).val < 5 := …
```

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [L9] Lean core v4.34.1 `src/Init/Data/Fin/Lemmas.lean` (`Fin.val_add`)
- [L5] Lean core v4.34.1 `src/Init/Data/Fin/Basic.lean` (`Fin.add`, `Fin.sub`, `Fin.ofNat`, `Fin.instOfNat`)

**Design question.** How should a statement be written so that its Lean reading and its exact human reading coincide?

Basis: execution (Lean kernel check) — `restate_fin_add_of_lt`.

Non-claims: Boundaries, *Non-claims*, R23.

### R24. bounded_quantifier_guard_rule

**Kind:** theorem · **Tier:** T1 · **Depth:** shallow

**Plain claim.** For every list of facts Gamma, natural variable x, bound term t that does not mention x, and body phi: ballNat x t phi (for all x, x <= t -> phi) is accepted relative to Gamma iff t is guarded by Gamma and phi is guarded by the facts of Gamma that do not mention x together with the fact x <= t. For example, for every connective semantics and reading, for all a : Nat, for all b : Nat with b <= a, a - b + b = a (fBoundedCancel) is accepted by guarded, Lean-valid and human-valid; without the bound, for each connective semantics, for all a b : Nat, a - b + b = a (fUnboundedCancel) is rejected, Lean-false, undefined under partialNat and true under intValued.

**Tier rationale.** The rule is the toy checker's instance of passing a bound as a guard fact to the quantified body; it is stated and proved for this checker and no other.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Quantifiers.lean:205-209
theorem ballNat_guardedIn_iff_of_not_mentionsNat (Γ : List Formula) (x : Nat) (t : Term .nat)
    (φ : Formula) (hm : t.mentionsNat x = false) :
    (ballNat x t φ).guardedIn Γ = true ↔
      t.guardedIn Γ = true ∧
        φ.guardedIn ((Γ.filter fun f => !f.mentionsNat x) ++ [.le (.natVar x) t]) = true := …
-- lean/ToyJunk/Quantifiers.lean:282-283
theorem boundedCancel_guarded_leanValid_humanValid (c : Conn) (r : SubReading) :
    guarded fBoundedCancel = true ∧ LeanValid fBoundedCancel ∧ HumanValid c r fBoundedCancel := …
-- lean/ToyJunk/Quantifiers.lean:299-302
theorem ce_unbounded_cancel (c : Conn) :
    guarded fUnboundedCancel = false ∧ evalJ leanJ fUnboundedCancel Env.zero = false ∧
      hEval c .partialNat fUnboundedCancel Env.zero = none ∧
      hEval c .intValued fUnboundedCancel Env.zero = some true := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fBoundedCancel`: `∀ a b : Nat, b ≤ a → a - b + b = a` (closed; `leanReading_fBoundedCancel`)
- `fUnboundedCancel`: `∀ a b : Nat, a - b + b = a` (closed; `leanReading_fUnboundedCancel`)
- `fSubAddCancel`: `a - b + b = a` (with `a b : Nat`; `leanReading_fSubAddCancel`)

**Hypothesis ledger.** *tight* = a counterexample satisfying all the other hypotheses in which the conclusion fails; its class is recorded.

| Hypothesis | Purpose | Tightness | Counterexample | Witness class |
|---|---|---|---|---|
| hm : t.mentionsNat x = false (ballNat_guardedIn_iff_of_not_mentionsNat) | The bound t lies inside the scope of the quantifier; if t mentions x, that occurrence refers to the bound x. | tight | `ce_ballNat_bound_mentions_var` | Gamma = [a <= b], x = a (natural variable 0), t = b - a (Nat subtraction), body (0 : Nat) = 0 |

Counterexample statements:

```lean
-- lean/ToyJunk/Quantifiers.lean:223-231
theorem ce_ballNat_bound_mentions_var :
    (Term.sub vB vA).mentionsNat 0 = true ∧
      ¬ ((ballNat 0 (.sub vB vA) (.eq (.natLit 0) (.natLit 0))).guardedIn [.le vA vB] = true ↔
        (Term.sub vB vA).guardedIn [.le vA vB] = true ∧
          (Formula.eq (.natLit 0) (.natLit 0)).guardedIn
            (([.le vA vB] : List Formula).filter (fun f => !f.mentionsNat 0) ++
              [.le (.natVar 0) (.sub vB vA)]) = true) ∧
      hEval .seq .partialNat (ballNat 0 (.sub vB vA) (.eq (.natLit 0) (.natLit 0))) (envAB 0 0) =
        none := …
```

**Non-vacuity.** The bound a does not mention b, and for all b : Nat with b <= a, a - b + b = a (Nat subtraction) is accepted with no facts.

```lean
-- lean/ToyJunk/Quantifiers.lean:246-249
theorem nv_ballNat_guardedIn_iff : (vA : Term .nat).mentionsNat 1 = false ∧
    (ballNat 1 vA fSubAddCancel).guardedIn [] = true ∧
    fSubAddCancel.guardedIn (([] : List Formula).filter (fun f => !f.mentionsNat 1) ++
      [.le (.natVar 1) vA]) = true := …
```

**Supporting theorems** (cited by the non-claims; quoted under *Supporting theorems* or *Connective tables*): `guarded_rejects_strict_bound`, `guarded_accepts_vacuous_guards`.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P5] Adam Darvas, Farhad Mehta and Arsenii Rudich (2008)
- [P2] David Gries and Fred B. Schneider (1995)

**Design question.** Can quantification over a junk-dependent body change a statement's truth between the human and the Lean readings?

Basis: execution (Lean kernel check) — `ballNat_guardedIn_iff_of_not_mentionsNat`, `boundedCancel_guarded_leanValid_humanValid`, `ce_unbounded_cancel`.

Non-claims: Boundaries, *Non-claims*, R24.

### R25. flips_under_intValued

**Kind:** counterexample · **Tier:** T1 · **Depth:** shallow

**Plain claim.** Under the intValued reading, for each connective semantics: for all a : Nat, 0 <= a - 1 (fAllZeroLeSubOne) is human-false (at a = 0) and Lean-true, and for all a b : Nat, a - b + b = a (fUnboundedCancel) is human-true and Lean-false.

**Tier rationale.** Concrete instances in this toy language.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Quantifiers.lean:336-338
theorem ce_intValued_forall_humanFalse_leanTrue (c : Conn) :
    hEval c .intValued fAllZeroLeSubOne Env.zero = some false ∧
      evalJ leanJ fAllZeroLeSubOne Env.zero = true := …
-- lean/ToyJunk/Quantifiers.lean:348-350
theorem ce_intValued_forall_humanTrue_leanFalse (c : Conn) :
    hEval c .intValued fUnboundedCancel Env.zero = some true ∧
      evalJ leanJ fUnboundedCancel Env.zero = false := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fAllZeroLeSubOne`: `∀ a : Nat, 0 ≤ a - 1` (closed; `leanReading_fAllZeroLeSubOne`)
- `fUnboundedCancel`: `∀ a b : Nat, a - b + b = a` (closed; `leanReading_fUnboundedCancel`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). The sole parameter of ce_intValued_forall_humanFalse_leanTrue and of ce_intValued_forall_humanTrue_leanFalse is c : Conn (inhabited by kleene and seq); the reading is fixed to intValued, and the formulas are closed (their quantifiers are toy quantifiers inside the formula) and evaluated at Env.zero.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [L1] Lean core v4.34.1 `src/Init/Prelude.lean` (`Nat.sub`, `Nat.div`, `Nat.modCore`)
- [P1] Lean Prover Community (web page)

**Design question.** Can quantification over a junk-dependent body change a statement's truth between the human and the Lean readings?

Basis: execution (Lean kernel check) — `ce_intValued_forall_humanFalse_leanTrue`, `ce_intValued_forall_humanTrue_leanFalse`.

Non-claims: Boundaries, *Non-claims*, R25.

### R26. undefined_to_lean_truth_under_partialNat

**Kind:** counterexample · **Tier:** T1 · **Depth:** shallow

**Plain claim.** Under partialNat, for each connective semantics: for all a : Nat, a - (a + 1) = 0 (fAllSubSucc) is human-undefined (every instance is undefined), true in Lean and false for oneJ; and there exists a : Nat with NOT (a - (a + 1) = 0) (fExSubSuccNe) is human-undefined, false in Lean and true for oneJ. For each connective semantics and reading, (1 : Nat) / 2 = 0 (fOneDivTwo) and for all n : Nat, 2 < n -> 1 / n = 0 (fAllOneDivZero) are human-undefined and true in Lean.

**Tier rationale.** Concrete instances in this toy language.

**Lean statements** (verbatim; proofs elided):

```lean
-- lean/ToyJunk/Quantifiers.lean:356-358
theorem ce_partialNat_forall_undefined_leanTrue (c : Conn) :
    hEval c .partialNat fAllSubSucc Env.zero = none ∧ evalJ leanJ fAllSubSucc Env.zero = true ∧
      evalJ oneJ fAllSubSucc Env.zero = false := …
-- lean/ToyJunk/Quantifiers.lean:377-379
theorem ce_partialNat_exists_undefined_leanFalse (c : Conn) :
    hEval c .partialNat fExSubSuccNe Env.zero = none ∧
      evalJ leanJ fExSubSuccNe Env.zero = false ∧ evalJ oneJ fExSubSuccNe Env.zero = true := …
-- lean/ToyJunk/Quantifiers.lean:403-405
theorem inexact_quotient_undefined_leanTrue (c : Conn) (r : SubReading) :
    hEval c r fOneDivTwo Env.zero = none ∧ evalJ leanJ fOneDivTwo Env.zero = true ∧
      hEval c r fAllOneDivZero Env.zero = none ∧ evalJ leanJ fAllOneDivZero Env.zero = true := …
```

**Named formulas in these statements** (Lean readings with types; definitions under *Named formulas*):

- `fAllSubSucc`: `∀ a : Nat, a - (a + 1) = 0` (closed; `leanReading_fAllSubSucc`)
- `fExSubSuccNe`: `∃ a : Nat, ¬ a - (a + 1) = 0` (closed; `leanReading_fExSubSuccNe`)
- `fOneDivTwo`: `(1 : Nat) / 2 = 0` (closed; `leanReading_fOneDivTwo`)
- `fAllOneDivZero`: `∀ n : Nat, 2 < n → 1 / n = 0` (closed; `leanReading_fAllOneDivZero`)

**Hypothesis ledger.** No hypotheses beyond the universally quantified parameters shown in the statements.

**Non-vacuity.** No propositional hypotheses (vacuous). ce_partialNat_forall_undefined_leanTrue and ce_partialNat_exists_undefined_leanFalse quantify over c : Conn, with the reading fixed to partialNat; inexact_quotient_undefined_leanTrue quantifies over c : Conn and r : SubReading. Conn and SubReading are inhabited; the formulas are closed (their quantifiers are toy quantifiers inside the formula) and evaluated at Env.zero.

**Depth:** shallow.

**Prior art** (full records under Evidence, *Sources*):

- [P2] David Gries and Fred B. Schneider (1995)
- [P1] Lean Prover Community (web page)

**Design question.** Can quantification over a junk-dependent body change a statement's truth between the human and the Lean readings?

Basis: execution (Lean kernel check) — `ce_partialNat_forall_undefined_leanTrue`, `ce_partialNat_exists_undefined_leanFalse`, `inexact_quotient_undefined_leanTrue`.

Non-claims: Boundaries, *Non-claims*, R26.

## Boundaries

### Non-claims

For each result, what it does not show. A remark that points at a refutation cites the proved theorem by name or is marked *not proved here*.

**R0 `lean_reading_is_junk_record_leanJ`.**

- Does not show that the toy language covers Lean's surface syntax: implicit coercion insertion, numeral defaulting and overloaded notation are outside the model, and leanEvalF is itself a definition of this package written with Lean's operators.
- Covers +, -, *, /, %, the cast Nat -> Int and Int.toNat on Nat and Int, with the atoms =, <=, < and divisibility; Fin n, rationals, reals and other operators are not covered.
- Says nothing about other proof assistants or programming languages; their conventions appear in this package as prose (modeling bridge) and are not kernel-checked.
- In this package's human reading, / denotes exact division: DivDom n d (for n d : Int) is d != 0 and d | n, so an inexact quotient with a nonzero divisor, such as (7 : Nat) / 2, is human-undefined and its total value comes from the junk record, whereas ModDom (0 <= n and 0 < d) makes (7 : Nat) % 2 defined. Floor or Euclidean division read as intended (with (7 : Nat) / 2 = 3 not junk) is not modeled. Consequently (7 : Nat) / 2 = 3 (fSevenDivTwo) is junk-dependent although Lean's, the truncating and the flooring records all give 3, and the floor-division identity (a b : Nat), not (b = 0) -> a / b * b + a % b = a (fNatDivModId) is Lean-valid but rejected by guarded, junk-dependent and not defined everywhere (Toy.Junk.inexact_division_is_junk).

**R1 `agreement_where_defined_partialNat`.**

- Does not say where the human value is defined; for unguarded formulas it may be undefined at many or all environments (Toy.Junk.ce_leanValid_not_humanValid), and a formula whose human value is undefined can be Lean-true or Lean-false (Toy.Junk.ce_partialNat_forall_undefined_leanTrue, Toy.Junk.ce_partialNat_exists_undefined_leanFalse).
- Fails for the intValued reading of natural subtraction (Toy.Junk.ce_agreement_intValued, Toy.Junk.ce_intValued_forall_humanFalse_leanTrue).
- The absence of flips holds within the toy language and under this package's reading of / as exact division (an inexact quotient is undefined, not false). For every connective semantics and reading, (1 : Nat) / 2 = 0 (fOneDivTwo) and for all n : Nat, 2 < n -> 1 / n = 0 (fAllOneDivZero) are human-undefined and Lean-true here (Toy.Junk.inexact_quotient_undefined_leanTrue); under a rational-valued human reading in which the quotient of 1 by 2 denotes one half they would be human-false and Lean-true (that reading is not modeled; not proved here). Outside the toy language, (3 : Fin 5) + 4 = 2 is Lean-true (Toy.Junk.trap_fin_wrap).
- The agreement is partly by construction: each junk record is consulted outside the fixed domains (b <= a for Nat subtraction, DivDom for /, ModDom for %, 0 <= z for Int.toNat) and nowhere else (definitions jSub, jDiv, jMod, jToNat), and under partialNat these are the points where the human reading is undefined (definitions hSub, hDiv, hMod, hToNat). The content is the propagation through connectives and quantifiers; adequacy of the domains is supported separately by Toy.Junk.evalJ_leanJ_iff and Toy.Junk.rounding_conventions_agree_on_domains.
- Quantifiers are the strong Kleene quantifiers under both connective semantics (a universal statement is false as soon as one instance is false; Toy.Junk.kleene_quantifier_tables); a strict reading of quantifiers is not modeled.

**R2 `definedEverywhere_implies_junkIndependent`.**

- The converse fails: junk independence does not give definedness (Toy.Junk.ce_junkIndependent_not_definedEverywhere).
- A formula that is Lean-valid and junk-independent need not be human-valid or defined anywhere, even without multiplication by zero: (x : Int) / 0 = x / 0 (fDivZeroRefl) and (x : Int) / 0 = 0 OR NOT (x / 0 = 0) (fDivZeroEM) are true at every environment under every junk record and human-undefined at every environment under both connective semantics and both readings (Toy.Junk.ce_junkIndependent_leanValid_undefined).
- Gives no procedure for deciding definedness; the guard checker guarded is a decidable sufficient condition (Toy.Junk.definedEverywhere_of_guarded).
- Junk records assign out-of-domain values as functions of the operand values, so (x : Int) / 0 and (y : Int) / 0 coincide when x = y; independence from arbitrary per-occurrence choices of junk values is not what JunkIndependent expresses (per-occurrence choices are not modeled; not proved here).
- In this package's human reading, / denotes exact division: DivDom n d (for n d : Int) is d != 0 and d | n, so an inexact quotient with a nonzero divisor, such as (7 : Nat) / 2, is human-undefined and its total value comes from the junk record, whereas ModDom (0 <= n and 0 < d) makes (7 : Nat) % 2 defined. Floor or Euclidean division read as intended (with (7 : Nat) / 2 = 3 not junk) is not modeled. Consequently (7 : Nat) / 2 = 3 (fSevenDivTwo) is junk-dependent although Lean's, the truncating and the flooring records all give 3, and the floor-division identity (a b : Nat), not (b = 0) -> a / b * b + a % b = a (fNatDivModId) is Lean-valid but rejected by guarded, junk-dependent and not defined everywhere (Toy.Junk.inexact_division_is_junk).

**R3 `junkIndependent_does_not_imply_defined`.**

- The first instance depends on strict term evaluation; a human semantics in which 0 absorbs an undefined factor would make (a b : Nat), (a - b) * 0 = 0 defined everywhere (not modeled; not proved here). The second and third instances do not involve multiplication.
- No claim is made about the decidability or complexity of junk independence.

**R4 `agreement_does_not_imply_junkIndependent_or_definedness`.**

- Under partialNat, AgreesWhereDefined holds for every formula (Toy.Junk.agreesWhereDefined_partialNat), so it does not separate formulas under that reading; under intValued it does (Toy.Junk.AgreesWhereDefined_pos, Toy.Junk.AgreesWhereDefined_neg).
- Does not say that the Lean statement (a b : Nat) : a - b <= a is a defective lemma; it says that its truth at a < b rests on Lean's specific junk value 0.
- The Lean truth of (a b : Nat), a - b <= a at a < b rests on truncated subtraction. Readers bring a convention, not the absence of one: under wrapping unsigned subtraction, 0 - 1 is the largest machine value and the inequality is false at a = 0, b = 1, as it is for the junk record oneJ; under subtraction that panics below zero there is no value there, the partialNat outcome. Wrapping subtraction is not modeled (modeling bridge; not proved here).
- The junk record oneJ is a test device, not a convention of any system.

**R5 `validity_transfer_partialNat`.**

- Lean validity does not give human validity without definedness: (x : Int) / 0 = 0 (fDivZero) is Lean-valid but its human value is never defined (Toy.Junk.ce_leanValid_not_humanValid).
- A formula that is Lean-valid and junk-independent need not be human-valid or defined anywhere, even without multiplication by zero: (x : Int) / 0 = x / 0 (fDivZeroRefl) and (x : Int) / 0 = 0 OR NOT (x / 0 = 0) (fDivZeroEM) are true at every environment under every junk record and human-undefined at every environment under both connective semantics and both readings (Toy.Junk.ce_junkIndependent_leanValid_undefined).
- Provides no decision procedure for DefinedEverywhere; the guard checker guarded is a decidable sufficient condition (Toy.Junk.definedEverywhere_of_guarded).
- Validity means truth at every environment of the toy semantics, not provability in any proof system.

**R6 `guarded_fragment_conservativity`.**

- The checker is incomplete: it rejects junk-independent formulas, formulas that are human-valid, and (under strong Kleene) formulas defined everywhere (Toy.Junk.guarded_incomplete_junkIndependent, Toy.Junk.guarded_incomplete_defined, Toy.Junk.guarded_incomplete_disjunctive_guards, Toy.Junk.definedEverywhere_kleene_guardSecond).
- Acceptance by guarded certifies that the human and total truth values coincide; it does not check that hypotheses are satisfiable. For every connective semantics and reading, (a b : Nat), b <= a AND a < b -> a - b = 1 (fContradictoryGuard) and the bounded existential written with an implication, (a : Nat), exists b : Nat, b <= a -> a - b = 1 (fExImpGuard), are accepted by guarded, Lean-valid and human-valid, the first because its premise is never true and the second because b = a + 1 falsifies the premise; the AND form (a : Nat), exists b : Nat, b <= a AND a - b = 1 (fExAndGuard) is not Lean-valid (Toy.Junk.guarded_accepts_vacuous_guards).
- guarded adds no facts across disjunctions (unlike left-to-right well-definedness operators that propagate the negated left disjunct into the right one). For every connective semantics and reading, (a b : Nat), NOT (b <= a) OR a - b + b = a (fOrNegGuardSubCancel) and (a b : Nat), b = 0 OR a % b < b (fModDisjGuard) are rejected by guarded although both are human-valid (Toy.Junk.guarded_incomplete_disjunctive_guards).
- Guards are matched syntactically: a strict bound b < a, a fact 0 < d for a Nat divisor, or a guard implied by other facts is not recognized (Toy.Junk.guarded_rejects_strict_bound for b < a; the other two cases are not proved here).
- In this package's human reading, / denotes exact division: DivDom n d (for n d : Int) is d != 0 and d | n, so an inexact quotient with a nonzero divisor, such as (7 : Nat) / 2, is human-undefined and its total value comes from the junk record, whereas ModDom (0 <= n and 0 < d) makes (7 : Nat) % 2 defined. Floor or Euclidean division read as intended (with (7 : Nat) / 2 = 3 not junk) is not modeled. Consequently (7 : Nat) / 2 = 3 (fSevenDivTwo) is junk-dependent although Lean's, the truncating and the flooring records all give 3, and the floor-division identity (a b : Nat), not (b = 0) -> a / b * b + a % b = a (fNatDivModId) is Lean-valid but rejected by guarded, junk-dependent and not defined everywhere (Toy.Junk.inexact_division_is_junk).
- Covers the toy language (Nat and Int terms with +, -, *, /, %, the cast Nat -> Int and Int.toNat; atoms =, <=, <, divisibility). Fin n, rationals, reals and user-defined functions are not covered. The toy has no implicit casts, so 'every cast is explicit' holds by construction rather than being checked.
- Gives no translation from Lean source statements into the toy language, so it does not by itself certify any Lean statement.

**R7 `guarded_validity_transfer`.**

- Acceptance by guarded certifies that the human and total truth values coincide; it does not check that hypotheses are satisfiable. For every connective semantics and reading, (a b : Nat), b <= a AND a < b -> a - b = 1 (fContradictoryGuard) and the bounded existential written with an implication, (a : Nat), exists b : Nat, b <= a -> a - b = 1 (fExImpGuard), are accepted by guarded, Lean-valid and human-valid, the first because its premise is never true and the second because b = a + 1 falsifies the premise; the AND form (a : Nat), exists b : Nat, b <= a AND a - b = 1 (fExAndGuard) is not Lean-valid (Toy.Junk.guarded_accepts_vacuous_guards).
- The guarded restatement (a b : Nat), b <= a -> a - b + b = a says nothing at environments with b > a (its premise is false there), whereas the intValued reading of the unguarded (a b : Nat), a - b + b = a asserts the integer identity there as well; that reading is treated in Toy.Junk.restate_signedDiff_cast.
- Validity is semantic truth at every environment of the toy, not provability; no claim about Lean statements outside the toy language.

**R8 `guard_checker_incomplete`.**

- Does not quantify the loss and claims no completeness result for any sub-fragment; no checker that accepts these formulas is defined here.

**R9 `trap_truncated_subtraction`.**

- These are closed instances; the open formulas (a b : Nat), a - b + b = a and (a b : Nat), a - b <= a are treated by other theorems (Toy.Junk.ce_not_humanValid_not_leanValid, Toy.Junk.ce_agrees_not_junkIndependent).
- Both Lean values rest on truncated subtraction, (0 : Nat) - 1 = 0. Readers of (0 : Nat) - 1 bring a convention, not the absence of one: integer subtraction (the intValued reading), subtraction that panics or traps below zero (no value; the closest toy outcome is the partialNat value, undefined), or wrapping unsigned machine subtraction, under which 0 - 1 is the largest machine value, so 0 - 1 + 1 = 0 would be true and 0 - 1 <= 0 false. Lean's truncation agrees with none of these below zero. Wrapping subtraction is not modeled, and no relation between the toy readings and any machine or language semantics is proved (modeling bridge; not proved here).

**R10 `trap_division_by_zero`.**

- Does not claim that any other proof assistant uses the same values; the system checked is Lean core v4.34.1.
- Lean's (5 : Int) / 0 = 0 and (5 : Nat) % 0 = 5 are totalizing conventions. Readers bring a convention for division by zero, not the absence of one: that it is undefined (as in mathematics), or that it traps, panics or is undefined behaviour (conventions found in programming languages); Lean's values match none of these. The toy represents all of them by the undefined human value, and no relation to any language's semantics is proved (modeling bridge; not proved here).

**R11 `trap_floor_division_read_as_exact`.**

- Under a rational-valued reading in which the quotient of 7 by 2 denotes 3.5 the statement would be human-true (not modeled; not proved here).
- In this package's human reading, / denotes exact division: DivDom n d (for n d : Int) is d != 0 and d | n, so an inexact quotient with a nonzero divisor, such as (7 : Nat) / 2, is human-undefined and its total value comes from the junk record, whereas ModDom (0 <= n and 0 < d) makes (7 : Nat) % 2 defined. Floor or Euclidean division read as intended (with (7 : Nat) / 2 = 3 not junk) is not modeled. Consequently (7 : Nat) / 2 = 3 (fSevenDivTwo) is junk-dependent although Lean's, the truncating and the flooring records all give 3, and the floor-division identity (a b : Nat), not (b = 0) -> a / b * b + a % b = a (fNatDivModId) is Lean-valid but rejected by guarded, junk-dependent and not defined everywhere (Toy.Junk.inexact_division_is_junk).
- Lean's (7 : Nat) / 2 = 3 is floor division. Readers bring a convention, not the absence of one: exact or rational division (under which 7 / 2 is 3.5, or has no integer value; the toy's human reading takes the second), or the integer division of programming languages, which also gives 3 for these nonnegative operands; the trap concerns the first convention (modeling bridge; not proved here).

**R12 `trap_integer_rounding`.**

- Does not state which convention any programming language uses; remarks about truncating division in C or Rust are modeling-bridge prose and are not kernel-checked.
- Readers bring a rounding convention for negative operands, not the absence of one, typically truncation toward zero (Int.tdiv, Int.tmod) or flooring (Int.fdiv, Int.fmod); Lean's default / and % are Euclidean (Int.ediv, Int.emod), and at (-7, 2) and (7, -2) the three conventions do not all agree (Toy.Junk.trap_int_rounding_values). Which convention a given reader brings is not examined (not proved here).
- Int.div and Int.mod do not exist in Lean core v4.34.1 (removed in December 2024 according to the core module comment); older material using those names referred to truncating division.

**R13 `rounding_conventions_agree_on_domains`.**

- Neither DivDom nor ModDom is the largest agreement set: the quotients Int.tdiv n d and n / d coincide iff 0 <= n or d | n or d = 0, and Int.fdiv n d and n / d iff 0 <= d or d | n (for instance at n = 7, d = 2, outside DivDom); the remainders likewise (Toy.Junk.restate_named_int_division).
- Does not justify reading / as exact division; what it shows is that the domains used by the total semantics hide no choice of rounding convention.

**R14 `trap_fin_wraparound`.**

- Fin n is outside the toy language; the agreement, guard and quantifier results say nothing about Fin arithmetic.
- Wrap-around is the documented meaning of Fin addition and subtraction (modulo n); it is a trap for a reader who reads + on Fin n as exact natural-number addition, not for one who reads it modulo n.

**R15 `trap_cast_placement_and_toNat`.**

- The toy does not model where Lean's elaborator inserts coercions; which of the two cast placements a given Lean source statement elaborates to must be checked in Lean.
- The first Lean value rests on truncated subtraction inside the cast ((0 : Nat) - 1 is 0 before it is cast), and (-3 : Int).toNat = 0 on the truncation of negative integers to 0. Readers bring a convention, not the absence of one: integer subtraction (the cast equation holds, as in the intValued reading), subtraction that panics below zero (no value; the closest toy outcome is the partialNat value, undefined), or wrapping unsigned subtraction followed by a widening cast (the cast of the largest machine value); for Int.toNat, an error, a saturating conversion (which also gives 0 here) or a bit-reinterpreting conversion. Wrapping and reinterpreting conversions are not modeled, and no relation to any language's semantics is proved (modeling bridge; not proved here).

**R16 `trap_numeral_typing`.**

- The toy does not model numeral defaulting; the unannotated conjuncts are checked directly in Lean core v4.34.1, where the default numeral instance is instOfNatNat.
- The Nat value rests on truncated subtraction, (2 : Nat) - 3 = 0. A reader who brings integer subtraction expects 2 - 3 < 0 to hold (as it does at Int and in the intValued reading); one who brings subtraction that panics below zero expects no value; one who brings wrapping unsigned subtraction expects a large positive value, so that 2 - 3 < 0 and 2 - 3 = 0 are both false. Wrapping subtraction is not modeled (modeling bridge; not proved here).

**R17 `guarded_fragment_not_closed_under_lean_equivalences`.**

- Concerns the checker's verdict, not semantic definedness. Whether a sound checker can restore closure depends on the connective semantics: under sequential connectives even the semantic class of everywhere-defined formulas fails closure under both rewrites (Toy.Junk.ce_seq_not_closed), so no checker sound for sequential connectives can accept both members of either pair; under strong Kleene connectives the class of everywhere-defined formulas is closed under both rewrites (Toy.Junk.definedEverywhere_kleene_closed), and a symmetric checker that lets later conjuncts or negated consequents supply facts is not defined or examined here.
- Says nothing about closure under other Lean equivalences (associativity, distributivity, de Morgan) beyond the two shown.

**R18 `kleene_definedness_closed_under_comm_and_contraposition`.**

- Does not extend to the syntactic checker, which is closed under neither rewrite (Toy.Junk.ce_guarded_not_closed_under_and_comm, Toy.Junk.ce_guarded_not_closed_under_contrapose).

**R19 `sequential_connectives_break_closure`.**

- Under the intValued reading natural subtraction is always defined, so the Nat-subtraction formulas above are defined everywhere even with sequential connectives (Toy.Junk.seq_defined_intValued); the toNat formulas separate the connective semantics under both readings.

**R20 `restate_signed_difference_with_casts`.**

- Stated for the atomic Nat variables a, b and the single formula (a b : Nat), a - b + b = a; it says nothing about other formulas. Casting compound Nat subterms shallowly as (t : Int) - (u : Int) does not match the intValued reading when t or u contains a nested Nat subtraction: with t = (0 : Nat) - 1 and u = (0 : Nat), the intValued value of the Nat term t - u is -1 while Lean's value of ((0 - 1 : Nat) : Int) - ((0 : Nat) : Int) is 0 (Toy.Junk.ce_shallow_cast_nested_sub). Translating Nat formulas with quantifiers or % into Int needs explicit nonnegativity and domain guards (not proved here).
- Concerns the toy cast; it does not address where Lean's elaborator places coercions in source statements.

**R21 `restate_exact_division_with_nonzero_divisor_guard`.**

- Does not claim that b != 0 is needed for the Lean-validity of the divisibility statement; it is not (first conjunct of restate_dvd_div, and Lean core's Nat.div_mul_cancel has no such hypothesis).
- Does not identify a weakest guard in general; what it shows is that the undefinedness set of this one formula is the single point a = b = 0.

**R22 `named_integer_division_characterization`.**

- The b = 0 disjunct for tdiv and tmod is easy to miss: all three conventions give (a : Int) / 0 = 0 and (a : Int) % 0 = a in Lean core, so they agree at b = 0 even when 0 <= a and b | a both fail. This agreement comes from Lean core's convention; Boute (1992) and Leijen (2001) treat nonzero divisors, and programming languages in which division by zero traps or is undefined are not covered (modeling bridge, not proved here).
- Characterizes agreement with the default operator; it does not say which convention a given statement should use.

**R23 `restate_fin_addition_with_bound`.**

- Fin n is outside the toy language; this is a Lean-core fact, not an instance of the guard theorem.
- The bound inspects the already-reduced values of a and b: an operand written as an out-of-range numeral has wrapped before the bound is checked (in Fin 3, (1 : Fin 3).val + (4 : Fin 3).val < 3 holds while ((1 : Fin 3) + 4).val is not the natural number 1 + 4; Toy.Junk.trap_fin_numeral_wraps_before_bound).
- Degenerate modulus: at n = 0 the statement holds vacuously, because Fin 0 has no elements (a.val < 0 is impossible); the non-vacuity witness is at n = 5 (Toy.Junk.nv_restate_fin_add_of_lt). Fin n arithmetic wraps modulo n (Toy.Junk.trap_fin_wrap), which matches a reader who brings wrapping machine arithmetic with modulus n and not one who reads + as natural-number addition.

**R24 `bounded_quantifier_guard_rule`.**

- The rule concerns the checker's verdict; the semantic agreement for accepted formulas comes from Toy.Junk.hEval_eq_some_evalJ_of_guarded.
- Bounds must be written as the fact x <= t: strict bounds such as b < a or b < a + 1 are rejected (Toy.Junk.guarded_rejects_strict_bound).
- A bounded existential must be written with AND (exists b, b <= a AND phi), not with an implication (exists b, b <= a -> phi), which is accepted and valid by vacuity (Toy.Junk.guarded_accepts_vacuous_guards).

**R25 `flips_under_intValued`.**

- These flips come from the intValued reading of natural subtraction, not from quantification as such: quantifier-free instances already disagree ((2 : Nat) - 3 < 0, Toy.Junk.ce_agreement_intValued; (a b : Nat), a - b + b = a, human-valid under intValued and not Lean-valid, Toy.Junk.ce_intValued_humanValid_not_leanValid).
- Under partialNat no flip occurs in the toy language (Toy.Junk.no_flip_partialNat); a rational-valued reading of / would produce flips such as (1 : Nat) / 2 = 0 read with the quotient of 1 by 2 denoting one half (not modeled; not proved here).
- Both Lean values rest on truncated subtraction (a - 1 = 0 at a = 0, and a - b = 0 when a < b). Readers bring a convention, not the absence of one: integer subtraction (the intValued reading used here), subtraction that panics below zero (no value at a = 0, or where a < b), or wrapping unsigned subtraction, under which 0 <= a - 1 holds trivially and a - b + b = a holds because the wrap-around cancels. Wrapping subtraction is not modeled (modeling bridge; not proved here).

**R26 `undefined_to_lean_truth_under_partialNat`.**

- Does not show a human-false statement that is Lean-true under partialNat; in the toy language that is impossible (Toy.Junk.no_flip_partialNat).
- The absence of flips holds within the toy language and under this package's reading of / as exact division (an inexact quotient is undefined, not false). For every connective semantics and reading, (1 : Nat) / 2 = 0 (fOneDivTwo) and for all n : Nat, 2 < n -> 1 / n = 0 (fAllOneDivZero) are human-undefined and Lean-true here (Toy.Junk.inexact_quotient_undefined_leanTrue); under a rational-valued human reading in which the quotient of 1 by 2 denotes one half they would be human-false and Lean-true (that reading is not modeled; not proved here). Outside the toy language, (3 : Fin 5) + 4 = 2 is Lean-true (Toy.Junk.trap_fin_wrap).
- The Lean values of the first two formulas rest on truncated subtraction (a - (a + 1) = 0), and those of the last two on floor division ((1 : Nat) / 2 = 0). Readers bring a convention, not the absence of one: subtraction that panics below zero (no value, the partialNat outcome), wrapping unsigned subtraction (a - (a + 1) is the largest machine value, so the universal formula would be false and the existential true), or integer subtraction (a - (a + 1) = -1, with the same truth values). Wrapping subtraction is not modeled, and the integer-reading values of these two formulas are not proved here.

### Escape hatches

The package has one impossibility result, `guarded_fragment_not_closed_under_lean_equivalences` (R17). Its conclusion is a property of the checker `guarded`, which accumulates facts left to right:

- Under strong Kleene connectives the semantic class of everywhere-defined formulas *is* closed under both rewrites (`definedEverywhere_kleene_closed`, its positive control), so the non-closure is not a property of the semantics; a checker that also lets later conjuncts or negated consequents supply facts would escape the counterexamples, but no such checker is defined or examined here.
- Under sequential connectives the semantic class itself is not closed (`ce_seq_not_closed`), so no checker that is sound for sequential connectives can accept both members of either pair.

For the theorems, the hypotheses whose removal defeats the conclusion are the `tight` entries of each hypothesis ledger, each with a counterexample theorem; in particular every agreement result (R1, R2, R5) fails when `partialNat` is replaced by `intValued`, and every guard result (R6, R7) fails for some formula rejected by `guarded`.

### Hypotheses of unknown tightness

No hypothesis of any result has tightness `unknown`; every listed hypothesis is `tight`, with a counterexample theorem.

### Disproved or dropped statements

No stated result of this package was disproved or left unproved: every Lean statement listed in `results.json` is proved, and no statement was removed.

### Not examined

- Statements written in Lean source files: there is no translation into the toy language, so no result applies to a source statement without a separate argument that the statement corresponds to a toy formula.
- Lean versions other than `v4.34.1`, Mathlib, and other proof assistants or programming languages.
- Floor or Euclidean division read as intended by the human reading, rational-valued readings of `/`, and other domains for `/` and `%` than `DivDom` and `ModDom`.
- Human semantics in which `0` absorbs an undefined factor, strict (non-Kleene) quantifiers, per-occurrence junk choices, and guard checkers other than `guarded` (for instance a symmetric checker that lets later conjuncts supply facts).
- Operators outside the toy language (other than the listed `Fin` facts): `Fin` arithmetic inside the toy, rationals, reals, bit operations, user-defined functions.

## Evidence

**Toolchain.** `leanprover/lean4` `v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (resolved through the GitHub API, `git/ref/tags/v4.34.1`, object type `commit`). Core library only; no Mathlib. `lean/lakefile.toml` declares one `[[lean_lib]]` (`ToyJunk`) and no `[[require]]`.

**Build and axioms.** `lake build` of `lean/` succeeds with no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations. Every one of the 890 declarations of the `ToyJunk` library depends at most on the axioms `Classical.choice`, `Quot.sound`, `propext` (computed with Lean's `collectAxioms`; recorded per declaration in `audit/axioms.json`). `Classical.choice` enters through the classical decision of unbounded quantifiers in `evalJ`, `tvAll` and `tvEx`.

**Statement hashes.** For each Lean name referenced by `results.json`, `audit/statements.json` records the SHA-256 of the statement (the Lean `repr` of its type) and of its definition closure (the sorted lines `name : repr(type) [:= repr(value)]` of every `ToyJunk` constant reachable from the statement, theorem bodies excluded), with the closure size. The table lists, for every such name, the results that use it and in which role, its axioms, and both hashes as recorded in `audit/statements.json`.

| Lean name (`Toy.Junk.`) | Used by | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|---|
| `evalJ_leanJ_iff` | R0 result | Classical.choice, Quot.sound, propext | `e92b3d8cf839a13d7220ca4cfcb0d91356a37e738ca687b850b2a7478ad08588` | `922306ecde4b4372e6949ccc8843526b934d3b1de900a324844d9bb85baf5cb8` (86) |
| `evalT_leanJ` | R0 result | propext | `967b3bbcfb1ef7269c68fe3fb63b41531668c6948cfbb8515c660adfc3cfb82b` | `1c0237e73f89dbd77e164c2310d8d7c5d7af1879f1a911aaf0e3bbcda003c940` (56) |
| `inexact_division_is_junk` | R0 supporting; R2 supporting; R6 supporting; R11 supporting | Classical.choice, Quot.sound, propext | `862fd70168efacfbe0e30ef613cedb5dee24ab49efcc6f3ba2f027f5dc902447` | `8b8e97e2d49b474455b800259848c309148ebff14c9c02d22c8563de3fbea80a` (218) |
| `leanReading_fAllOneDivZero` | R0 reading | Classical.choice, Quot.sound, propext | `257e08542dd9efb1e538e218bd800e23328d5ddad13e9bf9ab5ed1df5e810caa` | `11c231a57ded2f23f363038b815e6e3bfbea733b1e6b7204977875e41166ca4e` (80) |
| `leanReading_fAllSubSucc` | R0 reading | Classical.choice, Quot.sound, propext | `eb9226edba47a150060746006e3bba96fdd2030f753c839f711ee8dcf42604e4` | `e9826bf6db6e15cec22df5f12e61b1c0e62b554a645fe315f4c085b96465744a` (80) |
| `leanReading_fAllZeroLeSubOne` | R0 reading | Classical.choice, Quot.sound, propext | `fbdae716aad6ed8b7d3b9998d5c66c42ee967ad0cdd8891700bd4f22a5630120` | `ab7919c196c5b7959878abc02b0ceecbec5ad7b868e91d752442818607ed3aab` (80) |
| `leanReading_fBoundedCancel` | R0 reading | Classical.choice, Quot.sound, propext | `85ab6584a06533ae49c4b1cc869fa77d249d58b5552cdf73f6a488839919a8cf` | `8b09dbdef8101a2c213eef7bbec4fb58a7c9b5c900be5879ac51f6f6c8db820c` (83) |
| `leanReading_fCastPlacement` | R0 reading | Classical.choice, Quot.sound, propext | `cb33967c3f7acb2f0016cec756bb9bc5b041c8c5ef57182fde5fa69df2f86b15` | `10681e9e6b4d11c34a0716cd61c30e98f9e21f1514cb7099c5fe24120736dc02` (82) |
| `leanReading_fCastPlacement01` | R0 reading | Classical.choice, Quot.sound, propext | `58d0d47ee777efdb71d7de86f289f0c738cfd6dd9d0ffa46fa9d77538a816024` | `8dc9f42506d24fce2533485e1e9fd8ee622e08cf267c3d1e548831da7caa821a` (79) |
| `leanReading_fContradictoryGuard` | R0 reading | Classical.choice, Quot.sound, propext | `46162ef84fd196f7c60c630d5320888546f16655bc4a6e0fe481cdbfd16291c2` | `bea3572e0bf512eb1d7caf8db833325b524689d2ae67486aca07f8b9406c2ca4` (82) |
| `leanReading_fContrapositive` | R0 reading | Classical.choice, Quot.sound, propext | `f76b84aeff3b84a10c20ca3c9d4efd9ed55815148afe821ad69047c204021116` | `b3e94e23bc84e31871e7692eae4edef6a01bc00c25d04dea6e38478532628776` (83) |
| `leanReading_fDivZero` | R0 reading | Classical.choice, Quot.sound, propext | `d52d914fe1c9acc84ad878484891a37288ca889a9c4ca3de545388422fe6975b` | `29dddfdfe3e8ef2dd7c90b94c334b4e2c55c355b4371eea573305be7daea17b2` (81) |
| `leanReading_fDivZeroEM` | R0 reading | Classical.choice, Quot.sound, propext | `87858f2aa8ed248a4d78c4140471dbdbbb54eb03e8d0ee3df0030abdec7df3ce` | `d17dc655def1488a1e7d9eed7cf78cc92ca6d6dd6042ce90ddd6a8081f46f307` (82) |
| `leanReading_fDivZeroRefl` | R0 reading | Classical.choice, Quot.sound, propext | `475009b089f7b19577374c73d47faa33f90e3f9df445b9245779130061106346` | `06df1421e09375d031aeb771c966015c80b29f5cf40d3570f70e9f852542ec2c` (81) |
| `leanReading_fDvdDiv` | R0 reading | Classical.choice, Quot.sound, propext | `822bcefe192ab32e8b64c3d619f34cbb534f40165b217a08f8cd49277810b7c1` | `f6537c7cb61e75944a47499aaa66e8a83782bb40b0156e2ff6059b22c2686c52` (82) |
| `leanReading_fDvdDivDividendGuard` | R0 reading | Classical.choice, Quot.sound, propext | `b1fac9a2ecf36835035415f3523a3f8e59c2e12b46bf94766b5ded8b35b9e259` | `5c1872e94b2c1ef70b5b465975a2705f32b1c9e04c72d355d7f7aa58cd78714d` (83) |
| `leanReading_fDvdDivGuarded` | R0 reading | Classical.choice, Quot.sound, propext | `8cabd71f9137313be6701562209ed6b524fcacde98b7e7f9343edb7b26b7b171` | `c3be8f2a5eae68883daba1bca11656aab078a0962e20e24b64f2b549e4e75e65` (83) |
| `leanReading_fExAndGuard` | R0 reading | Classical.choice, Quot.sound, propext | `1afd312f69f3cb37a56f41f775582121240341fc0ab0a75b103d31b5dd52e207` | `4b50ad473f9231a901c41866f726c01d218398211d9de768318cc44d9f4fa8d6` (82) |
| `leanReading_fExImpGuard` | R0 reading | Classical.choice, Quot.sound, propext | `5c9fdd6daa10e64d27f3b0776380a0307bec29c68d7923f299ce7062bff555fa` | `16269dd5823ff5f69f7edd82df7473ca2bda0eb66461b72884a7c4de35a15ec5` (82) |
| `leanReading_fExSubSuccNe` | R0 reading | Classical.choice, Quot.sound, propext | `a775fbd1b9b3034daeb60945eaf7e16ae5066a0f2735e25a795d77ceb16187a0` | `1bc5aed79efc60ced745ae20691e180cddf4cb7f24837ddb00d73b01e4071f23` (80) |
| `leanReading_fFiveDivZero` | R0 reading | Classical.choice, Quot.sound, propext | `3a4592c306297e7c5351b5feb912e061089ce87a58288c0277281c618a349d27` | `070df6354d115e588531293e620ee91ea8f3cbdd5419d5a1aef6204d2db913c9` (79) |
| `leanReading_fFiveModZero` | R0 reading | Classical.choice, Quot.sound, propext | `fc9503ef48f035f71fef4e5c22e54089347b95fec76795ef2c4cc29a7bbcc1c4` | `47db76647a181b39ac58e875a51dcac046bd8ed04ce7c96b2fe9bf59d05d9c77` (79) |
| `leanReading_fFiveSubThree` | R0 reading | Classical.choice, Quot.sound, propext | `dade1026cc61542e83b1afc05cdd1e342cb64617f6b4f20c13c50b3f4b69f2a4` | `df1b4eb104b6bed3d009f78860f69fb36beabb5faab97a0c8f77b2f4c9aee481` (79) |
| `leanReading_fFloorDiv` | R0 reading | Classical.choice, Quot.sound, propext | `9d4aa629c707f6130abf493969217627fcf9a167ae3e8aa5bba181c905284d36` | `b58e4a66f48c5767f40772e3d1639e5436b05dd4ffcf0f56253474f2a10a886e` (79) |
| `leanReading_fGuardFirst` | R0 reading | Classical.choice, Quot.sound, propext | `8d1f702b7b5785f98a7a2f0fde72ea230799dffc9224e525e20b63b8ef74811c` | `a823a5e85b7b5aa3fdea69e2d85f4d91bfdc9d12aa340ce8d824f4e55dafc150` (83) |
| `leanReading_fGuardSecond` | R0 reading | Classical.choice, Quot.sound, propext | `3cc4068f2d2a5237a189485757c2af0f70397469fb2b5759fa283726c479e081` | `02f156b86f83847da9f1d63960018f577edd2c24253f404561098dc324b13475` (83) |
| `leanReading_fGuardedIntDiv` | R0 reading | Classical.choice, Quot.sound, propext | `29c86bbe04bdcf3046bda0bc5cf7ca3f90c1b6756fcd73c4ce8305eb9023726c` | `a3b2624d2d94057d8db21c970e79a03c3dea3aba5e6d7aad2f7d5e825a924901` (81) |
| `leanReading_fGuardedIntMod` | R0 reading | Classical.choice, Quot.sound, propext | `0e7b2b8623a313b8bc9c38266810303b6496557203300e9c807e986d6adf5428` | `12d6175011ee238e47fc02a737dab03ef298998117f4e336425dd91dd076acb6` (81) |
| `leanReading_fGuardedNatMod` | R0 reading | Classical.choice, Quot.sound, propext | `594ac111b6ed2a6bbc029b485099b140d08a92bd6988d86a5213284984a2aedb` | `1afba3d94110783eaa343524c29354d5824c16405c4b4b4ee108c6781bc40f2f` (82) |
| `leanReading_fGuardedToNat` | R0 reading | Classical.choice, Quot.sound, propext | `807ab7ca7c880f063d6d39bb73bb0f7e005ccfc77069df6604927b7564c1cbc3` | `82ba17556e33a97fde54c02c80e01470a6657868f77c773114af6170c70c76b8` (81) |
| `leanReading_fModDisjGuard` | R0 reading | Classical.choice, Quot.sound, propext | `a09ca0fd8067a2c505cc683fd5347cfd8ac4cc14b54896573b9171a260be9b6f` | `164e3a7f5f40cecf65b3cad2109e04142b2aefc3c210ad350126e34adb51ce92` (82) |
| `leanReading_fMulZero` | R0 reading | Classical.choice, Quot.sound, propext | `8570cc9f9c9ab35d65828266eabb612d8c22e878a9b3fb6336cabbed420e5d27` | `e342423c64c3662cad571e29cbf594c4bdb94b9f65feb162cc0f8424fb06a772` (82) |
| `leanReading_fNatDivModId` | R0 reading | Classical.choice, Quot.sound, propext | `a72ca41652f82e0db4df8e9d84820864d9daa1f1714dff3bd9fcfbc4b5d26eeb` | `816e8e0f3bbc1d6b37e20286ae97d2a084a521bf03c1bf891c6f5815c593320a` (82) |
| `leanReading_fNegSevenDivTwo` | R0 reading | Classical.choice, Quot.sound, propext | `84ba957b40939c7d46d229e746aeb4cfc82bf7dcc1e5dcec7f1dbfebc5d87916` | `fac2bf380fcc340734fcab04d9659ae5a86ec8959b3ddff4edeb3c8b0eb51fe6` (79) |
| `leanReading_fNegSevenModTwo` | R0 reading | Classical.choice, Quot.sound, propext | `7f3bce18d64f39ad59f526a358051d096cc645bd0788284467b73cbb5562bd9d` | `b206011dce4a9265f022ee1d9fd802f270420f46cf87b82f1545a07d55d844a1` (79) |
| `leanReading_fNumeralInt` | R0 reading | Classical.choice, Quot.sound, propext | `813e5f4afed654656bfd035f2bbdbd032694e47b300fc0e484b494a35c4488c0` | `bc6493e6055c40938b273c95adb9606890391ebcb19f440f1a211afb51c54054` (79) |
| `leanReading_fNumeralNat` | R0 reading | Classical.choice, Quot.sound, propext | `ad8522d662e30d9cf20b553dfbef42f332bd1fda546b6efc7ded17b57a8f01a5` | `8e1b3f63b240b9ce9e1897b08ff8a31895c3c1d82f686a6dbb9f4f6104f1b84b` (79) |
| `leanReading_fOneDivTwo` | R0 reading | Classical.choice, Quot.sound, propext | `4900e78012c31feaf27866de21e29dedf9b118ec6217d8fb2c8d1a9d944ee547` | `7061c1f858f5ef36ee106afa48e94deb20fd288947ba78922a302eb39318a987` (79) |
| `leanReading_fOrNegGuardSubCancel` | R0 reading | Classical.choice, Quot.sound, propext | `570e986e7f6c649da549bb6ad29bf58743dd20dd50ff893fc87e4c83a42d50ce` | `6f639f5321e9c67d86d1689e1871e7e557ef92923e325e120b383a42d24ad468` (83) |
| `leanReading_fSevenDivNegTwo` | R0 reading | Classical.choice, Quot.sound, propext | `4d7824af71e938dda85da2eeee7f7d2173a3029b5f6e656718db9e716b08f693` | `5f08e99a604aa27751739648fd50681af61be96167e792194c7a10201ea27626` (79) |
| `leanReading_fSevenDivTwo` | R0 reading | Classical.choice, Quot.sound, propext | `183f76ec62adc6a67f2638180187d6e40d9d435b2c8806d5dfaf28700b96597c` | `80a537a8cdb7ebae4de39eb413f86c651c20f1d35843b614cdb9bb7f3e572316` (79) |
| `leanReading_fSevenModNegTwo` | R0 reading | Classical.choice, Quot.sound, propext | `cac134b1a1094a2cb82704b9587c09289d2637b87e5e77c4159b35d06b0470d8` | `a4a896f2252096dce85627f92080963694b8565757b03ae649b00842ae046fbc` (79) |
| `leanReading_fSevenModTwo` | R0 reading | Classical.choice, Quot.sound, propext | `c96fdc961f995c1755f49992b3c68de90904314b250c2aecbfc0c430d9c9d052` | `b16791cb5606a88dbec892b8e8ed9e6b142887aa20c64d7ded3e96c6142b099a` (79) |
| `leanReading_fStaleGuard` | R0 reading | Classical.choice, Quot.sound, propext | `4ec439f8983d18a1f965881690b789f1d94796e9b34944bf0644c24d1a070211` | `50d291bd34bf4dd3d226c8002f7a15ec424319bc24176b8d4123d66afba36bb1` (83) |
| `leanReading_fSubAddCancel` | R0 reading | Classical.choice, Quot.sound, propext | `2e75b930973c6f7654db4a9204a6f1a14eb5a0610d8c728c8117a8c0f2ba2b04` | `7f3a4cf28e5a59a708cfedc7dfb059c12e6da31a52ef81aa9ec865586b31902c` (82) |
| `leanReading_fSubAddCancelCast` | R0 reading | Classical.choice, Quot.sound, propext | `16f2e9ac9366b0ef2ecb28c41c9c8e592f591c71750b071092b837c0686b7dc6` | `d58bc1487f0e7f8e509f0f4846b755f33cfe4374603d99348931da757d9fe5aa` (82) |
| `leanReading_fSubAddCancelGuarded` | R0 reading | Classical.choice, Quot.sound, propext | `c73f056a99bff07a32e50756fdc50b6aa06731c64a9d7f9b23d6e14bcf1fd53e` | `5bb51c6ea75e0a9797e0dc0805349847096dd1694ff73ea18d29722545a02511` (83) |
| `leanReading_fSubLeSelf` | R0 reading | Classical.choice, Quot.sound, propext | `fe12a7ca57056d03bf917b5fcbd2545f154362fc5862361b850626b22923d107` | `c6c8e4726d301e3082e174108fbbf5ae61402bed2456c3b6ff38ae745dfe3dc5` (82) |
| `leanReading_fToNatContrapose` | R0 reading | Classical.choice, Quot.sound, propext | `f903468890533ccd120006d476ec5656d7af23c9c637ef221bb2c92246d70f60` | `9bd0c5a50cffe3f1bf24c82232134ff499d4bc76a0599e41476f9c56e778103b` (81) |
| `leanReading_fToNatGuardFirst` | R0 reading | Classical.choice, Quot.sound, propext | `40cc333cfd272f72bab73dc039e1245ba88ec1126dd27eb718252ebb25546e53` | `bc800d2ec32dc63d833b17135a4fb7858694c78b98bcfa6b85393fe70ee4cdfc` (81) |
| `leanReading_fToNatGuardSecond` | R0 reading | Classical.choice, Quot.sound, propext | `dd7c419e2d20a5af4d821f225d14bc6e278f739cbaff2a5dbf88d8e2efdd4774` | `4c9ac409f9c4ca0cbba59a2e3cb488a5502ce2746a6b205ef3fb78629aeaeb99` (81) |
| `leanReading_fToNatImp` | R0 reading | Classical.choice, Quot.sound, propext | `a3d7e95f9e66306fe88fc1ba5b52043ccd1e9dbcf5874c5492f891dbdd486ba9` | `00f07990249266ab979f587eb990acb39a26446c3b1aa8afa5eeb3f131866c71` (81) |
| `leanReading_fToNatNeg` | R0 reading | Classical.choice, Quot.sound, propext | `9fe909a299a81f1a21305e85caee82ba7a59d61e1ef9fa52259a5dbd01a690b1` | `ce5e5a66b6d1a327faa16f776c8fe296af60d2d458e2761b698316c529a1ae4d` (79) |
| `leanReading_fTrivOr` | R0 reading | Classical.choice, Quot.sound, propext | `7b795bcb69275edd87fa6d078f40c49886ee5e6ca5bea4cdf2e38b92683b4783` | `6c61719ead38b77bbddd6c31a49f41e5c9a7972c8e663d4f3bfce90c7fb082f9` (82) |
| `leanReading_fTruncSubCancel01` | R0 reading | Classical.choice, Quot.sound, propext | `0cb6a491a9e18910a24a96794ce77e8619c95aaac806d21f5e29888d5a52d48b` | `368bc3637ffc184352c036348f28d618d658fe92857509e1251e82f7f64033b2` (79) |
| `leanReading_fTruncSubLe01` | R0 reading | Classical.choice, Quot.sound, propext | `6f2c44117335a1d33f88ff99172dd94368261b85d2e6c8e60c1732c61b05d02b` | `3431eacaa87b300eb5314acb7095f801a2c216d6fa4d112ee7ef38e316842b0d` (79) |
| `leanReading_fUnboundedCancel` | R0 reading | Classical.choice, Quot.sound, propext | `54d1dee27afd27d8e95acc0c7037086bb47900bfca61d9b95167ddece24a6dd7` | `ecebbce96f2d68788a1480a1ff54b59ca02661e997047bd2c6738bd7bd09479f` (82) |
| `leanReading_fZeroSubOne` | R0 reading | Classical.choice, Quot.sound, propext | `a2c6266cfd6672e1fd1c91889c6b542a21c855dea1066ec246c1490c6cc1fab2` | `b0da99f16e6c6e1bc39177399aa15331275987cf454b503ffc22efc97d51091e` (79) |
| `ce_agreement_intValued` | R1 counterexample | Classical.choice, Quot.sound, propext | `50b0694e15b6059bb7aec63e6f6b4dd597f94911f750d9614e9898807d6e96e2` | `974c0c247c96ec6f62e5cc2dfa32adcbea34bcdf6d7836d0bdfb9a707b7b6ec7` (114) |
| `ce_agreement_undefined` | R1 counterexample | Classical.choice, Quot.sound, propext | `bd8b054a0c67effde2b006589fe9acec5a6164e72d1d280a34161bb802db4738` | `7d3b5f9f5246821817dcebdf70ffa44487352516f343fe09f78f24ae1dd9afbf` (115) |
| `ce_intValued_forall_humanFalse_leanTrue` | R1 counterexample; R25 result | Classical.choice, Quot.sound, propext | `ee5a5ec0584df43584f9c493fbcb3c1e68a56cda6f0d01ab59f7ac8911276e1b` | `bf3a0a24b26fcb2e50654ec31c12473c4a38e7fac0ae4216a0da2cfe34fb2c9c` (115) |
| `evalJ_eq_of_hEval_eq_some_partialNat` | R1 result | Classical.choice, Quot.sound, propext | `52a19a0026bb61863e340ad6772ea36b1278bded4744f6349ccf0799bb94e109` | `d15826bdbf009af7184ce668008238482cf7a9ea76f279c2629468a98691ebfd` (111) |
| `kleene_quantifier_tables` | R1 supporting; R18 supporting | Classical.choice, Quot.sound, propext | `faff16c169a0cd0dee4afa1f471f4fcdeca0757b4c7f1ccdb95bb7ac8d1a8e0c` | `da87bb5385605b9bbcf2e0f91fda05336b10d77b9873ee07eaad38e9d7d2dc19` (2) |
| `kleene_tables` | R1 supporting; R18 supporting | propext | `9fc20cfb8b33ed167dfec97868e0a460eeac277a625e48bc44ec04b8d45f258e` | `d594c4d62b0e951da620359ae7d4719601615ebf3102f28f939a04d612bd5419` (16) |
| `no_flip_partialNat` | R1 result | Classical.choice, Quot.sound, propext | `905c7857cb1a5ba4aa49144f76e8b11934e55d23c1a6652902b7a4df1fb3afa9` | `d15826bdbf009af7184ce668008238482cf7a9ea76f279c2629468a98691ebfd` (111) |
| `nv_evalJ_eq_of_hEval_eq_some_partialNat` | R1 non-vacuity | Classical.choice, Quot.sound, propext | `14281b0b2d29ec407ea80901c13d99694d7ef1f922a76f57e231457946d149e8` | `cdafc2583f9c96159b2b9863341fbf1099a91bd0018560cfd3bb4f9ae1d3886b` (90) |
| `nv_hEval_eq_some_false_partialNat` | R1 non-vacuity | Classical.choice, Quot.sound, propext | `446fc5baba2daf387caf804d2bc364d5e81576526eeaa5d5af0f0edd6bc5217d` | `e63fe9d553958c25b40a94eb800c24708598eb2ee5e6e1bd900eb9d8df9d5841` (89) |
| `seq_tables` | R1 supporting; R8 supporting; R17 supporting; R19 supporting | propext | `fc47f2ad4627a8f1d8f0ce2839591987382d074b89e5c2583fdf1259b801638e` | `a0d6051161e4659124709064572a070ce0c5e53a8f10681d4c437efff01c7c19` (14) |
| `ce_zeroSubOne_junkDependent` | R2 counterexample; R2 counterexample | Classical.choice, Quot.sound, propext | `f3a4750dcb8b18b4c107121c7263c1219ca3d63238443298a30432f536686c59` | `7bf859f047128a26dea5053363dba21c6e447e245266781b41e246d1fbfc66e0` (114) |
| `junkIndependent_of_definedEverywhere_partialNat` | R2 result | Classical.choice, Quot.sound, propext | `acb15a7397dfe5da36d0d72caa4af0a9f41a6d4713ce09f27af73820b95986bc` | `324d746fe2917106ed5972b0dacda839bf1ded567080b9a22ec2e5495382840a` (113) |
| `nv_definedEverywhere_partialNat` | R2 non-vacuity; R5 non-vacuity | Classical.choice, Quot.sound, propext | `ef7b98275efd8e2f6b7b59435f04d26a97f696603216d6268a41a09574a2c071` | `de71db64854d5dd4fdfd7fd103b4e41a0525be71b46e3d20d888925e16b3da89` (90) |
| `ce_junkIndependent_leanValid_undefined` | R3 result | Classical.choice, Quot.sound, propext | `6eab92cbdc4e3b71d2cf2924d66360c2672d9829a13c5c01f8527adb3a7a8077` | `a2436adf4b52563fe3d8c8bb1a5070e5dba7184010b4dda8a72d02084e27b217` (118) |
| `ce_junkIndependent_not_definedEverywhere` | R3 result | Classical.choice, Quot.sound, propext | `dabc6d3ea1f70fab0c759afcb0f87dec76d7131e4e4863480ad03b5b76725db3` | `0612726cd1fe04267807a02c8f02a0a85be3d8888077154799f361120c09fe52` (117) |
| `AgreesWhereDefined_neg` | R4 supporting | Classical.choice, Quot.sound, propext | `fa7146d36dccaf6dbdec53407ef810132ccc750c57f61315739e3ec99e5f7181` | `a0bbc6e379cb2a025eed8862d3b1b2bbc5ebb1d6f0938cfe481f40f4d4bc2786` (114) |
| `AgreesWhereDefined_pos` | R4 supporting | Classical.choice, Quot.sound, propext | `1c42a89baffae88ab6468851ddde1d6e6d0cf51bbc7b798f4138bec6e0061c11` | `1352a07c40ad06818dd5c545c2a7bcfbb197171183a294edbfd5e1ec7e89b70f` (116) |
| `agreesWhereDefined_partialNat` | R4 supporting | Classical.choice, Quot.sound, propext | `e880442dfcbb67fc123635c863f258e438f021a7c5369cb01038a27edb0ae809` | `351d4ab5d1b08e605394e168f68ddbdf3e642e58dadab48e7fda4b462bf18c77` (112) |
| `ce_agrees_not_junkIndependent` | R4 result | Classical.choice, Quot.sound, propext | `1ce78d35a70fb1f8130a65c64e0b6fad8a31a2be8eb56226ec76ffd900dd3da4` | `f547575b83c6a4898d1dbd27d2e7775458ed76e1d67e4f7a0a6a0acd1a30fd96` (121) |
| `ce_intValued_definedEverywhere_humanValid_not_leanValid` | R5 counterexample | Classical.choice, Quot.sound, propext | `1582a276dd35b99dfbef10db9338228ebd4b8949fd69ae2e6d08ea0351deb16d` | `6023886808b5fdb8cc14a4d7a797b99ccf7f6b8f7d6cc60579eb31a775069d87` (118) |
| `ce_intValued_humanValid_not_leanValid` | R5 counterexample | Classical.choice, Quot.sound, propext | `6a0ecc4af1af49021be2568da785d7f2e579add5af8d955920d1ddc2b99f64a9` | `b00b07f0bb97fe97df4db2049aa0cb2bc8d7b2988eee7f541717ec53725f3392` (117) |
| `ce_leanValid_not_humanValid` | R5 counterexample | Classical.choice, Quot.sound, propext | `971a40d9c4d523a5bd7f7be328056d650537c4899144945ff0eceec5a20e7aeb` | `0b1feb8b3eb677ce123a0dedf980c35570c37167e2622c80b8e560fa1e0d263c` (116) |
| `ce_not_humanValid_not_leanValid` | R5 counterexample | Classical.choice, Quot.sound, propext | `e484e3c08bbfbb202af81577ec6888b4b032b0dcd122f073945a0551c06a136e` | `b00b07f0bb97fe97df4db2049aa0cb2bc8d7b2988eee7f541717ec53725f3392` (117) |
| `leanValid_iff_humanValid_of_definedEverywhere_partialNat` | R5 result | Classical.choice, Quot.sound, propext | `1c3ceae514e2d01d7ec39cb50efa6c4f416f8a50c7cb91e36b13eec3ba7e4f91` | `b5910d10c0c7aa1582f1c9f6c4934c3a17ec37efd0c65c152b2a0279e6a9074a` (115) |
| `leanValid_of_humanValid_partialNat` | R5 result | Classical.choice, Quot.sound, propext | `1ccc2b3ed6e7d8833bf59e457f45e5780123dd6f67bab9bcd5f07ec8549714d1` | `66f48c2db5e4174d669f940f2943ae7f01f7c99ed0b2e9fe3b59101ce6937f8c` (114) |
| `nv_humanValid_partialNat` | R5 non-vacuity | Classical.choice, Quot.sound, propext | `0ab03c56077194d14c78dcc7e592f24950abf1befd469a24ab19875ec1b79fd5` | `faf9f82c59108b3b9f7aea76310ef909dec57186cf3362aa9f02191e76a5133e` (90) |
| `ce_unguarded_divZero` | R6 counterexample | Classical.choice, Quot.sound, propext | `00f772e862c841bea9b4ccbe2c93e7ec4eb2332706d63cbcb80e65689dbdd314` | `7c6e9329f6f52a951612273cd46f373ffd5d9174d058f644a22ef0f580cf1458` (185) |
| `ce_unguarded_junkDependent` | R6 counterexample | Classical.choice, Quot.sound, propext | `980d16c6f34a11e59653462fc19c580e117d461032adf83d7b318a3ccd3ec6c7` | `817a988ac6a1280def8f6b0bcf8d3ef6fd93d3a2235a643839947f8ea355a38c` (173) |
| `definedEverywhere_of_guarded` | R6 result | Classical.choice, Quot.sound, propext | `e3287c1dc152c00844f906a7afc6a72bc794524b4226fba62bd6560ae65d075e` | `a801fe3ade24f6722e79b440967f0899aa01f3cf542e1b819753f5f7f2ba2f6d` (184) |
| `guarded_accepts_vacuous_guards` | R6 supporting; R7 supporting; R24 supporting | Classical.choice, Quot.sound, propext | `bc6b648f72590e0a822e68c02232c784724b659fd6b0c75d73b8ba88425e9270` | `e037503056f7fa8f8e2a2d6c5e5e15055f57efeb63bd93f1a8342c0f2c4c4da0` (213) |
| `guarded_pos` | R6 non-vacuity | propext | `aed586a658a15dc16648fd3a5d767638d773a0a454dd1dc5d0300e79351de5b2` | `c9a613cd587029629ecf4bfb711bf12f12991969cdb1663bcd122b2d2ff42880` (150) |
| `guarded_rejects_strict_bound` | R6 supporting; R24 supporting | Classical.choice, Quot.sound, propext | `9a5f24137b6179c19758a0e086469d29d90c2354399898f7a16b004f0e2c8db0` | `7ae616acf6d3aaff45953e454d0143cd997ac49e8966f0b7023acaca4c16181d` (176) |
| `hEval_eq_some_evalJ_of_guarded` | R6 result | Classical.choice, Quot.sound, propext | `b632ffb2ab28f8509806abd3c19bf2788fb390fcc99638d00ade1f6cc715579c` | `fa07f9763144a1d7c7109f2c897b9402a897abf6b1e3539f7c5c204524010433` (205) |
| `junkIndependent_of_guarded` | R6 result | Classical.choice, Quot.sound, propext | `6962b07445b0c67945916bf5d3736197d023c69d0bb1000c8b89636231a182da` | `3e73c836c575d17969d5e270b25f268e692f908fffa10f17fba2d3d18680e790` (172) |
| `nv_guarded_subAddCancel` | R6 non-vacuity; R7 non-vacuity | propext | `de190b5cb12b3f5805af31f24062b81dd4c1c21402cf86af1667268eff487c04` | `c86eb78eab8ee2cd37dd531a1b6d60f896c1fa56beae584c8f79c42155c301df` (140) |
| `ce_unguarded_leanValid_not_humanValid` | R7 counterexample | Classical.choice, Quot.sound, propext | `7b9f1babd6eacf17735b0d47f33bcc0043645c40e0669f0e93f4e45d14ae5a5f` | `304eeb53b0d85b170b70fe928b6eff465319d71ea9843a536c078ee49424046c` (210) |
| `leanValid_iff_humanValid_of_guarded` | R7 result | Classical.choice, Quot.sound, propext | `bb2cc9eb6753037b772f19e6be31c43f7f43ad442114aa2f8977bedbdfdd300a` | `027c97fa47a431d5f2cc7176679c9c1a34b04f57f9c30fdc6b822f06298b90fd` (208) |
| `restate_subAddCancel_guarded` | R7 result | Classical.choice, Quot.sound, propext | `59683807d2961bb5efe694f421395912ec8545cc83c2c73ef404c762a1ca11e4` | `e240009266a54d7d46b0045ef972223a96bb3f465705bd9eb24c3578fd72d169` (212) |
| `ce_seq_not_closed` | R8 counterexample; R18 counterexample; R19 result | Classical.choice, Quot.sound, propext | `731409591cb9315e6d4a641c1246f4044a833e85154c0b5c02ea88e4e07381a3` | `930619dabd4232f4bf2a9a7b8b2ed5e840938ff3afb97123a8e74852423aeb75` (96) |
| `definedEverywhere_kleene_guardSecond` | R8 result; R18 non-vacuity | Classical.choice, Quot.sound, propext | `18008c15e27a782fd86ef5c2ae01ccd86a5c5bf753cc0c5804b4455f710cc49b` | `c7f1544affa91575389f114500b9536069dcbad717400b855c1d0d866ece465b` (188) |
| `guarded_incomplete_defined` | R8 result | Classical.choice, Quot.sound, propext | `1ddf999ceefcef84644587f028322ade94193ac96c475d1e5c889720e17cfddc` | `6c81815a4b39ac3140087f393380c9fc384f0d691bef5c1a6d70b56a9205105c` (187) |
| `guarded_incomplete_disjunctive_guards` | R8 result | Classical.choice, Quot.sound, propext | `8e3f8ee33ff05a573eb25e396d66830f020010f1ab3d7a049af73f32d618e193` | `7ae5976d0e70ccfb2ff3c4043170e7961f74c7b6805c48d228ccc8d8bba7074a` (189) |
| `guarded_incomplete_junkIndependent` | R8 result | Classical.choice, Quot.sound, propext | `ee19cffeaa6e572d28d95be7b64279d21fef467c1ed12a352d7b3a41bc95e54f` | `3c6380d44616962c0fc2357e01caeace88fe53cdff10d7906a6093586094b699` (175) |
| `trap_truncSub_addCancel` | R9 result | Classical.choice, Quot.sound, propext | `820637f4058cd9a2931e7407f626baa8d383c31fb0d8bf028b4112f55bc70474` | `53c9c44e055792aa6883bc2b3373d77973f76a624dfa2e8587f5fa9994f2af43` (114) |
| `trap_truncSub_le_self` | R9 result | Classical.choice, Quot.sound, propext | `9446b0b7e5f5fd240d4c82eb010751809331c12f77c742155865e24ae03648a8` | `c75b60d2b1e64c56b636487b54291d310e34cc690a17d0112a47560a9b340f03` (115) |
| `trap_div_mod_zero` | R10 result | Classical.choice, Quot.sound, propext | `e38e6806f777bf5718188a36593465b8e6529343b663d859409c7f43b07471da` | `8c16d554211b1a76fc2827bddcfddf419f03fd3826b037df39742fed86b225cb` (116) |
| `trap_floorDiv_exact` | R11 result | Classical.choice, Quot.sound, propext | `6d325f916fc4448dedc52800be68c054f635c9d75588901826b36fb5ca4ea967` | `c4d0c3e42e7f1e1300556cd64cdff40f49475a18392cc7621a0a0c3d3c84ccd9` (114) |
| `trap_int_rounding` | R12 result | Classical.choice, Quot.sound, propext | `0a91a6e7b460bd99978e86e8cb894218d0be107bcc5d77a5a93b566bae7a901f` | `687b3821d08b6e05ab37721b9111e6998f10a5a59e3e7c2b2a1632e231d598db` (119) |
| `trap_int_rounding_values` | R12 result | none | `26a902db3cedba52991be8d8bbe85b95d88071e8d9bbf63b0ff3bde41fd84f79` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `DivDom_pos` | R13 non-vacuity | propext | `4e9044ec5af11dc1a1919d7b288ef7640a322744ac7b693c9bc441776625f981` | `573b578672a0c004fa907e2a44f1b810c24ee35187a1fc1127a53233d1162312` (1) |
| `ModDom_pos` | R13 non-vacuity | none | `36e73d9fbfbb3f7d7ec1909dd28b07ba9ba1831f65310e5ed6e1bb0f28d89ce9` | `a618198ee0dcaabde3b67ff107c5266621c3dec33f3de3649177564d4884e173` (1) |
| `ce_quotient_conventions_not_dvd` | R13 counterexample | propext | `d42319de995a558b60dae5bde0740cc90d63fa262fafd9de4988a16a347ade69` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ce_remainder_conventions_neg_dividend` | R13 counterexample | none | `34edaf43d80143e5e9c1acc9d4a753b965d9067ee30410c46a8dfda29a87722c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ce_remainder_conventions_neg_divisor` | R13 counterexample | none | `56f9430bfb73505f1929918d8b50c52f1b989b9fc392037a20f3b79a599877e6` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_quotient_conventions_agree_of_dvd` | R13 non-vacuity | propext | `153defd2ca7df34f8f05ef857896086b34c086c9c9b272887d6b4f2a7aebcd15` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_remainder_conventions_agree_of_nonneg` | R13 non-vacuity | none | `0ae65a981dd99d858923c57fe5b7f8b719b1b77cb01d8bbbf8bf7534e187288c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `quotient_conventions_agree_of_dvd` | R13 result | Classical.choice, Quot.sound, propext | `e74f76508c6b89854450cd2f7c9a6972ef35bf94d8461377d32c4450514a442f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `remainder_conventions_agree_of_nonneg` | R13 result | propext | `de5b64f1267067dee085c596f51f6da6410e7fb60d889fc07ce26bb2044dc59f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `rounding_conventions_agree_on_domains` | R13 result | Classical.choice, Quot.sound, propext | `a6f8838cd921b3e25c906b3d1bcf21f68c3af5e3b4a36a37bb77309caf235ef5` | `cb490f603449ef8d8b7fedb9af57ebc4a8e6660c772b89d597fd44fb1c61b20e` (2) |
| `trap_fin_numeral_wraps_before_bound` | R14 result | propext | `4e367b4f49e820704e46b87ef66470aa5b83a694f033fbbf6c819670c141fdbf` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `trap_fin_wrap` | R14 result | propext | `3f16ec1ce6f1e56c8f2aeafa665f2a6a406fd83115309b8c82be48b0d69c30f4` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `natCast_sub_eq_iff_le` | R15 result | Classical.choice, Quot.sound, propext | `47e0e60dab791c5614c1cc447fff9fddfa22107f4aa280aba713f8d760dfdebd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `trap_cast_placement` | R15 result | Classical.choice, Quot.sound, propext | `0628238bb87990e08ee79161abcc1ab888b890a6a2082a38409c9f4b89b6c18b` | `29e3c11eafed0093b992727cc9ddfd05ab1517b9378a6911fe0b11fdf1b9afa9` (117) |
| `trap_toNat_neg` | R15 result | Classical.choice, Quot.sound, propext | `d81553ccfc7ae92b6f4a76fab1cdf9fc3f69fe0214815641b30f9af654895527` | `b1067c39efd14949906f89cf2567ff2ebbffd5beb8f070e07ba818365db7bcfb` (115) |
| `trap_numeral_typing` | R16 result | Classical.choice, Quot.sound, propext | `c65b7247f93e3913f3f30f52d66c2424ba729e0d6ac91d98d24880b5dfc95ce3` | `b3fa1da4833b7403d5f4eeae48b7265b00c32c71ae5888071e6fb23ee04d0c0c` (115) |
| `ce_guarded_not_closed_under_and_comm` | R17 result | Classical.choice, Quot.sound, propext | `b7be375396a24c3c45708eba3ab0adafec019ff234d4a9785482a367ea4aaaae` | `3fbde878231fb75126dc9e14bc58a273cb0d8cc604c7fffb2569467d4e537b84` (176) |
| `ce_guarded_not_closed_under_contrapose` | R17 result | Classical.choice, Quot.sound, propext | `1c9532ac3f5045d9c918353dd2616c8d94bbdb282b42a17830634a6e8d21b207` | `926668f40c370fd2ec77d809954d057d5c9815eb26eb3b56ed0a4695543934b4` (176) |
| `definedEverywhere_kleene_closed` | R17 positive control; R18 result | Classical.choice, Quot.sound, propext | `9f484821ba5d936368d1cddbe6a081a75c0bbccb42b9fb44a7d3f7f0fc364f3a` | `21fbe31df0ee8a23e5e6ac8164ef110f1192253c38e6b3cfd5b29061c898c927` (89) |
| `hEval_kleene_and_comm` | R18 result | Classical.choice, Quot.sound, propext | `7896e17fdb38675bd993582e82575c8ffcfc5c31300c33762351a098533a9b79` | `46248c6a65c4ba8510cb20e1f2c94191b3eb3f70b865eef7f6b095411137b02e` (88) |
| `hEval_kleene_contrapose` | R18 result | Classical.choice, Quot.sound, propext | `a6669c7352ba079525dd99cb4d76da9448f6dbb4c7b5ad697b94eda50b2abb17` | `46248c6a65c4ba8510cb20e1f2c94191b3eb3f70b865eef7f6b095411137b02e` (88) |
| `ce_seq_and_comm_changes_definedness` | R19 result | Classical.choice, Quot.sound, propext | `123db8f9b0221cc61976df26a82681ec75ecc959181c74b48b493b9c0e67d26d` | `b1501593f93cc5c5d9ffb33c078abbf1d8b52800f24c95d1a3961b51322639dd` (94) |
| `ce_seq_contrapose_changes_definedness` | R19 result | Classical.choice, Quot.sound, propext | `372399bea98bd2299899542a9351349882d57d12dfea4d48191aebbe36070c6d` | `4e343e50dabf49c84a5a7bc08188f00ba02f283994946167f7f9ca1aad0e6e63` (94) |
| `ce_seq_not_closed_toNat` | R19 result | Classical.choice, Quot.sound, propext | `51c53dfc900ec878ca3e696ec564e7dc720aa362afcd7dcb3a7f5edaed427f9c` | `5a60cba20c6555d537d90fd8b35874f9280a1a381ff1568ff0e3a22c4568f839` (94) |
| `seq_defined_intValued` | R19 supporting | Classical.choice, Quot.sound, propext | `e75d25d34983cd1caced8b8747f4d88cbab3bef48e0800ccab33cc396b9a70a1` | `20f2dacc1d07c6fb4eb9f164e7041dce1c19c8e14b4081cee4b0196fb886a35f` (94) |
| `ce_restate_signedDiff_partialNat` | R20 counterexample | Classical.choice, Quot.sound, propext | `2a21db548535a853934d3c93a4bb4519d52d99af13c117acf67527864ad3021d` | `ed72486ffb4b0693180eaa79f9a962cececb7141f0d8726bfc4680d96d4f32e5` (115) |
| `ce_shallow_cast_nested_sub` | R20 supporting | propext | `c130ef8e11b8bfb0ce489b8c1e3c2b1a8e197e50849547f0e176d04399beaacc` | `c5da9d93e9ff789d6ba974afcd915b4983d0a9666bc9c68877229895aaef0404` (70) |
| `restate_signedDiff_cast` | R20 result | Classical.choice, Quot.sound, propext | `3db63cce2d1c4538fa4685702f4d4d0b7b6e2e6fffdef88a1dbc0c9b5d5fe924` | `a1df6b9f8ec40be551d62d66bb8dbbb20ca1cec12f04f771663d8879ebda5d6b` (211) |
| `hEval_dvdDiv` | R21 result | Classical.choice, Quot.sound, propext | `5e438d1c71a6e62d9f8e3f893b85f561da120bd7f897202ee01bc802b152e38b` | `0f6e3dd843cceffe4aec6dc4e326bccaacd214463a37fa9042bd7072a95fb1fe` (91) |
| `humanValid_dvdDiv_dividend_guard` | R21 result | Classical.choice, Quot.sound, propext | `8a58c121f0c9fd2a21b75c94f54bd4ef588ad9ed6198cb3c596ba710f7d88989` | `a7750798f431e7cc796aa3602a23295b56bcd6ee92a792beebb90a11756f9ae7` (213) |
| `restate_dvd_div` | R21 result | Classical.choice, Quot.sound, propext | `7e2eab9a5fe19a8f82433ab4a0b080d9207b96f220362de5ba629651a7911146` | `d9808302095b7403e5abbc199c314d3cad995f9e6a45d23e6b103ca9d9d0beb7` (212) |
| `restate_named_int_division` | R22 result | Classical.choice, Quot.sound, propext | `5e4289d2980d3e8e71a27410bfd839819f4ef1ae00db78cdc2daf4d70b905499` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ce_restate_fin_add_bound` | R23 counterexample | propext | `4efb3f2f39533a375275623c2327910ab7e04a8486602ba1a3e9189a779dad5f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_restate_fin_add_of_lt` | R23 non-vacuity | propext | `35e887a8bfc0fe92365f346db1a31325d419b8e3768c6d754899d35c4b9e378d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `restate_fin_add_of_lt` | R23 result | propext | `1024d72eb3341ebfd9761c65210dca7db654bd83e10727eed377b11c4836b2f5` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ballNat_guardedIn_iff_of_not_mentionsNat` | R24 result | propext | `bc57817b7ea6ed6eb351dbb80e410ed57c8176c003a1c659f8bbb345808ac3c2` | `7a55239cb1bc0d4b87ac5dc9d03ac985c493a81904c7717723ea349fdc96042d` (136) |
| `boundedCancel_guarded_leanValid_humanValid` | R24 result | Classical.choice, Quot.sound, propext | `869b1531c0329157be600052200934d8d2ff4b0af62ef8051d2c8b7742e1a2cb` | `227b65f2e437620ce0892869124b80f63709e43b95c37f5f84219346386099db` (213) |
| `ce_ballNat_bound_mentions_var` | R24 counterexample | Classical.choice, Quot.sound, propext | `adf13252e82c03597ba5b2e933ef2c2fccc70a6d03ce0c723742ec2d3ec4b433` | `cf8b8444daacb9393ea0ef08a9458a30e0786394cba96f6df45f8c380b95eb4a` (186) |
| `ce_unbounded_cancel` | R24 result | Classical.choice, Quot.sound, propext | `430accc6b7ea3cf877e232569ea83ce9fcc0d55226fa240d9c0c5f59c2117c88` | `cbe02f4489b4692899e4e8b9c37fdc8caf3156f68c05819488c9fd262e284523` (211) |
| `nv_ballNat_guardedIn_iff` | R24 non-vacuity | propext | `11f8140a97655c89089c4b8a6ad151810b7cb3ca2c6a4c7d34c534f6e4a0f27c` | `1f38dc862104ad7d6f3370192412f2fe5f7139b3e9f2af4fe6ea6624e3fa7edb` (139) |
| `ce_intValued_forall_humanTrue_leanFalse` | R25 result | Classical.choice, Quot.sound, propext | `e02b23faf4aa00899c2ad9ea57c6405ac55782abca4dc656a222de265a2322fd` | `b2754a9b76cee311ad3f57fa66ae4f173c2c10dc8f3468c5bda3e774354929d2` (117) |
| `ce_partialNat_exists_undefined_leanFalse` | R26 result | Classical.choice, Quot.sound, propext | `eaaa1205a801130ed6f006dce37e86b5355ac17dc7c65159f24dc73ea17ab3c6` | `68f8eec3490dd467a1f44e0cf9e80788ed164c4436fec03112289f9433ddd88f` (116) |
| `ce_partialNat_forall_undefined_leanTrue` | R26 result | Classical.choice, Quot.sound, propext | `2aafebf97d71cc6f225089a73a7ec937a5695057d3b08ebf8740d2ee183a8e07` | `fe9100787a1b81222c2cfd591b5bf9311ff1b67d1934e180793f0aaa0f49894b` (116) |
| `inexact_quotient_undefined_leanTrue` | R26 result | Classical.choice, Quot.sound, propext | `3b6d2bec5c069d074a7131e18af83b5bed3c747119e950d4347120e85b81f786` | `4a39f25465982b1b9f8ea652d03fa04b1467717e438536025a5d20bcabb7505d` (116) |

### Sources

Lean core sources (tag `v4.34.1`; git blob hashes and line numbers as recorded):

- **[L1]** Lean 4 core, leanprover/lean4 tag v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, src/Init/Prelude.lean (blob 66af67237683d3c7f8230bcf473c0871e67749a2): Nat.sub (docstring at line 2111) 'Subtraction of natural numbers, truncated at 0'; Nat.div (docstring lines 2170-2184) 'Division by 0 returns 0 ... sometimes called floor division'; Nat.modCore (docstring lines 2202-2214, definition at line 2216) 'When the divisor is 0, the result is the dividend rather than an error'.
- **[L2]** Lean 4 core, leanprover/lean4 tag v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, src/Init/Data/Int/DivMod/Basic.lean (blob 855635fb1ddc652debd9b4f843ecd546ef94dee9): module comment 'There are three main conventions for integer division, referred here as the E, F, T rounding conventions. All three pairs satisfy the identity x % y + (x / y) * y = x unconditionally, and satisfy x / 0 = 0 and x % 0 = x'; the default / and % instances use Int.ediv and Int.emod (E-rounding, 0 <= emod x y < natAbs y for y != 0); Int.div and Int.mod were removed in December 2024.
- **[L3]** Lean 4 core, leanprover/lean4 tag v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, src/Init/Data/Int/Basic.lean (blob 13eb3c86d79160bb9bda2edd33772d6d4439ce0c): Int.toNat 'Negative numbers are converted to 0'.
- **[L4]** Lean 4 core, leanprover/lean4 tag v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, src/Init/Data/Int/DivMod/Lemmas.lean (blob 99da2d83e13e782fb6ab3304b39321ded95e3737): Int.tdiv_eq_ediv (line 223), Int.fdiv_eq_ediv (line 265), Int.tdiv_eq_ediv_of_dvd (line 323), Int.fdiv_eq_ediv_of_dvd (line 326), Int.fmod_eq_emod_of_nonneg (line 418), Int.fmod_eq_emod (line 421), Int.tmod_eq_emod_of_nonneg (line 431), Int.tmod_eq_emod (line 434).
- **[L5]** Lean 4 core, leanprover/lean4 tag v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, src/Init/Data/Fin/Basic.lean (blob 6fee3ab2eaacf1b76de02ea7f7880f29fbac8294): Fin.add (line 90) 'Addition modulo n'; Fin.sub (line 113) 'Subtraction modulo n'; Fin.ofNat (line 54) 'Returns a modulo n as a Fin n', used by the numeral instance Fin.instOfNat (line 245).
- **[L6]** Lean 4 core, leanprover/lean4 tag v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, src/Init/Data/Int/Lemmas.lean (blob be4123f91d766b8563c965e72e9f96010dfbee61): Int.ofNat_sub (line 346) '((n - m : Nat) : Int) = n - m' under m <= n.
- **[L7]** Lean 4 core, leanprover/lean4 tag v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, src/Init/Prelude.lean (blob 66af67237683d3c7f8230bcf473c0871e67749a2): instance instOfNatNat (lines 1280-1281) carries the attribute @[default_instance 100], so a numeral whose type is not otherwise determined elaborates at Nat.
- **[L8]** Lean 4 core, leanprover/lean4 tag v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, src/Init/Data/Nat/Dvd.lean (blob 996481d2e08458e4484f0b34480376711b7fb5dd): Nat.div_mul_cancel (line 110) 'm / n * n = m' under n | m, with no n != 0 hypothesis.
- **[L9]** Lean 4 core, leanprover/lean4 tag v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, src/Init/Data/Fin/Lemmas.lean (blob 4bda280b83da6927f2408516b4673669e7f548fe): Fin.val_add (line 361) '(a + b).val = (a.val + b.val) % n'.

Literature and documentation:

- **[P1]** Lean Prover Community, 'Common Lean Pitfalls', https://leanprover-community.github.io/extras/pitfalls.html: sections 'Division by 0' ('In Lean, n / 0 = 0'), 'Natural number subtraction' ('Subtraction of natural numbers truncates at 0') and 'Wrapping arithmetic in Fin' ('Arithmetic in Fin wraps around if it overflows or underflows').
- **[P2]** David Gries and Fred B. Schneider, 'Avoiding the undefined by underspecification', in J. van Leeuwen (ed.), Computer Science Today: Recent Trends and Developments, LNCS 1000, Springer, 1995, pp. 366-373, DOI 10.1007/BFb0015254. Section 4: all operations are total but the value of an expression need not be uniquely specified; theorems about an underspecified operation carry an antecedent describing where it is uniquely specified (example: y != 0 => y/y = 1); a formula is valid if it evaluates to true for every combination of values that can be assigned to its underspecified terms. Section 2 notes that under a strict extension with an undefined value, excluded middle fails.
- **[P3]** S. C. Kleene, Introduction to Metamathematics, North-Holland / P. Noordhoff / Van Nostrand, 1952, section 64 ('The 3-valued logic'): the strong three-valued connectives with truth values t, f, u, under which conjunction is the minimum and disjunction the maximum in the order f < u < t (as summarized in the Stanford Encyclopedia of Philosophy entry 'Many-Valued Logic', https://plato.stanford.edu/entries/logic-manyvalued/). These are the connectives of Conn.kleene (kleene_tables); the quantifiers tvAll and tvEx are the corresponding strong quantifiers (kleene_quantifier_tables).
- **[P4]** John McCarthy, 'A basis for a mathematical theory of computation', in P. Braffort and D. Hirschberg (eds.), Computer Programming and Formal Systems, Studies in Logic and the Foundations of Mathematics, North-Holland, 1963, pp. 33-70, DOI 10.1016/S0049-237X(08)72018-4. Defines p AND q = (p -> q, T -> F) and p OR q = (p -> T, T -> q) by conditional expressions, and remarks that if p is false and q is undefined then p AND q is false and q AND p is undefined. These are the sequential connectives of Conn.seq (seq_tables).
- **[P5]** Adam Darvas, Farhad Mehta and Arsenii Rudich, 'Efficient Well-Definedness Checking', in Automated Reasoning: 4th International Joint Conference, IJCAR 2008, LNCS 5195, Springer, 2008, pp. 100-115, DOI 10.1007/978-3-540-71070-7_8. Requiring well-definedness conditions to be proven 'allows us to reason in a two-valued logic even if the underlying specification language has a three-valued semantics' (abstract); the paper contrasts a well-definedness operator D corresponding to strong Kleene connectives with a simpler, stricter left-to-right operator L, with L(phi1 AND phi2) = L(phi1) AND (phi1 => L(phi2)).
- **[P6]** Matthias Schmalz, Formalizing the Logic of Event-B: Partial Functions, Definitional Extensions, and Automated Theorem Proving, doctoral thesis, Diss. ETH No. 20516, ETH Zurich, 2012, DOI 10.3929/ethz-a-007577749: gives Event-B's logic, including its well-definedness operator D, a semantics by embedding into higher-order logic, discusses Kleene semantics for partial formulas, and checks a substantial part of the soundness proof in Isabelle/HOL.
- **[P7]** John Rushby, Sam Owre and Natarajan Shankar, 'Subtypes for Specifications: Predicate Subtyping in PVS', IEEE Transactions on Software Engineering 24(9):709-720, 1998, DOI 10.1109/32.713327: predicate subtyping, with type-checking proof obligations called Type Correctness Conditions (TCCs).
- **[P8]** Matt Kaufmann and J Strother Moore, 'An Industrial Strength Theorem Prover for a Logic Based on Common Lisp', IEEE Transactions on Software Engineering 23(4):203-213, 1997, DOI 10.1109/32.588534: total functions in the logic (Section 3.4), with guards that are extra-logical (not involved in the axioms defining functions; Sections 3.4 and 3.6) and connect the logic to execution in Common Lisp (Section 4).
- **[P9]** Kevin Buzzard, 'Division by zero in type theory: a FAQ', Xena project blog, July 5, 2020, https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/ (Lean's / is total with 1/0 = 0; natural subtraction x - y is 0 when x < y; idiomatic Lean lets functions accept 'garbage inputs' and puts the side conditions as hypotheses of the theorems).
- **[P10]** Lawrence C. Paulson, 'Undefined values, or what do we get when we divide by zero?', Machine Logic blog, 1 December 2021, https://lawrencecpaulson.github.io/2021/12/01/Undefined.html: surveys totalization ('we go ahead and define x/0=0') and mentions proposals to use a three-valued logic.
- **[P11]** Jan A. Bergstra and John V. Tucker, 'The Rational Numbers as an Abstract Data Type', Journal of the ACM 54(2), Article 7, 2007, DOI 10.1145/1219092.1219095: an equational specification of the rationals with a total inverse in which 0^-1 = 0.
- **[P12]** Raymond T. Boute, 'The Euclidean definition of the functions div and mod', ACM Transactions on Programming Languages and Systems 14(2):127-144, 1992, DOI 10.1145/128861.128862 (Euclidean conditions as summarized in Leijen 2001; they presuppose a nonzero divisor).
- **[P13]** Daan Leijen, 'Division and Modulus for Computer Scientists', note, University of Utrecht, December 3, 2001, https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/, Section 1.2 (Euclidean division: q in Z, D = d*q + r, 0 <= r < |d|, conditions that presuppose d != 0, attributed to Boute 1992); Section 1 reviews truncated and floored division. The note is unnumbered: neither the note nor its landing page gives a DOI, arXiv identifier or report number (the landing page lists it as a short note dated July 2003 and links the PDF https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/divmodnote-letter.pdf, whose title page is dated December 3, 2001). With no immutable identifier available, `REPORT.json` records the landing-page URL, the PDF URL and the printed date as the strongest available identity; no content hash of the PDF is recorded.

Two sources are cited through secondary material, as their entries state: Kleene (1952, section 64) through the Stanford Encyclopedia of Philosophy summary and the section reference in Schmalz (2012), and Boute (1992) through Leijen (2001). They are not listed as subjects in `REPORT.json`, which lists the toolchain and the sources examined directly.

**Observation date.** All kernel checks, hashes and source lookups recorded here were made or revalidated on the `observed_at` date of `REPORT.json`.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is installed; the project has no dependencies.

**Primary check.** From the package directory run:

```bash
python3 support/revalidate.py .
```

The script copies `lean/` to a temporary directory (the package is not modified) and then:

1. runs `lake build`;
2. scans every Lean source for `sorry`, `admit`, `native_decide` and `axiom` declarations;
3. runs a small Lean audit program (embedded in the script) that computes, with Lean's `collectAxioms`, the axioms of every declaration of the `ToyJunk` library and fails if any declaration uses an axiom other than `propext`, `Classical.choice` and `Quot.sound`;
4. recomputes, for every Lean name referenced by `results.json` and every name recorded in `audit/statements.json`, the statement hash (SHA-256 of the Lean `repr` of the declaration's type) and the closure hash (SHA-256 of the newline-joined, sorted lines `name : repr(type)`, followed by ` := repr(value)` for non-theorems, of every `ToyJunk` constant reachable from the statement), and compares both, and the closure size, with `audit/statements.json`.

It prints `REVALIDATED` and exits with status 0 exactly when all four checks pass. The script's docstring states what is hashed.

**Manual build and spot audit.** The same facts can be checked by hand. Build the library:

```bash
cd lean
lake build
```

Then print the axioms of selected theorems (any declaration name of the library can be added):

```bash
cd lean
cat > /tmp/ToyJunkAxioms.lean <<'EOF'
import ToyJunk
#print axioms Toy.Junk.evalJ_eq_of_hEval_eq_some_partialNat
#print axioms Toy.Junk.hEval_eq_some_evalJ_of_guarded
#print axioms Toy.Junk.leanValid_iff_humanValid_of_guarded
#print axioms Toy.Junk.trap_numeral_typing
#print axioms Toy.Junk.restate_named_int_division
EOF
lake env lean /tmp/ToyJunkAxioms.lean
```

Each line of output must list a subset of `propext`, `Classical.choice`, `Quot.sound`.

**Narrow checks after a change.** If the Lean toolchain changes, the results most likely to be affected are the Lean-core facts (R9 to R16, R22, R23) and `evalT_leanJ` (R0), because they depend on the definitions of `Nat.sub`, `Nat.div`, `Nat.mod`, `Int.ediv`, `Int.emod`, `Int.tdiv`, `Int.fdiv`, `Int.toNat`, `Fin.add`, `Fin.sub`, `Fin.ofNat` and the default numeral instance; rebuilding with the new toolchain and rerunning `python3 support/revalidate.py .` re-checks all of them. A changed statement or closure hash means that a statement or a definition it depends on changed, and the corresponding card must be re-read against the new statement. A passing revalidation establishes the kernel facts above; it does not by itself re-establish the modeling-bridge lines, which rest on the reasoning stated in each card.
