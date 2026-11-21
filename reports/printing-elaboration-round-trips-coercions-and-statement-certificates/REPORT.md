# Printing, elaboration round trips, coercions and statement certificates

## Summary

This package is a Lean 4 formalization (core Lean, no Mathlib) of what a printed statement certifies about the term a proof assistant checked. It models, as a toy, a typed term language with numerals, truncated `Nat` subtraction, a `Nat → Int` coercion and implicit type arguments; an untyped surface syntax ("text", a parsed syntax tree rather than a character string); a family of deterministic elaborators that differ in their numeral default and in where they insert coercions; printers that show or elide each kind of annotation; and a declarative elaboration relation. It proves that default-printed text can denote statements of different truth, that a textual round trip (elaborate, print, compare) does not certify the term, that the term round trip under a given reader does, how far annotation-minimizing printers and full annotation carry that certificate across readers, and when the choice of coercion placement is semantically irrelevant. Every result is a kernel-checked theorem about the toy model. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Lean 4's pretty-printer and elaborator, Mathlib, Isabelle/HOL, HOL Zero or any other system. Separate `derived (modeling bridge)` paragraphs in Findings relate some cards to build-checked observations of Lean v4.34.1.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

What each result does *not* show is listed under **Boundaries**, first subsection (non-claims), followed by escape hatches, results that are known not to apply, and cases not examined. Code-formatted identifiers of the package (namespace `Toy.Render`) are Lean declarations quoted verbatim in this report (definitions and definition examples under **Applicability**, results with their tightness counterexamples and non-vacuity witnesses in **Findings**, results cited in non-claims at the end of **Boundaries**); card ids are the headings of the cards under **Findings**; names such as `Nat`, `Int` and `pp.numericTypes` are Lean's own. Throughout, `-` on `Nat` is truncated subtraction (`2 - 3 = 0` at `Nat`).

Results (plain-language claims, as recorded in `results.json`):

1. **`default_printer_collision_changes_truth`** (impossibility, T1). In the running signature S₀, the default printer (which elides numeral types, type arguments and coercions) maps the distinct closed terms (2 : Nat) - 3 = 0 and (2 : Int) - 3 = 0 to the same text 2 - 3 = 0; the first is valid and the second is not; and for every reader R (any function from a signature and a text to an optional term), R does not return (2 : Nat) - 3 = 0 on the default text of the first, or R does not return (2 : Int) - 3 = 0 on the default text of the second.
2. **`explicit_printer_section_law`** (theorem, T1). For every elaborator configuration cfg of the family (any numeral default, including the degenerate default Prop, and either coercion-placement rule), every signature S and every term t: if t is well typed in S, then cfg reads the explicit text ppExplicit t (every type argument, numeral ascription and coercion printed) back as exactly t.
3. **`default_faithful_iff_default_recoverable`** (characterization, T1). For every signature S and every term t (well typed or not): the system elaborator cfg0 (numeral default Nat, coercions at the operator) reads the default text of t back as t if and only if t passes the structural check DefaultRecoverable S t (the recursion defRec, quoted verbatim under Applicability; clause-by-clause description in this card).
4. **`textual_round_trip_does_not_certify_term`** (counterexample, T1). In S₀, the term tTrunc = ↑(a - b) = ↑a - ↑b at Int, with a b : Nat, has default text a - b = a - b; the system elaborator reads that text as the different term a - b = a - b at Nat, whose default text is again a - b = a - b; the re-read term is valid, while tTrunc is not valid and is false at a = 0, b = 1.
5. **`textual_idempotence_necessary_for_faithfulness`** (theorem, T0). For every configuration cfg, signature S, printer p : Tm → Stx and term t: if cfg reads p t back as t, then printing the re-read term with p gives back the text p t.
6. **`annotation_free_text_survives_textual_round_trip`** (theorem, T1). For every configuration cfg, signature S, text s and term t': if s contains no annotation tokens (s.annCount = 0) and cfg elaborates s to t', then the default printing of t' is s.
7. **`term_round_trip_determines_reading`** (theorem, T0). For every configuration cfg, signature S, text r and term t: if cfg reads r as t (Faithful cfg S r t), then every term t' that cfg returns on r equals t and has the same denotation as t in every environment.
8. **`greedy_printer_faithful`** (theorem, T1). For every configuration cfg, signature S and term t: if t is well typed in S, then cfg reads the deletion-greedy rendering ppMin cfg S t back as t.
9. **`greedy_printer_locally_minimal`** (theorem, T1). For every configuration cfg, signature S, term t and annotation position q: if t is well typed in S and q is kept by minMask cfg S t, then cfg reads ppMin cfg S t back as t, and cfg does not read back as t the rendering that shows the kept positions except q.
10. **`greedy_printer_eq_default_when_default_faithful`** (theorem, T1). For every configuration cfg, signature S and term t: if cfg reads the default text of t back as t, then ppMin cfg S t is the default text of t.
11. **`elaborator_family_agrees_on_fully_annotated_text`** (theorem, T1). For every configuration cfg (any numeral default, including Prop, and either coercion rule), signature S and text s: if s is fully annotated (every +, -, = carries a type argument and every numeral is directly ascribed), then cfg and the system elaborator return the same result on s.
12. **`explicit_text_faithful_for_every_agreeing_reader`** (theorem, T0). For every signature S, term t and reader e' (any function from a signature and a text to an optional term): if t is well typed in S and, in every signature, e' returns the same result as the system elaborator on every fully annotated text, then e' reads the explicit text of t as t.
13. **`faithfulness_is_reader_relative`** (counterexample, T1). In S₀: the default text a - b = z of tZ = ↑(a - b) = z is faithful for the system elaborator and equals ppMin cfg0 S₀ tZ, but the leaf-coercion reader reads it as ↑a - ↑b = z, which differs in truth from tZ at a = 0, b = 1, z = 0; the default text 2 - 3 = 0 of (2 : Nat) - 3 = 0 is faithful for the system elaborator and equals ppMin cfg0 of that term, but the Int-numeral reader reads it as (2 : Int) - 3 = 0, which is not valid while (2 : Nat) - 3 = 0 is; and the leaf-coercion and Int-numeral readers read the respective explicit texts back as the original terms.
14. **`correct_annotations_monotone`** (theorem, T1). For every configuration cfg, signature S, term t and masks m, m' (functions from a position and an annotation kind to Bool): if every position-kind pair selected by m is selected by m', and cfg reads back as t the rendering of t that shows the annotations selected by m, then cfg reads back as t the rendering of t that shows the annotations selected by m'.
15. **`wrong_type_annotation_changes_term`** (counterexample, T1). In S₀: adding the type argument Int to the - of the faithful default text a - b = z of tZ = ↑(a - b) = z gives a text with the same annotation-erased form, which the system elaborator reads without error as the well-typed ↑a - ↑b = z, a term different from tZ that differs from it in truth at a = 0, b = 1, z = 0.
16. **`equal_delta_normal_forms_equal_evaluation`** (theorem, T0). For every signature S and terms t₁, t₂: if t₁ and t₂ have the same δ-normal form in S (every definition of S unfolded), then they evaluate to the same value in every environment.
17. **`delta_check_incomplete`** (counterexample, T0). In S₀ (P := a = b, Q := z = 0, PQ := P ∧ Q): the system elaborator reads the unfolded, conjunct-swapped rendering z = 0 ∧ a = b as a term whose δ-normal form differs from that of PQ, and that term and PQ evaluate identically in every environment.
18. **`deterministic_elaborators_sound_for_declarative_elaboration`** (theorem, T1). For every configuration cfg, signature S, optional expected type exp, text s, term t and type τ: if elabE cfg S exp s returns (t, τ), then t is a declarative elaboration of s at τ (Elabs S s τ t, which allows a Nat → Int coercion at any node) and t has type τ.
19. **`coherence_when_every_subtraction_annotated`** (theorem, T1). For every signature S, text s, type τ and terms t₁, t₂: if every subtraction in s carries an explicit type argument (s.subAnnotated) and t₁ and t₂ are both declarative elaborations of s at τ, then t₁ and t₂ evaluate identically in every environment.
20. **`coherence_without_subtraction`** (theorem, T1). For every signature S, text s, type τ and terms t₁, t₂: if s contains no subtraction and t₁ and t₂ are both declarative elaborations of s at τ, then t₁ and t₂ evaluate identically in every environment, wherever their coercions were inserted.
21. **`coherence_on_fully_annotated_syntax`** (theorem, T1). For every signature S, text s, type τ and terms t₁, t₂: if s is fully annotated (subtraction allowed) and t₁ and t₂ are both declarative elaborations of s at τ, then t₁ and t₂ evaluate identically in every environment.
22. **`default_text_incoherent`** (counterexample, T1). In S₀: the default text a - b = z has two declarative elaborations, ↑(a - b) = z (returned by the system elaborator) and ↑a - ↑b = z (returned by the leaf-coercion reader), which differ in truth at a = 0, b = 1, z = 0.

## Applicability

**Model fidelity.** All definitions are toy models written for this package (Lean namespace `Toy.Render`); none is a production definition of an existing system. The model is meant to capture the shape of the gap between a kernel term and its printed text in a proof assistant whose printer can elide coercions, implicit type arguments and numeral types, and whose elaborator fills them back in by numeral defaults, expected types and coercion insertion. The real systems in view are interactive theorem provers with such printers and elaborators, in particular Lean 4 (its delaborator options `pp.numericTypes`, `pp.coercions`, `pp.explicit` and `pp.analyze`, and its `binop%` elaborator), and the printing and parsing discipline discussed for HOL-family provers in the prior art.

**Known gaps.** Text is a parsed syntax tree (`Stx`), not a character string: lexing, operator precedence, parentheses, whitespace, binder syntax, name resolution and shadowing are not modeled. There is one coercion (`Nat → Int`), three types, the operators `+`, `-` (with truncated subtraction at `Nat`), `=`, `↔`, `∧`, and named definitions without parameters; there are no binders inside statements, no polymorphism, no unification, no type classes, no universe levels and no proof terms. The typing context of a statement's variables is assumed to be shared exactly by writer and reader. Elaborators are a fixed finite family (`ElabCfg`: numeral default and coercion-placement rule), plus arbitrary functions (`Reader`) where a result quantifies over all readers. The printers and the deletion-greedy printer `ppMin` are not models of Lean's delaborator or of its `pp.analyze` heuristic.

**Model–system relation: none proved.** These are statements about the toy model; they neither establish nor refute the corresponding claims about Lean 4's pretty-printer and elaborator (at v4.34.1 or any other version), Mathlib, Isabelle/HOL, HOL Zero or any other system. Some cards carry a separate `derived (modeling bridge)` paragraph relating them to build-checked observations of Lean v4.34.1 (quoted at the end of this section); those observations concern the named inputs and options and are not theorems about Lean.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library and `Std`, with no Mathlib and no other Lake dependency. The library `Toy` lives in `lean/` (modules `Toy.Render.Defs`, `Lemmas`, `Statements`, `Examples`, `Counterexamples`, `Witnesses`, `Remarks`, `LeanObservations`).

**Subjects.** `REPORT.json` lists the Lean toolchain (which checks every proof and whose printer and elaborator are observed in `LeanObservations.lean`), the Mathlib revision whose `linter.ppRoundtrip` source is cited as a contrast, and the papers and formal developments cited as prior art. The papers and Mathlib are prior art; none of them is formalized here, and Mathlib is not a dependency.

### Setting (prose)

*Prose summary (not a Lean term); the definitions are quoted verbatim below.* Types `Ty ::= nat | int | prop` (`nat` and `int` are numeric). Church-style terms `Tm ::= var x τ | lit τ n | add τ a b | sub τ a b | eq τ a b | iff a b | and a b | coe a | const c`, where `sub nat` is truncated subtraction and `coe` is the coercion `Nat → Int`. Untyped syntax `Stx ::= var x | num n | add oτ a b | sub oτ a b | eq oτ a b | iff a b | and a b | asc e τ | coe e | const c`, where `oτ : Option Ty` is an optional explicit type argument and `asc e τ` is the ascription `(e : τ)`. A signature `S : Sig` gives the variables' types and a telescope of definitions. `tyOf` is syntax-directed typing and `WellTyped S t := ∃ τ, tyOf S t = some τ`. Semantics is Boolean-valued: `eval S ρ t` evaluates `t` in the environment `ρ`, `Denote S t ρ` says the value is `true`, and `Valid S t := ∀ ρ, Denote S t ρ`. `deltaNF S t` unfolds every definition of `S`.

*Elaborators (prose).* `ElabCfg` has two fields, `numDefault : Ty` and `rule : CoeRule` (`atOperator` or `atLeaves`). Because `numDefault` ranges over all of `Ty`, quantifying over every `ElabCfg` includes degenerate configurations with numeral default `prop`, under which an unconstrained numeral does not elaborate. `cfg0 = (nat, atOperator)` is the configuration of the system elaborator `elabSys = elabWith cfg0`; `cfgIntNumerals = (int, atOperator)`; `cfgLeaves = (nat, atLeaves)`. `elabE cfg S exp s` elaborates `s` against an optional expected type `exp`: an unconstrained numeral takes the numeric expected type, else `numDefault`; an unannotated `+` or `-` takes `opType cfg (joinH (hint S a) (hint S b)) exp` (under `atOperator`: the join of the operand hints if it is not `none`, else the numeric expected type, else `numDefault`; under `atLeaves`: the join of the operand hints and the numeric expected type, else `numDefault`); an unannotated `=` takes the join of its operand hints, else `numDefault`; every result passes through `coerceTo exp`, which inserts `coe` where a `Nat` result meets an expected `Int` and fails on any other mismatch. `elabWith cfg S s` runs `elabE` with no expected type. `Faithful cfg S r t` says `elabWith cfg S r = some t` (the term round trip).

*Printers (prose).* `ppMask m [] t` prints `t`, showing the annotation of kind `k` (`typeArg`, `numType` or `coercion`) at position `p` exactly when `m p k = true`; an elided coercion disappears from the text. `ppDefault` shows no annotation, `ppExplicit` shows every annotation, and `ppNumericTypes` and `ppCoercions` show one kind each. `annPos [] t` lists the annotation positions of `t` in pre-order. `minMask cfg S t` starts from all positions and, visiting them in pre-order, drops each position whose removal keeps `faithfulB cfg S (ppMask …) t` true; `ppMin cfg S t` prints the kept positions. `Stx.annCount` counts annotation tokens; `Stx.fullyAnnotated`, `Stx.subFree` and `Stx.subAnnotated` are the syntax classes used by the agreement and coherence results. `Elabs S s τ t` is the declarative elaboration relation, which allows a coercion at any node.

### Definitions (verbatim)

The whole of `Toy/Render/Defs.lean` after its module header, section by section, verbatim (doc comments, derived instances and `Decidable` instances included). The first line of each block gives the file and line range within the package.

**Types**

```lean
-- lean/Toy/Render/Defs.lean:21-55
/-! ## Types -/

/-- Types of the toy language: natural numbers, integers, propositions. -/
inductive Ty where
  | nat
  | int
  | prop
  deriving DecidableEq, Repr

/-- Numeric types: those at which numerals, `+`, `-` and `=` may be used. -/
def Ty.isNum : Ty → Bool
  | .nat => true
  | .int => true
  | .prop => false

/-- The "maximal type" of two operand types: `Nat ≤ Int`. Any combination
involving `Prop` yields `Prop` (which then fails to elaborate as an arithmetic
type). -/
def Ty.max : Ty → Ty → Ty
  | .nat, .nat => .nat
  | .nat, .int => .int
  | .int, .nat => .int
  | .int, .int => .int
  | _, _ => .prop

/-- Join of optional type hints; `none` means "unconstrained" (a bare numeral). -/
def joinH : Option Ty → Option Ty → Option Ty
  | none, h => h
  | some a, none => some a
  | some a, some b => some (a.max b)

/-- Keep an expected type only if it is numeric. -/
def numOnly : Option Ty → Option Ty
  | some τ => if τ.isNum then some τ else none
  | none => none
```

**Terms, syntax, signatures**

```lean
-- lean/Toy/Render/Defs.lean:57-130
/-! ## Terms, syntax, signatures -/

/-- Kernel-level typed terms (Church style: every node carries the type arguments
that a real kernel term would carry).
* `var x τ`: a context variable, annotated with its type;
* `lit τ n`: the numeral `@OfNat.ofNat τ n`;
* `add τ a b`, `sub τ a b`: `@HAdd.hAdd τ τ τ`, `@HSub.hSub τ τ τ`; `sub` at `Nat`
  truncates at `0`;
* `eq τ a b`: `@Eq τ a b`;
* `iff`, `and`: the propositional connectives;
* `coe a`: the coercion `↑ : Nat → Int`;
* `const c`: a reference to the named definition (abbreviation) `c`. -/
inductive Tm where
  | var (x : Nat) (τ : Ty)
  | lit (τ : Ty) (n : Nat)
  | add (τ : Ty) (a b : Tm)
  | sub (τ : Ty) (a b : Tm)
  | eq (τ : Ty) (a b : Tm)
  | iff (a b : Tm)
  | and (a b : Tm)
  | coe (a : Tm)
  | const (c : Nat)
  deriving DecidableEq, Repr

/-- Untyped surface syntax, as a reader sees it, represented as a parsed abstract
syntax tree (not as a character string: there is no lexing, precedence,
parenthesization, whitespace, binder syntax or shadowing).
* `add (some τ) a b` is the explicit form `@add τ a b`; `add none a b` is `a + b`;
* `asc e τ` is the type ascription `(e : τ)`;
* `coe e` is the explicit coercion `↑e`. -/
inductive Stx where
  | var (x : Nat)
  | num (n : Nat)
  | add (ty : Option Ty) (a b : Stx)
  | sub (ty : Option Ty) (a b : Stx)
  | eq (ty : Option Ty) (a b : Stx)
  | iff (a b : Stx)
  | and (a b : Stx)
  | asc (e : Stx) (τ : Ty)
  | coe (e : Stx)
  | const (c : Nat)
  deriving DecidableEq, Repr

/-- A named definition (abbreviation) with its declared type and body. -/
structure Def where
  name : Nat
  ty : Ty
  body : Tm
  deriving DecidableEq, Repr

/-- A signature: the typing context of the statement's variables (the printed
binders, assumed to be shared exactly by writer and reader) and a telescope of
definitions. In `defs`, the first entry with a given name is the one that counts,
and an entry's body is interpreted with respect to the entries *after* it. -/
structure Sig where
  ctx : List (Nat × Ty)
  defs : List Def
  deriving DecidableEq, Repr

/-- Look up a variable's type in a context (first binding wins). -/
def ctxLookup : List (Nat × Ty) → Nat → Option Ty
  | [], _ => none
  | (y, τ) :: Γ, x => if y = x then some τ else ctxLookup Γ x

/-- Look up a definition by name (first entry wins). -/
def lookupDef : List Def → Nat → Option Def
  | [], _ => none
  | d :: D, c => if d.name = c then some d else lookupDef D c

/-- The type of a variable in the signature's context. -/
def Sig.varTy (S : Sig) (x : Nat) : Option Ty := ctxLookup S.ctx x

/-- The declared type of a named definition. -/
def Sig.constTy (S : Sig) (c : Nat) : Option Ty := (lookupDef S.defs c).map Def.ty
```

**Typing of terms**

```lean
-- lean/Toy/Render/Defs.lean:132-155
/-! ## Typing of terms -/

/-- Syntax-directed type inference for (Church-style) terms. -/
def tyOf (S : Sig) : Tm → Option Ty
  | .var x τ => if S.varTy x = some τ then some τ else none
  | .lit τ _ => if τ.isNum = true then some τ else none
  | .add τ a b =>
    if τ.isNum = true ∧ tyOf S a = some τ ∧ tyOf S b = some τ then some τ else none
  | .sub τ a b =>
    if τ.isNum = true ∧ tyOf S a = some τ ∧ tyOf S b = some τ then some τ else none
  | .eq τ a b =>
    if τ.isNum = true ∧ tyOf S a = some τ ∧ tyOf S b = some τ then some .prop else none
  | .iff a b => if tyOf S a = some .prop ∧ tyOf S b = some .prop then some .prop else none
  | .and a b => if tyOf S a = some .prop ∧ tyOf S b = some .prop then some .prop else none
  | .coe a => if tyOf S a = some .nat then some .int else none
  | .const c => S.constTy c

/-- A term is well typed if type inference succeeds. -/
def WellTyped (S : Sig) (t : Tm) : Prop := ∃ τ, tyOf S t = some τ

instance (S : Sig) (t : Tm) : Decidable (WellTyped S t) :=
  match h : tyOf S t with
  | some τ => isTrue ⟨τ, h⟩
  | none => isFalse (fun ⟨_, h'⟩ => by simp [h] at h')
```

**Semantics**

```lean
-- lean/Toy/Render/Defs.lean:157-242
/-! ## Semantics -/

/-- Semantic values. -/
inductive Val where
  | nat (n : Nat)
  | int (i : Int)
  | prop (b : Bool)
  deriving DecidableEq, Repr

/-- Read a value as a natural number (`0` on a type mismatch). -/
def Val.toNat : Val → Nat
  | .nat n => n
  | _ => 0

/-- Read a value as an integer (`0` on a type mismatch). -/
def Val.toInt : Val → Int
  | .int i => i
  | _ => 0

/-- Read a value as a truth value (`false` on a type mismatch). -/
def Val.toBool : Val → Bool
  | .prop b => b
  | _ => false

/-- An environment: values for the statement's variables, by type. -/
structure Env where
  nat : Nat → Nat
  int : Nat → Int
  prop : Nat → Bool

/-- Evaluation, following the type annotations in the term, with named
definitions interpreted by `k`. `Nat` subtraction truncates. -/
def evalWith (k : Nat → Val) (ρ : Env) : Tm → Val
  | .var x τ =>
    match τ with
    | .nat => .nat (ρ.nat x)
    | .int => .int (ρ.int x)
    | .prop => .prop (ρ.prop x)
  | .lit τ n =>
    match τ with
    | .nat => .nat n
    | .int => .int (Int.ofNat n)
    | .prop => .prop false
  | .add τ a b =>
    match τ with
    | .nat => .nat ((evalWith k ρ a).toNat + (evalWith k ρ b).toNat)
    | .int => .int ((evalWith k ρ a).toInt + (evalWith k ρ b).toInt)
    | .prop => .prop false
  | .sub τ a b =>
    match τ with
    | .nat => .nat ((evalWith k ρ a).toNat - (evalWith k ρ b).toNat)
    | .int => .int ((evalWith k ρ a).toInt - (evalWith k ρ b).toInt)
    | .prop => .prop false
  | .eq τ a b =>
    match τ with
    | .nat => .prop (decide ((evalWith k ρ a).toNat = (evalWith k ρ b).toNat))
    | .int => .prop (decide ((evalWith k ρ a).toInt = (evalWith k ρ b).toInt))
    | .prop => .prop false
  | .iff a b => .prop ((evalWith k ρ a).toBool == (evalWith k ρ b).toBool)
  | .and a b => .prop ((evalWith k ρ a).toBool && (evalWith k ρ b).toBool)
  | .coe a => .int (Int.ofNat (evalWith k ρ a).toNat)
  | .const c => k c

/-- Value of an undefined name. -/
def undefVal : Val := .prop false

/-- Evaluation against a telescope of definitions (structural on the telescope):
a name resolves to the first entry with that name, whose body is evaluated
against the remaining entries. -/
def evalD : List Def → Env → Tm → Val
  | [], ρ, t => evalWith (fun _ => undefVal) ρ t
  | d :: D, ρ, t =>
    evalWith (fun c => if c = d.name then evalD D ρ d.body else evalD D ρ (.const c)) ρ t

/-- Evaluation in a signature. -/
def eval (S : Sig) (ρ : Env) (t : Tm) : Val := evalD S.defs ρ t

/-- `⟦t⟧ ρ`: the proposition denoted by a (proposition-typed) term. -/
def Denote (S : Sig) (t : Tm) (ρ : Env) : Prop := (eval S ρ t).toBool = true

instance (S : Sig) (t : Tm) (ρ : Env) : Decidable (Denote S t ρ) :=
  inferInstanceAs (Decidable (_ = true))

/-- A statement is valid if it holds in every environment (its free variables are
read as universally quantified, as in a theorem statement with binders). -/
def Valid (S : Sig) (t : Tm) : Prop := ∀ ρ, Denote S t ρ
```

**δ-unfolding**

```lean
-- lean/Toy/Render/Defs.lean:244-264
/-! ## δ-unfolding -/

/-- Replace every occurrence of the name `c` by `b`. -/
def substConst (c : Nat) (b : Tm) : Tm → Tm
  | .var x τ => .var x τ
  | .lit τ n => .lit τ n
  | .add τ x y => .add τ (substConst c b x) (substConst c b y)
  | .sub τ x y => .sub τ (substConst c b x) (substConst c b y)
  | .eq τ x y => .eq τ (substConst c b x) (substConst c b y)
  | .iff x y => .iff (substConst c b x) (substConst c b y)
  | .and x y => .and (substConst c b x) (substConst c b y)
  | .coe x => .coe (substConst c b x)
  | .const c' => if c' = c then b else .const c'

/-- Unfold a telescope of definitions, outermost entry first. -/
def unfoldDefs : List Def → Tm → Tm
  | [], t => t
  | d :: D, t => unfoldDefs D (substConst d.name d.body t)

/-- The δ-normal form of a term: all definitions of the signature unfolded. -/
def deltaNF (S : Sig) (t : Tm) : Tm := unfoldDefs S.defs t
```

**Deterministic elaborators**

```lean
-- lean/Toy/Render/Defs.lean:266-410
/-! ## Deterministic elaborators -/

/-- A reader is any function from a signature and a text to an optional term
(a human or machine that re-reads printed text). -/
abbrev Reader := Sig → Stx → Option Tm

/-- Where an elaborator inserts a `Nat ↝ Int` coercion inside an unannotated
arithmetic operator tree.
* `atOperator`: an operator's type is the maximal type of its operands' hints
  (the expected type is used only when all operands are unconstrained numerals);
  a mismatch with the expected type is repaired by coercing the operator's result.
* `atLeaves`: the expected type also participates in the maximal type, so it is
  pushed down and coercions land on the leaves. -/
inductive CoeRule where
  | atOperator
  | atLeaves
  deriving DecidableEq, Repr

/-- Elaborator configuration: the default type of unconstrained numerals and the
coercion-placement rule. `numDefault` is an arbitrary `Ty`, so statements that
quantify over every `ElabCfg` include the degenerate configurations with
`numDefault = .prop`, under which an unconstrained numeral (and an unannotated
operator or equation whose type would come from the default) fails to elaborate. -/
structure ElabCfg where
  numDefault : Ty
  rule : CoeRule
  deriving DecidableEq, Repr

/-- The system elaborator's configuration: numerals default to `Nat`, coercions at
the operator. -/
def cfg0 : ElabCfg := { numDefault := .nat, rule := .atOperator }

/-- A reader whose unconstrained numerals default to `Int`. -/
def cfgIntNumerals : ElabCfg := { numDefault := .int, rule := .atOperator }

/-- A reader that places coercions at the leaves. -/
def cfgLeaves : ElabCfg := { numDefault := .nat, rule := .atLeaves }

/-- The type a piece of syntax announces without elaborating it ("hint"):
`none` for unconstrained numerals and trees of them. -/
def hint (S : Sig) : Stx → Option Ty
  | .var x => S.varTy x
  | .num _ => none
  | .add oτ a b =>
    match oτ with
    | some τ => some τ
    | none => joinH (hint S a) (hint S b)
  | .sub oτ a b =>
    match oτ with
    | some τ => some τ
    | none => joinH (hint S a) (hint S b)
  | .eq _ _ _ => some .prop
  | .iff _ _ => some .prop
  | .and _ _ => some .prop
  | .asc _ τ => some τ
  | .coe _ => some .int
  | .const c => S.constTy c

/-- The type chosen for an unannotated `+`/`-` node, from the join of its operand
hints `h` and the expected type `exp`. -/
def opType (cfg : ElabCfg) (h exp : Option Ty) : Ty :=
  match cfg.rule with
  | .atOperator =>
    match h with
    | some τ => τ
    | none => (numOnly exp).getD cfg.numDefault
  | .atLeaves => (joinH h (numOnly exp)).getD cfg.numDefault

/-- Repair an elaborated term against the expected type: identity on a match,
insert `↑` on `Nat` where `Int` is expected, fail otherwise. -/
def coerceTo : Option Ty → Tm × Ty → Option (Tm × Ty)
  | none, p => some p
  | some τ, (t, σ) =>
    if σ = τ then some (t, σ)
    else if σ = .nat ∧ τ = .int then some (.coe t, .int)
    else none

/-- Bidirectional elaboration against an optional expected type; returns the term
and its type. Unconstrained numerals get the expected type or the default;
operators get their type from `opType` (or from an explicit type argument);
coercions are inserted by `coerceTo`. -/
def elabE (cfg : ElabCfg) (S : Sig) : Option Ty → Stx → Option (Tm × Ty)
  | exp, .var x =>
    match S.varTy x with
    | some τ => coerceTo exp (.var x τ, τ)
    | none => none
  | exp, .num n =>
    let τ := (numOnly exp).getD cfg.numDefault
    if τ.isNum = true then coerceTo exp (.lit τ n, τ) else none
  | exp, .add oτ a b =>
    let τ := oτ.getD (opType cfg (joinH (hint S a) (hint S b)) exp)
    if τ.isNum = true then
      match elabE cfg S (some τ) a, elabE cfg S (some τ) b with
      | some (a', _), some (b', _) => coerceTo exp (.add τ a' b', τ)
      | _, _ => none
    else none
  | exp, .sub oτ a b =>
    let τ := oτ.getD (opType cfg (joinH (hint S a) (hint S b)) exp)
    if τ.isNum = true then
      match elabE cfg S (some τ) a, elabE cfg S (some τ) b with
      | some (a', _), some (b', _) => coerceTo exp (.sub τ a' b', τ)
      | _, _ => none
    else none
  | exp, .eq oτ a b =>
    let τ := oτ.getD ((joinH (hint S a) (hint S b)).getD cfg.numDefault)
    if τ.isNum = true then
      match elabE cfg S (some τ) a, elabE cfg S (some τ) b with
      | some (a', _), some (b', _) => coerceTo exp (.eq τ a' b', .prop)
      | _, _ => none
    else none
  | exp, .iff a b =>
    match elabE cfg S (some .prop) a, elabE cfg S (some .prop) b with
    | some (a', _), some (b', _) => coerceTo exp (.iff a' b', .prop)
    | _, _ => none
  | exp, .and a b =>
    match elabE cfg S (some .prop) a, elabE cfg S (some .prop) b with
    | some (a', _), some (b', _) => coerceTo exp (.and a' b', .prop)
    | _, _ => none
  | exp, .asc e τ =>
    match elabE cfg S (some τ) e with
    | some (e', _) => coerceTo exp (e', τ)
    | none => none
  | exp, .coe e =>
    match elabE cfg S (some .nat) e with
    | some (e', _) => coerceTo exp (.coe e', .int)
    | none => none
  | exp, .const c =>
    match S.constTy c with
    | some τ => coerceTo exp (.const c, τ)
    | none => none

/-- Top-level elaboration (no expected type) under a configuration. -/
def elabWith (cfg : ElabCfg) (S : Sig) (s : Stx) : Option Tm :=
  (elabE cfg S none s).map Prod.fst

/-- The system elaborator (`elabWith cfg0`). -/
def elabSys : Reader := elabWith cfg0

/-- A rendering `r` is faithful to `t` for the reader `cfg` if `cfg` reads `r` back
as exactly `t` (the term round trip). -/
def Faithful (cfg : ElabCfg) (S : Sig) (r : Stx) (t : Tm) : Prop :=
  elabWith cfg S r = some t

instance (cfg : ElabCfg) (S : Sig) (r : Stx) (t : Tm) : Decidable (Faithful cfg S r t) :=
  inferInstanceAs (Decidable (_ = _))
```

**Printers**

```lean
-- lean/Toy/Render/Defs.lean:412-491
/-! ## Printers -/

/-- Kinds of annotation a printer may show or elide. -/
inductive AnnKind where
  | typeArg
  | numType
  | coercion
  deriving DecidableEq, Repr

/-- A position in a term: the child-index path from the root, stored innermost
index first. -/
abbrev Path := List Nat

/-- Which annotations to print, by position and kind. -/
abbrev Mask := Path → AnnKind → Bool

/-- Print a term, showing exactly the annotations selected by the mask: explicit
type arguments on `+`, `-`, `=`; ascriptions `(n : τ)` on numerals; explicit
coercions `↑`. Elided coercions disappear from the text. -/
def ppMask (m : Mask) : Path → Tm → Stx
  | _, .var x _ => .var x
  | p, .lit τ n => if m p .numType then .asc (.num n) τ else .num n
  | p, .add τ a b =>
    .add (if m p .typeArg then some τ else none) (ppMask m (0 :: p) a) (ppMask m (1 :: p) b)
  | p, .sub τ a b =>
    .sub (if m p .typeArg then some τ else none) (ppMask m (0 :: p) a) (ppMask m (1 :: p) b)
  | p, .eq τ a b =>
    .eq (if m p .typeArg then some τ else none) (ppMask m (0 :: p) a) (ppMask m (1 :: p) b)
  | p, .iff a b => .iff (ppMask m (0 :: p) a) (ppMask m (1 :: p) b)
  | p, .and a b => .and (ppMask m (0 :: p) a) (ppMask m (1 :: p) b)
  | p, .coe a => if m p .coercion then .coe (ppMask m (0 :: p) a) else ppMask m (0 :: p) a
  | _, .const c => .const c

/-- The printer that shows exactly the annotation kinds selected by `shows`. -/
def ppWith (shows : AnnKind → Bool) (t : Tm) : Stx := ppMask (fun _ k => shows k) [] t

/-- The default printer: elides coercions, type arguments and numeral types. -/
def ppDefault (t : Tm) : Stx := ppWith (fun _ => false) t

/-- The explicit printer: prints every type argument, numeral type and coercion. -/
def ppExplicit (t : Tm) : Stx := ppWith (fun _ => true) t

/-- Intermediate printer showing only numeral types. -/
def ppNumericTypes (t : Tm) : Stx := ppWith (fun k => decide (k = .numType)) t

/-- Intermediate printer showing only coercions. -/
def ppCoercions (t : Tm) : Stx := ppWith (fun k => decide (k = .coercion)) t

/-- All annotation positions of a term (in pre-order). -/
def annPos : Path → Tm → List (Path × AnnKind)
  | _, .var _ _ => []
  | p, .lit _ _ => [(p, .numType)]
  | p, .add _ a b => (p, .typeArg) :: (annPos (0 :: p) a ++ annPos (1 :: p) b)
  | p, .sub _ a b => (p, .typeArg) :: (annPos (0 :: p) a ++ annPos (1 :: p) b)
  | p, .eq _ a b => (p, .typeArg) :: (annPos (0 :: p) a ++ annPos (1 :: p) b)
  | p, .iff a b => annPos (0 :: p) a ++ annPos (1 :: p) b
  | p, .and a b => annPos (0 :: p) a ++ annPos (1 :: p) b
  | p, .coe a => (p, .coercion) :: annPos (0 :: p) a
  | _, .const _ => []

/-- The mask selecting exactly the listed positions. -/
def maskOf (M : List (Path × AnnKind)) : Mask := fun p k => decide ((p, k) ∈ M)

/-- Boolean form of the term round-trip check. -/
def faithfulB (cfg : ElabCfg) (S : Sig) (r : Stx) (t : Tm) : Bool :=
  decide (elabWith cfg S r = some t)

/-- Deletion-greedy annotation selection: start from all annotation positions
(the explicit rendering) and, visiting positions in pre-order, drop each one whose
removal keeps the term round trip `faithfulB` intact. The result depends on the
visiting order and is in general not a smallest faithful selection. -/
def minMask (cfg : ElabCfg) (S : Sig) (t : Tm) : List (Path × AnnKind) :=
  (annPos [] t).foldl
    (fun M q => if faithfulB cfg S (ppMask (maskOf (M.erase q)) [] t) t then M.erase q else M)
    (annPos [] t)

/-- The deletion-greedy printer relative to the reader `cfg`: shows the positions
kept by `minMask`. The name abbreviates "locally minimal"; `ppMin` is not a
minimum-size printer. -/
def ppMin (cfg : ElabCfg) (S : Sig) (t : Tm) : Stx := ppMask (maskOf (minMask cfg S t)) [] t
```

**Syntax measures and classes**

```lean
-- lean/Toy/Render/Defs.lean:493-565
/-! ## Syntax measures and classes -/

/-- Number of annotation tokens in a text (explicit type arguments, ascriptions,
explicit coercions): the length overhead over the default text. -/
def Stx.annCount : Stx → Nat
  | .var _ => 0
  | .num _ => 0
  | .add oτ a b => (if oτ.isSome then 1 else 0) + a.annCount + b.annCount
  | .sub oτ a b => (if oτ.isSome then 1 else 0) + a.annCount + b.annCount
  | .eq oτ a b => (if oτ.isSome then 1 else 0) + a.annCount + b.annCount
  | .iff a b => a.annCount + b.annCount
  | .and a b => a.annCount + b.annCount
  | .asc e _ => 1 + e.annCount
  | .coe e => 1 + e.annCount
  | .const _ => 0

/-- Strip every annotation from a text. -/
def Stx.erase : Stx → Stx
  | .var x => .var x
  | .num n => .num n
  | .add _ a b => .add none a.erase b.erase
  | .sub _ a b => .sub none a.erase b.erase
  | .eq _ a b => .eq none a.erase b.erase
  | .iff a b => .iff a.erase b.erase
  | .and a b => .and a.erase b.erase
  | .asc e _ => e.erase
  | .coe e => e.erase
  | .const c => .const c

/-- Fully annotated syntax: every `+`, `-`, `=` carries an explicit type argument
and every numeral is directly ascribed. Coercions may still be implicit; every
configuration of the family reads fully annotated text as the system elaborator
does (`elabWith_eq_elabSys_of_fullyAnnotated`). -/
def Stx.fullyAnnotated : Stx → Bool
  | .var _ => true
  | .num _ => false
  | .add oτ a b => oτ.isSome && a.fullyAnnotated && b.fullyAnnotated
  | .sub oτ a b => oτ.isSome && a.fullyAnnotated && b.fullyAnnotated
  | .eq oτ a b => oτ.isSome && a.fullyAnnotated && b.fullyAnnotated
  | .iff a b => a.fullyAnnotated && b.fullyAnnotated
  | .and a b => a.fullyAnnotated && b.fullyAnnotated
  | .asc (.num _) _ => true
  | .asc e _ => e.fullyAnnotated
  | .coe e => e.fullyAnnotated
  | .const _ => true

/-- Syntax without truncating subtraction `-`. -/
def Stx.subFree : Stx → Bool
  | .var _ => true
  | .num _ => true
  | .add _ a b => a.subFree && b.subFree
  | .sub _ _ _ => false
  | .eq _ a b => a.subFree && b.subFree
  | .iff a b => a.subFree && b.subFree
  | .and a b => a.subFree && b.subFree
  | .asc e _ => e.subFree
  | .coe e => e.subFree
  | .const _ => true

/-- Syntax in which every subtraction `-` carries an explicit type argument (other
annotations may be missing). Both subtraction-free and fully annotated syntax have
this property. -/
def Stx.subAnnotated : Stx → Bool
  | .var _ => true
  | .num _ => true
  | .add _ a b => a.subAnnotated && b.subAnnotated
  | .sub oτ a b => oτ.isSome && a.subAnnotated && b.subAnnotated
  | .eq _ a b => a.subAnnotated && b.subAnnotated
  | .iff a b => a.subAnnotated && b.subAnnotated
  | .and a b => a.subAnnotated && b.subAnnotated
  | .asc e _ => e.subAnnotated
  | .coe e => e.subAnnotated
  | .const _ => true
```

**Default recoverability (the structural side of the ppDefault characterization)**

```lean
-- lean/Toy/Render/Defs.lean:567-640
/-! ## Default recoverability (the structural side of the `ppDefault` characterization) -/

/-- The hint the default text of `t` announces (equal to `hint S (ppDefault t)`),
computed on the term. -/
def dh (S : Sig) : Tm → Option Ty
  | .var x _ => S.varTy x
  | .lit _ _ => none
  | .add _ a b => joinH (dh S a) (dh S b)
  | .sub _ a b => joinH (dh S a) (dh S b)
  | .eq _ _ _ => some .prop
  | .iff _ _ => some .prop
  | .and _ _ => some .prop
  | .coe a => dh S a
  | .const c => S.constTy c

/-- `w` admits the type `τ` (`none` admits every type). -/
def tyMatches (w : Option Ty) (τ : Ty) : Bool :=
  match w with
  | none => true
  | some σ => decide (σ = τ)

/-- `defRec S e w t`: the structural check behind `DefaultRecoverable`. The argument
`e` is the expected type at which the system elaborator `cfg0` meets the default
text of `t`; `w` constrains the type of `t` itself, before any coercion that the
elaborator inserts at the root of `t` (`none` admits every type). `dh S a` is the
hint announced by the default text of `a`; `dh S (coe a) = dh S a`. Clause by
clause:
* `var x τ`: `S.varTy x = some τ`, and `w` admits `τ`;
* `lit τ n`: `τ = (numOnly e).getD .nat`, and `w` admits `τ`;
* `add τ a b`, `sub τ a b`: `τ = opType cfg0 (joinH (dh S a) (dh S b)) e` (the join of
  the operand hints if it is not `none`, else `e` if numeric, else `Nat`), `τ` is
  numeric, both operands pass `defRec S (some τ) (some τ)`, and `w` admits `τ`;
* `eq τ a b`: `τ = (joinH (dh S a) (dh S b)).getD .nat` (`e` is not consulted), `τ` is
  numeric, both operands pass `defRec S (some τ) (some τ)`, and `w` admits `Prop`;
* `iff a b`, `and a b`: both operands pass `defRec S (some .prop) (some .prop)`, and
  `w` admits `Prop`;
* `coe a`: `e = some .int`, `w` admits `Int`, and `a` passes
  `defRec S (some .int) (some .nat)`: met at expected `Int` (the coercion itself is
  not in the text), `a` must still come out at type `Nat`. A numeral, or an
  unannotated `+`/`-` tree all of whose operand hints are `none`, takes type `Int`
  at expected `Int`, so for example `↑(2 : Nat) = z` fails this clause;
* `const c`: `S.constTy c = some τ` for a `τ` that `w` admits. -/
def defRec (S : Sig) : Option Ty → Option Ty → Tm → Bool
  | _, w, .var x τ => decide (S.varTy x = some τ) && tyMatches w τ
  | e, w, .lit τ _ => decide (τ = (numOnly e).getD .nat) && tyMatches w τ
  | e, w, .add τ a b =>
    decide (τ = opType cfg0 (joinH (dh S a) (dh S b)) e) && τ.isNum &&
      defRec S (some τ) (some τ) a && defRec S (some τ) (some τ) b && tyMatches w τ
  | e, w, .sub τ a b =>
    decide (τ = opType cfg0 (joinH (dh S a) (dh S b)) e) && τ.isNum &&
      defRec S (some τ) (some τ) a && defRec S (some τ) (some τ) b && tyMatches w τ
  | _, w, .eq τ a b =>
    decide (τ = (joinH (dh S a) (dh S b)).getD .nat) && τ.isNum &&
      defRec S (some τ) (some τ) a && defRec S (some τ) (some τ) b && tyMatches w .prop
  | _, w, .iff a b =>
    defRec S (some .prop) (some .prop) a && defRec S (some .prop) (some .prop) b &&
      tyMatches w .prop
  | _, w, .and a b =>
    defRec S (some .prop) (some .prop) a && defRec S (some .prop) (some .prop) b &&
      tyMatches w .prop
  | e, w, .coe a =>
    decide (e = some .int) && tyMatches w .int && defRec S (some .int) (some .nat) a
  | _, w, .const c =>
    match S.constTy c with
    | some τ => tyMatches w τ
    | none => false

/-- A term is default-recoverable if it passes `defRec S none none`. By
`elabSys_ppDefault_eq_some_iff_defaultRecoverable` this holds exactly when the
system elaborator reads the term's default text back as the term. -/
def DefaultRecoverable (S : Sig) (t : Tm) : Prop := defRec S none none t = true

instance (S : Sig) (t : Tm) : Decidable (DefaultRecoverable S t) :=
  inferInstanceAs (Decidable (_ = true))
```

**Declarative elaboration**

```lean
-- lean/Toy/Render/Defs.lean:642-668
/-! ## Declarative elaboration -/

/-- `Elabs S s τ t`: `t` is *a* possible elaboration of the syntax `s` at type `τ`,
where an operator without a type argument may be elaborated at any numeric type,
a numeral at any numeric type, and a coercion `↑ : Nat → Int` may be inserted at
any node (`coeIns`). Every deterministic elaborator of the family picks one
derivation. -/
inductive Elabs (S : Sig) : Stx → Ty → Tm → Prop where
  | var {x : Nat} {τ : Ty} : S.varTy x = some τ → Elabs S (.var x) τ (.var x τ)
  | num {n : Nat} {τ : Ty} : τ.isNum = true → Elabs S (.num n) τ (.lit τ n)
  | add {oτ : Option Ty} {τ : Ty} {a b : Stx} {a' b' : Tm} :
      τ.isNum = true → (oτ = none ∨ oτ = some τ) →
      Elabs S a τ a' → Elabs S b τ b' → Elabs S (.add oτ a b) τ (.add τ a' b')
  | sub {oτ : Option Ty} {τ : Ty} {a b : Stx} {a' b' : Tm} :
      τ.isNum = true → (oτ = none ∨ oτ = some τ) →
      Elabs S a τ a' → Elabs S b τ b' → Elabs S (.sub oτ a b) τ (.sub τ a' b')
  | eq {oτ : Option Ty} {τ : Ty} {a b : Stx} {a' b' : Tm} :
      τ.isNum = true → (oτ = none ∨ oτ = some τ) →
      Elabs S a τ a' → Elabs S b τ b' → Elabs S (.eq oτ a b) .prop (.eq τ a' b')
  | iff {a b : Stx} {a' b' : Tm} :
      Elabs S a .prop a' → Elabs S b .prop b' → Elabs S (.iff a b) .prop (.iff a' b')
  | and {a b : Stx} {a' b' : Tm} :
      Elabs S a .prop a' → Elabs S b .prop b' → Elabs S (.and a b) .prop (.and a' b')
  | asc {e : Stx} {τ : Ty} {e' : Tm} : Elabs S e τ e' → Elabs S (.asc e τ) τ e'
  | coe {e : Stx} {e' : Tm} : Elabs S e .nat e' → Elabs S (.coe e) .int (.coe e')
  | const {c : Nat} {τ : Ty} : S.constTy c = some τ → Elabs S (.const c) τ (.const c)
  | coeIns {s : Stx} {t : Tm} : Elabs S s .nat t → Elabs S s .int (.coe t)
```

**Readers that agree on fully annotated text**

```lean
-- lean/Toy/Render/Defs.lean:670-674
/-! ## Readers that agree on fully annotated text -/

/-- `e'` agrees with `e` on fully annotated text. -/
def AgreeOnFull (e e' : Reader) : Prop :=
  ∀ S s, s.fullyAnnotated = true → e' S s = e S s
```

### Running examples (verbatim)

The running signature `S₀` has variables `a b : Nat` (numbers 0 and 1) and `z : Int` (number 2) and the definitions `P := (a = b)` (name 0), `Q := (z = 0)` (name 1) and `PQ := P ∧ Q` (name 2); `ρ₀` is the environment `a = 0, b = 1, z = 0`. The source of these objects:

```lean
-- lean/Toy/Render/Examples.lean:13-68
/-! ## The running signature and terms -/

/-- `a : Nat` (variable 0). -/
def vA : Tm := .var 0 .nat
/-- `b : Nat` (variable 1). -/
def vB : Tm := .var 1 .nat
/-- `z : Int` (variable 2). -/
def vZ : Tm := .var 2 .int

/-- The running signature. Context: `a b : Nat`, `z : Int`. Definitions (telescope,
outermost first): `PQ := P ∧ Q` (name 2), `P := (a = b)` at `Nat` (name 0),
`Q := (z = 0)` at `Int` (name 1). -/
def S₀ : Sig where
  ctx := [(0, .nat), (1, .nat), (2, .int)]
  defs := [⟨2, .prop, .and (.const 0) (.const 1)⟩,
           ⟨0, .prop, .eq .nat vA vB⟩,
           ⟨1, .prop, .eq .int vZ (.lit .int 0)⟩]

/-- `(2 : Nat) - 3 = 0` (true: subtraction truncates). -/
def tNatSub : Tm := .eq .nat (.sub .nat (.lit .nat 2) (.lit .nat 3)) (.lit .nat 0)

/-- `(2 : Int) - 3 = 0` (false). -/
def tIntSub : Tm := .eq .int (.sub .int (.lit .int 2) (.lit .int 3)) (.lit .int 0)

/-- `↑(a - b) = ↑a - ↑b` at `Int` (false when `a < b`). -/
def tTrunc : Tm := .eq .int (.coe (.sub .nat vA vB)) (.sub .int (.coe vA) (.coe vB))

/-- `a - b = a - b` at `Nat` (a tautology): how the default text of `tTrunc` reads back. -/
def tReread : Tm := .eq .nat (.sub .nat vA vB) (.sub .nat vA vB)

/-- `↑(a - b) = z` at `Int`: default text `a - b = z`. -/
def tZ : Tm := .eq .int (.coe (.sub .nat vA vB)) vZ

/-- `↑a - ↑b = z` at `Int`: the leaf-coercion reading of `a - b = z`. -/
def tZLeaves : Tm := .eq .int (.sub .int (.coe vA) (.coe vB)) vZ

/-- `↑(a + b) = z` at `Int`. -/
def tAddOp : Tm := .eq .int (.coe (.add .nat vA vB)) vZ

/-- `↑a + ↑b = z` at `Int`. -/
def tAddLeaves : Tm := .eq .int (.add .int (.coe vA) (.coe vB)) vZ

/-- A fully annotated text `@eq Int (2 : Int) z`. -/
def sTwoEqZ : Stx := .eq (some .int) (.asc (.num 2) .int) (.var 2)

/-- An ill-typed term: the variable `a : Nat` annotated as `Int`. -/
def tIll : Tm := .var 0 .int

/-- An ill-typed proposition `a ↔ a` (with `a : Nat`); its default text does not elaborate. -/
def tIffNat : Tm := .iff vA vA

/-- The environment `a = 0`, `b = 1`, `z = 0`. -/
def ρ₀ : Env where
  nat := fun x => if x = 1 then 1 else 0
  int := fun _ => 0
  prop := fun _ => false
```

The table renders `Stx` values as prose text (an annotation is shown as `(n : τ)`, `↑`, or a type argument written `@op τ`); each cell is backed by the named theorem, quoted in this report.

| term | meaning | default text | `ppMin cfg0` text | annotation tokens: default / `ppMin cfg0` / explicit |
| :--- | :--- | :--- | :--- | :--- |
| `tNatSub` | `(2 : Nat) - 3 = 0`, valid (`valid_tNatSub`) | `2 - 3 = 0` | `2 - 3 = 0` (`default_and_min_texts_faithful_for_cfg0_but_not_other_readers`) | 0 / 0 / 5 |
| `tIntSub` | `(2 : Int) - 3 = 0`, not valid (`not_valid_tIntSub`) | `2 - 3 = 0` | `2 - 3 = (0 : Int)` (`ppMin_tIntSub`) | 0 / 1 / 5 |
| `tTrunc` | `↑(a - b) = ↑a - ↑b` at `Int`, not valid (`not_valid_tTrunc`) | `a - b = a - b` (`ppDefault_tTrunc`) | `a - b = a - ↑b` (`ppMin_tTrunc`) | 0 / 1 / 6 |
| `tZ` | `↑(a - b) = z` at `Int` | `a - b = z` | `a - b = z` (`default_and_min_texts_faithful_for_cfg0_but_not_other_readers`) | 0 / 0 / 3 |

Annotation counts: `annCount_overhead_examples`. For `ppMin cfgLeaves` the counts on `tTrunc, tZ, tIntSub, tNatSub` are 2, 1, 1, 0, and for `ppMin cfgIntNumerals` they are 1, 0, 0, 1 (`annCount_overhead_examples_other_readers`). `tReread = (a - b = a - b at Nat)` is valid (`valid_tReread`) and is how the system elaborator reads the default text of `tTrunc`; `tZLeaves = (↑a - ↑b = z)` is how the leaf-coercion reader reads `a - b = z`.

### Definition examples (verbatim)

Proved positive and negative examples for the core definitions: the rest of `Toy/Render/Examples.lean`, section by section, verbatim. Named theorems and unnamed `example` checks are both kernel-checked when the library is built.

**Examples: types and hints**

```lean
-- lean/Toy/Render/Examples.lean:70-77
/-! ## Examples: types and hints -/

example : Ty.isNum .int = true := rfl
example : Ty.isNum .prop = false := rfl
example : joinH (some .nat) (some .int) = some .int := rfl
example : joinH none none = none := rfl
example : numOnly (some .prop) = none := rfl
example : numOnly (some .int) = some .int := rfl
```

**Examples: typing**

```lean
-- lean/Toy/Render/Examples.lean:79-86
/-! ## Examples: typing -/

/-- Positive: `↑(a - b) = ↑a - ↑b` is well typed. -/
theorem wellTyped_tTrunc : WellTyped S₀ tTrunc := by decide
/-- Negative: a coercion applied to an `Int` is rejected. -/
theorem not_wellTyped_coe_int : ¬ WellTyped S₀ (.coe vZ) := by decide
/-- Negative: a variable annotated with a type other than its context type is rejected. -/
theorem not_wellTyped_tIll : ¬ WellTyped S₀ tIll := by decide
```

**Examples: semantics**

```lean
-- lean/Toy/Render/Examples.lean:88-99
/-! ## Examples: semantics -/

/-- Positive: `(2 : Nat) - 3 = 0` is valid. -/
theorem valid_tNatSub : Valid S₀ tNatSub := fun _ => rfl
/-- Negative: `(2 : Int) - 3 = 0` is not valid (it is false everywhere). -/
theorem not_denote_tIntSub (ρ : Env) : ¬ Denote S₀ tIntSub ρ := by
  simp [Denote, eval, evalD, evalWith, tIntSub, S₀, Val.toInt, Val.toBool]
theorem not_valid_tIntSub : ¬ Valid S₀ tIntSub := fun h => not_denote_tIntSub ρ₀ (h ρ₀)
/-- Positive: the abbreviation `P` means `a = b`. -/
example : eval S₀ ρ₀ (.const 0) = eval S₀ ρ₀ (.eq .nat vA vB) := by decide
/-- Negative: an undefined name has the default value. -/
example : eval S₀ ρ₀ (.const 9) = undefVal := by decide
```

**Examples: δ-unfolding**

```lean
-- lean/Toy/Render/Examples.lean:101-106
/-! ## Examples: δ-unfolding -/

/-- Positive: `PQ` unfolds to `(a = b) ∧ (z = 0)`. -/
example : deltaNF S₀ (.const 2) = .and (.eq .nat vA vB) (.eq .int vZ (.lit .int 0)) := by decide
/-- Negative: an undefined name is left alone. -/
example : deltaNF S₀ (.const 9) = .const 9 := by decide
```

**Examples: elaboration**

```lean
-- lean/Toy/Render/Examples.lean:108-130
/-! ## Examples: elaboration -/

example : hint S₀ (.num 2) = none := rfl
example : hint S₀ (.add none (.var 0) (.num 2)) = some .nat := by decide
example : opType cfg0 (some .nat) (some .int) = .nat := rfl
example : opType cfgLeaves (some .nat) (some .int) = .int := rfl
example : coerceTo (some .int) (vA, .nat) = some (.coe vA, .int) := by decide
/-- Negative: there is no `Int ↝ Nat` coercion. -/
example : coerceTo (some .nat) (vZ, .int) = none := by decide

/-- Positive: the system elaborator reads `a - b = z` as `↑(a - b) = z`. -/
theorem elabSys_ppDefault_tZ : elabSys S₀ (ppDefault tZ) = some tZ := by decide
/-- Negative: `a ↔ a` with `a : Nat` does not elaborate. -/
theorem elabSys_ppDefault_tIffNat : elabSys S₀ (ppDefault tIffNat) = none := by decide
/-- Positive: an unconstrained numeral defaults to `Nat` under `cfg0`. -/
example : elabSys S₀ (.num 2) = some (.lit .nat 2) := by decide
/-- Negative: under `cfgIntNumerals` the same numeral is read at `Int`. -/
example : elabWith cfgIntNumerals S₀ (.num 2) ≠ some (.lit .nat 2) := by decide

/-- Positive: the explicit rendering of `tTrunc` is faithful. -/
theorem faithful_ppExplicit_tTrunc : Faithful cfg0 S₀ (ppExplicit tTrunc) tTrunc := by decide
/-- Negative: the default rendering of `tTrunc` is not faithful. -/
theorem not_faithful_ppDefault_tTrunc : ¬ Faithful cfg0 S₀ (ppDefault tTrunc) tTrunc := by decide
```

**Examples: printers**

```lean
-- lean/Toy/Render/Examples.lean:132-178
/-! ## Examples: printers -/

/-- Positive: the default text of `tTrunc` is `a - b = a - b`. -/
theorem ppDefault_tTrunc :
    ppDefault tTrunc = .eq none (.sub none (.var 0) (.var 1)) (.sub none (.var 0) (.var 1)) := by
  decide
/-- Positive: the explicit text of `tTrunc` is `@eq Int ↑(@sub Nat a b) (@sub Int ↑a ↑b)`. -/
theorem ppExplicit_tTrunc :
    ppExplicit tTrunc = .eq (some .int) (.coe (.sub (some .nat) (.var 0) (.var 1)))
      (.sub (some .int) (.coe (.var 0)) (.coe (.var 1))) := by
  decide
/-- Negative: the default printer does not show a coercion. -/
example : ppDefault (.coe vA) ≠ .coe (.var 0) := by decide
/-- Positive: an intermediate printer shows numeral types only. -/
example : ppNumericTypes tIntSub =
    .eq none (.sub none (.asc (.num 2) .int) (.asc (.num 3) .int)) (.asc (.num 0) .int) := by decide
/-- Negative: the numeral-type printer does not show coercions. -/
example : ppNumericTypes (.coe vA) = .var 0 := by decide
example : annPos [] tZ = [([], .typeArg), ([0], .coercion), ([0, 0], .typeArg)] := by decide
/-- Negative: a variable has no annotation position. -/
example : annPos [] vA = [] := rfl
example : maskOf [([], .typeArg)] [] .typeArg = true := by decide
example : maskOf [([], .typeArg)] [] .coercion = false := by decide

/-- Positive: the deletion-greedy rendering of `tTrunc` under `cfg0` is
`a - b = a - ↑b` (one explicit coercion). -/
theorem ppMin_tTrunc :
    ppMin cfg0 S₀ tTrunc =
      .eq none (.sub none (.var 0) (.var 1)) (.sub none (.var 0) (.coe (.var 1))) := by
  decide
/-- Negative: it is not the default rendering. -/
example : ppMin cfg0 S₀ tTrunc ≠ ppDefault tTrunc := by decide

/-- Positive: the deletion-greedy rendering of `(2 : Int) - 3 = 0` under `cfg0` is
`2 - 3 = (0 : Int)` (one ascription). -/
theorem ppMin_tIntSub :
    ppMin cfg0 S₀ tIntSub = .eq none (.sub none (.num 2) (.num 3)) (.asc (.num 0) .int) := by
  decide

example : (ppExplicit tTrunc).annCount = 6 := by decide
example : (ppDefault tTrunc).annCount = 0 := by decide
example : (ppExplicit tTrunc).erase = ppDefault tTrunc := by decide
/-- Positive / negative: explicit text is fully annotated, default text is not. -/
example : (ppExplicit tTrunc).fullyAnnotated = true := by decide
example : (ppDefault tTrunc).fullyAnnotated = false := by decide
example : (ppDefault tAddOp).subFree = true := by decide
example : (ppDefault tZ).subFree = false := by decide
```

**Examples: default recoverability**

```lean
-- lean/Toy/Render/Examples.lean:180-186
/-! ## Examples: default recoverability -/

example : dh S₀ (.coe (.sub .nat vA vB)) = some .nat := by decide
/-- Positive: every annotation `ppDefault` elides from `tZ` is recoverable. -/
theorem defaultRecoverable_tZ : DefaultRecoverable S₀ tZ := by decide
/-- Negative: the coercion of `↑(a - b) = ↑a - ↑b` is not recoverable. -/
theorem not_defaultRecoverable_tTrunc : ¬ DefaultRecoverable S₀ tTrunc := by decide
```

**Examples: declarative elaboration**

```lean
-- lean/Toy/Render/Examples.lean:188-206
/-! ## Examples: declarative elaboration -/

/-- Positive: `a - b = z` admits the operator-coercion elaboration. -/
theorem elabs_ppDefault_tZ_tZ : Elabs S₀ (ppDefault tZ) .prop tZ :=
  .eq (τ := .int) rfl (.inl rfl)
    (.coeIns (.sub rfl (.inl rfl) (.var rfl) (.var rfl)))
    (.var rfl)

/-- Positive: `a - b = z` also admits the leaf-coercion elaboration. -/
theorem elabs_ppDefault_tZ_tZLeaves : Elabs S₀ (ppDefault tZ) .prop tZLeaves :=
  .eq (τ := .int) rfl (.inl rfl)
    (.sub rfl (.inl rfl) (.coeIns (.var rfl)) (.coeIns (.var rfl)))
    (.var rfl)

/-- Negative: an `Int` variable never elaborates at `Nat` (no `Int ↝ Nat` coercion). -/
theorem not_elabs_int_var_at_nat (t : Tm) : ¬ Elabs S₀ (.var 2) .nat t := by
  intro h
  cases h with
  | var h => simp [Sig.varTy, ctxLookup, S₀] at h
```

**Examples: agreeing readers**

```lean
-- lean/Toy/Render/Examples.lean:208-217
/-! ## Examples: agreeing readers -/

/-- Positive: the system elaborator agrees with itself. -/
theorem agreeOnFull_refl : AgreeOnFull elabSys elabSys := fun _ _ _ => rfl
/-- Negative: the reader that never answers does not agree with it. -/
theorem not_agreeOnFull_none : ¬ AgreeOnFull elabSys (fun _ _ => none) := by
  intro h
  have := h S₀ (ppExplicit tTrunc) (by decide)
  revert this
  decide
```

**Examples: subtraction-annotated syntax**

```lean
-- lean/Toy/Render/Examples.lean:219-227
/-! ## Examples: subtraction-annotated syntax -/

/-- Positive: explicit text annotates every subtraction. -/
example : (ppExplicit tTrunc).subAnnotated = true := by decide
/-- Positive: a text with an annotated `-` but an unannotated `=` and `+`. -/
example : (Stx.eq none (.add none (.sub (some .nat) (.var 0) (.var 1)) (.var 0)) (.var 2)).subAnnotated
    = true := by decide
/-- Negative: the default text `a - b = z` has an unannotated `-`. -/
example : (ppDefault tZ).subAnnotated = false := by decide
```

**Examples: the coercion-showing printer**

```lean
-- lean/Toy/Render/Examples.lean:229-234
/-! ## Examples: the coercion-showing printer -/

/-- Positive: `ppCoercions` shows a coercion. -/
example : ppCoercions (.coe vA) = .coe (.var 0) := by decide
/-- Negative: `ppCoercions` does not show numeral types. -/
example : ppCoercions (.lit .int 2) = .num 2 := by decide
```

**Examples: a degenerate configuration**

```lean
-- lean/Toy/Render/Examples.lean:236-244
/-! ## Examples: a degenerate configuration -/

/-- A configuration whose numeral default is `Prop` (allowed by `ElabCfg`). -/
def cfgPropNumerals : ElabCfg := { numDefault := .prop, rule := .atOperator }

/-- Negative: under `cfgPropNumerals` an unconstrained numeral does not elaborate. -/
example : elabWith cfgPropNumerals S₀ (.num 2) = none := by decide
/-- Positive: an ascribed numeral still elaborates under `cfgPropNumerals`. -/
example : elabWith cfgPropNumerals S₀ (.asc (.num 2) .int) = some (.lit .int 2) := by decide
```

**Examples: what DefaultRecoverable rejects and admits**

```lean
-- lean/Toy/Render/Examples.lean:246-281
/-! ## Examples: what `DefaultRecoverable` rejects and admits -/

/-- `↑(2 : Nat) = z` at `Int`. -/
def tCoeTwoEqZ : Tm := .eq .int (.coe (.lit .nat 2)) vZ
/-- `↑((2 : Nat) - 3) = z` at `Int`. -/
def tCoeNumSub : Tm := .eq .int (.coe (.sub .nat (.lit .nat 2) (.lit .nat 3))) vZ
/-- `(2 : Int) + 3 = z` at `Int`. -/
def tAddIntNumEqZ : Tm := .eq .int (.add .int (.lit .int 2) (.lit .int 3)) vZ

/-- Negative: a coerced numeral is not default-recoverable, although the coerced
subterm has type `Nat` and meets an expected `Int`; its default text `2 = z` reads
back as `(2 : Int) = z`. -/
theorem not_defaultRecoverable_tCoeTwoEqZ :
    WellTyped S₀ tCoeTwoEqZ ∧ tyOf S₀ (.lit .nat 2) = some .nat ∧
      ¬ DefaultRecoverable S₀ tCoeTwoEqZ ∧
      elabSys S₀ (ppDefault tCoeTwoEqZ) = some (.eq .int (.lit .int 2) vZ) := by
  decide

/-- Negative: a coerced unannotated numeral subtraction is not default-recoverable;
its default text `2 - 3 = z` reads back as `(2 : Int) - 3 = z`, which differs in truth
at `ρ₀`. -/
theorem not_defaultRecoverable_tCoeNumSub :
    WellTyped S₀ tCoeNumSub ∧ tyOf S₀ (.sub .nat (.lit .nat 2) (.lit .nat 3)) = some .nat ∧
      ¬ DefaultRecoverable S₀ tCoeNumSub ∧
      elabSys S₀ (ppDefault tCoeNumSub) =
        some (.eq .int (.sub .int (.lit .int 2) (.lit .int 3)) vZ) ∧
      Denote S₀ tCoeNumSub ρ₀ ∧ ¬ Denote S₀ (.eq .int (.sub .int (.lit .int 2) (.lit .int 3)) vZ) ρ₀ := by
  decide

/-- Positive: an operator whose operand hints are both `none` takes the expected
type (`Int`, from the other side of `=`). -/
theorem defaultRecoverable_tAddIntNumEqZ :
    joinH (dh S₀ (.lit .int 2)) (dh S₀ (.lit .int 3)) = none ∧
      DefaultRecoverable S₀ tAddIntNumEqZ ∧
      elabSys S₀ (ppDefault tAddIntNumEqZ) = some tAddIntNumEqZ := by
  decide
```

### Concrete objects used in counterexamples, witnesses and remarks (verbatim)

```lean
-- lean/Toy/Render/Counterexamples.lean:79-81
/-- The text `a - b = z` with the type argument `Int` on `-`: type-correct, but not
the type `-` has in `tZ`. -/
def sWrongSub : Stx := .eq none (.sub (some .int) (.var 0) (.var 1)) (.var 2)
-- lean/Toy/Render/Counterexamples.lean:93-95
/-- A hand rendering of `PQ` (name 2) with its definitions unfolded but its
conjuncts swapped: `z = 0 ∧ a = b`. -/
def rSwapped : Stx := .and (.eq none (.var 2) (.num 0)) (.eq none (.var 0) (.var 1))
-- lean/Toy/Render/Counterexamples.lean:97-98
/-- The reading of `rSwapped`. -/
def tSwapped : Tm := .and (.eq .int vZ (.lit .int 0)) (.eq .nat vA vB)
-- lean/Toy/Render/Counterexamples.lean:122-123
/-- `a = b` at `Nat`. -/
def tEqAB : Tm := .eq .nat vA vB
-- lean/Toy/Render/Counterexamples.lean:264-265
/-- `↑(0 : Nat) = (0 : Int)` at `Int`. -/
def tCoeZeroEqZero : Tm := .eq .int (.coe (.lit .nat 0)) (.lit .int 0)
-- lean/Toy/Render/Counterexamples.lean:285-286
/-- `↑a = ↑b` at `Int`. -/
def tCoeEqCoe : Tm := .eq .int (.coe vA) (.coe vB)
-- lean/Toy/Render/Counterexamples.lean:297-301
/-- The deletion-greedy selection visiting positions in reverse pre-order. -/
def minMaskRev (cfg : ElabCfg) (S : Sig) (t : Tm) : List (Path × AnnKind) :=
  (annPos [] t).reverse.foldl
    (fun M q => if faithfulB cfg S (ppMask (maskOf (M.erase q)) [] t) t then M.erase q else M)
    (annPos [] t)
-- lean/Toy/Render/Counterexamples.lean:380-381
/-- The ill-typed `a = z` at `Int` with `a : Nat` annotated as `Int`. -/
def tIllEq : Tm := .eq .int (.var 0 .int) vZ
-- lean/Toy/Render/Counterexamples.lean:393-395
/-- A signature whose single definition is ill typed: `c₀ : Prop := (x₉₉ : Int)`
with `x₉₉` not in the context. -/
def S_illDef : Sig := { ctx := [], defs := [⟨0, .prop, .var 99 .int⟩] }
-- lean/Toy/Render/Counterexamples.lean:403-404
/-- `0 = 0` at `Nat`. -/
def tZeroEqZero : Tm := .eq .nat (.lit .nat 0) (.lit .nat 0)
-- lean/Toy/Render/Counterexamples.lean:418-419
/-- An ill-typed proposition-typed numeral. -/
def tLitProp : Tm := .lit .prop 0
-- lean/Toy/Render/Witnesses.lean:70-73
/-- A reader that agrees with the system elaborator on fully annotated text and
otherwise reads like the leaf-coercion configuration. -/
def eLeavesOnNonFull : Reader :=
  fun S s => if s.fullyAnnotated = true then elabSys S s else elabWith cfgLeaves S s
-- lean/Toy/Render/Witnesses.lean:114-115
/-- `a - b + a = z` with the subtraction annotated at `Nat` and nothing else annotated. -/
def sSubAnnMixed : Stx := .eq none (.add none (.sub (some .nat) (.var 0) (.var 1)) (.var 0)) (.var 2)
-- lean/Toy/Render/Remarks.lean:15-17
/-- The unannotated text `z - z = z` (with `z : Int`). It contains a subtraction
without a type argument. -/
def sZZSub : Stx := .eq none (.sub none (.var 2) (.var 2)) (.var 2)
-- lean/Toy/Render/Remarks.lean:58-59
/-- The unannotated text `a - a = z` (with `a : Nat`, `z : Int`). -/
def sAASub : Stx := .eq none (.sub none (.var 0) (.var 0)) (.var 2)
```

### Build-checked observations of Lean v4.34.1

`Toy/Render/LeanObservations.lean` is part of the library and is checked by `lake build`: each `#guard_msgs` block fails the build if the message printed by the following command differs from the `info:` text above it. Every block runs with Lean's default options except where a `set_option … in` line names an option; the defaults involved, as documented in `src/Lean/PrettyPrinter/Delaborator/Options.lean` at the toolchain commit, are `pp.numericTypes` false, `pp.coercions` true, `pp.explicit` false, and (in `TopDownAnalyze.lean`) `pp.analyze` false. Basis: execution (Lean v4.34.1 build) for each printed output below; these observations concern the named inputs and options and are not theorems about Lean. The source of each section, verbatim:

*Numeral types.* With default options (`pp.numericTypes` false), `#check ((2 : Int) - 3 = 0)` and `#check ((2 : Nat) - 3 = 0)` both print `2 - 3 = 0 : Prop`, although the first proposition is false and the second true (the two `example`s are checked by `decide`). With `set_option pp.numericTypes true`, the `Int` statement prints as `(2 : Int) - (3 : Int) = (0 : Int) : Prop`.

```lean
-- lean/Toy/Render/LeanObservations.lean:13-30
/-! ## Numeral types are elided by default -/

/-- info: 2 - 3 = 0 : Prop -/
#guard_msgs in
#check ((2 : Int) - 3 = 0)

/-- info: 2 - 3 = 0 : Prop -/
#guard_msgs in
#check ((2 : Nat) - 3 = 0)

-- The two statements above have different truth values.
example : (2 : Nat) - 3 = 0 := by decide
example : ¬ ((2 : Int) - 3 = 0) := by decide

/-- info: (2 : Int) - (3 : Int) = (0 : Int) : Prop -/
#guard_msgs in
set_option pp.numericTypes true in
#check ((2 : Int) - 3 = 0)
```

*Coercions.* With default options (`pp.coercions` true), the term `fun (a b : Nat) => ((a - b : Nat) : Int) = (a : Int) - (b : Int)` prints as `fun a b => ↑(a - b) = ↑a - ↑b : Nat → Nat → Prop`: coercions are displayed as `↑`, not elided. With `set_option pp.coercions false`, it prints as `fun a b => (a - b).cast = a.cast - b.cast : Nat → Nat → Prop`.

```lean
-- lean/Toy/Render/LeanObservations.lean:32-41
/-! ## Coercions are shown (as `↑`) by default -/

/-- info: fun a b => ↑(a - b) = ↑a - ↑b : Nat → Nat → Prop -/
#guard_msgs in
#check fun (a b : Nat) => ((a - b : Nat) : Int) = (a : Int) - (b : Int)

/-- info: fun a b => (a - b).cast = a.cast - b.cast : Nat → Nat → Prop -/
#guard_msgs in
set_option pp.coercions false in
#check fun (a b : Nat) => ((a - b : Nat) : Int) = (a : Int) - (b : Int)
```

*Coercion placement.* With default options, `fun (a b : Nat) (z : Int) => a - b = z` elaborates and prints as `fun a b z => ↑a - ↑b = z : Nat → Nat → Int → Prop`, with the coercions on the leaves; the `example` checks by `rfl` that the ascription `(a - b : Int)` elaborates to `(a : Int) - (b : Int)`.

```lean
-- lean/Toy/Render/LeanObservations.lean:43-49
/-! ## The elaborator places coercions at the leaves of an arithmetic tree -/

/-- info: fun a b z => ↑a - ↑b = z : Nat → Nat → Int → Prop -/
#guard_msgs in
#check fun (a b : Nat) (z : Int) => a - b = z

example (a b : Nat) : ((a - b : Int)) = (a : Int) - (b : Int) := rfl
```

*`pp.analyze` on the truncation example.* With `set_option pp.analyze true` (its sub-options, among them `pp.analyze.typeAscriptions` (default true) and `pp.analyze.trustOfNat` (default true), and all other options at their defaults), the coercion term above prints as `fun a b => ↑(a - b) = HSub.hSub (α := Int) ↑a ↑b : Nat → Nat → Prop`.

```lean
-- lean/Toy/Render/LeanObservations.lean:51-56
/-! ## `pp.analyze` adds an annotation it deems needed for re-elaboration -/

/-- info: fun a b => ↑(a - b) = HSub.hSub (α := Int) ↑a ↑b : Nat → Nat → Prop -/
#guard_msgs in
set_option pp.analyze true in
#check fun (a b : Nat) => ((a - b : Nat) : Int) = (a : Int) - (b : Int)
```

*`pp.analyze` on the numeral collision.* With `set_option pp.analyze true` (sub-options and all other options at their defaults, as in the previous section), `#check ((2 : Int) - 3 = 0)` still prints `2 - 3 = 0 : Prop`, the same text as the `Nat` statement under default options.

```lean
-- lean/Toy/Render/LeanObservations.lean:58-68
/-! ## `pp.analyze` does not always add the annotation that separates a collision

With `pp.analyze` enabled, the `Int` statement of the numeral collision above still
prints without any numeral type, exactly like the `Nat` statement. (The option's
documentation in `TopDownAnalyze.lean` states that the analysis is "neither sound
nor complete".) -/

/-- info: 2 - 3 = 0 : Prop -/
#guard_msgs in
set_option pp.analyze true in
#check ((2 : Int) - 3 = 0)
```

These observations are recorded for the modeling-bridge paragraphs in Findings. The module documentation of `TopDownAnalyze.lean` at the toolchain commit describes the `pp.analyze` analysis as "neither sound nor complete" (documentation, read at that commit on 2026-11-21).

## Findings

Each card gives the tier, kind and depth, the plain claim, the Lean statement quoted verbatim (signature up to `:=`, proof elided as `:= …`), where useful an unfolded rendering (a Lean term checked to be definitionally equal to the quoted statement, or a block labelled prose), the hypothesis ledger, the non-vacuity witness, the positive control for the impossibility result, the verbatim statements of the tightness counterexamples and non-vacuity witnesses, prior art, the design question and the evidence basis. A hypothesis is *tight* when a proved counterexample satisfies all the other hypotheses and falsifies the conclusion; the class of that witness is recorded. Unfolded renderings elaborate in namespace `Toy.Render` (the namespace of every quoted declaration) with `autoImplicit` off. Non-claims are listed under **Boundaries**.

### Default and explicit printing

#### 1. `default_printer_collision_changes_truth`

Tier T1 · kind: impossibility · depth: shallow · Lean: `ppDefault_collision_natSub_intSub_changes_truth`

**Plain claim.** In the running signature S₀, the default printer (which elides numeral types, type arguments and coercions) maps the distinct closed terms (2 : Nat) - 3 = 0 and (2 : Int) - 3 = 0 to the same text 2 - 3 = 0; the first is valid and the second is not; and for every reader R (any function from a signature and a text to an optional term), R does not return (2 : Nat) - 3 = 0 on the default text of the first, or R does not return (2 : Int) - 3 = 0 on the default text of the second.

**Statement.**

```lean
-- lean/Toy/Render/Counterexamples.lean:20-24
theorem ppDefault_collision_natSub_intSub_changes_truth :
    tNatSub ≠ tIntSub ∧ ppDefault tNatSub = ppDefault tIntSub ∧
      Valid S₀ tNatSub ∧ ¬ Valid S₀ tIntSub ∧
      ∀ R : Reader, R S₀ (ppDefault tNatSub) ≠ some tNatSub ∨
        R S₀ (ppDefault tIntSub) ≠ some tIntSub := …
```

Unfolded statement of `ppDefault_collision_natSub_intSub_changes_truth` (`Reader` and `Valid` written out):

```lean
tNatSub ≠ tIntSub ∧ ppDefault tNatSub = ppDefault tIntSub ∧
  (∀ ρ, Denote S₀ tNatSub ρ) ∧ ¬ (∀ ρ, Denote S₀ tIntSub ρ) ∧
  ∀ R : Sig → Stx → Option Tm, R S₀ (ppDefault tNatSub) ≠ some tNatSub ∨
    R S₀ (ppDefault tIntSub) ≠ some tIntSub
```

**Hypothesis ledger.**

No hypotheses beyond the parameters: the statement is a closed proposition about concrete objects of the running signature `S₀`.

**Non-vacuity.** No hypotheses: the statement is about two concrete closed terms of S₀.

**Positive control.** The explicit printer separates the two terms: their explicit texts differ, and the system elaborator reads each explicit text back as the term it was printed from. This is a nearby setting (a printer that shows annotations) in which the impossibility's conclusion fails for the system elaborator. (`ppExplicit_separates_natSub_intSub`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:36-39
theorem ppExplicit_separates_natSub_intSub :
    ppExplicit tNatSub ≠ ppExplicit tIntSub ∧
      elabSys S₀ (ppExplicit tNatSub) = some tNatSub ∧
      elabSys S₀ (ppExplicit tIntSub) = some tIntSub := …
```

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified. Relation to this card: the two terms give the toy analogue of a Pollack-axiom (2 : Nat) - 3 = 0 ↔ (2 : Int) - 3 = 0 whose sides differ in truth.
- Robert Pollack, 'How to believe a machine-checked proof', in G. Sambin and J. M. Smith (eds.), Twenty-Five Years of Constructive Type Theory, Oxford University Press, 1998, pp. 205-220, DOI 10.1093/oso/9780198501275.003.0013; preprint BRICS Report Series RS-97-18 (1997), DOI 10.7146/brics.v4i18.18945. Section 3.1 'Reading the files': a reader sees a concrete representation (a string) while the checker uses an abstract syntax tree; unless their relationship is understood nothing the checker says can be believed, so a checker should support an official syntax that is parseable and printable.
- Mark Adams, 'HOL Zero's Solutions for Pollack-Inconsistency', Interactive Theorem Proving (ITP 2016), LNCS 9807, pp. 20-35, Springer, 2016, DOI 10.1007/978-3-319-43144-4_2. Only the abstract was consulted: HOL Zero aims at well-behaved parsing/printing and Pollack-consistency, and annotates terms minimally with types for unambiguous printing.
- Lean 4 v4.34.1 (leanprover/lean4 commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Lean/PrettyPrinter/Delaborator/Options.lean: pp.explicit (default false, 'display implicit arguments'), pp.coercions (default true, described as 'hide coercion applications'; with the default, coercions are displayed as an up-arrow, not elided), pp.numericTypes (default false, 'display types of numeric literals'); src/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.lean: pp.analyze (default false, 'try to determine annotations sufficient to ensure round-tripping'); its module documentation says the analyzer 'is neither sound nor complete'. With pp.analyze enabled, this toolchain prints ((2 : Int) - 3 = 0) as 2 - 3 = 0 (build-checked observation in LeanObservations.lean). Modeling bridge (model–system relation: none proved): the toy models neither this printer nor the analyzer.

**Design question.** Can a reader of printed statements rely on default-printed text to identify the statement that was proved? (No: in the toy, two statements with different truth values share their default text.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Model–system relation: none proved. Lean v4.34.1 with default options (in particular `pp.numericTypes` false) prints both `((2 : Nat) - 3 = 0)` and `((2 : Int) - 3 = 0)` as `2 - 3 = 0 : Prop`; with `pp.numericTypes` true it prints the second as `(2 : Int) - (3 : Int) = (0 : Int) : Prop`; and with `pp.analyze` true it still prints the second as `2 - 3 = 0 : Prop` (build-checked observations quoted under Applicability). So a collision of the same shape occurs in that printer's character output on these inputs. That observation is not a consequence of the theorem, and the theorem says nothing about Lean.

#### 2. `explicit_printer_section_law`

Tier T1 · kind: theorem · depth: shallow · Lean: `elabWith_ppExplicit_of_wellTyped`

**Plain claim.** For every elaborator configuration cfg of the family (any numeral default, including the degenerate default Prop, and either coercion-placement rule), every signature S and every term t: if t is well typed in S, then cfg reads the explicit text ppExplicit t (every type argument, numeral ascription and coercion printed) back as exactly t.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:19-20
theorem elabWith_ppExplicit_of_wellTyped (cfg : ElabCfg) (S : Sig) (t : Tm)
    (ht : WellTyped S t) : elabWith cfg S (ppExplicit t) = some t := …
```

Unfolded statement of `elabWith_ppExplicit_of_wellTyped` (`WellTyped` written out):

```lean
∀ (cfg : ElabCfg) (S : Sig) (t : Tm), (∃ τ, tyOf S t = some τ) →
  elabWith cfg S (ppExplicit t) = some t
```

**Hypothesis ledger.**

- `ht : WellTyped S t` — The explicit printer omits the type annotation of a variable (the context supplies it), so an annotation that disagrees with the context cannot be recovered; every term that an elaborator of the family returns is well typed (`elabE_sound`). Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: an ill-typed variable term (a : Nat annotated as Int) under the system configuration cfg0. (*tight: counterexample `ce_elabWith_ppExplicit_drop_wellTyped`*)

**Non-vacuity.** tTrunc = ↑(a - b) = ↑a - ↑b at Int is well typed in S₀. (`nv_elabWith_ppExplicit_of_wellTyped`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:138-139
theorem ce_elabWith_ppExplicit_drop_wellTyped :
    ¬ WellTyped S₀ tIll ∧ elabWith cfg0 S₀ (ppExplicit tIll) ≠ some tIll := …
-- lean/Toy/Render/Witnesses.lean:14
theorem nv_elabWith_ppExplicit_of_wellTyped : WellTyped S₀ tTrunc := …
```

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified. Relation to this card: the explicit printer plays the role of the failsafe printer of Section 8.1, and this card is its round-trip property for the toy family.
- Nils Anders Danielsson, 'Correct-by-construction pretty-printing', Proceedings of the 2013 ACM SIGPLAN Workshop on Dependently-Typed Programming (DTP '13), pp. 1-12, DOI 10.1145/2502409.2502410: pretty-printing and then parsing with the same unambiguous grammar returns the original value; it concerns concrete syntax and involves no elaboration.
- Tillmann Rendel and Klaus Ostermann, 'Invertible syntax descriptions: unifying parsing and pretty printing', Haskell '10 (Third ACM Haskell Symposium), pp. 1-12, ACM, 2010, DOI 10.1145/1863523.1863525, also in ACM SIGPLAN Notices 45(11): one syntax description yields both a parser and a printer via partial isomorphisms; it concerns concrete syntax and involves no elaboration.
- Lean 4 v4.34.1 (leanprover/lean4 commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Lean/PrettyPrinter/Delaborator/Options.lean: pp.explicit (default false, 'display implicit arguments'), pp.coercions (default true, described as 'hide coercion applications'; with the default, coercions are displayed as an up-arrow, not elided), pp.numericTypes (default false, 'display types of numeric literals'); src/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.lean: pp.analyze (default false, 'try to determine annotations sufficient to ensure round-tripping'); its module documentation says the analyzer 'is neither sound nor complete'. With pp.analyze enabled, this toolchain prints ((2 : Int) - 3 = 0) as 2 - 3 = 0 (build-checked observation in LeanObservations.lean). Modeling bridge (model–system relation: none proved): the toy models neither this printer nor the analyzer.

**Design question.** Is there a printer whose output every configuration of the family reads back as the original term? (Yes on well-typed terms: the explicit printer.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 3. `default_faithful_iff_default_recoverable`

Tier T1 · kind: characterization · depth: substantive · Lean: `elabSys_ppDefault_eq_some_iff_defaultRecoverable`, `elabSys_ppDefault_of_defaultRecoverable`, `defaultRecoverable_of_elabSys_ppDefault`

**Plain claim.** For every signature S and every term t (well typed or not): the system elaborator cfg0 (numeral default Nat, coercions at the operator) reads the default text of t back as t if and only if t passes the structural check DefaultRecoverable S t (the recursion defRec, quoted verbatim under Applicability; clause-by-clause description in this card).

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:47-48
theorem elabSys_ppDefault_eq_some_iff_defaultRecoverable (S : Sig) (t : Tm) :
    elabSys S (ppDefault t) = some t ↔ DefaultRecoverable S t := …
-- lean/Toy/Render/Statements.lean:27-28
theorem elabSys_ppDefault_of_defaultRecoverable (S : Sig) (t : Tm)
    (h : DefaultRecoverable S t) : elabSys S (ppDefault t) = some t := …
-- lean/Toy/Render/Statements.lean:36-37
theorem defaultRecoverable_of_elabSys_ppDefault (S : Sig) (t : Tm)
    (h : elabSys S (ppDefault t) = some t) : DefaultRecoverable S t := …
```

Unfolded statement of `elabSys_ppDefault_eq_some_iff_defaultRecoverable` (`elabSys` and `DefaultRecoverable` written out):

```lean
∀ (S : Sig) (t : Tm), elabWith cfg0 S (ppDefault t) = some t ↔ defRec S none none t = true
```

`defRec` and `DefaultRecoverable` are quoted verbatim under **Applicability** (section *Default recoverability*).

*Definitions used (prose restating the quoted source).* DefaultRecoverable S t is defRec S none none t = true, where defRec S e w t checks t against the expected type e at which cfg0 meets the default text of t, with w constraining the type of t itself before any coercion inserted at its root (none admits every type); dh S a is the hint announced by the default text of a, and dh S (coe a) = dh S a. Clauses: var x τ: S.varTy x = some τ and w admits τ. lit τ n: τ = (numOnly e).getD Nat and w admits τ. add/sub τ a b: τ = opType cfg0 (joinH (dh S a) (dh S b)) e (the join of the operand hints if it is not none, else e if numeric, else Nat), τ is numeric, both operands pass defRec S (some τ) (some τ), and w admits τ. eq τ a b: τ = (joinH (dh S a) (dh S b)).getD Nat (e is not consulted), τ is numeric, both operands pass defRec S (some τ) (some τ), and w admits Prop. iff/and a b: both operands pass defRec S (some Prop) (some Prop), and w admits Prop. coe a: e = some Int, w admits Int, and a passes defRec S (some Int) (some Nat): met at expected Int (the coercion itself is not in the text), a must still come out at type Nat. const c: S.constTy c = some τ for a τ that w admits.

**Hypothesis ledger.**

- `h : DefaultRecoverable S t (in elabSys_ppDefault_of_defaultRecoverable)` — The 'if' direction as a separate lemma. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the well-typed tTrunc in S₀. (*tight: counterexample `ce_elabSys_ppDefault_drop_defaultRecoverable`*)
- `h : elabSys S (ppDefault t) = some t (in defaultRecoverable_of_elabSys_ppDefault)` — The 'only if' direction as a separate lemma. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the well-typed tTrunc in S₀. (*tight: counterexample `ce_defaultRecoverable_drop_faithful`*)

**Non-vacuity.** Both sides hold on tZ = ↑(a - b) = z, whose default text a - b = z elides one coercion and two type arguments; both sides fail on tTrunc. (`nv_elabSys_ppDefault_eq_some_iff_defaultRecoverable`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:143-144
theorem ce_elabSys_ppDefault_drop_defaultRecoverable :
    ¬ DefaultRecoverable S₀ tTrunc ∧ elabSys S₀ (ppDefault tTrunc) ≠ some tTrunc := …
-- lean/Toy/Render/Counterexamples.lean:148-149
theorem ce_defaultRecoverable_drop_faithful :
    elabSys S₀ (ppDefault tTrunc) ≠ some tTrunc ∧ ¬ DefaultRecoverable S₀ tTrunc := …
-- lean/Toy/Render/Witnesses.lean:46-48
theorem nv_elabSys_ppDefault_eq_some_iff_defaultRecoverable :
    (elabSys S₀ (ppDefault tZ) = some tZ ∧ DefaultRecoverable S₀ tZ) ∧
      (elabSys S₀ (ppDefault tTrunc) ≠ some tTrunc ∧ ¬ DefaultRecoverable S₀ tTrunc) := …
```

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified. Relation to this card: Definition 1.2 asks for the round trip on all terms; this card characterizes the terms on which one fixed printer/reader pair has it.
- Lean 4 v4.34.1 (leanprover/lean4 commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Lean/PrettyPrinter/Delaborator/Options.lean: pp.explicit (default false, 'display implicit arguments'), pp.coercions (default true, described as 'hide coercion applications'; with the default, coercions are displayed as an up-arrow, not elided), pp.numericTypes (default false, 'display types of numeric literals'); src/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.lean: pp.analyze (default false, 'try to determine annotations sufficient to ensure round-tripping'); its module documentation says the analyzer 'is neither sound nor complete'. With pp.analyze enabled, this toolchain prints ((2 : Int) - 3 = 0) as 2 - 3 = 0 (build-checked observation in LeanObservations.lean). Modeling bridge (model–system relation: none proved): the toy models neither this printer nor the analyzer.
- Lean 4 v4.34.1 (leanprover/lean4 commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Lean/Elab/Extra.lean, module documentation of the binop%/binrel% elaborators: computes a 'maximal type' for an operator tree and inserts coercions in the 'leaves'. Modeling bridge (model–system relation: none proved): the toy's system elaborator places coercions at the operator, and its leaf-coercion reader cfgLeaves resembles the Lean rule.

**Design question.** For which terms is default text enough for the system elaborator? (Exactly the terms passing DefaultRecoverable; the card proves both directions.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Model–system relation: none proved. Lean v4.34.1 elaborates `fun (a b : Nat) (z : Int) => a - b = z` with default options as `↑a - ↑b = z` (coercions at the leaves; build-checked observation quoted under Applicability), which is the reading of the toy leaf-coercion reader `cfgLeaves`, not of the toy system elaborator `cfg0`. The characterization is about `cfg0`; it neither establishes nor refutes a characterization of the terms whose default Lean printing re-elaborates to themselves.

### Textual and term round trips

#### 4. `textual_round_trip_does_not_certify_term`

Tier T1 · kind: counterexample · depth: shallow · Lean: `textual_round_trip_passes_on_tTrunc_but_term_and_truth_change`

**Plain claim.** In S₀, the term tTrunc = ↑(a - b) = ↑a - ↑b at Int, with a b : Nat, has default text a - b = a - b; the system elaborator reads that text as the different term a - b = a - b at Nat, whose default text is again a - b = a - b; the re-read term is valid, while tTrunc is not valid and is false at a = 0, b = 1.

**Statement.**

```lean
-- lean/Toy/Render/Counterexamples.lean:54-57
theorem textual_round_trip_passes_on_tTrunc_but_term_and_truth_change :
    (elabSys S₀ (ppDefault tTrunc)).map ppDefault = some (ppDefault tTrunc) ∧
      elabSys S₀ (ppDefault tTrunc) = some tReread ∧ tReread ≠ tTrunc ∧
      Valid S₀ tReread ∧ ¬ Valid S₀ tTrunc ∧ ¬ Denote S₀ tTrunc ρ₀ := …
```

Unfolded statement of `textual_round_trip_passes_on_tTrunc_but_term_and_truth_change` (`elabSys` and `Valid` written out):

```lean
(elabWith cfg0 S₀ (ppDefault tTrunc)).map ppDefault = some (ppDefault tTrunc) ∧
  elabWith cfg0 S₀ (ppDefault tTrunc) = some tReread ∧ tReread ≠ tTrunc ∧
  (∀ ρ, Denote S₀ tReread ρ) ∧ ¬ (∀ ρ, Denote S₀ tTrunc ρ) ∧ ¬ Denote S₀ tTrunc ρ₀
```

**Hypothesis ledger.**

No hypotheses beyond the parameters: the statement is a closed proposition about concrete objects of the running signature `S₀`.

**Non-vacuity.** No hypotheses: a concrete statement about tTrunc and tReread in S₀.

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified.
- Robert Pollack, 'How to believe a machine-checked proof', in G. Sambin and J. M. Smith (eds.), Twenty-Five Years of Constructive Type Theory, Oxford University Press, 1998, pp. 205-220, DOI 10.1093/oso/9780198501275.003.0013; preprint BRICS Report Series RS-97-18 (1997), DOI 10.7146/brics.v4i18.18945. Section 3.1 'Reading the files': a reader sees a concrete representation (a string) while the checker uses an abstract syntax tree; unless their relationship is understood nothing the checker says can be believed, so a checker should support an official syntax that is parseable and printable.
- Mathlib linter.ppRoundtrip (leanprover-community/mathlib4 commit 3eae40f5eb25c5934211edf662d3b24c5afbe47a, Mathlib/Tactic/Linter/PPRoundtrip.lean, lines 124-147): for a command that produced no error messages, it formats the command's parsed, unelaborated Syntax with Lean.PrettyPrinter.ppCategory `command (Lean v4.34.1 src/Lean/PrettyPrinter.lean, lines 20-23: sanitize, parenthesize, format), normalizes whitespace in the formatted string and in the original source, and warns at the first difference. It does not elaborate to a kernel term, does not delaborate, and does not reparse the formatted string; annotations written in the source, such as (2 : Int), stay in the Syntax. It is a syntax-level format-and-compare check, not an instance of the elaborate-then-print round trip studied here. Relation to this card: a contrast, not an instance: annotations survive that check because no elaboration happens, whereas ppDefault after elaboration erases them.

**Design question.** Does 'elaborate, default-print, compare strings' certify a printed statement? (No: the strings can agree while the term and its truth change.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Model–system relation: none proved. With default options (`pp.coercions` true) Lean v4.34.1 displays coercions as `↑` (`fun a b => ↑(a - b) = ↑a - ↑b`), and with `pp.coercions` false it prints them as `.cast` applications (build-checked observations quoted under Applicability). In neither setting does the toy collision on `tTrunc` (which needs a printer that elides coercions) arise for that input. The counterexample is about the toy default printer, which elides coercions; it neither establishes nor refutes that an elaborate-print-compare check is unsound for Lean's printer.

#### 5. `textual_idempotence_necessary_for_faithfulness`

Tier T0 · kind: theorem · depth: definitional · Lean: `textual_round_trip_of_faithful`

**Plain claim.** For every configuration cfg, signature S, printer p : Tm → Stx and term t: if cfg reads p t back as t, then printing the re-read term with p gives back the text p t.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:56-57
theorem textual_round_trip_of_faithful (cfg : ElabCfg) (S : Sig) (p : Tm → Stx) (t : Tm)
    (h : elabWith cfg S (p t) = some t) : (elabWith cfg S (p t)).map p = some (p t) := …
```

**Hypothesis ledger.**

- `h : elabWith cfg S (p t) = some t` — Faithfulness of p on t. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: p = ppDefault under cfg0 on the ill-typed a ↔ a (a : Nat), whose default text does not elaborate. Within terms whose default text elaborates, h is not tight for p = ppDefault: the conclusion then holds without it (`textual_round_trip_holds_on_elaborating_ppDefault`). (*tight: counterexample `ce_textual_round_trip_drop_faithful`*)

**Non-vacuity.** p = ppDefault, cfg = cfg0, t = tZ: the default text of tZ is faithful. (`nv_textual_round_trip_of_faithful`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:155-157
theorem ce_textual_round_trip_drop_faithful :
    elabSys S₀ (ppDefault tIffNat) ≠ some tIffNat ∧
      (elabSys S₀ (ppDefault tIffNat)).map ppDefault ≠ some (ppDefault tIffNat) := …
-- lean/Toy/Render/Witnesses.lean:26
theorem nv_textual_round_trip_of_faithful : elabWith cfg0 S₀ (ppDefault tZ) = some tZ := …
```

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified.

**Design question.** What does a textual round trip check? (A necessary condition for faithfulness, which on annotation-free text holds whenever the text elaborates.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 6. `annotation_free_text_survives_textual_round_trip`

Tier T1 · kind: theorem · depth: shallow · Lean: `ppDefault_elabWith_of_annotationFree`

**Plain claim.** For every configuration cfg, signature S, text s and term t': if s contains no annotation tokens (s.annCount = 0) and cfg elaborates s to t', then the default printing of t' is s.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:63-64
theorem ppDefault_elabWith_of_annotationFree (cfg : ElabCfg) (S : Sig) (s : Stx) (t' : Tm)
    (hs : s.annCount = 0) (h : elabWith cfg S s = some t') : ppDefault t' = s := …
```

**Hypothesis ledger.**

- `hs : s.annCount = 0` — An annotated text such as (2 : Int) loses its annotation when default-printed. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the ascribed numeral text (2 : Int) under cfg0. (*tight: counterexample `ce_ppDefault_elabWith_drop_annotationFree`*)
- `h : elabWith cfg S s = some t'` — Without it t' is unrelated to s. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the annotation-free text of a ↔ a (a : Nat), which does not elaborate, paired with an unrelated numeral term. (*tight: counterexample `ce_ppDefault_elabWith_drop_elab`*)

**Non-vacuity.** The default text a - b = a - b of tTrunc is annotation-free and elaborates under cfg0 (to tReread). (`nv_ppDefault_elabWith_of_annotationFree`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:161-164
theorem ce_ppDefault_elabWith_drop_annotationFree :
    (Stx.asc (.num 2) .int).annCount ≠ 0 ∧
      elabSys S₀ (.asc (.num 2) .int) = some (.lit .int 2) ∧
      ppDefault (.lit .int 2) ≠ .asc (.num 2) .int := …
-- lean/Toy/Render/Counterexamples.lean:168-170
theorem ce_ppDefault_elabWith_drop_elab :
    (ppDefault tIffNat).annCount = 0 ∧ elabSys S₀ (ppDefault tIffNat) ≠ some (.lit .nat 0) ∧
      ppDefault (.lit .nat 0) ≠ ppDefault tIffNat := …
-- lean/Toy/Render/Witnesses.lean:30-31
theorem nv_ppDefault_elabWith_of_annotationFree :
    (ppDefault tTrunc).annCount = 0 ∧ elabWith cfg0 S₀ (ppDefault tTrunc) = some tReread := …
```

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified.
- Mathlib linter.ppRoundtrip (leanprover-community/mathlib4 commit 3eae40f5eb25c5934211edf662d3b24c5afbe47a, Mathlib/Tactic/Linter/PPRoundtrip.lean, lines 124-147): for a command that produced no error messages, it formats the command's parsed, unelaborated Syntax with Lean.PrettyPrinter.ppCategory `command (Lean v4.34.1 src/Lean/PrettyPrinter.lean, lines 20-23: sanitize, parenthesize, format), normalizes whitespace in the formatted string and in the original source, and warns at the first difference. It does not elaborate to a kernel term, does not delaborate, and does not reparse the formatted string; annotations written in the source, such as (2 : Int), stay in the Syntax. It is a syntax-level format-and-compare check, not an instance of the elaborate-then-print round trip studied here. Relation to this card: a contrast, not an instance: that linter compares source text with formatted unelaborated syntax, so it is not the elaborate-then-default-print check this card analyzes.

**Design question.** Why is a textual round trip on default text uninformative? (Every annotation-free text that elaborates passes it, under every configuration.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 7. `term_round_trip_determines_reading`

Tier T0 · kind: theorem · depth: definitional · Lean: `faithful_reading_unique_and_same_denotation`

**Plain claim.** For every configuration cfg, signature S, text r and term t: if cfg reads r as t (Faithful cfg S r t), then every term t' that cfg returns on r equals t and has the same denotation as t in every environment.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:74-76
theorem faithful_reading_unique_and_same_denotation (cfg : ElabCfg) (S : Sig) (r : Stx)
    (t : Tm) (h : Faithful cfg S r t) :
    ∀ t', elabWith cfg S r = some t' → t' = t ∧ ∀ ρ, (Denote S t' ρ ↔ Denote S t ρ) := …
```

Unfolded statement of `faithful_reading_unique_and_same_denotation` (`Faithful` written out):

```lean
∀ (cfg : ElabCfg) (S : Sig) (r : Stx) (t : Tm), elabWith cfg S r = some t →
  ∀ t', elabWith cfg S r = some t' → t' = t ∧ ∀ ρ, (Denote S t' ρ ↔ Denote S t ρ)
```

**Hypothesis ledger.**

- `h : Faithful cfg S r t` — The term round trip. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the default text of tTrunc under cfg0, which is read as a different term. (*tight: counterexample `ce_faithful_reading_drop_faithful`*)

**Non-vacuity.** The explicit text of tTrunc is faithful under cfg0. (`nv_faithful_reading_unique_and_same_denotation`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:175-177
theorem ce_faithful_reading_drop_faithful :
    ¬ Faithful cfg0 S₀ (ppDefault tTrunc) tTrunc ∧
      elabWith cfg0 S₀ (ppDefault tTrunc) = some tReread ∧ tReread ≠ tTrunc := …
-- lean/Toy/Render/Witnesses.lean:35-36
theorem nv_faithful_reading_unique_and_same_denotation :
    Faithful cfg0 S₀ (ppExplicit tTrunc) tTrunc := …
```

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified.
- Robert Pollack, 'How to believe a machine-checked proof', in G. Sambin and J. M. Smith (eds.), Twenty-Five Years of Constructive Type Theory, Oxford University Press, 1998, pp. 205-220, DOI 10.1093/oso/9780198501275.003.0013; preprint BRICS Report Series RS-97-18 (1997), DOI 10.7146/brics.v4i18.18945. Section 3.1 'Reading the files': a reader sees a concrete representation (a string) while the checker uses an abstract syntax tree; unless their relationship is understood nothing the checker says can be believed, so a checker should support an official syntax that is parseable and printable.
- Nils Anders Danielsson, 'Correct-by-construction pretty-printing', Proceedings of the 2013 ACM SIGPLAN Workshop on Dependently-Typed Programming (DTP '13), pp. 1-12, DOI 10.1145/2502409.2502410: pretty-printing and then parsing with the same unambiguous grammar returns the original value; it concerns concrete syntax and involves no elaboration.

**Design question.** What check identifies the term a printed statement denotes for a given reader? (The term round trip under that reader's elaborator.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

### The deletion-greedy printer

#### 8. `greedy_printer_faithful`

Tier T1 · kind: theorem · depth: shallow · Lean: `ppMin_faithful_of_wellTyped`

**Plain claim.** For every configuration cfg, signature S and term t: if t is well typed in S, then cfg reads the deletion-greedy rendering ppMin cfg S t back as t.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:85-86
theorem ppMin_faithful_of_wellTyped (cfg : ElabCfg) (S : Sig) (t : Tm)
    (ht : WellTyped S t) : Faithful cfg S (ppMin cfg S t) t := …
```

Unfolded statement of `ppMin_faithful_of_wellTyped` (`WellTyped` and `Faithful` written out):

```lean
∀ (cfg : ElabCfg) (S : Sig) (t : Tm), (∃ τ, tyOf S t = some τ) →
  elabWith cfg S (ppMin cfg S t) = some t
```

*Definition used (prose).* ppMin cfg S t shows exactly the annotation positions kept by minMask cfg S t, the deletion-greedy selection: start from all annotation positions of t (the explicit text), visit them in pre-order, and drop a position whenever cfg still reads the rendering without it back as t. The name abbreviates 'locally minimal'; it is not a minimum-size printer.

**Hypothesis ledger.**

- `ht : WellTyped S t` — The deletion search starts from the explicit text, which is proved faithful for well-typed terms (`explicit_printer_section_law`); without well-typedness the greedy rendering need not be faithful (see the counterexample). Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: an ill-typed variable term under cfg0. (*tight: counterexample `ce_ppMin_faithful_drop_wellTyped`*)

**Non-vacuity.** tTrunc is well typed and its default text is not faithful under cfg0, so ppMin must keep annotations. (`nv_ppMin_faithful_of_wellTyped`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:181-182
theorem ce_ppMin_faithful_drop_wellTyped :
    ¬ WellTyped S₀ tIll ∧ ¬ Faithful cfg0 S₀ (ppMin cfg0 S₀ tIll) tIll := …
-- lean/Toy/Render/Witnesses.lean:40-41
theorem nv_ppMin_faithful_of_wellTyped :
    WellTyped S₀ tTrunc ∧ ¬ Faithful cfg0 S₀ (ppDefault tTrunc) tTrunc := …
```

**Prior art.**

- Kevin Kappelmann, Maximilian Schäffeler, Lukas Stevens, Mohammad Abdulaziz, Andrei Popescu and Dmitriy Traytel, 'Type Annotations with Roundtrip Property', Archive of Formal Proofs, May 2026 (entry Printing_Parsing_Roundtrip), companion paper arXiv:2604.15713: complete and minimal type annotations for rank-one polymorphic λ-terms as printed by Isabelle, so that reparsing and type inference recover the term; mechanized in Isabelle/HOL; a reverse-greedy approach yields a locally minimal and complete annotation set. The closest mechanized prior art for the deletion-greedy printer here; its setting is Hindley-Milner type inference, not coercions and numeral defaults. Relation to this card: same shape of algorithm (greedy deletion checked by re-reading) in a different type system.
- Steffen Juilf Smolka and Jasmin Christian Blanchette, 'Robust, Semi-Intelligible Isabelle Proofs from ATP Proofs', PxTP 2013, EPiC Series in Computing 14, pp. 117-132, 2013, DOI 10.29007/zbdb: Isabelle proof reconstruction that provides enough type annotations for formulas to be parsed correctly without printing all types.
- Jasmin Christian Blanchette, Sascha Böhme, Mathias Fleury, Steffen Juilf Smolka and Albert Steckermeier, 'Semi-intelligible Isar proofs from machine-generated proofs', Journal of Automated Reasoning 56(2), pp. 155-200, 2016, DOI 10.1007/s10817-015-9335-3 (journal account of the same reconstruction work; cited as background, its annotation procedure is not compared here in detail).
- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified. Relation to this card: Section 8.1 falls back to the fully annotated printing as a whole; ppMin drops annotations one position at a time.
- Mark Adams, 'HOL Zero's Solutions for Pollack-Inconsistency', Interactive Theorem Proving (ITP 2016), LNCS 9807, pp. 20-35, Springer, 2016, DOI 10.1007/978-3-319-43144-4_2. Only the abstract was consulted: HOL Zero aims at well-behaved parsing/printing and Pollack-consistency, and annotates terms minimally with types for unambiguous printing.
- Lean 4 v4.34.1 (leanprover/lean4 commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Lean/PrettyPrinter/Delaborator/Options.lean: pp.explicit (default false, 'display implicit arguments'), pp.coercions (default true, described as 'hide coercion applications'; with the default, coercions are displayed as an up-arrow, not elided), pp.numericTypes (default false, 'display types of numeric literals'); src/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.lean: pp.analyze (default false, 'try to determine annotations sufficient to ensure round-tripping'); its module documentation says the analyzer 'is neither sound nor complete'. With pp.analyze enabled, this toolchain prints ((2 : Int) - 3 = 0) as 2 - 3 = 0 (build-checked observation in LeanObservations.lean). Modeling bridge (model–system relation: none proved): the toy models neither this printer nor the analyzer.

**Design question.** Can a certified rendering use fewer annotations than the explicit text? (Yes: greedy deletion checked by re-elaboration gives a faithful rendering; it is not minimum-size.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Model–system relation: none proved. Lean v4.34.1's option `pp.analyze` (default false) is documented as trying to determine annotations sufficient to ensure round-tripping and as neither sound nor complete; with `pp.analyze` true it prints `fun (a b : Nat) => ((a - b : Nat) : Int) = (a : Int) - (b : Int)` as `fun a b => ↑(a - b) = HSub.hSub (α := Int) ↑a ↑b`, and `((2 : Int) - 3 = 0)` as `2 - 3 = 0` (build-checked observations quoted under Applicability). The toy `ppMin` is a search checked by re-elaboration, not a model of that analyzer; this card neither establishes nor refutes faithfulness of `pp.analyze` output.

#### 9. `greedy_printer_locally_minimal`

Tier T1 · kind: theorem · depth: substantive · Lean: `ppMin_locally_minimal_of_wellTyped`

**Plain claim.** For every configuration cfg, signature S, term t and annotation position q: if t is well typed in S and q is kept by minMask cfg S t, then cfg reads ppMin cfg S t back as t, and cfg does not read back as t the rendering that shows the kept positions except q.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:97-100
theorem ppMin_locally_minimal_of_wellTyped (cfg : ElabCfg) (S : Sig) (t : Tm)
    (ht : WellTyped S t) (q : Path × AnnKind) (hq : q ∈ minMask cfg S t) :
    Faithful cfg S (ppMin cfg S t) t ∧
      ¬ Faithful cfg S (ppMask (maskOf ((minMask cfg S t).erase q)) [] t) t := …
```

Unfolded statement of `ppMin_locally_minimal_of_wellTyped` (`WellTyped` and `Faithful` written out):

```lean
∀ (cfg : ElabCfg) (S : Sig) (t : Tm), (∃ τ, tyOf S t = some τ) →
  ∀ q : Path × AnnKind, q ∈ minMask cfg S t →
    elabWith cfg S (ppMin cfg S t) = some t ∧
      ¬ elabWith cfg S (ppMask (maskOf ((minMask cfg S t).erase q)) [] t) = some t
```

*Definition used (prose).* ppMin cfg S t shows exactly the annotation positions kept by minMask cfg S t, the deletion-greedy selection: start from all annotation positions of t (the explicit text), visit them in pre-order, and drop a position whenever cfg still reads the rendering without it back as t. The name abbreviates 'locally minimal'; it is not a minimum-size printer.

**Hypothesis ledger.**

- `ht : WellTyped S t` — On ill-typed terms minMask can keep a position although ppMin itself is not faithful. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the ill-typed numeral lit Prop 0 under cfg0, for which minMask keeps one position. (*tight: counterexample `ce_ppMin_locally_minimal_drop_wellTyped`*)
- `hq : q ∈ minMask cfg S t` — Erasing a position that was not kept changes nothing. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the well-typed tTrunc under cfg0 with q the type argument of = (dropped by minMask). (*tight: counterexample `ce_ppMin_locally_minimal_drop_mem`*)

**Non-vacuity.** tTrunc is well typed and minMask cfg0 keeps the coercion on b (position [1, 1]). (`nv_ppMin_locally_minimal_of_wellTyped`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:424-429
theorem ce_ppMin_locally_minimal_drop_wellTyped :
    ¬ WellTyped S₀ tLitProp ∧ ([], AnnKind.numType) ∈ minMask cfg0 S₀ tLitProp ∧
      ¬ (Faithful cfg0 S₀ (ppMin cfg0 S₀ tLitProp) tLitProp ∧
        ¬ Faithful cfg0 S₀
          (ppMask (maskOf ((minMask cfg0 S₀ tLitProp).erase ([], .numType))) [] tLitProp)
          tLitProp) := …
-- lean/Toy/Render/Counterexamples.lean:435-439
theorem ce_ppMin_locally_minimal_drop_mem :
    WellTyped S₀ tTrunc ∧
      ¬ (Faithful cfg0 S₀ (ppMin cfg0 S₀ tTrunc) tTrunc ∧
        ¬ Faithful cfg0 S₀
          (ppMask (maskOf ((minMask cfg0 S₀ tTrunc).erase ([], .typeArg))) [] tTrunc) tTrunc) := …
-- lean/Toy/Render/Witnesses.lean:53-54
theorem nv_ppMin_locally_minimal_of_wellTyped :
    WellTyped S₀ tTrunc ∧ ([1, 1], AnnKind.coercion) ∈ minMask cfg0 S₀ tTrunc := …
```

**Prior art.**

- Kevin Kappelmann, Maximilian Schäffeler, Lukas Stevens, Mohammad Abdulaziz, Andrei Popescu and Dmitriy Traytel, 'Type Annotations with Roundtrip Property', Archive of Formal Proofs, May 2026 (entry Printing_Parsing_Roundtrip), companion paper arXiv:2604.15713: complete and minimal type annotations for rank-one polymorphic λ-terms as printed by Isabelle, so that reparsing and type inference recover the term; mechanized in Isabelle/HOL; a reverse-greedy approach yields a locally minimal and complete annotation set. The closest mechanized prior art for the deletion-greedy printer here; its setting is Hindley-Milner type inference, not coercions and numeral defaults. Relation to this card: the AFP entry also proves local minimality of a greedy annotation set.
- Steffen Juilf Smolka and Jasmin Christian Blanchette, 'Robust, Semi-Intelligible Isabelle Proofs from ATP Proofs', PxTP 2013, EPiC Series in Computing 14, pp. 117-132, 2013, DOI 10.29007/zbdb: Isabelle proof reconstruction that provides enough type annotations for formulas to be parsed correctly without printing all types.
- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified.

**Design question.** Can any single annotation shown by the greedy printer be dropped without losing the certificate? (No, on well-typed terms; this is minimality relative to the kept set, not minimum size.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 10. `greedy_printer_eq_default_when_default_faithful`

Tier T1 · kind: theorem · depth: shallow · Lean: `ppMin_eq_ppDefault_of_faithful_ppDefault`

**Plain claim.** For every configuration cfg, signature S and term t: if cfg reads the default text of t back as t, then ppMin cfg S t is the default text of t.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:111-112
theorem ppMin_eq_ppDefault_of_faithful_ppDefault (cfg : ElabCfg) (S : Sig) (t : Tm)
    (h : Faithful cfg S (ppDefault t) t) : ppMin cfg S t = ppDefault t := …
```

Unfolded statement of `ppMin_eq_ppDefault_of_faithful_ppDefault` (`Faithful` written out):

```lean
∀ (cfg : ElabCfg) (S : Sig) (t : Tm), elabWith cfg S (ppDefault t) = some t →
  ppMin cfg S t = ppDefault t
```

*Definition used (prose).* ppMin cfg S t shows exactly the annotation positions kept by minMask cfg S t, the deletion-greedy selection: start from all annotation positions of t (the explicit text), visit them in pre-order, and drop a position whenever cfg still reads the rendering without it back as t. The name abbreviates 'locally minimal'; it is not a minimum-size printer.

**Hypothesis ledger.**

- `h : Faithful cfg S (ppDefault t) t` — Otherwise some annotation must be kept. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the well-typed tTrunc under cfg0. (*tight: counterexample `ce_ppMin_eq_ppDefault_drop_faithful`*)

**Non-vacuity.** The default text of tZ is faithful under cfg0. (`nv_ppMin_eq_ppDefault_of_faithful_ppDefault`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:186-187
theorem ce_ppMin_eq_ppDefault_drop_faithful :
    ¬ Faithful cfg0 S₀ (ppDefault tTrunc) tTrunc ∧ ppMin cfg0 S₀ tTrunc ≠ ppDefault tTrunc := …
-- lean/Toy/Render/Witnesses.lean:58
theorem nv_ppMin_eq_ppDefault_of_faithful_ppDefault : Faithful cfg0 S₀ (ppDefault tZ) tZ := …
```

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified. Relation to this card: the combined printer of Section 8.1 also returns the normal output whenever re-reading it succeeds.

**Design question.** Does the greedy printer fall back to the default printer when default text already certifies the term? (Yes.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

### Readers with different elaborators

#### 11. `elaborator_family_agrees_on_fully_annotated_text`

Tier T1 · kind: theorem · depth: shallow · Lean: `elabWith_eq_elabSys_of_fullyAnnotated`, `elabWith_agreeOnFull`

**Plain claim.** For every configuration cfg (any numeral default, including Prop, and either coercion rule), signature S and text s: if s is fully annotated (every +, -, = carries a type argument and every numeral is directly ascribed), then cfg and the system elaborator return the same result on s.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:128-129
theorem elabWith_eq_elabSys_of_fullyAnnotated (cfg : ElabCfg) (S : Sig) (s : Stx)
    (hs : s.fullyAnnotated = true) : elabWith cfg S s = elabSys S s := …
-- lean/Toy/Render/Statements.lean:133
theorem elabWith_agreeOnFull (cfg : ElabCfg) : AgreeOnFull elabSys (elabWith cfg) := …
```

Unfolded statement of `elabWith_agreeOnFull` (AgreeOnFull and Reader written out):

```lean
∀ (cfg : ElabCfg) (S : Sig) (s : Stx), s.fullyAnnotated = true → elabWith cfg S s = elabSys S s
```

The rendering above is the type of `elabWith_eq_elabSys_of_fullyAnnotated` with the binder order unchanged; the two theorems state the same proposition in two forms.

**Hypothesis ledger.**

- `hs : s.fullyAnnotated = true` — Unannotated operators and numerals are where configurations differ. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the annotation-free default text a - b = z under the leaf-coercion configuration cfgLeaves. (*tight: counterexample `ce_elabWith_eq_elabSys_drop_fullyAnnotated`*)

**Non-vacuity.** The explicit text of tTrunc is fully annotated, and cfgLeaves reads it to a term, as the system elaborator does. (`nv_elabWith_eq_elabSys_of_fullyAnnotated`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:445-447
theorem ce_elabWith_eq_elabSys_drop_fullyAnnotated :
    (ppDefault tZ).fullyAnnotated = false ∧
      elabWith cfgLeaves S₀ (ppDefault tZ) ≠ elabSys S₀ (ppDefault tZ) := …
-- lean/Toy/Render/Witnesses.lean:64-67
theorem nv_elabWith_eq_elabSys_of_fullyAnnotated :
    (ppExplicit tTrunc).fullyAnnotated = true ∧
      elabWith cfgLeaves S₀ (ppExplicit tTrunc) = some tTrunc ∧
      elabSys S₀ (ppExplicit tTrunc) = some tTrunc := …
```

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified. Relation to this card: the failsafe printing of Section 8.1 prints type annotations everywhere so that it is trivially parsed correctly.
- Val Breazu-Tannen, Thierry Coquand, Carl A. Gunter and Andre Scedrov, 'Inheritance as implicit coercion', Information and Computation 93(1), pp. 172-221, 1991, DOI 10.1016/0890-5401(91)90055-7: coherence of a coercion semantics, i.e. independence of the meaning from the derivation chosen. The toy has a single coercion Nat → Int, so uniqueness of coercion paths is trivial here; the toy's coherence question is whether coercion insertion commutes with the overloaded operators.

**Design question.** Which readers read annotated text the same way? (In the toy, every configuration of the family, on fully annotated text.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 12. `explicit_text_faithful_for_every_agreeing_reader`

Tier T0 · kind: theorem · depth: shallow · Lean: `agreeing_reader_reads_ppExplicit`

**Plain claim.** For every signature S, term t and reader e' (any function from a signature and a text to an optional term): if t is well typed in S and, in every signature, e' returns the same result as the system elaborator on every fully annotated text, then e' reads the explicit text of t as t.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:139-140
theorem agreeing_reader_reads_ppExplicit (S : Sig) (t : Tm) (e' : Reader)
    (ht : WellTyped S t) (hag : AgreeOnFull elabSys e') : e' S (ppExplicit t) = some t := …
```

Unfolded statement of `agreeing_reader_reads_ppExplicit` (`Reader`, `WellTyped` and `AgreeOnFull` written out):

```lean
∀ (S : Sig) (t : Tm) (e' : Sig → Stx → Option Tm), (∃ τ, tyOf S t = some τ) →
  (∀ (S' : Sig) (s : Stx), s.fullyAnnotated = true → e' S' s = elabSys S' s) →
    e' S (ppExplicit t) = some t
```

**Hypothesis ledger.**

- `ht : WellTyped S t` — The section law needs it. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: an ill-typed variable term, with e' the system elaborator itself. (*tight: counterexample `ce_agreeing_reader_drop_wellTyped`*)
- `hag : AgreeOnFull elabSys e'` — Transfers the system elaborator's reading of fully annotated text to e'. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the reader that always returns none, which lies outside the configuration family (inside the family hag always holds, by `elaborator_family_agrees_on_fully_annotated_text`). (*tight: counterexample `ce_agreeing_reader_drop_agree`*)

**Non-vacuity.** tTrunc with the reader eLeavesOnNonFull, which agrees with the system elaborator on fully annotated text but reads the default text a - b = z differently. (`nv_agreeing_reader_reads_ppExplicit`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:192-194
theorem ce_agreeing_reader_drop_wellTyped :
    AgreeOnFull elabSys elabSys ∧ ¬ WellTyped S₀ tIll ∧
      elabSys S₀ (ppExplicit tIll) ≠ some tIll := …
-- lean/Toy/Render/Counterexamples.lean:199-201
theorem ce_agreeing_reader_drop_agree :
    WellTyped S₀ tTrunc ∧ ¬ AgreeOnFull elabSys (fun _ _ => none) ∧
      (fun (_ : Sig) (_ : Stx) => (none : Option Tm)) S₀ (ppExplicit tTrunc) ≠ some tTrunc := …
-- lean/Toy/Render/Witnesses.lean:78-80
theorem nv_agreeing_reader_reads_ppExplicit :
    WellTyped S₀ tTrunc ∧ AgreeOnFull elabSys eLeavesOnNonFull ∧
      eLeavesOnNonFull S₀ (ppDefault tZ) ≠ elabSys S₀ (ppDefault tZ) := …
```

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified. Relation to this card: Section 8.1 requires the adapted parser to read the failsafe output correctly; agreement on fully annotated text is the analogous assumption here.

**Design question.** What does full annotation buy for a reader whose elaborator differs from the system's? (A correct reading, provided the reader agrees with the system on fully annotated text.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 13. `faithfulness_is_reader_relative`

Tier T1 · kind: counterexample · depth: shallow · Lean: `default_and_min_texts_faithful_for_cfg0_but_not_other_readers`

**Plain claim.** In S₀: the default text a - b = z of tZ = ↑(a - b) = z is faithful for the system elaborator and equals ppMin cfg0 S₀ tZ, but the leaf-coercion reader reads it as ↑a - ↑b = z, which differs in truth from tZ at a = 0, b = 1, z = 0; the default text 2 - 3 = 0 of (2 : Nat) - 3 = 0 is faithful for the system elaborator and equals ppMin cfg0 of that term, but the Int-numeral reader reads it as (2 : Int) - 3 = 0, which is not valid while (2 : Nat) - 3 = 0 is; and the leaf-coercion and Int-numeral readers read the respective explicit texts back as the original terms.

**Statement.**

```lean
-- lean/Toy/Render/Counterexamples.lean:67-75
theorem default_and_min_texts_faithful_for_cfg0_but_not_other_readers :
    Faithful cfg0 S₀ (ppDefault tZ) tZ ∧ ppMin cfg0 S₀ tZ = ppDefault tZ ∧
      elabWith cfgLeaves S₀ (ppDefault tZ) = some tZLeaves ∧
      Denote S₀ tZ ρ₀ ∧ ¬ Denote S₀ tZLeaves ρ₀ ∧
      Faithful cfg0 S₀ (ppDefault tNatSub) tNatSub ∧ ppMin cfg0 S₀ tNatSub = ppDefault tNatSub ∧
      elabWith cfgIntNumerals S₀ (ppDefault tNatSub) = some tIntSub ∧
      Valid S₀ tNatSub ∧ ¬ Valid S₀ tIntSub ∧
      Faithful cfgLeaves S₀ (ppExplicit tZ) tZ ∧
      Faithful cfgIntNumerals S₀ (ppExplicit tNatSub) tNatSub := …
```

Unfolded statement of `default_and_min_texts_faithful_for_cfg0_but_not_other_readers` (`Faithful` and `Valid` written out):

```lean
elabWith cfg0 S₀ (ppDefault tZ) = some tZ ∧ ppMin cfg0 S₀ tZ = ppDefault tZ ∧
  elabWith cfgLeaves S₀ (ppDefault tZ) = some tZLeaves ∧
  Denote S₀ tZ ρ₀ ∧ ¬ Denote S₀ tZLeaves ρ₀ ∧
  elabWith cfg0 S₀ (ppDefault tNatSub) = some tNatSub ∧ ppMin cfg0 S₀ tNatSub = ppDefault tNatSub ∧
  elabWith cfgIntNumerals S₀ (ppDefault tNatSub) = some tIntSub ∧
  (∀ ρ, Denote S₀ tNatSub ρ) ∧ ¬ (∀ ρ, Denote S₀ tIntSub ρ) ∧
  elabWith cfgLeaves S₀ (ppExplicit tZ) = some tZ ∧
  elabWith cfgIntNumerals S₀ (ppExplicit tNatSub) = some tNatSub
```

**Hypothesis ledger.**

No hypotheses beyond the parameters: the statement is a closed proposition about concrete objects of the running signature `S₀`.

**Non-vacuity.** No hypotheses: concrete statements about tZ and tNatSub in S₀.

**Prior art.**

- Dmitriy Traytel, Stefan Berghofer and Tobias Nipkow, 'Extending Hindley-Milner type inference with coercive structural subtyping', APLAS 2011, LNCS 7078, pp. 89-104, Springer, 2011, DOI 10.1007/978-3-642-25318-8_10. Section 5.1: sin(n + n) with n : N, an overloaded + and real : N → R has the two type-correct completions sin(real(n + n)) and sin(real n + real n); the deterministic implementation picks the first, and the authors note that without coherence a system may silently prove a different theorem. Relation to this card: the operator-coercion and leaf-coercion readings of a - b = z are the toy counterparts of the two completions of sin(n + n).
- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified.
- Lean 4 v4.34.1 (leanprover/lean4 commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Lean/Elab/Extra.lean, module documentation of the binop%/binrel% elaborators: computes a 'maximal type' for an operator tree and inserts coercions in the 'leaves'. Modeling bridge (model–system relation: none proved): the toy's system elaborator places coercions at the operator, and its leaf-coercion reader cfgLeaves resembles the Lean rule.

**Design question.** Does a certificate computed against the system's elaborator certify the statement for a reader with a different elaborator? (No.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Model–system relation: none proved. The toy readers `cfg0` and `cfgLeaves` differ in coercion placement in the way that the documented `binop%` elaborator of Lean v4.34.1 (coercions inserted at the leaves of an operator tree) differs from a coerce-the-result strategy. Whether two real readers disagree on a given printed statement is a property of those readers; this card exhibits the phenomenon in the toy and neither establishes nor refutes it for any real pair of readers.

#### 14. `correct_annotations_monotone`

Tier T1 · kind: theorem · depth: substantive · Lean: `faithful_ppMask_mono`

**Plain claim.** For every configuration cfg, signature S, term t and masks m, m' (functions from a position and an annotation kind to Bool): if every position-kind pair selected by m is selected by m', and cfg reads back as t the rendering of t that shows the annotations selected by m, then cfg reads back as t the rendering of t that shows the annotations selected by m'.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:151-153
theorem faithful_ppMask_mono (cfg : ElabCfg) (S : Sig) (t : Tm) (m m' : Mask)
    (hle : ∀ p k, m p k = true → m' p k = true)
    (hf : Faithful cfg S (ppMask m [] t) t) : Faithful cfg S (ppMask m' [] t) t := …
```

Unfolded statement of `faithful_ppMask_mono` (`Faithful` and `Mask` written out):

```lean
∀ (cfg : ElabCfg) (S : Sig) (t : Tm) (m m' : List Nat → AnnKind → Bool),
  (∀ p k, m p k = true → m' p k = true) →
  elabWith cfg S (ppMask m [] t) = some t → elabWith cfg S (ppMask m' [] t) = some t
```

**Hypothesis ledger.**

- `hle : ∀ p k, m p k = true → m' p k = true` — Only annotations are added, none removed. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: tTrunc under cfg0 with m selecting everything and m' nothing. (*tight: counterexample `ce_faithful_ppMask_mono_drop_le`*)
- `hf : Faithful cfg S (ppMask m [] t) t` — The smaller rendering must already be faithful. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: tTrunc under cfg0 with m = m' selecting nothing. (*tight: counterexample `ce_faithful_ppMask_mono_drop_faithful`*)

**Non-vacuity.** From the single annotation 'coercion on b' (the faithful text a - b = a - ↑b) to all annotation positions of tTrunc, under cfg0. (`nv_faithful_ppMask_mono`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:205-208
theorem ce_faithful_ppMask_mono_drop_le :
    ¬ (∀ p k, (fun _ _ => true : Mask) p k = true → (fun _ _ => false : Mask) p k = true) ∧
      Faithful cfg0 S₀ (ppMask (fun _ _ => true) [] tTrunc) tTrunc ∧
      ¬ Faithful cfg0 S₀ (ppMask (fun _ _ => false) [] tTrunc) tTrunc := …
-- lean/Toy/Render/Counterexamples.lean:213-215
theorem ce_faithful_ppMask_mono_drop_faithful :
    (∀ p k, (fun _ _ => false : Mask) p k = true → (fun _ _ => false : Mask) p k = true) ∧
      ¬ Faithful cfg0 S₀ (ppMask (fun _ _ => false) [] tTrunc) tTrunc := …
-- lean/Toy/Render/Witnesses.lean:85-87
theorem nv_faithful_ppMask_mono :
    (∀ p k, maskOf [([1, 1], .coercion)] p k = true → maskOf (annPos [] tTrunc) p k = true) ∧
      Faithful cfg0 S₀ (ppMask (maskOf [([1, 1], .coercion)]) [] tTrunc) tTrunc := …
```

**Prior art.**

- Kevin Kappelmann, Maximilian Schäffeler, Lukas Stevens, Mohammad Abdulaziz, Andrei Popescu and Dmitriy Traytel, 'Type Annotations with Roundtrip Property', Archive of Formal Proofs, May 2026 (entry Printing_Parsing_Roundtrip), companion paper arXiv:2604.15713: complete and minimal type annotations for rank-one polymorphic λ-terms as printed by Isabelle, so that reparsing and type inference recover the term; mechanized in Isabelle/HOL; a reverse-greedy approach yields a locally minimal and complete annotation set. The closest mechanized prior art for the deletion-greedy printer here; its setting is Hindley-Milner type inference, not coercions and numeral defaults. Relation to this card: completeness of an annotation set (every superset also round-trips) is part of what the AFP entry establishes in its setting.
- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified.

**Design question.** Can adding correct annotations ever break a certified rendering? (No, for every configuration of the toy family.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 15. `wrong_type_annotation_changes_term`

Tier T1 · kind: counterexample · depth: shallow · Lean: `wrong_type_annotation_changes_term_tZ`

**Plain claim.** In S₀: adding the type argument Int to the - of the faithful default text a - b = z of tZ = ↑(a - b) = z gives a text with the same annotation-erased form, which the system elaborator reads without error as the well-typed ↑a - ↑b = z, a term different from tZ that differs from it in truth at a = 0, b = 1, z = 0.

**Statement.**

```lean
-- lean/Toy/Render/Counterexamples.lean:87-90
theorem wrong_type_annotation_changes_term_tZ :
    sWrongSub.erase = ppDefault tZ ∧ Faithful cfg0 S₀ (ppDefault tZ) tZ ∧
      elabSys S₀ sWrongSub = some tZLeaves ∧ WellTyped S₀ tZLeaves ∧ tZLeaves ≠ tZ ∧
      Denote S₀ tZ ρ₀ ∧ ¬ Denote S₀ tZLeaves ρ₀ := …
```

Unfolded statement of `wrong_type_annotation_changes_term_tZ` (`Faithful`, `elabSys` and `WellTyped` written out):

```lean
sWrongSub.erase = ppDefault tZ ∧ elabWith cfg0 S₀ (ppDefault tZ) = some tZ ∧
  elabWith cfg0 S₀ sWrongSub = some tZLeaves ∧ (∃ τ, tyOf S₀ tZLeaves = some τ) ∧ tZLeaves ≠ tZ ∧
  Denote S₀ tZ ρ₀ ∧ ¬ Denote S₀ tZLeaves ρ₀
```

**Hypothesis ledger.**

No hypotheses beyond the parameters: the statement is a closed proposition about concrete objects of the running signature `S₀`.

**Non-vacuity.** No hypotheses: concrete statement about tZ and sWrongSub in S₀.

**Prior art.**

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified.
- Dmitriy Traytel, Stefan Berghofer and Tobias Nipkow, 'Extending Hindley-Milner type inference with coercive structural subtyping', APLAS 2011, LNCS 7078, pp. 89-104, Springer, 2011, DOI 10.1007/978-3-642-25318-8_10. Section 5.1: sin(n + n) with n : N, an overloaded + and real : N → R has the two type-correct completions sin(real(n + n)) and sin(real n + real n); the deterministic implementation picks the first, and the authors note that without coherence a system may silently prove a different theorem.

**Design question.** Is it safe for a human to 'clarify' a printed statement by adding a plausible annotation? (No: a type-correct but wrong annotation silently changes the term.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

### δ-unfolded renderings

#### 16. `equal_delta_normal_forms_equal_evaluation`

Tier T0 · kind: theorem · depth: shallow · Lean: `eval_eq_of_deltaNF_eq`

**Plain claim.** For every signature S and terms t₁, t₂: if t₁ and t₂ have the same δ-normal form in S (every definition of S unfolded), then they evaluate to the same value in every environment.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:160-161
theorem eval_eq_of_deltaNF_eq (S : Sig) (t₁ t₂ : Tm) (h : deltaNF S t₁ = deltaNF S t₂) :
    ∀ ρ, eval S ρ t₁ = eval S ρ t₂ := …
```

Unfolded statement of `eval_eq_of_deltaNF_eq` (`deltaNF` and `eval` written out):

```lean
∀ (S : Sig) (t₁ t₂ : Tm), unfoldDefs S.defs t₁ = unfoldDefs S.defs t₂ →
  ∀ ρ, evalD S.defs ρ t₁ = evalD S.defs ρ t₂
```

`unfoldDefs`, `evalD` and the definitions they use are quoted verbatim under **Applicability**.

**Hypothesis ledger.**

- `h : deltaNF S t₁ = deltaNF S t₂` — The δ-check. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the closed terms (2 : Nat) - 3 = 0 and (2 : Int) - 3 = 0 in S₀. (*tight: counterexample `ce_eval_eq_drop_deltaNF`*)

**Non-vacuity.** The abbreviation P and its body a = b are distinct terms with the same δ-normal form in S₀. (`nv_eval_eq_of_deltaNF_eq`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:219-220
theorem ce_eval_eq_drop_deltaNF :
    deltaNF S₀ tNatSub ≠ deltaNF S₀ tIntSub ∧ eval S₀ ρ₀ tNatSub ≠ eval S₀ ρ₀ tIntSub := …
-- lean/Toy/Render/Witnesses.lean:96-97
theorem nv_eval_eq_of_deltaNF_eq :
    Tm.const 0 ≠ Tm.eq .nat vA vB ∧ deltaNF S₀ (.const 0) = deltaNF S₀ (.eq .nat vA vB) := …
```

**Prior art.**

- Robert Pollack, 'How to believe a machine-checked proof', in G. Sambin and J. M. Smith (eds.), Twenty-Five Years of Constructive Type Theory, Oxford University Press, 1998, pp. 205-220, DOI 10.1093/oso/9780198501275.003.0013; preprint BRICS Report Series RS-97-18 (1997), DOI 10.7146/brics.v4i18.18945. Section 1.1: to believe a checked theorem one must read its formal statement and the definitions used hereditarily in stating it; Section 3.3 'What theorem is it?': library definitions must mean what they informally claim.
- Paula Severi and Erik Poll, 'Pure type systems with definitions', LFCS '94, LNCS 813, pp. 316-328, Springer, 1994, DOI 10.1007/3-540-58140-5_30: pure type systems extended with definitions and a reduction that unfolds them.

**Design question.** Does equality of δ-normal forms show that an unfolded rendering means the same as the original? (It shows equal evaluation in every environment.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 17. `delta_check_incomplete`

Tier T0 · kind: counterexample · depth: shallow · Lean: `deltaNF_check_rejects_reordered_unfolded_rendering`

**Plain claim.** In S₀ (P := a = b, Q := z = 0, PQ := P ∧ Q): the system elaborator reads the unfolded, conjunct-swapped rendering z = 0 ∧ a = b as a term whose δ-normal form differs from that of PQ, and that term and PQ evaluate identically in every environment.

**Statement.**

```lean
-- lean/Toy/Render/Counterexamples.lean:103-105
theorem deltaNF_check_rejects_reordered_unfolded_rendering :
    elabSys S₀ rSwapped = some tSwapped ∧ deltaNF S₀ tSwapped ≠ deltaNF S₀ (.const 2) ∧
      ∀ ρ, eval S₀ ρ tSwapped = eval S₀ ρ (.const 2) := …
```

**Hypothesis ledger.**

No hypotheses beyond the parameters: the statement is a closed proposition about concrete objects of the running signature `S₀`.

**Non-vacuity.** No hypotheses: concrete statement about rSwapped and PQ in S₀.

**Prior art.**

- Robert Pollack, 'How to believe a machine-checked proof', in G. Sambin and J. M. Smith (eds.), Twenty-Five Years of Constructive Type Theory, Oxford University Press, 1998, pp. 205-220, DOI 10.1093/oso/9780198501275.003.0013; preprint BRICS Report Series RS-97-18 (1997), DOI 10.7146/brics.v4i18.18945. Section 1.1: to believe a checked theorem one must read its formal statement and the definitions used hereditarily in stating it; Section 3.3 'What theorem is it?': library definitions must mean what they informally claim.
- Paula Severi and Erik Poll, 'Pure type systems with definitions', LFCS '94, LNCS 813, pp. 316-328, Springer, 1994, DOI 10.1007/3-540-58140-5_30: pure type systems extended with definitions and a reduction that unfolds them.

**Design question.** Is the δ-normal-form check complete for unfolded renderings? (No.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

### Declarative elaboration and coherence

#### 18. `deterministic_elaborators_sound_for_declarative_elaboration`

Tier T1 · kind: theorem · depth: shallow · Lean: `elabE_sound`

**Plain claim.** For every configuration cfg, signature S, optional expected type exp, text s, term t and type τ: if elabE cfg S exp s returns (t, τ), then t is a declarative elaboration of s at τ (Elabs S s τ t, which allows a Nat → Int coercion at any node) and t has type τ.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:172-173
theorem elabE_sound (cfg : ElabCfg) (S : Sig) (exp : Option Ty) (s : Stx) (t : Tm) (τ : Ty)
    (h : elabE cfg S exp s = some (t, τ)) : Elabs S s τ t ∧ tyOf S t = some τ := …
```

Unfolded (prose): what `Elabs S s τ t` admits (the inductive is quoted under Applicability).

```text
Elabs S s τ t is the inductive predicate generated by the rules var, num, add, sub, eq, iff,
and, asc, coe, const and coeIns of the quoted inductive. A derivation applies one of the first ten
rules at each node of s and may apply coeIns to any Nat-typed result, wrapping it in a coercion at
type Int. An operator without a type
argument may be elaborated at any numeric type; an operator with type argument σ is elaborated at σ.
```

**Hypothesis ledger.**

- `h : elabE cfg S exp s = some (t, τ)` — The elaborator succeeded. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the variable text a with an unrelated numeral term at Nat in S₀. (*tight: counterexample `ce_elabE_sound_drop_elab`*)

**Non-vacuity.** The system elaborator on the default text of tZ. (`nv_elabE_sound`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:224-226
theorem ce_elabE_sound_drop_elab :
    elabE cfg0 S₀ none (.var 0) ≠ some (.lit .nat 5, .nat) ∧
      ¬ Elabs S₀ (.var 0) .nat (.lit .nat 5) := …
-- lean/Toy/Render/Witnesses.lean:101
theorem nv_elabE_sound : elabE cfg0 S₀ none (ppDefault tZ) = some (tZ, .prop) := …
```

**Prior art.**

- Val Breazu-Tannen, Thierry Coquand, Carl A. Gunter and Andre Scedrov, 'Inheritance as implicit coercion', Information and Computation 93(1), pp. 172-221, 1991, DOI 10.1016/0890-5401(91)90055-7: coherence of a coercion semantics, i.e. independence of the meaning from the derivation chosen. The toy has a single coercion Nat → Int, so uniqueness of coercion paths is trivial here; the toy's coherence question is whether coercion insertion commutes with the overloaded operators.
- Amokrane Saïbi, 'Typing algorithm in type theory with inheritance', POPL '97, pp. 292-301, ACM, 1997, DOI 10.1145/263699.263742: coercion inference for a type theory with inheritance.
- Dmitriy Traytel, Stefan Berghofer and Tobias Nipkow, 'Extending Hindley-Milner type inference with coercive structural subtyping', APLAS 2011, LNCS 7078, pp. 89-104, Springer, 2011, DOI 10.1007/978-3-642-25318-8_10. Section 5.1: sin(n + n) with n : N, an overloaded + and real : N → R has the two type-correct completions sin(real(n + n)) and sin(real n + real n); the deterministic implementation picks the first, and the authors note that without coherence a system may silently prove a different theorem.

**Design question.** Do the coherence results about the declarative judgment apply to the concrete readers? (Yes: every configuration returns one declarative elaboration.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 19. `coherence_when_every_subtraction_annotated`

Tier T1 · kind: theorem · depth: substantive · Lean: `elabs_coherent_of_subAnnotated`

**Plain claim.** For every signature S, text s, type τ and terms t₁, t₂: if every subtraction in s carries an explicit type argument (s.subAnnotated) and t₁ and t₂ are both declarative elaborations of s at τ, then t₁ and t₂ evaluate identically in every environment.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:179-181
theorem elabs_coherent_of_subAnnotated (S : Sig) (s : Stx) (τ : Ty) (t₁ t₂ : Tm)
    (hs : s.subAnnotated = true) (h₁ : Elabs S s τ t₁) (h₂ : Elabs S s τ t₂) :
    ∀ ρ, eval S ρ t₁ = eval S ρ t₂ := …
```

**Hypothesis ledger.**

- `hs : s.subAnnotated = true` — Fixes the type of every subtraction, the one operator that does not commute with Nat → Int. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the default text a - b = z with its operator-coercion and leaf-coercion elaborations. (*tight: counterexample `ce_elabs_coherent_drop_subAnnotated`*)
- `h₁ : Elabs S s τ t₁` — t₁ must be an elaboration of s. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: a closed term unrelated to s (in place of t₁), with t₂ a genuine elaboration. (*tight: counterexample `ce_elabs_coherent_of_subAnnotated_drop_elabs`*)
- `h₂ : Elabs S s τ t₂` — Symmetric to h1. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the same instance with the roles of t₁ and t₂ exchanged. (*tight: counterexample `ce_elabs_coherent_of_subAnnotated_drop_elabs`*)

**Non-vacuity.** The text a - b + a = z in which the subtraction carries the type argument Nat and nothing else is annotated is subtraction-annotated but neither subtraction-free nor fully annotated, and has two distinct elaborations. (`nv_elabs_coherent_of_subAnnotated`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:452-454
theorem ce_elabs_coherent_drop_subAnnotated :
    (ppDefault tZ).subAnnotated = false ∧ Elabs S₀ (ppDefault tZ) .prop tZ ∧
      Elabs S₀ (ppDefault tZ) .prop tZLeaves ∧ eval S₀ ρ₀ tZ ≠ eval S₀ ρ₀ tZLeaves := …
-- lean/Toy/Render/Counterexamples.lean:460-462
theorem ce_elabs_coherent_of_subAnnotated_drop_elabs :
    (ppDefault tAddOp).subAnnotated = true ∧ Elabs S₀ (ppDefault tAddOp) .prop tAddOp ∧
      eval S₀ ρ₀ tNatSub ≠ eval S₀ ρ₀ tAddOp := …
-- lean/Toy/Render/Witnesses.lean:120-127
theorem nv_elabs_coherent_of_subAnnotated :
    sSubAnnMixed.subAnnotated = true ∧ sSubAnnMixed.subFree = false ∧
      sSubAnnMixed.fullyAnnotated = false ∧
      Elabs S₀ sSubAnnMixed .prop
        (.eq .int (.add .int (.coe (.sub .nat vA vB)) (.coe vA)) vZ) ∧
      Elabs S₀ sSubAnnMixed .prop (.eq .int (.coe (.add .nat (.sub .nat vA vB) vA)) vZ) ∧
      Tm.eq .int (.add .int (.coe (.sub .nat vA vB)) (.coe vA)) vZ ≠
        Tm.eq .int (.coe (.add .nat (.sub .nat vA vB) vA)) vZ := …
```

**Prior art.**

- John C. Reynolds, 'Using category theory to design implicit conversions and generic operators', in N. D. Jones (ed.), Semantics-Directed Compiler Generation, LNCS 94, pp. 211-258, Springer, 1980, DOI 10.1007/3-540-10250-7_24: implicit conversions and generic operators organized so that conversions commute with the operators. Truncating Nat subtraction is the toy's operator that does not commute with Nat → Int.
- Val Breazu-Tannen, Thierry Coquand, Carl A. Gunter and Andre Scedrov, 'Inheritance as implicit coercion', Information and Computation 93(1), pp. 172-221, 1991, DOI 10.1016/0890-5401(91)90055-7: coherence of a coercion semantics, i.e. independence of the meaning from the derivation chosen. The toy has a single coercion Nat → Int, so uniqueness of coercion paths is trivial here; the toy's coherence question is whether coercion insertion commutes with the overloaded operators.
- Dmitriy Traytel, Stefan Berghofer and Tobias Nipkow, 'Extending Hindley-Milner type inference with coercive structural subtyping', APLAS 2011, LNCS 7078, pp. 89-104, Springer, 2011, DOI 10.1007/978-3-642-25318-8_10. Section 5.1: sin(n + n) with n : N, an overloaded + and real : N → R has the two type-correct completions sin(real(n + n)) and sin(real n + real n); the deterministic implementation picks the first, and the authors note that without coherence a system may silently prove a different theorem.

**Design question.** When does the choice of coercion placement stop mattering semantically in the toy? (Whenever every subtraction carries its type; this condition is sufficient, not necessary: `subAnnotated_not_necessary_for_coherence_int`, `subAnnotated_not_necessary_for_coherence_cancel`.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 20. `coherence_without_subtraction`

Tier T1 · kind: theorem · depth: shallow · Lean: `elabs_coherent_of_subFree`

**Plain claim.** For every signature S, text s, type τ and terms t₁, t₂: if s contains no subtraction and t₁ and t₂ are both declarative elaborations of s at τ, then t₁ and t₂ evaluate identically in every environment, wherever their coercions were inserted.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:190-192
theorem elabs_coherent_of_subFree (S : Sig) (s : Stx) (τ : Ty) (t₁ t₂ : Tm)
    (hs : s.subFree = true) (h₁ : Elabs S s τ t₁) (h₂ : Elabs S s τ t₂) :
    ∀ ρ, eval S ρ t₁ = eval S ρ t₂ := …
```

**Hypothesis ledger.**

- `hs : s.subFree = true` — Fixes the type of every subtraction, the one operator that does not commute with Nat → Int. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the default text a - b = z with its operator-coercion and leaf-coercion elaborations. (*tight: counterexample `ce_elabs_coherent_drop_subFree`*)
- `h₁ : Elabs S s τ t₁` — t₁ must be an elaboration of s. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: a closed term unrelated to s (in place of t₁), with t₂ a genuine elaboration. (*tight: counterexample `ce_elabs_coherent_of_subFree_drop_elabs`*)
- `h₂ : Elabs S s τ t₂` — Symmetric to h1. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the same instance with the roles of t₁ and t₂ exchanged. (*tight: counterexample `ce_elabs_coherent_of_subFree_drop_elabs`*)

**Non-vacuity.** The default text a + b = z is subtraction-free and has two distinct elaborations, ↑(a + b) = z and ↑a + ↑b = z. (`nv_elabs_coherent_of_subFree`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:232-234
theorem ce_elabs_coherent_drop_subFree :
    (ppDefault tZ).subFree = false ∧ Elabs S₀ (ppDefault tZ) .prop tZ ∧
      Elabs S₀ (ppDefault tZ) .prop tZLeaves ∧ eval S₀ ρ₀ tZ ≠ eval S₀ ρ₀ tZLeaves := …
-- lean/Toy/Render/Counterexamples.lean:247-249
theorem ce_elabs_coherent_of_subFree_drop_elabs :
    (ppDefault tAddOp).subFree = true ∧ Elabs S₀ (ppDefault tAddOp) .prop tAddOp ∧
      eval S₀ ρ₀ tNatSub ≠ eval S₀ ρ₀ tAddOp := …
-- lean/Toy/Render/Witnesses.lean:105-107
theorem nv_elabs_coherent_of_subFree :
    (ppDefault tAddOp).subFree = true ∧ Elabs S₀ (ppDefault tAddOp) .prop tAddOp ∧
      Elabs S₀ (ppDefault tAddOp) .prop tAddLeaves ∧ tAddOp ≠ tAddLeaves := …
```

**Prior art.**

- John C. Reynolds, 'Using category theory to design implicit conversions and generic operators', in N. D. Jones (ed.), Semantics-Directed Compiler Generation, LNCS 94, pp. 211-258, Springer, 1980, DOI 10.1007/3-540-10250-7_24: implicit conversions and generic operators organized so that conversions commute with the operators. Truncating Nat subtraction is the toy's operator that does not commute with Nat → Int.
- Val Breazu-Tannen, Thierry Coquand, Carl A. Gunter and Andre Scedrov, 'Inheritance as implicit coercion', Information and Computation 93(1), pp. 172-221, 1991, DOI 10.1016/0890-5401(91)90055-7: coherence of a coercion semantics, i.e. independence of the meaning from the derivation chosen. The toy has a single coercion Nat → Int, so uniqueness of coercion paths is trivial here; the toy's coherence question is whether coercion insertion commutes with the overloaded operators.

**Design question.** When does it not matter, semantically, how a reader inserts coercions? (Sufficient conditions: the text has no subtraction, or more generally every subtraction is annotated; neither condition is necessary: `subAnnotated_not_necessary_for_coherence_int`.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 21. `coherence_on_fully_annotated_syntax`

Tier T1 · kind: theorem · depth: shallow · Lean: `elabs_coherent_of_fullyAnnotated`

**Plain claim.** For every signature S, text s, type τ and terms t₁, t₂: if s is fully annotated (subtraction allowed) and t₁ and t₂ are both declarative elaborations of s at τ, then t₁ and t₂ evaluate identically in every environment.

**Statement.**

```lean
-- lean/Toy/Render/Statements.lean:198-200
theorem elabs_coherent_of_fullyAnnotated (S : Sig) (s : Stx) (τ : Ty) (t₁ t₂ : Tm)
    (hs : s.fullyAnnotated = true) (h₁ : Elabs S s τ t₁) (h₂ : Elabs S s τ t₂) :
    ∀ ρ, eval S ρ t₁ = eval S ρ t₂ := …
```

**Hypothesis ledger.**

- `hs : s.fullyAnnotated = true` — Fixes the type of every subtraction, the one operator that does not commute with Nat → Int. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the default text a - b = z with its operator-coercion and leaf-coercion elaborations. (*tight: counterexample `ce_elabs_coherent_drop_fullyAnnotated`*)
- `h₁ : Elabs S s τ t₁` — t₁ must be an elaboration of s. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: a closed term unrelated to s (in place of t₁), with t₂ a genuine elaboration. (*tight: counterexample `ce_elabs_coherent_of_fullyAnnotated_drop_elabs`*)
- `h₂ : Elabs S s τ t₂` — Symmetric to h1. Tight: there is a proved counterexample in which every other hypothesis holds and the conclusion fails; witness class: the same instance with the roles of t₁ and t₂ exchanged. (*tight: counterexample `ce_elabs_coherent_of_fullyAnnotated_drop_elabs`*)

**Non-vacuity.** @eq Int (2 : Int) z is fully annotated and has two distinct elaborations, (2 : Int) = z and ↑(2 : Nat) = z. (`nv_elabs_coherent_of_fullyAnnotated`)

Counterexample, witness and control statements (verbatim):

```lean
-- lean/Toy/Render/Counterexamples.lean:239-241
theorem ce_elabs_coherent_drop_fullyAnnotated :
    (ppDefault tZ).fullyAnnotated = false ∧ Elabs S₀ (ppDefault tZ) .prop tZ ∧
      Elabs S₀ (ppDefault tZ) .prop tZLeaves ∧ eval S₀ ρ₀ tZ ≠ eval S₀ ρ₀ tZLeaves := …
-- lean/Toy/Render/Counterexamples.lean:257-259
theorem ce_elabs_coherent_of_fullyAnnotated_drop_elabs :
    sTwoEqZ.fullyAnnotated = true ∧ Elabs S₀ sTwoEqZ .prop (.eq .int (.lit .int 2) vZ) ∧
      eval S₀ ρ₀ tNatSub ≠ eval S₀ ρ₀ (.eq .int (.lit .int 2) vZ) := …
-- lean/Toy/Render/Witnesses.lean:140-144
theorem nv_elabs_coherent_of_fullyAnnotated :
    sTwoEqZ.fullyAnnotated = true ∧
      Elabs S₀ sTwoEqZ .prop (.eq .int (.lit .int 2) vZ) ∧
      Elabs S₀ sTwoEqZ .prop (.eq .int (.coe (.lit .nat 2)) vZ) ∧
      Tm.eq .int (.lit .int 2) vZ ≠ Tm.eq .int (.coe (.lit .nat 2)) vZ := …
```

**Prior art.**

- John C. Reynolds, 'Using category theory to design implicit conversions and generic operators', in N. D. Jones (ed.), Semantics-Directed Compiler Generation, LNCS 94, pp. 211-258, Springer, 1980, DOI 10.1007/3-540-10250-7_24: implicit conversions and generic operators organized so that conversions commute with the operators. Truncating Nat subtraction is the toy's operator that does not commute with Nat → Int.
- Val Breazu-Tannen, Thierry Coquand, Carl A. Gunter and Andre Scedrov, 'Inheritance as implicit coercion', Information and Computation 93(1), pp. 172-221, 1991, DOI 10.1016/0890-5401(91)90055-7: coherence of a coercion semantics, i.e. independence of the meaning from the derivation chosen. The toy has a single coercion Nat → Int, so uniqueness of coercion paths is trivial here; the toy's coherence question is whether coercion insertion commutes with the overloaded operators.

**Design question.** Is full annotation enough to make the meaning independent of a reader that inserts coercions freely? (Yes in the toy.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

#### 22. `default_text_incoherent`

Tier T1 · kind: counterexample · depth: shallow · Lean: `default_text_incoherent_operator_vs_leaf_coercion`

**Plain claim.** In S₀: the default text a - b = z has two declarative elaborations, ↑(a - b) = z (returned by the system elaborator) and ↑a - ↑b = z (returned by the leaf-coercion reader), which differ in truth at a = 0, b = 1, z = 0.

**Statement.**

```lean
-- lean/Toy/Render/Counterexamples.lean:114-118
theorem default_text_incoherent_operator_vs_leaf_coercion :
    Elabs S₀ (ppDefault tZ) .prop tZ ∧ Elabs S₀ (ppDefault tZ) .prop tZLeaves ∧
      elabSys S₀ (ppDefault tZ) = some tZ ∧
      elabWith cfgLeaves S₀ (ppDefault tZ) = some tZLeaves ∧
      Denote S₀ tZ ρ₀ ∧ ¬ Denote S₀ tZLeaves ρ₀ := …
```

**Hypothesis ledger.**

No hypotheses beyond the parameters: the statement is a closed proposition about concrete objects of the running signature `S₀`.

**Non-vacuity.** No hypotheses: concrete statement about the default text of tZ in S₀.

**Prior art.**

- Dmitriy Traytel, Stefan Berghofer and Tobias Nipkow, 'Extending Hindley-Milner type inference with coercive structural subtyping', APLAS 2011, LNCS 7078, pp. 89-104, Springer, 2011, DOI 10.1007/978-3-642-25318-8_10. Section 5.1: sin(n + n) with n : N, an overloaded + and real : N → R has the two type-correct completions sin(real(n + n)) and sin(real n + real n); the deterministic implementation picks the first, and the authors note that without coherence a system may silently prove a different theorem.
- John C. Reynolds, 'Using category theory to design implicit conversions and generic operators', in N. D. Jones (ed.), Semantics-Directed Compiler Generation, LNCS 94, pp. 211-258, Springer, 1980, DOI 10.1007/3-540-10250-7_24: implicit conversions and generic operators organized so that conversions commute with the operators. Truncating Nat subtraction is the toy's operator that does not commute with Nat → Int.
- Val Breazu-Tannen, Thierry Coquand, Carl A. Gunter and Andre Scedrov, 'Inheritance as implicit coercion', Information and Computation 93(1), pp. 172-221, 1991, DOI 10.1016/0890-5401(91)90055-7: coherence of a coercion semantics, i.e. independence of the meaning from the derivation chosen. The toy has a single coercion Nat → Int, so uniqueness of coercion paths is trivial here; the toy's coherence question is whether coercion insertion commutes with the overloaded operators.
- Lean 4 v4.34.1 (leanprover/lean4 commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Lean/Elab/Extra.lean, module documentation of the binop%/binrel% elaborators: computes a 'maximal type' for an operator tree and inserts coercions in the 'leaves'. Modeling bridge (model–system relation: none proved): the toy's system elaborator places coercions at the operator, and its leaf-coercion reader cfgLeaves resembles the Lean rule.

**Design question.** Why does default text fail to fix the meaning across readers? (Coercion placement is not coherent around an unannotated truncating subtraction.)

Basis: execution (Lean kernel check) — every Lean declaration named in this card.

Basis: derived (modeling bridge) — Model–system relation: none proved. Lean v4.34.1 with default options elaborates `fun (a b : Nat) (z : Int) => a - b = z` as `↑a - ↑b = z` (build-checked observation quoted under Applicability), the toy leaf-coercion reading. The toy incoherence is between two readers of the toy; it neither establishes nor refutes that Lean's elaborator is incoherent in any sense.

## Boundaries

### Non-claims

For each result, what it does not show. Names in code format are quoted verbatim in this report (results cited here that are not cards are quoted at the end of this section).

#### Non-claims of 1. `default_printer_collision_changes_truth`

- Does not say that default text is usually ambiguous: one collision is exhibited; how often collisions occur in any real corpus is not examined.
- Does not say that every reader misreads 2 - 3 = 0: the system elaborator reads it as the Nat statement (`default_and_min_texts_faithful_for_cfg0_but_not_other_readers`); the impossibility is that no single reader returns both terms.
- Escape hatch: a printer that shows an annotation separating the two terms defeats the impossibility (positive control `ppExplicit_separates_natSub_intSub`).
- Does not formalize Pollack-inconsistency: the toy has no proof system, so the collision is a toy analogue of one Pollack-axiom in the sense of Wiedijk (2012, Definition 1.4), not a derivation of a contradiction (Definition 1.5).
- Text in this package is a parsed syntax tree (Stx), not a character string. That Lean v4.34.1 prints both statements as 2 - 3 = 0 by default is a separate build-checked observation (LeanObservations.lean), not a consequence of this theorem.

#### Non-claims of 2. `explicit_printer_section_law`

- Does not say the explicit text is the shortest faithful text: on tTrunc the deletion-greedy rendering ppMin cfg0 has 1 annotation token versus 6 (`annCount_overhead_examples`).
- Does not say the explicit text is faithful for readers outside the configuration family; for an arbitrary reader, agreement with the system elaborator on fully annotated text suffices (`agreeing_reader_reads_ppExplicit`).
- Does not cover variable binder types: the typing context is assumed to be shared by writer and reader.

#### Non-claims of 3. `default_faithful_iff_default_recoverable`

- DefaultRecoverable is specific to the system elaborator cfg0; it says nothing about other configurations (`faithfulness_is_reader_relative`).
- DefaultRecoverable does not admit a coercion wherever a Nat-typed subterm meets an expected Int: the coerced subterm must still come out at type Nat when elaborated at expected Int, which excludes coerced numerals and coerced unannotated numeral arithmetic (`not_defaultRecoverable_tCoeTwoEqZ`: ↑(2 : Nat) = z, whose default text 2 = z re-reads as (2 : Int) = z; `not_defaultRecoverable_tCoeNumSub`: ↑((2 : Nat) - 3) = z, whose default text re-reads as (2 : Int) - 3 = z, which differs from it in truth at ρ₀).
- An operator whose two operand hints are none takes the expected numeric type (`defaultRecoverable_tAddIntNumEqZ`: (2 : Int) + 3 = z is default-recoverable).
- Does not say default-recoverable terms are common or rare.

#### Non-claims of 4. `textual_round_trip_does_not_certify_term`

- Does not say textual round trips never detect anything: they fail when the text does not elaborate (`ce_textual_round_trip_drop_faithful`), and for a printer that shows annotations they can fail when the elaborator inserts an annotation the text lacked (`ppCoercions_textual_round_trip_fails`).
- Lean v4.34.1 shows coercions by default (as an up-arrow), so this exact collision does not arise there with default options; that is a build-checked observation, not part of this result.
- Mathlib's linter.ppRoundtrip is not an instance of this check: it formats unelaborated syntax and compares strings, without elaboration or delaboration (see prior art).
- Does not quantify how often a textual round trip passes while the term changes.

#### Non-claims of 5. `textual_idempotence_necessary_for_faithfulness`

- The converse is false: textual idempotence does not imply faithfulness (`textual_round_trip_does_not_certify_term`).
- A failed textual round trip refutes faithfulness (the contrapositive of this theorem). For annotation-free text a passed textual round trip carries no information beyond the fact that the text elaborates: every annotation-free text that elaborates passes it (`annotation_free_text_survives_textual_round_trip`, `textual_round_trip_holds_on_elaborating_ppDefault`).

#### Non-claims of 6. `annotation_free_text_survives_textual_round_trip`

- Its hypothesis is that the text is annotation-free; it says nothing about annotated text, and for a printer that shows annotations the textual round trip can fail (`ppCoercions_textual_round_trip_fails`, on an ill-typed term).
- Does not say the re-read term t' is the term the text was printed from (`textual_round_trip_does_not_certify_term`).

#### Non-claims of 7. `term_round_trip_determines_reading`

- The certificate is relative to the reader cfg: it says nothing about a reader with a different configuration (`faithfulness_is_reader_relative`).
- It identifies the term, not that the statement says what a human intended.
- Decidability of Faithful (a Decidable instance in Defs.lean) is not part of this theorem.

#### Non-claims of 8. `greedy_printer_faithful`

- Guaranteed faithful for the reader cfg it was computed against; it neither establishes nor refutes faithfulness for other configurations, which can fail (`default_and_min_texts_faithful_for_cfg0_but_not_other_readers`: ppMin cfg0 S₀ tZ is the default text a - b = z, which cfgLeaves reads as a different term) or still hold (`ppMin_cfg0_tEqAB_faithful_for_all_cfg`: ppMin cfg0 S₀ tEqAB is faithful for every configuration, and ppMin cfg0 S₀ tTrunc is faithful for cfgIntNumerals).
- Not a minimum-size rendering: `ppMin_not_globally_minimal_cfg0` (under cfg0, 2 annotations kept where a faithful 1-annotation rendering exists) and `ppMin_not_globally_minimal_on_tTrunc_cfgLeaves`.
- The kept set depends on the visiting order (`visiting_order_changes_kept_set_on_tTrunc`).
- The rendering may read oddly to a human: for tTrunc under cfg0 it is a - b = a - ↑b.
- Annotation tokens on the running examples (default / ppMin cfg0 / explicit): tTrunc 0/1/6, tZ 0/0/3, tIntSub 0/1/5, tNatSub 0/0/5 (`annCount_overhead_examples`); ppMin cfgLeaves: 2, 1, 1, 0 and ppMin cfgIntNumerals: 1, 0, 0, 1 (`annCount_overhead_examples_other_readers`).
- ppMin models a search over annotation subsets checked by re-elaboration; it does not model Lean's pp.analyze, which is heuristic and does not add a numeral type to (2 : Int) - 3 = 0 (LeanObservations.lean).

#### Non-claims of 9. `greedy_printer_locally_minimal`

- Minimality here is local: dropping q is tested against the remaining kept set. A kept position need not be shown by every faithful rendering (`ppMin_kept_position_not_globally_necessary`: on ↑a = ↑b, two other single-position renderings are faithful), and ppMin is not minimum-size (`ppMin_not_globally_minimal_cfg0`).
- Dropping several kept positions at once is not stated here (not proved here; it would follow from `correct_annotations_monotone`).
- The proof uses `correct_annotations_monotone` and the fact that annotation positions are pairwise distinct.

#### Non-claims of 10. `greedy_printer_eq_default_when_default_faithful`

- ppMin does not start from the default text: minMask starts from all annotation positions (the explicit text) and deletes; this card says the deletions reach the default text when that text is faithful.
- The converse fails: on the ill-typed tIll, ppMin returns the default text although it is not faithful (`ppMin_eq_ppDefault_converse_false_on_tIll`).
- Does not say the default text is faithful for other readers.
- The proof uses `correct_annotations_monotone`.

#### Non-claims of 11. `elaborator_family_agrees_on_fully_annotated_text`

- 'Fully annotated' does not require coercions to be printed.
- Full annotation is not needed for every configuration to read a given text as the intended term: the rendering of (2 : Int) - 3 = 0 that shows its two type arguments and no other annotation is read as that term by every configuration (`partial_annotation_faithful_for_every_configuration`).
- Does not cover readers outside this toy family.

#### Non-claims of 12. `explicit_text_faithful_for_every_agreeing_reader`

- Agreement on fully annotated text is an assumption about the reader; nothing here establishes it for a real reader.
- Does not say full annotation is required. A text r is read as t by every reader agreeing with the system elaborator on fully annotated text iff r is fully annotated and the system elaborator reads it as t (`read_by_all_agreeing_readers_iff`), but the same equivalence holds for any predicate in place of full annotation (`read_by_all_readers_agreeing_on_pred_iff`), because such readers are unconstrained elsewhere; for the configuration family, partial annotation can suffice (`partial_annotation_faithful_for_every_configuration`).

#### Non-claims of 13. `faithfulness_is_reader_relative`

- Two concrete readers and two terms; no frequency claim.
- Both readers agree with the system elaborator on fully annotated text (`elaborator_family_agrees_on_fully_annotated_text`); the disagreement is confined to unannotated operators and numerals.
- Coherent text can also fail the term round trip for another reader: the subtraction-free default text a + b = z is read differently by cfg0 and cfgLeaves although both readings agree in value (`subFree_term_round_trip_fails_across_readers`, `coherence_without_subtraction`).

#### Non-claims of 14. `correct_annotations_monotone`

- Only annotations that t actually carries are added: ppMask prints t's own types and coercions. A type-correct but wrong annotation can change the reading (`wrong_type_annotation_changes_term`).
- The Lean source has no order relation on Mask; the hypothesis hle is stated pointwise.

#### Non-claims of 15. `wrong_type_annotation_changes_term`

- Does not say every added annotation is dangerous: annotations that t actually carries preserve faithfulness (`correct_annotations_monotone`).
- One example; no frequency claim.

#### Non-claims of 16. `equal_delta_normal_forms_equal_evaluation`

- Equal evaluation is a coarse equivalence: all valid propositions evaluate alike (`eval_equivalence_identifies_distinct_valid_terms`); it is not syntactic or definitional equality.
- The converse fails: equal evaluation does not imply equal δ-normal form (`delta_check_incomplete`).
- No well-typedness of definitions is assumed, and with ill-typed definitions δ-unfolding need not preserve typing (`deltaNF_not_wellTyped_of_illTyped_defs`).
- Names not defined in the signature are left unchanged by deltaNF.

#### Non-claims of 17. `delta_check_incomplete`

- Does not say equal evaluation is decidable in general; it is proved here for one pair.
- Does not prescribe what a checker should do when the δ-check fails (not examined).
- Equal evaluation is coarse (`eval_equivalence_identifies_distinct_valid_terms`).

#### Non-claims of 18. `deterministic_elaborators_sound_for_declarative_elaboration`

- Not completeness: Elabs admits the elaboration ↑(2 : Nat) = z of the fully annotated @eq Int (2 : Int) z, which no configuration returns (`elabs_not_complete_for_elabWith`).

#### Non-claims of 19. `coherence_when_every_subtraction_annotated`

- Coherence is semantic: the two elaborations can be different terms, so the term round trip across readers can still fail (`subFree_term_round_trip_fails_across_readers`).
- Not claimed for languages with other operators or other coercions (not examined).
- s.subAnnotated = true is sufficient, not necessary, for coherence: the unannotated texts z - z = z (whose subtraction is forced to Int by its operands; `subAnnotated_not_necessary_for_coherence_int`) and a - a = z (with the two distinct declarative elaborations ↑(a - a) = z and ↑a - ↑a = z, which evaluate identically because truncated subtraction gives a - a = 0; `subAnnotated_not_necessary_for_coherence_cancel`) have subAnnotated = false, and all of their declarative elaborations evaluate identically in every environment.

#### Non-claims of 20. `coherence_without_subtraction`

- Depth: an immediate corollary of `coherence_when_every_subtraction_annotated`.
- Coherence is semantic: the two elaborations are different terms, so the term round trip across readers can still fail (`subFree_term_round_trip_fails_across_readers`).
- Not claimed for languages with other operators or other coercions (not examined).
- s.subFree = true is sufficient, not necessary, for coherence: the text z - z = z contains a subtraction, and all of its declarative elaborations evaluate identically in every environment (`subAnnotated_not_necessary_for_coherence_int`).

#### Non-claims of 21. `coherence_on_fully_annotated_syntax`

- Depth: an immediate corollary of `coherence_when_every_subtraction_annotated`.
- Does not say fully annotated syntax has a unique elaboration term: @eq Int (2 : Int) z has two (`nv_elabs_coherent_of_fullyAnnotated`).
- s.fullyAnnotated = true is sufficient, not necessary, for coherence: the texts z - z = z and a - a = z are not fully annotated, and all of their declarative elaborations evaluate identically in every environment (`subAnnotated_not_necessary_for_coherence_int`, `subAnnotated_not_necessary_for_coherence_cancel`).

#### Non-claims of 22. `default_text_incoherent`

- Does not say every default text is incoherent: subtraction-free text is coherent (`coherence_without_subtraction`), and so is any text whose subtractions are annotated (`coherence_when_every_subtraction_annotated`).

### Escape hatches

- `default_printer_collision_changes_truth` (the impossibility) concerns one printer, the default printer, which elides every annotation. A printer that shows an annotation distinguishing the two terms defeats it: the positive control `ppExplicit_separates_natSub_intSub` shows that the system elaborator reads the explicit text of each term back as that term. The impossibility also concerns a single reader returning both terms; it does not prevent a reader from returning either one of them (the system elaborator returns `tNatSub` on `2 - 3 = 0`).

### Tightness status

Every hypothesis of every card is recorded as `tight`, with a proved counterexample in which all other hypotheses hold and the conclusion fails; the witness class is stated in each ledger. No hypothesis is recorded as `harmless` or `unknown`. Tightness is relative to the stated witness class: for `h : elabWith cfg S (p t) = some t` in `textual_idempotence_necessary_for_faithfulness`, the witness is a text that does not elaborate, and within terms whose default text elaborates the conclusion holds without `h` for `p = ppDefault` (`textual_round_trip_holds_on_elaborating_ppDefault`).

### Known not to apply (proved)

- Global minimality of `ppMin`: `ppMin_not_globally_minimal_cfg0` and `ppMin_not_globally_minimal_on_tTrunc_cfgLeaves`.
- Necessity of each kept position across all faithful renderings: `ppMin_kept_position_not_globally_necessary`.
- Independence of the kept set from the visiting order: `visiting_order_changes_kept_set_on_tTrunc`.
- The converse of `ppMin_eq_ppDefault_of_faithful_ppDefault`: `ppMin_eq_ppDefault_converse_false_on_tIll`.
- Completeness of the configuration family for the declarative judgment: `elabs_not_complete_for_elabWith`.
- Preservation of typing by δ-unfolding when definitions are ill typed: `deltaNF_not_wellTyped_of_illTyped_defs`.
- Equal evaluation as a fine equivalence: `eval_equivalence_identifies_distinct_valid_terms`.
- Necessity of `subAnnotated`, `subFree` or `fullyAnnotated` for coherence: `subAnnotated_not_necessary_for_coherence_int` and `subAnnotated_not_necessary_for_coherence_cancel`.
- Necessity of full annotation for reading a text as the intended term under every configuration: `partial_annotation_faithful_for_every_configuration` and `ppDefault_tEqAB_faithful_for_named_readers`.

### Candidate statement not adopted as a result

'A text is read as the intended term by every reader that agrees with the system elaborator on fully annotated text only if the text is fully annotated.' The Lean theorem `read_by_all_agreeing_readers_iff` proves the corresponding equivalence, but it is the instance `P = fullyAnnotated`, `f = elabSys` of `read_by_all_readers_agreeing_on_pred_iff`, which holds for every predicate `P` on texts, because a reader that agrees with `f` on the texts satisfying `P` is unconstrained on the others. It therefore says nothing specific about annotation, and it is recorded as a definitional remark rather than as a card. For the configuration family, partial annotation can make a text read as the intended term by every configuration (`partial_annotation_faithful_for_every_configuration`).

### Not examined

- Frequencies of collisions, of default-recoverable terms or of reader disagreement in any corpus of statements.
- Languages with other operators, other coercions, coercion chains, binders inside statements, polymorphism or type classes.
- Character-level printing and parsing (lexing, precedence, parentheses, notation).
- Real printers and elaborators beyond the build-checked observations of Lean v4.34.1 under **Applicability**; those observations concern the named inputs and options and neither establish nor refute claims about other inputs, options or versions. The deletion-greedy printer is compared with no real printer.

### Results cited in non-claims and boundaries (verbatim)

```lean
-- lean/Toy/Render/Counterexamples.lean:43
theorem valid_tReread : Valid S₀ tReread := …
-- lean/Toy/Render/Counterexamples.lean:48
theorem not_valid_tTrunc : ¬ Valid S₀ tTrunc := …
-- lean/Toy/Render/Counterexamples.lean:128-131
theorem ppDefault_tEqAB_faithful_for_named_readers :
    (ppDefault tEqAB).fullyAnnotated = false ∧ Faithful cfg0 S₀ (ppDefault tEqAB) tEqAB ∧
      Faithful cfgIntNumerals S₀ (ppDefault tEqAB) tEqAB ∧
      Faithful cfgLeaves S₀ (ppDefault tEqAB) tEqAB := …
-- lean/Toy/Render/Counterexamples.lean:270-273
theorem ppMin_not_globally_minimal_cfg0 :
    WellTyped S₀ tCoeZeroEqZero ∧ (ppMin cfg0 S₀ tCoeZeroEqZero).annCount = 2 ∧
      Faithful cfg0 S₀ (ppMask (maskOf [([0], .coercion)]) [] tCoeZeroEqZero) tCoeZeroEqZero ∧
      (ppMask (maskOf [([0], .coercion)]) [] tCoeZeroEqZero).annCount = 1 := …
-- lean/Toy/Render/Counterexamples.lean:279-282
theorem ppMin_not_globally_minimal_on_tTrunc_cfgLeaves :
    WellTyped S₀ tTrunc ∧ (ppMin cfgLeaves S₀ tTrunc).annCount = 2 ∧
      Faithful cfgLeaves S₀ (ppMask (maskOf [([0], .coercion)]) [] tTrunc) tTrunc ∧
      (ppMask (maskOf [([0], .coercion)]) [] tTrunc).annCount = 1 := …
-- lean/Toy/Render/Counterexamples.lean:291-294
theorem ppMin_kept_position_not_globally_necessary :
    WellTyped S₀ tCoeEqCoe ∧ minMask cfg0 S₀ tCoeEqCoe = [([1], .coercion)] ∧
      Faithful cfg0 S₀ (ppMask (maskOf [([0], .coercion)]) [] tCoeEqCoe) tCoeEqCoe ∧
      Faithful cfg0 S₀ (ppMask (maskOf [([], .typeArg)]) [] tCoeEqCoe) tCoeEqCoe := …
-- lean/Toy/Render/Counterexamples.lean:306-309
theorem visiting_order_changes_kept_set_on_tTrunc :
    minMask cfg0 S₀ tTrunc = [([1, 1], .coercion)] ∧
      minMaskRev cfg0 S₀ tTrunc = [([1], .typeArg)] ∧
      Faithful cfg0 S₀ (ppMask (maskOf (minMaskRev cfg0 S₀ tTrunc)) [] tTrunc) tTrunc := …
-- lean/Toy/Render/Counterexamples.lean:315-316
theorem ppMin_eq_ppDefault_converse_false_on_tIll :
    ppMin cfg0 S₀ tIll = ppDefault tIll ∧ ¬ Faithful cfg0 S₀ (ppDefault tIll) tIll := …
-- lean/Toy/Render/Counterexamples.lean:325-328
theorem partial_annotation_faithful_for_every_configuration :
    (ppWith (fun k => decide (k = .typeArg)) tIntSub).fullyAnnotated = false ∧
      (ppWith (fun k => decide (k = .typeArg)) tIntSub).annCount = 2 ∧
      ∀ cfg : ElabCfg, Faithful cfg S₀ (ppWith (fun k => decide (k = .typeArg)) tIntSub) tIntSub := …
-- lean/Toy/Render/Counterexamples.lean:337-340
theorem read_by_all_readers_agreeing_on_pred_iff (P : Sig → Stx → Bool) (f : Reader)
    (S : Sig) (r : Stx) (t : Tm) :
    (∀ e' : Reader, (∀ S' s', P S' s' = true → e' S' s' = f S' s') → e' S r = some t) ↔
      (P S r = true ∧ f S r = some t) := …
-- lean/Toy/Render/Counterexamples.lean:354-356
theorem read_by_all_agreeing_readers_iff (S : Sig) (r : Stx) (t : Tm) :
    (∀ e' : Reader, AgreeOnFull elabSys e' → e' S r = some t) ↔
      (r.fullyAnnotated = true ∧ elabSys S r = some t) := …
-- lean/Toy/Render/Counterexamples.lean:362-365
theorem subFree_term_round_trip_fails_across_readers :
    (ppDefault tAddOp).subFree = true ∧ Faithful cfg0 S₀ (ppDefault tAddOp) tAddOp ∧
      elabWith cfgLeaves S₀ (ppDefault tAddOp) = some tAddLeaves ∧
      ¬ Faithful cfgLeaves S₀ (ppDefault tAddOp) tAddOp := …
-- lean/Toy/Render/Counterexamples.lean:371-373
theorem elabs_not_complete_for_elabWith :
    Elabs S₀ sTwoEqZ .prop (.eq .int (.coe (.lit .nat 2)) vZ) ∧
      ∀ cfg : ElabCfg, elabWith cfg S₀ sTwoEqZ ≠ some (.eq .int (.coe (.lit .nat 2)) vZ) := …
-- lean/Toy/Render/Counterexamples.lean:386-388
theorem ppCoercions_textual_round_trip_fails :
    elabSys S₀ (ppCoercions tIllEq) = some (.eq .int (.coe vA) vZ) ∧
      (elabSys S₀ (ppCoercions tIllEq)).map ppCoercions ≠ some (ppCoercions tIllEq) := …
-- lean/Toy/Render/Counterexamples.lean:398-400
theorem deltaNF_not_wellTyped_of_illTyped_defs :
    WellTyped S_illDef (.const 0) ∧ ¬ WellTyped S_illDef (deltaNF S_illDef (.const 0)) ∧
      elabSys S_illDef (ppExplicit (deltaNF S_illDef (.const 0))) = none := …
-- lean/Toy/Render/Counterexamples.lean:408-411
theorem eval_equivalence_identifies_distinct_valid_terms :
    tZeroEqZero ≠ tReread ∧ tZeroEqZero ≠ tNatSub ∧
      (∀ ρ, eval S₀ ρ tZeroEqZero = eval S₀ ρ tReread) ∧
      (∀ ρ, eval S₀ ρ tZeroEqZero = eval S₀ ρ tNatSub) := …
-- lean/Toy/Render/Counterexamples.lean:472-474
theorem textual_round_trip_holds_on_elaborating_ppDefault (cfg : ElabCfg) (S : Sig)
    (t t' : Tm) (helab : elabWith cfg S (ppDefault t) = some t') :
    (elabWith cfg S (ppDefault t)).map ppDefault = some (ppDefault t) := …
-- lean/Toy/Render/Remarks.lean:24-27
theorem subAnnotated_not_necessary_for_coherence_int :
    sZZSub.subAnnotated = false ∧ sZZSub.subFree = false ∧ sZZSub.fullyAnnotated = false ∧
    Elabs S₀ sZZSub .prop (.eq .int (.sub .int vZ vZ) vZ) ∧
    ∀ τ t₁ t₂, Elabs S₀ sZZSub τ t₁ → Elabs S₀ sZZSub τ t₂ → ∀ ρ, eval S₀ ρ t₁ = eval S₀ ρ t₂ := …
-- lean/Toy/Render/Remarks.lean:84-89
theorem subAnnotated_not_necessary_for_coherence_cancel :
    sAASub.subAnnotated = false ∧ sAASub.subFree = false ∧ sAASub.fullyAnnotated = false ∧
    Elabs S₀ sAASub .prop (.eq .int (.coe (.sub .nat vA vA)) vZ) ∧
    Elabs S₀ sAASub .prop (.eq .int (.sub .int (.coe vA) (.coe vA)) vZ) ∧
    Tm.eq .int (.coe (.sub .nat vA vA)) vZ ≠ Tm.eq .int (.sub .int (.coe vA) (.coe vA)) vZ ∧
    ∀ τ t₁ t₂, Elabs S₀ sAASub τ t₁ → Elabs S₀ sAASub τ t₂ → ∀ ρ, eval S₀ ρ t₁ = eval S₀ ρ t₂ := …
-- lean/Toy/Render/Remarks.lean:136-140
theorem ppMin_cfg0_tEqAB_faithful_for_all_cfg :
    WellTyped S₀ tEqAB ∧
    (∀ cfg : ElabCfg, Faithful cfg S₀ (ppMin cfg0 S₀ tEqAB) tEqAB) ∧
    cfgIntNumerals ≠ cfg0 ∧
    Faithful cfgIntNumerals S₀ (ppMin cfg0 S₀ tTrunc) tTrunc := …
-- lean/Toy/Render/Witnesses.lean:152-160
theorem annCount_overhead_examples :
    ((ppDefault tTrunc).annCount, (ppMin cfg0 S₀ tTrunc).annCount,
        (ppExplicit tTrunc).annCount) = (0, 1, 6) ∧
      ((ppDefault tZ).annCount, (ppMin cfg0 S₀ tZ).annCount, (ppExplicit tZ).annCount) =
        (0, 0, 3) ∧
      ((ppDefault tIntSub).annCount, (ppMin cfg0 S₀ tIntSub).annCount,
        (ppExplicit tIntSub).annCount) = (0, 1, 5) ∧
      ((ppDefault tNatSub).annCount, (ppMin cfg0 S₀ tNatSub).annCount,
        (ppExplicit tNatSub).annCount) = (0, 0, 5) := …
-- lean/Toy/Render/Witnesses.lean:165-171
theorem annCount_overhead_examples_other_readers :
    ((ppMin cfgLeaves S₀ tTrunc).annCount, (ppMin cfgLeaves S₀ tZ).annCount,
      (ppMin cfgLeaves S₀ tIntSub).annCount, (ppMin cfgLeaves S₀ tNatSub).annCount) =
        (2, 1, 1, 0) ∧
      ((ppMin cfgIntNumerals S₀ tTrunc).annCount, (ppMin cfgIntNumerals S₀ tZ).annCount,
        (ppMin cfgIntNumerals S₀ tIntSub).annCount, (ppMin cfgIntNumerals S₀ tNatSub).annCount) =
        (1, 0, 0, 1) := …
```

## Evidence

**Kernel check.** Every result, counterexample, witness and remark is a theorem of the Lean library under `lean/`, checked by the Lean kernel when the library is built. Basis: execution (Lean kernel check).

The library builds with `lake build` under `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) with no errors. Lean sources contain no `sorry`, `admit`, `native_decide`, `implemented_by`, `@[extern]` or `unsafe`, and no `axiom` or `opaque` declarations. An axiom audit with `Lean.collectAxioms` over all 874 declarations of the library's modules (including compiler-generated auxiliary declarations) finds no axioms other than `propext`, `Classical.choice` and `Quot.sound`; the per-declaration record is `audit/axioms.json`.

**Statement and closure hashes.** For every Lean name referenced by a card in `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean` and hypothesis `counterexample`s; `lean_names` lists the further declarations quoted in this report), `audit/statements.json` records the SHA-256 of the statement (the Lean `repr` of its type) and of its definition closure (the sorted list of `name : type := value` for every package constant reachable from the statement, theorem bodies excluded). The table lists them with the axioms of each declaration ("none" means no axioms).

| Lean name | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :-- | :-- | :-- | :-- |
| `AgreeOnFull` | propext | `0a3e857a5959f52a10018bae956e607e29a9c2f8c4b3030a003f98399225ad84` | `a99c60b1302fb2cc84c293f31c510ae63063f9bfbea201e724e1f2278964f9f6` (30) |
| `AnnKind` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `CoeRule` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Def` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `DefaultRecoverable` | propext | `df7f77eca0cfb29cfae719f7b5139feb5c6ff1192dd6606a5591f759e75657eb` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `Denote` | propext | `77e983acc293749d12bfbba0dfafe8213c143c64b28cd8d40f5ecf424356cb71` | `b7aaab9cb773a418f92bc136defd254ac5ebfee7c7b50ac106a3b5fcb4c73e45` (20) |
| `ElabCfg` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Elabs` | none | `b886789ea2949075999f9fe74b247b28f2873064deb2384a704aed0553b66739` | `0eb0a7e06a6c5386ef591c1b503a46b9905b38741be62af228f857406e0d1cb9` (29) |
| `Env` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Faithful` | propext | `ad5c18c593897f76ee4695f3e0fc1ed69cfc0931bfccddfbd39b9ee9b927e81f` | `963bebad62c053cc58ebaefeda492e86b9b1210a7de2fb91ba5c58c83bf58637` (34) |
| `Mask` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Path` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Reader` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `S_illDef` | none | `51c6630041d4242796542d61950c8213ffc77b1392a00c0562047a8bc7f4bcaa` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `Sig` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Sig.constTy` | none | `cce831e3b417384726cbdd4d7d25ac620f813354aa0c653997c25dada9267df7` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `Sig.varTy` | none | `826d62867ad7efe8205ca0cefa16c65c86903de84e71c475ee6eb2629a676b50` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `Stx` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Stx.annCount` | none | `bb869b0191c28738e89a47b05b266551c552352a65721d78342b4470f32de0db` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `Stx.erase` | none | `efc8c5fbe28b4c6234b9f70fd51df3ccdef03b71b7287ccdec782f70bfda441b` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `Stx.fullyAnnotated` | propext | `c98452dbf7fc5a55b7ed8f53eed508705f4768c258ef054622d85144ad8ab139` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `Stx.subAnnotated` | none | `c98452dbf7fc5a55b7ed8f53eed508705f4768c258ef054622d85144ad8ab139` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `Stx.subFree` | none | `c98452dbf7fc5a55b7ed8f53eed508705f4768c258ef054622d85144ad8ab139` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `S₀` | none | `51c6630041d4242796542d61950c8213ffc77b1392a00c0562047a8bc7f4bcaa` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `Tm` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Ty` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Ty.isNum` | none | `1b99f97ca45af020ac087e2334e181348574ddbe0c4633188b7144e010791205` | `24b75290190d70e3616d04a90f1819b7e19d190a96381df18c33097908f73405` (4) |
| `Ty.max` | propext | `fa6b1520de2cbfe64570191f7767cdbd277e2910ae5208fc8ff7291198249b1a` | `24b75290190d70e3616d04a90f1819b7e19d190a96381df18c33097908f73405` (4) |
| `Val` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Val.toBool` | propext | `a2e1bdb00545cb53dde1e19aff36a6daa3febbb7fee66bf6ed6338f022753991` | `1e1805282c156e7556785d75cafa15f70600a03284349c93342f2da105c46e53` (4) |
| `Val.toInt` | propext | `280089eb39e69aabcf01fbc5d940a752ec6a9f7b888507b17758b3d026646a5f` | `1e1805282c156e7556785d75cafa15f70600a03284349c93342f2da105c46e53` (4) |
| `Val.toNat` | propext | `bc2e7db82566e633ef20c2d90f566693e6e7784593990e898ebe130ca7573743` | `1e1805282c156e7556785d75cafa15f70600a03284349c93342f2da105c46e53` (4) |
| `Valid` | propext | `df7f77eca0cfb29cfae719f7b5139feb5c6ff1192dd6606a5591f759e75657eb` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `WellTyped` | none | `df7f77eca0cfb29cfae719f7b5139feb5c6ff1192dd6606a5591f759e75657eb` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `agreeOnFull_refl` | propext | `9c4d5075d6b537ea37c0fd64cc302670a2a9937dd3f021148f3298d4583ff165` | `fef4601cddbb6f815d3bdba7886d6d58af55b1900246038b68ec0072c1e0896a` (93) |
| `agreeing_reader_reads_ppExplicit` | propext | `81bb000f3a1249e8d7500528e4007e3e77633c595148594ffc260f23abc30f43` | `a70d5a7cf69fc5ca107c4f261cf40d96ccefc211b1a6302c33ce53de9af21a7d` (113) |
| `annCount_overhead_examples` | Quot.sound, propext | `fae40643217a405d946439c5681d9d83816297246cd47a29f39319fa8b2ee2bc` | `07901ca41744510835b44aface74d906ab8aa4432c65369837a6b5f5a486dc10` (152) |
| `annCount_overhead_examples_other_readers` | Quot.sound, propext | `2d754f1e3ddb0f4f1c306a3f1b7eb3b12368302bdc605a663bb9239b0655c180` | `45089f29c0d31fc71c2d9946daf87ea041f3bb808caefc056affb9a79b802b1f` (150) |
| `annPos` | none | `eea4ff0b028dbc020b389adeefb258aa3799d7ac5440e0c140f1a2f7ace59bc9` | `c50f5181807568f34c9907346c35d44ab62c57ebd13edbbc875de8a9e2b12447` (19) |
| `ce_agreeing_reader_drop_agree` | propext | `73dae8f46436424e3fe2661971441683d0cf793c5539e9c0e1590efaf6d66c5f` | `a32a5e766eecb3f7e720977848c22c133907ac2abd3a82cd6125c04a0392198d` (118) |
| `ce_agreeing_reader_drop_wellTyped` | propext | `7106a457553b568787a3cc559b940228ae42fa4e7a68c55867aecedd04fa7942` | `2218651f96b8ea34fc852c2bf9a5193de52bced049b2116ac228d9ffd0010959` (118) |
| `ce_defaultRecoverable_drop_faithful` | propext | `db2fb68c97505426a92f6a99b8205be242c7f6c0d82c0509a2e7dc371272278c` | `205a0bbc1431c6e3d97650a1a7e8c1985ab4f0a1c5a4d90cd251d5e3f1d5029a` (117) |
| `ce_elabE_sound_drop_elab` | propext | `c1989eaece9083cba2f3ef4a18694a0ae0edf87cca8dbb12af04b8e6492e7b31` | `fd4c0a0a4fef842e6eb3f3f228c627cf529c02a899703d200f6f2ce0f1e67135` (100) |
| `ce_elabSys_ppDefault_drop_defaultRecoverable` | propext | `10c1f92faef7f3f4996b2d761385bab1ec2f0419fe5c35a8d4061e78a1e712fa` | `205a0bbc1431c6e3d97650a1a7e8c1985ab4f0a1c5a4d90cd251d5e3f1d5029a` (117) |
| `ce_elabWith_eq_elabSys_drop_fullyAnnotated` | propext | `40489beaa03ffe17b5311c8b035765fef92c9ebf37f0fefe4ba08c9d443c8a7d` | `1eef9d2afe8068263ea08a77f01f5d3de70571ec8865a326e55f8de024c06f15` (114) |
| `ce_elabWith_ppExplicit_drop_wellTyped` | propext | `b1a52425e50b0a3efbf02e8e4ead53a382ba507625d471d80b7139f6372b66e0` | `bcdc83de3e8c79a2ba1975ee7451bdfce15473531692a33f74b2fe64fb3fa180` (110) |
| `ce_elabs_coherent_drop_fullyAnnotated` | propext | `e791266d92e6ad3ebd5fa8745095ee0ff67099b90ea043ae888c045d9eb7c811` | `020a948bd2d02584e745df615b114e3cb1206355a66eb9a7b78793319b49fd85` (120) |
| `ce_elabs_coherent_drop_subAnnotated` | propext | `0aab0e5535c71bd2c4e00bbee11aa871f87526987a1a32b5cec7e9e9845a253e` | `4306a8c4a8588adb2bfcd6432d4f5d0703b88ee8af51675debc09fa23fe86aa0` (118) |
| `ce_elabs_coherent_drop_subFree` | propext | `56447616611e99f3d16d9cad85f417fa9257f6380474f86d7c400af1aca2f185` | `2158049653d48132acc000217c1c924e1ff1f47625dd601f0ef5d6bea12a6d4a` (118) |
| `ce_elabs_coherent_of_fullyAnnotated_drop_elabs` | propext | `ba65f4f533d9558412b618a7dd8132f85f5cea43dd6fd39c322ee6b37fa9704e` | `f912bdcda175a2f83f7aa89185b44495e0fbbde0a6975c1bd8703dc7eb30bd0d` (109) |
| `ce_elabs_coherent_of_subAnnotated_drop_elabs` | propext | `ce8290d40650287e0fc6388052aab51f07e5357ee0a897e54ef9b50f46ece53c` | `8ae245d32cb2e212f20ff1f6c33ab3fb0a352cb1d31853cb4ddfc1c5c527dede` (118) |
| `ce_elabs_coherent_of_subFree_drop_elabs` | propext | `ec8ec1b57487afc2724d310b868a5b458333655a8761a4059e221a9cfe06b4fe` | `1b8e85a33dbc4a13349056f5579ca9327db6cd614c5e08a8552f38cc8075b7ef` (118) |
| `ce_eval_eq_drop_deltaNF` | propext | `7186db5c63b9ed59871e0be1c10e80dfea3ebfe1c62dbb4c1977a8d8e81c36d6` | `70f2c089dde5eb13a68e2f78ea871ebbf3367b3b7f897e927df1f8bd07621a2b` (71) |
| `ce_faithful_ppMask_mono_drop_faithful` | propext | `86943ab5043bd5afebc56d1cef74cd11435956bc1515c94630d2a43eda2f7891` | `588095d0f2fa793e0308531cd3fe3a5841241439a5f3e1bb9945e1ddeda1f64d` (105) |
| `ce_faithful_ppMask_mono_drop_le` | propext | `b15c09990d75877e5ae1d998a6944b5d62434dbb93ccbfac94bcc90852b0ff26` | `588095d0f2fa793e0308531cd3fe3a5841241439a5f3e1bb9945e1ddeda1f64d` (105) |
| `ce_faithful_reading_drop_faithful` | propext | `60b6c3bb4e91901d363fb8a12704fee0eb34b691926d906702c6afb809369b55` | `233740ac7067093e1241cdb59487b1d91249dfb314d2c8f184db5d01540c0646` (108) |
| `ce_ppDefault_elabWith_drop_annotationFree` | propext | `544d21f06bcb5fdb8d8fbbe8a8c9c65e9753c23e3e08282e69b14dc77da116d1` | `231aa615a8e9f3987f752604054bbb8e76070087dfe424d8d9a9d7df23e814bf` (109) |
| `ce_ppDefault_elabWith_drop_elab` | propext | `6332598a3414f335598f9d52798bb7bcc794100bfce5e577438722867278bfaf` | `5c8b18dfa5c8dbd346bfe79e5e45411540fb6c6ff9a380954ea313339c86878f` (110) |
| `ce_ppMin_eq_ppDefault_drop_faithful` | Quot.sound, propext | `c439e86156a331a774ffcd713c11d3fee9e4cf03eb4922fe78da300f12b84d8f` | `013c59e9727bc72894a9cc521722a45d68a879861d540898a646d255f0d95144` (147) |
| `ce_ppMin_faithful_drop_wellTyped` | Quot.sound, propext | `e1852d0ec2c4b526c054c127a6da493589f7a6987e795d9988675cee97811a1f` | `28a34450ed2c751a5ca73aa7aef80e6008d2b1250e7097206f70c8955be26640` (149) |
| `ce_ppMin_locally_minimal_drop_mem` | Quot.sound, propext | `6c64e3f62f50fc65d3dcfcf42864f929a5028981382a5de039f189a966cd2f8c` | `ef23c2ec539385b7eef20c84ab10515467b0a7ed1f411e77ff2a4e6d16671dec` (149) |
| `ce_ppMin_locally_minimal_drop_wellTyped` | Quot.sound, propext | `1f71a6a1ab6504323260c47f52c6510c793ad9e8f2d9c10efb603e7c9afa08ff` | `9afbd7a17657f0af3ca946df12a44e613dc7db6a496b298b0164ce977e814872` (149) |
| `ce_textual_round_trip_drop_faithful` | propext | `2c67cffbf97566925ba72cf4c0e4d3ebfc3fc21811f7742d01b411edc2d9d45e` | `737f628fb368ca80d450781a7cf2b1ca873a33f0c540d300e9dbcc9217c53bb9` (108) |
| `cfg0` | none | `c9ca26e589cd56b30018b0364c705435aa9c3e3513e768ac841fb694f01501bd` | `017e49cfea971d7180a07db664039de4f5f58b707837614d488efcd0a5fe1068` (9) |
| `cfgIntNumerals` | none | `c9ca26e589cd56b30018b0364c705435aa9c3e3513e768ac841fb694f01501bd` | `017e49cfea971d7180a07db664039de4f5f58b707837614d488efcd0a5fe1068` (9) |
| `cfgLeaves` | none | `c9ca26e589cd56b30018b0364c705435aa9c3e3513e768ac841fb694f01501bd` | `017e49cfea971d7180a07db664039de4f5f58b707837614d488efcd0a5fe1068` (9) |
| `cfgPropNumerals` | none | `c9ca26e589cd56b30018b0364c705435aa9c3e3513e768ac841fb694f01501bd` | `017e49cfea971d7180a07db664039de4f5f58b707837614d488efcd0a5fe1068` (9) |
| `coerceTo` | none | `0549094058d90607771bd83ac5c5b389b5e69a575aded90c192a14aff8705c88` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `ctxLookup` | none | `da02fe3eed8b4f0755a309ef953ee2d095ed4427411ba31582e0e13d363d7895` | `24b75290190d70e3616d04a90f1819b7e19d190a96381df18c33097908f73405` (4) |
| `defRec` | propext | `1ba42e1c84ea9a98b328741d036ee91c3129fc6efafea501925937f38da6e154` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `defaultRecoverable_of_elabSys_ppDefault` | Quot.sound, propext | `bfc2a06696dbe960b69804b51402b1c96fc7dd9b41031ef0d601fb2e34d61981` | `1400c57d7ea028aaf88ce349b1dc03434cbb32c6e86ea2567bbda26f98bb39b8` (112) |
| `defaultRecoverable_tAddIntNumEqZ` | propext | `e74e4375f02b5bf27d322791ccfc89dc22e610bf4944436d43e4c1a174cb29ea` | `d11411322dcbb8d973e358f687ada346f5952d97ee3e0acfa8d81be172ffb038` (117) |
| `defaultRecoverable_tZ` | propext | `c412e94d603afcb835fa18241e565aff550078808401c1f51c8d1f3fc6993dc6` | `184752a40931d96c027041238d1a433570e81a7544d0882de44e2190ddcd07bc` (76) |
| `default_and_min_texts_faithful_for_cfg0_but_not_other_readers` | Quot.sound, propext | `59cf874e19f24863112b78f5d14b6b93c39b1dd2c83fee3666e5326f36c4f63a` | `f9bd7e4878aefb95304d24ad5704fa7457395ca0f7a92976677c9b0559455594` (186) |
| `default_text_incoherent_operator_vs_leaf_coercion` | propext | `a377a3febab4afd3ed0e50c546f47ef1b36cfa83d80ce200b5d2bc4efaa8f143` | `65061f619adbb698960c217e433f963f48261be39429c885eb9ae42d568661df` (154) |
| `deltaNF` | none | `56a4c9a6169e718f8538d98206a4638a3408413b878ea350b3b0281d93f35607` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `deltaNF_check_rejects_reordered_unfolded_rendering` | propext | `5ee015b2337272f1ce80b5effae03d57c9f1fdfdfb6eb9b3193c7af4dfd4a9b4` | `342a309a29f7931fa12ad7177e3dc8e671528e1926ebf91218fa038839f03005` (134) |
| `deltaNF_not_wellTyped_of_illTyped_defs` | propext | `72c100e1864ac5644fa45b4ad6be524151c84c0dfa0b71fe22a0928ac89c6606` | `cac3e21493acfe1d015f76544472a4792797ae640ee6b0e9a383a73a8d9d1661` (115) |
| `dh` | propext | `b2fe1fda4cff52d46239e63eac80b73d1ef6327c2f4917946a623ab0dfea60e7` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `eLeavesOnNonFull` | propext | `d6922b993b52cc736465d8e42f4136553c7753b313b686a7705d12f03ca1e043` | `a99c60b1302fb2cc84c293f31c510ae63063f9bfbea201e724e1f2278964f9f6` (30) |
| `elabE` | propext | `6f8f690b4216f518ddd39b41aee47fabca98c34ec2c32d818cd010ef062116c9` | `963bebad62c053cc58ebaefeda492e86b9b1210a7de2fb91ba5c58c83bf58637` (34) |
| `elabE_sound` | propext | `77ba876395a37860147c8075216e31bacd5dd5d4fc2e2bc399a7cc19ac88704c` | `69c1d238e13eaa9f63e8313710af6f8204ffb423031a627316b377ca795e9e0e` (103) |
| `elabSys` | propext | `d6922b993b52cc736465d8e42f4136553c7753b313b686a7705d12f03ca1e043` | `a99c60b1302fb2cc84c293f31c510ae63063f9bfbea201e724e1f2278964f9f6` (30) |
| `elabSys_ppDefault_eq_some_iff_defaultRecoverable` | Quot.sound, propext | `eb18722163206a3016517a25d4cd4fe3742dacd417abaae02242a515d83ef2fa` | `1400c57d7ea028aaf88ce349b1dc03434cbb32c6e86ea2567bbda26f98bb39b8` (112) |
| `elabSys_ppDefault_of_defaultRecoverable` | propext | `0526193324633277c6e33132b4654c040616bf7d98ebd078a4eed16f2cde82c5` | `1400c57d7ea028aaf88ce349b1dc03434cbb32c6e86ea2567bbda26f98bb39b8` (112) |
| `elabSys_ppDefault_tIffNat` | propext | `8ae4384d20c329fd2324dca587e0693e69e9c2c9b85e48075c9c8ab6db41a29b` | `737f628fb368ca80d450781a7cf2b1ca873a33f0c540d300e9dbcc9217c53bb9` (108) |
| `elabSys_ppDefault_tZ` | propext | `45058ed716f9f6b01f10fb849cea447545798fabe3a2cc4913c3bac055e1805f` | `26a67efb96657e75d1e5b19ccc960a1e7b7d191625ba2be7149e6c36b2f0b147` (108) |
| `elabWith` | propext | `f5829a739f8f2d9b4a5dcdd42459d40a7e316ce52e1b3724d5023811b2199e62` | `963bebad62c053cc58ebaefeda492e86b9b1210a7de2fb91ba5c58c83bf58637` (34) |
| `elabWith_agreeOnFull` | Classical.choice, Quot.sound, propext | `a987d597b74b52c5b2c07bb428421b0bd6795e769f30d31321cb097cd46507c9` | `fef4601cddbb6f815d3bdba7886d6d58af55b1900246038b68ec0072c1e0896a` (93) |
| `elabWith_eq_elabSys_of_fullyAnnotated` | Classical.choice, Quot.sound, propext | `f4b6931ea6905003a2395edd4cd9e23ef18e85b1ee120824b14c7dfc560de0c7` | `b894035163a34edd1a2c022dd6f8f2c12ee7b277f2f82f677399b81161f3bcc9` (92) |
| `elabWith_ppExplicit_of_wellTyped` | propext | `58b5439dc0facf517faed4f0d78fd419c6ad1912290d55c388dcc17e47367533` | `e3db6de2d8f1c971153b901f1db72a2ca89f0a6f117727e22618add4621d36e5` (104) |
| `elabs_coherent_of_fullyAnnotated` | Classical.choice, Quot.sound, propext | `d597c7b2a27c46bc1e1e0994eb147d6d8c0fa775e7e6f5cd5577a1a83ec72cfa` | `362f789d65443f0658f37b2c1881ae94756232fa39906265754118b4ec434e91` (102) |
| `elabs_coherent_of_subAnnotated` | Quot.sound, propext | `5ee45bd6e42ab898f31a28fad2605b07085266677cc4954a706d120598c6acc5` | `76450113a9ad64923d2a4776ecb41d21730404b50e1a26e55fe11debca958660` (100) |
| `elabs_coherent_of_subFree` | Quot.sound, propext | `1c9993710faca32318c072c02ec19fde8c3ff3cc66d22d31927504bd564d9721` | `f0f1f335e9f9fcc15cbbe95439f15b97b742c5dab0f4ccb4c7da80728b63b36e` (100) |
| `elabs_not_complete_for_elabWith` | propext | `69439fadaddf47c12271f3b4d29f7da6c95ee015c240eb75ae59349a8be35e08` | `918770140f7a8903fd43136b90bd5bf1d432877dd33ab6044ccb3a4b01e5657e` (101) |
| `elabs_ppDefault_tZ_tZ` | none | `5a4f6369950ed88f9ad0e09bfecd234588532dd445d7ec7d6320a61c8d5e946a` | `c6d1249fc933d60c933580a5c564066456c3c4ad7b7de734b2abc616035ee99a` (78) |
| `elabs_ppDefault_tZ_tZLeaves` | none | `ca907e3fd4d0c5a54fc84e9746303bc1013d894feea5bfb8028eaa9b3901ebc3` | `416e07702406d96050a8059cb076570ce88e49d3c2f064d2733d0b27efd9697a` (79) |
| `eval` | propext | `f68d0ce04d3e6a3909d757b1c13060a9161f14957eddd2afc7a97a8dce0ef8b4` | `25f2f56c0e67541980cd5907465758e0edceba1c81a906d7524e77b4f254c930` (24) |
| `evalD` | propext | `1bca0f959e66908159dadfcd049887b92736d8baf90b6e8121c601a5714e5b39` | `76cd21c0e8e57a8a05c2a18b81383b53fb6de8074b6c55c1a3c81b8718394fb5` (22) |
| `evalWith` | propext | `7cdf90688458e30fd56c5ae3ee0a9dc5d977ce1fd16a54a45159152ad1c30c08` | `dd52f39a87d1c87b003a21eeef89df25d6029b6bddbd269d5e9af64aea687894` (20) |
| `eval_eq_of_deltaNF_eq` | Quot.sound, propext | `501d93d79faa5d26cdcb2faf29563312106163c4e6713e7560fbb7335a53b413` | `54fa2ce22b1c576d2baf296323a727fee6b26a8cdba0049335977df8c42c5219` (64) |
| `eval_equivalence_identifies_distinct_valid_terms` | propext | `e8f209f792c0a3fb19c5df992a8168fa48fbc8ee4394a15bda1579bea5e4f088` | `619b91d0f29ef94fac8a63c6799a0df96dae1077480dc832982ad686eae54efb` (65) |
| `faithfulB` | propext | `13bf140584b92965ac5c6bd10250feb0216f67e9b7bf35007ef5e90d30cb3a55` | `963bebad62c053cc58ebaefeda492e86b9b1210a7de2fb91ba5c58c83bf58637` (34) |
| `faithful_ppExplicit_tTrunc` | propext | `3e49eecab7c4564d89b12410cafb3cf300642f6ec896a53c06f9e4a498c3cbfe` | `de2ef36067319cd68a185647835d7053311a6073c56520e1bc517ea8b9fcffd6` (107) |
| `faithful_ppMask_mono` | Quot.sound, propext | `98c0dab20dff2b4a56f29cbed87c6e1e1c7bf2e1ab14e2624c5b35526f98e2bd` | `f1e5f753654b4c0cc4b1cda81377f46ee697c8c850f5fb0e1394079cf3db1ff7` (99) |
| `faithful_reading_unique_and_same_denotation` | propext | `4da8590d33b08f083dcf197648ac0983cd54aad628e71ab3b9cbdcfd18348b1a` | `a77ca83e0461a2eb697f6f10c36cb2124ca3f7543f7fb637fd3bba365c557d06` (121) |
| `hint` | propext | `cec47cd02dbcfed4158c70b1f5155f2dba5ca309002b2a4089cecee4f873311c` | `0eb0a7e06a6c5386ef591c1b503a46b9905b38741be62af228f857406e0d1cb9` (29) |
| `joinH` | propext | `85c6ac9d7a4f3aef8b34dbe22eb4ab924b69963558c89a6d6446e6fc0fa65970` | `24b75290190d70e3616d04a90f1819b7e19d190a96381df18c33097908f73405` (4) |
| `lookupDef` | none | `b3f2c5d628b8129555bf6b9c4f5650536ce41c330e3a937b6da6b80532df7bd9` | `235eaebdabcad194127479d59e86d9966acddb4daf82fb1484aaf3f66af0ef22` (16) |
| `maskOf` | Quot.sound, propext | `b872a218f7a6fb8fc1d397c53e271703c1b4fbeafbf1305e80a489eb15cf4f23` | `5f0ded938c8d04045730fe54d8559e49fccd5fe24164b371d6395758eff05d9c` (6) |
| `minMask` | Quot.sound, propext | `3304b4199a071585b87d574e6e3093d30c8f2bbc494afdd219a77d4853d377d1` | `1ad3d5e5a67c72abac1fb7f3c907e03eddcf434c8d952298e8c70d7c09e5b1a8` (28) |
| `minMaskRev` | Quot.sound, propext | `3304b4199a071585b87d574e6e3093d30c8f2bbc494afdd219a77d4853d377d1` | `1ad3d5e5a67c72abac1fb7f3c907e03eddcf434c8d952298e8c70d7c09e5b1a8` (28) |
| `not_agreeOnFull_none` | propext | `3bc578f9181f12e8c8125c80bdcc6934313c40011dc40e01bf2b1503a7836a05` | `fef4601cddbb6f815d3bdba7886d6d58af55b1900246038b68ec0072c1e0896a` (93) |
| `not_defaultRecoverable_tCoeNumSub` | propext | `2255455dbe561724533410540902ca74d0789373294dd8be03fc288b72f265a3` | `eeadac8556172c95e264779dd590041694405ff0472dfd45cc6c812df097c625` (151) |
| `not_defaultRecoverable_tCoeTwoEqZ` | propext | `e020877a2cc7097d5f703515912defcbd842a0906d7bafad57807858201180f9` | `4b7889f3f9bff62f28965a637970ceb2efe1a542d70183211426cda5602d7a6e` (120) |
| `not_defaultRecoverable_tTrunc` | propext | `28a1eef480950d519f39f9dd824212fd3c726b11925a967ecc794ca0c9a208e2` | `9f955ccbf8a4d2f1c2a09371c295275f0e8bee518dea34214860c039ef761d9b` (76) |
| `not_denote_tIntSub` | propext | `c294fd473ce1ab23439c0b1083097043ae65c867ba01b49a17ee8f2b9722c64f` | `6f122607b4bef784e18129a33e9f826a24549312e4a8269ef8d640f9a1f7c4e8` (64) |
| `not_elabs_int_var_at_nat` | propext | `7e97bf79987eb59a171b9a96f344ceb4cbedb3c4de040c86fa630133d8b1adff` | `292b21ba3c01c148ee8a99baba6d295d3d935cfc3c72ae089b486e566a39faf6` (61) |
| `not_faithful_ppDefault_tTrunc` | propext | `47147d4e98bb89326e53531a79029fb7fbaea4c8dc7377510f63cff2da27afa3` | `77162c9d6229c1efed1a00ad1119d8d7b24081fe5abd335e2c4991ab59dfeaa5` (107) |
| `not_valid_tIntSub` | propext | `e2f43711d2c47062373f2f7bb10d9c155b875dad0ae3444103c6f034c012875d` | `6acf298e16852d067436cfd0d6bf7220fce6f3f748bc5cb034fe4c9d52a97de5` (65) |
| `not_valid_tTrunc` | propext | `fa9397d35bf0f026ee227c63628ef0437fb53f5e0c4e60c55b41913b8287f1fe` | `2c86d5519f6166bf3f1450bfcde7600e5c4177bed1626d81cbd6fb7d836397a5` (65) |
| `not_wellTyped_coe_int` | propext | `e582a382fc211c378c438473c55e0c8fea74eb8de0715fe3584bfb9040286289` | `2fefb75c5f60a059ae201140201fc642becad459cfc49d47038586bf03467c44` (51) |
| `not_wellTyped_tIll` | propext | `0a3ffd4d14767989ae8a6f44b11ebe9e6ee40157d91046f1d5aac82e573b4dd3` | `5f1bb219192dd54b750b3d7c83a520acc061fad0572c84e4e33870934f385873` (52) |
| `numOnly` | none | `daa04412898d7ae910ddb13a827aa9c950de58af37f58f722782fc4017f4c023` | `24b75290190d70e3616d04a90f1819b7e19d190a96381df18c33097908f73405` (4) |
| `nv_agreeing_reader_reads_ppExplicit` | propext | `8f25459188a2ce5ce456bc00c3311179bff57e752f333f155cefc70959097538` | `123e9cf2d0999fd1e185a0e2f517fea5f2fc63cc1731f5b5e22753e5bdeaa961` (121) |
| `nv_elabE_sound` | propext | `09143a66118ce6bfef4186d351532d1f2d9e220e2fa85dbc4ef229e08503c45e` | `10f4e9a44b5a2109d755a2368147de3e13d9d2b88552289da519948322c474ca` (105) |
| `nv_elabSys_ppDefault_eq_some_iff_defaultRecoverable` | propext | `682d5a7ab2fef1147bb37e1209fe37253bd81f0976f022b3d3e65997f0da0b69` | `4680288eba03c97c2c232316a35d6fd7643bfe4f4c8e60af86113b6867d95d7a` (118) |
| `nv_elabWith_eq_elabSys_of_fullyAnnotated` | propext | `265982ebd9409fbbee62368e5134ec0b0ae46227551cafa9afba56f00835593a` | `a5422e965db209eb01090344fa33c598410e53e7ba5a54b7e5b22dacdbd0c12d` (114) |
| `nv_elabWith_ppExplicit_of_wellTyped` | propext | `51c49ec7428ce3a0c58014469376451d8a68fc84d094c3a446b97607c3e89b36` | `12016ab2ca1803714580371464b92dfe5099235af4698898fe50937e93138750` (52) |
| `nv_elabs_coherent_of_fullyAnnotated` | propext | `2c4472509684a95a674e9f31dbccedd45cc8605ce5c1cbd9027b425d87ae1ee7` | `d12af01fcb91b0e7acd05934fab42a0504df1b17792e9dd7f97044e76c0c2535` (72) |
| `nv_elabs_coherent_of_subAnnotated` | propext | `68d31e8c2b05a2b327c8b263af6796b30c6e639a56b9d0b9f50c655606455a32` | `0880e46e3e3f6fcbbddc98d8d4b12921c58d794f7bc8221a7e54a0c88abdf84e` (77) |
| `nv_elabs_coherent_of_subFree` | none | `a9aeaf53354773e0952c3edd7b8cd53b432c63bbfdbb15f5f543aa43f259dda1` | `148d5fe29b8746b994a4dffc6db64f3bb879645fed33ddb56d2c9a89df0b1ea8` (87) |
| `nv_eval_eq_of_deltaNF_eq` | none | `ad2b2c5a30b31eabd07a048893a7ae214e3d4b2d38ce6742b16a1a6a3da7cb21` | `1055b852d427ef88cfa011ca731608c584657a89ac938611b787519161a32288` (37) |
| `nv_faithful_ppMask_mono` | Quot.sound, propext | `407b52f3750ef5aa30a92933abf440f3db84d26867367a4b29f7ab4b104ae6b6` | `73ee2f44fd5347290f00d3f24965216a88a584a1ccc850b574f2d027328cec04` (115) |
| `nv_faithful_reading_unique_and_same_denotation` | propext | `3e49eecab7c4564d89b12410cafb3cf300642f6ec896a53c06f9e4a498c3cbfe` | `de2ef36067319cd68a185647835d7053311a6073c56520e1bc517ea8b9fcffd6` (107) |
| `nv_ppDefault_elabWith_of_annotationFree` | propext | `ddbcfc76eccfc606944d9d3be9acb324c35962a0e59d30a4c44d90f6e3874b10` | `801632a8a7a2678b481c0ad5bdf3fe75a835e6f4afe7b97a4be04ca98dc1bb54` (109) |
| `nv_ppMin_eq_ppDefault_of_faithful_ppDefault` | propext | `f3c5237453a517d99582626baee247d4204940004c7a21fb55ef7ef8aadebcc8` | `5553cd4723afb7ffa1a1306af5146dec600e75013c0e44c0d349b21e4a80f52d` (107) |
| `nv_ppMin_faithful_of_wellTyped` | propext | `877e9809e389324e7b93c2f70a50d89108a927f6119f87643768c0bf065a2abf` | `dad27c3ee544e9739381059f00ed744f924c49f31633846d29e727aa4e0737ed` (111) |
| `nv_ppMin_locally_minimal_of_wellTyped` | Quot.sound, propext | `dda33faa55e083eb9d9b746c01ca890e747f4c1c6775e8bdf83be3dc244098bb` | `4d07ccc034fb9a9423de15f3b7f9f2bf31018a39d09775436d168f70304d90b3` (147) |
| `nv_textual_round_trip_of_faithful` | propext | `0e0da3184e494ea6835acaace1314f1173f34b29ef74638590b09330df0b5d33` | `269bbd51198d8ed12b25d72d8c5bc2a9fc3fa8f39458a2bcb61f142cc8fa4a80` (106) |
| `opType` | propext | `ce0b9598c15a8f04db2a2f15d86ac17311ba08dfb890fd4b2097262bffe75b35` | `017e49cfea971d7180a07db664039de4f5f58b707837614d488efcd0a5fe1068` (9) |
| `partial_annotation_faithful_for_every_configuration` | propext | `fbc2a3d4019c13209c90af59c6e5442e884f45022d9fae9c4c75d5736207df98` | `2dd04954ce52a28f5ab59103cba9ef20fb6cc36dbad8c393a5344b69306ac017` (118) |
| `ppCoercions` | none | `646e758896645de143b935ee5013276cd8c2775c9468665902a9863a720be402` | `38c86f60a567458fd6c915bdd646ec93bcab34432a44ebc33f9a77031a3e4fad` (25) |
| `ppCoercions_textual_round_trip_fails` | propext | `8df8f06cabf85446d793a8ffbfb32b4e478a1684d48d14ccdd9fec68a66b3461` | `ede05d110435b41e8cb3e3fbce1f5c96071e2506202ee05c2a5fd3a334c490d5` (114) |
| `ppDefault` | none | `646e758896645de143b935ee5013276cd8c2775c9468665902a9863a720be402` | `38c86f60a567458fd6c915bdd646ec93bcab34432a44ebc33f9a77031a3e4fad` (25) |
| `ppDefault_collision_natSub_intSub_changes_truth` | propext | `cc21d284337975968d29e7d0092561765114731ba7994c7118c03731a9aba6ce` | `fc5043a8ffc5e9b463de8da3098ba82eb8258fcbb256941ae3cdd64c14e9a7c8` (89) |
| `ppDefault_elabWith_of_annotationFree` | Quot.sound, propext | `78be19396075379be80d56e1bf923463da0e306d37416a3a0c09c716110b63a6` | `c047f2ff95e77bd1138af6eb8cb68b68bf81950fc42e2e0aa8fa0983a04a6c83` (102) |
| `ppDefault_tEqAB_faithful_for_named_readers` | propext | `292f9ebd33ea0043c664888424fc9bfa0adb9faa00c54e6bd9addadc8d134676` | `7bb74610d8a9a809129edf89414ea9caa3701b6cdee3d622ffc1574910328286` (114) |
| `ppDefault_tTrunc` | none | `bed9d0629dfcecd7cb63af1023a29093f746fc9fb30eaffb552e597f2dc78f5c` | `fb3b231829ff70b1d1abfbc42d05ec2ad51a56a96b0b7b0a7b5e81651945fe64` (44) |
| `ppExplicit` | none | `646e758896645de143b935ee5013276cd8c2775c9468665902a9863a720be402` | `38c86f60a567458fd6c915bdd646ec93bcab34432a44ebc33f9a77031a3e4fad` (25) |
| `ppExplicit_separates_natSub_intSub` | propext | `d8e21dba8fb43bd499db9b346b1d9afdd40635d9cdd75da1cc44dba28e5ad40b` | `29d61f99210492d67b4a2f761b58610c8a0cc4b1a2d3e75aefa1ab40fd867400` (109) |
| `ppExplicit_tTrunc` | none | `f540ef29c550d176fa917d08b60e88b21542d66e683acd351035865ef853119c` | `85327843231472924cc82815d20df49c300df7fd17a859a0f45fcbc062fe8b32` (44) |
| `ppMask` | none | `8ec8919ecd46990676ea2de3c0b4b69a0056ede4a4c115e6635be37c783f78f1` | `54b67da13e4afa53074917d8a39dfd5c90430a430fd5bcb28f04e52e80abcb44` (31) |
| `ppMin` | Quot.sound, propext | `a14fad102014eeac81cf7828342c8c85040deadaf0e17307922f443c01601435` | `963bebad62c053cc58ebaefeda492e86b9b1210a7de2fb91ba5c58c83bf58637` (34) |
| `ppMin_cfg0_tEqAB_faithful_for_all_cfg` | Quot.sound, propext | `3611bf62b65fe535012b135d5d870d6009ccca56cec31182f3af204da23f9e99` | `29630c98abd868588c258ed4e1fe441c4d4640f051b2316d35cd9abfde3b3ab4` (151) |
| `ppMin_eq_ppDefault_converse_false_on_tIll` | Quot.sound, propext | `abaecc949651c20d460bc19250c7b540a172b5e677ade95bb3cf91217af5a06f` | `be88e8e211276843c7b91468b7b92b8d1aa5830669a5cad7bd9050a27f1ad615` (147) |
| `ppMin_eq_ppDefault_of_faithful_ppDefault` | Quot.sound, propext | `b28a976a85e21361e525b00568d81ed0ebc2707217556600917e97190fb35bd9` | `d4dc8c4e48bbeba4c9c60ecc8d5aa9d56104cc143ad65fe65bdd113df73763ba` (141) |
| `ppMin_faithful_of_wellTyped` | Quot.sound, propext | `a99fe0c2c62f4ce61f665b920fbb01869974b0b3bdc6d97523503199fc57ce20` | `ad62fb1fe3a8fb1c11253a3d140697f1c060aba5e75f01305849343880ac041d` (143) |
| `ppMin_kept_position_not_globally_necessary` | Quot.sound, propext | `5ce7547fada50f1c19073fb2fd1aff4f3a17c060b0481dc6d3d2544f6b6f4787` | `deb4b3356c7f4d5c9b8d2d66fa8ab62a032aa8acb1bdfe9dc5c9b93d1dccc613` (148) |
| `ppMin_locally_minimal_of_wellTyped` | Classical.choice, Quot.sound, propext | `ca73cdad24ca8a2aba1cfd08c195f098e15c9f74b47bd1e1fb4c944dd63ecd24` | `ad62fb1fe3a8fb1c11253a3d140697f1c060aba5e75f01305849343880ac041d` (143) |
| `ppMin_not_globally_minimal_cfg0` | Quot.sound, propext | `0c62e60fd53dc0c574e9dd61cd1c437b50afd46a4b30b79ca6198a743d2ecd10` | `30006dffdd602fa90d5c88ed9fee25d8b49cb1f1a9b5a917bc7599770339398c` (151) |
| `ppMin_not_globally_minimal_on_tTrunc_cfgLeaves` | Quot.sound, propext | `6e31d8d8acaba7398b5b3612a51777baf2f94563b42b4b6dd5dd48837680c6a2` | `087b5ba6c333c1e7abdfb4f735dd5295373cc3230c5ff0ac974bea1254a77104` (151) |
| `ppMin_tIntSub` | Quot.sound, propext | `f0911798e6feca0f49a69b5dd929f101b9c61a945c8677c7790efa14b639d987` | `02c25ef021b8df1b86f55ff754755f4ca39ff95679513aa42c2f06f54ba5bf63` (144) |
| `ppMin_tTrunc` | Quot.sound, propext | `921a94051b049bdedbff7979e3b87670e108c3f6c60b09dde0f4690a702bf8be` | `ab6a277430c04a1e1c58b1c716159f9718238ae950c9f499a2bdb30325eb4ea3` (144) |
| `ppNumericTypes` | none | `646e758896645de143b935ee5013276cd8c2775c9468665902a9863a720be402` | `38c86f60a567458fd6c915bdd646ec93bcab34432a44ebc33f9a77031a3e4fad` (25) |
| `ppWith` | none | `bb0177e8b9f54b7d4f5125b7f0b49a8b23617f8fb77fec8c15883dd72a23a883` | `5c58c662a3b772c75d3da3337a491ad8d3c5f77b4d346b08b40254390a25bc0d` (29) |
| `rSwapped` | none | `7683f5bdd15cfa30e6110ad066f4a75851185d6dca96abbd74b5c1893dc4b55e` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `read_by_all_agreeing_readers_iff` | propext | `933130eb0f0f00551bfb7ef885bbac6c9744724dd925819ac29e91081dd8b5b1` | `fef4601cddbb6f815d3bdba7886d6d58af55b1900246038b68ec0072c1e0896a` (93) |
| `read_by_all_readers_agreeing_on_pred_iff` | propext | `b68608a38cece0f22f9fc906b377f7ed7105b4e185d610c496f2d34483fefcb7` | `a99c60b1302fb2cc84c293f31c510ae63063f9bfbea201e724e1f2278964f9f6` (30) |
| `sAASub` | none | `7683f5bdd15cfa30e6110ad066f4a75851185d6dca96abbd74b5c1893dc4b55e` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `sSubAnnMixed` | none | `7683f5bdd15cfa30e6110ad066f4a75851185d6dca96abbd74b5c1893dc4b55e` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `sTwoEqZ` | none | `7683f5bdd15cfa30e6110ad066f4a75851185d6dca96abbd74b5c1893dc4b55e` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `sWrongSub` | none | `7683f5bdd15cfa30e6110ad066f4a75851185d6dca96abbd74b5c1893dc4b55e` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `sZZSub` | none | `7683f5bdd15cfa30e6110ad066f4a75851185d6dca96abbd74b5c1893dc4b55e` | `c121608388adcebc7f6ccdd150c9336057721ac881b82a2cd38ad73df30db982` (15) |
| `subAnnotated_not_necessary_for_coherence_cancel` | propext | `304ff343175e89688528d03159a7cefe1c730fc50552b8d8d45bd7fc6777d56d` | `97c1d98f8704e3e613a524d7e35648ec4cecd98f2e3e13544e301c34d38b61fe` (112) |
| `subAnnotated_not_necessary_for_coherence_int` | propext | `78616bd59af290b267de22733f54f79140c9e8447faf782391132bccc25c34cc` | `23d5072869477b3c0bff195fc95a4c3258573a6228f9b55c5863e896af8c0e70` (112) |
| `subFree_term_round_trip_fails_across_readers` | propext | `422ec295c3afb4027ca3814578ec84182bfcdb7ea4c83c15264f2217c569ea66` | `f968895edcf829b5e7cbac0a2833239a045ee4a8c76d5ba60d4253483e7d264b` (111) |
| `substConst` | none | `eb6ce21fce59f8825549a60cc1e73d721df00271f199b0af64b5edd354dc0a56` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tAddIntNumEqZ` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tAddLeaves` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tAddOp` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tCoeEqCoe` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tCoeNumSub` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tCoeTwoEqZ` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tCoeZeroEqZero` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tEqAB` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tIffNat` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tIll` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tIllEq` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tIntSub` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tLitProp` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tNatSub` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tReread` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tSwapped` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tTrunc` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tZ` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tZLeaves` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `tZeroEqZero` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `textual_round_trip_holds_on_elaborating_ppDefault` | Quot.sound, propext | `5fed480f3d524f214261624c45056f217f68e0b29b67e0afee07430064e03582` | `8c08eed4c18c93a8a551f7c0dd66a0d64151a1ee771bacf578529884201d6ba3` (100) |
| `textual_round_trip_of_faithful` | propext | `d3e2d252c01d7840be03232514933b3c8104486a88561a09ef34fcce1a1cf903` | `ec33851e90e41be837c4363f5030da84858bff00017c67d44cca45aaadcc0c47` (84) |
| `textual_round_trip_passes_on_tTrunc_but_term_and_truth_change` | propext | `877456b79028a25befd2b8410c3cd92123776ee59f74396cbc5cb521c573bc98` | `18f6d216e07dfebedf429cde0ce4681000d4aadb40f081bc66e075e81d567d79` (142) |
| `tyMatches` | none | `6eddaa22c3889465b4b994e6606c5a0bf01fdb7c0791abb936278c8069c6b516` | `24b75290190d70e3616d04a90f1819b7e19d190a96381df18c33097908f73405` (4) |
| `tyOf` | none | `b2fe1fda4cff52d46239e63eac80b73d1ef6327c2f4917946a623ab0dfea60e7` | `09d2a1cd0425e6ec4a5ee170d6ec951aaab25277568a9aae966055bea45d0247` (18) |
| `undefVal` | none | `3134bf9c702fb4cbb8889753b4ed1065c08a5d5704ab722a596f16576a60b588` | `1e1805282c156e7556785d75cafa15f70600a03284349c93342f2da105c46e53` (4) |
| `unfoldDefs` | none | `de3e2a83558150c0525b09b9ba8be2e2be053094ad706729656ee32758bb1f7e` | `235eaebdabcad194127479d59e86d9966acddb4daf82fb1484aaf3f66af0ef22` (16) |
| `vA` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `vB` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `vZ` | none | `5c4d5e65dead4786a1dd8f459620b28bef65f6f45e352020fc3d09da99f9dca4` | `1c88b8f0bd8e0bdf1a18c7f17cdbfaa811a8c7054fadc053ee0e7f9c015b2e97` (14) |
| `valid_tNatSub` | propext | `11b8705d49bad96552e7ceba732752c0db41efecb6a381ce081d2ab913303da4` | `814bdfd8f944262a8f60b37617b98af13c85d70b500811a43a2d18ac247e0b3a` (65) |
| `valid_tReread` | propext | `79b2642cfb76fba6aba2085031a51b680a4bb67282876958144e3c9916b7ddb0` | `2b4cfbe3b02c6ccf829eb614d158e281300b611ddf6a85a9c333f9b367a6f05c` (65) |
| `visiting_order_changes_kept_set_on_tTrunc` | Quot.sound, propext | `42d7425ac2479a010fb2c2463871af7b3d0ce29f1711a9f893ef95eb57a0face` | `9a7234038c35b91aa306e0601997058132aafb248dc27cfe5dd9c6452105792e` (145) |
| `wellTyped_tTrunc` | propext | `51c49ec7428ce3a0c58014469376451d8a68fc84d094c3a446b97607c3e89b36` | `12016ab2ca1803714580371464b92dfe5099235af4698898fe50937e93138750` (52) |
| `wrong_type_annotation_changes_term_tZ` | propext | `a26ec230dffb24ceb58de3b7b2076bdce535e8f12865c1f8af94c735029fa81c` | `82cc9ab607dc468c0435aa486cc892db3fb26cd2dee42db6f5625edff774e584` (148) |
| `ρ₀` | none | `7e13719e20cce3673f08b09b65cdb19b7c6b03b93b52e4bf587dd9103399a108` | `3e8df74eb573a7fdb1d7443403026d94b60d8f95f230df29bba025050210850c` (2) |

**Toolchain.** `leanprover/lean4` tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (tag reference read from the GitHub API on 2026-11-21). Lean sources cited in the prior art and in the observations: `src/Lean/PrettyPrinter/Delaborator/Options.lean`, `src/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.lean`, `src/Lean/PrettyPrinter.lean` (lines 20-23) and `src/Lean/Elab/Extra.lean` (module documentation of `binop%`/`binrel%`), all at that commit. Mathlib: `leanprover-community/mathlib4` commit `3eae40f5eb25c5934211edf662d3b24c5afbe47a`, `Mathlib/Tactic/Linter/PPRoundtrip.lean`, lines 124-147 (commit existence confirmed through the GitHub API on 2026-11-21).

**Primary sources for prior art.** Each entry below is cited by at least one card, where its relation to the card is stated. All DOIs listed resolve through the DOI handle service (checked on 2026-11-21); the Archive of Formal Proofs entry `Printing_Parsing_Roundtrip` and arXiv record 2604.15713 were retrieved on the same date. Where a card states that only an abstract was consulted, the claim rests on that abstract.

- Freek Wiedijk, 'Pollack-inconsistency', Electronic Notes in Theoretical Computer Science 285 (2012), pp. 85-100 (UITP 2010), DOI 10.1016/j.entcs.2012.06.008. Definition 1.2: parse and print are well-behaved if parse is a left inverse of print (this package's term round trip). Definition 1.4: a Pollack-axiom is a well-typed equation t₁ = t₂ (or equivalence of formulas) whose two sides have the same output under the system's default printer. Definition 1.5: a system is Pollack-inconsistent if a contradiction is derivable from finitely many Pollack-axioms; two terms with the same printed form give a Pollack-axiom, not by themselves an inconsistency. Section 8.1: a failsafe printer (all coercions and type annotations printed), a parser adapted to also read the failsafe output, and a combined printer that prints normally, parses the output back, and falls back to the failsafe output when the reparse differs; both the printer and the parser are modified.
- Robert Pollack, 'How to believe a machine-checked proof', in G. Sambin and J. M. Smith (eds.), Twenty-Five Years of Constructive Type Theory, Oxford University Press, 1998, pp. 205-220, DOI 10.1093/oso/9780198501275.003.0013; preprint BRICS Report Series RS-97-18 (1997), DOI 10.7146/brics.v4i18.18945. Section 3.1 'Reading the files': a reader sees a concrete representation (a string) while the checker uses an abstract syntax tree; unless their relationship is understood nothing the checker says can be believed, so a checker should support an official syntax that is parseable and printable.
- Mark Adams, 'HOL Zero's Solutions for Pollack-Inconsistency', Interactive Theorem Proving (ITP 2016), LNCS 9807, pp. 20-35, Springer, 2016, DOI 10.1007/978-3-319-43144-4_2. Only the abstract was consulted: HOL Zero aims at well-behaved parsing/printing and Pollack-consistency, and annotates terms minimally with types for unambiguous printing.
- Lean 4 v4.34.1 (leanprover/lean4 commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Lean/PrettyPrinter/Delaborator/Options.lean: pp.explicit (default false, 'display implicit arguments'), pp.coercions (default true, described as 'hide coercion applications'; with the default, coercions are displayed as an up-arrow, not elided), pp.numericTypes (default false, 'display types of numeric literals'); src/Lean/PrettyPrinter/Delaborator/TopDownAnalyze.lean: pp.analyze (default false, 'try to determine annotations sufficient to ensure round-tripping'); its module documentation says the analyzer 'is neither sound nor complete'. With pp.analyze enabled, this toolchain prints ((2 : Int) - 3 = 0) as 2 - 3 = 0 (build-checked observation in LeanObservations.lean). Modeling bridge (model–system relation: none proved): the toy models neither this printer nor the analyzer.
- Nils Anders Danielsson, 'Correct-by-construction pretty-printing', Proceedings of the 2013 ACM SIGPLAN Workshop on Dependently-Typed Programming (DTP '13), pp. 1-12, DOI 10.1145/2502409.2502410: pretty-printing and then parsing with the same unambiguous grammar returns the original value; it concerns concrete syntax and involves no elaboration.
- Tillmann Rendel and Klaus Ostermann, 'Invertible syntax descriptions: unifying parsing and pretty printing', Haskell '10 (Third ACM Haskell Symposium), pp. 1-12, ACM, 2010, DOI 10.1145/1863523.1863525, also in ACM SIGPLAN Notices 45(11): one syntax description yields both a parser and a printer via partial isomorphisms; it concerns concrete syntax and involves no elaboration.
- Lean 4 v4.34.1 (leanprover/lean4 commit 5045d0056413266e57c625dcd7c365b10e377c52), src/Lean/Elab/Extra.lean, module documentation of the binop%/binrel% elaborators: computes a 'maximal type' for an operator tree and inserts coercions in the 'leaves'. Modeling bridge (model–system relation: none proved): the toy's system elaborator places coercions at the operator, and its leaf-coercion reader cfgLeaves resembles the Lean rule.
- Mathlib linter.ppRoundtrip (leanprover-community/mathlib4 commit 3eae40f5eb25c5934211edf662d3b24c5afbe47a, Mathlib/Tactic/Linter/PPRoundtrip.lean, lines 124-147): for a command that produced no error messages, it formats the command's parsed, unelaborated Syntax with Lean.PrettyPrinter.ppCategory `command (Lean v4.34.1 src/Lean/PrettyPrinter.lean, lines 20-23: sanitize, parenthesize, format), normalizes whitespace in the formatted string and in the original source, and warns at the first difference. It does not elaborate to a kernel term, does not delaborate, and does not reparse the formatted string; annotations written in the source, such as (2 : Int), stay in the Syntax. It is a syntax-level format-and-compare check, not an instance of the elaborate-then-print round trip studied here.
- Kevin Kappelmann, Maximilian Schäffeler, Lukas Stevens, Mohammad Abdulaziz, Andrei Popescu and Dmitriy Traytel, 'Type Annotations with Roundtrip Property', Archive of Formal Proofs, May 2026 (entry Printing_Parsing_Roundtrip), companion paper arXiv:2604.15713: complete and minimal type annotations for rank-one polymorphic λ-terms as printed by Isabelle, so that reparsing and type inference recover the term; mechanized in Isabelle/HOL; a reverse-greedy approach yields a locally minimal and complete annotation set. The closest mechanized prior art for the deletion-greedy printer here; its setting is Hindley-Milner type inference, not coercions and numeral defaults.
- Steffen Juilf Smolka and Jasmin Christian Blanchette, 'Robust, Semi-Intelligible Isabelle Proofs from ATP Proofs', PxTP 2013, EPiC Series in Computing 14, pp. 117-132, 2013, DOI 10.29007/zbdb: Isabelle proof reconstruction that provides enough type annotations for formulas to be parsed correctly without printing all types.
- Jasmin Christian Blanchette, Sascha Böhme, Mathias Fleury, Steffen Juilf Smolka and Albert Steckermeier, 'Semi-intelligible Isar proofs from machine-generated proofs', Journal of Automated Reasoning 56(2), pp. 155-200, 2016, DOI 10.1007/s10817-015-9335-3 (journal account of the same reconstruction work; cited as background, its annotation procedure is not compared here in detail).
- Val Breazu-Tannen, Thierry Coquand, Carl A. Gunter and Andre Scedrov, 'Inheritance as implicit coercion', Information and Computation 93(1), pp. 172-221, 1991, DOI 10.1016/0890-5401(91)90055-7: coherence of a coercion semantics, i.e. independence of the meaning from the derivation chosen. The toy has a single coercion Nat → Int, so uniqueness of coercion paths is trivial here; the toy's coherence question is whether coercion insertion commutes with the overloaded operators.
- Dmitriy Traytel, Stefan Berghofer and Tobias Nipkow, 'Extending Hindley-Milner type inference with coercive structural subtyping', APLAS 2011, LNCS 7078, pp. 89-104, Springer, 2011, DOI 10.1007/978-3-642-25318-8_10. Section 5.1: sin(n + n) with n : N, an overloaded + and real : N → R has the two type-correct completions sin(real(n + n)) and sin(real n + real n); the deterministic implementation picks the first, and the authors note that without coherence a system may silently prove a different theorem.
- Robert Pollack, 'How to believe a machine-checked proof', in G. Sambin and J. M. Smith (eds.), Twenty-Five Years of Constructive Type Theory, Oxford University Press, 1998, pp. 205-220, DOI 10.1093/oso/9780198501275.003.0013; preprint BRICS Report Series RS-97-18 (1997), DOI 10.7146/brics.v4i18.18945. Section 1.1: to believe a checked theorem one must read its formal statement and the definitions used hereditarily in stating it; Section 3.3 'What theorem is it?': library definitions must mean what they informally claim.
- Paula Severi and Erik Poll, 'Pure type systems with definitions', LFCS '94, LNCS 813, pp. 316-328, Springer, 1994, DOI 10.1007/3-540-58140-5_30: pure type systems extended with definitions and a reduction that unfolds them.
- Amokrane Saïbi, 'Typing algorithm in type theory with inheritance', POPL '97, pp. 292-301, ACM, 1997, DOI 10.1145/263699.263742: coercion inference for a type theory with inheritance.
- John C. Reynolds, 'Using category theory to design implicit conversions and generic operators', in N. D. Jones (ed.), Semantics-Directed Compiler Generation, LNCS 94, pp. 211-258, Springer, 1980, DOI 10.1007/3-540-10250-7_24: implicit conversions and generic operators organized so that conversions commute with the operators. Truncating Nat subtraction is the toy's operator that does not commute with Nat → Int.

**Observation date.** All evidence in this report (build, axiom audit, hashes, observations of Lean v4.34.1, and source and citation checks) was acquired on 2026-11-21.

## Revalidation

Requirements: `elan` (which installs the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

The script copies `lean/` to a temporary directory and runs `lake build`; scans the Lean sources for `sorry`, `admit`, `native_decide` and `axiom` declarations; runs a generated Lean program that computes, with `Lean.collectAxioms`, the axioms of every declaration of the library (allowed: `propext`, `Classical.choice`, `Quot.sound`); and recomputes, for every Lean name referenced by `results.json`, the SHA-256 of the statement (`repr` of its type) and of its definition closure (types and values of every package constant reachable from the statement, theorem bodies excluded), comparing them with `audit/statements.json`. It prints `REVALIDATED` on success. The package itself is not modified. Because `Toy.Render.LeanObservations` is part of the library, the same `lake build` also re-runs every `#guard_msgs` observation of the Lean printer; a changed printer output fails the build.

A shorter check of the build and of per-theorem axioms, with `lake` and no Python:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` (outside the library target) imports `Toy` and runs `#print axioms` for every theorem quoted in this report; each output line must list a subset of `propext`, `Classical.choice` and `Quot.sound`, or report that the declaration depends on no axioms. A change to any Lean definition reachable from a recorded statement changes its closure hash, so a failed hash comparison means the corresponding card must be re-examined. On another Lean version, the observations in `LeanObservations.lean` are the first thing to re-check: they record printer output, which is not stable across versions.
