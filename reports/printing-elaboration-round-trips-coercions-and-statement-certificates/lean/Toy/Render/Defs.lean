/-!
# Toy elaboration and printing: definitions (`Toy.Render`)

A small typed language with an implicit coercion `Nat → Int`, overloaded numerals
with a default type, and implicit type arguments on `+`, `-`, `=`; an untyped
surface syntax; a family of deterministic elaborators; printers parameterized by
which annotations they show; a declarative (relational) elaboration judgment; a
Boolean-valued semantics; and δ-unfolding of named definitions.

The model is a toy. It is meant to capture the *shape* of the gap between a kernel
term and its printed text in a proof assistant whose printer elides coercions,
implicit type arguments, and numeral types, and whose elaborator fills them back
in by defaults, unification, and coercion insertion. It does not model any real
printer or elaborator. "Text" in this package always means a value of the parsed
syntax tree `Stx`: lexing, operator precedence, parentheses, whitespace, binder
syntax and name shadowing are not modeled.
-/

namespace Toy.Render

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

/-! ## Readers that agree on fully annotated text -/

/-- `e'` agrees with `e` on fully annotated text. -/
def AgreeOnFull (e e' : Reader) : Prop :=
  ∀ S s, s.fullyAnnotated = true → e' S s = e S s

end Toy.Render
