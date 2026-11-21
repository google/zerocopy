# Edition-indexed drop scopes and inhabitedness-gated switch specialization: tail-expression and `if let` temporaries in a toy elaboration, and discriminant-read semantics for a toy switch rewrite (Lean 4)

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The package is a toy model in two parts that share no definitions. Part (a) (cards R1 to R4-window) is a small expression language whose elaboration-and-execution function `eval` is parameterized by two temporary-scope rule switches (`Rules`), with `Edition.e2021.rules = ⟨false, false⟩` and `Edition.e2024.rules = ⟨true, true⟩`. Part (b) (cards R5-eq to R6-all) is a switch on a discriminant read with two candidate semantics for tags of uninhabited variants (both kept open), a rejecting read and a synthetic `passThrough` boundary read for tags that denote no variant, and a rewrite modeled on the documented unreachable-enum-branching pass. These are statements about the toy model (Model–system relation: none proved); they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, Rust's operational semantics, MIR `Rvalue::Discriminant` and `SwitchInt`, or any Rust compiler, including rustc's unreachable-enum-branching pass. Connections to Rust documentation are separate `derived (modeling bridge)` remarks.

* **R1** (theorem, T1): For every toy program `e`: if no temporary escapes a block tail expression (`NoTailEscapingTemps e`) and no temporary escapes an `if let` scrutinee (`NoIfLetEscapingTemps e`), then the action list produced by `run` under the 2021 rules (`Edition.e2021.rules`) equals the one produced under the 2024 rules (`Edition.e2024.rules`); consequently the event traces (`trace`), the toy borrow-check verdicts (`accepts`) and the behaviours (`beh`) under the two editions agree.
* **R1-split** (theorem, T1): For every toy program `e` and every setting `b` of the other rule: if `NoTailEscapingTemps e`, then switching the tail rule leaves the action list produced by `run` unchanged (`run ⟨true, b⟩ e = run ⟨false, b⟩ e`); and if `NoIfLetEscapingTemps e`, then switching the `if let` rule leaves it unchanged (`run ⟨b, true⟩ e = run ⟨b, false⟩ e`).
* **R1-perm** (theorem, T1): For every toy program `e` and every two rule settings `R₁`, `R₂`: the action lists `run R₁ e` and `run R₂ e` are permutations of each other; `run R₁ e` contains no action twice; in `run R₁ e` the temporaries dropped (`dropTemps`: tag and borrow list of every `dropTemp`) are a permutation of the temporaries created (`mkTemps`: the same data of every `mkTemp`); and the actions other than temporary drops occur in the same order in `run R₁ e` and `run R₂ e`. Consequently (second theorem) under every setting each temporary created during the run occurs exactly once among the temporaries dropped. Rescoping thus reorders temporary drops, keeps the order of every other action, and adds or removes no action.
* **R1-match-tail** (counterexample, T1): For the program `matchInTailProg` (a `match` whose scrutinee creates a temporary with destructor event `dtor 1`, in the tail position of a block with one local whose destructor emits `dtor 0`), the 2021 trace is `[dtor 0, dtor 1]` and the 2024 trace is `[dtor 1, dtor 0]`; with the tail rule on and the `if let` rule off the trace is `[dtor 1, dtor 0]`, and with the tail rule off and the `if let` rule on it is `[dtor 0, dtor 1]`. For every rule setting, `eval` of a `match` is the setting-independent combinator `matchStep` (`eval_matchE_eq_matchStep`). Separately (`refuted_match_outside_blockTail_same_drop_point`, which refutes the stronger reading that a `match` scrutinee temporary has the same drop point in both editions whenever the `match` is outside block tail positions), `matchInIfLetScrutProg` (a `match` inside an `if let` scrutinee, with no block) satisfies `NoTailEscapingTemps`, violates `NoIfLetEscapingTemps`, and has 2021 trace `[out 1, dtor 0]` and 2024 trace `[dtor 0, out 1]`.
* **R2** (counterexample, T1): For the program `tailProg` (one local whose destructor emits `dtor 0`, and a tail temporary whose destructor emits `dtor 1`), the toy borrow check (`accepts`) accepts it under both editions, the 2021 trace is `[dtor 0, dtor 1]` and the 2024 trace is `[dtor 1, dtor 0]`; consequently neither edition's accepted behaviour is included in the other's (`BehIncl` fails in both directions). For `refCellTailProg` (a tail temporary borrowing the block's local), the toy borrow check accepts under the 2024 rules and rejects under the 2021 rules.
* **R3-match** (theorem, T1): For every toy program `e` and every rule setting `R`, the action list that `run` produces for the `match`-rewritten program `toMatch e` under `R` equals the action list of `e` under `R` with the `if let` rule set to its 2021 setting and the tail rule unchanged (`run R (toMatch e) = run { R with ifLet2024 := false } e`). The `if let` rule is observable: for `ifLetElseProg` (an `if let` whose scrutinee temporary's destructor emits `dtor 0`, whose pattern does not match and whose `else` block emits `out 1`) the 2021 trace is `[out 1, dtor 0]` and the 2024 trace is `[dtor 0, out 1]`.
* **R3-migration** (theorem, T1): For every toy program `e`: if `NoTailEscapingTemps e`, then the action list that `run` produces for `toMatch e` under the 2024 rules equals the action list of `e` under the 2021 rules.
* **R4-if** (theorem, T1): For every toy program `e`: if every pair of actions that occur in opposite orders in the action lists produced by `run` under the 2021 and the 2024 rules (`Flipped e a b`) has commuting event lists (`Commute a b`, equality of the words `a.events ++ b.events` and `b.events ++ a.events`), then the 2021 and 2024 event traces of `e` are equal.
* **R4-site** (characterization, T1): For every list `ls` of local destructor event lists and every list `ds` of tail-temporary destructor event lists, the program `tailSiteProg ls ds` has equal 2021 and 2024 traces iff `dropOrderEvents ls ++ dropOrderEvents ds = dropOrderEvents ds ++ dropOrderEvents ls`; and for every `ds` and every list `es` of output numbers, `elseSiteProg ds es` has equal traces iff `es.map Ev.out ++ dropOrderEvents ds = dropOrderEvents ds ++ es.map Ev.out`. If moreover every event in `dropOrderEvents ds` is a `dtor` event, the latter condition holds iff `es = []` or `dropOrderEvents ds = []` (`elseSite_commute_iff_of_dtorOnly`).
* **R4-not-necessary** (counterexample, T1): For `ababProg` (two locals and two tail temporaries whose drops spell `[dtor 0, dtor 1]` on each side), the 2021 and 2024 traces are equal, yet the temporary drop `ababTempDrop` and the local drop `ababLocalDrop` occur in opposite orders under the two editions and their event lists do not commute; per-action commutation is therefore not necessary for trace preservation in the toy.
* **R4-window** (counterexample, T1): For `nestedTailProg` (a tail temporary created in the tail of an inner block with no locals, the inner block being the tail of an outer block with one local), the traces differ (`[dtor 1, dtor 0]` under 2021, `[dtor 0, dtor 1]` under 2024); for `thenBranchProg` (an `if let` with a matching pattern followed in the same expression by `out 1`), the traces differ (`[out 1, dtor 0]` under 2021, `[dtor 0, out 1]` under 2024); and for `siblingTailProg` (a block with no locals whose tail creates a temporary, followed in the same expression by `out 1`), the traces differ (`[out 1, dtor 0]` under 2021, `[dtor 0, out 1]` under 2024).
* **R5-eq** (theorem, T1): For every tag count `n`, allowed-tag predicate `A`, read-UB predicate `R` and payload predicate `P`: if every tag `t` that is not an allowed tag (`allowedTag n A t = false`) is read as undefined behaviour (`R t = true`), then for every switch `sw` and tag `t`, `exec R P (specializeSwitch n A sw) t = exec R P sw t`. In particular (second theorem), under the discriminant semantics `rejectBoth` (reading an uninhabited-variant tag or an invalid tag is undefined behaviour), for every enum `E`, switch `sw` and tag `t`, the enum-derived specialization `specializeEnum E sw` has the same outcome as `sw`.
* **R5-iff** (characterization, T1): For every `n`, `A`, `R`, `P`: the specialized switch's outcome refines the original's (`Refines`: the original is undefined behaviour or the two outcomes are equal) for every switch and every tag iff every tag that is not an allowed tag is read as undefined behaviour.
* **R5-iff-shapes** (characterization, T1): For every `n`, `A`, `R`, `P`: `pruneArms` alone (every explicit arm whose value is not an allowed tag is retargeted to `unreachable`) refines the original for every switch and tag iff every non-allowed tag is read as undefined behaviour; and `lastVariantTakesWildcard` alone (if zero allowed tags lack an explicit arm, the wildcard becomes `unreachable`; if exactly one allowed tag `j` lacks one, an arm `j ↦ otherwise` is appended and the wildcard becomes `unreachable`; otherwise the switch is unchanged) refines the original for every switch and tag iff the same condition holds.
* **R5-valid** (characterization, T1): For every discriminant semantics `D`: the enum-derived specialization refines the original for every enum, every switch and every valid tag (`t < E.length`) iff `D` rejects uninhabited-variant tags (`D.uninh = .rejectUninhabited`).
* **R5-permissive** (characterization, T1): For every invalid-tag choice `inv` and every enum `E`, under the permissive uninhabited-tag semantics `⟨.permissive, inv⟩`: the enum-derived specialization refines the original for every switch and every valid tag iff every variant of `E` is inhabited.
* **R5-cx** (counterexample, T1): Under `permissiveRejectInvalid`: for `deadNicheEnum` with `deadNicheSwitch`, the stored value 2 decodes (toy niche encoding `exampleNiche`) to the uninhabited variant 1, the original switch continues normally (`ret 1`) and the specialized switch is undefined behaviour; and for the enum `[true, false, true, true]` with explicit arms `0 ↦ goto 1` and `2 ↦ goto 2` and wildcard `goto 3`, on the uninhabited tag 1 the original switch continues normally (`ret 3`) and the specialized switch is undefined behaviour (`ub`).
* **R6-all** (characterization, T1): For every discriminant semantics `D`: the enum-derived specialization refines the original for every enum, every switch and every tag, valid or invalid, iff `D` rejects both uninhabited-variant tags and invalid tags. Rejecting uninhabited-variant tags alone does not suffice (second theorem): under `⟨.rejectUninhabited, .passThrough⟩`, for the one-variant enum `[true]` and the switch with no explicit arm and wildcard `goto 0`, the invalid tag 1 yields `ret 0` in the original and undefined behaviour after specialization.

Non-claims for every card are listed under **Boundaries** (non-claims first); read them before relying on a result. The five theorems named `refuted_*` (`refuted_stmtTempsProg_three_temp_drops`, `refuted_match_outside_blockTail_same_drop_point`, `refuted_emptyTailDtors_give_run_eq`, `refuted_specializeSwitch_retargets_every_nonAllowed_tag`, `refuted_allInhabited_specializeEnum_changes_nothing`) refute stronger readings that the toy results might suggest; they are collected under **Boundaries**, subsection *Refuted stronger readings*. `refuted_match_outside_blockTail_same_drop_point` is one of the main statements of R1-match-tail; the other four are auxiliary theorems cited by R1, R3-migration, R5-eq and R5-permissive. All five are statements about the toy model; they neither establish nor refute the corresponding claims about Rust or rustc.

## Applicability

### Model fidelity

The package is a toy model in two parts.

Part (a) is a small expression language with blocks, `let`, tail expressions, `if let`, `match` and calls that create temporaries whose destructors emit events; one elaboration-and-execution function `eval` is parameterized by two rule switches (`Rules`), and the editions are `Edition.e2021.rules = ⟨false, false⟩` and `Edition.e2024.rules = ⟨true, true⟩`. The rules are meant to capture the temporary-scope changes documented in the Edition Guide and RFC 3606; this connection is `derived (modeling bridge)` prose, not a proved relation. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.

Part (b) is a switch on a discriminant read with two candidate semantics for tags of uninhabited variants (kept open, as the documentation of `Rvalue::Discriminant` says the validity requirements of the read are undecided), a rejecting read and a synthetic `passThrough` boundary read for tags that denote no variant, and the rewrite documented in the source of rustc's unreachable-enum-branching pass; this connection is `derived (modeling bridge)` prose, not a proved relation. These are statements about the toy switch model; they neither establish nor refute the corresponding claims about Rust's operational semantics, MIR `Rvalue::Discriminant` and `SwitchInt`, or rustc's unreachable-enum-branching pass. Model–system relation: none proved.

The two parts share no definitions; each card states the scope of its own part.

Truncating operations and degenerate edges: `NicheEnc.decode` uses `Nat` truncated subtraction `v - N.nicheStart`, guarded by `N.nicheStart ≤ v`, and no wrapping arithmetic occurs in the package; with an empty niche range (`nicheHi < nicheLo`) every stored value decodes to the untagged variant (`decode_of_nicheHi_lt_nicheLo`). An `Enum` may be empty, in which case every tag takes the invalid-tag branch of `readUB` (`readUB_emptyEnum`); `allowedTag 0 A t = false` for every `t`; `remainingAllowed` may be empty, in which case `lastVariantTakesWildcard` makes the wildcard `unreachable` (`lastVariantTakesWildcard_no_remaining`).

### Known gaps (modeling choices, not findings)

* **Part (a).** Not modeled: temporary lifetime extension; per-block editions for macro-generated code (RFC 3606 applies the tail rule according to the edition of a block's `{}` tokens; in the toy the rule setting is per program); `else if let` chains and `let` chains; closures, `async` and `const` blocks; destructuring assignment; unwinding and panics; loops and `while let`; `if` conditions, match guards and lazy boolean operators. Branch outcomes of `if let` and `match` are fixed by a boolean in the syntax (`hit`), scrutinee values are abstracted, and destructors cannot change state. `run` treats its argument as a whole function body without adding a block around it, and in a `letS` statement the initializer's temporaries are dropped before the local is bound. The toy borrow check `borrowOK` tracks live locals as a multiset of `Nat` names, not binders (shadowing hides an inner local's drop, `borrowOK_shadowing_limitation`), and models no `&mut` exclusivity, no non-lexical lifetimes and no borrows of temporaries.
* **Part (b).** The toy switch has no memory, aliasing model, partial moves or uninitialized bytes, and no MIR context (no statements between the discriminant read and the switch, no `Assume`, no cleanup blocks); tags equal variant indices (no custom discriminant values and no tagless single-variant layouts); explicit arms may repeat a value (the first one is selected); the pass's own applicability conditions are not modeled. `InvalidRead.passThrough` is a synthetic modeling boundary of this package, not a candidate semantics taken from Rust documentation. The toy niche decoder `NicheEnc.decode` uses guarded truncated subtraction instead of the documented wrapping subtraction.

### Relation to nearby corpus packages

Cited in prose; nothing is repeated or imported. The published drop-flag package (`drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction`) treats exactly-once destruction within a fixed scope assignment, whereas this package varies where temporaries' scopes end; the published drop-check package (`drop-check-may-dangle-and-destructor-soundness-for-generic-containers`) treats destructor soundness with respect to lifetimes, which is not modeled here; the published niche package (`enum-niche-layout-guarantees-and-validity-invariants`) treats niche layouts for inhabited variants and does not model uninhabited variants.

### Toolchain and project

* Lean `leanprover/lean4` release `v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`); no Mathlib; `lean/lakefile.toml` declares one `[[lean_lib]]` (`ToyDropScope`, Lake package `toy_drop_scope`) and no `[[require]]`.
* Namespace `Toy.DropScope`. Modules under `lean/ToyDropScope/`: `Syntax` (events, editions, rule switches, expressions, blocks, actions), `Semantics` (`eval`, `evalBlock`, `run`, `trace`, the toy borrow check, `beh`, `BehIncl`, `toMatch`, the escape checks, `Before`/`Flipped`/`Commute`), `Switch` (the Part (b) switch model), `Examples` (proved positive and negative examples for every definition, and named programs), `DropResults` (Part (a) results), `SwitchResults` (Part (b) results). `lean/RevalidationAudit.lean` is outside the library target.
* Every main result, definition example, counterexample, non-vacuity witness and positive control is fully proved (kernel-checked; closed instances mostly by `decide`).

### Subjects

`REPORT.json` lists the Lean release used to check every theorem; the pinned revisions of the Rust Edition Guide, the RFC repository (RFC 3606 and RFC 66), the Rust Reference, rust-lang/rust (documentation and source of the unreachable-enum-branching pass, the `Rvalue::Discriminant` documentation and the `TagEncoding::Niche` documentation) and MiniRust, whose texts are quoted for the `derived (modeling bridge)` remarks and as related work; and the published works cited as prior art (bibliographic records checked; full texts not inspected unless a card says so). The report concerns the toy model; it states no formal relation between the toy and any of these subjects (Model–system relation: none proved). The issue rust-lang/rust#91095, linked from the `Rvalue::Discriminant` documentation, is an open issue mentioned in prose for orientation; it is not a subject and is not relied on.

## Findings

### Definitions (verbatim)

All declarations live in namespace `Toy.DropScope` (files under `lean/ToyDropScope/`). Every definition below is quoted verbatim with its file and line range. The intended positive and negative examples named in each entry are proved theorems, quoted under *Auxiliary declarations cited by name*.

#### `Ev`

Observable events: outputs (`out`, standing for any side effect) and destructor events (`dtor`). Traces are `List Ev`.

```lean
-- lean/ToyDropScope/Syntax.lean:13-16
inductive Ev where
  | out (n : Nat)
  | dtor (n : Nat)
  deriving DecidableEq, Repr
```

#### `Edition`

The two editions compared.

```lean
-- lean/ToyDropScope/Syntax.lean:19-22
inductive Edition where
  | e2021
  | e2024
  deriving DecidableEq, Repr
```

#### `Rules`

The two independent narrowing rules (tail expression, `if let`) as booleans.

```lean
-- lean/ToyDropScope/Syntax.lean:29-32
structure Rules where
  tail2024 : Bool
  ifLet2024 : Bool
  deriving DecidableEq, Repr
```

#### `Edition.rules`

2021 has neither rule, 2024 has both. Examples: `edition_rules_e2024` (positive), `edition_rules_e2021_ne_e2024` (negative).

```lean
-- lean/ToyDropScope/Syntax.lean:35-37
def Edition.rules : Edition → Rules
  | .e2021 => ⟨false, false⟩
  | .e2024 => ⟨true, true⟩
```

#### `Expr`

Toy expressions (meant to capture: blocks, tail expressions, `if let`, `match`, and calls creating temporaries in place contexts). Pattern outcomes are fixed by a boolean in the syntax.

```lean
-- lean/ToyDropScope/Syntax.lean:52-59
inductive Expr where
  | unit
  | out (n : Nat)
  | temp (dt : List Ev) (bs : List Nat)
  | seq (a b : Expr)
  | block (b : Block)
  | ifLet (hit : Bool) (scrut thn els : Expr)
  | matchE (hit : Bool) (scrut arm₁ arm₂ : Expr)
```

#### `Block`

Toy blocks: a tail expression preceded by `let` and expression statements.

```lean
-- lean/ToyDropScope/Syntax.lean:67-71
inductive Block where
  | tail (e : Expr)
  | letS (x : Nat) (dl : List Ev) (init : Expr) (rest : Block)
  | exprS (e : Expr) (rest : Block)
end
```

#### `Tag`

Syntax positions; every action carries the position that produced it, which makes actions unique within a run.

```lean
-- lean/ToyDropScope/Syntax.lean:75
abbrev Tag := List Nat
```

#### `Act`

Executed actions: bind/drop of locals, creation/drop of temporaries, outputs.

```lean
-- lean/ToyDropScope/Syntax.lean:80-86
inductive Act where
  | out (tag : Tag) (n : Nat)
  | mkLocal (tag : Tag) (x : Nat)
  | dropLocal (tag : Tag) (x : Nat) (dl : List Ev)
  | mkTemp (tag : Tag) (bs : List Nat)
  | dropTemp (tag : Tag) (bs : List Nat) (dt : List Ev)
  deriving DecidableEq, Repr
```

#### `Act.events`

The observable events of an action.

```lean
-- lean/ToyDropScope/Syntax.lean:90-95
def Act.events : Act → List Ev
  | .out _ n => [.out n]
  | .mkLocal _ _ => []
  | .dropLocal _ _ dl => dl
  | .mkTemp _ _ => []
  | .dropTemp _ _ dt => dt
```

#### `Pending`

A live temporary awaiting the end of its temporary scope.

```lean
-- lean/ToyDropScope/Syntax.lean:98-102
structure Pending where
  tag : Tag
  bs : List Nat
  dt : List Ev
  deriving DecidableEq, Repr
```

#### `dropAll`

Drops pending temporaries in reverse creation order.

```lean
-- lean/ToyDropScope/Semantics.lean:11-12
def dropAll (ps : List Pending) : List Act :=
  ps.reverse.map fun q => .dropTemp q.tag q.bs q.dt
```

#### `closeScope`

Closes a temporary scope.

```lean
-- lean/ToyDropScope/Semantics.lean:16-17
def closeScope (r : List Act × List Pending) : List Act :=
  r.1 ++ dropAll r.2
```

#### `eval`

Elaboration and execution in one pass (meant to capture the documented temporary-scope rules: statements, `if let` branches, `match` arms and the whole function are temporary scopes; with `tail2024`, block tail expressions; with `ifLet2024`, an `if let` scrutinee with its consequent; a `match` scrutinee never). Examples: `trace_tailProg_e2021`, `trace_tailProg_e2024`, `trace_tailProg_e2024_ne_local_first`, `trace_letInitTemp_both`, `trace_ifLetElseProg_e2024`, `trace_ifLetThen_e2024`, `trace_ifLetElseProg_e2021_ne_scrutinee_first`, `trace_two_temps_reverse`.

```lean
-- lean/ToyDropScope/Semantics.lean:29-48
def eval (R : Rules) (p : Tag) : Expr → List Act × List Pending
  | .unit => ([], [])
  | .out n => ([.out p n], [])
  | .temp dt bs => ([.mkTemp p bs], [⟨p, bs, dt⟩])
  | .seq a b =>
      let ra := eval R (0 :: p) a
      let rb := eval R (1 :: p) b
      (ra.1 ++ rb.1, ra.2 ++ rb.2)
  | .block b => evalBlock R (0 :: p) b
  | .ifLet hit s a b =>
      let rs := eval R (0 :: p) s
      let body := if hit then closeScope (eval R (1 :: p) a) else closeScope (eval R (2 :: p) b)
      if R.ifLet2024 then
        (if hit then rs.1 ++ body ++ dropAll rs.2 else rs.1 ++ dropAll rs.2 ++ body, [])
      else
        (rs.1 ++ body, rs.2)
  | .matchE hit s a b =>
      let rs := eval R (0 :: p) s
      let body := if hit then closeScope (eval R (1 :: p) a) else closeScope (eval R (2 :: p) b)
      (rs.1 ++ body, rs.2)
```

#### `evalBlock`

Block elaboration: locals drop at block end in reverse declaration order; without `tail2024`, tail temporaries stay pending past the block end; in `letS`, the initializer's temporaries are dropped before the local is bound (an order the toy borrow check can observe and `trace` cannot, since `mkLocal` emits no event).

```lean
-- lean/ToyDropScope/Semantics.lean:57-67
def evalBlock (R : Rules) (p : Tag) : Block → List Act × List Pending
  | .tail e =>
      let r := eval R (0 :: p) e
      if R.tail2024 then (closeScope r, []) else r
  | .letS x dl i rest =>
      let rr := evalBlock R (1 :: p) rest
      (closeScope (eval R (0 :: p) i) ++ [.mkLocal p x] ++ rr.1 ++ [.dropLocal p x dl], rr.2)
  | .exprS e rest =>
      let rr := evalBlock R (1 :: p) rest
      (closeScope (eval R (0 :: p) e) ++ rr.1, rr.2)
end
```

#### `run`

Whole-program execution: the argument is treated as an entire function body, without an added block. Example: `run_tailProg`.

```lean
-- lean/ToyDropScope/Semantics.lean:72-73
def run (R : Rules) (e : Expr) : List Act :=
  closeScope (eval R [] e)
```

#### `trace`

The event trace of a program.

```lean
-- lean/ToyDropScope/Semantics.lean:76-77
def trace (R : Rules) (e : Expr) : List Ev :=
  (run R e).flatMap Act.events
```

#### `Act.isDropTemp`

Whether an action drops a temporary. Examples: `isDropTemp_dropTemp` (positive), `not_isDropTemp_dropLocal` (negative).

```lean
-- lean/ToyDropScope/Semantics.lean:80-82
def Act.isDropTemp : Act → Bool
  | .dropTemp _ _ _ => true
  | _ => false
```

#### `Act.mkTempKey?`

The tag and borrow list of a temporary-creating action.

```lean
-- lean/ToyDropScope/Semantics.lean:85-87
def Act.mkTempKey? : Act → Option (Tag × List Nat)
  | .mkTemp t bs => some (t, bs)
  | _ => none
```

#### `Act.dropTempKey?`

The tag and borrow list of a temporary-dropping action.

```lean
-- lean/ToyDropScope/Semantics.lean:90-92
def Act.dropTempKey? : Act → Option (Tag × List Nat)
  | .dropTemp t bs _ => some (t, bs)
  | _ => none
```

#### `mkTemps`

The temporaries created in an action list. Examples: `mkTemps_dropTemps_tailProg` (positive), `dropTemps_mkTemp_mkTemps_dropTemp` (negative).

```lean
-- lean/ToyDropScope/Semantics.lean:95
def mkTemps (l : List Act) : List (Tag × List Nat) := l.filterMap Act.mkTempKey?
```

#### `dropTemps`

The temporaries dropped in an action list. Examples as for `mkTemps`.

```lean
-- lean/ToyDropScope/Semantics.lean:99
def dropTemps (l : List Act) : List (Tag × List Nat) := l.filterMap Act.dropTempKey?
```

#### `borrowOK`

The toy borrow check over an action list (meant to capture one rule, 'a temporary may not outlive a local it borrows'; no other borrow-checking rule is modeled). Borrows refer to local names, not binders, so shadowing can hide a dropped inner local (`borrowOK_shadowing_limitation`). Examples: `accepts_refCellTailProg_e2024`, `accepts_refCellTailProg_e2021`, `accepts_unboundBorrow`.

```lean
-- lean/ToyDropScope/Semantics.lean:110-116
def borrowOK : List Nat → List Act → Bool
  | _, [] => true
  | live, .mkLocal _ x :: as => borrowOK (x :: live) as
  | live, .dropLocal _ x _ :: as => borrowOK (live.erase x) as
  | live, .mkTemp _ bs :: as => bs.all live.contains && borrowOK live as
  | live, .dropTemp _ bs _ :: as => bs.all live.contains && borrowOK live as
  | live, .out _ _ :: as => borrowOK live as
```

#### `accepts`

Borrow-check verdict of a program under a setting.

```lean
-- lean/ToyDropScope/Semantics.lean:119-120
def accepts (R : Rules) (e : Expr) : Bool :=
  borrowOK [] (run R e)
```

#### `beh`

Accepted behaviour: the trace if accepted, `none` otherwise.

```lean
-- lean/ToyDropScope/Semantics.lean:124-125
def beh (R : Rules) (e : Expr) : Option (List Ev) :=
  if accepts R e then some (trace R e) else none
```

#### `BehIncl`

Inclusion of accepted behaviours between settings. Examples: `behIncl_refl`, `not_behIncl_e2021_e2024_at_tailProg`.

```lean
-- lean/ToyDropScope/Semantics.lean:130-131
def BehIncl (R₁ R₂ : Rules) : Prop :=
  ∀ e tr, beh R₁ e = some tr → beh R₂ e = some tr
```

#### `toMatch`

The rewrite `if let P = s { a } else { b }` to `match s { P => a, _ => b }`, everywhere. Examples: `toMatch_ifLetElseProg`, `toMatch_ifLetElseProg_ne`.

```lean
-- lean/ToyDropScope/Semantics.lean:136-143
def toMatch : Expr → Expr
  | .unit => .unit
  | .out n => .out n
  | .temp dt bs => .temp dt bs
  | .seq a b => .seq (toMatch a) (toMatch b)
  | .block b => .block (toMatchBlock b)
  | .ifLet hit s a b => .matchE hit (toMatch s) (toMatch a) (toMatch b)
  | .matchE hit s a b => .matchE hit (toMatch s) (toMatch a) (toMatch b)
```

#### `toMatchBlock`

`toMatch` on blocks.

```lean
-- lean/ToyDropScope/Semantics.lean:146-150
def toMatchBlock : Block → Block
  | .tail e => .tail (toMatch e)
  | .letS x dl i r => .letS x dl (toMatch i) (toMatchBlock r)
  | .exprS e r => .exprS (toMatch e) (toMatchBlock r)
end
```

#### `noEscape`

Syntactic check: no temporary of `e` is in a position from which it stays pending past `e` under the 2021 rules. Examples: `noEscape_letInit`, `noEscape_matchArms`, `noEscape_temp`, `noEscape_ifLetScrut`.

```lean
-- lean/ToyDropScope/Semantics.lean:158-165
def noEscape : Expr → Bool
  | .unit => true
  | .out _ => true
  | .temp _ _ => false
  | .seq a b => noEscape a && noEscape b
  | .block b => noEscapeBlock b
  | .ifLet _ s _ _ => noEscape s
  | .matchE _ s _ _ => noEscape s
```

#### `noEscapeBlock`

`noEscape` on blocks.

```lean
-- lean/ToyDropScope/Semantics.lean:168-172
def noEscapeBlock : Block → Bool
  | .tail e => noEscape e
  | .letS _ _ _ r => noEscapeBlock r
  | .exprS _ r => noEscapeBlock r
end
```

#### `tailsClean`

Every block tail expression passes `noEscape`.

```lean
-- lean/ToyDropScope/Semantics.lean:176-183
def tailsClean : Expr → Bool
  | .unit => true
  | .out _ => true
  | .temp _ _ => true
  | .seq a b => tailsClean a && tailsClean b
  | .block b => tailsCleanBlock b
  | .ifLet _ s a b => tailsClean s && tailsClean a && tailsClean b
  | .matchE _ s a b => tailsClean s && tailsClean a && tailsClean b
```

#### `tailsCleanBlock`

`tailsClean` on blocks.

```lean
-- lean/ToyDropScope/Semantics.lean:186-190
def tailsCleanBlock : Block → Bool
  | .tail e => noEscape e && tailsClean e
  | .letS _ _ i r => tailsClean i && tailsCleanBlock r
  | .exprS e r => tailsClean e && tailsCleanBlock r
end
```

#### `ifLetsClean`

Every `if let` scrutinee passes `noEscape`.

```lean
-- lean/ToyDropScope/Semantics.lean:194-201
def ifLetsClean : Expr → Bool
  | .unit => true
  | .out _ => true
  | .temp _ _ => true
  | .seq a b => ifLetsClean a && ifLetsClean b
  | .block b => ifLetsCleanBlock b
  | .ifLet _ s a b => noEscape s && ifLetsClean s && ifLetsClean a && ifLetsClean b
  | .matchE _ s a b => ifLetsClean s && ifLetsClean a && ifLetsClean b
```

#### `ifLetsCleanBlock`

`ifLetsClean` on blocks.

```lean
-- lean/ToyDropScope/Semantics.lean:204-208
def ifLetsCleanBlock : Block → Bool
  | .tail e => ifLetsClean e
  | .letS _ _ i r => ifLetsClean i && ifLetsCleanBlock r
  | .exprS e r => ifLetsClean e && ifLetsCleanBlock r
end
```

#### `NoTailEscapingTemps`

Hypothesis class of R1 (tail part). Examples: `noTailEscapingTemps_stmtTempsProg`, `not_noTailEscapingTemps_tailProg`, `not_noTailEscapingTemps_nested`.

```lean
-- lean/ToyDropScope/Semantics.lean:212
def NoTailEscapingTemps (e : Expr) : Prop := tailsClean e = true
```

#### `NoIfLetEscapingTemps`

Hypothesis class of R1 (`if let` part). Examples: `noIfLetEscapingTemps_stmtTempsProg`, `not_noIfLetEscapingTemps_ifLetElseProg`.

```lean
-- lean/ToyDropScope/Semantics.lean:216
def NoIfLetEscapingTemps (e : Expr) : Prop := ifLetsClean e = true
```

#### `Before`

Order of two actions in an action list.

```lean
-- lean/ToyDropScope/Semantics.lean:219-220
def Before (l : List Act) (a b : Act) : Prop :=
  ∃ i j : Nat, i < j ∧ l[i]? = some a ∧ l[j]? = some b
```

#### `Flipped`

Two actions occur in opposite orders under the 2021 and the 2024 rules. Examples: `flipped_tailProg`, `not_flipped_tailProg_mkLocal`.

```lean
-- lean/ToyDropScope/Semantics.lean:224-225
def Flipped (e : Expr) (a b : Act) : Prop :=
  Before (run Edition.e2021.rules e) a b ∧ Before (run Edition.e2024.rules e) b a
```

#### `Commute`

Two actions' event lists commute as words. Examples: `commute_same_event`, `not_commute_tailProg`.

```lean
-- lean/ToyDropScope/Semantics.lean:228-229
def Commute (a b : Act) : Prop :=
  a.events ++ b.events = b.events ++ a.events
```

#### `Arm`

Switch targets.

```lean
-- lean/ToyDropScope/Switch.lean:20-24
inductive Arm where
  | unreachable
  | goto (k : Nat)
  | usePayload (k : Nat)
  deriving DecidableEq, Repr
```

#### `Switch`

A switch: explicit arms (searched in order; values may repeat) and a wildcard.

```lean
-- lean/ToyDropScope/Switch.lean:28-31
structure Switch where
  arms : List (Nat × Arm)
  otherwise : Arm
  deriving DecidableEq, Repr
```

#### `Outcome`

Undefined behaviour or normal continuation.

```lean
-- lean/ToyDropScope/Switch.lean:34-37
inductive Outcome where
  | ub
  | ret (k : Nat)
  deriving DecidableEq, Repr
```

#### `Switch.target`

Arm selection. Examples: `target_orderingSwitch_0`, `target_orderingSwitch_2`.

```lean
-- lean/ToyDropScope/Switch.lean:41-44
def Switch.target (sw : Switch) (t : Nat) : Arm :=
  match sw.arms.find? (fun a => a.1 == t) with
  | some a => a.2
  | none => sw.otherwise
```

#### `runArm`

Running a target; payload use is undefined behaviour unless `payloadOK t`. Examples: `runArm_usePayload_ok` (positive), `runArm_usePayload_bad` (negative).

```lean
-- lean/ToyDropScope/Switch.lean:48-51
def runArm (payloadOK : Nat → Bool) (t : Nat) : Arm → Outcome
  | .unreachable => .ub
  | .goto k => .ret k
  | .usePayload k => if payloadOK t then .ret k else .ub
```

#### `exec`

Discriminant read then switch. Examples: `exec_ok`, `exec_readUB`.

```lean
-- lean/ToyDropScope/Switch.lean:56-57
def exec (readUB payloadOK : Nat → Bool) (sw : Switch) (t : Nat) : Outcome :=
  if readUB t then .ub else runArm payloadOK t (sw.target t)
```

#### `Refines`

Outcome refinement (undefined behaviour in the source admits anything). Examples: `refines_ub`, `refines_ret_eq` (positive); `not_refines_ub_ret`, `not_refines_ret_ne` (negative).

```lean
-- lean/ToyDropScope/Switch.lean:61-62
def Refines (tgt src : Outcome) : Prop :=
  src = .ub ∨ tgt = src
```

#### `allowedTag`

The allowed tags: variant tags below `n` satisfying `A`. Examples: `allowedTag_pos`, `allowedTag_neg`.

```lean
-- lean/ToyDropScope/Switch.lean:66-67
def allowedTag (n : Nat) (A : Nat → Bool) (t : Nat) : Bool :=
  decide (t < n) && A t
```

#### `pruneArms`

Shape 1 of the documented pass. Examples: `pruneArms_example`, `pruneArms_keeps_allowed`.

```lean
-- lean/ToyDropScope/Switch.lean:71-72
def pruneArms (n : Nat) (A : Nat → Bool) (sw : Switch) : Switch :=
  { sw with arms := sw.arms.map fun a => if allowedTag n A a.1 then a else (a.1, .unreachable) }
```

#### `remainingAllowed`

Allowed tags without an explicit arm. Examples: `remainingAllowed_orderingSwitch`, `remainingAllowed_all_covered`.

```lean
-- lean/ToyDropScope/Switch.lean:75-76
def remainingAllowed (n : Nat) (A : Nat → Bool) (sw : Switch) : List Nat :=
  (List.range n).filter fun i => A i && !(sw.arms.any fun a => a.1 == i)
```

#### `lastVariantTakesWildcard`

Shape 2 of the documented pass, with two changing branches (zero or exactly one allowed tag without an explicit arm). Examples: `lastVariantTakesWildcard_orderingSwitch` (one remaining; the pass's own documentation example), `lastVariantTakesWildcard_no_remaining` (zero remaining), `lastVariantTakesWildcard_two_remaining` (two remaining: unchanged).

```lean
-- lean/ToyDropScope/Switch.lean:84-88
def lastVariantTakesWildcard (n : Nat) (A : Nat → Bool) (sw : Switch) : Switch :=
  match remainingAllowed n A sw with
  | [] => { sw with otherwise := .unreachable }
  | [j] => { arms := sw.arms ++ [(j, sw.otherwise)], otherwise := .unreachable }
  | _ :: _ :: _ => sw
```

#### `specializeSwitch`

Shape 1 then shape 2.

```lean
-- lean/ToyDropScope/Switch.lean:92-93
def specializeSwitch (n : Nat) (A : Nat → Bool) (sw : Switch) : Switch :=
  lastVariantTakesWildcard n A (pruneArms n A sw)
```

#### `Enum`

A toy enum: inhabitedness per variant; variant `i` has tag `i`.

```lean
-- lean/ToyDropScope/Switch.lean:97
abbrev Enum := List Bool
```

#### `Enum.inhabitedTag`

Tag of an inhabited variant (false for invalid tags).

```lean
-- lean/ToyDropScope/Switch.lean:100-101
def Enum.inhabitedTag (E : Enum) (t : Nat) : Bool :=
  E.getD t false
```

#### `UninhabitedRead`

The two candidate semantics for uninhabited-variant tags (`rejectUninhabited`, `permissive`), both kept open.

```lean
-- lean/ToyDropScope/Switch.lean:106-109
inductive UninhabitedRead where
  | rejectUninhabited
  | permissive
  deriving DecidableEq, Repr
```

#### `InvalidRead`

Choices for tags that denote no variant (`rejectInvalid`, and the synthetic boundary `passThrough`).

```lean
-- lean/ToyDropScope/Switch.lean:115-118
inductive InvalidRead where
  | rejectInvalid
  | passThrough
  deriving DecidableEq, Repr
```

#### `DiscrSem`

A discriminant-read semantics.

```lean
-- lean/ToyDropScope/Switch.lean:122-125
structure DiscrSem where
  uninh : UninhabitedRead
  invalid : InvalidRead
  deriving DecidableEq, Repr
```

#### `readUB`

Whether a discriminant read is undefined behaviour. Examples: `readUB_rejectUninhabited`, `readUB_permissive`, `readUB_inhabited`, `readUB_invalid`; degenerate edge `readUB_emptyEnum`.

```lean
-- lean/ToyDropScope/Switch.lean:129-131
def readUB (D : DiscrSem) (E : Enum) (t : Nat) : Bool :=
  if t < E.length then D.uninh == .rejectUninhabited && !E.inhabitedTag t
  else D.invalid == .rejectInvalid
```

#### `runSwitch`

A switch on an enum value under a discriminant semantics.

```lean
-- lean/ToyDropScope/Switch.lean:135-136
def runSwitch (D : DiscrSem) (E : Enum) (sw : Switch) (t : Nat) : Outcome :=
  exec (readUB D E) E.inhabitedTag sw t
```

#### `specializeEnum`

The specialization with the inhabited tags as allowed set, as the documented pass computes it from the layout.

```lean
-- lean/ToyDropScope/Switch.lean:140-141
def specializeEnum (E : Enum) (sw : Switch) : Switch :=
  specializeSwitch E.length E.inhabitedTag sw
```

#### `NicheEnc`

A toy niche encoding (no wrapping).

```lean
-- lean/ToyDropScope/Switch.lean:147-152
structure NicheEnc where
  untagged : Nat
  nicheLo : Nat
  nicheHi : Nat
  nicheStart : Nat
  deriving DecidableEq, Repr
```

#### `NicheEnc.decode`

Decoding a stored value (guarded truncated subtraction). Examples: `decode_exampleNiche`, `decode_exampleNiche_untagged`; degenerate edge `decode_of_nicheHi_lt_nicheLo`.

```lean
-- lean/ToyDropScope/Switch.lean:155-157
def NicheEnc.decode (N : NicheEnc) (v : Nat) : Nat :=
  if N.nicheStart ≤ v ∧ v - N.nicheStart + N.nicheLo ≤ N.nicheHi then v - N.nicheStart + N.nicheLo
  else N.untagged
```

### Cards

Unfolded renderings marked `explicit` are Lean terms definitionally equal to the quoted statement (checked by elaboration in the theorem's context); renderings marked prose are explanations. Proofs are elided. In every hypothesis ledger, `tight` means: the named counterexample theorem exhibits an instance, in the stated witness class, satisfying all the other hypotheses of the theorem the hypothesis belongs to, in which the conclusion fails; on a card with several theorems, the hypothesis column names the theorem or theorems the hypothesis belongs to, and where two counterexample theorems are named they concern the same instance and together show this for each theorem named. It does not mean the hypothesis is necessary outside that class.

#### R1 — theorem, T1

**Plain claim.** For every toy program `e`: if no temporary escapes a block tail expression (`NoTailEscapingTemps e`) and no temporary escapes an `if let` scrutinee (`NoIfLetEscapingTemps e`), then the action list produced by `run` under the 2021 rules (`Edition.e2021.rules`) equals the one produced under the 2024 rules (`Edition.e2024.rules`); consequently the event traces (`trace`), the toy borrow-check verdicts (`accepts`) and the behaviours (`beh`) under the two editions agree.

**Tier.** T1: the two 2024 narrowing rules are documented in prose (Edition Guide, RFC 3606); this card states a consequence of them inside a toy elaboration. No mechanized statement of it was found in the search recorded under Prior-art search; novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:731-733
theorem run_e2021_eq_run_e2024_of_noTailEscapingTemps_of_noIfLetEscapingTemps (e : Expr)
    (ht : NoTailEscapingTemps e) (hi : NoIfLetEscapingTemps e) :
    run Edition.e2021.rules e = run Edition.e2024.rules e :=
```

```lean
-- lean/ToyDropScope/DropResults.lean:739-743
theorem trace_accepts_beh_eq_of_noTailEscapingTemps_of_noIfLetEscapingTemps (e : Expr)
    (ht : NoTailEscapingTemps e) (hi : NoIfLetEscapingTemps e) :
    trace Edition.e2021.rules e = trace Edition.e2024.rules e ∧
    accepts Edition.e2021.rules e = accepts Edition.e2024.rules e ∧
    beh Edition.e2021.rules e = beh Edition.e2024.rules e := by
```

Unfolded (explicit, definitionally equal to `run_e2021_eq_run_e2024_of_noTailEscapingTemps_of_noIfLetEscapingTemps`):

```lean
∀ (e : Expr), tailsClean e = true → ifLetsClean e = true →
  closeScope (eval ⟨false, false⟩ [] e) = closeScope (eval ⟨true, true⟩ [] e)
```

Unfolded (prose): `NoTailEscapingTemps e` is `tailsClean e = true`: every block tail expression `t` in `e` passes `noEscape t`, that is, no `temp` node of `t` sits in a position from which (under the 2021 rules) its temporary is still pending when `t` finishes (`t` itself, `seq` operands, tails of nested blocks, scrutinees of nested `if let` and `match`). `NoIfLetEscapingTemps e` is the same check applied to every `if let` scrutinee. `run R e` is `closeScope (eval R [] e)`: the executed actions followed by the drops of temporaries still pending at the end of the program.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `ht : NoTailEscapingTemps e (both theorems)` | excludes temporaries whose drop point the tail rule moves | tight: counterexamples `tailProg_noIfLetEscapingTemps_and_run_ne` and `tailProg_accepted_and_traces_reversed` (witness class: a one-block program with one local and one tail temporary (`tailProg`), satisfying `NoIfLetEscapingTemps`; `tailProg_noIfLetEscapingTemps_and_run_ne` shows that `tailProg` satisfies `NoIfLetEscapingTemps` and that its 2021 and 2024 action lists differ (the first theorem's conclusion fails), and `tailProg_accepted_and_traces_reversed` shows that its 2021 and 2024 traces differ (the trace conjunct of the second theorem's conclusion fails)) |
| `hi : NoIfLetEscapingTemps e (both theorems)` | excludes temporaries whose drop point the `if let` rule moves | tight: counterexamples `ifLetElseProg_noTailEscapingTemps_and_run_ne` and `ifLetElseProg_traces_differ` (witness class: a single `if let` whose scrutinee creates one temporary (`ifLetElseProg`), satisfying `NoTailEscapingTemps`; `ifLetElseProg_noTailEscapingTemps_and_run_ne` shows that `ifLetElseProg` satisfies `NoTailEscapingTemps` and that its 2021 and 2024 action lists differ (the first theorem's conclusion fails), and `ifLetElseProg_traces_differ` shows that its 2021 and 2024 traces differ (the trace conjunct of the second theorem's conclusion fails)) |

**Depth.** shallow (corollary of R1-split; the second theorem listed is a corollary of the first).

**Non-vacuity witness.** `stmtTempsProg` satisfies both hypotheses; under the 2021 rules it executes exactly two temporary drops (a third syntactic temporary sits in the `if let` branch that does not run; `refuted_stmtTempsProg_three_temp_drops`, which refutes the reading that counts three temporary drops, records that the count is not three). (`stmtTempsProg_noTailEscapingTemps_noIfLetEscapingTemps`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R1*; read them before relying on this card.

**Prior art.**

- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:5 (summary), :54 (`RefCell` example: 2021 drops `c` before the temporary, 2024 after), :58 (2021 extends tail temporaries to the next temporary scope boundary; 2024 drops them at the end of the block before the block's locals), :62-69 (a program accepted in 2021 and rejected in 2024 with E0716), :90 (no semantics-preserving rewrite shortens tail temporaries) [documentation]
- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-if-let-scope.md:5 (2024 drops `if let` scrutinee temporaries before entering `else`), :30 (2021 keeps them until after the `if let`), :32 (2024: until the then-block is evaluated or control enters `else`) [documentation]
- RFC 3606 'Shorter temporary lifetimes in tail expressions' (merged), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/3606-temporary-lifetimes-in-tail-expressions.md:10, :53-61, :78-79 [documentation (accepted design RFC)]
- RFC 66 'Better temporary lifetimes', rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/0066-better-temporary-lifetimes.md:7-10 (temporary lifetime extension for `let` bindings, which this package does not model) [documentation (accepted design RFC)]
- Formal semantics of Rust, cited as related work and not examined for edition-specific temporary scopes: F. Wang et al., 'KRust: A Formal Executable Semantics of Rust', TASE 2018, DOI 10.1109/TASE.2018.00014; L. Gäher et al., 'RefinedRust: A Type System for High-Assurance Verification of Rust Programs', Proceedings of the ACM on Programming Languages (PLDI) 2024, DOI 10.1145/3656422 [related work]
- Corpus package `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction` (published), card R1 (`Toy.DropFlags.stdElab_correct_of_forward_moveChecked_noNormalPathToResume`): exactly-once destruction within a fixed scope assignment; this package varies the scope assignment instead

**Modeling bridge.** Basis: derived (modeling bridge). The toy rule switches mirror the two documented 2024 changes: temporaries of a block's tail expression are dropped before the block's locals (Edition Guide `temporary-tail-expr-scope.md:58`; RFC 3606 `:53-61`), and temporaries of an `if let` scrutinee are dropped before control enters `else` (`temporary-if-let-scope.md:5`, `:32`). In the toy, the two escape checks single out the temporaries whose drop point these rules move; reading the card as a statement about Rust would also require that the escape checks match Rust's temporary-scope rules, which is not shown. No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** Can a verified compiler share one elaboration for both editions on the programs where the edition cannot be observed, and which syntactic class is safe to treat edition-independently?

#### R1-split — theorem, T1

**Plain claim.** For every toy program `e` and every setting `b` of the other rule: if `NoTailEscapingTemps e`, then switching the tail rule leaves the action list produced by `run` unchanged (`run ⟨true, b⟩ e = run ⟨false, b⟩ e`); and if `NoIfLetEscapingTemps e`, then switching the `if let` rule leaves it unchanged (`run ⟨b, true⟩ e = run ⟨b, false⟩ e`).

**Tier.** T1: the two 2024 narrowing rules are documented in prose (Edition Guide, RFC 3606); this card states a consequence of them inside a toy elaboration. No mechanized statement of it was found in the search recorded under Prior-art search; novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:717-718
theorem run_tail2024_eq_of_noTailEscapingTemps (e : Expr) (b : Bool) (ht : NoTailEscapingTemps e) :
    run ⟨true, b⟩ e = run ⟨false, b⟩ e := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:723-724
theorem run_ifLet2024_eq_of_noIfLetEscapingTemps (e : Expr) (b : Bool) (hi : NoIfLetEscapingTemps e) :
    run ⟨b, true⟩ e = run ⟨b, false⟩ e := by
```

Unfolded (explicit, definitionally equal to `run_tail2024_eq_of_noTailEscapingTemps`):

```lean
∀ (e : Expr) (b : Bool), tailsClean e = true →
  closeScope (eval ⟨true, b⟩ [] e) = closeScope (eval ⟨false, b⟩ [] e)
```

Unfolded (explicit, definitionally equal to `run_ifLet2024_eq_of_noIfLetEscapingTemps`):

```lean
∀ (e : Expr) (b : Bool), ifLetsClean e = true →
  closeScope (eval ⟨b, true⟩ [] e) = closeScope (eval ⟨b, false⟩ [] e)
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `ht : NoTailEscapingTemps e (first theorem)` | excludes temporaries the tail rule moves | tight: counterexample `ifLetInTailProg_tail_rule_changes_run` (witness class: an `if let` with a scrutinee temporary in the tail of a block with one local (`ifLetInTailProg`), at `b = false`) |
| `hi : NoIfLetEscapingTemps e (second theorem)` | excludes temporaries the `if let` rule moves | tight: counterexample `ifLetElseProg_not_noIfLetEscapingTemps_and_ifLet_rule_changes_run` (witness class: a single `if let` whose scrutinee creates one temporary (`ifLetElseProg`), at `b = true`) |

**Depth.** shallow.

**Non-vacuity witness.** `ifLetElseProg` satisfies `NoTailEscapingTemps` and its 2021 and 2024 traces differ, so the first theorem applies to a program the edition does affect; `tailProg` satisfies `NoIfLetEscapingTemps`. (`ifLetElseProg_noTailEscapingTemps_and_traces_differ`, `tailProg_noIfLetEscapingTemps_and_run_ne`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R1-split*; read them before relying on this card.

**Prior art.**

- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:5 (summary), :54 (`RefCell` example: 2021 drops `c` before the temporary, 2024 after), :58 (2021 extends tail temporaries to the next temporary scope boundary; 2024 drops them at the end of the block before the block's locals), :62-69 (a program accepted in 2021 and rejected in 2024 with E0716), :90 (no semantics-preserving rewrite shortens tail temporaries) [documentation]
- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-if-let-scope.md:5 (2024 drops `if let` scrutinee temporaries before entering `else`), :30 (2021 keeps them until after the `if let`), :32 (2024: until the then-block is evaluated or control enters `else`) [documentation]
- RFC 3606 'Shorter temporary lifetimes in tail expressions' (merged), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/3606-temporary-lifetimes-in-tail-expressions.md:10, :53-61, :78-79 [documentation (accepted design RFC)]

**Modeling bridge.** Basis: derived (modeling bridge). Each switch corresponds to one documented change (tail: `temporary-tail-expr-scope.md:58`, RFC 3606 `:53-61`; `if let`: `temporary-if-let-scope.md:5`, `:32`). The mixed settings `⟨true, false⟩` and `⟨false, true⟩` are a device of the toy for separating the two rules; the cited documents describe the two changes as parts of Rust 2024. No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** Are the two 2024 narrowing rules independent on their clean classes, so that a compiler can stage or verify them separately?

#### R1-perm — theorem, T1

**Plain claim.** For every toy program `e` and every two rule settings `R₁`, `R₂`: the action lists `run R₁ e` and `run R₂ e` are permutations of each other; `run R₁ e` contains no action twice; in `run R₁ e` the temporaries dropped (`dropTemps`: tag and borrow list of every `dropTemp`) are a permutation of the temporaries created (`mkTemps`: the same data of every `mkTemp`); and the actions other than temporary drops occur in the same order in `run R₁ e` and `run R₂ e`. Consequently (second theorem) under every setting each temporary created during the run occurs exactly once among the temporaries dropped. Rescoping thus reorders temporary drops, keeps the order of every other action, and adds or removes no action.

**Tier.** T1: that the 2024 rules move drops of temporaries without adding or losing drops is implicit in the Edition Guide's description of the change; this card makes it precise for the toy elaboration. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:752-755
theorem run_perm_nodup_and_dropTemps_perm_mkTemps_and_nonDropTemps_eq (R₁ R₂ : Rules) (e : Expr) :
    (run R₁ e).Perm (run R₂ e) ∧ (run R₁ e).Nodup ∧
    (dropTemps (run R₁ e)).Perm (mkTemps (run R₁ e)) ∧
    (run R₁ e).filter (fun a => !a.isDropTemp) = (run R₂ e).filter (fun a => !a.isDropTemp) := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:783-784
theorem run_each_created_temp_dropped_exactly_once (R : Rules) (e : Expr) :
    ∀ k ∈ mkTemps (run R e), (dropTemps (run R e)).count k = 1 := by
```

Unfolded (explicit, definitionally equal to `run_perm_nodup_and_dropTemps_perm_mkTemps_and_nonDropTemps_eq`):

```lean
∀ (R₁ R₂ : Rules) (e : Expr),
  (run R₁ e).Perm (run R₂ e) ∧ (run R₁ e).Nodup ∧
  ((run R₁ e).filterMap Act.dropTempKey?).Perm ((run R₁ e).filterMap Act.mkTempKey?) ∧
  (run R₁ e).filter (fun a => !a.isDropTemp) = (run R₂ e).filter (fun a => !a.isDropTemp)
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** substantive.

**Non-vacuity witness.** No hypotheses beyond the quantified variables. `run_tailProg` shows two settings whose action lists differ, so the permutation is not the identity, and `mkTemps_dropTemps_tailProg` shows a run with a created and dropped temporary. (`run_tailProg`, `mkTemps_dropTemps_tailProg`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R1-perm*; read them before relying on this card.

**Prior art.**

- Corpus package `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction` (published), card R1 (`Toy.DropFlags.stdElab_correct_of_forward_moveChecked_noNormalPathToResume`): exactly-once destruction within a fixed scope assignment; this package varies the scope assignment instead
- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:5 (summary), :54 (`RefCell` example: 2021 drops `c` before the temporary, 2024 after), :58 (2021 extends tail temporaries to the next temporary scope boundary; 2024 drops them at the end of the block before the block's locals), :62-69 (a program accepted in 2021 and rejected in 2024 with E0716), :90 (no semantics-preserving rewrite shortens tail temporaries) [documentation]

**Modeling bridge.** Basis: derived (modeling bridge). The cited documents describe the 2024 changes as changes of when temporaries are dropped (`temporary-tail-expr-scope.md:58`; `temporary-if-let-scope.md:5`, `:32`); the toy version is that the rule setting permutes temporary drops and keeps every other action and its order. The toy has no panics, no conditional initialization and no state-dependent control flow. No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** May a verified compiler treat the edition change as a pure reordering of temporary drops (no new or lost drops, no other action moved)?

#### R1-match-tail — counterexample, T1

**Plain claim.** For the program `matchInTailProg` (a `match` whose scrutinee creates a temporary with destructor event `dtor 1`, in the tail position of a block with one local whose destructor emits `dtor 0`), the 2021 trace is `[dtor 0, dtor 1]` and the 2024 trace is `[dtor 1, dtor 0]`; with the tail rule on and the `if let` rule off the trace is `[dtor 1, dtor 0]`, and with the tail rule off and the `if let` rule on it is `[dtor 0, dtor 1]`. For every rule setting, `eval` of a `match` is the setting-independent combinator `matchStep` (`eval_matchE_eq_matchStep`). Separately (`refuted_match_outside_blockTail_same_drop_point`, which refutes the stronger reading that a `match` scrutinee temporary has the same drop point in both editions whenever the `match` is outside block tail positions), `matchInIfLetScrutProg` (a `match` inside an `if let` scrutinee, with no block) satisfies `NoTailEscapingTemps`, violates `NoIfLetEscapingTemps`, and has 2021 trace `[out 1, dtor 0]` and 2024 trace `[dtor 0, out 1]`.

**Tier.** T1: RFC 3606 states that temporaries in a block's tail expression are dropped before the block's locals from Rust 2024 on, and the Reference states that a `match` scrutinee is not a temporary scope; this card records the resulting closed computation in the toy. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:801-805
theorem matchInTailProg_scrutinee_drop_moves_by_tail_rule :
    trace Edition.e2021.rules matchInTailProg = [.dtor 0, .dtor 1] ∧
    trace Edition.e2024.rules matchInTailProg = [.dtor 1, .dtor 0] ∧
    trace ⟨true, false⟩ matchInTailProg = [.dtor 1, .dtor 0] ∧
    trace ⟨false, true⟩ matchInTailProg = [.dtor 0, .dtor 1] := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:793-795
theorem eval_matchE_eq_matchStep (R : Rules) (p : Tag) (hit : Bool) (s a b : Expr) :
    eval R p (.matchE hit s a b) =
      matchStep hit (eval R (0 :: p) s) (eval R (1 :: p) a) (eval R (2 :: p) b) := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:811-814
theorem refuted_match_outside_blockTail_same_drop_point :
    NoTailEscapingTemps matchInIfLetScrutProg ∧ ¬ NoIfLetEscapingTemps matchInIfLetScrutProg ∧
    trace Edition.e2021.rules matchInIfLetScrutProg = [.out 1, .dtor 0] ∧
    trace Edition.e2024.rules matchInIfLetScrutProg = [.dtor 0, .out 1] := by decide
```

Unfolded (prose): Under the 2021 rules the scrutinee temporary of the `match` stays pending past the end of the block (no rule closes the tail), so it is dropped after the local; under the tail rule the block's tail expression is a temporary scope and the temporary is dropped before the local. `matchStep hit rs ra rb` appends the selected arm's closed actions to the scrutinee's actions and passes the scrutinee's pending temporaries on, with no dependence on the rules.

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** definitional.

**Non-vacuity witness.** Closed computations. (`matchInTailProg_scrutinee_drop_moves_by_tail_rule`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R1-match-tail*; read them before relying on this card.

**Prior art.**

- RFC 3606 'Shorter temporary lifetimes in tail expressions' (merged), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/3606-temporary-lifetimes-in-tail-expressions.md:10, :53-61, :78-79 [documentation (accepted design RFC)]
- The Rust Reference, Destructors, rust-lang/reference@84dc36ff4712fad6829b6063cd4acbcaf5381708:src/destructors.md:281-282 (a `match` scrutinee is not a temporary scope) [documentation]
- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-if-let-scope.md:5 (2024 drops `if let` scrutinee temporaries before entering `else`), :30 (2021 keeps them until after the `if let`), :32 (2024: until the then-block is evaluated or control enters `else`) [documentation]

**Modeling bridge.** Basis: derived (modeling bridge). RFC 3606 `:53-61` states the tail rule for the tail expression of every block, and the Reference note at `destructors.md:281-282` says that a `match` scrutinee is not a temporary scope; in the toy, `matchE` has no rule switch of its own, so its scrutinee temporaries are governed by the enclosing tail or `if let` scope. No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** Does an edition-independent treatment of `match` suffice, or must the compiler know whether a `match` sits in a tail position or inside an `if let` scrutinee?

#### R2 — counterexample, T1

**Plain claim.** For the program `tailProg` (one local whose destructor emits `dtor 0`, and a tail temporary whose destructor emits `dtor 1`), the toy borrow check (`accepts`) accepts it under both editions, the 2021 trace is `[dtor 0, dtor 1]` and the 2024 trace is `[dtor 1, dtor 0]`; consequently neither edition's accepted behaviour is included in the other's (`BehIncl` fails in both directions). For `refCellTailProg` (a tail temporary borrowing the block's local), the toy borrow check accepts under the 2024 rules and rejects under the 2021 rules.

**Tier.** T1: the Edition Guide documents both the reversed drop order and the `RefCell` program accepted in 2024 and rejected in 2021; this card records the corresponding toy computations and the incomparability they imply. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:887-890
theorem tailProg_accepted_and_traces_reversed :
    accepts Edition.e2021.rules tailProg = true ∧ accepts Edition.e2024.rules tailProg = true ∧
    trace Edition.e2021.rules tailProg = [.dtor 0, .dtor 1] ∧
    trace Edition.e2024.rules tailProg = [.dtor 1, .dtor 0] := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:894-896
theorem not_behIncl_e2021_e2024_and_not_behIncl_e2024_e2021 :
    ¬ BehIncl Edition.e2021.rules Edition.e2024.rules ∧
    ¬ BehIncl Edition.e2024.rules Edition.e2021.rules := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:908-910
theorem refCellTailProg_accepted_e2024_rejected_e2021 :
    accepts Edition.e2024.rules refCellTailProg = true ∧
    accepts Edition.e2021.rules refCellTailProg = false := by decide
```

Unfolded (explicit, definitionally equal to `not_behIncl_e2021_e2024_and_not_behIncl_e2024_e2021`):

```lean
(¬ ∀ (e : Expr) (tr : List Ev), beh ⟨false, false⟩ e = some tr → beh ⟨true, true⟩ e = some tr) ∧
  ¬ ∀ (e : Expr) (tr : List Ev), beh ⟨true, true⟩ e = some tr → beh ⟨false, false⟩ e = some tr
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** definitional.

**Non-vacuity witness.** Concrete programs; closed computations. (`tailProg_accepted_and_traces_reversed`)

**Positive control.** Restricted to programs satisfying `NoTailEscapingTemps` and `NoIfLetEscapingTemps`, the 2021 and 2024 behaviours coincide (`trace_accepts_beh_eq_of_noTailEscapingTemps_of_noIfLetEscapingTemps`), so incomparability disappears on that class; `behIncl_refl` is the trivial reflexive case. (`trace_accepts_beh_eq_of_noTailEscapingTemps_of_noIfLetEscapingTemps`, `behIncl_refl`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R2*; read them before relying on this card.

**Prior art.**

- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:5 (summary), :54 (`RefCell` example: 2021 drops `c` before the temporary, 2024 after), :58 (2021 extends tail temporaries to the next temporary scope boundary; 2024 drops them at the end of the block before the block's locals), :62-69 (a program accepted in 2021 and rejected in 2024 with E0716), :90 (no semantics-preserving rewrite shortens tail temporaries) [documentation]
- RFC 3606 'Shorter temporary lifetimes in tail expressions' (merged), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/3606-temporary-lifetimes-in-tail-expressions.md:10, :53-61, :78-79 [documentation (accepted design RFC)]
- Corpus package `drop-check-may-dangle-and-destructor-soundness-for-generic-containers` (published), card R5 (`Toy.Dropck.dropOrder_matters_pReaderAfter`): destructor soundness depends on drop order; this package does not model destructor soundness

**Modeling bridge.** Basis: derived (modeling bridge). The Edition Guide's `RefCell` example (`temporary-tail-expr-scope.md:54`) describes a program in which 2024 reverses the 2021 drop order of a tail temporary and a local and which compiles under 2024; `tailProg` and `refCellTailProg` mirror this in the toy. The guide also documents a program accepted in 2021 and rejected in 2024 (`:62-69`), which the toy borrow check cannot express (see the non-claims). No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** Must a verified compiler's semantics be indexed by edition (no edition's behaviour is included in the other's), and does the edition also change which programs are accepted?

#### R3-match — theorem, T1

**Plain claim.** For every toy program `e` and every rule setting `R`, the action list that `run` produces for the `match`-rewritten program `toMatch e` under `R` equals the action list of `e` under `R` with the `if let` rule set to its 2021 setting and the tail rule unchanged (`run R (toMatch e) = run { R with ifLet2024 := false } e`). The `if let` rule is observable: for `ifLetElseProg` (an `if let` whose scrutinee temporary's destructor emits `dtor 0`, whose pattern does not match and whose `else` block emits `out 1`) the 2021 trace is `[out 1, dtor 0]` and the 2024 trace is `[dtor 0, out 1]`.

**Tier.** T1: the Edition Guide documents the `if let` rule and the Reference documents that a `match` scrutinee is not a temporary scope; this card states in the toy that rewriting to `match` is the same as switching the `if let` rule off. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:923-924
theorem run_toMatch_eq_run_ifLet2021 (R : Rules) (e : Expr) :
    run R (toMatch e) = run { R with ifLet2024 := false } e := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:916-918
theorem ifLetElseProg_traces_differ :
    trace Edition.e2021.rules ifLetElseProg = [.out 1, .dtor 0] ∧
    trace Edition.e2024.rules ifLetElseProg = [.dtor 0, .out 1] := by decide
```

Unfolded (explicit, definitionally equal to `run_toMatch_eq_run_ifLet2021`):

```lean
∀ (R : Rules) (e : Expr),
  closeScope (eval R [] (toMatch e)) = closeScope (eval ⟨R.tail2024, false⟩ [] e)
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** No hypotheses beyond the quantified variables; `toMatch_ifLetElseProg_ne` shows the rewrite changes a program, and `ifLetElseProg_traces_differ` shows the `if let` rule changes that program's trace. (`toMatch_ifLetElseProg_ne`, `ifLetElseProg_traces_differ`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R3-match*; read them before relying on this card.

**Prior art.**

- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-if-let-scope.md:5 (2024 drops `if let` scrutinee temporaries before entering `else`), :30 (2021 keeps them until after the `if let`), :32 (2024: until the then-block is evaluated or control enters `else`) [documentation]
- The Rust Reference, Destructors, rust-lang/reference@84dc36ff4712fad6829b6063cd4acbcaf5381708:src/destructors.md:281-282 (a `match` scrutinee is not a temporary scope) [documentation]

**Modeling bridge.** Basis: derived (modeling bridge). The Reference note at `destructors.md:281-282` (a `match` scrutinee is not a temporary scope) and the documented `if let` change (`temporary-if-let-scope.md:5`, `:32`) motivate the toy's choice that `matchE` evaluates like `ifLet` with the `if let` rule off. `toMatch` is a toy rewrite; the card is not a statement about rewriting Rust code. No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** Does rewriting every `if let` to `match` amount, in the toy, to switching off the `if let` rule while leaving the tail rule in force?

#### R3-migration — theorem, T1

**Plain claim.** For every toy program `e`: if `NoTailEscapingTemps e`, then the action list that `run` produces for `toMatch e` under the 2024 rules equals the action list of `e` under the 2021 rules.

**Tier.** T1: the two 2024 narrowing rules are documented in prose (Edition Guide, RFC 3606); this card states a consequence of them inside a toy elaboration. No mechanized statement of it was found in the search recorded under Prior-art search; novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:930-931
theorem run_e2024_toMatch_eq_run_e2021_of_noTailEscapingTemps (e : Expr) (ht : NoTailEscapingTemps e) :
    run Edition.e2024.rules (toMatch e) = run Edition.e2021.rules e :=
```

Unfolded (explicit, definitionally equal to `run_e2024_toMatch_eq_run_e2021_of_noTailEscapingTemps`):

```lean
∀ (e : Expr), tailsClean e = true →
  closeScope (eval ⟨true, true⟩ [] (toMatch e)) = closeScope (eval ⟨false, false⟩ [] e)
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `ht : NoTailEscapingTemps e` | the 2024 tail rule also applies to `match` scrutinee temporaries in tail positions | tight: counterexample `ifLetInTailProg_toMatch_e2024_ne_e2021` (witness class: an `if let` with a scrutinee temporary in the tail position of a block with one local (`ifLetInTailProg`)) |

**Depth.** shallow (corollary of R3-match and R1-split).

**Non-vacuity witness.** `ifLetElseProg` satisfies the hypothesis and its 2021 and 2024 traces differ. (`ifLetElseProg_noTailEscapingTemps_and_traces_differ`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R3-migration*; read them before relying on this card.

**Prior art.**

- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-if-let-scope.md:5 (2024 drops `if let` scrutinee temporaries before entering `else`), :30 (2021 keeps them until after the `if let`), :32 (2024: until the then-block is evaluated or control enters `else`) [documentation]
- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:5 (summary), :54 (`RefCell` example: 2021 drops `c` before the temporary, 2024 after), :58 (2021 extends tail temporaries to the next temporary scope boundary; 2024 drops them at the end of the block before the block's locals), :62-69 (a program accepted in 2021 and rejected in 2024 with E0716), :90 (no semantics-preserving rewrite shortens tail temporaries) [documentation]
- RFC 3606 'Shorter temporary lifetimes in tail expressions' (merged), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/3606-temporary-lifetimes-in-tail-expressions.md:10, :53-61, :78-79 [documentation (accepted design RFC)]

**Modeling bridge.** Basis: derived (modeling bridge). The card combines the toy's `if let`/`match` correspondence (R3-match) with the toy tail rule (RFC 3606 `:53-61`). It is a statement about the toy rewrite `toMatch`, not about rewriting Rust code. No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** When does rewriting every `if let` to `match` (`toMatch`) reproduce, under the toy's 2024 rules, the toy's 2021 action list?

#### R4-if — theorem, T1

**Plain claim.** For every toy program `e`: if every pair of actions that occur in opposite orders in the action lists produced by `run` under the 2021 and the 2024 rules (`Flipped e a b`) has commuting event lists (`Commute a b`, equality of the words `a.events ++ b.events` and `b.events ++ a.events`), then the 2021 and 2024 event traces of `e` are equal.

**Tier.** T1: the abstract core (a reordering in which every inverted pair has commuting images leaves the product of a word unchanged) is standard trace theory (cited below); its instantiation to the toy's edition-indexed action lists, via R1-perm, is folklore made precise. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:968-970
theorem trace_e2021_eq_trace_e2024_of_flipped_commute (e : Expr)
    (h : ∀ a b, Flipped e a b → Commute a b) :
    trace Edition.e2021.rules e = trace Edition.e2024.rules e := by
```

Unfolded (explicit, definitionally equal to `trace_e2021_eq_trace_e2024_of_flipped_commute`):

```lean
∀ (e : Expr),
  (∀ a b : Act,
      (∃ i j : Nat, i < j ∧ (run ⟨false, false⟩ e)[i]? = some a ∧ (run ⟨false, false⟩ e)[j]? = some b) ∧
      (∃ i j : Nat, i < j ∧ (run ⟨true, true⟩ e)[i]? = some b ∧ (run ⟨true, true⟩ e)[j]? = some a) →
      a.events ++ b.events = b.events ++ a.events) →
    (run ⟨false, false⟩ e).flatMap Act.events = (run ⟨true, true⟩ e).flatMap Act.events
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `h : ∀ a b, Flipped e a b → Commute a b` | every reordered pair must be unobservable as a word | tight: counterexample `tailProg_flipped_not_commute_and_traces_differ` (witness class: `tailProg`: one flipped pair with distinct single destructor events) |

**Depth.** substantive (uses R1-perm and an induction over permutations of duplicate-free lists).

**Non-vacuity witness.** `commutingTailProg` has a flipped pair and every flipped pair commutes. (`commutingTailProg_flipped_and_all_commute`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R4-if*; read them before relying on this card.

**Prior art.**

- Trace theory: P. Cartier and D. Foata, Problèmes combinatoires de commutation et réarrangements, Lecture Notes in Mathematics 85, Springer, 1969, DOI 10.1007/BFb0079468; A. Mazurkiewicz, 'Concurrent Program Schemes and their Interpretations', DAIMI Report PB-78, 1977, DOI 10.7146/dpb.v6i78.7691; V. Diekert and G. Rozenberg (eds.), The Book of Traces, World Scientific, 1995, DOI 10.1142/2563: words identified up to commutation of independent letters; the abstract core of R4-if (a reordering in which every inverted pair has commuting images leaves the product unchanged) belongs to this standard theory [prior art]
- Combinatorics on words: M. Lothaire, Combinatorics on Words, Cambridge University Press, 1997, DOI 10.1017/CBO9780511566097, and R. C. Lyndon and M. P. Schützenberger, 'The equation a^M = b^N c^P in a free group', Michigan Mathematical Journal 9(4), 1962, DOI 10.1307/mmj/1028998766: the classical fact that two words commute iff both are powers of a common word [prior art; not proved in this package]
- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:5 (summary), :54 (`RefCell` example: 2021 drops `c` before the temporary, 2024 after), :58 (2021 extends tail temporaries to the next temporary scope boundary; 2024 drops them at the end of the block before the block's locals), :62-69 (a program accepted in 2021 and rejected in 2024 with E0716), :90 (no semantics-preserving rewrite shortens tail temporaries) [documentation]
- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-if-let-scope.md:5 (2024 drops `if let` scrutinee temporaries before entering `else`), :30 (2021 keeps them until after the `if let`), :32 (2024: until the then-block is evaluated or control enters `else`) [documentation]

**Modeling bridge.** Basis: derived (modeling bridge). The Edition Guide states that before 2024 tail temporaries were extended to the next temporary scope boundary (`temporary-tail-expr-scope.md:58`) and that no semantics-preserving rewrite shortens them (`:90`); the toy's 2021 rules keep such temporaries pending until an enclosing scope closes. `Commute` compares toy event words; it is not an independence relation on Rust effects. No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** What sufficient condition lets a migration tool certify that the edition change is unobservable in the trace of a program?

#### R4-site — characterization, T1

**Plain claim.** For every list `ls` of local destructor event lists and every list `ds` of tail-temporary destructor event lists, the program `tailSiteProg ls ds` has equal 2021 and 2024 traces iff `dropOrderEvents ls ++ dropOrderEvents ds = dropOrderEvents ds ++ dropOrderEvents ls`; and for every `ds` and every list `es` of output numbers, `elseSiteProg ds es` has equal traces iff `es.map Ev.out ++ dropOrderEvents ds = dropOrderEvents ds ++ es.map Ev.out`. If moreover every event in `dropOrderEvents ds` is a `dtor` event, the latter condition holds iff `es = []` or `dropOrderEvents ds = []` (`elseSite_commute_iff_of_dtorOnly`).

**Tier.** T1: the Edition Guide describes which events a moved temporary crosses at one tail or `else` site; this card gives the exact whole-word condition for one site in the toy. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:1019-1021
theorem tailSiteProg_trace_eq_iff_commute (ls ds : List (List Ev)) :
    trace Edition.e2021.rules (tailSiteProg ls ds) = trace Edition.e2024.rules (tailSiteProg ls ds) ↔
      dropOrderEvents ls ++ dropOrderEvents ds = dropOrderEvents ds ++ dropOrderEvents ls := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:1036-1038
theorem elseSiteProg_trace_eq_iff_commute (ds : List (List Ev)) (es : List Nat) :
    trace Edition.e2021.rules (elseSiteProg ds es) = trace Edition.e2024.rules (elseSiteProg ds es) ↔
      es.map Ev.out ++ dropOrderEvents ds = dropOrderEvents ds ++ es.map Ev.out := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:1051-1054
theorem elseSite_commute_iff_of_dtorOnly (ds : List (List Ev)) (es : List Nat)
    (hd : ∀ ev ∈ dropOrderEvents ds, ∃ n, ev = .dtor n) :
    es.map Ev.out ++ dropOrderEvents ds = dropOrderEvents ds ++ es.map Ev.out ↔
      es = [] ∨ dropOrderEvents ds = [] := by
```

Unfolded (explicit, definitionally equal to `tailSiteProg_trace_eq_iff_commute`):

```lean
∀ (ls ds : List (List Ev)),
  trace ⟨false, false⟩ (tailSiteProg ls ds) = trace ⟨true, true⟩ (tailSiteProg ls ds) ↔
    ls.reverse.flatten ++ ds.reverse.flatten = ds.reverse.flatten ++ ls.reverse.flatten
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hd : ∀ ev ∈ dropOrderEvents ds, ∃ n, ev = .dtor n (third theorem)` | restricts the third theorem to destructors all of whose events are `dtor` events; the two characterizations have no hypotheses | tight: counterexample `elseSite_commute_iff_of_dtorOnly_hypothesis_tight` (witness class: one scrutinee temporary whose destructor emits `out 1`, with `es = [1]`) |

The main characterizations of this card have no hypotheses beyond the quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** `site_examples` gives instances of both sides of both characterizations, including an `else` site whose scrutinee temporary's destructor emits an `out` event that commutes with the `else` block's output; `elseSite_dtorOnly_hypothesis_holds` satisfies the hypothesis of the third theorem. (`site_examples`, `elseSite_dtorOnly_hypothesis_holds`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R4-site*; read them before relying on this card.

**Prior art.**

- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:5 (summary), :54 (`RefCell` example: 2021 drops `c` before the temporary, 2024 after), :58 (2021 extends tail temporaries to the next temporary scope boundary; 2024 drops them at the end of the block before the block's locals), :62-69 (a program accepted in 2021 and rejected in 2024 with E0716), :90 (no semantics-preserving rewrite shortens tail temporaries) [documentation]
- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-if-let-scope.md:5 (2024 drops `if let` scrutinee temporaries before entering `else`), :30 (2021 keeps them until after the `if let`), :32 (2024: until the then-block is evaluated or control enters `else`) [documentation]
- Combinatorics on words: M. Lothaire, Combinatorics on Words, Cambridge University Press, 1997, DOI 10.1017/CBO9780511566097, and R. C. Lyndon and M. P. Schützenberger, 'The equation a^M = b^N c^P in a free group', Michigan Mathematical Journal 9(4), 1962, DOI 10.1307/mmj/1028998766: the classical fact that two words commute iff both are powers of a common word [prior art; not proved in this package]

**Modeling bridge.** Basis: derived (modeling bridge). The two site shapes mirror the documented situations (a temporary in a block's tail expression, `temporary-tail-expr-scope.md:58`; a scrutinee temporary of an `if let` whose `else` block runs, `temporary-if-let-scope.md:5`, `:32`) in their simplest toy form. No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** At a single affected site, exactly which destructor behaviours make the migration unobservable in the trace?

#### R4-not-necessary — counterexample, T1

**Plain claim.** For `ababProg` (two locals and two tail temporaries whose drops spell `[dtor 0, dtor 1]` on each side), the 2021 and 2024 traces are equal, yet the temporary drop `ababTempDrop` and the local drop `ababLocalDrop` occur in opposite orders under the two editions and their event lists do not commute; per-action commutation is therefore not necessary for trace preservation in the toy.

**Tier.** T1: a toy instance of the classical fact that a product of words can be preserved by a reordering whose individual swaps do not commute; novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:1114-1116
theorem ababProg_trace_eq_and_flipped_not_commute :
    trace Edition.e2021.rules ababProg = trace Edition.e2024.rules ababProg ∧
    Flipped ababProg ababLocalDrop ababTempDrop ∧ ¬ Commute ababLocalDrop ababTempDrop := by
```

Unfolded (prose): Both editions emit `dtor 0, dtor 1, dtor 0, dtor 1`: under 2021 the locals' drops (`dtor 0, dtor 1`) precede the temporaries' drops (`dtor 0, dtor 1`), under 2024 the order of the two groups is swapped, and the two groups spell the same word. The pair (`ababLocalDrop`, `ababTempDrop`) is flipped and `[dtor 1] ++ [dtor 0]` is not `[dtor 0] ++ [dtor 1]`.

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** definitional.

**Non-vacuity witness.** Closed computation. (`ababProg_trace_eq_and_flipped_not_commute`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R4-not-necessary*; read them before relying on this card.

**Prior art.**

- Combinatorics on words: M. Lothaire, Combinatorics on Words, Cambridge University Press, 1997, DOI 10.1017/CBO9780511566097, and R. C. Lyndon and M. P. Schützenberger, 'The equation a^M = b^N c^P in a free group', Michigan Mathematical Journal 9(4), 1962, DOI 10.1307/mmj/1028998766: the classical fact that two words commute iff both are powers of a common word [prior art; not proved in this package]
- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:5 (summary), :54 (`RefCell` example: 2021 drops `c` before the temporary, 2024 after), :58 (2021 extends tail temporaries to the next temporary scope boundary; 2024 drops them at the end of the block before the block's locals), :62-69 (a program accepted in 2021 and rejected in 2024 with E0716), :90 (no semantics-preserving rewrite shortens tail temporaries) [documentation]

**Modeling bridge.** Basis: derived (modeling bridge). A toy instance; it relies on distinct drop actions emitting identical event labels. No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** Can a migration checker demand per-temporary commutation without rejecting trace-preserving programs?

#### R4-window — counterexample, T1

**Plain claim.** For `nestedTailProg` (a tail temporary created in the tail of an inner block with no locals, the inner block being the tail of an outer block with one local), the traces differ (`[dtor 1, dtor 0]` under 2021, `[dtor 0, dtor 1]` under 2024); for `thenBranchProg` (an `if let` with a matching pattern followed in the same expression by `out 1`), the traces differ (`[out 1, dtor 0]` under 2021, `[dtor 0, out 1]` under 2024); and for `siblingTailProg` (a block with no locals whose tail creates a temporary, followed in the same expression by `out 1`), the traces differ (`[out 1, dtor 0]` under 2021, `[dtor 0, out 1]` under 2024).

**Tier.** T1: the Edition Guide states that 2021 extends tail temporaries to the next temporary scope boundary; this card records toy instances of the events crossed. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/DropResults.lean:1131-1133
theorem nestedTailProg_traces_differ :
    trace Edition.e2021.rules nestedTailProg = [.dtor 1, .dtor 0] ∧
    trace Edition.e2024.rules nestedTailProg = [.dtor 0, .dtor 1] := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:1138-1140
theorem thenBranchProg_traces_differ :
    trace Edition.e2021.rules thenBranchProg = [.out 1, .dtor 0] ∧
    trace Edition.e2024.rules thenBranchProg = [.dtor 0, .out 1] := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:1145-1147
theorem siblingTailProg_traces_differ :
    trace Edition.e2021.rules siblingTailProg = [.out 1, .dtor 0] ∧
    trace Edition.e2024.rules siblingTailProg = [.dtor 0, .out 1] := by decide
```

Unfolded (prose): In each program the 2021 rules keep the temporary pending until an enclosing temporary scope closes (the end of the program), so its drop follows events produced outside its owning block (the outer local's drop, or the following `out 1`); the 2024 rules close the owning tail expression or `if let` first.

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** definitional.

**Non-vacuity witness.** Closed computations. (`nestedTailProg_traces_differ`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R4-window*; read them before relying on this card.

**Prior art.**

- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:5 (summary), :54 (`RefCell` example: 2021 drops `c` before the temporary, 2024 after), :58 (2021 extends tail temporaries to the next temporary scope boundary; 2024 drops them at the end of the block before the block's locals), :62-69 (a program accepted in 2021 and rejected in 2024 with E0716), :90 (no semantics-preserving rewrite shortens tail temporaries) [documentation]
- Edition Guide, rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-if-let-scope.md:5 (2024 drops `if let` scrutinee temporaries before entering `else`), :30 (2021 keeps them until after the `if let`), :32 (2024: until the then-block is evaluated or control enters `else`) [documentation]
- RFC 3606 'Shorter temporary lifetimes in tail expressions' (merged), rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/3606-temporary-lifetimes-in-tail-expressions.md:10, :53-61, :78-79 [documentation (accepted design RFC)]

**Modeling bridge.** Basis: derived (modeling bridge). The Edition Guide states that before 2024 tail temporaries were extended to the next temporary scope boundary, in many cases the end of a statement or function body (`temporary-tail-expr-scope.md:58`); the toy programs record which toy events such an extended temporary crosses. No theorem of this package mentions Rust; the correspondence is informal reasoning from the cited text, not a proved relation (Model–system relation: none proved), and the card's theorems neither establish nor refute the corresponding claims about Rust's editions or any Rust compiler.

**Design question.** Which events must a migration check consider for each moved temporary?

#### R5-eq — theorem, T1

**Plain claim.** For every tag count `n`, allowed-tag predicate `A`, read-UB predicate `R` and payload predicate `P`: if every tag `t` that is not an allowed tag (`allowedTag n A t = false`) is read as undefined behaviour (`R t = true`), then for every switch `sw` and tag `t`, `exec R P (specializeSwitch n A sw) t = exec R P sw t`. In particular (second theorem), under the discriminant semantics `rejectBoth` (reading an uninhabited-variant tag or an invalid tag is undefined behaviour), for every enum `E`, switch `sw` and tag `t`, the enum-derived specialization `specializeEnum E sw` has the same outcome as `sw`.

**Tier.** T1: that removing branches on tags whose read is undefined behaviour preserves behaviour is the informal justification of the documented pass and an instance of standard refinement reasoning (cited); this card states it parametrically for the toy rewrite. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/SwitchResults.lean:124-126
theorem exec_specializeSwitch_eq_of_readUB_of_not_allowedTag (n : Nat) (A R P : Nat → Bool)
    (hR : ∀ t, allowedTag n A t = false → R t = true) (sw : Switch) (t : Nat) :
    exec R P (specializeSwitch n A sw) t = exec R P sw t := by
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:314-315
theorem runSwitch_specializeEnum_eq_of_rejectBoth (E : Enum) (sw : Switch) (t : Nat) :
    runSwitch rejectBoth E (specializeEnum E sw) t = runSwitch rejectBoth E sw t :=
```

Unfolded (explicit, definitionally equal to `exec_specializeSwitch_eq_of_readUB_of_not_allowedTag`):

```lean
∀ (n : Nat) (A R P : Nat → Bool), (∀ t, (decide (t < n) && A t) = false → R t = true) →
  ∀ (sw : Switch) (t : Nat),
    (if R t then Outcome.ub else runArm P t ((specializeSwitch n A sw).target t)) =
      (if R t then Outcome.ub else runArm P t (sw.target t))
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hR : ∀ t, allowedTag n A t = false → R t = true (first theorem)` | the specialization leaves the target of every allowed tag unchanged and may retarget non-allowed tags to `unreachable` (non-allowed explicit arms, and the wildcard when at most one allowed tag lacks an explicit arm); on the non-allowed tags the read must already be undefined behaviour | tight: counterexample `specializeSwitch_eq_hypothesis_tight` (witness class: `deadNicheEnum` with the permissive read (one uninhabited tag), `deadNicheSwitch`, tag 1) |

The second theorem (`runSwitch_specializeEnum_eq_of_rejectBoth`) has no hypotheses beyond the quantified variables.

**Depth.** shallow (the second theorem is a corollary of the first with `readUB_rejectBoth_of_allowedTag_eq_false`).

**Non-vacuity witness.** `rejectBoth` on `deadNicheEnum` (which has an uninhabited variant) satisfies the hypothesis, and `rejectBoth_deadNicheSwitch_same` shows a switch the specialization changes. (`deadNicheEnum_rejectBoth_satisfies_hypothesis`, `rejectBoth_deadNicheSwitch_same`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R5-eq*; read them before relying on this card.

**Prior art.**

- rustc unreachable-enum-branching pass, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:1 (pass summary), :123-127 (explicit arms whose value is not an allowed variant become unreachable), :129-167 (when at most one allowed variant lacks an arm, the wildcard is made unreachable, after the one remaining variant, if any, takes the wildcard target) [documentation (source comments and code of the pass), used as derived (modeling bridge)]
- rustc MIR `Rvalue::Discriminant` documentation, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1412-1422 ('The validity requirements for the underlying value are undecided for this rvalue, see [#91095]') [documentation]
- Refinement under undefined behaviour: X. Leroy, 'Formal Verification of a Realistic Compiler', Communications of the ACM 52(7), 2009, DOI 10.1145/1538788.1538814; J. Lee et al., 'Taming Undefined Behavior in LLVM', PLDI 2017, DOI 10.1145/3062341.3062343: compiler correctness as refinement, where undefined behaviour of the source admits any target behaviour (the shape of `Refines`) [prior art]
- MiniRust, minirust/minirust@063d784186d3252bee242217f218223205c0b568:spec/lang/step/expressions.md:101-130 (`ValueExpr::GetDiscriminant`: a discriminant read that raises undefined behaviour when the bytes it reads do not decode to a discriminant) and spec/lang/step/terminators.md:34-48 (`Terminator::Switch`) [documentation (a proposed specification); this package neither adopts nor evaluates its choices]
- rust-lang/rust#91095 'Decide on when MIR Discriminant() operation is UB' (open issue linked from the `Rvalue::Discriminant` documentation; mentioned for orientation, not relied on)

**Modeling bridge.** Basis: derived (modeling bridge). The rewrites `pruneArms` and `lastVariantTakesWildcard` (composed in `specializeSwitch`, and instantiated with an enum's inhabited tags in `specializeEnum`) are modeled on the source of the unreachable-enum-branching pass (`unreachable_enum_branching.rs:1`, `:123-127`, `:129-167`, quoted under *External sources*): explicit arms on values that are not allowed variants become unreachable, and when at most one allowed variant lacks an arm the wildcard becomes unreachable after that variant, if any, takes the wildcard target. The two uninhabited-variant read semantics are kept open because the `Rvalue::Discriminant` documentation says the validity requirements of that read are undecided (rustc_middle `syntax.rs:1412-1422`, which links rust-lang/rust#91095, an open issue mentioned for orientation and not relied on); `InvalidRead.passThrough` is a modeling boundary of the toy. No claim is made about which semantics Rust has or about the behaviour of the pass (Model–system relation: none proved); the card's theorems neither establish nor refute the corresponding claims about Rust or rustc.

**Design question.** Under which discriminant-read semantics is inhabitedness-gated specialization an equivalence?

#### R5-iff — characterization, T1

**Plain claim.** For every `n`, `A`, `R`, `P`: the specialized switch's outcome refines the original's (`Refines`: the original is undefined behaviour or the two outcomes are equal) for every switch and every tag iff every tag that is not an allowed tag is read as undefined behaviour.

**Tier.** T1: the forward direction is the informal justification of the pass; the converse (no weaker read semantics suffices for all switches) is folklore of refinement reasoning; this card mechanizes both for the toy rewrite. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/SwitchResults.lean:135-137
theorem specializeSwitch_refines_all_iff (n : Nat) (A R P : Nat → Bool) :
    (∀ (sw : Switch) (t : Nat), Refines (exec R P (specializeSwitch n A sw) t) (exec R P sw t)) ↔
      ∀ t, allowedTag n A t = false → R t = true := by
```

Unfolded (explicit, definitionally equal to `specializeSwitch_refines_all_iff`):

```lean
∀ (n : Nat) (A R P : Nat → Bool),
  (∀ (sw : Switch) (t : Nat),
      exec R P sw t = Outcome.ub ∨ exec R P (specializeSwitch n A sw) t = exec R P sw t) ↔
    ∀ t, (decide (t < n) && A t) = false → R t = true
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** Both sides occur: `deadNicheEnum_rejectBoth_satisfies_hypothesis` (right side holds) and `specializeSwitch_deadNicheSwitch_permissive_not_refines` (right side fails and `Refines` fails, for `deadNicheSwitch` at tag 1 under the permissive read). (`deadNicheEnum_rejectBoth_satisfies_hypothesis`, `specializeSwitch_deadNicheSwitch_permissive_not_refines`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R5-iff*; read them before relying on this card.

**Prior art.**

- rustc unreachable-enum-branching pass, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:1 (pass summary), :123-127 (explicit arms whose value is not an allowed variant become unreachable), :129-167 (when at most one allowed variant lacks an arm, the wildcard is made unreachable, after the one remaining variant, if any, takes the wildcard target) [documentation (source comments and code of the pass), used as derived (modeling bridge)]
- rustc MIR `Rvalue::Discriminant` documentation, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1412-1422 ('The validity requirements for the underlying value are undecided for this rvalue, see [#91095]') [documentation]
- Refinement under undefined behaviour: X. Leroy, 'Formal Verification of a Realistic Compiler', Communications of the ACM 52(7), 2009, DOI 10.1145/1538788.1538814; J. Lee et al., 'Taming Undefined Behavior in LLVM', PLDI 2017, DOI 10.1145/3062341.3062343: compiler correctness as refinement, where undefined behaviour of the source admits any target behaviour (the shape of `Refines`) [prior art]
- MiniRust, minirust/minirust@063d784186d3252bee242217f218223205c0b568:spec/lang/step/expressions.md:101-130 (`ValueExpr::GetDiscriminant`: a discriminant read that raises undefined behaviour when the bytes it reads do not decode to a discriminant) and spec/lang/step/terminators.md:34-48 (`Terminator::Switch`) [documentation (a proposed specification); this package neither adopts nor evaluates its choices]
- rust-lang/rust#91095 'Decide on when MIR Discriminant() operation is UB' (open issue linked from the `Rvalue::Discriminant` documentation; mentioned for orientation, not relied on)

**Modeling bridge.** Basis: derived (modeling bridge). The rewrites `pruneArms` and `lastVariantTakesWildcard` (composed in `specializeSwitch`, and instantiated with an enum's inhabited tags in `specializeEnum`) are modeled on the source of the unreachable-enum-branching pass (`unreachable_enum_branching.rs:1`, `:123-127`, `:129-167`, quoted under *External sources*): explicit arms on values that are not allowed variants become unreachable, and when at most one allowed variant lacks an arm the wildcard becomes unreachable after that variant, if any, takes the wildcard target. The two uninhabited-variant read semantics are kept open because the `Rvalue::Discriminant` documentation says the validity requirements of that read are undecided (rustc_middle `syntax.rs:1412-1422`, which links rust-lang/rust#91095, an open issue mentioned for orientation and not relied on); `InvalidRead.passThrough` is a modeling boundary of the toy. No claim is made about which semantics Rust has or about the behaviour of the pass (Model–system relation: none proved); the card's theorems neither establish nor refute the corresponding claims about Rust or rustc.

**Design question.** What exactly must the discriminant read guarantee for the specialization to be sound for all switches?

#### R5-iff-shapes — characterization, T1

**Plain claim.** For every `n`, `A`, `R`, `P`: `pruneArms` alone (every explicit arm whose value is not an allowed tag is retargeted to `unreachable`) refines the original for every switch and tag iff every non-allowed tag is read as undefined behaviour; and `lastVariantTakesWildcard` alone (if zero allowed tags lack an explicit arm, the wildcard becomes `unreachable`; if exactly one allowed tag `j` lacks one, an arm `j ↦ otherwise` is appended and the wildcard becomes `unreachable`; otherwise the switch is unchanged) refines the original for every switch and tag iff the same condition holds.

**Tier.** T1: the two shapes are the two rewrites documented in the pass's source; this card characterizes each separately in the toy. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/SwitchResults.lean:158-160
theorem pruneArms_refines_all_iff (n : Nat) (A R P : Nat → Bool) :
    (∀ (sw : Switch) (t : Nat), Refines (exec R P (pruneArms n A sw) t) (exec R P sw t)) ↔
      ∀ t, allowedTag n A t = false → R t = true := by
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:177-180
theorem lastVariantTakesWildcard_refines_all_iff (n : Nat) (A R P : Nat → Bool) :
    (∀ (sw : Switch) (t : Nat),
        Refines (exec R P (lastVariantTakesWildcard n A sw) t) (exec R P sw t)) ↔
      ∀ t, allowedTag n A t = false → R t = true := by
```

Unfolded (explicit, definitionally equal to `pruneArms_refines_all_iff`):

```lean
∀ (n : Nat) (A R P : Nat → Bool),
  (∀ (sw : Switch) (t : Nat),
      exec R P sw t = Outcome.ub ∨ exec R P (pruneArms n A sw) t = exec R P sw t) ↔
    ∀ t, (decide (t < n) && A t) = false → R t = true
```

Unfolded (explicit, definitionally equal to `lastVariantTakesWildcard_refines_all_iff`):

```lean
∀ (n : Nat) (A R P : Nat → Bool),
  (∀ (sw : Switch) (t : Nat),
      exec R P sw t = Outcome.ub ∨ exec R P (lastVariantTakesWildcard n A sw) t = exec R P sw t) ↔
    ∀ t, (decide (t < n) && A t) = false → R t = true
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** Right side holds: `deadNicheEnum_rejectBoth_satisfies_hypothesis`. Right side fails and refinement fails for each shape exercised directly: `pruneArms_explicitUninhabitedArm_permissive_not_refines` (`pruneArms` changes a switch with an explicit arm on the uninhabited tag) and `lastVariantTakesWildcard_permissive_not_refines_both_branches` (both changing branches of `lastVariantTakesWildcard`: zero remaining allowed tags on `deadNicheSwitch`, exactly one on the enum `[true, false, true, true]`). (`deadNicheEnum_rejectBoth_satisfies_hypothesis`, `pruneArms_explicitUninhabitedArm_permissive_not_refines`, `lastVariantTakesWildcard_permissive_not_refines_both_branches`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R5-iff-shapes*; read them before relying on this card.

**Prior art.**

- rustc unreachable-enum-branching pass, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:1 (pass summary), :123-127 (explicit arms whose value is not an allowed variant become unreachable), :129-167 (when at most one allowed variant lacks an arm, the wildcard is made unreachable, after the one remaining variant, if any, takes the wildcard target) [documentation (source comments and code of the pass), used as derived (modeling bridge)]
- Refinement under undefined behaviour: X. Leroy, 'Formal Verification of a Realistic Compiler', Communications of the ACM 52(7), 2009, DOI 10.1145/1538788.1538814; J. Lee et al., 'Taming Undefined Behavior in LLVM', PLDI 2017, DOI 10.1145/3062341.3062343: compiler correctness as refinement, where undefined behaviour of the source admits any target behaviour (the shape of `Refines`) [prior art]

**Modeling bridge.** Basis: derived (modeling bridge). The rewrites `pruneArms` and `lastVariantTakesWildcard` (composed in `specializeSwitch`, and instantiated with an enum's inhabited tags in `specializeEnum`) are modeled on the source of the unreachable-enum-branching pass (`unreachable_enum_branching.rs:1`, `:123-127`, `:129-167`, quoted under *External sources*): explicit arms on values that are not allowed variants become unreachable, and when at most one allowed variant lacks an arm the wildcard becomes unreachable after that variant, if any, takes the wildcard target. The two uninhabited-variant read semantics are kept open because the `Rvalue::Discriminant` documentation says the validity requirements of that read are undecided (rustc_middle `syntax.rs:1412-1422`, which links rust-lang/rust#91095, an open issue mentioned for orientation and not relied on); `InvalidRead.passThrough` is a modeling boundary of the toy. No claim is made about which semantics Rust has or about the behaviour of the pass (Model–system relation: none proved); the card's theorems neither establish nor refute the corresponding claims about Rust or rustc.

**Design question.** Is either half of the pass sound under a weaker discriminant semantics than the other?

#### R5-valid — characterization, T1

**Plain claim.** For every discriminant semantics `D`: the enum-derived specialization refines the original for every enum, every switch and every valid tag (`t < E.length`) iff `D` rejects uninhabited-variant tags (`D.uninh = .rejectUninhabited`).

**Tier.** T1: the dependence of the pass on the uninhabited-variant read is implicit in the pass and in the undecided status documented for `Rvalue::Discriminant`; this card makes it exact in the toy. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/SwitchResults.lean:322-325
theorem specializeEnum_refines_validTags_iff_rejectUninhabited (D : DiscrSem) :
    (∀ (E : Enum) (sw : Switch) (t : Nat), t < E.length →
        Refines (runSwitch D E (specializeEnum E sw) t) (runSwitch D E sw t)) ↔
      D.uninh = .rejectUninhabited := by
```

Unfolded (explicit, definitionally equal to `specializeEnum_refines_validTags_iff_rejectUninhabited`):

```lean
∀ (D : DiscrSem),
  (∀ (E : Enum) (sw : Switch) (t : Nat), t < E.length →
      runSwitch D E sw t = Outcome.ub ∨
        runSwitch D E (specializeEnum E sw) t = runSwitch D E sw t) ↔
    D.uninh = UninhabitedRead.rejectUninhabited
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** Both values of `D.uninh` occur: `rejectBoth_deadNicheSwitch_same` (right side holds) and `deadNiche_permissive_specializeEnum_introduces_ub` (right side fails, refinement fails). (`rejectBoth_deadNicheSwitch_same`, `deadNiche_permissive_specializeEnum_introduces_ub`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R5-valid*; read them before relying on this card.

**Prior art.**

- rustc unreachable-enum-branching pass, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:1 (pass summary), :123-127 (explicit arms whose value is not an allowed variant become unreachable), :129-167 (when at most one allowed variant lacks an arm, the wildcard is made unreachable, after the one remaining variant, if any, takes the wildcard target) [documentation (source comments and code of the pass), used as derived (modeling bridge)]
- rustc MIR `Rvalue::Discriminant` documentation, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1412-1422 ('The validity requirements for the underlying value are undecided for this rvalue, see [#91095]') [documentation]
- rust-lang/rust#91095 'Decide on when MIR Discriminant() operation is UB' (open issue linked from the `Rvalue::Discriminant` documentation; mentioned for orientation, not relied on)
- MiniRust, minirust/minirust@063d784186d3252bee242217f218223205c0b568:spec/lang/step/expressions.md:101-130 (`ValueExpr::GetDiscriminant`: a discriminant read that raises undefined behaviour when the bytes it reads do not decode to a discriminant) and spec/lang/step/terminators.md:34-48 (`Terminator::Switch`) [documentation (a proposed specification); this package neither adopts nor evaluates its choices]

**Modeling bridge.** Basis: derived (modeling bridge). The rewrites `pruneArms` and `lastVariantTakesWildcard` (composed in `specializeSwitch`, and instantiated with an enum's inhabited tags in `specializeEnum`) are modeled on the source of the unreachable-enum-branching pass (`unreachable_enum_branching.rs:1`, `:123-127`, `:129-167`, quoted under *External sources*): explicit arms on values that are not allowed variants become unreachable, and when at most one allowed variant lacks an arm the wildcard becomes unreachable after that variant, if any, takes the wildcard target. The two uninhabited-variant read semantics are kept open because the `Rvalue::Discriminant` documentation says the validity requirements of that read are undecided (rustc_middle `syntax.rs:1412-1422`, which links rust-lang/rust#91095, an open issue mentioned for orientation and not relied on); `InvalidRead.passThrough` is a modeling boundary of the toy. No claim is made about which semantics Rust has or about the behaviour of the pass (Model–system relation: none proved); the card's theorems neither establish nor refute the corresponding claims about Rust or rustc.

**Design question.** Does soundness of the specialization for valid tags hinge exactly on the uninhabited-variant read semantics?

#### R5-permissive — characterization, T1

**Plain claim.** For every invalid-tag choice `inv` and every enum `E`, under the permissive uninhabited-tag semantics `⟨.permissive, inv⟩`: the enum-derived specialization refines the original for every switch and every valid tag iff every variant of `E` is inhabited.

**Tier.** T1: as for R5-valid, restricted to the permissive read; novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/SwitchResults.lean:350-354
theorem specializeEnum_refines_validTags_permissive_iff_allInhabited (inv : InvalidRead) (E : Enum) :
    (∀ (sw : Switch) (t : Nat), t < E.length →
        Refines (runSwitch ⟨.permissive, inv⟩ E (specializeEnum E sw) t)
          (runSwitch ⟨.permissive, inv⟩ E sw t)) ↔
      ∀ t, t < E.length → E.inhabitedTag t = true := by
```

Unfolded (explicit, definitionally equal to `specializeEnum_refines_validTags_permissive_iff_allInhabited`):

```lean
∀ (inv : InvalidRead) (E : Enum),
  (∀ (sw : Switch) (t : Nat), t < E.length →
      runSwitch ⟨.permissive, inv⟩ E sw t = Outcome.ub ∨
        runSwitch ⟨.permissive, inv⟩ E (specializeEnum E sw) t = runSwitch ⟨.permissive, inv⟩ E sw t) ↔
    ∀ t, t < E.length → E.getD t false = true
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** `permissive_allInhabited_orderingSwitch_same` (all-inhabited enum, right side holds, a switch the specialization changes) and `deadNiche_permissive_specializeEnum_introduces_ub` (right side fails). (`permissive_allInhabited_orderingSwitch_same`, `deadNiche_permissive_specializeEnum_introduces_ub`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R5-permissive*; read them before relying on this card.

**Prior art.**

- rustc unreachable-enum-branching pass, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:1 (pass summary), :123-127 (explicit arms whose value is not an allowed variant become unreachable), :129-167 (when at most one allowed variant lacks an arm, the wildcard is made unreachable, after the one remaining variant, if any, takes the wildcard target) [documentation (source comments and code of the pass), used as derived (modeling bridge)]
- rustc MIR `Rvalue::Discriminant` documentation, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1412-1422 ('The validity requirements for the underlying value are undecided for this rvalue, see [#91095]') [documentation]

**Modeling bridge.** Basis: derived (modeling bridge). The rewrites `pruneArms` and `lastVariantTakesWildcard` (composed in `specializeSwitch`, and instantiated with an enum's inhabited tags in `specializeEnum`) are modeled on the source of the unreachable-enum-branching pass (`unreachable_enum_branching.rs:1`, `:123-127`, `:129-167`, quoted under *External sources*): explicit arms on values that are not allowed variants become unreachable, and when at most one allowed variant lacks an arm the wildcard becomes unreachable after that variant, if any, takes the wildcard target. The two uninhabited-variant read semantics are kept open because the `Rvalue::Discriminant` documentation says the validity requirements of that read are undecided (rustc_middle `syntax.rs:1412-1422`, which links rust-lang/rust#91095, an open issue mentioned for orientation and not relied on); `InvalidRead.passThrough` is a modeling boundary of the toy. No claim is made about which semantics Rust has or about the behaviour of the pass (Model–system relation: none proved); the card's theorems neither establish nor refute the corresponding claims about Rust or rustc.

**Design question.** Is there a non-trivial class of enums on which the specialization is sound under the permissive semantics?

#### R5-cx — counterexample, T1

**Plain claim.** Under `permissiveRejectInvalid`: for `deadNicheEnum` with `deadNicheSwitch`, the stored value 2 decodes (toy niche encoding `exampleNiche`) to the uninhabited variant 1, the original switch continues normally (`ret 1`) and the specialized switch is undefined behaviour; and for the enum `[true, false, true, true]` with explicit arms `0 ↦ goto 1` and `2 ↦ goto 2` and wildcard `goto 3`, on the uninhabited tag 1 the original switch continues normally (`ret 3`) and the specialized switch is undefined behaviour (`ub`).

**Tier.** T1: the `TagEncoding::Niche` documentation states that uninhabited variants can fall into the niche range as dead values; this card computes the consequence for the toy specialization. Novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/SwitchResults.lean:385-389
theorem deadNiche_permissive_specializeEnum_introduces_ub :
    exampleNiche.decode 2 = 1 ∧ deadNicheEnum.inhabitedTag 1 = false ∧
    runSwitch permissiveRejectInvalid deadNicheEnum deadNicheSwitch (exampleNiche.decode 2) = .ret 1 ∧
    runSwitch permissiveRejectInvalid deadNicheEnum (specializeEnum deadNicheEnum deadNicheSwitch)
      (exampleNiche.decode 2) = .ub := by decide
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:395-399
theorem lastVariant_permissive_introduces_ub :
    runSwitch permissiveRejectInvalid [true, false, true, true] ⟨[(0, .goto 1), (2, .goto 2)], .goto 3⟩ 1
      = .ret 3 ∧
    runSwitch permissiveRejectInvalid [true, false, true, true]
      (specializeEnum [true, false, true, true] ⟨[(0, .goto 1), (2, .goto 2)], .goto 3⟩) 1 = .ub := by
```

Unfolded (prose): `exampleNiche.decode 2` subtracts the niche start 2 (truncated subtraction, guarded by `2 ≤ 2`) and adds `nicheLo = 1`, giving variant 1, which is at most `nicheHi = 2`. Under the permissive read, the read of tag 1 is defined; the original selects the wildcard `goto 1`, while `specializeEnum` makes the wildcard `unreachable` because no inhabited tag lacks an explicit arm. In the second theorem, tag 1 has no explicit arm, so the original takes the wildcard `goto 3`; the inhabited tags are 0, 2 and 3, and exactly one of them (3) lacks an explicit arm, so `specializeEnum` appends the arm `3 ↦ goto 3` and makes the wildcard `unreachable`; the permissive read of tag 1 is defined, and tag 1 then reaches that `unreachable` wildcard, which is undefined behaviour.

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** definitional.

**Non-vacuity witness.** Closed computations. (`deadNiche_permissive_specializeEnum_introduces_ub`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R5-cx*; read them before relying on this card.

**Prior art.**

- rustc unreachable-enum-branching pass, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:1 (pass summary), :123-127 (explicit arms whose value is not an allowed variant become unreachable), :129-167 (when at most one allowed variant lacks an arm, the wildcard is made unreachable, after the one remaining variant, if any, takes the wildcard target) [documentation (source comments and code of the pass), used as derived (modeling bridge)]
- rustc `TagEncoding::Niche` documentation, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_abi/src/lib.rs:2013-2015 (decoding a tag to a variant index, with wrapping subtraction) and :2022-2029 (uninhabited variants can fall into `niche_variants`; such values are dead values) [documentation]
- rustc MIR `Rvalue::Discriminant` documentation, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1412-1422 ('The validity requirements for the underlying value are undecided for this rvalue, see [#91095]') [documentation]
- Corpus package `enum-niche-layout-guarantees-and-validity-invariants` (published), card `nicheLayout_lawful_iff_isNiche` (niche-filled layouts are lawful iff the niche pattern is invalid for the payload); that package models inhabited extra variants and states that uninhabited variants are not modeled there

**Modeling bridge.** Basis: derived (modeling bridge). The rewrites `pruneArms` and `lastVariantTakesWildcard` (composed in `specializeSwitch`, and instantiated with an enum's inhabited tags in `specializeEnum`) are modeled on the source of the unreachable-enum-branching pass (`unreachable_enum_branching.rs:1`, `:123-127`, `:129-167`, quoted under *External sources*): explicit arms on values that are not allowed variants become unreachable, and when at most one allowed variant lacks an arm the wildcard becomes unreachable after that variant, if any, takes the wildcard target. `NicheEnc.decode` follows the documented `TagEncoding::Niche` decoding (rustc_abi `lib.rs:2013-2015`) with guarded truncated subtraction instead of wrapping subtraction; the same documentation says that uninhabited variants can fall into the niche range as dead values (`lib.rs:2022-2029`). The two uninhabited-variant read semantics are kept open because the `Rvalue::Discriminant` documentation says the validity requirements of that read are undecided (rustc_middle `syntax.rs:1412-1422`, which links rust-lang/rust#91095, an open issue mentioned for orientation and not relied on); `InvalidRead.passThrough` is a modeling boundary of the toy. No claim is made about which semantics Rust has or about the behaviour of the pass (Model–system relation: none proved); the card's theorems neither establish nor refute the corresponding claims about Rust or rustc.

**Design question.** Under the permissive semantics, does the specialization introduce undefined behaviour on stored tag values that decode to an uninhabited variant?

#### R6-all — characterization, T1

**Plain claim.** For every discriminant semantics `D`: the enum-derived specialization refines the original for every enum, every switch and every tag, valid or invalid, iff `D` rejects both uninhabited-variant tags and invalid tags. Rejecting uninhabited-variant tags alone does not suffice (second theorem): under `⟨.rejectUninhabited, .passThrough⟩`, for the one-variant enum `[true]` and the switch with no explicit arm and wildcard `goto 0`, the invalid tag 1 yields `ret 0` in the original and undefined behaviour after specialization.

**Tier.** T1: as for R5-valid, extended to tags that denote no variant; novelty is not claimed.

**Statement.** Basis: execution (Lean kernel check). Verbatim quotes of the Lean source; proofs elided.

```lean
-- lean/ToyDropScope/SwitchResults.lean:433-436
theorem specializeEnum_refines_allTags_iff_rejectUninhabited_and_rejectInvalid (D : DiscrSem) :
    (∀ (E : Enum) (sw : Switch) (t : Nat),
        Refines (runSwitch D E (specializeEnum E sw) t) (runSwitch D E sw t)) ↔
      D.uninh = .rejectUninhabited ∧ D.invalid = .rejectInvalid := by
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:458-461
theorem invalidTag_passThrough_specializeEnum_introduces_ub :
    runSwitch ⟨.rejectUninhabited, .passThrough⟩ [true] ⟨[], .goto 0⟩ 1 = .ret 0 ∧
    runSwitch ⟨.rejectUninhabited, .passThrough⟩ [true] (specializeEnum [true] ⟨[], .goto 0⟩) 1
      = .ub := by decide
```

Unfolded (explicit, definitionally equal to `specializeEnum_refines_allTags_iff_rejectUninhabited_and_rejectInvalid`):

```lean
∀ (D : DiscrSem),
  (∀ (E : Enum) (sw : Switch) (t : Nat),
      runSwitch D E sw t = Outcome.ub ∨
        runSwitch D E (specializeEnum E sw) t = runSwitch D E sw t) ↔
    D.uninh = UninhabitedRead.rejectUninhabited ∧ D.invalid = InvalidRead.rejectInvalid
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** `rejectBoth_deadNicheSwitch_same` (right side holds) and `invalidTag_passThrough_specializeEnum_introduces_ub` (right side fails, refinement fails). (`rejectBoth_deadNicheSwitch_same`, `invalidTag_passThrough_specializeEnum_introduces_ub`)

**Non-claims.** Listed under `## Boundaries`, subsection *Non-claims: R6-all*; read them before relying on this card.

**Prior art.**

- rustc unreachable-enum-branching pass, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:1 (pass summary), :123-127 (explicit arms whose value is not an allowed variant become unreachable), :129-167 (when at most one allowed variant lacks an arm, the wildcard is made unreachable, after the one remaining variant, if any, takes the wildcard target) [documentation (source comments and code of the pass), used as derived (modeling bridge)]
- rustc MIR `Rvalue::Discriminant` documentation, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1412-1422 ('The validity requirements for the underlying value are undecided for this rvalue, see [#91095]') [documentation]
- rustc `TagEncoding::Niche` documentation, rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_abi/src/lib.rs:2013-2015 (decoding a tag to a variant index, with wrapping subtraction) and :2022-2029 (uninhabited variants can fall into `niche_variants`; such values are dead values) [documentation]
- MiniRust, minirust/minirust@063d784186d3252bee242217f218223205c0b568:spec/lang/step/expressions.md:101-130 (`ValueExpr::GetDiscriminant`: a discriminant read that raises undefined behaviour when the bytes it reads do not decode to a discriminant) and spec/lang/step/terminators.md:34-48 (`Terminator::Switch`) [documentation (a proposed specification); this package neither adopts nor evaluates its choices]
- rust-lang/rust#91095 'Decide on when MIR Discriminant() operation is UB' (open issue linked from the `Rvalue::Discriminant` documentation; mentioned for orientation, not relied on)
- Corpus package `enum-niche-layout-guarantees-and-validity-invariants` (published), card `nicheLayout_lawful_iff_isNiche` (niche-filled layouts are lawful iff the niche pattern is invalid for the payload); that package models inhabited extra variants and states that uninhabited variants are not modeled there

**Modeling bridge.** Basis: derived (modeling bridge). The rewrites `pruneArms` and `lastVariantTakesWildcard` (composed in `specializeSwitch`, and instantiated with an enum's inhabited tags in `specializeEnum`) are modeled on the source of the unreachable-enum-branching pass (`unreachable_enum_branching.rs:1`, `:123-127`, `:129-167`, quoted under *External sources*): explicit arms on values that are not allowed variants become unreachable, and when at most one allowed variant lacks an arm the wildcard becomes unreachable after that variant, if any, takes the wildcard target. `NicheEnc.decode` follows the documented `TagEncoding::Niche` decoding (rustc_abi `lib.rs:2013-2015`) with guarded truncated subtraction instead of wrapping subtraction; the same documentation says that uninhabited variants can fall into the niche range as dead values (`lib.rs:2022-2029`). The two uninhabited-variant read semantics are kept open because the `Rvalue::Discriminant` documentation says the validity requirements of that read are undecided (rustc_middle `syntax.rs:1412-1422`, which links rust-lang/rust#91095, an open issue mentioned for orientation and not relied on); `InvalidRead.passThrough` is a modeling boundary of the toy. No claim is made about which semantics Rust has or about the behaviour of the pass (Model–system relation: none proved); the card's theorems neither establish nor refute the corresponding claims about Rust or rustc.

**Design question.** Is rejecting uninhabited-variant tags enough, or must the read also reject tags that denote no variant?

### Auxiliary declarations cited by name (verbatim)

Every package-local declaration named above and not quoted in its own section is quoted here.

Helper definitions that occur inside the quoted declarations (for example in `tailSiteProg`, `elseSiteProg`, `borrowOK_shadowing_limitation`, `pruneArms_explicitUninhabitedArm_permissive_not_refines`, `usePayloadSwitch_permissive_specializeEnum_refines` and the theorems about `orderingSwitch`):

```lean
-- lean/ToyDropScope/DropResults.lean:17-19
def letsFrom (k : Nat) : List (List Ev) → Block → Block
  | [], b => b
  | dl :: ls, b => .letS k dl .unit (letsFrom (k + 1) ls b)
```

```lean
-- lean/ToyDropScope/DropResults.lean:22-24
def tempsSeq : List (List Ev) → Expr
  | [] => .unit
  | d :: ds => .seq (.temp d []) (tempsSeq ds)
```

```lean
-- lean/ToyDropScope/DropResults.lean:27-29
def outsSeq : List Nat → Expr
  | [] => .unit
  | n :: ns => .seq (.out n) (outsSeq ns)
```

```lean
-- lean/ToyDropScope/Examples.lean:57-59
def shadowedBorrowProg : Expr :=
  .block (.letS 0 [] .unit
    (.exprS (.block (.letS 0 [] .unit (.tail (.temp [.dtor 1] [0])))) (.tail .unit)))
```

```lean
-- lean/ToyDropScope/Examples.lean:212
def tailProgLocalDrop : Act := .dropLocal [0] 0 [.dtor 0]
```

```lean
-- lean/ToyDropScope/Examples.lean:214
def tailProgTempDrop : Act := .dropTemp [0, 1, 0] [] [.dtor 1]
```

```lean
-- lean/ToyDropScope/Examples.lean:263
def orderingSwitch : Switch := ⟨[(0, .goto 1), (1, .goto 2)], .goto 3⟩
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:29
def explicitUninhabitedArmSwitch : Switch := ⟨[(1, .goto 1)], .goto 0⟩
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:33
def usePayloadSwitch : Switch := ⟨[(0, .goto 0), (2, .goto 2)], .usePayload 1⟩
```

Witness for the free-monoid remark in the non-claims of R4-if (distinct non-empty event lists can commute):

```lean
-- lean/ToyDropScope/DropResults.lean:1151-1155
theorem commute_distinct_nonempty_event_lists :
    (Act.dropLocal [] 0 [.dtor 0]).events ≠ [] ∧
    (Act.dropTemp [1] [] [.dtor 0, .dtor 0]).events ≠ [] ∧
    (Act.dropLocal [] 0 [.dtor 0]).events ≠ (Act.dropTemp [1] [] [.dtor 0, .dtor 0]).events ∧
    Commute (.dropLocal [] 0 [.dtor 0]) (.dropTemp [1] [] [.dtor 0, .dtor 0]) := by decide
```

Further declarations cited by name:

```lean
-- lean/ToyDropScope/DropResults.lean:33
def dropOrderEvents (xs : List (List Ev)) : List Ev := xs.reverse.flatten
```

```lean
-- lean/ToyDropScope/DropResults.lean:37
def tailSiteProg (ls ds : List (List Ev)) : Expr := .block (letsFrom 0 ls (.tail (tempsSeq ds)))
```

```lean
-- lean/ToyDropScope/DropResults.lean:41-42
def elseSiteProg (ds : List (List Ev)) (es : List Nat) : Expr :=
  .ifLet false (tempsSeq ds) .unit (outsSeq es)
```

```lean
-- lean/ToyDropScope/DropResults.lean:45-46
def matchInTailProg : Expr :=
  .block (.letS 0 [.dtor 0] .unit (.tail (.matchE true (.temp [.dtor 1] []) .unit .unit)))
```

```lean
-- lean/ToyDropScope/DropResults.lean:50-51
def ifLetInTailProg : Expr :=
  .block (.letS 0 [.dtor 0] .unit (.tail (.ifLet true (.temp [.dtor 1] []) .unit .unit)))
```

```lean
-- lean/ToyDropScope/DropResults.lean:54
def ababProg : Expr := tailSiteProg [[.dtor 1], [.dtor 0]] [[.dtor 1], [.dtor 0]]
```

```lean
-- lean/ToyDropScope/DropResults.lean:58-59
def nestedTailProg : Expr :=
  .block (.letS 0 [.dtor 1] .unit (.tail (.block (.tail (.temp [.dtor 0] [])))))
```

```lean
-- lean/ToyDropScope/DropResults.lean:62
def thenBranchProg : Expr := .seq (.ifLet true (.temp [.dtor 0] []) .unit .unit) (.out 1)
```

```lean
-- lean/ToyDropScope/DropResults.lean:65
def commutingTailProg : Expr := tailSiteProg [[.dtor 0]] [[.dtor 0]]
```

```lean
-- lean/ToyDropScope/DropResults.lean:69-70
def matchStep (hit : Bool) (rs ra rb : List Act × List Pending) : List Act × List Pending :=
  (rs.1 ++ (if hit then closeScope ra else closeScope rb), rs.2)
```

```lean
-- lean/ToyDropScope/DropResults.lean:818-821
theorem stmtTempsProg_noTailEscapingTemps_noIfLetEscapingTemps :
    NoTailEscapingTemps stmtTempsProg ∧ NoIfLetEscapingTemps stmtTempsProg ∧
    trace Edition.e2021.rules stmtTempsProg = [.dtor 1, .out 0, .dtor 3, .out 1, .dtor 0] ∧
    (dropTemps (run Edition.e2021.rules stmtTempsProg)).length = 2 := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:826-827
theorem refuted_stmtTempsProg_three_temp_drops :
    (dropTemps (run Edition.e2021.rules stmtTempsProg)).length ≠ 3 := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:831-833
theorem tailProg_noIfLetEscapingTemps_and_run_ne :
    NoIfLetEscapingTemps tailProg ∧ ¬ NoTailEscapingTemps tailProg ∧
    run Edition.e2021.rules tailProg ≠ run Edition.e2024.rules tailProg := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:837-839
theorem ifLetElseProg_noTailEscapingTemps_and_run_ne :
    NoTailEscapingTemps ifLetElseProg ∧ ¬ NoIfLetEscapingTemps ifLetElseProg ∧
    run Edition.e2021.rules ifLetElseProg ≠ run Edition.e2024.rules ifLetElseProg := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:847-854
theorem noEscape_hypotheses_not_necessary_for_run_eq :
    (¬ NoTailEscapingTemps topLevelTailTempProg ∧ NoIfLetEscapingTemps topLevelTailTempProg ∧
      (∀ b, run ⟨true, b⟩ topLevelTailTempProg = run ⟨false, b⟩ topLevelTailTempProg) ∧
      run Edition.e2021.rules topLevelTailTempProg = run Edition.e2024.rules topLevelTailTempProg ∧
      run Edition.e2024.rules (toMatch topLevelTailTempProg) =
        run Edition.e2021.rules topLevelTailTempProg) ∧
    (NoTailEscapingTemps bareIfLetThenProg ∧ ¬ NoIfLetEscapingTemps bareIfLetThenProg ∧
      ∀ b, run ⟨b, true⟩ bareIfLetThenProg = run ⟨b, false⟩ bareIfLetThenProg) := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:859-861
theorem commutingTailProg_run_ne_and_trace_eq :
    run Edition.e2021.rules commutingTailProg ≠ run Edition.e2024.rules commutingTailProg ∧
    trace Edition.e2021.rules commutingTailProg = trace Edition.e2024.rules commutingTailProg := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:866-868
theorem ifLetInTailProg_tail_rule_changes_run :
    ¬ NoTailEscapingTemps ifLetInTailProg ∧
    run ⟨true, false⟩ ifLetInTailProg ≠ run ⟨false, false⟩ ifLetInTailProg := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:872-874
theorem ifLetElseProg_not_noIfLetEscapingTemps_and_ifLet_rule_changes_run :
    ¬ NoIfLetEscapingTemps ifLetElseProg ∧
    run ⟨true, true⟩ ifLetElseProg ≠ run ⟨true, false⟩ ifLetElseProg := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:879-881
theorem ifLetInTailProg_rules_interact :
    run ⟨true, true⟩ ifLetInTailProg = run ⟨false, true⟩ ifLetInTailProg ∧
    run ⟨true, false⟩ ifLetInTailProg ≠ run ⟨false, false⟩ ifLetInTailProg := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:937-939
theorem ifLetElseProg_noTailEscapingTemps_and_traces_differ :
    NoTailEscapingTemps ifLetElseProg ∧
    trace Edition.e2021.rules ifLetElseProg ≠ trace Edition.e2024.rules ifLetElseProg := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:944-948
theorem ifLetInTailProg_toMatch_e2024_ne_e2021 :
    ¬ NoTailEscapingTemps ifLetInTailProg ∧
    run Edition.e2024.rules (toMatch ifLetInTailProg) ≠ run Edition.e2021.rules ifLetInTailProg ∧
    trace Edition.e2024.rules (toMatch ifLetInTailProg) = [.dtor 1, .dtor 0] ∧
    trace Edition.e2021.rules ifLetInTailProg = [.dtor 0, .dtor 1] := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:954-962
theorem refuted_emptyTailDtors_give_run_eq :
    ¬ NoTailEscapingTemps silentTailProg ∧
    trace Edition.e2024.rules (toMatch silentTailProg) = trace Edition.e2021.rules silentTailProg ∧
    run Edition.e2024.rules (toMatch silentTailProg) ≠ run Edition.e2021.rules silentTailProg ∧
    ¬ NoTailEscapingTemps silentRefCellTailProg ∧
    trace Edition.e2024.rules (toMatch silentRefCellTailProg) =
      trace Edition.e2021.rules silentRefCellTailProg ∧
    accepts Edition.e2024.rules (toMatch silentRefCellTailProg) = true ∧
    accepts Edition.e2021.rules silentRefCellTailProg = false := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:978-980
theorem commutingTailProg_flipped_and_all_commute :
    (∃ a b, Flipped commutingTailProg a b) ∧
    (∀ a b, Flipped commutingTailProg a b → Commute a b) := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:997-1000
theorem tailProg_flipped_not_commute_and_traces_differ :
    Flipped tailProg tailProgLocalDrop tailProgTempDrop ∧
    ¬ Commute tailProgLocalDrop tailProgTempDrop ∧
    trace Edition.e2021.rules tailProg ≠ trace Edition.e2024.rules tailProg :=
```

```lean
-- lean/ToyDropScope/DropResults.lean:1006-1009
theorem refCellTailProg_flipped_commute_and_trace_eq_and_accepts_ne :
    (∀ a b, Flipped refCellTailProg a b → Commute a b) ∧
    trace Edition.e2021.rules refCellTailProg = trace Edition.e2024.rules refCellTailProg ∧
    accepts Edition.e2021.rules refCellTailProg ≠ accepts Edition.e2024.rules refCellTailProg := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:1075-1076
theorem elseSite_dtorOnly_hypothesis_holds :
    ∀ ev ∈ dropOrderEvents [[.dtor 0]], ∃ n, ev = .dtor n := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:1084-1087
theorem elseSite_commute_iff_of_dtorOnly_hypothesis_tight :
    ¬ (∀ ev ∈ dropOrderEvents [[.out 1]], ∃ n, ev = .dtor n) ∧
    ¬ ([1].map Ev.out ++ dropOrderEvents [[.out 1]] = dropOrderEvents [[.out 1]] ++ [1].map Ev.out ↔
        [1] = [] ∨ dropOrderEvents [[.out 1]] = []) := by
```

```lean
-- lean/ToyDropScope/DropResults.lean:1095-1103
theorem site_examples :
    trace Edition.e2021.rules commutingTailProg = trace Edition.e2024.rules commutingTailProg ∧
    trace Edition.e2021.rules (tailSiteProg [[.dtor 0]] [[.dtor 1]]) ≠
      trace Edition.e2024.rules (tailSiteProg [[.dtor 0]] [[.dtor 1]]) ∧
    trace Edition.e2021.rules (elseSiteProg [[]] [1]) = trace Edition.e2024.rules (elseSiteProg [[]] [1]) ∧
    trace Edition.e2021.rules (elseSiteProg [[.dtor 0]] [1]) ≠
      trace Edition.e2024.rules (elseSiteProg [[.dtor 0]] [1]) ∧
    trace Edition.e2021.rules (elseSiteProg [[.out 1]] [1]) = [.out 1, .out 1] ∧
    trace Edition.e2024.rules (elseSiteProg [[.out 1]] [1]) = [.out 1, .out 1] := by decide
```

```lean
-- lean/ToyDropScope/DropResults.lean:1106
def ababTempDrop : Act := .dropTemp [0, 1, 0, 1, 1, 0] [] [.dtor 0]
```

```lean
-- lean/ToyDropScope/DropResults.lean:1108
def ababLocalDrop : Act := .dropLocal [0] 0 [.dtor 1]
```

```lean
-- lean/ToyDropScope/Examples.lean:14
def tailProg : Expr := .block (.letS 0 [.dtor 0] .unit (.tail (.temp [.dtor 1] [])))
```

```lean
-- lean/ToyDropScope/Examples.lean:17
def ifLetElseProg : Expr := .ifLet false (.temp [.dtor 0] []) .unit (.out 1)
```

```lean
-- lean/ToyDropScope/Examples.lean:22
def refCellTailProg : Expr := .block (.letS 0 [] .unit (.tail (.temp [.dtor 1] [0])))
```

```lean
-- lean/ToyDropScope/Examples.lean:27-30
def stmtTempsProg : Expr :=
  .block (.letS 0 [.dtor 0] (.temp [.dtor 1] [])
    (.exprS (.ifLet false .unit (.temp [.dtor 2] []) (.seq (.temp [.dtor 3] []) (.out 0)))
      (.tail (.out 1))))
```

```lean
-- lean/ToyDropScope/Examples.lean:33
def silentTailProg : Expr := .block (.letS 0 [] .unit (.tail (.temp [] [])))
```

```lean
-- lean/ToyDropScope/Examples.lean:36
def silentRefCellTailProg : Expr := .block (.letS 0 [] .unit (.tail (.temp [] [0])))
```

```lean
-- lean/ToyDropScope/Examples.lean:40
def topLevelTailTempProg : Expr := .block (.tail (.temp [.dtor 0] []))
```

```lean
-- lean/ToyDropScope/Examples.lean:43
def bareIfLetThenProg : Expr := .ifLet true (.temp [.dtor 0] []) .unit .unit
```

```lean
-- lean/ToyDropScope/Examples.lean:48-49
def matchInIfLetScrutProg : Expr :=
  .ifLet false (.matchE true (.temp [.dtor 0] []) .unit .unit) .unit (.out 1)
```

```lean
-- lean/ToyDropScope/Examples.lean:53
def siblingTailProg : Expr := .seq (.block (.tail (.temp [.dtor 0] []))) (.out 1)
```

```lean
-- lean/ToyDropScope/Examples.lean:64
theorem edition_rules_e2024 : Edition.e2024.rules = ⟨true, true⟩ := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:67
theorem edition_rules_e2021_ne_e2024 : Edition.e2021.rules ≠ Edition.e2024.rules := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:72
theorem trace_tailProg_e2024 : trace Edition.e2024.rules tailProg = [.dtor 1, .dtor 0] := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:75
theorem trace_tailProg_e2021 : trace Edition.e2021.rules tailProg = [.dtor 0, .dtor 1] := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:78-79
theorem trace_tailProg_e2024_ne_local_first :
    trace Edition.e2024.rules tailProg ≠ [.dtor 0, .dtor 1] := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:83-87
theorem trace_letInitTemp_both :
    trace Edition.e2021.rules (.block (.letS 0 [] (.temp [.dtor 1] []) (.tail (.out 0))))
      = [.dtor 1, .out 0] ∧
    trace Edition.e2024.rules (.block (.letS 0 [] (.temp [.dtor 1] []) (.tail (.out 0))))
      = [.dtor 1, .out 0] := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:91-92
theorem trace_ifLetElseProg_e2024 :
    trace Edition.e2024.rules ifLetElseProg = [.dtor 0, .out 1] := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:96-98
theorem trace_ifLetThen_e2024 :
    trace Edition.e2024.rules (.ifLet true (.temp [.dtor 0] []) (.out 1) .unit)
      = [.out 1, .dtor 0] := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:102-103
theorem trace_ifLetElseProg_e2021_ne_scrutinee_first :
    trace Edition.e2021.rules ifLetElseProg ≠ [.dtor 0, .out 1] := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:106-107
theorem trace_two_temps_reverse :
    trace Edition.e2021.rules (.seq (.temp [.dtor 0] []) (.temp [.dtor 1] [])) = [.dtor 1, .dtor 0] :=
```

```lean
-- lean/ToyDropScope/Examples.lean:113
theorem isDropTemp_dropTemp : (Act.dropTemp [] [] [.dtor 0]).isDropTemp = true := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:116
theorem not_isDropTemp_dropLocal : (Act.dropLocal [] 0 [.dtor 0]).isDropTemp = false := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:120-122
theorem mkTemps_dropTemps_tailProg :
    mkTemps (run Edition.e2021.rules tailProg) = [([0, 1, 0], [])] ∧
    dropTemps (run Edition.e2021.rules tailProg) = [([0, 1, 0], [])] := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:126-127
theorem dropTemps_mkTemp_mkTemps_dropTemp :
    dropTemps [.mkTemp [] []] = [] ∧ mkTemps [.dropTemp [] [] []] = [] := ⟨rfl, rfl⟩
```

```lean
-- lean/ToyDropScope/Examples.lean:132
theorem accepts_refCellTailProg_e2024 : accepts Edition.e2024.rules refCellTailProg = true := by
```

```lean
-- lean/ToyDropScope/Examples.lean:137
theorem accepts_refCellTailProg_e2021 : accepts Edition.e2021.rules refCellTailProg = false := by
```

```lean
-- lean/ToyDropScope/Examples.lean:141
theorem accepts_unboundBorrow : accepts Edition.e2024.rules (.temp [] [5]) = false := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:146-151
theorem borrowOK_shadowing_limitation :
    run Edition.e2021.rules shadowedBorrowProg =
      [.mkLocal [0] 0, .mkLocal [0, 0, 1, 0] 0, .mkTemp [0, 1, 0, 0, 1, 0] [0],
       .dropLocal [0, 0, 1, 0] 0 [], .dropTemp [0, 1, 0, 0, 1, 0] [0] [.dtor 1],
       .dropLocal [0] 0 []] ∧
    accepts Edition.e2021.rules shadowedBorrowProg = true := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:156
theorem behIncl_refl (R : Rules) : BehIncl R R := fun _ _ h => h
```

```lean
-- lean/ToyDropScope/Examples.lean:160-162
theorem not_behIncl_e2021_e2024_at_tailProg :
    beh Edition.e2021.rules tailProg = some [.dtor 0, .dtor 1] ∧
    beh Edition.e2024.rules tailProg = some [.dtor 1, .dtor 0] := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:167-168
theorem toMatch_ifLetElseProg :
    toMatch ifLetElseProg = .matchE false (.temp [.dtor 0] []) .unit (.out 1) := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:171
theorem toMatch_ifLetElseProg_ne : toMatch ifLetElseProg ≠ ifLetElseProg := by
```

```lean
-- lean/ToyDropScope/Examples.lean:177
theorem noEscape_letInit : noEscape (.block (.letS 0 [] (.temp [] []) (.tail .unit))) = true := by
```

```lean
-- lean/ToyDropScope/Examples.lean:181
theorem noEscape_matchArms : noEscape (.matchE true .unit (.temp [] []) (.temp [] [])) = true := by
```

```lean
-- lean/ToyDropScope/Examples.lean:185
theorem noEscape_temp : noEscape (.temp [] []) = false := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:188
theorem noEscape_ifLetScrut : noEscape (.ifLet true (.temp [] []) .unit .unit) = false := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:193
theorem noTailEscapingTemps_stmtTempsProg : NoTailEscapingTemps stmtTempsProg := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:196
theorem not_noTailEscapingTemps_tailProg : ¬ NoTailEscapingTemps tailProg := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:200-201
theorem not_noTailEscapingTemps_nested :
    ¬ NoTailEscapingTemps (.block (.tail (.block (.tail (.temp [] []))))) := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:204
theorem noIfLetEscapingTemps_stmtTempsProg : NoIfLetEscapingTemps stmtTempsProg := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:207
theorem not_noIfLetEscapingTemps_ifLetElseProg : ¬ NoIfLetEscapingTemps ifLetElseProg := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:217-221
theorem run_tailProg :
    run Edition.e2021.rules tailProg =
      [.mkLocal [0] 0, .mkTemp [0, 1, 0] [], tailProgLocalDrop, tailProgTempDrop] ∧
    run Edition.e2024.rules tailProg =
      [.mkLocal [0] 0, .mkTemp [0, 1, 0] [], tailProgTempDrop, tailProgLocalDrop] := by
```

```lean
-- lean/ToyDropScope/Examples.lean:225
theorem flipped_tailProg : Flipped tailProg tailProgLocalDrop tailProgTempDrop := by
```

```lean
-- lean/ToyDropScope/Examples.lean:230-231
theorem not_flipped_tailProg_mkLocal :
    ¬ Flipped tailProg (.mkLocal [0] 0) tailProgLocalDrop := by
```

```lean
-- lean/ToyDropScope/Examples.lean:252-253
theorem commute_same_event :
    Commute (.dropLocal [] 0 [.dtor 0]) (.dropTemp [1] [] [.dtor 0]) := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:256
theorem not_commute_tailProg : ¬ Commute tailProgLocalDrop tailProgTempDrop := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:266
theorem target_orderingSwitch_0 : orderingSwitch.target 0 = .goto 1 := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:270
theorem target_orderingSwitch_2 : orderingSwitch.target 2 = .goto 3 := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:273
theorem exec_ok : exec (fun _ => false) (fun _ => true) orderingSwitch 1 = .ret 2 := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:276
theorem exec_readUB : exec (fun _ => true) (fun _ => true) orderingSwitch 1 = .ub := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:279
theorem runArm_usePayload_ok : runArm (fun _ => true) 0 (.usePayload 7) = .ret 7 := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:282
theorem runArm_usePayload_bad : runArm (fun _ => false) 0 (.usePayload 7) = .ub := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:285
theorem refines_ub (o : Outcome) : Refines o .ub := Or.inl rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:288
theorem not_refines_ub_ret : ¬ Refines .ub (.ret 0) := by simp [Refines]
```

```lean
-- lean/ToyDropScope/Examples.lean:291
theorem refines_ret_eq : Refines (.ret 3) (.ret 3) := Or.inr rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:294
theorem not_refines_ret_ne : ¬ Refines (.ret 0) (.ret 1) := by simp [Refines]
```

```lean
-- lean/ToyDropScope/Examples.lean:297
theorem allowedTag_pos : allowedTag 3 (fun _ => true) 2 = true := rfl
```

```lean
-- lean/ToyDropScope/Examples.lean:300-301
theorem allowedTag_neg :
    allowedTag 3 (fun _ => true) 3 = false ∧ allowedTag 3 (fun t => t != 1) 1 = false := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:305
theorem remainingAllowed_orderingSwitch : remainingAllowed 3 (fun _ => true) orderingSwitch = [2] := by
```

```lean
-- lean/ToyDropScope/Examples.lean:310-311
theorem remainingAllowed_all_covered :
    remainingAllowed 3 (fun _ => true) ⟨[(0, .goto 0), (1, .goto 1), (2, .goto 2)], .goto 3⟩ = [] := by
```

```lean
-- lean/ToyDropScope/Examples.lean:317-320
theorem lastVariantTakesWildcard_no_remaining :
    lastVariantTakesWildcard 3 (Enum.inhabitedTag [true, false, true])
        ⟨[(0, .goto 0), (2, .goto 2)], .goto 1⟩ =
      ⟨[(0, .goto 0), (2, .goto 2)], .unreachable⟩ := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:325-327
theorem lastVariantTakesWildcard_orderingSwitch :
    lastVariantTakesWildcard 3 (fun _ => true) orderingSwitch =
      ⟨[(0, .goto 1), (1, .goto 2), (2, .goto 3)], .unreachable⟩ := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:331-332
theorem lastVariantTakesWildcard_two_remaining :
    lastVariantTakesWildcard 3 (fun _ => true) ⟨[(0, .goto 1)], .goto 3⟩ = ⟨[(0, .goto 1)], .goto 3⟩ :=
```

```lean
-- lean/ToyDropScope/Examples.lean:336-338
theorem pruneArms_example :
    pruneArms 2 (fun t => t == 0) ⟨[(0, .goto 0), (1, .goto 1)], .goto 2⟩ =
      ⟨[(0, .goto 0), (1, .unreachable)], .goto 2⟩ := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:341-343
theorem pruneArms_keeps_allowed :
    pruneArms 2 (fun _ => true) ⟨[(0, .goto 0), (1, .goto 1)], .goto 2⟩ =
      ⟨[(0, .goto 0), (1, .goto 1)], .goto 2⟩ := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:347-348
theorem readUB_rejectUninhabited :
    readUB ⟨.rejectUninhabited, .rejectInvalid⟩ [true, false] 1 = true := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:351
theorem readUB_permissive : readUB ⟨.permissive, .rejectInvalid⟩ [true, false] 1 = false := by
```

```lean
-- lean/ToyDropScope/Examples.lean:356
theorem readUB_inhabited (D : DiscrSem) : readUB D [true, false] 0 = false := by
```

```lean
-- lean/ToyDropScope/Examples.lean:361-363
theorem readUB_invalid :
    readUB ⟨.permissive, .rejectInvalid⟩ [true] 1 = true ∧
    readUB ⟨.rejectUninhabited, .passThrough⟩ [true] 1 = false := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:367-369
theorem readUB_emptyEnum :
    readUB ⟨.rejectUninhabited, .passThrough⟩ [] 0 = false ∧
    readUB ⟨.permissive, .rejectInvalid⟩ [] 0 = true := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:373
def exampleNiche : NicheEnc := ⟨0, 1, 2, 2⟩
```

```lean
-- lean/ToyDropScope/Examples.lean:377
theorem decode_exampleNiche : exampleNiche.decode 2 = 1 ∧ exampleNiche.decode 3 = 2 := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:381-382
theorem decode_exampleNiche_untagged :
    exampleNiche.decode 0 = 0 ∧ exampleNiche.decode 1 = 0 ∧ exampleNiche.decode 4 = 0 := by decide
```

```lean
-- lean/ToyDropScope/Examples.lean:386-387
theorem decode_of_nicheHi_lt_nicheLo (N : NicheEnc) (h : N.nicheHi < N.nicheLo) (v : Nat) :
    N.decode v = N.untagged := by
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:15
def rejectBoth : DiscrSem := ⟨.rejectUninhabited, .rejectInvalid⟩
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:19
def permissiveRejectInvalid : DiscrSem := ⟨.permissive, .rejectInvalid⟩
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:23
def deadNicheEnum : Enum := [true, false, true]
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:26
def deadNicheSwitch : Switch := ⟨[(0, .goto 0), (2, .goto 2)], .goto 1⟩
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:39-40
theorem readUB_rejectBoth_of_allowedTag_eq_false (E : Enum) (t : Nat)
    (h : allowedTag E.length E.inhabitedTag t = false) : readUB rejectBoth E t = true := by
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:223-225
theorem deadNicheEnum_rejectBoth_satisfies_hypothesis :
    ∀ t, allowedTag deadNicheEnum.length deadNicheEnum.inhabitedTag t = false →
      readUB rejectBoth deadNicheEnum t = true :=
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:231-237
theorem specializeSwitch_eq_hypothesis_tight :
    ¬ (∀ t, allowedTag 3 deadNicheEnum.inhabitedTag t = false →
        readUB permissiveRejectInvalid deadNicheEnum t = true) ∧
    exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
        (specializeSwitch 3 deadNicheEnum.inhabitedTag deadNicheSwitch) 1 ≠
      exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
        deadNicheSwitch 1 := by
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:245-252
theorem specializeSwitch_deadNicheSwitch_permissive_not_refines :
    ¬ (∀ t, allowedTag 3 deadNicheEnum.inhabitedTag t = false →
        readUB permissiveRejectInvalid deadNicheEnum t = true) ∧
    ¬ Refines
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          (specializeSwitch 3 deadNicheEnum.inhabitedTag deadNicheSwitch) 1)
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          deadNicheSwitch 1) := by
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:260-267
theorem pruneArms_explicitUninhabitedArm_permissive_not_refines :
    pruneArms 3 deadNicheEnum.inhabitedTag explicitUninhabitedArmSwitch ≠
      explicitUninhabitedArmSwitch ∧
    ¬ Refines
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          (pruneArms 3 deadNicheEnum.inhabitedTag explicitUninhabitedArmSwitch) 1)
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          explicitUninhabitedArmSwitch 1) := by
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:277-293
theorem lastVariantTakesWildcard_permissive_not_refines_both_branches :
    remainingAllowed 3 deadNicheEnum.inhabitedTag deadNicheSwitch = [] ∧
    ¬ Refines
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          (lastVariantTakesWildcard 3 deadNicheEnum.inhabitedTag deadNicheSwitch) 1)
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          deadNicheSwitch 1) ∧
    remainingAllowed 4 (Enum.inhabitedTag [true, false, true, true])
        ⟨[(0, .goto 1), (2, .goto 2)], .goto 3⟩ = [3] ∧
    ¬ Refines
        (exec (readUB permissiveRejectInvalid [true, false, true, true])
          (Enum.inhabitedTag [true, false, true, true])
          (lastVariantTakesWildcard 4 (Enum.inhabitedTag [true, false, true, true])
            ⟨[(0, .goto 1), (2, .goto 2)], .goto 3⟩) 1)
        (exec (readUB permissiveRejectInvalid [true, false, true, true])
          (Enum.inhabitedTag [true, false, true, true])
          ⟨[(0, .goto 1), (2, .goto 2)], .goto 3⟩ 1) := by
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:300-302
theorem refuted_specializeSwitch_retargets_every_nonAllowed_tag :
    allowedTag 3 deadNicheEnum.inhabitedTag 1 = false ∧
    (specializeSwitch 3 deadNicheEnum.inhabitedTag ⟨[], .goto 7⟩).target 1 = .goto 7 := by decide
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:307-308
theorem refuted_allInhabited_specializeEnum_changes_nothing :
    specializeEnum [true, true, true] orderingSwitch ≠ orderingSwitch := by decide
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:404-407
theorem permissive_allInhabited_orderingSwitch_same :
    ∀ t, t < 3 → runSwitch permissiveRejectInvalid [true, true, true]
        (specializeEnum [true, true, true] orderingSwitch) t =
      runSwitch permissiveRejectInvalid [true, true, true] orderingSwitch t := by decide
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:412-417
theorem usePayloadSwitch_permissive_specializeEnum_refines :
    specializeEnum deadNicheEnum usePayloadSwitch ≠ usePayloadSwitch ∧
    readUB permissiveRejectInvalid deadNicheEnum 1 = false ∧
    ∀ t, Refines
      (runSwitch permissiveRejectInvalid deadNicheEnum (specializeEnum deadNicheEnum usePayloadSwitch) t)
      (runSwitch permissiveRejectInvalid deadNicheEnum usePayloadSwitch t) := by
```

```lean
-- lean/ToyDropScope/SwitchResults.lean:465-468
theorem rejectBoth_deadNicheSwitch_same :
    specializeEnum deadNicheEnum deadNicheSwitch ≠ deadNicheSwitch ∧
    ∀ t, t < 5 → runSwitch rejectBoth deadNicheEnum (specializeEnum deadNicheEnum deadNicheSwitch) t =
      runSwitch rejectBoth deadNicheEnum deadNicheSwitch t := by decide
```

### External sources (verbatim quotes)

`rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:54` (verbatim):

```text
In 2021 the local variable `c` is dropped before the temporary created by `c.borrow()`. The 2024 Edition changes this so that the temporary value `c.borrow()` is dropped first, followed by dropping the local variable `c`, allowing the code to compile as expected.
```

`rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:58` (verbatim):

```text
When a temporary is created in order to evaluate an expression, the temporary is dropped based on the [temporary scope rules]. Those rules define how long the temporary will be kept alive. Before 2024, temporaries from tail expressions of a block would be extended outside the block to the next temporary scope boundary. In many cases this would be the end of a statement or function body. In 2024, the temporaries of the tail expression may now be dropped immediately at the end of the block (before any local variables in the block).
```

`rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:62-69` (verbatim):

````text
```rust,edition2024,E0716,compile_fail
// This example works in 2021, but fails to compile in 2024.
fn main() {
    let x = { &String::from("1234") }.len();
}
```

In this example, in 2021, the temporary `String` is extended outside of the block, past the call to `len()`, and is dropped at the end of the statement. In 2024, it is dropped immediately at the end of the block, causing a compile error about the temporary being dropped while borrowed.
````

`rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-tail-expr-scope.md:90` (verbatim):

```text
Unfortunately, there are no semantics-preserving rewrites to shorten the lifetime for temporary values in tail expressions[^RFC3606]. The [`tail_expr_drop_order`] lint detects if a temporary value with a custom, non-trivial `Drop` destructor is generated in a tail expression. Warnings from this lint will appear when running `cargo fix --edition`, but will otherwise not automatically make any changes. It is recommended to manually inspect the warnings and determine whether or not you need to make any adjustments.
```

`rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-if-let-scope.md:5` (verbatim):

```text
- In an `if let $pat = $expr { .. } else { .. }` expression, the temporary values generated from evaluating `$expr` will be dropped before the program enters the `else` branch instead of after.
```

`rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f:src/rust-2024/temporary-if-let-scope.md:32` (verbatim):

```text
The 2024 Edition shortens the lifetime of the temporaries to the point where the then-block is completely evaluated or the program control enters the `else` block.
```

`rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/3606-temporary-lifetimes-in-tail-expressions.md:53-61` (verbatim):

```text
Temporaries are normally dropped at the end of the statement.

The tail expression of a block
(such as a function body, if/else body, match arm, block expression, etc.)
is not a statement, so has its own rule:

- Starting in Rust 2024,
  temporaries in tail expressions are dropped after evaluating the tail expression,
  but before dropping any local variables of the block.
```

`rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/3606-temporary-lifetimes-in-tail-expressions.md:78-79` (verbatim):

```text
For blocks/bodies/arms whose `{}` tokens come from Rust 2024 code,
temporaries in the tail expression will be dropped *before* the locals of the block are dropped.
```

`rust-lang/reference@84dc36ff4712fad6829b6063cd4acbcaf5381708:src/destructors.md:281-282` (verbatim):

```text
> [!NOTE]
> The [scrutinee] of a `match` expression is not a temporary scope, so temporaries in the scrutinee can be dropped after the `match` expression. For example, the temporary for `1` in `match 1 { ref mut z => z };` lives until the end of the statement.
```

`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:1` (verbatim):

```text
//! A pass that eliminates branches on uninhabited or unreachable enum variants.
```

`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:123-167` (verbatim):

```text
            for (index, (val, _)) in targets.iter().enumerate() {
                if !allowed_variants.remove(&val) {
                    unreachable_targets.push(index);
                }
            }

            // If and only if there is a variant that does not have a branch set, change the
            // current of otherwise as the variant branch and set otherwise to unreachable. It
            // transforms the following code
            // ```rust
            // match c {
            //     Ordering::Less => 1,
            //     Ordering::Equal => 2,
            //     _ => 3,
            // }
            // ```
            // to
            // ```rust
            // match c {
            //     Ordering::Less => 1,
            //     Ordering::Equal => 2,
            //     Ordering::Greater => 3,
            // }
            // ```
            let replace_otherwise_to_unreachable = allowed_variants.len() <= 1
                && !body.basic_blocks[targets.otherwise()].is_empty_unreachable();
            if unreachable_targets.is_empty() && !replace_otherwise_to_unreachable {
                continue;
            }

            let unreachable_block = patch.unreachable_no_cleanup_block();
            let mut targets = targets.clone();
            if replace_otherwise_to_unreachable {
                let otherwise_is_last_variant = allowed_variants.len() == 1;
                if otherwise_is_last_variant {
                    // We have checked that `allowed_variants` has only one element.
                    #[allow(rustc::potential_query_instability)]
                    let last_variant = *allowed_variants.iter().next().unwrap();
                    targets.add_target(last_variant, targets.otherwise());
                }
                unreachable_targets.push(targets.iter().count());
            }
            for index in unreachable_targets.iter() {
                targets.all_targets_mut()[*index] = unreachable_block;
            }
```

`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1412-1422` (verbatim):

```text
    /// Computes the discriminant of the place, returning it as an integer of type
    /// [`discriminant_ty`]. Returns zero for types without discriminant.
    ///
    /// The validity requirements for the underlying value are undecided for this rvalue, see
    /// [#91095]. Note too that the value of the discriminant is not the same thing as the
    /// variant index; use [`discriminant_for_variant`] to convert.
    ///
    /// [`discriminant_ty`]: crate::ty::Ty::discriminant_ty
    /// [#91095]: https://github.com/rust-lang/rust/issues/91095
    /// [`discriminant_for_variant`]: crate::ty::Ty::discriminant_for_variant
    Discriminant(Place<'tcx>),
```

`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_abi/src/lib.rs:2013-2015` (verbatim):

```text
    /// To recover the variant index `i` from a `tag`, the above formula has to be reversed,
    /// i.e. `i = tag.wrapping_sub(niche_start) + niche_variants.start`. If `i` ends up outside
    /// `niche_variants`, the tag must have encoded the `untagged_variant`.
```

`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_abi/src/lib.rs:2022-2029` (verbatim):

```text
    /// Other variants that are not `untagged_variant` and that are outside the `niche_variants`
    /// range cannot be represented; they must be uninhabited.
    /// Nonetheless, uninhabited variants can also fall into the range of `niche_variants`.
    Niche {
        untagged_variant: VariantIdx,
        /// This range *may* contain `untagged_variant` or uninhabited variants;
        /// these are then just "dead values" and not used to encode anything.
        niche_variants: RangeInclusive<VariantIdx>,
```

`rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/0066-better-temporary-lifetimes.md:7-10` (verbatim):

```text
Temporaries live for the enclosing block when found in a let-binding. This only
holds when the reference to the temporary is taken directly. This logic should
be extended to extend the cleanup scope of any temporary whose lifetime ends up
in the let-binding.
```

`minirust/minirust@063d784186d3252bee242217f218223205c0b568:spec/lang/step/expressions.md:123-125` (verbatim):

```text
        let Some(discriminant) = decode_discriminant::<M>(accessor, discriminator)? else {
            throw_ub!("ValueExpr::GetDiscriminant encountered invalid discriminant.");
        };
```

rust-lang/rust#91095 (open issue, title 'Decide on when MIR Discriminant() operation is UB') is mentioned in prose for orientation; it is not normative, not relied on, and not a subject.

### Prior-art search

Web searches (2026-11-21): 'formal semantics Rust temporary lifetime drop scope tail expression edition 2024 mechanized'; '"UnreachableEnumBranching" discriminant uninhabited variant undefined behavior soundness'; 'arXiv formal semantics Rust source code temporaries drop order destructors edition K framework OR Lean OR Coq'. Hits were general explanations of the edition change and general Rust semantics projects; none was found to contain a mechanized edition-indexed trace statement, a migration commutation condition, or a semantics-parametric soundness characterization of the specialization. The trace-theory, combinatorics-on-words, refinement and Rust-semantics references cited in the cards were checked for existence and bibliographic data (DOI resolution and publisher metadata, 2026-11-21); the MiniRust and RFC 66 citations were checked against the pinned files. Tier T1 throughout; no T3 claim.

## Boundaries

### Non-claims

Non-claims come first: each card's list says what the card does not show. Read the list of a card before relying on it.

#### Non-claims: R1 (theorem, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- The hypotheses are sufficient for equal action lists, not necessary: `noEscape_hypotheses_not_necessary_for_run_eq` gives `topLevelTailTempProg`, which violates `NoTailEscapingTemps` and has equal 2021 and 2024 action lists. Equal traces are weaker than equal action lists: `commutingTailProg_run_ne_and_trace_eq` has different action lists and equal traces (R4-if and R4-site give conditions on traces).
- `NoTailEscapingTemps` and `NoIfLetEscapingTemps` are syntactic checks on the toy syntax; they are not the `tail_expr_drop_order` or `if_let_rescope` lints, and the package proves nothing about those lints.
- Not modeled: temporary lifetime extension; per-block editions for macro-generated code (RFC 3606 applies the tail rule according to the edition of a block's `{}` tokens); `else if let` chains and `let` chains; closures, `async` and `const` blocks; destructuring assignment; unwinding and panics; loops and `while let`; `if` conditions, match guards and lazy boolean operators. `run` treats its argument as a whole function body without adding a block around it, and in a `letS` statement the initializer's temporaries are dropped before the local is bound.

#### Non-claims: R1-split (theorem, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- The two rule switches are a modeling choice of the toy (`Rules`); no real compiler is claimed to expose them separately.
- Each hypothesis is sufficient, not necessary: `noEscape_hypotheses_not_necessary_for_run_eq` gives `topLevelTailTempProg` (violates `NoTailEscapingTemps`; the tail rule leaves its action list unchanged at both settings of the `if let` rule) and `bareIfLetThenProg` (violates `NoIfLetEscapingTemps`; the `if let` rule leaves its action list unchanged at both settings of the tail rule).
- The card does not say that the two rules are non-interacting on programs outside both classes: `ifLetInTailProg_rules_interact` shows that for `ifLetInTailProg` the tail rule changes the action list when the `if let` rule is off and leaves it unchanged when the `if let` rule is on.
- The constructs listed as not modeled in R1 are not modeled here either.

#### Non-claims: R1-perm (theorem, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- Branch outcomes are fixed in the toy syntax (`hit : Bool`), destructors cannot change state, and nothing panics, so rescoping cannot change which branches or drops execute in the toy; this neither establishes nor refutes whether changing drop order in Rust can change control flow, unwinding or poisoning behaviour.
- Exactly-once destruction here is a property of the toy elaboration, which has no moves, no conditional initialization and no unwinding; drop flags and partial moves are the subject of the published drop-flag package and are not modeled here. The card says nothing about temporaries in branches that do not run.
- The card does not say that a temporary is dropped after it is created (an ordering property between a creation and its drop); it states the permutation, duplicate-freeness, counting and relative-order facts above.

#### Non-claims: R1-match-tail (counterexample, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- `refuted_match_outside_blockTail_same_drop_point` refutes, in the toy, the reading that a `match` scrutinee temporary has the same drop point in both editions whenever the `match` is outside block tail positions: in `matchInIfLetScrutProg` the `match` scrutinee temporary escapes into an enclosing `if let` scrutinee and the `if let` rule moves it. The drop point agrees in both editions when both `NoTailEscapingTemps` and `NoIfLetEscapingTemps` hold (R1).
- RFC 3606 at text/3606-temporary-lifetimes-in-tail-expressions.md:53-61 describes the tail rule for Rust 2024; this card is about the toy model and neither establishes nor refutes rustc's behaviour.

#### Non-claims: R2 (counterexample, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- The toy borrow check models one direction of the documented acceptance change (a temporary may not outlive a local it borrows). It has no borrows of temporaries, so it cannot express programs accepted under 2021 and rejected under 2024 (the Edition Guide documents such a program at temporary-tail-expr-scope.md:62-69). Whether acceptance under the toy 2021 rules implies acceptance under the toy 2024 rules for every toy program is not proved here and is not a claim about Rust.
- `borrowOK` tracks live locals as a multiset of `Nat` names, not binders: shadowing an outer local with the same name hides the inner local's drop (`borrowOK_shadowing_limitation`). It models no `&mut` exclusivity, no non-lexical lifetimes and no borrows of temporaries.
- Escape hatches for the incomparability: comparability holds on the class of R1 (`trace_accepts_beh_eq_of_noTailEscapingTemps_of_noIfLetEscapingTemps`); action lists agree up to permutation for every program (R1-perm); traces agree when every flipped pair commutes (R4-if), although verdicts of `accepts` may still differ (`refCellTailProg_flipped_commute_and_trace_eq_and_accepts_ne`).
- No destructor-order measurement of any real compilation is made; every trace is a trace of the toy semantics.
- `BehIncl` is the inclusion of accepted behaviours of a deterministic toy semantics; it is not a refinement relation on Rust programs.

#### Non-claims: R3-match (theorem, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- In the toy the rewrite does not in general reproduce, under the 2024 rules, the 2021 action list: the tail rule still applies to the resulting `match` (R3-migration and its tightness counterexample `ifLetInTailProg_toMatch_e2024_ne_e2021`).
- `toMatch` rewrites every `if let` of the program, in a language where `matchE` and `ifLet` with the `if let` rule off have the same evaluation; it does not model `let` chains, `else if let` chains, match ergonomics, autoref or type-inference differences between `if let` and `match`, and rewriting a single site in context is not stated separately.
- No claim about deadlocks or locks; a destructor event stands for any observable effect of a guard's destructor.

#### Non-claims: R3-migration (theorem, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- Without the hypothesis the statement is false in the toy (`ifLetInTailProg_toMatch_e2024_ne_e2021`). Nothing is claimed about rustc or about the `if_let_rescope` lint.
- The hypothesis is sufficient, not necessary: `noEscape_hypotheses_not_necessary_for_run_eq` gives `topLevelTailTempProg`, which violates `NoTailEscapingTemps` and for which the rewrite under the 2024 rules reproduces the 2021 action list.
- Empty destructor events do not remove the need for the hypothesis: `refuted_emptyTailDtors_give_run_eq` (which refutes the stronger reading that they do) shows that for `silentTailProg` (tail temporary and local with no destructor events) the traces agree but the action lists differ, and for `silentRefCellTailProg` the traces agree but the verdicts of `accepts` differ.
- The constructs listed as not modeled in R1 are not modeled here either.

#### Non-claims: R4-if (theorem, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- The converse is false in the toy: `ababProg_trace_eq_and_flipped_not_commute` (R4-not-necessary) has equal traces and a flipped pair that does not commute.
- Equal traces do not imply equal toy borrow-check verdicts or behaviours: `refCellTailProg_flipped_commute_and_trace_eq_and_accepts_ne` shows that `refCellTailProg` satisfies the hypothesis and has equal traces, yet `accepts` differs between the editions (so `beh` differs as well).
- `Commute` is word equality in the free monoid `List Ev`; it is not an independence relation on effects. Two non-empty event lists commute iff both are powers of a common word (classical; not proved in this package). Hence two actions emitting distinct single events (such as `[dtor 0]` and `[dtor 1]`, `not_commute_tailProg`), or non-empty event lists over disjoint alphabets, never commute, even when the effects they stand for are independent; distinct non-empty event lists that are powers of a common word do commute (`commute_distinct_nonempty_event_lists`: `[dtor 0]` and `[dtor 0, dtor 0]`).

#### Non-claims: R4-site (characterization, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- These are single-site shapes (one block with all temporaries in its tail, or one `if let` with a non-matching pattern, as the whole program); the commutation is of whole words, not of each temporary separately.
- Once a block or `if let` is nested inside a larger expression, a moved temporary can cross events outside the immediate block or `else` block (R4-window: `nestedTailProg_traces_differ`, `thenBranchProg_traces_differ`, `siblingTailProg_traces_differ`). No multi-site characterization is claimed; for general programs per-action commutation is sufficient (R4-if) but not necessary (R4-not-necessary).
- In `elseSiteProg` the `else` block emits `out` events; a destructor may also emit `out` events in the toy (`Ev.out` stands for any side effect). For destructors all of whose events are `dtor` events, the condition reduces to emptiness of one side (`elseSite_commute_iff_of_dtorOnly`).
- Equal traces do not imply equal toy borrow-check verdicts (`refCellTailProg_flipped_commute_and_trace_eq_and_accepts_ne`).

#### Non-claims: R4-not-necessary (counterexample, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- This refutes, in the toy, the reading 'trace preserved iff each moved temporary's destructor events commute with the events it is moved across'; it does not refute the single-site whole-word characterization R4-site.
- Escape hatch: the counterexample relies on distinct drop actions emitting the same event labels; it does not refute necessity of per-action commutation under an additional hypothesis that distinct actions emit pairwise disjoint event alphabets (not proved here).

#### Non-claims: R4-window (counterexample, T1)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's 2021 or 2024 editions, the Rust Reference, or any Rust compiler. Model–system relation: none proved.
- These show that the events a moved temporary crosses are not confined to its owning block's locals (tail) or to the `else` block (`if let`): under the 2021 rules the temporary survives until the enclosing temporary scope closes, which can include an outer block's locals, an output after a matching `if let`, or an output after a block with no locals. Commutation with the owning block's locals or with the `else` block alone is therefore not sufficient in the toy.

#### Non-claims: R5-eq (theorem, T1)

- These are statements about the toy switch model; they neither establish nor refute the corresponding claims about Rust's operational semantics, MIR `Rvalue::Discriminant` and `SwitchInt`, or rustc's unreachable-enum-branching pass. Model–system relation: none proved.
- The two uninhabited-variant read semantics (`UninhabitedRead.rejectUninhabited`, `UninhabitedRead.permissive`) are both kept open, following the documentation of `Rvalue::Discriminant`, which says that the validity requirements of that read are undecided (it links rust-lang/rust#91095, an open issue, mentioned here for orientation and not relied on); the package does not say which semantics Rust has. `InvalidRead.passThrough` is a modeling boundary of this package, not a candidate semantics taken from Rust documentation.
- The toy switch has no memory, aliasing model, partial moves or uninitialized bytes, and no MIR context (no statements between the discriminant read and the switch, no `Assume`, no cleanup blocks); tags equal variant indices (no custom discriminant values and no tagless single-variant layouts); explicit arms may repeat a value (the first one is selected); the pass's own applicability conditions are not modeled. The toy therefore does not engage with the considerations that bear on deciding the validity requirement of the discriminant read.
- Equality of outcomes includes equal undefined behaviour; it is a statement about the toy `exec`.
- The hypothesis does not say that every non-allowed tag is retargeted to `unreachable` on every switch: when two or more allowed tags lack an explicit arm, `lastVariantTakesWildcard` leaves the wildcard unchanged, and non-allowed tags reaching it keep their target (`refuted_specializeSwitch_retargets_every_nonAllowed_tag`, which refutes the stronger reading that every non-allowed tag is retargeted).

#### Non-claims: R5-iff (characterization, T1)

- These are statements about the toy switch model; they neither establish nor refute the corresponding claims about Rust's operational semantics, MIR `Rvalue::Discriminant` and `SwitchInt`, or rustc's unreachable-enum-branching pass. Model–system relation: none proved.
- The two uninhabited-variant read semantics (`UninhabitedRead.rejectUninhabited`, `UninhabitedRead.permissive`) are both kept open, following the documentation of `Rvalue::Discriminant`, which says that the validity requirements of that read are undecided (it links rust-lang/rust#91095, an open issue, mentioned here for orientation and not relied on); the package does not say which semantics Rust has. `InvalidRead.passThrough` is a modeling boundary of this package, not a candidate semantics taken from Rust documentation.
- The toy switch has no memory, aliasing model, partial moves or uninitialized bytes, and no MIR context (no statements between the discriminant read and the switch, no `Assume`, no cleanup blocks); tags equal variant indices (no custom discriminant values and no tagless single-variant layouts); explicit arms may repeat a value (the first one is selected); the pass's own applicability conditions are not modeled. The toy therefore does not engage with the considerations that bear on deciding the validity requirement of the discriminant read.
- Escape hatch: the left side quantifies over all switches, including switches whose arms ignore the payload (`goto`). A fixed switch can be refined although the condition fails: `usePayloadSwitch_permissive_specializeEnum_refines` shows a switch on `deadNicheEnum` whose arm for the uninhabited tag uses the payload and whose specialization refines it on every tag under `permissiveRejectInvalid`.

#### Non-claims: R5-iff-shapes (characterization, T1)

- These are statements about the toy switch model; they neither establish nor refute the corresponding claims about Rust's operational semantics, MIR `Rvalue::Discriminant` and `SwitchInt`, or rustc's unreachable-enum-branching pass. Model–system relation: none proved.
- The two uninhabited-variant read semantics (`UninhabitedRead.rejectUninhabited`, `UninhabitedRead.permissive`) are both kept open, following the documentation of `Rvalue::Discriminant`, which says that the validity requirements of that read are undecided (it links rust-lang/rust#91095, an open issue, mentioned here for orientation and not relied on); the package does not say which semantics Rust has. `InvalidRead.passThrough` is a modeling boundary of this package, not a candidate semantics taken from Rust documentation.
- The toy switch has no memory, aliasing model, partial moves or uninitialized bytes, and no MIR context (no statements between the discriminant read and the switch, no `Assume`, no cleanup blocks); tags equal variant indices (no custom discriminant values and no tagless single-variant layouts); explicit arms may repeat a value (the first one is selected); the pass's own applicability conditions are not modeled. The toy therefore does not engage with the considerations that bear on deciding the validity requirement of the discriminant read.
- The name `lastVariantTakesWildcard` describes its one-remaining branch; its zero-remaining branch (wildcard made `unreachable`, no arm added) is part of the rewrite and of both characterizations (`lastVariantTakesWildcard_no_remaining`).
- Escape hatch: as in R5-iff, a fixed switch whose arm for an uninhabited tag uses the payload can be refined although the condition fails (`usePayloadSwitch_permissive_specializeEnum_refines`).

#### Non-claims: R5-valid (characterization, T1)

- These are statements about the toy switch model; they neither establish nor refute the corresponding claims about Rust's operational semantics, MIR `Rvalue::Discriminant` and `SwitchInt`, or rustc's unreachable-enum-branching pass. Model–system relation: none proved.
- The two uninhabited-variant read semantics (`UninhabitedRead.rejectUninhabited`, `UninhabitedRead.permissive`) are both kept open, following the documentation of `Rvalue::Discriminant`, which says that the validity requirements of that read are undecided (it links rust-lang/rust#91095, an open issue, mentioned here for orientation and not relied on); the package does not say which semantics Rust has. `InvalidRead.passThrough` is a modeling boundary of this package, not a candidate semantics taken from Rust documentation.
- The toy switch has no memory, aliasing model, partial moves or uninitialized bytes, and no MIR context (no statements between the discriminant read and the switch, no `Assume`, no cleanup blocks); tags equal variant indices (no custom discriminant values and no tagless single-variant layouts); explicit arms may repeat a value (the first one is selected); the pass's own applicability conditions are not modeled. The toy therefore does not engage with the considerations that bear on deciding the validity requirement of the discriminant read.
- Restricted to valid tags; with invalid tags included the condition also involves the invalid-tag semantics (R6-all).
- Escape hatch: the left side quantifies over all enums and switches; a fixed switch can be refined under the permissive read (`usePayloadSwitch_permissive_specializeEnum_refines`).
- Degenerate edge: for the empty enum `[]` no tag is valid, so the valid-tag guard `t < E.length` makes the left side hold trivially for that enum (`readUB_emptyEnum` shows that every tag of `[]` takes the invalid-tag branch).

#### Non-claims: R5-permissive (characterization, T1)

- These are statements about the toy switch model; they neither establish nor refute the corresponding claims about Rust's operational semantics, MIR `Rvalue::Discriminant` and `SwitchInt`, or rustc's unreachable-enum-branching pass. Model–system relation: none proved.
- The two uninhabited-variant read semantics (`UninhabitedRead.rejectUninhabited`, `UninhabitedRead.permissive`) are both kept open, following the documentation of `Rvalue::Discriminant`, which says that the validity requirements of that read are undecided (it links rust-lang/rust#91095, an open issue, mentioned here for orientation and not relied on); the package does not say which semantics Rust has. `InvalidRead.passThrough` is a modeling boundary of this package, not a candidate semantics taken from Rust documentation.
- The toy switch has no memory, aliasing model, partial moves or uninitialized bytes, and no MIR context (no statements between the discriminant read and the switch, no `Assume`, no cleanup blocks); tags equal variant indices (no custom discriminant values and no tagless single-variant layouts); explicit arms may repeat a value (the first one is selected); the pass's own applicability conditions are not modeled. The toy therefore does not engage with the considerations that bear on deciding the validity requirement of the discriminant read.
- On an all-inhabited enum, shape 1 (`pruneArms`) changes no explicit arm on a valid tag, while shape 2 (`lastVariantTakesWildcard`) can still change the switch (`lastVariantTakesWildcard_orderingSwitch`; `refuted_allInhabited_specializeEnum_changes_nothing` refutes the stronger reading that `specializeEnum` changes nothing on an all-inhabited enum); the card says that the result preserves outcomes on valid tags, and says nothing about invalid tags (with `inv = passThrough`, R6-all shows refinement can fail on invalid tags).
- Escape hatch: on an enum with an uninhabited variant, a fixed switch can be refined under the permissive read (`usePayloadSwitch_permissive_specializeEnum_refines`).

#### Non-claims: R5-cx (counterexample, T1)

- These are statements about the toy switch model; they neither establish nor refute the corresponding claims about Rust's operational semantics, MIR `Rvalue::Discriminant` and `SwitchInt`, or rustc's unreachable-enum-branching pass. Model–system relation: none proved.
- The two uninhabited-variant read semantics (`UninhabitedRead.rejectUninhabited`, `UninhabitedRead.permissive`) are both kept open, following the documentation of `Rvalue::Discriminant`, which says that the validity requirements of that read are undecided (it links rust-lang/rust#91095, an open issue, mentioned here for orientation and not relied on); the package does not say which semantics Rust has. `InvalidRead.passThrough` is a modeling boundary of this package, not a candidate semantics taken from Rust documentation.
- The toy switch has no memory, aliasing model, partial moves or uninitialized bytes, and no MIR context (no statements between the discriminant read and the switch, no `Assume`, no cleanup blocks); tags equal variant indices (no custom discriminant values and no tagless single-variant layouts); explicit arms may repeat a value (the first one is selected); the pass's own applicability conditions are not modeled. The toy therefore does not engage with the considerations that bear on deciding the validity requirement of the discriminant read.
- How a value whose stored tag decodes to an uninhabited variant arises in a Rust program is not examined; the toy takes the stored tag as given. The toy niche decoder uses guarded truncated subtraction and no wrapping, unlike the documented wrapping formula, and with an empty niche range (`nicheHi < nicheLo`) every stored value decodes to the untagged variant (`decode_of_nicheHi_lt_nicheLo`).

#### Non-claims: R6-all (characterization, T1)

- These are statements about the toy switch model; they neither establish nor refute the corresponding claims about Rust's operational semantics, MIR `Rvalue::Discriminant` and `SwitchInt`, or rustc's unreachable-enum-branching pass. Model–system relation: none proved.
- The two uninhabited-variant read semantics (`UninhabitedRead.rejectUninhabited`, `UninhabitedRead.permissive`) are both kept open, following the documentation of `Rvalue::Discriminant`, which says that the validity requirements of that read are undecided (it links rust-lang/rust#91095, an open issue, mentioned here for orientation and not relied on); the package does not say which semantics Rust has. `InvalidRead.passThrough` is a modeling boundary of this package, not a candidate semantics taken from Rust documentation.
- The toy switch has no memory, aliasing model, partial moves or uninitialized bytes, and no MIR context (no statements between the discriminant read and the switch, no `Assume`, no cleanup blocks); tags equal variant indices (no custom discriminant values and no tagless single-variant layouts); explicit arms may repeat a value (the first one is selected); the pass's own applicability conditions are not modeled. The toy therefore does not engage with the considerations that bear on deciding the validity requirement of the discriminant read.
- Escape hatch: the left side quantifies over all enums and switches; a fixed switch can be refined under weaker read semantics (`usePayloadSwitch_permissive_specializeEnum_refines`).
- Degenerate edge: for the empty enum `[]` every tag takes the invalid-tag branch of `readUB` (`readUB_emptyEnum`), so on that enum the uninhabited-tag choice is irrelevant.

### Escape hatches

Which hypotheses, if dropped or weakened, defeat a negative result or a characterization of this package. Each item is copied from the non-claims of the card named.

* R2: Escape hatches for the incomparability: comparability holds on the class of R1 (`trace_accepts_beh_eq_of_noTailEscapingTemps_of_noIfLetEscapingTemps`); action lists agree up to permutation for every program (R1-perm); traces agree when every flipped pair commutes (R4-if), although verdicts of `accepts` may still differ (`refCellTailProg_flipped_commute_and_trace_eq_and_accepts_ne`).
* R4-not-necessary: Escape hatch: the counterexample relies on distinct drop actions emitting the same event labels; it does not refute necessity of per-action commutation under an additional hypothesis that distinct actions emit pairwise disjoint event alphabets (not proved here).
* R5-iff: Escape hatch: the left side quantifies over all switches, including switches whose arms ignore the payload (`goto`). A fixed switch can be refined although the condition fails: `usePayloadSwitch_permissive_specializeEnum_refines` shows a switch on `deadNicheEnum` whose arm for the uninhabited tag uses the payload and whose specialization refines it on every tag under `permissiveRejectInvalid`.
* R5-iff-shapes: Escape hatch: as in R5-iff, a fixed switch whose arm for an uninhabited tag uses the payload can be refined although the condition fails (`usePayloadSwitch_permissive_specializeEnum_refines`).
* R5-valid: Escape hatch: the left side quantifies over all enums and switches; a fixed switch can be refined under the permissive read (`usePayloadSwitch_permissive_specializeEnum_refines`).
* R5-permissive: Escape hatch: on an enum with an uninhabited variant, a fixed switch can be refined under the permissive read (`usePayloadSwitch_permissive_specializeEnum_refines`).
* R6-all: Escape hatch: the left side quantifies over all enums and switches; a fixed switch can be refined under weaker read semantics (`usePayloadSwitch_permissive_specializeEnum_refines`).

### Hypotheses whose tightness is `unknown`

None. Every hypothesis in the ledgers is `tight`, with a proved counterexample theorem in the stated witness class.

### Dropped or disproved statements

None. Every main statement of the cards is proved as stated. The theorems in the next subsection are proved refutations of stronger readings of the results, not disproved statements of this package; one of them (`refuted_match_outside_blockTail_same_drop_point`) is itself a main statement of R1-match-tail.

### Refuted stronger readings

Each theorem below refutes, in the toy model, a stronger reading that a card's results might suggest. `refuted_match_outside_blockTail_same_drop_point` is one of the main statements of R1-match-tail: it is listed in that card's `lean` field, quoted in its statement block and listed under **Evidence**, *Main results*. The other four are auxiliary theorems: each supports the non-vacuity witness or a non-claim of the card named in its heading. All five are statements about the toy model; they neither establish nor refute the corresponding claims about Rust or rustc.

#### `refuted_stmtTempsProg_three_temp_drops` (auxiliary; cited in R1)

Refuted reading: under the 2021 rules, `stmtTempsProg` executes three temporary drops. It executes exactly two (`stmtTempsProg_noTailEscapingTemps_noIfLetEscapingTemps`); the third syntactic temporary sits in the `if let` branch that does not run.

```lean
-- lean/ToyDropScope/DropResults.lean:826-827
theorem refuted_stmtTempsProg_three_temp_drops :
    (dropTemps (run Edition.e2021.rules stmtTempsProg)).length ≠ 3 := by decide
```

#### `refuted_match_outside_blockTail_same_drop_point` (main statement of R1-match-tail)

Refuted reading: a `match` scrutinee temporary has the same drop point in both editions whenever the `match` is outside block tail positions. In `matchInIfLetScrutProg` the `match` sits in an `if let` scrutinee with no block, satisfies `NoTailEscapingTemps`, and the `if let` rule moves its scrutinee temporary.

```lean
-- lean/ToyDropScope/DropResults.lean:811-814
theorem refuted_match_outside_blockTail_same_drop_point :
    NoTailEscapingTemps matchInIfLetScrutProg ∧ ¬ NoIfLetEscapingTemps matchInIfLetScrutProg ∧
    trace Edition.e2021.rules matchInIfLetScrutProg = [.out 1, .dtor 0] ∧
    trace Edition.e2024.rules matchInIfLetScrutProg = [.dtor 0, .out 1] := by decide
```

#### `refuted_emptyTailDtors_give_run_eq` (auxiliary; cited in R3-migration)

Refuted reading: tail temporaries whose destructors emit no events make the hypothesis `NoTailEscapingTemps` of R3-migration unnecessary. For `silentTailProg` the traces agree but the action lists differ, and for `silentRefCellTailProg` the traces agree but the verdicts of `accepts` differ.

```lean
-- lean/ToyDropScope/DropResults.lean:954-962
theorem refuted_emptyTailDtors_give_run_eq :
    ¬ NoTailEscapingTemps silentTailProg ∧
    trace Edition.e2024.rules (toMatch silentTailProg) = trace Edition.e2021.rules silentTailProg ∧
    run Edition.e2024.rules (toMatch silentTailProg) ≠ run Edition.e2021.rules silentTailProg ∧
    ¬ NoTailEscapingTemps silentRefCellTailProg ∧
    trace Edition.e2024.rules (toMatch silentRefCellTailProg) =
      trace Edition.e2021.rules silentRefCellTailProg ∧
    accepts Edition.e2024.rules (toMatch silentRefCellTailProg) = true ∧
    accepts Edition.e2021.rules silentRefCellTailProg = false := by decide
```

#### `refuted_specializeSwitch_retargets_every_nonAllowed_tag` (auxiliary; cited in R5-eq)

Refuted reading: `specializeSwitch` retargets every non-allowed tag to `unreachable`. When two or more allowed tags lack an explicit arm, `lastVariantTakesWildcard` leaves the wildcard unchanged, and the non-allowed tag 1 of `deadNicheEnum` keeps the wildcard target `goto 7`.

```lean
-- lean/ToyDropScope/SwitchResults.lean:300-302
theorem refuted_specializeSwitch_retargets_every_nonAllowed_tag :
    allowedTag 3 deadNicheEnum.inhabitedTag 1 = false ∧
    (specializeSwitch 3 deadNicheEnum.inhabitedTag ⟨[], .goto 7⟩).target 1 = .goto 7 := by decide
```

#### `refuted_allInhabited_specializeEnum_changes_nothing` (auxiliary; cited in R5-permissive)

Refuted reading: on an enum all of whose variants are inhabited, `specializeEnum` changes nothing. On `[true, true, true]` it changes `orderingSwitch` (shape 2, `lastVariantTakesWildcard`, gives the remaining tag the wildcard target and makes the wildcard `unreachable`).

```lean
-- lean/ToyDropScope/SwitchResults.lean:307-308
theorem refuted_allInhabited_specializeEnum_changes_nothing :
    specializeEnum [true, true, true] orderingSwitch ≠ orderingSwitch := by decide
```

## Evidence

Basis for every theorem below: execution (Lean kernel check). Toolchain `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`); no Mathlib; `lake build` of `lean/` succeeds with no `sorry`. The axiom audit (`Lean.collectAxioms`, recorded in `audit/axioms.json`) covers all 705 non-internal declarations of the library (including generated auxiliary declarations); 0 of them depend on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. The statement hash is the SHA-256 of the Lean `repr` of the declaration's type; the closure hash is the SHA-256 of the sorted `name : type := value` texts of every package-local constant reachable from the statement (theorem bodies excluded), as recorded in `audit/statements.json` (223 names) and recomputed by `support/revalidate.py`.

### Main results (card `lean` fields)

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.DropScope.run_e2021_eq_run_e2024_of_noTailEscapingTemps_of_noIfLetEscapingTemps` | `propext` | `4a09d2ba4ea2846b764582ab3f532683018034ea94b7d87b7ad998acb651dbb0` | `4dc82d92d808d75a2d241babb6733e6dd5c5a8c89928a6eea55cd4b69e0177b6` |
| `Toy.DropScope.trace_accepts_beh_eq_of_noTailEscapingTemps_of_noIfLetEscapingTemps` | `propext` | `76a148b7cb365089008acdb6990ec2ed0edc603af6b54fa69ec9bec00a0e718a` | `f5dcc2141fd4496f10eba93770ddc09b5959b6ae9d6e98f3c8fb262ab6c9efd0` |
| `Toy.DropScope.run_tail2024_eq_of_noTailEscapingTemps` | `propext` | `1a9767ea27d2cd4545704c973fc149c4a004d8667dc624c405a1b34f0573a654` | `e7d6bb9dd4d3636d00ec7dce8dc7b2b375e9124e7e74be41594c5181270e5e1b` |
| `Toy.DropScope.run_ifLet2024_eq_of_noIfLetEscapingTemps` | `propext` | `fb39d48c3d011038e5cd67879c8b3ceb08e4119c245323046c4a9cb797fffa8b` | `89eece4c2ce7a8cdb2a34470054d3aec5508c2a3d2c99366e0f8e9d47ecc87cb` |
| `Toy.DropScope.run_perm_nodup_and_dropTemps_perm_mkTemps_and_nonDropTemps_eq` | `Classical.choice`, `Quot.sound`, `propext` | `7876a321f2ab27d0c6584f7e417dc8e08c06fe286636ca1e30871c43cc7bff26` | `44537a6354db9cbd0d31361f2f99e5937e9028e588fbdbae6573337303d1e9d5` |
| `Toy.DropScope.run_each_created_temp_dropped_exactly_once` | `Classical.choice`, `Quot.sound`, `propext` | `d7056195b13119c10cd2e4e1e2af8c43818fa928b5d3c4d6e1388ccbb786f5a1` | `11dc0f976f64deafb1b4612e8b9f2cf7aa750a97bafe6860f8180509ff015593` |
| `Toy.DropScope.matchInTailProg_scrutinee_drop_moves_by_tail_rule` | none | `dd2809c618947371dd8b20ad4e315a0972218e87ea427da711c97b7e34fe120f` | `3920e345cf2098b97c0558be2a8dc7cca806b49e120fb753a355eacafbc1f285` |
| `Toy.DropScope.eval_matchE_eq_matchStep` | `propext` | `ae6c3fced4d7399cdb7ca8b7dadbe1fff02f00bbb0410ad5a39f6a35626d87b6` | `ff3c5b09864d3e53ccc2528e81414777154f233b9768dc8b3de25d8b21e93b07` |
| `Toy.DropScope.refuted_match_outside_blockTail_same_drop_point` | none | `5e557fdd9bd2057a634fb0e851405f8c4c01593e0320e2a04ee930fc1a559cb2` | `9839e6f1805c3da1dab56e645e69b0a4da3bf6a17f768481801f41c54921bb0b` |
| `Toy.DropScope.tailProg_accepted_and_traces_reversed` | none | `277524abcc54d595d947ab923b9f18aaab64c0a5af4f84fcbec72f9ff267c809` | `d4da734acdc9f087c18ed2920b362698dd59a4d2202ee5d1394f94ffed7a0fc2` |
| `Toy.DropScope.not_behIncl_e2021_e2024_and_not_behIncl_e2024_e2021` | none | `a2f667e04397ac1ab6db368c04e59f67862e098e95addb6f24f90c20ba52f1be` | `aca05e72218acd85c84785a06d8becac62addd1c52ca7d53eedbe8fb1b65f8e2` |
| `Toy.DropScope.refCellTailProg_accepted_e2024_rejected_e2021` | none | `61169ea68b7f689c7676ec073bea6501c048bca45037b94bc9223ae25100bcfb` | `d22a48c3faeb6d18890446b3773b14cfc7a99735dc7f0e4804ae5b9099eb2994` |
| `Toy.DropScope.run_toMatch_eq_run_ifLet2021` | `propext` | `cc4308fc4e3a1810506ca3dc72f0d8e5bb1df86d2d3ccf2eef74926f2cbfd563` | `42daf1860b9952567128729e29891acd3f2d682ab373336fee04142fa1a679c7` |
| `Toy.DropScope.ifLetElseProg_traces_differ` | none | `7679dd7ab2b715243ae56082f7f521f376570e5d37c8441db43976f8c51ae7f1` | `332d0e609c20372f966e86d1921db1bdfb241a5c83b19b16c35c9f21a0af2290` |
| `Toy.DropScope.run_e2024_toMatch_eq_run_e2021_of_noTailEscapingTemps` | `propext` | `6821a8ecb2862c1c5ebf7fe9281cda800ba0a14b0cbddc9fb0a0d78c28354919` | `ee9a60a853ab97f59b4fea535b9d5faa230e396f3847b6deb71e0cab78474b41` |
| `Toy.DropScope.trace_e2021_eq_trace_e2024_of_flipped_commute` | `Classical.choice`, `Quot.sound`, `propext` | `3faabe4036746788a29912abb85824be85e1a7170fa2c9e37280748d506ddd79` | `261d62577494033415c3f46de32b162d02d42ced2b9d7d68e67fd002e2063806` |
| `Toy.DropScope.tailSiteProg_trace_eq_iff_commute` | `propext` | `a792ab873e379774dc00168a3cb9c5b83263da4ccf5460da9921f95d3bd114d5` | `bca0f63cbc5689f43494d484caec1321cde8da7933bef46fcf755301a6bd9729` |
| `Toy.DropScope.elseSiteProg_trace_eq_iff_commute` | `propext` | `8e8e2eed6c2dfcf45aacf280bf42b173af25e65377671ace82811d36673c7a1b` | `0685c1506b3951bba3eebf6b05d1be6e0dd1a4b877f4d4f0f0653477cf54c0da` |
| `Toy.DropScope.elseSite_commute_iff_of_dtorOnly` | `propext` | `e2668f867802c78dc1d7f194509f48ec8c9dfeeb5babebba3869768337a43163` | `b714b2bdf71d3f6f981423edbfee3389ed80e6723f7b2cb16ce6a6834395847b` |
| `Toy.DropScope.ababProg_trace_eq_and_flipped_not_commute` | `propext` | `67dbba22aab89c3be3ae8e8bc19eafd290fc640a9d6554a077bd26fdbd9b203a` | `1048ce661f8d5228e1276629e02569b41db3bae81c6618122d96e7cbc34d3274` |
| `Toy.DropScope.nestedTailProg_traces_differ` | none | `b1037e5cecfd488b9a0c2d0dbaac2923ac280701cdf8ee4eda317b17f8905a64` | `c40bc886d4ec24652d47b32e7a7275c29834e76cfe67cac84f82f6bcb6fcb7de` |
| `Toy.DropScope.thenBranchProg_traces_differ` | none | `609ac53056abe7e9956e1a92461f7c8515e590b62bce6ecbe182bece1e94f51b` | `0fa6efecc1f99d496501a97c9910667559dc17f4aa35a7b84c512bffbd849fa3` |
| `Toy.DropScope.siblingTailProg_traces_differ` | none | `4cbf56263db46f83277e15e772b34e3609f4265c70f96e3e246ba85b2b7d4947` | `4b2b8408f26a0d6b596f97786019ef1ca330c5e4a95aa045874070bd94bc057a` |
| `Toy.DropScope.exec_specializeSwitch_eq_of_readUB_of_not_allowedTag` | `Classical.choice`, `Quot.sound`, `propext` | `d93810f344b6995135a25ff1014bbf327a6ce270396338afb1731befc9b30d15` | `74b49e4f255bc70791ffd8d2bf8154c9d6e3964a89b3bcf69a0621a21dd517ac` |
| `Toy.DropScope.runSwitch_specializeEnum_eq_of_rejectBoth` | `Classical.choice`, `Quot.sound`, `propext` | `de3a315f3998886f35eb00ddabdb24a9d886da5c473bb2d7d4b33a57139e7291` | `ad277249f8cde13611342988b18e50d114b99fdfca9e895f43f7ea422c3a6631` |
| `Toy.DropScope.specializeSwitch_refines_all_iff` | `Classical.choice`, `Quot.sound`, `propext` | `4b6aa9cae0dd3177ac2f64d78ca2a35cc7ebf38052b61de3e1cbb8783b3213ff` | `dd56c836cadcbde48db592e65d15eae649ee3b61aeb9696d773c1b8b88a87edc` |
| `Toy.DropScope.pruneArms_refines_all_iff` | `Classical.choice`, `Quot.sound`, `propext` | `2e4b769d60f221c8ead70eec98f0eb7c23ef436693f80820e57f94fa49c8a3cd` | `fef298f279f493e4a4f357ad1bb9bd09ba981b41574ac997a9a1266fe8f728ac` |
| `Toy.DropScope.lastVariantTakesWildcard_refines_all_iff` | `Classical.choice`, `Quot.sound`, `propext` | `aea7f7d6293b53da478f1782711c228e8874487bf773850ade34c86f90bb251a` | `3e52de08e94d1c86231a9e16e5b0abb364deeaf3b53ed31b806ffd9c2fc3985c` |
| `Toy.DropScope.specializeEnum_refines_validTags_iff_rejectUninhabited` | `Classical.choice`, `Quot.sound`, `propext` | `7cac849881df2be7dbf12c691b94b26b80b1cdabbf6a77d795aa1a602d271191` | `99ac9c2859373954b276f91587c25785c35d78c4d975f234f0a1abf84787cef0` |
| `Toy.DropScope.specializeEnum_refines_validTags_permissive_iff_allInhabited` | `Classical.choice`, `Quot.sound`, `propext` | `18364d79efcaf5a655b4e4e88d292db7d4b168233c043b24fca41bb2bf58fa53` | `99ac9c2859373954b276f91587c25785c35d78c4d975f234f0a1abf84787cef0` |
| `Toy.DropScope.deadNiche_permissive_specializeEnum_introduces_ub` | `propext` | `5f697e1ceb2a6dfd732b0489e241e9e1e4b74244e4319b05622f51e5bcc3f236` | `25b1fa91fd282f77cb5bdcbee2fbd0747fcf05652e3ec4f6e0d803d635ad6f3d` |
| `Toy.DropScope.lastVariant_permissive_introduces_ub` | `propext` | `c3d8855fb79cd5714ff2fb4bb810ef75f4c9b69cbc3493a4e66731e71c6ba05c` | `a399dbb5b99ea8b518a6e897f0d2df9490072bcb3d91c80ecee73af25a14820a` |
| `Toy.DropScope.specializeEnum_refines_allTags_iff_rejectUninhabited_and_rejectInvalid` | `Classical.choice`, `Quot.sound`, `propext` | `182046d4a29b79fd309a39cbdfb6858bcc7dce39fc84073cc8ee01138165cd3d` | `99ac9c2859373954b276f91587c25785c35d78c4d975f234f0a1abf84787cef0` |
| `Toy.DropScope.invalidTag_passThrough_specializeEnum_introduces_ub` | `propext` | `7c388c599fb6a88ad8e23a898bd030c029cb4cd235e152633a32a4ea7b42cf65` | `3eb462c2d0f09c7e606f32ac05ad50d1ea62e6a5d0bf837b2780f50b49c51077` |

### Non-vacuity witnesses, positive controls and tightness counterexamples

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.DropScope.stmtTempsProg_noTailEscapingTemps_noIfLetEscapingTemps` | `propext` | `cd401ec301164079ec6a3000d54921744822f1e1e100ac9d511d0aa4f38e8ff1` | `ff13df8ada16f611c2086c8399ed77882f8c08692a96701566eb2ed0e3f189fa` |
| `Toy.DropScope.tailProg_noIfLetEscapingTemps_and_run_ne` | none | `bcc13cf02bd175788d05f8337005030c9660f5d62645370bc3948dcedf157f77` | `6c277e4e2a02219bd8e9cbb7197b85ef59e9117e962656013dc0af663c1c72d7` |
| `Toy.DropScope.ifLetElseProg_noTailEscapingTemps_and_run_ne` | none | `8a4167fcd175cb2ae8bc3c69bb18b1fc0f3c47b31ccbdab6b09b2ff901d87d81` | `121b5740cc6e270eceec187af6de8a0eea12710479675c3eab79d0c7d65912f1` |
| `Toy.DropScope.ifLetElseProg_noTailEscapingTemps_and_traces_differ` | none | `b147e9f5dd233e3a2f7fc27358039f6b9859321872314e0e933d057ff2a47b56` | `9bf4c4e9d4917469e8fdcd6cb38470c2cd6ff7c53a22316d82915e99ab0c3378` |
| `Toy.DropScope.ifLetInTailProg_tail_rule_changes_run` | none | `30ece394bb100980e22776db71c19ef71241d88e33dcd0f47293eb3e95aa65d5` | `79199ff7c2b9a0d10d0d1771f7171237f6a9a90345217e8a587717aa297c1368` |
| `Toy.DropScope.ifLetElseProg_not_noIfLetEscapingTemps_and_ifLet_rule_changes_run` | none | `ed2d5063fbb5abb0cb336722f302d50004be9ce9fda2c09726c6ff060340dfe4` | `5a7796eee93259fee529ec5b3078236e31518827ba7b403cd09dd15be0295878` |
| `Toy.DropScope.run_tailProg` | none | `291a4b4265f0b80d347008c1646f24129cb917ebacb336d299538794645de1e3` | `42c32b62321ec7409daec896e390aeb51db6f61ed5c1ce0aabf00b1928753069` |
| `Toy.DropScope.mkTemps_dropTemps_tailProg` | `propext` | `eba7b9ac321aceb9ea85bc43ab682ba31b4e501efeeadcd510d4177995a78bfe` | `47d2d52d349dc7a44113673ed69fa0337685e7e1aff0ac2f5fa3b9e9094e71f4` |
| `Toy.DropScope.behIncl_refl` | none | `2beff570fec82a2c7287e7ee00ca1fddfad584991a603641713473b3555cf00d` | `0dcd802632c452d3cc4b1f49da01e6df46e19a39955b94b05c8aad3115706572` |
| `Toy.DropScope.toMatch_ifLetElseProg_ne` | `propext` | `a632d28196683bdd93368482d287d923d7a8e1b56679647aae3386b0a4f84623` | `a2be4f8db2aeb4adfd04d7561b77108ffc6bed602d226383b11c8b1e9ff443cd` |
| `Toy.DropScope.ifLetInTailProg_toMatch_e2024_ne_e2021` | none | `65a599b12f8a82c295348f72661e541ab7953e9217d332ec53d819d04e006d72` | `0fc13d053f5dd52babc4998c465a85611e24ca78cfcc733cf88a09f055083109` |
| `Toy.DropScope.commutingTailProg_flipped_and_all_commute` | `propext` | `569b5da1195cef6b98f83732a43a5bf17671e6b3ecba107aab77b64bddbcbf66` | `b2b0ad0da8d3543e8785b666dd16b4c3459551dbacda4a7f055ca74b1e93dd71` |
| `Toy.DropScope.tailProg_flipped_not_commute_and_traces_differ` | `propext` | `4188c6b66da8b460501277c3c59064a00c0f71733c38b4e41296037173047ee6` | `91e609bae1f753792581a6e77f20467c0c96981f2230db936aa89dc19d43e2f7` |
| `Toy.DropScope.site_examples` | none | `394ce81825a20c563b0a2bbfcc8d21a8ef4ab66d948b34cc9061bda28653fade` | `d644e2a1b00a46b3f244917f390bcb0fdd536d23ee3d563ac4969eefb3d0f287` |
| `Toy.DropScope.elseSite_dtorOnly_hypothesis_holds` | `propext` | `471c051ed46e40ffcc83885fd707e320d46ab58028f8b54708ac37b662e59266` | `b714b2bdf71d3f6f981423edbfee3389ed80e6723f7b2cb16ce6a6834395847b` |
| `Toy.DropScope.elseSite_commute_iff_of_dtorOnly_hypothesis_tight` | `propext` | `360bafb9b82c9253362b8e16a111da51eaf54a668fcaef6b76fdf31529a494f2` | `b714b2bdf71d3f6f981423edbfee3389ed80e6723f7b2cb16ce6a6834395847b` |
| `Toy.DropScope.deadNicheEnum_rejectBoth_satisfies_hypothesis` | `propext` | `e8ca9d619249d964aabe897548eef20fe8b2796dfca66ab5ec2ae53072e1c669` | `a6c8b0a55eaf8450b217f53c07992ddb128d73b5d7140dbec571c9401ad97e31` |
| `Toy.DropScope.rejectBoth_deadNicheSwitch_same` | `propext` | `7d951e5674e01aae47bdb62ad5db9a130af10e8e9629c8b92e7c321010c1c1f8` | `7e9b811bed15bca377ace8ce5f607ee6150063a15c688bfca01f70aeb964d650` |
| `Toy.DropScope.specializeSwitch_eq_hypothesis_tight` | `propext` | `8e2b56570b68c3d619d316cda4f794a8f591b86624af701e35d37efb908a145c` | `44c4b9e5ddb52e1265f37643622619cf26bbfae9c2359c4c94df72ec6596cf4d` |
| `Toy.DropScope.specializeSwitch_deadNicheSwitch_permissive_not_refines` | `propext` | `b5882038d5369310c910ba5c7c7522c2e5d446f9cf22d07c2dc8e2d5c3cb8f45` | `f0c29d75e505a44c5da04a6f403a0afdcae8ef45648a25763eae90ec510d8ef5` |
| `Toy.DropScope.pruneArms_explicitUninhabitedArm_permissive_not_refines` | `propext` | `c3a0b0ea0ed14799bdc18ef888db0dc1574fd462babc616c1f5f3754eb3bdf01` | `8a42b40a5301390d546f1dca09d9512944db41e2f3db682d5f7a9c386df3e850` |
| `Toy.DropScope.lastVariantTakesWildcard_permissive_not_refines_both_branches` | `propext` | `f9235cc48f991bc63286394c2204d8326f35ad70774aa794dce0c70ace30b0ab` | `d5a9655d87be220a1d46be01e819bad8b643c1f3992b4923c1e4c3f4dac13988` |
| `Toy.DropScope.permissive_allInhabited_orderingSwitch_same` | `propext` | `ea33e91507b404ca9760cf178a4384d109991b56cd0a4a9564aa9951c71ac79f` | `ebd3847cbde9d8adb7c4035b4b7ea8d1162da4c0cb1daa7f07eee3edf3c17dcc` |

### Definitions and auxiliary declarations cited by name (`lean_names`)

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.DropScope.Act` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Act.dropTempKey?` | `propext` | `769a3d5bd47c726a04abbdac6aed10c3e690fc2c84032245d3112458ea198cea` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.Act.events` | none | `73bc380ebd1312fb633f6b16ed2bd2c25d2bd71d156640aa3105ef32194d07ee` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.Act.isDropTemp` | `propext` | `7ab3643ce63e2b659ea8b00eb7af995ae228d9b111dfc48a553cd255b38b7900` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.Act.mkTempKey?` | `propext` | `769a3d5bd47c726a04abbdac6aed10c3e690fc2c84032245d3112458ea198cea` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.Arm` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Before` | `propext` | `7336ec2afeaa4eae894041616d4a97b33374329da86d400723f5910aa7d72fd7` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.BehIncl` | none | `86524037e69acd3da8d7311a823018f21446573187fa54defe048d438e92fb46` | `03f67e7b69468f3158193eaac99ffc7da69ed0caaff2fcfa59f5ddc49cae8d2b` |
| `Toy.DropScope.Block` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Commute` | none | `b7d1553dd6efbaec0790ff36f16163197dbb5e14be092bd0a8a871da88c98b0e` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.DiscrSem` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Edition` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Edition.rules` | none | `881e3767980b1288e9d79b6cc72dc2c7fff9c7d851abf662a284deec7afd1967` | `ee512b53482e4b3ede12db6c3a76308dff84dbfbd021c1b49d3e03f88fdeac95` |
| `Toy.DropScope.Enum` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Enum.inhabitedTag` | `propext` | `6ac0a3287eba1ff6a6f083afc4a50021b6ef9b63f26daeb7e472e26b347f0206` | `80f54cdae27e2eefa6def8685a9004706ab45e657f5554f789f83748e4bc764b` |
| `Toy.DropScope.Ev` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Expr` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Flipped` | `propext` | `41d3e9f190152afa50e228050b0277c60bcae985341fc961dcb5245b65f8973b` | `f2bfe4e9f8b314497c44f833ee7d05c41490dc06a9c93615d94706b55d29e039` |
| `Toy.DropScope.InvalidRead` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.NicheEnc` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.NicheEnc.decode` | none | `1282d303752ba212e97adf1a4ad6bacbc44e7d7526632f397fc3980d827a17a2` | `1f256337f2e5f5078e5be4185ec928922c7777ade76e4cfdf7864e6ff2d8cbbc` |
| `Toy.DropScope.NoIfLetEscapingTemps` | none | `68be500851b73ada7c5cd33ffe6e936e304c8593deb23fa44febd84e1bb19105` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.NoTailEscapingTemps` | none | `68be500851b73ada7c5cd33ffe6e936e304c8593deb23fa44febd84e1bb19105` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.Outcome` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Pending` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Refines` | none | `7b5444e4be0d8fff38244368f2bc9f863ee15c67de1a5d990548c32732908606` | `9338a94712075fa9aaa8d1e5dfe52ba4e6bf07b12ae34432c925e77b19387159` |
| `Toy.DropScope.Rules` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Switch` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.Switch.target` | none | `5493a3b2185f0fbceb29ebfa6391a3e6d1ab86fb8c851a7bd4d2a339ac270d06` | `e878d1802b8f28c19cbeff4794e2045760efee4237c7dab0e392a6bc23bfe15e` |
| `Toy.DropScope.Tag` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.UninhabitedRead` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.ababLocalDrop` | none | `1b17576a7a090b23ff6637d2d7ce0e1d46327c737d50b263f4a289143da5a68a` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.ababProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.ababTempDrop` | none | `1b17576a7a090b23ff6637d2d7ce0e1d46327c737d50b263f4a289143da5a68a` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.accepts` | none | `d684dee4fd1f2e97fd5b498cdc0211cfadd9220f2311469af1aa1ffec83ea10d` | `e4b234bfa6471d9f7822a65b870cce6eedf0884a109df8b0107e42d92e9788cb` |
| `Toy.DropScope.accepts_refCellTailProg_e2021` | none | `3c0cf2e7480a897beeab03782e9f4fe99372d5a3842dd955070dd4270dd16807` | `d22a48c3faeb6d18890446b3773b14cfc7a99735dc7f0e4804ae5b9099eb2994` |
| `Toy.DropScope.accepts_refCellTailProg_e2024` | none | `ab77660e0de93e1ace7791822ed4412523e52342ae977450fb3ebd660a61bf52` | `d22a48c3faeb6d18890446b3773b14cfc7a99735dc7f0e4804ae5b9099eb2994` |
| `Toy.DropScope.accepts_unboundBorrow` | none | `3cba9d04e2a15651fa57ba65ffaf080844245780e85fbb188d96671b7cc8733a` | `54e6d8bf461c49630caa1b3ea2f018186140ba0a63a404ff8be952e54a434257` |
| `Toy.DropScope.allowedTag` | none | `c4bbe7842496e181cb29f4b6bc745e629593fbd863f84fd0a64728b9a8040d9a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.DropScope.allowedTag_neg` | none | `b59d3cd6e9d30cf57e8aec355d5e1c74712d360cf79d1f54a530857eecaa6e21` | `f025c4683de6273c3a59ec0b27ecb11eaf7b992688da0865784d31a7b90f07c6` |
| `Toy.DropScope.allowedTag_pos` | none | `2c48452df01b3c8a7793ec1546b8f6d870eaa3a40b5b87412bc3683002d7c6fa` | `f025c4683de6273c3a59ec0b27ecb11eaf7b992688da0865784d31a7b90f07c6` |
| `Toy.DropScope.bareIfLetThenProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.beh` | none | `e7eb942899435a30ffe33b94061c6c343f08e9f4119b17cfb9823131e6c9c70f` | `e4b234bfa6471d9f7822a65b870cce6eedf0884a109df8b0107e42d92e9788cb` |
| `Toy.DropScope.borrowOK` | none | `5564a373a3f7054585d7b1bda7cb8b03990f6904285dca7676ee4340453be06f` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.borrowOK_shadowing_limitation` | none | `6e2794d0a9ce4496bcfade68891e0ce608ad2d6ad1da2c797b877e5d3d17778f` | `df503f13b14d384931be9bea447f40909064115a1543e4dfde7063c9c83e5a3d` |
| `Toy.DropScope.closeScope` | none | `132b11bb0a6bf08b417b9dae995d06bbac814bf8198c57a7d680b8ea9aae89a5` | `f35b552122fffa7f988664b39311eb663198d7a75f6c163c3f04d052f6291556` |
| `Toy.DropScope.commute_distinct_nonempty_event_lists` | none | `2289f6d49a9b9b01f7ecadc7aafd708282f5a71d4efce090d3f41dfb8f02ccce` | `286ae07467cf5e4019e779f5ca185f96275f7f19a523497990f10e70997cd1b5` |
| `Toy.DropScope.commute_same_event` | none | `a733e077fec962c9d5beb4b683fa1181bbc9ad1f5edf2612c2679e5b2cc138f5` | `286ae07467cf5e4019e779f5ca185f96275f7f19a523497990f10e70997cd1b5` |
| `Toy.DropScope.commutingTailProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.commutingTailProg_run_ne_and_trace_eq` | none | `0bc17646bd9f9978a13958047f5aa4260dd5ace2e1443867bb72ad57c9a626a4` | `065e49d862f34bec884b78ea9ba07a177a533feb35897cbb8ba217419ade00d2` |
| `Toy.DropScope.deadNicheEnum` | none | `d0453ea857454b4cbd1e119cb3c07dbb6c652a45d028413d0378d049564c1544` | `80f54cdae27e2eefa6def8685a9004706ab45e657f5554f789f83748e4bc764b` |
| `Toy.DropScope.deadNicheSwitch` | none | `8f5dea4cf189b0e9cd765c17804d6f01e773ce40e1db11475f606d32127c0983` | `e878d1802b8f28c19cbeff4794e2045760efee4237c7dab0e392a6bc23bfe15e` |
| `Toy.DropScope.decode_exampleNiche` | none | `2785701226c761802fe6afa4ab326afe0e62bc194bbd1281232253c42cb772b6` | `e484f6d82d35915c9102e9ccec35cf31bfcd8b7e7fe15163f0b48a536cb0f92d` |
| `Toy.DropScope.decode_exampleNiche_untagged` | none | `a26c46a93d37af45b0d2d23da609048e0453c6bebec2c7955d0309604fcb5f8c` | `e484f6d82d35915c9102e9ccec35cf31bfcd8b7e7fe15163f0b48a536cb0f92d` |
| `Toy.DropScope.decode_of_nicheHi_lt_nicheLo` | `Quot.sound`, `propext` | `68c94442a8f995553d5d6decc77ede70934b77095638e033f7887eab340b6530` | `234af3bb167b609e65dc3c2ae232aa6cba1c8d28f3cda1faba635b63eedbecbd` |
| `Toy.DropScope.dropAll` | none | `b9cc68f433e63d8505e070527c86fc751a01dcb2fff0e073a7cc6d3ff86a50c9` | `f35b552122fffa7f988664b39311eb663198d7a75f6c163c3f04d052f6291556` |
| `Toy.DropScope.dropOrderEvents` | none | `15602dc98b9e608c0942ff0e1f2385ae6d6044a8c065466ecee554fa778e4061` | `28c4e30600618ee205501a3e990eb2f60b1b25ad1f067a73aa3ddea445d14727` |
| `Toy.DropScope.dropTemps` | `propext` | `64d9644a6b1a2f46d1c8d12693b5bdf5594ec0632fa0015e7993a938fa600a5b` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.dropTemps_mkTemp_mkTemps_dropTemp` | `propext` | `a3e2f24964fb86b301a053ab68be5404dbbabfbbbda10445a68316b9c02a5e94` | `229c2070b68807019b5f9201cc3a304269c368e90f0f38e4f152cd1a0afaab56` |
| `Toy.DropScope.edition_rules_e2021_ne_e2024` | none | `e88827dbac601e9ca4a7b6dc7fb91048ccd239a6a367657a8c8b9f88d7ce5108` | `429671b06929f4cfa4f3d589c3406e92c101371b49e486923ca3a6794f40a5e9` |
| `Toy.DropScope.edition_rules_e2024` | none | `784d91ca1c362032ec806cc52799f5749b471c4fd3d875cd9726bc66c43bf9aa` | `429671b06929f4cfa4f3d589c3406e92c101371b49e486923ca3a6794f40a5e9` |
| `Toy.DropScope.elseSiteProg` | none | `b5e8aa2860e0b40be1627f3efeda956550e9285adbb25ec0779f0d772817c223` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.eval` | none | `2340ffffe5869bb7d5f7635a045dd02bab2c470163cbe124583968bbf39f3a5d` | `ce8a54b13b6c314ab3e62385a7697bf00a78212cd7e8ec739a5250c4d9b8f901` |
| `Toy.DropScope.evalBlock` | none | `5862e49bc61faa970963248fe8cd4f3ccdda3c522dd4b0547844fe90a4846956` | `ce8a54b13b6c314ab3e62385a7697bf00a78212cd7e8ec739a5250c4d9b8f901` |
| `Toy.DropScope.exampleNiche` | none | `c5ac6d4e692a46b33005cf4d5a7590d3734a79eb184a842ed003d87f3eb3cb25` | `1f256337f2e5f5078e5be4185ec928922c7777ade76e4cfdf7864e6ff2d8cbbc` |
| `Toy.DropScope.exec` | none | `d6914cfe697e135f19357d4e87689b1b6a3c3f3953a0b3fee2dc611ea0099d88` | `bc9426cff0f7e587a65f28590eb9891467a360a1c8e6076b47367dbf964372f3` |
| `Toy.DropScope.exec_ok` | none | `9061cdceb3866113f586afbdc809a30cfc0f20e0d3f1ec52e50bb2962cdcbb66` | `551d0d67675512446235f06cb3379bca9a3e09fc60bad1a6da8578b4e945368e` |
| `Toy.DropScope.exec_readUB` | none | `48192d459e236b8f324f4d26760cf8dcdd17a4f831afc7935713d105a1b4a1ed` | `551d0d67675512446235f06cb3379bca9a3e09fc60bad1a6da8578b4e945368e` |
| `Toy.DropScope.explicitUninhabitedArmSwitch` | none | `8f5dea4cf189b0e9cd765c17804d6f01e773ce40e1db11475f606d32127c0983` | `e878d1802b8f28c19cbeff4794e2045760efee4237c7dab0e392a6bc23bfe15e` |
| `Toy.DropScope.flipped_tailProg` | `propext` | `a93962b936e809add497174f5415d4408875a1e367dbf52414398e85f6892253` | `ffaf4cb1c489713e13e1c2a4a5233d6d4c6b81c4950f206f624294c9740a01e7` |
| `Toy.DropScope.ifLetElseProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.ifLetInTailProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.ifLetInTailProg_rules_interact` | none | `547c8e2b08ca7243172753b59d07e1e534ca695dfb49974bace9ab9607665b9f` | `c03baf55d2c0184f93e97bc9d940997bad7d0b93b20373ac1c61c996433e6522` |
| `Toy.DropScope.ifLetsClean` | none | `fb84afd68db6e584ae6508523c8c9915c51386ea85a180a7c954ec76662a3381` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.ifLetsCleanBlock` | none | `aea6b59bafa71ccf90b40bddfad6a297e6190e123e39f56ecc5a8119c8444eed` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.isDropTemp_dropTemp` | `propext` | `16fbef99b0b3e14b7c46807742d340d62008fbf3c69ce53bc129427732063a50` | `683999a4c1b74c22bbe0913f5e9c3a0f8e25cae5be37476eb0fc1019ee15a31e` |
| `Toy.DropScope.lastVariantTakesWildcard` | none | `ec87363907f5ff8ca0762679d7c84aa8c2f1fb4998fd038026b07683723cffbf` | `e878d1802b8f28c19cbeff4794e2045760efee4237c7dab0e392a6bc23bfe15e` |
| `Toy.DropScope.lastVariantTakesWildcard_no_remaining` | `propext` | `46fc77f38766e529ca21db3be8f6697600298bdced2e551bfdfc8619b4a4d052` | `1260e85d639c905783908eb4d17749658334206bcc9ba7b6e3182a70730f5476` |
| `Toy.DropScope.lastVariantTakesWildcard_orderingSwitch` | none | `7bec3aed2d5058379914f9360d88dca41c8d330da52116e4bb8d61b12c7b16d6` | `965a36bb31aee91128add9ebd5f784d73b28ebde1110eac494911e3beaa89fe0` |
| `Toy.DropScope.lastVariantTakesWildcard_two_remaining` | none | `bbabd969463eb3422440dfa02de6c69813f6470ebd1069bf4a61e3705d65d821` | `bdfdc35b9540bd8e95ccc3ca33042068c52426d7e7e61903e824fc893d6ab435` |
| `Toy.DropScope.letsFrom` | none | `8540d26ee24582ad2152bbdef96bf1f8c147223ec91e02933145f84d9ac0cae6` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.matchInIfLetScrutProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.matchInTailProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.matchStep` | none | `226eab7b94e6f61c1042d19300d545887c54d7265d43e8e897a945892290a06b` | `f35b552122fffa7f988664b39311eb663198d7a75f6c163c3f04d052f6291556` |
| `Toy.DropScope.mkTemps` | `propext` | `64d9644a6b1a2f46d1c8d12693b5bdf5594ec0632fa0015e7993a938fa600a5b` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.nestedTailProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.noEscape` | none | `fb84afd68db6e584ae6508523c8c9915c51386ea85a180a7c954ec76662a3381` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.noEscapeBlock` | none | `aea6b59bafa71ccf90b40bddfad6a297e6190e123e39f56ecc5a8119c8444eed` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.noEscape_hypotheses_not_necessary_for_run_eq` | none | `2ff688d329a5da5527d751a26e1a3dde05a56162e73433a012e8ce3cbc1e3eb4` | `05fd19c5e05f5d94a111e9359603c595ba1785ecc74ddde981d08c19950cf304` |
| `Toy.DropScope.noEscape_ifLetScrut` | none | `08ff33b31d1e24db10e8d1d6562869c2feea0e2873664d8c82a7b6e352a6b8a8` | `ea2a0a4db2724cbd3c05fdf2d6ddfbb95678f4daade149e9d4fce048f05f887f` |
| `Toy.DropScope.noEscape_letInit` | none | `e03ddde5d3d8a678fc19a045f09a2ee322aaf2e4e36975838671b75a2fa79410` | `ea2a0a4db2724cbd3c05fdf2d6ddfbb95678f4daade149e9d4fce048f05f887f` |
| `Toy.DropScope.noEscape_matchArms` | none | `2262b6377e1a889d3a50f054f93742b78fee5b2d424ec4e5182a010ffd1f4710` | `ea2a0a4db2724cbd3c05fdf2d6ddfbb95678f4daade149e9d4fce048f05f887f` |
| `Toy.DropScope.noEscape_temp` | none | `82ce0c0dca95308ae42006b3761bd639f91cb7e059f4367d813120307b00351a` | `ea2a0a4db2724cbd3c05fdf2d6ddfbb95678f4daade149e9d4fce048f05f887f` |
| `Toy.DropScope.noIfLetEscapingTemps_stmtTempsProg` | none | `d4e5bf56dfb1e004172f398b319ff9ce9614b3fc03f6b29c8522f87b7bab9566` | `9336c8176275494d43b5b0058005b1753a5531580c2c101937ac8bee5313d21a` |
| `Toy.DropScope.noTailEscapingTemps_stmtTempsProg` | none | `600c960bff7179a179bff0b49b836018e01c6f075367ac384bd0f1141f2288d0` | `d5794e063bb0f41f9d6fba22a29831f76570be786ef5170cb70f798a54dd8ddc` |
| `Toy.DropScope.not_behIncl_e2021_e2024_at_tailProg` | none | `15a28540a17d652606cef3ccae4c85d104e01c442acbc0e3823c02ba78378954` | `e54caeb986a810073c1efdcb0271573554f19143c055efb8bcc08228e23ccd9a` |
| `Toy.DropScope.not_commute_tailProg` | none | `56b4febe9afbb3c6f92f4ff585dbf36f9076d8edd4ee8041b2a82933943362f4` | `72244617657df44a2acb1ad4e609a0ceea115713aee85993cc9472acc7f13607` |
| `Toy.DropScope.not_flipped_tailProg_mkLocal` | `Quot.sound`, `propext` | `eef8e5debc6a1f4cd859c0b2ed1cf88b4f76792b57c5a11c505d9d7511ca5279` | `ddd4e31a28f747adb959cec2aeeac8b4d8d0582b9497d04c89ebed0f09e981be` |
| `Toy.DropScope.not_isDropTemp_dropLocal` | `propext` | `dbbf284f8d89ff03ba431d7c924786cf13c21c25843bc3b194145a36970662ba` | `683999a4c1b74c22bbe0913f5e9c3a0f8e25cae5be37476eb0fc1019ee15a31e` |
| `Toy.DropScope.not_noIfLetEscapingTemps_ifLetElseProg` | none | `f71bfa0732ad04f8ce6c5d46fddaef2f1846a3b227b8866339adbf8fe14799fc` | `f21125ac36140edb7bdbea6efa8e6aba750ea0f7eec0c61f6f3f9065c27cdc73` |
| `Toy.DropScope.not_noTailEscapingTemps_nested` | none | `e7c3c39eb2ca7e74ea65e33348e1cf1bb1bb41c19977c0d467ad14abf1dbb329` | `49571e2177b23e798a4f2b7e991ce902a9dc34c17caa1cc074efa9c95e04bff9` |
| `Toy.DropScope.not_noTailEscapingTemps_tailProg` | none | `55d14f0b49278664ae0cf7d60e9d8ec7473e46199a4351c751a5507983687507` | `fa5125025520a186e0c530f437f43b4916951110ecad8c33ea566883cf64c3e2` |
| `Toy.DropScope.not_refines_ret_ne` | `propext` | `e08869471ccde9418bfeb462e78092fa5227a33dca029b431a353eabaee570ce` | `a1e2413b583aded5ad24e183cdb3aaa66f411e638c1cdc3749737155c7cc6b62` |
| `Toy.DropScope.not_refines_ub_ret` | `propext` | `b0e1fda2e15078f120d6bcb5f70d52e221afdf8c5bf6d4f7b727f0aee30439be` | `a1e2413b583aded5ad24e183cdb3aaa66f411e638c1cdc3749737155c7cc6b62` |
| `Toy.DropScope.orderingSwitch` | none | `8f5dea4cf189b0e9cd765c17804d6f01e773ce40e1db11475f606d32127c0983` | `e878d1802b8f28c19cbeff4794e2045760efee4237c7dab0e392a6bc23bfe15e` |
| `Toy.DropScope.outsSeq` | none | `1bb2571cd29123480193ec74b01d5142475c13990d1212878c9169e161d9b07e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.permissiveRejectInvalid` | none | `ffa61dd559b3ec7f703f2252e052ae4ace8cf387b4c83d28fde3ce0a0c10d707` | `fad461b99601c4c3ebec53d9963b82283c77f3c70857993a05fba346236f4714` |
| `Toy.DropScope.pruneArms` | none | `ec87363907f5ff8ca0762679d7c84aa8c2f1fb4998fd038026b07683723cffbf` | `e878d1802b8f28c19cbeff4794e2045760efee4237c7dab0e392a6bc23bfe15e` |
| `Toy.DropScope.pruneArms_example` | none | `f8ba5ab617f6761412445ab8b84698517dc1db4563b24c19b28d636dc44f896e` | `7b8f059b767db7fdd69279a27779738f78ae1db3b9ba9c5ccb80e2e0b2a94c5c` |
| `Toy.DropScope.pruneArms_keeps_allowed` | none | `f4a1f4185b030f94b57b85c7722460cb75b381ad82e2a52d220d1646ea7ad3b9` | `7b8f059b767db7fdd69279a27779738f78ae1db3b9ba9c5ccb80e2e0b2a94c5c` |
| `Toy.DropScope.readUB` | `propext` | `e92c5694bcffb6e23889a224ddcaa1869a274bb7c3ecaa4a8495e8aac372751b` | `5b191b0729c2a12914d1268f1eb64ec895155bfeb3fead9d7c0e6c3931471ba1` |
| `Toy.DropScope.readUB_emptyEnum` | `propext` | `e2ba8f7c95bdbdeeebfbaa818e8a5263b79053939c63f16291a93e441e5bf849` | `be03a4d8d8699183ae062c4a7794cd8c5eab1fdb60a6d5c9998e740e0a6273e8` |
| `Toy.DropScope.readUB_inhabited` | `propext` | `b8dedee42ad74ee81ff7dd88a9c453656dc9b6189a9e59016803385002199213` | `be03a4d8d8699183ae062c4a7794cd8c5eab1fdb60a6d5c9998e740e0a6273e8` |
| `Toy.DropScope.readUB_invalid` | `propext` | `7317b6ef1975777e341d1dc2f0191c1ff4df4e84a68aec14ffa1477f6889ef7b` | `be03a4d8d8699183ae062c4a7794cd8c5eab1fdb60a6d5c9998e740e0a6273e8` |
| `Toy.DropScope.readUB_permissive` | `propext` | `9ba5ca8ac65a25126b13d12e051f8f1e5af42f5534c92633114e4f7af35c69f5` | `be03a4d8d8699183ae062c4a7794cd8c5eab1fdb60a6d5c9998e740e0a6273e8` |
| `Toy.DropScope.readUB_rejectBoth_of_allowedTag_eq_false` | `propext` | `59c304970090b5fd507c31473ecae9052efadf811d3306e645c427a0cee10d2d` | `cabc29e9cf04a1a0ca13c6ff923620255ac53ddc538f15841609d6678ea0dbc9` |
| `Toy.DropScope.readUB_rejectUninhabited` | `propext` | `53ca2008ed2a95a29e2827c66fcf066d98f7d052b0e9497849ed199c98f70df8` | `be03a4d8d8699183ae062c4a7794cd8c5eab1fdb60a6d5c9998e740e0a6273e8` |
| `Toy.DropScope.refCellTailProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.refCellTailProg_flipped_commute_and_trace_eq_and_accepts_ne` | `propext` | `4390415c074f471ea6b33cf35038d3b3f184c9296b20074a8553db22c7df1c09` | `059f623c49f10af5707e94606ba677dfa0f02261b7780859026b936794a5dc50` |
| `Toy.DropScope.refines_ret_eq` | none | `1a7d6374a010e312934d160a60bd6cc78a1be68b9a6968b2308e64f6c9de3336` | `a1e2413b583aded5ad24e183cdb3aaa66f411e638c1cdc3749737155c7cc6b62` |
| `Toy.DropScope.refines_ub` | none | `6b5eb35c3265b2f8c0e98eaabbc2770e53d726b39e8961e1a4559ec0418ecb17` | `a1e2413b583aded5ad24e183cdb3aaa66f411e638c1cdc3749737155c7cc6b62` |
| `Toy.DropScope.refuted_allInhabited_specializeEnum_changes_nothing` | `propext` | `65fb671fc15f8f08736d82ef902c534b539aa13906839398c95baa5a08dd8e6c` | `84240bcd24c59cc4477b069090a108fdfd8994ee725500168025adc226896b00` |
| `Toy.DropScope.refuted_emptyTailDtors_give_run_eq` | none | `38eaa3b7de1cdcd05ae3605a1fa2e2d0a7314eebba01bb99b8e537e942ee465a` | `86bc2c754f131994dc578447f4bdf176f5bd10ffee211b62e1f80f29ec4c1381` |
| `Toy.DropScope.refuted_specializeSwitch_retargets_every_nonAllowed_tag` | `propext` | `861cd19fb1bbb042cbe8a59be2bdb1d883e200c3ec62d4be6c8f50cb50cf4e7e` | `9dea3c30bd4c58780eb83d194d59e478e8030e9c8527a672ac1847bbe0f285c3` |
| `Toy.DropScope.refuted_stmtTempsProg_three_temp_drops` | `propext` | `b1608a6ab509a2961ab7daf60b148e17b133331489cad98f048c942c5532b45f` | `1b96c5151a4eb35b82c28a0dc85bb08c62179d52237211d01378a9f8ebfbdc5e` |
| `Toy.DropScope.rejectBoth` | none | `ffa61dd559b3ec7f703f2252e052ae4ace8cf387b4c83d28fde3ce0a0c10d707` | `fad461b99601c4c3ebec53d9963b82283c77f3c70857993a05fba346236f4714` |
| `Toy.DropScope.remainingAllowed` | none | `1009f983c5fd964c9fd04f891d7adc3f3f72fbc0b5373c2baf5d2450ff9cba18` | `e878d1802b8f28c19cbeff4794e2045760efee4237c7dab0e392a6bc23bfe15e` |
| `Toy.DropScope.remainingAllowed_all_covered` | none | `c92de43729b939db3e23be71a38525eaf7be0abb2565af4f150aea8cb6459693` | `f25c8a262747642e1244a31cabd608eff64a890d996c201e2505359b59d56c2c` |
| `Toy.DropScope.remainingAllowed_orderingSwitch` | none | `72589f227dc0a9a033667e4100e01981ceb0f1ec4d821ed89d94d606e2970dc3` | `845014be3c53074e3a2b281946c6e6a5482cc133b117ea100ebb2b333f62e6a6` |
| `Toy.DropScope.run` | none | `7f43feb6cafc1eb22976f77556934ef4a6a24dc36e28d6b99433759251b88423` | `adea3586c957dc8f7e53bece1bc501dfc95d28564db0669dc815c11230fe6c18` |
| `Toy.DropScope.runArm` | none | `b209dd3cc4507d1e4fbcc09e713aadb7e4e43e43dae61ec5e5f33b440a68c0c5` | `439432cd5723b767e9a84763a882dee1ed5dc56ba0123227de029aa521841164` |
| `Toy.DropScope.runArm_usePayload_bad` | none | `22e0727564db4badcb909e9731ea2539c3ee81edd2280df2fdfa032271f9dd8d` | `68d5daa83179c67b0551d5a9e3ffcd9d7e0444da1ed50f266a1d27dae32127f7` |
| `Toy.DropScope.runArm_usePayload_ok` | none | `58b1c4dc83bccd367d107a7645e5ddb30178847f373418d35c49ef878c88d237` | `68d5daa83179c67b0551d5a9e3ffcd9d7e0444da1ed50f266a1d27dae32127f7` |
| `Toy.DropScope.runSwitch` | `propext` | `957726d9c6863def8e67420bf36998272932b6b5c0d62bbd2b9026d0f8de9642` | `8586c8c1aff7f4063f71f312df62f2801cff7372d204715eedec415b0db05799` |
| `Toy.DropScope.shadowedBorrowProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.siblingTailProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.silentRefCellTailProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.silentTailProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.specializeEnum` | `propext` | `9e97dc36fe8326b0142748f2f547d6213762431a37a945b478f465972def4005` | `afa0ec2472639a4002539b21f4ac63faa444d6fe123160af21e12fd9d40ead01` |
| `Toy.DropScope.specializeSwitch` | none | `ec87363907f5ff8ca0762679d7c84aa8c2f1fb4998fd038026b07683723cffbf` | `e878d1802b8f28c19cbeff4794e2045760efee4237c7dab0e392a6bc23bfe15e` |
| `Toy.DropScope.stmtTempsProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.tailProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.tailProgLocalDrop` | none | `1b17576a7a090b23ff6637d2d7ce0e1d46327c737d50b263f4a289143da5a68a` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.tailProgTempDrop` | none | `1b17576a7a090b23ff6637d2d7ce0e1d46327c737d50b263f4a289143da5a68a` | `bd0f4b4fad5bcee1d2a38bb38f64c9548dc7d2b113c748b3fc4b23035b1ea2d8` |
| `Toy.DropScope.tailSiteProg` | none | `347211fab1d306f531f3cfd2f6fbfb843f1b03a4aa85d07c7eb75251b1f5d61d` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.tailsClean` | none | `fb84afd68db6e584ae6508523c8c9915c51386ea85a180a7c954ec76662a3381` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.tailsCleanBlock` | none | `aea6b59bafa71ccf90b40bddfad6a297e6190e123e39f56ecc5a8119c8444eed` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.target_orderingSwitch_0` | none | `411ec0d400c89c3682e72c208bd7d948c06e2d29748ebf0b038bf5509bfc35ae` | `7359deb112d9497a5c2d315fc80b3bdce557adbc4e8b1fe26dd54030d2519667` |
| `Toy.DropScope.target_orderingSwitch_2` | none | `1b004504f926ffea5df38b0a1b21f0c0d24172f5ddeda4c37a2786c82a0f33bd` | `7359deb112d9497a5c2d315fc80b3bdce557adbc4e8b1fe26dd54030d2519667` |
| `Toy.DropScope.tempsSeq` | none | `8203b80b46efa3d8044912cced66ce36aab0e5abf8a225c0ef22898fe43cd68c` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.thenBranchProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.toMatch` | none | `9453549b2323b79493f4977d3c6294c0494f32e2598c4e5747bbae3fb392d0e2` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.toMatchBlock` | none | `9e813c5e26dbd91862a40bc9c868b63be4e09fafd05f457011eb39c1f1d1a282` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.toMatch_ifLetElseProg` | none | `31ce1b91ca5a59795b32b4ad8d1004b32000ba98df73dd0e1f9c3fba898cdd0e` | `a2be4f8db2aeb4adfd04d7561b77108ffc6bed602d226383b11c8b1e9ff443cd` |
| `Toy.DropScope.topLevelTailTempProg` | none | `fb343310c03cda605a30de13482f54f64e70456fb52378b31fcaf91fb0816b6e` | `29246fedfdbb433da151012777b6c365e24efd41c390a125eb39d30e46eb8f97` |
| `Toy.DropScope.trace` | none | `f5ae3dc4f91c77fc01f49d36f8b0c9b987ac3a6fc4094347a02173e09ef148b7` | `e4b234bfa6471d9f7822a65b870cce6eedf0884a109df8b0107e42d92e9788cb` |
| `Toy.DropScope.trace_ifLetElseProg_e2021_ne_scrutinee_first` | none | `681aa34c5328528b1fe1641f1bc719ccc9ce91029861a920acf10469db7e3f34` | `332d0e609c20372f966e86d1921db1bdfb241a5c83b19b16c35c9f21a0af2290` |
| `Toy.DropScope.trace_ifLetElseProg_e2024` | none | `57fb3e8e3ddbffa3073019c9c122334105b43149d8c26c472d4ead29e813d84c` | `332d0e609c20372f966e86d1921db1bdfb241a5c83b19b16c35c9f21a0af2290` |
| `Toy.DropScope.trace_ifLetThen_e2024` | none | `61fa21de8615368560bbfd1ad01f0f93b4d16057dfb3c862e896cf5243d8a406` | `d714d660f9d2881c6979ffa26f02d32c39dcb433bd3e644a038e89d82bad91ed` |
| `Toy.DropScope.trace_letInitTemp_both` | none | `606095985121c6a00729819389c67903cf12d0c79e0b1186098132ba8cf0bbcf` | `d714d660f9d2881c6979ffa26f02d32c39dcb433bd3e644a038e89d82bad91ed` |
| `Toy.DropScope.trace_tailProg_e2021` | none | `486232e0884360922096b3f80c5cab9b6b13d04bebaf84ad43fa1958f52273b9` | `7345951b5e42f98c31b67d8adf6bbf3894aef37f7278e9b957a8b1a92a33fa33` |
| `Toy.DropScope.trace_tailProg_e2024` | none | `b9a60245c31abf8e3563f6028dc6d8aa5f4099cef3d705a99bec02c9eafaf9e1` | `7345951b5e42f98c31b67d8adf6bbf3894aef37f7278e9b957a8b1a92a33fa33` |
| `Toy.DropScope.trace_tailProg_e2024_ne_local_first` | none | `a834d17bc465776593849bb2222be4e40d23c071b7186816a0be085b9dc40bd6` | `7345951b5e42f98c31b67d8adf6bbf3894aef37f7278e9b957a8b1a92a33fa33` |
| `Toy.DropScope.trace_two_temps_reverse` | none | `3081f2787f123096179fabf5fb6e022be7f9db224076c3c5bb4710c7284525ef` | `d714d660f9d2881c6979ffa26f02d32c39dcb433bd3e644a038e89d82bad91ed` |
| `Toy.DropScope.usePayloadSwitch` | none | `8f5dea4cf189b0e9cd765c17804d6f01e773ce40e1db11475f606d32127c0983` | `e878d1802b8f28c19cbeff4794e2045760efee4237c7dab0e392a6bc23bfe15e` |
| `Toy.DropScope.usePayloadSwitch_permissive_specializeEnum_refines` | `Quot.sound`, `propext` | `bc478770a9a13903f1ce5d5b4efdf55973f97e4574a3896cbcd3e8b6f395dcc9` | `7c09271675113d1e9f6732a87bb82b27de406742926acc0ccd37d9a0efb00bf0` |

### Primary sources

External files were fetched on 2026-11-21 at the pinned revisions below; every verbatim quote under *External sources* was compared line by line with the fetched file (file SHA-256 in parentheses):

* rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f `src/rust-2024/temporary-tail-expr-scope.md` (`4a5b00fed6e2e7328dd2c03bf94fa2dbead59ff37d162b367442a7bbdd4bc677`) and `src/rust-2024/temporary-if-let-scope.md` (`e1185817f15b842f231b7b89f362db10aeb1ffd1af6ee128f95a848548ef5969`) [documentation]
* rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 `text/3606-temporary-lifetimes-in-tail-expressions.md` (`fbff55cca1d517ed043c5ff55a4a78b6c7711163ec6e493d47a22271956e1bce`) and `text/0066-better-temporary-lifetimes.md` (`c9fbe2541a660a972643b8eddfcf4181ccc6265faeb412b0148f448e6ce40762`) [documentation (accepted design RFCs)]
* rust-lang/reference@84dc36ff4712fad6829b6063cd4acbcaf5381708 `src/destructors.md` (`3dd3a9215d8d8b3bdbcf9282679f272a5c9a8a147720a448a79bbdea3f65f51b`) [documentation]
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe `compiler/rustc_mir_transform/src/unreachable_enum_branching.rs` (`75408fed3fa223d2ac0ce51a30bdd3d2c9ac780e9338cf44a80dd222b267773e`), `compiler/rustc_middle/src/mir/syntax.rs` (`24450e48c164243648410aefa13dfe2faaf632c1681b418b0d0d0687495b6b39`) and `compiler/rustc_abi/src/lib.rs` (`a5dd6fdc63d995f95c2093cfed3b1828e9e6ffb185788e4c2122f7450d9a992b`) [documentation and source comments; used in derived (modeling bridge) remarks only as documented behaviour]
* minirust/minirust@063d784186d3252bee242217f218223205c0b568 `spec/lang/step/expressions.md` (`cfa01e5f8d30eae252e36dbd1ecca51365f5cc02e90fe73b1b706fc3747cb6cb`) and `spec/lang/step/terminators.md` (`ae0c30634abe041ab520ee647c249489db5aa01e82ee0baa07b783e1d4086360`) [documentation (a proposed specification)]
* The Lean release tag `v4.34.1` resolves to commit `5045d0056413266e57c625dcd7c365b10e377c52` of leanprover/lean4 (GitHub API, 2026-11-21).
* Bibliographic records of the cited works were checked against their DOI metadata on 2026-11-21: Cartier and Foata 1969 (10.1007/BFb0079468), Mazurkiewicz 1977 (10.7146/dpb.v6i78.7691), Diekert and Rozenberg 1995 (10.1142/2563), Lothaire 1997 (10.1017/CBO9780511566097), Lyndon and Schützenberger 1962 (10.1307/mmj/1028998766), Leroy 2009 (10.1145/1538788.1538814), Lee et al. 2017 (10.1145/3062341.3062343), Wang et al. 2018 (10.1109/TASE.2018.00014), Gäher et al. 2024 (10.1145/3656422). Their full texts were not inspected.

## Revalidation

Requirements: `elan` (it installs the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No other tool and no network access beyond the toolchain download are needed.

Primary command, run from the package directory:

```text
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory and never modifies the package. It then (1) runs `lake build`; (2) checks that no Lean source contains `sorry`, `admit` or `native_decide` or declares an `axiom`; (3) computes, with Lean's `collectAxioms`, the axioms of every declaration of the library and checks that only `propext`, `Classical.choice` and `Quot.sound` occur; and (4) for every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample` lists) recomputes the SHA-256 of the statement (the Lean `repr` of the declaration's type) and of its definition closure (the sorted `name : type := value` texts of every package-local constant reachable from the statement, theorem bodies excluded) and compares them with `audit/statements.json`. Exit status 0 means all four checks passed.

Manual alternative (build and print the axioms of the main results):

```text
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is not part of the library target; it imports the library and runs `#print axioms` on every main result of the cards (the `lean` field of every entry of `results.json`). Each line of its output must list only `propext`, `Classical.choice` and `Quot.sound`, or report that the declaration depends on no axioms.

To check that a later Lean release or a modified copy still supports the cards, edit `lean/lean-toolchain`, run the primary command, and compare: a changed statement or closure hash means that the corresponding card must be re-read against the new statement before it is relied on.
