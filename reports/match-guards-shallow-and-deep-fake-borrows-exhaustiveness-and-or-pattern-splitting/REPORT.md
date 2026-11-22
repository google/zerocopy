# Match guards: shallow and deep fake borrows, exhaustiveness preservation, or-pattern splitting, constant patterns and deref accessors in a toy match lowering (Lean 4)

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Model–system relation: none proved. These are statements about the toy model (namespace `Toy.MatchGuard`); they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, the Rust Reference, or Rust's unstable deref patterns. Real systems enter as separate `derived (modeling bridge)` remarks that quote their documented behaviour at pinned revisions; no tool was run and nothing was measured.

Every result below is kernel-checked in Lean 4 (`leanprover/lean4:v4.34.1`, no Mathlib) with at most the standard axioms `propext`, `Classical.choice` and `Quot.sound`. Each bullet is the card's plain-language claim, verbatim; kind, tier and depth follow the card name.

* **R1** `runMatch_not_unreachable_of_exhaustive_of_shallowFrozenAll_of_deepFrozenAll` (theorem, T1, substantive): For every value domain `Dom`, every arm list `arms` that is exhaustive on `Dom` (`Exhaustive Dom arms`: every value in `Dom` is matched directly by some arm that has no guard), such that no guard write of any arm is to a place switched on by any arm or to a prefix of such a place (`ShallowFrozenAll arms`) and no guard write of any arm is to a place that overlaps a deref-pattern scrutinee of any arm (`DeepFrozenAll arms`), and every `v` in `Dom`, the toy lowered execution `runMatch arms v` does not reach `Unreachable`.
* **R2** `runMatch_not_unreachable_of_exhaustive_of_guardsPreserveDom_of_frozenBefore` (theorem, T1, substantive): For every value domain `Dom` and every arm list `arms` that is exhaustive on `Dom`, whose guards keep the memory inside `Dom` when run from any memory in `Dom` on which their arm matches directly, whether or not the lowered execution can reach that guard with that memory (`GuardsPreserveDom Dom arms`), such that each guard writes neither a place switched on by its own arm or by an earlier arm nor a prefix of such a place (`ShallowFrozenBefore arms`) and writes no place overlapping a deref-pattern scrutinee of its own arm or of an earlier arm (`DeepFrozenBefore arms`), and every `v` in `Dom`, `runMatch arms v` does not reach `Unreachable`.
* **R3** `reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable` (counterexample, T1, definitional): There is a deref-free arm list, `reassignArms` (on `x : &Option<bool>`: `match *x { None, Some(_) if { x = &None; false }, Some(true), Some(false) }`, adapted from rustc's E0510 example on `&Option<i32>` with its last arm split), that is exhaustive on `RefOptBoolDom`, satisfies `DeepFrozenAll` (vacuously: it has no deref-pattern test), violates `ShallowFrozenAll` (its guard writes `x`, a prefix of the switched place `*x`), and whose lowered execution on `&Some(true)` reaches `Unreachable`.
* **R4** `boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable` (counterexample, T1, definitional): There is an arm list, `boxBoolArms` (on `b : Box<bool>`: `match b { deref!(true), _ if { *b = true; false }, deref!(false) }`), that is exhaustive on `BoxBoolDom`, satisfies `ShallowFrozenAll` and shallow freezing of its deref-pattern scrutinee (`ShallowFrozenDerefAll`), violates `DeepFrozenAll`, and whose lowered execution on `Box(false)` reaches `Unreachable`.
* **R5** `runMatch_not_unreachable_of_noDerefPatterns_of_exhaustive_of_shallowFrozenAll` (theorem, T1, shallow): For every value domain `Dom` and every arm list `arms` with no deref-pattern test (`NoDerefPatterns arms`) that is exhaustive on `Dom`, such that no guard write of any arm is to a place switched on by any arm or to a prefix of such a place (`ShallowFrozenAll arms`), and every `v` in `Dom`, `runMatch arms v` does not reach `Unreachable`.
* **R6** `shallowFrozenAll_of_deepFrozenSwitchAll_strict_on_shallowGuardArms` (theorem, T0, definitional): For every arm list `arms`, if no guard write of any arm overlaps a place switched on by any arm (`DeepFrozenSwitchAll arms`), then `ShallowFrozenAll arms`; and there is a deref-free arm list exhaustive on `OptIntDom`, namely `shallowGuardArms` (adapted from the allowed example in rustc's `FakeBorrowKind::Shallow` documentation), that satisfies `ShallowFrozenAll` and violates `DeepFrozenSwitchAll`.
* **R7** `borrowck_eq_true_iff` (characterization, T0, definitional): For every arm list `arms`, the toy borrow check `borrowck arms`, which tests every guard write against a shallow fake borrow of every switched place and a deep fake borrow of every deref-pattern scrutinee (`fakeBorrows arms`), returns `true` iff `ShallowFrozenAll arms` and `DeepFrozenAll arms`.
* **R8** `runMatch_not_unreachable_of_borrowck_of_exhaustive` (theorem, T1, shallow): For every value domain `Dom`, every arm list `arms` accepted by the toy borrow check (`borrowck arms = true`) and exhaustive on `Dom`, and every `v` in `Dom`, `runMatch arms v` does not reach `Unreachable`.
* **R9** `sameVariantArms_rejected_exhaustive_and_never_unreachable` (counterexample, T1, shallow): There is an arm list, `sameVariantArms` (on `x : Option<i32>`: `match x { None, Some(_) if { x = Some(5); false }, Some(_) }`), that `borrowck` rejects, that is exhaustive on `OptIntDom`, and whose lowered execution reaches no `Unreachable` on any value of `OptIntDom` (every test of `sameVariantArms` reads the variant at `[]`, and its guard writes a value with the same variant).
* **R10** `OrPat.runSrc_eq_runSplit_splitArms` (theorem, T1, substantive): For every drop policy `pol`, every value `v`, every arm list `arms` (patterns may contain nested or-patterns and are not required to be well-formed; guards may read bindings) and every starting arm index `i`, the source semantics `runSrc pol v i arms`, which evaluates an arm's guard once for each matching alternative with that alternative's bindings, produces the same event trace as the split lowering `runSplit v (splitArms pol i arms)`, whose sub-branches each carry their own copy of the guard and the policy's drop order.
* **R11** `OrPat.runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms` (counterexample, T1, definitional): For every drop policy `pol`: on `(1, 2)`, for `bindingGuardArms` (`(x, _) | (_, x) if x == 2 => .., _ => ..`, whose guard reads its binding), the source semantics evaluates the guard with `x = 1`, then with `x = 2`, runs the body of arm `0` with `x = 2` and drops `2`, while the guard-once lowering `runGuardOnce` evaluates the guard exactly once (with `x = 1`) and runs the body of arm `1`; and on `1`, for `constGuardArms` (`1 | _ if { effect; false } => .., _ => ..`, whose guard returns `false` for every binding environment), the source semantics evaluates the guard exactly twice and the guard-once lowering exactly once, both then running the body of arm `1`. In both cases the two traces differ.
* **R12** `OrPat.runSrc_firstAlternative_eq_matchedAlternative_of_noDupBindings_of_sameDeclOrder` (theorem, T1, substantive): For every value `v`, every arm list `arms` and every arm index `i` such that no alternative of any arm's pattern binds a name twice (`NoDupBindings`) and every alternative of every arm's pattern declares its bindings in the order of that pattern's first alternative (`SameDeclOrder`), the source traces under the `firstAlternative` and `matchedAlternative` drop policies are equal.
* **R13** `OrPat.runSplit_matchedAlternative_ne_runSrc_firstAlternative_refDropArms` (counterexample, T1, definitional): There is an arm list, `refDropArms` (`Ok((x, y)) | Err((y, x))`), and a value, `Err((10, 20))`, on which the split lowering whose sub-branches drop in their own declaration order (`splitArms .matchedAlternative`) does not reproduce the source trace under the `firstAlternative` policy.
* **R14** `ConstPat.loweringAgrees_of_allDerived_of_noFloat` (theorem, T1, shallow): For every toy type `T` all of whose struct and enum nodes have a derived `==` (`AllDerived T`: every node of the type, whether or not a given constant uses it) and which has no float leaf (`NoFloat T`), for every constant `c` and every scrutinee `v` of type `T`, the structural lowering `smatch c v` (which compares float leaves by bit pattern) equals `teq T c v`. This is the `←` direction of R15.
* **R15** `ConstPat.loweringAgrees_iff_noFloat_of_allDerived` (characterization, T1, shallow): For every toy type `T` all of whose struct and enum nodes have a derived `==` (`AllDerived T`), the structural lowering (which compares float leaves by bit pattern) agrees with `teq T` for every constant and every scrutinee of type `T` (`LoweringAgrees T`) iff `T` has no float leaf (`NoFloat T`).
* **R16** `Accessor.shared_selected_eq_repeated_selected_iff_resultStable` (characterization, T0, shallow): For every accessor `acc : Acc σ S R` (every hidden-state type `σ`, scrutinee type `S` and result type `R`), the shared and repeated lowerings select the same arm for every scrutinee, every hidden state and every arm list iff `ResultStable acc`: from every hidden state, reachable or not, and every scrutinee, a second call returns the same result as the first.
* **R17** `Accessor.shared_eq_repeated_iff_resultStable_and_stateIdempotent` (characterization, T0, shallow): For every accessor `acc`, `shared acc s arms st = repeated acc s arms 0 st` (the same selected arm and the same final hidden state) for every scrutinee `s`, every hidden state `st` and every arm list `arms` iff `ResultStable acc` and `StateIdempotent acc`, each required from every hidden state, reachable or not.
* **R18** `Accessor.repeated_not_unreachable_on_exhaustiveOn_iff_resultStable_of_wellTyped` (characterization, T1, shallow): For every result domain `RDom` and every accessor `acc` all of whose results, from every hidden state and every scrutinee, lie in `RDom` (`WellTyped RDom acc`): the repeated lowering does not reach `Unreachable` for every arm list exhaustive on `RDom` (`ExhaustiveOn RDom arms`), every scrutinee and every hidden state, iff from every hidden state, reachable or not, and every scrutinee, a second call returns the same result as the first (`ResultStable acc`).
* **R19** `Accessor.toggleAcc_repeated_reaches_unreachable` (counterexample, T1, definitional): There is an accessor, `toggleAcc : Acc Bool Unit Bool` (hidden state `Bool`, scrutinee `Unit`, result `Bool`; it returns its hidden flag and flips it), that satisfies `WellTyped (fun _ => True)` (every result lies in the full `Bool` domain) and is not result-stable, and with the exhaustive arm list `boolResultArms` (`[true => .., false => ..]`) from hidden state `false` the repeated lowering reaches `Unreachable` while the shared lowering selects arm `1`.

Non-claims for every card are listed under **Boundaries** (non-claims first); read them before relying on a result. In particular, `runMatch` is one in-order toy lowering that memoizes switch results; bindings are by-value reads that no freezing predicate constrains; the float results concern the toy's bit-pattern leaf test; and the accessor results concern state-passing functions that cannot modify the scrutinee.

## Applicability

### Model fidelity

This is a toy model. Its definitions are meant to capture how a `match` with guards is lowered to a decision procedure that tests places of the scrutinee, runs guards that may write places, and continues testing later arms after a failed guard; the fake borrows that rustc documents for keeping tested places stable across guards (shallow for switched places, deep for deref-pattern scrutinees); the splitting of guarded or-patterns into sub-branches and the drop order of their bindings; the lowering of constant patterns to structural tests; and repeated versus shared calls of a user-defined accessor in deref patterns. The parts of the model:

- **Freezing and exhaustiveness.** A scrutinee is a toy value (`Val`); places are projection paths. An arm is a list of tests (switches on a place's head, or deref-pattern tests through the box at a deref-pattern scrutinee), bindings (by-value reads of places, taken before the guard runs), and an optional guard (syntactic writes, then a condition). `runMatch` tries arms in order; a switch reads a place's head at most once and every later test of that place reuses the recorded result; deref-pattern tests re-read through the box each time; failing every arm reaches `Unreachable`. A test on a nonexistent place fails; a write to a nonexistent place is skipped. Exhaustiveness is relative to a value domain `Dom` and counts unguarded arms. Freezing predicates restrict the places guards write: shallow (no write to a frozen place or to a prefix of it) and deep (no write overlapping it); static forms freeze for the whole match, per-guard forms freeze the places of the guard's own and earlier arms. A toy borrow check (`borrowck`) decides the static forms.
- **Or-patterns.** A separate pattern language with nested or-patterns; `runSrc` enumerates matches left to right and evaluates the guard once per matching alternative; `runSplit` runs or-free sub-branches. Event traces record guard evaluations, the body, and destructor runs; drop order is a parameter (`firstAlternative` or `matchedAlternative`).
- **Constant patterns.** Canonical value trees and toy types whose struct/enum nodes carry a derived or manual `==`; `smatch` is a structural lowering of a constant pattern that compares float leaves by bit pattern; `teq` is the type's `==` (IEEE-style on float leaves).
- **Accessors.** Accessors `σ → S → R × σ` (hidden state, scrutinee); `repeated` calls the accessor once per arm test, `shared` once.

Known gaps (each is repeated in the non-claims of the cards it affects):

- `runMatch` is one lowering strategy: arms in order, every switch result memoized for the rest of the match, deref-pattern tests re-read after every guard, matching continued on the memory a failed guard left. rustc documents a backtracking automaton that may test a place more than once (B3); it is not modelled.
- A test on a nonexistent place fails and a write to a nonexistent place is skipped; Rust would reject such a program or have undefined behaviour of another kind.
- Bindings are by-value reads taken before the guard runs, and no freezing predicate constrains bound places; the Rust Reference instead takes shared references to bound parts of the scrutinee during the guard, and rustc fake-borrows the dereference prefixes of bound places (B1).
- Guard writes are a syntactic list of (place, value function); writes through aliases, raw pointers, interior mutability or calls are not modelled; arm bodies are not modelled.
- Values use unbounded integers (`Int`); there is no overflow.
- The or-pattern language does not enforce Rust's static rules (equal binding sets of alternatives, unique identifiers); guards there are functions of the bindings that cannot write the scrutinee (B4).
- The constant-pattern lowering `smatch` compares float leaves by bit pattern, while rustc compares float constants with `==` (B5); the toy's conditions `AllDerived` and `NoFloat` are on the whole type, the Reference's on the constant's value.
- Toy accessors are functions `σ → S → R × σ` that cannot modify the scrutinee (B6). Deref patterns (`deref_patterns`) and `DerefPure` are unstable Rust features.

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, or the Rust Reference.

### Modeling bridges (`derived (modeling bridge)`; not proved)

Each bridge quotes documented behaviour at a pinned revision and states how the toy relates to it. Basis: derived (modeling bridge) — the correspondence is textual; no relation between the toy and rustc or the Reference is proved.

- **B1 (fake-borrow placement).** rustc documents a shallow fake borrow for places matched on (`FakeBorrowKind::Shallow`, `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:247-278`), a deep fake borrow for deref-pattern scrutinees (`:279-292`), and fake borrows "for each discriminant accessed in the entire `match` statement" at the beginning of each guard (`:507-519`). `collect_fake_borrows` documents that it fake-borrows the places "bound or tested by the match" and, because "Borrowing `*x` doesn't prevent assigning to `x`", also the prefixes of such places (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:34-68`); it inserts a deep borrow for a deref-pattern scrutinee and a shallow borrow for every switched place (`:161-193`), and a shallow borrow of the dereference prefixes of bound places (`:195-227`). The toy's `ShallowFrozenAll`, `DeepFrozenAll` and `borrowck` mirror the placement for tested places (one set for the whole match, live across every guard; a write to any prefix of a frozen place conflicts). They do not model the borrows of bound places: in the toy, bindings are by-value reads taken before the guard and are not frozen (contrast `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:175-182`, quoted in R1). Reasoning: correspondence of documented placement to toy definitions; no claim that rustc's borrow checker decides exactly `ShallowFrozenAll ∧ DeepFrozenAll`.
- **B2 (headline examples).** `reassignArms` is adapted from the E0510 example of the `Shallow` docs (rustc's scrutinee is `&Option<i32>`; the toy uses `&Option<bool>` and splits the last arm into `Some(true)`/`Some(false)`; on the unsplit shape the toy selects the last arm, `e0510Arms_selects_last_arm_with_changed_memory`); `boxBoolArms` mirrors the `Box<bool>` example of the `Deep` docs, which ends "UB because we reached the unreachable" (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:279-292`); `shallowGuardArms` mirrors the allowed example of the `Shallow` docs. Reasoning: same arm structure and same guard writes; rustc's actual MIR for these programs was not examined.
- **B3 (lowering strategy).** `runMatch` memoizes every switch result for the rest of the match. rustc documents a "backtracking automaton" lowering that may test the same place more than once ("Note how we test `x` twice. This is the tradeoff of backtracking automata", `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:1739-1740`; `:2232-2270`), and terminates the otherwise block of an exhaustive match with `TerminatorKind::Unreachable` (`:1643-1671`). Reasoning: the toy models one lowering strategy; no correspondence with rustc's strategy is claimed.
- **B4 (or-patterns).** The Reference says "Each pattern will be tested in left-to-right sequence until a successful match is found" (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:83-84`), that after a failed guard "the next pattern, including other matches with the `|` operator in the same arm, is tested" (`:145-146`), and that the guard may execute multiple times (`:159-170`); it defines matching `c(p | q, ..rest)` as matching `c(p, ..rest) | c(q, ..rest)` (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:1044-1045`). This is `runSrc` with `expand`'s left-to-right order. rustc documents sub-branches "requiring its own bindings and its own copy of the guard" that "jump together to a common block" (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:509-513`); `runSplit` gives each sub-branch its own guard copy but, unlike rustc, also its own body event. For drop order the Reference says or-patterns "declare bindings in the order given by the first subpattern" (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/destructors.md:223-224`, example `:226-259`), and rustc lowers sub-branches in reverse "To use the drop order for the first sub-branch" (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:550-551`); this is the `firstAlternative` policy. The Reference requires the alternatives of `p | q` to introduce the same set of bindings (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:1024-1031`) and an identifier to be unique within a pattern (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:175-176`); the toy's `Pat` does not enforce either. Reasoning: textual correspondence.
- **B5 (constant patterns).** The Reference requires `T: PartialEq` and that "the value of `C` *has (recursive) structural equality*" (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:983-984`), where "A value of `struct` or `enum` type has structural equality if its `PartialEq` instance is derived via `#[derive(PartialEq)]`, and all fields (for enums: of the active variant) have structural equality" (`:995-996`) and "A float value has structural equality if it is not a `NaN`" (`:1001-1002`); the condition is on the constant's value, not on every node of its type. `StructuralPartialEq`'s documentation states the goal that "interpreting the value of the constant as a pattern is equivalent to calling `PartialEq`" (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:library/core/src/marker.rs:239-253`). rustc lowers a float constant pattern to `TestKind::ScalarEq` (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/test.rs:43-45`), performed as a `BinOp::Eq` comparison (`:181-234`), documented as "The `==` operator (equality)" (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1672-1673`); RFC 1445 records that match "*will* compare 0.0 and -0.0 as equal" (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07:text/1445-restrict-constants-in-patterns.md:238-253`). The toy's `smatch` compares float leaves by bit pattern instead, and the toy conditions `AllDerived` and `NoFloat` are on the whole type. Reasoning: the toy isolates the bit-pattern leaf test; its float results (R14, R15) are about that test and neither establish nor refute anything about rustc's float comparison.
- **B6 (accessors).** The perma-unstable `DerefPure` documentation says successive `deref` calls without intermediate mutation "should be idempotent, in the sense that they return the same value as far as pattern-matching is concerned" and that "The precise semantics are undecided" (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:library/core/src/ops/deref.rs:285-297`). rustc's deref-pattern test calls `Deref::deref[_mut]` and stores the result in a temporary (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:1342-1347`). The toy's `ResultStable` is one precise reading (identical result from every hidden state); toy accessors cannot modify the scrutinee. Reasoning: informal correspondence; no claim about which reading rustc relies on.

### Nearby reference-corpus packages

Published packages of the same corpus (google/zerocopy branch `reference`, commit `8978e7348aaa6d0808db1d0232d020d053020f4d`) are cited by name, not repeated, and are not subjects of this report: `place-evaluation-ub-placemention-erasure-inbounds-projections-and-equal-target-switches` (`PlaceMention` and the scrutinee read); `edition-indexed-drop-scopes-tail-and-if-let-temporaries-and-inhabitedness-gated-switches` (drop scopes of `match` temporaries, inhabitedness-gated switches); `enum-niche-layout-guarantees-and-validity-invariants` and `wrapping-niche-intervals-affine-tags-nested-option-capacity-and-discriminant-write-order` (how discriminants, the toy's heads, are encoded); `two-phase-borrows-reservation-activation-dominator-approximations-and-early-exit-edges` (borrow-check approximations); `drop-check-may-dangle-and-destructor-soundness-for-generic-containers` (drop check). As far as their catalog topics and titles show, none of them treats guards that run between discriminant tests and arm selection, or the fake borrows that keep tested places stable.

### Toolchain and project

* Lean `leanprover/lean4:v4.34.1` (pinned in `lean/lean-toolchain`); no Mathlib and no other dependency (`lean/lakefile.toml` has one `[[lean_lib]]`, `ToyMatchGuard`, and no `[[require]]`).
* Namespaces `Toy.MatchGuard`, `Toy.MatchGuard.OrPat`, `Toy.MatchGuard.ConstPat`, `Toy.MatchGuard.Accessor`. Files under `lean/ToyMatchGuard/`: `Places.lean` (values, places, writes), `Match.lean` (tests, guards, arms, `runMatch`, freezing predicates), `Exhaust.lean` (exhaustiveness preservation), `Checker.lean` (toy borrow check), `Instances.lean` (domains, arm lists, counterexamples, witnesses), `OrPat.lean` (or-patterns), `ConstPat.lean` (constant patterns), `Accessor.lean` (accessors).
* `lean/RevalidationAudit.lean` is outside the library target; it prints the axioms of every main result (see **Revalidation**).
* In the card names below, `OrPat.`, `ConstPat.` and `Accessor.` abbreviate `Toy.MatchGuard.OrPat.`, `Toy.MatchGuard.ConstPat.` and `Toy.MatchGuard.Accessor.`; all other names are in `Toy.MatchGuard`.

### Subjects

`REPORT.json` lists the Lean toolchain release that checks every proof; the upstream revisions whose documentation is quoted in modeling bridges and prior-art entries (rust-lang/rust `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, rust-lang/reference `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, rust-lang/rfcs `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`); and the papers cited as prior art. The toy is written in the style of the documented rules of those systems; the report establishes facts about the toy (kernel-checked) and, separately, quotes what those systems document. No relation between the toy and any of them is proved, and no tool of theirs was run.

## Findings

Statement blocks are verbatim quotes of the Lean sources under `lean/`, sliced by declaration and labelled with their `file:A-B` line ranges; definitions are quoted in full, theorem proofs are elided as `:= …`, and equation-style declarations are quoted through their signature. Renderings labelled "Unfolded (prose)" are prose, not Lean.

### Definitions (verbatim)

#### Values, places and writes

##### `Val`

```lean
-- lean/ToyMatchGuard/Places.lean:18-21
inductive Val where
  | int (n : Int)
  | ctor (tag : Nat) (fields : List Val)
  | box (v : Val)
```

Captures: toy runtime values: integers, enum values (active variant + fields) and boxes; `bool` and `Option` are encoded with `ctor`. A box also encodes a reference.

##### `vFalse`

```lean
-- lean/ToyMatchGuard/Places.lean:60-60
def vFalse : Val := .ctor 0 []
```

Captures: toy `false` (`ctor 0 []`).

##### `vTrue`

```lean
-- lean/ToyMatchGuard/Places.lean:62-62
def vTrue : Val := .ctor 1 []
```

Captures: toy `true` (`ctor 1 []`).

##### `vNone`

```lean
-- lean/ToyMatchGuard/Places.lean:64-64
def vNone : Val := .ctor 0 []
```

Captures: toy `None` (`ctor 0 []`).

##### `vSome`

```lean
-- lean/ToyMatchGuard/Places.lean:66-66
def vSome (x : Val) : Val := .ctor 1 [x]
```

Captures: toy `Some x` (`ctor 1 [x]`).

##### `Proj`

```lean
-- lean/ToyMatchGuard/Places.lean:72-75
inductive Proj where
  | field (variant idx : Nat)
  | deref
  deriving DecidableEq, Repr
```

Captures: one projection: a field of a given variant (it exists while that variant is active, and not otherwise) or a box dereference.

##### `Place`

```lean
-- lean/ToyMatchGuard/Places.lean:79-79
abbrev Place := List Proj
```

Captures: a path from the scrutinee root; `w <+: p` (list prefix) means that `p` lies inside `w` or equals it.

##### `step`

```lean
-- lean/ToyMatchGuard/Places.lean:83-86
def step : Val → Proj → Option Val
  | .ctor t fs, .field k i => if t = k then fs[i]? else none
  | .box v, .deref => some v
  | _, _ => none
```

Captures: one projection step on a value (`none` if it does not exist).

##### `lookup`

```lean
-- lean/ToyMatchGuard/Places.lean:89-94
def lookup : Val → Place → Option Val
  | v, [] => some v
  | v, p :: ps =>
    match step v p with
    | some c => lookup c ps
    | none => none
```

Captures: the value at a place, `none` if the place does not exist. Positive example: `lookup_example_some`. Negative example: `lookup_example_none`.

##### `setChild`

```lean
-- lean/ToyMatchGuard/Places.lean:97-100
def setChild : Val → Proj → Val → Option Val
  | .ctor t fs, .field k i, c => if t = k ∧ i < fs.length then some (.ctor t (fs.set i c)) else none
  | .box _, .deref, c => some (.box c)
  | _, _, _ => none
```

Captures: replaces the child selected by one projection.

##### `write`

```lean
-- lean/ToyMatchGuard/Places.lean:103-111
def write : Val → Place → Val → Option Val
  | _, [], new => some new
  | v, p :: ps, new =>
    match step v p with
    | none => none
    | some c =>
      match write c ps new with
      | none => none
      | some c' => setChild v p c'
```

Captures: writes a value at a place (`none` if the place does not exist).

##### `writeOrSkip`

```lean
-- lean/ToyMatchGuard/Places.lean:115-115
def writeOrSkip (v : Val) (w : Place) (new : Val) : Val := (write v w new).getD v
```

Captures: the toy write statement: a write to a nonexistent place leaves the value unchanged. Positive example: `writeOrSkip_example_inside`. Negative example: `writeOrSkip_example_skip`.

##### `Head`

```lean
-- lean/ToyMatchGuard/Places.lean:118-122
inductive Head where
  | int (n : Int)
  | ctor (tag : Nat)
  | box
  deriving DecidableEq, Repr
```

Captures: what a switch reads: an integer, a variant index, or "a box".

##### `Val.head`

```lean
-- lean/ToyMatchGuard/Places.lean:125-128
def Val.head : Val → Head
  | .int n => .int n
  | .ctor t _ => .ctor t
  | .box _ => .box
```

Captures: the head of a value.

##### `headAt`

```lean
-- lean/ToyMatchGuard/Places.lean:131-131
def headAt (v : Val) (p : Place) : Option Head := (lookup v p).map Val.head
```

Captures: the head at a place, `none` if the place does not exist. Positive example: `headAt_example`. Negative example: `headAt_example_none`.

#### Matches and the toy lowering

##### `Test`

```lean
-- lean/ToyMatchGuard/Match.lean:21-23
inductive Test where
  | switch (p : Place) (h : Head)
  | derefSwitch (p : Place) (q : Place) (h : Head)
```

Captures: a test node: a switch on a place's head, or a deref-pattern test through the box at a deref-pattern scrutinee (the pointee is not a place the freezing predicates see).

##### `derefHead`

```lean
-- lean/ToyMatchGuard/Match.lean:26-29
def derefHead (v : Val) (p q : Place) : Option Head :=
  match lookup v p with
  | some (.box c) => headAt c q
  | _ => none
```

Captures: the head a deref-pattern test reads.

##### `Test.holds`

```lean
-- lean/ToyMatchGuard/Match.lean:32-34
def Test.holds (v : Val) : Test → Bool
  | .switch p h => decide (headAt v p = some h)
  | .derefSwitch p q h => decide (derefHead v p q = some h)
```

Captures: direct evaluation of a test on a value.

##### `Memo`

```lean
-- lean/ToyMatchGuard/Match.lean:37-37
abbrev Memo := List (Place × Option Head)
```

Captures: recorded switch results.

##### `memoFind`

```lean
-- lean/ToyMatchGuard/Match.lean:40-42
def memoFind : Memo → Place → Option (Option Head)
  | [], _ => none
  | (q, r) :: m, p => if q = p then some r else memoFind m p
```

Captures: the most recent recorded result for a place.

##### `evalTest`

```lean
-- lean/ToyMatchGuard/Match.lean:47-52
def evalTest (v : Val) (m : Memo) : Test → Bool × Memo
  | .switch p h =>
    match memoFind m p with
    | some r => (decide (r = some h), m)
    | none => (decide (headAt v p = some h), (p, headAt v p) :: m)
  | .derefSwitch p q h => (decide (derefHead v p q = some h), m)
```

Captures: lowered evaluation of one test: a switch reuses a recorded result for its place (recorded by any earlier test of any arm); a deref-pattern test always re-reads.

##### `evalTests`

```lean
-- lean/ToyMatchGuard/Match.lean:55-60
def evalTests (v : Val) : Memo → List Test → Bool × Memo
  | m, [] => (true, m)
  | m, t :: ts =>
    match evalTest v m t with
    | (true, m') => evalTests v m' ts
    | (false, m') => (false, m')
```

Captures: lowered evaluation of an arm's tests, stopping at the first failure.

##### `Env`

```lean
-- lean/ToyMatchGuard/Match.lean:64-64
abbrev Env := List (Nat × Option Val)
```

Captures: binding environments (by-value reads of places).

##### `Guard`

```lean
-- lean/ToyMatchGuard/Match.lean:69-71
structure Guard where
  writes : List (Place × (Env → Val → Val))
  cond : Env → Val → Bool
```

Captures: a guard: writes (place, value function of the bindings and the current memory), then a condition.

##### `runWrites`

```lean
-- lean/ToyMatchGuard/Match.lean:74-76
def runWrites (env : Env) : Val → List (Place × (Env → Val → Val)) → Val
  | v, [] => v
  | v, (w, f) :: ws => runWrites env (writeOrSkip v w (f env v)) ws
```

Captures: runs a guard's writes left to right.

##### `Arm`

```lean
-- lean/ToyMatchGuard/Match.lean:79-82
structure Arm where
  tests : List Test
  binds : List (Nat × Place) := []
  guard : Option Guard := none
```

Captures: an arm: tests of an or-free pattern, bindings, optional guard.

##### `bindEnv`

```lean
-- lean/ToyMatchGuard/Match.lean:85-85
def bindEnv (v : Val) (bs : List (Nat × Place)) : Env := bs.map (fun xp => (xp.1, lookup v xp.2))
```

Captures: reads an arm's bindings from memory (used before the guard's writes run).

##### `Outcome`

```lean
-- lean/ToyMatchGuard/Match.lean:89-91
inductive Outcome where
  | arm (index : Nat) (env : Env) (mem : Val)
  | unreachable (mem : Val)
```

Captures: the selected arm (index, bindings, memory after its guard) or `Unreachable` (memory).

##### `Outcome.reachesUnreachable`

```lean
-- lean/ToyMatchGuard/Match.lean:94-96
def Outcome.reachesUnreachable : Outcome → Bool
  | .unreachable _ => true
  | .arm .. => false
```

Captures: whether the lowered match reached `Unreachable`.

##### `Outcome.selected`

```lean
-- lean/ToyMatchGuard/Match.lean:99-101
def Outcome.selected : Outcome → Option Nat
  | .unreachable _ => none
  | .arm i _ _ => some i
```

Captures: the selected arm index, if any.

##### `runArms`

```lean
-- lean/ToyMatchGuard/Match.lean:104-115
def runArms (v : Val) (m : Memo) (i : Nat) : List Arm → Outcome
  | [] => .unreachable v
  | a :: as =>
    match evalTests v m a.tests with
    | (false, m') => runArms v m' (i + 1) as
    | (true, m') =>
      match a.guard with
      | none => .arm i (bindEnv v a.binds) v
      | some g =>
        let env := bindEnv v a.binds
        if g.cond env (runWrites env v g.writes) then .arm i env (runWrites env v g.writes)
        else runArms (runWrites env v g.writes) m' (i + 1) as
```

Captures: the toy lowered decision procedure: arms in order; after a failed guard it continues with the next arm on the memory the guard left.

##### `runMatch`

```lean
-- lean/ToyMatchGuard/Match.lean:118-118
def runMatch (arms : List Arm) (v : Val) : Outcome := runArms v [] 0 arms
```

Captures: the toy lowered execution of a match on scrutinee memory `v`. Examples: `runMatch_reassignArms_none`, `runMatch_laterTestedArms_someFalse`, `runMatch_shallowGuardArms`, `runMatch_sameVariantArms_some0`.

##### `Arm.matchesDirect`

```lean
-- lean/ToyMatchGuard/Match.lean:121-121
def Arm.matchesDirect (v : Val) (a : Arm) : Bool := a.tests.all (Test.holds v)
```

Captures: direct matching of an arm's tests against a value (guards ignored).

##### `Exhaustive`

```lean
-- lean/ToyMatchGuard/Match.lean:126-127
def Exhaustive (Dom : Val → Prop) (arms : List Arm) : Prop :=
  ∀ v, Dom v → ∃ a ∈ arms, a.guard = none ∧ a.matchesDirect v = true
```

Captures: type-level exhaustiveness on a value domain; guarded arms do not count. Positive examples: `reassignArms_exhaustive`, `boxBoolArms_exhaustive`. Negative examples: `reassignArms_take3_not_exhaustive`, `guarded_arm_not_counted`.

##### `Test.switchPlace?`

```lean
-- lean/ToyMatchGuard/Match.lean:130-132
def Test.switchPlace? : Test → Option Place
  | .switch p _ => some p
  | .derefSwitch .. => none
```

Captures: the place a switch test reads.

##### `Test.derefScrutinee?`

```lean
-- lean/ToyMatchGuard/Match.lean:135-137
def Test.derefScrutinee? : Test → Option Place
  | .switch .. => none
  | .derefSwitch p _ _ => some p
```

Captures: the scrutinee of a deref-pattern test.

##### `Arm.switchPlaces`

```lean
-- lean/ToyMatchGuard/Match.lean:140-140
def Arm.switchPlaces (a : Arm) : List Place := a.tests.filterMap Test.switchPlace?
```

Captures: the places an arm switches on.

##### `Arm.derefScrutinees`

```lean
-- lean/ToyMatchGuard/Match.lean:143-143
def Arm.derefScrutinees (a : Arm) : List Place := a.tests.filterMap Test.derefScrutinee?
```

Captures: the deref-pattern scrutinees of an arm.

##### `Arm.guardWrites`

```lean
-- lean/ToyMatchGuard/Match.lean:146-149
def Arm.guardWrites (a : Arm) : List Place :=
  match a.guard with
  | none => []
  | some g => g.writes.map Prod.fst
```

Captures: the places an arm's guard writes.

##### `NoDerefPatterns`

```lean
-- lean/ToyMatchGuard/Match.lean:152-152
def NoDerefPatterns (arms : List Arm) : Prop := ∀ a ∈ arms, a.derefScrutinees = []
```

Captures: no arm has a deref-pattern test. Positive example: `reassignArms_noDerefPatterns`. Negative example: `boxBoolArms_not_noDerefPatterns`.

##### `ShallowConflict`

```lean
-- lean/ToyMatchGuard/Match.lean:156-156
def ShallowConflict (w p : Place) : Prop := w <+: p
```

Captures: a write at `w` conflicts with a shallow freeze of `p` iff `w` is `p` or a prefix of `p`.

##### `DeepConflict`

```lean
-- lean/ToyMatchGuard/Match.lean:160-160
def DeepConflict (w p : Place) : Prop := w <+: p ∨ p <+: w
```

Captures: a write at `w` conflicts with a deep freeze of `p` iff the places overlap (one is a prefix of the other).

##### `ShallowFrozenAll`

```lean
-- lean/ToyMatchGuard/Match.lean:169-170
def ShallowFrozenAll (arms : List Arm) : Prop :=
  ∀ a ∈ arms, ∀ w ∈ a.guardWrites, ∀ b ∈ arms, ∀ p ∈ b.switchPlaces, ¬ ShallowConflict w p
```

Captures: static shallow freezing of every switched place across every guard. Positive example: `shallowGuardArms_shallowFrozenAll`. Negative example: `reassignArms_not_shallowFrozenAll`.

##### `DeepFrozenAll`

```lean
-- lean/ToyMatchGuard/Match.lean:174-175
def DeepFrozenAll (arms : List Arm) : Prop :=
  ∀ a ∈ arms, ∀ w ∈ a.guardWrites, ∀ b ∈ arms, ∀ p ∈ b.derefScrutinees, ¬ DeepConflict w p
```

Captures: static deep freezing of every deref-pattern scrutinee across every guard. Positive example: `pairBoxArms_deepFrozenAll`. Negative example: `boxBoolArms_not_deepFrozenAll`.

##### `ShallowFrozenDerefAll`

```lean
-- lean/ToyMatchGuard/Match.lean:179-180
def ShallowFrozenDerefAll (arms : List Arm) : Prop :=
  ∀ a ∈ arms, ∀ w ∈ a.guardWrites, ∀ b ∈ arms, ∀ p ∈ b.derefScrutinees, ¬ ShallowConflict w p
```

Captures: static shallow freezing of deref-pattern scrutinees (used to show that it is not enough). Positive example: `boxBoolArms_shallowFrozenDerefAll`. Negative example: `reassignBox_not_shallowFrozenDerefAll`.

##### `DeepFrozenSwitchAll`

```lean
-- lean/ToyMatchGuard/Match.lean:183-184
def DeepFrozenSwitchAll (arms : List Arm) : Prop :=
  ∀ a ∈ arms, ∀ w ∈ a.guardWrites, ∀ b ∈ arms, ∀ p ∈ b.switchPlaces, ¬ DeepConflict w p
```

Captures: static deep freezing of switched places (used to compare with shallow freezing). Positive example: `disjointSwitchWriteArms_deepFrozenSwitchAll` (a guard write and switched places, disjoint). Negative example: `shallowGuardArms_not_deepFrozenSwitchAll`.

##### `ShallowFrozenBeforeAux`

```lean
-- lean/ToyMatchGuard/Match.lean:189-193
def ShallowFrozenBeforeAux : List Place → List Arm → Prop
  | _, [] => True
  | seen, a :: as =>
    (∀ w ∈ a.guardWrites, ∀ p ∈ seen ++ a.switchPlaces, ¬ ShallowConflict w p) ∧
      ShallowFrozenBeforeAux (seen ++ a.switchPlaces) as
```

Captures: per-guard shallow freezing given the places switched on by earlier arms.

##### `DeepFrozenBeforeAux`

```lean
-- lean/ToyMatchGuard/Match.lean:196-200
def DeepFrozenBeforeAux : List Place → List Arm → Prop
  | _, [] => True
  | seen, a :: as =>
    (∀ w ∈ a.guardWrites, ∀ p ∈ seen ++ a.derefScrutinees, ¬ DeepConflict w p) ∧
      DeepFrozenBeforeAux (seen ++ a.derefScrutinees) as
```

Captures: per-guard deep freezing given the deref-pattern scrutinees of earlier arms.

##### `ShallowFrozenBefore`

```lean
-- lean/ToyMatchGuard/Match.lean:203-203
def ShallowFrozenBefore (arms : List Arm) : Prop := ShallowFrozenBeforeAux [] arms
```

Captures: each guard is shallow-frozen against the places switched on by its own arm and earlier arms (in arm order); places switched on by later arms are not frozen. Positive example: `laterTestedArms_shallowFrozenBefore`. Negative example: `reassignArms_not_shallowFrozenBefore`.

##### `DeepFrozenBefore`

```lean
-- lean/ToyMatchGuard/Match.lean:206-206
def DeepFrozenBefore (arms : List Arm) : Prop := DeepFrozenBeforeAux [] arms
```

Captures: each guard is deep-frozen against the deref-pattern scrutinees of its own arm and earlier arms. Positive example: `pairBoxArms_deepFrozenBefore`. Negative example: `boxBoolArms_not_deepFrozenBefore`.

##### `GuardsPreserveDom`

```lean
-- lean/ToyMatchGuard/Match.lean:213-215
def GuardsPreserveDom (Dom : Val → Prop) (arms : List Arm) : Prop :=
  ∀ a ∈ arms, ∀ g, a.guard = some g → ∀ v, Dom v → a.matchesDirect v = true →
    Dom (runWrites (bindEnv v a.binds) v g.writes)
```

Captures: well-typed guards: from every memory in `Dom` on which the guarded arm matches directly (whether or not the lowered execution can reach that guard with that memory), the guard's writes give a memory in `Dom`; memories on which the arm does not match are unconstrained. Positive examples: `laterTestedArms_guardsPreserveDom`, `copyBoundFieldArms_guardsPreserveDom_and_unmatched_write_leaves_dom` (a guard that reads its binding). Negative example: `illTypedArms_not_guardsPreserveDom`.

#### Toy borrow check

##### `FakeKind`

```lean
-- lean/ToyMatchGuard/Checker.lean:14-17
inductive FakeKind where
  | shallow
  | deep
  deriving DecidableEq, Repr
```

Captures: the two kinds of fake borrow.

##### `fakeBorrows`

```lean
-- lean/ToyMatchGuard/Checker.lean:21-23
def fakeBorrows (arms : List Arm) : List (Place × FakeKind) :=
  arms.flatMap (fun b => b.switchPlaces.map (fun p => (p, FakeKind.shallow))) ++
    arms.flatMap (fun b => b.derefScrutinees.map (fun p => (p, FakeKind.deep)))
```

Captures: a shallow fake borrow of every switched place and a deep fake borrow of every deref-pattern scrutinee, of every arm (bound places get none).

##### `conflicts`

```lean
-- lean/ToyMatchGuard/Checker.lean:27-29
def conflicts : FakeKind → Place → Place → Bool
  | .shallow, p, w => w.isPrefixOf p
  | .deep, p, w => w.isPrefixOf p || p.isPrefixOf w
```

Captures: conflict of a write with a fake borrow, computed with `List.isPrefixOf`.

##### `borrowck`

```lean
-- lean/ToyMatchGuard/Checker.lean:32-34
def borrowck (arms : List Arm) : Bool :=
  arms.all (fun a => a.guardWrites.all (fun w =>
    (fakeBorrows arms).all (fun pk => !conflicts pk.2 pk.1 w)))
```

Captures: the toy borrow check: no guard write conflicts with any fake borrow. Positive example: `borrowck_shallowGuardArms`. Negative examples: `borrowck_reassignArms`, `borrowck_boxBoolArms`.

#### Value domains and arm lists

##### `OptBoolDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:12-12
def OptBoolDom (v : Val) : Prop := v = vNone ∨ v = vSome vFalse ∨ v = vSome vTrue
```

Captures: the values of `Option<bool>`.

##### `RefOptBoolDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:15-16
def RefOptBoolDom (v : Val) : Prop :=
  v = .box vNone ∨ v = .box (vSome vFalse) ∨ v = .box (vSome vTrue)
```

Captures: the values of `&Option<bool>` (a reference modelled as a box).

##### `BoxBoolDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:19-19
def BoxBoolDom (v : Val) : Prop := v = .box vFalse ∨ v = .box vTrue
```

Captures: the values of `Box<bool>`.

##### `OptIntDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:22-22
def OptIntDom (v : Val) : Prop := v = vNone ∨ ∃ n : Int, v = vSome (.int n)
```

Captures: the values of `Option<i32>` (unbounded integers in the toy).

##### `PairBoxDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:25-26
def PairBoxDom (v : Val) : Prop :=
  ∃ b n, (b = vFalse ∨ b = vTrue) ∧ v = .ctor 0 [.box b, .int n]
```

Captures: the values of `(Box<bool>, i32)`.

##### `PairBoolIntDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:29-30
def PairBoolIntDom (v : Val) : Prop :=
  ∃ b n, (b = vFalse ∨ b = vTrue) ∧ v = .ctor 0 [b, .int n]
```

Captures: the values of `(bool, i32)`.

##### `OptPairBoxBoolDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:33-36
def OptPairBoxBoolDom (v : Val) : Prop :=
  v = vNone ∨
    ∃ b c, (b = vFalse ∨ b = vTrue) ∧ (c = vFalse ∨ c = vTrue) ∧
      v = vSome (.ctor 0 [.box b, c])
```

Captures: the values of `Option<(Box<bool>, bool)>`.

##### `PairOptBoolDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:39-40
def PairOptBoolDom (v : Val) : Prop :=
  ∃ x y, OptBoolDom x ∧ OptBoolDom y ∧ v = .ctor 0 [x, y]
```

Captures: the values of `(Option<bool>, Option<bool>)`.

##### `BoolDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:536-536
def BoolDom (v : Val) : Prop := v = vFalse ∨ v = vTrue
```

Captures: the values of `bool`.

##### `reassignArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:48-53
def reassignArms : List Arm :=
  [ { tests := [.switch [.deref] (.ctor 0)] },
    { tests := [.switch [.deref] (.ctor 1)],
      guard := some { writes := [([], fun _ _ => .box vNone)], cond := fun _ _ => false } },
    { tests := [.switch [.deref] (.ctor 1), .switch [.deref, .field 1 0] (.ctor 1)] },
    { tests := [.switch [.deref] (.ctor 1), .switch [.deref, .field 1 0] (.ctor 0)] } ]
```

Captures: adapted from the E0510 example (rustc's scrutinee type is `&Option<i32>`; here `&Option<bool>`, with the last arm split); the guard reassigns the reference.

##### `boxBoolArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:58-61
def boxBoolArms : List Arm :=
  [ { tests := [.derefSwitch [] [] (.ctor 1)] },
    { tests := [], guard := some { writes := [([.deref], fun _ _ => vTrue)], cond := fun _ _ => false } },
    { tests := [.derefSwitch [] [] (.ctor 0)] } ]
```

Captures: the `Box<bool>` deref-pattern example of the `FakeBorrowKind::Deep` documentation; the guard writes `*b`.

##### `illTypedArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:66-71
def illTypedArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([.field 1 0], fun _ _ => .int 7)], cond := fun _ _ => false } },
    { tests := [.switch [] (.ctor 1), .switch [.field 1 0] (.ctor 1)] },
    { tests := [.switch [] (.ctor 1), .switch [.field 1 0] (.ctor 0)] } ]
```

Captures: a guard writing an integer into a `bool` field that arms after the guard switch on.

##### `laterTestedArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:75-80
def laterTestedArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([.field 1 0], fun _ _ => vTrue)], cond := fun _ _ => false } },
    { tests := [.switch [] (.ctor 1), .switch [.field 1 0] (.ctor 1)] },
    { tests := [.switch [] (.ctor 1), .switch [.field 1 0] (.ctor 0)] } ]
```

Captures: as `illTypedArms` but the guard writes `true`.

##### `incrSomeField`

```lean
-- lean/ToyMatchGuard/Instances.lean:84-88
def incrSomeField (v : Val) : Val :=
  match lookup v [.field 1 0] with
  | some (.int n) => .int (n + 1)
  | some w => w
  | none => .int 0
```

Captures: the value written by `*y += 1` for `y = &mut (x as Some).0`.

##### `shallowGuardArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:94-98
def shallowGuardArms : List Arm :=
  [ { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([.field 1 0], fun _ v => incrSomeField v)],
                      cond := fun _ _ => true } },
    { tests := [] } ]
```

Captures: the allowed example of the `FakeBorrowKind::Shallow` documentation (`Some(_)`, no binding); the guard increments `(x as Some).0`.

##### `pairBoxArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:102-105
def pairBoxArms : List Arm :=
  [ { tests := [.derefSwitch [.field 0 0] [] (.ctor 1)] },
    { tests := [], guard := some { writes := [([.field 0 1], fun _ _ => .int 5)], cond := fun _ _ => false } },
    { tests := [.derefSwitch [.field 0 0] [] (.ctor 0)] } ]
```

Captures: deref patterns on the first field of `(Box<bool>, i32)`; the guard writes the second field.

##### `sameVariantArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:109-113
def sameVariantArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([], fun _ _ => vSome (.int 5))], cond := fun _ _ => false } },
    { tests := [.switch [] (.ctor 1)] } ]
```

Captures: a guard reassigning the scrutinee to a value with the same variant.

##### `disjointSwitchWriteArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:117-121
def disjointSwitchWriteArms : List Arm :=
  [ { tests := [.switch [.field 0 0] (.ctor 1)],
      guard := some { writes := [([.field 0 1], fun _ _ => .int 9)], cond := fun _ _ => false } },
    { tests := [.switch [.field 0 0] (.ctor 1)] },
    { tests := [.switch [.field 0 0] (.ctor 0)] } ]
```

Captures: switches on the first field of `(bool, i32)`; the guard writes the second field.

##### `mixedStaticArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:127-133
def mixedStaticArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1), .derefSwitch [.field 1 0, .field 0 0] [] (.ctor 1)] },
    { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([.field 1 0, .field 0 1], fun _ _ => vTrue)],
                      cond := fun _ _ => false } },
    { tests := [.switch [] (.ctor 1), .derefSwitch [.field 1 0, .field 0 0] [] (.ctor 0)] } ]
```

Captures: switches, deref-pattern tests and a guard write together on `Option<(Box<bool>, bool)>`; the guard writes strictly inside the switched place and disjoint from the deref-pattern scrutinee.

##### `mixedLaterTestedArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:138-147
def mixedLaterTestedArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1), .derefSwitch [.field 1 0, .field 0 0] [] (.ctor 1)] },
    { tests := [.switch [] (.ctor 1)],
      guard := some { writes := [([.field 1 0, .field 0 1], fun _ _ => vTrue)],
                      cond := fun _ _ => false } },
    { tests := [.switch [] (.ctor 1), .derefSwitch [.field 1 0, .field 0 0] [] (.ctor 0),
                .switch [.field 1 0, .field 0 1] (.ctor 1)] },
    { tests := [.switch [] (.ctor 1), .derefSwitch [.field 1 0, .field 0 0] [] (.ctor 0),
                .switch [.field 1 0, .field 0 1] (.ctor 0)] } ]
```

Captures: as `mixedStaticArms`, but the written place is switched on by the two arms after the guard.

##### `writeBoundOptBool`

```lean
-- lean/ToyMatchGuard/Instances.lean:151-154
def writeBoundOptBool (env : Env) (_ : Val) : Val :=
  match env.lookup 0 with
  | some (some b) => vSome b
  | _ => .int (-1)
```

Captures: the value `Some(b)` for the binding `b` named `0` (the integer `-1` if `b` is unbound).

##### `copyBoundFieldArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:159-168
def copyBoundFieldArms : List Arm :=
  [ { tests := [.switch [.field 0 0] (.ctor 0)] },
    { tests := [.switch [.field 0 0] (.ctor 1)],
      binds := [(0, [.field 0 0, .field 1 0])],
      guard := some { writes := [([.field 0 1], writeBoundOptBool)], cond := fun _ _ => false } },
    { tests := [.switch [.field 0 0] (.ctor 1), .switch [.field 0 1] (.ctor 0)] },
    { tests := [.switch [.field 0 0] (.ctor 1), .switch [.field 0 1] (.ctor 1),
                .switch [.field 0 1, .field 1 0] (.ctor 1)] },
    { tests := [.switch [.field 0 0] (.ctor 1), .switch [.field 0 1] (.ctor 1),
                .switch [.field 0 1, .field 1 0] (.ctor 0)] } ]
```

Captures: a guard writing a value computed from its pattern binding into a place switched on by later arms.

##### `missingArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:539-541
def missingArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] },
    { tests := [.switch [] (.ctor 1), .switch [.field 1 0] (.ctor 1)] } ]
```

Captures: a non-exhaustive guard-free match on `Option<bool>` (misses `Some(false)`).

##### `boolArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:544-545
def boolArms : List Arm :=
  [ { tests := [.switch [] (.ctor 0)] }, { tests := [.switch [] (.ctor 1)] } ]
```

Captures: a guard-free exhaustive match on `bool`.

##### `e0510Arms`

```lean
-- lean/ToyMatchGuard/Instances.lean:594-594
def e0510Arms : List Arm := reassignArms.take 3 |>.set 2 { tests := [.switch [.deref] (.ctor 1)] }
```

Captures: the literal (unsplit) E0510 shape.

#### Or-patterns

##### `OrPat.PV`

```lean
-- lean/ToyMatchGuard/OrPat.lean:16-21
inductive PV where
  | int (n : Int)
  | pair (a b : PV)
  | inl (a : PV)
  | inr (a : PV)
  deriving DecidableEq, Repr
```

Captures: values: integers, pairs, two variants.

##### `OrPat.Pat`

```lean
-- lean/ToyMatchGuard/OrPat.lean:25-33
inductive Pat where
  | wild
  | bind (x : Nat)
  | int (n : Int)
  | pair (p q : Pat)
  | inl (p : Pat)
  | inr (p : Pat)
  | or (p q : Pat)
  deriving DecidableEq, Repr
```

Captures: patterns with nested or-patterns (no static well-formedness rules are enforced).

##### `OrPat.Env`

```lean
-- lean/ToyMatchGuard/OrPat.lean:36-36
abbrev Env := List (Nat × PV)
```

Captures: bindings in declaration order of the matched alternative.

##### `OrPat.matchAll`

```lean
-- lean/ToyMatchGuard/OrPat.lean:39-54
def matchAll : Pat → PV → List Env
  | .wild, _ => [[]]
  | .bind x, v => [[(x, v)]]
  | .int n, v => match v with
    | .int m => if n = m then [[]] else []
    | _ => []
  | .pair p q, v => match v with
    | .pair a b => (matchAll p a).flatMap (fun e1 => (matchAll q b).map (fun e2 => e1 ++ e2))
    | _ => []
  | .inl p, v => match v with
    | .inl a => matchAll p a
    | _ => []
  | .inr p, v => match v with
    | .inr a => matchAll p a
    | _ => []
  | .or p q, v => matchAll p v ++ matchAll q v
```

Captures: all matches in left-to-right alternative order. Positive example: `matchAll_example`. Negative example: `matchAll_example_none`.

##### `OrPat.OrFree`

```lean
-- lean/ToyMatchGuard/OrPat.lean:57-61
def OrFree : Pat → Prop
  | .wild | .bind _ | .int _ => True
  | .pair p q => OrFree p ∧ OrFree q
  | .inl p | .inr p => OrFree p
  | .or _ _ => False
```

Captures: no or-pattern inside. Positive example: `orFree_example`. Negative example: `not_orFree_example`.

##### `OrPat.expand`

```lean
-- lean/ToyMatchGuard/OrPat.lean:65-72
def expand : Pat → List Pat
  | .wild => [.wild]
  | .bind x => [.bind x]
  | .int n => [.int n]
  | .pair p q => (expand p).flatMap (fun p' => (expand q).map (fun q' => .pair p' q'))
  | .inl p => (expand p).map .inl
  | .inr p => (expand p).map .inr
  | .or p q => expand p ++ expand q
```

Captures: the or-free alternatives in lexicographic left-to-right order (eager expansion: a tuple of `n` two-way or-patterns has `2^n` alternatives). Positive example: `expand_example`.

##### `OrPat.declOrder`

```lean
-- lean/ToyMatchGuard/OrPat.lean:76-81
def declOrder : Pat → List Nat
  | .wild | .int _ => []
  | .bind x => [x]
  | .pair p q => declOrder p ++ declOrder q
  | .inl p | .inr p => declOrder p
  | .or p _ => declOrder p
```

Captures: declaration order; an or-pattern uses its first alternative. Positive example: `declOrder_example`.

##### `OrPat.Ev`

```lean
-- lean/ToyMatchGuard/OrPat.lean:86-91
inductive Ev where
  | guard (arm : Nat) (env : Env)
  | body (arm : Nat) (env : Env)
  | drop (v : PV)
  | unreachable
  deriving DecidableEq, Repr
```

Captures: observable events: guard evaluations, body runs, destructor runs, `Unreachable`.

##### `OrPat.DropPolicy`

```lean
-- lean/ToyMatchGuard/OrPat.lean:97-100
inductive DropPolicy where
  | firstAlternative
  | matchedAlternative
  deriving DecidableEq, Repr
```

Captures: first-alternative or matched-alternative drop order.

##### `OrPat.dropsInOrder`

```lean
-- lean/ToyMatchGuard/OrPat.lean:103-104
def dropsInOrder (order : List Nat) (e : Env) : List Ev :=
  ((order.filterMap (fun x => e.lookup x)).reverse).map Ev.drop
```

Captures: drops in reverse of a name list, looking each name up in the environment (a name absent from the environment gives no drop; a repeated name gives the first entry each time).

##### `OrPat.dropsMatched`

```lean
-- lean/ToyMatchGuard/OrPat.lean:107-107
def dropsMatched (e : Env) : List Ev := ((e.map Prod.snd).reverse).map Ev.drop
```

Captures: drops in reverse of the environment order.

##### `OrPat.armDrops`

```lean
-- lean/ToyMatchGuard/OrPat.lean:110-112
def armDrops : DropPolicy → Pat → Env → List Ev
  | .firstAlternative, P, e => dropsInOrder (declOrder P) e
  | .matchedAlternative, _, e => dropsMatched e
```

Captures: the drops of an arm under a policy.

##### `OrPat.SArm`

```lean
-- lean/ToyMatchGuard/OrPat.lean:115-117
structure SArm where
  pat : Pat
  guard : Option (Env → Bool) := none
```

Captures: source arm: a pattern and an optional guard reading bindings.

##### `OrPat.tryEnvs`

```lean
-- lean/ToyMatchGuard/OrPat.lean:120-126
def tryEnvs (drops : Env → List Ev) (i : Nat) (g : Option (Env → Bool)) (rest : List Ev) :
    List Env → List Ev
  | [] => rest
  | e :: es =>
    match g with
    | none => .body i e :: drops e
    | some g => .guard i e :: (if g e then .body i e :: drops e else tryEnvs drops i g rest es)
```

Captures: tries one arm's binding environments in order, evaluating the guard for each.

##### `OrPat.runSrc`

```lean
-- lean/ToyMatchGuard/OrPat.lean:130-132
def runSrc (pol : DropPolicy) (v : PV) : Nat → List SArm → List Ev
  | _, [] => [.unreachable]
  | i, a :: as => tryEnvs (armDrops pol a.pat) i a.guard (runSrc pol v (i + 1) as) (matchAll a.pat v)
```

Captures: source semantics.

##### `OrPat.SubBranch`

```lean
-- lean/ToyMatchGuard/OrPat.lean:136-140
structure SubBranch where
  pat : Pat
  guard : Option (Env → Bool)
  arm : Nat
  order : Option (List Nat)
```

Captures: a sub-branch of the split lowering.

##### `OrPat.SubBranch.drops`

```lean
-- lean/ToyMatchGuard/OrPat.lean:143-146
def SubBranch.drops (sb : SubBranch) (e : Env) : List Ev :=
  match sb.order with
  | some order => dropsInOrder order e
  | none => dropsMatched e
```

Captures: the drops of a sub-branch.

##### `OrPat.splitArm`

```lean
-- lean/ToyMatchGuard/OrPat.lean:150-155
def splitArm (pol : DropPolicy) (i : Nat) (a : SArm) : List SubBranch :=
  (expand a.pat).map (fun p' =>
    { pat := p', guard := a.guard, arm := i,
      order := match pol with
        | .firstAlternative => some (declOrder a.pat)
        | .matchedAlternative => none })
```

Captures: splits one arm into one sub-branch per alternative, each with its own guard copy.

##### `OrPat.splitArms`

```lean
-- lean/ToyMatchGuard/OrPat.lean:158-160
def splitArms (pol : DropPolicy) : Nat → List SArm → List SubBranch
  | _, [] => []
  | i, a :: as => splitArm pol i a ++ splitArms pol (i + 1) as
```

Captures: splits all arms.

##### `OrPat.runSplit`

```lean
-- lean/ToyMatchGuard/OrPat.lean:164-172
def runSplit (v : PV) : List SubBranch → List Ev
  | [] => [.unreachable]
  | sb :: sbs =>
    match (matchAll sb.pat v).head? with
    | none => runSplit v sbs
    | some e =>
      match sb.guard with
      | none => .body sb.arm e :: sb.drops e
      | some g => .guard sb.arm e :: (if g e then .body sb.arm e :: sb.drops e else runSplit v sbs)
```

Captures: the split lowering (each sub-branch emits its own body event and drops).

##### `OrPat.runGuardOnce`

```lean
-- lean/ToyMatchGuard/OrPat.lean:176-186
def runGuardOnce (pol : DropPolicy) (v : PV) : Nat → List SArm → List Ev
  | _, [] => [.unreachable]
  | i, a :: as =>
    match matchAll a.pat v with
    | [] => runGuardOnce pol v (i + 1) as
    | e :: _ =>
      match a.guard with
      | none => .body i e :: armDrops pol a.pat e
      | some g =>
        .guard i e :: (if g e then .body i e :: armDrops pol a.pat e
          else runGuardOnce pol v (i + 1) as)
```

Captures: a lowering that evaluates an arm's guard at most once.

##### `OrPat.SameDeclOrder`

```lean
-- lean/ToyMatchGuard/OrPat.lean:190-191
def SameDeclOrder (P : Pat) : Prop :=
  ∀ p' ∈ expand P, declOrder p' = declOrder P
```

Captures: every alternative declares its bindings in the first alternative's order. Positive example: `sameDeclOrder_example`. Negative example: `not_sameDeclOrder_example`.

##### `OrPat.NoDupBindings`

```lean
-- lean/ToyMatchGuard/OrPat.lean:194-195
def NoDupBindings (P : Pat) : Prop :=
  ∀ p' ∈ expand P, (declOrder p').Nodup
```

Captures: no alternative binds a name twice. Positive example: `noDupBindings_example`. Negative example: `not_noDupBindings_example`.

##### `OrPat.bindingGuardArms`

```lean
-- lean/ToyMatchGuard/OrPat.lean:444-447
def bindingGuardArms : List SArm :=
  [ { pat := .or (.pair (.bind 0) .wild) (.pair .wild (.bind 0)),
      guard := some (fun e => decide (e.lookup 0 = some (.int 2))) },
    { pat := .wild } ]
```

Captures: `(x, _) | (_, x) if x == 2 => .., _ => ..` (overlapping alternatives; the guard reads the binding).

##### `OrPat.constGuardArms`

```lean
-- lean/ToyMatchGuard/OrPat.lean:451-453
def constGuardArms : List SArm :=
  [ { pat := .or (.int 1) .wild, guard := some (fun _ => false) },
    { pat := .wild } ]
```

Captures: `1 | _ if <effect; false> => .., _ => ..` (overlapping alternatives; the guard ignores the bindings).

##### `OrPat.refDropArms`

```lean
-- lean/ToyMatchGuard/OrPat.lean:456-457
def refDropArms : List SArm :=
  [ { pat := .or (.inl (.pair (.bind 0) (.bind 1))) (.inr (.pair (.bind 1) (.bind 0))) } ]
```

Captures: `Ok((x, y)) | Err((y, x))`.

##### `OrPat.shadowedSwapArms`

```lean
-- lean/ToyMatchGuard/OrPat.lean:461-462
def shadowedSwapArms : List SArm :=
  [ { pat := .or (.pair (.bind 0) (.bind 1)) (.pair (.bind 1) (.bind 0)) } ]
```

Captures: `(x, y) | (y, x)`, unguarded (the second alternative is never used).

##### `OrPat.okErrGuardArms`

```lean
-- lean/ToyMatchGuard/OrPat.lean:466-469
def okErrGuardArms : List SArm :=
  [ { pat := .or (.inl (.bind 0)) (.inr (.bind 0)),
      guard := some (fun e => decide (e.lookup 0 = some (.int 2))) },
    { pat := .wild } ]
```

Captures: `Ok(x) | Err(x) if x == 2 => .., _ => ..` (mutually exclusive alternatives).

##### `OrPat.dupBindArms`

```lean
-- lean/ToyMatchGuard/OrPat.lean:472-472
def dupBindArms : List SArm := [ { pat := .pair (.bind 0) (.bind 0) } ]
```

Captures: the ill-formed `(x, x)`.

##### `OrPat.unbalancedOrArms`

```lean
-- lean/ToyMatchGuard/OrPat.lean:476-476
def unbalancedOrArms : List SArm := [ { pat := .or (.inl .wild) (.inr (.bind 0)) } ]
```

Captures: the ill-formed `Ok(_) | Err(x)`.

#### Constant patterns

##### `ConstPat.F`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:14-19
inductive F where
  | pzero
  | nzero
  | one
  | nan
  deriving DecidableEq, Repr
```

Captures: toy float payloads (distinct bit patterns).

##### `ConstPat.F.ieeeEq`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:23-28
def F.ieeeEq : F → F → Bool
  | .nan, _ => false
  | _, .nan => false
  | .pzero, .nzero => true
  | .nzero, .pzero => true
  | a, b => decide (a = b)
```

Captures: IEEE-style equality.

##### `ConstPat.CVal`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:31-37
inductive CVal where
  | int (n : Int)
  | flt (f : F)
  | pair (a b : CVal)
  | inl (a : CVal)
  | inr (a : CVal)
  deriving DecidableEq, Repr
```

Captures: canonical value trees.

##### `ConstPat.EqImpl`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:40-42
inductive EqImpl where
  | derived
  | manual (eq : CVal → CVal → Bool)
```

Captures: derived or manual `==` at a node.

##### `ConstPat.CTy`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:46-50
inductive CTy where
  | int
  | flt
  | prod (impl : EqImpl) (A B : CTy)
  | sum (impl : EqImpl) (A B : CTy)
```

Captures: toy types with `==` implementations (every toy type has a value: there is no uninhabited type).

##### `ConstPat.HasTy`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:53-59
def HasTy : CVal → CTy → Prop
  | .int _, .int => True
  | .flt _, .flt => True
  | .pair a b, .prod _ A B => HasTy a A ∧ HasTy b B
  | .inl a, .sum _ A _ => HasTy a A
  | .inr b, .sum _ _ B => HasTy b B
  | _, _ => False
```

Captures: typing. Positive example: `hasTy_example`. Negative example: `not_hasTy_example`.

##### `ConstPat.teq`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:63-71
def teq : CTy → CVal → CVal → Bool
  | .int, .int a, .int b => decide (a = b)
  | .flt, .flt a, .flt b => a.ieeeEq b
  | .prod .derived A B, .pair a1 b1, .pair a2 b2 => teq A a1 a2 && teq B b1 b2
  | .prod (.manual f) _ _, x, y => f x y
  | .sum .derived A _, .inl a1, .inl a2 => teq A a1 a2
  | .sum .derived _ B, .inr b1, .inr b2 => teq B b1 b2
  | .sum (.manual f) _ _, x, y => f x y
  | _, _, _ => false
```

Captures: the type's `==`.

##### `ConstPat.smatch`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:75-81
def smatch : CVal → CVal → Bool
  | .int a, .int b => decide (a = b)
  | .flt a, .flt b => decide (a = b)
  | .pair a1 b1, .pair a2 b2 => smatch a1 a2 && smatch b1 b2
  | .inl a, .inl b => smatch a b
  | .inr a, .inr b => smatch a b
  | _, _ => false
```

Captures: structural lowering of a constant pattern, comparing float leaves by bit pattern. Positive example: `smatch_example`. Negative example: `smatch_example_false`.

##### `ConstPat.AllDerived`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:84-87
def AllDerived : CTy → Prop
  | .int | .flt => True
  | .prod .derived A B | .sum .derived A B => AllDerived A ∧ AllDerived B
  | .prod (.manual _) _ _ | .sum (.manual _) _ _ => False
```

Captures: derived `==` at every struct or enum node of the type (every variant, used or not). Positive example: `allDerived_example`. Negative example: `not_allDerived_example`.

##### `ConstPat.NoFloat`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:90-93
def NoFloat : CTy → Prop
  | .int => True
  | .flt => False
  | .prod _ A B | .sum _ A B => NoFloat A ∧ NoFloat B
```

Captures: no float leaf anywhere in the type. Positive example: `noFloat_example`. Negative example: `not_noFloat_example`.

##### `ConstPat.LoweringAgrees`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:97-97
def LoweringAgrees (T : CTy) : Prop := ∀ c v, HasTy c T → HasTy v T → smatch c v = teq T c v
```

Captures: agreement for every constant and every scrutinee of the type. Positive example: `loweringAgrees_example`. Negative example: `not_loweringAgrees_example`.

##### `ConstPat.inhabit`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:109-113
def inhabit : CTy → CVal
  | .int => .int 0
  | .flt => .flt .pzero
  | .prod _ A B => .pair (inhabit A) (inhabit B)
  | .sum _ A _ => .inl (inhabit A)
```

Captures: a canonical value of each toy type.

##### `ConstPat.HasNan`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:284-288
def HasNan : CVal → Prop
  | .int _ => False
  | .flt f => f = .nan
  | .pair a b => HasNan a ∨ HasNan b
  | .inl a | .inr a => HasNan a
```

Captures: the value tree contains a `nan` leaf.

##### `ConstPat.NoNanNoZeroLeaf`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:291-295
def NoNanNoZeroLeaf : CVal → Prop
  | .int _ => True
  | .flt f => f = .one
  | .pair a b => NoNanNoZeroLeaf a ∧ NoNanNoZeroLeaf b
  | .inl a | .inr a => NoNanNoZeroLeaf a
```

Captures: every float leaf of the value tree is `one`.

##### `ConstPat.flipZeros`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:298-305
def flipZeros : CVal → CVal
  | .int n => .int n
  | .flt .pzero => .flt .nzero
  | .flt .nzero => .flt .pzero
  | .flt f => .flt f
  | .pair a b => .pair (flipZeros a) (flipZeros b)
  | .inl a => .inl (flipZeros a)
  | .inr a => .inr (flipZeros a)
```

Captures: swaps `+0` and `-0` leaves.

##### `ConstPat.payloadEq`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:207-210
def payloadEq : CVal → CVal → Bool
  | .inl (.int a), .inl (.int b) | .inl (.int a), .inr (.int b)
  | .inr (.int a), .inl (.int b) | .inr (.int a), .inr (.int b) => decide (a = b)
  | _, _ => false
```

Captures: a manual `==` ignoring the variant.

##### `ConstPat.manualVariantTy`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:213-213
def manualVariantTy : CTy := .sum (.manual payloadEq) .int .int
```

Captures: a two-variant integer enum with `payloadEq`.

##### `ConstPat.nestedManualTy`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:216-216
def nestedManualTy : CTy := .prod .derived .int manualVariantTy
```

Captures: a derived struct containing `manualVariantTy`.

##### `ConstPat.manualStructuralTy`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:219-219
def manualStructuralTy : CTy := .sum (.manual smatch) .int .int
```

Captures: an enum whose manual `==` is structural.

##### `ConstPat.derivedTy`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:275-275
def derivedTy : CTy := .prod .derived .int (.sum .derived .int .int)
```

Captures: an all-derived float-free type.

#### Accessors

##### `Accessor.Acc`

```lean
-- lean/ToyMatchGuard/Accessor.lean:15-15
abbrev Acc (σ S R : Type) := σ → S → R × σ
```

Captures: accessor: hidden state and scrutinee to result and new hidden state.

##### `Accessor.repeated`

```lean
-- lean/ToyMatchGuard/Accessor.lean:22-25
def repeated (acc : Acc σ S R) (s : S) : List (R → Bool) → Nat → σ → Option Nat × σ
  | [], _, st => (none, st)
  | p :: ps, i, st =>
    if p (acc st s).1 then (some i, (acc st s).2) else repeated acc s ps (i + 1) (acc st s).2
```

Captures: one accessor call per arm test.

##### `Accessor.findFrom`

```lean
-- lean/ToyMatchGuard/Accessor.lean:28-30
def findFrom (r : R) : List (R → Bool) → Nat → Option Nat
  | [], _ => none
  | p :: ps, i => if p r then some i else findFrom r ps (i + 1)
```

Captures: the first arm whose predicate holds.

##### `Accessor.shared`

```lean
-- lean/ToyMatchGuard/Accessor.lean:34-37
def shared (acc : Acc σ S R) (s : S) (arms : List (R → Bool)) (st : σ) : Option Nat × σ :=
  match arms with
  | [] => (none, st)
  | _ :: _ => (findFrom (acc st s).1 arms 0, (acc st s).2)
```

Captures: one accessor call whose result every arm reuses (no call for an empty arm list).

##### `Accessor.ResultStable`

```lean
-- lean/ToyMatchGuard/Accessor.lean:40-40
def ResultStable (acc : Acc σ S R) : Prop := ∀ st s, (acc (acc st s).2 s).1 = (acc st s).1
```

Captures: from every hidden state (reachable or not) and every scrutinee, a second call returns the first call's result. Positive example: `resultStable_example`. Negative example: `not_resultStable_example`.

##### `Accessor.StateIdempotent`

```lean
-- lean/ToyMatchGuard/Accessor.lean:43-43
def StateIdempotent (acc : Acc σ S R) : Prop := ∀ st s, (acc (acc st s).2 s).2 = (acc st s).2
```

Captures: from every hidden state (reachable or not), a second call leaves the state where the first left it. Positive example: `stateIdempotent_example`. Negative example: `not_stateIdempotent_example`.

##### `Accessor.Pure`

```lean
-- lean/ToyMatchGuard/Accessor.lean:46-46
def Pure (acc : Acc σ S R) : Prop := ∀ st s, (acc st s).2 = st ∧ ∀ st', (acc st' s).1 = (acc st s).1
```

Captures: the hidden state never changes and the result does not depend on it. Positive example: `pure_example`. Negative example: `not_pure_example`.

##### `Accessor.WellTyped`

```lean
-- lean/ToyMatchGuard/Accessor.lean:49-49
def WellTyped (RDom : R → Prop) (acc : Acc σ S R) : Prop := ∀ st s, RDom (acc st s).1
```

Captures: every result lies in the result domain. Positive example: `wellTyped_example`. Negative example: `not_wellTyped_example`.

##### `Accessor.ExhaustiveOn`

```lean
-- lean/ToyMatchGuard/Accessor.lean:52-53
def ExhaustiveOn (RDom : R → Prop) (arms : List (R → Bool)) : Prop :=
  ∀ r, RDom r → ∃ p ∈ arms, p r = true
```

Captures: exhaustiveness of arm predicates on the result domain. Positive example: `exhaustiveOn_example`. Negative example: `not_exhaustiveOn_example`.

##### `Accessor.toggleAcc`

```lean
-- lean/ToyMatchGuard/Accessor.lean:188-188
def toggleAcc : Acc Bool Unit Bool := fun st _ => (st, !st)
```

Captures: returns its hidden flag and flips it.

##### `Accessor.countAcc`

```lean
-- lean/ToyMatchGuard/Accessor.lean:191-191
def countAcc : Acc Nat Unit Unit := fun n _ => ((), n + 1)
```

Captures: counts calls; result type `Unit`.

##### `Accessor.flagAcc`

```lean
-- lean/ToyMatchGuard/Accessor.lean:194-194
def flagAcc : Acc Bool Unit Unit := fun _ _ => ((), true)
```

Captures: sets a flag on its first call; result type `Unit`.

##### `Accessor.idAcc`

```lean
-- lean/ToyMatchGuard/Accessor.lean:197-197
def idAcc : Acc Unit Bool Bool := fun st s => (s, st)
```

Captures: returns the scrutinee; pure.

##### `Accessor.constFalseAcc`

```lean
-- lean/ToyMatchGuard/Accessor.lean:200-200
def constFalseAcc : Acc Unit Unit Bool := fun st _ => (false, st)
```

Captures: always returns `false`.

##### `Accessor.boolResultArms`

```lean
-- lean/ToyMatchGuard/Accessor.lean:203-203
def boolResultArms : List (Bool → Bool) := [fun r => r, fun r => !r]
```

Captures: `[true => .., false => ..]`.

##### `Accessor.countedBoolAcc`

```lean
-- lean/ToyMatchGuard/Accessor.lean:269-269
def countedBoolAcc : Acc Nat Bool Bool := fun n s => (s, n + 1)
```

Captures: returns the scrutinee (a `Bool`) and counts calls.

##### `Accessor.loggedBoolAcc`

```lean
-- lean/ToyMatchGuard/Accessor.lean:272-272
def loggedBoolAcc : Acc Bool Bool Bool := fun _ s => (s, true)
```

Captures: returns the scrutinee (a `Bool`) and sets a flag on its first call.

##### `Accessor.twoThenFlipAcc`

```lean
-- lean/ToyMatchGuard/Accessor.lean:295-298
def twoThenFlipAcc : Acc Nat Unit Bool
  | 0, () => (true, 1)
  | 1, () => (true, 2)
  | _, () => (false, 2)
```

Captures: returns `true` from hidden states `0` and `1`, then `false`.

##### `Accessor.threeBoolArms`

```lean
-- lean/ToyMatchGuard/Accessor.lean:301-301
def threeBoolArms : List (Bool → Bool) := [fun r => !r, fun r => !r, fun r => r]
```

Captures: `[false => .., false => .., true => ..]`.

### Cards

Each card gives kind, tier and depth, the plain claim, the verbatim Lean statement, the hypothesis ledger (each `tight` entry names a counterexample theorem in which all other hypotheses hold and the conclusion fails, with the class of that witness), the non-vacuity witness, positive controls where present, prior art and the design question. The non-claims of every card are under **Boundaries**.

#### R1 — `runMatch_not_unreachable_of_exhaustive_of_shallowFrozenAll_of_deepFrozenAll` (theorem)

- **Kind:** theorem. **Tier:** T1 — rustc documents fake borrows for this purpose (`FakeBorrowKind`, `FakeReadCause::ForMatchGuard`, E0510); a mechanized preservation statement over a lowering was not found (novelty search below).
- **Depth:** substantive.

**Plain claim.** For every value domain `Dom`, every arm list `arms` that is exhaustive on `Dom` (`Exhaustive Dom arms`: every value in `Dom` is matched directly by some arm that has no guard), such that no guard write of any arm is to a place switched on by any arm or to a prefix of such a place (`ShallowFrozenAll arms`) and no guard write of any arm is to a place that overlaps a deref-pattern scrutinee of any arm (`DeepFrozenAll arms`), and every `v` in `Dom`, the toy lowered execution `runMatch arms v` does not reach `Unreachable`.

**Statement.**

```lean
-- lean/ToyMatchGuard/Exhaust.lean:260-263
theorem runMatch_not_unreachable_of_exhaustive_of_shallowFrozenAll_of_deepFrozenAll
    (Dom : Val → Prop) (arms : List Arm) (hex : Exhaustive Dom arms)
    (hs : ShallowFrozenAll arms) (hd : DeepFrozenAll arms) (v : Val) (hv : Dom v) :
    (runMatch arms v).reachesUnreachable = false := …
```

Unfolded (prose): with `ShallowConflict w p := w <+: p` and `DeepConflict w p := w <+: p ∨ p <+: w`, the hypotheses say: for every arm `a` whose guard writes a place `w` and every arm `b`, `w` is not a prefix of (or equal to) any place `b` switches on, and `w` is neither a prefix nor an extension of any deref-pattern scrutinee of `b`.

**Hypothesis ledger.**

| Hypothesis | Why | Tightness |
| :--- | :--- | :--- |
| `hex : Exhaustive Dom arms` | type-level exhaustiveness (guarded arms do not count) | tight: counterexample `missingArms_frozen_not_exhaustive_and_reaches_unreachable` (a guard-free arm list with exactly two arms on `Option<bool>`, missing `Some(false)`) |
| `hs : ShallowFrozenAll arms` | switched places keep their heads across every guard | tight: counterexample `reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable` (a deref-free arm list with exactly four arms on `&Option<bool>` whose guard reassigns the reference) |
| `hd : DeepFrozenAll arms` | deref-pattern scrutinees keep their whole value across every guard | tight: counterexample `boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable` (an arm list with exactly three arms on `Box<bool>`, exactly two of them deref-pattern tests, whose guard writes `*b`) |
| `hv : Dom v` | the scrutinee is a value of the type | tight: counterexample `boolArms_exhaustive_frozen_and_reaches_unreachable_outside_dom` (a guard-free arm list with exactly two arms on `bool`, run on the integer `0`) |

**Non-vacuity witness.** `mixedStaticArms` on `Option<(Box<bool>, bool)>` satisfies all hypotheses on an inhabited domain, with a switched place, a deref-pattern scrutinee and a guard write all present; its guard writes strictly inside the switched place `[]` (so `DeepFrozenSwitchAll` fails) and disjoint from the deref-pattern scrutinee. `shallowGuardArms` (adapted from rustc's allowed `Shallow` example) also satisfies them (`shallowGuardArms_satisfy_static_hypotheses`). (`mixedStaticArms_satisfy_static_hypotheses`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R1; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:246-293 (`FakeBorrowKind::{Shallow, Deep}` documentation: the E0510 example `match *x { None => (), Some(_) if { x = &None; false } => (), Some(_) => () }` on `x = &Some(0)` (lines 254-260); the allowed guard that mutates `(x as Some).0` (lines 265-277); the `Box<bool>` deref-pattern example ending "UB because we reached the unreachable" (lines 283-290)) — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:507-519 (`FakeReadCause::ForMatchGuard`: "At the beginning of each match guard, a [fake borrow][FakeBorrowKind] is inserted for each discriminant accessed in the entire `match` statement.") — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:34-68 (`collect_fake_borrows`: places "bound or tested by the match", their prefixes, shallow borrows) and :161-227 (`visit_match_pair`: deep borrow of a deref-pattern scrutinee, shallow borrow of a switched place; `visit_binding`: shallow borrows of the dereference prefixes of bound places) — documentation and source
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:235-275 (match-lowering diagram: decision tree, guard, "(create fake borrows)", otherwise block) and :1643-1671 (exhaustive matches terminate the otherwise block with `TerminatorKind::Unreachable`) — documentation and source
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:1690-1740 and :2232-2270 (the "backtracking automaton" lowering, which may test a place more than once: "Note how we test `x` twice.") — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_error_codes/src/error_codes/E0510.md:1-29 ("The matched value was assigned in a match guard." ... "this could cause the match to be non-exhaustive") — documentation
- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:83-84 ("Each pattern will be tested in left-to-right sequence until a successful match is found."), :142-146 (the guard runs when the pattern matches; "Otherwise, the next pattern, including other matches with the `|` operator in the same arm, is tested."), :159-170 (the guard and its side effects may execute multiple times; `Cell` example), :175-182 (pattern variables are accessed through shared references during the guard; mutation inside guards is prevented) — normative
- Corpus package `place-evaluation-ub-placemention-erasure-inbounds-projections-and-equal-target-switches` (google/zerocopy branch `reference` at 8978e7348aaa6d0808db1d0232d020d053020f4d): `PlaceMention` and the scrutinee read; not repeated here
- Corpus package `two-phase-borrows-reservation-activation-dominator-approximations-and-early-exit-edges` (google/zerocopy branch `reference` at 8978e7348aaa6d0808db1d0232d020d053020f4d): borrow-check approximations; not repeated here
- Corpus packages `enum-niche-layout-guarantees-and-validity-invariants` and `wrapping-niche-intervals-affine-tags-nested-option-capacity-and-discriminant-write-order` (google/zerocopy branch `reference` at 8978e7348aaa6d0808db1d0232d020d053020f4d): how discriminants (the toy's heads) are encoded; not repeated here
- Fabrice Le Fessant and Luc Maranget, "Optimizing Pattern Matching", ICFP 2001, pp. 26–37, DOI 10.1145/507635.507641 (abstract: "improvements to the backtracking technique of pattern-matching compilation") — literature, background on backtracking automata
- Luc Maranget, "Compiling Pattern Matching to Good Decision Trees", ACM SIGPLAN Workshop on ML 2008, pp. 35–46, DOI 10.1145/1411304.1411311 — literature, background on decision-tree compilation
- Luc Maranget, "Warnings for pattern matching", Journal of Functional Programming 17(3), 2007, pp. 387–421, DOI 10.1017/S0956796807006223 — literature, background on deciding whether an ML-style match is exhaustive and whether a clause is useless, including matches with or-patterns (the toy's `Exhaustive` is the type-level fact such a check establishes; the paper's algorithm is not modelled here)
- Thomas Tuerk, Magnus O. Myreen and Ramana Kumar, "Pattern Matches in HOL: A New Representation and Improved Code Generation", ITP 2015 (LNCS), pp. 453–468, DOI 10.1007/978-3-319-22102-1_30 (a HOL4 representation of case expressions that supports guards, used for CakeML code generation) — literature, mechanized pattern matching with guards that do not write the scrutinee
- René Thiemann and Akihisa Yamada, "Verifying a Decision Procedure for Pattern Completeness", Archive of Formal Proofs, 2024-05-27, https://www.isa-afp.org/entries/Pattern_Completeness.html — literature, mechanized pattern completeness
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** Which freezing discipline on guard writes guarantees that a lowered decision procedure reaches an arm whenever the type-level match is exhaustive, and must a place that no test before a guard reads be frozen across that guard?

Basis: execution (Lean kernel check) — `runMatch_not_unreachable_of_exhaustive_of_shallowFrozenAll_of_deepFrozenAll` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R2 — `runMatch_not_unreachable_of_exhaustive_of_guardsPreserveDom_of_frozenBefore` (theorem)

- **Kind:** theorem. **Tier:** T1 — refines the documented static discipline; the per-guard form and its well-typedness hypothesis are made precise here and were not found documented upstream.
- **Depth:** substantive.

**Plain claim.** For every value domain `Dom` and every arm list `arms` that is exhaustive on `Dom`, whose guards keep the memory inside `Dom` when run from any memory in `Dom` on which their arm matches directly, whether or not the lowered execution can reach that guard with that memory (`GuardsPreserveDom Dom arms`), such that each guard writes neither a place switched on by its own arm or by an earlier arm nor a prefix of such a place (`ShallowFrozenBefore arms`) and writes no place overlapping a deref-pattern scrutinee of its own arm or of an earlier arm (`DeepFrozenBefore arms`), and every `v` in `Dom`, `runMatch arms v` does not reach `Unreachable`.

**Statement.**

```lean
-- lean/ToyMatchGuard/Exhaust.lean:370-374
theorem runMatch_not_unreachable_of_exhaustive_of_guardsPreserveDom_of_frozenBefore
    (Dom : Val → Prop) (arms : List Arm) (hex : Exhaustive Dom arms)
    (hdom : GuardsPreserveDom Dom arms) (hs : ShallowFrozenBefore arms)
    (hd : DeepFrozenBefore arms) (v : Val) (hv : Dom v) :
    (runMatch arms v).reachesUnreachable = false := …
```

Unfolded (prose): `ShallowFrozenBefore arms` says that the guard of arm number `k` writes no place that is a prefix of (or equal to) a place switched on by arms `0..k`; `DeepFrozenBefore arms` says the same for overlap with deref-pattern scrutinees of arms `0..k`; places switched on by arms after `k` and by no arm in `0..k` are unconstrained. `GuardsPreserveDom Dom arms` says: for every guarded arm `a` with guard `g` and every `v` with `Dom v` and `a.matchesDirect v = true`, `Dom (runWrites (bindEnv v a.binds) v g.writes)`.

**Hypothesis ledger.**

| Hypothesis | Why | Tightness |
| :--- | :--- | :--- |
| `hex : Exhaustive Dom arms` | type-level exhaustiveness (guarded arms do not count) | tight: counterexample `missingArms_frozen_not_exhaustive_and_reaches_unreachable` (a guard-free arm list with exactly two arms on `Option<bool>`, missing `Some(false)`) |
| `hdom : GuardsPreserveDom Dom arms` | guards are well-typed, so the memory after a guard is again a value of the type | tight: counterexample `illTypedArms_exhaustive_frozenBefore_and_reaches_unreachable` (an arm list with exactly four arms on `Option<bool>` whose guard writes an integer into the `bool` field, which the arms after the guard switch on and no arm up to the guard's own switches on) |
| `hs : ShallowFrozenBefore arms` | places switched on up to a guard keep their heads across it | tight: counterexample `reassignArms_exhaustive_guardsPreserveDom_deepFrozenBefore_and_reaches_unreachable` (the `&Option<bool>` arm list `reassignArms` with exactly four arms, whose well-typed guard reassigns the reference) |
| `hd : DeepFrozenBefore arms` | deref-pattern scrutinees tested up to a guard keep their value across it | tight: counterexample `boxBoolArms_exhaustive_guardsPreserveDom_shallowFrozenBefore_and_reaches_unreachable` (the `Box<bool>` arm list `boxBoolArms` with exactly three arms, whose well-typed guard writes `*b`) |
| `hv : Dom v` | the scrutinee is a value of the type | tight: counterexample `boolArms_exhaustive_frozen_and_reaches_unreachable_outside_dom` (a guard-free arm list with exactly two arms on `bool`, run on the integer `0`) |

**Non-vacuity witness.** `mixedLaterTestedArms` on `Option<(Box<bool>, bool)>` satisfies all hypotheses on an inhabited domain, with a switched place and a deref-pattern scrutinee among the arms up to the guard's own and a guard write present, and violates `ShallowFrozenAll` (its guard writes a place switched on by the arms after it), so R1 does not apply to it. (`mixedLaterTestedArms_satisfy_frozenBefore_hypotheses_and_not_shallowFrozenAll`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R2; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:246-293 (`FakeBorrowKind::{Shallow, Deep}` documentation: the E0510 example `match *x { None => (), Some(_) if { x = &None; false } => (), Some(_) => () }` on `x = &Some(0)` (lines 254-260); the allowed guard that mutates `(x as Some).0` (lines 265-277); the `Box<bool>` deref-pattern example ending "UB because we reached the unreachable" (lines 283-290)) — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:507-519 (`FakeReadCause::ForMatchGuard`: "At the beginning of each match guard, a [fake borrow][FakeBorrowKind] is inserted for each discriminant accessed in the entire `match` statement.") — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:34-68 (`collect_fake_borrows`: places "bound or tested by the match", their prefixes, shallow borrows) and :161-227 (`visit_match_pair`: deep borrow of a deref-pattern scrutinee, shallow borrow of a switched place; `visit_binding`: shallow borrows of the dereference prefixes of bound places) — documentation and source
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:235-275 (match-lowering diagram: decision tree, guard, "(create fake borrows)", otherwise block) and :1643-1671 (exhaustive matches terminate the otherwise block with `TerminatorKind::Unreachable`) — documentation and source
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:1690-1740 and :2232-2270 (the "backtracking automaton" lowering, which may test a place more than once: "Note how we test `x` twice.") — documentation
- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:83-84 ("Each pattern will be tested in left-to-right sequence until a successful match is found."), :142-146 (the guard runs when the pattern matches; "Otherwise, the next pattern, including other matches with the `|` operator in the same arm, is tested."), :159-170 (the guard and its side effects may execute multiple times; `Cell` example), :175-182 (pattern variables are accessed through shared references during the guard; mutation inside guards is prevented) — normative
- Corpus package `two-phase-borrows-reservation-activation-dominator-approximations-and-early-exit-edges` (google/zerocopy branch `reference` at 8978e7348aaa6d0808db1d0232d020d053020f4d): borrow-check approximations; not repeated here
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** Which freezing discipline on guard writes guarantees that a lowered decision procedure reaches an arm whenever the type-level match is exhaustive, and must a place that no test before a guard reads be frozen across that guard?

Basis: execution (Lean kernel check) — `runMatch_not_unreachable_of_exhaustive_of_guardsPreserveDom_of_frozenBefore` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R3 — `reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable` (counterexample)

- **Kind:** counterexample. **Tier:** T1 — adapted from rustc's documented E0510 example (which rustc rejects).
- **Depth:** definitional.

**Plain claim.** There is a deref-free arm list, `reassignArms` (on `x : &Option<bool>`: `match *x { None, Some(_) if { x = &None; false }, Some(true), Some(false) }`, adapted from rustc's E0510 example on `&Option<i32>` with its last arm split), that is exhaustive on `RefOptBoolDom`, satisfies `DeepFrozenAll` (vacuously: it has no deref-pattern test), violates `ShallowFrozenAll` (its guard writes `x`, a prefix of the switched place `*x`), and whose lowered execution on `&Some(true)` reaches `Unreachable`.

**Statement.**

```lean
-- lean/ToyMatchGuard/Instances.lean:416-420
theorem reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable :
    NoDerefPatterns reassignArms ∧ Exhaustive RefOptBoolDom reassignArms ∧
      DeepFrozenAll reassignArms ∧ ¬ ShallowFrozenAll reassignArms ∧
      RefOptBoolDom (.box (vSome vTrue)) ∧
      (runMatch reassignArms (.box (vSome vTrue))).reachesUnreachable = true := …
```

**Hypothesis ledger.** No hypotheses: the statement is a concrete instance.

**Non-vacuity witness.** The statement is itself a concrete instance (`reassignArms`, value `&Some(true)`). (`reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R3; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:246-293 (`FakeBorrowKind::{Shallow, Deep}` documentation: the E0510 example `match *x { None => (), Some(_) if { x = &None; false } => (), Some(_) => () }` on `x = &Some(0)` (lines 254-260); the allowed guard that mutates `(x as Some).0` (lines 265-277); the `Box<bool>` deref-pattern example ending "UB because we reached the unreachable" (lines 283-290)) — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_error_codes/src/error_codes/E0510.md:1-29 ("The matched value was assigned in a match guard." ... "this could cause the match to be non-exhaustive") — documentation

**Design question.** Which freezing discipline on guard writes guarantees that a lowered decision procedure reaches an arm whenever the type-level match is exhaustive, and must a place that no test before a guard reads be frozen across that guard?

Basis: execution (Lean kernel check) — `reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R4 — `boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable` (counterexample)

- **Kind:** counterexample. **Tier:** T1 — toy form of the example in rustc's `FakeBorrowKind::Deep` documentation.
- **Depth:** definitional.

**Plain claim.** There is an arm list, `boxBoolArms` (on `b : Box<bool>`: `match b { deref!(true), _ if { *b = true; false }, deref!(false) }`), that is exhaustive on `BoxBoolDom`, satisfies `ShallowFrozenAll` and shallow freezing of its deref-pattern scrutinee (`ShallowFrozenDerefAll`), violates `DeepFrozenAll`, and whose lowered execution on `Box(false)` reaches `Unreachable`.

**Statement.**

```lean
-- lean/ToyMatchGuard/Instances.lean:438-442
theorem boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable :
    Exhaustive BoxBoolDom boxBoolArms ∧ ShallowFrozenAll boxBoolArms ∧
      ShallowFrozenDerefAll boxBoolArms ∧ ¬ DeepFrozenAll boxBoolArms ∧
      BoxBoolDom (.box vFalse) ∧
      (runMatch boxBoolArms (.box vFalse)).reachesUnreachable = true := …
```

**Hypothesis ledger.** No hypotheses: the statement is a concrete instance.

**Non-vacuity witness.** The statement is itself a concrete instance (`boxBoolArms`, value `Box(false)`). (`boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R4; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:246-293 (`FakeBorrowKind::{Shallow, Deep}` documentation: the E0510 example `match *x { None => (), Some(_) if { x = &None; false } => (), Some(_) => () }` on `x = &Some(0)` (lines 254-260); the allowed guard that mutates `(x as Some).0` (lines 265-277); the `Box<bool>` deref-pattern example ending "UB because we reached the unreachable" (lines 283-290)) — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:34-68 (`collect_fake_borrows`: places "bound or tested by the match", their prefixes, shallow borrows) and :161-227 (`visit_match_pair`: deep borrow of a deref-pattern scrutinee, shallow borrow of a switched place; `visit_binding`: shallow borrows of the dereference prefixes of bound places) — documentation and source
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:src/doc/unstable-book/src/language-features/deref-patterns.md:1-13 (the unstable `deref_patterns` feature: matching through `Deref` targets with `deref!(_)` patterns) and rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:1342-1347 (`TestKind::Deref`: "Call `Deref::deref[_mut]` on the value.", result stored in a temporary) — documentation of an unstable feature

**Design question.** Why are shallow fake borrows insufficient for deref-pattern scrutinees, and is shallow freezing enough for every other pattern shape of the toy?

Basis: execution (Lean kernel check) — `boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R5 — `runMatch_not_unreachable_of_noDerefPatterns_of_exhaustive_of_shallowFrozenAll` (theorem)

- **Kind:** theorem. **Tier:** T1 — documented design (shallow fake borrows for switched places); here a corollary of R1.
- **Depth:** shallow.

**Plain claim.** For every value domain `Dom` and every arm list `arms` with no deref-pattern test (`NoDerefPatterns arms`) that is exhaustive on `Dom`, such that no guard write of any arm is to a place switched on by any arm or to a prefix of such a place (`ShallowFrozenAll arms`), and every `v` in `Dom`, `runMatch arms v` does not reach `Unreachable`.

**Statement.**

```lean
-- lean/ToyMatchGuard/Exhaust.lean:391-394
theorem runMatch_not_unreachable_of_noDerefPatterns_of_exhaustive_of_shallowFrozenAll
    (Dom : Val → Prop) (arms : List Arm) (hnd : NoDerefPatterns arms)
    (hex : Exhaustive Dom arms) (hs : ShallowFrozenAll arms) (v : Val) (hv : Dom v) :
    (runMatch arms v).reachesUnreachable = false := …
```

**Hypothesis ledger.**

| Hypothesis | Why | Tightness |
| :--- | :--- | :--- |
| `hnd : NoDerefPatterns arms` | without deref-pattern tests, `DeepFrozenAll` holds vacuously | tight: counterexample `boxBoolArms_not_noDerefPatterns_exhaustive_shallowFrozenAll_and_reaches_unreachable` (the `Box<bool>` deref-pattern arm list `boxBoolArms` with exactly three arms) |
| `hex : Exhaustive Dom arms` | type-level exhaustiveness (guarded arms do not count) | tight: counterexample `missingArms_frozen_not_exhaustive_and_reaches_unreachable` (a guard-free arm list with exactly two arms on `Option<bool>`, missing `Some(false)`) |
| `hs : ShallowFrozenAll arms` | switched places keep their heads across every guard | tight: counterexample `reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable` (the deref-free `&Option<bool>` arm list `reassignArms` with exactly four arms) |
| `hv : Dom v` | the scrutinee is a value of the type | tight: counterexample `boolArms_exhaustive_frozen_and_reaches_unreachable_outside_dom` (a guard-free arm list with exactly two arms on `bool`, run on the integer `0`) |

**Non-vacuity witness.** `shallowGuardArms` (deref-free; adapted from rustc's allowed `Shallow` example: `match x { Some(_) if { if let Some(ref mut y) = x { *y += 1 }; true } => {}, _ => {} }` on `x : Option<i32>`) satisfies all hypotheses on `OptIntDom`, with a switched place and a guard write present; its guard writes strictly inside the switched place. (`shallowGuardArms_satisfy_static_hypotheses`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R5; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:246-293 (`FakeBorrowKind::{Shallow, Deep}` documentation: the E0510 example `match *x { None => (), Some(_) if { x = &None; false } => (), Some(_) => () }` on `x = &Some(0)` (lines 254-260); the allowed guard that mutates `(x as Some).0` (lines 265-277); the `Box<bool>` deref-pattern example ending "UB because we reached the unreachable" (lines 283-290)) — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:34-68 (`collect_fake_borrows`: places "bound or tested by the match", their prefixes, shallow borrows) and :161-227 (`visit_match_pair`: deep borrow of a deref-pattern scrutinee, shallow borrow of a switched place; `visit_binding`: shallow borrows of the dereference prefixes of bound places) — documentation and source
- Luc Maranget, "Warnings for pattern matching", Journal of Functional Programming 17(3), 2007, pp. 387–421, DOI 10.1017/S0956796807006223 — literature, background on deciding whether an ML-style match is exhaustive and whether a clause is useless, including matches with or-patterns (the toy's `Exhaustive` is the type-level fact such a check establishes; the paper's algorithm is not modelled here)
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** Why are shallow fake borrows insufficient for deref-pattern scrutinees, and is shallow freezing enough for every other pattern shape of the toy?

Basis: execution (Lean kernel check) — `runMatch_not_unreachable_of_noDerefPatterns_of_exhaustive_of_shallowFrozenAll` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R6 — `shallowFrozenAll_of_deepFrozenSwitchAll_strict_on_shallowGuardArms` (theorem)

- **Kind:** theorem. **Tier:** T0 — rustc's `Shallow` documentation states why a deep (shared) borrow of the switched place would be too strict and gives the allowed example (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:262-277`); restated in the toy's vocabulary. Kept as a reference point for R5.
- **Depth:** definitional.

**Plain claim.** For every arm list `arms`, if no guard write of any arm overlaps a place switched on by any arm (`DeepFrozenSwitchAll arms`), then `ShallowFrozenAll arms`; and there is a deref-free arm list exhaustive on `OptIntDom`, namely `shallowGuardArms` (adapted from the allowed example in rustc's `FakeBorrowKind::Shallow` documentation), that satisfies `ShallowFrozenAll` and violates `DeepFrozenSwitchAll`.

**Statement.**

```lean
-- lean/ToyMatchGuard/Instances.lean:526-529
theorem shallowFrozenAll_of_deepFrozenSwitchAll_strict_on_shallowGuardArms :
    (∀ arms, DeepFrozenSwitchAll arms → ShallowFrozenAll arms) ∧
      NoDerefPatterns shallowGuardArms ∧ Exhaustive OptIntDom shallowGuardArms ∧
      ShallowFrozenAll shallowGuardArms ∧ ¬ DeepFrozenSwitchAll shallowGuardArms := …
```

**Hypothesis ledger.** No hypotheses: the statement is unconditional (the premise `DeepFrozenSwitchAll arms` of its first conjunct is quantified inside the statement).

**Non-vacuity witness.** The premise of the first conjunct holds non-vacuously for `disjointSwitchWriteArms` on `(bool, i32)`, which has a guard write and switched places, with the write disjoint from every switched place. (`disjointSwitchWriteArms_deepFrozenSwitchAll`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R6; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:246-293 (`FakeBorrowKind::{Shallow, Deep}` documentation: the E0510 example `match *x { None => (), Some(_) if { x = &None; false } => (), Some(_) => () }` on `x = &Some(0)` (lines 254-260); the allowed guard that mutates `(x as Some).0` (lines 265-277); the `Box<bool>` deref-pattern example ending "UB because we reached the unreachable" (lines 283-290)) — documentation

**Design question.** Why are shallow fake borrows insufficient for deref-pattern scrutinees, and is shallow freezing enough for every other pattern shape of the toy? (reference point: deep freezing of switched places would reject the documented allowed guard.)

Basis: execution (Lean kernel check) — `shallowFrozenAll_of_deepFrozenSwitchAll_strict_on_shallowGuardArms` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R7 — `borrowck_eq_true_iff` (characterization)

- **Kind:** characterization. **Tier:** T0 — a Boolean reflection of the toy check `borrowck` (defined in the same file) onto the freezing predicates; kept as the backing equivalence of R8.
- **Depth:** definitional.

**Plain claim.** For every arm list `arms`, the toy borrow check `borrowck arms`, which tests every guard write against a shallow fake borrow of every switched place and a deep fake borrow of every deref-pattern scrutinee (`fakeBorrows arms`), returns `true` iff `ShallowFrozenAll arms` and `DeepFrozenAll arms`.

**Statement.**

```lean
-- lean/ToyMatchGuard/Checker.lean:46-47
theorem borrowck_eq_true_iff (arms : List Arm) :
    borrowck arms = true ↔ ShallowFrozenAll arms ∧ DeepFrozenAll arms := …
```

**Hypothesis ledger.** No hypotheses: the statement is an unconditional equivalence.

**Non-vacuity witness.** `mixedStaticArms` is accepted, with a shallow and a deep fake borrow and a guard write present (`borrowck_reassignArms` and `borrowck_boxBoolArms` are rejected instances). (`mixedStaticArms_accepted_exhaustive`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R7; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:246-293 (`FakeBorrowKind::{Shallow, Deep}` documentation: the E0510 example `match *x { None => (), Some(_) if { x = &None; false } => (), Some(_) => () }` on `x = &Some(0)` (lines 254-260); the allowed guard that mutates `(x as Some).0` (lines 265-277); the `Box<bool>` deref-pattern example ending "UB because we reached the unreachable" (lines 283-290)) — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:507-519 (`FakeReadCause::ForMatchGuard`: "At the beginning of each match guard, a [fake borrow][FakeBorrowKind] is inserted for each discriminant accessed in the entire `match` statement.") — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:34-68 (`collect_fake_borrows`: places "bound or tested by the match", their prefixes, shallow borrows) and :161-227 (`visit_match_pair`: deep borrow of a deref-pattern scrutinee, shallow borrow of a switched place; `visit_binding`: shallow borrows of the dereference prefixes of bound places) — documentation and source

**Design question.** Is a syntactic fake-borrow check on guard writes a sound (and how incomplete) approximation of exhaustiveness preservation?

Basis: execution (Lean kernel check) — `borrowck_eq_true_iff` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R8 — `runMatch_not_unreachable_of_borrowck_of_exhaustive` (theorem)

- **Kind:** theorem. **Tier:** T1 — the toy check mirrors documented fake-borrow placement; corollary of R1 and R7.
- **Depth:** shallow.

**Plain claim.** For every value domain `Dom`, every arm list `arms` accepted by the toy borrow check (`borrowck arms = true`) and exhaustive on `Dom`, and every `v` in `Dom`, `runMatch arms v` does not reach `Unreachable`.

**Statement.**

```lean
-- lean/ToyMatchGuard/Checker.lean:73-75
theorem runMatch_not_unreachable_of_borrowck_of_exhaustive (Dom : Val → Prop) (arms : List Arm)
    (hck : borrowck arms = true) (hex : Exhaustive Dom arms) (v : Val) (hv : Dom v) :
    (runMatch arms v).reachesUnreachable = false := …
```

**Hypothesis ledger.**

| Hypothesis | Why | Tightness |
| :--- | :--- | :--- |
| `hck : borrowck arms = true` | acceptance by the toy check | tight: counterexample `reassignArms_rejected_exhaustive_and_reaches_unreachable` (the rejected `&Option<bool>` arm list `reassignArms` with exactly four arms) |
| `hex : Exhaustive Dom arms` | type-level exhaustiveness | tight: counterexample `missingArms_accepted_and_reaches_unreachable` (an accepted guard-free arm list with exactly two arms on `Option<bool>`, missing `Some(false)`) |
| `hv : Dom v` | the scrutinee is a value of the type | tight: counterexample `boolArms_accepted_and_reaches_unreachable_outside_dom` (an accepted guard-free arm list with exactly two arms on `bool`, run on the integer `0`) |

**Non-vacuity witness.** `mixedStaticArms` is accepted by `borrowck` and is exhaustive on the inhabited domain `OptPairBoxBoolDom`; its fake borrows include a shallow borrow of `[]` and a deep borrow of `[.field 1 0, .field 0 0]`, and its guard writes `[.field 1 0, .field 0 1]`. (`mixedStaticArms_accepted_exhaustive`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R8; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:246-293 (`FakeBorrowKind::{Shallow, Deep}` documentation: the E0510 example `match *x { None => (), Some(_) if { x = &None; false } => (), Some(_) => () }` on `x = &Some(0)` (lines 254-260); the allowed guard that mutates `(x as Some).0` (lines 265-277); the `Box<bool>` deref-pattern example ending "UB because we reached the unreachable" (lines 283-290)) — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:507-519 (`FakeReadCause::ForMatchGuard`: "At the beginning of each match guard, a [fake borrow][FakeBorrowKind] is inserted for each discriminant accessed in the entire `match` statement.") — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:34-68 (`collect_fake_borrows`: places "bound or tested by the match", their prefixes, shallow borrows) and :161-227 (`visit_match_pair`: deep borrow of a deref-pattern scrutinee, shallow borrow of a switched place; `visit_binding`: shallow borrows of the dereference prefixes of bound places) — documentation and source
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:235-275 (match-lowering diagram: decision tree, guard, "(create fake borrows)", otherwise block) and :1643-1671 (exhaustive matches terminate the otherwise block with `TerminatorKind::Unreachable`) — documentation and source
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** Is a syntactic fake-borrow check on guard writes a sound (and how incomplete) approximation of exhaustiveness preservation?

Basis: execution (Lean kernel check) — `runMatch_not_unreachable_of_borrowck_of_exhaustive` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R9 — `sameVariantArms_rejected_exhaustive_and_never_unreachable` (counterexample)

- **Kind:** counterexample. **Tier:** T1 — E0510's documentation forbids mutating a matched variable in a guard because it "could cause the match to be non-exhaustive" (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_error_codes/src/error_codes/E0510.md:14-15`); that the toy check also rejects a guard write that keeps every test outcome is made precise here.
- **Depth:** shallow.

**Plain claim.** There is an arm list, `sameVariantArms` (on `x : Option<i32>`: `match x { None, Some(_) if { x = Some(5); false }, Some(_) }`), that `borrowck` rejects, that is exhaustive on `OptIntDom`, and whose lowered execution reaches no `Unreachable` on any value of `OptIntDom` (every test of `sameVariantArms` reads the variant at `[]`, and its guard writes a value with the same variant).

**Statement.**

```lean
-- lean/ToyMatchGuard/Checker.lean:93-95
theorem sameVariantArms_rejected_exhaustive_and_never_unreachable :
    borrowck sameVariantArms = false ∧ Exhaustive OptIntDom sameVariantArms ∧
      ∀ v, OptIntDom v → (runMatch sameVariantArms v).reachesUnreachable = false := …
```

**Hypothesis ledger.** No hypotheses: the statement is a concrete instance, quantified over every value of `OptIntDom`.

**Non-vacuity witness.** The statement is itself a concrete instance, over the infinite domain `OptIntDom`. (`sameVariantArms_rejected_exhaustive_and_never_unreachable`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R9; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_error_codes/src/error_codes/E0510.md:1-29 ("The matched value was assigned in a match guard." ... "this could cause the match to be non-exhaustive") — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:246-293 (`FakeBorrowKind::{Shallow, Deep}` documentation: the E0510 example `match *x { None => (), Some(_) if { x = &None; false } => (), Some(_) => () }` on `x = &Some(0)` (lines 254-260); the allowed guard that mutates `(x as Some).0` (lines 265-277); the `Box<bool>` deref-pattern example ending "UB because we reached the unreachable" (lines 283-290)) — documentation

**Design question.** Is a syntactic fake-borrow check on guard writes a sound (and how incomplete) approximation of exhaustiveness preservation?

Basis: execution (Lean kernel check) — `sameVariantArms_rejected_exhaustive_and_never_unreachable` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R10 — `OrPat.runSrc_eq_runSplit_splitArms` (theorem)

- **Kind:** theorem. **Tier:** T1 — the Reference documents per-alternative guard evaluation and rustc documents per-sub-branch guard copies; the trace equivalence with a drop-order policy was not found mechanized (novelty search below).
- **Depth:** substantive.

**Plain claim.** For every drop policy `pol`, every value `v`, every arm list `arms` (patterns may contain nested or-patterns and are not required to be well-formed; guards may read bindings) and every starting arm index `i`, the source semantics `runSrc pol v i arms`, which evaluates an arm's guard once for each matching alternative with that alternative's bindings, produces the same event trace as the split lowering `runSplit v (splitArms pol i arms)`, whose sub-branches each carry their own copy of the guard and the policy's drop order.

**Statement.**

```lean
-- lean/ToyMatchGuard/OrPat.lean:340-341
theorem runSrc_eq_runSplit_splitArms (pol : DropPolicy) (v : PV) :
    ∀ (arms : List SArm) (i : Nat), runSrc pol v i arms = runSplit v (splitArms pol i arms) := …
```

**Hypothesis ledger.** No hypotheses: the statement is unconditional.

**Non-vacuity witness.** An instance in which the source trace evaluates the guard exactly twice with different bindings before running a body: `bindingGuardArms` on `(1, 2)`, whose source trace `runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms` spells out (R10 equates it with the split trace). (`OrPat.runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R10; they are part of this card.

**Prior art.**

- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:83-84 (left-to-right testing of `|` alternatives), :96-102 (the example `S(z @ 1, _) | S(_, z @ 2) => assert_eq!(z, 1)`), :142-146 (after a failed guard "the next pattern, including other matches with the `|` operator in the same arm, is tested"), :159-170 ("Multiple matches using the `|` operator can cause the pattern guard and the side effects it has to execute multiple times.") — normative
- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:1016-1046 (or-patterns: static semantics, including that "the same set of bindings" must be introduced in `p` and `q` (lines 1024-1031); dynamic semantics of `c(p | q, ..rest)` as `c(p, ..rest) | c(q, ..rest)` (lines 1044-1045)) and :175-176 ("The identifier must be unique within the pattern.") — normative
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:509-513 (sub-branches "with each sub-branch requiring its own bindings and its own copy of the guard", which "jump together to a common block") and :2094-2149 (`test_remaining_match_pairs_after_or`: remaining or-patterns are tested after each sub-candidate, avoiding "exponentially large CFGs") — documentation and source
- rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07:text/2535-or-patterns.md:620-624 (dynamic semantics of nested or-patterns) and :628-664 (DNF expansion and its multiplicative blow-up) — RFC (design document)
- Fabrice Le Fessant and Luc Maranget, "Optimizing Pattern Matching", ICFP 2001, pp. 26–37, DOI 10.1145/507635.507641 (abstract: "improvements to the backtracking technique of pattern-matching compilation") — literature, background on backtracking automata
- Luc Maranget, "Compiling Pattern Matching to Good Decision Trees", ACM SIGPLAN Workshop on ML 2008, pp. 35–46, DOI 10.1145/1411304.1411311 — literature, background on decision-tree compilation
- Luc Maranget, "Warnings for pattern matching", Journal of Functional Programming 17(3), 2007, pp. 387–421, DOI 10.1017/S0956796807006223 — literature, background on deciding whether an ML-style match is exhaustive and whether a clause is useless, including matches with or-patterns (the toy's `Exhaustive` is the type-level fact such a check establishes; the paper's algorithm is not modelled here)
- Thomas Tuerk, Magnus O. Myreen and Ramana Kumar, "Pattern Matches in HOL: A New Representation and Improved Code Generation", ITP 2015 (LNCS), pp. 453–468, DOI 10.1007/978-3-319-22102-1_30 (a HOL4 representation of case expressions that supports guards, used for CakeML code generation) — literature, mechanized pattern matching with guards that do not write the scrutinee
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** How do or-patterns with guards lower soundly to sub-branches, how often is the guard evaluated, and with which binding drop order?

Basis: execution (Lean kernel check) — `OrPat.runSrc_eq_runSplit_splitArms` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R11 — `OrPat.runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms` (counterexample)

- **Kind:** counterexample. **Tier:** T1 — the Reference's note that the guard may execute multiple times, made precise as two trace counterexamples against a guard-once lowering.
- **Depth:** definitional.

**Plain claim.** For every drop policy `pol`: on `(1, 2)`, for `bindingGuardArms` (`(x, _) | (_, x) if x == 2 => .., _ => ..`, whose guard reads its binding), the source semantics evaluates the guard with `x = 1`, then with `x = 2`, runs the body of arm `0` with `x = 2` and drops `2`, while the guard-once lowering `runGuardOnce` evaluates the guard exactly once (with `x = 1`) and runs the body of arm `1`; and on `1`, for `constGuardArms` (`1 | _ if { effect; false } => .., _ => ..`, whose guard returns `false` for every binding environment), the source semantics evaluates the guard exactly twice and the guard-once lowering exactly once, both then running the body of arm `1`. In both cases the two traces differ.

**Statement.**

```lean
-- lean/ToyMatchGuard/OrPat.lean:485-495
theorem runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms (pol : DropPolicy) :
    runSrc pol (.pair (.int 1) (.int 2)) 0 bindingGuardArms =
        [.guard 0 [(0, .int 1)], .guard 0 [(0, .int 2)], .body 0 [(0, .int 2)], .drop (.int 2)] ∧
      runGuardOnce pol (.pair (.int 1) (.int 2)) 0 bindingGuardArms =
        [.guard 0 [(0, .int 1)], .body 1 []] ∧
      runGuardOnce pol (.pair (.int 1) (.int 2)) 0 bindingGuardArms ≠
        runSrc pol (.pair (.int 1) (.int 2)) 0 bindingGuardArms ∧
      (∃ g, constGuardArms[0].guard = some g ∧ ∀ e, g e = false) ∧
      runSrc pol (.int 1) 0 constGuardArms = [.guard 0 [], .guard 0 [], .body 1 []] ∧
      runGuardOnce pol (.int 1) 0 constGuardArms = [.guard 0 [], .body 1 []] ∧
      runGuardOnce pol (.int 1) 0 constGuardArms ≠ runSrc pol (.int 1) 0 constGuardArms := …
```

**Hypothesis ledger.** No hypotheses: the statement is a concrete instance for each drop policy.

**Non-vacuity witness.** The statement is itself a concrete instance (two arm lists, two values, both drop policies). (`OrPat.runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms`)

**Positive control.** When every arm's pattern matches the value in at most one way, the guard-once lowering produces the same trace as the source semantics, even for guards that read bindings (`runGuardOnce_eq_runSrc_of_matchAll_length_le_one`); this holds on every value for the mutually exclusive alternatives `Ok(x) | Err(x)` of `okErrGuardArms` (`okErrGuardArms_matchAll_length_le_one`).

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R11; they are part of this card.

**Prior art.**

- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:83-84 (left-to-right testing of `|` alternatives), :96-102 (the example `S(z @ 1, _) | S(_, z @ 2) => assert_eq!(z, 1)`), :142-146 (after a failed guard "the next pattern, including other matches with the `|` operator in the same arm, is tested"), :159-170 ("Multiple matches using the `|` operator can cause the pattern guard and the side effects it has to execute multiple times.") — normative
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:509-513 (sub-branches "with each sub-branch requiring its own bindings and its own copy of the guard", which "jump together to a common block") and :2094-2149 (`test_remaining_match_pairs_after_or`: remaining or-patterns are tested after each sub-candidate, avoiding "exponentially large CFGs") — documentation and source

**Design question.** How do or-patterns with guards lower soundly to sub-branches, how often is the guard evaluated, and with which binding drop order?

Basis: execution (Lean kernel check) — `OrPat.runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R12 — `OrPat.runSrc_firstAlternative_eq_matchedAlternative_of_noDupBindings_of_sameDeclOrder` (theorem)

- **Kind:** theorem. **Tier:** T1 — the Reference fixes the first-subpattern drop order; when the matched-alternative order coincides with it is made precise here.
- **Depth:** substantive.

**Plain claim.** For every value `v`, every arm list `arms` and every arm index `i` such that no alternative of any arm's pattern binds a name twice (`NoDupBindings`) and every alternative of every arm's pattern declares its bindings in the order of that pattern's first alternative (`SameDeclOrder`), the source traces under the `firstAlternative` and `matchedAlternative` drop policies are equal.

**Statement.**

```lean
-- lean/ToyMatchGuard/OrPat.lean:409-412
theorem runSrc_firstAlternative_eq_matchedAlternative_of_noDupBindings_of_sameDeclOrder (v : PV) :
    ∀ (arms : List SArm) (i : Nat), (∀ a ∈ arms, NoDupBindings a.pat) →
      (∀ a ∈ arms, SameDeclOrder a.pat) →
      runSrc .firstAlternative v i arms = runSrc .matchedAlternative v i arms := …
```

**Hypothesis ledger.**

| Hypothesis | Why | Tightness |
| :--- | :--- | :--- |
| `∀ a ∈ arms, NoDupBindings a.pat` | each binding's value is dropped once under the first-alternative order | tight: counterexample `OrPat.dupBindArms_sameDeclOrder_not_noDupBindings_and_policies_differ` (an arm list with exactly one arm, the or-free pattern `(x, x)`, on the value `(1, 2)`) |
| `∀ a ∈ arms, SameDeclOrder a.pat` | the matched alternative declares its bindings in the first alternative's order | tight: counterexample `OrPat.refDropArms_noDupBindings_not_sameDeclOrder_and_policies_differ` (an arm list with exactly one arm, `Ok((x, y)) | Err((y, x))`, on the value `Err((10, 20))`) |

**Non-vacuity witness.** Every arm of `bindingGuardArms` satisfies both hypotheses; its first arm is a guarded or-pattern whose guard reads the binding. (`OrPat.bindingGuardArms_noDupBindings_sameDeclOrder`)

**Positive control.** The hypotheses are sufficient, not necessary: `shadowedSwapArms` (`(x, y) | (y, x)`, unguarded) violates `SameDeclOrder`, yet the two policies give the same trace on every value, because its order-reversing alternative is never used. (`OrPat.shadowedSwapArms_not_sameDeclOrder_and_policies_agree`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R12; they are part of this card.

**Prior art.**

- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/destructors.md:223-259 ("For the purpose of drop order, [or-patterns] declare bindings in the order given by the first subpattern.", with the `Ok([x, y]) | Err([y, x])` example matching each subpattern) — normative
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:550-551 ("To use the drop order for the first sub-branch, we lower sub-branches in reverse", citing rust-lang/rust#142163, an issue-tracker item used as background, not as a subject) and :978-984 (`SubpatternBindings::FromOrPattern`) — source comments
- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:1016-1046 (or-patterns: static semantics, including that "the same set of bindings" must be introduced in `p` and `q` (lines 1024-1031); dynamic semantics of `c(p | q, ..rest)` as `c(p, ..rest) | c(q, ..rest)` (lines 1044-1045)) and :175-176 ("The identifier must be unique within the pattern.") — normative
- Corpus packages `edition-indexed-drop-scopes-tail-and-if-let-temporaries-and-inhabitedness-gated-switches` and `drop-check-may-dangle-and-destructor-soundness-for-generic-containers` (google/zerocopy branch `reference` at 8978e7348aaa6d0808db1d0232d020d053020f4d): drop scopes and drop check; not repeated here
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** How do or-patterns with guards lower soundly to sub-branches, how often is the guard evaluated, and with which binding drop order?

Basis: execution (Lean kernel check) — `OrPat.runSrc_firstAlternative_eq_matchedAlternative_of_noDupBindings_of_sameDeclOrder` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R13 — `OrPat.runSplit_matchedAlternative_ne_runSrc_firstAlternative_refDropArms` (counterexample)

- **Kind:** counterexample. **Tier:** T1 — toy form of the Reference's `Ok([x, y]) | Err([y, x])` drop-order example.
- **Depth:** definitional.

**Plain claim.** There is an arm list, `refDropArms` (`Ok((x, y)) | Err((y, x))`), and a value, `Err((10, 20))`, on which the split lowering whose sub-branches drop in their own declaration order (`splitArms .matchedAlternative`) does not reproduce the source trace under the `firstAlternative` policy.

**Statement.**

```lean
-- lean/ToyMatchGuard/OrPat.lean:561-563
theorem runSplit_matchedAlternative_ne_runSrc_firstAlternative_refDropArms :
    runSplit (.inr (.pair (.int 10) (.int 20))) (splitArms .matchedAlternative 0 refDropArms) ≠
      runSrc .firstAlternative (.inr (.pair (.int 10) (.int 20))) 0 refDropArms := …
```

**Hypothesis ledger.** No hypotheses: the statement is a concrete instance.

**Non-vacuity witness.** The statement is itself a concrete instance (`refDropArms`, value `Err((10, 20))`). (`OrPat.runSplit_matchedAlternative_ne_runSrc_firstAlternative_refDropArms`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R13; they are part of this card.

**Prior art.**

- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/destructors.md:223-259 ("For the purpose of drop order, [or-patterns] declare bindings in the order given by the first subpattern.", with the `Ok([x, y]) | Err([y, x])` example matching each subpattern) — normative
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:550-551 ("To use the drop order for the first sub-branch, we lower sub-branches in reverse", citing rust-lang/rust#142163, an issue-tracker item used as background, not as a subject) and :978-984 (`SubpatternBindings::FromOrPattern`) — source comments

**Design question.** How do or-patterns with guards lower soundly to sub-branches, how often is the guard evaluated, and with which binding drop order?

Basis: execution (Lean kernel check) — `OrPat.runSplit_matchedAlternative_ne_runSrc_firstAlternative_refDropArms` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R14 — `ConstPat.loweringAgrees_of_allDerived_of_noFloat` (theorem)

- **Kind:** theorem. **Tier:** T1 — the goal is documented for `StructuralPartialEq`; the toy agreement statement was not found mechanized.
- **Depth:** shallow.

**Plain claim.** For every toy type `T` all of whose struct and enum nodes have a derived `==` (`AllDerived T`: every node of the type, whether or not a given constant uses it) and which has no float leaf (`NoFloat T`), for every constant `c` and every scrutinee `v` of type `T`, the structural lowering `smatch c v` (which compares float leaves by bit pattern) equals `teq T c v`. This is the `←` direction of R15.

**Statement.**

```lean
-- lean/ToyMatchGuard/ConstPat.lean:184-185
theorem loweringAgrees_of_allDerived_of_noFloat (T : CTy) (hd : AllDerived T) (hf : NoFloat T) :
    LoweringAgrees T := …
```

**Hypothesis ledger.**

| Hypothesis | Why | Tightness |
| :--- | :--- | :--- |
| `hd : AllDerived T` | every node's `==` is the structural composition of its fields' `==` | tight: counterexample `ConstPat.manualVariantTy_noFloat_and_lowering_disagrees` (a two-variant integer enum whose manual `==` ignores the variant, with constant `inl 0` and scrutinee `inr 0`) |
| `hf : NoFloat T` | the bit-pattern leaf test differs from IEEE equality on floats | tight: counterexample `ConstPat.flt_allDerived_and_lowering_disagrees_nan` (the toy float type, with constant and scrutinee `nan`) |

**Non-vacuity witness.** `derivedTy` (an `(i32, Option<i32>)`-like type with derived `==` everywhere) satisfies both hypotheses and has a value. (`ConstPat.derivedTy_allDerived_noFloat`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R14; they are part of this card.

**Prior art.**

- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:980-1014 (constant patterns: `T: PartialEq` (lines 980-981); "the value of `C` *has (recursive) structural equality*" (lines 983-984); "A value of `struct` or `enum` type has structural equality if its `PartialEq` instance is derived via `#[derive(PartialEq)]`, and all fields (for enums: of the active variant) have structural equality." (lines 995-996); "A float value has structural equality if it is not a `NaN`." (lines 1001-1002); translation into a pattern (lines 1013-1014)) — normative
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:library/core/src/marker.rs:239-253 (`StructuralPartialEq`: "interpreting the value of the constant as a pattern is equivalent to calling `PartialEq`") — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/test.rs:43-45 (float constants use `TestKind::ScalarEq`) and :181-234 (`ScalarEq` is performed with `BinOp::Eq`), rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1672-1673 (`BinOp::Eq`: "The `==` operator (equality)") — source and documentation
- rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07:text/1445-restrict-constants-in-patterns.md:238-253 ("in the compiler today, match *will* compare 0.0 and -0.0 as equal") — RFC (design document, 2015)
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** When does lowering a constant pattern to structural tests agree with calling `==`?

Basis: execution (Lean kernel check) — `ConstPat.loweringAgrees_of_allDerived_of_noFloat` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R15 — `ConstPat.loweringAgrees_iff_noFloat_of_allDerived` (characterization)

- **Kind:** characterization. **Tier:** T1 — made precise here for the toy's bit-pattern leaf test; not found mechanized.
- **Depth:** shallow.

**Plain claim.** For every toy type `T` all of whose struct and enum nodes have a derived `==` (`AllDerived T`), the structural lowering (which compares float leaves by bit pattern) agrees with `teq T` for every constant and every scrutinee of type `T` (`LoweringAgrees T`) iff `T` has no float leaf (`NoFloat T`).

**Statement.**

```lean
-- lean/ToyMatchGuard/ConstPat.lean:191-192
theorem loweringAgrees_iff_noFloat_of_allDerived (T : CTy) (hd : AllDerived T) :
    LoweringAgrees T ↔ NoFloat T := …
```

**Hypothesis ledger.**

| Hypothesis | Why | Tightness |
| :--- | :--- | :--- |
| `hd : AllDerived T` | restricts the characterization to all-derived types | tight: counterexample `ConstPat.manualVariantTy_not_allDerived_and_iff_fails` (a two-variant integer enum whose manual `==` ignores the variant) |

**Non-vacuity witness.** `derivedTy` satisfies `AllDerived` with both sides of the equivalence true; the toy float type satisfies `AllDerived` with both sides false (`flt_allDerived_and_lowering_disagrees_nan`). (`ConstPat.derivedTy_allDerived_noFloat`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R15; they are part of this card.

**Prior art.**

- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:980-1014 (constant patterns: `T: PartialEq` (lines 980-981); "the value of `C` *has (recursive) structural equality*" (lines 983-984); "A value of `struct` or `enum` type has structural equality if its `PartialEq` instance is derived via `#[derive(PartialEq)]`, and all fields (for enums: of the active variant) have structural equality." (lines 995-996); "A float value has structural equality if it is not a `NaN`." (lines 1001-1002); translation into a pattern (lines 1013-1014)) — normative
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:library/core/src/marker.rs:239-253 (`StructuralPartialEq`: "interpreting the value of the constant as a pattern is equivalent to calling `PartialEq`") — documentation
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/test.rs:43-45 (float constants use `TestKind::ScalarEq`) and :181-234 (`ScalarEq` is performed with `BinOp::Eq`), rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/mir/syntax.rs:1672-1673 (`BinOp::Eq`: "The `==` operator (equality)") — source and documentation
- rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07:text/1445-restrict-constants-in-patterns.md:238-253 ("in the compiler today, match *will* compare 0.0 and -0.0 as equal") — RFC (design document, 2015)
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** When does lowering a constant pattern to structural tests agree with calling `==`?

Basis: execution (Lean kernel check) — `ConstPat.loweringAgrees_iff_noFloat_of_allDerived` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R16 — `Accessor.shared_selected_eq_repeated_selected_iff_resultStable` (characterization)

- **Kind:** characterization. **Tier:** T0 — an elementary two-call law for a state-passing function, restated for the toy lowerings.
- **Depth:** shallow.

**Plain claim.** For every accessor `acc : Acc σ S R` (every hidden-state type `σ`, scrutinee type `S` and result type `R`), the shared and repeated lowerings select the same arm for every scrutinee, every hidden state and every arm list iff `ResultStable acc`: from every hidden state, reachable or not, and every scrutinee, a second call returns the same result as the first.

**Statement.**

```lean
-- lean/ToyMatchGuard/Accessor.lean:104-105
theorem shared_selected_eq_repeated_selected_iff_resultStable (acc : Acc σ S R) :
    (∀ s st arms, (shared acc s arms st).1 = (repeated acc s arms 0 st).1) ↔ ResultStable acc := …
```

**Hypothesis ledger.** No hypotheses: the statement is an unconditional equivalence for every accessor.

**Non-vacuity witness.** `countedBoolAcc` (result type `Bool`, result depending on the scrutinee) is result-stable but neither state-idempotent nor strictly pure; `toggleAcc` is not result-stable (`not_resultStable_example`). (`Accessor.countedBoolAcc_resultStable_not_stateIdempotent_not_pure`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R16; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:library/core/src/ops/deref.rs:285-297 (`DerefPure`, perma-unstable: successive `deref` calls "should be idempotent, in the sense that they return the same value as far as pattern-matching is concerned"; "The precise semantics are undecided") — documentation of an unstable trait
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:1342-1347 (`TestKind::Deref`: "Call `Deref::deref[_mut]` on the value.", result stored in a temporary) and rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:src/doc/unstable-book/src/language-features/deref-patterns.md:1-13 (the unstable `deref_patterns` feature) — documentation
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** What property must a user-defined accessor used by deref patterns have so that repeated calls and a shared (DAG) result agree, and so that exhaustiveness is preserved?

Basis: execution (Lean kernel check) — `Accessor.shared_selected_eq_repeated_selected_iff_resultStable` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R17 — `Accessor.shared_eq_repeated_iff_resultStable_and_stateIdempotent` (characterization)

- **Kind:** characterization. **Tier:** T0 — an elementary two-call law for a state-passing function, restated for the toy lowerings.
- **Depth:** shallow.

**Plain claim.** For every accessor `acc`, `shared acc s arms st = repeated acc s arms 0 st` (the same selected arm and the same final hidden state) for every scrutinee `s`, every hidden state `st` and every arm list `arms` iff `ResultStable acc` and `StateIdempotent acc`, each required from every hidden state, reachable or not.

**Statement.**

```lean
-- lean/ToyMatchGuard/Accessor.lean:126-128
theorem shared_eq_repeated_iff_resultStable_and_stateIdempotent (acc : Acc σ S R) :
    (∀ s st arms, shared acc s arms st = repeated acc s arms 0 st) ↔
      ResultStable acc ∧ StateIdempotent acc := …
```

**Hypothesis ledger.** No hypotheses: the statement is an unconditional equivalence for every accessor.

**Non-vacuity witness.** `loggedBoolAcc` (result type `Bool`, result depending on the scrutinee) is result-stable and state-idempotent but not strictly pure. (`Accessor.loggedBoolAcc_resultStable_stateIdempotent_not_pure`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R17; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:library/core/src/ops/deref.rs:285-297 (`DerefPure`, perma-unstable: successive `deref` calls "should be idempotent, in the sense that they return the same value as far as pattern-matching is concerned"; "The precise semantics are undecided") — documentation of an unstable trait
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:1342-1347 (`TestKind::Deref`: "Call `Deref::deref[_mut]` on the value.", result stored in a temporary) and rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:src/doc/unstable-book/src/language-features/deref-patterns.md:1-13 (the unstable `deref_patterns` feature) — documentation
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** What property must a user-defined accessor used by deref patterns have so that repeated calls and a shared (DAG) result agree, and so that exhaustiveness is preserved?

Basis: execution (Lean kernel check) — `Accessor.shared_eq_repeated_iff_resultStable_and_stateIdempotent` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R18 — `Accessor.repeated_not_unreachable_on_exhaustiveOn_iff_resultStable_of_wellTyped` (characterization)

- **Kind:** characterization. **Tier:** T1 — `DerefPure` documents the idempotence requirement informally; the characterization of exhaustiveness preservation is made precise here.
- **Depth:** shallow.

**Plain claim.** For every result domain `RDom` and every accessor `acc` all of whose results, from every hidden state and every scrutinee, lie in `RDom` (`WellTyped RDom acc`): the repeated lowering does not reach `Unreachable` for every arm list exhaustive on `RDom` (`ExhaustiveOn RDom arms`), every scrutinee and every hidden state, iff from every hidden state, reachable or not, and every scrutinee, a second call returns the same result as the first (`ResultStable acc`).

**Statement.**

```lean
-- lean/ToyMatchGuard/Accessor.lean:152-155
theorem repeated_not_unreachable_on_exhaustiveOn_iff_resultStable_of_wellTyped (RDom : R → Prop)
    (acc : Acc σ S R) (hwt : WellTyped RDom acc) :
    (∀ arms, ExhaustiveOn RDom arms → ∀ s st, (repeated acc s arms 0 st).1 ≠ none) ↔
      ResultStable acc := …
```

**Hypothesis ledger.**

| Hypothesis | Why | Tightness |
| :--- | :--- | :--- |
| `hwt : WellTyped RDom acc` | exhaustiveness on `RDom` covers every result the accessor can return | tight: counterexample `Accessor.constFalseAcc_resultStable_not_wellTyped_and_iff_fails` (a stateless accessor that returns `false`, with result domain `{true}`) |

**Non-vacuity witness.** `idAcc` (strictly pure, result `Bool`) is well-typed for the full `Bool` domain, and both sides hold. (`Accessor.idAcc_pure_wellTyped`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R18; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:library/core/src/ops/deref.rs:285-297 (`DerefPure`, perma-unstable: successive `deref` calls "should be idempotent, in the sense that they return the same value as far as pattern-matching is concerned"; "The precise semantics are undecided") — documentation of an unstable trait
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:1342-1347 (`TestKind::Deref`: "Call `Deref::deref[_mut]` on the value.", result stored in a temporary) and rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:src/doc/unstable-book/src/language-features/deref-patterns.md:1-13 (the unstable `deref_patterns` feature) — documentation
- Novelty search (2026-11-21; web queries "formal verification match guard fake borrows exhaustiveness preservation Rust decision tree mechanized proof", "Coq OR Lean OR Isabelle proof or-pattern guard compilation decision tree correctness side effects guard evaluated multiple times", "deref patterns DerefPure soundness formalization idempotent deref pattern matching unreachable", "verified pattern match compiler CakeML decision tree correctness proof HOL4"): no mechanized statement was found of exhaustiveness preservation under shallow/deep fake-borrow freezing, of or-pattern splitting trace equivalence with a drop-order policy, or of the accessor-stability characterizations; the closest mechanized work found is Tuerk, Myreen and Kumar (ITP 2015, HOL4: guarded pattern matches) and Thiemann and Yamada (Archive of Formal Proofs 2024, Isabelle: pattern completeness), whose abstracts do not mention guards that write the scrutinee. A search is not a proof of absence.

**Design question.** What property must a user-defined accessor used by deref patterns have so that repeated calls and a shared (DAG) result agree, and so that exhaustiveness is preserved?

Basis: execution (Lean kernel check) — `Accessor.repeated_not_unreachable_on_exhaustiveOn_iff_resultStable_of_wellTyped` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

#### R19 — `Accessor.toggleAcc_repeated_reaches_unreachable` (counterexample)

- **Kind:** counterexample. **Tier:** T1 — toy form of the soundness concern behind `DerefPure`.
- **Depth:** definitional.

**Plain claim.** There is an accessor, `toggleAcc : Acc Bool Unit Bool` (hidden state `Bool`, scrutinee `Unit`, result `Bool`; it returns its hidden flag and flips it), that satisfies `WellTyped (fun _ => True)` (every result lies in the full `Bool` domain) and is not result-stable, and with the exhaustive arm list `boolResultArms` (`[true => .., false => ..]`) from hidden state `false` the repeated lowering reaches `Unreachable` while the shared lowering selects arm `1`.

**Statement.**

```lean
-- lean/ToyMatchGuard/Accessor.lean:215-219
theorem toggleAcc_repeated_reaches_unreachable :
    WellTyped (fun _ => True) toggleAcc ∧ ¬ ResultStable toggleAcc ∧
      ExhaustiveOn (fun _ => True) boolResultArms ∧
      (repeated toggleAcc () boolResultArms 0 false).1 = none ∧
      (shared toggleAcc () boolResultArms false).1 = some 1 := …
```

**Hypothesis ledger.** No hypotheses: the statement is a concrete instance.

**Non-vacuity witness.** The statement is itself a concrete instance (`toggleAcc`, `boolResultArms`, hidden state `false`). (`Accessor.toggleAcc_repeated_reaches_unreachable`)

**Non-claims.** Listed under **Boundaries**, *Non-claims*, R19; they are part of this card.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:library/core/src/ops/deref.rs:285-297 (`DerefPure`, perma-unstable: successive `deref` calls "should be idempotent, in the sense that they return the same value as far as pattern-matching is concerned"; "The precise semantics are undecided") — documentation of an unstable trait
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:1342-1347 (`TestKind::Deref`: "Call `Deref::deref[_mut]` on the value.", result stored in a temporary) and rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:src/doc/unstable-book/src/language-features/deref-patterns.md:1-13 (the unstable `deref_patterns` feature) — documentation

**Design question.** What property must a user-defined accessor used by deref patterns have so that repeated calls and a shared (DAG) result agree, and so that exhaustiveness is preserved?

Basis: execution (Lean kernel check) — `Accessor.toggleAcc_repeated_reaches_unreachable` and the witnesses, positive controls and tightness counterexamples named in this card; axioms and statement hashes are under **Evidence**.

Basis: derived (modeling bridge) — the prior-art entries that cite rustc, the Rust Reference or Rust RFCs quote documented behaviour at pinned revisions, and the toy definitions this card uses are written to follow it (modeling bridges B1–B6 under **Applicability**); no correspondence is proved, so these remarks neither establish nor refute the corresponding claims about rustc or the Rust Reference.

### Auxiliary lemmas and instances cited by name (verbatim)

#### `disjointSwitchWriteArms_deepFrozenSwitchAll`

```lean
-- lean/ToyMatchGuard/Instances.lean:345-348
theorem disjointSwitchWriteArms_deepFrozenSwitchAll :
    DeepFrozenSwitchAll disjointSwitchWriteArms ∧
      disjointSwitchWriteArms.map Arm.guardWrites = [[[.field 0 1]], [], []] ∧
      disjointSwitchWriteArms.map Arm.switchPlaces = [[[.field 0 0]], [[.field 0 0]], [[.field 0 0]]] := …
```

#### `copyBoundFieldArms_guardsPreserveDom_and_unmatched_write_leaves_dom`

```lean
-- lean/ToyMatchGuard/Instances.lean:372-377
theorem copyBoundFieldArms_guardsPreserveDom_and_unmatched_write_leaves_dom :
    GuardsPreserveDom PairOptBoolDom copyBoundFieldArms ∧
      PairOptBoolDom (.ctor 0 [vNone, vNone]) ∧
      ¬ PairOptBoolDom
        (runWrites (bindEnv (.ctor 0 [vNone, vNone]) [(0, [.field 0 0, .field 1 0])])
          (.ctor 0 [vNone, vNone]) [([.field 0 1], writeBoundOptBool)]) := …
```

#### `reassignArms_exhaustive_guardsPreserveDom_deepFrozenBefore_and_reaches_unreachable`

```lean
-- lean/ToyMatchGuard/Instances.lean:426-430
theorem reassignArms_exhaustive_guardsPreserveDom_deepFrozenBefore_and_reaches_unreachable :
    Exhaustive RefOptBoolDom reassignArms ∧ GuardsPreserveDom RefOptBoolDom reassignArms ∧
      DeepFrozenBefore reassignArms ∧ ¬ ShallowFrozenBefore reassignArms ∧
      RefOptBoolDom (.box (vSome vTrue)) ∧
      (runMatch reassignArms (.box (vSome vTrue))).reachesUnreachable = true := …
```

#### `boxBoolArms_exhaustive_guardsPreserveDom_shallowFrozenBefore_and_reaches_unreachable`

```lean
-- lean/ToyMatchGuard/Instances.lean:448-452
theorem boxBoolArms_exhaustive_guardsPreserveDom_shallowFrozenBefore_and_reaches_unreachable :
    Exhaustive BoxBoolDom boxBoolArms ∧ GuardsPreserveDom BoxBoolDom boxBoolArms ∧
      ShallowFrozenBefore boxBoolArms ∧ ¬ DeepFrozenBefore boxBoolArms ∧
      BoxBoolDom (.box vFalse) ∧
      (runMatch boxBoolArms (.box vFalse)).reachesUnreachable = true := …
```

#### `boxBoolArms_not_noDerefPatterns_exhaustive_shallowFrozenAll_and_reaches_unreachable`

```lean
-- lean/ToyMatchGuard/Instances.lean:459-462
theorem boxBoolArms_not_noDerefPatterns_exhaustive_shallowFrozenAll_and_reaches_unreachable :
    ¬ NoDerefPatterns boxBoolArms ∧ Exhaustive BoxBoolDom boxBoolArms ∧
      ShallowFrozenAll boxBoolArms ∧ BoxBoolDom (.box vFalse) ∧
      (runMatch boxBoolArms (.box vFalse)).reachesUnreachable = true := …
```

#### `illTypedArms_exhaustive_frozenBefore_and_reaches_unreachable`

```lean
-- lean/ToyMatchGuard/Instances.lean:468-472
theorem illTypedArms_exhaustive_frozenBefore_and_reaches_unreachable :
    Exhaustive OptBoolDom illTypedArms ∧ ShallowFrozenBefore illTypedArms ∧
      DeepFrozenBefore illTypedArms ∧ ¬ GuardsPreserveDom OptBoolDom illTypedArms ∧
      OptBoolDom (vSome vTrue) ∧
      (runMatch illTypedArms (vSome vTrue)).reachesUnreachable = true := …
```

#### `mixedStaticArms_satisfy_static_hypotheses`

```lean
-- lean/ToyMatchGuard/Instances.lean:485-492
theorem mixedStaticArms_satisfy_static_hypotheses :
    Exhaustive OptPairBoxBoolDom mixedStaticArms ∧ ShallowFrozenAll mixedStaticArms ∧
      DeepFrozenAll mixedStaticArms ∧ OptPairBoxBoolDom (vSome (.ctor 0 [.box vFalse, vFalse])) ∧
      mixedStaticArms.map Arm.switchPlaces = [[[]], [[]], [[]], [[]]] ∧
      mixedStaticArms.map Arm.derefScrutinees =
        [[], [[.field 1 0, .field 0 0]], [], [[.field 1 0, .field 0 0]]] ∧
      mixedStaticArms.map Arm.guardWrites = [[], [], [[.field 1 0, .field 0 1]], []] ∧
      ¬ DeepFrozenSwitchAll mixedStaticArms := …
```

#### `shallowGuardArms_satisfy_static_hypotheses`

```lean
-- lean/ToyMatchGuard/Instances.lean:499-502
theorem shallowGuardArms_satisfy_static_hypotheses :
    NoDerefPatterns shallowGuardArms ∧ Exhaustive OptIntDom shallowGuardArms ∧
      ShallowFrozenAll shallowGuardArms ∧ DeepFrozenAll shallowGuardArms ∧
      OptIntDom (vSome (.int 0)) := …
```

#### `mixedLaterTestedArms_satisfy_frozenBefore_hypotheses_and_not_shallowFrozenAll`

```lean
-- lean/ToyMatchGuard/Instances.lean:510-518
theorem mixedLaterTestedArms_satisfy_frozenBefore_hypotheses_and_not_shallowFrozenAll :
    Exhaustive OptPairBoxBoolDom mixedLaterTestedArms ∧
      GuardsPreserveDom OptPairBoxBoolDom mixedLaterTestedArms ∧
      ShallowFrozenBefore mixedLaterTestedArms ∧ DeepFrozenBefore mixedLaterTestedArms ∧
      ¬ ShallowFrozenAll mixedLaterTestedArms ∧
      OptPairBoxBoolDom (vSome (.ctor 0 [.box vFalse, vFalse])) ∧
      (mixedLaterTestedArms.take 3).map Arm.switchPlaces = [[[]], [[]], [[]]] ∧
      (mixedLaterTestedArms.take 3).map Arm.derefScrutinees = [[], [[.field 1 0, .field 0 0]], []] ∧
      mixedLaterTestedArms.map Arm.guardWrites = [[], [], [[.field 1 0, .field 0 1]], [], []] := …
```

#### `missingArms_frozen_not_exhaustive_and_reaches_unreachable`

```lean
-- lean/ToyMatchGuard/Instances.lean:551-556
theorem missingArms_frozen_not_exhaustive_and_reaches_unreachable :
    ¬ Exhaustive OptBoolDom missingArms ∧ NoDerefPatterns missingArms ∧
      ShallowFrozenAll missingArms ∧ DeepFrozenAll missingArms ∧
      GuardsPreserveDom OptBoolDom missingArms ∧ ShallowFrozenBefore missingArms ∧
      DeepFrozenBefore missingArms ∧ OptBoolDom (vSome vFalse) ∧
      (runMatch missingArms (vSome vFalse)).reachesUnreachable = true := …
```

#### `boolArms_exhaustive_frozen_and_reaches_unreachable_outside_dom`

```lean
-- lean/ToyMatchGuard/Instances.lean:578-582
theorem boolArms_exhaustive_frozen_and_reaches_unreachable_outside_dom :
    Exhaustive BoolDom boolArms ∧ NoDerefPatterns boolArms ∧ ShallowFrozenAll boolArms ∧
      DeepFrozenAll boolArms ∧ GuardsPreserveDom BoolDom boolArms ∧
      ShallowFrozenBefore boolArms ∧ DeepFrozenBefore boolArms ∧ ¬ BoolDom (.int 0) ∧
      (runMatch boolArms (.int 0)).reachesUnreachable = true := …
```

#### `e0510Arms_selects_last_arm_with_changed_memory`

```lean
-- lean/ToyMatchGuard/Instances.lean:599-604
theorem e0510Arms_selects_last_arm_with_changed_memory :
    ¬ ShallowFrozenAll e0510Arms ∧
      (runMatch e0510Arms (.box (vSome vTrue))).selected = some 2 ∧
      (match runMatch e0510Arms (.box (vSome vTrue)) with
        | .arm _ _ mem => decide (mem = .box vNone)
        | .unreachable _ => false) = true := …
```

#### `borrowck_reassignArms`

```lean
-- lean/ToyMatchGuard/Checker.lean:84-84
theorem borrowck_reassignArms : borrowck reassignArms = false := …
```

#### `borrowck_boxBoolArms`

```lean
-- lean/ToyMatchGuard/Checker.lean:87-87
theorem borrowck_boxBoolArms : borrowck boxBoolArms = false := …
```

#### `runMatch_sameVariantArms_some0`

```lean
-- lean/ToyMatchGuard/Checker.lean:104-107
theorem runMatch_sameVariantArms_some0 :
    (match runMatch sameVariantArms (vSome (.int 0)) with
      | .arm i _ mem => decide (i = 2 ∧ mem = vSome (.int 5))
      | .unreachable _ => false) = true := …
```

#### `reassignArms_rejected_exhaustive_and_reaches_unreachable`

```lean
-- lean/ToyMatchGuard/Checker.lean:111-114
theorem reassignArms_rejected_exhaustive_and_reaches_unreachable :
    borrowck reassignArms = false ∧ Exhaustive RefOptBoolDom reassignArms ∧
      RefOptBoolDom (.box (vSome vTrue)) ∧
      (runMatch reassignArms (.box (vSome vTrue))).reachesUnreachable = true := …
```

#### `missingArms_accepted_and_reaches_unreachable`

```lean
-- lean/ToyMatchGuard/Checker.lean:119-121
theorem missingArms_accepted_and_reaches_unreachable :
    borrowck missingArms = true ∧ ¬ Exhaustive OptBoolDom missingArms ∧
      OptBoolDom (vSome vFalse) ∧ (runMatch missingArms (vSome vFalse)).reachesUnreachable = true := …
```

#### `boolArms_accepted_and_reaches_unreachable_outside_dom`

```lean
-- lean/ToyMatchGuard/Checker.lean:128-130
theorem boolArms_accepted_and_reaches_unreachable_outside_dom :
    borrowck boolArms = true ∧ Exhaustive BoolDom boolArms ∧ ¬ BoolDom (.int 0) ∧
      (runMatch boolArms (.int 0)).reachesUnreachable = true := …
```

#### `mixedStaticArms_accepted_exhaustive`

```lean
-- lean/ToyMatchGuard/Checker.lean:137-142
theorem mixedStaticArms_accepted_exhaustive :
    borrowck mixedStaticArms = true ∧ Exhaustive OptPairBoxBoolDom mixedStaticArms ∧
      OptPairBoxBoolDom (vSome (.ctor 0 [.box vFalse, vFalse])) ∧
      ([], FakeKind.shallow) ∈ fakeBorrows mixedStaticArms ∧
      ([.field 1 0, .field 0 0], FakeKind.deep) ∈ fakeBorrows mixedStaticArms ∧
      mixedStaticArms.map Arm.guardWrites = [[], [], [[.field 1 0, .field 0 1]], []] := …
```

#### `OrPat.matchAll_eq_flatMap_expand`

```lean
-- lean/ToyMatchGuard/OrPat.lean:303-304
theorem matchAll_eq_flatMap_expand (P : Pat) (v : PV) :
    matchAll P v = (expand P).flatMap (fun p' => matchAll p' v) := …
```

#### `OrPat.runGuardOnce_eq_runSrc_of_matchAll_length_le_one`

```lean
-- lean/ToyMatchGuard/OrPat.lean:501-503
theorem runGuardOnce_eq_runSrc_of_matchAll_length_le_one (pol : DropPolicy) (v : PV) :
    ∀ (arms : List SArm) (i : Nat), (∀ a ∈ arms, (matchAll a.pat v).length ≤ 1) →
      runGuardOnce pol v i arms = runSrc pol v i arms := …
```

#### `OrPat.okErrGuardArms_matchAll_length_le_one`

```lean
-- lean/ToyMatchGuard/OrPat.lean:526-527
theorem okErrGuardArms_matchAll_length_le_one :
    ∀ v, ∀ a ∈ okErrGuardArms, (matchAll a.pat v).length ≤ 1 := …
```

#### `OrPat.refDropArms_noDupBindings_not_sameDeclOrder_and_policies_differ`

```lean
-- lean/ToyMatchGuard/OrPat.lean:540-547
theorem refDropArms_noDupBindings_not_sameDeclOrder_and_policies_differ :
    (∀ a ∈ refDropArms, NoDupBindings a.pat) ∧ ¬ (∀ a ∈ refDropArms, SameDeclOrder a.pat) ∧
      runSrc .firstAlternative (.inr (.pair (.int 10) (.int 20))) 0 refDropArms =
        [.body 0 [(1, .int 10), (0, .int 20)], .drop (.int 10), .drop (.int 20)] ∧
      runSrc .matchedAlternative (.inr (.pair (.int 10) (.int 20))) 0 refDropArms =
        [.body 0 [(1, .int 10), (0, .int 20)], .drop (.int 20), .drop (.int 10)] ∧
      runSrc .firstAlternative (.inr (.pair (.int 10) (.int 20))) 0 refDropArms ≠
        runSrc .matchedAlternative (.inr (.pair (.int 10) (.int 20))) 0 refDropArms := …
```

#### `OrPat.dupBindArms_sameDeclOrder_not_noDupBindings_and_policies_differ`

```lean
-- lean/ToyMatchGuard/OrPat.lean:570-577
theorem dupBindArms_sameDeclOrder_not_noDupBindings_and_policies_differ :
    (∀ a ∈ dupBindArms, SameDeclOrder a.pat) ∧ ¬ (∀ a ∈ dupBindArms, NoDupBindings a.pat) ∧
      runSrc .firstAlternative (.pair (.int 1) (.int 2)) 0 dupBindArms =
        [.body 0 [(0, .int 1), (0, .int 2)], .drop (.int 1), .drop (.int 1)] ∧
      runSrc .matchedAlternative (.pair (.int 1) (.int 2)) 0 dupBindArms =
        [.body 0 [(0, .int 1), (0, .int 2)], .drop (.int 2), .drop (.int 1)] ∧
      runSrc .firstAlternative (.pair (.int 1) (.int 2)) 0 dupBindArms ≠
        runSrc .matchedAlternative (.pair (.int 1) (.int 2)) 0 dupBindArms := …
```

#### `OrPat.unbalancedOrArms_firstAlternative_omits_drop`

```lean
-- lean/ToyMatchGuard/OrPat.lean:592-595
theorem unbalancedOrArms_firstAlternative_omits_drop :
    runSrc .firstAlternative (.inr (.int 5)) 0 unbalancedOrArms = [.body 0 [(0, .int 5)]] ∧
      runSrc .matchedAlternative (.inr (.int 5)) 0 unbalancedOrArms =
        [.body 0 [(0, .int 5)], .drop (.int 5)] := …
```

#### `OrPat.shadowedSwapArms_not_sameDeclOrder_and_policies_agree`

```lean
-- lean/ToyMatchGuard/OrPat.lean:601-605
theorem shadowedSwapArms_not_sameDeclOrder_and_policies_agree :
    (∀ a ∈ shadowedSwapArms, NoDupBindings a.pat) ∧
      ¬ (∀ a ∈ shadowedSwapArms, SameDeclOrder a.pat) ∧
      ∀ v, runSrc .firstAlternative v 0 shadowedSwapArms =
        runSrc .matchedAlternative v 0 shadowedSwapArms := …
```

#### `OrPat.bindingGuardArms_noDupBindings_sameDeclOrder`

```lean
-- lean/ToyMatchGuard/OrPat.lean:625-626
theorem bindingGuardArms_noDupBindings_sameDeclOrder :
    (∀ a ∈ bindingGuardArms, NoDupBindings a.pat) ∧ (∀ a ∈ bindingGuardArms, SameDeclOrder a.pat) := …
```

#### `ConstPat.hasTy_inhabit`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:115-115
theorem hasTy_inhabit : ∀ T : CTy, HasTy (inhabit T) T
```

#### `ConstPat.exists_teq_self_false_of_allDerived_of_not_noFloat`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:121-122
theorem exists_teq_self_false_of_allDerived_of_not_noFloat : ∀ T : CTy, AllDerived T →
    ¬ NoFloat T → ∃ c, HasTy c T ∧ teq T c c = false
```

#### `ConstPat.manualVariantTy_noFloat_and_lowering_disagrees`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:225-229
theorem manualVariantTy_noFloat_and_lowering_disagrees :
    NoFloat manualVariantTy ∧ ¬ AllDerived manualVariantTy ∧ ¬ LoweringAgrees manualVariantTy ∧
      HasTy (.inl (.int 0)) manualVariantTy ∧ HasTy (.inr (.int 0)) manualVariantTy ∧
      smatch (.inl (.int 0)) (.inr (.int 0)) = false ∧
      teq manualVariantTy (.inl (.int 0)) (.inr (.int 0)) = true := …
```

#### `ConstPat.nestedManualTy_lowering_disagrees`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:238-243
theorem nestedManualTy_lowering_disagrees :
    NoFloat nestedManualTy ∧ ¬ AllDerived nestedManualTy ∧
      HasTy (.pair (.int 0) (.inl (.int 0))) nestedManualTy ∧
      HasTy (.pair (.int 0) (.inr (.int 0))) nestedManualTy ∧
      smatch (.pair (.int 0) (.inl (.int 0))) (.pair (.int 0) (.inr (.int 0))) = false ∧
      teq nestedManualTy (.pair (.int 0) (.inl (.int 0))) (.pair (.int 0) (.inr (.int 0))) = true := …
```

#### `ConstPat.flt_allDerived_and_lowering_disagrees_nan`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:250-252
theorem flt_allDerived_and_lowering_disagrees_nan :
    AllDerived .flt ∧ ¬ NoFloat .flt ∧ ¬ LoweringAgrees .flt ∧
      smatch (.flt .nan) (.flt .nan) = true ∧ teq .flt (.flt .nan) (.flt .nan) = false := …
```

#### `ConstPat.manualStructuralTy_loweringAgrees_and_not_allDerived`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:267-268
theorem manualStructuralTy_loweringAgrees_and_not_allDerived :
    LoweringAgrees manualStructuralTy ∧ ¬ AllDerived manualStructuralTy := …
```

#### `ConstPat.derivedTy_allDerived_noFloat`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:277-278
theorem derivedTy_allDerived_noFloat :
    AllDerived derivedTy ∧ NoFloat derivedTy ∧ HasTy (.pair (.int 1) (.inr (.int 2))) derivedTy := …
```

#### `ConstPat.smatch_agrees_with_teq_iff_noNanNoZeroLeaf_of_allDerived`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:431-433
theorem smatch_agrees_with_teq_iff_noNanNoZeroLeaf_of_allDerived {T : CTy} {c : CVal}
    (hd : AllDerived T) (hc : HasTy c T) :
    (∀ v, HasTy v T → smatch c v = teq T c v) ↔ NoNanNoZeroLeaf c := …
```

#### `ConstPat.optFlt_none_agrees`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:451-454
theorem optFlt_none_agrees :
    ¬ NoFloat (.sum .derived .int .flt) ∧
      ∀ v, HasTy v (.sum .derived .int .flt) →
        smatch (.inl (.int 0)) v = teq (.sum .derived .int .flt) (.inl (.int 0)) v := …
```

#### `ConstPat.manualVariantTy_not_allDerived_and_iff_fails`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:489-490
theorem manualVariantTy_not_allDerived_and_iff_fails :
    ¬ AllDerived manualVariantTy ∧ ¬ (LoweringAgrees manualVariantTy ↔ NoFloat manualVariantTy) := …
```

#### `Accessor.resultStable_and_stateIdempotent_of_pure`

```lean
-- lean/ToyMatchGuard/Accessor.lean:179-180
theorem resultStable_and_stateIdempotent_of_pure (acc : Acc σ S R) (h : Pure acc) :
    ResultStable acc ∧ StateIdempotent acc := …
```

#### `Accessor.countAcc_same_selection_different_state`

```lean
-- lean/ToyMatchGuard/Accessor.lean:228-233
theorem countAcc_same_selection_different_state :
    ResultStable countAcc ∧ ¬ StateIdempotent countAcc ∧
      (shared countAcc () [fun _ => false, fun _ => true] 0).1 =
        (repeated countAcc () [fun _ => false, fun _ => true] 0 0).1 ∧
      (shared countAcc () [fun _ => false, fun _ => true] 0).2 = 1 ∧
      (repeated countAcc () [fun _ => false, fun _ => true] 0 0).2 = 2 := …
```

#### `Accessor.flagAcc_stable_idempotent_not_pure`

```lean
-- lean/ToyMatchGuard/Accessor.lean:241-242
theorem flagAcc_stable_idempotent_not_pure :
    ResultStable flagAcc ∧ StateIdempotent flagAcc ∧ ¬ Pure flagAcc := …
```

#### `Accessor.constFalseAcc_resultStable_not_wellTyped_and_iff_fails`

```lean
-- lean/ToyMatchGuard/Accessor.lean:251-256
theorem constFalseAcc_resultStable_not_wellTyped_and_iff_fails :
    ResultStable constFalseAcc ∧ ¬ WellTyped (fun r => r = true) constFalseAcc ∧
      ExhaustiveOn (fun r => r = true) [fun r => r] ∧
      (repeated constFalseAcc () [fun r => r] 0 ()).1 = none ∧
      ¬ ((∀ arms, ExhaustiveOn (fun r => r = true) arms → ∀ s st,
            (repeated constFalseAcc s arms 0 st).1 ≠ none) ↔ ResultStable constFalseAcc) := …
```

#### `Accessor.idAcc_pure_wellTyped`

```lean
-- lean/ToyMatchGuard/Accessor.lean:265-265
theorem idAcc_pure_wellTyped : Pure idAcc ∧ WellTyped (fun _ => True) idAcc := …
```

#### `Accessor.countedBoolAcc_resultStable_not_stateIdempotent_not_pure`

```lean
-- lean/ToyMatchGuard/Accessor.lean:276-278
theorem countedBoolAcc_resultStable_not_stateIdempotent_not_pure :
    ResultStable countedBoolAcc ∧ ¬ StateIdempotent countedBoolAcc ∧ ¬ Pure countedBoolAcc ∧
      (countedBoolAcc 0 true).1 ≠ (countedBoolAcc 0 false).1 := …
```

#### `Accessor.loggedBoolAcc_resultStable_stateIdempotent_not_pure`

```lean
-- lean/ToyMatchGuard/Accessor.lean:285-287
theorem loggedBoolAcc_resultStable_stateIdempotent_not_pure :
    ResultStable loggedBoolAcc ∧ StateIdempotent loggedBoolAcc ∧ ¬ Pure loggedBoolAcc ∧
      (loggedBoolAcc false true).1 ≠ (loggedBoolAcc false false).1 := …
```

#### `Accessor.twoThenFlipAcc_stable_at_zero_and_repeated_reaches_unreachable`

```lean
-- lean/ToyMatchGuard/Accessor.lean:314-319
theorem twoThenFlipAcc_stable_at_zero_and_repeated_reaches_unreachable :
    (twoThenFlipAcc (twoThenFlipAcc 0 ()).2 ()).1 = (twoThenFlipAcc 0 ()).1 ∧
      WellTyped (fun _ => True) twoThenFlipAcc ∧ ¬ ResultStable twoThenFlipAcc ∧
      ExhaustiveOn (fun _ => True) threeBoolArms ∧
      (repeated twoThenFlipAcc () threeBoolArms 0 0).1 = none ∧
      (shared twoThenFlipAcc () threeBoolArms 0).1 = some 2 := …
```

#### `Accessor.shared_eq_repeated_of_unit_of_satisfiable`

```lean
-- lean/ToyMatchGuard/Accessor.lean:329-331
theorem shared_eq_repeated_of_unit_of_satisfiable (acc : Acc σ S Unit) (s : S) (st : σ)
    (arms : List (Unit → Bool)) (h : ∀ p ∈ arms, ∃ r, p r = true) :
    shared acc s arms st = repeated acc s arms 0 st := …
```

#### `Accessor.not_resultStable_example`

```lean
-- lean/ToyMatchGuard/Accessor.lean:344-344
theorem not_resultStable_example : ¬ ResultStable toggleAcc := …
```

### Definition examples (verbatim)

#### `lookup_example_some`

```lean
-- lean/ToyMatchGuard/Places.lean:136-137
theorem lookup_example_some :
    lookup (.box (vSome vTrue)) [.deref, .field 1 0] = some vTrue := …
```

#### `lookup_example_none`

```lean
-- lean/ToyMatchGuard/Places.lean:140-141
theorem lookup_example_none :
    lookup (.box vNone) [.deref, .field 1 0] = none := …
```

#### `writeOrSkip_example_inside`

```lean
-- lean/ToyMatchGuard/Places.lean:144-145
theorem writeOrSkip_example_inside :
    writeOrSkip (vSome (.int 0)) [.field 1 0] (.int 1) = vSome (.int 1) := …
```

#### `writeOrSkip_example_skip`

```lean
-- lean/ToyMatchGuard/Places.lean:148-149
theorem writeOrSkip_example_skip :
    writeOrSkip vNone [.field 1 0] (.int 1) = vNone := …
```

#### `headAt_example`

```lean
-- lean/ToyMatchGuard/Places.lean:152-152
theorem headAt_example : headAt (vSome (.int 3)) [] = some (.ctor 1) := …
```

#### `headAt_example_none`

```lean
-- lean/ToyMatchGuard/Places.lean:155-155
theorem headAt_example_none : headAt vNone [.field 1 0] = none := …
```

#### `reassignArms_exhaustive`

```lean
-- lean/ToyMatchGuard/Instances.lean:172-172
theorem reassignArms_exhaustive : Exhaustive RefOptBoolDom reassignArms := …
```

#### `boxBoolArms_exhaustive`

```lean
-- lean/ToyMatchGuard/Instances.lean:187-187
theorem boxBoolArms_exhaustive : Exhaustive BoxBoolDom boxBoolArms := …
```

#### `laterTestedArms_guardsPreserveDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:216-216
theorem laterTestedArms_guardsPreserveDom : GuardsPreserveDom OptBoolDom laterTestedArms := …
```

#### `illTypedArms_not_guardsPreserveDom`

```lean
-- lean/ToyMatchGuard/Instances.lean:227-227
theorem illTypedArms_not_guardsPreserveDom : ¬ GuardsPreserveDom OptBoolDom illTypedArms := …
```

#### `reassignArms_take3_not_exhaustive`

```lean
-- lean/ToyMatchGuard/Instances.lean:296-296
theorem reassignArms_take3_not_exhaustive : ¬ Exhaustive RefOptBoolDom (reassignArms.take 3) := …
```

#### `guarded_arm_not_counted`

```lean
-- lean/ToyMatchGuard/Instances.lean:308-311
theorem guarded_arm_not_counted :
    ¬ Exhaustive OptIntDom
      [ { tests := [.switch [] (.ctor 1)], guard := some { writes := [], cond := fun _ _ => true } },
        { tests := [.switch [] (.ctor 0)] } ] := …
```

#### `shallowGuardArms_shallowFrozenAll`

```lean
-- lean/ToyMatchGuard/Instances.lean:320-320
theorem shallowGuardArms_shallowFrozenAll : ShallowFrozenAll shallowGuardArms := …
```

#### `reassignArms_not_shallowFrozenAll`

```lean
-- lean/ToyMatchGuard/Instances.lean:323-323
theorem reassignArms_not_shallowFrozenAll : ¬ ShallowFrozenAll reassignArms := …
```

#### `pairBoxArms_deepFrozenAll`

```lean
-- lean/ToyMatchGuard/Instances.lean:327-327
theorem pairBoxArms_deepFrozenAll : DeepFrozenAll pairBoxArms := …
```

#### `boxBoolArms_not_deepFrozenAll`

```lean
-- lean/ToyMatchGuard/Instances.lean:330-330
theorem boxBoolArms_not_deepFrozenAll : ¬ DeepFrozenAll boxBoolArms := …
```

#### `boxBoolArms_shallowFrozenDerefAll`

```lean
-- lean/ToyMatchGuard/Instances.lean:334-334
theorem boxBoolArms_shallowFrozenDerefAll : ShallowFrozenDerefAll boxBoolArms := …
```

#### `reassignBox_not_shallowFrozenDerefAll`

```lean
-- lean/ToyMatchGuard/Instances.lean:337-340
theorem reassignBox_not_shallowFrozenDerefAll :
    ¬ ShallowFrozenDerefAll
      [ { tests := [.derefSwitch [] [] (.ctor 1)] },
        { tests := [], guard := some { writes := [([], fun _ _ => .box vTrue)], cond := fun _ _ => false } } ] := …
```

#### `shallowGuardArms_not_deepFrozenSwitchAll`

```lean
-- lean/ToyMatchGuard/Instances.lean:352-352
theorem shallowGuardArms_not_deepFrozenSwitchAll : ¬ DeepFrozenSwitchAll shallowGuardArms := …
```

#### `laterTestedArms_shallowFrozenBefore`

```lean
-- lean/ToyMatchGuard/Instances.lean:357-357
theorem laterTestedArms_shallowFrozenBefore : ShallowFrozenBefore laterTestedArms := …
```

#### `reassignArms_not_shallowFrozenBefore`

```lean
-- lean/ToyMatchGuard/Instances.lean:360-360
theorem reassignArms_not_shallowFrozenBefore : ¬ ShallowFrozenBefore reassignArms := …
```

#### `pairBoxArms_deepFrozenBefore`

```lean
-- lean/ToyMatchGuard/Instances.lean:363-363
theorem pairBoxArms_deepFrozenBefore : DeepFrozenBefore pairBoxArms := …
```

#### `boxBoolArms_not_deepFrozenBefore`

```lean
-- lean/ToyMatchGuard/Instances.lean:366-366
theorem boxBoolArms_not_deepFrozenBefore : ¬ DeepFrozenBefore boxBoolArms := …
```

#### `reassignArms_noDerefPatterns`

```lean
-- lean/ToyMatchGuard/Instances.lean:396-396
theorem reassignArms_noDerefPatterns : NoDerefPatterns reassignArms := …
```

#### `boxBoolArms_not_noDerefPatterns`

```lean
-- lean/ToyMatchGuard/Instances.lean:399-399
theorem boxBoolArms_not_noDerefPatterns : ¬ NoDerefPatterns boxBoolArms := …
```

#### `runMatch_reassignArms_none`

```lean
-- lean/ToyMatchGuard/Instances.lean:402-402
theorem runMatch_reassignArms_none : (runMatch reassignArms (.box vNone)).selected = some 0 := …
```

#### `runMatch_laterTestedArms_someFalse`

```lean
-- lean/ToyMatchGuard/Instances.lean:407-408
theorem runMatch_laterTestedArms_someFalse :
    (runMatch laterTestedArms (vSome vFalse)).selected = some 2 := …
```

#### `runMatch_shallowGuardArms`

```lean
-- lean/ToyMatchGuard/Instances.lean:609-612
theorem runMatch_shallowGuardArms :
    (match runMatch shallowGuardArms (vSome (.int 41)) with
      | .arm i _ mem => decide (i = 0 ∧ mem = vSome (.int 42))
      | .unreachable _ => false) = true := …
```

#### `borrowck_shallowGuardArms`

```lean
-- lean/ToyMatchGuard/Checker.lean:81-81
theorem borrowck_shallowGuardArms : borrowck shallowGuardArms = true := …
```

#### `OrPat.matchAll_example`

```lean
-- lean/ToyMatchGuard/OrPat.lean:633-635
theorem matchAll_example :
    matchAll (.or (.pair (.bind 0) .wild) (.pair .wild (.bind 0))) (.pair (.int 1) (.int 2)) =
      [[(0, .int 1)], [(0, .int 2)]] := …
```

#### `OrPat.matchAll_example_none`

```lean
-- lean/ToyMatchGuard/OrPat.lean:638-638
theorem matchAll_example_none : matchAll (.inl .wild) (.inr (.int 1)) = [] := …
```

#### `OrPat.expand_example`

```lean
-- lean/ToyMatchGuard/OrPat.lean:641-644
theorem expand_example :
    expand (.pair (.or (.int 0) (.int 1)) (.or (.int 2) (.int 3))) =
      [.pair (.int 0) (.int 2), .pair (.int 0) (.int 3), .pair (.int 1) (.int 2),
        .pair (.int 1) (.int 3)] := …
```

#### `OrPat.declOrder_example`

```lean
-- lean/ToyMatchGuard/OrPat.lean:647-647
theorem declOrder_example : declOrder (refDropArms[0]).pat = [0, 1] := …
```

#### `OrPat.orFree_example`

```lean
-- lean/ToyMatchGuard/OrPat.lean:650-650
theorem orFree_example : OrFree (.pair (.bind 0) .wild) := …
```

#### `OrPat.not_orFree_example`

```lean
-- lean/ToyMatchGuard/OrPat.lean:653-653
theorem not_orFree_example : ¬ OrFree (.or .wild .wild) := …
```

#### `OrPat.sameDeclOrder_example`

```lean
-- lean/ToyMatchGuard/OrPat.lean:656-656
theorem sameDeclOrder_example : SameDeclOrder (.or (.inl (.bind 0)) (.inr (.bind 0))) := …
```

#### `OrPat.not_sameDeclOrder_example`

```lean
-- lean/ToyMatchGuard/OrPat.lean:660-661
theorem not_sameDeclOrder_example :
    ¬ SameDeclOrder (.or (.inl (.pair (.bind 0) (.bind 1))) (.inr (.pair (.bind 1) (.bind 0)))) := …
```

#### `OrPat.noDupBindings_example`

```lean
-- lean/ToyMatchGuard/OrPat.lean:665-666
theorem noDupBindings_example :
    NoDupBindings (.or (.inl (.pair (.bind 0) (.bind 1))) (.inr (.pair (.bind 1) (.bind 0)))) := …
```

#### `OrPat.not_noDupBindings_example`

```lean
-- lean/ToyMatchGuard/OrPat.lean:670-670
theorem not_noDupBindings_example : ¬ NoDupBindings (.pair (.bind 0) (.bind 0)) := …
```

#### `ConstPat.allDerived_example`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:461-461
theorem allDerived_example : AllDerived derivedTy := …
```

#### `ConstPat.not_allDerived_example`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:463-463
theorem not_allDerived_example : ¬ AllDerived manualVariantTy := …
```

#### `ConstPat.noFloat_example`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:465-465
theorem noFloat_example : NoFloat derivedTy := …
```

#### `ConstPat.not_noFloat_example`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:467-467
theorem not_noFloat_example : ¬ NoFloat (.prod .derived .int .flt) := …
```

#### `ConstPat.hasTy_example`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:469-469
theorem hasTy_example : HasTy (.inl (.int 3)) manualVariantTy := …
```

#### `ConstPat.not_hasTy_example`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:471-471
theorem not_hasTy_example : ¬ HasTy (.flt .one) manualVariantTy := …
```

#### `ConstPat.smatch_example`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:473-473
theorem smatch_example : smatch (.inr (.int 2)) (.inr (.int 2)) = true := …
```

#### `ConstPat.smatch_example_false`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:475-475
theorem smatch_example_false : smatch (.inl (.int 2)) (.inr (.int 2)) = false := …
```

#### `ConstPat.loweringAgrees_example`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:477-477
theorem loweringAgrees_example : LoweringAgrees derivedTy := …
```

#### `ConstPat.not_loweringAgrees_example`

```lean
-- lean/ToyMatchGuard/ConstPat.lean:481-481
theorem not_loweringAgrees_example : ¬ LoweringAgrees manualVariantTy := …
```

#### `Accessor.resultStable_example`

```lean
-- lean/ToyMatchGuard/Accessor.lean:342-342
theorem resultStable_example : ResultStable countedBoolAcc := …
```

#### `Accessor.stateIdempotent_example`

```lean
-- lean/ToyMatchGuard/Accessor.lean:347-347
theorem stateIdempotent_example : StateIdempotent flagAcc := …
```

#### `Accessor.not_stateIdempotent_example`

```lean
-- lean/ToyMatchGuard/Accessor.lean:349-349
theorem not_stateIdempotent_example : ¬ StateIdempotent countAcc := …
```

#### `Accessor.pure_example`

```lean
-- lean/ToyMatchGuard/Accessor.lean:352-352
theorem pure_example : Pure idAcc := …
```

#### `Accessor.not_pure_example`

```lean
-- lean/ToyMatchGuard/Accessor.lean:354-354
theorem not_pure_example : ¬ Pure flagAcc := …
```

#### `Accessor.wellTyped_example`

```lean
-- lean/ToyMatchGuard/Accessor.lean:356-356
theorem wellTyped_example : WellTyped (fun _ => True) toggleAcc := …
```

#### `Accessor.not_wellTyped_example`

```lean
-- lean/ToyMatchGuard/Accessor.lean:358-358
theorem not_wellTyped_example : ¬ WellTyped (fun r => r = true) constFalseAcc := …
```

#### `Accessor.exhaustiveOn_example`

```lean
-- lean/ToyMatchGuard/Accessor.lean:361-361
theorem exhaustiveOn_example : ExhaustiveOn (fun _ => True) boolResultArms := …
```

#### `Accessor.not_exhaustiveOn_example`

```lean
-- lean/ToyMatchGuard/Accessor.lean:363-363
theorem not_exhaustiveOn_example : ¬ ExhaustiveOn (fun _ => True) [fun r : Bool => r] := …
```

## Boundaries

### Non-claims

Non-claims first, per card. Each bullet is part of the card.

#### R1 — `runMatch_not_unreachable_of_exhaustive_of_shallowFrozenAll_of_deepFrozenAll` (theorem)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, or the Rust Reference. Model–system relation: none proved.
- `runMatch` is a toy in-order lowering (`runArms`): arms are tried in order; a switch reads a place's head at most once, and every later test of that place, in any later arm (including after a wildcard arm and after a guard), reuses the recorded result; a deref-pattern test reads through the box each time it is evaluated; after a failed guard, matching continues with the next arm on the memory the guard left. Lowerings that test places of later arms before an earlier guard, that read a switched place again after a guard (for example a backtracking automaton such as rustc's, B3), or that share deref results across a guard are not modelled; whether the hypotheses here suffice for them is not proved here (accessor sharing is treated separately, R16–R19).
- In the toy a test on a nonexistent place (for example a field of an inactive variant) fails, and a guard write to a nonexistent place is skipped; Rust would have undefined behaviour of another kind or would reject the program.
- The conclusion says that `runMatch arms v` does not return `.unreachable _`. When it returns `.arm i env mem`, the theorem does not say which arm `i` is selected, that the memory `mem` after the guards is in `Dom`, that arm `i` still matches `mem` directly, or that the bindings `env` agree with `mem` (not proved here); arm bodies are not modelled (R9 shows a selected arm running with a memory that a guard changed).
- Guard writes are a syntactic list of (place, value function); the written value may depend on the bindings and the current memory. Writes through aliases, raw pointers, interior mutability or calls are not modelled, and guard conditions are arbitrary Lean functions.
- In the toy, an arm's bindings (`Arm.binds`) are by-value reads (`bindEnv`) taken before the guard's writes run, and `ShallowFrozenAll`, `DeepFrozenAll`, `ShallowFrozenBefore`, `DeepFrozenBefore` and `borrowck` place no restriction on bound places. The Rust Reference says: "Before evaluating the guard, a shared reference is taken to the part of the scrutinee the variable matches on.", "Only when the guard evaluates successfully is the value moved, or copied, from the scrutinee into the variable.", and "Moreover, by holding a shared reference while evaluating the guard, mutation inside guards is also prevented." (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:175-182`); rustc also fake-borrows the dereference prefixes of bound places (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:195-227`). These theorems neither establish nor refute that a guard writing a bound place is sound or accepted; the witnesses `mixedStaticArms`, `mixedLaterTestedArms` and `shallowGuardArms` bind nothing.
- The hypotheses are sufficient, not necessary: there is an arm list, `sameVariantArms`, exhaustive on `OptIntDom`, that `borrowck` rejects (so, by R7, it does not satisfy both `ShallowFrozenAll` and `DeepFrozenAll`) and whose lowered execution reaches no `Unreachable` on any value of `OptIntDom` (`sameVariantArms_rejected_exhaustive_and_never_unreachable`).
- `Dom` is an arbitrary predicate on values; the theorem does not require guard writes to keep the memory in `Dom` (compare R2).

#### R2 — `runMatch_not_unreachable_of_exhaustive_of_guardsPreserveDom_of_frozenBefore` (theorem)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, or the Rust Reference. Model–system relation: none proved.
- `runMatch` is a toy in-order lowering (`runArms`): arms are tried in order; a switch reads a place's head at most once, and every later test of that place, in any later arm (including after a wildcard arm and after a guard), reuses the recorded result; a deref-pattern test reads through the box each time it is evaluated; after a failed guard, matching continues with the next arm on the memory the guard left. Lowerings that test places of later arms before an earlier guard, that read a switched place again after a guard (for example a backtracking automaton such as rustc's, B3), or that share deref results across a guard are not modelled; whether the hypotheses here suffice for them is not proved here (accessor sharing is treated separately, R16–R19).
- In the toy a test on a nonexistent place (for example a field of an inactive variant) fails, and a guard write to a nonexistent place is skipped; Rust would have undefined behaviour of another kind or would reject the program.
- The conclusion says that `runMatch arms v` does not return `.unreachable _`. When it returns `.arm i env mem`, the theorem does not say which arm `i` is selected, that the memory `mem` after the guards is in `Dom`, that arm `i` still matches `mem` directly, or that the bindings `env` agree with `mem` (not proved here); arm bodies are not modelled (R9 shows a selected arm running with a memory that a guard changed).
- Guard writes are a syntactic list of (place, value function); the written value may depend on the bindings and the current memory. Writes through aliases, raw pointers, interior mutability or calls are not modelled, and guard conditions are arbitrary Lean functions.
- In the toy, an arm's bindings (`Arm.binds`) are by-value reads (`bindEnv`) taken before the guard's writes run, and `ShallowFrozenAll`, `DeepFrozenAll`, `ShallowFrozenBefore`, `DeepFrozenBefore` and `borrowck` place no restriction on bound places. The Rust Reference says: "Before evaluating the guard, a shared reference is taken to the part of the scrutinee the variable matches on.", "Only when the guard evaluates successfully is the value moved, or copied, from the scrutinee into the variable.", and "Moreover, by holding a shared reference while evaluating the guard, mutation inside guards is also prevented." (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:175-182`); rustc also fake-borrows the dereference prefixes of bound places (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:195-227`). These theorems neither establish nor refute that a guard writing a bound place is sound or accepted; the witnesses `mixedStaticArms`, `mixedLaterTestedArms` and `shallowGuardArms` bind nothing.
- "Earlier arm" means earlier in arm order. The toy lowering tests arms in order, so the places tested before a guard are those of its own and earlier arms; a decision procedure that tests places of later arms before a guard is not modelled.
- `GuardsPreserveDom` is required from every memory in `Dom` on which the guarded arm matches directly, whether or not the lowered execution can reach that guard with that memory (for example after earlier guards wrote other places); a variant of R2 that requires it from reachable memories alone is not proved here. Memories on which the arm does not match are unconstrained: `copyBoundFieldArms_guardsPreserveDom_and_unmatched_write_leaves_dom` shows a guard that reads its binding, satisfies `GuardsPreserveDom`, and would leave the domain if run from a memory its arm does not match.
- A place that no arm up to a guard's own switches on need not be frozen across that guard when every guard is well-typed (`GuardsPreserveDom`); without that hypothesis this per-guard form fails (`illTypedArms_exhaustive_frozenBefore_and_reaches_unreachable`), while the static form R1, which also freezes such places, has no well-typedness hypothesis.

#### R3 — `reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable` (counterexample)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, or the Rust Reference. Model–system relation: none proved.
- The toy splits the last arm `Some(_)` of rustc's example into `Some(true)` and `Some(false)` so that a test runs after the guard. On the literal E0510 shape the toy lowering does not reach `Unreachable`: it selects the last arm from the recorded variant while the memory is `&None` (`e0510Arms_selects_last_arm_with_changed_memory`); the toy does not model what that arm body would then do.
- Reaching `Unreachable` here comes from the toy convention that a test on a nonexistent place (the field of `None`) fails.
- Reaching `Unreachable` relies on `runMatch` continuing with the next arm on the memory the guard left; a lowering that restarted matching from the first arm on the changed scrutinee, or that matched against an unchanged copy of the scrutinee, would not reach `Unreachable` on an exhaustive arm list (not proved here). rustc's backtracking-automaton lowering (B3) is not modelled; rustc's documentation shows the unsplit example rejected (E0510), and the split variant was not run through rustc.

#### R4 — `boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable` (counterexample)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, or the Rust Reference. Model–system relation: none proved.
- The counterexample relies on the toy lowering re-reading deref-pattern tests through the box after the guard; it says nothing about a lowering that shares the deref result across the guard (whether shallow freezing suffices for such a lowering is not proved here).
- In `boxBoolArms` the deref-pattern test `.derefSwitch [] [] h` records the deref-pattern scrutinee `[]` and reads the head of the pointee through the box; the pointee is not a place the freezing predicates see (mirroring rustc's `TestKind::Deref`, which calls `Deref::deref` and stores the result in a temporary, B6). A switch on `[.deref]`, as `reassignArms` uses for a reference, would make `[.deref]` a switched place, and `ShallowFrozenAll` would then forbid the guard's write to `[.deref]`.
- Reaching `Unreachable` relies on `runMatch` continuing with the next arm on the memory the guard left; a lowering that restarted matching from the first arm, or that matched against an unchanged copy of the scrutinee, would not reach `Unreachable` here (not proved here).
- Deref patterns are an unstable Rust feature (`deref_patterns`).

#### R5 — `runMatch_not_unreachable_of_noDerefPatterns_of_exhaustive_of_shallowFrozenAll` (theorem)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, or the Rust Reference. Model–system relation: none proved.
- `runMatch` is a toy in-order lowering (`runArms`): arms are tried in order; a switch reads a place's head at most once, and every later test of that place, in any later arm (including after a wildcard arm and after a guard), reuses the recorded result; a deref-pattern test reads through the box each time it is evaluated; after a failed guard, matching continues with the next arm on the memory the guard left. Lowerings that test places of later arms before an earlier guard, that read a switched place again after a guard (for example a backtracking automaton such as rustc's, B3), or that share deref results across a guard are not modelled; whether the hypotheses here suffice for them is not proved here (accessor sharing is treated separately, R16–R19).
- In the toy a test on a nonexistent place (for example a field of an inactive variant) fails, and a guard write to a nonexistent place is skipped; Rust would have undefined behaviour of another kind or would reject the program.
- The conclusion says that `runMatch arms v` does not return `.unreachable _`. When it returns `.arm i env mem`, the theorem does not say which arm `i` is selected, that the memory `mem` after the guards is in `Dom`, that arm `i` still matches `mem` directly, or that the bindings `env` agree with `mem` (not proved here); arm bodies are not modelled (R9 shows a selected arm running with a memory that a guard changed).
- In the toy, an arm's bindings (`Arm.binds`) are by-value reads (`bindEnv`) taken before the guard's writes run, and `ShallowFrozenAll`, `DeepFrozenAll`, `ShallowFrozenBefore`, `DeepFrozenBefore` and `borrowck` place no restriction on bound places. The Rust Reference says: "Before evaluating the guard, a shared reference is taken to the part of the scrutinee the variable matches on.", "Only when the guard evaluates successfully is the value moved, or copied, from the scrutinee into the variable.", and "Moreover, by holding a shared reference while evaluating the guard, mutation inside guards is also prevented." (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:175-182`); rustc also fake-borrows the dereference prefixes of bound places (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:195-227`). These theorems neither establish nor refute that a guard writing a bound place is sound or accepted; the witnesses `mixedStaticArms`, `mixedLaterTestedArms` and `shallowGuardArms` bind nothing.
- Within the toy, the theorem covers every deref-free arm list; it says nothing about pattern shapes the toy does not have (slices, ranges, string literals, bindings by reference).
- R6 shows that freezing the switched places deeply (`DeepFrozenSwitchAll`) would reject `shallowGuardArms`.

#### R6 — `shallowFrozenAll_of_deepFrozenSwitchAll_strict_on_shallowGuardArms` (theorem)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, or the Rust Reference. Model–system relation: none proved.
- That shallow freezing accepts strictly more arm lists than deep freezing of switched places is witnessed by one arm list; no count or measure of accepted guards is claimed.
- The witness's guard computes `*y += 1` on the toy's unbounded integers (`Int`); overflow is not modelled.
- R6 compares two freezing predicates of the toy; it says nothing about which one rustc's borrow checker implements beyond the documented placement (B1).

#### R7 — `borrowck_eq_true_iff` (characterization)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, or the Rust Reference. Model–system relation: none proved.
- `borrowck` is a decision procedure for the toy predicates; it is not rustc's borrow checker. It checks syntactic guard write places against `fakeBorrows arms` and ignores bindings, two-phase borrows, liveness, and writes through aliases (B1).
- `fakeBorrows` contains no borrow of bound places, unlike rustc's `collect_fake_borrows` (B1).

#### R8 — `runMatch_not_unreachable_of_borrowck_of_exhaustive` (theorem)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, or the Rust Reference. Model–system relation: none proved.
- `runMatch` is a toy in-order lowering (`runArms`): arms are tried in order; a switch reads a place's head at most once, and every later test of that place, in any later arm (including after a wildcard arm and after a guard), reuses the recorded result; a deref-pattern test reads through the box each time it is evaluated; after a failed guard, matching continues with the next arm on the memory the guard left. Lowerings that test places of later arms before an earlier guard, that read a switched place again after a guard (for example a backtracking automaton such as rustc's, B3), or that share deref results across a guard are not modelled; whether the hypotheses here suffice for them is not proved here (accessor sharing is treated separately, R16–R19).
- In the toy a test on a nonexistent place (for example a field of an inactive variant) fails, and a guard write to a nonexistent place is skipped; Rust would have undefined behaviour of another kind or would reject the program.
- The conclusion says that `runMatch arms v` does not return `.unreachable _`. When it returns `.arm i env mem`, the theorem does not say which arm `i` is selected, that the memory `mem` after the guards is in `Dom`, that arm `i` still matches `mem` directly, or that the bindings `env` agree with `mem` (not proved here); arm bodies are not modelled (R9 shows a selected arm running with a memory that a guard changed).
- Guard writes are a syntactic list of (place, value function); the written value may depend on the bindings and the current memory. Writes through aliases, raw pointers, interior mutability or calls are not modelled, and guard conditions are arbitrary Lean functions.
- In the toy, an arm's bindings (`Arm.binds`) are by-value reads (`bindEnv`) taken before the guard's writes run, and `ShallowFrozenAll`, `DeepFrozenAll`, `ShallowFrozenBefore`, `DeepFrozenBefore` and `borrowck` place no restriction on bound places. The Rust Reference says: "Before evaluating the guard, a shared reference is taken to the part of the scrutinee the variable matches on.", "Only when the guard evaluates successfully is the value moved, or copied, from the scrutinee into the variable.", and "Moreover, by holding a shared reference while evaluating the guard, mutation inside guards is also prevented." (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:175-182`); rustc also fake-borrows the dereference prefixes of bound places (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/util.rs:195-227`). These theorems neither establish nor refute that a guard writing a bound place is sound or accepted; the witnesses `mixedStaticArms`, `mixedLaterTestedArms` and `shallowGuardArms` bind nothing.
- *Soundness of the toy borrow check* in this card means the stated conclusion: acceptance by `borrowck` and exhaustiveness on `Dom` imply that `runMatch arms v` does not reach `Unreachable` for `v` in `Dom`. It is not soundness of rustc's borrow checker, and it covers none of the borrows of bound places that rustc also inserts (B1).

#### R9 — `sameVariantArms_rejected_exhaustive_and_never_unreachable` (counterexample)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's match lowering, rustc's borrow checker, or the Rust Reference. Model–system relation: none proved.
- Incompleteness is witnessed by one arm list; no characterization of the matches that reach no `Unreachable` is claimed.
- R9 does not say that a same-variant reassignment in a guard is harmless beyond not reaching `Unreachable`: the guard's write changes the memory the selected arm runs with (on `Some(0)`, arm `2` is selected with memory `Some(5)`, `runMatch_sameVariantArms_some0`). `sameVariantArms` has no bindings and the toy has no arm bodies; a binding of `(x as Some).0` in a later arm, or an arm body reading `x`, would observe `5` (not modelled).

#### R10 — `OrPat.runSrc_eq_runSplit_splitArms` (theorem)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about the Rust Reference's or-pattern semantics or rustc's match lowering. Model–system relation: none proved.
- Guards are functions of the bindings whose every evaluation is an observable event; guards cannot write the scrutinee, and bindings are by value.
- `OrPat.Pat` does not enforce the Reference's static rules that the alternatives of `p | q` introduce the same set of bindings (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:1024-1031`) and that an identifier is unique within a pattern (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:175-176`). On patterns violating them, `runSrc` and `runSplit` still agree (both use `dropsInOrder (declOrder a.pat)` under `firstAlternative`), but the drop events are not those of any Rust program: `dupBindArms_sameDeclOrder_not_noDupBindings_and_policies_differ` shows `firstAlternative` dropping the first value of `(x, x)` twice, and `unbalancedOrArms_firstAlternative_omits_drop` shows `firstAlternative` emitting no drop for the binding of `Ok(_) | Err(x)`.
- `expand` distributes pairs over or-patterns eagerly (a tuple of `n` two-way or-patterns has `2^n` alternatives; `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07:text/2535-or-patterns.md:628-664` shows the 16 alternatives of `(0 | 1, 0 | 1, 0 | 1, 0 | 1)`), and `runSplit` emits the body event and the drops inside each sub-branch. R10 says nothing about code size, or about sub-branches that "jump together to a common block" as rustc's do (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:509-513`; rustc avoids eager expansion, `:2094-2097`).
- `expand`'s left-to-right lexicographic order matches repeated use of the Reference's rule that matching `c(p | q, ..rest)` is matching `c(p, ..rest) | c(q, ..rest)` (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/patterns.md:1044-1045`) together with left-to-right testing of `|` alternatives (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:83-84`); whether rustc's lowering, which tests remaining or-patterns after each sub-candidate (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:2094-2149`), evaluates guards in the same order for every nested pattern is not proved here.
- The supporting lemma `matchAll_eq_flatMap_expand` (or-pattern matching enumerates the matches of the expanded alternatives, in order) is a statement about the toy's `matchAll` and `expand`.

#### R11 — `OrPat.runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms` (counterexample)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about the Rust Reference's or-pattern semantics or rustc's match lowering. Model–system relation: none proved.
- Both counterexamples use overlapping alternatives: an arm whose pattern matches the value in two ways. The positive control shows that when every arm's pattern matches the value at hand in at most one way, the two lowerings give the same trace.
- In the toy every guard evaluation is an observable event; `constGuardArms` differs by the number of guard events although its guard ignores the bindings.
- R11 does not say that rustc evaluates guards once: the Reference says the guard may execute multiple times (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/expressions/match-expr.md:159-170`), and rustc gives each sub-branch its own copy of the guard (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_mir_build/src/builder/matches/mod.rs:509-513`).
- Guards are functions of the bindings whose every evaluation is an observable event; guards cannot write the scrutinee, and bindings are by value.

#### R12 — `OrPat.runSrc_firstAlternative_eq_matchedAlternative_of_noDupBindings_of_sameDeclOrder` (theorem)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about the Rust Reference's or-pattern semantics or rustc's match lowering. Model–system relation: none proved.
- The Reference's drop rule corresponds to the `firstAlternative` policy (B4); R12 says when the `matchedAlternative` policy would give the same trace. `SameDeclOrder` implies that the alternatives bind the same names, and `NoDupBindings` is the toy form of the Reference's uniqueness rule (B4); the theorem does not require Rust's other static rules (types, binding modes).
- The converse fails: `shadowedSwapArms_not_sameDeclOrder_and_policies_agree` (the positive control of this card).
- Guards are functions of the bindings whose every evaluation is an observable event; guards cannot write the scrutinee, and bindings are by value.

#### R13 — `OrPat.runSplit_matchedAlternative_ne_runSrc_firstAlternative_refDropArms` (counterexample)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about the Rust Reference's or-pattern semantics or rustc's match lowering. Model–system relation: none proved.
- R13 follows in one step from R10 (with the `matchedAlternative` policy) and the explicit traces of `refDropArms_noDupBindings_not_sameDeclOrder_and_policies_differ`; it is stated separately because it names the lowering that would be wrong under the Reference's drop rule.
- R13 says nothing about rustc's drop order beyond the documented correspondence (B4).

#### R14 — `ConstPat.loweringAgrees_of_allDerived_of_noFloat` (theorem)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's constant patterns, `StructuralPartialEq`, or rustc's lowering of constant patterns. Model–system relation: none proved.
- `smatch` compares float leaves by bit pattern. rustc lowers a float constant pattern to an `==` comparison (`TestKind::ScalarEq`, then `BinOp::Eq`; B5), and RFC 1445 records that match compares `0.0` and `-0.0` as equal. For a structural lowering whose float-leaf test is the float `==` itself, the `NoFloat` hypothesis would not be needed for agreement with a derived `==` (not proved here). These results neither establish nor refute anything about rustc's comparison of float constants.
- `LoweringAgrees T`, `AllDerived T` and `NoFloat T` are conditions on the whole type: `LoweringAgrees T` quantifies over every constant of `T`, including `nan`-containing constants (which the Reference does not allow as patterns, B5) and constants of every variant, and `AllDerived T` and `NoFloat T` inspect every node of `T`, including variants a given constant does not use. The Reference's condition is on the value of the constant (B5). For one fixed constant `c` of an all-derived type, `smatch_agrees_with_teq_iff_noNanNoZeroLeaf_of_allDerived` shows agreement on every scrutinee iff `c` has no `nan`, `+0` or `-0` leaf (`NoNanNoZeroLeaf c`); for example the constant `inl 0` agrees on the type `.sum .derived .int .flt`, which has a float leaf (`optFlt_none_agrees`).
- Requiring a derived `==` at every node of the type matters: `nestedManualTy_lowering_disagrees` shows a type with a derived `==` at the top, no float leaf, and a manual `==` one level down, on which the lowering and `==` disagree.
- `AllDerived` is a syntactic marker; it is not necessary for agreement: `manualStructuralTy_loweringAgrees_and_not_allDerived` shows a manual `==` that happens to be structural and agrees.

#### R15 — `ConstPat.loweringAgrees_iff_noFloat_of_allDerived` (characterization)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's constant patterns, `StructuralPartialEq`, or rustc's lowering of constant patterns. Model–system relation: none proved.
- `smatch` compares float leaves by bit pattern. rustc lowers a float constant pattern to an `==` comparison (`TestKind::ScalarEq`, then `BinOp::Eq`; B5), and RFC 1445 records that match compares `0.0` and `-0.0` as equal. For a structural lowering whose float-leaf test is the float `==` itself, the `NoFloat` hypothesis would not be needed for agreement with a derived `==` (not proved here). These results neither establish nor refute anything about rustc's comparison of float constants.
- `LoweringAgrees T`, `AllDerived T` and `NoFloat T` are conditions on the whole type: `LoweringAgrees T` quantifies over every constant of `T`, including `nan`-containing constants (which the Reference does not allow as patterns, B5) and constants of every variant, and `AllDerived T` and `NoFloat T` inspect every node of `T`, including variants a given constant does not use. The Reference's condition is on the value of the constant (B5). For one fixed constant `c` of an all-derived type, `smatch_agrees_with_teq_iff_noNanNoZeroLeaf_of_allDerived` shows agreement on every scrutinee iff `c` has no `nan`, `+0` or `-0` leaf (`NoNanNoZeroLeaf c`); for example the constant `inl 0` agrees on the type `.sum .derived .int .flt`, which has a float leaf (`optFlt_none_agrees`).
- The `→` direction builds, for an all-derived type with a float leaf, a constant containing `nan` that is not `teq`-equal to itself (`exists_teq_self_false_of_allDerived_of_not_noFloat`); it uses `hasTy_inhabit`: every toy type has a value, so every component of a product or sum does. The toy has no uninhabited types; with an uninhabited component (such as `!` or an empty enum) a float leaf that no value reaches would make `NoFloat` fail while agreement holds, so the `→` direction would fail (not proved here).
- Outside `AllDerived`, agreement does not determine `NoFloat` either way: `manualStructuralTy_loweringAgrees_and_not_allDerived` shows agreement without `AllDerived`, and `manualVariantTy_not_allDerived_and_iff_fails` shows the equivalence failing.

#### R16 — `Accessor.shared_selected_eq_repeated_selected_iff_resultStable` (characterization)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's `Deref`/`DerefPure` or rustc's deref-pattern lowering. Model–system relation: none proved.
- `ResultStable` is required from every hidden state, reachable or not. Two-call result stability from one fixed initial state does not suffice: from hidden state `0`, a second call of `twoThenFlipAcc` returns the same result as the first, yet on the exhaustive arm list `threeBoolArms` (exactly three arms) from state `0` the repeated lowering reaches `Unreachable` while the shared lowering selects arm `2` (`twoThenFlipAcc_stable_at_zero_and_repeated_reaches_unreachable`).
- Toy accessors cannot modify the scrutinee, and their hidden state is threaded through the calls of one match; interior mutability shared with guards, or mutation of the scrutinee between calls, is not modelled.
- `ResultStable` is one precise reading of the informal `DerefPure` requirement (B6); R16 does not say which reading rustc relies on.
- On a result type with one value, such as `Unit`, every accessor is result-stable (immediate from the definition of `ResultStable`; not stated as a separate theorem), so the equivalence carries no information there; the non-vacuity witness has result type `Bool`.

#### R17 — `Accessor.shared_eq_repeated_iff_resultStable_and_stateIdempotent` (characterization)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's `Deref`/`DerefPure` or rustc's deref-pattern lowering. Model–system relation: none proved.
- `ResultStable` and `StateIdempotent` are required from every hidden state, reachable or not. Two-call result stability alone from one fixed initial state does not suffice: from hidden state `0`, a second call of `twoThenFlipAcc` returns the same result as the first, yet on the exhaustive arm list `threeBoolArms` (exactly three arms) from state `0` the repeated lowering reaches `Unreachable` while the shared lowering selects arm `2` (`twoThenFlipAcc_stable_at_zero_and_repeated_reaches_unreachable`).
- Toy accessors cannot modify the scrutinee, and their hidden state is threaded through the calls of one match; interior mutability shared with guards, or mutation of the scrutinee between calls, is not modelled.
- The `→` direction for `StateIdempotent` uses the arm list `[fun _ => false, fun _ => true]`, whose first predicate holds of no result. On a result type with one value this is essential: for every accessor with result type `Unit` and every arm list each of whose predicates holds of some result, the two lowerings agree, including the final hidden state (`shared_eq_repeated_of_unit_of_satisfiable`), although `countAcc` is not state-idempotent (`countAcc_same_selection_different_state`).
- `shared` makes no accessor call when `arms = []`; a shared lowering that called the accessor before checking for an empty arm list would differ from `repeated` on `[]` whenever that call changes the hidden state (not proved here).
- Strict purity is sufficient (`resultStable_and_stateIdempotent_of_pure`) and not necessary (`flagAcc_stable_idempotent_not_pure`, and the non-vacuity witness `loggedBoolAcc`).

#### R18 — `Accessor.repeated_not_unreachable_on_exhaustiveOn_iff_resultStable_of_wellTyped` (characterization)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's `Deref`/`DerefPure` or rustc's deref-pattern lowering. Model–system relation: none proved.
- `ResultStable` is required from every hidden state, reachable or not. Two-call result stability from one fixed initial state does not suffice: from hidden state `0`, a second call of `twoThenFlipAcc` returns the same result as the first, yet on the exhaustive arm list `threeBoolArms` (exactly three arms) from state `0` the repeated lowering reaches `Unreachable` while the shared lowering selects arm `2` (`twoThenFlipAcc_stable_at_zero_and_repeated_reaches_unreachable`).
- Toy accessors cannot modify the scrutinee, and their hidden state is threaded through the calls of one match; interior mutability shared with guards, or mutation of the scrutinee between calls, is not modelled.
- The `→` direction uses, for an unstable accessor, an exhaustive arm list with exactly two arms built from the accessor's second result; R18 does not say that every exhaustive arm list exposes an unstable accessor.

#### R19 — `Accessor.toggleAcc_repeated_reaches_unreachable` (counterexample)

- These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust's `Deref`/`DerefPure` or rustc's deref-pattern lowering. Model–system relation: none proved.
- Escape hatches: a lowering that calls the accessor once and shares the result (`shared`) does not reach `Unreachable` here, and an accessor that is result-stable makes the repeated lowering agree with it (R16, R18).
- Toy accessors cannot modify the scrutinee, and their hidden state is threaded through the calls of one match; interior mutability shared with guards, or mutation of the scrutinee between calls, is not modelled.

### Escape hatches

For each hypothesis of a theorem card the ledger names a counterexample in which all other hypotheses hold and the conclusion fails, so dropping that hypothesis defeats the theorem as stated; it is not claimed that every weakening of a hypothesis does. Settings in which a counterexample card's conclusion does not arise, and hypotheses shown sufficient but not necessary:

- R3 and R4 rely on `runMatch` continuing with the next arm on the memory the guard left. A lowering that restarted matching from the first arm, or matched against an unchanged copy of the scrutinee, would not reach `Unreachable` on these exhaustive arm lists (not proved here). R4 also relies on deref-pattern tests re-reading through the box after the guard; a lowering that shares the deref result across the guard is not covered (not proved here).
- R11: when every arm's pattern matches the value in at most one way, the guard-once lowering gives the source trace (`runGuardOnce_eq_runSrc_of_matchAll_length_le_one`, proved).
- R12's hypotheses are sufficient, not necessary (`shadowedSwapArms_not_sameDeclOrder_and_policies_agree`, proved).
- R19: the shared lowering does not reach `Unreachable` on the same instance (part of the theorem), and a result-stable accessor makes the repeated lowering agree with the shared one (R16, R18).
- R1's two freezing hypotheses jointly, and R8's acceptance hypothesis, are sufficient, not necessary: `borrowck` rejects `sameVariantArms`, which is exhaustive on `OptIntDom` and never reaches `Unreachable` on it (R9); by R7 it does not satisfy both `ShallowFrozenAll` and `DeepFrozenAll`. Whether R2's or R5's hypotheses are necessary is not addressed (not proved either way).

### Hypotheses whose tightness is `unknown`

None: every hypothesis in every ledger is `tight`, with a counterexample theorem stating that all other hypotheses hold and the conclusion fails.

### Dropped or disproved statements

None. All 19 cards are fully proved as stated; no statement of this package was found false or left unproved, and no theorem of the package refutes an earlier candidate statement.

## Evidence

Kernel check (`execution (Lean kernel check)`): `lake build` of `lean/` with `leanprover/lean4:v4.34.1`; Lean's `collectAxioms` over all 1049 declarations of the library reports at most `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `partial`, `implemented_by` or `@[extern]` declaration occurs. Statement hash = SHA-256 of the Lean `repr` of the declaration's type; closure hash = SHA-256 of the sorted `name : type := value` texts of every package-local constant reachable from the statement (theorem bodies excluded). Both are recorded in `audit/statements.json` (273 declarations: every Lean name referenced by `results.json`), the per-declaration axioms in `audit/axioms.json`. Observed 2026-11-22.

### Main results (card `lean` fields)

| Card | Theorem | Axioms | Statement SHA-256 | Closure SHA-256 |
|---|---|---|---|---|
| R1 | `runMatch_not_unreachable_of_exhaustive_of_shallowFrozenAll_of_deepFrozenAll` | `Quot.sound`, `propext` | `e49b1d4366836d43e7bb89ab504e5d3fda4347d66732c46d5452a963cc2aefe1` | `6c442a39c4d887e540e41dc685d9f6fb8a76159e8b1bc101a260f63b1ef8e8c3` |
| R2 | `runMatch_not_unreachable_of_exhaustive_of_guardsPreserveDom_of_frozenBefore` | `Classical.choice`, `Quot.sound`, `propext` | `4d4e8a09631bda4ac8d8dc4f5d0924776f9944894e812e6a1626de4a9b28858e` | `8117e46ed24304e603f3db2f397ee35e78a4a7a62eae664948faeec761ec1b27` |
| R3 | `reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable` | `Quot.sound`, `propext` | `6c0a51d6b8c9ffa672c9a1865be06b67cc0156f63d0f485ac92b3e3f5dd344fa` | `9bf99a3bf4bb1d73f13a24a6a4c2fce9c6e660b5d5e6634a2a232771b30b442b` |
| R4 | `boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable` | `Quot.sound`, `propext` | `c88fbde7e2cfb540d597745b278fdd3becd73a40c8f7107aeb278999f16cd50e` | `cb524df3aef1bd75f56aa56c3e6f73ea3e3ff22f77d6ea4bf0c2154d734c5ad4` |
| R5 | `runMatch_not_unreachable_of_noDerefPatterns_of_exhaustive_of_shallowFrozenAll` | `Quot.sound`, `propext` | `8965702cb2d314bffdf37342463e6bb2506523f3b920e5485b99a9f6268e0813` | `605428fceff6cd66d7c9fbe8a6b60f430c3fd73d7600a4e90c85331d09acc102` |
| R6 | `shallowFrozenAll_of_deepFrozenSwitchAll_strict_on_shallowGuardArms` | `Quot.sound`, `propext` | `55cf9dbbf32a9ab2d3cef5194abbaaecc9a6bc7bdfa5c15356318c03f5c2731a` | `c52a9cc7a34cf509452e2b5953c947d650511053574a783fa134502aa1445ef7` |
| R7 | `borrowck_eq_true_iff` | `Quot.sound`, `propext` | `1dea727eaa91da3cace7af1fc38ad8d33e057d552072c9f23bf5b324863841c1` | `1e3c679c1b8fbb50256adfecdf615decd56ab4d822f1f5ae6edfad568c37632c` |
| R8 | `runMatch_not_unreachable_of_borrowck_of_exhaustive` | `Quot.sound`, `propext` | `635290aad77f7cf16a94792d986868a73962cbdafa7b9e632d0f406293f036f5` | `7acb6f75ea3be80210db487d273be913a48a0562833d422c15b5f70dcf68ac31` |
| R9 | `sameVariantArms_rejected_exhaustive_and_never_unreachable` | `propext` | `38059e10a33d9a86d996892f42e955247f82878b91b81a025618486540bb9ba3` | `f196e8d2f6692acbf863edd6e95d89f1865b95e86b2efedf152dd1cadff0fbab` |
| R10 | `OrPat.runSrc_eq_runSplit_splitArms` | `Quot.sound`, `propext` | `1fa14bf72d5cc9b0f1386e8a3598174f5c8b7c3db14dfe4914c71e1a27730dd1` | `4d344fdec129bf947896de6efef07ba65fe520a3205e8f9ab025843c1d8f517d` |
| R11 | `OrPat.runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms` | `propext` | `d68425f85ac62fd1b94b1c9c3da43c6fccd267744ee859ab25025b39ae7ae831` | `efb2f62bb464ff1fc1f0e056d3c7f166d3932fe1a1700f017d55d2bbe080e300` |
| R12 | `OrPat.runSrc_firstAlternative_eq_matchedAlternative_of_noDupBindings_of_sameDeclOrder` | `Classical.choice`, `Quot.sound`, `propext` | `c4f1709aab348e254781f2e0e53829d9259cda733eabf3743b6c1cbf89a34887` | `c6582d283d221e14e05192e2f742e9644603c6dad73c853c8d5de8e4bf7d76a5` |
| R13 | `OrPat.runSplit_matchedAlternative_ne_runSrc_firstAlternative_refDropArms` | `propext` | `c76946650c6e215fd22c4f18318db2add148edd5dded15f4ee97e5104859b4b5` | `d181e23deaa3ed51234bd6a86ccab9b9a7c6f5126544bf3a9006e478382464e8` |
| R14 | `ConstPat.loweringAgrees_of_allDerived_of_noFloat` | `propext` | `b31cb5e1287e59a336b7288960fadc32d050b6c85685b5dbc06e267ea7778f8b` | `51d089272b72b664b9a20f781bba9d05269e340e2892c78a0c66cf4dae5aa786` |
| R15 | `ConstPat.loweringAgrees_iff_noFloat_of_allDerived` | `Classical.choice`, `Quot.sound`, `propext` | `a626958c69f189632346561ee5d6a5c0aa5b0b2035ffd0f5fa8d5187ab10b83e` | `51d089272b72b664b9a20f781bba9d05269e340e2892c78a0c66cf4dae5aa786` |
| R16 | `Accessor.shared_selected_eq_repeated_selected_iff_resultStable` | `Classical.choice`, `Quot.sound`, `propext` | `4e9571b278449bf803bc65a60f9c441a3976a86cc5931780dc209c58c03f6ec3` | `6d8bed6f11746b73b2a68bda075b8247e1717805f94ef776301bbe39124b66f5` |
| R17 | `Accessor.shared_eq_repeated_iff_resultStable_and_stateIdempotent` | `Classical.choice`, `Quot.sound`, `propext` | `88372f9b6b5a750a9fe025a537aa1373d2a80cb9e86ce7ad0d2b5a7352968ed9` | `b46407cdd7c9286168b9c926b52cb4a9dbaf73bf6f726b2b9059144090f3c759` |
| R18 | `Accessor.repeated_not_unreachable_on_exhaustiveOn_iff_resultStable_of_wellTyped` | `Classical.choice`, `Quot.sound`, `propext` | `0801e80aa3eb30fde09ab6b287eee58a9699bc9710a5ee21e08f09cff023a60d` | `9b36ce84476f35ea206f556e67cd41781b03a9a7f03049ec6e94056e17bdb56b` |
| R19 | `Accessor.toggleAcc_repeated_reaches_unreachable` | none | `251c3d567c3d2394c8fab0f0a81a1ca72d9ce375acb6b048d064b44852e8e2d2` | `a13c5eefb6f40a64b1d9d7df8f7597abc74f53902fac8313f3e5ce601583191a` |

### Non-vacuity witnesses, positive controls and tightness counterexamples

| Card | Role | Declaration | Axioms | Statement SHA-256 | Closure SHA-256 |
|---|---|---|---|---|---|
| R1 | non-vacuity | `mixedStaticArms_satisfy_static_hypotheses` | `Quot.sound`, `propext` | `93766213a3273aa87f19e3f46469a90050ba2fe494ea6470eb1db54ba2528807` | `ac9c64ab763ba1b2bd2fabb2c6ae0fb450f8ff89777fdde641c45e9e08f7ac80` |
| R1 | counterexample for `hex : Exhaustive Dom arms` | `missingArms_frozen_not_exhaustive_and_reaches_unreachable` | `Quot.sound`, `propext` | `c52533dd93a5cf63d9743ed6c90665f48585b097abf5e38b34990586db3b2502` | `20f74ee1b311e1cbe9b67748aed5c6311322518ff6aa9490dd1ee4986d0b0688` |
| R1 | counterexample for `hs : ShallowFrozenAll arms` | `reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable` | `Quot.sound`, `propext` | `6c0a51d6b8c9ffa672c9a1865be06b67cc0156f63d0f485ac92b3e3f5dd344fa` | `9bf99a3bf4bb1d73f13a24a6a4c2fce9c6e660b5d5e6634a2a232771b30b442b` |
| R1 | counterexample for `hd : DeepFrozenAll arms` | `boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable` | `Quot.sound`, `propext` | `c88fbde7e2cfb540d597745b278fdd3becd73a40c8f7107aeb278999f16cd50e` | `cb524df3aef1bd75f56aa56c3e6f73ea3e3ff22f77d6ea4bf0c2154d734c5ad4` |
| R1 | counterexample for `hv : Dom v` | `boolArms_exhaustive_frozen_and_reaches_unreachable_outside_dom` | `Quot.sound`, `propext` | `5a67048e6fa6f1309d3e94d2895d5a8e66cd2e506f07f481fa41d39be77895b3` | `6808e017b126aaf386e354cfc815dc4fbd0924620a1f3caaac27bed6f3e99245` |
| R2 | non-vacuity | `mixedLaterTestedArms_satisfy_frozenBefore_hypotheses_and_not_shallowFrozenAll` | `Quot.sound`, `propext` | `95e34bf31683b7dbb063cdf112efaab26c9bb186236cf222debff58a01f55db4` | `ddff0aba9847048593431c01c372605c4d37e4bea619796ef594c5baa08ec638` |
| R2 | counterexample for `hex : Exhaustive Dom arms` | `missingArms_frozen_not_exhaustive_and_reaches_unreachable` | `Quot.sound`, `propext` | `c52533dd93a5cf63d9743ed6c90665f48585b097abf5e38b34990586db3b2502` | `20f74ee1b311e1cbe9b67748aed5c6311322518ff6aa9490dd1ee4986d0b0688` |
| R2 | counterexample for `hdom : GuardsPreserveDom Dom arms` | `illTypedArms_exhaustive_frozenBefore_and_reaches_unreachable` | `Quot.sound`, `propext` | `d566fd1cf7e81862d04f9fddfee1bc9b6db08564bab803348d5886a4891f0c21` | `e287d0355c539573d0109703188c7c235560c0ebb38cfef63e1d69b705f2b558` |
| R2 | counterexample for `hs : ShallowFrozenBefore arms` | `reassignArms_exhaustive_guardsPreserveDom_deepFrozenBefore_and_reaches_unreachable` | `Quot.sound`, `propext` | `cae54f6ef80f27d01bc0c0c531b9a121ac3c2dc8c9d937ba6c79afaf89977e4c` | `9a0f7cbdd96b73fa28844c05efb043f2efe5d8cc92090b6ad82ca475c4ddd873` |
| R2 | counterexample for `hd : DeepFrozenBefore arms` | `boxBoolArms_exhaustive_guardsPreserveDom_shallowFrozenBefore_and_reaches_unreachable` | `Quot.sound`, `propext` | `08196f15e4a21c723ffdb1f7a97a46e806a4336206ab5abbe51eaae1fb9339f9` | `c1c7347dab51fdcf706b3ff8556e2ee21161ea4aef13126bf8d69f82bd986963` |
| R2 | counterexample for `hv : Dom v` | `boolArms_exhaustive_frozen_and_reaches_unreachable_outside_dom` | `Quot.sound`, `propext` | `5a67048e6fa6f1309d3e94d2895d5a8e66cd2e506f07f481fa41d39be77895b3` | `6808e017b126aaf386e354cfc815dc4fbd0924620a1f3caaac27bed6f3e99245` |
| R3 | non-vacuity | `reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable` | `Quot.sound`, `propext` | `6c0a51d6b8c9ffa672c9a1865be06b67cc0156f63d0f485ac92b3e3f5dd344fa` | `9bf99a3bf4bb1d73f13a24a6a4c2fce9c6e660b5d5e6634a2a232771b30b442b` |
| R4 | non-vacuity | `boxBoolArms_exhaustive_shallowFrozenAll_shallowFrozenDerefAll_and_reaches_unreachable` | `Quot.sound`, `propext` | `c88fbde7e2cfb540d597745b278fdd3becd73a40c8f7107aeb278999f16cd50e` | `cb524df3aef1bd75f56aa56c3e6f73ea3e3ff22f77d6ea4bf0c2154d734c5ad4` |
| R5 | non-vacuity | `shallowGuardArms_satisfy_static_hypotheses` | `Quot.sound`, `propext` | `ff38e4b343ebe7edbe094384c21cefa4ac90abe282a0f08694442e3ada3ead27` | `d9f65b8265d89309b947138c5262530fe84183c19e75ba03794b7cd0797463b8` |
| R5 | counterexample for `hnd : NoDerefPatterns arms` | `boxBoolArms_not_noDerefPatterns_exhaustive_shallowFrozenAll_and_reaches_unreachable` | `Quot.sound`, `propext` | `4906d6668080dc0f46e98e6ebf05f45a306331fcf4a049c6d4abb3665d51c51e` | `55cdd02bae5a0022218f069e3b6aa4f3aecb8f2e9f305b7242221c10f1e0bbdf` |
| R5 | counterexample for `hex : Exhaustive Dom arms` | `missingArms_frozen_not_exhaustive_and_reaches_unreachable` | `Quot.sound`, `propext` | `c52533dd93a5cf63d9743ed6c90665f48585b097abf5e38b34990586db3b2502` | `20f74ee1b311e1cbe9b67748aed5c6311322518ff6aa9490dd1ee4986d0b0688` |
| R5 | counterexample for `hs : ShallowFrozenAll arms` | `reassignArms_exhaustive_deepFrozenAll_and_reaches_unreachable` | `Quot.sound`, `propext` | `6c0a51d6b8c9ffa672c9a1865be06b67cc0156f63d0f485ac92b3e3f5dd344fa` | `9bf99a3bf4bb1d73f13a24a6a4c2fce9c6e660b5d5e6634a2a232771b30b442b` |
| R5 | counterexample for `hv : Dom v` | `boolArms_exhaustive_frozen_and_reaches_unreachable_outside_dom` | `Quot.sound`, `propext` | `5a67048e6fa6f1309d3e94d2895d5a8e66cd2e506f07f481fa41d39be77895b3` | `6808e017b126aaf386e354cfc815dc4fbd0924620a1f3caaac27bed6f3e99245` |
| R6 | non-vacuity | `disjointSwitchWriteArms_deepFrozenSwitchAll` | `Quot.sound`, `propext` | `45dc526ec7011a9e1fab6f317d74d8c3d949cb8728565ffdd3ee8e6f3f1f1bbe` | `3c95bb5070597a5d71fe465e87fe642a1c7cff5f22c1ddec2d007fffbd1ab55f` |
| R7 | non-vacuity | `mixedStaticArms_accepted_exhaustive` | `propext` | `e46aaa313f406d5d25f08b5a0191f7291d89c7ac2c9627d4ff1df50c496a0d3d` | `dc3e378fc6f665631d44658d60dd6392d69bf3e502d3d7ebcd63f6c62f3fef56` |
| R8 | non-vacuity | `mixedStaticArms_accepted_exhaustive` | `propext` | `e46aaa313f406d5d25f08b5a0191f7291d89c7ac2c9627d4ff1df50c496a0d3d` | `dc3e378fc6f665631d44658d60dd6392d69bf3e502d3d7ebcd63f6c62f3fef56` |
| R8 | counterexample for `hck : borrowck arms = true` | `reassignArms_rejected_exhaustive_and_reaches_unreachable` | `propext` | `077b7f238b9ca04900e6a60d94c51e2ba5bd8da7b154b7c80e99d8f2e43782d2` | `5fec2675ab967a00b503d549ae186a753547c7b89f9287f6a1043c236d88c41a` |
| R8 | counterexample for `hex : Exhaustive Dom arms` | `missingArms_accepted_and_reaches_unreachable` | `Quot.sound`, `propext` | `032eb1655f495df6d9f2ea91471276c87100ae6fefb673a44ce333e5da375cd7` | `8642a6043b227d14fcd99448e0035546cf8a1295eecfcffd75342eb68b7d5729` |
| R8 | counterexample for `hv : Dom v` | `boolArms_accepted_and_reaches_unreachable_outside_dom` | `propext` | `aa8a0925b6f0c74bd3c5c11af3f5c7ec5ef1f01ec10c5c441296be527d3260e3` | `374b5190f08c4ddef3a10e7a42139b14589f3de065e3f65ba1b96c8457545923` |
| R9 | non-vacuity | `sameVariantArms_rejected_exhaustive_and_never_unreachable` | `propext` | `38059e10a33d9a86d996892f42e955247f82878b91b81a025618486540bb9ba3` | `f196e8d2f6692acbf863edd6e95d89f1865b95e86b2efedf152dd1cadff0fbab` |
| R10 | non-vacuity | `OrPat.runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms` | `propext` | `d68425f85ac62fd1b94b1c9c3da43c6fccd267744ee859ab25025b39ae7ae831` | `efb2f62bb464ff1fc1f0e056d3c7f166d3932fe1a1700f017d55d2bbe080e300` |
| R11 | non-vacuity | `OrPat.runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms` | `propext` | `d68425f85ac62fd1b94b1c9c3da43c6fccd267744ee859ab25025b39ae7ae831` | `efb2f62bb464ff1fc1f0e056d3c7f166d3932fe1a1700f017d55d2bbe080e300` |
| R11 | positive control | `OrPat.runGuardOnce_eq_runSrc_of_matchAll_length_le_one` | `propext` | `d45615ada64f61d22346a47b1c067c14fcb8066928c8fbf1c8b9c645c7381eb9` | `05c697bbe29a7d765c2d9b777dc617586767f139307b187d351eab7d381beb7d` |
| R12 | non-vacuity | `OrPat.bindingGuardArms_noDupBindings_sameDeclOrder` | `propext` | `96c28195d1feee0fa06340f80be17e4959996b4fe34cdec9786d9cc8db97c96a` | `a937f74e96fb17eeac697a4a7c70b57ca0049b2def76b8e4ede0a5d9b17c3dfd` |
| R12 | positive control | `OrPat.shadowedSwapArms_not_sameDeclOrder_and_policies_agree` | `Classical.choice`, `Quot.sound`, `propext` | `fbfc3656e28879b7b19e918babb6c89d20a637ca9a06fead4838a24798504f4e` | `1531b2999d890358cd886924b673529fc9586fc0f26c5efb0cc50fe7ce530d73` |
| R12 | counterexample for `∀ a ∈ arms, NoDupBindings a.pat` | `OrPat.dupBindArms_sameDeclOrder_not_noDupBindings_and_policies_differ` | `propext` | `6fcbc2922057bbc3e1ae1159522ce190de0401a14ae00dd9a848839f81eab33e` | `264dc7953464264369597257d45698435d00caf58a2bd7bac7a05945a9b0d2b0` |
| R12 | counterexample for `∀ a ∈ arms, SameDeclOrder a.pat` | `OrPat.refDropArms_noDupBindings_not_sameDeclOrder_and_policies_differ` | `propext` | `bbdad0b1827462d21db1397c9d347b7a3b99f79d576a4d8edacaffa0c1e5b0da` | `a0e7bf6592577fe49aec2bf042c2012872398f8feb084719bee21121e0db3ad1` |
| R13 | non-vacuity | `OrPat.runSplit_matchedAlternative_ne_runSrc_firstAlternative_refDropArms` | `propext` | `c76946650c6e215fd22c4f18318db2add148edd5dded15f4ee97e5104859b4b5` | `d181e23deaa3ed51234bd6a86ccab9b9a7c6f5126544bf3a9006e478382464e8` |
| R14 | non-vacuity | `ConstPat.derivedTy_allDerived_noFloat` | `propext` | `205a81814fa399553c4f34e97207e267f1c8027e37b7e4f069f5610d135deefb` | `1b9fff73bbb89f5aaca0401452c2337b045ee4622147e83641ac2f4db9a839c1` |
| R14 | counterexample for `hd : AllDerived T` | `ConstPat.manualVariantTy_noFloat_and_lowering_disagrees` | `propext` | `61f3f0ad0521689f4b31b7f09174361ec74ea8c086a5501468128025e3d4358b` | `f065536f50336a5abca420405a297127b595897604cff63a0ef4a190f83b6aca` |
| R14 | counterexample for `hf : NoFloat T` | `ConstPat.flt_allDerived_and_lowering_disagrees_nan` | `propext` | `0e7f52ad81033a18c5ed40b5a71bc74c75717fb774f33494e577dd3d33cdf691` | `51d089272b72b664b9a20f781bba9d05269e340e2892c78a0c66cf4dae5aa786` |
| R15 | non-vacuity | `ConstPat.derivedTy_allDerived_noFloat` | `propext` | `205a81814fa399553c4f34e97207e267f1c8027e37b7e4f069f5610d135deefb` | `1b9fff73bbb89f5aaca0401452c2337b045ee4622147e83641ac2f4db9a839c1` |
| R15 | counterexample for `hd : AllDerived T` | `ConstPat.manualVariantTy_not_allDerived_and_iff_fails` | `propext` | `f5fb0d3b4cabf84b76cd334a85b3867d940369d025a3d8e77e624d08f52cf900` | `f065536f50336a5abca420405a297127b595897604cff63a0ef4a190f83b6aca` |
| R16 | non-vacuity | `Accessor.countedBoolAcc_resultStable_not_stateIdempotent_not_pure` | none | `46337a890b5664e6b244a94b99dd0ed5d74928946473871484f6712f9f2355f7` | `9ccc28fbaabf994a0818bd0bcc16921c1d3328e92124e85866cedb92815e46a6` |
| R17 | non-vacuity | `Accessor.loggedBoolAcc_resultStable_stateIdempotent_not_pure` | none | `1d873005abe4d18eb5cf005e85138b4040ffd33f8eab5c722ce1aed656d9c0e4` | `a5ea437dcf804878a363ad305697db433f17625cc6bce70defd5174dc0b1283c` |
| R18 | non-vacuity | `Accessor.idAcc_pure_wellTyped` | none | `8dfdf188d635feff24b3257c538a330951e7adbacc980de37fda567bb2fe2e46` | `9debb8f3346181e060ab1cf8a0cf98b1519b00b723a11064c84ff4c46b5f3c3d` |
| R18 | counterexample for `hwt : WellTyped RDom acc` | `Accessor.constFalseAcc_resultStable_not_wellTyped_and_iff_fails` | none | `11f1e30b590e7e8ae62fde92968572e8add5035f108b3c5700a7ec17d6e51c7b` | `47f64d9ea14b7b735c5bd1980b600ebdd6a38b91630762564c984c67c9a8569a` |
| R19 | non-vacuity | `Accessor.toggleAcc_repeated_reaches_unreachable` | none | `251c3d567c3d2394c8fab0f0a81a1ca72d9ce375acb6b048d064b44852e8e2d2` | `a13c5eefb6f40a64b1d9d7df8f7597abc74f53902fac8313f3e5ce601583191a` |

### Definitions and auxiliary declarations cited by name (`lean_names`)

| Declaration | Axioms | Statement SHA-256 | Closure SHA-256 |
|---|---|---|---|
| `Accessor.Acc` | none | `c476dd8413008cdadaf5c288ba629ab431cb5856d27dab0e63f160d6328032b9` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Accessor.boolResultArms` | none | `abc14f603d5ad27ffbc0ee88f37b5a6675ac846809f551e519e771fac7d847f9` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Accessor.constFalseAcc` | none | `b3db91567ea2a1a522b0585e92a8f5b3752b4f2801391aa6727a241ac434037d` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.countAcc` | none | `9d759341ff070988eb55055a5dd805fa45a1ff3e1bdbb8fcb0835230f3e14b2a` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.countAcc_same_selection_different_state` | none | `1bac466c21b8566dc2c2e60e04b0ee32129e188309629c4e7670d99e2014ba6b` | `0374b10154b933e443fc50fe066bfa46c51d444620668ef226a5b7554f51da96` |
| `Accessor.countedBoolAcc` | none | `5e2123afd514dac805d7bf20a47de8b8e889263f229ff887f1e2daa2f5a47bae` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.ExhaustiveOn` | none | `5d413eec24f04de68db3f3567d5465f1bd20a52c36d47aa8a5b89c676f9d4cef` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Accessor.exhaustiveOn_example` | none | `d9bd2f3843367ff9deafc4e1575ec79e70b672bd3d667ded6c7597980c6982db` | `f2f4cdb502c4ede7679308fd395111cd3dbc57c4ea9e44ea0936b9bd48579102` |
| `Accessor.findFrom` | none | `1f866f77fac50c9e38903fd5182c5c3d111058c3cb906dee42f6e985172a499a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Accessor.flagAcc` | none | `4b484ba8d622aac8be8bdbb80501484ae036f5146d9fcd4aed61bf0ac3e8fba9` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.flagAcc_stable_idempotent_not_pure` | none | `547df273314908c5593e187617f28c94c03e9f2457fb33a1f5d6126b442e646f` | `bede0be4b5fa2e86df30a85f11dee6c7fdc9afd9e324ff42359c617108092509` |
| `Accessor.idAcc` | none | `1b775f50e9e967c8730365d5201ec276f3ea6977ba6d35137a922e84a7b7a424` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.loggedBoolAcc` | none | `445be26f8e4089e28e30b346515e4cc920dcd8ad035cdeccbab7bcd6919845bd` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.not_exhaustiveOn_example` | `propext` | `f2de16b7c10025d1ef099dbaa8712f74560f9f5e1b077f5c1a518a7afb299e3b` | `91d975a2cb9b2bb5d01a6b7d82b0a5ab9f7f38c014efdc429348b916f376ee16` |
| `Accessor.not_pure_example` | none | `f205d7e7bff4e8215f233cbc1ab080db036e5b9120ef030ca61ef3af35378287` | `92c36d45da7e4fbf4e9fa31a61058c7e6dd3e9c9ff562d6ad72dc467ee2dbe17` |
| `Accessor.not_resultStable_example` | none | `e61582131fe900f014d3fe9474d8c31945f00bf0b98cfcc2a8ae87d1173d7b96` | `f2d99cc80ed9d94fd80bdf1d93c29b2f30a6c8f6e314a7a8c40707adc6a80686` |
| `Accessor.not_stateIdempotent_example` | none | `3f4db2365a8767e235db36d73c39847c654ca9c85b7a2339ba7353eb50012c6e` | `1da276db61ce864e568619b89ad28e88ee69c19dba0147ed445711b97f1eee6b` |
| `Accessor.not_wellTyped_example` | none | `24a3346526645711738f0c0cd213f2b0a8b3f0bf790137e85d2cc19efa8feb7a` | `a4e8bbdd357aca8f17b05a098e95746109b1fd24feb65ae1b303bea21778be2d` |
| `Accessor.Pure` | none | `34e4a3159b9b3e8d7c4af024917973d270cd952b02e17a8c77d16087a9a30a33` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.pure_example` | none | `369e33f3e6b2da6d7e2061235c8ccced9ed2de9b74d35b0e98295d6863584ed6` | `9ba9cf5cafa406d25a5830249b3888a9d2e0a1158fadb64c9426bc1995b639f4` |
| `Accessor.repeated` | none | `7ac729f303f14d272619058884e82f19d156d5f5ea99a0eb54116d42d64d10cb` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.ResultStable` | none | `34e4a3159b9b3e8d7c4af024917973d270cd952b02e17a8c77d16087a9a30a33` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.resultStable_and_stateIdempotent_of_pure` | none | `93918d29b62927bcfb4faf6645059168319a7bd68325001935bd49ee46765d29` | `956aeceb96fbfa2081cb5530f255fa433a1bdba0274123385d261cd386e797da` |
| `Accessor.resultStable_example` | none | `bf668b592ebad46e48846107d0908ba9736a79e6987a8950cdf656028a31f0e6` | `541f3485685142263a6c76395a9ddc67256e391363bc99fac4ee4fe0a67c84a5` |
| `Accessor.shared` | none | `8e6789d4e33fbb56c591726ea19de3dccb80c94fdf63c10bb49bfdf6a878ead6` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.shared_eq_repeated_of_unit_of_satisfiable` | `propext` | `5b0b60daa623796a30872a3c3540b66760c581b89d13941e5bb279fcf773f62f` | `030dd35a6d544b4c5f30d79826c9ed80d379a6f12e2c27a7b4fc94a772cc8f40` |
| `Accessor.StateIdempotent` | none | `34e4a3159b9b3e8d7c4af024917973d270cd952b02e17a8c77d16087a9a30a33` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.stateIdempotent_example` | none | `f85b66eeca1e2e38b2daa74db105120765f57d78e7bf197399e288be178ec6e9` | `1fbde7d72f0088645c4a0cac3d80a4be79aa64bcbb81b9ad6ce4697fa7e35443` |
| `Accessor.threeBoolArms` | none | `abc14f603d5ad27ffbc0ee88f37b5a6675ac846809f551e519e771fac7d847f9` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Accessor.toggleAcc` | none | `925cff1cd387c9fd599d4cd8d0619cb7cb2f6c2a94e9971ff63dd4367c861c4e` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.twoThenFlipAcc` | none | `7fbb19958d430eb517c859879031d9742b7dc3a1a8e80d91660c1105919109dc` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.twoThenFlipAcc_stable_at_zero_and_repeated_reaches_unreachable` | none | `e003d81577f3b458102b4eeed065708adeafe56b74caa442117b7b15f719e62e` | `af81ee5330fe88d67280ddd5b3d125566231572477e786aed3a59536e1c85122` |
| `Accessor.WellTyped` | none | `9b0cda87babd4e6a15f45b8debbd63bf5000c68f851d12903941ef5f3defb82d` | `fcea1d98aaa651f52e1beafbdf99c6a98a79a62bb46e5e13c4fbd1476b4f5eab` |
| `Accessor.wellTyped_example` | none | `8c7ef8aaf28c8a32b893af5528cb7a3bd1b607e1ff82aeb0a17dfc450967d8e2` | `e01b606edc1fa3c19de9895cd83425b12aaf60ff488d3254f1ac39f5d12306c9` |
| `Arm` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Arm.derefScrutinees` | none | `fbbef197d82835c74b7fe55f47530e53a69758df0667350f3126fc472f746027` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `Arm.guardWrites` | none | `fbbef197d82835c74b7fe55f47530e53a69758df0667350f3126fc472f746027` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `Arm.matchesDirect` | `propext` | `cb4401402b598859cce141286ccbdcc8ceaf98aee1186dff29b23c062f812c8e` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `Arm.switchPlaces` | none | `fbbef197d82835c74b7fe55f47530e53a69758df0667350f3126fc472f746027` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `bindEnv` | `propext` | `45ee86a273d7b3cd4c92cca69eb08afa09535c4e0269c271fa818678138af577` | `f0524266b2bf17ee154e4ce0c7a59452ab5fce228bbe328da8d8c4417609880b` |
| `boolArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `BoolDom` | none | `bdf341d936af9c33baa213551d00b0caf12f8925c0a4b381027776164d603a36` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `borrowck` | none | `5bbb6c89a6100fda9eb97e4336dbab18bcacbb2eea0c523c6654a87ac57ea6f8` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `borrowck_boxBoolArms` | none | `a635297175706ef7c10d0bb163ff31a98125bc097578659c865a9d325013d394` | `3e61d937913fbf6a60e49df8f2a9c8a3c0d8c9f010bbc321407339eeaa8d2a29` |
| `borrowck_reassignArms` | none | `9cae6a9c7990cc986d3d5a753e7aa42673a2f70608bbddebf2370604a7f8eb7d` | `69046cbcda83ba0c564709f76a0f1f0250cf8a058ad1b78a08024e1503a4ce29` |
| `borrowck_shallowGuardArms` | `propext` | `ff76cc7fc6d8304cb83a751f90ff66eba70e59aec4c8b7e14a53d60e0dd710ac` | `373aeb308f835851c829073db08d1d84cf2f5adf3cf4bf4ee0493c4b0dc3001f` |
| `boxBoolArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `boxBoolArms_exhaustive` | `propext` | `8c9fe197e912676edafb5d77d7782fcc8b501c84f0548d1cf603ec181548a580` | `676dba280802c19c054a26160b0cb17c6d874481861e2d7b57ff8fafd1ad9a4e` |
| `boxBoolArms_not_deepFrozenAll` | `Quot.sound`, `propext` | `0e44828872e29a38997880ee36b118fd84b3aacddb54963e7277026f7c4f2c3f` | `dac1ca7e14699a69992280fd2dbfe1cc4b2bb150fc63670e78ff3a6180cd0a7b` |
| `boxBoolArms_not_deepFrozenBefore` | `Quot.sound`, `propext` | `5b2eadd3d9f44bf3e0bb27cd04d145c257c1dd1ce925a9d699f734f7dea917b1` | `7e108d5e258f18f1c21d90f2f7fe9b308e6106e3bf3da2360d5bd885b4cd9ad2` |
| `boxBoolArms_not_noDerefPatterns` | none | `514e575499cca057b1e1df2efcaabce1c8c9119464335d8846fbfbdf12188fbc` | `98eef69ff69bf794b2c20d16ebd9da61850affbcc5a5eec5d0dbe8ef0b946432` |
| `boxBoolArms_shallowFrozenDerefAll` | `Quot.sound`, `propext` | `15b482fe513104d938eb86fbb358d052ee91bd0f6542f45dc60f7dc50d09a1e3` | `992c08fd60ffa376a817eb0dc7d1fc0baf77268ae4019e1481023bd91f9dc5bd` |
| `BoxBoolDom` | none | `bdf341d936af9c33baa213551d00b0caf12f8925c0a4b381027776164d603a36` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `conflicts` | none | `feb2b278d03e819650d35272c3f752e6775b3c224ffcdc998995e70a43016618` | `00bfe42eef68fef72f0167ccea74adbc1bbc5ad545f70e8c982fc8f748458006` |
| `ConstPat.AllDerived` | none | `f57d90242467f0d4f71bd4a48bee785f52311ffd8313a803f22a92811dd90ea1` | `1b472b89cfa1a854417397287debfd50b6055499869ed8afb0b8ed476d21f823` |
| `ConstPat.allDerived_example` | none | `4ea7185c513824a8caa1fd7603d636892e04e3d1c42ccddd0fc9d0826052ad77` | `42188c3a34fd08a5cc47d4cf0bfce5ec0ad8c7df7c1910f601e4b538c5accc51` |
| `ConstPat.CTy` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ConstPat.CVal` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ConstPat.derivedTy` | none | `a3b29069e0d6cb9a7387f3ab5b7412f39cf5d8530b257d007ac2039799a75a0d` | `1b472b89cfa1a854417397287debfd50b6055499869ed8afb0b8ed476d21f823` |
| `ConstPat.EqImpl` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ConstPat.exists_teq_self_false_of_allDerived_of_not_noFloat` | `Classical.choice`, `Quot.sound`, `propext` | `c4128db526f356d12e0f7264f14804ce6f9458d0c8f19dbc73bf19b4eb82b4cb` | `ec850b584a9d27c695648ce9a4ccfe93752c434076ac6039c43c47cc02867d16` |
| `ConstPat.F` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ConstPat.F.ieeeEq` | `propext` | `d9720d74a1947b1633d49b260e9119f643f2838fbe4b4569c464647a9e96d251` | `e42599daa64e5665272858a964f8984e7c83e1d9a922c13f32925a8b8ee89e18` |
| `ConstPat.flipZeros` | `propext` | `9065f35e655131b04c631b9de174f7ab4731121ddc13754e06557885f11416a8` | `2460e4ff90015f51123161ebc985f845b29a591b80fde0e04561c97dd2d879ed` |
| `ConstPat.HasNan` | none | `9c2742b531f78a15845f08f39e60d87a8972ea3b16ca6bb3a897323eca79d47d` | `2460e4ff90015f51123161ebc985f845b29a591b80fde0e04561c97dd2d879ed` |
| `ConstPat.HasTy` | `propext` | `3a27e9ffad58cfdbb3a4ba313cc561ce97841eaef9e99e2b6537ce9fe409c1e5` | `1b472b89cfa1a854417397287debfd50b6055499869ed8afb0b8ed476d21f823` |
| `ConstPat.hasTy_example` | `propext` | `eaa50b8cf0be1a31796ab62912c3039a574e1b9fd442607364ce634b0e4d7e2b` | `f9181f110515466529918b85a6d4114dbbad25d2cfff080f9131041e68451ce9` |
| `ConstPat.hasTy_inhabit` | `propext` | `01ba2df89f11c5000734e9d047185f8481ad68f4bac3c8301ee0bb54d5625f80` | `9452911d09a3bbe3cbf6725e33b45289438543ec02ce5580ca628a920d29f5e4` |
| `ConstPat.inhabit` | none | `05f6226766bf1a1b8df563d88e1d51a9fa93dd4f6aa5c255d4c666f162e179f8` | `1b472b89cfa1a854417397287debfd50b6055499869ed8afb0b8ed476d21f823` |
| `ConstPat.LoweringAgrees` | `propext` | `a375ccac3c07152554a44494ba903a2401dbeb5b31607af2ca5959aeec755330` | `1b472b89cfa1a854417397287debfd50b6055499869ed8afb0b8ed476d21f823` |
| `ConstPat.loweringAgrees_example` | `propext` | `d4a6967de201f5127b96fd193e110454d8a7eaa4814cea83491852a327ba8089` | `8911a8fe9d7717d60cc28424b0c743968e0fed731490f19de4098998603ad3da` |
| `ConstPat.manualStructuralTy` | `propext` | `a3b29069e0d6cb9a7387f3ab5b7412f39cf5d8530b257d007ac2039799a75a0d` | `1b472b89cfa1a854417397287debfd50b6055499869ed8afb0b8ed476d21f823` |
| `ConstPat.manualStructuralTy_loweringAgrees_and_not_allDerived` | `propext` | `882d11b48255bc5c1a4e9cba6550d6d479d03ff72ca0857fb963f0fa49b1dd2e` | `4b92e7621e84ea154458927657aa99c6204ca7e6c164aa454fc664b1250bae74` |
| `ConstPat.manualVariantTy` | `propext` | `a3b29069e0d6cb9a7387f3ab5b7412f39cf5d8530b257d007ac2039799a75a0d` | `1b472b89cfa1a854417397287debfd50b6055499869ed8afb0b8ed476d21f823` |
| `ConstPat.nestedManualTy` | `propext` | `a3b29069e0d6cb9a7387f3ab5b7412f39cf5d8530b257d007ac2039799a75a0d` | `1b472b89cfa1a854417397287debfd50b6055499869ed8afb0b8ed476d21f823` |
| `ConstPat.nestedManualTy_lowering_disagrees` | `propext` | `3e2772cc009cc491b5d3552d01b89924f5a1d69a9bbef4daa63433287653cbf5` | `522a596c330e8eb48e1acba215c140289c95315e067c4d5eb7504aca4b852749` |
| `ConstPat.NoFloat` | none | `f57d90242467f0d4f71bd4a48bee785f52311ffd8313a803f22a92811dd90ea1` | `1b472b89cfa1a854417397287debfd50b6055499869ed8afb0b8ed476d21f823` |
| `ConstPat.noFloat_example` | none | `111889b7f40a17a524a57885130408204afa9dcd825e08204f3e0043ea0b4b70` | `fe7c7eb3785cce75a96f261d60d5d5fa96acfb7a35a71fffa4f97d8991724f6f` |
| `ConstPat.NoNanNoZeroLeaf` | none | `9c2742b531f78a15845f08f39e60d87a8972ea3b16ca6bb3a897323eca79d47d` | `2460e4ff90015f51123161ebc985f845b29a591b80fde0e04561c97dd2d879ed` |
| `ConstPat.not_allDerived_example` | `propext` | `68a411d1992b6595ec13bac63291efe90ba9719ea0b89532cc888c57692616dd` | `89db30a4175ba1e6bcc111caed8aebf4dbb04e6fb56ffc5d58c0f8382e0a4a48` |
| `ConstPat.not_hasTy_example` | `propext` | `a4fe2d1a2107633653f14be91f26dba11468ea7605ce406a2877cfca823d0097` | `f9181f110515466529918b85a6d4114dbbad25d2cfff080f9131041e68451ce9` |
| `ConstPat.not_loweringAgrees_example` | `propext` | `2ef2b7767c6003d9ae12d2f300438e5c6c4de7491cd96133e2ed3891bf734057` | `158bd60b8284c10975b165edfc68e646cc587138c86fc19e10432a7e5e8cdcae` |
| `ConstPat.not_noFloat_example` | none | `f1042d0c43cfa60697c9cb3ccae0c00cac2968c30eeaba642e6cbd3b26ac3a0a` | `a36e9bba88676251ddd6c6d63baf807bc69bd627799aff9fa4b408916099bcef` |
| `ConstPat.optFlt_none_agrees` | `Classical.choice`, `Quot.sound`, `propext` | `91843036b9ea0168d4438ebd3206995578e5d21afe0fba3d4db230af67a21aa7` | `c6e89fc6f30afa0241f7a98cefaf7d735881db60429e98574d0fc90d1510cbe2` |
| `ConstPat.payloadEq` | `propext` | `9974a9558bfad6cc9320ab570ded3bb54b93155ec38bcceccbd1a93a543aff7d` | `2460e4ff90015f51123161ebc985f845b29a591b80fde0e04561c97dd2d879ed` |
| `ConstPat.smatch` | `propext` | `9974a9558bfad6cc9320ab570ded3bb54b93155ec38bcceccbd1a93a543aff7d` | `2460e4ff90015f51123161ebc985f845b29a591b80fde0e04561c97dd2d879ed` |
| `ConstPat.smatch_agrees_with_teq_iff_noNanNoZeroLeaf_of_allDerived` | `Classical.choice`, `Quot.sound`, `propext` | `7530aa6d7eee6d63dd7326b43dcca603591f5e7ff9ae71ecda0f24fded0b33c5` | `90f7a1a463b75a86e809b42ac2b2912273b2939f6ff894ec48d036298faa4da0` |
| `ConstPat.smatch_example` | `propext` | `b20145bd220c1c79db045727406e48b3d1656bfd450cea883c19eafc7e6f1da4` | `35a504e30dfc8e1e6a233685c01d8814c2cff0b2d2493628a323ae4c5269c35f` |
| `ConstPat.smatch_example_false` | `propext` | `72f12ab30ca9170dbf5f2b14743036a701bb217e0ace22452fa7bdffcdf0a42a` | `35a504e30dfc8e1e6a233685c01d8814c2cff0b2d2493628a323ae4c5269c35f` |
| `ConstPat.teq` | `propext` | `2bf6fb1db91b02c9aef7c48a8e95f765e9933269da9fae73dc4e8c2977562cd4` | `1b472b89cfa1a854417397287debfd50b6055499869ed8afb0b8ed476d21f823` |
| `copyBoundFieldArms` | `propext` | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `copyBoundFieldArms_guardsPreserveDom_and_unmatched_write_leaves_dom` | `Classical.choice`, `Quot.sound`, `propext` | `5329a413535508da667e6c48ee9bfe0db585d4b88e8c99a426eab25e0f2cc514` | `7bb58cbd559defd945f5a82db73dfb0334b5092f2194acc2befa7103a081c581` |
| `DeepConflict` | none | `589d2916adceec7db17a627622da6f43aae1de122799f8258984907f9045968c` | `9cfee06c9d5f7c36176698fc883afa8f150f34c1d763d32185ecc1722c8eed19` |
| `DeepFrozenAll` | none | `8dffcace91e038ad415b6de46e10cbdb8595117a699cab4ffbc4180a90a415c9` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `DeepFrozenBefore` | none | `8dffcace91e038ad415b6de46e10cbdb8595117a699cab4ffbc4180a90a415c9` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `DeepFrozenBeforeAux` | none | `305dcaa46a5274081909bb1ae018ba45258b49db273645b747af9bfb283c1c7f` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `DeepFrozenSwitchAll` | none | `8dffcace91e038ad415b6de46e10cbdb8595117a699cab4ffbc4180a90a415c9` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `derefHead` | `propext` | `5fc042f313f7d64b738c02c49473d9b98332c1102ccab4b2707f8871e56b99a9` | `c16d5559e672da25d07b835ebc71da64850d07941f3218f8cd783d2b80fb95ea` |
| `disjointSwitchWriteArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `e0510Arms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `e0510Arms_selects_last_arm_with_changed_memory` | `Quot.sound`, `propext` | `7ec91f6ef32a8b659ae3f9096447cecd3f1b6e755ea946764c0aeae035c00c33` | `5abfe8015e753c86d48f7a5884f1757bffdad0365690aafdc6f7c3347cb50acc` |
| `Env` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `evalTest` | `propext` | `cdb9be7602057ebb9043bee2e71b38f327413aa2b77e6420be5fbe4daba3a0ac` | `25d931eee36427b615767b0e054e05347b1af67b97aa75cd47b6ebb73b020e81` |
| `evalTests` | `propext` | `951bf3b78e644f37f0206322fcfd5f87669c41ab5f3eba16fabb79bbb4f0930f` | `25d931eee36427b615767b0e054e05347b1af67b97aa75cd47b6ebb73b020e81` |
| `Exhaustive` | `propext` | `f9fa0ae17803e25f612d097576caacef7f224c189364deeacce9c5b7d6db47d6` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `fakeBorrows` | none | `81c0105fbeb35d2aebfcff328115e4aefd6ea2f85654ffdeb3558659fb810db4` | `5d7d5eebc2d9ca124354524d703a242024d80a3756656cc5b601aafea2df5855` |
| `FakeKind` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Guard` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `guarded_arm_not_counted` | `propext` | `5c1798ecc41a97c7f5be7f450392efea58fec6bc63ff1a8f855416b9998380e4` | `7614396669cb058bee5418ebbf8a4a2a02dc8ce64441cd576b34200904d0fcaf` |
| `GuardsPreserveDom` | `propext` | `f9fa0ae17803e25f612d097576caacef7f224c189364deeacce9c5b7d6db47d6` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `Head` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `headAt` | `propext` | `4dff7e1686c5cc9b924b8a1e70ce7fb28a33847257860a6f2fdd4b8ecbf500a3` | `c16d5559e672da25d07b835ebc71da64850d07941f3218f8cd783d2b80fb95ea` |
| `headAt_example` | `propext` | `bfbc6f2707c9a126351c33df0a5650080c41b3fc252d2e53f9fbe54e62f6af00` | `cf7900ed0b6bbf81efec1a35337c91c8053f6371f305cc6ee4b67f3689020419` |
| `headAt_example_none` | `propext` | `7dcdfb4738c87d310e8831e6b770a52aa5dfb6f70eb5089b8e8f86f065d85017` | `8fdd6dc603ae90bbeca4106c5965572c339d200767fb05d7e0a376164ad2e1f0` |
| `illTypedArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `illTypedArms_not_guardsPreserveDom` | `propext` | `78381f6e35effc4b38e14e5c6877165113f55cf800ff2f14a6f0a891542ab4bf` | `fa93357949cc6457533fffd8ee8acdaf8995be79fedb33d252e6fc70977d0477` |
| `incrSomeField` | `propext` | `ac2da96c864f0f2a4fac1c8848d3ca46ce2db0c262e6517dbaa2aae69cd3d81f` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `laterTestedArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `laterTestedArms_guardsPreserveDom` | `propext` | `a4f17a2123fd85fdbe843877d583f44b323bee8eaa9406879d9bfbb211b1380f` | `16e0f9192f8392749f8327843a8cd0709c8c94afbe886c51d997ab7fddc25dbe` |
| `laterTestedArms_shallowFrozenBefore` | `Quot.sound`, `propext` | `53a91f503ac5a9b9d6cf61e05f84d29796465f1ba85e00c9df6c41f3ab720c68` | `a0654c29bbb3ffaefa4eed81442a277f481f0420e9e8ad6c8ad62d61852eb438` |
| `lookup` | `propext` | `fd6bdd43c3813a29501a6698dd2669cfc38bc87bb1342dee214eca3ae92ea428` | `0740b9918b941fed6b7d168071fe01053e1ca759e60f7662362ad13be50408b3` |
| `lookup_example_none` | `propext` | `923e584f18ef6598603dd5442afb8329b899b7fc84e013ba3a77fb93619264d9` | `74f5ea6831633a73dd665a02dfbba209a50921f7d9d677725c0f332a8d6c7426` |
| `lookup_example_some` | `propext` | `5dfde04c0ab0c6f229417835deb6bbaa681805fee8c72daf2368d4da34940bbc` | `6c881524bcfe07922fc8e986d682549b492c8a341eaa53a8e22d502a21d7db24` |
| `Memo` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `memoFind` | none | `29e97921e0525a59a07c918b651d4f94ee95160a00d76cba063dbf5e0c170f99` | `de11ebc9d0971352a56ccf5002979e6da385d4ab4b8f6b0bf2f679f8e200ec56` |
| `missingArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `mixedLaterTestedArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `mixedStaticArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `NoDerefPatterns` | none | `8dffcace91e038ad415b6de46e10cbdb8595117a699cab4ffbc4180a90a415c9` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `OptBoolDom` | none | `bdf341d936af9c33baa213551d00b0caf12f8925c0a4b381027776164d603a36` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `OptIntDom` | none | `bdf341d936af9c33baa213551d00b0caf12f8925c0a4b381027776164d603a36` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `OptPairBoxBoolDom` | none | `bdf341d936af9c33baa213551d00b0caf12f8925c0a4b381027776164d603a36` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `OrPat.armDrops` | none | `c5e367298c1b792fe1072d733d068e452411a9872bb9250bb4cc07ab300de0b8` | `b0224a3914d53a817b853605d9f4bf916074a33eec51e5321cbaba08cffc6a53` |
| `OrPat.bindingGuardArms` | none | `969c08f455f1c89393b4bae9b01bc54abe85846e3b41604ab307165b81afe42a` | `fe65fb8eec838f1fead66e4586d16ca6333b9a2ab6d79d5ff5bdc7a9cf4d63d1` |
| `OrPat.constGuardArms` | none | `969c08f455f1c89393b4bae9b01bc54abe85846e3b41604ab307165b81afe42a` | `fe65fb8eec838f1fead66e4586d16ca6333b9a2ab6d79d5ff5bdc7a9cf4d63d1` |
| `OrPat.declOrder` | none | `4551d284df66bb5584b050cd8b12bb9275ff574e7b99fb4326b342f78e584967` | `07f4673a21f2691f8889f56800462286ee4938b0bd5b9ef9ec5287e2e0b1f86b` |
| `OrPat.declOrder_example` | none | `526c9419f9c3b7aefe26cad68c5986dc35c16d6dfe7c4814ef1051d28069f3dd` | `584cbb9ea193792fed0dd916cdf8e0df5632eeb8d87d0357d22dd4985975bc2a` |
| `OrPat.DropPolicy` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `OrPat.dropsInOrder` | none | `32efb5cb2db0d63bb7315314e147d949843dc1d87130e94f5e4b8773bec569a0` | `18ab2b37abe8ef1310407bcfcd9e32009471f8c765013c204663bb3e9e0d70c9` |
| `OrPat.dropsMatched` | none | `d6e7d775c39b1ed1225570150d4dea910c66cad0f78e9c590f56de351c162520` | `18ab2b37abe8ef1310407bcfcd9e32009471f8c765013c204663bb3e9e0d70c9` |
| `OrPat.dupBindArms` | none | `969c08f455f1c89393b4bae9b01bc54abe85846e3b41604ab307165b81afe42a` | `fe65fb8eec838f1fead66e4586d16ca6333b9a2ab6d79d5ff5bdc7a9cf4d63d1` |
| `OrPat.Env` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `OrPat.Ev` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `OrPat.expand` | none | `5cd89a68fc9a0a6997c558a69d5c8ebab614f6947993f9352a0f81ecb1f6e928` | `07f4673a21f2691f8889f56800462286ee4938b0bd5b9ef9ec5287e2e0b1f86b` |
| `OrPat.expand_example` | none | `323ba7a9d6318fbbf9b560a39bd8c7f4e67bbf4b5631767afa4282bfcec6c403` | `5b9f80936797f5302a46076d43e562ae8a4b81f1a2b3798040f00b2660eb7496` |
| `OrPat.matchAll` | `propext` | `657389ffb78ad81cbbe2274da8112f1a7b4e17e81c1f9d1f52712a6d6ba8b5d2` | `ee2ffe4f8f658567034bfda7c3c1ae1cd93a3142de7c7d3d9b36053ba48dc233` |
| `OrPat.matchAll_eq_flatMap_expand` | `Quot.sound`, `propext` | `845aeb528bd9ef4613415187a26af078f81b31eae7c2b9fb42fa35d5094334df` | `3ebfe8f8f55ce22b7988610a344f25960ef80be9cf53ca48b9d07a040be7ad71` |
| `OrPat.matchAll_example` | `propext` | `0330248c70aa626371bb6332488c42fdbf8911833d5d8ed3656b07eab1598906` | `ac5e32c0c59c698032d91f67a00e53d77494cda8b7438a4f05c93f72c1daafeb` |
| `OrPat.matchAll_example_none` | `propext` | `6a9dc70eedde05d95f3b918f714d6369428bd43bb957ab1a062a49cb0d87252c` | `ac5e32c0c59c698032d91f67a00e53d77494cda8b7438a4f05c93f72c1daafeb` |
| `OrPat.NoDupBindings` | none | `4ca20bf9f4d90b573ae65c3d067fe4aeb8aaaa71ca2cae98ea2b5c836fc7223a` | `07f4673a21f2691f8889f56800462286ee4938b0bd5b9ef9ec5287e2e0b1f86b` |
| `OrPat.noDupBindings_example` | none | `68afc16d4f1fe5b8112be363e41ed334f09ff929ac09f2b67822aa5df43b6a07` | `28538d1aef4ab061d53a3d9adac4b9383e710825171c6fe3a167d567bc327828` |
| `OrPat.not_noDupBindings_example` | none | `a34a37d3d1f36b90dc017642fa8e026e2c58b4b747b81d14b99fa661d0437409` | `28538d1aef4ab061d53a3d9adac4b9383e710825171c6fe3a167d567bc327828` |
| `OrPat.not_orFree_example` | none | `0a7c0942bc0bf683380fd48127e5726d3308a76849941da4d9f859944f5dfd8e` | `e3b17e690591238f84ae51ebbe384f440f9bc93676a14363e77d52f0de6731ed` |
| `OrPat.not_sameDeclOrder_example` | none | `2b27dc5e2419bbca001127b3ac9bd441db2df1432146d2a657e685977615fb27` | `5173f80e4b3f7dd6a38e36fdb3834cf148f45e70ca4b3a3686d2cfb0873928fe` |
| `OrPat.okErrGuardArms` | none | `969c08f455f1c89393b4bae9b01bc54abe85846e3b41604ab307165b81afe42a` | `fe65fb8eec838f1fead66e4586d16ca6333b9a2ab6d79d5ff5bdc7a9cf4d63d1` |
| `OrPat.okErrGuardArms_matchAll_length_le_one` | `Quot.sound`, `propext` | `116433865d2b49cc5a3d8f37fab930ef8f11a4ff7e4d36df2d45c461ddbd85a6` | `545634437cae8802bdc7ccb29e3153b1071e11658e867823d0d167c176263af1` |
| `OrPat.OrFree` | none | `1b5dd373ca6447c54014ecd725606129a9308ec03bbcc4f66915751cda7bafb5` | `07f4673a21f2691f8889f56800462286ee4938b0bd5b9ef9ec5287e2e0b1f86b` |
| `OrPat.orFree_example` | none | `ca3cd5ff9a18b3b76c9602c5f429e375c0bb821bb1de30a23ff105e119cf7f5a` | `e3b17e690591238f84ae51ebbe384f440f9bc93676a14363e77d52f0de6731ed` |
| `OrPat.Pat` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `OrPat.PV` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `OrPat.refDropArms` | none | `969c08f455f1c89393b4bae9b01bc54abe85846e3b41604ab307165b81afe42a` | `fe65fb8eec838f1fead66e4586d16ca6333b9a2ab6d79d5ff5bdc7a9cf4d63d1` |
| `OrPat.runGuardOnce` | `propext` | `ba2d9843370239c91e82c9bfe61f079c09b70eb7c9546396cb16e8b7f2134b33` | `972ea7085ba5f0f8efc4d52d388700c3d27f4e8e4fb01c3739153b762aa76814` |
| `OrPat.runSplit` | `propext` | `1d8ded99737cb314c717d3abdd954a766cc875309b47c2e0a4d58b6b1929f183` | `4913d299f83f890f22da9b80cc075215f01d260f4c7dd514f79e761d798ca42d` |
| `OrPat.runSrc` | `propext` | `ba2d9843370239c91e82c9bfe61f079c09b70eb7c9546396cb16e8b7f2134b33` | `972ea7085ba5f0f8efc4d52d388700c3d27f4e8e4fb01c3739153b762aa76814` |
| `OrPat.SameDeclOrder` | none | `4ca20bf9f4d90b573ae65c3d067fe4aeb8aaaa71ca2cae98ea2b5c836fc7223a` | `07f4673a21f2691f8889f56800462286ee4938b0bd5b9ef9ec5287e2e0b1f86b` |
| `OrPat.sameDeclOrder_example` | none | `8c822c0d09d7274d61a22cd92aae3a108b0eb9c476d99299ce49ba42daed56d4` | `5173f80e4b3f7dd6a38e36fdb3834cf148f45e70ca4b3a3686d2cfb0873928fe` |
| `OrPat.SArm` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `OrPat.shadowedSwapArms` | none | `969c08f455f1c89393b4bae9b01bc54abe85846e3b41604ab307165b81afe42a` | `fe65fb8eec838f1fead66e4586d16ca6333b9a2ab6d79d5ff5bdc7a9cf4d63d1` |
| `OrPat.splitArm` | none | `83b0ef1618d8b698d15a9096012dfd4755a356ffc373619dbf2f288c6a85bede` | `26639b5b88906c53685700df8bdb821698b9f84a6566f13c6e53421eb05ab7bb` |
| `OrPat.splitArms` | none | `a05a1533872f8bf3821fbf3425abec8adc3652e33c27aa21b77134766b3fb897` | `26639b5b88906c53685700df8bdb821698b9f84a6566f13c6e53421eb05ab7bb` |
| `OrPat.SubBranch` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `OrPat.SubBranch.drops` | none | `babb0857e9f818b21e9c2f5eca77620c9c08c5e5b0563c58a1eb6cbd22154e1c` | `4913d299f83f890f22da9b80cc075215f01d260f4c7dd514f79e761d798ca42d` |
| `OrPat.tryEnvs` | none | `1612b987455017fd6b4a9d72dc054bcdf21f34c3735573ac54e7bfa4dd58a95a` | `18ab2b37abe8ef1310407bcfcd9e32009471f8c765013c204663bb3e9e0d70c9` |
| `OrPat.unbalancedOrArms` | none | `969c08f455f1c89393b4bae9b01bc54abe85846e3b41604ab307165b81afe42a` | `fe65fb8eec838f1fead66e4586d16ca6333b9a2ab6d79d5ff5bdc7a9cf4d63d1` |
| `OrPat.unbalancedOrArms_firstAlternative_omits_drop` | `propext` | `3d2fbc441515de7846c9e6e8e1f566492c99920b2ebd4d33e434c14d4406c72e` | `7daa06936512addab7b57c94ea7dc796b7f4e942e086d1a711d37930781a43ec` |
| `Outcome` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Outcome.reachesUnreachable` | none | `ecbf618e75753a6df572e713a370ec9b03c4691efb976dc997ca9e7696f8bb1c` | `99e3a80627281ad9f26825f3cdf10de4ed7f0a9c27720ff5a50a6f381f0ace63` |
| `Outcome.selected` | none | `4a3a8fb3bc2a5afb266a1f198b0164334a0c0968288f6f337f63b89570a9ccaa` | `99e3a80627281ad9f26825f3cdf10de4ed7f0a9c27720ff5a50a6f381f0ace63` |
| `PairBoolIntDom` | none | `bdf341d936af9c33baa213551d00b0caf12f8925c0a4b381027776164d603a36` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `pairBoxArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `pairBoxArms_deepFrozenAll` | `Quot.sound`, `propext` | `585e0055799adccdb21e97f27285e31adbea857fe38c0aa6dd8bf5c0a1b28a30` | `e6abffd145824b8ca0e65605586ad07b16b64d72dafb31541c488fad136784d1` |
| `pairBoxArms_deepFrozenBefore` | `Quot.sound`, `propext` | `cc4bf078b04a78f73f30f9a8dc1f85e1cd9fcd663e6067530fb0c530c75e2cc2` | `1a167fcbe3d1f62c0cca92bbe4b0fe9facd003951c783711f0a25c1f2cd44745` |
| `PairBoxDom` | none | `bdf341d936af9c33baa213551d00b0caf12f8925c0a4b381027776164d603a36` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `PairOptBoolDom` | none | `bdf341d936af9c33baa213551d00b0caf12f8925c0a4b381027776164d603a36` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `Place` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Proj` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `reassignArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `reassignArms_exhaustive` | `propext` | `0bdc6d61f85ee65d063d6bc86252990235a064fef8de011338a7e8a314ff2ef2` | `37af542a62a28a280d25c96b08d9c0994eb124a22f389877cae274ffb908cecc` |
| `reassignArms_noDerefPatterns` | none | `dc0812cda9519fa6d8efc9d0a2ce3cd65716043f20aa2c6ea052f307fc614b1a` | `d8cede0ab933d0afce8b8c60732ff6834365524ab31b41d14d1abe6ffe993c65` |
| `reassignArms_not_shallowFrozenAll` | `Quot.sound`, `propext` | `6e4e0f07da874f3e52e8e926f93601128a8812f481b148a947270f23d560164b` | `2a96142f00214543845094a296478a9f62a15ba0abdabbd661a93a7541208a66` |
| `reassignArms_not_shallowFrozenBefore` | `Quot.sound`, `propext` | `8e9074fa59daeb6aac12c7ba271b3de8c5f0e735837a6e9fcf2ac89d38de5e09` | `b662f50bba60f0f8a8b9fc57ca43ab1bcb823d46ffa7c3bd265555056f8894fc` |
| `reassignArms_take3_not_exhaustive` | `propext` | `9a6e265387040c890782ba7aff4354ac8bd3fc274d63c5b805d9c0d7edbaba2e` | `37af542a62a28a280d25c96b08d9c0994eb124a22f389877cae274ffb908cecc` |
| `reassignBox_not_shallowFrozenDerefAll` | `Quot.sound`, `propext` | `79401d5cfd2f85421647730e0bea6a8b666cebdc4b28e190cca3d41e0a4cf150` | `b7b36c2b96a8d5660291bbe628459a7725129d0ea53a7169d2bb8a34fb77a64b` |
| `RefOptBoolDom` | none | `bdf341d936af9c33baa213551d00b0caf12f8925c0a4b381027776164d603a36` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `runArms` | `propext` | `c4b7ee920f85cc04d0d17c0ab8b8ca11a8636db485a63fbc64532c3a9f3d1717` | `d09e491712849cd0370490f426cb970363404339d821c373854275b495490bc2` |
| `runMatch` | `propext` | `9c0c25ee1bdcab005c848ed8e25bab4ad98326b178c97b465f4ad8a52634b086` | `327d0acfa73d83e8ff85e010a14038cf857d61dd78abf7268e016eba4544dd0c` |
| `runMatch_laterTestedArms_someFalse` | `propext` | `df5a8ee43aa10d89365d21a59a7525f1da9b21966b9120a9d1b96546cc35414e` | `d1084fcfa87586aaad21c9e59b7df95fb2ec0726692d1f299e62c161594de660` |
| `runMatch_reassignArms_none` | `propext` | `7e3150971f6809418bac2c9962d58e331711ac333f374ad523f548f0c931c4fb` | `bb4b7c7792e9511e776572b875b6d9ba2391b24af3d9fbf24627ddfc95a63343` |
| `runMatch_sameVariantArms_some0` | `propext` | `6d0ac719add6fb3f703f3834b8f11643f6f3365507e77bb29519255ffd1abe5c` | `761d48ab366fc3cc9183d8eecf7e9cbf7e8ac5c399b20eeba6c74b997a6e5c6c` |
| `runMatch_shallowGuardArms` | `propext` | `a28ec068ee9abd5210495179af42bae5a82a6495a47b45ab65a7ca19ebc53cab` | `e37edd42a3cc911d7eec99331607eea63764b128f2e926fb1c5ec5758f5a8771` |
| `runWrites` | `propext` | `5e2b2a6775d7c302552a309ed738789708776ed7a24b4111f418315fe187b446` | `f0524266b2bf17ee154e4ce0c7a59452ab5fce228bbe328da8d8c4417609880b` |
| `sameVariantArms` | none | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `setChild` | `propext` | `3826453a8b5ac2e4aab195dbce5af33547a8d2005e08b3c8b05a8a59006d6b32` | `e187f743adb2f4bc79f5c630214fea91aa191d1a5c1ee54141c7dcb546caa1d9` |
| `ShallowConflict` | none | `589d2916adceec7db17a627622da6f43aae1de122799f8258984907f9045968c` | `9cfee06c9d5f7c36176698fc883afa8f150f34c1d763d32185ecc1722c8eed19` |
| `ShallowFrozenAll` | none | `8dffcace91e038ad415b6de46e10cbdb8595117a699cab4ffbc4180a90a415c9` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `ShallowFrozenBefore` | none | `8dffcace91e038ad415b6de46e10cbdb8595117a699cab4ffbc4180a90a415c9` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `ShallowFrozenBeforeAux` | none | `305dcaa46a5274081909bb1ae018ba45258b49db273645b747af9bfb283c1c7f` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `ShallowFrozenDerefAll` | none | `8dffcace91e038ad415b6de46e10cbdb8595117a699cab4ffbc4180a90a415c9` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `shallowGuardArms` | `propext` | `7fec6765e3abc289c1f87ee1cd1104383345f56ac0c48d109753751b9d99e854` | `0de6ac20fc78153983c1bafd4edb93d3d711e3ff2452b81428dbf4646b1aa0dd` |
| `shallowGuardArms_not_deepFrozenSwitchAll` | `Quot.sound`, `propext` | `436ff418c5ec23288b98d5f5d8449719554e6a7b2cbcf24b1a76170c2c7f83f1` | `cdc2e19000cc491dffcb4e04de486db002fd9864c1adb62494bafd3a1174bef4` |
| `shallowGuardArms_shallowFrozenAll` | `Quot.sound`, `propext` | `195d70947b98f31b0143f239daee49b51a5f2f7cbee4b53797cce9c054584533` | `1026b6f2d60938adea45dc637bb6e4d7ac2c91b5398f731f1cf18500d287c4dd` |
| `step` | `propext` | `2d7ab4731598f25ceabd281b2aeeb2fc7228ccf93ab14d33545cc8435ae01286` | `e187f743adb2f4bc79f5c630214fea91aa191d1a5c1ee54141c7dcb546caa1d9` |
| `Test` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Test.derefScrutinee?` | none | `2d16f41dc08ccd8ff589aa18256a0856433f0df8cc351ecc028c3905f9e1f678` | `2622b7bc0f4b3b7d15de8596369d62f12011a7c85f82bddf048ad42ffbe25bce` |
| `Test.holds` | `propext` | `79d64c1f3bb4edca259a89e93af82e689d4563bafe32748568a9c03050ed6d6c` | `aa8d84003e71693085164c1e9ab64f56747aac5c63136f3f772f5fe5ea7d5cae` |
| `Test.switchPlace?` | none | `2d16f41dc08ccd8ff589aa18256a0856433f0df8cc351ecc028c3905f9e1f678` | `2622b7bc0f4b3b7d15de8596369d62f12011a7c85f82bddf048ad42ffbe25bce` |
| `Val` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Val.head` | none | `9e53710b423f06599b980d284ccc7c8ed08ee59daaf6d8d1c216ae3c2d4c4402` | `cc1643504298ab19e7cb568e7b7f0de247ec3c380f9ff78c6920867a5edaf386` |
| `vFalse` | none | `98dcf81248de921f5b3560dbe9c471c71b1d0ebebf401503670cfbb51e23260c` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `vNone` | none | `98dcf81248de921f5b3560dbe9c471c71b1d0ebebf401503670cfbb51e23260c` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `vSome` | none | `067d6123e37e5645514318c802ad2685fceb1abf681d350b55066015212d75b2` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `vTrue` | none | `98dcf81248de921f5b3560dbe9c471c71b1d0ebebf401503670cfbb51e23260c` | `1d4904083519c4926cba6afc246c5e78cec0c5c8b3bef575ac905cf04c0420b5` |
| `write` | `propext` | `f3d53a30ed1b95e783a93a8116fd9a6c2d2b292a93e95739e50a3a6c92796da5` | `0740b9918b941fed6b7d168071fe01053e1ca759e60f7662362ad13be50408b3` |
| `writeBoundOptBool` | `propext` | `ed9deb34f37e41de46a70f3e599728fe2d33ecd4740298a2ba604b368190f1d5` | `81d569e7b4e99a0b050ed2fa4c74080acf0a5af839e08b721b3f96a0215667b7` |
| `writeOrSkip` | `propext` | `1ea8c97f8c32915cb1523cb463e9e40dc70cc6b38240344735bfab43e30e1f77` | `0740b9918b941fed6b7d168071fe01053e1ca759e60f7662362ad13be50408b3` |
| `writeOrSkip_example_inside` | `propext` | `51fb033b17b57a3ee704066524cc4eea038efbe79901f0f28296d0092341522b` | `696a993fad9acf091590065e99fec48c937fcf346ccb8d75d6265f45fdd1bf4f` |
| `writeOrSkip_example_skip` | `propext` | `1a46f5f73fbbc4648be9b5d8544df9a76146e856224bca797f3fbd931a678ec2` | `d662a42be1dd7acd399919aaf919170dd50815068ac750b7d5578c6690135093` |

### Primary sources

* Fabrice Le Fessant and Luc Maranget, "Optimizing pattern matching", ICFP 2001, pp. 26–37, DOI 10.1145/507635.507641.
* Luc Maranget, "Warnings for pattern matching", Journal of Functional Programming 17(3), 2007, pp. 387–421, DOI 10.1017/S0956796807006223.
* Luc Maranget, "Compiling pattern matching to good decision trees", ACM SIGPLAN Workshop on ML 2008, pp. 35–46, DOI 10.1145/1411304.1411311.
* Thomas Tuerk, Magnus O. Myreen and Ramana Kumar, "Pattern Matches in HOL: A New Representation and Improved Code Generation", ITP 2015, LNCS, pp. 453–468, DOI 10.1007/978-3-319-22102-1_30.
* René Thiemann and Akihisa Yamada, "Verifying a Decision Procedure for Pattern Completeness", Archive of Formal Proofs, 2024-05-27, https://www.isa-afp.org/entries/Pattern_Completeness.html (Archive of Formal Proofs entries carry no entry-level DOI and are cited by entry URL and initial publication date, 2024-05-27; the live entry page updates across Isabelle releases, checked 2026-11-21).
* rust-lang/rust `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`; rust-lang/reference `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`; rust-lang/rfcs `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`. Paths and full line ranges of every quoted passage are given where it is quoted (modeling bridges and prior-art entries); every quoted passage was re-checked against these revisions on 2026-11-22. The rustc comment at `compiler/rustc_mir_build/src/builder/matches/mod.rs:550-551` refers to rust-lang/rust issue #142163 as background; the issue is not a subject of this report.
* Lean 4 toolchain `v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (leanprover/lean4).
* Published reference-corpus packages cited by name (not as subjects), google/zerocopy branch `reference` at `8978e7348aaa6d0808db1d0232d020d053020f4d`: `place-evaluation-ub-placemention-erasure-inbounds-projections-and-equal-target-switches`, `edition-indexed-drop-scopes-tail-and-if-let-temporaries-and-inhabitedness-gated-switches`, `enum-niche-layout-guarantees-and-validity-invariants`, `wrapping-niche-intervals-affine-tags-nested-option-capacity-and-discriminant-write-order`, `two-phase-borrows-reservation-activation-dominator-approximations-and-early-exit-edges`, `drop-check-may-dangle-and-destructor-soundness-for-generic-containers`.

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

`lean/RevalidationAudit.lean` is not part of the library target; it imports the library and runs `#print axioms` on the main result of every card. Each line of its output must list only `propext`, `Classical.choice` and `Quot.sound` (or no axioms).

To check that a later Lean release still accepts the proofs, change `lean/lean-toolchain` and rerun the primary command; a statement-hash mismatch then means that the statement or its definitions elaborate differently and the card text must be re-checked against the new statement. To check the modeling bridges against a newer rustc or Reference, re-read the quoted line ranges at the new revision; the kernel-checked results do not depend on them.
