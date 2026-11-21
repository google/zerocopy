# Context features and program equivalence: fully abstract game models, nominal games, relational reasoning under higher-order state and control, the Hobbit bounded checker, and layout randomization

## Summary

- **Equivalence is relative to what contexts can do; game semantics turns each missing capability into an opponent constraint** (Basis: documentation): innocence ⇔ no state (PCF; dropped for Idealized Algol), well-bracketing ⇔ no control (dropped by Laird), and, in call-by-value, visibility ⇔ no higher-order store (dropped by Abramsky–Honda–McCusker). PCF and bad-variable models are fully abstract only after a quotient; Murawski–Tzevelekos's nominal models are direct.
- **A context that can keep a function after the call that handed it over is exactly a higher-order-state context.** Murawski–Tzevelekos's `M3 ≅ M4`, O'Hearn–Reddy's deferred divergence and probe `p1` hold without that ability and fail with it; program-side revocation (`p2`) restores them. (Basis: documentation + execution.)
- **Local reasoning principles need specific features absent** (Dreyer–Neis–Birkedal; Basis: documentation): private transitions and inconsistent states need no `call/cc`; backtracking needs first-order state. Well-bracketed state change and Bohr's deferred divergence fail with `call/cc`; callback-with-lock only with higher-order state plus `call/cc`; the awkward example never.
- **Hobbit (`LaifsV1/Hobbit` at `63bc5153…`) decides equivalence for one context class** (Basis: source + execution): higher-order state, well-bracketed, no references in hand (references are not values). Its bound counts function applications per play; `equivalent` means no play hit the bound, `inequivalent` comes with a trace, else `inconclusive`. Built here, it refuted every retention-dependent pair, left bracketing-dependent equivalences (and the awkward example) inconclusive up to bound 24, and did not reproduce the repository's recorded `equivalent` for callback-with-lock.
- **Layout randomization yields probabilistic full abstraction under no-reuse assumptions** (Basis: documentation + derived). Abadi–Plotkin: fixed finite locations, no allocation, preservation for loc-free interfaces with bounds `δ` → 1 as memory grows. Jagadeesan et al.: bounded deterministic allocation in uniformly random order, `alloc` blocks on exhaustion, Thm 18 `≃N` iff `≃N_{ε,B}` (`B ≤ εN`). Exhaustion is already observable in their *source*, and their target guarantee is vacuous for exhausting runs. Neither models deallocation; observing when memory is returned would break the monotone-store premise of both hit-probability bounds (derived).

## Applicability

- **Scope.** How the capabilities of contexts determine program equivalence: state, control, higher-order store, bad variables, names (comparison and storage), memory addresses and allocation exhaustion. Plus one executable checker.
- **How the subjects relate.** The papers in `REPORT.json` were read and compared, not mechanized. `LaifsV1/Hobbit` at the pinned revision was inspected, built and run on its own benchmarks and on probes written for this report. The probes are inputs to that tool only; they do not model any other system.
- **Context classes.** HOSC/FOSC/HOS/FOS follow Dreyer–Neis–Birkedal: higher-order or first-order (ground) state, with or without `call/cc`. Each game-model claim belongs to that model's language (call-by-name PCF/IA vs. call-by-value ML-like). These languages differ in bad variables, reference equality and names, so a §1 row does not transfer to another language without an argument.
- **Versions and environment.** Several papers were read as preprints or extended abstracts, and Laird 1997 was not read at all; page and theorem numbers follow Evidence. Execution used one x86-64 Linux workstation with OCaml 5.4.0 and Z3 4.13.3, not the authors' environment (Ubuntu 18.04, Z3 4.8.10). Verdicts are deterministic; timings hold for this host only.

## Findings

### 1. Fully abstract game models

Basis: documentation. The Laird row is secondhand, from Abramsky–McCusker's 1999 "Game Semantics" notes §6, Hyland–Ong p. 407 and Abramsky–Honda–McCusker p. 2.

| Model | Language | Strategy constraints | Excluded context feature | Form of full abstraction |
|---|---|---|---|---|
| Abramsky–Jagadeesan–Malacaria 2000 | PCF, call-by-name | history-free strategies; bracketing as a rule of the games | state; control (their "errors" model "is fully abstract for SPCF, an extension of PCF with a catch construct", fn. p. 2) | intensionally fully abstract for PCF+`case` (Thm 3.23). Fully abstract for PCF only after "quotienting the intensional model by the intrinsic preorder" (Thm 4.15). By Loader's result, an intensional description "is the best that we can hope" for |
| Hyland–Ong 2000 | PCF, call-by-name | justification; priority ("last-asked-first-answered" = well-bracketing); innocence | a non-bracketed strategy "is essentially the catch (and throw) facility"; a non-innocent one is not PCF-definable (§7.5) | Thm 7.2: "The observational quotient … gives rise to an order-extensional, order fully abstract model of PCF". Compact innocent strategies are definable (Thm 7.1) |
| Abramsky–McCusker 1996 | Idealized Algol: call-by-name PCF plus block ground `var`/`new`, active expressions, `mkvar` | well-bracketed, "knowing" (not innocent) | control | Thm 9.1: fully abstract up to the intrinsic preorder `≲`. Thm 10.1: `σ ≲ τ` iff `comp(σ) ⊆ comp(τ)`. Thm 10.2: the model is "effectively presentable. It is still unknown if the analogous result holds for PCF". Definability comes from factorization `σ = cell ; τ` with `τ` innocent (Thm 7.1) |
| Laird 1997 | PCF plus a catch-style operator (SPCF variant) | innocent, not well-bracketed | state | "the addition of a simple control operator to PCF corresponds precisely to the violation of the bracketing condition" (1999 notes §6); full abstraction is up to an intrinsic preorder (notes, Thm 41) |
| Abramsky–Honda–McCusker 1998 | call-by-value with general references and `mkvar`; no reference equality | "visibility and innocence … are both relaxed"; bracketing and thread-independence kept | control. Visible strategies "yield full abstraction for languages with first-order store" (p. 8) | Thm 8: "Fam(C)/≾ is fully abstract" (a quotient). Factorization: higher-order cell → visible strategy → first-order cell plus innocent strategy |
| Murawski–Tzevelekos 2016 (GroundML, nominal) | call-by-value; references to ground types including `ref ref int`; reference equality; no bad variables | alternation, bracketing, visibility, frugality; equivariant and deterministic; **no innocence** | bracketing because "we do not have control mechanisms, such as call-cc or exceptions" (p. 229); "The absence of higher-order state … is captured by visibility" (p. 230) | **direct**: Thm 5.41, `M ≅ N ⟺ comp([[M]]) = comp([[N]])`. The general-reference variant (RefML, LICS 2011) drops visibility and is also direct |

### 2. The semantic cube and witness pairs

- **Statement.** "D+I+B purely functional; D+I functional + control; D+B functional + store; D functional + store + control" (D determinacy, I innocence, B bracketing; 1999 notes §2.11). "These increments in expressive power are exact, as shown by factorization theorems" (p. 2). The call-by-value axis is visibility: "Just as relaxing the condition of innocence corresponds to the model of ground-type references, so the additional freedom provided by abandoning visibility precisely captures the semantics of general references" (Abramsky–Honda–McCusker, p. 2). (Basis: documentation.)
- **Caveat: the state corners are bad-variable languages.** IA, RML and the general-references language of Abramsky–Honda–McCusker all contain `mkvar`, and "adding mkvar to the language does alter the observational preorder" (1999 notes, p. 36). A bad-variable context "will be able to distinguish x := !x from ()" (Murawski–Tzevelekos 2016, p. 193). Murawski–Tzevelekos (LICS 2011) list `x := !x ≅ ()`, `(x := V; x := W) ≅ x := W` and `(x := V; !x) ≅ (x := V; V)` as equivalences the earlier model "fails to validate".
- **Witnesses** (each pair holds without the feature and fails with it):

| Feature gained by the context | Pair | Basis |
|---|---|---|
| state (innocence dropped) | `λf. ifzero (f 0) then (f 0) else (f 0)` vs `λf. f 0`: equal in PCF. In IA, `new x in [−](λy. (x := !x+1; !x))` yields 2 vs 1 | derived (not in source), from "cannot vary its behaviour from one call to the next" (1999 notes p. 14); Hobbit separates the analogous `p3`/`p4` (§7) |
| control (bracketing dropped) | strict `λx.λy.` testing `x` then `y`, vs testing `y` then `x`: equal in PCF. `catch(λz. F z Ω)` returns 0 vs diverges. State with side-effecting arguments also separates them | derived (not in source), from `catch` (1999 notes §2.10); Hyland–Ong §7.5 give the non-bracketed strategy |
| higher-order references (visibility dropped) | `M3 ≡ let x = ref(0) in let c = ref(0) in f (λ_. if !c = 0 then div else x); c := 1; λy. x = y` vs `M4 ≡ f (λ_. div); λy. 0`: equal in GroundML, but "would not hold if our language supported higher-order references. The environment could then store the function and delay its use until the value of c becomes 1" | documentation (Murawski–Tzevelekos 2016, Ex. 3.7) |
| higher-order references | `let n = ref(0) in λy. if !n then () else (n := 1; f ())` vs the same with `(f (); n := 1)`: "equivalent in Reduced ML, but inequivalent when tested with RefML contexts" | documentation (Murawski–Tzevelekos 2011, §II, which prints the context) |
| control, with higher-order state present | the well-bracketed and deferred-divergence rows of §4 | documentation |

### 3. Names and locality

Basis: documentation (author copies).

- **ν-calculus (Pitts–Stark 1993).** A call-by-value, terminating calculus with types `o` and `ν`. Names "can be tested for equality and can be passed around via function application, but that is all"; there is no store.
  - Equivalences that hold (Cor. 6): `νn.M ≈ M` when `n` is not free; ν-binders commute; `β_v`.
  - Equivalences that fail: Ex. 2, `νn.λx.n ≇ λx.νn.n`, separated by `λf.(f new = f new)`; Ex. 3, `(λx. x = x) new ≇ new = new`. The context lemma also fails.
  - Ex. 4(2): `νn.λx.(x = n) ≈ λx.false` is provable by their logical relation.
  - Ex. 4(3): `νn.νn′.λf.(f n = f n′) ≈ λf.true` is not provable by their methods, and "certainly would not hold in languages where evaluation of functions can have side-effects on mutable state". Koutavas's dissertation (ch. 4) proves (3) operationally.
  - The logical relation is "complete (and decidable) for expressions of first order types, but incomplete at higher types" (Thm 22, Cor. 23).
- **Nominal games (Murawski–Tzevelekos 2016).** References are names. GroundML types are `θ ::= ζ | θ×θ | θ→θ`, `ζ ::= unit | int | ref ζ`, with reference equality.
  - *Comparison* separates `gen ≡ λz. let x = ref(0) in (x := z; x)` from `gen′ ≡ let x = ref(0) in λz.(x := z; x)` via `(λf. if f 0 = f 0 then () else div)[−]` (Ex. 3.4).
  - *A secret name the context cannot guess* gives `let x = ref(0) in λy. x = y ≅ λy. 0` (Ex. 3.7).
  - *Storing names* needs full ground storage: without it "names cannot be remembered by programs" (ICALP 2012, §1).
  - *Higher-order references* break `M3 ≅ M4`.
- **Decidability (finite integers).** Contextual equivalence is undecidable once types reach higher order: "The smallest GroundML term types of this kind are unit → unit → unit and ((unit → unit) → unit) → unit with unit → unit and (unit → unit) → unit remaining decidable" (2016, §6.3). ICALP 2012 lists the undecidable cases (Thm 10) and proves its GRef⁻ fragment decidable (Thm 18) using register pushdown automata "extended with fresh-symbol generation". No complexity bounds are stated.
- **Hobbit** has no name or reference values (§6), so it cannot express any of these pairs directly (unsupported).

### 4. Local relational reasoning (Dreyer–Neis–Birkedal)

Basis: documentation (JFP 2012).

- **Languages and model.** The base language, HOSC, is ML-like with recursive and abstract types, general references and `call/cc`. FOSC permits only "reference types ref b, where b represents base types". HOS removes `call/cc`. FOS has both restrictions. Contexts come from the same language.
  - The model is a step-indexed Kripke logical relation whose worlds are state transition systems (STSs).
  - Biorthogonality makes it "both sound and complete with respect to observational equivalence" in all four languages (p. 480). Completeness comes from biorthogonality, not from which features are present.
- **Principles and the feature each needs to be absent:**
  - public monotone STSs (generalized Pitts–Stark local invariants): sound in all four languages;
  - *private transitions* and *inconsistent states*: sound only without `call/cc`, because with it "every time we pass control to the context may be the last" (§5.1);
  - *backtracking*: sound only with first-order state; with higher-order state the callback "might have stored some higher-order data … that are only logically related in the locked state and its successors" (§6.1).
- **Examples** (✓ holds, ✗ fails):

| Name | Programs | HOSC | FOSC | HOS | FOS |
|---|---|---|---|---|---|
| awkward (§3) | `let x = ref 0 in λf.(x := 1; f (); !x)` vs `λf.(f (); 1)` | ✓ | ✓ | ✓ | ✓ |
| well-bracketed state change (§5.1) | `let x = ref 0 in λf.(x := 0; f (); x := 1; f (); !x)` vs `λf.(f (); f (); 1)` | ✗ | ✗ | ✓ | ✓ |
| callback with lock (§5.1, §6.1) | a counter whose `inc` reads `!x` after vs. before the callback, guarded by a lock `b` | ✗ | ✓ | ✓ | ✓ |
| deferred divergence, Bohr (§5.2) | `let x = ref ff in let y = ref ff in λf. f (λ_. if !x then ⊥ else y := tt); if !y then ⊥ else x := tt` vs `λf. f (λ_. ⊥)` | ✗ | ✗ | ✓ | ✓ |
| deferred divergence, O'Hearn–Reddy (§6.2) | `let y = ref ff in λf. f (λ_. y := tt); if !y then ⊥ else ()` vs `λf. f (λ_. ⊥)` | ✗ | ✗ | ✗ | ✓ |

- **Distinguishing contexts printed in the paper:**
  - well-bracketed state change in FOSC: `let g = • in let b = ref ff in let f = (λ_. if !b then call/cc(k. g (λ_. throw () to k)) else b := tt) in g f`, which "is able to set x back to 0 and then immediately throw control back to k";
  - Bohr's deferred divergence with `call/cc`: `call/cc(k. • (λg. throw g to k))`;
  - O'Hearn–Reddy in HOS: `let r = ref (λ_. ()) in • (λg. r := g); !r ()`, which stores the thunk and calls it after return.

### 5. Bisimulation techniques

- **Koutavas–Wand small bisimulations.** Basis: documentation, read in Koutavas's 2008 dissertation ch. 3; the POPL 2006 paper itself was not obtained.
  - The language is an untyped CBV λ-calculus where "functions are storable", locations are values, and there is no control operator.
  - Proofs use *adequate sets* of triples `(s, s′, R)`: two stores plus a relation `R` that records what the context has learned. Proof obligations are reduced to "smaller, necessary and sufficient" ones (Thm 3.5.1). The method is sound and complete (Thm 3.3.13).
  - Because `R` only grows and remains usable forever, the method models retaining (HOS-like) contexts.
- **Koutavas–Lin–Tzevelekos (TACAS 2022) and Hobbit.** Basis: documentation, accepted manuscript.
  - The language λimp is simply typed CBV with recursion, tuples and `ref l = v in e`. "We do not include reference types as value types, effectively keeping all locations local" (§3). Contexts are λimp contexts; the observation is termination (Def. 3).
  - The LTS configurations `⟨A; Γ; K; s; e⟩` (Fig. 3) have two key parts: `Γ`, the "proponent functions known to opponent", and `K`, "a stack of proponent continuations". OpApp applies any `Γ(i)`; OpRet returns only into the top frame of `K`.
  - Thm 8: "e1 ≈ e2 iff e1 ≡ e2". The up-to techniques are separation, re-entry and annotated state invariants. "no set of up-to techniques is guaranteed to finitise all examples".
  - Stated limitation: "Hobbit is not able to prove examples with inner recursion and well-bracketing properties" (p. 3; also p. 16).

### 6. Hobbit at the pinned revision

Basis: source (`LaifsV1/Hobbit` at `63bc51532a6173066fff1cb2d28e0b4998fe459a`) + `README.md`.

- **References are not values.**
  - `src/type.ml:1–8` defines the types `UnitT | BoolT | IntT | FunT | TupleT | VarT | ListT`; there is no reference type.
  - `value` (`src/ast.ml:165–189`) has no location constructor. Locations appear only as syntax: `NewRefExp of loc * …`, `DerefExp of loc * …`, `AssignExp of loc * …` (`src/ast.ml:199–201`), parsed from `REF l = location EQUAL e1 IN e2` (`src/parser/parser.mly:192–193`).
  - Stores can hold functions (e.g. `programs/equiv/cell-ho.bils`).
- **The opponent keeps every function it receives.** `collect_funcs` moves each function in a proponent value into the opponent's environment `g`; for returns, `src/lts.ml:1102–1104` does `let new_g,new_prval = collect_funcs v cfg0.g in … Some (PrRet new_prval)`. `op_call_trans` (`src/lts.ml:729`ff.) may then call any index of `g`. Only garbage-collection and separation up-to steps prune `g`, and those are claimed sound.
- **The opponent is well-bracketed.** `op_ret_trans` returns only into the top frame of the continuation stack (`src/lts.ml:686–701`):

  ```ocaml
  | Some ({k = (k1_nxt,k1_type) :: k1_rest; e = None} as c01),
    Some ({k = (k2_nxt,k2_type) :: k2_rest; e = None} as c02) ->
  …   c1 = Some {c01 with k = k1_rest; e = Some {ecxt = k1_nxt; e = ValExp (new_abs, None)}};
  ```

  So FOSC/HOSC contexts are not representable. Hobbit's equivalence is HOS minus first-class references.
- **The bound counts function applications along a play.**
  - `README.md:99`: "`-b <integer bound>`: number of function applications Hobbit is allowed to perform before returning an "incoclusive" result".
  - Default: `let bound = ref 6` (`src/hobbit.ml:20`).
  - The bound is decremented in `reduce_app` (`src/reductions.ml:407`). Opponent calls stop when `min bound10 bound20 = 0` (`src/lts.ml:748`). Exhaustion during a proponent move sets `bound_reached := true` and prunes the play (`src/lts.ml:1139–1141`).
- **Verdicts** (`src/lts.ml:16–18`: `exit_eq = 43`, `exit_ineq = 42`, `exit_unknown = 0`):
  - *equivalent*: the search ended and no play hit the bound ("the terms are indeed equivalent!", `:1721`). This is a proof only as far as the up-to techniques are sound.
  - *inequivalent*: a trace, plus a Z3 model when symbolic (`:1028–1037`). If generalisation was used, the search is first retried without it (`:1042–1050`).
  - *inconclusive*: "However the bound was exceeded in some plays" (`:1715–1717`). This is no evidence of equivalence beyond the bound. A run whose up-to re-entry is found unsound is retried without re-entry (`:1698–1706`).

### 7. Hobbit runs

Basis: execution. Host: x86-64 Linux workstation, 96 vCPU Xeon 2.60 GHz. Scripts, outputs and inputs are in `support/run_probes.sh`, `support/probe_output.txt` and `support/probes/`. All runs use bound 6 and up-to techniques `ngsrialfzue` unless stated.

| Input | Status in literature (§2, §4) | Verdict | Time / peak RSS |
|---|---|---|---|
| `hector-pitts-stark.bils` (awkward) | ✓ in HOSC | inconclusive at bounds 6, 12, 24 and with up-to techniques off | ≤ 0.04 s / 33 MB |
| `hector-thamsborg.bils`, `syteci-well-bracket-state.bils` (well-bracketed state change) | ✓ in HOS, FOS; ✗ with `call/cc` | inconclusive at 6 and 12. Timeout (150 s) at 24, and at 12 with all up-to techniques off | 0.07 s / 34 MB; 23.6 s / 139 MB; 150 s / 429 MB |
| `syteci-call-lock.bils` (callback with lock, annotated) | ✓ in HOS and FOSC | inconclusive at 6 and 10, after "up-to reentry failed … Retrying with up-to reentry call-skipping off" | 3.5 s / 49 MB; 114 s / 339 MB |
| `meyer-sieber-e1.bils` (`fun f -> ref x = 0 in f ()` vs `fun f -> f ()`) | ✓ | **equivalent**; with up-to techniques off, inconclusive at 6, and inconclusive at 12 after 104.7 s / 1.17 GB | 0.01 s / 31 MB |
| `hector-snapback.bils` (O'Hearn–Reddy, flag allocated per call) | ✓ in FOS only (stated for DNB's variant; derived for this one) | **inequivalent**: `pr_ret _idx_1_ → op_call _idx_1_ (af6) → pr_call af6 _idx_1_ → op_ret () → pr_ret () → op_call _idx_1_ () → [RHS=bot] → pr_ret () → [only LHS terminates]` | 0.03 s |
| `p7` (Bohr deferred divergence) | ✓ in HOS | inconclusive at 6, 12, 24 | ≤ 0.23 s |
| `p1`: `fun f -> ref x = 0 in f (fun u -> !x); x := 1; ()` vs `fun f -> f (fun u -> 0); ()` | ✓ without retention (derived; the shape of `M3`/`M4`) | **inequivalent**: same trace shape, ending `op_call _idx_1_ () → pr_ret 1` vs `pr_ret 0` | 0.01 s |
| `p2`: `p1` with a `live` flag, so calls after return diverge | ✓ (derived) | **equivalent** at 6 and 12; inconclusive with up-to techniques off | 0.01 s |
| `p3`, `p4`: `f 0 + f 0` vs `2 * f 0`; `f (); f (); 0` vs `f (); 0` | ✓ for pure contexts (derived) | **inequivalent**: the second `pr_call` is unmatched | 0.01 s |
| `p5`: private never-read counter vs constant; `p5b`: the same with annotation `{w \| c as w \| true}` | ✓ | `p5` inconclusive at 6, 12, 24. `p5b` **equivalent**, but inconclusive with the `z` flag removed | ≤ 0.02 s |
| `p6`; `counter`, `cell-ho`, `hector-scope-extrusion-2-3`; `hector-stark-tricky`, `hector-scope-extrusion-1-2` | as labelled | as labelled (`p6` inequivalent) | ≤ 0.02 s |
| `meyer-sieber-ineq.bils` | ✗ | inconclusive at 6, inequivalent at 8 (the repository's bound) | 0.01 s |

- **Reading.** Bracketing-dependent equivalences stay inconclusive, as the paper states; so does the awkward example (inference: unbounded re-entrant nesting keeps its LTS infinite; two ad hoc annotations did not help). Every pair relying on the context *not* retaining a callback is refuted with a trace: Hobbit gives the HOS answer, never the FOS one. `p2` shows a program enforcing the scope itself.
- **Recorded result not reproduced.** `experiments/hobbit_experiments/bfs_equiv.txt.csv` and its log (`default/out_bfs_equiv.txt`: "Bound: 10 … indeed equivalent!", 0.312 s) record `syteci-call-lock.bils` as *equivalent*; here it is *inconclusive*. The logs spell "exceded", fixed in a 2022-03-16 commit to `src/lts.ml`, so they predate the current code (a 2023-04-05 commit is titled "major update: added lists, fixes to rentry, fixes to generalisation, …"). The cause was not isolated.

### 8. Contexts that observe memory: layout randomization

Basis: documentation. Abadi–Plotkin (AP): TISSEC author preprint (preprint pages), compared with CSF 2010. Jagadeesan–Pitcher–Rathke–Riely (JPRR): author PDF. *Reconstructed* = glyphs lost in extraction.

- **AP languages.** High level: CBV λ-calculus with `nat`, `loc`, sums, recursion; attackers are public contexts `C : σ → bool`. Low level: only `nat`; `!nat M` and `M :=nat M′` take "a natural-number address, which may be obtained as the result of arbitrary numerical computations"; `loc` becomes `nat`. No heap-stored functions, code jumps or side channels.
- **AP randomization.** A layout `w : Loc ↪ {0,…,c}` is chosen once per run and extends a fixed public layout. The results hold "for any probability distribution"; the uniform distribution is optimal.
  - Bad accesses have two models. In the *fatal* model, the high level needs `raise error`; otherwise `λf.Ω` vs `λf. let x be f(∗) in Ω` is a counterexample. In the *recoverable* model, `!nat : nat → nat + unit`.
  - `δ_d(n)` is the minimum, over probe sets of size `n`, of the probability that no probe hits private memory. For the uniform distribution, `δ_U(n) = C(c+1−n−#PubLoc, #PriLoc) / C(c+1−#PubLoc, #PriLoc)` (*reconstructed*; `#` = cardinality). It "tends to 1 as c increases while PriLoc and PubLoc remain fixed".
- **AP theorems.**
  - Thm 4.7 (fatal model): "if σ is loc-free and M ≈h,p N, then M↓ ≈l,p N↓. The converse holds for all σ, if δ1 > 0". Low-level equivalence means, for every store, one of three outcomes: equal results with equal public stores for every layout; `error` on both sides with probability ≥ δ1; or divergence of both (*reconstructed*).
  - Thm 5.8 (recoverable model): for loc-free σ, `0 ≤ b ≤ c − #Loc` and `δ_{b+1} > 1/2`, "M ≈h,p N iff M↓ ≈bl,p N↓". Here runs with more than `b` erroneous accesses count as divergence.
  - There is no security parameter. The TISSEC version corrects CSF 2010: the low-level relation "is a partial equivalence. (Reflexivity fails…)" (p. 19).
- **AP assumptions.** "a finite set Loc of locations"; addresses `0,…,c` with `#Loc ≤ c+1`; total stores; no allocation and no deallocation. Exhaustion therefore cannot occur (derived). "dynamic allocation" is listed as future work (§6).
- **JPRR languages.** Source λµhashref: untyped λµ (control), first-class references storing references and functions, `null`, and `hashref` ("testing the hash of a reference against any possible reference hash"). Target adds `proberef` ("access to any reference, reversing its hash"); a failed probe returns `null`. Pointer arithmetic is encodable (Ex. 13).
- **JPRR randomization and allocation.** "the number of allocations is bounded and the allocation is deterministic". `alloc` takes the next cell of an order `η` fixed before execution, and the order is uniform over the "N! possible layouts". Cells are never reused, and "we still do not address deallocation nor contiguous memory allocation".
- **JPRR exhaustion.** "Once all memory is allocated, alloc blocks". The source is bounded to match, so `alloc; unit ≄ unit` (the context first allocates `|η|` cells) while `alloc; Ω ≃ Ω`. Meyer–Sieber's first example fails "because allocation is bounded".
  - Returning `null`/`err` instead is called "easily adapted" (unproved); Ex. 1 says "ends in an error at the (N + 1)th allocation", inconsistent with blocking.
- **JPRR theorem.** Thm 18: "For closed λµhashref terms t and u and for values of N, ε and B such that B ≤ εN: t ≃N u iff t ≃Nε,B u".
  - The target relation only considers paths with weight `p > ε` and `n ≤ B`, where `n` counts allocated cells plus failed probes. A hit on an unknown cell has weight at most `n/N ≤ B/N ≤ ε` (Lemma 23, *reconstructed*).
  - The ⇐ direction is proved in one line: "every λµhashref context is a λµproberef context".
- **Observing allocation failure or memory return.** Neither paper is affected directly, because neither models these events. The rest of this item is derived.
  - *Allocation failure.* In JPRR, failure is already observable at the source. Target paths that exhaust memory have `n ≥ N > εN ≥ B` when `ε < 1`, so the target guarantee is vacuous for them. Adding allocation with observable failure to AP would have two effects:
    - Count-based failure would expose private allocation counts, so `new x; t ≃ t` would survive only if the source exposed the same bound, as JPRR's does.
    - Placement-based failure (fragmentation) would be a layout-dependent observable that is not a probe hit. AP's argument (Prop 4.2(3)/Lemma 5.3(3): behaviour is layout-independent until a probe hits) would then fail.
  - *Memory return.* Both bounds assume that the set of allocated cells only grows. AP's Lemma A.3 states "if m has the form sw, so does m′"; JPRR's Lemma 23 uses a monotone `|s|` and a monotone knowledge set. AP already note that "a low-level attacker may store the numbers that represent the locations that it receives, and use them later" (p. 6).
    - With reuse, such a kept number or reference can alias a later private cell, at a rate set by the reuse policy rather than by `δ` or `n/N`. Seeing when memory is returned lets the attacker time that access.
    - JPRR anticipate this: with deallocation "we would need to consider the list of all probes, including successful ones" (§IV-D).

### 9. Synthesis: context feature → which equivalences break

Basis: derived; each cell cites its source. "mono" means the cell follows by monotonicity: for fixed programs, shrinking the context class can only keep or add equivalences. "Pure" means contexts without state or control.

| Pair | Pure | FOS | HOS | FOSC | HOSC | Hobbit |
|---|---|---|---|---|---|---|
| call twice vs once (`p3`, `p4`) | ✓ [§2] | ✗ [§2] | ✗ mono | ✗ mono | ✗ mono | ✗ trace |
| Meyer–Sieber 1 | ✓ mono | ✓ mono | ✓ mono | ✓ mono | ✓ (no context reaches `x`; derived) | ✓ proved |
| awkward | ✓ mono | ✓ | ✓ | ✓ | ✓ [DNB] | inconclusive |
| well-bracketed state change | ✓ mono | ✓ | ✓ | ✗ | ✗ [DNB] | inconclusive |
| callback with lock | ✓ mono | ✓ | ✓ | ✓ | ✗ [DNB] | inconclusive (old log: equivalent) |
| deferred divergence, Bohr | ✓ mono | ✓ | ✓ | ✗ | ✗ [DNB] | inconclusive |
| O'Hearn–Reddy; `p1`; `M3`/`M4` | ✓ mono | ✓ [DNB; MT16] | ✗ [DNB; MT16] | ✗ [DNB] | ✗ mono | ✗ trace |
| `νn.νn′.λf.(f n = f n′)` vs `λf.true` | ✓ [PS93 Ex. 4(3)] | ✗ (a counting `f`; PS93 remark + derived) | ✗ mono | ✗ mono | ✗ mono | not expressible |
| `νn.λx.(x = n)` vs `λx.false` | ✓ [PS93 Ex. 4(2)] | ✓ [MT16 `M1 ≅ M2`] | ✓ derived | ✓ derived | ✓ derived | not expressible |

| Feature added to contexts | Breaks | Source |
|---|---|---|
| state | repeated-call equivalences; ν Ex. 4(3) | §2, PS93 |
| control | evaluation order of strict arguments; well-bracketed state change; Bohr deferred divergence; callback with lock (together with higher-order state) | §2, DNB |
| higher-order state (retention) | `M3`/`M4`; the Reduced ML pair; O'Hearn–Reddy; `p1` | MT16, MT11, DNB, Hobbit |
| bad variables | `x := !x ≅ ()` and related | MT16, MT11 |
| name comparison | `gen`/`gen′`; `νn.λx.n` vs `λx.νn.n` | MT16, PS93 |
| observable exhaustion | any pair whose sides allocate different numbers of cells: Meyer–Sieber 1, and also awkward, well-bracketed state change, deferred divergence (derived via JPRR's memory-filling context) | JPRR Ex. 1, 12 |
| forgeable addresses | without randomization: any equivalence relying on a private cell (derived). With randomization: the pair holds up to `δ`/`ε`, for loc-free interfaces (AP) or bounded allocation (JPRR) | §8 |
| observable memory return | not modelled; it breaks the hit-probability bound (derived) | §8 |

### 10. Performance and resource footprint (L1–L6)

| Level | Value |
|---|---|
| L1 authoring | Hobbit `src/`: 18 files, 7,223 lines. Test suite: 129 `equiv` (3,840 lines), 78 `inequiv` (2,380), 12 `misc`, 3 `smart_contracts` [measured: `wc -l`]. The paper used 105/68 files, and annotations were "necessary for 34.7% of equivalences" proven [cited]. Probes here: 8 files of 1–6 lines. Proof effort for the papers: not measured |
| L2 toolchain build | Z3 4.13.3 with OCaml bindings, `make -j32`: 2 min 44 s, 793 MB peak RSS. Hobbit `make`: 4.7 s, 88.6 MB. The linker emits non-fatal "SFrame section ignored" warnings [measured: `/usr/bin/time -v`, x86-64 Linux workstation] |
| L3 checking latency | 0.01–0.07 s and 29–49 MB per default run, except `syteci-call-lock` (3.5 s at bound 6; 114 s at 10). With up-to techniques off, `meyer-sieber-e1` at bound 12 took 104.7 s / 1.17 GB; three runs hit the 150 s timeout [measured, §7]. Paper: default mode proved 72 equivalences in 5.6 s and 68 inequivalences in 20.0 s; all-off mode proved 3 equivalences in 2,098.5 s [cited] |
| L4 generated-code perf | not applicable to Hobbit. Randomization overhead is a design parameter, e.g. "twice the maximum required" [cited, JPRR p. 1]. Hit chance `1/(c+1)` per blind probe with one private cell [derived from `δ_U`]. Runtime cost: not measured |
| L5 verification speed | Hobbit: see L3. Game-semantic decision procedures exist only for fragments, with no complexity bounds stated [cited]. Paper proofs: not measured |
| L6 RAM/disk | `hobbit.native` 6.6 MB; `_build/` 9.7 MB; Z3 build tree 227 MB; `libz3.so` 33.5 MB; peak RSS 29 MB to 1.17 GB [measured] |

### 11. Comprehensibility and conceptual simplicity (C1–C2)

- **C1.** Hobbit's counterexample traces can be read without knowing the tool: `p1`'s seven moves say "the context kept the callback and called it after return". Inconclusive verdicts, however, do not say why exploration failed to close, and annotations require relational invariants. DNB's STS pictures are legible proofs, but each extension is a separate rule whose soundness depends on some feature being absent.
- **C2.** One idea unifies the four lines of work: removing a context feature constrains the opponent (innocence/bracketing/visibility; admissible STS moves; LTS rules; probe budget). Stating each claim as *(program language, context capabilities, observation)* makes scoped or borrowed callbacks "remove retention" (visibility) and exhaustion "add an observation" (this report's synthesis).

### 12. Validation (V1–V4)

- **V1.** Hobbit's Thm 8 and its up-to techniques (e.g. Lemma 13) are proved on paper. On the 6 pairs whose status is published (the §4 rows and Meyer–Sieber 1) and the repository-labelled benchmarks run here, no verdict contradicted the label; several were merely inconclusive. One recorded verdict was not reproduced (§7).
- **V2.** No fuzzing or differential testing was performed. In KLT §9's comparison, SyTeCi "was sound for equivalences, but not always for inequivalences".
- **V3–V4:** not examined.

## Boundaries

- **Not examined (no text obtained):**
  - Laird 1997, so §1's control row is secondhand;
  - Meyer–Sieber 1988;
  - Koutavas–Wand POPL 2006 itself (the dissertation was read instead);
  - DNB ICFP 2010 (the JFP version was read);
  - the full *Algol-like Languages* chapter of Abramsky–McCusker;
  - Ghica–McCusker ICALP 2000 and Murawski–Tzevelekos ESOP 2011;
  - the publisher layouts of TISSEC 2012 and CSF 2011.
- **Unsupported by Hobbit:** first-class references and names, non-well-bracketed contexts, pure or ground-state-only contexts, and exceptions.
  - A Hobbit "equivalent" says nothing about contexts with control.
  - A Hobbit "inequivalent" may fail to hold for weaker contexts; `p1` is an example.
- **Unknown:**
  - why `syteci-call-lock.bils` is now inconclusive (the 2023 re-entry changes, OCaml 5.4 and Z3 4.13.3 are all candidates; nothing was bisected);
  - whether better annotations would let Hobbit prove the awkward or well-bracketed examples;
  - whether JPRR's one-line ⇐ proof covers source contexts that distinguish only by exhausting memory, which needs paths with `n > B`.
- **Known not to apply:**
  - AP covers no allocation, deallocation, heap-stored functions, or `loc` in interface types (preservation).
  - JPRR covers no deallocation and no contiguous data.
  - The cube's state corners concern bad-variable languages.
- **Attractive but unsupported conclusions:**
  - "Hobbit found no difference, so the programs are equivalent." This holds only for the `equivalent` verdict.
  - "Randomization makes the target fully abstract." It does so only probabilistically, parameterized by memory size and probe budget, and only without reuse.
  - "Game models give practical checkers for ML." Decidability holds only for low-order finitary fragments.
- **Derived claims to re-check:** the §9 cells marked derived; the two §2 pairs marked "derived (not in source)"; the analysis at the end of §8.

## Evidence

- **Date.** All evidence was gathered on 2026-11-21 (UTC).
- **Repository.** `LaifsV1/Hobbit` at `63bc51532a6173066fff1cb2d28e0b4998fe459a`, which was HEAD on that date (commit dated 2024-06-18).
  - Fetched from codeload; tarball sha256 `f0f19892167c56a460eababeb992ba2cbacece8f53b758ad0ea6bb8e34976af1` (codeload archives are not guaranteed byte-stable).
  - Files cited: `README.md:99`; `src/type.ml:1–8`; `src/ast.ml:165–201`; `src/parser/parser.mly:148–149`, `:192–193`; `src/reductions.ml:401–407`; `src/hobbit.ml:20–32`; `src/lts.ml:16–18`, `:648–709`, `:729–748`, `:1023–1062`, `:1085–1141`, `:1694–1723`; `run-tests.sh:60–120`; `experiments/hobbit_experiments/bfs_equiv.txt.csv`; `default/out_bfs_equiv.txt:1373–1383`.
  - The commit history of `src/lts.ml` came from the GitHub REST API.
- **Build.**
  - Z3: tag `z3-4.13.3` (tarball sha256 `f59c9cf600ea57fb64ffeffbffd0f2d2b896854f339e846f48f069d23bc14ba0`), configured with `python3 scripts/mk_make.py --ml` and built with `make -j32`. Its findlib package was installed with a private `-destdir`.
  - Hobbit: the repository's `make`, using OCaml 5.4.0, menhir 20260122 and ocamlbuild 0.16.1.
- **Execution.** `support/run_probes.sh` with inputs `support/probes/` produced `support/probe_output.txt`, which records each run's verdict, wall time, peak RSS and full trace.
- **Literature.** Every DOI was checked against Crossref by `support/verify_dois.py`, with output in `support/doi_verification.txt`. AP's CSF 2010 paper is `10.1109/CSF.2010.30` (not `10.1109/CSF.2010.28`, which Crossref assigns to a different CSF 2010 paper). The arXiv IDs 1311.6125 and 2105.02541 (the KLT preprint, whose text was not read) were checked against their arXiv abstract pages. Versions read:
  - AJM, Inf. Comput. 163(2):409–470, 10.1006/inco.2000.2930 [arXiv 1311.6125v2]
  - Hyland–Ong, 163(2):285–408, 10.1006/inco.2000.2917 [publisher PDF]
  - Abramsky–McCusker, ENTCS 3:2–14, 10.1016/S1571-0661(05)80398-6 [extended abstract]
  - Abramsky–McCusker, "Game Semantics", Computational Logic 1999, 10.1007/978-3-642-58622-4_1 [preprint]
  - Laird, LICS 1997, 10.1109/LICS.1997.614931 [not obtained]
  - Abramsky–Honda–McCusker, LICS 1998, 10.1109/LICS.1998.705669 [preprint]
  - Pitts–Stark, MFCS 1993, 10.1007/3-540-57182-5_8 [author copy]
  - Murawski–Tzevelekos, FnT PL 2(4):191–269, 10.1561/2500000017 [author copy]
  - Murawski–Tzevelekos, LICS 2011, 10.1109/LICS.2011.31 [author copy]
  - Murawski–Tzevelekos, ICALP 2012, 10.1007/978-3-642-31585-5_30 [author copy]
  - Koutavas–Wand, POPL 2006, 10.1145/1111037.1111050 [Koutavas, PhD dissertation, Northeastern 2008, chs. 3–4]
  - DNB, ICFP 2010, 10.1145/1863543.1863566 [not read]
  - DNB, JFP 22(4–5):477–528, 10.1017/S095679681200024X [journal PDF]
  - Koutavas–Lin–Tzevelekos, TACAS 2022, 10.1007/978-3-030-99527-0_10 [accepted manuscript]
  - JPRR, CSF 2011, 10.1109/CSF.2011.18 [author PDF]
  - AP, TISSEC 15(2), 10.1145/2240276.2240279 [preprint]
  - AP, CSF 2010, 10.1109/CSF.2010.30 [proceedings PDF]
  - Meyer–Sieber, POPL 1988, 10.1145/73560.73577 [DOI only]
- **Synthesis versus source.** This report's own contributions are the §9 matrix and its monotonicity argument, the analysis at the end of §8, the two derived pairs in §2, and the probes `p1`–`p7`. Quoted definitions, theorems, examples and limitations are source facts. The related package `gustavsson-sands-space-improvement-bakewell-runciman-space-models-forster-kunze-roth-reasonable-space-devriese-approximate-back-translation-and-ahmed-blume-closure-conversion` covers observable resource budgets in back-translation.

## Revalidation

- **Hobbit (cheapest).** Build as described in Evidence, then run `HOBBIT=… HOBBIT_SRC=… bash support/run_probes.sh`. This takes about 12 minutes, mostly in 150 s timeouts. Diff its verdict column against `support/probe_output.txt`. The key expectations:
  - `p1` is inequivalent, with the call made after `op_ret`;
  - `p2` is equivalent;
  - `hector-thamsborg` and `hector-pitts-stark` stay inconclusive;
  - `p5b` is equivalent only when the `z` flag is set.
- **Newer Hobbit revision.** Diff `op_ret_trans`, `src/type.ml`, and the bound and verdict logic (`src/lts.ml:16–18`, `:748`, `:1694–1723`). If any of these changed, re-derive §6 before reusing §7 or the Hobbit column of §9.
- **Literature.** The papers are fixed, so re-check only against a different version. `python3 support/verify_dois.py` re-checks the DOI metadata.
- **Layout randomization.** If later work adds deallocation or observable allocation failure, check whether its theorem still bounds hits by distinct probes and allocations alone, or, as JPRR anticipate, counts successful probes and reuse.
