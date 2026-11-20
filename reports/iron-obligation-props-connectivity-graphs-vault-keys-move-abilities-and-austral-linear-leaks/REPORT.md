# Leak freedom as theorem, checked invariant, or intent: Iron, connectivity graphs, LinearActris, Vault keys, Move abilities, Austral and Linear Haskell, and what a last-use leak-freedom certificate must contain

## Summary

- **Leak freedom is a mechanized theorem only in the separation-logic line of work, and always under side conditions.** Iron (POPL 2019) proves that a closed program with triple `{e_1} e {e_1}` ends with an empty heap *once every thread has become a value*; it builds a linear logic (Iron++) on top of an affine one by threading fractional permissions. The connectivity-graph developments (POPL 2022, ICFP 2022, POPL 2023) prove global progress plus "full reachability" (no memory leak) for well-typed closed programs, under the invariant that the undirected ownership/connectivity graph is a **forest** (`cgraph_wf := no_short_loops g ∧ is_uforest (to_uforest g)`). LinearActris (POPL 2024) proves, in Coq, that `⊢ WP e {{ _, emp }}` implies every reachable configuration is either finished with an empty heap or can step (`global_progress`). Basis: source + documentation.
- **Production resource type systems state no leak-freedom theorem for their checkers.** Move's bytecode verifier *checks* that values without `drop` are never discarded (at `Pop`, `StLoc`, `WriteRef`, `Eq`/`Neq`, `Ret`), but the published resource-safety theorem (conservation, Theorem 5.10 of arXiv:2004.05106) is a paper proof over a dynamically checked semantics and explicitly does not cover the verifier. `Abort` is deliberately unchecked because transactions revert. Vault checks that the held-key set at every function exit equals the declared postcondition and appeals to the Capability Calculus soundness proof. Austral states leak freedom as design intent and enforces it with a 778-line unverified OCaml checker. Linear Haskell's guarantee is conditional ("if the result is consumed exactly once"), with a paper metatheory. GHC still marks the extension experimental, and its Linear Core Lint is opt-in and admits false failures. Basis: source + documentation.
- **Austral's linearity checker accepts leaking and double-consuming programs** when a `case` has three or more arms. At `austral/austral@0962d2a8a5d77f7daacd7f696819520733f4897d`, `lib/LinearityCheck.ml:356-365` compares arm states only in adjacent *disjoint pairs* (`a::b::rest -> ...; table_list_is_consistent rest`), so the third arm is never compared. A probe program was accepted and compiled; its C output aborted with `free(): double free detected in tcache 2`. Changing the recursion to `(b :: rest)` rejects all eight probes and keeps all 284 upstream end-to-end tests passing. Basis: source + execution.
- **A certificate of leak freedom for compiler-inserted last-use annotations** needs per-program-point live sets (or per-binding consumption witnesses), an **n-ary join condition checked against one certified set**, loop invariants with a body-preservation obligation, disjoint ownership splits plus a frame for parallel branches, an exit-emptiness obligation, and an explicit abort policy. Shared or cyclic ownership needs an acyclicity witness of the connectivity-graph kind, and no surveyed type checker supplies one. A 134-line toy checker (not any surveyed system) discharges these obligations and kills all generated mutants. An adjacent-pairs join variant of the same toy misses 246 of 468 "skip in the last arm" mutants. Basis: execution (toy model) + derived.

## Applicability

The report covers:

- the leak-freedom and deadlock-freedom theorem statements in the cited papers and in the Coq sources of `julesjacobs/cgraphs@74329952423f3db07dd0b60c62d823bd42df544c` and `julesjacobs/dlf-actris@121131ccc74c9793e620ebfcd2ae6d6bc6545169`;
- the drop-ability checks of the Move bytecode verifier at `move-language/move@c453c90994cba0af30314fe4134acee57fb20d0c`. That repository is archived, and downstream forks were not examined;
- the Austral linearity checker at `austral/austral@0962d2a8a5d77f7daacd7f696819520733f4897d`;
- GHC's `LinearTypes` documentation and multiplicity core files at the GitHub mirror `ghc/ghc@83038fbee5efea8e3ebd5090b2ff5537462e169d`;
- Rust RFC 1066 at `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, used as the reference case for "memory-safe but leak-permitting".

`julesjacobs/dlf-actris@02a9c468aa5b8d8f6e87476871756a4514ac4af0` is the repository tip. Its commit message is "Remove everything.", and its README says the development moved to the Actris GitLab project. All LinearActris source citations therefore use the preceding revision `121131cc…`. The Iron Coq development lives on a GitLab host and was not pinned or read. Iron claims come from the paper only.

The cgraphs directories map to papers as follows:

- `theories/sessiontypes` is the higher-order binary session-typed language that the POPL 2022 paper (DOI 10.1145/3498662) describes as mechanized. This mapping comes from the repository README and the paper's abstract.
- `theories/multiparty` is the ICFP 2022 artifact, per its README.
- `theories/locks` carries an annotated copy of "Higher-Order Leak and Deadlock Free Locks" (POPL 2023).
- `theories/lambdabar` is the artifact of "ƛ: A Self-Dual Distillation of Session Types (Pearl)", per its README. No DOI is cited for it here.

The subjects are related as a **comparison**. The logics (Iron, connectivity graphs, LinearActris) give per-program proofs whose trusted base is a proof assistant kernel plus the statement. The type systems (Vault, Move, Austral, Linear Haskell) give whole-language checkers whose soundness is argued separately or not at all. The certificate section (F8) uses all of them to derive what a checker for one specific artifact must verify. That artifact is a compiler's last-use (`move`/`drop`) annotations. The certificate section is a design derivation. It is not a property of any subject.

Execution evidence covers only:

1. Austral, built from source with OCaml 5.4.0 and dune on an x86-64 Linux workstation (96 vCPU Intel Xeon @ 2.60 GHz), with probe programs compiled by `gcc -fwrapv`;
2. a toy checker written for this report.

No Coq development, Move verifier, Move Prover or GHC was built or run.

## Findings

### F1. Theorem statements at a glance

| System | Statement (paraphrase; quoted forms below) | Language features | Side conditions | Mechanization |
| :-- | :-- | :-- | :-- | :-- |
| Iron, Thm 3.1/3.2 | `{e_1} e {w. φ(w)}` gives postcondition validity and safety. `{e_1} e {e_1}` and `(e,∅) →*tp ((e1..en),σ)` with all `ei` values give `σ = ∅` | higher-order, fork-based concurrency, heap alloc/free, impredicative shared invariants, ghost state | all threads terminated; trackable invariants must be uniform w.r.t. fractions; fraction sums in pre/post must match | Coq (paper: "formalized all of the theory and examples"); size not measured |
| cgraphs binary sessions `safety` | `typed ∅ e UnitT → steps [e] ∅ es h → (h = ∅ ∧ ∀e∈es, e = Val UnitV) ∨ ∃ es' h', step es h es' h'` | linear/unrestricted functions, pairs, sums, recursive session types, fork, send/recv/close | invariant: connectivity graph well-formed (undirected forest, no 2-cycles) | Coq, `theories/sessiontypes` 2,806 lines + `theories/cgraphs` library 5,786 lines |
| MPGV (ICFP 2022) Thm 5.1–5.3 | global progress; `deadlock_free ↔ fully_reachable`; well-typed gives `deadlock_free ∧ fully_reachable` | multiparty session types, global types | same forest invariant | Coq, `theories/multiparty` 5,048 lines |
| Leak/deadlock-free locks (POPL 2023) | `typed ∅ e UnitT → steps … ρ → fully_reachable ρ`, implying `global_progress ρ` | higher-order locks with fork/acquire/release/wait/drop, barriers | forest invariant | Coq, `theories/locks` 6,900 lines (2,232 + 4,668) |
| LinearActris (POPL 2024) `adequacy` | `(⊢ WP e {{ _, emp }}) → steps ([e],∅) σ → global_progress σ ∧ all_progress_or_blocked σ` | dependent higher-order message passing (Actris-style protocols), semantic session type system | linear (no weakening) logic; connectivity-graph forest in the model | Coq, 11,893 lines total, of which `base_logic` is 5,789 |
| CP (Wadler 2012) Thm 1–2 | preservation; top-level cut elimination: every well-typed process reduces to one that is not a cut ("corresponds to lack of deadlock") | classical linear logic processes; GV translated into CP | each cut composes two processes that share exactly one channel (derived from the rule form) | paper proof |
| Move resource safety (Thm 5.10) | `R(σn) = R(σ0) ∪ RI(π) \ RE(π)` for every well-formed execution | Move bytecode with Pack/Unpack, global storage, references | dynamic checks in the semantics; bytecode verifier *not* formalized | paper proof |
| Linear Haskell (Thm 3.5/3.6) | type preservation and progress for an operational semantics that gets stuck on a second use of a 1-variable | laziness, multiplicity polymorphism (core calculus) | conditional linearity; divergence makes the claim hold vacuously | paper proof (appendix) |

Basis: source (Coq statements quoted below) + documentation (paper statements).

### F2. Iron: obligations as fractions over an affine base

The paper text (DOI 10.1145/3290378) states:

> Theorem 3.2 (Adequacy for correct usage of resources). Suppose the Hoare triple {e_1} e {e_1} is derivable in Iron and we have: (e, ∅) →→tp ((e1,e2,...,en),σ). If all expressions ei are values, then σ = ∅.

Here `e_π` is Iron's trackable "empty with fraction π" resource. Points-to is `ℓ ↦_π v`. Allocation trades fraction into the points-to and `free` returns it, so only a program that frees what it allocates can restore the full fraction 1. The paper explains that `{e_π} ref(3); skip {e_π}` is unprovable: the best provable triple is `{e_π} ref(3); skip {e_π′}` with `π′ < π`, and that triple cannot feed the adequacy theorem. The key design statement is "require positive evidence, instead of relying on the absence of resources as evidence". Weakening (`P ∗ Q ⊢ P`) stays sound because discarding a resource also discards the fraction it carries, and the missing fraction is then visible in the postcondition.

Side conditions and limits, all from the paper:

- **All threads must terminate** before Theorem 3.2 applies. A forked thread can loop forever holding transferred resources.
- **Trackable invariants require uniformity with respect to fractions.** Section 8 states that examples where "it is not statically known who disposes of the shared resources" are out of reach of Iron++ and need the lower-level Iron logic.
- Iron addresses leak freedom, not deadlock freedom. Section 8 discusses locks as another user-defined resource, but progress is not part of the theorem.

Basis: documentation (paper).

### F3. Connectivity graphs: leak freedom as reachability, with a forest invariant

The binary-session-type theorem at `theories/sessiontypes/safety.v:3-12` reads:

```coq
Theorem safety (e : expr) (es : list expr) (h : heap) :
  typed ∅ e UnitT ->
  steps [e] ∅ es h ->
    (h = ∅ ∧ ∀ e, e ∈ es -> e = Val UnitV) ∨
    (∃ es' h', step es h es' h').
```

`Close` deletes the channel from the heap (`head_step (Close (Val (ChanV c))) h (Val UnitV) (delete c h)`, `langdef.v:401-403`), so `h = ∅` in a final state means every channel was closed. The file comments say `Print Assumptions safety` should show only `classic`, that is, classical excluded middle.

The multiparty development defines a partial deadlock, which is the same thing as a memory leak, at `theories/multiparty/definitions.v:114-120`:

```coq
Record deadlock (es : list expr) (h : heap) (s : gset object) := {
  dl_nonempty : s ≠ ∅;
  dl_active x : x ∈ s -> active es h x;
  dl_threadb i : Thread i ∈ s -> ¬ can_stepi i es h;
  dl_threadw i c : Thread i ∈ s -> thread_blocked es h i c -> Chan c ∈ s;
  dl_chan c x : Chan c ∈ s -> Chan c ∈ obj_refs es h x -> x ∈ s
}.
```

`theories/multiparty/theorems.v:52-54` proves `typed ∅ e UnitT -> steps [e] ∅ es h -> deadlock_free es h ∧ fully_reachable es h`, where `fully_reachable es h := ∀ x, active es h x -> reachable es h x` (`definitions.v:134`). A leaked channel is an active object that nothing reachable references, so full reachability excludes leaks and deadlocks together. The locks development uses the same shape (`locks/lambdalock/definitions.v:68-89`, `theorems.v:32-47`).

**The topological side condition** sits in the generic library, `theories/cgraphs/cgraph.v:43-46`:

```coq
Definition no_short_loops (g : cgraph V L) :=
  ∀ v1 v2, ¬ (edge g v1 v2 ∧ edge g v2 v1).
Definition cgraph_wf (g : cgraph V L) := no_short_loops g ∧ is_uforest (to_uforest g).
```

The run-time type system keeps the graph of threads, channels and locks (edges are ownership references) an undirected forest. Every proof of progress goes through induction over this forest (`cgraph_ind'` in `sessiontypes/progress.v:350-360`). The surface type system enforces the invariant through linearity: channel endpoints and locks cannot be duplicated, except as typing permits for unrestricted types (`unrestricted` covers `NatT`, `UnitT`, `VoidT`, `UFunT` and products/sums of these, `langdef.v:225-235`). Channels are never unrestricted. This is the formal counterpart of Rust's leak vector in RFC 1066 ("creating a cycle of `Rc` pointers, leaking the actual contents"). A cycle in the ownership graph is exactly what the forest invariant forbids.

Basis: source.

### F4. LinearActris: a linear program logic whose adequacy gives deadlock and leak freedom

At `julesjacobs/dlf-actris@121131cc…`, `theories/base_logic/adequacy.v:263-264` and `:290-293` state:

```coq
Definition global_progress (σ : cfg) :=
  (Forall (λ e', is_Some (to_val e')) σ.1 ∧ σ.2 = ∅) ∨ ∃ σ', step σ σ'.

Lemma adequacy e σ :
  (⊢ WP e {{ _, emp }}) →
  steps ([e],∅) σ →
  global_progress σ (* deadlock and leak freedom *) ∧
  all_progress_or_blocked σ (* conventional safety *).
```

The proposition type is `aProp := linPred aResUR` (`base_logic/aprop.v:34`), a linear predicate type rather than Iris's affine `iProp`. The model reuses the forest definition (`base_logic/cgraph.v:34-38`, identical to cgraphs). The postcondition `emp` forces every owned resource to be consumed. Unlike Iron, the theorem gives **progress** (no deadlock) and does not require prior termination: either the configuration is final with an empty heap, or some thread can step. The README states testing with Coq 8.20.0 and a custom Iris branch (`robbert/sbi`).

Basis: source + documentation (README).

### F5. Classification: theorem, checked invariant, or intent, and escape hatches

| System | Leak freedom is… | Enforcement point | Escape hatches permitted |
| :-- | :-- | :-- | :-- |
| Iron | mechanized theorem (Thm 3.2) | per-program proof | nontermination of any thread (theorem then silent); lower-level Iron needed for unknown disposer |
| cgraphs / MPGV / locks | mechanized theorem (full reachability) | type system + Coq metatheory | none inside the language; nontermination gives progress, not termination |
| LinearActris | mechanized theorem (`adequacy`) | per-program WP proof or semantic typing | none in the logic; divergence allowed (progress) |
| Vault (2001) | checked invariant, with soundness by appeal to the Capability Calculus proof | held-key set at each exit node equals the declared postcondition; join points must agree; loops may need declared invariants | not examined (paper describes C interop by translation to C) |
| Move | checked invariant (no implicit discard of non-`drop` values); conservation theorem is a paper proof over a *dynamically checked* semantics excluding the verifier | `locals_safety` + `type_safety` + stack balance | `Abort` (transaction revert); resources may be parked indefinitely in global storage (conserved, not leaked, under Move's definition) |
| Austral | design intent ("A linear type system guarantees all resources allocated by a terminating program will be freed") enforced by an unverified checker | `lib/LinearityCheck.ml` | `abort` (`_Exit(-1)`, no cleanup); `pragma Unsafe_Module` raw memory; the `case` join defect (F7) |
| Linear Haskell / GHC | conditional property with paper metatheory | GHC typechecker multiplicity inference | divergence (vacuous); unrestricted fields; experimental inference ("may over-eagerly guess … `Many`"); Linear Core Lint off by default |
| Rust (contrast) | explicitly *not* guaranteed (RFC 1066) | none | `mem::forget` is safe; `Rc` cycles; panics |

Quoted bases:

- **Austral.** Specification section "Linear Types and Exceptions": linearity is "incompatible with exception handling". The conclusion of the error-handling chapter: "We reject exception handling on the grounds of semantic complexity … Without exception handling, there's no benefit to an affine type system over a linear one". The prelude implements abort as `fprintf(stderr, …); fflush(stderr); _Exit(-1);` (`lib/prelude.c:92-104`).
- **Move.** arXiv:2004.05106 §3: "An aborting transaction script evaluates to the pre-state of the script, at which point all resources reside safely in global storage". The same paper: "leave formalization of the bytecode verifier to future work. Our formalization and resource safety theorem (Theorem 5.10) therefore do not depend on any of the invariants ensured by the bytecode verifier".
- **GHC.** `docs/users_guide/exts/linear_types.rst:13-21`: `:status: Experimental` and "expect bugs, warts, and bad error messages". `docs/users_guide/debugging.rst`, `-dlinear-core-lint`: "some optimizations in GHC might not preserve linearity and there are valid programs that fail Linear Core Lint".
- **Rust.** RFC 1066: "It has never been a guarantee of Rust that destructors for a type will run".

Basis: source + documentation.

### F6. Move bytecode verifier: drop-ability checks and the join lattice

The `locals_safety/abstract_state.rs:17-25` lattice is `Unavailable | MaybeAvailable | Available`. The join is pointwise. Equal states stay the same, and any disagreement goes to `MaybeAvailable` (`:112-124`). The checks in `locals_safety/mod.rs`:

```rust
Bytecode::StLoc(idx) => match state.local_state(*idx) {
    LocalState::MaybeAvailable | LocalState::Available
        if !state.local_abilities(*idx).has_drop() =>
    { return Err(state.error(StatusCode::STLOC_UNSAFE_TO_DESTROY_ERROR, offset)) }
    _ => state.set_available(*idx),
},                                                          // lines 41-48
Bytecode::MoveLoc(idx) => match state.local_state(*idx) {
    LocalState::MaybeAvailable | LocalState::Unavailable =>
        return Err(state.error(StatusCode::MOVELOC_UNAVAILABLE_ERROR, offset)),
    LocalState::Available => state.set_unavailable(*idx),
},                                                          // lines 50-55
Bytecode::Ret => { … LocalState::MaybeAvailable | LocalState::Available
        if !local_abilities.has_drop() =>
    return Err(state.error(StatusCode::UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP, offset)) … } // lines 73-90
```

`Bytecode::Abort` appears in the no-op arm (`:92-95`). In `type_safety.rs` the checks are:

- `Pop` requires `has_drop()` (`:434-442`, `POP_WITHOUT_DROP_ABILITY`);
- `WriteRef` requires the overwritten type to have `drop` (`:652-654`);
- `Eq`/`Neq` require `drop` (`:729-736`);
- `Abort` only checks that the operand is `u64` (`:458-463`).

`stack_usage_verifier.rs:5-11` (doc comment) and the end-of-block check (`stack_size_increment == 0`, otherwise `POSITIVE_STACK_SIZE_AT_BLOCK_END`) prevent a block from stranding values on the operand stack. `ability_field_requirements.rs:20-52` requires a struct's fields to have the abilities that the struct's declared abilities require.

**Design consequence (derived).** The abstract interpreter joins each block's post-state into every successor's pre-state (`absint.rs:94-100`). A disagreement therefore cannot slip through a join. It becomes `MaybeAvailable`, which is rejected at the next `MoveLoc`/`CopyLoc`/borrow of that local. For a non-`drop` local it is also rejected at `StLoc` overwrite and at `Ret`. This "lattice join, check at use/exit" design is associative over all predecessors. Austral's "equality at join" design (F7) is correct only if every arm is compared.

Move's verifier stack has no concurrency and no `Abort` check. The conservation theorem does not cover the verifier. The Move Prover (CAV 2020) "can rely on" the verifier's guarantees, which include "Procedures and struct declarations are well-typed (e.g., linearity of resources)". Its own specifications are user-written Floyd–Hoare pre/post/abort conditions. A user who wants an obligation-discharge property beyond non-discard (for example, total-supply conservation) must state it as a specification.

Basis: source + documentation.

### F7. Austral: a 778-line checker and an n-ary join defect (executed)

The checker tracks `Unconsumed | BorrowedRead | BorrowedWrite | Consumed` per variable, together with a loop depth (`LinearityCheck.ml:16-30`). Its rules:

- `remove_entry` raises "Forgot to consume a linear variable" at scope exit (`:98-122`).
- `TReturn` requires all linear variables to be `Consumed`, except write references and write spans (`:685-714`).
- Loops (`TWhile`/`TFor`, `:592-618`) reject variables consumed inside the loop body and not reassigned ("pending").
- `TIf` compares the two branch tables with `tables_are_consistent` (`:572-579`).
- `TCase` calls `table_list_is_consistent` on the list of arm tables and continues with the **first** arm's table (`:580-591`).

The defect is at `lib/LinearityCheck.ml:356-365`:

```ocaml
let rec table_list_is_consistent (lst: state_tbl list): unit =
  match lst with
  | a::b::rest ->
     let _ = tables_are_consistent "a case" a b in
     table_list_is_consistent rest
  | [a] ->
     let _ = a in
     ()
  | [] ->
     ()
```

The recursion drops `b`. Arms are therefore compared only as pairs (1,2), (3,4), and so on. With three arms, arm 3 is never compared with anything. With four arms, the pairs (1,2) and (3,4) are never related to each other, although the return or scope-exit check may still catch the result.

Typed `case` arms reach the checker in reverse declaration order. This was observed from which pair the error messages name. In `union Color is case Red; case Green; case Blue;` the unchecked arm is therefore `Red`. Probe results with the unmodified compiler:

| Probe | Shape | Compiler | Run |
| :-- | :-- | :-- | :-- |
| p1–p4 | 2–3 arms, disagreement inside the compared pair | rejected (exit 255) | n/a |
| p5 | 4 arms, pairs internally consistent | rejected, but only by the later return check | n/a |
| p6 | `Red` skips, `Green`/`Blue` consume `r` | **accepted** (exit 0) | `r` leaked when `c = Red` |
| p7 | `Red` consumes, others skip; `r` destructured again after `case` | **accepted** | prints `32` (use after consume) |
| p8 | p7 with a linear `Box` that owns `allocate()`d memory, destroyed by `deallocate` | **accepted** | `free(): double free detected in tcache 2`, exit 134 |

With `table_list_is_consistent (b :: rest)`, all eight probes are rejected with "is used inconsistently in the branches of a case statement". `test-programs/runner.py` reports 284 PASS and 0 FAIL both before and after the change. Across all `.aum` files under `test-programs/suites/`, exactly one `case` has three or more arms (`004-union/001-simple-union`), and it involves no linear values. Two GitHub issue searches found no existing report: `repo:austral/austral case inconsistent linear` and `table_list_is_consistent`.

Basis: source + execution. The probes and the diff are in `support/austral-case-join-probes/`.

### F8. What a leak-freedom certificate for last-use annotations must contain

Setting: a compiler inserts last-use annotations (`move x` at the final use, `drop x` where a value dies unused) into a program with linear bindings. A **certificate** is data that a small trusted checker validates *locally*, in time linear in program size, without re-running the inference that produced it. From F2–F7, the certificate needs the following parts:

1. **Live-set annotations** `L(p)` at every program point (equivalently, a per-binding set of consumption witnesses `W(x)` such that every complete path from `x`'s binding meets `W(x)` exactly once). Transfer: `let x` requires `x ∉ L` and adds `x`; `move x` and `drop x` require `x ∈ L` and remove it (obligation **O1**: no use of a dead binding, no double consumption).
2. **n-ary join sets** `J(j)` for every merge point, with the obligation that **every** predecessor's live set equals `J(j)` (**O2**). The check must compare each arm against one reference. Adjacent-pair comparison is the F7 defect. Move instead uses a lattice join with a check at the next use (F6). That design is equivalent for linear values, provided the exit check also rejects `MaybeAvailable`.
3. **Loop invariants** `I(ℓ)` with obligations `L(head) = I(ℓ)` and `L(back-edge) = I(ℓ)`. Bindings introduced in the body must die in the body (**O3**). Vault requires declared loop invariants unless they can be inferred in a bounded number of iterations. Austral forbids consuming outer variables in a loop unless they are reassigned.
4. **Parallel ownership splits** `(S_l, S_r)` with `S_l ∩ S_r = ∅` and `S_l ∪ S_r ⊆ L`. Each branch must consume exactly what it owns, and the frame `L \ (S_l ∪ S_r)` stays untouched (**O4**). This is the type-level shadow of separating conjunction. None of the production checkers surveyed has parallelism. The logics (Iron's fork rule, cgraphs' fork) handle it.
5. **Exit condition**: `L(exit) = ∅` or `L(exit) = returned bindings` (**O5**). Vault states this as postcondition key sets, Move as `Ret` with no non-`drop` locals, and Austral as the `TReturn` check.
6. **Abort policy**: either `L(abort) = ∅`, or an explicit declaration that abort may leak, justified outside the checker (**O6**). Move justifies it by transaction revert. Austral justifies it by OS reclamation at `_Exit`, and its own specification lists resources that survive process exit as a hazard.
7. **Call summaries**: per-callee consumed parameters and returned obligations (Vault effect clauses; Austral linear parameters). Without them the checker is not compositional.
8. **Beyond the certificate.** Shared mutable ownership or reference cycles (`Rc` cycles, channels sent over channels, locks stored in locks) need a **topology witness**: an acyclic connectivity graph maintained as an invariant (F3, F4). No surveyed type checker issues such a witness. A last-use certificate is sound only for alias-free linear bindings or for aliasing disciplined by borrows that cannot outlive or consume their origin, as Austral's `BorrowedRead`/`BorrowedWrite` states enforce.

What the certificate establishes (derived): on every terminating, non-aborting execution, each linear binding is consumed exactly once. If consumption means deallocation, the result is leak freedom and double-free freedom for those bindings. It establishes nothing about divergent runs, which matches the vacuity in Iron (all threads terminated) and Linear Haskell ("the claim holds vacuously").

**Trusted checker each system implies:**

| Approach | Trusted checking code (measured lines) | Obligations discharged | Soundness argument |
| :-- | :-- | :-- | :-- |
| Toy certificate checker (this report; not a surveyed system) | 134 non-blank, non-comment lines of Python (`leakcert.py`, 152 lines total) | O1–O6 | none (toy); mutation-tested only |
| Austral `LinearityCheck.ml` | 778 (+94 `.mli`) OCaml, plus typed-AST construction in `TypingPass.ml` | O1, O2 (defective for ≥3 arms), O3, O5; O6 unchecked by design; O4 n/a | none published |
| Move verifier passes relevant to drop | `locals_safety` 349 + `type_safety.rs` 989 + `stack_usage_verifier.rs` 272 + `absint.rs` 150 Rust; whole verifier `src/` 7,113 lines | O1, O2 (lattice), O3 (fixpoint), O5; O6 by revert; O4 n/a | conservation theorem excludes the verifier |
| Vault type checker | not available; not measured | O1, O2 (join agreement), O3 (declared invariants), O5, O7 | appeal to Capability Calculus proof |
| GHC linearity | `GHC/Core/Multiplicity.hs` 414 + `GHC/Core/UsageEnv.hs` 116 lines of data structures; full typechecker share not measured | O1/O5 for `%1 ->` arrows, conditionally | paper metatheory for the core calculus; Linear Core Lint optional |
| Iron / cgraphs / LinearActris | Coq kernel + semantics + statement (statement ≤ 5 lines; e.g. `safety.v:3-7`, `adequacy.v:290-293`) | O1–O5 plus concurrency, sharing via invariants (Iron), topology (cgraphs) | mechanized; developments of 5.8k–22.3k lines |

Basis: derived (from F2–F7) + source (line counts by `wc -l` at the pinned revisions).

### F9. Toy checker measurements

`support/toy-leak-certificate-checker/leakcert.py` implements O1–O6 over a toy statement language: `let`, `move`, `drop`, n-ary `branch`, `loop`, `par`, `abort`. `leakcert_eval.py` generates random valid programs with matching certificates and applies four mutation operators:

- delete one consumption;
- duplicate one consumption;
- delete a consumption in the last arm of a branch with three or more arms;
- move one binding across a parallel split.

Results from `python3 leakcert_eval.py 1 500` and `python3 leakcert_eval.py 2 2000`:

| Seed / programs | Valid accepted | M1 | M2 | M3 (last arm) | M4 | M3 under adjacent-pairs join |
| :-- | :-- | :-- | :-- | :-- | :-- | :-- |
| 1 / 500 (200,427 statements) | 500/500 | 500/500 | 500/500 | 468/468 | 245/245 | **222/468** |
| 2 / 2000 (803,307 statements) | 2000/2000 | 2000/2000 | 2000/2000 | 1843/1843 | 975/975 | **941/1843** |

Throughput was 1.05–1.73 million statements/s across three runs on the workstation above with CPython 3.13. These figures characterize the toy, not any surveyed checker. M1 under the pairs variant was also weaker: 456/500 and 1829/2000.

Basis: execution (toy model of a certificate checker, not any surveyed system).

### F10. Performance and resource footprint (L1–L6)

| Level | Item | Value | Basis |
| :-- | :-- | :-- | :-- |
| L1 authoring | Vault floppy driver port | C 4,900 lines → Vault 5,200 lines (5200/4900 = 1.061×) | documentation (Vault §4) |
| L1 | Move Prover core modules | Libra 420 LoC, LibraAccount 867 LoC incl. specs; 25/25 and 34/38 functions verified | documentation (CAV 2020) |
| L1 | proof effort for Iron, cgraphs, LinearActris | not measured (person-months not reported in sources read) | — |
| L2 toolchain build | Austral compiler clean build (`DUNE_CACHE=disabled dune build -j 1`) | 12.35 s wall, 8.39 s user, 111,612 KB max RSS | execution |
| L2 | Coq developments build time | not measured (no Coq toolchain run) | — |
| L3 checking latency | Austral compile of p8 (whole compiler, C output) | 0.13–0.32 s, 12.4–14.0 MB RSS over 5 runs | execution |
| L3 | Move Prover | Libra 2.99 s, LibraAccount 46.66 s (Boogie 3,875 / 10,362 lines; SMT 11,688 / 40,293 lines), Intel Core i9 8-core 2.4 GHz, 32 GB | documentation (CAV 2020) |
| L3 | Move bytecode verifier, Vault, GHC linearity | not measured | — |
| L4 generated code | runtime cost of linearity in any subject | not measured; all surveyed checks are static, except Move's dynamic checks in the *formal* semantics, which the verifier lets an implementation skip (arXiv:2004.05106) | documentation |
| L5 certificate check | toy checker | 1.05–1.73 M statements/s | execution (toy) |
| L5 | Coq kernel re-check of the developments | not measured | — |
| L6 footprint | Austral binary | 8,686,792 bytes | execution |
| L6 | mechanization sizes | cgraphs 22,334 lines `.v`; LinearActris 11,893 lines `.v`; Move verifier 7,113 lines Rust; Austral checker 778 lines | source (`wc -l`) |
| L6 | `.vo` sizes, checker peak RSS for Coq | not measured | — |

### F11. Comprehensibility and conceptual simplicity (C1–C2)

**C1, human comprehension.** Austral's error messages name the variable, the construct and both states ("In one branch it is consumed while in the other it is not yet consumed"). The checker state is four values per variable, which is low working-memory load. Move's `MaybeAvailable` is a lattice artifact that users meet only as status codes (`UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP`), and the codes do not say which path disagreed. Iron requires fraction bookkeeping that the authors call "additional bookkeeping". Iron++ hides it, at the cost of the uniformity side condition, which is a nonlocal concept. Connectivity-graph theorems are stated in 3–5 lines, but full reachability (`deadlock` record, `reachable` inductive) takes about 20 lines of definitions to read. Human-auditable statements are short in all three logics. The statement is the trusted part. Basis: source + derived.

**C2, simplicity and model refinement.** One invariant has several mechanisms. "Every resource consumed exactly once on every path" appears as fractions summing to 1 (Iron), `emp` postconditions in a linear BI (LinearActris), held-key-set equality (Vault), an availability lattice plus ability checks at five opcodes (Move), and state-table equality at joins (Austral). The minimal common abstraction is the **live-set transfer system with n-ary joins** of F8. Every surveyed type system is an instance of it, and each "exception" (abort, loops, borrows) becomes an explicit certificate field rather than a special case in the checker. The genuinely different mechanism is the **topology invariant** (forest of ownership references). It is needed only once sharing, channels-in-channels or cycles exist, and it should not be merged into the linear-binding check, because its laws differ: it is global and graph-theoretic, not path-local. Basis: derived.

### F12. Validation of implementations (V1–V4)

- **V1, specification adequacy and non-vacuity.** The Coq statements are short enough to audit, and `safety.v` notes that `Print Assumptions` shows only `classic`. Austral's 284 end-to-end tests include rejection tests for 2-arm `if`/`case` inconsistency. The only ≥3-arm `case` in the suite has no linear values, which is how the F7 defect survives. The toy mutation run shows that a "skip in the last of ≥3 arms" operator separates a sound n-ary join from the pairs pattern: 222/468 killed versus 468/468. Basis: execution.
- **V2, checker soundness testing.** No differential or metamorphic testing of Move's verifier, Austral's checker or GHC's linearity checker was examined. GHC itself documents that valid programs can fail Linear Core Lint, so its post-optimization check is not used as an oracle. Basis: documentation; otherwise not examined.
- **V3, concurrency, crash and physical validation.** The logics prove deadlock freedom for their calculi. No weak-memory, crash or fault-injection validation of any implementation was examined. For the sequential type checkers, V3 is not applicable beyond the abort semantics recorded in F5.
- **V4, human mental models.** No empirical study of programmers' understanding of linear or affine discard rules was found or examined.

## Boundaries

- **Not examined.**
  - The Iron Coq development, hosted on a GitLab instance and not pinned: its size, build time and whether its adequacy statement matches the paper verbatim.
  - The LinearActris sources at their new GitLab location.
  - Downstream Move verifier forks, for example in the Aptos or Sui codebases. Whether they changed the drop checks is unknown.
  - Building or running the Move verifier, the Move Prover, GHC or any Coq development.
- **Not measured.** Every L-table cell marked so: Coq build and check times, `.vo` sizes, GHC linearity-checker size and latency, Vault implementation size, proof-engineering effort.
- **Secondary only.** A search-engine summary of the TACAS 2022 Move Prover paper (DOI 10.1007/978-3-030-99524-9_10, arXiv:2110.08362) reports about 8,800 lines of Move and about 6,500 lines of specification for the Diem framework, verified "in a few minutes". The full text could not be retrieved, so these figures are not used in the tables.
- **Unknown.**
  - Why the Austral `case` arms arrive in reverse declaration order. Observed, not traced to the environment's declaration-list construction.
  - Whether Austral's maintainers consider the pairs recursion intentional. Nothing in the source or tests suggests so.
  - Whether downstream uses of Austral are affected.
- **Known not to apply.**
  - The leak-freedom theorems of Iron, cgraphs and LinearActris do not transfer to Move, Austral or GHC. None of those implementations is formally connected to a logic.
  - Move's Theorem 5.10 is about conservation of resource tags. It does not say that resources reach a destructor: resources may remain in global storage forever.
  - A last-use certificate (F8) says nothing about programs with reference cycles or shared ownership unless it carries a topology witness.
- **Attractive stronger conclusions the evidence does not establish.**
  - That Move's verifier is sound for non-discard. It is checked, but no proof covers it.
  - That fixing `table_list_is_consistent` makes Austral's checker sound. Only the eight probes and 284 existing tests were run.
  - That the toy checker's throughput predicts a production checker's.
  - That leak freedom implies deadlock freedom or the reverse. Iron gives the former without the latter, while LinearActris and cgraphs give both under the forest invariant.

## Evidence

Evidence acquired 2026-11-20 (UTC). Repository revisions were resolved through the GitHub API on that date:

- `julesjacobs/cgraphs@74329952423f3db07dd0b60c62d823bd42df544c` (committed 2023-06-02):
  - `theories/sessiontypes/safety.v:3-12`, `theories/sessiontypes/langdef.v:225-235, 401-403`, `theories/sessiontypes/progress.v:350, 671-674`;
  - `theories/multiparty/definitions.v:114-134`, `theories/multiparty/theorems.v:10-59`;
  - `theories/locks/lambdalock/definitions.v:68-89`, `theories/locks/lambdalock/theorems.v:32-47`;
  - `theories/cgraphs/cgraph.v:43-46`;
  - `cgraphs.opam` (requires `coq-iris >= 3.4.0`); per-directory READMEs (the multiparty one is an ICFP 2022 artifact; the barrier one is the artifact for "ƛ: A Self-Dual Distillation of Session Types (Pearl)").
- `julesjacobs/dlf-actris@121131ccc74c9793e620ebfcd2ae6d6bc6545169`: `theories/base_logic/adequacy.v:263-267, 290-302`, `theories/base_logic/aprop.v:34`, `theories/base_logic/cgraph.v:34-38`, `README.md`. The tip `02a9c468aa5b8d8f6e87476871756a4514ac4af0` contains only a README.
- `move-language/move@c453c90994cba0af30314fe4134acee57fb20d0c`, under `language/move-bytecode-verifier/src/`:
  - `locals_safety/mod.rs:41-55, 73-95`, `locals_safety/abstract_state.rs:17-25, 100-124`;
  - `type_safety.rs:434-442, 458-463, 641-656, 729-737`;
  - `ability_field_requirements.rs:20-52`, `stack_usage_verifier.rs:5-11`, `absint.rs:63-133`, `verifier.rs:87-117`.
- `austral/austral@0962d2a8a5d77f7daacd7f696819520733f4897d`:
  - `lib/LinearityCheck.ml:16-30, 98-122, 306-365, 572-618, 685-714`;
  - `lib/TypingPass.ml:397-466`, `lib/Env.ml:302-309`, `lib/prelude.c:92-104`, `lib/builtin/Memory.aui`, `test-programs/runner.py:356-372`.
- `ghc/ghc@83038fbee5efea8e3ebd5090b2ff5537462e169d`: `docs/users_guide/exts/linear_types.rst:1-40, 340-377`; `docs/users_guide/debugging.rst` (`-dlinear-core-lint` entry); `compiler/GHC/Core/Multiplicity.hs` (414 lines); `compiler/GHC/Core/UsageEnv.hs` (116 lines).
- `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/1066-safe-mem-forget.md:7-60, 80-110`.
- Papers. All DOIs were verified against Crossref, and the arXiv identifiers against arXiv, on 2026-11-20:
  - Bizjak, Gratzer, Krebbers, Birkedal, POPL 2019, 10.1145/3290378 (text read: §2.5, §3.4, §7, §8);
  - Jacobs, Balzer, Krebbers, POPL 2022, 10.1145/3498662, and ICFP 2022, 10.1145/3547638;
  - Jacobs, Balzer, POPL 2023, 10.1145/3571229;
  - Jacobs, Hinrichsen, Krebbers, POPL 2024, 10.1145/3632889;
  - DeLine, Fähndrich, PLDI 2001, 10.1145/378795.378811 (text read: §2.4, §3, §4, §6);
  - Blackshear, Dill, Qadeer, Barrett, Mitchell, Padon, Zohar, arXiv:2004.05106v2 (text read: §3, §5, Theorem 5.10);
  - Zhong, Cheang, Qadeer, Grieskamp, Blackshear, Park, Zohar, Barrett, Dill, CAV 2020, 10.1007/978-3-030-53288-8_7 (text read: §2, evaluation table);
  - Bernardy, Boespflug, Newton, Peyton Jones, Spiwack, POPL 2018, 10.1145/3158093 / arXiv:1710.09756 (text read: Def. 2.1, §3 theorems, divergence paragraph);
  - Wadler, ICFP 2012, 10.1145/2364527.2364568 (text read: abstract, Theorems 1–2).
- The Austral specification at https://austral-lang.org/spec/spec.html was retrieved 2026-11-20 (sections "Linear Types and Exceptions", "Error Handling" conclusion). The web edition carries no version identifier.
- Execution:
  - Build: `python3 concat_builtins.py && dune build bin/austral.exe` with OCaml 5.4.0 and system gcc. The linker printed SFrame-format warnings, and the build succeeded.
  - Probes: `support/austral-case-join-probes/run.sh`; expected outputs are in `EXPECTED.txt`.
  - Test suite: `python3 test-programs/runner.py` → "All tests passed" (284 PASS).
  - Toy checker: `support/toy-leak-certificate-checker/OUTPUT.txt`.

## Revalidation

1. **Austral defect, cheapest check.** At a new revision, inspect `table_list_is_consistent` in `lib/LinearityCheck.ml`. If the `a::b::rest` arm still recurses on `rest`, the defect is present. To confirm by execution, build (`python3 concat_builtins.py && dune build bin/austral.exe`) and run `support/austral-case-join-probes/run.sh`: p6, p7 and p8 should be accepted, and p8 should abort with a double free. If arm ordering changes, permute the arms so that the unchecked arm is the one that differs.
2. **Move drop checks.** Grep `locals_safety/mod.rs` for `STLOC_UNSAFE_TO_DESTROY_ERROR` and `UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP`, `type_safety.rs` for `POP_WITHOUT_DROP_ABILITY` and `WRITEREF_WITHOUT_DROP_ABILITY`, and confirm that `Bytecode::Abort` remains a no-op in locals safety. For a fork, repeat these greps on its verifier crate.
3. **Logic statements.** Diff `theories/sessiontypes/safety.v`, `theories/multiparty/theorems.v` and `theories/cgraphs/cgraph.v` (cgraphs), and `theories/base_logic/adequacy.v` (LinearActris, at its current location), against the quoted text. A changed statement invalidates F1, F3 and F4. Changed proofs do not.
4. **GHC status.** Check `docs/users_guide/exts/linear_types.rst` for `:status:` and the Limitations list, and the `-dlinear-core-lint` text in `debugging.rst`.
5. **Toy checker.** `python3 leakcert_eval.py 1 500` should reproduce the counts in F9 exactly, because the generator is deterministic per seed. Throughput will vary with the host.
