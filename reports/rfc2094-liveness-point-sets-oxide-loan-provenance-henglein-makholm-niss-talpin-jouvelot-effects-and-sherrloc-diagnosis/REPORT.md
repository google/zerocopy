# Origins at control-flow joins, loop back edges and calls: NLL point sets, Polonius loan subsets, Oxide loan-set unions, region and effect inference results, SPARK permission merges, and constraint-error localization

## Summary

- **Every system examined over-approximates a reference's origin at a join with a join-semilattice element. None tracks which path a value came from.** The elements differ by system:
  - NLL (Rust RFC 2094): a set of control-flow points.
  - Polonius: a set of loans.
  - Oxide: a set of loans held in the typing environment.
  - SPARK: a point in the 4-element permission lattice RW/R/W/NO.

  The join operation is union for the set-based systems, and the greatest lower bound (most restrictive) for SPARK. A least solution exists in each fixpoint formulation because every constraint only grows a set. `Basis: normative + source + derived`.
- **NLL as specified is location-sensitive; rustc's NLL is not.**
  - RFC 2094 states constraints `('a: 'b) @ P` ("starting from the point P, the lifetime `'a` must include all points in `'b` that are reachable from the point P"). It solves them by growing every lifetime from the empty set to a fixed point, which yields the least solution.
  - rustc at `rust-lang/rust@c7d5ba5…` instead computes strongly connected components (SCCs) of the location-insensitive outlives graph. It unions the successor values once, in dependency order (`propagate_constraints`), so the subset relation holds everywhere at once.
  - This is why "problem case #3" (a reference conditionally returned on one branch) is rejected. Measured: rustc 1.100.0 rejects it with `E0499`, and rejects a loop variant with `E0502`. `Basis: normative + source + execution`.
- **Polonius variants differ precisely at joins and back edges (measured on rustc-emitted facts with `polonius-engine@bfd4c94…`).**
  - `Naive` and `DatafrogOpt` accept problem case #3 and its loop variant.
  - `LocationInsensitive` reports 11 and 2 error points on them, plus 4 on a loan that an assignment kills. It is an over-approximating pre-filter.
  - Legacy Polonius (Naive, DatafrogOpt, and `rustc -Zpolonius=legacy`) *rejects* a program in which a subset relation created on one branch meets a loan created on a later branch. NLL rejects it too; Polonius Alpha (`-Zpolonius=next`) accepts it.
  - Conversely, a conditional reborrow in a `while let` loop is accepted only by legacy Polonius.
  - Neither formulation subsumes the other.
- **Polonius Alpha is the nightly default at the pinned rustc.** `src/bootstrap/src/core/build_steps/compile.rs` sets `CFG_DEFAULT_POLONIUS_NEXT` for `nightly`/`dev` channels ("We want to enable Polonius Alpha … by default on nighty"). The executed nightly therefore accepts problem case #3 without flags; stable 1.100.0 does not. `Basis: source + execution`.
- **The cost of location-sensitive Datalog is dominated by fact volume.** rustc's legacy fact emission copies every location-insensitive outlives constraint to *every* CFG point (`emit_outlives_facts`). On a synthetic function with N two-way joins, input tuples grew 658,216 → 2,602,616 → 10,350,166 for N = 25 → 50 → 100. rustc's MIR-checking pass with `-Zpolonius=legacy` took 0.79 s → 3.5 s → 15.7 s → 105.7 s for N = 25 → 200, with peak resident memory of 1,938 MiB at N = 200. NLL and Polonius Alpha stayed at or below 0.03 s at N = 200, and at or below 1.1 s at N = 3,200. `Basis: execution (synthetic input, single runs, shared host)`.
- **Oxide unions loan sets at branches and demands an invariant environment at loops.** T-Branch requires equal variable types and unions loan sets (`⋓`). T-While re-types the condition and body once and requires the output environment to be reproduced exactly; there is no iteration. The pinned OCaml implementation matches: `union` calls `list_union` on loans, and `While` checks `gamma2 = gamma3`, else `VarEnvMismatch`. Type safety is proven on paper. 208 rustc borrowck/NLL tests agree with rustc; 407 were excluded as out of scope. `Basis: documentation + source`.
- **Region and effect inference results are mostly negative about principality once recursion or flow sensitivity enters.**
  - Tofte and Birkedal (1998) state that principal types for Tofte–Talpin region inference are an open problem. Their algorithm gives up principality to run in O(n⁴).
  - Aiken, Fähndrich and Levien (1995): "an optimal completion does not always exist". Their constraints have multiple solutions, resolved by a prove-then-choose heuristic. The closure analysis is worst-case exponential; constraint solving is low-order polynomial.
  - Talpin–Jouvelot 1992 was examined only through its abstract, which claims soundness and a reconstruction algorithm "correct … with respect to the static semantics".
  - Henglein–Makholm–Niss 2001 was **not examined**.
- **SPARK merges permissions by greatest lower bound and has no loop fixpoint.** The language reference at `AdaCore/spark2014@d737789…` scopes borrows and observes lexically ("between the point where a path is borrowed and the end of the scope of the borrower"). It states no explicit join rule. Jaloyan (2017) merges branch environments by pointwise greatest lower bound (glb, "Fusion"). Loops only require that permissions at loop exit be no more restrictive than at entry. The paper proves no-aliasing on paper, for a loop-free fragment. `Basis: normative + documentation`.
- **rustc explains a conflict by naming one path.**
  - For a conflicting access, rustc runs a breadth-first search (BFS) over the outlives graph for the first sub-region live at the conflict. A second BFS forward over the control-flow graph finds the first use, giving "borrow later used here". A special case handles loops ("in later iteration of loop").
  - For region errors, it takes the shortest constraint path and picks the most "interesting" category, preferring returns (`best_blame_constraint`).
  - General constraint-graph localization does better on type errors in published evaluations. SHErrLoc found 96% of error locations on 336 OCaml programs, against about 75% for OCaml (journal version), and 88–89% on Haskell against 48–68% for GHC. A learned ranker (Nate) reaches 72% top-1, against 56% for SHErrLoc and 44% for OCaml.
  - No published evaluation measures borrow-checker diagnostics this way; an evaluation design is given below.

## Applicability

The report concerns how deployed and published borrow and region systems represent origins **at merge points, loop back edges and calls**. It covers which solution they compute and at what cost, and how they explain errors whose cause lies on one branch.

Subjects and their relation:

- **`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/2094-nll.md`**: the normative NLL design, read in full. It is the specification against which the rustc implementation is compared.
- **`rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`** (source, committed 2026-11-20): `compiler/rustc_borrowck/src/{region_infer,constraints,diagnostics,polonius}`, `compiler/rustc_session/src/{config,options}.rs`, and `src/bootstrap/src/core/build_steps/compile.rs`.
- **Executed compilers**:
  - rustc **1.100.0** (`0ef1bc386059596dada8fb65b50425aab2ea637a`): Polonius defaults to `Off` on non-nightly builds.
  - rustc **1.102.0-nightly** (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, 2026-11-11), the rustup toolchain `nightly-2026-11-12`. The relevant bootstrap and `Polonius::DEFAULT` lines are textually present at both `3ef0c22c…` and `c7d5ba59…`.
- **`rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df`**: `polonius-engine` (Naive, DatafrogOpt, LocationInsensitive, Hybrid, Compare), executed through a small fact-file driver preserved in `support/polonius-driver/`. Its README says: "This implementation of Polonius is mainly used for experiments. The Rust compiler uses its own implementation". rustc's `-Zpolonius=legacy` still uses this engine; `-Zpolonius=next` is a different, in-tree formulation.
- **`aatxe/oxide@203e42936b273e7f1351ce1d0ea5bb8d1b0dc5c1`** (2021): the executable Oxide type checker, examined as source. It was built with OCaml 5.4.0 (`dune build --profile release`). All 7 embedded examples in `oxexe.ml` raised `Not_found` at run time, and the cause was not diagnosed. **No Oxide behaviour is reported as executed.** The paper is Weiss et al., arXiv:1903.00982 v4.
- **`AdaCore/spark2014@d737789cf270fb29659d176793c9a40b7ae16714`**: `docs/lrm/source/declarations-and-types.rst`, the SPARK language reference section on access-type ownership.
- **Documentation**:
  - `rust-lang/rustc-dev-guide@d946d7402d269990f3b64baabaf6592409791c11` (region inference chapters).
  - `rust-lang/blog.rust-lang.org@8666f7c3a86260ec58e4d914d451b14613c690a4`: "Polonius update" (2023-10-06) and "Enabling the next iteration of the borrow checker on nightly" (2026-08-04).
  - Matsakis, "An alias-based formulation of the borrow checker" (blog, 2018-04-27).
- **Papers**:
  - Talpin–Jouvelot 1992: abstract only.
  - Aiken–Fähndrich–Levien 1995: author PostScript copy, full text.
  - Tofte–Birkedal 1998: author copy, full text; secondary for principality.
  - Zhang–Myers 2014: abstract only. Numbers come from the superseding journal version, Zhang et al., *SHErrLoc*, TOPLAS 2017, read in full.
  - Zhang et al. 2015: full text. Seidel et al. 2017: full text. Jaloyan 2017: full text. Oxide v4: full text.

Exact observation versus extension:

- Accept/reject results hold for the stated compilers, flags and probe programs.
- Engine results hold for facts emitted by the nightly above.
- Scaling numbers hold for one synthetic program family on one host. They are not a claim about real crates; real-crate impact is reported only through the 2026 blog post (documentation).

## Findings

### 1. Representation of an origin at a join, a back edge and a call

| System | Origin domain | At a join | At a loop back edge | At a call | Solution computed |
|---|---|---|---|---|---|
| NLL as specified (RFC 2094) | set of CFG points, plus `end('r)` elements for named lifetimes | the region contains points of both arms reached through liveness and location-sensitive outlives `('a: 'b) @ P` | ordinary CFG edges; infinite loops get false "unwind" edges so that the exit postdominates every node (Layer 2) | named lifetimes are universal regions, and `end('r)` is added only if the CFG exit is reachable from P without leaving `'b` (Layer 4) | least fixpoint, grown from empty sets ("repeatedly growing the lifetimes until they are big enough") |
| rustc NLL (`region_infer`) | interval sets of points, plus free and placeholder regions (`RegionValues`) | the same region variable is used on both arms; outlives `'a: 'b` is location-insensitive | the same; SCCs absorb cycles | universal regions are checked against declared bounds after propagation | least solution of liveness seeds plus a global outlives closure, one union per SCC-DAG edge |
| Polonius legacy (Naive / DatafrogOpt) | set of loans per origin, per point (`origin_contains_loan_on_entry(O, L, P)`) | subset facts `subset(O1, O2, P)` and loan facts flow along CFG edges while the origins are live, merging by set union | same propagation rule; Datalog iterates to the least model | placeholder origins with `known_placeholder_subset`; error if an undeclared subset arises (rule 9) | least model of a stratified Datalog program |
| Polonius LocationInsensitive | set of loans per origin (no point) | — | — | as above | least model of a coarser program; over-approximates errors |
| Polonius Alpha (`-Zpolonius=next`) | loans reach points through a "localized" constraint graph | outlives edges are reified at the point where they arise (`a@p: b@p`); liveness edges connect `a@p → a@q` for live regions | reachability in that graph | NLL machinery for universal regions | live loans by graph traversal, then the NLL dataflow |
| Oxide (paper and `typeck.ml`) | concrete region ↦ set of loans in the stack typing Γ | `Γ′2 ⋓ Γ′3`: variable types must be equal, and loan sets are unioned | T-While: Γ2 must be reproduced by one more typing of the condition and body; no iteration | region polymorphism; `T-AppFunction` substitutes and checks where-bounds | deterministic flow-sensitive typing; not a constraint solver |
| SPARK (LRM; Jaloyan 2017) | permission RW/R/W/NO per path (a lattice) | pointwise glb ("Fusion") of the branch environments | exit permissions must be no more restrictive than entry; no fixpoint | in-mode parameters are observed and in-out parameters borrowed for the duration of the call | single forward pass |

`Basis: normative (RFC 2094; SPARK LRM) + source (rustc, polonius-engine, Oxide) + documentation (Oxide paper, Jaloyan, rustc-dev-guide, blog posts)`.

Derived observation: every row uses a monotone join, so every row loses path correlation. After `let r = if c { &a } else { &b }`, every system records that `r` may borrow from `a` *or* `b`. Writing to either owner while `r` is live is therefore an error. Measured: `join_two_owners.rs` is rejected with `E0506` by all five rustc configurations and by all three engine variants. Uniqueness of the inferred origin is thus never claimed at joins; a least *over-approximation* is computed instead.

### 2. RFC 2094 constraint system and least solution

Grammar (RFC lines 656–664): `C = true | C, (L1: L2) @ P` with `L = 'a | {P}`. Constraints arise from three sources:

- **liveness**: `(L: {P}) @ P` whenever L appears in the type of a variable live at P;
- **subtyping at the successor point** of an assignment: `('foo: 'p) @ A/1`;
- **reborrows**, through "supporting prefixes", which stop at a dereference of a shared reference.

Solution (lines 952–965): "each lifetime variable begins as an empty set and we iterate over the constraints, repeatedly growing the lifetimes until they are big enough to satisfy all constraints". A constraint `('a: 'b) @ P` adds to `'a` every point of `'b` reachable from P without leaving `'b`, found by depth-first search.

Derived properties:

- Each constraint is an extensive, monotone operator on the product lattice of point sets. The least common solution therefore exists by Knaster–Tarski, and iteration from ⊥ reaches it.
- It is the one the RFC computes.
- The RFC states no complexity. Each productive outer iteration adds at least one point, so at most |V|·|P| productive iterations occur, each costing |C| depth-first searches over the CFG. The RFC's algorithm is therefore polynomial with crude bound O(|V|·|P|·|C|·(|P|+|E_cfg|)).

The RFC accepts problem cases #1, #2 and #4 through liveness and the assignment-kill rule ("if this is an assignment `lv = <rvalue>`, then any loan for some path P of which `lv` is a prefix is killed"). Problem case #3 needs the Layer 4 rule: the first borrow "must extend to the end of the `'r`, but only if we branch to SOME". The RFC notes: "This part of the prototype is partially implemented."

### 3. What rustc actually implements (source at `c7d5ba5…`)

- `UnsolvedRegionInferenceContext::propagate_constraints` (`region_infer/region_context.rs` lines 858–886) does the following. It walks "the DAG induced by the SCC. For each SCC `A`, we visit its successors and compute their values, then we union all those values to get our own. This one-shot approach works because iteration is in dependency order."
- `RegionValues::add_region` (`values.rs` 300–304) unions whole rows of point intervals, free regions and placeholders. The constraint's `locations` field does not take part in propagation; it is used for diagnostics and for legacy fact emission.
- Consequence (derived): rustc computes the least solution of a *weaker* system than the RFC, in which `'a: 'b` holds at all points. On problem case #3, the `Some` arm's return forces `'m1: 'r`, hence `'m1 ⊇` all points. The `None` arm's `map.insert` then conflicts. This matches the 2023 Polonius update ("the existing borrowck computes a single subtype relation") and the 2026 blog post ("NLL's analysis is *flow-insensitive*").
- Complexity (derived from code structure): Tarjan SCC is O(|V|+|C|), plus at most one interval-set union per condensed edge, each O(|intervals|) ≤ O(|P|). This gives O(|V| + |C|·|P|) worst case. Measured behaviour on the synthetic family is in §6.
- Member constraints from `impl Trait` are the one place where the solver is not a pure least-solution computation. The rustc-dev-guide calls the "minimal choice" rule "consistent with the general 'flow' of region propagation, which always aims to compute a minimal value … However, it is somewhat arbitrary."

### 4. Polonius rules and variants (`polonius-engine@bfd4c94…`)

Naive (`output/naive.rs`, rule comments at lines 93–233):

```text
subset(O1,O2,P)   :- subset_base(O1,O2,P).
subset(O1,O3,P)   :- subset(O1,O2,P), subset(O2,O3,P).
subset(O1,O2,Q)   :- subset(O1,O2,P), cfg_edge(P,Q),
                     origin_live_on_entry(O1,Q), origin_live_on_entry(O2,Q).
origin_contains_loan_on_entry(O,L,P) :- loan_issued_at(O,L,P).
origin_contains_loan_on_entry(O2,L,P) :- origin_contains_loan_on_entry(O1,L,P), subset(O1,O2,P).
origin_contains_loan_on_entry(O,L,Q)  :- origin_contains_loan_on_entry(O,L,P), !loan_killed_at(L,P),
                                         cfg_edge(P,Q), origin_live_on_entry(O,Q).
loan_live_at(L,P) :- origin_contains_loan_on_entry(O,L,P), origin_live_on_entry(O,P).
errors(L,P)       :- loan_invalidated_at(L,P), loan_live_at(L,P).
subset_error(O1,O2,P) :- subset(O1,O2,P), placeholder_origin(O1), placeholder_origin(O2),
                         !known_placeholder_subset(O1,O2).
```

Negated relations are inputs (`loan_killed_at`, `known_placeholder_subset`), so the program is stratified, and its least model is the computed solution. `Basis: source`.

The other variants:

- `DatafrogOpt` (`datafrog_opt.rs`, from line 199) computes the same errors. It propagates transitive subsets only for origins that die on an edge (`live_to_dying_regions`, `dying_can_reach_live`).
- `Compare` runs Naive and DatafrogOpt and checks equal errors.
- `LocationInsensitive` (`location_insensitive.rs`, from line 34) drops points: `subset(O1,O2) :- subset_base(O1,O2,_)`. It also ignores kills, so it can only add errors.
- `Hybrid` runs LocationInsensitive first and falls back to DatafrogOpt only for potential errors.

Worst-case size, derived from the rules:

- `subset` has at most |O|²·|P| tuples, and the transitivity rule can derive O(|O|³·|P|).
- `origin_contains_loan_on_entry` has at most |O|·|L|·|P| tuples.
- These bounds are polynomial, but cubic in origins per point.

### 5. Execution: what each formulation accepts

`Basis: execution`. Probes are in `support/probes/rs/`. Accept or reject and diagnostics come from `support/probes/run_rustc_probes.sh` (`results.tsv`, `out/*.stderr`). Engine results come from `support/probes/run_engine_probes.sh` (`engine_probe_results.txt`), which runs on facts from `rustc +nightly-2026-11-12 -Zpolonius=legacy -Znll-facts`. Engine columns give the number of CFG points with an error.

| probe | stable 1.100.0 | nightly `-Zpolonius=off` | nightly default | nightly `legacy` | nightly `next` | engine Naive / DatafrogOpt / LocationInsensitive |
|---|---|---|---|---|---|---|
| RFC problem case #1 (reference stored in a variable) | accept | accept | accept | accept | accept | — |
| RFC problem case #2 (`match` arm borrow) | accept | accept | accept | accept | accept | 0 / 0 / 0 |
| RFC problem case #3 (`get_default`) | reject `E0499` | reject `E0499` | accept | accept | accept | 0 / 0 / 11 |
| problem case #3 inside `loop` | reject `E0502` | reject `E0502` | accept | accept | accept | 0 / 0 / 2 |
| RFC problem case #4 (`to_refs` list walk) | accept | accept | accept | accept | accept | — |
| reborrow killed by reassignment (from Oxide's `kill_rules.rs`) | accept | accept | accept | accept | accept | 0 / 0 / 4 |
| subset created on one branch meets a later loan (from Oxide's `unnecessary_error.rs`) | reject `E0506` | reject `E0506` | **accept** | **reject `E0506`** | **accept** | 1 / 1 / 2 |
| conditional reborrow in `while let` (example from the 2026 blog post) | reject `E0499`,`E0503` | reject | reject | **accept** | reject | 0 / 0 / 4 |
| reference joined from two owners, one owner written | reject `E0506` | reject | reject | reject | reject | 1 / 1 / 1 |
| loan created on one branch, conflicting write after the join | reject `E0502` | reject | reject | reject | reject | — |
| loan used on a later loop iteration (two variants) | reject `E0502` / `E0499` | reject | reject | reject | reject | — |
| returned reference joined from `'a` and `'b` with signature `-> &'a` | reject (lifetime error) | reject | reject | reject | reject | — |

Readings:

- The "subset meets a later loan" probe separates the two location-sensitive formulations. Legacy Polonius keeps `subset('x,'y,P)` alive along the CFG for as long as both origins are live. When `x.0 = &z` issues a loan into `'x` on the second branch, rule 5 copies it into `'y`. `'y` is live until `drop(y.0)`, so `z += 1` is reported.
- Polonius Alpha reifies the subset edge only at the point of the assignment, so the later loan does not reach `'y`.
- The `while let` probe shows the opposite gap. This confirms, by execution, the blog post's statement that Alpha "is not really a full subset" of legacy Polonius, in both directions. `Basis: execution + source (Alpha design comment in polonius/mod.rs and constraints.rs)`.

### 6. Cost at scale (synthetic joins)

Input: `support/scaling/gen_joins.py N` generates one function with N sequential blocks. Each block is `let rI: &u32 = if c[I % c.len()] { &a[0] } else { &b[0] }; acc = acc.wrapping_add(*rI); a.push(acc);`, which is accepted by every configuration. Measured with `support/scaling/measure.sh` (`rustc +nightly-2026-11-12 -Ztime-passes`; the "MIR_checking" line includes borrow checking) on an x86_64 VM (Intel Xeon @ 2.60 GHz, 96 vCPUs, 236 GiB RAM). The host was shared with unrelated workloads, and every cell is a single run. `Basis: execution`.

| N joins | NLL (`off`): MIR checking s / peak RSS MiB | Alpha (`next`) | legacy Polonius |
|---:|---|---|---|
| 25 | 0.005 / 98 | 0.006 / 96 | 0.786 / 140 |
| 50 | 0.010 / 99 | 0.011 / 98 | 3.535 / 264 |
| 100 | 0.013 / 97 | 0.011 / 100 | 15.744 / 649 |
| 200 | 0.030 / 110 | 0.022 / 107 | 105.688 / 1,938 |
| 400 | 0.062 / 123 | 0.045 / 129 | not run |
| 800 | 0.105 / 164 | 0.103 / 184 | not run |
| 1,600 | 0.411 / 272 | 0.466 / 340 | not run |
| 3,200 | 0.825 / 578 | 1.082 / 829 | not run |

Engine-only timings on the same facts (`support/scaling/engine_scaling.txt`; median of 3 runs of `Output::compute`):

| N | CFG points | origins | loans | input tuples | LocationInsensitive s | DatafrogOpt s | Naive s | Naive peak RSS |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 25 | 3,222 | 629 | 78 | 658,216 | 0.93 | 1.10 | 2.14 | 414 MiB |
| 50 | 6,422 | 1,254 | 153 | 2,602,616 | 4.13 | 4.54 | 9.18 | 1,509 MiB |
| 100 | 12,822 | 2,504 | 303 | 10,350,166 | 22.8 | 26.3 | 40.7 | 5,889 MiB |

Explanation, from source plus derived reasoning:

- Input tuples grow about 4× per doubling of N because `emit_outlives_facts` (`polonius/legacy/mod.rs` lines 202–224) emits each constraint lacking a `from_location` "at every point": `location_table.all_points().map(move |location| (constraint.sup.into(), constraint.sub.into(), location))`.
- Even the point-free `LocationInsensitive` variant pays for this input and for the shared liveness and initialization phases. That is why it is only about 15% faster than DatafrogOpt here.
- An attempt to time the repository's `clap-rs` fact set (35 MB of `subset_base`) was stopped after more than 6 minutes, at a resident set size (RSS) above 3 GiB, without completing. It is **not measured**.
- Real-crate data exists only as documentation (blog, 2026-08-04): Alpha "does strictly equal or more work compared to NLL"; top-10,000 crates show "relatively few 'significant' regressions"; the worst case seen outside them is "a 2-3x regression".

### 7. Oxide: branches, loops and calls

From the paper (arXiv:1903.00982 v4):

- Regions are "collections of these loans which together form a static approximation of the origins of references".
- T-Branch types both arms from Γ1 and rewrites the result types into one, picking "the region with the shortest scope". It requires `Γ′2 ⋓ Γ′3 = Γ′`. "⋓ requires that types of bound variables in the two stack typings be equal (which potentially demands use of T-Drop when typing the branches), and unions the loan sets for each region".
- T-While has premises `Γ ⊢ e1 ⇒ Γ1`, `Γ1 ⊢ e2 ⇒ Γ2`, `Γ2 ⊢ e1 ⇒ Γ2`, `Γ2 ⊢ e2 ⇒ Γ2`. The paper gives no algorithm for finding Γ2.
- Non-lexical behaviour comes from `gc-loans`, which empties loan sets of regions no longer mentioned in Γ. Assignment kills loans prefixed by the assigned place.
- Metatheory: progress and preservation, with paper proofs; no mechanization is claimed. NLL problem case #3 is not discussed.

From the implementation (`oxide/typeck.ml`, `oxide/meta.ml`):

- `T-Branch` (typeck.ml line 307 onward) calls `union gamma2 gamma3` and then `unify`.
- `union` (meta.ml line 869 onward) is commented "conservatively merge the static environment by: unioning loan sets for the same provenances; taking uninitialized types over initialized types". It calls `failwith` if the two environments' variable orderings differ.
- `T-While` (typeck.ml line 382 onward) types the body once, re-types the condition, and accepts only `when gamma2 = gamma3`; otherwise it fails with `VarEnvMismatch`.
- `T-ForArray`/`T-ForSlice` require the shifted body output to equal the loop entry environment.
- `outlives` in `Combine` mode (meta.ml line 462 onward) realizes subtyping between two local provenances by *copying* loans: `list_union rep1 rep2` into the outlived provenance.

Derived consequences:

- Oxide answers the join question by making the post-join environment *unique by construction*. There is no inference variable at the join, so there is no principality question.
- The loop rule trades completeness for simplicity. A loop whose loan sets grow on the first iteration is rejected rather than iterated to a fixpoint.
- `polonius.ml` in the same repository comments that, on the subset-after-join example, "Polonius errors here, and so do we". That is documentation, not an observed run; see **Applicability**.

### 8. Published region and effect inference: principality, decidability and complexity

| Work | What was examined | Principality / most precise solution | Complexity | Features that break it |
|---|---|---|---|---|
| Talpin and Jouvelot 1992, "Polymorphic type, region and effect inference" (JFP 2(3) 245–271) | abstract only | the abstract says the static semantics is "consistent with respect to the dynamic semantics" and the reconstruction algorithm "correct … with respect to the static semantics"; completeness and principality claims **not verified** | not verified | per a 2025 secondary source, TJ92 uses algebraic type schemes with subeffect constraints and ML-style let-polymorphism |
| Tofte and Birkedal 1998, "A Region Inference Algorithm" (TOPLAS 20(5)) | full text (secondary) | "It is an open problem whether Damas and Milner's result about the existence of principal types … can be extended to the region inference rules of Tofte and Talpin"; "The algorithm does not always infer principal types" | S in O(n³), R in O(n⁴) worst case, n = term size with annotations | polymorphic recursion in regions; "Polymorphic recursion in types would make the type inference problem undecidable" |
| Aiken, Fähndrich and Levien 1995 (PLDI) | full text (author copy, March 1995) | U/A/D state per region per point; "In general, the constraint system has multiple solutions"; "an optimal completion does not always exist"; resolved by repeatedly proving implied facts and making free choices; a trivial solution always exists (Tofte–Talpin placement) | extended closure analysis "worst-case exponential time"; constraint generation and solving "low-order polynomial time"; analysis "a matter of seconds" on its examples | context-insensitive choice variables shared across region environments; whole-program analysis ("serious problems for separate compilation") |
| Henglein, Makholm and Niss 2001 (PPDP) | **not examined** (full text and abstract unobtainable) | — | — | — |
| Jaloyan 2017 (SPARK pointers) | full text | no inference variables: glb merge, deterministic | not stated | loops excluded from the formal subset |

Space results in Aiken et al. Table 2 (`Basis: documentation`): on the Appel example at n = 100, the maximum storable values held are 306 against 20,709 under Tofte–Talpin, an O(n²) → O(n) change. Quicksort(500) gives 2,509 against 8,078. Factorial shows no change. The authors warn that "a small change to the program … makes a dramatic difference in the quality of the completion", and that "neither the size of our benchmarks nor the size of our benchmark suite is large enough to draw meaningful statistical conclusions".

### 9. SPARK ownership merges

The LRM at the pinned revision:

- "A given path cannot have more than one marker at a given program point" (line 629). Markers are Persistent, Observed, Borrowed and Moved.
- Observed and Borrowed hold "In the region of program text between the point where a path is borrowed and the end of the scope of the borrower" (lines 752–773). These are lexical regions, so no join problem arises for borrows.
- Moved state persists "until the object is assigned another value" (lines 798–800).
- The section states **no explicit rule** for combining markers at the end of `if`/`case` or loops.

`Basis: normative`.

Jaloyan 2017 (§2.5, App. E):

- "For conditions, we apply our rules on each block independently … and then merge those by taking, for each path, the greatest lower bound of its permission". The rule is `P-ifCondition: PermRelease(Fusion(Φ′, Φ″))`.
- "For loops, we require permissions to get only less restrictive at the end of the loop, when compared to the entry". It is implemented with an accumulator per loop.
- The analysis "does not require any additional user annotation".
- The implementation is 6,200 lines, with 30 regressions on 2,087 SPARK tests.
- The no-aliasing theorem is a paper proof for µSPARK without loops.

`Basis: documentation`.

### 10. How rustc chooses what to blame across a join (source at `c7d5ba5…`)

`MirBorrowckCtxt::explain_why_borrow_contains_point` (`diagnostics/explain_borrow.rs` lines 588–712) runs in four steps:

1. `find_sub_region_live_at(borrow_region, location)` (`region_context.rs` 563–570) does a BFS over outlives edges from the borrow's region to the *first* region live at the conflict point. The BFS comment reads: "We will stop at the first match, which ought to be the shortest path (fewest constraints)" (lines 458–460).
2. If that region is the borrow region itself, the loan was re-issued at the same location, which suggests a loop. The function then looks for a `FalseUnwind` terminator reachable in the region, and re-searches from there (`use_in_later_iteration_of_loop`).
3. `find_use::find` does a BFS forward over the CFG within the region, and returns the first statement that uses or drops a local whose type mentions the region. The result is `UsedLater` ("borrow later used here"), `UsedLaterInLoop`, or `UsedLaterWhenDropped`.
4. If no use is found, `best_blame_constraint` (lines 594–800) takes the BFS constraint path to the error region and ranks categories:
   - `Return` = 0, then unsizing `Cast` = 1;
   - then `Assignment`, `CallArgument`, `Usage`, and others = 2;
   - then generic-argument annotations = 3, predicates and opaque types = 4, `Boring` = 5, …, solver internals = 9.

   It picks the minimum. Among equal minima it takes the occurrence nearest the end of the path for free-region origins (`.rev().min_by_key`), and nearest the start for placeholders. The result is `MustBeValidFor` ("returning this value requires that `*map` is borrowed for `'r`").

Derived consequences for joins:

- The *loan* is reported at its exact borrow site, because loans are per-site.
- The *reason the loan is still live* is a single shortest path plus the first reachable use in BFS order. When several arms contribute, the other contributors are not mentioned.

Observed with stable 1.100.0:

- `join_cause_on_one_branch.rs` labels `immutable borrow occurs here` inside the `if` arm, `mutable borrow occurs here` at `v.push(2)`, and `immutable borrow later used here` at `*r`.
- `region_join_return.rs` labels the `else` arm's `y` with "function was supposed to return data with lifetime `'a` but it is returning data with lifetime `'b`" and suggests `'b: 'a`.
- `loop_previous_iteration.rs` yields "`x` was mutably borrowed here in the previous iteration of the loop" / "first borrow used here, in later iteration of loop".
- `pc3_cross_fn.rs` yields "returning this value requires that `*map` is borrowed for `'r`", which is the flow-insensitive cause stated as if it held on the `None` arm.

`Basis: source + execution`.

### 11. Constraint-graph and data-driven error localization

- **SHErrLoc** (Zhang and Myers 2014, and the journal version TOPLAS 2017):
  - Constraints form a graph whose saturation is CFL-reachability. A program fails if an unsatisfiable path exists.
  - Explanations E minimize `C1·|E| + C2·k_E`, where `k_E` counts satisfiable paths through E. This follows from an Occam prior P1 per wrong expression, and P2 < 0.5 for an expression on a satisfiable path.
  - A* search is proven optimal ("about 10s even when the size of the search space is 2^1000").
  - On 336 OCaml programs from Lerner et al.: 96% of error locations against OCaml about 75% and Seminal about 80%. Graph construction takes at most 79 s, and 95% of programs take at most 20 s. Construction is "in practice quadratic in the graph size". No asymptotic bound is stated.
  - These numbers come from the journal version; the POPL'14 text was not read.
- **Type classes** (Zhang, Myers, Vytiniotis and Peyton Jones 2015):
  - The graph is expanded with axiom-generated nodes, and termination is proven.
  - Accuracy 88% against GHC 48% and Helium 68% on 77 CE programs; 89% against 68% and 75% on 228 Helium programs.
  - Analysis takes at most 35 s, with a median of 3.3 s, and is "roughly quadratic".
- **Nate** (Seidel et al. 2017):
  - Classifiers over 282 features per subexpression, trained across cohorts on more than 5,000 University of California San Diego (UCSD) ill-typed and fixed pairs.
  - Top-1 accuracy is 72% for a multilayer perceptron with 500 hidden units (91% top-3). The comparison figures are SHErrLoc 56% (84%), OCaml 44%, Mycroft 40%, and random-from-slice 30%.
  - Run time is not reported.
  - A 31-student user study at the University of Virginia showed a non-significant trend toward Nate.

Evaluation design for borrow-checker diagnostics on join errors. This is a design only, not run:

1. **Corpus.** Accepted programs containing at least one `if`/`match` join, loop, or conditional return.
2. **Single mutation, confined to one arm.** Either insert a conflicting access while a borrow from that arm is live, or route a shorter-lived owner into a joined reference on that arm.
3. **Ground truth.** The mutated span, plus the borrow site it creates.
4. **Metric.** Use the Seidel/SHErrLoc criterion: a report is correct if a reported location lies within the ground-truth spans. Score the primary span and "any labelled span" separately.
5. **Arms.**
   - Compare NLL (`-Zpolonius=off`), Alpha and legacy.
   - Add a SHErrLoc-style ranking over the outlives graph exported with `-Znll-facts`. The ranking would add satisfiable-path counts to rustc's category ranking.
6. **Stratify** by whether the mutated arm is the one the BFS reaches first. Step 3 of §10 predicts lower accuracy when it is not.

### 12. Performance and resource footprint across the six levels

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 authoring | annotations demanded at joins | SPARK: none (Jaloyan §4.5); Oxide formal model: `let` annotations (implementation synthesizes); Rust: signature lifetimes only | documentation |
| L1 authoring | workaround cost for problem case #3 under NLL | RFC: "the resulting code is actually less efficient at runtime, since it must do multiple lookups"; human time not measured | normative text |
| L1 authoring | implementation size | Oxide `typeck.ml` + `meta.ml` + `borrowck.ml` = 1,902 lines; `polonius-engine` `output/*.rs` + `facts.rs` = 2,147 lines; SPARK checker 6,200 lines; SHErrLoc 5,000 + 2,500 lines | measured (`wc -l`) / cited |
| L2 build | `polonius-engine` + driver release build (offline) | 6.27 s | measured |
| L2 build | rustc, Oxide, SHErrLoc builds | not measured | — |
| L3 checking latency | rustc MIR checking on synthetic joins | §6 table (NLL and Alpha ≤ 1.1 s at 3,200 joins; legacy 105.7 s at 200) | measured |
| L3 checking latency | engine variants | §6 (0.93–40.7 s at N = 25–100) | measured |
| L3 checking latency | Alpha on real crates | worst case "2-3x regression" | documentation |
| L3 checking latency | SHErrLoc / type-class extension | ≤ 79 s (OCaml); median 3.3 s, ≤ 35 s (Haskell) | cited |
| L3 checking latency | Aiken et al. analysis | "a matter of seconds" | cited |
| L4 generated code | borrow-check formulation | no effect on codegen; region placement (Aiken et al.) changes space: 306 vs 20,709 values | derived / cited |
| L5 checking | — | the borrow checker *is* the checker; see L3 | — |
| L6 memory | peak RSS, rustc legacy at N = 200 | 1,938 MiB (NLL 110 MiB) | measured |
| L6 memory | Naive engine at N = 100 | 5,889 MiB | measured |
| L6 memory | legacy input volume | `subset_base` ∝ (#location-free constraints) × (#points) | source + measured |

### 13. Human comprehensibility and conceptual simplicity

- **C1.** NLL's narrative ("framing errors in terms of points", RFC §"How We Teach This") names three points: borrow, conflicting access, and later use. That fits working memory, but at a join it presents one witness. In problem case #3 the witness is wrong for the `None` arm, because the flow-insensitive solution makes the borrow live there. SHErrLoc's holistic ranking is designed to weigh *all* paths, but it outputs expressions to change, not a story. Oxide's environment-threading rules are locally checkable (one rule per construct). Its loop rule fails with a whole-environment mismatch (`VarEnvMismatch(loc, Γ2, Γ3)`), which is hard to read. `Basis: normative + source + derived`.
- **C2.** One abstraction covers every row of §1: a forward may-analysis over a join-semilattice of provenance. Loan sets are ordered by ⊆, and SPARK permissions by ≤ reversed. The rows differ only in two choices:
  - where subset edges live: global, persistent-while-live, or point-local;
  - whether loops are iterated (Datalog, NLL) or required to be invariant (Oxide, SPARK).

  The measured disagreements in §5 are exactly the cases where those two choices differ. Treating "subset relation lifetime" as an explicit parameter turns the legacy-vs-Alpha discrepancies into ordinary instances rather than special cases. `Basis: derived`.

### 14. How these systems and claims are validated

- **V1, specification adequacy.**
  - Oxide's "tested semantics": 208 rustc tests agree; 407 were excluded, of which 103 involved heap or library code and 93 traits.
  - The RFC's prototype tests (`nll/test/*.nll`) were not examined.
  - The probe matrix here is a small differential specification check across five configurations and three engines.
- **V2, checker differential testing.**
  - Polonius' `Compare` variant cross-checks Naive against DatafrogOpt.
  - rustc CI runs the UI test suite "under the polonius compare mode" (rustc-dev-guide).
  - Crater-style ecosystem runs underlie the 2026 blog's regression data (not examined).
- **V3.** Concurrency, crash and hardware validation do not apply.
- **V4, human validation.** Only Seidel et al. ran a user study (31 students; not significant). No study measures programmer comprehension of borrow-checker explanations at joins.

## Boundaries

- **Not examined.**
  - Henglein–Makholm–Niss 2001: its full text, abstract, thesis follow-ups and implementation could not be retrieved.
  - Talpin–Jouvelot 1992 beyond its abstract: its theorem statements and any principality or masking results are unverified.
  - The POPL'14 SHErrLoc text: journal numbers are used instead.
  - Aiken et al.'s technical report CSD-95-866, cited for full proofs.
  - Oxide's external test suite: a private submodule.
  - The RFC prototype `nikomatsakis/nll`.
  - rustc's crater results.
- **Not executed.** Oxide: the build succeeded, but every embedded example raised `Not_found`. SHErrLoc was not run, and no Rust front end for it exists in the sources examined.
- **Not measured.**
  - Engine time on the repository's `clap-rs` facts, which was stopped after more than 6 minutes.
  - Borrow-check time on real crates.
  - Human time to understand join diagnostics.
  - The proposed diagnostic-accuracy evaluation.
- **Unknown.**
  - Whether a *principal* origin assignment exists for Rust functions with joins, loops and recursion. No examined source proves or refutes it.
  - The systems examined sidestep the question: rustc and Polonius compute least over-approximations of origin *sets*, Oxide makes environments unique by construction, and SPARK has no origin variables.
- **Known not to apply.**
  - The RFC's location-sensitive constraint semantics do not describe rustc's NLL; rustc's outlives propagation is location-insensitive.
  - Polonius Alpha does not subsume legacy Polonius, nor the reverse (§5).
  - The scaling numbers are for one synthetic shape; they do not predict real-crate regressions.
- **Attractive stronger conclusions not established.**
  - That location sensitivity alone fixes join imprecision. Legacy Polonius is location-sensitive yet rejects the subset-after-join probe.
  - That Oxide's loop rule is complete for Rust's accepted loops. It is not examined on loops whose loan sets grow.
  - That glb merging (SPARK) is less precise than union of loan sets. The two domains are incomparable, because SPARK has lexical borrows.

## Evidence

Observation date: all sources, executions and readings are from 2026-11-20 (UTC).

Source (full commits in `REPORT.json`):

- `rust-lang/rfcs@f43d578…` `text/2094-nll.md`:
  - lines 97–420: problem cases #1–#4;
  - lines 591–674: regions as point sets and the constraint grammar;
  - lines 683–951: liveness, subtyping and reborrow constraints;
  - lines 952–1061: solving and the correctness intuition;
  - lines 1280–1336: Layer 2, false unwind edges;
  - lines 1409–1516: Layer 4, `end('r)`;
  - lines 1540–1593: loans in scope and kills;
  - lines 1969–1992: errors during inference.
- `rust-lang/rust@c7d5ba5…`:
  - `compiler/rustc_borrowck/src/region_infer/region_context.rs`: lines 391–559 (constraint-path BFS), 563–570 (`find_sub_region_live_at`), 594–800 (`best_blame_constraint`), 858–886 (`propagate_constraints`).
  - `region_infer/values.rs` 300–304 (`add_region`).
  - `diagnostics/explain_borrow.rs`: 29–42 (`BorrowExplanation`), 588–712.
  - `diagnostics/find_use.rs` (`find`, BFS).
  - `polonius/mod.rs`: 1–33 (Alpha design: "Loan propagation is seen as a reachability problem").
  - `polonius/constraints.rs` 15–31 (localized outlives constraints).
  - `polonius/legacy/mod.rs` 202–224 (`emit_outlives_facts`).
  - `compiler/rustc_session/src/config.rs` 3835–3867 (`enum Polonius`, `DEFAULT`).
  - `compiler/rustc_session/src/options.rs` 1064–1080 (`parse_polonius`).
  - `src/bootstrap/src/core/build_steps/compile.rs` 1374–1381.
- `rust-lang/polonius@bfd4c94…`:
  - `README.md`;
  - `polonius-engine/src/output/mod.rs` 25–42 (`Algorithm`);
  - `naive.rs` 93–233;
  - `datafrog_opt.rs` 199–316;
  - `location_insensitive.rs` 34–109;
  - `facts.rs` (`AllFacts`).
- `aatxe/oxide@203e429…`:
  - `oxide/typeck.ml` 307–318 (T-Branch), 382–393 (T-While), 394–412 (T-For);
  - `oxide/meta.ml` 462–505 (`outlives`), 607–613 (`unify`), 869–888 (`union`);
  - `oxide/polonius.ml` (the `unnecessary_error` example and its comment);
  - `README-submission.md` (208/407 test counts).
- `AdaCore/spark2014@d737789…` `docs/lrm/source/declarations-and-types.rst`: 403–450 and 620–870.
- `rust-lang/rustc-dev-guide@d946d74…`: `src/borrow-check/region-inference.md`, `…/constraint-propagation.md`, `…/member-constraints.md`.
- `rust-lang/blog.rust-lang.org@8666f7c…`: `content/inside-rust/polonius-update/index.md` and `content/enabling-polonius-alpha-on-nightly/index.md`.

Papers. DOIs were verified through the doi.org handle API plus OpenAlex, because Crossref was unreachable through the available fetcher. arXiv identifiers were verified on arXiv abstract pages.

- Talpin and Jouvelot, JFP 2(3):245–271, 1992, DOI 10.1017/S0956796800000393 (abstract only).
- Aiken, Fähndrich and Levien, PLDI 1995, pp. 174–185, DOI 10.1145/207110.207137. Cited §3–§7 and Table 2 of the author copy.
- Tofte and Birkedal, "A Region Inference Algorithm", ACM TOPLAS 20(5), 1998 (author copy; DOI not verified, so omitted). Cited §1, §6 and §10.
- Zhang and Myers, POPL 2014, pp. 569–581, DOI 10.1145/2535838.2535870 (abstract).
- Zhang, Myers, Vytiniotis and Peyton Jones, "SHErrLoc: A Static Holistic Error Locator", ACM TOPLAS 39(4), 2017, DOI 10.1145/3121137. Cited §2, §9–§10.
- Zhang, Myers, Vytiniotis and Peyton Jones, PLDI 2015, pp. 12–21, DOI 10.1145/2737924.2738009. Cited §5–§8.
- Seidel, Sibghat, Chaudhuri, Weimer and Jhala, PACMPL 1(OOPSLA) Article 60, 2017, DOI 10.1145/3138818; arXiv:1708.07583. The arXiv page's "related DOI" 10.1145/3133884 does not match the printed DOI. Cited §4.
- Jaloyan, "Safe Pointers in SPARK 2014", arXiv:1710.07047 v1. Cited §2.5, §3.4, §4 and App. E–F.
- Weiss, Gierczak, Patterson and Ahmed, "Oxide: The Essence of Rust", arXiv:1903.00982 v4 (2021-10-19). Cited §2.2, §3.1–3.8, §4.1, App. C.
- Balik, Jędras and Polesiuk, arXiv:2510.20532 (2025). This is a secondary description of Talpin–Jouvelot's algorithm.
- Matsakis, "An alias-based formulation of the borrow checker", smallcultfollowing.com, 2018-04-27.

Execution. Host: x86_64 Linux VM, Intel Xeon @ 2.60 GHz, 96 vCPUs, shared with other jobs.

- `support/probes/run_rustc_probes.sh rs out` reproduces `support/probes/results.tsv` and `out/*.stderr`. It was re-run once and the table reproduced identically.
- `support/probes/run_engine_probes.sh rs facts <driver>` reproduces `engine_probe_results.txt`; it was likewise re-run once and reproduced identically. The driver (`support/polonius-driver/`) was built with cargo 1.100.0 against `polonius-engine` 0.13.0 at the pinned revision, with datafrog 2.0.1.
- `support/scaling/measure.sh N off next legacy` produces `scaling.tsv`. `engine_scaling.txt` holds the driver's `median_s` over 3 runs, plus `/usr/bin/time` peak RSS.

## Revalidation

- **Is Polonius Alpha still nightly-only?** Grep `CFG_DEFAULT_POLONIUS_NEXT` in `src/bootstrap/src/core/build_steps/compile.rs`, and `Polonius::DEFAULT` in `compiler/rustc_session/src/config.rs`. Then run `support/probes/run_rustc_probes.sh` with a new stable toolchain in place of 1.100.0. If stable accepts `pc3_cross_fn.rs`, Alpha has shipped.
- **Has the NLL solver become location-sensitive?** Diff `propagate_constraints` and `RegionValues::add_region`. Location-insensitivity holds as long as propagation is a union over SCC successors.
- **Have the formulation gaps closed?** Re-run the probe matrix. The two discriminating rows are `subset_after_join` (legacy rejects, Alpha accepts) and `alpha_limit_loop` (legacy accepts, Alpha rejects).
- **Explanation policy.** Diff `explain_why_borrow_contains_point`, `find_use::find`, and the `constraint_interest` table in `best_blame_constraint`. Re-run `join_cause_on_one_branch.rs`, `pc3_cross_fn.rs` and `loop_previous_iteration.rs`, and compare their `.stderr`.
- **Legacy fact volume.** Grep `all_points()` in `polonius/legacy/mod.rs::emit_outlives_facts`. Running `measure.sh 25 legacy` should take seconds, not minutes.
- **Oxide and SPARK.** Their pinned sources are frozen. For SPARK, a newer LRM revision should be re-read at the ownership section for an explicit merge rule.
- **Literature.** Fixed. The open items (TJ92 full text, HMN 2001) require obtaining the papers. No probe substitutes for them.
