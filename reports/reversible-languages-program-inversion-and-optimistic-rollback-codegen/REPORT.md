# Reversible Languages, Program Inversion, and Optimistic Rollback Code Generation (Janus, Pi/Theseus, NiLang, ROSS, Backstroke)

## Summary

Undoing a computation is implemented by four different mechanisms that place the obligation `undo(do(s)) = s` on different parties and pay for it in different currencies:

1. **Reversible by construction** (Janus, the Pi family, Theseus). Only injective steps are expressible; every statement has a syntactic inverse; nothing is logged. The price is that each control-flow join needs a predicate that tells the backward run which arm was taken (Janus `fi e`, `from e`, `delocal x = e`) or a syntactic coverage discipline (Theseus clauses). In Janus those predicates are checked at run time, so a Janus program can abort in either direction.
2. **Reversible embedding of irreversible code** (Bennett compute-copy-uncompute and its checkpointed recursion). Nothing is required of the source program; the price is garbage: `T` irreversible steps cost either `T+1` live states and `2T-1` step applications, or at most `n(k-1)+2` live states (input and output included) and `(2k-1)^n` step applications for `T = k^n`.
3. **Reversible eDSL used as a differentiable language** (NiLang). Janus-style statements plus a compute/uncompute macro; reverse-mode AD retraces the program backwards instead of reading a tape. Floating-point `+=`/`-=` are *treated* as mutually inverse although they are not, and reversibility checks on floats are tolerance-based.
4. **Optimistic execution with rollback** (Time Warp as implemented in ROSS). Events are executed speculatively; a straggler forces rollback of already-processed events, cancellation of the messages they sent, and re-execution. Rollback is realized either by hand-written reverse event handlers (reverse computation) or by logging overwritten values (incremental state saving); undo data is discarded, and deferred effects are released, only when Global Virtual Time (GVT) passes the event.

Facts that are easy to get wrong:

- **Released Backstroke 2.x does not emit reverse functions.** It rewrites C++ so that every assignment target, `new`, and `delete` in the *forward* code calls a runtime state store (RTSS); "reverse" and "commit" are two generic library functions that pop or drop that per-event log. It is incremental state saving, not program inversion.
- **ROSS trusts the model author's reverse handler** but ships a scheduler mode (`--synch=6`, `SEQUENTIAL_ROLLBACK_CHECK`) that executes every event forward, rolls it back, compares the logical-process state and random-number streams byte-for-byte with a checkpoint, then re-executes and commits.
- **Jana, the Janus interpreter examined here, decides aliasing dynamically**: `a[i] += a[j]` is accepted when the evaluated indices differ and rejected when they coincide; `x += x` and reading the assigned array in its own index expression are always rejected.
- **Bennett's trade-off constants are exact and small enough to check**: the recursion used by NiLang's `bennett!` performs `(2k-1)^n` step applications and holds at most `n(k-1)+2` states (including input and output); the probe in this report reproduces both formulas.
- **A wrong exit assertion is not a benign annotation error**: with checks disabled, the inverse silently takes the wrong branch and returns a state that was never a predecessor (probe, 32-bit two's-complement values: `3` goes forward to `-2`, the unchecked inverse returns `-3`).

## Applicability

The subjects listed in `REPORT.json` are examined as *independent exemplars* of the four mechanisms; no claim is made about their combination except where stated (Backstroke's ROSS integration layer, NiLang depending on NiLangCore).

- **Janus** behavior is taken from the Jana interpreter (`mbudde/jana`, cabal version 1.0, authors Michael Budde and Claus Skou Nielsen) at the pinned revision, by source inspection. Jana was not built or run. The original Janus papers (Lutz and Derby 1986; Yokoyama and Glück, PEPM 2007, DOI `10.1145/1244381.1244404`; Yokoyama, Axelsen and Glück, CF 2008, DOI `10.1145/1366230.1366239`) were identified by bibliographic metadata only; their full text was not obtained, so nothing here should be read as a statement of what those papers define beyond what Jana implements and what James and Sabry (2014) report about Janus.
- **Pi and Theseus** are taken from James and Sabry, *Information Effects* (POPL 2012; abstract, introduction, and the passages defining Pi and the `create`/`erase` operations were read) and *Theseus: A High Level Language for Reversible Computing* (2014; sections 1-3 and 5 and the concluding discussion were read), using the PDF copies carried at `papers/` in `chessai/theseus` at the pinned revision. That repository is also examined, at README, specification-index and theorem-name level only, as a later Rust/Lean implementation in the same lineage; it is not the authors' original implementation (the paper points to a Bitbucket repository that was not examined) and was not built or run.
- **NiLang** findings combine source inspection of NiLang.jl 0.9.4 and NiLangCore.jl 0.10.7 at the pinned revisions with arXiv:2003.04617v3 (abstract, sections 2-3 and Appendix F were read). The paper states it describes NiLang v0.7.3; where the paper and the pinned source could differ, the source is cited. No Julia code was executed.
- **ROSS** findings are source inspection of `core/` at the pinned revision (`.version` file: 8.1.1). ROSS was not built or run; in particular no multi-process (MPI) behavior was observed.
- **Backstroke** findings are source inspection of the tool, its RTSS runtime header, and the LaTeX user manual at the pinned revision. Backstroke needs the ROSE compiler infrastructure and was not built or run. The paper abstracts (RC 2015, New Generation Computing 2018) were read; the paper bodies were not.
- **Bennett (1989), Jefferson (1985), Carothers et al. (1999)**: abstracts only (publisher page or Crossref deposit).
- **Execution evidence** is limited to the Python probe reproduced under Evidence. It models the mechanisms; it does not execute any of the subject systems. Probe results therefore support claims about the *mechanisms* (and about formulas that the subjects document), not about the subjects' implementations.

## Findings

### 1. Mechanism taxonomy

| Mechanism | What must be stored to undo | Who establishes `undo . do = id` | What happens when that fails | Exemplar examined |
|---|---|---|---|---|
| Injective statements with join predicates | Nothing | Language (statement forms) plus programmer (predicates), checked dynamically | Run-time assertion failure in the forward or backward run | Jana |
| Clause-wise isomorphisms | Nothing | Type and coverage checker | Program rejected statically; non-termination remains possible | Theseus paper; `chessai/theseus` |
| Compute-copy-uncompute | All intermediate results until uncomputed | Construction (inverse of each step is known) | Not applicable; cost is space/time | Bennett 1989; NiLang `@routine`, `bennett!` |
| Reverse event handlers | Per-event control bits and whatever the handler cannot recompute | Model author, per handler | Silent divergence from the sequential result unless a checker is run | ROSS |
| Incremental state saving | `(address, old value)` per executed write, per event | Instrumentation tool plus the assumption that all state-changing code was instrumented | Silent partial rollback for uninstrumented code | Backstroke RTSS |
| State snapshot / delta | Copy or compressed delta of the whole LP state per event | Runtime | None for state covered by the copy; pointers are copied shallowly | ROSS `tw_snapshot*` |

Basis: derived from the source and documentation findings in sections 2-7.

### 2. Janus as implemented by Jana

Statement forms, their inverses, and the dynamic obligations (function names are in `src/Jana/`):

| Statement | Inverse produced by `invertStmt` | Run-time obligation in `evalStmt` |
|---|---|---|
| `x += e`, `x -= e`, `x ^= e` | `x -= e`, `x += e`, `x ^= e` | assigned variable must not occur in `e` (alias check below) |
| `x <=> y` | itself | types must agree |
| `if e1 then s1 else s2 fi e2` | `if e2 then inv(s1) else inv(s2) fi e1` | after `s1`: `assertTrue e2`; after `s2`: `assertFalse e2` |
| `from e1 do s1 loop s2 until e2` | `from e2 do inv(s1) loop inv(s2) until e1` | `assertTrue e1` on entry; `assertFalse e1` after every `s2` |
| `local t x = e1` ... `delocal t x = e2` | `local t x = e2` ... `delocal t x = e1` | at `delocal`, the value of `x` must equal `e2`, else "Expected value to be ... for local variable ..." |
| `push(x, s)` | `pop(x, s)` | `push` moves `x` onto `s` and zeroes `x`; `pop` requires `x = 0` ("Can't pop to non-zero variable") and a non-empty stack |
| `call p(...)` | `uncall p(...)` (see below) | arguments are passed by reference |
| statement sequence | inverted statements in reverse order | - |

Details that matter when porting or verifying:

- **Two inversion modes.** `invertProgram` inverts every procedure body but leaves `call`/`uncall` statements unchanged ("Globally"); inverting a single procedure flips `call` and `uncall` ("Locally"). Both are consistent: after global inversion `call p` already reaches the inverted body.
- **Loop semantics are asymmetric in `s1`/`s2`.** `s1` runs at least once; the exit test `e2` is evaluated after `s1`; `s2` runs only when the loop continues. The entry predicate `e1` must be true exactly on first entry.
- **Alias discipline is partly dynamic.** For `id op= e` the expression is evaluated with the assigned identifier as context; any read of an identifier that is the same as, or recorded as an alias of, the target raises "Identifiers ... are aliases". For `id[i] op= e`: the index expression is evaluated with the *whole array* as context (so `x[x[0]] ^= 1` is an error), then `e` is evaluated with the context `id[<evaluated index>]`; a read `id[m]` inside `e` raises the alias error only if `m` equals the evaluated index. Hence `a[i] += a[j]` is accepted when `i != j` at run time and rejected when `i = j`.
- **Reference parameters create aliases that are tracked as a set of name pairs.** `call foo(x, x)` binds two formals to one actual; the pair is recorded (`introduce`) and propagated through nested calls (`propagate`); the error is raised when an assignment actually reads one name while writing the other (test programs `tests/errors/alias-1.ja`, `alias-2.ja`), not at the call.
- **Integer width is an option.** With `-m`, values are normalized to `[-2^31, 2^31)` after expression evaluation (`numberToModular`); without it they are not wrapped. A program can therefore be reversible in one mode and fail an assertion in the other (`tests/errors/modular-integer.ja` distinguishes the modes on purpose).
- The shipped examples include the recursive Fibonacci-pair procedure (`if n = 0 then x1 += 1; x2 += 1 else n -= 1; call fib; x1 += x2; x1 <=> x2 fi x1 = x2`) and an integer square root adapted from Lutz and Derby with `local`/`delocal` and nested `from`/`if` assertions.

Basis: source (`Eval.hs` `assignLval`, `evalStmt`, `evalLval`, `checkLvalAlias`, `numberToModular`; `Invert.hs`; `Aliases.hs`; `ErrorMessages.hs`; `tests/errors/*.ja`; `examples/fib.ja`, `examples/sqrt.ja`).

James and Sabry (2014) characterize the same design from outside: every primitive statement is reversible, procedures can be called or uncalled, "the same value may not be referenced twice to avoid aliasing issues", and "both the choice of deallocation-time values and predicates for inverse control flow are application specific choices ... hard to determine in general and can result in programs that will not correctly execute in reverse". Basis: documentation (peer description in the Theseus report).

Why the assertions and the alias rule are load-bearing (probe section A; a Python model of the statement forms above, not Jana itself):

- An iterative Fibonacci-pair loop maps `(x1, x2, n) = (0, 0, 10)` to `(89, 144, 0)`; the statically inverted program maps it back.
- For `if x > 0 then x -= 5 else x += 1 fi (x > 0)` on 32-bit wraparound integers, with the exit test read as signed positivity (`0 < x < 2^31` in the probe), input `7` passes (`2`, assertion true). Input `3` takes the then-arm, yields `-2` (printed as `4294967294`), and violates the exit assertion. If the check is skipped, the inverse evaluates the predicate on that value, takes the *else* inverse, and returns `-3` (printed as `4294967293`): a well-formed state that is not the predecessor.
- On two 2-bit cells, `a[0] ^= a[1]` and `a[0] += a[1]` are bijections of the 16 states; with the indices equal, `a[0] ^= a[0]` reaches 4 states and `a[0] += a[0]` reaches 8. No inverse exists, so the aliasing rule cannot be replaced by a join predicate.

Basis: execution (probe lines `A1`-`A3`).

### 3. Pi, Theseus, and information effects

**Pi-o (the target calculus).** Value types `b ::= 0 | 1 | b + b | b * b | x | mu x.b`. Programs are witnesses of type isomorphisms, each line giving a combinator and its inverse:

| Isomorphism | Left-to-right | Right-to-left |
|---|---|---|
| `0 + b <-> b` | `zeroe` | `zeroi` |
| `b1 + b2 <-> b2 + b1` | `swap+` | `swap+` |
| `b1 + (b2 + b3) <-> (b1 + b2) + b3` | `assocl+` | `assocr+` |
| `1 * b <-> b` | `unite` | `uniti` |
| `b1 * b2 <-> b2 * b1` | `swap*` | `swap*` |
| `b1 * (b2 * b3) <-> (b1 * b2) * b3` | `assocl*` | `assocr*` |
| `0 * b <-> 0` | `distrib0` | `factor0` |
| `(b1 + b2) * b3 <-> (b1 * b3) + (b2 * b3)` | `distrib` | `factor` |
| `b[mu x.b / x] <-> mu x.b` | `fold` | `unfold` |

Closure combinators: `id`, `sym c`, sequential composition, `c1 + c2`, `c1 * c2`, and `trace c : b2 <-> b3` for `c : b1 + b2 <-> b1 + b3` (looping). Every combinator has an adjoint that is homomorphic on the structure except that sequencing reverses order. "Logically reversible" is defined as: `c1 : b1 -> b2` has an inverse map `c2` with `c1(v1) = v2` iff `c2(v2) = v1`. With `trace`, programs are *partial* isomorphisms: non-termination is admitted.

**Theseus (the surface language).** A map `f :: a <-> b` is a list of clauses `pattern <-> pattern` over user-defined algebraic types. Reversibility is guaranteed by exactly two rules:

1. *Non-overlapping and exhaustive coverage on both sides*: the left-hand patterns are a complete, non-overlapping covering of the input type, and the right-hand patterns a complete, non-overlapping covering of the output type.
2. *Typed variables are preserved*: each variable occurs once on a side and exactly once on the other side, with the same type.

The inverse is obtained by swapping the two sides of every clause. Iteration uses typed *labels*: a clause may jump to a label on the right and resume from a label pattern on the left; the label's occurrences on each side must themselves cover the label's type. The paper's rejected examples are a missing left-hand case, overlapping right-hand cases (`0 <-> 0` and `Succ n <-> n`), a dropped variable, and a duplicated variable. The paper states that the fragment without labels (modulo full recursive types) is expressible in Pi without `trace`, that all Pi-o programs are expressible in Theseus and vice versa, and lists as missing an error mechanism and "an FFI mechanism to take advantage of third-party libraries".

**Information effects.** Irreversible computation is recovered on top of Pi by an arrow metalanguage with exactly two effect operations, `create_b : 1 ~> b` and `erase : b ~> 1`. The paper notes an inherent asymmetry: `create` always introduces a known constant, while `erase` discards information known only at run time. Derived consequence for interface design: an irreversible callee is, in this model, a reversible one plus explicit `erase` (garbage that the caller does not get back) and `create` (fresh constants), which is the same accounting as the garbage output of Bennett's embedding in section 4.

Basis: documentation (text of both papers; the passages read are listed under Applicability).

**A later implementation in this lineage (`chessai/theseus`).** The README describes a linearly typed reversible language with sums, products, isomorphism clauses and bounded iteration, a compiler to a reversible instruction set, and Lean 4 proofs. Checked against the tree at the pinned revision: the checker has diagnostics for linearity (`T0201` variable used a wrong number of times, `T0202` variable bound on one side only) and coverage (`T0301` non-exhaustive, `T0302` overlap or redundant clause, `T0303` uncovered label state), which are the paper's two rules plus the label rule; `theseus-proofs/TheseusProofs/Reversibility.lean` (toolchain `leanprover/lean4:v4.31.0`) contains theorems named `denote_bijective`, `denote_inv_leftInverse`, `denote_inv_rightInverse`, `seq_inv`, `iter_bijective`, and `card_preserved`. The README states that in its "synthesizable" dialect every program is a *total* bijection with a static worst-case running time, i.e. it trades the paper's unbounded labels/`trace` for bounded iteration. Basis: documentation (README) + source (diagnostic and theorem names only; proofs not checked, nothing built).

### 4. Bennett's embedding and its exact costs

Bennett (1989) states: for any `eps > 0`, an ordinary multitape Turing machine using time `T` and space `S` can be simulated by a reversible one using time `O(T^(1+eps))` and space `O(S log T)`, or in linear time and space `O(S T^eps)`; these results are for machines that *save their input*, and a reversible machine that erases its input can compute only injective partial functions. Basis: documentation (abstract).

The recursion behind the first bound, as implemented in NiLang's `bennett!` (`src/stdlib/bennett.jl`) and given as pseudo-code in the NiLang paper: to advance `len` steps from a stored state, split into `k` sub-segments, compute them left to right (each recursively), then uncompute the first `k-1` sub-segments in reverse order, leaving only the segment's final state. The source documents the expected log sizes as "`(2k-1)^n`" calls and peak memory "`n*(k-1)+2`" for `k^n` steps.

| `k` | `T = k^n` | step applications `(2k-1)^n` | exponent `log_k(2k-1)` | peak live states `n(k-1)+2` | naive compute-copy-uncompute |
|---|---|---|---|---|---|
| 2 | 16 | 81 | 1.585 | 6 | 31 steps, 17 states |
| 2 | 1024 | 59049 | 1.585 | 12 | 2047 steps, 1025 states |
| 3 | 243 | 3125 | 1.465 | 12 | 485 steps, 244 states |
| 4 | 1024 | 16807 | 1.404 | 17 | 2047 steps, 1025 states |
| 8 | 4096 | 50625 | 1.302 | 30 | 8191 steps, 4097 states |

The naive column is the `n = 1`, `k = T` instance of the same formulas (`2T-1` step applications, `T+1` states).

The probe reimplements the recursion and asserts both closed forms; the two states that remain at the end are the input and the output, as the "save the input" qualification requires. Increasing `k` lowers the time exponent toward 1 and raises the number of live states per level, which is the `T^(1+eps)` versus `S log T` trade. The NiLang paper summarizes the same comparison against checkpointing for AD: checkpointing can reach `O(S)` space at `O(T^2)` time, whereas the most space-efficient reverse-computing scheme it lists is time `O(T (T/S)^0.585)` at space `O(S log(T/S))`, "the reversibility of the original program is not utilized".

Basis: source (NiLang `bennett.jl`) + documentation (NiLang paper section 2) + execution (probe lines `B`); the exponent column is derived arithmetic.

### 5. NiLang: a reversible eDSL whose inverse doubles as the adjoint sweep

**Statement inversion table** (`NiLangCore/src/dualcode.jl`, `dual_ex`):

| Statement | Dual |
|---|---|
| `a += f(b...)` / `a -= f(b...)` | each other |
| `a *= b` / `a /= b` | each other |
| `a ⊻= b` | itself |
| `x ← val` (allocate) / `x → val` (deallocate) | each other |
| `s[end+1] ← x` (push) / `s[end] → x` (pop) | each other |
| `x ↔ y` | `y ↔ x` (with special cases for empty variables and stack ends) |
| `f(args...)` | `(~f)(args...)` |
| `if (pre, post) ... end` | `if (post, pre) ... end` with dual bodies |
| `while (pre, post) ... end` | `while (post, pre) ... end` with dual body |
| `for i = a:s:b ... end` | `for i = b:-s:a ... end` with dual body |
| block | dual statements in reverse order |
| anything else | `error("can not invert target expression ...")` |

**Compiled obligations** (`compiler.jl`): an `if (pre, post)` stores `pre` in a fresh variable before the branch and, when checking is on, asserts afterwards that `post` equals it; a `while (pre, post)` asserts `post` false before the loop and true after each iteration; `for` re-evaluates and compares the range bounds afterwards; `x → val` asserts the value on deallocation. A statement whose operands share memory is rejected when the enclosing function is defined (`InvertibilityError`, "shared read and shared write are not allowed"; the documentation example is `out! += abs2(out!)`). `@invcheckoff` removes the run-time checks for a block; `@safe` inserts an arbitrary irreversible host-language statement that the inverter passes through unchanged.

**Compute-copy-uncompute as syntax.** `@routine stmt` records a statement; `~@routine` emits its inverse. The documented pattern is compute ancillas, accumulate the result with `+=`, uncompute. Basis for the three paragraphs above: source + documentation (`docs/src/tutorial.md`, `docs/src/grammar.md`).

**Number systems and exactness.** The paper states: for integer and fixed-point numbers `y += f(...)` and `y -= f(...)` are rigorously reversible; for logarithmic numbers `*=` and `/=` are (without the zero element); for floating-point numbers "none of the above operations are rigorously reversible", and "for convenience, we ignore the round-off errors in floating-point + and - operations". The paper also lists as "reversible hardware incompatible features" that NiLang views floating-point `+`/`-` as reversible, lets users extend the instruction set, and allows inserted external statements. In the source, the generic equality used by reversibility checks is `a === b || abs(b - a) < atol` for floats (`almost_same`, `checks.jl`), and the FAQ gives the default `NiLangCore.GLOBAL_ATOL[]` as `1e-8` and recommends raising it or using `@invcheckoff` "due to the fact that floating pointing numbers are not exactly reversible". Basis: documentation + source.

Magnitude of the float issue (probe section C): for 200000 pseudo-random binary64 pairs with decimal exponents in `[-8, 8]`, `(x + y) - y != x` in 96267 cases (48.1%); the same test on 64-bit wraparound integers fails 0 times; adding `1/i` for `i = 1..1000` to `0.1` and subtracting in reverse order ends at `0.10000000000000075`. Basis: execution. Derived consequence: a float-based reversible program reconstructs an *approximation* of each earlier state, so (a) exact-equality join predicates on reconstructed floats can flip, and (b) a gradient computed during the backward run is evaluated along a slightly different primal trajectory. The paper's Appendix F studies this for a leapfrog integrator and reports the effect is benign there when ancillas are returned to the pool (they are zero-cleared); that benchmark was not reproduced.

**Titles disagree across sources.** arXiv v3 is titled "Differentiate Everything with a Reversible Embeded Domain-Specific Language" (spelling as on arXiv); the README's BibTeX entry at the pinned revision gives "Differentiate Everything with a Reversible Programming Language". Both refer to arXiv:2003.04617.

### 6. Time Warp in ROSS: what the runtime does and what it trusts

Jefferson (1985) introduces virtual time, "implemented using the Time Warp mechanism, a synchronization protocol distinguished by its reliance on lookahead-rollback, and by its implementation of rollback via antimessages". Carothers, Perumalla and Fujimoto (1999) propose reverse computation as an alternative to state saving for realizing rollback and report "as much as a six-fold improvement in execution speed over traditional state-saving" on sample models. Basis: documentation (abstracts).

**Model ABI** (`core/ross-types.h`):

```c
typedef void (*event_f)  (void *sv, tw_bf * cv, void *msg, tw_lp * me);
typedef void (*revent_f) (void *sv, tw_bf * cv, void *msg, tw_lp * me);
typedef void (*commit_f) (void *sv, tw_bf * cv, void *msg, tw_lp * me);
struct tw_lptype { init_f init; pre_run_f pre_run; event_f event; revent_f revent;
                   commit_f commit; final_f final; map_f map; size_t state_sz; };
```

`sv` is the logical process (LP) state of `state_sz` bytes, `msg` the event payload, and `cv` a 32-flag bitfield (`struct tw_bf`, members `c0`..`c31`, described in the source as the "Reverse Computation Bitfield") stored in the event so that the forward handler can record which branches it took for the reverse handler. The payload itself is the other place a handler can stash overwritten values.

**Rollback path.** A straggler makes the scheduler call `tw_kp_rollback_to(kp, t)`, which pops every processed event with receive time `>= t` from the *kernel process* (a group of LPs sharing one processed-event list) and for each calls `tw_event_rollback` and re-enqueues it. Rollback granularity is therefore the kernel process, not the LP. `tw_event_rollback(event)`:

1. discards the event's buffered output messages;
2. calls `(*dest_lp->type->revent)(dest_lp->cur_state, &event->cv, tw_event_data(event), dest_lp)` (skipped if the LP was suspended and the event never ran forward);
3. frees the event's state delta, if any;
4. walks `event->caused_by_me` and cancels every event this event sent (`event_cancel`; for events already transmitted to another process this sends a cancellation over the network, the anti-message);
5. when built with the tie-breaker option, steps the core random stream backwards once per sent and per aborted event.

**Random numbers are reversible by stepping the generator backwards.** `tw_rand_reverse_unif` is `rng_gen_reverse_val`, which decrements the draw counter and multiplies each of the four stream components by `b[j]` modulo `m[j]`, where `b[j]` is precomputed at initialization as `a[j]^(m[j]-2) mod m[j]`, the modular inverse of the forward multiplier `a[j]`. Derived: a reverse handler must call it once per forward draw; the checker's diagnostic for forgetting this is quoted in section 9.

**Commit horizon.** Fossil collection (`tw_eventq_fossil_collect`, which hands the collected events to `tw_eventq_push_list`) walks committed events "in reverse to ensure correct commit order", calls the optional `commit` handler, prints and releases the event's buffered output (`tw_free_output_messages(e, 1)`; the rollback path calls it with `0`, discarding the text), and frees deltas. `tw_output(lp, fmt, ...)` is a "rollback-aware printf": in optimistic modes the text is attached to the current event and printed only when that event is committed; in sequential, conservative and rollback-check modes it prints immediately; if the kernel process has no free output buffer it prints immediately after warning "This event may be rolled back!". Each buffer holds `256 - 2*sizeof(void *)` bytes.

**State-saving alternative inside ROSS.** `tw_snapshot` copies the LP state; `tw_snapshot_delta` stores the byte-wise difference to the snapshot, LZ4-compressed, in the event; `tw_snapshot_restore` decompresses and subtracts. This restores exactly the `state_sz` bytes and nothing reachable through pointers (derived from the `memcpy`/byte loop).

**Built-in reverse-handler check.** `--synch` accepts `SEQUENTIAL=1, CONSERVATIVE=2, OPTIMISTIC=3, OPTIMISTIC_DEBUG=4, OPTIMISTIC_REALTIME=5, SEQUENTIAL_ROLLBACK_CHECK=6`. Mode 6 (`tw_scheduler_sequential_rollback_check`, single process only) does, for every event in timestamp order:

```text
prev := checkpoint(LP)                 # state bytes + rng + core_rng + gvt-hook flag
event(LP);  cur := checkpoint(LP)
tw_event_rollback(ev);  compare(LP, prev)   # "before processing event" vs "after processing event and rollback"
event(LP);  commit(LP) if defined;  compare(LP, cur)
```

The default comparison is `memcmp` over `state_sz` bytes plus `memcmp` of both random streams; a mismatch prints both byte images and aborts. A model can register a `crv_checkpointer` with custom `save_lp`, `check_lps` and print hooks. Derived limits: the default comparison does not follow pointers out of the LP state, can report padding differences, exercises only the event sequence of that sequential run, and validates the reverse handler one event deep (never a multi-event rollback or a cancellation cascade). The second comparison additionally requires that re-execution is deterministic and that `commit` leaves the LP state unchanged.

Basis for this section unless noted: source (`core/ross-types.h`, `tw-kp.c`, `tw-event.c`, `rand-clcg4.c`, `ross-random-internal.h`, `tw-eventq.h`, `tw-util.c`, `tw-state.c`, `tw-setup.c`, `tw-sched.c`, `check-revent/crv-state.{h,c}`).

Mechanism check (probe section D, a 4-LP model with one new message per event, not ROSS): randomly ordered optimistic execution with stragglers, cascading cancellations and GVT commits ends in exactly the sequential final state for three schedules, both with a hand-written reverse handler plus a backward-steppable generator and with an undo log; 62-65 stragglers cause 118-124 event undo operations in a run that commits 484 events. The undo-log variant logs three entries per executed event (1806-1824 in total, re-executions included) but at most 45-51 are live at once because commits discard them. A reverse handler that restores everything except the generator state yields a different final state, and a forward-reverse-compare check on a single event pinpoints the unrestored field. Basis: execution.

### 7. Backstroke 2.x: instrumented forward code plus a generic undo log

**What the tool emits.** For input `FILE` it writes `backstroke_FILE` containing "instrumented forward functions for all functions that are present in the input file" (headers included, since the input is preprocessed). The transformations listed by the manual: left-hand sides of all assignment forms including `++`/`--`; `new` (placement `new` is detected and left alone); `delete`; calls to overloaded global `new`/`delete`; generation of *reversible default copy-assignment operators* where the class relies on the implicit one; a `friend` declaration where a destructor is private or protected so the runtime can run it at commit. The manual's example:

```cpp
// original                         // generated forward code
if (state->x > 20) state->x = 0;    if (state->x > 20) (xpdes::avpushT(state->x)) = 0;
else state->x++;                    else (xpdes::avpushT(state->x))++;
```

There is no generated reverse function. "The reverse and commit functions in the rtss library only depend on the state information that is recorded when the reversible (instrumented) forward functions are executed." Basis: documentation (`docs/user-manual.tex`) + source (`src/TransformationSequence.C` emits `avpushT`, `registerAllocationT`, `allocateArrayT<...>`, `registerDeallocationT`).

**Runtime interface.** Generated code calls five templates: `avpushT(T& lhs)`, `registerAllocationT(T*)`, `registerDeallocationT(T*)`, `allocateArrayT<T>(n)`, `registerArrayDeallocationT(T*)`. The driver brackets each event with `xpdes::beginForwardEvent()` / `endForwardEvent()` and later calls `xpdes::reverseEvent()` or `xpdes::commitEvent()`.

**Data model and the three operations** (`src/rtss/backstroke/rtss.h`):

- Per event, an `EventRecord` holds a stack of type tags and four queues (allocations, deallocations, array allocations, array deallocations). The saved `(address, old value)` pairs live in per-type containers shared across events; event records sit in a deque.
- `avpush(address)` pushes a type tag and `(address, *address)` **only if the address is not on the program stack**: `is_stack_ptr(p)` tests `stack_bottom <= p <= stack_local`, with the bounds taken once from `pthread_getattr_np`/`pthread_attr_getstack` of the initializing thread. Writes to automatic variables are thus filtered at run time; a compile-time "local variable" optimization exists as well (`--no-optimization` disables it).
- `reverseEvent()` takes the **newest** record (`pop_back`), restores values in LIFO order, releases memory the event allocated with `::operator delete` (no destructor is run on this path), and forgets the event's registered deallocations.
- `commitEvent()` takes the **oldest** record (`pop_front`), drops its saved values, forgets its allocations, and **performs the deferred `::operator delete` calls**. In reversible mode "all delete operations are deferred until the RTSS commit function is called", which is what keeps addresses valid across a rollback. For class and union types the *destructor* is not deferred: `registerDeallocationT` runs it during the forward event with recording still on, so the destructor's own writes are logged and undone like any others, and only the release of memory waits for commit. (The manual says the generated `friend` declaration lets the runtime call the destructor "in the commit function"; the header at this revision calls it in the forward path.)
- Recording is off by default and is switched on between `beginForwardEvent` and `endForwardEvent`; calling the operations in the wrong recording state throws. Only built-in types are stored (integers, floating types, `bool`, pointers); class and union types fall through to their member-wise generated assignment; an unknown non-class type throws `Backstroke::Exception("RTSS:avpushT: unknown type.")`.

**ROSS integration.** Compiled with `-DRTSS_LIBRARY_WITH_ROSS`, the header adds a map from LP pointer to a per-LP state store (`RunTimeLpStateStore`), `beginForwardEvent(lp)`, `reverseEvent(lp)`, `commitEvent(lp)`, and, "only required if no commit function is provided by ROSS", `commitEvent(lp, now)`, which commits all records whose recorded simulation time is below the processing element's GVT.

**Stated limits.** Bitfields are not supported (the generator prints a warning and skips them in generated assignment operators; `--ignore-bitfields` exists). The user must supply every function reachable from an event for instrumentation: "If code is linked that has not been processed by Backstroke and it modifies state ... then the generated code is not reversible"; the stated general remedy is to run the entire C++ standard library through the tool. Stream input is not undone and stream output is not deferred. `#pragma reversible map forward = original` excludes a statement, block or function definition from instrumentation (intended for statistics that must not be rolled back). The paper abstracts concede "a significant runtime overhead" in exchange for handling "the entire C++ language". Basis: documentation + source.

**Residue of an inversion design.** The type-tag enum contains `BITYPE_REVERSE_FUNCTION_CALL_NO_ARGS` and a commented-out `BITYPE_REVERSE_FUNCTION_CALL_JANUS`; in `restore` the former only discards its entry. Hooks for registering reverse *functions* in the log therefore exist but are inert at this revision. Basis: source.

**Version strings disagree inside the tree**: `ChangeLog` tops out at V2.1.2 (2018-02-06), the manual's title macro says 2.1.1 (dated August 21, 2017), and `--version` prints "Version 2.1.4" (`src/CommandLineOptions.C`). The tool checks for ROSE version `0.9.9.87`.

Derived caveats from the source: the stack filter knows one thread's stack bounds (state on another thread's stack would be logged, and a heap-allocated coroutine stack would not be recognized as stack); `pthread_getattr_np` is a GNU extension; the cost is one log entry per executed non-stack write whether or not the write is algebraically invertible.

### 8. Cross-system matrix

| Property | Jana (Janus) | Theseus / Pi | NiLang | ROSS reverse handlers | Backstroke RTSS |
|---|---|---|---|---|---|
| Unit that is undone | statement / procedure (`uncall`) | whole map | statement / function (`~f`) | one event | one event |
| Inverse obtained by | syntactic inverter | swapping clause sides; adjoint | macro-time `dual_ex` | written by hand | none; log replay |
| Join disambiguation | exit predicates, dynamic | disjoint right-hand patterns, static | `(pre, post)` pairs, dynamic, can be disabled | `tw_bf` bits or payload | not needed |
| Aliasing | rejected; array indices compared at run time | none (values, linear variables) | shared read/write rejected at definition | author's problem | irrelevant (addresses logged) |
| Heap | stacks with zero-on-pop | recursive types | allocate/deallocate with value assertion | author's problem | allocation undone, deallocation deferred to commit |
| Floating point | integers only | not addressed | treated as reversible; tolerance checks | author's problem; byte compare in check mode | old value restored exactly |
| Irreversible effects | none in the core | `create`/`erase` arrows (paper); FFI listed as missing | `@safe` escape, unchecked | `tw_output` deferred to GVT; `commit` handler | streams not handled; `delete` deferred |
| Evidence that undo is right | run-time assertions | type and coverage rules; Lean proofs in `chessai/theseus` | run-time checks; `check_inv` test helper | `--synch=6` forward/reverse/compare | none in tree beyond tests |
| Extra state per step | 0 | 0 | 0 for reversible code; ancillas otherwise | bits per branch | one entry per write |

Basis: derived from sections 2-7.

### 9. Obligations at a reversible/irreversible boundary

The examined systems jointly identify what a caller must know about a callee before it may be executed inside an undoable region. Each line names where the obligation is visible.

1. **Footprint closure**: every state-changing instruction reachable from the region is either invertible or logged. Backstroke states this as a user obligation and does not check it; NiLang's `@safe` and Janus-external code have no counterpart check either.
2. **Non-aliasing of update targets and operands**: Jana (dynamic), NiLang (definition time), Theseus (by construction).
3. **Join information**: one predicate, flag bit, or disjoint pattern per control-flow merge; violated predicates must fail loudly (section 2 shows the silent alternative).
4. **Exactness of arithmetic inverses**: holds for modular integers, fixed-point, and XOR; does not hold for binary floating point (section 5). Logging the old value sidesteps the issue.
5. **Generator state is state**: random draws must be stepped back (ROSS) or logged; forgetting this is the specific failure ROSS's checker reports as "Random number generation `rng` did not rollback properly!".
6. **Deferred release**: frees and externally visible output are postponed to the commit horizon (Backstroke deferred `delete`; ROSS `tw_output`), and a fallback that emits early must be visible (ROSS warns).
7. **Undo granularity matches the runtime's**: ROSS rolls back whole kernel processes and always most-recent-first; Backstroke's `reverseEvent` undoes the newest record and `commitEvent` commits the oldest, so events must be reversed in exact LIFO order and committed in FIFO order per store.

Basis: derived.

## Boundaries

- **Not examined**: the full text of the Janus papers, Bennett (1973, 1989 body), Jefferson (1985 body), Carothers et al. (1999 body), and the Backstroke papers beyond their abstracts; the 2016 kinetic Monte-Carlo paper (DOI `10.1145/2901378.2901394`, metadata only); the earlier Backstroke generation built on path-oriented inversion; ROSE itself; ROSS's GVT algorithm (`core/gvt/mpi_allreduce.c`), network layer, and optimistic-debug/realtime schedulers; NiLang's AD implementation (`src/autodiff/`), GPU kernels, and logarithmic-number types; reversible functional languages (RFUN, CoreFun); quantum uncomputation; reversible hardware and thermodynamic (Landauer) arguments; causally consistent reversibility for concurrent calculi and reversible debuggers; record-and-replay debuggers.
- **Not executed**: Jana, NiLang, ROSS, Backstroke, and `chessai/theseus` were not built or run. Every statement about them is from source or documentation at the pinned revisions. The probe is an independent model.
- **Unknown**: whether Jana's dynamic index-alias rule matches the published Janus semantics or is an implementation relaxation; whether NiLang's tolerance-based float policy can change a gradient materially in long-running codes other than the paper's leapfrog benchmark; measured overhead of Backstroke relative to hand-written reverse handlers (the abstracts say "significant" without a figure readable from the examined material); whether ROSS's default byte comparison produces padding-related false alarms in practice.
- **Known not to apply**: Backstroke 2.x at the pinned revision does not perform program inversion or emit per-function reverse code; ROSS's rollback check does not validate multi-event rollbacks, cancellation cascades, or parallel runs; Theseus's static guarantee is reversibility, not termination; Bennett's bounds are for input-saving machines.
- **Unsupported by the subjects**: Backstroke: bitfields, undoing stream input, deferring stream output, uninstrumented callees that modify state. Jana: heap structures other than integer stacks and fixed-size arrays (no other allocation form appears in the evaluator). NiLang: exact reversibility of binary floating-point arithmetic. Theseus (2014 report): foreign calls and error exits are listed as future work.
- **Stronger conclusions the evidence does not establish**: that reverse computation is faster than state saving in general (one abstract reports up to six-fold on sample models); that instrumented C++ is reversible for any program (it is conditional on footprint closure); that the probe's event counts or percentages transfer to any real model; that the Lean development in `chessai/theseus` proves what its README says (the proofs were not checked).

## Evidence

All repository observations were made on 2026-11-19 from source archives of the pinned revisions; papers were read the same day.

**Repositories (path: what was read)**

- `mbudde/jana` @ `5b51b57e0b6f13ec1e1c61d719a18bf58696f84b`: `src/Jana/Eval.hs` (`assignLval`, `evalStmt`, `evalLval`, `numberToModular`, `findAlias`, `checkAlias`, `checkLvalAlias`), `src/Jana/Invert.hs` (whole file), `src/Jana/Aliases.hs` (whole file), `src/Jana/ErrorMessages.hs`, `src/Main.hs` (`-m` option text), `tests/errors/{alias-1,alias-2,var-modified-on-rhs,var-modified-on-lhs,assertion-fail-if-fwd,assertion-fail-from-fwd,delocal-wrong-value,pop-to-non-zero,modular-integer}.ja`, `examples/{fib,sqrt}.ja`, `jana.cabal`.
- `GiggleLiu/NiLangCore.jl` @ `3464affc5215890847a7d59dc653aabab6664758`: `src/dualcode.jl` (`dual_ex`, `dual_if`, `dual_body`), `src/compiler.jl` (`compile_if`, `analyse_if`, `whilestatement`, `forstatement`), `src/checks.jl` (`check_inv`, `almost_same`), `src/variable_analysis.jl` (shared read/write error), `Project.toml`.
- `GiggleLiu/NiLang.jl` @ `4b003966d3441f9b1ff98aafff50bdeebcdc83ac`: `src/stdlib/bennett.jl`, `docs/src/{tutorial,grammar,faq}.md`, `README.md`, `Project.toml`.
- `ROSS-org/ROSS` @ `dc3a6a056cfc7a5e68f7141f88d8833407599ef8`: `core/ross-types.h` (`enum tw_synch_e`, handler typedefs, `struct tw_lptype`, `struct tw_bf`, `tw_out`, `struct tw_event`), `core/tw-kp.c` (`tw_kp_rollback_to`), `core/tw-event.c` (`event_cancel`, `tw_event_rollback`), `core/rand-clcg4.c` (`rng_gen_reverse_val`), `core/ross-random-internal.h`, `core/tw-eventq.h` (commit loop), `core/tw-util.c` (`tw_output`), `core/tw-state.c`, `core/tw-setup.c` (`--synch` option), `core/tw-sched.c` (`tw_scheduler_sequential_rollback_check`), `core/check-revent/crv-state.{h,c}`, `.version`.
- `LLNL/backstroke` @ `c3d8848b5e12785e30ec87dc19d645df5c63bf89`: `README.md`, `docs/user-manual.tex`, `ChangeLog`, `src/rtss/backstroke/rtss.h` (`RunTimeStateStore`, `EventRecord`, `is_stack_ptr`, `beginForwardEvent`, `endForwardEvent`, `reverseEvent`, `commitEvent`, `commitEventsLessThanSimTime`, `restore`, `dispose`, `avpushT`, ROSS-specific `xpdes` functions), `src/rtss/backstroke/rtss-macros.h`, `src/rtss/rtss.C` (`init_stack_info`), `src/TransformationSequence.C`, `src/ClassInfo.C`, `src/CommandLineOptions.C`, `src/backstroke.C`.
- `chessai/theseus` @ `4c0ec5c3d0738313ee44f603baed68b8a61d2da8`: `papers/theseus.pdf`, `papers/information-effects.pdf` (text extracted with `pdftotext -layout`), `README.md`, `crates/theseus-check/src/diagnostics.rs`, `theseus-proofs/TheseusProofs/Reversibility.lean` (declaration names), `theseus-proofs/lean-toolchain`, `conformance/programs/0003-not.thse`, `0024-adder.thse`.

**Papers (identifier: what was read)**

- James and Sabry, *Information Effects*, POPL 2012, DOI `10.1145/2103656.2103667`: abstract, introduction, the table of Pi isomorphisms, and the passage introducing `create_b` and `erase`. James and Sabry, *Theseus: A High Level Language for Reversible Computing*, 2014: sections 1-3 and 5 and the concluding discussion (no DOI found; identified by the pinned PDF path above).
- Liu and Zhao, arXiv:2003.04617v3 (submitted 2020-03-10, revised 2021-01-31): abstract page; sections 2-3 and the opening of Appendix F of the full text.
- Bennett, DOI `10.1137/0218053`; Jefferson, DOI `10.1145/3916.3988`; Carothers, Perumalla, Fujimoto, DOI `10.1145/347823.347828`; Schordan et al., DOI `10.1007/978-3-319-20860-2_6` and DOI `10.1007/s00354-018-0038-2`: abstracts, with author/venue/page metadata confirmed against Crossref.
- Metadata only (Crossref), cited for identification and not for content: Yokoyama and Glück, DOI `10.1145/1244381.1244404`; Yokoyama, Axelsen, Glück, DOI `10.1145/1366230.1366239`; Yokoyama, DOI `10.1016/j.entcs.2010.02.007`; Bennett 1973, DOI `10.1147/rd.176.0525`; Landauer 1961, DOI `10.1147/rd.53.0183`; Schordan et al. 2016, DOI `10.1145/2901378.2901394`.

**Probe (execution).** Environment: CPython 3.13.15, Linux x86_64, standard library only. Save the following as `/tmp/revprobe/probe_reversible.py` and run `python3 /tmp/revprobe/probe_reversible.py` (about one second). Section A models Janus statements, B the Bennett recursion, C float invertibility, D a Time Warp executive with two rollback mechanisms. The models are this report's own and are not derived from any subject's code.

```python
#!/usr/bin/env python3
"""Reversible-computation micro-probes (Python 3.10+, standard library only)."""
import heapq, itertools, random, struct

# --- A. Janus-style statements: executor with entry/exit assertions + static inverter ---
W = 1 << 32
def ev(e, s): return e(s) if callable(e) else s[e] if isinstance(e, str) else e
def run(p, s, check=True):
    op = p[0]
    if op == 'seq':
        for q in p[1]: run(q, s, check)
    elif op in ('+=', '-=', '^='):
        v = ev(p[2], s)
        s[p[1]] = (s[p[1]] + v) % W if op == '+=' else (s[p[1]] - v) % W if op == '-=' else s[p[1]] ^ v
    elif op == 'swap': s[p[1]], s[p[2]] = s[p[2]], s[p[1]]
    elif op == 'if':                       # if e1 then s1 else s2 fi e2
        took = bool(ev(p[1], s)); run(p[2] if took else p[3], s, check)
        if check and bool(ev(p[4], s)) != took: raise AssertionError('fi assertion')
    elif op == 'loop':                     # from e1 do s1 loop s2 until e2
        if check and not ev(p[1], s): raise AssertionError('from assertion (entry)')
        while True:
            run(p[2], s, check)
            if ev(p[4], s): break
            run(p[3], s, check)
            if check and ev(p[1], s): raise AssertionError('from assertion (re-entry)')
def inv(p):
    op = p[0]
    if op == 'seq': return ('seq', [inv(q) for q in reversed(p[1])])
    if op in ('+=', '-='): return ('-=' if op == '+=' else '+=', p[1], p[2])
    if op in ('^=', 'swap'): return p
    if op == 'if': return ('if', p[4], inv(p[2]), inv(p[3]), p[1])
    if op == 'loop': return ('loop', p[4], inv(p[2]), inv(p[3]), p[1])
skip = ('seq', [])
fib = ('seq', [('+=', 'x1', 1), ('+=', 'x2', 1),
       ('loop', lambda s: s['x1'] == s['x2'],
        ('seq', [('+=', 'x1', 'x2'), ('swap', 'x1', 'x2'), ('-=', 'n', 1)]), skip,
        lambda s: s['n'] == 0)])
s = {'x1': 0, 'x2': 0, 'n': 10}; run(fib, s); print('A1 fib forward :', s)
run(inv(fib), s); print('A1 fib inverse :', s)
bad = ('if', lambda s: s['x'] > 0, ('-=', 'x', 5), ('+=', 'x', 1), lambda s: s['x'] < W // 2 and s['x'] > 0)
for x0 in (7, 3):
    s = {'x': x0}
    try: run(bad, s); r = 'ok'
    except AssertionError as e: r = 'REJECTED: %s' % e
    t = dict(s); run(inv(bad), t, check=False)
    print('A2 x0=%d forward=%s post=%d unchecked-inverse=%d' % (x0, r, s['x'], t['x']))
for i, j in ((0, 1), (0, 0)):              # aliasing: a[i] op= a[j] on two 2-bit cells
    for name, f in (('^=', lambda a, b: a ^ b), ('+=', lambda a, b: (a + b) % 4)):
        img = set()
        for a in itertools.product(range(4), repeat=2):
            a = list(a); a[i] = f(a[i], a[j]); img.add(tuple(a))
        print('A3 a[%d] %s a[%d]: %2d distinct post-states of 16' % (i, name, j, len(img)))

# --- B. Bennett k-ary checkpoint recursion: step count and peak number of live states ---
def bennett(k, n):
    live, peak, calls = {0}, [1], [0]
    def seg(base, ln, sign, unc):          # sign=+1 compute segment, -1 uncompute it
        if ln == 1:
            calls[0] += 1
            (live.add if sign > 0 else live.discard)(base + 1); peak[0] = max(peak[0], len(live))
            return
        sub = ln // k
        fw = [(base + sub * j, sub, +1, True) for j in range(k)]
        bw = [(base + sub * j, sub, -1, True) for j in reversed(range(k - 1))] if unc else []
        for b, l, sg, u in (fw + bw if sign > 0 else [(b, l, -sg, u) for b, l, sg, u in reversed(fw + bw)]):
            seg(b, l, sg, u)
    seg(0, k ** n, +1, True)
    return calls[0], peak[0], sorted(live)
for k, n in ((2, 1), (2, 4), (2, 10), (3, 5), (4, 5), (8, 4)):
    c, p, live = bennett(k, n); T = k ** n
    assert c == (2 * k - 1) ** n and p == n * (k - 1) + 2 and live == [0, T]
    print('B k=%d T=%-5d steps=%-7d =(2k-1)^n  peak_states=%-3d =n(k-1)+2  naive: steps=%d states=%d'
          % (k, T, c, p, 2 * T - 1, T + 1))

# --- C. IEEE-754 binary64 "+=" then "-=" is not the identity; modular integers are ---
rnd = random.Random(20261119); bad_f = bad_i = 0; N = 200000
for _ in range(N):
    x = rnd.uniform(-1, 1) * 10.0 ** rnd.randint(-8, 8); y = rnd.uniform(-1, 1) * 10.0 ** rnd.randint(-8, 8)
    bad_f += ((x + y) - y) != x
    a, b = rnd.getrandbits(64), rnd.getrandbits(64); bad_i += (((a + b) % 2**64) - b) % 2**64 != a
print('C float (x+y)-y != x: %d of %d (%.1f%%); u64 wraparound failures: %d' % (bad_f, N, 100 * bad_f / N, bad_i))
x = 0.1; xs = x
for i in range(1, 1001): x += 1.0 / i
for i in range(1000, 0, -1): x -= 1.0 / i
print('C 1000 float += then reversed -=: start=%r end=%r bits-equal=%s' % (xs, x, struct.pack('d', x) == struct.pack('d', xs)))

# --- D. Time Warp: optimistic run == sequential run, rollback by reverse handlers or by an undo log ---
M = (1 << 61) - 1; A = 0x5DEECE66D; AINV = pow(A, -1, M); INV31 = pow(31, -1, 2**64); L = 4; TEND = 300
def plain_put(st, k, v): st[k] = v
def handler(st, ts, put):                  # forward event handler; returns [(recv_ts, dest_lp)]
    s = st['s'] * A % M                    # RNG step: a bijection on 1..M-1, so it can be stepped back
    put(st, 's', s); put(st, 'acc', (st['acc'] * 31 + (s ^ ts)) % 2**64); put(st, 'n', st['n'] + 1)
    return [(ts + 1 + (s >> 9) % 9, (s >> 3) % L)]
def reverse(st, ts, fix_rng=True):         # hand-written reverse handler (reverse computation)
    s = st['s']; st['n'] -= 1; st['acc'] = (st['acc'] - (s ^ ts)) * INV31 % 2**64
    if fix_rng: st['s'] = s * AINV % M
def child(e, k, t2, d2): return (t2, (e[1] * 1000003 + k + 1) % M, d2)
def fresh(): return [dict(s=i + 1, acc=0, n=0) for i in range(L)]
INIT = [(1 + i, 7 * i + 1, i % L) for i in range(8)]
def sequential():
    lps, pq = fresh(), list(INIT); heapq.heapify(pq)
    while pq and pq[0][0] <= TEND:
        e = heapq.heappop(pq)
        for k, (t2, d2) in enumerate(handler(lps[e[2]], e[0], plain_put)): heapq.heappush(pq, child(e, k, t2, d2))
    return lps
def optimistic(mode, seed, fix_rng=True):
    rnd, lps = random.Random(seed), fresh()
    pend, done = [[] for _ in range(L)], [[] for _ in range(L)]   # per LP: pending heap, processed stack
    st = dict(stragglers=0, undone=0, anti=0, committed=0, writes_logged=0, peak_log=0)
    def undo_to(d, key, inclusive):
        while done[d] and (done[d][-1][0] >= key if inclusive else done[d][-1][0] > key):
            e, sent, log = done[d].pop(); st['undone'] += 1
            if mode == 'iss':
                for s_, k, old in reversed(log): s_[k] = old
            else: reverse(lps[d], e[0], fix_rng)
            for m in reversed(sent): cancel(m)
            heapq.heappush(pend[d], e)
    def cancel(m):                         # anti-message: annihilate m, rolling the receiver back first if needed
        st['anti'] += 1; d = m[2]
        if m not in pend[d]: undo_to(d, m, True)
        pend[d].remove(m); heapq.heapify(pend[d])
    for e in INIT: heapq.heappush(pend[e[2]], e)
    while True:
        ready = [d for d in range(L) if pend[d] and pend[d][0][0] <= TEND]
        if not ready: break
        d = rnd.choice(ready); e = heapq.heappop(pend[d]); log = []
        put = (lambda s_, k, v: (log.append((s_, k, s_[k])), plain_put(s_, k, v))) if mode == 'iss' else plain_put
        sent = [child(e, k, t2, d2) for k, (t2, d2) in enumerate(handler(lps[d], e[0], put))]
        done[d].append((e, sent, log)); st['writes_logged'] += len(log)
        for m in sent:
            if done[m[2]] and m < done[m[2]][-1][0]: st['stragglers'] += 1; undo_to(m[2], m, False)
            heapq.heappush(pend[m[2]], m)
        st['peak_log'] = max(st['peak_log'], sum(len(x[2]) for q in done for x in q))
        gvt = min(p[0] for p in pend if p)                    # nothing in transit here, so min pending key = GVT
        for q in done:
            while q and q[0][0] < gvt: q.pop(0); st['committed'] += 1   # commit: drop undo data below GVT
    return lps, st
ref = sequential(); print('D sequential final:', [(x['n'], x['acc'] % 10**6) for x in ref])
for mode in ('rc', 'iss'):
    for seed in (1, 2, 3):
        lps, st = optimistic(mode, seed); print('D optimistic %-3s seed=%d equal_to_sequential=%s %s' % (mode, seed, lps == ref, st))
lps, st = optimistic('rc', 1, fix_rng=False)
print('D reverse handler that forgets the RNG: equal_to_sequential=%s (undone=%d)' % (lps == ref, st['undone']))
lp = fresh()[0]; before = dict(lp); handler(lp, 5, plain_put); reverse(lp, 5, fix_rng=False)
print('D forward;reverse;compare check on that handler: state restored=%s differing fields=%s'
      % (lp == before, [k for k in lp if lp[k] != before[k]]))
```

Output observed:

```text
A1 fib forward : {'x1': 89, 'x2': 144, 'n': 0}
A1 fib inverse : {'x1': 0, 'x2': 0, 'n': 10}
A2 x0=7 forward=ok post=2 unchecked-inverse=7
A2 x0=3 forward=REJECTED: fi assertion post=4294967294 unchecked-inverse=4294967293
A3 a[0] ^= a[1]: 16 distinct post-states of 16
A3 a[0] += a[1]: 16 distinct post-states of 16
A3 a[0] ^= a[0]:  4 distinct post-states of 16
A3 a[0] += a[0]:  8 distinct post-states of 16
B k=2 T=2     steps=3       =(2k-1)^n  peak_states=3   =n(k-1)+2  naive: steps=3 states=3
B k=2 T=16    steps=81      =(2k-1)^n  peak_states=6   =n(k-1)+2  naive: steps=31 states=17
B k=2 T=1024  steps=59049   =(2k-1)^n  peak_states=12  =n(k-1)+2  naive: steps=2047 states=1025
B k=3 T=243   steps=3125    =(2k-1)^n  peak_states=12  =n(k-1)+2  naive: steps=485 states=244
B k=4 T=1024  steps=16807   =(2k-1)^n  peak_states=17  =n(k-1)+2  naive: steps=2047 states=1025
B k=8 T=4096  steps=50625   =(2k-1)^n  peak_states=30  =n(k-1)+2  naive: steps=8191 states=4097
C float (x+y)-y != x: 96267 of 200000 (48.1%); u64 wraparound failures: 0
C 1000 float += then reversed -=: start=0.1 end=0.10000000000000075 bits-equal=False
D sequential final: [(121, 387854), (128, 354765), (110, 833706), (125, 27269)]
D optimistic rc  seed=1 equal_to_sequential=True {'stragglers': 62, 'undone': 118, 'anti': 118, 'committed': 484, 'writes_logged': 0, 'peak_log': 0}
D optimistic rc  seed=2 equal_to_sequential=True {'stragglers': 65, 'undone': 122, 'anti': 122, 'committed': 484, 'writes_logged': 0, 'peak_log': 0}
D optimistic rc  seed=3 equal_to_sequential=True {'stragglers': 64, 'undone': 124, 'anti': 124, 'committed': 484, 'writes_logged': 0, 'peak_log': 0}
D optimistic iss seed=1 equal_to_sequential=True {'stragglers': 62, 'undone': 118, 'anti': 118, 'committed': 484, 'writes_logged': 1806, 'peak_log': 45}
D optimistic iss seed=2 equal_to_sequential=True {'stragglers': 65, 'undone': 122, 'anti': 122, 'committed': 484, 'writes_logged': 1818, 'peak_log': 51}
D optimistic iss seed=3 equal_to_sequential=True {'stragglers': 64, 'undone': 124, 'anti': 124, 'committed': 484, 'writes_logged': 1824, 'peak_log': 48}
D reverse handler that forgets the RNG: equal_to_sequential=False (undone=122)
D forward;reverse;compare check on that handler: state restored=False differing fields=['s']
```

## Revalidation

- **Mechanism claims**: rerun the probe; the output is deterministic (fixed seeds) and should match byte-for-byte on CPython 3.10 or later with IEEE-754 doubles. The assertions in section B fail if the closed forms `(2k-1)^n` and `n(k-1)+2` are wrong.
- **Jana alias and assertion semantics**: diff `src/Jana/Eval.hs` between the pinned revision and the revision of interest, looking at `checkLvalAlias` (the clause comparing two evaluated indices is what makes `a[i] += a[j]` legal for `i != j`) and at `evalStmt` for `If`, `From`, `Local`, `Pop`. If a build is available, run the files under `tests/errors/`; each is expected to fail with the message its name suggests.
- **NiLang**: check that `dual_ex` in `NiLangCore/src/dualcode.jl` still pairs the same statements and that `almost_same` for floats still has the `abs(b - a) < atol` disjunct. With Julia available, `NiLang.check_inv(f, args)` on a float loop with `NiLangCore.GLOBAL_ATOL[] = 0` versus the default shows whether tolerance is still what makes the check pass; `bennett(step, y, x; k, N, logger)` prints call counts and peak memory to compare with section 4.
- **ROSS**: `grep -n SEQUENTIAL_ROLLBACK_CHECK core/*.c core/*.h` confirms the checker mode still exists and its `--synch` number; read `tw_event_rollback` for the order (free output, reverse handler, free delta, cancel caused events). With a build, run any model with `--synch=6` after deleting one `tw_rand_reverse_unif` call from its reverse handler; the expected diagnostic is the "`rng` did not rollback properly" message.
- **Backstroke**: `grep -n "avpushT\|registerAllocationT\|registerDeallocationT" src/TransformationSequence.C` shows whether generation is still instrumentation-only; if a reverse-function tag other than the inert `BITYPE_REVERSE_FUNCTION_CALL_NO_ARGS` becomes active in `restore` (`src/rtss/backstroke/rtss.h`), the "no generated reverse code" finding no longer holds. Check `docs/user-manual.tex` section "Limitations" for bitfield support.
- **Paper-level statements** (Pi table, Theseus rules, Bennett bound) do not change; re-read only if a different edition is substituted.
