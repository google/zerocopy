# Rust correctness and termination terminology at nightly-2026-05-31

## Summary

At the Rust revision behind nightly-2026-05-31, several outcomes that all fail to produce an ordinary function result must remain distinct: an execution can panic and unwind, panic and abort, terminate through another process-ending path, execute undefined behavior, or continue forever. Rust's own term *diverging* is broader than *nonterminating*: the Reference defines a diverging expression as one that never completes normal execution, and it explicitly includes `panic!` as well as infinite `loop {}`. A Rust function returning `!` therefore promises only that it never returns normally.

The verification terms *partial correctness* and *total correctness* are not Rust language terms. This report uses them as report-local analytical definitions over Rust outcomes. A **normal-return partial-correctness** claim says: for every execution that reaches an ordinary normal return, the returned state/value satisfies the postcondition. By itself, that claim says nothing about whether executions terminate, panic, abort, or continue forever. For Rust-level reasoning it also does not discharge undefined-behavior obligations; UB-freedom must be established separately because Rust does not assign an ordinary reliable execution semantics to UB.

A **normal-return total-correctness** claim strengthens that statement by requiring every in-scope execution to reach a normal return in finite time and satisfy the postcondition. This excludes nontermination and also excludes panic/unwind and process termination for the in-scope executions. If a project instead wants to count panic, abort, or another finite exceptional outcome as an acceptable form of termination, that is a different explicitly outcome-indexed property; calling it simply "total correctness" would hide a material semantic choice.

Panic-freedom, unwind-freedom, termination, and normal termination are likewise distinct. `panic=abort` can make Rust-frame unwinding impossible while panics still terminate the process. A computation can be panic-free but nonterminating. A computation can terminate by aborting without ever returning normally. An unwinding panic can run destructors before either recovery or eventual termination. A verifier should therefore state which outcomes its theorem permits rather than using one undifferentiated word such as "failure" or "termination."

No fresh Rust execution was performed. The report applies conventional verification terminology to the exact pinned Rust Reference rules. The companion corpus report `rust-panic-unwind-abort-divergence-nightly-2026-05-31` supplies the detailed MIR and Charon representations; this report does not duplicate those implementation findings.

## Applicability

This report applies to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`;
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

The Rust Reference is authoritative here for Rust's language-level terms and outcome distinctions. The terms *partial correctness* and *total correctness* below are **derived analytical vocabulary**, not terms defined normatively by the Rust Reference.

The report uses **normal return** for an execution that completes the called Rust function through its ordinary return path and yields the function's return value. This is intentionally narrower than “the process eventually stops.”

The report uses **finite termination** for an execution that ends after finitely many steps, whether by normal return or by an explicitly named terminating exceptional outcome. Because Rust admits several semantically different non-returning outcomes, any property that uses this broader notion must say which outcomes count.

The report does not define an Anneal result taxonomy. It records distinctions any such taxonomy would need to preserve if its claims mention termination, panic, or correctness.

## Findings

### Rust divergence means absence of normal completion, not semantic nontermination

The pinned Reference defines a diverging expression as an expression that “never completes normal execution.” It separately identifies both an infinite `loop` without an associated `break` and panic-generating expressions such as `panic!` as diverging.

Therefore:

- an infinite loop may diverge by continuing execution forever;
- `panic!` diverges even when it unwinds and is later caught;
- `panic!` also diverges when the panic strategy aborts the process;
- a `return`, `break`, or `continue` expression is itself diverging with respect to the surrounding expression even though control may continue elsewhere.

“Diverging” is therefore a control-flow/type-system category about the absence of a normal value at that expression. It is not a synonym for “runs forever.”

Basis: Rust Reference **normative** rules for divergence and the never type.

### `!` states that normal return is impossible, not why

The pinned Reference says the never type has no values and that a function return type of `!` identifies a function that never returns normally.

That statement is compatible with several behaviors:

- an infinite loop;
- a panic that unwinds;
- a panic that aborts;
- another supported non-returning operation.

A proof that a call has type `!` establishes no ordinary return value exists. It does not establish nontermination, panic-freedom, process termination, or UB-freedom.

Basis: Rust Reference **normative** never-type and divergence rules.

### Panic and unwind are not synonyms

A panic is a Rust error-control event that prevents the current computation from returning normally. The panic handler determines what happens next.

At the pinned Reference:

- the `unwind` handler unwinds Rust frames and is potentially recoverable;
- the `abort` handler terminates the process and is non-recoverable;
- the unwind handler does not guarantee that every possible panic is recoverable;
- `catch_unwind` applies only to unwinding panics.

Thus a claim that “the function cannot unwind” is weaker than a claim that “the function cannot panic.” Under an abort strategy, a panic can occur without any Rust stack unwind.

Basis: Rust Reference **normative** panic rules.

### Unwinding is an observable execution mode, not merely a different exit code

When a panic unwinds through Rust frames, the Reference requires live objects in those frames to be cleaned up through `Drop`. Those destructors are Rust code and can have program-visible effects.

Consequently, collapsing unwind into a generic “failure” can erase behavior relevant to a proof. Even if no ordinary return value is produced, unwind cleanup may mutate state, release resources, call user code, or itself panic.

A correctness claim that abstracts over exceptional outcomes must say whether unwind cleanup is inside the modeled behavior, outside the claimed domain, or explicitly trusted.

Basis: Rust Reference **normative** unwind-cleanup rules + **derived** verification consequence.

### Abort is finite termination but not normal termination

The standard abort panic handler terminates the process rather than returning from the current Rust function. It also does not perform ordinary Rust stack unwinding.

For terminology in this report:

- abort **is** a finite terminating outcome;
- abort **is not** a normal return;
- therefore “this execution terminates” does not imply “this function returns”;
- therefore “termination” is too weak a success condition for an API theorem unless the acceptable terminal outcomes are named.

This distinction is especially important when a postcondition is about a return value or final caller-visible state: an aborting execution has no such normal return state.

Basis: Rust Reference **normative** panic behavior + **derived** terminology.

### Nontermination is narrower than Rust divergence

This report uses **nontermination** for an execution that continues indefinitely rather than reaching a finite terminal outcome.

Under that definition:

- `loop {}` can be nonterminating;
- an aborting panic is terminating, though not normally;
- an unwinding panic that is caught may later continue and terminate normally;
- an uncaught unwinding panic may ultimately terminate the thread or process;
- all of those panic expressions are still *diverging expressions* at the source expression itself.

Thus the implication runs only one way for the common cases examined here: semantic nontermination implies the relevant computation does not normally complete, but a diverging Rust expression need not be semantically nonterminating.

Basis: Rust Reference **normative** divergence/panic rules + report-local **derived** definition of nontermination.

### Normal-return partial correctness is conditional on normal return

For this report, a normal-return partial-correctness claim for precondition `P` and postcondition `Q` means:

> For every in-scope execution starting from a state satisfying `P`, if the function returns normally, the returned state/value satisfies `Q`.

This property does **not** by itself require that any execution returns. A function that loops forever on every input can satisfy such a postcondition vacuously if the semantic model asks only about states reached on normal return.

It also does not by itself forbid panic or abort. Those executions simply do not reach the condition's normal-return premise.

This is a report-local **derived** verification definition. Rust itself does not define the term “partial correctness.”

### Rust UB-freedom is an independent prerequisite for useful Rust-level correctness claims

The Reference says Rust programs must not exhibit undefined behavior and warns that UB affects the entire program. It also notes that Rust does not yet have a complete formal model of all unsafe-code semantics.

Accordingly, a theorem of the shape “if this execution returns normally, `Q` holds” is not sufficient to establish an Anneal-style Rust correctness promise if another in-scope execution can exhibit UB. Compiler reasoning may exploit the assumption that UB never occurs, so it is not generally sound to treat UB as merely another ordinary exceptional result alongside panic or abort.

For Rust-level verification, partial/total correctness and UB-freedom answer different questions. A useful combined claim must establish both the desired outcome property and the required well-definedness property.

Basis: Rust Reference **normative** UB requirements + **derived** verification consequence.

### Normal-return total correctness adds finite normal termination

For this report, a normal-return total-correctness claim for `P` and `Q` means:

> Every in-scope execution starting from a state satisfying `P` reaches a normal return in finite time, and its returned state/value satisfies `Q`.

Relative to the normal-return partial-correctness definition above, this adds a progress/termination obligation.

It therefore rules out, for the executions in scope:

- infinite execution;
- panic that unwinds instead of returning normally;
- panic that aborts;
- any other finite process/thread termination that prevents the function's normal return.

UB-freedom remains an independent Rust-level requirement rather than an acceptable alternative terminating outcome.

This is a report-local **derived** definition, not Rust normative terminology.

### “Total correctness” without an outcome convention is ambiguous for Rust

Some verification contexts use “termination” broadly enough to mean only that execution does not run forever. Under such a convention, an aborting program terminates. That convention is insufficient when the theorem is intended to establish that a Rust function actually produces its specified result.

For Rust work, a report should therefore avoid an unqualified statement such as “the function is totally correct” when the treatment of panic/abort is material. Prefer an explicit statement, for example:

- “all in-scope executions return normally and satisfy `Q`”;
- “all in-scope executions either return normally with `Q` or panic by unwinding”;
- “the function is panic-free but termination is not established”;
- “the proof is partial correctness only; divergence remains possible.”

The extra words encode a real semantic distinction, not stylistic caution.

Basis: **derived** from the pinned Rust outcome taxonomy.

### Panic-freedom and termination are independent properties

A panic-free function can still fail to terminate:

```rust
fn spin() -> ! {
    loop {}
}
```

Conversely, a function may terminate in finite time because it panics under an abort strategy. It is terminating in the broad finite-outcome sense but not panic-free and not normally returning.

Therefore neither of these implications is valid in general:

- panic-free ⇒ terminating;
- terminating ⇒ panic-free.

A proof system that cares about both must track both obligations or prove a stronger property that entails them.

Basis: Rust Reference **normative** examples/rules + **derived** consequence.

### Unwind-freedom and panic-freedom are also independent

Under `panic=abort`, ordinary Rust panic does not unwind through Rust frames, yet the panic still occurs and terminates the process. A theorem that excludes unwind edges can therefore coexist with reachable panic behavior.

Conversely, a system may model a foreign unwind or another unwind-capable boundary separately from Rust panic. The Reference makes ABI unwind permission an independent safety condition.

For Rust verification terminology, “no unwind” should therefore not be used as shorthand for “no panic” or “normal return.”

Basis: Rust Reference **normative** panic and FFI-unwind rules + **derived** consequence.

### Panic-freedom does not imply UB-freedom, and UB-freedom does not imply panic-freedom

A program can be panic-free yet perform a dangling-pointer dereference or another form of UB. A program can be entirely well-defined and still intentionally call `panic!`.

These are separate dimensions:

- **UB-freedom** asks whether all behavior remains within Rust's defined semantic envelope;
- **panic-freedom** asks whether the panic control path is unreachable;
- **normal termination** asks whether execution reaches a normal return;
- **postcondition correctness** asks what is true at that return.

A sound verifier may combine these dimensions into stronger results, but it should not erase the underlying distinctions.

Basis: Rust Reference **normative** UB and panic rules + **derived** decomposition.

### Recovery after unwind is still not the same as the panicking function returning normally

With an unwinding panic, a caller may recover through `catch_unwind` or a thread boundary. The panicking function itself still did not return its declared ordinary value.

This gives two scopes that reports should distinguish:

- **callee normal return**: did the function invocation itself produce its normal result?
- **larger computation recovery**: did some enclosing computation catch the unwind and later continue normally?

A theorem about one is not automatically a theorem about the other.

Basis: Rust Reference **normative** unwind-recovery rules + **derived** scope distinction.

### Outcome-indexed specifications avoid overloaded correctness words

The Rust outcome taxonomy can be expressed without choosing one global definition of “correctness.” A specification can state explicitly which outcome classes are permitted and what condition applies to each.

For example, a verifier could prove a property equivalent in prose to:

- normal return is guaranteed and satisfies `Q`;
- or normal return satisfies `Q`, while nontermination remains allowed;
- or normal return satisfies `Q`, panic-by-unwind is permitted and separately constrained, and abort is forbidden.

Those examples are not Anneal design recommendations. They demonstrate that the underlying Rust facts support multiple legitimate proof contracts. The report's terminology is intended to keep those contracts distinguishable.

Basis: **derived**.

## Boundaries

- The Rust Reference does not normatively define the verification terms *partial correctness* or *total correctness*. Their definitions in this report are explicit analytical conventions.
- This report does not prescribe Anneal's eventual result taxonomy, proof encoding, or user-facing terms.
- No fresh Rust, MIR, Charon, Aeneas, Lean, panic, unwind, or nontermination experiment was performed.
- “Nontermination” here means infinite execution in the semantic sense. A syntactic loop or MIR CFG cycle is not by itself proof of nontermination.
- The report does not model fairness, scheduler progress, cancellation, signals, `exit`, `_exit`, `longjmp`, asynchronous exceptions, resource exhaustion, or OS process-kill behavior.
- Thread-level and process-level termination are not exhaustively classified. When that distinction matters, a later report should name the concrete boundary.
- Panic payloads, hooks, double-panics, foreign exceptions, and all recovery corner cases are outside the report except where needed to distinguish unwind from abort.
- The report does not assert that an aborting panic is observationally equivalent to any other process-abort mechanism.
- Undefined behavior is deliberately not classified as an ordinary terminating outcome. Rust-level proofs require a separate adequacy argument for UB-freedom.
- The companion panic/MIR report contains implementation-level rustc and Charon details. This terminology report does not duplicate or supersede those findings.

## Evidence

**Normative Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`:

- `src/divergence.md`, blob `5e25d6d0d944ae8a62236ce7e46f347ded3fbfcc`: a diverging expression never completes normal execution; `panic!` and infinite loops can both diverge.
- `src/types/never.md`, blob `fe30bce74d6ab02eb06b9d6a852f9dc3e523eec2`: `!` has no values and a function returning `!` never returns normally.
- `src/panic.md`, blob `2be7e42fb2c3d4c752202f87aa07c890d68e437b`: panic handlers, unwind versus abort, unwind cleanup, recoverability, panic strategy, and FFI unwind restrictions.
- `src/expressions/loop-expr.md`, blob `8e67295482c3826c841585172560d93b2823510f`: infinite `loop` without associated `break` is diverging.
- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`: Rust programs must not exhibit UB; UB categories and whole-program consequence; incomplete unsafe-code model.

**Rust compiler identity.** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` identifies the compiler/toolchain subject to which this Reference snapshot is applied in the Anneal corpus. This report makes no new compiler-implementation claim beyond that identity.

**Companion corpus evidence.** `reports/rust-panic-unwind-abort-divergence-nightly-2026-05-31/` on the zerocopy `reference` branch contains the detailed rustc MIR and Charon representation study for the same Rust/Reference subject. It is supporting corpus context, not an additional subject of this report.

No evidence above is fresh **execution**.

## Revalidation

For a later Rust revision, the cheapest source-level revalidation is:

1. Re-read the Reference definitions of divergence and `!`.
2. Re-read panic-handler, panic-strategy, unwind-cleanup, and FFI-unwind rules.
3. Re-read the Reference's UB statement.
4. Check whether the language has introduced a new ordinary/exceptional outcome category that makes this report's taxonomy incomplete.

The report-local definitions of partial and total correctness need not change merely because implementation details change. They should change only if the intended verification convention changes.

On an execution-capable surface, a small discriminator can demonstrate the distinctions without attempting to prove them:

- one function that returns normally;
- one infinite `loop {}`;
- one `panic!` under `panic=unwind` caught by an outer `catch_unwind`;
- the same panic under `panic=abort`;
- one well-defined panic-free function;
- one deliberately excluded UB witness that is inspected but **not executed**.

Observe which calls return normally, which larger computations recover, and which process executions terminate. This demonstrates the terminology on that toolchain; it does not establish the general language rules or justify executing UB.
