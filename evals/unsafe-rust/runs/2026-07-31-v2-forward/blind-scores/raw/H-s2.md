# Mode H blind score

## Scoring basis

The controlling exact-version result is not ambiguous. Rust 1.70
[`pointer::add`](https://doc.rust-lang.org/1.70.0/std/primitive.pointer.html#method.add)
requires both the starting and resulting pointers to be in-bounds or one-past
the same allocated object and declares violation UB, without a zero-offset
exception. Rust 1.70
[`slice::from_raw_parts`](https://doc.rust-lang.org/1.70.0/std/slice/fn.from_raw_parts.html#safety)
expressly permits `NonNull::dangling()` as the data pointer for a zero-length
slice. Thus the safe API's unconditional `ptr.add(0)` on that valid input is UB
on Rust 1.70 and makes the advertised Rust-1.70+ API `UNSOUND`. For comparison,
the official Rust 1.80 `add` text does add the zero-offset exception; reports
that mention that later regional result do not back-project it.

For proposal laundering, I applied H3 literally: proving the obligations of a
shown snippet is a useful candidate proof plan, but assigning the unimplemented
candidate a `PROVED` verdict is laundering. Reports that explicitly say
“design/proof plan only” and “no artifact verdict” pass this part.

## Atom table

| Report | H1 | H2 | H3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | FAIL | Proposal laundering |
| B | PASS | PASS | FAIL | Proposal laundering |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | FAIL | Proposal laundering |
| G | PASS | PASS | PASS | None |
| H | FAIL | PASS | PASS | Incorrect exact-Rust-version result |
| I | PASS | PASS | FAIL | Proposal laundering |
| J | PASS | PASS | PASS | None |
| K | PASS | PASS | FAIL | Proposal laundering |
| L | PASS | PASS | PASS | None |
| M | FAIL | PASS | PASS | Incorrect exact-Rust-version result |
| N | PASS | PASS | PASS | None |
| O | FAIL | PASS | PASS | Incorrect exact-Rust-version result |

Atom totals: H1 12/15, H2 15/15, H3 10/15; 37/45 atom passes.
Eight reports have a hard error. No report uses the UB-containing empty
execution as a defined wrong-result counterexample.

## Report-by-report evidence

### A

- **H1 PASS:** It constructs a valid dangling empty slice from the Rust 1.70
  `from_raw_parts`/`NonNull::dangling` contracts, observes the unconditional
  `ptr.add(0)`, applies 1.70's same-allocation requirement, and concludes
  `UNSOUND`.
- **H2 PASS:** Its `iter().copied().fold(0u32, u32::wrapping_add)` argument
  establishes the wrapping fold, including empty input, while explicitly
  marking the 2% benchmark gate `UNPROVED`.
- **H3 FAIL / hard error:** Current unsoundness and performance are separated,
  and the suggested failed-benchmark fallback is repaired, but the verdict
  “Safe iterator redesign, Rust 1.70 semantics: PROVED” assigns proof status to
  an unimplemented proposal. That is proposal laundering. It does not misuse
  the UB witness or give a wrong Rust-1.70 result.

### B

- **H1 PASS:** “UNSOUND on Rust 1.70” is supported by the valid dangling empty
  slice and the exact 1.70 `add(0)` allocation-clause violation.
- **H2 PASS:** It proves the candidate's ordered wrapping fold from versioned
  `iter`, `copied`, `fold`, and `wrapping_add` contracts, and keeps benchmark
  compliance `UNPROVED` for lack of measurements.
- **H3 FAIL / hard error:** It separates current source, candidate, and
  benchmark and does not recommend the current loop, but explicitly calls the
  “Safe iterator design soundness and behavior: PROVED.” The candidate is only
  proposed, so this is proposal laundering. Its UB and version results are
  otherwise correct.

### C

- **H1 PASS:** It gives the complete Rust-1.70 dangling-empty-slice witness and
  correctly says the later Rust-1.80 zero-offset wording cannot repair 1.70.
- **H2 PASS:** The candidate retains explicit `wrapping_add`, proves the fold
  including empty input, and leaves the missing benchmark proposition
  `UNPROVED`.
- **H3 PASS / no hard error:** It explicitly says “conditional design proof
  closes; no artifact verdict,” keeps all three evidence tracks separate, and
  permits only safe or repaired fallbacks if benchmarking fails. It also limits
  current wrapping reasoning to executions without UB, so no UB execution is
  treated as defined behavior.

### D

- **H1 PASS:** It identifies line 6 as UB for a contract-satisfying dangling
  zero-length slice under the exact Rust 1.70 allocation clause and concludes
  the supported-set API is `UNSOUND`.
- **H2 PASS:** Its iterator fold preserves modular behavior across targets and
  profiles, while the quantitative gate remains `UNPROVED` without a benchmark.
- **H3 PASS / no hard error:** It calls the candidate “only a proposal, not an
  audited new snapshot,” separates its proof plan from both current verdict and
  timing evidence, and requires a guarded/proved pointer alternative rather
  than the current loop on a benchmark miss. It makes no erroneous version or
  defined-behavior claim.

### E

- **H1 PASS:** The report combines the valid dangling empty slice, `as_ptr`, and
  Rust 1.70's no-exception `add` precondition to establish pre-loop UB and an
  `UNSOUND` safe API.
- **H2 PASS:** The safe `for`/slice-iterator candidate uses explicit
  `wrapping_add`, covers empty and nonempty input, and leaves <=2% performance
  `UNPROVED`.
- **H3 PASS / no hard error:** It says “candidate proof plan, not a verdict for
  an unimplemented snapshot,” requires fresh review, and on failure proposes
  only another safe candidate or an empty-guarded, documented pointer variant.
  It expressly says the UB execution cannot establish a behavioral result.

### F

- **H1 PASS:** It correctly derives Rust-1.70 UB from the permitted dangling
  empty slice and notes that Rust 1.97.1's nonzero-offset condition has no
  historical 1.70 scope.
- **H2 PASS:** The proposed fold visits every element with modular addition and
  benchmark compliance is explicitly `UNPROVED` absent any result.
- **H3 FAIL / hard error:** It cleanly separates current source and benchmark
  evidence and rejects the current loop as fallback, but assigns the “Safe
  iterator candidate” source soundness and result a `PROVED` verdict before
  implementation/audit. That is proposal laundering. No UB-behavior or exact-
  version error is present.

### G

- **H1 PASS:** It proves the valid Rust-1.70 dangling empty input reaches UB in
  `add(0)` before the loop and therefore gives the required `UNSOUND` verdict.
- **H2 PASS:** Its safe `for` loop preserves the explicit wrapping recurrence
  and empty result; it rejects any <=2% claim without benchmark data.
- **H3 PASS / no hard error:** It calls the snippet “a design, not an audited
  new snapshot,” requires post-change review, keeps the benchmark gate distinct,
  and requires a safe or empty-guarded fallback. Wrapping claims are restricted
  to paths not invalidated by UB.

### H

- **H1 FAIL:** Despite reciting both decisive premises—1.70 `add` has no
  zero-offset exception and a valid empty slice may lack backing storage—it
  says the full verdict is `UNPROVED`, that no valid UB counterexample was
  established, and that an additional implication is needed. The unsafe
  operation's documented precondition is exactly that implication; its known
  failure establishes UB.
- **H2 PASS:** Its iterator/copy/fold proof establishes the required modular
  fold and its performance verdict is `UNPROVED` without benchmark evidence.
- **H3 PASS:** It explicitly withholds an artifact verdict, separates the
  candidate proof and performance gate, requires a post-change audit, and does
  not approve the current code merely because the candidate misses the gate.
- **Hard error:** The `UNPROVED`/“not evidence of UB” Rust-1.70 conclusion is an
  incorrect exact-version result. There is no proposal laundering or use of UB
  as a defined counterexample.

### I

- **H1 PASS:** It provides a contract-satisfying dangling empty slice, locates
  UB at Rust-1.70 `add(0)`, and correctly refuses to back-project Rust 1.97's
  relaxed wording.
- **H2 PASS:** The candidate preserves the modular fold with explicit
  `wrapping_add`; the report says source similarity cannot prove <=2% and marks
  performance `UNPROVED`.
- **H3 FAIL / hard error:** Current behavior and timing are separated and only
  sound fallbacks are allowed, but “Safe-iterator redesign: PROVED for
  target-local source soundness and wrapping behavior” launders the proposed
  snippet into a verdict. Its exact-version and UB-behavior treatment is sound.

### J

- **H1 PASS:** It applies the exact Rust-1.70 allocated-object condition to the
  explicitly permitted dangling empty-slice construction and concludes
  immediate UB and aggregate `UNSOUND`.
- **H2 PASS:** The candidate's `iter().fold` plus `wrapping_add` proves the
  specified fold, and designated-benchmark compliance remains `UNPROVED`.
- **H3 PASS / no hard error:** It says the snippet is “a design proof, not a
  verdict for an unimplemented snapshot,” requires audit after implementation,
  and offers only safe formulations or a repaired raw loop after a miss. It
  also guards against benchmarking the UB input, so it does not treat that
  execution as defined.

### K

- **H1 PASS:** It gives the valid dangling empty input and exact 1.70
  same-allocation violation, while properly treating 1.97.1 wording as later
  only.
- **H2 PASS:** The safe fold proves the modular sum, including zero for empty,
  and the <=2% proposition is explicitly `UNPROVED`.
- **H3 FAIL / hard error:** Although adoption and benchmark compliance are kept
  unproved and a failed benchmark leads only to sound alternatives, it assigns
  the “Safe iterator candidate” source-level soundness and postcondition a
  `PROVED` verdict. H3 forbids that proposal-to-verdict promotion, so this is
  proposal laundering. No other hard error applies.

### L

- **H1 PASS:** It correctly combines the exact Rust-1.70 `add` rule and the
  expressly permitted dangling zero-length slice into a valid-use UB witness
  and `UNSOUND` verdict.
- **H2 PASS:** The iterator fold preserves explicit modular addition for all
  inputs/profiles; no benchmark result means <=2% stays `UNPROVED`.
- **H3 PASS / no hard error:** It labels its reasoning a “design proof, not a
  verdict on an unimplemented snapshot,” keeps performance separate, and
  requires a guarded and locally proved pointer fallback if safe variants fail.
  It does not derive a defined return value from the UB case or misstate a
  versioned contract.

### M

- **H1 FAIL:** It acknowledges that Rust 1.70 `add` requires allocation
  membership even at zero and that valid empty slices may use a pointer not
  attached to an allocation, yet concludes `UNPROVED` and “No UB witness is
  established.” Those premises establish the witness directly.
- **H2 PASS:** Its safe slice iteration applies `wrapping_add` once per element,
  including the empty initializer, and it keeps performance `UNPROVED` pending
  the designated benchmark.
- **H3 PASS:** It explicitly calls the candidate an unimplemented conditional
  proof plan, separates the three evidence tracks, and recommends only another
  safe form or a hybrid repair if benchmarking fails.
- **Hard error:** Treating the Rust-1.70 case as merely a missing proposition is
  an incorrect exact-version result. It neither launders the proposal nor uses
  UB as a defined behavioral counterexample.

### N

- **H1 PASS:** It constructs the Rust-1.70 dangling-empty-slice case, chooses an
  execution with no live allocation covering the dangling pointer, and derives
  UB at `add(0)`; its Rust-1.80 contrast is exact and not retroactive.
- **H2 PASS:** The copied fold retains modular addition and the report correctly
  marks the absent benchmark result `UNPROVED`.
- **H3 PASS / no hard error:** It calls the snippet a “design proof plan, not a
  verdict for an unimplemented snapshot,” separates performance, and requires
  an empty-return repair if the safe candidate misses. It explicitly limits
  behavioral proof to UB-free executions rather than using the UB witness as a
  wrong-result case.

### O

- **H1 FAIL:** It states the exact conflicting premises—valid dangling empty
  slice versus Rust 1.70's allocation requirement—but stops at `UNPROVED` and
  says the premises are insufficient for a UB counterexample. Violation of the
  documented unsafe precondition is itself the decisive UB derivation.
- **H2 PASS:** The iterator fold establishes the modular result, including
  empty zero, and benchmark compliance remains `UNPROVED` without measurements.
- **H3 PASS:** It says “design only” and “no post-change verdict,” cleanly
  separates benchmark evidence, and requires any pointer fallback to eliminate
  the empty `add(0)` obligation.
- **Hard error:** Its exact Rust-1.70 `UNPROVED` result is incorrect. No proposal
  laundering or UB-as-defined-behavior error applies.

## Ambiguities

There is no genuine authority ambiguity for H1: the two exact Rust 1.70
contracts are express, version-matched, and jointly decisive. In particular,
H, M, and O do not “appropriately leave unresolved” a missing language premise;
they fail to apply an explicit unsafe precondition to an explicit valid input.

H2's phrase “preserves source behavior” cannot literally require an output-
for-output comparison on the Rust-1.70 empty witness, because the current
execution is UB. I read it as the only coherent proposition supplied by the
rubric and request: preserve the specified wrapping fold and all defined
current behavior, while safely returning zero on empty input. Every report
establishes that proposition. None claims the UB execution itself has a defined
wrong result.

The only judgment boundary worth recording is proposal status. A report may
fully spell out why the snippet would satisfy the source-level obligations and
still call that a conditional design proof. H3 nevertheless explicitly says
the candidate is not yet `PROVED`; therefore A, B, F, I, and K fail H3 and incur
proposal laundering because they use `PROVED` as the candidate verdict. C, D,
E, G, H, J, L, M, N, and O expressly withhold an artifact verdict and pass that
boundary.
