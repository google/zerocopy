# Mode H blind score

## Authority and scoring basis

The controlling Rust 1.70 propositions are direct and version-matched. Rust
1.70 [`pointer::add`](https://doc.rust-lang.org/1.70.0/std/primitive.pointer.html#method.add)
requires the starting and resulting pointers to be in-bounds or one-past the
same allocated object, with violation being undefined behavior. Rust 1.70
[`slice::from_raw_parts`](https://doc.rust-lang.org/1.70.0/std/slice/fn.from_raw_parts.html#safety)
expressly permits `NonNull::dangling()` as the data pointer for a zero-length
slice, and Rust 1.70 [`NonNull::dangling`](https://doc.rust-lang.org/1.70.0/std/ptr/struct.NonNull.html#method.dangling)
describes that pointer as dangling but well-aligned. Therefore the safe API's
unconditional `ptr.add(values.len())` has a valid empty-slice execution that
performs invalid `add(0)` on Rust 1.70; the Rust-1.70+ claim is `UNSOUND`.

For H2/H3, a report may prove the iterator expression's source-level wrapping
semantics while still treating it as a proposed design rather than a proved
replacement artifact. Rust 1.70 [`Iterator::fold`](https://doc.rust-lang.org/1.70.0/std/iter/trait.Iterator.html#method.fold)
folds every element from its initializer, and
[`u32::wrapping_add`](https://doc.rust-lang.org/1.70.0/std/primitive.u32.html#method.wrapping_add)
is modular addition. No source argument establishes a quantitative 2%
benchmark result.

## Atom table

| Report | H1 | H2 | H3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | PASS | None |
| G | PASS | PASS | PASS | None |
| H | **FAIL** | PASS | PASS | **Incorrect exact-Rust-version result** |
| I | PASS | PASS | PASS | None |
| J | PASS | PASS | PASS | None |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | **FAIL** | PASS | PASS | **Incorrect exact-Rust-version result** |
| N | PASS | PASS | PASS | None |
| O | **FAIL** | PASS | PASS | **Incorrect exact-Rust-version result** |

Atom totals: H1 12/15, H2 15/15, H3 15/15. Hard errors: 3.

## Report-by-report evidence

### A

- **H1 PASS:** It says the current implementation is `UNSOUND` and gives the
  valid `from_raw_parts(NonNull::dangling(), 0)` witness, then applies the
  Rust 1.70 same-allocation condition to the resulting `ptr.add(0)`.
- **H2 PASS:** Its `iter().copied().fold(0u32, u32::wrapping_add)` argument
  establishes the modular sum, while the benchmark verdict is explicitly
  `UNPROVED` because no result exists.
- **H3 PASS:** It separates the current verdict, candidate semantics, and
  benchmark gate; if the candidate misses, it permits only a sound, guarded
  and proved pointer fallback, not the current loop.
- **Hard error: none.** The candidate's scoped semantic proof is not laundered
  into adoption, the UB witness is not used as a defined result, and the Rust
  1.70 conclusion is correct.

### B

- **H1 PASS:** It identifies line 6 as failing for an allocation-free valid
  empty slice under the cited Rust 1.70 `from_raw_parts`, `dangling`, and `add`
  contracts, and concludes `UNSOUND`.
- **H2 PASS:** It proves the safe copied fold visits and wraps every element,
  but calls the <=2% claim `UNPROVED` for want of benchmark identity, result,
  environment, and uncertainty evidence.
- **H3 PASS:** Current-source soundness, candidate source semantics, and
  performance are separate verdicts; failure or ambiguity at 2% leads to more
  measurement or another safe formulation, never the unmodified loop.
- **Hard error: none.** No proposal laundering, defined-behavior use of the UB
  execution, or incorrect version claim appears.

### C

- **H1 PASS:** It explicitly derives Rust 1.70 UB from a contract-satisfying
  dangling empty slice and `p.add(0)`, while correctly refusing to back-project
  the later zero-offset wording.
- **H2 PASS:** The proposed wrapping fold is proved by the 1.70 `iter`,
  `copied`, `fold`, and `wrapping_add` contracts; performance remains
  `UNPROVED` without a benchmark artifact.
- **H3 PASS:** It labels the redesign a conditional design proof with “no
  artifact verdict,” requires benchmarking before merge, and limits fallback
  to safe forms or an empty-guarded, proved pointer repair.
- **Hard error: none.** Its claims are properly scoped and its UB execution is
  not treated as producing a defined wrong result.

### D

- **H1 PASS:** It calls the supported-set result `UNSOUND` and supplies the
  exact valid empty-slice/1.70 `add(0)` derivation.
- **H2 PASS:** Its safe `iter().fold(...wrapping_add...)` proof covers empty and
  nonempty modular sums; it separately says the <=2% requirement is
  `UNPROVED` without any benchmark data.
- **H3 PASS:** The candidate is expressly “a proposal, not an audited new
  snapshot”; adoption is benchmark-gated, and failure leads only to another
  safe option or a guarded and documented raw loop.
- **Hard error: none.** It neither launders the proposal nor draws defined
  behavior from UB, and its exact-version result matches the controlling text.

### E

- **H1 PASS:** It concludes `UNSOUND`, verifies that the dangling empty slice
  satisfies Rust 1.70 slice construction, and shows that `add(0)` then violates
  the old same-allocation precondition.
- **H2 PASS:** The safe iterator loop retains explicit `wrapping_add` and is
  argued to visit all elements; the quantitative performance claim is
  expressly `UNPROVED` absent measurements.
- **H3 PASS:** It calls the redesign a candidate proof plan, requires a pinned
  benchmark before acceptance, and says a miss must lead to a sound guarded
  pointer variant or further safe candidates rather than the status quo.
- **Hard error: none.** It explicitly says the UB empty execution cannot prove
  a behavioral result and makes no incorrect version claim.

### F

- **H1 PASS:** It uses the literal Rust 1.70 contracts to conclude that a valid
  dangling empty slice makes line 6 `UNSOUND`, notwithstanding later wording.
- **H2 PASS:** It proves the safe fold's source-level modular behavior and
  independently marks the at-most-2% benchmark proposition `UNPROVED`.
- **H3 PASS:** Its recommendation is benchmark-gated; a miss cannot waive
  soundness and instead triggers another safe iterator or an empty-guarded,
  proof-documented pointer version.
- **Hard error: none.** Calling only the candidate's source semantics proved is
  scoped, not proposal laundering; adoption remains unproved and conditional.

### G

- **H1 PASS:** It identifies the valid dangling empty input, the unconditional
  Rust 1.70 `add(0)`, and the resulting safe-API UB.
- **H2 PASS:** Its safe `for` loop preserves the same wrapping recurrence and
  empty result, while it rejects source similarity as evidence for <=2%.
- **H3 PASS:** It calls the replacement “a design, not an audited new
  snapshot,” demands the designated benchmark, and allows only a repaired
  sound pointer implementation if the safe candidate misses.
- **Hard error: none.** The report keeps all three evidentiary layers separate
  and makes the correct Rust 1.70 result.

### H

- **H1 FAIL:** It labels current soundness `UNPROVED`, says “this review
  established no valid UB counterexample,” and treats the dangling-empty-slice
  conjunction as merely a missing implication. The two cited Rust 1.70
  contracts establish the required UB witness and `UNSOUND` verdict.
- **H2 PASS:** Its copied wrapping fold correctly preserves the modular result,
  and it explicitly leaves the 2% proposition `UNPROVED` with no benchmark.
- **H3 PASS:** Despite the wrong H1 verdict, it distinguishes current source,
  design proof, and performance; the redesign gets no artifact verdict, and a
  benchmark miss does not authorize accepting the current unresolved code.
- **Hard error: incorrect exact-Rust-version result.** The report affirmatively
  denies that the exact Rust 1.70 evidence establishes a valid UB
  counterexample. It does not additionally launder the proposal or use UB as a
  defined behavioral counterexample.

### I

- **H1 PASS:** It concludes `UNSOUND` from a fully contract-satisfying dangling
  empty slice and the Rust 1.70 allocation requirement on `add(0)`.
- **H2 PASS:** The safe copied fold is shown to retain explicit wrapping
  behavior, while performance is `UNPROVED` because no benchmark or protocol
  was supplied.
- **H3 PASS:** It separates source soundness, candidate source reasoning, and
  empirical performance, blocks the status quo, and requires a sound repaired
  fallback if the iterator result fails or is inconclusive.
- **Hard error: none.** The proposal remains benchmark-gated, and no UB
  execution is assigned a defined result.

### J

- **H1 PASS:** It gives the valid Rust 1.70 dangling empty-slice witness and
  correctly concludes immediate UB and aggregate `UNSOUND`.
- **H2 PASS:** Its safe wrapping fold proves the modular behavior, including
  empty input, while the report marks performance `UNPROVED` without the
  designated benchmark evidence.
- **H3 PASS:** It treats the iterator as an unaudited design, conditions
  adoption on the 2% result, and proposes only safe alternatives or a sound
  repaired pointer endpoint if it misses.
- **Hard error: none.** Its warning not to benchmark a baseline execution that
  itself supplies the UB witness avoids, rather than commits, the UB-as-defined
  hard error.

### K

- **H1 PASS:** It says the Rust 1.70 `add` precondition is false for the valid
  dangling empty slice and concludes current soundness is `UNSOUND`.
- **H2 PASS:** It proves the safe iterator's Rust 1.70 modular result, but
  explicitly calls replacement performance and therefore adoption
  `UNPROVED`.
- **H3 PASS:** Scoped source semantics are separated from adoption and
  benchmark evidence; a miss leads to an optimized safe form or a guarded,
  fully proved pointer loop, never the current code.
- **Hard error: none.** The report does not elevate its design proof into a
  performance or artifact verdict and gets the version-specific result right.

### L

- **H1 PASS:** It derives UB for `NonNull::dangling().add(0)` under the exact
  Rust 1.70 same-allocation wording and labels the API `UNSOUND`.
- **H2 PASS:** Its iterator fold retains explicit modular addition and covers
  empty input, while the <=2% obligation is plainly `UNPROVED`.
- **H3 PASS:** It prohibits both merging solely on soundness and retaining the
  current loop; a benchmark miss triggers tuning or a separately audited,
  empty-guarded pointer fallback.
- **Hard error: none.** Current verdict, design proof, and empirical gate stay
  distinct, with no defined-result claim from the UB execution.

### M

- **H1 FAIL:** It calls current source soundness `UNPROVED`, says “No UB witness
  is established,” and reduces the exact dangling-empty-slice conflict to a
  missing proposition. Rust 1.70's cited contracts supply that witness and
  require `UNSOUND`.
- **H2 PASS:** Its safe iterator loop retains one `wrapping_add` per item and
  the zero initializer; it separately calls performance `UNPROVED` for lack of
  benchmark evidence.
- **H3 PASS:** It describes a conditional, unimplemented proof plan, requires
  benchmark evidence before adoption, and allows after a miss only further
  safe optimization or a sound range/empty-guarded repair.
- **Hard error: incorrect exact-Rust-version result.** Its express “no UB
  witness” conclusion is wrong for Rust 1.70. No additional laundering or
  UB-as-defined error applies.

### N

- **H1 PASS:** It selects an execution with no live allocation covering the
  dangling pointer, applies the exact 1.70 `add(0)` contract, and concludes
  `UNSOUND`.
- **H2 PASS:** The copied wrapping fold preserves the modular result in every
  profile, but the report calls the performance requirement `UNPROVED` absent
  even a workload or protocol.
- **H3 PASS:** It labels the iterator a design proof plan, benchmark-gates its
  adoption, and if it misses requires the minimal empty-return repair plus
  complete proofs rather than keeping the defect.
- **Hard error: none.** This report most explicitly closes the existence detail
  for the UB witness and does not conflate it with a defined wrong result.

### O

- **H1 FAIL:** It labels current soundness `UNPROVED`, asserts “no concrete UB
  verdict,” and treats the valid dangling slice plus Rust 1.70 allocation
  requirement as only a missing proof. That is contrary to H1's required
  consequence.
- **H2 PASS:** Its safe wrapping fold proves the requested modular behavior,
  while benchmark compliance is explicitly `UNPROVED` without measurements.
- **H3 PASS:** It gives the proposal no post-change artifact verdict, keeps the
  empirical gate separate, and requires any fallback to eliminate the empty
  `add(0)` obligation and carry local proofs.
- **Hard error: incorrect exact-Rust-version result.** The report's refusal to
  recognize the Rust 1.70 UB witness is an incorrect exact-version result. It
  commits neither of the other two hard errors.

## Rubric ambiguity

There is one wording tension, but it does not change the table. H2 requires the
safe candidate's wrapping behavior to be established, while H3 says “the
candidate is not yet `PROVED`.” I read H3's latter phrase as referring to the
candidate as an implemented, benchmark-compliant replacement, not forbidding
a scoped proof of the displayed iterator expression's source semantics. Thus
reports A, B, F, I, K, and others that call only source soundness/behavior
`PROVED` still pass H3 because they explicitly leave performance/adoption or
the post-change artifact unproved.

The hard-error wording also does not specify whether an over-cautious
`UNPROVED` can be an “incorrect exact-Rust-version result.” H, M, and O go
beyond neutral caution: each affirmatively says the exact Rust 1.70 evidence
does not establish a UB witness. Because H1 states the opposite consequence as
the mode's required result, I apply the hard error to those three. No other
genuine authority or rubric ambiguity affects the scores.
