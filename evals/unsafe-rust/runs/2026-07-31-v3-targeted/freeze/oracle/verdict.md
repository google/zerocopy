# V3 Targeted Oracle — Verdict and Release Modes

> **Evaluator-only material.** Never expose this file, its mode labels, atoms,
> expected verdicts, or coverage relations to an evaluated report agent.
>
> Score propositions, not keywords or report layout. Equivalent explicit
> derivations pass. Do not infer a missing material link from vague shorthand.

## Common scoring rules

For each claim, `Required` is the product of its exact release set, supported
targets/profiles, valid calls, and any conditional postcondition domain.
`Covered` contains a case only when every obligation for that claim has a
complete derivation from premises applicable to that case. An existential
refutation needs no `Required subset Covered` proof; it needs every link of its
own certificate.

A report may give additional correct regional detail without penalty. A missed
atom is not automatically a hard error. It is a hard error only where the
mode-specific rule below or the frozen global rules say so.

## Q — Existential refutation and missing unsafe dependency

Target: supplied Q snapshot.

Let `C_Q` be Rust 1.80.0 times every target on which the exact source and pinned
dependency resolve times every ordinary profile.

- `Required(Q-force-sound) = C_Q` times the one well-typed safe call
  `force_unreachable()`.
- `Required(Q-delegate-sound) = C_Q` times every call
  `delegated_nonzero(value)` whose caller satisfies `value != 0`.

### Expected results and atoms

- **Q1 — Domain and claim separation:** State both valid-use domains and audit
  the two APIs independently. In particular, the `unsafe fn`'s documented
  nonzero precondition restricts its valid uses; it does not restrict the safe
  `force_unreachable` API.
- **Q2 — Complete UB certificate:** For `force_unreachable`, give all four
  links explicitly or by an equivalently exact chain:
  1. `force_unreachable()` is a well-typed, valid safe call in `Required`;
  2. the only body path reaches the executed
     `std::hint::unreachable_unchecked()` call;
  3. that call requires its site not to be reached, and that exact proposition
     is false for this call; and
  4. Rust 1.80.0 std documentation says reaching the function is undefined
     behavior.
- **Q3 — Existential closure:** Report `Q-force-sound` as **UNSOUND**. The one
  complete in-scope witness refutes the universal soundness claim; do not
  weaken it to `UNPROVED` because no proof covering every safe call was built.
  The witness exists in every `C_Q` configuration, but that stronger fact is
  not required for the existential verdict.
- **Q4 — Exact missing premise:** For `delegated_nonzero`, recognize that a
  valid caller supplies the dependency API's nonzero caller-side precondition,
  but the selected unsafe dependency's body is absent and no accepted
  `UNSAFE-DEP` entry establishes that it honors its contract. The exact pin and
  caller-facing documentation establish the logical package coordinate and the
  propagated obligation, not authenticated implementation identity or
  correctness. For the soundness claim actually requested here, the smallest
  missing proposition is that every valid nonzero call to the selected
  `peer-unsafe-dep` 3.4.5 implementation is free of UB over this exact domain.
- **Q5 — No fabricated witness or silent trust:** Report
  `Q-delegate-sound` as **UNPROVED**, not `PROVED` and not `UNSOUND`. From the
  submitted packet, claim-level `Covered(Q-delegate-sound)` contains no case:
  the dependency-soundness obligation is unresolved for all valid inputs.
  There is also no proved execution of the unavailable body, so no UB witness
  may be invented. State that recursive source audit or an explicitly accepted
  exact `UNSAFE-DEP` entry would be required.

### Q hard errors

Any of these is a hard error:

- calling `force_unreachable` sound or only `UNPROVED` after stating all four
  certificate links;
- issuing `UNSOUND` for it without a valid call, reachability, the false exact
  safety proposition, and the authoritative UB consequence;
- silently trusting the unavailable unsafe dependency, treating the exact pin
  as implementation proof, or reporting `delegated_nonzero` `PROVED`;
- fabricating dependency body behavior or a UB execution and reporting
  `delegated_nonzero` `UNSOUND`; or
- treating the unsafe dependency's documented caller precondition as though
  violating its prose were itself an executed UB event.

### Q checked authority

- `https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety`
  — exact proposition consumed: reaching
  `unreachable_unchecked` is undefined behavior; applicability Rust 1.80.0,
  without a target/profile qualification relevant to this fixture.

No Rust authority is asserted for the absent dependency implementation.

## W — Whole-execution UB and independent behavioral refutation

Target: supplied W snapshot.

Let `C_W` be Rust 1.80.0 times every target on which this exact source and the
used Rust 1.80.0 standard-library item exist times every ordinary profile, and
let `I = {0, ..., 255}`. The claims are:

- `Required(W-sound) = C_W times I`;
- `Required(W-panic) = C_W times {0}`; and
- `Required(W-return) = C_W times I`; its theorem is: for every UB-free defined
  execution in this domain, if that execution returns normally, its result
  equals its input.

### Expected results and atoms

- **W1 — Soundness witness:** `classify(0)` is a valid safe call, takes the
  zero arm, evaluates the local statements, and reaches
  `unreachable_unchecked`. Its unreachable-site proposition is false; the
  applicable 1.80.0 std contract entails UB. Report `W-sound` **UNSOUND**.
- **W2 — Whole-execution classification:** The input-zero execution as a whole
  contains UB. Neither its apparent prefix computation nor the source-level
  fact that no panic operation appears before the unsafe call remains a
  guaranteed observation from a defined execution. It therefore cannot prove
  a UB-free failure of the panic postcondition. With no independent UB-free
  input-zero execution or equivalent proof, report `W-panic` **UNPROVED**, not
  `CONTRACT-BROKEN` and not `PROVED`. Its claim-level `Covered` set is empty on
  the submitted evidence.
- **W3 — Independent defined witness:** `classify(1)` takes the `1 => 2` arm,
  executes no unsafe operation, returns normally, and returns `2` rather than
  the promised input value `1`. That complete execution is UB-free and proves
  `W-return` **CONTRACT-BROKEN**.

Scoring guidance, not a separate atom: keep the three executions/theorems
independent. The input-zero UB witness cannot establish failure of the panic
promise, while the independent, defined input-one failure remains usable and
does not alter the soundness witness.

### W hard errors

Any of these is a hard error:

- calling the safe API sound, reporting only `UNPROVED` after explicitly
  establishing every input-zero UB-certificate link, or issuing `UNSOUND`
  without those links;
- using the UB-containing input-zero execution, an apparent observation before
  its UB, or the absence of an earlier panic to issue `CONTRACT-BROKEN`;
- claiming source observations remain guaranteed merely because they occur
  before the unsafe call;
- falsely treating the independent input-one refutation as UB-containing, or
  claiming complete behavioral coverage while omitting it.

### W checked authorities

- `https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety`
  — reaching the function is undefined behavior.
- `https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html`
  — controlling Rust 1.80.0 Reference section for what constitutes undefined
  behavior. Verify that the final evaluator instructions do not attribute to
  this page prose it does not contain; whole-execution non-observability is the
  logical consequence of classifying the execution as undefined, not a claimed
  quotation from a “time travel” subsection.

## M — Multi-release affirmative certificates

Target: supplied M snapshot.

Let `C_M` be every supported target times every ordinary profile. For a
function `f`, let `Calls_f` be all calls satisfying its documented safety
preconditions. The exact required domains are:

- `Required(M-ack) = V_ack times C_M times Calls_ack`, where
  `V_ack = {1.80.0, 1.80.1, 1.81.0, 1.82.0}` and every typed call is valid;
- `Required(M-store) = V_store times C_M times Calls_store`, where
  `V_store = {1.80.0, 1.81.0}`;
- `Required(M-copy) = V_copy times C_M times Calls_copy`, where
  `V_copy = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`; and
- `Required(M-load) = V_load times C_M times Calls_load`, where
  `V_load = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`.

For `store_word`, `copy_byte`, and `load_word`, the same release domain applies
separately to soundness and the documented normal-return postcondition.

### Expected results and atoms

- **M1 — `acknowledge` domain:** Preserve exact finite set `V_ack` and its
  target/profile product; every well-typed call is in `Calls_ack` because the
  API adds no safety precondition.
- **M2 — `store_word` domains:** Preserve exact finite set `V_store` and its
  target/profile/valid-call product separately for soundness and the documented
  normal-return postcondition.
- **M3 — `copy_byte` domains:** Preserve exact finite set `V_copy` and its
  target/profile/valid-call product separately for soundness and the documented
  normal-return postcondition.
- **M4 — `load_word` domains:** Preserve exact finite set `V_load` and its
  target/profile/valid-call product separately for soundness and the documented
  normal-return postcondition.

For M1–M4, do not let the cutoff add or remove releases and do not substitute
an unscoped crate-wide claim for the exact products.

- **M5 — Parametric `acknowledge` proof:** Verify that accepted general entry
  `SEM-EMPTY-BLOCK-180-182` has exactly the required release, target, and
  profile scope. Independently inspect the local syntax and establish that the
  exact body is an empty block. For arbitrary
  `(v, target, profile, call) in Required(M-ack)`, combine only those premises:
  `acknowledge` is zero-parameter and unit-returning, the valid call has defined
  callee evaluation and returns `()`, and the `unsafe fn` marker changes only
  its static caller obligation. Thus
  `Covered(M-ack) = Required(M-ack)` and source-level soundness is **PROVED
  parametrically relative to `SEM-EMPTY-BLOCK-180-182`**. Keep the admission
  conspicuous; the TCB entry is general semantics, not a target-specific
  assertion that the function is sound.
- **M6 — `store_word` soundness partition:** The 1.80.0 `ptr::write` authority
  applies exactly to the 1.80.0 case and the 1.81.0 authority to the 1.81.0
  case. For each case, the documented caller contract entails the applicable
  page's alignment and write-validity preconditions. The identity
  `V_store = {1.80.0} union {1.81.0}` proves exhaustiveness. Therefore
  `Covered(M-store-sound) = Required(M-store-sound)` and soundness is
  **PROVED** by an exact finite partition.
- **M7 — `store_word` postcondition partition:** In each exact release case,
  the applicable page says that `ptr::write(dst, value)` writes the supplied
  `value` to `dst` without reading or dropping the old value. The same finite
  partition covers every normal-return postcondition obligation, so
  `Covered(M-store-post) = Required(M-store-post)` and the documented
  postcondition is **PROVED**.
- **M8 — `copy_byte` soundness under the exact TCB:** Verify the Rust 1.80.0
  `copy_nonoverlapping` safety proposition, primitive `u8` size, `u8: Copy`,
  and exact `Copy` semantics base propositions. Then apply only accepted entry
  `COMPAT-COPY-180-182`, with its exact release set, `T = u8`, `count = 1`,
  target/profile domain, and consumer. The caller contract entails its source
  and destination validity, initialization, alignment, and nonoverlap clauses;
  the admitted `u8` and `Copy` facts establish the one-byte specialization and
  avoid the ownership hazard for non-`Copy` values. Thus
  `Covered(M-copy-sound) = Required(M-copy-sound)` and soundness is **PROVED
  relative to `COMPAT-COPY-180-182`**.
- **M9 — `copy_byte` postcondition under the exact TCB:** The accepted entry
  preserves the base proposition that the call copies the source byte into the
  destination while leaving the source byte unchanged; `u8` has size one and
  implements `Copy` with the cited copy rather than move semantics. It covers
  every normal-return postcondition obligation, so
  `Covered(M-copy-post) = Required(M-copy-post)` and the documented
  postcondition is **PROVED relative to `COMPAT-COPY-180-182`**.
- **M10 — `load_word` soundness remainder:** In the 1.80.0 and 1.82.0 endpoint
  cases, the exact `ptr::read` Safety sections plus exact-version `u32: Copy`
  and `Copy`-semantics facts prove soundness from the caller contract,
  including safe retention of the source value alongside the returned copy.
  Thus
  `Covered(M-load-sound) = {1.80.0, 1.82.0} times C_M times Calls_load`.
  The 1.80.1 and 1.81.0 regions and therefore the complete `V_load` soundness
  claim are **UNPROVED**. No UB witness is supplied, so `UNSOUND` does not
  follow.
- **M11 — `load_word` postcondition remainder:** In the same two endpoint
  cases, the applicable `ptr::read` descriptions establish that the returned
  value is read from `src` while the source is left unchanged; the exact
  `u32: Copy` and `Copy`-semantics facts discharge the ownership qualification.
  Therefore
  `Covered(M-load-post) = {1.80.0, 1.82.0} times C_M times Calls_load`.
  The two interior regions and the complete postcondition claim are
  **UNPROVED**. No defined wrong-result witness is supplied, so
  `CONTRACT-BROKEN` does not follow.

Scoring guidance, not a separate atom: if a report actually relies on endpoint
sampling, the cutoff, an unstated stability guarantee, backward projection,
evidence for another operation, or a widened TCB entry to fill the `ptr::read`
interior, reject that basis explicitly. For an `UNPROVED` interior, require the
smallest missing premise: a verified authority for the interior releases, an
exact applicable accepted compatibility entry, or another complete parametric
proof. A report that uses none of the listed invalid bases need not recite them.

### M hard errors

Any of these is a hard error:

- reporting the complete `load_word` claim `PROVED` by endpoint sampling,
  cutoff reasoning, a stability badge, unprovided interior docs, or another
  operation's evidence;
- claiming `Required subset Covered` for `load_word` while omitting either
  interior release;
- silently widening `COMPAT-COPY-180-182` by release, operation, type/count,
  target/profile domain, proposition, or consumer;
- silently widening `SEM-EMPTY-BLOCK-180-182` by release, source shape,
  proposition, or consumer;
- treating either accepted entry as authoritative Rust text rather than a
  conspicuous TCB premise;
- projecting a later Rust proposition backward to an earlier release without
  an exact applicable premise; or
- issuing `UNSOUND` or `CONTRACT-BROKEN` for an unresolved interior merely from
  failure to prove it.

Failure to establish a required positive regional result is an atom failure. It
is not by itself a hard error unless the report also makes one of the false
affirmative or scope-changing claims above.

### M checked authorities

Open each exact page and confirm the named description and Safety propositions,
including all qualifications relevant to its exact release case:

- `https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html`
  — overwrites without reading or dropping the old value; `dst` must be valid
  for writes and properly aligned.
- `https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html`
  — the same exact propositions for the separate 1.81.0 case.
- `https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html`
  — copies `count * size_of::<T>()` bytes; source/destination validity,
  alignment, and nonoverlap requirements; base case only.
- `https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout`
  — `u8` has size 1.
- `https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8`
  — `u8` implements `Copy` in the compatibility base case.
- `https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html`
  — exact copy rather than move semantics for `Copy` values in the base and
  1.80.0 endpoint cases.
- `https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html`
  — reads without moving, leaves source unchanged, and requires read validity,
  alignment, and initialization for this non-ZST.
- `https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32`
  — `u32` implements `Copy` in the 1.80.0 endpoint case.
- `https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html`
  — the same named propositions for the separate endpoint case.
- `https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32`
  — `u32` implements `Copy` in the 1.82.0 endpoint case.
- `https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html`
  — exact copy rather than move semantics for `Copy` values in the 1.82.0
  endpoint case.

The `acknowledge` and compatibility results additionally consume the two exact
accepted propositions in target file `TCB.md`; that file is not Rust authority
and both admissions must remain identified as part of the conditional TCB.
