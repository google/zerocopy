# Mode M Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

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
