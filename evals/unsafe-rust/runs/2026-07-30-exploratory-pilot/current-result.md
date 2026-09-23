# Current Zerocopy `impls.rs` Challenge

Snapshot: `53a3fbfa15d656b25b74688369f7248ff354a021`.

This challenge has no whole-target positive oracle and receives no aggregate
semantic score. Novel claims were independently source-reviewed; they are not
converted into confirmed production unsoundness merely because an evaluated
agent reported them.

## Paired result

| Behavior | Skill | Baseline |
|---|---|---|
| Overall production verdict | `UNPROVED`; no concrete valid-use UB or false postcondition established | `UNPROVED`; no concrete downstream production UB established |
| SIMD normative proof gap | Found | Found |
| Historical-version `Option` zero-representation gap | Missed/claimed locally closed | Found |
| `ManuallyDrop<T>: HasField` exact-contract concern | Missed | Found |
| Incomplete `Immutable` proof for `Box<T>` | Found | Found as a documentation residual |
| Optional function-pointer/`NonNull` `Immutable` proof | Called unproved | Called documentation residual |
| Missing fixture/configuration inputs | Found | Not made explicit |
| Two `assume_initialized` sites | Correctly scoped test-only and `UNPROVED`, not `UNSOUND` | Correctly scoped test-only and unjustified, not downstream production |

Both agents resisted the tempting but unjustified conclusion that an explicit
“this is unsound” FIXME in generic test machinery proves a concrete bad
execution or a downstream-shipping defect.

## Independent adjudication

### Confirmed proof gaps

- **Option zero representation: `UNPROVED` over the declared Rust 1.56+
  range.** The source cites a Rust 1.89 guarantee. Independent version review
  found that the explicit all-zero-to-`None` guarantee appears later than the
  declared MSRV for several families, and the explicit unsafe-function-pointer
  coverage later still. No compiler counterexample was established, so this
  is missing authoritative coverage, not demonstrated unsoundness.
- **Aggregate SIMD matrix: `UNPROVED`.** The generic argument relies on
  nonnormative UCG text that disclaims being a guarantee. Some current
  per-type standard-library pages may close individual types, but no reviewed
  proof covers every emitted type, architecture, feature, nightly, and
  supported compiler version.
- **`Box<T>: Immutable`: `UNPROVED`.** No reviewed normative contract
  establishes the representation property required by zerocopy's trait over
  the entire supported compiler range. No counterexample was found.

### Claims narrowed or disputed

- A reviewer derived the optional function-pointer and `NonNull<T>`
  `Immutable` obligations from normative `Copy` restrictions and
  `UnsafeCell` rules and classified them `PROVED`. Thus the skill report's
  `UNPROVED` classification for these two families is conservative
  over-reporting, not an admitted defect.
- A reviewer classified `ManuallyDrop<T>: HasField` as
  `CONTRACT-BROKEN`: the local contract asks for exact field identity, type,
  and visibility, while public std documentation exposes only private fields
  and the implementation uses a public proxy marker. No invalid projection,
  memory unsafety, or provenance failure was demonstrated because std does
  guarantee `ManuallyDrop<T>` has `T`'s layout and bit validity.

  This semantic classification still needs project-author review. The local
  contract permits `Self` merely to share the layout of a type containing the
  field, so a layout-equivalent public proxy-field interpretation may be
  intended. The pilot therefore records the claim as a high-priority contract
  ambiguity, not a final production defect.
- The two test-only `assume_initialized` comments give an invalid generic
  implication: `TryFromBytes` does not imply initialized padding. A second
  review found that the finite current test invocations nevertheless construct
  byte-initialized values. The admitted conclusion is proof-comment debt in
  test-only code; no concrete bad execution or production issue was proved.

## Fixture failure discovered by the skill

The current blind bundle included `Cargo.toml`, `build.rs`, and `src/`, but
omitted the lockfile, path-dependency sources, linked MSRV policy, and pinned
nightly/configuration material needed for a complete theorem. The skill agent
correctly refused closure for those axes.

This is an evaluation-fixture defect, not evidence against zerocopy. A future
scored current-source run must rebuild the bundle with all semantically
required policy, dependency, generated, and configuration inputs and then
restart both conditions from fresh agents.

## Interpretation

The baseline found two important obligations that the skill report omitted,
while the skill was more explicit about theorem status, configuration
incompleteness, and exact residual scope. This mixed result is useful: the
skill improved reporting discipline but did not dominate unaided defect/proof
gap discovery on the current high-quality target.
