# Mode V blind score

The exact versioned authorities confirm the rubric's split: `[u8; 0]` has size
zero; Rust 1.79.0's `add` contract unconditionally requires the start and result
to be in or one-past the same allocated object; Rust 1.80.0 guards that
allocation condition on a nonzero byte offset and expressly makes a zero offset
always well-defined. Each report is scored independently below.

## Atom and hard-error table

| Report | V1 | V2 | V3 | V4 | Hard error |
|---|---|---|---|---|---|
| A | PASS | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | PASS | None |
| F | PASS | PASS | PASS | PASS | None |
| G | PASS | PASS | PASS | PASS | None |
| H | PASS | PASS | PASS | PASS | None |
| I | PASS | PASS | PASS | PASS | None |
| J | PASS | PASS | PASS | PASS | None |
| K | PASS | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | PASS | None |
| M | PASS | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | PASS | None |
| O | PASS | PASS | PASS | PASS | None |

## Report-by-report evidence

### A

- **V1 PASS:** `O1` cites both versioned Reference array-layout pages, derives
  `size_of::<[u8; 0]>() == 0`, and computes `1 * 0 = 0` bytes.
- **V2 PASS:** `O2-79` cites the 1.79 `add`, `null`, and pointer-safety text,
  explains that null fails the unconditional allocated-object condition, and
  gives `let _ = advance_marker();` as the safe-call UB witness.
- **V3 PASS:** `O2-80` cites the 1.80 zero-offset sentence, discharges the
  arithmetic clauses, and notes that the raw pointer is not dereferenced.
- **V4 PASS:** The verdict table says 1.79 `UNSOUND`, 1.80 `PROVED`, and the
  union `UNSOUND`; the TCB section expressly rejects cross-version premises.
- **Hard error: none:** Both regional verdicts are proved, and both the
  zero-size derivation and null safe-call witness are present.

### B

- **V1 PASS:** The boundary section cites the two versioned array-layout rules
  and derives a zero byte offset for `add(1)`.
- **V2 PASS:** The ledger marks 1.79 `O2` failed; the derivation cites exact
  1.79 `null`, pointer-safety, and `add` text and identifies an ordinary safe
  invocation as the unconditional UB witness.
- **V3 PASS:** The report uses only the 1.80 `add` contract for its express
  zero-offset exception and observes that returning the raw pointer does not
  dereference it.
- **V4 PASS:** It reports 1.79 `UNSOUND`, 1.80 `PROVED`, combined `UNSOUND`,
  and explicitly says the 1.80 wording is not applied backward.
- **Hard error: none:** No uniform unsupported verdict, wrong region, backward
  projection, or missing required derivation/witness occurs.

### C

- **V1 PASS:** `O-ADD` cites version-matched `size_of` pages and derives
  `size_of::<[u8; 0]>() = 0` and offset `1 * 0 = 0`.
- **V2 PASS:** The 1.79 subsection cites the exact `add` and pointer-safety
  pages, states that null is neither in nor one-past an allocation, and says
  every safe call reaches UB.
- **V3 PASS:** The 1.80 subsection cites “always well-defined” for zero offset,
  checks the arithmetic, and notes that no dereference occurs.
- **V4 PASS:** The opening table partitions both releases and gives the union
  `UNSOUND`; the TCB is separately versioned.
- **Hard error: none:** The complete regional proof and counterexample include
  all hard-error-sensitive propositions.

### D

- **V1 PASS:** The configuration/ledger derives
  `1 * size_of::<[u8; 0]>() = 0` from exact 1.79/1.80 `size_of` authorities.
- **V2 PASS:** `O3` is marked violated for 1.79; the prose cites its
  unconditional same-allocation `add` clause and identifies any ordinary call
  to this argument-free safe function as the UB witness.
- **V3 PASS:** The report cites 1.80's express zero-offset exception, checks
  `isize`/`usize`, and observes there is no dereference or reference creation.
- **V4 PASS:** The opening verdicts correctly give 1.79 `UNSOUND`, 1.80
  `PROVED`, and combined `UNSOUND` without reusing 1.80 text for 1.79.
- **Hard error: none:** Every regional and combined verdict is supported, with
  the null witness and ZST arithmetic explicit.

### E

- **V1 PASS:** The inventory cites exact versioned `size_of` pages and computes
  the byte offset as `1 * 0 = 0`.
- **V2 PASS:** The 1.79 derivation cites `add`, `null`, and contemporaneous
  pointer-safety text; it explains the failed allocation conjunct and calls
  every ordinary invocation a valid safe-use counterexample.
- **V3 PASS:** The 1.80 derivation cites the changed clause and “always
  well-defined” sentence, checks arithmetic, and excludes later dereference.
- **V4 PASS:** Its table gives the two correct regional verdicts and combined
  `UNSOUND`; its TCB says no compatibility inference crosses versions.
- **Hard error: none:** None of the listed hard-error conditions applies.

### F

- **V1 PASS:** The common derivation cites exact 1.79/1.80 `size_of` contracts,
  establishes the ZST, and computes zero bytes.
- **V2 PASS:** The 1.79 section cites the unconditional allocation wording and
  null-validity text, then says every safe call reaches the violating `add`.
- **V3 PASS:** The 1.80 section cites the zero-offset exception and raw-pointer
  nullability and states that any dereference would be a separate unsafe act.
- **V4 PASS:** The verdict table partitions the releases and reports their
  union `UNSOUND`; the TCB is exact-version scoped.
- **Hard error: none:** The report proves rather than merely asserts all three
  verdicts and includes both mandatory witness components.

### G

- **V1 PASS:** Common local fact 2 uses exact versioned Reference array-layout
  links; fact 3 computes `1 * 0 = 0`.
- **V2 PASS:** The 1.79 regional derivation cites its exact `add` contract,
  states why null satisfies neither allocation alternative, and identifies
  every safe call as a concrete UB counterexample.
- **V3 PASS:** The 1.80 derivation cites its express zero-offset rule, checks
  both arithmetic constraints, and notes no dereference occurs.
- **V4 PASS:** Despite placeholder region labels, the text unambiguously names
  1.79 `UNSOUND`, 1.80 `PROVED`, and their union `UNSOUND`; each TCB link is
  version matched.
- **Hard error: none:** The placeholders do not obscure any material
  proposition, and no listed substantive error occurs.

### H

- **V1 PASS:** `OB-1` cites both exact `size_of` pages and derives the
  zero-sized pointee and zero byte offset.
- **V2 PASS:** The 1.79 section cites exact `add` and pointer-module text,
  explains why null fails the unconditional allocation condition, and uses a
  plain safe invocation as the UB witness.
- **V3 PASS:** The 1.80 section cites the changed contract, checks zero's
  representability/address arithmetic, and notes no reference or access.
- **V4 PASS:** The verdict table has both correct regions and combined
  `UNSOUND`; the report expressly says the 1.80 text is not projected backward.
- **Hard error: none:** All hard-error-sensitive facts are present and correct.

### I

- **V1 PASS:** The ledger cites exact versioned Reference array layout and
  computes `size_of::<[u8; 0]>() = 0` and a zero byte offset.
- **V2 PASS:** The 1.79 subsection cites that version's `add`, derives the
  failed allocation clause from the null start, and gives an unconditional
  ordinary safe call as witness.
- **V3 PASS:** The 1.80 subsection cites the express exception, checks the
  remaining clauses, and states that no dereference/reference is formed.
- **V4 PASS:** The report gives separate correct verdicts and combined
  `UNSOUND`; its TCB admits no cross-version compatibility premise.
- **Hard error: none:** Its extra edition observation does not alter or weaken
  the proved requested partition; no rubric hard error applies.

### J

- **V1 PASS:** `O-1` cites exact 1.79/1.80 `size_of` pages and derives
  `1 * 0 = 0` independently of target/profile.
- **V2 PASS:** `O-2/1.79` cites `null`, pointer safety, and `add`; it explains
  the allocation failure and supplies `let _ = advance_marker();` as witness.
- **V3 PASS:** `O-2/1.80` cites the express zero-offset sentence, checks
  arithmetic, and notes that returning the pointer is no further unsafe act.
- **V4 PASS:** The table correctly partitions and combines the regions, and
  the TCB says no later documentation was carried backward.
- **Hard error: none:** All required propositions and the witness are proved.

### K

- **V1 PASS:** `O-SIZE` cites exact versioned official `std::mem::size_of`
  pages and computes the zero byte offset.
- **V2 PASS:** `O-179` cites exact 1.79 official `std` reexports for `null`,
  pointer safety, and `add`, then identifies every safe call as UB at line 4.
- **V3 PASS:** `O-180` cites the exact 1.80 `std` pointer contract, checks the
  arithmetic clauses, and notes there is no access/dereference.
- **V4 PASS:** The table reports the two correct regions and combined
  `UNSOUND`; the TCB confines each contract to its exact release.
- **Hard error: none:** Using official `std` documentation rather than the
  equivalent `core` pages is permitted and introduces no material gap.

### L

- **V1 PASS:** The derivation cites exact release-specific `size_of` pages and
  computes `1 * size_of::<[u8; 0]>() = 0`.
- **V2 PASS:** The 1.79 subsection cites exact `add`, `null`, and pointer-safety
  text, marks the allocation conjunct false, and identifies all safe calls as
  the counterexample.
- **V3 PASS:** The 1.80 subsection cites the explicit zero exception, checks
  `isize`/`usize`, and observes no access/reference is created.
- **V4 PASS:** Its table gives 1.79 `UNSOUND`, 1.80 `PROVED`, and combined
  `UNSOUND`; the TCB is version matched.
- **Hard error: none:** No uniform-verdict, regional, projection, witness, or
  size-derivation error appears.

### M

- **V1 PASS:** Common facts 1 and 3 cite both exact versioned `size_of` pages
  and derive the zero-byte offset.
- **V2 PASS:** The 1.79 section cites exact `add` plus the exact 1.79 Reference
  dangling-pointer rule (including its zero-size/nonzero-literal alternatives),
  correctly excludes address-zero `null`, and says every call reaches UB.
- **V3 PASS:** The 1.80 section cites “always well-defined,” discharges both
  arithmetic clauses, and only returns the pointer.
- **V4 PASS:** The opening verdicts correctly partition and combine the set;
  the TCB expressly forbids compatibility inference across releases.
- **Hard error: none:** The regional proofs include the complete ZST
  derivation and null safe-call counterexample.

### N

- **V1 PASS:** `O1` cites exact versioned Reference array layout and computes
  the byte offset `1 * 0 = 0`.
- **V2 PASS:** `O2` cites exact 1.79 `null` and `add`, explains that null is
  neither in-bounds nor one-past an allocation, and calls invocation of the
  safe API a valid counterexample.
- **V3 PASS:** `O3` cites exact 1.80 `null` and `add`, applies the explicit zero
  exception, checks arithmetic, and notes the lack of dereference.
- **V4 PASS:** Its verdict table correctly gives both regions and combined
  `UNSOUND`; the TCB explicitly says 1.80 is not projected backward.
- **Hard error: none:** Every enumerated hard-error prerequisite is satisfied.

### O

- **V1 PASS:** The coverage section cites exact versioned Reference array
  layout and derives the zero byte offset.
- **V2 PASS:** `O-79` cites exact 1.79 `null`, pointer safety, and `add`, states
  why null fails the allocation conjunct, and identifies any safe call as UB.
- **V3 PASS:** `O-80` cites the exact 1.80 exception, checks all arithmetic,
  and notes that the returned raw pointer is not dereferenced.
- **V4 PASS:** The opening table correctly partitions both releases and gives
  the required union `UNSOUND`; the TCB contains no compatibility premise.
- **Hard error: none:** No wrong or unproved verdict, backward projection, or
  missing witness/derivation is present.

## Genuine rubric or authority ambiguities

None. The exact Rust 1.79.0 and 1.80.0 official documentation resolves the
only version-sensitive premise in the same way as the rubric, and all reports
provide enough version-matched authority and explicit reasoning to score every
atom without inference of an unstated material premise.
