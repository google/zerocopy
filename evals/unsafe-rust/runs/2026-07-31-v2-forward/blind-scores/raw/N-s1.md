# Mode N blind score

Scoring convention: the two N1 witnesses are (i) a live shared result from
`get` overlapping a later mutable result from `get_mut`, and (ii) two live
mutable results from repeated `get_mut` calls. A concise explicit
“likewise/analogous” derivation passes when the report has already established
the unbound result lifetime, unchanged pointer, simultaneous liveness, and
controlling alias rule. I did not infer a witness from a merely generic phrase
such as “another/conflicting call.” Under `SCORER.md`, a material well-typedness
premise also needs applicable version-matched Rust authority in the report.

| Report | N1 | N2 | N3 | Hard error |
|---|---|---|---|---|
| A | FAIL | FAIL | FAIL | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | FAIL | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | PASS | None |
| G | PASS | PASS | PASS | None |
| H | FAIL | PASS | PASS | None |
| I | PASS | PASS | PASS | None |
| J | PASS | PASS | PASS | None |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | FAIL | FAIL | PASS | None |

## Report evidence

### A

- **N1 FAIL:** It reports the snapshot `UNSOUND`, gives the mixed witness
  (`shared = view.get(); *view.get_mut() = 1; ... *shared`), and explicitly
  adds that repeated `get_mut` calls can create two simultaneous mutable
  results. But the material premise making either second call well typed—the
  explicit `'a` output being independent of the elided receiver lifetime—is
  asserted without any version-matched lifetime-elision authority.
- **N2 FAIL:** “returns `&'a T` ... rather than ... tied to `&self`” identifies
  the right defect, but the report verifies raw-pointer construction,
  `PhantomData`, borrowing/UB, not the applicable Rust 1.70 method-lifetime
  rule.
- **N3 FAIL:** It changes both returns to `&T`/`&mut T` and says elision ties
  them to the receiver, but that material elision proposition is likewise
  unverified. It does correctly keep the candidate at “no verdict” pending a
  fresh exact-implementation audit.
- **Hard error: none.** The proposal is expressly “unimplemented” with “no
  verdict,” not certified.

### B

- **N1 PASS:** It reports `UNSOUND`, derives a safe live shared/mutable pair in
  `collide(read, write)`, and explicitly says two `get_mut` calls manufacture
  overlapping mutable references. Exact Rust 1.70 lifetime-elision and
  alias/immutability authorities support the derivation.
- **N2 PASS:** It names the smallest false implication: `PhantomData<&'a mut
  T>` does not make the `View` receiver borrow last for `'a`; explicit outputs
  bypass receiver-output elision.
- **N3 PASS:** Its direct-reference replacement gives both accessors
  receiver-bound elided outputs and is labeled “unimplemented proposal, not
  `PROVED`,” requiring fresh audit.
- **Hard error: none.** No proposal certification occurs.

### C

- **N1 PASS:** It gives and derives the safe `shared`/`unique` witness, then
  states repeated `get_mut` calls yield two simultaneously usable mutable
  references under the same uniqueness rule; verdict is `UNSOUND`.
- **N2 PASS:** It expressly contrasts struct `'a` outputs with the receiver
  lifetime and cites Rust 1.70 lifetime elision.
- **N3 PASS:** Both proposed signatures explicitly use `<'s>(&'s self) ->
  &'s T` / `<'s>(&'s mut self) -> &'s mut T`; the proposal has “no verdict”
  until implemented and re-audited.
- **Hard error: none.** The repair is expressly unaudited.

### D

- **N1 FAIL:** It reports `UNSOUND` and fully derives the mixed
  shared/mutable witness. It never identifies the second required witness—two
  results of repeated `get_mut`. Saying only that safe code can call “another
  method” while a mutable result lives does not establish that distinct alias
  pattern without inference.
- **N2 PASS:** It identifies both explicit `'a` outputs as escaping their
  receiver borrows and verifies the receiver-output rule against Rust 1.70.
- **N3 PASS:** It changes both outputs to receiver-elided lifetimes and marks
  the patch `UNIMPLEMENTED / UNPROVED`, requiring re-audit.
- **Hard error: none.** The proposal is not certified.

### E

- **N1 PASS:** It fully derives two live mutable aliases using two `get_mut`
  calls and `touch(first, second)`, and separately explains retaining `get()`
  across later `get_mut`; current verdict is `UNSOUND` with exact Rust 1.70
  authority.
- **N2 PASS:** It gives the effective type `get_mut<'s>(&'s mut self) -> &'a
  mut T` and explains that `'s` does not constrain the result.
- **N3 PASS:** Both proposed outputs explicitly use `'s`, and the candidate is
  “unimplemented and unaudited” pending fresh audit.
- **Hard error: none.** No certification.

### F

- **N1 PASS:** The safe `shared`/`unique` call to `clobber` is fully derived;
  the obligation ledger also explicitly says repeated calls issue mutable
  aliases. It concludes current `UNSOUND` using exact Rust 1.70 rules.
- **N2 PASS:** It expands both effective signatures with fresh receiver
  lifetime `'s` and explains why explicit `'a` outputs do not carry it.
- **N3 PASS:** It changes both returns to `&T`/`&mut T`, explains receiver
  elision, and calls the proposal `UNIMPLEMENTED and UNPROVED` pending fresh
  audit.
- **Hard error: none.** No proposal certification.

### G

- **N1 PASS:** It derives repeated `get_mut` aliases through `clash(a, b)` and
  separately states the analogous retained-`get`/later-`get_mut` composition;
  verdict is `UNSOUND`.
- **N2 PASS:** It cites Rust 1.70 elision and states that explicit struct `'a`
  outputs, not `PhantomData` or raw-pointer presence alone, detach the results.
- **N3 PASS:** It changes both output lifetimes and labels both repair variants
  `UNIMPLEMENTED / NOT AUDITED`, requiring a fresh implementation audit.
- **Hard error: none.** No certification.

### H

- **N1 FAIL:** It reports `UNSOUND` and fully derives the mixed
  shared/mutable witness in `conflict`. It does not identify or derive two
  simultaneous results of repeated `get_mut`; generic statements about a
  “conflicting call” appear only in repair discussion.
- **N2 PASS:** It explicitly says both outputs use struct `'a`, not receiver
  lifetime, and verifies the Rust 1.70 receiver-elision rule.
- **N3 PASS:** Both accessors receive receiver-bound elided outputs, and the
  candidates receive “no verdict” until a fresh audit.
- **Hard error: none.** The proposal remains uncertified.

### I

- **N1 PASS:** It fully derives two mutable aliases with repeated `get_mut`
  and `use_both(first, second)`, then explicitly identifies the analogous
  mixed `get()`/`get_mut()` conflict; verdict is `UNSOUND`.
- **N2 PASS:** It distinguishes the elided receiver lifetime from explicit
  impl `'a` and cites exact Rust 1.70 lifetime rules.
- **N3 PASS:** Both the preferred direct-reference design and the retained-raw
  alternative give receiver-bound outputs; either must be implemented and
  freshly audited before `PROVED`.
- **Hard error: none.** The repair is explicitly unproved.

### J

- **N1 PASS:** It derives two live mutable aliases in `collide(first,
  second)` and expressly gives the analogous retained-`get` then `get_mut`
  route; the current snapshot is `UNSOUND`.
- **N2 PASS:** Its obligation analysis attributes both failures to outputs not
  tied to temporary receiver borrows; the exact Rust 1.70 elision rule is
  linked in the repair analysis.
- **N3 PASS:** Both outputs change to receiver-elided forms, with the result
  described only as a conditional design requiring a fresh exact audit.
- **Hard error: none.** No implemented-patch verdict is claimed.

### K

- **N1 PASS:** It fully derives repeated-`get_mut` aliases through
  `write_both`; its `get` obligation separately says a retained shared result
  can conflict with later `get_mut`. The same-pointer invariant, liveness, and
  Rust 1.70 alias rule are stated; verdict is `UNSOUND`.
- **N2 PASS:** It identifies the elided receiver lifetime versus explicit
  result `'a` as the enabling difference, and includes the exact Rust 1.70
  receiver-elision authority.
- **N3 PASS:** Both signatures are changed; the report says these are
  “unimplemented candidate designs, not audited or PROVED artifacts” and
  demands exact re-audit.
- **Hard error: none.** No certification.

### L

- **N1 PASS:** It derives the live shared/mutable witness and explicitly adds
  that two successive `get_mut` calls yield coexisting aliases to the same
  `T`; current status is `UNSOUND` with exact Rust 1.70 authority.
- **N2 PASS:** It identifies the explicit `'a` results as unrelated to the
  implicit receiver lifetime, not the raw pointer alone.
- **N3 PASS:** Both proposed outputs are receiver-bound under the cited elision
  rule, and the proposal is `UNIMPLEMENTED / UNPROVED AS SOURCE` pending fresh
  review.
- **Hard error: none.** No certification.

### M

- **N1 PASS:** It fully derives two mutable aliases returned by `duplicate`
  and explicitly identifies retained `get` followed by later `get_mut` as the
  second safe route; verdict is `UNSOUND`.
- **N2 PASS:** It writes the effective `get_mut<'s>(&'s mut self) -> &'a mut
  T` type and verifies why explicit `'a` is not rewritten by receiver elision.
- **N3 PASS:** Both outputs explicitly use receiver `'s`; the change is
  `UNPROVED`, unimplemented, and requires fresh review.
- **Hard error: none.** No certification.

### N

- **N1 PASS:** It fully derives the retained-shared/later-mutable witness and
  explicitly states that the same retained-capability defect permits repeated
  `get_mut`; the effective types, unchanged pointer, liveness, and exact Rust
  1.70 alias rule establish both routes. Verdict is `UNSOUND`.
- **N2 PASS:** It displays both effective signatures with independent
  receiver lifetimes and `'a` outputs, identifying the correct cause.
- **N3 PASS:** Both outputs become receiver-elided; the proposal is expressly
  “proposed and unimplemented; not `PROVED`” pending implementation audit.
- **Hard error: none.** No certification.

### O

- **N1 FAIL:** It reports `UNSOUND`, explicitly identifies both repeated
  `get_mut` and mixed `get`/`get_mut` routes, and gives an exact Rust 1.70
  `UnsafeCell` alias witness. But it provides no version-matched authority for
  the material premise that an explicit impl-`'a` output is independent of the
  elided receiver loan, which is what makes the second call well typed.
- **N2 FAIL:** The diagnosis is substantively correct—“return the stored
  lifetime `'a`, not the lifetime of their receiver borrow”—but the applicable
  Rust 1.70 lifetime/elision rule is not verified anywhere in the report.
- **N3 PASS:** Unlike A, O spells both receiver relationships explicitly as
  `<'s>(&'s self) -> &'s T` and `<'s>(&'s mut self) -> &'s mut T`, so the
  required binding is present without an elision premise. It labels the
  proposal `UNPROVED` until implemented and re-audited.
- **Hard error: none.** The proposal is explicitly uncertified.

## Genuine ambiguities

1. **Granularity of “derive both witnesses.”** The rubric does not say whether
   each witness needs its own complete code block and repeated UB proof. I
   applied the proposition-not-format rule: explicit “likewise/analogous”
   identification of the second alias pattern passes when the preceding
   lifetime/same-pointer/liveness argument also covers it. This is why A, B,
   C, F, G, I–O are not failed merely for giving one code block. D and H do
   not name the duplicate-mutable pattern, so I did not infer it.
2. **What counts as report-side verification.** The actual Rust 1.70
   [lifetime-elision rule](https://doc.rust-lang.org/1.70.0/reference/lifetime-elision.html#lifetime-elision-in-functions)
   supports A's and O's substantive diagnosis, but `SCORER.md` says the
   *report* must verify a material, version-matched premise. I therefore did
   not cure their missing authority externally. Reports that include the
   exact rule later (for example in repair discussion) were treated as having
   verified it; the instructions do not require the citation to be adjacent.
3. **A's N3 versus O's N3.** A relies on undocumented lifetime elision to make
   its proposed `-> &T` / `-> &mut T` receiver-bound, so N3 fails under the
   authority rule. O explicitly writes the same named `'s` on receiver and
   output, directly satisfying the signature relation, so N3 passes even
   though O does not establish N2's causal language premise with authority.
   Treating an explicit, correct lifetime claim as self-verifying would instead
   make A/O N1 and N2 (and A N3) pass; the stricter reading follows the
   scorer's express verification sentence.

