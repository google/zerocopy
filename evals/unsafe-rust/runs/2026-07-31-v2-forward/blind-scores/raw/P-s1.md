# Mode P blind score

## Atom table

| Report | P1 | P2 | P3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | PASS | None |
| G | PASS | PASS | PASS | None |
| H | PASS | PASS | PASS | None |
| I | PASS | PASS | PASS | None |
| J | PASS | PASS | PASS | None |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | PASS | PASS | PASS | None |

**Tally:** 45/45 atoms pass; 0 hard errors.

## Scoring basis

For P1, I accepted both treatments expressly permitted by the rubric: (a) an operational reading under which “readable for 16 bytes during the borrow” means that the initialized bytes can actually be read without pointer, aliasing, race, or lifetime UB for the relevant interval, and (b) a conditional proof that states the missing implication exactly and does not manufacture an `UNSOUND` verdict. The reports' material Rust premises are tied to versioned Rust 1.70 Reference or standard-library pages. Those premises are the unsafe-implementation obligation, array/`repr(C)`/`align` layout, `slice::as_ptr`, and the raw-read UB conditions ([unsafe traits](https://doc.rust-lang.org/1.70.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait), [layout](https://doc.rust-lang.org/1.70.0/reference/type-layout.html), [`slice::as_ptr`](https://doc.rust-lang.org/1.70.0/std/primitive.slice.html#method.as_ptr), [UB rules](https://doc.rust-lang.org/1.70.0/reference/behavior-considered-undefined.html), [`ptr::read`](https://doc.rust-lang.org/1.70.0/std/ptr/fn.read.html#safety)). Reports also appropriately qualify the open-ended portion of “1.70+” rather than silently projecting 1.70 documentation into the future.

## Report-by-report evidence

### A

- **P1 PASS:** It enumerates the full provider clauses, proves `ALIGN = 16`, offset-zero `[u8; 16]` layout, 16-byte alignment, non-nullness, and lifetime/readability for `Page`, then states C1/C2 as the exact operational propositions needed by `first`. It conditionally proves generic `first`, proves `first::<Page>`, and explicitly says the unresolved prose is not an `UNSOUND` finding. It also leaves post-1.70 propagation unresolved absent `RUST-COMPAT`.
- **P2 PASS:** It says the whole published contract remains binding because downstream implementations and unsafe consumers may use every clause despite the sole known in-tree consumer.
- **P3 PASS:** It limits 1.x work to equivalent proof documentation and a parallel additive capability while retaining `Block`; it assigns weakening, sealing, removal, and signature/bound changes to an authorized 2.0.
- **Hard error: none.** The redesign is expressly “preferred” future design, and A says implemented 2.0 source needs a fresh audit; it does not certify an absent artifact.

### B

- **P1 PASS:** It adopts an explicit ordinary operational reading—16 initialized bytes readable for the receiver-borrow interval—then proves every `Page` clause from layout and `as_ptr` and proves the one-byte dereference. It separately marks unbounded later-version coverage `UNPROVED` without a compatibility premise.
- **P2 PASS:** “Local search cannot close a public boundary” directly covers unknown generic consumers and unsafe implementations, including both weakening and strengthening directions.
- **P3 PASS:** It permits adjacent proofs/private one-byte factoring and an additive runway while preserving the old API; it places contract weakening, strengthening, sealing, and replacement in a major migration.
- **Hard error: none.** Its capability split is a migration design, and it explicitly requires adapters and new implementations to be re-audited after implementation.

### C

- **P1 PASS:** It identifies five contract obligations, proves all five for `Page`, and proves `first` under its stated safety-contract reading that the region is initialized and valid for shared reads during the borrow. It makes later-release coverage relative to an explicit `COMPAT-1` premise and otherwise unresolved.
- **P2 PASS:** It explicitly treats downstream implementations and consumers as quantified public sets and rejects repository search as a narrowing argument.
- **P3 PASS:** It distinguishes local proof/private-helper or parallel-API work from removing items, changing guarantees, sealing, making the trait safe, or changing `first`, all of which it reserves for 2.0.
- **Hard error: none.** C says no edit is authorized and presents the adapter/capability split only as a migration possibility; source or contract changes are review triggers, not certified current artifacts.

### D

- **P1 PASS:** It normalizes the obligation to 16 consecutive initialized readable bytes for the live receiver borrow, proves the complete `Page` representation/pointer argument, and proves that `first` immediately consumes only byte zero with `u8` alignment one. It explicitly leaves the unbounded version range unproved.
- **P2 PASS:** It states that repository search cannot authorize weakening because downstream consumers and implementations remain unknown.
- **P3 PASS:** Proof-only wording and an additive narrow API are separated from weakened extent/alignment, required-item, representation, or trait-bound changes requiring a major release.
- **Hard error: none.** The safe reference/value surfaces are labeled possible 2.0 choices whose selection and migration still require downstream requirements; no implementation verdict is issued.

### E

- **P1 PASS:** E proves the whole `Page` implementation, then gives the exact two missing implications for generic `first`—initialized `u8` readability and an interval covering the dereference. It reports `UNPROVED`, not `UNSOUND`, and gives the complete conditional derivation if those meanings are authoritative. It also keeps open-ended toolchain compatibility pending.
- **P2 PASS:** It says the known local consumer is not exhaustive and preserves obligations for unknown downstream consumers and implementers.
- **P3 PASS:** It allows reconstructed proofs, private/local factoring, and a parallel safe API while retaining the legacy surface; its explicit breaking list includes strengthening implementers as well as weakening consumers.
- **Hard error: none.** The proposed major-version split is not treated as implemented and E expressly requires a fresh audit of the implemented replacement.

### F

- **P1 PASS:** It proves every `Page` clause and makes `first` conditional on a precise meaning of readable: a live, initialized, provenance-permitted byte readable without an alias violation throughout the receiver borrow. It identifies that proposition as missing if the quoted meaning is not controlling and qualifies post-1.70 coverage.
- **P2 PASS:** It says repository-only use cannot narrow the public trait because downstream consumers and implementations are unknown.
- **P3 PASS:** It confines 1.x to local proof/lemma/documentation work and additive APIs, while classifying weakening, strengthening, sealing, item changes, and layout removal as 2.0 work.
- **Hard error: none.** Its safe method is described as a future endpoint and migration, not as an audited implementation.

### G

- **P1 PASS:** It proves `Page`'s constant, offset, alignment, live buffer, non-nullness, and full 16-byte region. For `first`, it operationally treats “readable” as a capability that makes the actual `*p` load permissible (“A3 consequently permits `*p`”), and it explicitly says a shorter interpretation of “during the borrow” would leave `first` `UNPROVED`. This is an allowed operational/conditional treatment, not a manufactured counterexample. Its future-version aggregate is also left unproved absent `COMPAT-1`.
- **P2 PASS:** It keeps the entire old contract because unknown consumers may use all bytes/alignment and unknown implementers may be broken by sealing or strengthening.
- **P3 PASS:** It separates local proof/documentation and independent APIs from sealing, narrowing, or removing the trait and gives an explicit 2.0 capability split.
- **Hard error: none.** G says the implemented 2.0 snapshot would require a fresh audit.

### H

- **P1 PASS:** Its obligation ledger proves `ALIGN`, address/alignment, all 16 initialized readable bytes for the borrow, and the immediate first-byte load. Its proposed wording explicitly covers initialization and validity, with the condition that any newly added temporal/provenance/interference duty would be a contract change. Later versions are relative to an identified compatibility premise.
- **P2 PASS:** It expressly rejects narrowing based on repository search and separately discusses consumer guarantees and implementer obligations.
- **P3 PASS:** It permits narrow local proof and additive APIs in 1.x, but assigns the shown safe-trait replacement and removal of old obligations to an explicitly authorized 2.0.
- **Hard error: none.** The code is presented as a 2.0 design sketch, and H says the capability choice requires downstream requirements; it does not give a proof verdict for a changed artifact.

### I

- **P1 PASS:** It supplies the clearest explicit operational reading: initialized non-atomic `u8` loads with no lifetime, aliasing, or race UB during the borrow. It then proves every `Page` clause and `first`'s exact byte-zero load. Its cutoff claim is explicitly relative to non-Reference `COMPAT-1`, and it says rejecting that premise leaves intervening versions unproved.
- **P2 PASS:** It says neither downstream consumers nor downstream implementations can be closed by repository search and preserves the full contract in 1.x.
- **P3 PASS:** It distinguishes proof comments/internal factoring/parallel APIs from weakening, sealing, bound changes, or layout removal requiring 2.0.
- **Hard error: none.** The proposed `FirstByte` migration is explicitly a new artifact requiring a fresh audit.

### J

- **P1 PASS:** It states the operational meaning of readable as 16 initialized bytes in a live allocation with reads permitted for the receiver borrow, proves full `Page`, and proves `first`; it also says a weaker intended meaning would make `first` `UNPROVED`. The through-cutoff claim is expressly relative to `TCB-COMPAT`, with future review required.
- **P2 PASS:** It covers both open-world directions: weakened provider guarantees break consumers, while strengthened duties break implementations.
- **P3 PASS:** Equivalent comments/private wrappers and opt-in APIs remain 1.x-compatible; narrowing, removing, making safe, or changing the bound is assigned to 2.0.
- **Hard error: none.** Both proposed designs are explicitly major-version designs requiring a fresh audit.

### K

- **P1 PASS:** It proves the complete strong `Page` contract, then precisely identifies why generic `first` is conditional: “valid for reads” and initialized typed data are distinct raw-read requirements, and the current word “readable” does not define initialization/race freedom or the interval. Its `MaybeUninit` discussion is a countermodel to an implication, not a claimed valid-contract UB witness, and it explicitly refuses `UNSOUND`. Version propagation is also pending.
- **P2 PASS:** It preserves all current clauses because public downstream consumers are unknown and notes that strengthening can invalidate downstream unsafe implementations.
- **P3 PASS:** It permits proof factoring and an additive separately named API while reserving strengthening, weakening, replacement, sealing, and layout changes for 2.0.
- **Hard error: none.** K labels the safe surface a recommendation/migration and states that no edit is authorized; it does not certify code that is absent.

### L

- **P1 PASS:** It proves the full `Page` layout and pointer contract, proves `first` under the expressly stated live/provenance/initialized-read meaning, and identifies that exact implication as a documentation gap if not already controlling. It qualifies the future toolchain range through `TCB-COMPAT`.
- **P2 PASS:** It directly says unknown downstream implementations owe the current theorem and unknown consumers may use every supplied guarantee.
- **P3 PASS:** It allows a derived internal one-byte lemma and equivalent proof comments, while placing extent/alignment reduction, strengthening, and unsafe-boundary changes behind a 2.0 migration.
- **Hard error: none.** Its alternative value/reference capabilities are choices to be made from actual requirements, not claimed implemented or audited results.

### M

- **P1 PASS:** It proves every `Page` conjunct and gives the smallest missing implication for `first`: byte zero is initialized and this non-atomic load is permitted throughout the interval. It conditionally closes the proof, does not call the current code unsound, and leaves later Rust versions pending `TCB-COMPAT-PENDING`.
- **P2 PASS:** It explicitly protects guarantees used by unknown consumers and obligations borne by unknown implementations.
- **P3 PASS:** It limits 1.x to proof/internal work and additive migration APIs with the old surface intact; weakening, strengthening, bound changes, and layout reconsideration are placed in 2.0.
- **Hard error: none.** The sample `FirstByte` code is a proposed major migration, and M expressly requires the implemented snapshot to receive a fresh audit.

### N

- **P1 PASS:** It explicitly expands readable into “live, allocated, and initialized for reads,” proves all `Page` obligations, and proves that `first` consumes only one live initialized byte with alignment one. It makes later-release coverage relative to `COMPAT-1` and says otherwise only 1.70 is proved.
- **P2 PASS:** It states that unknown consumers may rely on every clause and that stronger obligations may invalidate unknown unsafe implementations.
- **P3 PASS:** It allows local proof simplification and a parallel safe capability in 1.x while retaining legacy `Block` and `first`; contract/signature/removal changes require 2.0.
- **Hard error: none.** The staged replacement is a recommendation, and N requires the eventual 2.0 snapshot to be re-audited.

### O

- **P1 PASS:** It proves `Page`'s complete constant/layout/non-null/alignment/16-byte contract, then precisely states the missing live-allocation, initialized-`u8`, aliasing/race, and post-return interval proposition for `first`. It gives a conditional proof, explicitly says there is no valid-use UB witness, and qualifies open-ended version coverage.
- **P2 PASS:** It rejects local search as a bound on public consumers or implementations and preserves both sides of the 1.x contract.
- **P3 PASS:** It permits equivalent safety documentation and a parallel migration lane, but requires an authorized major release for weakening, stronger implementer duties, removal, or changing `first`'s bound.
- **Hard error: none.** The 2.0 split is a preferred future design and O explicitly calls for a fresh audit of resulting source.

## Genuine ambiguities

1. **Meaning and interval of “readable.”** The source does not formally define whether “readable for 16 bytes” entails initialization, provenance/access permission, alias/race freedom, or which receiver borrow survives the method return. The rubric expressly permits either an explicit operational meaning or an exact conditional proof. I therefore did not distinguish reports that prove under the operational meaning from A/E/K/M/O-style reports that leave the generic result conditional.
2. **Open-ended Rust `1.70+`.** Exact Rust 1.70 documentation cannot establish every future release. I treated an explicit unresolved compatibility premise or finite-cutoff qualification as the “appropriately leaves the proposition unresolved” option required by `SCORER.md`; I did not demand an impossible proof of future language versions.
3. **Design discussion versus hard-error certification.** Several reports call a by-value safe-trait redesign “safe” or show a sketch. I treated that as architectural reasoning, not certification, where the report places it in a future authorized migration and does not issue an artifact-level proof verdict. C's suggested adapter returning `&u8` would in particular need an aliasing/lifetime proof beyond a bare raw-read capability, but C does not implement or certify it and flags changed source as requiring review. On the rubric's stated hard-error wording, this is not a hard error.
