# Mode N blind score

Interpretation used for N1: the two safe alias witnesses are (1) a live shared result from `get` overlapping a result from `get_mut`, and (2) two live results from repeated `get_mut` calls. Per `SCORER.md`, a code block is not required for each witness when the report gives equivalent explicit reasoning.

| Report | N1 | N2 | N3 | Hard error |
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

Overall: 45/45 atoms pass; 0 hard errors.

## Report-by-report evidence

### A

- **N1 — PASS:** Calls the exact snapshot `UNSOUND`, gives the safe `get`/`get_mut` shared-then-write witness, and expressly adds that repeated `get_mut` calls can produce two simultaneously usable `&'a mut T` values. It says the audit is fresh and does not inherit the design note.
- **N2 — PASS:** Identifies that both methods return `'a` “rather than” a reference tied to the receiver borrow, so the receiver borrow can end while the result lives. The raw pointer is only how both operations reach the same object, not the enabling defect.
- **N3 — PASS:** Changes both outputs to elided `&T`/`&mut T` and says the candidate is unimplemented, has “no verdict,” and requires a fresh exact-implementation audit.
- **Hard error — none:** The proposal is explicitly not certified.

### B

- **N1 — PASS:** Reports the snapshot `UNSOUND`, fully derives the safe shared/mutable overlap through `collide`, and explicitly states that two `get_mut` calls can likewise manufacture overlapping mutable references.
- **N2 — PASS:** Names the smallest false implication as assuming `PhantomData<&'a mut T>` makes the receiver borrow last for `'a`; it instead points to the explicit `'a` outputs and the receiver-elision rule.
- **N3 — PASS:** The direct-reference replacement gives both receiver-bound outputs and is labeled an “unimplemented proposal, not `PROVED`,” requiring fresh audit of the exact implementation.
- **Hard error — none:** Its discussion that the replacement blocks the demonstrated calls is conditional design reasoning, followed by an express refusal to certify it.

### C

- **N1 — PASS:** Gives a safe `get` followed by `get_mut` witness, derives the live shared-reference mutation, and expressly says repeated `get_mut` calls can return two simultaneously usable mutable references. It states the prior approval is not a premise.
- **N2 — PASS:** Says the results have struct lifetime `'a`, not the `self`-borrow lifetime; only elided outputs receive the receiver lifetime. It also says pointer/lifetime provenance alone does not serialize issued references.
- **N3 — PASS:** Repairs both signatures with an explicit receiver lifetime `'s` and labels the change “unimplemented; not audited,” with no verdict until a new snapshot is re-audited.
- **Hard error — none:** No status is granted to the proposal.

### D

- **N1 — PASS:** Declares the implemented snapshot `UNSOUND` and fully derives the safe shared/mutable witness. For the second witness it separately states that `get_mut` returns `'a`, its receiver borrow can end while its result remains live, and safe code can make another method call; together with the stated unchanged pointer and exclusivity obligation, this explicitly establishes capability reuse and the second conflicting alias route.
- **N2 — PASS:** Contrasts explicit `'a` results with receiver lifetimes and explains that `PhantomData` carries the original borrow but does not connect a method result to its receiver borrow.
- **N3 — PASS:** Changes both accessors to elided receiver-bound outputs and labels the proposal “UNIMPLEMENTED / UNPROVED,” requiring re-audit after the source change.
- **Hard error — none:** It expressly says blocking the witness is not proof of a nonexistent source snapshot.

### E

- **N1 — PASS:** Reports `UNSOUND`; its code derives two live mutable references from two safe `get_mut` calls, and the following paragraph explicitly derives the retained-`get` then `get_mut` shared/mutable conflict.
- **N2 — PASS:** Gives the effective `get_mut<'s>(&'s mut self) -> &'a mut T` relationship and says `'s` does not constrain the result. `PhantomData` is expressly rejected as method-call serialization.
- **N3 — PASS:** Both outputs become explicitly receiver-bound `'s` results, and the candidate is called “unimplemented and unaudited” with no `PROVED` status before fresh audit.
- **Hard error — none:** The report keeps the proposal’s status separate and uncertified.

### F

- **N1 — PASS:** Calls the snapshot `UNSOUND`, derives the safe mixed-alias witness through `clobber`, and its obligation ledger expressly says repeated `get_mut` calls can issue aliases.
- **N2 — PASS:** Expands both methods to receiver lifetime `'s` with output lifetime `'a` and explains that neither result carries `'s`; it explicitly says `PhantomData` does not serialize calls or tie outputs to receivers.
- **N3 — PASS:** Requires changing both outputs to `&T`/`&mut T` and marks the proposal “UNIMPLEMENTED and UNPROVED,” requiring a fresh audit.
- **Hard error — none:** The proposed source receives no certification.

### G

- **N1 — PASS:** Reports `UNSOUND`, fully derives the repeated-`get_mut` safe witness through `clash`, and explicitly derives the retained `get` followed by `get_mut` analogue.
- **N2 — PASS:** Identifies the distinct elided receiver lifetime versus explicit struct `'a`; says neither result keeps `View` borrowed and `PhantomData` does not change the signatures.
- **N3 — PASS:** Changes both outputs to receiver-elided lifetimes and labels both candidate designs “UNIMPLEMENTED / NOT AUDITED,” requiring fresh audit of the implementation.
- **Hard error — none:** No unimplemented candidate is certified.

### H

- **N1 — PASS:** Declares the fresh snapshot `UNSOUND` and fully derives the safe shared/mutable witness. It also derives the mutable capability-reuse defect: a returned reference outlives the authorizing receiver borrow, and an `'a`-long mutable result would require consuming `self` “instead of allowing reuse of the capability.” Alongside the stated single unchanged pointer consumer, that establishes the repeated-mutable route.
- **N2 — PASS:** Explicitly says both accessors return `'a`, not the receiver-borrow lifetime, and that only elided output lifetimes receive the receiver lifetime.
- **N3 — PASS:** Repairs both outputs with `&T`/`&mut T`; all alternatives are called unimplemented candidates with “no verdict,” and the chosen exact repair must receive a fresh audit.
- **Hard error — none:** Its proposal status is expressly uncertified.

### I

- **N1 — PASS:** Reports the exact implementation `UNSOUND`, gives and derives the safe repeated-`get_mut` witness, and explicitly states that mixed `get()` then `get_mut()` has the analogous shared/mutable conflict.
- **N2 — PASS:** Says the output uses impl lifetime `'a` rather than the receiver loan, so the first temporary receiver borrow ends independently of the returned reference.
- **N3 — PASS:** Both proposed representations have receiver-bound `&T`/`&mut T` outputs; the repair is `UNPROVED (unimplemented)` and must be implemented and freshly audited.
- **Hard error — none:** It explicitly says the repair does not alter the snapshot verdict and is not proved.

### J

- **N1 — PASS:** Calls the current snapshot `UNSOUND`, derives two safe `get_mut` calls yielding live aliases, and explicitly gives the analogous retained-`get` then `get_mut` route.
- **N2 — PASS:** States that neither result is tied to the temporary receiver borrow, so later safe access is permitted; the raw pointer is discussed only as the common address used after this lifetime escape.
- **N3 — PASS:** Changes both outputs to receiver-elided `&T`/`&mut T` and calls this only a conditional design argument; the implemented patch needs full fresh review.
- **Hard error — none:** The proposal heading says “not implemented; no verdict.”

### K

- **N1 — PASS:** Reports the implemented source `UNSOUND`, fully derives the repeated-mutable safe witness, and separately explains that a retained `get` result can conflict with a later `get_mut`; no design-note result is inherited.
- **N2 — PASS:** Says the explicit `'a` result and elided receiver lifetime are distinct and that the receiver loan can end while the returned reference stays live. It also rejects `PhantomData` as tracking method results.
- **N3 — PASS:** Requires changing both outputs to `&T`/`&mut T`; the designs are “unimplemented,” “not audited,” and not `PROVED`, with an exact-source re-audit required.
- **Hard error — none:** The proposal is explicitly denied certification.

### L

- **N1 — PASS:** Declares the fresh implementation `UNSOUND`, derives the safe shared/mutable witness, and explicitly says two successive `get_mut` calls can return coexisting aliases.
- **N2 — PASS:** States that explicit output `'a` is unrelated to the implicit receiver lifetime, allowing the receiver loan to end after the call; pointer origin and `PhantomData` do not imply exclusivity for escaped results.
- **N3 — PASS:** Repairs both outputs with receiver-elided lifetimes and labels the proposal “UNIMPLEMENTED / UNPROVED AS SOURCE,” requiring a fresh exact-source review.
- **Hard error — none:** It does not certify the proposal.

### M

- **N1 — PASS:** Reports `UNSOUND`, fully derives a safe function returning two `get_mut` results, and explicitly says `get` has the analogous escape permitting a later `get_mut` conflict.
- **N2 — PASS:** Gives the effective `get_mut<'s>(&'s mut self) -> &'a mut T` signature and explains that the receiver loan can end independently; private pointer origin and `PhantomData` do not serialize method results.
- **N3 — PASS:** Repairs both accessors with explicit receiver lifetime `'s` and labels the change an `UNPROVED` proposal requiring implementation and fresh review.
- **Hard error — none:** It expressly separates the proposal from the snapshot verdict.

### N

- **N1 — PASS:** Calls the exact implementation `UNSOUND`, fully derives the safe retained-shared plus mutable witness, and explicitly states that the same defect permits repeated `get_mut` calls.
- **N2 — PASS:** Writes the effective types with fresh receiver lifetimes and `'a` outputs, explaining that each receiver borrow can end while its result remains usable; `PhantomData` only carries the originating borrow.
- **N3 — PASS:** Repairs both outputs with receiver-elided lifetimes and calls the change proposed, unimplemented, and not `PROVED`; it requires auditing the implemented replacement.
- **Hard error — none:** No certification is assigned to the proposal.

### O

- **N1 — PASS:** Reports the fresh snapshot `UNSOUND`, derives two safe repeated-`get_mut` results using `UnsafeCell<u8>`, and explicitly says `get_mut` after `get` gives the shared/mutable route. [Rust 1.70’s versioned interior-mutability rule](https://doc.rust-lang.org/1.70.0/reference/interior-mutability.html) expressly says multiple `&mut UnsafeCell<T>` aliases are UB, so the chosen witness is material and valid even though the callee does not mutate them.
- **N2 — PASS:** Says both explicit `'a` results are not tied to their receiver loans; `PhantomData` models the original borrow but does not relate returned references to individual receiver loans.
- **N3 — PASS:** Changes both accessors to explicit receiver lifetime `'s` and marks the proposal `UNPROVED` until implemented and re-audited as a new exact artifact.
- **Hard error — none:** The proposed repair is explicitly not audited or certified.

## Authority check

The reports’ controlling Rust premise is supported by exact Rust 1.70 authority: the Reference’s [method lifetime-elision rule](https://doc.rust-lang.org/1.70.0/reference/lifetime-elision.html#lifetime-elision-in-functions) assigns the receiver lifetime only to **elided** output lifetimes, so the explicit `&'a T` and `&'a mut T` outputs remain tied to the impl lifetime rather than the call’s receiver loan. The Rust 1.70 [aliasing outline](https://doc.rust-lang.org/1.70.0/reference/behavior-considered-undefined.html#behavior-considered-undefined) states that a live shared reference excludes mutation of ordinary reachable data and a live mutable reference excludes other references/accesses; its liveness bounds make references passed to a function live for that call. Rust 1.70’s [interior-mutability text](https://doc.rust-lang.org/1.70.0/reference/interior-mutability.html) separately states that multiple `&mut UnsafeCell<T>` aliases are UB. Thus O’s variant and the ordinary integer variants establish the same required safe-alias proposition. Reports B and E mention later documentation only corroboratively; each derives the negative aggregate verdict from the in-range Rust 1.70 member, so no later text is back-projected.

## Rubric ambiguity

N1 says “both safe alias witnesses” without enumerating them or prescribing how fully each must be rendered. I used the two natural independent failures in this source—shared/mutable overlap and repeated mutable results—and applied `SCORER.md`’s instruction that equivalent explicit reasoning passes. D and H give one witness as code and the second as a receiver-lifetime/capability-reuse derivation rather than spelling out a second program; I counted that as explicit enough because both also establish that all accessor results use the unchanged pointer. Requiring two separate code blocks would be a formatting/length requirement contrary to `SCORER.md`. No other genuine rubric or authority ambiguity affects the scores.
