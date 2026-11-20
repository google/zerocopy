# Borrow-checker relaxations in Rust (non-lexical lifetimes, two-phase autoref borrows, precise closure capture) versus Swift's static and dynamic exclusivity enforcement: admitted programs, residual rejections, costs, and soundness record

## Summary

- **One invariant, three narrow relaxations.** Rust and Swift enforce the same core rule: two accesses to the same storage may not overlap unless both are reads. Rust relaxed *when an access is considered to overlap* three times. Each time it adopted the narrowest rule that admitted the motivating programs:
  1. **Non-lexical lifetimes (NLL, RFC 2094).** A loan lasts only where the reference is live, and assigning to a path kills loans of paths that extend it.
  2. **Two-phase borrows (RFC 2025).** Selected `&mut` borrows start as *reservations* that act like shared borrows and become mutable borrows at their single use. rustc creates them only for compiler-inserted autoref and reborrow adjustments and for overloaded compound-assignment operands. An explicit `&mut v` written as a call argument was not treated as two-phase on any toolchain tested (probe `p05`).
  3. **Precise closure capture (RFC 2229).** Closures capture places, not whole variables. The capture is truncated at raw-pointer derefs, union fields, `repr(packed)` fields, indexing, moves through references, and moves out of `Drop` types. The behavior applies only from edition 2021 and comes with an allow-by-default migration lint.
- **Residual rejections are concrete and probe-confirmed.** These programs are still rejected:
  - NLL problem case #3 (conditional return of a borrow) on stable rustc 1.100.0 and with `-Zpolonius=off`. It **is accepted by nightly rustc 1.102.0 (2026-11-11) by default**, because nightly builds now default to the in-tree Polonius analysis.
  - `v[0].push_str(&format!("{}", v.len()))`, because `IndexMut` activates the borrow first.
  - `x.increment(x.increment(1))`.
  - Manual desugaring with `let tmp = &mut v`.
  - Field-disjoint use through `&mut self` methods.
  - Closure use of `s.arr[1]` while `s.arr[0]` is borrowed.
- **The assignment design point.** rustc (NLL) accepts `let r = &x; x = *r + 1;`. MIR evaluates `*r` into a temporary before the write, and the loan is dead at the write. The program is rejected if `r` is used afterwards. The pre-NLL checker (rustc 1.35.0, edition 2015) rejected it. A checker that invalidates all loans of `x` before it evaluates the right-hand side would also reject it.
- **Measured ecosystem costs (Crater):**

  | Change | Regressed / total | Notes |
  |---|---|---|
  | NLL migrate-mode warnings become errors, edition 2018 (PR #63565) | 1,622 / 70,078 | Mostly two old crate versions with large reverse-dependency fan-out |
  | Two-phase reservation restriction (PR #58739) | 3 crates.io root regressions + 13 GitHub-only crates | |
  | Migrate-mode removal (PR #95565) | 454 / 223,389 | 160 of 179 root regressions had already been warned |
  | Polonius alpha on nightly (PR #159343) | 2 / 1,026,208 | 18 fixed |

  The Polonius try build cost +3.0% mean instruction count on 88 primary benchmarks (range 0.3–15.3%).
- **Soundness record.** On 2026-11-20, two open `I-unsound` issues concern two-phase borrows: rust-lang/rust#160598 (a `break` in a method argument defeats the dominator test in `is_active`) and #164163 (reassigning the receiver's base inside an argument). Both reproducers compile on nightly, stable 1.100.0 and, for the variants that parse, 1.61.0 and 1.56.0. The reservation-versus-existing-shared-borrow pattern was warned against from 2019 until rustc 1.62.0 and then allowed. Stacked Borrows accommodates it by treating two-phase borrows "like (tagged) raw pointers", which forgoes alias-based optimization on them.
- **Swift places the boundary differently.** Enforcement is static for locals, `inout` parameters and struct properties that are not captured by escaping closures. It is dynamic (runtime `swift_beginAccess`/`swift_endAccess` over a thread-local list) for class properties, globals, static properties and escaping captures. Swift 5 enabled the dynamic checks in release builds. Its own enabling PR measured 11 of 656 microbenchmarks regressing by more than 10%, the worst being `ClassArrayGetter2` at 0.11× (+840%). An `inout` access starts only after argument evaluation, so `x += x` and `array[0] += array[1]` are legal by definition, with no two-phase machinery. All Swift entries rest on documentation and source; no Swift compiler was run.

## Applicability

This report covers two things:

1. The Rust language and compiler rules that decide whether overlapping borrows are accepted: RFC 2094, RFC 2025, RFC 2229, and the edition-2021 migration.
2. Swift's exclusivity rules (SE-0176 and the Ownership Manifesto) and their enforcement implementation.

The subjects in `REPORT.json` relate as follows:

- **Design records** (`rust-lang/rfcs`, `swiftlang/swift-evolution`, `swiftlang/swift` `docs/OwnershipManifesto.md`, `rust-lang/edition-guide`, the Swift.org post in `swiftlang/swift-org-website`) state the intended rules. They are cited as normative or documentation evidence.
- **Implementation source.** `rust-lang/rust` at `c7d5ba59` (committed 2026-11-20) and `swiftlang/swift` at `64060457` show how the rules are realized. Every Rust `file:line` below refers to `c7d5ba59` unless stated otherwise.
- **Toolchains** (rustc nightly `3ef0c22cd`, stable 1.100.0, 1.61.0, 1.56.0, 1.35.0) are the systems actually executed. Probe outcomes describe those builds on x86-64 Linux, not the source commit. The nightly toolchain commit is 2,447 commits behind `c7d5ba59` (GitHub compare API). In the quoted regions, the files differ only cosmetically:
  - `path_utils.rs` is identical.
  - `borrow_set.rs` differs only by one `&` removal.
  - `upvar.rs` restructures `truncate_place_to_len_and_update_capture_kind` with the same logic.
  - The `Polonius` default code in `rustc_session/src/config.rs` is unchanged.
  - `adjustment.rs` adds an unrelated `AutoBorrow::mutability` helper.
- **`rust-lang/crater` at `abaa9494`** documents the tool that produced the regression counts. The counts themselves come from bot comments on rust-lang/rust pull requests (cited by URL). They describe the crate sets and toolchains of those experiments, not the Crater revision pinned here.

Configuration that matters:

- **Edition.** Precise capture applies only when the closure's span is edition 2021 or later (`upvar.rs:2749-2755`).
- **NLL rollout by release** (`RELEASES.md`):
  - Edition 2015 used the pre-NLL checker up to rustc 1.35. NLL was enabled on edition 2015 in 1.36 (line 8777).
  - Edition 2018 used NLL from 1.31. Until 1.38, errors that the old checker would have accepted were downgraded to warnings ("migrate" mode).
  - Those warnings became errors in 1.39 for edition 2018 (line 8503) and in 1.40 for edition 2015 (line 8370).
  - Migrate mode was removed in 1.63 (line 4847).
- **Channel.** Nightly builds default to `-Zpolonius=next`. Stable builds default to `off` (§2.4). Statements about "NLL" therefore mean stable or `-Zpolonius=off` unless noted otherwise.
- **Lints.** `rust_2021_incompatible_closure_captures` is allow-by-default and fires only when requested, for example by `-W rust-2021-incompatible-closure-captures` or `cargo fix --edition`.

Swift claims rest only on the pinned documentation and source. They are not confirmed by executing a Swift compiler.

## Findings

### 1. The shared invariant and what each Rust relaxation changes

| | Pre-NLL checker (edition 2015, ≤1.35) | NLL (RFC 2094) | Two-phase (RFC 2025) | Precise capture (RFC 2229) |
|---|---|---|---|---|
| What is relaxed | — | Duration of a loan | Start of a `&mut` loan's exclusivity | Footprint of a closure's capture |
| New rule | Loan region is a lexical scope; a reference stored in a variable keeps its loan for that variable's whole scope (RFC 2094 lines 115–117) | Loan region = points where the reference may later be used; assigning to `lv` kills loans of paths having `lv` as prefix | Reservation acts as a shared borrow until the unique use of the temporary; an extra conflict check runs at activation | Capture the minimal place; truncate at operations that would need `unsafe`, calls, indexing, or illegal moves |
| Where it applies | — | All borrows | Compiler-inserted autoref/reborrow and overloaded compound-assignment operands only | Closures whose span is edition ≥ 2021 |
| Checker change | — | New region inference and dataflow | New borrow kind, activation bookkeeping, two access kinds, a dominator test | None to the borrow checker; changes closure lowering and adds a migration analysis |

Basis: normative (the three RFCs) + source (§§2–4).

### 2. Non-lexical lifetimes (RFC 2094)

**Programs the RFC targets** (`text/2094-nll.md`):

| Case | Program | Fix in the RFC |
|---|---|---|
| #1 (line 97) | Reference stored in a variable then dead: `let slice = &mut data[..]; capitalize(slice); data.push('d');` | Liveness-based regions |
| #2 (line 143) | Borrow used in one `match` arm, mutation in another (`map.get_mut` / `map.insert`) | Liveness-based regions |
| #3 (line 201) | Borrow *returned* on one path, mutation on the other (`get_default`) | Layer 4: regions include `end('r)` "end regions" for named lifetimes (lines 1468–1472). Line 1514 says: "NB: This part of the prototype is partially implemented." |
| #4 (line 336) | Reassigning a `&mut` variable whose referent is borrowed (`list = n` while `&mut list.value` is held) | Transfer function rule (lines 1566–1567): "if this is an assignment `lv = <rvalue>`, then any loan for some path P of which `lv` is a prefix is killed" |

Safety argument (lines 431–434): "the lifetime of a reference lasts only for those portions of the function in which the reference may later be used (where the reference is **live**)". A reference that will never be used again cannot observe a conflicting write.

The RFC's appendix lists errors it **will not fix** (lines 2102–2165):

- Closure desugaring capturing whole variables. RFC 2229 later fixed this.
- "Disjoint fields across functions". Still rejected; see probe `p21`.
- Self-referential structs.

**Adopted outcome for case #3.** rustc's own regression test states that the case was deferred. `tests/ui/nll/polonius/nll-problem-case-3-issue-21906.rs:3-5` reads: "the NLL problem case 3 that was deferred from the implementation of the NLL RFC, and left to be implemented by polonius". Its revisions encode the current split: `[nll] known-bug: #21906` with `-Z polonius=off`, and `check-pass` for `-Z polonius=next` and `-Z polonius=legacy` (lines 9–15). The directory holds 10 such `nll-problem-case-3-issue-*.rs` tests at `c7d5ba59`. Basis: source.

**Probe results** (`support/results/probe_matrix.tsv`). Here `rej(Exxxx)` means rejected with that error code.

| Probe | 1.35.0 e2015 (pre-NLL) | 1.35.0 e2018 (NLL migrate) | stable 1.100.0 e2021 | nightly default e2021 | nightly `-Zpolonius=off` |
|---|---|---|---|---|---|
| `p09` case #1 | rej (E0499 ×3) | accept | accept | accept | accept |
| `p10` case #2 | rej (E0499) | accept | accept | accept | accept |
| `p11` case #3 | rej (E0499 ×2) | rej | rej (E0499 ×2) | **accept** | rej (E0499 ×2) |
| `p12` case #4 | rej (E0499 ×2, E0506) | accept | accept | accept | accept |

Basis: execution.

**2.4 Polonius on nightly.** `compiler/rustc_session/src/config.rs:3856-3857` defines the default:

```rust
pub(crate) const DEFAULT: Self =
    if option_env!("CFG_DEFAULT_POLONIUS_NEXT").is_some() { Self::Next } else { Self::Off };
```

The nightly toolchain's `rustc -Z help` prints `polonius=val -- enable polonius-based borrow-checker (default: next)`. Do not confuse this with the parse error text at `options.rs:981-982`, "either no value or one of `legacy` (the default), `off`, or `next`". That message describes what a bare `-Zpolonius` means, not the unflagged default.

The enabling change was rust-lang/rust#159343, "Enable polonius alpha on nightly", merged 2026-08-05. Its record shows:

- Crater: "2 regressed and 18 fixed (1026208 total)".
- Try-build perf: instruction count regressions on 88 primary benchmarks, mean 3.0%, range [0.3%, 15.3%]. Max RSS +4.2% on 6 primary benchmarks. Bootstrap time 487.651 s → 492.438 s (+0.98%).

Basis: source + execution + documentation (PR record).

### 3. Two-phase borrows (RFC 2025)

**3.1 Rule (normative).**

- Lines 12–17: "select `&mut` borrows are modified so that they begin with a 'reservation' phase and can later be 'activated' into a full mutable borrow. During the reservation phase, reads and shared borrows of the borrowed data are permitted (but not mutation)".
- Lines 19–20: "only used when desugaring method calls; this is intended as a conservative step."
- Lines 285–289: "reservations act just as a shared borrow does".
- Lines 291–293 add one check: "At the point `Q` where a mutable borrow is activated, we must check that there are no active borrows or reservations in scope (other than the reservation being upgraded)."

The RFC explicitly leaves two cases rejected:

- `v[0].push_str(&format!("{}", v.len()))` (lines 195–202), because "the mutable borrow of `v` is 'activated' by the indexing".
- `x.increment(x.increment(1))` (lines 528–532).

It also declines to make **all** `&mut` borrows two-phase (lines 572–578). The stated reason is that `let x = &mut vec;` and `let x; x = &mut vec;` would behave differently, a distinction that "cannot be explained except by examining the desugarings into MIR" (lines 591–592).

**3.2 Where rustc creates them (source + execution).**

- `compiler/rustc_middle/src/ty/adjustment.rs:152-163` documents `AllowTwoPhase { Yes, No }`. It limits two-phase borrows to "`x.some_method()` syntax, where some_method takes `&mut self`", "`Foo::some_method(&mut x, ...)` syntax", and "binary assignment operators (`+=`, `-=`, `*=`, etc.)". The reason given is that "dataflow can't handle the general case where there is more than one use of a mutable borrow".
- `compiler/rustc_middle/src/mir/syntax.rs:200-201` adds the MIR borrow kind: "`TwoPhaseBorrow`: This borrow arose from method-call auto-ref."

Probes show that the second bullet of the doc comment holds only for *implicit* reborrows:

| Probe | Code | Result |
|---|---|---|
| `p05` | `Vec::push(&mut v, v.len())` (explicit `&mut` argument) | Rejected (E0502) on every toolchain tested |
| `p27` | `fn f(v: &mut Vec<usize>) { Vec::push(v, v.len()); }` | Accepted from 1.35.0 edition 2018 onward; rejected (E0502) by 1.35.0 edition 2015, which has no two-phase borrows |
| `p06` | `w += w.len()` with an overloaded `AddAssign` | Accepted |
| `p01` | `vec.push(vec.len())` | Accepted from edition 2018 on 1.35.0 and on all later toolchains; rejected (E0502) by 1.35.0 edition 2015 |

`p27` being accepted is consistent with the implicit reborrow adjustment being two-phase (derived).

**3.3 Checker concepts in the implementation (source).**

- `compiler/rustc_borrowck/src/borrow_set.rs:131-135`: `enum TwoPhaseActivation { NotTwoPhase, NotActivated, ActivatedAt(Location) }`.
- `BorrowData` (lines 138–152) records `reserve_location` and `activation_location`. `BorrowSet::activation_map` (line 40) maps locations to activated borrows.
- `GatherBorrows::pending_activations` (lines 241–249) records `TEMP = &foo`. A two-phase borrow must assign to a local, otherwise `span_bug!` fires (lines 453–459). A second use of the temporary also triggers `span_bug!` (lines 546–555). This encodes the RFC's "the temporary `tmp` will only be used once".
- `compiler/rustc_borrowck/src/lib.rs:1089-1092` adds the access kinds `Reservation(WriteKind)`, "treated like a Read", and `Activation(WriteKind, BorrowIndex)`, "treated like a write". A two-phase `&mut` is checked as `(Deep, Reservation(wk))` (lines 1490–1496). Reads during a reservation pass (lines 1324–1328): "Reading from mere reservations of mutable-borrows is OK."
- `compiler/rustc_borrowck/src/path_utils.rs:60-120`, `is_active`, decides whether a location lies between reservation R and activation A using dominators only. Lines 88–93 state its assumptions:

  ```rust
  // Note that we assume that:
  // - the reservation R dominates the activation A
  // - the activation A post-dominates the reservation R (ignoring unwinding edges).
  ```

**3.4 Reservation versus a pre-existing shared borrow (history).** The pattern is `let shared = &v; v.push(shared.len());`.

- NLL accepted it at stabilization.
- PR rust-lang/rust#58739, "More restrictive 2 phase borrows – take 2" (merged 2019-04-07), added the `mutable_borrow_reservation_conflict` lint. The Crater run that informed it reported "3 root regressions of crates.io crates" and "13 github only crates" (https://github.com/rust-lang/rust/pull/58739#issuecomment-470230949).
- Tracking issue #59159 called the pattern a "known bug" at NLL stabilization.
- Probes show the warning on 1.35.0 (edition 2018) and 1.61.0 ("this borrowing pattern was not meant to be accepted, and may become a hard error in the future").
- PR #96268 (merged 2022-05-06; `RELEASES.md:5060`, version 1.62.0) removed the lint and allowed the pattern: "This was the only breaking issue with the NLL stabilization PR."
- In that PR, the Stacked Borrows author explained the semantic price: "any aliasing model has no issue with 2-phase-borrows if it just entirely gives up on doing anything interesting with them, and treats them like (tagged) raw pointers ... This is exactly what I ended up doing with Stacked Borrows" (https://github.com/rust-lang/rust/pull/96268#issuecomment-1105261537).
- The current checker carries a tombstone comment at `lib.rs:1313-1317`: `(Reservation(_), BorrowKind::Fake(_) | BorrowKind::Shared) => { // This used to be a future compatibility warning (to be disallowed on NLL). See rust-lang/rust#56254`.
- `compiler/rustc_lint/src/lib.rs:581-585` registers the lint as removed with "now allowed, see issue #59159".
- Probe `p07` is accepted silently on stable 1.100.0 and nightly.

Basis: source + execution + documentation (PR records).

**3.5 Open soundness reports (execution + source).**

| Issue | Shape | nightly default | nightly `-Zpolonius=off` | stable 1.100.0 | 1.61.0 | 1.56.0 |
|---|---|---|---|---|---|---|
| #160598 (`s02`, labeled block) | `r = Some(v.insert(match true { false => break 'b, true => 1 }));` then `let s = &v;` while `r` is live | compiles | compiles | compiles | parse error (labeled blocks unstable) | not run |
| #160598 loop variant (`s03`) | same shape with `loop { ... break ... }` | compiles | not run | compiles | compiles | compiles |
| #164163 (`s01`) | `p.push({ s = &p[0]; p = &mut b; 0 });`, then reads `*s` after `a` may have reallocated | compiles | compiles | compiles | compiles | compiles |

Running the `s02` binary built by nightly printed `Some(1) Some(2)`: a live `&Option<i32>` observed a write made through another reference. #160598 attributes the bug to `is_active` and the false post-dominance assumption quoted in §3.3. A `break` inside an argument creates an edge from between R and A to a join point. There, `succ(R)` dominates but A does not, so `is_active` returns `false` ("mere reservation") although the activated borrow is live on the fall-through path. Both issues were open on 2026-11-20. #164163 carries `P-high`. A comment on #164163 reports that a bisection on edition 2015 points to nightly-2019-04-23, the nightly after PR #59114 (merged 2019-04-22) enabled NLL and two-phase borrows on edition 2015. That bisection was not reproduced here.

### 4. Precise closure capture (RFC 2229)

**4.1 Rule and argument (normative).**

- `text/2229-capture-disjoint-fields.md:9-10`: "closure capturing should be minimal rather than maximal".
- Lines 106–107: "This RFC does not propose any changes to the borrow checker. Instead, the MIR generation for closures should be altered to produce the minimal capture."
- Lines 132–137: a capture is minimal when making it more precise would require "a call to an impure function" or "an illegal move".
- Lines 145–147: "*all* functions are considered impure (including to overloaded deref implementations)" and "all indexing is considered impure".

The safety argument is that capture expressions are subsets of the body, so only lifetimes change. The acknowledged breakage is at lines 155–157: "the drop order of uncaptured data can be altered."

**4.2 Implementation truncation rules (source, `compiler/rustc_hir_typeck/src/upvar.rs`).**

| Rule | Location | Quote or effect |
|---|---|---|
| Raw pointers and unions | `restrict_precision_for_unsafe`, lines 2339–2369 | "No projections are applied to raw pointers, since these require unsafe blocks." "No projections are applied on top of Union ADTs" |
| Indexing | `restrict_capture_precision`, lines 2392–2396 | "Arrays are completely captured, so we drop Index and Subslice projections" |
| `repr(packed)` | `restrict_repr_packed_field_ref_capture`, lines 2120–2150 | "We stop here regardless of field alignment" |
| Moves out of `Drop` types | `restrict_precision_for_drop_types`, lines 2315–2336 | "Rust doesn't permit moving fields out of a type that implements drop" |
| `move` closures | `adjust_for_move_closure`, lines 2406–2419 | Truncate at the first `Deref`, capture by value |
| Non-move by-value captures | `adjust_for_non_move_closure`, lines 2436–2467 | Truncate at the first `Deref` |
| Shared-reference optimization | `truncate_capture_for_optimization`, lines 2700–2747 | Truncates after the rightmost deref of a `&T` |
| Edition gate | `enable_precise_capture`, lines 2749–2755 | `span.at_least_rust_2021()` |

The internal `#[rustc_capture_analysis]` attribute (probe `p26`, nightly, edition 2021) shows the effect for a closure body using `s.inner.x`, `*s.raw`, `s.boxed.y`, `s.arr[1]` and `s.shr.x`:

| Place used | First-pass capture | Minimal capture |
|---|---|---|
| `s.inner.x` | `s[(0,0),(0,0)]` | `s.inner.x` (unchanged) |
| `*s.raw` (raw pointer) | `s[(1,0),Deref]` | `s.raw` (truncated before the deref) |
| `s.boxed.y` (through `Box`) | `s[(2,0),Deref,(1,0)]` | unchanged (precise through `Box`) |
| `s.arr[1]` | `s[(3,0)]` | `s.arr` (index dropped) |
| `s.shr.x` (through `&'static Inner`) | `s[(4,0),Deref,(0,0)]` | `s[(4,0),Deref]` (field after a shared-ref deref dropped) |

With `--edition 2018`, the minimal capture is `s[]`, the whole variable. Basis: execution.

**4.3 Migration (normative + source + execution).**

- The edition guide (`src/rust-2021/disjoint-capture-in-closures.md:5-7`) says `|| a.x + 1` "now captures only `a.x`" and that this "can cause things to be dropped at different times or affect whether closures implement traits like `Send` or `Clone`". `cargo fix` inserts `let _ = &a` (line 7), "a conservative analysis" (line 62).
- `compiler/rustc_lint_defs/src/builtin.rs:3407-3484` declares `RUST_2021_INCOMPATIBLE_CLOSURE_CAPTURES` as `Allow` with `fcw!(EditionSemanticsChange 2021 "disjoint-capture-in-closures")`. It was renamed from `disjoint_capture_migration` (`rustc_lint/src/lib.rs:423`).
- The migration analysis is still present in `upvar.rs` five years later: `perform_2229_migration_analysis` through `has_significant_drop_outside_of_captures` spans lines 1073–1872, which is 800 lines, about 29% of the 2,755-line file (derived).

Probes with `--edition 2018 -W rust-2021-incompatible-closure-captures`:

- `p17` (drop order) emits "changes to closure capture in Rust 2021 will affect drop order" and suggests `let _ = &p;`.
- `p18` (`Send` wrapper around `*mut i32`) also emits the lint.
- In edition 2021, `p18` fails with E0277: the closure captures `fptr.0`, which is not `Send`.
- `p15` (`self.list.retain(|i| self.filter.allowed(i))`, the RFC's motivating example) and `p16` (closure reads `foo.b` while `&mut foo.a` is live) are rejected (E0502) in edition 2018 on every toolchain and accepted in edition 2021 on 1.61.0, 1.100.0 and nightly.

**4.4 The rule moved after stabilization.** Probe `p20` borrows `&p.b` inside a closure while `&mut p.a` is live, with `#[repr(packed)] struct P { a: u8, b: u8 }`. rustc 1.61.0 (edition 2021) **accepts** it. Stable 1.100.0 and nightly **reject** it (E0502), as the alignment-independent truncation quoted in §4.2 predicts. The change came from PR #115315, merged 2023-09-16: "field capturing always stops at projections into packed structs, no matter the alignment of the field". The PR's justification is that a private field's type change could otherwise change program output. Basis: execution + documentation.

**4.5 Size cost (documentation).** The stabilization report (rust-lang/rust#88126) measured 23,694 closures. Average size was 12.39 bytes in 2018 rules, and growth under 2021 rules was +0.34 bytes (+2.74%). By bucket:

| Closure size bucket (bytes) | Growth |
|---|---|
| 0–16 | +5.56% |
| 64 and above | −0.27% |

### 5. Assignment whose right-hand side reads through the last loan

Probe `p13` checks `let r = &x; x = *r + 1;` and the `&mut` variant.

- **Accepted** by 1.35.0 edition 2018, 1.61.0, stable 1.100.0, and nightly with or without Polonius.
- **Rejected** by 1.35.0 edition 2015 (E0506 ×2, E0503). Under the pre-NLL checker, the loan lasted to the end of the scope.

The built MIR (`support/results/p13_shared.built.after.mir`) shows why NLL accepts it. The read `_3 = copy (*_2);` and the arithmetic `_4 = AddWithOverflow(copy _3, const 1_i32);` occur in `bb0`. The write `_1 = move (_4.0: i32);` occurs in `bb1`, and `_2` (`r`) is never used after the read. The loan therefore lies outside its region at the write, and the RFC 2094 kill-on-assignment rule then clears loans of `x`.

Probe `p14` uses `*r` after the assignment and is rejected (E0506) on every toolchain.

The design point, stated generically: a checker that invalidates every loan of the assigned place **before** evaluating the right-hand side (atomic "kill then evaluate") rejects `p13`. rustc's order is "evaluate the right-hand side into temporaries, then write, then kill". Swift states the same order for its instantaneous accesses. SE-0176 lines 299–303 say `x = x` is "NOT A CONFLICT" because "The right-hand side of the assignment is a read of 'x' which completes instantaneously."

Basis: execution + source (MIR) + normative (RFC 2094 lines 1564–1567; SE-0176).

### 6. Program classes: how Rust and Swift treat them

Key:

- **R-static**: rejected at compile time.
- **D**: dynamically checked (trap at run time).
- **A**: accepted.
- **[exec]**: the Rust entry comes from a probe on stable 1.100.0, edition 2021 unless noted. Swift entries are documentation or source only; no Swift compiler was run.

| Program class | Rust | Basis (Rust) | Swift analogue | Swift | Basis (Swift) |
|---|---|---|---|---|---|
| NLL case #1/#2/#4 (dead reference, borrow in one arm, reassigning a `&mut`) | A (pre-NLL: R-static) | [exec] `p09`,`p10`,`p12` | No lifetime-carrying references; accesses are scoped to the expression or call | A (class does not arise) | documentation (SE-0176 lines 38–60) |
| NLL case #3 (conditional return of a borrow) | R-static on stable and `-Zpolonius=off`; A on nightly default | [exec] `p11` | No borrowed return values in Swift 5 | not applicable | documentation |
| Nested method call `vec.push(vec.len())` | A (two-phase; pre-NLL e2015: R-static) | [exec] `p01` | `vec.append(vec.count)`: the `inout`/`mutating` access starts after argument evaluation | A | derived from normative (SE-0176 lines 305–310, by analogy with `x += x`) |
| Overloaded compound assignment `w += w.len()` / `x += x` | A | [exec] `p06` | `x += x` | A | normative (SE-0176 lines 305–310) |
| `v[0] += v[1]` (primitive) | A (also on 1.35.0 e2015) | [exec] `p24` | `array[0] += array[1]` | A | normative (SE-0176 lines 442–445) |
| Reservation conflicting with an earlier shared borrow `let s=&v; v.push(s.len())` | A since 1.62 (warning on 1.35–1.61) | [exec] `p07` | No persistent shared borrows; the read is instantaneous | A (class does not arise) | derived |
| Argument mutates receiver base `v[0].push_str({v.push(s); ""})` | R-static (E0499) | [exec] `p03` | `x.assignResultOf { x + 1 }` (closure reads during a mutating method) | R-static for locals; D for globals and class properties | normative (SE-0176 lines 323–327, 597–616) |
| Closure reads receiver during a `&mut self` call `x.assign_result_of(\|\| x.0 + 1)` | R-static (E0502) | [exec] `p22` | same | R-static (local) / D (global, class) | normative |
| Same variable passed twice mutably `swap(&mut x, &mut x)` | R-static (E0499) | [exec] `p23` | `swap(&x, &x)` | R-static | normative (lines 312–315) |
| Two elements of one array `swap(&mut a[0], &mut a[1])` | R-static (E0499); library `swap`/`split_at_mut` | [exec] `p23` | `swap(&array[0], &array[1])` | R-static (local); `swapAt` added | normative (lines 447–451, 481–487) |
| Disjoint fields, direct paths | A | [exec] `p21::fields` | Disjoint stored struct properties | A (statically, for known-stored properties) | normative (lines 371–375, 418–422) |
| Disjoint fields through `&mut self` methods | R-static (E0499) | [exec] `p21::through_method` | `mutating` method = access to the whole value | R-static (local) / D | normative (lines 358–363) |
| Disjoint fields of a class-held struct `swap(&object.pair.x, &object.pair.y)` | n/a (no implicit dynamic check; `RefCell` is all-or-nothing, see `p25`) | [exec] `p25` | as written | D traps (enforcement is per property, not per sub-field) | normative (lines 391–398); source (`AccessEnforcementOpts.cpp:44-47`) |
| Closure using disjoint field while sibling borrowed | A in 2021, R-static in 2018 | [exec] `p16` | Non-escaping closure capturing `point.y` while `point.x` is `inout` in the same statement | A (special-cased) | documentation (Swift.org post lines 283–303) |
| Closure using an index while another index is borrowed | R-static (whole array captured) | [exec] `p19` | Array subscript is a computed access to the whole array | R-static / D | normative (lines 426–431) |
| Assignment RHS reads through the last loan (`x = *r + 1`) | A (pre-NLL e2015: R-static) | [exec] `p13` | `x = x` | A | normative (lines 299–303) |
| Same, but loan used afterwards | R-static (E0506) | [exec] `p14` | No persistent references | not applicable | derived |

### 7. Swift's exclusivity enforcement

**7.1 Rule.** `docs/OwnershipManifesto.md:361-365` states the Law of Exclusivity: the formal access duration of an access to a variable "may not overlap the formal access duration of any other access to the same variable unless both accesses are reads." Lines 379–386 add: "static approaches to dynamic problems can only be conservatively correct: there will be dynamically-reasonable programs that are nonetheless rejected."

SE-0176 (`proposals/0176-enforce-exclusive-access-to-memory.md`, "Implemented (Swift 4.0)", line 6) splits enforcement (lines 271–286):

| Storage | Enforcement |
|---|---|
| "Local variables, inout parameters, and struct properties" | "generally enforce the rule statically" |
| "Class properties and global variables" | "will have to enforce the rule dynamically"; captured locals sometimes need dynamic enforcement too |
| "Unsafe pointers" | "will not use any active enforcement" |
| Immutable memory | none needed |

Escaping captures generally need dynamic enforcement. Non-escaping variables "can always use static enforcement" (lines 568–577), at the price of the Non-Escaping Recursion Restriction and its conservative user-level form, the NPCR (lines 624–671). Dynamic checking is per thread and does not detect races (lines 339–345). The proposal sketches an `@exclusivity(unchecked)` opt-out (lines 524–546). It exists in the pinned compiler: `test/SILGen/exclusivityattr.swift` uses `@exclusivity(checked)` and `@exclusivity(unchecked)`.

**7.2 Implementation (source, `swiftlang/swift@64060457`).**

- `lib/SILOptimizer/Mandatory/DiagnoseStaticExclusivity.cpp:13-22` finds violations at compile time from `begin_access`/`end_access` markers. It "models the in-progress accesses with a map from storage locations to the counts of read and write-like accesses".
- `lib/SILOptimizer/Mandatory/AccessEnforcementSelection.cpp:13-14` "eliminates 'unknown' access enforcement by selecting either static or dynamic enforcement".
- `lib/SILOptimizer/Transforms/AccessEnforcementOpts.cpp:22-77` folds scopes without nested conflicts, demotes local dynamic accesses to static when safe, and merges scopes. It "does not attempt to differentiate accesses on disjoint subaccess paths, because it should not weaken enforcement in any way--a program that traps at -Onone should also trap at -O."
- The runtime is in `stdlib/public/core/Exclusivity.swift`. `swift_beginAccess` (line 172) calls `Access.search` (lines 70–115), which walks a singly linked list of in-flight accesses (`while let nextPtr = unsafe cursor`, line 79). It reports a conflict `if unsafe nextPtr.pointee.action == .modify || action == .modify` (line 81) and pushes the new access at the head (line 112). The list head lives in thread-local storage (`stdlib/public/runtime/Exclusivity.cpp:128-129`). `swift_endAccess` (lines 210–223) unlinks the access. The per-access cost is therefore one TLS read plus a scan proportional to the number of tracked in-flight accesses on the thread (derived).

**7.3 Performance record (documentation).** The Swift.org post (`_posts/2019-02-05-swift-5-exclusivity.md:9-12`) says: "The Swift 5 release enables runtime checking of 'Exclusive Access to Memory' by default in Release builds ... In Swift 4, these runtime checks were only enabled in Debug builds." Lines 101–109 call the overhead "small in most cases". The flags `-enforce-exclusivity=unchecked` and `-enforce-exclusivity=none` (line 121) opt out.

The enabling PR, swiftlang/swift#20302 (merged 2018-11-07), says: "Of the 656 public microbenchmarks in the Swift repository, there are still several regressions larger than 10%". It lists 11:

| Benchmark | Ratio | Change |
|---|---|---|
| ClassArrayGetter2 | 0.11× | +840.3% |
| HashTest | 0.51× | +95.4% |
| NopDeinit | 0.66× | +52.3% |
| Hanoi | 0.68× | +46.5% |
| Calculator | 0.80× | +24.4% |
| Dictionary3OfObjects | 0.86× | +16.4% |
| CSVParsingAltIndices2 | 0.87× | +14.8% |
| Prims | 0.88× | +14.0% |
| CSVParsingAlt2 | 0.89× | +12.7% |
| Dictionary4OfObjects | 0.89× | +12.6% |
| ArrayInClass | 0.90× | +10.9% |

The PR attributes the pattern to arrays held in class properties and accessed repeatedly through the class reference: "Each of those class property accesses now incurs a runtime call." 11/656 = 1.7% of the suite exceeded 10% (derived).

**7.4 Source compatibility (normative).** SE-0176 lines 723–739: exclusivity "will eventually demand a source break". The proposal states: "Overall, we do not expect that a significant amount of code will violate exclusivity. This has been borne out so far by our testing." It names `swap(&array[i], &array[j])` → `array.swapAt(i, j)` as an automatic rewrite. The Swift.org post lines 64–78 add that diagnostics were strengthened in 4.1 and 4.2 and that Swift 5 "fixes the remaining holes", with footnoted exceptions SR-8546 and SR-9043. No ecosystem-wide breakage count comparable to Crater was found in the examined record.

### 8. Cost census

**8.1 Design.** For each relaxation, the census records:

| Dimension | Contents | Sources |
|---|---|---|
| (a) Checker concepts | Named types, enum variants and functions that exist only because of the relaxation | Pinned source |
| (b) Compile time | Upstream perf comments on the enabling or removing PR, plus a local synthetic measurement | PR comments; local runs |
| (c) Ecosystem breakage | Crater experiments, recorded as regressed/fixed/total plus any root-cause triage | Crater bot and triage comments on the PR |
| (d) Edition migration | Lint definition and remaining migration code | Source |
| (e) Soundness | GitHub issue searches with exact query strings and a dated total, then title triage of the matching lists; reproducers re-run locally | GitHub search; local runs |

The same template applies to Swift where a record exists.

**8.2 Checker concepts (source; counts derived from the listed declarations).**

| Relaxation | Concepts it added |
|---|---|
| NLL | Liveness-derived regions; location-aware outlives (`'b: 'a @ P`); end regions `end('r)`; loans-in-scope dataflow with kill-on-assignment (RFC 2094 lines 1468–1567). Not counted from rustc source. |
| Two-phase | `MutBorrowKind::TwoPhaseBorrow`, `AllowTwoPhase`, `TwoPhaseActivation` (3 variants), `reserve_location`, `activation_location`, `activation_map`, `pending_activations`, access kinds `Reservation` and `Activation`, `is_active`: 10 named declarations. Case-insensitive matches for `two_phase\|twophase\|two-phase\|2-phase\|reservation\|activation`: 45 in `borrow_set.rs`, 17 in `path_utils.rs`, 46 in `lib.rs`. |
| RFC 2229 | Capture place with projections and capture kind; 8 truncation or adjustment functions plus `truncate_place_to_len_and_update_capture_kind`; edition gate; an 800-line migration analysis |
| Polonius (`next`) | `compiler/rustc_borrowck/src/polonius/`: 12 files, 106,333 bytes, out of 62 `.rs` files and 1,539,157 bytes of `.rs` source in `compiler/rustc_borrowck` (Git tree API) |
| Swift | Access markers with `Static`/`Dynamic`/`Unknown`/`Unsafe` enforcement; four SIL passes named above; runtime access list; NRR/NPCR; `@exclusivity` attribute; `-enforce-exclusivity` modes |

**8.3 Ecosystem regression runs.** Percentages are derived.

| Change | Crater experiment | Result | Triage |
|---|---|---|---|
| Restrict two-phase reservations (lint) — #58739 | 2019-03-06 | 3 crates.io root regressions, 1 crate with reverse deps, 13 GitHub-only crates | Became a warning, not an error |
| NLL migrate-mode errors become hard errors, edition 2018 — #63565 | `pr-63565`, `mode=check-only` | 1,622 regressed / 70,078 (2.31%), 0 fixed | ">885 regressed reverse-deps" of `url` 1.7.0 and ">244" of `nalgebra` 0.16.13 (comment 528120122) |
| Remove migrate mode — #95565 | `pr-95565`, `check` | 454 regressed / 223,389 (0.20%), 33 fixed | 160 of 179 root regressions already carried the reservation-conflict warning; all root regressions arose from that lint (comments 1095117178, 1129132079) |
| Remove the reservation lint — #96268 | none found in PR comments | — | Perf: no relevant primary change |
| Whole-edition 2021 migration — #87190 | `pr-87190-3`, full | 1,827 regressed / 179,415 (1.02%), 14,976 fixed | Covers *all* 2021 changes. 872 dependency regressions were due to `resolver = "2"`. Closure-related items included an ICE (#87987), lifetime errors from different captures (#88114), and a trait-overflow caused by the migration lint (#88103). |
| Polonius alpha on nightly — #159343 | `pr-159343`, `check` | 2 regressed / 1,026,208, 18 fixed, 5,682 spurious | — |

**8.4 Soundness census (execution of GitHub search, 2026-11-20).** Exact queries and totals are in `support/results/census/census_queries.tsv`; the matching issue lists are in `census_lists.tsv`.

| Query | Total | Open |
|---|---|---|
| `label:I-unsound` | 763 | — |
| `label:I-unsound label:A-borrow-checker` | 53 | 22 |
| `label:I-unsound label:A-NLL` | 25 | 2 |
| `label:NLL-sound` | 54 | 4 |
| `label:I-unsound label:A-closures` | 13 | 9 |
| `label:I-unsound` with text `two-phase` | 17 | — |
| `label:I-unsound` with text `2229` | 0 | — |

The `two-phase` text match is noisy. Only six of its 17 hits concern borrow checking (#160598, #164163, #53026, #45045, #38899, #27282), and only the first two concern two-phase borrows. Title triage of the `A-NLL` list finds early NLL implementation bugs (2017–2019). Examples:

- #53026 "NLL migration mode is accepting code that both NLL and AST-borrowck reject!"
- #58776, about migrate mode downgrading an error into a use-after-free.
- #53142, "Polonius (but not ordinary NLL) accepts code which segfaults".

The `A-closures` list mostly concerns well-formedness and higher-ranked bounds, not capture precision. Several open 2026 reports involve the nightly-default Polonius, for example #164337 and #161038.

Labels are applied by humans, so these totals are lower bounds on relevant bugs and include unrelated ones.

**8.5 Performance and footprint (L1–L6).**

| Level | NLL | Two-phase | RFC 2229 | Polonius `next` (nightly) | Swift exclusivity |
|---|---|---|---|---|---|
| L1 authoring and maintenance | not measured (concepts in §8.2) | 10 named declarations; 108 keyword matches in 3 files | 800-line migration analysis retained (29% of `upvar.rs`) | 106,333 bytes in 12 files | not measured |
| L2 toolchain build | not measured | not measured | not measured | Bootstrap 487.651 → 492.438 s (+0.98%), cited from #159343 | not measured |
| L3 compile latency | Migrate-mode removal: −0.5% mean instruction count, max −1.9%, on 47 primary benchmarks (cited from #95565, comment 1148413415) | Removing the lint: no relevant primary change (cited from #96268) | not measured upstream. Local synthetic run (below): `type_check_crate` ratio e2021/e2018 median 0.91, range 0.65–1.43, n=9; not resolvable | Cited: +3.0% mean instructions on 88 primary benchmarks, range 0.3–15.3%. Local synthetic: `MIR_checking` paired ratio next/off median 1.085, range 0.81–1.53, n=9 per edition | not measured (compile side) |
| L4 generated code | not measured | Forgoes alias-based optimization on two-phase borrows (Stacked Borrows treats them as raw pointers, §3.4); magnitude not measured | not measured | Derived: an analysis-only change should not alter generated code; not measured | 11 of 656 microbenchmarks regress >10%; worst 0.11× (cited from #20302) |
| L5 checking or certificate speed | not applicable (no certificates) | not applicable | not applicable | not applicable | Runtime check = TLS read plus list scan (source, derived); cycles not measured |
| L6 memory and size | not measured | not measured | Closures +0.34 bytes average (+2.74%) over 23,694 closures (cited from #88126) | Max RSS +4.2% on 6 primary benchmarks (cited); local max RSS ≈ 548–550 MB for all configurations | Access record per in-flight dynamic access in a caller-provided buffer (source); bytes not measured |

Local synthetic measurement:

- Input: `support/scripts/gen_synthetic.py 1000`, 36,003 lines.
- Command: `rustc -Ztime-passes --crate-type lib --emit=metadata`, 9 interleaved rounds.
- Host: x86-64 Linux workstation with 96 logical CPUs, shared, 1-minute load average 43–67.
- Medians, Polonius `next` / `off`: edition 2021, `MIR_checking` 1.638 s / 1.412 s, wall 4.47 s / 4.28 s; edition 2018, 1.541 s / 1.495 s.

The direction matches the upstream report, but run-to-run spread exceeds the difference. This is a real compiler on a synthetic input, not a representative crate.

### 9. Human comprehensibility (C1) and model refinement (C2)

**C1, mental-model load.**

- **NLL** removed a nonlocal rule ("a borrow stored in a variable lasts to the end of the variable's scope") in favor of a local one ("until the last use"). On paper this reduces the reasoning needed for cases #1, #2 and #4. Residual case #3 is nonlocal: the region depends on whether the value flows to the caller. Its diagnostic mentions the named lifetime `'r` (probe logs), and the user must restructure control flow. The RFC's own workaround costs extra lookups (lines 311–313).
- **Two-phase borrows** add a hidden phase that the surface syntax does not show. Whether a borrow is two-phase depends on *how* it was written: `vec.push(vec.len())` passes, `Vec::push(&mut vec, vec.len())` fails (`p01` vs `p05`). RFC 2025 lines 572–592 rejected wider use precisely because the distinction "cannot be explained except by examining the desugarings into MIR". The 2026 soundness reports show that even the implementers' stated invariant (post-dominance) was not a property of the input language.
- **RFC 2229** aligns closures with the existing field-disjointness intuition (RFC lines 33–37). It adds truncation exceptions that users meet as surprises: indexing (`p19`), `repr(packed)` (`p20`, which changed between releases), raw pointers, and auto-trait changes (`p18`). The migration lint's "dummy let" output is legible, but the analysis is acknowledged as conservative.
- **Swift** keeps one rule (non-overlapping formal accesses) and moves the burden into *which enforcement applies*, a property of storage kind and escape analysis. Diagnostics are static for the common local cases and run-time traps with two program counters for the rest (Swift.org post lines 232–241).

None of these comprehension claims is backed by a controlled human study in the examined record. Crichton et al. 2023 and Zhu et al. 2022 study Rust ownership comprehension generally, not these relaxations (see Boundaries).

**C2, orthogonality.**

- Rust now enforces "no conflicting overlap" through four mechanisms: lexical-scope-free regions (NLL), a special borrow kind with its own dominator test (two-phase), a closure-lowering transformation with eight truncation rules (2229), and, on nightly, a second region analysis (Polonius).
- The two-phase special case exists because the evaluation order of method calls puts the receiver's borrow before the arguments. RFC 2025 considered fixing the order instead (lines 406–488) and the `Ref2<'r,'w>` "write lifetime" generalization (lines 666–760). It rejected both for complexity.
- Swift's "access begins after argument evaluation" rule (SE-0176 lines 305–309) makes Rust's nested-call case an ordinary case without a new borrow kind. This works only because Swift has no long-lived references whose region must be inferred.
- The RFC 2229 truncations are not ad hoc in origin. Each prevents capture from executing something the closure body would execute: `unsafe` operations, impure calls, indexing, or moves out of `Drop` types. Packed-field truncation, however, is a realization-medium constraint (alignment) promoted to a semantic rule to keep capture independent of private field types (§4.4).
- A unifying abstraction that would make reservations, disjoint method footprints and closure captures ordinary cases (for example, place-based "view" footprints on references) is not present in stable Rust. The pinned compiler contains an unfinished `ty::View` type kind, which hits `unimplemented!()` in the borrow checker (`compiler/rustc_borrowck/src/lib.rs:1952`, `1997`).

### 10. Validation of these mechanisms (V1–V4)

- **V1, specification adequacy and non-vacuity.**
  - Rust validates relaxations mostly by UI tests that pin expected acceptance and rejection, such as the `nll-problem-case-3-*` revisions. Each test is run under `nll`, `polonius` and `legacy`, which is a three-way differential check of the same program.
  - RFC 2229's stabilization relied on `#[rustc_capture_analysis]` dumps (probe `p26` reproduces the mechanism) and on public edition testing.
  - Operationally, Miri executes MIR under Stacked or Tree Borrows. #160598's reporter cites a Tree Borrows violation, and #96268 cites a Miri test of the reservation pattern. This checks that accepted programs are not undefined behavior, but only for executed paths.
  - No spec-mutation or mutant-kill rates for the borrow checker were found.
- **V2, checker soundness fuzzing and differential testing.**
  - Crater is a large differential test of compiler versions on real crates (README lines 3–6; modes `check-only` and `build-and-test` in `docs/bot-usage.md:82-84`). It detects *new rejections* well (§8.3). By construction it cannot detect *new unsound acceptances*, because a crate that keeps compiling is not flagged.
  - The two open two-phase bugs did not come from Crater. #160598's reporter states that large language models were used to search for soundness issues. How #164163 was found is not stated in the examined text.
  - No CSmith-style fuzzing campaign aimed at borrow-checker acceptance was found in the examined record.
- **V3, concurrency, crash and physical validation.**
  - Swift's dynamic enforcement is explicitly not a race detector (SE-0176 lines 339–345). Weak-memory or interleaving model checking of exclusivity is not part of the record.
  - Rust's relaxations are sequential, intra-procedural analyses. Thread-safety rests on `Send`/`Sync`, which RFC 2229 can perturb: probe `p18` shows the migration hazard.
  - Hardware and leakage validation does not apply to these mechanisms.
- **V4, human mental models.**
  - Swift's record uses benchmark and source-compatibility testing, not user studies.
  - Rust's edition migration uses `cargo fix` plus crater runs of the fixed code (#87190).
  - Empirical studies exist for ownership in general: Crichton, Gray and Krishnamurthi, OOPSLA 2023, whose abstract reports an "Ownership Inventory" assessment; and Zhu et al., ICSE 2022. No examined study targets two-phase borrows or precise capture specifically.

## Boundaries

**Not examined.**

- No Swift compiler was run, so every Swift row in §6 is documentation or source only.
- Swift's static diagnostics for corner cases SR-8546 and SR-9043 were not examined.
- Swift ecosystem breakage counts were not examined. None were found in SE-0176 or the Swift.org post.
- The full NLL region-inference implementation (`region_infer/`, liveness) was not read. NLL concept counts come from the RFC, not the source.
- Location-aware subtyping and end regions from RFC 2094 were not traced into rustc, beyond the case-#3 deferral quoted from the tests.
- The hackmd triage documents linked from #87190 were not opened, so the closure-specific share of the 2021-edition regressions is unknown.
- The Crater run for RFC 2229 alone (as opposed to the whole edition) was not found.
- Tree Borrows' treatment of two-phase borrows was not examined. Only the Stacked Borrows statement in #96268 was used.
- `Rvalue::Reborrow`/`gather_reborrows` in `borrow_set.rs` (a reborrow experiment marked `FIXME(reborrow)`) and the `ty::View` experiment were not analyzed.
- The bisection on #164163 was not reproduced.
- Probes on Windows or macOS were not run.

**Unknown.**

- Whether Polonius `next` will become the stable default, and its final compile-time cost on stable.
- The magnitude of optimization lost by treating two-phase borrows as raw pointers. Nobody has measured it. The compromise proposal on #58739 (comment 476387184) already said "we do not expect to be able to say 'N% impact on this benchmark'".
- Whether the doc comment's `Foo::some_method(&mut x, ...)` bullet (`adjustment.rs:156`) was ever true for explicit `&mut` arguments. It is false on every toolchain tested here (1.35.0 editions 2015 and 2018, 1.61.0, 1.100.0, nightly), while implicit reborrows of an existing `&mut` argument (`p27`) do behave as two-phase from 1.35.0 edition 2018 onward.
- How many crates contain the shapes in #160598 and #164163.

**Known not to apply.**

- The local compile-time numbers do not characterize real crates or an unloaded host.
- The Crater counts for #87190 cover the entire 2021 edition, not RFC 2229 alone.
- The `-Zpolonius` behavior described applies to nightly builds with `CFG_DEFAULT_POLONIUS_NEXT`. Stable 1.100.0 does not accept problem case #3.
- Swift's "access begins after argument evaluation" explanation does not transfer to Rust references that outlive the expression.

**Unsupported.**

- `-Zpolonius=nll` is rejected by the nightly toolchain. The accepted values are `legacy`, `off` and `next`.
- Labeled block expressions are unsupported on 1.61.0 (E0658), so `s02` cannot test that toolchain. The loop variant `s03` was used instead.

**Stronger conclusions not established.**

- The evidence does not show that Polonius `next` is sound. Several open 2026 `I-unsound` reports name it.
- It does not show that two-phase borrows are the main source of borrow-checker unsoundness. Two open issues out of 22 open `I-unsound` plus `A-borrow-checker` reports is a count, not a rate per feature.
- It does not show that Swift's dynamic checks cost little in general. The only quantified record is a microbenchmark suite with known worst cases.
- It does not show that RFC 2229 increased compile time. No upstream measurement was found, and the local measurement is noise-dominated.

## Evidence

All evidence was acquired on 2026-11-20 (UTC).

**Pinned source** (raw files fetched from `raw.githubusercontent.com` at these commits):

- `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`
  - `text/2094-nll.md`: lines 9–11, 97, 143, 201, 311–313, 336, 431–434, 1416–1516, 1564–1567, 2102–2165.
  - `text/2025-nested-method-calls.md`: lines 12–20, 192–202, 233–238, 285–293, 406–488, 528–532, 572–592, 666–760.
  - `text/2229-capture-disjoint-fields.md`: lines 9–10, 33–53, 106–107, 132–157, 311–312.
- `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`
  - `compiler/rustc_borrowck/src/borrow_set.rs`: 40, 128–152, 241–249, 443–473, 538–568.
  - `compiler/rustc_borrowck/src/path_utils.rs`: 60–120.
  - `compiler/rustc_borrowck/src/lib.rs`: 1089–1092, 1313–1328, 1490–1496, 1952, 1997.
  - `compiler/rustc_middle/src/ty/adjustment.rs`: 152–168.
  - `compiler/rustc_middle/src/mir/syntax.rs`: 198–201.
  - `compiler/rustc_hir_typeck/src/upvar.rs`: 1073–1872, 2120–2150, 2315–2467, 2700–2755.
  - `compiler/rustc_lint_defs/src/builtin.rs`: 3407–3484.
  - `compiler/rustc_lint/src/lib.rs`: 423, 581–585.
  - `compiler/rustc_session/src/config.rs`: 3835–3858.
  - `compiler/rustc_session/src/options.rs`: 981–982, 2458–2461.
  - `tests/ui/nll/polonius/nll-problem-case-3-issue-21906.rs`: 3–15.
  - `RELEASES.md`: 4847, 5060, 8370, 8503, 8777.
- Toolchain commits `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (nightly), used for the cross-version diff of the quoted files.
- `rust-lang/edition-guide@ab8544aeed7b792984366aa122ac19bd47ad9a2f`: `src/rust-2021/disjoint-capture-in-closures.md`, lines 5–7, 15–33, 44–62, 144–148.
- `rust-lang/crater@abaa949414a8b9457858f0fc1a6ed97824cb9120`: `README.md` lines 3–6; `docs/bot-usage.md` lines 76–94.
- `swiftlang/swift-evolution@f75d0a0456d72c2ca3ae418cc6a9939d32f42779`: `proposals/0176-enforce-exclusive-access-to-memory.md`, lines 6, 263–328, 339–345, 358–451, 481–487, 524–616, 624–671, 721–739.
- `swiftlang/swift@640604572aaeae2e0f37c139bc70556129efb550`
  - `docs/OwnershipManifesto.md`: 356–386.
  - `lib/SILOptimizer/Mandatory/DiagnoseStaticExclusivity.cpp`: 13–22.
  - `lib/SILOptimizer/Mandatory/AccessEnforcementSelection.cpp`: 13–14.
  - `lib/SILOptimizer/Transforms/AccessEnforcementOpts.cpp`: 22–77.
  - `lib/SILOptimizer/Mandatory/AccessMarkerElimination.cpp`: 13–16.
  - `stdlib/public/core/Exclusivity.swift`: 70–115, 167–223.
  - `stdlib/public/runtime/Exclusivity.cpp`: 13, 55, 128–139.
  - `test/SILGen/exclusivityattr.swift`: 5, 8.
- `swiftlang/swift-org-website@dabf9ac18178ccbd17e43bb4972b5064ee577385`: `_posts/2019-02-05-swift-5-exclusivity.md`, lines 9–14, 57–83, 101–132, 232–241, 270–304.

**GitHub records** (read through the REST API; numbers quoted verbatim from bot or author comments):

- rust-lang/rust PRs #58739 (comments 470230949, 476387184), #59114, #63565 (comments 521404515, 528068366, 528120122), #64221, #87190 (comments 899853369, 905223861, 905250803), #88126 (body: capture algorithm, size table), #95565 (comments 1092781219, 1095117178, 1129132079, 1148413415), #96268 (body; comments 1104688116, 1105261537, 1119777744), #115315, #159343 (comments 4984259233, 5017384026).
- rust-lang/rust issues #56254, #59159, #160598, #164163, #164337, #43234, #44100, #53488, #49434, #27868.
- swiftlang/swift PR #20302 (body; merged 2018-11-07).
- Search-API census: `support/results/census/`.

**Execution.**

- Host: x86-64 Linux workstation.
- Toolchains: `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, `rustc 1.100.0 (0ef1bc386 2026-11-09)`, `rustc 1.61.0 (fe5b13d68 2022-05-18)`, `rustc 1.56.0 (09c42c458 2021-10-18)`, `rustc 1.35.0 (3c235d560 2019-05-20)`. Full commits are in `REPORT.json`.
- Probe sources: `support/probes/`.
- Every compiler invocation and its complete output: `support/results/raw/`. First line is the command, last line the exit code.
- Summary: `support/results/probe_matrix.tsv` (243 runs).
- MIR dump: `support/results/p13_shared.built.after.mir`.
- Timing: `support/results/bench/`.

Representative commands:

- `rustc --edition 2021 --crate-type lib --emit=metadata p11_nll_case3.rs` (nightly: exit 0)
- `rustc -Zpolonius=off --edition 2021 --crate-type lib --emit=metadata p11_nll_case3.rs` (exit 1, E0499 ×2)
- `rustup run 1.100.0 rustc --edition 2018 -W rust-2021-incompatible-closure-captures --crate-type lib --emit=metadata p17_migration_lint_drop.rs`

**Literature** (identity verified through the doi.org handle API, `https://doi.org/api/handles/<doi>`, responseCode 1, plus OpenAlex and publisher metadata via web search; the Crossref API was unreachable from the fetching tool; content was not re-read in this investigation):

- R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, "RustBelt: Securing the Foundations of the Rust Programming Language", PACMPL 2(POPL), 2018, DOI 10.1145/3158154.
- R. Jung, H.-H. Dang, J. Kang, D. Dreyer, "Stacked Borrows: An Aliasing Model for Rust", PACMPL 4(POPL), 2020, DOI 10.1145/3371109.
- R. Jung, *Understanding and Evolving the Rust Programming Language*, PhD thesis, Saarland University, 2020, DOI 10.22028/D291-31946.
- N. Villani, J. Hostert, D. Dreyer, R. Jung, "Tree Borrows", PACMPL 9(PLDI), 2025, DOI 10.1145/3735592.
- A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, "Oxide: The Essence of Rust", arXiv:1903.00982 (v4, 2021; arXiv abstract page fetched).
- W. Crichton, G. Gray, S. Krishnamurthi, "A Grounded Conceptual Model for Ownership Types in Rust", PACMPL 7(OOPSLA2), 2023, DOI 10.1145/3622841. OpenAlex lists a different venue string; publisher-side metadata gives OOPSLA 2023.
- S. Zhu, Z. Zhang, B. Qin, A. Xiong, L. Song, "Learning and Programming Challenges of Rust: A Mixed-Methods Study", ICSE 2022, DOI 10.1145/3510003.3510164.

## Revalidation

Start with these checks, cheapest first.

1. **Probe matrix.** Run `bash support/scripts/run_probes.sh` after editing the two path variables at its top. Compare exit codes with `support/results/probe_matrix.tsv`. The discriminating rows are:
   - `p11` (case #3): nightly default vs `-Zpolonius=off`.
   - `p05` vs `p27` (explicit `&mut` vs implicit reborrow).
   - `p13` / `p14` (assignment design point).
   - `p20` (packed capture rule).
   - `s01`, `s02`, `s03` (soundness reproducers). If any of these starts failing to compile, the corresponding issue was probably fixed. Check whether `is_active` changed.
2. **Polonius default.** Run `rustc -Z help | grep polonius` and inspect `Polonius::DEFAULT` in `compiler/rustc_session/src/config.rs`.
3. **Two-phase scope.** Diff `compiler/rustc_middle/src/ty/adjustment.rs` (`AllowTwoPhase` comment), `compiler/rustc_borrowck/src/path_utils.rs` (`is_active` and its assumption comment) and the `(Reservation(_), ...)` arm in `compiler/rustc_borrowck/src/lib.rs` against the quoted text.
4. **Capture truncation.** Run probe `p26` on a nightly with `#![feature(rustc_attrs)]` and compare the "Min Capture" lines with §4.2. Diff the functions named in §4.2 in `upvar.rs`.
5. **Census.** Re-issue the query strings in `support/results/census/census_queries.tsv` against the GitHub search API. Totals will drift, so compare issue lists, not just counts.
6. **Swift.** Diff SE-0176's "Proposed solution" section, `AccessEnforcementOpts.cpp` header lines 22–47, and `Access.search` in `stdlib/public/core/Exclusivity.swift`. To turn the §6 Swift entries from documentation into execution evidence, compile the SE-0176 examples with a Swift toolchain. That has not been done here.
7. **Compile-time claims.** These require a quiet host or instruction counting, which was not available here. Rerun `support/scripts/run_bench_interleaved.sh`, or rely on upstream perf comments.
