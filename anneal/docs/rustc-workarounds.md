<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Upstream `rustc` workarounds

Anneal pins one nightly compiler (`COMPILER_COMMIT` in
`trusted/rustc-capture/src/ir.rs`) and drives it through `rustc_private`
interfaces. Some Anneal code exists only because the pinned compiler, its
standard library, or a companion tool lacks an interface, behaves
surprisingly, or exposes only unstable internals. This document owns the
procedure for tracking those workarounds, so that each is evaluated once for
an upstream fix and deleted once a compiler bump makes it unnecessary. The
anchor and the policy keep the `rustc` name for workarounds of any upstream
Rust toolchain component listed below.

This document grants no authority to file issues, post comments, or submit
changes outside this repository: every upstream filing or comment it calls
for needs maintainer sign-off first.

Live state stays on GitHub rather than in this repository. The
[umbrella issue][umbrella] (#4358) has one native sub-issue per workaround,
and code carries only a stable anchor to that sub-issue.

## What to track

Track a workaround when all three conditions hold:

1. **Upstream cause:** An API gap, pass or lowering quirk, diagnostic or `-Z`
   flag behavior, feature-gate or stability limitation, or private layout
   dependency in `rustc`, `rustc_public`, `rustc_driver`, `rustdoc`, `cargo`,
   or `core`/`alloc`/`std` triggers it.
2. **Observable cost:** It adds capture, `cargo-anneal`, or CI code, adds
   complexity to `trusted/`, couples Anneal to private compiler or library
   internals that can break across bumps, or rejects valid crates.
3. **Plausible remedy:** An upstream bug fix, stable or `rustc_public` API,
   query, flag or diagnostic change, MIR phase guarantee, or stabilization
   could remove or shrink it.

Do not track:

- Anneal design choices unrelated to compiler behavior, such as the Lean IR
  encoding, specification syntax, receipt formats, or CLI ergonomics.
- Intentional language non-guarantees with no missing compiler interface,
  such as unspecified `repr(Rust)` padding, unless checking them forces Anneal
  to read private compiler or library internals.
- Routine renames of `rustc_private` items that per-compiler adapters absorb,
  unless a rename exposes a missing `rustc_public` surface.
- Limitations already fixed at or before `COMPILER_COMMIT`. Use the supported
  interface instead.

## Code anchors

Anchor each open workaround at its primary site, and at each helper that
lives elsewhere, with one tag in the file's comment syntax:

```rust
// RUSTC-WORKAROUND(#4364): codegen rewrites `Use` calls after capture.
```

Use `#` in Python, shell, TOML, YAML, and Nix, and `--` in Lean. The tag is
`RUSTC-WORKAROUND(#NNNN): ` followed by a short summary, which may continue
on the next comment lines, where `#NNNN` names a sub-issue of the umbrella.
Keep mutable state, such as status and upstream links, in the issue rather
than in comments, so triage never edits `trusted/`. Anchors supplement the
pinned upstream quotes and citations that `trusted/` code already requires;
they never replace them.

Contributors and delegated workers who cannot file issues write
`RUSTC-WORKAROUND(#PENDING): <summary>` and hand off the completed
[evaluation](#five-minute-evaluation). Whoever publishes the change files the
sub-issue, attaches it to the umbrella, and replaces every `#PENDING` before
Gate 1 converges or the PR is marked ready for review. Review rejects any
remaining `#PENDING`.

## Public and private boundary

Track neutral compiler-interface limitations publicly, framed around Rust
verification and analysis tooling. Never cite private repositories, private
issue numbers, internal products, or roadmaps in issues, code, commits, or
Review Receipts.

An unvetted compiler soundness or security defect stays under private
security disclosure until responsible disclosure produces a public issue in
this repository or in `rust-lang/rust`. Until then, describe any guard it
motivates solely by the guard's neutral fail-closed invariant: do not claim
upstream unsoundness, add an anchor, or reference the private report. Add the
anchor once a public issue exists. Because such a guard has no anchor or
public issue, its re-verification on every compiler-pin bump is confirmed
privately at Gate 5 (see the
[retirement checklist](#compiler-bump-retirement-checklist)). If you are
unsure whether a limitation falls under private security disclosure, ask a
maintainer before filing anything public.

## Five-minute evaluation

Complete this evaluation in the sub-issue before Gate 1 converges, since the
anchor must name an evaluated issue. The upstream work that its disposition
calls for never blocks landing the local workaround; only the Q1 disclosure
check can stop public tracking.

1. **Q1, disclosure (yes or no):** Is this an unvetted soundness or security
   defect? If so, stop public filing and follow the
   [boundary](#public-and-private-boundary) above.
2. **Q2, generality (0–2):** 0 if specific to Anneal's architecture; 1 if it
   helps at least two verification or analysis tools (such as Miri, Kani,
   Verus, Aeneas, or Clippy); 2 for a broad `rustc_public`, `-Z` flag,
   diagnostic, or nightly-Rust improvement.
3. **Q3, cost (0–2):** 0 for a small helper outside critical semantics that
   survives bumps; 1 for moderate complexity or rejecting valid crates; 2 if
   it lives in `trusted/`, couples to private compiler or library internals,
   or risks silent divergence on bumps.
4. **Q4, actionability (0–2):** 0 for an intentional upstream non-goal or a
   change needing a language RFC; 1 if upstream design alignment (an issue,
   major change proposal, or Zulip discussion) must come first; 2 for a small,
   self-contained upstream PR or issue.

Choose the first matching disposition:

| Condition | Disposition | Action | Labels |
| :--- | :--- | :--- | :--- |
| The fix already landed upstream after `COMPILER_COMMIT`, or an active upstream track covers it | (c) Park on the track | Link the upstream fix or tracking issue; mark `upstream-landed` if already fixed, else `upstream-pitched` | `anneal`, plus `blocked-on-rust` until the fix lands |
| `Q2+Q3+Q4 >= 5`, or `Q3 == 2` and `Q4 == 2` | (a) Upstream now | Draft a minimal reproducer and upstream PR or proposal; submit only after maintainer sign-off | `anneal`, `blocked-on-rust` |
| `Q2 >= 1` and `Q4 == 1` | (b) Signal upstream | Draft a new upstream issue, or a comment on an existing one, with a minimal reproducer; post only after maintainer sign-off | `anneal`, `blocked-on-rust` |
| `Q4 == 0` | (d) Keep local | Record why upstreaming is not worthwhile | `anneal` |

If no row matches, choose the closest disposition and justify it in the
sub-issue.

## Lifecycle

Each sub-issue body opens with one status line (see the
[template](#sub-issue-template)) whose state follows:

```text
identified -> evaluated -> upstream-pitched | upstream-pr-open
                        -> upstream-landed
                        -> deferred-local
upstream-pitched | upstream-pr-open -> upstream-landed -> workaround-retired
```

- Dispositions (a), (b), and (c) stay open through `upstream-landed`, dropping
  `blocked-on-rust` once the fix lands upstream, and close at
  `workaround-retired`, after a bump PR deletes the workaround and its anchor.
  A (c) item whose upstream track has not landed rests at `upstream-pitched`;
  one whose fix already landed after `COMPILER_COMMIT` goes straight to
  `upstream-landed`.
- Disposition (d) closes at `deferred-local` unless the workaround relies on
  private compiler or library internals that each bump must re-verify (such
  as private `Vec` field paths); such issues stay open without
  `blocked-on-rust`. Anchors may cite a closed (d) issue so later
  contributors find why the workaround stays local.

## Sub-issue template

Title each sub-issue `[anneal][rustc-workaround] <neutral summary>`, attach it
to the umbrella, and start from:

```markdown
Status: evaluated | Disposition: (a)|(b)|(c)|(d) | Upstream: none|<url>
Umbrella: #4358 | Code anchor(s): `path/to/file.rs`

## Upstream limitation
- **Compiler pin observed:** `<COMPILER_COMMIT>` (`<COMPILER_VERSION>`)
- **Upstream location:** `https://github.com/rust-lang/rust/blob/<40-hex-sha>/<path>`
- **Local workaround and cost:** <what Anneal does and what it costs>

## Evaluation
- **Q1 disclosure:** <no unvetted soundness or security defect>
- **Q2 generality (0-2):** <score and affected tools>
- **Q3 cost (0-2):** <score and bump risk>
- **Q4 actionability (0-2):** <score and concrete upstream change>
- **Disposition:** <(a)|(b)|(c)|(d)>: <one or two sentences>

## Removal criteria
1. <Required upstream change, such as a minimum `COMPILER_COMMIT`>
2. <Local code and anchor to delete or simplify>
3. <Command confirming clean removal>
```

## Compiler-bump retirement checklist

Every PR that changes `COMPILER_COMMIT` (`trusted/rustc-capture/src/ir.rs`),
`PINNED_RUSTC_COMMIT` (`trusted/cargo-anneal/src/verify.rs`), or `rustDate`
(`flake.nix`) runs these steps, and reviewers check them under
[`trust-review`](../skills/trust-review/SKILL.md#4-provenance-locks-manifests-and-packaged-bundles):

1. **Inventory:** List every in-repo anchor (from `anneal/`, run
   `git grep -nE 'RUSTC-WORKAROUND\(#[0-9]+\)' -- . ':!*.md'`, which skips
   the policy text and examples) and every open sub-issue of the umbrella.
2. **Audit each item against the old and new pins:**
   - `upstream-landed`: Confirm the new pin contains the fix, then delete the
     workaround and its anchor in the bump PR.
   - `upstream-pitched` or `upstream-pr-open`: Check the upstream issue or PR;
     if the new pin contains the fix, promote the item to `upstream-landed`
     and retire it as above.
   - Workarounds coupled to private internals, including open (d) items:
     Re-verify every relied-upon private path, layout, signature, or hook
     against the new pin's source.
   - Embargoed guards: The Gate 5 approver, who can read private security
     reports, approves the bump only after every embargoed guard has been
     re-verified against the new pin by its report holder, or after
     confirming that none exists. Every bump PR's Review Receipt carries the
     same fixed line, which records only this routing and reveals neither
     the existence nor the number of such guards:
     `Embargoed guards: confirmation routed to the Gate 5 approver.`
3. **Close retired issues:** Set the status to `workaround-retired`, cite the
   retiring PR, and close the sub-issue.
4. **Report:** Add an audit table
   (`Anchor | Issue | Status at old -> new pin | Action`) to the bump PR's
   Review Receipt.

[umbrella]: https://github.com/google/zerocopy/issues/4358
