# Unsafe Rust source audit: `cross-axis-target` 0.1.0

## Claim, scope, and verdicts

This audits the exact supplied `Cargo.toml`, `build.rs`, `src/lib.rs`,
`SUPPORT.md`, `BUILD.md`, and `TCB.md`, source-only, at the 2026-08-01 audit
cutoff. No build, execution, expansion, test, prior audit, or VCS identity is
used.

`Supported(c)` means: edition 2021 with Rust, std, and Cargo 1.85.1; target
triple in `{x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu,
wasm32-unknown-unknown}`; `burst` either disabled or enabled; allocator selected
through `BUILD.md` as `system` or `arena`; excluding `wasm32`+`arena`; every
Cargo profile and either debug-assertion state. Thus there are ten supported
target/feature/allocator tuples, each parametric over profiles and debug
assertions.

The soundness claim is: for every `Supported(c)`, every well-typed safe use of
the public API, and every permitted source-level Rust execution, the supplied
crate introduces no undefined behavior, relative only to the TCB below.

- **Whole supported-domain soundness: UNSOUND (F-01).** One expressly supported
  tuple, `aarch64-unknown-linux-gnu` + `arena` + `burst`, admits a safe call
  `lane_id(0)` that violates `NonZeroU8::new_unchecked`'s safety precondition.
- **Other nine supported tuples: PROVED** for source-level soundness and the
  documented `lane_id` behavior, relative to the stated TCB.
- **Documented zero-input panic:** PROVED in those nine tuples; **UNPROVED** in
  the defective tuple. It is not `CONTRACT-BROKEN`: the known zero-input
  execution contains UB, so it is not a UB-free postcondition witness.
- **Rejected `wasm32`+`arena` tuples (both feature states): PROVED effectively
  rejected** before a library artifact is produced, relative to BUILD-MAP-X.

No binary/backend, deployment, security, probabilistic, or additional
robustness theorem is claimed.

## Snapshot, boundary, and configurations

The manifest has no dependencies, an empty default feature set, and only the
`burst` feature. The build script is the sole configuration producer; there is
no generated source. Its finite successful selector output family is exactly
`fixture_allocator="system"` and `fixture_allocator="arena"`:

1. [`env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html) supplies a
   Unicode `String`, `NotPresent`, or `NotUnicode`. Lines 9-15 preserve an
   accepted Unicode value, map absence to `system`, and panic on non-Unicode.
2. Lines 16-20 accept only the two literal strings and execute exactly one
   selector `println!`; every other Unicode value panics. [`println!`](https://doc.rust-lang.org/1.85.1/std/macro.println.html)
   writes one newline-terminated stdout record and panics on a write failure.
3. BUILD-MAP-X supplies only the Cargo-to-library transmission and unsuccessful
   build-script behavior. Therefore accepted runs set exactly one allocator
   cfg; invalid selectors and stdout failures produce no library compilation.

Under the [Reference `cfg` rules](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute),
false-attributed forms are removed and true-attributed forms remain. Cargo's
[feature contract](https://doc.rust-lang.org/1.85.1/cargo/reference/features.html)
and BUILD-MAP-X map the boolean `burst` state; BUILD-MAP-X maps each supported
target triple to its stated `target_arch`.

`src/lib.rs:3-13` rejects neither or both allocator cfgs. On the supported Cargo
interface exactly one is present, so those guards are inactive. For the listed
Wasm target plus `arena`, lines 15-16 retain `compile_error!`, which
[`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)
documents as causing compilation to fail. This proves the policy exclusion.
Unlisted targets and manual `rustc` cfg invention are outside the theorem and
are not claimed generally rejected.

The only language-reachable crate API is safe
`lane_id(u8) -> NonZeroU8` (`src/lib.rs:23-46`). There are no crate-defined
public fields/types, unsafe APIs/traits/impls, callbacks, FFI, statics,
reexports, exported macros, or hidden APIs. The two unsafe consumers are lines
31 and 44. There is no crate-owned temporal invariant; each call must locally
establish that its particular argument is nonzero.

Profiles, optimization, debug assertions, and panic strategy do not select code
here. There is no arithmetic, debug assertion, mutable state, destructor-held
invariant, concurrency, allocation-sensitive unsafe operation, or unwinding
cleanup obligation, so the proofs are parametric over those axes.

## TCB and authoritative premises

**BUILD-MAP-X (accepted, not widened):** exactly the proposition and scope in
supplied `TCB.md`: Cargo 1.85.1 executes this build script as required; honors
its rerun directive; check-cfg declares without setting; transmits emitted
allocator cfgs; maps enabled `burst` and the three target triples as stated; and
performs no library compilation after unsuccessful build-script exit. It is
consumed only for reachability and rejection. It does not establish the emitted
string, source correctness, abstract semantics, backend correctness, or a
binary theorem. Any named input, Cargo/toolchain, source, target-set, or human
disposition change triggers review.

**AXIOM-NZ (Rust/std 1.85.1):**
[`NonZero::new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)
requires that its value “must not be zero”; zero produces undefined behavior.
Consumers: O-03/O-04.

**AXIOM-FLOW (Rust 1.85.1):** equality compares the operands, and an
[`if`](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html)
executes its consequent when its Boolean condition is true. The
[`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html) macro panics
the current thread. Consumers: O-03/O-05.

**AXIOM-CFG/BUILD:** the version-matched cfg, feature, environment, output, and
compile-error pages cited above supply only the propositions used in the
configuration derivation. There are no safe/unsafe third-party dependencies,
tool-derived facts, implementation premises, or other admitted assumptions.

## Obligation ledger and proofs

| ID | Proposition and complete domain | Derivation | Status |
|---|---|---|---|
| O-01 | Accepted selector yields exactly one supported cfg; rejected values yield no library compilation | `build.rs:9-20`, AXIOM-CFG/BUILD, BUILD-MAP-X | PROVED |
| O-02 | `wasm32`+`arena`, either feature state, cannot ship | `lib.rs:15-16`, AXIOM-CFG/BUILD, BUILD-MAP-X | PROVED |
| O-03 | Line 44 receives nonzero in all nine ordinary tuples | Its cfg is the complement of the special conjunction. If `value == 0`, lines 40-42 panic and line 44 is not reached; normal reach therefore entails `value != 0`, satisfying AXIOM-NZ. For nonzero, `new_unchecked` returns the corresponding `NonZeroU8`. | PROVED |
| O-04 | Line 31 receives nonzero for every safe call in the special tuple | The `u8` parameter is caller-controlled and unchecked. `value = 0` is well typed and falsifies the required premise. | UNSOUND |
| O-05 | Zero input panics | In ordinary tuples O-03 reaches `panic!`. In the special tuple line 31 instead reaches UB; that execution cannot prove or refute a defined postcondition. | PROVED ordinary / UNPROVED special |

This also proves build-script source soundness: it contains no unsafe operation,
and all branches use safe std APIs; its documented rejection behavior is
covered by O-01.

## F-01 — supported safe call violates `NonZeroU8` validity

- **Affected claim/configuration:** public safe `lane_id`, all profiles/debug
  states under `aarch64-unknown-linux-gnu` + `arena` + enabled `burst`.
- **Proof artifact:** `lib.rs:30` says burst-mode identifiers are never zero.
  That is an unsupported assertion about an arbitrary safe caller's `u8`, not
  an invariant, check, type fact, or postcondition. The smallest false
  implication is “this cfg conjunction and caller input imply `value != 0`.”
- **UB witness:** BUILD-MAP-X makes lines 24-32 active and lines 34-45 absent.
  A safe caller invokes `lane_id(0)`; line 31 calls `new_unchecked(0)`, which
  AXIOM-NZ classifies as UB. No caller-side safety obligation exists.
- **Defined postcondition refutation:** not established; the witness contains
  UB. Hence soundness is `UNSOUND` and the special-tuple panic postcondition is
  `UNPROVED`.
- **Minimum repair:** remove the special case and use the checked path, or make
  a zero check dominate line 31 (prefer safe `NonZeroU8::new(value)` plus the
  documented panic). A comment-only or documentation-only change cannot repair
  a safe API with a hidden safety precondition. After a check, suitable proof
  text is: “Reaching this call means the preceding zero branch panicked, so
  `value != 0`, satisfying `new_unchecked`'s safety precondition.” Re-audit all
  ten tuples; the repair restores rather than weakens the published panic
  behavior.

## Residual scope and review triggers

Excluded: unlisted targets, Rust/Cargo/std versions other than 1.85.1, manual
cfg injection, and compiler/backend/binary behavior. No tool evidence was used.
Review is invalidated by any source, manifest, support/build policy, allocator
mapping, feature/target set, relevant Rust documentation, or BUILD-MAP-X change.
Every in-scope surface, unsafe site, supported tuple class, mandatory documented
behavior, and enforced exclusion has a disposition above; independent review
was not performed.
