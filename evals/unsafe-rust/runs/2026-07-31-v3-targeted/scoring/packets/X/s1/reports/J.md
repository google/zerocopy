# Unsafe Rust source audit: supplied crate snapshot

## Claim and verdicts

Audit cutoff: 2026-08-01. The artifact is exactly the supplied `Cargo.toml`,
`build.rs`, `BUILD.md`, `SUPPORT.md`, `TCB.md`, `REQUEST.md`, and `src/lib.rs`;
no expansion, build, execution, test, prior audit, dependency resolution, or
generated file was used.

**SOUND — UNSOUND.** For Rust/standard library 1.85.1, the complete crate is
not free of Rust undefined behavior for every well-typed safe use over
`Required` below, relative only to accepted TCB entry `BUILD-MAP-X` and the
version-matched Rust axiom `AXIOM-NZ`. Finding F-1 is a complete existential
certificate.

**POST-PANIC — UNPROVED over `Required`; PROVED over `Required ∧ ¬Bad`.** The
documented safe-API guarantee “Panics when `value` is zero” holds outside
`Bad`. In `Bad`, the zero call has UB, so it cannot be a UB-free
`CONTRACT-BROKEN` witness. No independent UB-free refutation is established.

Thus the strongest combined result over the complete supported domain is
**UNSOUND**, with the documented zero-input behavior additionally **UNPROVED**.

## Snapshot, domain, and closure

The manifest fixes edition 2021, Rust 1.85.1, no dependencies, feature set
`{burst}`, and this build script/library. Let

```text
T = {x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu,
     wasm32-unknown-unknown}
A = {system, arena}
Required(t,b,a,p,d) = t∈T ∧ b∈{off,on} ∧ a∈A
                      ∧ ¬(t=wasm32-unknown-unknown ∧ a=arena)
                      ∧ p is any Cargo profile ∧ d∈{off,on}.
Bad = Required ∧ t=aarch64-unknown-linux-gnu ∧ b=on ∧ a=arena.
Good = Required ∧ ¬Bad.
```

This is an equality normalization of `SUPPORT.md:3-16`: the three listed
targets, both feature states, both BUILD-selected allocators, the single
wasm/arena exclusion, every profile, and either debug-assertion state.
`BUILD.md:3-14` restricts supported selection to Cargo plus `build.rs`:
missing/`system` selects system, `arena` selects arena, and other values are
rejected. Invented cfgs and manual rustc are outside `Required`.

`build.rs:9-21` exhaustively maps `env::var`: absence creates `system`; the two
exact accepted strings emit one allocator cfg; non-Unicode or any other string
panics. `BUILD-MAP-X` establishes Cargo's exact propagation of emitted
allocator cfg, `burst`, and each target architecture, and establishes that a
failed script/output write yields no library compilation. The `rustc-check-cfg`
line declares but does not set values. Therefore accepted builds reach exactly
one allocator selector. This uses the version-matched [`env::var`
contract](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html).

The only unsafe-code selector is `Bad` (`src/lib.rs:24-38`). No profile,
debug-assertion, optimization, panic-strategy, allocator implementation, or
other target property affects either unsafe operation. Hence the proofs below
are parametric in those axes: `Covered(SOUND)=Good`, while F-1 refutes SOUND on
`Bad`; `Good ∪ Bad = Required`.

## Boundary, API, and invariant inventory

The complete language-reachable project surface is build entrypoint `main`
with `FIXTURE_ALLOCATOR`, compile-time cfg gates, and the one public safe
function `lane_id(u8) -> NonZeroU8`. There are no public fields, project types,
unsafe APIs/traits/impls, macros, callbacks, statics, FFI, assembly, generated
source, or hidden APIs. The only unsafe operations are
`NonZeroU8::new_unchecked` at `src/lib.rs:31` and `:44`.

Invariant `INV-NZ`: immediately before either unsafe constructor, its argument
must be nonzero. It is local to `lane_id`; there is no persistent
invariant-bearing representation. The Rust 1.85.1 contract says “The value must
not be zero” and that zero produces UB
([`NonZero::new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)).

## Obligation ledger

| ID | Site/domain | Required proposition | Derivation/status |
|---|---|---|---|
| O-CFG | build/configuration | Exact supported reachability and exclusions | Source mapping plus accepted `BUILD-MAP-X`; proved. |
| O-31 | `lib.rs:31`, `Bad` | `value != 0` | False for safe input 0; **UNSOUND**, F-1. |
| O-44 | `lib.rs:44`, `Good` | `value != 0` | The active branch executes `panic!` when `value == 0`; reaching line 44 therefore entails nonzero ([comparison](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators), [`if`](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html)). Proved for every `Good` case. |
| O-PANIC | `lane_id(0)` | Panic | `Good`: explicit [`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html), proved. `Bad`: UB witness, postcondition unproved. |

Line 43's adjacent proof is sufficient: the dominating zero branch and
control flow establish the exact constructor precondition. Line 30's comment
is deficient and false: neither the `u8` type nor any check constrains the safe
argument in burst mode.

## F-1 — supported safe call invokes `new_unchecked(0)`

- **Status:** UNSOUND implementation; missing/invalid proof artifact; affects
  SOUND and POST-PANIC.
- **Configuration:** Rust 1.85.1,
  `aarch64-unknown-linux-gnu`, `burst=on`, allocator `arena`, any Cargo profile
  and either debug-assertion state. `SUPPORT.md` includes it, `BUILD.md` permits
  `FIXTURE_ALLOCATOR=arena`, and `BUILD-MAP-X` proves the cfg mapping. It is not
  the excluded wasm/arena pair.
- **Valid use:** downstream safe Rust calls public safe `lane_id(0)`; the API
  has no safety precondition.
- **Reachability:** the configuration includes `lib.rs:24-32` and excludes
  `:34-45`; line 31 is executed before return, without testing `value`.
- **False proposition:** the argument to `new_unchecked` is exactly zero,
  contradicting `AXIOM-NZ`'s safety requirement.
- **UB consequence:** the same authoritative Rust 1.85.1 documentation states
  that zero “results in undefined behavior.” This completes the existential
  certificate; it does not depend on backend behavior or testing.
- **Postcondition:** that execution is not UB-free, so it establishes no
  `CONTRACT-BROKEN` verdict.
- **Minimal repair:** remove the special unchecked branch and use the checked
  path in every configuration (or `NonZeroU8::new(value).expect(...)`). Replace
  line 30 with the actual dominating-check derivation. Re-audit both unsafe
  sites and the panic guarantee after the change.

## Rejected and residual configurations

For accepted `arena` plus `wasm32-unknown-unknown`, `BUILD-MAP-X` makes both cfg
predicates true and `lib.rs:15-16` activates `compile_error!`; this exactly
enforces SUPPORT's sole supported-set exclusion
([cfg](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute),
[`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)).
Invalid Unicode/other allocator values fail in `build.rs`, and `BUILD-MAP-X`
ensures no library compilation. Neither/both allocator cfgs are also rejected
by `lib.rs:3-13`, but can arise only through out-of-scope invented cfgs under
the documented interface. Unlisted targets, manual rustc, future Rust/Cargo,
and invented flags are unsupported, not claimed rejected, and outside the
theorem.

## TCB audit log and evidence

- **BUILD-MAP-X (accepted OUT-OF-BAND/IMPLEMENTATION premise):** exactly the
  Cargo 1.85.1 proposition and scope in supplied `TCB.md:3-32`; consumed only
  by O-CFG and F-1 reachability/rejection. It admits no script behavior, Rust
  semantics, backend, or binary claim and is not widened here. Re-audit on any
  listed identity/source/interface/target/disposition change.
- **AXIOM-NZ (Rust axiom):** exact Rust 1.85.1 `new_unchecked` nonzero
  precondition and zero-UB consequence; consumed by O-31/O-44/F-1. Re-audit if
  the supported Rust or authoritative contract changes.

No dependency, tool-derived, test, generated-artifact, external ABI,
deployment, probabilistic, or binary premise is consumed. Source-level Rust
semantics only. Review must recur on source/docs, support/build interface,
feature/target/profile scope, Cargo/Rust identity, generated cfg mapping, TCB
disposition, or `NonZero` contract changes. Every discovered obligation and
documented behavior has a disposition above.
