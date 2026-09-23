# Unsafe Rust audit: `cross-axis-target` 0.1.0

## Claim, snapshot, and verdicts

Audit date/cutoff: 2026-08-01. Snapshot: the complete supplied `Cargo.toml`, `build.rs`, `BUILD.md`, `SUPPORT.md`, `TCB.md`, `src/lib.rs`, and `REQUEST.md`; no expansion, build, execution, tests, prior audit, dependency resolution, or repository metadata was used. Rust, Cargo, and standard library are exactly 1.85.1; edition 2021. Scope is source-level Rust abstract semantics, the build interface and rejection behavior, the sole public safe API, both unsafe calls, and documented panic behavior. There are no third-party dependencies or generated source; the build script generates cfg options.

Let

`Required(c) := rust=cargo=stdlib=1.85.1 ∧ Cargo/build.rs is used ∧ target∈{x86_64-linux-gnu,aarch64-linux-gnu,wasm32-unknown} ∧ burst∈{off,on} ∧ allocator∈{system,arena} ∧ ¬(target=wasm32-unknown ∧ allocator=arena) ∧ profile is any Cargo profile ∧ debug_assertions∈{off,on}`.

Successful build-script stdout is implicit; accepted `BUILD-MAP-X` says a write/script failure produces no library compilation and hence no `Required` configuration. Let `H := burst=on ∧ target=aarch64-linux-gnu ∧ allocator=arena`.

| Claim | Verdict | Certificate |
|---|---|---|
| Every well-typed safe `lane_id(v)` use is UB-free for every `c∈Required` and `v:u8` | **UNSOUND** | `H∈Required`; safe `lane_id(0)` reaches `NonZeroU8::new_unchecked(0)`, whose 1.85.1 contract says this is UB. |
| “Panics when `value` is zero” over every `c∈Required` | **UNPROVED** | Proved for `Required\H`; in `H`, the zero call reaches UB instead. That UB-containing execution cannot certify `CONTRACT-BROKEN`, and no UB-free refutation exists in the snapshot. |
| Soundness on `(Required\H)×u8 ∪ H×{1..=255}` | **PROVED**, relative to the TCB below | Exhaustive cfg/input partition and OBL-3/OBL-4 below. |
| Documented selector and excluded-pair rejection | **PROVED**, relative to `BUILD-MAP-X` | OBL-1/OBL-2 below. |

Combined mandatory result: **UNSOUND** for soundness and **UNPROVED** for the zero-input panic guarantee.

## Domain and configuration closure

`SUPPORT.md:3-16` supplies the exact singleton toolchain, three targets, two feature states, two allocators, all profiles/debug-assertion states, and the sole excluded cross-product member. `BUILD.md:3-14` restricts support to Cargo plus `build.rs` and defines selector normalization: absent or `system`→system; `arena`→arena; everything else rejected. This is preserved symbolically above, not inferred from samples.

`build.rs:9-21` implements that three-way mapping: [`env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html), `NotPresent`/`NotUnicode`, [`str::to_owned`](https://doc.rust-lang.org/1.85.1/std/primitive.str.html#impl-ToOwned-for-str), [`String::as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str), literal/or/wildcard matching, and named formatting select one accepted string or [`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html). `BUILD-MAP-X` alone admits Cargo’s execution, rerun, directive, feature, target-cfg, and failed-script mapping; it admits no local correctness.

For every accepted selector, exactly one `rustc-cfg` line is reached. `src/lib.rs:3-13` rejects neither/both allocator cfgs. `src/lib.rs:15-16` rejects wasm32+arena. Under the [cfg-attribute rule](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute), a true predicate retains the [`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html), which makes compilation fail. Within the controlling supported target predicate, successful library compilations are exactly `Required`; `H` is included (aarch64, arena, burst is not excluded). Profile/debug/panic strategy do not select source or alter `new_unchecked`'s precondition; panic abort versus unwind does not affect the proved panic initiation.

Aggregate `Covered` for soundness is `(Required\H)×u8 ∪ H×{1..=255}`. Because `H×{0}⊆Required×u8` but is not covered—and is affirmatively refuted—`Required×u8 ⊄ Covered`.

## Boundary, invariant, and obligation ledger

The full language-reachable crate surface is: safe public free function `lane_id(u8)->NonZeroU8`; its return type’s standard safe behavior; build-script entrypoint/environment input; cfg-generated variants; two private unsafe calls. There are no public fields/types/traits/statics/macros, callbacks, FFI, impls, reexports, hidden items, mutable state, allocator operations, or destruction/concurrency invariants. `INV-NZ` is local: immediately before either `new_unchecked(value)`, `value≠0` must hold; the unsafe call consumes it and returns a valid `NonZeroU8`.

| ID | Site and exact obligation | Proof/status |
|---|---|---|
| OBL-1 | `build.rs`: map every documented selector, emit exactly one value, reject every other value | Direct exhaustive `Result` and string-match cases; emitted-line propagation/failure is exactly accepted `BUILD-MAP-X`. **PROVED**. |
| OBL-2 | cfg closure and wasm32+arena rejection | Two allocator predicates are total/exclusive under OBL-1; target/feature mapping is `BUILD-MAP-X`; active `compile_error!` rejects the excluded pair. **PROVED**. |
| OBL-3 | `src/lib.rs:40-44`: establish `value≠0` | For `Required\H`, this is the active block. Rust [integer equality](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators) plus [`if`](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html) partitions `value=0` (panic) from `value≠0` (call). The adjacent comment states the complete material derivation. **PROVED** for all such configurations/inputs. |
| OBL-4 | `src/lib.rs:29-31`: establish `value≠0` | In `H` this unconditional block is active. No type, check, boundary, or accepted TCB premise constrains safe input. False for `value=0`; true for 1..=255. **UNSOUND witness below**. |
| OBL-5 | `src/lib.rs:22`: zero always panics | OBL-3 proves it outside `H`; OBL-4 prevents a defined proof in `H`. **UNPROVED** globally. |

The Rust 1.85.1 `NonZero::new_unchecked` contract states: “This results in undefined behavior if the value is zero” and requires that the value not be zero ([authoritative page](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)). It also establishes the nonzero result needed by the return type when its precondition holds.

## Finding F-1 — supported safe call reaches UB

- **Status:** critical; implementation **UNSOUND**; safety comment deficient and false.
- **Valid use:** choose supported `H`; call public safe `lane_id(0)` from well-typed safe Rust. A safe API has no caller safety precondition.
- **Reachability:** `BUILD-MAP-X` establishes all three true cfg atoms. Conditional compilation retains `src/lib.rs:24-32` and removes `:34-45`; the function executes `new_unchecked(value)` with `value=0`.
- **False proposition:** OBL-4 requires `value≠0`; `0≠0` is false.
- **UB consequence:** the cited 1.85.1 std contract expressly makes zero UB. This closes every existential `UNSOUND` link.
- **Proof defect:** “Burst-mode lane identifiers are never zero” reverses no enforced producer contract and is contradicted by the unrestricted `u8` parameter.
- **Minimum repair:** perform the zero check in every configuration (prefer `NonZeroU8::new(value).expect(...)`), or remove `H` from support and effectively reject it. Replace the comment with the actual dominating-check derivation. Re-audit source, panic behavior, domain closure, and compatibility; narrowing support is a policy change.
- **Postcondition:** the same execution is UB-containing, so it does not establish `CONTRACT-BROKEN`; absent a separate UB-free witness, OBL-5 remains `UNPROVED`.

## TCB audit log

| ID | Category/disposition | Exact admitted proposition; scope; consumer; trigger |
|---|---|---|
| BUILD-MAP-X | OUT-OF-BAND/IMPLEMENTATION; **accepted by authorized human** | Exactly `TCB.md:5-32`, Cargo 1.85.1 mapping/failure proposition only; all `Required`; OBL-1/2 and F-1 reachability; trigger is any named toolchain/manifest/script/interface/target/cfg/disposition change. |
| AXIOM-NZ-1.85.1 | AXIOM; verified | Exact quoted `new_unchecked` zero precondition/UB and valid-result contract; Rust/std 1.85.1; OBL-3/4 and F-1; trigger: toolchain or cited documentation change. |
| AXIOM-CFG-1.85.1 | AXIOM; verified | Applicable cfg attributes remove/retain attributed constructs; active `compile_error!` fails compilation; Rust 1.85.1; OBL-2/3/4; trigger: toolchain/docs/source predicate change. |
| AXIOM-CONTROL-1.85.1 | AXIOM; verified | Applicable equality/if/panic semantics used in OBL-1/3/5; Rust/std 1.85.1; trigger: toolchain/docs/control-flow source change. |

No dependency, backend, binary, tool-result, allocator-implementation, deployment, or compatibility premise is consumed. No TCB proposition was widened beyond `TCB.md`.

## Rejected, residual, and review triggers

Invalid/non-Unicode selectors are rejected by build-script panic; wasm32+arena is rejected at library compilation; missing or simultaneous allocator cfgs are likewise compile errors but arise only from out-of-interface manual rustc use. Other targets, invented cfgs, other Rust/Cargo versions, and manual rustc builds are unsupported, not proved rejected. Build-script stdout failure yields no compiled artifact under accepted `BUILD-MAP-X`. Binary/backend correctness is outside this source theorem. No tool-derived evidence exists.

Re-audit on any source/documentation change; support, target, feature, profile, selector, or cfg change; Rust/Cargo/std or cited-contract change; `BUILD-MAP-X` disposition/scope change; or newly exposed API/generated artifact. Every in-scope obligation and rejected region has a disposition; no tests or absence-of-counterexample reasoning supports a verdict.
