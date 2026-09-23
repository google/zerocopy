# Source-only unsafe-code audit

## Claim, scope, and verdict

**Snapshot:** the supplied `Cargo.toml`, `build.rs`, `BUILD.md`, `SUPPORT.md`, `TCB.md`, `src/lib.rs`, and `REQUEST.md`, audited 2026-08-01. Rust and standard library are exactly 1.85.1. There are no dependencies or generated source files. The build script generates only a library configuration option.

**Claim:** for every successful library compilation in the supported domain, every well-typed safe use of the public API is free of Rust undefined behavior and its documented behavior holds, relative only to accepted TCB entry `BUILD-MAP-X` and the cited Rust 1.85.1 semantics.

| Component | Verdict | Certificate |
|---|---|---|
| Safe-API soundness over the complete supported domain | **UNSOUND** | Finding F-1 gives a valid supported safe call, reaches `new_unchecked(0)`, proves its precondition false, and cites the resulting UB contract. |
| Soundness outside `aarch64 + burst + arena` | **PROVED** | OBL-U2 below; the zero check dominates the only unsafe call in this region. |
| Documented “panics when `value` is zero” behavior over the complete domain | **UNPROVED** | It is established outside F-1’s configuration, but the only zero-input execution established in F-1 has UB. Such an execution is not an UB-free `CONTRACT-BROKEN` witness. |
| Required policy rejection | **PROVED** | Every `wasm32 + arena` combination encounters `compile_error!`; invalid allocator selectors make the build script fail before library compilation. |

Thus the strongest complete-domain result is **UNSOUND**. This is a source-level result, not a compiler-backend or binary claim.

## Required domain and closure

Let:

- `T = {x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu, wasm32-unknown-unknown}`;
- `B = {burst disabled, burst enabled}`;
- `A = {system, arena}`;
- `P` be every Cargo profile and `D = {debug assertions off, on}`.

From `Cargo.toml`, `SUPPORT.md`, and `BUILD.md`, normalized without enumeration loss:

`Required = Rust 1.85.1 × {(t,b,a,p,d) in T×B×A×P×D | not(t=wasm32-unknown-unknown and a=arena)}`,

restricted to Cargo builds using the supplied build script whose stdout writes succeed. The latter restriction is exactly `TCB.md`’s execution scope; a write failure produces no library compilation and is not a policy rejection. `BUILD.md` excludes manual `rustc` cfg invention.

`BUILD-MAP-X` is accepted exactly as written: Cargo maps the script’s emitted allocator cfg, feature `burst`, and the three triples to their stated cfgs; `rustc-check-cfg` declares but does not set values; unsuccessful scripts halt before library compilation. No source-correctness or Rust-semantic proposition is imported from it.

Source inspection proves the remaining mapping. `env::var` partitions into present Unicode, absent, and non-Unicode cases. Absence produces `"system"`; exact string matches `system|arena` emit exactly one corresponding cfg; every other Unicode string and non-Unicode input panics. On successful writes, `BUILD-MAP-X` therefore gives exactly one allocator cfg. The code has no profile/debug-assertion conditional and no `debug_assert!`, so all `P×D` cases share the same proof.

The Rust Reference states that a cfg option predicate is true exactly when set, `all` requires all operands, and `not` negates its operand ([conditional compilation](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#conditional-compilation)). It also states conditionally compiled source is compiled only under its condition. Consequently the two `lane_id` blocks form an exhaustive complementary partition. Define

`Bad = Required ∩ {t=aarch64-unknown-linux-gnu, b=enabled, a=arena}`.

The proof below covers `Required \ Bad`; F-1 existentially refutes soundness on `Bad`. Profiles and debug assertions remain parametric in both cases.

## Build rejection proof

For `t=wasm32-unknown-unknown, a=arena`, `BUILD-MAP-X` sets `target_arch="wasm32"` and `fixture_allocator="arena"`; hence the third top-level cfg is true for both feature states and all profiles/debug states. `compile_error!` “causes compilation to fail ... when encountered” ([Rust 1.85.1 documentation](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)), so the mandated excluded pair cannot produce the library.

Invalid or non-Unicode `FIXTURE_ALLOCATOR` values reach a `panic!`; `BUILD-MAP-X` then halts before library compilation. Omitted, `system`, and `arena` are the complete accepted selector interface. The first two top-level `compile_error!` items additionally reject missing or simultaneously set allocator cfgs, although accepted Cargo builds cannot generate them. Other targets and manual cfg injection are outside `Required`, not silently proved. A build-script stdout failure is an infrastructure failure with no compiled configuration, per the TCB, not another selector or successful rejection.

## Boundary, invariant, and obligation coverage

The complete public Rust surface is the safe function `lane_id(u8) -> NonZeroU8` (`src/lib.rs:23`). There are no public fields, traits or impls, macros, statics, callbacks, hidden items, generated APIs, custom destruction, FFI, concurrency, assembly, or allocator operations. `build.rs::main` is the complete build interface. The only unsafe operations are the two cfg-disjoint `NonZeroU8::new_unchecked(value)` calls.

`INV-NZ`: each value returned as `NonZeroU8` must have a nonzero integer value. Its producer/consumer boundary is each `new_unchecked` call; the unsafe function requires its argument to be nonzero.

| ID | Site/domain | Required proposition | Derivation and status |
|---|---|---|---|
| OBL-U1 | `src/lib.rs:31`, `Bad` | `value != 0` before `new_unchecked` | No check, type restriction, or caller precondition exists. False for safe input `0`. **UNSOUND**, F-1. |
| OBL-U2 | `src/lib.rs:40-44`, `Required \ Bad` | `value != 0` before `new_unchecked` | If `value == 0`, `panic!` prevents reaching line 44; reaching line 44 therefore entails `value != 0`. This satisfies the exact callee contract and establishes `INV-NZ`. **PROVED**. |
| OBL-PANIC | documented `# Panics` clause | every zero input panics | Proved by the dominating branch on `Required \ Bad`; unresolved on `Bad` because the reached operation has UB. **UNPROVED**, not `CONTRACT-BROKEN`. |
| OBL-CFG | build/policy boundary | exactly supported cfgs compile; excluded pair fails | Build-script partition, `BUILD-MAP-X`, complementary cfgs, and `compile_error!` proof above. **PROVED**. |

The local comment for OBL-U2 is an adequate compact proof. OBL-U1’s comment—“Burst-mode lane identifiers are never zero”—is not a derivation: `value` is an unrestricted argument to a safe function, and no earlier producer or check establishes that assertion.

## F-1 — supported safe call invokes `new_unchecked(0)`

- **Affected theorem:** complete-domain safe-API soundness.
- **Valid in-scope use:** select target `aarch64-unknown-linux-gnu`, enable `burst`, select `arena`, use any Cargo profile/debug state, then safe code calls `lane_id(0)`. `SUPPORT.md` includes this combination, and the safe signature imposes no caller safety precondition.
- **Reachability:** `BUILD-MAP-X` sets all three predicates of the first `cfg(all(...))`. The first block is compiled, its complementary block is not, and the function immediately executes `NonZeroU8::new_unchecked(value)`.
- **False safety proposition:** at that operation `value == 0`, while the contract says, “The value must not be zero.”
- **UB consequence:** Rust 1.85.1 documents that `new_unchecked` “results in undefined behavior if the value is zero” ([exact API contract](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)). This completes the existential `UNSOUND` certificate.
- **Proof artifact:** incorrect; it reverses an unsupported assertion into an invariant.
- **Minimum repair:** remove the special unchecked branch and use the already guarded implementation in every configuration (or use checked `NonZeroU8::new(value)` and panic on `None`). Replace the special comment with the OBL-U2 derivation. This preserves the public panic contract and configuration policy. The changed snapshot needs a fresh full-domain audit.

## Authority and TCB log

- **Accepted TCB:** only `BUILD-MAP-X`, exact identity/scope/disposition from `TCB.md`; consumers are domain reachability and rejection. Re-audit on any trigger listed there. It is not widened.
- **Rust axioms:** the versioned `new_unchecked`, cfg, and `compile_error!` passages cited above. Build-script control flow uses the allowlisted Rust 1.85.1 contracts for [`env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html), [`String::as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str), [match expressions](https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html), [literal/or/wildcard patterns](https://doc.rust-lang.org/1.85.1/reference/patterns.html#literal-patterns), and [`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html).
- **Tools/tests:** none; no target code was built, run, tested, or expanded.

## Residual scope and review triggers

Excluded are unsupported targets, Rust versions other than 1.85.1, direct `rustc`/invented cfgs, backend/binary behavior, and build attempts producing no library after script failure. Re-audit on source, public contract, support policy, Cargo/toolchain, build environment interface, cfg mapping, target/feature/profile scope, TCB disposition, or material cited-documentation changes.
