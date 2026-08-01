# Focused source-only audit of `lib.rs`

## Claim, snapshot, and verdicts

The audited artifact is exactly `lib.rs` SHA-256
`705278735813eeafd774bc4b032994b7727d5e6740c836f0f7236aa2fc06bde1`.
Scope is its sole public safe API, `classify(u8) -> u8`. `Supported(C)` means:
this exact source; Rust compiler and standard library 1.80.0; every target on
which this source and `std::hint::unreachable_unchecked` exist; and every
ordinary debug or release profile. This is a Rust source-level result, not a
compiler-backend or binary theorem. TCB identity is embedded log `TCB-R1` below.

1. **Freedom from UB: UNSOUND in every supported configuration.** The claimed
   theorem is that every well-typed safe call, for every `u8` input, is free
   from Rust UB. The valid safe call `classify(0)` refutes it.
2. **Input-zero panic guarantee: UNPROVED in every supported configuration.**
   The claim is that every call with `input == 0` panics. Its only source path
   reaches UB. That UB-containing execution proves unsoundness, but cannot be a
   UB-free witness that the panic postcondition is false; therefore it does
   **not** establish `CONTRACT-BROKEN`.
3. **Normal-return result guarantee: CONTRACT-BROKEN in every supported
   configuration.** The UB-free witness `classify(1)` normally returns `2`, and
   `2 != 1`.

The combined mandatory result is `UNSOUND` + panic guarantee `UNPROVED` +
normal-return guarantee `CONTRACT-BROKEN`.

## Boundary, configuration, and obligation coverage

The complete language-reachable surface is the safe free function `classify`.
There are no public fields, constructors, user-defined types or traits, hidden
items, callbacks, FFI, macros, generated artifacts, dependencies other than
`std`, conditional compilation, features, concurrency, allocation, or
invariant-bearing state. The `allow(dead_code)` attribute and `marker` local do
not affect control flow or safety. The only unsafe site is
`unreachable_unchecked()` at `lib.rs:12`.

The input partition is exhaustive for `u8` and supplies the obligation ledger:

| Input | Source derivation | UB status | Applicable postcondition result |
|---|---|---|---|
| `0` | The `0` arm is selected; the two inert `marker` statements complete; execution reaches `unreachable_unchecked()` unconditionally. | UB by `AXIOM-UU`; this is the exact safe-call witness for `UNSOUND`. | It cannot establish either a defined failure to panic or a defined normal return. The panic claim remains `UNPROVED`. |
| `1` | The distinct `1 => 2` arm normally returns `2`; it executes no unsafe operation and no panic. | UB-free relative to an otherwise defined safe calling context. | Exact UB-free witness for `CONTRACT-BROKEN`: normal result `2` differs from input `1`. |
| `2..=255` | The `_ => input` arm normally returns that input and executes no unsafe operation. | UB-free relative to an otherwise defined safe calling context. | The normal-return guarantee is satisfied for each of these inputs. |

`OBL-UU` is the intrinsic's requirement that its call site not be reached.
`classify(0)` proves the required proposition false. The adjacent comment,
“This branch is assumed to be unreachable,” is not a proof and directly
contradicts the enclosing match arm. `OBL-SOUND` therefore fails. `OBL-PANIC`
cannot be proved from an execution after UB. `OBL-RETURN` is independently
refuted by the defined input-`1` execution.

This partition is parametric over every supported target and profile: the
source has no configuration selection, and optimization/debug settings do not
alter the Rust 1.80.0 abstract contract that reaching the intrinsic is UB or
the source-level selection of the `0`, `1`, and catch-all arms. Thus the union
of the three cases closes the requested configuration domain without sampling.

## TCB-R1 and authority

| ID | Accepted Rust 1.80.0 proposition | Scope and consumers | Disposition |
|---|---|---|---|
| `AXIOM-UU` | The standard-library Safety section states: “Reaching this function is *Undefined Behavior*.” ([Rust 1.80.0 documentation](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)) | Every supported target/profile where the item exists; `OBL-UU`, `OBL-SOUND`, `OBL-PANIC`. | Accepted: exact request-selected authority independently opened and verified. |
| `AXIOM-REF` | The Reference says unsafe code is unsound when safe code can trigger UB, and lists “Invoking undefined behavior via compiler intrinsics.” ([Rust 1.80.0 Reference](https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html)) | Rust 1.80.0 source semantics; aggregation of `OBL-SOUND`. | Accepted: exact request-selected authority independently opened and verified. |

No external, implementation, dependency, tool, deployment, probabilistic, or
out-of-band premise is consumed. No tests, execution, compilation, expansion,
or tool-derived proof was used. The TCB must be revisited if either cited
contract or the supported Rust/target/profile predicate changes.

## Findings and minimum resolution

### F-01 — reachable `unreachable_unchecked`

- **Status:** `UNSOUND`; proof artifact deficient.
- **Witness:** the well-typed safe call `classify(0)`, in every supported
  configuration.
- **Defect:** the required implication `input == 0 implies this arm is
  unreachable` is false; the condition instead selects the arm.
- **Resolution:** replace the UB path with a defined panic. Remove the false
  `SAFETY` comment and unsafe call.

### F-02 — input-zero panic is not established

- **Status:** `UNPROVED`, not `CONTRACT-BROKEN`.
- **Evidence classification:** `classify(0)` reaches UB before any panic. As an
  execution containing UB, it establishes F-01 but cannot establish the
  required UB-free existential refutation of this behavioral contract.
- **Resolution:** implement a defined panic in the zero arm, then re-audit.

### F-03 — normal return changes input one

- **Status:** `CONTRACT-BROKEN`; implementation behavior is defined on this
  witness and the documentation is unambiguous.
- **Witness:** `classify(1)` selects `1 => 2` and normally returns `2` without
  executing unsafe code; hence it is an independent UB-free refutation.
- **Resolution:** return `input` in the `1` arm (or remove that special arm).

There is no authoritative-documentation gap in the propositions needed for
these conclusions. Excluded residual scope is compiler/backend correctness and
binary behavior. Re-audit on any source, contract, Rust version, supported-set,
or cited-authority change. Every in-scope surface, input, obligation, and
requested postcondition has the status recorded above.
