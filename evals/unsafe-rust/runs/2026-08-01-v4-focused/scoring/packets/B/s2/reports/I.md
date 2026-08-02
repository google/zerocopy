# Unsafe Rust audit: supplied `ordered-build-target` snapshot

Audit cutoff: 2026-08-01. This is a source-level Rust 1.85.1/standard-library
1.85.1 audit of the supplied manifest, policies, `TCB.md`, `build.rs`, and
`src/lib.rs`; no backend or binary claim is made. No dependency, generated
file, test, prior audit, or tool result is present or used.

## Claims and verdicts

* **Safe-library soundness: UNSOUND.** A supported, well-typed safe call reaches
  `NonZeroU8::new_unchecked(0)` (certificate `BAD` below).
* **Documented panic postcondition: UNPROVED**, not `CONTRACT-BROKEN`. It is
  proved wherever its antecedent is relevant outside `BAD`; in `BAD`, the only
  source execution already has undefined behavior, so it cannot be the required
  UB-free postcondition witness.
* **Ordered build interface and exclusion: PROVED relative to the accepted
  `BUILD-MAP-ORDERED` premise.** This includes all raw-selector classes, write
  failures, partial prefixes, current-build rejection, and the stated
  arena-to-arena-stop freshness sequence.

The combined mandatory result is therefore **UNSOUND / postcondition
UNPROVED**, relative only to `TCB.md`'s accepted, exact Cargo premise and the
Rust axioms quoted below.

## Exact domain and its recovery

Let

* `T={x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu,
  wasm32-unknown-unknown}`, `B={off,on}`, `A={system,arena}`;
* `P` be every Cargo profile and `D={debug_assertions off,on}`; and
* `U={0,...,255}`, exactly the values of `u8`.

`SUPPORT.md` literally defines the base product `C0=T×B×A×P×D` and the sole
exclusion `E={c∈C0 | c.target=wasm32-unknown-unknown ∧ c.allocator=arena}`.
Thus the supported library predicate is exactly `C=C0\E`: `C⊆C0\E` follows
from “every other combination ... is supported,” and `C0\E⊆C` follows from
the same exhaustive product statement; the single exclusion proves the reverse
nonmembership. Rust/Cargo are exactly 1.85.1 and the edition is 2021.

The raw environment partition is the disjoint, exhaustive set
`R={absent, U("system"), U("arena"), U("arena-stop"), U(other), non-U}`.
Here `U(other)` means every other Unicode string. `env::var` “Returns a
`VarError` if the variable is not present, or if it is not valid Unicode”
([Rust 1.85.1 `env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html));
the two documented error variants and the `Ok(String)` case, followed by
equality with the three literals and `_`, prove both coverage and disjointness.
`String::as_str` “Extracts a string slice containing the entire `String`”
([1.85.1](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str)).
Accepted fibers are `absent,U("system") -> system` and `U("arena") -> arena`;
the other three are rejection cases, not allocators. Manual `rustc`, invented
cfgs, and build-script overrides are expressly outside `BUILD.md`'s theorem.

The full required case domain is (i) every build-interface execution over `R`,
the supported target/feature/profile/debug axes, each stdout success/failure
possibility, and reusable prior Cargo-target state, plus (ii) every safe
`lane_id(v)` call for `(c,v)∈C×U` produced by an accepted current build. This
retains inputs, execution/history, and configuration rather than replacing
them by `Required_cfg=C`.

## Complete ordered build relation

Write `RERUN` for the complete first line and `CFG(a)` for the allocator line.
Blocks execute operations sequentially and a match chooses the first matching
arm ([block](https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html),
[match](https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html)).
`println!` “Panics if writing to `io::stdout` fails”
([1.85.1](https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics)).
Consequently:

| Raw class | after successful `RERUN` write | terminal result if later writes succeed |
|---|---|---|
| absent | read `NotPresent`; attempt `CFG(system)` | return success |
| `U("system")` | read `Ok`; attempt `CFG(system)` | return success |
| `U("arena")` | read `Ok`; attempt `CFG(arena)` | return success |
| `U("arena-stop")` | read `Ok`; attempt `CFG(arena)` | explicit panic after that complete line |
| `U(other)` | read `Ok`; no allocator write | explicit unsupported-value panic |
| non-U | read `NotUnicode`; no allocator write | explicit valid-Unicode panic |

This table lists every successful script path: exactly its first three rows.
Before every row, failure of the first write exits by panic with no complete
line (and possibly a byte-prefix of `RERUN`); the environment read and all later
steps are unreached. In the four rows that attempt `CFG`, failure of that second
write exits by panic after complete prefix `[RERUN]` (and possibly a byte-prefix
of `CFG`); its return or explicit later panic is unreached. The successful
`arena-stop` write produces complete prefix `[RERUN,CFG(arena)]` before its
explicit panic. The other explicit rejections leave complete prefix `[RERUN]`.
These are all stdout calls and all alternative exits in `build.rs`.

`BUILD-MAP-ORDERED` supplies, for Cargo 1.85.1 and every profile, exactly the
following consumed facts: a complete successful `RERUN` registers changes in
the raw value (including present-to-present); only a successful current script's
complete `CFG(a)` reaches the current library compilation; no prior selector is
retained; any write failure or uncaught explicit panic is unsuccessful; and an
unsuccessful script yields no current library or prior artifact as the current
result. Therefore arbitrary failed-write byte prefixes and every complete
prefix above are inert for source selection.

**Freshness witness.** For a successful arena build (necessarily x86_64 or
aarch64 once the source exclusion is applied), the first run successfully wrote
`RERUN,CFG(arena)`. In the same target directory, raw `arena -> arena-stop` is a
registered present-to-present change, so Cargo reruns before selection. The new
run either fails at write 1, fails at write 2, or writes both lines and then
panics. Every exhaustive case is unsuccessful and `BUILD-MAP-ORDERED` forbids
both a current compilation and presentation of the earlier arena library.

**Target exclusion.** A successful raw-arena script gives exactly
`fixture_allocator="arena"`; the accepted TCB maps the wasm triple to
`target_arch="wasm32"`. The `all` predicate on `lib.rs:3` is then true,
regardless of `burst`. A `cfg` attribute includes its item when true and removes
it when false
([Reference 1.85.1](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute));
`compile_error!` “Causes compilation to fail with the given error message when
encountered”
([std 1.85.1](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)).
Thus every wasm/arena current compilation fails; if the script failed earlier,
the TCB already forbids compilation. No later-source fact is used on that exit.
For all other target/allocator pairs this particular `all` is false, so the
error item is absent. This proves exactly `E`, not a wider exclusion.

## API, invariants, and unsafe obligations

The complete language-reachable crate API is the safe free function
`lane_id(u8)->NonZeroU8`; there are no public fields, constructors of a local
type, traits/impls, macros, statics, FFI, reexports, callbacks, or dependencies.
Build code contains no unsafe operation. The two unsafe sites are
`lib.rs:21` and `lib.rs:36`. The consumed standard-library contract is exact:
`new_unchecked` “Creates a non-zero without checking whether the value is
non-zero. This results in undefined behavior if the value is zero,” and its
safety clause is “The value must not be zero”
([Rust 1.85.1](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)).

Define `H(c) = c.target=aarch64-unknown-linux-gnu ∧ c.burst=on ∧
c.allocator=arena`. Accepted Cargo mappings and Rust `cfg(all(...))` semantics
make `H` select the first block and remove the `not(all(...))` block; `¬H` does
the reverse.

* If `H(c)∧v!=0`, line 21 satisfies the exact unsafe precondition and returns
  the corresponding nonzero value.
* If `¬H(c)∧v=0`, `if value==0` reaches `panic!` before line 36. If
  `¬H(c)∧v!=0`, the false branch itself establishes the proposition needed by
  line 36. Thus the second safety comment is adequate and this entire case is
  UB-free. Profile, debug-assertion state, and panic strategy cannot alter the
  cfg or value partition; abort versus unwind occurs only after the proved
  zero-input panic and no invariant is suspended.
* **`BAD`:** choose any profile/debug state, `c=(aarch64,burst on,arena,...)∈C`
  and safe input `v=0`. The public safe call is valid; `H(c)` reaches line 21;
  its required `v!=0` proposition is false; the quoted contract directly
  entails undefined behavior. This is a complete existential UB certificate.
  The adjacent claim “Burst-mode lane identifiers are never zero” is false:
  the API accepts every `u8` and enforces no such invariant.

Therefore the **exact maximal sound region** over the requested full product is

`SOUND = C×U \ { (c,0) | H(c) }`.

Positive inclusion follows from the first two bullets. Reverse inclusion and
maximality follow because every omitted case satisfies `H∧v=0` and the `BAD`
derivation is parametric in profile/debug state, proving UB for every such
case—not merely one sample. The regions partition `C×U` exhaustively by
`H/¬H` and `v=0/v!=0`.

The panic postcondition is proved for every zero input in `¬H`: the check
executes `panic!`, which “Panics the current thread”
([1.85.1](https://doc.rust-lang.org/1.85.1/std/macro.panic.html)). It imposes no
claim for nonzero inputs. For `H∧v=0`, UB precedes any panic, leaving the global
postcondition `UNPROVED` and supplying no `CONTRACT-BROKEN` certificate.

## Finding, TCB log, and residual scope

**F-1 (critical, UNSOUND; proof comment deficient).** `lib.rs:13-22` hides an
unenforced nonzero precondition behind a safe API. Minimum repair: perform the
zero check before either cfg branch (or use checked `NonZeroU8::new` and panic
on `None`), then replace the first safety comment with the dominating check's
exact `value!=0` derivation. Re-audit all `C×U`, both panic strategies, and the
documented panic after any change.

**TCB log `supplied-TCB/BUILD-MAP-ORDERED`.** Category `IMPLEMENTATION`, human
disposition accepted; identity Cargo 1.85.1 plus the supplied manifest/build
interface; consumers are only ordered output interpretation, raw-value
freshness, feature/target/cfg reachability, selected source, and rejection. It
does not supply local emission order, source correctness, Rust semantics,
backend, or binary correctness; those were not widened. No other admitted
premise is consumed. Re-audit on any toolchain, source, manifest, policy,
target, cfg, feature, environment-interface, or TCB-disposition change.

Residual scope: compiler/backend correctness, binaries, manually manufactured
cfgs, unsupported targets/toolchains, and overridden build machinery. Tool
evidence: none. The current global failure is proved rather than inferred from
missing tests.
