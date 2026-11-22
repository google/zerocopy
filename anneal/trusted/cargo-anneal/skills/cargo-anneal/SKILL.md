---
name: cargo-anneal
description: >-
  Use when checking whether cargo-anneal can verify a Rust function or scalar
  crate, preparing a request or Lean proof, or interpreting a verification
  receipt.
---

# Verify Rust code with Anneal

Anneal verifies a subset of Rust. Support depends on the installed version and
the requested scope and compilation. Use `cargo anneal --version` and the
matching release's documentation for orientation. Run the intended request to
learn whether that build can verify the user's code.

Lean elaboration can execute code as the caller. Run the entire verifier in
an isolated execution environment when working with untrusted inputs.

## Run the project's verification

Identify the Rust function or crate scope, the intended property, and any
caller preconditions. If the project has a request and proof for that claim,
use them with its toolchain. If setup is needed, run `cargo anneal setup` for a
published build (reusing an existing cached installation for this version), or
run `cargo anneal setup --local-archive <path>` to install a local archive and
replace any existing installation for this version. Pass `--clear-old` to remove
older cached toolchain directories without prompting (on an interactive terminal
without `--clear-old`, `setup` prompts before removing them; in automated or
agent shells with a pseudo-TTY, pass `--clear-old` or redirect stdin from
`/dev/null` so the prompt cannot block). Use the same user and cache for setup
and verification; the cache lock coordinates concurrent runs so each `verify`
observes one complete toolchain. To keep an existing cached installation
untouched on Linux, point `XDG_CACHE_HOME` at a separate directory.
Builds compiled with `--no-default-features` omit `setup` and require explicit
`--capture`, `--sysroot`, and `--lean` paths.

Run the request, save stdout to a new receipt file, and record the exit status.

```sh
cargo anneal verify --request path/to/request.json > path/to/new-receipt.json
```

Build systems that already resolve source files and module mappings (including
symlinked runfiles) can invoke `cargo anneal verify rustc <crate_root>
--crate-name <name> --spec-file <Mod>=<path> --proof-file <Mod>=<path> ...`
directly instead of writing `request.json`.

## Create a request and proof when needed

Run `cargo anneal skill --example` to print a complete working example from the
installed CLI. Save the four files together in a scratch directory to try it.
The example proves that a safe function with no arguments terminates and always
returns zero in the captured MIR model.

1. For request schema `1`, set `scope` either to `{"kind": "selected_unit",
   "roots": ["module::function"]}` with non-empty crate-relative Rust
   definition paths (`UnitTheorem`), or to `{"kind": "crate"}` with no `roots`
   field (`CrateTheorem` across the whole crate). Set the Rust edition, target,
   and `cfg` for the intended compilation, and include `crate_root` in
   `source_files`. The `proof` section lists Lean modules with `specification`
   or `proof` roles. Each `source_root` resolves relative to the request file's
   directory or to an existing out-of-tree directory; list regular files by
   clean relative paths inside their canonicalized `source_root`.
2. Write the property and proof in their declared Lean modules. The default
   declarations are `Spec.specs` and `Proof.verify`. Express actual caller
   preconditions for an `unsafe` function in `Specs.safety`. A predicate of
   `False` excludes every caller of an unsafe function. Check which calls the
   predicate admits before claiming that callers may rely on the proof.
3. Import `Expected` in the proof and prove `Expected.claim`. Anneal generates
   `Captured.lean` from the Rust compilation and `Expected.lean` from that
   capture and the specification. Keep the requested scope, configuration,
   property, and caller preconditions fixed while diagnosing the proof. Discuss
   any proposed change to the verification claim with the user.

The example uses `execProg` to check a bounded execution of its captured body.
`wellFormed_and_spec_of_wp` turns that check into safety, a postcondition, and
termination in the model. Proof modules (not `specification` modules) may also
import bundled 3-axiom `Anneal.*` proof libraries (`Anneal.MirWp`,
`Anneal.LoopInv`, `Anneal.LinearArith`, `Anneal.SpineForce`, `Anneal.PTree`,
`Anneal.BitTrieLrat`, `Anneal.BitVec`, `Anneal.BitVecArith`,
`Anneal.NatBitwise`, `Anneal.LeBytes`, and `Anneal.ListChunks`), compiled and
audited on demand when imported. When adapting the example, run the request
with `--artifacts <new-directory>`. In `capture/capture.json`, inspect
`selected` for the body index and `program` for the MIR. Choose fuel to cover
the executed MIR steps through the return. Use `generated/Expected.lean` to
inspect the goal. For functions with arguments, address all permitted inputs
when the claim requires it.

## Diagnose limitations and report results

Read `status`, `phase`, and `detail` together. When stdout has no receipt,
inspect stderr for a command-line or execution error.

- For `unsupported`, read the detail before drawing a conclusion about Rust
  support. Correct request, selector, file, or module errors. When the detail
  names an unsupported target or Rust construct, report what this version
  refused for the requested scope and compilation.
- For `compiler_failed`, inspect the Rust diagnostics. For `tool_failed`,
  diagnose the named phase, such as setup or artifact retention.
- For `proof_failed`, inspect the Lean or audit diagnostic and the generated
  obligation. The failure may require a change to the proof or expose a gap
  between the implementation and specification.

For diagnostics, rerun with `--artifacts` and a fresh UTF-8 directory path
under an existing parent (adding `--export-lean-lib` when compiled `.olean*`
files should be copied to `<artifacts>/lean-lib/`, or `--lean-memory-mb <MB>`
to adjust Lean's `-M` limit). Retained `capture/Captured.lean` shows that the
compiler adapter produced a Lean representation of the MIR.
`generated/Expected.lean` shows that Anneal generated the obligation. Passing
`--allow-unpinned-lean` with `--lean <path>` admits an unpinned host Lean
toolchain over its discovered `Init.*`/`Std.*` sysroot closure, prints a
`TAINTED` stderr warning, and sets `taint_reasons` to `["unpinned_lean"]`. Use
the receipt to determine the outcome.

With exit `0` and `selected_unit_verified` or `crate_verified` (or
`tainted_selected_unit_verified` / `tainted_crate_verified` when
`taint_reasons` is non-empty), compare the checked specification and applicable
caller preconditions with the user's intent. The receipt's
`audit.specificationClosure` identifies definitions to inspect. Report the
property actually checked and any gap with the request, along with the verified
scope, compilation configuration, `taint_reasons`, material assumptions, and
deferred checks. Keep the input identities with the receipt. A successful
receipt can be large. Read `status`, `taint_reasons`, `scope`, and
`configuration` first, then inspect the relevant audit entries and the
specification itself.
