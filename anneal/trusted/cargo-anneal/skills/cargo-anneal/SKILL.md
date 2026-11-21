---
name: cargo-anneal
description: >-
  Use when checking whether cargo-anneal can verify a Rust function, preparing
  a request or Lean proof, or interpreting a verification receipt.
---

# Verify a Rust function with Anneal

Anneal verifies a subset of Rust. Support depends on the installed version and
the selected function and compilation. Use `cargo anneal --version` and the
matching release's documentation for orientation. Run the intended request to
learn whether that build can verify the user's code.

Lean elaboration can execute code as the caller. Run the entire verifier in
an isolated execution environment when working with untrusted inputs.

## Run the project's verification

Identify the Rust function, the intended property, and any caller
preconditions. If the project has a request and proof for that claim, use
them with its toolchain. If setup is needed, run `cargo anneal setup` for a
published build, or select a matching local archive with
`cargo anneal setup --local-archive <path>`. Use the same user and cache for
setup and verification. Setup can reuse an existing installation. To select a
specific archive on Linux, point `XDG_CACHE_HOME` at a fresh directory.

Run the request, save stdout to a new receipt file, and record the exit status.

```sh
cargo anneal verify --request path/to/request.json > path/to/new-receipt.json
```

## Create a request and proof when needed

Run `cargo anneal skill --example` to print a complete working example from the
installed CLI. Save the four files together in a scratch directory to try it.
The example proves that a safe function with no arguments terminates and always
returns zero in the captured MIR model.

1. For request schema `1`, set `scope.kind` to `selected_unit` and put one
   exact Rust definition path in `scope.roots`, relative to the crate root
   (for example, `module::function`). Set the Rust edition, target, and `cfg`
   for the intended compilation. Include the crate root in `source_files`.
   The `proof` section lists Lean modules with `specification` or `proof`
   roles. Resolve both source roots relative to the directory containing the
   request and keep them within it. List regular files by paths relative to
   their source roots.
2. Write the property and proof in their declared Lean modules. The default
   declarations are `Spec.specs` and `Proof.verify`. Express actual caller
   preconditions for an `unsafe` function in `Specs.safety`. A predicate of
   `False` excludes every caller of an unsafe function. Check which calls the
   predicate admits before claiming that callers may rely on the proof.
3. Import `Expected` in the proof and prove `Expected.claim`. Anneal generates
   `Captured.lean` from the Rust compilation and `Expected.lean` from that
   capture and the specification. Keep the selected function, configuration,
   property, and caller preconditions fixed while diagnosing the proof. Discuss
   any proposed change to the verification claim with the user.

The example uses `execProg` to check a bounded execution of its captured body.
`wellFormed_and_spec_of_wp` turns that check into safety, a postcondition, and
termination in the model. When adapting the example, run the request with
`--artifacts <new-directory>`. In `capture/capture.json`, inspect `selected` for
the body index and `program` for the MIR. Choose fuel to cover the executed MIR
steps through the return. Use `generated/Expected.lean` to inspect the goal.
For functions with arguments, address all permitted inputs when the claim
requires it.

## Diagnose limitations and report results

Read `status`, `phase`, and `detail` together. When stdout has no receipt,
inspect stderr for a command-line or execution error.

- For `unsupported`, read the detail before drawing a conclusion about Rust
  support. Correct request, selector, file, or module errors. When the detail
  names an unsupported target or Rust construct, report what this version
  refused for the selected function and compilation.
- For `compiler_failed`, inspect the Rust diagnostics. For `tool_failed`,
  diagnose the named phase, such as setup or artifact retention.
- For `proof_failed`, inspect the Lean or audit diagnostic and the generated
  obligation. The failure may require a change to the proof or expose a gap
  between the implementation and specification.

For diagnostics, rerun with `--artifacts` and a fresh UTF-8 directory path
under an existing parent. Retained `capture/Captured.lean` shows that the
compiler adapter produced a Lean representation of the MIR.
`generated/Expected.lean` shows that Anneal generated the obligation. Use the
receipt to determine the outcome.

With exit `0` and `selected_unit_verified`, compare the checked specification
and applicable caller preconditions with the user's intent. The receipt's
`audit.specificationClosure` identifies definitions to inspect. Report the
property actually checked and any gap with the request, along with the selected
function, compilation configuration, material assumptions, and deferred checks.
Keep the input identities with the receipt. A successful receipt can be large.
Read `status`, `scope`, and `configuration` first, then inspect the relevant
audit entries and the specification itself.
