# Final abstract-hook support integration review

Disposition: **source-level approval for one bounded integration attempt**, with
fresh output and complete selected-closure checking. No source contract or
generator-consumer mismatch was found in the proposed three declarations. This
review did not execute a generator, Lean, Docker or runtime command, modify
sources, or assert that the new interface elaborates.

Reviewed `sail-proof-design/EXTERN-DIAGNOSIS.md` and
`proposed-extern.patch`, SHA256
`bd7c48e9ea4f28e85f1c34cd55e80eb0c8def03ebe50876d4ac8655881f9cc82`.
Independently read the original Sail contracts, actual annotation-repaired
generated Defs/Events/Counters/ValidateConfig/RiscvExtras, pinned backend source
and the saved `build-termination-82.stdout`. The last is an ordinary unknown-name
error for Events.lean:288 `event_callback`; it is not evidence of a timeout,
panic, OOM or theorem failure. The parent separately records 82 successful
preceding modules; this review did not rerun them.

## Exact contract and placement

The patch preserves the three actual external interfaces:

| Sail source contract | Proposed Lean type | Actual generated use |
|---|---|---|
| core/events.sail:28, impure `(Event, Privilege) -> unit` | `LeanRV64D.Event → LeanRV64D.Privilege → LeanRV64D.SailM Unit` | Events.lean:288 directly returns the monadic callback computation |
| core/counters.sail:211, pure `(hpmidx,bits64,bits64) -> unit` | `LeanRV64D.hpmidx → BitVec 64 → BitVec 64 → Unit` | Counters.lean:464 wraps the pure callback result in `pure` |
| postlude/validate_config.sail:1158, pure `unit -> bool` | `Unit → Bool` | ValidateConfig.lean:2075 uses a plain Bool-producing call |

Generated Defs.lean:1486 abbreviates hpmidx to Nat; the source range3–31 is
recorded as a generated function-parameter constraint, not an Int or a Lean
subtype proof argument. The patch therefore correctly uses the model alias
without adding a conversion or proof parameter. Defs.lean:2394 supplies the
concrete Arch instance, and :2420 abbreviates the model SailM using its exception
type. The fully qualified callback monad is the generated model's own monad.

RiscvExtras already imports LeanRV64D.Defs. The inserted declarations sit before
`section defs` / `variable [Arch]`, so they do not acquire that later arbitrary
architecture parameter or select the support library's generic error type.
The basename RiscvExtras remains unchanged, preserving emitted import visibility.
No existing generated declaration for these names is replaced or shadowed.

These are opaque data/computation constants in Lean's axiom form, consistent
with the existing proof support's external interfaces. They assert no proposition
about a desired ADD result, termination, success, effect erasure or correctness.
They do add named logical assumptions and must remain in the reported subject
and assumption closure. In particular event_callback may denote an arbitrary
SailM computation, including effects and errors. Its pure Unit-valued companion
cannot model native host-side effects outside Sail's pure contract. The patch
does not implement or prove correspondence to C++ event queues/counter-selector
registration. It does not turn any missing callback into a no-op.

## Stock import copying can be replayed without a third Sail translation

The inspected backend at rems-project/sail
`7e0e53d183cad75b8f36bfbbecc0ef75614a8418`,
`src/sail_lean_backend/sail_plugin_lean.ml`, has SHA256
`c79c314d2a5f83cdf6230e352e7afb6c47f1415df19e4f49a1079e9d786385a5`.
Its opt_lean_import_files uses are declaration/CLI storage, filename-derived
import preludes, and the start_lean_output copying loop. The latter applies
`sed 's/THE_MODULE_NAME/<out_name_camel>/g'` to the imported file. The imported
content does not enter Sail parsing, type checking, callgraph construction or
the target's registered IR rewrites. The main output function computes its
generated module structure from the already processed Sail AST; copied support
bytes have no earlier semantic consumer in this pinned source.

Thus a fresh full raw project copy plus exact replay of the native substitution
on the patched, same-basename RiscvExtras input reproduces the support-file
change that this backend would make. It avoids another expensive Sail
translation without changing emitted ISA bodies. This is an argument about the
inspected copy operation, not a new generator execution result or a general
equivalence theorem for arbitrary backend changes.

The raw annotation-repaired local project currently contains 178 regular files,
174 ending in `.lean`, with no symlinks found. Before compilation require the
new copy to have exactly the same path/type set, all other177 file bytes
identical, and the replacement support file exactly equal to the patched source
under global literal THE_MODULE_NAME→LeanRV64D substitution. Preserve before/
after manifests, patch/input/output hashes, actual native command/streams/status,
and the exact backend identity. Quote native input/output paths correctly. The
stock backend ignores its sed subprocess status; the owned replay must check
status and resulting bytes rather than inheriting that omission.

Do not copy partial compiled state into the new build: use raw project sources
and a new create-only serial-build output with the same pinned support library,
compiler and resource controls. Require fresh full143-module compilation for
LeanRV64D plus Sail.ArchSemSequential. A source-copy comparison or 82 prior
successes cannot replace that check. There were two Sail translations; the
new subject is the annotation-repaired generated model with explicitly rebound
abstract-hook support, not a third translation or untouched upstream output.

## Scope and final stop boundary

The generated DeviceTree module remains outside the selected complete143-module
closure. Its missing get_initramfs_base/get_initramfs_size interfaces stay a
recorded limitation. Report the target closure accurately; do not claim all178
project files, all174 generated Lean files or every --all-modules output checks.
No additional hook repair is authorized by this review.

For any later selected theorem, print its actual axiom closure. The theorem's
type may mention whole Functions.execute, which can bring syntactically
referenced hook/platform/FP assumptions into that closure even if a particular
ADD branch does not invoke them. Preserve actual-execute binding and distinguish
syntactic dependency from operational invocation; do not normalize away the
binding to manufacture a smaller assumption report. No theorem correctness or
closure result is established here.

Allow exactly this final bounded integration attempt under the parent's prior
limits. At the next ordinary compiler error, unexpected assertion/invariant or
resource failure, preserve exact inputs/streams/status and stop for diagnosis
before another changed run. No automatic repair cycle, hidden model reduction,
deleted import, expanded allocation or reuse of rejected compiled artifacts is
implied by the source-level approval.
