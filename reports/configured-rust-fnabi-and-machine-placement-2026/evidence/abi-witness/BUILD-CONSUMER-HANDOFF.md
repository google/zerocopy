# E33 observer build and strict consumer gate

*Authored by an AI agent acting on joshlf's behalf.*

The corrected observer was built once, but has never been launched. No actual
FnAbi query, fixture compilation/code generation, foreign call or native fixture
execution occurred. E33 remains incomplete. The new consumer's capture/check
paths are implemented and source-reviewed; only its data/preflight paths were
executed.

## Preserved original preparation and failed build

The original twelve inputs remain byte-identical to preparation manifest
`f43a6306944d5ee5c2e1984f1bafd20fe95706e6217e0c6c3ec1640547ca26b8`.
The first exact observer build encountered ordinary compiler E0283/E0284 at the
unqualified `Into::into` expression. Its controller had separately failed when
the sandbox denied `/bin/ps` after launch. That controller did not persist the
child PID or wait status: both remain unknown, and there is no claimed RSS bound
for that attempt. Full compiler streams and the emitted long-type artifact are
retained. A later authorized exact-source-path process lookup found no matching
process; that does not reconstruct a wait status. See `build-01/diagnosis.json`.

The parent reviewed the diagnosis and authorized only type disambiguation in a
distinct source, `.map(Into::into)` to `.map(ty::GenericArg::from)`. Original source
`proposed_observer.rs` remains untouched. `observer-v2.diff` records the exact
change; corrected source `observer_v2.rs` is
`88c4552c3f51f66b204e0aec9d415ed9211836f8f9ed1dc5992a58b94dc716b6`.
The historical caller catalog was not rewritten. The new
`consumer-authority.json` binds that catalog and the corrected observer identities
as a separate effective consumer profile.

## Corrected controller and actual build

`build_control_v2.py` preflights its scoped process monitor before launching a
child, persists PID/PGID/argv immediately after launch, and waits/reaps the child
in `finally`, including on monitoring failures. It queries only the owned
process group; it does not dump all system processes. The harmless-child
regression checks simulated denial both before launch (no child) and after
launch (PID retained, SIGTERM status -15, child reaped). These observations do
not prove a general process-controller theorem.

The parent-authorized new compiler process PID8513 was waited with exit0 and
empty stdout/stderr. The controller recorded0.746 seconds and a maximum sampled
owned-process-group RSS239,616,000 bytes. This is periodic RSS observation, not a
hard address-space cap, OS isolation or proof of the unsampled peak. No stop
budget was reached, no remaining group was found after waiting, and all five
frozen tool identities remained unchanged. Raw argv, exact environment, samples,
streams/status and source/controller hashes are in `build-02/`.

The actual executable `observer-v2` is1,103,224 bytes, SHA256
`c1c6ecdcdd07d779c50f83ad3b55bf789d905288d87d283e0b1cffa7fed6cc41`.
It remains unexecuted. Building a driver is not validating its queried meanings
or accepting any fixture ABI witness.

## Actual loader metadata and remaining runtime trust

Read-only Mach-O inspection found the new executable's LC_RPATH:

```text
@loader_path/../toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin/lib/rustlib/aarch64-apple-darwin/lib
```

The named `@rpath/librustc_driver-16d1e96e5b674978.dylib` resolves under that actual
layout to the retained202,329,432-byte regular file with SHA256
`dcaea7cc1884046940eb55fcb783e6a86272cf4743600925431022332fa9d69d`.
The selected and actual resolved driver bytes agree. System libSystem, Objective-C,
Foundation, zlib, C++ and iconv dependencies remain OS/shared-cache/runtime trust;
missing standalone files at those named paths do not mean unavailable runtime.
No transitive dependency-closure theorem or relocated-loader equivalence is claimed.

An initial metadata reader used capture names differing only by L/l on this
case-insensitive filesystem. The second command overwrote the first capture, so
the first dependency-list output was not retained. The reader stopped before a
loader verdict. `build-02/loader-reader-diagnosis.json` preserves the equal inode
and retained load-command hash. A parent-authorized read-only recapture used
create-only descriptive `dependencies`/`loadcommands` names; binary hashes before
and after agree. `build-02/linkage.json` binds the corrected raw evidence. No
compiler build or observer launch was repeated for that metadata recovery.

## Closed data consumer and ownership of the requested claim

`e33_data.py` pins the consumer authority digest
`4af1a36c1ad3cb1fc7d808b06cdbe94abd80c74da62a673eae0879e687a898ac`.
That authority fixes the historical preparation/catalog, corrected observer
source/binary and four permitted caller-selected host profiles. The caller
chooses a profile before producer input. Candidate data cannot supply a request,
source, target, flags, reference, weaker root or replacement authority. Original
source/selector/tool hashes and the actual resolved driver are checked, including
after a future capture. The source, compiler, Python/helper implementation,
consumer-owned filesystem and OS remain explicit trusted premises; this is not
an adversarial filesystem race or independently verified parser theorem.

The parser rejects duplicate/unknown keys, floats/NaN/infinite JSON tokens,
invalid UTF8, oversize/deep inputs, oversized integer tokens and malformed/trailing
JSON. It bounds input to4MiB and lexical nesting to64 before recursive parsing.
Every admitted structure has closed keys. Integers are type-checked so bool does
not stand in for an integer; scalar ranges use canonical bounded decimal u128
strings and retain wrapping ranges. Config/source/root/instance/extra-argument
sets are checked against the caller request. Every mode, attribute bitset,
extension, pointee property, cast component, layout and supplemental opaque
compiler rendering participates in final equality. Rustc's weaker `eq_abi` is
not used.

The source's nonvariadic `track_caller` construction appends a location after the
fixed source inputs. The grammar therefore allows `fixed_count < len(args)` for
that shape instead of enforcing a misleading equal-count invariant. Actual
tracked-argument and indirect-return observations are still unperformed.

`e33_consumer.py` has separate preflight, capture and check modes. Preflight only
reads/hashes. Capture would create a fresh reference from exactly the fixed
observer/profile; it does not accept a candidate. Check prevalidates candidate
data, generates its own new reference, and compares complete observations. There
is no CLI for a producer-supplied reference or arbitrary flags. Failure to load,
monitor, reach the callback, return status0, produce a complete reference, or
validate that independent reference is an operational stop, not a semantic
candidate rejection. A normal semantic mismatch remains a distinct data rejection.
No capture/check mode has been executed in this checkpoint.

A successful future comparison would establish equality with the selected trusted
compiler observation, not independent ABI classification soundness, Rust value
safety, memory-resource ownership, full dependency closure or machine placement.
Debug strings retain an opaque compiler-rendering frontier. FnAbi does not
provide a complete physical register/stack assignment or Windows shadow-space
ledger; later exact IR/assembly/object observations remain separate.

## Actually executed pure-data controls

`pure-data-controls/results.json` records54 outcomes:9 synthetic grammar/equality
positives,43 rejections and2 unknown/abbreviated CLI rejections. Controls cover
consumer-authority/catalog/source/selector substitution, stale target/options,
wrong roots/generic instances, omission/reordering, attribute/extension/return
changes, opaque-layout differences, nested unknown fields, bad integer/alignment
and scalar-range representations, duplicate keys and parser bounds. The capture
launcher was replaced with a trap for this test, and was never invoked.

All synthetic packets explicitly say they are invented data, not actual compiler
observations. Their equality results test the grammar/comparison code under a
supplied reference premise; they do not establish the fixture ABI, hidden-result
law, vector ABI or any machine/resource claim. A separate actual preflight checked
the retained compiler/driver/core/metadata/observer identities and returned
`preflight_only` with0 observer invocations, effective host-subjects-opt0 request
`cc4ed69fcd3cdf7b525a27008cf5144fb8b29ff1a522e29c8685e66f2dec6027`.

## Proposed next gate, not authorization or completed commands

`next-capture-plan.json` contains explicit nonexecuted commands. The smallest
next step is one parent-reviewed host-subjects-opt0 capture in a fresh owned run
directory, using the corrected binary and the inspected loader layout. It needs
the scoped monitor grant, one compiler,60-second timeout, sampled1GiB stop budget
and128MiB output budget. Stop on new diagnostics/query failures/grammar mismatch
before patching or extending the sequence.

Only after reviewing that actual whole observation should a next grant admit a
fresh same-profile check of its candidate and the other fixed profiles/actual
semantic mutants. A candidate check must generate a new independent reference;
passing an invented pure-data reference is not a substitute. Fixture LLVM
IR/assembly/object output, Windows target setup, foreign/native execution and
source-to-machine proof remain separately unperformed and ungranted.
