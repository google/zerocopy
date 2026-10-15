# E46 positive runtime capture preparation

The runtime helper is prepared and has not been imported or invoked. No pilot,
QEMU guest, changed image or invalid call has executed. The only new container
action was the parent-authorized read-only env/Python identity query, exit0
with empty stderr, preserved in runtime-preparation/metadata-tools.*.
The prior static freeze and all375 entries remain unchanged.

The parent must review capture_runtime_v1.py, runtime-capture-policy.json and
this preparation manifest before granting runtime. Authorization remains the
parent's out-of-band decision; historical execution_authorized=false fields
in the unchanged runtime proposal record its preparation state. The explicit
helper command requires the externally reviewed preparation manifest hash:

    python3 capture_runtime_v1.py --execute-positive-sequence-after-parent-grant <RUNTIME-CAPTURE-PREPARATION.json SHA256>

This is a proposed command, not an executed receipt. The helper takes no
arbitrary command or image selector. It checks the exact four target argv and
image hashes independently against literal constants: AArch64 O0/O3 native
container calls, then x86_64 O0/O3 QEMU user-mode calls with explicit
-cpu qemu64-v1 and -L /usr/x86_64-linux-gnu. Source/compiler/oracle/image bytes
are unchanged. Each image runs at most once. GNU timeout --signal=KILL 30s
bounds each subject; the45-second host Docker-CLI timeout includes transport
slack and does not extend the subject's deadline. There is no retry path.

Before the sequence and before/after each call, the helper checks the
externally reviewed capture manifest and the immutable static freeze. Host
Python and Docker CLI hashes and paths must match. Each call gets fresh full
Docker inspection checking exact container/base-image/name/start identity,
running state, no mounts,1CPU/1GiB memory,2GiB memory+swap configured limit,
PID256 cap, unprivileged configuration and no-new-privileges. The same resource
configuration and container start state must survive the call. The optional
cgroup readings are raw snapshots, not a per-run peak-memory claim.

Each before/after file snapshot checks the fixed28 staged source files,69
selected target libraries,12 previously bound tools including GNU timeout,
all20 generated build files including all four final images, and7 runtime
library path identities covering six unique loader/libc/libgcc files.
Additional Python/env reader/wrapper pins include the path's link bytes/mode,
resolved-target path/mode/size/hash and actual interpreter path. /usr/bin/env
is68,992 bytes SHA25667a8c7fac47281a5ee335366bcd12f31aa7eeca008cef6eccad38304753ddee9.
/usr/bin/python3 is the literal symlink python3.11 to /usr/bin/python3.11;
target6,618,304 bytes SHA2569a070c8a36e16c152dae21b66aeb707f4d21b506c875e9b15edf4387fca7dcf8.
These identities bind the observed tools. Python/stdlib/hash-reader, env,
Docker, kernel, loader, compiler and emulator implementations remain trusted.
No self-hosting or correctness proof of the capture/checker is claimed.

All future capture writes are create-only under a fresh runtime-captures-v1/
directory. A pre-existing directory or receipt prevents rerun. Every subprocess
uses a direct argument array without a shell, stdin closed, with full raw
stdout/stderr, actual status, timeout/spawn error and elapsed time. Subject
argv use env -i with only the fixed PATH/LC_ALL/TZ allowlist. No feature probe,
source edit, compile, install, network tool, mutated image or negative native
case is available through the helper. Read-only after-checks still collect
diagnostics if a subject fails. Any unexpected status/output/identity/resource
or helper error records STOP evidence and prevents dependent target calls.

Each positive must return0, empty stderr and the exact architecture-tagged
E46_OK line reporting4617 checks. After a successful unchanged image call,
the helper makes six DATA ONLY copies: wrong printed count, wrong architecture,
missing final newline, trailing stdout, nonempty stderr and nonzero status.
The exact-output/status matcher must reject every copy; originals stay
untouched. JSON stores the changed byte strings/status and a no-execution
label. Four successes would yield24 such controls. These controls test receipt
admission, not injected bad runtime returns/guards, wrong machine code or ABI
faults. The one-line output contains no per-case return/guard record, and none
is invented. Existing prepared arithmetic/span/footprint controls retain their
separate data-only scope.

Host AST parsing checks the helper, embedded metadata reader and identity
query syntax without executing the runtime helper. validation.json also binds
all frozen entries and exact four proposal rows. The AST inspector's initial
literal_eval/BinOp error and narrow extraction correction are preserved in
ast-inspection-diagnosis.json. No helper/container/target effect followed from
that host-only failed inspection. This preparation has no runtime result.
Even later finite passes would not establish the stronger Rust/ISA/compiler/
ABI/resource/trace theorems or close any checkbox. The existing authorship
notice is retained once in PLAN.md.
