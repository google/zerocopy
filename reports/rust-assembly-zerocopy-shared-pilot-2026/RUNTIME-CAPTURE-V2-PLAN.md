# E46 runtime capture v2: exact correction and authorized continuation

This is an immutable pre-execution snapshot. Parent independently diagnosed
v1's metadata-only failure before the first target call and authorized this
exact descendant plus the same four original positive calls once if every
corrected metadata gate passes. No target has executed at this freeze.

capture_runtime_v2.py differs from reviewed v1 only by reading20 rather than18
bytes for ELF_identity, and versioning its capture directory and reviewed
manifest path. runtime-v2.diff preserves the complete diff. The policy, images,
source, compiler, four argv, environment, deadline and oracles are unchanged.
The v1 helper, preparation manifest, failed gate output/STOP trace, outer
receipt and root-cause diagnosis are retained byte-for-byte.

regress_runtime_header_v2.py operates only on retained actual JSON records.
For each of7 library paths,28 checks in total show: the actual old18-byte
record is rejected; the exact retained20-byte static header accepts; changed
e_machine (byte18) rejects; and changed earlier magic byte rejects. All full
hashes/other record fields are held fixed in these DATA ONLY candidates.
No invalid ELF file, process, image, pointer, metadata or Rust execution occurs.
The regression is an unverified Python record comparison, not ISA correctness.

The explicit continuation command after this freeze is:

    python3 capture_runtime_v2.py --execute-positive-sequence-after-parent-grant <RUNTIME-CAPTURE-PREPARATION-v2.json SHA256>

The helper retains all reviewed375 static entries and v2 preparation entries,
exact host/container tool and source/library/build/image identity gates,
no-mount/container1CPU/1GiB resource checks, GNU KILL30s target deadline with
45s Docker supervision, and create-only captures in runtime-captures-v2/.
The same AArch64 O0/O3 native-container then x86_64 O0/O3 QEMU qemu64-v1
sequence may run once serially. No compilation, guest probe, mutant execution
or source change is authorized. Six DATA ONLY output/status controls follow
each actual positive success; all native calls remain unchanged positives.

ANY further status/output/panic/assertion/timeout/identity/metadata-reader
failure stops all dependent calls. The parent requires a new mechanism
decision before any further descendant or retry. This document does not claim
a run has happened or that any stronger Rust/ISA/ABI/resource theorem follows.
The existing authorship notice remains once in PLAN.md.
