# E46 shared pilot: preparation for review

The proposed fixture is complete as source/data for review, but **not compiled,
linked or executed**. No container action, network operation, installation or
Git operation has been performed by this preparation. Only the parent may grant
the next stage after accepting these exact source, ABI and oracle contracts.

The aim is a matched bounded experiment with exact Rust1.89 and actual zerocopy
operations, on Linux AArch64 in the existing native container and Linux x86_64
SysV under QEMU user mode. It addresses the concrete E46 corpus criterion. It
does not close the stronger compiler/model/resource/ISA proofs tracked
separately. See [CONTRACTS.md](CONTRACTS.md) for valid-use preconditions and
instruction, ABI, memory, clobber and effect details.

## Fixed source and corpus

`pilot.rs` is shared source, with only the architecture-specific inline templates
and `global_asm!` inclusion selected by target cfg. `aarch64.s` and `x86_64.s`
define ten matching whole functions. Outputs larger than one word use pointer
spans rather than aggregate/vector C ABI returns. The same Rust harness, Python
oracle data and checks must be used for all target/profile runs. It never
executes deliberately incorrect assembly, metadata or ABI declarations.
Separately named non-inlined Rust baselines make the corresponding operations
available for compiler/object inspection. Their reference/value Rust ABI is
different from the raw-pointer C ABI; comparison is through each explicit
valid-input construction and shared value oracle.

| Case | Fixed finite corpus | Independent oracle and observations |
|---|---|---|
| unsigned multiply to128 | 17×17=289 | Python unbounded product split by2^64; Rust u128 baseline; both output limbs and guards |
|128-bit add/carry |12×12=144 | Python sum split by2^64/2^128; Rust overflowing_add; carry0/1 and output guards; diagonal shared-read inputs |
| scalar carry-in/out inline |17×17×2=578 | Python unbounded a+b+cin; Rust u128; declared flags and registers |
| byte-swap |17 | Python explicit byte positions; Rust swap_bytes; actual zerocopy wire bytes/native read |
| aligned load/store |17 each | Rust array element/value; whole and inline loads/stores; before/after guards and unchanged source |
| copy16 |12 byte patterns | scalar and SIMD assembly vs actual zerocopy read/write; exact byte list; source/destination guards |
| pointer return |12×17=204 | pointer derived with bounded add from the same live array; equality only, including one-past, never dereferenced |
| inline label |17 | Python/Rust condition value=0→17, else41; no asm output operands |
| C ABI helper |17×17=289 | Python rotate/xor/wrapping multiply+1; Rust bounce and assembly bounce each call the same C helper once; separate counter checks |
| SIMD16 lane add |12×12=144 | independent list of sixteen (a+b) mod256 values; Rust array baseline; all guards; diagonal shared-read inputs |
| zerocopy error paths |7/9-byte read/write | safe documented Err and unchanged destination; no short buffer reaches assembly |

The words include0,1,2,byte and32-bit boundaries, bit63, u64::MAX and its predecessor,
alternating bits and nonsymmetric hex patterns. The128-bit pairs cover carry
propagation from low to high, overflow, sign-bit boundaries and nonsymmetric
limbs. Vector patterns cover all-zero/all-ones, ascending/descending,127/128,
alternating bytes, walking bits and wire-header bytes. SIMD copy is motivated by
moving a fixed wire header; SIMD lane add is a deliberately richer16-byte
read/read/write stress case with byte overflow. It does not assert zerocopy
performs arithmetic or that enabling zerocopy's optional SIMD trait feature has
been tested.

`prepare_oracles.py` generates only integers/bytes and source literals. It was
run in preparation, without invoking a compiler, assembler, emulator or subject.
`expected.json`, `vectors.rs`, `oracle-preparation.json` and
`controls-proposed.json` are fixed before the first compile. `check_preparation.py`
checks the generated arithmetic and distinguishability controls as data; it is
not an ISA evaluator, compiler verifier or access-trace checker.

## Source identity and real dependency selection

The parent supplied a read-only clean-tree/Git-blob receipt for zerocopy:
`execution/parent/zerocopy-e46-source.json`, SHA256
`646d3b45cffdcdcaf496a37d7300fc1b55c6816c5f53fe128786e0ffa7df1f43`.
`zerocopy-selected-source.json` selects24 regular entries,1,337,662 bytes, and
was checked against those current bytes without Git. After authorization the
parent can copy those exact regular source inputs to `upstream/zerocopy/` inside
an owned staging directory/container. No symlink may be dereferenced. Original
license links remain literal metadata; separately selected real repository-root
license texts must be hashed if a source redistribution is prepared.

Repository AGENTS and its zerocopy-development/unsafe-rust skills were read.
The fixture uses the Cargo.toml's explicitly supported direct-rustc path, with
no Cargo invocation or repository changes. The source selection/configuration
and deliberate missing universal proof are recorded in CONTRACTS.md.

## Exact proposed tool domain and needed preparation

The parent's fresh read-only E46 preflight identifies container
`c1bf0a443c09a62a7747793d9ce696edfea27dbdc58bbacc652a4d999212c2d5`
named `anneal-big-endian-20261014`, running with no mounts and1CPU/1GiB. The
current Rust version capture identifies Rust1.89 commit
`29483883eed69d5fb4db01964cdf2af4d86e9cb2`, LLVM20.1.7, host
`aarch64-unknown-linux-gnu`, and only AArch64+s390x installed std targets.
`qemu-x86_64` is actually present, version7.2.22, Debian package
`1:7.2+dfsg-7+deb12u18+b3`. The x86 cross-GCC lookup returned127, meaning
absent; apt reports uninstalled candidates gcc-x86-64-linux-gnu4:12.2.0-3 and
libc6-dev-amd64-cross2.36-8cross1. No component was installed and no pilot was
compiled/run. `parent-input-identities.json` binds these existing receipts.
Native GCC12.2/binutils2.40 are earlier E08 observations still to refresh.

Proposed next-stage read-only preflight must capture exact rustc -Vv, matching
target libstd/library inventories, linker/QEMU versions and hashes, target cfg,
container/host process architecture and CPU features. QEMU's binary identity,
selected guest CPU and matching loader/sysroot must still be checked. AArch64
must be identified as actual native calls in
the Linux container on the host's AArch64 CPU; x86_64 results must be identified
as emulated calls, never x86 hardware observations. Compiler CPU defaults are
not physical CPU identity. Exact architecture/feature observations are needed
before NEON/SSE2 entrypoints execute.

Only the parent may extend the existing runtime with the missing **exact
Rust1.89 x86_64-unknown-linux-gnu standard library** and an x86_64 GNU cross
linker/sysroot. Candidate target command is `rustup target add --toolchain
1.89.0 x86_64-unknown-linux-gnu`; candidate Debian components are
`gcc-x86-64-linux-gnu`, `libc6-dev-amd64-cross` and dependencies, with the
currently observed candidates recorded above. These are
unperformed needs, not authorization for installation. Parent must pin/capture
actual package versions and acquired component hashes; do not substitute a
macOS, different Rust release, musl, host linker or differently configured
compiler. Existing qemu-user already supplies qemu-x86_64; do not reinstall it
or substitute a different emulator without an explicit plan revision.

Primary-contract preflight is also explicit: cached pinned AAPCS64 rules have
been read, but a pinned primary SysV psABI source and version-applicable1.89
asm documentation are not locally established here. With no network permitted
in preparation, these remain parent acquisition/review needs, before depending
on them. CONTRACTS records the exact proposed external rules, rather than
presenting later documentation or a compiler run as a proof of those rules.

Use baseline targets without `target-cpu=native`, explicit optimization0 and3,
codegen-units1, panic=abort and overflow-checks=yes. No LTO, feature extension or
`RUSTC_BOOTSTRAP`. Each selected crate and harness must use the same compiler,
target and profile. `commands-proposed.json` contains the intended argument
arrays, relative cwd and minimum environment, not executed receipts. The x86
linker/sysroot/PT_INTERP and QEMU loader prefix must be inspected before any run;
a missing loader is a prerequisite gap, not permission to copy an arbitrary one.

## Staged review and proposed limits

1. Parent accepts exact sources, CONTRACTS, oracle/control data, commands and
   dependency/resource needs. No compile/run until this review.
2. Parent authorizes/pins missing components, refreshes identity/feature
   preflight, stages the small exact source selection and hashes all inputs.
3. Build serially one target/profile at a time. Preserve source hashes,
   compiler status/stdout/stderr, object/final ELF, assembly and LLVM IR.
   Compilation or linking failure stops that path for diagnosis.
4. Inspect all ten whole functions, four inline functions and actual zerocopy
   adapters in object/final ELF, symbol/relocation/section metadata, helper
   resolution, instructions/access widths, stack/CFI and feature requirements.
   Recheck declared C ABI against actual caller code. Bind function bytes to
   objects and final images; relocation-aware comparison must name any changed
   call displacement rather than claim byte equality where it does not hold.
5. Only after parent grants runtime, run each unchanged positive image once,
   serially, capturing hashes before/after, status/stdout/stderr and a30s timeout.
   Proposed total four positive runs: A64 O0/O3 native and x86 O0/O3 QEMU.
   Expected harness total is4617 checks per run; no current check is a runtime
   observation. Preserve actual result rather than manufacturing this count.
6. Run only data checkers on copied metadata/byte/result controls. Never link,
   load or execute a mutated object/image or a misannotated-asm source. Package
   exact source/oracles/identities/commands/results with bounded-scope wording.

Proposed resource budget: one compiler or run at a time, existing1CPU/1GiB
container cap, ≤256MiB additional owned source/build/report artifacts, source
selection~1.34MB plus small fixture, ≤10minutes per compile and ≤30s per run.
Cross-target std/linker installation footprint is separately parent-controlled;
request a measured estimate before acquisition if it risks the host disk budget.
No upstream build, tool installation by this agent, concurrency stress or large
download is part of this fixture. Do not clean diagnostic artifacts to meet the
cap; stop and report if it would be exceeded.

Unexpected tool panic/assertion, compiler ICE, abnormal target status, mismatch,
changed source/image hash, missing feature, inconsistent metadata, failed
guard/return/call count, or unexpected unwind is a stop-and-diagnose condition.
No fallback compiler/target/optimization, source patch after results, ignored
check, native mutant or retry is implicit. An ordinary compile diagnostic is
preserved and reviewed before a new source snapshot is considered.

## Claims reserved for later work

At present the outcome is preparation only. Later finite agreement would be
compiler/runtime observations for four exact images and this finite corpus,
plus artifact/control checks. It would not establish a universal instruction,
Rust compiler, ABI, provenance, complete scalar/SIMD access, resource, source
adequacy or reference-ISA theorem. E46 acceptance and all milestone status
decisions remain the parent's responsibility.

*Authored by an AI agent acting on joshlf's behalf.*
