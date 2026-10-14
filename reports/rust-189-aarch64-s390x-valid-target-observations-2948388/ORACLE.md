# Valid Rust target fixture: oracle fixed before execution

Prepared by an AI assistant for the authorized E08 experiment. Initial status:
source prepared and manually reviewed; compilation and execution not yet observed.
The accompanying sources require Rust 1.89.0, edition 2021, and only `std`.

## Paired subjects and finite domain

The planned comparison uses the **same five source files and Rust 1.89.0 commit
29483883eed69d5fb4db01964cdf2af4d86e9cb2 / LLVM 20.1.7** for native
`aarch64-unknown-linux-gnu` and emulated `s390x-unknown-linux-gnu`. Both are
64-bit Linux subjects; the latter is big-endian. This is a fresh paired subject,
not an assertion of identity with an earlier May-nightly/MiniRust experiment.
Record complete compiler verbose identities, target cfgs, compilation argv,
linker/QEMU versions and identities, source and ELF SHA-256s, process statuses,
and raw output before interpreting results. QEMU is an additional execution
premise, not proof of physical s390x equivalence.

PowerPC64 was an initial environment lead. Its cross-linker package was absent
from the observed Debian arm64 package index; the selected available target is
s390x. That observation does not establish Rust, LLVM, PowerPC, or ISA semantic
unsupportedness. No PowerPC result is claimed.

## Outcome classes fixed before running

| Area / emitted prefix | Required finite oracle | Allowed target differences / exclusions |
|---|---|---|
| `integer.*` | Exact explicit byte-order arrays; native roundtrip; explicit wrapping/checked arithmetic; valid/checked/wrapping shifts; defined truncating/sign casts. All `CHECK` lines pass. | `integer.u64.native_bytes` is little-order on aarch64 and big-order on s390x. Explicit little/big arrays are equal between subjects. No plain overflowing arithmetic or out-of-range ordinary shift is executed. |
| `float.*` bit conversions | Each listed f32/f64 input bit pattern survives `from_bits` → `to_bits`. Exact binary arithmetic and exactly representable width conversion; the listed finite/NaN/infinity integer casts meet the stated truncating/saturating results. | Signaling/quiet NaN interpretation is not assumed portable. No arithmetic is required to retain an input NaN's sign/payload. The tiny subnormal test concerns the constructed value/bit conversion, not a universal no-flush arithmetic theorem. |
| `CHOICE float.*` | All three outputs classify as NaN; retain actual hexadecimal bits. | Exact arithmetic-NaN or width-converted NaN bits may differ and may also happen to agree. Either outcome fails to establish portable NaN canonicalization. No epsilon-based comparison replaces exact checks. |
| `layout.repr_c_formula`, scalar fields | Size/alignment/offsets match the field-order, alignment-rounding `repr(C)` formula computed using each subject's own primitive alignments. Field values survive. | Actual offsets/size/alignment are observations, not a prescribed shared C ABI. Never read struct padding or transmute its representation. Scalar native bytes are endian-dependent. |
| array / slice / DST | Three u16 elements occupy three element sizes; safe slice length, middle view, and pointee size match. A final-field `[u32;3]` → `[u32]` unsizing preserves head, elements, alignment and total pointee size for this instance. | Wide reference size/alignment is recorded. No generic guarantee that all DSTs, references or metadata are exactly two words is asserted. No raw metadata reconstruction. |
| enums / niches | Three constructed `repr(u8)` fieldless variants have the named values/one-byte representation; safe data-enum matching yields the selected payloads. The documented Option<NonZeroU16> / Option<&u8> size/alignment optimization and safe value behavior hold. | Data-enum and Option<bool> sizes are observations. No invalid discriminant, enum/Option transmute, niche byte inspection, or inferred arbitrary enum layout. |
| trait-object dispatch | Two safe `&dyn Measure` calls return 1007 and 18; `size_of_val`/`align_of_val` agree with each concrete pointee. | Reference size/alignment is observed; no vtable address, slots, contents, drop-entry layout, or stable ABI is assumed. Compiler devirtualization is permitted and not measured. |
| `readiness.*` | The ten fixed range decisions, checked sums and empty allocation model match the literal expectations. Addition overflow and out-of-bounds ranges are rejected before indexing. | Boolean arrays are a **model** of initialization/readability/stability. Actual Rust storage is fully initialized. This does not establish provenance, concurrency stability, a physical memory permission, or compiler memory-model correspondence. |
| `wide_union.*` | A valid raw slice pointer copied through each of two unions retains pointer identity and the live slice's elements/length. | Only the initialized pointer field is read; never inactive words/padding. Size/alignment is recorded, not used to forge a pointer or allocator state. This is an ordinary valid Rust case, not a MiniRust replay or repair. |
| `drop.*` | Move does not drop, explicit drop occurs once, scope exit does not double-drop the moved value, and a second guard drops once on normal scope exit. | No panic/unwind, FFI, allocator, asynchronous cancellation, dynamic destructor/vtable ABI, or nontermination claim. |

The safe controls deliberately refute broader oracle mistakes: native bytes are
not endian-independent; checked and wrapping operations differ; equal float
values need not have equal bits; NaN equality is not reflexive; actual array
presence does not imply model readiness. A control passes when that distinction
is observed; it does **not** deliberately invoke UB or cause a failing assertion.

## Observation acceptance and stop conditions

Each executable prints `META`, `CHECK`, `OBS`, `CHOICE`, and one final `SUMMARY`.
Require exit 0, empty stderr, `failures=0`, no `CHECK ...=FAIL`, no missing/duplicate
check keys, and matching check-key sets/counts between the two subjects. Verify
configuration metadata separately: native aarch64/little/64 versus s390x/big/64.
Do not compare complete stdout byte-for-byte: the documented observation classes
have different cross-target oracles. Preserve any unexpected compiler diagnostic,
runtime panic/assertion, process failure, or failed portable check and stop the
affected dependent path for diagnosis before retry. A compile/link infrastructure
error is not a language counterexample; a valid-program mismatch needs its own
source/compiler/emulator analysis.

Suggested matched compiler arguments after runtime authorization are
`--edition=2021 -C opt-level=0 -C overflow-checks=yes`; add the selected target to
both builds and `-C linker=s390x-linux-gnu-gcc` only to the s390x build. Capture
the exact actual arguments. No target binary is run on the host macOS system.
The parent authorized native Linux-arm64 execution in the task container and
`qemu-s390x -L /usr/s390x-linux-gnu` for the s390x ELF after READY.

## Safety and claim boundary

Only `wide_copy_drop.rs` uses unsafe: each union's pointer field was initialized
from a live shared slice; copying leaves that field unchanged; only that field
is read; dereferencing occurs while the same allocation and borrow remain live.
All source bytes later inspected are initialized. No byte read of aggregate
padding, invalid union field reinterpretation, invalid native Rust, data race,
allocator forgery, or external-memory observation occurs. All other tests use
safe Rust. The readiness masks are data, not actual uninitialized memory.

A successful run can answer E08 for these two exact configured subjects and
finite cases. It is not E49's all-target/all-input numeric/FP theorem, proof of
LLVM/QEMU, a general Rust ABI theorem, a source-to-MiniRust theorem, an E05 erasure
experiment, or proof of E30 concurrent/resource semantics. Finite agreement does
not close those semantic arrows; target-specific layout or permitted NaN-bit
differences do not themselves refute portable Rust behavior.
