# Rust Inline Assembly Contracts, Mach-O `aarch64` Relocation Binding, and Kraken `Effects` / Parser Opacity Boundaries

## Summary

Verifying a Rust-to-assembly call boundary on `aarch64` across source contracts,
compiled Mach-O object/executable artifacts, and `leanprover/kraken` ISA
semantics exposes four distinct verification gaps that are invisible if a bridge
checks only source attributes, return values, or default Kraken execution:

1. **Normative `#[inline(never)]` Ignore Rule on Exported Rust Functions (`rust-lang/reference@82da570b`):**
   Under Rust Reference rule `[attributes.codegen.inline.ignored]`
   (`src/attributes/codegen.md:83-84`), `#[inline]` (including `#[inline(never)]`)
   is ignored when applied to externally exported functions carrying `#[no_mangle]`
   or `#[export_name]`. Source-level `#[inline(never)]` on an exported Rust caller
   wrapper therefore cannot establish that a compiled call site emits an explicit
   branch-with-link (`bl`) instruction; binary inspection of the emitted object
   and linked executable is required.
2. **Return-Value vs. Memory-Footprint Discrimination on Naked `aarch64` Leaves:**
   For a 4-instruction `#[unsafe(naked)] extern "C"` exchange leaf over a 2-slot
   `#[repr(C)] [u64; 2]` buffer (`ldr x2, [x0]; str x1, [x0]; mov x0, x2; ret`,
   machine words `0xf9400002, 0xf9000001, 0xaa0203e0, 0xd65f03c0`), a wrong-slot
   mutation (`str x1, [x0, #8]`, word `0xf9000401`) still loads and returns the
   initial first-slot value `a` in `x0` while overwriting the adjacent second slot
   `[x0 + 8, x0 + 16)`. Furthermore, when the old and new values coincide (`a == v`),
   even inspecting `(x0, slot0)` produces `(a, a) == (a, v)` on both programs.
   Sound discrimination requires either witnessing the adjacent slot `slot1` on a
   non-degenerate state `(a, v, b)` or enforcing narrow write-footprint permissions
   `[x0, x0 + 8)` over the instruction semantics.
3. **Mach-O `aarch64` Relocation Adjacency (`ARM64_RELOC_ADDEND` Preceding `ARM64_RELOC_BRANCH26`):**
   In 64-bit Mach-O `MH_OBJECT` (`CPU_TYPE_ARM64`), an `ARM64_RELOC_ADDEND`
   entry (`r_type == 10`) in a section relocation table modifies the immediately
   following relocation record by table index (`table_index + 1`), regardless of
   whether the `ARM64_RELOC_ADDEND` record's own `r_address` field overlaps the
   4-byte `bl` instruction range. A verifier that filters relocations solely by
   byte-range overlap with the `bl` instruction offset misses non-overlapping
   preceding addend relocations.
4. **Kraken `8af7806` Recursive `partial def` Kernel Opacity and Permissive `Effects.All`:**
   - **Kernel Opacity of `Kraken.AArch64.Parser.parse`:** In `leanprover/kraken@8af7806`
     (`Kraken/AArch64/Parser/Basic.lean:138-152, 703`), `Parser.parse` dispatches
     through `parseAddr` to a recursive `partial def parseConstExpr`. In Lean 4
     (`leanprover/lean4:v4.34.1`, `Lean/Elab/PreDefinition/Main.lean:299-320`,
     `Lean/Meta/Eqns.lean:142-151`), recursive `partial def` declarations elaborate
     as kernel `Declaration.opaqueDecl` constants (`ConstantInfo.opaqueInfo`) paired
     with an `unsafe` compiled auxiliary `._unsafe_rec` and generate no kernel
     unfolding equations (`getEqnsFor?` returns `none`). Consequently, `#eval` /
     `MetaM` can evaluate `Parser.parse`, but kernel definitional equality (`rfl` /
     `decide`) cannot unfold it. By contrast, a fuel-bounded structural parser or a
     total AST token printer elaborates as a safe `ConstantInfo.defnInfo` and
     reduces in the kernel by `rfl`.
   - **Permissive Default `Effects.All` and `Executable.eval`:** Kraken's memory
     helpers (`Kraken/AArch64/Semantics.lean:171-221, 980-993`) emit
     `require_read_access`, `require_write_access`, and `require_exec_access`
     events into the `Effects` interaction tree, while `checkSPAlignment`
     (`319-327`) checks alignment only when the base register is `SP`. However,
     both `Effects.All` (`Kraken/AArch64/OmniSemantics.lean:13-22`) and
     `Executable.eval` ignore all `require_*_access` events
     (`require_*_access => Effects.All k`), accepting out-of-footprint stores
     (`str x1, [x0, #8]`) and non-`SP` unaligned loads/stores unless a custom
     footprint-and-alignment observer interprets those `Effects` constructors.

## Applicability

These findings apply to:

- **`rust-lang/reference`:** Commit `82da570bafd9efed421bdbae0f8603ede8dd308b`
  (tree `2f158dd465eb5a755cbbf2d77b6f2db0075498f8`), specifically
  `src/inline-assembly.md` (blob `f8e48cf1b9931ed5ab9429fc3db7ac22bb01d219`),
  `src/attributes/codegen.md` (blob `ab3c4972abbb659b5c3ce78d6247829e65929d93`),
  `src/items/functions.md` (blob `03d74dc28a3811be5742c33d780f6bd59b1d7d74`),
  `src/items/external-blocks.md` (blob `7d5eb3f49a5d4bf778ed95bf63ca8c3bf87d2e84`),
  `src/type-layout.md` (blob `62c1cbff1899a2db0c330594d9081b0943fb7a56`), and
  `src/behavior-considered-undefined.md` (blob `77ba221befb527cdab2da1ecad599ab44ffce659`).
- **Mach-O `aarch64` Binary Verification:** 64-bit Mach-O relocatable objects
  (`MH_OBJECT = 1`) and demand-paged executables (`MH_EXECUTE = 2`) for
  `CPU_TYPE_ARM64 = 0x0100000c`, `CPU_SUBTYPE_ARM64_ALL = 0`, validated by
  [`support/bind_artifacts.py`](support/bind_artifacts.py) (SHA-256
  `7a659675dc278e57b6ad6121e734984de08cbdd5a15c06b9742c95876776d678`).
- **`leanprover/kraken`:** Commit `8af78062037bc237b341d20252aafd1797c1bcb7`
  (tree `e8d44f05dd01f8fc1564f57ef00237d8e1a9d825`, pinned upstream to
  `leanprover/lean4:v4.20.1`).
- **`leanprover/lean4`:** Release `v4.34.1`, commit
  `5045d0056413266e57c625dcd7c365b10e377c52` on `x86_64-unknown-linux-gnu`
  under deterministic flags `-j1 -M768`.

Companion packages in this repository cover adjacent aspects of the Kraken
`8af7806` model:

- `reports/kraken-aarch64-selected-instruction-validation-8af7806/` covers the
  bit-level decode/execute semantics of `LDR`, `STR`, `MOV`/`ORR`, and `RET`.
- `reports/kraken-parser-layout-fragment-boundaries-8af7806/` covers the six
  instruction-layout families in `Kraken/AArch64/Parser/Basic.lean`.
- `reports/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/` and
  `reports/kraken-consumer-bound-scalar-certificate-checker-8af7806/` cover
  byte-decoded leaf resource adapters and consumer-bound scalar certificate
  checkers.
- `reports/rust-inline-assembly-contracts-2dafab9/` covers the earlier Rust
  Reference `2dafab9` snapshot.

## Findings

### 1. Rust Reference `82da570b` Normative Contract and `[attributes.codegen.inline.ignored]`

- **Basis:** `normative` (`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`,
  recorded in [`support/reference-selected-identities.json`](support/reference-selected-identities.json)).

Across the six normative files in `rust-lang/reference@82da570b`:

| Normative Rule ID | File & Lines | Technical Consequence for Assembly Boundary Verification |
|---|---|---|
| `[attributes.codegen.inline.ignored]` | `src/attributes/codegen.md:83-84` | `#[inline]` (including `#[inline(never)]`) is ignored on externally exported functions carrying `#[no_mangle]` or `#[export_name]`. Source annotations alone cannot guarantee a non-inlined `bl` call site in an exported caller wrapper. |
| `[attributes.codegen.naked.intro]` .. `[attributes.codegen.naked.body]` | `src/attributes/codegen.md:148-206` | A `#[unsafe(naked)]` function body must consist of a single `core::arch::naked_asm!` call, suppresses compiler prologue/epilogue generation, and requires assembly code to respect the declared `extern "C"` ABI and return path. |
| `[asm.rules.abi]` & `[asm.register-operands.abi-clobbers]` | `src/inline-assembly.md:1079-1182` | Any register or memory modification not declared via operands or clobbers violates the inline/naked assembly contract; `aarch64` `extern "C"` passes the first two 64-bit integer/pointer arguments in `x0` and `x1` and returns the 64-bit result in `x0` (`x30`/`lr` holds the return address). |
| `[layout.array]` & `[layout.repr.c.struct]` | `src/type-layout.md:191-194, 344-391` | A `#[repr(C)]` wrapper around `[u64; 2]` has size 16 bytes, alignment 8 bytes, `slot0` at byte offset `0`, and `slot1` at byte offset `8`. |

### 2. Return-Value vs. Two-Slot Memory Footprint Discrimination (`boundary.rs`)

- **Basis:** `source`, `execution`, and `derived` ([`support/boundary.rs`](support/boundary.rs)
  and [`support/kraken_effects_and_parser_opacity_probe.lean`](support/kraken_effects_and_parser_opacity_probe.lean)).

In [`support/boundary.rs`](support/boundary.rs) (SHA-256
`e6ea8e1c426d4d88c69e20f3753c35806a41fac76e6ea0ad34d2ce509029e21e`), the
selected 4-instruction `#[unsafe(naked)] pub unsafe extern "C" fn _anneal_exchange(slot: *mut u64, value: u64) -> u64`
leaf is compared against a wrong-slot control inside a 16-byte `#[repr(C)] struct Pair([u64; 2])`
buffer initialized to `[a, b]`:

| Variant | Instruction Sequence | Little-Endian 32-bit Words | Post-Call `(ret_x0, slot0, slot1)` |
|---|---|---|---|
| `positive` (`#[cfg(not(anneal_control))]`) | `ldr x2, [x0]; str x1, [x0]; mov x0, x2; ret` | `0xf9400002, 0xf9000001, 0xaa0203e0, 0xd65f03c0` (`020040f9010000f9e00302aac0035fd6`) | `(a, v, b)` |
| `control` (`#[cfg(anneal_control)]`) | `ldr x2, [x0]; str x1, [x0, #8]; mov x0, x2; ret` | `0xf9400002, 0xf9000401, 0xaa0203e0, 0xd65f03c0` (`020040f9010400f9e00302aac0035fd6`) | `(a, a, v)` |

Because `slot` points to `pair.0.as_mut_ptr()`, `str x1, [x0, #8]` writes into
`pair.0[1]`—which is allocated, aligned, and initialized memory—so the control
leaf executes deterministically without trapping in hardware while violating the
narrow single-slot `&mut u64` write contract `[x0, x0 + 8)`. Machine-checked
theorems in [`support/kraken_effects_and_parser_opacity_probe.lean`](support/kraken_effects_and_parser_opacity_probe.lean)
establish:

- **`return_value_only_cannot_distinguish`:** Observing only `(s.x0, s.pc)` yields
  `some (a, 0x2000)` on both `positiveLeafProg` and `wrongSlotLeafProg` for all
  `(baseAddr, a, v, b)`.
- **`effects_all_accepts_wrong_slot_when_equal`:** When `a == v`, even checking
  `(s.x0 == a) && (s.slot0 == a) && (s.pc == 0x2000)` under Kraken's default
  `Effects.All` returns `true` on `wrongSlotLeafProg`, because `slot0` already
  contained `a == v` and `Effects.All` ignores the out-of-footprint write event
  `require_write_access (baseAddr + 8) 8`.
- **`two_slot_state_discriminator`:** Observing the full 2-slot state
  `(s.x0, s.slot0, s.slot1)` yields `some (a, v, b)` on `positiveLeafProg` versus
  `some (a, a, v)` on `wrongSlotLeafProg`, separating the two programs whenever
  `v != a` or `v != b` (e.g., on the four test vectors in `boundary.rs:5-10`).

### 3. Mach-O `aarch64` Relocation Binding and Non-Overlapping `ARM64_RELOC_ADDEND` Rejection (`bind_artifacts.py`)

- **Basis:** `source` and `execution` ([`support/bind_artifacts.py`](support/bind_artifacts.py)
  and [`support/macho_relocation_controls.eval.json`](support/macho_relocation_controls.eval.json)).

Because source-level `#[inline(never)]` on `_anneal_call` is normatively ignored
under `[attributes.codegen.inline.ignored]`, [`support/bind_artifacts.py`](support/bind_artifacts.py)
verifies the compiled `.o` (`MH_OBJECT = 1`) and linked executable (`MH_EXECUTE = 2`)
pair directly:

1. **Exact Symbol & VM-to-File Mapping (`selected_range`, lines 245–280):**
   Resolves `_anneal_exchange` (16 bytes) and `_anneal_call` in `__TEXT,__text`,
   checks that no interior symbols or overlapping sections/segments exist, and
   verifies that in `MH_EXECUTE` the section file offset equals
   `segment.file_offset + symbol.value - segment.address`
   (stage `selected-vm-file-mapping`).
2. **Leaf Byte Identity and Instruction Word Decode (`decode_leaf`, lines 288–305):**
   Requires byte-for-byte identity between `.o` and linked executable leaf ranges
   (`leaf-byte-identity`), zero relocations overlapping the leaf (`leaf-relocation`),
   and exact bit-field masks for `ldr x2, [x0]`, `str x1, [x0, #0/#8]`,
   `mov x0, x2` (`orr x0, xzr, x2`), and `ret` (`x30`).
3. **Call-Site `bl` Relocation and Table-Index Adjacency (`object_call_relocation`, lines 317–329):**
   In `.o`, the 4-byte `bl` instruction at `pc = caller.entry + call_offset` must
   have zero embedded branch immediate (`word & 0x3ffffff == 0`) and exactly one
   overlapping relocation with `r_type == 2` (`ARM64_RELOC_BRANCH26`),
   `r_length == 2` (4 bytes), `r_extern == 1`, `r_pcrel == 1`, and
   `r_symbolnum == leaf.symbol_index`. Crucially, lines 326–328 also enforce:
   ```python
   need(not any(r["section"] == relocation["section"] and
                r["table_index"] + 1 == relocation["table_index"] and r["type"] == 10
                for r in image["relocations"]), "paired-call-addend")
   ```
   In Mach-O `ARM64`, an `ARM64_RELOC_ADDEND` (`r_type == 10`) record pairs with
   the immediately following relocation entry by relocation-table index
   (`table_index + 1`), regardless of its `r_address` (`offset`) field. As
   re-validated in [`support/macho_relocation_controls.eval.json`](support/macho_relocation_controls.eval.json)
   (control 12, `nonoverlapping-preceding-call-addend`), inserting an
   `ARM64_RELOC_ADDEND` record at `table_index == relocation["table_index"]` with
   `offset = caller_offset` (which does **not** overlap the `bl` instruction at
   `caller_offset + 8`) passes byte-range overlap filters (`overlapping(addend, obj, call_range) == False`)
   but is deterministically rejected at stage `paired-call-addend`. All 13
   synthetic negative controls pass for both `positive` and `control` cells.

### 4. Kraken `8af7806` Recursive `partial def` Parser Opacity vs. Fuel-Bounded Kernel Reduction

- **Basis:** `source` and `execution` (`Kraken/AArch64/Parser/Basic.lean:138-152, 703`,
  `Lean/Elab/PreDefinition/Main.lean:299-320`, `Lean/Compiler/LCNF/ToDecl.lean:100-117`,
  `Lean/Meta/Eqns.lean:142-151`, and
  [`support/kraken_effects_and_parser_opacity_probe.lean`](support/kraken_effects_and_parser_opacity_probe.lean)).

In `leanprover/kraken@8af78062037bc237b341d20252aafd1797c1bcb7`:

- `Kraken.AArch64.Parser.parse` (`Kraken/AArch64/Parser/Basic.lean:703`) parses
  instruction lines by calling operand parsers including `parseAddr`, which calls
  `parseConstExpr` (`Kraken/AArch64/Parser/Basic.lean:138-152`).
- `parseConstExpr` is declared as a recursive `partial def` because parenthesized
  sub-expressions recurse without a structural decrease argument.
- In Lean 4 (`v4.34.1` commit `5045d0056413266e57c625dcd7c365b10e377c52`),
  `addAndCompilePartial` (`Lean/Elab/PreDefinition/Main.lean:299-320`) registers a
  recursive `partial def` in the kernel environment via `addAsAxiom` as a
  `Declaration.opaqueDecl` (`ConstantInfo.opaqueInfo`), while compiling its body
  into an `unsafe` auxiliary definition `._unsafe_rec`
  (`Lean/Compiler/LCNF/ToDecl.lean:100-117`). When tactics or `simp`/`rfl` request
  equational lemmas via `getEqnsFor?` (`Lean/Meta/Eqns.lean:142-151`), Lean
  generates unfolding equations only for `ConstantInfo.defnInfo` and returns
  `none` for `ConstantInfo.opaqueInfo`.
- Re-validated in [`support/kraken_effects_and_parser_opacity_probe.lean`](support/kraken_effects_and_parser_opacity_probe.lean)
  under `lean -j1 -M768` (`1.567s`, `522.9 MB` max RSS in
  [`support/kraken_effects_and_parser_opacity_probe.eval.json`](support/kraken_effects_and_parser_opacity_probe.eval.json)):
  1. `#eval parseImmPartial ['#', '8']` succeeds in `MetaM` and outputs `some 8`
     (verified by `#guard_msgs`).
  2. Attempting a kernel proof `example : parseImmPartial ['#', '8'] = some 8 := Eq.refl (parseImmPartial ['#', '8'])`
     fails with a kernel type mismatch because `parseImmPartial` remains stuck on
     the opaque constant `parseConstExprPartial` (verified by `#guard_msgs`).
  3. Replacing `parseConstExprPartial` with the fuel-bounded structural parser
     `parseConstExprFuel (fuel : Nat)` yields kernel reflexivity proofs
     `parseImmFuel_hash8`, `parseImmFuel_expr8`, `parse_positive_leaf_rfl`,
     `parse_wrong_slot_leaf_rfl`, `print_parse_roundtrip_positive`, and
     `print_parse_roundtrip_wrong_slot` by `rfl`.

### 5. Kraken `8af7806` `Effects.All` Permissiveness vs. Strict Footprint Observation

- **Basis:** `source` and `execution` (`Kraken/AArch64/Semantics.lean:171-221, 319-327, 980-993`,
  `Kraken/AArch64/OmniSemantics.lean:13-22`, and
  [`support/kraken_effects_and_parser_opacity_probe.lean`](support/kraken_effects_and_parser_opacity_probe.lean)).

In `leanprover/kraken@8af78062037bc237b341d20252aafd1797c1bcb7`:

1. `MachineData.load` and `MachineData.store` (`Kraken/AArch64/Semantics.lean:199-221`)
   wrap every memory read and write in `Effects.require_read_access addr n` and
   `Effects.require_write_access addr n`, while instruction fetch wraps execution
   in `Effects.require_exec_access pc 4`.
2. However, `Effects.All` (`Kraken/AArch64/OmniSemantics.lean:13-22`) and
   `Executable.eval` (`Kraken/AArch64/Semantics.lean:980-993`) strip and ignore
   all three access constructors (`require_*_access => Effects.All k`), and
   `checkSPAlignment` (`Kraken/AArch64/Semantics.lean:319-327`) checks alignment
   only when the base register is `SP`.
3. As proved in [`support/kraken_effects_and_parser_opacity_probe.lean`](support/kraken_effects_and_parser_opacity_probe.lean):
   - `strict_observe_accepts_positive_leaf`: A custom permission-and-alignment
     observer `Effects.StrictObserve` parameterized by the narrow 1-slot
     `FootprintPolicy` (`code: [0x1000, 0x1010)`, `read: [0x4000, 0x4008)`,
     `write: [0x4000, 0x4008)`) accepts `positiveLeafProg` and establishes
     `(s.x0, s.slot0, s.slot1, s.pc) = (42, 99, 7, 0x2000)` by `decide`.
   - `strict_observe_rejects_wrong_slot_even_when_all_values_equal`: Even when
     `a = v = b = 42` (where both return value and memory contents after
     execution are identical to the positive specification),
     `Effects.StrictObserve` rejects `wrongSlotLeafProg` (`= false` by `decide`)
     because `require_write_access 0x4008 8` violates `writeBase = 0x4000, writeLen = 8`.
   - `effects_all_accepts_unaligned_x0_access` vs.
     `strict_observe_rejects_unaligned_x0_access`: On an unaligned base address
     `baseAddr = 0x4004`, `Effects.All` accepts `positiveLeafProg` (`= true` by
     `decide`) because `x0 != sp`, whereas `Effects.StrictObserve` rejects it
     (`= false` by `decide`) at `require_read_access 0x4004 8`.

## Boundaries

- **Not examined:**
  - Native hardware execution on an `aarch64-apple-darwin` host (this Linux
    `x86_64` environment re-validates the Mach-O parser/relocation verifier and
    Lean 4.34.1 mechanization directly).
  - System registers, SIMD/FP instructions, atomics, exceptions, and virtual
    memory translation outside the 4-instruction scalar `LDR`/`STR`/`MOV`/`RET`
    leaf fragment.
- **Unknown:**
  - Whether upstream `leanprover/kraken` intends a future `Effects` interpreter
    beyond `Effects.All` and `Executable.eval` to consume `require_read_access`,
    `require_write_access`, and `require_exec_access`.
- **Known not to apply:**
  - `[attributes.codegen.inline]` does **not** guarantee non-inlining on
    `#[no_mangle]` or `#[export_name]` functions (`[attributes.codegen.inline.ignored]`).
  - `Lean.Meta.getEqnsFor?` and kernel `rfl` / `decide` reduction do **not**
    apply to `Kraken.AArch64.Parser.parseConstExpr` (or any caller reaching it)
    while `parseConstExpr` remains a recursive `partial def`.
  - Kraken's default `Effects.All` and `Executable.eval` do **not** enforce memory
    read/write/execute footprints or general-purpose register alignment.
- **Unsupported:**
  - In [`support/bind_artifacts.py`](support/bind_artifacts.py), 32-bit Mach-O
    segments (`unsupported-32-bit-segment`), multi-segment relocatable objects
    (`unsupported-object-container`), non-zero external/local dynamic symbol table
    relocations (`unsupported-global-relocations`), and relocations overlapping
    the leaf body (`leaf-relocation`) are explicitly unsupported and rejected.

## Evidence

| File | SHA-256 | Role |
|---|---|---|
| [`support/boundary.rs`](support/boundary.rs) | `e6ea8e1c426d4d88c69e20f3753c35806a41fac76e6ea0ad34d2ce509029e21e` | Rust `aarch64-apple-darwin` `#[unsafe(naked)]` leaf (`_anneal_exchange`) and caller (`_anneal_call`) specimen with positive (`str x1, [x0]`) and wrong-slot control (`str x1, [x0, #8]`) variants |
| [`support/bind_artifacts.py`](support/bind_artifacts.py) | `7a659675dc278e57b6ad6121e734984de08cbdd5a15c06b9742c95876776d678` | Data-only 64-bit Mach-O `aarch64` object/executable binding and relocation verifier with 13 built-in negative controls |
| [`support/reference-selected-identities.json`](support/reference-selected-identities.json) | `dc54275b2b912b5fb62da3164d1ccbf4c37b4b8b9e638df8bc615e862898115f` | Commit, tree, and blob SHA-256/Git-SHA1 manifest for the 6 normative files in `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` |
| [`support/kraken_effects_and_parser_opacity_probe.lean`](support/kraken_effects_and_parser_opacity_probe.lean) | `c6086d0cbc3d4ec4337558502df878bee4e06fc3ddf6712cdbc9bc3f30436336` | Standalone Lean 4.34.1 mechanization of recursive `partial def` kernel opacity vs. fuel-bounded reduction and `Effects.All` vs. `Effects.StrictObserve` |
| [`support/kraken_effects_and_parser_opacity_probe.eval.json`](support/kraken_effects_and_parser_opacity_probe.eval.json) | `8489aa64f7b0c46c97074a57d768173c8dfdc69f848ab96ef5c88488a34db9fa` | Fresh Lean 4.34.1 (`-j1 -M768`) execution record (`returncode: 0`, `1.567s`, `522,904 KB` max RSS) |
| [`support/macho_relocation_controls.eval.json`](support/macho_relocation_controls.eval.json) | `7ff2bc4fc2619d799a1030b3f9262bfdc316a5e18ab30fb835494192a55537c2` | Execution output of `bind_artifacts.py` positive, control, and 13 synthetic negative controls (including `nonoverlapping-preceding-call-addend`) |

## Revalidation

To re-validate the Lean 4.34.1 mechanization under `-j1 -M768`:

```bash
lean +leanprover/lean4:v4.34.1 -j1 -M768 \
  reports/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/support/kraken_effects_and_parser_opacity_probe.lean
```

To re-validate the Mach-O `aarch64` positive/control binding and all 13 synthetic
negative controls (including `ARM64_RELOC_ADDEND` table-index adjacency):

```bash
python3 - <<'PY'
import struct, sys
sys.path.insert(0, "reports/rust-inline-asm-macho-relocations-and-kraken-aarch64-bridge/support")
import bind_artifacts as ba

def make_obj(store_word):
    words = (0xF9400002, store_word, 0xAA0203E0, 0xD65F03C0,
             0xA9BF7BFD, 0x910003FD, 0x94000000, 0xA8C17BFD, 0xD65F03C0)
    text = b"".join(struct.pack("<I", w) for w in words)
    r_bits = 0 | (1 << 24) | (2 << 25) | (1 << 27) | (2 << 28)
    reloc = struct.pack("<iI", 0x18, r_bits)
    reloff, symoff = 0xD0 + len(text), 0xD0 + len(text) + len(reloc)
    strtab = b"\x00_anneal_exchange\x00_anneal_call\x00"
    syms = struct.pack("<IBBHQ", 1, 0x0F, 1, 0, 0) + struct.pack("<IBBHQ", 18, 0x0F, 1, 0, 0x10)
    hdr = struct.pack("<IiiIIIII", 0xFEEDFACF, 0x0100000C, 0, 1, 2, 176, 0, 0)
    seg = struct.pack("<II16sQQQQiiII", 0x19, 152, b"\x00"*16, 0, len(text)+16, 0xCC, len(text)+16, 7, 7, 1, 0)
    sec = struct.pack("<16s16sQQIIIIIIII", b"__text\x00"+b"\x00"*9, b"__TEXT\x00"+b"\x00"*9, 0, len(text), 0xD0, 2, reloff, 1, 0x80000400, 0, 0, 0)
    sym = struct.pack("<IIIIII", 2, 24, symoff, 2, symoff + len(syms), len(strtab))
    return hdr + seg + sec + sym + text + reloc + syms + strtab

def make_exe(store_word):
    bl_word = 0x94000000 | ((-6) & 0x3FFFFFF)
    words = (0xF9400002, store_word, 0xAA0203E0, 0xD65F03C0,
             0xA9BF7BFD, 0x910003FD, bl_word, 0xA8C17BFD, 0xD65F03C0)
    text = b"".join(struct.pack("<I", w) for w in words)
    symoff, sec_addr = 0xE8 + len(text), 0x1000000E8
    strtab = b"\x00_anneal_exchange\x00_anneal_call\x00"
    syms = struct.pack("<IBBHQ", 1, 0x0F, 1, 0, sec_addr) + struct.pack("<IBBHQ", 18, 0x0F, 1, 0, sec_addr + 0x10)
    stroff = symoff + len(syms)
    total = stroff + len(strtab)
    hdr = struct.pack("<IiiIIIII", 0xFEEDFACF, 0x0100000C, 0, 2, 3, 200, 0, 0)
    seg = struct.pack("<II16sQQQQiiII", 0x19, 152, b"__TEXT\x00"+b"\x00"*9, 0x100000000, total, 0, total, 7, 5, 1, 0)
    sec = struct.pack("<16s16sQQIIIIIIII", b"__text\x00"+b"\x00"*9, b"__TEXT\x00"+b"\x00"*9, sec_addr, len(text), 0xE8, 2, 0, 0, 0x80000400, 0, 0, 0)
    sym = struct.pack("<IIIIII", 2, 24, symoff, 2, stroff, len(strtab))
    main = struct.pack("<IIQQ", 0x80000028, 24, 0xF8, 0)
    return hdr + seg + sec + sym + main + text + syms + strtab

obj, exe = ba.parse(make_obj(0xF9000001), 1), ba.parse(make_exe(0xF9000001), 2)
oleaf, ocaller, oword, opc = ba.bind(obj, 20, 8)
eleaf, ecaller, eword, epc = ba.bind(exe, 20, 8)
assert ba.pair_identity(oleaf, eleaf, "positive") == [0xF9400002, 0xF9000001, 0xAA0203E0, 0xD65F03C0]
reloc = ba.object_call_relocation(obj, ocaller, oword, opc, oleaf)
call = ba.linked_call(eword, epc, eleaf["entry"])
controls = ba.negative_controls(obj, exe, oleaf, eleaf, ocaller, reloc, call, "positive", None, oword, opc)
assert len(controls) == 13
print("Verified 13 Mach-O negative controls successfully.")
PY
```
