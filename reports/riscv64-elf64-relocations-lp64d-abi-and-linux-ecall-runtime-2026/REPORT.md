<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# RISC-V 64-Bit (`RV64GC`) Instruction Encoding, ELF64 Relocations, `LP64D` Calling Convention, and Freestanding Linux `ecall` Runtime

## Summary

Lowering a verified compiler backend directly to native
`riscv64gc-unknown-linux-gnu` ELF64 relocatable object files (`.o`) without
delegating to an external assembler requires discharging four coupled
architectural and linker invariants:

1. **12-bit signed immediate overflow (`[-2048, 2047]`) in large stack frames
   and `lui` + `addi` sign-extension compensation**: `RV64I` I-type (`addi`,
   `ld`, `lw`, `lbu`, `jalr`) and S-type (`sd`, `sw`, `sb`) instructions encode
   only a 12-bit two's-complement immediate. When a function's stack frame
   exceeds `2,047` bytes (for example, `112` eight-byte spill slots plus saved
   `ra`/`s0` aligned to `2,720` bytes = `0xaa0`), emitting `frame_size` or
   `-frame_size` directly in `addi sp, sp, -frame_size` or `ld`/`sd` truncates
   the offset modulo `4,096` and sign-extends bit 11 (`0x800`), turning `+2720`
   into `-1376` and `-2720` into `+1376`. Materializing arbitrary 32-bit signed
   offsets requires the sign-compensated decomposition `hi20 = ((imm + 0x800) >>
   12) & 0xfffff` and `lo12 = imm & 0xfff` into dedicated scratch registers `t3`
   (`x28`) and `t4` (`x29`) (`lui t4, hi20; addi t4, t4, lo12; add t4, sp, t4;
   ld/sd reg, 0(t4)`).
2. **Conditional `B`-type (`±4 KiB`) vs. `J`-type (`±1 MiB`) vs. `auipc`+`jalr`
   (`±2 GiB`) multi-round branch relaxation**: Conditional `B`-type instructions
   (`beq`, `bne`, `blt`, `bge`, `bltu`, `bgeu`) scramble a 13-bit signed even
   byte offset (`imm[12|10:5|4:1|11]`, range `[-4096, +4094]` bytes = `[-1024,
   +1023]` instructions). Functions exceeding `1,024` instructions overflow
   `B`-type offsets unless out-of-range branches are relaxed by inverting the
   condition (`funct3 ^ 1`) over an unconditional `jal x0, target` (`+8` bytes,
   `±1 MiB`) or `auipc t6, hi20; jalr x0, lo12(t6)` (`+12` bytes, `±2 GiB`).
   Because each relaxed branch expands `.text` by `+4` or `+8` bytes and shifts
   all subsequent label offsets, single-pass relaxation can push an enclosing
   near-threshold branch past `4,094` bytes, requiring a multi-round fixed-point
   loop paired with a two-pass layout verifier.
3. **RISC-V ELF64 `ET_REL` `.symtab` partition and indirect
   `R_RISCV_PCREL_LO12_I`/`_S` relocations**: `lld` (`lld/ELF/InputFiles.cpp`
   and `lld/ELF/Arch/RISCV.cpp`) enforces two strict ELF64 invariants on
   `EM_RISCV` (`243`, `e_flags = 0x0005`) relocatable objects: (a) all
   `STB_LOCAL` (`0`) symbols in `.symtab` must precede all `STB_GLOBAL` (`1`)
   symbols, with `.symtab.sh_info` equal to the index of the first `STB_GLOBAL`
   symbol; and (b) `R_RISCV_PCREL_LO12_I` (`24`) and `R_RISCV_PCREL_LO12_S`
   (`25`) are **indirect** relocations whose `r_sym` must reference a local
   label (`.Lpcrel_hi*`) at the address `P_auipc` of the paired `auipc`
   (`R_RISCV_PCREL_HI20` = `23`) instruction—not the target `.rodata`/`.data`
   symbol `S`—so the linker computes `lo12 = (S + A - P_auipc) & 0xfff`.
4. **`LP64D` calling convention, 3-word trait-object vtables, and freestanding
   Linux `riscv64` `ecall` + `tp` (`x4`) runtime**: Under `LP64D`, aggregates up
   to 8 bytes pass in `a0`, 9–16-byte `ScalarPair` values (fat pointers
   `&[T]`/`&str`/`&dyn Trait`, `u128`/`i128`, 2-word `Result`/`Option`) pass in
   `(a0, a1)`, and aggregates `> 16` bytes pass indirectly via a
   caller-allocated `sret` buffer pointer in `a0`. Dynamic trait dispatch reads
   a 3-word header `[drop_in_place, size, align, method_0, ...]` in
   `.data.rel.ro` populated via `R_RISCV_64` (`2`) relocations (method `i` at
   byte offset `24 + 8 * i`), while freestanding process I/O, allocation,
   entropy, and termination invoke the Linux `riscv64` generic UAPI syscall
   numbers (`SYS_read = 63`, `SYS_write = 64`, `SYS_exit = 93`,
   `SYS_exit_group = 94`, `SYS_brk = 214`, `SYS_mmap = 222`,
   `SYS_getrandom = 278`) via `a7` (`x17`), `a0`–`a5` (`x10`–`x15`), and
   `ecall` (`0x00000073`).

## Applicability

These results apply to verified compiler backends, binary object emitters, and
translation validators targeting 64-bit RISC-V Linux
(`riscv64gc-unknown-linux-gnu`):

- **ISA and ABI Specifications**:
  - *The RISC-V Instruction Set Manual, Volume I: Unprivileged ISA* (`RV64I`
    base integer instruction set, `M` integer multiply/divide, `A` atomic
    instructions and `fence`, `F`/`D` single/double-precision floating-point,
    and `C` compressed 16-bit instructions).
  - *RISC-V ELF psABI Specification* (`riscv-non-isa/riscv-elf-psabi-doc`,
    revision `7188fa53123d7eb9ef8dbad02db2ca2cabdf9c62`), governing the `LP64D`
    calling convention, ELF header flags (`EF_RISCV_RVC = 0x0001`,
    `EF_RISCV_FLOAT_ABI_DOUBLE = 0x0004`), and relocation table semantics.
- **Formal ISA Models and Theorem Prover**:
  - `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`) and
    `joshlf/anneal` (`beb778bb135474a67dc017c185d2753a60693d8c`).
  - `leanprover/lean4` version `4.34.1`
    (`5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`,
    binary SHA-256
    `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`).
- **Linker, Binary Inspection, and Emulation Toolchains**:
  - `llvm/llvm-project` `21.1.8` (`85a90d119deb25b518867cd37d62c7b93b575a6f`,
    `lld/ELF/Arch/RISCV.cpp`, `lld/ELF/InputFiles.cpp`,
    `llvm/include/llvm/BinaryFormat/ELFRelocs/RISCV.def`), exercised via
    `rust-lld -flavor gnu -m elf64lriscv` (SHA-256
    `ed7d2923baca14739c3df6ce3393ba07116e7f529b785bcec2d1e25f90d28173`),
    `llvm-readelf-21` (SHA-256
    `bc93dae4a9c5584add48d2a5953232bc86eea82d2f3abe47b4c6c75ef006482a`), and
    `llvm-objdump-21` (SHA-256
    `fa677a86e691b7c42c29bfd1690edf5c3e0b7d5b9b8bb0aaef19f795e15b9021`).
  - `qemu-riscv64` version `11.1.0` (`1:11.1.0+ds-2`, SHA-256
    `328369968794f853dde737be961b290fe74cb21ff4f23de65ed52a281d360d40`).

## Findings

### 1. 12-Bit Signed Immediate Overflow (`[-2048, 2047]`), `lui` + `addi` Sign-Extension Compensation, and `.fence` Bitfields

**Basis: source | execution | derived**

In the `RV64I` base instruction set, every I-type instruction (`addi`, `ld`,
`lw`, `lbu`, `jalr`) and S-type instruction (`sd`, `sw`, `sb`) encodes a 12-bit
signed two's-complement immediate `imm12` in bits `[31:20]` (for I-type) or
split across `[31:25]` and `[11:7]` (for S-type). At execution time, the CPU
sign-extends bit 11 (`2048 = 0x800`) to 64 bits:

$$\operatorname{sext}_{12}(u) = \begin{cases} (u \bmod 4096) - 4096 & \text{if } (u \bmod 4096) \ge 2048 \\ u \bmod 4096 & \text{if } (u \bmod 4096) < 2048 \end{cases}$$

Consequently, single-instruction register-plus-immediate addressing covers only
byte displacements in $[-2048, +2047]$.

#### Silent Sign Inversion in Large Stack Frames (`> 2,047` Bytes)

For a function frame with `N` eight-byte spill slots and 16 bytes reserved for
caller `ra` (`[s0 - 8]`) and `s0` (`[s0 - 16]`), the 16-byte-aligned frame size
is:

$$\operatorname{frameBytes}(N) = \left\lfloor \frac{16 + 8(N + 1) + 15}{16} \right\rfloor \times 16$$

When a function's frame exceeds `2,047` bytes—for instance, `2,720` bytes
(`0xaa0`) for a 112-slot frame, or any frame with `frameBytes >= 2048`—emitting
`addi sp, sp, -frameBytes`, `addi s0, sp, frameBytes`, or `ld`/`sd` with an
unsplit 12-bit immediate silently wraps the immediate modulo `4,096` and flips
its sign whenever bit 11 (`0x800`) is set:

- `+2720` (`0xaa0` has bit 11 equal to `1`) is decoded by `addi`/`ld`/`sd` as
  $2720 - 4096 = -1376$ (`-0x560`).
- `-2720` (`(-2720) mod 4096 = 1376 = 0x560` has bit 11 equal to `0`) is decoded
  by `addi sp, sp, -2720` as $+1376$ (`+0x560`), advancing `sp` upward into the
  caller's stack frame instead of allocating stack storage and causing stack
  corruption or `SIGSEGV`.

This failure mode is machine-checked in
`control_large_frame_2720_direct_imm12_sign_flips` in
[`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean).

#### Exact 32-Bit Signed Offset Materialization via `lui` + `addi`

To materialize an arbitrary 32-bit signed displacement `imm` into a register
`rd`, the backend pairs `lui rd, hi20` (loading
$\operatorname{sext}_{32}(\text{hi20} \ll 12)$) with `addi rd, rd, lo12` (adding
$\operatorname{sext}_{12}(\text{lo12})$). A naive split
$\text{hi20}_{\text{naive}} = \lfloor \text{imm} / 4096 \rfloor$,
$\text{lo12} = \text{imm} \bmod 4096$ fails whenever bit 11 of `imm` is set
(`imm mod 4096 >= 2048`), because `addi` subtracts `4,096` (`0x1000`), leaving
the result equal to $\text{imm} - 4096$
(`control_naive_uncompensated_split_fails_when_bit11_set` in
[`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean)).

Adding `0x800` (`2,048`) to `imm` before shifting right by 12 bits increments
`hi20` by `+1` (`+4,096` after shifting left by 12) if and only if bit 11 of
`lo12` is `1`, exactly canceling the `-4,096` from `addi`'s sign extension:

$$\text{hi20} = \left\lfloor \frac{\text{imm} + 2048}{4096} \right\rfloor \bmod 2^{20}, \qquad \text{lo12} = \text{imm} \bmod 4096$$

$$\text{hi20} \cdot 4096 + \operatorname{sext}_{12}(\text{lo12}) = \text{imm}$$

| Signed Offset `imm` | Role in `probe_rv64gc.o` | `hi20` (20-bit hex) | `lo12` (signed / hex) | Reconstructed Sum `hi20 * 4096 + sext12(lo12)` |
| :--- | :--- | :--- | :--- | :--- |
| `+2047` | Maximum positive 12-bit immediate | `0x00000` (`0`) | `+2047` (`0x7ff`) | `0 + 2047 = +2047` |
| `+2048` | First positive overflow boundary | `0x00001` (`+1`) | `-2048` (`0x800`) | `4096 + (-2048) = +2048` |
| `+2400` | Deep spill slot `sp + 2400` | `0x00001` (`+1`) | `-1696` (`-0x6a0` / `0x960`) | `4096 + (-1696) = +2400` |
| `+2704` | Saved `s0` slot `sp + 2704` | `0x00001` (`+1`) | `-1392` (`-0x570` / `0xa90`) | `4096 + (-1392) = +2704` |
| `+2712` | Saved `ra` slot `sp + 2712` | `0x00001` (`+1`) | `-1384` (`-0x568` / `0xa98`) | `4096 + (-1384) = +2712` |
| `+2720` | Epilogue frame deallocation `+2720` | `0x00001` (`+1`) | `-1376` (`-0x560` / `0xaa0`) | `4096 + (-1376) = +2720` |
| `-2048` | Minimum negative 12-bit immediate | `0x00000` (`0`) | `-2048` (`0x800`) | `0 + (-2048) = -2048` |
| `-2049` | First negative overflow boundary | `0xfffff` (`-1`) | `+2047` (`0x7ff`) | `-4096 + 2047 = -2049` |
| `-2720` | Prologue frame allocation `-2720` | `0xfffff` (`-1`) | `+1376` (`+0x560`) | `-4096 + 1376 = -2720` |

Universal correctness across all non-negative and signed offsets is proved in
`lui_addi_compensated_exact`, `lui_addi_signed_exact`, and
`large_frame_boundary_offsets_verified` in
[`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean).
To avoid clobbering live expression temporaries (`t0`–`t2`), frame/stack
pointers (`s0`, `sp`, `ra`, `gp`, `tp`), or `LP64D` argument/return registers
(`a0`–`a7`), large-frame address calculation reserves caller-saved scratch
registers `t3` (`x28`) and `t4` (`x29`)
(`scratch_t3_t4_disjoint_from_abi_and_frame_regs`), emitting:

```text
lui  t4, hi20(offset)
addi t4, t4, lo12(offset)
add  t4, sp, t4
ld/sd reg, 0(t4)
```

#### Little-Endian `ReadWord32`/`WriteWord32` Round-Trip and `.fence` Encoding

In [`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean),
`readU32LE_leBytes32` and `readU32LE_encodeRv64RawInsn` prove that every 32-bit
encoded `RV64GC` instruction word `w = encodeRv64RawInsn insn` satisfies
`readU32LE (leBytes32 w) = w`. Furthermore, `fence_iorw_encoding` and
`control_fence_zero_imm_omits_pred_succ` verify the `MISC-MEM` (`opcode = 0x0f`)
encoding of `fence iorw, iorw`: bits `[27:24]` hold the predecessor ordering
mask `pred = 0xf` (`iorw`) and bits `[23:20]` hold the successor ordering mask
`succ = 0xf` (`iorw`), yielding `imm12 = 0x0ff` and the 32-bit word `0x0ff0000f`
(little-endian bytes `[0x0f, 0x00, 0xf0, 0x0f]`), whereas encoding `imm12 = 0`
produces `0x0000000f` with empty ordering sets (`pred = 0, succ = 0`).

### 2. Conditional `B`-Type (`±4 KiB`) vs. `J`-Type (`±1 MiB`) vs. `auipc`+`jalr` (`±2 GiB`) and Multi-Round Cascading Branch Relaxation

**Basis: source | execution | derived**

The three PC-relative control-flow encodings in `RV64I` have distinct bit
scrambling and reach limits:

| Format & Instructions | Bit Layout in 32-Bit Instruction Word | Signed Byte Reach | 32-Bit Instruction Reach |
| :--- | :--- | :--- | :--- |
| **`B`-type** (`beq`, `bne`, `blt`, `bge`, `bltu`, `bgeu`, `opcode = 0x63`) | `inst[31] = imm[12]`, `inst[30:25] = imm[10:5]`, `inst[11:8] = imm[4:1]`, `inst[7] = imm[11]` (`imm[0] = 0`) | `[-4096, +4094]` (`±4 KiB`) | `[-1024, +1023]` instructions |
| **`J`-type** (`jal`, `opcode = 0x6f`) | `inst[31] = imm[20]`, `inst[30:21] = imm[10:1]`, `inst[20] = imm[11]`, `inst[19:12] = imm[19:12]` (`imm[0] = 0`) | `[-1048576, +1048574]` (`±1 MiB`) | `[-262144, +262143]` instructions |
| **Far PC-relative pair** (`auipc t6, hi20; jalr x0, lo12(t6)`) | `U`-type (`0x17`) + `I`-type (`0x67`) using `t6` (`x31`) | `[-2147483648, +2147481599]` (`±2 GiB`) | `≈ ±536.8 million` instructions |

Universal bit-scrambling round-trip for every even `imm13 < 8192` and every even
`imm21 < 2097152` is machine-checked in `reconstructBImm13_roundtrip`,
`reconstructJImm21_roundtrip`, and `bType_and_jType_boundary_encodings_verified`
in [`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean).

#### Condition Inversion (`funct3 ^ 1`) and Multi-Round Cascading Relaxation

When a function exceeds `1,024` instructions (`4,096` bytes), any conditional
branch `B_cond rs1, rs2, target` whose byte displacement `delta = target_pc -
branch_pc` falls outside `[-4096, +4094]` overflows `imm13`. Because `RV64I`
provides no 21-bit or 32-bit conditional branch instruction, the backend relaxes
the branch by inverting `funct3` (`funct3 ^ 1`: `beq (0) <-> bne (1)`, `blt (4)
<-> bge (5)`, `bltu (6) <-> bgeu (7)`, proved involutive in
`invertBranchFunct3_involutive`) to skip over an unconditional jump
(`relaxed_branch_control_flow_equiv`):

- **Medium relaxation (`±1 MiB`, 8 bytes total, `+4` bytes expansion)**:
  ```text
  B_inv_cond rs1, rs2, +8    # if !cond, skip to fallthrough at pc + 8
  jal        x0, target      # if cond, jump to target (±1 MiB)
  ```
- **Far relaxation (`±2 GiB`, 12 bytes total, `+8` bytes expansion)**:
  ```text
  B_inv_cond rs1, rs2, +12   # if !cond, skip to fallthrough at pc + 12
  auipc      t6, hi20(delta) # t6 = auipc_pc + (hi20 << 12)
  jalr       x0, lo12(delta)(t6)
  ```

Relaxing one conditional branch inserts `+4` (or `+8`) bytes into `.text`,
increasing the byte span of every outer branch that crosses the relaxed site. As
proved in `cascading_relaxation_single_pass_fails_and_fixpoint_succeeds` in
[`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean),
if an outer branch initially has displacement `4,092` bytes (`<= 4,094`, valid
for `B`-type) and spans across an inner branch with displacement `4,096` bytes
(`> 4,094`, requiring relaxation), a single relaxation pass expands the inner
branch by `+4` bytes and pushes the outer branch's displacement to `4,096` bytes
(`> 4,094`), invalidating the layout. Branch relaxation must therefore iterate
to a multi-round fixed point (`relaxFixpoint`) until no unrelaxed branch exceeds
its reach bound.

### 3. RISC-V ELF64 `ET_REL` Format, `.symtab` Ordering, and the Indirect `R_RISCV_PCREL_LO12_I`/`_S` Relocation Rule

**Basis: source | execution | derived**

To link cleanly with `rust-lld -flavor gnu -m elf64lriscv` without external
assembly, an `ET_REL` (`e_type = 1`) object file must set `e_machine = EM_RISCV
= 243` (`0xf3`) and `e_flags = 0x0005` (`EF_RISCV_RVC (0x0001) |
EF_RISCV_FLOAT_ABI_DOUBLE (0x0004)`), matching the `LP64D` + `RVC` ABI of
standard Rust target libraries.

#### `.symtab` Local-Before-Global Partition and `sh_info` Invariant

Per the ELF64 specification and `lld/ELF/InputFiles.cpp`, `.symtab` must place
all `STB_LOCAL` (`st_info >> 4 == 0`) symbols—starting with `STN_UNDEF` at index
`0`, section symbols, internal functions, `.rodata`/`.data.rel.ro` objects, and
`.Lpcrel_hi*` labels—before all `STB_GLOBAL` (`1`) and `STB_WEAK` (`2`) symbols,
and `.symtab.sh_info` must equal the exact symbol index of the first non-local
symbol (`1 + count(STB_LOCAL)`).

In [`support/gen_and_verify_rv64_elf.py`](support/gen_and_verify_rv64_elf.py)
(**Negative Probe A**, `neg_symtab_order.o`, SHA-256
`c88e37078a8e98adb980d69e91b350977472ff82db1e12d0fd82d133149df639`), placing a
local label `.Lpcrel_hi0` (`STB_LOCAL = 0`) at symbol index `2` after global
`_start` (`STB_GLOBAL = 1` at index `1`, `sh_info = 1`) causes `rust-lld` to
reject the object file with exit code `1`:

```text
rust-lld: error: neg_symtab_order.o: symbol (2) has invalid binding: 0
```

This partition check is formalized in
`symtab_local_before_global_and_sh_info_controls` in
[`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean).

#### Why `R_RISCV_PCREL_LO12_I` (`24`) and `R_RISCV_PCREL_LO12_S` (`25`) Are Indirect Relocations

In the RISC-V ELF psABI (`riscv-non-isa/riscv-elf-psabi-doc`) and LLVM's
`lld/ELF/Arch/RISCV.cpp` + `llvm/include/llvm/BinaryFormat/ELFRelocs/RISCV.def`,
PC-relative global addressing uses a paired two-instruction sequence:

1. At address `P_auipc`, `auipc rd, 0` carries `R_RISCV_PCREL_HI20` (`23`) whose
   `r_sym` points **directly** to the target symbol `S` (such as `trait_vtable`,
   `tls_slot_data`, or `rodata_banner`) with addend `A`. The linker writes
   `hi20 = ((S + A - P_auipc + 0x800) >> 12) & 0xfffff` into `auipc`, so at
   runtime `rd` receives $P_{\text{auipc}} + (\text{hi20} \ll 12)$.
2. At address `P_lo` (typically `P_auipc + 4`), an I-type instruction (`addi`,
   `ld`, `lw`, `lbu`, `jalr`) carries `R_RISCV_PCREL_LO12_I` (`24`), or an
   S-type store (`sd`, `sw`, `sb`) carries `R_RISCV_PCREL_LO12_S` (`25`).
   Crucially, the low 12 bits added to `rd` must be the low 12 bits of
   $S + A - P_{\text{auipc}}$ (relative to the `auipc` PC $P_{\text{auipc}}$,
   **not** the load/store PC $P_{\text{lo}}$!).

Because multiple load/store instructions at different addresses $P_{\text{lo}}$
can share a single `auipc` at $P_{\text{auipc}}$, the `Elf64_Rela` entry at
$P_{\text{lo}}$ does not know $P_{\text{auipc}}$ unless `r_sym` tells it where
the `auipc` is. Therefore, `R_RISCV_PCREL_LO12_I` (`24`) and
`R_RISCV_PCREL_LO12_S` (`25`) are **indirect**: their `r_sym` must reference a
local symbol (`.Lpcrel_hi*`, `STB_LOCAL`) defined in `.text` at the exact byte
offset $P_{\text{auipc}}$ of the paired `auipc` instruction. The linker looks up
the `R_RISCV_PCREL_HI20` relocation at
$P_{\text{auipc}} = \operatorname{Value}(r_{\text{sym}}) + A_{\text{lo}}$ to
find $S + A_{\text{hi}}$ and writes
$\text{lo12} = (S + A_{\text{hi}} - P_{\text{auipc}}) \bmod 4096$.

- **Formal address proof (`pcrel_lo12_indirect_via_auipc_exact` vs.
  `control_pcrel_lo12_direct_pc_off_by_four`)**: In
  [`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean),
  we prove that indirect calculation relative to $P_{\text{auipc}}$ reconstructs
  `targetAddr` exactly for all addresses, whereas computing `lo12` relative to
  $P_{\text{lo}} = P_{\text{auipc}} + 4$ misses `targetAddr` by `-4` bytes.
- **Empirical linker rejection (**Negative Probe B**, `neg_direct_lo12.o`,
  SHA-256
  `69219e192ce0fc955d582cbfd80de28329db063d344057112235c3c90f62bb07`)**: When
  `R_RISCV_PCREL_LO12_I` at `.text+0x4` sets `r_sym` directly to `rodata_banner`
  instead of `.Lpcrel_hi0`, `rust-lld` rejects the object file with two
  diagnostic errors:
  ```text
  rust-lld: error: neg_direct_lo12.o:(function _start: .text+0x4): R_RISCV_PCREL_LO12 relocation points to a symbol 'rodata_banner' in a different section '.rodata'
  rust-lld: error: neg_direct_lo12.o:(function _start: .text+0x4): R_RISCV_PCREL_LO12 relocation points to neg_direct_lo12.o:(rodata_banner) without an associated R_RISCV_PCREL_HI20 relocation
  ```

#### Complete Relocation Table Exercised in `support/probe_rv64gc.o`

| Relocation Type | ELF Code | Section | Instruction / Slot | `r_sym` Target | Resolved Values in `support/probe_rv64gc.elf` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `R_RISCV_64` | `2` | `.rela.data.rel.ro` | 8-byte pointer slots at `+0x0` and `+0x18` | `drop_noop` (`1`), `vtable_method_add` (`2`) | `0x111c8` (`drop_noop`), `0x111cc` (`vtable_method_add`) |
| `R_RISCV_CALL_PLT` | `19` | `.rela.text` | `auipc ra, 0; jalr ra, 0(ra)` at `.text+0x10cc` | `callee_with_large_frame` (`3`) | `auipc ra, 0xfffff; jalr -0xb8(ra)` (`0x12294 -> 0x111dc`) |
| `R_RISCV_PCREL_HI20` | `23` | `.rela.text` | `auipc` at `.Lpcrel_hi_vtable` (`0x1124`), `.Lpcrel_hi_store` (`0x1180`), `.Lpcrel_hi_tls` (`0x1188`), `.Lpcrel_hi_banner` (`0x11d0`) | `trait_vtable` (`5`), `tls_slot_data` (`6`), `rodata_banner` (`4`) | `auipc t0, 0x1` (`0x122ec`), `auipc t0, 0x1` (`0x12348`), `auipc tp, 0x1` (`0x12350`), `auipc a1, 0xffffe` (`0x12398`) |
| `R_RISCV_PCREL_LO12_I` | `24` | `.rela.text` | `addi` at `0x1128`, `0x118c`, `0x11d4` | Indirect: `.Lpcrel_hi_vtable` (`7`), `.Lpcrel_hi_tls` (`9`), `.Lpcrel_hi_banner` (`10`) | `addi t0, t0, 0xd4`, `addi tp, tp, 0x90`, `addi a1, a1, -0x208` |
| `R_RISCV_PCREL_LO12_S` | `25` | `.rela.text` | `sd a0, 0(t0)` at `0x1184` | Indirect: `.Lpcrel_hi_store` (`8`) | `sd a0, 0x98(t0)` (`0x12348 + 0x1098 = 0x133e0`) |

### 4. `LP64D` Calling Convention, 3-Word Trait-Object Vtables, and Freestanding Linux `riscv64` `ecall` + `tp` (`x4`) Runtime

**Basis: source | execution | derived**

#### `LP64D` Register Roles and Aggregate Passing (`classifyLp64dSize`)

Under the RISC-V `LP64D` psABI (`XLEN = 64`, `FLEN = 64` with
`EF_RISCV_FLOAT_ABI_DOUBLE`):

- **Integer argument/return registers**: `a0`–`a7` (`x10`–`x17`) pass up to 8
  integer/pointer arguments; `a0` (`x10`) and `a1` (`x11`) return integer and
  `ScalarPair` results.
- **Floating-point argument/return registers**: `fa0`–`fa7` (`f10`–`f17`) pass
  hardware `f32`/`f64` arguments; `fa0` and `fa1` return floating-point results.
- **Callee-saved vs. caller-saved preservation**: Callees must preserve `sp`
  (`x2`, 16-byte aligned at call boundaries), `s0`/`fp` (`x8`), `s1` (`x9`),
  `s2`–`s11` (`x18`–`x27`), and `fs0`–`fs11` (`f8`–`f9`, `f18`–`f27`). Callers
  own `ra` (`x1`), `t0`–`t2` (`x5`–`x7`), `t3`–`t6` (`x28`–`x31`), `a0`–`a7`,
  `fa0`–`fa7`, and `ft0`–`ft11`. `gp` (`x3`) and `tp` (`x4`, thread pointer) are
  platform-reserved across normal calls.
- **Aggregate size classification (`lp64d_classification_boundaries` in
  [`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean))**:
  - `0` bytes (ZST): no register or stack transfer (`.zst`).
  - `1..8` bytes: passed/returned in a single 64-bit register `a0`
    (`.directScalar`).
  - `9..16` bytes (`ScalarPair`, including fat pointers `&[T]`, `&str`, and
    `&dyn Trait` as `(data_ptr, meta_word)`, `u128`/`i128`, and 2-word
    `Result`/`Option` enums): passed in two consecutive registers and returned
    in `(a0, a1)` (`.scalarPair`).
  - `> 16` bytes: passed by reference to a caller-allocated buffer; for return
    values, the caller passes the destination buffer address as a hidden first
    argument (`sret`) in `a0` (`.indirectSret`).

#### 3-Word Trait-Object Vtable Layout in `.data.rel.ro`

A Rust `&dyn Trait` fat pointer is a 16-byte `ScalarPair` `(data_ptr: a0,
vtable_ptr: a1)` where `vtable_ptr` points to a read-only `.data.rel.ro` table
with a 3-word (24-byte) metadata header followed by method function pointers
(`vtable_three_word_header_offsets` in
[`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean)):

- Offset `0` (`0x00`): `drop_in_place` function pointer (`R_RISCV_64`
  relocation).
- Offset `8` (`0x08`): concrete payload `size` in bytes (`u64`).
- Offset `16` (`0x10`): concrete payload `align` in bytes (`u64`).
- Offset `24 + 8 * idx` (`(3 + idx) * 8`): `method_idx` function pointer
  (`R_RISCV_64` relocation), invoked dynamically via
  `ld t1, (24 + 8*idx)(vtable_reg); jalr ra, 0(t1)` with `a0 = data_ptr`.

#### Freestanding Linux `riscv64` `ecall` Syscall Table, Bump/Mmap Allocator, and `tp` (`x4`) TLS

Freestanding `riscv64` Linux binaries invoke kernel services directly via
`ecall` (`0x00000073`) with the generic UAPI syscall number
(`include/uapi/asm-generic/unistd.h`) in `a7` (`x17`), up to six arguments in
`a0`–`a5` (`x10`–`x15`), and the signed return value (or `-errno` in
`[-4095, -1]`) in `a0` (`x10`):

| Syscall Name | Linux `riscv64` Number (`a7`) | Register Arguments (`a0`..`a5`) | Role in Freestanding Runtime & `probe_rv64gc.elf` |
| :--- | :--- | :--- | :--- |
| `SYS_read` | `63` (`0x3f`) | `a0 = fd`, `a1 = buf`, `a2 = count` | Standard input and file descriptor reads |
| `SYS_write` | `64` (`0x40`) | `a0 = fd`, `a1 = buf`, `a2 = count` | Writes 56-byte verification banner to `stdout` (`fd = 1`) |
| `SYS_exit` | `93` (`0x5d`) | `a0 = status` | Thread termination with exit code `0` |
| `SYS_exit_group` | `94` (`0x5e`) | `a0 = status` | Process-wide termination |
| `SYS_brk` | `214` (`0xd6`) | `a0 = brk_addr` | Contiguous heap segment expansion |
| `SYS_mmap` | `222` (`0xde`) | `a0 = addr (0)`, `a1 = len`, `a2 = prot (3)`, `a3 = flags (0x22)`, `a4 = fd (-1)`, `a5 = off (0)` | Anonymous page allocation (`PROT_READ\|PROT_WRITE`, `MAP_PRIVATE\|MAP_ANONYMOUS`) |
| `SYS_getrandom` | `278` (`0x116`) | `a0 = buf`, `a1 = buflen`, `a2 = flags (0)` | Kernel CSPRNG entropy for `HashMap` seed initialization |

Sequential allocations from a bump cursor over a mapped region `[base, limit)`
satisfy spatial disjointness `p1 + sz1 <= p2` (`bumpAlloc_disjoint` in
[`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean)),
and thread-local state is addressed relative to the hardware thread pointer `tp`
(`x4`) (or local-exec `.tdata` relocations `R_RISCV_TPREL_HI20 = 29`,
`R_RISCV_TPREL_ADD = 32`, `R_RISCV_TPREL_LO12_I = 30`, and
`R_RISCV_TPREL_LO12_S = 31`).

## Boundaries

- **`not examined`**:
  - Linker relaxation (`R_RISCV_RELAX = 51`), which shrinks `auipc` +
    `addi`/`jalr` pairs when targets fall within `gp`-relative or `J`-type range
    at link time; the verified object emitter omits `R_RISCV_RELAX` so
    instruction byte offsets proven before linking remain invariant through
    linking.
  - Dynamic shared-object (`ET_DYN`) Global Offset Table (`R_RISCV_GOT_HI20 =
    20`) and TLS GD/IE models; our proofs and binary probes target static
    relocatable objects (`ET_REL`) linked into static executables (`ET_EXEC`).
  - Privileged RISC-V CSRs (`mstatus`, `satp`, `mtvec`) and kernel-mode trap
    handling (`mret`/`sret`), which lie below the Linux user-space `ecall` ABI
    boundary.
- **`known not to apply`**:
  - Direct 12-bit immediate encoding (`addi`, `ld`, `sd`) cannot represent frame
    sizes or slot offsets outside `[-2048, +2047]` bytes
    (`control_large_frame_2720_direct_imm12_sign_flips`).
  - Uncompensated upper/lower splitting (`hi20 = imm >> 12`, `lo12 = imm &
    0xfff`) fails by `-4,096` whenever bit 11 of `imm` is `1`
    (`control_naive_uncompensated_split_fails_when_bit11_set`).
  - Single-pass branch relaxation is unsound when inner branch expansion pushes
    an enclosing near-boundary branch past `4,094` bytes
    (`cascading_relaxation_single_pass_fails_and_fixpoint_succeeds`).
  - Setting `r_sym` of `R_RISCV_PCREL_LO12_I` (`24`) or `R_RISCV_PCREL_LO12_S`
    (`25`) directly to the target `.rodata`/`.data` symbol instead of the local
    `.Lpcrel_hi*` label on the paired `auipc` is rejected by `rust-lld` and is
    mathematically off by $P_{\text{lo}} - P_{\text{auipc}}$
    (`control_pcrel_lo12_direct_pc_off_by_four`, Negative Probe B).

## Evidence

| Artifact | Path | Size (Bytes) | SHA-256 | Role |
| :--- | :--- | :--- | :--- | :--- |
| Lean 4.34.1 Proof Probe | [`support/rv64_encoding_and_imm_proofs.lean`](support/rv64_encoding_and_imm_proofs.lean) | `28,204` | `5e6951772faf79c18c384d261550e8945226bcf7b094b4ee8ac775ae7bb37442` | `prelude`-only machine-checked proofs of instruction encoding round-trips, `.fence` bitfields, `lui`+`addi` sign-extension compensation, cascading branch relaxation, `.symtab` ordering, indirect `PCREL_LO12` addressing, `LP64D` classification, vtable offsets, and `bumpAlloc` disjointness |
| ELF64 Generator & Linker/QEMU Harness | [`support/gen_and_verify_rv64_elf.py`](support/gen_and_verify_rv64_elf.py) | `37,018` | `a238f78d9bc0995fdeb2ff0024eab6794cb6f0f56ccdea00cf7b72c8b329fb92` | Self-contained Python 3 generator for Negative Probes A & B and `probe_rv64gc.o`, invoking `rust-lld`, `llvm-readelf`, `llvm-objdump`, and `qemu-riscv64` |
| Generated `RV64GC` Relocatable Object | [`support/probe_rv64gc.o`](support/probe_rv64gc.o) | `6,144` | `c45f22f0de47bd13157603e4f0f72f06a727de7e229ae977875b56dfc692e119` | Standards-compliant `ET_REL` object (`EM_RISCV = 243`, `e_flags = 0x5`) with 2,720-byte frame, 4,128-byte relaxed branch, `.rodata`/`.data.rel.ro` relocations, 3-word vtable, and Linux syscalls |
| Linked `RV64GC` Static Executable | [`support/probe_rv64gc.elf`](support/probe_rv64gc.elf) | `6,304` | `5f588cb59db32198aafca550df6290a861238011ddce44a6df85de8dbec47377` | Static ELF64 executable produced by `rust-lld -flavor gnu -m elf64lriscv -static -e _start` |
| Structured Probe Ledger | [`support/probe_ledger.json`](support/probe_ledger.json) | `1,340` | `f5c09092ca69508507abfa4c63b43f1c6701533964f588ed9d387a04aae3e600` | Hashes, sizes, exit codes, and `rust-lld` / `qemu-riscv64` outputs for Negative Probes A & B and `probe_rv64gc.elf` |
| Recorded Disassembly & Execution Dump | [`support/verification_output.txt`](support/verification_output.txt) | `17,898` | `6a7b0fc894105c3cc8b1a31e5d5be0da314587aa8ca50a4444f3007834affb66` | Complete `rust-lld` negative diagnostic stderr, `llvm-readelf -h -S -s -r`, pre-link and post-link `llvm-objdump -d`, and `qemu-riscv64` stdout |

## Revalidation

Run the following commands from this report directory to re-verify all Lean 4
theorems and regenerate, relink, inspect, and execute the `RV64GC` ELF64 object
and executable probes:

```bash
# 1. Machine-check all encoding, immediate-compensation, branch-relaxation, and ABI theorems in Lean 4.34.1:
lean -j1 -M768 support/rv64_encoding_and_imm_proofs.lean

# 2. Regenerate Negative Probes A & B, support/probe_rv64gc.o, and support/probe_rv64gc.elf,
#    verify rust-lld relocations and llvm-readelf/llvm-objdump outputs, and execute under qemu-riscv64:
python3 support/gen_and_verify_rv64_elf.py

# 3. Verify SHA-256 digests of all support artifacts:
sha256sum \
  support/rv64_encoding_and_imm_proofs.lean \
  support/gen_and_verify_rv64_elf.py \
  support/probe_rv64gc.o \
  support/probe_rv64gc.elf \
  support/probe_ledger.json \
  support/verification_output.txt
```
