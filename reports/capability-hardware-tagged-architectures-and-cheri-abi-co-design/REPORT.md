# Capability Hardware and Tagged Architectures: Descriptor Machines, Symbolics Ivory, CHERI ISAv9, Morello, CheriABI, Cornucopia Reloaded, CHERIoT, Mill SASOS, and CHERI-DMA

## Summary

- **Core mechanism.** A CHERI capability is a pointer twice the address width (128 bits for a 64-bit address) plus one out-of-band *tag* bit per capability-sized, capability-aligned granule of memory and per register. The instruction set enforces *provenance validity* (a tag arises only by derivation from a tagged capability, never from data), *integrity* (any non-capability store into a granule atomically clears its tag), and *monotonicity* (bounds and permissions only shrink). In CHERI ISAv9's CHERI-RISC-V a non-monotonic request does not trap; it yields a result with the tag cleared.
- **Compression made the pointer affordable and leaks into the ABI.** CHERI Concentrate stores base and top in 27 bits, floating-point style, relative to the address. In the 128-bit format bounds are byte-exact below 4 KiB; larger objects need base and length aligned to `2^(E+3)` bytes (8 bytes at 4 KiB, 2 KiB for 1 MiB, 2 MiB for 1 GiB). The address may roam at least 1/8 of the representable space below base and 1/4 above top; further out the tag is cleared.
- **"Capabilities are inherently slow" is a historical artifact — the architectural performance law.** Comparing Burroughs B5000/MCP (48-bit flag-bit descriptors), Symbolics 3600/Ivory (40-bit VLSI tagged Lisp CPU: 8-bit tag = 6-bit type + 2-bit CDR code, 32-bit payload, parallel tag/GC checks), CHERI/Morello, and Mill PLB/WKR against Intel iAPX 432 (Colwell et al., 1988) shows hardware enforcement costs `<5%` when checks run *in parallel* with L1/register pipelines, versus `2–10×` slowdowns under *serial uncached multi-level descriptor indirection*, bit-unaligned decode, and microcoded calls (the 432's 982-cycle call; its postmortem concludes performance was "dominated, in large part, by artifacts and not by concepts"). What stays irreducible is metadata storage: wider pointers cost cache/bandwidth, and tags need atomic storage beside data.
- **The pure-capability ABI rewrites C's integer/pointer contract.** `uintptr_t` becomes capability-carrying and stops being the size of `size_t`; `ptraddr_t` holds bare addresses; an integer cast to a pointer is untagged; arithmetic on two `uintptr_t` values must pick one provenance source; `memcpy` must move aligned capability words to keep tags while byte loops strip them; sub-object bounds break `container_of` and are opt-in; the kernel takes and returns capabilities.
- **Language provenance models and hardware capabilities diverge at three edges:** integer-to-pointer casts (angelic "exposed" provenance has no hardware counterpart), byte-wise pointer copies (per-byte provenance versus one tag per granule), and optimization (compilers may remove but not introduce tag-clearing excursions, so tag clearing is not a source-level guarantee).
- **Bounds do not give temporal safety.** CHERI heaps add quarantine, a revocation bitmap, and sweeping. Cornucopia tracks capability *stores* and needs a stop-the-world re-scan; Cornucopia Reloaded uses a per-page capability *load* barrier so the world stops only to scan registers; CHERIoT checks a per-8-byte revocation bit on every capability load, without an MMU.
- **Sealed capabilities realize hardware existential types.** `CSeal`/`CUnseal` over unforgeable `otype`s (and CHERIoT RTOS's two-level software sealing extending 7 non-executable hardware `otype`s to `2^32 - 2^24` `TokenKey`s) enforce $\exists \alpha.\, \mathrm{Cap}(\alpha) \times (\mathrm{Cap}(\alpha) \to \dots)$ in hardware for zero-trust opaque cross-language FFI handles.
- **Mill SASOS protection domains are the Single-Address-Space counterpart to CHERI fat pointers.** Mill (U.S. Patents 9,747,218; 10,678,700; 9,524,163; 9,652,230) decouples protection (`iPLB`/`dPLB` + `WKR` registers parallel to virtual L1) from translation (`TLB` after LLC misses), switching `Turfs` via ~4–5 cycle `Portal` calls with per-turf stacklets and zero TLB flushes. Call-scoped transient `PASS`/`GRANT` grants — auto-revoked on non-speculative `RETURN` with a confused-deputy guard bit — map isomorphically to lifetime-scoped borrows (`&'call [u8]`).
- **Peripheral DMA requires capability-bounded isolation beyond page-granular IOMMUs.** *Thunderclap* (NDSS '19) exposed IOMMU 4 KiB sub-page aliasing, async IOTLB reuse windows, 600% worst-case 6-level IOTLB-miss overheads, and PCIe ATS bypasses; CHERI-DMA (HASP '20) adds tag-clearing on DMA writes, byte-granular `CSU`/`CLUT` (100% worst-case single-level lookup, atomic updates), and capability-bounded descriptor rings.
- **MTE, pointer authentication, shadow stacks, and protection keys** each cover a slice probabilistically or coarsely; none gives unforgeable per-pointer bounds.
- **Not established here:** internals of Plessey System 250 and IBM System/38, published CHERIoT/Morello performance figures, measured Mill silicon (unshipped), full PDFs of Baker et al. (1987) / Lonergan & King (1961) / U.S. Patent 9,747,218 B2, and any ratified successor to ISAv9.

## Applicability

The findings describe the architecture-neutral CHERI model and its CHERI-RISC-V instantiation as specified by **CHERI ISAv9** (UCAM-CL-TR-987, read from its LaTeX source at tag `release-9.0`) and as executed by the **CHERI-RISC-V Sail model** at the pinned revision. The Sail revision is three years newer than the report; the properties used (field widths, tag clearing on non-monotonic manipulation, set-bounds and decode algorithms) agree between the two where both were read. Nothing is claimed about a ratified RISC-V CHERI extension.

How the subjects relate:

- *History and tagged lineage*: Levy (landing page, Ch. 1–2), Colwell–Gehringer–Jensen (iAPX 432), Moon (IEEE Computer 1987), U.S. Patent 4,887,235 (3600), and Withington et al. (1994, 40-bit Ivory emulation); ISAv9 gives the CHERI authors' historical reading.
- *Mechanism*: ISAv9, the CHERI Concentrate paper, the two Sail models, and the `cheri-compressed-cap` test vectors. The support probe transcribes the Sail functions and is cross-checked against those vectors.
- *Silicon*: Arm Morello, only through the IEEE Micro platform paper. Morello uses a CHERI Concentrate variant "with different precision constants and a slightly different encoding format" (ISAv9), so every numeric rule below is for CHERI-RISC-V.
- *ABI and language*: the CheriABI paper (CHERI-MIPS FPGA measurements, 2019), CheriBSD (current tree), the living CHERI C/C++ Programming Guide, and the CHERI C formal-semantics paper. Rust and MiniRust appear only as provenance models; no Rust CHERI target was examined.
- *Temporal safety, embedded, and existential sealing*: the Cornucopia papers, CheriBSD's revocation interface, and CHERIoT Sail (`cheri_cap_common.sail`, `cheri_insts.sail`, `cheri_mem.sail`), archdoc, and RTOS (`switcher/entry.S`, `token.h`, `token_unseal.S`). CHERIoT is a distinct ISA; its statements never transfer to CHERI-RISC-V or Morello.
- *Mill SASOS and DMA*: Mill U.S. Patents `10,678,700 B2`, `9,524,163 B2`, `9,652,230 B2` (full text), official summaries (incl. `9,747,218 B2`), and Mill Programming Model (unshipped silicon — architectural claims only); Markettos et al. (NDSS '19 *Thunderclap* empirical FPGA study; HASP '20 analytical CHERI-DMA design space).
- *Alternatives*: Linux kernel documentation, for architectural parameters only.

Adjacent packages, not duplicated here: `anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey` (Sail-CHERI and Cerberus-CHERI as verification artifacts), `rust-allocation-provenance-and-stack-lifetime-semantics` (Rust provenance tables), `verified-cfi-cet-bti-pac-cfguard-and-speculative-hardening` (CET, BTI, PAC code generation), `modern-sfi-lfi-and-ring0-wasm-kernels-2020-2026` (software fault isolation). The support probe is an executable model: it establishes properties of the transcribed algorithms and abstract state machines, not of a processor or of the Sail emulator.

## Findings

### 1. Lineage, and why early capability hardware stalled

#### 1.1 Chronology

Levy defines a capability as "a token, ticket, or key that gives the possessor permission to access an entity or object", an object identifier plus access rights, with the integrity rule every design must enforce: "the system must prohibit a program from directly modifying the bits in a capability". His capability operations already include the monotone one: "Restrict the rights in a capability, producing a less-privileged version". From his Table 1-1 (selected rows):

| Year | System | Levy's characterization |
|---|---|---|
| 1961 | Burroughs B5000 | stack machine with descriptor addressing |
| 1967 | Multicomputer / Magic Number Machine (University of Chicago) | first capability hardware system design |
| 1969 | Plessey System 250 | first industrial capability hardware and software system |
| 1970 | Cambridge CAP Computer | capability hardware with microcode support |
| 1978 | IBM System/38 | first major commercial capability system, tagged capabilities |
| 1981 | Intel iAPX 432 | highly-integrated object-based microprocessor system |

On the B5000 a program's addressing environment is its Program Reference Table of up to 1024 48-bit words; "a tag field in each word in the table indicates whether the entry is a descriptor or a scalar data element", and "all memory references, including procedure calls, are made through Program Reference Table descriptors".

Basis: documentation (Levy, Chapters 1 and 2; row pairing reconstructed from column-scrambled text extraction and cross-checked against Chapter 2's "Introduced in 1961, the Burroughs B5000").

#### 1.2 Two ways to keep capabilities unforgeable

| Family | Where "this is a capability" is recorded | Examples named by ISAv9 | Cost profile |
|---|---|---|---|
| Tagged memory | with the bits: tag bit(s) per granule | Burroughs large systems (per-word tag; three-bit tag from the B6500); IBM System/38 ("four bits per capability-sized piece of memory", all required set); CHERI (one bit) | capabilities interleave with data; tags must be stored through caches and memory |
| Segmented | with the access path: a segment holds only capabilities or only data | Cambridge CAP ("C-type"/"D-type"); Hydra | no tags; data structures must be split |
| Indirect | capabilities stay in a protected table; programs hold indices | CAP capability index + offset; Coyotos capability pages | drop-in with MMU-style translation; every use is a lookup |

ISAv9 words the B5000 tag as a per-word bit "distinguishing its intended use as either data or instructions"; Levy as descriptor versus scalar. Both are kept; Burroughs manuals were not consulted.

Basis: documentation (ISAv9 `chap-historical.tex`; Levy Chapter 2).

#### 1.3 The iAPX 432 postmortem

Colwell, Gehringer, and Jensen measured and simulated the 432 to separate architecture from accident.

- *Addressing.* A reference goes from an access-descriptor selector through an Object Table Directory and an Object Table in physical memory ("two-level addressing"); every reference is checked for rights and object bounds. Mitigation was two small caches: "The data-segment cache is only five entries deep, and is flushed upon procedure calls, returns, and enters"; "the object-table cache is only four entries deep".
- *Calls.* "A typical procedure call requires 16 read accesses to memory and 24 write accesses, and it consumes 982 machine cycles", about ten times an MC68010 or VAX 11/780 call, with object orientation "only a minor factor".
- *Raw speed.* The 4 MHz system ran four low-level benchmarks 10 to 26 times slower than a VAX 11/780.
- *Attribution.* 25–35 percent of potential throughput lost to Ada compiler code quality (which also used protected calls exclusively and copy-in/copy-out parameters); 5–10 percent to missing instruction-stream literals and bit-aligned instructions; a further 35–45 percent recoverable by "incrementally better technology" (wider buses, local data registers).
- *Residual.* The corrected design ran "from one to four times slower than conventional processors", "the inherent cost of the 432's style of object orientation", with the caution "that other approaches to object-based architecture are possible". The paper closes hoping interest "can be rejuvenated by our demonstration that the 432's performance has been dominated, in large part, by artifacts and not by concepts."

Basis: documentation (primary measurement paper).

#### 1.4 Contingent versus irreducible

That capability checks must be slow is **contingent**. The classification is derived from three warrants: (a) the postmortem assigns most of the gap to compiler and implementation choices; (b) CHERI is a contrasting precedent without the costly structure — no object table, the capability *is* the pointer, and on Morello the checks "run in parallel to the normal memory-management function of the TLB and have similar timing"; (c) Levy records a commercial tagged capability machine three years before the 432.

Three costs are **irreducible** in kind, not magnitude: (i) per-pointer bounds occupy storage, so pointers widen (cache, bandwidth) or bounds lose precision (alignment) — compression picks a point on that curve; (ii) tags must be bound atomically to data, which changes caches, buses, and DRAM; (iii) revocation is paid either on every dereference (indirection) or at revocation time (direct pointers plus sweeping). CHERI chose the latter (Section 7).

Basis: derived (from 1.3, 4, and 7 as stated).

#### 1.5 Parallel-pipeline tagged hardware (Burroughs B5000/MCP, Symbolics Ivory) and the architectural performance law

Comparing **Burroughs B5000/MCP** and **Symbolics 3600 / Ivory** against **Intel iAPX 432** codifies a quantitative architectural law:

- **Burroughs B5000/MCP (1961; B6500, 1969).** Co-designed under Robert S. Barton with zero assembly language (MCP written in Extended ALGOL/ESPOL), using 48-bit words (+1 parity bit) where bit 0 flagged descriptors vs. data (expanded to a 3-bit hardware tag on 51-bit B6500 words). Array and call references resolved through Program Reference Table (PRT) descriptors carrying base, length, and presence bits with hardware bounds checks on indexed fetch.
- **Symbolics 3600 (1983–1987) and Ivory (1987).** Moon (IEEE Computer, 1987) and U.S. Patent 4,887,235 document the 3600's 36-bit tagged word (4-bit tag: 2-bit CDR code + 2/6-bit type; +7-bit ECC, 10% DRAM cost) on a 4-stage pipeline with a 1K-word stack buffer: *"Hardware can process the tag in parallel with other hardware that processes the rest of a word... Minimizing the cycle count demands that these checks be performed in parallel, not each in a separate cycle."* `Add` runs fixed-point ALU, FPU, and tag check concurrently in 1 cycle (trapping to microcode only for non-fixnums); stores check ephemeral-GC tables in parallel with writes. **Symbolics Ivory** (1987; single-chip ~390k-transistor 2-micron CMOS, 4-stage Fetch/Decode/Execute/Write-Back pipeline; Baker et al., ICCD 1987; emulated by Withington et al., 1994) widened words to **40 bits**: **8-bit tag** (**6-bit data type + 2-bit CDR code** compacting cons lists) + **32-bit full address/data payload** (48 bits with 8-bit ECC), keeping parallel Execute-stage tag checks, CDR traversal, and ephemeral-GC read/write barriers.

| Architecture | Metadata locus & width | Fast-path timing | Dereference indirection | Overhead |
|---|---|---|---|---|
| Burroughs B5000 / B6500 | 1-bit flag / 48-bit (3-bit tag / 51-bit B6500); PRT | Parallel bounds/presence check | 1-level PRT lookup | Mainframe baseline |
| Symbolics 3600 / Ivory | 4-bit / 36-bit (3600); **8-bit (6-bit type + 2-bit CDR) + 32-bit = 40-bit** (Ivory) | **Parallel** Execute tag + GC barrier alongside ALU/store | None (microcode only on slow types) | 1-cycle fixnum; 10% DRAM (3600), ~20% width (Ivory) |
| Intel iAPX 432 | Access Descriptors + Object Table Dir + Object Table | **Serial** 2-level walk behind call-flushed 5-/4-entry caches; bit-unaligned decode | 2-level uncached walk + 982-cycle microcoded call | **10–26×** raw vs. VAX; **1–4×** residual (Colwell 1988; **2–10×** typical) |
| CHERI / Morello | 1-bit tag / 16 B + inline 27-bit compressed bounds | **Parallel** to TLB/ALU | None | **0–5%** typical cycle overhead (Section 4) |
| Mill PLB/WKR | `WKR` regs + split `iPLB`/`dPLB` over virtual addrs | **Parallel** to virtual L1 (TLB after LLC) | None on hit; 2 cache lines on Portal | ~4–5 cycle architectural Portal; unshipped silicon (Section 10) |

**Architectural performance law (derived).** Hardware safety incurs `<5%` execution overhead **iff** checks run *in parallel* with L1/register/ALU pipelines over in-register or word-adjacent metadata (Ivory, CHERI, Mill), adding zero serial memory indirections; it degrades to `2–10×` slowdowns under *serial uncached multi-level descriptor walks*, bit-unaligned decoding, or heavy microcode (iAPX 432; uncached 6-level IOMMUs in Section 11). Language-specific word tags (`Ivory` Lisp tags/CDR codes) clash with C byte punning, whereas minimal orthogonal primitives (provenance, bounds, sealing, region permissions) compose across languages.

Basis: documentation (Moon 1987; U.S. Patent 4,887,235; Withington et al. 1994; Colwell et al. 1988; Levy Ch. 2; Morello 2023; Mill `US10678700B2`) + derived (performance law; Baker et al. 1987 and Lonergan & King 1961 bibliographic only — Boundaries).

### 2. The CHERI ISAv9 capability model

#### 2.1 Fields and formats

| Property | CC-128 (CHERI-RISC-V RV64) | CC-64 (CHERI-RISC-V RV32) | CHERIoT |
|---|---|---|---|
| Size / address / tag granule | 16 B / 64 bit / 16 B | 8 B / 32 bit / 8 B | 8 B / 32 bit / 8 B |
| Permissions | 12 hardware + 4 software | 12 hardware | 6-bit compressed field, 12 architectural |
| Object type | 18 bits, 4 values reserved | 4 bits | 3-bit field |
| Bounds bits | 27 = `I_E` 1 + `T` 12 + `B` 14 | 15 = 1 + 6 + 8 | 22 = `E` 4 + `T` 9 + `B` 9 |
| Mantissa width `MW` | 14 | 8 | 9 |
| Byte-exact lengths | below 4096 | below 64 | up to 511 |
| Alignment above that | `2^(E+3)` | `2^(E+3)` | `2^e` |
| Out-of-bounds slack, `s = 2^(E+MW)` | at least `s/8` below base, `s/4` above top | same rule | none below base; up to `base + 2^(e+9)` |

CC-128 layout in the Sail model: `perms[127:112] reserved[111:110] flags[109] otype[108:91] I_E[90] T[89:78] B[77:64] address[63:0]`. Hardware permissions: Global, Permit_Execute, Permit_Load, Permit_Store, Permit_Load_Capability, Permit_Store_Capability, Permit_Store_Local_Capability, Permit_Seal, Permit_CInvoke, Permit_Unseal, Access_System_Registers, Permit_Set_CID. Object type −1 is unsealed, −2 the sealed-entry ("sentry") type. Two representation rules that C relies on: NULL "has an all zeroes in-memory representation, with cleared tag" (the Sail model XORs stored capabilities with the NULL encoding), and "the bottom XLEN bits of a capability hold its address value".

Basis: normative (ISAv9 `chap-architecture.tex`) + source (`src/cheri_prelude_128.sail`, `cheri_prelude_64.sail`, `cheri_cap_common.sail` in sail-cheri-riscv; `src/cheri_cap_common.sail`, `archdoc/chap-cheri-riscv.tex` in cheriot-sail).

#### 2.2 Tagged memory

ISAv9: "CHERI relies on tagged physical memory: the association of a 1-bit tag with each capability-sized, capability-aligned location in physical memory." A permitted capability store writes tag and value atomically; "other stores of untagged capability values or other types (e.g., bytes, half words, words, floats, doubles, and double words) across one or more capability-aligned locations in memory will atomically clear the corresponding tag bits"; "it is not possible to partially overwrite a capability value in memory while retaining the tag". Tags attach to physical memory so aliased mappings agree. In the Sail models every data write supplies `default_meta` (`false`) and `__WriteRAM_Meta` clears the tag of the first granule touched and, when the write straddles, the next. Capability loads and stores at non-capability alignment raise an alignment exception.

Basis: normative + source (`model/riscv_mem.sail` in sail-riscv; `src/cheri_mem_metadata.sail`, `cheri_mem.sail`) + execution (probe group "tagged memory").

#### 2.3 Monotonicity by guarded manipulation

ISAv9 names four mechanisms: *limited expressivity* (permissions change only by AND), *stripping the tag in register write-back*, *exceptions* (generally avoided), and *stripping the tag in memory store*. Version 9 made CHERI-RISC-V clear "tags rather than raising exceptions for non-monotonic modifications to capabilities". Rationale: trapping instructions cannot be hoisted or reordered (a miscompilation hazard observed in the FreeBSD kernel), code handling untrusted capabilities would otherwise branch around each operation, and fewer trapping instructions simplify the pipeline; the cost is later, harder-to-debug failures.

| Instruction (result `cd`, operands `cs1`, `cs2`, `rs2`) | Effect | Result tag cleared when |
|---|---|---|
| `CSetBounds` | base := `cs1.address`, length := `rs2`, rounded outward | `cs1` sealed, or the *requested* range is outside `cs1`'s bounds |
| `CSetBoundsExact` | same | also when rounding was needed |
| `CAndPerm` | perms := perms AND `rs2` | `cs1` sealed |
| `CIncOffset`, `CSetAddr` | new address | `cs1` sealed, or address not representable |
| `CSeal` | otype := `cs2.address` | `cs1` sealed; `cs2` untagged, sealed, lacking Permit_Seal, cursor out of its bounds or above the maximum otype |
| `CUnseal` | unseal; Global := `cs1.Global AND cs2.Global` | `cs1` unsealed or reserved otype; `cs2` untagged, sealed, lacking Permit_Unseal, `cs2.address != cs1.otype`, or out of bounds |
| `CSealEntry` | otype := sentry | `cs1` sealed |
| `CBuildCap` | re-tag the untagged bits of `cs2` under authority `cs1` | bits not a subset of `cs1` in bounds and permissions, not a derivable encoding, or `cs1` untagged or sealed |

*Dereference* still traps (tag, seal, permission, or length violation). Two flow rules sit on the memory path: a capability loaded through an authority lacking Permit_Load_Capability arrives untagged, and storing a tagged non-Global capability requires Permit_Store_Local_Capability.

`CSetBounds` checks the requested range but installs the rounded one, so monotonicity rests on an encoding property: rounding a sub-range of a representable range never escapes it. The probe checks this exhaustively on a toy instance (7-bit address, 6-bit mantissa; 138,509 parent/child pairs) and on 42,050 random derivation steps in the real formats, with no violation.

The sanctioned non-monotonic transitions are exception delivery and sealed-capability invocation: `CInvoke` unseals a code/data pair with matching object types and jumps; a jump through a sentry atomically unseals it into the program counter. ISAv9 credits the M-Machine's "enter capabilities" for sentries. How the Sail and Cerberus CHERI models serve as verification artifacts is covered in `anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey`.

Basis: normative (ISAv9 `chap-model.tex`, `chap-rationale.tex`, `chap-architecture.tex`) + source (`src/cheri_insts.sail`) + execution (probe groups "random derivation chains", "sealing", "CBuildCap", "tag conservation").

### 3. CHERI Concentrate bounds compression

#### 3.1 Encoding and decoding (128-bit format)

```text
Set bounds for base b, 65-bit top t, length l = t - b:
  E   = 52 - CountLeadingZeros(l[64:13])
  I_E = 0 if (E == 0 and l[12] == 0) else 1
  I_E = 0:  B = b[13:0]        T = t[11:0]              (exact)
  I_E = 1:  B = b[E+13:E+3]    T = t[E+11:E+3]          (low 3 bits of each hold E)
            if t[E+2:0] != 0: T += 1                    (round top up)
            if the length MSB moved: E += 1, re-extract B and T
Decode at address a:
  T[13:12] = B[13:12] + L_carry + L_msb     L_msb = I_E;  L_carry = (T[11:0] < B[11:0])
  R   = B[13:11] - 1                        (3-bit edge of the representable space)
  c_t = (T[13:11] < R) - (a[E+13:E+11] < R)             c_b likewise with B
  top = (a[63:E+14] + c_t) : T : zeros(E)   base = (a[63:E+14] + c_b) : B : zeros(E)
  if E < 51 and (top[64:63] - base[63]) > 1: flip top[64]
```

The top is 65 bits so one capability can cover the address space (`E = 52`, `T = 2^12`, `B = 0`, the reset and NULL encoding).

Basis: normative (ISAv9 "CHERI Concentrate Compression") + source (`setCapBounds`, `getCapBoundsBits`, `encCapabilityToCapability` in `src/cheri_cap_common.sail`).

#### 3.2 Alignment rule and allocator cost

ISAv9: `I_E = 0` allocations have no alignment requirement; "for larger allocations the base and length must be aligned to `2^(E+3)` byte boundaries"; "there is a jump in required alignment from 1-byte to 8-bytes at the transition". Granule required per request length, asserted by the probe:

| Requested length | CC-128 | CC-64 | CHERIoT |
|---|---|---|---|
| 63 B | 1 | 1 | 1 |
| 511 B | 1 | 64 | 1 |
| 4095 B | 1 | 512 | 16 |
| 4 KiB | 8 | 512 | 16 |
| 1 MiB | 2 KiB | 128 KiB | 4 KiB |
| 1 GiB | 2 MiB | 128 MiB | 16 MiB (saturated exponent) |

One byte added to a 1 MiB request pads it by 2 KiB (CC-128), 128 KiB (CC-64), or 4 KiB (CHERIoT). Relative alignment is at most 1/512 of the length in CC-128, 1/8 in the ISAv9 64-bit format, and about 1/256 in CHERIoT up to 8 MiB. Consequences: an allocator rounds the size with `CRRL` and aligns the base with the `CRAM` mask so `CSetBoundsExact` succeeds (every `CRAM`-aligned base with a `CRRL` length is exact on the toy format, 2,334 cases); and narrowing a pointer to a large unaligned sub-range silently yields wider bounds than requested, which ISAv9 flags ("care must be taken to ensure that this cannot lead to buffer overflows").

Basis: normative + execution (probe groups "alignment rule", "alignment table") + derived (the fractions follow from the length MSB sitting at bit `E+12`, `E+6`, or about `e+8`).

#### 3.3 Representable region and the fast check

The decoder derives a boundary `R = B[13:11] - 1` that places a window of size `s = 2^(E+14)` around the object; ISAv9 guarantees "at least 1/8 s bytes below the base and 1/4 s above top where `a` can roam out-of-bounds while still allowing us to recover the bounds". Outside it the tag is cleared. `CIncOffset` uses a check on the increment `i` and stored fields only:

```text
inRange = bits i[63:E+14] all equal                    (-s < i < s)
inLimit = i >= 0 ? I_mid <  (R - A_mid - 1)
                 : I_mid >= (R - A_mid) and R != A_mid       I_mid = i[E+13:E], A_mid = a[E+13:E]
representable = (inRange and inLimit) or E >= 50
```

It is deliberately conservative. The probe confirms both directions: it never accepted a move that the exact check (decoded bounds unchanged) rejected, across 60,000 stressed samples in three formats, and it rejected a few exactly representable moves (9 of 11,505 in CC-128; 498 of 11,263 in CC-64). All 107,957 probes at `base - s/8` and `top + s/4 - 1` were representable, and every address in `[base, top]` kept its bounds in the exhaustive toy run, which makes one-past-the-end pointers safe. The CHERI Concentrate paper reports a HOL4 proof of "the decode and pointer-modify operations" and "a 50% to 75% reduction in L2 misses" against the uncompressed 256-bit format; neither was reproduced.

Basis: normative (ISAv9 "Fast Representable Limit Checking") + source (`fastRepCheck`, `setCapAddr`) + execution (probe group "fast representability check") + documentation (paper abstract).

### 4. Morello: what the silicon prototype established

Morello adds CHERI to a Neoverse-N1-derived out-of-order core whose parameters "remained the same" (4-way decode, 128-entry reorder buffer, three cache levels), running "at 2.5GHz in the SoC which was fabricated on a TSMC N7 process".

- *Where the cost is.* "The main cost of using the CHERI technology this way comes from the larger cache and memory footprint of 128-bit capabilities, which various benchmarks have shown to be in the range of 0-5%, though on some very pointer heavy workloads, it can be more than that." Registers are 129 bits; caches and buses carry a tag per 128 bits.
- *Prototype artifacts.* Indirect branches must predict a capability program counter; "the Morello implementation stalls in some circumstances until the new bounds are known", worked around in the compiler. Spectre-class attacks were not addressed.
- *Features driven by software.* Faulting on a store of a *tagged* value where capability stores are not permitted depends on the tag of the data, "a micro-architecturally novel concept that added complexity and performance cost", included because temporal-safety sweeping relies on it.
- *Tag storage.* Two schemes built for comparison: "a <1% area of the DRAM" plus a tag cache, or the bits normally used for ECC.
- *Assurance.* The specification ("62K lines") was translated via Sail and "reachable capability monotonicity, i.e. that the available capabilities cannot be increased during normal execution of arbitrary code" proved in Isabelle for the full sequential architecture; "three security issues were found before tapeout".

Basis: documentation (IEEE Micro platform paper).

### 5. CheriABI and language/FFI co-design

#### 5.1 Language models and ABIs

ISAv9 distinguishes pure-integer, hybrid (`__capability`-annotated pointers), and pure-capability C, and native, hybrid, and pure-capability ABIs; in the last, "capabilities are used for all language-level pointers, but also underlying addresses in the run-time environment, such as return addresses. The goal of this ABI is strong protection at significant cost to binary interoperability." CheriABI is the POSIX process ABI of that kind: "all pointers are capabilities, and all kernel manipulations of process memory are via explicitly delegated capabilities". Its governing notion is the *abstract capability*, the access a program should have at a point in execution, built "only by legitimate provenance chains of operations" even where the architectural chain is broken and re-derived (context switch, swap, signals). Its design rule is the *principle of intentional use*: "an invoked privilege should be selected explicitly rather than implicitly".

Basis: normative (ISAv9 "C and C++ Language and Code Generation Models") + documentation (CheriABI paper).

#### 5.2 What changes for C types

| C entity | Pure-capability CHERI C |
|---|---|
| `T *` | capability: twice the address width, capability-aligned, tagged |
| `uintptr_t`, `intptr_t` | capability-carrying; "no longer the same size as `size_t`"; integer range still that of an address |
| `ptraddr_t` | new address-sized integer; "should not be directly cast to a pointer type for dereference" (`vaddr_t` in the 2020 edition) |
| `size_t`, `ptrdiff_t`, `long` | plain integers; a cast to a pointer gives "a `NULL`-derived capability with the address set to the integer value", untagged (`-Wcheri-capability-misuse`) |
| `intmax_t` | "not provenance-carrying"; stays 64-bit |
| `max_align_t` | includes capability alignment; allocators aligning to `sizeof(long double)` must change |
| under-aligned pointer storage (`__packed`) | cannot keep a tag: capability access traps, oblivious copy drops the tag |
| metadata in pointer bits | high bits unusable (address leaves the representable region); low bits still usable |
| variadic calls | "variadic arguments are always spilled to the stack and passed via a capability"; mismatched prototypes break |

For values that may be either integer or pointer the guide recommends `uintptr_t`, which "ensures that provenance is maintained".

Basis: documentation (guide `src/impact/recommended-use-c-types.md`, `restrictions-in-capability-locations.md`, `src/compiler/loss-of-provenance.md`; CheriABI paper Section 5.3).

#### 5.3 Single-origin provenance

A capability has one parent, but C can add two `uintptr_t` values (annotations added to the guide's example):

```c
void *c1 = (void *)((uintptr_t)input_ptr + 1);        /* provenance: input_ptr */
void *c2 = (void *)(1 + (uintptr_t)input_ptr);        /* provenance: input_ptr */
uintptr_t offset = 1;
void *c3 = (void *)(offset + (uintptr_t)input_ptr);   /* ambiguous: left operand wins, c3 untagged */
size_t n = 1;
void *ok = (void *)(n + (uintptr_t)input_ptr);        /* unambiguous */
```

The compiler warns on `c3`; "the current behavior for such ambiguous cases is to select the left-hand-side as the provenance source". Remedies: a non-provenance type for one operand, or `__attribute__((cheri_no_provenance))`.

Basis: documentation (guide `src/impact/single-origin-provenance.md`).

#### 5.4 `memcpy`, tags, and byte loops

A copy preserves pointers only if it moves capability-sized units at capability alignment with capability instructions. CheriBSD's portable `bcopy.c` (also `memcpy` and `memmove`) changes one typedef:

```c
#if __has_feature(capabilities)
typedef __intcap_t word;        /* "word" used for optimal copy speed */
#else
typedef intptr_t word;          /* "word" used for optimal copy speed */
#endif
```

and keeps its structure: if source and destination differ modulo the word size (`(t ^ dst) & wmask`) it copies everything by bytes; otherwise bytes up to alignment, whole words, then trailing bytes. The probe reproduces the consequences on a tagged-memory model (48,000 destination granules over 1,500 random copies):

1. Operands *mutually aligned* modulo 16: tags survive for every wholly copied granule; partial head and tail granules lose theirs.
2. Mutually *misaligned*: the copy is byte-wise and every tag is lost though the bytes are identical, as for any hand-written byte or `uint64_t` loop.
3. Rewriting a stored capability with its own bytes clears the tag (139 placements); writing the byte image of a valid capability as data never yields a tag (24,000 steps).

At source level this is weaker than it looks: a pointer-copying `for` loop "may be optimised (e.g. by GCC's tree-loop-distribute-patterns) to a call to memcpy", which preserves tags (Section 6). Across the user/kernel boundary CheriABI is conservative: "we strip tags from copied capabilities unless special interfaces are used".

Basis: source (`lib/libc/string/bcopy.c` in cheribsd) + execution (probe groups "tagged memory", "memcpy") + documentation (CHERI C semantics paper; CheriABI paper).

#### 5.5 Sub-object bounds versus `container_of`

Bounds are per allocation by default. Narrowing to a member when its address is taken is "not enabled by default as [it] may require additional source code changes" (`-Xclang -cheri-bounds=subobject-safe`). It breaks recovering the enclosing object from a member pointer by subtraction (`container_of`, BSD `queue.h`, `uthash.h`). The opt-out is per type, field, or expression:

```c
struct str {
    char              str_array[128];                                    /* member bounds */
    struct list_entry str_le __attribute__((cheri_no_subobject_bounds)); /* container bounds */
};
```

Member bounds are "opportunistic" and inherit compression imprecision.

Basis: documentation (guide `src/impact/subobject-bounds.md`).

#### 5.6 Kernel and loader side

| Interface | CheriABI rule |
|---|---|
| System-call pointer arguments | capabilities; "non-capability versions of `copyout` and `copyin` return errors", so the kernel cannot be a confused deputy for a forged integer |
| Pointers the kernel stores and returns (signal handlers, async I/O, `kevent`) | kept as capabilities in kernel structures |
| `mmap`, `shmat` | return capabilities bounded to the request; fixed mappings and `munmap` require a software-defined `vmmap` permission |
| `malloc` | bounded to the requested size, non-executable, `vmmap` stripped |
| `execve` startup | argument and environment vectors hold bounded capabilities found via the auxiliary vector, not by stack layout |
| Dynamic linking | relocations initialize and bound capabilities at load time because "tags are not preserved on disk"; function capabilities bounded to the shared object |
| `sbrk`; XOR on pointers | unsupported |
| `ioctl`, `sysctl` | handled case by case |

The paper's taxonomy of required source changes: pointer provenance, integer provenance (pointers laundered through non-`uintptr_t` integers), monotonicity, pointer shape (size, alignment), pointer-as-integer sentinels, virtual-address arithmetic (bit flags, hashing, alignment), calling convention, and unsupported constructs. Reported on the CHERI-MIPS FPGA prototype: "over 99% of the C-language userspace" adapted; system-call micro-benchmarks from "3.4% slower for fork, to 9.8% faster for select"; PostgreSQL `initdb` 6.8% slower, against 3.29 times more cycles under Address Sanitizer; on a 291-program overflow suite CheriABI detected 279 / 289 / 291 of the minimal / medium / large overflows where plain MIPS detected 4 / 8 / 175.

Linker-mediated compartments: CheriBSD's library compartmentalisation wraps each resolved function in one trampoline; "a domain transition consists of switching the execution stack and clearing non-argument registers so that no capability leaks to the callee that is not passed as an argument", with a trusted stack recording the path and hooks for `setjmp`/`longjmp`, C++ unwinding, and signals.

Basis: documentation (CheriABI paper Sections 4–5, Tables 2–3) + source (`libexec/rtld-elf/rtld_c18n.c` design comment in cheribsd).

### 6. Provenance models versus capabilities

| Question | PNVI-ae-udi (per the CHERI C paper) | CHERI C semantics | CHERI hardware | Rust core docs | MiniRust |
|---|---|---|---|---|---|
| Carrier | pointer values (allocation ID or empty); "integers do not" | capability plus PNVI provenance; `(u)intptr_t` carries a capability | the value: tag, bounds, permissions | pointers; `usize` does not | `ThinPointer { addr, provenance: Option<Provenance> }` |
| Integer to pointer | allowed into an *exposed* allocation | plain integer: untagged; `uintptr_t`: capability kept | never from an integer; `CSetAddr`/`CBuildCap` need a held authority | `with_addr` (strict); `with_exposed_provenance` (exposed) | `int2ptr` angelically picks an exposed provenance |
| Out-of-bounds arithmetic | undefined beyond one-past | ISO rule kept | defined: tagged within the representable region, untagged outside | `wrapping_offset` may leave the provenance | `wrapping_offset` unchecked |
| Byte-wise pointer copy | — | representation access tracked in ghost state | each byte store clears the tag | — | per-byte `ProvenanceFrag { provenance, position }`; `decode_ptr` rebuilds if all agree |
| Mechanization | Cerberus | Cerberus extension; memory model in Coq | Sail; Isabelle proof for Morello | — | executable specification |

Rust-side allocation and provenance rules are tabulated in `rust-allocation-provenance-and-stack-lifetime-semantics`.

1. **CHERI C does not expose hardware tag clearing as defined behavior.** It keeps ISO's one-past rule "even though that leaves code that exploits the architectural guarantee as UB", because optimizers fold `(p+100001)-100000` into `p+1`. The compiler rule is "compilers can optimise away, but not introduce, code that creates non-representability", modeled with "a ghost-state bit per capability value"; a second ghost bit marks capabilities whose representation bytes were written. The paper states that optimization and undefined behavior "appear to make it impossible" to define the security guarantees by a source-language semantics and gives a "positive semantics" instead.
2. **Strict provenance is the fragment that maps onto capabilities.** Rust's documentation says avoiding integer-to-pointer casts "is pretty much a requirement for using tools like Miri and architectures like CHERI", and that exposed provenance "will not work (well) with tools like Miri and CHERI". Reading `ptr.addr()` as address extraction and `ptr.with_addr(a)` as `CSetAddr` is a derived correspondence: both keep an existing pointer's authority and change only the address. It is inexact at one point: Rust's `wrapping_offset` is documented to "remember" its allocation "even if it is offset far outside the memory range occupied by that allocation", whereas a capability that leaves the representable region stays untagged.
3. **Exposed provenance has no hardware counterpart.** PNVI-ae-udi and MiniRust let an integer regain provenance because some allocation was exposed; MiniRust guesses "maximally in the programmer's favor". CHERI re-tags bits only under an explicit authority (`CBuildCap`), which in the probe never exceeded that authority (4,000 trials) and never succeeded from untagged operands (33,000 results).
4. **Per-byte provenance is strictly finer than one tag per granule.** A pointer copied one `AbstractByte` at a time keeps provenance in MiniRust; on CHERI it becomes untagged. A CHERI implementation refines MiniRust here only if byte loops over pointers become capability-word copies or are avoided (derived; Rust-on-CHERI toolchains were not examined).

Basis: documentation (CHERI C semantics paper Sections 2–4; `library/core/src/ptr/mod.rs` module docs in rust-lang/rust) + source (MiniRust `spec/mem/pointer.md`, `spec/mem/interface.md`, `spec/mem/intptrcast.md`, `spec/lang/representation.md`) + execution (probe groups "CBuildCap", "tag conservation") + derived (items 2 and 4).

### 7. Heap temporal safety by sweeping revocation

#### 7.1 Guarantee and mechanism

A capability to freed memory keeps its tag and bounds, so spatial enforcement alone permits use after free and use after reallocation. The CHERI heap designs delay *reuse*, not `free`: "use-after-free is possible and will continue to access the old object, as if its lifetime extended until revocation; use-after-reallocation is ruled out". Stale pointers are replaced by clearing tags, which "risks type confusion if programmers intend to use the capability tag to distinguish between integers and pointers in tagged unions". Stack temporal safety is not provided.

Freed address space sits in **quarantine**; the allocator "paints" a **revocation bitmap** (one bit per capability-sized granule; CheriBSD also keeps per-page and per-otype bitmaps); a **sweep** clears the tag of every capability, in registers and memory, whose *base* lies in a painted granule; an **epoch counter** increments when a sweep starts and when it ends. Memory may be reused once a sweep that started after painting has finished:

```c
static inline int
cheri_revoke_epoch_clears(cheri_revoke_epoch_t now, cheri_revoke_epoch_t then)
{
	return (cheri_revoke_epoch_ge(now, then + (then & 1) + 2));
}
```

The probe checks this against the start/finish reading for 320 `(then, now)` pairs; the CHERIoT allocator uses the same test (`current - previous > 1 + (previous & 1)`).

| Design | Barrier | Mutator pause | Invariant |
|---|---|---|---|
| CHERIvoke | none | the whole sweep | sweep sees a snapshot |
| Cornucopia | capability-*store* tracking (capability-dirty pages) | concurrent pass, then stop-the-world over re-dirtied pages | stated over dirty pages; progress only while stopped |
| Cornucopia Reloaded | capability-*load* barrier: a generation bit per page-table entry compared with a per-core bit; a tagged load from a mismatching page traps and the handler cleans that page first | only to scan registers and flip the per-core generation | "any pointer held in a user thread's register file did not point into quarantine as of the beginning of the last revocation" |

With the generation bit, page-table entries are written once per epoch and starting an epoch is constant-time. ISAv9 specifies the hooks: a trapping load-capability page permission, a capability-dirty bit that must never give false negatives, and per-core/per-mapping "generation counters".

Reported costs: Cornucopia on CHERI-MIPS FPGA added roughly 10% cycles and 10–15% DRAM traffic on memory-intensive workloads; on Morello "4% cycle and 9% memory bus traffic geomean overheads, with a 33% traffic overhead for omnetpp" and median pauses "as high as 30 milliseconds". Reloaded removes "significant revocation-induced stop-the-world periods, without additional wall- or CPU-time cost over Cornucopia and with median 87% of Cornucopia's DRAM traffic overheads across SPEC CPU2006 and < 50% for pgbench". The evaluated policy revokes when quarantine exceeds a quarter of the heap, unless under 8 MiB.

Basis: documentation (Cornucopia and Cornucopia Reloaded papers; guide `src/impact/revocation.md`) + source (`sys/cheri/revoke.h`, `lib/libsys/cheri_revoke.2` in cheribsd; `sdk/core/allocator/revoker.h` in cheriot-rtos) + normative (ISAv9 "Capability Dirty Bit", "Per-Page Capability Load Barriers").

#### 7.2 Why a barrier is needed at all

The probe's abstract model (one register, three single-slot pages each empty, live, or stale; a sweeper visiting pages in order; a mutator loading or storing between sweeper steps) explores every interleaving from every initial state:

| Design in the model | Result | States |
|---|---|---|
| register scan at start, concurrent sweep, no barrier | **unsound**: a stale capability loaded from an unswept page is stored into a swept page | 474 |
| plus store tracking and a final stopped re-sweep of dirtied pages and registers | sound | 474 |
| register scan at start, load barrier cleaning an unswept page before the load completes | sound | 266 |

This is why Cornucopia needs its stop-the-world phase and why Reloaded's invariant can be stated over registers alone.

Basis: execution (probe group "sweeping revocation") + derived (the model is this report's abstraction of the designs in 7.1).

### 8. CHERIoT: the model re-cut for a microcontroller

#### 8.1 ISA differences from CHERI-RISC-V

| Aspect | CHERIoT |
|---|---|
| Base | RV32, machine mode only, "no virtual memory"; sixteen registers of 64 bits plus tag |
| Modes | no hybrid mode, no default data capability, no offset addressing; "all code runs in pure-cap mode" |
| Roots | memory, executable, and sealing roots, since the 6-bit permission field cannot express every combination |
| Deep attenuation | without *Load Mutable*, loaded capabilities lose store and load-mutable (transitive read-only); without *Load Global*, they lose global and load-global (transitively non-capturable) |
| Sentries | forward sentries that inherit, disable, or enable interrupts, and two backward (return) sentries; `CJALR` accepts only the kinds legal for its register operands, closing an attack where a caller gives an interrupt-disabling callee a return sentry to itself |
| NULL | all zeroes, decoding to length 0 (other CHERI architectures: maximum length) |
| Stack tracking | two registers record the lowest stack address written, at 16-byte granularity |

The encoding drops the internal exponent: 9-bit `B` and `T`, a 4-bit exponent where 15 means 24, byte precision to 511 bytes, and a representable range `[base, base + 2^(e+9))`. The stated trade: "Other CHERI implementations include much larger representable ranges than this minimum in order to accommodate common C programming practices. However, this comes at the cost of bits in the representation and our experience so far has shown that it is not necessary for embedded systems." The probe agrees with these statements on 22,575 cases, including that the address one below base always changes the decoded bounds.

Basis: documentation (`archdoc/chap-cheri-riscv.tex`) + source (`src/cheri_cap_common.sail` in cheriot-sail) + execution (probe group "CHERIoT encoding").

#### 8.2 Temporal safety in the instruction set

"In addition to the capability tag bits there is a revocation bit for each revocation granule (currently the same size as a capability, 8 bytes). After loading a capability with the tag set, the `CLC` instruction loads the revocation bit corresponding to the base address of the capability (N.B. not the address). If the granule's revocation bit is set then the capability's tag is cleared before writing it to the destination register." The bits are memory-mapped for the allocator; regions without them (code, globals, device memory) are never revoked; sealing capabilities are not revoked this way. This is a load barrier on every capability load, with no MMU; a sweep is still required before reuse (software or hardware revoker).

Basis: documentation (architecture document, "Temporal safety") + source (`mem_read_cap_revoked` in `src/cheri_mem.sail`; `sdk/core/allocator/revoker.h`, `sdk/include/platform/concepts/hardware_revoker.hh` in cheriot-rtos).

#### 8.3 Mutual-distrust compartments without an MMU

A cross-compartment call enters the RTOS switcher through an interrupt-disabling forward sentry with a sealed export-table entry naming the callee. The switcher:

1. validates the caller's stack capability — exact expected permissions (local, store-local), base equal to the high-water-mark base register, 16-byte alignment — else forces an unwind;
2. pushes a frame on a per-thread trusted stack reached through a machine-mode special register;
3. zeroes the used part of the stack, from the high-water mark, with capability stores of NULL (`csc cnull, 0(base)` in 32-byte chunks), clearing data and tags together;
4. zeroes unused argument registers and dead registers so nothing reaches the callee except arguments;
5. on return or fault pops the frame; a forced unwind returns `-ECOMPARTMENTFAIL`.

Faults are recoverable per compartment: the switcher may call `compartment_error_handler(struct ErrorState *frame, size_t mcause, size_t mtval)`, counts invocations in the trusted-stack frame, treats a fault inside the handler as a double fault, and stops at a fixed limit per call; each case ends in a forced unwind. Hazard-pointer slots are cleared by 32-bit zero stores "to clobber the tags", a direct use of Section 2.2.

Basis: source (`sdk/core/switcher/entry.S` in cheriot-rtos) + documentation (architecture document, "Sealed capabilities", "Stack high water mark").

#### 8.4 Sealed capabilities as hardware existential types

Under Mitchell and Plotkin's encoding of abstract data types, sealing realizes hardware-enforced existential quantification across mutually distrusting cross-language FFI boundaries:

$$\exists \alpha.\; \mathrm{Cap}(\alpha) \times (\mathrm{Cap}(\alpha) \to \dots)$$

1. **Pack (`CSeal`) / unpack (`CUnseal`).** A compartment holding private sealing authority $k_\alpha$ (`Permit_Seal`/`Permit_Unseal` over unforgeable `otype` $\alpha$) packs concrete state $v : \mathrm{Cap}(\tau)$ via `CSeal(v, k_\alpha)`, exporting an opaque sealed handle $h$ plus sentry operations closing over $k_\alpha$. Untrusted callers (e.g., unverified C linked against verified Rust) trap on dereferencing $h$, clear $h$'s tag on any mutation (Section 2.3), and cannot reconstruct $v$ via `CBuildCap` without ambient memory authority. Only the holder of $k_\alpha$ can unpack $v$ via `CUnseal(h, k_\alpha)`.
2. **CHERIoT's 3-bit `otype` partition vs. ISAv9.** Unlike ISAv9 CC-128 (18-bit `otype`, exact `cs2.addr == cs1.otype` check in `CUnseal`), CHERIoT (`cheriot-sail` `src/cheri_insts.sail`, lines 783–842) encodes a 3-bit stored `otype` with implicit bit 3 for non-executable capabilities: `0` unsealed, `1–5` forward/backward IRQ sentries, `6–7` executable sealed, `8` reserved, `9–15` non-executable sealed. `CSeal` clears the tag on format mismatch (`1..7` requires `Permit_Execute`; `9..15` requires non-executable) or reserved values; `CUnseal` checks `inCapBounds(cs2, zero_extend(cs1.otype), 1)` (range containment rather than cursor equality) and strips `Global` if `cs2` lacks `Global`.
3. **CHERIoT RTOS two-level software sealing (`2^32 - 2^24` keys).** To extend seven non-executable hardware `otype`s, CHERIoT RTOS (`sdk/include/token.h`, `sdk/core/allocator/token.h`, `sdk/core/token_library/token_unseal.S`) reserves `CheriSealTypeAllocator = 11` and `CheriSealTypeStaticToken = 12` behind private keys `__sealingkey_{either,static,dynamic}`. Compartments mint length-1 non-dereferenceable `TokenKey`s from the sealing root (`STATIC_SEALING_TYPE` / `token_key_new`). `token_sealed_unsealed_alloc` prepends an 8-byte `TokenObjectHeader { uint32_t type }` (`type == key.addr`), sets cursor to `->data`, and seals with `otype = 11`. `token_unseal_internal` (IRQs disabled) verifies `key.tag`, `key.addr == key.base`, `key.len > 0`, and `CHERI_PERM_UNSEAL`; executes hardware `cunseal`; clears low 3 user-permission bits; loads `header.type` at `-8(ca2)` and checks equality with `key.addr`; narrows bounds strictly to `->data` via `csetboundsexact` (hiding the header); and zeroes the architectural key register before `cret`.

Group 24 of the probe (5,557 existential-sealing checks) verifies CHERIoT's `otype` partition, `inCapBounds` unsealing, `token_unseal_internal` header exclusion and rejection of forged/mismatched `TokenKey`s, and ISAv9 `CSeal`/`CUnseal`/`CBuildCap` non-forgeability.

Basis: source (`src/cheri_insts.sail` lines 776–842 in cheriot-sail; `sdk/include/token.h`, `sdk/core/allocator/token.h`, `sdk/core/token_library/token_unseal.S` in cheriot-rtos) + documentation (`archdoc/chap-cheri-riscv.tex`) + execution (probe group 24) + derived (existential correspondence per Mitchell & Plotkin 1988, DOI 10.1145/44501.45065, bibliographic only).

### 9. CHERI against partial and probabilistic hardware mitigations

| Mechanism | Architectural state | What a passing check proves | Limits |
|---|---|---|---|
| CHERI | 1 tag bit per pointer-sized granule; double-width pointers | the pointer derives from an authority covering this access; no secret | needs revocation for temporal safety; no C type safety beyond code/data and sealed types |
| Arm MTE | "a 4-bit allocation tag for each 16-byte granule"; logical tag in address bits 59–56 | pointer tag equals memory tag | 16 values, so reuse can collide; tags are ordinary pointer bits; synchronous, asynchronous, or asymmetric reporting |
| Arm pointer authentication | a code "55 minus the virtual address size" bits wide (7 at 48-bit addresses); five keys | the pointer was signed with a key | probabilistic, key-dependent; no bounds |
| x86 CET shadow stack, Arm GCS | a second stack writable only by call/return and dedicated instructions | return address matches the protected copy | backward control flow only |
| Protection keys | 4-bit key per page-table entry, per-thread rights register (16 keys; 8 on arm64) | the thread's register allows this key | page granularity; register is user-writable; on x86 "no effect on instruction fetches" |

Only the CHERI row is deterministic for arbitrary data pointers; the Morello paper's phrase is "deterministic and secrets-free". The MTE collision remark is derived from the tag width alone. Code generation for CET, BTI, and PAC is in `verified-cfi-cet-bti-pac-cfguard-and-speculative-hardening`; software-only isolation is in `modern-sfi-lfi-and-ring0-wasm-kernels-2020-2026`.

Basis: documentation (Linux `Documentation/arch/arm64/memory-tagging-extension.rst`, `pointer-authentication.rst`, `gcs.rst`, `Documentation/arch/x86/shstk.rst`, `Documentation/core-api/protection-keys.rst`; guide `src/limitations/integer-pointer-safety.md`) + derived (comparative classification).

### 10. Mill SASOS protection domains: Turfs, Portals, PLBs, WKRs, Pointer Events, and IZM

Where CHERI puts bounds and tags into double-width capabilities atop paged virtual memory, the **Mill CPU** (Mill Computing, Inc.; U.S. Patents 9,747,218; 10,678,700; 9,524,163; 9,652,230) explores the orthogonal **Single-Address-Space OS (SASOS)** point: keeping 64-bit pointers while enforcing thread-specific protection domains (**Turfs**) in hardware parallel to virtually-tagged L1 caches.

#### 10.1 Decoupling protection from translation (`iPLB`/`dPLB`, `WKR`, and TLB after LLC)

Mill splits translation from protection (`US10678700B2`; Mill Programming Model):

1. **Virtual caches + TLB after LLC miss.** L1I, L1D, and L2/LLC are virtually tagged in one 64-bit address space. Virtual-to-physical translation sits in a **TLB in the memory controller between the LLC and DRAM**, invoked only on LLC misses (with lazy DRAM backing on eviction).
2. **Split `iPLB`/`dPLB` parallel to L1.** Fetches and loads/stores check virtual ranges against split **Protection Lookaside Buffers** (`iPLB`: `execute`/`portal`; `dPLB`: `read`/`write`, optional `grant`) in parallel with L1 access (buffering stores until approved). Backed by per-turf **Persistent Permission Tables** (byte-granular interval trees in `rwTableReg`/`xpTableReg`) and per-call **Transient Permission Tables** (in private **spillets**), PLB entries carry a **`novel` bit** set on insertion and cleared only on eviction: revoking a `novel = 1` entry discards it from the PLB with zero memory-table writes.
3. **Well-Known Region (`WKR`) fast-path registers.** Nine `WKR` registers form a micro-cache above the PLBs (`10,678,700`): `cWKR` (code bitmask+comparand), `dWKR` (`.data`/`.bss` off `dpReg`), `rWKR` (`.rodata`), `tWKR` (lazy per-turf-per-thread TLS via `tLibIndex`), `sWKR` (stack `[fpReg, spReg)`), `oWKR`/`iWKR` (argument windows), `hWKR` (home), and `nWKR` (null). Base-register hits bypass `dPLB`; pointer dereferences query `dPLB`.

Basis: documentation (`US10678700B2` Claims 1–14; Mill summary of `US9747218B2`; Mill Programming Model).

#### 10.2 Portals, stacklets, call-scoped `PASS`/`GRANT`/`REVOKE`, and borrow isomorphism

A thread executes in one **Turf** (20–32-bit `turfID` + `threadID`) at a time and crosses domains without thread switches or kernel traps:

- **Portals, stacklets, and ~4–5 cycle calls.** A **Portal** is a memory descriptor in an `iPLB` region with `portal` (`p`) permission holding target `turfID`, entry PC, and callee `WKR` state. On portal `CALL`, the asynchronous **Spiller** saves caller belt/return/turf state outside the callee's turf; hardware switches `specReg`, loads callee `WKR`s and per-thread-turf **stacklet** bounds from two cache lines (portal entry + stacklet info block), and zero-initializes a frame. Re-entrant calls (`A → B → C → B`) avoid stacklet overlap via a Top-of-Stacklet Pointer (`TOSP`, lazily zeroed on first TLB miss). With zero TLB flush, kernel trap, or stack copy — and 1-cycle call dispatch, 3-cycle L1 load latency, plus a short non-speculative `RETURN` bubble — portal crossing targets **~4–5 cycles** (vs. hundreds of cycles for OS context switches noted in `10,678,700`), unmeasured on silicon.
- **Non-speculative `RETURN` and patent evolution (`9,747,218` vs. `10,678,700`).** Both patents force portal `RETURN` to execute **non-speculatively** (blocking speculative cross-domain leakage). Protocols evolved between filings:
  - **`US9747218B2`** (filed 2015-03-20, granted 2017-08-29; per Mill's summary) separates persistent `GRANT`/`REVOKE` (lazy via `novel` bit) from call-scoped `PASS` (wildcard-turf transient grant auto-revoked on `RETURN`) and `ARGS` (`OutP`→`InP`).
  - **`US10678700B2`** (filed 2016-03-21, granted 2020-06-09; Claims 15–24) generalizes this to transient call-scoped `GRANT` (auto-revoked on portal `RETURN`), `RELAY` (nested forwarding), `PERSIST` (promoting a transient grant with `grant` permission into a persistent turf permission while stripping `grant`), `SESSIONBEGIN`/`SESSIONISSTARTED`/`SESSIONEND`/`SESSIONMAKE`, `ARGS`, and a **pointer guard bit** (Claims 19–20): guarded pointers check **only** transient grants (blocking confused-deputy access to the server's persistent turf), unguarded pointers ignore transient grants, and loads through guarded pointers propagate the guard bit.
- **Borrow isomorphism (`&'call [u8]` / `&'call mut [u8]`, derived).** A caller compiles `&'call [u8]` or `&'call mut [u8]` across a Portal into one call-scoped transient `PASS`/`GRANT` (`M_READ` or `M_READ|M_WRITE`, without `M_GRANT`), yielding zero-copy byte-granular confinement, guard-bit confused-deputy separation, monotone nested `RELAY`, and auto-revocation on non-speculative `RETURN`. Probe Group 24 (10,400 checks across 400 nested/re-entrant `A → B → C → B` trees) verifies monotonicity, guard-bit isolation, stacklet non-overlap, `PERSIST` gating, `novel`-bit revocation, and zero post-return access.

Basis: documentation (`US10678700B2` Claims 15–24; Mill summary of `US9747218B2`) + execution (probe group 24) + derived (borrow isomorphism; ~4–5 cycle envelope).

#### 10.3 Pointer events (`US9524163B2`), Implicit Zero Map (`US9652230B2`), and CHERI vs. Mill

- **Pointer processing (`US9524163B2`, granted 2016-12-20).** Adds (1) per-pointer **event bits** indexing **Read**, **Write**, and **Update Interest Mask Registers** (stores concatenate destination and stored event bits into Update for zero-overhead generational GC write barriers); and (2) a **6-bit granularity field** + 58-bit chunk/offset address checked by an **Address Derivation Unit** for offset overflow, with `Refine` decrementing granularity and a **valid/invalid bit** permitting C/C++ one-past-the-end comparisons/differences while rejecting dereference or escape (advisory chunk checks, not out-of-band-tagged capabilities).
- **Implicit Zero Map (`IZM`, `US9652230B2`, granted 2017-05-16).** A 1-bit-per-cache-line bitmap for frame-local stack lines: new frames start implicitly zero (loads return zero without cache/DRAM reads, blocking stack leaks and zeroing loops); partial stores zero-fill unwritten line bytes without write-allocate RMW fills; frame exit invalidates lines and cancels pending write-backs.

| Dimension | CHERI (ISAv9 / Morello / CHERIoT) | Mill SASOS (Turfs / Portals / PLBs) |
|---|---|---|
| Authority locus | Inline 128-bit / 64-bit fat ptr + 1-bit memory tag | Domain tables (`WKR` + `iPLB`/`dPLB` + spillet transients); 64-bit ptrs |
| Bounds precision | Compressed FP (`CRRL`/`CRAM` above 4 KiB / 511 B) | Byte-granular interval trees in PLBs; optional 6-bit granularity (`9,524,163`) |
| Domain crossing | Sealed cap / sentry + switcher (`rtld_c18n` / CHERIoT) | Portal `CALL` + Spiller + stacklets + non-speculative `RETURN` (~4–5 cycles arch.) |
| Call borrow (`&'call`) | Local-cap discipline (`Store_Local`) or heap revocation | Native transient `PASS`/`GRANT` auto-revoked on `RETURN` + guard bit |
| Heap temporal safety | Quarantine + sweep (`Cornucopia Reloaded` / CHERIoT) | Persistent grants need explicit `REVOKE` (`novel` bit) |
| Status | Silicon (Morello, CHERIoT); Sail/Isabelle/Cerberus proofs | Patents/specs only; no shipped silicon or public mechanized proofs |

Basis: documentation (`US9524163B2`, `US9652230B2`, `US10678700B2`; Sections 2–4, 7–8) + derived (comparison table).

### 11. Peripheral DMA isolation: CHERI-DMA capability bounds versus page-granular IOMMUs

Bus-mastering peripherals (NICs, Wi-Fi/baseband MCUs, GPUs, NVMe, Thunderbolt/USB4) performing DMA directly to DRAM bypass CPU-side capabilities or Turfs unless the I/O path enforces bounds.

#### 11.1 Why page-granular IOMMU IOVA mappings fail (*Thunderclap*)

*Thunderclap* (Markettos et al., NDSS '19, FPGA evaluation across Linux, FreeBSD, macOS, Windows) and HASP '20 expose four IOMMU flaws:

1. **4 KiB sub-page aliasing.** Page-granular mappings expose unrelated adjacent kernel slab objects sharing the same 4 KiB DMA page (enabling VPN sniffing and root-shell hijacking in seconds).
2. **IOTLB-miss cost.** Millions of per-packet mappings/sec hit up to **6 memory lookups** on Intel IOMMU misses (4 page-table + 2 device levels = **600% worst-case overhead**).
3. **Async IOTLB invalidation.** Deferred shootdowns open temporal windows across reallocated pages.
4. **PCIe ATS bypass.** Advertising PCIe Address Translation Services (`ATS`) led Linux to enable switch ATS, letting a malicious peripheral mark packets "pre-translated" and bypass IOMMU translation completely.

Basis: documentation (Markettos et al., NDSS '19 *Thunderclap*; HASP '20 Sections 2.1, 5.4, 7.1).

#### 11.2 CHERI-DMA: capability-bounded peripherals, CSU, CLUT, and descriptor rings

Markettos et al. (HASP '20) extend CHERI bounds across untrusted peripheral hardware and trusted SoC hardware running untrusted firmware:

- **Tag-clearing invariant.** Untrusted I/O interconnects carry no tags; every DMA write atomically clears CHERI tags on touched granules (and invalidates cached caps), blocking capability forgery and tag-DRAM access.
- **MCUs (no MMU): Capability Search Unit (`CSU`).** Replaces privileged MPU registers with capability slots written atomically by one capability store; monotonicity allows delegating slots to unprivileged drivers, though associative lookup caps capacity (~8–16 entries).
- **Application SoCs: `ALUT` / `CLUT`.** Splits a 64-bit IOVA into slot index $I = A[63:s]$ and offset $O = A[s-1:0]$ ($s=40 \Rightarrow 2^{24}$ buffers of 1 TiB) for a **single-level** per-device table (**100% worst-case overhead** vs. 600% for IOMMU). A **CLUT** holds tagged capabilities directly for **1-byte bounds**, **atomic** slot updates, and null-write revocation without kernel mediation. A **virtually-addressed CLUT** tags entries with an ASID above a static superpage IOMMU: the CLUT absorbs dynamic per-packet protection while the IOMMU handles static virtualization.
- **Trusted SoC hardware / untrusted firmware.** Peripherals can consume **capability-typed DMA descriptor rings** (shared representation, tag-clearing on writes) or run CHERI over private memory; shared DRAM enforces CPU↔device non-interference via **memory segregation** or **capability coloring** (spare bits trapping cross-color access).

| Mechanism | Spatial granule | Atomic | Shared SW/HW rep | Worst-case mem overhead | Scalable |
|---|---|---|---|---|---|
| Raw integer DMA | None | No | Yes | 0% | Yes |
| MPU | HW, 1 B | No | No | 0% | No (~8–16) |
| **CHERI CSU** | HW, **1 B** | **Yes** | **Yes** (delegable) | **0%** | No (~8–16) |
| **IOMMU** | HW, **4096 B** | No | No | **600%** (6-level) | Yes |
| **ALUT** | HW, **1 B** | No | Yes | **100%** (1 lookup) | Yes |
| **CHERI CLUT** | HW, **1 B** | **Yes** | **Yes** (tagged cap) | **100%** (1 lookup) | Yes |
| In-device CHERI cap | HW, **1 B** | **Yes** | **Yes** | **0%** | Yes |

**Cache-coherence complementarity (derived).** `CSU`/`CLUT`/capability rings enforce spatial authority and atomic revocation on DMA, but on non-coherent ARM/RISC-V PCIe interconnects do not replace physical pinning, exclusive in-flight ownership, or explicit cache clean/invalidate maintenance (and cache-line alignment preventing tearing) absent hardware coherence (x86 snooping or CXL `CXL.cache`).

Basis: documentation (Markettos et al., HASP '20 Sections 4–10, Table 1; NDSS '19 *Thunderclap*) + derived (cache-coherence complementarity).

## Boundaries

**Not examined**

- Levy Chapters 3–10. The author-hosted files for Chapters 3, 4, 8, 9, and 10 could not be retrieved (5–7 were not attempted), so nothing here rests on Levy's accounts of the Plessey System 250, IBM System/38 (including its single-level-store pointer format), the iAPX 432, or his "Issues" chapter. The 432 findings come from the Colwell postmortem; System/38 and System 250 appear only through Table 1-1 and one ISAv9 sentence.
- Full text of **Baker et al. (1987)** (ICCD, pp. 512–514), **Lonergan & King (1961)** (Datamation 7(5):28–32), **Barton (1961)** (WJCC 19:393–396), **Mitchell & Plotkin (1988)** (TOPLAS 10(3):470–502, DOI 10.1145/44501.45065), and USPTO full text of **U.S. Patent 9,747,218 B2** (granted 2017-08-29): verified via bibliographic records, secondary summaries, or Mill Computing's patent summary; parallel Symbolics checks were read directly in Moon (1987) and U.S. Patent 4,887,235 (3600), 40-bit Ivory emulation in Withington et al. (1994), and full Mill Turf/Portal mechanics in `US10678700B2`.
- The CHERIoT MICRO 2023 paper (Amar et al., "CHERIoT: Complete Memory Safety for Embedded Devices", DOI 10.1145/3613424.3614266, pages 641–653): only its bibliographic record was verified. No area, power, or performance figure for CHERIoT is reported here.
- The Morello performance report (UCAM-CL-TR-986, DOI 10.48456/tr-986): only title, authors, date, and abstract were read. The Morello architecture specification and Morello's exact encoding constants were not read.
- Measured CHERI-DMA silicon/FPGA performance (e.g., CAPcelerate): HASP '20 Table 1 is an analytical design-space sketch prior to RTL implementation.
- Any ratified or draft RISC-V CHERI specification after ISAv9, the CHERI-x86-64 sketch, CHERI Linux, and Rust-on-CHERI compilers.
- The proofs themselves: the HOL4 development for CHERI Concentrate, the Isabelle Morello proofs, the Coq CHERI C memory model, and the SMT-checked Sail properties are known only from their papers or READMEs.
- The ISO technical specification for PNVI-ae-udi; it is represented only by the CHERI C paper's summary.

**Unknown**

- Whether Rust's `usize` should be address-sized or capability-sized on CHERI, and how a Rust CHERI target reconciles MiniRust's per-byte provenance with per-granule tags. The examined Rust source names CHERI only as a motivation for strict provenance; the examined MiniRust files do not mention it.
- Production-grade overhead. The "0-5%" figure is a summary sentence in the Morello paper, and the same paper attributes some measured slowdowns to prototype stalls.
- Real-silicon cycle counts, PLB hit rates, area, and power for Mill Turfs/Portals/`WKR`/`IZM`: no Mill silicon has shipped, so ~4–5 cycle Portal calls remain patent/architectural claims.

**Known not to apply**

- "A capability check implies a table lookup": CHERI capabilities are direct pointers.
- "A byte-wise overwrite clearing a tag is a C-source-level guarantee": optimizers may turn loops into tag-preserving copies and remove transient excursions (Section 6).
- "CHERI bounds give temporal safety": they do not (Section 7).
- "The CC-128 alignment numbers hold for Morello or CHERIoT": Morello uses different constants and CHERIoT a different encoding.
- "MTE or pointer authentication are capabilities": their tags and codes are forgeable or guessable pointer bits.
- "Mill call-scoped `PASS`/`GRANT` solves general heap temporal safety": auto-revocation enforces lexical call borrows (`&'call`), not escaping heap graphs.
- "CHERI-DMA removes cache-coherence maintenance": spatial DMA bounds (`CSU`/`CLUT`) do not replace clean/invalidate barriers on non-coherent interconnects (Section 11.2).

**Unsupported**

- CheriABI: `sbrk`, XOR-ing pointers, pointers in under-aligned storage. CHERIoT: hybrid mode, virtual memory, offset addressing. ISAv9 removed CHERI-MIPS and deprecated relocation by the default data and program counter capabilities. Modifying a sealed capability clears its tag (CHERIoT documents one exception: a load through an authority without Load Global clears Global even on a sealed capability). Mill `US10678700B2`: `PERSIST` cannot transfer `grant`; guarded pointers cannot access persistent turf regions.

**Stronger conclusions the evidence does not support**

- That the probe proves monotonicity, Mill non-interference, or CHERIoT soundness: it checks transcriptions/abstract models (exhaustive only for 7-bit toy CHERI; sampled for CC-128/CC-64, Mill portal trees, and sealing), without concurrency, exceptions, or hardware speculative channels.
- That CHERI or Mill is verified end to end: cited CHERI proofs are ISA-level (excluding compilers, kernels, allocators, RTL), and no public mechanized Mill proof was examined.

## Evidence

All material was retrieved on 2026-11-19.

| Source | Identity | Parts used |
|---|---|---|
| CHERI ISAv9 | CTSRD-CHERI/cheri-specification `b1570f87612584f31da7a962214068b7d71dd6a5` (tag `release-9.0`; commit dated 2023-09-20); report page UCAM-CL-TR-987, September 2023, 523 pages, DOI 10.48456/tr-987 | `chap-architecture.tex`, `chap-model.tex`, `chap-rationale.tex`, `chap-historical.tex`; section titles cross-checked against the first 67 pages of the published PDF |
| CHERI-RISC-V Sail | CTSRD-CHERI/sail-cheri-riscv `cf36cfd4fca0bd10a5906651bf48b9674ccd0a2b` | `src/cheri_prelude_128.sail`, `cheri_prelude_64.sail`, `cheri_cap_common.sail`, `cheri_insts.sail`, `cheri_mem.sail`, `cheri_mem_metadata.sail`, `cheri_types.sail`, `README.md` |
| RISC-V Sail | rems-project/sail-riscv `b748a82361d12d20fa6da30d62b98a83ef8860d8` (submodule pin of the above) | `model/riscv_mem.sail`, `model/prelude_mem.sail` |
| Test vectors | CTSRD-CHERI/cheri-compressed-cap `5b3dfd25ae49a62594477ba25be1371d29774cf9` | `test/contrib/setbounds_inputs_128.cpp` (10,000 rows), `test/setbounds_test_128.cpp` |
| CheriBSD | CTSRD-CHERI/cheribsd `88f39900c32928d807dba245fba138808c666f34` | `lib/libc/string/bcopy.c`, `sys/cheri/revoke.h`, `lib/libsys/cheri_revoke.2`, `libexec/rtld-elf/rtld_c18n.c` |
| Programming guide | CTSRD-CHERI/cheri-c-programming `4fe4405fe9466ddb728f712deaba267f662fb268`; 2020 edition UCAM-CL-TR-947 for the `vaddr_t` spelling | `src/impact/*.md`, `src/compiler/*.md`, `src/limitations/*.md`, `src/introduction/history.md` |
| CHERIoT | CHERIoT-Platform/cheriot-sail `518813ec3e595f79930d9129eaded2521831cbe2`; CHERIoT-Platform/cheriot-rtos `e2dad05078bd25ed6f1ab993e14f332aa8c20557` | `archdoc/chap-cheri-riscv.tex`, `src/cheri_cap_common.sail`, `src/cheri_insts.sail`, `src/cheri_mem.sail`; `sdk/core/switcher/entry.S`, `sdk/core/allocator/revoker.h`, `sdk/core/allocator/token.h`, `sdk/include/token.h`, `sdk/core/token_library/token_unseal.S`, `sdk/include/platform/concepts/hardware_revoker.hh` |
| Rust, MiniRust | rust-lang/rust `b0b600668bb9b4a897e2299b0a44289d42276545`; minirust/minirust `063d784186d3252bee242217f218223205c0b568` | `library/core/src/ptr/mod.rs` module documentation; `spec/mem/*.md`, `spec/lang/representation.md` |
| Linux | torvalds/linux `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` | the five documentation files named in Section 9 |
| Papers (full text retrieved) | DOIs 10.1145/45059.214411, 10.1109/TC.2019.2914037, 10.1109/MM.2023.3264676, 10.1145/3297858.3304042, 10.1145/3617232.3624859, 10.1109/SP40000.2020.00098, 10.1145/3620665.3640416, 10.1109/MC.1987.1663356 (Moon 1987), 10.14722/ndss.2019.23194 (Thunderclap); Markettos et al. HASP '20 (`2020hasp-cheri-dma.pdf`); Withington et al. (PLDI '94 VLM extended abstract) | author- or archive-hosted copies; bibliographic records confirmed against Crossref or publisher indices |
| Patents (full text retrieved) | `US10678700B2` (granted 2020-06-09), `US9524163B2` (granted 2016-12-20), `US9652230B2` (granted 2017-05-16), `US4887235A` (Symbolics 3600, granted 1989-12-12) | Google Patents full text (Mill patents) and Bitsavers HTML text (Symbolics 3600 patent): specifications, figures descriptions, and claims |
| Mill official docs | `https://millcomputing.com/patents/` (summaries of `US9747218B2`, `US10678700B2`, `US9524163B2`, `US9652230B2`); `https://millcomputing.com/introduction-to-the-mill-cpu-programming-model/` | patent summaries (including `PASS`/`GRANT`/`REVOKE` in `9,747,218`), memory/PLB/TLB/pipeline latencies |
| Levy | https://homes.cs.washington.edu/~levy/capabook/ | landing page (publisher, year), `Chapter1.pdf`, `Chapter2.pdf` as extracted text |

Coordinate checks: CHERI Concentrate appeared in *IEEE Transactions on Computers* 68(10):1455–1469; the Crossref record omits Thomas Bauereiss, whom the paper's own author list includes. Cornucopia Reloaded is DOI 10.1145/3620665.3640416 (ASPLOS '24 Volume 2, pages 251–268); the similar DOI ending `3640395` is an unrelated paper in the same volume. No immutable hash is available for the papers, patents, or Levy's files; the URLs, patent numbers, and DOIs are the strongest identities obtained.

Execution evidence: `python3 -B support/verify_cheri_capability_algebra.py` under CPython 3.13.15 on x86-64 Linux printed `PASS: 24 check groups, 426808 cases` in about 7 seconds; the complete output is preserved as `support/expected_output.txt` and two consecutive runs were byte-identical. Cases by kind: 15 golden; 97 alignment; 175,420 exhaustive toy-format; 60,000 representability; 42,050 derivation steps; 37,017 sealing, `CBuildCap`, and tag conservation; 72,139 tagged memory and `memcpy`; 22,579 CHERIoT; 1,534 epoch and sweep states; 15,957 Group 24 checks (10,400 Mill SASOS nested/re-entrant portal, `PASS`/`RELAY`/`PERSIST`, guard-bit, and `novel`-bit checks; 5,557 CHERIoT format-partition, RTOS `token_unseal_internal`, and ISAv9 existential-sealing checks). Run with `--upstream-vectors` pointing at the pinned `setbounds_inputs_128.cpp`, the transcription matched all 10,000 rows (20,000 bound pairs).

Synthesis versus source: Sections 1.4, 1.5 (architectural performance law), 3.2 (fractions), 6 (items 2 and 4), 7.2, 8.4 (existential-type correspondence), 9 (comparative classification), 10.2 (borrow isomorphism), 10.3 (comparison table), and 11.2 (cache-coherence complementarity) are this report's derivations; the rest restates the cited artifacts.

## Revalidation

- **Probe.** Run `python3 -B support/verify_cheri_capability_algebra.py` and compare with `support/expected_output.txt`. Counts in sampled groups depend on the interpreter's `random` module; the pass/fail meaning does not. For the full upstream comparison, fetch `test/contrib/setbounds_inputs_128.cpp` at the pinned `cheri-compressed-cap` revision and pass it with `--upstream-vectors`.
- **Encoding drift.** Diff `setCapBounds`, `getCapBoundsBits`, and `fastRepCheck` in `src/cheri_cap_common.sail` and the constants `cap_mantissa_width`, `cap_E_width`, `internal_E_take_bits` in `src/cheri_prelude_128.sail` and `cheri_prelude_64.sail`. Any change invalidates Sections 2.1 and 3 and the probe's `CCFormat`. A ratified RISC-V CHERI encoding must be re-derived, not assumed.
- **Tag-clear versus trap.** Count `clearTagIf` uses against `handle_cheri_cap_exception` in the capability-manipulation clauses of `src/cheri_insts.sail`.
- **ABI rules.** Check the `word` typedef in cheribsd `lib/libc/string/bcopy.c`, `cheri_revoke_epoch_clears` in `sys/cheri/revoke.h`, and in the guide whether sub-object bounds are still off by default and ambiguous `uintptr_t` arithmetic still selects the left operand (the guide says both may change).
- **CHERIoT & existential sealing.** Re-read "Temporal safety", "Sealed capabilities", and "Capability bounds" in `archdoc/chap-cheri-riscv.tex`, `setCapBounds` and `CSeal`/`CUnseal` in `cheriot-sail` (`src/cheri_cap_common.sail`, `src/cheri_insts.sail`), `zero_stack` in `sdk/core/switcher/entry.S`, and `CheriSealTypeAllocator`/`TokenObjectHeader` plus `.Ltoken_unseal_internal` in `sdk/core/allocator/token.h` and `sdk/core/token_library/token_unseal.S`.
- **Mill SASOS & CHERI-DMA.** If Mill Computing publishes RTL, a simulator, or an ISA manual, re-verify WKR/PLB/TLB placement, portal call cycle counts, and `PASS`/`GRANT`/`RELAY`/`PERSIST` guard-bit semantics against executable traces rather than patents. For CHERI-DMA, check downstream FPGA/ASIC CLUT or Arm Morello SMMU/IOMMU measurements against the analytical bounds in Section 11.2.
- **Provenance comparison.** Re-read the strict and exposed provenance text of `library/core/src/ptr/mod.rs` and search MiniRust's `spec/` for a CHERI memory model; a Rust CHERI target or such a model would change Section 6, items 2–4.
- **History.** The historical sources are fixed; the open work is reading Levy Chapters 4, 8, 9, and 10, the two CHERI reports named under Boundaries, and the full PDFs of Baker et al. (1987) and Lonergan & King (1961).
