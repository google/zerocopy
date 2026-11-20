# Where finite registers and frame sizes enter space semantics: CakeML, CompCert variants, GCC IRA/LRA, regalloc2, and SSA spilling

## Summary

- **Every verified compiler examined that proves an end-to-end space guarantee uses the same architecture.** CakeML's space cost semantics, Quantitative CompCert (Carbonneaux et al., PLDI 2014), and CompCertS all parameterize a high-level semantics with a **per-function frame-size map that the compiler itself produces after register allocation**. None of them charges register spills or callee-save slots directly in the source semantics. Basis: source + documentation.
- **The finite register count enters CakeML in exactly one place.** That place is `compute_stack_frame_sizes`, which uses `reg_count = c.reg_count - LENGTH c.avoid_regs - 5`. The CakeML intermediate meter charges **zero heap** for small integers and code pointers (`size_of lims [Number i] = 0` when `small_num`). Live immediates therefore show up only through the compiler-supplied frame size of their function. Basis: source.
- **Mainline CompCert has no memory bound.** It models infinite memory: `Mem.alloc` "never fails". Its only physical frame check is `fe_size <= Ptrofs.max_unsigned`, which raises the error "Too many spilled variables, stack size exceeded". Its frame-size computation `Bounds.function_bounds` is a high-water mark over the stack-slot offsets that the untrusted OCaml allocator assigned. Basis: source.
- **Production allocators share spill slots heuristically.**
  - GCC LRA and CompCert's IRC both assign spill slots first-fit: a spilled value reuses a slot whose occupants it does not conflict with.
  - regalloc2 tests each existing slot against the *aggregate hull* of a spill set's live ranges and probes at most `MAX_ATTEMPTS = 10` existing slots. Its own source comment calls the hull pessimistic for fragmented bundles.
  - So `num_spillslots` and the frame sizes these allocators report are upper bounds. None of them is a minimum.

  Basis: source.
- **Measurements on gcc 15.2.0 for x86-64 (Debian 15.2.0-14), with synthetic functions that keep exactly N 64-bit values simultaneously live:**
  - With `-O2 -mno-red-zone`, the frame equals return address + 6 callee-save pushes + **8·(N−14) spill bytes for every 15 ≤ N ≤ 512**.
  - With the default red zone, leaf-function spills land below `%rsp` and `-fstack-usage` does not count them (N = 24: reported 56 B, versus 136 B with `-mno-red-zone`).
  - `-O0` frames (no red zone) are 16·⌊N/2⌋ + 40 bytes, one slot per source variable rounded to 16-byte pairs. Naive per-variable counting therefore matches `-O0` and not optimized code.
  - Spill-slot sharing across two disjoint groups of 32 live values gives 216 B versus 368 B when `-fno-ira-share-spill-slots` is passed.

  Basis: execution on the real gcc, with synthetic inputs.
- **Choice of meter formulation.** A physically grounded source space meter can be:
  - (F1) direct source-level register-file metering;
  - (F2) a platform-parameterized high-water mark filled in from a compiler oracle;
  - (F3) pass-by-pass refinement of a stack bound.

  The verified systems use F2, with F3-style per-pass obligations inside the proof. F1 is not adopted by any examined verified compiler. F1 is well defined only after optimization and SSA construction: register pressure is a property of the optimized program, and k-colourability of an SSA interference graph is equivalent to maxlive ≤ k (Hack–Grund–Goos), whereas any real allocator may exceed that bound. In the measurements here gcc used one more slot than that bound. Basis: derived.

## Applicability

- **Subjects and how they relate.**
  - **Primary source-level subjects.** These are read at the pinned revisions in `REPORT.json`:
    - the CakeML compiler backend;
    - the CompCert back end;
    - GCC's register allocator and stack-layout code (trunk, compared against the 15.2.0 release);
    - regalloc2.
  - **Papers.** The three papers listed as subjects were read as primary descriptions of designs whose code was not inspected here:
    - the CakeML space cost semantics paper;
    - Quantitative CompCert;
    - CompCertS.

    Quantitative CompCert and CompCertS are forks of older CompCert versions: CompCert 1.13 for Quantitative CompCert, and a Coq 8.4 development for CompCertS. **Neither fork's code was inspected.** Claims about them have basis *documentation* (the papers), not source.
  - **Executed compiler.** The Debian `gcc-15` 15.2.0-14 binary is the only executed compiler. The GCC trunk revision is a source subject. For the three functions that determine the probed behaviour, the bodies of `assign_stack_slot_num_and_sort_pseudos` and `partition_stack_vars` are byte-identical between the trunk revision and `releases/gcc-15.2.0`. `output_stack_usage_1` differs: trunk adds a column to the `.su` output (see Findings §2.1).
- **Host for the measurements.** x86-64 Linux, Intel Xeon @ 2.60 GHz, 96 logical CPUs, about 236 GiB RAM, System V AMD64 ABI. The measured frame sizes are specific to the System V AMD64 ABI:
  - 15 allocatable general-purpose registers;
  - 6 callee-saved registers (`rbx`, `rbp`, `r12`–`r15`);
  - a 128-byte red zone.

  They do **not** transfer to Windows x64 (no red zone), AArch64 (31 GPRs), or 32-bit targets.
- **Probe inputs are synthetic.** The probe programs are synthetic C functions designed to fix maxlive at N. The frame sizes are real gcc behaviour **on those inputs**. They are not a claim about frame sizes of real-world code.
- **Scope.**
  - In scope: stack frames, register spills, callee-save areas and spill-slot sharing, and how each verified semantics meters them.
  - Heap accounting: CakeML's `size_of_heap`/`peak_heap_length` is described only where it bears on immediates. Garbage-collector space safety is covered only as context.

## Findings

### 1. Verified compilers: where stack space is charged and where the register count enters

Basis for this section: source (CakeML, CompCert) + documentation (the three papers).

| System | Level of the space meter | Cost of a live immediate in the meter | Where spills and callee-saves are paid | Origin of frame sizes | Where the finite register count enters | Out-of-memory behaviour in the semantics | End-to-end statement |
|---|---|---|---|---|---|---|---|
| CakeML (pinned) | dataLang (first-order IL, after closure conversion; not source CakeML) | 0 heap words for `small_num` integers and `CodePtr` (`size_of`) | Inside the per-function frame size `stack_frame_sizes` | `compute_stack_frame_sizes asm_conf word_prog`, computed from the **compiled** wordLang program | `reg_count = c.reg_count - LENGTH c.avoid_regs - 5` in `compute_stack_frame_sizes`, and the same `k` in `word_to_stack$compile_def` | stackLang `StackAlloc n` with `stack_space < n` halts with `Halt (Word 2w)`: an observable early exit, not undefined behaviour | `compile_correct_is_safe_for_space`: if `is_safe_for_space` holds then `machine_sem ⊆ semantics_prog` |
| CompCert mainline (pinned) | None (memory is infinite) | n/a | Mach frames sized by `Stacklayout.make_env (function_bounds f)` | `Bounds.function_bounds`: maximum over the `Local`/`Outgoing` slot offsets that appear in the Linear code | Implicitly, through the allocator's choice of registers versus `S Local` slots (untrusted OCaml `IRC.ml`, validated by `Allocation.v`) | `Mem.alloc` never fails; the only check is `fe_size <= Ptrofs.max_unsigned` at compile time | Forward simulation with no space component |
| Quantitative CompCert (paper) | Clight and every intermediate language, via call/return events weighted by a metric M | not examined | Folded into the per-function M(f) | "During compilation the compiler produces a specific cost metric" M0; Mach syntax carries a finite map SF giving SF(f) bytes per call | Through M0, after allocation | New x86 assembly `ASMsz` with a finite stack | Compiled traces have weight ≤ source weight under M0, and the program runs on a stack of the computed size |
| CompCertS (paper) | C through Linear, instrumented with a per-function oracle `ns` | not examined | The oracle `ns` "specifies, for each function f, the additional space that is needed"; space is reserved at entry and released at exit | Built "as a byproduct of the compilation" during Stacking | Through `ns` | Allocation may fail, which is an observable going-wrong behaviour | Theorem 6: `bh' ∈ ASem(tp) ⇒ ∃ bh ∈ CSem(p, ns). bh ⊆ bh'` |

Details and quotations:

#### 1.1 CakeML

- **Meter state.** `dataSemScript.sml` defines `limits = <| heap_limit; length_limit; stack_limit; arch_64_bit; ... |>`. The state carries:
  - `locals_size : num option` — "size of locals when pushed to stack, NONE if unbounded";
  - `stack_max : num option`;
  - `stack_frame_sizes : num num_map` — "stack frame sizes, unbounded if unmapped";
  - `safe_for_space : bool`;
  - `peak_heap_length`.

  On a call, `call_env args size s` updates `stack_max := MAX s.stack_max (size_of_stack s.stack + size)` and conjoins `stack_limit > new_stack_max` into `safe_for_space`. The `size` comes from `find_code`, which returns `lookup p ssize`, the frame size of the callee.
- **Immediates.** `size_of lims [Number i] = (if small_num lims.arch_64_bit i then 0 else bignum_size ...)` and `size_of lims [CodePtr _] = 0`. The paper states: "Small numbers are stored within their containing block or stack frame, and hence they have heap size 0." Their stack cost exists only inside the opaque per-function frame size.
- **Frame sizes come from the compiled program.** The backend correctness proof defines
  ```
  compute_stack_frame_sizes c word_prog =
    let reg_count = c.reg_count - LENGTH c.avoid_regs - 5 in
      mapi (λn (arg_count,prog,md).
              let stack_arg_count = arg_count - reg_count ;
                  stack_var_count = MAX (max_var (isa_bits c) prog DIV 2 + 1 - reg_count) stack_arg_count ;
              in if stack_var_count = 0 then 0 else stack_var_count + 1)
        (fromAList (word_prog))
  ```
  `compute_stack_frame_sizes_thm` proves it equal to the frame size returned by `word_to_stack$compile_prog`. `is_safe_for_space` evaluates `data_lang_safe_for_space` with this map, where `word_prog = SND (to_word asm_conf c prog)` is the register-allocated wordLang program.
- **Register model.** In `word_to_stackScript.sml`:
  - the comment reads "Here k = number of registers"; another reads "stack args are in wordLang vars 0,2,4,...,2*(k-1), 2*k , ..." and "2*k and above are 'stack' variables";
  - `compile_def` sets `let k = asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs)`;
  - the frame is `stack_var_count + 1` words; the extra word is for the garbage-collector bitmap pointer.

  Register allocation (`word_allocScript.sml`, choice of simple, IRC, or linear-scan allocator) colours variables. Variables coloured at or above `2*k` become stack slots, so slot sharing between non-interfering spilled variables is a by-product of graph colouring.
- **Out-of-stack is observable.** stackLang `evaluate (StackAlloc n,s) = if s.stack_space < n then (SOME (Halt (Word 2w)),empty_env s) else ...`. The machine stack is a concrete bounded region.
- **Proof and authoring effort, from the paper.**
  - "Each of the examples took us on the order of 8-12 person-days to complete, except reverse which took around 4 person-hours. The proof scripts are often 1000 lines or more … for programs no longer than ∼20 lines of CakeML."
  - The dataLang-to-wordLang simulation "builds on some 35,000 lines of invariant definitions and proofs", all of which were updated.
  - Stated limitation: "making it convenient for CakeML users is future work".

#### 1.2 CompCert mainline

- **Infinite memory.** `common/Memory.v`: "Note that allocation never fails: we model an infinite memory." `Program Definition alloc (m: mem) (lo hi: Z)` is total.
- **Frame entry.** Mach `exec_function_internal` performs `Mem.alloc m 0 f.(fn_stacksize) = (m1, stk)`, where `fn_stacksize = fe_size` from Stacking.
- **Frame layout.** `x86/Stacklayout.v` `make_env`, from low to high addresses:
  1. outgoing arguments, `4 * bound_outgoing`;
  2. the back link;
  3. callee-saves (`size_callee_save_area b ocs`);
  4. locals, `4 * bound_local`, aligned to 8;
  5. stack data, `bound_stack_data`;
  6. the return address.

  `fe_size = oretaddr + w`.
- **Bounds.** `backend/Bounds.v`: `bound_local := max_over_slots_of_funct local_slot`, where `local_slot (Local, ofs, ty) = ofs + typesize ty`. `used_callee_save := RegSet.elements record_regs_of_function`. The bound is a **high-water mark of slot offsets**, not a count of spilled variables. Sharing is whatever the allocator chose.
- **Allocator (untrusted).** `backend/IRC.ml` `assign_color` works in three steps:
  1. try a register;
  2. otherwise try `reuse_slot`, which reuses a preferred move-partner's `S(Local,…)` slot "provided no conflict occurs";
  3. otherwise `find_slot`: "assign lowest nonconflicting stack slot", a first-fit scan over conflicting slots sorted by offset.
- **Compile-time check.** `backend/Stacking.v` `transf_function` returns `Error (msg "Too many spilled variables, stack size exceeded")` when `Ptrofs.max_unsigned < fe.(fe_size)`. The comment explains that the check prevents overflow of unsigned offset arithmetic. It is not a resource bound.

#### 1.3 Quantitative CompCert (paper only)

- **Mechanism.** It "extend[s] event traces with events for function calls and returns and define[s] a weight for event traces". "During compilation the compiler produces a specific cost metric that guarantees that the weight of an event trace under this metric is an upper bound on the stack-space usage of the compiled assembly program." Compiled traces may reorder or delete call/return events "as long as the weight of the trace is reduced or unchanged".
- **Size of the change.** "about 5000 lines of Coq code that we integrated into CompCert 1.13 (which originally consists of about 90000 lines of Coq code)".
- **Limitations stated in the paper.**
  - No variable-length arrays or `alloca`.
  - "Quantitative CompCert currently does not support … tail-call recognition and function inlining."
- **Precision.** "both the manually and automatically derived bounds over-approximate the stack usage by exactly four bytes" on the paper's benchmark set, described as more than 3000 lines of C from CertiKOS, MiBench and CompCert test programs.

#### 1.4 CompCertS (paper only)

- **Mechanism.** "we parameterise the semantics of all intermediate languages, from C to Linear, with an oracle ns which specifies, for each function f, the additional space that is needed. The semantics therefore include special operations that reserve some space at function entry and release it at function exit." Correctness condition: "The oracle ns is correct if the amount of boxes that is reserved is sufficient to hold this extra space in Mach."
- **Why the oracle comes from the compiler.** "it seems unlikely that the impact of register allocation could be modelled accurately. Instead, as the exact amount of additional memory space is known during the Stacking pass, we construct the oracle ns as a byproduct of the compilation … the construction is not circular since the oracle is only needed for the correctness proof of the compiler and not by the compiler itself."

#### 1.5 CerCo

- CerCo's overview paper (FOPARA 2013, LNCS 8552) describes a verified C compiler that emits a cost-annotated copy of the source program for source-level cost reasoning.
- **How CerCo treats stack frames or spills was not examined at primary-source level** (see Boundaries).

**Convergent invariant (derived).** In the three systems whose mechanism was read, the source-level claim is *parametric* in a function `M : fn → bytes` (CakeML `ss`, Quantitative CompCert M, CompCertS `ns`). The compiler instantiates M after register allocation. The space theorem then holds for that instance. The register count is never a parameter of the source semantics itself.

### 2. Production allocators: register pressure, spill-slot sharing and frame reporting

Basis for this section: source + execution.

#### 2.1 GCC

- **Pressure accounting.** `ira-lives.cc` `inc_register_pressure` raises `curr_reg_pressure[cl]` for every pressure class. It records `high_pressure_start_point[cl]` once `curr_reg_pressure[cl] > ira_class_hard_regs_num[cl]` and keeps a per-region maximum `reg_pressure[cl]` (declared in `ira-int.h` as "Maximal register pressure inside loop for given register class"). `ira-build.cc` refuses to treat a loop as a low-pressure region when `node->reg_pressure[pclass] > ira_class_hard_regs_num[pclass]`. The bounded register file is therefore the per-class constant `ira_class_hard_regs_num`.
- **Spill-slot sharing in LRA.** The header of `lra-spills.cc` gives the algorithm: "for all spilled pseudos P most frequently used first do / for all stack slots S do / if P doesn't conflict with pseudos assigned to S then assign S to P … create new stack slot S and assign P to S". In `assign_stack_slot_num_and_sort_pseudos`:
  - `if (! flag_ira_share_spill_slots) j = slots_num;` gives every pseudo a fresh slot when sharing is off;
  - otherwise a slot is shared when `! lra_intersected_live_ranges_p (slots[j].live_ranges, lra_reg_info[regno].live_ranges)` holds and the size and alignment fit;
  - constant-width and variable-width modes are kept apart.
- **Source-variable stack sharing.** `cfgexpand.cc` `add_scope_conflicts` approximates the live range of an addressable stack variable "by taking the first mention of its name as starting point(s), and by the end-of-scope death clobber added by gimplify as ending point(s)". `partition_stack_vars` then greedily unions non-conflicting variables, largest first. This is the `-fstack-reuse` machinery. It acts on *source-level* lexical scopes, not on register pressure.
- **Reporting.**
  - `toplev.cc` `output_stack_usage_1` reports `current_function_static_stack_size`, labelled `static`, `dynamic` or `dynamic,bounded`. It adds pushed-argument space and dynamic allocation.
  - It is a **per-function** figure; summing along call paths is left to the user, for example through callgraph information.
  - Format difference: the trunk revision prints an extra tab-separated `PRINT_DECL_UNIQUE_NAME` column before the byte count, which 15.2.0 does not. Scripts that read field 2 of `.su` lines must be adjusted for trunk.

#### 2.2 regalloc2

- **Register-file model.** `MachineEnv` lists `preferred_regs_by_class: [PRegSet; 3]`, `non_preferred_regs_by_class`, an optional `scratch_by_class`, and `fixed_stack_slots`. If no scratch register is given, "the register allocator will automatically allocate one as needed, spilling a value to the stack if necessary". Cyclic parallel moves can therefore cost a spill that is invisible at source level.
- **Slot allocation.** `src/ion/spill.rs` `allocate_spillslots`:
  - `const MAX_ATTEMPTS: usize = 10;`
  - for each required spill set, probe up to `min(slots.len(), MAX_ATTEMPTS)` existing slots of the class, starting at `probe_start`, and accept the first for which `spillslot_can_fit_spillset` holds; otherwise push a new slot.
  - `spillslot_can_fit_spillset` tests the slot's B-tree for overlap with `LiveRangeKey::from_range(&spillsets[ss].range)`.
- **Pessimistic hull.** `SpillSet.range` is documented in `data_structures.rs`: "The aggregate CodeRange of all involved LiveRanges … For fragmented bundles with lots of open space this abstraction is pessimistic."
- **Reported count.** `Output::num_spillslots` is documented as "How many spillslots are needed in the frame?" Because of the probe cap and the hull, it can exceed the minimum colouring of the spill sets (derived; not measured here).
- **Splitting cap.** `MAX_SPLITS_PER_SPILLSET: u8 = 2` caps live-range splitting before the allocator falls back to "minimal bundles" with a spill bundle (`process.rs`).

#### 2.3 SSA spilling theory

- **Chordality.** Hack, Grund and Goos (CC 2006, LNCS 3923, pp. 247–262) show that interference graphs of strict SSA programs are chordal. Colouring is therefore polynomial, and the chromatic number equals maxlive.
- **Consequence for the meter (derived).** For SSA programs, "spill until maxlive ≤ k at every point" is necessary and sufficient for k registers before coalescing and precolouring. A meter of the form Σ max(0, maxlive − k) is therefore exact for a perfect SSA allocator, and only for that allocator.
- **Spilling heuristic.** Braun and Hack (CC 2009, LNCS 5501, pp. 174–189) generalize Belady's furthest-next-use (MIN) heuristic from basic blocks to CFGs, with live-range splitting. Their reported reductions of dynamic loads and stores relative to linear-scan and graph-colouring allocators (CINT2000, x86) are quoted from a search-engine summary of the paper and were not checked against the paper text.
- **Spill-slot colouring** in those papers was not examined.

### 3. Measured gcc frame sizes versus number of simultaneously live scalars

Basis: execution of the real gcc 15.2.0 on synthetic inputs (the generator and script are listed under Revalidation).

The probe works as follows:

- `liveN` loads N `unsigned long` values through a `volatile` pointer, which fixes the load order.
- It then folds them with the non-associative chain `r = (r * 31u) ^ x_i`, which starts from the last value loaded.
- All N values are therefore live after the last load.

Values in bytes are taken from `-fstack-usage`. The "rsp stores" column counts `mov reg, off(%rsp)` instructions in the default (red-zone) `-O2` assembly.

| N | -O0 | -O2 | -O0 -mno-red-zone | -O2 -mno-red-zone | rsp stores (-O2) | pushes (-O2) |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 16 | 8 | 72 | 8 | 0 | 0 |
| 8 | 16 | 16 | 104 | 16 | 0 | 1 |
| 12 | 16 | 48 | 136 | 48 | 0 | 5 |
| 13 | 16 | 48 | 136 | 48 | 0 | 5 |
| 14 | 32 | 56 | 152 | 56 | 0 | 6 |
| 15 | 32 | 56 | 152 | 64 | 1 | 6 |
| 16 | 48 | 56 | 168 | 72 | 2 | 6 |
| 17 | 48 | 56 | 168 | 80 | 3 | 6 |
| 20 | 80 | 56 | 200 | 104 | 6 | 6 |
| 24 | 112 | 56 | 232 | 136 | 10 | 6 |
| 32 | 176 | 80 | 296 | 200 | 18 | 6 |
| 64 | 432 | 336 | 552 | 456 | 50 | 6 |
| 512 | – | – | – | 4040 | – | – |

Derived readings of the table:

- **`-O2 -mno-red-zone` frame = 8 (return address) + 8·pushes + 8·max(0, N − 14).** The table rows for 15 ≤ N ≤ 64 fit this formula exactly, and so does N = 512 (56 + 8·498 = 4040).
  - The default-red-zone column agrees: rsp stores = N − 14 for 15 ≤ N ≤ 64.
  - x86-64 has 15 allocatable GPRs, so a perfect SSA allocator would need N − 15 slots (the volatile base pointer dies at the last load). On this input gcc uses **one slot more than the chordal lower bound**.
  - A source meter that assumes "k = 15 free registers" would under-count this compiler by one slot. One that assumes "k = 14" happens to match it on this input only.
- **Callee-saved registers are a step function.** They are pushed as soon as more than the caller-saved registers are needed. N = 12 already costs 5 pushes (40 B), and pressure saturates at 6 pushes (48 B) by N = 14. This cost is paid before any spill happens.
- **The red zone hides leaf spills from `-fstack-usage`.** With the default ABI, `-O2` reports 56 B for every N from 14 to 24, while the spills move to negative `%rsp` offsets (for example `movq %rsi, -72(%rsp)`). The System V AMD64 psABI §3.2.2 reserves "the 128-byte area beyond the location pointed to by %rsp" for this purpose; leaf functions "may use this area for their entire stack frame". A whole-program stack bound computed from `.su` files must therefore add up to 128 B for the deepest leaf on this ABI. Basis: execution + normative (ABI text as quoted in a search result; the ABI document itself was not fetched).
- **`-O0` frames grow by one 8-byte slot per source variable.** With `-mno-red-zone` they equal 16·⌊N/2⌋ + 40 bytes for every N in the table (72 → 552 for N = 4 → 64; odd N pads to the next 16-byte pair). There is no reuse. Optimized frames are not monotone in source-variable count in this way. N = 14 and N = 4 differ by 48 B at `-O2` but by 80 B at `-O0`.

**Spill-slot sharing across two disjoint groups of N live values**, from `twoN`, in which the first group is dead before the second is loaded:

| N | sharing on | sharing off | liveN alone | sharing on, no red zone | sharing off, no red zone |
|---:|---:|---:|---:|---:|---:|
| 20 | 56 | 56 | 56 | 120 | 176 |
| 32 | 96 | 248 | 80 | 216 | 368 |
| 64 | 352 | 760 | 336 | 472 | 880 |

- With sharing on (the default), the frame is within 16 B of a single group.
- With sharing off, it is 1.7–1.9× the single-group frame (no-red-zone columns).

**Source-level array reuse** (`scopes.c`, two `char[256]` arrays in disjoint `if`/`else` scopes):

| Flags | Frame | Kind |
|---|---:|---|
| `-O2 -fstack-reuse=all` | 272 B | static |
| `-O2 -fstack-reuse=none` | 528 B | static |
| `-O0` | 288 B | static |

So scope-based partitioning is active at `-O0` as well on this input. In the same file:

- a VLA is reported as `dynamic`;
- `__builtin_alloca(c ? 64 : 32)` is reported as `dynamic`, not `dynamic,bounded`.

Toolchain cost on the same host, measured with `/usr/bin/time`:

| Input | gcc -O2 wall time | Max RSS |
|---|---:|---:|
| `live64.c` | 0.09 s | 27 108 KB |
| `two64.c` | 0.13 s | 28 688 KB |
| `live512.c` | 0.54 s | 36 384 KB |
| Whole probe script (≈ 90 compiler invocations) | 2.76 s | – |

### 4. Why source-level live-variable counts are not a sound proxy for machine stack

Each item is labelled with its basis.

1. **Callee-save areas are charged before spilling begins**, and their size depends on which registers were used. Examples: the step from 0 to 48 B in §3; CompCert's `used_callee_save` from `record_regs_of_function`. Basis: execution + source.
2. **Allocator suboptimality.** In §3 gcc used N − 14 slots against a chordal bound of N − 15. regalloc2's hull and 10-probe cap can over-allocate. Basis: execution + source.
3. **ABI artefacts.** Several layout costs come from the ABI rather than from the program:
   - the red zone (§3);
   - outgoing-argument areas (CompCert `bound_outgoing`; GCC pushed-argument space);
   - the Win64 32-byte shadow area (`fe_ofs_arg := if Archi.win64 then 32 else 0` in CompCert);
   - return-address and back-link words;
   - alignment padding (`align … 8` in `make_env`).

   Basis: source.
4. **Parallel moves and scratch registers** (regalloc2 `scratch_by_class`) can force a spill with no source counterpart. Basis: source.
5. **Optimizations change liveness.**
   - Common-subexpression elimination and loop-invariant code motion lengthen live ranges.
   - Rematerialization and dead-code elimination shorten them.
   - Inlining merges frames: two sequential callees whose frames would each be popped become one frame sized to the larger live set, plus any values live across the former call boundary.
   - Tail calls delete frames. Quantitative CompCert disabled both inlining and tail calls for this reason, at the time of the paper.

   Basis: derived + documentation. Not measured here.
6. **Optimization level.** The `-O0` frame grows linearly with the number of source variables (16·⌊N/2⌋ + 40 B on this probe). The `-O2` frame depends on maxlive relative to the register file. A source meter calibrated against unoptimized code over-counts by up to N·8 B, for example 552 B versus 456 B at N = 64 without the red zone. Basis: execution.

### 5. Three candidate formulations of a physically grounded source space meter

Let R be the number of allocatable registers of a class, w the slot width, and C the callee-save cost of a function.

- **F1 — direct source-level register-file metering.** The source semantics charges `w·max(0, live_scalars(p) − R) + C` at every program point p, using source liveness.
- **F2 — platform-parameterized high-water mark.** The source semantics is parametric in `M : fn → bytes` and charges M(f) per activation, plus heap. The compiler emits M and the theorem is stated for that M. This is what CakeML, Quantitative CompCert and CompCertS do.
- **F3 — pass-level stack-bound refinement.** Every pass is proved to preserve or decrease a weighted cost. Examples: Quantitative CompCert's per-pass "weight non-increase" lemmas over call/return events; CompCertS's reservation sufficiency at Stacking.

| Transformation | F1 (source-level register metering) | F2 (compiler-emitted M) | F3 (per-pass refinement) |
|---|---|---|---|
| CSE / GVN, LICM (lengthen live ranges) | **Constrained.** Must prove pressure non-increase, or forbid. | Admitted. M grows and the source proof stays parametric. | Pass must prove that weight does not increase, or pay through reservation. |
| Rematerialization, DCE (shorten ranges) | Admitted. The meter over-approximates. | Admitted | Admitted |
| Register allocation heuristics (IRC, linear scan, regalloc2) | **Constrained.** The meter is sound only if the allocator meets `maxlive − R`; real allocators did not (§3), so a slack term or a verified-optimal allocator is needed. | Admitted. The allocator's actual result defines M. | Admitted if Stacking checks reservation sufficiency (CompCertS) |
| Inlining | Requires re-metering the merged body | Admitted. M(caller) grows. | **Constrained.** Was unsupported in Quantitative CompCert. |
| Tail-call elimination | Meter must model frame reuse | Admitted, provided the source semantics models the deleted frame. Otherwise the bound is merely loose. | **Constrained.** Was unsupported in Quantitative CompCert. Needs event reordering or deletion lemmas. |
| Spill-slot sharing / stack colouring | Implicitly assumed perfect | Admitted. Whatever sharing occurs lowers M. | Admitted |
| Callee-save shrink-wrapping | Must be modelled in C | Admitted | Admitted |
| VLA / `alloca` | Unsupported unless bounded | Unsupported in all three verified systems (dynamic frames) | Unsupported |

Derived trade-offs:

- **Where the human writes numbers.**
  - F1 lets a source author compute a concrete byte bound before compilation, but couples the meter to every optimization.
  - F2 makes the *proof* independent of optimizations, but concrete numbers are only known after compilation. Source proofs must stay symbolic in M(f), or be re-instantiated per build. The CakeML paper's examples show concrete instances, such as "56 words of stack and 89 words of heap".
  - F3 is where verified compilers place the engineering cost: about 5000 Coq lines for Quantitative CompCert; 12 back-end passes re-proved for CompCertS.
- **Live immediates in the meter.** A source meter that charges zero bytes for simultaneously live immediates is equivalent to F1 with R = ∞. Under F2 that is harmless: CakeML charges small integers 0 heap, and their stack residence is inside M. Under F1 it is unsound for any physical machine once maxlive exceeds R.

### 6. Performance and resource footprint (L1–L6)

| Level | CakeML space semantics | CompCert mainline | Quantitative CompCert | CompCertS | gcc 15.2.0 | regalloc2 |
|---|---|---|---|---|---|---|
| L1 authoring | 8–12 person-days per example of ≤ 20 lines, proofs often ≥ 1000 lines; ~35 000 lines of simulation invariants updated (paper) | not measured | ~5000 Coq lines added to ~90 000 (paper) | 12 back-end passes re-proved (companion page); line count not measured | n/a | n/a |
| L2 toolchain build | not measured | not measured | not measured | "about 30 minutes" to compile the development (companion page) | not measured | not measured |
| L3 compile latency | not measured | not measured | not measured | not measured | 0.09 s (N=64), 0.54 s (N=512) per `-O2` compile (measured) | not measured |
| L4 generated code | not measured | not measured | not measured | not measured | Spill stores grow N − 14 (measured instruction count; runtime cycles not measured) | not measured |
| L5 proof checking | not measured | not measured | not measured | not measured | n/a | n/a |
| L6 footprint | Example bounds such as 56 words of stack and 78–108 words of heap (paper) | Frame = `make_env` layout | Bounds over-approximate actual stack by exactly 4 B (paper) | not measured | Frames in §3; compiler max RSS 27–36 MB (measured) | `num_spillslots` (not measured) |

### 7. Comprehensibility and simplicity (C1, C2)

- **C1 (human).**
  - F2 makes one concept local: "a function costs M(f) per activation". The source author reasons about recursion depth times M only.
  - The price is a non-local dependency, since M is produced by a compiler run. A human auditor must trust or check the emitted map.
  - The CakeML statement keeps the dependency visible: `is_safe_for_space` literally calls `compute_stack_frame_sizes asm_conf word_prog`.
  - The red-zone discrepancy (§3) is the kind of hidden footgun that a reader of `.su` files would not anticipate.
- **C2 (simplicity).**
  - The three verified systems invented three names for one abstraction: CakeML `stack_frame_sizes`, Quantitative CompCert's metric M, CompCertS's `ns`. All three are a compiler-emitted per-function cost map plus a monotone accumulator (`stack_max`, trace weight, reserved boxes).
  - The distinctions between them are realization quirks: event trace versus state field versus reservation operation. They do not differ in the semantic invariant.
  - Making the register count a source-level parameter (F1) would add a second mechanism enforcing the same invariant that M already enforces.

### 8. Validation (V1–V4)

- **V1 (specification adequacy).**
  - Quantitative CompCert compared verified bounds with measured stack usage; the gap was exactly 4 B on its benchmark set.
  - The CakeML paper validates by proving concrete instances.
  - No mutation testing of space specifications was found in the examined material (not examined further).
- **V2 (compiler differential testing).** No differential or metamorphic testing of frame-size output (Csmith- or YARPGen-style against `-fstack-usage`) was found or performed. This report's gcc probe is a small, targeted differential run across flags: `-O0`/`-O2`, red zone on and off, sharing on and off.
- **V3 (physical validation)** — not applicable to stack accounting except for **signal and interrupt stacks**. The red-zone rule exists because asynchronous handlers must not clobber below-`%rsp` data. Kernels compile with `-mno-red-zone`, and a bound computed with the red zone is wrong in that context (derived from the ABI rule; not examined in kernel sources).
- **V4 (field replay, human mental models)** — not examined.

## Boundaries

- **Not examined.**
  - CerCo's handling of stack frames or spills (only the overview paper was consulted).
  - The source code of Quantitative CompCert and CompCertS: claims rest on their papers.
  - LLVM's register allocators and `-fstack-size-section`.
  - Interprocedural stack bounding tools (GCC callgraph information, `-Wstack-usage` thresholds).
  - regalloc2 *execution* (no allocator runs were made, so its over-allocation is a derived possibility, not a measurement).
  - CakeML and CompCert execution.
  - AArch64, RISC-V, 32-bit x86 and Windows x64 ABIs.
  - Spill-slot colouring in the Braun–Hack and Hack–Grund–Goos papers.
  - Energy and power draw.
  - How CakeML's `word_alloc` linear-scan option affects frame size.
- **Unknown.**
  - Whether gcc's one-slot excess over the chordal bound (N − 14 versus N − 15) persists on other code shapes or other gcc versions.
  - Whether it comes from the base-pointer register, from LRA's slot-number assignment, or from IRA's pressure classes. The probe does not discriminate between these.
- **Known not to apply.**
  - Mainline CompCert's theorem says nothing about stack overflow (infinite memory). Any claim of a "CompCert stack bound" refers to the Quantitative CompCert or CompCertS forks.
  - The `-O0` frame model (16·⌊N/2⌋ + 40) does not predict optimized frames.
- **Unsupported.** Variable-sized frames (VLAs, `alloca`) in all three verified systems.
- **Stronger conclusions this evidence does not establish.**
  - That F2 is the *only* workable formulation; F1 with a verified allocator achieving the chordal bound has not been built, as far as this investigation found.
  - That regalloc2 produces larger frames than gcc on real code.
  - That the measured byte counts characterise real programs: the inputs are synthetic.
  - That a source calculus *should* or *should not* meter live immediates. This report documents how existing systems place the cost; it does not decide a language design.

## Evidence

All observations were made on 2026-11-20 (UTC).

**CakeML/cakeml @ 2874b664e10939a3ee462215b2e068c89c1f70eb**

| Path | Lines | Content |
|---|---|---|
| `compiler/backend/semantics/dataSemScript.sml` | 42–50 | `limits` |
| same | 53–74 | `state`, including `locals_size`, `stack_max`, `stack_frame_sizes`, `safe_for_space`, `peak_heap_length` |
| same | 94–98 | `small_num_def` |
| same | 112–121 | `size_of_def`: `Number` 0 when small; `CodePtr` 0 |
| same | 451–466 | `size_of_stack_frame`, `size_of_stack`, `do_stack` |
| same | 1372–1383 | `call_env_def` |
| same | 1385–1401 | `push_env_def` |
| same | 1468–1475 | `find_code_def`, which returns the `lookup p ssize` frame size |
| same | 1792–1799 | `data_lang_safe_for_space_def` |
| `compiler/backend/semantics/wordSemScript.sml` | 245–251 | `locals_size`, `stack_limit`, `stack_max`, `stack_size` |
| same | 1514–1519 | `word_lang_safe_for_space_def` |
| `compiler/backend/word_to_stackScript.sml` | 1–8 | Header: "The most complicated part is the handling of spilled variables in conjunction with function calls" |
| same | 22–26 | Comment defining k, f, f' |
| same | 597–608 | `compile_prog_def` |
| same | 618–631 | `compile_def`, with `k = asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs)` |
| `compiler/backend/semantics/stackSemScript.sml` | 980–983 | `StackAlloc` halts with `Halt (Word 2w)` |
| `compiler/backend/proofs/backendProofScript.sml` | 2787–2795 | `compute_stack_frame_sizes_def` |
| same | 2797–2811 | `compute_stack_frame_sizes_thm` |
| same | 2819–2827 | `is_safe_for_space_def` |
| same | 5005–5016 | `compile_correct_is_safe_for_space` |
| `compiler/backend/word_allocScript.sml` | 1–8 | Allocator modes |

**AbsInt/CompCert @ 2685140bf72c959446981fb99b5e44a8975021bc**

| Path | Lines | Content |
|---|---|---|
| `common/Memory.v` | 343–357 | `alloc` and the "never fails … infinite memory" comment |
| `backend/Mach.v` | 398–406 | `exec_function_internal` performs `Mem.alloc m 0 f.(fn_stacksize)` |
| `backend/Bounds.v` | 36–45 | `Record bounds` |
| same | 130–157 | `slots_of_instr`, `local_slot`, `outgoing_slot`, `outgoing_space` |
| same | 225–229 | `function_bounds` |
| `x86/Stacklayout.v` | 22–49 | Layout comment and `make_env` |
| `backend/Stacking.v` | 188–217 | "Subtle point" frame-size comment and `transf_function` |
| `backend/IRC.ml` | 817–861 | `reuse_slot`, `find_slot` |
| same | 877–896 | `assign_color` |

**gcc-mirror/gcc @ 78dfcd5a2bc9beb9dc4398f7f747b9b242fd37b6 (trunk)**

| Path | Lines | Content |
|---|---|---|
| `gcc/lra-spills.cc` | 22–56 | Header algorithm |
| same | 399–450 | `assign_stack_slot_num_and_sort_pseudos`, including `if (! flag_ira_share_spill_slots)` at 409–410 and `lra_intersected_live_ranges_p` at 424–426 |
| `gcc/ira-lives.cc` | 210–236 | `inc_register_pressure` |
| `gcc/ira-int.h` | 123–125 | `reg_pressure` |
| `gcc/ira-build.cc` | 2223–2238 | `low_pressure_loop_node_p` |
| `gcc/cfgexpand.cc` | 951–975 | `add_scope_conflicts`; live-range comment at 966–974 |
| same | 1225–1239 | `partition_stack_vars` algorithm comment |
| `gcc/toplev.cc` | 779–850 | `output_stack_usage_1`; the `PRINT_DECL_UNIQUE_NAME` column is at 845–847 |

**gcc-mirror/gcc @ 5115c7e447fc07457443df874bf57840e8316d5f (releases/gcc-15.2.0)**

- The bodies of `assign_stack_slot_num_and_sort_pseudos` (`gcc/lra-spills.cc`, from line 362) and `partition_stack_vars` (`gcc/cfgexpand.cc`, from line 1230) are byte-identical to trunk.
- `output_stack_usage_1` (`gcc/toplev.cc`, from line 776) lacks the extra name column.

**bytecodealliance/regalloc2 @ 4eb655fa745fba271af74be8495154a4b0cac56f**

| Path | Lines | Content |
|---|---|---|
| `src/lib.rs` | 1320–1328 | `spillslot_size` |
| same | 1540–1580 | `MachineEnv` |
| same | 1586–1588 | `Output::num_spillslots` |
| `src/ion/spill.rs` | 70–150 | `spillslot_can_fit_spillset`, `allocate_spillset_to_spillslot`, `allocate_spillslots` with `MAX_ATTEMPTS = 10` |
| `src/ion/data_structures.rs` | 298–313 | `SpillSet` with the aggregate-range comment; `MAX_SPLITS_PER_SPILLSET = 2` |

**Literature.** DOIs were checked against bibliographic search results on 2026-11-20. Paper texts were read from the authors' or publishers' PDFs where noted.

- A. Gómez-Londoño, J. Åman Pohjola, H. T. Syeda, M. O. Myreen, Y. K. Tan. *Do You Have Space for Dessert? A Verified Space Cost Semantics for CakeML Programs.* OOPSLA 2020. DOI 10.1145/3428272. Text read from cakeml.org/oopsla20.pdf.
- Q. Carbonneaux, J. Hoffmann, T. Ramananandro, Z. Shao. *End-to-End Verification of Stack-Space Bounds for C Programs.* PLDI 2014, pp. 270–281. DOI 10.1145/2594291.2594301. Text read from flint.cs.yale.edu/certikos/publications/veristack.pdf.
- F. Besson, S. Blazy, P. Wilke. *CompCertS: A Memory-Aware Verified C Compiler Using a Pointer as Integer Semantics.* Journal of Automated Reasoning, 2019. DOI 10.1007/s10817-018-9496-y. Text read from the ResearchGate full-text page; companion page at cs.yale.edu/homes/wilke-pierre/itp17/.
- R. M. Amadio et al. *Certified Complexity (CerCo).* FOPARA 2013, LNCS 8552, pp. 1–18. DOI 10.1007/978-3-319-12466-7_1. Bibliographic metadata only.
- S. Hack, D. Grund, G. Goos. *Register Allocation for Programs in SSA-Form.* CC 2006, LNCS 3923, pp. 247–262. DOI 10.1007/11688817_17. Bibliographic and abstract-level only.
- M. Braun, S. Hack. *Register Spilling and Live-Range Splitting for SSA-Form Programs.* CC 2009, LNCS 5501, pp. 174–189. DOI 10.1007/978-3-642-00722-4_13. Abstract-level only.
- P. Briggs, K. D. Cooper, L. Torczon. *Improvements to Graph Coloring Register Allocation.* ACM TOPLAS 16(3):428–455, 1994. DOI 10.1145/177492.177575. Bibliographic only.
- W. D. Clinger. *Proper Tail Recursion and Space Efficiency.* PLDI 1998, pp. 174–185. DOI 10.1145/277650.277719. Bibliographic only.
- X. Leroy. *A Formally Verified Compiler Back-end.* Journal of Automated Reasoning, 2009. DOI 10.1007/s10817-009-9155-4. Bibliographic only.
- System V AMD64 psABI §3.2.2 "The Stack Frame": red-zone text as quoted in a search result. The ABI document itself was not fetched.

**Execution.**

- Host: x86-64 Linux, Intel Xeon @ 2.60 GHz, 96 logical CPUs.
- Compiler: `gcc (Debian 15.2.0-14) 15.2.0`, `cc1` SHA-256 as recorded in `REPORT.json`.
- Commands: as in the Revalidation script.
- Raw output: reproduced in the tables of Findings §3.

## Revalidation

1. **Verified-compiler architecture (CakeML).** Grep at a new revision:
   ```bash
   R=https://raw.githubusercontent.com/CakeML/cakeml/<rev>
   curl -sSL $R/compiler/backend/proofs/backendProofScript.sml | grep -n -A8 'Definition compute_stack_frame_sizes_def\|Definition is_safe_for_space_def'
   curl -sSL $R/compiler/backend/semantics/dataSemScript.sml | grep -n 'size_of lims \[Number i\]\|size_of lims \[CodePtr'
   ```
   The finding holds while `is_safe_for_space` still passes a compiler-computed frame map into `data_lang_safe_for_space`, and while `reg_count` is computed only there and in `word_to_stack$compile_def`.
2. **CompCert infinite memory and frame check.**
   ```bash
   curl -sSL https://raw.githubusercontent.com/AbsInt/CompCert/<rev>/common/Memory.v | grep -n 'never fails'
   curl -sSL https://raw.githubusercontent.com/AbsInt/CompCert/<rev>/backend/Stacking.v | grep -n 'Too many spilled'
   ```
3. **Allocator slot-sharing rules.** Grep for:
   - `flag_ira_share_spill_slots` and `lra_intersected_live_ranges_p` in `gcc/lra-spills.cc`;
   - `MAX_ATTEMPTS` and `from_range(&self.ctx.spillsets` in `regalloc2/src/ion/spill.rs`;
   - `find_slot` in `CompCert/backend/IRC.ml`.
4. **gcc measurements.** Recreate and rerun; the script takes about 3 s. The `cut -f2` field index must change to `-f3` on gcc builds that print the extra `.su` name column (trunk at the pinned revision).
   ```bash
   mkdir -p /tmp/p1 && cd /tmp/p1
   cat > gen.py <<'EOF'
   import sys
   def live_fn(name, n):
       s = [f"unsigned long {name}(volatile unsigned long *a) {{"]
       s += [f"  unsigned long x{i} = a[{i}];" for i in range(n)]
       s.append(f"  unsigned long r = x{n-1};")
       s += [f"  r = (r * 31u) ^ x{i};" for i in range(n-2, -1, -1)]
       return "\n".join(s + ["  return r;\n}"])
   def two_group(name, n):
       s = [f"unsigned long {name}(volatile unsigned long *a) {{"]
       for p in range(2):
           s += [f"  unsigned long y{p}_{i} = a[{p*n+i}];" for i in range(n)]
           s.append(f"  unsigned long r{p} = y{p}_{n-1};")
           s += [f"  r{p} = (r{p} * 31u) ^ y{p}_{i};" for i in range(n-2, -1, -1)]
           s.append(f"  a[{2*n+p}] = r{p};")
       return "\n".join(s + ["  return r0 + r1;\n}"])
   kind, n = sys.argv[1], int(sys.argv[2])
   print(live_fn(f"live{n}", n) if kind == "live" else two_group(f"two{n}", n))
   EOF
   su() { gcc "$@" -fstack-usage -c "$SRC" -o "$OUT.o"; cut -f2 "$OUT.su"; }
   for n in 4 8 12 13 14 15 16 17 20 24 32 64; do
     python3 gen.py live $n > live$n.c
     echo "N=$n O0=$(SRC=live$n.c OUT=a$n su -O0) O2=$(SRC=live$n.c OUT=b$n su -O2)" \
          "O0nrz=$(SRC=live$n.c OUT=c$n su -O0 -mno-red-zone) O2nrz=$(SRC=live$n.c OUT=d$n su -O2 -mno-red-zone)"
   done
   for n in 20 32 64; do
     python3 gen.py two $n > two$n.c
     echo "two N=$n on=$(SRC=two$n.c OUT=e$n su -O2 -mno-red-zone) off=$(SRC=two$n.c OUT=f$n su -O2 -mno-red-zone -fno-ira-share-spill-slots)"
   done
   ```
   - `scopes.c` contains `void disjoint_scopes(int c){ if(c){char a[256];use(a);} else {char b[256];use(b);} }` with `extern void use(char*);`. Compile it with `-O2 -fstack-reuse=all` and with `-fstack-reuse=none`.
   - **Discriminating checks:**
     - the `O2nrz` column should equal 56 + 8·(N − 14) for N ≥ 15;
     - `two N=32 on` should be far below `off`.
   - A different slope or offset on another gcc, ISA or ABI is a new finding, not a contradiction.
5. **What these checks do not cover.** None of them revalidates the claims taken from the Quantitative CompCert or CompCertS papers. That requires reading those forks' code.
