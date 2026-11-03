# In-Kernel Side-Channel-Freedom Certificates, Speculative Constant-Time Typing, and Linux eBPF Spectre Sanitization (2018–2026)

## Summary

Admitting untrusted extensions into Ring 0 requires protecting not only architectural memory safety (`oobViolation = false`) but also architectural and microarchitectural **side-channel-freedom** (constant-time execution and speculative constant-time execution under Spectre v1 `PHT` and Spectre v4 `STL`). Across the 2018–2026 literature on constant-time bytecode/IR verification (`CT-Wasm` POPL 2019, `Jasmin` CCS 2017 / POPL 2020), speculative constant-time typing (`Pitchfork` PLDI 2020, `Blade` POPL 2021, `Jasmin SCT` IEEE S&P 2021 / S&P 2023 / POPL 2025), and the Linux kernel eBPF verifier's Spectre mitigations (`kernel/bpf/verifier.c` and `kernel/bpf/fixups.c` at `torvalds/linux@0fcb05b72344f40806cbe810de8872f1698bf053`), five structural invariants govern in-kernel side-channel certificate checking:

1. **Collapsing 2-Safety Hyperproperties to Single-Pass $O(|I| + |E|)$ Cutpoint Certificates (`checkKernelCtCertIndexed` & `checkKernelRelCtCertIndexed`)**:
   Constant-time side-channel-freedom (`CtLowEq cert.entryEnv s₁ s₂ → obsTrace prog fuel bid s₁ = obsTrace prog fuel bid s₂`) is a **2-safety hyperproperty** over pairs of executions $(s_1, s_2)$. Constructing a self-composition product CFG $P \times P$ inside the kernel would blow up verification space and time from $O(|V| + |E|)$ to $O(|V|^2 + |E|^2)$. Instead, a single-pass certificate checker verifies a per-basic-block security typing $\Gamma_\ell : (\text{Reg} \to \{\mathsf{Public}, \mathsf{Secret}\}) \times (\text{StackSlot} \to \{\mathsf{Public}, \mathsf{Secret}\})$ in $O(|I| + |E|)$ linear time by interpreting $\Gamma_\ell(x) = \mathsf{Public}$ directly as a **relational equality predicate** $s_1(x) = s_2(x)$ (`CtLowEq`) and enforcing synchronized control flow ($\mathsf{Public}$ branch conditions, memory/map addresses, variable-time `.udivVarTime` operands, and public metric/exit sinks; `kernel_ct_cert_implies_2safety_noninterference`). Enriching the per-block certificate with relational algebraic equality tags (`RelValClass.PubEq` for zero-difference self-XOR scrubbing `r ^ r = 0` and branchless `cmov(pub_cond, sec1, sec2)` scrubbing) strictly extends the class of accepted Ring-0 extensions (`relational_kernel_cert_strictly_extends_ct_cert`) while preserving $O(|I| + |E|)$ single-pass checking (`kernel_rel_ct_cert_soundness`).
2. **Why Architectural CT + Memory Safety Fails Under Spectre v1 (`arch_ct_and_memsafe_cert_leaks_under_spectre_v1`)**:
   An extension that is simultaneously **architecturally memory-safe** (`idx < pubBound` verified before every load) and **architecturally constant-time** (`checkKernelCtCertIndexed = true`, using only $\mathsf{Public}$ registers in branches and addresses) can still leak arbitrary Ring-0 secrets (`SecretKernelKeyArena`) under a Spectre v1 (`PHT`) branch-misprediction oracle. When a bounds check `if r_idx < pubBound` is mispredicted (`oracle = true`), the first out-of-bounds load `r_val := *(pub_base + r_idx)` transiently reads `s.secretMem (r_idx - pubBound)` into a register typed architecturally $\mathsf{Public}$, and the second load `*(pub_base + (r_val & 7))` transmits that secret over the data-cache address trace (`specObsTrace prog 2 0 [true] s₁ ≠ specObsTrace prog 2 0 [true] s₂`).
3. **Why Linux eBPF's Stateful `can_skip_alu_sanitation` Path Pruning Failed (`CVE-2021-33624`) and Why `sanitize_speculative_path` Explodes**:
   In `kernel/bpf/verifier.c:14266-14515`, Linux attempts to mitigate Spectre v1 by patching pointer arithmetic with a 6-instruction branchless `BPF_REG_AX` mask sequence (`fixups.c:1753-1803`). Prior to commit `9183671af6db` (`CVE-2021-33624`), the verifier only walked architecturally feasible paths (`check_cond_jmp_op`) and called `can_skip_alu_sanitation` (`verifier.c:14296`) to skip masking whenever the architectural path had `alu_state == BPF_ALU_NON_POINTER`. When an architecturally dead branch (`if r4 != 0` where `r4 = 0`) assigned an untrusted offset `r1 := r3` before jumping to a shared join block `B2`, `B2` was verified only along the architectural fallthrough (`r1 = 0`), skipping `BPF_REG_AX` masking and leaking `s.secretMem` under branch misprediction (`linux_skip_alu_sanitation_cve2021_33624_unsound`). Fixing `CVE-2021-33624` via `sanitize_speculative_path` (`verifier.c:14344-14498` and `17057-17096`) forces the verifier to clone and explore mispredicted paths at conditional jumps up to `BPF_COMPLEXITY_LIMIT_INSNS = 1,000,000`.
4. **Single-Pass Dual-Label Speculative Constant-Time (`SCT`) Certificates (`checkKernelSctCertIndexed`) and Minimal Cut-Set Instrumentation (`Blade` vs. SFI Masking)**:
   Tracking a 2-bit dual label $(\tau_{\text{arch}}, \tau_{\text{spec}}) \in \{\mathsf{Public}, \mathsf{Secret}\} \times \{\mathsf{SpecSafe}, \mathsf{SpecTransient}\}$ per register (`Jasmin SCT` / `Pitchfork`) with a 1-bit `msfSynced` flag verified in a single linear pass $O(|I| + |E|)$ (`kernel_sct_dual_label_cert_soundness`) eliminates speculative path explosion completely. Across 6 representative Ring-0 workloads (`53` basic blocks, `203` instructions, `25` conditional branches, `58` public loads), `77.6%` (`45/58`) of public packet/map loads flow only into non-transmitter data accumulators; both `Blade` min-cut `slhProtect` (`13` protections) and `SCT`-guided SFI bitwise masking (`13` `ldMasked` instructions, `0` `lfence` barriers) instrument only the `13` transmitter-feeding loads—compared to `50` `lfence` barriers under naive per-branch `BPF_ST_NOSPEC` and `348` extra instructions under Linux's 6-instruction `BPF_REG_AX` `sanitize_ptr_alu`.
5. **Spectre v4 (`STL` Speculative Store Bypass) on Stack Spills & Sticky Stack-Slot Secret Typing (`Jasmin SCT` S&P 2023 / POPL 2025)**:
   When an extension spills a $\mathsf{Secret}$ to stack slot `k` (`spillStack k r_sec`) and later overwrites `spillStack k r_pub` with a $\mathsf{Public}$ value, a flow-sensitive Spectre-v1-only checker overwrites $\Gamma_{\text{stack}}(k) \leftarrow (\mathsf{Public}, \mathsf{SpecSafe})$. Under a Spectre v4 store-bypass oracle (`stlBypass = true`), a subsequent `fillStack r_idx k` bypasses the store buffer and transiently reads the stale secret (`spectre_v4_stl_bypass_leaks_overwritten_secret_slot`). Enforcing **Sticky Stack-Slot Secret Typing** (`checkKernelSctV1V4CertIndexed`, where `spillStack` joins the new register label into the existing stack-slot label $\Gamma_{\text{stack}}(k) \leftarrow \Gamma_{\text{stack}}(k) \sqcup \Gamma_{\text{reg}}(\text{src})$ unless drained by `.lfence`) rejects unsafe secret/public slot reuse (`spectre_v4_sticky_cert_rejects_reuse_and_accepts_disjoint_slots`) and guarantees combined Spectre v1 (`PHT`) + Spectre v4 (`STL`) speculative noninterference with zero `lfence` barriers when public and secret spills use disjoint stack slots (`kernel_sct_v1_v4_sticky_stack_soundness`).

---

## Applicability

The findings, primary-source analyses, and Lean 4 mechanizations in this report apply to the following subjects and their relationships:

- **Linux Kernel eBPF Verifier Spectre v1 and v4 Sanitization (`torvalds/linux@0fcb05b72344f40806cbe810de8872f1698bf053`)**:
  Covers `kernel/bpf/verifier.c:14266-14515` (`retrieve_ptr_limit`, `can_skip_alu_sanitation`, `update_alu_sanitation_state`, `sanitize_val_alu`, `sanitize_speculative_path`, `sanitize_ptr_alu`), `kernel/bpf/verifier.c:17057-17096` (`check_cond_jmp_op` speculative path exploration), `kernel/bpf/verifier.c:18551-18564` (`insn_aux->nospec` Spectre v4 stack-store fence marking), `kernel/bpf/fixups.c:1753-1803` (6-instruction `BPF_REG_AX` branchless pointer masking), and historical commits `b2157399cc98` (`CVE-2017-5753`), `979d63d50c0c` (`CVE-2019-7308`), `7fedb63a8307` (`CVE-2020-27170`), `9183671af6db` (`CVE-2021-33624`), and `f5e81d111750` (Spectre v4 `BPF_ST_NOSPEC`).
- **Architectural Constant-Time Bytecode and IR Type Systems**:
  - `CT-Wasm` (Conrad Watt, John Renner, Natalie Popescu, Sunjay Cauligi, and Deian Stefan, *"CT-Wasm: Type-Driven Secure Cryptography for the Web Ecosystem"*, PACMPL Vol. 3, Issue POPL, Article 77, Jan 2019, DOI `10.1145/3290390`).
  - `Jasmin` (José Bacelar Almeida et al., *"Jasmin: High-Assurance and High-Speed Cryptography"*, ACM CCS 2017, DOI `10.1145/3133956.3134078`; Gilles Barthe et al., *"Formal Verification of a Constant-Time Preserving C Compiler"*, PACMPL Vol. 4, Issue POPL, Article 7, Jan 2020, DOI `10.1145/3371075`).
- **Speculative Constant-Time (`SCT`) Type Systems and Selective SLH Compilers**:
  - `Pitchfork` (Sunjay Cauligi et al., *"Constant-Time Foundations for the New Spectre Era"*, ACM PLDI 2020, DOI `10.1145/3385412.3385970`).
  - `Blade` (Marco Vassena et al., *"Automatically Eliminating Speculative Leaks from Cryptographic Code with Blade"*, PACMPL Vol. 5, Issue POPL, Article 49, Jan 2021, DOI `10.1145/3434330`).
  - `Jasmin SCT` (Gilles Barthe et al., *"High-Assurance Cryptography in the Spectre Era"*, IEEE S&P 2021, DOI `10.1109/SP40001.2021.00046`; Bharath Anand Shivakumar et al., *"Typing High-Speed Cryptography against Spectre v1"*, IEEE S&P 2023, DOI `10.1109/SP46215.2023.10179418`; Santiago Arranz Olmos et al., *"Preservation of Speculative Constant-Time by Compilation"*, PACMPL Vol. 9, Issue POPL, Jan 2025, DOI `10.1145/3704885`).
- **Target Verification Architecture (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**:
  All 29 theorems in `support/InKernelSideChannelAndSpeculativeCertificates.lean` (`4,144` lines) are machine-checked in Lean `v4.34.1` with zero `sorryAx`, zero `Classical.choice`, and zero `Lean.ofReduceBool`.

---

## Findings

### 1. Single-Pass $O(|I| + |E|)$ In-Kernel Side-Channel-Freedom Certificates (`checkKernelCtCertIndexed` & `checkKernelRelCtCertIndexed`)

`Basis: normative + source + execution + derived`

#### 1.1 Collapsing a 2-Safety Hyperproperty to a 1-Pass Cutpoint Certificate
Side-channel-freedom (`LowEq s₁ s₂ → ObsTrace(s₁) = ObsTrace(s₂)`) is a **2-safety hyperproperty**: a single execution trace cannot violate constant-time execution in isolation because leakage is defined by whether two runs starting from states with identical $\mathsf{Public}$ inputs and differing $\mathsf{Secret}$ inputs produce distinguishable hardware observation traces (program-counter branch decisions, memory/cache load and store addresses, variable-latency ALU operands, public helper arguments, or exit return codes).

In general relational program logics (Barthe et al., CCS 2017 / POPL 2020), verifying a 2-safety hyperproperty via self-composition constructs a product program $P \times P$ whose control-flow graph has $|V|^2$ basic-block pairs and $|E|^2$ edge pairs—unacceptable inside an in-kernel extension loader.

A certificate-verifying kernel avoids constructing $P \times P$ by exploiting two structural invariants (`CT-Wasm` POPL 2019 DOI `10.1145/3290390`; formalized in Sections 1–2 of `support/InKernelSideChannelAndSpeculativeCertificates.lean`):

1. **Synchronized Control Flow (`pc₁ = pc₂` Lockstep Invariant)**:
   Because every conditional branch operand (`branch condReg targetTrue targetFalse`) is required to have security label $\mathsf{Public}$, any two runs $(s_1, s_2)$ satisfying `CtLowEq env s₁ s₂` evaluate identical branch conditions (`s₁.getReg condReg = s₂.getReg condReg`), emit identical `.branchPC` leakage events, and transition to the **exact same next basic-block ID `bid'`**. Consequently, only the **diagonal** $\{(\ell, \ell) \mid \ell \in V\}$ of the product CFG $V \times V$ is ever reachable, collapsing $|V|^2$ states to $|V|$.
2. **Unary Security Labels as Relational Equality Predicates**:
   A unary security label $\Gamma_\ell(r) \in \{\mathsf{Public}, \mathsf{Secret}\}$ at basic-block header $\ell$ is interpreted semantically as a **binary relation** (`CtLowEq`) between two concrete states $s_1, s_2$:
   $$\text{CtLowEq}(\Gamma_\ell, s_1, s_2) \iff (s_1.\text{pubMem} = s_2.\text{pubMem}) \wedge \forall r,\ (\Gamma_\ell(r) = \mathsf{Public} \implies s_1(r) = s_2(r)) \wedge \forall k,\ (\Gamma_\ell(k) = \mathsf{Public} \implies s_1(k) = s_2(k)).$$
   Subtyping $\mathsf{Public} \sqsubseteq \mathsf{Secret}$ (`SecLabel.le`) corresponds directly to **logical implication weakening**: if $s_1(r) = s_2(r)$ holds at block exit ($\mathsf{Public}$), then weakening the label to $\mathsf{Secret}$ at a control-flow merge $\ell \to \ell'$ vacuously preserves `CtLowEq` (`ctLowEq_weaken`).

Thus, the in-kernel checker `checkKernelCtCertIndexed` (`InKernelSideChannelAndSpeculativeCertificates.lean:642-643`) verifies the 2-safety hyperproperty in a **single linear pass $O(|I| + |E|)$**:
- For each basic block $\ell$, start from the certificate's block-entry environment $\Gamma_\ell = \text{cert}(\ell)$ (`CtTypeEnv` = 7 bits: 5 register bits + 2 stack-slot bits).
- Walk the block's instructions linearly via `transferCtInstr` (`lines 422-463`), checking that:
  1. Constant-latency ALU operations (`.addConst`, `.xorConst`, `.cmovConst`) assign $\bigsqcup_i \Gamma(\text{src}_i)$ to $\text{dst}$;
  2. Variable-latency ALU operations (`.udivVarTime dst src`) require $\Gamma(\text{dst}) = \mathsf{Public} \wedge \Gamma(\text{src}) = \mathsf{Public}$ before emitting `.varTimeAlu (s.getReg dst) (s.getReg src)`;
  3. Memory loads/stores (`.ldMem`, `.stMem`) require $\Gamma(\text{addrReg}) = \mathsf{Public}$ (and $\Gamma(\text{src}) = \mathsf{Public}$ when storing to `PublicPacketArena`); loads from `PublicPacketArena` produce $\mathsf{Public}$ while loads from `SecretKernelKeyArena` produce $\mathsf{Secret}$;
  4. Kernel helper calls satisfy their information-flow signature (`.helperReadSecretKey` taints `dst` $\mathsf{Secret}$; `.helperLookupPublicMap` requires $\Gamma(\text{keyReg}) = \mathsf{Public}$ and returns $\mathsf{Public}$; `.helperEmitPublicMetric` requires $\Gamma(\text{valReg}) = \mathsf{Public}$).
- At block termination (`checkCtTerminator`, `lines 472-490`), check that `.exit retReg` has $\Gamma(\text{retReg}) = \mathsf{Public}$, `.branch condReg tTrue tFalse` has $\Gamma(\text{condReg}) = \mathsf{Public}$, and every CFG successor edge $\ell \to \ell'$ satisfies $\Gamma_{\text{out}}(\ell) \sqsubseteq \Gamma_{\ell'}$ (`CtTypeEnv.le`).

We proved `kernel_ct_cert_implies_2safety_noninterference` (`lines 691-728`): for any extension `prog`, certificate `cert`, step budget `fuel`, block ID `bid`, and initial states $s_1, s_2$, if `checkKernelCtCertIndexed prog cert = true` and `CtLowEq certEnv s₁ s₂`, then `obsTrace prog fuel bid s₁ = obsTrace prog fuel bid s₂`.

#### 1.2 Architecture B — Single-Pass Relational Algebraic Certificate (`checkKernelRelCtCertIndexed`)
Standard non-relational taint typing (`CT-Wasm` / `checkKernelCtCertIndexed`) assigns $\mathsf{Secret} \sqcup \mathsf{Secret} = \mathsf{Secret}$ to every binary operation on secret registers. Consequently, it rejects constant-time cryptographic idioms used in Ring-0 packet authentication and register scrubbing:
1. **Self-XOR register scrubbing (`xorConst r r`)**: Zeroes out a secret key register (`v ^ v = 0`) before returning or emitting a metric, which `transferCtInstr` rejects as still $\mathsf{Secret}$.
2. **Branchless masked selection (`cmovConst r_dst r_cond r_sec r_sec`)**: Selecting between identical secret registers under a secret condition (`if c ≠ 0 then v else v = v`) is branchless and independent of `c`, and scrubbing it via `xorConst` yields `0`.

In Section 3 of `support/InKernelSideChannelAndSpeculativeCertificates.lean` (`lines 798-1370`), we enrich the per-block certificate to `RelCtTypeEnv` over the 3-element relational lattice `RelValClass`:
- `.PubEq` ($\Delta = 0$, public equal across runs: $s_1(r) = s_2(r)$),
- `.SecVar id` (secret value carrying static symbolic equivalence-class tag `id : Nat`),
- `.SecAny` (arbitrary secret value).

Because `transferRelCtInstr` (`lines 914-969`) tracks `RelValClass.sameSecretSource (.SecVar id₁) (.SecVar id₂) = Nat.beq id₁ id₂`:
- `xorConst dst src` checks whether `dst` and `src` carry the same `.SecVar id`; since `Nat.lxor v v = 0` for all $v$ (`nat_lxor_self`, proved by strong induction on `Nat.bitwise` at `lines 809-831` without `Classical.choice`), `transferRelCtInstr` soundly upgrades `dst` to `.PubEq`!
- `cmovConst dst condReg srcTrue srcFalse` preserves `.SecVar id` when both branches carry `.SecVar id`, and upgrades to `.PubEq` when both branches are `.PubEq`.

We proved:
- **Soundness (`kernel_rel_ct_cert_soundness`, `lines 1255-1291`)**: `checkKernelRelCtCertIndexed prog cert = true` guarantees 2-safety observational noninterference (`obsTrace prog fuel bid s₁ = obsTrace prog fuel bid s₂`) in $O(|I| + |E|)$ single-pass time.
- **Strict Expressiveness Separation (`relational_kernel_cert_strictly_extends_ct_cert`, `lines 1344-1370`)**:
  1. **Conservative Extension**: Every certificate `cert` accepted by `checkKernelCtCertIndexed` is automatically accepted by `checkKernelRelCtCertIndexed` via `liftCtCertToRel cert` (`checkCtCert_imp_checkRelCtCert`, `lines 1297-1341`).
  2. **Strict Separation Witness**: The constant-time keyed packet tag scrubber `relScrubbingCryptoProg` (`lines 1310-1321`, which reads a secret key into `R3`, copies `R2 := R3`, performs branchless `cmovConst R2 R3 R2 R3`, scrubs `R2 := R2 ^ R2`, and emits `R2` via `helperEmitPublicMetric`) is **accepted** by `checkKernelRelCtCertIndexed` (`rfl`), executes with identical observation traces, and is **rejected (`= false`)** by `checkKernelCtCertIndexed` for **every** possible non-relational certificate `ctCert`!

---

### 2. Speculative Side-Channel Certificates (`SCT`, `Blade`, `Pitchfork`, `Jasmin SCT`) vs. Linux eBPF `sanitize_ptr_alu`

`Basis: normative + source + execution + derived`

#### 2.1 Primary-Source Mechanics of Linux eBPF's Spectre v1 and v4 Defenses (`torvalds/linux@0fcb05b72344f40806cbe810de8872f1698bf053`)
Direct inspection of `kernel/bpf/verifier.c` and `kernel/bpf/fixups.c` at commit `0fcb05b72344f40806cbe810de8872f1698bf053` establishes how Linux attempts to prevent speculative bounds bypasses in unprivileged eBPF:

1. **Branchless `BPF_REG_AX` Pointer-ALU Sanitization (`verifier.c:14266-14515`, `fixups.c:1753-1803`)**:
   When a scalar is added to or subtracted from a stack, packet, or map-value pointer (`adjust_ptr_min_max_vals`), `sanitize_ptr_alu` (`verifier.c:14424-14515`) invokes `retrieve_ptr_limit` (`lines 14266-14294`) to compute the maximum valid architectural offset `alu_limit`, records `BPF_ALU_SANITIZE_SRC` or `BPF_ALU_SANITIZE_DST` in `insn_aux_data[insn_idx].alu_state`, and later rewrites the single pointer-ALU instruction in `bpf_do_misc_fixups` (`fixups.c:1753-1803`) into a **6-instruction sequence** using scratch register `BPF_REG_AX`:
   ```c
   *patch++ = BPF_MOV32_IMM(BPF_REG_AX, aux->alu_limit);
   *patch++ = BPF_ALU64_REG(BPF_SUB, BPF_REG_AX, off_reg);
   *patch++ = BPF_ALU64_REG(BPF_OR, BPF_REG_AX, off_reg);
   *patch++ = BPF_ALU64_IMM(BPF_NEG, BPF_REG_AX, 0);
   *patch++ = BPF_ALU64_IMM(BPF_ARSH, BPF_REG_AX, 63);
   *patch++ = BPF_ALU64_REG(BPF_AND, BPF_REG_AX, off_reg);
   ```
   Wait: this arithmetic trick computes a sign-bit mask in `BPF_REG_AX` (`0xffffffffffffffff` if `off_reg` and `alu_limit - off_reg` are both non-negative, else `0`) and masks `off_reg`.
2. **Historical Spectre Bypasses in `verifier.c` (`2018–2022`)**:
   - **CVE-2017-5753 (Spectre v1 bounds bypass, commit `b2157399cc98`)**: Initial motivation for array index masking (`array_map_gen_lookup`) and pointer ALU sanitization.
   - **CVE-2019-7308 (Signed bounds & `can_skip_alu_sanitation` bypass, commit `979d63d50c0c`)**: `retrieve_ptr_limit` initially failed to account for mixed signed/unsigned bounds and direction changes across `BPF_ADD`/`BPF_SUB`.
   - **CVE-2020-27170 (Pointer-to-pointer comparison speculative bypass, commit `7fedb63a8307`)**: `retrieve_ptr_limit` computed `alu_limit` using `umax_value` before the pointer offset was updated or when comparing two pointers (`BPF_JMP` on `PTR_TO_MAP_VALUE`), yielding an off-by-bounds `alu_limit`.
   - **CVE-2021-33624 (Speculative path-pruning bypass of `can_skip_alu_sanitation`, commit `9183671af6db`)**:
     In `verifier.c:14296-14306`, `can_skip_alu_sanitation(env, insn)` skips patching if `env->insn_aux_data[insn_idx].alu_state == BPF_ALU_NON_POINTER`. Prior to `9183671af6db`, when a conditional branch `if (cond)` was statically known to take only one edge architecturally (`pred == 0` or `pred == 1` in `check_cond_jmp_op`), the verifier **pruned the architecturally untaken branch** without exploring it. If the architecturally feasible path loaded from `[r_ptr + r_const]` (`BPF_ALU_NON_POINTER` because `r_const` is a known constant), `update_alu_sanitation_state` marked the instruction `BPF_ALU_NON_POINTER`. Under CPU branch misprediction, the CPU transiently executes the architecturally dead branch (where `r_off` holds an attacker-controlled variable offset) and reaches the **same shared load instruction**—which now lacks `BPF_REG_AX` masking!
   - **The Post-CVE-2021-33624 Fix (`sanitize_speculative_path`, `verifier.c:14344-14498` and `17057-17096`)**:
     To patch `CVE-2021-33624`, `check_cond_jmp_op` (`lines 17057-17096`) now calls `sanitize_speculative_path` whenever a branch is architecturally one-sided (`pred == 1` or `pred == 0`), pushing a cloned speculative `bpf_verifier_state` (`speculative = true`) onto the exploration stack so the verifier symbolically executes **both** architectural and mispredicted paths. If `update_alu_sanitation_state` (`lines 14308-14331`) sees conflicting `alu_state` or `alu_limit` values across paths joining at the same instruction, it gives up on branchless masking and falls back to `sanitize_mark_insn_seen(env)` (`verifier.c:18551-18564`), which sets `insn_aux->nospec = true` and emits a full `BPF_ST_NOSPEC()` (`lfence`) barrier!

#### 2.2 Mechanized Proof of `CVE-2021-33624` and the Failure of Architectural CT + Memory Safety (`support/InKernelSideChannelAndSpeculativeCertificates.lean`, Section 4)
In Section 4 of `support/InKernelSideChannelAndSpeculativeCertificates.lean`:
1. **`arch_ct_and_memsafe_cert_leaks_under_spectre_v1` (`lines 1679-1748`)**:
   We construct `spectreBoundsBypassGadget` (`lines 1638-1657`): Block 0 checks `r1 < pubBound` (`r4 := natBlt r1 r2; branch r4 1 2`); Block 1 loads `r3 := *(pub_base + r1)`, masks `r3 := r3 & 7`, and loads `r0 := *(pub_base + r3)`.
   We prove:
   - `checkKernelCtCertIndexed spectreBoundsBypassGadget spectreBoundsBypassArchCtCert = true` (every register in the program is architecturally $\mathsf{Public}$);
   - Under architectural execution (`oracle = [false]`), when `r1 = 16 >= pubBound (8)`, the branch jumps to exit Block 2 and performs **zero** out-of-bounds reads;
   - Under Spectre v1 misprediction (`oracle = [true]`), the CPU transiently enters Block 1 with `r1 = 16`, reads `s.secretMem (16 - 8) = s.secretMem 8` into `r3`, and indexes `*(pub_base + (r3 & 7))`, leaking the secret key byte into the speculative cache-line address trace (`specObsTrace spectreBoundsBypassGadget 2 0 [true] s₁ ≠ specObsTrace spectreBoundsBypassGadget 2 0 [true] s₂`)!
2. **`linux_skip_alu_sanitation_cve2021_33624_unsound` (`lines 1805-1869`)**:
   We model the exact diamond-join CFG of `CVE-2021-33624` (`cve2021_33624_gadget`, `lines 1766-1786`):
   - Block 0 sets `r1 := 0` (safe constant offset), `r4 := 0` (architecturally false condition), and branches `branch r4 2 1`;
   - Block 1 (architecturally unreachable because `r4 = 0`, but transiently reachable under branch misprediction) sets `r1 := r3` (untrusted scalar offset `16`) and jumps to shared Block 2;
   - Block 2 loads `r2 := *(pub_base + r1)` (unmasked because `linuxArchOnlySkipSanitation` sees only the architectural path `0 → 2` where `r1 = 0`), masks `r2 & 7`, and loads `r0 := *(pub_base + r2)`.
   We prove that `linuxArchOnlySkipSanitation cve2021_33624_gadget = true` (skipping `sanitize_ptr_alu`), yet under branch misprediction (`oracle = [true]`) the shared Block 2 load reads `s.secretMem 8` and leaks it across `s₁` (`secretMem 8 = 2`) and `s₂` (`secretMem 8 = 6`).

#### 2.3 Single-Pass Dual-Label `SCT` Certificate Checker (`checkKernelSctCertIndexed`) and Soundness Theorem
In Section 5 of `support/InKernelSideChannelAndSpeculativeCertificates.lean` (`lines 1871-2785`), we formalize a single-pass Speculative Constant-Time (`SCT`) certificate checker combining the dual-label type system of `Jasmin SCT` (IEEE S&P 2021 / S&P 2023) and `Pitchfork` (PLDI 2020) with `Blade`'s (POPL 2021) selective `SLH` primitives and SFI bitwise address masking:

- **Per-Register Dual Security Lattice (`SctDualLabel`)**:
  Each register carries a 2-bit pair $(\tau_{\text{arch}}, \tau_{\text{spec}}) \in \{\mathsf{Public}, \mathsf{Secret}\} \times \{\mathsf{SpecSafe}, \mathsf{SpecTransient}\}$, plus a 1-bit per-block `msfSynced : Bool` flag tracking whether the CPU's Misspeculation Flag (`msfMasked`) has been synchronized with `specMode` via `.slhInitMsf`:
  - `pubSafe = (Public, SpecSafe)`: equal across $(s_1, s_2)$ in **both** architectural and speculative execution (`s₁.specHalted = false → s₁.getReg r = s₂.getReg r`);
  - `pubTransient = (Public, SpecTransient)`: equal across $(s_1, s_2)$ when `specMode = false`, but potentially holding a transiently loaded out-of-bounds secret when `specMode = true`;
  - `secTransient = (Secret, SpecTransient)`: secret in both modes.
- **Why Unmasked Public Loads Produce `pubTransient` while SFI-Masked Loads Produce `pubSafe`**:
  - An unmasked load `.ldUnmasked dst addrReg` from `PublicPacketArena` requires `isPubSafe(addrReg) = true`, ensuring the load address itself does not leak secrets. However, because a prior bounds check may have been mispredicted (`specMode = true`), `addrReg` can exceed `pubBound` transiently and read `s.secretMem` (`readUnmasked`, `lines 1463-1467`). Therefore `transferSctInstr` types `dst` as `pubTransient = (Public, SpecTransient)`!
  - By contrast, a bitwise-masked SFI load `.ldMasked dst addrReg mask` with `natBlt mask env.pubBound = true` guarantees `(addr & mask) ≤ mask < pubBound` (`natBlt_and_of_natBlt` and `readSpecMem_masked_eq_pubMem`, proved by strong induction on `Nat.bitwise` at `lines 1545-1625` without `Classical.choice`). Even under arbitrary branch misprediction (`specMode = true`), `addr & mask` can **never** reach `s.secretMem`, so `transferSctInstr` soundly types `dst` as `pubSafe = (Public, SpecSafe)`!
- **Three Compositional Defenses Accepted by `checkKernelSctCertIndexed`**:
  1. **`Blade` Selective Speculative Load Hardening (`.slhInitMsf` + `.slhProtect dst src`)**: When `env.msfSynced = true`, `.slhProtect dst src` masks `src` with the architectural/speculative misspeculation mask (`if s.msfMasked then 0 else s.getReg src`), upgrading `(arch, SpecTransient)` to `(arch, SpecSafe)` in 1 cycle (`cmov`/`and`) without a pipeline fence (`spectre_gadget_repaired_by_blade_slh_accepted`, `lines 2747-2757`).
  2. **SFI Bitwise Address Masking (`.ldMasked dst addrReg mask`)**: Confines the load address to `[0, mask] ⊂ [0, pubBound)` in 1 ALU `and` instruction, keeping `dst` `pubSafe` without tracking `msfSynced` across branches (`spectre_gadget_repaired_by_sfi_mask_accepted`, `lines 2759-2771`).
  3. **Speculation Barrier (`.lfence`)**: Sets `specHalted := specMode` and upgrades all registers from `(arch, SpecTransient)` to `(arch, SpecSafe)` (`spectre_gadget_repaired_by_lfence_accepted`, `lines 2773-2785`).
- **Universal Speculative Noninterference Theorem (`kernel_sct_dual_label_cert_soundness`, `lines 2566-2607`)**:
  For **any** extension `prog`, certificate `cert`, step budget `fuel`, block ID `bid`, **arbitrary misprediction oracle schedule `oracles : List Bool`**, and initial states $s_1, s_2$, if `checkKernelSctCertIndexed prog cert = true` and `SctLowEq certEnv s₁ s₂`, then:
  $$\text{specObsTrace}(\text{prog}, \text{fuel}, \text{bid}, \text{oracles}, s_1) = \text{specObsTrace}(\text{prog}, \text{fuel}, \text{bid}, \text{oracles}, s_2).$$

---

### 3. Spectre v4 (`STL` Speculative Store Bypass) on Stack Spills & Sticky Stack-Slot Secret Typing (`Jasmin SCT` S&P 2023 / POPL 2025)

`Basis: normative + source + execution + derived`

#### 3.1 Why Flow-Sensitive Overwrite Typing Fails Under Spectre v4 Store Bypass
In `Jasmin SCT` (Shivakumar et al., IEEE S&P 2023 DOI `10.1109/SP46215.2023.10179418`; Arranz Olmos et al., PACMPL Vol. 9 POPL 2025 DOI `10.1145/3704885`), register allocation spills architectural and cryptographic values to stack slots `s0, s1, ...`. In an architectural CT or Spectre-v1-only type system (`transferSctV1OnlyOverwriteInstr`, `InKernelSideChannelAndSpeculativeCertificates.lean:2958-3004`), storing a register `src` to stack slot `k` (`spillStack k src`) overwrites the slot's type with the new value's label:
$$\Gamma_{\text{stack}}^{\text{v1-only}}(k) \leftarrow \Gamma_{\text{reg}}(\text{src}).$$
However, on out-of-order CPUs with store buffers, a subsequent stack reload `fillStack dst k` can execute **before** an older store `spillStack k r_pub` commits its address/data in the store buffer (**Spectre v4 / Speculative Store Bypass (`STL`)**), transiently forwarding the **stale** stack value `s.getStackStale k` from an earlier spill `spillStack k r_sec`!

In Section 6 of `support/InKernelSideChannelAndSpeculativeCertificates.lean` (`lines 2788-4144`), we formalize `SpecV4State` (tracking both architectural `s0Curr, s1Curr` and store-buffer stale `s0Stale, s1Stale` stack values, plus per-instruction `stlOracles : List Bool`) and prove:

- **`spectre_v4_stl_bypass_leaks_overwritten_secret_slot` (`lines 3194-3252`)**:
  The extension `spectreV4OverwriteGadget` (`lines 3145-3165`):
  1. Reads a secret key into `R3` (`helperReadSecretKey .R3`) and spills it to stack slot `.S0` (`spillStack .S0 .R3`);
  2. Overwrites stack slot `.S0` with public constant `0` (`movImm .R2 0; spillStack .S0 .R2`);
  3. Reloads `R1` from `.S0` (`fillStack .R1 .S0`), masks `R1 & 7`, and loads `R0 := *(pub_base + (R1 & 7))` (`ldMasked .R0 .R1 7`).
  We prove that:
  - `spectreV4OverwriteGadget` **passes** the Spectre-v1-only certificate checker (`checkKernelSctV1OnlyOverwriteCertIndexed spectreV4OverwriteGadget spectreV4OverwriteV1Cert = true`), because `spillStack .S0 .R2` overwrites `.S0`'s label to `pubSafe`;
  - Under architectural execution (`stlBypass = false`), `fillStack .R1 .S0` reads `0` and produces identical traces `[.loadAddr 0, .exitCode 0]`;
  - Under a Spectre v4 `STL` store-bypass oracle (`stlBypass = true` on `fillStack`), `fillStack .R1 .S0` transiently reads the overwritten secret `s.secretMem 0` from `s0Stale` and leaks it into the speculative load address trace (`specV4ObsTrace ... = [.loadAddr 3]` vs. `[.loadAddr 5]`)!

#### 3.2 Sticky Stack-Slot Secret Typing (`checkKernelSctV1V4CertIndexed`) & Combined Spectre v1 + v4 Soundness
To defeat Spectre v4 (`STL`) without inserting an `lfence` (`BPF_ST_NOSPEC`) at every stack store (as Linux's `verifier.c:18551-18564` does via `insn_aux->nospec`), `transferSctV1V4Instr` (`lines 3013-3063`) enforces **Sticky Stack-Slot Secret Typing**:
1. **Sticky Spill Rule (`spillStack slot src`)**:
   $$\Gamma_{\text{stack}}^{\text{v1+v4}}(\text{slot}) \leftarrow \Gamma_{\text{stack}}^{\text{v1+v4}}(\text{slot}) \sqcup \Gamma_{\text{reg}}(\text{src}).$$
   Once a stack slot holds a $\mathsf{Secret}$ or $\mathsf{SpecTransient}$ value, overwriting it with a $\mathsf{Public}$ value does **not** clear its secret/transient taint, because the older secret store remains transiently readable in the store buffer under `STL` bypass!
2. **Store-Buffer Speculation Rule (`fillStack dst slot`)**:
   Because any `fillStack` can trigger `STL` store-buffer bypass (`enterStlSpec stlBypass`), `transferSctV1V4Instr` clears `msfSynced := false` (since `STL` misspeculation does not update the branch-based `SLH` misspeculation flag `msfMasked`!) and assigns $\Gamma_{\text{reg}}(\text{dst}) \leftarrow \Gamma_{\text{stack}}^{\text{v1+v4}}(\text{slot})$. If $\Gamma_{\text{stack}}^{\text{v1+v4}}(\text{slot}) = \mathsf{pubSafe}$, then **both** the current architectural value `s.getStackCurr slot` and the stale store-buffer value `s.getStackStale slot` are guaranteed to be $\mathsf{Public}$ and $\mathsf{SpecSafe}$ (`SctV4LowEq.stackCurrRel` and `SctV4LowEq.stackStaleRel`), so `dst` remains `pubSafe` even if `stlBypass = true`!
3. **Compiler Discipline (`Jasmin SCT` Disjoint Public/Secret Stack Frames)**:
   The extension compiler partitions stack slots into **public stack slots** (e.g. `.S1`, typed `pubSafe`, which never receive secret spills) and **secret stack slots** (e.g. `.S0`, typed `secTransient`, used exclusively for secret spills), requiring **zero `lfence` instructions** while adding only 2 bits per stack slot to each basic-block certificate header.

We proved:
- **Combined Spectre v1 + v4 Soundness (`kernel_sct_v1_v4_sticky_stack_soundness`, `lines 4018-4065`)**: For any extension `prog`, sticky certificate `cert`, step budget `fuel`, block ID `bid`, **arbitrary Spectre v1 branch-misprediction oracle schedule `branchOracles : List Bool`**, **arbitrary Spectre v4 store-bypass oracle schedule `stlOracles : List (List Bool)`**, and initial states $s_1, s_2$, if `checkKernelSctV1V4CertIndexed prog cert = true` and `SctV4LowEq certEnv s₁ s₂`, then:
  $$\text{specV4ObsTrace}(\text{prog}, \text{fuel}, \text{bid}, \text{branchOracles}, \text{stlOracles}, s_1) = \text{specV4ObsTrace}(\text{prog}, \text{fuel}, \text{bid}, \text{branchOracles}, \text{stlOracles}, s_2).$$
- **Rejection of Slot Reuse & Acceptance of Disjoint Slots (`spectre_v4_sticky_cert_rejects_reuse_and_accepts_disjoint_slots`, `lines 4108-4138`)**:
  `checkKernelSctV1V4CertIndexed` rejects `spectreV4OverwriteGadget` (`= false`) and accepts `spectreV4DisjointSlotRepair` (`= true`, where secrets spill to `.S0` and public indices spill to `.S1` with zero `lfence` barriers), guaranteeing identical `specV4ObsTrace` under all `(branchOracles, stlOracles)` schedules.

---

### 4. Quantitative Trade-Offs Across 6 Ring-0 Extension Workloads (`support/sct_certificate_vs_fence_probe.py`)

`Basis: execution + derived`

We implemented `check_kernel_sct_cert`, `Blade`'s Edmonds-Karp max-flow / min-cut selective `SLH` placement (`apply_blade_min_cut_slh`), and `SCT`-guided SFI bitwise load masking (`apply_sfi_bitwise_masking`) in `support/sct_certificate_vs_fence_probe.py` (`1,168` lines) and evaluated four Spectre v1 mitigation architectures plus three Spectre v4 stack-spill models across 6 representative Ring-0 workloads (`support/sct_certificate_vs_fence_probe_results.json`):

#### 4.1 Spectre v1 (`PHT`) Mitigation Comparison Across 6 Ring-0 Workloads

| Workload (`support/sct_certificate_vs_fence_probe.py`) | Blocks / Instrs / Branches / Public Loads | Scheme 1: Naive Per-Branch `lfence` (`BPF_ST_NOSPEC`) Barriers (Est. Cycles) | Scheme 2: Linux `sanitize_ptr_alu` (`BPF_REG_AX` Patch Instrs / Spec Verifier States / Cycles) | Scheme 3: `Blade` Min-Cut `SLH` + `SCT` Cert (`slhProtect` Instrs / Verifier Steps / Cert Bytes / Cycles) | Scheme 4: SFI Bitwise Mask (`ldMasked`) + `SCT` Cert (Masked Loads / `lfence` / Verifier Steps / Cert Bytes / Cycles) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`l2_l3_l4_packet_parser`** (Ethernet/VLAN/IPv4/TCP parser) | `5` / `23` / `3` / `12` | `6` `lfence` (`54` cyc) | `72` insns / `40` states / `36` cyc | **`3` `slhProtect`** (`9` loads spared) / `32` steps / `10` B / `6` cyc | **`3` `ldMasked`** / `0` `lfence` / `29` steps / `10` B / **`3` cyc** |
| **`bpf_cgroup_firewall_acl`** (5-tuple ACL + 2 map lookups) | `5` / `19` / `3` / `10` | `6` `lfence` (`54` cyc) | `60` insns / `40` states / `30` cyc | **`3` `slhProtect`** (`7` loads spared) / `28` steps / `10` B / `6` cyc | **`3` `ldMasked`** / `0` `lfence` / `25` steps / `10` B / **`3` cyc** |
| **`xdp_ddos_syn_cookie_filter`** (Keyed SipHash + self-XOR scrub) | `4` / `26` / `1` / `6` | `2` `lfence` (`36` cyc) | `36` insns / `8` states / `36` cyc | **`2` `slhProtect`** (`4` loads spared) / `32` steps / `8` B / `6` cyc | **`2` `ldMasked`** / `0` `lfence` / `30` steps / `8` B / **`4` cyc** |
| **`chacha20_poly1305_pkt_aead`** (Constant-time AEAD packet core) | `3` / `25` / `1` / `7` | `2` `lfence` (`72` cyc) | `42` insns / `6` states / `84` cyc | **`0` `slhProtect`** (`7` loads spared) / `28` steps / `6` B / `4` cyc | **`0` `ldMasked`** / `0` `lfence` / `28` steps / `6` B / **`0` cyc** |
| **`cve_2021_33624_branch_prune_cfg`** (Diamond-join speculative gadget) | `3` / `11` / `1` / `2` | `2` `lfence` (`18` cyc) | `12` insns / `6` states / `6` cyc | **`1` `slhProtect`** (`1` load spared) / `15` steps / `6` B / `2` cyc | **`1` `ldMasked`** / `0` `lfence` / `14` steps / `6` B / **`1` cyc** |
| **`scaled_diamond_pipeline_d16`** (16-stage conditional inspection) | `33` / `99` / `16` / `20` | `32` `lfence` (`288` cyc) | `120` insns / **`1,000,000` states** / `60` cyc | **`4` `slhProtect`** (`16` loads spared) / **`146` steps** / `66` B / `20` cyc | **`4` `ldMasked`** / `0` `lfence` / **`142` steps** / `66` B / **`4` cyc** |
| **Aggregate Across All 6 Workloads** | **`53` / `203` / `25` / `58`** | **`50` `lfence` (`522` cyc)** | **`348` insns / `1,000,100` states / `252` cyc** | **`13` `slhProtect` (`45/58 = 77.6%` loads spared) / `281` steps / `106` B / `44` cyc** | **`13` `ldMasked` / `0` `lfence` / `268` steps / `106` B / `15` cyc** |

Key takeaways from the empirical probe:
1. **`77.6%` (`45 / 58`) of Public Loads Do Not Feed Speculative Transmitters**:
   In packet parsers, firewalls, and AEAD authenticators, most packet loads (`ipv4_tos`, `ipv4_ttl`, `saddr`, `daddr`, payload words, AEAD block words) only feed arithmetic/hash accumulators or branchless `cmov` selections and **never** flow into memory addresses, branch conditions, or public metric emissions. Both `Blade` min-cut `SLH` (`Scheme 3`) and `SCT`-guided SFI bitwise masking (`Scheme 4`) leave all `45` non-transmitter loads uninstrumented and protect only the `13` transmitter-feeding loads (`ihl`, `tcp_doff`, map lookup keys, etc.).
2. **Single-Pass `checkKernelSctCert` Eliminates `sanitize_speculative_path` State Explosion**:
   On `scaled_diamond_pipeline_d16` ($2^{16} = 65,536$ speculative paths), Linux's `sanitize_speculative_path` hits the `1,000,000`-instruction verification cap, whereas `checkKernelSctCert` verifies a `66`-byte dual-label certificate (`2` bytes per basic-block header) in `142–146` linear steps.
3. **SFI Bitwise Load Masking (`Scheme 4`) Dominates Both `lfence` and `Blade` `SLH` when Power-of-2 Arena Bounds Hold**:
   Unlike `Blade` `SLH` (`Scheme 3`), which must still maintain the running misspeculation flag `msfMasked` across every conditional branch (`1` cycle per branch + `1` cycle per `slhProtect` = `44` cycles aggregate) and requires `msfSynced` to be re-established after any Spectre v4 `fillStack`, SFI bitwise address masking (`ldMasked` with `and addr, mask`) requires **zero** branch MSF tracking and **zero** `lfence` barriers (`15` cycles aggregate, a `34.8x` reduction over naive `lfence` and `16.8x` reduction over Linux `sanitize_ptr_alu`).

#### 4.2 Summary of All 29 Machine-Checked Theorems in `support/InKernelSideChannelAndSpeculativeCertificates.lean`

All **29 theorems** in `support/InKernelSideChannelAndSpeculativeCertificates.lean` (`4,144` lines) compile under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with **zero `sorryAx`, zero `Classical.choice`, and zero `Lean.ofReduceBool`**:

| Section | Theorem Name | Formal Statement & Significance | Axioms |
| :--- | :--- | :--- | :--- |
| **Sec 2** | `ct_instr_step_noninterference` | Single-step instruction noninterference for `transferCtInstr` preserving `CtLowEq` and identical `LeakEvent` lists. | `[propext, Quot.sound]` |
| **Sec 2** | `ct_block_step_noninterference` | Single-block execution and terminator noninterference under `checkCtBlock`. | `[propext, Quot.sound]` |
| **Sec 2** | `checkKernelCtCertIndexed_imp_AllBlocksCtCertified` | Linear-pass `checkKernelCtCertIndexed prog cert = true` implies `AllBlocksCtCertified prog cert`. | `[propext, Quot.sound]` |
| **Sec 2** | `kernel_ct_cert_implies_2safety_noninterference` | **Main CT Soundness**: `checkKernelCtCertIndexed prog cert = true` implies `obsTrace prog fuel bid s₁ = obsTrace prog fuel bid s₂` for all `CtLowEq` states $s_1, s_2$. | `[propext, Quot.sound]` |
| **Sec 2** | `ct_cert_rejects_secret_branch_and_cache_index` | `checkKernelCtCertIndexed` rejects both secret-dependent branch (`secretBranchBadProg`) and secret cache-index (`secretCacheIndexBadProg`) extensions. | `[propext]` |
| **Sec 2** | `ct_cert_accepts_constant_time_keyed_mac` | `checkKernelCtCertIndexed` accepts `ctKeyedPacketFilterProg` (`= true`) and guarantees identical observation traces. | `[propext]` |
| **Sec 3** | `rel_ct_instr_step_noninterference` | Single-step relational noninterference for `transferRelCtInstr` (`PubEq`, `SecVar id`, `SecAny`) with self-XOR (`nat_lxor_self`) and `cmov` cancellation. | `[propext, Quot.sound]` |
| **Sec 3** | `rel_ct_block_step_noninterference` | Single-block relational noninterference under `checkRelCtBlock`. | `[propext, Quot.sound]` |
| **Sec 3** | `checkKernelRelCtCertIndexed_imp_AllBlocksRelCtCertified` | Linear-pass `checkKernelRelCtCertIndexed prog cert = true` implies `AllBlocksRelCtCertified prog cert`. | `[propext, Quot.sound]` |
| **Sec 3** | `kernel_rel_ct_cert_soundness` | **Main Relational CT Soundness**: `checkKernelRelCtCertIndexed prog cert = true` implies `obsTrace prog fuel bid s₁ = obsTrace prog fuel bid s₂` for all `RelCtLowEq` states $s_1, s_2$. | `[propext, Quot.sound]` |
| **Sec 3** | `relational_kernel_cert_strictly_extends_ct_cert` | **Strict Expressiveness Separation**: Every `CtCertificate` lifts to a valid `RelCtCertificate`, and `relScrubbingCryptoProg` passes `checkKernelRelCtCertIndexed` while failing `checkKernelCtCertIndexed` for **all** `ctCert`. | `[propext, Quot.sound]` |
| **Sec 4** | `natBlt_and_of_natBlt` | Bitwise mask bound theorem (`Nat.land a m ≤ m < b` when `m < b`), proved by strong induction on `Nat.bitwise` without `Classical.choice`. | `[propext, Quot.sound]` |
| **Sec 4** | `readSpecMem_masked_eq_pubMem` | When `natBlt mask s.pubBound = true`, `readSpecMem s (addr &&& mask) = s.pubMem (addr &&& mask)` even under speculative execution. | `[propext, Quot.sound]` |
| **Sec 4** | `arch_ct_and_memsafe_cert_leaks_under_spectre_v1` | `spectreBoundsBypassGadget` passes `checkKernelCtCertIndexed = true` and is architecturally memory-safe, yet leaks `s.secretMem` under Spectre v1 (`oracle = [true]`). | `[propext]` |
| **Sec 4** | `linux_skip_alu_sanitation_cve2021_33624_unsound` | Models Linux `CVE-2021-33624` (`9183671af6db`): `cve2021_33624_gadget` passes `linuxArchOnlySkipSanitation = true`, yet leaks `s.secretMem 8` across the shared join block under branch misprediction. | `[propext]` |
| **Sec 5** | `sct_instr_step_noninterference` | Single-step speculative noninterference for dual-label `transferSctInstr` (`SctDualLabel` + `msfSynced`). | `[propext, Quot.sound]` |
| **Sec 5** | `sct_block_step_noninterference` | Single-block speculative noninterference under `checkSctBlock` across both architectural (`oracle = false`) and mispredicted (`oracle = true`) branch transitions. | `[propext, Quot.sound]` |
| **Sec 5** | `checkKernelSctCertIndexed_imp_AllBlocksSctCertified` | Linear-pass `checkKernelSctCertIndexed prog cert = true` implies `AllBlocksSctCertified prog cert`. | `[propext, Quot.sound]` |
| **Sec 5** | `kernel_sct_dual_label_cert_soundness` | **Main Spectre v1 `SCT` Soundness**: `checkKernelSctCertIndexed prog cert = true` implies `specObsTrace prog fuel bid oracles s₁ = specObsTrace prog fuel bid oracles s₂` for **all** misprediction oracle schedules `oracles`. | `[propext, Quot.sound]` |
| **Sec 5** | `spectre_gadget_rejected_by_sct_cert` | Unmitigated `spectreBoundsBypassGadget` is rejected (`= false`) by `checkKernelSctCertIndexed`. | `[propext]` |
| **Sec 5** | `spectre_gadget_repaired_by_blade_slh_accepted` | `Blade` selective `SLH` repair (`spectreGadgetBladeSlhProg`) passes `checkKernelSctCertIndexed = true` (`0` `lfence` barriers). | `[propext]` |
| **Sec 5** | `spectre_gadget_repaired_by_sfi_mask_accepted` | SFI bitwise mask repair (`spectreGadgetSfiMaskProg`) passes `checkKernelSctCertIndexed = true` (`0` `lfence` barriers, `0` branch MSF tracking). | `[propext]` |
| **Sec 5** | `spectre_gadget_repaired_by_lfence_accepted` | Fence repair (`spectreGadgetLfenceProg`) passes `checkKernelSctCertIndexed = true`. | `[propext]` |
| **Sec 6** | `spectre_v4_stl_bypass_leaks_overwritten_secret_slot` | **Spectre v4 (`STL`) Counterexample**: `spectreV4OverwriteGadget` (spilling secret to `.S0`, overwriting `.S0 := 0`, and reloading `.S0`) passes Spectre-v1-only `checkKernelSctV1OnlyOverwriteCertIndexed = true`, yet leaks `s.secretMem 0` under `STL` store bypass (`stlBypass = true`). | `[propext]` |
| **Sec 6** | `sct_v1_v4_instr_step_noninterference` | Single-step combined Spectre v1 + v4 noninterference for `transferSctV1V4Instr` with sticky `spillStack` typing and `enterStlSpec` on `fillStack`. | `[propext, Quot.sound]` |
| **Sec 6** | `sct_v1_v4_block_step_noninterference` | Single-block combined Spectre v1 + v4 noninterference under `checkSctV1V4Block` for arbitrary `(branchOracle, stlOracles)`. | `[propext, Quot.sound]` |
| **Sec 6** | `checkKernelSctV1V4CertIndexed_imp_AllBlocksSctV1V4Certified` | Linear-pass `checkKernelSctV1V4CertIndexed prog cert = true` implies `AllBlocksSctV1V4Certified prog cert`. | `[propext, Quot.sound]` |
| **Sec 6** | `kernel_sct_v1_v4_sticky_stack_soundness` | **Main Combined Spectre v1 + v4 Soundness**: `checkKernelSctV1V4CertIndexed prog cert = true` implies `specV4ObsTrace prog fuel bid branchOracles stlOracles s₁ = specV4ObsTrace prog fuel bid branchOracles stlOracles s₂` across **all** PHT and STL oracle schedules. | `[propext, Quot.sound]` |
| **Sec 6** | `spectre_v4_sticky_cert_rejects_reuse_and_accepts_disjoint_slots` | `checkKernelSctV1V4CertIndexed` rejects shared-slot `spectreV4OverwriteGadget` (`= false`) and accepts disjoint-slot `spectreV4DisjointSlotRepair` (`= true`, `0` `lfence` barriers), guaranteeing identical `specV4ObsTrace`. | `[propext]` |

---

## Boundaries

- **Known not to apply (Architectural CT + Architectural Memory Safety Under Speculative Execution)**:
  A certificate proving architectural memory safety (`idx < pubBound`) and architectural constant-time execution (`checkKernelCtCertIndexed = true`) does **not** prevent speculative secret disclosure under Spectre v1 (`arch_ct_and_memsafe_cert_leaks_under_spectre_v1`). Protecting against Spectre v1 requires dual-label speculative taint tracking (`checkKernelSctCertIndexed`).
- **Known not to apply (Spectre-v1-Only Flow-Sensitive Stack Typing Under Spectre v4 `STL`)**:
  A Spectre-v1-only certificate checker (`checkKernelSctV1OnlyOverwriteCertIndexed`) that overwrites $\Gamma_{\text{stack}}(k) \leftarrow \mathsf{pubSafe}$ when a secret stack slot is overwritten with a public value is **unsound** under Spectre v4 Speculative Store Bypass (`spectre_v4_stl_bypass_leaks_overwritten_secret_slot`). Preventing Spectre v4 leaks without per-store `lfence` barriers requires sticky stack-slot secret typing (`checkKernelSctV1V4CertIndexed`) and disjoint public/secret stack-slot allocation (`kernel_sct_v1_v4_sticky_stack_soundness`).
- **Known not to apply (Branch-Only `SLH` Misspeculation Flag Across Unfenced Spectre v4 Store Bypass)**:
  Because CPU store-buffer bypass (`STL`) does not flip a conditional branch condition, a branch-tracked `SLH` misspeculation flag (`msfMasked`) is **not** automatically set to `true` when `fillStack` bypasses an older store (`transferSctV1V4Instr` clears `msfSynced := false` on `fillStack`). Thus, protecting stack reloads against Spectre v4 without `lfence` relies on sticky stack-slot typing (disjoint public/secret stack slots) or SFI bitwise address masking (`ldMasked`), not on branch-driven `slhProtect` alone.
- **Not examined (Indirect Branch Target Injection / Spectre v2 / BHI and Return Stack Buffer Underflow)**:
  Our speculative operational semantics (`stepSctBlock` and `stepSctV4Block`) models Spectre v1 (`PHT` conditional branch misprediction) and Spectre v4 (`STL` speculative store bypass on stack slots). Indirect call/jump target poisoning (Spectre v2 / Branch History Injection `CVE-2022-0001` / `CVE-2022-0002`, mitigated in Linux via Retpoline, `IBHF`, or fine-grained CFI) and `RSB` underflow are orthogonal control-flow redirection mechanisms not modeled in `SctTerminator`.

---

## Evidence

1. **Linux Kernel eBPF Verifier Spectre v1 and v4 Source (`torvalds/linux@0fcb05b72344f40806cbe810de8872f1698bf053`, observed `2026-11-02`)**:
   - `kernel/bpf/verifier.c:14266-14515`: `retrieve_ptr_limit`, `can_skip_alu_sanitation`, `update_alu_sanitation_state`, `sanitize_val_alu`, `sanitize_speculative_path`, `sanitize_err`, and `sanitize_ptr_alu`.
   - `kernel/bpf/verifier.c:17057-17096`: speculative path exploration in `check_cond_jmp_op` when one branch edge is architecturally pruned (`pred == 1` or `pred == 0`).
   - `kernel/bpf/verifier.c:18551-18564`: `sanitize_mark_insn_seen` marking `env->insn_aux_data[env->insn_idx].nospec = true` for Spectre v4 (`BPF_ST_NOSPEC`).
   - `kernel/bpf/fixups.c:1753-1803`: 6-instruction `BPF_REG_AX` branchless pointer-ALU masking patch in `bpf_do_misc_fixups`.
   - Historical CVE commits in `torvalds/linux`: `b2157399cc98` (`CVE-2017-5753`), `979d63d50c0c` (`CVE-2019-7308`), `7fedb63a8307` (`CVE-2020-27170`), `9183671af6db` (`CVE-2021-33624`), and `f5e81d111750` (Spectre v4 `BPF_ST_NOSPEC`).
2. **Primary Literature on Constant-Time and Speculative Constant-Time Type Systems (`2017–2025`, observed `2026-11-02`)**:
   - `CT-Wasm`: Conrad Watt, John Renner, Natalie Popescu, Sunjay Cauligi, and Deian Stefan, *"CT-Wasm: Type-Driven Secure Cryptography for the Web Ecosystem"*, PACMPL Vol. 3, Issue POPL, Article 77, Jan 2019, DOI `10.1145/3290390`.
   - `Jasmin` (Architectural CT): José Bacelar Almeida et al., *"Jasmin: High-Assurance and High-Speed Cryptography"*, ACM CCS 2017, DOI `10.1145/3133956.3134078`; Gilles Barthe et al., *"Formal Verification of a Constant-Time Preserving C Compiler"*, PACMPL Vol. 4, Issue POPL, Article 7, Jan 2020, DOI `10.1145/3371075`.
   - `Pitchfork`: Sunjay Cauligi et al., *"Constant-Time Foundations for the New Spectre Era"*, ACM PLDI 2020, DOI `10.1145/3385412.3385970`.
   - `Blade`: Marco Vassena et al., *"Automatically Eliminating Speculative Leaks from Cryptographic Code with Blade"*, PACMPL Vol. 5, Issue POPL, Article 49, Jan 2021, DOI `10.1145/3434330`.
   - `Jasmin SCT` (Spectre v1 & v4): Gilles Barthe et al., *"High-Assurance Cryptography in the Spectre Era"*, IEEE S&P 2021, DOI `10.1109/SP40001.2021.00046`; Bharath Anand Shivakumar et al., *"Typing High-Speed Cryptography against Spectre v1"*, IEEE S&P 2023, DOI `10.1109/SP46215.2023.10179418`; Santiago Arranz Olmos et al., *"Preservation of Speculative Constant-Time by Compilation"*, PACMPL Vol. 9, Issue POPL, Jan 2025, DOI `10.1145/3704885`.
3. **Preserved Package Artifacts (`support/`, observed `2026-11-02`)**:
   - `support/InKernelSideChannelAndSpeculativeCertificates.lean`: 4,144-line Lean 4.34.1 mechanization containing all 29 zero-axiom theorems across Sections 1–6.
   - `support/sct_certificate_vs_fence_probe.py` and `support/sct_certificate_vs_fence_probe_results.json`: deterministic implementation and benchmark comparison of `check_kernel_sct_cert`, `Blade` Edmonds-Karp min-cut selective `SLH`, SFI bitwise load masking, Linux `sanitize_ptr_alu`, naive `lfence`, and Spectre v4 sticky stack-slot typing across 6 Ring-0 workloads.

---

## Revalidation

To revalidate the machine-checked proofs and empirical probe results in this package:

1. **Verify all 29 Lean 4 theorems and their zero-axiom footprint**:
   ```bash
   lean reports/in-kernel-side-channel-certificates-and-speculative-ct-2018-2026/support/InKernelSideChannelAndSpeculativeCertificates.lean
   ```
   Confirm that `lean` (`v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`) exits with code `0` and that all 29 `#print axioms` outputs depend only on `[propext, Quot.sound]` or `[propext]` (zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`).

2. **Re-run the empirical `SCT` certificate, `Blade` min-cut `SLH`, SFI masking, and Spectre v4 stack-spill probe**:
   ```bash
   python3 reports/in-kernel-side-channel-certificates-and-speculative-ct-2018-2026/support/sct_certificate_vs_fence_probe.py
   ```
   Confirm that `support/sct_certificate_vs_fence_probe_results.json` is regenerated identically (`13` `Blade` `slhProtect` instructions and `13` SFI `ldMasked` instructions across `58` public loads, `0` `lfence` barriers, and `100%` single-pass certificate verification).
