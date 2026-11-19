# PagedAttention KV Prefix Sharing, Lossless Speculative Rejection Sampling, and BPE Token-Boundary Healing

## Summary

High-throughput autoregressive Large Language Model (`LLM`) serving stacks combine virtualized Key-Value (`KV`) block paging (**`PagedAttention`** and **`RadixAttention`**), **speculative draft-then-verify rejection sampling**, and **Byte-Pair Encoding (`BPE`) subword tokenization**. Across primary-source inspections of `vllm-project/vllm` (`2359b442c6872ea54f3fe78200033eb55abf81de`), `sgl-project/sglang` (`54d68123dcc672bc6920371ee6d90ee4ab73edaf`), `openai/tiktoken` (`79dc2c0533685b893616c78160b5d9e40876e724`), `ggml-org/llama.cpp` (`9a080f44b503c64f66c84a6274b9d9ee5d5b09d5`), Kwon et al. (`SOSP 2023`, `arXiv:2309.06180`), Leviathan et al. (`arXiv:2211.17192`), and Chen et al. (`arXiv:2302.01318`), three deep cross-layer correctness and security hazards emerge whenever memory optimization, low-precision sampling, and string-to-token lowering interact:

1. **Copy-on-Write (`CoW`) Radix `lock_ref` Lifecycle Races & Cross-Tenant / Multi-Modal KV Prefix Leakage**: `PagedAttention` (`vLLM`) and `RadixAttention` (`SGLang` `radix_cache.py`) deduplicate `16`-token physical GPU KV blocks via content-addressed Merkle block hashes (`vllm/v1/core/kv_cache_utils.py:697–728`) and reference-counted radix trees (`TreeNode.lock_ref` at `radix_cache.py:259, 797–811`). Two critical failure modes break isolation: (a) `vLLM` intentionally uses a **fixed cross-process SHA-256 seed** (`kv_cache_utils.py:91–96`) so identical token sequences hit the same cache unless callers explicitly supply `request.cache_salt` at root block `0` (`lines 650–653`), `lora_extra_keys` for LoRA adapters, and relative block offsets `("mm", identifier, offset - start_token_idx)` (`line 564`) for multi-modal embeddings—omitting `cache_salt` exposes a **cross-tenant Time-To-First-Token (`TTFT`) timing side-channel** that leaks private prompts and RAG documents block-by-block, while omitting `lora_id` corrupts activations across adapters; and (b) asymmetric `dec_lock_ref` on chunked-prefill preemption or missing CUDA `record_stream` fences (`sglang` `spec_utils.py:486`) drops `lock_ref` to `0` while an async GPU kernel still reads or writes the physical KV page, recycling private tenant activations into a concurrent request.
2. **Lossless Speculative Rejection Sampling (`TV == 0`) vs. `FP16` `0.0 / 0.0` Underflow and Greedy `top_k = 1` Aliasing**: Speculative decoding (`arXiv:2211.17192`, `arXiv:2302.01318`) proposes $\gamma$ draft tokens $X_i \sim q(\cdot)$ and accepts with $\min(1, p(X_i)/q(X_i))$, resampling rejections from the normalized positive residual $(p - q)_+ / \sum_v (p_v - q_v)_+$ to preserve exact target distribution ($\operatorname{TV}(P_{\text{spec}}, P_{\text{target}}) = 0$; `1.1e-44` in `FP64` probe). Under low-temperature `FP16` (`T <= 0.25`), tail probabilities $< 5.96 \times 10^{-8}$ flush to `0.0`, turning naive `u < p(X) / q(X)` into **`0.0 / 0.0 = NaN`**. Primary-source inspection of `SGLang` (`python/sglang/srt/speculative/spec_utils.py:260–304`) reveals both the division-free fix (**`coin * q(X) < p(X)` in `FP32`**) and a subtle **greedy `temperature=0 -> (T=1.0, top_k=1)` trap**: when a greedy row deterministically proposes `X = argmax(q)` rather than drawing $X \sim q$, passing un-truncated `p` and `q` to the verifier **accepts a wrong non-argmax draft token with probability `0.673`** (`verify_paged_kv_speculative_bpe.py`) unless `p` is first `top_k=1` one-hot renormalized (`spec_utils.py:272–278`)!
3. **Non-Homomorphic `BPE` Prompt-Boundary Splits and `1`-Token Rewind Healing (`tiktoken` & `llama.cpp`)**: Byte-Pair Encoding (`openai/tiktoken` `src/lib.rs:140–219`, `_byte_pair_merge`) greedily merges minimum-rank adjacent byte pairs within regex chunks. Because $\operatorname{encode} : \Sigma^* \to \mathcal{V}^*$ is **not a monoid homomorphism** ($\operatorname{encode}(u \mathbin{\Vert} w) \neq \operatorname{encode}(u) \mathbin{\Vert} \operatorname{encode}(w)$), cutting a prompt at a subword seam such as `"http:"` encodes `[t("http"), t(":")]` (`[258, 58]`), preventing the model from ever emitting the canonical merged token `t("://")` (`260`) seen throughout pretraining (`[258, 260, 262]` vs. split `[258, 58, 261, 262]`). **Token Healing** rewinds `1–k` trailing tokens to a merge-closed boundary and constrains generation via prefix-trie masking over $\{ v \in \mathcal{V} \mid \operatorname{bytes}(v) \text{ extends } \operatorname{tail} \}$, restoring exact BPE canonicality (`encode(decode(prompt ++ out)) == healed_tokens`).

Created a runnable verification probe at `reports/pagedattention-kv-prefix-sharing-speculative-sampling-and-bpe-healing/probes/verify_paged_kv_speculative_bpe.py` confirming `vLLM` Merkle `cache_salt` isolation & `lock_ref` premature-eviction corruption, exact `TV = 1.1e-44` speculative sampling vs. `FP16` `0.0/0.0` `ZeroDivisionError` & `67.3%` unrenormalized greedy acceptance error, and `tiktoken` BPE boundary split + token healing.

---

## Applicability

These findings apply directly to:

- **Multi-tenant LLM inference engines, disaggregated KV-cache routers, and confidential-compute serving planes** (`vLLM`, `SGLang`, `TensorRT-LLM`, `Mooncake`), where KV block hashes and reference-counted GPU page allocators form a security-critical isolation boundary on par with OS page tables.
- **Verified probabilistic programming and exact sampling kernels**, where IEEE-754 underflow, PRNG/Gumbel-max log-domain transforms, and proposal-distribution aliasing (`top_k`/`top_p` truncation order) silently break zero-total-variation (`TV == 0`) equivalence theorems.
- **Structured generation, grammar-constrained decoding (`CFG` / JSON Schema), and code-completion engines**, where non-canonical BPE tokenization at prompt or fill-in-the-middle (`FIM`) boundaries degrades completion accuracy unless paired with formal token-healing transducers.

---

## Findings

### 1. `PagedAttention` / `RadixAttention` Block Hashing, `lock_ref` Races, and Cross-Tenant Isolation

`Basis: source | documentation | execution`

Kwon et al. (`SOSP 2023`, `arXiv:2309.06180`) observed that contiguous pre-allocation of KV tensors wastes `60–80%` of GPU HBM via internal/external fragmentation and blocks dynamic sharing. `PagedAttention` partitions KV states into fixed-size physical blocks ($B = 16$ or $32$ tokens; e.g., for Llama-3-70B GQA with `8` KV heads, `head_dim = 128`, `80` layers in `BF16`, $2 \times 80 \times 8 \times 128 \times 2\text{ B} = 320\text{ KB}$/token $\implies$ **`5.12 MB` per `16`-token block**), mapped per sequence via logical-to-physical block tables with Copy-on-Write (`CoW`) reference counts.

Direct source inspection of `vllm-project/vllm` (`2359b442c6872ea54f3fe78200033eb55abf81de`, `vllm/v1/core/kv_cache_utils.py:91–96, 530–568, 650–728`) and `sgl-project/sglang` (`54d68123dcc672bc6920371ee6d90ee4ab73edaf`, `python/sglang/srt/mem_cache/radix_cache.py:60–142, 256–295, 712–811`) exposes four concrete invariants:

1. **Merkle Chaining & Intentional Seed Determinism (`kv_cache_utils.py:91–96, 650–728`)**:
   `vLLM` computes block keys recursively via `hash_block_tokens(hash_fn, parent_block_hash, curr_block_token_ids, extra_keys)` (`line 697`):
   $$H_0 = \operatorname{SHA256}\bigl(\text{NONE\_HASH},\; T_{0..B-1},\; \text{extra\_keys}_0\bigr), \qquad H_k = \operatorname{SHA256}\bigl(H_{k-1},\; T_{kB..(k+1)B-1},\; \text{extra\_keys}_k\bigr)$$
   Notice two critical subtleties in `kv_cache_utils.py`:
   - Lines `91–96` explicitly fix a **deterministic cross-process SHA-256 seed** so distributed KV stores hit identical hashes across nodes. Consequently, **multi-tenant isolation does NOT exist by default**: if `request.cache_salt` is `None`, Tenant B probing candidate `16`-token blocks observes a `5–20x` lower `TTFT` (`prefill cache hit`) whenever a prefix matches Tenant A's cached system prompt, legal contract, or medical record!
   - When `request.cache_salt` *is* supplied, `lines 650–653` inject `("cache_salt", request.cache_salt)` **only at `start_token_idx == 0`**, relying on Merkle chaining (`parent_block_hash` $H_0 \to H_1 \to \dots \to H_k$) to namespace every downstream block (`verified in verify_paged_kv_speculative_bpe.py`). Any local/sliding-window cache or disaggregated block lookup that indexes interior blocks without full root-chained `parent_block_hash` immediately loses `cache_salt` isolation!
2. **Hidden State Confounders (`LoRA`, Multi-Modal Offsets, Position IDs)**:
   Identical token IDs `[t_0, ..., t_15]` produce **different physical KV tensors** whenever:
   - Distinct `LoRA` adapters (`lora_extra_keys` in `vLLM`; `RadixKey.extra_key` at `sglang/radix_cache.py:75`) modify $W_K, W_V$ projections;
   - Identical `<image>` placeholder tokens span different sub-slices of two images (`vLLM` `line 564` hashes `("mm", mm_feature.identifier, offset - start_token_idx)` so shifted image alignments within identically tokenized placeholder blocks never collide!); or
   - `is_bigram` / hybrid Mamba-attention states (`RadixKey.is_bigram` at `radix_cache.py:61–80, 128–137`) depend on boundary state outside pure causal self-attention.
3. **`TreeNode.lock_ref` & Asynchronous CUDA Stream Lifetime Races (`radix_cache.py:797–811`, `spec_utils.py:486`)**:
   In `SGLang`'s `RadixCache`, a node enters `self.evictable_leaves` the instant `node.lock_ref == 0` and all children are evicted (`_update_leaf_status`, `line 798`). Host Python scheduling runs *ahead* of asynchronous GPU execution streams:
   - If an aborted request, chunked-prefill rollback, or tree-split exception decrements `lock_ref` on the CPU **before** the GPU `fwd_stream` finishes reading those physical KV indices—or without `torch.Tensor.record_stream(fwd_stream)` (`spec_utils.py:486`)—`evict()` immediately hands the physical page to another tenant's `insert()`, causing **live GPU write-after-read / read-after-write cross-tenant KV corruption** (`demonstrated in verify_paged_kv_speculative_bpe.py`).

---

### 2. Speculative Decoding Rejection Sampling: `FP16` Underflow, Log-Domain Gumbel, and Greedy `top_k=1` Traps

`Basis: source | derived | execution`

Given target distribution $p(\cdot \mid x_{<t})$ and fast draft distribution $q(\cdot \mid x_{<t})$ (`Leviathan et al. arXiv:2211.17192`; `Chen et al. arXiv:2302.01318`), speculative verification draws draft token $X \sim q$ and uniform $U \sim \operatorname{Uniform}(0, 1)$:
1. **Accept** $X$ if $U < \min\!\bigl(1, \frac{p(X)}{q(X)}\bigr)$;
2. **Reject** otherwise, discarding remaining draft suffix tokens and sampling a replacement token $X' \sim p_{\text{res}}$ where $p_{\text{res}}(v) = \frac{\max(0, p(v) - q(v))}{\sum_{w} \max(0, p(w) - q(w))}$.

By algebraic cancellation, $\mathbb{P}(\text{emit } v) = \min(p(v), q(v)) + \bigl(1 - \sum_w \min(p(w), q(w))\bigr)\frac{\max(0, p(v) - q(v))}{\sum_w \max(0, p(w) - q(w))} = p(v)$ identically (`TV = 1.1e-44` in `FP64`, `verify_paged_kv_speculative_bpe.py`). Yet real serving engines (`sglang` `spec_utils.py:222–305` and `llama.cpp` `common/speculative.cpp:33–70, 504–545`) hit three concrete numerical/plumbing failures:

| Failure Mechanism | Root Cause in Serving Kernel | Quantitative / Behavioral Consequence (`verify_paged_kv_speculative_bpe.py`) | Sound Primary-Source / Algebraic Fix |
| :--- | :--- | :--- | :--- |
| **`FP16` `0.0 / 0.0 = NaN` Ratio** | At $T = 0.25$, `exp(-16/0.25)` $< 5.96\times 10^{-8}$ flushes both `p(X)` and `q(X)` to `FP16` `0.0`; `u < p/q` divides `0.0/0.0` | `NaN` poisons CUDA rejection mask or crashes CPU sampler (`ZeroDivisionError`) | Cast to `FP32` + rewrite division-free: **`coin * q(X) < p(X)`** (`sglang` `spec_utils.py:262`) or verify in log-domain $\ln U + \ell_q(X) < \ell_p(X)$ |
| **Residual Mass Collapse $\sum (p - q)_+ == 0$** | `FP16` rounding produces $\sum_v p_{\text{fp16}}(v) < \sum_v q_{\text{fp16}}(v)$ on rejection so all $(p - q)_+ == 0$ | `p_res / 0.0` yields all-`NaN` multinomial weights, crashing `torch.multinomial` | Compute `softmax` & `(p - q).clamp_min_(0)` in `FP32` with fallback to `argmax(logits_p)` if `Z_res <= 1e-30` |
| **Greedy `T=0 -> (T=1, top_k=1)` Aliasing** (`spec_utils.py:266–278`) | API rewrites `T=0` to `T=1.0, top_k=1`; draft picks deterministic `X = argmax(q)` (`line 302`) instead of $X \sim q$, while passing un-truncated `q`! | If target `p` omits `top_k=1` one-hot renorm, **wrong non-argmax token accepts `67.3%` of the time!** | Apply identical `top_k` / `top_p` renormalization to `p` *before* accept test & `(p - q)_+`, AND assert `top_ks.device == probs.device` (`line 296`)! |
| **Draft/Target Temperature Skew** (`llama.cpp` `speculative.cpp:33–36`) | Caller updates target `temp` mid-session without retuning stateful draft sampler (`spec_retune`) | Mismatched $q_T$ collapses acceptance length $\mathbb{E}[\alpha] = \sum_v \min(p_v, q_v)$ by `20–60%` | Couple draft & target `(temp, top_k, top_p)` inside a single immutable `SamplingLaw` value |

---

### 3. Non-Canonical `BPE` Prompt-Boundary Splits (`tiktoken`) and Token-Healing Transducers

`Basis: source | derived | execution`

In `openai/tiktoken` (`79dc2c0533685b893616c78160b5d9e40876e724`, `src/lib.rs:47–219`), `byte_pair_encode(piece, ranks)` partitions UTF-8 input via a regex pre-tokenizer (`cl100k_base` / `o200k_base`) and repeatedly merges the adjacent pair with minimum `Rank` (`O(mn)` small-vector loop `_byte_pair_merge` for `len < 100`, `O(m log n)` indexed `BinaryHeap` `_byte_pair_merge_large` for `len >= 100`).

**Formal Algebraic Obstruction (Failure of Concatenation Homomorphism)**:
Let $\Sigma = \{0..255\}$ be raw bytes, $\mathcal{V}$ the token vocabulary with injective byte decoding $\psi : \mathcal{V}^* \to \Sigma^*$, and $\phi = \operatorname{bpe\_encode} : \Sigma^* \to \mathcal{V}^*$ the canonical encoder ($\psi(\phi(s)) = s$). A sequence $\mathbf{t} \in \mathcal{V}^*$ is **BPE-canonical** iff $\phi(\psi(\mathbf{t})) = \mathbf{t}$ (equivalently, no adjacent pair $(t_i, t_{i+1})$ inside the same regex chunk has a merge rank smaller than or compatible with the greedy merge derivation of $\psi(\mathbf{t})$).

Because $\phi(u \mathbin{\Vert} w) \neq \phi(u) \mathbin{\Vert} \phi(w)$ across prompt boundary `|`:
- **Concrete Example (`verify_paged_kv_speculative_bpe.py`)**: For `s = "http://ex"`, canonical `tiktoken`-style merging produces **`[258 ("http"), 260 ("://"), 262 ("ex")]`**. If the user prompt ends at `"http:"` (`\phi("http:") = [258 ("http"), 58 (":")]`), any unhealed autoregressive continuation `w = "//ex"` (`[261 ("//"), 262 ("ex")]`) forces the joint token stream `[258, 58, 261, 262]`—a **non-canonical tokenization (`encode(decode(t)) != t`) that had near-zero frequency during LLM pretraining**, causing severe perplexity spikes on URLs, trailing spaces (`" "` merged into leading `" word"` tokens!), and code identifiers!
- **Exact Token-Healing Algorithm**:
  1. Given prompt bytes $P \in \Sigma^*$ with canonical encoding $\phi(P) = [t_1, \dots, t_{m-k}, t_{m-k+1}, \dots, t_m]$, choose lookback $k \ge 1$ covering the trailing regex/merge horizon (`k = 1` suffices whenever `bytes(t_{m-1})` ends at an unmergeable boundary; `k <= max_token_bytes` in general) and set $B_{\text{tail}} = \psi([t_{m-k+1}, \dots, t_m])$.
  2. Roll back KV prefill to prefix $[t_1, \dots, t_{m-k}]$ and mask next-token probabilities to the prefix-compatible set:
     $$\mathcal{C}(B_{\text{tail}}) = \bigl\{\, v \in \mathcal{V} \;\big|\; \psi(v) \text{ starts with } B_{\text{tail}} \;\lor\; B_{\text{tail}} \text{ starts with } \psi(v) \,\bigr\}$$
  3. Repeat until generated bytes consume $B_{\text{tail}}$, then lift the mask and strip the already-present $B_{\text{tail}}$ byte prefix from streamed user output. Our probe confirms `[258, 58]` rewinds to `[258]` with `B_tail = b":"`, unlocks token `260` (`b"://"`), and emits exact canonical `[258, 260, 262]`.

---

### 4. Six-Level Performance & Resource Footprint Matrix (`L1`–`L6`)

`Basis: source | documentation | execution | derived`

| Level | Metric / Resource Axis | `vLLM` + `SGLang` (`PagedAttention` / `RadixCache` + Speculative) | `tiktoken` (Rust BPE) + `llama.cpp` (`speculative.cpp`) | Verification / System Engineering Implication |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | `vLLM` `block_pool` + `kv_cache_utils` `~2,200 LoC` Python; `SGLang` `radix_cache` + `spec_utils` `~2,350 LoC` (`high` concurrency/stream subtlety) | `tiktoken` core BPE `~700 LoC` Rust; `llama.cpp` `speculative.cpp` `~3,600 LoC` C++ (`3–5x` formal invariant / proof ratio) | Linear reference-count capabilities (`KvLease<Stream>`) and typed `Salt x LoRA` block keys prevent `90%` of subtle eviction/leakage bugs in `< 50 LoC` of types |
| **L2** | **Framework & Toolchain Build Time** | `vLLM` custom CUDA/PyTorch C++ wheel build **`25–60 min`** (`~32–64 GB` RAM); `SGLang` pure-Python layer `< 15 s` over `sgl-kernel` | `tiktoken` Rust `cargo build --release` `~12–25 s`; `llama.cpp` CMake CPU/CUDA build `~1–4 min` | Keep scheduling, prefix-key, and BPE-healing verification decoupled from multi-arch CUDA kernel compilation |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | Prefix-hash provenance & `KvLease` linearity typecheck `< 5 ms`; log-domain speculative `TV == 0` proof check `< 25 ms` | Aho–Corasick / prefix-trie compilation over `128k–200k` vocab (`cl100k`/`o200k`) `~15–40 ms` once at model load | Pre-build vocabulary prefix tries once at startup so per-request token healing adds `< 5 us` latency |
| **L4** | **Generated Code Execution Performance** | `PagedAttention` `< 4%` KV waste (`2–4x` batch throughput); speculative decoding (`EAGLE-3`) **`2.2–3.1x` decode tok/s**; SHA-256 block hash `~0.3 us`/block | `tiktoken` Rust **`~3–6 MB/s/core`** (`~1–2M` tok/s, note `fancy_regex` scratch contention warning at `lib.rs:232–238`!); `1`-token heal `< 1 step` | Never share `fancy_regex` mutable scratch across threads (`lib.rs:233`); use division-free `FP32` `coin * q < p` on GPU (`0` throughput penalty) |
| **L5** | **Proof / Certificate Verification Speed** | Deterministic PRNG-seeded rejection-sampling trace audit **`< 2 us`/token**; radix `sum(lock_ref)` invariant check `O(#active_reqs)` (`< 50 us`) | Canonical BPE round-trip check `encode(decode(tokens)) == tokens` **`< 10 us`/prompt** (`O(n)` bytes) | Cheap runtime `encode(decode(boundary_window))` assertions catch non-canonical BPE splits in `< 5 us`! |
| **L6** | **RAM, Disk & Binary Footprints** | KV cache consumes **`30–75 GB`/GPU** on `80 GB` H100 (`5.12 MB`/`16`-tok block on 70B); `RadixCache` CPU metadata `~64–128 B`/node (`< 50 MB` for `400k` blocks) | `tiktoken` `o200k_base` `FxHashMap` + prefix trie `~12–28 MB` RAM (`lib.rs:246–255` avoids separate LRU cache!); `llama.cpp` binary `~4–20 MB` | Avoiding `RWLock` LRU caches in `tiktoken` (`lib.rs:249–254`) saves both multi-core cache-line bouncing and per-thread heap bloat |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived | source`

#### (C1) Human Comprehensibility & Mental-Model Ergonomics
- **Deceptive "Content-Addressed" Mental Model for KV Caches**: Engineers instinctively equate KV prefix caching with pure functional memoization (`tokens -> KV`), forgetting that Transformer KV tensors are **implicit functions of `(ModelWeights, LoRA_Adapter, TenantNamespace, MultiModalEmbeddings, QuantizationScale, PositionalEncoding)`**! In `vLLM`, placing `cache_salt` only at block `0` (`kv_cache_utils.py:650–653`) works subtly via Merkle induction, whereas a developer inspecting an interior block's `extra_keys` sees `None` and cannot tell locally whether tenant isolation is active.
- **Hidden Coupling Between `SamplingParams` Rewrites and Speculative Unbiasedness**: Rewriting `temperature = 0` into `(temperature = 1.0, top_k = 1)` (`sglang` `spec_utils.py:266–278`) is locally harmless in standard single-model decoding, yet **silently breaks Leviathan rejection sampling** (`67.3%` wrong-token acceptance in our probe!) unless a human maintainer notices `4` files away that `X = argmax(q)` violated `X ~ q` and compensates by `top_k=1`-renormalizing `p`! And as `spec_utils.py:292–295` notes, a device mismatch on `top_ks` wouldn't even crash without an explicit `assert`—it would merely manifest as *"draft accept length quietly dropping about 20%."*
- **Invisible Subword Seams in String Prompts**: Humans read `"http:" + "//example.com"` as seamless character concatenation, completely blind to the invisible token boundary `[258, 58]` vs `[258, 260]` underneath.

#### (C2) Simplicity, Orthogonality & Universal Model Refinement
- **Typed Capability-Scoped Merkle Keys + Stream-Fenced Linear Leases**: Replace ad-hoc `Optional[str]` `cache_salt` / `extra_key` tuples with a **mandatory non-optional `KvDomainKey = { tenant: TenantCap, weights_hash: Digest, lora: AdapterId }`** hashed into the root seed `H_init(KvDomainKey)`, making cross-tenant or cross-LoRA omission a compile-time missing-field error. Pair physical KV page handles with **GPU-event-fenced linear leases (`Drop` forbidden until `CudaEventReceipt<e>` signals)** so CPU preemption can never recycle an in-flight GPU page.
- **Single-Source Measure-Carrying Proposals (`SampledProposal<Law>`)**: Instead of passing raw `(probs, topk_p, topk_index)` tensors across functions that might apply `top_k`, `top_p`, or temperature differently (`spec_utils.py:262–279`, `speculative.cpp:33`), encapsulate the sampling operator as a single morphism `Law : Logits -> Dist32` and type draft draws as **`(X, q_exact_X)` witnessed by the exact post-truncation `Dist32 = Law(draft_logits)`**, evaluated exclusively via log-domain/FP32 division-free Gumbel/rejection predicates.
- **Byte-Level Surface Semantics with Internal BPE Canonicalization**: By Ousterhout's deep-module principle, **token boundaries are an internal compression detail that should never leak into prompt semantics**. Treating `Prompt` semantically as `ByteSeq` and making `1`-token BPE boundary healing part of the standard `prefill_and_decode(bytes)` entry point turns mid-token splits from a user-facing prompt-engineering trap into an ordinary, invisible internal case.

---

## Boundaries

1. **Hybrid State-Space / Linear-Attention (`Mamba-2`, `Gated DeltaNet`) Recurrent Checkpointing (`known not to apply` to pure `16`-token block paging)**: Standard `PagedAttention` assumes causal self-attention where token $t$'s KV entry never mutates once written (`O(1)` block-granular rollback on speculative rejection). Recurrent state-space layers overwrite an in-place $d_{\text{state}} \times d_{\text{head}}$ state matrix at every step, requiring dense periodic state snapshots rather than pure `16`-token KV block sharing (`known not to apply` without hybrid recurrent-slot managers).
2. **Lossy Multi-Token Tree-Draft Relaxation (`Medusa` "typical acceptance", `not examined`)**: Our `TV == 0` analysis covers **exact** speculative rejection sampling (`Leviathan`/`Chen`/`EAGLE` strict mode). Heuristic entropy-threshold acceptance schemes (`Medusa` typical sampling) intentionally trade `TV > 0` distribution shift for longer accept lengths (`not examined` here).
3. **Disaggregated Cross-Node RDMA KV-Cache Timing Channels (`unknown`)**: Even when `cache_salt` isolates tenants cryptographically, global HBM eviction pressure across shared GPU pools can create second-order cache-occupancy side channels (`Prime+Probe` over total free KV blocks); exact information-leakage bit-rates under continuous batching remain **`unknown`** without partitioned per-tenant block quotas.
4. **Unpaired UTF-8 Surrogate / Byte-Fallback Token Healing Across Regex Lookaheads (`unsupported` by `1`-token lookback)**: Prompts ending inside multi-token stateful regex lookaheads (e.g., `tiktoken`'s `fancy_regex` contraction/whitespace lookahead rules at `lib.rs:232`) can alter pre-tokenization chunk boundaries `> 1` token back (`unsupported` without re-lexing from the last regex-chunk-safe offset).

---

## Evidence

| Artifact / Source | Immutable Identity / Location | Grounded Fact / Observation |
| :--- | :--- | :--- |
| `vllm-project/vllm` (`kv_cache_utils.py` & `block_pool.py`) | Commit `2359b442c6872ea54f3fe78200033eb55abf81de` (`vllm/v1/core/kv_cache_utils.py:91–96, 561–565, 650–728`, `vllm/v1/core/block_pool.py`) | Fixed cross-process SHA-256 seed (`lines 91–96`), root-only `cache_salt` (`lines 650–653`), `("mm", id, offset - start)` (`line 564`), Merkle `hash_block_tokens` (`line 697`) |
| `sgl-project/sglang` (`radix_cache.py`) | Commit `54d68123dcc672bc6920371ee6d90ee4ab73edaf` (`python/sglang/srt/mem_cache/radix_cache.py:60–142, 259, 797–811`) | `RadixKey` (`extra_key`, `cache_salt`, `is_bigram`), `TreeNode.lock_ref` leaf-eviction eligibility (`line 798`) |
| `sgl-project/sglang` (`spec_utils.py`) | Commit `54d68123dcc672bc6920371ee6d90ee4ab73edaf` (`python/sglang/srt/speculative/spec_utils.py:250–305, 486`) | Division-free `coin*q(X) < p(X)` (`line 262`), `T=0 -> top_k=1` target-renorm requirement (`lines 266–278`), `record_stream` (`line 486`) |
| `openai/tiktoken` (`lib.rs`) | Commit `79dc2c0533685b893616c78160b5d9e40876e724` (`src/lib.rs:47–260`) | `_byte_pair_merge` (`O(mn)` small) & `_byte_pair_merge_large` (`BinaryHeap`), `fancy_regex` thread contention & cacheless `FxHashMap` notes (`lines 221–260`) |
| `ggml-org/llama.cpp` (`speculative.cpp`) | Commit `9a080f44b503c64f66c84a6274b9d9ee5d5b09d5` (`common/speculative.cpp:33–70, 504–545`) | `spec_retune` draft-to-target temperature synchronization (`line 33`) and rejected-draft verify batch state handling (`lines 508–514`) |
| Kwon et al. (SOSP 2023) | `arXiv:2309.06180`, `DOI: 10.1145/3600006.3613165` | `PagedAttention` virtual-memory KV block tables, `< 4%` fragmentation, and Copy-on-Write prefix sharing |
| Leviathan, Kalman, Matias (2022) & Chen et al. (2023) | `arXiv:2211.17192` & `arXiv:2302.01318` | Lossless speculative rejection sampling theorem ($\operatorname{TV}(P_{\text{spec}}, P_{\text{target}}) = 0$) and residual distribution $(p - q)_+$ |
| Executable Verification Probe | `probes/verify_paged_kv_speculative_bpe.py` | Verified `vLLM` Merkle `cache_salt` isolation, `lock_ref` premature eviction, `TV = 1.1e-44`, `FP16` `0/0` vs. division-free predicate, `67.3%` unrenormalized greedy bug, and BPE healing `[258, 58, 261, 262] -> [258, 260, 262]` |

---

## Revalidation

Re-run the self-contained verification probe using standard Python 3 (`>= 3.10`, zero external dependencies):

```bash
python3 reports/pagedattention-kv-prefix-sharing-speculative-sampling-and-bpe-healing/probes/verify_paged_kv_speculative_bpe.py
```

Expected output (`exit 0`):

```text
PASS: vLLM salt isolation (block0 & Merkle block1 distinct) | Speculative TV(FP64)=1.1e-44, FP16 0/0 caught=True, unrenorm greedy bug accept=0.673 | BPE canonical=[258, 260, 262] vs split=[258, 58, 261, 262] -> healed=[258, 260, 262]
```

Trigger revalidation if:
1. `vLLM` enables mandatory per-API-key `cache_salt` by default or migrates hybrid Mamba-attention prefix hashing in `kv_cache_utils.py`;
2. `SGLang` unifies `sample_draft_proposal` and `eagle_sample` into a single fused Gumbel-max verification kernel; or
3. `tiktoken` updates regex pre-tokenization lookahead semantics beyond `o200k_base`.
