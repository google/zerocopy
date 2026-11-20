# Naming pieces created inside parallel tasks: DPJ region path lists, Legion/Regent partition trees, fork-path task identities, and splittable generator keys

## Summary

- **One shape, four realizations.** Every examined system names a piece produced by dividing a resource (memory, a task identity, a random stream) by a *path from a root*, and decides "these two pieces cannot overlap" by finding where two paths diverge. DPJ region path lists (`Root:A:[i]`), Legion region trees (region → partition → subregion), Cilk pedigrees (rank sequences) and MPL's fork-path task ids (bit strings) are all such paths; splittable generators (SplitMix, JAX keys) derive a child's state from the parent's state plus a branch label.
- **Disjointness is decided by divergence, and only certain divergences count.** DPJ: two RPLs are disjoint if a constraint says so, if their last elements are distinct, or if they share a prefix and then diverge at distinct names or provably different indices; `*`, region parameters and final-variable ("z region") heads never prove disjointness. Legion: walk both index spaces up to the same depth and then to a common parent; if that parent partition is *disjoint* and the children differ, they are disjoint; otherwise an expensive set intersection runs (or, when independence tests are disabled, the pair is conservatively treated as intersecting).
- **Partitioning inside a task and reassembling works when the pieces are *views* whose names are not provably disjoint from the parent's name.** Rust's `split_at_mut` does this with lifetimes (compile errors `E0524`, `E0500` observed against rayon at the pinned revision), so reassembly needs no operation. DPJ's `Partition.get` returns `ArraySlice<T,this:[idx]:*>`: by the checker's rules two segments of one partition object are disjoint and segments of different partition objects are not provably disjoint; whether a segment is provably disjoint from the root slice depends on how the root slice's region is written (a region parameter: no; an RPL starting with `Root`: the literal head rule says yes — an open soundness question recorded under Boundaries, not compiled).
- **Freshness of generated names and keys assumes linear use, and nothing enforces it by default.** Reusing a name supply yields the same name; reusing a SplitMix generator after `splitSMGen` reproduces the left child's stream shifted by two outputs (port, validated against upstream doctests); JAX's split and sample on the same key evaluate the same Threefry hash on the same counters, so a sample is an exact XOR of the two children's words. JAX's key-reuse checker is experimental and off by default, tracks only typed keys, and by design treats `fold_in` and `wrap_key_data` outputs as fresh.
- **Capacity limits are part of the identity scheme.** MPL fork-path ids stop at tree depth 31 (in entanglement-detecting builds the scheduler declines to spawn deeper); OpenCilk Cheetah's pedigree DPRNG table has 4096 entries and the spawn path indexes it by spawn depth with no bounds check in the examined runtime sources.

## Applicability

- **Subjects examined (source):** `dpj/DPJ` @ `bffe77a8e83ddb82a59d50f24435081b7c762f40` (compiler `code/RPLs.java`, `code/RPLElement.java`, `code/Effect.java`; runtime `Implementation/Runtime/dpj/{Partition,ArraySlice}.java`, `Framework/DisjointArray.java`); `StanfordLegion/legion` @ `aea587e157abff12f7d089c81f29cd3a8b993a2b` (Regent `language/src/regent/{type_check,std,check_parallelizable}.t`; runtime `runtime/legion/nodes/index.cc`, `api/runtime.h`, `kernel/runtime.cc`); `rayon-rs/rayon` @ `599425d4a4c64714632817f48496dbc53f656a90` (`rayon-core/src/join/mod.rs`, `src/slice/{mod,chunks}.rs`, `src/iter/plumbing/mod.rs`); `OpenCilk/cheetah` @ `33ac0d586cdbafe4e400f3741c4ce4ff07e61c26` (`runtime/pedigree-internal.h`, `runtime/pedigree_{ext,lib,globals}.cpp`, `include/cilk/cilk_api.h`, `runtime/CMakeLists.txt`); `haskellari/splitmix` @ `66ca2edbe935582cb66fd1fd36d1cd06366d9779` (`src/System/Random/SplitMix.hs`, `README.md`, `Changelog.md`); `jax-ml/jax` @ `715e767052bc29ff65400e576b58dc37d1ad179f` (`docs/jep/263-prng.md`, `docs/jep/9263-typed-keys.md`, `jax/experimental/key_reuse/{__init__,_core}.py`, `tests/key_reuse_test.py`, `jax/_src/random/{threefry2x32,prng}.py`, `jax/_src/config.py`); `MPLLang/mpl` @ `254325b5946f609f76458f0d9509a3206e0521cd` (`runtime/gc/decheck.c`, `basis-library/schedulers/spork/Scheduler.sml`) as a second fork-path identity scheme.
- **Executed:** rustc/cargo 1.102.0-nightly (3ef0c22cd 2026-11-11) compiling small crates against rayon from the pinned tarball (with crossbeam-deque 0.8.8, crossbeam-epoch 0.9.21, crossbeam-utils 0.8.23, either 1.19.0 resolved offline). Python 3.13.15 running two **ports** written for this report: a SplitMix port validated against the upstream doctest vectors, and a port of MPL's fork-path bit formulas. Neither port is the upstream package; claims from them are labelled.
- **Not executed:** DPJ compiler, Regent/Legion, OpenCilk (no toolchain), JAX (not installed). Findings on those are from source and documentation.
- **Relationship among subjects:** comparison of mechanisms for one problem — naming divided resources so that non-overlap (of storage, identity, or randomness) can be decided without shared state — across languages (DPJ, Regent, Rust), runtimes (Legion, Cheetah, MPL) and generator libraries (splitmix, JAX).

## Findings

### 1. The common structure

Basis: derived from §§2–6.

| System | Root | Child name | Disjointness / freshness decision | Who guarantees the pieces really are disjoint |
| --- | --- | --- | --- | --- |
| DPJ | `Root` | `P:[i]` (array index), `A:B` (nested names) | divergence after a common prefix, or distinct last elements, or declared constraint | type checker for names; trusted library casts for `Partition` segments |
| Regent / Legion | logical region | `p[i]` subregion of partition `p` | common parent partition marked disjoint ⇒ disjoint; else set intersection | Regent: by construction (equal, by-field) or by annotation; runtime: geometric test or `-lg:partcheck` |
| Cilk pedigree | root strand | rank sequence ⟨r₁,…,r_d⟩ | sequences differ ⇒ distinct strands; hashed by DotMix | runtime bookkeeping at spawn/sync |
| MPL decheck | path `1` | bit string with sentinel | LCA by bit tricks + sync-depth table | runtime, only in entanglement-detecting builds |
| Name supply / SplitMix / JAX key | seed | `split` children | different derivation paths ⇒ different states (with high probability for hashes) | programmer discipline (linear use); JAX optional checker |

### 2. DPJ region path lists (`dpj/DPJ` @ `bffe77a8e83ddb82a59d50f24435081b7c762f40`; Bocchino et al., OOPSLA 2009, `10.1145/1640089.1640097`)

Basis: source + derived.

- **Disjointness decision** (`RPLs.java` lines 57–84):

  ```java
  // If rpl1 and rpl2 are included in disjoint RPLs, then they are disjoint.
  for (Pair<RPL,RPL> constraint : constraints) { ... return true; }
  // DISJOINT-RIGHT-1
  if (rpl1.elts.last().isDisjointFrom(rpl2.elts.last(), this, constraints)) return true;
  // DISJOINT-RIGHT-2
  if (areDisjointFromRight(rpl1, rpl2, constraints)) return true;
  // DISJOINT-LEFT
  if (areDisjointFromLeft(rpl1, rpl2, constraints) ||
      areDisjointFromLeft(bound1, bound2, constraints)) return true;
  return false;
  ```

  `areDisjointFromLeft` (lines 86–118) returns `true` if `rpl1`'s head reports itself disjoint from `rpl2`'s head, `false` if the heads are otherwise unequal, and for equal heads scans the tails pairwise: a `*` on either side returns `false`; reaching the end of one list returns `true`; a pair of disjoint elements returns `true`. `areDisjointFromRight` (lines 120–134) scans from the end, stopping with `false` at any `*`.
- **Element-level rules** (`RPLElement.java`): `STAR.isDisjointFrom` → `false` (line 117); two region names are disjoint iff they are different symbols (line 151); region parameters → `false` (line 201); an array index element is disjoint from any non-index element it neither includes nor is included in, and from another index element iff `areNeverEqualExprs(indexExp, …)` (lines 246–253, a syntactic test over literals, identifiers and binary expressions); final-variable "z region" elements (including `this`) → `false` (line 339); `Root` is disjoint from every element other than `Root` itself (`return e != ROOT_ELEMENT;`, lines 81–88). For an RPL whose head is a z region, `RPL.upperBound()` substitutes the variable's owner region followed by `*` (`RPL.java` lines 174–182), and `areDisjoint` also tries DISJOINT-LEFT on these bounds.
- **Aliased versus disjoint** is therefore *not* a property of a partition in DPJ but of the two names compared: `R:[i]` vs `R:[j]` are disjoint only if `i` and `j` are provably never equal; anything under `*` is potentially aliased.
- **Partitioning inside a task** uses the runtime library, not the type checker. `Partition.java` lines 58–68 build the segments with unchecked casts, e.g. `segs[0] = (ArraySlice<T,this:[0]>) A.subslice(0, idx);`. The split-point constructor checks monotonicity dynamically (throws `ArrayIndexOutOfBoundsException` when a segment length is negative). Segments are retrieved by

  ```java
  public ArraySlice<T,this:[idx]:*> get(final int idx)
  	reads this:[idx]
  ```

  (lines 191–192). Applying the rules above by hand (derived; not compiled): for one partition object `P`, `P:[0]:*` and `P:[1]:*` are disjoint by DISJOINT-LEFT (equal head `P`, then indices `0`/`1`); for two partition objects `P1`, `P2` — even over the same slice — `P1:[0]:*` vs `P2:[1]:*` is *not* provable (the trailing `*` defeats both right rules and the heads `P1`, `P2` are z regions whose `isDisjointFrom` is `false`); and when the root slice's region is a region parameter `R` (`ArraySlice.put` has effect `writes R`, `ArraySlice.java` line 110), `R` vs `P:[0]:*` is not provable either (parameter heads never separate; the bound of `P:[0]:*` begins with the owner region and `*`). So in generic code a task may split, recurse in parallel on the segments of one partition, and afterwards use the root slice again, while concurrent use of root and segments, or of segments of two partitions, is rejected. If instead the root slice's region is a concrete RPL such as `Root:A`, a literal application of `areDisjointFromLeft` compares the heads `Root` and `P` first, and `ROOT_ELEMENT.isDisjointFrom` returns `true` for any non-`Root` element, so the quoted code would report `Root:A` and `P:[0]:*` disjoint unless effect computation rewrites z-region heads before this test; this was not determined (see Boundaries). The element test is also not symmetric for this pair — `ROOT_ELEMENT.isDisjointFrom(P)` is `true` but `VarRPLElement.isDisjointFrom(Root)` is `false` — and `areDisjoint` applies the head and last-element tests only as `rpl1 … isDisjointFrom(rpl2 …)`, so by hand `areDisjoint(Root:A, P:[0]:*)` evaluates to `true` while `areDisjoint(P:[0]:*, Root:A)` evaluates to `false` (assuming the variable's owner region is `Root:A`). The obligation left to the library in every case is that the casts in the constructor describe genuinely non-overlapping subslices.

### 3. Legion and Regent partition trees (`StanfordLegion/legion` @ `aea587e157abff12f7d089c81f29cd3a8b993a2b`; Bauer et al. SC 2012 `10.1109/SC.2012.71`; Treichler et al. OOPSLA 2013 `10.1145/2509136.2509545`; Treichler et al. OOPSLA 2016 `10.1145/2983990.2984016`)

Basis: source + documentation.

- **Partition kinds in Regent's types:** `std.disjoint` / `std.aliased` (`std.t` lines 2727–2728) are part of the partition type `std.partition(disjointness, completeness, region_symbol, colors_symbol)` (line 2735 onward). Operators that are disjoint *by construction*: `partition(equal, …)` (`type_check.expr_partition_equal`, line 1780) and partition by field (`expr_partition_by_field`, line 1840). Operators that default to aliased unless the program annotates them: `restrict` (line 1867), `image` (line 1961); `preimage` inherits the source partition's disjointness for pointer fields and defaults to aliased for `rect` fields (lines 2240–2242). A cast between disjoint and aliased partition types is a type error (lines 1484–1486).
- **Static disjointness facts:** indexing a disjoint partition at an analyzable (constant/affine) index adds pairwise disjointness constraints with other constant subregions whose indices `affine_helper.analyze_index_noninterference` separates (`type_check.t` lines 642–651, 676–681). Dynamic indices produce `subregion_dynamic()` with only subregion constraints. Freshly created regions are recorded as disjoint from all existing regions with the same field space (lines 1625–1634).
- **Runtime decision** (`nodes/index.cc` lines 1629–1667): if two index spaces are in the same tree, bring both to the same depth by stepping `parent->parent` (index space → partition → index space), walk up until their parents coincide; "If they have the same parent and it's not nullptr and it is disjoint then they don't intersect if they are different"; "Otherwise fall through and do the expensive test", which computes `intersect_index_spaces(this, rhs)` unless `compute` is false, in which case the pair is reported as intersecting. `IndexPartNode::are_disjoint` (lines 2839–2870) short-circuits on a disjoint partition and memoizes pairwise answers in `disjoint_subspaces` / `aliased_subspaces`; the caller passes `!runtime->disable_independence_tests` as `compute` (line 2861).
- **Trust in annotations:** `api/runtime.h` lines 4532–4540: "`-lg:partcheck` This flag will ask the runtime to dynamically verify that all correctness properties for partitions are upheld. This includes checking that the parent region dominates all subregions and that all annotations of disjointness and completeness from the user are correct. This is an expensive test …"; `-lg:disjointness` is a synonym (`kernel/runtime.cc` lines 11157–11158). Without the flag, a wrong `disjoint` annotation is trusted by both the type checker and the region-tree short-circuit.
- **Partition then reassemble:** subregions are nodes below their parent in the same tree, so using the parent after child tasks finish is ordinary; concurrent use of parent and child is ordered by the runtime's dependence analysis on the region tree (privileges on a parent cover its subregions). The examined sources do not show a separate "reassembly" operation; none is needed.

### 4. Fork-path task identities

Basis: source + documentation + execution (MPL port only).

- **Cilk pedigrees and DotMix** (Leiserson, Schardl & Sukha, PPoPP 2012, `10.1145/2145816.2145841`): a strand is identified by the sequence of ranks along its spawn path; DotMix compresses the pedigree by a dot product with a random coefficient vector modulo a prime and then applies a nonlinear mixing function. Cheetah implementation:
  - `pedigree_ext.cpp` lines 5–36, on spawn: child `pedigree.rank = parent_frame->rank`, child `rank = 0`, `frame->dprng_depth = parent_frame->dprng_depth + 1;` (line 25), child dot product `+= __pedigree_dprng_m_array[frame->dprng_depth]` (line 29), then `parent_frame->rank++` (line 32) with the parent's dot product updated likewise. On sync (lines 45–51): `rank++` and dot product update. `__cilkrts_get_dprand` bumps the rank and returns `mix_mod_p(dprng_dotproduct)` (`pedigree_lib.cpp`).
  - Modulus `DPRNG_PRIME = (uint64_t)(-59)`, i.e. `2^64 − 59` (`pedigree-internal.h` line 8). Coefficients come from a fixed default seed `0x8c679c168e6bf733` (`pedigree_lib.cpp` line 9) unless `__cilkrts_dprand_set_seed` is called.
  - **Table size versus depth (upstream defect candidate; source-derived, not executed):** `pedigree_lib.cpp` lines 31–39:

    ```cpp
    __pedigree_dprng_m_array =
        (uint64_t *)malloc(sizeof(uint64_t *) * 4096);
    ...
    for (int i = 0; i < 4096; i++) {
        __pedigree_dprng_m_array[i] =
            __cilkrts_dprng_mix_mod_p(__pedigree_dprng_seed + i);
    }
    ```

    and `pedigree_ext.cpp` lines 25 and 28–29:

    ```cpp
    frame->dprng_depth = parent_frame->dprng_depth + 1;
    ...
    frame->dprng_dotproduct = __cilkrts_dprng_sum_mod_p(
        parent_dprng_dotproduct, __pedigree_dprng_m_array[frame->dprng_depth]);
    ```

    A search of `runtime/` for `dprng_depth` finds only these uses and the field declaration; none compares it with 4096. A spawn nesting depth of 4096 or more would therefore read past the 4096-entry table. Pedigrees are opt-in: "Linking this code with a Cilk program enables pedigrees" (`pedigree_lib.cpp` line 3; library `opencilk-pedigrees`, `CMakeLists.txt` line 104).
  - Derived property: for a coefficient vector drawn uniformly at random, two distinct pedigrees of length ≤ 4095 with rank differences below the modulus collide in the dot product with probability `1/p` (a nonzero linear form over `Z_p` vanishes on a `1/p` fraction of vectors). With the fixed default seed the vector is a constant, so the guarantee is over the seed choice, not over program behaviour.
- **MPL fork-path ids** (`decheck.c`): `path` is a bit string with a sentinel bit; fork at tree depth `h` gives children `(path & ~(1<<h)) | (1<<(h+1))` and `(path | (1<<h)) | (1<<(h+1))` (lines 106–112); join restores the parent's normalized path (`path | (1<<td)`, line 198); ordering checks compute the LCA from the lowest differing bit (lines 273–318). Capacity: `MAX_FORK_DEPTH 31`; with entanglement detection compiled in, the scheduler declines to spawn at depth ≥ 31 (`Scheduler.sml` `depthOkayForDECheck`). Port execution (below): over random fork-join trees, children's normalized paths are always distinct, are descendants of the parent and not of each other, and join restores the parent's name — 0 violations in 4,269 strands across 5 seeds; a fork at tree depth 31 trips the `h < MAX_FORK_DEPTH` assertion.
- **Name supplies** (Augustsson, Rittri & Synek, JFP 4(1) 1994, `10.1017/S0956796800000988`): a supply can be split into two and queried for a name; names drawn from different nodes of the split tree differ, while querying the same supply twice yields the same name. Freshness is thus a linearity obligation on supplies.

### 5. Splittable and counter-based generator keys

Basis: source + documentation + execution (SplitMix port).

- **SplitMix (Steele, Lea & Flood, OOPSLA 2014, `10.1145/2660193.2660195`) as implemented in `haskellari/splitmix`** (`SplitMix.hs`):

  ```haskell
  -- | Split a generator into a two uncorrelated generators.
  splitSMGen :: SMGen -> (SMGen, SMGen)
  splitSMGen (SMGen seed gamma) =
      (SMGen seed'' gamma, SMGen (mix64 seed') (mixGamma seed''))
    where
      seed'  = seed `plus` gamma
      seed'' = seed' `plus` gamma
  ```

  (lines 217–223); `nextWord64 (SMGen seed gamma) = (mix64 seed', SMGen seed' gamma)` (lines 114–117). The module header warns it "should not be used for cryptographic or security applications ... two successive outputs suffice to reconstruct the internal state" (lines 20–23).
- **Port results** (`splitmix_port.py`, validated first against the doctests `mkSMGen 42 == SMGen 9297814886316923340 13679457532755275413` and the first three `nextWord64` outputs of `mkSMGen 1337`):
  - (A) reusing the parent after a split: the parent's outputs 3–12 equal the left child's outputs 1–10 (`True`) — the left child is the parent advanced by two steps with the same gamma;
  - (B) the right child's seed equals the parent's first output (`True`);
  - (C) skipping a split (giving the same generator to two branches) duplicates the stream exactly (`True`);
  - (D) used linearly, left and right children shared no 64-bit outputs in 10^5 draws each (0 common values; this is a weak sanity check, not a statistical test).
- **Gamma selection.** `mixGamma` (lines 260–268) forces `z1` odd and keeps it if it has ≥ 24 bit transitions, else XORs `0xaaaaaaaaaaaaaaaa`; the comment cites the O'Neill blog post and says "let's trust the text of the paper, not the code". O'Neill ("Bugs in SplitMix(es)", 2017-08-10) reports that the code listing in the paper inverted this test, giving gammas `1, 7, 15, 31` for 16 listed seeds, and that the repaired value `0xaaaaaaaaaaaaaaab` still fails PractRand (BRank at 256 MB in that post's C implementation). Port (E): with the paper-listing logic the 16 seeds give exactly `[1,1,1,1,7,7,7,7,15,15,15,15,31,31,31,31]`; with the pinned-revision logic they give `0xaaaaaaaaaaaaaaab` (×4), `…aaad` (×4), `…aaa5` (×4), `…aab5` (×4) — all 63 transitions, so they pass the transition test, and the first is the constant the post reports failing. Whether streams of this Haskell package with these gammas fail statistical tests was not executed here.
- **Claessen & Pałka** (Haskell Symposium 2013, `10.1145/2503778.2503784`) build splitting on a cryptographic hash; **Salmon et al.** (SC 2011, `10.1145/2063384.2063405`) define counter-based generators (Philox, Threefry), where a key and a counter determine each output and no state is carried.
- **JAX (`jax-ml/jax` @ `715e767052bc29ff65400e576b58dc37d1ad179f`).** `docs/jep/263-prng.md`: "JAX PRNG = Threefry counter PRNG + a functional array-oriented splitting model" (line 15); `type Key = Sample -- important identification for splitting` (line 112); `split key = (hash key 0, hash key 1)` (line 118); "Surprisingly, drawing a sample is very similar to splitting!" (line 124). In code, with the default `jax_threefry_partitionable=True`, `_threefry_split_foldlike` computes `threefry2x32_p.bind(k1, k2, counts1, counts2)` over `iota_2x32_shape(shape)` and stacks the two words (`threefry2x32.py` lines 325–329); `_threefry_raw_bits_partitionable` returns the same `threefry2x32_p.bind(k1, k2, counts1, counts2)` (lines 360–367); 32-bit `random_bits` reduces the two raw streams with XOR (`prng.py` lines 845–853, `num_streams=2`). Derived (not executed): for the same key and shape, `random_bits(key, 32, shape) == w0 ^ w1` where `(w0, w1)` are the words of `split(key, shape)`. Using one key both to sample and to split therefore makes the samples a deterministic function of the child keys — the documented "Key = Sample" identification turned into a concrete failure mode.
- **JAX key-reuse checker.** `jax/experimental/key_reuse/__init__.py`: experimental; enabled by `jax_debug_key_reuse` (default `False`, `jax/_src/config.py` lines 1245–1254); "Only typed PRNG keys created with `jax.random.key` are checked; legacy raw `uint32` keys created with `jax.random.PRNGKey` are not tracked, and reusing them will not raise an error" (lines 40–42). Mechanism: per-primitive signatures (`_core.py` lines 288–318) — `random_bits`: `Sink(0)`; `random_split`: `Sink(0), Source(0)`; `random_fold_in`: `Source(0)` only (the input key is **not** consumed); `random_wrap`: `Source(0)` (wrapping raw data yields an unconsumed key); `random_unwrap`: no effect. A static pass over jaxprs propagates consumption (`jaxpr_type_signature`), `cond` ORs branch sinks and ANDs sources (lines 480–496), `scan`/`while_loop` reject bodies that consume loop-invariant keys (lines 499–560), and a dynamic `_consumed` mask on key arrays raises "Previously-consumed key passed to … at index …" at jit boundaries (lines 177–181). Tests pin the design: `test_fold_in` asserts the key stays unconsumed after `fold_in` (`tests/key_reuse_test.py` lines 120–126); `test_wrap` asserts a wrapped key is unconsumed (lines 136–140); `test_unwrap` asserts `key_data` does not consume (lines 142–146). Derived: `wrap_key_data(key_data(k))` after consuming `k` yields an unconsumed key with identical bits, and two `fold_in(k, 7)` calls yield equal unconsumed keys; the checker enforces "no primitive consumes the same traced key value twice", not "no two keys in use are equal".

### 6. Rayon: recursive division of exclusive slices (`rayon-rs/rayon` @ `599425d4a4c64714632817f48496dbc53f656a90`)

Basis: source + execution.

- `join<A, B, RA, RB>(oper_a: A, oper_b: B)` requires `A: FnOnce() -> RA + Send`, `B: FnOnce() -> RB + Send` (`rayon-core/src/join/mod.rs` lines 93–99); its documentation states that if closure B "has been stolen, then it will look for other work while waiting for the thief to fully execute closure B" (lines 30–31) — the same help-while-waiting strategy whose stack and space effects are a scheduling concern, separate from disjointness.
- Slice producers divide with safe `split_at_mut` (e.g., `ChunksMutProducer::split_at`, `src/slice/chunks.rs` lines 255–257); `src/slice/mod.rs` and `src/slice/chunks.rs` contain no `unsafe` tokens (count 0 each). Disjointness of the halves is therefore a property of the standard library's `split_at_mut` signature, checked by the borrow checker at every use.
- Execution (four crates against the pinned rayon, offline):

  | Crate | Pattern | Result |
  | --- | --- | --- |
  | `probe_ok` | recursive `split_at_mut` + `join`; then `par_chunks_mut` | compiles; test passes (2^20 elements each incremented once) |
  | `bad_same_slice` | both closures capture the same `&mut [u64]` | `error[E0524]: two closures require unique access to *v at the same time` |
  | `bad_parent_after_split` | parent slice used in one branch while a half is live in the other | `error[E0500]: closure requires unique access to *v but it is already borrowed` |
  | `bad_not_send` | `Rc<u64>` captured by a `join` closure | ``error[E0277]: `Rc<u64>` cannot be sent between threads safely`` |
  | `ok_overlap_via_mutex` | overlapping access through `Mutex<Vec<u64>>` | compiles (overlap moved to run-time locking) |

- Reassembly is implicit: the halves borrow from the parent for a lifetime that ends before the parent is usable again — the same "children are not disjoint from the parent" rule as DPJ's trailing `*`.

### 7. Enforcement matrix

| Obligation | DPJ | Regent / Legion | Rayon / Rust | Cheetah pedigrees | MPL fork ids | splitmix | JAX keys |
| --- | --- | --- | --- | --- | --- | --- | --- |
| pieces of one division are disjoint | static (names); library cast trusted | static by construction or annotation; dynamic with `-lg:partcheck`; geometric runtime test otherwise | static (`split_at_mut` + borrowck) | n/a | n/a | n/a | n/a |
| parent not used concurrently with children | static for parameter-typed roots (`R` vs `P:[i]:*` not disjoint); unknown for `Root`-prefixed roots | dynamic dependence analysis | static (lifetimes) | n/a | n/a | n/a | n/a |
| identity/key used once | n/a | n/a | n/a | runtime advances ranks automatically | runtime | convention | convention; optional checker (typed keys only; `fold_in`/`wrap` exempt) |
| split not skipped | n/a | n/a | n/a | runtime (spawn/sync hooks) | runtime | convention | convention |
| depth/capacity respected | n/a | n/a | n/a | none observed (4096-entry table) | spawn declines at 31 (detection builds) | n/a | n/a |

### 8. Performance and resource footprint (L1–L6)

| Level | Evidence | Status |
| --- | --- | --- |
| L1 authoring | DPJ requires region/effect annotations on classes and methods (e.g., `Partition` constructors carry `writes this:[?]`); Regent requires partition and privilege declarations; Rust needs none beyond `split_at_mut`; JAX requires explicit `split` threading | qualitative; effort not measured |
| L2 build | rayon probe crate (debug, clean, offline): 3.12 s wall, 325 MB max RSS; incremental rebuild 0.11 s | execution (this host) |
| L3 checking latency | DPJ `areDisjoint`: linear in RPL length per pair plus a scan over declared constraints; Legion: O(depth) tree walk, else a set intersection, memoized per pair | source |
| L4 runtime | splitmix README: "list 64/splitmix" 17.86 µs vs tf-random 141.1 µs vs random 1.317 ms (upstream-reported benchmark); Cheetah pedigree cost: one modular add per spawn/sync plus a frame on the extension stack; JAX checker: "a small Python overhead on every call to a JIT-compiled function with keys as inputs or outputs" (config help text); Legion `-lg:partcheck`: "significant slow-down" | documentation + source |
| L5 verification | `-lg:partcheck` cost not measured; JAX static pass cost not measured | not examined |
| L6 memory | Cheetah DPRNG table 4096 × 8 B = 32 KiB plus a 4-word pedigree frame per spawned frame; MPL tid 8 B per task; SplitMix state 16 B; JAX Threefry key 2 × 32 bits | source |

### 9. Comprehensibility and conceptual simplicity (C1–C2)

Basis: derived.

- **C1.** All seven mechanisms reduce to "compare two paths from a root". The concepts a reader must hold are the root, the path syntax, which path elements can *prove* separation (DPJ: names and provably distinct indices; Legion: children of a disjoint partition; pedigrees: ranks) and which only *preserve* possible overlap (`*`, parameters, aliased partitions, z regions). Diagnostics differ sharply: Rust names the conflicting borrow and closure; DPJ reports interfering effects; Legion's runtime silently serializes aliased accesses (correct but invisible), and a wrong `disjoint` annotation is silent without `-lg:partcheck`; key reuse in JAX is silent unless the experimental flag is set.
- **C2.** A single abstraction covers storage pieces, task identities and random streams: a *path-indexed name* with a decision procedure "diverged at a separating element" and a linear-use rule for the generator of fresh paths. The systems realize the separating elements differently (index arithmetic, partition kinds, ranks, hash inputs), but the hidden special case is the same everywhere — a child name must never be provably disjoint from its parent's name (DPJ's trailing `*`, Rust lifetimes, Legion's tree ancestry), otherwise reassembly is unsound. Counter-based keys (Threefry over `(key, counter)`) make the path explicit data; SplitMix's split instead derives the left child by advancing the parent, which is why parent reuse aliases the left child.

### 10. Validation (V1–V4)

| Level | What exists | Gap |
| --- | --- | --- |
| V1 spec adequacy | JAX tests assert the intended consumption semantics of each primitive (examples quoted in §5); Legion `-lg:partcheck` validates user annotations against geometry; SplitMix port validated against upstream doctests | no evidence of mutation testing of DPJ's disjointness rules; DotMix collision analysis is a paper argument |
| V2 differential/fuzzing | splitmix README reports Dieharder runs ("2.49% were weak (3247 passed, 83 weak, 0 failed)" over 30 runs); a TestU01 suite was added (Changelog 0.1.0.4) | no split-pattern-specific statistical runs examined |
| V3 concurrency | Rust compile-time rejection is exhaustive for safe code; MPL decheck is a runtime monitor | Cheetah depth bound unvalidated; no model checking of the examined runtimes |
| V4 human mental model | DPJ tutorial program `DisjointArrayUpdate.java` illustrates `Data<[i]>` per-index regions | no empirical study of programmers' understanding examined |

## Boundaries

- **Not examined:** DPJ effect inference and method-effect summaries beyond the quoted rules; Legion control replication and the equivalence-set analysis; Regent index-launch optimization beyond the quoted constraint generation; OpenCilk compiler-side pedigree support; JAX `rbg`/`unsafe_rbg` implementations and Philox variants; the statistical evaluation of splittable generators by Schaathun (JFP 25, e6, 2015, `10.1017/S095679681500012X`), whose findings were not reviewed.
- **Unknown:** whether a Cheetah program with spawn depth ≥ 4096 actually misbehaves (the out-of-bounds index is source-derived; heap layout determines the effect); whether checks outside `runtime/` (for example in the OpenCilk compiler) bound spawn depth; whether the DPJ compiler at the pinned revision accepts or rejects the hand-derived examples in §2 exactly as predicted (not compiled) — in particular whether a `cobegin` that writes a root slice typed in a concrete region `Root:A` while writing a segment `P.get(0)` of a partition of that slice is accepted (which the literal head rule suggests and which would be a race) or rejected because z-region heads are rewritten before the disjointness test.
- **Known not to apply:** the DotMix `1/p` argument to a fixed default seed against structured inputs; JAX's checker to legacy `PRNGKey` arrays (documented); the SplitMix independence intuition to a parent used after `splitSMGen` (port result A).
- **Unsupported (by the subject):** spawning beyond tree depth 31 in MPL entanglement-detecting builds (declined); disjoint casts between partition kinds in Regent (type error); cryptographic use of splitmix (documented).
- **Stronger conclusions not established:** that Legion's runtime is unsound with wrong annotations in every case (only that it trusts them without `-lg:partcheck`); that JAX programs in the wild sample and split the same key (only that doing so yields an exact algebraic relation); that splitmix's current gammas for the 16 listed seeds fail statistical tests in this package (the failure report concerns a C implementation with the same gamma).

## Evidence

All evidence acquired 2026-11-20 (UTC).

**Repositories (pinned):**

- `dpj/DPJ` `bffe77a8e83ddb82a59d50f24435081b7c762f40`: `Implementation/Compiler/src/share/classes/com/sun/tools/javac/code/RPLs.java` 57–134; `.../code/RPLElement.java` 56, 112–121, 151–156, 201–204, 223–253, 302–342; `Implementation/Runtime/dpj/Partition.java` 58–101, 154–199; `Implementation/Runtime/dpj/ArraySlice.java` 92, 110, 133; `Documentation/v1.1/Source/Tutorial/Programs/dpj/DisjointArrayUpdate.java`.
- `StanfordLegion/legion` `aea587e157abff12f7d089c81f29cd3a8b993a2b`: `language/src/regent/std.t` 254–300, 454–520, 2727–2785; `language/src/regent/type_check.t` 642–720, 1484–1486, 1625–1634, 1748–1780, 1798–1840, 1866–1867, 1960–1961, 2162–2244; `language/src/regent/check_parallelizable.t` 14–50; `runtime/legion/nodes/index.cc` 764, 1629–1667, 2817–2870; `runtime/legion/api/runtime.h` 4532–4540; `runtime/legion/kernel/runtime.cc` 11157–11158.
- `rayon-rs/rayon` `599425d4a4c64714632817f48496dbc53f656a90` (tarball sha256 `d05cb32d934be1e9bb25286f2d4f661554bbcb5eae75dd0ac8b127ff0cea93bb`): `rayon-core/src/join/mod.rs` 12–160; `src/slice/chunks.rs` 242–283; `src/iter/plumbing/mod.rs` 95–137.
- `OpenCilk/cheetah` `33ac0d586cdbafe4e400f3741c4ce4ff07e61c26`: `runtime/pedigree-internal.h` 8–75; `runtime/pedigree_ext.cpp` 5–51; `runtime/pedigree_lib.cpp` 3–90; `runtime/pedigree_globals.cpp` 5; `include/cilk/cilk_api.h` 21–29; `runtime/CMakeLists.txt` 18, 29–30, 104.
- `haskellari/splitmix` `66ca2edbe935582cb66fd1fd36d1cd06366d9779`: `src/System/Random/SplitMix.hs` 1–23, 76–117, 214–268, 330–390; `README.md`; `Changelog.md`.
- `jax-ml/jax` `715e767052bc29ff65400e576b58dc37d1ad179f`: `docs/jep/263-prng.md` 15, 82, 104–124; `jax/experimental/key_reuse/__init__.py` 15–46; `jax/experimental/key_reuse/_core.py` 145–201, 288–330, 470–560; `tests/key_reuse_test.py` 120–146; `jax/_src/random/threefry2x32.py` 302–367, 432–444; `jax/_src/random/prng.py` 763–853, 1068–1131; `jax/_src/config.py` 1245–1254, 1467–1476.
- `MPLLang/mpl` `254325b5946f609f76458f0d9509a3206e0521cd`: `runtime/gc/decheck.c` 9–11, 64–75, 98–124, 181–208, 273–318; `basis-library/schedulers/spork/Scheduler.sml` 138–150.

**Literature (DOIs resolved through Crossref on 2026-11-20):** Augustsson, Rittri & Synek, JFP 4(1):117–123, 1994, `10.1017/S0956796800000988`; Bocchino et al., OOPSLA 2009 pp. 97–116, `10.1145/1640089.1640097`; Salmon, Moraes, Dror & Shaw, SC 2011 pp. 1–12, `10.1145/2063384.2063405`; Leiserson, Schardl & Sukha, PPoPP 2012 pp. 193–204, `10.1145/2145816.2145841`; Bauer, Treichler, Slaughter & Aiken, SC 2012 pp. 1–11, `10.1109/SC.2012.71`; Treichler, Bauer & Aiken, OOPSLA 2013 pp. 495–514, `10.1145/2509136.2509545`; Claessen & Pałka, Haskell 2013 pp. 47–58, `10.1145/2503778.2503784`; Steele, Lea & Flood, OOPSLA 2014 pp. 453–472, `10.1145/2660193.2660195`; Treichler, Bauer, Sharma, Slaughter & Aiken, OOPSLA 2016 pp. 344–358, `10.1145/2983990.2984016`. Blog: M. E. O'Neill, "Bugs in SplitMix(es)", 2017-08-10, https://www.pcg-random.org/posts/bugs-in-splitmix.html (read 2026-11-20).

**Rayon probe** (each crate's `Cargo.toml` declares `rayon = { path = "<pinned tarball>/rayon-599425d4a4c64714632817f48496dbc53f656a90" }`, edition 2021; commands `cargo test --offline -q` for `probe_ok`, `cargo build --offline -q` for the others):

```rust
// probe_ok/src/lib.rs
pub fn bump(v: &mut [u64]) {
    if v.len() <= 1024 {
        for x in v.iter_mut() { *x += 1; }
        return;
    }
    let mid = v.len() / 2;
    let (lo, hi) = v.split_at_mut(mid);
    rayon::join(|| bump(lo), || bump(hi));
}
#[cfg(test)]
mod tests {
    #[test]
    fn all_bumped_once() {
        let mut v = vec![0u64; 1 << 20];
        super::bump(&mut v);
        assert!(v.iter().all(|&x| x == 1));
        use rayon::prelude::*;
        v.par_chunks_mut(4096).enumerate().for_each(|(i, c)| for x in c { *x += i as u64; });
        assert_eq!(v[4096 * 3 + 7], 1 + 3);
    }
}
// bad_same_slice/src/lib.rs
pub fn f(v: &mut [u64]) { rayon::join(|| v[0] += 1, || v[1] += 1); }
// bad_parent_after_split/src/lib.rs
pub fn f(v: &mut [u64]) {
    let (lo, _hi) = v.split_at_mut(4);
    rayon::join(|| lo[0] += 1, || v[5] += 1);
}
// bad_not_send/src/lib.rs
use std::rc::Rc;
pub fn f() {
    let r = Rc::new(5u64);
    let r2 = r.clone();
    rayon::join(move || *r + 1, || 0u64);
    drop(r2);
}
// ok_overlap_via_mutex/src/lib.rs
use std::sync::Mutex;
pub fn f(v: &Mutex<Vec<u64>>) {
    rayon::join(|| v.lock().unwrap()[0] += 1, || v.lock().unwrap()[0] += 1);
}
```

Observed: `probe_ok` "test result: ok. 1 passed"; the three `bad_*` crates exit 101 with exactly one error each (`E0524`, `E0500`, `E0277` as tabulated); `ok_overlap_via_mutex` exits 0.

**SplitMix port** (`python3 splitmix_port.py`; port, not the Haskell package; verbatim):

```python
#!/usr/bin/env python3
"""Line-by-line Python port of System.Random.SplitMix (haskellari/splitmix @ 66ca2edb...),
used to exercise split/reuse behaviour. This is a PORT, not the Haskell package itself; it is
validated against the doctest vectors embedded in the upstream source before anything else runs.
"""
M = (1 << 64) - 1
GOLDEN_GAMMA = 0x9e3779b97f4a7c15

def shift_xor(n, w): return w ^ (w >> n)
def shift_xor_mul(n, k, w): return (shift_xor(n, w) * k) & M

def mix64(z):            # MurmurHash3 finalizer (upstream `mix64`)
    z = shift_xor_mul(33, 0xff51afd7ed558ccd, z)
    z = shift_xor_mul(33, 0xc4ceb9fe1a85ec53, z)
    return shift_xor(33, z)

def mix64variant13(z):   # Stafford Mix13 (upstream `mix64variant13`)
    z = shift_xor_mul(30, 0xbf58476d1ce4e5b9, z)
    z = shift_xor_mul(27, 0x94d049bb133111eb, z)
    return shift_xor(31, z)

def popcount(x): return bin(x).count('1')

def mix_gamma(z):        # upstream logic at the pinned revision: keep z1 if >= 24 transitions
    z1 = mix64variant13(z) | 1
    n = popcount(z1 ^ (z1 >> 1))
    return z1 if n >= 24 else z1 ^ 0xaaaaaaaaaaaaaaaa

def mix_gamma_paper_listing(z):  # inverted test, as reported for the code listing in the 2014 paper
    z1 = mix64variant13(z) | 1
    n = popcount(z1 ^ (z1 >> 1))
    return z1 ^ 0xaaaaaaaaaaaaaaaa if n >= 24 else z1

def mk(seed, mg=mix_gamma): return (mix64(seed), mg((seed + GOLDEN_GAMMA) & M))

def next_word64(g):
    seed, gamma = g
    s1 = (seed + gamma) & M
    return mix64(s1), (s1, gamma)

def split(g, mg=mix_gamma):
    seed, gamma = g
    s1 = (seed + gamma) & M
    s2 = (s1 + gamma) & M
    return (s2, gamma), (mix64(s1), mg(s2))

def stream(g, n):
    out = []
    for _ in range(n):
        w, g = next_word64(g); out.append(w)
    return out

def main():
    # --- validation against upstream doctests ---
    assert mk(42) == (9297814886316923340, 13679457532755275413), mk(42)
    assert ['%x' % w for w in stream(mk(1337), 3)] == ['b5c19e300e8b07b3', 'd600e0e216c0ac76', 'c54efc3b3cc5af29']
    print('doctest vectors: OK (mkSMGen 42 state; first 3 nextWord64 of mkSMGen 1337)')

    g = mk(2024)
    left, right = split(g)
    # (A) reusing the parent after a split: parent stream shifted by 2 == left child's stream
    ps, ls = stream(g, 12), stream(left, 10)
    print('A parent-reuse overlap: parent[2:12] == left[0:10] ->', ps[2:12] == ls)
    # (B) right child's seed equals the parent's first output
    print('B right.seed == first nextWord64(parent) ->', right[0] == ps[0])
    # (C) skipped split: passing the same generator to two branches yields identical streams
    print('C no-split duplication: stream(g) == stream(g) ->', stream(g, 8) == stream(g, 8))
    # (D) proper use: left/right/parent-after-left-consumption share no outputs in 10^5 draws each
    a, b = stream(left, 100000), stream(right, 100000)
    print('D left vs right common outputs in 1e5 draws each ->', len(set(a) & set(b)))

    # (E) weak-gamma seeds reported for implementations copying the paper's listing
    seeds = [0x61c8864680b583eb, 0xf8364607e9c949bd, 0x88e48f4fcc823718, 0x7f83ab8da2e71dd1,
             0x7957d809e827ff4c, 0xf8d059aee4c53639, 0x9cd9f015db4e58b7, 0xf4077b0dbebc73c0,
             0x305cb877109d0686, 0x359e58eeafebd527, 0xbeb721c511b0da6d, 0x86466fd0fcc363a6,
             0xefee3e7b93db3075, 0x79629ee76aa83059, 0x05d507d05e785673, 0x76442b62dddf926c]
    pinned = [mk(s)[1] for s in seeds]
    paper = [mk(s, mix_gamma_paper_listing)[1] for s in seeds]
    print('E gammas with paper-listing logic :', paper)
    print('E gammas with pinned-revision logic: min transitions =',
          min(popcount(x ^ (x >> 1)) for x in pinned), '; any gamma < 2^32 ->', any(x < (1 << 32) for x in pinned))

if __name__ == '__main__':
    main()
```

Output:

```text
doctest vectors: OK (mkSMGen 42 state; first 3 nextWord64 of mkSMGen 1337)
A parent-reuse overlap: parent[2:12] == left[0:10] -> True
B right.seed == first nextWord64(parent) -> True
C no-split duplication: stream(g) == stream(g) -> True
D left vs right common outputs in 1e5 draws each -> 0
E gammas with paper-listing logic : [1, 1, 1, 1, 7, 7, 7, 7, 15, 15, 15, 15, 31, 31, 31, 31]
E gammas with pinned-revision logic: min transitions = 63 ; any gamma < 2^32 -> False
```

The pinned-revision gammas are `0xaaaaaaaaaaaaaaab` (seeds 1–4), `0xaaaaaaaaaaaaaaad` (5–8), `0xaaaaaaaaaaaaaaa5` (9–12) and `0xaaaaaaaaaaaaaab5` (13–16), printed by `[hex(mk(s)[1]) for s in seeds]` with the functions above.

**MPL fork-path port** (`python3 mpl_tid_port.py`; port of the bit formulas only; verbatim):

```python
#!/usr/bin/env python3
"""Port of the fork-path task identifiers in MPL's runtime/gc/decheck.c (MPLLang/mpl @ 254325b5...),
exercised on random fork-join trees. PORT of the bit formulas only; not MPL itself.

tid = (path:uint32, depth:uint32) with depth = (dag_depth << 5) | tree_depth.
fork  (decheck.c GC_HH_decheckFork): left.path  = (path & ~(1<<h)) | (1<<(h+1));
                                      right.path = (path |  (1<<h)) | (1<<(h+1)); h = tree_depth
join  (decheck.c GC_HH_decheckJoin): path = left.path | (1<<td), td = tree_depth(left) - 1
norm_path(t) = path & ((1 << (tree_depth+1)) - 1)
"""
import random

MAXD = 31
U32 = (1 << 32) - 1

def td(t): return t[1] & 0x1f
def dd(t): return t[1] >> 5
def norm(t): return t[0] & ((1 << (td(t) + 1)) - 1)

def fork(t):
    h = td(t)
    assert h < MAXD, 'decheck.c asserts h < MAX_FORK_DEPTH'
    d = t[1] + (1 << 5) + 1
    return (((t[0] & ~(1 << h)) | (1 << (h + 1))) & U32, d), (((t[0] | (1 << h)) | (1 << (h + 1))) & U32, d)

def join(l, r):
    t = td(l) - 1
    ddn = max(dd(l), dd(r)) + 1
    return ((l[0] | (1 << t)) & U32, (ddn << 5) + t)

def is_ancestor_path(a, b):
    """a is an ancestor-or-self of b in the fork tree (by normalized paths)."""
    la, lb = td(a), td(b)
    if la > lb: return False
    mask = (1 << la) - 1
    return (norm(a) & mask) == (norm(b) & mask)

def run(seed, max_depth):
    rng = random.Random(seed)
    live = []           # tids of strands that exist concurrently at some point
    problems = 0
    def go(t, depth):
        nonlocal problems
        live.append(norm(t) | (td(t) << 32))
        if depth < max_depth and (depth == 0 or rng.random() < 0.8):
            l, r = fork(t)
            if norm(l) == norm(r): problems += 1
            if not (is_ancestor_path(t, l) and is_ancestor_path(t, r)): problems += 1
            if is_ancestor_path(l, r) or is_ancestor_path(r, l): problems += 1
            lj = go(l, depth + 1); rj = go(r, depth + 1)
            j = join(lj, rj)
            if norm(j) != norm(t) or td(j) != td(t): problems += 1   # join restores the parent's name
            return j
        return t
    root = (1, 0)
    go(root, 0)
    return problems, len(live)

if __name__ == '__main__':
    for s in range(5):
        p, n = run(s, 12)
        print(f'seed={s} strands={n} problems={p}')
    # capacity: forking at tree depth 31 trips the assertion
    t = (1, 0)
    try:
        for i in range(40):
            t, _ = fork(t)
    except AssertionError as e:
        print(f'fork refused at tree depth {td(t)}: {e}')
```

Output:

```text
seed=0 strands=829 problems=0
seed=1 strands=759 problems=0
seed=2 strands=3 problems=0
seed=3 strands=1303 problems=0
seed=4 strands=1375 problems=0
fork refused at tree depth 31: decheck.c asserts h < MAX_FORK_DEPTH
```

## Revalidation

- **DPJ:** re-read `RPLs.areDisjoint` and the `isDisjointFrom` overrides for `ROOT_ELEMENT`, `STAR`, `RPLParameterElement`, `ArrayIndexRPLElement`, `VarRPLElement`; check that `Partition.get` still returns `ArraySlice<T,this:[idx]:*>`. If the trailing `*` were removed, re-derive the cross-partition case of §2. The open root-versus-segment question is settled by compiling one class with the DPJ compiler: a `cobegin` whose first statement writes `a.put(0, x)` on an `ArraySlice<Integer,Root:A> a` and whose second writes `P.get(0).put(0, y)` for `final Partition<Integer,Root:A> P = new Partition<Integer,Root:A>(a, 4)`; acceptance means the head rule applies literally.
- **Legion/Regent:** `grep -n 'is_disjoint())' runtime/legion/nodes/index.cc` for the LCA short-circuit; `grep -n 'partcheck' runtime/legion/api/runtime.h runtime/legion/kernel/runtime.cc`; `grep -n 'std.partition(std.disjoint' language/src/regent/type_check.t` for by-construction disjoint operators.
- **Rayon:** rebuild the five probe crates against the new revision; the three `bad_*` crates must still fail with `E0524`, `E0500`, `E0277`; `grep -c unsafe src/slice/mod.rs src/slice/chunks.rs`.
- **Cheetah:** `grep -rn 'dprng_depth\|4096' runtime/` — the boundary is resolved if a comparison against the table size or a larger/dynamic table appears. A direct test needs an OpenCilk toolchain: spawn-recurse to depth 5000 with the pedigree library linked, under AddressSanitizer (`opencilk-pedigrees-asan`).
- **splitmix:** diff `splitSMGen` and `mixGamma`; rerun the port (it re-checks the doctest vectors first).
- **JAX:** check `_core.py` signatures for `random_fold_in_p`, `random_wrap_p`, `random_split_p`; check `jax_debug_key_reuse` default in `jax/_src/config.py`; compare `_threefry_split_foldlike` with `_threefry_raw_bits_partitionable`. With JAX installed, the relation of §5 is a one-line check: `jax.random.bits(k, (n,), 'uint32')` against `jax.random.key_data(jax.random.split(k, n))` XORed along the last axis (with `jax_threefry_partitionable=True`).
- **MPL:** check `MAX_FORK_DEPTH` and the fork/join formulas in `runtime/gc/decheck.c`; rerun the port.
