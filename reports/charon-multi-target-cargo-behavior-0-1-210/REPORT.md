# Charon multi-target and multi-primary Cargo behavior at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), two different multiplicities must be kept separate.

Charon's own `--targets=a,b,...` mode is an explicit **cross-target fan-out and merge**. The outer process starts one translation thread per requested target. Each target receives a unique temporary output file such as `target_0.llbc`, so those target translations do not compete for the user's final `--dest-file`. After all target translations succeed, Charon deserializes them, merges their semantic items, performs post-merge cleanup, and serializes one merged crate through the original invocation-wide output options.

A single `charon cargo` execution can independently contain **multiple target-side primary Cargo units**. Charon sets one `RUSTC_WRAPPER` and one serialized `CliOpts` value for the whole Cargo process. Its driver translates every wrapped invocation that is target-side and has `CARGO_PRIMARY_PACKAGE`; it does not assign a distinct Charon destination to each such compiler unit. Thus if one Cargo invocation produces more than one selected primary rustc process, those processes inherit the same Charon output policy. With an explicit `--dest-file` they necessarily name the same path. Without one, outputs are derived from each unit's rustc crate name, so distinct crate names separate files but identical crate names collide. The pinned source contains no lock, per-unit staging path, or aggregation step for this within-one-Cargo-invocation case. This establishes a write-collision/race possibility from the source; no fresh concurrent execution was performed to characterize the resulting winner or filesystem behavior.

The cross-target merger first makes every item target-qualified, then tries to remove unnecessary duplication. Items that compare equal after Charon's normalization are deduplicated. A function whose name, generics, and signature agree across target variants but whose body differs gets a synthetic `target_dispatch` façade and keeps target-specific implementations behind it. Items with incompatible semantic shapes are not merged and remain target-qualified. An item that exists on only one requested target is trivially deduplicated and loses the target suffix rather than being wrapped in a one-target dispatcher.

Type layouts receive special treatment: layout differences are ignored while deciding whether otherwise equal type declarations can deduplicate, and the surviving type accumulates the per-target layout records. Source spans/text and selected `rustc_*` attributes are also ignored for equality. These choices define what "same item across targets" means at this pin.

Checked-in multi-target outputs preserve these behaviors: equal functions appear once, target-varying function bodies produce target-specific implementations plus a dispatcher, target-only functions lose their suffix, and conditional layout differences can coexist under one deduplicated type declaration. These are upstream preserved execution artifacts, not fresh execution performed by this report.

## Applicability

This report applies to:

- repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- package version `0.1.210`;
- the outer `charon` multi-target orchestration and `charon_lib::export::multi_target` merge implementation at that revision.

The report distinguishes:

1. **Charon target fan-out** — one Charon invocation deliberately repeats translation for the explicit Charon `--targets` list and merges those results.
2. **Cargo primary-unit multiplicity** — one `cargo build` selected by `charon cargo` may invoke rustc more than once for target-side primary work.

The existing `cargo-unit-graphs-rustc-invocations-2026-05-31` corpus report establishes why a Cargo command can have several compilation roots and same-package target units. This report does not repeat Cargo's unit-graph derivation; it establishes what pinned Charon does when more than one driver invocation is selected.

"Race" below means that source-defined Charon writers can target the same filesystem path without Charon-level synchronization. No claim is made about which write wins, whether writes interleave at byte granularity on a particular filesystem, or the probability that a collision manifests.

## Findings

### Charon's `--targets` option means repeated compilation followed by semantic merge

`CliOpts.targets` is documented as a list of target architectures to translate. The outer command removes that list from the ordinary options and calls `translate_multi_target`.

For each requested target, the caller reuses the chosen translation mode:

- Cargo mode appends `--target <target>` to the forwarded Cargo build arguments.
- Direct-rustc mode appends `--target <target>` to the rustc arguments.

This is not one rustc process with several target triples. It is one translation per target, followed by a Charon-level merge.

Basis: pinned Charon **source**.

### Per-target translations run concurrently

`translate_multi_target` uses scoped threads and starts one thread for each target in the provided target list. It joins all threads and collects their `CrateData` values before merging.

The option is therefore a concurrency boundary as well as a semantic merge feature. The `CliOpts.targets` documentation calls the implementation initial and "extremely slow"; it does not promise a particular scheduling order.

Basis: pinned Charon **source**.

### Charon isolates its own cross-target intermediate files

Before starting each target translation, Charon creates one temporary directory for the overall multi-target operation. Target thread `i` writes to a distinct path:

```text
<temporary-directory>/target_<i>.<format-extension>
```

Per-target printing is suppressed, serialization is forced, and `dest_file` is replaced with that unique temporary path. After the child translation exits successfully, the thread deserializes its own file.

This prevents Charon's explicit `--targets` threads from racing on the user's requested final destination.

Basis: pinned Charon **source**.

### Per-target staging intentionally overrides several invocation options

Each target clone of `CliOpts` is changed before translation:

- `targets` is cleared to prevent recursive multi-target dispatch;
- `preset` is cleared because the outer multi-target path already applied it;
- `print_ullbc` and `print_llbc` are disabled for the child;
- `no_serialize` is forced false so the result can be reloaded;
- the temporary output format is forced to one concrete format;
- `unbind_item_vars` is forced false so IDs/variables remain manipulable during merge;
- `translate_all_methods` is forced true so all targets start with comparable trait method populations.

After merging, post-merge cleanup removes unneeded methods and applies unbinding if the original invocation requested it.

Thus child artifacts are merge intermediates, not individually faithful realizations of all user-facing output options.

Basis: pinned Charon **source**.

### `--format all` does not make each target emit two intermediate files

The per-target staging format chooses JSON when the outer format is absent, JSON, or `all`; it chooses Postcard only when the outer format is explicitly Postcard. Each target therefore emits one temporary representation.

Only after merge does Charon call the original output-target logic. An outer `--format all` can then emit both JSON and Postcard versions of the **merged** crate.

Basis: pinned Charon **source**.

### Any failed target prevents the merged result

After each per-target child exits, Charon checks its `ExitStatus`. A failing target is reported and passed through the same exit-status handler rather than being silently omitted. Deserialization failure for a target also fails collection.

The merge therefore requires a loadable result from every requested target. `CrateMerger` further expects each per-target `CrateData` to contain exactly one target-information key and unwraps that invariant.

This is fail-closed with respect to missing requested target artifacts at this orchestration layer. It does not prove that each successful per-target translation is semantically complete; `has_errors` is a separate condition.

Basis: pinned Charon **source**.

### Partial-output state is ORed across targets

When `CrateMerger` consumes each `CrateData`, it sets the merged `has_errors` to the logical OR of the per-target values.

A target that produced a serializable but partial result therefore taints the merged result as partial rather than disappearing from the aggregate status.

Basis: pinned Charon **source**.

### Every item is initially target-qualified before deduplication

Before appending one target's declarations to the merged crate, `CrateMerger` remaps declaration IDs and appends `PathElem::Target(target)` to every translated `Name`.

That target suffix makes otherwise same-named declarations distinct during the initial union. File IDs are separately remapped, and Charon deduplicates file records by `FileName`.

Later deduplication strips the target suffix only when Charon concludes a group can be represented by one cross-target item.

Basis: pinned Charon **source**.

### Cross-target groups are keyed by normalized item name and item kind

`ItemDeduplicator` removes the trailing target suffix to construct a base name and groups items by that name plus the item-ID kind. References to impls inside names are normalized through the candidate remap so groups can converge across mutually referring items.

If Charon encounters two items with the same normalized key **within one target**, it clears that group and excludes it from cross-target merging. This avoids treating an ambiguous same-target name collision as one cross-target identity.

The grouping/dedup process runs to a fixpoint because merging one referenced item can make additional names comparable.

Basis: pinned Charon **source**.

### Equal item variants are deduplicated

For a target group, Charon normalizes declaration IDs/references and compares owned item values.

Before equality comparison it deliberately ignores:

- target suffixes;
- source spans;
- `item_meta.source_text`;
- selected `rustc_*` attributes;
- type layout records.

If all normalized item values are equal, Charon chooses a deterministic canonical item, removes its target suffix, remaps references to it, and removes the other copies.

This defines a semantic equality policy narrower than byte-for-byte equality of per-target LLBC.

Basis: pinned Charon **source**.

### Target-only items normally become ordinary unsuffixed items

A group may contain an item from only one of the requested targets—for example a function behind `#[cfg(target_arch = "aarch64")]`.

A one-element group is equal to itself and therefore takes the ordinary dedup path. Charon removes the sole target suffix. It does not create a one-target dispatcher merely to record that the source item was absent on other requested targets.

The checked-in `issue-1157-single-target-suffix.out` preserves this behavior: target-exclusive `aarch64_only` and `x86_64_only` functions appear without target suffixes in the final merged output.

A consumer cannot infer "present on every requested target" merely from absence of a target suffix.

Basis: pinned Charon **source** + preserved upstream **execution** artifact.

### A function with a stable interface but target-varying body gets a façade

When normalized function items are not equal, Charon checks whether their item name, generic parameters, and function signature are still equal. If so, it creates a new synthetic `FunDecl` whose body is `TargetDispatch`.

The façade maps each represented target triple to that target's function declaration. Per-target implementations are marked `ItemSource::TargetDependent` and retain target-qualified names. References that previously selected a variant are remapped to the façade.

The preserved `multi-targets.out` and `issue-1158-partial-dedup.out` show this shape: per-target implementations coexist with an unsuffixed function containing a `target_dispatch` map.

Basis: pinned Charon **source** + preserved upstream **execution** artifacts.

### Incompatible variants remain target-qualified rather than being forced into one abstraction

If non-function items differ after normalization, or function name/generics/signature differ, `decide_merge` returns `Skip`. Such groups do not participate in ID remapping/deduplication.

Their target-qualified declarations remain in the merged crate. Charon does not synthesize a generic union type or overloaded façade to hide incompatible interfaces.

This is an important boundary for consumers: a source-level name can correspond to multiple target-qualified Charon items when the target changes semantic structure.

Basis: pinned Charon **source**.

### Type layout differences are retained separately from type-declaration equality

For comparing type declarations, `normalize_item` clears layout records. Two declarations can therefore deduplicate even when their target layouts differ.

When Charon deduplicates the type group, it collects the layouts from every per-target type declaration into the canonical type before removing the other copies.

The checked-in conditional-`repr` fixture demonstrates the intended case: a type whose alignment attribute changes under target cfg is still one logical type declaration after merge, while layout data can remain target-specific.

Basis: pinned Charon **source** + preserved upstream **execution** artifact.

### File identity is merged by Charon `FileName`, not target

`CrateMerger` maintains one `file_name_to_id` map. When a later target contains a file with a `FileName` already registered from an earlier target, Charon reuses the existing `FileId` instead of inserting another file record.

The merge path does not compare source contents or crate-name metadata before this reuse. In ordinary repeated compilation of one source tree this is a useful deduplication. It is nevertheless a source-defined assumption: the same Charon filename is treated as one merged file identity across targets.

Basis: pinned Charon **source**.

### Multi-target merge preserves the first crate name as the merged crate name

The merged crate starts with an empty crate name. The first per-target crate supplies it; later `crate_name` values are not compared before their declarations are appended.

Ordinary `--targets` use should compile the same selected crate name for each target. The implementation itself does not enforce that equality at the merge boundary. The final output path is derived from the resulting merged crate name unless the user supplied `--dest-file`.

Basis: pinned Charon **source**.

### Cargo primary-unit multiplicity is a separate output-collision boundary

Outside explicit Charon `--targets`, `charon cargo` runs one Cargo build with one `RUSTC_WRAPPER` and one serialized `CliOpts` value. The driver translates each wrapped rustc invocation that it classifies as a target-side primary package.

The outer Cargo path does not assign a new `dest_file` per selected primary rustc invocation. Every selected driver process sees the same invocation-wide Charon output options.

Therefore, **if** one Cargo invocation yields multiple selected target-side primary rustc processes:

- an explicit `--dest-file` points every such process at the same file;
- without `--dest-file`, each process derives its output from its rustc crate name;
- primary units with distinct crate names get distinct default output names;
- primary units with the same crate name derive the same default output name.

The pinned Charon output writer creates/truncates the chosen path directly. This path contains no Charon-level lock, primary-unit suffix, atomic cross-process merge, or per-unit temporary staging. Multiple selected primary units targeting the same filename therefore create a write-collision/race possibility.

The existing Cargo unit-graph report establishes that Cargo commands can construct several root/same-package compilation units. This report does not claim an observed corrupt file or a deterministic "last writer" outcome; no fresh concurrent filesystem experiment was performed.

Basis: pinned Charon **source** + existing corpus Cargo findings + **derived** collision argument.

### Cross-target temporary isolation does not fix a multi-primary collision inside one target child

When explicit `--targets` is used, each target thread assigns one unique temporary `dest_file` to its child invocation. In Cargo mode, however, that child still runs one Cargo build. If that Cargo build itself selects several target-side primary rustc processes, they all inherit the **same temporary file for that target thread**.

Thus target-thread isolation prevents target A from writing target B's temp file, but it does not create one file per Cargo primary unit within target A.

A multi-primary collision can therefore occur inside one target child before Charon reaches `multi_target::merge`.

Basis: pinned Charon **source** + **derived** composition.

### Options are invocation-wide unless Charon deliberately overrides them for merge staging

The outer Charon invocation creates one `CliOpts`. Explicit multi-target mode clones it for each target, making only the staging overrides listed above. Cargo mode serializes one clone into `CHARON_ARGS` for the whole Cargo child process.

Options such as inclusion/opacity roots, transformation presets, error policy, extra rustc flags, and output policy are therefore invocation-wide by default. Charon does not expose a per-Cargo-primary-unit option map at this revision.

Basis: pinned Charon **source**.

## Boundaries

- No fresh Cargo, rustc, Charon, multi-thread, filesystem-race, or cross-target execution was performed.
- The checked-in `.out` files are preserved upstream generated artifacts. They demonstrate shapes upstream had generated before the pinned commit; this report did not regenerate them.
- The report proves a same-output-path **possibility** for multiple selected primary driver processes from source composition. It does not establish byte-level interleaving, winner ordering, frequency, or behavior of a particular filesystem.
- It does not enumerate every Cargo command that produces multiple target-side primary rustc invocations. The separate Cargo unit-graph report covers build-unit construction.
- It does not claim ordinary `charon --targets` target threads race on their own Charon-assigned temporary files; the source gives each target index a separate file.
- It does not prove semantic correctness of `multi_target::merge`.
- It does not establish that ignoring spans/source text/selected attributes during dedup is sound for every downstream property; it records the pinned equality policy.
- It does not establish that same `FileName` always implies identical source contents across targets.
- It does not characterize target-specific native/linker behavior that never reaches Charon's translated crate.
- It does not choose how Anneal should model cross-target verification results.

## Evidence

Primary Charon subject:

```text
AeneasVerif/charon
a535e914f74db4fd9e6be7048f4233270d8945c0
version 0.1.210
```

**Source:**

- `charon/src/bin/charon/main.rs`, blob `b4460ce4cd3baa32308718e79b6e194860b042a6`: target-thread fan-out, temporary-file naming, child option overrides, target-specific Cargo/rustc invocation, load-all-before-merge, final serialization.
- `charon/src/export/multi_target.rs`, blob `a5e3516521e1c107db5800fd7e806b20c2c7e6df`: per-target union, target suffixes, file-ID reuse, fixpoint grouping, equality normalization, deduplication, function façades, layout merging, cleanup.
- `charon/src/bin/charon-driver/driver.rs`, blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`: selection of every target-side `CARGO_PRIMARY_PACKAGE` invocation and invocation-wide `CHARON_ARGS`.
- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: `--targets` and output policy.
- `charon/src/export.rs`, blob `d5428958eb870f9f8531a8d193385c6be782338a`: direct creation/truncation of selected output files and merged `has_errors`.

**Preserved execution artifacts** at the same Charon revision:

- `charon/tests/ui/multi-target/multi-targets.rs`, blob `742988f7a12636bcf6e6eabd511ee7fa5e2dc60b`, and `.out`, blob `8fb3fa5bbffa38e6b2a7831c0feaee9d72de6d58`: equal-item dedup and function target dispatcher.
- `charon/tests/ui/multi-target/issue-1157-single-target-suffix.rs`, blob `35d99861e9856a5a3732e14903cba9b301aa6140`, and `.out`, blob `33dcc8854100ca9d2b2b6026f730ac17c90fbcd3`: single-target item suffix removal.
- `charon/tests/ui/multi-target/issue-1158-partial-dedup.rs`, blob `3a0fdb6b60de08bd459bde6365da277c4a6ff123`, and `.out`, blob `423c51a2b61926f7961c2fb6284aa16968c837b9`: partial-target dedup and dispatcher.
- `charon/tests/ui/multi-target/issue-1186-conditional-repr.rs`, blob `2f9c733ae9e02634613f72c06e99f2eee17f9433`, and `.out`, blob `998307cbf9f049cbe545c67855037da3b69684bb`: conditional layout case.
- `charon/tests/cargo/multi-targets/src/lib.rs`, blob `f70ad5be41543da6343cb08756faadef1a43b0a5`, and `charon/tests/cargo/multi-targets.out`, blob `ef98e938d5d6614f3e4ce62dee5593b554d7473f`: target cfg selection through Cargo.

The execution artifacts pre-existed in the pinned repository. No fresh **execution** was performed by this report.

## Revalidation

For another Charon pin, diff `main.rs`, `export/multi_target.rs`, `driver.rs`, `options.rs`, and `export.rs`. Check whether:

1. one thread/process is still created per `--targets` member;
2. per-target destination files remain unique;
3. per-target options are still rewritten before extraction;
4. merge grouping and equality normalization changed;
5. function façades still require equal signatures;
6. target-only items still lose their suffix;
7. type layouts and source metadata still receive special equality treatment;
8. file identity is still keyed only by Charon `FileName`;
9. selected Cargo primary units still share invocation-wide output options.

On an execution-capable surface, use two independent probes.

**Cross-target merge probe:** compile one source file for at least three targets with:
- one item present everywhere and identical;
- one item present on one target only;
- one function with the same signature and different bodies;
- one function whose signature differs by target;
- one type with equal fields but target-specific layout;
- one type whose semantic fields differ by target.

Preserve every per-target LLBC and final merged LLBC, commands, target triples, hashes, and stderr.

**Multi-primary Cargo output probe:** create a package/workspace command that selects at least two target-side primary rustc units. Test both default output naming and one explicit `--dest-file`. Capture rustc-wrapper invocations, process IDs/timing, filesystem events if practical, and final output bytes.

The first probe revalidates merge semantics. The second determines the concrete manifestation of the source-defined output collision on that platform; it should not be replaced by an assumption that cross-target temporary files solve multi-primary output sharing.
