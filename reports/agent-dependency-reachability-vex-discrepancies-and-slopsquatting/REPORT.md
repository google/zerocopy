# Dependency Vulnerability Reachability, SBOM and VEX Discrepancies, and LLM Package Hallucination Defenses

## Summary

Autonomous coding, dependency-remediation, and security-triage agents rely on three software supply-chain primitives—**static and binary vulnerability reachability**, **SBOM + VEX vulnerability suppression**, and **LLM package recommendation and installation**—whose real implementations violate common soundness assumptions across normative specifications (`OSV Schema`, `OpenVEX v0.2.0`, `OASIS CSAF v2.0`), fourteen primary empirical and specification sources, ten pinned upstream repositories, and a deterministic five-suite verification probe (`scripts/verify_vuln_reachability_sbom_slopsquatting.py`):

1. **Two-Pass `CHA -> VTA -> VTA` Call-Graph Precision vs. Four Unsoundness and VEX Justification Failure Modes (`golang/vuln@ef4cb2f7`, `golang/tools@70e48cd7`, `google/osv-scanner@925d1b4c`):**
   - Ecosystem-scale call-graph analysis eliminates **>98.7%** of transitive Maven metadata alerts (`~1.1M` $D_p(\max)$ down to $10^{4.15} \approx 14,125$ $D_m(\max)$ across `3M` Maven package versions and `517` CVEs; `Mir et al., SANER '23`) and **`74.4%`** (`121 -> 31`) of Go SBOM alerts (`Zhou et al., CODASPY '26`, `§5.7 Table 8` & `Appendix A Table 9`), yet trades completeness for precision. In `govulncheck` (`internal/vulncheck/utils.go:63–89`, `slicing.go:14–46`) paired with `vta.CallGraph`'s per-parameter `typePropGraph` propagation (`go/callgraph/vta/vta.go:79–165`, `graph.go:312–352, 660–698`), Pass 1 prunes uninstantiated interface callees (`cha_flagged=['GO-TAR', 'GO-XML', 'GO-YAML'] -> vta_pass1_flagged=['GO-TAR', 'GO-YAML']`) while still propagating function arguments passed at static call sites inside dead interface methods (`DeadXML.Decode -> main.runHook(main.evilSink)`), and Pass 2 (`fslice_1`) evicts those dead methods to prune `GO-YAML` (`vta_pass2_flagged=['GO-TAR']`, while immediately pruning unpassed local closures in Pass 1: `vta_unpassed_closure_pruned_pass1=True`). However, `govulncheck` silently misses `reflect` invocations (`ground_truth_main=['GO-REFL', 'GO-TAR']`, `vta_missed_reflection=['GO-REFL']`, `vta.go:74–75`) and **100% of uninstantiated generic library entry points** (`generic_lib_entries_count=0`, `generic_lib_flagged=[]`, `entries.go:17–46`, `https://go.dev/issue/57221`).
   - Binary mode (`binary.go:46–48, 107–114`) constructs **zero call graphs**, flagging all symbols compiled into linked package symbol tables when unstripped (`binary_unstripped_flagged=['GO-REFL', 'GO-TAR', 'GO-XML', 'GO-YAML']`) and expanding to **`allKnownVulnerableSymbols(affVulns)`** on stripped `-ldflags="-s -w"` binaries (`binary_stripped_flagged=['GO-MODONLY', 'GO-REFL', 'GO-TAR', 'GO-TOML', 'GO-XML', 'GO-YAML']`, including unimported `go.mod`-only modules).
   - Two VEX justification defects corrupt downstream machine triage: `golang/vuln/internal/openvex/handler.go:102–107` returns `-1` on *both* `(fr1.Package != "" && fr2.Package == "")` and `(fr1.Package == "" && fr2.Package != "")`, violating comparator antisymmetry (`antisymmetry_violations=['(required,imported):-1_vs_-1', '(imported,required):-1_vs_-1']`) and overwriting `imported` with `required` on `[imported, required]` streams (`openvex_imp_then_req_buggy='vulnerable_code_not_present'` vs. `openvex_req_then_imp='vulnerable_code_not_in_execute_path'`); conversely, `google/osv-scanner`'s SCALIBR enricher (`govulncheck.go:125–138`) emits `'vulnerable_code_not_in_execute_path'` even for unimported `go.mod`-only dependencies (`scalibr_unimported_mod_signal='vulnerable_code_not_in_execute_path'`).

2. **`OSV-Scanner` Experimental Rust Build RCE, DWARF/Regex Recall Collapse, and OSV `GIT`/`SEMVER` Range Hazards (`google/osv-scanner@925d1b4c`, `rustsec/rustsec@9284e112`, `ossf/osv-schema@e34af15e`):**
   - `osv-scanner` experimental Rust reachability (`internal/sourceanalysis/rust.go:31, 234–248`) invokes `cargo build --workspace --all-targets --release` (`opt-level=3`, `lto`, `debuginfo=1`), executing arbitrary untrusted `build.rs` scripts and procedural macros on the scanning host.
   - Post-build, `cleanRustFunctionSymbols` (`rust.go:288–304`) strips generics via `<[\w,]+>`, achieving only **`2/6` recall** (`rust_regex_upstream_recall='2/6'`, `rust_regex_failed_count=4` vs. `rust_regex_balanced_recall='6/6'`) across const-generic arrays (`smallvec::SmallVec<[u8; 4]>::grow`), nested generics, lifetimes, and generic trait impls; `functionsFromDWARF` (`L154–174`) inspects only `DW_TAG_subprogram`, missing `opt-level=3 + lto` inlined vulnerable functions (`DW_TAG_inlined_subroutine`, `dwarf_inlined_detected=False`) while flagging dead `#[no_mangle]` exports (`dwarf_dead_export_flagged=True`); `L275–280` splits the entire `.d` depfile on `": "` and errors on multi-rule Cargo depfiles (`cargo_depfile_multi_rule_err=True`); and `go.go:104–126` (`L110` `TODO`) ignores version ranges in `vulnHasImportsField` (`go_v1_false_imports_inheritance=True`).
   - Under normative `OSV Schema` evaluation (`docs/schema.md:1144–1148, 1269–1398`), replacing `{"fixed": "Y"}` (`osv_git_fixed_affected=['X', 'A', 'B', 'C', 'D', 'E', 'F']`) with `{"limit": "Y"}` (`osv_git_limit_affected=['X', 'A', 'B', 'C']`) restricts ancestry to `X..Y` and causes **silent false negatives on unmerged sibling branches** (`osv_git_limit_false_negatives=['D', 'E', 'F']`), while under SemVer 2.0.0 (`1.0.2-rc.1 < 1.0.2`), `{"fixed": "1.0.2"}` catches `1.0.2-rc.1` (`osv_semver_prerelease_before_fix=True`) whereas `{"last_affected": "1.0.1"}` silently misses `1.0.2-rc.1` (`osv_semver_last_affected_ceiling_fn=True`).

3. **`Syft` vs. `Trivy` Python Manifest Erasure, Opposite Version Guessing, and CycloneDX Edge Loss (`anchore/syft@9ad9aa5e`, `aquasecurity/trivy@edf9f5c1`):**
   - Without a lockfile (`80.9%` Python lockfile-generation failure rate in `Zhou et al., CODASPY '26 Table 4`), both `Syft` (`GuessUnpinnedRequirements=false`) and `Trivy` (`useMinVersion=false`) retain only **`3/10`** declarations on a 10-entry `requirements.txt` (`syft_default_count=3`, `trivy_default_count=3`, `default_omitted_count=7`) on **disjoint subsets** (`Syft` parses `certifi===2024.2.2 -> '2024.2.2'` and drops `pyjwt==2.8.0,!=2.8.1`; `Trivy` parses `pyjwt -> '2.8.0'` and drops `certifi===2024.2.2 -> None`). Heuristic version guessing diverges in opposite directions (`werkzeug>=2.0.0,<=2.2.2` resolves to ceiling `'2.2.2'` in `Syft` vs. floor `'2.0.0'` in `Trivy`), and `Syft`'s `guessVersion` (`parse_requirements.go:224–239`) contains a `strings.SplitAfter(part, "=")` bug on `"==2.8.0,!=2.8.1"` that leaves line `237` unreachable dead code (`syft_guess_pyjwt_splitafter_bug=None`).
   - `Trivy` `pyproject.go:45–60` leaks all `[project.optional-dependencies]` extras into `MainDeps()` (`trivy_pep621_extras_leaked=['mypy', 'pytest', 'sphinx']`) while `p.Project.OptionalDependencies != nil` shadows the `else if p.Tool.Poetry.Dependencies.Set != nil` branch, **erasing 100% of Poetry main dependencies** (`trivy_poetry_deps_retained_when_optional_set=[]`). Meanwhile, `Syft` CycloneDX serialization (`cyclonedxhelpers/to_format_model.go:235–264`) retains only `1/4` relationship types (`dependency-of`) compared with `4/4` in SPDX (`spdxhelpers/to_format_model.go:58–69, 170–218, 698–748`).

4. **Cross-Alias VEX Revocation Bypass and the Two-Sided Disconnected-SBOM Impossibility (`openvex/go-vex@42a83ee2`, `aquasecurity/trivy@edf9f5c1`, `Zięba-Kozarzewski 2026`):**
   - `go-vex` `SortStatements` (`statement.go:142–173`) sorts primarily by `Vulnerability.Name` ASCII order and only secondarily by `Timestamp`. While `Document.EffectiveStatement` (`vex.go:173–209`) resolves timestamps directly (`govex_effective_stmt_status='affected'`), `Document.Matches` (`vex.go:227–244`) calls `SortStatements` and `Trivy` (`openvex.go:69`) selects `stmts[len(stmts)-1]`. Because **`6/6` standard ecosystem prefixes** (`GHSA-`, `GO-`, `RUSTSEC-`, `PYSEC-`, `OSV-`, `SNYK-`) sort ASCII-after `'CVE-'` (`prefixes_sorting_after_cve='6/6'`), an older `GHSA-*` `not_affected` statement (`2026-01-10`) sorts after and **falsely suppresses a newer `CVE-*` `affected` revocation (`2026-02-20`)** (`trivy_openvex_falsely_suppresses_revoked_cve=True`).
   - Across `77,092` parseable Wild SBOMs (`wild_sbom_parseable_total=77092`), **`61.68%` (`47,552`)** fail to form a connected graph (`52.9%` `NO_EDGES` + `8.8%` `degenerate-with-edges`), and `Syft` container SBOMs leave **`95%–98%` of components as orphans** (`97%` on `gitlab/gitlab-ce:17.0`). On a `97%`-orphan container SBOM (`100` vulnerable leaves), `Trivy`'s `reachRoot` orphan fail-safe (`vex.go:195–199`) terminates DFS before visiting `root`, collapsing root-scoped OpenVEX, CSAF `default_component_of`, and root-BOM-Link CycloneDX suppression from **`100/100` down to `3/100`** (whereas leaf-targeted CycloneDX BOM-Links preserve `100/100`), while closed-world reachability ("no path from root $\implies$ unreachable") drops `97/100` Known Exploited Vulnerabilities (`closed_world_kev_retained_on_degen='3/100'` vs. open-world three-valued `{reachable, unreachable, unknown}` gating at `'100/100'`).

5. **Hallucination Benchmark Defects, Benign vs. Adversarial Decoding Trade-Offs, and Universal `Slopsquatting` (`Spracks/PackageHallucination@bd3031cc`, `Spracklen '25`, `Churilov '26`, `Djire '26`):**
   - In `Spracks/PackageHallucination`, `refine_package_list` (`custom_parse_javascript.py:15`) aliases and mutates the caller's list in-place (`parser_caller_list_mutated=True`), and `refine_package_list`, `extract_npm_packages` (`L111–136`), and `extract_npm_install` (`L163–188`) call `new_list.remove(item)` during iteration so adjacent relative imports and CLI flags leak as false hallucinations (`['--legacy-peer-flag', './config']`) while `len(i) > 2` erases 2-character packages (`['ws', 'pg']`). Separately, pure PyPI-snapshot validation without `sys.stdlib_module_names` (`Djire et al., ASE '26 §5.1 Table 2`) inflates empirical Python PHR by `+7.6` to `+9.4 pp` (`64.71%` vs. `11.76%` on Probe 5's fixture, while PyPI-hosted backports `['dataclasses', 'pathlib']` pass), whereas `Spracks`'s manually appended `pypi_package_names.csv:500315–500565` block omits **`22` public `len > 2` `sys.stdlib_module_names` modules** (`xml`, `concurrent`, `mmap`, `atexit`, `stringprep` [`L500328` `'strinprep'` typo], etc.; `41.18%` on the fixture).
   - Under **benign prompts (`Djire et al., §5.3 Table 4`)**, `RAG` lowers mean PHR from `29.7%` to `18.1%` (`19/32`) but degrades JavaScript on `7/8` models (`+12.7 pp`); under **adversarial prompts (`§5.6 Table 5`)**, `DoLa` backfires in **`24/32` (`75.0%`)** configurations over `Greedy`, whereas benign JavaScript degradation disappears and `RAG` achieves the lowest PHR in **`16/32` (`50%`)** overall and **`5/8` JavaScript models** (`RAG` + `Self-Refine` win `29/32`; `Gemma-4b` + `RAG` reaches `11.4%` on Python). Across five 2026 frontier models (`4.62%–6.10%` PHR, `Churilov 2026`), **`127` package names are hallucinated identically by all 5 models**, of which **`53` (`41` PyPI, `12` npm)** remain immediately attacker-registrable: in Probe 5's `[illustrative analytical model]` (`Basis: derived`), **5-of-5 cross-model consensus voting still compromises `53/53` (`100%`)**, whereas a pre-cutoff registry-timestamp or committed-lockfile gate reduces compromise to **`0/53`**.

## Applicability

This report applies to source and binary vulnerability reachability analyzers (`govulncheck`, `osv-scanner`, `cargo-audit`, Eclipse Steady/`Vulas`, Maven call-graph analyzers), OSV range evaluators, Python and container SBOM generators (`Syft`, `Trivy`), machine-readable VEX libraries and scanners (`OpenVEX v0.2.0`, `go-vex`, `CSAF v2.0`, `CycloneDX VEX`, `Trivy`), and LLM package-recommendation benchmarks and `slopsquatting` defenses (`observed_at`: `2026-11-23`). Version resolution SAT/CDCL solvers, static SemVer ABI checkers, and cryptographic transparency logs (`TUF`, `Uptane`, `in-toto`, `SLSA`) lie outside this report's scope. The sixteen subjects in `REPORT.json` relate across four layers:

1. **Call-Graph Reachability, Binary Scanning, and Advisory Range Semantics (`normative` + `documentation` + `source` + `derived`):**
   - `golang/vuln@ef4cb2f7cae47fe3e21fc596455f694951867b29` and `golang/tools@70e48cd7db64b457438d8d171c8734478f84a52f` (`go/callgraph/vta`) govern Go SSA entry-point selection, two-pass `CHA -> VTA -> VTA` call-graph slicing, binary symbol matching, and `govulncheck -format openvex` emission.
   - `google/osv-scanner@925d1b4cf77c4dd26540672f6fa045a3a8327754` and `rustsec/rustsec@9284e112641a1992f022711395389d9246aa9837` characterize experimental Rust `cargo build` + DWARF symbol reachability, Go SCALIBR VEX enrichment, and `Cargo.lock` / binary panic-string auditing, interpreted against `ossf/osv-schema@e34af15e6f05eff600d1223c05f60d39b53bc131` and empirical call-graph studies (`Ponta et al., ICSME 2018 & EMSE 2020`; `Mir et al., SANER 2023`; `Shi et al., EMNLP 2026`).
2. **Manifest-to-SBOM Extraction and Serialization Fidelity (`documentation` + `source` + `derived`):**
   - `anchore/syft@9ad9aa5e80a6762c33b0344d252ec669ae53afdc` and `aquasecurity/trivy@edf9f5c13d27ba1f6b1bc747f2f41a383dc56dc9` are compared directly on `requirements.txt` and `pyproject.toml` inputs and CycloneDX vs. SPDX relationship serialization, contextualized by `Zhou et al. (CODASPY 2026)`, `Cofano et al. (TrustCom 2024)`, `Yu et al. (DSN 2024)`, and `O'Donoghue et al. (SCORED 2024)`.
3. **VEX Statement Ordering and Disconnected-SBOM Graph Traversal (`normative` + `documentation` + `source` + `derived`):**
   - `openvex/spec@93139bd2c65390b504e47f82f11c50451289f93a` (`v0.2.0`), `openvex/go-vex@42a83ee2b1ae9e8b1cde8f5161dc869fc76fdefa`, and `aquasecurity/trivy@edf9f5c13d27ba1f6b1bc747f2f41a383dc56dc9` (`pkg/vex/{vex,openvex,csaf,cyclonedx}.go`) interact with the empirical SBOM topology distribution measured by `Zięba-Kozarzewski (2026)` across `77,092` parseable Wild SBOMs.
4. **LLM Package Hallucination Measurement and `Slopsquatting` Mitigation (`documentation` + `source` + `execution` + `derived`):**
   - `Spracks/PackageHallucination@bd3031cce6a0007997a0604d3ad3365031ed79b2` (`Spracklen et al., USENIX Security 2025`), `Churilov (2026)`, and `Djire et al. (ASE 2026)` characterize parser and allowlist measurement artifacts, benign vs. adversarial decoding behavior, and cross-model slopsquatting defenses.
   - Evidentiary role boundary: findings on upstream Go and Rust repositories (`golang/vuln`, `golang/tools`, `google/osv-scanner`, `rustsec/rustsec`, `anchore/syft`, `aquasecurity/trivy`, `openvex/go-vex`) carry `Basis: source + derived` (plus `normative` where `OSV Schema` or `OpenVEX v0.2.0` rules apply) because the preserved verification script (`scripts/verify_vuln_reachability_sbom_slopsquatting.py`) executes faithful Python 3.10+ standard-library ports of the audited upstream functions (`execution` of the preserved probe under **Evidence** and **Revalidation**) rather than invoking compiled Go or Rust subject binaries.

## Findings

### 1. Call-Graph Vulnerability Reachability, Binary Stripping, and VEX Justification Bugs (`govulncheck` and `OSV-Scanner`)

`Basis: documentation + source + derived`

#### 1.1 Ecosystem Call-Graph Pruning vs. Static Unsoundness (`Mir et al.`, `Ponta et al.`, `Shi et al.`)
Metadata-only Software Composition Analysis (SCA) exhibits severe false-positive inflation because importing a library rarely reaches its vulnerable methods, yet static call graphs alone are neither sound nor sufficient for exploitability:
- **Maven Ecosystem Pruning (`Mir, Keshani, & Proksch, SANER 2023`, `§IV Approach`, `§§V-B–V-D`, `Table IV`, `Figs. 3, 6, 7, 8`):** Across **3,000,000 versioned Maven packages** and **517 CVEs**, transitive package-level matching $D_p(\max)$ flags **`~1.1M` (`40%`)** package versions (`369K` under direct $D_p(1)$), whereas `OPAL` method-level call-graph reachability $D_m(\max)$ flags **`10^{4.15} ≈ 14,125` (`<1%` of all packages, `~1.2%` of $D_p(\max)$ — a `>98.7%` metadata false-positive rate)**. Across the top-10 CVEs (`786,921` package versions under $D_p(\max)$), only **`4,485` (`0.57%`)** are call-graph reachable (`CVE-2020-36518` in `jackson-databind`: `233,430` vs. `1,153` [`0.49%`]; `CVE-2022-24823` in `netty-codec-http`: `142,177` vs. `90` [`0.063%`]; `CVE-2022-24329` in `kotlin-stdlib`: `82,060` vs. `32` [`0.039%`]). In `§V-B` (`Figs. 3, 6`), $|D_m(1) \cap D_m(\max)| / |D_m(\max)| = 0.53$ ($10^{3.88}$ vs. $10^{4.15}$), while the cumulative depth-cutoff analysis in `§V-D` (`Figs. 7–8`) shows direct dependencies $D_m(1)$ accounting for **`55.8%`** of reachable vulnerabilities and depth-3 truncation $D_m(3)$ capturing **`94%`**.
- **Static + Dynamic Complementarity (`Ponta, Plate, & Sabetta, ICSME 2018`, `§IV-A`, p. 455 & `Fig. 6`; `EMSE 2020`):** Across **`>250,000` industrial scans** of **`496` Java applications** since December 2016 in Eclipse Steady/`Vulas` (which pairs patch-derived AST/bytecode construct lists and `Reachable Body Stability` [`RBS`] with analysis), vulnerable library constructs were reachable statically or dynamically in **`131` out of `496` applications** across **`390` `(application, vulnerability)` pairs**. In **`32` of `390` pairs (`8.2%` of reachable pairs; reported by the authors as a `7.9%` increase of evidence)**, reachability was established *only* by combining dynamic JVM touch-point tracing with static bytecode call-graph expansion across reflection and framework inversion-of-control boundaries.
- **Infeasible Call Paths and Agent Justification Cliff (`Shi et al., VEX-Bench, EMNLP 2026`, `§§3.2–4.4`, `Tables 1–3`, `Figs. 2, 4, 5`):** Across `75` real-world Go, Python, and Java cases (`67` CVEs across `35` repositories; `88.3%` expert review confirmation in `§3.2` after calibration Fleiss' $\kappa = 0.667$), `22` (`29.3%`) are `affected` and `53` (`70.7%`) are `not_affected` (`Figure 2` & `Figure 4`: `38` [`50.7%`] `code_not_reachable`, `7` [`9.3%`] `requires_configuration`, **`6` [`8.0%`] `code_not_present`**, and `2` [`2.7%`] `requires_environment`). Traditional reachability tools struggle (`Table 3`: `govulncheck` builds and analyzes only **`63.3%`** of historical Go targets with `Acc = 36.7%, Prec = 22.2%, Rec = 28.6%, F1 = 25.0%`, vs. `OSV-Scanner` reachability at `Cov = 100.0%, F1 = 42.9%`), and **`70%` of their false positives remain labeled `code_not_reachable`** (`§4.3`, p. 8) due to infeasible intra-procedural guards. Frontier LLM coding agents exhibit a steep **status-to-justification cliff** (`Table 2`: `GPT-5.5` drops from `89.3%` status accuracy / `79.9%` status F1 to `78.2%` justification accuracy / `73.5%` justification macro-F1; `Claude Opus 4.6` records `88.4%` status accuracy / `81.6%` status F1; `GPT-5.4 mini` drops `82.2% -> 66.7%` [`-15.5 pp`]; `DeepSeek-V4-Flash` reaches `47.2% ± 3.3%` justification macro-F1; and `MiniMax-M2.7` drops to `44.8% ± 12.0%`).

#### 1.2 `golang/vuln@ef4cb2f7` + `golang/tools@70e48cd7` Two-Pass `CHA -> VTA -> VTA` Lattice and Four Blind Spots
Auditing `golang/vuln/internal/vulncheck/{utils,slicing,entries,source,binary}.go` alongside `golang/tools/go/callgraph/vta/{vta,graph,utils}.go` and porting `typePropGraph` + `propagate` + `resolves` in Probe 1 isolates both the precision mechanism and four failure modes:
1. **Per-Parameter `typePropGraph` Flow and Why Two `VTA` Passes Are Required (`vulncheck/utils.go:63–89`, `slicing.go:14–46`, `vta/vta.go:79–165`, `vta/graph.go:312–352, 660–698`):**
   - Unlike Rapid Type Analysis (`RTA`), `vta.CallGraph(funcs, initial)` constructs a directed per-SSA-variable type-propagation graph (`typePropGraph`): `addArgumentFlows` (`graph.go:660–698`) adds inflow edges from call-site arguments into each `siteCallees` target's formal `Params`, and `resolve(c)` (`vta.go:142–150`) resolves an interface or indirect function call strictly from `types.propTypes(local{val: c.Common().Value})`. Consequently, an unpassed closure `main.unusedClosure` referenced inside `main.main` (`func_val_refs`) is included in `fslice_0` and `cha_cg["main.runHook"]` yet pruned immediately in Pass 1 (`vta_unpassed_closure_pruned_pass1=True`).
   - In Probe 1's 6-sink Go SSA program (`GO-TAR`, `GO-XML`, `GO-YAML`, `GO-REFL`, `GO-TOML`, `GO-MODONLY`), `main.main` calls `main.decodeInput(SafeJSON{})` (`SafeJSON.Decode -> GO-TAR`) and `main.runHook(main.safeSink)`, while uninstantiated `DeadXML.Decode` (`implements_iface="Decoder"`) calls both `vuln_xml.Parse` (`GO-XML`) and **`main.runHook(main.evilSink)`** (`evilSink -> GO-YAML`). `CHA` flags **`cha_flagged = ['GO-TAR', 'GO-XML', 'GO-YAML']`**.
   - In **VTA Pass 1 (`vta_1`)**, `DeadXML` is uninstantiated in `fslice_0`, pruning `main.decodeInput -> DeadXML.Decode` (`GO-XML` eliminated). *However*, `b.visit(fslice_0)` (`graph.go:339–343`) still visits every function in `fslice_0`, so `DeadXML.Decode`'s static call `main.runHook(main.evilSink)` injects `func(main.evilSink) -> local{main.runHook:param0}` (`graph.go:696`), retaining `main.runHook -> main.evilSink -> GO-YAML` (**`vta_pass1_flagged = ['GO-TAR', 'GO-YAML']`**).
   - Re-slicing `fslice_1 = forwardSlice({main.main}, vta_1)` evicts `DeadXML.Decode` (now unreachable in `vta_1`), so **VTA Pass 2 (`vta_2`)** removes the `evilSink` inflow edge into `main.runHook:param0` and converges to **`vta_pass2_flagged = ['GO-TAR']`**.
2. **Reflection, Generic Entry-Point, and Binary-Stripping Blind Spots:**
   - **Reflection & `unsafe` (`vta.go:74–75`):** `main.main` invokes `reflSvc.Trigger -> vuln_refl.Exec` via `reflect.Value.Call`. Because VTA adds zero reflection edges, `govulncheck` silently misses `GO-REFL` (`ground_truth_main = ['GO-REFL', 'GO-TAR']`, **`vta_missed_reflection = ['GO-REFL']`**).
   - **Generic Library Entry Points (`entries.go:17–46`, `https://go.dev/issue/57221`):** Scanning library package `libpkg` whose exported API is generic `ParseGeneric[T]` (`-> GO-TOML`) yields zero concrete `memberFuncs` when uninstantiated (`L17–18` `TODO`), resulting in **`generic_lib_entries_count = 0`** and **`generic_lib_flagged = []`** (`CGO` `import "C"` calls are similarly opaque).
   - **Unstripped vs. Stripped Binary Degradation (`binary.go:46–48, 107–114`):** Binary mode builds **no call graph** (`L47`), flagging every symbol present in linked package symbol tables (`binary_unstripped_flagged = ['GO-REFL', 'GO-TAR', 'GO-XML', 'GO-YAML']`). When symbol tables are stripped (`-ldflags="-s -w"`, `len(bin.PkgSymbols) == 0`, `L107–111`), `govulncheck` falls back to `allKnownVulnerableSymbols(affVulns)`, reporting **all `6` module-level advisories as called** (`binary_stripped_flagged = ['GO-MODONLY', 'GO-REFL', 'GO-TAR', 'GO-TOML', 'GO-XML', 'GO-YAML']`).

#### 1.3 Non-Antisymmetric `moreSpecific` Bug in `govulncheck -format openvex` and SCALIBR Conflation
- **`golang/vuln/internal/openvex/handler.go:83–128, 216–227`:** `handler.Finding` retains only the highest-specificity finding level (`required=0`, `imported=1`, `called=2`) via `moreSpecific(f1, f2)`. At `L102–107`, *both* `fr1.Package != "" && fr2.Package == ""` and `fr1.Package == "" && fr2.Package != ""` return **`-1`** instead of `-1` and `+1`, violating comparator antisymmetry on **`antisymmetry_violations = ['(required,imported):-1_vs_-1', '(imported,required):-1_vs_-1']`**. While `source.go:83, 94` normally emits `required` before `imported` (`openvex_req_then_imp = 'vulnerable_code_not_in_execute_path'`), replaying or feeding `[imported, required]` causes `moreSpecific(required, imported) == -1` to overwrite `imported` with `required`, emitting **`openvex_imp_then_req_buggy = 'vulnerable_code_not_present'`** (fixed to `'vulnerable_code_not_in_execute_path'` when `L106` returns `+1`).
- **`google/osv-scanner/internal/scalibrenricher/govulncheck/source/govulncheck.go:117–139`:** Conversely, `osv-scanner`'s SCALIBR enricher tests only whether any trace has `trace[0].Function != ""` (`L125–138`), emitting **`scalibr_unimported_mod_signal = 'vulnerable_code_not_in_execute_path'`** even for unimported `go.mod`-only modules.

---

### 2. `OSV-Scanner` Rust DWARF/Regex Defects, `cargo-audit`, and Normative OSV Range Algebra

`Basis: normative + source + derived`

1. **Compile-Time Arbitrary Code Execution and `rustsec` Binary Fallback (`osv-scanner` `rust.go:31, 234–248`; `rustsec` `auditor.rs:159–202`, `binary_deps.rs:24–55`):**
   - `osv-scanner` experimental Rust source analysis executes `cargo build --workspace --all-targets --release` (`RUSTFLAGS="-C opt-level=3 -C debuginfo=1 -C embed-bitcode=yes -C lto -C codegen-units=1 -C strip=none"`), running untrusted `build.rs` build scripts and procedural macros on the host. Static `cargo-audit` (`auditor.rs:159–202`) checks `Cargo.lock` without function-level reachability, and `cargo audit bin` (`binary_deps.rs:24–55`) falls back on binaries compiled without `cargo-auditable` (`.dep-v0`) to `quitters` panic-message scraping (`BinaryReport::Incomplete`), missing panic-free dependencies.
2. **Four Deterministic Source Defects in `osv-scanner` (`rust.go:154–174, 275–304`, `go.go:104–137`, Probe 2):**
   - **`cleanRustFunctionSymbols` `<[\w,]+>` Recall Collapse (`rust.go:288–304`):** Because `\w` matches only `[0-9A-Za-z_]`, `antiGenericRegex = <[\w,]+>` achieves **`rust_regex_upstream_recall = '2/6'`** (`rust_regex_failed_count = 4` vs. `rust_regex_balanced_recall = '6/6'`), failing on const-generic arrays (`smallvec::SmallVec<[u8; 4]>::grow`—the exact `smallvec` crate cited in `rust.go:84`), nested generics (`mycrate::Parser<alloc::vec::Vec<u8>>::parse`), lifetimes (`http::HeaderMap<&'static str>::insert`), and generic trait impls (`<smallvec::SmallVec<[u8; 4]> as core::ops::Drop>::drop`, where `antiTraitImplRegex` runs *after* `antiGenericRegex` failed to strip `<[u8; 4]>`).
   - **LTO Inlining Blindness vs. Dead Exports (`rust.go:154–174`):** `functionsFromDWARF` inspects only `DW_TAG_subprogram`, skipping `DW_TAG_inlined_subroutine` entries produced under `opt-level=3 + lto` (**`dwarf_inlined_detected = False`**) while flagging uncalled `#[no_mangle]` / `--all-targets` library exports (**`dwarf_dead_export_flagged = True`**).
   - **Multi-Rule Cargo `.d` Split Error (`rust.go:275–280`) and Go `v1`/`v2` Inheritance (`go.go:104–126`):** Splitting the entire `.d` file on `": "` rejects valid multi-rule Cargo depfiles (**`cargo_depfile_multi_rule_err = True`**), and `vulnHasImportsField` (`go.go:110` `TODO`) ignores version ranges when checking `affected[].ecosystem_specific.imports`, attributing `v2.x` symbol metadata to unannotated `v1.4.0` modules (**`go_v1_false_imports_inheritance = True`**).
3. **Normative OSV `GIT` Ancestry vs. `SEMVER` Pre-Release Evaluation (`ossf/osv-schema@e34af15e`, `docs/schema.md:1144–1148, 1269–1398`, `proto/vulnerability.proto:69–119`):**
   - **`GIT` `fixed` vs. `limit` Partial-Order Trap (`schema.md:1364–1398`):** Over commit DAG `root -> X -> A -> B -> C -> Y` (`main`) with unmerged sibling branches `A -> D -> E` (`release-1.x`) and `X -> F` (`feature`), `[{"introduced": "X"}, {"fixed": "Y"}]` evaluates $X \le c \land \neg(Y \le c)$, flagging all **`7`** unfixed commits **`osv_git_fixed_affected = ['X', 'A', 'B', 'C', 'D', 'E', 'F']`**. Replacing `fixed` with `limit` (`BeforeLimits`: $c \ne Y \land c \in \text{ancestors}(Y)$, equivalent to `git rev-list X..Y`) flags only **`osv_git_limit_affected = ['X', 'A', 'B', 'C']`**, creating **`3` silent false negatives `osv_git_limit_false_negatives = ['D', 'E', 'F']`** across unmerged branches.
   - **`SEMVER` Pre-Release Ordering (`1.0.2-rc.1 < 1.0.2`):** Because SemVer 2.0.0 §11 orders pre-releases strictly before their normal release (`1.0.1 < 1.0.2-rc.1 < 1.0.2`), `{"introduced": "1.0.0"}, {"fixed": "1.0.2"}` flags `1.0.2-rc.1` (**`osv_semver_prerelease_before_fix = True`**), whereas `{"introduced": "1.0.0"}, {"last_affected": "1.0.1"}` treats `1.0.2-rc.1 > 1.0.1` as unaffected (**`osv_semver_last_affected_ceiling_fn = True`**).

---

### 3. Generator-Induced SBOM Divergence and Format Edge Loss (`Syft` vs. `Trivy`)

`Basis: documentation + source + derived`

Across `496` Grype-scanned (`5,615` vulnerabilities) and `486` Trivy-scanned (`5,555` vulnerabilities) repositories (`Zhou, Dacier, & Konstantinou, CODASPY '26`, `Tables 4–8` & `Appendix A Table 9`), automated lockfile generation succeeds on `96.4%` (`532/552`) of Rust repositories yet drops to **`19.1%` (`42/220`)** on Python repositories; while `Syft` and `Trivy` reach `100.00%` component agreement on committed lockfiles (`Table 5`), end-to-end SBOM vulnerability scanning exhibits a **`92.0%` false-positive rate** (`104/113` reported CVEs unconfirmed, and `78.6%` [`33/42`] unconfirmed even on imported libraries, `Table 7`; Go call-graph reachability cuts `121` reported Go alerts across `12` repositories to `31` confirmed reachable = **`74.4%` reduction** in `§5.7 Table 8` and `Appendix A Table 9`, p. 14). Differential studies across **`7,876` open-source projects spanning `9` programming languages / package ecosystems** (`535` Python, `819` Ruby, `384` PHP, `398` Java, `1,019` Swift, `700` C#/.NET, `994` Rust, `2,367` Go, and `660` JavaScript in `Yu, Song, Hu, & Yin, DSN 2024`, Abstract & `§III`, pp. 29, 31), **`2,313` Docker images** (`O'Donoghue et al., SCORED '24`, pp. 67–76), and `12` Python build backend/frontend combinations (`Cofano, Benedetti, & Dell'Amico, TrustCom 2024`, `Tables I–V`, `T1`–`T6`, `E1`–`E3`) confirm widespread manifest-parser divergence.

Porting `anchore/syft@9ad9aa5e` (`parse_requirements.go:129–250`, `cyclonedxhelpers/to_format_model.go:235–293`, `spdxhelpers/to_format_model.go:58–69, 170–218, 698–748`) and `aquasecurity/trivy@edf9f5c1` (`pip/parse.go:39–116, 167–170`, `pyproject.go:45–60`) in Probe 3 over a 10-entry `requirements.txt` (`total_declared_reqs = 10`) isolates four exact divergences:
1. **`70%` Default Manifest Erasure on Disjoint `3/10` Subsets:** Under default settings (`GuessUnpinnedRequirements=false`, `useMinVersion=false`), both tools retain only **`3/10`** packages (`syft_default_count = 3`, `trivy_default_count = 3`, **`default_omitted_count = 7`**), dropping `>=`, `~=`, `==3.1.*`, unpinned `pyyaml`, and `git+https://` VCS URLs (where `Syft` regex-parses `Name="git"`, `VersionConstraint=""` and drops `version == ""` at `L142–148`). On the remaining `3`, `Syft` (`L195–201`) checks `===` before `==` and retains **`syft_default_certifi_triple_eq = '2024.2.2'`** while rejecting `pyjwt==2.8.0,!=2.8.1` at `L192` (`!=` check), whereas `Trivy` (`pip/parse.go:100`) strips `"=="` from `"===2024.2.2"` leaving invalid `"=2024.2.2"` (**`trivy_default_certifi_triple_eq = None`**) while extracting **`trivy_default_pyjwt = '2.8.0'`**.
2. **Ceiling vs. Floor Guessing and `Syft` `strings.SplitAfter` Dead Code:** With heuristic guessing enabled, `werkzeug>=2.0.0,<=2.2.2` resolves to upper ceiling **`syft_guess_werkzeug = '2.2.2'`** (`v.GreaterThan(closestVersion)`, `L240`) vs. lower floor **`trivy_min_werkzeug = '2.0.0'`** (`useMinVersion=true`). In `Syft`'s `guessVersion` (`L224–239`), `strings.SplitAfter("==2.8.0", "=")` yields `["=", "=", "2.8.0"]`, so `parts[1] == "="` fails `pep440.Parse` (`L228`) and makes `L236–239` (`if strings.Contains(part, "==")`) **unreachable dead code** (**`syft_guess_pyjwt_splitafter_bug = None`**).
3. **`Trivy` `pyproject.toml` Extras Leak and Poetry Shadowing (`pyproject.go:45–60`):** `MainDeps()` merges every `[project.optional-dependencies]` group into production dependencies (**`trivy_pep621_extras_leaked = ['mypy', 'pytest', 'sphinx']`**), and because `L47` checks `if p.Project.Dependencies != nil || p.Project.OptionalDependencies != nil` before `L56` `else if p.Tool.Poetry.Dependencies.Set != nil`, a Poetry project declaring `[project.optional-dependencies]` without `[project.dependencies]` loses **100% of its `[tool.poetry.dependencies]`** (**`trivy_poetry_deps_retained_when_optional_set = []`**).
4. **CycloneDX vs. SPDX Relationship Loss (`cyclonedxhelpers` vs. `spdxhelpers`):** `Syft`'s `isExpressiblePackageRelationship` (`cyclonedxhelpers/to_format_model.go:235–242`) serializes only `dependency-of` between two packages (**`syft_cdx_relationships_kept = '1/4'`**), discarding `contains`, `evident-by`, and `ownership-by-file-overlap`. By contrast, `spdxhelpers/to_format_model.go` converts all four `artifact.Relationship` types via `toRelationships` and `lookupRelationship` (`L58–69, 698–748`: `ContainsRelationship -> CONTAINS` including `isFileContainsPackage` at `L730–734`, `DependencyOfRelationship -> DEPENDENCY_OF`, and `OwnershipByFileOverlapRelationship` / `EvidentByRelationship -> OTHER` with descriptive `RelationshipComment`) alongside `toRootRelationships` (`L170–218`) (**`syft_spdx_relationships_kept = '4/4'`**).

---

### 4. Cross-Alias VEX Revocation Bypass and the Two-Sided Disconnected-SBOM Impossibility

`Basis: normative + documentation + source + derived`

#### 4.1 `openvex/go-vex` + `Trivy` Cross-Alias ASCII Ordering Bug (`statement.go:142–173`, `vex.go:173–244`, `trivy/pkg/vex/openvex.go:60–87`)
Under `OpenVEX v0.2.0` (`OPENVEX-SPEC.md:190–236, 343–378, 417–499`), later statements chronologically supersede earlier statements for the same product and vulnerability (`not_affected` requires `justification` or `impact_statement`; `affected` requires `action_statement`). In `openvex/go-vex@42a83ee2`:
- `SortStatements` (`statement.go:144–172`) sorts **primary-key by `strings.Compare(Vulnerability.Name)`** and only **secondary-key by `Timestamp`**.
- Although `Document.EffectiveStatement` (`vex.go:173–209`) compares timestamps directly across aliases (`govex_effective_stmt_status = 'affected'`), `Document.Matches` (`vex.go:227–244`) returns `SortStatements(matches, t)`, and `Trivy`'s `OpenVEX.NotAffected` (`pkg/vex/openvex.go:69`) picks **`stmt := stmts[len(stmts)-1]`**.
- Because **`6/6` major ecosystem advisory prefixes** (`GHSA-`, `GO-`, `RUSTSEC-`, `PYSEC-`, `OSV-`, `SNYK-`) sort ASCII-after `'CVE-'` (`prefixes_sorting_after_cve = '6/6'`), an older `2026-01-10` statement filed under `GHSA-4374-p667-p6c8` (`status: "not_affected"`) sorts *after* and **falsely suppresses a newer `2026-02-20` `CVE-2023-45288` revocation (`status: "affected"`)** (**`trivy_openvex_falsely_suppresses_revoked_cve = True`**).

#### 4.2 The Two-Sided Disconnected-SBOM Impossibility (`Zięba-Kozarzewski 2026` $\times$ `Trivy reachRoot`)
Across **`77,092` parseable Wild SBOMs** (`wild_sbom_parseable_total = 77092` of `78,612` total in `Zięba-Kozarzewski 2026`, `Table I`), `40,756` (`52.9%`) have `NO_EDGES` and `6,796` (`8.8%`) are `degenerate-with-edges`, leaving **`wild_sbom_non_connected_pct = 61.68%`** non-connected (`Syft` repository SBOMs: `82.6% + 7.1% = 89.7%` non-connected in `Table II`; `Syft 1.42.3/1.42.4` production container SBOMs in `Table III`: **`95%` orphans** on `continuumio/anaconda3` [$V=8,744, E=2,002, E/V=0.228$] to **`98%` orphans**, with `gitlab/gitlab-ce:17.0` at $V=87,777, E=2,360, E/V=0.027$, **`97%` orphans**).

Evaluating `Trivy`'s `reachRoot` (`pkg/vex/vex.go:178–219`) on Probe 4's `97%`-orphan container SBOM (`100` vulnerable leaves: `3` wired to `root`, `97` disconnected) exposes a **two-sided impossibility for two-valued graph consumers**:
1. **Broken Product-Scoped VEX Suppression (`vex.go:181, 191, 195–199`):** When VEX scopes `not_affected` to `(product = root_oci_image, subcomponent = leaf_purl)` (`OpenVEX`, `CSAF` `default_component_of` at `csaf.go:92–115`, or `CycloneDX` root BOM-Link at `cyclonedx.go:46–74`), `notAffected(leaf, nil)` and `notAffected(leaf, leaf)` return `false` (`leaf != root`), and `vex.go:195–199` returns `true` (`unvisited_parents == 0`) **before DFS ever visits `root`**—collapsing suppression from **`connected_openvex_suppressed = '100/100'`** to **`degen_97pct_orphan_openvex_suppressed = '3/100'`**, **`degen_97pct_orphan_csaf_suppressed = '3/100'`**, and **`degen_97pct_orphan_cdx_root_suppressed = '3/100'`** (only leaf-targeted CycloneDX BOM-Links short-circuit at `L181`: **`degen_97pct_orphan_cdx_leaf_suppressed = '100/100'`**).
2. **Closed-World KEV Erasure vs. Open-World Three-Valued Gating:** Treating missing edges as closed-world unreachability drops `97/100` Known Exploited Vulnerabilities (**`closed_world_kev_retained_on_degen = '3/100'`**), whereas gating reachability on `orphan_ratio` via an open-world three-valued lattice `{reachable, unreachable, unknown}` (`orphan_ratio > 0.5 -> unknown`, treated fail-closed for KEVs) retains **`open_world_three_valued_kev_retained = '100/100'`**.

---

### 5. LLM Package Hallucination Benchmark Defects, Benign vs. Adversarial Decoding, and Universal `Slopsquatting`

`Basis: documentation + source + execution + derived`

#### 5.1 Parser Bugs and Two Distinct Python Stdlib Validation Pitfalls (`Spracks/PackageHallucination@bd3031cc` and `Djire et al., ASE '26 §5.1`)
1. **Caller-List Aliasing, In-Place `remove` Loop Skips, and 2-Character Package Erasure (`custom_parse_javascript.py`, `custom_parse_python.py`):**
   - In `custom_parse_javascript.py` (`480L`), `refine_package_list` (`L15`: `new_list = lst`) aliases and mutates the caller's input list in-place (**`parser_caller_list_mutated = True`**), whereas `extract_npm_packages` (`L111`: `new_list = list(set(matches))`) and `extract_npm_install` (`L163`: `new_list = list(set(matches))`) allocate fresh lists from regex matches. All three functions share the in-place `for item in new_list: new_list.remove(item)` loop-skip defect (`L17–34`, `L113–130`, `L165–182`; plus single-occurrence `if core_item in new_list: new_list.remove(core_item)` at `L36–38`, `L132–134`, `L184–186`): passing consecutive relative imports `['./utils', './config']` and CLI flags `['--save-exact-custom', '--legacy-peer-flag']` shifts index $i+1$ into $i$, leaking **`parser_leaked_local_and_cli_as_hallucinations = ['--legacy-peer-flag', './config']`** as false npm hallucinations, while `delete_dupes_and_empty` (`custom_parse_python.py:4–7`, `custom_parse_javascript.py:198–201`) enforces `len(i) > 2`, erasing valid 2-character packages (**`parser_erased_valid_2char_packages = ['ws', 'pg']`**) and 2-character stdlib modules (`os`, `re`, `io`) from denominators.
2. **Pure-PyPI Stdlib Omission (`Djire et al. §5.1 Table 2`) vs. `Spracks`'s `22`-Module Appended-CSV Gap (`package_detection.py:9–17, 63–93`):**
   - **Pure PyPI Registry Snapshot Without `sys.stdlib_module_names` (`Djire et al., ASE '26 §5.1 Table 2`, p. 5):** Validating generated Python imports against a raw PyPI package snapshot without subtracting `sys.stdlib_module_names` passes PyPI-hosted backport packages (`dataclasses`, `pathlib`, `asyncio`, `graphlib`, **`pypi_backports_not_flagged = ['dataclasses', 'pathlib']`**) but falsely flags stdlib-only modules absent from PyPI (`os`, `math`, `json`, `tomllib`, `zoneinfo`, `sqlite3`, `urllib`, `xml`, `mmap`, `atexit`), inflating empirical Python PHR by **`+7.6` to `+9.4 pp`** (`+9.4 pp` on `Self-Refine`, `+9.1 pp` on `Nudging`, `+8.1 pp` on `Greedy`, `+7.6 pp` on `Vanilla`), and raising PHR on Probe 5's 18-import fixture (`17` surviving `len > 2` imports) from **`phr_with_stdlib_pct = 11.76%`** (`2/17`) to **`phr_pure_pypi_without_stdlib_pct = 64.71%`** (`11/17`, **`pure_pypi_stdlib_inflation_pp_on_fixture = 52.95` pp**).
   - **`Spracks/PackageHallucination`'s Corrupted Appended Stdlib Block (`Data/Python/pypi_package_names.csv:500315–500565` & `false_positive_packages.csv`):** `Data/Python/false_positive_packages.csv` (`3,884L`, read at `package_detection.py:67–68`) holds markdown/punctuation tokens (`!-git`, `!doctype`, `!function`) with `0` stdlib modules; instead, `Spracklen et al.` appended a manual stdlib list directly onto `Data/Python/pypi_package_names.csv` (`L500315–500565`), which covers `math` (`L500348`), `json` (`L500420`), `tomllib` (`L500381`), `zoneinfo` (`L500333`), `sqlite3` (`L500372`), and `urllib` (`L500440`), **but** pasted dotted documentation headings (`collections.abc` [`L500336`], `os.path` [`L500358`], `concurrent.features` [`L500406`], `xml.etree` [`L500429`], `xml.dom` [`L500430`], `xml.sax` [`L500433`]—rewritten by `normalize_python` at `package_detection.py:17` via `re.sub(r'[-_.]+', '-', name)` into `'xml-etree'` and `'concurrent-features'`) and misspelled `'stringprep'` as **`'strinprep'` (`L500328`)**. Consequently, **`spracks_missing_public_stdlib_gt2_count = 22` public `len > 2` `sys.stdlib_module_names` modules** are missing from both CSVs (`atexit`, `cProfile`, `concurrent`, `encodings`, `genericpath`, `idlelib`, `mmap`, `ntpath`, `nturl2path`, `opcode`, `posixpath`, `profile`, `pstats`, `pydoc_data`, `pyexpat`, `sre_compile`, `sre_constants`, `sre_parse`, `stringprep`, `this`, `turtledemo`, `xml`), inflating PHR on Probe 5's fixture to **`phr_spracks_appended_csv_pct = 41.18%`** (`7/17`, **`spracks_false_positive_stdlib_modules = ['atexit', 'concurrent', 'mmap', 'stringprep', 'xml']`**).

#### 5.2 Benign vs. Adversarial Decoding Trade-Offs and Universal Frontier `Slopsquatting` (`Spracklen '25`, `Djire '26`, `Churilov '26`)
1. **Fine-Tuning Utility Loss and Benign vs. Adversarial Inference-Time Defenses (`Spracklen et al., USENIX Security '25`; `Djire et al., ASE '26`, `§§5.1–5.6`, `Tables 1–5`, `Figs. 2–3`):**
   - Across `576,000` generated code samples and `2.23M` recommended packages (`440,445` [`19.7%`] total / `205,474` unique hallucinations; `5.2%` commercial vs. `21.7%` open-source, `Spracklen et al., Tables 7–8`), supervised fine-tuning lowers `DeepSeek` PHR from `16.14%` to `2.66%` (`Table 4`) **while cutting HumanEval `pass@1` in half from `51.4%` to `25.3%`** (`CodeLlama`: `19.6% -> 16.4%`, `Table 5`).
   - Under **benign package-recommendation prompts (`Djire et al., §5.3 Table 4`, pp. 6–7)**, `Greedy` and `Self-Refine` both reduce cross-model mean PHR from `29.7%` (`Vanilla`) to **`25.6%`** (with `Greedy` preserving the highest Package Utility `PU` in `§5.5 Fig. 3`), whereas **`RAG` lowers overall benign mean PHR from `29.7%` to `18.1%` (`19/32` lowest-PHR configurations) yet degrades JavaScript PHR on `7 of 8` models (`+12.7 pp` mean increase)** due to noisy npm retrieval.
   - Under **adversarial prompts (`Djire et al., §5.6 Table 5`, pp. 9–11; `4,000` prompts—`1,000` per language—explicitly instructing the model to install fabricated package names)**, vanilla PHR surges to **`46.6%–92.5%`**, and **Decoding by Contrasting Layers (`DoLa`) backfires in `24/32` (`75.0%`) configurations** relative to `Greedy` (`38.6% -> 94.1%` [`+55.5 pp`] on `DeepSeek-1.3B` Rust, `49.5% -> 87.1%` [`+37.6 pp`] on `Gemma-4b` Rust, `46.1% -> 81.3%` [`+35.2 pp`] on `Mistral-7b` Rust). Conversely, **the benign JavaScript degradation of `§5.3` is absent under adversarial attack (`§5.6`, p. 10): `RAG` achieves the lowest adversarial PHR in `16/32` (`50%`) configurations overall and `5/8` JavaScript models**, and `RAG` (`16/32`) plus `Self-Refine` (`13/32`) achieve the lowest PHR in **`29/32`** combinations (`Gemma-4b` + `RAG` reaching **`11.4%`** on Python).
2. **Universal Cross-Model `Slopsquatting` and Consensus Failure (`Churilov 2026` + Probe 5 `[illustrative analytical model]`, `Basis: derived`):**
   - Across `199,845` paired Python/JS prompts on five 2026 frontier models (`Claude Haiku 4.5` [`4.62%`], `Claude Sonnet 4.6` [`5.41%`], `Gemini 2.5 Pro` [`5.80%`], `DeepSeek V3.2` [`5.89%`], `GPT-5.4-mini` [`6.10%`]; `Churilov 2026`, `§§5–6`, `Tables 1–4`), overall PHR compresses into a `1.48 pp` band, yet **all 5 models identically hallucinate `churilov_universal_5model_total = 127` non-existent package names** (`109` PyPI, `18` npm). Registry similarity and blocklist rules block **`churilov_registry_blocked = 74`**, leaving **`churilov_universal_registrable = 53` names (`41` PyPI, `12` npm)** immediately registrable by an attacker—reinforced by **`spracklen_10of10_attractor_share = 0.43`** (`43%` of hallucination-inducing prompts regenerating the identical name in `10/10` runs vs. `39%` `0/10`, `Spracklen Fig. 5`).
   - In Probe 5's `[illustrative analytical model]` (`Basis: derived`), if an attacker registers all `53` universal names at $T_{\text{attack}} > T_{\text{cutoff}}$: unguarded live resolution compromises **`compromised_unguarded = '53/53'` (`100%`)**; **5-of-5 cross-model consensus voting** (filtering single-model hallucinations, `81%` in `Spracklen Fig. 8`) still passes every universal attractor and compromises **`compromised_5of5_consensus = '53/53'` (`100%`)**; whereas a **pre-cutoff registry-timestamp (`created_at <= T_cutoff`) or committed-lockfile (`--locked` / `--require-hashes`) gate** blocks every newly squatted package (**`compromised_snapshot_lockfile_gate = '0/53'`**).

## Boundaries

- **Camera-ready IEEE paywall bytes and commercial SCA / Grype VEX engines (`not examined`):** Direct byte-level inspection of the paywalled IEEE Xplore PDF of `Cofano et al. (TrustCom 2024)` (`10.1109/TrustCom63139.2024.00077`) was **not examined** (bibliographic metadata `pp. 427–434` was verified via Crossref and interior `Tables I–V`, `T1`–`T6`, `E1`–`E3` against the open-access `arXiv:2409.01214v1` text). Proprietary call-graph SCA engines (Snyk, Endor Labs, Mend), `anchore/grype`'s internal VEX matcher, and direct execution of compiled Go/Rust scanner binaries against external registries were **not examined**.
- **Soundness-preserving generic library entry-point instantiation in `golang/vuln` (`unknown`):** Whether `golang/vuln` issue `https://go.dev/issue/57221` (`entries.go:17–46`) can instantiate exported parameterized Go library functions over synthetic type arguments without incurring pathological SSA/VTA state explosion or false interface edges remains **unknown**.
- **Stylized Probe 3 and Probe 5 fixture percentages as ecosystem prevalence estimates (`known not to apply`):** Exact ratios on Probe 3's 10-line `requirements.txt` (`3/10` default retention), Probe 5's 18-import stdlib-heavy Python fixture (`64.71%` pure-PyPI and `41.18%` `Spracks` CSV vs. `11.76%` with `sys.stdlib_module_names`), and Probe 5's 53-package post-cutoff slopsquatting comparison (`[illustrative analytical model]`, `Basis: derived`) are deterministic mechanism witnesses and are **known not to apply** as population-wide prevalence rates (for which the empirical rates in `Zhou et al. Table 4`, `Djire et al. §5.1 Table 2`, and `Churilov 2026 §6` govern). Likewise, `Djire et al.`'s benign JavaScript `RAG` degradation (`+12.7 pp`, `7/8` models in `§5.3`) is **known not to apply** under adversarial package-injection prompts (`§5.6 Table 5`, where `RAG` wins `5/8` JavaScript models).
- **Explicit upstream analyzer and serializer feature omissions (`unsupported`):** Uninstantiated generic library entry points (`entries.go:17–46`), `reflect` / `unsafe` / `CGO` call edges (`vta.go:74–75`), and call-graph construction on compiled Go binaries (`binary.go:46–48`) are **unsupported** in `golang/vuln@ef4cb2f7`; DWARF `DW_TAG_inlined_subroutine` attribution (`rust.go:154–174`), multi-rule `.d` depfiles (`rust.go:275–280`), and non-`[\w,]+` Rust generic arguments (`rust.go:288–304`) are **unsupported** in `google/osv-scanner@925d1b4c`; editable `-e` and VCS `git+https://` requirements (`parse_requirements.go:129–148`) and non-`dependency-of` CycloneDX package relationships (`cyclonedxhelpers/to_format_model.go:235–242`) are **unsupported** in `anchore/syft@9ad9aa5e`; and root-scoped OpenVEX / CSAF VEX suppression across disconnected orphan SBOM components (`pkg/vex/vex.go:195–199`) is **unsupported** in `aquasecurity/trivy@edf9f5c1`.

## Evidence

### 1. Normative Specifications and Primary Literature (`14` Audited Works)

| Work | Exact Authors, Year, & Title | Venue / Standard, Vol., & Exact Pages | Identifier (DOI / ISBN / arXiv / Repo) | Audited Sections, Tables & Primary-Source Notes |
| :--- | :--- | :--- | :--- | :--- |
| **Ponta et al. (`ICSME '18`)** | Serena Elisa Ponta, Henrik Plate, Antonino Sabetta (`2018`): *Beyond Metadata: Code-Centric and Usage-Based Analysis of Known Vulnerabilities in Open-Source Software* | *2018 IEEE ICSME*, Madrid, Spain, **pp. 449–460** (Sept. 2018) | DOI `10.1109/ICSME.2018.00054`; `arXiv:1806.05893` | `§§I–IV`, `Figs. 6–7` (`>250,000` scans, `131/496` apps, `390` app-vuln pairs, `32` static+dynamic pairs [`8.2%` share; `7.9%` stated increase]). |
| **Ponta et al. (`EMSE '20`)** | Serena Elisa Ponta, Henrik Plate, Antonino Sabetta (`2020`): *Detection, assessment and mitigation of vulnerabilities in open source dependencies* | *Empirical Software Engineering*, Vol. 25, Issue 5, **pp. 3175–3215** (June 30, 2020) | DOI `10.1007/s10664-020-09830-x` | Eclipse Steady / `Vulas` architecture, patch AST/bytecode construct extraction, `Reachable Body Stability` (`RBS`). |
| **Mir et al. (`SANER '23`)** | Amir M. Mir, Mehdi Keshani, Sebastian Proksch (`2023`): *On the Effect of Transitivity and Granularity on Vulnerability Propagation in the Maven Ecosystem* | *2023 IEEE SANER*, **pp. 201–211** (March 2023) | DOI `10.1109/SANER56733.2023.00028`; `arXiv:2301.07972` | `§IV Approach`, `§V-B` (`Figs. 3, 6`: `0.53`), `§V-D` (`Figs. 7–8`: `55.8%` $D_m(1)$, `94%` $D_m(3)$), `Table IV` (`3M` packages, `517` CVEs). |
| **Shi et al. (`EMNLP '26`)** | Jiahao Shi, Edward Tsien, Yifeng Di, Hongjiao Zhang, Yuan Tang, Ronit Dey, Ilona Shishov, Gal Netanel, Zvi Grinberg, Vladimir Belousov, Bat-Zion Rotman, Ilan Pinto, Tianyi Zhang (`2026`): *VEX-Bench: Benchmarking LLM Agents for Assessing Exploitability of Software Supply Chain Vulnerabilities* | *Proceedings of EMNLP 2026*, Budapest, Hungary, **pp. 59409–59425** (Oct. 2026) | DOI `10.18653/2026.emnlp-main.2615`; `arXiv:2609.08040v1` | `§§3.2–4.4`, `Tables 1–3`, `Figs. 2, 4, 5` (`75` cases: `22` `affected`, `38` `code_not_reachable`, `7` `requires_configuration`, `6` `code_not_present`, `2` `requires_environment`). |
| **Zhou et al. (`CODASPY '26`)** | Li Zhou, Marc Dacier, Charalambos Konstantinou (`2026`): *A Reality Check on SBOM-based Vulnerability Management: An Empirical Study and A Path Forward* | *16th ACM CODASPY '26*, Frankfurt am Main, Germany, **pp. 255–268** (June 2026) | DOI `10.1145/3800506.3803490`; `arXiv:2511.20313v2` | `§§5.1–5.7`, `Tables 3–8` (`Table 4`: `96.4%` Rust vs. `19.1%` Python; `Table 7`: `92.0%` FP; `Table 8` & `Appendix A Table 9` p. 14: `121 -> 31` [`74.4%`] Go reduction). |
| **Zięba-Kozarzewski (`2026`)** | Artur Zięba-Kozarzewski (`2026`): *No Edges, No Verdict: A Large-Scale Empirical Study of Declared Dependency Graphs in 78K SBOMs in the Wild* | *arXiv Technical Report* (`v3`, Oct. 22, 2026, `11` pp.) | `arXiv:2607.22140v3` (`10.48550/arXiv.2607.22140`) | `§§IV–VI`, `Tables I–III` (`77,092` parseable Wild SBOMs, `61.68%` non-connected; `Syft` `89.7%` non-connected; container orphans `95%–98%`). |
| **Cofano et al. (`TrustCom '24`)** | Serena Cofano, Giacomo Benedetti, Matteo Dell'Amico (`2024`): *SBOM Generation Tools in the Python Ecosystem: an In-Detail Analysis* | *2024 IEEE 23rd TrustCom*, Sanya, China, **pp. 427–434** (Dec. 2024) | DOI `10.1109/TrustCom63139.2024.00077`; `arXiv:2409.01214v1` | `§§III–IV`, `Tables I–V`, `T1`–`T6`, `E1`–`E3` (`12` Python backend/frontend combinations). |
| **Yu et al. (`DSN '24`)** | Sheng Yu, Wei Song, Xunchao Hu, Heng Yin (`2024`): *On the Correctness of Metadata-Based SBOM Generation: A Differential Analysis Approach* | *2024 54th IEEE/IFIP DSN*, **pp. 29–36** (June 2024) | DOI `10.1109/DSN58291.2024.00018` | Abstract & `§III` (`7,876` projects across `9` languages: `535` Python, `819` Ruby, `384` PHP, `398` Java, `1,019` Swift, `700` C#/.NET, `994` Rust, `2,367` Go, `660` JS). |
| **O'Donoghue et al. (`SCORED '24`)** | Eric O'Donoghue, Brittany Boles, Clemente Izurieta, Ann Marie Reinhold (`2024`): *Impacts of Software Bill of Materials (SBOM) Generation on Vulnerability Detection* | *ACM SCORED '24* (co-located with `CCS '24`), **pp. 67–76** (Nov. 2024) | DOI `10.1145/3689944.3696164` | `2,313` Docker images across `Syft`/`Trivy` $\times$ `CycloneDX`/`SPDX` $\times$ `Trivy`/`Grype`/`CVE-bin-tool`. |
| **Spracklen et al. (`USENIX '25`)** | Joseph Spracklen, Raveen Wijewickrama, A H M Nazmus Sakib, Anindya Maiti, Bimal Viswanath, Murtuza Jadliwala (`2025`): *We Have a Package for You! A Comprehensive Analysis of Package Hallucinations by Code Generating LLMs* | *34th USENIX Security Symposium*, Seattle, WA, USA, **pp. 3687–3706** (Aug. 2025) | ISBN `978-1-939133-52-6`; `arXiv:2406.10279` | `§§5–6`, `Tables 3–5, 7–8`, `Figs. 5, 8` (`576,000` samples, `2.23M` packages, `440,445` [`19.7%`] / `205,474` unique hallucinations, `43%` `10/10`, `81%` single-model). |
| **Churilov (`2026`)** | Aleksandr Churilov (`2026`): *The Range Shrinks, the Threat Remains: Re-evaluating LLM Package Hallucinations on the 2026 Frontier-Model Cohort* | *arXiv Technical Report* (`v3`, Aug. 9, 2026) | `arXiv:2605.17062v3`; Zenodo `10.5281/zenodo.19859120` | `§§4–6`, `Tables 1–4` (`199,845` prompts, `[4.62%, 6.10%]` across 5 models, `127` universal / `74` blocked / `53` registrable [`41` PyPI, `12` npm]). |
| **Djire et al. (`ASE '26`)** | Alberick Euraste Djire, Iyiola E. Olatunji, Melissa Tessa, Earl T. Barr, Jacques Klein, Tegawendé F. Bissyandé (`2026`): *Evaluating Inference-Time Defenses against Package Hallucination in LLM-Generated Code* | *41st IEEE/ACM ASE '26*, Munich, Germany, **pp. 3290–3302** (Oct. 2026) | DOI `10.1145/3832783.3837555`; `arXiv:2608.22652v1` | `§§5.1–5.6`, `Tables 1–5`, `Figs. 2–3` (`§5.1`: `+7.6` to `+9.4 pp` stdlib bias; `§5.3 Table 4`: benign `RAG` `29.7%->18.1%` & `+12.7 pp` JS `7/8`; `§5.6 Table 5`: adversarial `DoLa` `24/32` backfire & `RAG` `16/32` overall / `5/8` JS). |
| **OSV Schema (`2026`)** | OpenSSF OSV Schema Authors (`2026`): *Open Source Vulnerability Format (`OSV Schema`)* | OpenSSF Normative Specification (`docs/schema.md`, `proto/vulnerability.proto`) | `ossf/osv-schema@e34af15e6f05eff600d1223c05f60d39b53bc131` | `docs/schema.md` (`2,032L`: `L909–1437`, esp. `L1144–1148`, `L1269–1398`), `proto/vulnerability.proto` (`234L`: `L62–145`). |
| **OpenVEX v0.2.0 (`2022–2026`)** | OpenVEX Authors & CISA VEX Working Group (`2022–2026`): *OpenVEX Specification v0.2.0* & *CSAF v2.0 VEX Profile* | OpenVEX Normative Specification (`OPENVEX-SPEC.md`) | `openvex/spec@93139bd2c65390b504e47f82f11c50451289f93a` | `OPENVEX-SPEC.md` (`671L`: `L190–236`, `L343–378`, `L417–499`). |

### 2. Pinned Upstream Repository and Source-Span Audit (`10` Repositories)

| Repository | Full 40-Character Revision SHA | Author Date (UTC) | Committer Date (UTC) | Audited Files, Exact Line Counts, & Verified Spans |
| :--- | :--- | :--- | :--- | :--- |
| `golang/vuln` | `ef4cb2f7cae47fe3e21fc596455f694951867b29` | `2026-11-17T19:45:13Z` | `2026-11-17T20:25:28Z` | `internal/vulncheck/utils.go` (`346L`: `L63–89`), `slicing.go` (`46L`: `L14–46`), `entries.go` (`56L`: `L13–56`), `source.go` (`312L`: `L50–105`), `binary.go` (`237L`: `L46–48, 107–131`), `internal/openvex/handler.go` (`261L`: `L70–128, 216–227`). |
| `golang/tools` | `70e48cd7db64b457438d8d171c8734478f84a52f` | `2026-11-12T05:14:24Z` | `2026-11-20T20:49:33Z` | `go/callgraph/vta/vta.go` (`193L`: `L57, 73–165`), `go/callgraph/vta/graph.go` (`836L`: `L312–352, 660–698`), `go/callgraph/vta/utils.go` (`188L`: `L34–66, 151–188`). |
| `google/osv-scanner` | `925d1b4cf77c4dd26540672f6fa045a3a8327754` | `2026-11-22T17:45:21Z` | `2026-11-22T17:45:21Z` | `internal/sourceanalysis/rust.go` (`304L`: `L31–33, 70–86, 154–174, 234–248, 275–280, 288–304`), `internal/sourceanalysis/go.go` (`222L`: `L104–137`), `internal/scalibrenricher/govulncheck/source/govulncheck.go` (`191L`: `L117–139`). |
| `rustsec/rustsec` | `9284e112641a1992f022711395389d9246aa9837` | `2026-11-22T18:51:51Z` | `2026-11-22T18:51:51Z` | `cargo-audit/src/auditor.rs` (`463L`: `L159–202`), `rustsec/src/binary_scanning/binary_deps.rs` (`183L`: `L24–55`). |
| `ossf/osv-schema` | `e34af15e6f05eff600d1223c05f60d39b53bc131` | `2026-11-23T02:22:57Z` | `2026-11-23T02:22:57Z` | `docs/schema.md` (`2,032L`: `L909–1437`, esp. `L1076–1088, 1144–1148, 1269–1398`), `proto/vulnerability.proto` (`234L`: `L62–145`). |
| `anchore/syft` | `9ad9aa5e80a6762c33b0344d252ec669ae53afdc` | `2026-11-23T01:26:41Z` | `2026-11-23T01:26:41Z` | `syft/pkg/cataloger/python/cataloger.go` (`44L`: `L18–35`), `parse_requirements.go` (`321L`: `L29, 67–87, 129–250`), `parse_setup.go` (`137L`: `L40–115`), `syft/format/common/cyclonedxhelpers/to_format_model.go` (`367L`: `L235–293`), `syft/format/common/spdxhelpers/to_format_model.go` (`1,049L`: `L58–69, 170–218, 698–748`). |
| `aquasecurity/trivy` | `edf9f5c13d27ba1f6b1bc747f2f41a383dc56dc9` | `2026-11-20T11:14:25Z` | `2026-11-20T11:14:25Z` | `pkg/dependency/parser/python/pip/parse.go` (`170L`: `L39–116, 167–170`), `pyproject/pyproject.go` (`109L`: `L45–60`), `pkg/vex/vex.go` (`219L`: `L178–219`), `openvex.go` (`100L`: `L60–87`), `csaf.go` (`184L`: `L36–115`), `cyclonedx.go` (`88L`: `L25–74`). |
| `openvex/go-vex` | `42a83ee2b1ae9e8b1cde8f5161dc869fc76fdefa` | `2026-11-19T02:07:24Z` | `2026-11-19T02:07:24Z` | `pkg/vex/vex.go` (`521L`: `L173–209, 227–244`), `statement.go` (`279L`: `L69–137, 142–196`), `product.go` (`109L`: `L29–47`), `component.go` (`72L`: `L25–58`), `vulnerability.go` (`66L`: `L32–47`). |
| `openvex/spec` | `93139bd2c65390b504e47f82f11c50451289f93a` | `2026-10-30T19:59:30Z` | `2026-10-30T19:59:30Z` | `OPENVEX-SPEC.md` (`671L`: `L190–236, 343–378, 417–499`). |
| `Spracks/PackageHallucination` | `bd3031cce6a0007997a0604d3ad3365031ed79b2` | `2026-08-14T02:17:03Z` | `2026-08-14T02:17:03Z` | `package_detection.py` (`275L`: `L9–17, 36–49, 63–93`), `custom_parse_python.py` (`89L`: `L4–7`), `custom_parse_javascript.py` (`480L`: `L5–52, 111–136, 163–188, 198–201`), `Data/Python/pypi_package_names.csv` (`500,565L`: `L500315–500565`, incl. `L500328`, `L500406`, `L500429`), `Data/Python/false_positive_packages.csv` (`3,884L`). |

### 3. Preserved Executable Probe Artifact and Cryptographic Receipts

- **Package-Relative Path:** `reports/agent-dependency-reachability-vex-discrepancies-and-slopsquatting/scripts/verify_vuln_reachability_sbom_slopsquatting.py`
- **Script Size & SHA-256:** `71,887` bytes (`1,769` lines, Python 3.10+ standard library only), SHA-256 `6e221ba7e5ec2a6c477a37727a63cb6cdf98fb0733ac9dab395b762c76f4a67e`
- **Deterministic Stdout Size & SHA-256 (`PYTHONHASHSEED=1` & `PYTHONHASHSEED=2`):** `4,243` bytes (`148` lines, valid JSON, `0` stderr bytes, zero external network I/O, isolated `with tempfile.TemporaryDirectory():` cleanup), SHA-256 `7c3601f6385e922c3dcb1cf4d602f7e8eac05f6e5d120fabd4ac2a73aa677b88`
- **Observed Runtime (`CPython 3.13`, `python3 -I -B`):** `0.0719s` (`PYTHONHASHSEED=1`) / `0.0700s` (`PYTHONHASHSEED=2`)

## Revalidation

1. **Deterministic Local Probe Re-Execution (`< 0.2s`, zero network or third-party packages):**
   Run from the corpus repository root under isolated Python flags and distinct hash seeds:

   ```bash
   PYTHONHASHSEED=1 python3 -I -B reports/agent-dependency-reachability-vex-discrepancies-and-slopsquatting/scripts/verify_vuln_reachability_sbom_slopsquatting.py | sha256sum
   PYTHONHASHSEED=2 python3 -I -B reports/agent-dependency-reachability-vex-discrepancies-and-slopsquatting/scripts/verify_vuln_reachability_sbom_slopsquatting.py | sha256sum
   ```

   Both invocations must exit `0` and emit `7c3601f6385e922c3dcb1cf4d602f7e8eac05f6e5d120fabd4ac2a73aa677b88` (`4,243` bytes):

   ```json
   {
     "probe_1_govulncheck_vta_and_openvex": {
       "cha_flagged": [
         "GO-TAR",
         "GO-XML",
         "GO-YAML"
       ],
       "vta_pass1_flagged": [
         "GO-TAR",
         "GO-YAML"
       ],
       "vta_pass2_flagged": [
         "GO-TAR"
       ],
       "vta_unpassed_closure_pruned_pass1": true,
       "ground_truth_main": [
         "GO-REFL",
         "GO-TAR"
       ],
       "vta_missed_reflection": [
         "GO-REFL"
       ],
       "generic_lib_entries_count": 0,
       "generic_lib_flagged": [],
       "binary_unstripped_flagged": [
         "GO-REFL",
         "GO-TAR",
         "GO-XML",
         "GO-YAML"
       ],
       "binary_stripped_flagged": [
         "GO-MODONLY",
         "GO-REFL",
         "GO-TAR",
         "GO-TOML",
         "GO-XML",
         "GO-YAML"
       ],
       "antisymmetry_violations": [
         "(required,imported):-1_vs_-1",
         "(imported,required):-1_vs_-1"
       ],
       "openvex_req_then_imp": "vulnerable_code_not_in_execute_path",
       "openvex_imp_then_req_buggy": "vulnerable_code_not_present",
       "openvex_imp_then_req_fixed": "vulnerable_code_not_in_execute_path",
       "scalibr_unimported_mod_signal": "vulnerable_code_not_in_execute_path"
     },
     "probe_2_osv_scanner_rust_dwarf_and_osv_ranges": {
       "rust_regex_upstream_recall": "2/6",
       "rust_regex_balanced_recall": "6/6",
       "rust_regex_failed_count": 4,
       "dwarf_inlined_detected": false,
       "dwarf_dead_export_flagged": true,
       "cargo_depfile_multi_rule_err": true,
       "osv_git_fixed_affected": [
         "X",
         "A",
         "B",
         "C",
         "D",
         "E",
         "F"
       ],
       "osv_git_limit_affected": [
         "X",
         "A",
         "B",
         "C"
       ],
       "osv_git_limit_false_negatives": [
         "D",
         "E",
         "F"
       ],
       "osv_semver_prerelease_before_fix": true,
       "osv_semver_last_affected_ceiling_fn": true,
       "go_v1_false_imports_inheritance": true
     },
     "probe_3_syft_trivy_python_sbom_and_edges": {
       "total_declared_reqs": 10,
       "syft_default_count": 3,
       "trivy_default_count": 3,
       "default_omitted_count": 7,
       "syft_guess_werkzeug": "2.2.2",
       "trivy_min_werkzeug": "2.0.0",
       "syft_guess_pyjwt_splitafter_bug": null,
       "trivy_default_pyjwt": "2.8.0",
       "syft_default_certifi_triple_eq": "2024.2.2",
       "trivy_default_certifi_triple_eq": null,
       "trivy_pep621_extras_leaked": [
         "mypy",
         "pytest",
         "sphinx"
       ],
       "trivy_poetry_deps_retained_when_optional_set": [],
       "syft_cdx_relationships_kept": "1/4",
       "syft_spdx_relationships_kept": "4/4"
     },
     "probe_4_vex_alias_revocation_and_orphan_impossibility": {
       "govex_effective_stmt_status": "affected",
       "trivy_openvex_falsely_suppresses_revoked_cve": true,
       "prefixes_sorting_after_cve": "6/6",
       "connected_openvex_suppressed": "100/100",
       "degen_97pct_orphan_openvex_suppressed": "3/100",
       "degen_97pct_orphan_csaf_suppressed": "3/100",
       "degen_97pct_orphan_cdx_root_suppressed": "3/100",
       "degen_97pct_orphan_cdx_leaf_suppressed": "100/100",
       "wild_sbom_parseable_total": 77092,
       "wild_sbom_non_connected_pct": 61.68,
       "closed_world_kev_retained_on_degen": "3/100",
       "open_world_three_valued_kev_retained": "100/100"
     },
     "probe_5_package_hallucination_parser_and_slopsquatting": {
       "parser_caller_list_mutated": true,
       "parser_leaked_local_and_cli_as_hallucinations": [
         "--legacy-peer-flag",
         "./config"
       ],
       "parser_erased_valid_2char_packages": [
         "ws",
         "pg"
       ],
       "phr_pure_pypi_without_stdlib_pct": 64.71,
       "phr_spracks_appended_csv_pct": 41.18,
       "phr_with_stdlib_pct": 11.76,
       "pure_pypi_stdlib_inflation_pp_on_fixture": 52.95,
       "pypi_backports_not_flagged": [
         "dataclasses",
         "pathlib"
       ],
       "spracks_false_positive_stdlib_modules": [
         "atexit",
         "concurrent",
         "mmap",
         "stringprep",
         "xml"
       ],
       "spracks_missing_public_stdlib_gt2_count": 22,
       "model_label": "[illustrative analytical model] (Basis: derived)",
       "churilov_universal_5model_total": 127,
       "churilov_registry_blocked": 74,
       "churilov_universal_registrable": 53,
       "compromised_unguarded": "53/53",
       "compromised_5of5_consensus": "53/53",
       "compromised_snapshot_lockfile_gate": "0/53",
       "spracklen_10of10_attractor_share": 0.43
     }
   }
   ```

2. **Targeted Upstream Diffs When Updating Subject Revisions:**
   - **`golang/vuln` & `golang/tools`:** Diff `internal/vulncheck/{utils,slicing,entries,binary}.go` (`entryPoints` generic `TypeParams` handling and `binary` stripped-symtab fallback), `internal/openvex/handler.go` (`moreSpecific` `L102–107`), and `go/callgraph/vta/{vta,graph}.go` (`typePropGraph` and `addArgumentFlows`).
   - **`google/osv-scanner` & `rustsec/rustsec`:** Diff `internal/sourceanalysis/rust.go` (`cargo build` invocation, `antiGenericRegex`, `functionsFromDWARF` `DW_TAG_inlined_subroutine`, and `.d` depfile split), `internal/sourceanalysis/go.go` (`vulnHasImportsField` version filtering), and `internal/scalibrenricher/govulncheck/source/govulncheck.go` (`L125–138`).
   - **`anchore/syft` & `aquasecurity/trivy`:** Diff `syft/pkg/cataloger/python/parse_requirements.go` (`parsePinnedVersion`, `guessVersion` `strings.SplitAfter`), `cyclonedxhelpers/to_format_model.go` (`isExpressiblePackageRelationship`), `spdxhelpers/to_format_model.go` (`toRelationships`, `lookupRelationship`), and `trivy/pkg/dependency/parser/python/{pip/parse.go,pyproject/pyproject.go}`.
   - **`openvex/go-vex` & `aquasecurity/trivy` VEX:** Diff `go-vex/pkg/vex/{statement,vex}.go` (`SortStatements` primary key and `Document.Matches`) and `trivy/pkg/vex/{openvex,vex,csaf,cyclonedx}.go` (`stmts[len(stmts)-1]` and `reachRoot` `unvisited` orphan return).
   - **`Spracks/PackageHallucination`:** Diff `custom_parse_javascript.py` (`refine_package_list` `new_list = lst` and in-place `remove`), `custom_parse_python.py` (`len(i) > 2`), `package_detection.py` (`normalize_python` and `package_search_python`), and `Data/Python/pypi_package_names.csv` tail (`L500315–500565`).
