# Independent source review: termination-only Stateen patch

**PASS for the parent's proposed fresh-copy regeneration and full-closure compilation gate.** The patch is sufficient at the source-ranking level for the actual rejected mutual block and preserves the ISA equations/effect order. This is not a checked Lean termination proof or a claim that downstream modules/theorems pass. No generator/compiler/proof/runtime command ran in this review; only source reads and a finite text/rank audit ran. No files outside this scratch review were changed.

Reviewed patch: `work/execution/jasmin-execution-plan/proposed.patch`. Original sources: frozen official riscv/sail-riscv7d3c9c2568b77f516783aa2ac63bd9c0e0c6df86 `model/extensions/Stateen/stateen_regs.sail`, `model/core/extensions.sail`; original generated `work/execution/sail-runtime/generated-project/LeanRV64D/PlatformConfig.lean:5587–5662,5946–6258`. Existing independent author's diagnosis was read, but the counts and inequalities below were recomputed from original generated definitions, not accepted from its adjacency list.

## Scope and equation/effect preservation

The patch adds exactly three absent termination_measure annotations (legalize_mstateen0=5, read_mstateen0=6, get_mstateen=7), increases check_stateen_bit7→8 and is_zfinx_enabled_by_stateen8→9, and changes four cases of the dedicated currentlyEnabled_measure helper (Zfinx9→10, Zdinx10→11, Zhinx10→11, Zhinxmin11→12). The Zdinx explanatory comment is corrected. Every other ranking value and default2 remains unchanged.

No architectural function body, condition, register lookup/write, exception, callback, import, configuration, or call ordering is edited. In particular, `stateen_regs.sail:56–83` still legalizes stale mstateen0 on reads. Its FCSR condition calls **hartSupports(Ext_Zfinx)**, not currentlyEnabled(Ext_Zfinx); replacing it by the latter would introduce a cycle and is not part of this patch. Generated `read_mstateen0` performs two reads of mstateen0 before calling legalization; preserve both reads and their order even though they look redundant under a sequential state interpreter. Generated legalize_mstateen0 preserves its actual currentlyEnabled calls for S,Sdtrig,H,Ssqosid and its misa read.

Qualification: currentlyEnabled_measure is an ordinary auxiliary function whose four return values do change. Therefore do not claim every generated definition has unchanged outputs. Source search over model/*.sail found it used only in its definition and currentlyEnabled's termination annotation, plus comments. Its auxiliary numeric change has no identified architectural observation. Well-founded recursion proof/compilation strategy and definitional unfolding may change even when the user-facing recursive equations do not. Extensional bridging can be stated separately if later claims need more than restricted-source-diff preservation.

## Complete mutual-call audit

I split the original actual mutual block into all11 definitions, then currentlyEnabled into all139 constructor branches, and enumerated each direct occurrence of a mutual member. All currentlyEnabled call arguments in this block are literal extension constructors; there were zero unmatched variable-argument calls. Collapsing repeated syntactic sites yields **134 directed edges from94 nonleaf nodes**. I obtained **zero nondecreasing edges** under the proposed ranks. All values are nonnegative, so the backend's `.toNat` conversions preserve strict decrease. This reproduces, independently, the author's134-edge result.

Critical newly extended path:

```
Zhinxmin12 > Zhinx11 > Zfinx10 > is_zfinx_enabled_by_stateen9
  > check_stateen_bit8 > get_mstateen7 > read_mstateen0(6)
  > legalize_mstateen0(5) > H4 > Sv39(2) > S1 > Zicsr0
```

Zdinx11→Zfinx10 and Zhinxmin12→Zfinx10 also strictly decrease. Unchanged branch chains are covered, including Sha6→Sh*5→H4, V5→Zve64d4→Zve64f3, Zvfhmin5→Zvfh4, and Zicfilp3→get_xLPE2→S1. Stateen's other branch accesses stay below check8: get_hstateen6→is_hstateen_accessible5→H4; get_sstateen3→is_sstateen_accessible2→S/Smstateen/Ssstateen1. No modified rank is a callee of an unchanged lower-rank node in this block. With all other ranks fixed, the new chain's consecutive integer assignment is minimal.

The finite lexical audit is not a Lean proof. It uses the real generated SCC plus all named mutual calls, and the fixed-constructor property makes rank evaluation exact rather than symbolic. Backend regeneration must still emit all three new hints and the new integer helper cases; Lean must prove its ordinary obligations without partial/unsafe/admission/axiom escape.

## Gate and downstream risks

Approve only the proposed effects: patch a fresh exact source copy, regenerate the **whole** same configured model with same flags, inspect complete generated diff (allowing source location shifts), and compile the full143-module closure in fresh output dirs under the existing bounds. Preserve original source, original generation, compiler failure and unchanged controls/draft. Identify the repaired subject as official model revision plus exact patch hash; do not report an unmodified upstream replay.

Expected generated diff is the three added termination_by hints, two adjusted scalar hints, four currentlyEnabled_measure values and source-location metadata. A changed mutual member set, changed architecture equations, deleted callbacks/reads, partial recursion, or extra native/import assumptions requires stopping for review. Neither source ranking nor the first69 successful modules predicts success of all later modules. Other upstream recursion-measure omissions, proof-generation elaboration/resource limits, or the owned draft's untested definitional/simp steps remain plausible downstream failures. Those are hypotheses, not observed defects. If the extended hints are present but termination still fails, preserve the exact obligation before proposing a narrowly scoped decreasing proof. Do not change runtime semantics to make it pass.

The ADD draft's actual selected branch uses rX/wX and the pure fixed-index name callback; it does not call currentlyEnabled. A successful repaired closure still needs the actual ADD theorem and individual axiom audit. No theorem success follows from this review.

## Independently recomputed edge inequalities

Each row lists caller→callee and proposed ranks. Repeated call sites are collapsed; currentlyEnabled branches use their extension names, unlisted leaf branches contribute no edges.

```text
Ext_D -> Ext_F: 2 > 1
Ext_F -> Ext_Zicsr: 1 > 0
Ext_H -> Ext_S: 4 > 1
Ext_H -> Ext_Sv32: 4 > 2
Ext_H -> Ext_Sv39: 4 > 2
Ext_S -> Ext_Zicsr: 1 > 0
Ext_Sha -> Ext_H: 6 > 4
Ext_Sha -> Ext_Shcounterenw: 6 > 5
Ext_Sha -> Ext_Shgatpa: 6 > 5
Ext_Sha -> Ext_Shtvala: 6 > 5
Ext_Sha -> Ext_Shvsatpa: 6 > 5
Ext_Sha -> Ext_Shvstvala: 6 > 5
Ext_Sha -> Ext_Shvstvecd: 6 > 5
Ext_Sha -> Ext_Ssstateen: 6 > 1
Ext_Shcounterenw -> Ext_H: 5 > 4
Ext_Shgatpa -> Ext_H: 5 > 4
Ext_Shtvala -> Ext_H: 5 > 4
Ext_Shvsatpa -> Ext_H: 5 > 4
Ext_Shvstvala -> Ext_H: 5 > 4
Ext_Shvstvecd -> Ext_H: 5 > 4
Ext_Smcntrpmf -> Ext_Zicntr: 2 > 1
Ext_Smstateen -> Ext_Zicsr: 1 > 0
Ext_Ssccptr -> Ext_Sv32: 3 > 2
Ext_Ssccptr -> Ext_Sv39: 3 > 2
Ext_Sscofpmf -> Ext_Zihpm: 2 > 1
Ext_Sscounterenw -> Ext_S: 2 > 1
Ext_Ssdbltrp -> Ext_S: 2 > 1
Ext_Ssnpm -> Ext_S: 2 > 1
Ext_Sspm -> Ext_S: 2 > 1
Ext_Ssqosid -> Ext_Zicsr: 2 > 0
Ext_Ssstateen -> Ext_Zicsr: 1 > 0
Ext_Ssstrict -> Ext_S: 2 > 1
Ext_Sstvala -> Ext_S: 2 > 1
Ext_Sstvecd -> Ext_S: 2 > 1
Ext_Ssu64xl -> Ext_S: 2 > 1
Ext_Supm -> Ext_U: 3 > 2
Ext_Sv32 -> Ext_S: 2 > 1
Ext_Sv39 -> Ext_S: 2 > 1
Ext_Sv48 -> Ext_S: 2 > 1
Ext_Sv57 -> Ext_S: 2 > 1
Ext_Svbare -> Ext_S: 2 > 1
Ext_Svnapot -> Ext_Sv39: 3 > 2
Ext_Svpbmt -> Ext_Sv39: 3 > 2
Ext_Svrsw60t59b -> Ext_Sv39: 3 > 2
Ext_Svukte -> Ext_Sv39: 3 > 2
Ext_Svvptc -> Ext_Sv32: 3 > 2
Ext_Svvptc -> Ext_Sv39: 3 > 2
Ext_U -> Ext_Zicsr: 2 > 0
Ext_V -> Ext_Zve64d: 5 > 4
Ext_V -> Ext_Zvl128b: 5 > 0
Ext_Za128rs -> Ext_Zalrsc: 2 > 1
Ext_Za64rs -> Ext_Zalrsc: 2 > 1
Ext_Zaamo -> Ext_A: 1 > 0
Ext_Zabha -> Ext_Zaamo: 2 > 1
Ext_Zacas -> Ext_Zaamo: 2 > 1
Ext_Zalrsc -> Ext_A: 1 > 0
Ext_Zba -> Ext_B: 2 > 0
Ext_Zbb -> Ext_B: 2 > 0
Ext_Zbs -> Ext_B: 2 > 0
Ext_Zca -> Ext_C: 1 > 0
Ext_Zcb -> Ext_Zca: 2 > 1
Ext_Zcd -> Ext_C: 3 > 0
Ext_Zcd -> Ext_D: 3 > 2
Ext_Zcd -> Ext_Zca: 3 > 1
Ext_Zcf -> Ext_C: 2 > 0
Ext_Zcf -> Ext_F: 2 > 1
Ext_Zcf -> Ext_Zca: 2 > 1
Ext_Zcmop -> Ext_Zca: 2 > 1
Ext_Zdinx -> Ext_Zfinx: 11 > 10
Ext_Zfa -> Ext_F: 2 > 1
Ext_Zfbfmin -> Ext_F: 2 > 1
Ext_Zfh -> Ext_F: 2 > 1
Ext_Zfhmin -> Ext_F: 3 > 1
Ext_Zfhmin -> Ext_Zfh: 3 > 2
Ext_Zfinx -> Ext_Zicsr: 10 > 0
Ext_Zfinx -> is_zfinx_enabled_by_stateen: 10 > 9
Ext_Zhinx -> Ext_Zfinx: 11 > 10
Ext_Zhinxmin -> Ext_Zfinx: 12 > 10
Ext_Zhinxmin -> Ext_Zhinx: 12 > 11
Ext_Zicfilp -> Ext_Zicsr: 3 > 0
Ext_Zicfilp -> get_xLPE: 3 > 2
Ext_Zicfiss -> Ext_Zaamo: 2 > 1
Ext_Zicfiss -> Ext_Zicsr: 2 > 0
Ext_Zicfiss -> Ext_Zimop: 2 > 0
Ext_Zicntr -> Ext_Zicsr: 1 > 0
Ext_Zihpm -> Ext_Zicsr: 1 > 0
Ext_Zmmul -> Ext_M: 2 > 0
Ext_Zvabd -> Ext_Zve32x: 2 > 1
Ext_Zvbb -> Ext_Zve32x: 2 > 1
Ext_Zvbc -> Ext_Zve64x: 3 > 2
Ext_Zve32f -> Ext_F: 2 > 1
Ext_Zve32f -> Ext_Zve32x: 2 > 1
Ext_Zve32x -> Ext_Zicsr: 1 > 0
Ext_Zve32x -> Ext_Zvl32b: 1 > 0
Ext_Zve64d -> Ext_D: 4 > 2
Ext_Zve64d -> Ext_Zve64f: 4 > 3
Ext_Zve64f -> Ext_Zve32f: 3 > 2
Ext_Zve64f -> Ext_Zve64x: 3 > 2
Ext_Zve64x -> Ext_Zve32x: 2 > 1
Ext_Zve64x -> Ext_Zvl64b: 2 > 0
Ext_Zvfbfmin -> Ext_Zve32f: 3 > 2
Ext_Zvfbfwma -> Ext_Zfbfmin: 4 > 2
Ext_Zvfbfwma -> Ext_Zvfbfmin: 4 > 3
Ext_Zvfh -> Ext_Zfhmin: 4 > 3
Ext_Zvfh -> Ext_Zve32f: 4 > 2
Ext_Zvfhmin -> Ext_Zve32f: 5 > 2
Ext_Zvfhmin -> Ext_Zvfh: 5 > 4
Ext_Zvkb -> Ext_Zvbb: 3 > 2
Ext_Zvkb -> Ext_Zve32x: 3 > 1
Ext_Zvkg -> Ext_Zve32x: 2 > 1
Ext_Zvkned -> Ext_Zve32x: 2 > 1
Ext_Zvknha -> Ext_Zve32x: 2 > 1
Ext_Zvknhb -> Ext_Zve64x: 3 > 2
Ext_Zvksed -> Ext_Zve32x: 2 > 1
Ext_Zvksh -> Ext_Zve32x: 2 > 1
check_stateen_bit -> get_hstateen: 8 > 6
check_stateen_bit -> get_mstateen: 8 > 7
check_stateen_bit -> get_sstateen: 8 > 3
get_hstateen -> is_hstateen_accessible: 6 > 5
get_mstateen -> read_mstateen0: 7 > 6
get_sstateen -> is_sstateen_accessible: 3 > 2
get_xLPE -> Ext_S: 2 > 1
is_hstateen_accessible -> Ext_H: 5 > 4
is_hstateen_accessible -> Ext_Smstateen: 5 > 1
is_hstateen_accessible -> Ext_Ssstateen: 5 > 1
is_sstateen_accessible -> Ext_S: 2 > 1
is_sstateen_accessible -> Ext_Smstateen: 2 > 1
is_sstateen_accessible -> Ext_Ssstateen: 2 > 1
is_zfinx_enabled_by_stateen -> check_stateen_bit: 9 > 8
legalize_mstateen0 -> Ext_H: 5 > 4
legalize_mstateen0 -> Ext_S: 5 > 1
legalize_mstateen0 -> Ext_Sdtrig: 5 > 2
legalize_mstateen0 -> Ext_Ssqosid: 5 > 2
read_mstateen0 -> legalize_mstateen0: 6 > 5
```

Reviewed-byte SHA256 identities:

- `work/execution/sail-runtime/generated-project/LeanRV64D/PlatformConfig.lean`: `65e1d923d59611cadad25d39d6629f77969daaf609a1ce1a59739f7da7ee517e`.
- `work/execution/jasmin-execution-plan/proposed.patch`: `6cf5860e7d493bc224060c4508541a81db91d6e40b5d6421ee2ced2dff126236`.
- `work/execution/cross-foundation-runtime/sail-sources/sail-riscv/model/extensions/Stateen/stateen_regs.sail`: `c430ab2e36986589d92e72a2fde4e30671fbac277bef2be3bb6f5828f95dd1bb`.
- `work/execution/cross-foundation-runtime/sail-sources/sail-riscv/model/core/extensions.sail`: `723ce4349033bdecbf8c33932aff35b8b6f28e2b62572e64845ecfa528c5b906`.
