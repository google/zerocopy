# Stateen termination-measure mismatch

Source-only causal review, 2026-10-15. No source outside this scratch directory
was modified; no model generation, Lean compilation, runtime operation or retry
was performed. `proposed.patch` is an unapplied Sail-source proposal, requiring
the parent's independent review and a separately identified patched subject.

The frozen failure is an ordinary total-definition termination rejection in
`PlatformConfig.lean:5946–6258`, after 69 successful modules. Lean first reports
an incomplete set of termination hints because `get_mstateen`, `read_mstateen0`
and `legalize_mstateen0` are in the mutual block without measures; it therefore
ignores the present hints and cannot synthesize a decreasing measure. Adding
only those missing hints would expose a second mismatch: the former
`check_stateen_bit = 7` must now dominate a `get_mstateen` chain of rank 7.
No assertion, panic, OOM or timeout explains this error.

`stateen_regs.sail:56–83` makes reads of mstateen0 pass through legalization,
with the explicit reason that misa may change after the last write. Legalization
calls `currentlyEnabled` for S, Sdtrig, H and Ssqosid, whose current measures are
1, 2, 4 and 2. Its FCSR clause uses `hartSupports(Ext_Zfinx)`, NOT
`currentlyEnabled(Ext_Zfinx)`: there is no genuine Zfinx recursion cycle at that
point. Preserve this distinction and every operational equation. The mismatch
is an incomplete/outdated scalar ranking of a semantically terminating path,
not evidence that architectural reads should skip legalization.

The official model/CMakeLists.txt:419–490 recipe contains the same ordinary
Lean/default noncomputable generation flags and no partial-recursion escape.
The failure is consistent with missing upstream termination maintenance, not
an omitted CMake workaround. This conclusion is specific to the frozen source,
generated output and actual failed compiler invocation.

## Sufficient proposed ranks

| Node | Old | Proposed | Largest immediate intra-block callee rank |
|---|---:|---:|---:|
| legalize_mstateen0 | missing | 5 | H = 4 |
| read_mstateen0 | missing | 6 | legalize_mstateen0 = 5 |
| get_mstateen | missing | 7 | read_mstateen0 = 6 |
| check_stateen_bit | 7 | 8 | get_mstateen = 7 |
| is_zfinx_enabled_by_stateen | 8 | 9 | check_stateen_bit = 8 |
| currentlyEnabled Zfinx | 9 | 10 | is_zfinx_enabled_by_stateen = 9 |
| currentlyEnabled Zdinx | 10 | 11 | Zfinx = 10 |
| currentlyEnabled Zhinx | 10 | 11 | Zfinx = 10 |
| currentlyEnabled Zhinxmin | 11 | 12 | Zhinx = 11 |

Keep all other measures unchanged: get_hstateen=6,
is_hstateen_accessible=5, get_sstateen=3, is_sstateen_accessible=2,
get_xLPE=2, and the rest of currentlyEnabled_measure's extension ranks/default.
Every value is nonnegative, so generated `Int.toNat` preserves these strict
inequalities. Keeping H=4 forces legalize>=5, read>=6, get_m>=7, check>=8,
is_zfinx>=9, Zfinx>=10, its direct dependents>=11, Zhinxmin>=12; this assignment
is minimal along the new chain with the unchanged ranks fixed.

The patch adds three `termination_measure` declarations and changes the two
existing Stateen scalar hints plus four cases in the auxiliary measure function.
It also corrects the misleading existing Zdinx comment from `> Zdinx` to
`> Zfinx`. No ISA function clause, branch, state read/write, import, recursive
call, config setting or exception equation changes. A repository-wide Sail-text
search finds currentlyEnabled_measure used only as its own definition and the
termination annotation, apart from comments. The auxiliary rank function's
values change; the architectural currentlyEnabled equations do not.

## Complete-block audit and limits

I independently split the exact generated mutual block into its 11 definitions,
split all 139 currentlyEnabled match branches, and enumerated every direct call
to another mutual member. All currentlyEnabled arguments in that block are
fixed extension constructors. There are 134 distinct directed edges after
collapsing repeated call sites, with 94 nonleaf nodes (extension-specific
currentlyEnabled cases are separate nodes). For every edge, the proposed caller
rank is strictly greater than the callee rank: zero violating edges. This checks
the full block, including the unchanged vector/crypto/hypervisor/CFI branches,
not only the functions named in Lean's first error. The complete adjacency list
below makes that finite source audit reviewable. Ordinary reads, bitfield
helpers, hartSupports and other calls outside the mutual block do not need an
intra-block rank; no such helper can return to this SCC without being part of
the generated mutual dependency group. Full regeneration must confirm that
group and its operational equations remain unchanged.

This is a source-derived sufficient ranking, not an executed termination proof.
Generated Lean must still check all decreasing obligations at the exact pinned
compiler, and the backend must successfully emit the new annotations. Existing
generated measures use the same scalar/Int.toNat format. If Lean cannot unfold
the auxiliary measure automatically, diagnose its exact remaining obligation
before proposing a termination-proof-only `decreasing_by` lemma; do not add
`partial`, `unsafe`, `axiom`, `sorry`, `admit` or a replacement model.

After approval, apply only to a new source copy, regenerate the entire original
model using the same configuration/flags, retain original and patched hashes,
and review that differences are limited to the proposed measure definitions and
termination hints (allowing source-location metadata shifts). Compile the full
143-module target closure under the same bounded serial adapter in a new output
directory. Stop at the first new invariant/ordinary error and preserve it; no
automatic retry. Successful elaboration would establish termination acceptance
of the patched model, not a checked ISA theorem or unchanged reduction strategy.
Equation preservation follows from the restricted source diff and requires
independent generated-output review; stronger extensional/equational bridging
can be proved separately if later claims depend on proof-term identity.

Input SHA256 identities:

- Generated PlatformConfig.lean: `65e1d923d59611cadad25d39d6629f77969daaf609a1ce1a59739f7da7ee517e`.
- model/extensions/Stateen/stateen_regs.sail: `c430ab2e36986589d92e72a2fde4e30671fbac277bef2be3bb6f5828f95dd1bb`.
- model/core/extensions.sail: `723ce4349033bdecbf8c33932aff35b8b6f28e2b62572e64845ecfa528c5b906`.
- model/CMakeLists.txt: `abbb565cf6ba2f54b524ba155bc4e5ca11b223c39329ef48eb98e83060a4242b`.

## Complete adjacency, with equal callee sets grouped

`Ext_X` denotes the currentlyEnabled case for X; function names denote their
own scalar measure. A grouped left side has the listed outgoing edges for each
member. Leaf cases have no intra-block calls.

```text
Ext_D, Ext_Zfh, Ext_Zfa, Ext_Zfbfmin -> Ext_F
Ext_H -> Ext_S, Ext_Sv32, Ext_Sv39
Ext_Sha -> Ext_H, Ext_Shcounterenw, Ext_Shgatpa, Ext_Shtvala, Ext_Shvsatpa, Ext_Shvstvala, Ext_Shvstvecd, Ext_Ssstateen
Ext_Shcounterenw, Ext_Shgatpa, Ext_Shtvala, Ext_Shvsatpa, Ext_Shvstvala, Ext_Shvstvecd -> Ext_H
Ext_Smcntrpmf -> Ext_Zicntr
Ext_Sscofpmf -> Ext_Zihpm
Ext_Ssnpm, Ext_Ssstrict, Ext_Sstvala, Ext_Sstvecd, Ext_Sspm, Ext_Ssu64xl, Ext_Svbare, Ext_Sv32, Ext_Sv39, Ext_Sv48, Ext_Sv57, Ext_Ssdbltrp, Ext_Sscounterenw, get_xLPE -> Ext_S
Ext_Supm -> Ext_U
Ext_Svnapot, Ext_Svpbmt, Ext_Svrsw60t59b, Ext_Svukte -> Ext_Sv39
Ext_Svvptc, Ext_Ssccptr -> Ext_Sv32, Ext_Sv39
Ext_U, Ext_S, Ext_Smstateen, Ext_Ssstateen, Ext_F, Ext_Zihpm, Ext_Zicntr, Ext_Ssqosid -> Ext_Zicsr
Ext_V -> Ext_Zve64d, Ext_Zvl128b
Ext_Za64rs, Ext_Za128rs -> Ext_Zalrsc
Ext_Zaamo, Ext_Zalrsc -> Ext_A
Ext_Zabha, Ext_Zacas -> Ext_Zaamo
Ext_Zba, Ext_Zbb, Ext_Zbs -> Ext_B
Ext_Zca -> Ext_C
Ext_Zcb, Ext_Zcmop -> Ext_Zca
Ext_Zcd -> Ext_C, Ext_D, Ext_Zca
Ext_Zcf -> Ext_C, Ext_F, Ext_Zca
Ext_Zdinx, Ext_Zhinx -> Ext_Zfinx
Ext_Zfhmin -> Ext_F, Ext_Zfh
Ext_Zfinx -> Ext_Zicsr, is_zfinx_enabled_by_stateen
Ext_Zhinxmin -> Ext_Zfinx, Ext_Zhinx
Ext_Zicfilp -> Ext_Zicsr, get_xLPE
Ext_Zicfiss -> Ext_Zaamo, Ext_Zicsr, Ext_Zimop
Ext_Zmmul -> Ext_M
Ext_Zvbb, Ext_Zvkg, Ext_Zvkned, Ext_Zvksed, Ext_Zvknha, Ext_Zvksh, Ext_Zvabd -> Ext_Zve32x
Ext_Zvbc, Ext_Zvknhb -> Ext_Zve64x
Ext_Zve32f -> Ext_F, Ext_Zve32x
Ext_Zve32x -> Ext_Zicsr, Ext_Zvl32b
Ext_Zve64d -> Ext_D, Ext_Zve64f
Ext_Zve64f -> Ext_Zve32f, Ext_Zve64x
Ext_Zve64x -> Ext_Zve32x, Ext_Zvl64b
Ext_Zvfbfmin -> Ext_Zve32f
Ext_Zvfbfwma -> Ext_Zfbfmin, Ext_Zvfbfmin
Ext_Zvfh -> Ext_Zfhmin, Ext_Zve32f
Ext_Zvfhmin -> Ext_Zve32f, Ext_Zvfh
Ext_Zvkb -> Ext_Zvbb, Ext_Zve32x
check_stateen_bit -> get_hstateen, get_mstateen, get_sstateen
get_hstateen -> is_hstateen_accessible
get_mstateen -> read_mstateen0
get_sstateen -> is_sstateen_accessible
is_hstateen_accessible -> Ext_H, Ext_Smstateen, Ext_Ssstateen
is_sstateen_accessible -> Ext_S, Ext_Smstateen, Ext_Ssstateen
is_zfinx_enabled_by_stateen -> check_stateen_bit
legalize_mstateen0 -> Ext_H, Ext_S, Ext_Sdtrig, Ext_Ssqosid
read_mstateen0 -> legalize_mstateen0
Ext_Zic64b, Ext_Zama16b, Ext_Ziccif, Ext_Zicclsm, Ext_Zkt, Ext_Zvkt, Ext_Zvkn, Ext_Zvknc, Ext_Zvkng, Ext_Zvks, Ext_Zvksc, Ext_Zvksg, Ext_Smdbltrp, Ext_Smmpm, Ext_Smnpm, Ext_Sstc, Ext_Zvl32b, Ext_Zvl64b, Ext_Zvl128b, Ext_Zvl256b, Ext_Zvl512b, Ext_Zvl1024b, Ext_Sdtrig, Ext_Svade, Ext_Svadu, Ext_Zicbop, Ext_Zihintntl, Ext_Zihintpause, Ext_C, Ext_A, Ext_Ziccamoa, Ext_Ziccamoc, Ext_Ziccrse, Ext_M, Ext_B, Ext_Zbkb, Ext_Zbc, Ext_Zbkc, Ext_Zknh, Ext_Zkne, Ext_Zknd, Ext_Zksh, Ext_Zksed, Ext_Zkr, Ext_Zbkx, Ext_Zicsr, Ext_Svinval, Ext_Zawrs, Ext_Zicond, Ext_Zicbom, Ext_Zibi, Ext_Zicboz, Ext_Zifencei, Ext_Zilx, Ext_Zimop -> (leaf)
```
